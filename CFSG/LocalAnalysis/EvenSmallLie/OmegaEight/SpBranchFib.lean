module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKZero
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchOrbit

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] def wprodN (mul : ℕ → ℕ → ℕ) (m : ℕ) (ys : ℕ → ℕ) (e : ℕ) : ℕ :=
  (List.range m).foldl (fun r l => if e.testBit l then mul r (ys l) else r) 0

theorem wprodN_succ (mul : ℕ → ℕ → ℕ) (m : ℕ) (ys : ℕ → ℕ) (e : ℕ) :
    wprodN mul (m + 1) ys e = if e.testBit m then mul (wprodN mul m ys e) (ys m)
      else wprodN mul m ys e := by
  unfold wprodN
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem wprodN_congr (mul : ℕ → ℕ → ℕ) {m : ℕ} {ys zs : ℕ → ℕ} (h : ∀ l, l < m → ys l = zs l)
    (e : ℕ) : wprodN mul m ys e = wprodN mul m zs e := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [wprodN_succ, wprodN_succ, ih fun l hl => h l (by omega), h m (by omega)]

namespace CodeIso

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul)

theorem g_wprodN (h0 : mul 0 0 = 0) {m : ℕ} {ys : ℕ → ℕ} (hys : ∀ l, l < m → ys l < N) (e : ℕ) :
    wprodN mul m ys e < N ∧ Φ.g (wprodN mul m ys e) =
      ((List.range m).filter (e.testBit ·)).foldl (fun x l => x * Φ.g (ys l)) 1 := by
  induction m with
  | zero =>
    refine ⟨Φ.pos, ?_⟩
    change Φ.g 0 = 1
    rw [← Φ.f_one h0, Φ.g_f]
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih fun l hl => hys l (by omega)
    rw [wprodN_succ, List.range_succ, List.filter_append, List.foldl_append]
    split
    · rename_i hb
      have hlt : mul (wprodN mul m ys e) (ys m) < N := by
        rw [← Φ.f_g h1, ← Φ.f_g (hys m (by omega)), ← Φ.map_mul]; exact Φ.lt _
      refine ⟨hlt, ?_⟩
      rw [List.filter_singleton, hb]
      simp only [Bool.cond_true, List.foldl_cons, List.foldl_nil]
      rw [← h2]
      apply Φ.inj
      rw [Φ.f_g hlt, Φ.map_mul, Φ.f_g h1, Φ.f_g (hys m (by omega))]
    · rename_i hb
      refine ⟨h1, ?_⟩
      rw [List.filter_singleton, Bool.eq_false_iff.2 hb]
      simpa using h2

theorem f_map_wprodN (h0 : mul 0 0 = 0) (γ : H ≃* H) {m : ℕ} {ys : ℕ → ℕ}
    (hys : ∀ l, l < m → ys l < N) (e : ℕ) :
    Φ.f (γ (Φ.g (wprodN mul m ys e))) = wprodN mul m (fun l => Φ.f (γ (Φ.g (ys l)))) e := by
  have hys' : ∀ l, l < m → Φ.f (γ (Φ.g (ys l))) < N := fun l _ => Φ.lt _
  have key : ∀ (L : List ℕ) (x : H),
      γ (L.foldl (fun x l => x * Φ.g (ys l)) x) =
        L.foldl (fun x l => x * Φ.g (Φ.f (γ (Φ.g (ys l))))) (γ x) := by
    intro L
    induction L with
    | nil => intro x; rfl
    | cons a L ih => intro x; rw [List.foldl_cons, List.foldl_cons, ih, _root_.map_mul, Φ.g_f]
  have h1 : γ (Φ.g (wprodN mul m ys e)) =
      Φ.g (wprodN mul m (fun l => Φ.f (γ (Φ.g (ys l)))) e) := by
    rw [(Φ.g_wprodN h0 hys e).2, (Φ.g_wprodN h0 hys' e).2, key, _root_.map_one]
  rw [h1, Φ.f_g (Φ.g_wprodN h0 hys' e).1]

theorem ncard_orbit_map (γ : H ≃* H) (x : H) :
    (MulAction.orbit (ConjAct H) (γ x)).ncard = (MulAction.orbit (ConjAct H) x).ncard := by
  have : MulAction.orbit (ConjAct H) (γ x) = γ '' MulAction.orbit (ConjAct H) x := by
    ext y
    simp only [Set.mem_image, mem_orbit_iff_conj]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨γ.symm g * x * (γ.symm g)⁻¹, ⟨γ.symm g, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨γ g, by simp⟩
  rw [this, Set.ncard_image_of_injective _ γ.injective]

end CodeIso

structure AutData where
  K : KCoord
  q : ℕ
  g : ℕ → ℕ
  nfE : ℕ → ℕ
  nfA : ℕ → ℕ
  relE : ℕ → ℕ → ℕ
  relA : ℕ → ℕ → ℕ
  olen : ℕ → ℕ
  M : ℕ → ℕ → ℕ
  cb : ℕ → ℕ → ℕ
  nk : ℕ
  P : ℕ → ℕ → ℕ
  h : ℕ → ℕ → ℕ
  R : ℕ → ℕ → List ℕ
  cA : ℕ → ℕ → ℕ → ℕ
  cD : ℕ → ℕ → ℕ → ℕ
  gens : List ℕ

namespace AutData

variable (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (D : AutData)

@[expose] def Pk (k v : ℕ) : ℕ := xorBits D.K.n (D.P k) v

@[expose] def ys (k : ℕ) (ds : List ℕ) (l : ℕ) : ℕ := mul (D.h k l) (D.K.lin (ds.getD l 0))

@[expose] def relOK (k i : ℕ) (ds : List ℕ) : Bool :=
  (List.range (i + 1)).all fun j =>
    (if j < i then cconj mul inv (D.ys mul k ds i) (D.ys mul k ds j)
      else mul (D.ys mul k ds i) (D.ys mul k ds i)) ==
    mul (wprodN mul i (D.ys mul k ds) (D.relE i j)) (D.K.lin (D.Pk k (D.relA i j)))

@[expose] def fStates (k m : ℕ) : List (List ℕ) :=
  (List.range m).foldl (fun acc i => acc.flatMap fun ds =>
    ((D.R k i).filter fun d => D.relOK mul inv k i (ds ++ [d])).map fun d => ds ++ [d]) [[]]

@[expose] def fSearch (k : ℕ) : List (List ℕ) := D.fStates mul inv k D.q

@[expose] def F (k : ℕ) (ds : List ℕ) (x : ℕ) : ℕ :=
  mul (wprodN mul D.q (D.ys mul k ds) (D.nfE x)) (D.K.lin (D.Pk k (D.nfA x)))

theorem mem_fSearch {k : ℕ} {Dt : ℕ → ℕ} (hR : ∀ l, l < D.q → Dt l ∈ D.R k l)
    (hrel : ∀ i, i < D.q → D.relOK mul inv k i ((List.range (i + 1)).map Dt) = true) :
    (List.range D.q).map Dt ∈ D.fSearch mul inv k := by
  have key : ∀ m, m ≤ D.q → (List.range m).map Dt ∈ D.fStates mul inv k m := by
    intro m
    induction m with
    | zero => intro _; simp [fStates]
    | succ m ih =>
      intro hm
      rw [fStates, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine List.mem_flatMap.2 ⟨_, ih (by omega), ?_⟩
      refine List.mem_map.2 ⟨Dt m, List.mem_filter.2 ⟨hR m (by omega), ?_⟩, ?_⟩
      · have := hrel m (by omega)
        rwa [List.range_succ, List.map_append, List.map_singleton] at this
      · rw [List.map_append, List.map_singleton]
  exact key _ le_rfl

end AutData

end CFSG.EvenSmallLie.OmegaEight.SpBranch
