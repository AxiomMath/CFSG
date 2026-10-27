module

public import CFSG.Certificates.Kernel.TcRes.CompSound
public import CFSG.Certificates.Kernel.TcRes.LabSound
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4TwistOuter
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDefs
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.Certificates.Kernel.TcRes.Moved8Sound

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.TcRes.TK

variable {τ : Tag}

@[expose] def mset (N Φ : ℕ) : Set ℕ := {g | g < N ∧ bit Φ g = true}

@[expose] def InnerW (rt : ℕ → ℕ → ℕ) (ph : ℕ → ℕ) (ψ : Set ℕ) (s : ℕ) : Prop :=
  ∃ wd : List ℕ, (∀ l ∈ wd, l ∈ ψ) ∧ ∀ g ∈ ψ, wd.foldl (fun v l => rt l v) (ph^[s] g) = g

@[expose] def DiscW (vec : ℕ → Fin τ.rank → ℤ) (ph : ℕ → ℕ) (ψ : Set ℕ) (s : ℕ) : Prop :=
  ∃ (r : ℕ) (dl : Fin r → ℕ) (a b : Fin r → ℤ) (D : ℤ), (∀ j, dl j ∈ ψ) ∧
    (∀ g ∈ ψ, D ∣ iform (∑ j, a j • vec (dl j)) (vec g)) ∧
    (∀ g ∈ ψ, D ∣ iform (∑ j, b j • vec (dl j)) (vec g)) ∧
    ¬ D * D ∣ iform (∑ j, b j • vec (dl j))
      ((∑ j, a j • vec (ph^[s] (dl j))) - ∑ j, a j • vec (dl j))

structure CompRaw (vec : ℕ → Fin τ.rank → ℤ) (rt : ℕ → ℕ → ℕ) (ph : ℕ → ℕ) (N : ℕ)
    (Φ ψ : Set ℕ) (g0 d root : ℕ) : Prop where
  sub : ψ ⊆ Φ
  g0_mem : g0 ∈ ψ
  root_mem : root ∈ ψ
  conn : ∀ g ∈ ψ, Relation.ReflTransGen
    (fun a b => a ∈ ψ ∧ b ∈ ψ ∧ iform (vec a) (vec b) ≠ 0) root g
  closed : ∀ g ∈ ψ, ∀ h ∈ Φ, iform (vec g) (vec h) ≠ 0 → h ∈ ψ
  lt : ∀ g ∈ ψ, g < N
  e_pos : 0 < dE d
  e_le : dE d ≤ 12
  e_in : ph^[dE d] root ∈ ψ
  e_out : ∀ s, 0 < s → s < dE d → ph^[s] root ∉ ψ
  card : ψ.ncard = dN d
  simple : ∃ S : Finset ℕ, S.card = dR d ∧
    ∀ g, g ∈ S ↔ g ∈ ψ ∧ vec g ∈ simpleRoots (vec '' ψ)

structure KindRaw (vec : ℕ → Fin τ.rank → ℤ) (rt : ℕ → ℕ → ℕ) (ph : ℕ → ℕ) (ψ : Set ℕ)
    (d : ℕ) : Prop where
  lt : dK d < 4
  inner : dK d = 0 → InnerW rt ph ψ (dE d) ∨ (famE (dR d) (dN d) = false ∧
    famD4 (dR d) (dN d) = false ∧ famD (dR d) (dN d) = false ∧ famA (dR d) (dN d) = false)
  suN : dK d = 1 → DiscW vec ph ψ (dE d) ∧ famA (dR d) (dN d) = true ∧
    famD (dR d) (dN d) = false ∧ famD4 (dR d) (dN d) = false ∧ famE (dR d) (dN d) = false
  twoD : dK d = 2 → DiscW vec ph ψ (dE d) ∧ ((famD (dR d) (dN d) = true ∧
    famD4 (dR d) (dN d) = false ∧ famE (dR d) (dN d) = false) ∨
    (famD4 (dR d) (dN d) = true ∧ InnerW rt ph ψ (2 * dE d)))
  exc : dK d = 3 → DiscW vec ph ψ (dE d) ∧ (famE (dR d) (dN d) = true ∨
    (famD4 (dR d) (dN d) = true ∧ DiscW vec ph ψ (2 * dE d)))

section CbK

open CFSG.KC.TcRes.Lane

@[expose] def cbEnt (rest j : ℕ) : ℕ := (rest >>> (14 * j)) &&& 127

theorem cbEnt_zero (rest : ℕ) : cbEnt rest 0 = rest &&& 127 := by
  simp [cbEnt]

theorem cbEnt_succ (rest j : ℕ) : cbEnt rest (j + 1) = cbEnt (rest >>> 14) j := by
  simp only [cbEnt, Nat.shiftRight_add, Nat.mul_succ, Nat.add_comm (14 * j) 14]

theorem cbK_dcode {e r c kd : ℕ} (he : e < 16) (hr : r < 16) (hc : c < 256) :
    dE (e + (16 * r + (256 * c + 65536 * kd))) = e ∧
    dR (e + (16 * r + (256 * c + 65536 * kd))) = r ∧
    dN (e + (16 * r + (256 * c + 65536 * kd))) = c ∧
    dK (e + (16 * r + (256 * c + 65536 * kd))) = kd := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [dE, land15]; omega
  · rw [dR, land15, shr_eq]; norm_num; omega
  · rw [dN, land255, shr_eq]; norm_num; omega
  · rw [dK, shr_eq]; norm_num; omega

theorem cbK_olen (ph : ℕ → ℕ) (psi : ℕ) :
    ∀ f x s, 0 < olen ph psi f x s → s ≤ olen ph psi f x s ∧ olen ph psi f x s < s + f ∧
      psi.testBit (ph^[olen ph psi f x s - s + 1] x) = true ∧
      ∀ t, s ≤ t → t < olen ph psi f x s → psi.testBit (ph^[t - s + 1] x) = false := by
  intro f
  induction f with
  | zero => intro x s h; exact absurd h (lt_irrefl 0)
  | succ f ih =>
    intro x s h
    have hs : olen ph psi (f + 1) x s =
        cond (bit psi (ph x)) s (olen ph psi f (ph x) (s + 1)) := by
      simp only [olen, strictN_eq]; cases bit psi (ph x) <;> rfl
    rw [hs] at h ⊢
    cases hb : bit psi (ph x) with
    | true =>
      rw [bit_iff] at hb
      simp only [cond_true, Nat.sub_self, zero_add, Function.iterate_one]
      exact ⟨le_rfl, by omega, hb, fun t h1 h2 => absurd h2 (by omega)⟩
    | false =>
      rw [hb, cond_false] at h
      simp only [cond_false]
      obtain ⟨h1, h2, h3, h4⟩ := ih (ph x) (s + 1) h
      refine ⟨by omega, by omega, ?_, fun t ht1 ht2 => ?_⟩
      · have hq : olen ph psi f (ph x) (s + 1) - s + 1 =
            (olen ph psi f (ph x) (s + 1) - (s + 1) + 1) + 1 := by omega
        rw [hq, Function.iterate_succ_apply]
        exact h3
      · rcases Nat.eq_or_lt_of_le ht1 with rfl | ht1
        · rw [Nat.sub_self, zero_add, Function.iterate_one]
          rw [← Bool.not_eq_true, ← bit_iff, hb]
          simp
        · have hq : t - s + 1 = (t - (s + 1) + 1) + 1 := by omega
          rw [hq, Function.iterate_succ_apply]
          exact h4 t (by omega) ht2

theorem cbK_lt72 {psi g : ℕ} (hlt : psi < 2 ^ 72) (h : psi.testBit g = true) : g < 72 := by
  by_contra hg
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num)
    (by omega)))] at h
  exact absurd h (by decide)

theorem cbK_treeM_zero (ADJ Φ rest C NB : ℕ) : treeM ADJ Φ 0 rest C NB =
    Bool.rec (motive := fun _ => ℕ) (1 <<< 72) C
      (CFSG.TcRes.TK.andB (Nat.blt 0 C) (Nat.beq (NB &&& Φ &&& C) (NB &&& Φ))) := by
  simp only [treeM, strictN_eq] <;> rfl

theorem cbK_treeM_succ (ADJ Φ c rest C NB : ℕ) : treeM ADJ Φ (c + 1) rest C NB =
    Bool.rec (motive := fun _ => ℕ) (1 <<< 72)
      (treeM ADJ Φ c (rest >>> 14) (C ||| 1 <<< (rest &&& 127)) (NB ||| fld ADJ 72 (rest &&& 127)))
      (CFSG.TcRes.TK.andB (bit Φ (rest &&& 127)) (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (bit C (rest &&& 127)))
        (Bool.rec (motive := fun _ => Bool)
          (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (Nat.beq (rest &&& 127) ((rest >>> 7) &&& 127)))
            (CFSG.TcRes.TK.andB (bit C ((rest >>> 7) &&& 127)) (bit (fld ADJ 72 (rest &&& 127)) ((rest >>> 7) &&& 127))))
          (Nat.beq (rest &&& 127) ((rest >>> 7) &&& 127)) (Nat.beq C 0)))) := by
  simp only [treeM, strictN_eq] <;> rfl

theorem cbK_bit_false {m i : ℕ} : bit m i = false ↔ m.testBit i = false := by
  rw [← Bool.not_eq_true, bit_iff, Bool.not_eq_true]

theorem cbK_tree_inv {ADJ Φ psi : ℕ} (hlt : psi < 2 ^ 72) : ∀ c rest C NB,
    treeM ADJ Φ c rest C NB = psi →
    (∀ x, psi.testBit x = true ↔ C.testBit x = true ∨ ∃ j < c, cbEnt rest j = x) ∧
    (∀ j < c, Φ.testBit (cbEnt rest j) = true ∧ C.testBit (cbEnt rest j) = false ∧
      ∀ i < j, cbEnt rest i ≠ cbEnt rest j) ∧
    (∀ x, (NB.testBit x = true ∨ ∃ j < c, (fld ADJ 72 (cbEnt rest j)).testBit x = true) →
      Φ.testBit x = true → psi.testBit x = true) ∧
    (C = 0 → 0 < c) ∧
    (∀ j < c, (C = 0 ∧ j = 0) ∨ ((C.testBit (cbEnt (rest >>> 7) j) = true ∨
      ∃ i < j, cbEnt rest i = cbEnt (rest >>> 7) j) ∧
      (fld ADJ 72 (cbEnt rest j)).testBit (cbEnt (rest >>> 7) j) = true)) := by
  have hbig : ¬ (1 <<< 72 : ℕ) = psi := by
    rw [Nat.shiftLeft_eq, one_mul]
    rintro rfl
    exact lt_irrefl _ hlt
  intro c
  induction c with
  | zero =>
    intro rest C NB h
    rw [cbK_treeM_zero, brecN_eq, Bool.cond_eq_ite] at h
    split_ifs at h with hb
    · subst h
      rw [andB_eq_true, blt_eq_true, beq_eq_true] at hb
      refine ⟨fun x => by simp, fun j hj => absurd hj (Nat.not_lt_zero _), ?_,
        fun h0 => absurd h0 (by omega), fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      rintro x (hx | ⟨j, hj, -⟩) hΦx
      · have := congrArg (fun m => m.testBit x) hb.2
        simpa [Nat.testBit_and, hx, hΦx] using this
      · exact absurd hj (Nat.not_lt_zero _)
    · exact absurd h hbig
  | succ c ih =>
    intro rest C NB h
    rw [cbK_treeM_succ, brecN_eq, Bool.cond_eq_ite] at h
    split_ifs at h with hb
    swap
    · exact absurd h hbig
    simp only [andB_eq_true, notB_eq_true, cbK_bit_false, bit_iff, boolRec_true, beq_eq_true,
      beq_eq_false] at hb
    obtain ⟨hΦg, hCg, hpa⟩ := hb
    rw [← cbEnt_zero rest] at hΦg hCg hpa
    rw [← cbEnt_zero (rest >>> 7)] at hpa
    rw [← cbEnt_zero rest] at h
    obtain ⟨I1, I2, I3, I4, I5⟩ := ih _ _ _ h
    have hsh : rest >>> 14 >>> 7 = rest >>> 7 >>> 14 := by
      rw [← Nat.shiftRight_add, ← Nat.shiftRight_add, Nat.add_comm]
    have hE : ∀ j, cbEnt (rest >>> 14) j = cbEnt rest (j + 1) := fun j => (cbEnt_succ rest j).symm
    have hP : ∀ j, cbEnt (rest >>> 14 >>> 7) j = cbEnt (rest >>> 7) (j + 1) := fun j => by
      rw [hsh, cbEnt_succ]
    refine ⟨fun x => ?_, fun j hj => ?_, fun x hx hΦx => ?_, fun _ => by omega, fun j hj => ?_⟩
    · rw [I1 x, testBit_or_pow]
      simp only [Bool.or_eq_true, decide_eq_true_eq, hE]
      constructor
      · rintro ((h1 | h1) | ⟨j, hj, rfl⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨0, by omega, h1.symm⟩
        · exact Or.inr ⟨j + 1, by omega, rfl⟩
      · rintro (h1 | ⟨j, hj, rfl⟩)
        · exact Or.inl (Or.inl h1)
        · rcases j with _ | j
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr ⟨j, by omega, rfl⟩
    · rcases j with _ | j
      · exact ⟨hΦg, hCg, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      · obtain ⟨a1, a2, a3⟩ := I2 j (by omega)
        rw [hE] at a1 a2
        rw [testBit_or_pow, Bool.or_eq_false_iff, decide_eq_false_iff_not] at a2
        refine ⟨a1, a2.1, fun i hi => ?_⟩
        rcases i with _ | i
        · exact fun h' => a2.2 h'.symm
        · have := a3 i (by omega)
          rw [hE, hE] at this
          exact this
    · apply I3 x _ hΦx
      rw [Nat.testBit_or]
      rcases hx with hx | ⟨j, hj, hx⟩
      · left
        simp [hx]
      · rcases j with _ | j
        · left
          simp [hx]
        · right
          exact ⟨j, by omega, by rw [hE]; exact hx⟩
    · rcases j with _ | j
      · by_cases hC : C = 0
        · exact Or.inl ⟨hC, rfl⟩
        · obtain ⟨-, h2, h3⟩ := hpa.2 hC
          exact Or.inr ⟨Or.inl h2, h3⟩
      · right
        have hC' : C ||| 1 <<< cbEnt rest 0 ≠ 0 := by
          intro h0
          have := congrArg (fun m => m.testBit (cbEnt rest 0)) h0
          simp [testBit_or_pow] at this
        rcases I5 j (by omega) with ⟨h0, -⟩ | ⟨h1, h2⟩
        · exact absurd h0 hC'
        · rw [hP, hE] at h2
          rw [hP] at h1
          refine ⟨?_, h2⟩
          rcases h1 with h1 | ⟨i, hi, h1⟩
          · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at h1
            rcases h1 with h1 | h1
            · exact Or.inl h1
            · exact Or.inr ⟨0, by omega, h1.symm⟩
          · rw [hE] at h1
            exact Or.inr ⟨i + 1, by omega, h1⟩

theorem cbK_tree {vec : ℕ → Fin Tag.E6.rank → ℤ} {neg : ℕ → ℕ} {RT ADJ Φ c rest psi : ℕ}
    (hD : DatumRaw Tag.E6 72 vec (fun g v => rtv RT g v)
      (fun g v => Nat.beq (fld (fld ADJ 72 g) 1 v) 1) neg)
    (hpsi : treeM ADJ Φ c rest 0 0 = psi) (hlt : psi < 2 ^ 72) :
    0 < c ∧ (∀ g, g ∈ mset 72 psi ↔ ∃ j < c, cbEnt rest j = g) ∧
    (∀ i < c, ∀ j < c, cbEnt rest i = cbEnt rest j → i = j) ∧
    mset 72 psi ⊆ mset 72 Φ ∧
    (∀ g ∈ mset 72 psi, Relation.ReflTransGen (fun a b => a ∈ mset 72 psi ∧ b ∈ mset 72 psi ∧
      iform (vec a) (vec b) ≠ 0) (cbEnt rest 0) g) ∧
    (∀ g ∈ mset 72 psi, ∀ h ∈ mset 72 Φ, iform (vec g) (vec h) ≠ 0 → h ∈ mset 72 psi) := by
  obtain ⟨I1, I2, I3, I4, I5⟩ := cbK_tree_inv hlt c rest 0 0 hpsi
  have hen : ∀ g, g ∈ mset 72 psi ↔ ∃ j < c, cbEnt rest j = g := by
    intro g
    constructor
    · rintro ⟨-, hb⟩
      rw [bit_iff, I1] at hb
      simpa using hb
    · rintro ⟨j, hj, rfl⟩
      have hb : psi.testBit (cbEnt rest j) = true := (I1 _).2 (Or.inr ⟨j, hj, rfl⟩)
      exact ⟨cbK_lt72 hlt hb, bit_iff.2 hb⟩
  refine ⟨I4 rfl, hen, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij ((I2 j hj).2.2 i h)
    · exact h
    · exact absurd hij.symm ((I2 i hi).2.2 j h)
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := (hen g).1 hg
    exact ⟨hg.1, bit_iff.2 (I2 j hj).1⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := (hen g).1 hg
    clear hg
    revert hj
    induction j using Nat.strong_induction_on with
    | _ j ihj =>
      intro hj
      rcases j with _ | j
      · exact .refl
      rcases I5 (j + 1) hj with ⟨-, h0⟩ | ⟨h1, h2⟩
      · omega
      rcases h1 with h1 | ⟨i, hi, h1⟩
      · simp at h1
      have hmi : cbEnt rest i ∈ mset 72 psi := (hen _).2 ⟨i, by omega, rfl⟩
      have hg : cbEnt rest (j + 1) ∈ mset 72 psi := (hen _).2 ⟨j + 1, hj, rfl⟩
      have hadj : iform (vec (cbEnt rest i)) (vec (cbEnt rest (j + 1))) ≠ 0 := by
        have hp72 : cbEnt (rest >>> 7) (j + 1) < 72 := h1 ▸ hmi.1
        rw [h1]
        exact (hD.adj _ hg.1 _ hp72).1 (by simp only [beq_eq_true, fld_one_eq_one]; exact h2)
      exact Relation.ReflTransGen.tail (ihj i (by omega) (by omega)) ⟨hmi, hg, hadj⟩
  · intro g hg h hh hne
    obtain ⟨j, hj, rfl⟩ := (hen g).1 hg
    have hb : (fld ADJ 72 (cbEnt rest j)).testBit h = true := by
      have := (hD.adj _ hg.1 h hh.1).2 (by rw [iform_comm]; exact hne)
      simpa only [beq_eq_true, fld_one_eq_one] using this
    exact ⟨hh.1, bit_iff.2 (I3 h (Or.inr ⟨j, hj, hb⟩) (bit_iff.1 hh.2))⟩

theorem cbK_ncard {ψ : Set ℕ} {c : ℕ} {ent : ℕ → ℕ} (hen : ∀ g, g ∈ ψ ↔ ∃ j < c, ent j = g)
    (hinj : ∀ i < c, ∀ j < c, ent i = ent j → i = j) : ψ.ncard = c := by
  have : ψ = ((Finset.range c).image ent : Set ℕ) := by
    ext g; simp [hen g]
  rw [this, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact hinj i (by simpa using hi) j (by simpa using hj) hij

theorem simple_of_dec {τ : Tag} {N : ℕ}
    {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    (hD : DatumRaw τ N vec rt adj neg) (hsym1 : ∀ i, τ.symmetrizer i i = 1) {Φ ψ : Set ℕ}
    {pos : ℕ → Prop} {dec : ℕ → ℕ → Prop} (hpos : ∀ g < N, pos g ↔ ∀ m, 0 ≤ vec g m)
    (hdec : ∀ g < N, ∀ d < N, dec g d ↔ pos d ∧ iform (vec g) (vec d) = 1 ∧ pos (rt d g))
    (hψN : ∀ g ∈ ψ, g < N) (hψΦ : ψ ⊆ Φ)
    (hclosed : ∀ g ∈ ψ, ∀ h ∈ Φ, iform (vec g) (vec h) ≠ 0 → h ∈ ψ)
    (hΦsub : ∀ a ∈ Φ, ∀ b ∈ Φ, ∀ c < N, vec c = vec a - vec b → c ∈ Φ) {g : ℕ} (hg : g ∈ ψ) :
    vec g ∈ simpleRoots (vec '' ψ) ↔ pos g ∧ ∀ d ∈ ψ, ¬ dec g d := by
  have h2 : ∀ {x}, IsRoot τ x → iform x x = 2 := fun hx => by
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hx
    rw [hj, hsym1]
    norm_num
  have hposh : ∀ i < N, pos i ↔ 0 < height (vec i) := by
    intro i hi
    rw [hpos i hi]
    have hr := hD.isRoot i hi
    constructor
    · intro h
      have h1 : 0 ≤ height (vec i) := Finset.sum_nonneg fun j _ => h j
      exact lt_of_le_of_ne h1 (Ne.symm hr.height_ne_zero)
    · intro h
      rcases hr.nonneg_or_nonpos with hs | hs
      · exact hs
      · have h2 : height (vec i) ≤ 0 := Finset.sum_nonpos fun j _ => hs j
        exact absurd h (not_lt.2 h2)
  have hgN := hψN g hg
  have hrg := hD.isRoot g hgN
  constructor
  · intro hs
    obtain ⟨-, hpg, hnd⟩ := mem_simpleRoots.1 hs
    refine ⟨(hposh g hgN).2 hpg.2, fun d hd hdg => ?_⟩
    have hdN := hψN d hd
    obtain ⟨hpd, hip, hpe⟩ := (hdec g hgN d hdN).1 hdg
    obtain ⟨heN, hev⟩ := hD.refl d hdN g hgN
    rw [hip, one_smul] at hev
    have heΦ : rt d g ∈ Φ := hΦsub g (hψΦ hg) d (hψΦ hd) _ heN hev
    have heψ : rt d g ∈ ψ := hclosed g hg _ heΦ (by
      rw [hev, iform_sub_right, h2 hrg, hip]
      norm_num)
    exact hnd (vec d) ⟨⟨d, hd, rfl⟩, (hposh d hdN).1 hpd⟩ (vec (rt d g))
      ⟨⟨_, heψ, rfl⟩, (hposh _ heN).1 hpe⟩ (by rw [hev]; abel)
  · rintro ⟨hpg, hnd⟩
    rw [mem_simpleRoots]
    refine ⟨hrg, ⟨⟨g, hg, rfl⟩, (hposh g hgN).1 hpg⟩, ?_⟩
    rintro γ ⟨⟨d, hd, rfl⟩, hγ⟩ δ ⟨⟨k, hk, rfl⟩, hδ⟩ h
    have hdN := hψN d hd
    have hkN := hψN k hk
    have E1 : iform (vec d + vec k) (vec d + vec k) = 2 := by
      rw [← h]
      exact h2 hrg
    rw [iform_add_left, iform_add_right, iform_add_right, h2 (hD.isRoot d hdN),
      h2 (hD.isRoot k hkN), iform_comm (vec k) (vec d)] at E1
    have hip1 : iform (vec g) (vec d) = 1 := by
      rw [h, iform_add_left, h2 (hD.isRoot d hdN), iform_comm (vec k) (vec d)]
      linarith
    obtain ⟨heN, hev⟩ := hD.refl d hdN g hgN
    rw [hip1, one_smul, h, add_sub_cancel_left] at hev
    exact hnd d hd ((hdec g hgN d hdN).2 ⟨(hposh d hdN).2 hγ, hip1,
      (hposh _ heN).2 (by rw [hev]; exact hδ)⟩)

theorem cbK_sub_mem {τ : Tag} {N : ℕ}
    {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    (hD : DatumRaw τ N vec rt adj neg) (hsym1 : ∀ i, τ.symmetrizer i i = 1) {Φ ψ : Set ℕ}
    (hψN : ∀ g ∈ ψ, g < N) (hψΦ : ψ ⊆ Φ)
    (hclosed : ∀ g ∈ ψ, ∀ h ∈ Φ, iform (vec g) (vec h) ≠ 0 → h ∈ ψ)
    (hΦsub : ∀ a ∈ Φ, ∀ b ∈ Φ, ∀ c < N, vec c = vec a - vec b → c ∈ Φ)
    {a b : ℕ} (ha : a ∈ ψ) (hb : b ∈ ψ) (hne : vec a ≠ vec b) (hpos : 0 < iform (vec a) (vec b)) :
    ∃ c ∈ ψ, vec c = vec a - vec b := by
  have hra := hD.isRoot a (hψN a ha)
  have hrb := hD.isRoot b (hψN b hb)
  have hrd := isRoot_sub_of_iform_pos hra hrb hne hpos
  obtain ⟨c, hc, hvc⟩ := hD.exists_eq hrd
  have hcΦ : c ∈ Φ := hΦsub a (hψΦ ha) b (hψΦ hb) c hc hvc
  have h2 : ∀ {x}, IsRoot τ x → iform x x = 2 := fun hx => by
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hx
    rw [hj, hsym1]
    norm_num
  have h1 : iform (vec a) (vec b) = 1 := by
    have := h2 hrd
    rw [iform_sub_left, iform_sub_right, iform_sub_right, h2 hra, h2 hrb,
      iform_comm (vec b) (vec a)] at this
    linarith
  refine ⟨c, hclosed a ha c hcΦ ?_, hvc⟩
  rw [hvc, iform_sub_right, h2 hra, h1]
  norm_num

theorem card_simple_le {τ : Tag} {N : ℕ}
    {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    (hD : DatumRaw τ N vec rt adj neg) (hsym1 : ∀ i, τ.symmetrizer i i = 1) {Φ ψ : Set ℕ}
    (hψN : ∀ g ∈ ψ, g < N) (hψΦ : ψ ⊆ Φ)
    (hclosed : ∀ g ∈ ψ, ∀ h ∈ Φ, iform (vec g) (vec h) ≠ 0 → h ∈ ψ)
    (hΦsub : ∀ a ∈ Φ, ∀ b ∈ Φ, ∀ c < N, vec c = vec a - vec b → c ∈ Φ)
    (S : Finset ℕ) (hS : ∀ g ∈ S, g ∈ ψ ∧ vec g ∈ simpleRoots (vec '' ψ)) : S.card ≤ τ.rank := by
  classical
  have hle : ∀ a ∈ S, ∀ b ∈ S, vec a ≠ vec b → iform (vec a) (vec b) ≤ 0 := by
    intro a ha b hb hne
    by_contra hp
    have hp' := not_le.1 hp
    obtain ⟨ha1, ha2⟩ := hS a ha
    obtain ⟨hb1, hb2⟩ := hS b hb
    obtain ⟨c, hc, hvc⟩ := cbK_sub_mem hD hsym1 hψN hψΦ hclosed hΦsub ha1 hb1 hne hp'
    rcases IsRoot.height_pos_or_neg (hD.isRoot c (hψN c hc)) with h | h
    · exact (mem_simpleRoots.1 ha2).2.2 (vec b) (mem_simpleRoots.1 hb2).2.1 (vec c)
        ⟨⟨c, hc, rfl⟩, h⟩ (by rw [hvc]; abel)
    · have hp2 : 0 < iform (vec b) (vec a) := by rwa [iform_comm]
      obtain ⟨c', hc', hvc'⟩ := cbK_sub_mem hD hsym1 hψN hψΦ hclosed hΦsub hb1 ha1 (Ne.symm hne) hp2
      have h' : 0 < height (vec c') := by
        rw [hvc', height_sub]
        rw [hvc, height_sub] at h
        linarith
      exact (mem_simpleRoots.1 hb2).2.2 (vec a) (mem_simpleRoots.1 ha2).2.1 (vec c')
        ⟨⟨c', hc', rfl⟩, h'⟩ (by rw [hvc']; abel)
  have hinj : Set.InjOn vec S := fun a ha b hb h =>
    hD.inj a (hψN a (hS a ha).1) b (hψN b (hS b hb).1) h
  rw [← Finset.card_image_of_injOn hinj]
  have hht : ∀ β ∈ S.image vec, 0 < height β := by
    intro β hβ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hβ
    exact (mem_simpleRoots.1 (hS a ha).2).2.1.2
  have hle' : ∀ β ∈ S.image vec, ∀ γ ∈ S.image vec, β ≠ γ → iform β γ ≤ 0 := by
    intro β hβ γ hγ hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hβ
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hγ
    exact hle a ha b hb hne
  have hind : LinearIndependent ℝ fun β : S.image vec => toReal (β : Fin τ.rank → ℤ) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg β
    have := eq_zero_of_sum_smul_toReal_eq_zero hht hle'
      (c := fun γ => if h : γ ∈ S.image vec then g ⟨γ, h⟩ else 0) (by
        rw [← Finset.sum_coe_sort]
        simpa using hg) β.1 β.2
    simpa using this
  have hcard := hind.fintype_card_le_finrank
  rw [Fintype.card_coe, Module.finrank_fin_fun] at hcard
  exact hcard

theorem cbK_posOK {vec : ℕ → Fin Tag.E6.rank → ℤ} {V POS : ℕ} (hvec : vec = vecOf 6 V) {g : ℕ}
    (h : posOK V POS g = true) : bit POS g = true ↔ ∀ m, 0 ≤ vec g m := by
  have hall : (allLt 6 fun m => Nat.ble 7 (fld (fld V 96 g) 16 m)) = true ↔
      ∀ m : Fin Tag.E6.rank, 0 ≤ vec g m := by
    rw [allLt_iff, hvec]
    constructor
    · intro h m
      have := h m.val (by have := m.isLt; simpa [Tag.rank] using this)
      rw [Nat.ble_eq] at this
      simp only [vecOf]
      push_cast
      omega
    · intro h m hm
      have := h ⟨m, by simpa [Tag.rank] using hm⟩
      have h96 : 16 * 6 = 96 := rfl
      simp only [vecOf, h96] at this
      rw [Nat.ble_eq]
      omega
  rw [← hall]
  unfold posOK at h
  rw [strictB_eq] at h
  cases hb : bit POS g <;> cases ha : (allLt 6 fun m => Nat.ble 7 (fld (fld V 96 g) 16 m)) <;>
    simp_all [CFSG.TcRes.TK.notB]

theorem cbK_decOK {vec : ℕ → Fin Tag.E6.rank → ℤ} {RT X Y POS DEC : ℕ}
    (hX : ∀ v < 72, ∀ g < 72, (dP 6 (fld X 192 v * fld Y 192 g) : ℤ) -
      dQ 6 (fld X 192 v * fld Y 192 g) = iform (vec v) (vec g)) {g : ℕ} (hg : g < 72)
    (h : decOK RT X Y POS DEC g = true) {d : ℕ} (hd : d < 72) :
    bit (fld DEC 72 g) d = true ↔ bit POS d = true ∧ iform (vec g) (vec d) = 1 ∧
      bit POS (rtv RT d g) = true := by
  unfold decOK at h
  rw [strictB_eq, allLt_iff] at h
  have h1 := h d hd
  rw [strictB_eq, boolRec_true, notB_eq_true] at h1
  have hip : Nat.beq (ipK X Y g d) (Nat.add OFS 1) = true ↔ iform (vec g) (vec d) = 1 := by
    rw [beq_eq_true, ← hX g hg d hd]
    have e1 : ipK X Y g d = spk (dP 6 (fld X 192 g * fld Y 192 d)) (dQ 6 (fld X 192 g * fld Y 192 d)) :=
      strictN_eq _ _
    rw [e1]
    simp only [spk, OFS, nadd, nsub]
    omega
  rw [← hip, ← andB_eq_true, ← andB_eq_true]
  constructor
  · intro hb
    by_contra hc
    rw [Bool.not_eq_true] at hc
    rw [h1.2 hc] at hb
    exact absurd hb (by decide)
  · exact h1.1

theorem cbK_simpM (POS DEC psi : ℕ) : ∀ c rest acc, (∀ j < c, cbEnt rest j < 72) →
    simpM POS DEC psi c rest acc >>> 80 = acc >>> 80 + ∑ j ∈ Finset.range c,
      if CFSG.TcRes.TK.andB (bit POS (cbEnt rest j)) (Nat.beq (fld DEC 72 (cbEnt rest j) &&& psi) 0) = true
      then 1 else 0 := by
  intro c
  induction c with
  | zero =>
    intro rest acc _
    rw [Finset.sum_range_zero, add_zero]
    rfl
  | succ c ih =>
    intro rest acc hlt
    have h : simpM POS DEC psi (c + 1) rest acc = simpM POS DEC psi c (rest >>> 14)
        (Bool.rec (motive := fun _ => ℕ) acc ((acc ||| 1 <<< cbEnt rest 0) + 1 <<< 80)
          (CFSG.TcRes.TK.andB (bit POS (cbEnt rest 0)) (Nat.beq (fld DEC 72 (cbEnt rest 0) &&& psi) 0))) := by
      simp only [simpM, strictN_eq] <;> rfl
    rw [h, ih _ _ (fun j hj => by rw [← cbEnt_succ]; exact hlt (j + 1) (by omega)),
      Finset.sum_range_succ']
    simp only [← cbEnt_succ]
    have hg := hlt 0 (by omega)
    cases hb : CFSG.TcRes.TK.andB (bit POS (cbEnt rest 0)) (Nat.beq (fld DEC 72 (cbEnt rest 0) &&& psi) 0)
    · simp
    · have key : ((acc ||| 1 <<< cbEnt rest 0) + 1 <<< 80) >>> 80 = acc >>> 80 + 1 := by
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq 1 80, one_mul,
          Nat.add_div_right _ (by positivity), ← Nat.shiftRight_eq_div_pow]
        congr 1
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, testBit_or_pow]
        have : ¬ (80 + i = cbEnt rest 0) := by omega
        simp [this]
      simp only [key, if_true]
      omega

theorem cbK_simpM_mask (POS DEC psi : ℕ) : ∀ c rest acc, (∀ j < c, cbEnt rest j < 72) →
    ∀ x < 72, (simpM POS DEC psi c rest acc).testBit x = true →
      acc.testBit x = true ∨ ∃ j < c, cbEnt rest j = x := by
  intro c
  induction c with
  | zero => intro rest acc _ x _ hx; exact Or.inl hx
  | succ c ih =>
    intro rest acc hlt x hx h
    have h0 : simpM POS DEC psi (c + 1) rest acc = simpM POS DEC psi c (rest >>> 14)
        (Bool.rec (motive := fun _ => ℕ) acc ((acc ||| 1 <<< cbEnt rest 0) + 1 <<< 80)
          (CFSG.TcRes.TK.andB (bit POS (cbEnt rest 0)) (Nat.beq (fld DEC 72 (cbEnt rest 0) &&& psi) 0))) := by
      simp only [simpM, strictN_eq] <;> rfl
    rw [h0] at h
    rcases ih _ _ (fun j hj => by rw [← cbEnt_succ]; exact hlt (j + 1) (by omega)) x hx h with
      h1 | ⟨j, hj, h1⟩
    · cases hb : CFSG.TcRes.TK.andB (bit POS (cbEnt rest 0)) (Nat.beq (fld DEC 72 (cbEnt rest 0) &&& psi) 0)
      · rw [hb] at h1
        exact Or.inl h1
      · rw [hb] at h1
        change ((acc ||| 1 <<< cbEnt rest 0) + 1 <<< 80).testBit x = true at h1
        rw [Nat.shiftLeft_eq 1 80, one_mul, Nat.add_comm, Nat.testBit_two_pow_add_gt (by omega),
          testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at h1
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨0, by omega, h1.symm⟩
    · rw [← cbEnt_succ] at h1
      exact Or.inr ⟨j + 1, by omega, h1⟩

theorem cbK_row {row psi : ℕ} :
    Nat.beq (row &&& psi) 0 = true ↔ ∀ d, psi.testBit d = true → row.testBit d = false := by
  rw [beq_eq_true]
  constructor
  · intro h d hd
    have := congrArg (fun m => m.testBit d) h
    simp only [Nat.testBit_and, hd, Bool.and_true, Nat.zero_testBit] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro d
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases hd : psi.testBit d
    · simp
    · simp [h d hd]

theorem cbK_simple {vec : ℕ → Fin Tag.E6.rank → ℤ} {neg : ℕ → ℕ}
    {RT X Y ADJ POS DEC V Φ c rest psi : ℕ}
    (hvec : vec = vecOf 6 V)
    (hD : DatumRaw Tag.E6 72 vec (fun g v => rtv RT g v)
      (fun g v => Nat.beq (fld (fld ADJ 72 g) 1 v) 1) neg)
    (hX : ∀ v < 72, ∀ g < 72, (dP 6 (fld X 192 v * fld Y 192 g) : ℤ) -
      dQ 6 (fld X 192 v * fld Y 192 g) = iform (vec v) (vec g))
    (hpos : ∀ g < 72, posOK V POS g = true) (hdec : ∀ g < 72, decOK RT X Y POS DEC g = true)
    (hΦsub : ∀ a ∈ mset 72 Φ, ∀ b ∈ mset 72 Φ, ∀ c < 72, vec c = vec a - vec b → c ∈ mset 72 Φ)
    (hen : ∀ g, g ∈ mset 72 psi ↔ ∃ j < c, cbEnt rest j = g)
    (hinj : ∀ i < c, ∀ j < c, cbEnt rest i = cbEnt rest j → i = j)
    (hsub : mset 72 psi ⊆ mset 72 Φ)
    (hcl : ∀ g ∈ mset 72 psi, ∀ h ∈ mset 72 Φ, iform (vec g) (vec h) ≠ 0 → h ∈ mset 72 psi) :
    simpM POS DEC psi c rest 0 >>> 80 ≤ 6 ∧ ∃ S : Finset ℕ,
      S.card = simpM POS DEC psi c rest 0 >>> 80 ∧
      ∀ g, g ∈ S ↔ g ∈ mset 72 psi ∧ vec g ∈ simpleRoots (vec '' mset 72 psi) := by
  have hsym1 : ∀ i, Tag.E6.symmetrizer i i = 1 := fun i => by simp [Tag.symmetrizer]
  have hψN : ∀ g ∈ mset 72 psi, g < 72 := fun g hg => hg.1
  have hentlt : ∀ j < c, cbEnt rest j < 72 := fun j hj => ((hen _).2 ⟨j, hj, rfl⟩).1
  have hsimp : ∀ {g}, g ∈ mset 72 psi → (vec g ∈ simpleRoots (vec '' mset 72 psi) ↔
      bit POS g = true ∧ ∀ d ∈ mset 72 psi, ¬ bit (fld DEC 72 g) d = true) := fun hg =>
    simple_of_dec hD hsym1 (pos := fun g => bit POS g = true)
      (dec := fun g d => bit (fld DEC 72 g) d = true)
      (fun g hg => cbK_posOK hvec (hpos g hg)) (fun g hg d hd => cbK_decOK hX hg (hdec g hg) hd)
      hψN hsub hcl hΦsub hg
  let S : Finset ℕ := (Finset.range c).image (cbEnt rest) |>.filter fun g =>
    vec g ∈ simpleRoots (vec '' mset 72 psi)
  have hSiff : ∀ g, g ∈ S ↔ g ∈ mset 72 psi ∧ vec g ∈ simpleRoots (vec '' mset 72 psi) := by
    intro g
    simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_range, hen g]
  have hcard : S.card = simpM POS DEC psi c rest 0 >>> 80 := by
    rw [cbK_simpM POS DEC psi c rest 0 hentlt, Nat.zero_shiftRight, zero_add, Finset.card_filter,
      Finset.sum_image (fun i hi j hj hij => hinj i (by simpa using hi) j (by simpa using hj) hij)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < c := by simpa using hj
    have hm : cbEnt rest j ∈ mset 72 psi := (hen _).2 ⟨j, hj', rfl⟩
    congr 1
    rw [hsimp hm, andB_eq_true, cbK_row, eq_iff_iff]
    refine and_congr Iff.rfl ⟨fun h d hd => ?_, fun h d hd hb => ?_⟩
    · rcases lt_or_ge d 72 with hd72 | hd72
      · rw [← Bool.not_eq_true]
        intro hb'
        exact h d ⟨hd72, bit_iff.2 hd⟩ (bit_iff.2 hb')
      · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (fld_lt _ _ _)
          (Nat.pow_le_pow_right (by norm_num) hd72))
    · rw [bit_iff, h d (bit_iff.1 hd.2)] at hb
      exact absurd hb (by decide)
  refine ⟨?_, S, hcard, hSiff⟩
  rw [← hcard]
  exact card_simple_le hD hsym1 hψN hsub hcl hΦsub S fun g hg => (hSiff g).1 hg

theorem cbK_phPow (ph : ℕ → ℕ) (e g : ℕ) : phPow ph e g = ph^[e] g := by
  induction e with
  | zero => rfl
  | succ e ih =>
    change strictN (phPow ph e g) ph = _
    rw [strictN_eq, ih, Function.iterate_succ_apply']

theorem cbK_applyW (RT : ℕ) : ∀ wl w v, applyW RT wl w v =
    ((List.range wl).map (fld w 7)).foldl (fun v l => rtv RT l v) v := by
  intro wl
  induction wl with
  | zero => intro w v; rfl
  | succ n ih =>
    intro w v
    change strictN (rtv RT (Nat.land w 127) v) (fun v' => applyW RT n (w >>> 7) v') = _
    rw [strictN_eq, ih, List.range_succ_eq_map, List.map_cons, List.foldl_cons, List.map_map]
    have h127 : (127 : ℕ) = 2 ^ 7 - 1 := by norm_num
    have h0 : fld w 7 0 = Nat.land w 127 := by
      rw [fld_eq, nland, h127, Nat.and_two_pow_sub_one_eq_mod]
      simp
    rw [h0]
    congr 1
    apply List.map_congr_left
    intro i _
    have := fld_shr w 7 1 i
    rw [mul_one, add_comm] at this
    exact this

theorem cbK_loop (q : ℕ → Bool) : ∀ c rest,
    Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun _ ih r => strictB (Nat.land r 127) fun g => CFSG.TcRes.TK.andB (q g) (ih (Nat.shiftRight r 14)))
      c rest = true → ∀ j < c, q (cbEnt rest j) = true := by
  intro c
  induction c with
  | zero => intro rest _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ c ih =>
    intro rest h0 j hj
    have h : strictB (Nat.land rest 127) (fun g => CFSG.TcRes.TK.andB (q g) (Nat.rec (motive := fun _ => ℕ → Bool)
        (fun _ => true) (fun _ ih r => strictB (Nat.land r 127) fun g => CFSG.TcRes.TK.andB (q g)
          (ih (Nat.shiftRight r 14))) c (Nat.shiftRight rest 14))) = true := h0
    rw [strictB_eq, andB_eq_true] at h
    rcases j with _ | j
    · rw [cbEnt_zero]; exact h.1
    · rw [cbEnt_succ]; exact ih _ h.2 j (by omega)

theorem cbK_loop2 (q : ℕ → Bool) : ∀ c rest,
    Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun _ ih r => CFSG.TcRes.TK.andB (q (Nat.land r 127)) (ih (Nat.shiftRight r 14)))
      c rest = true → ∀ j < c, q (cbEnt rest j) = true := by
  intro c
  induction c with
  | zero => intro rest _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ c ih =>
    intro rest h0 j hj
    have h : CFSG.TcRes.TK.andB (q (Nat.land rest 127)) (Nat.rec (motive := fun _ => ℕ → Bool)
        (fun _ => true) (fun _ ih r => CFSG.TcRes.TK.andB (q (Nat.land r 127))
          (ih (Nat.shiftRight r 14))) c (Nat.shiftRight rest 14)) = true := h0
    rw [andB_eq_true] at h
    rcases j with _ | j
    · rw [cbEnt_zero]; exact h.1
    · rw [cbEnt_succ]; exact ih _ h.2 j (by omega)

theorem cbK_wOK {RT : ℕ} {ph : ℕ → ℕ} {psi c rest s wl w : ℕ} (hlt : psi < 2 ^ 72)
    (hen : ∀ g, g ∈ mset 72 psi ↔ ∃ j < c, cbEnt rest j = g)
    (h : wOK RT ph psi c rest s wl w = true) :
    InnerW (fun g v => rtv RT g v) ph (mset 72 psi) s := by
  unfold wOK at h
  rw [andB_eq_true, allLt_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hl := cbK_loop (fun g => Nat.beq (applyW RT wl w (phPow ph s g)) g) c rest h2
  refine ⟨(List.range wl).map (fld w 7), ?_, ?_⟩
  · intro l hl'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl'
    have hb := h1 i (List.mem_range.1 hi)
    exact ⟨cbK_lt72 hlt (bit_iff.1 hb), hb⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := (hen g).1 hg
    have := hl j hj
    rw [beq_eq_true, cbK_applyW, cbK_phPow] at this
    exact this

@[expose] def cbSv (x : ℕ) : ℤ := (x : ℤ) - 4294967296

theorem cbSv_ofs : cbSv OFS = 0 := by
  change ((4294967296 : ℕ) : ℤ) - 4294967296 = 0
  norm_num

theorem cbSv_spk (a b : ℕ) (hb : b ≤ 4294967296) : cbSv (spk a b) = (a : ℤ) - b := by
  have e : spk a b = 4294967296 + a - b := rfl
  rw [cbSv, e]
  omega

theorem cbSv_sadd {x y : ℕ} (h : -4294967296 ≤ cbSv x + cbSv y) :
    cbSv (sadd x y) = cbSv x + cbSv y := by
  have e : sadd x y = x + y - 4294967296 := rfl
  unfold cbSv at h ⊢
  rw [e]
  omega

theorem cbSv_smul {x y : ℕ} (h : -4294967296 ≤ cbSv x * cbSv y) :
    cbSv (smul x y) = cbSv x * cbSv y := by
  have e : smul x y = x * y + (18446744073709551616 + 4294967296) - 4294967296 * (x + y) := rfl
  have key : ((x * y + (18446744073709551616 + 4294967296) : ℕ) : ℤ) -
      ((4294967296 * (x + y) : ℕ) : ℤ) = cbSv x * cbSv y + 4294967296 := by
    push_cast
    unfold cbSv
    ring
  have hle : ((4294967296 * (x + y) : ℕ) : ℤ) ≤
      ((x * y + (18446744073709551616 + 4294967296) : ℕ) : ℤ) := by
    linarith
  have hle' : 4294967296 * (x + y) ≤ x * y + (18446744073709551616 + 4294967296) := by
    exact_mod_cast hle
  rw [e]
  unfold cbSv at key ⊢
  rw [Nat.cast_sub hle']
  linarith

theorem cbK_ssum_succ (c : ℕ) (f : ℕ → ℕ) : ssum (c + 1) f = sadd (f c) (ssum c f) := by
  have e : ssum (c + 1) f = strictN (ssum c f) (fun a => sadd (f c) a) := rfl
  rw [strictN_eq] at e
  exact e

theorem cbSv_ssum (f : ℕ → ℕ) (B : ℤ) : ∀ c, (∀ j < c, |cbSv (f j)| ≤ B) → c * B < 4294967296 →
    cbSv (ssum c f) = ∑ j ∈ Finset.range c, cbSv (f j) ∧
      |∑ j ∈ Finset.range c, cbSv (f j)| ≤ c * B := by
  intro c
  induction c with
  | zero =>
    intro _ _
    refine ⟨cbSv_ofs, ?_⟩
    simp
  | succ c ih =>
    intro hf hB
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hf 0 (by omega))
    obtain ⟨i1, i2⟩ := ih (fun j hj => hf j (by omega)) (by push_cast at hB ⊢; linarith)
    have hc := abs_le.1 (hf c (by omega))
    have hs := abs_le.1 i2
    rw [cbK_ssum_succ, Finset.sum_range_succ, cbSv_sadd (by rw [i1]; push_cast at hB; linarith), i1]
    refine ⟨by ring, abs_le.2 ⟨?_, ?_⟩⟩ <;> push_cast <;> linarith

theorem cbSv_smul_bd {x y : ℕ} {A B : ℤ} (hx : |cbSv x| ≤ A) (hy : |cbSv y| ≤ B)
    (hAB : A * B < 4294967296) : cbSv (smul x y) = cbSv x * cbSv y ∧ |cbSv x * cbSv y| ≤ A * B := by
  have hA : 0 ≤ A := le_trans (abs_nonneg _) hx
  have hm : |cbSv x * cbSv y| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hA
  refine ⟨cbSv_smul ?_, hm⟩
  linarith [(abs_le.1 hm).1]

theorem cbSv_sadd_bd {x y : ℕ} {A B : ℤ} (hx : |cbSv x| ≤ A) (hy : |cbSv y| ≤ B)
    (hAB : A + B < 4294967296) : cbSv (sadd x y) = cbSv x + cbSv y ∧ |cbSv x + cbSv y| ≤ A + B := by
  have h1 := abs_le.1 hx
  have h2 := abs_le.1 hy
  exact ⟨cbSv_sadd (by linarith), abs_le.2 ⟨by linarith, by linarith⟩⟩

theorem cbSv_sneg_bd {x : ℕ} {A : ℤ} (hx : |cbSv x| ≤ A) (hA : A < 4294967296) :
    cbSv (sneg x) = - cbSv x ∧ |- cbSv x| ≤ A := by
  have h1 := abs_le.1 hx
  have e : sneg x = 8589934592 - x := rfl
  refine ⟨?_, by rw [abs_neg]; exact hx⟩
  rw [e]
  unfold cbSv at h1 ⊢
  omega

theorem cbSv_adjE (cb j k : ℕ) : |cbSv (adjE cb j k)| ≤ 128 := by
  have hv := fld_lt cb 8 (85 + (6 * j + k))
  have e : adjE cb j k = spk (fld cb 8 (85 + (6 * j + k)) - 128)
      (128 - fld cb 8 (85 + (6 * j + k))) := strictN_eq _ _
  rw [e, cbSv_spk _ _ (by omega), abs_le]
  have : (2 : ℕ) ^ 8 = 256 := by norm_num
  constructor <;> omega

theorem cbK_sDvd (d x : ℕ) : sDvd d x = true ↔ (d : ℤ) ∣ cbSv x := by
  unfold sDvd
  rw [beq_eq_true]
  change Nat.ModEq d x OFS ↔ _
  rw [Nat.modEq_iff_dvd]
  have e : ((OFS : ℕ) : ℤ) - x = - cbSv x := by
    unfold cbSv
    change ((4294967296 : ℕ) : ℤ) - x = _
    push_cast
    ring
  rw [e, dvd_neg]

theorem cbK_abs_iform_le {τ : Tag}
    (hsym1 : ∀ i, τ.symmetrizer i i = 1) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) : |iform α β| ≤ 2 := by
  have h2 : ∀ {x}, IsRoot τ x → iform x x = 2 := fun hx => by
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hx
    rw [hj, hsym1]
    norm_num
  by_cases e1 : α = β
  · subst e1
    rw [h2 hα]
    norm_num
  by_cases e2 : α = -β
  · subst e2
    have : iform (-β) β = -iform β β := by
      have := iform_smul_left (-1) β β
      rwa [neg_one_smul, neg_one_mul] at this
    rw [this, h2 hβ]
    norm_num
  have := iform_sq_lt hα hβ e1 e2
  rw [h2 hα, h2 hβ] at this
  rw [abs_le]
  constructor <;> nlinarith

theorem cbK_iform_sum_left {τ : Tag} {ι : Type*} (s : Finset ι) (f : ι → Fin τ.rank → ℤ)
    (y : Fin τ.rank → ℤ) : iform (∑ i ∈ s, f i) y = ∑ i ∈ s, iform (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := iform_smul_left 0 y y
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, iform_add_left, ih]

theorem cbK_iform_sum_right {τ : Tag} {ι : Type*} (s : Finset ι) (f : ι → Fin τ.rank → ℤ)
    (x : Fin τ.rank → ℤ) : iform x (∑ i ∈ s, f i) = ∑ i ∈ s, iform x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := iform_smul_right 0 x x
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, iform_add_right, ih]

theorem cbK_dlt (cb SM : ℕ) : ∀ r prev, Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun i ih prev => strictB (dlt cb i) fun g =>
      CFSG.TcRes.TK.andB (Nat.blt g prev) (CFSG.TcRes.TK.andB (bit SM g) (ih g))) r prev = true →
    ∀ j < r, bit SM (dlt cb j) = true := by
  intro r
  induction r with
  | zero => intro _ _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ r ih =>
    intro prev h0 j hj
    have h : strictB (dlt cb r) (fun g => CFSG.TcRes.TK.andB (Nat.blt g prev) (CFSG.TcRes.TK.andB (bit SM g)
        (Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true) (fun i ih prev =>
          strictB (dlt cb i) fun g => CFSG.TcRes.TK.andB (Nat.blt g prev) (CFSG.TcRes.TK.andB (bit SM g) (ih g))) r g))) =
        true := h0
    rw [strictB_eq, andB_eq_true, andB_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact ih _ h.2.2 j hj
    · exact h.2.1

theorem cbK_iter_lt {ph : ℕ → ℕ} (hph : ∀ g < 72, ph g < 72) :
    ∀ s x, x < 72 → ph^[s] x < 72 := by
  intro s
  induction s with
  | zero => intro x hx; exact hx
  | succ s ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    exact hph _ (ih x hx)

theorem cbSv_ipK {vec : ℕ → Fin Tag.E6.rank → ℤ} {X Y : ℕ}
    (hX : ∀ v < 72, ∀ g < 72, (dP 6 (fld X 192 v * fld Y 192 g) : ℤ) -
      dQ 6 (fld X 192 v * fld Y 192 g) = iform (vec v) (vec g)) {u v : ℕ} (hu : u < 72)
    (hv : v < 72) : cbSv (ipK X Y u v) = iform (vec u) (vec v) := by
  have e : ipK X Y u v = spk (dP 6 (fld X 192 u * fld Y 192 v)) (dQ 6 (fld X 192 u * fld Y 192 v)) :=
    strictN_eq _ _
  have hq : dQ 6 (fld X 192 u * fld Y 192 v) ≤ 4294967296 := by
    rw [dQ_eq]
    have := fld_lt (fld X 192 u * fld Y 192 v) 16 (2 * 6 - 1)
    have h16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
    omega
  rw [e, cbSv_spk _ _ hq, hX u hu v hv]

theorem cbK_odOK
    {vec : ℕ → Fin Tag.E6.rank → ℤ} {neg : ℕ → ℕ} {RT ADJ X Y : ℕ} {ph : ℕ → ℕ}
    {cb r SM s i i2 psi : ℕ}
    (hD : DatumRaw Tag.E6 72 vec (fun g v => rtv RT g v)
      (fun g v => Nat.beq (fld (fld ADJ 72 g) 1 v) 1) neg)
    (hX : ∀ v < 72, ∀ g < 72, (dP 6 (fld X 192 v * fld Y 192 g) : ℤ) -
      dQ 6 (fld X 192 v * fld Y 192 g) = iform (vec v) (vec g))
    (hph : ∀ g < 72, ph g < 72)
    (hen : ∀ g, g ∈ mset 72 psi ↔ ∃ j < (cb &&& 63), cbEnt (cb >>> 6) j = g)
    (hSM : ∀ g, SM.testBit g = true → g ∈ mset 72 psi)
    (hr : r ≤ 6) (h : odOK X Y ph cb r SM (cb &&& 63) s i i2 = true) :
    DiscW vec ph (mset 72 psi) s := by
  have hsym1 : ∀ i, Tag.E6.symmetrizer i i = 1 := fun i => by simp [Tag.symmetrizer]
  have hip : ∀ u < 72, ∀ v < 72, |cbSv (ipK X Y u v)| ≤ 2 := fun u hu v hv => by
    rw [cbSv_ipK hX hu hv]
    exact cbK_abs_iform_le hsym1 (hD.isRoot u hu) (hD.isRoot v hv)
  unfold odOK at h
  simp only [strictB_eq, andB_eq_true, notB_eq_true, blt_eq_true, allLt_iff] at h
  obtain ⟨hdl, -, hi, hi2, -, hdiv, hnd⟩ := h
  unfold dltOK at hdl
  have hdlt : ∀ j < r, dlt cb j ∈ mset 72 psi := fun j hj =>
    hSM _ (bit_iff.1 (cbK_dlt cb SM r 72 hdl j hj))
  have hrB : (r : ℤ) ≤ 6 := by exact_mod_cast hr
  have hrow : ∀ a < r, ∀ g ∈ mset 72 psi, ((Nat.add (fld cb 8 83) (fld cb 8 84) : ℕ) : ℤ) ∣
      iform (∑ j : Fin r, cbSv (adjE cb a j) • vec (dlt cb j)) (vec g) := by
    intro a ha g hg
    obtain ⟨jj, hjj, rfl⟩ := (hen g).1 hg
    have hl := cbK_loop2 (fun g => sDvd (Nat.add (fld cb 8 83) (fld cb 8 84))
      (ssum r fun j => smul (adjE cb a j) (ipK X Y (dlt cb j) g))) _ _ (hdiv a ha) jj hjj
    rw [cbK_sDvd] at hl
    have hterm : ∀ j < r, cbSv (smul (adjE cb a j) (ipK X Y (dlt cb j) (cbEnt (cb >>> 6) jj))) =
        cbSv (adjE cb a j) * iform (vec (dlt cb j)) (vec (cbEnt (cb >>> 6) jj)) ∧
        |cbSv (smul (adjE cb a j) (ipK X Y (dlt cb j) (cbEnt (cb >>> 6) jj)))| ≤ 128 * 2 := by
      intro j hj
      have hb := cbSv_smul_bd (cbSv_adjE cb a j) (hip _ (hdlt j hj).1 _ hg.1) (by norm_num)
      rw [hb.1, ← cbSv_ipK hX (hdlt j hj).1 hg.1]
      exact ⟨rfl, hb.2⟩
    obtain ⟨hs1, -⟩ := cbSv_ssum _ (128 * 2) r (fun j hj => (hterm j hj).2) (by linarith)
    have key : iform (∑ j : Fin r, cbSv (adjE cb a j) • vec (dlt cb j)) (vec (cbEnt (cb >>> 6) jj)) =
        cbSv (ssum r fun j => smul (adjE cb a j) (ipK X Y (dlt cb j) (cbEnt (cb >>> 6) jj))) := by
      rw [cbK_iform_sum_left]
      simp only [iform_smul_left]
      rw [Fin.sum_univ_eq_sum_range (fun j => cbSv (adjE cb a j) *
        iform (vec (dlt cb j)) (vec (cbEnt (cb >>> 6) jj))), hs1]
      exact Finset.sum_congr rfl fun j hj => (hterm j (Finset.mem_range.1 hj)).1.symm
    rw [key]
    exact hl
  refine ⟨r, fun j => dlt cb j, fun j => cbSv (adjE cb i j), fun j => cbSv (adjE cb i2 j),
    ((Nat.add (fld cb 8 83) (fld cb 8 84) : ℕ) : ℤ), fun j => hdlt j j.2, ?_, ?_, ?_⟩
  · exact fun g hg => hrow i hi g hg
  · exact fun g hg => hrow i2 hi2 g hg
  · intro hcon
    have hdk : ∀ k < r, dlt cb k < 72 := fun k hk => (hdlt k hk).1
    have hpk : ∀ k < r, phPow ph s (dlt cb k) < 72 := fun k hk => by
      rw [cbK_phPow]
      exact cbK_iter_lt hph s _ (hdk k hk)
    have hT : ∀ j < r, ∀ k < r,
        cbSv (smul (smul (adjE cb i2 j) (adjE cb i k))
          (sadd (ipK X Y (dlt cb j) (phPow ph s (dlt cb k))) (sneg (ipK X Y (dlt cb j) (dlt cb k))))) =
          cbSv (adjE cb i2 j) * cbSv (adjE cb i k) *
            (iform (vec (dlt cb j)) (vec (ph^[s] (dlt cb k))) -
              iform (vec (dlt cb j)) (vec (dlt cb k))) ∧
        |cbSv (smul (smul (adjE cb i2 j) (adjE cb i k))
          (sadd (ipK X Y (dlt cb j) (phPow ph s (dlt cb k))) (sneg (ipK X Y (dlt cb j) (dlt cb k)))))|
          ≤ 128 * 128 * (2 + 2) := by
      intro j hj k hk
      have hm := cbSv_smul_bd (cbSv_adjE cb i2 j) (cbSv_adjE cb i k) (by norm_num)
      have hn := cbSv_sneg_bd (hip _ (hdk j hj) _ (hdk k hk)) (by norm_num)
      have hn2 : |cbSv (sneg (ipK X Y (dlt cb j) (dlt cb k)))| ≤ 2 := by
        rw [hn.1]
        exact hn.2
      have ha := cbSv_sadd_bd (hip _ (hdk j hj) _ (hpk k hk)) hn2 (by norm_num)
      have hm2 : |cbSv (smul (adjE cb i2 j) (adjE cb i k))| ≤ 128 * 128 := by
        rw [hm.1]
        exact hm.2
      have ha2 : |cbSv (sadd (ipK X Y (dlt cb j) (phPow ph s (dlt cb k)))
          (sneg (ipK X Y (dlt cb j) (dlt cb k))))| ≤ 2 + 2 := by
        rw [ha.1]
        exact ha.2
      have hb := cbSv_smul_bd hm2 ha2 (by norm_num)
      refine ⟨?_, ?_⟩
      · rw [hb.1, hm.1, ha.1, hn.1, cbSv_ipK hX (hdk j hj) (hpk k hk),
          cbSv_ipK hX (hdk j hj) (hdk k hk), cbK_phPow]
        ring
      · rw [hb.1]
        exact hb.2
    have hin : ∀ j < r, cbSv (ssum r fun k => smul (smul (adjE cb i2 j) (adjE cb i k))
          (sadd (ipK X Y (dlt cb j) (phPow ph s (dlt cb k))) (sneg (ipK X Y (dlt cb j) (dlt cb k))))) =
        ∑ k ∈ Finset.range r, cbSv (adjE cb i2 j) * cbSv (adjE cb i k) *
            (iform (vec (dlt cb j)) (vec (ph^[s] (dlt cb k))) -
              iform (vec (dlt cb j)) (vec (dlt cb k))) ∧
        |cbSv (ssum r fun k => smul (smul (adjE cb i2 j) (adjE cb i k))
          (sadd (ipK X Y (dlt cb j) (phPow ph s (dlt cb k))) (sneg (ipK X Y (dlt cb j) (dlt cb k)))))|
          ≤ 6 * (128 * 128 * (2 + 2)) := by
      intro j hj
      obtain ⟨h1, h2⟩ := cbSv_ssum _ (128 * 128 * (2 + 2)) r (fun k hk => (hT j hj k hk).2)
        (by nlinarith)
      refine ⟨h1.trans (Finset.sum_congr rfl fun k hk => (hT j hj k (Finset.mem_range.1 hk)).1),
        ?_⟩
      rw [h1]
      exact le_trans h2 (by nlinarith)
    obtain ⟨ho, -⟩ := cbSv_ssum _ (6 * (128 * 128 * (2 + 2))) r (fun j hj => (hin j hj).2)
      (by nlinarith)
    rw [← Bool.not_eq_true, cbK_sDvd] at hnd
    apply hnd
    have e : ((Nat.mul (Nat.add (fld cb 8 83) (fld cb 8 84)) (Nat.add (fld cb 8 83) (fld cb 8 84)) :
        ℕ) : ℤ) = ((Nat.add (fld cb 8 83) (fld cb 8 84) : ℕ) : ℤ) *
          ((Nat.add (fld cb 8 83) (fld cb 8 84) : ℕ) : ℤ) := Nat.cast_mul _ _
    rw [e, ho, Finset.sum_congr rfl fun j hj => (hin j (Finset.mem_range.1 hj)).1]
    convert hcon using 1
    rw [cbK_iform_sum_left]
    simp only [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iform_smul_left, iform_sub_right, cbK_iform_sum_right, cbK_iform_sum_right,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iform_smul_right, iform_smul_right]
    ring

theorem cbK_kind {RT X Y : ℕ} {ph : ℕ → ℕ} {cb psi r N SM e : ℕ} {P Q : ℕ → Prop}
    (hW : ∀ s wl w, wOK RT ph psi (cb &&& 63) (cb >>> 6) s wl w = true → P s)
    (hO : ∀ s i i2, odOK X Y ph cb r SM (cb &&& 63) s i i2 = true → Q s)
    (hk : kindOf RT X Y ph cb psi r N SM e < 4) :
    (kindOf RT X Y ph cb psi r N SM e = 0 → P e ∨ (famE r N = false ∧ famD4 r N = false ∧
      famD r N = false ∧ famA r N = false)) ∧
    (kindOf RT X Y ph cb psi r N SM e = 1 → Q e ∧ famA r N = true ∧ famD r N = false ∧
      famD4 r N = false ∧ famE r N = false) ∧
    (kindOf RT X Y ph cb psi r N SM e = 2 → Q e ∧ ((famD r N = true ∧ famD4 r N = false ∧
      famE r N = false) ∨ (famD4 r N = true ∧ P (2 * e)))) ∧
    (kindOf RT X Y ph cb psi r N SM e = 3 → Q e ∧ (famE r N = true ∨
      (famD4 r N = true ∧ Q (2 * e)))) := by
  have hW1 : ∀ wl w, wOK RT ph psi (Nat.land cb (nat_lit 63)) (Nat.shiftRight cb (nat_lit 6)) e
      wl w = true → P e := fun wl w h => hW e wl w h
  have hW2 : ∀ wl w, wOK RT ph psi (Nat.land cb (nat_lit 63)) (Nat.shiftRight cb (nat_lit 6))
      (Nat.mul (nat_lit 2) e) wl w = true → P (2 * e) := fun wl w h => hW _ wl w h
  have hO1 : ∀ i i2, odOK X Y ph cb r SM (Nat.land cb (nat_lit 63)) e i i2 = true → Q e :=
    fun i i2 h => hO e i i2 h
  have hO2 : ∀ i i2, odOK X Y ph cb r SM (Nat.land cb (nat_lit 63)) (Nat.mul (nat_lit 2) e) i i2 =
      true → Q (2 * e) := fun i i2 h => hO _ i i2 h
  clear hW hO
  simp only [kindOf, strictN_eq, brecN_eq, Bool.cond_eq_ite, andB_eq, orB_eq,
    Bool.and_eq_true, Bool.or_eq_true] at hk ⊢
  split_ifs at hk ⊢ <;> (try simp only [KBAD] at hk) <;> (try omega) <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hv <;> (try simp only [KBAD] at hv) <;> (try omega) <;>
    simp_all only [Bool.not_eq_true, true_and, and_true, or_true, true_or, not_false_eq_true]
  all_goals first
    | exact Or.inl (hW1 _ _ ‹_›)
    | exact hO1 _ _ ‹_›
    | (obtain ⟨-, h2, h3⟩ := ‹_ = true ∧ _ = true ∧ _ = true›
       first
        | exact ⟨hO1 _ _ h2, Or.inr (hW2 _ _ h3)⟩
        | exact ⟨hO1 _ _ h2, Or.inr (hO2 _ _ h3)⟩)
    | (have hn := ‹¬ (_ ∨ _)›
       simp only [not_or, Bool.not_eq_true] at hn
       exact Or.inr hn)

theorem compRaw_of_cbK {vec : ℕ → Fin Tag.E6.rank → ℤ} {neg : ℕ → ℕ}
    {RT X Y ADJ POS DEC V : ℕ} {ph : ℕ → ℕ} {cb Φ g0 : ℕ} {k : ℕ → ℕ → Bool}
    (hvec : vec = vecOf 6 V)
    (hD : DatumRaw Tag.E6 72 vec (fun g v => rtv RT g v)
      (fun g v => Nat.beq (fld (fld ADJ 72 g) 1 v) 1) neg)
    (hX : ∀ v < 72, ∀ g < 72, (dP 6 (fld X 192 v * fld Y 192 g) : ℤ) -
      dQ 6 (fld X 192 v * fld Y 192 g) = iform (vec v) (vec g))
    (hpos : ∀ g < 72, posOK V POS g = true) (hdec : ∀ g < 72, decOK RT X Y POS DEC g = true)
    (hph : ∀ g < 72, ph g < 72)
    (hΦsub : ∀ a ∈ mset 72 Φ, ∀ b ∈ mset 72 Φ, ∀ c < 72, vec c = vec a - vec b → c ∈ mset 72 Φ)
    (h : cbK RT X Y ADJ POS DEC ph cb Φ g0 k = true) :
    ∃ ψ d r0, k ψ d = true ∧
      CompRaw vec (fun g v => rtv RT g v) ph 72 (mset 72 Φ) (mset 72 ψ) g0 d r0 ∧
      KindRaw vec (fun g v => rtv RT g v) ph (mset 72 ψ) d := by
  simp only [cbK, strictB_eq, andB_eq_true, blt_eq_true] at h
  obtain ⟨hlt, hg0, he0, hkd, hk⟩ := h
  generalize hpsi : treeM ADJ Φ (cb &&& 63) (cb >>> 6) 0 0 = psi at hlt hg0 he0 hkd hk
  generalize hsm : simpM POS DEC psi (cb &&& 63) (cb >>> 6) 0 = sm at hkd hk
  generalize he : olen ph psi 12 ((cb >>> 6) &&& 127) 1 = e at he0 hkd hk
  have hlt' : psi < 2 ^ 72 := hlt
  rw [bit_iff] at hg0
  obtain ⟨hc0, hen, hinj, hsub, hconn, hcl⟩ := cbK_tree hD hpsi hlt'
  obtain ⟨hr6, S, hS, hSiff⟩ := cbK_simple hvec hD hX hpos hdec hΦsub hen hinj hsub hcl
  rw [hsm] at hr6 hS
  obtain ⟨he1, he12, hein, heout⟩ := cbK_olen ph psi 12 ((cb >>> 6) &&& 127) 1 (he ▸ he0)
  rw [he] at he1 he12 hein heout
  have hc64 : cb &&& 63 < 64 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hentlt : ∀ j < cb &&& 63, cbEnt (cb >>> 6) j < 72 := fun j hj => ((hen _).2 ⟨j, hj, rfl⟩).1
  have hSM : ∀ g, (Nat.land sm (Nat.sub (Nat.shiftLeft 1 72) 1)).testBit g = true →
      g ∈ mset 72 psi := by
    intro g hg
    have e1 : Nat.sub (Nat.shiftLeft 1 72) 1 = 2 ^ 72 - 1 := rfl
    rw [e1, nland, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow, Bool.and_eq_true,
      decide_eq_true_eq] at hg
    rw [← hsm] at hg
    rcases cbK_simpM_mask POS DEC psi _ _ 0 hentlt g hg.1 hg.2 with h0 | ⟨j, hj, rfl⟩
    · simp at h0
    · exact (hen _).2 ⟨j, hj, rfl⟩
  have hK := cbK_kind (P := InnerW (fun g v => rtv RT g v) ph (mset 72 psi))
    (Q := DiscW vec ph (mset 72 psi)) (fun s wl w hw => cbK_wOK hlt' hen hw)
    (fun s i i2 ho => cbK_odOK hD hX hph hen hSM hr6 ho) hkd
  generalize hkd' : kindOf RT X Y ph cb psi (Nat.shiftRight sm 80) (Nat.land cb 63)
    (Nat.land sm (Nat.sub (Nat.shiftLeft 1 72) 1)) e = kd at hkd hk hK
  obtain ⟨hdE, hdR, hdN, hdK⟩ := cbK_dcode (e := e) (r := sm >>> 80) (c := cb &&& 63) (kd := kd)
    (by omega) (by omega) (by omega)
  have hroot : (cb >>> 6) &&& 127 ∈ mset 72 psi := (hen _).2 ⟨0, hc0, cbEnt_zero _⟩
  refine ⟨psi, e + (16 * (sm >>> 80) + (256 * (cb &&& 63) + 65536 * kd)), (cb >>> 6) &&& 127,
    hk, ⟨hsub, ⟨cbK_lt72 hlt' hg0, bit_iff.2 hg0⟩, hroot, ?_, hcl, fun g hg => hg.1, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ?_⟩
  · intro g hg
    rw [← cbEnt_zero]
    exact hconn g hg
  · rw [hdE]; omega
  · rw [hdE]; omega
  · rw [hdE, Nat.sub_add_cancel he1] at *
    exact ⟨cbK_lt72 hlt' hein, bit_iff.2 hein⟩
  · intro s hs1 hs2
    rw [hdE] at hs2
    have h4 := heout s hs1 hs2
    rw [Nat.sub_add_cancel hs1] at h4
    rintro ⟨-, hb⟩
    rw [bit_iff, h4] at hb
    exact absurd hb (by decide)
  · rw [hdN]; exact cbK_ncard hen hinj
  · exact ⟨S, hS.trans hdR.symm, hSiff⟩
  · refine ⟨by rw [hdK]; exact hkd, ?_, ?_, ?_, ?_⟩ <;> simp only [hdE, hdR, hdN, hdK]
    · exact hK.1
    · exact hK.2.1
    · exact hK.2.2.1
    · exact hK.2.2.2

end CbK

theorem rt_eq_rootReflection
    {N : ℕ} {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    (hD : DatumRaw τ N vec rt adj neg) (hsym1 : ∀ i, τ.symmetrizer i i = 1) {l v : ℕ}
    (hl : l < N) (hv : v < N) : vec (rt l v) = rootReflection (vec l) • vec v := by
  have hr := hD.isRoot l hl
  rw [(hD.refl l hl v hv).2, rootReflection_smul hr]
  have h1 := corootPair_mul hr (vec v)
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hr
  rw [hj, hsym1] at h1
  rw [iform_comm (vec v)]
  congr 2
  linarith

theorem twistInner_of_innerW
    {N : ℕ} {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    (hD : DatumRaw τ N vec rt adj neg) (hsym1 : ∀ i, τ.symmetrizer i i = 1) {ph : ℕ → ℕ}
    {ψ : Set ℕ} (hψ : ∀ g ∈ ψ, g < N) (hphN : ∀ g < N, ph g < N) {s : ℕ}
    (σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) (hσ : ∀ g ∈ ψ, σ (vec g) = vec (ph^[s] g))
    (hw : InnerW rt ph ψ s) : twistInner (vec '' ψ) σ := by
  obtain ⟨wd, hwd, hfix⟩ := hw
  have hiter' : ∀ t g, g < N → ph^[t] g < N := by
    intro t
    induction t with
    | zero => exact fun g hg => hg
    | succ t ih =>
      intro g hg
      rw [Function.iterate_succ_apply']
      exact hphN _ (ih g hg)
  have hiter : ∀ g < N, ph^[s] g < N := fun g hg => hiter' s g hg
  have claim : ∀ (wd : List ℕ), (∀ l ∈ wd, l ∈ ψ) →
      ∃ u ∈ Subgroup.closure {x : WeylGroup τ | ∃ γ ∈ vec '' ψ, x = rootReflection γ},
        ∀ v < N, wd.foldl (fun v l => rt l v) v < N ∧
          vec (wd.foldl (fun v l => rt l v) v) = u • vec v := by
    intro wd
    induction wd with
    | nil => exact fun _ => ⟨1, Subgroup.one_mem _, fun v hv => ⟨hv, by simp⟩⟩
    | cons l wd ih =>
      intro hl
      have hlψ : l ∈ ψ := hl l List.mem_cons_self
      have hlN : l < N := hψ l hlψ
      obtain ⟨u, hu, hall⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      refine ⟨u * rootReflection (vec l), Subgroup.mul_mem _ hu
        (Subgroup.subset_closure ⟨vec l, ⟨l, hlψ, rfl⟩, rfl⟩), fun v hv => ?_⟩
      have hrv := (hD.refl l hlN v hv).1
      obtain ⟨h1, h2⟩ := hall _ hrv
      simp only [List.foldl_cons]
      refine ⟨h1, ?_⟩
      rw [h2, rt_eq_rootReflection hD hsym1 hlN hv, mul_smul]
  obtain ⟨u, hu, hall⟩ := claim wd hwd
  refine ⟨u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
  rintro γ ⟨g, hg, rfl⟩
  have key := (hall _ (hiter g (hψ g hg))).2
  rw [hfix g hg] at key
  rw [hσ g hg, key, inv_smul_smul]

theorem not_twistInner_of_discW
    {N : ℕ} {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    (hD : DatumRaw τ N vec rt adj neg) (hsym1 : ∀ i, τ.symmetrizer i i = 1) {ph : ℕ → ℕ}
    {ψ : Set ℕ} (hψ : ∀ g ∈ ψ, g < N) {s : ℕ} (σ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hσ : ∀ g ∈ ψ, σ (vec g) = vec (ph^[s] g)) (hw : DiscW vec ph ψ s) :
    ¬ twistInner (vec '' ψ) σ := by
  obtain ⟨r, dl, a, b, D, hdl, hμ, hν, hnd⟩ := hw
  have hroot : ∀ γ ∈ vec '' ψ, IsRoot τ γ := by
    rintro γ ⟨g, hg, rfl⟩
    exact hD.isRoot g (hψ g hg)
  have hsl : ∀ γ ∈ vec '' ψ, iform γ γ = 2 := by
    intro γ hγ
    obtain ⟨j, hj⟩ := iform_self_of_isRoot (hroot γ hγ)
    rw [hj, hsym1]
    norm_num
  have hσμ : σ (∑ j, a j • vec (dl j)) = ∑ j, a j • vec (ph^[s] (dl j)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, hσ _ (hdl j)]
  refine CFSG.StandardType.TableCRes.not_twistInner_of_disc hroot hsl σ (d := D)
    (μ := ∑ j, a j • vec (dl j)) (ν := ∑ j, b j • vec (dl j)) ?_ ?_ ?_ ?_
  · exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨dl j, hdl j, rfl⟩)
  · rintro γ ⟨g, hg, rfl⟩
    exact hμ g hg
  · rintro γ ⟨g, hg, rfl⟩
    exact hν g hg
  · rw [hσμ]
    exact hnd

theorem vec_iterate_all {N : ℕ} {vec : ℕ → Fin τ.rank → ℤ} {ph : ℕ → ℕ}
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hphN : ∀ g < N, ph g < N)
    (hph : ∀ g < N, vec (ph g) = ρ (vec g)) (s : ℕ) :
    ∀ g < N, ph^[s] g < N ∧ vec (ph^[s] g) = (⇑ρ)^[s] (vec g) := by
  induction s with
  | zero => exact fun g hg => ⟨hg, rfl⟩
  | succ s ih =>
    intro g hg
    obtain ⟨h1, h2⟩ := ih g hg
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← h2]
    exact ⟨hphN _ h1, hph _ h1⟩

theorem orbitLength_of_compRaw
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {N : ℕ} {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {ph : ℕ → ℕ} {Φ ψ : Set ℕ}
    {g0 d r0 : ℕ}
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hker : kernelRoots χ = ρ '' kernelRoots χ)
    (hform : ∀ α ∈ kernelRoots χ, ∀ β ∈ kernelRoots χ, iform (ρ α) (ρ β) = iform α β)
    (hΦ : vec '' Φ = kernelRoots χ) (hphN : ∀ g < N, ph g < N)
    (hph : ∀ g < N, vec (ph g) = ρ (vec g)) (hinj : ∀ a < N, ∀ b < N, vec a = vec b → a = b)
    (h : CompRaw vec rt ph N Φ ψ g0 d r0) :
    ∃ i : KernelComponent χ, componentRoots χ i = vec '' ψ ∧
      componentOrbitLength ρ (componentRoots χ i) = dE d := by
  obtain ⟨i, hi⟩ := exists_componentRoots_eq_image hΦ h.sub h.root_mem h.conn h.closed
  refine ⟨i, hi, ?_⟩
  have hrN : r0 < N := h.lt _ h.root_mem
  have hmemiff : ∀ s, ((⇑ρ)^[s] (vec r0) ∈ componentRoots χ i ↔ ph^[s] r0 ∈ ψ) := by
    intro s
    obtain ⟨h1, h2⟩ := vec_iterate_all ρ hphN hph s _ hrN
    rw [hi, ← h2]
    constructor
    · rintro ⟨g, hg, hgv⟩
      rw [← hinj _ (h.lt g hg) _ h1 hgv]
      exact hg
    · intro hm
      exact ⟨_, hm, rfl⟩
  refine componentOrbitLength_eq_of_first ρ hker hform i ?_ h.e_pos ((hmemiff _).2 h.e_in)
    fun s h1 h2 hm => h.e_out s h1 h2 ((hmemiff s).1 hm)
  rw [hi]
  exact ⟨_, h.root_mem, rfl⟩

theorem ncard_of_compRaw {N : ℕ} {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {ph : ℕ → ℕ}
    {Φ ψ : Set ℕ} {g0 d r0 : ℕ} (hinj : ∀ a < N, ∀ b < N, vec a = vec b → a = b)
    (h : CompRaw vec rt ph N Φ ψ g0 d r0) : (vec '' ψ).ncard = dN d := by
  have hio : Set.InjOn vec ψ := fun a ha b hb hab => hinj a (h.lt a ha) b (h.lt b hb) hab
  rw [hio.ncard_image, h.card]

theorem compRank_of_compRaw {N : ℕ}
    {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {ph : ℕ → ℕ}
    {Φ ψ : Set ℕ} {g0 d r0 : ℕ} (hinj : ∀ a < N, ∀ b < N, vec a = vec b → a = b)
    (h : CompRaw vec rt ph N Φ ψ g0 d r0) (hΨ : IsRootComponent (vec '' ψ)) :
    compRank (vec '' ψ) = dR d := by
  classical
  obtain ⟨S, hS, hSm⟩ := h.simple
  rw [CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ, ← hS]
  have himg : simpleRoots (vec '' ψ) = S.image vec := by
    ext β
    rw [Finset.mem_image]
    constructor
    · intro hβ
      obtain ⟨g, hg, rfl⟩ : β ∈ vec '' ψ := ((mem_simpleRoots.1 hβ).2.1).1
      exact ⟨g, (hSm g).2 ⟨hg, hβ⟩, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ((hSm g).1 hg).2
  rw [himg, Finset.card_image_of_injOn]
  intro a ha b hb hab
  exact hinj a (h.lt a ((hSm a).1 ha).1) b (h.lt b ((hSm b).1 hb).1) hab

theorem famA_iff (r N : ℕ) : famA r N = true ↔ 2 ≤ r ∧ N = r * (r + 1) := by
  simp [famA, andB_eq, nble_eq, nbeq_eq, nmul_eq]

theorem famD_iff (r N : ℕ) : famD r N = true ↔ 4 ≤ r ∧ N = 2 * r * (r - 1) := by
  simp [famD, andB_eq, nble_eq, nbeq_eq, nmul_eq, nsub_eq]

theorem famE_iff (r N : ℕ) : famE r N = true ↔ r = 6 ∧ N = 72 := by
  simp [famE, andB_eq, nbeq_eq]

theorem famD4_iff (r N : ℕ) : famD4 r N = true ↔ r = 4 ∧ N = 24 := by
  simp [famD4, andB_eq, nbeq_eq]

theorem kind_of_kindRaw {N : ℕ}
    {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    (hD : DatumRaw τ N vec rt adj neg) (hsym1 : ∀ i, τ.symmetrizer i i = 1) {ph : ℕ → ℕ}
    {ψ : Set ℕ} {d : ℕ} (hψ : ∀ g ∈ ψ, g < N) (hphN : ∀ g < N, ph g < N)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (φ : AddMonoid.End (Fin τ.rank → ℤ))
    (hφ : ∀ g < N, vec (ph g) = φ (vec g)) (hρ : ∀ g < N, ρ (vec g) = φ (vec g))
    (he : componentOrbitLength ρ (vec '' ψ) = dE d) (hr : compRank (vec '' ψ) = dR d)
    (hN : (vec '' ψ).ncard = dN d) (hk : KindRaw vec rt ph ψ d) :
    CFSG.StandardType.TableCRes.tcrKindOfK
      (CFSG.StandardType.TableCRes.twistKindOf ρ (vec '' ψ)) = tkKind (dK d) := by
  have hpow : ∀ s, ∀ g < N, ph^[s] g < N ∧ vec (ph^[s] g) = (φ ^ s) (vec g) ∧
      (⇑ρ)^[s] (vec g) = (φ ^ s) (vec g) := by
    intro s
    induction s with
    | zero => exact fun g hg => ⟨hg, rfl, rfl⟩
    | succ s ih =>
      intro g hg
      obtain ⟨h1, h2, h3⟩ := ih g hg
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ']
      refine ⟨hphN _ h1, ?_, ?_⟩
      · rw [hφ _ h1, h2]
        rfl
      · rw [h3, ← h2, hρ _ h1, h2]
        rfl
  have hI : ∀ s, InnerW rt ph ψ s → twistInner (vec '' ψ) ((⇑ρ)^[s]) := fun s hw =>
    twistInner_of_innerW hD hsym1 hψ hphN _ (fun g hg => by
      rw [(hpow s g (hψ g hg)).2.2, (hpow s g (hψ g hg)).2.1]) hw
  have hO : ∀ s, DiscW vec ph ψ s → ¬ twistInner (vec '' ψ) ((⇑ρ)^[s]) := by
    intro s hw hin
    refine not_twistInner_of_discW hD hsym1 hψ (φ ^ s)
      (fun g hg => (hpow s g (hψ g hg)).2.1.symm) hw ?_
    obtain ⟨w, hw', hσ⟩ := hin
    refine ⟨w, hw', ?_⟩
    rintro γ ⟨g, hg, rfl⟩
    exact ((hpow s g (hψ g hg)).2.2).symm.trans (hσ _ ⟨g, hg, rfl⟩)
  have hfA := famA_iff (dR d) (dN d)
  have hfD := famD_iff (dR d) (dN d)
  have hfE := famE_iff (dR d) (dN d)
  have hfD4 := famD4_iff (dR d) (dN d)
  unfold CFSG.StandardType.TableCRes.twistKindOf
  rw [he, hr, hN]
  have hlt := hk.lt
  have hcases : dK d = 0 ∨ dK d = 1 ∨ dK d = 2 ∨ dK d = 3 := by omega
  rcases hcases with h0 | h0 | h0 | h0
  · rw [h0]
    rcases hk.inner h0 with hw | ⟨e1, e2, e3, e4⟩
    · rw [if_pos (hI _ hw)]
      rfl
    · have n1 : ¬(dR d = 6 ∧ dN d = 72) := fun hp => by simp [hfE.2 hp] at e1
      have n2 : ¬(dR d = 4 ∧ dN d = 24) := fun hp => by simp [hfD4.2 hp] at e2
      have n3 : ¬(4 ≤ dR d ∧ dN d = 2 * dR d * (dR d - 1)) := fun hp => by simp [hfD.2 hp] at e3
      have n4 : ¬(2 ≤ dR d ∧ dN d = dR d * (dR d + 1)) := fun hp => by simp [hfA.2 hp] at e4
      by_cases h1 : twistInner (vec '' ψ) (⇑ρ)^[dE d]
      · rw [if_pos h1]
        rfl
      · rw [if_neg h1, if_neg (fun hc => hc.elim n1 fun h => n2 ⟨h.1, h.2.1⟩), if_neg n3,
          if_neg n4]
        rfl
  · rw [h0]
    obtain ⟨hw, e1, e2, e3, e4⟩ := hk.suN h0
    have n2 : ¬(dR d = 4 ∧ dN d = 24) := fun hp => by simp [hfD4.2 hp] at e3
    have n3 : ¬(4 ≤ dR d ∧ dN d = 2 * dR d * (dR d - 1)) := fun hp => by simp [hfD.2 hp] at e2
    have n1 : ¬(dR d = 6 ∧ dN d = 72) := fun hp => by simp [hfE.2 hp] at e4
    rw [if_neg (hO _ hw), if_neg (fun hc => hc.elim n1 fun h => n2 ⟨h.1, h.2.1⟩), if_neg n3,
      if_pos (hfA.1 e1)]
    rfl
  · rw [h0]
    obtain ⟨hw, hc⟩ := hk.twoD h0
    rw [if_neg (hO _ hw)]
    rcases hc with ⟨e1, e2, e3⟩ | ⟨e1, hw2⟩
    · have n2 : ¬(dR d = 4 ∧ dN d = 24) := fun hp => by simp [hfD4.2 hp] at e2
      have n1 : ¬(dR d = 6 ∧ dN d = 72) := fun hp => by simp [hfE.2 hp] at e3
      rw [if_neg (fun hc => hc.elim n1 fun h => n2 ⟨h.1, h.2.1⟩), if_pos (hfD.1 e1)]
      rfl
    · obtain ⟨hr4, hn24⟩ := hfD4.1 e1
      have hin2 := hI _ hw2
      have hx : ¬((dR d = 6 ∧ dN d = 72) ∨ (dR d = 4 ∧ dN d = 24 ∧
          ¬ twistInner (vec '' ψ) (⇑ρ)^[2 * dE d])) := by
        rintro (⟨a, _⟩ | ⟨_, _, c⟩)
        · omega
        · exact c hin2
      have hy : 4 ≤ dR d ∧ dN d = 2 * dR d * (dR d - 1) := by
        rw [hr4, hn24]
        decide
      rw [if_neg hx, if_pos hy]
      rfl
  · rw [h0]
    obtain ⟨hw, hc⟩ := hk.exc h0
    rw [if_neg (hO _ hw)]
    rcases hc with e1 | ⟨e1, hw2⟩
    · rw [if_pos (Or.inl (hfE.1 e1))]
      rfl
    · rw [if_pos (Or.inr ⟨(hfD4.1 e1).1, (hfD4.1 e1).2, hO _ hw2⟩)]
      rfl

theorem tcDataOK_of_compRaw
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {N : ℕ}
    {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    (hD : DatumRaw τ N vec rt adj neg) (hsym1 : ∀ i, τ.symmetrizer i i = 1) {ph : ℕ → ℕ}
    {Φ ψ : Set ℕ} {g0 d r0 : ℕ} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (φ : AddMonoid.End (Fin τ.rank → ℤ)) (hker : kernelRoots χ = ρ '' kernelRoots χ)
    (hform : ∀ α ∈ kernelRoots χ, ∀ β ∈ kernelRoots χ, iform (ρ α) (ρ β) = iform α β)
    (hΦ : vec '' Φ = kernelRoots χ) (hphN : ∀ g < N, ph g < N)
    (hφ : ∀ g < N, vec (ph g) = φ (vec g)) (hρ : ∀ g < N, ρ (vec g) = φ (vec g))
    (h : CompRaw vec rt ph N Φ ψ g0 d r0) (hk : KindRaw vec rt ph ψ d) :
    ∃ i : KernelComponent χ, componentRoots χ i = vec '' ψ ∧
      CFSG.StandardType.TableCRes.TcDataOK ρ (componentRoots χ i) (tkCd d) := by
  have hph : ∀ g < N, vec (ph g) = ρ (vec g) := fun g hg => (hφ g hg).trans (hρ g hg).symm
  obtain ⟨i, hi, he⟩ := orbitLength_of_compRaw ρ hker hform hΦ hphN hph hD.inj h
  have hΨ : IsRootComponent (vec '' ψ) := hi ▸ isRootComponent_componentRoots i
  have hr := compRank_of_compRaw hD.inj h hΨ
  have hN := ncard_of_compRaw hD.inj h
  refine ⟨i, hi, ?_, ?_, ?_, ?_⟩
  · exact he.symm
  · rw [hi, hr]
    rfl
  · rw [hi, hN]
    rfl
  · rw [hi, kind_of_kindRaw hD hsym1 h.lt hphN ρ φ hφ hρ (hi ▸ he) hr hN hk]
    exact List.mem_singleton_self _

theorem fld_fld (T W w g v : ℕ) (h : w * v + w ≤ W) :
    fld (fld T W g) w v = Nat.land (Nat.shiftRight T (W * g + w * v))
      (Nat.sub (Nat.shiftLeft 1 w) 1) := by
  have e1 : ∀ a b : ℕ, Nat.land a b = a &&& b := fun _ _ => rfl
  have e2 : ∀ a b : ℕ, Nat.shiftRight a b = a >>> b := fun _ _ => rfl
  have e3 : ∀ k : ℕ, Nat.sub (Nat.shiftLeft 1 k) 1 = 2 ^ k - 1 := fun k => by
    rw [nsub_eq]
    congr 1
    exact (Nat.shiftLeft_eq 1 k).trans (one_mul _)
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [fld, e1, e2, e3, nmul_eq]
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < w
  · have h1 : w * v + i < W := by nlinarith
    have h2 : W * g + (w * v + i) = W * g + w * v + i := by ring
    simp [hi, h1, h2]
  · simp [hi]

theorem rtv_eq_fld (RT g v : ℕ) (hv : v < 72) : rtv RT g v = fld (fld RT 504 g) 7 v := by
  rw [fld_fld RT 504 7 g v (by omega)]
  have h2 : (g * 72 + v) * 7 = 504 * g + 7 * v := by ring
  simp only [rtv, nmul_eq, nadd_eq, h2]
  rfl

theorem compRaw_of_crK8
    {vec : ℕ → Fin Tag.E8.rank → ℤ} {neg : ℕ → ℕ}
    {ADJ POS DEC V X Y : ℕ} {RTs QS MVS : ℕ → ℕ} {ph : ℕ → ℕ} {cr Φ g0 : ℕ}
    {k : ℕ → ℕ → Bool} (hvec : vec = vecOf 8 V)
    (hD : DatumRaw Tag.E8 240 vec (fun g v => fld (RTs g) 8 v)
      (fun g v => Nat.beq (fld (fld ADJ 240 g) 1 v) 1) neg)
    (hX : ∀ v < 240, ∀ g < 240, (dP 8 (fld X 256 v * fld Y 256 g) : ℤ) -
      dQ 8 (fld X 256 v * fld Y 256 g) = iform (vec v) (vec g))
    (hq : ∀ i < 240, qOK QS V i = true) (hmv : ∀ x < 240, mvOK QS Y MVS x = true)
    (hpos : ∀ g < 240, pos8OK V POS g = true) (hdec : ∀ g < 240, dec8OK QS MVS V POS DEC g = true)
    (hph : ∀ g < 240, ph g < 240)
    (hΦsub : ∀ a ∈ mset 240 Φ, ∀ b ∈ mset 240 Φ, ∀ c < 240, vec c = vec a - vec b →
      c ∈ mset 240 Φ)
    (hVl : ∀ i < 240, ∀ m < 8, fld (fld V 128 i) 16 m < 16)
    (hYc : ∀ g < 240, ∀ m : Fin Tag.E8.rank, (fld (fld Y 256 g) 16 (7 - m) : ℤ) -
      fld (fld Y 256 g) 16 (15 - m) = ∑ k, Tag.E8.symmetrizedCartan m k * vec g k)
    (hYl : ∀ g < 240, ∀ j, fld (fld Y 256 g) 16 j ≤ 3) (hQb : ∀ m < 8, QS m < 2 ^ (16 * 240))
    (h : crK8 ADJ POS DEC ph cr Φ g0 k = true) :
    ∃ ψ d r0, k ψ d = true ∧
      CompRaw vec (fun g v => fld (RTs g) 8 v) ph 240 (mset 240 Φ) (mset 240 ψ) g0 d r0 ∧
      dKs d = ksOf (dR d) (dN d) := by
  classical
  simp only [crK8, Lane.strictB_eq] at h
  generalize hc : Nat.land cr 127 = c at h
  generalize hrest : Nat.shiftRight cr 15 = rest at h
  generalize hpsi : treeM8 ADJ Φ c rest 0 0 = psi at h
  generalize he : olen ph psi 12 (Nat.land rest 255) 1 = e at h
  generalize hr : simpN8 POS DEC psi c rest 0 = r at h
  simp only [Lane.andB_eq_true, Lane.blt_eq_true] at h
  obtain ⟨hlt, hg0, hepos, hk⟩ := h
  have h240 : Nat.shiftLeft 1 240 = 2 ^ 240 := by decide
  rw [h240] at hlt
  have hc128 : c < 128 := by
    rw [← hc]
    exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := treeM8_spec hpsi hlt
  have hbit : ∀ x, psi.testBit x = true → x < 240 := fun x hx => by
    by_contra hx'
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt
      (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hx
    exact absurd hx (by decide)
  have hmem : ∀ x, x ∈ mset 240 psi ↔ psi.testBit x = true := fun x => by
    change x < 240 ∧ bit psi x = true ↔ _
    rw [Lane.bit_iff]
    exact ⟨fun h => h.2, fun h => ⟨hbit x h, h⟩⟩
  have hmemΦ : ∀ x, x ∈ mset 240 Φ ↔ x < 240 ∧ Φ.testBit x = true := fun x => by
    change x < 240 ∧ bit Φ x = true ↔ _
    rw [Lane.bit_iff]
  have hψN : ∀ g ∈ mset 240 psi, g < 240 := fun g hg => hg.1
  have hψΦ : mset 240 psi ⊆ mset 240 Φ := fun x hx => by
    rw [hmem] at hx
    exact (hmemΦ x).2 ⟨hbit x hx, (t2 x hx).1⟩
  have hclosed : ∀ g ∈ mset 240 psi, ∀ h ∈ mset 240 Φ, iform (vec g) (vec h) ≠ 0 →
      h ∈ mset 240 psi := by
    intro g hg x hx hne
    rw [hmem] at hg ⊢
    obtain ⟨hxl, hxΦ⟩ := (hmemΦ x).1 hx
    have ha := (hD.adj g (hbit g hg) x hxl).2 (by rwa [iform_comm])
    rw [Lane.beq_eq_true, Lane.fld_one_eq_one] at ha
    exact t3 g hg x ha hxΦ
  obtain ⟨o1, o2, o3, o4⟩ := olen8_spec ph psi 12 (Nat.land rest 255) 1 le_rfl (he ▸ hepos)
  rw [he] at o1 o2 o3 o4
  rw [Nat.add_sub_cancel] at o3 o4
  have hsym1 : ∀ i, Tag.E8.symmetrizer i i = 1 := fun i => by simp [Tag.symmetrizer]
  have hsimp : ∀ g ∈ mset 240 psi, (vec g ∈ simpleRoots (vec '' mset 240 psi) ↔
      CFSG.TcRes.TK.andB (bit POS g) (Nat.beq (Nat.land (fld DEC 240 g) psi) 0) = true) := by
    intro g hg
    rw [simple_of_dec (pos := fun g => bit POS g = true)
      (dec := fun g d => bit (fld DEC 240 g) d = true) hD hsym1
      (fun g hg => pos8_iff hvec (hpos g hg))
      (fun g hg d hd => dec8_iff hD hvec hVl hYc hYl hQb hq hmv hpos hdec hg hd)
      hψN hψΦ hclosed hΦsub hg]
    rw [Lane.andB_eq_true, Lane.beq_eq_true, land_eq_zero_iff]
    refine and_congr Iff.rfl ⟨fun h x hx => ?_, fun h d hd => ?_⟩
    · have := h x ((hmem x).2 hx)
      rw [Lane.bit_iff] at this
      simpa using this
    · rw [Lane.bit_iff, h d ((hmem d).1 hd)]
      decide
  set S := ((Finset.range c).filter (fun i => CFSG.TcRes.TK.andB (bit POS (ent8 rest i))
    (Nat.beq (Nat.land (fld DEC 240 (ent8 rest i)) psi) 0) = true)).image (ent8 rest) with hS
  have hSmem : ∀ g, g ∈ S ↔ g ∈ mset 240 psi ∧ vec g ∈ simpleRoots (vec '' mset 240 psi) := by
    intro g
    rw [hS, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [Finset.mem_filter, Finset.mem_range] at hi
      have hgm : ent8 rest i ∈ mset 240 psi := (hmem _).2 ((t5 _).2 ⟨i, hi.1, rfl⟩)
      exact ⟨hgm, (hsimp _ hgm).2 hi.2⟩
    · rintro ⟨hg, hs⟩
      obtain ⟨i, hi, rfl⟩ := (t5 g).1 ((hmem g).1 hg)
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, (hsimp _ hg).1 hs⟩, rfl⟩
  have hScard : S.card = r := by
    rw [hS, Finset.card_image_of_injOn (fun i hi j hj hij => t6 i
      (Finset.mem_range.1 (Finset.mem_filter.1 hi).1) j
      (Finset.mem_range.1 (Finset.mem_filter.1 hj).1) hij), ← hr, simpN8_eq, zero_add,
      Finset.card_filter]
  have hr8 : r ≤ 8 := by
    rw [← hScard]
    exact card_simple_le hD hsym1 hψN hψΦ hclosed hΦsub S (fun g hg => (hSmem g).1 hg)
  obtain ⟨dE_eq, dR_eq, dN_eq, dKs_eq⟩ := code8_dec (e := e) (r := r) (c := c) (ks := ksOf r c) (by omega) (by omega)
    (by omega) rfl
  refine ⟨psi, _, Nat.land rest 255, hk, ⟨hψΦ, (hmem g0).2 (Lane.bit_iff.1 hg0), (hmem _).2 t1,
    fun g hg => ?_, hclosed, hψN, ?_, ?_, ?_, fun s hs1 hs2 => ?_, ?_, ⟨S, ?_, hSmem⟩⟩, ?_⟩
  ·
    have hj := (t2 g ((hmem g).1 hg)).2
    unfold TJoin at hj
    clear hg
    induction hj with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih =>
      refine ih.tail ⟨(hmem _).2 hab.1, (hmem _).2 hab.2.1, ?_⟩
      have ha := (hD.adj _ (hbit _ hab.2.1) _ (hbit _ hab.1)).1
      apply ha
      rw [Lane.beq_eq_true, Lane.fld_one_eq_one]
      exact hab.2.2
  · rw [dE_eq]
    exact hepos
  · rw [dE_eq]
    omega
  · rw [dE_eq, hmem]
    rw [← Lane.bit_iff]
    exact o3
  · rw [dE_eq] at hs2
    rw [hmem, ← Lane.bit_iff, o4 s hs1 hs2]
    decide
  · rw [dN_eq]
    have e : mset 240 psi = ↑((Finset.range 256).filter (fun x => psi.testBit x = true)) := by
      ext x
      rw [hmem, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
      exact ⟨fun h => ⟨by have := hbit x h; omega, h⟩, fun h => h.2⟩
    rw [e, Set.ncard_coe_finset, t4]
  · rw [dR_eq, hScard]
  · rw [dKs_eq, dR_eq, dN_eq]

theorem bit_ksOf (a b c : Bool) :
    bit (1 + (2 * b2n a + (4 * b2n b + 8 * b2n c))) 0 = true ∧
    bit (1 + (2 * b2n a + (4 * b2n b + 8 * b2n c))) 1 = a ∧
    bit (1 + (2 * b2n a + (4 * b2n b + 8 * b2n c))) 2 = b ∧
    bit (1 + (2 * b2n a + (4 * b2n b + 8 * b2n c))) 3 = c := by
  cases a <;> cases b <;> cases c <;> decide

theorem mem_tkKs {m k : ℕ} (hk : k < 4) (hb : bit m k = true) : tkKind k ∈ tkKs m := by
  simp only [tkKs, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨k, ⟨hk, hb⟩, rfl⟩

theorem kind_mem_ksOf {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)} :
    CFSG.StandardType.TableCRes.tcrKindOfK (CFSG.StandardType.TableCRes.twistKindOf ρ Ψ) ∈
      tkKs (ksOf (compRank Ψ) Ψ.ncard) := by
  obtain ⟨b0, b1, b2, b3⟩ := bit_ksOf (famA (compRank Ψ) Ψ.ncard) (famD (compRank Ψ) Ψ.ncard)
    (CFSG.TcRes.TK.orB (famE (compRank Ψ) Ψ.ncard) (famD4 (compRank Ψ) Ψ.ncard))
  have hks : ksOf (compRank Ψ) Ψ.ncard = 1 + (2 * b2n (famA (compRank Ψ) Ψ.ncard) +
      (4 * b2n (famD (compRank Ψ) Ψ.ncard) +
        8 * b2n (CFSG.TcRes.TK.orB (famE (compRank Ψ) Ψ.ncard) (famD4 (compRank Ψ) Ψ.ncard)))) := rfl
  rw [hks]
  unfold CFSG.StandardType.TableCRes.twistKindOf
  split_ifs with h1 h2 h3 h4
  · exact mem_tkKs (k := 0) (by norm_num) b0
  · refine mem_tkKs (k := 3) (by norm_num) ?_
    rw [b3, orB_eq, Bool.or_eq_true]
    rcases h2 with h | h
    · exact Or.inl ((famE_iff _ _).2 h)
    · exact Or.inr ((famD4_iff _ _).2 ⟨h.1, h.2.1⟩)
  · exact mem_tkKs (k := 2) (by norm_num) (b2.trans ((famD_iff _ _).2 h3))
  · exact mem_tkKs (k := 1) (by norm_num) (b1.trans ((famA_iff _ _).2 h4))
  · exact mem_tkKs (k := 0) (by norm_num) b0

theorem tcDataOK5_of_compRaw
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {N : ℕ}
    {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    (hD : DatumRaw τ N vec rt adj neg) {ph : ℕ → ℕ}
    {Φ ψ : Set ℕ} {g0 d r0 : ℕ} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hker : kernelRoots χ = ρ '' kernelRoots χ)
    (hform : ∀ α ∈ kernelRoots χ, ∀ β ∈ kernelRoots χ, iform (ρ α) (ρ β) = iform α β)
    (hΦ : vec '' Φ = kernelRoots χ) (hphN : ∀ g < N, ph g < N)
    (hph : ∀ g < N, vec (ph g) = ρ (vec g))
    (h : CompRaw vec rt ph N Φ ψ g0 d r0) (hks : dKs d = ksOf (dR d) (dN d)) :
    ∃ i : KernelComponent χ, componentRoots χ i = vec '' ψ ∧
      CFSG.StandardType.TableCRes.TcDataOK ρ (componentRoots χ i) (tkCd5 d) := by
  obtain ⟨i, hi, he⟩ := orbitLength_of_compRaw ρ hker hform hΦ hphN hph hD.inj h
  have hΨ : IsRootComponent (vec '' ψ) := hi ▸ isRootComponent_componentRoots i
  have hr := compRank_of_compRaw hD.inj h hΨ
  have hN := ncard_of_compRaw hD.inj h
  refine ⟨i, hi, he.symm, ?_, ?_, ?_⟩
  · rw [hi, hr]
    rfl
  · rw [hi, hN]
    rfl
  · have hm := kind_mem_ksOf (ρ := ρ) (Ψ := vec '' ψ)
    rw [hr, hN, ← hks] at hm
    rw [hi]
    exact hm

end CFSG.KC.TcRes

end
