module

public import Certificates.Data.Kernel.HeAutK
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.HeAutK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.HexaK CFSG.KC.BfsPin
open CFSG.KLie.CT (anyN andB orB notB)

@[expose] noncomputable def cfldH (d k : Nat) : Nat :=
  Nat.land (Nat.shiftRight d (Nat.mul (nat_lit 10) k)) (nat_lit 1023)

@[expose] noncomputable def slotR (D i : Nat) : Nat :=
  Nat.land (Nat.shiftRight D (Nat.mul (nat_lit 180) i))
    (nat_lit 1532495540865888858358347027150309183618739122183602175)

@[expose] noncomputable def cosRK (n w : Nat) (T : Nat → Nat) (FZ z x d : Nat) : Bool :=
  andB (allR (fun k => Nat.beq (mul n w (T (cfldH d (Nat.add k 1))) (T (cfldH d (Nat.add k 9))))
      (pidn n w)) 0 8)
    (andB (allR (fun l => allR (fun k => notB (commZ n w z x
        (mul n w (T (cfldH d (Nat.add l 1))) (T (cfldH d (Nat.add k 9)))))) 0 l) 0 8)
      (andB (notB (bitK FZ (cfldH d 17))) (commZ n w z x (T (cfldH d 17)))))

@[expose] noncomputable def goodQR (n w N : Nat) (T : Nat → Nat) (FZ z x d : Nat) : Bool :=
  Bool.rec (goodQK n w N T FZ z x) (cosRK n w T FZ z x d) (Nat.beq (cfldH d 0) 1)

@[expose] noncomputable def uqAtR (n w NX : Nat) (TX : Nat → Nat) (NQ : Nat) (TQ : Nat → Nat)
    (FZ z D i : Nat) : Bool :=
  andB (bitK FZ i) (strictB (TX i) fun x =>
    andB (notB (inL NQ TQ x)) (notB (goodQR n w NX TX FZ z x (slotR D i))))

@[expose] noncomputable def zcHK (n w N : Nat) (T : Nat → Nat) (z : Nat) : Bool :=
  andB (Nat.beq (mul n w z z) (pidn n w))
    (allR (fun i => Nat.beq (mul n w z (T i)) (mul n w (T i) z)) 0 N)

end CFSG.KC.HeAutK

end

namespace CFSG.KC.HeAutK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.HexaK CFSG.KC.BfsPin CFSG.KS.Raw.Orb
open CFSG.KLie.CT (anyN andB orB notB)

variable {n w : Nat}

theorem sB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl
theorem aB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl
theorem oB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl
theorem nB_eq (a : Bool) : notB a = !a := by cases a <;> rfl
theorem sN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem setYK_recR (T : Nat → Nat) (FZ z x : Nat) : ∀ M acc,
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun r ih acc => Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (r :: acc))
        (andB (bitK FZ r) (commZ n w z x (T r)))) M acc =
      (List.range M).filter (fun r => andB (bitK FZ r) (commZ n w z x (T r))) ++ acc
  | 0, acc => rfl
  | M + 1, acc => by
    change Bool.rec (motive := fun _ => List Nat) _ _ (andB (bitK FZ M) (commZ n w z x (T M))) = _
    rw [List.range_succ, List.filter_append]
    cases h : andB (bitK FZ M) (commZ n w z x (T M))
    · change Nat.rec (motive := fun _ => List Nat → List Nat) _ _ M acc = _
      rw [setYK_recR T FZ z x M acc]
      simp [h]
    · change Nat.rec (motive := fun _ => List Nat → List Nat) _ _ M (M :: acc) = _
      rw [setYK_recR T FZ z x M (M :: acc)]
      simp [h]

theorem setYK_eqR (N : Nat) (T : Nat → Nat) (FZ z x : Nat) :
    setYK n w N T FZ z x =
      (List.range N).filter (fun r => andB (bitK FZ r) (commZ n w z x (T r))) :=
  (setYK_recR T FZ z x N []).trans (List.append_nil _)

theorem cntR_eqR (F : Nat → Bool) : ∀ K, cntR F 0 K = ((List.range K).filter F).length
  | 0 => rfl
  | K + 1 => by
    change strictN (cntR F 0 K)
      (fun a => Nat.add a (Bool.rec (motive := fun _ => Nat) 0 1 (F (Nat.add 0 K)))) = _
    rw [sN_eq, cntR_eqR F K, List.range_succ, List.filter_append, List.length_append]
    simp only [Nat.add_eq, Nat.zero_add]
    cases h : F K <;> simp [h]

theorem allR_iff {f : Nat → Bool} {lo : Nat} :
    ∀ {N : Nat}, allR f lo N = true ↔ ∀ k < N, f (lo + k) = true
  | 0 => ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | N + 1 => by
    have e : allR f lo (N + 1) = andB (allR f lo N) (f (lo + N)) := rfl
    rw [e, aB_eq, Bool.and_eq_true, allR_iff]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h N (by omega)⟩

theorem ppPrep {p : Nat} (hp : PP n w p) : ∃ g : Equiv.Perm (Fin n), PRep n w p g := by
  let f : Fin n → Fin n := fun x => ⟨pg w (mask w) p x, hp.2.1 x x.2⟩
  have hf : Function.Injective f := fun a b e =>
    Fin.ext (hp.2.2 a a.2 b b.2 (congrArg Fin.val e))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun x => rfl⟩

theorem ppEq {p q : Nat} {g h : Equiv.Perm (Fin n)} (hp : PP n w p) (hq : PP n w q)
    (hg : PRep n w p g) (hh : PRep n w q h) : p = q ↔ g = h := by
  constructor
  · rintro rfl
    exact Equiv.ext fun y => Fin.ext (by rw [← hg y, ← hh y])
  · rintro rfl
    obtain ⟨-, hw, hp0, -⟩ := PF.canon_facts hp.1
    obtain ⟨-, -, hq0, -⟩ := PF.canon_facts hq.1
    exact PF.eq_of_fields (PF.w_pos hw) hp0 hq0 fun i hi => (hg ⟨i, hi⟩).trans (hh ⟨i, hi⟩).symm

theorem ppMul {p q : Nat} (hp : PP n w p) (hq : PP n w q) : PP n w (mul n w p q) :=
  PP.mul hp hq

theorem ppPrepMul {p q : Nat} {g h : Equiv.Perm (Fin n)} (hp : PP n w p) (hg : PRep n w p g)
    (hh : PRep n w q h) : PRep n w (mul n w p q) (g * h) :=
  prep_pcomp (PP.lt32 hp) hg hh

theorem ppPrepId (hsz : CFSG.KS.Raw.szOK n w = true) : PRep n w (pidn n w) 1 := by
  obtain ⟨hn, hw⟩ := szOK_facts' hsz
  exact prep_pidn hn hw

theorem commZ_iff {z a b : Nat} {Z A B : Equiv.Perm (Fin n)} (hz : PP n w z) (ha : PP n w a)
    (hb : PP n w b) (hZ : PRep n w z Z) (hA : PRep n w a A) (hB : PRep n w b B) :
    commZ n w z a b = true ↔ (A * B = B * A ∨ A * B = B * A * Z) := by
  unfold commZ
  rw [sB_eq, sB_eq, sB_eq, sB_eq, oB_eq, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq,
    ppEq (ppMul ha hb) (ppMul hb ha) (ppPrepMul ha hA hB) (ppPrepMul hb hB hA),
    ppEq (ppMul ha hb) (ppMul (ppMul hb ha) hz) (ppPrepMul ha hA hB)
      (ppPrepMul (ppMul hb ha) (ppPrepMul hb hB hA) hZ)]

theorem cZ_mul {G : Type*} [Group G] {x z c c' : G} (hzz : z * z = 1) (hzx : z * x = x * z)
    (hzc : z * c = c * z) (hzc' : z * c' = c' * z)
    (hc : x * c = c * x ∨ x * c = c * x * z) (hc' : x * c' = c' * x ∨ x * c' = c' * x * z) :
    x * (c'⁻¹ * c) = c'⁻¹ * c * x ∨ x * (c'⁻¹ * c) = c'⁻¹ * c * x * z := by
  have hzci : z * c'⁻¹ = c'⁻¹ * z := by
    calc z * c'⁻¹ = c'⁻¹ * (c' * z) * c'⁻¹ := by group
      _ = c'⁻¹ * (z * c') * c'⁻¹ := by rw [hzc']
      _ = c'⁻¹ * z := by group
  obtain ⟨a, ha1, ha⟩ : ∃ a, (a = 1 ∨ a = z) ∧ x * c = c * x * a := by
    rcases hc with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, mul_one]⟩
    · exact ⟨z, Or.inr rfl, h⟩
  obtain ⟨b, hb1, hb⟩ : ∃ b, (b = 1 ∨ b = z) ∧ x * c' = c' * x * b := by
    rcases hc' with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, mul_one]⟩
    · exact ⟨z, Or.inr rfl, h⟩
  have hbb : b * b = 1 := by rcases hb1 with rfl | rfl <;> simp [hzz]
  have hbc : b * c = c * b := by rcases hb1 with rfl | rfl <;> simp [hzc]
  have hbci : b * c'⁻¹ = c'⁻¹ * b := by rcases hb1 with rfl | rfl <;> simp [hzci]
  have e0 : c' * x * c'⁻¹ = x * b := by
    calc c' * x * c'⁻¹ = c' * x * (b * b) * c'⁻¹ := by rw [hbb, mul_one]
      _ = c' * x * b * (b * c'⁻¹) := by group
      _ = c' * x * b * (c'⁻¹ * b) := by rw [hbci]
      _ = x * c' * c'⁻¹ * b := by rw [hb]; group
      _ = x * b := by group
  have e1 : x * c'⁻¹ = c'⁻¹ * x * b := by
    calc x * c'⁻¹ = c'⁻¹ * (c' * x * c'⁻¹) := by group
      _ = c'⁻¹ * (x * b) := by rw [e0]
      _ = c'⁻¹ * x * b := by group
  have e2 : x * (c'⁻¹ * c) = c'⁻¹ * c * x * (a * b) := by
    calc x * (c'⁻¹ * c) = x * c'⁻¹ * c := by group
      _ = c'⁻¹ * x * (b * c) := by rw [e1]; group
      _ = c'⁻¹ * x * (c * b) := by rw [hbc]
      _ = c'⁻¹ * (x * c) * b := by group
      _ = c'⁻¹ * (c * x * a) * b := by rw [ha]
      _ = c'⁻¹ * c * x * (a * b) := by group
  rcases ha1 with rfl | rfl <;> rcases hb1 with rfl | rfl
  · rw [mul_one, mul_one] at e2
    exact Or.inl e2
  · rw [one_mul] at e2
    exact Or.inr e2
  · rw [mul_one] at e2
    exact Or.inr e2
  · rw [hzz, mul_one] at e2
    exact Or.inl e2

public theorem bfsK_injR {ng N : Nat} {G T E S : Nat → Nat} (hk : bfsK n w ng G N T E S = true) :
    ∀ a < N, ∀ b < N, T a = T b → a = b := by
  unfold bfsK at hk
  simp only [bAnd_iff] at hk
  exact distinctK_inj hk.2.2.2.2.1

public theorem pts_mulR {ng N : Nat} {G T E S : Nat → Nat} (hk : bfsK n w ng G N T E S = true)
    (hp : ∀ k < ng, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true) :
    ∀ a < N, ∀ b < N, ∃ c < N, T c = mul n w (T a) (T b) := by
  have hT := PP_pts hk hp
  have hG := PP_gen hk hp
  have hb := bfsK_points (fun _ => True) trivial (fun _ _ _ _ => trivial) hk
  have hsz : CFSG.KS.Raw.szOK n w = true := PP.sz (hT 0 hb.1)
  have assoc : ∀ {p q r : Nat}, PP n w p → PP n w q → PP n w r →
      mul n w (mul n w p q) r = mul n w p (mul n w q r) := by
    intro p q r hp' hq hr
    obtain ⟨P, hP⟩ := ppPrep hp'
    obtain ⟨Q, hQ⟩ := ppPrep hq
    obtain ⟨R, hR⟩ := ppPrep hr
    rw [ppEq (ppMul (ppMul hp' hq) hr) (ppMul hp' (ppMul hq hr))
      (ppPrepMul (ppMul hp' hq) (ppPrepMul hp' hP hQ) hR) (ppPrepMul hp' hP (ppPrepMul hq hQ hR)),
      mul_assoc]
  have hid : ∀ {p : Nat}, PP n w p → mul n w (pidn n w) p = p := by
    intro p hp'
    obtain ⟨P, hP⟩ := ppPrep hp'
    rw [ppEq (ppMul (PP.id hsz) hp') hp' (ppPrepMul (PP.id hsz) (ppPrepId hsz) hP) hP, one_mul]
  have key := bfsK_points (fun y => PP n w y ∧ ∀ b < N, ∃ c < N, T c = mul n w y (T b))
    ⟨PP.id hsz, fun b hb' => ⟨b, hb', (hid (hT b hb')).symm⟩⟩
    (fun y ⟨hy, hyc⟩ k hk' => ⟨PP.mul (hG k hk') hy, fun b hb' => by
      obtain ⟨c, hc, ec⟩ := hyc b hb'
      obtain ⟨c', hc', ec'⟩ := hb.2.2.2 c hc k hk'
      refine ⟨c', hc', ?_⟩
      change T c' = mul n w (mul n w (G k) y) (T b)
      rw [ec', assoc (hG k hk') hy (hT b hb'), ← ec]
      rfl⟩) hk
  exact fun a ha b hb' => (key.2.2.1 a ha).2 b hb'

theorem cfldH_lt (d k : Nat) : cfldH d k < 1024 := by
  unfold cfldH
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem goodQK_of_goodQR {N : Nat} {T : Nat → Nat} {FZ z d : Nat} (hN : N = 1024)
    (hT : ∀ i < N, PP n w (T i)) (hinj : ∀ a < N, ∀ b < N, T a = T b → a = b)
    (hcl : ∀ a < N, ∀ b < N, ∃ c < N, T c = mul n w (T a) (T b))
    (hz : PP n w z) (hzz : mul n w z z = pidn n w)
    (hzc : ∀ i < N, mul n w z (T i) = mul n w (T i) z) {i : Nat} (hi : i < N)
    (h : goodQR n w N T FZ z (T i) d = true) : goodQK n w N T FZ z (T i) = true := by
  unfold goodQR at h
  cases e0 : Nat.beq (cfldH d 0) 1
  · rw [e0] at h
    exact h
  rw [e0] at h
  change cosRK n w T FZ z (T i) d = true at h
  have hsz : CFSG.KS.Raw.szOK n w = true := PP.sz hz
  have fl : ∀ k, cfldH d k < N := fun k => hN ▸ cfldH_lt d k
  unfold cosRK at h
  rw [aB_eq, aB_eq, aB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, allR_iff,
    allR_iff, nB_eq, Bool.not_eq_true'] at h
  obtain ⟨hgh, hpair, hj0, hj1⟩ := h
  obtain ⟨Z, hZ⟩ := ppPrep hz
  choose σ hσ using fun r (hr : r < N) => ppPrep (hT r hr)
  have px := hT i hi
  let A := (List.range N).filter fun r => commZ n w z (T i) (T r)
  have hY : (setYK n w N T FZ z (T i)).length < A.length := by
    rw [setYK_eqR]
    have e : ((List.range N).filter fun r => andB (bitK FZ r) (commZ n w z (T i) (T r))) =
        A.filter fun r => bitK FZ r := by
      rw [List.filter_filter]
      congr 1
    rw [e, List.length_filter_lt_length_iff_exists]
    exact ⟨cfldH d 17, List.mem_filter.2 ⟨List.mem_range.2 (fl 17), hj1⟩, by simp [hj0]⟩
  have zc : ∀ r (hr : r < N), Z * σ r hr = σ r hr * Z := fun r hr => by
    have e := hzc r hr
    rwa [ppEq (ppMul hz (hT r hr)) (ppMul (hT r hr) hz) (ppPrepMul hz hZ (hσ r hr))
      (ppPrepMul (hT r hr) (hσ r hr) hZ)] at e
  have hZZ : Z * Z = 1 := by
    rwa [ppEq (ppMul hz hz) (PP.id hsz) (ppPrepMul hz hZ hZ) (ppPrepId hsz)] at hzz
  let g : Nat → Nat := fun k => cfldH d (k + 1)
  let hk : Nat → Nat := fun k => cfldH d (k + 9)
  have ginv : ∀ k < 8, σ (g k) (fl _) * σ (hk k) (fl _) = 1 := fun k hk8 => by
    have e := hgh k hk8
    rw [Nat.zero_add, Nat.beq_eq, ppEq (ppMul (hT _ (fl _)) (hT _ (fl _))) (PP.id hsz)
      (ppPrepMul (hT _ (fl _)) (hσ _ (fl _)) (hσ _ (fl _))) (ppPrepId hsz)] at e
    exact e
  have inC : ∀ r (hr : r < N), commZ n w z (T i) (T r) = true ↔
      (σ i hi * σ r hr = σ r hr * σ i hi ∨ σ i hi * σ r hr = σ r hr * σ i hi * Z) :=
    fun r hr => commZ_iff hz px (hT r hr) hZ (hσ i hi) (hσ r hr)
  have notC : ∀ l < 8, ∀ k < l, ¬ (σ i hi * (σ (g l) (fl _) * σ (hk k) (fl _)) =
      σ (g l) (fl _) * σ (hk k) (fl _) * σ i hi ∨ σ i hi * (σ (g l) (fl _) * σ (hk k) (fl _)) =
      σ (g l) (fl _) * σ (hk k) (fl _) * σ i hi * Z) := fun l hl k hkl hc => by
    have e := (allR_iff.1 (hpair l hl)) k (by omega)
    rw [Nat.zero_add, Nat.zero_add, nB_eq, Bool.not_eq_true'] at e
    have e' := (commZ_iff hz px (ppMul (hT _ (fl _)) (hT _ (fl _))) hZ (hσ i hi)
      (ppPrepMul (hT _ (fl _)) (hσ _ (fl _)) (hσ _ (fl _)))).2 hc
    rw [e] at e'
    exact Bool.false_ne_true e'
  choose m hm hme using fun r (hr : r < N) k (_ : k < 8) => hcl r hr (g k) (fl _)
  let f : Nat × Nat → Nat := fun p =>
    if h : p.1 < N ∧ p.2 < 8 then m p.1 h.1 p.2 h.2 else 0
  have hA8 : A.length * 8 ≤ N := by
    have hcard : (A.toFinset ×ˢ Finset.range 8).card ≤ (Finset.range N).card := by
      refine Finset.card_le_card_of_injOn f (fun p hp => ?_) (fun p hp q hq e => ?_)
      · obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
        have h1 := List.mem_range.1 (List.mem_filter.1 (List.mem_toFinset.1 hp1)).1
        have h2 := Finset.mem_range.1 hp2
        simp only [f, h1, h2, and_self, ↓reduceDIte]
        exact Finset.mem_range.2 (hm _ _ _ _)
      · obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hp)
        obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hq)
        obtain ⟨hpr, hpc⟩ := List.mem_filter.1 (List.mem_toFinset.1 hp1)
        obtain ⟨hqr, hqc⟩ := List.mem_filter.1 (List.mem_toFinset.1 hq1)
        have a1 := List.mem_range.1 hpr
        have b1 := List.mem_range.1 hqr
        have a2 := Finset.mem_range.1 hp2
        have b2 := Finset.mem_range.1 hq2
        simp only [f, a1, a2, b1, b2, and_self, ↓reduceDIte] at e
        have e' : mul n w (T p.1) (T (g p.2)) = mul n w (T q.1) (T (g q.2)) := by
          rw [← hme _ a1 _ a2, ← hme _ b1 _ b2, e]
        rw [ppEq (ppMul (hT _ a1) (hT _ (fl _))) (ppMul (hT _ b1) (hT _ (fl _)))
          (ppPrepMul (hT _ a1) (hσ _ a1) (hσ _ (fl _)))
          (ppPrepMul (hT _ b1) (hσ _ b1) (hσ _ (fl _)))] at e'
        have cp := (inC _ a1).1 hpc
        have cq := (inC _ b1).1 hqc
        rcases lt_trichotomy p.2 q.2 with hlt | heq | hgt
        · exfalso
          have hgq : σ (g q.2) (fl _) * σ (hk p.2) (fl _) = (σ q.1 b1)⁻¹ * σ p.1 a1 := by
            rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← e', mul_assoc, ginv p.2 a2, mul_one]
          refine notC q.2 b2 p.2 hlt ?_
          rw [hgq]
          exact cZ_mul hZZ (zc i hi) (zc _ a1) (zc _ b1) cp cq
        · have e2 : σ p.1 a1 = σ q.1 b1 := by
            have e3 : σ p.1 a1 * σ (g p.2) (fl _) = σ q.1 b1 * σ (g p.2) (fl _) := by
              have := e'
              simp only [g, heq] at this ⊢
              exact this
            exact mul_right_cancel e3
          have := (ppEq (hT _ a1) (hT _ b1) (hσ _ a1) (hσ _ b1)).2 e2
          exact Prod.ext (hinj _ a1 _ b1 this) heq
        · exfalso
          have hgp : σ (g p.2) (fl _) * σ (hk q.2) (fl _) = (σ p.1 a1)⁻¹ * σ q.1 b1 := by
            rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, e', mul_assoc, ginv q.2 b2, mul_one]
          refine notC p.2 a2 q.2 hgt ?_
          rw [hgp]
          exact cZ_mul hZZ (zc i hi) (zc _ b1) (zc _ a1) cq cp
    rw [Finset.card_product, Finset.card_range, Finset.card_range,
      List.toFinset_card_of_nodup (List.nodup_range.filter _)] at hcard
    exact hcard
  unfold goodQK
  rw [sB_eq, oB_eq, Bool.or_eq_true]
  left
  have hlt : (setYK n w N T FZ z (T i)).length < 128 := by omega
  rw [Nat.blt_eq]
  exact hlt

public theorem cntR_uqAt_of_R {NX NQ : Nat} {TX TQ : Nat → Nat} {FZ z D : Nat} (hN : NX = 1024)
    (hT : ∀ i < NX, PP n w (TX i)) (hinj : ∀ a < NX, ∀ b < NX, TX a = TX b → a = b)
    (hcl : ∀ a < NX, ∀ b < NX, ∃ c < NX, TX c = mul n w (TX a) (TX b)) (hz : PP n w z)
    (hzc : zcHK n w NX TX z = true) {M : Nat} (hM : M ≤ NX)
    (h : cntR (uqAtR n w NX TX NQ TQ FZ z D) 0 M = 0) :
    cntR (uqAt n w NX TX NQ TQ FZ z) 0 M = 0 := by
  unfold zcHK at hzc
  rw [aB_eq, Bool.and_eq_true, Nat.beq_eq, allR_iff] at hzc
  have hzc' : ∀ i < NX, mul n w z (TX i) = mul n w (TX i) z := fun i hi => by
    have := hzc.2 i hi
    rwa [Nat.zero_add, Nat.beq_eq] at this
  have pt : ∀ i < M, uqAtR n w NX TX NQ TQ FZ z D i = false →
      uqAt n w NX TX NQ TQ FZ z i = false := fun i hi h0 => by
    unfold uqAtR at h0
    unfold uqAt
    rw [sB_eq] at h0 ⊢
    rw [aB_eq, aB_eq, nB_eq, nB_eq] at h0 ⊢
    have hg := goodQK_of_goodQR (FZ := FZ) (d := slotR D i) hN hT hinj hcl hz hzc.1 hzc'
      (i := i) (by omega)
    revert h0 hg
    generalize bitK FZ i = a
    generalize HexaK.inL NQ TQ (TX i) = b
    generalize goodQK n w NX TX FZ z (TX i) = c
    generalize goodQR n w NX TX FZ z (TX i) (slotR D i) = c'
    cases a <;> cases b <;> cases c <;> cases c' <;> simp
  rw [cntR_eqR] at h ⊢
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h ⊢
  intro i hi
  have hi' := List.mem_range.1 hi
  simpa using pt i hi' (by simpa using h i hi)

end CFSG.KC.HeAutK
