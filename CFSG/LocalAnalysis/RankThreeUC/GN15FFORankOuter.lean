module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFORankSplit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.Sporadic.HNSchreier.Algebra

public section

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.Burgoyne.U (uU uConjAut)

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.RankCore

private theorem uFactor_eq_one_of_mem_conj_range {p f m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hm : 3 ≤ m) (hq : ¬(m = 3 ∧ p ^ f = 2))
    {γ : MulAut (StatedProj (StatedSU m (p ^ f) K))}
    (hγ : γ ∈ (MulAut.conj : StatedProj (StatedSU m (p ^ f) K) →*
      MulAut (StatedProj (StatedSU m (p ^ f) K))).range) :
    CFSG.ComponentClassification.Burgoyne.U.uFactor h hm hq γ = 1 := by
  classical
  obtain ⟨z, rfl⟩ := hγ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  let A : uU h m :=
    ⟨(g : GL (Fin m) K), CFSG.ComponentClassification.Burgoyne.U.statedSU_le_uU h g.2⟩
  have hc : (MulAut.conj (QuotientGroup.mk g : StatedProj (StatedSU m (p ^ f) K))) =
      uConjAut h (by omega : 1 ≤ m) A := by
    refine MulEquiv.ext fun w => ?_
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective w
    refine Eq.trans ?_ (CFSG.ComponentClassification.Burgoyne.U.uConjAut_proj h
      (by omega : 1 ≤ m) A t).symm
    rw [MulAut.conj_apply]
    rfl
  rw [hc]
  have h1 := CFSG.ComponentClassification.Burgoyne.U.uFactor_apply h hm hq A 1
  rwa [map_one, mul_one] at h1

private theorem uFactor_eq_one_iff_exists_uConjAut {p f m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hm : 3 ≤ m) (hq : ¬(m = 3 ∧ p ^ f = 2))
    (α : MulAut (StatedProj (StatedSU m (p ^ f) K))) :
    CFSG.ComponentClassification.Burgoyne.U.uFactor h hm hq α = 1 ↔
      ∃ A : uU h m, α = uConjAut h (by omega : 1 ≤ m) A := by
  constructor
  · intro h1
    obtain ⟨A, φ, hAφ⟩ :=
      CFSG.ComponentClassification.Burgoyne.U.exists_uConjAut_mul_uFieldAut h hm hq α
    refine ⟨A, ?_⟩
    have hφ : φ = 1 := by
      rw [hAφ, CFSG.ComponentClassification.Burgoyne.U.uFactor_apply] at h1
      exact h1
    rw [hAφ, hφ, map_one, mul_one]
  · rintro ⟨A, rfl⟩
    have h1 := CFSG.ComponentClassification.Burgoyne.U.uFactor_apply h hm hq A 1
    rwa [map_one, mul_one] at h1

theorem mem_range_uConjAut_of_inverted {p f m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hm : 3 ≤ m) (hq : ¬(m = 3 ∧ p ^ f = 2)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {βa βy : MulAut (StatedProj (StatedSU m (p ^ f) K))}
    (hrel : βa * βy * βa⁻¹ = βy⁻¹)
    (hyr : βy ^ r ∈ (MulAut.conj : StatedProj (StatedSU m (p ^ f) K) →*
      MulAut (StatedProj (StatedSU m (p ^ f) K))).range) :
    βy ∈ (uConjAut h (by omega : 1 ≤ m)).range := by
  classical
  have : Finite K := h.finite
  set Θ := CFSG.ComponentClassification.Burgoyne.U.uFactor h hm hq with hΘ
  have hΘy2 : Θ βy ^ 2 = 1 := by
    have h1 : Θ βa * Θ βy * (Θ βa)⁻¹ = (Θ βy)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, hrel, map_inv]
    have h2 : Θ βa * Θ βy * (Θ βa)⁻¹ = Θ βy := by
      rw [CFSG.RankThree.PartOne.OutStructure.ringAut_comm K (Θ βa) (Θ βy),
        mul_inv_cancel_right]
    rw [h2] at h1
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.2 h1
  have hΘyr : Θ βy ^ r = 1 := by
    rw [← map_pow]
    exact uFactor_eq_one_of_mem_conj_range h hm hq hyr
  have hΘy : Θ βy = 1 := by
    have hcop : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2)
    have h1 : orderOf (Θ βy) ∣ Nat.gcd 2 r :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hΘy2) (orderOf_dvd_of_pow_eq_one hΘyr)
    rw [hcop] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  obtain ⟨A, hA⟩ := (uFactor_eq_one_iff_exists_uConjAut h hm hq βy).1 hΘy
  exact ⟨A, hA.symm⟩

private theorem exists_zpow_mul_pow_five_of_not_fifth_power {G : Type*} [CommGroup G] [Finite G]
    [IsCyclic G] {d ζ : G} (hd : ∀ μ : G, μ ^ 5 ≠ d) (h5 : 5 ∣ Nat.card G) :
    ∃ (k : ℤ) (μ : G), ζ = d ^ k * μ ^ 5 := by
  classical
  let H : Subgroup G := (powMonoidHom 5).range
  have hdH : d ∉ H := by
    intro hdH
    obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.1 hdH
    exact hd μ (by simpa [powMonoidHom_apply] using hμ)
  let L : Subgroup G := Subgroup.zpowers d ⊔ H
  have hHL : H ≤ L := le_sup_right
  have hdL : d ∈ L := Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  have hLH : L ≠ H := fun h => hdH (h ▸ hdL)
  have hHindex : H.index = 5 := by
    have hgcd : Nat.gcd (Nat.card G) 5 = 5 := Nat.gcd_eq_right h5
    change (powMonoidHom 5 : G →* G).range.index = 5
    rw [IsCyclic.index_powMonoidHom_range, hgcd]
  have hdvd : L.index ∣ 5 := by
    rw [← hHindex]
    exact Subgroup.index_dvd_of_le hHL
  have htop : L = ⊤ := by
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h5'
    · exact Subgroup.index_eq_one.1 h1
    · exfalso
      have hrel : H.relIndex L = 1 := by
        have hprod := Subgroup.relIndex_mul_index hHL
        rw [h5', hHindex] at hprod
        omega
      have hLH' : L ≤ H := Subgroup.relIndex_eq_one.1 hrel
      exact hLH (le_antisymm hLH' hHL)
  have hζL : ζ ∈ L := by
    rw [htop]
    exact Subgroup.mem_top ζ
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 hζL
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
  obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.1 hz
  refine ⟨k, μ, ?_⟩
  calc ζ = y * z := hyz.symm
    _ = d ^ k * μ ^ 5 := by
      rw [← hk]
      congr 1
      have hμz : μ ^ 5 = z := by simpa [powMonoidHom_apply] using hμ
      exact hμz.symm

private theorem unitary_norm_mul {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (a b : K) : h.norm (a * b) = h.norm a * h.norm b := by
  simp only [UnitaryFieldData.norm, map_mul]
  ring

private theorem unitary_norm_zpow_eq_one {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {z : Kˣ} (hz : h.norm (z : K) = 1) (k : ℤ) :
    h.norm ((z ^ k : Kˣ) : K) = 1 := by
  have hz_inv : h.norm (((z⁻¹ : Kˣ) : K)) = 1 := by
    have h1 : h.norm ((z : K) * ((z⁻¹ : Kˣ) : K)) =
        h.norm (z : K) * h.norm (((z⁻¹ : Kˣ) : K)) :=
      unitary_norm_mul h (z : K) ((z⁻¹ : Kˣ) : K)
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, UnitaryFieldData.norm, map_one, one_mul]
      at h1
    rw [hz, one_mul] at h1
    exact h1.symm
  refine zpow_induction_right (P := fun a : Kˣ => h.norm (a : K) = 1) ?_ ?_ ?_ k
  · simp [UnitaryFieldData.norm]
  · intro a ha
    rw [Units.val_mul, unitary_norm_mul, ha, hz, mul_one]
  · intro a ha
    rw [Units.val_mul, unitary_norm_mul, ha, hz_inv, mul_one]

private theorem diagGL_mem_uU_of_norm_one {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {n : ℕ} (u : Fin n → Kˣ)
    (hu : ∀ i, h.norm (u i : K) = 1) : TauCeti.diagGL u ∈ uU h n := by
  rw [CFSG.ComponentClassification.Burgoyne.U.mem_uU, TauCeti.diagGL_coe,
    Matrix.diagonal_map (f := h.bar) (map_zero h.bar),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [mul_comm]
  simpa [UnitaryFieldData.norm] using hu i

private theorem diagGL_mem_statedSU_of_norm_one {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {n : ℕ} (u : Fin n → Kˣ)
    (hu : ∀ i, h.norm (u i : K) = 1) (hprod : ∏ i, u i = 1) :
    TauCeti.diagGL u ∈ StatedSU n (2 ^ f) K := by
  rw [CFSG.ComponentClassification.Burgoyne.U.statedSU_eq_gramSU h,
    CFSG.ClassicalGroups.UnitaryFlag.mem_gramSU]
  refine ⟨?_, ?_⟩
  · simpa only [Units.val_one, Matrix.mul_one] using
      (CFSG.ComponentClassification.Burgoyne.U.mem_uU h).1 (diagGL_mem_uU_of_norm_one h u hu)
  · rw [← Matrix.GeneralLinearGroup.val_det_apply, TauCeti.det_diagGL, hprod, Units.val_one]

private noncomputable def diagU {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (u : Fin 5 → Kˣ) (hu : ∀ i, h.norm (u i : K) = 1) : uU h 5 :=
  ⟨TauCeti.diagGL u, diagGL_mem_uU_of_norm_one h u hu⟩

private noncomputable def diagSU {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (u : Fin 5 → Kˣ) (hu : ∀ i, h.norm (u i : K) = 1) (hprod : ∏ i, u i = 1) :
    StatedSU 5 (2 ^ f) K :=
  ⟨TauCeti.diagGL u, diagGL_mem_statedSU_of_norm_one h u hu hprod⟩

private theorem norm_mulSingle_family {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1) (i : Fin 5) :
    ∀ j, h.norm ((Pi.mulSingle i ζ : Fin 5 → Kˣ) j : K) = 1 := by
  intro j
  by_cases hji : j = i
  · subst hji
    simp [Pi.mulSingle, hζ]
  · simp [Pi.mulSingle, hji, UnitaryFieldData.norm]

private theorem diagGL_mul_comm {n : ℕ} {K : Type} [Field K] (u v : Fin n → Kˣ) :
    TauCeti.diagGL u * TauCeti.diagGL v = TauCeti.diagGL v * TauCeti.diagGL u := by
  rw [← map_mul (TauCeti.diagGL), ← map_mul (TauCeti.diagGL)]
  congr 1
  exact mul_comm u v

private theorem diagGL_conj_eq_self {n : ℕ} {K : Type} [Field K] (u v : Fin n → Kˣ) :
    TauCeti.diagGL v * TauCeti.diagGL u * (TauCeti.diagGL v)⁻¹ = TauCeti.diagGL u := by
  rw [← map_inv (TauCeti.diagGL), ← map_mul (TauCeti.diagGL), ← map_mul (TauCeti.diagGL)]
  congr 1
  rw [mul_comm v u, mul_assoc, mul_inv_cancel, mul_one]

private theorem uConjAut_coe_SU_eq_conjProjH {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {n : ℕ} (hn : 1 ≤ n) (g : StatedSU n (p ^ f) K) :
    uConjAut h hn
        ⟨(g : GL (Fin n) K), CFSG.ComponentClassification.Burgoyne.U.statedSU_le_uU h g.2⟩ =
      CFSG.ComponentClassification.Burgoyne.Proj.conjProjH (StatedSU n (p ^ f) K) g := by
  ext x
  obtain ⟨y, rfl⟩ := CFSG.ComponentClassification.Burgoyne.Proj.projH_surjective x
  rw [CFSG.ComponentClassification.Burgoyne.U.uConjAut_proj]
  change CFSG.ComponentClassification.Burgoyne.Proj.projH _ _ =
    CFSG.ComponentClassification.Burgoyne.Proj.projH _ g *
      CFSG.ComponentClassification.Burgoyne.Proj.projH _ y *
      (CFSG.ComponentClassification.Burgoyne.Proj.projH _ g)⁻¹
  rw [← map_mul, ← map_inv, ← map_mul]
  rfl

private noncomputable def diagClass {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (ζ : Kˣ) (hζ : h.norm (ζ : K) = 1) (i : Fin 4) :
    MulAut (StatedProj (StatedSU 5 (2 ^ f) K)) :=
  uConjAut h (by norm_num)
    (diagU h (Pi.mulSingle (Fin.castSucc i) ζ) (norm_mulSingle_family h hζ (Fin.castSucc i)))

private theorem prod_four_diagGL {K : Type} [Field K] (ζ : Kˣ) (a : Fin 4 → ℕ) :
    TauCeti.diagGL (Pi.mulSingle (Fin.castSucc (0 : Fin 4)) ζ) ^ a 0 *
        TauCeti.diagGL (Pi.mulSingle (Fin.castSucc (1 : Fin 4)) ζ) ^ a 1 *
        TauCeti.diagGL (Pi.mulSingle (Fin.castSucc (2 : Fin 4)) ζ) ^ a 2 *
        TauCeti.diagGL (Pi.mulSingle (Fin.castSucc (3 : Fin 4)) ζ) ^ a 3 =
      TauCeti.diagGL (fun j : Fin 5 => if h : (j : ℕ) < 4 then ζ ^ a ⟨j, h⟩ else 1) := by
  rw [← map_pow (TauCeti.diagGL), ← map_pow (TauCeti.diagGL), ← map_pow (TauCeti.diagGL),
    ← map_pow (TauCeti.diagGL)]
  rw [← map_mul (TauCeti.diagGL), ← map_mul (TauCeti.diagGL), ← map_mul (TauCeti.diagGL)]
  congr 1
  funext j
  fin_cases j <;> simp [Pi.mulSingle]

private theorem norm_family_if {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1) (a : Fin 4 → ℕ) :
    ∀ j, h.norm ((fun j : Fin 5 => if h : (j : ℕ) < 4 then ζ ^ a ⟨j, h⟩ else 1) j : K) = 1 := by
  intro j
  by_cases hj : (j : ℕ) < 4
  · simp only [dif_pos hj]
    simpa [zpow_natCast] using unitary_norm_zpow_eq_one h hζ (a ⟨j, hj⟩ : ℤ)
  · simp only [dif_neg hj]
    simp [UnitaryFieldData.norm]

private theorem prod_four_diagClass {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1) (a : Fin 4 → ℕ) :
    (diagClass h ζ hζ 0) ^ (a 0 : ℕ) * (diagClass h ζ hζ 1) ^ (a 1 : ℕ) *
        (diagClass h ζ hζ 2) ^ (a 2 : ℕ) * (diagClass h ζ hζ 3) ^ (a 3 : ℕ) =
      uConjAut h (by norm_num)
        (diagU h (fun j : Fin 5 => if h : (j : ℕ) < 4 then ζ ^ a ⟨j, h⟩ else 1)
          (norm_family_if h hζ (fun i => (a i : ℕ)))) := by
  have hU : (diagU h (Pi.mulSingle (Fin.castSucc (0 : Fin 4)) ζ)
        (norm_mulSingle_family h hζ _)) ^ (a 0 : ℕ) *
      (diagU h (Pi.mulSingle (Fin.castSucc (1 : Fin 4)) ζ)
        (norm_mulSingle_family h hζ _)) ^ (a 1 : ℕ) *
      (diagU h (Pi.mulSingle (Fin.castSucc (2 : Fin 4)) ζ)
        (norm_mulSingle_family h hζ _)) ^ (a 2 : ℕ) *
      (diagU h (Pi.mulSingle (Fin.castSucc (3 : Fin 4)) ζ)
        (norm_mulSingle_family h hζ _)) ^ (a 3 : ℕ) =
      diagU h (fun j : Fin 5 => if h : (j : ℕ) < 4 then ζ ^ a ⟨j, h⟩ else 1)
        (norm_family_if h hζ (fun i => (a i : ℕ))) := by
    apply Subtype.ext
    simpa only [diagU, Subgroup.coe_pow, Subgroup.coe_mul, OneMemClass.coe_one]
      using prod_four_diagGL ζ a
  simp only [diagClass]
  simp only [← map_pow, ← map_mul]
  exact congrArg (uConjAut h (n := 5) (by norm_num)) hU

private theorem exists_scalar_eq_one_of_diagU_mul_inv {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {u v : Fin 5 → Kˣ}
    (hu : ∀ j, h.norm (u j : K) = 1) (hv : ∀ j, h.norm (v j : K) = 1)
    (hlast : u (Fin.last 4) * (v (Fin.last 4))⁻¹ = 1)
    (hker : uConjAut h (by norm_num) (diagU h u hu * (diagU h v hv)⁻¹) = 1) :
    ∃ c : Kˣ, c = 1 ∧ ∀ j, u j * (v j)⁻¹ = c := by
  obtain ⟨c, hc⟩ :=
    (CFSG.ComponentClassification.Burgoyne.U.uConjAut_eq_one_iff h (by norm_num) _).1 hker
  have hdiag : TauCeti.diagGL (fun j => u j * (v j)⁻¹) =
      Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
    calc TauCeti.diagGL (fun j => u j * (v j)⁻¹)
        = TauCeti.diagGL u * (TauCeti.diagGL v)⁻¹ := by
          rw [← map_inv (TauCeti.diagGL), ← map_mul (TauCeti.diagGL)]
          rfl
      _ = Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
          simpa [diagU] using hc
  have hdiag' : TauCeti.diagGL (fun j => u j * (v j)⁻¹) =
      TauCeti.diagGL (fun _ => c) := by
    rw [hdiag, TauCeti.diagGL_const]
  have hfun := TauCeti.diagGL_injective hdiag'
  have hc1 : c = 1 := by
    have hlast' := congrFun hfun (Fin.last 4)
    rw [hlast] at hlast'
    exact hlast'.symm
  exact ⟨c, hc1, fun j => congrFun hfun j⟩

private theorem diagClass_four_independent {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1)
    (hζo : orderOf ζ = 5) {a b : Fin 4 → Fin 5}
    (hab : (diagClass h ζ hζ 0) ^ (a 0 : ℕ) * (diagClass h ζ hζ 1) ^ (a 1 : ℕ) *
        (diagClass h ζ hζ 2) ^ (a 2 : ℕ) * (diagClass h ζ hζ 3) ^ (a 3 : ℕ) =
      (diagClass h ζ hζ 0) ^ (b 0 : ℕ) * (diagClass h ζ hζ 1) ^ (b 1 : ℕ) *
        (diagClass h ζ hζ 2) ^ (b 2 : ℕ) * (diagClass h ζ hζ 3) ^ (b 3 : ℕ)) :
    a = b := by
  classical
  let t : (Fin 4 → Fin 5) → Fin 5 → Kˣ := fun c j =>
    if h : (j : ℕ) < 4 then ζ ^ (c ⟨j, h⟩ : ℕ) else 1
  have hta : (diagClass h ζ hζ 0) ^ (a 0 : ℕ) * (diagClass h ζ hζ 1) ^ (a 1 : ℕ) *
        (diagClass h ζ hζ 2) ^ (a 2 : ℕ) * (diagClass h ζ hζ 3) ^ (a 3 : ℕ) =
      uConjAut h (by norm_num) (diagU h (t a) (norm_family_if h hζ (fun i => (a i : ℕ)))) := by
    simpa [t] using prod_four_diagClass h hζ (fun i => (a i : ℕ))
  have htb : (diagClass h ζ hζ 0) ^ (b 0 : ℕ) * (diagClass h ζ hζ 1) ^ (b 1 : ℕ) *
        (diagClass h ζ hζ 2) ^ (b 2 : ℕ) * (diagClass h ζ hζ 3) ^ (b 3 : ℕ) =
      uConjAut h (by norm_num) (diagU h (t b) (norm_family_if h hζ (fun i => (b i : ℕ)))) := by
    simpa [t] using prod_four_diagClass h hζ (fun i => (b i : ℕ))
  have heq : uConjAut h (by norm_num) (diagU h (t a) (norm_family_if h hζ (fun i => (a i : ℕ)))) =
      uConjAut h (by norm_num) (diagU h (t b) (norm_family_if h hζ (fun i => (b i : ℕ)))) := by
    rw [← hta, ← htb]
    exact hab
  have hker : uConjAut h (by norm_num)
      (diagU h (t a) (norm_family_if h hζ (fun i => (a i : ℕ))) *
        (diagU h (t b) (norm_family_if h hζ (fun i => (b i : ℕ))))⁻¹) = 1 := by
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  obtain ⟨c, hc1, hc⟩ := exists_scalar_eq_one_of_diagU_mul_inv h
    (norm_family_if h hζ (fun i => (a i : ℕ)))
    (norm_family_if h hζ (fun i => (b i : ℕ)))
    (by simp) hker
  apply funext
  intro i
  have hi := hc (Fin.castSucc i)
  have hpow : ζ ^ (a i : ℕ) = ζ ^ (b i : ℕ) := by
    have hz : ζ ^ (a i : ℕ) * (ζ ^ (b i : ℕ))⁻¹ = 1 := by
      simpa [t, hc1] using hi
    exact mul_inv_eq_one.1 hz
  have hmod := pow_eq_pow_iff_modEq.1 hpow
  rw [hζo] at hmod
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod (a i).2 (b i).2)

private theorem card_closure_diagClass {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1)
    (hζo : orderOf ζ = 5) :
    5 ^ 4 ≤ Nat.card (Subgroup.closure (Set.range (diagClass h ζ hζ))) := by
  let γ : Fin 4 → MulAut (StatedProj (StatedSU 5 (2 ^ f) K)) := diagClass h ζ hζ
  let ν : (Fin 4 → Fin 5) → Subgroup.closure (Set.range γ) := fun a =>
    ⟨(diagClass h ζ hζ 0) ^ (a 0 : ℕ) * (diagClass h ζ hζ 1) ^ (a 1 : ℕ) *
      (diagClass h ζ hζ 2) ^ (a 2 : ℕ) * (diagClass h ζ hζ 3) ^ (a 3 : ℕ), by
      refine Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
      · exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self 0)) _
      · exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self 1)) _
      · exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self 2)) _
      · exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self 3)) _⟩
  have hν : Function.Injective ν := by
    intro a b hab
    exact diagClass_four_independent h hζ hζo (congrArg Subtype.val hab)
  calc 5 ^ 4 = Nat.card (Fin 4 → Fin 5) := by
        rw [Nat.card_fun]
        simp
    _ ≤ _ := Nat.card_le_card_of_injective ν hν

private theorem diagClass_pairwise_commute {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1) :
    (Set.range (diagClass h ζ hζ)).Pairwise Commute := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
  change diagClass h ζ hζ i * diagClass h ζ hζ j =
    diagClass h ζ hζ j * diagClass h ζ hζ i
  simp only [diagClass]
  rw [← map_mul (uConjAut h (n := 5) (by norm_num)),
    ← map_mul (uConjAut h (n := 5) (by norm_num))]
  congr 1
  apply Subtype.ext
  simpa [diagU] using diagGL_mul_comm
    (Pi.mulSingle (Fin.castSucc i) ζ) (Pi.mulSingle (Fin.castSucc j) ζ)

private theorem diagClass_pow_five_eq_one {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1)
    (hζo : orderOf ζ = 5) :
    ∀ y ∈ Set.range (diagClass h ζ hζ), y ^ 5 = 1 := by
  have hζ5 : ζ ^ 5 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  rintro _ ⟨i, rfl⟩
  simp only [diagClass]
  rw [← map_pow (uConjAut h (n := 5) (by norm_num))]
  have hpow : (diagU h (Pi.mulSingle (Fin.castSucc i) ζ)
      (norm_mulSingle_family h hζ _)) ^ 5 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, diagU]
    rw [← map_pow (TauCeti.diagGL)]
    have hfun : (Pi.mulSingle (Fin.castSucc i) ζ : Fin 5 → Kˣ) ^ 5 = 1 := by
      funext j
      by_cases hji : j = Fin.castSucc i
      · subst hji
        simp [Pi.mulSingle, hζ5]
      · simp [Pi.mulSingle, hji]
    rw [hfun, map_one]
  rw [hpow, map_one]

private theorem four_le_pRank_of_diagClass {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1)
    (hζo : orderOf ζ = 5)
    {D : Subgroup (StatedProj (StatedSU 5 (2 ^ f) K))}
    {α : MulAut (StatedProj (StatedSU 5 (2 ^ f) K))}
    (hmem : ∀ i : Fin 4, diagClass h ζ hζ i ∈
      D.map (MulAut.conj : StatedProj (StatedSU 5 (2 ^ f) K) →*
        MulAut (StatedProj (StatedSU 5 (2 ^ f) K))) ⊔ Subgroup.zpowers α) :
    4 ≤ CFSG.Open.pRank 5
      (D.map (MulAut.conj : StatedProj (StatedSU 5 (2 ^ f) K) →*
        MulAut (StatedProj (StatedSU 5 (2 ^ f) K))) ⊔ Subgroup.zpowers α) := by
  have hS : (Set.range (diagClass h ζ hζ)).Pairwise Commute :=
    diagClass_pairwise_commute h hζ
  have hgen : ∀ y ∈ Set.range (diagClass h ζ hζ), y ^ 5 = 1 :=
    diagClass_pow_five_eq_one h hζ hζo
  have hclosure_le : Subgroup.closure (Set.range (diagClass h ζ hζ)) ≤
      D.map (MulAut.conj : StatedProj (StatedSU 5 (2 ^ f) K) →*
        MulAut (StatedProj (StatedSU 5 (2 ^ f) K))) ⊔ Subgroup.zpowers α := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  exact (CFSG.AGLEmbeddingD2.AltFiveRankTools.le_pRank_closure_of_pairwise_commute
    hS hgen (card_closure_diagClass h hζ hζo)).trans
    (CFSG.SectionRank.pRank_mono (by norm_num) hclosure_le)

private theorem scalar_mem_uU_of_norm_one {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {c : Kˣ} (hc : h.norm (c : K) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 5) c ∈ uU h 5 := by
  have hbar : h.bar (c : K) * (c : K) = 1 := by
    rw [UnitaryFieldData.norm] at hc
    rw [mul_comm]
    exact hc
  rw [CFSG.ComponentClassification.Burgoyne.U.mem_uU]
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp [hbar]
  · simp [hij, Ne.symm hij]

private theorem mem_statedSU_of_det_one {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {n : ℕ} {B : uU h n}
    (hdet : Matrix.GeneralLinearGroup.det (B : GL (Fin n) K) = 1) :
    (B : GL (Fin n) K) ∈ StatedSU n (2 ^ f) K := by
  rw [CFSG.ComponentClassification.Burgoyne.U.statedSU_eq_gramSU h,
    CFSG.ClassicalGroups.UnitaryFlag.mem_gramSU]
  refine ⟨?_, ?_⟩
  · simpa only [Units.val_one, Matrix.mul_one] using
      (CFSG.ComponentClassification.Burgoyne.U.mem_uU h).1 B.2
  · rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]

private theorem uConjAut_mul_inv_of_uConjAut_eq_one {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {A s : uU h 5}
    (hs1 : uConjAut h (by norm_num) s = 1) :
    uConjAut h (by norm_num) A = uConjAut h (by norm_num) (A * s⁻¹) := by
  calc uConjAut h (by norm_num) A = uConjAut h (by norm_num) (A * s⁻¹ * s) := by
        rw [show A * s⁻¹ * s = A by group]
    _ = uConjAut h (n := 5) (by norm_num) (A * s⁻¹) *
        uConjAut h (n := 5) (by norm_num) s :=
        map_mul (uConjAut h (n := 5) (by norm_num)) _ _
    _ = uConjAut h (by norm_num) (A * s⁻¹) := by rw [hs1, mul_one]

private theorem det_mul_inv_eq_one {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {A s : uU h 5} {c : Kˣ}
    (hs : (s : GL (Fin 5) K) = Matrix.GeneralLinearGroup.scalar (Fin 5) c)
    (hc5 : c ^ 5 = Matrix.GeneralLinearGroup.det (A : GL (Fin 5) K)) :
    Matrix.GeneralLinearGroup.det ((A * s⁻¹ : uU h 5) : GL (Fin 5) K) = 1 := by
  change Matrix.GeneralLinearGroup.det ((A : GL (Fin 5) K) * (s : GL (Fin 5) K)⁻¹) = 1
  rw [hs, map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hc5]
  exact mul_inv_cancel _

private theorem uConjAut_of_SU_eq_conj {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {B : uU h 5} (g : StatedSU 5 (2 ^ f) K)
    (hg : (g : GL (Fin 5) K) = (B : GL (Fin 5) K)) :
    uConjAut h (by norm_num) B = MulAut.conj
      (CFSG.ComponentClassification.Burgoyne.Proj.projH
        (StatedSU 5 (2 ^ f) K) g) := by
  have hB : B = (⟨(g : GL (Fin 5) K),
      CFSG.ComponentClassification.Burgoyne.U.statedSU_le_uU h g.2⟩ : uU h 5) :=
    Subtype.ext hg.symm
  rw [hB]
  exact uConjAut_coe_SU_eq_conjProjH h (by norm_num) g

private theorem exists_inner_of_fifth_power_det {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {A : uU h 5} {c : Kˣ} (hc : h.norm (c : K) = 1)
    (hc5 : c ^ 5 = Matrix.GeneralLinearGroup.det (A : GL (Fin 5) K)) :
    uConjAut h (by norm_num) A ∈ (MulAut.conj :
      StatedProj (StatedSU 5 (2 ^ f) K) →*
      MulAut (StatedProj (StatedSU 5 (2 ^ f) K))).range := by
  let s : uU h 5 :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 5) c, scalar_mem_uU_of_norm_one h hc⟩
  have hs : (s : GL (Fin 5) K) = Matrix.GeneralLinearGroup.scalar (Fin 5) c := rfl
  have hs1 : uConjAut h (by norm_num) s = 1 := by
    rw [show uConjAut h (by norm_num) s = 1 ↔
        ∃ b : Kˣ, (s : GL (Fin 5) K) = Matrix.GeneralLinearGroup.scalar (Fin 5) b from
      CFSG.ComponentClassification.Burgoyne.U.uConjAut_eq_one_iff h (by norm_num) s]
    exact ⟨c, hs⟩
  let B : uU h 5 := A * s⁻¹
  have hdet : Matrix.GeneralLinearGroup.det (B : GL (Fin 5) K) = 1 :=
    det_mul_inv_eq_one h hs hc5
  have hAeq : uConjAut h (by norm_num) A = uConjAut h (by norm_num) B :=
    uConjAut_mul_inv_of_uConjAut_eq_one h hs1
  let g : StatedSU 5 (2 ^ f) K := ⟨B, mem_statedSU_of_det_one h hdet⟩
  refine ⟨CFSG.ComponentClassification.Burgoyne.Proj.projH
    (StatedSU 5 (2 ^ f) K) g, ?_⟩
  rw [hAeq]
  exact (uConjAut_of_SU_eq_conj h (B := B) g rfl).symm

private theorem not_fifth_power_of_det_of_outer {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {A : uU h 5}
    (hA : uConjAut h (by norm_num) A ∉ (MulAut.conj :
      StatedProj (StatedSU 5 (2 ^ f) K) →*
      MulAut (StatedProj (StatedSU 5 (2 ^ f) K))).range)
    {c : Kˣ} (hc : h.norm (c : K) = 1) :
    c ^ 5 ≠ Matrix.GeneralLinearGroup.det (A : GL (Fin 5) K) := by
  intro hc5
  exact hA (exists_inner_of_fifth_power_det h hc hc5)

private theorem det_norm_one {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {A : uU h 5} :
    h.norm (Matrix.GeneralLinearGroup.det (A : GL (Fin 5) K) : K) = 1 := by
  have h1 := (CFSG.ComponentClassification.Burgoyne.U.mem_uU h).1 A.2
  have h2 := congrArg (fun M : Matrix (Fin 5) (Fin 5) K => M.det) h1
  have hbar : (((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map h.bar).det =
      h.bar (((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det) :=
    (RingHom.map_det h.bar _).symm
  rw [Matrix.det_mul, Matrix.det_transpose, hbar, Matrix.det_one,
    ← Matrix.GeneralLinearGroup.val_det_apply] at h2
  rw [UnitaryFieldData.norm, mul_comm]
  exact h2

private theorem exists_SU_mul_diag {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {A : uU h 5} {d : Kˣ}
    (hdA : d = Matrix.GeneralLinearGroup.det (A : GL (Fin 5) K))
    {δ : uU h 5} (hdetδ : Matrix.GeneralLinearGroup.det (δ : GL (Fin 5) K) = d) :
    ∃ s₀ : StatedSU 5 (2 ^ f) K,
      (s₀ : GL (Fin 5) K) * (δ : GL (Fin 5) K) = (A : GL (Fin 5) K) := by
  let g : GL (Fin 5) K := (A : GL (Fin 5) K) * (δ : GL (Fin 5) K)⁻¹
  have hgU : g ∈ uU h 5 := mul_mem A.2 (inv_mem δ.2)
  have hgdet : Matrix.GeneralLinearGroup.det g = 1 := by
    change Matrix.GeneralLinearGroup.det
      ((A : GL (Fin 5) K) * (δ : GL (Fin 5) K)⁻¹) = 1
    rw [map_mul, map_inv, hdetδ, ← hdA]
    exact mul_inv_cancel d
  have hgSU : g ∈ StatedSU 5 (2 ^ f) K := by
    rw [CFSG.ComponentClassification.Burgoyne.U.statedSU_eq_gramSU h,
      CFSG.ClassicalGroups.UnitaryFlag.mem_gramSU]
    refine ⟨?_, ?_⟩
    · simpa only [Units.val_one, Matrix.mul_one] using
        (CFSG.ComponentClassification.Burgoyne.U.mem_uU h).1 hgU
    · rw [← Matrix.GeneralLinearGroup.val_det_apply, hgdet, Units.val_one]
  refine ⟨⟨g, hgSU⟩, ?_⟩
  change g * (δ : GL (Fin 5) K) = (A : GL (Fin 5) K)
  dsimp [g]
  group

private theorem exists_diag_split {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {A : uU h 5} {d : Kˣ}
    (hdA : d = Matrix.GeneralLinearGroup.det (A : GL (Fin 5) K)) :
    ∃ (δFun : Fin 5 → Kˣ) (δ : uU h 5) (s : StatedProj (StatedSU 5 (2 ^ f) K))
      (α : MulAut (StatedProj (StatedSU 5 (2 ^ f) K))),
      δFun = Pi.mulSingle (0 : Fin 5) d ∧ (δ : GL (Fin 5) K) = TauCeti.diagGL δFun ∧
      α = uConjAut h (by norm_num) δ ∧ uConjAut h (by norm_num) A = MulAut.conj s * α := by
  have hnorm_d : h.norm (d : K) = 1 := by
    rw [hdA]
    exact det_norm_one h
  let δFun : Fin 5 → Kˣ := Pi.mulSingle (0 : Fin 5) d
  have hδnorm : ∀ j, h.norm ((δFun j : Kˣ) : K) = 1 := by
    simpa [δFun] using norm_mulSingle_family h hnorm_d (0 : Fin 5)
  let δ : uU h 5 := diagU h δFun hδnorm
  have hdetδ : Matrix.GeneralLinearGroup.det (δ : GL (Fin 5) K) = d := by
    change Matrix.GeneralLinearGroup.det (TauCeti.diagGL δFun) = d
    rw [TauCeti.det_diagGL]
    simp [δFun]
  obtain ⟨s₀, hs₀⟩ := exists_SU_mul_diag h hdA hdetδ
  refine ⟨δFun, δ, CFSG.ComponentClassification.Burgoyne.Proj.projH
      (StatedSU 5 (2 ^ f) K) s₀, uConjAut h (by norm_num) δ, rfl, rfl, rfl, ?_⟩
  have hAδ : (A : uU h 5) =
      (⟨s₀, CFSG.ComponentClassification.Burgoyne.U.statedSU_le_uU h s₀.2⟩ : uU h 5) * δ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact hs₀.symm
  calc uConjAut h (by norm_num) A
      = uConjAut h (by norm_num)
          ((⟨s₀, CFSG.ComponentClassification.Burgoyne.U.statedSU_le_uU h s₀.2⟩ : uU h 5) *
            δ) := by rw [hAδ]
    _ = uConjAut h (n := 5) (by norm_num)
          ⟨s₀, CFSG.ComponentClassification.Burgoyne.U.statedSU_le_uU h s₀.2⟩ *
        uConjAut h (n := 5) (by norm_num) δ :=
        map_mul (uConjAut h (n := 5) (by norm_num)) _ _
    _ = MulAut.conj (CFSG.ComponentClassification.Burgoyne.Proj.projH
          (StatedSU 5 (2 ^ f) K) s₀) * uConjAut h (by norm_num) δ := by
        rw [uConjAut_coe_SU_eq_conjProjH h (by norm_num) s₀]
        rfl
private theorem norm_of_diag_torus_factor {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {ζ μ d : Kˣ} (hζ : h.norm (ζ : K) = 1)
    (hμ : h.norm (μ : K) = 1) (hd : h.norm (d : K) = 1)
    {δFun : Fin 5 → Kˣ} (hδFun : δFun = Pi.mulSingle (0 : Fin 5) d) (k : ℤ) (i : Fin 4) :
    ∀ j, h.norm ((((Pi.mulSingle (Fin.castSucc i) ζ : Fin 5 → Kˣ) j) *
      ((δFun ^ (-k)) j) * (fun _ : Fin 5 => μ⁻¹) j : Kˣ) : K) = 1 := by
  intro j
  have hζj : h.norm (((Pi.mulSingle (Fin.castSucc i) ζ : Fin 5 → Kˣ) j : Kˣ) : K) = 1 :=
    norm_mulSingle_family h hζ (Fin.castSucc i) j
  have hδj : h.norm (((δFun ^ (-k)) j : Kˣ) : K) = 1 := by
    have hδj0 : h.norm ((δFun j : Kˣ) : K) = 1 := by
      rw [hδFun]
      exact norm_mulSingle_family h hd (0 : Fin 5) j
    rw [show (δFun ^ (-k)) j = (δFun j) ^ (-k) by simp]
    exact unitary_norm_zpow_eq_one h hδj0 (-k)
  have hμj : h.norm (((fun _ : Fin 5 => μ⁻¹) j : Kˣ) : K) = 1 := by
    simpa using unitary_norm_zpow_eq_one h hμ (-1)
  simp only [Units.val_mul]
  rw [unitary_norm_mul, unitary_norm_mul, hζj, hδj, hμj, mul_one, one_mul]

private theorem prod_of_diag_torus_factor {K : Type} [Field K]
    {ζ μ d : Kˣ} {k : ℤ} {δFun : Fin 5 → Kˣ}
    (hδFun : δFun = Pi.mulSingle (0 : Fin 5) d) (hζeq : ζ = d ^ k * μ ^ 5) (i : Fin 4) :
    (∏ j, ((Pi.mulSingle (Fin.castSucc i) ζ : Fin 5 → Kˣ) j) *
      ((δFun ^ (-k)) j) * (fun _ : Fin 5 => μ⁻¹) j) = 1 := by
  have hδprod : (∏ j, (δFun ^ (-k)) j) = d ^ (-k) := by
    rw [show (∏ j, (δFun ^ (-k)) j) = ∏ j, (δFun j) ^ (-k) by simp]
    rw [Finset.prod_zpow]
    congr 1
    simp [hδFun]
  have hμprod : (∏ j, (fun _ : Fin 5 => μ⁻¹) j) = (μ ^ 5)⁻¹ := by
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ∏ j, ((Pi.mulSingle (Fin.castSucc i) ζ : Fin 5 → Kˣ) j) *
        ((δFun ^ (-k)) j) * (fun _ : Fin 5 => μ⁻¹) j
      = (∏ j, (Pi.mulSingle (Fin.castSucc i) ζ : Fin 5 → Kˣ) j) *
          (∏ j, (δFun ^ (-k)) j) * (∏ j, (fun _ : Fin 5 => μ⁻¹) j) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = ζ * d ^ (-k) * (μ ^ 5)⁻¹ := by
        rw [Fintype.prod_pi_mulSingle', hδprod, hμprod]
    _ = 1 := by
        rw [hζeq]
        rw [show d ^ (-k) = (d ^ k)⁻¹ by rw [zpow_neg]]
        calc d ^ k * μ ^ 5 * (d ^ k)⁻¹ * (μ ^ 5)⁻¹
            = (d ^ k * (d ^ k)⁻¹) * (μ ^ 5 * (μ ^ 5)⁻¹) := by ac_rfl
          _ = 1 := by simp

private theorem eq_mul_inv_mul_inv {G : Type*} [CommGroup G] (a b c : G) :
    a = a * b⁻¹ * c⁻¹ * b * c := by
  symm
  calc a * b⁻¹ * c⁻¹ * b * c = a * (b⁻¹ * b) * (c⁻¹ * c) := by ac_rfl
    _ = a := by simp

private theorem exists_torus_family {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {ζ μ d : Kˣ} (hζ : h.norm (ζ : K) = 1)
    (hμ : h.norm (μ : K) = 1) (hd : h.norm (d : K) = 1)
    {k : ℤ} {δFun : Fin 5 → Kˣ} (hδFun : δFun = Pi.mulSingle (0 : Fin 5) d)
    (hζeq : ζ = d ^ k * μ ^ 5) :
    ∃ u : Fin 4 → Fin 5 → Kˣ,
      (∀ i, u i = Pi.mulSingle (Fin.castSucc i) ζ * (δFun ^ (-k)) *
        (fun _ : Fin 5 => μ⁻¹)) ∧
      (∀ i j, h.norm ((u i j : Kˣ) : K) = 1) ∧ (∀ i, ∏ j, u i j = 1) := by
  let u : Fin 4 → Fin 5 → Kˣ := fun i =>
    Pi.mulSingle (Fin.castSucc i) ζ * (δFun ^ (-k)) * (fun _ : Fin 5 => μ⁻¹)
  refine ⟨u, fun i => rfl, ?_, ?_⟩
  · intro i j
    exact norm_of_diag_torus_factor h hζ hμ hd hδFun k i j
  · intro i
    exact prod_of_diag_torus_factor hδFun hζeq i

private theorem isMulCommutative_closure_diagSU {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {u : Fin 4 → Fin 5 → Kˣ}
    (hu : ∀ i j, h.norm ((u i j : Kˣ) : K) = 1)
    (hprod : ∀ i, ∏ j, u i j = 1) :
    IsMulCommutative (Subgroup.closure (Set.range (fun i : Fin 4 =>
      CFSG.ComponentClassification.Burgoyne.Proj.projH
        (StatedSU 5 (2 ^ f) K) (diagSU h (u i) (hu i) (hprod i))))) := by
  let t : Fin 4 → StatedSU 5 (2 ^ f) K := fun i => diagSU h (u i) (hu i) (hprod i)
  let q : Fin 4 → StatedProj (StatedSU 5 (2 ^ f) K) := fun i =>
    CFSG.ComponentClassification.Burgoyne.Proj.projH (StatedSU 5 (2 ^ f) K) (t i)
  change IsMulCommutative (Subgroup.closure (Set.range q))
  refine Subgroup.isMulCommutative_closure ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
  change q i * q j = q j * q i
  rw [← map_mul (CFSG.ComponentClassification.Burgoyne.Proj.projH
      (StatedSU 5 (2 ^ f) K)),
    ← map_mul (CFSG.ComponentClassification.Burgoyne.Proj.projH
      (StatedSU 5 (2 ^ f) K))]
  congr 1
  apply Subtype.ext
  simpa only [t, diagSU, Subgroup.coe_mul] using diagGL_mul_comm (u i) (u j)

private theorem diagSU_fixes_diagClass {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {u : Fin 4 → Fin 5 → Kˣ}
    (hu : ∀ i j, h.norm ((u i j : Kˣ) : K) = 1)
    (hprod : ∀ i, ∏ j, u i j = 1) {δFun : Fin 5 → Kˣ}
    {δ : uU h 5} (hδ : (δ : GL (Fin 5) K) = TauCeti.diagGL δFun)
    {α : MulAut (StatedProj (StatedSU 5 (2 ^ f) K))}
    (hα : α = uConjAut h (by norm_num) δ) :
    ∀ z ∈ Subgroup.closure (Set.range (fun i : Fin 4 =>
      CFSG.ComponentClassification.Burgoyne.Proj.projH
        (StatedSU 5 (2 ^ f) K) (diagSU h (u i) (hu i) (hprod i)))), α z = z := by
  let t : Fin 4 → StatedSU 5 (2 ^ f) K := fun i => diagSU h (u i) (hu i) (hprod i)
  let q : Fin 4 → StatedProj (StatedSU 5 (2 ^ f) K) := fun i =>
    CFSG.ComponentClassification.Burgoyne.Proj.projH (StatedSU 5 (2 ^ f) K) (t i)
  change ∀ z ∈ Subgroup.closure (Set.range q), α z = z
  intro z hz
  refine Subgroup.closure_induction (p := fun z _ => α z = z) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨i, rfl⟩
    rw [hα]
    dsimp only [q]
    rw [CFSG.ComponentClassification.Burgoyne.U.uConjAut_proj]
    congr 1
    apply Subtype.ext
    simp only [t, diagSU, hδ]
    exact diagGL_conj_eq_self (u i) δFun
  · exact map_one _
  · intro x y _ _ ihx ihy
    rw [map_mul, ihx, ihy]
  · intro x _ ih
    rw [map_inv, ih]

private theorem diagGL_coordinate_eq_torus {K : Type} [Field K]
    {ζ μ : Kˣ} {k : ℤ} {δFun : Fin 5 → Kˣ} {u : Fin 4 → Fin 5 → Kˣ}
    (hudef : ∀ i, u i = Pi.mulSingle (Fin.castSucc i) ζ * (δFun ^ (-k)) *
      (fun _ : Fin 5 => μ⁻¹)) (i : Fin 4) :
    TauCeti.diagGL (Pi.mulSingle (Fin.castSucc i) ζ) =
      TauCeti.diagGL (u i) * (TauCeti.diagGL δFun) ^ k *
        TauCeti.diagGL (fun _ : Fin 5 => μ) := by
  calc TauCeti.diagGL (Pi.mulSingle (Fin.castSucc i) ζ)
      = TauCeti.diagGL (u i * (δFun ^ k) * (fun _ : Fin 5 => μ)) := by
        congr 1
        funext j
        have hk : (δFun ^ (-k)) j = ((δFun ^ k) j)⁻¹ := by simp
        rw [hudef i]
        simp only [Pi.mul_apply, hk]
        exact eq_mul_inv_mul_inv _ _ _
    _ = TauCeti.diagGL (u i) * TauCeti.diagGL (δFun ^ k) *
        TauCeti.diagGL (fun _ : Fin 5 => μ) := by rw [map_mul, map_mul]
    _ = TauCeti.diagGL (u i) * (TauCeti.diagGL δFun) ^ k *
        TauCeti.diagGL (fun _ : Fin 5 => μ) := by rw [map_zpow]

private theorem diagClass_eq_conj_mul_zpow {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1)
    {d : Kˣ} (hd : h.norm (d : K) = 1) {k : ℤ} {μ : Kˣ}
    (hμ : h.norm (μ : K) = 1) (hζeq : ζ = d ^ k * μ ^ 5)
    {δFun : Fin 5 → Kˣ} (hδFun : δFun = Pi.mulSingle (0 : Fin 5) d)
    {u : Fin 4 → Fin 5 → Kˣ}
    (hudef : ∀ i, u i = Pi.mulSingle (Fin.castSucc i) ζ * (δFun ^ (-k)) *
      (fun _ : Fin 5 => μ⁻¹))
    (hu : ∀ i j, h.norm ((u i j : Kˣ) : K) = 1)
    (hprod : ∀ i, ∏ j, u i j = 1) {δ : uU h 5}
    (hδ : (δ : GL (Fin 5) K) = TauCeti.diagGL δFun)
    {α : MulAut (StatedProj (StatedSU 5 (2 ^ f) K))}
    (hα : α = uConjAut h (by norm_num) δ) :
    ∀ i : Fin 4, diagClass h ζ hζ i =
      MulAut.conj (CFSG.ComponentClassification.Burgoyne.Proj.projH
        (StatedSU 5 (2 ^ f) K) (diagSU h (u i) (hu i) (hprod i))) * α ^ k := by
  let t : Fin 4 → StatedSU 5 (2 ^ f) K := fun i => diagSU h (u i) (hu i) (hprod i)
  let q : Fin 4 → StatedProj (StatedSU 5 (2 ^ f) K) := fun i =>
    CFSG.ComponentClassification.Burgoyne.Proj.projH (StatedSU 5 (2 ^ f) K) (t i)
  let μU : uU h 5 := diagU h (fun _ : Fin 5 => μ) (fun _ => hμ)
  have hdata : h.norm (d : K) = 1 ∧ ζ = d ^ k * μ ^ 5 ∧
      δFun = Pi.mulSingle (0 : Fin 5) d := ⟨hd, hζeq, hδFun⟩
  clear hdata
  intro i
  have hGL := diagGL_coordinate_eq_torus hudef i
  have hUeq : diagU h (Pi.mulSingle (Fin.castSucc i) ζ)
      (norm_mulSingle_family h hζ (Fin.castSucc i)) =
      (⟨t i, CFSG.ComponentClassification.Burgoyne.U.statedSU_le_uU h (t i).2⟩ : uU h 5) *
        δ ^ k * μU := by
    apply Subtype.ext
    simpa only [diagU, t, diagSU, μU, Subgroup.coe_mul, SubgroupClass.coe_zpow, hδ] using hGL
  have hscalar : uConjAut h (by norm_num) μU = 1 := by
    rw [show uConjAut h (by norm_num) μU = 1 ↔
        ∃ b : Kˣ, (μU : GL (Fin 5) K) = Matrix.GeneralLinearGroup.scalar (Fin 5) b from
      CFSG.ComponentClassification.Burgoyne.U.uConjAut_eq_one_iff h (by norm_num) μU]
    exact ⟨μ, by simp [μU, diagU, TauCeti.diagGL_const]⟩
  calc diagClass h ζ hζ i
      = uConjAut h (by norm_num)
          (diagU h (Pi.mulSingle (Fin.castSucc i) ζ)
            (norm_mulSingle_family h hζ (Fin.castSucc i))) := rfl
    _ = uConjAut h (by norm_num)
          ((⟨t i, CFSG.ComponentClassification.Burgoyne.U.statedSU_le_uU h (t i).2⟩ :
            uU h 5) * δ ^ k * μU) := by rw [hUeq]
    _ = uConjAut h (n := 5) (by norm_num)
          ⟨t i, CFSG.ComponentClassification.Burgoyne.U.statedSU_le_uU h (t i).2⟩ *
        (uConjAut h (n := 5) (by norm_num) δ) ^ k *
          uConjAut h (n := 5) (by norm_num) μU := by
        rw [map_mul, map_mul, map_zpow (uConjAut h (n := 5) (by norm_num))]
    _ = MulAut.conj (q i) * α ^ k := by
        rw [hscalar, mul_one,
          uConjAut_coe_SU_eq_conjProjH h (by norm_num) (t i), ← hα]
        rfl

private theorem diagClass_mem_torus_sup {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1)
    {d : Kˣ} (hd : h.norm (d : K) = 1) {k : ℤ} {μ : Kˣ}
    (hμ : h.norm (μ : K) = 1) (hζeq : ζ = d ^ k * μ ^ 5)
    {δFun : Fin 5 → Kˣ} (hδFun : δFun = Pi.mulSingle (0 : Fin 5) d)
    {u : Fin 4 → Fin 5 → Kˣ}
    (hudef : ∀ i, u i = Pi.mulSingle (Fin.castSucc i) ζ * (δFun ^ (-k)) *
      (fun _ : Fin 5 => μ⁻¹))
    (hu : ∀ i j, h.norm ((u i j : Kˣ) : K) = 1)
    (hprod : ∀ i, ∏ j, u i j = 1) {δ : uU h 5}
    (hδ : (δ : GL (Fin 5) K) = TauCeti.diagGL δFun)
    {α : MulAut (StatedProj (StatedSU 5 (2 ^ f) K))}
    (hα : α = uConjAut h (by norm_num) δ) :
    ∀ i : Fin 4, diagClass h ζ hζ i ∈
      (Subgroup.closure (Set.range (fun i : Fin 4 =>
        CFSG.ComponentClassification.Burgoyne.Proj.projH (StatedSU 5 (2 ^ f) K)
          (diagSU h (u i) (hu i) (hprod i))))).map
        (MulAut.conj : StatedProj (StatedSU 5 (2 ^ f) K) →*
          MulAut (StatedProj (StatedSU 5 (2 ^ f) K))) ⊔ Subgroup.zpowers α := by
  intro i
  rw [diagClass_eq_conj_mul_zpow h hζ hd hμ hζeq hδFun hudef hu hprod hδ hα i]
  refine Subgroup.mul_mem _ ?_ ?_
  · refine Subgroup.mem_sup_left ?_
    exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (Set.mem_range_self i))
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩)

private theorem exists_diag_torus {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1)
    {d : Kˣ} (hd : h.norm (d : K) = 1) {k : ℤ} {μ : Kˣ}
    (hμ : h.norm (μ : K) = 1) (hζeq : ζ = d ^ k * μ ^ 5)
    {δFun : Fin 5 → Kˣ} (hδFun : δFun = Pi.mulSingle (0 : Fin 5) d) {δ : uU h 5}
    (hδ : (δ : GL (Fin 5) K) = TauCeti.diagGL δFun)
    {α : MulAut (StatedProj (StatedSU 5 (2 ^ f) K))}
    (hα : α = uConjAut h (by norm_num) δ) :
    ∃ D : Subgroup (StatedProj (StatedSU 5 (2 ^ f) K)),
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) ∧ (∀ t ∈ D, α t = t) ∧
      (∀ i : Fin 4, diagClass h ζ hζ i ∈ D.map
        (MulAut.conj : StatedProj (StatedSU 5 (2 ^ f) K) →*
          MulAut (StatedProj (StatedSU 5 (2 ^ f) K))) ⊔ Subgroup.zpowers α) := by
  obtain ⟨u, hudef, hu, hprod⟩ := exists_torus_family h hζ hμ hd hδFun hζeq
  let t : Fin 4 → StatedSU 5 (2 ^ f) K := fun i => diagSU h (u i) (hu i) (hprod i)
  let q : Fin 4 → StatedProj (StatedSU 5 (2 ^ f) K) := fun i =>
    CFSG.ComponentClassification.Burgoyne.Proj.projH (StatedSU 5 (2 ^ f) K) (t i)
  have hcomm : IsMulCommutative (Subgroup.closure (Set.range q)) := by
    simpa only [t, q] using isMulCommutative_closure_diagSU h hu hprod
  have hfixD : ∀ z ∈ Subgroup.closure (Set.range q), α z = z := by
    simpa only [t, q] using diagSU_fixes_diagClass h hu hprod hδ hα
  have hmem : ∀ i : Fin 4, diagClass h ζ hζ i ∈
      (Subgroup.closure (Set.range q)).map
        (MulAut.conj : StatedProj (StatedSU 5 (2 ^ f) K) →*
          MulAut (StatedProj (StatedSU 5 (2 ^ f) K))) ⊔ Subgroup.zpowers α := by
    simpa only [t, q] using
      diagClass_mem_torus_sup h hζ hd hμ hζeq hδFun hudef hu hprod hδ hα
  refine ⟨Subgroup.closure (Set.range q), ?_, hfixD, hmem⟩
  intro a ha b hb
  exact congrArg Subtype.val (hcomm.is_comm.comm
    (⟨a, ha⟩ : Subgroup.closure (Set.range q))
    (⟨b, hb⟩ : Subgroup.closure (Set.range q)))

private theorem exists_zeta_fifth_data {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) {A : uU h 5}
    (hA : uConjAut h (by norm_num) A ∉ (MulAut.conj :
      StatedProj (StatedSU 5 (2 ^ f) K) →*
      MulAut (StatedProj (StatedSU 5 (2 ^ f) K))).range)
    {d : Kˣ} (hdA : d = Matrix.GeneralLinearGroup.det (A : GL (Fin 5) K))
    (hd : h.norm (d : K) = 1) (h5 : 5 ∣ 2 ^ f + 1) :
    ∃ (ζ μ : Kˣ) (k : ℤ), orderOf ζ = 5 ∧ h.norm (ζ : K) = 1 ∧
      h.norm (μ : K) = 1 ∧ ζ = d ^ k * μ ^ 5 := by
  let H : Subgroup Kˣ := (Units.map h.normHom).ker
  have hcardH : Nat.card H = 2 ^ f + 1 := by
    simpa [H] using h.card_ker_normUnits_and_surjective.1
  have h5H : 5 ∣ Nat.card H := by
    rw [hcardH]
    exact h5
  have hdH : d ∈ H := by
    rw [show d ∈ (Units.map h.normHom).ker ↔ h.norm (d : K) = 1 from
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.mem_ker_normUnits h]
    exact hd
  have hd5 : ∀ μ : H, (μ : Kˣ) ^ 5 ≠ d := by
    intro μ hμ
    exact not_fifth_power_of_det_of_outer h hA
      ((CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.mem_ker_normUnits h).1 μ.2)
      (by simpa [hdA] using hμ)
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' (p := 5) (hp := ⟨Nat.prime_five⟩) h5H
  have hζnorm : h.norm ((ζ : Kˣ) : K) = 1 :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.mem_ker_normUnits h).1 ζ.2
  have hd5H : ∀ ν : H, ν ^ 5 ≠ ⟨d, hdH⟩ := by
    intro ν hν
    exact hd5 ν (by simpa using congrArg (fun x : H => (x : Kˣ)) hν)
  obtain ⟨k, μ, hζeqH⟩ :=
    exists_zpow_mul_pow_five_of_not_fifth_power (d := ⟨d, hdH⟩) (ζ := ζ) hd5H h5H
  have hζeq : (ζ : Kˣ) = d ^ k * (μ : Kˣ) ^ 5 := by
    simpa using congrArg (fun x : H => (x : Kˣ)) hζeqH
  have hμnorm : h.norm ((μ : Kˣ) : K) = 1 :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.mem_ker_normUnits h).1 μ.2
  refine ⟨(ζ : Kˣ), (μ : Kˣ), k, ?_, hζnorm, hμnorm, hζeq⟩
  rw [Subgroup.orderOf_coe]
  exact hζo

theorem exists_split_psu_five {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {A : uU h 5}
    (hA : uConjAut h (by norm_num) A ∉ (MulAut.conj : StatedProj (StatedSU 5 (2 ^ f) K) →*
      MulAut (StatedProj (StatedSU 5 (2 ^ f) K))).range) :
    ∃ (s : StatedProj (StatedSU 5 (2 ^ f) K)) (D : Subgroup (StatedProj (StatedSU 5 (2 ^ f) K)))
      (α : MulAut (StatedProj (StatedSU 5 (2 ^ f) K))),
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) ∧ uConjAut h (by norm_num) A = MulAut.conj s * α ∧
      (∀ t ∈ D, α t = t) ∧
      4 ≤ CFSG.Open.pRank 5
        (D.map (MulAut.conj : StatedProj (StatedSU 5 (2 ^ f) K) →*
          MulAut (StatedProj (StatedSU 5 (2 ^ f) K))) ⊔ Subgroup.zpowers α) := by
  classical
  let d : Kˣ := Matrix.GeneralLinearGroup.det (A : GL (Fin 5) K)
  obtain ⟨δFun, δ, s, α, hδFun, hδ, hα, hsplit⟩ :=
    exists_diag_split h (A := A) (d := d) rfl
  obtain ⟨ζ, μ, k, hζo, hζnorm, hμnorm, hζeq⟩ :=
    exists_zeta_fifth_data h hA rfl (det_norm_one h) h5
  obtain ⟨D, hDcomm, hfixD, hmem⟩ :=
    exists_diag_torus h hζnorm (det_norm_one h) hμnorm hζeq hδFun hδ hα
  exact ⟨s, D, α, hDcomm, hsplit, hfixD,
    four_le_pRank_of_diagClass h hζnorm hζo hmem⟩

private theorem betaHom_eq_one_of_mem_centralizer {Y : Type} [Group Y] {E : Subgroup Y}
    {P : Type} [Group P] (e' : ↥E ⧸ Subgroup.center ↥E ≃* P) {c : Y}
    (hc : c ∈ Subgroup.centralizer (E : Set Y)) :
    betaHom e' ⟨c, Subgroup.centralizer_le_normalizer (E : Set Y) hc⟩ = 1 := by
  let cN : ↥(Subgroup.normalizer (E : Set Y)) :=
    ⟨c, Subgroup.centralizer_le_normalizer (E : Set Y) hc⟩
  have hker : cN ∈ (Subgroup.normalizerMonoidHom E).ker := by
    rw [Subgroup.normalizerMonoidHom_ker]
    exact Subgroup.mem_subgroupOf.2 hc
  have h1 : Subgroup.normalizerMonoidHom E cN = 1 := MonoidHom.mem_ker.1 hker
  change (MulAut.congr e') (descL ↥E (Subgroup.normalizerMonoidHom E cN)) = 1
  rw [h1, map_one, map_one]

private theorem betaHom_inverted_data {Y : Type} [Group Y] {E : Subgroup Y}
    [Group.IsPerfect ↥E] {P : Type} [Group P]
    (e' : ↥E ⧸ Subgroup.center ↥E ≃* P) {a y : Y}
    (ha : a ∈ Subgroup.normalizer (E : Set Y)) (hy : y ∈ Subgroup.normalizer (E : Set Y))
    (hinv : a * y * a⁻¹ * y ∈ Subgroup.centralizer (E : Set Y))
    (hy5 : y ^ 5 ∈ E ⊔ Subgroup.centralizer (E : Set Y))
    (hyE : y ∉ E ⊔ Subgroup.centralizer (E : Set Y)) :
    (betaHom e' ⟨a, ha⟩ * betaHom e' ⟨y, hy⟩ * (betaHom e' ⟨a, ha⟩)⁻¹ =
      (betaHom e' ⟨y, hy⟩)⁻¹) ∧
    (betaHom e' ⟨y, hy⟩ ^ 5 ∈ (MulAut.conj : P →* MulAut P).range) ∧
    (betaHom e' ⟨y, hy⟩ ∉ (MulAut.conj : P →* MulAut P).range) := by
  have hcent : ((⟨a, ha⟩ * ⟨y, hy⟩ * ⟨a, ha⟩⁻¹ * ⟨y, hy⟩ :
      ↥(Subgroup.normalizer (E : Set Y))) : Y) ∈ Subgroup.centralizer (E : Set Y) := by
    simpa using hinv
  have hone : betaHom e' (⟨a, ha⟩ * ⟨y, hy⟩ * ⟨a, ha⟩⁻¹ * ⟨y, hy⟩) = 1 :=
    betaHom_eq_one_of_mem_centralizer e' hcent
  have hrel : betaHom e' ⟨a, ha⟩ * betaHom e' ⟨y, hy⟩ * (betaHom e' ⟨a, ha⟩)⁻¹ =
      (betaHom e' ⟨y, hy⟩)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    simpa only [map_mul, map_inv] using hone
  have hy5' : (((⟨y, hy⟩ : ↥(Subgroup.normalizer (E : Set Y))) ^ 5 : _) : Y) ∈
      E ⊔ Subgroup.centralizer (E : Set Y) := by
    simpa using hy5
  have hpow : betaHom e' ⟨y, hy⟩ ^ 5 ∈ (MulAut.conj : P →* MulAut P).range := by
    have h := betaHom_mem_inner_of_mem e' (⟨y, hy⟩ ^ 5) hy5'
    simpa only [map_pow] using h
  have houter : betaHom e' ⟨y, hy⟩ ∉ (MulAut.conj : P →* MulAut P).range := by
    intro h
    exact hyE (by simpa using mem_of_betaHom_mem_inner e' ⟨y, hy⟩ h)
  exact ⟨hrel, hpow, houter⟩

theorem four_le_pRank_of_outer_psu_five {Y : Type} [Group Y] [Finite Y] {E : Subgroup Y}
    (hZ : Subgroup.center ↥E = ⊥) {f : ℕ}
    (hm : StatedClassicalModel (↥E ⧸ Subgroup.center ↥E) .PSU 5 2 f) (h5 : 5 ∣ 2 ^ f + 1)
    {a y : Y} (ha : a ∈ Subgroup.normalizer (E : Set Y))
    (hy : y ∈ Subgroup.normalizer (E : Set Y))
    (hinv : a * y * a⁻¹ * y ∈ Subgroup.centralizer (E : Set Y))
    (hy5 : y ^ 5 ∈ E ⊔ Subgroup.centralizer (E : Set Y))
    (hyE : y ∉ E ⊔ Subgroup.centralizer (E : Set Y)) :
    4 ≤ CFSG.Open.pRank 5 (E ⊔ Subgroup.zpowers y) := by
  classical
  obtain ⟨⟨-, hf, -⟩, K, hKfield, hKfin, hKcard, ⟨eP⟩⟩ := hm
  have h : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hKcard, ← pow_mul, mul_comm]⟩
  have hchar : CharP K 2 := h.charP
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSU : Group.IsPerfect (StatedSU 5 (2 ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (n := 5) (p := 2) (f := f) hKcard
      (by norm_num) (by norm_num)
  have hperfSU : Group.IsPerfect (StatedProj (StatedSU 5 (2 ^ f) K)) :=
    Group.IsPerfect.ofSurjective
      (f := QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ f) K)))
      (QuotientGroup.mk'_surjective _)
  let qE : ↥E ≃* ↥E ⧸ Subgroup.center ↥E :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ).symm
  have hperfE : Group.IsPerfect ↥E :=
    Group.IsPerfect.ofSurjective (f := (qE.trans eP).symm.toMonoidHom)
      (qE.trans eP).symm.surjective
  obtain ⟨hrel, hpow, houter⟩ := betaHom_inverted_data eP ha hy hinv hy5 hyE
  have hlin : betaHom eP ⟨y, hy⟩ ∈ (uConjAut h (by omega : 1 ≤ 5)).range :=
    mem_range_uConjAut_of_inverted (m := 5) (r := 5) h (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hrel hpow
  obtain ⟨A, hAeq⟩ := MonoidHom.mem_range.mp hlin
  have hAeq' : uConjAut h (by norm_num : 1 ≤ 5) A = betaHom eP ⟨y, hy⟩ := hAeq
  have hA : uConjAut h (by norm_num : 1 ≤ 5) A ∉
      (MulAut.conj : StatedProj (StatedSU 5 (2 ^ f) K) →*
        MulAut (StatedProj (StatedSU 5 (2 ^ f) K))).range := by
    rw [hAeq']
    exact houter
  obtain ⟨s, D, α, hD, hsplit, hfix, hrank⟩ := exists_split_psu_five h h5 hA
  have hβ : betaHom eP ⟨y, hy⟩ = MulAut.conj s * α := by
    rw [← hAeq', hsplit]
  exact le_pRank_of_split hZ eP hy hD hβ hfix (by norm_num) hrank

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.RankCore
