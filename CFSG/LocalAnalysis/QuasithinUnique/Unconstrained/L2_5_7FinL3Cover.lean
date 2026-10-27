module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourKernelStructure
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverLarge
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinRed

public section

namespace CFSG.QuasithinUnique.Fin257

namespace L3

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.LocalAnalysis.ComponentInitial.LinearCover

open scoped commutatorElement

variable {F : Type} [Field F]

theorem lieModel_L3 [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) :
    CFSG.Blueprint.LieModel (projectiveSL 3 F) .PSL 3 2 n :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, hn, by norm_num, by simp, by simp⟩, F, inferInstance,
    inferInstance, hF, ⟨((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (projectiveSpecialLinearEquivProjectiveSL 3 F)).symm⟩⟩

theorem coverElem_large [Finite F] {n : ℕ} (hn : 3 ≤ n) (hF : Nat.card F = 2 ^ n)
    (R : Subgroup (projectiveSL 3 F)) (hR : IsElemAbelian 2 R) :
    CoverElem (projectiveSL 3 F) R := by
  intro X _ _ hperf η hη hcen h2 _
  have hC : η.ker ≤ Subgroup.center X := fun z hz =>
    Subgroup.mem_center_iff.mpr fun y => (hcen z hz y).symm
  obtain ⟨-, hbij⟩ := even_linear_three_large_field_catalog_central_two_cover_trivial η hη hC h2
    hn (lieModel_L3 (by omega) hF)
  have hinj : Function.Injective η := hbij.1
  refine ⟨isMulCommutative_iff_of_setLike.mpr ?_, ?_⟩
  · intro x hx y hy
    apply hinj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hR.1.is_comm.comm ⟨η x, hx⟩ ⟨η y, hy⟩)
  · intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hR.2 _ hx

theorem isElemAbelian_of_decomp {α X : Type*} [Group X] (S : Subgroup X) (p q : α → X)
    (hpp : ∀ a a', Commute (p a) (p a')) (hqq : ∀ b b', Commute (q b) (q b'))
    (hpq : ∀ a b, Commute (p a) (q b)) (hp2 : ∀ a, p a * p a = 1) (hq2 : ∀ b, q b * q b = 1)
    (hS : ∀ v ∈ S, ∃ a b : α, ∃ z : X, (∀ g, g * z = z * g) ∧ z * z = 1 ∧ v = p a * q b * z) :
    IsElemAbelian 2 S := by
  have hcz : ∀ (A z : X), (∀ g, g * z = z * g) → Commute A z := fun A z hz => hz A
  refine ⟨isMulCommutative_iff_of_setLike.mpr ?_, ?_⟩
  · intro v hv v' hv'
    obtain ⟨a, b, z, hz, hz2, rfl⟩ := hS v hv
    obtain ⟨a', b', z', hz', hz2', rfl⟩ := hS v' hv'
    have h1 : Commute (p a) (p a' * q b') := (hpp a a').mul_right (hpq a b')
    have h2 : Commute (q b) (p a' * q b') := (hpq a' b).symm.mul_right (hqq b b')
    have h3 : Commute (p a * q b) (p a' * q b') := h1.mul_left h2
    exact ((h3.mul_right (hcz _ z' hz')).mul_left
      ((hcz (p a' * q b') z hz).symm.mul_right (hcz z z' hz')))
  · intro v hv
    obtain ⟨a, b, z, hz, hz2, rfl⟩ := hS v hv
    rw [Commute.mul_pow (hcz _ z hz), Commute.mul_pow (hpq a b), pow_two (p a), hp2, pow_two (q b),
      hq2, pow_two z, hz2]
    simp

open LinearFieldFourKernel in
theorem cover_four_facts [CharP F 2] (hk : Nat.card F = 4) {X : Type} [Group X]
    (η : X →* projectiveSL 3 F) (hη : Function.Surjective η)
    (hker : ∀ z, η z = 1 → z ∈ Subgroup.center X) (hsq : ∀ z, η z = 1 → z * z = 1) :
    (∀ c a, wxComm η hη c a = 1) ∧ (∀ c b, wyComm η hη c b = 1) ∧
    (∀ c, lift η hη (wP c) * lift η hη (wP c) = 1) ∧
    (∀ a, lift η hη (xP a) * lift η hη (xP a) = 1) ∧
    (∀ b, lift η hη (yP b) * lift η hη (yP b) = 1) := by
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hk
  have hω3 : ω * ω * ω = 1 := omega_cube hk hω0
  obtain ⟨u, hu⟩ := hη (hP ω hω3)
  have hsame : ∀ d d' : X, η d = η d' → d * d = d' * d' := by
    intro d d' h
    have hz : η (d⁻¹ * d') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have hzc := Subgroup.mem_center_iff.mp (hker _ hz)
    have hz2 := hsq _ hz
    set z := d⁻¹ * d' with hzdef
    have hd' : d' = d * z := by rw [hzdef]; group
    calc d * d = d * d * (z * z) := by rw [hz2, mul_one]
      _ = d * (d * z) * z := by group
      _ = d * (z * d) * z := by rw [hzc d]
      _ = (d * z) * (d * z) := by group
      _ = d' * d' := by rw [← hd']
  have hd : ∀ a b : F, rootComm η hη a b * rootComm η hη a b = wxComm η hη (a * b * a) 1 := by
    intro a b
    have h := rootComm_sq η hη hker a b
    rw [pow_two] at h
    rw [h, wxComm_eq_one η hη hker hω3 u hu hk hω0 hω1 (a * b) a]
  have hLconst : ∀ z z' : F, z ≠ 0 → z' ≠ 0 → wxComm η hη z 1 = wxComm η hη z' 1 := by
    intro z z' hz hz'
    have e1 := hd z z⁻¹
    rw [show z * z⁻¹ * z = z by field_simp] at e1
    have e2 := hd z' z'⁻¹
    rw [show z' * z'⁻¹ * z' = z' by field_simp] at e2
    have := hsame (rootComm η hη z z⁻¹) (rootComm η hη z' z'⁻¹)
      (by rw [map_rootComm, map_rootComm, mul_inv_cancel₀ hz, mul_inv_cancel₀ hz'])
    rw [e1, e2] at this
    exact this
  have hω1' : ω + 1 ≠ 0 := by
    intro h
    apply hω1
    linear_combination h - (CharP.cast_eq_zero F 2)
  have hL1 : wxComm η hη 1 1 = 1 := by
    have hadd := wxComm_add_left η hη hker ω 1 1
    have e1 : wxComm η hη (ω + 1) 1 = wxComm η hη 1 1 := hLconst _ _ hω1' one_ne_zero
    have e2 : wxComm η hη ω 1 = wxComm η hη 1 1 := hLconst _ _ hω0 one_ne_zero
    rw [e1, e2] at hadd
    exact left_eq_mul.mp hadd
  have hL : ∀ z : F, wxComm η hη z 1 = 1 := by
    intro z
    by_cases hz : z = 0
    · rw [hz, wxComm_zero_left η hη hker]
    · rw [hLconst z 1 hz one_ne_zero, hL1]
  have F1 : ∀ c a, wxComm η hη c a = 1 := fun c a => by
    rw [wxComm_eq_one η hη hker hω3 u hu hk hω0 hω1 c a, hL]
  have F2 : ∀ c b, wyComm η hη c b = 1 := fun c b => by
    rw [wyComm_eq η hη hker hω3 u hu hk hω0 hω1 c b, hL]
  have F3 : ∀ c, lift η hη (wP c) * lift η hη (wP c) = 1 := fun c => by
    have := hsame (lift η hη (wP c)) (rootComm η hη c 1)
      (by rw [map_lift, map_rootComm, mul_one])
    rw [this, hd, hL]
  refine ⟨F1, F2, F3, fun a => ?_, fun b => ?_⟩
  · have hcen := lift_xP_sq_mem_center η hη hker a
    set w := lift η hη (s₂₃P : projectiveSL 3 F) with hw
    have hy : η (w⁻¹ * lift η hη (xP a) * w) = η (lift η hη (wP a)) := by
      rw [map_mul, map_mul, map_inv, map_lift, map_lift, map_lift, s₂₃P_conj_xP]
    have h1 := hsame _ _ hy
    have hc := Subgroup.mem_center_iff.mp hcen w⁻¹
    calc lift η hη (xP a) * lift η hη (xP a) =
        w⁻¹ * (lift η hη (xP a) * lift η hη (xP a)) * w := by
          rw [hc]; group
      _ = (w⁻¹ * lift η hη (xP a) * w) * (w⁻¹ * lift η hη (xP a) * w) := by group
      _ = lift η hη (wP a) * lift η hη (wP a) := h1
      _ = 1 := F3 a
  · have hcen := lift_yP_sq_mem_center η hη hker b
    set w := lift η hη (s₁₂P : projectiveSL 3 F) with hw
    have hy : η (w⁻¹ * lift η hη (yP b) * w) = η (lift η hη (wP b)) := by
      rw [map_mul, map_mul, map_inv, map_lift, map_lift, map_lift, s₁₂P_conj_yP]
    have h1 := hsame _ _ hy
    have hc := Subgroup.mem_center_iff.mp hcen w⁻¹
    calc lift η hη (yP b) * lift η hη (yP b) =
        w⁻¹ * (lift η hη (yP b) * lift η hη (yP b)) * w := by
          rw [hc]; group
      _ = (w⁻¹ * lift η hη (yP b) * w) * (w⁻¹ * lift η hη (yP b) * w) := by group
      _ = lift η hη (wP b) * lift η hη (wP b) := h1
      _ = 1 := F3 b

open LinearFieldFourKernel in
theorem coverElem_four_V1 [Finite F] [CharP F 2] (hk : Nat.card F = 4) :
    CoverElem (projectiveSL 3 F) (V1 : Subgroup (projectiveSL 3 F)) := by
  intro X _ _ hperf η hη hcen h2 hsq
  have hker : ∀ z, η z = 1 → z ∈ Subgroup.center X := fun z hz =>
    Subgroup.mem_center_iff.mpr fun y => (hcen z hz y).symm
  have hsq' : ∀ z, η z = 1 → z * z = 1 := fun z hz => by
    rw [← pow_two]
    exact hsq z (MonoidHom.mem_ker.mpr hz)
  obtain ⟨F1, F2, F3, F4, F5⟩ := cover_four_facts hk η hη hker hsq'
  refine isElemAbelian_of_decomp _ (fun a => lift η hη (xP a)) (fun c => lift η hη (wP c))
    ?_ ?_ ?_ F4 F3 ?_
  · intro a a'
    exact (projRoots (K := F)).preimage_x_comm η hker hη _ _ ⟨a, map_lift η hη _⟩
      ⟨a', map_lift η hη _⟩
  · intro c c'
    exact (projRoots (K := F)).preimage_w_comm η hker hη _ _ ⟨c, map_lift η hη _⟩
      ⟨c', map_lift η hη _⟩
  · intro a c
    exact (commutatorElement_eq_one_iff_mul_comm.mp (F1 c a)).symm
  · intro v hv
    obtain ⟨a, c, hvac⟩ := hv
    have hz : η ((lift η hη (xP a) * lift η hη (wP c))⁻¹ * v) = 1 := by
      rw [map_mul, map_inv, map_mul, map_lift, map_lift, hvac]
      exact inv_mul_cancel _
    exact ⟨a, c, _, fun g => (Subgroup.mem_center_iff.mp (hker _ hz) g), hsq' _ hz, by group⟩

open LinearFieldFourKernel in
theorem coverElem_four_V2 [Finite F] [CharP F 2] (hk : Nat.card F = 4) :
    CoverElem (projectiveSL 3 F) (V2 : Subgroup (projectiveSL 3 F)) := by
  intro X _ _ hperf η hη hcen h2 hsq
  have hker : ∀ z, η z = 1 → z ∈ Subgroup.center X := fun z hz =>
    Subgroup.mem_center_iff.mpr fun y => (hcen z hz y).symm
  have hsq' : ∀ z, η z = 1 → z * z = 1 := fun z hz => by
    rw [← pow_two]
    exact hsq z (MonoidHom.mem_ker.mpr hz)
  obtain ⟨F1, F2, F3, F4, F5⟩ := cover_four_facts hk η hη hker hsq'
  refine isElemAbelian_of_decomp _ (fun b => lift η hη (yP b)) (fun c => lift η hη (wP c))
    ?_ ?_ ?_ F5 F3 ?_
  · intro b b'
    exact (projRoots (K := F)).preimage_y_comm η hker hη _ _ ⟨b, map_lift η hη _⟩
      ⟨b', map_lift η hη _⟩
  · intro c c'
    exact (projRoots (K := F)).preimage_w_comm η hker hη _ _ ⟨c, map_lift η hη _⟩
      ⟨c', map_lift η hη _⟩
  · intro b c
    exact (commutatorElement_eq_one_iff_mul_comm.mp (F2 c b)).symm
  · intro v hv
    obtain ⟨b, c, hvbc⟩ := hv
    have hz : η ((lift η hη (yP b) * lift η hη (wP c))⁻¹ * v) = 1 := by
      rw [map_mul, map_inv, map_mul, map_lift, map_lift, hvbc]
      exact inv_mul_cancel _
    exact ⟨b, c, _, fun g => (Subgroup.mem_center_iff.mp (hker _ hz) g), hsq' _ hz, by group⟩

theorem coverElem_L3 [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    CoverElem (projectiveSL 3 F) (V1 : Subgroup (projectiveSL 3 F)) ∧
      CoverElem (projectiveSL 3 F) (V2 : Subgroup (projectiveSL 3 F)) := by
  by_cases hn2 : n = 2
  · subst hn2
    have hk : Nat.card F = 4 := by rw [hF]; norm_num
    exact ⟨coverElem_four_V1 hk, coverElem_four_V2 hk⟩
  · have hn3 : 3 ≤ n := by omega
    exact ⟨coverElem_large hn3 hF _ isElemAbelian_V1, coverElem_large hn3 hF _ isElemAbelian_V2⟩

end L3

end CFSG.QuasithinUnique.Fin257
