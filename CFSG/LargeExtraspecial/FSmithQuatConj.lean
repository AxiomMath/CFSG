module

public import CFSG.LargeExtraspecial.FSmithQuat
public import CFSG.LargeExtraspecial.DWTransConj
public import CFSG.LargeExtraspecial.S12Cent
public import CFSG.LargeExtraspecial.AS35LMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

variable {G : Type*} [Group G] [Finite G]

namespace NormalQuat

variable {S : Setting G} {P : Subgroup G}

private theorem exists_inner_sq_of_card {A B : Setting G} {P' : Subgroup G}
    (hP' : NormalQuat A P') {R : Subgroup G} (hRM : R ≤ A.M) (hRQ : R ≤ B.QG)
    (hw : B.width = A.width) (hcard : Nat.card R = 2 ^ (2 * A.width)) (hnA : 3 ≤ A.width) :
    ∃ c ∈ R, InnerOn (S := A) P' c ∧ c * c = B.z := by
  classical
  have hRsub : Nat.card (R.subgroupOf A.M) = 2 ^ (2 * A.width) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv, hcard]
  have hinner := hP'.card_le_two_mul_card_innerPart (R.subgroupOf A.M) hRsub
  have h1 : 1 ≤ 2 * A.width := by have := hnA; omega
  have hsplit : 2 ^ (2 * A.width) = 2 * 2 ^ (2 * A.width - 1) := by
    conv_lhs => rw [show 2 * A.width = (2 * A.width - 1) + 1 from (Nat.sub_add_cancel h1).symm,
      pow_succ]
    rw [mul_comm]
  rw [hRsub, hsplit] at hinner
  have hge : 2 ^ (2 * A.width - 1) ≤ Nat.card (hP'.innerPart (R.subgroupOf A.M)) :=
    Nat.le_of_mul_le_mul_left hinner (by norm_num)
  set R₀ : Subgroup G := (hP'.innerPart (R.subgroupOf A.M)).map A.M.subtype with hR₀
  have hR₀Q : R₀ ≤ B.QG := by
    rintro - ⟨x, hx, rfl⟩
    exact hRQ (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1)
  have hcardR₀ : Nat.card R₀ = Nat.card (hP'.innerPart (R.subgroupOf A.M)) :=
    Subgroup.card_map_of_injective A.M.subtype_injective
  have hlt : 2 ^ (B.width + 1) < Nat.card R₀ := by
    rw [hcardR₀, hw]
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega)) hge
  obtain ⟨c, hcR₀, hc⟩ := B.exists_sq_eq_z_of_lt_card hR₀Q hlt
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hcR₀
  refine ⟨(x : G), Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1,
    hP'.innerOn_iff_ρWhom_eq_one.mpr (Subgroup.mem_inf.mp hx).2, hc⟩

theorem conj_commute_z (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ : g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) :
    ∀ p' ∈ conjSub P g, p' * S.z = S.z * p' := by
  classical
  have hPT : NormalQuat (S.conjBy g) (conjSub P g) := hP.conj g
  have he1 : g * S.z * g⁻¹ ≠ 1 := by
    intro h
    have hz : S.z = 1 := by
      calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    exact S.z_ne_one hz
  have hRM : centralizer ({g * S.z * g⁻¹} : Set G) ⊓ S.QG ≤ (S.conjBy g).M := by
    intro x hx
    rw [show (S.conjBy g).M = centralizer ({(S.conjBy g).z} : Set G) from rfl, Setting.conjBy_z]
    exact (Subgroup.mem_inf.mp hx).1
  have hcard : Nat.card ↥(centralizer ({g * S.z * g⁻¹} : Set G) ⊓ S.QG) =
      2 ^ (2 * S.width) := by
    have h := S.two_mul_card_centralizer_inf_QG heQ he1 hene
    rw [S.card_QG_eq_card_Q, S.card_Q_eq, pow_add, pow_one] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hcard' : Nat.card ↥(centralizer ({g * S.z * g⁻¹} : Set G) ⊓ S.QG) =
      2 ^ (2 * (S.conjBy g).width) := by
    rw [S.width_conjBy]; exact hcard
  obtain ⟨c, hcR, hcinner, hcsq⟩ :=
    exists_inner_sq_of_card (A := S.conjBy g) (B := S) hPT hRM inf_le_right
      (S.width_conjBy g).symm hcard' (by rw [S.width_conjBy]; exact hn)
  have hcM : c ∈ (S.conjBy g).M := hRM hcR
  intro p' hp'
  have h := hPT.conj_mul_self_eq_of_innerOn hcM hcinner hp'
  rw [hcsq] at h
  calc p' * S.z = (S.z * p' * S.z⁻¹) * S.z := by rw [h]
    _ = S.z * p' := by rw [mul_assoc, inv_mul_cancel, mul_one]

theorem commute_conj_z (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ : g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) :
    ∀ p ∈ P, (g * S.z * g⁻¹) * p = p * (g * S.z * g⁻¹) := by
  classical
  have hzQe : S.z ∈ (S.conjBy g).QG :=
    S.z_mem_Qa_of_mem_QG (t := g * S.z * g⁻¹) rfl heQ hene
  have hRM : centralizer ({S.z} : Set G) ⊓ (S.conjBy g).QG ≤ S.M := fun x hx =>
    (Subgroup.mem_inf.mp hx).1
  have hcard : Nat.card ↥(centralizer ({S.z} : Set G) ⊓ (S.conjBy g).QG) =
      2 ^ (2 * S.width) := by
    have h := (S.conjBy g).two_mul_card_centralizer_inf_QG hzQe S.z_ne_one (by
      rw [Setting.conjBy_z]; exact hene.symm)
    rw [(S.conjBy g).card_QG_eq_card_Q, (S.conjBy g).card_Q_eq, Setting.width_conjBy S g,
      pow_add, pow_one] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  obtain ⟨c, hcR, hcinner, hcsq⟩ :=
    exists_inner_sq_of_card (A := S) (B := S.conjBy g) hP hRM inf_le_right
      (S.width_conjBy g) hcard hn
  have hcM : c ∈ S.M := hRM hcR
  intro p hp
  have h := hP.conj_mul_self_eq_of_innerOn hcM hcinner hp
  rw [show (S.conjBy g).z = g * S.z * g⁻¹ from rfl] at hcsq
  rw [hcsq] at h
  calc (g * S.z * g⁻¹) * p = ((g * S.z * g⁻¹) * p * (g * S.z * g⁻¹)⁻¹) * (g * S.z * g⁻¹) := by
        group
    _ = p * (g * S.z * g⁻¹) := by rw [h]

theorem conjSub_le_M (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ : g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) :
    conjSub P g ≤ S.M := fun p' hp' =>
  S.mem_M_iff.mpr (hP.conj_commute_z hn heQ hene p' hp')

theorem le_conjBy_M (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ : g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) :
    P ≤ (S.conjBy g).M := by
  intro p hp
  rw [show (S.conjBy g).M = centralizer ({(S.conjBy g).z} : Set G) from rfl, Setting.conjBy_z]
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (hP.commute_conj_z hn heQ hene p hp).symm

theorem conjSub_le_normalizer (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ : g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) :
    conjSub P g ≤ Subgroup.normalizer (P : Set G) := by
  intro m hm
  have hmM : m ∈ S.M := hP.conjSub_le_M hn heQ hene hm
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · intro hp
    exact hP.conj_mem m hmM p hp
  · intro hp
    have h := hP.conj_mem m⁻¹ (S.M.inv_mem hmM) (m * p * m⁻¹) hp
    rwa [show m⁻¹ * (m * p * m⁻¹) * (m⁻¹)⁻¹ = p from by group] at h

theorem le_normalizer_conjSub (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ : g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) :
    P ≤ Subgroup.normalizer (conjSub P g : Set G) := by
  have hPT : NormalQuat (S.conjBy g) (conjSub P g) := hP.conj g
  intro m hm
  have hmM : m ∈ (S.conjBy g).M := hP.le_conjBy_M hn heQ hene hm
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · intro hp
    exact hPT.conj_mem m hmM p hp
  · intro hp
    have h := hPT.conj_mem m⁻¹ ((S.conjBy g).M.inv_mem hmM) (m * p * m⁻¹) hp
    rwa [show m⁻¹ * (m * p * m⁻¹) * (m⁻¹)⁻¹ = p from by group] at h

theorem conjSub_mul_self_eq_one_iff (hP : NormalQuat S P) {g : G} {y : G} (hy : y ∈ conjSub P g) :
    y * y = 1 ↔ y = 1 ∨ y = g * S.z * g⁻¹ := by
  have hPT : NormalQuat (S.conjBy g) (conjSub P g) := hP.conj g
  have h := hPT.mul_self_eq_one_iff hy
  rwa [show (S.conjBy g).z = g * S.z * g⁻¹ from rfl] at h

theorem inf_conjSub_eq_bot (hP : NormalQuat S P) {g : G} (hene : g * S.z * g⁻¹ ≠ S.z) :
    P ⊓ conjSub P g = ⊥ := by
  have hPT : NormalQuat (S.conjBy g) (conjSub P g) := hP.conj g
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  by_contra hy1
  have hbot : P ⊓ conjSub P g ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hy
    exact hy1 hy
  have hz : S.z ∈ P ⊓ conjSub P g :=
    hP.z_mem_of_ne_bot (H := P ⊓ conjSub P g) inf_le_left hbot
  rcases (hP.conjSub_mul_self_eq_one_iff hz.2).mp S.z_mul_z with h | h
  · exact S.z_ne_one h
  · exact hene h.symm

theorem commute_conjSub (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ : g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) :
    ∀ p ∈ P, ∀ q ∈ conjSub P g, p * q = q * p := by
  intro p hp q hq
  have hinf := hP.inf_conjSub_eq_bot (g := g) hene
  have hPn : (P.subgroupOf (P ⊔ conjSub P g)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer (hP.conjSub_le_normalizer hn heQ hene)
  have hQn : ((conjSub P g).subgroupOf (P ⊔ conjSub P g)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
    exact sup_le (hP.le_normalizer_conjSub hn heQ hene) Subgroup.le_normalizer
  have hcomm := Subgroup.commutator_le_inf (P.subgroupOf (P ⊔ conjSub P g))
    ((conjSub P g).subgroupOf (P ⊔ conjSub P g))
  have hinf' : P.subgroupOf (P ⊔ conjSub P g) ⊓ (conjSub P g).subgroupOf (P ⊔ conjSub P g) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    have hx' : (x : G) ∈ P ⊓ conjSub P g := Subgroup.mem_inf.mpr hx
    rw [hinf, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  have hbot : ⁅(conjSub P g).subgroupOf (P ⊔ conjSub P g), P.subgroupOf (P ⊔ conjSub P g)⁆ ≤ ⊥ := by
    refine (Subgroup.commutator_comm _ _).le.trans ?_
    exact hcomm.trans (le_of_eq hinf')
  have h1 : ⁅P, conjSub P g⁆ = ⊥ :=
    commutator_eq_bot_of_sup_subgroupOf_commutator_le_bot P (conjSub P g) hbot
  have hpq : p * q * p⁻¹ * q⁻¹ = 1 := by
    have h := (Subgroup.commutator_le (H₁ := P) (H₂ := conjSub P g) (H₃ := ⊥)).mp h1.le p hp q hq
    rwa [Subgroup.mem_bot, commutatorElement_def] at h
  calc p * q = (p * q * p⁻¹ * q⁻¹) * (q * p) := by group
    _ = q * p := by rw [hpq, one_mul]

theorem cl_conj_mem_perp (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ : g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) :
    S.cl (g * S.z * g⁻¹) ∈ perp S (S.clSub P) ∧ S.cl (g * S.z * g⁻¹) ≠ 0 ∧
      S.q (S.cl (g * S.z * g⁻¹)) = 0 := by
  have he1 : g * S.z * g⁻¹ ≠ 1 := by
    intro h
    have hz : S.z = 1 := by
      calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    exact S.z_ne_one hz
  have hesq : (g * S.z * g⁻¹) * (g * S.z * g⁻¹) = 1 := by
    rw [show g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ from by group,
      S.z_mul_z, mul_one, mul_inv_cancel]
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_perp]
    intro w hw
    obtain ⟨p, hp, hpQ, rfl⟩ := S.mem_clSub_iff.mp hw
    exact (S.polar_cl_eq_zero_iff hpQ heQ).mpr (hP.commute_conj_z hn heQ hene p hp).symm
  · intro h
    rcases (S.cl_eq_zero_iff heQ).mp h with h' | h'
    · exact he1 h'
    · exact hene h'
  · exact (S.q_cl_eq_zero_iff heQ).mpr (by rw [pow_two]; exact hesq)

theorem inf_conjSub_QG_le (hP : NormalQuat S P) {g : G} (heQ : g * S.z * g⁻¹ ∈ S.QG)
    (hene : g * S.z * g⁻¹ ≠ S.z) :
    ∀ y ∈ conjSub P g ⊓ S.QG, y = 1 ∨ y = g * S.z * g⁻¹ := by
  have he1 : g * S.z * g⁻¹ ≠ 1 := by
    intro h
    have hz : S.z = 1 := by
      calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    exact S.z_ne_one hz
  intro y hy
  rw [Subgroup.mem_inf] at hy
  by_cases hy1 : y = 1
  · exact Or.inl hy1
  by_cases hye : y = g * S.z * g⁻¹
  · exact Or.inr hye
  exfalso
  have hPT : NormalQuat (S.conjBy g) (conjSub P g) := hP.conj g
  have hsq : y * y = g * S.z * g⁻¹ := by
    refine hPT.mul_self_eq y hy.1 hy1 ?_
    rwa [show (S.conjBy g).z = g * S.z * g⁻¹ from rfl]
  rcases S.sq_eq_one_or_z hy.2 with h | h
  · rw [pow_two, hsq] at h
    exact he1 h
  · rw [pow_two, hsq] at h
    exact hene h

theorem inf_conjSub_Qa_le (hP : NormalQuat S P) {g : G} (heQ : g * S.z * g⁻¹ ∈ S.QG)
    (hene : g * S.z * g⁻¹ ≠ S.z) : ∀ x ∈ P ⊓ S.Qa g, x = 1 ∨ x = S.z := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  by_cases h1 : x = 1
  · exact Or.inl h1
  by_cases hz : x = S.z
  · exact Or.inr hz
  exfalso
  have hsq : x * x = S.z := hP.mul_self_eq x hx.1 h1 hz
  have hPT := (S.conjBy g).sq_eq_one_or_z hx.2
  rw [pow_two, hsq] at hPT
  rcases hPT with h | h
  · exact S.z_ne_one h
  · exact hene h.symm

theorem ρL_fixes_clSub (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ : g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) {y : G}
    (hy : y ∈ S.L0 g) {p : G} (hp : p ∈ P) :
    S.ρL ⟨y, (Subgroup.mem_inf.mp hy).2⟩ (S.cl p) = S.cl p := by
  have hyM : y ∈ S.M := (Subgroup.mem_inf.mp hy).2
  have hyQa : y ∈ S.Qa g := (Subgroup.mem_inf.mp hy).1
  have hpQ : p ∈ S.QG := hP.le_QG hp
  rw [S.ρL_cl ⟨y, hyM⟩ hpQ]
  have hmem : y * p * y⁻¹ * p⁻¹ ∈ P ⊓ S.Qa g := by
    refine ⟨?_, ?_⟩
    · exact P.mul_mem (hP.conj_mem y hyM p hp) (P.inv_mem hp)
    · have hpM : p ∈ (S.conjBy g).M := hP.le_conjBy_M hn heQ hene hp
      have h1 : p * y⁻¹ * p⁻¹ ∈ S.Qa g :=
        (S.conjBy g).conj_mem_QG hpM ((S.conjBy g).QG.inv_mem hyQa)
      have h2 : y * (p * y⁻¹ * p⁻¹) ∈ S.Qa g := (S.conjBy g).QG.mul_mem hyQa h1
      rwa [show y * (p * y⁻¹ * p⁻¹) = y * p * y⁻¹ * p⁻¹ from by group] at h2
  have hsplit : y * p * y⁻¹ = (y * p * y⁻¹ * p⁻¹) * p := by group
  rcases hP.inf_conjSub_Qa_le heQ hene _ hmem with h | h
  · rw [hsplit, h, one_mul]
  · rw [hsplit, h, S.cl_mul S.z_mem_QG hpQ, S.cl_z, zero_add]

section StepFour

variable {G : Type} [Group G] [Finite G] {S : Setting G} {P : Subgroup G}

private theorem coe_ρ (m : S.M) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = S.ρL m := rfl

private theorem ρL_symm_apply (m : S.M) (v : S.Qt) : (S.ρL m).symm v = S.ρL m⁻¹ v := by
  apply (S.ρL m).injective
  rw [LinearEquiv.apply_symm_apply, S.ρL_apply_apply_inv]

private def fixesGL (V : Submodule (ZMod 2) S.Qt) : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) where
  carrier := {x | ∀ v ∈ V, x v = v}
  mul_mem' := fun {x y} hx hy v hv => by
    rw [LinearEquiv.mul_apply, hy v hv, hx v hv]
  one_mem' := fun v _ => rfl
  inv_mem' := fun {x} hx v hv => by
    rw [← hx v hv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact (hx v hv).symm

private noncomputable def fixesO (V : Submodule (ZMod 2) S.Qt) : Subgroup S.O :=
  (fixesGL V).comap (Subgroup.subtype S.O)

private theorem mem_fixesO {V : Submodule (ZMod 2) S.Qt} {x : S.O} :
    x ∈ fixesO V ↔ ∀ v ∈ V, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := Iff.rfl

private theorem coe_mul_apply (x y : S.O) (v : S.Qt) :
    (((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) v =
      ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply]

private theorem coe_inv_apply (x : S.O) (v : S.Qt) :
    (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) v =
      ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).symm v := by
  rw [Subgroup.coe_inv, LinearEquiv.coe_inv]

theorem ρ_eq_one_of_forall_perp (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ: g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) {m : S.M}
    (hm : ∀ u ∈ perp S (S.clSub P), S.ρL m u = u) : S.ρ m = 1 := by
  classical
  set W := S.clSub P with hW
  set U := perp S W with hU
  have hcompl : IsCompl W U := hP.isCompl_clSub_perp
  have hWinv : IsMbarInvariant S W := hP.isMbarInvariant_clSub
  have hUinv : IsMbarInvariant S U := hWinv.perp
  have hWU : W ⊔ U = ⊤ := hcompl.sup_eq_top
  set Y : Subgroup S.O := S.Mbar ⊓ fixesO U with hY
  have hYle : Y ≤ S.Mbar := by rw [hY]; exact inf_le_left
  have hYnorm : S.Mbar ≤ Subgroup.normalizer (Y : Set S.O) := by
    intro σ hσ
    obtain ⟨m', rfl⟩ := MonoidHom.mem_range.mp hσ
    rw [Subgroup.mem_normalizer_iff]
    intro τ
    constructor
    · intro hτ
      rw [hY, Subgroup.mem_inf] at hτ ⊢
      refine ⟨S.Mbar.mul_mem (S.Mbar.mul_mem ⟨m', rfl⟩ hτ.1) (S.Mbar.inv_mem ⟨m', rfl⟩), ?_⟩
      rw [mem_fixesO] at hτ ⊢
      intro u hu
      rw [coe_mul_apply, coe_mul_apply, coe_inv_apply]
      simp only [coe_ρ]
      rw [ρL_symm_apply, hτ.2 (S.ρL m'⁻¹ u) (hUinv m'⁻¹ u hu), S.ρL_apply_apply_inv]
    · intro hτ
      rw [hY, Subgroup.mem_inf] at hτ ⊢
      refine ⟨?_, ?_⟩
      · have h := S.Mbar.mul_mem (S.Mbar.mul_mem (S.Mbar.inv_mem ⟨m', rfl⟩) hτ.1) ⟨m', rfl⟩
        rwa [show (S.ρ m')⁻¹ * ((S.ρ m') * τ * (S.ρ m')⁻¹) * (S.ρ m') = τ from by group] at h
      · rw [mem_fixesO] at hτ ⊢
        intro u hu
        have h1 : S.ρL m' u ∈ U := hUinv m' u hu
        have h2 := hτ.2 (S.ρL m' u) h1
        rw [coe_mul_apply, coe_mul_apply, coe_inv_apply] at h2
        simp only [coe_ρ] at h2
        rw [ρL_symm_apply, S.ρL_inv_apply_apply] at h2
        exact (S.ρL m').injective h2
  have hcomm : ∀ σ ∈ S.Lbar g, ∀ τ ∈ Y, σ * τ = τ * σ := by
    intro σ hσ τ hτ
    rw [hY, Subgroup.mem_inf] at hτ
    obtain ⟨y, hy, rfl⟩ := S.s12_mem_Lbar.mp hσ
    have hyM : y ∈ S.M := (Subgroup.mem_inf.mp hy).2
    have hσW' : ∀ w ∈ W, ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
      intro w hw
      obtain ⟨p, hp, hpQ, rfl⟩ := S.mem_clSub_iff.mp hw
      exact hP.ρL_fixes_clSub hn heQ hene hy hp
    have hσU : ∀ u ∈ U, ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U := by
      intro u hu
      rw [mem_perp]
      intro w hw
      obtain ⟨p, hp, hpQ, rfl⟩ := S.mem_clSub_iff.mp hw
      have hpol := polar_ρ_apply (S := S) ⟨y, hyM⟩⁻¹ (S.cl p)
        (((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u)
      simp only [coe_ρ] at hpol
      rw [S.ρL_inv_apply_apply] at hpol
      have hw' : S.ρL ⟨y, hyM⟩⁻¹ (S.cl p) = S.cl p :=
        hP.ρL_fixes_clSub hn heQ hene ((S.L0 g).inv_mem hy) hp
      rw [hw'] at hpol
      simp only [coe_ρ]
      rw [← hpol]
      exact mem_perp.mp hu (S.cl p) (S.cl_mem_clSub hp hpQ)
    have hτW : ∀ w ∈ W, ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W := by
      intro w hw
      obtain ⟨m'', rfl⟩ := MonoidHom.mem_range.mp hτ.1
      exact hWinv m'' w hw
    have hτU' : ∀ u ∈ U, ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := mem_fixesO.mp hτ.2
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ W ⊔ U := by rw [hWU]; exact Submodule.mem_top
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
    rw [coe_mul_apply, coe_mul_apply, map_add, map_add, map_add, map_add,
      hσW' _ (hτW w hw), hτU' _ (hσU u hu), hτU' u hu, hσW' w hw]
  have hYle' : Y ≤ S.Mbar ⊓ centralizer (S.Lbar g : Set S.O) := by
    intro τ hτ
    rw [Subgroup.mem_inf] at hτ ⊢
    refine ⟨hτ.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact hcomm l hl τ ⟨hτ.1, hτ.2⟩
  have h2Y : IsPGroup 2 Y := (S.timmesfeld_12_4_2 heQ hene hn).to_le hYle'
  have hYbot : Y = ⊥ := S.eq_bot_of_normalized_L hYle hYnorm h2Y
  have hmem : S.ρ m ∈ Y := by
    rw [hY, Subgroup.mem_inf]
    refine ⟨⟨m, rfl⟩, ?_⟩
    rw [mem_fixesO]
    intro u hu
    exact hm u (by rw [hU, hW] at hu; exact hu)
  rw [hYbot, Subgroup.mem_bot] at hmem
  exact hmem

end StepFour

section StepThree

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {P : Subgroup G}

private theorem conj_ne_one {g : G} (heQ : g * S.z * g⁻¹ ∈ S.QG)
    (hene : g * S.z * g⁻¹ ≠ S.z) : g * S.z * g⁻¹ ≠ 1 := by
  intro h
  have hz : S.z = 1 := by
    calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  exact S.z_ne_one hz

private theorem conj_mul_e_mul_inv (hP : NormalQuat S P) {g r : G} (hr : r ∈ conjSub P g) :
    r * (g * S.z * g⁻¹) * r⁻¹ = g * S.z * g⁻¹ := by
  have hp : g⁻¹ * r * g ∈ P := mem_conjSub.mp hr
  have hzp : (g⁻¹ * r * g) * S.z * (g⁻¹ * r * g)⁻¹ = S.z := by
    rw [S.z_comm (S.QG_le_M (hP.le_QG hp))]
    group
  calc r * (g * S.z * g⁻¹) * r⁻¹
      = g * ((g⁻¹ * r * g) * S.z * (g⁻¹ * r * g)⁻¹) * g⁻¹ := by group
    _ = g * S.z * g⁻¹ := by rw [hzp]

theorem ρL_mem_pointRadical (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ : g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) {r : G}
    (hr : r ∈ conjSub P g) :
    ((S.ρ ⟨r, hP.conjSub_le_M hn heQ hene hr⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈
      pointRadical S.q (S.cl (g * S.z * g⁻¹)) := by
  classical
  set e := g * S.z * g⁻¹ with he
  have hrM : r ∈ S.M := hP.conjSub_le_M hn heQ hene hr
  have hPT : NormalQuat (S.conjBy g) (conjSub P g) := hP.conj g
  have he1 : e ≠ 1 := conj_ne_one heQ hene
  have hre : r * e * r⁻¹ = e := conj_mul_e_mul_inv hP hr
  have ht : ((S.ρ ⟨r, hrM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) = S.cl e := by
    rw [show ((S.ρ ⟨r, hrM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = S.ρL ⟨r, hrM⟩ from rfl,
      S.ρL_cl ⟨r, hrM⟩ heQ, hre]
  rw [mem_pointRadical]
  refine ⟨(S.ρ ⟨r, hrM⟩).2, ht, ?_, ?_⟩
  ·
    intro x hx
    obtain ⟨x₀, hx₀Q, hx₀⟩ := S.exists_cl x
    have hxe : polar S.q (S.cl e) (S.cl x₀) = 0 := by rw [hx₀]; exact hx
    have hcomm : e * x₀ = x₀ * e := (S.polar_cl_eq_zero_iff heQ hx₀Q).mp hxe
    have hx₀M : x₀ ∈ (S.conjBy g).M := by
      rw [show (S.conjBy g).M = centralizer ({(S.conjBy g).z} : Set G) from rfl, Setting.conjBy_z]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
    have hx₀r : x₀ * r * x₀⁻¹ ∈ conjSub P g := hPT.conj_mem x₀ hx₀M r hr
    have hcPg : r * x₀ * r⁻¹ * x₀⁻¹ ∈ conjSub P g := by
      have heq : r * x₀ * r⁻¹ * x₀⁻¹ = r * (x₀ * r * x₀⁻¹)⁻¹ := by group
      rw [heq]
      exact (conjSub P g).mul_mem hr ((conjSub P g).inv_mem hx₀r)
    have hcQ : r * x₀ * r⁻¹ * x₀⁻¹ ∈ S.QG :=
      S.QG.mul_mem (S.conj_mem_QG hrM hx₀Q) (S.QG.inv_mem hx₀Q)
    have hc : r * x₀ * r⁻¹ * x₀⁻¹ = 1 ∨ r * x₀ * r⁻¹ * x₀⁻¹ = e :=
      hP.inf_conjSub_QG_le heQ hene _ ⟨hcPg, hcQ⟩
    have htx : ((S.ρ ⟨r, hrM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x =
        x + S.cl (r * x₀ * r⁻¹ * x₀⁻¹) := by
      rw [← hx₀]
      show S.ρL ⟨r, hrM⟩ (S.cl x₀) = S.cl x₀ + S.cl (r * x₀ * r⁻¹ * x₀⁻¹)
      rw [S.ρL_cl ⟨r, hrM⟩ hx₀Q, add_comm, ← S.cl_mul hcQ hx₀Q]
      congr 1
      show r * x₀ * r⁻¹ = (r * x₀ * r⁻¹ * x₀⁻¹) * x₀
      group
    rw [htx, show x + S.cl (r * x₀ * r⁻¹ * x₀⁻¹) - x = S.cl (r * x₀ * r⁻¹ * x₀⁻¹) from by abel]
    rcases hc with h | h
    · rw [h, S.cl_one]; exact Submodule.zero_mem _
    · rw [h]; exact Submodule.mem_span_singleton_self _
  ·
    intro v
    have h1 : polar S.q (S.cl e) (((S.ρ ⟨r, hrM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        polar S.q (S.cl e) v := by
      have hiso := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ ⟨r, hrM⟩).2
        (S.cl e) v
      rw [ht] at hiso
      exact hiso
    rw [polar_sub_right, h1, sub_self]

theorem exists_eichler_mem_perp (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ: g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) {r : G}
    (hr : r ∈ conjSub P g) :
    ∃ u ∈ perp S (S.clSub P), polar S.q (S.cl (g * S.z * g⁻¹)) u = 0 ∧
      ((S.ρ ⟨r, hP.conjSub_le_M hn heQ hene hr⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        CFSG.ClassicalGroups.Orthogonal.eichler S.q (S.cl (g * S.z * g⁻¹)) u := by
  classical
  set e := g * S.z * g⁻¹ with he
  have hrM : r ∈ S.M := hP.conjSub_le_M hn heQ hene hr
  obtain ⟨hne0, hq0⟩ := (hP.cl_conj_mem_perp hn heQ hene).2
  have hPR := hP.ρL_mem_pointRadical hn heQ hene hr
  obtain ⟨u, hau, heich⟩ :=
    (mem_pointRadical_iff (V := S.Qt) S.q_nondegenerate hne0 hq0).mp hPR
  have hne0' : S.cl e ≠ 0 := hne0
  refine ⟨u, ?_, hau, heich⟩
  rw [mem_perp]
  intro w hw
  obtain ⟨p, hp, hpQ, rfl⟩ := S.mem_clSub_iff.mp hw
  have hfixW : ((S.ρ ⟨r, hrM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl p) = S.cl p := by
    rw [show ((S.ρ ⟨r, hrM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = S.ρL ⟨r, hrM⟩ from rfl,
      S.ρL_cl ⟨r, hrM⟩ hpQ]
    congr 1
    have hcomm : r * p = p * r := (hP.commute_conjSub hn heQ hene p hp r hr).symm
    calc r * p * r⁻¹ = p * r * r⁻¹ := by rw [hcomm]
      _ = p := by group
  have hpe : polar S.q (S.cl p) (S.cl e) = 0 :=
    (S.polar_cl_eq_zero_iff hpQ heQ).mpr (hP.commute_conj_z hn heQ hene p hp).symm
  have hE : CFSG.ClassicalGroups.Orthogonal.eichler S.q (S.cl e) u (S.cl p) =
      S.cl p + polar S.q (S.cl p) u • S.cl e := by
    rw [eichler_apply_zmod2 hq0 hau, hpe]
    simp only [zero_smul, mul_zero, zero_add, add_zero]
    rw [← he]
  have hEw : CFSG.ClassicalGroups.Orthogonal.eichler S.q (S.cl e) u (S.cl p) = S.cl p := by
    rw [← heich]
    exact hfixW
  rw [hEw] at hE
  have hzero : polar S.q (S.cl p) u • S.cl e = 0 := by
    have := hE.symm
    exact (add_eq_left.mp this)
  rcases smul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd h hne0'

private theorem mem_perp_sup {V₁ V₂ : Submodule (ZMod 2) S.Qt} {u : S.Qt} :
    u ∈ perp S (V₁ ⊔ V₂) ↔ u ∈ perp S V₁ ∧ u ∈ perp S V₂ := by
  rw [mem_perp, mem_perp, mem_perp]
  constructor
  · intro h
    exact ⟨fun w hw => h w (Submodule.mem_sup_left hw),
      fun w hw => h w (Submodule.mem_sup_right hw)⟩
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [polar_add_left, h1 a ha, h2 b hb, add_zero]

private theorem card_range_conj (hP : NormalQuat S P) (hn : 3 ≤ S.width) {g : G}
    (heQ : g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) :
    Nat.card ((S.ρ.comp (Subgroup.inclusion (hP.conjSub_le_M hn heQ hene))).range) = 4 := by
  classical
  set φ : ↥(conjSub P g) →* S.O := S.ρ.comp (Subgroup.inclusion (hP.conjSub_le_M hn heQ hene))
  have hcardPg : Nat.card ↥(conjSub P g) = 8 := by
    rw [show conjSub P g = P.map (MulAut.conj g).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hP.card_eq]
  have hePg : g * S.z * g⁻¹ ∈ conjSub P g := conj_mem_conjSub hP.z_mem
  have he_inf : g * S.z * g⁻¹ ∈ conjSub P g ⊓ S.QG := ⟨hePg, heQ⟩
  have hmem_iff : ∀ x : ↥(conjSub P g), φ x = 1 ↔ (x : G) ∈ S.QG := by
    intro x
    show S.ρ (Subgroup.inclusion _ x) = 1 ↔ (x : G) ∈ S.QG
    rw [S.ρ_eq_one_iff]
    rfl
  have hker2 : Nat.card φ.ker = 2 := by
    have hequiv : φ.ker ≃ ↥(conjSub P g ⊓ S.QG) :=
      { toFun := fun x => ⟨(x.1 : G), x.1.2, (hmem_iff x.1).mp x.2⟩
        invFun := fun y => ⟨⟨(y : G), y.2.1⟩, (hmem_iff ⟨(y : G), y.2.1⟩).mpr y.2.2⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun y => by ext; rfl }
    rw [Nat.card_congr hequiv]
    have he1 : g * S.z * g⁻¹ ≠ 1 := conj_ne_one heQ hene
    refine (Nat.card_eq_two_iff' (1 : ↥(conjSub P g ⊓ S.QG))).mpr
      ⟨⟨g * S.z * g⁻¹, he_inf⟩, ?_, ?_⟩
    · intro h
      exact he1 (congrArg (fun y : ↥(conjSub P g ⊓ S.QG) => (y : G)) h)
    · intro y hy
      rcases hP.inf_conjSub_QG_le heQ hene y.1 y.2 with h | h
      · exact absurd (Subtype.ext h) hy
      · exact Subtype.ext h
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hiso : Nat.card (↥(conjSub P g) ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  rw [hcardPg, hker2, hiso] at h
  omega

private theorem card_perp_sup_span (hP : NormalQuat S P) (hw : S.width = 3) {g : G}
    (heQ: g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) :
    Nat.card ↥(perp S (S.clSub P ⊔ ZMod 2 ∙ S.cl (g * S.z * g⁻¹))) = 8 := by
  classical
  obtain ⟨hne0, hq0⟩ := (hP.cl_conj_mem_perp (by omega : 3 ≤ S.width) heQ hene).2
  have hdisj := hP.isCompl_clSub_perp.disjoint
  have haU : S.cl (g * S.z * g⁻¹) ∈ perp S (S.clSub P) :=
    (hP.cl_conj_mem_perp (by omega : 3 ≤ S.width) heQ hene).1
  have ha_notin : S.cl (g * S.z * g⁻¹) ∉ S.clSub P := by
    intro haW
    have hbot : S.cl (g * S.z * g⁻¹) ∈ (⊥ : Submodule (ZMod 2) S.Qt) := by
      have hm : S.cl (g * S.z * g⁻¹) ∈ S.clSub P ⊓ perp S (S.clSub P) := ⟨haW, haU⟩
      rwa [hdisj.eq_bot] at hm
    have h0 : S.cl (g * S.z * g⁻¹) = 0 := by simpa using hbot
    exact hne0 h0
  have hinf : S.clSub P ⊓ (ZMod 2 ∙ S.cl (g * S.z * g⁻¹)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_inf.mp hx).2
    have hc : c = 0 := by
      by_contra hc
      apply ha_notin
      have := (S.clSub P).smul_mem c⁻¹ (Submodule.mem_inf.mp hx).1
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    rw [hc, zero_smul]
  have hsup : finrank (ZMod 2) ↥(S.clSub P ⊔ ZMod 2 ∙ S.cl (g * S.z * g⁻¹)) = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub P)
      (ZMod 2 ∙ S.cl (g * S.z * g⁻¹))
    rw [hinf, finrank_bot, finrank_span_singleton hne0, hP.finrank_clSub] at h
    omega
  rw [S.card_submodule, perp, LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate,
    S.finrank_Qt_eq_two_mul_width, hw, hsup]
  norm_num

theorem exists_ρL_eq_eichler (hP : NormalQuat S P) (hw : S.width = 3) {g : G}
    (heQ: g * S.z * g⁻¹ ∈ S.QG) (hene : g * S.z * g⁻¹ ≠ S.z) {u : S.Qt}
    (hu : u ∈ perp S (S.clSub P)) (hau : polar S.q (S.cl (g * S.z * g⁻¹)) u = 0) :
    ∃ m : S.M, S.ρL m = CFSG.ClassicalGroups.Orthogonal.eichler S.q (S.cl (g * S.z * g⁻¹)) u := by
  classical
  set W := S.clSub P with hW
  set e := g * S.z * g⁻¹ with he
  set a := S.cl e with ha
  have hn : 3 ≤ S.width := by omega
  obtain ⟨hne0, hq0⟩ := (hP.cl_conj_mem_perp hn heQ hene).2
  set C : Submodule (ZMod 2) S.Qt := perp S (W ⊔ ZMod 2 ∙ a) with hC
  have hCmem : ∀ x : ↥C, polar S.q a (x : S.Qt) = 0 := by
    intro x
    have h := (mem_perp_sup (S := S) (V₁ := W) (V₂ := ZMod 2 ∙ a)).mp x.2
    exact mem_perp.mp h.2 a (Submodule.mem_span_singleton_self a)
  have hC8 : Nat.card ↥C = 8 := by
    rw [hC, hW, ha, he]
    exact card_perp_sup_span hP hw heQ hene
  let ψ : Multiplicative ↥C →* (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    { toFun := fun x => CFSG.ClassicalGroups.Orthogonal.eichler S.q a (x.toAdd : S.Qt)
      map_one' := by
        show CFSG.ClassicalGroups.Orthogonal.eichler S.q a (((1 : Multiplicative ↥C).toAdd : ↥C) : S.Qt) = 1
        rw [show (((1 : Multiplicative ↥C).toAdd : ↥C) : S.Qt) = 0 from rfl]
        exact CFSG.ClassicalGroups.Orthogonal.eichler_zero_right S.q a
      map_mul' := fun x y => by
        show CFSG.ClassicalGroups.Orthogonal.eichler S.q a (((x * y).toAdd : ↥C) : S.Qt) =
          CFSG.ClassicalGroups.Orthogonal.eichler S.q a (x.toAdd : S.Qt) *
            CFSG.ClassicalGroups.Orthogonal.eichler S.q a (y.toAdd : S.Qt)
        rw [show (((x * y).toAdd : ↥C) : S.Qt) = ((x.toAdd : ↥C) : S.Qt) + ((y.toAdd : ↥C) : S.Qt)
          from rfl]
        exact (CFSG.ClassicalGroups.Orthogonal.eichler_mul (hCmem x.toAdd) (hCmem y.toAdd)).symm }
  have haC : a ∈ C := by
    rw [hC, mem_perp_sup]
    exact ⟨hW ▸ (hP.cl_conj_mem_perp hn heQ hene).1,
      mem_perp.mpr (fun w hw => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [polar_smul_left, CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero]
        exact smul_zero c)⟩
  have hker_ne : ψ (Multiplicative.ofAdd ⟨a, haC⟩) = 1 := by
    show CFSG.ClassicalGroups.Orthogonal.eichler S.q a (a) = 1
    have h := CFSG.ClassicalGroups.Orthogonal.eichler_add_smul_self (Q := S.q) hq0 0 1
    rw [zero_add, one_smul] at h
    rw [h, CFSG.ClassicalGroups.Orthogonal.eichler_zero_right]
  have hker2 : 2 ≤ Nat.card ↥ψ.ker := by
    have hmem : (Multiplicative.ofAdd (⟨a, haC⟩ : ↥C)) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact hker_ne
    have hne1 : (Multiplicative.ofAdd (⟨a, haC⟩ : ↥C)) ≠ 1 := by
      intro h
      have h' : a = 0 := by
        have := congrArg (fun y : Multiplicative ↥C => (y.toAdd : ↥C)) h
        simpa using congrArg (fun y : ↥C => (y : S.Qt)) this
      exact hne0 h'
    have hnt : Nontrivial ↥ψ.ker :=
      ⟨⟨(Multiplicative.ofAdd (⟨a, haC⟩ : ↥C)), hmem⟩, 1, by
        intro h
        exact hne1 (congrArg (fun y : ↥ψ.ker => (y : Multiplicative ↥C)) h)⟩
    exact Finite.one_lt_card
  have hrange4 : Nat.card ψ.range ≤ 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    have hiso : Nat.card (Multiplicative ↥C ⧸ ψ.ker) = Nat.card ψ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    have hC8' : Nat.card (Multiplicative ↥C) = 8 := by
      rw [← hC8]
      exact Nat.card_congr Multiplicative.toAdd
    rw [hC8', hiso] at h
    have h1 : Nat.card ψ.range * 2 ≤ Nat.card ψ.range * Nat.card ↥ψ.ker :=
      Nat.mul_le_mul_left _ hker2
    rw [← h] at h1
    omega
  let φ : ↥(conjSub P g) →* S.O := S.ρ.comp (Subgroup.inclusion (hP.conjSub_le_M hn heQ hene))
  let φ' : ↥(conjSub P g) →* (S.Qt ≃ₗ[ZMod 2] S.Qt) := (Subgroup.subtype S.O).comp φ
  have hφ' : φ'.range = φ.range.map (Subgroup.subtype S.O) := MonoidHom.range_comp _ _
  have hcardφ : Nat.card φ.range = 4 := by
    rw [show φ = S.ρ.comp (Subgroup.inclusion (hP.conjSub_le_M hn heQ hene)) from rfl]
    exact card_range_conj hP hn heQ hene
  have hcardφ' : Nat.card φ'.range = 4 := by
    rw [hφ', Subgroup.card_map_of_injective Subtype.coe_injective, hcardφ]
  have hle : φ'.range ≤ ψ.range := by
    rintro x ⟨r, rfl⟩
    obtain ⟨u', hu'U, hu'a, hE⟩ := hP.exists_eichler_mem_perp hn heQ hene r.2
    have hu'C : u' ∈ C := by
      rw [hC, hW, ha, mem_perp_sup]
      exact ⟨hu'U, mem_perp.mpr (fun w hw => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [polar_smul_left, hu'a]
        exact smul_zero c)⟩
    refine ⟨Multiplicative.ofAdd ⟨u', hu'C⟩, ?_⟩
    show CFSG.ClassicalGroups.Orthogonal.eichler S.q a u' = φ' r
    rw [show φ' r = ((φ r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) from rfl, ← hE]
    rfl
  have h4 : Nat.card ψ.range = 4 :=
    le_antisymm hrange4 (by rw [← hcardφ']; exact Subgroup.card_le_of_le hle)
  have heq : φ'.range = ψ.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardφ', h4])
  have huC : u ∈ C := by
    rw [hC, hW, ha, mem_perp_sup]
    exact ⟨hu, mem_perp.mpr (fun w hw => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [polar_smul_left, hau]
      exact smul_zero c)⟩
  have hmem : CFSG.ClassicalGroups.Orthogonal.eichler S.q a u ∈ ψ.range :=
    ⟨Multiplicative.ofAdd ⟨u, huC⟩, rfl⟩
  rw [← heq] at hmem
  obtain ⟨r, hr⟩ := hmem
  refine ⟨⟨r.1, hP.conjSub_le_M hn heQ hene r.2⟩, ?_⟩
  rw [← hr]
  rfl

end StepThree

end NormalQuat

end CFSG.LargeExtraspecial.DW
