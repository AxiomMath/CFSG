module

public import CFSG.ClassicalGroups.Orthogonal.SiegelGroupPencil
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4FamilyConj
public import CFSG.CGT.T75E.RootLinMat
public import CFSG.CGT.Timmesfeld75.ListWCLinPSL
public import CFSG.HardMathSupport.Kantor79.LongRootElementClass
public import CFSG.HardMathSupport.Kantor79.OverlappingLongRoot
public import CFSG.HardMathSupport.Kantor79.DisjointLongRoot
public import CFSG.GroupTheory.InvariantSubgroup
import CFSG.Quasithin.Background.G1Module

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelSL

open CFSG.ClassicalGroups.Orthogonal.SiegelRT1 CFSG.HardMathSupport.Kantor79 CFSG.CGT.Timmesfeld75
open CFSG.CGT.T75E QuadraticMap Module Matrix
open scoped MatrixGroups

section Orth

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem commute_of_inf_ne_bot [CharP K 2] [FiniteDimensional K V] {Qf : QuadraticForm K V}
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s')
    (h : movedSpace s ⊓ movedSpace s' ≠ ⊥) : s * s' = s' * s := by
  have hQ := nondegenerate_polarBilin hnd
  obtain ⟨a, b, ha, hb, hab, hli, hmem, hne⟩ :=
    (isLongRootElement_iff_exists_mem_longRootGroup hQ).mp hs
  obtain ⟨a', b', ha', hb', hab', hli', hmem', hne'⟩ :=
    (isLongRootElement_iff_exists_mem_longRootGroup hQ).mp hs'
  have h1 := (mem_longRootGroup_isLongRootElement hnd hli hmem hne).2
  have h2 := (mem_longRootGroup_isLongRootElement hnd hli' hmem' hne').2
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
  refine longRootGroup_comm_of_common hQ ha hb hab ha' hb' hab'
    (hs.qf_eq_zero_of_mem_movedSpace hu1) hu0 ?_ ?_ hmem hmem'
  · rwa [h1] at hu1
  · rwa [h2] at hu2

theorem commute_of_orthogonal [CharP K 2] [FiniteDimensional K V] {Qf : QuadraticForm K V}
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s')
    (h : ∀ x ∈ movedSpace s, ∀ y ∈ movedSpace s', polar Qf x y = 0) : s * s' = s' * s := by
  have hQ := nondegenerate_polarBilin hnd
  obtain ⟨a, b, ha, hb, hab, hli, hmem, hne⟩ :=
    (isLongRootElement_iff_exists_mem_longRootGroup hQ).mp hs
  obtain ⟨a', b', ha', hb', hab', hli', hmem', hne'⟩ :=
    (isLongRootElement_iff_exists_mem_longRootGroup hQ).mp hs'
  have h1 := (mem_longRootGroup_isLongRootElement hnd hli hmem hne).2
  have h2 := (mem_longRootGroup_isLongRootElement hnd hli' hmem' hne').2
  rw [h1, h2] at h
  exact longRootGroup_comm_of_orthogonal ha hb hab ha' hb' hab' h hmem hmem'

theorem commutatorSpace_range_le {L : Type*} [Group L] (ψ : L →* (V ≃ₗ[K] V)) {S : Set L}
    (hS : Subgroup.closure S = ⊤) {U : Submodule K V} (hU : ∀ s ∈ S, movedSpace (ψ s) ≤ U) :
    commutatorSpace ψ.range ≤ U := by
  let H : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {g | ∀ v, g v - v ∈ U}
      one_mem' := fun v => by simp
      mul_mem' := fun {g h} hg hh v => by
        have e : (g * h) v - v = (g (h v) - h v) + (h v - v) := by
          rw [LinearEquiv.mul_apply]
          abel
        rw [e]
        exact U.add_mem (hg _) (hh v)
      inv_mem' := fun {g} hg v => by
        have h1 : g (g⁻¹ v) = v := by simp
        have e : g⁻¹ v - v = -(g (g⁻¹ v) - g⁻¹ v) := by
          rw [h1]
          abel
        rw [e]
        exact U.neg_mem (hg _) }
  have hcl : Subgroup.closure S ≤ H.comap ψ := by
    rw [Subgroup.closure_le]
    intro s hs v
    exact hU s hs (sub_mem_movedSpace (ψ s) v)
  rw [hS] at hcl
  rw [commutatorSpace, Submodule.span_le]
  rintro w ⟨h, ⟨g, rfl⟩, v, rfl⟩
  exact hcl (Subgroup.mem_top g) v

private theorem exists_independent_of_ne_zero {m : ℕ} (hm : 2 ≤ m) {x : Fin m → K}
    (hx : x ≠ 0) : ∃ z : Fin m → K, ∀ s t : K, s • x + t • z = 0 → s = 0 ∧ t = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := by simpa using hi
  obtain ⟨j, hj⟩ : ∃ j : Fin m, j ≠ i := by
    by_cases h0 : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
  refine ⟨Pi.single j 1, fun s t hst => ?_⟩
  have h1 := congrFun hst i
  have h2 := congrFun hst j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2
  rw [Pi.single_eq_of_ne hj.symm, mul_zero, add_zero] at h1
  rw [Pi.single_eq_same, mul_one] at h2
  have hs : s = 0 := (mul_eq_zero.mp h1).resolve_right hi'
  rw [hs, zero_mul, zero_add] at h2
  exact ⟨hs, h2⟩

private theorem map_add_smul_self [CharP K 2] {m : ℕ} (hm : 2 ≤ m)
    {F : (Fin m → K) → V} (h0 : F 0 = 0)
    (hadd : ∀ x y : Fin m → K, LinearIndependent K ![x, y] → F (x + y) = F x + F y)
    {x : Fin m → K} (hx : x ≠ 0) {μ : K} (hμ0 : μ ≠ 0) :
    F (x + μ • x) = F x + F (μ • x) := by
  by_cases hμ1 : μ = 1
  · subst hμ1
    rw [one_smul, vec_add_self', h0, ← two_smul K (F x), CharTwo.two_eq_zero, zero_smul]
  obtain ⟨z, hz⟩ := exists_independent_of_ne_zero hm hx
  have hA : LinearIndependent K ![x + μ • x, z] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h' := (show (s * (1 + μ)) • x + t • z = s • (x + μ • x) + t • z by module).trans h
    obtain ⟨h1, h2⟩ := hz _ _ h'
    refine ⟨(mul_eq_zero.mp h1).resolve_right fun h3 => hμ1 ?_, h2⟩
    have h4 := eq_neg_of_add_eq_zero_right h3
    rwa [CharTwo.neg_eq] at h4
  have hB : LinearIndependent K ![x, μ • x + z] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h' := (show (s + t * μ) • x + t • z = s • x + t • (μ • x + z) by module).trans h
    obtain ⟨h1, h2⟩ := hz _ _ h'
    refine ⟨?_, h2⟩
    rwa [h2, zero_mul, add_zero] at h1
  have hC : LinearIndependent K ![μ • x, z] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h' := (show (s * μ) • x + t • z = s • (μ • x) + t • z by module).trans h
    obtain ⟨h1, h2⟩ := hz _ _ h'
    exact ⟨(mul_eq_zero.mp h1).resolve_right hμ0, h2⟩
  have e1 := hadd _ _ hA
  have e2 := hadd _ _ hB
  have e3 := hadd _ _ hC
  rw [add_assoc] at e1
  rw [e3] at e2
  have e4 := e1.symm.trans e2
  rw [← add_assoc] at e4
  exact add_right_cancel e4

theorem map_add_of_linearIndependent [CharP K 2] {m : ℕ} (hm : 2 ≤ m)
    {F : (Fin m → K) → V} (h0 : F 0 = 0)
    (hadd : ∀ x y : Fin m → K, LinearIndependent K ![x, y] → F (x + y) = F x + F y)
    (x y : Fin m → K) : F (x + y) = F x + F y := by
  by_cases hx0 : x = 0
  · rw [hx0, zero_add, h0, zero_add]
  by_cases hy0 : y = 0
  · rw [hy0, add_zero, h0, add_zero]
  by_cases hli : LinearIndependent K ![x, y]
  · exact hadd x y hli
  rw [LinearIndependent.pair_iff] at hli
  push Not at hli
  obtain ⟨s, t, hst, hne⟩ := hli
  have ht : t ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hst
    exact hne ((smul_eq_zero.mp hst).resolve_right hx0) rfl
  have hy : y = (-(t⁻¹ * s)) • x := by
    calc y = t⁻¹ • (t • y) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = t⁻¹ • (-(s • x)) := by rw [eq_neg_of_add_eq_zero_right hst]
      _ = (-(t⁻¹ * s)) • x := by module
  have hμ0 : -(t⁻¹ * s) ≠ 0 := fun h => hy0 (by rw [hy, h, zero_smul])
  rw [hy]
  exact map_add_smul_self hm h0 hadd hx0 hμ0

end Orth

section SL

variable {K : Type} [Field K] {m : ℕ}

theorem swap_mulVec [CharP K 2] {c d α β : Fin m → K} (hαd : α ⬝ᵥ d = 0) (hαc : α ⬝ᵥ c = 1)
    (hβc : β ⬝ᵥ c = 0) (hβd : β ⬝ᵥ d = 1) :
    ((tvSL d α hαd : SL(m, K)) : Matrix (Fin m) (Fin m) K) *ᵥ c = c + d ∧
      ((tvSL d α hαd * tvSL c β hβc * tvSL d α hαd : SL(m, K)) :
        Matrix (Fin m) (Fin m) K) *ᵥ c = d := by
  have h1 : ((tvSL d α hαd : SL(m, K)) : Matrix (Fin m) (Fin m) K) *ᵥ c = c + d := by
    rw [coe_tvSL, one_add_vecMulVec_mulVec, hαc, one_smul]
  have h2 : ((tvSL c β hβc : SL(m, K)) : Matrix (Fin m) (Fin m) K) *ᵥ (c + d) = d := by
    rw [coe_tvSL, one_add_vecMulVec_mulVec, dotProduct_add, hβc, hβd, zero_add, one_smul,
      add_comm c d, add_assoc, vec_add_self', add_zero]
  have h3 : ((tvSL d α hαd : SL(m, K)) : Matrix (Fin m) (Fin m) K) *ᵥ d = d := by
    rw [coe_tvSL, one_add_vecMulVec_mulVec, hαd, zero_smul, add_zero]
  refine ⟨h1, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2, h3]

theorem map_conjSubgroup_eq {L : Type*} [Group L] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : L →* (V ≃ₗ[K] V)) (T : Subgroup L) (g : L) :
    (CFSG.CGT.Timmesfeld75.conjSubgroup g T).map ρ =
      CFSG.ClassicalGroups.Orthogonal.SiegelRT1.conjSubgroup (ρ g) (T.map ρ) :=
  (CFSG.GroupTheory.map_conjSubgroup ρ T g).symm

end SL

variable {K : Type} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {m : ℕ}

structure SLSetting (Qf : QuadraticForm K V) (ρ : SL(m, K) →* (V ≃ₗ[K] V)) : Prop where
  three_le : 3 ≤ m
  nondeg : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0
  iso : ∀ g v, Qf (ρ g v) = Qf v
  siegel : ∀ (c a : Fin m → K) (h : a ⬝ᵥ c = 0), c ≠ 0 → a ≠ 0 →
    IsLongRootElement Qf (ρ (tvSL c a h))

omit [FiniteDimensional K V] in
theorem slSetting_of_contract [Finite K] (hm : 3 ≤ m) (Qf : QuadraticForm K V)
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : SL(m, K) →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (hS₀ : ∃ t₀ : SL(m, K), IsTransvection t₀ ∧
      finrank K (movedSpace (ρ t₀)) = 2 ∧ ∀ w ∈ movedSpace (ρ t₀), Qf w = 0) :
    SLSetting Qf ρ := by
  obtain ⟨t₀, ht₀, hfin, hsing⟩ := hS₀
  have hS : IsLongRootElement Qf (ρ t₀) := (isLongRootElement_iff hnd).2 ⟨hρQ _, hfin, hsing⟩
  refine ⟨hm, hnd, hρQ, fun c a h hc ha => ?_⟩
  obtain ⟨g, hg⟩ := exists_conj_of_isTransvection ht₀
    (isTransvection_of_coe (x := tvSL c a h) hc ha h (coe_tvSL h))
  have e : ρ (tvSL c a h) = ρ g * ρ t₀ * (ρ g)⁻¹ := by
    rw [← hg, map_mul, map_mul, map_inv]
  rw [e]
  exact IsLongRootElement.conj (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hρQ g)) hS

variable {Qf : QuadraticForm K V} {ρ : SL(m, K) →* (V ≃ₗ[K] V)}

omit [FiniteDimensional K V] in
theorem SLSetting.comp_invT (hs : SLSetting Qf ρ) : SLSetting Qf (ρ.comp invT) := by
  refine ⟨hs.three_le, hs.nondeg, fun g v => hs.iso _ v, fun c a h hc ha => ?_⟩
  have e : (invT (tvSL c a h) : SL(m, K)) = tvSL a c (by rw [dotProduct_comm]; exact h) :=
    Subtype.ext (by rw [coe_invT_tvSL, coe_tvSL])
  rw [MonoidHom.comp_apply, e]
  exact hs.siegel a c _ ha hc

omit [CharP K 2] [FiniteDimensional K V] in
theorem range_comp_invT (ρ : SL(m, K) →* (V ≃ₗ[K] V)) : (ρ.comp invT).range = ρ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr invT_surjective, ← MonoidHom.range_eq_map]

omit [CharP K 2] [FiniteDimensional K V] in
private theorem SLSetting.isLongRootElement_of_mem_center (hs : SLSetting Qf ρ)
    {c : Fin m → K} {x : SL(m, K)} (hx : x ∈ tvCenterSL c) (hx1 : x ≠ 1) :
    IsLongRootElement Qf (ρ x) := by
  obtain ⟨a, ha, hxa⟩ := hx
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx1 (Subtype.ext (by
      rw [hxa, zero_vecMulVec, add_zero, Matrix.SpecialLinearGroup.coe_one]))
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx1 (Subtype.ext (by
      rw [hxa, vecMulVec_zero, add_zero, Matrix.SpecialLinearGroup.coe_one]))
  rw [show x = tvSL c a ha from Subtype.ext hxa]
  exact hs.siegel c a ha hc ha0

omit [CharP K 2] [FiniteDimensional K V] in
private theorem SLSetting.isLongRootElement_of_mem_axis (hs : SLSetting Qf ρ)
    {α : Fin m → K} {x : SL(m, K)} (hx : x ∈ tvAxisSL α) (hx1 : x ≠ 1) :
    IsLongRootElement Qf (ρ x) := by
  obtain ⟨v, hv, hxv⟩ := hx
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hx1 (Subtype.ext (by
      rw [hxv, zero_vecMulVec, add_zero, Matrix.SpecialLinearGroup.coe_one]))
  have hα : α ≠ 0 := by
    rintro rfl
    exact hx1 (Subtype.ext (by
      rw [hxv, vecMulVec_zero, add_zero, Matrix.SpecialLinearGroup.coe_one]))
  rw [show x = tvSL v α hv from Subtype.ext hxv]
  exact hs.siegel v α hv hv0 hα

omit [CharP K 2] [FiniteDimensional K V] in
theorem SLSetting.isSiegelGroup_center (hs : SLSetting Qf ρ) (c : Fin m → K) :
    IsSiegelGroup Qf ((tvCenterSL c).map ρ) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, tvCenterSL_comm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩ hρx
    exact hs.isLongRootElement_of_mem_center hx fun h => hρx (by rw [h, map_one])

omit [CharP K 2] [FiniteDimensional K V] in
theorem SLSetting.isSiegelGroup_axis (hs : SLSetting Qf ρ) (α : Fin m → K) :
    IsSiegelGroup Qf ((tvAxisSL α).map ρ) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, tvAxisSL_comm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩ hρx
    exact hs.isLongRootElement_of_mem_axis hx fun h => hρx (by rw [h, map_one])

omit [FiniteDimensional K V] in
theorem SLSetting.injOn_center (hs : SLSetting Qf ρ) (c : Fin m → K) :
    ∀ x ∈ tvCenterSL c, ∀ y ∈ tvCenterSL c, ρ x = ρ y → x = y := by
  intro x hx y hy hxy
  by_contra hne
  have hz1 : x * y⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  have hz := hs.isLongRootElement_of_mem_center (mul_mem hx (inv_mem hy)) hz1
  rw [map_mul, map_inv, hxy, mul_inv_cancel] at hz
  exact not_isLongRootElement_one hs.nondeg hz

omit [FiniteDimensional K V] in
theorem SLSetting.injOn_axis (hs : SLSetting Qf ρ) (α : Fin m → K) :
    ∀ x ∈ tvAxisSL α, ∀ y ∈ tvAxisSL α, ρ x = ρ y → x = y := by
  intro x hx y hy hxy
  by_contra hne
  have hz1 : x * y⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  have hz := hs.isLongRootElement_of_mem_axis (mul_mem hx (inv_mem hy)) hz1
  rw [map_mul, map_inv, hxy, mul_inv_cancel] at hz
  exact not_isLongRootElement_one hs.nondeg hz

omit [FiniteDimensional K V] in
theorem SLSetting.card_map_center [Finite K] (hs : SLSetting Qf ρ) {c : Fin m → K}
    (hc : c ≠ 0) : Nat.card ((tvCenterSL c).map ρ) = Nat.card K ^ (m - 1) := by
  rw [card_map_of_injOn ρ (hs.injOn_center c), card_tvCenterSL hc]

omit [FiniteDimensional K V] in
theorem SLSetting.card_map_axis [Finite K] (hs : SLSetting Qf ρ) {α : Fin m → K}
    (hα : α ≠ 0) : Nat.card ((tvAxisSL α).map ρ) = Nat.card K ^ (m - 1) := by
  rw [card_map_of_injOn ρ (hs.injOn_axis α), card_tvAxisSL hα]

omit [CharP K 2] [FiniteDimensional K V] in
theorem map_center_mulVec (ρ : SL(m, K) →* (V ≃ₗ[K] V)) (g : SL(m, K)) (c : Fin m → K) :
    (tvCenterSL ((g : Matrix (Fin m) (Fin m) K) *ᵥ c)).map ρ =
      CFSG.ClassicalGroups.Orthogonal.SiegelRT1.conjSubgroup (ρ g) ((tvCenterSL c).map ρ) := by
  rw [← conjSubgroup_tvCenterSL g c]
  exact map_conjSubgroup_eq ρ _ g

omit [CharP K 2] [FiniteDimensional K V] in
theorem map_center_smul (ρ : SL(m, K) →* (V ≃ₗ[K] V)) {c : Fin m → K} {μ : K} (hμ : μ ≠ 0) :
    (tvCenterSL (μ • c)).map ρ = (tvCenterSL c).map ρ := by
  rw [tvCenterSL_smul hμ]

omit [FiniteDimensional K V] in
theorem axisInf_map_center_mulVec (ρ : SL(m, K) →* (V ≃ₗ[K] V)) (g : SL(m, K))
    (c : Fin m → K) :
    axisInf ((tvCenterSL ((g : Matrix (Fin m) (Fin m) K) *ᵥ c)).map ρ) =
      (axisInf ((tvCenterSL c).map ρ)).map ((ρ g : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  rw [map_center_mulVec, axisInf_conjSubgroup]

omit [FiniteDimensional K V] in
theorem commutatorSpace_map_center_mulVec (ρ : SL(m, K) →* (V ≃ₗ[K] V)) (g : SL(m, K))
    (c : Fin m → K) :
    commutatorSpace ((tvCenterSL ((g : Matrix (Fin m) (Fin m) K) *ᵥ c)).map ρ) =
      (commutatorSpace ((tvCenterSL c).map ρ)).map ((ρ g : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  rw [map_center_mulVec, commutatorSpace_conjSubgroup]

omit [FiniteDimensional K V] in
theorem isStar_map_center_mulVec_iff (ρ : SL(m, K) →* (V ≃ₗ[K] V)) (g : SL(m, K))
    (c : Fin m → K) :
    IsStar ((tvCenterSL ((g : Matrix (Fin m) (Fin m) K) *ᵥ c)).map ρ) ↔
      IsStar ((tvCenterSL c).map ρ) := by
  rw [map_center_mulVec]
  unfold IsStar
  rw [axes_conjSubgroup, exists_le_map_iff]

omit [FiniteDimensional K V] in
theorem isStar_map_center_iff (ρ : SL(m, K) →* (V ≃ₗ[K] V)) (hm : 2 ≤ m) {c d : Fin m → K}
    (hc : c ≠ 0) (hd : d ≠ 0) :
    IsStar ((tvCenterSL c).map ρ) ↔ IsStar ((tvCenterSL d).map ρ) := by
  have z : Fin m := ⟨0, by omega⟩
  obtain ⟨g₁, hg₁⟩ := CFSG.Quasithin.G1.exists_smul_single_eq hm z hc
  obtain ⟨g₂, hg₂⟩ := CFSG.Quasithin.G1.exists_smul_single_eq hm z hd
  rw [CFSG.Quasithin.G1.smul_eq_mulVec'] at hg₁ hg₂
  have hd' : ((g₂ * g₁⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) *ᵥ c = d := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← hg₁, inv_mulVec_mulVec',
      hg₂]
  rw [← hd']
  exact (isStar_map_center_mulVec_iff ρ (g₂ * g₁⁻¹) c).symm

omit [FiniteDimensional K V] in
theorem map_comp_invT_center (ρ : SL(m, K) →* (V ≃ₗ[K] V)) (α : Fin m → K) :
    (tvCenterSL α).map (ρ.comp invT) = (tvAxisSL α).map ρ := by
  rw [← Subgroup.map_map, map_invT_tvCenterSL]

theorem SLSetting.not_commute_of_dot (hs : SLSetting Qf ρ) {c d β γ : Fin m → K}
    (hβc : β ⬝ᵥ c = 0) (hγd : γ ⬝ᵥ d = 0) (hγc : γ ⬝ᵥ c = 0) (hβd : β ⬝ᵥ d ≠ 0) (hc : c ≠ 0)
    (hγ : γ ≠ 0) :
    ρ (tvSL c β hβc) * ρ (tvSL d γ hγd) ≠ ρ (tvSL d γ hγd) * ρ (tvSL c β hβc) ∧
      movedSpace (ρ (tvSL c β hβc)) ⊓ movedSpace (ρ (tvSL d γ hγd)) = ⊥ ∧
      ¬ ∀ x ∈ movedSpace (ρ (tvSL c β hβc)), ∀ y ∈ movedSpace (ρ (tvSL d γ hγd)),
        polar Qf x y = 0 := by
  have hd : d ≠ 0 := by
    rintro rfl
    exact hβd (dotProduct_zero β)
  have hβ : β ≠ 0 := by
    rintro rfl
    exact hβd (zero_dotProduct d)
  have h₁ : IsLongRootElement Qf (ρ (tvSL c β hβc)) := hs.siegel c β hβc hc hβ
  have h₂ : IsLongRootElement Qf (ρ (tvSL d γ hγd)) := hs.siegel d γ hγd hd hγ
  have hncomm : ρ (tvSL c β hβc) * ρ (tvSL d γ hγd) ≠ ρ (tvSL d γ hγd) * ρ (tvSL c β hβc) := by
    intro hcomm
    have h₃ : IsLongRootElement Qf (ρ ((tvSL d γ hγd * tvSL c β hβc) ^ 2)) := by
      rw [tvSL_pair_sq hγd hγc hβc]
      exact hs.siegel c _ _ hc (smul_ne_zero hβd hγ)
    have h₄ : (ρ (tvSL d γ hγd) * ρ (tvSL c β hβc)) * (ρ (tvSL d γ hγd) * ρ (tvSL c β hβc)) =
        1 := by
      calc _ = ρ (tvSL d γ hγd) * (ρ (tvSL c β hβc) * ρ (tvSL d γ hγd)) * ρ (tvSL c β hβc) := by
            group
        _ = ρ (tvSL d γ hγd) * (ρ (tvSL d γ hγd) * ρ (tvSL c β hβc)) * ρ (tvSL c β hβc) := by
            rw [hcomm]
        _ = (ρ (tvSL d γ hγd) * ρ (tvSL d γ hγd)) * (ρ (tvSL c β hβc) * ρ (tvSL c β hβc)) := by
            group
        _ = 1 := by rw [h₂.mul_self, h₁.mul_self, mul_one]
    rw [map_pow, pow_two, map_mul, h₄] at h₃
    exact not_isLongRootElement_one hs.nondeg h₃
  refine ⟨hncomm, ?_, fun h => hncomm (commute_of_orthogonal hs.nondeg h₁ h₂ h)⟩
  by_contra h
  exact hncomm (commute_of_inf_ne_bot hs.nondeg h₁ h₂ h)

end CFSG.ClassicalGroups.Orthogonal.SiegelSL
