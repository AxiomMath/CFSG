module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCoverCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigherField

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 0}

variable (θ) in
@[expose] def IsN (B : Matrix (Fin r) (Fin r) K) (m : E) : Prop :=
  ∃ hB : IsHerm h B, θ m = hypProj h r 0 (nElt hB)

variable (θ) in
@[expose] def preN : Subgroup E :=
  ((radN h r).map (hypProj h r 0)).comap θ

theorem mem_preN {m : E} : m ∈ preN θ ↔ ∃ B, IsN θ B m := by
  constructor
  · rintro ⟨_, ⟨B, hB, rfl⟩, he⟩
    exact ⟨B, hB, he.symm⟩
  · rintro ⟨B, hB, he⟩
    exact ⟨_, nElt_mem_radN hB, he.symm⟩

theorem IsN.mem {B : Matrix (Fin r) (Fin r) K} {m : E} (hm : IsN θ B m) : m ∈ preN θ :=
  mem_preN.mpr ⟨B, hm⟩

theorem IsN.congr {B B' : Matrix (Fin r) (Fin r) K} {m : E} (hm : IsN θ B m) (hB : B = B') :
    IsN θ B' m :=
  hB ▸ hm

theorem IsN.mul {B B' : Matrix (Fin r) (Fin r) K} {m m' : E} (hm : IsN θ B m)
    (hm' : IsN θ B' m') : IsN θ (B + B') (m * m') := by
  obtain ⟨hB, he⟩ := hm
  obtain ⟨hB', he'⟩ := hm'
  exact ⟨isHerm_add hB hB', by rw [map_mul, he, he', ← map_mul, nElt_mul]⟩

theorem IsN.inv {B : Matrix (Fin r) (Fin r) K} {m : E} (hm : IsN θ B m) : IsN θ (-B) m⁻¹ := by
  obtain ⟨hB, he⟩ := hm
  exact ⟨isHerm_neg hB, by rw [map_inv, he, ← map_inv, nElt_inv]⟩

theorem IsN.map_eq {B : Matrix (Fin r) (Fin r) K} {m m' : E} (hm : IsN θ B m)
    (hm' : IsN θ B m') : θ m = θ m' := by
  obtain ⟨hB, he⟩ := hm
  obtain ⟨hB', he'⟩ := hm'
  rw [he, he']

theorem isN_zero_iff {m : E} : IsN θ 0 m ↔ θ m = 1 := by
  constructor
  · rintro ⟨hB, he⟩
    rw [he, show nElt hB = 1 from nElt_zero h, map_one]
  · intro he
    exact ⟨isHerm_zero h, by rw [he, nElt_zero, map_one]⟩

theorem exists_isN (hθ : Function.Surjective θ) {B : Matrix (Fin r) (Fin r) K}
    (hB : IsHerm h B) : ∃ m, IsN θ B m := by
  obtain ⟨m, hm⟩ := hθ (hypProj h r 0 (nElt hB))
  exact ⟨m, hB, hm⟩

theorem IsN.eq_of_isN (hr : 1 ≤ r) {B B' : Matrix (Fin r) (Fin r) K} {m : E} (hm : IsN θ B m)
    (hm' : IsN θ B' m) : B = B' := by
  obtain ⟨hB, he⟩ := hm
  obtain ⟨hB', he'⟩ := hm'
  have hinj := hypProj_injective_on h hr (Nat.zero_le 1)
  have : (⟨nElt hB, nElt_mem_hypUnitriangular hB⟩ : hypUnitriangular h r 0) =
      ⟨nElt hB', nElt_mem_hypUnitriangular hB'⟩ :=
    hinj (Subtype.ext (by
      simp only [MonoidHom.subgroupMap_apply_coe]
      rw [← he, ← he']))
  exact eq_of_nElt_eq (hB := hB) (hB' := hB') (congrArg Subtype.val this)

theorem IsN.conj {B : Matrix (Fin r) (Fin r) K} {m g : E} (hm : IsN θ B m) (A : detFixed h r)
    (hg : θ g = hypProj h r 0 (lHom h r A)) :
    IsN θ ((A : GL (Fin r) K) * B * (((A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ)
      (g * m * g⁻¹) := by
  obtain ⟨hB, he⟩ := hm
  exact ⟨isHerm_conj _ hB, by
    rw [map_mul, map_mul, map_inv, hg, he, ← map_inv, ← map_mul, ← map_mul, lHom_mul_nElt]⟩

theorem commutatorElement_mem_center (hC : θ.ker ≤ Subgroup.center E) {m m' : E}
    (hm : m ∈ preN θ) (hm' : m' ∈ preN θ) : ⁅m, m'⁆ ∈ Subgroup.center E := by
  refine hC ?_
  obtain ⟨g, hg, hgm⟩ := hm
  obtain ⟨g', hg', hgm'⟩ := hm'
  rw [MonoidHom.mem_ker, map_commutatorElement, ← hgm, ← hgm', ← map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm_of_mem_radN hg hg'), map_one]

theorem commutatorElement_mul_preN (hC : θ.ker ≤ Subgroup.center E) {m₁ m₂ m' : E}
    (hm₂ : m₂ ∈ preN θ) (hm' : m' ∈ preN θ) :
    ⁅m₁ * m₂, m'⁆ = ⁅m₁, m'⁆ * ⁅m₂, m'⁆ := by
  have hc₂ := commutatorElement_mem_center hC hm₂ hm'
  rw [show ⁅m₁ * m₂, m'⁆ = m₁ * ⁅m₂, m'⁆ * m₁⁻¹ * ⁅m₁, m'⁆ by
      simp only [commutatorElement_def]; group,
    Subgroup.mem_center_iff.mp hc₂ m₁, mul_inv_cancel_right]
  exact (Subgroup.mem_center_iff.mp hc₂ _).symm

theorem commutatorElement_eq_of_map_eq' (hC : θ.ker ≤ Subgroup.center E) {m m₁ m' m'₁ : E}
    (hm : θ m = θ m₁) (hm' : θ m' = θ m'₁) : ⁅m, m'⁆ = ⁅m₁, m'₁⁆ :=
  LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq θ (fun _ hz => hC hz) hm hm'

variable [CharP K 2]

variable (h r) in
@[expose] def leviHom : SpecialLinearGroup (Fin r) K →* hypPSU h r 0 :=
  (hypProj h r 0).comp ((lHom h r).comp (slHom h r))

include θ in
theorem exists_levi_split [Finite K] [Finite E] (hK : 4 ≤ Nat.card K) (hr : 4 ≤ r)
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) :
    Group.IsPerfect (leviHom h r).range ∧
      ∀ y ∈ ⁅(leviHom h r).range.comap θ, (leviHom h r).range.comap θ⁆, θ y = 1 → y = 1 := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin r) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by omega)
  have : Group.IsPerfect (leviHom h r).range := Group.IsPerfect.range _
  refine ⟨this, ?_⟩
  set R := (leviHom h r).range with hR
  set Y := ⁅R.comap θ, R.comap θ⁆ with hY
  have : Group.IsPerfect Y := SymplecticSixCover.isPerfect_derivedComap hθ hC R
  have hYR : ∀ y : Y, θ y ∈ R := fun y =>
    Subgroup.mem_comap.1 (Subgroup.commutator_le_self (R.comap θ) y.2)
  let θR : Y →* R := (θ.comp Y.subtype).codRestrict R hYR
  have hθRsurj : Function.Surjective θR := by
    intro x
    have hx : (x : hypPSU h r 0) ∈ Y.map θ := by
      rw [SymplecticSixCover.map_derivedComap hθ R]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have hθRker : ∀ z : Y, θR z = 1 ↔ θ z = 1 := fun z => by
    rw [Subtype.ext_iff]
    rfl
  have hcen : θR.ker ≤ Subgroup.center Y := fun z hz => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hθRker z).mp hz)) g)
  have h2R : IsPGroup 2 θR.ker := fun z => by
    obtain ⟨n, hn⟩ := h2 ⟨(z : Y), (hθRker z).mp z.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun w : θ.ker => (w : E)) hn))⟩
  set ρ : SpecialLinearGroup (Fin r) K →* R := (leviHom h r).rangeRestrict with hρ
  have hρsurj : Function.Surjective ρ := (leviHom h r).rangeRestrict_surjective
  have hρinj : ∀ u ∈ LinearFlag.unitriangular r K, ρ u = 1 → u = 1 := fun u hu h1 =>
    eq_one_of_hypProj_lHom (by omega) hu (congrArg Subtype.val h1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := r) (by omega)
  set S := P.mapSurjective hρsurj with hS
  have hSle : (S : Subgroup R) ≤ (LinearFlag.unitriangular r K).map ρ := by
    rw [hS, Sylow.coe_mapSurjective, hP]
  have hbot := LinearCover.ker_eq_bot_of_rootHom (by omega) hr ρ hρinj S hSle θR hθRsurj hcen h2R
  intro y hy hy1
  have hk : (⟨y, hy⟩ : Y) ∈ θR.ker := (hθRker _).mpr hy1
  rw [hbot, Subgroup.mem_bot] at hk
  exact congrArg Subtype.val hk

theorem commute_of_isN_offH [Finite K] [Finite E] (hK : 4 ≤ Nat.card K) (hr : 4 ≤ r)
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker)
    {i j : Fin r} (hij : i ≠ j) {a a' : K} {x x' : E} (hx : IsN θ (offH h i j a) x)
    (hx' : IsN θ (offH h i j a') x') : x * x' = x' * x := by
  obtain ⟨hperf, hinj⟩ := exists_levi_split hK hr hθ hC h2
  obtain ⟨w, hw⟩ := hθ (hypProj h r 0 (swapElt h j))
  have hroot : ∀ (c : K) (y : E), IsN θ (offH h i j c) y →
      θ (w⁻¹ * y * w) = leviHom h r (SpecialLinearGroup.transvection hij c) := by
    intro c y hy
    obtain ⟨hB, he⟩ := hy
    have hsw := swapElt_mul_lHom (h := h) hij (A := SpecialLinearGroup.transvection hij c)
      (a := c) rfl
    rw [map_mul, map_mul, map_inv, hw, he, nElt_ext _ (isHerm_offH i j c) rfl, ← hsw]
    simp only [map_mul, map_inv, leviHom, MonoidHom.comp_apply]
    group
  have hy := hroot a x hx
  have hy' := hroot a' x' hx'
  have hcomm := SymplecticSixCover.mul_comm_of_derivedComap hθ hC (leviHom h r).range hinj
    (x := w⁻¹ * x * w) (y := w⁻¹ * x' * w) (by rw [hy]; exact ⟨_, rfl⟩)
    (by rw [hy']; exact ⟨_, rfl⟩)
    (by
      rw [hy, hy', ← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext ?_
      change Matrix.transvection i j a * Matrix.transvection i j a' =
        Matrix.transvection i j a' * Matrix.transvection i j a
      rw [Matrix.transvection_mul_transvection_same i j hij,
        Matrix.transvection_mul_transvection_same i j hij, add_comm])
  have := congrArg (fun z => w * z * w⁻¹) hcomm
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at this
  exact this

end CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover
