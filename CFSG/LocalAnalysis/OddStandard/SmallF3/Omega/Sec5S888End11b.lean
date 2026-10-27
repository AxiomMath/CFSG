module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End9b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End11a

public section

open Subgroup
open scoped MatrixGroups commutatorElement

namespace CFSG.OddStandard.SmallF3.Omega

theorem caseB_pocket {H X : Type} [Group H] [Finite H] [Group X] {z : H} (hz : z ∈ center H)
    (hz2 : orderOf z = 2) (α : H →* X) (hα : Function.Surjective α) (hker : α.ker = zpowers z)
    {Ob B : Subgroup X} [Ob.Normal] (hodd : Odd (Nat.card Ob)) (hOB : Ob ≤ B)
    (hBsub : B.IsSubnormal) {p n : ℕ} [Fact p.Prime] (hp : p ≠ 2) (h5 : 5 ≤ p ^ n)
    (e : ↥B ⧸ Ob.subgroupOf B ≃* PSL(2, GaloisField p n)) {a b : H} (ha : α a ∈ B)
    (hb : α b ∈ B) (hab : a * b * a⁻¹ * b⁻¹ = z) :
    ∃ P : Subgroup H, z ∈ P ∧ P.IsSubnormal ∧ IsSL2qMod P p n := by
  classical
  have hzker : z ∈ α.ker := by rw [hker]; exact Subgroup.mem_zpowers z
  have hαz : α z = 1 := MonoidHom.mem_ker.mp hzker
  let P : Subgroup H := B.comap α
  have hzP : z ∈ P := by
    change α z ∈ B
    rw [hαz]
    exact Subgroup.one_mem B
  have haP : a ∈ P := by
    change α a ∈ B
    exact ha
  have hbP : b ∈ P := by
    change α b ∈ B
    exact hb
  let R : Subgroup H := Ob.comap α
  have hRP : R ≤ P := Subgroup.comap_mono hOB
  let αB : ↥P →* ↥B :=
    { toFun := fun x => ⟨α x.1, Subgroup.mem_comap.mp x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hαBsurj : Function.Surjective αB := by
    intro y
    obtain ⟨x, hx⟩ := hα y.1
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change α x ∈ B
    rw [hx]
    exact y.2
  haveI hObBnorm : (Ob.subgroupOf B).Normal :=
    (inferInstance : Ob.Normal).subgroupOf B
  let φ : ↥P →* ↥B ⧸ Ob.subgroupOf B := (QuotientGroup.mk' (Ob.subgroupOf B)).comp αB
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Ob.subgroupOf B) y
    obtain ⟨x, hx⟩ := hαBsurj b
    exact ⟨x, by simp [φ, hx]⟩
  have hzφ : φ ⟨z, hzP⟩ = 1 := by
    have h1 : αB ⟨z, hzP⟩ = 1 := by
      ext
      simpa [αB] using hαz
    simp [φ, h1]
  have hφker : φ.ker = R.subgroupOf P := by
    ext x
    show (QuotientGroup.mk' (Ob.subgroupOf B) (αB x) : ↥B ⧸ Ob.subgroupOf B) = 1 ↔
      x.1 ∈ Ob.comap α
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_comap]
    rfl
  have hzR : z ∈ R := by
    change α z ∈ Ob
    rw [hαz]
    exact Subgroup.one_mem Ob
  have hcardR : Nat.card R = 2 * Nat.card Ob := by
    have hcardker : Nat.card (α.comp R.subtype).ker = 2 := by
      rw [← MonoidHom.comap_ker α R.subtype, hker]
      change Nat.card ((zpowers z).subgroupOf R) = 2
      rw [Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le_of_mem hzR)).toEquiv,
        Nat.card_zpowers, hz2]
    have hrange : (α.comp R.subtype).range = Ob := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact Subgroup.map_comap_eq_self_of_surjective hα Ob
    have h := Subgroup.card_ker_mul_card_range (α.comp R.subtype)
    rw [hcardker, hrange] at h
    exact h.symm
  have hcardφker : Nat.card φ.ker = 2 * Nat.card Ob := by
    rw [hφker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRP).toEquiv]
    exact hcardR
  have hzcenter : (⟨z, hzP⟩ : ↥P) ∈ center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz (g : H))
  have hz2' : orderOf (⟨z, hzP⟩ : ↥P) = 2 := by
    rw [Subgroup.orderOf_mk z hzP, hz2]
  have hzcomm : (⟨z, hzP⟩ : ↥P) ∈ commutator ↥P := by
    have h_eq : (⟨z, hzP⟩ : ↥P) = ⁅(⟨a, haP⟩ : ↥P), (⟨b, hbP⟩ : ↥P)⁆ := by
      apply Subtype.ext
      simpa [commutatorElement_def] using hab.symm
    rw [_root_.commutator_def, h_eq]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  refine ⟨P, hzP, isSubnormal_comap α hBsub, ?_⟩
  unfold IsSL2qMod
  exact sl2_quotient_of_double_cover hzcenter hz2' φ hφsurj hzφ hcardφker hodd hzcomm hp h5 e

end CFSG.OddStandard.SmallF3.Omega