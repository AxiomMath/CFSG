module

public import CFSG.Open.Defs
import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.Quasithin

private theorem le_normalizer_perfectCore_of_isSubnormal {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} (hHK : IsSubnormal H K) : ∀ {T : Subgroup G}, T ≤ K →
      (T.subgroupOf K).Normal → Group.IsSolvable T →
        T ≤ Subgroup.normalizer (perfectCore H : Set G) := by
  induction hHK with
  | refl K =>
    intro T hTK _ _
    exact hTK.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le K)).mp
      (perfectCore_normal K))
  | @step H M K hle hN hMK ih =>
    intro T hTK hTn hTs t ht
    have hQ : t ∈ Subgroup.normalizer (perfectCore M : Set G) := ih hTK hTn hTs ht
    have hMnorm : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
    have hMP : M ≤ Subgroup.normalizer (perfectCore H : Set G) :=
      hMnorm.trans (normalizer_le_normalizer_perfectCore H)
    have hPQ : perfectCore H ≤ perfectCore M := perfectCore_mono hle
    have hQP : perfectCore M ≤ Subgroup.normalizer (perfectCore H : Set G) :=
      (perfectCore_le M).trans hMP
    have hMK' : M ≤ K := A3.subnormal_le hMK
    set A : Subgroup G := T ⊓ perfectCore M with hA
    have hAs : Group.IsSolvable A :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_left : A ≤ T))
        (Subgroup.inclusion_injective _)
    have hAnorm : A ≤ Subgroup.normalizer (perfectCore H : Set G) := inf_le_right.trans hQP
    have hconj : (perfectCore H).map (MulAut.conj t).toMonoidHom ≤ perfectCore H ⊔ A := by
      rintro _ ⟨x, hx, rfl⟩
      have hxK : x ∈ K := hMK' (hle ((perfectCore_le H) hx))
      have hxQ : x ∈ perfectCore M := hPQ hx
      have htxQ : t * x * t⁻¹ ∈ perfectCore M :=
        (Subgroup.mem_normalizer_iff.mp hQ x).mp hxQ
      have hxT : x * t⁻¹ * x⁻¹ ∈ T :=
        (Subgroup.normal_subgroupOf_iff hTK).mp hTn t⁻¹ x (T.inv_mem ht) hxK
      have ha : t * x * t⁻¹ * x⁻¹ ∈ A := by
        refine ⟨?_, (perfectCore M).mul_mem htxQ ((perfectCore M).inv_mem hxQ)⟩
        have := T.mul_mem ht hxT
        simpa [mul_assoc] using this
      have : (MulAut.conj t).toMonoidHom x = (t * x * t⁻¹ * x⁻¹) * x := by
        simp [mul_assoc]
      rw [this]
      have h := Subgroup.mul_mem_sup ha hx
      rwa [sup_comm] at h
    have hPnormal : ((perfectCore H).subgroupOf (perfectCore H ⊔ A)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
      exact sup_le Subgroup.le_normalizer hAnorm
    have hperf : ⁅(perfectCore H).map (MulAut.conj t).toMonoidHom,
        (perfectCore H).map (MulAut.conj t).toMonoidHom⁆ =
        (perfectCore H).map (MulAut.conj t).toMonoidHom := by
      rw [← Subgroup.map_commutator, perfectCore_perfect]
    have hle' : (perfectCore H).map (MulAut.conj t).toMonoidHom ≤ perfectCore H :=
      (le_perfectCore_of_perfect hconj hperf).trans
        (perfectCore_le_of_sup_solvable le_sup_left hPnormal rfl hAs)
    have heq : (perfectCore H).map (MulAut.conj t).toMonoidHom = perfectCore H := by
      apply Subgroup.eq_of_le_of_card_ge hle'
      rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem le_normalizer_of_isSubnormal_of_perfect {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : IsSubnormal H ⊤) (hperf : ⁅H, H⁆ = H) (T : Subgroup G) [T.Normal]
    [Group.IsSolvable T] : T ≤ Subgroup.normalizer (H : Set G) := by
  have h := le_normalizer_perfectCore_of_isSubnormal hH (T := T) le_top
    Subgroup.normal_subgroupOf inferInstance
  rwa [perfectCore_eq_self_of_perfect hperf] at h

end CFSG.ClassicalInvolution
