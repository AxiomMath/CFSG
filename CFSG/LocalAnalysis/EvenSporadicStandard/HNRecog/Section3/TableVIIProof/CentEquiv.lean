module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem tableVII_cent_equiv {a c t : G} (htc : t ∈ Gxy a c) :
    ∃ e : ↥(Gx (⟨t, htc⟩ : ↥(Gxy a c))) ≃* ↥(Gxyz a t c),
      ∀ g, ((e g : ↥(Gxyz a t c)) : G) = ((g : ↥(Gxy a c)) : G) := by
  refine ⟨{ toFun := fun g => ⟨((g : ↥(Gxy a c)) : G), ?_⟩
            invFun := fun x => ⟨⟨(x : G), ?_⟩, ?_⟩
            left_inv := fun g => rfl
            right_inv := fun x => rfl
            map_mul' := fun g h => rfl }, fun g => rfl⟩
  · obtain ⟨hga, hgc⟩ := mem_Gxy.1 (g : ↥(Gxy a c)).2
    have hgt := congrArg Subtype.val (mem_Gx.1 g.2)
    exact mem_Gxyz.2 ⟨hga, mem_Gx.2 hgt, hgc⟩
  · obtain ⟨hxa, -, hxc⟩ := mem_Gxyz.1 x.2
    exact mem_Gxy.2 ⟨hxa, hxc⟩
  · obtain ⟨-, hxt, -⟩ := mem_Gxyz.1 x.2
    exact mem_Gx.2 (Subtype.ext (mem_Gx.1 hxt))

theorem tableVII_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (x : A) :
    Nonempty (↥(Subgroup.centralizer ({x} : Set A)) ≃*
      ↥(Subgroup.centralizer ({e x} : Set B))) := by
  refine ⟨{ toFun := fun u => ⟨e (u : A), ?_⟩
            invFun := fun v => ⟨e.symm (v : B), ?_⟩
            left_inv := fun u => Subtype.ext (e.symm_apply_apply (u : A))
            right_inv := fun v => Subtype.ext (e.apply_symm_apply (v : B))
            map_mul' := fun u v => Subtype.ext (map_mul e (u : A) (v : A)) }⟩
  · have hu := Subgroup.mem_centralizer_singleton_iff.1 u.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hu]
  · have hv := Subgroup.mem_centralizer_singleton_iff.1 v.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hv]

theorem tableVII_eq_closure_of_top {H : Type*} [Group H] (K : Subgroup H) (P : H → Prop)
    (hC : Subgroup.closure {y : ↥K | P (y : H)} = ⊤) :
    K = Subgroup.closure ((K : Set H) ∩ {x | P x}) := by
  have h1 := congrArg (Subgroup.map K.subtype) hC
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  refine h1.symm.trans (congrArg Subgroup.closure ?_)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hp⟩
    exact ⟨⟨x, hx⟩, hp, rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
