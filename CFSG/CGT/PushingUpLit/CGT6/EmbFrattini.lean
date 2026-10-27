module

public import CFSG.CGT.PushingUpLit.CGT6.EmbRes
public import CFSG.CGT.PushingUpLit.CGT6.EmbEight

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Frattini

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv G W)

theorem isSubnormal_barW {A Y : Subgroup (MulAut V)} (hYA : Y ≤ A) (hAG : A ≤ G)
    (hsub : (Y.subgroupOf A).IsSubnormal) :
    ((barW h Y).subgroupOf (barW h A)).IsSubnormal := by
  let f : ↥A →* ↥(barW h A) :=
    ((resG G W h).comp (Subgroup.inclusion hAG)).codRestrict (barW h A)
      (fun a => resG_mem_barW h (g := ⟨a, hAG a.2⟩) a.2)
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barW h).mp hz
    exact ⟨⟨g, hg⟩, rfl⟩
  have h1 := hsub.map hf
  convert h1 using 1
  ext z
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · intro hz
    obtain ⟨g, hg, hgz⟩ := (mem_barW h).mp hz
    refine ⟨⟨g, hYA hg⟩, hg, ?_⟩
    exact Subtype.ext hgz
  · rintro ⟨a, ha, rfl⟩
    exact resG_mem_barW h (g := ⟨a, hAG a.2⟩) ha

theorem conjClosure_le_centralizer {T Y A : Subgroup (MulAut V)}
    (hAT : A ≤ Subgroup.normalizer (T : Set (MulAut V)))
    (hYT : Y ≤ Subgroup.centralizer (T : Set (MulAut V))) :
    conjClosure Y A ≤ Subgroup.centralizer (T : Set (MulAut V)) := by
  rw [conjClosure, Subgroup.closure_le]
  rintro _ ⟨a, ha, y, hy, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro t ht
  have h1 : a⁻¹ * t * a⁻¹⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hAT (A.inv_mem ha)) t).mp ht
  have h2 : (a⁻¹ * t * a⁻¹⁻¹) * y = y * (a⁻¹ * t * a⁻¹⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (hYT hy) _ h1
  calc t * (a * y * a⁻¹) = a * ((a⁻¹ * t * a⁻¹⁻¹) * y) * a⁻¹ := by group
    _ = a * (y * (a⁻¹ * t * a⁻¹⁻¹)) * a⁻¹ := by rw [h2]
    _ = (a * y * a⁻¹) * t := by group

theorem isSubnormal_normalizer {G T Y : Subgroup (MulAut V)} (hYG : Y ≤ G)
    (hYT : Y ≤ Subgroup.centralizer (T : Set (MulAut V)))
    (hsub : (Y.subgroupOf (G ⊓ Subgroup.centralizer (T : Set (MulAut V)))).IsSubnormal) :
    (Y.subgroupOf (G ⊓ Subgroup.normalizer (T : Set (MulAut V)))).IsSubnormal := by
  set A := G ⊓ Subgroup.normalizer (T : Set (MulAut V)) with hA
  have hYA : Y ≤ A := le_inf hYG (hYT.trans (Subgroup.centralizer_le_normalizer _))
  have hY0 : conjClosure Y A ≤ G ⊓ Subgroup.centralizer (T : Set (MulAut V)) :=
    le_inf (conjClosure_le hYA |>.trans inf_le_left)
      (conjClosure_le_centralizer inf_le_right hYT)
  have h1 : (Y.subgroupOf (conjClosure Y A)).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hY0 hsub
  have h2 : ((conjClosure Y A).subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (conjClosure_le hYA)).2
      le_normalizer_conjClosure
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans le_conjClosure (conjClosure_le hYA)
    h1 h2.isSubnormal

theorem normalizer_barW_le {T Y : Subgroup (MulAut V)} [Finite V] (hTG : T ≤ G)
    (hT2 : IsPGroup 2 ↥T) (hCY : G ⊓ fixW W ≤ Subgroup.centralizer (Y : Set (MulAut V)))
    (hTY : T ≤ Subgroup.centralizer (Y : Set (MulAut V)))
    (hmax : ∀ T' : Subgroup (MulAut V), T ≤ T' →
      T' ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) → IsPGroup 2 ↥T' → T' = T) :
    barW h G ⊓ Subgroup.normalizer (barW h T : Set (MulAut ↥W)) ≤
      barW h (G ⊓ Subgroup.normalizer (T : Set (MulAut V))) := by
  rintro z ⟨hzG, hzN⟩
  obtain ⟨g, hg, rfl⟩ := (mem_barW h).mp hzG
  set M := preW h (barW h T) with hM
  have hMG : M ≤ G := preW_le h _
  have hTM : T ≤ M := le_preW_barW h hTG
  have hMY : M ≤ Subgroup.centralizer (Y : Set (MulAut V)) := by
    intro x hx
    obtain ⟨x', hx'x, hx'⟩ := (mem_preW h).mp hx
    obtain ⟨t, ht, hρ⟩ := (mem_barW h).mp hx'
    have hker : t⁻¹ * x' ∈ (resG G W h).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρ, inv_mul_cancel]
    have hc : ((t⁻¹ * x' : ↥G) : MulAut V) ∈ G ⊓ fixW W :=
      ⟨(t⁻¹ * x').2, (mem_ker_resG h).mp hker⟩
    have hx_eq : x = (t : MulAut V) * ((t⁻¹ * x' : ↥G) : MulAut V) := by
      rw [← hx'x]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [hx_eq]
    exact Subgroup.mul_mem _ (hTY ht) (hCY hc)
  have hmaxM : ∀ T' : Subgroup (MulAut V), T ≤ T' → T' ≤ M → IsPGroup 2 ↥T' → T' = T :=
    fun T' hTT' hT'M hT'2 => hmax T' hTT' (le_inf (hT'M.trans hMG) (hT'M.trans hMY)) hT'2
  have hgTM : T.map (MulAut.conj (g : MulAut V)).toMonoidHom ≤ M := by
    rintro _ ⟨t, ht, rfl⟩
    refine (mem_preW h).mpr ⟨g * ⟨t, hTG ht⟩ * g⁻¹, by simp [MulAut.conj_apply], ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hzN _).mp (resG_mem_barW h (g := ⟨t, hTG ht⟩) ht)
  obtain ⟨c, hcM, hc⟩ := exists_conj_le_of_maximal hTM hT2 hmaxM hgTM (hT2.map _)
  have hcG : c ∈ G := hMG hcM
  have hmapeq : (T.map (MulAut.conj (g : MulAut V)).toMonoidHom).map
      (MulAut.conj c).toMonoidHom = T.map (MulAut.conj (c * (g : MulAut V))).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
  rw [hmapeq] at hc
  have hcg : T.map (MulAut.conj (c * (g : MulAut V))).toMonoidHom = T := by
    refine Subgroup.eq_of_le_of_card_ge hc ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj (c * (g : MulAut V))).injective]
  have hcgN : c * (g : MulAut V) ∈ Subgroup.normalizer (T : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : (c * (g : MulAut V)) * x * (c * (g : MulAut V))⁻¹ ∈
          T.map (MulAut.conj (c * (g : MulAut V))).toMonoidHom :=
        ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      rwa [hcg] at this
    · intro hx
      rw [← hcg] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := (MulAut.conj (c * (g : MulAut V))).injective
        (hyx.trans (by simp only [MulAut.conj_apply]))
      rwa [← this]
  have h1 : resG G W h ⟨c, hcG⟩ ∈ barW h (G ⊓ Subgroup.normalizer (T : Set (MulAut V))) :=
    barW_mono h (le_inf hTG Subgroup.le_normalizer) (resG_mem_of_mem_preW h hcM hcG)
  have h2 : resG G W h ⟨c * (g : MulAut V), G.mul_mem hcG g.2⟩ ∈
      barW h (G ⊓ Subgroup.normalizer (T : Set (MulAut V))) :=
    resG_mem_barW h (g := ⟨c * (g : MulAut V), G.mul_mem hcG g.2⟩) ⟨G.mul_mem hcG g.2, hcgN⟩
  have h3 : resG G W h g = (resG G W h ⟨c, hcG⟩)⁻¹ *
      resG G W h ⟨c * (g : MulAut V), G.mul_mem hcG g.2⟩ := by
    rw [← map_inv, ← map_mul]
    congr 1
    ext
    simp
  rw [h3]
  exact mul_mem (inv_mem h1) h2

theorem isSubnormal_barW_normalizer {T Y : Subgroup (MulAut V)} [Finite V] (hYG : Y ≤ G)
    (hTG : T ≤ G) (hT2 : IsPGroup 2 ↥T)
    (hCY : G ⊓ fixW W ≤ Subgroup.centralizer (Y : Set (MulAut V)))
    (hTY : T ≤ Subgroup.centralizer (Y : Set (MulAut V)))
    (hmax : ∀ T' : Subgroup (MulAut V), T ≤ T' →
      T' ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) → IsPGroup 2 ↥T' → T' = T)
    (hYT : Y ≤ Subgroup.centralizer (T : Set (MulAut V)))
    (hsub : (Y.subgroupOf (G ⊓ Subgroup.centralizer (T : Set (MulAut V)))).IsSubnormal) :
    ((barW h Y).subgroupOf
      (barW h G ⊓ Subgroup.normalizer (barW h T : Set (MulAut ↥W)))).IsSubnormal := by
  have h1 := isSubnormal_normalizer hYG hYT hsub
  have hYA : Y ≤ G ⊓ Subgroup.normalizer (T : Set (MulAut V)) :=
    le_inf hYG (hYT.trans (Subgroup.centralizer_le_normalizer _))
  have h2 := isSubnormal_barW h hYA inf_le_left h1
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (normalizer_barW_le h hTG hT2 hCY hTY hmax) h2

end Frattini

end CFSG.CGT.PushingUpLit.CGT6
