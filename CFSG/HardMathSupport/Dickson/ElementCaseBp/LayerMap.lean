module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport

public section

namespace CFSG.HardMathSupport.Dickson.ElementCaseBp

open CFSG.ComponentClassification

theorem isPComponent_map_of_surjective {G G' : Type*} [Group G] [Group G'] [Finite G] {p : ℕ}
    [Fact p.Prime] {φ : G →* G'} (hφ : Function.Surjective φ) {B : Subgroup G}
    (hB : CFSG.IsPComponent p B) (hBφ : ¬ B ≤ φ.ker) : CFSG.IsPComponent p (B.map φ) := by
  have : Finite G' := Finite.of_surjective φ hφ
  rw [CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple] at hB ⊢
  obtain ⟨hsub, hres, hqs⟩ := hB
  have hψ : Function.Surjective (φ.subgroupMap B) := φ.subgroupMap_surjective B
  have hres' : CatalogueBPrimeJoin.primeResidual p (B.map φ) = ⊤ := by
    rw [← CatalogueBPrimeJoin.primeResidual_map_surjective p _ hψ, hres,
      Subgroup.map_top_of_surjective _ hψ]
  refine ⟨hsub.map hφ, hres', ?_⟩
  have : (CFSG.pPrimeCore p B).Normal := CFSG.pPrimeCore_normal
  have : (CFSG.pPrimeCore p (B.map φ)).Normal := CFSG.pPrimeCore_normal
  have hle : CFSG.pPrimeCore p B ≤ (CFSG.pPrimeCore p (B.map φ)).comap (φ.subgroupMap B) :=
    Subgroup.map_le_iff_le_comap.mp (CFSG.map_pPrimeCore_le _ hψ)
  have hθ := QuotientGroup.map_surjective_of_surjective _ _ _
    (QuotientGroup.mk_surjective.comp hψ) hle
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs
      (QuotientGroup.map _ _ _ hle).normal_ker with hker | hker
  · exfalso
    apply hBφ
    have hO : CFSG.pPrimeCore p (B.map φ) = ⊤ := by
      rw [← QuotientGroup.subsingleton_iff]
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := hθ a
      obtain ⟨b, rfl⟩ := hθ b
      rw [MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top a),
        MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top b)]
    have hcop : Nat.Coprime p (Nat.card (B.map φ)) := by
      have := CFSG.pPrimeCore_coprime_card (p := p) (G := B.map φ)
      rwa [hO, Subgroup.card_top] at this
    have hbot := CatalogueBPrimeJoin.primeResidual_eq_bot_of_coprime_card p hcop
    rw [hres'] at hbot
    rw [← Subgroup.map_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx⟩ : B.map φ) ∈ (⊥ : Subgroup (B.map φ)) :=
      hbot ▸ Subgroup.mem_top _
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hx'))
  · exact CFSG.LocalCores.isQuasisimple_of_surjective hqs _ hθ hker

theorem map_pLayer_le_of_range_normal {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (p : ℕ) [Fact p.Prime] (f : A →* B) (hf : f.range.Normal) :
    (CFSG.pLayer A p).map f ≤ CFSG.pLayer B p := by
  have : f.range.Normal := hf
  have hsub : f.range.IsSubnormal := Subgroup.Normal.isSubnormal hf
  unfold CFSG.pLayer
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro L hL
  apply Subgroup.map_le_iff_le_comap.mp
  have hL' : CFSG.IsPComponent p L := hL
  by_cases hLf : L ≤ f.ker
  · have h0 : L.map f ≤ ⊥ := by
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp (hLf hy))
    exact h0.trans bot_le
  · have hLg : ¬ L ≤ f.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hLf
    have hL1 : CFSG.IsPComponent p (L.map f.rangeRestrict) :=
      isPComponent_map_of_surjective f.rangeRestrict_surjective hL' hLg
    have hL2 := CatalogueBPrimeJoin.pComponent_extend_subnormal p f.range hsub
      (L.map f.rangeRestrict) hL1
    have heq : (L.map f.rangeRestrict).map f.range.subtype = L.map f := by
      rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
    rw [heq] at hL2
    exact le_sSup hL2

theorem map_pPrimeCore_le_of_range_normal {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] (p : ℕ) [Fact p.Prime] (f : A →* B) (hf : f.range.Normal) :
    (CFSG.pPrimeCore p A).map f ≤ CFSG.pPrimeCore p B := by
  have h1 : (CFSG.pPrimeCore p A).map f.rangeRestrict ≤ CFSG.pPrimeCore p f.range :=
    CFSG.map_pPrimeCore_le f.rangeRestrict f.rangeRestrict_surjective
  have h2 : (CFSG.pPrimeCore p f.range).map f.range.subtype = f.range ⊓ CFSG.pPrimeCore p B :=
    CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := p) hf
  have h3 : (CFSG.pPrimeCore p A).map f =
      ((CFSG.pPrimeCore p A).map f.rangeRestrict).map f.range.subtype := by
    rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
  rw [h3]
  calc ((CFSG.pPrimeCore p A).map f.rangeRestrict).map f.range.subtype
      ≤ (CFSG.pPrimeCore p f.range).map f.range.subtype := Subgroup.map_mono h1
    _ = f.range ⊓ CFSG.pPrimeCore p B := h2
    _ ≤ CFSG.pPrimeCore p B := inf_le_right

end CFSG.HardMathSupport.Dickson.ElementCaseBp
