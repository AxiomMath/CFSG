module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitChainWeak
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainOrbitTools

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem nonempty_fusionZStar_equiv_of_quotient_equiv {X Y : Type} [Group X] [Group Y]
    [Finite X] [Finite Y] (e : X ⧸ pPrimeCore 2 X ≃* Y ⧸ pPrimeCore 2 Y) :
    Nonempty (X ⧸ Open.fusionZStar X ≃* Y ⧸ Open.fusionZStar Y) := by
  have hodd : ∀ (Z : Type) [Group Z] [Finite Z],
      ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 Z)).ker := by
    intro Z _ _ h
    rw [QuotientGroup.ker_mk'] at h
    exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
      (even_iff_two_dvd.mpr h)
  obtain ⟨e₁⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective
    (QuotientGroup.mk' (pPrimeCore 2 X)) (QuotientGroup.mk'_surjective _) (hodd X)
  obtain ⟨e₂⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective
    (QuotientGroup.mk' (pPrimeCore 2 Y)) (QuotientGroup.mk'_surjective _) (hodd Y)
  obtain ⟨e₃⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective e.toMonoidHom
    e.surjective (by
      rw [show e.toMonoidHom.ker = ⊥ from (MonoidHom.ker_eq_bot_iff _).mpr e.injective, card_bot]
      norm_num)
  exact ⟨e₁.trans (e₃.trans e₂.symm)⟩

theorem isSubnormal_inf_centralizer {a b : G} (hab : a * b = b * a) {M : Subgroup G}
    (hMb : M ≤ centralizer ({b} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G)))) :
    (((M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G)).subgroupOf
      (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G))).IsSubnormal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({b} : Set G) with hH
  set K := M ⊔ conjugate M a with hKdef
  obtain ⟨hKE, hEK⟩ := sup_conjugate_le_pLayer hab hMb hM
  have : (pLayer ↥H 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  have hEn : (pLayer ↥H 2).IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
  have hKE' : K.subgroupOf H ≤ pLayer ↥H 2 := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := mem_map.mp (hKE (mem_subgroupOf.mp hx))
    rwa [← Subtype.ext hyx]
  have hKn : ((K.subgroupOf H).subgroupOf (pLayer ↥H 2)).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
    have hgN : ((g : H) : G) ∈ normalizer (K : Set G) := hEK ⟨g, g.2, rfl⟩
    have h1 := (mem_normalizer_iff.mp hgN ((x : H) : G)).mp hx
    simpa using h1
  have hKsub : (K.subgroupOf H).IsSubnormal := Subgroup.IsSubnormal.trans hKE' hKn.isSubnormal hEn
  have h1 := hKsub.comap (Subgroup.inclusion (inf_le_right :
    centralizer ({a} : Set G) ⊓ H ≤ H))
  have h2 : (K.subgroupOf H).comap (Subgroup.inclusion (inf_le_right :
      centralizer ({a} : Set G) ⊓ H ≤ H)) =
      (K ⊓ centralizer ({a} : Set G)).subgroupOf (centralizer ({a} : Set G) ⊓ H) := by
    ext x
    simp only [mem_comap, mem_subgroupOf, coe_inclusion, mem_inf]
    exact ⟨fun h => ⟨h, (mem_inf.mp x.2).1⟩, fun h => h.1⟩
  rwa [h2] at h1

theorem gsFixedLayer_isPComponent_of_gsWeakCorr (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) {a b : G} {L M : Subgroup G}
    (h : GSWeakCorr a L b M) (hbZ : b ∉ center G) :
    gsFixedLayer L b ≤ (M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G) ∧
      IsPComponent 2 ((gsFixedLayer L b).subgroupOf
        ((M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G))) ∧
      Nonempty (gsFixedLayer L b ⧸ pPrimeCore 2 (gsFixedLayer L b) ≃* L ⧸ pPrimeCore 2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ha, hb, hab, hLa, hL, hMb, hM, hbL, hLb, hTK⟩ := id h
  have hLaa : conjugate L a = L := UnbalancedCorr.conjugate_eq_self_of_le_centralizer hLa
  have hKe : ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * b⁻¹ * k * b ∈
      (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype := by
    rw [hLaa, sup_idem]
    intro k hk
    exact GSLit.map_pPrimeCore_le_of_isPComponent hLa hL (hLb k hk)
  obtain ⟨-, -, -, -, hTab, hTpc, -, -, -, -, φ, -⟩ :=
    UGSChain.kProper_core_trivial_orbit_fixed_layer_containment_of_schreier hS hK ha hb rfl hab
      hbZ hLa hL hKe
  set T := gsFixedLayer L b with hTdef
  set N := (M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G) with hNdef
  set H₀ := centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) with hH₀
  have hTN : T ≤ N := le_inf hTK (hTab.trans inf_le_left)
  have hNH₀ : N ≤ H₀ := by
    obtain ⟨hMaHb, -⟩ := UGSChain.conjugate_isPComponent_centralizer hab hMb hM
    exact le_inf inf_le_right (inf_le_left.trans (sup_le hMb hMaHb))
  have hNsub := isSubnormal_inf_centralizer hab hMb hM
  have h1 := (CatalogueBPrimeJoin.pComponent_subnormal_overgroup_iff 2 (T.subgroupOf H₀)
    (N.subgroupOf H₀) (fun x hx => hTN hx) hNsub).mpr hTpc
  exact ⟨hTN, (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) hNH₀ 2
    Nat.prime_two).mp h1, ⟨φ⟩⟩

theorem gsWeakCorr_type_dichotomy (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) {a b : G} {L M : Subgroup G}
    (h : GSWeakCorr a L b M) (hbZ : b ∉ center G) :
    Nonempty (L ⧸ Open.fusionZStar L ≃* M ⧸ Open.fusionZStar M) ∨
      (conjugate M a = M ∧ gsFixedLayer L b ≤ M ⊓ centralizer ({a} : Set G) ∧
        IsPComponent 2 ((gsFixedLayer L b).subgroupOf (M ⊓ centralizer ({a} : Set G))) ∧
        (pPrimeCore 2 (gsFixedLayer L b)).index < (pPrimeCore 2 M).index ∧
        Nonempty (L ⧸ Open.fusionZStar L ≃*
          gsFixedLayer L b ⧸ Open.fusionZStar (gsFixedLayer L b))) := by
  obtain ⟨ha, hb, hab, hLa, hL, hMb, hM, hbL, hLb, -⟩ := id h
  obtain ⟨hTN, hTpc, ⟨φ⟩⟩ := gsFixedLayer_isPComponent_of_gsWeakCorr hS hK h hbZ
  set T := gsFixedLayer L b with hTdef
  obtain ⟨hidxle, hmoved, heqcase⟩ := UGSChain.orbit_fixed_component_comparison ha hab hMb hM hTN
    hTpc
  have hTL : (pPrimeCore 2 T).index = (pPrimeCore 2 L).index := by
    rw [index_eq_card, index_eq_card]
    exact Nat.card_congr φ.toEquiv
  by_cases hcase : M ≠ conjugate M a ∨ (pPrimeCore 2 T).index = (pPrimeCore 2 M).index
  · left
    have hfix : gsFixedLayer (M ⊔ conjugate M a) a = T := by
      rcases hcase with hne | heq
      · exact hmoved hne
      · exact (heqcase heq).1
    have hC : GSCorr a L b M := ⟨ha, hb, hab, hLa, hL, hMb, hM, hbL, hLb, hfix.symm⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hiso, -⟩ :=
      commuting_source_change_and_quotient_control ha rfl hab hLa hL hC rfl rfl
    rcases hcase with hne | heq
    · exact (hiso (Or.inl (Ne.symm hne))).2
    · exact (hiso (Or.inr (hTL.symm.trans heq))).2
  · right
    push Not at hcase
    obtain ⟨hMa, hne⟩ := hcase
    have hMa' : conjugate M a = M := hMa.symm
    rw [hMa', sup_idem] at hTN hTpc
    obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_quotient_equiv φ
    exact ⟨hMa', hTN, hTpc, lt_of_le_of_ne hidxle hne, ⟨e.symm⟩⟩

end CFSG.ComponentClassification.GrSLit
