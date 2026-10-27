module

public import CFSG.GH74.Generic.BProg.Stability
public import CFSG.GH74.Generic.BProg.LBalanceNested
public import CFSG.GH74.Generic.BProg.BpGeneral
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31D
public import CFSG.GH74.Generic.BProg.Helpers
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic Subgroup
open scoped commutatorElement

theorem component_le_of_noncomm {X : Type*} [Group X] [Finite X] {K₀ Z : Subgroup X}
    (hK : IsPComponent 2 K₀) (hZ : ∀ k ∈ K₀, ∀ z ∈ Z, k * z * k⁻¹ ∈ Z)
    {l₁ l₂ : X} (h₁ : l₁ ∈ K₀) (h₂ : l₂ ∈ K₀) (hz₁ : l₁ ∈ Z)
    (hnc : QuotientGroup.mk' (pPrimeCore 2 X) l₁ * QuotientGroup.mk' (pPrimeCore 2 X) l₂ ≠
      QuotientGroup.mk' (pPrimeCore 2 X) l₂ * QuotientGroup.mk' (pPrimeCore 2 X) l₁) :
    K₀ ≤ Z := by
  classical
  set π : X →* X ⧸ pPrimeCore 2 X := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  obtain ⟨Kb, hKbc, hsub, hmap, hmin⟩ := hK
  subst hmap
  set D : Subgroup X := K₀ ⊓ Z with hD
  have hDK : D ≤ K₀ := inf_le_left
  have hDnorm : (D.subgroupOf K₀).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hDK).2 fun d k hd hk =>
      Subgroup.mem_inf.2 ⟨K₀.mul_mem (K₀.mul_mem hk (Subgroup.mem_inf.1 hd).1) (K₀.inv_mem hk),
        hZ k hk d (Subgroup.mem_inf.1 hd).2⟩
  have hNnorm : ((D.map π).subgroupOf (K₀.map π)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨d, hd, hdn⟩ := hn
    obtain ⟨k, hk, hkg⟩ := g.2
    refine ⟨k * d * k⁻¹, (Subgroup.normal_subgroupOf_iff hDK).1 hDnorm d k hd hk, ?_⟩
    rw [map_mul, map_mul, map_inv, hkg, hdn]
    rfl
  have hQ : IsQuasisimple ↥(K₀.map π) := hKbc.1
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hQ hNnorm with
    htop | hcen
  · have hle : K₀.map π ≤ D.map π := fun a ha => by
      have : (⟨a, ha⟩ : ↥(K₀.map π)) ∈ (D.map π).subgroupOf (K₀.map π) := by
        rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.1 this
    have heq : D.map π = K₀.map π := le_antisymm (Subgroup.map_mono hDK) hle
    have hDeq : D = K₀ := by
      by_contra hne
      exact hmin D (lt_of_le_of_ne hDK hne)
        (Subgroup.IsSubnormal.trans hDK hDnorm.isSubnormal hsub) heq
    intro k hk
    rw [← hDeq] at hk
    exact (Subgroup.mem_inf.1 hk).2
  · exfalso
    apply hnc
    have hl₁ : (⟨π l₁, Subgroup.mem_map_of_mem π h₁⟩ : ↥(K₀.map π)) ∈
        (D.map π).subgroupOf (K₀.map π) := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_inf.2 ⟨h₁, hz₁⟩)
    have := Subgroup.mem_center_iff.1 (hcen hl₁) ⟨π l₂, Subgroup.mem_map_of_mem π h₂⟩
    exact (congrArg Subtype.val this).symm

theorem exists_noncomm_images {G : Type} [Group G] [Finite G] {Y I : Subgroup G} (hIY : I ≤ Y)
    [Group.IsPerfect ↥I] (hI1 : I ≠ ⊥) :
    ∃ a b : ↥Y, a ∈ I.subgroupOf Y ∧ b ∈ I.subgroupOf Y ∧
      QuotientGroup.mk' (pPrimeCore 2 ↥Y) a * QuotientGroup.mk' (pPrimeCore 2 ↥Y) b ≠
        QuotientGroup.mk' (pPrimeCore 2 ↥Y) b * QuotientGroup.mk' (pPrimeCore 2 ↥Y) a := by
  by_contra hcon
  push Not at hcon
  set π : ↥Y →* ↥Y ⧸ pPrimeCore 2 ↥Y := QuotientGroup.mk' (pPrimeCore 2 ↥Y) with hπ
  set I' : Subgroup ↥Y := I.subgroupOf Y with hI'
  have hperf : Group.IsPerfect ↥I' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hIY).symm.toMonoidHom)
      (MulEquiv.surjective _)
  set ψ : ↥I' →* ↥Y ⧸ pPrimeCore 2 ↥Y := π.comp I'.subtype with hψ
  have hker : (⊤ : Subgroup ↥I') ≤ ψ.ker := by
    have h1 : commutator ↥I' = ⊤ := hperf.commutator_eq_top
    rw [← h1, commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcon (g : ↥Y) (h : ↥Y) g.2 h.2)
  have hsub : I' ≤ pPrimeCore 2 ↥Y := by
    intro z hz
    have := hker (Subgroup.mem_top (⟨z, hz⟩ : ↥I'))
    rw [MonoidHom.mem_ker] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  have hodd : Odd (Nat.card ↥I') :=
    Odd.of_dvd_nat (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥Y)))
      (Subgroup.card_dvd_of_le hsub)
  have hsolv : Group.IsSolvable ↥I' := CFSG.Milestones.odd_order_solvable hodd
  have hnt : Nontrivial ↥I' := by
    have : Nontrivial ↥I := (Subgroup.nontrivial_iff_ne_bot I).2 hI1
    exact (Subgroup.subgroupOfEquivOfLe hIY).toEquiv.nontrivial
  exact Group.IsPerfect.not_isSolvable ↥I' hsolv

theorem dsemisimple_of_centralizes {G : Type} [Group G] [Finite G] {D L I : Subgroup G}
    (hL : IsPCompIn 2 (centralizer (D : Set G)) L) (hIL : I ≤ L) (hI1 : I ≠ ⊥)
    [Group.IsPerfect ↥I]
    (hleft : ∀ d ∈ D, d ≠ 1 → ⁅I, pPrimeCoreOf 2 (centralizer ({d} : Set G))⁆ = ⊥) :
    ∀ d ∈ D, d ≠ 1 → ⁅oPrimeResidualOf 2 L, pPrimeCoreOf 2 (centralizer ({d} : Set G))⁆ = ⊥ := by
  classical
  intro d hd hd1
  set W : Subgroup G := pPrimeCoreOf 2 (centralizer ({d} : Set G)) with hW
  set C : Subgroup G := centralizer (D : Set G) with hC
  have hLC : L ≤ C := hL.1
  have hIC : I ≤ C := hIL.trans hLC
  have hIW : I ≤ centralizer (W : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hleft d hd hd1)
  obtain ⟨a, b, ha, hb, hab⟩ := exists_noncomm_images hIC hI1
  have hZ : ∀ k ∈ L.subgroupOf C, ∀ z ∈ (centralizer (W : Set G)).subgroupOf C,
      k * z * k⁻¹ ∈ (centralizer (W : Set G)).subgroupOf C := by
    intro k hk z hz
    rw [Subgroup.mem_subgroupOf] at hk hz ⊢
    have hkd : (k : G)⁻¹ ∈ centralizer ({d} : Set G) := by
      refine Subgroup.inv_mem _ (Subgroup.mem_centralizer_singleton_iff.2 ?_)
      exact (Subgroup.mem_centralizer_iff.1 (hLC hk) d hd).symm
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : (k : G)⁻¹ * w * (k : G)⁻¹⁻¹ ∈ W :=
      CFSG.GH74.GLS.TwoThin.pPrimeCoreOf_normalized _ hkd hw
    have hzw : (k : G)⁻¹ * w * (k : G)⁻¹⁻¹ * (z : G) = (z : G) * ((k : G)⁻¹ * w * (k : G)⁻¹⁻¹) :=
      Subgroup.mem_centralizer_iff.1 hz _ hw'
    show w * ((k : G) * (z : G) * (k : G)⁻¹) = ((k : G) * (z : G) * (k : G)⁻¹) * w
    calc w * ((k : G) * (z : G) * (k : G)⁻¹)
        = (k : G) * ((k : G)⁻¹ * w * (k : G)⁻¹⁻¹ * (z : G)) * (k : G)⁻¹ := by group
      _ = (k : G) * ((z : G) * ((k : G)⁻¹ * w * (k : G)⁻¹⁻¹)) * (k : G)⁻¹ := by rw [hzw]
      _ = ((k : G) * (z : G) * (k : G)⁻¹) * w := by group
  have hLle : L.subgroupOf C ≤ (centralizer (W : Set G)).subgroupOf C :=
    component_le_of_noncomm hL.2 hZ (l₁ := a) (l₂ := b)
      (Subgroup.mem_subgroupOf.2 (hIL (Subgroup.mem_subgroupOf.1 ha)))
      (Subgroup.mem_subgroupOf.2 (hIL (Subgroup.mem_subgroupOf.1 hb)))
      (Subgroup.mem_subgroupOf.2 (hIW (Subgroup.mem_subgroupOf.1 ha))) hab
  have hLW : L ≤ centralizer (W : Set G) := fun l hl =>
    Subgroup.mem_subgroupOf.1 (hLle (Subgroup.mem_subgroupOf.2 hl : (⟨l, hLC hl⟩ : ↥C) ∈ L.subgroupOf C))
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 ?_
  exact (by
    rintro _ ⟨z, -, rfl⟩
    exact hLW z.2 : oPrimeResidualOf 2 L ≤ centralizer (W : Set G))

theorem lemma22_gen (hB : B_B2_g4) {G : Type} [Group G] [Finite G]
    (hKG : ∀ e : G, orderOf e = 2 →
      Gen4 ↥(centralizer ({e} : Set G)) ∧ IsKGroupNative ↥(centralizer ({e} : Set G)))
    {R : Subgroup G} (hR : IsPGroup 2 ↥R) {d e : G} (hdR : d ∈ R) (heR : e ∈ R)
    (hd : orderOf d = 2) (he : orderOf e = 2) (hde : d * e = e * d) :
    ⁅pLayerOf 2 (centralizer (R : Set G)),
        pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({e} : Set G)⁆ ≤
      pPrimeCoreOf 2 (centralizer ({e} : Set G)) := by
  set M : Subgroup G := centralizer ({e} : Set G) with hM
  have hdM : d ∈ M := Subgroup.mem_centralizer_singleton_iff.2 hde
  have hb2 := b2_general_inf hB (hKG e he).1 (hKG e he).2 hdM hd
  have hbal : pLayerOf 2 (centralizer (R : Set G)) ≤ pLayerOf 2 (M ⊓ centralizer ({d} : Set G)) := by
    have := pLayerOf_centralizer_le_inf_centralizer_of_mem hR hdR heR
    rwa [inf_comm] at this
  have hO : pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({e} : Set G) ≤
      pPrimeCoreOf 2 (M ⊓ centralizer ({d} : Set G)) := by
    have h1 := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.l31_inf_pPrimeCoreOf_le
      (H := centralizer ({d} : Set G)) (J := M ⊓ centralizer ({d} : Set G)) inf_le_right
    intro g hg
    have hgd : g ∈ centralizer ({d} : Set G) := CFSG.GH74.GLS.TwoThin.pPrimeCoreOf_le _ hg.1
    exact h1 (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hg.2, hgd⟩, hg.1⟩)
  exact (Subgroup.commutator_mono hbal hO).trans hb2

theorem thm2_nonsolvable (hB : B_B2_g4) {G : Type} [Group G] [Finite G]
    (hKG : ∀ e : G, orderOf e = 2 →
      Gen4 ↥(centralizer ({e} : Set G)) ∧ IsKGroupNative ↥(centralizer ({e} : Set G)))
    {D E L I : Subgroup G} (hD : CFSG.IsElementaryAbelian 2 ↥D) (hE : CFSG.IsElementaryAbelian 2 ↥E)
    (hDnE : D ≤ normalizer (E : Set G)) (hCE : 2 ≤ pRank 2 ↥(E ⊓ centralizer (D : Set G)))
    (hL : IsPCompIn 2 (centralizer (D : Set G)) L)
    (hI : IsPCompIn 2 (centralizer ((D ⊔ E : Subgroup G) : Set G)) I) (hIL : I ≤ L) (hI1 : I ≠ ⊥) :
    thetaHalf (pRank 2 ↥E - 1) E ≠ ⊥ ∨
      ∀ d ∈ D, d ≠ 1 → ⁅oPrimeResidualOf 2 L, pPrimeCoreOf 2 (centralizer ({d} : Set G))⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDp : IsPGroup 2 ↥D := IsElementaryAbelian.isPGroup 2 D
  have hEp : IsPGroup 2 ↥E := IsElementaryAbelian.isPGroup 2 E
  have hRp : IsPGroup 2 ↥(D ⊔ E) := IsPGroup.to_sup_of_normal_right' hDp hEp hDnE
  set Y : Subgroup G := centralizer ((D ⊔ E : Subgroup G) : Set G) with hY
  have hIY : I ≤ Y := hI.1
  have hIperf : Group.IsPerfect ↥(I.subgroupOf Y) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hI.2
  have hIperf' : Group.IsPerfect ↥I :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hIY).toMonoidHom)
      (MulEquiv.surjective _)
  have hI2 : oPrimeResidualOf 2 I = I := by
    have htop : oPrimeResidual 2 ↥I = ⊤ := oPrimeResidual_eq_top_of_isPerfect
    unfold oPrimeResidualOf
    rw [htop, Subgroup.map_top, Subgroup.range_subtype]
  have h2C : ∀ d ∈ D ⊔ E, ∀ e ∈ D ⊔ E, orderOf d = 2 → orderOf e = 2 → d * e = e * d →
      ⁅I, pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({e} : Set G)⁆ ≤
        pPrimeCoreOf 2 (centralizer ({e} : Set G)) := by
    intro d hd e he hd2 he2 hde
    have hIle : I ≤ pLayerOf 2 (centralizer ((D ⊔ E : Subgroup G) : Set G)) := le_sSup hI
    exact (Subgroup.commutator_mono hIle le_rfl).trans (lemma22_gen hB hKG hRp hd he hd2 he2 hde)
  rcases stability hD hE hDnE hCE hI.1 hI2 h2C with hleft | hright
  · right
    have : Group.IsPerfect ↥I := hIperf'
    exact dsemisimple_of_centralizes hL hIL hI1 hleft
  · left
    intro h
    apply hright
    rw [h]
    exact Subgroup.commutator_bot_right _

end CFSG.GH74.Generic.BProg
