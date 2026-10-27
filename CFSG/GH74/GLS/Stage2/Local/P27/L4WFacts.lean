module

public import CFSG.GH74.GLS.Stage2.Local.P27.L4Pgl
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Base

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GorensteinWalter

namespace L4WFacts

theorem normalizer_of_pglOver {X : Type} [Group X] [Finite X] {L : Subgroup X} {y : X} {q : ℕ}
    (hL : HasSL2Model ↥L (fun s => s = q)) (hyL : y ∉ L) (h : PGLOver L (zpowers y) q) :
    y ∈ normalizer (L : Set X) := by
  classical
  have hLcard : Nat.card ↥L = q * (q ^ 2 - 1) := L4Pgl.card_hasSL2Model hL
  have hZle : Nat.card ↥(center ↥L) ≤ 2 := L4Pgl.card_center_le_two hL
  obtain ⟨hZn, F, iF, fF, hFq, ⟨φ⟩⟩ := h
  set Z : Subgroup X := (center ↥L).map L.subtype with hZdef
  set N : Subgroup X := L ⊔ zpowers y with hNdef
  have hZL : Z ≤ L := Subgroup.map_subtype_le _
  have hLN : L ≤ N := le_sup_left
  have hyN' : y ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hZN : Z ≤ N := hZL.trans hLN
  have hZcard : Nat.card ↥Z = Nat.card ↥(center ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hPGL : Nat.card (PGL2 F) = q * (q ^ 2 - 1) := by rw [pgl2_card_formula, hFq]
  have hNcard : Nat.card ↥N = Nat.card ↥Z * (q * (q ^ 2 - 1)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf N)
    rw [Nat.card_congr φ.toEquiv, hPGL,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv] at h1
    rw [h1]
    ring
  have hZ2 : Nat.card ↥Z = 2 := by
    have hlt : Nat.card ↥L < Nat.card ↥N := by
      by_contra hge
      push Not at hge
      have hLeq := Subgroup.eq_of_le_of_card_ge hLN hge
      exact hyL (hLeq ▸ hyN')
    rw [hNcard, ← hLcard] at hlt
    have h1 : 1 < Nat.card ↥Z := by
      by_contra hle
      push Not at hle
      have : Nat.card ↥Z * Nat.card ↥L ≤ 1 * Nat.card ↥L := Nat.mul_le_mul_right _ hle
      omega
    omega
  have hNL : Nat.card ↥N = 2 * Nat.card ↥L := by rw [hNcard, hZ2, hLcard]
  have hidx : (L.subgroupOf N).index = 2 := by
    have h1 := Subgroup.index_mul_card (L.subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv, hNL] at h1
    have hLpos : 0 < Nat.card ↥L := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hLpos h1
  have hnormal : (L.subgroupOf N).Normal := Subgroup.normal_of_index_eq_two hidx
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hLN).1 hnormal) hyN'

end L4WFacts

theorem l4_w_facts {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q a : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z))
    (hP : Stage1Pair G z S q L₁ L₂) {P₁ : Subgroup G}
    (hP₁ : P₁ = (L₁.comap (Psp4Stage1.rhoS hS)).map S.subtype) (hPc : Nat.card ↥P₁ = 2 ^ a)
    {w : G} (hw : GoodInvolution z S L₁ L₂ q w) (hwR : w ∉ RC S z) :
    (∀ p ∈ P₁, w * p * w⁻¹ ∈ P₁) ∧
      ∃ (D : Type) (_ : Group D) (f : ↥(P₁ ⊔ zpowers w) →* D), Function.Surjective f ∧
        f.ker = (zpowers z).subgroupOf (P₁ ⊔ zpowers w) ∧ IVK.IsDihedralTwoGroup D a := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hwS, hw2, hPGL₁, -⟩ := hw
  have hSC : S ≤ Cen z := Psp4Stage1.S_le_Cen hS
  have hwC : w ∈ Cen z := hSC hwS
  have hρ := Psp4Stage1.rhoS_injective hS
  set ρ := Psp4Stage1.rhoS hS with hρdef
  have hzS : z ∈ S := Psp4Stage1.z_mem_of_sylow hz hS
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, pow_two] at this
  set wb : CentralizerBar z := toBar z ⟨w, hwC⟩ with hwb
  have hwb2 : wb * wb = 1 := by
    rw [hwb, ← map_mul]
    have : (⟨w, hwC⟩ : ↥(Cen z)) * ⟨w, hwC⟩ = 1 := Subtype.ext hww
    rw [this, map_one]
  have hρw : ρ ⟨w, hwS⟩ = wb := rfl
  have hP₁S : P₁ ≤ S := by
    rw [hP₁]
    exact Subgroup.map_subtype_le _
  have hmem : ∀ g : G, g ∈ P₁ ↔ ∃ hg : g ∈ S, ρ ⟨g, hg⟩ ∈ L₁ := by
    intro g
    rw [hP₁]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.2, hs⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hbarw : barOf z (zpowers w) = zpowers wb := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hc)
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have : (⟨w, hwC⟩ : ↥(Cen z)) ^ k = c := Subtype.ext (by simpa using hk)
      rw [hwb, ← map_zpow, this]
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      refine ⟨⟨w, hwC⟩ ^ k, ?_, by rw [hwb, map_zpow]⟩
      exact Subgroup.mem_subgroupOf.2 (by simp)
  have hPGL : PGLOver L₁ (zpowers wb) q := hbarw ▸ hPGL₁
  have hL₁le : L₁ ≤ LBar z := by
    rw [← hP.prod.1]
    exact le_sup_left
  have hwL : wb ∉ L₁ := by
    intro h
    apply hwR
    have hg : (⟨w, hwC⟩ : ↥(Cen z)) ^ (2 ^ 1) = 1 := by
      rw [pow_one, pow_two]
      exact Subtype.ext hww
    have hLC : w ∈ LC z := (Stage1.Thm6.Prod.mem_LC_iff_of_pElt z ⟨w, hwC⟩ hg).2 (hL₁le h)
    exact Subgroup.mem_inf.2 ⟨hwS, hLC⟩
  have hnorm : wb ∈ normalizer (L₁ : Set (CentralizerBar z)) :=
    L4WFacts.normalizer_of_pglOver hP.sl₁ hwL hPGL
  have hpart1 : ∀ p ∈ P₁, w * p * w⁻¹ ∈ P₁ := by
    intro p hp
    obtain ⟨hpS, hpL⟩ := (hmem p).1 hp
    have hwpS : w * p * w⁻¹ ∈ S := S.mul_mem (S.mul_mem hwS hpS) (S.inv_mem hwS)
    refine (hmem _).2 ⟨hwpS, ?_⟩
    have : ρ ⟨w * p * w⁻¹, hwpS⟩ = wb * ρ ⟨p, hpS⟩ * wb⁻¹ := by
      have h1 : (⟨w * p * w⁻¹, hwpS⟩ : ↥S) = ⟨w, hwS⟩ * ⟨p, hpS⟩ * ⟨w, hwS⟩⁻¹ := rfl
      rw [h1, map_mul, map_mul, map_inv, hρw]
    rw [this]
    exact (Subgroup.mem_normalizer_iff.1 hnorm _).1 hpL
  refine ⟨hpart1, ?_⟩
  have hrange : ρ.range = barOf z S := by
    ext x
    rw [Psp4Stage1.mem_barOf_S_iff hS]
    exact MonoidHom.mem_range
  have hbarP : barOf z P₁ = barOf z S ⊓ L₁ := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨hcS, hcL⟩ := (hmem (c : G)).1 (Subgroup.mem_subgroupOf.1 hc)
      exact ⟨(Psp4Stage1.mem_barOf_S_iff hS _).2 ⟨⟨c, hcS⟩, rfl⟩, hcL⟩
    · rintro ⟨hxS, hxL⟩
      obtain ⟨s, rfl⟩ := (Psp4Stage1.mem_barOf_S_iff hS _).1 hxS
      exact ⟨⟨s.1, hSC s.2⟩, Subgroup.mem_subgroupOf.2 ((hmem _).2 ⟨s.2, hxL⟩), rfl⟩
  have hbarP' : barOf z P₁ = (L₁.comap ρ).map ρ := by
    rw [hbarP, Subgroup.map_comap_eq, hrange, inf_comm]
  have hPcard' : Nat.card ↥(barOf z P₁) = 2 ^ a := by
    rw [hbarP', Subgroup.card_map_of_injective hρ]
    have h1 : Nat.card ↥P₁ = Nat.card ↥(L₁.comap ρ) := by
      rw [hP₁]
      exact Subgroup.card_map_of_injective S.subtype_injective
    rw [← h1, hPc]
  have hSyl : IsSylowOf 2 (barOf z P₁) L₁ := hbarP ▸ (Psp4Stage1.bar_sylow_structure hS hP).2.1
  have hZ2 : Nat.card ↥(center ↥L₁) = 2 := (Psp4Stage1.isSL2Or2A7_of_pair hz hP).1.2
  have hc2 : ∀ c ∈ center ↥L₁, IsPGroup 2 (zpowers c) := by
    intro c hc
    have hd : orderOf c ∣ 2 := by
      have h1 : orderOf (⟨c, hc⟩ : ↥(center ↥L₁)) ∣ Nat.card ↥(center ↥L₁) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hZ2] at h1
      exact h1
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  have hZP : (center ↥L₁).map L₁.subtype ≤ barOf z P₁ := by
    obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
    rintro _ ⟨c, hc, rfl⟩
    have h1 := Psp4Stage1.central_mem_sylow Q hc (hc2 c hc)
    rw [hQ] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hwbS : wb ∈ barOf z S := (Psp4Stage1.mem_barOf_S_iff hS _).2 ⟨⟨w, hwS⟩, rfl⟩
  have hyN : wb ∈ normalizer ((barOf z P₁ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
    rw [hbarP, Subgroup.mem_normalizer_iff]
    intro h
    have h1 := Subgroup.mem_normalizer_iff.1 hnorm h
    have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hwbS) h
    constructor
    · rintro ⟨hS', hL'⟩
      exact ⟨h2.1 hS', h1.1 hL'⟩
    · rintro ⟨hS', hL'⟩
      exact ⟨h2.2 hS', h1.2 hL'⟩
  set A : Subgroup G := P₁ ⊔ zpowers w with hAdef
  set Ab : Subgroup (CentralizerBar z) := barOf z P₁ ⊔ zpowers wb with hAbdef
  obtain ⟨D, iD, fb, hfs, hfk, hD⟩ := exists_dihedral_hom_of_pglOver (X := CentralizerBar z) (L := L₁)
    (P := barOf z P₁) (y := wb) (q := q) (a := a) hP.odd hP.gt3 hwb2 hP.sl₁ hSyl hPcard' hZP hyN hwL hPGL
  have hAS : A ≤ S := sup_le hP₁S (Subgroup.zpowers_le.2 hwS)
  have hAC : A ≤ Cen z := hAS.trans hSC
  have hbarA : barOf z A = Ab := by
    show ((P₁ ⊔ zpowers w).subgroupOf (Cen z)).map (toBar z) = _
    rw [Subgroup.subgroupOf_sup (hP₁S.trans hSC) (Subgroup.zpowers_le.2 hwC),
      Subgroup.map_sup, hAbdef, ← hbarw]
    rfl
  let ρA : ↥A →* CentralizerBar z := ρ.comp (Subgroup.inclusion hAS)
  have hρA : ∀ x : ↥A, ρA x ∈ Ab := fun x =>
    hbarA ▸ ⟨⟨x, hAC x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  let ρ' : ↥A →* ↥Ab := ρA.codRestrict Ab hρA
  have hρ'surj : Function.Surjective ρ' := by
    rintro ⟨y, hy⟩
    rw [← hbarA] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, Subgroup.mem_subgroupOf.1 hc⟩, Subtype.ext rfl⟩
  set zb : CentralizerBar z := toBar z ⟨z, mem_Cen_self z⟩ with hzbdef
  have hzb : zb ∈ L₁ := (IVK.Proofs2.Ivk93Adapt.zbarC_mem_inf hP).1
  have hzbc : (⟨zb, hzb⟩ : ↥L₁) ∈ center ↥L₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.1 (toBar_z_mem_center z) g.1))
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have hzb2 : orderOf (⟨zb, hzb⟩ : ↥L₁) = 2 := by
    rw [← Subgroup.orderOf_coe]
    apply orderOf_eq_prime _ (Psp4Stage1.zbar_ne_one_of_central hz)
    show zb ^ 2 = 1
    rw [pow_two, hzbdef, ← map_mul]
    have : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) * ⟨z, mem_Cen_self z⟩ = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hZeq : center ↥L₁ = zpowers (⟨zb, hzb⟩ : ↥L₁) := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzbc)
    rw [Nat.card_zpowers, hzb2, hZ2]
  have hZb : (center ↥L₁).map L₁.subtype = zpowers zb := by
    rw [hZeq, MonoidHom.map_zpowers]
    rfl
  have hker : (fb.comp ρ').ker = (zpowers z).subgroupOf A := by
    ext x
    have h1 : x ∈ (fb.comp ρ').ker ↔ ρ' x ∈ fb.ker := by simp [MonoidHom.mem_ker]
    rw [h1, hfk, Subgroup.mem_subgroupOf, hZb, Subgroup.mem_subgroupOf]
    have hval : ((ρ' x : ↥Ab) : CentralizerBar z) = ρ ⟨x, hAS x.2⟩ := rfl
    rw [hval]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
      have h3 : ρ (⟨z, hzS⟩ ^ k) = ρ ⟨x, hAS x.2⟩ := by
        rw [map_zpow]
        exact hk
      have h4 := hρ h3
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val h4⟩
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
      have h3 : (⟨x, hAS x.2⟩ : ↥S) = ⟨z, hzS⟩ ^ k := Subtype.ext (by simpa using hk.symm)
      rw [h3, map_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers zb) k
  exact ⟨D, iD, fb.comp ρ', hfs.comp hρ'surj, hker, hD⟩

end CFSG.GH74.GLS.Stage2.Local.P27
