module

public import CFSG.GH74.GLS.Stage1.Thm4.L97a
public import CFSG.GH74.GLS.Stage1.Thm4.L98b
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L97

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z : G} {K : Subgroup G}

omit [Finite G] in
theorem le_cen (h : IsRigidOfType Lh z K) : K ≤ Cz z := h.1.1.2.2.1

omit [Finite G] in
theorem pcomp (h : IsRigidOfType Lh z K) : IsPComponent 2 (K.subgroupOf (Cz z)) := h.1.1.2.2.2

theorem phiK_ker (hK : K ≤ Cz z) (hpc : IsPComponent 2 (K.subgroupOf (Cz z))) :
    (phiK hK).ker = pPrimeCore 2 ↥K := by
  ext x
  rw [mem_ker_phiK]
  constructor
  · intro hxO
    have hnorm : ((Oz z ⊓ K).subgroupOf K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : (n : G) ∈ Oz z ⊓ K := hn
      refine ⟨?_, (g * n * g⁻¹).2⟩
      have := Oz_conj (hK g.2) hn'.1
      simpa using this
    have hcop : Nat.Coprime 2 (Nat.card ((Oz z ⊓ K).subgroupOf K)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Oz z ⊓ K ≤ K)).toEquiv]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) card_Oz_coprime
    exact (le_sSup ⟨hnorm, hcop⟩ : (Oz z ⊓ K).subgroupOf K ≤ pPrimeCore 2 ↥K) ⟨hxO, x.2⟩
  · intro hx
    obtain ⟨_, _, hsub, _, _⟩ := hpc
    have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hsub
    let e : ↥(K.subgroupOf (Cz z)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hK
    have h2 := pPrimeCore_map_iso 2 e
    have hxm : x ∈ (pPrimeCore 2 ↥(K.subgroupOf (Cz z))).map e.toMonoidHom := by
      rw [h2]; exact hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxm
    have hy' : (y : ↥(Cz z)) ∈ pPrimeCore 2 ↥(Cz z) := h1 ⟨y, hy, rfl⟩
    have hyG : ((y : ↥(Cz z)) : G) = (x : G) := by
      have := congrArg Subtype.val hyx
      simpa [e] using this
    rw [← hyG]
    exact mem_Oz_iff.mpr hy'

noncomputable def hatBar (h : IsRigidOfType Lh z K) : HatT K ≃* ↥(barOf z K) :=
  (QuotientGroup.quotientMulEquivOfEq (phiK_ker (le_cen h) (pcomp h)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (phiK (le_cen h)) (phiK_surjective (le_cen h)))

omit [Finite G] in
theorem isComponent_bar (h : IsRigidOfType Lh z K) : IsComponent (barOf z K) := by
  obtain ⟨Kb, hKb, _, hmap, _⟩ := pcomp h
  have : barOf z K = Kb := hmap
  rw [this]; exact hKb

theorem bar_ne {K₁ K₂ : Subgroup G} (h₁ : IsRigidOfType Lh z K₁) (h₂ : IsRigidOfType Lh z K₂)
    (hne : K₁ ≠ K₂) : barOf z K₁ ≠ barOf z K₂ := by
  intro heq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.ComponentClassification.UnbalancedLayer.pComponent_eq_of_map_eq (p := 2)
    (pcomp h₁) (pcomp h₂) heq
  apply hne
  have := (Subgroup.subgroupOf_inj).mp h
  rwa [inf_eq_left.mpr (le_cen h₁), inf_eq_left.mpr (le_cen h₂)] at this

theorem bar_le_centralizer {K₁ K₂ : Subgroup G} (h₁ : IsRigidOfType Lh z K₁)
    (h₂ : IsRigidOfType Lh z K₂) (hne : K₁ ≠ K₂) :
    barOf z K₁ ≤ centralizer (barOf z K₂ : Set (CentralizerBar z)) := by
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_bar h₁) (isComponent_bar h₂)
    with h | h
  · exact absurd h (bar_ne h₁ h₂ hne)
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem rigid_unique {n : ℕ} (hrk : CFSG.pRank 2 G ≤ 4) (hn : 8 ≤ n)
    (hL : IsDoubleCoverOfAlt Lh n) {K₁ K₂ : Subgroup G} (h₁ : IsRigidOfType Lh z K₁)
    (h₂ : IsRigidOfType Lh z K₂) : K₁ = K₂ := by
  by_contra hne
  obtain ⟨e₁⟩ := h₁.2
  obtain ⟨e₂⟩ := h₂.2
  have : Finite Lh := Finite.of_equiv (HatT K₁) e₁.toEquiv
  obtain ⟨E, F, -, -, hE, hEc, hF, hFc, hFZ⟩ := exists_E_F hn hL
  let ψ₁ : Lh ≃* ↥(barOf z K₁) := e₁.symm.trans (hatBar h₁)
  let ψ₂ : Lh ≃* ↥(barOf z K₂) := e₂.symm.trans (hatBar h₂)
  let P : Subgroup (CentralizerBar z) := (E.map ψ₁.toMonoidHom).map (barOf z K₁).subtype
  let Q : Subgroup (CentralizerBar z) := (F.map ψ₂.toMonoidHom).map (barOf z K₂).subtype
  have hP : CFSG.Open.IsElemAbelian 2 P :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hE _) _
  have hQ : CFSG.Open.IsElemAbelian 2 Q :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hF _) _
  have hPc : Nat.card P = 2 ^ 3 := by
    rw [Subgroup.card_map_of_injective (barOf z K₁).subtype_injective,
      Subgroup.card_map_of_injective ψ₁.injective]
    exact hEc
  have hQc : Nat.card Q = 2 ^ 2 := by
    rw [Subgroup.card_map_of_injective (barOf z K₂).subtype_injective,
      Subgroup.card_map_of_injective ψ₂.injective]
    exact hFc
  have hPle : P ≤ barOf z K₁ := Subgroup.map_subtype_le _
  have hQle : Q ≤ barOf z K₂ := Subgroup.map_subtype_le _
  have hcent : P ≤ centralizer (Q : Set (CentralizerBar z)) := fun x hx =>
    Subgroup.centralizer_le (G := CentralizerBar z) (by exact_mod_cast hQle)
      (bar_le_centralizer h₁ h₂ hne (hPle hx))
  have hdisj : Disjoint P Q := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxP, hxQ⟩
    rw [Subgroup.mem_bot]
    obtain ⟨y, hyF, hyx⟩ := Subgroup.mem_map.mp hxQ
    obtain ⟨g, hgF, hgy⟩ := Subgroup.mem_map.mp hyF
    have hxc : x ∈ centralizer (barOf z K₂ : Set (CentralizerBar z)) :=
      bar_le_centralizer h₁ h₂ hne (hPle hxP)
    have hgZ : g ∈ center Lh := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply ψ₂.injective
      rw [map_mul, map_mul]
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp hxc ((ψ₂ l : ↥(barOf z K₂)) : CentralizerBar z)
        (ψ₂ l).2
      have hxy : (y : CentralizerBar z) = x := hyx
      have hgy' : ((ψ₂ g : ↥(barOf z K₂)) : CentralizerBar z) = (y : CentralizerBar z) := by
        rw [← hgy]; rfl
      change ((ψ₂ l : ↥(barOf z K₂)) : CentralizerBar z) *
          ((ψ₂ g : ↥(barOf z K₂)) : CentralizerBar z) =
        ((ψ₂ g : ↥(barOf z K₂)) : CentralizerBar z) * ((ψ₂ l : ↥(barOf z K₂)) : CentralizerBar z)
      rw [hgy', hxy]
      exact this
    have hg1 : g ∈ F ⊓ center Lh := ⟨hgF, hgZ⟩
    rw [hFZ, Subgroup.mem_bot] at hg1
    rw [← hyx, ← hgy, hg1]
    simp
  obtain ⟨R, -, -, hR, hRc, -⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
      (prime := 2) (firstRank := 3) (secondRank := 2) P Q hP hQ hPc hQc hcent hdisj
  have h5 : 3 + 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (CentralizerBar z)) :=
    CFSG.SectionRank.le_pRank one_lt_two le_top hR hRc
  have hN : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥(Cz z)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := CFSG.SectionRank.pRank_quotient_eq (p := 2) (pPrimeCore 2 ↥(Cz z)) hN
  have hs := CFSG.SectionRank.pRank_top_le_of_injective (p := 2) one_lt_two (Cz z).subtype
    (Cz z).subtype_injective
  have hG : CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 4 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]; exact hrk
  omega

end CFSG.GH74.GLS.Stage1.Thm4.L97
