module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLFam
public import CFSG.ClassicalInvolution.Asc77.AscT7L4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem mem_sylow_of_isUniqueInvolution (hΩ : HypOmegaGen Ω) {J P : Subgroup G} (hJ : J ∈ Ω)
    (hP : IsSylow2In P J) {z : G} (hz : IsUniqueInvolution J z) : z ∈ P := by
  obtain ⟨-, -, -, -, hnc⟩ := TwinEdge.Fam.member_data hΩ hJ hP (le_top : P ≤ (⊤ : Subgroup G))
  obtain ⟨w, hwP, hw1, hw2⟩ := TwinEdge.Fam.exists_involution_of_nonabelian hP.2.1 hnc
  have hwz : w = z := (hz.unique w (hP.1 hwP) hw2).resolve_left hw1
  exact hwz ▸ hwP

theorem isUniqueInvolution_secImage (hΩ : HypOmegaGen Ω) {J P : Subgroup G} (hJ : J ∈ Ω)
    (hP : IsSylow2In P J) (hPX : P ≤ rLayerSub Ω A) {z : G} (hz : IsUniqueInvolution J z)
    (hzX : z ∈ rLayerSub Ω A) :
    IsUniqueInvolution (secImage (rLayerSub Ω A) P)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub Ω A)) ⟨z, hzX⟩) := by
  have hzP := mem_sylow_of_isUniqueInvolution hΩ hJ hP hz
  have h1 : IsUniqueInvolution P z := isUniqueInvolution_mono hz hP.1 hzP
  have h2 := isUniqueInvolution_subgroupOf h1 hPX
  exact isUniqueInvolution_map_mk_of_odd
    (odd_natCard_inf (CFSG.ComponentClassification.OddCore.odd_card ↥(rLayerSub Ω A)) _) h2

theorem natCard_map_mk_of_isPGroup {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    (hN : Odd (Nat.card N)) {B : Subgroup H} (hB : IsPGroup 2 ↥B) :
    Nat.card ↥(B.map (QuotientGroup.mk' N)) = Nat.card ↥B := by
  have h1 := natCard_map_mk_mul (N := N) B
  have hBN : B ⊓ N = ⊥ := AscQuot.inf_eq_bot_of_isPGroup_of_odd N hB le_rfl (odd_natCard_inf hN B)
  have h2 : N ⊓ B = ⊥ := by rw [inf_comm]; exact hBN
  rw [h2] at h1
  simpa using h1

theorem secImage_ne_of_twin (hΩ : HypOmegaGen Ω) {K₁ K₂ P₁ P₂ : Subgroup G} (hK₁ : K₁ ∈ Ω)
    (hK₂ : K₂ ∈ Ω) (hP₁ : IsSylow2In P₁ K₁) (hP₂ : IsSylow2In P₂ K₂)
    (hP₁X : P₁ ≤ rLayerSub Ω A) (hP₂X : P₂ ≤ rLayerSub Ω A) {z : G}
    (hz₁ : IsUniqueInvolution K₁ z) (hz₂ : IsUniqueInvolution K₂ z) (hne : K₂ ≠ K₁)
    (hfix : ∀ c : G, Odd (orderOf c) → c ∈ Subgroup.centralizer ({z} : Set G) →
      conjSub c K₁ = K₁) :
    secImage (rLayerSub Ω A) P₂ ≠ secImage (rLayerSub Ω A) P₁ := by
  intro heq
  set X := rLayerSub Ω A with hXdef
  set N := classicalInvolutionOddCore ↥X with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hP₁2 : IsPGroup 2 ↥(P₁.subgroupOf X) := by
    have := hP₁.2.1
    exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hP₁X).symm
  have hP₂2 : IsPGroup 2 ↥(P₂.subgroupOf X) := by
    have := hP₂.2.1
    exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hP₂X).symm
  have hW2 : IsPGroup 2 ↥(secImage X P₁) := by
    unfold secImage
    exact hP₁2.map _
  obtain ⟨n, hn, V', hV'le, hV'2, hV'map⟩ := TwinEdge.Quot.exists_conj_lift (N := N) hN hW2
    (K := P₁.subgroupOf X) (J := P₂.subgroupOf X) le_rfl (by
      show secImage X P₁ ≤ secImage X P₂
      rw [heq])
  have hcardV : Nat.card ↥(V'.map (QuotientGroup.mk' N)) = Nat.card ↥V' :=
    natCard_map_mk_of_isPGroup hN hV'2
  have hcardJ : Nat.card ↥((P₂.subgroupOf X).map (QuotientGroup.mk' N)) =
      Nat.card ↥(P₂.subgroupOf X) := natCard_map_mk_of_isPGroup hN hP₂2
  have hWeq : (P₂.subgroupOf X).map (QuotientGroup.mk' N) = V'.map (QuotientGroup.mk' N) := by
    rw [hV'map]
    exact heq
  have hcard : Nat.card ↥V' = Nat.card ↥(P₂.subgroupOf X) := by
    rw [← hcardV, ← hcardJ, hWeq]
  have hVJ : V' = P₂.subgroupOf X :=
    Subgroup.eq_of_le_of_card_ge (fun x hx => (hV'le hx).2) hcard.ge
  have hJle : P₂.subgroupOf X ≤ conjSub n (P₁.subgroupOf X) :=
    hVJ ▸ (fun x hx => (hV'le hx).1)
  have hcn : conjSub (n : G) P₁ ≤ X := by
    have := conjSub_mono (n := (n : G)) hP₁X
    rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer n.2)] at this
  have h1 : P₂.subgroupOf X ≤ (conjSub (n : G) P₁).subgroupOf X := by
    have := hJle
    rwa [conjSub_subgroupOf X n P₁] at this
  have hP₂n : P₂ ≤ conjSub (n : G) P₁ := by
    intro x hx
    have hxX : x ∈ X := hP₂X hx
    have h3 := h1 (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hxX⟩ : ↥X) ∈ P₂.subgroupOf X)
    exact Subgroup.mem_subgroupOf.mp h3
  have hP₂K₁n : P₂ ≤ conjSub (n : G) K₁ := hP₂n.trans (conjSub_mono (n := (n : G)) hP₁.1)
  have h8 : 8 ≤ Nat.card ↥P₂ :=
    eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK₂ hP₂)
  have hKK : K₂ = conjSub (n : G) K₁ :=
    eq_of_le_of_le hΩ hK₂ (hΩ.conjInvariant (n : G) K₁ hK₁) hP₂.2.1 (by omega) hP₂.1 hP₂K₁n
  have hzn : (n : G) * z * (n : G)⁻¹ = z := by
    have h4 := hz₁.conj (n : G)
    have h5 : IsUniqueInvolution (conjSub (n : G) K₁) z := hKK ▸ hz₂
    exact h4.eq h5
  have hnC : (n : G) ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (n : G) * z = ((n : G) * z * (n : G)⁻¹) * (n : G) := by group
      _ = z * (n : G) := by rw [hzn]
  have hodd : Odd (orderOf (n : G)) := by
    have h6 : orderOf (⟨n, hn⟩ : ↥N) ∣ Nat.card N := orderOf_dvd_natCard _
    have h7 : orderOf (⟨n, hn⟩ : ↥N) = orderOf ((n : ↥X) : G) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    rw [h7] at h6
    exact hN.of_dvd_nat h6
  exact hne (hKK.trans (hfix (n : G) hodd hnC))

theorem secImage_conj_eq {B : Subgroup G} {n : ↥(rLayerSub Ω A)}
    (hn : n ∈ classicalInvolutionOddCore ↥(rLayerSub Ω A)) :
    secImage (rLayerSub Ω A) (conjSub (n : G) B) = secImage (rLayerSub Ω A) B := by
  unfold secImage
  rw [← conjSub_subgroupOf]
  exact OddQuot.map_conjSub_of_mem hn _

theorem perp_lift (hΩ : HypOmegaGen Ω) (hL1 : SecCoresTwoGroup Ω A) {K₁ K₂ P₁ P₂ : Subgroup G}
    (hK₁ : K₁ ∈ Ω) (hK₂ : K₂ ∈ Ω) (hP₁ : IsSylow2In P₁ K₁) (hP₂ : IsSylow2In P₂ K₂)
    (hP₁C : P₁ ≤ Subgroup.centralizer (A : Set G)) (hP₂C : P₂ ≤ Subgroup.centralizer (A : Set G))
    (hperp : KPerp Ω K₁ = {K₁, K₂}) :
    ∀ J ∈ sylFamA Ω A, J ≠ secImage (rLayerSub Ω A) P₁ →
      J ≤ Subgroup.normalizer ((secImage (rLayerSub Ω A) P₁ :
        Subgroup (SecQuot (rLayerSub Ω A))) : Set (SecQuot (rLayerSub Ω A))) →
      J = secImage (rLayerSub Ω A) P₂ := by
  intro J hJ hJne hJN
  set X := rLayerSub Ω A with hXdef
  set C := Subgroup.centralizer (A : Set G) with hCdef
  set N := classicalInvolutionOddCore ↥X with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  obtain ⟨R', hR', hR'C, rfl⟩ := hJ
  obtain ⟨J₀, hJ₀, hR'J₀⟩ := exists_isSylow2In_of_mem_RSet hR'
  have hJ₀C : ∃ P : Subgroup G, IsSylow2In P J₀ ∧ P ≤ C := ⟨R', hR'J₀, hR'C⟩
  have hK₁C : ∃ P : Subgroup G, IsSylow2In P K₁ ∧ P ≤ C := ⟨P₁, hP₁, hP₁C⟩
  have hK₂C : ∃ P : Subgroup G, IsSylow2In P K₂ ∧ P ≤ C := ⟨P₂, hP₂, hP₂C⟩
  have hR'X : R' ≤ X := by
    show R' ≤ rLayerSub Ω A
    unfold rLayerSub
    exact le_iSup₂_of_le R' hR' (le_iSup (fun _ : R' ≤ C => R') hR'C)
  have hcore₁X : tightCore (K₁ ⊓ C) ≤ X := core_le_rLayerSub hK₁ hK₁C
  have himg₁ : secImage X P₁ = secImage X (tightCore (K₁ ⊓ C)) :=
    secImage_syl_eq_core hK₁ hP₁ hP₁C (hL1 K₁ hK₁ hK₁C)
  have hUN : ∀ u ∈ R'.subgroupOf X, QuotientGroup.mk' N u ∈ Subgroup.normalizer
      ((((tightCore (K₁ ⊓ C)).subgroupOf X).map (QuotientGroup.mk' N) : Subgroup (↥X ⧸ N)) :
        Set (↥X ⧸ N)) := by
    intro u hu
    have hmem : QuotientGroup.mk' N u ∈ secImage X R' := Subgroup.mem_map_of_mem _ hu
    have h' := hJN hmem
    rw [himg₁] at h'
    exact h'
  have hR'2 : IsPGroup 2 ↥(R'.subgroupOf X) :=
    hR'J₀.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hR'X).symm
  obtain ⟨n, hn, hUn⟩ := TwinADescent2.exists_conj_normalizer_gen (N := N) (hypOmegaGen_coreFamX hΩ) hN
    (K := (tightCore (K₁ ⊓ C)).subgroupOf X)
    ⟨tightCore (K₁ ⊓ C), ⟨K₁, hK₁, hK₁C, rfl⟩, hcore₁X, rfl⟩ hR'2 hUN
  have hnC : (n : G) ∈ C := rLayerSub_le_centralizer_A Ω A n.2
  have hKn : conjSub (n : G) K₁ ∈ Ω := hΩ.conjInvariant (n : G) K₁ hK₁
  have hP₁nC : conjSub (n : G) P₁ ≤ C := by
    have := conjSub_mono (n := (n : G)) hP₁C
    rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hnC)] at this
  have hP₂nC : conjSub (n : G) P₂ ≤ C := by
    have := conjSub_mono (n := (n : G)) hP₂C
    rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hnC)] at this
  have hKnC : ∃ P : Subgroup G, IsSylow2In P (conjSub (n : G) K₁) ∧ P ≤ C :=
    ⟨conjSub (n : G) P₁, hP₁.conj _, hP₁nC⟩
  have hK₂n : conjSub (n : G) K₂ ∈ Ω := hΩ.conjInvariant (n : G) K₂ hK₂
  have hK₂nC : ∃ P : Subgroup G, IsSylow2In P (conjSub (n : G) K₂) ∧ P ≤ C :=
    ⟨conjSub (n : G) P₂, hP₂.conj _, hP₂nC⟩
  have e1 : conjSub (n : G) (tightCore (K₁ ⊓ C)) = tightCore (conjSub (n : G) K₁ ⊓ C) := by
    rw [conjSub_tightCore, conjSub_inf, conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hnC)]
  have hcoreX : tightCore (conjSub (n : G) K₁ ⊓ C) ≤ X := core_le_rLayerSub hKn hKnC
  rw [conjSub_subgroupOf X n, e1] at hUn
  have hR'N : R' ≤ Subgroup.normalizer
      ((tightCore (conjSub (n : G) K₁ ⊓ C) : Subgroup G) : Set G) := by
    intro x hx
    exact (mem_normalizer_subgroupOf_iff hcoreX).mpr (hUn (Subgroup.mem_subgroupOf.mpr hx :
      (⟨x, hR'X hx⟩ : ↥X) ∈ R'.subgroupOf X))
  obtain ⟨z, hz, hzcore, -, -⟩ := TwinEdge.Fam.member_data hΩ hK₁ hP₁ hP₁C
  have hzn : IsUniqueInvolution (conjSub (n : G) K₁) ((n : G) * z * (n : G)⁻¹) := hz.conj (n : G)
  have hzncore : (n : G) * z * (n : G)⁻¹ ∈ tightCore (conjSub (n : G) K₁ ⊓ C) := by
    rw [← e1]
    exact conj_mem_conjSub hzcore
  have hzn' : IsUniqueInvolution (tightCore (conjSub (n : G) K₁ ⊓ C)) ((n : G) * z * (n : G)⁻¹) :=
    isUniqueInvolution_mono hzn ((tightCore_le _).trans inf_le_left) hzncore
  have hR'z : R' ≤ Subgroup.centralizer ({(n : G) * z * (n : G)⁻¹} : Set G) :=
    Sec6Gen.le_centralizer_of_le_normalizer' hzn' hR'N
  have hmem₂ : ∀ {K P : Subgroup G}, K ∈ Ω → IsSylow2In P K → P ≤ C →
      secImage X P = secImage X (tightCore (K ⊓ C)) := fun hK hP hPC =>
    secImage_syl_eq_core hK hP hPC (hL1 _ hK ⟨_, hP, hPC⟩)
  by_cases hJK : J₀ = conjSub (n : G) K₁
  · exfalso
    apply hJne
    subst hJK
    rw [hmem₂ hJ₀ hR'J₀ hR'C, ← hmem₂ hJ₀ (hP₁.conj (n : G)) hP₁nC, secImage_conj_eq hn]
  · have hR'Nn : R' ≤ Subgroup.normalizer ((conjSub (n : G) K₁ : Subgroup G) : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hKn hJ₀ (Ne.symm hJK) hzn hR'J₀.1 hR'J₀.2.1
        (by have := eight_le_of_mem_RSet hΩ hR'; omega) hR'z
    have hnbr : J₀ ∈ omegaNbr Ω (conjSub (n : G) K₁) := ⟨hJ₀, hJK, R', hR', hR'J₀.1, hR'Nn⟩
    have hperpn := T7L.kPerp_conj_pair hΩ.conjInvariant hperp (n : G)
    have hJ₀perp : J₀ ∈ KPerp Ω (conjSub (n : G) K₁) := Or.inr hnbr
    rw [hperpn] at hJ₀perp
    rcases hJ₀perp with h | h
    · exact absurd h hJK
    · rw [Set.mem_singleton_iff] at h
      subst h
      rw [hmem₂ hJ₀ hR'J₀ hR'C, ← hmem₂ hJ₀ (hP₂.conj (n : G)) hP₂nC, secImage_conj_eq hn]

theorem le_rLayerSub_of_mem {R' : Subgroup G} (hR' : R' ∈ RSet Ω)
    (hRC : R' ≤ Subgroup.centralizer (A : Set G)) : R' ≤ rLayerSub Ω A := by
  unfold rLayerSub
  exact le_iSup₂_of_le R' hR' (le_iSup (fun _ : R' ≤ Subgroup.centralizer (A : Set G) => R') hRC)

end Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
