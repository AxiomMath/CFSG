module

public import CFSG.GH74.GLS.Prop27.Balance
public import CFSG.GH74.GLS.C3.Layer1.Back91Setup
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.GH74.GLS.C3.Layer1.Iv102

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.E2 CFSG.Blueprint Subgroup Assembly.LowTwoRank
  CFSG.Assembly.Dichotomy CFSG.GH74.GLS.Prop27 CFSG.GH74.L5U5 CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

theorem shapes7_of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L) (h : Shapes7 K) :
    Shapes7 L := by
  rcases h with ⟨hz, h⟩ | h | h
  · refine Or.inl ⟨?_, ?_⟩
    · rw [← Subgroup.map_center_eq e, hz, Subgroup.map_bot]
    · rcases h with h | h | h | h | h
      · exact Or.inl (lieModel_of_mulEquiv e h)
      · exact Or.inr (Or.inl (lieModel_of_mulEquiv e h))
      · exact Or.inr (Or.inr (Or.inl (lieModel_of_mulEquiv e h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (lieModel_of_mulEquiv e h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (isSporadic_of_mulEquiv e h))))
  · exact Or.inr (Or.inl (Shape2M12.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Shape2Sz8.of_mulEquiv e h))

section Image

variable {G : Type} [Group G] [Finite G]

theorem map_pPrimeCoreOf_le_involutionOddCore {x y : G} (hy : orderOf y = 2)
    (hxy : y ∈ centralizer ({x} : Set G)) {w : G} (hwC : w ∈ centralizer ({x} : Set G))
    (hw : w ∈ pPrimeCoreOf 2 (centralizer ({x, y} : Set G))) :
    QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G))) ⟨w, hwC⟩ ∈
      involutionOddCore (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G))) ⟨y, hxy⟩) := by
  classical
  set H : Subgroup G := centralizer ({x} : Set G) with hH
  set O : Subgroup ↥H := pPrimeCore 2 ↥H with hO
  have hOn : O.Normal := pPrimeCore_normal
  set π : ↥H →* CentralizerBar x := QuotientGroup.mk' O with hπ
  set a' : ↥H := ⟨y, hxy⟩ with ha'def
  set v : CentralizerBar x := π a' with hvdef
  have hOcop : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card
  have ha'2 : orderOf a' = 2 := by rw [← Subgroup.orderOf_coe]; exact hy
  have hfact : Fact (IsPGroup 2 ↥(zpowers a')) :=
    ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha'2]; norm_num)⟩
  have hcen : centralizer (((zpowers a').map π : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O)) =
      (centralizer ((zpowers a' : Subgroup ↥H) : Set ↥H)).map π :=
    centralizer_map_quotient_eq_map_centralizer 2 (zpowers a') O hOn hOcop
  have hmapz : (zpowers a').map π = zpowers v := MonoidHom.map_zpowers π a'
  rw [hmapz] at hcen
  have hcenv : centralizer ({v} : Set (CentralizerBar x)) =
      (centralizer ({a'} : Set ↥H)).map π := by
    have h1 : centralizer ((zpowers v : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) =
        centralizer ({v} : Set (CentralizerBar x)) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h2 : centralizer ((zpowers a' : Subgroup ↥H) : Set ↥H) =
        centralizer ({a'} : Set ↥H) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [← h1, hcen, h2]
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = pPrimeCoreOf 2 (centralizer ({x, y} : Set G)) := ⟨_, rfl⟩
  have hDxy : D ≤ centralizer ({x, y} : Set G) := hD ▸ TwoThin.pPrimeCoreOf_le _
  have hDx : ∀ d ∈ D, d * x = x * d := fun d hd =>
    ((Subgroup.mem_centralizer_iff.mp (hDxy hd)) x (by simp)).symm
  have hDy : ∀ d ∈ D, d * y = y * d := fun d hd =>
    ((Subgroup.mem_centralizer_iff.mp (hDxy hd)) y (by simp)).symm
  have hDH : D ≤ H := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hDx d hd)
  obtain ⟨W, hW⟩ : ∃ W : Subgroup (CentralizerBar x), W = (D.subgroupOf H).map π := ⟨_, rfl⟩
  have hWC : W ≤ centralizer ({v} : Set (CentralizerBar x)) := by
    rw [hW]
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hda : (d : G) * y = y * d := hDy d (Subgroup.mem_subgroupOf.mp hd)
    rw [hvdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hda
  have hWn : ∀ c ∈ centralizer ({v} : Set (CentralizerBar x)), ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    have hcv : c ∈ (centralizer ({a'} : Set ↥H)).map π := by
      rw [← hcenv]; exact hc
    obtain ⟨c₀, hc₀, rfl⟩ := hcv
    rw [hW] at hw ⊢
    obtain ⟨d, hd, rfl⟩ := hw
    refine ⟨c₀ * d * c₀⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have hc₀a : (c₀ : G) * y = y * c₀ := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc₀
      exact congrArg Subtype.val this
    have hc₀x : (c₀ : G) ∈ centralizer ({x} : Set G) := c₀.2
    have hc₀xy : (c₀ : G) ∈ centralizer ({x, y} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rcases hh with rfl | hh
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hc₀x).symm
      · rw [Set.mem_singleton_iff.mp hh]; exact hc₀a.symm
    have hd1 : (d : G) ∈ pPrimeCoreOf 2 (centralizer ({x, y} : Set G)) := by
      rw [← hD]; exact Subgroup.mem_subgroupOf.mp hd
    show c₀ * d * c₀⁻¹ ∈ D.subgroupOf H
    rw [Subgroup.mem_subgroupOf]
    have hmem : (c₀ : G) * d * (c₀ : G)⁻¹ ∈ pPrimeCoreOf 2 (centralizer ({x, y} : Set G)) :=
      TwoThin.pPrimeCoreOf_normalized _ hc₀xy hd1
    rw [hD]
    exact hmem
  have hWodd : Odd (Nat.card W) := by
    have h1 : Nat.card W ∣ Nat.card (D.subgroupOf H) := by
      rw [hW]; exact Subgroup.card_map_dvd _ π
    have h2 : Nat.card (D.subgroupOf H) = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv
    have h3 : Odd (Nat.card D) := hD ▸ TwoThin.card_pPrimeCoreOf_odd _
    exact Odd.of_dvd_nat (h2 ▸ h3) h1
  have hWle : W ≤ involutionOddCore v := le_involutionOddCore_of_normalized hWC hWn hWodd
  apply hWle
  rw [hW]
  exact ⟨⟨w, hwC⟩, Subgroup.mem_subgroupOf.mpr (by rw [hD]; exact hw), rfl⟩

end Image

section Pullback

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizerSection_of_image {x : G} {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) {w : G} (hw : w ∈ centralizer ({x} : Set G))
    (hcomm : ∀ k ∈ bar x K, sbar w hw * k = k * sbar w hw) :
    w ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
  classical
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hKC : K ≤ C := hK.1
  have hwN : w ∈ normalizer (K : Set G) := by
    have hL : CFSG.IsPComponent 2 (K.subgroupOf C) := hK.2
    have hcen : sbar w hw ∈ centralizer ((bar x K : Subgroup _) : Set _) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => (hcomm k hk).symm
    have hnorm : barMk ↥C ⟨w, hw⟩ ∈
        normalizer (((K.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) :
          Subgroup _) : Set _) :=
      Subgroup.centralizer_le_normalizer _ hcen
    have hn' := CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hL hnorm
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have hkC : k ∈ C := hKC hk
      have := (Subgroup.mem_normalizer_iff.mp hn' ⟨k, hkC⟩).mp (Subgroup.mem_subgroupOf.mpr hk)
      exact Subgroup.mem_subgroupOf.mp this
    · intro hk
      have hkC : k ∈ C := by
        have h1 : w * k * w⁻¹ ∈ C := hKC hk
        have := C.mul_mem (C.mul_mem (C.inv_mem hw) h1) hw
        simpa [mul_assoc] using this
      have := (Subgroup.mem_normalizer_iff.mp hn' ⟨k, hkC⟩).mpr (Subgroup.mem_subgroupOf.mpr hk)
      exact Subgroup.mem_subgroupOf.mp this
  have hnormK : ∀ m ∈ normalizer (K : Set G), ∀ l ∈ K, m * l * m⁻¹ ∈ K :=
    fun m hm l hl => (Subgroup.mem_normalizer_iff.mp hm l).mp hl
  refine ⟨hwN, TwoThin.mem_normalizer_pPrimeCoreOf hwN, fun k hk => ?_⟩
  have hkC : k ∈ C := hKC hk
  have hκK : ⁅k, w⁆ ∈ K := by
    have h1 : w * k⁻¹ * w⁻¹ ∈ K := hnormK w hwN k⁻¹ (K.inv_mem hk)
    have h2 : ⁅k, w⁆ = k * (w * k⁻¹ * w⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h2]
    exact K.mul_mem hk h1
  have hκO : ⁅k, w⁆ ∈ pPrimeCoreOf 2 C := by
    have hkb : barMk ↥C ⟨k, hkC⟩ ∈ bar x K :=
      Subgroup.mem_map.mpr ⟨⟨k, hkC⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hc := hcomm _ hkb
    have h1 : barMk ↥C ⁅(⟨k, hkC⟩ : ↥C), ⟨w, hw⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 hc.symm
    have h2 : (⁅(⟨k, hkC⟩ : ↥C), ⟨w, hw⟩⁆ : ↥C) ∈ pPrimeCore 2 ↥C :=
      (QuotientGroup.eq_one_iff _).1 h1
    have hκC : ⁅k, w⁆ ∈ C := hKC hκK
    have hκeq : (⁅(⟨k, hkC⟩ : ↥C), ⟨w, hw⟩⁆ : ↥C) = ⟨⁅k, w⁆, hκC⟩ := Subtype.ext rfl
    exact C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hκC, hκeq ▸ h2⟩
  have hN1 : K ⊓ pPrimeCoreOf 2 C ≤ pPrimeCoreOf 2 K := by
    refine C3.Layer1.Back.Setup91.le_pPrimeCoreOf_of_normalized inf_le_left
      (fun c hc n hn => ?_) ?_
    · exact ⟨K.mul_mem (K.mul_mem hc hn.1) (K.inv_mem hc),
        TwoThin.pPrimeCoreOf_normalized C (hKC hc) hn.2⟩
    · exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd C) (Subgroup.card_dvd_of_le inf_le_right)
  exact hN1 ⟨hκK, hκO⟩

end Pullback

end CFSG.GH74.GLS.C3.Layer1.Iv102
