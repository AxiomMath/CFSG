module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinF1

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

@[expose] def RadicalCharacteristicCase3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G) (z : G),
    UnconstrainedSetting G T M → Tuple25 T M H S z →
      ∀ K : Subgroup G, IsComponentIn K H → ¬ fusionIsBenderGroup ↥K → ComponentList M S z K →
        InCase3 M z K →
        ∀ R : Subgroup G, R ≤ conjJoin H K → IsPGroup 2 R → radicalOf M H K ≤ R →
          Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (radicalOf M H K : Set G)

theorem radicalCharacteristic_of_case3 (h252 : Lemma252) (h3 : RadicalCharacteristicCase3) :
    RadicalCharacteristic := by
  intro G _ _ T M H S z hs ht K hK hBe hcl R hRD hR2 hle
  have hinn : ∀ L : Subgroup G, IsComponentIn L H → Ch1.InducesInner z L := fun L hL =>
    (h252 G T M H S z hs ht L hL).2.1
  rcases sylowRadical_or_case3 ht hK hBe hcl with hsyl | hc3
  · have hS := isSylowTwoOf_radicalOf hs ht hinn hK hsyl
    have hR : R = radicalOf M H K := hS.eq_of_le hle hRD hR2
    rw [hR]
  · exact h3 G T M H S z hs ht K hK hBe hcl hc3 R hRD hR2 hle

@[expose] def Q8Characteristic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (t : G),
    (StatedClassicalModel ↥K .PSL 3 3 1 ∨
      Nonempty (↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) → t ∈ K →
    (∀ x ∈ K, (t * t) * x = x * (t * t)) →
    ∀ R : Subgroup G, R ≤ K → IsPGroup 2 ↥R →
      pCoreOf 2 (K ⊓ Subgroup.centralizer ({t} : Set G)) ≤ R →
        Subgroup.normalizer (R : Set G) ≤
          Subgroup.normalizer (pCoreOf 2 (K ⊓ Subgroup.centralizer ({t} : Set G)) : Set G)

section Case3

variable {G : Type} [Group G]

theorem sq_central_of_projection {z zL : G} {K : Subgroup G} (hzz : z * z = 1) (hzLK : zL ∈ K)
    (hproj : ∀ x ∈ K, z⁻¹ * x * z = zL⁻¹ * x * zL) :
    ∀ x ∈ K, (zL * zL) * x = x * (zL * zL) := by
  intro x hx
  have hx' : zL⁻¹ * x * zL ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hzLK) hx) hzLK
  have h1 := hproj x hx
  have h2 := hproj _ hx'
  have h3 : z⁻¹ * (z⁻¹ * x * z) * z = x := by
    have hinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    rw [hinv]
    calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
      _ = x := by rw [hzz]; group
  have h4 : x = zL⁻¹ * (zL⁻¹ * x * zL) * zL :=
    calc x = z⁻¹ * (z⁻¹ * x * z) * z := h3.symm
      _ = z⁻¹ * (zL⁻¹ * x * zL) * z := by rw [h1]
      _ = zL⁻¹ * (zL⁻¹ * x * zL) * zL := h2
  calc (zL * zL) * x = (zL * zL) * (zL⁻¹ * (zL⁻¹ * x * zL) * zL) := by rw [← h4]
    _ = x * (zL * zL) := by group

end Case3

theorem radicalCharacteristicCase3_of_q8 (hNP : NoCommutingConjugate)
    (hQ8 : Q8Characteristic) : RadicalCharacteristicCase3 := by
  intro G _ _ T M H S z hs ht K hK hBe hcl hc3 R hRD hR2 hle
  have hall := hNP G T M H S z hs ht K hK hBe hcl (Or.inr hc3)
  have hD : conjJoin H K = K := by
    refine le_antisymm (iSup_le fun g => ?_) (le_conjJoin_self H K)
    have := hall (g : G)⁻¹ (H.inv_mem g.2)
    simp only [CFSG.conjugate, inv_inv] at this
    exact this.le
  obtain ⟨hmodel, zL, ⟨hzLK, hproj⟩, hMK⟩ := hc3
  have hzz : z * z = 1 := by rw [← pow_two]; exact ht.z_sq
  have hrad : radicalOf M H K = pCoreOf 2 (K ⊓ Subgroup.centralizer ({zL} : Set G)) := by
    unfold radicalOf
    rw [hD, hMK]
  rw [hD] at hRD
  rw [hrad] at hle ⊢
  exact hQ8 G K zL hmodel hzLK (sq_central_of_projection hzz hzLK hproj) R hRD hR2 hle

theorem radicalCharacteristic_of_q8 (h252 : Lemma252) (hNP : NoCommutingConjugate)
    (hQ8 : Q8Characteristic) : RadicalCharacteristic :=
  radicalCharacteristic_of_case3 h252 (radicalCharacteristicCase3_of_q8 hNP hQ8)

end CFSG.QuasithinUnique.Fin253
