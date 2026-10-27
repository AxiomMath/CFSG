module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUSetup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUDiag
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKPump
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeOdd

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped Pointwise

namespace HeUM

theorem mem_four {X : Type} [Group X] {u₁ u₂ u : X} (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1)
    (hc : u₁ * u₂ = u₂ * u₁) (hu : u ∈ zpowers u₁ ⊔ zpowers u₂) (hu1 : u ≠ 1) :
    u = u₁ ∨ u = u₂ ∨ u = u₁ * u₂ := by
  have hle : zpowers u₁ ≤ normalizer (zpowers u₂ : Set X) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      rw [(Commute.zpow_right (show Commute u₁ u₂ from hc) k).eq, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers u₂) k
    · intro hy
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
      have h : y = u₂ ^ k := by
        calc y = u₁⁻¹ * (u₁ * y * u₁⁻¹) * u₁ := by group
          _ = u₁⁻¹ * u₂ ^ k * u₁ := by rw [hk]
          _ = u₂ ^ k := by
            rw [(Commute.zpow_right (show Commute u₁⁻¹ u₂ from
              (Commute.inv_left (show Commute u₁ u₂ from hc))) k).eq, inv_mul_cancel_right]
      rw [h]
      exact zpow_mem (mem_zpowers u₂) k
  have hu' : u ∈ (zpowers u₁ : Set X) * (zpowers u₂ : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hu
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hu'
  rcases OrbitFixedComponent.eq_one_or_eq_of_mem_zpowers h₁ hx with rfl | rfl <;>
    rcases OrbitFixedComponent.eq_one_or_eq_of_mem_zpowers h₂ hy with rfl | rfl
  · exact absurd (one_mul 1) hu1
  · exact Or.inr (Or.inl (one_mul _))
  · exact Or.inl (mul_one _)
  · exact Or.inr (Or.inr rfl)

end HeUM

open HeUM in
theorem heldUCentralStep_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hD : L34RankTwoCentralFixedInput) (hDiag : HeldUDiagonalStep) : HeldUCentralStep := by
  intro X _ _ L hset hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimp, hnab, hK, -, -, ⟨a, ha, hLa, hLc⟩, ⟨e⟩⟩ := id hset
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hZ : ∀ x : X, x ≠ 1 → centralizer ({x} : Set X) ≠ ⊤ := by
    intro x hx htop
    have hcen : center X = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
      · exact h
      · exfalso
        obtain ⟨y, z, hyz⟩ := hnab
        have hy : y ∈ center X := h ▸ mem_top y
        exact hyz (mem_center_iff.mp hy z).symm
    have hxc : x ∈ center X := mem_center_iff.mpr fun g =>
      (mem_centralizer_singleton_iff.mp (htop ▸ mem_top g : g ∈ centralizer ({x} : Set X)))
    rw [hcen, mem_bot] at hxc
    exact hx hxc
  have haL : a ∉ L := by
    intro haL
    obtain ⟨hQs, b, c, hbc⟩ := HeOdd.simple_nonab_of_held e
    have hcQ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥L ⧸ pPrimeCore 2 ↥L)) with h | h
      · exact h
      · exfalso
        have hb : b ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by rw [h]; exact mem_top b
        exact hbc ((mem_center_iff.mp hb) c).symm
    have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨a, haL⟩ ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hLa l.2))
    rw [hcQ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    have hodd : Odd (Nat.card (pPrimeCore 2 ↥L)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have h2 : orderOf (⟨⟨a, haL⟩, hmem⟩ : pPrimeCore 2 ↥L) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, ha]
    have h3 := orderOf_dvd_natCard (⟨⟨a, haL⟩, hmem⟩ : pPrimeCore 2 ↥L)
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)
  obtain ⟨u₁, hu₁L, u₂, hu₂L, h₁, h₂, hn₁, hn₂, hne, hc, hall⟩ :=
    HeU.exists_four_layers_in hLa hLc e
  set U := zpowers u₁ ⊔ zpowers u₂ with hUdef
  have hUe : IsElemTwo U := (isElemTwo_zpowers h₁).sup (isElemTwo_zpowers h₂) (by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute u₁ u₂ from hc) i j).eq)
  have hU4 : Nat.card U = 4 := by
    have hge := four_le_card_sup_zpowers h₁ h₂ hn₁ hn₂ hne hc
    have hu₁N : u₁ ∈ normalizer (zpowers u₂ : Set X) := by
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        rw [(Commute.zpow_right (show Commute u₁ u₂ from hc) k).eq, mul_inv_cancel_right]
        exact zpow_mem (mem_zpowers u₂) k
      · intro hy
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
        have h : y = u₂ ^ k := by
          calc y = u₁⁻¹ * (u₁ * y * u₁⁻¹) * u₁ := by group
            _ = u₁⁻¹ * u₂ ^ k * u₁ := by rw [hk]
            _ = u₂ ^ k := by
              rw [(Commute.zpow_right (show Commute u₁⁻¹ u₂ from
                (Commute.inv_left (show Commute u₁ u₂ from hc))) k).eq, inv_mul_cancel_right]
        rw [h]
        exact zpow_mem (mem_zpowers u₂) k
    have hle := card_zpowers_sup_le h₁ hu₁N
    have h2 : Nat.card (zpowers u₂) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact h₂) hn₂
    rw [hUdef]
    omega
  have hUf : IsFourGroup U := HeUV.isFourGroup_of_card hUe hU4
  have hUL : U ≤ L := sup_le (zpowers_le.mpr hu₁L) (zpowers_le.mpr hu₂L)
  have hUp : IsPGroup 2 U := hUe.isPGroup
  refine ⟨U, hUL, hUf, fun u hu hu1 => ?_⟩
  obtain ⟨T, hTL, hTau, hTp, htype, hz₁, hz₂⟩ := hall u (mem_four h₁ h₂ hc hu hu1)
  have hUT : U ≤ (Open.fusionZStar ↥T).map T.subtype :=
    sup_le (zpowers_le.mpr hz₁) (zpowers_le.mpr hz₂)
  have hUT' : U ≤ T := fun x hx => by
    obtain ⟨t, -, rfl⟩ := hUT hx
    exact t.2
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hUe.2 u hu) hu1
  have hau : a * u = u * a := (mem_centralizer_singleton_iff.mp (hLa (hUL hu))).symm
  obtain ⟨M, hMu, hMp, hTK, hTKp, hle, hswap, heq⟩ :=
    HeK.exists_pump hS hK ha hau (hZ u hu1) hTau hTp
  by_cases hMa : M = conjugate M a
  ·
    have hMa' : conjugate M a = M := hMa.symm
    rw [hMa', sup_idem] at hTK hTKp
    have hidx := HeK.index_eq_of_mem hD hK ha hu2 (hZ u hu1) hMu hMp hMa' hTK hTKp hle
      (hUT' hu) htype hz₁ hz₂ h₁ h₂ hn₁ hn₂ hne hc
    have hTO := heq hidx hMa
    obtain ⟨hcO, hcU⟩ := HeUV.central_of_invariant hS hUO hheld hK hZ ha hLa haL hW hUL hUe
      (by omega) hu hu2 (hTau.trans inf_le_left) hUT hMu hMp hMa' (hTK.trans inf_le_left) hTO
    have hMc := HeUC.isComponent_of_central hMu hMp hcO
    exact HeUC.le_pCore_map hMu hMc hMu hMc hUp
      (le_sup_of_le_left (hUT'.trans (hTK.trans inf_le_left))) hcU hcU
  ·
    have hfix := hswap hMa
    have hne' : conjugate M a ≠ M := fun h => hMa h.symm
    obtain ⟨hMau, hMap⟩ := UGSChain.conjugate_isPComponent_centralizer hau hMu hMp
    have hMM : conjugate (conjugate M a) a = M :=
      UnbalancedLayer.conjugate_conjugate_self_of_mul_self haa
    have hcO := hDiag X L hset hW a u U T M ha hLa hLc hUL hUf hu hu1 hTL hTau hTp htype hUT
      hMu hMp hne' hfix
    have hcO' := hDiag X L hset hW a u U T (conjugate M a) ha hLa hLc hUL hUf hu hu1 hTL hTau
      hTp htype hUT hMau hMap (by rw [hMM]; exact hne'.symm) (by rw [hMM, sup_comm]; exact hfix)
    have hMc := HeUC.isComponent_of_central hMu hMp hcO
    have hMac := HeUC.isComponent_of_central hMau hMap hcO'
    have hTK' : T ≤ M ⊔ conjugate M a := hTK.trans inf_le_left
    exact HeUC.le_pCore_map hMu hMc hMau hMac hUp (hUT'.trans hTK')
      (fun v hv => HeUD.commute_of_diagonal haa hMu hMc hMau hMac hne' hfix (hUT hv))
      (fun v hv => HeUD.commute_of_diagonal' haa hMu hMc hMau hMac hne' hfix (hUT hv))

end CFSG.ComponentClassification.GrSLit
