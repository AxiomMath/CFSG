module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMCMain

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeKMU

private theorem two_mul_card_le_of_lt {X : Type} [Group X] [Finite X] {H H' : Subgroup X}
    (hle : H ≤ H') {x : X} (hx : x ∈ H') (hxH : x ∉ H) : 2 * Nat.card H ≤ Nat.card H' := by
  have hne : H.subgroupOf H' ≠ ⊤ := fun h => hxH (by
    have hmem : (⟨x, hx⟩ : H') ∈ H.subgroupOf H' := h ▸ mem_top _
    exact hmem)
  have hidx : (H.subgroupOf H').index ≠ 1 := fun h => hne (index_eq_one.mp h)
  have hidx0 : (H.subgroupOf H').index ≠ 0 := index_ne_zero_of_finite
  have h := (H.subgroupOf H').card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at h
  have h2 : 2 ≤ (H.subgroupOf H').index := by omega
  calc 2 * Nat.card H ≤ (H.subgroupOf H').index * Nat.card H := Nat.mul_le_mul_right _ h2
    _ = Nat.card H' := by rw [mul_comm, h]

theorem exists_elem_eight_wGroup
    {X : Type} [Group X] [Finite X] {L : Subgroup X} (hset : HeldEndSetting X L) {a u : X}
    {M : Subgroup X} (ha : orderOf a = 2) (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X)))) (hu : HeldTwoA L u)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hne : conjugate M a ≠ M) (hfix : gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u)
    (hc : ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) {w : X}
    (hw : orderOf w = 2) (hMw : M ≤ centralizer ({w} : Set X)) :
    ∃ E : Subgroup X, E ≤ centralizer ({w} : Set X) ∧ (∀ e ∈ E, ∀ m ∈ M, e * m = m * e) ∧
      IsElemTwo E ∧ 8 ≤ Nat.card E ∧ wGroup E = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHS, hW, -, ⟨e⟩, -⟩ := id hset
  obtain ⟨-, -, -, -, hLB, -, ⟨e₀⟩⟩ := id hHS
  set Cu := centralizer ({u} : Set X) with hCu
  set N := conjugate M a with hN
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hu2 : orderOf u = 2 := hu.2.1
  have huu : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    norm_num at hu2
  have haCu : a ∈ Cu := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hLa hu.1)).symm
  have hMc : IsComponent (M.subgroupOf Cu) := HeUC.isComponent_of_central hMu hMp hc
  have hNc : IsComponent (N.subgroupOf Cu) := HeKP.isComponent_conjugate hMc haCu
  have hNu : N ≤ Cu := by
    intro x hx
    rw [hN, HeKP.mem_conjugate] at hx
    have h := mul_mem (mul_mem (inv_mem haCu) (hMu hx)) haCu
    rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at h
  have hMN := HeKP.commute_of_components hMu hNu hMc hNc (Ne.symm hne)
  have hNM : ∀ x ∈ N, ∀ y ∈ M, x * y = y * x := fun x hx y hy => (hMN y hy x hx).symm
  have hMq : IsQuasisimple ↥M :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hMu) hMc.1
  have hNq : IsQuasisimple ↥N :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hNu) hNc.1
  have haM : ∀ y ∈ M, a * y * a⁻¹ ∈ N := fun y hy => by
    rw [hN, HeKP.mem_conjugate,
      show a * (a * y * a⁻¹) * a⁻¹ = (a * a) * y * (a * a)⁻¹ by group, haa]
    simpa using hy
  have haN : ∀ x ∈ N, a * x * a⁻¹ ∈ M := fun x hx => HeKP.mem_conjugate.mp hx
  set K := gsFixedLayer L u with hKdef
  have hKL : K ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  have hKau : K ≤ centralizer ({a} : Set X) ⊓ Cu :=
    le_inf (hKL.trans hLa) ((gsFixedLayer_le_inf L u).trans inf_le_right)
  obtain ⟨B₈, hBK, hBe, hB8, V, hVB, hV4, hVZ⟩ := HeDE.exists_eight_le_center hLa e₀ hu.1 huu
    hu1 hKL hKau (HeDG.isPComponent_gsFixedLayer_inf e hLa hLc hu)
  have hfix' : gsFixedLayer (N ⊔ M) a = K := by rw [sup_comm]; exact hfix
  have hGW : GWTwoBalanced X := gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hLB
  have hWB : wGroup B₈ = ⊥ :=
    HeUV.wGroup_eq_bot_of_le hW hBe (hBK.trans (hKL.trans le_normalizer))
  have hBr : IsAbelianTwoOfRank 3 B₈ := hBe.isAbelianTwoOfRank (by rw [hB8])
  by_cases hwM : w ∈ M
  ·
    obtain ⟨E, hEe, hE8, hEN, hEM, hEB⟩ := HeDG.exists_elem_eight haa hMN haM haN hMq
      (by rw [hfix]; exact hBK) hBe hB8 hVB hV4 (by rw [hfix]; exact hVZ)
    refine ⟨E, fun x hx => mem_centralizer_singleton_iff.mpr (hMN w hwM x (hEN hx)).symm, hEM,
      hEe, hE8, ?_⟩
    rw [wGroup_eq_of_commute hGW (hEe.isAbelianTwoOfRank hE8) hBr
      (fun x hx y hy => (hEB y hy x hx).symm), hWB]
  ·
    obtain ⟨-, z₁, hz₁, z₂, hz₂, hs₁, hs₂, hn₁, hn₂, hz, hcz⟩ :=
      HeKMC.type_and_pair hset ha hLa hLc hu hMu hMp hne hfix hc
    obtain ⟨E₁, hE₁e, hE₁8, hE₁M, -, hE₁B⟩ := HeDG.exists_elem_eight haa hNM haN haM hNq
      (by rw [hfix']; exact hBK) hBe hB8 hVB hV4 (by rw [hfix']; exact hVZ)
    have hOM : pPrimeCore 2 ↥M ≤ center ↥M := fun y hy => mem_center_iff.mpr fun g =>
      Subtype.ext (hc _ (mem_map_of_mem _ hy) g g.2).symm
    have hZM : Open.fusionZStar ↥M = center ↥M :=
      GrS5.fusionZStar_eq_center_of_le hMq.1.commutator_eq_top hOM
    have hzC : ∀ z ∈ (Open.fusionZStar ↥M).map M.subtype, z ∈ centralizer (M : Set X) := by
      rw [hZM]
      rintro _ ⟨y, hy, rfl⟩
      exact mem_centralizer_iff.mpr fun m hm =>
        congrArg Subtype.val (mem_center_iff.mp hy ⟨m, hm⟩)
    have hz₁M : z₁ ∈ M := map_subtype_le _ hz₁
    have hz₂M : z₂ ∈ M := map_subtype_le _ hz₂
    have hwC : w ∈ centralizer (M : Set X) :=
      mem_centralizer_iff.mpr fun m hm => mem_centralizer_singleton_iff.mp (hMw hm)
    have hz₁2 : orderOf z₁ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs₁) hn₁
    have hww : w * w = 1 := by rw [← pow_two, ← hw, pow_orderOf_eq_one]
    set F := zpowers z₁ ⊔ zpowers z₂ with hFdef
    set E := F ⊔ zpowers w with hEdef
    have hFM : F ≤ M := sup_le (zpowers_le.mpr hz₁M) (zpowers_le.mpr hz₂M)
    have hFe : IsElemTwo F := (isElemTwo_zpowers hs₁).sup (isElemTwo_zpowers hs₂) (by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow (show Commute z₁ z₂ from hcz) i j).eq)
    have hEe : IsElemTwo E := hFe.sup (isElemTwo_zpowers hww) (by
      intro x hx y hy
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute x w from
        mem_centralizer_singleton_iff.mp (hMw (hFM hx))) j).eq)
    have hEC : E ≤ centralizer (M : Set X) :=
      sup_le (sup_le (zpowers_le.mpr (hzC _ hz₁)) (zpowers_le.mpr (hzC _ hz₂)))
        (zpowers_le.mpr hwC)
    have h2 : Nat.card (zpowers z₁) = 2 := by rw [Nat.card_zpowers, hz₁2]
    have hz₂n : z₂ ∉ zpowers z₁ := by
      rw [LocalB.mem_zpowers_iff_of_involution z₁ z₂ hz₁2]
      rintro (h | h)
      · exact hn₂ h
      · exact hz h.symm
    have hF4 : 4 ≤ Nat.card F := by
      have h : 2 * Nat.card (zpowers z₁) ≤ Nat.card F :=
        two_mul_card_le_of_lt le_sup_left (mem_sup_right (mem_zpowers z₂)) hz₂n
      omega
    have hE8 : 8 ≤ Nat.card E := by
      have h : 2 * Nat.card F ≤ Nat.card E :=
        two_mul_card_le_of_lt le_sup_left (mem_sup_right (mem_zpowers w)) fun h => hwM (hFM h)
      omega
    refine ⟨E, ?_, fun x hx m hm => (mem_centralizer_iff.mp (hEC hx) m hm).symm, hEe, hE8, ?_⟩
    · exact sup_le (hFM.trans hMw) (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    · rw [wGroup_eq_of_commute hGW (hEe.isAbelianTwoOfRank hE8)
        (hE₁e.isAbelianTwoOfRank hE₁8)
        (fun x hx y hy => (mem_centralizer_iff.mp (hEC hx) y (hE₁M hy)).symm),
        wGroup_eq_of_commute hGW (hE₁e.isAbelianTwoOfRank hE₁8) hBr
        (fun x hx y hy => (hE₁B y hy x hx).symm), hWB]

end HeKMU

end CFSG.ComponentClassification.GrSLit
