module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKComp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKDMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMCInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKPCore

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeKMC

theorem type_and_pair
    {X : Type} [Group X] [Finite X] {L : Subgroup X} (hset : HeldEndSetting X L) {a u : X}
    {M : Subgroup X} (ha : orderOf a = 2) (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X)))) (hu : HeldTwoA L u)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hne : conjugate M a ≠ M) (hfix : gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u)
    (hc : ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) :
    IsL34Type (↥M ⧸ Open.fusionZStar ↥M) ∧
      ∃ z₁ ∈ (Open.fusionZStar ↥M).map M.subtype, ∃ z₂ ∈ (Open.fusionZStar ↥M).map M.subtype,
        z₁ * z₁ = 1 ∧ z₂ * z₂ = 1 ∧ z₁ ≠ 1 ∧ z₂ ≠ 1 ∧ z₁ ≠ z₂ ∧ z₁ * z₂ = z₂ * z₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHS, -, -, ⟨e⟩, -⟩ := id hset
  obtain ⟨-, -, -, -, -, -, ⟨e₀⟩⟩ := id hHS
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
  have hMq : IsQuasisimple ↥M :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hMu) hMc.1
  have haM : ∀ y ∈ M, a * y * a⁻¹ ∈ N := fun y hy => by
    rw [hN, HeKP.mem_conjugate,
      show a * (a * y * a⁻¹) * a⁻¹ = (a * a) * y * (a * a)⁻¹ by group, haa]
    simpa using hy
  have haN : ∀ x ∈ N, a * x * a⁻¹ ∈ M := fun x hx => HeKP.mem_conjugate.mp hx
  set K := gsFixedLayer L u with hKdef
  have hKL : K ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  have hKau : K ≤ centralizer ({a} : Set X) ⊓ Cu :=
    le_inf (hKL.trans hLa) ((gsFixedLayer_le_inf L u).trans inf_le_right)
  obtain ⟨B₈, -, hBe, -, V, hVB, hV4, hVZ⟩ := HeDE.exists_eight_le_center hLa e₀ hu.1 huu
    hu1 hKL hKau (HeDG.isPComponent_gsFixedLayer_inf e hLa hLc hu)
  have hOM : pPrimeCore 2 ↥M ≤ center ↥M := fun y hy => mem_center_iff.mpr fun g =>
    Subtype.ext (hc _ (mem_map_of_mem _ hy) g g.2).symm
  have hZM : Open.fusionZStar ↥M = center ↥M :=
    GrS5.fusionZStar_eq_center_of_le hMq.1.commutator_eq_top hOM
  set δ := HeDQ.delta hMN haM with hδ
  have hKδ : K = δ.range :=
    hfix.symm.trans (HeDG.gsFixedLayer_eq_range haa hMN haM haN hMq (by rw [hfix]; exact hu.2.2))
  let f : ↥M →* ↥K := δ.codRestrict K fun x => by rw [hKδ]; exact ⟨x, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨k, hk⟩
    have hk' : k ∈ δ.range := hKδ ▸ hk
    obtain ⟨x, rfl⟩ := hk'
    exact ⟨x, Subtype.ext rfl⟩
  have hfker : f.ker ≤ center ↥M := by
    intro x hx
    apply HeDG.ker_le_center hMN haM
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  have hKt : IsL34Type (↥K ⧸ center ↥K) := (heldTwoALayerFact X L ⟨e⟩ u hu).2
  refine ⟨LieType.CurtisTits.lieModel_of_mulEquiv
    ((HeKM.centerQuotEquivOfSurjective hMq.1 f hf hfker).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZM).symm) hKt, ?_⟩
  have hVK : V ≤ K := hVZ.trans (map_subtype_le _)
  rw [hKδ] at hVZ hVK
  have hRq : IsQuasisimple ↥δ.range := HeDG.isQuasisimple_range hMN haM hMq
  have hRO : pPrimeCore 2 ↥δ.range ≤ center ↥δ.range := by
    rcases LocalCores.quasisimple_normal_subgroups hRq
        (inferInstance : (pPrimeCore 2 ↥δ.range).Normal) with h | h
    · exfalso
      obtain ⟨b, hb, hb1⟩ := (bot_or_exists_ne_one V).resolve_left fun h0 => by
        rw [h0, card_bot] at hV4
        norm_num at hV4
      have hmem : (⟨b, hVK hb⟩ : ↥δ.range) ∈ pPrimeCore 2 ↥δ.range := h ▸ mem_top _
      have h2 : orderOf (⟨⟨b, hVK hb⟩, hmem⟩ : pPrimeCore 2 ↥δ.range) = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext (Subtype.ext (hBe.2 b (hVB hb))))
          (fun h1 => hb1 (congrArg (fun x : pPrimeCore 2 ↥δ.range => ((x : ↥δ.range) : X)) h1))
      have h3 := orderOf_dvd_natCard (⟨⟨b, hVK hb⟩, hmem⟩ : pPrimeCore 2 ↥δ.range)
      rw [h2] at h3
      exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
        (even_iff_two_dvd.mpr h3)
    · exact h
  have hZR : Open.fusionZStar ↥δ.range = center ↥δ.range :=
    GrS5.fusionZStar_eq_center_of_le hRq.1.commutator_eq_top hRO
  rw [hZR] at hVZ
  have hYc : ∀ x : ↥M, δ x ∈ V → x ∈ center ↥M := by
    intro x hx
    obtain ⟨c, hc', hcx⟩ := hVZ hx
    apply HeDG.mem_center_of_delta hMN haM hMq
    intro y
    have h := mem_center_iff.mp hc' ⟨δ y, ⟨y, rfl⟩⟩
    have h' := congrArg Subtype.val h
    simp only [coe_mul] at h'
    rw [← hcx]
    exact h'.symm
  set Y := V.comap δ with hY
  have hYcomm : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ * y₂ = y₂ * y₁ := fun y₁ hy₁ y₂ _ =>
    (mem_center_iff.mp (hYc y₁ hy₁) y₂).symm
  have hfY : ∀ y ∈ Y, δ y * δ y = 1 := fun y hy => hBe.2 _ (hVB (show δ y ∈ V from hy))
  have hker : δ.ker ≤ Y := by
    intro k hk
    show δ k ∈ V
    rw [MonoidHom.mem_ker.mp hk]
    exact one_mem _
  have hΩ4 : 4 ≤ Nat.card (HeDG.omega Y hYcomm) := by
    have h := HeDG.card_le_card_omega Y hYcomm δ hfY hker
    rwa [map_comap_eq_self hVK, hV4] at h
  obtain ⟨y₁, hy₁, hy₁1⟩ := (bot_or_exists_ne_one (HeDG.omega Y hYcomm)).resolve_left
    fun h0 => by
      rw [h0, card_bot] at hΩ4
      norm_num at hΩ4
  have hy₁2 : y₁ * y₁ = 1 := (HeDG.mem_omega.mp hy₁).2
  obtain ⟨y₂, hy₂, hy₂1⟩ : ∃ y ∈ HeDG.omega Y hYcomm, y ∉ zpowers y₁ := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show HeDG.omega Y hYcomm ≤ zpowers y₁ from hcon)
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf y₁ ≤ 2 := orderOf_le_of_pow_eq_one two_pos (by rw [pow_two]; exact hy₁2)
    omega
  have hy₂2 : y₂ * y₂ = 1 := (HeDG.mem_omega.mp hy₂).2
  have hy₂ne : y₂ ≠ 1 := by
    rintro rfl
    exact hy₂1 (one_mem _)
  have hy₁₂ : y₁ ≠ y₂ := by
    rintro rfl
    exact hy₂1 (mem_zpowers _)
  have hy₁c : y₁ ∈ center ↥M := hYc y₁ (HeDG.mem_omega.mp hy₁).1
  have hy₂c : y₂ ∈ center ↥M := hYc y₂ (HeDG.mem_omega.mp hy₂).1
  refine ⟨(y₁ : X), ?_, (y₂ : X), ?_, congrArg Subtype.val hy₁2, congrArg Subtype.val hy₂2,
    fun h => hy₁1 (Subtype.ext h), fun h => hy₂ne (Subtype.ext h),
    fun h => hy₁₂ (Subtype.ext h), (congrArg Subtype.val (mem_center_iff.mp hy₁c y₂)).symm⟩
  · rw [hZM]
    exact mem_map_of_mem _ hy₁c
  · rw [hZM]
    exact mem_map_of_mem _ hy₂c

end HeKMC

theorem heldKDiagonalComponentStep_of_rest
    (hD : L34RankTwoCentralFixedInput) (hRest : HeldKDiagonalComponentRestStep) :
    HeldKDiagonalComponentStep := by
  intro X _ _ L hset a u M ha hLa hLc hu hMu hMp hne hfix hc w hw hMw
  refine hRest X L hset a u M ha hLa hLc hu hMu hMp hne hfix hc w hw hMw
    fun hwM N hNw hNp hNu hMN => not_lt.mp fun hlt => ?_
  obtain ⟨htype, z₁, hz₁, z₂, hz₂, hs₁, hs₂, hn₁, hn₂, hz, hcz⟩ :=
    HeKMC.type_and_pair hset ha hLa hLc hu hMu hMp hne hfix hc
  obtain ⟨⟨hsimp, hnab, hK, -⟩, -⟩ := hset
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    norm_num at hw
  have hMNu : M ≤ N ⊓ centralizer ({u} : Set X) := le_inf hMN hMu
  exact HeK.false_of_proper_fixed_l34 hD hK hu.2.1 (HeKC.centralizer_ne_top hsimp hnab hw1) hNw
    hNp hNu hMNu (UnbalancedCorr.isPComponent_subgroupOf_of_le hMNu inf_le_right hMp) hlt htype
    hz₁ hz₂ hs₁ hs₂ hn₁ hn₂ hz hcz hwM hw

end CFSG.ComponentClassification.GrSLit
