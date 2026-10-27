module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Fusion
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3NoncycPair
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3NoncycSquare
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Baum

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {Ω : Type*} [Group Ω]

theorem le_normalizer_of_elementwise_commute {L₁ L₂ : Subgroup Ω}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) : L₂ ≤ Subgroup.normalizer (L₁ : Set Ω) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  have key : ∀ a ∈ L₁, b * a * b⁻¹ = a := fun a ha => by
    rw [← hcomm a ha b hb]; group
  have hbi : b⁻¹ ∈ L₂ := L₂.inv_mem hb
  have key' : ∀ a ∈ L₁, b⁻¹ * a * b = a := fun a ha => by
    have := hcomm a ha b⁻¹ hbi
    rw [← this]; group
  constructor
  · intro ha
    rw [key a ha]; exact ha
  · intro h
    have h2 : b⁻¹ * (b * a * b⁻¹) * b = b * a * b⁻¹ := key' _ h
    have h3 : a = b * a * b⁻¹ := by
      calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
        _ = b * a * b⁻¹ := h2
    rw [h3]; exact h

theorem card_sup_mul_card_inf_of_elementwise_commute {L₁ L₂ : Subgroup Ω}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    Nat.card (L₁ ⊔ L₂ : Subgroup Ω) * Nat.card (L₁ ⊓ L₂ : Subgroup Ω) =
      Nat.card L₁ * Nat.card L₂ :=
  CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (le_normalizer_of_elementwise_commute hcomm)

theorem inf_ne_bot_of_le_sup_of_card_six [Finite Ω] {L₁ L₂ Ū : Subgroup Ω}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h1 : Nat.card L₁ = 6)
    (h2 : Nat.card L₂ = 6) (hŪ : Nat.card Ū = 9) (hle : Ū ≤ L₁ ⊔ L₂) : L₁ ⊓ Ū ≠ ⊥ := by
  intro hbot
  have hnorm : Ū ≤ Subgroup.normalizer (L₁ : Set Ω) := hle.trans
    (sup_le Subgroup.le_normalizer (le_normalizer_of_elementwise_commute hcomm))
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hnorm
  have h36 := card_sup_mul_card_inf_of_elementwise_commute hcomm
  rw [h1, h2] at h36
  have hpos : 0 < Nat.card (L₁ ⊓ L₂ : Subgroup Ω) := Nat.card_pos
  have hsup : Nat.card (L₁ ⊔ L₂ : Subgroup Ω) ≤ 36 := by
    have : Nat.card (L₁ ⊔ L₂ : Subgroup Ω) ≤ Nat.card (L₁ ⊔ L₂ : Subgroup Ω) *
        Nat.card (L₁ ⊓ L₂ : Subgroup Ω) := Nat.le_mul_of_pos_right _ hpos
    omega
  have hZ : Nat.card (L₁ ⊔ Ū : Subgroup Ω) ≤ 36 :=
    (Subgroup.card_le_of_le (sup_le le_sup_left hle)).trans hsup
  rw [hbot, Subgroup.card_bot, h1, hŪ] at h
  omega

section Main

variable {G : Type} [Group G] [Finite G] {V M : Subgroup G} {hU : IsElemAbelian 2 V}

omit [Finite G] in
theorem eq_one_of_three_pow_eq_one_of_mem_coprime {x : G} {C : Subgroup G} {k : ℕ}
    (hx : x ^ 3 ^ k = 1) (hxC : x ∈ C) (hC3 : ¬ 3 ∣ Nat.card C) : x = 1 := by
  have hord : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hx
  have hord2 : orderOf x ∣ Nat.card C := Subgroup.orderOf_dvd_natCard _ hxC
  have hcop : Nat.Coprime (3 ^ k) (Nat.card C) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hC3)
  exact orderOf_eq_one_iff.1 ((hcop.of_dvd_left hord).eq_one_of_dvd hord2)

omit [Finite G] in
theorem injective_actM_comp_inclusion (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M)) {Q : Subgroup G}
    (hQM : Q ≤ M) (hQp : IsPGroup 3 Q) :
    Function.Injective ((actM hU hMN).comp (Subgroup.inclusion hQM)) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  have hcent : (q : G) ∈ Subgroup.centralizer (V : Set G) :=
    (actM_eq_one_iff hU hMN ⟨q, hQM q.2⟩).1 hq
  obtain ⟨k, hk⟩ := hQp q
  have hsk : (q : G) ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact Subtype.ext (eq_one_of_three_pow_eq_one_of_mem_coprime hsk
    (show (q : G) ∈ Subgroup.centralizer (V : Set G) ⊓ M from ⟨hcent, hQM q.2⟩) hC3)

theorem not_isCyclic_of_E27_small_factor {W E A' U : Subgroup G} (hEW : E ≤ W)
    (hEel : IsElemAbelian 3 E) (hEc : Nat.card E = 27) (hA'W : A' ≤ W) (hUW : U ≤ W)
    (hA3 : Nat.card A' ≤ 3) (hfac : ∀ w ∈ W, ∃ a ∈ A', ∃ u ∈ U, w = a * u) :
    ¬ IsCyclic U ∧ Nat.card W ≤ 3 * Nat.card U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWle : Nat.card W ≤ Nat.card A' * Nat.card U := by
    let f : A' × U → W := fun p => ⟨(p.1 : G) * (p.2 : G), W.mul_mem (hA'W p.1.2) (hUW p.2.2)⟩
    have hsurj : Function.Surjective f := by
      intro w
      obtain ⟨a, ha, u, hu, hw⟩ := hfac w w.2
      exact ⟨(⟨a, ha⟩, ⟨u, hu⟩), Subtype.ext hw.symm⟩
    have := Nat.card_le_card_of_surjective f hsurj
    simpa [Nat.card_prod] using this
  have h2 : Nat.card W ≤ 3 * Nat.card U := hWle.trans (Nat.mul_le_mul_right _ hA3)
  refine ⟨?_, h2⟩
  intro hcyc
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hEU : Nat.card (E ⊓ U : Subgroup G) ≤ 3 := by
    have hcyc' : IsCyclic (E ⊓ U : Subgroup G) := Subgroup.isCyclic_of_le inf_le_right
    exact card_le_of_isElemAbelian_of_isCyclic
      (CFSG.AGLEmbeddingD2.Tits.MsidePrelim.isElemAbelian_of_le hEel inf_le_left) hcyc'
  have hP := card_mul_card_le_card_mul_card_inf hEW hUW
  rw [hEc] at hP
  have h1 : Nat.card W * Nat.card (E ⊓ U : Subgroup G) ≤ Nat.card W * 3 :=
    Nat.mul_le_mul_left _ hEU
  nlinarith

theorem exists_pair_of_le_sup {U : Subgroup G} (hUM : U ≤ M) (hUp : IsPGroup 3 U)
    (hU9 : Nat.card U = 9) (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M))
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) {L₁ L₂ : Subgroup (MulAut (IntMod V hU))}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h1 : Nat.card L₁ = 6) (h2 : Nat.card L₂ = 6)
    (hle : ∀ (x : G) (hx : x ∈ U), actM hU hMN ⟨x, hUM hx⟩ ∈ L₁ ⊔ L₂) :
    (∃ (x : G) (hx : x ∈ U), actM hU hMN ⟨x, hUM hx⟩ ∈ L₁ ∧ actM hU hMN ⟨x, hUM hx⟩ ≠ 1) ∧
    (∃ (x : G) (hx : x ∈ U), actM hU hMN ⟨x, hUM hx⟩ ∈ L₂ ∧ actM hU hMN ⟨x, hUM hx⟩ ≠ 1) := by
  set ψ : ↥U →* MulAut (IntMod V hU) := (actM hU hMN).comp (Subgroup.inclusion hUM) with hψ
  have hinj : Function.Injective ψ := injective_actM_comp_inclusion hMN hC3 hUM hUp
  have hŪ9 : Nat.card ψ.range = 9 := by
    rw [← hU9]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hŪle : ψ.range ≤ L₁ ⊔ L₂ := by
    rintro _ ⟨u, rfl⟩
    exact hle u u.2
  have key : ∀ {L L' : Subgroup (MulAut (IntMod V hU))}, (∀ a ∈ L, ∀ b ∈ L', a * b = b * a) →
      Nat.card L = 6 → Nat.card L' = 6 → ψ.range ≤ L ⊔ L' →
      ∃ (x : G) (hx : x ∈ U), actM hU hMN ⟨x, hUM hx⟩ ∈ L ∧ actM hU hMN ⟨x, hUM hx⟩ ≠ 1 := by
    intro L L' hc hL hL' hle'
    obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
      (inf_ne_bot_of_le_sup_of_card_six hc hL hL' hŪ9 hle')
    obtain ⟨u, hu⟩ := g.2.2
    refine ⟨(u : G), u.2, ?_, ?_⟩
    · have : actM hU hMN ⟨(u : G), hUM u.2⟩ = (g : MulAut (IntMod V hU)) := hu
      rw [this]; exact g.2.1
    · have : actM hU hMN ⟨(u : G), hUM u.2⟩ = (g : MulAut (IntMod V hU)) := hu
      rw [this]
      exact fun h => hg1 (Subtype.ext h)
  exact ⟨key hcomm h1 h2 hŪle, key (fun a ha b hb => (hcomm b hb a ha).symm) h2 h1
    (hŪle.trans (sup_comm L₁ L₂).le)⟩

omit [Finite G] in
theorem nine_dvd_card_sup {Ω : Type*} [Group Ω] [Finite Ω] {L₁ L₂ : Subgroup Ω}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h1 : Nat.card L₁ = 6) (h2 : Nat.card L₂ = 6)
    (hcop : ∀ g ∈ L₁ ⊓ L₂, g ^ 3 = 1 → g = 1) : 9 ∣ Nat.card (L₁ ⊔ L₂ : Subgroup Ω) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h36 := card_sup_mul_card_inf_of_elementwise_commute hcomm
  rw [h1, h2] at h36
  have h3 : ¬ 3 ∣ Nat.card (L₁ ⊓ L₂ : Subgroup Ω) := by
    intro h3
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(L₁ ⊓ L₂)) 3 h3
    have hg3 : (g : Ω) ^ 3 = 1 := by
      have := pow_orderOf_eq_one g
      rw [hg] at this
      exact congrArg Subtype.val this
    have h1' := hcop g g.2 hg3
    have : g = 1 := Subtype.ext h1'
    rw [this, orderOf_one] at hg
    omega
  have hcop9 : Nat.Coprime 9 (Nat.card (L₁ ⊓ L₂ : Subgroup Ω)) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
  exact hcop9.dvd_of_dvd_mul_right (h36.symm ▸ (by norm_num : 9 ∣ 6 * 6))

theorem false_of_inf_preimage_bot {Ystar : Subgroup (MulAut (IntMod V hU))}
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hY : Ystar ≤ autI hU M)
    (hYn : ∀ g ∈ autI hU M, ∀ φ ∈ Ystar, g * φ * g⁻¹ ∈ Ystar) (hY9 : 9 ∣ Nat.card Ystar)
    {W U : Subgroup G} (hWM : W ≤ M) (hWp : IsPGroup 3 W)
    (hWidx : ¬ 3 ∣ (W.subgroupOf M).index) (hUW : U ≤ W) (hU9 : Nat.card U = 9)
    (hW27 : Nat.card W ≤ 27)
    (hα : ∀ (x : G) (hx : x ∈ U), actM hU hMN ⟨x, hWM (hUW hx)⟩ ∈ Ystar → x = 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYM : preAutM hU hMN Ystar ≤ M := preAutM_le hU hMN Ystar
  have hYcard : Nat.card (preAutM hU hMN Ystar) =
      Nat.card Ystar * Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M) :=
    card_preAutM_of_le hU hMN hY
  have h9Y : 3 ^ 2 ∣ Nat.card (preAutM hU hMN Ystar) := by
    rw [hYcard]
    exact Dvd.dvd.mul_right (by simpa using hY9) _
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥(preAutM hU hMN Ystar)) := inferInstance
  have h9S : 3 ^ 2 ∣ Nat.card S := Sylow.pow_dvd_card_of_pow_dvd_card S h9Y
  set S' : Subgroup G := (S : Subgroup ↥(preAutM hU hMN Ystar)).map
    (preAutM hU hMN Ystar).subtype with hS'
  have hS'p : IsPGroup 3 S' := S.isPGroup'.map _
  have hS'Y : S' ≤ preAutM hU hMN Ystar := Subgroup.map_subtype_le _
  have hS'card : Nat.card S' = Nat.card S :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ (preAutM hU hMN Ystar).subtype
      (preAutM hU hMN Ystar).subtype_injective).toEquiv).symm
  obtain ⟨g, hgM, hgS⟩ := exists_conj_map_le_of_isPGroup hWM hWp hWidx (hS'Y.trans hYM) hS'p
  have hS''card : Nat.card (S'.map (MulAut.conj g).toMonoidHom) = Nat.card S' :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hgact : actM hU hMN ⟨g, hgM⟩ ∈ autI hU M := by
    rw [← range_actM hU hMN]
    exact ⟨⟨g, hgM⟩, rfl⟩
  have hbot : U ⊓ S'.map (MulAut.conj g).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, s, hsS', rfl⟩
    obtain ⟨hsM, hsY⟩ := (mem_preAutM hU hMN).1 (hS'Y hsS')
    have hxM : g * s * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM hsM) (M.inv_mem hgM)
    have hmem : actM hU hMN ⟨g * s * g⁻¹, hxM⟩ ∈ Ystar := by
      have : actM hU hMN ⟨g * s * g⁻¹, hxM⟩ =
          actM hU hMN ⟨g, hgM⟩ * actM hU hMN ⟨s, hsM⟩ * (actM hU hMN ⟨g, hgM⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [this]
      exact hYn _ hgact _ hsY
    exact hα (g * s * g⁻¹) hxU hmem
  have hP := card_mul_card_le_card_mul_card_inf hUW hgS
  rw [hbot, Subgroup.card_bot, hU9, hS''card, hS'card] at hP
  have h9 : 9 ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos (by simpa using h9S)
  omega


theorem false_of_pair_data3 {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K₀) (hstr : GLBStronglyEmbedded 3 M)
    {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I) (h2 : 2 ≤ I.card)
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hSylJ : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)))
    (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M)) {C₁ C₂ : Subgroup G}
    (hdat : FFPairData M T hU I C₁ C₂) : False := by
  classical
  have := ctx.amb
  have hc := ctx.conf
  have hOnly := ctx.allResidue.onlyL34At
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hC₁1, hC₁2, hC₂1, hC₂2, hT₁, hT₂, hCM₁, hJ₂, hH⟩ := hdat
  have hN₁ : ¬ Subgroup.normalizer (C₁ : Set G) ≤ M := fun h => hNT (hT₁.trans h)
  have hN₂ : ¬ Subgroup.normalizer (C₂ : Set G) ≤ M := fun h => hNT (hT₂.trans h)
  choose! Hf hHM hHL hH3 hHcase using hH
  set KA : Subgroup G := ⨆ L ∈ I, ⨆ (_ : Hf L ≤ Subgroup.normalizer (C₁ : Set G)), Hf L with hKA
  set KB : Subgroup G := ⨆ L ∈ I, ⨆ (_ : ¬ Hf L ≤ Subgroup.normalizer (C₁ : Set G)), Hf L
    with hKB
  have hKAM : KA ≤ M := iSup₂_le fun L hL => iSup_le fun _ => hHM L hL
  have hKBM : KB ≤ M := iSup₂_le fun L hL => iSup_le fun _ => hHM L hL
  have hKBN : KB ≤ Subgroup.normalizer (C₂ : Set G) :=
    iSup₂_le fun L hL => iSup_le fun h => (hHcase L hL).resolve_left h
  have hKAN : KA ≤ Subgroup.normalizer (C₁ : Set G) := iSup₂_le fun L hL => iSup_le fun h => h
  have hcov : ∀ L ∈ I, L ≤ autI hU KA ∨ L ≤ autI hU KB := by
    intro L hL
    by_cases h : Hf L ≤ Subgroup.normalizer (C₁ : Set G)
    · exact Or.inl ((hHL L hL).trans (autI_mono hU (le_iSup₂_of_le L hL
        (le_iSup (fun _ : Hf L ≤ Subgroup.normalizer (C₁ : Set G) => Hf L) h))))
    · exact Or.inr ((hHL L hL).trans (autI_mono hU
        (le_iSup₂_of_le L hL (le_iSup (fun _ : ¬ Hf L ≤ Subgroup.normalizer (C₁ : Set G) => Hf L)
          h))))
  have hAuniq : ∀ L₁ ∈ I, ∀ L₂ ∈ I, Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G) →
      Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G) → L₁ = L₂ := by
    intro L₁ h₁ L₂ h₂ hH₁ hH₂
    by_contra hne
    exact false_of_two_factors_in_normalizer3 hc hstr hOnly hMN hC₁1 hC₁2 hN₁ hKAM hKAN hC3 hI
      hcard h₁ h₂ hne ((hHL L₁ h₁).trans (autI_mono hU (le_iSup₂_of_le L₁ h₁
        (le_iSup (fun _ : Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G) => Hf L₁) hH₁))))
      ((hHL L₂ h₂).trans (autI_mono hU (le_iSup₂_of_le L₂ h₂
        (le_iSup (fun _ : Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G) => Hf L₂) hH₂))))
  have hBuniq : ∀ L₁ ∈ I, ∀ L₂ ∈ I, ¬ Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G) →
      ¬ Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G) → L₁ = L₂ := by
    intro L₁ h₁ L₂ h₂ hH₁ hH₂
    by_contra hne
    exact false_of_two_factors_in_normalizer3 hc hstr hOnly hMN hC₂1 hC₂2 hN₂ hKBM hKBN hC3 hI
      hcard h₁ h₂ hne ((hHL L₁ h₁).trans (autI_mono hU (le_iSup₂_of_le L₁ h₁
        (le_iSup (fun _ : ¬ Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G) => Hf L₁) hH₁))))
      ((hHL L₂ h₂).trans (autI_mono hU (le_iSup₂_of_le L₂ h₂
        (le_iSup (fun _ : ¬ Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G) => Hf L₂) hH₂))))
  have hbA : ∀ Q' : Subgroup (MulAut (IntMod V hU)), Q' ≤ autI hU KA → IsPGroup 3 Q' →
      Nat.card Q' ≤ 3 := by
    intro Q' hQ' hQ'p
    by_cases hex : ∃ L₀ ∈ I, Hf L₀ ≤ Subgroup.normalizer (C₁ : Set G)
    · obtain ⟨L₀, hL₀, hH₀⟩ := hex
      have hKAeq : KA ≤ Hf L₀ := iSup₂_le fun L hL => iSup_le fun h => by
        rw [hAuniq L hL L₀ hL₀ h hH₀]
      exact hH3 L₀ hL₀ Q' (hQ'.trans (autI_mono hU hKAeq)) hQ'p
    · push Not at hex
      have hKAbot : KA = ⊥ := by
        refine le_bot_iff.1 (iSup₂_le fun L hL => iSup_le fun h => absurd h (hex L hL))
      have hQ'bot : Q' = ⊥ := by
        refine le_bot_iff.1 (fun φ hφ => ?_)
        obtain ⟨g, hg, rfl⟩ := (mem_autI hU).1 (hQ' hφ)
        rw [hKAbot, Subgroup.mem_bot] at hg
        have : g = 1 := Subtype.ext hg
        rw [this, map_one]
        exact Subgroup.one_mem _
      rw [hQ'bot, Subgroup.card_bot]; norm_num
  obtain ⟨La, haI, Lb, hbI, hab⟩ := Finset.one_lt_card.1 h2
  have hside : ∃ L₁ ∈ I, ∃ L₂ ∈ I, Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G) ∧
      ¬ Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G) := by
    by_cases ha : Hf La ≤ Subgroup.normalizer (C₁ : Set G) <;>
      by_cases hb : Hf Lb ≤ Subgroup.normalizer (C₁ : Set G)
    · exact absurd (hAuniq La haI Lb hbI ha hb) hab
    · exact ⟨La, haI, Lb, hbI, ha, hb⟩
    · exact ⟨Lb, hbI, La, haI, hb, ha⟩
    · exact absurd (hBuniq La haI Lb hbI ha hb) hab
  obtain ⟨L₁, h₁, L₂, h₂, hA₁, hB₂⟩ := hside
  have hne : L₁ ≠ L₂ := fun h => hB₂ (h ▸ hA₁)
  have hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := hI.comm L₁ h₁ L₂ h₂ hne
  have hI2 : I = {L₁, L₂} := by
    ext L
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hL
      by_cases hLA : Hf L ≤ Subgroup.normalizer (C₁ : Set G)
      · exact Or.inl (hAuniq L hL L₁ h₁ hLA hA₁)
      · exact Or.inr (hBuniq L hL L₂ h₂ hLA hB₂)
    · rintro (rfl | rfl)
      · exact h₁
      · exact h₂
  have hY : autI hU (thompsonJ M) = L₁ ⊔ L₂ := by
    rw [hJM, hI2, Finset.iSup_insert, Finset.iSup_singleton]
  set CM : Subgroup G := Subgroup.centralizer (V : Set G) ⊓ M with hCM
  set 𝒜 : Subgroup G := CM ⊔ KA with h𝒜
  set ℬ : Subgroup G := KB ⊔ (M ⊓ Subgroup.normalizer (baum T : Set G)) with hℬ
  have h𝒜M : 𝒜 ≤ M := sup_le inf_le_right hKAM
  have hℬM : ℬ ≤ M := sup_le hKBM inf_le_left
  have hℬN : ℬ ≤ Subgroup.normalizer (C₂ : Set G) := sup_le hKBN hJ₂
  have hfac : ∀ m ∈ M, ∃ a ∈ 𝒜, ∃ b ∈ ℬ, m = a * b := by
    intro m hm
    obtain ⟨c, hc', a, ha, b, hb, n, hn, rfl⟩ := exists_factor_of_covering hMN hT (C1GN.baum_le T)
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T))
      (normalizer_inf_sup_le_normalizer_baum T _) hI hSylJ hJM hKAM hKBM hcov m hm
    exact ⟨c * a, Subgroup.mul_mem _ (Subgroup.mem_sup_left hc') (Subgroup.mem_sup_right ha),
      b * n, Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hn),
      by group⟩
  obtain ⟨W, hWM, hWp, hWidx, hWfac⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_sylow_eq_mul_of_mul (p := 3) h𝒜M hℬM hfac
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal ctx.setting ctx.sigma ctx.core
  have h3 : 3 ≤ CFSG.Open.pRank 3 M := hP3.ge.trans (pRank_mono 3 Nat.prime_three hPM)
  obtain ⟨E, hEW, hEel, hEc⟩ := exists_elemAbelian_le_sylow_pow hWM hWp hWidx h3
  set U : Subgroup G := W ⊓ ℬ with hUdef
  have hUW : U ≤ W := inf_le_left
  have hUM : U ≤ M := hUW.trans hWM
  have hUN : U ≤ Subgroup.normalizer (C₂ : Set G) := inf_le_right.trans hℬN
  have hUp : IsPGroup 3 U := hWp.to_le hUW
  have hA'3 : Nat.card (W ⊓ 𝒜 : Subgroup G) ≤ 3 :=
    card_le_of_le_sup_centralizer hMN hC3 hKAM inf_le_right (hWp.to_le inf_le_left) hbA
  obtain ⟨hUnc, hWle⟩ := not_isCyclic_of_E27_small_factor hEW hEel (by rw [hEc]; norm_num)
    inf_le_left hUW hA'3 hWfac
  obtain ⟨hUel, hU9, hconj⟩ := D2L34BetaConf3.exists_conj_eq_of_not_isCyclic hc hstr hOnly
    (⟨C₂, hC₂1, hC₂2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C₂ : Set G))) hN₂ hUN hUM hUp hUnc
  have hW27 : Nat.card W ≤ 27 := by rw [hU9] at hWle; omega
  have hact_mem : ∀ (m : G) (hm : m ∈ M), actM hU hMN ⟨m, hm⟩ ∈ autI hU M := fun m hm => by
    rw [← range_actM hU hMN]
    exact ⟨⟨m, hm⟩, rfl⟩
  have hYn := autI_thompsonJ_normalized (hU := hU) (V := V) (M := M)
  have hYM : autI hU (thompsonJ M) ≤ autI hU M := autI_mono hU (B6.thompsonJ_le M)
  have h9 : 9 ∣ Nat.card (autI hU (thompsonJ M)) := by
    rw [hY]
    exact nine_dvd_card_sup hcomm (hcard L₁ h₁) (hcard L₂ h₂)
      (fun g hg hg3 => hI.eq_one_of_mem_inf h₁ h₂ hne hg.1 hg.2 hg3)
  by_cases hβ : ∃ (x : G) (hx : x ∈ U), x ≠ 1 ∧
      actM hU hMN ⟨x, hUM hx⟩ ∈ autI hU (thompsonJ M)
  ·
    obtain ⟨x₀, hx₀U, hx₀1, hx₀Y⟩ := hβ
    have hall : ∀ (y : G) (hy : y ∈ U), actM hU hMN ⟨y, hUM hy⟩ ∈ L₁ ⊔ L₂ := by
      intro y hy
      rw [← hY]
      by_cases hy1 : y = 1
      · subst hy1
        have : actM hU hMN ⟨1, hUM hy⟩ = 1 := map_one _
        rw [this]
        exact Subgroup.one_mem _
      · obtain ⟨n, hn, hnx⟩ := hconj x₀ hx₀U hx₀1 y hy hy1
        obtain ⟨hnM, -⟩ := Subgroup.mem_inf.1 hn
        have : actM hU hMN ⟨y, hUM hy⟩ = actM hU hMN ⟨n, hnM⟩ * actM hU hMN ⟨x₀, hUM hx₀U⟩ *
            (actM hU hMN ⟨n, hnM⟩)⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (by simpa using hnx.symm)
        rw [this]
        exact hYn _ (hact_mem n hnM) _ hx₀Y
    obtain ⟨⟨x₁, hx₁, hg₁, hg₁1⟩, ⟨x₂, hx₂, hg₂, hg₂1⟩⟩ := exists_pair_of_le_sup hUM hUp hU9 hC3
      hMN hcomm (hcard L₁ h₁) (hcard L₂ h₂) hall
    have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hUel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    exact false_of_same_side_pair3 hc hstr hOnly
      (⟨C₂, hC₂1, hC₂2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C₂ : Set G))) hN₂ hU hMN hI h₁ h₂
      hne (hUM hx₁) (hUM hx₂) (hUN hx₁) (hUN hx₂) (hUab x₁ hx₁ x₂ hx₂) (hUel.2 x₁ hx₁)
      (hUel.2 x₂ hx₂) hg₁ hg₂ hg₁1 hg₂1
  ·
    push Not at hβ
    refine false_of_inf_preimage_bot hMN hYM hYn h9 hWM hWp hWidx hUW hU9 hW27
      (fun x hx hmem => ?_)
    by_contra hx1
    exact hβ x hx hx1 hmem

theorem ffRankTwoInput3_of_nodes (hX : D1NoXBlock3 G) (hGS : FFGroupStep3 G) :
    FFRankTwoInput3 G := by
  intro d P M A H R Rbar K ctx hstr hcon T hT hNT hC3 hU I hMN h2 hcard hJM hSyl hperm hfam
  have hN : NoXBlockFor G := noXBlockFor_of_setting hX ctx.setting
  have := ctx.amb
  have hc := ctx.conf
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨C₁, C₂, hdat⟩ := exists_ffPairData3 hN hGS ctx hstr hcon hT hNT hU I hMN hcard hJM hSyl
    hperm hfam
  obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  have hVT := hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT))
  have hBS := autI_baum_le_autI_thompsonJ hMN hT hVT hfam hJM
    (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT) hperm
  have hSylB := isSylowTwoOf_of_le_of_le hSyl (autI_mono hU (thompsonJ_le_baum T)) hBS
    (isPGroup_autI hU (hT.2.1.to_le (C1GN.baum_le T)))
  exact false_of_pair_data3 ctx hstr hT hNT hMN hfam h2 hcard hSylB hJM hC3 hdat

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC
