module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9J
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9H
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHeGen

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier

theorem nonempty_layerOfFixed_equiv_heOuterD
    {G : Type} [Group G] [Finite G] (Θ : G ≃* heP) (s : MulAut G) (hy : heAutU ∈ heAutGroup)
    (hs : MulAut.congr Θ s = heConjR ⟨heAutU, hy⟩) (hL : Sol78.layerOfFixed s ≠ ⊥) :
    Nonempty (↥(Sol78.layerOfFixed s) ≃* ↥heOuterD) := by
  obtain ⟨hDC, hq, -⟩ := ctbh_outer_centralizer_derived_quasisimple
  have hK := HeGen.map_layerOfFixed_heConjR (⟨heAutU, hy⟩ : heAutGroup)
  rw [← heOuterC_eq, ← hs, HeGen.layerOfFixed_congr Θ s] at hK
  set L := Sol78.layerOfFixed s with hLdef
  have hKD : HeGen.layerIn heOuterC ≤ heOuterD := by
    rw [hDC, ← HeGen.layerIn_perfect heOuterC]
    exact commutator_mono (HeGen.layerIn_le _) (HeGen.layerIn_le _)
  have hKn : ((HeGen.layerIn heOuterC).subgroupOf heOuterD).Normal := ⟨fun k hk d => by
    rw [mem_subgroupOf] at hk ⊢
    exact HeGen.conj_mem_layerIn heOuterC (heOuterD_le_C d.2) hk⟩
  have hCD : HeGen.layerIn heOuterC = heOuterD := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
      ((HeGen.layerIn heOuterC).subgroupOf heOuterD) with h | h
    · exfalso
      have hab : ⁅HeGen.layerIn heOuterC, HeGen.layerIn heOuterC⁆ = ⊥ := by
        rw [commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [mem_centralizer_iff]
        intro z hz
        have hc := mem_center_iff.1
          (h (show (⟨x, hKD hx⟩ : heOuterD) ∈ (HeGen.layerIn heOuterC).subgroupOf heOuterD
            from hx)) ⟨z, hKD hz⟩
        exact congrArg Subtype.val hc
      have hbot : HeGen.layerIn heOuterC = ⊥ := (HeGen.layerIn_perfect heOuterC).symm.trans hab
      rw [hbot, map_eq_bot_iff_of_injective _ heP.subtype_injective,
        map_eq_bot_iff_of_injective _ Θ.injective] at hK
      exact hL hK
    · refine le_antisymm hKD fun d hd => ?_
      have : (⟨d, hd⟩ : heOuterD) ∈ (HeGen.layerIn heOuterC).subgroupOf heOuterD := h ▸ mem_top _
      exact mem_subgroupOf.1 this
  rw [hCD] at hK
  exact ⟨((L.equivMapOfInjective Θ.toMonoidHom Θ.injective).trans
    ((L.map Θ.toMonoidHom).equivMapOfInjective heP.subtype heP.subtype_injective)).trans
    (MulEquiv.subgroupCongr hK)⟩

variable {X : Type} [Group X]

theorem false_of_pump_held
    [Finite X] {M : Subgroup X} {m : ℕ}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ) (hm : m ≤ 11)
    {H : Subgroup X} (hHN : H ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {e₁ : X} (he₁2 : e₁ * e₁ = 1) {N : Subgroup X} (he₁N : e₁ ∈ normalizer (N : Set X))
    (hNperf : ⁅N, N⁆ = N) (hCH : N ⊓ centralizer ({e₁} : Set X) ≤ H) (hOH : coreNOf N ≤ H)
    {L₀ F : Subgroup X} (hL₀ : L₀ ≤ N ⊓ centralizer ({e₁} : Set X))
    (hL₀pc : IsPComponent 2 (L₀.subgroupOf (N ⊓ centralizer ({e₁} : Set X))))
    (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 7)) (hFL₀ : F ≤ L₀)
    (hF4 : Nat.card F = 4) (hFsq : ∀ x ∈ F, x * x = 1) (hFH : normalizer (F : Set X) ≤ H)
    {DY : Finset (Fin 7)} (hDY : DY.card = 4)
    (hFY : ∀ x : ↥L₀, (x : X) ∈ F → ∀ y ∉ DY,
      ((χ (x : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) y = y)
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* Blueprint.NativeSporadic.He) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbij := ctbh_full_automorphism_permutation_model.1
  set O := pPrimeCore 2 ↥N with hOdef
  have hNc : commutator ↥N = ⊤ := by
    apply map_injective N.subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hNperf
  obtain ⟨ψb⟩ := nonempty_coreQuot_held hNc ψ
  have hL₀N : L₀ ≤ N := hL₀.trans inf_le_left
  have hFN : F ≤ N := hFL₀.trans hL₀N
  have hF2 : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [hF4]; norm_num)
  have hL₀H : L₀ ≤ H := hL₀.trans hCH
  have hOH' : ∀ z : ↥N, z ∈ O → (z : X) ∈ H := fun z hz => hOH ⟨z, hz, rfl⟩
  have hNH : ¬ N ≤ H := by
    intro hNH
    apply not_two_pow_nine_dvd_card_of_le hρ hm hHN hker hNH
    have h1 : Nat.card ↥N = Nat.card (↥N ⧸ O) * Nat.card O :=
      card_eq_card_quotient_mul_card_subgroup O
    rw [Nat.card_congr ψb.toEquiv, Sporadic.He.card_He] at h1
    rw [h1]
    exact Dvd.dvd.mul_right (by norm_num) _
  set s := coreQuotAut N ⟨e₁, he₁N⟩ with hsdef
  have he₁inv : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right he₁2
  have hs2 : s * s = 1 := by
    ext q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O q
    change s (s (y : ↥N ⧸ O)) = (y : ↥N ⧸ O)
    rw [hsdef, coreQuotAut_mk, coreQuotAut_mk]
    congr 1
    apply Subtype.ext
    change e₁ * (e₁ * (y : X) * e₁⁻¹) * e₁⁻¹ = y
    rw [he₁inv]
    calc e₁ * (e₁ * (y : X) * e₁) * e₁ = (e₁ * e₁) * y * (e₁ * e₁) := by group
      _ = y := by rw [he₁2]; group
  set Θ : ↥N ⧸ O ≃* heP := ψb.trans heEquivP with hΘdef
  obtain ⟨x, hx⟩ := hbij.2 (MulAut.congr Θ s)
  by_cases hxP : (x : Equiv.Perm (Fin 8330)) ∈ heP
  ·
    apply not_two_pow_nine_dvd_card_of_le hρ hm hHN hker hCH
    have h1 := two_pow_nine_dvd_card_fixed_of_inner Θ s hs2 x hx hxP
    have h2 : Nat.card (Open.signalizerFixedSubgroup s) ∣
        Nat.card ↥(N ⊓ centralizer ({e₁} : Set X)) := by
      refine (card_dvd_of_le (fixed_le_map_centralizer he₁N he₁2)).trans
        ((card_map_dvd _ _).trans ?_)
      rw [← card_map_of_injective N.subtype_injective, subgroupOf_map_subtype, inf_comm]
    exact h1.trans h2
  have hx1 : (x : Equiv.Perm (Fin 8330)) ≠ 1 := fun h => hxP (h ▸ one_mem heP)
  have hxx : x * x = 1 := by
    apply hbij.1
    rw [map_mul, hx, map_one, ← map_mul, hs2, map_one]
  have hx2 : orderOf (x : Equiv.Perm (Fin 8330)) = 2 := by
    refine orderOf_eq_prime ?_ hx1
    rw [sq, ← Subgroup.coe_mul, hxx, Subgroup.coe_one]
  obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
  set Θ' : ↥N ⧸ O ≃* heP := Θ.trans (MulAut.conj (⟨g, hg⟩ : heP))⁻¹ with hΘ'def
  have hy : heAutU ∈ heAutGroup := heAutU_mem_heAutGroup
  have hΘ' : MulAut.congr Θ' s = heConjR ⟨heAutU, hy⟩ := by
    have e : MulAut.congr Θ' s =
        MulAut.congr (MulAut.conj (⟨g, hg⟩ : heP))⁻¹ (MulAut.congr Θ s) :=
      MulEquiv.ext fun _ => rfl
    rw [e, ← hx]
    exact HeGen.congr_conj_heConjR hg x ⟨heAutU, hy⟩ hxg
  have hs1 : s ≠ 1 := by
    intro h
    apply hx1
    have h1 : heConjR x = heConjR 1 := by rw [hx, h, map_one, map_one]
    rw [hbij.1 h1, Subgroup.coe_one]
  have hso : orderOf s = 2 := orderOf_eq_prime (by rw [sq, hs2]) hs1
  set L := Sol78.layerOfFixed s with hLdef
  have hL₀bL : (L₀.subgroupOf N).map (QuotientGroup.mk' O) ≤ L :=
    map_le_layerOfFixed he₁N he₁2 hL₀ hL₀pc
  obtain ⟨f₀, hf₀F, hf₀1⟩ : ∃ f₀ ∈ F, f₀ ≠ 1 := by
    rcases F.bot_or_exists_ne_one with h | h
    · rw [h, Subgroup.card_bot] at hF4
      exact absurd hF4 (by norm_num)
    · exact h
  have hFO : F.subgroupOf N ⊓ O = ⊥ := by
    refine inf_eq_bot_of_two_odd ?_ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    exact hF2.of_equiv (subgroupOfEquivOfLe hFN).symm
  have hLne : L ≠ ⊥ := by
    intro h
    have h1 : QuotientGroup.mk' O ⟨f₀, hFN hf₀F⟩ ∈ L := hL₀bL ⟨_, hFL₀ hf₀F, rfl⟩
    rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : (⟨f₀, hFN hf₀F⟩ : ↥N) ∈ F.subgroupOf N ⊓ O := mem_inf.mpr ⟨hf₀F, h1⟩
    rw [hFO, mem_bot] at h2
    exact hf₀1 (congrArg Subtype.val h2)
  obtain ⟨φL⟩ := nonempty_layerOfFixed_equiv_heOuterD Θ' s hy hΘ' hLne
  have hLcard : Nat.card L = 7560 := by rw [Nat.card_congr φL.toEquiv, card_heOuterD]
  have hZ3 : Nat.card (center ↥L) = 3 := by
    rw [Nat.card_congr (centerCongr φL).toEquiv, card_center_heOuterD]
  have hOZ : pPrimeCore 2 ↥L = center ↥L := by
    apply map_injective (f := φL.toMonoidHom) φL.injective
    have hc : (center ↥L).map φL.toMonoidHom = center ↥heOuterD := map_center_eq φL
    rw [pPrimeCore_map_iso 2 φL, HeGen.pPrimeCore_heOuterD, hc]
  have hLperf : ⁅L, L⁆ = L := by
    rw [hLdef, HeGen.layerOfFixed_eq_layerIn]
    exact HeGen.layerIn_perfect _
  have hLc : commutator ↥L = ⊤ := by
    apply map_injective L.subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hLperf
  have hlamL : ∀ l : ↥L₀, QuotientGroup.mk' O (inclusion hL₀N l) ∈ L := fun l =>
    hL₀bL ⟨_, l.2, rfl⟩
  set lam : ↥L₀ →* ↥L :=
    ((QuotientGroup.mk' O).comp (inclusion hL₀N)).codRestrict L hlamL with hlamdef
  have hlamk : Odd (Nat.card lam.ker) := by
    let j : lam.ker →* O := ((inclusion hL₀N).comp lam.ker.subtype).codRestrict O fun l => by
      have h1 : lam (l : ↥L₀) = 1 := l.2
      have h2 : QuotientGroup.mk' O (inclusion hL₀N (l : ↥L₀)) = 1 := congrArg Subtype.val h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have hj : Function.Injective j := fun a b h => by
      have h' : (((a : ↥L₀) : X)) = ((b : ↥L₀) : X) := congrArg (fun z : O => ((z : ↥N) : X)) h
      exact Subtype.ext (Subtype.ext h')
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
      (card_dvd_of_injective j hj)
  have hLq : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ≤ Nat.card (alternatingGroup (Fin 7)) := by
    have h1 := card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥L)
    have h3 : Nat.card ↥(pPrimeCore 2 ↥L) = 3 := by rw [hOZ, hZ3]
    rw [hLcard, h3] at h1
    rw [nat_card_alternatingGroup, Nat.card_fin]
    have h7 : Nat.factorial 7 / 2 = 2520 := by decide
    omega
  have hlams : Function.Surjective lam :=
    surjective_of_card_coreQuot_le lam hlamk hLc hOZ χ hLq
  obtain ⟨eL, heL⟩ := exists_coreQuot_equiv_of_surjective lam hlams hlamk (by norm_num) χ
  have hT : Sol78.IsTripleCoverAltSeven L :=
    ⟨hLperf, hZ3, ⟨(QuotientGroup.quotientMulEquivOfEq hOZ.symm).trans eL⟩⟩
  set Fb := (F.subgroupOf N).map (QuotientGroup.mk' O) with hFbdef
  have hFbL : Fb ≤ L := by
    rintro _ ⟨f, hf, rfl⟩
    exact hL₀bL ⟨f, hFL₀ hf, rfl⟩
  have hFb4 : Nat.card Fb = 4 := by
    have hker' : F.subgroupOf N ⊓ (QuotientGroup.mk' O).ker = ⊥ := by
      rw [QuotientGroup.ker_mk']
      exact hFO
    rw [hFbdef, card_map_of_inf_ker _ _ hker', Nat.card_congr (subgroupOfEquivOfLe hFN).toEquiv,
      hF4]
  have hFbsq : ∀ z ∈ Fb, z * z = 1 := by
    rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, show f * f = 1 from Subtype.ext (hFsq f hf), map_one]
  have hD : ∃ D' : Finset (Fin 7), D'.card = 4 ∧ ∀ z : ↥L, (z : ↥N ⧸ O) ∈ Fb → ∀ ω ∉ D',
      ((eL (z : ↥L ⧸ pPrimeCore 2 ↥L) : alternatingGroup (Fin 7)) : Perm (Fin 7)) ω = ω := by
    refine ⟨DY, hDY, fun z hz ω hω => ?_⟩
    obtain ⟨f, hf, hfz⟩ := hz
    have hz' : lam ⟨(f : X), hFL₀ hf⟩ = z := Subtype.ext hfz
    rw [← hz', heL]
    exact hFY ⟨(f : X), hFL₀ hf⟩ hf ω hω
  have hgen := HeGen.heldGenerationInput (↥N ⧸ O) ⟨ψb⟩ s hso 7 (Or.inr hT) eL Fb hFbL
    (klein_of_card_sq hFb4 hFbsq) hD
  apply hNH
  set Y := (H.subgroupOf N).map (QuotientGroup.mk' O) with hYdef
  have hLY : L ≤ Y := by
    intro z hz
    obtain ⟨l, hl⟩ := hlams ⟨z, hz⟩
    refine ⟨inclusion hL₀N l, hL₀H l.2, ?_⟩
    exact congrArg Subtype.val hl
  have hNFY : normalizer (Fb : Set (↥N ⧸ O)) ≤ Y := by
    intro z hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O z
    refine ⟨y, ?_, rfl⟩
    change (y : X) ∈ H
    refine mem_of_map_conj_le_sup_odd hFH (hFL₀.trans hL₀H) hOH hF2
      (fun f hf => le_normalizer_pPrimeCore (le_normalizer (hFN hf))) (odd_coreNOf N) ?_
    rintro _ ⟨f, hf, rfl⟩
    have h1 : QuotientGroup.mk' O ⟨f, hFN hf⟩ ∈ Fb := ⟨⟨f, hFN hf⟩, hf, rfl⟩
    have h2 := (mem_normalizer_iff.mp hz _).mp h1
    obtain ⟨f', hf', hff'⟩ := h2
    have h3 : f'⁻¹ * (y * ⟨f, hFN hf⟩ * y⁻¹) ∈ O := by
      rw [← QuotientGroup.eq]
      simp only [QuotientGroup.mk'_apply] at hff'
      rw [hff', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h4 : (MulAut.conj (y : X)).toMonoidHom f =
        (f' : X) * ((f'⁻¹ * (y * ⟨f, hFN hf⟩ * y⁻¹) : ↥N) : X) := by
      change (y : X) * f * (y : X)⁻¹ = _
      simp
    rw [h4]
    exact mul_mem (mem_sup_left hf') (mem_sup_right ⟨_, h3, rfl⟩)
  have hYtop : Y = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le hLY hNFY
  intro n hn
  obtain ⟨h, hh, hhn⟩ : QuotientGroup.mk' O ⟨n, hn⟩ ∈ Y := hYtop ▸ mem_top _
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hhn
  have h1 : h⁻¹ * ⟨n, hn⟩ ∈ O := QuotientGroup.eq.mp hhn
  have h2 := mul_mem (show (h : X) ∈ H from hh) (hOH' _ h1)
  simpa using h2

end CFSG.ComponentClassification.SolMax
