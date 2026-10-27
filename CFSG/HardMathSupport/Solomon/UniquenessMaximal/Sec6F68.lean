module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6F69
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6F610
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FIa

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem prop68_of_inputs (hONG : InputONGroup) (hcov : CoverStmt) (iL3 : InputL3U3Facts) (i183 : Input18_3_4)
    (h515 : Lemma515) (hKT : InputKType) (hNoSL : InputNoSLSection) (h62 : Lemma62Stmt)
    (hOut : InputOutON) (hSyl : InputSylowON) (hSL34 : InputSL34Facts) (hL34 : InputL34Facts)
    (h2320 : Input23_20) (h2325 : Input23_25_2) (h65 : Lemma65) (h66 : Lemma66)
    (i1812 : Input18_3_12) (i254 : Input25_4)
    (hS : GLStanding G 4 3) (hC : GLCaseFour G 3) {B : Subgroup G} (hB : IsExtremal B)
    (hkZero : ∀ K : Subgroup G, IsHSet B K → ∀ a ∈ centralizerQuot B K, a ≠ 1 →
      kZeroOf B K ≤ bClosureIa K a) : Prop68Out B := by
  intro K hK
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK' := hK
  obtain ⟨⟨x, hxB, hx1, hcomp⟩, hty, hKM⟩ := hK'
  obtain ⟨hB1, b, L, A, hw⟩ := hB.exists_witness
  have e := exists_extCtx hS hC hB1 hw
  have hK34 : IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K) := by
    rcases hty with h | h | h
    · exact h
    · exact absurd h (lemma610 hcov iL3 i183 h515 hKT hNoSL h62 hSL34 h2320 h65 h66 hS hC hB hK)
    · exact absurd h (lemma69 hONG h62 hOut hSyl h2325 h66 hS hC hB hK)
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := by
    rcases h62 G 4 hS hC B hB x hxB hx1 K hcomp with h | h
    · exact h
    · exact absurd h (not_isLTwoOddPow_lThreeFour hK34)
  have hxC : B ≤ Subgroup.centralizer ({x} : Set G) := fun c hc => by
    rw [Subgroup.mem_centralizer_singleton_iff]; exact ea_comm e.Bel hc hxB
  have hB81 : Nat.card B = 81 := e.Bc
  have h20 := h2320 G _ K B hcomp (Or.inl hK34) hxC e.Bel hBN
  obtain ⟨hInn, hrel⟩ : (∀ b ∈ B, ∃ k ∈ K, ∀ y ∈ K,
      b * y * b⁻¹ * (k * y * k⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 K) ∧ (dQ K).relIndex B = 9 := by
    rcases h20 with h | h
    · exact absurd (le_glbCore_of_gammaCl hS hB1 hBN h) hKM
    · exact h
  have hD9 : Nat.card ↥(B ⊓ dQ K) = 9 := by
    have hmul := Subgroup.relIndex_mul_card (dQ K) B
    rw [inf_comm, hrel, hB81] at hmul
    omega
  have hAK : centralizerQuot B K = B ⊓ dQ K := centralizerQuot_eq_inf_dQ hBN
  have hBp : IsPGroup 3 ↥B := IsPGroup.of_card (n := 4) (by rw [hB81]; norm_num)
  obtain ⟨R, hBR, hRp, hRY, hR1c, hcommR, hdecR, hN1, hN2⟩ := exists_rStruct hBp hBN hInn
  obtain ⟨P', ⟨eP⟩⟩ := sylow_equiv_sylowBar (K := K) (P := R ⊓ K) inf_le_right
    (hRp.to_le inf_le_left) hR1c
  obtain ⟨hsimple, hSyl9⟩ := hL34 _ hK34
  obtain ⟨hP9, hPcomm, hPexp⟩ := hSyl9 P'
  have hR1card : Nat.card ↥(R ⊓ K) = 9 := (Nat.card_congr eP.toEquiv).trans hP9
  have hR1comm : ∀ a ∈ R ⊓ K, ∀ c ∈ R ⊓ K, a * c = c * a := fun a ha c hc => by
    have h1 := hPcomm (eP ⟨a, ha⟩) (eP ⟨c, hc⟩)
    have h2 : (⟨a, ha⟩ : ↥(R ⊓ K)) * ⟨c, hc⟩ = ⟨c, hc⟩ * ⟨a, ha⟩ := by
      apply eP.injective; rw [map_mul, map_mul]; exact h1
    exact congrArg Subtype.val h2
  have hR1exp : ∀ g ∈ R ⊓ K, g ^ 3 = 1 := fun g hg => by
    have h1 := hPexp (eP ⟨g, hg⟩)
    have h2 : (⟨g, hg⟩ : ↥(R ⊓ K)) ^ 3 = 1 := by
      apply eP.injective; rw [map_pow, map_one]; exact h1
    exact congrArg Subtype.val h2
  have hKbc : Nat.card (↥K ⧸ GLAPPrimeCore 3 ↥K) = 20160 := card_lThreeFour hK34
  have hcenter : Subgroup.center (↥K ⧸ GLAPPrimeCore 3 ↥K) = ⊥ := by
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥K ⧸ GLAPPrimeCore 3 ↥K))
      with h | h
    · exact h
    · exfalso
      have hcen : ∀ a b : ↥K ⧸ GLAPPrimeCore 3 ↥K, a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm
      have hnt : Nontrivial ↥(P' : Subgroup (↥K ⧸ GLAPPrimeCore 3 ↥K)) :=
        Finite.one_lt_card_iff_nontrivial.1 (by omega)
      obtain ⟨g, hg1⟩ := exists_ne (1 : ↥(P' : Subgroup (↥K ⧸ GLAPPrimeCore 3 ↥K)))
      have hg1' : (g : ↥K ⧸ GLAPPrimeCore 3 ↥K) ≠ 1 := fun h' => hg1 (Subtype.ext h')
      have : (Subgroup.zpowers (g : ↥K ⧸ GLAPPrimeCore 3 ↥K)).Normal := by
        refine ⟨fun n hn t => ?_⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
        have : t * (g : ↥K ⧸ GLAPPrimeCore 3 ↥K) ^ k * t⁻¹ = (g : ↥K ⧸ GLAPPrimeCore 3 ↥K) ^ k := by
          have hc : Commute t ((g : ↥K ⧸ GLAPPrimeCore 3 ↥K) ^ k) := hcen t _
          exact hc.mul_inv_cancel
        rw [this]; exact Subgroup.zpow_mem_zpowers _ _
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.zpowers (g : ↥K ⧸ GLAPPrimeCore 3 ↥K)) with h2 | h2
      · exact hg1' (Subgroup.zpowers_eq_bot.1 h2)
      · have h3 : Nat.card (↥K ⧸ GLAPPrimeCore 3 ↥K) = orderOf (g : ↥K ⧸ GLAPPrimeCore 3 ↥K) := by
          rw [← Nat.card_zpowers, h2, Nat.card_congr (Subgroup.topEquiv).toEquiv]
        have h4 : orderOf (g : ↥K ⧸ GLAPPrimeCore 3 ↥K) ∣ 9 := by
          rw [← hP9, Subgroup.orderOf_coe g]
          exact orderOf_dvd_natCard g
        have := Nat.le_of_dvd (by norm_num) h4
        omega
  have hZ1 : (R ⊓ K) ⊓ dQ K = ⊥ := by
    have h1 := card_sylow_inf_dQ (K := K) (P := R ⊓ K) inf_le_right (hRp.to_le inf_le_left) hR1c
    rw [hcenter, Subgroup.card_bot] at h1
    simp at h1
    exact (Subgroup.card_eq_one).1 h1
  have hR1B : R ⊓ K ≤ B := fun r hr => by
    refine mem_of_cube_centralizes e.Bel (fun E hE hBE => e.SC.2.2 E le_top hE hBE)
      (hR1exp r hr) (fun b hb => ?_)
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hdecR b (hBR hb)
    rw [← mul_assoc, hR1comm r hr r₁ hr₁, mul_assoc, (hcommR r hr r₂ hr₂), ← mul_assoc]
  have hFK : B ⊓ K = R ⊓ K := by
    refine le_antisymm ?_ (le_inf hR1B inf_le_right)
    have hpg : IsPGroup 3 ↥(B ⊓ K) := hBp.to_le inf_le_left
    exact (eq_of_le_sylow (le_inf hR1B inf_le_right) inf_le_right hpg hR1c).symm ▸ le_rfl
  have hfK : IsEkIn 3 2 B (B ⊓ K) :=
    ⟨inf_le_left, isElemAbelian_mono e.Bel inf_le_left, by
      rw [hFK, hR1card]; norm_num⟩
  have haK : IsEkIn 3 2 B (centralizerQuot B K) :=
    ⟨by rw [hAK]; exact inf_le_left, by rw [hAK]; exact isElemAbelian_mono e.Bel inf_le_left,
      by rw [hAK, hD9]; norm_num⟩
  have hinf : centralizerQuot B K ⊓ (B ⊓ K) = ⊥ := by
    rw [hAK, eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hg' := Subgroup.mem_inf.1 hg
    have : g ∈ (R ⊓ K) ⊓ dQ K := ⟨hFK ▸ hg'.2, (Subgroup.mem_inf.1 hg'.1).2⟩
    rw [hZ1] at this
    exact (Subgroup.mem_bot.1 this)
  have hsup : centralizerQuot B K ⊔ (B ⊓ K) = B := by
    have hle : centralizerQuot B K ⊔ (B ⊓ K) ≤ B := sup_le (hAK ▸ inf_le_left) inf_le_left
    have hN : (B ⊓ K) ≤ Subgroup.normalizer (centralizerQuot B K : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hgB : g ∈ B := hg.1
      have hAB : centralizerQuot B K ≤ B := hAK ▸ inf_le_left
      constructor
      · intro hh
        have hc := ea_comm e.Bel hgB (hAB hh)
        have : g * h * g⁻¹ = h := by rw [hc]; group
        rw [this]; exact hh
      · intro hh
        have hc := ea_comm e.Bel hgB (hAB hh)
        have h1 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
        have h2 : g⁻¹ * (g * h * g⁻¹) * g = g * h * g⁻¹ := by
          calc g⁻¹ * (g * h * g⁻¹) * g = g⁻¹ * ((g * h * g⁻¹) * g) := by group
            _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [← hc]
            _ = g * h * g⁻¹ := by group
        rw [← h1, h2]; exact hh
    have hmul := card_sup_mul_card_inf hN
    rw [hinf, Subgroup.card_bot, haK.2.2, hfK.2.2] at hmul
    have h81 : Nat.card ↥(centralizerQuot B K ⊔ (B ⊓ K)) = 81 := by omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h81, hB81])
  exact ⟨hBN, hK34, haK, hfK, hsup, hinf, fun a ha ha1 =>
    isIaFacts_of_inputs hcov h62 i1812 i254
      (fun M _ _ hM Z _ hZ => not_isLThreeFour_quot_of_isLTwoOddPow hM Z hZ) hS hC hB hxB hx1
      hcomp hKM hBN hK34 haK hfK hsup hinf ha ha1 (hkZero K hK a ha ha1)⟩


end CFSG.HardMathSupport.Solomon.UniquenessMaximal
