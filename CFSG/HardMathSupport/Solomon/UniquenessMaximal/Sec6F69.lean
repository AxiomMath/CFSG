module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FRStruct
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FCore69
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FM1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FNotL2
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FQuat

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isThreeOnePlusFour_of_equiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : IsThreeOnePlusFour Q) : IsThreeOnePlusFour P := by
  obtain ⟨hc, hexp, hz, hcomm⟩ := h
  have hcen : ∀ a : P, a ∈ Subgroup.center P ↔ e a ∈ Subgroup.center Q := by
    intro a
    rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro h g
      have := congrArg e (h (e.symm g))
      simpa using this
    · intro h g
      apply e.injective
      simpa using h (e g)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv]; exact hc
  · intro g
    apply e.injective
    rw [map_pow, map_one]; exact hexp _
  · rw [← hz]
    have : (Subgroup.center P).map e.toMonoidHom = Subgroup.center Q := Subgroup.map_center_eq e
    rw [← this, Subgroup.card_map_of_injective e.injective]
  · intro a c
    rw [hcen]
    simpa using hcomm (e a) (e c)


theorem hInn_of_out (hOut : InputOutON) {B K : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hON : IsHatON (↥K ⧸ GLAPPrimeCore 3 ↥K)) :
    ∀ b ∈ B, ∃ k ∈ K, ∀ y ∈ K, b * y * b⁻¹ * (k * y * k⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 K := by
  intro b hb
  set Kb := ↥K ⧸ GLAPPrimeCore 3 ↥K with hKb
  set σ := LocalBalance.barAut 3 K ⟨b, hBN hb⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨b, hBN hb⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 := by
      apply Subtype.ext
      exact hBel.2 b hb
    rw [this, map_one]
  have hidx := hOut Kb hON
  set N := (MulAut.conj : Kb →* MulAut Kb).range with hN
  have hσN : σ ∈ N := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h2
    · have : N = ⊤ := Subgroup.index_eq_one.1 h1
      rw [this]; exact Subgroup.mem_top _
    · have hsq := Subgroup.sq_mem_of_index_two h2 σ
      have : σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      rw [this, hσ3, one_mul]
      exact N.inv_mem hsq
  obtain ⟨kb, hkb⟩ := hσN
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kb
  refine ⟨(k : G), k.2, fun y hy => ?_⟩
  have h1 := congrArg (fun τ : MulAut Kb => τ (QuotientGroup.mk ⟨y, hy⟩)) hkb
  simp only [MulAut.conj_apply] at h1
  rw [hσ, LocalBalance.barAut_mk] at h1
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
  have h2 : (k * ⟨y, hy⟩ * k⁻¹)⁻¹ * (K.normalizerMonoidHom ⟨b, hBN hb⟩ ⟨y, hy⟩) ∈ GLAPPrimeCore 3 ↥K := h1
  have h3 : (((k * ⟨y, hy⟩ * k⁻¹)⁻¹ * (K.normalizerMonoidHom ⟨b, hBN hb⟩ ⟨y, hy⟩) : ↥K) : G) ∈
      GLAPPrimeCoreOf 3 K := Subgroup.mem_map.2 ⟨_, h2, rfl⟩
  have hnorm : ((K.normalizerMonoidHom ⟨b, hBN hb⟩ ⟨y, hy⟩ : ↥K) : G) = b * y * b⁻¹ := rfl
  have h4 : ((k : G) * y * (k : G)⁻¹)⁻¹ * (b * y * b⁻¹) ∈ GLAPPrimeCoreOf 3 K := by
    simpa [hnorm, mul_assoc] using h3
  have hU : ∀ u ∈ GLAPPrimeCoreOf 3 K, ∀ g ∈ K, g * u * g⁻¹ ∈ GLAPPrimeCoreOf 3 K := by
    intro u hu g hg
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 K hg) u).1 hu
  have h5 := hU _ h4 ((k : G) * y * (k : G)⁻¹) (K.mul_mem (K.mul_mem k.2 hy) (K.inv_mem k.2))
  have : ((k : G) * y * (k : G)⁻¹) * (((k : G) * y * (k : G)⁻¹)⁻¹ * (b * y * b⁻¹)) *
      ((k : G) * y * (k : G)⁻¹)⁻¹ = (b * y * b⁻¹) * ((k : G) * y * (k : G)⁻¹)⁻¹ := by group
  rw [this] at h5
  exact h5


theorem lemma69 (hONG : InputONGroup) (h62 : Lemma62Stmt) (hOut : InputOutON) (hSyl : InputSylowON)
    (h2325 : Input23_25_2) (h66 : Lemma66) (hS : GLStanding G 4 3) (hC : GLCaseFour G 3)
    {B : Subgroup G} (hB : IsExtremal B) {K : Subgroup G} (hK : IsHSet B K) :
    ¬ IsHatON (↥K ⧸ GLAPPrimeCore 3 ↥K) := by
  intro hON
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨x, hxB, hx1, hcomp⟩, -, hKM⟩ := hK
  obtain ⟨hB1, b, L, A, hw⟩ := hB.exists_witness
  have e := exists_extCtx hS hC hB1 hw
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := by
    rcases h62 G 4 hS hC B hB x hxB hx1 K hcomp with h | h
    · exact h
    · exact absurd h (not_isLTwoOddPow_hatON hONG hON)
  have hxC : B ≤ Subgroup.centralizer ({x} : Set G) := fun c hc => by
    rw [Subgroup.mem_centralizer_singleton_iff]; exact ea_comm e.Bel hc hxB
  have hKC : K ≤ Subgroup.centralizer ({x} : Set G) := hcomp.1
  have hxD : x ∈ dQ K := by
    refine ⟨hBN hxB, le_normalizer_glaPPrimeCoreOf_of_le_normalizer hBN hxB, fun y hy => ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hKC hy)
    have h1 : y * x * y⁻¹ * x⁻¹ = 1 := by
      rw [this]; group
    rw [h1]; exact one_mem _
  have hSCx : IsSCp 3 (Subgroup.centralizer ({x} : Set G)) B :=
    ⟨hxC, e.Bel, fun E _ hE hBE => e.SC.2.2 E le_top hE hBE⟩
  have hB81 : Nat.card B = 81 := e.Bc
  have hD3 : Nat.card ↥(B ⊓ dQ K) = 3 := by
    have hrel : ¬ (dQ K).relIndex B ≤ 9 := fun h =>
      hKM (le_glbCore_of_gammaL hS hB1 hBN (h2325 G _ K B hcomp hON hSCx hBN h))
    have hmul := Subgroup.relIndex_mul_card (dQ K) B
    rw [inf_comm] at hmul
    have hdvd : (dQ K).relIndex B ∣ 81 := ⟨Nat.card ↥(B ⊓ dQ K), by rw [← hB81, ← hmul]⟩
    have hx3 : Nat.card ↥(Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (e.Bel.2 x hxB) hx1]
    have hle : Subgroup.zpowers x ≤ B ⊓ dQ K := le_inf (Subgroup.zpowers_le.2 hxB) (Subgroup.zpowers_le.2 hxD)
    have hge : 3 ≤ Nat.card ↥(B ⊓ dQ K) := hx3 ▸ Subgroup.card_le_of_le hle
    have h27 : (dQ K).relIndex B ≤ 27 := by
      by_contra hcon
      replace hcon := not_le.1 hcon
      have : 28 * 3 ≤ (dQ K).relIndex B * Nat.card ↥(B ⊓ dQ K) := Nat.mul_le_mul hcon hge
      omega
    have hr : (dQ K).relIndex B = 27 := by
      have hd : (dQ K).relIndex B ∈ Nat.divisors 81 := by simp [hdvd]
      have : Nat.divisors 81 = {1, 3, 9, 27, 81} := by decide
      rw [this] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      omega
    rw [hr] at hmul
    omega
  have hInn := hInn_of_out hOut e.Bel hBN hON
  have hBp : IsPGroup 3 ↥B := IsPGroup.of_card (n := 4) (by rw [hB81]; norm_num)
  obtain ⟨R, hBR, hRp, hRY, hR1c, hcommR, hdecR, hN1, hN2⟩ := exists_rStruct hBp hBN hInn
  obtain ⟨P', ⟨eP⟩⟩ := sylow_equiv_sylowBar (K := K) (P := R ⊓ K) inf_le_right
    (hRp.to_le inf_le_left) hR1c
  obtain ⟨hR1card, hR1exp, hR1z, hR1comm⟩ := isThreeOnePlusFour_of_equiv eP (hSyl _ hON P')
  have hZeq : (R ⊓ K) ⊓ (R ⊓ dQ K) = (R ⊓ K) ⊓ dQ K := by
    ext g; simp only [Subgroup.mem_inf]; tauto
  have hZc : Nat.card ↥((R ⊓ K) ⊓ (R ⊓ dQ K)) = 3 := by
    rw [hZeq, card_sylow_inf_dQ inf_le_right (hRp.to_le inf_le_left) hR1c]
    have hc : Nat.card (Subgroup.center (↥K ⧸ GLAPPrimeCore 3 ↥K)) = 3 := hON.2.1
    rw [hc, Nat.Prime.factorization_self Nat.prime_three]; norm_num
  have hZcent : ∀ z ∈ (R ⊓ K) ⊓ (R ⊓ dQ K), ∀ r ∈ R ⊓ K, z * r = r * z := fun z hz r hr =>
    (hcommR r hr z (Subgroup.mem_inf.1 hz).2).symm
  have hCc : Nat.card ↥((Subgroup.center ↥(R ⊓ K)).map (R ⊓ K).subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (R ⊓ K).subtype_injective]; exact hR1z
  have hZle : (R ⊓ K) ⊓ (R ⊓ dQ K) ≤ (Subgroup.center ↥(R ⊓ K)).map (R ⊓ K).subtype := by
    intro z hz
    refine Subgroup.mem_map.2 ⟨⟨z, (Subgroup.mem_inf.1 hz).1⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro r
    exact Subtype.ext (hZcent z hz r r.2).symm
  have hZC : (R ⊓ K) ⊓ (R ⊓ dQ K) = (Subgroup.center ↥(R ⊓ K)).map (R ⊓ K).subtype :=
    Subgroup.eq_of_le_of_card_ge hZle (by rw [hZc, hCc])
  refine core69 (B := B) (R₁ := R ⊓ K) (R₂ := R ⊓ dQ K) (Z := (R ⊓ K) ⊓ (R ⊓ dQ K)) hB81 e.Bel
    (fun E hE hBE => e.SC.2.2 E le_top hE hBE) hR1card (fun g hg => ?_) inf_le_left hZc hZcent
    (fun z hz hzc => ?_) (fun a ha c hc => ?_) hcommR rfl (fun b hb => hdecR b (hBR hb))
    (hBR.trans hN2) ?_ (fun B₁ hB₁R hB₁N hc => ?_)
  · have := hR1exp ⟨g, hg⟩
    exact congrArg Subtype.val this
  · rw [hZC]
    exact Subgroup.mem_map.2 ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun r => Subtype.ext (hzc r r.2).symm, rfl⟩
  · have h1 := hR1comm ⟨a, ha⟩ ⟨c, hc⟩
    rw [hZC]
    exact Subgroup.mem_map.2 ⟨_, h1, by simp [commutatorElement_def]⟩
  · have : B ⊓ (R ⊓ dQ K) = B ⊓ dQ K := by
      ext g; simp only [Subgroup.mem_inf]; constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hBR h1, h3⟩
    rw [this]; exact hD3
  · exact lemma66_transport h66 hS hC hB1 hw B₁ hB₁N (hRp.to_le (hB₁R.trans inf_le_left)) hc


end CFSG.HardMathSupport.Solomon.UniquenessMaximal
