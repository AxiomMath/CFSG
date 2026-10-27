module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51A
public import CFSG.LocalAnalysis.ComponentClassification.Foote5GH74
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Statements

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {S : Subgroup G} {y : G}
    (hy : y ∈ normalizer (S : Set G)) : S.map (MulAut.conj y).toMonoidHom = S := by
  ext a
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (mem_normalizer_iff.mp hy s).mp hs
  · intro ha
    refine ⟨y⁻¹ * a * y, conj_mem_of_mem_normalizer hy ha, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

omit [Finite G] in
theorem conj_mem_commutator_of_mem_normalizer {S : Subgroup G} {y c : G}
    (hy : y ∈ normalizer (S : Set G)) (hc : c ∈ ⁅S, S⁆) : y * c * y⁻¹ ∈ ⁅S, S⁆ := by
  have h1 : (MulAut.conj y).toMonoidHom c ∈ ⁅S, S⁆.map (MulAut.conj y).toMonoidHom :=
    mem_map_of_mem _ hc
  rwa [map_commutator, map_conj_eq_of_mem_normalizer hy, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] at h1

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem three_le_pRank_S : 3 ≤ Open.pRank 2 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrQ : CFSG.Open.pRank 2 Q = 2 := by
    have h1 := h.pRank_Q
    rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h1
  obtain ⟨E, hEQ, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two Q
  rw [hrQ] at hEcard
  have ht2 : t ^ 2 = 1 := by rw [← h.t2]; exact pow_orderOf_eq_one t
  have htE : t ∉ E := fun htE => by
    have h1 : t ∈ Q ⊓ L := mem_inf.mpr ⟨hEQ htE, h.tL⟩
    rw [h.Q_inf_L, mem_bot] at h1
    have h2 := h.t2
    rw [h1, orderOf_one] at h2
    omega
  exact succ_le_open_pRank_of_commute Nat.prime_two hE hEcard
    (fun e he => h.commute_Q_R (hEQ he) h.tR) ht2 htE (hEQ.trans h.QS) h.tS

theorem t_ne_one : t ≠ 1 := fun h1 => by
  have h2 := h.t2
  rw [h1, orderOf_one] at h2
  omega

theorem exists_conj_t_not_mem_R (hB4 : GoldschmidtCorB4) (hST : IsSylowOf 2 S ⊤) :
    ∃ g : G, g⁻¹ * t * g ∈ S ∧ g⁻¹ * t * g ∉ S ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.sec4.simple
  by_contra hno
  have hno' : ∀ g : G, g⁻¹ * t * g ∈ S → g⁻¹ * t * g ∈ S ⊓ L := by
    intro g hg
    by_contra hg'
    exact hno ⟨g, hg, hg'⟩
  have hR2 : IsPGroup 2 ↥(S ⊓ L) := h.R_sylow.isPGroup
  have hinvR : ∀ c : G, ∀ r ∈ S ⊓ L, orderOf r = 2 → c⁻¹ * r * c ∈ S →
      c⁻¹ * r * c ∈ S ⊓ L := by
    intro c r hr hr2 hc
    obtain ⟨k, -, hk⟩ := h.exists_conj_t hr hr2
    have h1 : c⁻¹ * r * c = (k⁻¹ * c)⁻¹ * t * (k⁻¹ * c) := by rw [← hk]; group
    rw [h1] at hc ⊢
    exact hno' _ hc
  have hR : ∀ c : G, (∀ r ∈ S ⊓ L, c⁻¹ * r * c ∈ S) → ∀ r ∈ S ⊓ L, c⁻¹ * r * c ∈ S ⊓ L := by
    intro c hc r hr
    obtain ⟨m, -, ⟨e⟩⟩ := h.exists_dihedral_R
    obtain ⟨a, ha, b, hb, ha2, hb2, rfl⟩ := exists_mul_of_dihedral e hr
    have hinv1 : ∀ d ∈ S ⊓ L, d * d = 1 → c⁻¹ * d * c ∈ S ⊓ L := by
      intro d hd hd2
      by_cases hd1 : d = 1
      · rw [hd1, mul_one, inv_mul_cancel]
        exact one_mem _
      · exact hinvR c d hd (orderOf_eq_prime (by rw [sq]; exact hd2) hd1) (hc d hd)
    rw [show c⁻¹ * (a * b) * c = (c⁻¹ * a * c) * (c⁻¹ * b * c) by group]
    exact mul_mem (hinv1 a ha ha2) (hinv1 b hb hb2)
  have hstrong : ∀ y ∈ normalizer ((S ⊓ L : Subgroup G) : Set G), y ∉ S ⊓ L → orderOf y = 2 →
      ∀ d ∈ S ⊓ L, orderOf d = 2 → ∀ g : G, g⁻¹ * y * g ≠ d := by
    intro y hyN hyR hy2 d hdR hd2 g hgd
    obtain ⟨k, -, hk⟩ := h.exists_conj_t hdR hd2
    have hy2' : IsPGroup 2 (zpowers y) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
    have hRy : IsPGroup 2 ↥(S ⊓ L ⊔ zpowers y) :=
      hR2.to_sup_of_normal_left' hy2' (zpowers_le.mpr hyN)
    obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf hST le_top hRy
    have hcy : c⁻¹ * y * c ∈ S ⊓ L := by
      have hcyS : c⁻¹ * y * c ∈ S := hc y (mem_sup_right (mem_zpowers y))
      have h1 : c⁻¹ * y * c = ((g * k)⁻¹ * c)⁻¹ * t * ((g * k)⁻¹ * c) := by
        rw [← hk, ← hgd]
        group
      rw [h1] at hcyS ⊢
      exact hno' _ hcyS
    have hcR : conjugate (S ⊓ L) c ≤ S ⊓ L := by
      intro w hw
      rw [mem_conjugate_iff] at hw
      have h1 := hR c (fun r hr => hc r (mem_sup_left hr)) _ hw
      rwa [show c⁻¹ * (c * w * c⁻¹) * c = w by group] at h1
    have heq : conjugate (S ⊓ L) c = S ⊓ L :=
      eq_of_le_of_card_ge hcR (card_conjugate_eq_card _ c).ge
    have hyR' : c⁻¹ * y * c ∈ conjugate (S ⊓ L) c := heq.symm ▸ hcy
    rw [mem_conjugate_iff, show c * (c⁻¹ * y * c) * c⁻¹ = y by group] at hyR'
    exact hyR hyR'
  have hncl : normalClosure ((S ⊓ L : Subgroup G) : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (normalClosure ((S ⊓ L : Subgroup G) : Set G)) with h1 | h1
    · have h2 : t ∈ normalClosure ((S ⊓ L : Subgroup G) : Set G) := subset_normalClosure h.tR
      rw [h1, mem_bot] at h2
      exact absurd h2 h.t_ne_one
    · exact h1
  obtain ⟨E, hES, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two S
  have h4 := hB4 G (S ⊓ L) h.isDihedralTwoGroup_R hstrong S (hncl ▸ hST) E hES
    (fun x hx => by rw [← sq]; exact hE.2 x hx)
  have h8 : 2 ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right two_pos h.three_le_pRank_S
  omega

theorem conj_t_mem_R_of_mem_normalizer_Q {n : G} (hnS : n ∈ normalizer (S : Set G))
    (hnQ : n ∈ normalizer (Q : Set G)) : n⁻¹ * t * n ∈ S ⊓ L := by
  have hz1Q : n⁻¹ * z * n ∈ Q := conj_mem_of_mem_normalizer hnQ h.zQ
  have hz12 : orderOf (n⁻¹ * z * n) = 2 := by
    rw [show n⁻¹ * z * n = n⁻¹ * z * n⁻¹⁻¹ by rw [inv_inv], orderOf_conj', h.z2]
  have hz1S : ∀ s ∈ S, s * (n⁻¹ * z * n) = n⁻¹ * z * n * s := by
    intro s hs
    have h1 := h.zS _ ((mem_normalizer_iff.mp hnS s).mp hs)
    calc s * (n⁻¹ * z * n) = n⁻¹ * ((n * s * n⁻¹) * z) * n := by group
      _ = n⁻¹ * (z * (n * s * n⁻¹)) * n := by rw [h1]
      _ = n⁻¹ * z * n * s := by group
  rw [← h.inf_footeF_eq hz1Q hz12 hz1S, footeF_conj h.sec4.huniq, h.footeF_z]
  exact mem_inf.mpr ⟨conj_mem_of_mem_normalizer hnS h.tS, conj_mem_conjugate h.tL n⟩

variable {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}

omit [Finite 𝕊] in
theorem eq_of_psi_eq {a b : G} (ha : a ∈ S ⊓ L) (hb : b ∈ S ⊓ L)
    (hab : psi L ε ⟨a, (mem_inf.mp ha).2⟩ = psi L ε ⟨b, (mem_inf.mp hb).2⟩) : a = b := by
  rw [psi_eq_iff] at hab
  have h1 := eq_one_of_mem_of_odd h.R_sylow.isPGroup (odd_card_oddCoreIn L)
    (mul_mem (inv_mem ha) hb) hab
  rw [inv_mul_eq_one] at h1
  exact h1

omit [Finite 𝕊] in
theorem psi_comm_iff {a b : G} (ha : a ∈ S ⊓ L) (hb : b ∈ S ⊓ L) :
    psi L ε ⟨a, (mem_inf.mp ha).2⟩ * psi L ε ⟨b, (mem_inf.mp hb).2⟩ =
      psi L ε ⟨b, (mem_inf.mp hb).2⟩ * psi L ε ⟨a, (mem_inf.mp ha).2⟩ ↔ a * b = b * a := by
  constructor
  · intro h1
    rw [← map_mul, ← map_mul] at h1
    exact h.eq_of_psi_eq ε (mul_mem ha hb) (mul_mem hb ha) h1
  · intro h1
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h1

include ε in
theorem exists_mul_of_mem_commutator (hD : Foote5AutData 𝕊 Lin) {c : G} (hc : c ∈ ⁅S, S⁆) :
    ∃ q ∈ Q, ∃ r ∈ S ⊓ L, c = q * r := by
  have hle : ⁅S, S⁆ ≤ Q ⊔ (S ⊓ L) := by
    rw [commutator_le]
    intro a ha b hb
    have habS : ⁅a, b⁆ ∈ S := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hinn : actG L ε ⁅a, b⁆ ∈ innAut5 𝕊 := by
      rw [commutatorElement_def, actG_mul ε (h.S_le (mul_mem (mul_mem ha hb) (inv_mem ha)))
        (h.S_le (inv_mem hb)), actG_mul ε (h.S_le (mul_mem ha hb)) (h.S_le (inv_mem ha)),
        actG_mul ε (h.S_le ha) (h.S_le hb), actG_inv ε (h.S_le ha), actG_inv ε (h.S_le hb)]
      exact hD.commutator_mem _ _
    obtain ⟨q, hq, r, hr, hqr⟩ := h.exists_mul_of_inner ε habS hinn
    rw [hqr]
    exact mul_mem (mem_sup_left hq) (mem_sup_right hr)
  have h1 := hle hc
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right Q (S ⊓ L)
    (h.QS.trans h.S_le_normalizer_R)] at h1
  obtain ⟨q, hq, r, hr, hqr⟩ := h1
  exact ⟨q, hq, r, hr, hqr.symm⟩

include ε in
theorem exists_eq_of_mem_commutator_center (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {c : G} (hc : c ∈ ⁅S, S⁆)
    (hcZ : ∀ s ∈ S, s * c = c * s) : ∃ q ∈ Q, c = q ∨ c = q * t := by
  obtain ⟨q, hq, r, hr, rfl⟩ := h.exists_mul_of_mem_commutator ε hD hc
  have hrZ : ∀ r' ∈ S ⊓ L, r * r' = r' * r := by
    intro r' hr'
    have h1 := hcZ r' (mem_inf.mp hr').1
    have h2 := h.commute_Q_R hq hr'
    have h3 : q * (r * r') = q * (r' * r) := by
      calc q * (r * r') = (q * r) * r' := by group
        _ = r' * (q * r) := h1.symm
        _ = (r' * q) * r := by group
        _ = (q * r') * r := by rw [h2]
        _ = q * (r' * r) := by group
    exact mul_left_cancel h3
  rcases h.center_R hna hr hrZ with h1 | h1
  · exact ⟨q, hq, Or.inl (by rw [h1, mul_one])⟩
  · exact ⟨q, hq, Or.inr (by rw [h1])⟩

end Sec5

end CFSG.ComponentClassification.Foote5
