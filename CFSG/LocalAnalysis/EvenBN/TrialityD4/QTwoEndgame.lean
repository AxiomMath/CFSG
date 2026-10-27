module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.NotCentral

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem isElemAbelian_W : IsElemAbelian 2 d.W :=
  ⟨⟨⟨fun a b => Subtype.ext (d.mul_comm_of_mem_W a.2 b.2)⟩⟩,
    fun x hx => by rw [sq]; exact d.mul_self_eq_one_of_mem_W hx⟩

include d in
theorem exists_isElemAbelian_of_mul_self {y : X} (hy : y * y = 1) :
    ∃ E : Subgroup X, IsElemAbelian 2 E ∧ y ∈ E ∧ Nat.card E = q ^ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : y = 1
  · subst h1
    exact ⟨d.W, d.isElemAbelian_W, one_mem _, d.card_W⟩
  obtain ⟨g, hg⟩ := d.involution_conj y (orderOf_eq_prime (by rw [sq]; exact hy) h1)
  have hgW : g * y * g⁻¹ ∈ d.W := by
    rcases hg with hg | hg
    · rw [hg]
      exact d.x₆_mem_W 1
    · rw [hg]
      exact d.x₄_mem_W 1
  refine ⟨d.W.map (MulAut.conj g⁻¹).toMonoidHom,
    SectionRank.isElemAbelian_map d.isElemAbelian_W _, ⟨_, hgW, by simp [mul_assoc]⟩, ?_⟩
  rw [card_map_of_injective (MulAut.conj g⁻¹).injective, d.card_W]

end TrialityD4Data

theorem TrialityD4Data.exists_isElemAbelian_le_of_mem {G : Type*} [Group G] {H : Subgroup G}
    {q : ℕ} (d : TrialityD4Data H q) {y : G} (hy : y ∈ H) (hy2 : y * y = 1) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ y ∈ E ∧ E ≤ H ∧ Nat.card E = q ^ 5 := by
  obtain ⟨E, hE, hyE, hcard⟩ := d.exists_isElemAbelian_of_mul_self (y := ⟨y, hy⟩)
    (Subtype.ext hy2)
  exact ⟨E.map H.subtype, SectionRank.isElemAbelian_map hE _, ⟨_, hyE, rfl⟩, map_subtype_le _,
    by rw [card_map_of_injective H.subtype_injective, hcard]⟩

section Generic

variable {G : Type*} [Group G]

theorem le_centralizer_of_isElemAbelian_D4 {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    {y : G} (hy : y ∈ E) : E ≤ centralizer ({y} : Set G) := fun x hx =>
  mem_centralizer_singleton_iff.2 (congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))

theorem two_mul_pow_five_lt_D4 {q : ℕ} (hq : 2 ≤ q) : 2 * q ^ 5 < q ^ 5 * q ^ 5 :=
  Nat.mul_lt_mul_of_pos_right (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hq 5))
    (by positivity)

variable [Finite G]

theorem exists_sylow_eq_of_normalizer_eq_sup_D4 {p : ℕ} [Fact p.Prime] {Q A R : Subgroup G}
    (hQ : IsPGroup p Q) (hN : normalizer (Q : Set G) = A ⊔ Q) (hRA : IsSylowOf p R A)
    (hRQ : R ≤ Q) : ∃ T : Sylow p G, (T : Subgroup G) = Q := by
  have hAN : A ≤ normalizer (Q : Set G) := by
    rw [hN]
    exact le_sup_left
  have hAQ : Q ⊓ A = R := hRA.eq_of_le (le_inf hRQ hRA.le) inf_le_right hQ.to_inf_left
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have hidx : Q.relIndex (A ⊔ Q) = Q.relIndex A :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A Q hAN).toEquiv.symm
  have hQN : IsSylowOf p Q (normalizer (Q : Set G)) := by
    refine isSylowOf_iff.2 ⟨le_normalizer, hQ, ?_⟩
    rw [hN, hidx, ← inf_relIndex_right, hAQ]
    exact (isSylowOf_iff.1 hRA).2.2
  exact Common.exists_sylow_eq_of_isSylowOf_of_normalizer_le hQN le_rfl

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem isSylowOf_yamadaR_centralizer_of_odd (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : Odd f) : IsSylowOf 2 (yamadaR d t) (centralizer ({t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hRQ⟩ := h.exists_isSylowOf_le d
  have hQR : Q = yamadaR d t := (h.isSylowOf_yamadaR d).eq_of_le hRQ
    (h.le_sup_kernel_of_isPGroup d hf hQ.isPGroup hQ.le) hQ.isPGroup
  rwa [hQR] at hQ

theorem isSylowOf_yamadaR_of_le_of_odd (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : Odd f) {H : Subgroup G} (hRH : yamadaR d t ≤ H) (hHC : H ≤ centralizer ({t} : Set G)) :
    IsSylowOf 2 (yamadaR d t) H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (h.isSylowOf_yamadaR_centralizer_of_odd d hf).of_le hRH hHC

theorem exists_sylow_eq_sup_zpowers_of_odd (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : Odd f) {P : Subgroup G} (hP : IsPGroup 2 P) (htN : t ∈ normalizer (P : Set G))
    (hSP : d.S.map L.subtype ≤ P)
    (hN : normalizer ((P ⊔ zpowers t : Subgroup G) : Set G) =
      (centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) ⊔ P) :
    ∃ T : Sylow 2 G, (T : Subgroup G) = P ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)
    with hA
  have htS : t ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
    mem_normalizer_fintype fun n hn => by
      rw [← mem_centralizer_iff.1 h.htL n (map_subtype_le _ hn), mul_inv_cancel_right]
      exact hn
  have htA : zpowers t ≤ A := (zpowers_le).2 ⟨h.t_mem_centralizer, htS⟩
  have hR := yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)
  have hRA : yamadaR d t ≤ A := by
    rw [hR]
    exact sup_le (le_inf (h.S_le_centralizer d) le_normalizer) htA
  have hQ : IsPGroup 2 (P ⊔ zpowers t : Subgroup G) :=
    hP.to_sup_of_normal_left' (IsPGroup.of_card (n := 1) (by rw [h.card_zpowers_t, pow_one]))
      ((zpowers_le).2 htN)
  have hN' : normalizer ((P ⊔ zpowers t : Subgroup G) : Set G) = A ⊔ (P ⊔ zpowers t) := by
    rw [hN, ← sup_assoc, eq_comm, sup_eq_left]
    exact htA.trans le_sup_left
  have hRQ : yamadaR d t ≤ P ⊔ zpowers t := by
    rw [hR]
    exact sup_le_sup_right hSP _
  exact exists_sylow_eq_of_normalizer_eq_sup_D4 hQ hN'
    (h.isSylowOf_yamadaR_of_le_of_odd d hf hRA inf_le_left) hRQ

theorem conj_t_not_mem_of_lt_card (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {X : Subgroup G}
    (hX : ∀ y ∈ X, y * y = 1 → ∃ E : Subgroup G, IsElemAbelian 2 E ∧
      E ≤ centralizer ({y} : Set G) ∧ 2 * (2 ^ f) ^ 5 < Nat.card E)
    (g : G) : g * t * g⁻¹ ∉ X := by
  intro hg
  have hy2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, h.t_mul_t, mul_one,
      mul_inv_cancel]
  obtain ⟨E, hEab, hEC, hEcard⟩ := hX _ hg hy2
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'def
  have hmem : ∀ x ∈ E', ∃ w ∈ E, x = g⁻¹ * w * g := fun x hx => by
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨w, hw, by simp⟩
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE'C : E' ≤ centralizer ({t} : Set G) := fun x hx => by
    obtain ⟨w, hw, rfl⟩ := hmem x hx
    rw [mem_centralizer_singleton_iff]
    have hwt : w * (g * t * g⁻¹) = (g * t * g⁻¹) * w := mem_centralizer_singleton_iff.1 (hEC hw)
    calc g⁻¹ * w * g * t = g⁻¹ * (w * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * w) * g := by rw [hwt]
      _ = t * (g⁻¹ * w * g) := by group
  have hE'ab : IsElemAbelian 2 E' := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu, hua⟩ := hmem a a.2
      obtain ⟨v, hv, hvb⟩ := hmem b b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hua, hvb]
      calc g⁻¹ * u * g * (g⁻¹ * v * g) = g⁻¹ * (u * v) * g := by group
        _ = g⁻¹ * (v * u) * g := by rw [hcomm u hu v hv]
        _ = g⁻¹ * v * g * (g⁻¹ * u * g) := by group
    · obtain ⟨u, hu, rfl⟩ := hmem x hx
      rw [sq, show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, ← sq, hEab.2 u hu,
        mul_one, inv_mul_cancel]
  have hcard : Nat.card E' = Nat.card E := card_map_of_injective (MulAut.conj g⁻¹).injective
  obtain ⟨h1, h2⟩ := h.card_le_of_isElemAbelian d hE'C hE'ab
  omega

theorem false_of_isSylow_sup_zpowers (h : Setup G L f t) {P : Subgroup G}
    (hB : ∃ T : Sylow 2 G, (T : Subgroup G) = P ⊔ zpowers t)
    (htN : t ∈ normalizer (P : Set G)) (htP : t ∉ P)
    (hfus : ∀ g : G, g * t * g⁻¹ ∉ P) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdec : ∀ x ∈ P ⊔ zpowers t, x ∈ P ∨ ∃ p ∈ P, x = p * t := by
    intro x hx
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left P (zpowers t)
      ((zpowers_le).2 htN), Set.mem_mul] at hx
    obtain ⟨p, hp, τ, hτ, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [show m + m = 2 * m by ring, zpow_mul, zpow_two, h.t_mul_t, one_zpow, mul_one]
      exact hp
    · right
      refine ⟨p, hp, ?_⟩
      rw [zpow_add_one, zpow_mul, zpow_two, h.t_mul_t, one_zpow, one_mul]
  have htB : t ∈ P ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hidx : P.relIndex (P ⊔ zpowers t) = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htB⟩, fun b => ?_⟩
    obtain ⟨b, hb⟩ := b
    simp only [mem_subgroupOf, Subgroup.coe_mul]
    rcases hdec b hb with hbP | ⟨p, hp, rfl⟩
    · refine Or.inr ⟨hbP, fun hbt => htP ?_⟩
      have := mul_mem (inv_mem hbP) hbt
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨?_, fun hpt => htP ?_⟩
      · rw [mul_assoc, h.t_mul_t, mul_one]
        exact hp
      · have := mul_mem (inv_mem hp) hpt
        rwa [inv_mul_cancel_left] at this
  have hFT := Common.firstTransferData_of_relIndex_eq_two hB le_sup_left hidx htB htP h.ht
    fun g hg => hfus g⁻¹ (by rwa [inv_inv])
  have := h.isPerfect
  exact CFSG.LocalAnalysis.perfect_first_transfer_exclusion ⟨_, _, _, hFT⟩

theorem false_of_isSylow_sup_zpowers_of_lt_card (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) {P : Subgroup G}
    (hB : ∃ T : Sylow 2 G, (T : Subgroup G) = P ⊔ zpowers t)
    (htN : t ∈ normalizer (P : Set G)) (htP : t ∉ P)
    (hP : ∀ y ∈ P, y * y = 1 → ∃ E : Subgroup G, IsElemAbelian 2 E ∧
      E ≤ centralizer ({y} : Set G) ∧ 2 * (2 ^ f) ^ 5 < Nat.card E) : False :=
  h.false_of_isSylow_sup_zpowers hB htN htP (h.conj_t_not_mem_of_lt_card d hP)

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
