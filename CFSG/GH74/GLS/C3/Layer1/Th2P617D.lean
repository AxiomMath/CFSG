module

public import CFSG.GH74.GLS.C3.Layer1.Th2P64D
public import CFSG.GH74.GLS.C3.Layer1.Th2P64B

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Obstr52.B_le_centralizer {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) : B ≤ centralizer ({b} : Set G) := by
  obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  exact fun g hg => mem_centralizer_singleton_iff.2 (hBc g hg b h.mem)

theorem Obstr52.range_actOn_eq_top {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (e : kBar J ≃* alternatingGroup (Fin 7)) :
    (actOn e (h.centralizer_le_normalizer hG4 hB)).range = ⊤ := by
  classical
  set hCN := h.centralizer_le_normalizer hG4 hB with hCN_def
  have hBC : B ≤ centralizer ({b} : Set G) := h.B_le_centralizer hB
  have hBN : B ≤ normalizer (J : Set G) := hBC.trans hCN
  obtain ⟨F, t, hF, ht, hdis, hrange⟩ := h.exists_image_B hG4 hB e (le_refl B) hBN
  have htR : t ∈ (actOn e hCN).range := by
    have htmem : t ∈ F ⊔ zpowers t := mem_sup_right (mem_zpowers t)
    rw [← hrange] at htmem
    obtain ⟨⟨g, hg⟩, hgt⟩ := htmem
    exact ⟨⟨g, hBC hg⟩, hgt⟩
  have hJC : J ≤ centralizer ({b} : Set G) := h.comp.1
  have hA : alternatingGroup (Fin 7) ≤ (actOn e hCN).range := by
    intro σ hσ
    obtain ⟨kb, hkb⟩ := e.surjective ⟨σ, hσ⟩
    induction kb using QuotientGroup.induction_on with | H k => ?_
    refine ⟨⟨(k : G), hJC k.2⟩, ?_⟩
    rw [actOn_apply, a7Act_of_mem e k.2]
    exact congrArg Subtype.val hkb
  have hsign_t : Equiv.Perm.sign t = -1 := by
    obtain ⟨a₁, a₂, hne, rfl⟩ := ht
    exact Equiv.Perm.sign_swap hne
  refine eq_top_iff.2 fun σ _ => ?_
  by_cases hσ : Equiv.Perm.sign σ = 1
  · exact hA (Equiv.Perm.mem_alternatingGroup.2 hσ)
  · have hσ' : Equiv.Perm.sign σ = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
      · exact absurd h1 hσ
      · exact h1
    have h1 : σ * t⁻¹ ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hσ', hsign_t]
      decide
    have h2 := hA h1
    have h3 : σ = (σ * t⁻¹) * t := by group
    rw [h3]
    exact Subgroup.mul_mem _ h2 htR


theorem Obstr52.card_centralizer {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (e : kBar J ≃* alternatingGroup (Fin 7)) :
    Nat.card ↥(centralizer ({b} : Set G)) = Nat.card ↥(CxK b J) * 5040 := by
  classical
  set hCN := h.centralizer_le_normalizer hG4 hB with hCN_def
  set φ := actOn e hCN with hφ
  have hker : φ.ker = (CxK b J).subgroupOf (centralizer ({b} : Set G)) := by
    ext ⟨g, hg⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, actOn_eq_one_iff e hCN hg]
    exact ⟨fun hs => ⟨hg, hs⟩, fun hs => hs.2⟩
  have hk : Nat.card ↥((CxK b J).subgroupOf (centralizer ({b} : Set G))) = Nat.card ↥(CxK b J) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : CxK b J ≤ centralizer ({b} : Set G))).toEquiv
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [h.range_actOn_eq_top hG4 hB e, hker, Subgroup.card_top, hk] at hcard
  rw [← hcard, Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]

theorem Obstr52.twoPartCard_centralizer {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (e : kBar J ≃* alternatingGroup (Fin 7)) :
    twoPartCard (centralizer ({b} : Set G)) = 16 * twoPartCard (CxK b J) := by
  have hcard := h.card_centralizer hG4 hB e
  have hpos : Nat.card ↥(CxK b J) ≠ 0 := Nat.card_pos.ne'
  have h5040 : (Nat.factorization 5040) 2 = 4 := by decide +kernel
  unfold twoPartCard
  rw [hcard, Nat.factorization_mul hpos (by norm_num), Finsupp.add_apply, h5040, pow_add]
  ring

theorem Obstr52.exists_sylow {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (e : kBar J ≃* alternatingGroup (Fin 7)) {A : Subgroup G}
    (hAC : A ≤ centralizer ({b} : Set G)) (hA2 : IsPGroup 2 ↥A) :
    ∃ T₁ : Subgroup G, A ≤ T₁ ∧ IsSylowOf 2 T₁ (centralizer ({b} : Set G)) ∧
      Nat.card ↥T₁ = 16 * twoPartCard (CxK b J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁, hAT, hTC, hT2, hidx⟩ := C3.Layer1.P34.exists_sylow_ge hAC hA2
  have hsyl : IsSylowOf 2 T₁ (centralizer ({b} : Set G)) := isSylowOf_iff.2 ⟨hTC, hT2, hidx⟩
  refine ⟨T₁, hAT, hsyl, ?_⟩
  rw [← h.twoPartCard_centralizer hG4 hB e]
  exact hsyl.card_eq


theorem isMaximalClass_of_elementary_four {Q : Subgroup G} (hel : CFSG.IsElementaryAbelian 2 ↥Q)
    (h4 : Nat.card ↥Q = 4) : C3.Layer1.P34.IsMaximalClassTwoGroup ↥Q := by
  have hp : IsPGroup 2 ↥Q := IsPGroup.of_card (n := 2) (by rw [h4]; norm_num)
  have hab : IsMulCommutative ↥Q := hel.toIsMulCommutative
  have hnil : Group.IsNilpotent ↥Q := inferInstance
  have hnt : Nontrivial ↥Q := by
    have : 1 < Nat.card ↥Q := by rw [h4]; norm_num
    exact Finite.one_lt_card_iff_nontrivial.1 this
  refine ⟨hp, hnil, ?_⟩
  have hle : Group.nilpotencyClass ↥Q ≤ 1 := (Group.IsNilpotent.nilpotencyClass_le_one_iff).2 hab
  have hne : Group.nilpotencyClass ↥Q ≠ 0 := by
    intro h0
    have := (Group.nilpotencyClass_zero_iff_subsingleton).1 h0
    exact (not_subsingleton ↥Q) this
  have : Group.nilpotencyClass ↥Q = 1 := le_antisymm hle (Nat.one_le_iff_ne_zero.2 hne)
  rw [this, h4]
  norm_num

theorem isCyclic_or_isMaximalClass_of_card_le_four {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (h4 : Nat.card ↥Q ≤ 4) : IsCyclic ↥Q ∨ C3.Layer1.P34.IsMaximalClassTwoGroup ↥Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
  have hn2 : n ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  interval_cases n
  · left
    have : Nat.card ↥Q = 1 := by simpa using hn
    have : Subsingleton ↥Q := Finite.card_le_one_iff_subsingleton.1 this.le
    infer_instance
  · left
    have h2 : Nat.card ↥Q = 2 := by simpa using hn
    exact @isCyclic_of_prime_card _ _ 2 ⟨Nat.prime_two⟩ h2
  · have h4' : Nat.card ↥Q = 4 := by simpa using hn
    by_cases hsq : ∀ q ∈ Q, q * q = 1
    · right
      exact isMaximalClass_of_elementary_four (Th2.Bal.isElementaryAbelian_two_of_sq Q hsq) h4'
    · left
      push Not at hsq
      obtain ⟨q, hq, hq1⟩ := hsq
      have hdvd : orderOf (⟨q, hq⟩ : ↥Q) ∣ 2 ^ 2 := by
        have := orderOf_dvd_natCard (⟨q, hq⟩ : ↥Q)
        rwa [h4'] at this
      obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hi2 : i = 2 := by
        by_contra hne
        have hi1 : i ≤ 1 := by omega
        apply hq1
        have h3 : (⟨q, hq⟩ : ↥Q) ^ 2 = 1 := by
          have h5 : orderOf (⟨q, hq⟩ : ↥Q) ∣ 2 := by
            rw [hio]
            interval_cases i <;> simp
          exact orderOf_dvd_iff_pow_eq_one.1 h5
        have := congrArg Subtype.val h3
        simpa [sq] using this
      subst hi2
      exact isCyclic_of_orderOf_eq_card _ (by rw [hio, h4']; norm_num)

theorem isCentralInvolution_of_card {b : G} (hb2 : orderOf b = 2) {T₁ : Subgroup G} (hbT : b ∈ T₁)
    (hc : ∀ s ∈ T₁, s * b = b * s) (hcard : Nat.card ↥T₁ = 2 ^ (Nat.card G).factorization 2) :
    IsCentralInvolution b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hb2, Sylow.ofCard T₁ hcard, ?_, ?_⟩
  · rw [Sylow.coe_ofCard]; exact hbT
  · rw [Sylow.coe_ofCard]; exact hc


theorem Obstr52.false_of_isCentralInvolution_of_le_four
    {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hSimple : IsSimpleGroup G)
    (hNonab : ∃ a b : G, a * b ≠ b * a)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hA : Nonempty (kBar J ≃* alternatingGroup (Fin 7)))
    (hq : twoPartCard (CxK b J) ≤ 4) (hc : IsCentralInvolution b) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hfB, hf2, hind⟩ := h.exists_outer_involution hG4 hB
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have hfC : f ∈ centralizer ({b} : Set G) :=
    mem_centralizer_singleton_iff.2 (hBc f hfB b h.mem)
  have hnorm : ∀ c ∈ centralizer ({b} : Set G), ∀ k ∈ J, c * k * c⁻¹ ∈ J := fun c hc k hk =>
    (Subgroup.mem_normalizer_iff.mp (h.normalizes_centralizer hG4 hB c hc) k).mp hk
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 (CMK (centralizer ({b} : Set G)) J)
  have hQcard : Nat.card ↥Q ≤ 4 := by
    have h1 : Nat.card ↥Q = twoPartCard (CxK b J) := hQ.card_eq
    omega
  have hyp : C3.Layer1.Bk.Prop34HypN G b J :=
    { simple := hSimple
      nonab := hNonab
      central := hc
      comp := h.comp
      normal := hnorm
      shape := Or.inr hA
      sylowQ := ⟨Q, hQ, isCyclic_or_isMaximalClass_of_card_le_four hQ.isPGroup hQcard⟩ }
  exact C3.Layer1.Bk.prop34N_false hyp hfC hf2 hind

theorem Obstr52.false_of_isCentralInvolution
    {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J) (hG : C3Hyp G)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hA : Nonempty (kBar J ≃* alternatingGroup (Fin 7)))
    (hq : twoPartCard (CxK b J) ≤ 4) (hc : IsCentralInvolution b) : False :=
  Obstr52.false_of_isCentralInvolution_of_le_four h hG.pRank_eq_four.le
    hG.kproper.1 hG.kproper.2.1 hB hA hq hc

end CFSG.GH74.GLS.Th2.Obs
