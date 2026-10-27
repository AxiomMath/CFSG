module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Index

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

private theorem hall_two_p {L T : Subgroup G} {p : ℕ} (hp : p.Prime) (hTL : T ≤ L)
    (hT : ∀ q : ℕ, q.Prime → q ∣ Nat.card T → q = 2 ∨ q = p) (hL : Group.IsSolvable ↥L) :
    ∃ K₀ : Subgroup G, K₀ ≤ L ∧ T ≤ K₀ ∧
      (∀ q : ℕ, q.Prime → q ∣ Nat.card K₀ → q = 2 ∨ q = p) ∧
      ∀ q : ℕ, q.Prime → q ∣ K₀.relIndex L → q ≠ 2 ∧ q ≠ p := by
  let π' : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨p, hp⟩}
  obtain ⟨H, hH, hTH⟩ := CFSG.SolvableHall.solvable_hall_containment hL π' (T.subgroupOf L) (by
    intro q hq
    have hcard : Nat.card (T.subgroupOf L) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
    rw [hcard] at hq
    rcases hT q q.2 hq with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h))
  refine ⟨H.map L.subtype, Subgroup.map_subtype_le H, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hTL hx⟩, hTH (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  · intro q hq hdvd
    rw [Subgroup.card_map_of_injective L.subtype_injective] at hdvd
    have := hH.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hdvd
    rcases this with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · intro q hq hdvd
    have e : (H.map L.subtype).relIndex L = H.index := by
      show ((H.map L.subtype).comap L.subtype).index = H.index
      rw [Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    rw [e] at hdvd
    have := hH.p_in_pi_of_p_dvd_index ⟨q, hq⟩ hdvd
    exact ⟨fun h2 => this (Or.inl (Subtype.ext h2)), fun hpq => this (Or.inr (Subtype.ext hpq))⟩

private theorem exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {K U : Subgroup G} (hUK : U ≤ K)
    (hU : IsPGroup p U) : ∃ S : Subgroup G, IsSylowOf p S K ∧ U ≤ S := by
  have hU' : IsPGroup p (U.subgroupOf K) := hU.comap_subtype
  obtain ⟨Q, hQ⟩ := hU'.exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, ?_⟩
  intro u hu
  exact ⟨⟨u, hUK hu⟩, hQ (by simpa [Subgroup.mem_subgroupOf] using hu), rfl⟩

private theorem eq_pow_mul_pow_of_prime_dvd' {n p q : ℕ} (hn : n ≠ 0) (hpq : p ≠ q)
    (h : ∀ r : ℕ, r.Prime → r ∣ n → r = p ∨ r = q) :
    n = p ^ n.factorization p * q ^ n.factorization q := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod_of_support_subset _ (s := {p, q}) ?_ _ (fun _ _ => pow_zero _),
    Finset.prod_pair hpq]
  intro r hr
  rw [Nat.support_factorization] at hr
  have := h r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
  simpa using this

private theorem mul_eq_of_two_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K₀ Y S : Subgroup G}
    (hπ : ∀ q : ℕ, q.Prime → q ∣ Nat.card K₀ → q = 2 ∨ q = p)
    (hY : IsSylowOf 2 Y K₀) (hS : IsSylowOf p S K₀) :
    ∀ w ∈ K₀, ∃ y ∈ Y, ∃ s ∈ S, w = y * s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have hcardK : Nat.card K₀ = Nat.card Y * Nat.card S := by
    rw [hY.card_eq, hS.card_eq]
    exact eq_pow_mul_pow_of_prime_dvd' Nat.card_pos.ne' (Ne.symm hp2) hπ
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card S) := by
    rw [hY.card_eq, hS.card_eq]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hbot : Y ⊓ S = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  let f : Y × S → K₀ := fun x =>
    ⟨(x.1 : G) * (x.2 : G), mul_mem (hY.le x.1.2) (hS.le x.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨y, q⟩ ⟨y', q'⟩ h
    have h1 : (y : G) * q = y' * q' := congrArg Subtype.val h
    have h2 : (y' : G)⁻¹ * y = q' * (q : G)⁻¹ := by
      calc (y' : G)⁻¹ * y = (y' : G)⁻¹ * (y * q) * (q : G)⁻¹ := by group
        _ = (y' : G)⁻¹ * (y' * q') * (q : G)⁻¹ := by rw [h1]
        _ = q' * (q : G)⁻¹ := by group
    have hmemY : (y' : G)⁻¹ * y ∈ Y := mul_mem (inv_mem y'.2) y.2
    have hmemQ : (y' : G)⁻¹ * y ∈ S := h2 ▸ mul_mem q'.2 (inv_mem q.2)
    have h3 : (y' : G)⁻¹ * y = 1 := by
      have : (y' : G)⁻¹ * y ∈ Y ⊓ S := ⟨hmemY, hmemQ⟩
      rwa [hbot, Subgroup.mem_bot] at this
    have hyy : (y : G) = y' := by
      have := congrArg (fun z => (y' : G) * z) h3
      simpa using this
    have hqq : (q : G) = q' := by
      rw [h3] at h2
      have : (q' : G) * (q : G)⁻¹ = 1 := h2.symm
      exact (mul_inv_eq_one.1 this).symm
    exact Prod.ext (Subtype.ext hyy) (Subtype.ext hqq)
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_prod, ← hcardK]
  intro w hw
  obtain ⟨⟨y, s⟩, hys⟩ := hbij.2 ⟨w, hw⟩
  exact ⟨y, y.2, s, s.2, (congrArg Subtype.val hys).symm⟩

theorem exists_permutable_conj_sylow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L Y V U : Subgroup G} (hLsolv : Group.IsSolvable ↥L)
    (hY : CFSG.ABGLocalTools.IsSylowOf 2 Y L) (hV : CFSG.ABGLocalTools.IsSylowOf p V L)
    (hUL : U ≤ L) (hUp : IsPGroup p U) (hUY : U ≤ normalizer (Y : Set G)) :
    ∃ l ∈ L, U ≤ V.map (MulAut.conj l).toMonoidHom ∧
      ∀ w ∈ Y ⊔ V.map (MulAut.conj l).toMonoidHom,
        ∃ y ∈ Y, ∃ s ∈ V.map (MulAut.conj l).toMonoidHom, w = y * s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have hYL : Y ≤ L := hY.le
  have hTL : Y ⊔ U ≤ L := sup_le hYL hUL
  obtain ⟨a, ha⟩ := hY.isPGroup.exists_card_eq
  obtain ⟨b, hb⟩ := hUp.exists_card_eq
  have hcardT : Nat.card ↥(Y ⊔ U) ∣ Nat.card Y * Nat.card U := by
    have h := card_sup_mul_card_inf_of_le_normalizer hUY
    exact ⟨Nat.card ↥(Y ⊓ U), h.symm⟩
  have hT2p : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(Y ⊔ U) → q = 2 ∨ q = p := by
    intro q hq hdvd
    have h := hdvd.trans hcardT
    rw [ha, hb] at h
    rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h))
  obtain ⟨K₀, hK₀L, hTK₀, hK₀π, hK₀idx⟩ := hall_two_p hp hTL hT2p hLsolv
  have hYK₀ : Y ≤ K₀ := le_sup_left.trans hTK₀
  have hUK₀ : U ≤ K₀ := le_sup_right.trans hTK₀
  obtain ⟨S, hSK₀, hUS⟩ := exists_isSylowOf_ge hUK₀ hUp
  have hYsyl : IsSylowOf 2 Y K₀ := hY.of_le hYK₀ hK₀L
  have hSL : IsSylowOf p S L := by
    rw [isSylowOf_iff] at hSK₀ ⊢
    obtain ⟨hSle, hSp, hdvd⟩ := hSK₀
    refine ⟨hSle.trans hK₀L, hSp, fun h => ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex S K₀ L hSle hK₀L] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hdvd h
    · exact (hK₀idx p hp h).2 rfl
  obtain ⟨l, hlL, hl⟩ := IsSylowOf.exists_mem_conj hV hSL
  have hSeq : S = V.map (MulAut.conj l).toMonoidHom := by
    ext x
    rw [hl x, Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  refine ⟨l, hlL, hSeq ▸ hUS, ?_⟩
  rw [← hSeq]
  intro w hw
  exact mul_eq_of_two_p hp2 hK₀π hYsyl hSK₀ w (sup_le hYK₀ hSK₀.le hw)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
