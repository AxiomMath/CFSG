module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open Subgroup

variable {G : Type} [Group G]

theorem centralizer_zpowers_eq (z : G) :
    centralizer ((zpowers z : Subgroup G) : Set G) = centralizer ({z} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem card_modEq_three_of_iterate {α : Type*} [Finite α] (f : α → α)
    (hf : ∀ a, f (f (f a)) = a) : Nat.card α ≡ Nat.card {a // f a = a} [MOD 3] := by
  classical
  have := Fintype.ofFinite α
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) (by
    funext a
    exact hf a)
  rw [Nat.card_eq_fintype_card]
  have h : Nat.card {a // f a = a} = Fintype.card (Function.fixedPoints f) :=
    Nat.card_eq_fintype_card (α := Function.fixedPoints f)
  rw [h]
  exact key

variable [Finite G]

theorem relIndex_centralizer_modEq_one {Q : Subgroup G} {z : G} (hz3 : z ^ 3 = 1)
    (hzQ : z ∈ normalizer (Q : Set G)) (hQ : ¬ 3 ∣ Nat.card Q) :
    (centralizer ({z} : Set G)).relIndex Q ≡ 1 [MOD 3] := by
  have hz3' : z * z * z = 1 := by rw [← pow_three']; exact hz3
  let f : Q → Q := fun q => ⟨z * q * z⁻¹, (mem_normalizer_iff.1 hzQ q).1 q.2⟩
  have hf : ∀ q, f (f (f q)) = q := fun q => by
    apply Subtype.ext
    show z * (z * (z * q * z⁻¹) * z⁻¹) * z⁻¹ = q
    calc _ = (z * z * z) * q * (z * z * z)⁻¹ := by group
      _ = q := by rw [hz3']; group
  have hmod := card_modEq_three_of_iterate f hf
  have hfix : Nat.card {q // f q = q} = Nat.card ↥(centralizer ({z} : Set G) ⊓ Q) := by
    refine Nat.card_congr
      { toFun := fun q => ⟨q.1, mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, q.1.2⟩⟩
        invFun := fun c => ⟨⟨c.1, (mem_inf.1 c.2).2⟩, Subtype.ext ?_⟩
        left_inv := fun q => rfl
        right_inv := fun c => rfl }
    · have h := congrArg Subtype.val q.2
      change z * q.1 * z⁻¹ = q.1 at h
      calc (q.1 : G) * z = z * q.1 * z⁻¹ * z := by rw [h]
        _ = z * q.1 := by group
    · have h := mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).1
      change z * c.1 * z⁻¹ = c.1
      rw [← h]
      group
  rw [hfix, ← relIndex_mul_card (centralizer ({z} : Set G)) Q] at hmod
  have hcop : Nat.gcd 3 (Nat.card ↥(centralizer ({z} : Set G) ⊓ Q)) = 1 := by
    refine (Nat.Coprime.symm ?_)
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => hQ ?_)
    exact h.trans (card_dvd_of_le inf_le_right)
  exact Nat.ModEq.cancel_right_of_coprime hcop (by simpa using hmod)

theorem relIndex_centralizer_le_card_commutator (Q : Subgroup G) (z : G) :
    (centralizer ({z} : Set G)).relIndex Q ≤ Nat.card ↥⁅Q, zpowers z⁆ := by
  classical
  let φ : ↥Q ⧸ (centralizer ({z} : Set G)).subgroupOf Q → ↥⁅Q, zpowers z⁆ :=
    Quotient.lift (fun q : ↥Q =>
      (⟨(q : G) * z * (q : G)⁻¹ * z⁻¹, commutator_mem_commutator q.2 (mem_zpowers z)⟩ :
        ↥⁅Q, zpowers z⁆)) (by
      intro a b hab
      have hab := QuotientGroup.leftRel_apply.mp hab
      rw [mem_subgroupOf, mem_centralizer_singleton_iff] at hab
      apply Subtype.ext
      change (a : G) * z * (a : G)⁻¹ * z⁻¹ = (b : G) * z * (b : G)⁻¹ * z⁻¹
      have e : (b : G) = a * ((a : G)⁻¹ * b) := by group
      have hab' : ((a : G)⁻¹ * b) * z = z * ((a : G)⁻¹ * b) := by
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hab
      calc (a : G) * z * (a : G)⁻¹ * z⁻¹
          = (a : G) * (z * ((a : G)⁻¹ * b)) * ((a : G)⁻¹ * b)⁻¹ * (a : G)⁻¹ * z⁻¹ := by group
        _ = (a : G) * (((a : G)⁻¹ * b) * z) * ((a : G)⁻¹ * b)⁻¹ * (a : G)⁻¹ * z⁻¹ := by
          rw [hab']
        _ = (b : G) * z * (b : G)⁻¹ * z⁻¹ := by group)
  have hφ : Function.Injective φ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    have h := congrArg Subtype.val hab
    change (a : G) * z * (a : G)⁻¹ * z⁻¹ = (b : G) * z * (b : G)⁻¹ * z⁻¹ at h
    rw [QuotientGroup.eq, mem_subgroupOf, mem_centralizer_singleton_iff]
    have h' : (a : G) * z * (a : G)⁻¹ = (b : G) * z * (b : G)⁻¹ := mul_right_cancel h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (a : G)⁻¹ * b * z = (a : G)⁻¹ * ((b : G) * z * (b : G)⁻¹) * b := by group
      _ = (a : G)⁻¹ * ((a : G) * z * (a : G)⁻¹) * b := by rw [h']
      _ = z * ((a : G)⁻¹ * b) := by group
  exact Nat.card_le_card_of_injective φ hφ

theorem relIndex_centralizer_eq_four {Q : Subgroup G} {z : G} (hQ : IsPGroup 2 Q)
    (hz3 : z ^ 3 = 1) (hzQ : z ∈ normalizer (Q : Set G)) (hne : ∃ q ∈ Q, q * z ≠ z * q)
    (hc : Nat.card ↥⁅Q, zpowers z⁆ ≤ 4) : (centralizer ({z} : Set G)).relIndex Q = 4 := by
  have h3 : ¬ 3 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hmod := relIndex_centralizer_modEq_one hz3 hzQ h3
  have hle := (relIndex_centralizer_le_card_commutator Q z).trans hc
  have h1 : (centralizer ({z} : Set G)).relIndex Q ≠ 1 := by
    rw [Ne, relIndex_eq_one]
    obtain ⟨q, hq, hqz⟩ := hne
    exact fun h => hqz (mem_centralizer_singleton_iff.1 (h hq))
  unfold Nat.ModEq at hmod
  omega

theorem relIndex_centralizer_eq_four_of_section {Q A₀ : Subgroup G} {z : G} (hQ : IsPGroup 2 Q)
    (hz3 : z ^ 3 = 1) (hzQ : z ∈ normalizer (Q : Set G)) (hAc : A₀ ≤ centralizer ({z} : Set G))
    (h8 : A₀.relIndex Q = 8) (hne : ∃ q ∈ Q, q * z ≠ z * q) :
    (centralizer ({z} : Set G)).relIndex Q = 4 := by
  have h3 : ¬ 3 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hmod := relIndex_centralizer_modEq_one hz3 hzQ h3
  have hdvd : (centralizer ({z} : Set G)).relIndex Q ∣ 8 := h8 ▸ relIndex_dvd_of_le_left Q hAc
  have h1 : (centralizer ({z} : Set G)).relIndex Q ≠ 1 := by
    rw [Ne, relIndex_eq_one]
    obtain ⟨q, hq, hqz⟩ := hne
    exact fun h => hqz (mem_centralizer_singleton_iff.1 (h hq))
  have hle : (centralizer ({z} : Set G)).relIndex Q ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  unfold Nat.ModEq at hmod
  interval_cases h : (centralizer ({z} : Set G)).relIndex Q <;> simp_all

theorem relIndex_centralizer_le_of_forall_mul {Q U : Subgroup G} {z : G} (hUQ : U ≤ Q)
    (h : ∀ q ∈ Q, ∃ u ∈ U, u⁻¹ * q ∈ centralizer ({z} : Set G)) :
    (centralizer ({z} : Set G)).relIndex Q ≤ (centralizer ({z} : Set G)).relIndex U := by
  classical
  let ψ : ↥U ⧸ (centralizer ({z} : Set G)).subgroupOf U →
      ↥Q ⧸ (centralizer ({z} : Set G)).subgroupOf Q :=
    Quotient.lift (fun u : ↥U => ((⟨(u : G), hUQ u.2⟩ : ↥Q) :
      ↥Q ⧸ (centralizer ({z} : Set G)).subgroupOf Q)) (by
      intro a b hab
      have hab := QuotientGroup.leftRel_apply.mp hab
      rw [mem_subgroupOf] at hab
      change ((⟨(a : G), hUQ a.2⟩ : ↥Q) : ↥Q ⧸ (centralizer ({z} : Set G)).subgroupOf Q) =
        ((⟨(b : G), hUQ b.2⟩ : ↥Q) : ↥Q ⧸ (centralizer ({z} : Set G)).subgroupOf Q)
      rw [QuotientGroup.eq, mem_subgroupOf]
      simpa using hab)
  have hψ : Function.Surjective ψ := by
    intro w
    induction w using QuotientGroup.induction_on with | H q => ?_
    obtain ⟨u, hu, huq⟩ := h q q.2
    refine ⟨((⟨u, hu⟩ : ↥U) : ↥U ⧸ (centralizer ({z} : Set G)).subgroupOf U), ?_⟩
    change ((⟨u, hUQ hu⟩ : ↥Q) : ↥Q ⧸ (centralizer ({z} : Set G)).subgroupOf Q) = (q : _)
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa using huq
  exact Nat.card_le_card_of_surjective ψ hψ

theorem relIndex_centralizer_le_mul {O S : Subgroup G} (z : G) (hOS : O ≤ S) :
    (centralizer ({z} : Set G)).relIndex S ≤
      (centralizer ({z} : Set G)).relIndex O * O.relIndex S := by
  have h1 : (centralizer ({z} : Set G) ⊓ O).relIndex S =
      (centralizer ({z} : Set G)).relIndex O * O.relIndex S := by
    rw [← relIndex_mul_relIndex (centralizer ({z} : Set G) ⊓ O) O S inf_le_right hOS,
      inf_relIndex_right]
  rw [← h1]
  haveI := isFiniteRelIndex_of_finiteIndex (H := centralizer ({z} : Set G) ⊓ O) (K := S)
  exact relIndex_le_of_le_left inf_le_left relIndex_ne_zero

theorem relIndex_centralizer_le_card_of_conj_mem (Q : Subgroup G) (z : G) (A : Set G)
    (hA : ∀ q ∈ Q, q * z * q⁻¹ ∈ A) :
    (centralizer ({z} : Set G)).relIndex Q ≤ Nat.card A := by
  classical
  let φ : ↥Q ⧸ (centralizer ({z} : Set G)).subgroupOf Q → A :=
    Quotient.lift (fun q : ↥Q => (⟨(q : G) * z * (q : G)⁻¹, hA q q.2⟩ : A)) (by
      intro a b hab
      have hab := QuotientGroup.leftRel_apply.mp hab
      rw [mem_subgroupOf, mem_centralizer_singleton_iff] at hab
      apply Subtype.ext
      change (a : G) * z * (a : G)⁻¹ = (b : G) * z * (b : G)⁻¹
      have hab' : ((a : G)⁻¹ * b) * z = z * ((a : G)⁻¹ * b) := by
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hab
      calc (a : G) * z * (a : G)⁻¹
          = (a : G) * (z * ((a : G)⁻¹ * b)) * ((a : G)⁻¹ * b)⁻¹ * (a : G)⁻¹ := by group
        _ = (a : G) * (((a : G)⁻¹ * b) * z) * ((a : G)⁻¹ * b)⁻¹ * (a : G)⁻¹ := by rw [hab']
        _ = (b : G) * z * (b : G)⁻¹ := by group)
  have hφ : Function.Injective φ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    have h' : (a : G) * z * (a : G)⁻¹ = (b : G) * z * (b : G)⁻¹ := congrArg Subtype.val hab
    rw [QuotientGroup.eq, mem_subgroupOf, mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (a : G)⁻¹ * b * z = (a : G)⁻¹ * ((b : G) * z * (b : G)⁻¹) * b := by group
      _ = (a : G)⁻¹ * ((a : G) * z * (a : G)⁻¹) * b := by rw [h']
      _ = z * ((a : G)⁻¹ * b) := by group
  exact Nat.card_le_card_of_injective φ hφ

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I
