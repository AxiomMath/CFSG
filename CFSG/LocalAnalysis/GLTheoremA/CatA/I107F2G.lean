module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.GLTheoremA.OR107

theorem isCyclic_quotient {A : Type*} [Group A] {J S : Subgroup A} (hN : (J.subgroupOf S).Normal)
    (hcyc : ∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) : IsCyclic (S ⧸ J.subgroupOf S) := by
  obtain ⟨g, hg, hk⟩ := hcyc
  refine ⟨⟨QuotientGroup.mk (⟨g, hg⟩ : S), fun x => ?_⟩⟩
  induction x using QuotientGroup.induction_on with
  | H s =>
    obtain ⟨k, hks⟩ := hk s s.2
    refine ⟨-k, ?_⟩
    show (QuotientGroup.mk (⟨g, hg⟩ : S) : S ⧸ J.subgroupOf S) ^ (-k) = QuotientGroup.mk s
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [zpow_neg] using hks

theorem card_le_card_inf_mul_of_cyclic {A : Type*} [Group A] {p : ℕ} (hp : p.Prime)
    {J S E : Subgroup A} (hN : (J.subgroupOf S).Normal)
    (hcyc : ∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) (hES : E ≤ S)
    (hE : ∀ e ∈ E, e ^ p = 1) : Nat.card E ≤ Nat.card ↥(E ⊓ J) * p := by
  haveI := isCyclic_quotient hN hcyc
  let π : ↥E →* S ⧸ J.subgroupOf S :=
    (QuotientGroup.mk' (J.subgroupOf S)).comp (Subgroup.inclusion hES)
  have hker : π.ker = J.subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    simp only [π, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hrange : Nat.card π.range ≤ p := by
    obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := π.range)
    have hyp : y ^ p = 1 := by
      obtain ⟨_, e, rfl⟩ := y
      apply Subtype.ext
      show (π e) ^ p = 1
      rw [← map_pow, show e ^ p = 1 from Subtype.ext (hE e e.2), map_one]
    have htop : (Subgroup.zpowers y : Subgroup π.range) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact hy x
    have hc : Nat.card π.range = orderOf y := by
      rw [← Nat.card_zpowers, htop, Subgroup.card_top]
    rw [hc]
    exact orderOf_le_of_pow_eq_one hp.pos hyp
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv, hker] at hlag
  have hinf : Nat.card ↥(J.subgroupOf E) = Nat.card ↥(E ⊓ J) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hlag, hinf, mul_comm]
  exact Nat.mul_le_mul_left _ hrange

theorem le_of_forall_eq_mul {A : Type*} [Group A] {p d : ℕ} (hpd : Nat.Coprime p d)
    {J S E : Subgroup A} (hJS : J ≤ S) (hN : (J.subgroupOf S).Normal)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ J) (hES : E ≤ S)
    (hE : ∀ e ∈ E, e ^ p = 1)
    (hdec : ∀ e ∈ E, ∃ u ∈ J, ∃ f : A, f ^ d = 1 ∧ e = u * f) : E ≤ J := by
  intro e he
  obtain ⟨u, hu, f, hfd, rfl⟩ := hdec e he
  have hfS : f ∈ S := by
    have := S.mul_mem (S.inv_mem (hJS hu)) (hES he)
    simpa using this
  haveI := hN
  let q : S →* S ⧸ J.subgroupOf S := QuotientGroup.mk' (J.subgroupOf S)
  have hqu : q ⟨u, hJS hu⟩ = 1 := by
    simp only [q, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hu
  have hqf_p : q ⟨f, hfS⟩ ^ p = 1 := by
    have h1 : q ⟨u * f, hES he⟩ ^ p = 1 := by
      rw [← map_pow]
      have : (⟨u * f, hES he⟩ : S) ^ p = 1 := Subtype.ext (hE _ he)
      rw [this, map_one]
    have h2 : q ⟨u * f, hES he⟩ = q ⟨u, hJS hu⟩ * q ⟨f, hfS⟩ := by
      rw [← map_mul]
      rfl
    rwa [h2, hqu, one_mul] at h1
  have hqf_d : q ⟨f, hfS⟩ ^ d = 1 := by
    rw [← map_pow]
    have : (⟨f, hfS⟩ : S) ^ d = 1 := Subtype.ext hfd
    rw [this, map_one]
  have hqf : q ⟨f, hfS⟩ = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hqf_p, hqf_d⟩
    rwa [Nat.Coprime.gcd_eq_one hpd, pow_one] at this
  have hfJ : f ∈ J := by
    simpa [q, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] using hqf
  exact J.mul_mem hu hfJ

theorem commutator_mem_of_cyclic {A : Type*} [Group A] {J S : Subgroup A}
    (hN : (J.subgroupOf S).Normal) (hcyc : ∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) :
    ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ J := by
  haveI := isCyclic_quotient hN hcyc
  letI : CommGroup (S ⧸ J.subgroupOf S) := IsCyclic.commGroup
  intro a ha b hb
  have h : (QuotientGroup.mk (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : S)⁻¹ * (⟨b, hb⟩ : S)⁻¹ : S) :
      S ⧸ J.subgroupOf S) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, mul_comm (QuotientGroup.mk (⟨a, ha⟩ : S) : S ⧸ J.subgroupOf S),
      mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  exact h

theorem pow_eq_one_of_mem_closure {A : Type*} [Group A] {F : Set A} {f₀ : A}
    (hF : ∀ f ∈ F, f ∈ Subgroup.zpowers f₀) {d : ℕ} (hd : ∀ f ∈ F, f ^ d = 1) {x : A}
    (hx : x ∈ Subgroup.closure F) : x ^ d = 1 := by
  have hle : Subgroup.closure F ≤ Subgroup.zpowers f₀ := (Subgroup.closure_le _).2 hF
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hd x hx
  | one => exact one_pow d
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hle hx)
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hle hy)
    rw [(Commute.zpow_zpow_self f₀ a b).mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem exists_zpow_mul_mem {A : Type*} [Group A] {J : Subgroup A} [J.Normal] {g x : A}
    (hx : x ∈ (Subgroup.zpowers (g : A ⧸ J)).comap (QuotientGroup.mk' J)) :
    ∃ k : ℤ, g ^ k * x ∈ J := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hx)
  refine ⟨-k, ?_⟩
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_zpow, QuotientGroup.eq] at hk
  rwa [zpow_neg]

theorem card_le_card_inf_mul_of_le_comap {A : Type*} [Group A] {p : ℕ} (hp : p.Prime)
    {J : Subgroup A} [J.Normal] {g : A} {E : Subgroup A}
    (hES : E ≤ (Subgroup.zpowers (g : A ⧸ J)).comap (QuotientGroup.mk' J))
    (hE : ∀ e ∈ E, e ^ p = 1) : Nat.card E ≤ Nat.card ↥(E ⊓ J) * p :=
  card_le_card_inf_mul_of_cyclic hp inferInstance
    ⟨g, Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _), fun _ hs => exists_zpow_mul_mem hs⟩ hES hE

theorem mul_mem_of_coprime {A : Type*} [Group A] {N : Subgroup A} [N.Normal] {p d : ℕ}
    (hpd : Nat.Coprime p d) {u f : A} (hu : u ∈ N) (hf : f ^ d = 1) (he : (u * f) ^ p = 1) :
    u * f ∈ N := by
  have h1 : ((u * f : A) : A ⧸ N) = (f : A ⧸ N) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff u).2 hu, one_mul]
  have hp' : (f : A ⧸ N) ^ p = 1 := by
    rw [← h1, ← QuotientGroup.mk_pow, he, QuotientGroup.mk_one]
  have hd' : (f : A ⧸ N) ^ d = 1 := by
    rw [← QuotientGroup.mk_pow, hf, QuotientGroup.mk_one]
  have h := pow_gcd_eq_one.mpr ⟨hp', hd'⟩
  rw [Nat.Coprime.gcd_eq_one hpd, pow_one] at h
  rw [← QuotientGroup.eq_one_iff, h1]
  exact h

theorem triality_cube {A : Type*} [Group A] {θ ρ f : A} (k : ℕ) (hρρ : ρ * ρ = 1)
    (hρθ : ρ * θ * ρ = θ⁻¹) (hfθ : θ * f = f * θ) (hρf : ρ * f = f * ρ) :
    (θ ^ k * (ρ * f)) ^ 3 = θ ^ k * (ρ * f ^ 3) := by
  have hρθ' : ρ * θ = θ⁻¹ * ρ := by
    calc ρ * θ = ρ * θ * ρ * ρ := by rw [mul_assoc (ρ * θ), hρρ, mul_one]
      _ = θ⁻¹ * ρ := by rw [hρθ]
  have hc3 : (ρ * f) ^ 3 = ρ * f ^ 3 := by
    have hρf' : Commute ρ f := hρf
    rw [hρf'.mul_pow, pow_succ, pow_two, hρρ, one_mul]
  obtain ⟨c, hc⟩ : ∃ c, c = ρ * f := ⟨_, rfl⟩
  rw [← hc] at hc3 ⊢
  have hcθ : SemiconjBy c θ θ⁻¹ := by
    show c * θ = θ⁻¹ * c
    calc c * θ = ρ * (f * θ) := by rw [hc, mul_assoc]
      _ = ρ * (θ * f) := by rw [hfθ]
      _ = ρ * θ * f := by rw [mul_assoc]
      _ = θ⁻¹ * c := by rw [hρθ', hc, mul_assoc]
  have h1 : c * θ ^ k = (θ ^ k)⁻¹ * c := by
    have := hcθ.pow_right k
    rwa [inv_pow] at this
  have h2 : c * (θ ^ k)⁻¹ = θ ^ k * c := by
    have := (hcθ.pow_right k).inv_right
    rwa [inv_pow, inv_inv] at this
  calc (θ ^ k * c) ^ 3 = θ ^ k * (c * θ ^ k) * (c * θ ^ k) * c := by
        rw [pow_three]; simp only [mul_assoc]
    _ = θ ^ k * ((θ ^ k)⁻¹ * c) * ((θ ^ k)⁻¹ * c) * c := by rw [h1]
    _ = c * (θ ^ k)⁻¹ * c * c := by group
    _ = θ ^ k * c * c * c := by rw [h2]
    _ = θ ^ k * c ^ 3 := by rw [pow_three]; simp only [mul_assoc]
    _ = θ ^ k * (ρ * f ^ 3) := by rw [hc3]

end CFSG.LocalAnalysis.GLTheoremA.OR107
