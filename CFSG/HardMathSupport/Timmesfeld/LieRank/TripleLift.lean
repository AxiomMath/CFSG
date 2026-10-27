module

public import CFSG.RankThree.PartTwo.Census.TripleCoverLift
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.LieRank

open CFSG.RankThree.PartTwo.Sec4.Census

section

variable {L : Type} {X : Type*} [Group L] [Group X] {φ : L →* X}

theorem add_le_pRank_of_lift [Finite L] {Z : Subgroup L} (hZk : Z ≤ φ.ker)
    (hZp : ∀ z ∈ Z, z ^ 3 = 1) {s : ℕ} (hs : 3 ^ s ≤ Nat.card Z) {E : Subgroup X}
    (hcomm : ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x)
    (hlift : ∀ e ∈ E, ∃ y : L, φ y = e ∧ y ^ 3 = 1) {r : ℕ} (hr : 3 ^ r ≤ Nat.card E) :
    r + s ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U := TripleCoverLift.powOneSubgroup φ E 3 hcomm with hUdef
  have hUab : CFSG.Open.IsElemAbelian 3 U :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (TripleCoverLift.mem_powOneSubgroup.mp a.2).1 _
      (TripleCoverLift.mem_powOneSubgroup.mp b.2).1)⟩⟩,
      fun x hx => (TripleCoverLift.mem_powOneSubgroup.mp hx).2⟩
  have hUP : IsPGroup 3 U := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact (TripleCoverLift.mem_powOneSubgroup.mp x.2).2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUP
  let ψ : U →* X := φ.comp U.subtype
  have hψr : ψ.range = E := by
    ext e
    constructor
    · rintro ⟨x, rfl⟩
      exact (TripleCoverLift.mem_powOneSubgroup.mp x.2).1
    · intro he
      obtain ⟨y, hy, hyp⟩ := hlift e he
      exact ⟨⟨y, TripleCoverLift.mem_powOneSubgroup.mpr ⟨hy ▸ he, hyp⟩⟩, hy⟩
  have hZU : Z ≤ U := fun z hz => TripleCoverLift.mem_powOneSubgroup.mpr
    ⟨by rw [MonoidHom.mem_ker.mp (hZk hz)]; exact E.one_mem, hZp z hz⟩
  have hZψ : Z.subgroupOf U ≤ ψ.ker := fun w hw =>
    MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (hZk (Subgroup.mem_subgroupOf.mp hw)))
  have hψk : 3 ^ s ≤ Nat.card ψ.ker := by
    calc 3 ^ s ≤ Nat.card Z := hs
      _ = Nat.card (Z.subgroupOf U) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv).symm
      _ ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hZψ
  have hrk : r + s ≤ k := by
    have h1 : 3 ^ (r + s) ≤ 3 ^ k := by
      rw [← hk, ← Subgroup.card_ker_mul_card_range ψ, hψr, pow_add, mul_comm]
      exact Nat.mul_le_mul hψk hr
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  exact hrk.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hUab hk)

end

section

variable {X : Type*} [Group X]

theorem conj_eq_inv_of {n u : X} (h : n * u = u ^ 2 * n) (hu : u ^ 3 = 1) :
    n * u * n⁻¹ = u⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul, h]
  have : u ^ 2 = u⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hu
  rw [this]

theorem conj_eq_self_of {n v : X} (h : n * v = v * n) : n * v * n⁻¹ = v := by
  rw [mul_inv_eq_iff_eq_mul, h]

end

variable {L X : Type} [Group L] [Finite L] [Group X]

theorem four_le_pRank_of_cover (φ : L →* X) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center L) {z : L} (hz : z ∈ φ.ker) (hzo : orderOf z = 3)
    {u₀ u₁ u₂ t s : X} (h₀ : u₀ ^ 3 = 1) (h₁ : u₁ ^ 3 = 1) (h₂ : u₂ ^ 3 = 1)
    (c₀₁ : u₀ * u₁ = u₁ * u₀) (c₀₂ : u₀ * u₂ = u₂ * u₀) (c₁₂ : u₁ * u₂ = u₂ * u₁)
    (t₀ : t * u₀ = u₀ ^ 2 * t) (t₁ : t * u₁ = u₁ ^ 2 * t) (t₂ : t * u₂ = u₂ * t)
    (s₀ : s * u₀ = u₀ ^ 2 * s) (s₁ : s * u₁ = u₁ * s) (s₂ : s * u₂ = u₂ ^ 2 * s)
    (hE : 27 ≤ Nat.card (Subgroup.closure {u₀, u₁, u₂})) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have hodd : Odd 3 := by decide
  set S : Set X := {u₀, u₁, u₂} with hS
  set E : Subgroup X := Subgroup.closure S with hEdef
  have hpair : ∀ {a b n : X}, a * b = b * a → b ^ 3 = 1 →
      n * a * n⁻¹ = a → n * b * n⁻¹ = b⁻¹ → ∀ {x y : L}, φ x = a → φ y = b → x * y = y * x := by
    intro a b n hab hb hna hnb x y hx hy
    refine TripleCoverLift.commute_of_conj hφ hker hodd (x := x) (y := y) ?_ ?_ (n := n) ?_
    · rw [hx, hy]; exact hab
    · rw [hy]; exact hb
    · rw [hx, hy]; exact Or.inl ⟨hna, hnb⟩
  have hSpair : ∀ x y : L, φ x ∈ S → φ y ∈ S → φ x ≠ φ y → x * y = y * x := by
    intro x y hx hy hne
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
    all_goals first
      | exact absurd (hx.trans hy.symm) hne
      | skip
    ·
      exact (hpair c₀₁.symm h₀ (conj_eq_self_of s₁) (conj_eq_inv_of s₀ h₀) hy hx).symm
    ·
      exact (hpair c₀₂.symm h₀ (conj_eq_self_of t₂) (conj_eq_inv_of t₀ h₀) hy hx).symm
    ·
      exact hpair c₀₁.symm h₀ (conj_eq_self_of s₁) (conj_eq_inv_of s₀ h₀) hx hy
    ·
      exact (hpair c₁₂.symm h₁ (conj_eq_self_of t₂) (conj_eq_inv_of t₁ h₁) hy hx).symm
    ·
      exact hpair c₀₂.symm h₀ (conj_eq_self_of t₂) (conj_eq_inv_of t₀ h₀) hx hy
    ·
      exact hpair c₁₂.symm h₁ (conj_eq_self_of t₂) (conj_eq_inv_of t₁ h₁) hx hy
  have hcomm : ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x := fun x hx y hy =>
    TripleCoverLift.commute_of_mem_closure hφ hker hSpair hx hy
  have hSE : S ⊆ E := Subgroup.subset_closure
  have hSlift : ∀ a ∈ S, ∃ y : L, φ y = a ∧ y ^ 3 = 1 := by
    rintro a (rfl | rfl | rfl)
    · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker hodd h₀
        (conj_eq_inv_of t₀ h₀)
    · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker hodd h₁
        (conj_eq_inv_of t₁ h₁)
    · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker hodd h₂
        (conj_eq_inv_of s₂ h₂)
  have hlift : ∀ e ∈ E, ∃ y : L, φ y = e ∧ y ^ 3 = 1 := fun e he =>
    TripleCoverLift.exists_lift_pow_eq_one_of_mem_closure hcomm hSE hSlift he
  have hzo' : (z : L) ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
  have := add_le_pRank_of_lift (Z := Subgroup.zpowers z) (s := 1)
    (by rw [Subgroup.zpowers_le]; exact hz)
    (fun w hw => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzo', one_zpow])
    (by rw [Nat.card_zpowers, hzo, pow_one]) hcomm hlift (r := 3) (by simpa using hE)
  simpa using this

end CFSG.HardMathSupport.Timmesfeld.LieRank
