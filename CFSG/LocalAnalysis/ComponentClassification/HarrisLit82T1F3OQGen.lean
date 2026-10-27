module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQA4

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

theorem mul_comm_of_isCyclic {Q : Type*} [Group Q] [IsCyclic Q] (a b : Q) : a * b = b * a :=
  isMulCommutative_iff.mp inferInstance a b

theorem isCyclic_of_card_dvd_prime {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (h : Nat.card G ∣ p) : IsCyclic G := by
  rcases (Nat.dvd_prime hp).mp h with h1 | h1
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact isCyclic_of_subsingleton
  · have : Fact p.Prime := ⟨hp⟩
    exact isCyclic_of_prime_card h1

theorem isCyclic_quotient_of_exists_zpow {G : Type*} [Group G] {N H : Subgroup G}
    [(N.subgroupOf H).Normal] (h : ∃ g ∈ H, ∀ x ∈ H, ∃ k : ℤ, g ^ k * x ∈ N) :
    IsCyclic (H ⧸ N.subgroupOf H) := by
  obtain ⟨g, hg, hgen⟩ := h
  refine ⟨⟨QuotientGroup.mk ⟨g, hg⟩, fun y => ?_⟩⟩
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, hk⟩ := hgen x hx
  refine ⟨-k, ?_⟩
  change (QuotientGroup.mk ⟨g, hg⟩ : H ⧸ N.subgroupOf H) ^ (-k) = QuotientGroup.mk ⟨x, hx⟩
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_subgroupOf]
  simpa [zpow_neg] using hk

theorem isCyclic_quotient_of_exists_zpow_top {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (h : ∃ g : G, ∀ x : G, ∃ k : ℤ, g ^ k * x ∈ N) : IsCyclic (G ⧸ N) := by
  obtain ⟨g, hgen⟩ := h
  refine ⟨⟨QuotientGroup.mk g, fun y => ?_⟩⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, hk⟩ := hgen x
  refine ⟨-k, ?_⟩
  change (QuotientGroup.mk g : G ⧸ N) ^ (-k) = QuotientGroup.mk x
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
  simpa [zpow_neg] using hk

private theorem exists_sl23_three : ∃ a : SL(2, ZMod 3), a ^ 3 = 1 ∧ a ^ 2 ≠ 1 :=
  ⟨⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩, by decide, by decide⟩

theorem exists_psl23_three : ∃ a : PSL(2, ZMod 3), a ≠ 1 ∧ a ^ 3 = 1 := by
  obtain ⟨a, ha3, ha2⟩ := exists_sl23_three
  refine ⟨psl23 a, fun h => ?_, by rw [← map_pow, ha3, map_one]⟩
  rcases psl23_eq_one_iff.mp h with rfl | rfl
  · exact ha2 (one_pow 2)
  · exact ha2 (by rw [sq, neg_mul_neg, one_mul])

theorem false_of_forall_eq_one_three {A : Type*} [Group A] {R : Subgroup A}
    {φ : ↥R →* PSL(2, ZMod 3)} {N M : Subgroup A} (h3 : ∀ x : A, ∃ m : ℕ, ¬ 3 ∣ m ∧ x ^ m ∈ N)
    (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ M) (hφ : Function.Surjective φ)
    (hM : ∀ r : ↥R, (r : A) ∈ M → φ r = 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha1, ha3⟩ := exists_psl23_three
  obtain ⟨r, rfl⟩ := hφ a
  obtain ⟨m, hm3, hm⟩ := h3 r
  obtain ⟨k, hk⟩ := h2 _ hm
  have h1 : φ (r ^ (m * 2 ^ k)) = 1 := hM _ (by rw [pow_mul]; simpa using hk)
  rw [map_pow] at h1
  have hdvd : 3 ∣ m * 2 ^ k := orderOf_eq_prime ha3 ha1 ▸ orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h | h
  · exact hm3 h
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega

variable {T : Type*} [Group T]

theorem outNoA4_of_ker_le_inner {Q : Type*} [Group Q] (Θ : MulAut T →* Q)
    (hQ : ∀ a b : Q, a * b = b * a) (hker : Θ.ker ≤ inner T) : OutNoA4 T :=
  outNoA4_of_false fun _ _ hφ hinn => false_of_forall_eq_one_ker Θ (fun _ _ => hQ _ _) hφ
    fun r hr => hinn r (hker (MonoidHom.mem_ker.mpr hr))

theorem outNoA4_of_ker_cube {Q : Type*} [Group Q] (Θ : MulAut T →* Q)
    (hQ : ∀ a b : Q, a * b = b * a) {L : Subgroup (MulAut T)} (hker : Θ.ker = L)
    (hcube : ∀ a : L ⧸ (inner T).subgroupOf L, a ^ 3 = 1) : OutNoA4 T := by
  refine outNoA4_of_false fun R φ hφ hinn => ?_
  have hL : L.Normal := hker ▸ Θ.normal_ker
  have h3 : ∀ x ∈ L, x ^ 3 ∈ inner T := by
    intro x hx
    have h := hcube (QuotientGroup.mk ⟨x, hx⟩)
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, coe_pow] at h
  have hLφ := forall_eq_one_of_cube (N := L) (M := inner T) h3 hφ hinn
  exact false_of_forall_eq_one_ker Θ (fun _ _ => hQ _ _) hφ fun r hr =>
    hLφ r (hker ▸ MonoidHom.mem_ker.mpr hr)

theorem outNoA4_of_ker_cyclic {Q : Type*} [Group Q] (Θ : MulAut T →* Q)
    (hQ : ∀ a b : Q, a * b = b * a) {D : Subgroup (MulAut T)} [D.Normal] (hker : Θ.ker ≤ D)
    (hD : IsCyclic (D ⧸ (inner T).subgroupOf D)) : OutNoA4 T := by
  refine outNoA4_of_false fun R φ hφ hinn => ?_
  have hDφ := forall_eq_one_of_cyclic (QuotientGroup.mk' ((inner T).subgroupOf D))
    (fun x hx => by rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hx)
    hφ hinn
  exact false_of_forall_eq_one_ker Θ (fun _ _ => hQ _ _) hφ fun r hr =>
    hDφ r (hker (MonoidHom.mem_ker.mpr hr))

theorem outNoA4_of_outer_hom {B : Type*} [Group B] (Φ : Outer T →* B)
    (hB : ∀ a b : B, a * b = b * a) [IsCyclic Φ.ker] : OutNoA4 T := by
  refine outNoA4_of_false fun R φ hφ hinn => ?_
  set ψ : MulAut T →* B := Φ.comp (QuotientGroup.mk' (inner T)) with hψ
  let ρ : ↥ψ.ker →* ↥Φ.ker :=
    { toFun := fun x => ⟨QuotientGroup.mk' (inner T) x, MonoidHom.mem_ker.mpr
        (MonoidHom.mem_ker.mp x.2)⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  have hρ : ∀ x : ↥ψ.ker, ρ x = 1 → (x : MulAut T) ∈ inner T := by
    intro x hx
    have h : QuotientGroup.mk' (inner T) (x : MulAut T) = 1 := congrArg Subtype.val hx
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hker := forall_eq_one_of_cyclic (N := ψ.ker) (M := inner T) ρ hρ hφ hinn
  exact false_of_forall_eq_one_ker ψ (fun _ _ => hB _ _) hφ fun r hr =>
    hker r (MonoidHom.mem_ker.mpr hr)

theorem outNoA4_of_odd_card_outer (h : Odd (Nat.card (Outer T))) : OutNoA4 T := by
  refine outNoA4_of_false fun R φ hφ hinn => ?_
  refine false_of_forall_eq_one_odd (M := inner T) (fun x => ⟨_, h, ?_⟩) hφ hinn
  have h1 : (QuotientGroup.mk x : Outer T) ^ Nat.card (Outer T) = 1 := pow_card_eq_one'
  rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1

theorem outNoA4_of_forall_mem_inner (h : ∀ α : MulAut T, α ∈ inner T) : OutNoA4 T := by
  intro R φ hφ
  obtain ⟨a, ha1, -⟩ := exists_psl23_involution
  obtain ⟨r, rfl⟩ := hφ a
  exact ⟨r, h r, ha1⟩

theorem outNoA4_of_chain {D E : Subgroup (MulAut T)} [D.Normal] [E.Normal]
    {Q₁ Q₂ Q₃ : Type*} [Group Q₁] [Group Q₂] [Group Q₃] [IsCyclic Q₁] [IsCyclic Q₂]
    (ρ₁ : ↥D →* Q₁) (hρ₁ : ∀ x : ↥D, ρ₁ x = 1 → (x : MulAut T) ∈ inner T)
    (ρ₂ : ↥E →* Q₂) (hρ₂ : ∀ x : ↥E, ρ₂ x = 1 → (x : MulAut T) ∈ D)
    (ρ₃ : MulAut T →* Q₃) (hQ₃ : ∀ a b : Q₃, a * b = b * a) (hρ₃ : ∀ x, ρ₃ x = 1 → x ∈ E) :
    OutNoA4 T :=
  outNoA4_of_false fun _ _ hφ hinn =>
    false_of_forall_eq_one_ker ρ₃ (fun _ _ => hQ₃ _ _) hφ fun r hr =>
      forall_eq_one_of_cyclic ρ₂ hρ₂ hφ (forall_eq_one_of_cyclic ρ₁ hρ₁ hφ hinn) r (hρ₃ _ hr)

theorem outNoA4_of_chain_zpow {D E : Subgroup (MulAut T)} [D.Normal] [E.Normal]
    (hD : ∃ g ∈ D, ∀ x ∈ D, ∃ k : ℤ, g ^ k * x ∈ inner T)
    (hE : ∃ g ∈ E, ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ D)
    (hA : ∃ g : MulAut T, ∀ x, ∃ k : ℤ, g ^ k * x ∈ E) : OutNoA4 T := by
  have := isCyclic_quotient_of_exists_zpow hD
  have := isCyclic_quotient_of_exists_zpow hE
  have := isCyclic_quotient_of_exists_zpow_top hA
  refine outNoA4_of_chain (QuotientGroup.mk' ((inner T).subgroupOf D)) (fun x hx => ?_)
    (QuotientGroup.mk' (D.subgroupOf E)) (fun x hx => ?_) (QuotientGroup.mk' E)
    mul_comm_of_isCyclic fun x hx => ?_
  · rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hx
  · rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hx
  · rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx

theorem outNoA4_of_three {D : Subgroup (MulAut T)}
    (h3 : ∀ x : MulAut T, ∃ m : ℕ, ¬ 3 ∣ m ∧ x ^ m ∈ D)
    (h2 : ∀ x ∈ D, ∃ k : ℕ, x ^ 2 ^ k ∈ inner T) : OutNoA4 T :=
  outNoA4_of_false fun _ _ hφ hinn => false_of_forall_eq_one_three h3 h2 hφ hinn

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
