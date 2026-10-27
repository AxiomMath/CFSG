module

public import CFSG.GH74.GLS.Stage4.T2P71FrA
public import CFSG.GH74.GLS.Stage4.T2P71Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6.P71

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem exists_Pmax (h : T6Ctx N u p) :
    ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({N.z} : Set G) ∧ IsPGroup p ↥P ∧
      N.X₁ ⊔ N.X₂ ≤ P ∧ Nat.card ↥P = p ^ (Nat.card ↥(Subgroup.centralizer ({N.z} : Set G))).factorization p ∧
      ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({N.z} : Set G) → IsPGroup p ↥E →
        Nat.card ↥E ≤ Nat.card ↥P := by
  have : Fact p.Prime := ⟨h.prime⟩
  set C : Subgroup G := Subgroup.centralizer ({N.z} : Set G) with hC
  have hX₁C : N.X₁ ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (z_cent_X₁ h hx)
  have hX₂C : N.X₂ ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (z_cent_X₂ h hx)
  have hTC : N.X₁ ⊔ N.X₂ ≤ C := sup_le hX₁C hX₂C
  have hTp : IsPGroup p ↥(N.X₁ ⊔ N.X₂) := by
    have h0 : IsPGroup p ↥(⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
    have := Y_pGroup h (P₀ := ⊥) bot_le h0
    rwa [sup_bot_eq] at this
  obtain ⟨S, hS⟩ := (hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm).exists_le_sylow
  have hcardP : Nat.card ↥((S : Subgroup ↥C).map C.subtype) =
      p ^ (Nat.card ↥C).factorization p := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity S]
  refine ⟨(S : Subgroup ↥C).map C.subtype, Subgroup.map_subtype_le _, S.isPGroup'.map _, ?_, hcardP, ?_⟩
  · intro x hx
    exact ⟨⟨x, hTC hx⟩, hS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · intro E hEC hEp
    rw [hcardP]
    exact card_pSub_le_vp h.prime hEC hEp

theorem A_two_sub (h : T6Ctx N u p) (h' : T6Ctx N.swap u p) {P E : Subgroup G} (hXP : N.X₁ ⊔ N.X₂ ≤ P)
    (hEA : E ≤ Subgroup.centralizer (P : Set G)) (hE2 : IsPGroup 2 ↥E) (hzE : N.z ∈ E) :
    E = Subgroup.zpowers N.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := h.ctx.zz
  have hzord : orderOf N.z = 2 := h.sec5.loc.z_ord
  have hTE : Subgroup.zpowers N.z ≤ E := Subgroup.zpowers_le.2 hzE
  by_contra hne
  obtain ⟨n, hnE, hnT, hnN⟩ := t6_exists_normalizer_elt hE2 hTE (Ne.symm hne)
  have hnz : n * N.z * n⁻¹ = N.z := by
    have hmem := hnN N.z (Subgroup.mem_zpowers _)
    rcases t2C_zpowers_cases hz2 hmem with h1 | h1
    · exfalso
      have : N.z = n⁻¹ * (n * N.z * n⁻¹) * n := by group
      rw [h1] at this
      exact h.ctx.z_ne (by simpa using this)
    · exact h1
  have hnz' : n * N.z = N.z * n := by
    calc n * N.z = (n * N.z * n⁻¹) * n := by group
      _ = N.z * n := by rw [hnz]
  have hn2 : ∃ k : ℕ, n ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hE2 ⟨n, hnE⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hnc : ∀ x ∈ P, n * x * n⁻¹ = x := by
    intro x hx
    have := Subgroup.mem_centralizer_iff.1 (hEA hnE) x hx
    calc n * x * n⁻¹ = (x * n) * n⁻¹ := by rw [this]
      _ = x := by group
  exact hnT (cent_two_mem_zpowers h h' hnz' hn2 (fun x hx => hnc x (hXP (Subgroup.mem_sup_left hx)))
    (fun x hx => hnc x (hXP (Subgroup.mem_sup_right hx))))

theorem A_card2 (h : T6Ctx N u p) (h' : T6Ctx N.swap u p) {P : Subgroup G} (hXP : N.X₁ ⊔ N.X₂ ≤ P)
    (hzA : N.z ∈ Subgroup.centralizer (P : Set G)) :
    (Nat.card ↥(Subgroup.centralizer (P : Set G))).factorization 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup G := Subgroup.centralizer (P : Set G) with hA
  have hzord : orderOf N.z = 2 := h.sec5.loc.z_ord
  have hzp : IsPGroup 2 ↥((Subgroup.zpowers N.z).subgroupOf A) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hzA)).toEquiv,
      Nat.card_zpowers, hzord]; norm_num
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  have hE2 : IsPGroup 2 ↥((S : Subgroup ↥A).map A.subtype) := S.isPGroup'.map _
  have hzE : N.z ∈ (S : Subgroup ↥A).map A.subtype :=
    ⟨⟨N.z, hzA⟩, hS (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers _)), rfl⟩
  have hEA : (S : Subgroup ↥A).map A.subtype ≤ A := Subgroup.map_subtype_le _
  have heq := A_two_sub h h' hXP hEA hE2 hzE
  have hc : Nat.card ↥((S : Subgroup ↥A).map A.subtype) = 2 := by
    rw [heq, Nat.card_zpowers, hzord]
  rw [Subgroup.card_map_of_injective A.subtype_injective, Sylow.card_eq_multiplicity S] at hc
  have h2 : (2 : ℕ) ^ (Nat.card ↥A).factorization 2 = 2 ^ 1 := by rw [hc]; norm_num
  exact Nat.pow_right_injective (le_refl 2) h2

omit [Finite G] in
theorem exists_conj_involution [Finite G] {A : Subgroup G} {z z' : G} (hz : z ∈ A) (hz' : z' ∈ A)
    (hzo : orderOf z = 2) (hzo' : orderOf z' = 2) (hA2 : (Nat.card ↥A).factorization 2 = 1) :
    ∃ c ∈ A, c * z' * c⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card ↥(Subgroup.zpowers z') = 2 ^ 1 := by rw [Nat.card_zpowers, hzo']; norm_num
  have hc' : Nat.card ↥(Subgroup.zpowers z) = 2 ^ 1 := by rw [Nat.card_zpowers, hzo]; norm_num
  obtain ⟨k, hk, hkz⟩ := exists_conj_sylow (p := 2) (K := A) (Subgroup.zpowers_le.2 hz')
    (Subgroup.zpowers_le.2 hz) hc hc' hA2
  refine ⟨k, hk, ?_⟩
  have hmem : k * z' * k⁻¹ ∈ Subgroup.zpowers z := by
    rw [← hkz]
    exact ⟨z', Subgroup.mem_zpowers _, by simp [MulAut.conj_apply]⟩
  have hz2 : z * z = 1 := by rw [← pow_two]; exact hzo ▸ pow_orderOf_eq_one z
  rcases t2C_zpowers_cases hz2 hmem with h1 | h1
  · exfalso
    have : z' = k⁻¹ * (k * z' * k⁻¹) * k := by group
    rw [h1] at this
    have hz1 : z' = 1 := by simpa using this
    rw [hz1, orderOf_one] at hzo'
    omega
  · exact h1

omit [Finite G] in
theorem frattini {P : Subgroup G} {z : G} [Finite G] (hzP : ∀ x ∈ P, z * x = x * z) (hzo : orderOf z = 2)
    (hA2 : (Nat.card ↥(Subgroup.centralizer (P : Set G))).factorization 2 = 1) :
    ∀ g ∈ Subgroup.normalizer (P : Set G), ∃ c ∈ Subgroup.centralizer (P : Set G),
      ∃ n ∈ Subgroup.normalizer (P : Set G), n * z * n⁻¹ = z ∧ g = c * n := by
  intro g hg
  have hzA : z ∈ Subgroup.centralizer (P : Set G) := Subgroup.mem_centralizer_iff.2 (fun x hx => (hzP x hx).symm)
  have hgP : ∀ k ∈ P, g * k * g⁻¹ ∈ P := fun k hk => (Subgroup.mem_normalizer_iff.1 hg k).1 hk
  have hgP' : ∀ k ∈ P, g⁻¹ * k * g ∈ P := by
    intro k hk
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hg) k).1 hk
    simpa using this
  have hz'A : g * z * g⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun s hs => ?_
    have h1 := hzP _ (hgP' s hs)
    calc s * (g * z * g⁻¹) = g * ((g⁻¹ * s * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = (g * z * g⁻¹) * s := by group
  have hzo' : orderOf (g * z * g⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) z
    simpa [MulAut.conj_apply, hzo] using this
  obtain ⟨c, hc, hcz⟩ := exists_conj_involution hzA hz'A hzo hzo' hA2
  refine ⟨c⁻¹, Subgroup.inv_mem _ hc, c * g, ?_, ?_, by group⟩
  · have hcB : c ∈ Subgroup.normalizer (P : Set G) := Subgroup.centralizer_le_normalizer (P : Set G) hc
    exact (Subgroup.normalizer _).mul_mem hcB hg
  · calc c * g * z * (c * g)⁻¹ = c * (g * z * g⁻¹) * c⁻¹ := by group
      _ = z := hcz

end CFSG.GH74.GLS.Stage4.Rest.T6.P71
