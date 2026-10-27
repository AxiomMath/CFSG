module

public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.CoverRoots

public noncomputable section

namespace CFSG.EvenSmallLie.GTwoFour

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LieType.Chevalley.G2FieldFour CFSG.LocalAnalysis.ComponentInitial
open Subgroup
open scoped commutatorElement

theorem commutator_mem_zpowers_of_additive {K : Type*} [Field K] [CharP K 2] {G E : Type*}
    [Group G] [Group E] {η : E →* G} (hη : Function.Surjective η)
    (hker : ∀ k, η k = 1 → k ∈ center E) {φ : K → G} (hφ : ∀ s s', φ (s + s') = φ s * φ s')
    {ω : K} (hK : ∀ s : K, s = 0 ∨ s = 1 ∨ s = ω ∨ s = 1 + ω) {c : E}
    (hc : ∀ f f', η f = φ 1 → η f' = φ ω → ⁅f, f'⁆ = c) :
    c * c = 1 ∧ ∀ (e e' : E) (s s' : K), η e = φ s → η e' = φ s' → ⁅e, e'⁆ ∈ zpowers c := by
  set σ : G → E := Function.surjInv hη
  have hσ : ∀ g, η (σ g) = g := Function.surjInv_eq hη
  obtain ⟨β, hβdef⟩ : ∃ β : K → K → E, ∀ s s', β s s' = ⁅σ (φ s), σ (φ s')⁆ :=
    ⟨_, fun _ _ => rfl⟩
  have hβ : ∀ {e e' : E} {s s' : K}, η e = φ s → η e' = φ s' → ⁅e, e'⁆ = β s s' :=
    fun he he' => by
      rw [hβdef]
      exact LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq η hker
        (he.trans (hσ _).symm) (he'.trans (hσ _).symm)
  have hcen : ∀ s s', β s s' ∈ center E := fun s s' => hker _ (by
    rw [hβdef, map_commutatorElement, hσ, hσ, commutatorElement_eq_one_iff_mul_comm, ← hφ, ← hφ,
      add_comm])
  have hadd : ∀ s₁ s₂ s', β (s₁ + s₂) s' = β s₁ s' * β s₂ s' := fun s₁ s₂ s' => by
    rw [← hβ (e := σ (φ s₁) * σ (φ s₂)) (e' := σ (φ s')) (by rw [map_mul, hσ, hσ, hφ]) (hσ _),
      commutatorElement_mul_left', ← hβdef, ← hβdef, mem_center_iff.1 (hcen s₂ s') (σ (φ s₁)),
      mul_inv_cancel_right]
    exact (mem_center_iff.1 (hcen s₂ s') (β s₁ s')).symm
  have hswap : ∀ s s', β s' s = (β s s')⁻¹ := fun s s' => by
    rw [hβdef, hβdef, commutatorElement_inv]
  have hself : ∀ s, β s s = 1 := fun s => by rw [hβdef, commutatorElement_self]
  have hzero : ∀ s', β 0 s' = 1 := fun s' => by
    have h := hadd 0 0 s'
    rw [add_zero] at h
    exact left_eq_mul.mp h
  have hadd' : ∀ s s₁ s₂, β s (s₁ + s₂) = β s s₁ * β s s₂ := fun s s₁ s₂ => by
    rw [hswap (s₁ + s₂) s, hadd, mul_inv_rev, ← hswap s₂ s, ← hswap s₁ s]
    exact mem_center_iff.1 (hcen s s₁) (β s s₂)
  have hc' : β 1 ω = c := by rw [← hc (σ (φ 1)) (σ (φ ω)) (hσ _) (hσ _), hβdef]
  have h1 : ∀ s', β 1 s' ∈ zpowers c := fun s' => by
    rcases hK s' with h | h | h | h <;> rw [h]
    · rw [hswap, hzero, inv_one]
      exact one_mem _
    · rw [hself]
      exact one_mem _
    · rw [hc']
      exact mem_zpowers c
    · rw [hadd', hself, hc', one_mul]
      exact mem_zpowers c
  have hω : ∀ s, β s ω ∈ zpowers c := fun s => by
    rcases hK s with h | h | h | h <;> rw [h]
    · rw [hzero]
      exact one_mem _
    · rw [hc']
      exact mem_zpowers c
    · rw [hself]
      exact one_mem _
    · rw [hadd, hc', hself, mul_one]
      exact mem_zpowers c
  have hmem : ∀ s s', β s s' ∈ zpowers c := fun s s' => by
    have hωs : β ω s' ∈ zpowers c := by
      rw [hswap]
      exact inv_mem (hω s')
    rcases hK s with h | h | h | h <;> rw [h]
    · rw [hzero]
      exact one_mem _
    · exact h1 s'
    · exact hωs
    · rw [hadd]
      exact mul_mem (h1 s') hωs
  refine ⟨?_, fun e e' s s' he he' => by rw [hβ he he']; exact hmem s s'⟩
  rw [← hc', ← hadd, CharTwo.add_self_eq_zero, hzero]

section Weyl

variable {K : Type} [Field K] [CharP K 2] {M : Type*} [Group M] {π : M →* adjointGroup .G2 K}

theorem commutator_eq_of_reflect
    (hη : Function.Surjective π)
    (hker : ∀ k, π k = 1 → k ∈ center M) (i : Fin Tag.G2.rank) {d d' : Fin Tag.G2.rank → ℤ}
    (hd : IsRoot .G2 d) (hdd' : reflect .G2 i d = d') {e e' f f' : M} {s s' : K}
    (he : π e = rootX d s) (he' : π e' = rootX d s') (hf : π f = rootX d' s)
    (hf' : π f' = rootX d' s') : ⁅f, f'⁆ = ⁅e, e'⁆ := by
  let n : adjointGroup .G2 K := ⟨weylElt .G2 K i 1, weylElt_mem_adjointGroup _ _⟩
  obtain ⟨n', hn'⟩ := hη n
  have hconj : ∀ x : K, n * rootX d x * n⁻¹ = rootX d' x := fun x => Subtype.ext (by
    change weylElt .G2 K i 1 * pinnedX Tag.G2 K d x * (weylElt .G2 K i 1)⁻¹ =
      pinnedX Tag.G2 K d' x
    rw [weylElt_conj i hd, hdd'])
  have hc : ⁅e, e'⁆ ∈ center M := hker _ (by
    rw [map_commutatorElement, he, he', commutatorElement_eq_one_iff_mul_comm, ← rootX_add,
      ← rootX_add, add_comm])
  rw [LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq π hker
    (x' := n' * e * n'⁻¹) (y' := n' * e' * n'⁻¹)
    (by rw [map_mul, map_mul, map_inv, hn', he, hconj, hf])
    (by rw [map_mul, map_mul, map_inv, hn', he', hconj, hf'])]
  calc ⁅n' * e * n'⁻¹, n' * e' * n'⁻¹⁆ = n' * ⁅e, e'⁆ * n'⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅e, e'⁆ := by rw [mem_center_iff.1 hc n', mul_inv_cancel_right]

end Weyl

theorem exists_unit_forall_eq {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 4) :
    ∃ ω : Kˣ, ∀ s : K, s = 0 ∨ s = 1 ∨ s = ω ∨ s = 1 + ω := by
  obtain ⟨ω, -, -, hωsq⟩ := exists_unit_ne_one (K := K) hK
  refine ⟨ω, fun s => ?_⟩
  by_cases h0 : s = 0
  · exact Or.inl h0
  by_cases h1 : s = 1
  · exact Or.inr (Or.inl h1)
  rcases eq_or_eq_sq_of_sq_add hωsq (sq_add_self_add_one hK h0 h1) with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [h]
    linear_combination hωsq - (1 + (ω : K)) * CharTwo.two_eq_zero (R := K)

theorem card_ker_le_two
    (K : Type) [Field K] (hK : Nat.card K = 4) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (η : E →* adjointGroup .G2 K) (hη : Function.Surjective η)
    (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) : Nat.card η.ker ≤ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 2)
    (by norm_num) (by rw [hK]; norm_num)
  have hker : ∀ k, η k = 1 → k ∈ center E := fun k hk => hC hk
  obtain ⟨ω, hK4⟩ := exists_unit_forall_eq (K := K) hK
  obtain ⟨f₀, hf₀⟩ := hη (rootX rootR 1)
  obtain ⟨f₁, hf₁⟩ := hη (rootX rootR (ω : K))
  have hcr : ∀ f f', η f = rootX rootR 1 → η f' = rootX rootR (ω : K) → ⁅f, f'⁆ = ⁅f₀, f₁⁆ :=
    fun f f' hf hf' => LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq η hker
      (hf.trans hf₀.symm) (hf'.trans hf₁.symm)
  have hcu : ∀ f f', η f = rootX rootU 1 → η f' = rootX rootU (ω : K) → ⁅f, f'⁆ = ⁅f₀, f₁⁆ :=
    fun f f' hf hf' => commutator_eq_of_reflect hη hker g2ia isRoot_g2r reflect_a_r hf₀ hf₁ hf hf'
  have hcv : ∀ f f', η f = rootX rootV 1 → η f' = rootX rootV (ω : K) → ⁅f, f'⁆ = ⁅f₀, f₁⁆ := by
    intro f f' hf hf'
    obtain ⟨g₀, hg₀⟩ := hη (rootX rootU 1)
    obtain ⟨g₁, hg₁⟩ := hη (rootX rootU (ω : K))
    rw [commutator_eq_of_reflect hη hker g2ir isRoot_g2u reflect_r_u hg₀ hg₁ hf hf']
    exact hcu g₀ g₁ hg₀ hg₁
  obtain ⟨hcc, hr⟩ :=
    commutator_mem_zpowers_of_additive hη hker (φ := rootX rootR) (rootX_add rootR) hK4 hcr
  have hu :=
    (commutator_mem_zpowers_of_additive hη hker (φ := rootX rootU) (rootX_add rootU) hK4 hcu).2
  have hv :=
    (commutator_mem_zpowers_of_additive hη hker (φ := rootX rootV) (rootX_add rootV) hK4 hcv).2
  set Z := zpowers ⁅f₀, f₁⁆
  have hZker : Z ≤ η.ker := zpowers_le.2 (by
    rw [MonoidHom.mem_ker, map_commutatorElement, hf₀, hf₁,
      commutatorElement_eq_one_iff_mul_comm, ← rootX_add, ← rootX_add, add_comm])
  have : Z.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.1 (hC (hZker hn)) g, mul_inv_cancel_right]
    exact hn⟩
  let η' : E ⧸ Z →* adjointGroup .G2 K := QuotientGroup.lift Z η hZker
  have hη'e : ∀ e : E, η' (e : E ⧸ Z) = η e := fun e => rfl
  have hη' : Function.Surjective η' := fun g => by
    obtain ⟨e, rfl⟩ := hη g
    exact ⟨(e : E ⧸ Z), rfl⟩
  have : Group.IsPerfect (E ⧸ Z) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective Z)
  have hC' : η'.ker ≤ center (E ⧸ Z) := by
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ η.ker := by
      rw [MonoidHom.mem_ker, ← hη'e]
      exact hy
    rw [mem_center_iff]
    intro z
    obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 (hC he) z']
  have h2' : IsPGroup 2 η'.ker := by
    rintro ⟨y, hy⟩
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ η.ker := by
      rw [MonoidHom.mem_ker, ← hη'e]
      exact hy
    obtain ⟨n, hn⟩ := h2 ⟨e, he⟩
    have hn' : e ^ 2 ^ n = 1 := congrArg Subtype.val hn
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← QuotientGroup.mk_pow, hn', QuotientGroup.mk_one]
  have hab : ∀ d : Fin Tag.G2.rank → ℤ, IsRoot .G2 d → 0 < height d →
      ∀ x ∈ ((rootSubgroup .G2 K d).subgroupOf (adjointGroup .G2 K)).comap η',
      ∀ y ∈ ((rootSubgroup .G2 K d).subgroupOf (adjointGroup .G2 K)).comap η',
        x * y = y * x := by
    intro d hd1 hd2 x hx y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨e', rfl⟩ := QuotientGroup.mk_surjective y
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_rootSubgroup] at hx hy
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    have he : η e = rootX d s := Subtype.ext hs.symm
    have he' : η e' = rootX d s' := Subtype.ext hs'.symm
    suffices hm : ⁅e, e'⁆ ∈ Z by
      rw [← commutatorElement_eq_one_iff_mul_comm]
      exact (map_commutatorElement (QuotientGroup.mk' Z) e e').symm.trans
        ((QuotientGroup.eq_one_iff _).2 hm)
    have hcomm : ∀ {e e' : E}, e * e' = e' * e → ⁅e, e'⁆ ∈ Z := fun h => by
      rw [commutatorElement_eq_one_iff_mul_comm.2 h]
      exact one_mem _
    rcases mem_posRoots_cases (mem_posRoots.2 ⟨hd1, hd2⟩) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcomm (lift_commute_a hη hker he he')
    · exact hr e e' s s' he he'
    · exact hu e e' s s' he he'
    · exact hv e e' s s' he he'
    · exact hcomm (lift_commute_b hη hker he he')
    · exact hcomm (lift_commute_c hη hker he he')
  have hbot := (G2_field_four_abelian_root_central_two_cover_trivial K hK η' hη' hC' h2' hab).1
  have hle : η.ker ≤ Z := fun e he => by
    have hq : (e : E ⧸ Z) ∈ η'.ker := by
      rw [MonoidHom.mem_ker, hη'e]
      exact he
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hq
    exact hq
  calc Nat.card η.ker ≤ Nat.card Z := Subgroup.card_le_of_le hle
    _ = orderOf ⁅f₀, f₁⁆ := Nat.card_zpowers _
    _ ≤ 2 := orderOf_le_of_pow_eq_one two_pos (by rw [sq]; exact hcc)

end CFSG.EvenSmallLie.GTwoFour
