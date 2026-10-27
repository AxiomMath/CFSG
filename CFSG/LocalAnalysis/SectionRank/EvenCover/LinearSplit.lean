module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
public import CFSG.LieType.Steinberg.CentralExt.Split
public import CFSG.LieType.Steinberg.Classical.SpecialLinear

public section

namespace CFSG.SectionRank.EvenCover

open Matrix CFSG.LieType.Steinberg CFSG.LieType.Universal CFSG.LieType.CentralExt
  CFSG.Assembly.LowTwoRank

theorem not_two_dvd_of_odd {m : ℕ} (h : Odd m) : ¬ 2 ∣ m :=
  fun h2 => (Nat.not_even_iff_odd.2 h) (even_iff_two_dvd.2 h2)

theorem even_linear_central_odd_extension_splitting
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (_hn : 2 ≤ n) {E : Type*} [Group E] [Finite E]
    {π : E →* SpecialLinearGroup (Fin n) K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ s : SpecialLinearGroup (Fin n) K →* E, (∀ g, π (s g) = g) ∧
      (∀ τ : SpecialLinearGroup (Fin n) K →* E, (∀ g, π (τ g) = g) → τ = s) ∧
      ∃ e : π.ker × s.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := not_two_dvd_of_odd hodd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine exists_section_mulEquiv_of_existsUnique hcen
    (existsUnique_section_of_sl2_lift (p := 2) (SpecialLinear.isCTGroupDatum m K)
      (SpecialLinear.steinbergExtras m K) SL.isParametrization SL.rankOne hπ hcen hC
      fun ρ => ?_)
  obtain ⟨ρ', hρ', -⟩ := sl2_existsUnique_lift hπ hcen hC ρ
  exact ⟨ρ', fun g => congrArg (· g) hρ'⟩

theorem even_linear_central_odd_extension_splitting_stated
    {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} (hn : 2 ≤ n) {E : Type*} [Group E] [Finite E]
    {π : E →* StatedSL n K} (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) :
    ∃ s : StatedSL n K →* E, (∀ g, π (s g) = g) ∧
      ∀ τ : StatedSL n K →* E, (∀ g, π (τ g) = g) → τ = s := by
  set ε := specialLinearGroupEquivStatedSL n K with hε
  set π' : E →* SpecialLinearGroup (Fin n) K := ε.symm.toMonoidHom.comp π with hπ'
  have hker : π'.ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hπ', MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  have hπ's : Function.Surjective π' := ε.symm.surjective.comp hπ
  obtain ⟨s', hs', huniq, -⟩ := even_linear_central_odd_extension_splitting hn hπ's
    (hker ▸ hcen) (hker ▸ hodd)
  refine ⟨s'.comp ε.symm.toMonoidHom, fun g => ?_, fun τ hτ => ?_⟩
  · have h := hs' (ε.symm g)
    rw [hπ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ε.symm.injective h
  · have h := huniq (τ.comp ε.toMonoidHom) fun g => by
      rw [hπ', MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom, hτ, MulEquiv.symm_apply_apply]
    ext g
    have := congrArg (· (ε.symm g)) h
    simpa using this

theorem even_linear_existsUnique_lift
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) {E G : Type*} [Group E] [Group G] [Finite E] {π : E →* G}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (α : SpecialLinearGroup (Fin n) K →* G) :
    ∃! α' : SpecialLinearGroup (Fin n) K →* E, π.comp α' = α := by
  obtain ⟨σ, hσ, huniq, -⟩ := even_linear_central_odd_extension_splitting hn
    (pullbackFst_surjective hπ α) (pullbackFst_ker_le_center hcen α)
    (Odd.of_dvd_nat hodd (card_pullbackFst_ker_dvd π α))
  refine ⟨_, comp_snd_section σ hσ, fun τ hτ => ?_⟩
  let τ' : SpecialLinearGroup (Fin n) K →* pullback π α :=
    { toFun := fun g => ⟨(g, τ g), by
        change α g = π (τ g)
        rw [← hτ, MonoidHom.comp_apply]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have h1 := huniq τ' fun g => rfl
  ext g
  exact congrArg (fun f : SpecialLinearGroup (Fin n) K →* pullback π α =>
    ((f g : pullback π α) : SpecialLinearGroup (Fin n) K × E).2) h1

theorem even_linear_homomorphism_lifting
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) {E G : Type*} [Group E] [Group G] [Finite E] {π : E →* G}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (α : SpecialLinearGroup (Fin n) K →* G) :
    (∃! α' : SpecialLinearGroup (Fin n) K →* E, π.comp α' = α) ∧
      ∀ α' : SpecialLinearGroup (Fin n) K →* E, π.comp α' = α → Function.Injective α →
        Function.Injective α' := by
  refine ⟨even_linear_existsUnique_lift hn hπ hcen hodd α, fun α' h hinj => ?_⟩
  rw [← h, MonoidHom.coe_comp] at hinj
  exact hinj.of_comp

theorem even_linear_lift_commute
    {K₁ K₂ : Type} [Field K₁] [Finite K₁] [CharP K₁ 2] [Field K₂]
    [Finite K₂] [CharP K₂ 2] {n₁ n₂ : ℕ} (_hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) {E G : Type*} [Group E]
    [Group G] [Finite E] {π : E →* G} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker))
    {α₁ : SpecialLinearGroup (Fin n₁) K₁ →* G} {α₂ : SpecialLinearGroup (Fin n₂) K₂ →* G}
    (hcomm : ∀ a b, Commute (α₁ a) (α₂ b)) {α₁' : SpecialLinearGroup (Fin n₁) K₁ →* E}
    {α₂' : SpecialLinearGroup (Fin n₂) K₂ →* E} (h₁ : π.comp α₁' = α₁) (h₂ : π.comp α₂' = α₂) :
    ∀ a b, Commute (α₁' a) (α₂' b) := by
  intro a b
  set e := α₁' a with he
  have hconj : π.comp ((MulAut.conj e).toMonoidHom.comp α₂') = α₂ := by
    ext g
    have h1 : π e = α₁ a := by rw [he, ← h₁, MonoidHom.comp_apply]
    have h2 : π (α₂' g) = α₂ g := by rw [← h₂, MonoidHom.comp_apply]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, h1, h2]
    rw [(hcomm a g).eq, mul_inv_cancel_right]
  obtain ⟨_, _, huniq⟩ := even_linear_existsUnique_lift hn₂ hπ hcen hodd α₂
  have h3 := (huniq _ hconj).trans (huniq _ h₂).symm
  have h4 := congrArg (· b) h3
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h4
  calc e * α₂' b = e * α₂' b * e⁻¹ * e := by group
    _ = α₂' b * e := by rw [h4]

end CFSG.SectionRank.EvenCover
