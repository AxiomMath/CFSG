module

public import CFSG.LieType.Steinberg.CentralExt.CoverAssembly
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverLarge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryFiveCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover
public import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect
public import CFSG.Open.QuasithinDefs

public section

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SUOdd

theorem ker_eq_bot_of_section {P G : Type*} [Group P] [Group G] [Group.IsPerfect P]
    {η : P →* G} (hC : η.ker ≤ Subgroup.center P) {s : G →* P} (hs : ∀ g, η (s g) = g) :
    η.ker = ⊥ := by
  have hdec : ∀ x : P, ∃ c ∈ η.ker, x = c * s (η x) := fun x =>
    ⟨x * (s (η x))⁻¹, by rw [MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel],
      by group⟩
  have hle : commutator P ≤ s.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨c, hc, hx⟩ := hdec x
    obtain ⟨d, hd, hy⟩ := hdec y
    refine ⟨⁅η x, η y⁆, ?_⟩
    rw [map_commutatorElement]
    conv_rhs => rw [hx, hy]
    rw [CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center (hC hc) (hC hd)]
  rw [eq_bot_iff]
  intro x hx
  have hxs : x ∈ s.range := hle (by rw [Group.IsPerfect.commutator_eq_top]; trivial)
  obtain ⟨g, rfl⟩ := hxs
  have hg : g = 1 := by rw [← hs g]; exact hx
  rw [hg, map_one]
  exact Subgroup.one_mem _

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]

local notation "σ₀" => unitaryInvolution F p f

omit [CharP F p] in
theorem lieModel_statedProj_SU (hF : Nat.card F = (p ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ}
    (hn : 3 ≤ n) (hq : (n, p ^ f) ≠ (3, 2)) :
    CFSG.Blueprint.LieModel (StatedProj (StatedSU n (p ^ f) F)) .PSU n p f :=
  Or.inl ⟨by decide, ⟨hp.out, hf, hn, hq⟩, F, inferInstance, inferInstance, hF,
    ⟨MulEquiv.refl _⟩⟩

noncomputable def toPSU (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    SU σ₀ n →* StatedProj (StatedSU n (p ^ f) F) :=
  (QuotientGroup.mk' _).comp (equivStatedSU hF n).toMonoidHom

theorem toPSU_surjective (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    Function.Surjective (toPSU hF n) :=
  (QuotientGroup.mk'_surjective _).comp (equivStatedSU hF n).surjective

theorem toPSU_ker_le_center (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    (toPSU hF n).ker ≤ Subgroup.center (SU σ₀ n) := by
  intro x hx
  set ψ := equivStatedSU hF n
  have hz : ψ x ∈ (StatedScalars (Fin n) F).subgroupOf (StatedSU n (p ^ f) F) := by
    have h1 : (QuotientGroup.mk' _ (ψ x) : StatedProj (StatedSU n (p ^ f) F)) = 1 := hx
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hz' : ((ψ x : StatedSU n (p ^ f) F) : GL (Fin n) F) ∈
      Subgroup.center (GL (Fin n) F) := by
    have h1 := Subgroup.mem_subgroupOf.1 hz
    rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
  rw [Subgroup.mem_center_iff]
  intro y
  apply ψ.injective
  rw [map_mul, map_mul]
  exact Subtype.ext (Subgroup.mem_center_iff.1 hz' (ψ y))

theorem su_cover_trivial_of_psu (hF : Nat.card F = (p ^ f) ^ 2) {n ℓ : ℕ} [Fact ℓ.Prime]
    (htriv : ∀ (P : Type) [Group P] [Finite P] [Group.IsPerfect P]
      (η : P →* StatedProj (StatedSU n (p ^ f) F)), Function.Surjective η →
        η.ker ≤ Subgroup.center P → IsPGroup ℓ η.ker → η.ker = ⊥)
    (P : Type) [Group P] [Finite P] [Group.IsPerfect P] (η : P →* SU σ₀ n)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center P) (hℓ : IsPGroup ℓ η.ker) :
    η.ker = ⊥ :=
  CoverAssembly.ker_eq_bot_of_central_quotient (toPSU_surjective hF n)
    (toPSU_ker_le_center hF n) htriv P η hη hC hℓ

section Two

open CFSG.LocalAnalysis.ComponentInitial

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem psu_odd_two_cover_trivial (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ}
    (hn : 3 ≤ n) (ho : ¬ Even n) (h3 : n = 3 → 2 ≤ f) (P : Type) [Group P] [Finite P]
    [Group.IsPerfect P] (η : P →* StatedProj (StatedSU n (2 ^ f) F))
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center P) (h2 : IsPGroup 2 η.ker) :
    η.ker = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ : ∃ r, n = 2 * r + 1 := ⟨n / 2, by
    obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.1 ho
    omega⟩
  subst hr
  have hq : (2 * r + 1, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2' := congrArg Prod.snd h
    simp only at h1 h2'
    have := h3 h1
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hM := lieModel_statedProj_SU (p := 2) hF hf hn hq
  rcases (show r = 1 ∨ 2 ≤ r by omega) with rfl | hr2
  · have hf2 := h3 rfl
    have hcard : Nat.card F = 2 ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    exact (CFSG.ShultStronglyClosedTI.even_unitary_three_perfect_central_two_cover_trivial f hf2
      hcard η hη hC h2).1
  · rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
      · exact (even_unitary_five_prime_field_central_two_cover_trivial
          η hη hC h2 hM).1
      · exact (even_odd_dimensional_unitary_prime_field_central_two_cover_trivial
          η hη hC h2 hr3 hM).1
    · exact (even_odd_dimensional_unitary_catalog_perfect_central_two_cover_trivial
        η hη hC h2 hr2 hf2 hM).1

theorem odd_card_of_isPGroup {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {A : Type*} [Group A]
    [Finite A] (hA : IsPGroup r A) : Odd (Nat.card A) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA
  rw [hk]
  exact (hr.eq_two_or_odd'.resolve_left hr2).pow

theorem su_three_even_exists_section_of_odd
    (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 2 ≤ f) {E : Type*} [Group E] [Finite E] {π : E →* SU (unitaryInvolution F 2 f) 3}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) :
    ∃ s : SU (unitaryInvolution F 2 f) 3 →* E, ∀ x, π (s x) = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := equivStatedSU hF 3
  have hker : (ψ.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ψ.injective]
  obtain ⟨s, hs, -⟩ := CFSG.SectionRank.EvenCover.even_unitary_three_central_odd_extension_splitting
    hF hf (π := ψ.toMonoidHom.comp π) (ψ.surjective.comp hπ) (hker ▸ hcen) (hker ▸ hodd)
  refine ⟨s.comp ψ.toMonoidHom, fun g => ψ.injective ?_⟩
  exact hs (ψ g)

end Two

end CFSG.LieType.Steinberg.CentralExt.SUOdd
