module

public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralSectionQuotientBasis
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCentralOddComplement
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

theorem mem_normalHallOdd_iff {H : Type*} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    (hodd : Odd (Nat.card N)) (hindex : ∃ k : ℕ, N.index = 2 ^ k) (x : H) :
    x ∈ N ↔ Odd (orderOf x) := by
  constructor
  · intro hx
    exact hodd.of_dvd_nat (N.orderOf_dvd_natCard hx)
  · intro hx
    obtain ⟨k, hk⟩ := hindex
    have hcop : Nat.Coprime (orderOf x) (2 ^ k) := (Odd.coprime_two_right hx).pow_right k
    have h1 : orderOf (x : H ⧸ N) ∣ orderOf x := orderOf_map_dvd (QuotientGroup.mk' N) x
    have h2 : orderOf (x : H ⧸ N) ∣ 2 ^ k := by
      rw [← hk]
      exact orderOf_dvd_natCard _
    have hone : orderOf (x : H ⧸ N) = 1 := (hcop.coprime_dvd_left h1).eq_one_of_dvd h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at hone
    exact hone

theorem normalHallOdd_unique {H : Type*} [Group H] [Finite H] {N N' : Subgroup H} [N.Normal]
    [N'.Normal] (hodd : Odd (Nat.card N)) (hindex : ∃ k : ℕ, N.index = 2 ^ k)
    (hodd' : Odd (Nat.card N')) (hindex' : ∃ k : ℕ, N'.index = 2 ^ k) : N = N' := by
  ext x
  rw [mem_normalHallOdd_iff hodd hindex, mem_normalHallOdd_iff hodd' hindex']

theorem normalHallOdd_complement_of_sylow {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {C : Subgroup G} (hSC : (S : Subgroup G) ≤ C) (R : Subgroup C) [R.Normal]
    (hRodd : Odd (Nat.card R)) (hRidx : ∃ k : ℕ, R.index = 2 ^ k) :
    (∀ c : C, ∃ u ∈ R, ∃ y : (S : Subgroup G), c = u * Subgroup.inclusion hSC y) ∧
    R ⊓ (Subgroup.inclusion hSC).range = ⊥ := by
  set ι := Subgroup.inclusion hSC
  have hι : Function.Injective ι := Subgroup.inclusion_injective hSC
  have hRS : R ⊓ ι.range = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxR, y, rfl⟩
    rw [Subgroup.mem_bot]
    have hodd : Odd (orderOf (ι y)) := hRodd.of_dvd_nat (R.orderOf_dvd_natCard hxR)
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' y
    rw [orderOf_injective ι hι y, hj] at hodd
    have hj0 : j = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow.mpr ⟨even_two, hne⟩))
    rw [← orderOf_eq_one_iff, orderOf_injective ι hι y, hj, hj0, pow_zero]
  refine ⟨?_, hRS⟩
  obtain ⟨k, hk⟩ := hRidx
  let φ : (S : Subgroup G) →* C ⧸ R := (QuotientGroup.mk' R).comp ι
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hmem : ι y ∈ R := (QuotientGroup.eq_one_iff _).mp hy
    have hbot : ι y ∈ R ⊓ ι.range := ⟨hmem, ⟨y, rfl⟩⟩
    rw [hRS, Subgroup.mem_bot] at hbot
    exact hι (hbot.trans (map_one ι).symm)
  have hcardQ : Nat.card (C ⧸ R) = 2 ^ k := hk
  have hdvdC : 2 ^ k ∣ Nat.card C := by
    rw [R.card_eq_card_quotient_mul_card_subgroup, hcardQ]
    exact dvd_mul_right _ _
  have hdvdS : 2 ^ k ∣ Nat.card (S : Subgroup G) :=
    S.pow_dvd_card_of_pow_dvd_card (hdvdC.trans (Subgroup.card_subgroup_dvd_card C))
  have hle : Nat.card (C ⧸ R) ≤ Nat.card (S : Subgroup G) := by
    rw [hcardQ]
    exact Nat.le_of_dvd Nat.card_pos hdvdS
  have hφbij : Function.Bijective φ := by
    refine ⟨hφinj, ?_⟩
    have hle' : Nat.card (S : Subgroup G) ≤ Nat.card (C ⧸ R) :=
      Nat.card_le_card_of_injective φ hφinj
    exact (hφinj.bijective_of_nat_card_le (le_antisymm hle' hle).ge).2
  intro c
  obtain ⟨y, hy⟩ := hφbij.2 (c : C ⧸ R)
  have hv : (ι y)⁻¹ * c ∈ R := by
    have h := hy
    change ((ι y : C) : C ⧸ R) = (c : C ⧸ R) at h
    exact QuotientGroup.eq.mp h
  refine ⟨ι y * ((ι y)⁻¹ * c) * (ι y)⁻¹, ?_, y, by group⟩
  exact Subgroup.Normal.conj_mem inferInstance _ hv (ι y)

theorem mem_centralInvolutionSection_subgroup_iff {G : Type*} [Group G] {H : Subgroup G}
    (τ x : H) :
    x ∈ centralInvolutionSection τ ↔ (x : G) ∈ centralInvolutionSection (τ : G) := by
  simp only [centralInvolutionSection, Set.mem_ofPred_eq, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.orderOf_coe]
  constructor
  · rintro ⟨hc, he, hp⟩
    exact ⟨congrArg Subtype.val hc, he, by rw [← hp]; rfl⟩
  · rintro ⟨hc, he, hp⟩
    exact ⟨Subtype.ext hc, he, Subtype.ext hp⟩

theorem comp_mem_blocksIrr {C S : Type*} [Group C] [Group S] (π : C →* S)
    (hπ : Function.Surjective π) {χ : S → ℂ} (hχ : χ ∈ BlocksIrr S) : χ ∘ π ∈ BlocksIrr C := by
  obtain ⟨V, i₁, i₂, i₃, ρ, hρ, rfl⟩ := hχ
  exact ⟨V, i₁, i₂, i₃, ρ.comp π,
    CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective π hπ ρ hρ, rfl⟩

theorem card_dihedralIndexSet_ne_two {n M : ℕ} (hn : 2 ≤ n) (hM : M = 2 ^ (n - 1)) :
    Fintype.card (dihedralIndexSet M) ≠ 2 := by
  have hM2 : 2 ≤ M := by
    rw [hM]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard := card_option_dihedralIndexSet hM2
  rw [Fintype.card_option] at hcard
  have hhalf : M / 2 = 2 ^ (n - 2) := by
    rw [hM, show n - 1 = (n - 2) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  rw [hhalf] at hcard
  intro h2
  rw [h2] at hcard
  obtain ⟨m, hm⟩ : ∃ m, n - 2 = m := ⟨_, rfl⟩
  rw [hm] at hcard
  rcases m with _ | _ | m
  · norm_num at hcard
  · norm_num at hcard
  · have h4 : 4 ≤ 2 ^ (m + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem dihedral_principal_induced_character_family_of_normalHall {G : Type} [Group G]
    [Fintype G] {n M : ℕ} (hn : 2 ≤ n) (hM : M = 2 ^ (n - 1)) (S : Sylow 2 G)
    (hSiso : Nonempty (DihedralGroup M ≃* (S : Subgroup G))) (r s : (S : Subgroup G))
    (hr : orderOf r = M) (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹)
    (hgen : Subgroup.closure {r, s} = ⊤) (t : G)
    (ht : t = ((r ^ (M / 2) : (S : Subgroup G)) : G)) (C : Subgroup G)
    (hC : C = Subgroup.centralizer {t}) (R : Subgroup C) [R.Normal]
    (hRodd : Odd (Nat.card R)) (hRidx : ∃ k : ℕ, R.index = 2 ^ k) :
    (∃! π : C →* (S : Subgroup G), π.ker = R ∧
      ∀ (y : (S : Subgroup G)) (hy : (y : G) ∈ C), π ⟨y, hy⟩ = y) ∧
    ∀ π : C →* (S : Subgroup G), π.ker = R →
      (∀ (y : (S : Subgroup G)) (hy : (y : G) ∈ C), π ⟨y, hy⟩ = y) →
      ∃ (χ₁ χ₂ χ₃ : BlocksIrr G) (δ₁ δ₂ δ₃ ε : ℤ) (ψ : dihedralIndexSet M → BlocksIrr G),
        χ₁ ≠ χ₂ ∧ χ₁ ≠ χ₃ ∧ χ₂ ≠ χ₃ ∧
        (χ₁ : G → ℂ) ≠ 1 ∧ (χ₂ : G → ℂ) ≠ 1 ∧ (χ₃ : G → ℂ) ≠ 1 ∧
        (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧ (δ₃ = 1 ∨ δ₃ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
        Function.Injective ψ ∧
        (∀ k, (ψ k : G → ℂ) ≠ 1 ∧ ψ k ≠ χ₁ ∧ ψ k ≠ χ₂ ∧ ψ k ≠ χ₃) ∧
        inducedFunction C (dihedralTheta r s M ∘ π) =
          1 + (δ₁ : ℂ) • (χ₁ : G → ℂ) + (δ₂ : ℂ) • (χ₂ : G → ℂ) + (δ₃ : ℂ) • (χ₃ : G → ℂ) ∧
        (∀ k : dihedralIndexSet M, inducedFunction C (dihedralEta r s M k ∘ π) =
          1 + (δ₁ : ℂ) • (χ₁ : G → ℂ) + (ε : ℂ) • (ψ k : G → ℂ)) ∧
        1 + (δ₁ : ℂ) * (χ₁ : G → ℂ) 1 + (δ₂ : ℂ) * (χ₂ : G → ℂ) 1 +
          (δ₃ : ℂ) * (χ₃ : G → ℂ) 1 = 0 ∧
        ∀ k : dihedralIndexSet M,
          1 + (δ₁ : ℂ) * (χ₁ : G → ℂ) 1 + (ε : ℂ) * (ψ k : G → ℂ) 1 = 0 := by
  subst hC
  have hM2 : 2 ≤ M := by
    rw [hM]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hEven : Even M := by
    rw [hM]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hcard : Nat.card (S : Subgroup G) = 2 * M := by
    obtain ⟨e⟩ := hSiso
    rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hhalf : M / 2 = 2 ^ (n - 2) := by
    rw [hM, show n - 1 = (n - 2) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  have htS : r ^ (M / 2) ∈ Subgroup.center (S : Subgroup G) := by
    have hstruct := (dihedral_rotation_involution_structure (S := (S : Subgroup G)) hn
      (hM ▸ hSiso)).2 r s (hM ▸ hr) hs hrel hgen
    rw [hhalf]
    exact hstruct.2.2.2.2.2.1
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t} := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff, ht]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp htS ⟨y, hy⟩)
  set ι := Subgroup.inclusion hSC with hιdef
  have hι : Function.Injective ι := Subgroup.inclusion_injective hSC
  have hιt : ((ι (r ^ (M / 2)) : Subgroup.centralizer {t}) : G) = t := ht.symm
  have htC : ι (r ^ (M / 2)) ∈ Subgroup.center (Subgroup.centralizer {t}) := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
    simp only [Subgroup.coe_mul, hιt]
    exact hc
  obtain ⟨hprod, hRS⟩ := normalHallOdd_complement_of_sylow S hSC R hRodd hRidx
  obtain ⟨huniq, hfacts⟩ := dihedral_section_quotient_basis_of_embedding hn hM hcard hgen hr hs
    hrel hι hRodd hprod hRS htC
  have hcompiff : ∀ π : Subgroup.centralizer {t} →* (S : Subgroup G),
      π.comp ι = MonoidHom.id _ ↔
        ∀ (y : (S : Subgroup G)) (hy : (y : G) ∈ Subgroup.centralizer {t}), π ⟨y, hy⟩ = y := by
    intro π
    constructor
    · intro h y hy
      exact DFunLike.congr_fun h y
    · intro h
      ext y
      exact congrArg Subtype.val (h y (hSC y.2))
  refine ⟨?_, fun π hker hid' => ?_⟩
  · obtain ⟨π, ⟨hker, hid⟩, huniq'⟩ := huniq
    exact ⟨π, ⟨hker, (hcompiff π).mp hid⟩, fun π' ⟨hker', hid'⟩ =>
      huniq' π' ⟨hker', (hcompiff π').mpr hid'⟩⟩
  have hid := (hcompiff π).mpr hid'
  obtain ⟨-, -, hspan, -, hinfl⟩ := hfacts π hker hid
  have hπι : ∀ y, π (ι y) = y := fun y => DFunLike.congr_fun hid y
  have hπsurj : Function.Surjective π := fun y => ⟨ι y, hπι y⟩
  obtain ⟨-, -, hφirr, hγirr, -, -, -, -, -, -, -, -, -, -, -, hθθ, hθ1, hη1, hθη, hηη⟩ :=
    dihedral_explicit_character_family hM2 hEven hcard hgen hr hs hrel
  have hU : ∀ o, dihedralSectionFamily π r s M o ∈
      sectionQuotientSpace π (centralInvolutionSection (ι (r ^ (M / 2)))) := by
    intro o
    rw [← hspan]
    exact Submodule.subset_span ⟨o, rfl⟩
  have hsupp : ∀ o, ∀ x : Subgroup.centralizer {t}, (x : G) ∉ centralInvolutionSection t →
      dihedralSectionFamily π r s M o x = 0 := by
    intro o x hx
    apply (hU o).2.1 x
    rw [mem_centralInvolutionSection_subgroup_iff, hιt]
    exact hx
  have hclass : ∀ o, BlocksIsClassFunction (dihedralSectionFamily π r s M o) :=
    fun o => (hU o).1
  have hcompV : ∀ χ : ↥(S : Subgroup G) → ℂ, χ ∈ BlocksIrr (S : Subgroup G) →
      χ ∘ π ∈ BlocksVChar (Subgroup.centralizer {t}) :=
    fun χ hχ => AddSubgroup.subset_closure (comp_mem_blocksIrr π hπsurj hχ)
  have hθV : dihedralTheta r s M ∘ π ∈ BlocksVChar (Subgroup.centralizer {t}) := by
    have heq : dihedralTheta r s M ∘ π = dihedralLinearCharacter r s M 0 ∘ π +
        dihedralLinearCharacter r s M 1 ∘ π - dihedralLinearCharacter r s M 2 ∘ π -
        dihedralLinearCharacter r s M 3 ∘ π := by
      funext x
      simp [dihedralTheta]
    rw [heq]
    exact sub_mem (sub_mem (add_mem (hcompV _ (hφirr 0)) (hcompV _ (hφirr 1)))
      (hcompV _ (hφirr 2))) (hcompV _ (hφirr 3))
  have hηV : ∀ k ∈ dihedralIndexSet M,
      dihedralEta r s M k ∘ π ∈ BlocksVChar (Subgroup.centralizer {t}) := by
    intro k hk
    have heq : dihedralEta r s M k ∘ π = dihedralLinearCharacter r s M 0 ∘ π +
        dihedralLinearCharacter r s M 1 ∘ π - dihedralRotationCharacter r s M k ∘ π := by
      funext x
      simp [dihedralEta]
    rw [heq]
    exact sub_mem (add_mem (hcompV _ (hφirr 0)) (hcompV _ (hφirr 1))) (hcompV _ (hγirr k hk))
  have hone : (1 : Subgroup.centralizer {t} → ℂ) = (1 : ↥(S : Subgroup G) → ℂ) ∘ π := rfl
  obtain ⟨hAL3, hAL3iso, -⟩ := central_involution_section_induction_isometry t
  have hθfacts := hAL3 (dihedralTheta r s M ∘ π) (hclass none) (hsupp none)
  have hηfacts := fun k : dihedralIndexSet M =>
    hAL3 (dihedralEta r s M k ∘ π) (hclass (some k)) (hsupp (some k))
  have h1notin : (1 : G) ∉ ⋃ g : G, (fun y => g * y * g⁻¹) '' centralInvolutionSection t := by
    intro h1
    obtain ⟨g, y, hy, hgy⟩ := Set.mem_iUnion.mp h1
    have hy1 : y = 1 := by
      have h' : g * y * g⁻¹ = 1 := hgy
      rw [mul_inv_eq_one, mul_eq_left] at h'
      exact h'
    rw [hy1] at hy
    obtain ⟨-, heven, -⟩ := hy
    rw [orderOf_one] at heven
    exact (Nat.not_even_one) heven
  have key := blocksVChar_principal_degree_zero_gram_common_constituents
    (J := dihedralIndexSet M) (card_dihedralIndexSet_ne_two hn hM)
    (Θ := inducedFunction (Subgroup.centralizer {t}) (dihedralTheta r s M ∘ π))
    (E := fun k => inducedFunction (Subgroup.centralizer {t}) (dihedralEta r s M k ∘ π))
    (hθfacts.2.2.2 hθV) (fun k => (hηfacts k).2.2.2 (hηV k k.2))
    (hθfacts.2.1 1 h1notin) (fun k => (hηfacts k).2.1 1 h1notin)
    (by rw [hθfacts.2.2.1, hone]; exact (hinfl _ _).trans hθ1)
    (fun k => by rw [(hηfacts k).2.2.1, hone]; exact (hinfl _ _).trans (hη1 k k.2))
    (by
      rw [hAL3iso (dihedralTheta r s M ∘ π) (dihedralTheta r s M ∘ π) (hclass none) (hsupp none)
        (hclass none) (hsupp none)]
      exact (hinfl _ _).trans hθθ)
    (fun k => by
      rw [hAL3iso (dihedralTheta r s M ∘ π) (dihedralEta r s M k ∘ π) (hclass none) (hsupp none)
        (hclass (some k)) (hsupp (some k))]
      exact (hinfl _ _).trans (hθη k k.2))
    (fun j l => by
      rw [hAL3iso (dihedralEta r s M j ∘ π) (dihedralEta r s M l ∘ π) (hclass (some j))
        (hsupp (some j)) (hclass (some l)) (hsupp (some l))]
      refine (hinfl _ _).trans ((hηη j j.2 l l.2).trans ?_)
      congr 1
      exact if_congr Subtype.ext_iff.symm rfl rfl)
  obtain ⟨χ₁, χ₂, χ₃, δ₁, δ₂, δ₃, ε, ψ, h12, h13, h23, h1, h2, h3, hδ₁, hδ₂, hδ₃, hε, hψ,
    hψne, hΘ, hE, -⟩ := key
  refine ⟨χ₁, χ₂, χ₃, δ₁, δ₂, δ₃, ε, ψ, h12, h13, h23, h1, h2, h3, hδ₁, hδ₂, hδ₃, hε, hψ,
    hψne, hΘ, hE, ?_, ?_⟩
  · have h := hθfacts.2.1 1 h1notin
    change inducedFunction (Subgroup.centralizer {t}) (dihedralTheta r s M ∘ π) 1 = 0 at h
    rw [hΘ] at h
    simpa only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] using h
  · intro k
    have h := (hηfacts k).2.1 1 h1notin
    change inducedFunction (Subgroup.centralizer {t}) (dihedralEta r s M k ∘ π) 1 = 0 at h
    rw [hE k] at h
    simpa only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] using h

theorem dihedral_principal_induced_character_family {G : Type} [Group G] [Fintype G]
    {n M : ℕ} (hn : 2 ≤ n) (hM : M = 2 ^ (n - 1)) (S : Sylow 2 G)
    (hSiso : Nonempty (DihedralGroup M ≃* (S : Subgroup G))) (r s : (S : Subgroup G))
    (hr : orderOf r = M) (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹)
    (hgen : Subgroup.closure {r, s} = ⊤) (t : G)
    (ht : t = ((r ^ (M / 2) : (S : Subgroup G)) : G)) (C : Subgroup G)
    (hC : C = Subgroup.centralizer {t}) :
    (∃! R : Subgroup C, R.Normal ∧ Odd (Nat.card R) ∧ ∃ k : ℕ, R.index = 2 ^ k) ∧
    ∀ R : Subgroup C, R.Normal → Odd (Nat.card R) → (∃ k : ℕ, R.index = 2 ^ k) →
      (∃! π : C →* (S : Subgroup G), π.ker = R ∧
        ∀ (y : (S : Subgroup G)) (hy : (y : G) ∈ C), π ⟨y, hy⟩ = y) ∧
      ∀ π : C →* (S : Subgroup G), π.ker = R →
        (∀ (y : (S : Subgroup G)) (hy : (y : G) ∈ C), π ⟨y, hy⟩ = y) →
        ∃ (χ₁ χ₂ χ₃ : BlocksIrr G) (δ₁ δ₂ δ₃ ε : ℤ) (ψ : dihedralIndexSet M → BlocksIrr G),
          χ₁ ≠ χ₂ ∧ χ₁ ≠ χ₃ ∧ χ₂ ≠ χ₃ ∧
          (χ₁ : G → ℂ) ≠ 1 ∧ (χ₂ : G → ℂ) ≠ 1 ∧ (χ₃ : G → ℂ) ≠ 1 ∧
          (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧ (δ₃ = 1 ∨ δ₃ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
          Function.Injective ψ ∧
          (∀ k, (ψ k : G → ℂ) ≠ 1 ∧ ψ k ≠ χ₁ ∧ ψ k ≠ χ₂ ∧ ψ k ≠ χ₃) ∧
          inducedFunction C (dihedralTheta r s M ∘ π) =
            1 + (δ₁ : ℂ) • (χ₁ : G → ℂ) + (δ₂ : ℂ) • (χ₂ : G → ℂ) + (δ₃ : ℂ) • (χ₃ : G → ℂ) ∧
          (∀ k : dihedralIndexSet M, inducedFunction C (dihedralEta r s M k ∘ π) =
            1 + (δ₁ : ℂ) • (χ₁ : G → ℂ) + (ε : ℂ) • (ψ k : G → ℂ)) ∧
          1 + (δ₁ : ℂ) * (χ₁ : G → ℂ) 1 + (δ₂ : ℂ) * (χ₂ : G → ℂ) 1 +
            (δ₃ : ℂ) * (χ₃ : G → ℂ) 1 = 0 ∧
          ∀ k : dihedralIndexSet M,
            1 + (δ₁ : ℂ) * (χ₁ : G → ℂ) 1 + (ε : ℂ) * (ψ k : G → ℂ) 1 = 0 := by
  have hhalf : M / 2 = 2 ^ (n - 2) := by
    rw [hM, show n - 1 = (n - 2) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  have hstruct := (dihedral_rotation_involution_structure (S := (S : Subgroup G)) hn
    (hM ▸ hSiso)).2 r s (hM ▸ hr) hs hrel hgen
  have htS : r ^ (M / 2) ∈ Subgroup.center (S : Subgroup G) := by
    rw [hhalf]
    exact hstruct.2.2.2.2.2.1
  have htord : orderOf (r ^ (M / 2)) = 2 := by
    rw [hhalf]
    exact hstruct.2.2.2.1.2.1
  have hSC : (S : Subgroup G) ≤ C := by
    intro y hy
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ht]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp htS ⟨y, hy⟩)
  have htC : t ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have hSCiso : Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* ((S.subtype hSC : Sylow 2 C) :
      Subgroup C)) := by
    obtain ⟨e⟩ := hSiso
    exact ⟨hM ▸ e.trans (Subgroup.subgroupOfEquivOfLe hSC).symm⟩
  have hcenter : ∃ τ ∈ Subgroup.center C, orderOf τ = 2 := by
    refine ⟨⟨t, htC⟩, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      have hc : (c : G) ∈ Subgroup.centralizer {t} := hC ▸ c.2
      exact Subgroup.mem_centralizer_singleton_iff.mp hc
    · rw [Subgroup.orderOf_mk, ht, Subgroup.orderOf_coe, htord]
  obtain ⟨N, hNn, ⟨hNodd, hNidx⟩, -⟩ :=
    dihedral_central_involution_normal_odd_complement (S.subtype hSC) hn hSCiso hcenter
  refine ⟨⟨N, ⟨hNn, hNodd, hNidx⟩, fun R ⟨hRn, hRodd, hRidx⟩ => ?_⟩,
    fun R hRn hRodd hRidx => ?_⟩
  · exact normalHallOdd_unique hRodd hRidx hNodd hNidx
  · exact dihedral_principal_induced_character_family_of_normalHall hn hM S hSiso r s hr hs hrel
      hgen t ht C hC R hRodd hRidx

end CFSG.Semidihedral.Principal
