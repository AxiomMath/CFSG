module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33K
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem support_subset_compl_of_prime_cycle {n : ℕ} {ζ π : Perm (Fin n)} (hζ : ζ * ζ = 1)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hπq : π ^ q = 1) (hπ1 : π ≠ 1)
    (hπζ : π * ζ = ζ * π) (hcyc : π.IsCycle) : π.support ⊆ ζ.supportᶜ := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have ho : orderOf π = q := orderOf_eq_prime hπq hπ1
  have hsupp : π.support.card = q := by rw [← hcyc.orderOf, ho]
  have hζs : ∀ x, ζ x ∈ π.support ↔ x ∈ π.support := by
    intro x
    rw [Perm.mem_support, Perm.mem_support]
    have h2 : π (ζ x) = ζ (π x) := by rw [← Perm.mul_apply, hπζ, Perm.mul_apply]
    rw [h2]
    constructor
    · intro hx h
      exact hx (by rw [h])
    · intro hx h
      exact hx (ζ.injective h)
  have hodd : Odd (Nat.card {x // x ∈ π.support}) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_mem_eq_inter,
      Finset.univ_inter, hsupp]
    exact hq.odd_of_ne_two hq2
  set ζ' : Perm {x // x ∈ π.support} := ζ.subtypePerm hζs with hζ'def
  have hζ'2 : ∀ x, ζ' (ζ' x) = x := by
    intro x
    apply Subtype.ext
    change ζ (ζ x) = x
    rw [← Perm.mul_apply, hζ, Perm.one_apply]
  obtain ⟨⟨x₀, hx₀⟩, hfx⟩ := exists_apply_eq_of_odd_card hodd ζ' hζ'2
  have hζx₀ : ζ x₀ = x₀ := congrArg Subtype.val hfx
  intro y hy
  rw [Finset.mem_compl, Perm.mem_support, not_not]
  obtain ⟨i, rfl⟩ := hcyc.exists_pow_eq (Perm.mem_support.mp hx₀) (Perm.mem_support.mp hy)
  have hc : Commute ζ (π ^ i) := Commute.pow_right (show Commute ζ π from hπζ.symm) i
  rw [← Perm.mul_apply, hc.eq, Perm.mul_apply, hζx₀]

theorem eq_one_of_odd_commute_five {φ π : Perm (Fin 5)} (hφA : φ ∈ alternatingGroup (Fin 5))
    (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1) (hπ : Odd (orderOf π)) (hc : π * φ = φ * π) : π = 1 := by
  classical
  by_contra hπ1
  have h4 := four_le_card_support_of_mem_alternatingGroup hφA hφ2 hφ1
  have hfix : φ.supportᶜ.card ≤ 1 := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have ho1 : orderOf π ≠ 1 := fun h => hπ1 (orderOf_eq_one_iff.mp h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd ho1
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hπ) (even_iff_two_dvd.mpr hqd)
  have : Fact q.Prime := ⟨hq⟩
  set π' := π ^ (orderOf π / q) with hπ'def
  have hπ'o : orderOf π' = q := orderOf_pow_orderOf_div (orderOf_pos π).ne' hqd
  have hπ'q : π' ^ q = 1 := by
    rw [← hπ'o]
    exact pow_orderOf_eq_one π'
  have hπ'1 : π' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hπ'o
    exact hq.one_lt.ne hπ'o
  have hπ'c : π' * φ = φ * π' := (Commute.pow_left (show Commute π φ from hc) _).eq
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (σ := π') (by rw [hπ'o]; exact hq)
  have hsupp : π'.support.card = q * (k + 1) := by
    rw [← Perm.sum_cycleType, hk, Multiset.sum_replicate, hπ'o, smul_eq_mul]
    ring
  have hle : π'.support.card ≤ 5 := by
    have := Finset.card_le_univ π'.support
    rwa [Fintype.card_fin] at this
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  have hk0 : k = 0 := by
    by_contra hk0
    have h1 : 2 ≤ k + 1 := by omega
    have h2 : q * 2 ≤ π'.support.card := hsupp ▸ Nat.mul_le_mul_left q h1
    omega
  subst hk0
  simp only [zero_add, mul_one] at hsupp
  have hcyc : π'.IsCycle := Perm.card_cycleType_eq_one.mp (by rw [hk]; simp)
  have hsub := support_subset_compl_of_prime_cycle hφ2 hq hq2 hπ'q hπ'1 hπ'c hcyc
  have := Finset.card_le_card hsub
  omega

variable {X : Type} [Group X]

variable {M : Subgroup X} {ψ : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin 5)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 5)}

theorem image_of_five [Finite X] {T : Subgroup X}
    (hTN : T ≤ normalizer (M : Set X)) (hTperf : ⁅T, T⁆ = T)
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥T = ⊤)
    (χ : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 5))
    (hne : ∃ l : ↥T, ρ (inclusion hTN l) ≠ 1) :
    (∀ g ∈ alternatingGroup (Fin 5), ∃ l : ↥T, ρ (inclusion hTN l) = g) ∧
      (∀ l : ↥T, ρ (inclusion hTN l) ∈ alternatingGroup (Fin 5)) ∧
      ∀ l : ↥T, l ∈ pPrimeCore 2 ↥T → ρ (inclusion hTN l) = 1 := by
  classical
  have hA : ∀ l : ↥T, ρ (inclusion hTN l) ∈ alternatingGroup (Fin 5) := by
    intro l
    have hperf : Group.IsPerfect ↥T := (Subgroup.isPerfect_iff).mpr hTperf
    have h1 := Abelianization.commutator_subset_ker (Perm.sign.comp (ρ.comp (inclusion hTN)))
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact h1 (mem_top l)
  let φ : ↥T →* alternatingGroup (Fin 5) :=
    (ρ.comp (inclusion hTN)).codRestrict (alternatingGroup (Fin 5)) hA
  obtain ⟨l₀, hl₀⟩ := hne
  have hφ : φ l₀ ≠ 1 := fun h => hl₀ (congrArg Subtype.val h)
  have hQ : ∀ l, φ l ∈ fixAlt (1 : Perm (Fin 5)) := by
    intro l
    rw [mem_fixAlt]
    simp
  have hQc : Nat.card (fixAlt (1 : Perm (Fin 5))) ≤ Nat.factorial 5 / 2 := by
    rw [card_fixAlt (by simp)]
    simp
  obtain ⟨ψL, hψL⟩ := exists_coreQuot_equiv_of_hom hres (by norm_num) χ φ ⟨l₀, hφ⟩ hQ hQc
  refine ⟨fun g hg => ?_, hA, fun l hl => ?_⟩
  · have hgQ : (⟨g, hg⟩ : alternatingGroup (Fin 5)) ∈ fixAlt (1 : Perm (Fin 5)) := by
      rw [mem_fixAlt]
      simp
    obtain ⟨q, hq⟩ := ψL.surjective ⟨⟨g, hg⟩, hgQ⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨l, ?_⟩
    have h1 := hψL l
    rw [hq] at h1
    exact (congrArg Subtype.val h1).symm
  · have h1 := hψL l
    rw [(QuotientGroup.eq_one_iff l).mpr hl, map_one] at h1
    exact (congrArg Subtype.val h1).symm

theorem eq_one_of_mem_cak_of_image_five {T : Subgroup X}
    (hTN : T ≤ normalizer (M : Set X))
    (hsurj : ∀ g ∈ alternatingGroup (Fin 5), ∃ l : ↥T, ρ (inclusion hTN l) = g)
    (hO : ∀ l : ↥T, l ∈ pPrimeCore 2 ↥T → ρ (inclusion hTN l) = 1) {y : X}
    (hyN : y ∈ normalizer (M : Set X)) (hyT : y ∈ UnbalancedLayer.coreActionKernel T) :
    ρ ⟨y, hyN⟩ = 1 := by
  refine eq_one_of_commute_fixAlt (τ := 1) (fun x hx => by simp at hx) (by simp)
    fun b _ => ?_
  obtain ⟨l, hl⟩ := hsurj b b.2
  have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hyT)).2 l l.2
  rw [inv_inv] at h1
  obtain ⟨o, ho, hoeq⟩ := h1
  have hyl : y * (l : X) * y⁻¹ = (l : X) * (o : X) := by
    change (o : X) = (l : X)⁻¹ * y * l * y⁻¹ at hoeq
    rw [hoeq]
    group
  have h2 : (⟨y, hyN⟩ : ↥(normalizer (M : Set X))) * inclusion hTN l * ⟨y, hyN⟩⁻¹ =
      inclusion hTN l * inclusion hTN o := Subtype.ext hyl
  have h3 : ρ (inclusion hTN o) = 1 := hO o ho
  calc ρ ⟨y, hyN⟩ * (b : Perm (Fin 5)) = ρ ⟨y, hyN⟩ * ρ (inclusion hTN l) := by rw [hl]
    _ = ρ (⟨y, hyN⟩ * inclusion hTN l * ⟨y, hyN⟩⁻¹) * ρ ⟨y, hyN⟩ := by
        rw [map_mul, map_mul, map_inv]
        group
    _ = ρ (inclusion hTN l) * ρ ⟨y, hyN⟩ := by rw [h2, map_mul, h3, mul_one]
    _ = (b : Perm (Fin 5)) * ρ ⟨y, hyN⟩ := by rw [hl]

theorem le_coreActionKernel_of_five [Finite X] {T X₀ : Subgroup X} {s j : X}
    (hM : ⁅M, M⁆ = M) (ψ : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin 5))
    (hTN : T ≤ normalizer (M : Set X)) (hTperf : ⁅T, T⁆ = T)
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥T = ⊤)
    (χ : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 5))
    (hTK : ¬ T ≤ UnbalancedLayer.coreActionKernel M)
    (hsN : s ∈ normalizer (M : Set X)) (hs2 : s * s = 1)
    (hsK : s ∉ UnbalancedLayer.coreActionKernel M) (hj : j ∈ T)
    (hsj : s * j⁻¹ ∈ UnbalancedLayer.coreActionKernel T)
    (hX₀N : X₀ ≤ normalizer (M : Set X)) (hX₀s : X₀ ≤ centralizer ({s} : Set X))
    (hodd : Odd (Nat.card X₀)) : X₀ ≤ UnbalancedLayer.coreActionKernel M := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_isPermActionZ (N := M) (by norm_num) (by norm_num) ψ
  have hne : ∃ l : ↥T, ρ (inclusion hTN l) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hTK
    intro l hl
    exact hρ.mem_coreActionKernel hM (hTN hl) (hall ⟨l, hl⟩)
  obtain ⟨hsurj, hA, hO⟩ := image_of_five hTN hTperf hres χ hne
  have hjN : j ∈ normalizer (M : Set X) := hTN hj
  have hsjN : s * j⁻¹ ∈ normalizer (M : Set X) := mul_mem hsN (inv_mem hjN)
  have h1 : ρ ⟨s * j⁻¹, hsjN⟩ = 1 := eq_one_of_mem_cak_of_image_five hTN hsurj hO hsjN hsj
  have hρs : ρ ⟨s, hsN⟩ = ρ (inclusion hTN ⟨j, hj⟩) := by
    have h2 : (⟨s, hsN⟩ : ↥(normalizer (M : Set X))) =
        ⟨s * j⁻¹, hsjN⟩ * inclusion hTN ⟨j, hj⟩ := Subtype.ext (by simp)
    rw [h2, map_mul, h1, one_mul]
  have hφA : ρ ⟨s, hsN⟩ ∈ alternatingGroup (Fin 5) := by
    rw [hρs]
    exact hA ⟨j, hj⟩
  have hφ2 : ρ ⟨s, hsN⟩ * ρ ⟨s, hsN⟩ = 1 := by
    rw [← map_mul]
    have h2 : (⟨s, hsN⟩ : ↥(normalizer (M : Set X))) * ⟨s, hsN⟩ = 1 := Subtype.ext hs2
    rw [h2, map_one]
  have hφ1 : ρ ⟨s, hsN⟩ ≠ 1 := fun h => hsK (hρ.mem_coreActionKernel hM hsN h)
  intro x hx
  have hxN := hX₀N hx
  refine hρ.mem_coreActionKernel hM hxN (eq_one_of_odd_commute_five hφA hφ2 hφ1 ?_ ?_)
  · have h3 : Odd (orderOf x) := by
      have h4 : orderOf (⟨x, hx⟩ : ↥X₀) ∣ Nat.card ↥X₀ := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h4
      exact hodd.of_dvd_nat h4
    have h5 : orderOf (ρ ⟨x, hxN⟩) ∣ orderOf (⟨x, hxN⟩ : ↥(normalizer (M : Set X))) :=
      orderOf_map_dvd ρ _
    rw [Subgroup.orderOf_mk] at h5
    exact h3.of_dvd_nat h5
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hX₀s hx))

theorem swap_type_in [Finite X] {Y T : Subgroup X} {x : X} (hxY : x ∈ Y) (hx : orderOf x = 2)
    (hMY : M ≤ Y) (hMpc : IsPComponent 2 (M.subgroupOf Y))
    (hne : M.map (MulAut.conj x).toMonoidHom ≠ M)
    (hTM : T ≤ M ⊔ M.map (MulAut.conj x).toMonoidHom) (hTC : T ≤ centralizer ({x} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf ((M ⊔ M.map (MulAut.conj x).toMonoidHom) ⊓
      centralizer ({x} : Set X)))) :
    Nonempty (↥T ⧸ Open.fusionZStar ↥T ≃* ↥M ⧸ Open.fusionZStar ↥M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : x⁻¹ = x := by
    have h1 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
    exact inv_eq_of_mul_eq_one_right h1
  set x' : ↥Y := ⟨x, hxY⟩ with hx'def
  have hx' : orderOf x' = 2 := by rw [hx'def, Subgroup.orderOf_mk]; exact hx
  set M₀ := M.subgroupOf Y with hM₀def
  set Mx := M.map (MulAut.conj x).toMonoidHom with hMxdef
  have hM₀ : M₀.map Y.subtype = M := map_subgroupOf_eq_of_le hMY
  have hconj := map_conjugate_subtype hxY hx2 M₀
  rw [← hx'def, hM₀, ← hMxdef] at hconj
  have hMxY : Mx ≤ Y := by
    rw [← hconj]
    exact map_subtype_le _
  have hsup : (M₀ ⊔ conjugate M₀ x').map Y.subtype = M ⊔ Mx := by
    rw [Subgroup.map_sup, hconj, hM₀]
  have hTY : T ≤ Y := hTM.trans (sup_le hMY hMxY)
  set T₀ := T.subgroupOf Y with hT₀def
  have hne₀ : M₀ ≠ conjugate M₀ x' := by
    intro h
    apply hne
    rw [← hconj, ← h, hM₀]
  have heq : (M₀ ⊔ conjugate M₀ x') ⊓ centralizer ({x'} : Set ↥Y) =
      ((M ⊔ Mx) ⊓ centralizer ({x} : Set X)).subgroupOf Y := by
    rw [centralizer_mk_eq hxY, ← hsup]
    ext y
    simp only [mem_inf, mem_subgroupOf]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨⟨y, h1, rfl⟩, h2⟩
    · rintro ⟨⟨z, hz, hzy⟩, h2⟩
      have hzy' : z = y := Subtype.ext hzy
      exact ⟨hzy' ▸ hz, h2, y.2⟩
  have hle : (M ⊔ Mx) ⊓ centralizer ({x} : Set X) ≤ Y :=
    inf_le_left.trans (sup_le hMY hMxY)
  have hTC₀ : T₀ ≤ (M₀ ⊔ conjugate M₀ x') ⊓ centralizer ({x'} : Set ↥Y) := by
    rw [heq]
    intro y hy
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hTM (mem_subgroupOf.mp hy), hTC (mem_subgroupOf.mp hy)⟩)
  have hTpc₀ : IsPComponent 2
      (T₀.subgroupOf ((M₀ ⊔ conjugate M₀ x') ⊓ centralizer ({x'} : Set ↥Y))) := by
    rw [heq, hT₀def, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hle 2
      Nat.prime_two]
    exact hTpc
  obtain ⟨φ⟩ := CatLeaf.swap_case_type hx' M₀ hMpc hne₀ T₀ hTC₀ hTpc₀
  exact ⟨(Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hTY)).symm.trans
    (φ.trans (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hMY)))⟩

end CFSG.ComponentClassification.SolMax
