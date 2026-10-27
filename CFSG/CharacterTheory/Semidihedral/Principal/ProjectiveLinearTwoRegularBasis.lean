module

public import CFSG.CharacterTheory.Semidihedral.Principal.ProjectiveLineFixedPoints
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralSignRotationRegularBasis
public import CFSG.CharacterTheory.Semidihedral.Principal.NoncyclicDihedralIndexTwo
public import CFSG.CharacterTheory.Semidihedral.SemilinearOddExtensions

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOuterQuotient CFSG.GorensteinWalter CFSG.Wreathed

universe u

theorem dihedral_closure_r_one_sr_zero (n : ℕ) [NeZero n] :
    Subgroup.closure {DihedralGroup.r (1 : ZMod n), DihedralGroup.sr 0} = ⊤ := by
  rw [eq_top_iff]
  rintro (i | i) -
  · have h : DihedralGroup.r i = DihedralGroup.r (1 : ZMod n) ^ i.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    rw [h]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  · have h : DihedralGroup.sr i = DihedralGroup.sr 0 * DihedralGroup.r (1 : ZMod n) ^ i.val := by
      rw [DihedralGroup.r_one_pow, DihedralGroup.sr_mul_r, zero_add, ZMod.natCast_zmod_val]
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem sylow_two_le_coordinateD {p f : ℕ} (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f)
    (F : Type u) [Field F] [Finite F] (hcard : Nat.card F = p ^ f)
    (Γ : Subgroup (Equiv.Perm (Omega F))) (hDΓ : coordinateD F ≤ Γ) (hΓE : Γ ≤ coordinateE F)
    (S : Sylow 2 Γ) {k : ℕ} (hk : 2 ≤ k) (e : (S : Subgroup Γ) ≃* DihedralGroup (2 ^ (k - 1)))
    (s : Γ) (hs : s ∈ S) : (s : Equiv.Perm (Omega F)) ∈ coordinateD F := by
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hodd, hf, hcard⟩
  let Γ' : Subgroup (coordinateE F) := Γ.subgroupOf (coordinateE F)
  let eΓ : Γ' ≃* Γ := Subgroup.subgroupOfEquivOfLe hΓE
  have hdih : HasDihedralSylowTwo Γ' :=
    hasDihedralSylowTwo_of_mulEquiv eΓ (SemilinearOddExtensions.dihedralSylows_of_supplied S hk e)
  have hG : SemilinearOddExtensions.specialLayer F ≤ Γ' := by
    intro x hx
    exact hDΓ (coordinateG_le_D F hx)
  have hoddimg := SemilinearOddExtensions.field_image_odd F hK Γ' hG hdih
  let y : coordinateE F := ⟨s, hΓE s.2⟩
  have hyΓ' : y ∈ Γ' := s.2
  have himg : fieldProjection F y ∈ SemilinearOddExtensions.fieldImage F Γ' :=
    Subgroup.mem_map_of_mem _ hyΓ'
  obtain ⟨n, hn⟩ := (Sylow.isPGroup' S) ⟨s, hs⟩
  have hsn : s ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hyn : y ^ 2 ^ n = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hsn
    simpa [y] using this
  have hord1 : orderOf (fieldProjection F y) ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hyn, map_one]
  have hord2 :
      orderOf (fieldProjection F y) ∣ Nat.card (SemilinearOddExtensions.fieldImage F Γ') := by
    rw [← Subgroup.orderOf_mk (fieldProjection F y) himg]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ n) (Nat.card (SemilinearOddExtensions.fieldImage F Γ')) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hoddimg)
  have hone : orderOf (fieldProjection F y) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
  have hker : y ∈ (fieldProjection F).ker := orderOf_eq_one_iff.mp hone
  rw [fieldProjection_ker] at hker
  exact hker

theorem projective_linear_two_principal_regular_integral_basis {p f : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hf : 1 ≤ f) (F : Type) [Field F] [Fintype F] (hcard : Nat.card F = p ^ f)
    (Γ : Subgroup (Equiv.Perm (Omega F))) (hDΓ : coordinateD F ≤ Γ) (hΓE : Γ ≤ coordinateE F)
    {k : ℕ} (hk : 2 ≤ k)
    (hS : ∃ S : Sylow 2 Γ, Nonempty ((S : Subgroup Γ) ≃* DihedralGroup (2 ^ (k - 1))))
    (hG : ∃ T : Sylow 2 (coordinateG F), ¬ IsCyclic (T : Subgroup (coordinateG F)))
    (basis : FiniteIrreducibleCharacterBasis Γ) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    let φ : Γ → ℂ := fun g =>
      (Nat.card {x : Omega F // (g : Equiv.Perm (Omega F)) x = x} : ℂ) - 1
    let δ : Γ → ℂ := fun g =>
      if ∃ (d : coordinateD F) (σ : F ≃+* F) (a : Matrix.GeneralLinearGroup (Fin 2) F),
          (g : Equiv.Perm (Omega F)) = d * fieldExtension F σ ∧
            coordinatePGLAction F (Matrix.ProjGenLinGroup.mk a) = d ∧ IsSquare (a.det : F)
      then 1 else -1
    let e : ℤ := if Nat.card F % 4 = 1 then 1 else -1
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let h := 2 ^ (k - 2) - 1
    3 ≤ k ∧
    ∃ (lδ lφ lδφ : basis.index) (ψ : Fin h → basis.index),
      (∀ g, (basis.representation lδ).character g = δ g) ∧
      (∀ g, (basis.representation lφ).character g = φ g) ∧
      (∀ g, (basis.representation lδφ).character g = δ g * φ g) ∧
      [principal, lδ, lφ, lδφ].Nodup ∧ Function.Injective ψ ∧
      (∀ i, ψ i ≠ principal ∧ ψ i ≠ lδ ∧ ψ i ≠ lφ ∧ ψ i ≠ lδφ) ∧
      (∀ ℓ, ℓ ∈ B ↔ ℓ = principal ∨ ℓ = lδ ∨ ℓ = lφ ∨ ℓ = lδφ ∨ ∃ i, ℓ = ψ i) ∧
      (∀ ℓ ∈ B, Odd (Module.finrank ℂ (basis.representation ℓ).vector) ↔
        ℓ = principal ∨ ℓ = lδ ∨ ℓ = lφ ∨ ℓ = lδφ) ∧
      Module.finrank ℂ (basis.representation principal).vector = 1 ∧
      Module.finrank ℂ (basis.representation lδ).vector = 1 ∧
      Module.finrank ℂ (basis.representation lφ).vector = Nat.card F ∧
      Module.finrank ℂ (basis.representation lδφ).vector = Nat.card F ∧
      (∀ i, (Module.finrank ℂ (basis.representation (ψ i)).vector : ℤ) = Nat.card F + e) ∧
      (∀ i (y : Γ), Odd (orderOf y) → (basis.representation (ψ i)).character y = φ y + e) ∧
      LinearIndependent ℤ ![oddRestriction (1 : Γ → ℂ), oddRestriction (1 + (e : ℂ) • φ)] ∧
      Submodule.span ℤ {oddRestriction (1 : Γ → ℂ), oddRestriction (1 + (e : ℂ) • φ)} =
        oddRestrictionLattice basis B ∧
      (∀ i : Fin 4 ⊕ Fin h,
        oddRestriction (basis.representation
            (Sum.elim ![principal, lδ, lφ, lδφ] ψ i)).character =
          dihedralRegularRows e h i 0 • oddRestriction (1 : Γ → ℂ) +
            dihedralRegularRows e h i 1 • oddRestriction (1 + (e : ℂ) • φ)) ∧
      (dihedralRegularRows e h).transpose * dihedralRegularRows e h =
        !![4, -2; -2, ((2 ^ (k - 2) + 1 : ℕ) : ℤ)] := by
  intro φ δ e B h
  obtain ⟨S, ⟨eS⟩⟩ := hS
  have hqodd : Odd (Nat.card F) := by
    rw [hcard]
    exact hodd.pow
  have hF2 : ringChar F ≠ 2 := by
    intro h2
    have h' := FiniteField.even_card_iff_char_two.mp h2
    rw [← Nat.card_eq_fintype_card] at h'
    obtain ⟨m, hm⟩ := hqodd
    omega
  have hq3 : 3 ≤ Nat.card F := by
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd hodd (by decide)
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    rw [hcard]
    calc 3 ≤ p := h3
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hεe : ((e : ℤ) : ℂ) = if Nat.card F % 4 = 1 then 1 else -1 := by
    simp only [e]
    split_ifs <;> simp
  have he : e = 1 ∨ e = -1 := by
    simp only [e]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hGΓ : coordinateG F ≤ Γ := (coordinateG_le_D F).trans hDΓ
  obtain ⟨_hnf, ⟨lam, hlam⟩, ⟨c₀, hc₀⟩, hδsq, ⟨_lδ, lφ, _lδφ, _hδchar, hφchar, _hδφchar, _hnodup,
      hP, _hdeg1, _hdegδ, hdegφ, _hdegδφ, _hkerφ, _hkerδφ⟩, ⟨_hd1, _hd2, _hd3, _hd4, _hd5, hd6⟩,
      _hrestrict, hδL, _hδodd, hXclause, _hJclause⟩ :=
    projective_linear_two_four_principal_odd_degree_characters hp hodd hf F hcard Γ hDΓ hΓE
      (MonoidHom.id Γ) Function.surjective_id basis ideal principal hprincipal
  have hlam' : ∀ g : Γ, (lam g : ℂ) = δ g := fun g => hlam g
  have hφchar' : ∀ g : Γ, (basis.representation lφ).character g = φ g := fun g => hφchar g
  have hδsq' : ∀ g : Γ, δ g * δ g = 1 := fun g => hδsq g
  have hδval : ∀ g : Γ, δ g = 1 ∨ δ g = -1 := fun g => mul_self_eq_one_iff.mp (hδsq' g)
  have hδmul : ∀ a b : Γ, δ (a * b) = δ a * δ b := by
    intro a b
    rw [← hlam', map_mul, Units.val_mul, hlam', hlam']
  have hδc₀ : δ c₀ = -1 := (hδval c₀).resolve_left hc₀
  let J : Subgroup Γ := lam.ker
  have hmemJ : ∀ g : Γ, g ∈ J ↔ δ g = 1 := fun g => by
    change lam g = 1 ↔ δ g = 1
    rw [← hlam', Units.val_eq_one]
  have hJ : J.index = 2 := by
    refine Subgroup.index_eq_two_iff.mpr ⟨c₀, fun b => ?_⟩
    rw [hmemJ, hmemJ, hδmul, hδc₀]
    rcases hδval b with hb | hb
    · rw [hb]
      exact Or.inr ⟨rfl, by norm_num⟩
    · rw [hb]
      exact Or.inl ⟨by norm_num, by norm_num⟩
  let L : Subgroup Γ := (coordinateG F).comap (Γ.subtype.comp (MonoidHom.id Γ))
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hodd, hf, hcard⟩
  have hGnormalE : ((coordinateG F).subgroupOf (coordinateE F)).Normal := by
    rw [← theta_ker F hK]
    infer_instance
  have hLnormal : L.Normal := ⟨fun n hn g =>
    hGnormalE.conj_mem (Subgroup.inclusion hΓE n) hn (Subgroup.inclusion hΓE g)⟩
  have hLJ : L ≤ J := fun g hg => (hmemJ g).mpr (hδL g hg)
  have hL : ∃ T : Sylow 2 L, ¬ IsCyclic (T : Subgroup L) := by
    obtain ⟨T, hT⟩ := hG
    let ι : L →* coordinateG F :=
      MonoidHom.codRestrict ((Γ.subtype.comp (MonoidHom.id Γ)).comp L.subtype) (coordinateG F)
        fun x => x.2
    have hι : Function.Injective ι := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : coordinateG F => (z : Equiv.Perm (Omega F))) hxy
    have hιs : Function.Surjective ι := by
      intro g
      exact ⟨⟨⟨g, hGΓ g.2⟩, g.2⟩, rfl⟩
    refine ⟨T.comapOfInjective ι hι (by rw [MonoidHom.range_eq_top.mpr hιs]; exact le_top),
      fun hcyc => hT ?_⟩
    rw [Sylow.coe_comapOfInjective] at hcyc
    exact isCyclic_of_surjective (ι.subgroupComap T)
      (MonoidHom.subgroupComap_surjective ι T hιs)
  obtain ⟨hk3, hSL, -, -, ⟨eSL⟩, -⟩ := noncyclic_normal_dihedral_subgroup_fills_index_two_part S hk
    ⟨eS.symm⟩ L J hJ hLJ hL
  set M := 2 ^ (k - 1) with hMdef
  have hM4 : 4 ≤ M := by
    rw [hMdef]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hhalf : M / 2 = 2 ^ (k - 2) := by
    rw [hMdef, show k - 1 = (k - 2) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  have hhalfeven : Even (M / 2) := by
    rw [hhalf]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hM2 : M = M / 2 + M / 2 := by
    rw [hhalf, hMdef, show k - 1 = (k - 2) + 1 by omega, pow_succ]
    ring
  have : NeZero M := ⟨by omega⟩
  let r : (S : Subgroup Γ) := eS.symm (DihedralGroup.r 1)
  let s : (S : Subgroup Γ) := eS.symm (DihedralGroup.sr 0)
  have hr : orderOf r = M := by
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hs : orderOf s = 2 := by
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have hrel : s * r * s = r⁻¹ := by
    simp only [r, s, ← map_mul, ← map_inv]
    congr 1
    rw [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
    congr 1
    ring
  have hgen : Subgroup.closure {r, s} = ⊤ := by
    have h := congrArg (Subgroup.map eS.symm.toMonoidHom) (dihedral_closure_r_one_sr_zero M)
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ eS.symm.surjective,
      Set.image_pair] at h
    exact h
  have hcardS : Nat.card (S : Subgroup Γ) = 2 * M := by
    rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
  have hrJ : (r : Γ) ∉ J := by
    intro hrJ
    have hle : Subgroup.zpowers (r : Γ) ≤ (S : Subgroup Γ) ⊓ L := by
      rw [hSL, Subgroup.zpowers_le]
      exact ⟨r.2, hrJ⟩
    have hcardSL : Nat.card ((S : Subgroup Γ) ⊓ L : Subgroup Γ) = M := by
      rw [Nat.card_congr eSL.toEquiv, DihedralGroup.nat_card, hMdef,
        show k - 1 = (k - 2) + 1 by omega, pow_succ]
      ring
    have heq : Subgroup.zpowers (r : Γ) = (S : Subgroup Γ) ⊓ L := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [hcardSL, Nat.card_zpowers, Subgroup.orderOf_coe, hr]
    have hcyc : IsCyclic ((S : Subgroup Γ) ⊓ L : Subgroup Γ) := by
      rw [← heq]
      infer_instance
    exact DihedralGroup.not_isCyclic (Nat.one_lt_two_pow (by omega)).ne'
      (isCyclic_of_surjective eSL.toMonoidHom eSL.surjective)
  have hδr : δ (r : Γ) = -1 := (hδval _).resolve_left fun h1 => hrJ ((hmemJ _).mpr h1)
  let t : Γ := (r : Γ) ^ (M / 2)
  have hδt : δ t = 1 := by
    have hpow : ∀ n : ℕ, δ ((r : Γ) ^ n) = δ (r : Γ) ^ n := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero, ← hlam', map_one, Units.val_one]
      | succ n ih => rw [pow_succ, hδmul, ih, pow_succ]
    change δ ((r : Γ) ^ (M / 2)) = 1
    rw [hpow, hδr, hhalfeven.neg_one_pow]
  have htS : t ∈ (S : Subgroup Γ) := Subgroup.pow_mem _ r.2 _
  have htL : t ∈ L := by
    have : t ∈ (S : Subgroup Γ) ⊓ J := ⟨htS, (hmemJ t).mpr hδt⟩
    rw [← hSL] at this
    exact this.2
  have hrM : orderOf ((r : Γ) : Equiv.Perm (Omega F)) = M := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hr]
  have ht1 : ((t : Γ) : Equiv.Perm (Omega F)) ≠ 1 := by
    intro h1
    have h1' : ((r : Γ) : Equiv.Perm (Omega F)) ^ (M / 2) = 1 := by
      rw [← h1]
      rfl
    exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hrM]; omega) h1'
  have ht2 : ((t : Γ) : Equiv.Perm (Omega F)) * ((t : Γ) : Equiv.Perm (Omega F)) = 1 := by
    have h : ((t : Γ) : Equiv.Perm (Omega F)) = ((r : Γ) : Equiv.Perm (Omega F)) ^ (M / 2) := rfl
    rw [h, ← pow_add, ← hM2, ← hrM, pow_orderOf_eq_one]
  have hrD : ((r : Γ) : Equiv.Perm (Omega F)) ∈ coordinateD F :=
    sylow_two_le_coordinateD hp hodd hf F hcard Γ hDΓ hΓE S hk eS (r : Γ) r.2
  obtain ⟨X, hX, htX⟩ := exists_sl_sq_neg_one_of_involution hF2 htL ht2 ht1
  have hφt : φ t = ((e : ℤ) : ℂ) := by
    rw [hεe]
    exact (hXclause t X hX htX).1
  have hrot : ∀ j : ℕ, 1 ≤ j → j < M → ∀ x : Omega F,
      (((r : Γ) : Equiv.Perm (Omega F)) ^ j) x = x ↔
        (((r : Γ) : Equiv.Perm (Omega F)) ^ (M / 2)) x = x :=
    fun j hj1 hjM x => fixed_iff_of_two_power_order hF2 hrD ⟨k - 1, hMdef⟩ hM4 hrM j hj1 hjM x
  have hβr : ∀ j : ℕ, 1 ≤ j → j < M →
      (basis.representation lφ).character ((r : Γ) ^ j) = (e : ℂ) := by
    intro j hj1 hjM
    rw [hφchar', ← hφt]
    change (Nat.card {x : Omega F // (((r : Γ) ^ j : Γ) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 =
      (Nat.card {x : Omega F // (((r : Γ) ^ (M / 2) : Γ) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1
    have hc : Nat.card {x : Omega F // (((r : Γ) ^ j : Γ) : Equiv.Perm (Omega F)) x = x} =
        Nat.card {x : Omega F // (((r : Γ) ^ (M / 2) : Γ) : Equiv.Perm (Omega F)) x = x} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => hrot j hj1 hjM x)
    rw [hc]
  obtain ⟨y₀, hy₀odd, hy₀fix⟩ : ∃ y₀ : Γ, Odd (orderOf y₀) ∧
      Nat.card {x : Omega F // (y₀ : Equiv.Perm (Omega F)) x = x} = 1 := by
    refine ⟨⟨translation F 1, hGΓ (Subgroup.subset_closure (Or.inl ⟨1, rfl⟩))⟩, ?_,
      card_fixed_translation one_ne_zero⟩
    rw [← Subgroup.orderOf_coe]
    exact odd_orderOf_translation hqodd 1
  have hy₀ : ∃ y₀ : Γ, Odd (orderOf y₀) ∧
      (basis.representation lφ).character y₀ ≠ (Nat.card F : ℂ) := by
    refine ⟨y₀, hy₀odd, ?_⟩
    rw [hφchar']
    change (Nat.card {x : Omega F // (y₀ : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 ≠ _
    rw [hy₀fix, Nat.cast_one, sub_self]
    exact_mod_cast (show (0 : ℕ) ≠ Nat.card F by omega)
  have hlam2 : ∀ g : Γ, lam g ^ 2 = 1 := by
    intro g
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hlam', sq, hδsq', Units.val_one]
  have hlamr : (lam (r : Γ) : ℂ) = -1 := by rw [hlam', hδr]
  have hβ : lφ ∈ B := (hP lφ (by simp)).2.1
  have hq : (basis.representation lφ).character 1 = (Nat.card F : ℂ) := by
    rw [show (basis.representation lφ).character 1 =
      (Module.finrank ℂ (basis.representation lφ).vector : ℂ) from Representation.char_one _,
      hdegφ]
  have hlamβ : (fun g => (lam g : ℂ) * (basis.representation lφ).character g) ≠
      (basis.representation lφ).character := by
    intro h
    apply hd6
    funext g
    have := congrFun h g
    simp only [hlam', hφchar'] at this
    exact this.symm
  have hres := dihedral_sign_and_constant_rotation_character_regular_basis ideal hk3 hMdef S r s
    hr hs hrel hgen hcardS basis principal hprincipal lam hlam2 hlamr lφ hβ (Nat.card F) hq
    hqodd (by omega) e he hβr hlamβ hy₀
  have hφfun : (basis.representation lφ).character = φ := funext hφchar'
  rw [hhalf, hφfun] at hres
  obtain ⟨labelLam, labelLamβ, ψ, hcharLam, hcharLamβ, hψinj, hne12, hne13, hne14, hne23, hne24,
    hne34, hψne, hB, hdeg1, hdegLam, hdegβ, hdegLamβ, hψdeg, hψodd, hoddiff, hli, hspan, -, -,
    hrows, hgram⟩ := hres
  refine ⟨hk3, labelLam, lφ, labelLamβ, ψ, fun g => ?_, hφchar', fun g => ?_, ?_, hψinj, hψne,
    hB, hoddiff, hdeg1, hdegLam, hdegβ, hdegLamβ, hψdeg, hψodd, hli, hspan, hrows, hgram⟩
  · rw [hcharLam]
    exact hlam' g
  · rw [hcharLamβ]
    exact congrArg (· * φ g) (hlam' g)
  · simp [List.nodup_cons, hne12, hne13, hne14, hne23, hne24, hne34]

end CFSG.Semidihedral.Principal
