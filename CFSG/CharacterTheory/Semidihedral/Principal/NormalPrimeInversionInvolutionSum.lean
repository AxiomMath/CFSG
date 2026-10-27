module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeInversionFamily
public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistBlocks
public import CFSG.CharacterTheory.Wreathed.CoprimeClassUnitRatio

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G]

theorem primitiveRoot_add_inv_ne_sign {ℓ : ℕ} (hℓ : 5 ≤ ℓ) (hprime : ℓ.Prime) {z : ℂ}
    (hz : IsPrimitiveRoot z ℓ) (c : ℂ) (hc : c = 1 ∨ c = -1) : z + z⁻¹ ≠ c := by
  intro h
  have hz0 : z ≠ 0 := hz.ne_zero (by omega)
  have hquad : z ^ 2 + 1 = c * z := by
    have h' := congrArg (· * z) h
    simp only [add_mul, inv_mul_cancel₀ hz0] at h'
    rw [← h']
    ring
  have hsix : z ^ 6 = 1 := by
    rcases hc with rfl | rfl
    · have h3 : z ^ 3 = -1 := by linear_combination (z + 1) * hquad
      calc z ^ 6 = (z ^ 3) ^ 2 := by ring
        _ = 1 := by rw [h3]; norm_num
    · have h3 : z ^ 3 = 1 := by linear_combination (z - 1) * hquad
      calc z ^ 6 = (z ^ 3) ^ 2 := by ring
        _ = 1 := by rw [h3]; norm_num
  have hdvd : ℓ ∣ 6 := hz.dvd_of_pow_eq_one 6 hsix
  have hle : ℓ ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases ℓ
  · norm_num at hdvd
  · exact absurd hprime (by norm_num)

omit [Fintype G] in
theorem prime_dvd_index_centralizer_of_not_mem [Finite G] {ℓ : ℕ} [Fact ℓ.Prime] (W : Sylow ℓ G)
    (hWnormal : (W : Subgroup G).Normal) (hW : Nat.card W = ℓ) {c : G}
    (hc : c ∉ Subgroup.centralizer (W : Set G)) :
    ℓ ∣ (Subgroup.centralizer ({c} : Set G)).index := by
  have hp : ℓ.Prime := Fact.out
  have hnot : ¬ ℓ ∣ Nat.card (Subgroup.centralizer ({c} : Set G)) := by
    intro hdvd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({c} : Set G)) ℓ
      hdvd
    have hyord : orderOf (y : G) = ℓ := by rw [Subgroup.orderOf_coe, hy]
    have hyW : (y : G) ∈ (W : Subgroup G) := by
      have hpgroup : IsPGroup ℓ (Subgroup.zpowers (y : G)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyord, pow_one])
      obtain ⟨Q, hQ⟩ := hpgroup.exists_le_sylow
      have hQW : Q = W := by
        let := Sylow.unique_of_normal W hWnormal
        exact Subsingleton.elim _ _
      exact hQW ▸ hQ (Subgroup.mem_zpowers _)
    have hyne : (y : G) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hyord
      exact hp.one_lt.ne hyord
    have hgen : Subgroup.zpowers (y : G) = (W : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyW)
      rw [Nat.card_zpowers, hyord, hW]
    apply hc
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : w ∈ (W : Subgroup G) := hw
    rw [← hgen] at hw'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
    have hcy : (y : G) * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp y.2
    exact (Commute.zpow_left hcy k).eq
  have hcardG : ℓ ∣ Nat.card G := by
    rw [← hW]
    exact Subgroup.card_subgroup_dvd_card _
  rw [← Subgroup.card_mul_index (Subgroup.centralizer ({c} : Set G))] at hcardG
  exact (hp.dvd_mul.mp hcardG).resolve_left hnot

theorem normal_prime_inversion_principal_block_involution_sum
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ]
    (hℓ : 5 ≤ ℓ) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (W : Sylow ℓ G)
    (hWnormal : (W : Subgroup G).Normal) (hW : Nat.card W = ℓ)
    (hindex : (Subgroup.centralizer (W : Set G)).index = 2) :
    let K := Subgroup.centralizer (W : Set G)
    let b : ℕ := (Finset.univ.filter fun x : G => x ∉ K ∧ orderOf x = 2).card
    let h : basis.index → ℂ := fun θ => (Nat.card G : ℂ)⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x : G => orderOf x = 2), (basis.representation θ).character x
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    (∀ w ∈ (W : Subgroup G), w ≠ 1 →
      ∑ θ ∈ B, h θ ^ 2 * (basis.representation θ).character w /
          (basis.representation θ).character 1 =
        2 * (b : ℂ) ^ 2 / (Nat.card G : ℂ) ^ 2) ∧
    ∃ (lam : basis.index) (ψ : ℕ → basis.index),
      (∀ x, (basis.representation lam).character x = if x ∈ K then 1 else -1) ∧
      lam ≠ principal ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ψ i ≠ principal ∧ ψ i ≠ lam) ∧
      Set.InjOn ψ (Finset.Icc 1 ((ℓ - 1) / 2)) ∧
      B = insert principal (insert lam ((Finset.Icc 1 ((ℓ - 1) / 2)).image ψ)) ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ∀ g : G,
        starRingEnd ℂ ((basis.representation (ψ i)).character g) =
          (basis.representation (ψ i)).character g) ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), (basis.representation (ψ i)).character 1 = 2) ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ∀ x : G, ¬ ℓ ∣ orderOf x →
        (basis.representation (ψ i)).character x = 1 + (basis.representation lam).character x) ∧
      (∀ w ∈ (W : Subgroup G), w ≠ 1 →
        ∑ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), (basis.representation (ψ i)).character w = -1) := by
  intro K b h B
  have hp : ℓ.Prime := Fact.out
  have hℓ2 : ℓ ≠ 2 := by omega
  obtain ⟨u, huW, hu1⟩ : ∃ u ∈ (W : Subgroup G), u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : (W : Subgroup G) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [hbot, Subgroup.card_bot] at hW
    exact hp.one_lt.ne hW
  have hu : orderOf u = ℓ := by
    have hdvd : orderOf u ∣ ℓ := by
      rw [← hW]
      exact Subgroup.orderOf_dvd_natCard _ huW
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hu1
    · exact h1
  have hPu : (W : Subgroup G) = Subgroup.zpowers u := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huW)
    rw [Nat.card_zpowers, hu, hW]
  have hrel :
      (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2 := by
    have hNtop : Subgroup.normalizer (W : Set G) = ⊤ := by
      have := hWnormal
      exact Subgroup.normalizer_eq_top (H := (W : Subgroup G))
    rw [hNtop, Subgroup.relIndex_top_right]
    exact hindex
  obtain ⟨δ, χ, ψ, hδ, hχp, hψne, hψinj, hB, hreal, -, hψdeg, hψreg, hvals, -, -⟩ :=
    prime_order_sylow_inversion_normalizer_exact_principal_block_family basis ideal ℓ hℓ principal
      hprincipal W u hPu hW hrel
  have huK : u ∈ K := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [show (W : Set G) = (Subgroup.zpowers u : Set G) by rw [← hPu]; rfl] at hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left (Commute.refl u) k).eq
  have hWK : ∀ w ∈ (W : Subgroup G), w ∈ K := by
    intro w hw
    rw [hPu] at hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact K.zpow_mem huK k
  let sgn : G →* ℂˣ :=
    { toFun := fun x => if x ∈ K then 1 else -1
      map_one' := by simp [K.one_mem]
      map_mul' := fun x y => by
        simp only [K]
        rw [Subgroup.mul_mem_iff_of_index_two hindex]
        by_cases hx : x ∈ Subgroup.centralizer (W : Set G) <;>
          by_cases hy : y ∈ Subgroup.centralizer (W : Set G) <;> simp [hx, hy] }
  obtain ⟨lam, hlam⟩ := character_norm_one_basis_character basis
    (linearTwist sgn (basis.representation principal))
    (by rw [linearTwist_characterPairing, characterPairing_irreducible _ _
      (basis.irreducible principal) (basis.irreducible principal), ite_eq_left rfl])
  have hlamval : ∀ x, (basis.representation lam).character x = if x ∈ K then 1 else -1 := by
    intro x
    rw [hlam, linearTwist_character, hprincipal]
    by_cases hx : x ∈ K <;> simp [sgn, hx]
  have hlam1 : (basis.representation lam).character 1 = 1 := by
    simp [hlamval, K.one_mem]
  have hlamB : lam ∈ B := by
    rw [coefficientBlock_mem_iff, sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
    apply centralCharacterResidueHom_eq_of_class_values
    intro C
    obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective C
    set k := (Subgroup.centralizer ({c} : Set G)).index with hk
    set v := centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk c)
    have hvalP : (localCentralCharacterHom basis ideal principal v : ℂ) = k := by
      have h' := CFSG.Wreathed.centralCharacterScalar_conjugacyClassSum_mk basis c principal
      rw [hprincipal, Pi.one_apply, Pi.one_apply, mul_one, div_one] at h'
      exact h'
    have hvalL : (localCentralCharacterHom basis ideal lam v : ℂ) =
        k * (if c ∈ K then 1 else -1) := by
      have h' := CFSG.Wreathed.centralCharacterScalar_conjugacyClassSum_mk basis c lam
      rw [hlam1, div_one, hlamval c] at h'
      exact h'
    change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal principal v) =
      localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal lam v)
    by_cases hc : c ∈ K
    · have heq : localCentralCharacterHom basis ideal principal v =
          localCentralCharacterHom basis ideal lam v := by
        apply Subtype.ext
        rw [hvalP, hvalL]
        simp [hc]
      rw [heq]
    · have hdvd : ℓ ∣ k := prime_dvd_index_centralizer_of_not_mem W hWnormal hW hc
      have hk0 : ((k : ℕ) : ComplexAlgebraicIntegers ⧸ ideal) = 0 :=
        (CharP.cast_eq_zero_iff _ ℓ k).mpr hdvd
      have hP0 : localCentralCharacterHom basis ideal principal v =
          (k : localizedComplexIntegerRing ideal) := by
        apply Subtype.ext
        rw [hvalP]
        simp
      have hL0 : localCentralCharacterHom basis ideal lam v =
          (k : localizedComplexIntegerRing ideal) * (-1) := by
        apply Subtype.ext
        rw [hvalL]
        simp [hc]
      rw [hP0, hL0, map_mul, map_natCast, hk0, zero_mul]
  obtain ⟨g₀, hg₀⟩ : ∃ g : G, g ∉ K := by
    by_contra hcon
    push Not at hcon
    have hKtop : Subgroup.centralizer (W : Set G) = ⊤ := eq_top_iff.mpr fun g _ => hcon g
    rw [hKtop, Subgroup.index_top] at hindex
    omega
  have hlamp : lam ≠ principal := by
    intro heq
    have h' := congrFun (congrArg (fun θ => (basis.representation θ).character) heq) g₀
    simp only [hlamval g₀, hg₀, hprincipal, Pi.one_apply, ↓reduceIte] at h'
    norm_num at h'
  have hu_reg : ¬ ℓ ∣ orderOf (1 : G) := by
    rw [orderOf_one]
    exact hp.not_dvd_one
  have hone_mem : (1 : G) ∈ Subgroup.centralizer (W : Set G) := Subgroup.one_mem _
  have hj1 : 1 ∈ Finset.Icc 1 (ℓ - 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hu_lam : (basis.representation lam).character u = 1 := by
    simp [hlamval, huK]
  set r := (ℓ - 1) / 2 with hr
  have hψlam : ∀ i ∈ Finset.Icc 1 r, ψ i ≠ lam := by
    intro i hi heq
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    have hv := (hvals 1 hj1 1 hone_mem hu_reg).2 i hi
    rw [pow_one, mul_one, heq, hu_lam, mul_one] at hv
    set ζ := Complex.exp (2 * Real.pi * Complex.I / ℓ) with hζ
    have hprim : IsPrimitiveRoot (ζ ^ i) ℓ := by
      have hcop : Nat.Coprime i ℓ := by
        apply Nat.Coprime.symm
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      exact (Complex.isPrimitiveRoot_exp ℓ hp.ne_zero).pow_of_coprime i hcop
    have hsum : ζ ^ i + (ζ ^ i)⁻¹ = δ := by
      have hδsq : (δ : ℂ) * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
      rw [zpow_neg, zpow_natCast] at hv
      linear_combination (-(δ : ℂ)) * hv - (ζ ^ i + (ζ ^ i)⁻¹) * hδsq
    exact primitiveRoot_add_inv_ne_sign hℓ hp hprim δ
      (by rcases hδ with rfl | rfl <;> norm_num) hsum
  have hlamχ : lam = χ := by
    have hmem : lam ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := hlamB
    rw [hB, Finset.mem_insert, Finset.mem_insert, Finset.mem_image] at hmem
    rcases hmem with h1 | h1 | ⟨i, hi, hiψ⟩
    · exact absurd h1 hlamp
    · exact h1
    · exact absurd hiψ (hψlam i hi)
  subst hlamχ
  have hδ1 : δ = 1 := by
    have hv := (hvals 1 hj1 1 hone_mem hu_reg).1
    rw [pow_one, mul_one, hu_lam] at hv
    exact_mod_cast hv.symm
  subst hδ1
  have hψdeg2 : ∀ i ∈ Finset.Icc 1 r, (basis.representation (ψ i)).character 1 = 2 := by
    intro i hi
    rw [hψdeg i hi, hlam1]
    norm_num
  have hψreg' : ∀ i ∈ Finset.Icc 1 r, ∀ x : G, ¬ ℓ ∣ orderOf x →
      (basis.representation (ψ i)).character x = 1 + (basis.representation lam).character x := by
    intro i hi x hx
    rw [hψreg i hi x hx]
    push_cast
    ring
  have hψsum : ∀ w ∈ (W : Subgroup G), w ≠ 1 →
      ∑ i ∈ Finset.Icc 1 r, (basis.representation (ψ i)).character w = -1 := by
    intro w hw hw1
    rw [hPu] at hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    set j := (k % (ℓ : ℤ)).toNat with hjdef
    have hℓpos : (0 : ℤ) < ℓ := by exact_mod_cast hp.pos
    have hnonneg : 0 ≤ k % (ℓ : ℤ) := Int.emod_nonneg k hℓpos.ne'
    have hjlt : k % (ℓ : ℤ) < ℓ := Int.emod_lt_of_pos k hℓpos
    have hjcast : (j : ℤ) = k % (ℓ : ℤ) := Int.toNat_of_nonneg hnonneg
    have hupow : u ^ k = u ^ j := by
      rw [← zpow_natCast, hjcast, ← hu, zpow_mod_orderOf]
    have hj0 : j ≠ 0 := by
      intro hj0
      apply hw1
      rw [hupow, hj0, pow_zero]
    have hjmem : j ∈ Finset.Icc 1 (ℓ - 1) := by
      rw [Finset.mem_Icc]
      constructor
      · omega
      · have : (j : ℤ) < ℓ := by rw [hjcast]; exact hjlt
        omega
    have hjdvd : ¬ (ℓ : ℤ) ∣ (j : ℤ) := by
      intro hdvd
      rcases hdvd with ⟨c, hc⟩
      have hjpos : 0 < (j : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hj0
      have hjlt' : (j : ℤ) < ℓ := by rw [hjcast]; exact hjlt
      have hc1 : 0 < c := by
        by_contra hneg
        push Not at hneg
        nlinarith
      nlinarith
    rw [hupow]
    have hterm : ∀ i ∈ Finset.Icc 1 r, (basis.representation (ψ i)).character (u ^ j) =
        cyclicRoot ℓ ^ ((i : ℤ) * j) + cyclicRoot ℓ ^ (-((i : ℤ) * j)) := by
      intro i hi
      have hv := (hvals j hjmem 1 hone_mem hu_reg).2 i hi
      rw [mul_one, Int.cast_one, one_mul] at hv
      rw [hv]
      push_cast
      rfl
    rw [Finset.sum_congr rfl hterm]
    exact sum_cyclicRoot_pair_eq_neg_one hp hℓ2 hjdvd
  set I₂ := Finset.univ.filter (fun x : G => orderOf x = 2) with hI₂
  set a' := (I₂.filter fun x => x ∈ K).card with ha'
  set b' := (I₂.filter fun x => x ∉ K).card with hb'
  have hbb : b = b' := by
    simp only [b, hb', hI₂, Finset.filter_filter]
    congr 1
    ext x
    simp [and_comm]
  have hcardI : (I₂.card : ℂ) = a' + b' := by
    rw [← Finset.card_filter_add_card_filter_not (s := I₂) (fun x => x ∈ K)]
    push_cast
    rfl
  have hinv_reg : ∀ x ∈ I₂, ¬ ℓ ∣ orderOf x := by
    intro x hx
    rw [hI₂, Finset.mem_filter] at hx
    rw [hx.2]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hsum_lam : ∑ x ∈ I₂, (basis.representation lam).character x = a' - b' := by
    simp only [hlamval]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    simp [ha', hb']
    ring
  have hhP : h principal = (Nat.card G : ℂ)⁻¹ * (a' + b') := by
    simp only [h, hprincipal, Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← hI₂, hcardI]
  have hhL : h lam = (Nat.card G : ℂ)⁻¹ * (a' - b') := by
    simp only [h]
    rw [← hI₂, hsum_lam]
  have hhψ : ∀ i ∈ Finset.Icc 1 r, h (ψ i) = (Nat.card G : ℂ)⁻¹ * (2 * a') := by
    intro i hi
    simp only [h]
    rw [← hI₂, Finset.sum_congr rfl (fun x hx => hψreg' i hi x (hinv_reg x hx)),
      Finset.sum_add_distrib, hsum_lam, Finset.sum_const, nsmul_eq_mul, mul_one, hcardI]
    ring
  refine ⟨fun w hw hw1 => ?_, lam, ψ, hlamval, hlamp, fun i hi => ⟨(hψne i hi).1, hψlam i hi⟩,
    hψinj, hB, fun i hi g => hreal (ψ i) (by
      rw [hB, Finset.mem_insert, Finset.mem_insert, Finset.mem_image]
      exact Or.inr (Or.inr ⟨i, hi, rfl⟩)) g, hψdeg2, hψreg', hψsum⟩
  have hwK := hWK w hw
  have hnotP : principal ∉ insert lam ((Finset.Icc 1 r).image ψ) := by
    rw [Finset.mem_insert, Finset.mem_image]
    rintro (h1 | ⟨i, hi, hiψ⟩)
    · exact hlamp h1.symm
    · exact (hψne i hi).1 hiψ
  have hnotL : lam ∉ (Finset.Icc 1 r).image ψ := by
    rw [Finset.mem_image]
    rintro ⟨i, hi, hiψ⟩
    exact hψlam i hi hiψ
  rw [show B = insert principal (insert lam ((Finset.Icc 1 r).image ψ)) from hB,
    Finset.sum_insert hnotP, Finset.sum_insert hnotL, Finset.sum_image hψinj]
  have hψpart : ∑ i ∈ Finset.Icc 1 r, h (ψ i) ^ 2 * (basis.representation (ψ i)).character w /
      (basis.representation (ψ i)).character 1 =
        ((Nat.card G : ℂ)⁻¹ * (2 * a')) ^ 2 / 2 *
          ∑ i ∈ Finset.Icc 1 r, (basis.representation (ψ i)).character w := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hhψ i hi, hψdeg2 i hi]
    ring
  have hlamw : (basis.representation lam).character w = 1 := by simp [hlamval, hwK]
  rw [hψpart, hψsum w hw hw1, hhP, hhL, hprincipal, Pi.one_apply, Pi.one_apply, hlamw, hlam1,
    hbb]
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp
  ring

end CFSG.Semidihedral.Principal
