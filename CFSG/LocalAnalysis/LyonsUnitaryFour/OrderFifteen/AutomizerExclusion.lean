module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.PrincipalGram
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.ProductCharacterFormula
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ExponentTwo
public import CFSG.CharacterTheory.Blocks.NormTwo

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators

section Helpers

theorem trace_involutive_integer {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (hT : T * T = 1) : ∃ z : ℤ, LinearMap.trace ℂ V T = z := by
  set E : Module.End ℂ V := (2 : ℂ)⁻¹ • (1 + T) with hE
  have hidem : IsIdempotentElem E := by
    change E * E = E
    rw [hE, smul_mul_smul_comm, add_mul, one_mul, mul_add, mul_one, hT]
    have h2 : (1 : Module.End ℂ V) + T + (T + 1) = (2 : ℂ) • (1 + T) := by
      rw [two_smul]
      abel
    rw [h2, smul_smul]
    congr 1
    norm_num
  have htr := (LinearMap.IsIdempotentElem.isProj_range E hidem).trace
  have hTE : T = (2 : ℂ) • E - 1 := by
    rw [hE, smul_smul]
    norm_num
  refine ⟨2 * (Module.finrank ℂ (LinearMap.range E) : ℤ) - Module.finrank ℂ V, ?_⟩
  rw [hTE, map_sub, map_smul, LinearMap.trace_one, htr]
  push_cast
  ring

theorem character_integer_of_mul_self {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) {v : G} (hv : v * v = 1) :
    ∃ z : ℤ, ρ.character v = z :=
  trace_involutive_integer (ρ v) (by rw [← map_mul, hv, map_one])

theorem exists_isPPart_two_ne_one {G : Type*} [Group G] [Finite G] (g : G)
    (hg : ¬ Odd (orderOf g)) :
    ∃ a : G, CFSG.BlocksIsPPart 2 g a ∧ a ≠ 1 ∧ ∃ k : ℕ, orderOf a ∣ 2 ^ k := by
  obtain ⟨a, b, k, -, -, hab, habg, hak, hb⟩ :=
    finite_prime_primary_factorization g 2 Nat.prime_two
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hak
  refine ⟨a, ⟨b, habg, by rw [← hab.eq]; exact habg, ⟨m, hm⟩, orderOf_pos b, hb.symm⟩, ?_,
    ⟨k, hak⟩⟩
  intro ha1
  rw [ha1, one_mul] at habg
  apply hg
  rw [← habg]
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp ((Nat.Prime.coprime_iff_not_dvd
    Nat.prime_two).mp hb))

theorem mul_self_eq_one_of_isConj {G : Type*} [Group G] {x a : G} (hx : x * x = 1)
    (h : IsConj x a) : a * a = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
    _ = 1 := by rw [hx, mul_one, mul_inv_cancel]

theorem norm_two_degree_zero_support {ι : Type*} (B : Finset ι) (c : ι → ℤ) (d : ι → ℕ)
    (hd : ∀ l ∈ B, 0 < d l) (hnorm : ∑ l ∈ B, c l ^ 2 = 2)
    (hdeg : ∑ l ∈ B, c l * (d l : ℤ) = 0) :
    ∃ p ∈ B, ∃ q ∈ B, p ≠ q ∧ d p = d q ∧ c p ≠ 0 ∧ c q ≠ 0 ∧
      ∀ l ∈ B, c l ≠ 0 → l = p ∨ l = q := by
  classical
  have hnorm' : ∑ l : B, c l ^ 2 = 2 := by
    rw [Finset.sum_coe_sort B (fun l => c l ^ 2)]
    exact hnorm
  obtain ⟨p, q, hpq, hp, hq, hother⟩ :=
    CFSG.integer_norm_two_two_coefficients (fun l : B => c l) hnorm'
  have hdeg' : ∑ l : B, c l * (d l : ℤ) = 0 := by
    rw [Finset.sum_coe_sort B (fun l => c l * (d l : ℤ))]
    exact hdeg
  rw [Fintype.sum_eq_add p q hpq (fun l hl => by rw [hother l hl.1 hl.2, zero_mul])] at hdeg'
  have hdp := hd p p.2
  have hdq := hd q q.2
  have hpq' : (p : ι) ≠ q := fun h => hpq (Subtype.ext h)
  refine ⟨p, p.2, q, q.2, hpq', ?_, ?_, ?_, ?_⟩
  · rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq] at hdeg' <;> omega
  · rcases hp with hp | hp <;> rw [hp] <;> decide
  · rcases hq with hq | hq <;> rw [hq] <;> decide
  · intro l hl hcl
    by_contra hne
    push Not at hne
    exact hcl (hother ⟨l, hl⟩ (fun h => hne.1 (congrArg Subtype.val h))
      (fun h => hne.2 (congrArg Subtype.val h)))

theorem isConj_of_odd_orderOf_mul {G : Type*} [Group G] {u w : G} (hu : u * u = 1)
    (hw : w * w = 1) (hodd : Odd (orderOf (u * w))) : IsConj u w := by
  obtain ⟨k, hk⟩ := hodd
  set z := u * w with hz
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw
  have hinv : u * z * u⁻¹ = z⁻¹ := by
    rw [hz, huinv, mul_inv_rev, hwinv, huinv, ← mul_assoc, hu, one_mul]
  have hpow : ∀ j : ℕ, u * z ^ j = (z ^ j)⁻¹ * u := by
    intro j
    have h := congrArg (· ^ j) hinv
    simp only [conj_pow, inv_pow] at h
    calc u * z ^ j = (u * z ^ j * u⁻¹) * u := by group
      _ = (z ^ j)⁻¹ * u := by rw [h]
  have hzm : z ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one z
  refine isConj_iff.mpr ⟨(z ^ (k + 1))⁻¹, ?_⟩
  rw [inv_inv, mul_assoc, hpow (k + 1), ← mul_assoc, ← mul_inv_rev, ← pow_add]
  have h2 : z ^ (k + 1 + (k + 1)) = z := by
    rw [show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hzm, one_mul]
  rw [h2, hz, mul_inv_rev, hwinv, huinv, mul_assoc, hu, mul_one]

end Helpers

section Restriction

open scoped Classical

variable {H : Type} [Group H] [Fintype H]

theorem blocksInnerProduct_swap {G : Type} [Group G] [Fintype G] (f g : G → ℂ) :
    BlocksInnerProduct g f = starRingEnd ℂ (BlocksInnerProduct f g) := by
  unfold BlocksInnerProduct
  rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem blocksInnerProduct_restrict_sylowConj {P : Subgroup H} (ξ : H → ℂ)
    (hξ : ∀ g h : H, ξ (h * g * h⁻¹) = ξ g) (n : Subgroup.normalizer (P : Set H)) (j : ℕ)
    (θ : P → ℂ) :
    BlocksInnerProduct (fun x : P => ξ x) (sylowConj n j θ) =
      BlocksInnerProduct (fun x : P => ξ x) θ := by
  unfold BlocksInnerProduct sylowConj
  congr 1
  apply Fintype.sum_equiv (Subgroup.normalizerMonoidHom P (n ^ j)⁻¹).toEquiv
  intro x
  congr 1
  change ξ x = ξ ((Subgroup.normalizerMonoidHom P (n ^ j)⁻¹ x : P) : H)
  rw [coe_normalizerMonoidHom_inv_pow]
  have := hξ x ((n : H) ^ j)⁻¹
  rw [inv_inv] at this
  exact this.symm

theorem restrict_constant_of_orthogonal (P : Sylow 2 H)
    (e : (P : Subgroup H) ≃* Multiplicative SixteenVector)
    (n : Subgroup.normalizer ((P : Subgroup H) : Set H))
    (lam : Fin 3 → (↥(P : Subgroup H) → ℂ))
    (horbit : ∀ μ ∈ CFSG.BlocksIrr (P : Subgroup H), μ ≠ (fun _ => 1) →
      ∃! ij : Fin 3 × Fin 5, μ = sylowConj n ij.2 (lam ij.1))
    (ξ : H → ℂ) (hξ : ∀ g h : H, ξ (h * g * h⁻¹) = ξ g)
    (h1 : BlocksInnerProduct (lam 1 - lam 0) (fun x : (P : Subgroup H) => ξ x) = 0)
    (h2 : BlocksInnerProduct (lam 2 - lam 0) (fun x : (P : Subgroup H) => ξ x) = 0) :
    ∃ t : ℂ, ∀ x : (P : Subgroup H), x ≠ 1 → ξ x = t := by
  set res : ↥(P : Subgroup H) → ℂ := fun x => ξ x with hres
  set a := BlocksInnerProduct res (lam 0) with ha
  have hlam : ∀ i : Fin 3, BlocksInnerProduct res (lam i) = a := by
    have hsub : ∀ i : Fin 3, BlocksInnerProduct (lam i - lam 0) res = 0 →
        BlocksInnerProduct res (lam i) = a := by
      intro i hi
      rw [blocksInnerProduct_sub_left, sub_eq_zero] at hi
      rw [ha, blocksInnerProduct_swap, hi, ← blocksInnerProduct_swap]
    intro i
    fin_cases i
    · rfl
    · exact hsub 1 h1
    · exact hsub 2 h2
  have hm : ∀ ψ : AddChar SixteenVector ℂ, ψ ≠ 0 →
      BlocksInnerProduct res (sixteenChar e ψ) = a := by
    intro ψ hψ
    obtain ⟨ij, hij, -⟩ := horbit (sixteenChar e ψ) (sixteenChar_mem_blocksIrr e ψ)
      (fun h => hψ ((sixteenChar_eq_one_iff e ψ).mp h))
    rw [hij, blocksInnerProduct_restrict_sylowConj ξ hξ, hlam]
  refine ⟨BlocksInnerProduct res (sixteenChar e 0) - a, fun x hx => ?_⟩
  have hf := sixteenChar_fourier e res x
  have hsplit : ∀ ψ : AddChar SixteenVector ℂ,
      BlocksInnerProduct res (sixteenChar e ψ) * sixteenChar e ψ x =
        a * sixteenChar e ψ x + (if ψ = 0 then
          (BlocksInnerProduct res (sixteenChar e 0) - a) * sixteenChar e ψ x else 0) := by
    intro ψ
    by_cases hψ : ψ = 0
    · rw [ite_eq_left hψ, hψ]
      ring
    · rw [ite_eq_right hψ, hm ψ hψ, add_zero]
  rw [Finset.sum_congr rfl (fun ψ _ => hsplit ψ), Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_sixteenChar, ite_eq_right hx, mul_zero, zero_add, Finset.sum_ite_eq'] at hf
  rw [ite_eq_left (Finset.mem_univ _), sixteenChar_zero, mul_one] at hf
  exact hf

end Restriction

section Theorem

open scoped Classical

theorem simple_elementary_sixteen_order_five_automizer_impossible {H : Type} [Group H] [Finite H]
    [IsSimpleGroup H] (hnonab : ∃ a b : H, a * b ≠ b * a) (P : Sylow 2 H)
    (hP : Nonempty ((P : Subgroup H) ≃* Multiplicative (Fin 4 → ZMod 2)))
    (hidx : ((Subgroup.centralizer ((P : Subgroup H) : Set H)).subgroupOf
      (Subgroup.normalizer ((P : Subgroup H) : Set H))).index = 5)
    (hirr : ∀ A : Subgroup H, A ≤ P →
      (∀ n ∈ Subgroup.normalizer ((P : Subgroup H) : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) →
        A = ⊥ ∨ A = P) :
    False := by
  let _ : Fintype H := Fintype.ofFinite H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hP
  obtain ⟨hcard16, hcomm, hsq⟩ := elementarySixteen_facts e
  obtain ⟨ideal, hmax, hchar⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  have := hmax
  have := hchar
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := H)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation H) (principalFiniteComplexRepresentation_isIrreducible H)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨⟨n, lam, hlam, horbit, -, hαα, hββ, hαβ, hα1, hβ1⟩, -, -, hconst, hK, h3⟩ :=
    elementary_sixteen_order_five_principal_gram P ⟨e⟩ hidx hirr ideal basis principal hprincipal
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  set χ : basis.index → H → ℂ := fun l => (basis.representation l).character with hχ
  set deg : basis.index → ℕ := fun l => Module.finrank ℂ (basis.representation l).vector
    with hdeg
  have hχ1 : ∀ l, χ l 1 = deg l := fun l => Representation.char_one _
  have hdeg_pos : ∀ l, 0 < deg l := by
    intro l
    have h := irreducible_character_degree_ne_zero (basis.representation l) (basis.irreducible l)
    change χ l 1 ≠ 0 at h
    rw [hχ1] at h
    exact Nat.pos_of_ne_zero (fun h0 => h (by rw [h0, Nat.cast_zero]))
  have hdeg_one : ∀ l, l ≠ principal → deg l ≠ 1 := fun l hl h =>
    hl (CFSG.RankTwoShapes.simple_degree_one_eq_principal hnonab basis principal hprincipal l h)
  have hres_mem : ∀ l, (fun x : (P : Subgroup H) => χ l x) ∈ CFSG.BlocksVChar (P : Subgroup H) := by
    intro l
    rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup]
    have h := character_mem_virtualCharacters
      (inflatedFiniteComplexRepresentation (P : Subgroup H).subtype (basis.representation l))
    rw [inflatedFiniteComplexRepresentation_character] at h
    exact h
  have hlam_mem : ∀ i, lam i ∈ CFSG.BlocksVChar (P : Subgroup H) := fun i =>
    AddSubgroup.subset_closure (hlam i).1
  have hint : ∀ (i : Fin 3) (l : basis.index), ∃ z : ℤ,
      BlocksInnerProduct (lam i - lam 0) (fun x : (P : Subgroup H) => χ l x) = z := fun i l =>
    blocksInnerProduct_virtual_integer (AddSubgroup.sub_mem _ (hlam_mem i) (hlam_mem 0))
      (hres_mem l)
  choose z hz using hint
  have hcoeff : ∀ (i : Fin 3) (g : H), blocksInduction basis B (P : Subgroup H) (lam i - lam 0) g =
      ∑ l ∈ B, (z i l : ℂ) * χ l g := by
    intro i g
    unfold blocksInduction
    apply Finset.sum_congr rfl
    intro l _
    rw [blocksInduction_coeff, hz]
  have hgramz : ∀ i j : Fin 3,
      BlocksInnerProduct (blocksInduction basis B (P : Subgroup H) (lam i - lam 0))
        (blocksInduction basis B (P : Subgroup H) (lam j - lam 0)) =
        ((∑ l ∈ B, z i l * z j l : ℤ) : ℂ) := by
    intro i j
    rw [blocksInnerProduct_blocksInduction]
    push_cast
    apply Finset.sum_congr rfl
    intro l _
    rw [hz, hz, map_intCast]
  have hnorm1 : ∑ l ∈ B, z 1 l ^ 2 = 2 := by
    have h := hgramz 1 1
    rw [hαα] at h
    have h' : ((∑ l ∈ B, z 1 l * z 1 l : ℤ) : ℂ) = ((2 : ℤ) : ℂ) := by rw [← h]; norm_num
    have := Int.cast_injective h'
    simpa [sq] using this
  have hnorm2 : ∑ l ∈ B, z 2 l ^ 2 = 2 := by
    have h := hgramz 2 2
    rw [hββ] at h
    have h' : ((∑ l ∈ B, z 2 l * z 2 l : ℤ) : ℂ) = ((2 : ℤ) : ℂ) := by rw [← h]; norm_num
    have := Int.cast_injective h'
    simpa [sq] using this
  have hpair12 : ∑ l ∈ B, z 1 l * z 2 l = 1 := by
    have h := hgramz 1 2
    rw [hαβ] at h
    have h' : ((∑ l ∈ B, z 1 l * z 2 l : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by rw [← h]; norm_num
    exact Int.cast_injective h'
  have hdeg0 : ∀ i : Fin 3, i ≠ 0 → blocksInduction basis B (P : Subgroup H) (lam i - lam 0) 1 = 0 →
      ∑ l ∈ B, z i l * (deg l : ℤ) = 0 := by
    intro i _ h
    rw [hcoeff] at h
    simp_rw [hχ1] at h
    exact_mod_cast h
  have hdeg1 := hdeg0 1 (by decide) hα1
  have hdeg2 := hdeg0 2 (by decide) hβ1
  have hdeg_posB : ∀ l ∈ B, 0 < deg l := fun l _ => hdeg_pos l
  obtain ⟨p1, -, q1, -, hpq1, hdpq1, -, -, hsupp1⟩ :=
    norm_two_degree_zero_support B (z 1) deg hdeg_posB hnorm1 hdeg1
  obtain ⟨p2, -, q2, -, -, hdpq2, -, -, hsupp2⟩ :=
    norm_two_degree_zero_support B (z 2) deg hdeg_posB hnorm2 hdeg2
  have hsupp1' : ∀ l ∈ B, z 1 l ≠ 0 → deg l = deg p1 := by
    intro l hl hzl
    rcases hsupp1 l hl hzl with rfl | rfl
    · rfl
    · exact hdpq1.symm
  have hsupp2' : ∀ l ∈ B, z 2 l ≠ 0 → deg l = deg p2 := by
    intro l hl hzl
    rcases hsupp2 l hl hzl with rfl | rfl
    · rfl
    · exact hdpq2.symm
  obtain ⟨m, hm, hm1, hm2⟩ : ∃ m ∈ B, z 1 m ≠ 0 ∧ z 2 m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∑ l ∈ B, z 1 l * z 2 l = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      by_cases h1 : z 1 l = 0
      · rw [h1, zero_mul]
      · rw [hcon l hl h1, mul_zero]
    rw [h0] at hpair12
    exact absurd hpair12 (by decide)
  have hsupp : ∀ l ∈ B, (z 1 l ≠ 0 ∨ z 2 l ≠ 0) → deg l = deg p1 := by
    intro l hl hzl
    rcases hzl with h | h
    · exact hsupp1' l hl h
    · rw [hsupp2' l hl h, ← hsupp2' m hm hm2, hsupp1' m hm hm1]
  have hdeg_princ : deg principal = 1 := by
    have h : (basis.representation principal).character 1 = deg principal := hχ1 principal
    rw [hprincipal, Pi.one_apply] at h
    exact_mod_cast h.symm
  have hD1 : deg p1 ≠ 1 := by
    intro hD1
    have hp1p : p1 = principal := by
      by_contra h
      exact hdeg_one p1 h hD1
    have hq1p : q1 = principal := by
      by_contra h
      exact hdeg_one q1 h (by rw [← hdpq1]; exact hD1)
    exact hpq1 (hp1p.trans hq1p.symm)
  have hD2 : 2 ≤ deg p1 := by
    have := hdeg_pos p1
    omega
  have hprincB : principal ∈ B := coefficientBlock_self_mem _ _ _
  have hprinc : z 1 principal = 0 ∧ z 2 principal = 0 := by
    by_contra h
    rw [not_and_or] at h
    exact hD1 ((hsupp principal hprincB h).symm.trans hdeg_princ)
  have hcomp : ∀ l, z 1 l = 0 → z 2 l = 0 →
      ∃ t : ℂ, ∀ x : (P : Subgroup H), x ≠ 1 → χ l x = t := by
    intro l h1 h2
    apply restrict_constant_of_orthogonal P e n lam horbit (χ l)
      (fun g c => Representation.char_conj _ g c)
    · rw [hz 1 l, h1, Int.cast_zero]
    · rw [hz 2 l, h2, Int.cast_zero]
  obtain ⟨x, y, hx2, hy2, hxy⟩ : ∃ x y : H, orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
    have h1 :
        1 < Nat.card {c : ConjClasses H // ∃ x : H, orderOf x = 2 ∧ ConjClasses.mk x = c} := by
      rw [h3]
      norm_num
    have : Nontrivial {c : ConjClasses H // ∃ x : H, orderOf x = 2 ∧ ConjClasses.mk x = c} :=
      Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨c1, c2, hc⟩ :=
      exists_pair_ne {c : ConjClasses H // ∃ x : H, orderOf x = 2 ∧ ConjClasses.mk x = c}
    obtain ⟨x, hx, hxc⟩ := c1.2
    obtain ⟨y, hy, hyc⟩ := c2.2
    refine ⟨x, y, hx, hy, fun hxy => hc (Subtype.ext ?_)⟩
    rw [← hxc, ← hyc]
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr hxy
  have hxsq : x * x = 1 := by rw [← sq, ← hx2]; exact pow_orderOf_eq_one x
  have hysq : y * y = 1 := by rw [← sq, ← hy2]; exact pow_orderOf_eq_one y
  obtain ⟨c, hvP, hv1⟩ := exists_conj_mem_sylow_ne_one P hx2
  set v := c * x * c⁻¹ with hv
  have hvsq : v * v = 1 := mul_self_eq_one_of_isConj hxsq (isConj_iff.mpr ⟨c, rfl⟩)
  obtain ⟨ξ, hξB, hξ1, hξ2, hξp, hξv⟩ :
      ∃ ξ ∈ B, z 1 ξ = 0 ∧ z 2 ξ = 0 ∧ ξ ≠ principal ∧ χ ξ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hker : ∑ l ∈ B, χ l v * starRingEnd ℂ (χ l 1) = 0 := by
      have h := hK v hvP hv1 1 (one_mem _)
      rw [ite_eq_right (fun h' => hv1 (isConj_one_left.mp h'))] at h
      exact h
    have hintv : ∀ l, ∃ k : ℤ, χ l v = k := fun l =>
      character_integer_of_mul_self (basis.representation l).representation hvsq
    choose k hk using hintv
    have hker' : ∑ l ∈ B, k l * (deg l : ℤ) = 0 := by
      have h : ∑ l ∈ B, ((k l : ℂ) * (deg l : ℂ)) = 0 := by
        rw [← hker]
        apply Finset.sum_congr rfl
        intro l _
        rw [hk, hχ1, Complex.conj_natCast]
      exact_mod_cast h
    have hterm : ∀ l ∈ B, k l * (deg l : ℤ) =
        (deg p1 : ℤ) * (if z 1 l ≠ 0 ∨ z 2 l ≠ 0 then k l else 0) +
          (if l = principal then 1 else 0) := by
      intro l hl
      by_cases hE : z 1 l ≠ 0 ∨ z 2 l ≠ 0
      · have hlp : l ≠ principal := by
          rintro rfl
          rcases hE with h | h
          · exact h hprinc.1
          · exact h hprinc.2
        rw [ite_eq_left hE, ite_eq_right hlp, hsupp l hl hE, add_zero, mul_comm]
      · rw [ite_eq_right hE]
        push Not at hE
        by_cases hlp : l = principal
        · subst hlp
          have hkp : k l = 1 := by
            have h := hk l
            have h1 : χ l v = 1 := by
              change (basis.representation l).character v = 1
              rw [hprincipal]
              rfl
            rw [h1] at h
            exact_mod_cast h.symm
          rw [ite_eq_left rfl, hkp, hdeg_princ]
          norm_num
        · have hk0 : k l = 0 := by
            have h := hk l
            rw [hcon l hl hE.1 hE.2 hlp] at h
            exact_mod_cast h.symm
          rw [ite_eq_right hlp, hk0]
          ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq' B principal, ite_eq_left hprincB] at hker'
    set M := ∑ l ∈ B, (if z 1 l ≠ 0 ∨ z 2 l ≠ 0 then k l else 0)
    have hD2' : (2 : ℤ) ≤ deg p1 := by exact_mod_cast hD2
    rcases lt_trichotomy M 0 with hM | hM | hM
    · nlinarith
    · rw [hM] at hker'
      omega
    · nlinarith
  obtain ⟨t, ht⟩ := hcomp ξ hξ1 hξ2
  have htv : χ ξ v = t := ht ⟨v, hvP⟩ (fun h => hv1 (congrArg Subtype.val h))
  have ht0 : t ≠ 0 := htv ▸ hξv
  have heven : ∀ g : H, ¬ Odd (orderOf g) → χ ξ g = t := by
    intro g hg
    obtain ⟨a, hga, ha1, k, hak⟩ := exists_isPPart_two_ne_one g hg
    obtain ⟨d, -, hdP⟩ := exists_conj_mem_sylow_of_le P le_top (Subgroup.mem_top a)
      ⟨k, orderOf_dvd_iff_pow_eq_one.mp hak⟩
    have h1 : χ ξ g = χ ξ a := hconst ξ hξB g a hga ha1
    have h2 : χ ξ (d * a * d⁻¹) = χ ξ a := Representation.char_conj _ a d
    rw [h1, ← h2]
    apply ht ⟨d * a * d⁻¹, hdP⟩
    intro h
    exact ha1 (conj_eq_one_iff.mp (congrArg Subtype.val h))
  have hχx : χ ξ x = t := heven x (by rw [hx2]; decide)
  have hχy : χ ξ y = t := heven y (by rw [hy2]; decide)
  have hprod := irreducible_character_product_sum (basis.representation ξ) (basis.irreducible ξ)
    (conjClassFinset x) (conjClassFinset y) (conjClassFinset_invariant x)
    (conjClassFinset_invariant y) 1
  have hterm : ∀ a ∈ conjClassFinset x, ∀ b ∈ conjClassFinset y,
      (basis.representation ξ).character (a * b * 1) = t := by
    intro a ha b hb
    rw [mul_one]
    apply heven
    intro hodd
    simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hxy (ha.trans ((isConj_of_odd_orderOf_mul (mul_self_eq_one_of_isConj hxsq ha)
      (mul_self_eq_one_of_isConj hysq hb) hodd).trans hb.symm))
  rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => hterm a ha b hb)),
    character_conjClassFinset_sum, character_conjClassFinset_sum] at hprod
  simp only [Finset.sum_const, nsmul_eq_mul] at hprod
  have hA : ((conjClassFinset x).card : ℂ) ≠ 0 := by
    have hx : x ∈ conjClassFinset x := by
      simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact IsConj.refl x
    exact_mod_cast (Finset.card_pos.mpr ⟨x, hx⟩).ne'
  have hA' : ((conjClassFinset y).card : ℂ) ≠ 0 := by
    have hy : y ∈ conjClassFinset y := by
      simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact IsConj.refl y
    exact_mod_cast (Finset.card_pos.mpr ⟨y, hy⟩).ne'
  have hdegξ := irreducible_character_degree_ne_zero (basis.representation ξ) (basis.irreducible ξ)
  have hχx' : (basis.representation ξ).character x = t := hχx
  have hχy' : (basis.representation ξ).character y = t := hχy
  rw [hχx', hχy'] at hprod
  have htdeg : t = (basis.representation ξ).character 1 := by
    field_simp at hprod
    exact hprod.symm
  have hnontriv : ∃ g : H, (basis.representation ξ).representation g ≠ 1 := by
    by_contra hall
    push Not at hall
    have hconstχ : (basis.representation ξ).character = fun _ => (deg ξ : ℂ) := by
      funext g
      change LinearMap.trace ℂ _ ((basis.representation ξ).representation g) = _
      rw [hall g, LinearMap.trace_one]
    have h := blocksInnerProduct_basis basis ξ principal
    rw [ite_eq_right hξp, hconstχ, hprincipal] at h
    unfold BlocksInnerProduct at h
    simp only [Pi.one_apply, map_one, mul_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h
    rw [Nat.card_eq_fintype_card] at h
    have hcardH : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [← mul_assoc, inv_mul_cancel₀ hcardH, one_mul] at h
    exact (hdeg_pos ξ).ne' (by exact_mod_cast h)
  exact representation_involution_character_ne_degree_of_simple
    (basis.representation ξ).representation hnontriv x hx2 (hχx'.trans htdeg)

end Theorem

end CFSG.LyonsUnitaryFour
