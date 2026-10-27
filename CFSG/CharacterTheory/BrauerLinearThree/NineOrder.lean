module

public import CFSG.CharacterTheory.BrauerLinearThree.NineBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.DefectKleinFourExactOrder
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFour

public section

open scoped Classical

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Semidihedral.Principal.FreeSix

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include hZ hZodd h2 hJ in
theorem cube_dvd_card_of_centralizer_le [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    {z : G} (hzC : z ∈ centerSub φ) (hzodd : Odd (orderOf z))
    (hz : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer {J}) :
    Nat.card F ^ 3 ∣ Nat.card G := by
  let : Fintype G := Fintype.ofFinite G
  have : Fact p.Prime := ⟨hp⟩
  have hV := isKleinFour_fourV φ hZ h2 hJ
  have htV := J_mem_fourV φ
  have ht1 : J ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hJ
    exact absurd hJ (by norm_num)
  have hED := oddTorus_le_centralizer_fourV φ
  have hVE := fourV_inf_oddTorus φ hZ hZodd h2 hJ hq
  have hDVE : ∀ x ∈ dV (fourV φ), ∃ v ∈ fourV φ, ∃ e ∈ oddTorus φ, x = v * e :=
    fun x hx => exists_mul_of_mem_centralizer_fourV φ hZ hZodd h2 hJ hq hx
  have hEodd := odd_card_oddTorus φ h2 hq
  have hAut := normalizerMonoidHom_fourV_surjective φ hZ hZodd h2 hJ hnonab
  have hfour : ∀ U : Subgroup G, IsKleinFour U → J ∈ U → U ≤ cT J →
      ∃ c ∈ cT J, U.map (MulAut.conj c).toMonoidHom = fourV φ :=
    fun U hU hJU hUC => exists_conj_fourV φ hZ hZodd h2 hJ U hU hJU hUC
  obtain ⟨ι, hι⟩ := exists_injective_hom_units_complex Fˣ
  have hωV := torusCharacter_eq_one_of_mem_fourV φ hZ hZodd h2 hJ ι
  have hωstab : ∀ m ∈ mV (fourV φ), (∀ x y : dV (fourV φ), (y : G) = m⁻¹ * x * m →
      torusCharacter φ hZ hZodd h2 ι y = torusCharacter φ hZ hZodd h2 ι x) →
        m ∈ dV (fourV φ) :=
    fun m hm hst => torusCharacter_stabilizer φ hZ hZodd h2 hJ hq hq7 ι hι hzC hzodd hz hm hst
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨basisM⟩ := finiteIrreducibleCharacterBasis_exists (G := mV (fourV φ))
  obtain ⟨basisMD⟩ := finiteIrreducibleCharacterBasis_exists (G := dInM (fourV φ))
  obtain ⟨basisEM⟩ := finiteIrreducibleCharacterBasis_exists (G := eInM (fourV φ) (oddTorus φ))
  obtain ⟨basisC⟩ := finiteIrreducibleCharacterBasis_exists (G := cT J)
  obtain ⟨basisK⟩ := finiteIrreducibleCharacterBasis_exists (G := kInC (fourV φ) J)
  obtain ⟨basisKD⟩ := finiteIrreducibleCharacterBasis_exists (G := dInK (fourV φ) J)
  obtain ⟨basisCD⟩ := finiteIrreducibleCharacterBasis_exists (G := dInC (fourV φ) J)
  obtain ⟨⟨ideal, hmax, h2mem⟩, hchar⟩ :=
    CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax h2mem
  obtain ⟨-, -, -, -, -, -, μs, hμsΩ, hΩj2, -, -, A, Aj, B, b, -, -, -, -, -, -, hBdef, hbdef,
      hbinj, hfiber, -, hscl, -⟩ :=
    free_six_character_normalizer_orbit_defect_four_block basis ideal (fourV φ) hV J htV ht1
      (oddTorus φ) hED hVE hDVE hEodd hAut hfour (torusCharacter φ hZ hZodd h2 ι) hωV hωstab
      basisM basisMD basisEM basisC basisK basisKD basisCD
  have hs2 : orderOf (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) = 2 := by
    rw [Subgroup.orderOf_mk]; exact orderOf_invJ₁ φ hZ h2
  have hst : ((⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : G) ≠ J :=
    fun h => J_ne_invJ₁ φ hZ h2 h.symm
  have hs : IsPGroup 2 (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hs2, pow_one]
  have hsV : ((⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : G) ∈ fourV φ := invJ₁_mem_fourV φ
  have hsJ : ((⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : G) ∉ Subgroup.zpowers J := by
    intro h
    rcases eq_one_or_eq_of_mem_zpowers hJ h with h' | h'
    · have := orderOf_invJ₁ φ hZ h2
      change invJ₁ φ = 1 at h'
      rw [h', orderOf_one] at this
      exact absurd this (by norm_num)
    · exact hst h'
  obtain ⟨-, hsfib⟩ := hscl ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ hsV hsJ
  obtain ⟨basisCs⟩ := finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer
    (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : Set (cT J)))
  obtain ⟨-, hfib⟩ := hsfib hs basisCs
  have hblock : ∀ j : Fin 3, ∃ (θ : Fin 4 → basisC.index) (fj : ℕ), Function.Injective θ ∧
      coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j) =
        Finset.univ.image θ ∧
      0 < fj ∧ (∀ i, Module.finrank ℂ (basisC.representation (θ i)).vector = fj) ∧
      ((basisC.representation (θ 0)).character
          ⟨J, element_mem_centralizer_zpowers J⟩ = fj ∧
        (basisC.representation (θ 1)).character
          ⟨J, element_mem_centralizer_zpowers J⟩ = fj ∧
        (basisC.representation (θ 2)).character
          ⟨J, element_mem_centralizer_zpowers J⟩ = -(fj : ℂ) ∧
        (basisC.representation (θ 3)).character
          ⟨J, element_mem_centralizer_zpowers J⟩ = -(fj : ℂ)) ∧
      ((basisC.representation (θ 0)).character ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ = 2 ∧
        (basisC.representation (θ 1)).character ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ = -2 ∧
        (basisC.representation (θ 2)).character ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ = 0 ∧
        (basisC.representation (θ 3)).character ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ = 0) ∧
      (∀ x, x ∉ involutionLocalSection J →
        ((basisC.representation (θ 0)).character + (basisC.representation (θ 1)).character -
          (basisC.representation (θ 2)).character - (basisC.representation (θ 3)).character) x =
            0) ∧
      coefficientCharacterSpace basisC
          (coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j)) ⊓
          sectionSupported (involutionLocalSection J) =
        Submodule.span ℂ {(basisC.representation (θ 0)).character +
          (basisC.representation (θ 1)).character - (basisC.representation (θ 2)).character -
            (basisC.representation (θ 3)).character} := by
    intro j
    obtain ⟨ν, hν⟩ := exists_inflation_of_mem_linearOrbit φ hZ hZodd h2 hJ hq
      (torusCharacter φ hZ hZodd h2 ι) hωV (hμsΩ j)
    exact exists_block_four_characters φ hZ hZodd h2 hJ hq ideal basisC (b j) (hbdef j) (μs j)
      ν hν (hΩj2 j) hs basisCs (hfib j)
  choose θ fd hθinj hθb hfd hθdeg hθt hθs hαsupp hαspan using hblock
  have hpf : ∀ j, ¬ p ∣ fd j := by
    intro j h
    have hmem : θ j 0 ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j) := by
      rw [hθb j]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ 0)
    apply not_dvd_finrank_of_defect_fourV φ hZ hZodd h2 hJ hq p f hp hf hF ideal basisC (b j)
      (hbdef j) (θ j 0) hmem
    rw [hθdeg j 0]
    exact h
  have hpf3 : ¬ p ∣ fd 0 * fd 1 * fd 2 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
    · rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
      · exact hpf 0 h''
      · exact hpf 1 h''
    · exact hpf 2 h'
  have hbinj' : Function.Injective fun j =>
      coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j) := by
    intro j k hjk
    by_contra hne
    exact hbinj j k hne hjk
  obtain ⟨-, Φ, hh, -, -, -, -, -, -, -, -, -, hval⟩ :=
    defect_klein_four_three_local_blocks_exact_nonprincipal_order basis ideal
      (isConj_of_involutions φ hZ hZodd h2 hJ hnonab) J hJ (isPGroup_zpowers hV htV) basisC
      ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ hs2 hst (isConj_J_or_invJ₁ φ hZ hZodd h2 hJ) B (fourV φ) hV
      hBdef (fun j => coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j)) hbinj'
      hfiber θ hθinj hθb fd hfd hθdeg hθt hθs hαsupp hαspan
  have hineq := (hval p hp hpf3).2
  obtain ⟨hvc, hvd⟩ := padicValNat_centralizers φ hZ hZodd h2 p f hp hF
  have e1 : Nat.card (cT J) = Nat.card (Subgroup.centralizer ({J} : Set G)) := by
    rw [show cT J = Subgroup.centralizer ({J} : Set G) from centralizer_zpowers_eq J]
  rw [e1, hvc, card_centralizer_invJ₁_cT φ, hvd] at hineq
  have h3f : 3 * f ≤ padicValNat p (Nat.card G) := by omega
  rw [hF, ← pow_mul, mul_comm]
  exact (padicValNat_dvd_iff_le Nat.card_pos.ne').mpr h3f

omit [Finite F] in
include hZ hZodd in
theorem exists_odd_mem_centerSub (hq : Nat.card F % 4 = 3)
    (hu : Nat.card F - 1 ≠ 2 * Nat.card Z) :
    ∃ z ∈ centerSub φ, z ≠ 1 ∧ Odd (orderOf z) := by
  obtain ⟨u, hu', hcard⟩ := card_centerSub_eq_two_mul_odd φ hZ hZodd hq
  have hm : Nat.card (centerSub φ) * Nat.card Z = Nat.card F - 1 := card_scalarImage φ hZ
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hu
    rw [← hm, hcard]
  have hfin : Finite (centerSub φ) := Nat.finite_of_card_ne_zero (by
    obtain ⟨k, hk⟩ := hu'
    rw [hcard]
    omega)
  obtain ⟨r, hr, hru⟩ := Nat.exists_prime_and_dvd hu1
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r (hcard ▸ hru.trans (Dvd.intro_left 2 rfl))
  have hrodd : Odd r := hu'.of_dvd_nat hru
  refine ⟨x, x.2, fun h => ?_, ?_⟩
  · have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact hr.one_lt.ne' hx.symm
  · rw [Subgroup.orderOf_coe, hx]
    exact hrodd

include hZ hZodd h2 hJ in
theorem cube_dvd_card_of_four_G [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (h4G : ∀ z ∈ centerSub φ, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer {J})
    (hu : Nat.card F - 1 ≠ 2 * Nat.card Z) :
    Nat.card F ^ 3 ∣ Nat.card G := by
  obtain ⟨z, hzC, hz1, hzodd⟩ := exists_odd_mem_centerSub φ hZ hZodd hq hu
  exact cube_dvd_card_of_centralizer_le φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hzC hzodd
    (h4G z hzC hz1)

end CFSG.BrauerLinearThree
