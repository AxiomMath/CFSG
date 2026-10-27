module

public import CFSG.CharacterTheory.KleinFourBlocks.Fibre
public import CFSG.CharacterTheory.KleinFourBlocks.FibreLocal
public import CFSG.CharacterTheory.KleinFourBlocks.FibreSetup
public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneFixedCoreBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneFixedCoreSupport

public section

open CFSG CFSG.TwoRankLowerBound.Helpers CFSG.BrauerThirdMainTheorem.Helpers
  CFSG.Wreathed CFSG.Wreathed.BlockOrbits CFSG.BlockBasics
  CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.KleinFourFiber
  CFSG.Semidihedral.Principal.FreeSix
  CFSG.Semidihedral.Principal.FieldFactorOneFixedCore

open scoped Classical

namespace CFSG.KleinFourBlocks

theorem free_block_hyps {G : Type} [Group G] [Fintype G] {V : Subgroup G} (hV : IsKleinFour V)
    {R : Subgroup G} (hRD : R ≤ dV V) (hVR : V ⊓ R = ⊥)
    (hDVR : ∀ x ∈ dV V, ∃ v ∈ V, ∃ r ∈ R, x = v * r)
    {f₀ : G → ℂ} (hdata : FreeBlockData V f₀)
    (basisD : FiniteIrreducibleCharacterBasis (dV V)) {n₀ : basisD.index}
    (hn₀ : AffordsFun basisD (fun x => (x : G)) f₀ n₀)
    {w : ℕ} (hf₀1 : f₀ 1 = w) (hwdeg : 2 ^ (Nat.card R).factorization 2 ∣ w)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    coefficientBlockDefect basisD ideal 2 n₀ (V.subgroupOf (dV V)) ∧
    (∀ ℓ : basisD.index,
      sameCoefficientBlock basisD (localizedComplexIntegerRing ideal) n₀ ℓ →
      (∀ (x x' : dV V) (v : G), v ∈ V → (x : G) = v * x' →
        (basisD.representation ℓ).character x = (basisD.representation ℓ).character x') →
      ∀ x, (basisD.representation ℓ).character x = (basisD.representation n₀).character x) := by
  classical
  have : IsKleinFour V := hV
  set VX : Subgroup (dV V) := V.subgroupOf (dV V) with hVX
  set RX : Subgroup (dV V) := R.subgroupOf (dV V) with hRX
  have hRXcard : Nat.card RX = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRD).toEquiv
  have hV2 : ∀ v ∈ VX, v * v = 1 := fun v hv => Subtype.ext (mul_self hV (show (v : G) ∈ V from hv))
  have hVab : ∀ a ∈ VX, ∀ b ∈ VX, a * b = b * a := fun a ha b hb =>
    Subtype.ext (comm hV _ (show (a : G) ∈ V from ha) _ (show (b : G) ∈ V from hb))
  have hcomm : ∀ v ∈ VX, ∀ r ∈ RX, v * r = r * v := fun v hv r hr =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp (hRD (show (r : G) ∈ R from hr)) (v : G)
      (show (v : G) ∈ V from hv))
  have hVR' : VX ⊓ RX = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    have hmem : (x : G) ∈ V ⊓ R := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hVR, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have hX : ∀ x : dV V, ∃ v ∈ VX, ∃ r ∈ RX, x = v * r := by
    intro x
    obtain ⟨v, hv, r, hr, hxvr⟩ := hDVR (x : G) x.2
    exact ⟨⟨v, le_dV hV hv⟩, hv, ⟨r, hRD hr⟩, hr, Subtype.ext hxvr⟩
  have hn₀V : ∀ (x x' v : dV V), v ∈ VX → x = v * x' → x' ∈ RX →
      (basisD.representation n₀).character x = (basisD.representation n₀).character x' := by
    intro x x' v hv hx _
    rw [hn₀ x, hn₀ x']
    have hxG : (x : G) = (v : G) * (x' : G) := congrArg Subtype.val hx
    show f₀ (x : G) = f₀ (x' : G)
    rw [hxG]
    exact hdata.transV _ hv _
  have hn₀deg : ∃ d : ℕ, (basisD.representation n₀).character 1 = d ∧
      2 ^ (Nat.card RX).factorization 2 ∣ d := by
    refine ⟨w, ?_, by rw [hRXcard]; exact hwdeg⟩
    rw [hn₀ 1]
    simpa using hf₀1
  obtain ⟨ha, -, -, hd⟩ := defect_zero_twist_block_and_class_functions basisD ideal VX RX hV2
    hVab hcomm hVR' hX n₀ hn₀V hn₀deg
  refine ⟨hd, ?_⟩
  intro ℓ hsame hVinv x
  have hℓ : ℓ ∈ coefficientBlock basisD (localizedComplexIntegerRing ideal) n₀ :=
    (coefficientBlock_mem_iff basisD (localizedComplexIntegerRing ideal) n₀ ℓ).mpr hsame
  obtain ⟨lam, hlam⟩ := (ha ℓ).mp hℓ
  obtain ⟨v, hv, r, hr, hxvr⟩ := hX x
  have h1 : (basisD.representation ℓ).character x = (basisD.representation ℓ).character r :=
    hVinv x r (v : G) hv (congrArg Subtype.val hxvr)
  have h2 : (basisD.representation ℓ).character r = (basisD.representation n₀).character r := by
    have := hlam r r 1 (by simp) hr
    simpa using this
  have h3 : (basisD.representation n₀).character x = (basisD.representation n₀).character r :=
    hn₀V x r v hv hxvr hr
  rw [h1, h2, h3]

theorem three_blocks_formula {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    {V : Subgroup G} (hV : IsKleinFour V) {t : G} (sC : cT t) (htV : t ∈ V)
    (hsV : (sC : G) ∈ V) (ht1 : t ≠ 1) (hs1 : (sC : G) ≠ 1) (hst : (sC : G) ≠ t)
    (basisC : FiniteIrreducibleCharacterBasis (cT t))
    (hAut : Function.Surjective V.normalizerMonoidHom)
    {R : Subgroup G} (hRD : R ≤ dV V) (hVR : V ⊓ R = ⊥)
    (hDVR : ∀ x ∈ dV V, ∃ v ∈ V, ∃ r ∈ R, x = v * r)
    {f₀ : G → ℂ} (hdata : FreeBlockData V f₀)
    (basisD : FiniteIrreducibleCharacterBasis (dV V)) {n₀ : basisD.index}
    (hn₀ : AffordsFun basisD (fun x => (x : G)) f₀ n₀)
    {w : ℕ} (hw : 0 < w) (hf₀1 : f₀ 1 = w) (hwdeg : 2 ^ (Nat.card R).factorization 2 ∣ w) :
    ∃ (Bl : basis.index) (bl : Fin 3 → basisC.index) (h : ℕ) (fd : Fin 3 → ℕ),
      0 < h ∧ (∀ j, 0 < fd j) ∧
      coefficientBlockDefect basis ideal 2 Bl V ∧
      (∀ j, coefficientBlockDefect basisC ideal 2 (bl j) (vInC V t)) ∧
      (∀ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) Bl,
        Module.finrank ℂ (basis.representation l).vector = h) ∧
      (∀ j, ∀ l ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) (bl j),
        Module.finrank ℂ (basisC.representation l).vector = fd j) ∧
      Nat.card G * Nat.card (dV V) ^ 2 * (fd 0 * fd 1 * fd 2) =
        Nat.card (cT t) ^ 3 * w ^ 2 * h := by
  classical
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq, mul_self hV htV]) ht1
  have hs2G : orderOf (sC : G) = 2 :=
    orderOf_eq_prime (by rw [sq, mul_self hV hsV]) hs1
  have hs2 : orderOf sC = 2 := by rw [← hs2G]; exact (Subgroup.orderOf_coe sC).symm
  have hVC : V ≤ cT t := le_cT hV htV
  have hst' : sC ≠ ⟨t, element_mem_centralizer_zpowers t⟩ := fun h => hst (congrArg Subtype.val h)
  have hcl := closure_pair_cT_eq_vInC hV sC htV hsV ht1 hs1 hst
  have hDmem : ∀ x : G, t * x = x * t → (sC : G) * x = x * (sC : G) → x ∈ dV V :=
    fun x hxt hxs => mem_dV_of_commute_pair hV htV hsV ht1 hs1 hst hxt hxs
  obtain ⟨y, hyC, hyM, hys, hK⟩ := exists_y_splitting hV hAut htV hsV ht1 hs1 hst
  have hfour := hfour_of_hAut hV hAut htV ht1
  have hsG : IsConj t (sC : G) := isConj_of_mem_V hV hAut htV hsV ht1 hs1
  have htrans : ∀ u ∈ V, u ≠ 1 → IsConj t u := fun u hu hu1 =>
    isConj_of_mem_V hV hAut htV hu ht1 hu1
  have hsJ : (sC : G) ∉ Subgroup.zpowers t := by
    intro h
    rcases eq_one_or_eq_of_mem_zpowers_involution ht2 h with h' | h'
    · exact hs1 h'
    · exact hst h'
  obtain ⟨basisM⟩ := finiteIrreducibleCharacterBasis_exists (G := mV V)
  obtain ⟨basisMD⟩ := finiteIrreducibleCharacterBasis_exists (G := dInM V)
  obtain ⟨basisK⟩ := finiteIrreducibleCharacterBasis_exists (G := kInC V t)
  obtain ⟨basisKD⟩ := finiteIrreducibleCharacterBasis_exists (G := dInK V t)
  obtain ⟨basisCD⟩ := finiteIrreducibleCharacterBasis_exists (G := dInC V t)
  obtain ⟨hdef₀, hblock₀⟩ := free_block_hyps hV hRD hVR hDVR hdata basisD hn₀ hf₀1 hwdeg ideal
  obtain ⟨-, fs, hfsΩ, hΩj2, -, -, A, Aj, B, b, -, -, -, -, -, -, hBdef, hbdef, hdist, hfib, -,
      hslevel⟩ :=
    free_orbit_defect_four_block basis ideal V hV t htV ht1 hAut hfour f₀ hdata.supp hdata.cls
      hdata.transV hdata.stab basisM basisMD basisK basisKD basisC basisCD basisD n₀ hn₀ hdef₀
      hblock₀
  have hs : IsPGroup 2 (Subgroup.zpowers sC) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hs2, pow_one]
  obtain ⟨hcent, hslev⟩ := hslevel sC hsV hsJ
  obtain ⟨basisCs⟩ := finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer
    ((Subgroup.zpowers sC : Subgroup (cT t)) : Set (cT t)))
  obtain ⟨-, hsfib⟩ := hslev hs basisCs
  have hG1 : ∀ j : Fin 3, ∃ (θ : Fin 4 → basisC.index) (f : ℕ), Function.Injective θ ∧
      coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j) =
        Finset.univ.image θ ∧
      0 < f ∧ (∀ i, Module.finrank ℂ (basisC.representation (θ i)).vector = f) ∧
      ((basisC.representation (θ 0)).character ⟨t, element_mem_centralizer_zpowers t⟩ = f ∧
        (basisC.representation (θ 1)).character ⟨t, element_mem_centralizer_zpowers t⟩ = f ∧
        (basisC.representation (θ 2)).character ⟨t, element_mem_centralizer_zpowers t⟩ =
          -(f : ℂ) ∧
        (basisC.representation (θ 3)).character ⟨t, element_mem_centralizer_zpowers t⟩ =
          -(f : ℂ)) ∧
      ((basisC.representation (θ 0)).character sC = 2 * (w : ℂ) ∧
        (basisC.representation (θ 1)).character sC = -(2 * (w : ℂ)) ∧
        (basisC.representation (θ 2)).character sC = 0 ∧
        (basisC.representation (θ 3)).character sC = 0) ∧
      (∀ x, x ∉ involutionLocalSection t →
        ((basisC.representation (θ 0)).character + (basisC.representation (θ 1)).character -
          (basisC.representation (θ 2)).character - (basisC.representation (θ 3)).character) x =
            0) ∧
      coefficientCharacterSpace basisC
          (coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j)) ⊓
          sectionSupported (involutionLocalSection t) =
        Submodule.span ℂ {(basisC.representation (θ 0)).character +
          (basisC.representation (θ 1)).character - (basisC.representation (θ 2)).character -
            (basisC.representation (θ 3)).character} := fun j =>
    block_four_characters_gen sC htV hsV hs2 ht2 hst' hVC hcl hDmem hRD hVR hDVR hyC hyM hys hK
      hdata basisD hn₀ w hw hf₀1 hwdeg ideal basisC (b j) (hbdef j) (hfsΩ j) (hΩj2 j) hs hcent
      basisCs (hsfib j)
  choose θ fd hθinj hθb hfd hθdeg hθt hθs hαsupp hαspan using hG1
  have hbD : ∀ j, coefficientBlockDefect basisC ideal 2 (θ j 0)
      (Subgroup.closure ({⟨t, element_mem_centralizer_zpowers t⟩, sC} : Set (cT t))) := by
    intro j
    rw [hcl]
    have hmem : θ j 0 ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j) := by
      rw [hθb j]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ 0)
    have hsame := (coefficientBlock_mem_iff basisC (localizedComplexIntegerRing ideal) (b j)
      (θ j 0)).mp hmem
    exact (coefficientBlockDefect_iff_of_same_block basisC ideal 2 hsame _).mp (hbdef j)
  have hbinj : Function.Injective fun j =>
      coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j) := by
    intro j k hjk
    by_contra hne
    exact hdist j k hne hjk
  obtain ⟨-, Φ, h, hΦinj, hΦb, hh, hΦdeg, -, -, -, -, hcard, -⟩ :=
    defect_klein_four_three_local_blocks_exact_order_gen basis ideal t ht2
      (isPGroup_zpowers hV htV) basisC sC hs2 hst hsG ⟨y, hyC⟩ (Subtype.ext hys) B V hV
      htrans hBdef
      (fun j => coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j)) hbinj hfib θ
      hθinj hθb hbD fd hfd w hw hθdeg hθt hθs hαsupp hαspan
  refine ⟨B, b, h, fd, hh, hfd, hBdef, hbdef, ?_, ?_, ?_⟩
  · intro l hl
    rw [hΦb] at hl
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hl
    exact hΦdeg i
  · intro j l hl
    rw [hθb j] at hl
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hl
    exact hθdeg j i
  ·
    have hd : Nat.card (Subgroup.centralizer ({sC} : Set (cT t))) = Nat.card (dV V) :=
      card_centralizer_singleton_eq_card_dV hV sC htV hsV ht1 hs1 hst
    rw [hd] at hcard
    have hf0 : (0 : ℚ) < fd 0 := by exact_mod_cast hfd 0
    have hf1 : (0 : ℚ) < fd 1 := by exact_mod_cast hfd 1
    have hf2 : (0 : ℚ) < fd 2 := by exact_mod_cast hfd 2
    have hdpos : (0 : ℚ) < Nat.card (dV V) := by exact_mod_cast Nat.card_pos
    have hq : (Nat.card G : ℚ) * (Nat.card (dV V) : ℚ) ^ 2 * (fd 0 * fd 1 * fd 2) =
        (Nat.card (cT t) : ℚ) ^ 3 * w ^ 2 * h := by
      rw [hcard]
      field_simp
    exact_mod_cast hq

end CFSG.KleinFourBlocks
