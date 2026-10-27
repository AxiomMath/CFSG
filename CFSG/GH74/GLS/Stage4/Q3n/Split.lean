module

public import CFSG.GH74.GLS.Stage4.Q3n.Leaves
public import CFSG.GH74.GLS.Stage4.Q3n.Derived
public import CFSG.CharacterTheory.KleinFourBlocks.ThreeBlocks

public section

namespace CFSG.GH74.GLS.Stage4.Q3n

open CFSG CFSG.BrauerThirdMainTheorem.Helpers Subgroup CFSG.TwoRankLowerBound.Helpers
  CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.FreeSix

@[expose] def IV2_11_1_split : Prop :=
  ∀ (m : Ideal BlocksAlgInt), m.IsMaximal → (2 : BlocksAlgInt) ∈ m →
  ∀ (G : Type) [Group G] [Finite G] (U : Subgroup G),
    Nat.card U = 4 → (∀ x ∈ U, x * x = 1) →
    Function.Surjective U.normalizerMonoidHom →
    (∃ R : Subgroup G, R ≤ Subgroup.centralizer (U : Set G) ∧ U ⊓ R = ⊥ ∧
      ∀ c ∈ Subgroup.centralizer (U : Set G), ∃ u ∈ U, ∃ r ∈ R, c = u * r) →
    ∀ ω ∈ BlocksIrr ↥(Subgroup.centralizer (U : Set G)),
      (∀ u : ↥(Subgroup.centralizer (U : Set G)), (u : G) ∈ U → ω u = ω 1) →
      (∃ d : ℕ, ω 1 = d ∧
        2 ^ ((Nat.card ↥(Subgroup.centralizer (U : Set G))).factorization 2 - 2) ∣ d) →
      (∀ g ∈ Subgroup.normalizer U,
        (∀ c c' : ↥(Subgroup.centralizer (U : Set G)), (c' : G) = g * c * g⁻¹ → ω c' = ω c) →
        g ∈ Subgroup.centralizer (U : Set G)) →
      ∀ z ∈ U, z ≠ 1 → KleinFourConclusion m G U ω z

theorem isKleinFour_of_card_exp {G : Type} [Group G] {U : Subgroup G} (hcard : Nat.card U = 4)
    (hexp : ∀ x ∈ U, x * x = 1) : IsKleinFour ↥U := by
  refine ⟨hcard, ?_⟩
  have hdvd : Monoid.exponent ↥U ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      rw [pow_two]
      exact Subtype.ext (hexp x x.2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exfalso
    have hsub : Subsingleton ↥U := Monoid.exp_eq_one_iff.mp h1
    have h := Nat.card_unique (α := ↥U)
    rw [hcard] at h
    omega
  · exact h1

@[expose] def KleinFourConclusionAt (m : Ideal BlocksAlgInt) (G : Type) [Group G] [Finite G]
    (U : Subgroup G) (ω : ↥(Subgroup.centralizer (U : Set G)) → ℂ) (H : Subgroup G) : Prop :=
  ∃ (B : Set (G → ℂ)) (b : Fin 3 → Set (↥H → ℂ)) (f : ℕ) (fb : Fin 3 → ℕ),
    BlocksIsBlock m G B ∧ (∀ χ ∈ B, blockDefect 2 m χ U) ∧ (∀ χ ∈ B, χ 1 = (f : ℂ)) ∧
    (∀ i, BlocksIsBlock m ↥H (b i) ∧
      (∀ ψ ∈ b i, blockDefect 2 m ψ (U.subgroupOf H)) ∧
      ∀ ψ ∈ b i, ψ 1 = (fb i : ℂ)) ∧
    (Nat.card G : ℂ) * (Nat.card ↥(Subgroup.centralizer (U : Set G)) : ℂ) ^ 2 *
        ((fb 0 : ℂ) * fb 1 * fb 2) =
      (Nat.card ↥H : ℂ) ^ 3 * ω 1 ^ 2 * f

theorem kleinFourConclusion_iff_at (m : Ideal BlocksAlgInt) (G : Type) [Group G] [Finite G]
    (U : Subgroup G) (ω : ↥(Subgroup.centralizer (U : Set G)) → ℂ) (z : G) :
    KleinFourConclusion m G U ω z ↔
      KleinFourConclusionAt m G U ω (Subgroup.centralizer ({z} : Set G)) := Iff.rfl

theorem mem_blockOf_iff_label {K : Type} [Group K] [Fintype K]
    (b : FiniteIrreducibleCharacterBasis K) (m : Ideal BlocksAlgInt) [m.IsMaximal]
    (l : b.index) (χ : K → ℂ) :
    χ ∈ BlocksBlockOf m K (b.representation l).character ↔
      ∃ l' ∈ coefficientBlock b (localizedComplexIntegerRing m) l,
        (b.representation l').character = χ := by
  have h := Set.ext_iff.mp (CFSG.BlockBasics.coefficientBlock_image b m l) χ
  constructor
  · intro hχ
    obtain ⟨l', hl', hl'χ⟩ := h.mpr hχ
    exact ⟨l', hl', hl'χ⟩
  · rintro ⟨l', hl', hχ⟩
    exact h.mp ⟨l', hl', hχ⟩

theorem character_one_eq_finrank' {K : Type} [Group K] [Fintype K]
    (b : FiniteIrreducibleCharacterBasis K) (l : b.index) :
    (b.representation l).character 1 =
      ((Module.finrank ℂ (b.representation l).vector : ℕ) : ℂ) := by
  rw [FiniteComplexRepresentation.character, Representation.char_one]

theorem klein_conclusion_of_blocks {G : Type} [Group G] [Fintype G] (m : Ideal BlocksAlgInt)
    [m.IsMaximal] (U : Subgroup G) (ω : ↥(Subgroup.centralizer (U : Set G)) → ℂ)
    (H : Subgroup G) [Fintype ↥H] (basis : FiniteIrreducibleCharacterBasis G)
    (basisH : FiniteIrreducibleCharacterBasis ↥H) (Bl : basis.index) (bl : Fin 3 → basisH.index)
    (h : ℕ) (fd : Fin 3 → ℕ) (w : ℕ)
    (hBdef : coefficientBlockDefect basis m 2 Bl U)
    (hbdef : ∀ j, coefficientBlockDefect basisH m 2 (bl j) (U.subgroupOf H))
    (hBdeg : ∀ l ∈ coefficientBlock basis (localizedComplexIntegerRing m) Bl,
      Module.finrank ℂ (basis.representation l).vector = h)
    (hbdeg : ∀ j, ∀ l ∈ coefficientBlock basisH (localizedComplexIntegerRing m) (bl j),
      Module.finrank ℂ (basisH.representation l).vector = fd j)
    (hform : Nat.card G * Nat.card ↥(Subgroup.centralizer (U : Set G)) ^ 2 *
      (fd 0 * fd 1 * fd 2) = Nat.card ↥H ^ 3 * w ^ 2 * h) (hω1 : ω 1 = w) :
    KleinFourConclusionAt m G U ω H := by
  refine ⟨BlocksBlockOf m G (basis.representation Bl).character,
    fun i => BlocksBlockOf m ↥H (basisH.representation (bl i)).character, h, fd,
    ⟨_, CFSG.BlockBasics.basis_character_mem_irr basis Bl, rfl⟩, ?_, ?_,
    fun i => ⟨⟨_, CFSG.BlockBasics.basis_character_mem_irr basisH (bl i), rfl⟩, ?_, ?_⟩, ?_⟩
  · intro χ hχ
    obtain ⟨l', hl', rfl⟩ := (mem_blockOf_iff_label basis m Bl χ).mp hχ
    exact (CFSG.BlockBasics.coefficientBlockDefect_iff basis m 2 l' U).mp
      ((coefficientBlockDefect_iff_of_same_block basis m 2
        ((coefficientBlock_mem_iff basis _ Bl l').mp hl') U).mp hBdef)
  · intro χ hχ
    obtain ⟨l', hl', rfl⟩ := (mem_blockOf_iff_label basis m Bl χ).mp hχ
    rw [character_one_eq_finrank', hBdeg l' hl']
  · intro ψ hψ
    obtain ⟨l', hl', rfl⟩ := (mem_blockOf_iff_label basisH m (bl i) ψ).mp hψ
    exact (CFSG.BlockBasics.coefficientBlockDefect_iff basisH m 2 l' _).mp
      ((coefficientBlockDefect_iff_of_same_block basisH m 2
        ((coefficientBlock_mem_iff basisH _ (bl i) l').mp hl') _).mp (hbdef i))
  · intro ψ hψ
    obtain ⟨l', hl', rfl⟩ := (mem_blockOf_iff_label basisH m (bl i) ψ).mp hψ
    rw [character_one_eq_finrank', hbdeg i l' hl']
  · rw [hω1]
    have := congrArg (Nat.cast : ℕ → ℂ) hform
    push_cast at this
    linear_combination this

theorem irr_mul_of_ker {D : Type*} [Group D] {ω : D → ℂ} (hω : ω ∈ BlocksIrr D)
    (H : Subgroup D) [Finite H] (hH : ∀ h ∈ H, ω h = ω 1) (h : D) (hh : h ∈ H) (x : D) :
    ω (h * x) = ω x := by
  obtain ⟨W, _, _, _, ρ, -, rfl⟩ := hω
  have hker := CFSG.LyonsUnitaryFour.le_ker_of_character_eq_degree ρ H hH
  have h1 : ρ h = 1 := MonoidHom.mem_ker.mp (hker hh)
  show ρ.character (h * x) = ρ.character x
  simp [Representation.character, map_mul, h1]

theorem iv2_11_1_split_proved : IV2_11_1_split := by
  intro m hm h2 G _ _ U hcard hexp hAut hR ω hω hωker hdeg hinert z hzU hz1
  classical
  obtain ⟨R, hRC, hUR, hdec⟩ := hR
  let _ : Fintype G := Fintype.ofFinite G
  have hV : IsKleinFour U := isKleinFour_of_card_exp hcard hexp
  have _ : m.IsMaximal := hm
  have _ : CharP (ComplexAlgebraicIntegers ⧸ m) 2 :=
    (CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two).2 m hm h2
  obtain ⟨s, hsU, hs1, hsz⟩ : ∃ s ∈ U, s ≠ 1 ∧ s ≠ z := by
    by_contra hcon
    push Not at hcon
    have hsub : (U : Set G) ⊆ {1, z} := by
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1]
      · simp [hcon x hx hx1]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2' : ({1, z} : Set G).ncard ≤ 2 := by
      have := Set.ncard_insert_le (1 : G) ({z} : Set G)
      rw [Set.ncard_singleton] at this
      exact this
    have h3 : Nat.card U = (U : Set G).ncard := Nat.card_coe_set_eq (U : Set G)
    omega
  have hsC : s ∈ cT z :=
    DihedralAssociates.mem_centralizer_zpowers_of_commute (comm hV s hsU z hzU)
  have hcommUR : ∀ x ∈ U, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hRC hy) x hx
  have hUR_sup : U ⊔ R = Subgroup.centralizer (U : Set G) := by
    apply le_antisymm
    · exact sup_le (le_dV hV) hRC
    · intro c hc
      obtain ⟨u, hu, r, hr, rfl⟩ := hdec c hc
      exact Subgroup.mul_mem_sup hu hr
  have hcardD : Nat.card ↥(Subgroup.centralizer (U : Set G)) = 4 * Nat.card R := by
    rw [← hUR_sup, card_sup_of_comm_inf_bot hcommUR hUR, hcard]
  obtain ⟨basisD⟩ := finiteIrreducibleCharacterBasis_exists
    (G := ↥(Subgroup.centralizer (U : Set G)))
  let f₀ : G → ℂ := fun g =>
    if hg : g ∈ Subgroup.centralizer (U : Set G) then ω ⟨g, hg⟩ else 0
  have hf₀D : ∀ x : ↥(Subgroup.centralizer (U : Set G)), f₀ (x : G) = ω x := fun x => by
    simp [f₀]
  have hker : ∀ u ∈ U.subgroupOf (Subgroup.centralizer (U : Set G)), ω u = ω 1 :=
    fun u hu => hωker u hu
  have hdata : CFSG.KleinFourBlocks.FreeBlockData U f₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g hg
      simp [f₀, hg]
    · intro d hd g
      by_cases hg : g ∈ Subgroup.centralizer (U : Set G)
      · have hg' : d⁻¹ * g * d ∈ Subgroup.centralizer (U : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hd) hg) hd
        have h1 := irr_conj hω ⟨g, hg⟩ ⟨d⁻¹, Subgroup.inv_mem _ hd⟩
        simp only [f₀, hg, hg', ↓reduceDIte]
        convert h1 using 2
        apply Subtype.ext
        simp
      · have hg' : d⁻¹ * g * d ∉ Subgroup.centralizer (U : Set G) := by
          intro h
          apply hg
          have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hd h) (Subgroup.inv_mem _ hd)
          simpa [mul_assoc] using this
        simp [f₀, hg, hg']
    · intro v hv g
      have hvD : v ∈ Subgroup.centralizer (U : Set G) :=
        le_dV hV hv
      by_cases hg : g ∈ Subgroup.centralizer (U : Set G)
      · have hvg : v * g ∈ Subgroup.centralizer (U : Set G) := Subgroup.mul_mem _ hvD hg
        simp only [f₀, hg, hvg, ↓reduceDIte]
        exact irr_mul_of_ker hω (U.subgroupOf (Subgroup.centralizer (U : Set G))) hker
          ⟨v, hvD⟩ hv ⟨g, hg⟩
      · have hvg : v * g ∉ Subgroup.centralizer (U : Set G) := by
          intro h
          apply hg
          have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hvD) h
          simpa using this
        simp [f₀, hg, hvg]
    · intro g hg hfix
      have hginv : g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
        apply hinert g⁻¹ (Subgroup.inv_mem _ hg)
        intro c c' hc'
        have hc'' : (c' : G) = g⁻¹ * (c : G) * g := by rw [hc', inv_inv]
        have h1 := hfix (c : G)
        rw [← hc'', hf₀D c', hf₀D c] at h1
        exact h1
      simpa using Subgroup.inv_mem _ hginv
  obtain ⟨n₀, hn₀c⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basisD hω
  have hn₀ : CFSG.KleinFourBlocks.AffordsFun basisD (fun x => (x : G)) f₀ n₀ := fun x => by
    rw [congrFun hn₀c x]
    exact (hf₀D x).symm
  obtain ⟨d, hωd, hdvd⟩ := hdeg
  have hd0 : 0 < d := by
    have := irr_degree_ne_zero hω
    rw [hωd] at this
    exact Nat.pos_of_ne_zero (by exact_mod_cast this)
  have hf₀1 : f₀ 1 = d := (hf₀D 1).trans hωd
  have hwdeg : 2 ^ (Nat.card R).factorization 2 ∣ d := by
    have hR0 : Nat.card R ≠ 0 := Nat.card_pos.ne'
    have h4 : (4 : ℕ).factorization 2 = 2 := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    have hfac : (Nat.card ↥(Subgroup.centralizer (U : Set G))).factorization 2 =
        2 + (Nat.card R).factorization 2 := by
      rw [hcardD, Nat.factorization_mul (by norm_num) hR0, Finsupp.add_apply, h4]
    rw [hfac, Nat.add_sub_cancel_left] at hdvd
    exact hdvd
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨basisC⟩ := finiteIrreducibleCharacterBasis_exists (G := cT z)
  obtain ⟨Bl, bl, h, fd, hh, hfd, hBdef, hbdef, hBdeg, hbdeg, hform⟩ :=
    CFSG.KleinFourBlocks.three_blocks_formula basis m hV ⟨s, hsC⟩ hzU hsU hz1 hs1 hsz basisC
      hAut hRC hUR hdec hdata basisD hn₀ hd0 hf₀1 hwdeg
  have key : KleinFourConclusionAt m G U ω (cT z) :=
    klein_conclusion_of_blocks m U ω (cT z) basis basisC Bl bl h fd d hBdef hbdef hBdeg hbdeg
      hform hωd
  have heq : cT z = Subgroup.centralizer ({z} : Set G) := by
    show Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) = _
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [kleinFourConclusion_iff_at]
  rw [heq] at key
  exact key

end CFSG.GH74.GLS.Stage4.Q3n
