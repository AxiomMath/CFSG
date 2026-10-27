module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc7f
public import CFSG.HardMathSupport.Lang.D4Three.CharThreeData
public import CFSG.Quasithin.H13.NQCatLieCartanG2
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Sylow
public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeField
public import CFSG.RankThree.PartOne.KLC.D4OutCentral
public import CFSG.HardMathSupport.Lang.D4Three.BorelLayers

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7f

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three
open scoped Pointwise

section NormalForm

variable {K : Type} [Field K]

theorem pow_apply_monomial {G ι : Type*} [Group G] (ν : MulAut G) (π : Equiv.Perm ι)
    (f : ι → K) (σ : K ≃+* K) (adj : ι → K → G)
    (h1 : ∀ j c, ν (adj j c) = adj (π j) (f (π j) * σ c)) (n : ℕ) :
    ∀ i, ∃ m : K, ∀ c : K, (ν ^ n) (adj i c) = adj ((π ^ n) i) (m * (σ ^ n) c) := by
  induction n with
  | zero => exact fun i => ⟨1, fun c => by simp⟩
  | succ n ih =>
    intro i
    obtain ⟨m, hm⟩ := ih (π i)
    refine ⟨m * (σ ^ n) (f (π i)), fun c => ?_⟩
    rw [pow_succ, MulAut.mul_apply, h1, hm, pow_succ, Equiv.Perm.mul_apply, pow_succ]
    congr 1
    rw [map_mul, mul_assoc]
    rfl

theorem conj_mul_pow_eq {G : Type*} [Group G] (c : G) (β : MulAut G) (n : ℕ) :
    ∃ z : G, (MulAut.conj c * β) ^ n = MulAut.conj z * β ^ n := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨z * (β ^ n) c, ?_⟩
    rw [pow_succ, hz, pow_succ]
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]

theorem perm_pow_three_or_two_of_cartanD4 (π : Equiv.Perm (Fin Tag.D4.rank))
    (hπ : ∀ i j, Tag.D4.cartan (π i) (π j) = Tag.D4.cartan i j) : π ^ 3 = 1 ∨ π ^ 2 = 1 := by
  have key : ∀ π : Equiv.Perm (Fin 4),
      (∀ i j : Fin 4, (![![2, 0, -1, 0], ![0, 2, -1, 0], ![-1, -1, 2, -1], ![0, 0, -1, 2]] :
        Fin 4 → Fin 4 → ℤ) (π i) (π j) =
        (![![2, 0, -1, 0], ![0, 2, -1, 0], ![-1, -1, 2, -1], ![0, 0, -1, 2]] :
          Fin 4 → Fin 4 → ℤ) i j) → π ^ 3 = 1 ∨ π ^ 2 = 1 := by
    decide +kernel
  have hc : ∀ i j : Fin 4, Tag.D4.cartan i j =
      (![![2, 0, -1, 0], ![0, 2, -1, 0], ![-1, -1, 2, -1], ![0, 0, -1, 2]] :
        Fin 4 → Fin 4 → ℤ) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  exact key π (fun i j => by rw [← hc, ← hc]; exact hπ i j)

variable [Finite K]

theorem exists_pow_normal_form (α : MulAut (adjointGroup Tag.D4 K)) (k : ℕ)
    (hα : α ^ 3 ^ k = 1) :
    ∃ (c : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε < 3 ∧
      σ ^ 3 ^ k = 1 ∧ α = MulAut.conj c * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨c, β, hU, hV, rfl⟩ :=
    (exceptional_ordinary_Sylow_opposition Tag.D4 K (ringChar K) w₀ hw₀).2.2.2.2.2 α
  have hA : β ∈ unipotentPairAut Tag.D4 K := ⟨hU, hV⟩
  obtain ⟨π, hπ⟩ := exists_perm_map_simple hA
  have hcart := cartan_perm_eq_D4 (K := K) (fun i => (hπ i).1)
  obtain ⟨z, hz⟩ := conj_mul_pow_eq c β (3 ^ k)
  have hβk : β ^ 3 ^ k = MulAut.conj z⁻¹ := by
    have h1 : MulAut.conj z * β ^ 3 ^ k = 1 := hz.symm.trans hα
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_right h1
  have hβkA : β ^ 3 ^ k ∈ unipotentPairAut Tag.D4 K := pow_mem hA _
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag (hβk ▸ hβkA)
  have hπk : π ^ 3 ^ k = 1 := by
    refine perm_map_simple_unique (α := β ^ 3 ^ k) (π := π ^ 3 ^ k) (π' := 1)
      (fun i => map_simplePos_pow (fun j => (hπ j).1) (3 ^ k) i) (fun i => ?_)
    rw [hβk, hb, map_simplePosSubgroup_exactNormalAut b 1 0 i]
    rfl
  have hπ3 : π ^ 3 = 1 := by
    rcases perm_pow_three_or_two_of_cartanD4 π hcart with h | h
    · exact h
    · have hodd : Odd (3 ^ k) := Odd.pow (by decide)
      obtain ⟨m, hm⟩ := hodd
      have hπ1 : π = 1 := by
        have := hπk
        rw [hm, pow_succ, pow_mul, h, one_pow, one_mul] at this
        exact this
      rw [hπ1, one_pow]
  have hcases := perm_pow_of_cartanD4 π hcart hπ3
  have hex : ∃ ε : ℕ, ε < 3 ∧ π = d4Rho ^ ε := by
    rcases hcases with h | h | h
    · exact ⟨0, by norm_num, by rw [h]; rfl⟩
    · exact ⟨1, by norm_num, by rw [h]; exact (pow_one _).symm⟩
    · exact ⟨2, by norm_num, h⟩
  obtain ⟨ε, hε3, rfl⟩ := hex
  obtain ⟨a, σ, hβ⟩ := exists_normalAut_mul_graph (K := K) hπ
  have hσ : σ ^ 3 ^ k = 1 := by
    obtain ⟨m, hm⟩ := pow_apply_monomial (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)
      (d4Rho ^ ε) (fun j => (a j : K)) σ (adjX Tag.D4 K)
      (fun j c => normalGraph_apply_adjX a σ ε j c) (3 ^ k) ⟨0, by decide⟩
    have hm' : ∀ c : K, ((exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ^ 3 ^ k)
        (adjX Tag.D4 K ⟨0, by decide⟩ c) =
        adjX Tag.D4 K ⟨0, by decide⟩ ((b ⟨0, by decide⟩ : K) * c) := by
      intro c
      rw [← hβ, hβk, hb, exactNormalAut_adjX]
      rfl
    have hπ1 : ((d4Rho ^ ε) ^ 3 ^ k) ⟨0, by decide⟩ = ⟨0, by decide⟩ := by
      rw [hπk]
      rfl
    have hmc : ∀ c : K, m * (σ ^ 3 ^ k) c = (b ⟨0, by decide⟩ : K) * c := fun c => by
      have := (hm c).symm.trans (hm' c)
      rw [hπ1] at this
      exact adjX_injective _ this
    have hm1 : m = (b ⟨0, by decide⟩ : K) := by simpa using hmc 1
    refine RingEquiv.ext fun c => ?_
    have := hmc c
    rw [hm1] at this
    have hb0 : ((b ⟨0, by decide⟩ : Kˣ) : K) ≠ 0 := Units.ne_zero _
    exact mul_left_cancel₀ hb0 this
  exact ⟨c, a, σ, ε, hε3, hσ, by rw [hβ]⟩

end NormalForm

section Key

variable {K : Type} [Field K]

theorem IsGraded.mul {τ : Tag} {A B : Module.End K (RootModule τ K)} (hA : IsGraded A)
    (hB : IsGraded B) : IsGraded (A * B) :=
  (SupportedBy.mul (r := fun a b => a.weight = b.weight) (s := fun a b => a.weight = b.weight)
    hA hB).mono fun _ _ ⟨_, h₁, h₂⟩ => h₁.trans h₂

theorem height_permLattice' {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    height (permLattice π v) = height v := by
  unfold height permLattice
  exact Equiv.sum_comp π.symm v

theorem d4P_pow_hVec (n : ℕ) (j : Fin Tag.D4.rank) :
    ((d4P K ^ n : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) (hVec Tag.D4 K j) =
      hVec Tag.D4 K ((d4Rho ^ n) j) :=
  diagramMap_pow_hVec TwistTag.D4 K n j

theorem d4P_pow_rootVec
    (n : ℕ) {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α) :
    ((d4P K ^ n : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) (rootVec Tag.D4 K α) =
      rootVec Tag.D4 K (permLattice (d4Rho ^ n) α) :=
  diagramMap_pow_rootVec TwistTag.D4 K n α

theorem isGraded_d4P_pow
    (n : ℕ) :
    IsGraded (((d4P K ^ n : ModGL Tag.D4 K)) : Module.End K (RootModule Tag.D4 K)) := by
  intro a b hab
  rcases b with j | ⟨β, hβ⟩
  · have h := d4P_pow_hVec (K := K) n j
    rw [hVec, hVec] at h
    rw [h, Finsupp.single_apply] at hab
    have ha : Sum.inl ((d4Rho ^ n) j) = a := by
      by_contra h'
      exact hab (if_neg h')
    rw [← ha]
    rfl
  · have h := d4P_pow_rootVec (K := K) n hβ
    have hβ' : IsRoot Tag.D4 (permLattice (d4Rho ^ n) β) := hβ.permLattice (d4Rho_cartan n)
    rw [rootVec_eq_single_of_isRoot hβ, rootVec_eq_single_of_isRoot hβ'] at h
    rw [h, Finsupp.single_apply] at hab
    have ha : (Sum.inr ⟨permLattice (d4Rho ^ n) β, hβ'⟩ : Label Tag.D4) = a := by
      by_contra h'
      exact hab (if_neg h')
    rw [← ha]
    exact height_permLattice' _ _

theorem coord_self_ne_zero_of_mem_borelGroup
    {τ : Tag} {g : ModGL τ K} (hg : g ∈ borelGroup τ K)
    (b : Label τ) : (g : Module.End K (RootModule τ K)) (Finsupp.single b 1) b ≠ 0 := by
  have hTB := triangular_borel_structure.{0, 0} τ K
  have hg' : g ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hTB.2.2.2.2.1]
    exact hg
  obtain ⟨h, hh, u, hu, rfl⟩ := hg'
  obtain ⟨c, hc⟩ := exists_apply_single_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh) b
  have hu1 := (isUpperUnitriangular_of_mem (posUnipotent_le_posFiltration τ K hu)).1 b
  rw [Units.val_mul, Module.End.mul_apply,
    apply_apply_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh) b hc, hu1, mul_one]
  exact c.ne_zero

theorem eps_eq_zero_of_isRL {c : ModGL Tag.D4 K} (hc : c ∈ adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) {ε : ℕ} (hε : ε < 3)
    (hM : IsRL ((c * rootDiagUnit Tag.D4 a * d4P K ^ ε : ModGL Tag.D4 K) :
      Module.End K (RootModule Tag.D4 K))) : ε = 0 := by
  set M := c * rootDiagUnit Tag.D4 a * d4P K ^ ε with hMdef
  have hP3 : (d4P K ^ ε)⁻¹ = d4P K ^ (2 * ε) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_add, show 2 * ε + ε = 3 * ε by ring, pow_mul,
      show d4P K ^ 3 = 1 from diagramMap_pow_order TwistTag.D4 K, one_pow]
  have hceq : c = M * d4P K ^ (2 * ε) * rootDiagUnit Tag.D4 a⁻¹ := by
    rw [hMdef, ← hP3, ← rootDiagUnit_inv]
    group
  have hcg : IsGraded (c : Module.End K (RootModule Tag.D4 K)) := by
    rw [hceq, Units.val_mul, Units.val_mul]
    exact (hM.isGraded.mul (isGraded_d4P_pow (2 * ε))).mul (isRL_rootDiagUnit a⁻¹).isGraded
  have hcB := mem_borelGroup_of_isGraded hc hcg
  have hfix : ∀ i : Fin Tag.D4.rank, (d4Rho ^ ε) i = i := by
    intro i
    have hi := isRoot_single Tag.D4 i
    set γ := permLattice (d4Rho ^ ε) (Pi.single i 1) with hγ
    have hγr : IsRoot Tag.D4 γ := hi.permLattice (d4Rho_cartan ε)
    have hγe : γ = Pi.single ((d4Rho ^ ε) i) 1 := permLattice_single _ i
    obtain ⟨u, hu⟩ := ((CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_diagonalGroup (τ := Tag.D4)
      (K := K) a).2 γ hγr)
    have hMv : (M : Module.End K (RootModule Tag.D4 K)) (rootVec Tag.D4 K (Pi.single i 1)) =
        (u : K) • (c : Module.End K (RootModule Tag.D4 K)) (rootVec Tag.D4 K γ) := by
      rw [hMdef, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
        d4P_pow_rootVec ε hi, ← hγ, hu, map_smul]
    have hcoord : (M : Module.End K (RootModule Tag.D4 K))
        (Finsupp.single (Sum.inr ⟨Pi.single i 1, hi⟩) 1) (Sum.inr ⟨γ, hγr⟩) ≠ 0 := by
      rw [← rootVec_eq_single_of_isRoot hi, hMv, Finsupp.smul_apply, smul_eq_mul,
        rootVec_eq_single_of_isRoot hγr]
      exact mul_ne_zero u.ne_zero (coord_self_ne_zero_of_mem_borelGroup hcB _)
    have h := hM _ _ hcoord
    simp only [wRel, one_smul, Sum.inr.injEq, Subtype.mk.injEq] at h
    rw [hγe] at h
    have := congrFun h ((d4Rho ^ ε) i)
    by_contra hne
    simp [Pi.single_apply, hne] at this
  have hρ : d4Rho ^ ε = 1 := Equiv.ext hfix
  interval_cases ε
  · rfl
  · exact absurd hρ (by decide)
  · exact absurd hρ (by decide)

end Key

section Split

theorem d4_sep_check : ∀ m m' : Fin 24,
    (∀ j : Fin 4, (∑ k, Tag.D4.cartan j k * CFSG.RankThree.Chevalley.d4RootVec m k) % 3 =
      (∑ k, Tag.D4.cartan j k * CFSG.RankThree.Chevalley.d4RootVec m' k) % 3) → m = m' := by
  decide +kernel

theorem d4_ne_check : ∀ m : Fin 24, ∃ j : Fin 4,
    (∑ k, Tag.D4.cartan j k * CFSG.RankThree.Chevalley.d4RootVec m k) % 3 ≠ 0 := by
  decide +kernel

theorem d4_sep (α β : Fin Tag.D4.rank → ℤ) (hα : IsRoot Tag.D4 α)
    (hβ : IsRoot Tag.D4 β)
    (h : ∀ j, (∑ k, Tag.D4.cartan j k * α k) % 3 = (∑ k, Tag.D4.cartan j k * β k) % 3) : α = β := by
  obtain ⟨m, rfl⟩ := CFSG.RankThree.Chevalley.isRoot_iff_exists_d4RootVec.1 hα
  obtain ⟨m', rfl⟩ := CFSG.RankThree.Chevalley.isRoot_iff_exists_d4RootVec.1 hβ
  rw [d4_sep_check m m' h]

theorem d4_ne (α : Fin Tag.D4.rank → ℤ) (hα : IsRoot Tag.D4 α) :
    ∃ j, (∑ k, Tag.D4.cartan j k * α k) % 3 ≠ 0 := by
  obtain ⟨m, rfl⟩ := CFSG.RankThree.Chevalley.isRoot_iff_exists_d4RootVec.1 hα
  exact d4_ne_check m

variable {K : Type} [Field K]

theorem fix_cube_root {σ : K ≃+* K} {k : ℕ} (hσ : σ ^ 3 ^ k = 1) {w : K} (hw3 : w ^ 3 = 1)
    (hw1 : w ≠ 1) : σ w = w := by
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw3
  have hq : w ^ 2 + w + 1 = 0 := by
    have h : (w - 1) * (w ^ 2 + w + 1) = 0 := by linear_combination hw3
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hw1
    · exact h
  have hq' : (σ w) ^ 2 + σ w + 1 = 0 := by
    have := congrArg σ hq
    simpa using this
  have hcases : (σ w - w) * (σ w - w ^ 2) = 0 := by linear_combination hq' - σ w * hq + hw3
  rcases mul_eq_zero.1 hcases with h | h
  · exact sub_eq_zero.1 h
  · exfalso
    have hσw : σ w = w ^ 2 := sub_eq_zero.1 h
    have hσ2 : (σ ^ 2) w = w := by
      rw [pow_two]
      change σ (σ w) = w
      rw [hσw, map_pow, hσw]
      linear_combination w * hw3
    have hσ2m : ∀ m : ℕ, (σ ^ (2 * m)) w = w := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
        change (σ ^ (2 * m)) ((σ ^ 2) w) = w
        rw [hσ2, ih]
    obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have h1 : (σ ^ 3 ^ k) w = w := by rw [hσ]; rfl
    rw [hm, pow_succ] at h1
    change (σ ^ (2 * m)) (σ w) = w at h1
    rw [hσw, map_pow, hσ2m] at h1
    have : w * (w - 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · exact hw0 h
    · exact hw1 (sub_eq_zero.1 h)

theorem d4F_apply (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (x : ModGL Tag.D4 K) :
    d4F K a σ ε x = rootDiagUnit Tag.D4 a * d4P K ^ ε *
      Units.map (entrywiseHom σ.toRingHom) x * (d4P K ^ ε)⁻¹ * (rootDiagUnit Tag.D4 a)⁻¹ := by
  have e : d4F K a σ ε x = exactNormalAutGL Tag.D4 K a σ 0 (d4P K ^ ε * x * (d4P K ^ ε)⁻¹) := rfl
  rw [e, exactNormalAutGL_apply]
  have hQ : exactQ Tag.D4 K 0 = 1 := rfl
  have hP : Units.map (entrywiseHom σ.toRingHom) (d4P K) = d4P K :=
    units_map_entrywiseHom_diagramMap σ.toRingHom
  rw [hQ, map_mul, map_mul, map_inv, map_pow, hP]
  group

theorem eps_eq_zero_of_split [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    (S : Sylow 3 (adjointGroup Tag.D4 K)) (c : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (σ : K ≃+* K) {ε : ℕ} (hε : ε < 3) {k : ℕ} (hσ : σ ^ 3 ^ k = 1)
    (hfix : ∀ x ∈ (S : Subgroup (adjointGroup Tag.D4 K)),
      (MulAut.conj c * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) x = x) : ε = 0 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  obtain ⟨ω, hωo⟩ : ∃ ω : Kˣ, orderOf ω = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact h3)
  have hω3 : ω ^ 3 = 1 := by rw [← hωo]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hωo
    exact absurd hωo (by norm_num)
  have hσω : Units.map σ.toRingHom.toMonoidHom ω = ω := by
    apply Units.ext
    change σ (ω : K) = ω
    refine fix_cube_root hσ (by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]) ?_
    intro h
    exact hω1 (Units.ext h)
  set β := exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε with hβ
  obtain ⟨g, hg⟩ := exists_conj_fix_of_isPGroup S (isPGroup_torus3 (τ := Tag.D4) ω hω3) hfix
  set c' : adjointGroup Tag.D4 K := g * c * β g⁻¹ with hc'
  have heq : MulAut.conj g * (MulAut.conj c * β) * (MulAut.conj g)⁻¹ = MulAut.conj c' * β := by
    refine MulEquiv.ext fun x => ?_
    simp only [hc', MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv]
  set M : ModGL Tag.D4 K := (c' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε with hM
  have hcomm : ∀ j : Fin Tag.D4.rank, M * rootDiagUnit Tag.D4 (fun l => ω ^ Tag.D4.cartan j l) =
      rootDiagUnit Tag.D4 (fun l => ω ^ Tag.D4.cartan j l) * M := by
    intro j
    have h1 := hg _ (torusElt_mem_torus3 ω hω3 j)
    rw [heq] at h1
    have h2 := congrArg Subtype.val h1
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [hβ, coe_normal_mul_graph, d4F_apply] at h2
    change (c' : ModGL Tag.D4 K) * (rootDiagUnit Tag.D4 a * d4P K ^ ε *
      Units.map (entrywiseHom σ.toRingHom) (torusElt Tag.D4 K j ω) * (d4P K ^ ε)⁻¹ *
        (rootDiagUnit Tag.D4 a)⁻¹) * (c' : ModGL Tag.D4 K)⁻¹ = torusElt Tag.D4 K j ω at h2
    rw [CFSG.LieType.Chevalley.entrywise_torusElt, hσω, torusElt_eq_rootDiagUnit] at h2
    rw [hM]
    calc (c' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε *
          rootDiagUnit Tag.D4 (fun l => ω ^ Tag.D4.cartan j l)
        = ((c' : ModGL Tag.D4 K) * (rootDiagUnit Tag.D4 a * d4P K ^ ε *
            rootDiagUnit Tag.D4 (fun l => ω ^ Tag.D4.cartan j l) * (d4P K ^ ε)⁻¹ *
              (rootDiagUnit Tag.D4 a)⁻¹) * (c' : ModGL Tag.D4 K)⁻¹) *
            ((c' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) := by group
      _ = _ := by rw [h2]
  have hRL : IsRL (M : Module.End K (RootModule Tag.D4 K)) :=
    isRL_of_commute (fun j l => ω ^ Tag.D4.cartan j l) hcomm
      (fun α β hα hβ hαβ => sep_of_mod_three hωo d4_sep hα hβ hαβ)
      (fun α hα => ne_of_mod_three hωo (d4_ne α hα))
  exact eps_eq_zero_of_isRL c'.2 a hε hRL

end Split

section CharThree

variable {K : Type} [Field K] [Finite K]

theorem pinnedX_mem_posUnipotent' {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hpos : 0 < height α) (c : K) : pinnedX τ K α c ∈ posUnipotent τ K :=
  Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem ⟨hα, hpos⟩ (Subgroup.subset_closure ⟨c, rfl⟩))

theorem eps_eq_zero_of_char_three [CharP K 3] (S : Sylow 3 (adjointGroup Tag.D4 K))
    (c : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) {ε : ℕ} (hε : ε < 3)
    (hfix : ∀ x ∈ (S : Subgroup (adjointGroup Tag.D4 K)),
      (MulAut.conj c * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) x = x) : ε = 0 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  set H : Subgroup (adjointGroup Tag.D4 K) := (posUnipotent Tag.D4 K).subgroupOf
    (adjointGroup Tag.D4 K) with hH
  obtain ⟨P, hP⟩ := (exceptional_ordinary_Sylow_opposition Tag.D4 K 3 w₀ hw₀).1
  have hHp : IsPGroup 3 H := by
    rw [hH, ← hP]
    exact P.isPGroup'
  set β := exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε with hβ
  obtain ⟨g, hg⟩ := exists_conj_fix_of_isPGroup S hHp hfix
  set c' : adjointGroup Tag.D4 K := g * c * β g⁻¹ with hc'
  have heq : MulAut.conj g * (MulAut.conj c * β) * (MulAut.conj g)⁻¹ = MulAut.conj c' * β := by
    refine MulEquiv.ext fun x => ?_
    simp only [hc', MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv]
  rw [heq] at hg
  set α' := MulAut.conj c' * β with hα'
  have hmemH : ∀ y : ↥(adjointGroup Tag.D4 K), y ∈ H ↔
      (y : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K := fun y => by rw [hH, Subgroup.mem_subgroupOf]
  have hβA : β ∈ unipotentPairAut Tag.D4 K := mul_mem (exactNormalAut_mem a σ 0) (d4Graph_mem ε)
  have hβH : H.map β.toMonoidHom = H := by rw [hH]; exact hβA.1
  have hαH : H.map α'.toMonoidHom = H := by
    refine le_antisymm ?_ fun y hy => ⟨y, hy, hg y hy⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hg y hy]
    exact hy
  have hcH : H.map (MulAut.conj c').toMonoidHom = H := by
    have e : MulAut.conj c' = α' * β⁻¹ := by rw [hα']; group
    rw [e, map_toMonoidHom_mul_mulAut, map_inv_toMonoidHom_of_map_eq hβH, hαH]
  have hcH' : H.map (MulAut.conj c')⁻¹.toMonoidHom = H := map_inv_toMonoidHom_of_map_eq hcH
  have hnorm : (c' : ModGL Tag.D4 K) ∈
      Subgroup.normalizer (posUnipotent Tag.D4 K : Set (ModGL Tag.D4 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxG : x ∈ adjointGroup Tag.D4 K := posUnipotent_le_adjointGroup hx
      have hmem : (⟨x, hxG⟩ : ↥(adjointGroup Tag.D4 K)) ∈ H := (hmemH _).2 hx
      have h1 : (MulAut.conj c') ⟨x, hxG⟩ ∈ H.map (MulAut.conj c').toMonoidHom :=
        Subgroup.mem_map_of_mem _ hmem
      rw [hcH] at h1
      exact (hmemH _).1 h1
    · intro hx
      have hxG' : (c' : ModGL Tag.D4 K) * x * (c' : ModGL Tag.D4 K)⁻¹ ∈ adjointGroup Tag.D4 K :=
        posUnipotent_le_adjointGroup hx
      have hxG : x ∈ adjointGroup Tag.D4 K := by
        have := mul_mem (mul_mem (inv_mem c'.2) hxG') c'.2
        simpa [mul_assoc] using this
      have hmem : (⟨(c' : ModGL Tag.D4 K) * x * (c' : ModGL Tag.D4 K)⁻¹, hxG'⟩ :
          ↥(adjointGroup Tag.D4 K)) ∈ H := (hmemH _).2 hx
      have h1 : (MulAut.conj c')⁻¹ ⟨_, hxG'⟩ ∈ H.map (MulAut.conj c')⁻¹.toMonoidHom :=
        Subgroup.mem_map_of_mem _ hmem
      rw [hcH'] at h1
      have e : (MulAut.conj c')⁻¹ (⟨(c' : ModGL Tag.D4 K) * x * (c' : ModGL Tag.D4 K)⁻¹, hxG'⟩ :
          ↥(adjointGroup Tag.D4 K)) = ⟨x, hxG⟩ := by
        apply Subtype.ext
        simp [MulAut.conj_apply, mul_assoc]
      rw [e] at h1
      exact (hmemH _).1 h1
  have hcB : (c' : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K := by
    rw [← CFSG.Quasithin.H13.NQCat.LieCartan.G2.normalizer_posUnipotent_inf_eq
      (K := K) (τ := Tag.D4)]
    exact ⟨hnorm, c'.2⟩
  have hcS := borelScalar_of_mem_borelGroup hcB
  obtain ⟨e, he⟩ := exists_d4F_pinnedX (K := K) a σ ε
  have hfixρ : ∀ j : Fin Tag.D4.rank, (d4Rho ^ ε) j = j := by
    intro j
    by_contra hne
    set γ : Fin Tag.D4.rank → ℤ := Pi.single j 1 with hγ
    have hγr : IsRoot Tag.D4 γ := isRoot_single _ j
    have hγp : IsRoot Tag.D4 γ ∧ 0 < height γ := ⟨hγr, by rw [height_single']; norm_num⟩
    set δ : Fin Tag.D4.rank → ℤ := Pi.single ((d4Rho ^ ε) j) 1 with hδ
    have hδr : IsRoot Tag.D4 δ := isRoot_single _ _
    have hδp : IsRoot Tag.D4 δ ∧ 0 < height δ := ⟨hδr, by rw [height_single']; norm_num⟩
    have hργ : permLattice (d4Rho ^ ε) γ = δ := permLattice_single _ j
    have hγδ : γ ≠ δ := by
      intro h
      apply hne
      have := congrFun h ((d4Rho ^ ε) j)
      simp only [hγ, hδ, Pi.single_eq_same] at this
      by_contra h'
      rw [Pi.single_eq_of_ne h'] at this
      exact absurd this (by norm_num)
    have hxG : pinnedX Tag.D4 K γ 1 ∈ adjointGroup Tag.D4 K :=
      posUnipotent_le_adjointGroup (pinnedX_mem_posUnipotent' hγr (by rw [height_single']; norm_num) 1)
    set x : adjointGroup Tag.D4 K := ⟨pinnedX Tag.D4 K γ 1, hxG⟩ with hx
    have hxH : x ∈ H := (hmemH x).2 (pinnedX_mem_posUnipotent' hγr (by rw [height_single']; norm_num) 1)
    have hαx := congrArg Subtype.val (hg x hxH)
    rw [hα', MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hβ, coe_normal_mul_graph] at hαx
    change (c' : ModGL Tag.D4 K) * d4F K a σ ε (pinnedX Tag.D4 K γ 1) * (c' : ModGL Tag.D4 K)⁻¹ =
      pinnedX Tag.D4 K γ 1 at hαx
    rw [he γ hγr 1, hργ, map_one, mul_one] at hαx
    have hmemδ : pinnedX Tag.D4 K δ (e γ) ∈ heightSeries Tag.D4 K (height δ) :=
      pinnedX_mem_heightSeries_height hδp _
    have h1 := hcS.spec.2 δ hδp _ hmemδ
    rw [hαx, rootCoord_self] at h1
    have h0 : rootCoord hδp (pinnedX Tag.D4 K γ 1) = 0 :=
      rootCoord_pinnedX_of_ne hδp hγp (by rw [height_single', height_single']) hγδ 1
    rw [h0] at h1
    have heγ : e γ ≠ 0 := by
      intro h
      have h2 := he γ hγr 1
      rw [map_one, mul_one, h, pinnedX_zero] at h2
      have hinj : Function.Injective (d4F K a σ ε) := by
        intro u v huv
        have := congrArg (fun y => (MulAut.conj (d4P K ^ ε))⁻¹
          ((exactNormalAutGL Tag.D4 K a σ 0)⁻¹ y)) huv
        simpa [d4F] using this
      have h3 : pinnedX Tag.D4 K γ 1 = pinnedX Tag.D4 K γ 0 := by
        rw [pinnedX_zero]
        exact hinj (h2.trans (map_one _).symm)
      exact one_ne_zero (pinnedX_injective Tag.D4 K γ h3)
    exact mul_ne_zero (hcS.spec.1 δ hδr hδp.2) heγ h1.symm
  have hρ : d4Rho ^ ε = 1 := Equiv.ext hfixρ
  interval_cases ε
  · rfl
  · exact absurd hρ (by decide)
  · exact absurd hρ (by decide)

end CharThree

section ThreePoints

variable {G X : Type*} [Group G] [MulAction G X]

theorem smul_eq_of_decomp {F y z : X} (hO : ∀ a : G, a • F = F ∨ a • F = y ∨ a • F = z)
    {κ : G} (hκF : κ • F = F) (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z)
    {N : Subgroup G} (hNn : N.Normal) (hN : ∀ n ∈ N, n • F = F) {α ι δ s : G} (hι : ι ∈ N)
    (hδ : δ * δ ∈ N) (hsF : s • F = F) {m k : ℕ} (hs : s ^ 3 ^ m = 1) (hα : α = ι * δ * s)
    (hαk : α ^ 3 ^ k = 1) : α • F = F := by
  by_contra hαF
  have hyF : y ≠ F := by
    intro h
    apply hyz
    rw [← hκy, h, hκF]
  have hzF : z ≠ F := fun h => hyF (by rw [← hκz, h, hκF])
  have horb : ∀ w, (w = F ∨ w = y ∨ w = z) → ∃ g : G, g • F = w := by
    rcases hO α with h | h | h
    · exact absurd h hαF
    · rintro w (rfl | rfl | rfl)
      · exact ⟨1, one_smul _ _⟩
      · exact ⟨α, h⟩
      · exact ⟨κ * α, by rw [mul_smul, h, hκy]⟩
    · rintro w (rfl | rfl | rfl)
      · exact ⟨1, one_smul _ _⟩
      · exact ⟨κ * α, by rw [mul_smul, h, hκz]⟩
      · exact ⟨α, h⟩
  have hO' : ∀ (a : G) (w : X), (w = F ∨ w = y ∨ w = z) → (a • w = F ∨ a • w = y ∨ a • w = z) := by
    intro a w hw
    obtain ⟨g, rfl⟩ := horb w hw
    rw [← mul_smul]
    exact hO (a * g)
  have hNw : ∀ n ∈ N, ∀ w, (w = F ∨ w = y ∨ w = z) → n • w = w := by
    intro n hn w hw
    obtain ⟨g, rfl⟩ := horb w hw
    have : g⁻¹ * n * g ∈ N := by
      have := hNn.conj_mem n hn g⁻¹
      simpa [mul_assoc] using this
    have h1 := hN _ this
    calc n • g • F = g • ((g⁻¹ * n * g) • F) := by
          rw [← mul_smul, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      _ = g • F := by rw [h1]
  have hinj : ∀ (a : G) {u v : X}, a • u = a • v → u = v := fun a u v h => smul_left_cancel a h
  obtain ⟨j, hj⟩ : Odd (3 ^ m) := Odd.pow (by decide)
  obtain ⟨j', hj'⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have hsfix : ∀ w, (w = y ∨ w = z) → s • w = w := by
    have hsy : s • y = y ∨ s • y = z := by
      rcases hO' s y (Or.inr (Or.inl rfl)) with h | h | h
      · exact absurd (hinj s (h.trans hsF.symm)) hyF
      · exact Or.inl h
      · exact Or.inr h
    have hsz : s • z = y ∨ s • z = z := by
      rcases hO' s z (Or.inr (Or.inr rfl)) with h | h | h
      · exact absurd (hinj s (h.trans hsF.symm)) hzF
      · exact Or.inl h
      · exact Or.inr h
    have hnot : ¬ (s • y = z ∧ s • z = y) := by
      rintro ⟨h1, h2⟩
      have hs2 : (s * s) • y = y := by rw [mul_smul, h1, h2]
      have hs2j : ∀ i : ℕ, ((s * s) ^ i) • y = y := by
        intro i
        induction i with
        | zero => simp
        | succ i ih => rw [pow_succ, mul_smul, hs2, ih]
      have h3 : (s ^ 3 ^ m) • y = z := by
        rw [hj, pow_succ', mul_smul, pow_mul, sq, hs2j j, h1]
      rw [hs, one_smul] at h3
      exact hyz h3
    rintro w (rfl | rfl)
    · rcases hsy with h | h
      · exact h
      · rcases hsz with h' | h'
        · exact absurd ⟨h, h'⟩ hnot
        · exact absurd (hinj s (h.trans h'.symm)) hyz
    · rcases hsz with h | h
      · rcases hsy with h' | h'
        · exact absurd (hinj s (h.trans h'.symm)) hyz.symm
        · exact absurd ⟨h', h⟩ hnot
      · exact h
  have hsw : ∀ w, (w = F ∨ w = y ∨ w = z) → s • w = w := by
    rintro w (rfl | h)
    · exact hsF
    · exact hsfix w h
  have hαw : ∀ w, (w = F ∨ w = y ∨ w = z) → α • w = δ • w := by
    intro w hw
    rw [hα, mul_smul, mul_smul, hsw w hw, hNw ι hι _ (hO' δ w hw)]
  have hαn : ∀ n : ℕ, α ^ n • F = δ ^ n • F ∧ (δ ^ n • F = F ∨ δ ^ n • F = y ∨ δ ^ n • F = z) := by
    intro n
    induction n with
    | zero => exact ⟨by simp, by simp⟩
    | succ n ih =>
      refine ⟨?_, by rw [pow_succ', mul_smul]; exact hO' δ _ ih.2⟩
      rw [pow_succ', mul_smul, ih.1, hαw _ ih.2, ← mul_smul, ← pow_succ']
  have hδF : δ • F = F := by
    have h1 := (hαn (3 ^ k)).1
    rw [hαk, one_smul, hj', pow_succ, mul_smul] at h1
    have hδ2 : (δ * δ) ^ j' ∈ N := pow_mem hδ j'
    rw [← sq, ← pow_mul] at hδ2
    rw [hNw _ hδ2 (δ • F) (hO' δ F (Or.inl rfl))] at h1
    exact h1.symm
  exact hαF ((hαw F (Or.inl rfl)).trans hδF)

end ThreePoints

section Nonsplit

open CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
  CFSG.RankThree.PartOne.CTP CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.HardMathSupport.Seitz.Proving

@[expose] def frameV : Fin 4 → Fin Tag.D4.rank → ℤ :=
  ![Tag.D4.cartan ⟨2, by decide⟩,
    (reflM ⟨0, by decide⟩ * reflM ⟨1, by decide⟩).mulVec (Tag.D4.cartan ⟨2, by decide⟩),
    (reflM ⟨3, by decide⟩ * reflM ⟨0, by decide⟩).mulVec (Tag.D4.cartan ⟨2, by decide⟩),
    (reflM ⟨1, by decide⟩ * reflM ⟨3, by decide⟩).mulVec (Tag.D4.cartan ⟨2, by decide⟩)]

theorem d4_frame_sep_check : ∀ m m' : Fin 24,
    (∀ i : Fin 4, (∑ k, frameV i k * CFSG.RankThree.Chevalley.d4RootVec m k) % 3 =
      (∑ k, frameV i k * CFSG.RankThree.Chevalley.d4RootVec m' k) % 3) → m = m' := by
  decide +kernel

theorem d4_frame_ne_check : ∀ m : Fin 24, ∃ i : Fin 4,
    (∑ k, frameV i k * CFSG.RankThree.Chevalley.d4RootVec m k) % 3 ≠ 0 := by
  decide +kernel

theorem d4_frame_sep (α β : Fin Tag.D4.rank → ℤ)
    (hα : IsRoot Tag.D4 α) (hβ : IsRoot Tag.D4 β)
    (h : ∀ i, (∑ k, frameV i k * α k) % 3 = (∑ k, frameV i k * β k) % 3) : α = β := by
  obtain ⟨m, rfl⟩ := CFSG.RankThree.Chevalley.isRoot_iff_exists_d4RootVec.1 hα
  obtain ⟨m', rfl⟩ := CFSG.RankThree.Chevalley.isRoot_iff_exists_d4RootVec.1 hβ
  rw [d4_frame_sep_check m m' h]

theorem d4_frame_ne (α : Fin Tag.D4.rank → ℤ) (hα : IsRoot Tag.D4 α) :
    ∃ i, (∑ k, frameV i k * α k) % 3 ≠ 0 := by
  obtain ⟨m, rfl⟩ := CFSG.RankThree.Chevalley.isRoot_iff_exists_d4RootVec.1 hα
  exact d4_frame_ne_check m

variable {K : Type} [Field K]

theorem rootChar_zpow_vec {τ : Tag} (ω : Kˣ) (v α : Fin τ.rank → ℤ) :
    rootChar (fun k => ω ^ v k) α = ω ^ (∑ k, v k * α k) := by
  unfold rootChar
  rw [← prod_zpow_eq_zpow_sum']
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul]

theorem sep_of_mod_three_vec {τ : Tag} {ι : Type*} {ω : Kˣ} (hω : orderOf ω = 3)
    (V : ι → Fin τ.rank → ℤ)
    (hsep : ∀ α β, IsRoot τ α → IsRoot τ β →
      (∀ i, (∑ k, V i k * α k) % 3 = (∑ k, V i k * β k) % 3) → α = β)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hαβ : α ≠ β) :
    ∃ i, rootChar (fun k => ω ^ V i k) α ≠ rootChar (fun k => ω ^ V i k) β := by
  by_contra h
  push Not at h
  refine hαβ (hsep α β hα hβ fun i => ?_)
  have h1 := h i
  rw [rootChar_zpow_vec, rootChar_zpow_vec, zpow_eq_zpow_iff_modEq, hω] at h1
  exact h1

theorem ne_of_mod_three_vec {τ : Tag} {ι : Type*} {ω : Kˣ} (hω : orderOf ω = 3)
    (V : ι → Fin τ.rank → ℤ) {α : Fin τ.rank → ℤ} (hne : ∃ i, (∑ k, V i k * α k) % 3 ≠ 0) :
    ∃ i, rootChar (fun k => ω ^ V i k) α ≠ 1 := by
  obtain ⟨i, hi⟩ := hne
  refine ⟨i, fun h => hi ?_⟩
  rw [rootChar_zpow_vec, ← zpow_zero ω, zpow_eq_zpow_iff_modEq, hω] at h
  exact h

theorem isPGroup_closure_of_commute {G : Type*} [Group G] {p : ℕ} {s : Set G}
    (hc : ∀ x ∈ s, ∀ y ∈ s, Commute x y) (hp : ∀ x ∈ s, x ^ p = 1) :
    IsPGroup p (Subgroup.closure s) := by
  have h1 : Subgroup.closure s ≤ Subgroup.centralizer s :=
    (Subgroup.closure_le _).2 fun x hx =>
      Subgroup.mem_centralizer_iff.2 fun y hy => (hc y hy x hx).eq
  have h2 : Subgroup.closure s ≤ Subgroup.centralizer (Subgroup.closure s : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
      ((Subgroup.mem_centralizer_iff.1 (h1 hy)) x hx).symm
  have hpow : ∀ x ∈ Subgroup.closure s, x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hp x hx
    | one => exact one_pow p
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := (Subgroup.mem_centralizer_iff.1 (h2 hx) y hy).symm
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hpow g g.2)

theorem units_map_entrywiseHom_refl' {τ : Tag} (x : ModGL τ K) :
    Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) x = x :=
  Units.ext (entrywise_id _)

theorem commute_conj_baseChange
    {L : Type} [Field L] (f : K →+* L) {M X : ModGL Tag.D4 K}
    (G D : ModGL Tag.D4 L) (hMX : M * X = X * M) (hX : baseChangeGL f X = G * D * G⁻¹) :
    (G⁻¹ * baseChangeGL f M * G) * D = D * (G⁻¹ * baseChangeGL f M * G) := by
  have h1 := congrArg (baseChangeGL f) hMX
  rw [map_mul, map_mul, hX] at h1
  calc (G⁻¹ * baseChangeGL f M * G) * D = G⁻¹ * (baseChangeGL f M * (G * D * G⁻¹)) * G := by
        group
    _ = G⁻¹ * ((G * D * G⁻¹) * baseChangeGL f M) * G := by rw [h1]
    _ = D * (G⁻¹ * baseChangeGL f M * G) := by group

theorem frameDiag_conj_frameK₁ (C X : SL2 K) :
    frameDiag C * frameK₁ K X * (frameDiag C)⁻¹ = frameK₁ K (C * X * C⁻¹) := by
  obtain ⟨h13, h12, -⟩ := frameK_commute (K := K) X C
  rw [frameDiag, map_mul, map_mul, map_inv]
  calc frameK₁ K C * frameK₃ K C * frameK₂ K C * frameK₁ K X *
        (frameK₁ K C * frameK₃ K C * frameK₂ K C)⁻¹ =
      frameK₁ K C * (frameK₃ K C * (frameK₂ K C * frameK₁ K X * (frameK₂ K C)⁻¹) *
        (frameK₃ K C)⁻¹) * (frameK₁ K C)⁻¹ := by group
    _ = frameK₁ K C * frameK₁ K X * (frameK₁ K C)⁻¹ := by
      rw [← h12.eq, mul_inv_cancel_right, ← h13.eq, mul_inv_cancel_right]

theorem gTw_inv_conj_of_commute {Q : SL2 K} {x : ↥(adjointGroup Tag.D4 K)}
    (hx : Commute x (sl2At K ⟨2, by decide⟩ Q)) :
    (gTw Q)⁻¹ * x * gTw Q = frameDiag Q⁻¹ * x * (frameDiag Q⁻¹)⁻¹ := by
  rw [gTw, mul_inv_rev, frameDiag_inv, inv_inv,
    show (frameDiag Q)⁻¹ * (sl2At K ⟨2, by decide⟩ Q)⁻¹ * x *
        (sl2At K ⟨2, by decide⟩ Q * frameDiag Q) =
      (frameDiag Q)⁻¹ * ((sl2At K ⟨2, by decide⟩ Q)⁻¹ * (x * sl2At K ⟨2, by decide⟩ Q)) *
        frameDiag Q by group, hx.eq, inv_mul_cancel_left]

variable (K) in
@[expose] noncomputable def frameHom : Fin 4 → (SL2 K →* ↥(adjointGroup Tag.D4 K)) :=
  ![sl2At K ⟨2, by decide⟩, frameK₁ K, frameK₂ K, frameK₃ K]

theorem frameHom_pow_three (i : Fin 4) : frameHom K i (orderThreeSL K) ^ 3 = 1 := by
  rw [← map_pow, orderThreeSL_pow_three, map_one]

theorem frameHom_commute (i j : Fin 4) :
    Commute (frameHom K i (orderThreeSL K)) (frameHom K j (orderThreeSL K)) := by
  obtain ⟨c1, c3, c2⟩ := frameK_commute_sl2Two (K := K) (orderThreeSL K) (orderThreeSL K)
  obtain ⟨d13, d12, d32⟩ := frameK_commute (K := K) (orderThreeSL K) (orderThreeSL K)
  fin_cases i <;> fin_cases j
  exacts [Commute.refl _, c1.symm, c2.symm, c3.symm, c1, Commute.refl _, d12, d13, c2, d12.symm,
    Commute.refl _, d32.symm, c3, d13.symm, d32, Commute.refl _]

theorem bcAd_frameHom {L : Type} [Field L] (f : K →+* L) (i : Fin 4) :
    bcAd f (frameHom K i (orderThreeSL K)) = frameHom L i (orderThreeSL L) := by
  have h0 : bcAd f (sl2At K ⟨2, by decide⟩ (orderThreeSL K)) =
      sl2At L ⟨2, by decide⟩ (orderThreeSL L) := by rw [bcAd_sl2At, mapSL_orderThreeSL]
  have h1 : bcAd f (frameK₁ K (orderThreeSL K)) = frameK₁ L (orderThreeSL L) := by
    rw [bcAd_frameK₁, mapSL_orderThreeSL]
  have h2 : bcAd f (frameK₂ K (orderThreeSL K)) = frameK₂ L (orderThreeSL L) := by
    rw [bcAd_frameK₂, mapSL_orderThreeSL]
  have h3 : bcAd f (frameK₃ K (orderThreeSL K)) = frameK₃ L (orderThreeSL L) := by
    rw [bcAd_frameK₃, mapSL_orderThreeSL]
  fin_cases i
  exacts [h0, h1, h2, h3]

theorem units_map_frameHom (σ : K ≃+* K) (i : Fin 4) :
    Units.map (entrywiseHom σ.toRingHom)
        ((frameHom K i (orderThreeSL K) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      ((frameHom K i (orderThreeSL K) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) := by
  rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL, ← coe_bcAd, bcAd_frameHom]

theorem coe_ιTw_frameHom {K₂ : Type} [Field K₂] [Algebra K K₂] {Q : SL2 K₂} {ω : K₂ˣ}
    (hQ : Q⁻¹ * orderThreeSL K₂ * Q = HSL ω) (i : Fin 4) :
    ((ιTw K Q (frameHom K i (orderThreeSL K)) : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) =
      rootDiagUnit Tag.D4 (fun j => ω ^ frameV i j) := by
  have hB : Matrix.SpecialLinearGroup.map (algebraMap K K₂) (orderThreeSL K) = orderThreeSL K₂ :=
    mapSL_orderThreeSL _
  have hQ' : Q⁻¹ * orderThreeSL K₂ * Q⁻¹⁻¹ = HSL ω := by rw [inv_inv]; exact hQ
  obtain ⟨c1, c3, c2⟩ := frameK_commute_sl2Two (K := K₂) (orderThreeSL K₂) Q
  have h0 : ((ιTw K Q (sl2At K ⟨2, by decide⟩ (orderThreeSL K)) : ↥(adjointGroup Tag.D4 K₂)) :
      ModGL Tag.D4 K₂) = rootDiagUnit Tag.D4 (fun j => ω ^ Tag.D4.cartan ⟨2, by decide⟩ j) := by
    rw [ιTw_apply, bcAd_sl2At, hB, gTw_conj_sl2Two, hQ, sl2At_HSL, coe_torusElement]
  have h1 : ((ιTw K Q (frameK₁ K (orderThreeSL K)) : ↥(adjointGroup Tag.D4 K₂)) :
      ModGL Tag.D4 K₂) = rootDiagUnit Tag.D4 (fun j => ω ^ (reflM ⟨0, by decide⟩ *
        reflM ⟨1, by decide⟩).mulVec (Tag.D4.cartan ⟨2, by decide⟩) j) := by
    rw [ιTw_apply, bcAd_frameK₁, hB, gTw_inv_conj_of_commute c1, frameDiag_conj_frameK₁, hQ',
      frameK₁_apply, sl2At_HSL, coe_conj_torusElement (actsBy_nW_mul_nW _ _), tupAct_zpow]
  have h2 : ((ιTw K Q (frameK₂ K (orderThreeSL K)) : ↥(adjointGroup Tag.D4 K₂)) :
      ModGL Tag.D4 K₂) = rootDiagUnit Tag.D4 (fun j => ω ^ (reflM ⟨3, by decide⟩ *
        reflM ⟨0, by decide⟩).mulVec (Tag.D4.cartan ⟨2, by decide⟩) j) := by
    rw [ιTw_apply, bcAd_frameK₂, hB, gTw_inv_conj_of_commute c2, frameDiag_conj_frameK₂, hQ',
      frameK₂_eq, sl2At_HSL, coe_conj_torusElement (actsBy_nW_mul_nW _ _), tupAct_zpow]
  have h3 : ((ιTw K Q (frameK₃ K (orderThreeSL K)) : ↥(adjointGroup Tag.D4 K₂)) :
      ModGL Tag.D4 K₂) = rootDiagUnit Tag.D4 (fun j => ω ^ (reflM ⟨1, by decide⟩ *
        reflM ⟨3, by decide⟩).mulVec (Tag.D4.cartan ⟨2, by decide⟩) j) := by
    rw [ιTw_apply, bcAd_frameK₃, hB, gTw_inv_conj_of_commute c3, frameDiag_conj_frameK₃, hQ',
      frameK₃_eq, sl2At_HSL, coe_conj_torusElement (actsBy_nW_mul_nW _ _), tupAct_zpow]
  fin_cases i
  exacts [h0, h1, h2, h3]

theorem commute_of_fixed [Finite K] {c' x : ↥(adjointGroup Tag.D4 K)} {a : Fin Tag.D4.rank → Kˣ}
    {σ : K ≃+* K} {ε : ℕ}
    (h : (MulAut.conj c' * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) x = x)
    (hσ : Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.D4 K) = x) :
    (c' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε * (x : ModGL Tag.D4 K) =
      (x : ModGL Tag.D4 K) * ((c' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) := by
  have h2 := congrArg Subtype.val h
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_normal_mul_graph, d4F_apply, hσ] at h2
  calc (c' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε * (x : ModGL Tag.D4 K)
      = ((c' : ModGL Tag.D4 K) * (rootDiagUnit Tag.D4 a * d4P K ^ ε * (x : ModGL Tag.D4 K) *
          (d4P K ^ ε)⁻¹ * (rootDiagUnit Tag.D4 a)⁻¹) * (c' : ModGL Tag.D4 K)⁻¹) *
          ((c' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) := by group
    _ = _ := by rw [h2]

theorem exists_conj_baseChange_eq {L : Type} [Field L] [Finite L] (f : K →+* L)
    (c' : ↥(adjointGroup Tag.D4 K)) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ)
    (g : ↥(adjointGroup Tag.D4 L)) :
    ∃ c'' : ↥(adjointGroup Tag.D4 L),
      (g : ModGL Tag.D4 L)⁻¹ * baseChangeGL f ((c' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a *
          d4P K ^ ε) * (g : ModGL Tag.D4 L) =
        (c'' : ModGL Tag.D4 L) * rootDiagUnit Tag.D4 (fun j => Units.map (f : K →* L) (a j)) *
          d4P L ^ ε := by
  have hP : baseChangeGL f (d4P K) = d4P L := baseChangeGL_diagramMap f TwistTag.D4
  refine ⟨g⁻¹ * bcAd f c' * (exactNormalAut Tag.D4 L (fun j => Units.map (f : K →* L) (a j))
    (RingEquiv.refl L) 0 * d4Graph L ε) g, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_bcAd, coe_normal_mul_graph,
    d4F_apply, units_map_entrywiseHom_refl', map_mul, map_mul, map_pow, baseChangeGL_rootDiagUnit,
    hP]
  group
  rfl

theorem eps_eq_zero_of_nonsplit [Finite K] (hq : Nat.card K % 3 = 2)
    (S : Sylow 3 (adjointGroup Tag.D4 K)) (c : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (σ : K ≃+* K) {ε : ℕ} (hε : ε < 3)
    (hfix : ∀ x ∈ (S : Subgroup (adjointGroup Tag.D4 K)),
      (MulAut.conj c * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) x = x) : ε = 0 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  have := Fintype.ofFinite K
  obtain ⟨n, hp, -⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  obtain ⟨Q, ω, -, hQ, hω, -⟩ := exists_twist_data (K₂ := FiniteField.Extension K (ringChar K) 2)
    hq (FiniteField.natCard_extension K (ringChar K) 2)
    (σ := (FiniteField.Extension.frob K (ringChar K) 2).toRingEquiv.toRingHom)
    (fun y => FiniteField.Extension.frob_apply K (ringChar K) 2)
  have hRp : IsPGroup 3 (Subgroup.closure (Set.range fun i => frameHom K i (orderThreeSL K))) :=
    isPGroup_closure_of_commute (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact frameHom_commute i j)
      (by rintro _ ⟨i, rfl⟩; exact frameHom_pow_three i)
  obtain ⟨g, hg⟩ := exists_conj_fix_of_isPGroup S hRp hfix
  obtain ⟨c', hc'⟩ : ∃ c' : adjointGroup Tag.D4 K,
      c' = g * c * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) g⁻¹ := ⟨_, rfl⟩
  have heq : MulAut.conj g * (MulAut.conj c * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) *
      (MulAut.conj g)⁻¹ = MulAut.conj c' * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) := by
    refine MulEquiv.ext fun x => ?_
    simp only [hc', MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv]
  have hcommK : ∀ i, (c' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε *
      ((frameHom K i (orderThreeSL K) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      ((frameHom K i (orderThreeSL K) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) *
        ((c' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) := by
    intro i
    have h1 := hg _ (Subgroup.subset_closure (Set.mem_range_self i))
    rw [heq] at h1
    exact commute_of_fixed h1 (units_map_frameHom σ i)
  have hcomm : ∀ i, ((gTw Q : ↥(adjointGroup Tag.D4 (FiniteField.Extension K (ringChar K) 2))) :
      ModGL Tag.D4 (FiniteField.Extension K (ringChar K) 2))⁻¹ *
      baseChangeGL (algebraMap K (FiniteField.Extension K (ringChar K) 2))
        ((c' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) *
      ((gTw Q : ↥(adjointGroup Tag.D4 (FiniteField.Extension K (ringChar K) 2))) :
        ModGL Tag.D4 (FiniteField.Extension K (ringChar K) 2)) *
      rootDiagUnit Tag.D4 (fun j => ω ^ frameV i j) =
      rootDiagUnit Tag.D4 (fun j => ω ^ frameV i j) *
      (((gTw Q : ↥(adjointGroup Tag.D4 (FiniteField.Extension K (ringChar K) 2))) :
        ModGL Tag.D4 (FiniteField.Extension K (ringChar K) 2))⁻¹ *
      baseChangeGL (algebraMap K (FiniteField.Extension K (ringChar K) 2))
        ((c' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) *
      ((gTw Q : ↥(adjointGroup Tag.D4 (FiniteField.Extension K (ringChar K) 2))) :
        ModGL Tag.D4 (FiniteField.Extension K (ringChar K) 2))) := by
    intro i
    refine commute_conj_baseChange _ _ _ (hcommK i) ?_
    have hb : bcAd (algebraMap K (FiniteField.Extension K (ringChar K) 2))
        (frameHom K i (orderThreeSL K)) =
        gTw Q * ιTw K Q (frameHom K i (orderThreeSL K)) * (gTw Q)⁻¹ := by
      rw [ιTw_apply]
      group
    rw [← coe_bcAd, hb, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_ιTw_frameHom hQ i]
  have hRL := isRL_of_commute (fun i j => ω ^ frameV i j) hcomm
    (fun α β hα hβ hαβ => sep_of_mod_three_vec hω frameV d4_frame_sep hα hβ hαβ)
    (fun α hα => ne_of_mod_three_vec hω frameV (d4_frame_ne α hα))
  obtain ⟨c'', hc''⟩ := exists_conj_baseChange_eq
    (algebraMap K (FiniteField.Extension K (ringChar K) 2)) c' a ε (gTw Q)
  rw [hc''] at hRL
  exact eps_eq_zero_of_isRL c''.2 _ hε hRL

end Nonsplit

section Assembly

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal congr_conj)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit

variable {K : Type} [Field K]

theorem d4Graph_zero' : d4Graph K 0 = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [coe_d4Graph, pow_zero, one_mul, inv_one, mul_one, MulAut.one_apply]

theorem exactNormalAut_D4_eq_mul' (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) :
    exactNormalAut Tag.D4 K a σ 0 =
      exactNormalAut Tag.D4 K a 1 0 * entrywiseAdjointAut Tag.D4 σ := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [MulAut.mul_apply, coe_exactNormalAut, coe_exactNormalAut, coe_entrywiseAdjointAut]
  have hid : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom)
      (Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.D4 K)) =
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.D4 K) :=
    Units.ext (entrywise_id _)
  rw [hid]

theorem normalAut_sq_eq_conj (a : Fin Tag.D4.rank → Kˣ) :
    exactNormalAut Tag.D4 K a 1 0 * exactNormalAut Tag.D4 K a 1 0 =
      MulAut.conj (⟨rootDiagUnit Tag.D4 (fun j => a j ^ 2),
        rootDiagUnit_sq_mem_adjointGroup_D4 a⟩ : ↥(adjointGroup Tag.D4 K)) := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  have hid : ∀ x : ModGL Tag.D4 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ : exactQ Tag.D4 K 0 = 1 := rfl
  have hsq : rootDiagUnit Tag.D4 (fun j => a j ^ 2) =
      rootDiagUnit Tag.D4 a * rootDiagUnit Tag.D4 a := by
    rw [← rootDiagUnit_mul]
    congr 1
    funext j
    rw [Pi.mul_apply, sq]
  rw [MulAut.mul_apply, coe_exactNormalAut, coe_exactNormalAut, hid, hid, hQ, MulAut.conj_apply,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  change _ = rootDiagUnit Tag.D4 (fun j => a j ^ 2) * _ * (rootDiagUnit Tag.D4 (fun j => a j ^ 2))⁻¹
  rw [hsq]
  group

theorem eps_eq_zero [Finite K] (S : Sylow 3 (adjointGroup Tag.D4 K)) (c : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) {ε : ℕ} (hε : ε < 3) {k : ℕ} (hσ : σ ^ 3 ^ k = 1)
    (hfix : ∀ x ∈ (S : Subgroup (adjointGroup Tag.D4 K)),
      (MulAut.conj c * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) x = x) : ε = 0 := by
  by_cases h3 : ringChar K = 3
  · haveI : CharP K 3 := ringChar.eq_iff.1 h3
    exact eps_eq_zero_of_char_three S c a σ hε hfix
  · have := Fintype.ofFinite K
    obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
    have hK : Nat.card K % 3 ≠ 0 := by
      rw [Nat.card_eq_fintype_card, hn]
      intro h
      have hd : 3 ∣ ringChar K ^ (n : ℕ) := Nat.dvd_of_mod_eq_zero h
      exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.prime_three.dvd_of_dvd_pow hd)).symm
    rcases (by omega : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2) with h | h
    · exact eps_eq_zero_of_split (by omega) S c a σ hε hσ hfix
    · exact eps_eq_zero_of_nonsplit h S c a σ hε hfix

theorem d4NoTrialitySylowThree_holds : InputsMisc7e.D4NoTrialitySylowThree := by
  intro K _ _ S α ⟨k, hk⟩ hfix
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = coordinatePlusWitnessEquiv K
      (CFSG.HardMathSupport.Dickson.Bal207.D4Graph.isoAdj K).symm := ⟨_, rfl⟩
  have hαβ : α = MulAut.congr Φ (MulAut.congr Φ.symm α) := by
    refine MulEquiv.ext fun x => ?_
    simp [MulAut.congr_apply]
  have hβk : MulAut.congr Φ.symm α ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
  let S' : Sylow 3 (adjointGroup Tag.D4 K) := S.comapOfInjective Φ.toMonoidHom Φ.injective
    (by rw [MonoidHom.range_eq_top.2 Φ.surjective]; exact le_top)
  have hfix' : ∀ x ∈ (S' : Subgroup (adjointGroup Tag.D4 K)), MulAut.congr Φ.symm α x = x := by
    intro x hx
    have hx' : Φ x ∈ (S : Subgroup _) := hx
    have h := hfix _ hx'
    simp [MulAut.congr_apply, h]
  obtain ⟨c, a, σ, ε, hε, hσ, hβeq⟩ := exists_pow_normal_form (MulAut.congr Φ.symm α) k hβk
  have hε0 : ε = 0 := eps_eq_zero S' c a σ hε hσ (hβeq ▸ hfix')
  subst hε0
  rw [d4Graph_zero', mul_one, exactNormalAut_D4_eq_mul'] at hβeq
  have hα : α = MulAut.congr Φ (MulAut.conj c) * MulAut.congr Φ (exactNormalAut Tag.D4 K a 1 0) *
      MulAut.congr Φ (entrywiseAdjointAut Tag.D4 σ) := by
    rw [← map_mul, ← map_mul, mul_assoc, ← hβeq]
    exact hαβ
  have hsub := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  obtain ⟨κ, hκF, hκy, hκz, hyz⟩ := CFSG.RankThree.PartOne.KLC.swap_data_coordinate K
  refine smul_eq_of_decomp (fun b => by
      have := hsub (MulAction.mem_orbit _ b)
      simpa using this) hκF hκy hκz hyz (inner_normal _)
    (fun n hn => (mem_projectivePointFamilyAut_iff _ _).1 (projective_inner_le_pointFamilyAut _ hn))
    (ι := MulAut.congr Φ (MulAut.conj c)) (δ := MulAut.congr Φ (exactNormalAut Tag.D4 K a 1 0))
    (s := MulAut.congr Φ (entrywiseAdjointAut Tag.D4 σ)) (m := k) ⟨Φ c, (congr_conj Φ c).symm⟩ ?_ ?_
    ?_ hα hk
  · rw [← map_mul, normalAut_sq_eq_conj, congr_conj]
    exact ⟨_, rfl⟩
  · rw [hΦ]
    exact (mem_projectivePointFamilyAut_iff _ _).1 (projective_image_le_pointFamilyAut _
      (CFSG.HardMathSupport.Dickson.Bal207.D4Graph.congr_entrywiseAdjointAut_mem σ))
  · rw [← map_pow, ← entrywiseAdjointAut_pow, hσ, entrywiseAdjointAut_one, map_one]

end Assembly

theorem input7_10_1Rest2_holds :
    InputsMisc7e.Input7_10_1Rest2 :=
  ⟨e6InndiagSylowThree_holds, d4NoTrialitySylowThree_holds⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7f
