module

public import CFSG.LieType.Chevalley.DiagonalFieldActorData
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Ree

namespace EvenExceptionalActorCoverage

section IndexTwo

variable {G : Type*} [Group G]

theorem eq_top_or_index_eq_two_of_forall_mem_or_mul_inv_mem {H : Subgroup G} {γ : G}
    (h : ∀ α : G, α ∈ H ∨ α * γ⁻¹ ∈ H) : H = ⊤ ∨ H.index = 2 := by
  by_cases hγ : γ ∈ H
  · left
    refine eq_top_iff.mpr fun α _ => ?_
    rcases h α with hα | hα
    · exact hα
    · simpa using H.mul_mem hα hγ
  · right
    refine Subgroup.index_eq_two_iff.mpr ⟨γ⁻¹, fun b => ?_⟩
    by_cases hb : b ∈ H
    · refine Or.inr ⟨hb, fun h' => hγ ?_⟩
      have := H.mul_mem (H.inv_mem hb) h'
      simpa using this
    · exact Or.inl ⟨(h b).resolve_left hb, hb⟩

theorem normal_of_eq_top_or_index_eq_two {H : Subgroup G} (hH : H = ⊤ ∨ H.index = 2) :
    H.Normal := by
  rcases hH with rfl | h2
  · infer_instance
  · exact Subgroup.normal_of_index_eq_two h2

theorem index_le_two_of_eq_top_or_index_eq_two {H : Subgroup G} (hH : H = ⊤ ∨ H.index = 2) :
    H.index ≤ 2 := by
  rcases hH with rfl | h2
  · rw [Subgroup.index_top]
    omega
  · exact h2.le

theorem le_of_odd_card_of_eq_top_or_index_eq_two {H : Subgroup G} (hH : H = ⊤ ∨ H.index = 2)
    {X : Subgroup G} (hX : Odd (Nat.card X)) : X ≤ H := by
  rcases hH with rfl | h2
  · exact le_top
  intro x hx
  obtain ⟨k, hk⟩ := hX
  have h1 : x ^ Nat.card X = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := X) (x := ⟨x, hx⟩))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have hsq : x * x ∈ H := Subgroup.mul_self_mem_of_index_two h2 x
  have hx' : x = (x * x) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = Nat.card X + 1 by omega, pow_succ, h1, one_mul]
  rw [hx']
  exact H.pow_mem hsq _

end IndexTwo

section Membership

variable {τ : Tag} {K : Type} [Field K]

theorem mem_diagonalFieldActors_iff
    (φ : MulAut (adjointGroup τ K)) :
    φ ∈ diagonalFieldActors τ K ↔ ∃ g ∈ adjointGroup τ K, ∃ (a : Fin τ.rank → Kˣ)
      (δ : K ≃+* K), ∀ x : adjointGroup τ K, (φ x : ModGL τ K) = g * rootDiagUnit τ a *
        Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit τ a)⁻¹ * g⁻¹ :=
  (Chevalley_diagonal_field_actor_data.1 τ K).1 φ

theorem mem_diagonalFieldActors_of_inner_field
    {φ : MulAut (adjointGroup τ K)}
    (g : adjointGroup τ K) (σ : K ≃+* K)
    (h : ∀ x : adjointGroup τ K, (φ x : ModGL τ K) =
      (g : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) *
        (g : ModGL τ K)⁻¹) :
    φ ∈ diagonalFieldActors τ K :=
  (mem_diagonalFieldActors_iff φ).2 ⟨g, g.2, 1, σ, fun x => by
    rw [h x, rootDiagUnit_one]
    group⟩

variable {t : TwistTag} {σ : K ≃+* K}

theorem mem_fixedDiagonalFieldActors_iff
    (φ : MulAut (graphFixedRootGroup t K σ.toRingHom)) :
    φ ∈ fixedDiagonalFieldActors t K σ ↔ ∃ g ∈ graphFixedRootGroup t K σ.toRingHom,
      ∃ a : Fin t.tag.rank → Kˣ, (∀ i, a (t.perm i) = Units.map σ.toRingHom.toMonoidHom (a i)) ∧
        ∃ δ : K ≃+* K, δ * σ = σ * δ ∧ ∀ x : graphFixedRootGroup t K σ.toRingHom,
          (φ x : ModGL t.tag K) = g * rootDiagUnit t.tag a *
            Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit t.tag a)⁻¹ * g⁻¹ :=
  (Chevalley_diagonal_field_actor_data.2 t K σ).1 φ

end Membership

theorem exists_pow_two_pow_apply {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (δ : K ≃+* K) : ∃ j : ℕ, ∀ c, δ c = c ^ 2 ^ j := by
  obtain ⟨fr, hfr, hord, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality
    Nat.prime_two hf hK
  have hδ : δ ∈ Subgroup.zpowers fr := by rw [hzp]; exact Subgroup.mem_top δ
  have hfin : IsOfFinOrder fr := orderOf_pos_iff.mp (by rw [hord]; omega)
  obtain ⟨j, hj⟩ := (hfin.mem_powers_iff_mem_zpowers).mpr hδ
  exact ⟨j, fun c => by rw [← hj, ringAut_pow_apply_of_frobenius hfr j]⟩

theorem diagonalFieldActors_G2_eq_top
    {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) : diagonalFieldActors .G2 K = ⊤ := by
  refine eq_top_iff.mpr fun α _ => ?_
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ :=
    (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K
      hK).1 α
  exact mem_diagonalFieldActors_of_inner_field g σ hgσ

theorem diagonalFieldActors_E7_E8_eq_top
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) :
    diagonalFieldActors τ K = ⊤ := by
  refine eq_top_iff.mpr fun α _ => ?_
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ :=
    (even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ).1 α
  exact mem_diagonalFieldActors_of_inner_field g σ hgσ

theorem exactQ_E6_one {K : Type} [Field K] :
    exactQ .E6 K 1 = (diagramMap .E6 K : ModGL Tag.E6 K) :=
  pow_one _

theorem units_map_entrywiseHom_exactQ_E6_one {K : Type} [Field K] (σ : K ≃+* K) :
    Units.map (entrywiseHom σ.toRingHom) (exactQ .E6 K 1) = exactQ .E6 K 1 := by
  rw [exactQ_E6_one]
  exact units_map_entrywiseHom_diagramMap (t := TwistTag.E6) (K := K) σ.toRingHom

theorem coe_exactNormalAut_one_refl_one
    {K : Type} [Field K] (h : adjointGroup .E6 K) :
    (exactNormalAut .E6 K 1 (RingEquiv.refl K) 1 h : ModGL .E6 K) =
      exactQ .E6 K 1 * h * (exactQ .E6 K 1)⁻¹ := by
  rw [coe_exactNormalAut, rootDiagUnit_one, one_mul, inv_one, mul_one,
    show Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (h : ModGL .E6 K) = h from
      Units.ext (entrywise_id _)]

theorem diagonalFieldActors_E6_eq_top_or_index_eq_two
    {K : Type} [Field K] [Finite K] :
    diagonalFieldActors .E6 K = ⊤ ∨ (diagonalFieldActors .E6 K).index = 2 := by
  refine eq_top_or_index_eq_two_of_forall_mem_or_mul_inv_mem
    (γ := exactNormalAut .E6 K 1 (RingEquiv.refl K) 1) fun α => ?_
  obtain ⟨g, a, σ, ⟨ε, hε⟩, hα⟩ :=
    (ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K).2.2 α
  rcases ε with _ | _ | ε
  · left
    refine (mem_diagonalFieldActors_iff α).2 ⟨g, g.2, a, σ, fun x => ?_⟩
    rw [hα x, show exactQ .E6 K ((⟨0, hε⟩ : Fin (exactE .E6)) : ℕ) = 1 from exactQ_zero .E6 K]
    group
  · right
    refine (mem_diagonalFieldActors_iff _).2 ⟨g, g.2, a, σ, fun x => ?_⟩
    set y := (exactNormalAut .E6 K 1 (RingEquiv.refl K) 1)⁻¹ x with hy
    have hyx : (x : ModGL .E6 K) = exactQ .E6 K 1 * y * (exactQ .E6 K 1)⁻¹ := by
      rw [← coe_exactNormalAut_one_refl_one, hy, MulAut.apply_inv_self]
    have hy' : (y : ModGL .E6 K) = (exactQ .E6 K 1)⁻¹ * x * exactQ .E6 K 1 := by
      rw [hyx]
      group
    rw [MulAut.mul_apply, ← hy, hα y, hy', map_mul, map_mul, map_inv,
      units_map_entrywiseHom_exactQ_E6_one]
    group
  · simp [exactE] at hε

@[expose] def parityHom (f : ℕ) : Multiplicative (ZMod (2 * f)) →* Multiplicative (ZMod 2) :=
  (ZMod.castHom (dvd_mul_right 2 f) (ZMod 2)).toAddMonoidHom.toMultiplicative

theorem parityHom_ofAdd_natCast (f k : ℕ) :
    parityHom f (Multiplicative.ofAdd (k : ZMod (2 * f))) = Multiplicative.ofAdd (k : ZMod 2) := by
  simp [parityHom]

theorem parityHom_surjective (f : ℕ) : Function.Surjective (parityHom f) := fun y => by
  refine ⟨Multiplicative.ofAdd ((Multiplicative.toAdd y).val : ZMod (2 * f)), ?_⟩
  rw [parityHom_ofAdd_natCast, ZMod.natCast_zmod_val]
  rfl

theorem diagonalFieldActors_F4_index_eq_two
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) : (diagonalFieldActors ReeTag.F4.tag K).index = 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have h2 : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : CharP K ReeTag.F4.prime := h2
  obtain ⟨-, hnf, ⟨Θ, hΘ, hΘsurj, -⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨B, hB, -⟩, hrest⟩ :=
    G2_F4_root_character_diagonals_inner ReeTag.F4.tag (Or.inr rfl) K
  set ψ := (parityHom f).comp Θ with hψ
  have hfield : ∀ (δ : K ≃+* K) (j : ℕ), (∀ c, δ c = c ^ 2 ^ j) →
      exactNormalAut ReeTag.F4.tag K 1 δ 0 = ReeTag.F4.finiteExceptionalAut K ^ (2 * j) :=
    fun δ j hδ => by
      rw [finiteExceptionalAut_pow_two_mul (t := ReeTag.F4)]
      exact exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.F4 hδ
  have hcoe1 : ∀ (δ : K ≃+* K) (x : adjointGroup ReeTag.F4.tag K),
      (exactNormalAut ReeTag.F4.tag K 1 δ 0 x : ModGL ReeTag.F4.tag K) =
        Units.map (entrywiseHom δ.toRingHom) (x : ModGL ReeTag.F4.tag K) := fun δ x => by
    rw [coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one]
  have hker : diagonalFieldActors ReeTag.F4.tag K = ψ.ker := by
    ext α
    rw [MonoidHom.mem_ker]
    constructor
    · intro hα
      obtain ⟨g, hg, a, δ, hαx⟩ := (mem_diagonalFieldActors_iff α).1 hα
      obtain ⟨j, hj⟩ := exists_pow_two_pow_apply hf hK δ
      obtain ⟨hda, -⟩ := (hrest B hB a).2.2
      have he : α = MulAut.conj (⟨g, hg⟩ * ⟨rootDiagUnit ReeTag.F4.tag a, hda⟩ :
          adjointGroup ReeTag.F4.tag K) * ReeTag.F4.finiteExceptionalAut K ^ (2 * j) := by
        rw [← hfield δ j hj]
        refine MulEquiv.ext fun x => Subtype.ext ?_
        rw [hαx x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          hcoe1, Subgroup.coe_inv, Subgroup.coe_mul]
        simp only [mul_inv_rev, mul_assoc]
      rw [hψ, MonoidHom.comp_apply, hΘ _ _ _ he, parityHom_ofAdd_natCast, Nat.cast_mul,
        ZMod.natCast_self, zero_mul, ofAdd_zero]
    · intro hα
      obtain ⟨⟨g, k⟩, hgk, -⟩ := hnf α
      dsimp only at hgk
      rw [hψ, MonoidHom.comp_apply, hΘ α g k hgk, parityHom_ofAdd_natCast] at hα
      have hk : 2 ∣ (k : ℕ) := by
        have h0 : ((k : ℕ) : ZMod 2) = 0 := by
          have := congrArg Multiplicative.toAdd hα
          simpa using this
        exact (ZMod.natCast_eq_zero_iff _ _).mp h0
      obtain ⟨fr, hfr, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
      have hk2 : (k : ℕ) = 2 * ((k : ℕ) / 2) := by omega
      have hδ := ringAut_pow_apply_of_frobenius hfr ((k : ℕ) / 2)
      have hα' : α = MulAut.conj g * exactNormalAut ReeTag.F4.tag K 1 (fr ^ ((k : ℕ) / 2)) 0 := by
        rw [hgk, hfield _ _ hδ, ← hk2]
      refine mem_diagonalFieldActors_of_inner_field g (fr ^ ((k : ℕ) / 2)) fun x => ?_
      rw [hα', MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, hcoe1,
        Subgroup.coe_inv]
  have hψs : Function.Surjective ψ := by
    rw [hψ, MonoidHom.coe_comp]
    exact (parityHom_surjective f).comp hΘsurj
  rw [hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hψs, Subgroup.card_top]
  simp [Nat.card_eq_fintype_card]

theorem fixedDiagonalFieldActors_D4_eq_top
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    fixedDiagonalFieldActors .D4 K σ = ⊤ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨hfa, hnf, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  refine eq_top_iff.mpr fun α _ => ?_
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hnf α
  refine (mem_fixedDiagonalFieldActors_iff α).2 ⟨g, g.2, 1, fun _ => (map_one _).symm, δ,
    ringAut_mul_comm K δ σ, fun x => ?_⟩
  rw [hgδ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, hfa,
    rootDiagUnit_one, Subgroup.coe_inv]
  group

theorem fixedDiagonalFieldActors_E6_eq_top
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    fixedDiagonalFieldActors .E6 K σ = ⊤ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨-, -, -, -, -, hΔ, hfa, hnf, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  refine eq_top_iff.mpr fun α _ => ?_
  obtain ⟨g, u, δ, rfl⟩ := hnf α
  refine (mem_fixedDiagonalFieldActors_iff _).2 ⟨g, g.2,
    compatDiag TwistTag.E6 σ.toRingHom u, fun i => compatDiag_perm u i, δ,
    ringAut_mul_comm K δ σ, fun x => ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    hΔ, hfa, Subgroup.coe_inv]
  group

end EvenExceptionalActorCoverage

open EvenExceptionalActorCoverage

theorem even_exceptional_diagonal_field_actor_coverage :
    (∀ (τ : Tag) (f : ℕ) (K : Type) [Field K], 1 ≤ f → Nat.card K = 2 ^ f →
      (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ (τ = .G2 ∧ 2 ≤ f)) →
      (diagonalFieldActors τ K).Normal ∧ (diagonalFieldActors τ K).index ≤ 2 ∧
      ((τ = .G2 ∨ τ = .E7 ∨ τ = .E8) → diagonalFieldActors τ K = ⊤) ∧
      (τ = .F4 → (diagonalFieldActors τ K).index = 2) ∧
      ∀ X : Subgroup (MulAut (adjointGroup τ K)), Odd (Nat.card X) →
        X ≤ diagonalFieldActors τ K) ∧
    ∀ (t : TwistTag) (f : ℕ) (K : Type) [Field K] (σ : K ≃+* K), 1 ≤ f →
      Nat.card K = (2 ^ f) ^ t.order → (∀ c, σ c = c ^ 2 ^ f) →
      fixedDiagonalFieldActors t K σ = ⊤ ∧
      ∀ X : Subgroup (MulAut (graphFixedRootGroup t K σ.toRingHom)), Odd (Nat.card X) →
        X ≤ fixedDiagonalFieldActors t K σ := by
  refine ⟨fun τ f K _ hf hK hτ => ?_, fun t f K _ σ hf hK hσ => ?_⟩
  · have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have htop : (τ = .G2 ∨ τ = .E7 ∨ τ = .E8) → diagonalFieldActors τ K = ⊤ := by
      rintro (rfl | rfl | rfl)
      · rcases hτ with h | h | h | h | ⟨-, h2⟩
        all_goals first | exact absurd h (by decide) | exact diagonalFieldActors_G2_eq_top h2 hK
      · exact diagonalFieldActors_E7_E8_eq_top hf hK (Or.inl rfl)
      · exact diagonalFieldActors_E7_E8_eq_top hf hK (Or.inr rfl)
    have hF4 : τ = .F4 → (diagonalFieldActors τ K).index = 2 := by
      rintro rfl
      exact diagonalFieldActors_F4_index_eq_two hf hK
    have hH : diagonalFieldActors τ K = ⊤ ∨ (diagonalFieldActors τ K).index = 2 := by
      rcases hτ with rfl | rfl | rfl | rfl | ⟨rfl, -⟩
      · exact Or.inr (hF4 rfl)
      · exact diagonalFieldActors_E6_eq_top_or_index_eq_two
      · exact Or.inl (htop (Or.inr (Or.inl rfl)))
      · exact Or.inl (htop (Or.inr (Or.inr rfl)))
      · exact Or.inl (htop (Or.inl rfl))
    exact ⟨normal_of_eq_top_or_index_eq_two hH, index_le_two_of_eq_top_or_index_eq_two hH,
      htop, hF4, fun X hX => le_of_odd_card_of_eq_top_or_index_eq_two hH hX⟩
  · have htop : fixedDiagonalFieldActors t K σ = ⊤ := by
      cases t
      · exact fixedDiagonalFieldActors_E6_eq_top hf hK σ hσ
      · exact fixedDiagonalFieldActors_D4_eq_top hf hK σ hσ
    exact ⟨htop, fun X _ => htop ▸ le_top⟩

end CFSG.LieType.Chevalley
