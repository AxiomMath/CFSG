module

public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

section Counting

variable {G Q : Type*} [Group G] [Group Q]

theorem card_eq_card_subgroupOf_ker_mul_card_map (ψ : G →* Q) (B : Subgroup G) :
    Nat.card B = Nat.card (ψ.ker.subgroupOf B) * Nat.card (B.map ψ) := by
  have h := Subgroup.card_mul_index (ψ.comp B.subtype).ker
  rw [Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype] at h
  exact h.symm

theorem card_dvd_two_of_isCyclic [IsCyclic Q] {S : Subgroup Q} (hS : ∀ y ∈ S, y ^ 2 = 1) :
    Nat.card S ∣ 2 := by
  rw [← IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one fun y => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hS y y.2)

theorem card_eq_one_of_isCyclic_of_odd [IsCyclic Q] (hQ : Odd (Nat.card Q)) {S : Subgroup Q}
    (hS : ∀ y ∈ S, y ^ 2 = 1) : Nat.card S = 1 := by
  have h : Nat.card S ∣ Nat.gcd 2 (Nat.card Q) :=
    Nat.dvd_gcd (card_dvd_two_of_isCyclic hS) (Subgroup.card_subgroup_dvd_card S)
  rw [Nat.coprime_two_left.2 hQ] at h
  exact Nat.dvd_one.1 h

theorem map_pow_two_eq_one (ψ : G →* Q) {B : Subgroup G} (hB : ∀ x ∈ B, x ^ 2 = 1) :
    ∀ y ∈ B.map ψ, y ^ 2 = 1 := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pow, hB x hx, map_one]

theorem card_subgroupOf_ker_eq_one (ψ : G →* Q) (hker : ∀ x ∈ ψ.ker, x ^ 3 = 1)
    {B : Subgroup G} (hB : ∀ x ∈ B, x ^ 2 = 1) : Nat.card (ψ.ker.subgroupOf B) = 1 := by
  have hbot : ψ.ker.subgroupOf B = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => Subtype.ext ?_
    have h2 := hB x x.2
    have h3 := hker x hx
    rw [Subgroup.coe_one, show (x : G) = (x : G) ^ 3 * ((x : G) ^ 2)⁻¹ by group, h2, h3,
      inv_one, mul_one]
  rw [hbot, Subgroup.card_bot]

theorem card_subgroupOf_ker_le (ψ : G →* Q) [Finite ψ.ker] (B : Subgroup G) :
    Nat.card (ψ.ker.subgroupOf B) ≤ Nat.card ψ.ker :=
  Nat.card_le_card_of_injective (fun x => (⟨x.1.1, x.2⟩ : ψ.ker)) fun _ _ h =>
    Subtype.ext (Subtype.ext (Subtype.mk.inj h))

theorem card_le_two_of_ker_cube [IsCyclic Q] (ψ : G →* Q) (hker : ∀ x ∈ ψ.ker, x ^ 3 = 1)
    {B : Subgroup G} (hB : ∀ x ∈ B, x ^ 2 = 1) : Nat.card B ≤ 2 := by
  rw [card_eq_card_subgroupOf_ker_mul_card_map ψ B, card_subgroupOf_ker_eq_one ψ hker hB,
    one_mul]
  exact Nat.le_of_dvd two_pos (card_dvd_two_of_isCyclic (map_pow_two_eq_one ψ hB))

theorem card_le_of_prod {A E : Type*} [Group A] [Group E] [IsCyclic A] [Finite E]
    {S : Subgroup (A × E)} (hS : ∀ y ∈ S, y ^ 2 = 1) :
    Nat.card S ≤ 2 * Nat.card E ∧ (Odd (Nat.card A) → Nat.card S ≤ Nat.card E) := by
  have hc := card_eq_card_subgroupOf_ker_mul_card_map (MonoidHom.fst A E) S
  have hk : Nat.card ((MonoidHom.fst A E).ker.subgroupOf S) ≤ Nat.card E := by
    refine Nat.card_le_card_of_injective (fun x => ((x : S) : A × E).2) fun x y hxy => ?_
    have hx : ((x : S) : A × E).1 = 1 := x.2
    have hy : ((y : S) : A × E).1 = 1 := y.2
    exact Subtype.ext (Subtype.ext (Prod.ext (hx.trans hy.symm) hxy))
  have hm := map_pow_two_eq_one (MonoidHom.fst A E) hS
  refine ⟨?_, fun hodd => ?_⟩
  · rw [hc, mul_comm 2]
    exact Nat.mul_le_mul hk (Nat.le_of_dvd two_pos (card_dvd_two_of_isCyclic hm))
  · rw [hc, card_eq_one_of_isCyclic_of_odd hodd hm, mul_one]
    exact hk

theorem card_le_of_prod_bound {A E : Type*} [Group A] [Group E] [IsCyclic A] [Finite E]
    (Φ : G →* A × E) {B : Subgroup G} (hB : ∀ x ∈ B, x ^ 2 = 1) :
    Nat.card B ≤ Nat.card (Φ.ker.subgroupOf B) * (2 * Nat.card E) ∧
      (Odd (Nat.card A) → Nat.card B ≤ Nat.card (Φ.ker.subgroupOf B) * Nat.card E) := by
  obtain ⟨h1, h2⟩ := card_le_of_prod (map_pow_two_eq_one Φ hB)
  rw [card_eq_card_subgroupOf_ker_mul_card_map Φ B]
  exact ⟨Nat.mul_le_mul_left _ h1, fun hodd => Nat.mul_le_mul_left _ (h2 hodd)⟩

theorem exists_outer_subgroup_transport {H : Type*} [Group H] (e : G ≃* H)
    (B : Subgroup (Outer G)) (hB : ∀ x ∈ B, x ^ 2 = 1) :
    ∃ B' : Subgroup (Outer H), Nat.card B' = Nat.card B ∧ ∀ x ∈ B', x ^ 2 = 1 := by
  set E := CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
  exact ⟨B.map E.toMonoidHom, Subgroup.card_map_of_injective E.injective,
    map_pow_two_eq_one E.toMonoidHom hB⟩

end Counting

section Outer

theorem card_le_two_of_ker_eq_inner {C Q : Type*} [Group C] [Group Q] [IsCyclic Q]
    (Θ : MulAut C →* Q) (hker : Θ.ker = inner C) {B : Subgroup (Outer C)}
    (hB : ∀ x ∈ B, x ^ 2 = 1) : Nat.card B ≤ 2 := by
  refine card_le_two_of_ker_cube (QuotientGroup.lift (inner C) Θ hker.ge) (fun x hx => ?_) hB
  rw [QuotientGroup.ker_lift, hker, QuotientGroup.map_mk'_self, Subgroup.mem_bot] at hx
  rw [hx, one_pow]

theorem card_le_two_of_ker_cube_quotient {C Q : Type*} [Group C] [Group Q] [IsCyclic Q]
    (Θ : MulAut C →* Q) {L : Subgroup (MulAut C)} (hker : Θ.ker = L) (hle : inner C ≤ L)
    (hcube : ∀ a : L ⧸ (inner C).subgroupOf L, a ^ 3 = 1) {B : Subgroup (Outer C)}
    (hB : ∀ x ∈ B, x ^ 2 = 1) : Nat.card B ≤ 2 := by
  refine card_le_two_of_ker_cube (QuotientGroup.lift (inner C) Θ (hker ▸ hle)) (fun x hx => ?_)
    hB
  rw [QuotientGroup.ker_lift, hker] at hx
  obtain ⟨α, hα, rfl⟩ := hx
  have h3 := hcube (QuotientGroup.mk ⟨α, hα⟩)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow] at h3
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact h3

variable {K : Type} [Field K]

theorem card_le_two_of_outer_odd_F4_G2
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {τ : Tag} (hτ : τ = .F4 ∨ (τ = .G2 ∧ p ≠ 3))
    {B : Subgroup (Outer (adjointGroup τ K))} (hB : ∀ x ∈ B, x ^ 2 = 1) : Nat.card B ≤ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hp K hK).2
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hK τ hτ
  exact card_le_two_of_ker_eq_inner Θ hker hB

theorem card_le_two_of_outer_G2_three
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    {B : Subgroup (Outer (adjointGroup .G2 K))} (hB : ∀ x ∈ B, x ^ 2 = 1) : Nat.card B ≤ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf hK
  have : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := this
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  exact card_le_two_of_ker_eq_inner Θ hker hB

theorem card_le_two_of_outer_odd_triality
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {B : Subgroup (Outer (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (hB : ∀ x ∈ B, x ^ 2 = 1) : Nat.card B ≤ 2 := by
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  exact card_le_two_of_ker_eq_inner Θ hker hB

theorem card_le_two_of_outer_twistedE6
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {B : Subgroup (Outer (twistedE6RootGroup K σ))} (hB : ∀ x ∈ B, x ^ 2 = 1) :
    Nat.card B ≤ 2 := by
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hp K hK').2
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  exact card_le_two_of_ker_cube_quotient Θ hker le_sup_left hcube hB

theorem card_le_of_outer_E
    {p f : ℕ} (hp : p.Prime) (hK : Nat.card K = p ^ f) {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {B : Subgroup (Outer (adjointGroup τ K))}
    (hB : ∀ x ∈ B, x ^ 2 = 1) :
    (τ = .E6 ∨ τ = .E7 → Nat.card B ≤ 4 ∧ (Odd f → Nat.card B ≤ 2)) ∧
      (τ = .E8 → Nat.card B ≤ 2) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  obtain ⟨hcardA, hcyc⟩ := card_ringAut_and_isCyclic hp K hK
  have : NeZero (exactE τ) := ⟨(exactE_pos τ).ne'⟩
  obtain ⟨Φ, -, -, hdvd⟩ := exists_outer_hom_E (K := K) hτ
  have hE : Nat.card (Multiplicative (ZMod (exactE τ))) = exactE τ := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  obtain ⟨h1, h2⟩ := card_le_of_prod_bound Φ hB
  rw [hE] at h1 h2
  rw [hcardA] at h2
  have hker0 : Nat.card Φ.ker ≠ 0 := fun h0 => by
    rw [h0, zero_dvd_iff, Int.natAbs_eq_zero] at hdvd
    rcases hτ with rfl | rfl | rfl
    · exact absurd hdvd (by rw [det_cartan_E6]; norm_num)
    · exact absurd hdvd (by rw [det_cartan_E7]; norm_num)
    · exact absurd hdvd (by rw [det_cartan_E8]; norm_num)
  have : Finite Φ.ker := Nat.finite_of_card_ne_zero hker0
  have hm := card_subgroupOf_ker_le Φ B
  refine ⟨fun h67 => ?_, fun h8 => ?_⟩
  · rcases h67 with rfl | rfl
    ·
      rw [det_cartan_E6] at hdvd
      have hcube : ∀ x ∈ Φ.ker, x ^ 3 = 1 := fun x hx => by
        obtain ⟨c, hc⟩ := hdvd
        have h : (⟨x, hx⟩ : Φ.ker) ^ 3 = 1 := by
          rw [show (3 : ℕ) = Nat.card Φ.ker * c from hc, pow_mul, pow_card_eq_one', one_pow]
        simpa using congrArg Subtype.val h
      rw [card_subgroupOf_ker_eq_one Φ hcube hB] at h1 h2
      exact ⟨by simpa [exactE] using h1, fun hodd => by simpa [exactE] using h2 hodd⟩
    ·
      rw [det_cartan_E7] at hdvd
      have hk : Nat.card Φ.ker ≤ 2 := Nat.le_of_dvd two_pos (by simpa using hdvd)
      refine ⟨h1.trans ?_, fun hodd => (h2 hodd).trans ?_⟩
      · change _ * (2 * 1) ≤ 4
        omega
      · change _ * 1 ≤ 2
        omega
  · subst h8
    rw [det_cartan_E8] at hdvd
    have hk : Nat.card Φ.ker ≤ 1 := Nat.le_of_dvd one_pos (by simpa using hdvd)
    refine h1.trans ?_
    change _ * (2 * 1) ≤ 2
    omega

end Outer

theorem exists_mulEquiv_graphFixedRootGroup_card
    {G : Type} [Group G] (t : TwistTag) {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (h : TwistedChevalleyModel G t (p ^ f)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (p ^ f) ^ t.order ∧
      (∀ c, σ c = c ^ (p ^ f)) ∧ Nonempty (G ≃* graphFixedRootGroup t K σ.toRingHom) := by
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := h
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields t hp hf K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  have hperf := (finite_fixed_root_group_perfect t hp hf K hcard σ'.toRingHom hσ).2.2.1
  obtain ⟨e'⟩ :=
    nonempty_derivedCentralQuotient_equiv hperf (exceptional_fixed_center_trivial t K σ')
  exact ⟨K, inferInstance, inferInstance, σ', hcard, hσ', ⟨e.trans e'⟩⟩

theorem odd_exceptional_elementary_outer_two_rank
    (T : Type) [Group T] (t : StatedLieTag)
    (p f : ℕ) (hT : ChevalleyExceptionalModel T t p f) (hp : Odd p) (B : Subgroup (Outer T))
    (hB : ∀ x ∈ B, x ^ 2 = 1) (d : ℕ) (hd : Nat.card B = 2 ^ d) :
    ((t = .G2 ∨ t = .F4 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4) → d ≤ 1) ∧
    ((t = .E6 ∨ t = .E7) → d ≤ 2 ∧ (Odd f → d ≤ 1)) ∧
    (2 ≤ d → (t = .E6 ∨ t = .E7) ∧ Even f ∧ d = 2) := by
  have hd1 : Nat.card B ≤ 2 → d ≤ 1 := fun h => by
    by_contra hcon
    have : 2 ^ 2 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hd2 : Nat.card B ≤ 4 → d ≤ 2 := fun h => by
    by_contra hcon
    have : 2 ^ 3 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨⟨hpp, hf, -⟩, hm⟩ := hT
  have hp2 : p ≠ 2 := fun h => by
    subst h
    exact absurd hp (by decide)
  have key : ((t = .G2 ∨ t = .F4 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4) →
      Nat.card B ≤ 2) ∧ ((t = .E6 ∨ t = .E7) → Nat.card B ≤ 4 ∧ (Odd f → Nat.card B ≤ 2)) := by
    cases t
    case G2 =>
      have hm' : UntwistedChevalleyModel T .G2 (p ^ f) := hm
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm'
      obtain ⟨B', hB'c, hB'⟩ := exists_outer_subgroup_transport e B hB
      have h2 : Nat.card B' ≤ 2 := by
        by_cases h3 : p = 3
        · subst h3
          exact card_le_two_of_outer_G2_three hf hK hB'
        · exact card_le_two_of_outer_odd_F4_G2 hpp hp2 hf hK (Or.inr ⟨rfl, h3⟩) hB'
      refine ⟨fun _ => hB'c ▸ h2, ?_⟩
      rintro (h | h) <;> exact absurd h (by decide)
    case F4 =>
      have hm' : UntwistedChevalleyModel T .F4 (p ^ f) := hm
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm'
      obtain ⟨B', hB'c, hB'⟩ := exists_outer_subgroup_transport e B hB
      refine ⟨fun _ => hB'c ▸ card_le_two_of_outer_odd_F4_G2 hpp hp2 hf hK (Or.inl rfl) hB', ?_⟩
      rintro (h | h) <;> exact absurd h (by decide)
    case E6 =>
      have hm' : UntwistedChevalleyModel T .E6 (p ^ f) := hm
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm'
      obtain ⟨B', hB'c, hB'⟩ := exists_outer_subgroup_transport e B hB
      obtain ⟨h67, -⟩ := card_le_of_outer_E hpp hK (Or.inl rfl) hB'
      refine ⟨?_, fun _ => hB'c ▸ h67 (Or.inl rfl)⟩
      rintro (h | h | h | h | h) <;> exact absurd h (by decide)
    case E7 =>
      have hm' : UntwistedChevalleyModel T .E7 (p ^ f) := hm
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hm'
      obtain ⟨B', hB'c, hB'⟩ := exists_outer_subgroup_transport e B hB
      obtain ⟨h67, -⟩ := card_le_of_outer_E hpp hK (Or.inr (Or.inl rfl)) hB'
      refine ⟨?_, fun _ => hB'c ▸ h67 (Or.inr rfl)⟩
      rintro (h | h | h | h | h) <;> exact absurd h (by decide)
    case E8 =>
      have hm' : UntwistedChevalleyModel T .E8 (p ^ f) := hm
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hm'
      obtain ⟨B', hB'c, hB'⟩ := exists_outer_subgroup_transport e B hB
      obtain ⟨-, h8⟩ := card_le_of_outer_E hpp hK (Or.inr (Or.inr rfl)) hB'
      refine ⟨fun _ => hB'c ▸ h8 rfl, ?_⟩
      rintro (h | h) <;> exact absurd h (by decide)
    case twistedE6 =>
      have hm' : TwistedChevalleyModel T .E6 (p ^ f) := hm
      obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hpp hf hm'
      obtain ⟨B', hB'c, hB'⟩ := exists_outer_subgroup_transport e B hB
      refine ⟨fun _ => hB'c ▸ card_le_two_of_outer_twistedE6 hpp hf hK σ hσ hB', ?_⟩
      rintro (h | h) <;> exact absurd h (by decide)
    case trialityD4 =>
      have hm' : TwistedChevalleyModel T .D4 (p ^ f) := hm
      obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hpp hf hm'
      obtain ⟨B', hB'c, hB'⟩ := exists_outer_subgroup_transport e B hB
      refine ⟨fun _ => hB'c ▸ card_le_two_of_outer_odd_triality hpp hp2 hf hK σ hσ hB', ?_⟩
      rintro (h | h) <;> exact absurd h (by decide)
    all_goals exact (hm : False).elim
  obtain ⟨k1, k2⟩ := key
  have h1 : (t = .G2 ∨ t = .F4 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4) → d ≤ 1 :=
    fun ht => hd1 (k1 ht)
  have h2 : (t = .E6 ∨ t = .E7) → d ≤ 2 ∧ (Odd f → d ≤ 1) :=
    fun ht => ⟨hd2 (k2 ht).1, fun hodd => hd1 ((k2 ht).2 hodd)⟩
  refine ⟨h1, h2, fun hd' => ?_⟩
  have ht : t = .E6 ∨ t = .E7 := by
    by_contra hcon
    have : t = .G2 ∨ t = .F4 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4 := by
      cases t <;> simp_all
    have := h1 this
    omega
  obtain ⟨hle2, hodd⟩ := h2 ht
  refine ⟨ht, ?_, by omega⟩
  rcases Nat.even_or_odd f with hev | hodd'
  · exact hev
  · have := hodd hodd'
    omega

end CFSG.LieType.Chevalley
