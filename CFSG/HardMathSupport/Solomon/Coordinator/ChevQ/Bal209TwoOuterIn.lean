module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoIn
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodUntwist

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Coordinator

namespace Bal209TwoOuterInAux

section Abstract

theorem mem_of_coprime_of_exponent_three {A : Type*} [Group A] {N H : Subgroup A}
    [N.Normal] (h3 : ∀ a : ↥H ⧸ N.subgroupOf H, a ^ 3 = 1) {α : A} (hαH : α ∈ H)
    (hα3 : Nat.Coprime 3 (orderOf α)) : α ∈ N := by
  set a : ↥H ⧸ N.subgroupOf H := QuotientGroup.mk ⟨α, hαH⟩ with ha
  have ha3 := h3 a
  have haord : a ^ orderOf α = 1 := by
    have h1 : (⟨α, hαH⟩ : ↥H) ^ orderOf α = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [ha, ← QuotientGroup.mk_pow, h1]
    rfl
  have ha1 : a = 1 := by
    have h := pow_gcd_eq_one.2 ⟨ha3, haord⟩
    rwa [Nat.Coprime.gcd_eq_one hα3, pow_one] at h
  have h2 := (QuotientGroup.eq_one_iff _).1 ha1
  exact Subgroup.mem_subgroupOf.1 h2

theorem core_eq_bot_of_commute_mem {A : Type*} [Group A] [Finite A] {I N : Subgroup A} [I.Normal]
    (h3 : ∀ a : ↥N ⧸ I.subgroupOf N, a ^ 3 = 1) {δ : A}
    (hcomm : ∀ x : A, x * δ = δ * x → x ∈ N)
    (hcore : GLAPPrimeCoreOf 3 (I ⊓ Subgroup.centralizer ({δ} : Set A)) = ⊥)
    {H : Subgroup A} (hH : I ≤ H) :
    GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({δ} : Set A)) = ⊥ := by
  set X : Subgroup A := H ⊓ Subgroup.centralizer ({δ} : Set A) with hX
  set Q := GLAPPrimeCoreOf 3 X with hQ
  have hQX : Q ≤ X := GLAPPrimeCoreOf_le X
  have hcop : Nat.Coprime 3 (Nat.card Q) := coprime_card_GLAPPrimeCoreOf Nat.prime_three X
  have hQI : Q ≤ I ⊓ Subgroup.centralizer ({δ} : Set A) := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({δ} : Set A) := (hQX hx).2
    have hxN : x ∈ N := by
      refine hcomm x ?_
      exact Subgroup.mem_centralizer_singleton_iff.1 hxC
    have hord : Nat.Coprime 3 (orderOf x) := by
      have h1 : orderOf (⟨x, hx⟩ : Q) ∣ Nat.card Q := orderOf_dvd_natCard _
      have h2 : orderOf x = orderOf (⟨x, hx⟩ : Q) := (Subgroup.orderOf_mk x hx).symm
      rw [h2]
      exact hcop.coprime_dvd_right h1
    exact ⟨mem_of_coprime_of_exponent_three h3 hxN hord, hxC⟩
  have hle : Q ≤ GLAPPrimeCoreOf 3 (I ⊓ Subgroup.centralizer ({δ} : Set A)) := by
    refine le_GLAPPrimeCoreOf_of_normal hQI ?_ hcop
    intro g hg y hy
    exact GLAPPrimeCoreOf_conj_mem g (Subgroup.mem_inf.2 ⟨hH hg.1, hg.2⟩) y hy
  rw [hcore] at hle
  exact le_bot_iff.1 hle

theorem conj_commute_iff {G : Type*} [Group G] (g a b : G) :
    (g⁻¹ * a * g) * (g⁻¹ * b * g) = (g⁻¹ * b * g) * (g⁻¹ * a * g) ↔ a * b = b * a := by
  have h1 : (g⁻¹ * a * g) * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
  have h2 : (g⁻¹ * b * g) * (g⁻¹ * a * g) = g⁻¹ * (b * a) * g := by group
  rw [h1, h2, mul_right_cancel_iff, mul_left_cancel_iff]

theorem core_centralizer_of_conj {G : Type*} [Group G] {Γ : Subgroup G} [Finite Γ]
    (φ : ↥Γ ≃* ↥Γ) {m' m m₁ : G} (hφ : ∀ g : ↥Γ, ((φ g : ↥Γ) : G) = m' * g * m'⁻¹)
    (hm : m₁ = m' * m * m'⁻¹)
    (h : GLAPPrimeCoreOf 3 ((Subgroup.centralizer ({m₁} : Set G)).subgroupOf Γ) = ⊥) :
    GLAPPrimeCoreOf 3 ((Subgroup.centralizer ({m} : Set G)).subgroupOf Γ) = ⊥ := by
  set C : Subgroup ↥Γ := (Subgroup.centralizer ({m} : Set G)).subgroupOf Γ with hC
  set C₁ : Subgroup ↥Γ := (Subgroup.centralizer ({m₁} : Set G)).subgroupOf Γ with hC₁
  have hmap : C.map φ.toMonoidHom = C₁ := by
    ext y
    obtain ⟨g, rfl⟩ := φ.surjective y
    constructor
    · rintro ⟨g', hg', hgg'⟩
      have : g' = g := φ.injective hgg'
      subst this
      have hg'' : g' ∈ C := hg'
      rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hg''
      show φ g' ∈ C₁
      rw [hC₁, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      show ((φ g' : ↥Γ) : G) * m₁ = m₁ * ((φ g' : ↥Γ) : G)
      rw [hφ, hm]
      calc m' * g' * m'⁻¹ * (m' * m * m'⁻¹) = m' * (g' * m) * m'⁻¹ := by group
        _ = m' * (m * g') * m'⁻¹ := by rw [show (g' : G) * m = m * g' from hg'']
        _ = _ := by group
    · intro hy
      refine ⟨g, ?_, rfl⟩
      have hy' : φ g ∈ C₁ := hy
      rw [hC₁, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hy'
      show g ∈ C
      rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      rw [hφ, hm] at hy'
      have h2 : m' * (g * m) * m'⁻¹ = m' * (m * g) * m'⁻¹ := by
        calc m' * (g * m) * m'⁻¹ = m' * g * m'⁻¹ * (m' * m * m'⁻¹) := by group
          _ = m' * m * m'⁻¹ * (m' * g * m'⁻¹) := hy'
          _ = _ := by group
      have h3 : (g : G) * m = m * g := mul_left_cancel (mul_right_cancel h2)
      exact h3
  have h1 := map_glaPPrimeCoreOf_of_injective 3 φ.toMonoidHom φ.injective C
  rw [hmap, h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 h1

end Abstract

section TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial


variable {K : Type} [Field K] [Finite K]

theorem unit_pow_three_of_card_four (hK : Nat.card K = 4) (c : K) (hc : c ≠ 0) : c ^ 3 = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one c hc
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem orbitUnitsMap_eq_inv (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    (v : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    orbitUnitsMap σ.toRingHom (ringEquiv_comm_of_finite σ σ) v = v⁻¹ := by
  funext a
  refine Units.ext (Subtype.ext ?_)
  have hv0 : ((v a : orbitField TwistTag.E6 K σ.toRingHom a) : K) ≠ 0 := fun h =>
    (v a).ne_zero (Subtype.ext h)
  have h3 := unit_pow_three_of_card_four hK _ hv0
  change σ ((v a : orbitField TwistTag.E6 K σ.toRingHom a) : K) = _
  rw [hσ, Pi.inv_apply, Units.val_inv_eq_inv_val, Subfield.coe_inv]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ]
  exact h3

theorem ringAut_facts_of_card_four (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2) :
    σ ≠ 1 ∧ σ ^ 2 = 1 ∧ ∀ δ : K ≃+* K, δ = 1 ∨ δ = σ := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨σ', hσ', hord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two le_rfl K hK'
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]; norm_num
  rw [hσσ'] at hord
  have hσ1 : σ ≠ 1 := fun h => by rw [h, orderOf_one] at hord; exact absurd hord (by decide)
  have hσ2 : σ ^ 2 = 1 := by rw [← pow_orderOf_eq_one σ, hord]; rfl
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic Nat.prime_two K hK2
  refine ⟨hσ1, hσ2, fun δ => ?_⟩
  have hδ2 : δ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := RingAut K) (x := δ)
    rwa [hcard] at this
  exact eq_one_or_eq_of_sq_eq_one Nat.prime_two hK2 hσ1 hσ2 hδ2

theorem sq_eq_one_of_conj_inv {Q : Type*} [Group Q] {a b s : Q} (hab : a * b = b * a)
    (hsb : s * b = b⁻¹ * s) (hcomm : (a * s) * b = b * (a * s)) : b ^ 2 = 1 := by
  have h1 : a * b⁻¹ * s = b * a * s := by
    calc a * b⁻¹ * s = a * (b⁻¹ * s) := mul_assoc _ _ _
      _ = a * (s * b) := by rw [hsb]
      _ = (a * s) * b := (mul_assoc _ _ _).symm
      _ = b * (a * s) := hcomm
      _ = b * a * s := (mul_assoc _ _ _).symm
  have h2 : a * b⁻¹ = b * a := mul_right_cancel h1
  have h3 : a = b * b * a := by
    calc a = a * b⁻¹ * b := by group
      _ = b * a * b := by rw [h2]
      _ = b * (a * b) := mul_assoc _ _ _
      _ = b * (b * a) := by rw [hab]
      _ = b * b * a := (mul_assoc _ _ _).symm
  calc b ^ 2 = b * b := sq b
    _ = (b * b * a) * a⁻¹ := by group
    _ = a * a⁻¹ := by rw [← h3]
    _ = 1 := mul_inv_cancel a

theorem outer_core_of_inner_core (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {δ : MulAut (twistedE6RootGroup K σ)} (hδ3 : δ ^ 3 = 1) (hδ : δ ∉ twistedE6Inn K σ)
    (hcore : GLAPPrimeCoreOf 3 (twistedE6Inn K σ ⊓
      Subgroup.centralizer ({δ} : Set (MulAut (twistedE6RootGroup K σ)))) = ⊥)
    {H : Subgroup (MulAut (twistedE6RootGroup K σ))} (hH : twistedE6Inn K σ ≤ H) :
    GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({δ} : Set (MulAut (twistedE6RootGroup K σ)))) =
      ⊥ := by
  classical
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  obtain ⟨hσ1, hσsq, hRA⟩ := ringAut_facts_of_card_four hK σ hσ
  obtain ⟨-, -, -, -, -, hcd, hfield, hnf, ⟨Θ, hΘ, -, hker, -, hq3, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two le_rfl K hK2 σ hσ2
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  refine core_eq_bot_of_commute_mem (I := twistedE6Inn K σ)
    (N := twistedE6Inn K σ ⊔ twistedE6Diag K σ) hq3 ?_ hcore hH
  intro x hxδ
  by_contra hxN
  have hΘx : Θ x ≠ 1 := fun h => hxN (hker ▸ MonoidHom.mem_ker.2 h)
  have hΘxσ : Θ x = σ := (hRA (Θ x)).resolve_left hΘx
  obtain ⟨g, u, δ', hxe⟩ := hnf x
  have hδ'σ : δ' = σ := (hΘ x g u δ' hxe).symm.trans hΘxσ
  rw [hδ'σ] at hxe
  have hΘδ : Θ δ = 1 := by
    rcases hRA (Θ δ) with h | h
    · exact h
    · exfalso
      have h3 : Θ δ ^ 3 = 1 := by rw [← map_pow, hδ3, map_one]
      rw [h, pow_succ, hσsq, one_mul] at h3
      exact hσ1 h3
  obtain ⟨g₁, v, δ'', hδe⟩ := hnf δ
  have hδ''1 : δ'' = 1 := (hΘ δ g₁ v δ'' hδe).symm.trans hΘδ
  rw [hδ''1, fieldActor_one, mul_one] at hδe
  set D := compatDiagAutHom TwistTag.E6 K σ.toRingHom with hD
  set σ₀ := fieldActor (t := TwistTag.E6) σ σ with hσ₀
  let q := QuotientGroup.mk' (twistedE6Inn K σ)
  have hq1 : ∀ c : twistedE6RootGroup K σ, q (MulAut.conj c) = 1 := fun c =>
    (QuotientGroup.eq_one_iff _).2 ⟨c, rfl⟩
  have hqx : q x = q (D u) * q σ₀ := by
    rw [hxe, map_mul, map_mul, hq1, one_mul]
  have hqδ : q δ = q (D v) := by
    rw [hδe, map_mul, hq1, one_mul]
  have hcomm : (q (D u) * q σ₀) * q (D v) = q (D v) * (q (D u) * q σ₀) := by
    rw [← hqx, ← hqδ, ← map_mul, ← map_mul, hxδ]
  have hab : q (D u) * q (D v) = q (D v) * q (D u) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm u v]
  have hS : σ₀ * D v = (D v)⁻¹ * σ₀ := by
    rw [hσ₀, fieldActor_mul_compatDiagAutHom, orbitUnitsMap_eq_inv hK σ hσ, map_inv]
  have hsb : q σ₀ * q (D v) = (q (D v))⁻¹ * q σ₀ := by
    rw [← map_mul, hS, map_mul, map_inv]
  have hb2 : q (D v) ^ 2 = 1 := sq_eq_one_of_conj_inv hab hsb hcomm
  have hb3 : q (D v) ^ 3 = 1 := by rw [← hqδ, ← map_pow, hδ3, map_one]
  have hb1 : q (D v) = 1 := by
    calc q (D v) = q (D v) ^ 3 * (q (D v) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hb3, hb2]; simp
  rw [← hqδ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hb1
  exact hδ hb1

theorem mem_inn_sup_diag_of_pow_three (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {δ : MulAut (twistedE6RootGroup K σ)} (hδ3 : δ ^ 3 = 1) :
    δ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
  classical
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  obtain ⟨hσ1, hσsq, hRA⟩ := ringAut_facts_of_card_four hK σ hσ
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two le_rfl K hK2 σ hσ2
  rw [← hker]
  refine MonoidHom.mem_ker.2 ?_
  rcases hRA (Θ δ) with h | h
  · exact h
  · exfalso
    have h3 : Θ δ ^ 3 = 1 := by rw [← map_pow, hδ3, map_one]
    rw [h, pow_succ, hσsq, one_mul] at h3
    exact hσ1 h3

open CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem exists_ghat (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {δ : MulAut (twistedE6RootGroup K σ)} (hδ3 : δ ^ 3 = 1) (hδ : δ ∉ twistedE6Inn K σ) :
    ∃ ĝ : ModGL TwistTag.E6.tag K, ĝ ∈ twistedE6InndiagGL K σ ∧ ĝ ∉ twistedE6RootGroup K σ ∧
      ĝ ^ 3 = 1 ∧ ∀ c : twistedE6RootGroup K σ,
        ((δ c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = ĝ * c * ĝ⁻¹ := by
  classical
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  have hmem := mem_inn_sup_diag_of_pow_three hK σ hσ hδ3
  rw [← range_twistedE6InndiagConj] at hmem
  obtain ⟨g, hg⟩ := hmem
  have hinj := twistedE6InndiagConj_injective Nat.prime_two le_rfl hK2 σ hσ2
  refine ⟨(g : ModGL TwistTag.E6.tag K), g.2, ?_, ?_, ?_⟩
  · intro hgC
    apply hδ
    refine ⟨⟨(g : ModGL TwistTag.E6.tag K), hgC⟩, ?_⟩
    rw [← hg]
    refine MulEquiv.ext fun c => Subtype.ext ?_
    rfl
  · have h1 : twistedE6InndiagConj K σ (g ^ 3) = 1 := by rw [map_pow, hg, hδ3]
    have h2 : g ^ 3 = 1 := hinj (h1.trans (map_one _).symm)
    exact congrArg Subtype.val h2
  · intro c
    rw [← hg]
    exact twistedE6InndiagConj_apply g c

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.LangTorus in
theorem conj_ghat_mem_model [CharP K 2] (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    {ĝ : ModGL TwistTag.E6.tag K} (hĝ : ĝ ∈ twistedE6InndiagGL K σ) :
    g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ĝ * g0 ∈
      twE6TwoModel (AlgebraicClosure K) := by
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  have hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hFr : ∀ c : AlgebraicClosure K, iterateFrobenius (AlgebraicClosure K) 2 1 c = c ^ (2 ^ 1) :=
    fun c => by rw [iterateFrobenius_two_one]; norm_num
  have h1 := map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two le_rfl hK2 σ hσ2
    (iterateFrobenius (AlgebraicClosure K) 2 1) hFr (Subgroup.mem_map_of_mem _ hĝ)
  set D := LangDatum.ofTwist TwistTag.E6 (iterateFrobenius (AlgebraicClosure K) 2 1) 2
    iterateFrobenius_two_one twE6W0 hg0C hg0 with hD
  have h2 := model_eq_map_twistedFixedGroup D
    (Fr := iterateFrobenius (AlgebraicClosure K) 2 1) rfl
  have h3 : MulAut.conj D.g0⁻¹ (baseChangeGL (algebraMap K (AlgebraicClosure K)) ĝ) ∈ D.model := by
    rw [h2]
    exact Subgroup.mem_map_of_mem _ h1
  change g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ĝ * g0 ∈ D.model
  convert h3 using 1
  simp [hD, LangDatum.ofTwist, MulAut.conj_apply]

end TwE6


section Transport

theorem outer_of_mulEquiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (h : ∀ δ' : MulAut S', δ' ^ 3 = 1 → δ' ∉ innerAut S' →
      ∀ H' : Subgroup (MulAut S'), innerAut S' ≤ H' →
        GLAPPrimeCoreOf 3 (H' ⊓ Subgroup.centralizer ({δ'} : Set (MulAut S'))) = ⊥) :
    ∀ δ : MulAut S, δ ^ 3 = 1 → δ ∉ innerAut S → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
      GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({δ} : Set (MulAut S))) = ⊥ := by
  intro δ hδ3 hδ H hH
  let ψ : MulAut S →* MulAut S' := (MulAut.congr e).toMonoidHom
  have hψ : Function.Injective ψ := (MulAut.congr e).injective
  have hinn : innerAut S' ≤ (innerAut S).map ψ := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (e.symm y), ⟨e.symm y, rfl⟩, ?_⟩
    ext z
    simp [ψ, MulAut.congr_apply, MulAut.conj_apply]
  have hψd : ψ δ ∉ innerAut S' := by
    rintro ⟨x, hx⟩
    apply hδ
    refine ⟨e.symm x, ?_⟩
    apply hψ
    rw [← hx]
    ext z
    simp [ψ, MulAut.congr_apply, MulAut.conj_apply]
  have hψd3 : ψ δ ^ 3 = 1 := by rw [← map_pow, hδ3, map_one]
  have h0 := h (ψ δ) hψd3 hψd (H.map ψ) (hinn.trans (Subgroup.map_mono hH))
  rw [← map_inf_centralizer_of_injective ψ hψ, ← map_glaPPrimeCoreOf_of_injective 3 ψ hψ] at h0
  exact (Subgroup.map_eq_bot_iff_of_injective _ hψ).1 h0

end Transport

section Ext

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T


variable {K : Type} [Field K] {ω : Kˣ} {kb : List (List ℕ)}

@[expose] def FamData (ω : Kˣ) (kb : List (List ℕ)) : Prop :=
  (familyKernel (famV (τ := Tag.E6) ω kb) = ∅ ∧
      ∀ w ∈ familyStabilizer (famV (τ := Tag.E6) ω kb), w = 1) ∨
    ∃ α, IsRoot Tag.E6 α ∧ familyKernel (famV (τ := Tag.E6) ω kb) = {α, -α} ∧
      ∀ w ∈ familyStabilizer (famV (τ := Tag.E6) ω kb), w = 1 ∨ w = rootReflection α

theorem famV_append_left (kc : List (List ℕ)) (j : Fin (kb ++ kc).length)
    (hj : j.val < kb.length) :
    famV (τ := Tag.E6) ω (kb ++ kc) j = famV (τ := Tag.E6) ω kb ⟨j.val, hj⟩ := by
  simp only [famV, List.get_eq_getElem, List.getElem_append_left hj]

theorem famV_append_singleton_last (al : List ℕ) :
    famV (τ := Tag.E6) ω (kb ++ [al]) ⟨kb.length, by simp⟩ =
      torV ω (listVec Tag.E6.rank al) := by
  simp [famV, List.get_eq_getElem]

theorem mem_familyKernel_append (al : List ℕ) {α : Fin Tag.E6.rank → ℤ} :
    α ∈ familyKernel (famV (τ := Tag.E6) ω (kb ++ [al])) ↔
      α ∈ familyKernel (famV (τ := Tag.E6) ω kb) ∧
        rootChar (torV ω (listVec Tag.E6.rank al)) α = 1 := by
  constructor
  · rintro ⟨hα, h⟩
    refine ⟨⟨hα, fun j => ?_⟩, ?_⟩
    · have := h ⟨j.val, Nat.lt_of_lt_of_le j.2 (by simp)⟩
      rwa [famV_append_left [al] ⟨j.val, Nat.lt_of_lt_of_le j.2 (by simp)⟩ j.2] at this
    · have := h ⟨kb.length, by simp⟩
      rwa [famV_append_singleton_last] at this
  · rintro ⟨⟨hα, h⟩, h2⟩
    refine ⟨hα, fun j => ?_⟩
    by_cases hj : j.val < kb.length
    · rw [famV_append_left [al] j hj]
      exact h ⟨j.val, hj⟩
    · have hjk : j = ⟨kb.length, by simp⟩ := by
        apply Fin.ext
        have := j.2
        simp at this
        simp
        omega
      rw [hjk, famV_append_singleton_last]
      exact h2

theorem mem_familyStabilizer_append (al : List ℕ) {w : WeylGroup Tag.E6} :
    w ∈ familyStabilizer (famV (τ := Tag.E6) ω (kb ++ [al])) ↔
      w ∈ familyStabilizer (famV (τ := Tag.E6) ω kb) ∧
        w ∈ rootCharStabilizer (torV ω (listVec Tag.E6.rank al)) := by
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · have := h ⟨j.val, Nat.lt_of_lt_of_le j.2 (by simp)⟩
      rwa [famV_append_left [al] ⟨j.val, Nat.lt_of_lt_of_le j.2 (by simp)⟩ j.2] at this
    · have := h ⟨kb.length, by simp⟩
      rwa [famV_append_singleton_last] at this
  · rintro ⟨h, h2⟩ j
    by_cases hj : j.val < kb.length
    · rw [famV_append_left [al] j hj]
      exact h ⟨j.val, hj⟩
    · have hjk : j = ⟨kb.length, by simp⟩ := by
        apply Fin.ext
        have := j.2
        simp at this
        simp
        omega
      rw [hjk, famV_append_singleton_last]
      exact h2

end Ext

section Ext2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T


variable {K : Type} [Field K] {ω : Kˣ} {kb : List (List ℕ)}

theorem rootChar_eq_one_of_reflection_mem {a : Fin Tag.E6.rank → Kˣ} (h3 : ∀ i, a i ^ 3 = 1)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hr : rootReflection α ∈ rootCharStabilizer a) : rootChar a α = 1 := by
  have h1 : rootChar a (rootReflection α • α) = rootChar a α := hr α
  rw [CFSG.HardMathSupport.Timmesfeld.LangTorus.rootReflection_smul_self hα,
    rootChar_neg_vec_E6Four] at h1
  have hcube : rootChar a α ^ 3 = 1 :=
    CFSG.RankThree.Chevalley.rootChar_pow_of_pow_eq_one (funext fun i => by simpa using h3 i) α
  have hsq : rootChar a α * rootChar a α = 1 := by
    calc rootChar a α * rootChar a α = (rootChar a α)⁻¹ * rootChar a α := by rw [h1]
      _ = 1 := inv_mul_cancel _
  calc rootChar a α = rootChar a α ^ 3 * (rootChar a α * rootChar a α)⁻¹ := by group
    _ = 1 := by rw [hcube, hsq]; simp

theorem FamData.append (h : FamData ω kb) {al : List ℕ}
    (h3 : ∀ i, torV ω (listVec Tag.E6.rank al) i ^ 3 = 1) : FamData ω (kb ++ [al]) := by
  set a := torV ω (listVec Tag.E6.rank al) with ha
  rcases h with ⟨hK, hW⟩ | ⟨α, hα, hK, hW⟩
  · left
    refine ⟨Set.eq_empty_iff_forall_notMem.2 fun β hβ => ?_, fun w hw => ?_⟩
    · have := ((mem_familyKernel_append al).1 hβ).1
      rw [hK] at this
      exact this
    · exact hW w ((mem_familyStabilizer_append al).1 hw).1
  · by_cases hαa : rootChar a α = 1
    · right
      refine ⟨α, hα, Set.ext fun β => ?_, fun w hw => hW w ((mem_familyStabilizer_append al).1 hw).1⟩
      rw [mem_familyKernel_append, hK, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, -⟩
        simpa using h1
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, hαa⟩
        · exact ⟨Or.inr rfl, by rw [rootChar_neg_vec_E6Four, hαa, inv_one]⟩
    · left
      refine ⟨Set.eq_empty_iff_forall_notMem.2 fun β hβ => ?_, fun w hw => ?_⟩
      · obtain ⟨h1, h2⟩ := (mem_familyKernel_append al).1 hβ
        rw [hK, Set.mem_insert_iff, Set.mem_singleton_iff] at h1
        rcases h1 with rfl | rfl
        · exact hαa h2
        · rw [rootChar_neg_vec_E6Four, inv_eq_one] at h2
          exact hαa h2
      · obtain ⟨hw1, hw2⟩ := (mem_familyStabilizer_append al).1 hw
        rcases hW w hw1 with rfl | rfl
        · rfl
        · exact absurd (rootChar_eq_one_of_reflection_mem h3 hα hw2) hαa

end Ext2

section Hyper

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T Timmesfeld.Co1Leaf


variable {τ : Tag} {k : Type} [Field k] {G : Subgroup (ModGL τ k)} {ω : kˣ}

theorem mem_famCentS_append {kb kc : List (List ℕ)} {g : G} :
    g ∈ famCentS ω G (kb ++ kc) ↔ g ∈ famCentS ω G kb ∧ g ∈ famCentS ω G kc := by
  rw [mem_famCentS, mem_famCentS, mem_famCentS]
  constructor
  · intro h
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have := h ⟨j.val, Nat.lt_of_lt_of_le j.2 (by simp)⟩
      simpa [List.get_eq_getElem, List.getElem_append_left j.2] using this
    · have := h ⟨kb.length + j.val, by simp⟩
      simpa [List.get_eq_getElem, List.getElem_append_right] using this
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j.val < kb.length
    · have := h1 ⟨j.val, hj⟩
      simpa [List.get_eq_getElem, List.getElem_append_left hj] using this
    · have hj' : j.val - kb.length < kc.length := by
        have := j.2
        simp at this
        omega
      have := h2 ⟨j.val - kb.length, hj'⟩
      simpa [List.get_eq_getElem, List.getElem_append_right (Nat.not_lt.1 hj)] using this

variable [Finite G]

theorem gLAPPrimeCoreOf_centralizer_ext (hω3 : orderOf ω = 3) {m : ℕ} (hm : 0 < m)
    {e : Fin m → Fin τ.rank → ZMod 3} (he : ∀ i, dV (τ := τ) ω (e i) ∈ G)
    (hinj : Function.Injective (subLin (τ := τ) e)) (al : List ℕ)
    (hleaf : ∀ fl ∈ normVecs 3 m,
      GLAPPrimeCoreOf 3 (famCentS ω G (((kerBasis 3 fl).map (liftL e)) ++ [al])) = ⊥) :
    GLAPPrimeCoreOf 3 (famCentS ω G [al]) = ⊥ := by
  have hω : ω ^ 3 = 1 := pow_three_of_orderOf hω3
  set φ := vecProdHom (genS he) (genS_comm hω he) (genS_pow hω he) with hφdef
  have hφ : ∀ a, φ (Multiplicative.ofAdd a) = dS hω he a := fun a => vecProd_genS hω he a
  have hinjφ : Function.Injective φ := by
    intro a b h
    rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, hφ, hφ] at h
    have h1 := dV_injective (τ := τ) hω3 (congrArg Subtype.val h)
    rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, hinj h1]
  set A := φ.range with hAdef
  have hmemA : ∀ a, dS hω he a ∈ A := fun a => ⟨Multiplicative.ofAdd a, hφ a⟩
  have hAcomm : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hA : IsElemAbelian 3 A := by
    refine ⟨⟨⟨fun x z => Subtype.ext (hAcomm x x.2 z z.2)⟩⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := by
      rw [← ofAdd_toAdd a, ← ofAdd_nsmul]
      have h3 : (3 • Multiplicative.toAdd a) = 0 := by
        funext j
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
        have : (3 : ZMod 3) = 0 := rfl
        rw [Nat.cast_ofNat, this, zero_mul]
      rw [h3, ofAdd_zero]
    rw [this, map_one]
  have hAC : A ≤ famCentS ω G [al] := by
    rintro _ ⟨a, rfl⟩
    rw [← ofAdd_toAdd a, hφ]
    refine mem_famCentS.2 fun j => ?_
    have hj : ([al] : List (List ℕ)).get j = al := by
      have h0 : j.val = 0 := by
        have h1 : ([al] : List (List ℕ)).length = 1 := rfl
        have := j.2
        omega
      simp [List.get_eq_getElem, h0]
    rw [hj]
    change dV ω (subLin e (Multiplicative.toAdd a)) * dV ω (listVec τ.rank al) =
      dV ω (listVec τ.rank al) * dV ω (subLin e (Multiplicative.toAdd a))
    rw [← dV_add hω, ← dV_add hω, add_comm]
  have hA1 : A ≠ ⊥ := by
    intro h
    have hm' : (⟨0, hm⟩ : Fin m) = ⟨0, hm⟩ := rfl
    set y : Fin m → ZMod 3 := Pi.single ⟨0, hm⟩ 1 with hy
    have hy0 : y ≠ 0 := by
      intro h0
      have := congrFun h0 ⟨0, hm⟩
      simp [hy] at this
    have h1 : dS hω he y ∈ (⊥ : Subgroup G) := h ▸ hmemA y
    rw [Subgroup.mem_bot] at h1
    have h2 : dV ω (subLin e y) = dV ω (subLin e 0) := by
      rw [subLin_zero, dV_zero]
      exact congrArg Subtype.val h1
    exact hy0 (hinj (dV_injective (τ := τ) hω3 h2))
  have hcentB : ∀ (kb : List (List ℕ)), Subgroup.centralizer
      (Subgroup.closure {x | ∃ b ∈ kb, x = vecProd (genS he) (listVec m b)} : Set G) =
        famCentS ω G (kb.map (liftL e)) := by
    intro kb
    rw [Subgroup.centralizer_closure]
    ext x
    rw [Subgroup.mem_centralizer_iff, mem_famCentS]
    constructor
    · intro h j
      have hj : (kb.map (liftL e)).get j = liftL e (kb.get ⟨j.val, by simpa using j.2⟩) := by
        simp
      rw [hj, listVec_liftL]
      have h1 := h _ ⟨kb.get ⟨j.val, by simpa using j.2⟩, List.get_mem kb _,
        (vecProd_genS hω he _).symm⟩
      exact (congrArg Subtype.val h1).symm
    · rintro h _ ⟨b, hb, rfl⟩
      obtain ⟨j, rfl⟩ := List.get_of_mem hb
      rw [vecProd_genS hω he]
      have hj := h ⟨j.val, by simp⟩
      have e1 : (kb.map (liftL e)).get ⟨j.val, by simp⟩ = liftL e (kb.get j) := by simp
      rw [e1, listVec_liftL] at hj
      exact Subtype.ext hj.symm
  refine gLAPPrimeCoreOf_eq_bot_of_hyperplanes Nat.prime_three hA hAC hA1 fun B hBA hidx => ?_
  obtain ⟨fl, hfl, hBeq⟩ := exists_normVec_eq_closure (genS_comm hω he) (genS_pow hω he) hinjφ
    hBA hidx
  have heq : famCentS ω G [al] ⊓ Subgroup.centralizer (B : Set G) =
      famCentS ω G (((kerBasis 3 fl).map (liftL e)) ++ [al]) := by
    ext g
    rw [Subgroup.mem_inf, hBeq, hcentB, mem_famCentS_append, and_comm]
  rw [heq]
  exact hleaf fl hfl

end Hyper


section OuterCore

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T Timmesfeld.Co1Leaf

set_option linter.unusedSectionVars false


theorem famCentS_singleton {τ : Tag} {k : Type} [Field k] {G : Subgroup (ModGL τ k)} {ω : kˣ}
    (al : List ℕ) :
    famCentS ω G [al] =
      (Subgroup.centralizer ({dV (τ := τ) ω (listVec τ.rank al)} : Set (ModGL τ k))).subgroupOf G := by
  ext g
  rw [mem_famCentS, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact h ⟨0, by simp⟩
  · intro h j
    have hj : ([al] : List (List ℕ)).get j = al := by
      have h0 : j.val = 0 := by
        have h1 : ([al] : List (List ℕ)).length = 1 := rfl
        have := j.2
        omega
      simp [List.get_eq_getElem, h0]
    rw [hj]
    exact h

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem gLAPPrimeCoreOf_centralizer_dV_twE6Two
    [Finite (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))] {ω : Lˣ}
    (hω : orderOf ω = 3) (x : Fin Tag.E6.rank → ZMod 3) :
    GLAPPrimeCoreOf 3 ((Subgroup.centralizer ({dV (τ := Tag.E6) ω x} : Set (ModGL Tag.E6 L))).subgroupOf
      (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))) = ⊥ := by
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  have hcert := Certificates.certificate13614
  unfold Native.e6FourCoreCheck at hcert
  simp only [Bool.and_eq_true, List.all_eq_true] at hcert
  obtain ⟨⟨hhyp, -⟩, -⟩ := hcert
  have hGM : ⁅twE6TwoModel L, twE6TwoModel L⁆ ≤ twE6TwoModel L := twE6Two_commutator_le_model
  have hGC : ⁅twE6TwoModel L, twE6TwoModel L⁆ ≤ adjointGroup Tag.E6 L := fun g hg => (hGM hg).1
  have hX3 : ∀ g ∈ ⁅twE6TwoModel L, twE6TwoModel L⁆, g ∈ torusGroup Tag.E6 L → g ^ 3 = 1 := by
    intro g hg hgT
    obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hgT
    have hF : twE6TwoF L (rootDiagUnit Tag.E6 a) = rootDiagUnit Tag.E6 a := (hGM hg).2
    rw [twE6TwoF_rootDiagUnit, inv_pow] at hF
    change rootDiagUnit Tag.E6 a ^ 3 = 1
    rw [pow_succ]
    exact inv_eq_iff_mul_eq_one.1 hF
  have hlenL : ∀ (l : List (List ℕ)), ∀ b ∈ l.map (liftL (τ := .E6) e6InnerVec),
      b.length = Tag.E6.rank := by
    intro l b hb
    obtain ⟨b', -, rfl⟩ := List.mem_map.1 hb
    exact length_liftL _ _
  have hltL : ∀ (l : List (List ℕ)), ∀ b ∈ l.map (liftL (τ := .E6) e6InnerVec), ∀ x ∈ b,
      x < 3 := by
    intro l b hb
    obtain ⟨b', -, rfl⟩ := List.mem_map.1 hb
    exact lt_of_mem_liftL _ _
  set al : List ℕ := List.ofFn fun i => (x i).val with hal
  have hlistVec : listVec Tag.E6.rank al = x := by
    funext i
    simp [listVec, hal, List.getD_eq_getElem?_getD]
  have h3al : ∀ i, torV ω (listVec Tag.E6.rank al) i ^ 3 = 1 := by
    intro i
    simp only [torV]
    rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hleaf : ∀ fl ∈ normVecs 3 5, GLAPPrimeCoreOf 3 (famCentS ω ⁅twE6TwoModel L, twE6TwoModel L⁆
      (((kerBasis 3 fl).map (liftL (τ := .E6) e6InnerVec)) ++ [al])) = ⊥ := by
    intro fl hfl
    refine gLAPPrimeCoreOf_leafS hGC hX3 ?_
    have hd : Bal209TwoOuterInAux.FamData ω ((kerBasis 3 fl).map (liftL (τ := .E6) e6InnerVec)) :=
      famData_of_famOKW hω (hlenL _) (hltL _) (hhyp fl hfl)
    rcases hd.append h3al with h | ⟨α, hα, hker, hW⟩
    · exact Or.inl h
    · obtain ⟨μ, hμ⟩ := exists_twE6TwoF_rootSL2 (L := L) hα
      refine Or.inr ⟨α, hα, hker, hW, fun g hg hgTL => ?_, fun N hNL hnorm hcop => ?_⟩
      · exact pow_three_mem_rootSpan_tw (twE6TwoF L) twE6TwoF_rootDiagUnit hα hμ (hGM hg) hgTL
      · exact eq_bot_of_le_rootSpan_tw (twE6TwoF L) hω hα hμ hGM
          (twE6Two_rootSL2_HSL_mem_commutator hα hω3) N hNL hnorm hcop
  have key := Bal209TwoOuterInAux.gLAPPrimeCoreOf_centralizer_ext (G := ⁅twE6TwoModel L, twE6TwoModel L⁆)
    hω (m := 5) (by norm_num) (e := e6InnerVec)
    (twE6Two_dV_e6InnerVec_mem_commutator (L := L) hω3) subLin_e6InnerVec_injective al hleaf
  rw [famCentS_singleton, hlistVec] at key
  exact key

end OuterCore

section OuterFusion

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T Timmesfeld.Co1Leaf

set_option linter.unusedSectionVars false


variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem exists_model_conj_of_cocycle {y : ModGL Tag.E6 L} (hy : y ∈ adjointGroup Tag.E6 L)
    (a : Fin Tag.E6.rank → Lˣ) (hc : y⁻¹ * twE6TwoF L y ∈ toralRootGroup Tag.E6 L a) :
    ∃ u' ∈ twE6TwoModel L, u' * rootDiagUnit Tag.E6 a * u'⁻¹ =
      y * rootDiagUnit Tag.E6 a * y⁻¹ := by
  obtain ⟨z, hz, hzc⟩ := toralRootGroup_lang_tw a _ hc
  obtain ⟨hzG, hzd⟩ := mem_toralCentralizer.1 (toralRootGroup_le a hz)
  have hFz : twE6TwoF L z = z * (y⁻¹ * twE6TwoF L y) := by rw [← hzc]; group
  have hadj : y * z⁻¹ ∈ adjointGroup Tag.E6 L := mul_mem hy (inv_mem hzG)
  refine ⟨y * z⁻¹, ⟨hadj, ?_⟩, ?_⟩
  · change twE6TwoF L (y * z⁻¹) = y * z⁻¹
    rw [map_mul, map_inv, hFz]
    group
  · have h1 : rootDiagUnit Tag.E6 a * z = z * rootDiagUnit Tag.E6 a := by
      rw [mul_inv_eq_iff_eq_mul] at hzd
      exact hzd
    calc y * z⁻¹ * rootDiagUnit Tag.E6 a * (y * z⁻¹)⁻¹ =
        y * (z⁻¹ * (rootDiagUnit Tag.E6 a * z)) * y⁻¹ := by group
      _ = y * (z⁻¹ * (z * rootDiagUnit Tag.E6 a)) * y⁻¹ := by rw [h1]
      _ = y * rootDiagUnit Tag.E6 a * y⁻¹ := by group

theorem exists_model_conj_dV {ω : Lˣ} {s y : ModGL Tag.E6 L} (hy : y ∈ adjointGroup Tag.E6 L)
    {a : Fin Tag.E6.rank → Lˣ} (hsy : s = y * rootDiagUnit Tag.E6 a * y⁻¹)
    (hc : y⁻¹ * twE6TwoF L y ∈ toralRootGroup Tag.E6 L a) {x : Fin Tag.E6.rank → ZMod 3}
    (hax : a = torV ω x) :
    ∃ m ∈ twE6TwoModel L, m * s * m⁻¹ = dV (τ := Tag.E6) ω x := by
  obtain ⟨u', hu'M, hu'⟩ := exists_model_conj_of_cocycle hy a hc
  have hu'G : u' ∈ adjointGroup Tag.E6 L := hu'M.1
  refine ⟨u'⁻¹, (twE6TwoModel L).inv_mem hu'M, ?_⟩
  have hd : dV (τ := Tag.E6) ω x = rootDiagUnit Tag.E6 a := by rw [hax]; rfl
  rw [hd, hsy, ← hu']
  group

theorem cocycle_mem_toralRootGroup_of_nonInner
    {s y : ModGL Tag.E6 L} (hsM : s ∈ twE6TwoModel L)
    (hy : y ∈ adjointGroup Tag.E6 L) {a : Fin Tag.E6.rank → Lˣ} (ha3 : ∀ i, a i ^ 3 = 1)
    (hsy : s = y * rootDiagUnit Tag.E6 a * y⁻¹) (hnon : rootChar a e6Omega3 ≠ 1) :
    y⁻¹ * twE6TwoF L y ∈ toralRootGroup Tag.E6 L a := by
  set d : ModGL Tag.E6 L := rootDiagUnit Tag.E6 a with hd
  have hd3 : d ^ 3 = 1 := by
    rw [hd, rootDiagUnit_pow]
    have : a ^ 3 = 1 := funext fun j => by simpa using ha3 j
    rw [this, rootDiagUnit_one]
  have hFd : twE6TwoF L d = d := by
    rw [hd, twE6TwoF_rootDiagUnit, ← hd, inv_pow]
    exact inv_eq_of_mul_eq_one_left (by rw [← pow_succ']; exact hd3)
  have hFs : twE6TwoF L (y * d * y⁻¹) = y * d * y⁻¹ := by
    rw [← hsy]
    exact hsM.2
  rw [map_mul, map_mul, map_inv, hFd] at hFs
  set c : ModGL Tag.E6 L := y⁻¹ * twE6TwoF L y with hc
  have hcd : c * d * c⁻¹ = d := by
    calc c * d * c⁻¹ = y⁻¹ * (twE6TwoF L y * d * (twE6TwoF L y)⁻¹) * y := by rw [hc]; group
      _ = y⁻¹ * (y * d * y⁻¹) * y := by rw [hFs]
      _ = d := by group
  have hFy : twE6TwoF L y ∈ adjointGroup Tag.E6 L := by
    have hy' : (y : ModGL TwistTag.E6.tag L) ∈ adjointGroup TwistTag.E6.tag L := hy
    have h3 := mul_mem (mul_mem
      (canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.E6.tag) L twE6W0)
      (twistHom_mem_adjointGroup TwistTag.E6 L (iterateFrobenius L 2 1) hy'))
      (inv_mem (canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.E6.tag) L twE6W0))
    exact h3
  have hcG : c ∈ adjointGroup Tag.E6 L := mul_mem (inv_mem hy) hFy
  have hcC : c ∈ toralCentralizer Tag.E6 L a := by
    refine mem_toralCentralizer.2 ⟨hcG, ?_⟩
    rw [← hd]
    have h1 : c * d = d * c := mul_inv_eq_iff_eq_mul.1 hcd
    calc d * c * d⁻¹ = c * d * d⁻¹ := by rw [← h1]
      _ = c := by group
  have hW : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := fun w hw =>
    mem_kernelReflectionGroup_of_nonInner a ha3 hnon hw
  rw [← toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.E6 L a hW]
  exact hcC


end OuterFusion

end Bal209TwoOuterInAux

section Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

set_option linter.unusedSectionVars false

@[expose] def TwE6TwoOuterModel : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
    ∀ g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
      twistHom TwistTag.E6 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 →
    ∀ m ∈ twE6TwoModel (AlgebraicClosure K),
      m ∉ (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) → m ^ 3 = 1 →
      GLAPPrimeCoreOf 3 ((Subgroup.centralizer ({m} : Set (ModGL Tag.E6 (AlgebraicClosure K)))).subgroupOf
        (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
          Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) = ⊥

end Model

section Reduction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

@[expose] def TwE6TwoOuterInnCore : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
    ∀ δ : MulAut (twistedE6RootGroup K σ), δ ^ 3 = 1 → δ ∉ innerAut (twistedE6RootGroup K σ) →
      GLAPPrimeCoreOf 3 (innerAut (twistedE6RootGroup K σ) ⊓
        Subgroup.centralizer ({δ} : Set (MulAut (twistedE6RootGroup K σ)))) = ⊥


open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
theorem twE6TwoOuterInnCore_of_model (h : TwE6TwoOuterModel) : TwE6TwoOuterInnCore := by
  intro K _ _ hK σ hσ δ hδ3 hδ
  have hcK : CharP K 2 := charP_two_of_card_four hK
  obtain ⟨ĝ, hĝ, hĝC, hĝ3, hĝδ⟩ := Bal209TwoOuterInAux.exists_ghat hK σ hσ hδ3 hδ
  obtain ⟨g0, hg0C, hg0⟩ := exists_twE6Two_lang K
  set L := AlgebraicClosure K with hL
  set ι := algebraMap K L with hι
  set e := twE6TwoEquiv hK σ hσ hg0C hg0 with he
  have hcoe := coe_twE6TwoEquiv hK σ hσ hg0C hg0
  set m : ModGL Tag.E6 L := g0⁻¹ * baseChangeGL ι ĝ * g0 with hm
  have hmM : m ∈ twE6TwoModel L :=
    Bal209TwoOuterInAux.conj_ghat_mem_model hK σ hσ hg0C hg0 hĝ
  have hmΓ : m ∉ (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L)) := by
    intro hmΓ
    obtain ⟨c, hc⟩ := e.surjective ⟨m, hmΓ⟩
    have h1 : ((e c : ↥(⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))) :
        ModGL Tag.E6 L) = m := congrArg Subtype.val hc
    rw [hcoe c] at h1
    have h2 : baseChangeGL ι (c : ModGL TwistTag.E6.tag K) = baseChangeGL ι ĝ := by
      have := congrArg (fun y => g0 * y * g0⁻¹) h1
      simpa [hm, mul_assoc] using this
    exact hĝC (by
      have := baseChangeGL_injective ι h2
      rw [← this]
      exact c.2)
  have hm3 : m ^ 3 = 1 := by
    have h2 := conj_pow (a := g0⁻¹) (b := baseChangeGL ι ĝ) (i := 3)
    have h3 : (g0⁻¹ * baseChangeGL ι ĝ * g0) ^ 3 = g0⁻¹ * baseChangeGL ι ĝ ^ 3 * g0 := by
      simpa using h2
    have h4 : (g0⁻¹ * baseChangeGL ι ĝ * g0) ^ 3 = 1 := by
      rw [h3, ← map_pow, hĝ3, map_one]
      group
    exact h4
  have hcore := h K hK σ hσ g0 hg0C hg0 m hmM hmΓ hm3
  set A : Subgroup (twistedE6RootGroup K σ) :=
    (Subgroup.centralizer ({ĝ} : Set (ModGL TwistTag.E6.tag K))).comap
      (twistedE6RootGroup K σ).subtype with hA
  set B : Subgroup ↥(⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L)) :=
    (Subgroup.centralizer ({m} : Set (ModGL Tag.E6 L))).subgroupOf
      (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L)) with hB
  have hAB : ∀ c : twistedE6RootGroup K σ, c ∈ A ↔ e c ∈ B := by
    intro c
    rw [hA, hB, Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    have h2 : ((e c : ↥(⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))) :
        ModGL Tag.E6 L) = g0⁻¹ * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * g0 := hcoe c
    constructor
    · intro hc
      have hc' : (c : ModGL TwistTag.E6.tag K) * ĝ = ĝ * (c : ModGL TwistTag.E6.tag K) := hc
      have h3 : baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * baseChangeGL ι ĝ =
          baseChangeGL ι ĝ * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) := by
        rw [← map_mul, ← map_mul, hc']
      show ((e c : ↥(⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))) :
        ModGL Tag.E6 L) * m = m * ((e c : ↥(⁅twE6TwoModel L, twE6TwoModel L⁆ :
          Subgroup (ModGL Tag.E6 L))) : ModGL Tag.E6 L)
      rw [h2, hm]
      exact (Bal209TwoOuterInAux.conj_commute_iff g0 _ _).2 h3
    · intro hc
      have hc' : ((e c : ↥(⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))) :
          ModGL Tag.E6 L) * m = m * ((e c : ↥(⁅twE6TwoModel L, twE6TwoModel L⁆ :
            Subgroup (ModGL Tag.E6 L))) : ModGL Tag.E6 L) := hc
      rw [h2, hm] at hc'
      have h3 := (Bal209TwoOuterInAux.conj_commute_iff g0 _ _).1 hc'
      rw [← map_mul, ← map_mul] at h3
      exact baseChangeGL_injective ι h3
  have hmapA : A.map e.toMonoidHom = B := by
    ext y
    obtain ⟨c, rfl⟩ := e.surjective y
    constructor
    · rintro ⟨c', hc', hcc'⟩
      have : c' = c := e.injective hcc'
      subst this
      exact (hAB c').1 hc'
    · intro hy
      exact ⟨c, (hAB c).2 hy, rfl⟩
  have hAcore : GLAPPrimeCoreOf 3 A = ⊥ := by
    have h1 := map_glaPPrimeCoreOf_of_injective 3 e.toMonoidHom e.injective A
    rw [hmapA, hcore] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1
  have hinj : Function.Injective (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    mulAut_conj_injective_of_center_eq_bot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  have hδA : ∀ c : twistedE6RootGroup K σ, δ c = c ↔ c ∈ A := by
    intro c
    rw [hA, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have h1 := hĝδ c
    constructor
    · intro hc
      have h2 : ((δ c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
          (c : ModGL TwistTag.E6.tag K) := congrArg Subtype.val hc
      rw [h1] at h2
      show (c : ModGL TwistTag.E6.tag K) * ĝ = ĝ * (c : ModGL TwistTag.E6.tag K)
      calc (c : ModGL TwistTag.E6.tag K) * ĝ = (ĝ * c * ĝ⁻¹) * ĝ := by rw [h2]
        _ = _ := by group
    · intro hc
      have hc' : (c : ModGL TwistTag.E6.tag K) * ĝ = ĝ * (c : ModGL TwistTag.E6.tag K) := hc
      apply Subtype.ext
      rw [h1, ← hc']
      group
  have hinnC : innerAut (twistedE6RootGroup K σ) ⊓
      Subgroup.centralizer ({δ} : Set (MulAut (twistedE6RootGroup K σ))) =
        A.map (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) := by
    ext x
    constructor
    · rintro ⟨⟨c, rfl⟩, hx⟩
      refine ⟨c, ?_, rfl⟩
      rw [SetLike.mem_coe, ← hδA]
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 hx
      have h2 : δ * MulAut.conj c * δ⁻¹ = MulAut.conj (δ c) :=
        CFSG.LieType.Chevalley.mulAut_mul_conj_mul_inv δ c
      have h3 : δ * MulAut.conj c * δ⁻¹ = MulAut.conj c := by rw [← h1]; group
      exact hinj (h2.symm.trans h3)
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h2 : δ * MulAut.conj c * δ⁻¹ = MulAut.conj (δ c) :=
        CFSG.LieType.Chevalley.mulAut_mul_conj_mul_inv δ c
      rw [(hδA c).2 hc] at h2
      have : MulAut.conj c * δ = δ * MulAut.conj c := by
        calc MulAut.conj c * δ = MulAut.conj c * δ := rfl
          _ = (δ * MulAut.conj c * δ⁻¹) * δ := by rw [h2]
          _ = _ := by group
      exact this
  rw [hinnC, ← map_glaPPrimeCoreOf_of_injective 3 _ hinj, hAcore, Subgroup.map_bot]

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
@[expose] def TwE6TwoOuterExotic : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
    ∀ g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
      twistHom TwistTag.E6 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 →
    ∀ m ∈ twE6TwoModel (AlgebraicClosure K),
      m ∉ (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) → m ^ 3 = 1 →
    ∀ y ∈ adjointGroup Tag.E6 (AlgebraicClosure K), ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      (∀ i, a i ^ 3 = 1) → rootChar a e6Omega3 = 1 →
      m = y * rootDiagUnit Tag.E6 a * y⁻¹ →
      GLAPPrimeCoreOf 3 ((Subgroup.centralizer ({m} : Set (ModGL Tag.E6 (AlgebraicClosure K)))).subgroupOf
        (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
          Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) = ⊥

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
theorem twE6TwoOuterModel_of_exotic
    (h : TwE6TwoOuterExotic) : TwE6TwoOuterModel := by
  intro K _ _ _ hK σ hσ g0 hg0C hg0 m hmM hmΓ hm3
  set L := AlgebraicClosure K with hL
  have hcL : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨y, hyG, a, ha3, hsy⟩ := exists_conj_toral_E6_three hmM.1 hm3
  by_cases hnon : rootChar a e6Omega3 = 1
  · exact h K hK σ hσ g0 hg0C hg0 m hmM hmΓ hm3 y hyG a ha3 hnon hsy
  ·
    have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
    haveI hFin : Finite ↥(⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L)) :=
      Finite.of_equiv _ (twE6TwoEquiv hK σ hσ hg0C hg0).toEquiv
    obtain ⟨ω₀, hω₀⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [card_units_four hK])
    set ω : Lˣ := Units.map (algebraMap K L).toMonoidHom ω₀ with hωdef
    have hω : orderOf ω = 3 := by
      rw [hωdef, orderOf_injective (Units.map (algebraMap K L).toMonoidHom)
        (Units.map_injective (algebraMap K L).injective), hω₀]
    have hprim : IsPrimitiveRoot (ω : L) 3 :=
      IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hω)
    have hapow : ∀ i, ∃ n : ℕ, a i = ω ^ n := fun i => by
      obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (a i : L))
        (by have := congrArg Units.val (ha3 i); simpa using this)
      exact ⟨n, Units.ext (by simpa using hn.symm)⟩
    choose mm hmm using hapow
    have hax : a = torV ω (fun i => (mm i : ZMod 3)) := by
      funext i
      rw [torV, ZMod.val_natCast, hmm i]
      have := pow_mod_orderOf ω (mm i)
      rw [hω] at this
      exact this.symm
    obtain ⟨m', hm'M, hm'⟩ := Bal209TwoOuterInAux.exists_model_conj_dV hyG hsy
      (Bal209TwoOuterInAux.cocycle_mem_toralRootGroup_of_nonInner hmM hyG ha3 hsy hnon) hax
    have hcore := Bal209TwoOuterInAux.gLAPPrimeCoreOf_centralizer_dV_twE6Two (L := L) hω
      (fun i => (mm i : ZMod 3))
    exact Bal209TwoOuterInAux.core_centralizer_of_conj (conjCommutator _ hm'M)
      (fun g => coe_conjCommutator _ hm'M g) hm'.symm hcore

theorem bal209TwoOuter_of_innCore (h : TwE6TwoOuterInnCore) : Bal209TwoOuter := by
  intro S _ _ d hd ⟨e⟩ δ hδ3 hδ H hH _
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedE6 q =>
    have hq2 : q.p = 2 ∧ q.exponent = 1 := hd
    obtain ⟨K', hKf, σ, hcard, hσ, ⟨eC⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    have hcard4 : Nat.card K' = 4 := by
      rw [hcard, hq2.1, hq2.2]; norm_num
    haveI : Finite K' := Nat.finite_of_card_ne_zero (by rw [hcard4]; norm_num)
    have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by
      have := hσ c
      rwa [hq2.1, hq2.2, pow_one] at this
    refine Bal209TwoOuterInAux.outer_of_mulEquiv (e.trans eC) ?_ δ hδ3 hδ H hH
    intro δ' hδ'3 hδ' H' hH'
    exact Bal209TwoOuterInAux.outer_core_of_inner_core hcard4 σ hσ2 hδ'3 hδ'
      (h K' hcard4 σ hσ2 δ' hδ'3 hδ') hH'
  | _ => exact absurd hd (by simp [Bal209TwoIndex])

theorem bal209TwoOuter_of_model (h : TwE6TwoOuterModel) : Bal209TwoOuter :=
  bal209TwoOuter_of_innCore (twE6TwoOuterInnCore_of_model h)

theorem bal209TwoOuter_of_inputs
    (h : TwE6TwoOuterExotic) : Bal209TwoOuter :=
  bal209TwoOuter_of_model (twE6TwoOuterModel_of_exotic h)

end Reduction


end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
