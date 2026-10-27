module

public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification
open scoped Pointwise

theorem mulAut_mul_conj {G : Type*} [Group G] (β : MulAut G) (x : G) :
    β * MulAut.conj x = MulAut.conj (β x) * β :=
  MulEquiv.ext fun y => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem eq_one_or_eq_of_sq_eq_one {p n : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ n) {σ : RingAut K} (hσ1 : σ ≠ 1) (hσ2 : σ ^ 2 = 1)
    {δ : RingAut K} (hδ : δ ^ 2 = 1) : δ = 1 ∨ δ = σ := by
  classical
  obtain ⟨hcard, hcyc⟩ := card_ringAut_and_isCyclic hp K hK
  have hn : n ≠ 0 := by
    rintro rfl
    have h1 : Nat.card K = 1 := by rw [hK, pow_zero]
    have h2 := Finite.one_lt_card (α := K)
    omega
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hn)
  have : Fintype (RingAut K) := Fintype.ofFinite _
  by_contra h
  push Not at h
  have hle := IsCyclic.card_pow_eq_one_le (α := RingAut K) (n := 2) (by norm_num)
  have hsub : ({1, σ, δ} : Finset (RingAut K)) ⊆
      Finset.univ.filter fun a : RingAut K => a ^ 2 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    rcases hx with rfl | rfl | rfl
    · exact ⟨Finset.mem_univ _, one_pow 2⟩
    · exact ⟨Finset.mem_univ _, hσ2⟩
    · exact ⟨Finset.mem_univ _, hδ⟩
  have h3 : ({1, σ, δ} : Finset (RingAut K)).card = 3 :=
    Finset.card_eq_three.2 ⟨1, σ, δ, hσ1.symm, h.1.symm, h.2.symm, rfl⟩
  have := Finset.card_le_card hsub
  omega

theorem nonempty_derivedCentralQuotient_equiv
    {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}
    (hperf : ⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ = graphFixedRootGroup t K σ)
    (hZ : Subgroup.center (graphFixedRootGroup t K σ) = ⊥) :
    Nonempty (DerivedCentralQuotient (twistedFixedGroup t K σ) ≃* graphFixedRootGroup t K σ) := by
  set H := twistedFixedGroup t K σ
  set C := graphFixedRootGroup t K σ
  have hZ' : Subgroup.center ↥⁅H, H⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxC : (x : ModGL t.tag K) ∈ C := by
      rw [← hperf]
      exact x.2
    have hcen : (⟨x, hxC⟩ : C) ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyH : (y : ModGL t.tag K) ∈ ⁅H, H⁆ := by
        rw [hperf]
        exact y.2
      have h1 := congrArg (Subtype.val : ↥⁅H, H⁆ → ModGL t.tag K)
        (Subgroup.mem_center_iff.1 hx ⟨y, hyH⟩)
      exact Subtype.ext h1
    rw [hZ, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.2 (Subtype.ext (congrArg (Subtype.val : C → ModGL t.tag K) hcen))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ').trans
    (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr hperf))⟩

theorem exists_mulEquiv_graphFixedRootGroup_E6
    {G : Type} [Group G] {p f : ℕ}
    (h : ChevalleyExceptionalModel G .twistedE6 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (p ^ f) ^ 2 ∧
      (∀ c, σ c = c ^ (p ^ f)) ∧
      Nonempty (G ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  obtain ⟨hp, hf, -⟩ := h.1
  have hm : TwistedChevalleyModel G .E6 (p ^ f) := h.2
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields TwistTag.E6 hp hf K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 hp hf K hcard σ hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ'
  rw [hσσ'] at hZ
  obtain ⟨e'⟩ := nonempty_derivedCentralQuotient_equiv hperf hZ
  refine ⟨K, inferInstance, inferInstance, σ', hcard, hσ', ⟨?_⟩⟩
  rw [hσσ']
  exact e.trans e'

section NormalForm

variable {p f : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_normalForm_E6
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    ∃ g u δ, α = MulAut.conj g * normalActor σ u δ := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.E6.tag).length
  obtain ⟨c, β, hU, hV, rfl⟩ :=
    (exceptional_fixed_Sylow_opposition TwistTag.E6 K (ringChar K) σ w₀ hw₀).2.2.2.2.2 α
  obtain ⟨u, δ, rfl⟩ := exists_normalActor_eq_E6 hp hf hK σ hσ ⟨hU, hV⟩
  exact ⟨c, u, δ, rfl⟩

theorem delta_eq_of_normalForm_eq_E6
    {σ : K ≃+* K}
    (h0 : orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ = ⊤)
    {g g' : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    {u v : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ}
    {δ ε : K ≃+* K}
    (h : MulAut.conj g * normalActor σ u δ = MulAut.conj g' * normalActor σ v ε) : δ = ε := by
  have e : normalActor σ v ε * (normalActor σ u δ)⁻¹ = MulAut.conj (g'⁻¹ * g) := by
    have h' : normalActor σ v ε = (MulAut.conj g')⁻¹ * MulAut.conj g * normalActor σ u δ := by
      rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h', mul_inv_cancel_right, map_mul, map_inv]
  have hA : MulAut.conj (g'⁻¹ * g) ∈ graphFixedUnipotentStabilizer TwistTag.E6 K σ.toRingHom := by
    rw [← e]
    exact mul_mem (normalActor_mem σ v ε) (inv_mem (normalActor_mem σ u δ))
  obtain ⟨w, hw⟩ := exists_conj_eq_compatDiagAutHom σ.surjective hA
  have e2 : normalActor σ (w * u) δ = normalActor σ v ε := by
    change compatDiagAutHom TwistTag.E6 K σ.toRingHom (w * u) * fieldActor σ δ = _
    rw [map_mul, mul_assoc]
    change compatDiagAutHom TwistTag.E6 K σ.toRingHom w * normalActor σ u δ = _
    rw [← hw, ← e, inv_mul_cancel_right]
  exact eq_of_normalActor_eq_E6 h0 e2

end NormalForm

abbrev twistedE6RootGroup
    (K : Type) [Field K] (σ : K ≃+* K) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  graphFixedRootGroup TwistTag.E6 K σ.toRingHom

abbrev twistedE6Inn
    (K : Type) [Field K] (σ : K ≃+* K) :
    Subgroup (MulAut (twistedE6RootGroup K σ)) :=
  OuterAutomorphisms.inner (twistedE6RootGroup K σ)

abbrev twistedE6Diag
    (K : Type) [Field K] (σ : K ≃+* K) :
    Subgroup (MulAut (twistedE6RootGroup K σ)) :=
  (compatDiagAutHom TwistTag.E6 K σ.toRingHom).range

theorem twisted_E6_all_characteristic_exact_automorphism_normal_form
    {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ = ⊤ ∧
    orbitField TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ = ⊤ ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩ ↔ σ c = c) ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ ↔ σ c = c) ∧
    (∀ u, compatDiag TwistTag.E6 σ.toRingHom u =
      ![orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨0, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨3, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨1, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨2, by decide⟩),
        Units.map σ.toRingHom.toMonoidHom
          (orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨1, by decide⟩)),
        Units.map σ.toRingHom.toMonoidHom
          (orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨0, by decide⟩))]) ∧
    (∀ u (g : twistedE6RootGroup K σ),
      ((compatDiagAutHom TwistTag.E6 K σ.toRingHom u g : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) * g *
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹) ∧
    (∀ (δ : K ≃+* K) (g : twistedE6RootGroup K σ),
      ((fieldActor σ δ g : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        Units.map (entrywiseHom δ.toRingHom) g) ∧
    (∀ α : MulAut (twistedE6RootGroup K σ), ∃ g u δ,
      α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ δ) ∧
    (∃ Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K,
      (∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
        fieldActor σ δ → Θ α = δ) ∧
      Function.Surjective Θ ∧
      Θ.ker = twistedE6Inn K σ ⊔ twistedE6Diag K σ ∧
      (∀ a b : ↥(twistedE6Inn K σ ⊔ twistedE6Diag K σ) ⧸
          (twistedE6Inn K σ).subgroupOf (twistedE6Inn K σ ⊔ twistedE6Diag K σ), a * b = b * a) ∧
      (∀ a : ↥(twistedE6Inn K σ ⊔ twistedE6Diag K σ) ⧸
          (twistedE6Inn K σ).subgroupOf (twistedE6Inn K σ ⊔ twistedE6Diag K σ), a ^ 3 = 1) ∧
      ∀ α : MulAut (twistedE6RootGroup K σ), α ^ 2 = 1 →
        α ∈ twistedE6Inn K σ ∨ (Θ α = σ ∧ ∃ g u,
          α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ σ)) ∧
    (∀ g : twistedE6RootGroup K σ,
      ((fieldActor σ σ g : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) ∧
    ⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom, twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ =
      twistedE6RootGroup K σ ∧
    Subgroup.center (twistedE6RootGroup K σ) = ⊥ ∧
    Nonempty (DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ.toRingHom) ≃*
      twistedE6RootGroup K σ) ∧
    ∀ (G : Type) [Group G], ChevalleyExceptionalModel G .twistedE6 p f →
      ∃ (K' : Type) (_ : Field K') (_ : Finite K') (σ' : K' ≃+* K'),
        Nat.card K' = (p ^ f) ^ 2 ∧ (∀ c, σ' c = c ^ (p ^ f)) ∧
        Nonempty (G ≃* twistedE6RootGroup K' σ') := by
  obtain ⟨h0, h1top, h2, h3, hb, ⟨-, -, hcoe, -, -, -, -⟩, -, -, -, -, -, -, hcube⟩ :=
    twisted_E6_all_characteristic_compatible_diagonal_cubes hp K hK σ hσ
  obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 hp hf K hK
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
  rw [hσσ'] at hord
  have hσ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact absurd hord (by decide)
  have hσ2 : σ ^ 2 = 1 := by
    rw [← pow_orderOf_eq_one σ, hord]
    rfl
  have hK' : Nat.card K = p ^ (f * 2) := by rw [hK, ← pow_mul]
  choose gF uF δF hF using exists_normalForm_E6 hp hf hK σ hσ
  have hΘ : ∀ α g u δ, α = MulAut.conj g * normalActor σ u δ → δF α = δ :=
    fun α g u δ h => delta_eq_of_normalForm_eq_E6 h0 ((hF α).symm.trans h)
  have hmul : ∀ α β, δF (α * β) = δF α * δF β := by
    intro α β
    refine hΘ (α * β) (gF α * normalActor σ (uF α) (δF α) (gF β))
      (uF α * orbitUnitsMap σ.toRingHom (ringEquiv_comm_of_finite σ (δF α)) (uF β))
      (δF α * δF β) ?_
    calc α * β = MulAut.conj (gF α) * normalActor σ (uF α) (δF α) *
          (MulAut.conj (gF β) * normalActor σ (uF β) (δF β)) := by
          rw [← hF α, ← hF β]
      _ = MulAut.conj (gF α) * (normalActor σ (uF α) (δF α) * MulAut.conj (gF β)) *
          normalActor σ (uF β) (δF β) := by
          simp only [mul_assoc]
      _ = MulAut.conj (gF α) * (MulAut.conj (normalActor σ (uF α) (δF α) (gF β)) *
          normalActor σ (uF α) (δF α)) * normalActor σ (uF β) (δF β) := by
          rw [mulAut_mul_conj]
      _ = MulAut.conj (gF α * normalActor σ (uF α) (δF α) (gF β)) *
          (normalActor σ (uF α) (δF α) * normalActor σ (uF β) (δF β)) := by
          rw [map_mul]
          simp only [mul_assoc]
      _ = _ := by rw [normalActor_mul]
  let Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K := MonoidHom.mk' δF hmul
  have hker : Θ.ker = twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    apply le_antisymm
    · intro α hα
      have hδ : δF α = 1 := MonoidHom.mem_ker.1 hα
      rw [hF α, hδ, normalActor_one_right]
      exact mul_mem (Subgroup.mem_sup_left ⟨gF α, rfl⟩) (Subgroup.mem_sup_right ⟨uF α, rfl⟩)
    · refine sup_le ?_ ?_
      · rintro _ ⟨g, rfl⟩
        refine MonoidHom.mem_ker.2 (hΘ _ g 1 1 ?_)
        rw [normalActor_one_right, map_one, mul_one]
      · rintro _ ⟨u, rfl⟩
        refine MonoidHom.mem_ker.2 (hΘ _ 1 u 1 ?_)
        rw [normalActor_one_right, map_one, one_mul]
  have hmk : ∀ x ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ, ∃ u,
      (x : MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ) =
        (compatDiagAutHom TwistTag.E6 K σ.toRingHom u :
          MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ) := by
    intro x hx
    have hx' : x ∈ (twistedE6Inn K σ : Set (MulAut (twistedE6RootGroup K σ))) *
        (twistedE6Diag K σ : Set (MulAut (twistedE6RootGroup K σ))) := by
      rw [← Subgroup.normal_mul]
      exact hx
    obtain ⟨i, hi, d, ⟨u, rfl⟩, rfl⟩ := hx'
    refine ⟨u, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff i).2 hi, one_mul]
  have hcube' : ∀ u, ((compatDiagAutHom TwistTag.E6 K σ.toRingHom u ^ 3 :
      MulAut (twistedE6RootGroup K σ)) :
        MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ) = 1 := fun u => by
    obtain ⟨c, hc⟩ := hcube u
    rw [hc, QuotientGroup.eq_one_iff]
    exact ⟨c, rfl⟩
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 hp hf K hK σ.toRingHom hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  refine ⟨h0, h1top, h2, h3, hb, hcoe, fun δ g => rfl, fun α => ?_,
    ⟨Θ, fun α g u δ h => hΘ α g u δ (h.trans (mul_assoc _ _ _)), fun δ => ⟨fieldActor σ δ,
      hΘ _ 1 1 δ (by rw [map_one, one_mul, normalActor_one_left])⟩, hker, ?_, ?_, ?_⟩,
    ?_, hperf, hZ, nonempty_derivedCentralQuotient_equiv hperf hZ,
    fun G _ h => exists_mulEquiv_graphFixedRootGroup_E6 h⟩
  · exact ⟨gF α, uF α, δF α, (hF α).trans (mul_assoc _ _ _).symm⟩
  ·
    intro a b
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    obtain ⟨u, hu⟩ := hmk x x.2
    obtain ⟨v, hv⟩ := hmk y y.2
    have e : ((x * y : MulAut (twistedE6RootGroup K σ)) :
        MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ) =
          ((y * x : MulAut (twistedE6RootGroup K σ)) :
            MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hu, hv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, ← map_mul, ← map_mul, mul_comm u v]
    exact QuotientGroup.eq.1 e
  ·
    intro a
    induction a using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    obtain ⟨u, hu⟩ := hmk x x.2
    have e : ((x ^ 3 : MulAut (twistedE6RootGroup K σ)) :
        MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ) = 1 := by
      rw [QuotientGroup.mk_pow, hu, ← QuotientGroup.mk_pow]
      exact hcube' u
    exact (QuotientGroup.eq_one_iff _).1 e
  ·
    intro α hα2
    have hΘ2 : Θ α ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
    rcases eq_one_or_eq_of_sq_eq_one hp hK' hσ1 hσ2 hΘ2 with h1 | h1
    · left
      have hαN : α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
        rw [← hker]
        exact MonoidHom.mem_ker.2 h1
      obtain ⟨u, hu⟩ := hmk α hαN
      have e3 : (α : MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ) ^ 3 = 1 := by
        rw [hu, ← QuotientGroup.mk_pow]
        exact hcube' u
      have e2 : (α : MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ) ^ 2 = 1 := by
        rw [← QuotientGroup.mk_pow, hα2, QuotientGroup.mk_one]
      have e1 : (α : MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ) = 1 := by
        calc (α : MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ) =
            (α : MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ) ^ 3 *
              ((α : MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ) ^ 2)⁻¹ := by group
          _ = 1 := by rw [e3, e2, inv_one, one_mul]
      exact (QuotientGroup.eq_one_iff α).1 e1
    · right
      refine ⟨h1, gF α, uF α, ?_⟩
      have h1' : δF α = σ := h1
      have hα := hF α
      rw [h1'] at hα
      exact hα.trans (mul_assoc _ _ _).symm
  ·
    intro g
    have hP2 : diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K = 1 := by
      have h := diagramMap_pow_order TwistTag.E6 K
      rwa [show TwistTag.E6.order = 2 from rfl, pow_two] at h
    have hPinv : (diagramMap TwistTag.E6 K)⁻¹ = diagramMap TwistTag.E6 K :=
      (eq_inv_of_mul_eq_one_left hP2).symm
    have hgΓ := graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom g.2
    have hFix := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1 hgΓ).2
    rw [twistHom_apply] at hFix
    rw [coe_fieldActor]
    calc Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.E6.tag K) =
        (diagramMap TwistTag.E6 K)⁻¹ * (diagramMap TwistTag.E6 K *
          Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹) * diagramMap TwistTag.E6 K := by group
      _ = (diagramMap TwistTag.E6 K)⁻¹ * g * diagramMap TwistTag.E6 K := by rw [hFix]
      _ = diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ := by rw [hPinv]

end CFSG.LieType.Chevalley
