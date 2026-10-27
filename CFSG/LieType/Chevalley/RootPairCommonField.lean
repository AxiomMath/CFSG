module

public import CFSG.LieType.Chevalley.RankOneCentralImage
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem Tag.rank_pos (τ : Tag) : 0 < τ.rank := by
  cases τ <;> decide

theorem eq_of_cartan_edges
    {τ : Tag} {β : Type*} (σ : Fin τ.rank → β)
    (hedge : ∀ i j, τ.cartan i j = -1 → σ i = σ j) (i j : Fin τ.rank) : σ i = σ j := by
  suffices h : ∀ i, σ i = σ ⟨0, τ.rank_pos⟩ from (h i).trans (h j).symm
  have e : ∀ i j, τ.cartan i j = -1 → σ j = σ i := fun i j h => (hedge i j h).symm
  intro i
  cases τ
  · have e01 := e ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
    fin_cases i
    exacts [rfl, e01]
  · have e01 := e ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
    have e12 := e ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
    have e23 := e ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)
    fin_cases i
    exacts [rfl, e01, e12.trans e01, e23.trans (e12.trans e01)]
  · have e02 := e ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
    have e21 := e ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide)
    have e23 := e ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)
    fin_cases i
    exacts [rfl, e21.trans e02, e02, e23.trans e02]
  all_goals
    have e02 := e ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
    have e23 := e ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)
    have e31 := e ⟨3, by decide⟩ ⟨1, by decide⟩ (by decide)
    have e34 := e ⟨3, by decide⟩ ⟨4, by decide⟩ (by decide)
    have e45 := e ⟨4, by decide⟩ ⟨5, by decide⟩ (by decide)
  · fin_cases i
    exacts [rfl, e31.trans (e23.trans e02), e02, e23.trans e02, e34.trans (e23.trans e02),
      e45.trans (e34.trans (e23.trans e02))]
  · have e56 := e ⟨5, by decide⟩ ⟨6, by decide⟩ (by decide)
    fin_cases i
    exacts [rfl, e31.trans (e23.trans e02), e02, e23.trans e02, e34.trans (e23.trans e02),
      e45.trans (e34.trans (e23.trans e02)), e56.trans (e45.trans (e34.trans (e23.trans e02)))]
  · have e56 := e ⟨5, by decide⟩ ⟨6, by decide⟩ (by decide)
    have e67 := e ⟨6, by decide⟩ ⟨7, by decide⟩ (by decide)
    fin_cases i
    exacts [rfl, e31.trans (e23.trans e02), e02, e23.trans e02, e34.trans (e23.trans e02),
      e45.trans (e34.trans (e23.trans e02)), e56.trans (e45.trans (e34.trans (e23.trans e02))),
      e67.trans (e56.trans (e45.trans (e34.trans (e23.trans e02))))]

section RootPairs

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] def adjX
    (i : Fin τ.rank) (c : K) : adjointGroup τ K :=
  ⟨xUnit τ K i c, xUnit_mem_adjointGroup i c⟩

variable (τ K) in
@[expose] def adjY
    (i : Fin τ.rank) (c : K) : adjointGroup τ K :=
  ⟨yUnit τ K i c, yUnit_mem_adjointGroup i c⟩

variable (τ K) in
@[expose] def adjD
    (i : Fin τ.rank) (t : Kˣ) : adjointGroup τ K :=
  ⟨torusElt τ K i t, torusElt_mem_adjointGroup i t⟩

theorem adjX_injective
    (i : Fin τ.rank) : Function.Injective (adjX τ K i) := fun c d h =>
  xOp_injective i (by
    rw [← coe_xUnit, ← coe_xUnit]
    exact congrArg (fun g : adjointGroup τ K =>
      ((g : ModGL τ K) : Module.End K (RootModule τ K))) h)

theorem adjY_injective
    (i : Fin τ.rank) : Function.Injective (adjY τ K i) := fun c d h =>
  yOp_injective i (by
    rw [← coe_yUnit, ← coe_yUnit]
    exact congrArg (fun g : adjointGroup τ K =>
      ((g : ModGL τ K) : Module.End K (RootModule τ K))) h)

theorem rankOneRep_range_le
    (i : Fin τ.rank) :
    (exceptional_ordinary_rank_one_central_image τ K i).choose.range ≤ adjointGroup τ K := by
  rw [(exceptional_ordinary_rank_one_central_image τ K i).choose_spec.2.2.2.2.1]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]

variable (τ K) in
@[expose] def rankOneRep
    (i : Fin τ.rank) : SL(2, K) →* adjointGroup τ K :=
  (exceptional_ordinary_rank_one_central_image τ K i).choose.codRestrict (adjointGroup τ K)
    fun g => rankOneRep_range_le i ⟨g, rfl⟩

theorem rankOneRep_upper
    (i : Fin τ.rank) (c : K) :
    rankOneRep τ K i (sl2Upper K c) = adjX τ K i c :=
  Subtype.ext ((exceptional_ordinary_rank_one_central_image τ K i).choose_spec.1 c)

theorem rankOneRep_lower
    (i : Fin τ.rank) (c : K) :
    rankOneRep τ K i (sl2Lower K c) = adjY τ K i c :=
  Subtype.ext ((exceptional_ordinary_rank_one_central_image τ K i).choose_spec.2.1 c)

theorem rankOneRep_diag
    (i : Fin τ.rank) (t : Kˣ) :
    rankOneRep τ K i (sl2Diag K t) = adjD τ K i t :=
  Subtype.ext ((exceptional_ordinary_rank_one_central_image τ K i).choose_spec.2.2.1 t)

theorem rankOneRep_ker
    (i : Fin τ.rank) (g : SL(2, K)) (hg : rankOneRep τ K i g = 1) :
    ∃ l : Kˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨l, hl, hgl⟩ := (exceptional_ordinary_rank_one_central_image τ K i).choose_spec.2.2.2.2.2.1
    g (by rw [MonoidHom.mem_ker]; exact congrArg Subtype.val hg)
  exact ⟨l, Units.ext (by rw [Units.val_pow_eq_pow_val, hl, Units.val_one]), hgl⟩

theorem sl2RootX_rankOneRep
    (i : Fin τ.rank) :
    sl2RootX (rankOneRep τ K i) = simplePosSubgroup τ K i := by
  ext g
  rw [mem_sl2RootX, mem_simplePosSubgroup]
  simp only [rankOneRep_upper]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc.symm⟩

theorem sl2RootY_rankOneRep
    (i : Fin τ.rank) :
    sl2RootY (rankOneRep τ K i) = simpleNegSubgroup τ K i := by
  ext g
  rw [mem_sl2RootY, mem_simpleNegSubgroup]
  simp only [rankOneRep_lower]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc.symm⟩

theorem exists_rankOne_params
    [Finite K] {α : MulAut (adjointGroup τ K)} {i : Fin τ.rank}
    (hα : α ∈ pairAutSubgroup (simplePosSubgroup τ K i) (simpleNegSubgroup τ K i)) :
    ∃ (a : Kˣ) (σ : K ≃+* K), (∀ c, α (adjX τ K i c) = adjX τ K i (a * σ c)) ∧
      (∀ c, α (adjY τ K i c) = adjY τ K i (((a⁻¹ : Kˣ) : K) * σ c)) ∧
      ∀ t, α (adjD τ K i t) = adjD τ K i (Units.map σ.toMonoidHom t) := by
  rw [← sl2RootX_rankOneRep, ← sl2RootY_rankOneRep] at hα
  choose f hf using exists_sl2Upper_param hα
  choose g hg using exists_sl2Lower_param hα
  obtain ⟨a, σ, hfa, hga, hh⟩ := exists_semilinear_params (rankOneRep_ker i) hα hf hg
  refine ⟨a, σ, fun c => ?_, fun c => ?_, fun t => ?_⟩
  · rw [← rankOneRep_upper, hf, hfa, rankOneRep_upper]
  · rw [← rankOneRep_lower, hg, hga, rankOneRep_lower]
  · rw [← rankOneRep_diag, hh, rankOneRep_diag]

theorem ringEquiv_eq_of_cartan
    {α : MulAut (adjointGroup τ K)} {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) {a : Kˣ} {σi σj : K ≃+* K}
    (hx : ∀ c, α (adjX τ K j c) = adjX τ K j (a * σj c))
    (hd : ∀ t, α (adjD τ K i t) = adjD τ K i (Units.map σi.toMonoidHom t)) : σi = σj := by
  have hconj : ∀ (t : Kˣ) (c : K), adjD τ K i t * adjX τ K j c * (adjD τ K i t)⁻¹ =
      adjX τ K j (((t⁻¹ : Kˣ) : K) * c) := fun t c => by
    apply Subtype.ext
    change torusElt τ K i t * xUnit τ K j c * (torusElt τ K i t)⁻¹ = _
    rw [(simple_torus_root_conjugation τ K i j t c).1, hij, zpow_neg, zpow_one]
    rfl
  refine RingEquiv.ext fun c => ?_
  by_cases hc : c = 0
  · rw [hc, map_zero, map_zero]
  have h1 := congrArg α (hconj (Units.mk0 c hc) 1)
  simp only [map_mul, map_inv, hd, hx, map_one, mul_one] at h1
  rw [hconj] at h1
  have h2 := adjX_injective j h1
  simp only [Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, MonoidHom.coe_ofClass, RingHom.coe_coe, Units.val_mk0,
    map_inv₀] at h2
  have h3 : (σi c)⁻¹ = (σj c)⁻¹ := by
    rw [mul_comm] at h2
    exact mul_left_cancel₀ a.ne_zero h2
  exact inv_injective h3

variable (τ K) in
@[expose] def rootPairAut
    : Subgroup (MulAut (adjointGroup τ K)) :=
  ⨅ i, pairAutSubgroup (simplePosSubgroup τ K i) (simpleNegSubgroup τ K i)

theorem mem_rootPairAut
    {α : MulAut (adjointGroup τ K)} :
    α ∈ rootPairAut τ K ↔
      ∀ i, α ∈ pairAutSubgroup (simplePosSubgroup τ K i) (simpleNegSubgroup τ K i) :=
  Subgroup.mem_iInf

theorem exists_common_params
    [Finite K] {α : MulAut (adjointGroup τ K)}
    (hα : α ∈ rootPairAut τ K) :
    ∃ p : (Fin τ.rank → Kˣ) × (K ≃+* K), ∀ i,
      (∀ c, α (adjX τ K i c) = adjX τ K i (p.1 i * p.2 c)) ∧
      (∀ c, α (adjY τ K i c) = adjY τ K i (((p.1 i)⁻¹ : Kˣ) * p.2 c)) ∧
      ∀ t, α (adjD τ K i t) = adjD τ K i (Units.map p.2.toMonoidHom t) := by
  choose a σ hx hy hd using fun i => exists_rankOne_params (mem_rootPairAut.1 hα i)
  have hσ : ∀ i j, σ i = σ j :=
    eq_of_cartan_edges σ fun i j hij => ringEquiv_eq_of_cartan hij (hx j) (hd i)
  refine ⟨(a, σ ⟨0, τ.rank_pos⟩), fun i => ?_⟩
  simp only
  rw [← hσ i]
  exact ⟨hx i, hy i, hd i⟩

theorem common_params_unique
    {α : MulAut (adjointGroup τ K)}
    {p q : (Fin τ.rank → Kˣ) × (K ≃+* K)}
    (hp : ∀ i c, α (adjX τ K i c) = adjX τ K i (p.1 i * p.2 c))
    (hq : ∀ i c, α (adjX τ K i c) = adjX τ K i (q.1 i * q.2 c)) : p = q := by
  have e : ∀ i c, (p.1 i : K) * p.2 c = q.1 i * q.2 c := fun i c =>
    adjX_injective i ((hp i c).symm.trans (hq i c))
  have h1 : p.1 = q.1 := funext fun i => Units.ext (by simpa using e i 1)
  have h2 : p.2 = q.2 := RingEquiv.ext fun c => by
    have := e ⟨0, τ.rank_pos⟩ c
    rw [h1] at this
    exact mul_left_cancel₀ (q.1 _).ne_zero this
  exact Prod.ext h1 h2

variable (τ K) in
@[expose] noncomputable def commonParams
    [Finite K] (α : rootPairAut τ K) :
    (Fin τ.rank → Kˣ) × (K ≃+* K) :=
  (exists_common_params α.2).choose

theorem commonParams_spec
    [Finite K] (α : rootPairAut τ K) (i : Fin τ.rank) :
    (∀ c, (α : MulAut (adjointGroup τ K)) (adjX τ K i c) =
        adjX τ K i ((commonParams τ K α).1 i * (commonParams τ K α).2 c)) ∧
      (∀ c, (α : MulAut (adjointGroup τ K)) (adjY τ K i c) =
        adjY τ K i ((((commonParams τ K α).1 i)⁻¹ : Kˣ) * (commonParams τ K α).2 c)) ∧
      ∀ t, (α : MulAut (adjointGroup τ K)) (adjD τ K i t) =
        adjD τ K i (Units.map (commonParams τ K α).2.toMonoidHom t) :=
  (exists_common_params α.2).choose_spec i

theorem commonParams_mul
    [Finite K] (α β : rootPairAut τ K) :
    commonParams τ K (α * β) =
      (fun i => (commonParams τ K α).1 i *
        Units.map (commonParams τ K α).2.toMonoidHom ((commonParams τ K β).1 i),
        (commonParams τ K α).2 * (commonParams τ K β).2) := by
  refine common_params_unique (fun i c => (commonParams_spec (α * β) i).1 c) fun i c => ?_
  rw [Subgroup.coe_mul, MulAut.mul_apply, (commonParams_spec β i).1, (commonParams_spec α i).1]
  congr 1
  simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, MonoidHom.coe_ofClass, RingHom.coe_coe, map_mul, mul_assoc]
  rfl

theorem mulAut_eq_one_of_fix
    {α : MulAut (adjointGroup τ K)}
    (hx : ∀ i c, α (adjX τ K i c) = adjX τ K i c) (hy : ∀ i c, α (adjY τ K i c) = adjY τ K i c) :
    α = 1 := by
  have h := MonoidHom.eq_of_eqOn_dense (Subgroup.closure_closure_coe_preimage
      (k := {g : ModGL τ K | ∃ (i : Fin τ.rank) (c : K),
        (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
          (g : Module.End K (RootModule τ K)) = yOp τ K i c}))
    (f := α.toMonoidHom) (g := MonoidHom.id _) (fun g hg => by
      obtain ⟨i, c, hc | hc⟩ := hg
      · have e : g = adjX τ K i c := Subtype.ext (Units.ext (hc.trans (coe_xUnit i c).symm))
        rw [e]
        exact hx i c
      · have e : g = adjY τ K i c := Subtype.ext (Units.ext (hc.trans (coe_yUnit i c).symm))
        rw [e]
        exact hy i c)
  exact MulEquiv.ext fun g => DFunLike.congr_fun h g

theorem ringAut_isCyclic [Finite K] : IsCyclic (RingAut K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hK⟩ := FiniteField.card' K
  exact (card_ringAut_and_isCyclic hp K (by rw [Nat.card_eq_fintype_card, hK])).2

theorem ordinary_Chevalley_root_pair_common_field_parameter
    (τ : Tag) (K : Type) [Field K]
    [Finite K] :
    (∀ α ∈ rootPairAut τ K, ∃! p : (Fin τ.rank → Kˣ) × (K ≃+* K), ∀ i,
      (∀ c, α (adjX τ K i c) = adjX τ K i (p.1 i * p.2 c)) ∧
      (∀ c, α (adjY τ K i c) = adjY τ K i (((p.1 i)⁻¹ : Kˣ) * p.2 c)) ∧
      ∀ t, α (adjD τ K i t) = adjD τ K i (Units.map p.2.toMonoidHom t)) ∧
    ∃ δ : rootPairAut τ K →* RingAut K,
      (∀ (α : rootPairAut τ K) (p : (Fin τ.rank → Kˣ) × (K ≃+* K)),
        (∀ i c, (α : MulAut (adjointGroup τ K)) (adjX τ K i c) = adjX τ K i (p.1 i * p.2 c)) →
          δ α = p.2) ∧
      IsCyclic δ.range ∧
      ∃ ε : δ.ker →* (Fin τ.rank → Kˣ), Function.Injective ε ∧
        (∀ (α : δ.ker) (p : (Fin τ.rank → Kˣ) × (K ≃+* K)),
          (∀ i c, ((α : rootPairAut τ K) : MulAut (adjointGroup τ K)) (adjX τ K i c) =
            adjX τ K i (p.1 i * p.2 c)) → ε α = p.1) ∧
        Nat.card δ.ker ∣ (Nat.card K - 1) ^ τ.rank := by
  refine ⟨fun α hα => ?_, ?_⟩
  · obtain ⟨p, hp⟩ := exists_common_params hα
    exact ⟨p, hp, fun q hq => common_params_unique (fun i => (hq i).1) (fun i => (hp i).1)⟩
  have hparam : ∀ (α : rootPairAut τ K) (p : (Fin τ.rank → Kˣ) × (K ≃+* K)),
      (∀ i c, (α : MulAut (adjointGroup τ K)) (adjX τ K i c) = adjX τ K i (p.1 i * p.2 c)) →
        commonParams τ K α = p := fun α p hp =>
    common_params_unique (fun i => (commonParams_spec α i).1) hp
  let δ : rootPairAut τ K →* RingAut K :=
    { toFun := fun α => (commonParams τ K α).2
      map_one' := by
        have := hparam 1 (fun _ => 1, RingEquiv.refl K) fun i c => by simp
        rw [this]
        rfl
      map_mul' := fun α β => by rw [commonParams_mul] }
  have hδ : ∀ α, δ α = (commonParams τ K α).2 := fun _ => rfl
  have : IsCyclic (RingAut K) := ringAut_isCyclic
  have hker : ∀ α : δ.ker, (commonParams τ K α).2 = 1 := fun α => α.2
  let ε : δ.ker →* (Fin τ.rank → Kˣ) :=
    { toFun := fun α => (commonParams τ K α).1
      map_one' := by
        have := hparam 1 (fun _ => 1, RingEquiv.refl K) fun i c => by simp
        change (commonParams τ K 1).1 = 1
        rw [this]
        rfl
      map_mul' := fun α β => by
        change (commonParams τ K ((α : rootPairAut τ K) * β)).1 = _
        rw [commonParams_mul, hker α]
        funext i
        exact Units.ext (by simp) }
  have hinj : Function.Injective ε := by
    rw [injective_iff_map_eq_one]
    intro α hα
    have ha : (commonParams τ K α.1).1 = 1 := hα
    have hσ := hker α
    refine Subtype.ext (Subtype.ext (mulAut_eq_one_of_fix (fun i c => ?_) fun i c => ?_))
    · rw [(commonParams_spec α.1 i).1, ha, hσ]
      simp
    · rw [(commonParams_spec α.1 i).2.1, ha, hσ]
      simp
  refine ⟨δ, fun α p hp => by rw [hδ, hparam α p hp], inferInstance, ε, hinj,
    fun α p hp => by change (commonParams τ K α).1 = p.1; rw [hparam α p hp], ?_⟩
  have h := Subgroup.card_dvd_of_injective ε hinj
  rwa [Nat.card_fun, Nat.card_units, Nat.card_eq_fintype_card (α := Fin τ.rank),
    Fintype.card_fin] at h

end RootPairs

end CFSG.LieType.Chevalley
