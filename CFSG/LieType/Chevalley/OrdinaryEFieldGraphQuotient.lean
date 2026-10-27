module

public import CFSG.LieType.Chevalley.ExactNormalFormE
public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem exactPerm_add (τ : Tag) (m n : ℕ) :
    exactPerm τ (m + n) = exactPerm τ m * exactPerm τ n := by
  cases τ
  case E6 => exact pow_add (TwistTag.E6.perm : Equiv.Perm (Fin Tag.E6.rank)) m n
  all_goals exact (mul_one 1).symm

theorem exactPerm_zero (τ : Tag) : exactPerm τ 0 = 1 := by
  cases τ
  case E6 => exact pow_zero (TwistTag.E6.perm : Equiv.Perm (Fin Tag.E6.rank))
  all_goals rfl

theorem exactQ_zero (τ : Tag) (K : Type) [Field K] : exactQ τ K 0 = 1 := by
  cases τ
  case E6 => exact pow_zero (diagramMap .E6 K : ModGL Tag.E6 K)
  all_goals rfl

theorem exactQ_mod
    (τ : Tag) (K : Type) [Field K] (n : ℕ) :
    exactQ τ K (n % exactE τ) = exactQ τ K n := by
  cases τ
  case E6 =>
    have hP2 : (diagramMap .E6 K : ModGL Tag.E6 K) ^ 2 = 1 := diagramMap_pow_order TwistTag.E6 K
    change (diagramMap .E6 K : ModGL Tag.E6 K) ^ (n % 2) = (diagramMap .E6 K : ModGL Tag.E6 K) ^ n
    conv_rhs => rw [← Nat.mod_add_div n 2]
    rw [pow_add, pow_mul, hP2, one_pow, mul_one]
  all_goals rfl

theorem exactE_pos (τ : Tag) : 0 < exactE τ := by
  cases τ <;> simp [exactE]

theorem exactNormalAut_mod
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (n : ℕ) :
    exactNormalAut τ K a σ (n % exactE τ) = exactNormalAut τ K a σ n :=
  MulEquiv.ext fun h => Subtype.ext (by rw [coe_exactNormalAut, coe_exactNormalAut, exactQ_mod])

theorem exactNormalAut_mul
    (a a' : Fin τ.rank → Kˣ) (σ σ' : K ≃+* K) (ε ε' : ℕ) :
    exactNormalAut τ K a σ ε * exactNormalAut τ K a' σ' ε' =
      exactNormalAut τ K
        (fun j => a j * Units.map σ.toRingHom.toMonoidHom (a' ((exactPerm τ ε).symm j)))
        (σ * σ') (ε + ε') := by
  refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
  · rw [MulAut.mul_apply, exactNormalAut_adjX, exactNormalAut_adjX, exactNormalAut_adjX,
      exactPerm_add, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
    congr 1
    rw [Units.val_mul, Units.coe_map, map_mul, mul_assoc]
    rfl
  · rw [MulAut.mul_apply, exactNormalAut_adjY, exactNormalAut_adjY, exactNormalAut_adjY,
      exactPerm_add, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
    congr 1
    simp only [mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map,
      RingEquiv.toRingHom_eq_coe, map_mul, map_inv₀, RingAut.mul_apply, mul_assoc]
    rfl

theorem exactNormalAut_diag_mul
    (b a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    exactNormalAut τ K b 1 0 * exactNormalAut τ K a σ ε = exactNormalAut τ K (b * a) σ ε := by
  refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
  · rw [MulAut.mul_apply, exactNormalAut_adjX, exactNormalAut_adjX, exactNormalAut_adjX,
      exactPerm_zero, Equiv.Perm.one_apply, Pi.mul_apply, Units.val_mul, mul_assoc]
    rfl
  · rw [MulAut.mul_apply, exactNormalAut_adjY, exactNormalAut_adjY, exactNormalAut_adjY,
      exactPerm_zero, Equiv.Perm.one_apply, Pi.mul_apply, mul_inv, Units.val_mul, mul_assoc]
    rfl

theorem exists_conj_eq_exactNormalAut_diag
    {h : adjointGroup τ K}
    (hA : MulAut.conj h ∈ unipotentPairAut τ K) :
    ∃ b, MulAut.conj h = exactNormalAut τ K b 1 0 := by
  obtain ⟨hU, hV⟩ := hA
  have hNU := mem_normalizer_of_map_conj_subgroupOf posUnipotent_le_adjointGroup hU
  have hNV := mem_normalizer_of_map_conj_subgroupOf negUnipotent_le_adjointGroup hV
  have hB : (h : ModGL τ K) ∈ borelGroup τ K := by
    rw [← (borel_self_normalizers τ K).1]
    exact Subgroup.mem_inf.2 ⟨h.2, hNU⟩
  have hB' : (h : ModGL τ K) ∈ oppositeBorel τ K := by
    rw [← oppositeBorel_normalizer τ K]
    exact Subgroup.mem_inf.2 ⟨h.2, hNV⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  have hT : (h : ModGL τ K) ∈ torusGroup τ K := by
    rw [← (opposite_Borel_intersection τ K w₀ hw₀).2.2.1]
    exact Subgroup.mem_inf.2 ⟨hB, hB'⟩
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  refine ⟨b, MulEquiv.ext fun g => Subtype.ext ?_⟩
  rw [coe_exactNormalAut, exactQ_zero, inv_one, mul_one, mul_one, ← hb]
  change (h : ModGL τ K) * g * (h : ModGL τ K)⁻¹ = _
  congr 2
  exact (Units.ext (entrywise_id _)).symm

theorem exists_conj_mul_exactNormalAut
    [Finite K] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (α : MulAut (adjointGroup τ K)) :
    ∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : Fin (exactE τ)),
      α = MulAut.conj g * exactNormalAut τ K a σ ε := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  obtain ⟨c, β, hU, hV, rfl⟩ :=
    (exceptional_ordinary_Sylow_opposition τ K (ringChar K) w₀ hw₀).2.2.2.2.2 α
  obtain ⟨a, σ, ε, rfl⟩ := exists_exactNormalAut_eq hτ (show β ∈ unipotentPairAut τ K from
    ⟨hU, hV⟩)
  exact ⟨c, a, σ, ε, rfl⟩

theorem params_eq_of_conj_mul_exactNormalAut_eq
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {g g' : adjointGroup τ K} {a a' : Fin τ.rank → Kˣ} {σ σ' : K ≃+* K}
    {ε ε' : Fin (exactE τ)}
    (h : MulAut.conj g * exactNormalAut τ K a σ ε = MulAut.conj g' * exactNormalAut τ K a' σ' ε') :
    σ = σ' ∧ ε = ε' := by
  have e : exactNormalAut τ K a' σ' ε' * (exactNormalAut τ K a σ ε)⁻¹ =
      MulAut.conj (g'⁻¹ * g) := by
    have h' : exactNormalAut τ K a' σ' ε' =
        (MulAut.conj g')⁻¹ * MulAut.conj g * exactNormalAut τ K a σ ε := by
      rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h', mul_inv_cancel_right, map_mul, map_inv]
  have hA : MulAut.conj (g'⁻¹ * g) ∈ unipotentPairAut τ K := by
    rw [← e]
    exact mul_mem (exactNormalAut_mem _ _ _) (inv_mem (exactNormalAut_mem _ _ _))
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag hA
  have e2 : exactNormalAut τ K (b * a) σ ε = exactNormalAut τ K a' σ' ε' := by
    rw [← exactNormalAut_diag_mul, ← hb, ← e, inv_mul_cancel_right]
  have := exactNormalAut_injective hτ e2
  exact ⟨congrArg (fun x => x.2.1) this, congrArg (fun x => x.2.2) this⟩

theorem ringAut_pow_apply_of_frobenius {p : ℕ} {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ p) (n : ℕ)
    (c : K) : (φ ^ n) c = c ^ (p ^ n) := by
  induction n with
  | zero => rw [pow_zero, RingAut.one_apply, pow_zero, pow_one]
  | succ n ih => rw [pow_succ', RingAut.mul_apply, ih, hφ, ← pow_mul, ← pow_succ]

theorem ringEquiv_sq_eq_one_facts [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    Even f ∧ (∀ c, σ c = c ^ (p ^ (f / 2))) ∧ Nat.card {c : K // σ c = c} = p ^ (f / 2) := by
  obtain ⟨φ, hφ, hord, -, -, hfix⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
  have hσord : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  obtain ⟨hdvd, S, hS, hcardS⟩ := hfix (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσord] at hdvd hcardS
  have hev : Even f := even_iff_two_dvd.2 hdvd
  obtain ⟨h, hh⟩ := hev
  have hf2 : f / 2 = h := by omega
  have hSσ : (S : Set K) = {c | σ c = c} := by
    rw [hS]
    ext c
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hc
      exact hc σ (Subgroup.mem_zpowers σ)
    · intro hc τ hτ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hτ
      have hpow : ∀ m : ℕ, (σ ^ m) c = c := by
        intro m
        induction m with
        | zero => rw [pow_zero, RingAut.one_apply]
        | succ m ih => rw [pow_succ', RingAut.mul_apply, ih, hc]
      have hfin : IsOfFinOrder σ := orderOf_pos_iff.1 (by rw [hσord]; norm_num)
      obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1
        (hfin.mem_powers_iff_mem_zpowers.2 (Subgroup.zpow_mem_zpowers σ n))
      rw [← hm]
      exact hpow m
  have hcard : Nat.card {c : K // σ c = c} = p ^ (f / 2) := by
    rw [← hcardS]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
    rw [← SetLike.mem_coe, hSσ]
    exact Iff.rfl
  have hφh1 : φ ^ h ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at this
    have hh0 : 0 < h := by omega
    exact absurd (Nat.le_of_dvd hh0 this) (by omega)
  have hφh2 : (φ ^ h) ^ 2 = 1 := by
    rw [← pow_mul, show h * 2 = f by omega, ← hord, pow_orderOf_eq_one]
  have hK' : Nat.card K = p ^ f := hK
  rcases eq_one_or_eq_of_sq_eq_one hp hK' hφh1 hφh2 hσ2 with h1 | h1
  · exact absurd h1 hσ1
  · refine ⟨⟨h, hh⟩, fun c => ?_, hcard⟩
    rw [h1, ringAut_pow_apply_of_frobenius hφ, hf2]

theorem eq_conj_mul_exactNormalAut_of_apply
    {α : MulAut (adjointGroup τ K)}
    {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ}
    (hα : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      exactQ τ K ε * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (exactQ τ K ε)⁻¹ *
        (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) :
    α = MulAut.conj g * exactNormalAut τ K a σ ε := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [hα h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_exactNormalAut, Subgroup.coe_inv]
  simp only [mul_assoc]

theorem ordinary_E_field_graph_quotient_and_involutions
    (τ : Tag)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K] :
    ∃ Θ : MulAut (adjointGroup τ K) →* RingAut K × Multiplicative (ZMod (exactE τ)),
      Function.Surjective Θ ∧
      (∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ)
        (σ : K ≃+* K) (ε : Fin (exactE τ)),
        (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
          exactQ τ K ε * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
            (exactQ τ K ε)⁻¹ * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) →
        Θ α = (σ, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE τ)))) ∧
      (∀ α : MulAut (adjointGroup τ K), α ∈ Θ.ker ↔
        ∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ), ∀ h : adjointGroup τ K,
          (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a * (h : ModGL τ K) *
            (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) ∧
      (∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ)
        (σ : K ≃+* K) (ε : Fin (exactE τ)),
        (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
          exactQ τ K ε * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
            (exactQ τ K ε)⁻¹ * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) →
        α ^ 2 = 1 → σ ^ 2 = 1) ∧
      ∀ p f : ℕ, p.Prime → 1 ≤ f → Nat.card K = p ^ f → ∀ σ : K ≃+* K, σ ^ 2 = 1 → σ ≠ 1 →
        Even f ∧ (∀ c, σ c = c ^ (p ^ (f / 2))) ∧ Nat.card {c : K // σ c = c} = p ^ (f / 2) := by
  have : NeZero (exactE τ) := ⟨(exactE_pos τ).ne'⟩
  choose gF aF σF εF hF using exists_conj_mul_exactNormalAut (K := K) hτ
  have hΘ : ∀ α g a σ (ε : Fin (exactE τ)), α = MulAut.conj g * exactNormalAut τ K a σ ε →
      σF α = σ ∧ εF α = ε := fun α g a σ ε h =>
    params_eq_of_conj_mul_exactNormalAut_eq hτ ((hF α).symm.trans h)
  let F : MulAut (adjointGroup τ K) → RingAut K × Multiplicative (ZMod (exactE τ)) :=
    fun α => (σF α, Multiplicative.ofAdd (((εF α : ℕ) : ZMod (exactE τ))))
  have hmul : ∀ α β, F (α * β) = F α * F β := by
    intro α β
    have e : α * β = MulAut.conj (gF α * exactNormalAut τ K (aF α) (σF α) (εF α) (gF β)) *
        exactNormalAut τ K
          (fun j => aF α j * Units.map (σF α).toRingHom.toMonoidHom
            (aF β ((exactPerm τ (εF α)).symm j)))
          (σF α * σF β) (⟨((εF α : ℕ) + εF β) % exactE τ, Nat.mod_lt _ (exactE_pos τ)⟩ :
            Fin (exactE τ)) := by
      calc α * β = MulAut.conj (gF α) * exactNormalAut τ K (aF α) (σF α) (εF α) *
            (MulAut.conj (gF β) * exactNormalAut τ K (aF β) (σF β) (εF β)) := by
            rw [← hF α, ← hF β]
        _ = MulAut.conj (gF α) * (exactNormalAut τ K (aF α) (σF α) (εF α) *
            MulAut.conj (gF β)) * exactNormalAut τ K (aF β) (σF β) (εF β) := by
            simp only [mul_assoc]
        _ = MulAut.conj (gF α) * (MulAut.conj (exactNormalAut τ K (aF α) (σF α) (εF α) (gF β)) *
            exactNormalAut τ K (aF α) (σF α) (εF α)) *
              exactNormalAut τ K (aF β) (σF β) (εF β) := by
            rw [mulAut_mul_conj]
        _ = MulAut.conj (gF α * exactNormalAut τ K (aF α) (σF α) (εF α) (gF β)) *
            (exactNormalAut τ K (aF α) (σF α) (εF α) *
              exactNormalAut τ K (aF β) (σF β) (εF β)) := by
            rw [map_mul]
            simp only [mul_assoc]
        _ = _ := by
            rw [exactNormalAut_mul]
            exact congrArg _ (exactNormalAut_mod _ _ _).symm
    obtain ⟨h1, h2⟩ := hΘ _ _ _ _ _ e
    simp only [F, h1, h2, Prod.mk_mul_mk]
    congr 1
    rw [← ofAdd_add, ZMod.natCast_mod, Nat.cast_add]
  let Θ : MulAut (adjointGroup τ K) →* RingAut K × Multiplicative (ZMod (exactE τ)) :=
    MonoidHom.mk' F hmul
  have hexpr : ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ)
      (σ : K ≃+* K) (ε : Fin (exactE τ)),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        exactQ τ K ε * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
          (exactQ τ K ε)⁻¹ * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) →
      Θ α = (σ, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE τ))) := by
    intro α g a σ ε hα
    obtain ⟨h1, h2⟩ := hΘ α g a σ ε (eq_conj_mul_exactNormalAut_of_apply hα)
    change (σF α, _) = _
    rw [h1, h2]
  refine ⟨Θ, fun x => ?_, hexpr, fun α => ⟨fun hα => ?_, fun ⟨g, a, hα⟩ => ?_⟩,
    fun α g a σ ε hα h2 => ?_, fun p f hp hf hK σ h2 h1 => ringEquiv_sq_eq_one_facts hp hf hK h2 h1⟩
  ·
    obtain ⟨δ, w⟩ := x
    refine ⟨exactNormalAut τ K 1 δ (⟨(Multiplicative.toAdd w).val, ZMod.val_lt _⟩ :
      Fin (exactE τ)), ?_⟩
    rw [hexpr _ 1 1 δ _ fun h => by
      rw [coe_exactNormalAut, Subgroup.coe_one, inv_one, mul_one, one_mul]]
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, ofAdd_toAdd]
  ·
    have hα' : F α = 1 := MonoidHom.mem_ker.1 hα
    have h1 : σF α = 1 := congrArg Prod.fst hα'
    have h2 : (((εF α : ℕ) : ZMod (exactE τ))) = 0 :=
      congrArg (fun x => Multiplicative.toAdd x.2) hα'
    have h3 : (εF α : ℕ) = 0 :=
      Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).1 h2) (εF α).2
    refine ⟨gF α, aF α, fun h => ?_⟩
    conv_lhs => rw [hF α]
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_exactNormalAut, h1, h3, exactQ_zero, Subgroup.coe_inv, inv_one, mul_one, mul_one]
    rw [show Units.map (entrywiseHom (1 : RingAut K).toRingHom) (h : ModGL τ K) = h from
      Units.ext (entrywise_id _)]
    simp only [mul_assoc]
  ·
    refine MonoidHom.mem_ker.2 ?_
    have h := hexpr α g a 1 ⟨0, exactE_pos τ⟩ fun h => by
      rw [hα h, exactQ_zero, inv_one, mul_one, mul_one,
        show Units.map (entrywiseHom (1 : RingAut K).toRingHom) (h : ModGL τ K) = h from
          Units.ext (entrywise_id _)]
    rw [h, Prod.mk_eq_one]
    exact ⟨rfl, by rw [Fin.val_mk, Nat.cast_zero, ofAdd_zero]⟩
  ·
    have hΘα := hexpr α g a σ ε hα
    have hsq : Θ α ^ 2 = 1 := by rw [← map_pow, h2, map_one]
    rw [hΘα] at hsq
    exact congrArg Prod.fst hsq

end CFSG.LieType.Chevalley
