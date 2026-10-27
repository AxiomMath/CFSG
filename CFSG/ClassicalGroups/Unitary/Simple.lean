module

public import CFSG.ClassicalGroups.Unitary.Action
public import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_12

public noncomputable section

namespace CFSG.ClassicalGroups.Unitary

open Matrix CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def tvHom (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {a : Fin n → K} (ha : herm σ a a = 0) :
    Multiplicative (traceZero σ) →* SUid σ n where
  toFun c := tv hσ ha ((mem_traceZero σ).mp c.toAdd.2)
  map_one' := ext_smul _ fun v => by
    rw [tv_smul, one_smul]
    simp
  map_mul' c d := ext_smul _ fun v => by
    rw [mul_smul, tv_smul, tv_smul, tv_smul]
    simp only [toAdd_mul, AddSubgroup.coe_add, herm_add_right, herm_smul_right, ha, mul_zero,
      add_zero]
    module

theorem tvHom_smul (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {a : Fin n → K} (ha : herm σ a a = 0)
    (c : Multiplicative (traceZero σ)) (v : Fin n → K) :
    tvHom hσ ha c • v = v + ((c.toAdd : K) * herm σ a v) • a := by
  change tv hσ ha ((mem_traceZero σ).mp c.toAdd.2) • v = _
  exact tv_smul hσ ha _ v

theorem isSimpleGroup_statedProj_SUid (hσ : IsUnitaryInvolution σ) {n : ℕ} (hn : 3 ≤ n)
    (h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) :
    IsSimpleGroup (StatedProj (SUid σ n)) := by
  obtain ⟨W⟩ := hσ.nonempty_wittData
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let G := SUid σ (m + 2)
  let X := isoPts σ (m + 2)
  let Z := (StatedScalars (Fin (m + 2)) K).subgroupOf G
  let P := StatedProj G
  have hZ : Z ≤ (MulAction.toPermHom G X).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    exact Equiv.ext fun x => smul_eq_of_mem_scalars hg x
  let ρ : P →* Equiv.Perm X := QuotientGroup.lift Z (MulAction.toPermHom G X) hZ
  let _ : MulAction P X := MulAction.compHom X ρ
  have hsmul : ∀ (g : G) (x : X), ((g : P)) • x = g • x := fun _ _ => rfl
  have : FaithfulSMul P X := faithfulSMul_iff.mpr (by
    intro p hp
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
    rw [QuotientGroup.eq_one_iff]
    exact mem_scalars_of_smul_eq hσ hn fun x => hp x)
  have : MulAction.IsPreprimitive G X := isPreprimitive_isoPts hσ hn
  have : MulAction.IsPreprimitive P X :=
    MulAction.IsPreprimitive.of_surjective
      (f := (⟨id, fun _ _ => rfl⟩ : X →ₑ[(QuotientGroup.mk : G → P)] X)) Function.surjective_id
  set a₀ := W.hypA m with ha₀def
  set b₀ := W.hypB m with hb₀def
  have ha₀ : herm σ a₀ a₀ = 0 := W.herm_hypA_hypA
  have hb₀ : herm σ b₀ b₀ = 0 := W.herm_hypB_hypB
  have hab₀ : herm σ a₀ b₀ = 1 := W.herm_hypA_hypB
  have ha₀0 : a₀ ≠ 0 := W.hypA_ne_zero
  have hb₀0 : b₀ ≠ 0 := by
    rintro h
    rw [h, herm_zero_right] at hab₀
    exact zero_ne_one hab₀
  have : Nontrivial P := by
    obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
    refine ⟨⟨((tv hσ.invol ha₀ hτ : G) : P), 1, fun h1 => ?_⟩⟩
    have hx := congrArg (· • pt b₀ hb₀0 hb₀) h1
    simp only [one_smul] at hx
    rw [hsmul, smul_pt, pt_eq_pt_iff] at hx
    obtain ⟨c, hc⟩ := hx
    rw [tv_smul, hab₀, mul_one] at hc
    have hc1 := congrArg (herm σ a₀) hc
    rw [herm_smul_right, herm_add_right, herm_smul_right, hab₀, ha₀, mul_zero, add_zero,
      mul_one] at hc1
    rw [hc1, one_smul, left_eq_add] at hc
    exact ha₀0 ((smul_eq_zero.mp hc).resolve_left hτ0)
  have hperfect : commutator P = ⊤ := by
    have : Group.IsPerfect G := isPerfect_SUid hσ hn h3
    have : Group.IsPerfect P :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
    exact Group.IsPerfect.commutator_eq_top
  let L₀ : X := pt a₀ ha₀0 ha₀
  let U : Subgroup P := ((QuotientGroup.mk' Z).comp (tvHom hσ.invol ha₀)).range
  have hU : ∀ c, ((QuotientGroup.mk' Z).comp (tvHom hσ.invol ha₀)) c =
      ((tvHom hσ.invol ha₀ c : G) : P) := fun _ => rfl
  have hUle : U ≤ MulAction.stabilizer P L₀ := by
    rintro _ ⟨c, rfl⟩
    rw [MulAction.mem_stabilizer_iff, hU, hsmul, smul_pt]
    refine pt_eq_pt_of_smul _ _ _ _ 1 ?_
    rw [tvHom_smul, ha₀, mul_zero, zero_smul, add_zero, one_smul]
  have hUnormal : (U.subgroupOf (MulAction.stabilizer P L₀)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUle]
    rintro _ p ⟨c, rfl⟩ hp
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
    rw [MulAction.mem_stabilizer_iff, hsmul, smul_pt, pt_eq_pt_iff] at hp
    obtain ⟨l, hl⟩ := hp
    have hc' : σ l * l * (c.toAdd : K) ∈ traceZero σ := by
      rw [mem_traceZero, map_mul, hσ.norm_fixed]
      have := (mem_traceZero σ).mp c.toAdd.2
      linear_combination σ l * l * this
    refine ⟨Multiplicative.ofAdd ⟨_, hc'⟩, ?_⟩
    rw [hU, hU, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply ext_smul
    intro v
    rw [conj_smul_of_tv g _ (tvHom_smul hσ.invol ha₀ c), tvHom_smul, ← hl, toAdd_ofAdd]
    simp only [herm_smul_left]
    rw [smul_smul]
    congr 2
    ring
  have hUsolv : Group.IsSolvable U := by
    apply Group.isSolvable_of_comm
    rintro ⟨_, ⟨c, rfl⟩⟩ ⟨_, ⟨d, rfl⟩⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, mul_comm]
  have hUgen : Subgroup.normalClosure (U : Set P) = ⊤ := by
    have hset : (U : Set P) =
        QuotientGroup.mk' Z '' Set.range (tvHom hσ.invol ha₀) := by
      rw [MonoidHom.coe_range, MonoidHom.coe_comp, Set.range_comp]
    have htop : Subgroup.normalClosure (Set.range (tvHom hσ.invol ha₀)) = (⊤ : Subgroup G) := by
      rw [eq_top_iff, ← T_eq_top hσ (by omega) h3, T, Subgroup.closure_le]
      rintro g ⟨a, c, ha, hc, hg⟩
      by_cases ha0 : a = 0
      · have : g = 1 := by
          apply ext_smul
          intro v
          rw [hg, ha0, herm_zero_left, mul_zero, zero_smul, add_zero, one_smul]
        rw [this]
        exact (Subgroup.normalClosure _).one_mem
      · obtain ⟨h, -, hh⟩ := exists_mem_T_smul_eq_of_iso hσ hn ha₀0 ha₀ ha0 ha
        have : g = h * tvHom hσ.invol ha₀ (Multiplicative.ofAdd ⟨c, hc⟩) * h⁻¹ := by
          apply ext_smul
          intro v
          rw [conj_smul_of_tv h _ (tvHom_smul hσ.invol ha₀ _), hh, hg, toAdd_ofAdd]
        rw [this]
        exact Subgroup.normalClosure_normal.conj_mem _
          (Subgroup.subset_normalClosure (Set.mem_range_self _)) h
    rw [hset, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective Z), htop,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)]
  exact CFSG.BenderSuzuki.External.huppert_II_6_12 hperfect L₀ U hUle hUnormal hUsolv hUgen

theorem isSimpleGroup_statedProj_statedSU (K : Type) [Field K] [Finite K] (p f : ℕ)
    [Fact p.Prime] (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ) (hn : 3 ≤ n)
    (hnq : (n, p ^ f) ≠ (3, 2)) : IsSimpleGroup (StatedProj (StatedSU n (p ^ f) K)) := by
  have := charP_of_card_sq (p := p) (f := f) hK
  rw [← SUid_eq_statedSU hK n]
  exact isSimpleGroup_statedProj_SUid (isUnitaryInvolution_unitaryInvolution hK) hn fun h3 =>
    exists_norm_ne_one hK fun hq => hnq (by rw [h3, hq])

theorem finite_statedProj_statedSU (n q : ℕ) (K : Type) [Field K] [Finite K] :
    Finite (StatedProj (StatedSU n q K)) :=
  inferInstance

theorem fam_unitary_projective_simple (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime]
    (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ) (hn : 3 ≤ n) (hnq : (n, p ^ f) ≠ (3, 2)) :
    Finite (StatedProj (StatedSU n (p ^ f) K)) ∧ Nontrivial (StatedProj (StatedSU n (p ^ f) K)) ∧
      IsSimpleGroup (StatedProj (StatedSU n (p ^ f) K)) := by
  have := isSimpleGroup_statedProj_statedSU K p f hK n hn hnq
  exact ⟨finite_statedProj_statedSU n (p ^ f) K, IsSimpleGroup.toNontrivial, this⟩

theorem fam_PSU_simplicity (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .PSU n p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨⟨hp, -, hn, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := isSimpleGroup_statedProj_statedSU K p f hK n hn hne
  have hG : IsSimpleGroup G := e.isSimpleGroup
  exact ⟨hG.toNontrivial, hG⟩

end CFSG.ClassicalGroups.Unitary
