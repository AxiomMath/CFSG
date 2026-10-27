module

public import CFSG.LieType.Multipliers.U62Data
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Multipliers.U62BridgeInputs
public import Certificates.Certificate10015
public meta import CFSG.LieType.Multipliers.U62Data
public meta import CFSG.Certificates.CosetTableCompactColumns
public meta import Certificates.Data.CFSGNative.F4.T46Simple
public import CFSG.Assembly.Subnormal
public import CFSG.Certificates.CosetTableShort
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Fischer.T46Simple
public meta import CFSG.Fischer.T46Simple
public meta import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public meta import CFSG.LieType.Multipliers.CoverWords
public meta import CFSG.Open.Defs

public section

namespace CFSG.LieType.Multipliers.U62

open CFSG.Fischer CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable
  CFSG.Fischer.Classification.Recognition CFSG.Sporadic.Fi22.Native

noncomputable def genP
    (i : Fin 5) : Equiv.Perm (Fin 693) := wordG t46G (genWord i)

noncomputable def genE
    (i : Fin 5) : T46 := ⟨genP i, t46_wordG_mem t46G_mem _⟩

theorem bridge_check : bridgeCheck = true :=
  Certificates.certificate10015.1

private theorem bridge_parts :
    (∀ r ∈ relWords, t46FixAll (wordT 693 t46Gen (expand r)) = true) ∧
      t46TblEq (wordT 693 t46Gen (expand xWord)) t46XT = true ∧
      t46TblEq (wordT 693 t46Gen (expand yWord)) t46YT = true ∧
      ∀ k : ℕ, k < 46 →
        t46FixAll (compT 693 (t46Gen ((k : ℤ) + 1)) (t46Gen ((k : ℤ) + 1))) = true := by
  have h := bridge_check
  unfold bridgeCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, fun k hk => (allIn_eq_true.1 h4) k (Nat.zero_le _) hk⟩

theorem t46G_mul_self
    (z : ℤ) : t46G z * t46G z = 1 := by
  by_cases hz : z.natAbs - 1 < 46
  · have hR := Rep.compT (rep_t46G z) (rep_t46G z)
    have he : t46Gen z = t46Gen ((((z.natAbs - 1 : ℕ)) : ℤ) + 1) := by
      unfold t46Gen
      congr 2
    rw [he] at hR
    exact t46_eq_one_of_fixAll hR (bridge_parts.2.2.2 (z.natAbs - 1) hz)
  · rw [t46G_eq_one (by omega), one_mul]

theorem t46G_inv
    (z : ℤ) : (t46G z)⁻¹ = t46G z :=
  inv_eq_of_mul_eq_one_left (t46G_mul_self z)

theorem wordG_inv
    (w : List ℤ) : (wordG t46G w)⁻¹ = wordG t46G w.reverse := by
  unfold wordG
  rw [List.prod_inv_reverse, List.map_map, List.map_reverse]
  simp only [Function.comp_def, t46G_inv]

theorem wordG_append
    (u v : List ℤ) : wordG t46G (u ++ v) = wordG t46G u * wordG t46G v := by
  simp [wordG]

theorem lift_genP
    (v : List (Fin 5 × Bool)) :
    FreeGroup.lift genP (FreeGroup.mk v) = wordG t46G (expand v) := by
  induction v with
  | nil => simp [expand, wordG]
  | cons l v ih =>
    have hexp : expand (l :: v) =
        (if l.2 then genWord l.1 else (genWord l.1).reverse) ++ expand v := by
      simp [expand, List.flatMap_cons]
    rw [hexp, wordG_append, ← ih, ← List.singleton_append, ← FreeGroup.mul_mk, map_mul]
    congr 1
    obtain ⟨i, _ | _⟩ := l
    · simp [genP, wordG_inv]
    · simp [genP]

theorem lift_genE_val
    (v : FreeGroup (Fin 5)) :
    ((FreeGroup.lift genE v : T46) : Equiv.Perm (Fin 693)) = FreeGroup.lift genP v := by
  have : T46.subtype.comp (FreeGroup.lift genE) = FreeGroup.lift genP :=
    FreeGroup.ext_hom _ _ fun i => by simp [genE]
  rw [← this]
  rfl

theorem lift_genE_eq_one
    {v : List (Fin 5 × Bool)} (hv : v ∈ relWords) :
    FreeGroup.lift genE (FreeGroup.mk v) = 1 := by
  apply Subtype.ext
  rw [lift_genE_val, lift_genP]
  exact t46_eq_one_of_fixAll (Rep.wordT (by norm_num) _ fun l _ => rep_t46G l)
    (bridge_parts.1 v hv)

theorem lift_genE_rels :
    ∀ r ∈ wordSet rels, FreeGroup.lift genE r = 1 := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
  exact lift_genE_eq_one (List.mem_append_left _ hv)

theorem lift_genE_comm
    (i : Fin 5) :
    FreeGroup.lift genE (FreeGroup.mk (commWords (coverPairs i))) = genE i := by
  have h := lift_genE_eq_one (v := commWords (coverPairs i) ++ [(i, false)])
    (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))
  rw [← FreeGroup.mul_mk, map_mul] at h
  simpa [mul_inv_eq_one] using h

private theorem lift_genP_eq_of_tblEq
    {v : List (Fin 5 × Bool)} {T : Table}
    {g : Equiv.Perm (Fin 693)} (hg : Rep 693 T g)
    (h : t46TblEq (wordT 693 t46Gen (expand v)) T = true) :
    FreeGroup.lift genP (FreeGroup.mk v) = g := by
  rw [lift_genP]
  exact t46_perm_eq_of_tblEq (Rep.wordT (by norm_num) _ fun l _ => rep_t46G l) hg h

private theorem lift_genE_mem_closure
    (v : FreeGroup (Fin 5)) :
    FreeGroup.lift genE v ∈ Subgroup.closure (Set.range genE) := by
  induction v using FreeGroup.induction_on with
  | one => simp
  | of i =>
    rw [FreeGroup.lift_apply_of]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  | inv_of i =>
    rw [map_inv, FreeGroup.lift_apply_of]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self i))
  | mul _ _ h₁ h₂ => rw [map_mul]; exact Subgroup.mul_mem _ h₁ h₂

theorem closure_genE :
    Subgroup.closure (Set.range genE) = ⊤ := by
  rw [eq_top_iff, ← closure_t46xE_t46yE, Subgroup.closure_le]
  have hx : t46xE = FreeGroup.lift genE (FreeGroup.mk xWord) := by
    apply Subtype.ext
    rw [lift_genE_val, lift_genP_eq_of_tblEq rep_t46x bridge_parts.2.1]
  have hy : t46yE = FreeGroup.lift genE (FreeGroup.mk yWord) := by
    apply Subtype.ext
    rw [lift_genE_val, lift_genP_eq_of_tblEq rep_t46y bridge_parts.2.2.1]
  rintro _ (rfl | rfl)
  · rw [hx]; exact lift_genE_mem_closure _
  · rw [hy]; exact lift_genE_mem_closure _

theorem card_le_of_subsetCheckShortCC_nil {m : ℕ} (ws : List (List (Fin m × Bool)))
    {k cap n : ℕ} (h : subsetCheckShortCC ws [] k cap n = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  have hS : subsetOf m [] = [] := by simp [subsetOf]
  have : Finite (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) := by
    rw [hS]; exact (inferInstance : Finite (PG 0 _))
  have hc : Nat.card (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) = 1 := by
    rw [hS]; exact card_PG_zero _
  have := card_le_of_subsetCheckShortCC ws [] h
  rwa [hc, mul_one] at this

theorem finite_card_le :
    Finite (PG 5 rels) ∧ Nat.card (PG 5 rels) ≤ 9196830720 :=
  Certificates.certificate10015.2

theorem isPresentation_T46 :
    IsPresentation genE (wordSet rels) := by
  obtain ⟨hfin, hle⟩ := finite_card_le
  have : Finite (PresentedGroup (wordSet rels)) := hfin
  exact IsPresentation.of_card_le lift_genE_rels closure_genE (by
    rw [card_T46]; exact hle)

theorem nonempty_mulEquiv_T46
    {X : Type} [Group X] (h : CFSG.Blueprint.LieModel X .PSU 6 2 1) :
    Nonempty (X ≃* T46) := by
  rcases h with ⟨-, -, F, _, _, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have := Fintype.ofFinite F
    have : Fintype CFSG.Blueprint.Fischer.K := Fintype.ofFinite _
    have hc : Fintype.card F = Fintype.card CFSG.Blueprint.Fischer.K := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, card_K]
    exact ⟨((e.trans (statedProjSUEquiv (FiniteField.ringEquivOfCardEq hc) 6 (2 ^ 1))).trans
      psuOneEquivStatedProj.symm).trans (psuEquiv.symm.trans suQuotEquiv)⟩
  all_goals exact absurd h0 (by norm_num)

end CFSG.LieType.Multipliers.U62
