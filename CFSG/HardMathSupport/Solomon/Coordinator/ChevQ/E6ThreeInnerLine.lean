module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2Defs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false

section Character

variable {K : Type} [Field K] {ω : Kˣ}

theorem e6LineChar_kacNode (ω : Kˣ) : e6LineChar ω e6KacNode = ω := rfl

theorem e6LineChar_of_ne (ω : Kˣ) {i : Fin Tag.E6.rank} (hi : i ≠ e6KacNode) :
    e6LineChar ω i = 1 := by
  obtain ⟨i, hi6⟩ := i
  have hi6' : i < 6 := hi6
  have hne : i ≠ 3 := fun h => hi (Fin.ext h)
  interval_cases i <;> first | exact absurd rfl hne | rfl

theorem rootChar_e6LineChar (ω : Kˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (e6LineChar ω) v = ω ^ v e6KacNode := by
  unfold rootChar
  rw [Finset.prod_eq_single e6KacNode]
  · rfl
  · intro i _ hi
    rw [e6LineChar_of_ne ω hi, one_zpow]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem e6Line_zpow_eq_one_iff_three_dvd (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (n : ℤ) :
    ω ^ n = 1 ↔ (3 : ℤ) ∣ n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ω = 3 := orderOf_eq_prime h3 h1
  rw [← orderOf_dvd_iff_zpow_eq_one, hord]
  norm_cast

theorem e6Line_kernel (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    rootCharKernel (e6LineChar ω) = ⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)) := by
  ext α
  simp only [rootCharKernel, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe,
    rootChar_e6LineChar, e6Line_zpow_eq_one_iff_three_dvd h3 h1]
  constructor
  · rintro ⟨hα, hd⟩
    exact (three_dvd_iff_mem_e6LineRoots hα).1 hd
  · rintro ⟨i, hi⟩
    have hα := isRoot_of_mem_e6LineRoots hi
    exact ⟨hα, (three_dvd_iff_mem_e6LineRoots hα).2 ⟨i, hi⟩⟩

theorem e6LineChar_pow_three (h3 : ω ^ 3 = 1) (i : Fin Tag.E6.rank) : e6LineChar ω i ^ 3 = 1 := by
  by_cases hi : i = e6KacNode
  · rw [hi, e6LineChar_kacNode]
    exact h3
  · rw [e6LineChar_of_ne ω hi, one_pow]

theorem e6Line_exists_cube_root_unit [Finite K] (h : 3 ∣ Nat.card K - 1) :
    ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 (hcard ▸ h)
  refine ⟨ω, by rw [← hω]; exact pow_orderOf_eq_one ω, fun h1 => ?_⟩
  rw [h1, orderOf_one] at hω
  omega

end Character

@[expose] def e6KacCoweight : Fin Tag.E6.rank → ℕ := ![2, 3, 4, 6, 4, 2]

theorem sum_e6KacCoweight_cartan (l : Fin Tag.E6.rank) :
    ∑ j, (e6KacCoweight j : ℤ) * Tag.E6.cartan j l = if l = e6KacNode then 1 else 0 := by
  revert l
  decide +kernel

theorem cartanChar_e6KacCoweight {K : Type} [Field K] (ω : Kˣ) :
    cartanChar (τ := .E6) (fun j => ω ^ e6KacCoweight j) = e6LineChar ω := by
  funext l
  have h1 : cartanChar (τ := .E6) (fun j => ω ^ e6KacCoweight j) l =
      ω ^ ∑ j, (e6KacCoweight j : ℤ) * Tag.E6.cartan j l := by
    rw [← prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    show (ω ^ e6KacCoweight j) ^ Tag.E6.cartan j l = _
    rw [← zpow_natCast, ← zpow_mul]
  rw [h1, sum_e6KacCoweight_cartan]
  by_cases hl : l = e6KacNode
  · rw [if_pos hl, hl, zpow_one]
    rfl
  · rw [if_neg hl, zpow_zero, e6LineChar_of_ne ω hl]

section Torus

variable {K : Type} [Field K]

theorem e6Line_diag_mem_torusGroup (ω : Kˣ) :
    rootDiagUnit .E6 (e6LineChar ω) ∈ torusGroup .E6 K := by
  rw [← cartanChar_e6KacCoweight ω, ← list_prod_torusElt_eq_rootDiagUnit]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact torusElt_mem_torusGroup j _

end Torus

section Weyl

variable {K : Type} [Field K] {ω : Kˣ}

theorem e6LineWeyl_mem_stabilizer (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    e6LineWeyl ∈ rootCharStabilizerSubgroup (e6LineChar ω) := by
  have key : ∀ α ∈ rootFinset .E6,
      (3 : ℤ) ∣ e6WordAct e6LineWord α e6KacNode - α e6KacNode := by decide +kernel
  intro v
  refine rootChar_smul_eq_of_forall_isRoot (fun α hα => ?_) v
  have hd := (e6Line_zpow_eq_one_iff_three_dvd h3 h1 _).2 (key α (mem_rootFinset.2 hα))
  rw [zpow_sub] at hd
  rw [e6LineWeyl_smul, rootChar_e6LineChar, rootChar_e6LineChar]
  exact mul_inv_eq_one.1 hd

@[expose] def e6ShiftChar (a : Fin Tag.E6.rank → Kˣ) : rootCharStabilizerSubgroup a →* Kˣ where
  toFun w := rootChar a (e6Shift (w : WeylGroup .E6))
  map_one' := by
    change rootChar a (e6Shift 1) = 1
    rw [e6Shift_one, rootChar_zero]
  map_mul' w₁ w₂ := by
    change rootChar a (e6Shift ((w₁ : WeylGroup .E6) * w₂)) =
      rootChar a (e6Shift (w₁ : WeylGroup .E6)) * rootChar a (e6Shift (w₂ : WeylGroup .E6))
    rw [e6Shift_mul, rootChar_add, w₁.2 (e6Shift (w₂ : WeylGroup .E6)), mul_comm]

theorem e6ShiftChar_pow_three (a : Fin Tag.E6.rank → Kˣ) (w : rootCharStabilizerSubgroup a) :
    e6ShiftChar a w ^ 3 = 1 := by
  have h := rootChar_zsmul a 3 (e6Shift (w : WeylGroup .E6))
  rw [three_smul_e6Shift (w : WeylGroup .E6), rootChar_sub, w.2 e6Omega3, mul_inv_cancel] at h
  change rootChar a (e6Shift (w : WeylGroup .E6)) ^ 3 = 1
  exact_mod_cast h.symm

theorem e6Shift_e6LineWeyl : e6Shift e6LineWeyl = ![-1, -1, -1, -2, -1, 0] := by
  refine e6Shift_eq_of_three_smul ?_
  rw [e6LineWeyl_smul]
  decide +kernel

theorem rootChar_e6Shift_e6LineWeyl (h3 : ω ^ 3 = 1) :
    rootChar (e6LineChar ω) (e6Shift e6LineWeyl) = ω := by
  rw [rootChar_e6LineChar, e6Shift_e6LineWeyl]
  have h : (![-1, -1, -1, -2, -1, 0] : Fin Tag.E6.rank → ℤ) e6KacNode = -2 := rfl
  rw [h, zpow_neg, zpow_two]
  refine inv_eq_of_mul_eq_one_right ?_
  simpa only [pow_succ, pow_zero, one_mul] using h3

theorem e6Line_exists_pow_eq_of_pow_three_eq_one (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {x : Kˣ}
    (hx : x ^ 3 = 1) : ∃ j < 3, x = ω ^ j := by
  have hω : (ω : K) ^ 3 = 1 := by
    have := congrArg Units.val h3
    simpa using this
  have hs : (ω : K) ^ 2 + ω + 1 = 0 := by
    have h : ((ω : K) - 1) * ((ω : K) ^ 2 + ω + 1) = 0 := by linear_combination hω
    have hne : (ω : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => h1 (Units.ext h)
    exact (mul_eq_zero.1 h).resolve_left hne
  have hx' : (x : K) ^ 3 = 1 := by
    have := congrArg Units.val hx
    simpa using this
  have h : ((x : K) - 1) * ((x : K) - ω) * ((x : K) - ω ^ 2) = 0 := by
    linear_combination hx' + (-(x : K) ^ 2 + x) * hs + ((x : K) - 1) * hω
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact ⟨0, by norm_num, Units.ext (by simpa [sub_eq_zero] using h)⟩
    · exact ⟨1, by norm_num, Units.ext (by simpa [sub_eq_zero] using h)⟩
  · exact ⟨2, by norm_num, Units.ext (by simpa [sub_eq_zero] using h)⟩

theorem exists_mul_pow_of_mem_stabilizer (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {w : WeylGroup .E6}
    (hw : w ∈ rootCharStabilizerSubgroup (e6LineChar ω)) :
    ∃ j < 3, ∃ u ∈ kernelReflectionGroup (e6LineChar ω), w = u * e6LineWeyl ^ j := by
  set a : Fin Tag.E6.rank → Kˣ := e6LineChar ω with ha
  have hc := e6LineWeyl_mem_stabilizer h3 h1
  obtain ⟨j, hj, hjs⟩ := e6Line_exists_pow_eq_of_pow_three_eq_one h3 h1
    (e6ShiftChar_pow_three a ⟨w, hw⟩)
  have hcs : e6ShiftChar a ⟨e6LineWeyl, hc⟩ = ω := rootChar_e6Shift_e6LineWeyl h3
  have hcj : e6LineWeyl ^ j ∈ rootCharStabilizerSubgroup a := pow_mem hc j
  have hu : w * (e6LineWeyl ^ j)⁻¹ ∈ rootCharStabilizerSubgroup a :=
    mul_mem hw (inv_mem hcj)
  refine ⟨j, hj, w * (e6LineWeyl ^ j)⁻¹, ?_, by group⟩
  refine mem_kernelReflectionGroup_of_e6Shift a (e6LineChar_pow_three h3) hu ?_
  have h2 : e6ShiftChar a ⟨w * (e6LineWeyl ^ j)⁻¹, hu⟩ = 1 := by
    have e : (⟨w * (e6LineWeyl ^ j)⁻¹, hu⟩ : rootCharStabilizerSubgroup a) =
        ⟨w, hw⟩ * (⟨e6LineWeyl, hc⟩ ^ j)⁻¹ := rfl
    rw [e, map_mul, map_inv, map_pow, hjs, hcs, mul_inv_cancel]
  exact h2

end Weyl

section Centralizer

variable
    {K : Type} [Field K] {ω : Kˣ}

theorem e6Line_centralizer_mul (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {g : ModGL .E6 K}
    (hg : g ∈ toralCentralizer .E6 K (e6LineChar ω)) :
    ∃ m ∈ toralRootGroup .E6 K (e6LineChar ω), ∃ j < 3,
      g = m * canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j := by
  set a : Fin Tag.E6.rank → Kˣ := e6LineChar ω with ha
  set n : ModGL .E6 K := canonicalRep (coxeterSystem .E6) K e6LineWeyl with hn
  obtain ⟨-, -, -, -, φ, hφ, hφw⟩ := Chevalley_toral_centralizer_root_generated_quotient .E6 K a
  have hc := e6LineWeyl_mem_stabilizer h3 h1
  have hnX : n ∈ toralCentralizer .E6 K a := canonicalRep_mem_toralCentralizer hc
  have hnN : n ∈ Subgroup.normalizer (toralRootGroup .E6 K a : Set (ModGL .E6 K)) :=
    canonicalRep_mem_normalizer_toralRootGroup hc
  obtain ⟨q, hq⟩ := hφ (QuotientGroup.mk ⟨g, hg⟩)
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨j, hj, u, hu, rfl⟩ := exists_mul_pow_of_mem_stabilizer h3 h1 hw
  have huW : u ∈ rootCharStabilizerSubgroup a := kernelReflectionGroup_le a hu
  have hmk : (QuotientGroup.mk ⟨u * e6LineWeyl ^ j, hw⟩ : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) =
        (QuotientGroup.mk ⟨e6LineWeyl, hc⟩) ^ j := by
    have e : (⟨u * e6LineWeyl ^ j, hw⟩ : rootCharStabilizerSubgroup a) =
        ⟨u, huW⟩ * ⟨e6LineWeyl, hc⟩ ^ j := rfl
    rw [e, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hu),
      one_mul, QuotientGroup.mk_pow]
  have hφc : φ (QuotientGroup.mk ⟨e6LineWeyl, hc⟩) = QuotientGroup.mk ⟨n, hnX⟩ :=
    hφw ⟨e6LineWeyl, hc⟩
  rw [hmk, map_pow, hφc, ← QuotientGroup.mk_pow] at hq
  have h2 : (n ^ j)⁻¹ * g ∈ toralRootGroup .E6 K a :=
    Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hq)
  refine ⟨g * (n ^ j)⁻¹, ?_, j, hj, by group⟩
  have e : g * (n ^ j)⁻¹ = n ^ j * ((n ^ j)⁻¹ * g) * (n ^ j)⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hnN j) _).1 h2

theorem e6Line_centralizer (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    toralCentralizer .E6 K (e6LineChar ω) =
      toralRootGroup .E6 K (e6LineChar ω) ⊔
        Subgroup.zpowers (canonicalRep (coxeterSystem .E6) K e6LineWeyl) := by
  refine le_antisymm (fun g hg => ?_) (sup_le (toralRootGroup_le _)
    ((Subgroup.zpowers_le).2 (canonicalRep_mem_toralCentralizer (e6LineWeyl_mem_stabilizer h3 h1))))
  obtain ⟨m, hm, j, -, rfl⟩ := e6Line_centralizer_mul h3 h1 hg
  exact Subgroup.mul_mem_sup hm (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j)

end Centralizer

theorem mem_normalizer_of_map_conj_eq_aux {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h' := congrArg SetLike.coe h
  rw [Subgroup.coe_map] at h'
  exact h'

theorem map_conj_eq_of_mem_normalizer_aux {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.1 hg y).1 hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) x).1 hx
    simpa using this

theorem map_conj_mul_aux {G : Type*} [Group G] (H : Subgroup G) (g h : G) :
    H.map (MulAut.conj (g * h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

section Span

variable {K : Type} [Field K]

theorem torusGroup_le_normalizer_rootSpan_e6 {S : Set (Fin Tag.E6.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot .E6 α) :
    torusGroup .E6 K ≤ Subgroup.normalizer (rootSpan .E6 K S : Set (ModGL .E6 K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact mem_normalizer_of_map_conj_eq_aux (map_rootSpan_of_forall fun α hα =>
    map_conj_torusElt_rootSubgroup i t (hS α hα))

theorem rootSpan_eq_iSup_e6LineFactor :
    rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) =
      ⨆ i : Fin 3, e6LineFactor K i := by
  simp only [e6LineFactor, rootSpan, iSup_iUnion]

end Span

section Orthogonal

theorem iform_eq_zero_of_e6LineRoots :
    ∀ i j : Fin 3, i ≠ j → ∀ α ∈ e6LineRoots i, ∀ β ∈ e6LineRoots j, iform α β = 0 := by
  decide +kernel

theorem ne_and_ne_neg_of_e6LineRoots :
    ∀ i j : Fin 3, i ≠ j → ∀ α ∈ e6LineRoots i, ∀ β ∈ e6LineRoots j, α ≠ β ∧ α ≠ -β := by
  decide +kernel

theorem e6_iform_self_of_isRoot {σ : Fin Tag.E6.rank → ℤ}
    (hσ : IsRoot .E6 σ) : iform σ σ = 2 := by
  have h : ∀ σ ∈ rootFinset .E6, iform σ σ = 2 := by decide +kernel
  exact h σ (mem_rootFinset.2 hσ)

theorem not_isRoot_nsmul_add_of_e6LineRoots
    {i j : Fin 3} (hij : i ≠ j) {α β : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ e6LineRoots i) (hβ : β ∈ e6LineRoots j) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ¬IsRoot .E6 (a • α + b • β) := by
  intro hγ
  have h2 := e6_iform_self_of_isRoot hγ
  rw [iform_nsmul_add_nsmul, e6_iform_self_of_isRoot (isRoot_of_mem_e6LineRoots hα),
    e6_iform_self_of_isRoot (isRoot_of_mem_e6LineRoots hβ),
    iform_eq_zero_of_e6LineRoots i j hij α hα β hβ] at h2
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

end Orthogonal

theorem image_smul_e6LineRoots (i : Fin 3) :
    (fun α => e6LineWeyl • α) '' (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)) =
      (e6LineRoots (i + 1) : Set (Fin Tag.E6.rank → ℤ)) := by
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact smul_mem_e6LineRoots hα
  · intro hβ
    have e : ∀ i : Fin 3, i + 1 + 1 + 1 = i := by decide
    have hc : e6LineWeyl * e6LineWeyl ^ 2 = 1 := by
      rw [← pow_succ']
      exact e6LineWeyl_pow_three
    refine ⟨e6LineWeyl ^ 2 • β, ?_, ?_⟩
    · have h2 := smul_mem_e6LineRoots (smul_mem_e6LineRoots hβ)
      rw [e i] at h2
      rw [pow_two, mul_smul]
      exact h2
    · show e6LineWeyl • e6LineWeyl ^ 2 • β = β
      rw [← mul_smul, hc, one_smul]

section Transport

variable
    {K : Type} [Field K]

theorem e6LineFactor_conj (i : Fin 3) :
    (e6LineFactor K i).map
        (MulAut.conj (canonicalRep (coxeterSystem .E6) K e6LineWeyl)).toMonoidHom =
      e6LineFactor K (i + 1) := by
  rw [e6LineFactor, (canonical_weyl_root_transport .E6 K).1 e6LineWeyl _
    (fun α hα => isRoot_of_mem_e6LineRoots (Finset.mem_coe.1 hα)), image_smul_e6LineRoots]
  rfl

theorem exists_e6LineFactor_conj_pow (j : ℕ) :
    ∃ k : Fin 3, ∀ i : Fin 3,
      (e6LineFactor K i).map
          (MulAut.conj (canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j)).toMonoidHom =
        e6LineFactor K (i + k) := by
  induction j with
  | zero =>
    refine ⟨0, fun i => ?_⟩
    rw [pow_zero, add_zero]
    ext x
    simp [Subgroup.mem_map, MulAut.conj_apply]
  | succ j ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨1 + k, fun i => ?_⟩
    rw [pow_succ, map_conj_mul_aux, e6LineFactor_conj, hk, add_assoc]

theorem canonicalRep_e6LineWeyl_mem_normalizer :
    canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      Subgroup.normalizer (rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) :
        Set (ModGL .E6 K)) := by
  refine mem_normalizer_of_map_conj_eq_aux ?_
  rw [rootSpan_eq_iSup_e6LineFactor, Subgroup.map_iSup]
  simp only [e6LineFactor_conj]
  exact (Equiv.addRight (1 : Fin 3)).iSup_comp (g := fun i => e6LineFactor K i)

end Transport

section Factors

variable
    {K : Type} [Field K] {ω : Kˣ}

theorem commute_of_e6LineRoots {i j : Fin 3} (hij : i ≠ j) {α β : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ e6LineRoots i) (hβ : β ∈ e6LineRoots j) :
    ∀ x ∈ rootSubgroup .E6 K α, ∀ y ∈ rootSubgroup .E6 K β, Commute x y := by
  obtain ⟨hne, hne'⟩ := ne_and_ne_neg_of_e6LineRoots i j hij α hα β hβ
  exact commute_of_forall_not_isRoot (isRoot_of_mem_e6LineRoots hα)
    (isRoot_of_mem_e6LineRoots hβ) hne hne'
    (fun a b ha hb => not_isRoot_nsmul_add_of_e6LineRoots hij hα hβ ha hb) K

theorem e6LineFactor_commute {i j : Fin 3} (hij : i ≠ j) {x y : ModGL .E6 K}
    (hx : x ∈ e6LineFactor K i) (hy : y ∈ e6LineFactor K j) : x * y = y * x := by
  have h1 : ∀ α ∈ e6LineRoots i, ∀ x ∈ rootSubgroup .E6 K α,
      e6LineFactor K j ≤ Subgroup.centralizer ({x} : Set (ModGL .E6 K)) := by
    intro α hα x hx
    refine iSup₂_le fun β hβ => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_e6LineRoots hij hα (Finset.mem_coe.1 hβ) x hx y hy).eq.symm
  have h2 : e6LineFactor K i ≤ Subgroup.centralizer (e6LineFactor K j : Set (ModGL .E6 K)) := by
    refine iSup₂_le fun α hα => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (h1 α (Finset.mem_coe.1 hα) x hx hb)
  exact (Subgroup.mem_centralizer_iff.1 (h2 hx) y hy).symm

theorem e6LineFactor_le_normalizer (i j : Fin 3) :
    e6LineFactor K j ≤ Subgroup.normalizer (e6LineFactor K i : Set (ModGL .E6 K)) := by
  by_cases hij : j = i
  · subst hij
    exact Subgroup.le_normalizer
  · have hc : e6LineFactor K j ≤ Subgroup.centralizer (e6LineFactor K i : Set (ModGL .E6 K)) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact e6LineFactor_commute (Ne.symm hij) hx hy
    exact hc.trans (Subgroup.centralizer_le_normalizer _)

theorem e6LineFactor_normalizer (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (i : Fin 3) :
    toralRootGroup .E6 K (e6LineChar ω) ≤
      Subgroup.normalizer (e6LineFactor K i : Set (ModGL .E6 K)) := by
  refine sup_le (torusGroup_le_normalizer_rootSpan_e6 fun α hα =>
    isRoot_of_mem_e6LineRoots (Finset.mem_coe.1 hα)) ?_
  rw [e6Line_kernel h3 h1, rootSpan_eq_iSup_e6LineFactor]
  exact iSup_le (e6LineFactor_le_normalizer i)

end Factors

section CentralizerFactors

variable
    {K : Type} [Field K] {ω : Kˣ}

theorem e6LineFactor_conj_centralizer (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {g : ModGL .E6 K}
    (hg : g ∈ toralCentralizer .E6 K (e6LineChar ω)) :
    ∃ k : Fin 3, ∀ i : Fin 3,
      (e6LineFactor K i).map (MulAut.conj g).toMonoidHom = e6LineFactor K (i + k) := by
  obtain ⟨m, hm, j, -, rfl⟩ := e6Line_centralizer_mul h3 h1 hg
  obtain ⟨k, hk⟩ := exists_e6LineFactor_conj_pow (K := K) j
  refine ⟨k, fun i => ?_⟩
  rw [map_conj_mul_aux, hk]
  exact map_conj_eq_of_mem_normalizer_aux (e6LineFactor_normalizer h3 h1 _ hm)

end CentralizerFactors

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
