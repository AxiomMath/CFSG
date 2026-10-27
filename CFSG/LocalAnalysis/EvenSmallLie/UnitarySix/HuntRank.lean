module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntRankCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntRankModel

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open CFSG.ComponentClassification.WittDesign CFSG.EvenSmallLie.UnitarySix.MathieuExt
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Mathieu

theorem sqB_iff {g : Equiv.Perm (Fin 22)} : sqB ⇑g = true ↔ g * g = 1 := by
  rw [sqB, List.all_eq_true]
  constructor
  · intro h
    exact Equiv.ext fun i => by simpa using h i (List.mem_finRange i)
  · intro h i _
    rw [beq_iff_eq, ← Equiv.Perm.mul_apply, h, Equiv.Perm.one_apply]

theorem commB_iff {r g : Equiv.Perm (Fin 22)} : commB ⇑r ⇑g = true ↔ g * r = r * g := by
  rw [commB, List.all_eq_true]
  constructor
  · intro h
    exact Equiv.ext fun i => by simpa using h i (List.mem_finRange i)
  · intro h i _
    rw [beq_iff_eq, ← Equiv.Perm.mul_apply, h, Equiv.Perm.mul_apply]

theorem eqB_iff {r g : Equiv.Perm (Fin 22)} : eqB ⇑r ⇑g = true ↔ g = r := by
  rw [eqB, List.all_eq_true]
  constructor
  · intro h
    exact Equiv.ext fun i => by simpa using h i (List.mem_finRange i)
  · intro h i _
    rw [beq_iff_eq, h]

theorem eqB_id_iff {g : Equiv.Perm (Fin 22)} : eqB id ⇑g = true ↔ g = 1 :=
  eqB_iff (r := 1)

theorem sqMulB_iff {s g : Equiv.Perm (Fin 22)} : sqMulB ⇑s ⇑g = true ↔ g * s * (g * s) = 1 := by
  rw [sqMulB, List.all_eq_true]
  constructor
  · intro h
    exact Equiv.ext fun i => by simpa using h i (List.mem_finRange i)
  · intro h i _
    have := congrArg (fun p : Equiv.Perm (Fin 22) => p i) h
    simpa using this

theorem forall_not_of_count
    {Q : (Fin 22 → Fin 22) → Prop} [DecidablePred Q]
    (h : m22Count Q = 0) (x : M22) : ¬ Q ⇑(x : Equiv.Perm (Fin 22)) := fun hx => by
  have h0 := card_m22_subtype Q
  rw [h] at h0
  exact absurd h0 (Nat.card_pos_iff.2 ⟨⟨⟨x, hx⟩⟩, inferInstance⟩).ne'

@[expose] def tau0 : Equiv.Perm (Fin 22) := m22gB * m22gB * sigmaPerm

theorem rep_tab8 : Rep 22 tab8 sigmaPerm := by
  have h : ∀ i : Fin 22, ap tab8 i = (sigmaPerm i : ℕ) := by
    have hs : ∀ x : Fin 22, sigmaPerm x = sigmaFun x := fun _ => rfl
    have h' : ∀ i : Fin 22, ap tab8 i = (sigmaFun i : ℕ) := by decide +kernel
    intro i
    rw [hs]
    exact h' i
  intro i hi
  rw [idx_of_lt _ hi]
  exact h ⟨i, hi⟩

theorem rep_tab0 : Rep 22 tab0 tau0 := by
  have h : ∀ i : Fin 22, ap tab0 i = (tau0 i : ℕ) := by
    have hs : ∀ x : Fin 22, sigmaPerm x = sigmaFun x := fun _ => rfl
    have h' : ∀ i : Fin 22, ap tab0 i = (m22gB (m22gB (sigmaFun i)) : ℕ) := by decide +kernel
    intro i
    have e : tau0 i = m22gB (m22gB (sigmaFun i)) :=
      (Equiv.Perm.mul_apply (m22gB * m22gB) sigmaPerm i).trans
        ((Equiv.Perm.mul_apply m22gB m22gB (sigmaPerm i)).trans
          (congrArg (fun x => m22gB (m22gB x)) (hs i)))
    rw [e]
    exact h' i
  intro i hi
  rw [idx_of_lt _ hi]
  exact h ⟨i, hi⟩

theorem rep_tabY : Rep 22 tabY m22gA := by
  have h : ∀ i : Fin 22, ap tabY i = (m22gA i : ℕ) := by decide +kernel
  intro i hi
  rw [idx_of_lt _ hi]
  exact h ⟨i, hi⟩

theorem sigmaPerm_sq : sigmaPerm * sigmaPerm = 1 :=
  Equiv.ext fun i => phi_facts.2.2.1 i

theorem tau0_sq : tau0 * tau0 = 1 := by
  have hs : ∀ x : Fin 22, sigmaPerm x = sigmaFun x := fun _ => rfl
  have h' : ∀ i : Fin 22, m22gB (m22gB (sigmaFun (m22gB (m22gB (sigmaFun i))))) = i := by
    decide +kernel
  have e : ∀ x : Fin 22, tau0 x = m22gB (m22gB (sigmaFun x)) := fun x =>
    (Equiv.Perm.mul_apply (m22gB * m22gB) sigmaPerm x).trans
      ((Equiv.Perm.mul_apply m22gB m22gB (sigmaPerm x)).trans
        (congrArg (fun y => m22gB (m22gB y)) (hs x)))
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.mul_apply tau0 tau0 i, Equiv.Perm.one_apply, e, e]
  exact h' i

theorem tau0_ne (i : Fin 22) : tau0 i ≠ i := by
  have hs : ∀ x : Fin 22, sigmaPerm x = sigmaFun x := fun _ => rfl
  have h' : ∀ i : Fin 22, m22gB (m22gB (sigmaFun i)) ≠ i := by decide +kernel
  have e : tau0 i = m22gB (m22gB (sigmaFun i)) :=
    (Equiv.Perm.mul_apply (m22gB * m22gB) sigmaPerm i).trans
      ((Equiv.Perm.mul_apply m22gB m22gB (sigmaPerm i)).trans
        (congrArg (fun x => m22gB (m22gB x)) (hs i)))
  rw [e]
  exact h' i

theorem sigmaPerm_zero : sigmaPerm 0 = 0 := by
  have h' : sigmaFun 0 = 0 := by decide +kernel
  exact h'

theorem tau0_mem :
    tau0 ∈ hexadAut :=
  mul_mem (mul_mem (M22_le_hexadAut m22b.2) (M22_le_hexadAut m22b.2)) sigmaPerm_mem

theorem tau0_not_mem
    : tau0 ∉ M22 := fun h => sigmaPerm_not_mem (by
  have := mul_mem (inv_mem (mul_mem m22b.2 m22b.2)) h
  rwa [tau0, ← mul_assoc, inv_mul_cancel, one_mul] at this)

theorem m22gA_sq : m22gA * m22gA = 1 := by decide +kernel

theorem mul_mem_M22_of_not_mem
    {g h : Equiv.Perm (Fin 22)} (hg : g ∈ hexadAut)
    (hh : h ∈ hexadAut) (hg' : g ∉ M22) (hh' : h ∉ M22) : g * h ∈ M22 := by
  have hidx : (M22.subgroupOf hexadAut).index = 2 := card_hexadAut.2
  have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨g, hg⟩) (b := ⟨h, hh⟩)).2
    (by simp only [Subgroup.mem_subgroupOf]; exact iff_of_false hg' hh')
  rwa [Subgroup.mem_subgroupOf] at this

theorem conj_mem_M22'
    {g m : Equiv.Perm (Fin 22)} (hg : g ∈ hexadAut) (hm : m ∈ M22) :
    g * m * g⁻¹ ∈ M22 := by
  by_cases hgM : g ∈ M22
  · exact mul_mem (mul_mem hgM hm) (inv_mem hgM)
  · have hgm : g * m ∉ M22 := fun h => hgM (by simpa using mul_mem h (inv_mem hm))
    exact mul_mem_M22_of_not_mem (mul_mem hg (M22_le_hexadAut hm)) (inv_mem hg) hgm
      (fun h => hgM (by simpa using inv_mem h))

theorem conj_not_mem_M22
    {g x : Equiv.Perm (Fin 22)} (hg : g ∈ hexadAut) (hx : x ∉ M22) :
    g * x * g⁻¹ ∉ M22 := fun h => hx (by
  have := conj_mem_M22' (inv_mem hg) h
  simpa [mul_assoc] using this)

theorem toddAct_mk
    {g : Equiv.Perm (Fin 22)} (hg : g ∈ hexadAut) (w : W22) :
    toddAct hg (Submodule.Quotient.mk w) = Submodule.Quotient.mk (permW g w) := by
  rw [toddAct, Submodule.mapQ_apply]

theorem toddAct_mul
    {g h : Equiv.Perm (Fin 22)} (hg : g ∈ hexadAut) (hh : h ∈ hexadAut)
    (hgh : g * h ∈ hexadAut) (v : toddModule) :
    toddAct hgh v = toddAct hg (toddAct hh v) := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [toddAct_mk, toddAct_mk, toddAct_mk, permW_mul]

theorem toddAct_one
    (h1 : (1 : Equiv.Perm (Fin 22)) ∈ hexadAut) (v : toddModule) :
    toddAct h1 v = v := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [toddAct_mk]
  rfl

theorem toddAct_congr
    {g g' : Equiv.Perm (Fin 22)} (hg : g ∈ hexadAut) (hg' : g' ∈ hexadAut)
    (h : g = g') (v : toddModule) : toddAct hg v = toddAct hg' v := by
  subst h
  rfl

theorem card_conj
    {X : Subgroup (Equiv.Perm (Fin 22))} (hX : X ≤ hexadAut)
    {g : Equiv.Perm (Fin 22)} (hg : g ∈ hexadAut)
    (hX' : X.map (MulAut.conj g).toMonoidHom ≤ hexadAut) :
    Nat.card (X.map (MulAut.conj g).toMonoidHom) *
        Nat.card (fixV (X.map (MulAut.conj g).toMonoidHom) hX') =
      Nat.card X * Nat.card (fixV X hX) := by
  have hcX : Nat.card (X.map (MulAut.conj g).toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hgi : g⁻¹ ∈ hexadAut := inv_mem hg
  have hmem : ∀ x ∈ X, g * x * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := fun x hx =>
    Subgroup.mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hinv : ∀ v, toddAct hg (toddAct hgi v) = v := fun v => by
    rw [← toddAct_mul hg hgi (mul_mem hg hgi), toddAct_congr _ (one_mem _) (mul_inv_cancel g),
      toddAct_one]
  have hinv' : ∀ v, toddAct hgi (toddAct hg v) = v := fun v => by
    rw [← toddAct_mul hgi hg (mul_mem hgi hg), toddAct_congr _ (one_mem _) (inv_mul_cancel g),
      toddAct_one]
  have hcV : Nat.card (fixV (X.map (MulAut.conj g).toMonoidHom) hX') = Nat.card (fixV X hX) := by
    refine Nat.card_congr
      { toFun := fun v => ⟨toddAct hgi v.1, fun x hx => ?_⟩
        invFun := fun v => ⟨toddAct hg v.1, fun y hy => ?_⟩
        left_inv := fun v => Subtype.ext (hinv v.1)
        right_inv := fun v => Subtype.ext (hinv' v.1) }
    · have hc := v.2 _ (hmem x hx)
      rw [← toddAct_mul (hX hx) hgi (mul_mem (hX hx) hgi),
        toddAct_congr _ (mul_mem hgi (hX' (hmem x hx))) (by group),
        toddAct_mul hgi (hX' (hmem x hx)), hc]
    · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      have hc := v.2 x hx
      rw [← toddAct_mul (hX' hy) hg (mul_mem (hX' hy) hg),
        toddAct_congr _ (mul_mem hg (hX hx)) (by simp [MulAut.conj_apply]),
        toddAct_mul hg (hX hx), hc]
  rw [hcX, hcV]

theorem card_le_ncard_orbit_mul {G : Type*} [Group G] [Finite G] (x : G) {c : ℕ}
    (hc : Nat.card (Subgroup.centralizer {x}) ≤ c) :
    Nat.card G ≤ (MulAction.orbit (ConjAct G) x).ncard * c := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct G) x)
  rw [MulAction.index_stabilizer, ← Subgroup.nat_card_centralizer_nat_card_stabilizer] at h1
  have h2 : Nat.card (ConjAct G) = Nat.card G := Nat.card_congr ConjAct.ofConjAct.toEquiv
  rw [← h2, ← h1, mul_comm]
  exact Nat.mul_le_mul_left _ hc

theorem card_centralizer_le
    {τ : Equiv.Perm (Fin 22)} {T : Table} (hT : Rep 22 T τ)
    (hτ : τ ∈ hexadAut) (hτM : τ ∉ M22) (hττ : τ * τ = 1) :
    Nat.card (Subgroup.centralizer {(⟨τ, hτ⟩ : hexadAut)}) ≤
      m22Count (fun f => commB (tf T) f = true) * 2 := by
  classical
  have htf : tf T = ⇑τ := tf_eq hT
  have hc : ∀ c : Subgroup.centralizer {(⟨τ, hτ⟩ : hexadAut)},
      ((c : hexadAut) : Equiv.Perm (Fin 22)) * τ = τ * (c : hexadAut) := fun c =>
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 c.2)
  let f : Subgroup.centralizer {(⟨τ, hτ⟩ : hexadAut)} →
      {x : M22 // commB (tf T) ⇑(x : Equiv.Perm (Fin 22)) = true} × Bool := fun c =>
    if h : ((c : hexadAut) : Equiv.Perm (Fin 22)) ∈ M22 then
      (⟨⟨_, h⟩, by rw [htf]; exact commB_iff.2 (hc c)⟩, false)
    else
      (⟨⟨_ * τ, mul_mem_M22_of_not_mem (c : hexadAut).2 hτ h hτM⟩, by
        rw [htf]
        exact commB_iff.2 (by
          rw [mul_assoc, hττ, mul_one, ← mul_assoc, ← hc c, mul_assoc, hττ, mul_one])⟩, true)
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    split_ifs at hab with ha hb hb
    · simp only [Prod.mk.injEq, Subtype.mk.injEq, and_true] at hab
      exact Subtype.ext (Subtype.ext hab)
    · simp at hab
    · simp at hab
    · simp only [Prod.mk.injEq, Subtype.mk.injEq, and_true] at hab
      exact Subtype.ext (Subtype.ext (mul_right_cancel hab))
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  rw [← card_m22_subtype]
  exact this

theorem orbit_subset
    {t : hexadAut} (htM : (t : Equiv.Perm (Fin 22)) ∉ M22) (htt : t * t = 1) :
    MulAction.orbit (ConjAct hexadAut) t ⊆ {y | (y : Equiv.Perm (Fin 22)) ∉ M22 ∧ y * y = 1} := by
  intro y hy
  obtain ⟨c, rfl⟩ := isConj_iff.1 (isConj_comm.1 (ConjAct.mem_orbit_conjAct.1 hy))
  refine ⟨conj_not_mem_M22 c.2 htM, ?_⟩
  rw [show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, htt, mul_one,
    mul_inv_cancel]

theorem outer_conj
    {x : Equiv.Perm (Fin 22)} (hx : x ∈ hexadAut) (hxM : x ∉ M22)
    (hxx : x * x = 1) : ∃ g ∈ hexadAut, g * x * g⁻¹ = sigmaPerm ∨ g * x * g⁻¹ = tau0 := by
  set t8 : hexadAut := ⟨sigmaPerm, sigmaPerm_mem⟩
  set t0 : hexadAut := ⟨tau0, tau0_mem⟩
  set S : Set hexadAut := {y | (y : Equiv.Perm (Fin 22)) ∉ M22 ∧ y * y = 1}
  have h8S := orbit_subset (t := t8) sigmaPerm_not_mem (Subtype.ext sigmaPerm_sq)
  have h0S := orbit_subset (t := t0) tau0_not_mem (Subtype.ext tau0_sq)
  have hdisj : Disjoint (MulAction.orbit (ConjAct hexadAut) t8)
      (MulAction.orbit (ConjAct hexadAut) t0) := by
    rw [Set.disjoint_left]
    intro y h8 h0
    obtain ⟨c, hc⟩ := isConj_iff.1
      ((ConjAct.mem_orbit_conjAct.1 h8).symm.trans (ConjAct.mem_orbit_conjAct.1 h0))
    have h := congrArg (fun p : hexadAut => (p : Equiv.Perm (Fin 22)) ((c : Equiv.Perm _) 0)) hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply, t8, t0, sigmaPerm_zero] at h
    exact tau0_ne _ h.symm
  have hS : S.ncard ≤ 1716 := by
    rw [← Nat.card_coe_set_eq, ← count_outer, ← card_m22_subtype]
    refine Nat.card_le_card_of_injective (fun y => ⟨⟨(y : hexadAut).1 * sigmaPerm,
      mul_mem_M22_of_not_mem (y : hexadAut).2 sigmaPerm_mem y.2.1 sigmaPerm_not_mem⟩, ?_⟩) ?_
    · rw [tf_eq rep_tab8]
      refine sqMulB_iff.2 ?_
      rw [mul_assoc _ sigmaPerm sigmaPerm, sigmaPerm_sq, mul_one]
      exact congrArg Subtype.val y.2.2
    · intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (Subtype.ext (mul_right_cancel hab))
  have h8 := card_le_ncard_orbit_mul t8 ((card_centralizer_le rep_tab8 sigmaPerm_mem
    sigmaPerm_not_mem sigmaPerm_sq).trans (by rw [count_cent8]))
  have h0 := card_le_ncard_orbit_mul t0 ((card_centralizer_le rep_tab0 tau0_mem
    tau0_not_mem tau0_sq).trans (by rw [count_cent0]))
  rw [card_hexadAut.1] at h8 h0
  have hU := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have heq : MulAction.orbit (ConjAct hexadAut) t8 ∪ MulAction.orbit (ConjAct hexadAut) t0 = S :=
    Set.eq_of_subset_of_ncard_le (Set.union_subset h8S h0S) (by omega) (Set.toFinite _)
  have hxS : (⟨x, hx⟩ : hexadAut) ∈ S := ⟨hxM, Subtype.ext hxx⟩
  rw [← heq] at hxS
  rcases hxS with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 (ConjAct.mem_orbit_conjAct.1 h)
    exact ⟨c, c.2, Or.inl (congrArg Subtype.val hc)⟩
  · obtain ⟨c, hc⟩ := isConj_iff.1 (ConjAct.mem_orbit_conjAct.1 h)
    exact ⟨c, c.2, Or.inr (congrArg Subtype.val hc)⟩

theorem inner_conj
    {y : Equiv.Perm (Fin 22)} (hy : y ∈ M22) (hyy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ g ∈ M22, g * y * g⁻¹ = m22gA := by
  set a' : M22 := ⟨m22gA, m22a.2⟩
  set S : Set M22 := {z | z * z = 1 ∧ z ≠ 1}
  have ha1 : a' ≠ 1 := fun h => by
    have := congrArg (fun p : M22 => (p : Equiv.Perm (Fin 22)) 0) h
    exact absurd this (by decide +kernel)
  have haS : MulAction.orbit (ConjAct M22) a' ⊆ S := by
    intro z hz
    obtain ⟨c, rfl⟩ := isConj_iff.1 (isConj_comm.1 (ConjAct.mem_orbit_conjAct.1 hz))
    refine ⟨?_, fun h => ha1 ?_⟩
    · rw [show c * a' * c⁻¹ * (c * a' * c⁻¹) = c * (a' * a') * c⁻¹ by group,
        show a' * a' = 1 from Subtype.ext m22gA_sq, mul_one, mul_inv_cancel]
    · have h' := congrArg (fun p => c⁻¹ * p * c) h
      simpa [mul_assoc] using h'
  have hS : S.ncard ≤ 1155 := by
    rw [← Nat.card_coe_set_eq, ← count_inner, ← card_m22_subtype]
    refine Nat.card_le_card_of_injective (fun z => ⟨z.1, ?_⟩) ?_
    · rw [Bool.and_eq_true, sqB_iff, Bool.not_eq_true', ← Bool.not_eq_true, eqB_id_iff]
      exact ⟨congrArg Subtype.val z.2.1, fun h => z.2.2 (Subtype.ext h)⟩
    · intro a b h
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
  have hc : Nat.card (Subgroup.centralizer {a'}) ≤ 384 := by
    rw [← count_centY, ← card_m22_subtype]
    refine Nat.card_le_card_of_injective (fun c => ⟨c.1, ?_⟩) ?_
    · rw [tf_eq rep_tabY]
      exact commB_iff.2 (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 c.2))
    · intro a b h
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
  have h1 := card_le_ncard_orbit_mul a' hc
  rw [card_M22] at h1
  have heq : MulAction.orbit (ConjAct M22) a' = S :=
    Set.eq_of_subset_of_ncard_le haS (by omega) (Set.toFinite _)
  have hyS : (⟨y, hy⟩ : M22) ∈ S := ⟨Subtype.ext hyy, fun h => hy1 (congrArg Subtype.val h)⟩
  rw [← heq] at hyS
  obtain ⟨c, hc⟩ := isConj_iff.1 (ConjAct.mem_orbit_conjAct.1 hyS)
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

theorem miss_false
    (x : M22) :
    missOut (tf tab8) list8 ⇑(x : Equiv.Perm (Fin 22)) = false ∧
      missOut (tf tab0) list0 ⇑(x : Equiv.Perm (Fin 22)) = false ∧
      missIn (tf tabY) listY ⇑(x : Equiv.Perm (Fin 22)) = false := by
  have h := forall_not_of_count count_miss x
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem complete_outer
    {τ : Equiv.Perm (Fin 22)} {T : Table} {C : List Table}
    (hT : Rep 22 T τ) (hτ : τ ∈ hexadAut) (hτM : τ ∉ M22) (hττ : τ * τ = 1)
    (hmiss : ∀ x : M22, missOut (tf T) C ⇑(x : Equiv.Perm (Fin 22)) = false)
    {z : Equiv.Perm (Fin 22)} (hz : z ∈ hexadAut) (hzz : z * z = 1) (hzτ : z * τ = τ * z)
    (hz1 : z ≠ 1) (hzτ' : z ≠ τ) : ∃ t ∈ C, Rep 22 t z := by
  have htf : tf T = ⇑τ := tf_eq hT
  by_cases hzM : z ∈ M22
  · have h := hmiss ⟨z, hzM⟩
    have h3 : eqB id ⇑z = false := by
      rw [← Bool.not_eq_true, eqB_id_iff]
      exact hz1
    rw [missOut, htf, sqB_iff.2 hzz, commB_iff.2 hzτ, h3] at h
    simp only [Bool.true_and, Bool.not_false, Bool.or_eq_false_iff, Bool.not_eq_false'] at h
    exact ⟨_, List.contains_iff_mem.1 h.1, rep_tableF z⟩
  · have hc : z * τ ∈ M22 := mul_mem_M22_of_not_mem hz hτ hzM hτM
    have h := hmiss ⟨z * τ, hc⟩
    have h1 : z * τ * (z * τ) = 1 := by
      rw [mul_assoc, ← mul_assoc τ z τ, ← hzτ, mul_assoc, hττ, mul_one, hzz]
    have h2 : z * τ * τ = τ * (z * τ) := by rw [← mul_assoc, ← hzτ]
    have h3 : eqB id ⇑(z * τ) = false := by
      rw [← Bool.not_eq_true, eqB_id_iff]
      intro h0
      exact hzτ' (by rw [← mul_one z, ← hττ, ← mul_assoc, h0, one_mul])
    have h4 : (fun i => (z * τ) (τ i)) = ⇑z := funext fun i => by
      rw [Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply τ τ, hττ, Equiv.Perm.one_apply]
    rw [missOut, htf, sqB_iff.2 h1, commB_iff.2 h2, h3] at h
    simp only [Bool.true_and, Bool.not_false, Bool.or_eq_false_iff, Bool.not_eq_false'] at h
    refine ⟨_, List.contains_iff_mem.1 h.2, ?_⟩
    rw [h4]
    exact rep_tableF z

theorem complete_inner
    {r : Equiv.Perm (Fin 22)} {T : Table} {C : List Table}
    (hT : Rep 22 T r) (hmiss : ∀ x : M22, missIn (tf T) C ⇑(x : Equiv.Perm (Fin 22)) = false)
    {z : Equiv.Perm (Fin 22)} (hz : z ∈ M22) (hzz : z * z = 1) (hzr : z * r = r * z)
    (hz1 : z ≠ 1) (hzr' : z ≠ r) : ∃ t ∈ C, Rep 22 t z := by
  have h := hmiss ⟨z, hz⟩
  have h3 : eqB id ⇑z = false := by
    rw [← Bool.not_eq_true, eqB_id_iff]
    exact hz1
  have h4 : eqB ⇑r ⇑z = false := by
    rw [← Bool.not_eq_true, eqB_iff]
    exact hzr'
  rw [missIn, tf_eq hT, sqB_iff.2 hzz, commB_iff.2 hzr, h3, h4] at h
  simp only [Bool.true_and, Bool.not_false, Bool.not_eq_false'] at h
  exact ⟨_, List.contains_iff_mem.1 h, rep_tableF z⟩

theorem bound_tau8
    {X : Subgroup (Equiv.Perm (Fin 22))} (hX : X ≤ hexadAut)
    (hsq : ∀ x ∈ X, x * x = 1) (h8 : sigmaPerm ∈ X) : Nat.card X * Nat.card (fixV X hX) ≤ 256 :=
  bound_of_rootCheck hX hsq rep_tab8 h8 (fun z hz hz1 hzr => complete_outer rep_tab8
    sigmaPerm_mem sigmaPerm_not_mem sigmaPerm_sq (fun x => (miss_false x).1) (hX hz) (hsq z hz)
    (commute_of_sq hsq hz h8) hz1 hzr) search_check.2.2.2.1 search_check.1

theorem bound_tau0
    {X : Subgroup (Equiv.Perm (Fin 22))} (hX : X ≤ hexadAut)
    (hsq : ∀ x ∈ X, x * x = 1) (h0 : tau0 ∈ X) : Nat.card X * Nat.card (fixV X hX) ≤ 256 :=
  bound_of_rootCheck hX hsq rep_tab0 h0 (fun z hz hz1 hzr => complete_outer rep_tab0
    tau0_mem tau0_not_mem tau0_sq (fun x => (miss_false x).2.1) (hX hz) (hsq z hz)
    (commute_of_sq hsq hz h0) hz1 hzr) search_check.2.2.2.2.1 search_check.2.1

theorem bound_a
    {X : Subgroup (Equiv.Perm (Fin 22))} (hX : X ≤ hexadAut) (hXM : X ≤ M22)
    (hsq : ∀ x ∈ X, x * x = 1) (ha : m22gA ∈ X) : Nat.card X * Nat.card (fixV X hX) ≤ 512 :=
  bound_of_rootCheck hX hsq rep_tabY ha (fun z hz hz1 hza => complete_inner rep_tabY
    (fun x => (miss_false x).2.2) (hXM hz) (hsq z hz) (commute_of_sq hsq hz ha) hz1 hza)
    search_check.2.2.2.2.2 search_check.2.2.1

theorem map_conj_sq {X : Subgroup (Equiv.Perm (Fin 22))} (hsq : ∀ x ∈ X, x * x = 1)
    (g : Equiv.Perm (Fin 22)) : ∀ y ∈ X.map (MulAut.conj g).toMonoidHom, y * y = 1 := by
  rintro _ ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [show g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group, hsq y hy, mul_one,
    mul_inv_cancel]

theorem conj_mem_map {X : Subgroup (Equiv.Perm (Fin 22))} {x : Equiv.Perm (Fin 22)}
    (hx : x ∈ X) (g : Equiv.Perm (Fin 22)) : g * x * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom :=
  Subgroup.mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem card_mul_card_fixed_le_outer
    {X : Subgroup (Equiv.Perm (Fin 22))} (hX : X ≤ hexadAut)
    (hsq : ∀ x ∈ X, x * x = 1) (hout : ¬ X ≤ M22) :
    Nat.card X * Nat.card {v : toddModule // ∀ x (hx : x ∈ X), toddAct (hX hx) v = v} ≤
      2 ^ 8 := by
  obtain ⟨x, hxX, hxM⟩ := IsConcreteLE.not_le_iff_exists.1 hout
  obtain ⟨g, hg, hgx⟩ := outer_conj (hX hxX) hxM (hsq x hxX)
  have hX' : X.map (MulAut.conj g).toMonoidHom ≤ hexadAut := by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hg (hX hy)) (inv_mem hg)
  change Nat.card X * Nat.card (fixV X hX) ≤ 2 ^ 8
  rw [← card_conj hX hg hX']
  have hmem := conj_mem_map hxX g
  rcases hgx with h | h <;> rw [h] at hmem
  · exact (bound_tau8 hX' (map_conj_sq hsq g) hmem).trans (by norm_num)
  · exact (bound_tau0 hX' (map_conj_sq hsq g) hmem).trans (by norm_num)

theorem card_mul_card_fixed_le_inner
    {X : Subgroup (Equiv.Perm (Fin 22))} (hX : X ≤ M22)
    (hsq : ∀ x ∈ X, x * x = 1) (hne : X ≠ ⊥) :
    Nat.card X * Nat.card {v : toddModule //
      ∀ x (hx : x ∈ X), toddAct (M22_le_hexadAut (hX hx)) v = v} ≤ 2 ^ 9 := by
  obtain ⟨⟨y, hyX⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨g, hg, hgy⟩ := inner_conj (hX hyX) (hsq y hyX) hy1'
  have hXM' : X.map (MulAut.conj g).toMonoidHom ≤ M22 := by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem hg (hX hz)) (inv_mem hg)
  have hXA : X ≤ hexadAut := hX.trans M22_le_hexadAut
  change Nat.card X * Nat.card (fixV X hXA) ≤ 2 ^ 9
  rw [← card_conj hXA (M22_le_hexadAut hg) (hXM'.trans M22_le_hexadAut)]
  have hmem := conj_mem_map hyX g
  rw [hgy] at hmem
  exact (bound_a _ hXM' (map_conj_sq hsq g) hmem).trans (by norm_num)

end CFSG.EvenSmallLie.UnitarySix.Hunt
