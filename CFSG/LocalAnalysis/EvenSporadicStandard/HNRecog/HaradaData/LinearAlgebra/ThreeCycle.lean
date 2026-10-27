module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.Defs
public import Std.Tactic.BVDecide.Normalize.Prop
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.ThreeCycleK

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

@[expose] def ofNat6 (n : ℕ) : V6 := fun i => (((n >>> i.val) % 2 : ℕ) : ZMod 2)

@[expose] def ch1 : V6 := ofNat6 12
@[expose] def ch2 : V6 := ofNat6 7
@[expose] def ch3 : V6 := ofNat6 17
@[expose] def ch4 : V6 := ofNat6 3
@[expose] def ch5 : V6 := ofNat6 13
@[expose] def ch6 : V6 := ofNat6 35
@[expose] def ch7 : V6 := tv

set_option maxRecDepth 100000 in
theorem chain_facts :
    qp ch1 = 1 ∧ qp ch2 = 1 ∧ qp ch3 = 1 ∧ qp ch4 = 1 ∧ qp ch5 = 1 ∧ qp ch6 = 1 ∧ qp ch7 = 1 ∧
    bil ch1 ch2 = 1 ∧ bil ch2 ch3 = 1 ∧ bil ch3 ch4 = 1 ∧ bil ch4 ch5 = 1 ∧ bil ch5 ch6 = 1 ∧
    bil ch6 ch7 = 1 ∧
    bil ch1 ch3 = 0 ∧ bil ch1 ch4 = 0 ∧ bil ch1 ch5 = 0 ∧ bil ch1 ch6 = 0 ∧ bil ch1 ch7 = 0 ∧
    bil ch2 ch4 = 0 ∧ bil ch2 ch5 = 0 ∧ bil ch2 ch6 = 0 ∧ bil ch2 ch7 = 0 ∧
    bil ch3 ch5 = 0 ∧ bil ch3 ch6 = 0 ∧ bil ch3 ch7 = 0 ∧
    bil ch4 ch6 = 0 ∧ bil ch4 ch7 = 0 ∧ bil ch5 ch7 = 0 := by
  decide +kernel

@[expose] def w3 : Equiv.Perm V6 := transv ch1 * transv ch2

@[expose] def Fix3 : Finset V6 := Finset.univ.filter fun x => w3 x = x

private theorem OmegaPlus_eq : OmegaPlus = Subgroup.closure
    {g : Equiv.Perm V6 | ∃ u v : V6, qp u = 1 ∧ qp v = 1 ∧ g = transv u * transv v} := rfl

set_option maxRecDepth 100000 in
private theorem w3_cube : w3 * w3 * w3 = 1 :=
  ThreeCycleK.cube_of ThreeCycleK.cd_w3 ThreeCycleK.w3_cube_K

theorem mem_Fix3 {x : V6} : x ∈ Fix3 ↔ w3 x = x := by
  rw [Fix3, Finset.mem_filter]
  simp

theorem w3_mem_omegaPlus : w3 ∈ OmegaPlus := by
  rw [OmegaPlus_eq]
  exact Subgroup.subset_closure ⟨ch1, ch2, chain_facts.1, chain_facts.2.1, rfl⟩

theorem w3_pow_three : w3 ^ 3 = 1 := by
  have h : w3 ^ 3 = w3 * w3 * w3 := by
    rw [pow_succ, pow_succ, pow_succ]
    simp
  rw [h, w3_cube]

set_option maxRecDepth 100000 in
theorem w3_ne_one : w3 ≠ 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem w3_tv : w3 tv = tv := by decide +kernel

set_option maxRecDepth 100000 in
theorem card_Fix3 : Fix3.card = 16 := by decide +kernel

set_option maxRecDepth 100000 in
theorem card_Fix3_qp_one : (Fix3.filter fun x => qp x = 1).card = 10 := by decide +kernel

set_option maxRecDepth 100000 in
theorem w3_moves_ch1 : w3 ch1 ≠ ch1 ∧ (w3 * w3) ch1 ≠ ch1 := by decide +kernel

@[expose] def gA : Equiv.Perm V6 := transv ch4 * transv ch5

@[expose] def gB : Equiv.Perm V6 := transv ch5 * transv ch6

@[expose] def gC : Equiv.Perm V6 := transv ch6 * transv ch7

@[expose] def A5g : Subgroup (Equiv.Perm V6) := Subgroup.closure {gA, gB, gC}

private theorem A5g_eq :
    A5g = Subgroup.closure ({gA, gB, gC} : Set (Equiv.Perm V6)) := rfl

private theorem gA_mem : gA ∈ A5g :=
  Subgroup.subset_closure (show gA ∈ ({gA, gB, gC} : Set (Equiv.Perm V6)) by simp)

private theorem gB_mem : gB ∈ A5g :=
  Subgroup.subset_closure (show gB ∈ ({gA, gB, gC} : Set (Equiv.Perm V6)) by simp)

private theorem gC_mem : gC ∈ A5g :=
  Subgroup.subset_closure (show gC ∈ ({gA, gB, gC} : Set (Equiv.Perm V6)) by simp)

private theorem qp_ch4 : qp ch4 = 1 := chain_facts.2.2.2.1
private theorem qp_ch5 : qp ch5 = 1 := chain_facts.2.2.2.2.1
private theorem qp_ch6 : qp ch6 = 1 := chain_facts.2.2.2.2.2.1
private theorem qp_ch7 : qp ch7 = 1 := chain_facts.2.2.2.2.2.2.1

set_option maxRecDepth 100000 in
private theorem comm_gA_w3 : gA * w3 = w3 * gA :=
  ThreeCycleK.comm_of ThreeCycleK.cd_gA ThreeCycleK.cd_w3 ThreeCycleK.comm_gA_w3_K

set_option maxRecDepth 100000 in
private theorem comm_gB_w3 : gB * w3 = w3 * gB :=
  ThreeCycleK.comm_of ThreeCycleK.cd_gB ThreeCycleK.cd_w3 ThreeCycleK.comm_gB_w3_K

set_option maxRecDepth 100000 in
private theorem comm_gC_w3 : gC * w3 = w3 * gC :=
  ThreeCycleK.comm_of ThreeCycleK.cd_gC ThreeCycleK.cd_w3 ThreeCycleK.comm_gC_w3_K

set_option maxRecDepth 100000 in
private theorem fix_gA_ch1 : gA ch1 = ch1 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem fix_gB_ch1 : gB ch1 = ch1 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem fix_gC_ch1 : gC ch1 = ch1 := by decide +kernel

private def gen (k : Fin 3) : Equiv.Perm V6 :=
  if k = 0 then gA else if k = 1 then gB else gC

private def evalWord : List (Fin 3) → Equiv.Perm V6
  | [] => 1
  | k :: ks => gen k * evalWord ks

private def words : List (List (Fin 3)) :=
  [[], [0], [1], [2], [0,0], [0,1], [0,2], [1,0], [1,1], [1,2], [2,0], [2,1], [2,2],
   [0,0,1], [0,0,2], [0,1,1], [0,1,2], [0,2,0], [0,2,1], [0,2,2], [1,0,0], [1,1,0], [1,1,2],
   [1,2,0], [1,2,2], [2,0,0], [2,0,1], [2,1,0], [2,1,1], [2,2,0], [2,2,1],
   [0,0,2,1], [0,0,2,2], [0,1,1,0], [0,2,0,0], [0,2,0,1], [0,2,1,0], [0,2,1,1], [0,2,2,0],
   [1,1,2,0], [1,2,2,0], [1,2,2,1], [2,0,0,1], [2,0,0,2], [2,0,1,1], [2,1,0,0], [2,1,1,0],
   [2,2,0,0], [2,2,1,0],
   [0,0,2,1,0], [0,2,0,0,1], [0,2,0,1,1], [0,2,1,0,0], [0,2,1,1,0], [0,2,2,0,0],
   [1,2,2,0,0], [1,2,2,1,0], [2,0,1,1,0],
   [0,0,2,1,0,0], [0,2,0,1,1,0]]

private def A5list : List (Equiv.Perm V6) := words.map evalWord

private theorem gen_mem (k : Fin 3) : gen k ∈ A5g := by
  fin_cases k <;> simp [gen, gA_mem, gB_mem, gC_mem]

private theorem evalWord_mem (w : List (Fin 3)) : evalWord w ∈ A5g := by
  induction w with
  | nil => exact A5g.one_mem
  | cons k ks ih =>
    change gen k * evalWord ks ∈ A5g
    exact A5g.mul_mem (gen_mem k) ih

set_option maxRecDepth 100000 in
private theorem one_mem_list : (1 : Equiv.Perm V6) ∈ A5list := by decide +kernel

set_option maxRecDepth 100000 in
private theorem gA_mem_list : gA ∈ A5list := by decide +kernel

set_option maxRecDepth 100000 in
private theorem gB_mem_list : gB ∈ A5list := by decide +kernel

set_option maxRecDepth 100000 in
private theorem gC_mem_list : gC ∈ A5list := by decide +kernel

set_option maxRecDepth 100000 in
private theorem A5list_mul_gen_all :
    A5list.all (fun g => decide (∀ k : Fin 3, g * gen k ∈ A5list)) = true := by
  have hgen := ThreeCycleK.gen_codes (gen := gen) ThreeCycleK.cd_gA ThreeCycleK.cd_gB
    ThreeCycleK.cd_gC
  have hA := ThreeCycleK.map_cd_of (ev := evalWord) rfl (fun _ _ => rfl) hgen (A := A5list) rfl
  exact List.all_eq_true.mpr fun g hg =>
    decide_eq_true fun k => ThreeCycleK.mul_mem_of hA hgen hg k

private theorem A5list_mul_gen (g : Equiv.Perm V6) (hg : g ∈ A5list) (k : Fin 3) :
    g * gen k ∈ A5list := by
  have h' : decide (∀ k : Fin 3, g * gen k ∈ A5list) = true :=
    List.all_eq_true.mp A5list_mul_gen_all g hg
  exact of_decide_eq_true h' k

set_option maxRecDepth 100000 in
private theorem A5list_inv_all : A5list.all (fun g => decide (g⁻¹ ∈ A5list)) = true := by
  have hgen := ThreeCycleK.gen_codes (gen := gen) ThreeCycleK.cd_gA ThreeCycleK.cd_gB
    ThreeCycleK.cd_gC
  have hA := ThreeCycleK.map_cd_of (ev := evalWord) rfl (fun _ _ => rfl) hgen (A := A5list) rfl
  exact List.all_eq_true.mpr fun g hg => decide_eq_true (ThreeCycleK.inv_mem_of hA hg)

private theorem A5list_inv (g : Equiv.Perm V6) (hg : g ∈ A5list) : g⁻¹ ∈ A5list := by
  have h' : decide (g⁻¹ ∈ A5list) = true := List.all_eq_true.mp A5list_inv_all g hg
  exact of_decide_eq_true h'

private theorem A5list_mul_evalWord (x : Equiv.Perm V6) (hx : x ∈ A5list) :
    ∀ w : List (Fin 3), x * evalWord w ∈ A5list := by
  intro w
  induction w generalizing x with
  | nil => simpa [evalWord] using hx
  | cons k ks ih =>
    rw [show evalWord (k :: ks) = gen k * evalWord ks from rfl, ← mul_assoc]
    exact ih (x * gen k) (A5list_mul_gen x hx k)

private theorem hmem (g : Equiv.Perm V6) : g ∈ A5g ↔ g ∈ A5list := by
  constructor
  · intro hg
    rw [A5g_eq] at hg
    refine Subgroup.closure_induction (p := fun x _ => x ∈ A5list) ?mem ?one ?mul ?inv hg
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact gA_mem_list
      · exact gB_mem_list
      · exact gC_mem_list
    · exact one_mem_list
    · intro x y hx hy hpx hpy
      unfold A5list at hpy
      obtain ⟨w, -, hw⟩ := List.mem_map.mp hpy
      rw [← hw]
      exact A5list_mul_evalWord x hpx w
    · intro x hx hpx
      exact A5list_inv x hpx
  · intro hg
    unfold A5list at hg
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hg
    rw [← hw]
    exact evalWord_mem w

set_option maxRecDepth 100000 in
private theorem A5g_no_fixed_gen :
    ∀ x ∈ Fix3, gA x = x → gB x = x → gC x = x → x = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem comm_id_gA :
    gB * (gB * gC * gC * gA * gA) * gB⁻¹ * (gB * gC * gC * gA * gA)⁻¹ = gA :=
  ThreeCycleK.commA_of ThreeCycleK.cd_gA ThreeCycleK.cd_gB ThreeCycleK.cd_gC

set_option maxRecDepth 100000 in
private theorem comm_id_gB : gA * (gA * gA * gC) * gA⁻¹ * (gA * gA * gC)⁻¹ = gB :=
  ThreeCycleK.commB_of ThreeCycleK.cd_gA ThreeCycleK.cd_gB ThreeCycleK.cd_gC

set_option maxRecDepth 100000 in
private theorem comm_id_gC : gB * (gA * gC * gA) * gB⁻¹ * (gA * gC * gA)⁻¹ = gC :=
  ThreeCycleK.commC_of ThreeCycleK.cd_gA ThreeCycleK.cd_gB ThreeCycleK.cd_gC

theorem A5g_le_omegaPlus : A5g ≤ OmegaPlus := by
  rw [A5g_eq, OmegaPlus_eq, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact Subgroup.subset_closure ⟨ch4, ch5, qp_ch4, qp_ch5, rfl⟩
  · exact Subgroup.subset_closure ⟨ch5, ch6, qp_ch5, qp_ch6, rfl⟩
  · exact Subgroup.subset_closure ⟨ch6, ch7, qp_ch6, qp_ch7, rfl⟩

theorem A5g_comm_w3 : ∀ g ∈ A5g, g * w3 = w3 * g := by
  have hle : A5g ≤ Subgroup.centralizer ({w3} : Set (Equiv.Perm V6)) := by
    rw [A5g_eq, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr comm_gA_w3
    · exact Subgroup.mem_centralizer_singleton_iff.mpr comm_gB_w3
    · exact Subgroup.mem_centralizer_singleton_iff.mpr comm_gC_w3
  intro g hg
  have hg' := hle hg
  rwa [Subgroup.mem_centralizer_singleton_iff] at hg'

theorem A5g_fix_ch1 : ∀ g ∈ A5g, g ch1 = ch1 := by
  intro g hg
  rw [A5g_eq] at hg
  refine Subgroup.closure_induction (p := fun x _ => x ch1 = ch1) ?mem ?one ?mul ?inv hg
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact fix_gA_ch1
    · exact fix_gB_ch1
    · exact fix_gC_ch1
  · rfl
  · intro x y hx hy hpx hpy
    change x (y ch1) = ch1
    rw [hpy, hpx]
  · intro x hx hpx
    apply x.injective
    rw [hpx]
    exact Equiv.apply_symm_apply x ch1

theorem A5g_perfect : ⁅A5g, A5g⁆ = A5g := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact A5g.mul_mem (A5g.mul_mem (A5g.mul_mem hx hy) (A5g.inv_mem hx)) (A5g.inv_mem hy)
  · have hA : gA ∈ ⁅A5g, A5g⁆ := by
      have h2 : gB * gC * gC * gA * gA ∈ A5g :=
        A5g.mul_mem (A5g.mul_mem (A5g.mul_mem (A5g.mul_mem gB_mem gC_mem) gC_mem) gA_mem) gA_mem
      have hm := Subgroup.commutator_mem_commutator (H₁ := A5g) (H₂ := A5g)
        (g₁ := gB) (g₂ := gB * gC * gC * gA * gA) gB_mem h2
      rw [commutatorElement_def] at hm
      rwa [comm_id_gA] at hm
    have hB : gB ∈ ⁅A5g, A5g⁆ := by
      have h2 : gA * gA * gC ∈ A5g :=
        A5g.mul_mem (A5g.mul_mem gA_mem gA_mem) gC_mem
      have hm := Subgroup.commutator_mem_commutator (H₁ := A5g) (H₂ := A5g)
        (g₁ := gA) (g₂ := gA * gA * gC) gA_mem h2
      rw [commutatorElement_def] at hm
      rwa [comm_id_gB] at hm
    have hC : gC ∈ ⁅A5g, A5g⁆ := by
      have h2 : gA * gC * gA ∈ A5g :=
        A5g.mul_mem (A5g.mul_mem gA_mem gC_mem) gA_mem
      have hm := Subgroup.commutator_mem_commutator (H₁ := A5g) (H₂ := A5g)
        (g₁ := gB) (g₂ := gA * gC * gA) gB_mem h2
      rw [commutatorElement_def] at hm
      rwa [comm_id_gC] at hm
    change Subgroup.closure ({gA, gB, gC} : Set (Equiv.Perm V6)) ≤ ⁅A5g, A5g⁆
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hC

theorem A5g_no_fixed : ∀ x ∈ Fix3, (∀ g ∈ A5g, g x = x) → x = 0 := by
  intro x hx h
  exact A5g_no_fixed_gen x hx (h gA gA_mem) (h gB gB_mem) (h gC gC_mem)

set_option maxRecDepth 100000 in
theorem Fix3_comm_span : ∀ x ∈ Fix3, ∃ c0 c1 c2 c3 : ZMod 2,
    x = c0 • (ofNat6 3 + gA (ofNat6 3)) + c1 • (ofNat6 13 + gA (ofNat6 13)) +
      c2 • (ofNat6 13 + gB (ofNat6 13)) + c3 • (ofNat6 32 + gC (ofNat6 32)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem commV_mem : ofNat6 3 ∈ Fix3 ∧ ofNat6 13 ∈ Fix3 ∧ ofNat6 32 ∈ Fix3 := by
  decide +kernel

@[expose] def uV : Equiv.Perm V6 := gA * gB

@[expose] def wV : Equiv.Perm V6 := gB * gA

@[expose] def Vg : Subgroup (Equiv.Perm V6) := Subgroup.closure {uV, wV}

private theorem Vg_eq :
    Vg = Subgroup.closure ({uV, wV} : Set (Equiv.Perm V6)) := rfl

theorem Vg_le_A5g : Vg ≤ A5g := by
  rw [Vg_eq, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact A5g.mul_mem gA_mem gB_mem
  · exact A5g.mul_mem gB_mem gA_mem

set_option maxRecDepth 100000 in
theorem uV_wV_facts : uV * uV = 1 ∧ wV * wV = 1 ∧ uV * wV = wV * uV ∧ uV ≠ 1 ∧ wV ≠ 1 ∧
    uV ≠ wV :=
  ThreeCycleK.uV_wV_of ThreeCycleK.cd_uV ThreeCycleK.cd_wV

private def T : Finset (Equiv.Perm V6) := {1, uV, wV, uV * wV}

private theorem mem_T {g : Equiv.Perm V6} :
    g ∈ T ↔ g = 1 ∨ g = uV ∨ g = wV ∨ g = uV * wV := by
  simp [T]

set_option maxRecDepth 100000 in
private theorem card_T : T.card = 4 := by decide +kernel

theorem mem_Vg_iff {g : Equiv.Perm V6} : g ∈ Vg ↔ g = 1 ∨ g = uV ∨ g = wV ∨ g = uV * wV := by
  constructor
  · intro hg
    rw [Vg_eq] at hg
    refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = uV ∨ x = wV ∨ x = uV * wV)
      ?mem ?one ?mul ?inv hg
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · intro x y hx hy hpx hpy
      exact ThreeCycleK.klein_mul uV_wV_facts.1 uV_wV_facts.2.1 uV_wV_facts.2.2.1 hpx hpy
    · intro x hx hpx
      exact ThreeCycleK.klein_inv uV_wV_facts.1 uV_wV_facts.2.1 uV_wV_facts.2.2.1 hpx
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem card_Vg : Nat.card Vg = 4 := by
  have hset : (Vg : Set (Equiv.Perm V6)) = (T : Set (Equiv.Perm V6)) := by
    ext g
    rw [Finset.mem_coe, mem_T]
    exact mem_Vg_iff
  calc Nat.card Vg
      = Nat.card (T : Set (Equiv.Perm V6)) :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun g => Set.ext_iff.mp hset g))
    _ = (T : Set (Equiv.Perm V6)).ncard := Nat.card_coe_set_eq _
    _ = T.card := Set.ncard_coe_finset _
    _ = 4 := card_T

set_option maxRecDepth 100000 in
theorem Fix3_free : ∀ x ∈ Fix3, ∃ c0 c1 c2 c3 : ZMod 2,
    x = c0 • tv + c1 • uV tv + c2 • wV tv + c3 • (uV * wV) tv := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem card_fix_uV : (Fix3.filter fun x => uV x = x).card = 4 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem card_fix_wV : (Fix3.filter fun x => wV x = x).card = 4 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem card_fix_uwV : (Fix3.filter fun x => (uV * wV) x = x).card = 4 := by decide +kernel

theorem card_fix_Vg_ne_one : ∀ g ∈ Vg, g ≠ 1 → (Fix3.filter fun x => g x = x).card = 4 := by
  intro g hg hne
  rw [mem_Vg_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact absurd rfl hne
  · exact card_fix_uV
  · exact card_fix_wV
  · exact card_fix_uwV

set_option maxRecDepth 100000 in
theorem card_fix_Vg : (Fix3.filter fun x => uV x = x ∧ wV x = x).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem Fix3_split_u : ∀ s ∈ Fix3, uV s = s → ∃ x ∈ Fix3, x + uV x = s := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem Fix3_split_w : ∀ s ∈ Fix3, wV s = s → ∃ x ∈ Fix3, x + wV x = s := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem Fix3_split_uw : ∀ s ∈ Fix3, uV s = s → wV s = s →
    ∃ y ∈ Fix3, uV y = y ∧ y + wV y = s := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem Fix3_Vg_fixed_qp_zero : ∀ x ∈ Fix3, uV x = x → wV x = x → qp x = 0 := by
  decide +kernel

theorem tv_mem_Fix3 : tv ∈ Fix3 :=
  mem_Fix3.mpr w3_tv

set_option maxRecDepth 100000 in
private theorem A5list_center_gen_all :
    A5list.all (fun g =>
      decide ((g * gA = gA * g) ∧ (g * gB = gB * g) ∧ (g * gC = gC * g) → g = 1)) = true := by
  have hgen := ThreeCycleK.gen_codes (gen := gen) ThreeCycleK.cd_gA ThreeCycleK.cd_gB
    ThreeCycleK.cd_gC
  have hA := ThreeCycleK.map_cd_of (ev := evalWord) rfl (fun _ _ => rfl) hgen (A := A5list) rfl
  exact List.all_eq_true.mpr fun g hg => decide_eq_true fun h =>
    ThreeCycleK.center_of hA ThreeCycleK.cd_gA ThreeCycleK.cd_gB ThreeCycleK.cd_gC hg h

theorem A5g_center_trivial : ∀ g ∈ A5g, (∀ h ∈ A5g, g * h = h * g) → g = 1 := by
  intro g hg hcomm
  have hgl : g ∈ A5list := (hmem g).mp hg
  have h' : decide ((g * gA = gA * g) ∧ (g * gB = gB * g) ∧ (g * gC = gC * g) → g = 1) = true :=
    List.all_eq_true.mp A5list_center_gen_all g hgl
  exact of_decide_eq_true h' ⟨hcomm gA gA_mem, hcomm gB gB_mem, hcomm gC gC_mem⟩

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
