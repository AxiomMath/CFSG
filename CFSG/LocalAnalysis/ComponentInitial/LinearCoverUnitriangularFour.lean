module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourKernelStructure
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup Matrix LinearFlag LinearFieldFourKernel CFSG.ComponentClassification
open scoped commutatorElement

abbrev U4 : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) := unitriangular 4 (ZMod 2)

@[expose] def mkU4 (M : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (h : M.IsUpperTriangular ∧ ∀ i, M i i = 1) : U4 :=
  ⟨⟨M, by rw [det_of_isUpperTriangular h.1]; exact Finset.prod_eq_one fun i _ => h.2 i⟩,
    fun _ _ hij => h.1 hij, h.2⟩

theorem U4_ext {u v : U4}
    (h : ((u : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      ((v : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) : u = v :=
  Subtype.ext (Subtype.ext h)

@[expose] def mA : Matrix (Fin 4) (Fin 4) (ZMod 2) := 1 + single 0 1 1
@[expose] def mB : Matrix (Fin 4) (Fin 4) (ZMod 2) := 1 + single 1 2 1
@[expose] def mC : Matrix (Fin 4) (Fin 4) (ZMod 2) := 1 + single 2 3 1
@[expose] def mD : Matrix (Fin 4) (Fin 4) (ZMod 2) := 1 + single 0 2 1
@[expose] def mE : Matrix (Fin 4) (Fin 4) (ZMod 2) := 1 + single 1 3 1
@[expose] def mF : Matrix (Fin 4) (Fin 4) (ZMod 2) := 1 + single 0 3 1

@[expose] def u4a : U4 := mkU4 mA (by decide)
@[expose] def u4b : U4 := mkU4 mB (by decide)
@[expose] def u4c : U4 := mkU4 mC (by decide)
@[expose] def u4d : U4 := mkU4 mD (by decide)
@[expose] def u4e : U4 := mkU4 mE (by decide)
@[expose] def u4f : U4 := mkU4 mF (by decide)

theorem u4a_mul_self : u4a * u4a = 1 := U4_ext (by change mA * mA = 1; decide)
theorem u4b_mul_self : u4b * u4b = 1 := U4_ext (by change mB * mB = 1; decide)
theorem u4c_mul_self : u4c * u4c = 1 := U4_ext (by change mC * mC = 1; decide)
theorem u4d_mul_self : u4d * u4d = 1 := U4_ext (by change mD * mD = 1; decide)

theorem u4_commutator_ab : ⁅u4a, u4b⁆ = u4d := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right u4a_mul_self,
    inv_eq_of_mul_eq_one_right u4b_mul_self]
  exact U4_ext (by change mA * mB * mA * mB = mD; decide)

theorem u4_commutator_bc : ⁅u4b, u4c⁆ = u4e := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right u4b_mul_self,
    inv_eq_of_mul_eq_one_right u4c_mul_self]
  exact U4_ext (by change mB * mC * mB * mC = mE; decide)

theorem u4_commutator_dc : ⁅u4d, u4c⁆ = u4f := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right u4d_mul_self,
    inv_eq_of_mul_eq_one_right u4c_mul_self]
  exact U4_ext (by change mD * mC * mD * mC = mF; decide)

theorem u4_comm_ac : ⁅u4a, u4c⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (U4_ext (by change mA * mC = mC * mA; decide))

theorem u4_comm_da : ⁅⁅u4a, u4b⁆, u4a⁆ = 1 := by
  rw [u4_commutator_ab]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (U4_ext (by change mD * mA = mA * mD; decide))

theorem u4_comm_db : ⁅⁅u4a, u4b⁆, u4b⁆ = 1 := by
  rw [u4_commutator_ab]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (U4_ext (by change mD * mB = mB * mD; decide))

theorem u4_comm_eb : ⁅⁅u4b, u4c⁆, u4b⁆ = 1 := by
  rw [u4_commutator_bc]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (U4_ext (by change mE * mB = mB * mE; decide))

theorem u4_comm_ec : ⁅⁅u4b, u4c⁆, u4c⁆ = 1 := by
  rw [u4_commutator_bc]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (U4_ext (by change mE * mC = mC * mE; decide))

theorem u4_comm_de : ⁅⁅u4a, u4b⁆, ⁅u4b, u4c⁆⁆ = 1 := by
  rw [u4_commutator_ab, u4_commutator_bc]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (U4_ext (by change mD * mE = mE * mD; decide))

theorem u4_def_eq_one (i j k : Bool)
    (h : (if i then u4d else 1) * (if j then u4e else 1) * (if k then u4f else 1) = 1) :
    i = false ∧ j = false ∧ k = false := by
  have key : ∀ i j k : Bool, (if i then mD else 1) * (if j then mE else 1) * (if k then mF else 1)
      = (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) → i = false ∧ j = false ∧ k = false := by decide
  apply key
  have h' := congrArg (fun u : U4 =>
    ((u : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  cases i <;> cases j <;> cases k <;> exact h'

@[expose] def matU4 (v : Fin 6 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  1 + single 0 1 (v 0) + single 1 2 (v 1) + single 2 3 (v 2) + single 0 2 (v 3) +
    single 1 3 (v 4) + single 0 3 (v 5)

theorem matU4_eq (v : Fin 6 → ZMod 2) :
    matU4 v = mF ^ (v 5 - v 0 * v 1 * v 2 - (v 3 - v 0 * v 1) * v 2).val *
      mE ^ (v 4 - v 1 * v 2).val * mD ^ (v 3 - v 0 * v 1).val * mA ^ (v 0).val *
        mB ^ (v 1).val * mC ^ (v 2).val := by
  revert v
  decide

theorem closure_u4abc : Subgroup.closure {u4a, u4b, u4c} = ⊤ := by
  rw [eq_top_iff]
  intro u _
  set H := Subgroup.closure {u4a, u4b, u4c}
  have ha : u4a ∈ H := subset_closure (Set.mem_insert _ _)
  have hb : u4b ∈ H := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hc : u4c ∈ H := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hcomm : ∀ g h : U4, g ∈ H → h ∈ H → ⁅g, h⁆ ∈ H := fun g h hg hh => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hd : u4d ∈ H := by rw [← u4_commutator_ab]; exact hcomm _ _ ha hb
  have he : u4e ∈ H := by rw [← u4_commutator_bc]; exact hcomm _ _ hb hc
  have hf : u4f ∈ H := by rw [← u4_commutator_dc]; exact hcomm _ _ hd hc
  obtain ⟨hl, hdiag⟩ := mem_unitriangular.mp u.2
  set M := ((u : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
  set v : Fin 6 → ZMod 2 := ![M 0 1, M 1 2, M 2 3, M 0 2, M 1 3, M 0 3]
  have hM : M = matU4 v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matU4, v, hdiag, hl 1 0 (by decide), hl 2 0 (by decide), hl 3 0 (by decide),
        hl 2 1 (by decide), hl 3 1 (by decide), hl 3 2 (by decide)]
  have hu : u = u4f ^ (v 5 - v 0 * v 1 * v 2 - (v 3 - v 0 * v 1) * v 2).val *
      u4e ^ (v 4 - v 1 * v 2).val * u4d ^ (v 3 - v 0 * v 1).val * u4a ^ (v 0).val *
        u4b ^ (v 1).val * u4c ^ (v 2).val := by
    apply U4_ext
    change M = _
    rw [hM, matU4_eq]
    rfl
  rw [hu]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (pow_mem hf _) (pow_mem he _))
    (pow_mem hd _)) (pow_mem ha _)) (pow_mem hb _)) (pow_mem hc _)

theorem mem_closure_three_involutions {G : Type*} [Group G] {d e f : G} (hd : d * d = 1)
    (he : e * e = 1) (hf : f * f = 1) (hde : Commute d e) (hdf : Commute d f) (hef : Commute e f)
    {g : G} (hg : g ∈ Subgroup.closure {d, e, f}) :
    ∃ i j k : Bool, g = (if i then d else 1) * (if j then e else 1) * (if k then f else 1) := by
  have cde : ∀ i j : Bool, Commute (if i then d else 1) (if j then e else 1) := by
    intro i j; cases i <;> cases j <;> simp [hde]
  have cdf : ∀ i j : Bool, Commute (if i then d else 1) (if j then f else 1) := by
    intro i j; cases i <;> cases j <;> simp [hdf]
  have cef : ∀ i j : Bool, Commute (if i then e else 1) (if j then f else 1) := by
    intro i j; cases i <;> cases j <;> simp [hef]
  have sd : ∀ i i' : Bool, (if i then d else 1) * (if i' then d else 1) =
      if xor i i' then d else 1 := by
    intro i i'; cases i <;> cases i' <;> simp [hd]
  have se : ∀ i i' : Bool, (if i then e else 1) * (if i' then e else 1) =
      if xor i i' then e else 1 := by
    intro i i'; cases i <;> cases i' <;> simp [he]
  have sf : ∀ i i' : Bool, (if i then f else 1) * (if i' then f else 1) =
      if xor i i' then f else 1 := by
    intro i i'; cases i <;> cases i' <;> simp [hf]
  have invd : ∀ i : Bool, (if i then d else 1)⁻¹ = if i then d else 1 := by
    intro i; cases i <;> simp [inv_eq_of_mul_eq_one_right hd]
  have inve : ∀ i : Bool, (if i then e else 1)⁻¹ = if i then e else 1 := by
    intro i; cases i <;> simp [inv_eq_of_mul_eq_one_right he]
  have invf : ∀ i : Bool, (if i then f else 1)⁻¹ = if i then f else 1 := by
    intro i; cases i <;> simp [inv_eq_of_mul_eq_one_right hf]
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with rfl | rfl | rfl
    · exact ⟨true, false, false, by simp⟩
    · exact ⟨false, true, false, by simp⟩
    · exact ⟨false, false, true, by simp⟩
  | one => exact ⟨false, false, false, by simp⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    obtain ⟨i₁, j₁, k₁, rfl⟩ := ih₁
    obtain ⟨i₂, j₂, k₂, rfl⟩ := ih₂
    refine ⟨xor i₁ i₂, xor j₁ j₂, xor k₁ k₂, ?_⟩
    rw [← sd, ← se, ← sf, LinearFieldFourKernel.mul_shuffle (cde i₂ j₁).eq (cdf i₂ k₁).eq
      (cef j₂ k₁).eq]
  | inv g _ ih =>
    obtain ⟨i, j, k, rfl⟩ := ih
    refine ⟨i, j, k, ?_⟩
    rw [← LinearFieldFourKernel.inv_mul_inv_mul_inv (cde i j) (cdf i k) (cef j k), invd, inve,
      invf]

theorem stem_quotient_core {G : Type*} [Group G] {a b c : G}
    (hgen : Subgroup.closure {a, b, c} = ⊤) (ha : a * a ∈ center G) (hb : b * b ∈ center G)
    (hc : c * c ∈ center G) (hac : ⁅a, c⁆ = 1) (hda : ⁅⁅a, b⁆, a⁆ = 1) (hdb : ⁅⁅a, b⁆, b⁆ = 1)
    (heb : ⁅⁅b, c⁆, b⁆ = 1) (hec : ⁅⁅b, c⁆, c⁆ = 1) (hde : ⁅⁅a, b⁆, ⁅b, c⁆⁆ = 1)
    (ρ : G →* U4) (hρa : ρ a = u4a) (hρb : ρ b = u4b) (hρc : ρ c = u4c) {g : G}
    (hg : g ∈ commutator G) (hρg : ρ g = 1) : g = 1 := by
  set d := ⁅a, b⁆ with hddef
  set e := ⁅b, c⁆ with hedef
  have hac' : a * c = c * a := commutatorElement_eq_one_iff_mul_comm.mp hac
  have hda' : d * a = a * d := commutatorElement_eq_one_iff_mul_comm.mp hda
  have hdb' : d * b = b * d := commutatorElement_eq_one_iff_mul_comm.mp hdb
  have heb' : e * b = b * e := commutatorElement_eq_one_iff_mul_comm.mp heb
  have hec' : e * c = c * e := commutatorElement_eq_one_iff_mul_comm.mp hec
  have hde' : d * e = e * d := commutatorElement_eq_one_iff_mul_comm.mp hde
  have hd2 : d * d = 1 := by
    have h := commutatorElement_mul_left_eq a a b
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp ha b).symm, ← hddef,
      ← hda', mul_inv_cancel_right] at h
    exact h.symm
  have he2 : e * e = 1 := by
    have h := commutatorElement_mul_right_eq b c c
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hc b), ← hedef,
      ← hec', mul_inv_cancel_right] at h
    exact h.symm
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  set f := ⁅d, c⁆ with hfdef
  have hF1 : c * d * c⁻¹ = d * f := by
    rw [hfdef, commutatorElement_def, hdi]
    calc c * d * c⁻¹ = (d * d) * c * d * c⁻¹ := by rw [hd2, one_mul]
      _ = d * (d * c * d * c⁻¹) := by group
  have hF5 : a * e * a⁻¹ = e * f := by
    have h1 : (b * a * b⁻¹) * (b * c * b⁻¹) = (b * c * b⁻¹) * (b * a * b⁻¹) := by
      calc (b * a * b⁻¹) * (b * c * b⁻¹) = b * (a * c) * b⁻¹ := by group
        _ = b * (c * a) * b⁻¹ := by rw [hac']
        _ = (b * c * b⁻¹) * (b * a * b⁻¹) := by group
    have hba : b * a * b⁻¹ = d * a := by
      rw [← hdi, hddef, commutatorElement_def]
      group
    have hbc : b * c * b⁻¹ = e * c := by
      rw [hedef, commutatorElement_def]
      group
    rw [hba, hbc] at h1
    have h2 : d * (a * e * a⁻¹) * (a * c) = e * (c * d * c⁻¹) * (a * c) := by
      calc d * (a * e * a⁻¹) * (a * c) = d * a * (e * c) := by group
        _ = e * c * (d * a) := h1
        _ = e * (c * d * c⁻¹) * (c * a) := by group
        _ = e * (c * d * c⁻¹) * (a * c) := by rw [hac']
    rw [mul_left_inj, hF1] at h2
    calc a * e * a⁻¹ = d⁻¹ * (d * (a * e * a⁻¹)) := by group
      _ = d⁻¹ * (e * (d * f)) := by rw [h2]
      _ = d⁻¹ * (d * e * f) := by rw [← mul_assoc e, ← hde', mul_assoc]
      _ = e * f := by group
  have cda : Commute d a := hda'
  have cdb : Commute d b := hdb'
  have cde : Commute d e := hde'
  have cec : Commute e c := hec'
  have hfe : e * f = f * e := by
    have h : Commute e (d * c * d⁻¹ * c⁻¹) :=
      ((cde.symm.mul_right cec).mul_right cde.symm.inv_right).mul_right cec.inv_right
    rw [hfdef, commutatorElement_def]
    exact h
  have hfd : d * f = f * d := by
    have hf : f = e⁻¹ * (a * e * a⁻¹) := by rw [hF5]; group
    have h : Commute d (e⁻¹ * (a * e * a⁻¹)) :=
      cde.inv_right.mul_right ((cda.mul_right cde).mul_right cda.inv_right)
    rw [hf]
    exact h
  have hf2 : f * f = 1 := by
    have h1 : (d * f) * (d * f) = c * (d * d) * c⁻¹ := by rw [← hF1]; group
    rw [hd2, mul_one, mul_inv_cancel] at h1
    calc f * f = d * d * (f * f) := by rw [hd2, one_mul]
      _ = (d * f) * (d * f) := by rw [mul_assoc d f, ← mul_assoc f d, ← hfd]; group
      _ = 1 := h1
  have hconj_sq : ∀ s : G, s * s ∈ center G → ∀ r : G, s⁻¹ * r * s = s * r * s⁻¹ := by
    intro s hs r
    have h := mem_center_iff.mp (inv_mem hs) r
    calc s⁻¹ * r * s = s * ((s * s)⁻¹ * r) * s := by group
      _ = s * (r * (s * s)⁻¹) * s := by rw [h]
      _ = s * r * s⁻¹ := by group
  have hfa : a * f * a⁻¹ = f := by
    have h1 : a * (a * e * a⁻¹) * a⁻¹ = (e * f) * (a * f * a⁻¹) := by
      calc a * (a * e * a⁻¹) * a⁻¹ = a * (e * f) * a⁻¹ := by rw [hF5]
        _ = (a * e * a⁻¹) * (a * f * a⁻¹) := by group
        _ = (e * f) * (a * f * a⁻¹) := by rw [hF5]
    have h2 : a * (a * e * a⁻¹) * a⁻¹ = e := by
      rw [show a * (a * e * a⁻¹) * a⁻¹ = (a * a) * e * (a * a)⁻¹ by group,
        ← mem_center_iff.mp ha e, mul_inv_cancel_right]
    rw [h2] at h1
    have h3 : 1 = f * (a * f * a⁻¹) := by
      calc (1 : G) = e⁻¹ * e := by group
        _ = e⁻¹ * (e * f * (a * f * a⁻¹)) := by rw [← h1]
        _ = f * (a * f * a⁻¹) := by group
    calc a * f * a⁻¹ = f * f * (a * f * a⁻¹) := by rw [hf2, one_mul]
      _ = f := by rw [mul_assoc, ← h3, mul_one]
  have hfc : c * f * c⁻¹ = f := by
    have h1 : c * (c * d * c⁻¹) * c⁻¹ = (d * f) * (c * f * c⁻¹) := by
      calc c * (c * d * c⁻¹) * c⁻¹ = c * (d * f) * c⁻¹ := by rw [hF1]
        _ = (c * d * c⁻¹) * (c * f * c⁻¹) := by group
        _ = (d * f) * (c * f * c⁻¹) := by rw [hF1]
    have h2 : c * (c * d * c⁻¹) * c⁻¹ = d := by
      rw [show c * (c * d * c⁻¹) * c⁻¹ = (c * c) * d * (c * c)⁻¹ by group,
        ← mem_center_iff.mp hc d, mul_inv_cancel_right]
    rw [h2] at h1
    have h3 : 1 = f * (c * f * c⁻¹) := by
      calc (1 : G) = d⁻¹ * d := by group
        _ = d⁻¹ * (d * f * (c * f * c⁻¹)) := by rw [← h1]
        _ = f * (c * f * c⁻¹) := by group
    calc c * f * c⁻¹ = f * f * (c * f * c⁻¹) := by rw [hf2, one_mul]
      _ = f := by rw [mul_assoc, ← h3, mul_one]
  have hfb : b * f * b⁻¹ = f := by
    have hbd : b * d * b⁻¹ = d := by rw [← hdb', mul_inv_cancel_right]
    have hbc : b * c * b⁻¹ = e * c := by
      rw [hedef, commutatorElement_def]
      group
    rw [hfdef, LinearFieldFourKernel.conj_commutatorElement, hbd, hbc,
      commutatorElement_mul_right_eq, commutatorElement_eq_one_iff_mul_comm.mpr hde', one_mul,
      ← hfdef, hfe, mul_inv_cancel_right]
  set N := Subgroup.closure {d, e, f} with hNdef
  have hdN : d ∈ N := subset_closure (Set.mem_insert _ _)
  have heN : e ∈ N := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hfN : f ∈ N := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hconjN : ∀ s : G, (s * d * s⁻¹ ∈ N) → (s * e * s⁻¹ ∈ N) → (s * f * s⁻¹ ∈ N) →
      ∀ r ∈ N, s * r * s⁻¹ ∈ N := by
    intro s h1 h2 h3 r hr
    induction hr using Subgroup.closure_induction with
    | mem t ht =>
      rcases ht with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
    | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
    | mul r₁ r₂ _ _ ih₁ ih₂ =>
      rw [show s * (r₁ * r₂) * s⁻¹ = (s * r₁ * s⁻¹) * (s * r₂ * s⁻¹) by group]
      exact mul_mem ih₁ ih₂
    | inv r _ ih =>
      rw [show s * r⁻¹ * s⁻¹ = (s * r * s⁻¹)⁻¹ by group]
      exact inv_mem ih
  have hgenN : ∀ s ∈ ({a, b, c} : Set G), ∀ r ∈ N, s * r * s⁻¹ ∈ N ∧ s⁻¹ * r * s ∈ N := by
    rintro s hs r hr
    have hsq : s * s ∈ center G := by
      rcases hs with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    have key : ∀ r ∈ N, s * r * s⁻¹ ∈ N := by
      rcases hs with rfl | rfl | rfl
      · refine hconjN _ ?_ ?_ ?_
        · rw [← hda', mul_inv_cancel_right]; exact hdN
        · rw [hF5]; exact mul_mem heN hfN
        · rw [hfa]; exact hfN
      · refine hconjN _ ?_ ?_ ?_
        · rw [← hdb', mul_inv_cancel_right]; exact hdN
        · rw [← heb', mul_inv_cancel_right]; exact heN
        · rw [hfb]; exact hfN
      · refine hconjN _ ?_ ?_ ?_
        · rw [hF1]; exact mul_mem hdN hfN
        · rw [← hec', mul_inv_cancel_right]; exact heN
        · rw [hfc]; exact hfN
    exact ⟨key r hr, by rw [hconj_sq s hsq]; exact key r hr⟩
  have hnorm : ∀ g ∈ Subgroup.closure {a, b, c}, ∀ r ∈ N, g * r * g⁻¹ ∈ N := by
    intro g hg
    have key : ∀ r ∈ N, g * r * g⁻¹ ∈ N ∧ g⁻¹ * r * g ∈ N := by
      induction hg using Subgroup.closure_induction with
      | mem s hs => exact fun r hr => hgenN s hs r hr
      | one => intro r hr; simp only [mul_one, inv_one, one_mul]; exact ⟨hr, hr⟩
      | mul g₁ g₂ _ _ ih₁ ih₂ =>
        intro r hr
        refine ⟨?_, ?_⟩
        · rw [show g₁ * g₂ * r * (g₁ * g₂)⁻¹ = g₁ * (g₂ * r * g₂⁻¹) * g₁⁻¹ by group]
          exact (ih₁ _ (ih₂ r hr).1).1
        · rw [show (g₁ * g₂)⁻¹ * r * (g₁ * g₂) = g₂⁻¹ * (g₁⁻¹ * r * g₁) * g₂ by group]
          exact (ih₂ _ (ih₁ r hr).2).2
      | inv g _ ih =>
        intro r hr
        exact ⟨by rw [inv_inv]; exact (ih r hr).2, by rw [inv_inv]; exact (ih r hr).1⟩
    exact fun r hr => (key r hr).1
  have hX : ∀ s ∈ ({a, b, c} : Set G), ∀ s' ∈ ({a, b, c} : Set G), ⁅s, s'⁆ ∈ N := by
    rintro s hs s' hs'
    rcases hs with rfl | rfl | rfl <;> rcases hs' with rfl | rfl | rfl
    · rw [commutatorElement_self]; exact one_mem _
    · exact hdN
    · rw [hac]; exact one_mem _
    · rw [← commutatorElement_inv]; exact inv_mem hdN
    · rw [commutatorElement_self]; exact one_mem _
    · exact heN
    · rw [← commutatorElement_inv, hac, inv_one]; exact one_mem _
    · rw [← commutatorElement_inv]; exact inv_mem heN
    · rw [commutatorElement_self]; exact one_mem _
  have hgN : g ∈ N := by
    have hle : commutator G ≤ N := by
      rw [_root_.commutator_def, commutator_le]
      intro g₁ _ g₂ _
      exact commutatorElement_mem_of_mem_closure hnorm hX (hgen ▸ mem_top g₁)
        (hgen ▸ mem_top g₂)
    exact hle hg
  obtain ⟨i, j, k, rfl⟩ := mem_closure_three_involutions hd2 he2 hf2 hde' hfd hfe hgN
  have hρd : ρ d = u4d := by rw [hddef, map_commutatorElement, hρa, hρb, u4_commutator_ab]
  have hρe : ρ e = u4e := by rw [hedef, map_commutatorElement, hρb, hρc, u4_commutator_bc]
  have hρf : ρ f = u4f := by rw [hfdef, map_commutatorElement, hρd, hρc, u4_commutator_dc]
  have hite : ∀ (x : G) (y : U4) (hxy : ρ x = y) (i : Bool),
      ρ (if i then x else 1) = if i then y else 1 := by
    intro x y hxy i; cases i <;> simp [hxy]
  rw [map_mul, map_mul, hite d u4d hρd, hite e u4e hρe, hite f u4f hρf] at hρg
  obtain ⟨rfl, rfl, rfl⟩ := u4_def_eq_one i j k hρg
  simp

theorem zmodHom_mem {T : Type*} [Group T] {n : ℕ} [NeZero n] {c : T} (hc : c ^ n = 1)
    {H : Subgroup T} (hcH : c ∈ H) (m : Multiplicative (ZMod n)) : zmodHom n c hc m ∈ H := by
  have hm : m = Multiplicative.ofAdd 1 ^ (Multiplicative.toAdd m).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [hm, map_pow, zmodHom_ofAdd_one]
  exact pow_mem hcH _

theorem closure_four_central_involutions {T : Type*} [Group T] [Finite T] {q u v h : T}
    (hq : q ∈ center T) (hu : u ∈ center T) (hv : v ∈ center T) (hh : h ∈ center T)
    (hq2 : q ^ 2 = 1) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) (hh2 : h ^ 2 = 1) :
    IsElementaryAbelian 2 (Subgroup.closure {q, u, v, h}) ∧
      Nat.card (Subgroup.closure {q, u, v, h}) ≤ 16 := by
  set G₀ := Subgroup.closure {q, u, v, h} with hG₀
  have hG₀c : G₀ ≤ center T := by
    rw [hG₀, closure_le]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hq
    · exact hu
    · exact hv
    · exact hh
  have hcomm : ∀ (x y : T), x ∈ center T → Commute x y := fun x y hx =>
    (mem_center_iff.mp hx y).symm
  let M := Multiplicative (ZMod 2)
  let Φ₁ := MonoidHom.noncommCoprod (zmodHom 2 q hq2) (zmodHom 2 u hu2)
    (fun m n => hcomm _ _ (zmodHom_mem hq2 hq m))
  let Φ₂ := MonoidHom.noncommCoprod (zmodHom 2 v hv2) (zmodHom 2 h hh2)
    (fun m n => hcomm _ _ (zmodHom_mem hv2 hv m))
  have hΦ₁c : ∀ w, Φ₁ w ∈ center T := fun w =>
    mul_mem (zmodHom_mem hq2 hq w.1) (zmodHom_mem hu2 hu w.2)
  let Φ := MonoidHom.noncommCoprod Φ₁ Φ₂ (fun w w' => hcomm _ _ (hΦ₁c w))
  have hrange : Φ.range = G₀ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨⟨⟨m₁, m₂⟩, ⟨m₃, m₄⟩⟩, rfl⟩
      have hq' : q ∈ G₀ := subset_closure (Set.mem_insert _ _)
      have hu' : u ∈ G₀ := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      have hv' : v ∈ G₀ := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert _ _)))
      have hh' : h ∈ G₀ := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ rfl)))
      exact mul_mem (mul_mem (zmodHom_mem hq2 hq' m₁) (zmodHom_mem hu2 hu' m₂))
        (mul_mem (zmodHom_mem hv2 hv' m₃) (zmodHom_mem hh2 hh' m₄))
    · rw [hG₀, closure_le]
      rintro _ (rfl | rfl | rfl | rfl)
      · exact ⟨((Multiplicative.ofAdd 1, 1), (1, 1)), by
          simp [Φ, Φ₁, Φ₂, MonoidHom.noncommCoprod_apply, zmodHom_ofAdd_one]⟩
      · exact ⟨((1, Multiplicative.ofAdd 1), (1, 1)), by
          simp [Φ, Φ₁, Φ₂, MonoidHom.noncommCoprod_apply, zmodHom_ofAdd_one]⟩
      · exact ⟨((1, 1), (Multiplicative.ofAdd 1, 1)), by
          simp [Φ, Φ₁, Φ₂, MonoidHom.noncommCoprod_apply, zmodHom_ofAdd_one]⟩
      · exact ⟨((1, 1), (1, Multiplicative.ofAdd 1)), by
          simp [Φ, Φ₁, Φ₂, MonoidHom.noncommCoprod_apply, zmodHom_ofAdd_one]⟩
  have hM2 : Nat.card M = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hsq : ∀ w : (M × M) × (M × M), w ^ 2 = 1 := by
    intro w
    have h1 : ∀ m : M, m ^ 2 = 1 := fun m => by
      have := pow_card_eq_one' (G := M) (x := m)
      rwa [hM2] at this
    exact Prod.ext (Prod.ext (h1 _) (h1 _)) (Prod.ext (h1 _) (h1 _))
  have hcommG₀ : IsMulCommutative G₀ := isMulCommutative_iff.mpr fun a b =>
    Subtype.ext (hcomm (a : T) (b : T) (hG₀c a.2))
  have hpow : ∀ g : G₀, g ^ 2 = 1 := fun g => by
    obtain ⟨w, hw⟩ := (show (g : T) ∈ Φ.range by rw [hrange]; exact g.2)
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hw, ← map_pow, hsq, map_one]
    rfl
  refine ⟨{ toIsMulCommutative := hcommG₀
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }, ?_⟩
  · rw [← hrange]
    calc Nat.card Φ.range ≤ Nat.card ((M × M) × (M × M)) :=
          Nat.card_le_card_of_surjective _ Φ.rangeRestrict_surjective
      _ = 16 := by rw [Nat.card_prod, Nat.card_prod, hM2]

theorem stem_kernel_bound {T : Type*} [Group T] [Finite T] (ρ : T →* U4)
    (hρ : Function.Surjective ρ) (hC : ρ.ker ≤ center T ⊓ commutator T) :
    IsElementaryAbelian 2 ρ.ker ∧ Nat.card ρ.ker ≤ 16 := by
  have hCc : ∀ z, ρ z = 1 → z ∈ center T := fun z hz => (hC hz).1
  have hCd : ∀ z, ρ z = 1 → z ∈ commutator T := fun z hz => (hC hz).2
  obtain ⟨x, hx⟩ := hρ u4a
  obtain ⟨y, hy⟩ := hρ u4b
  obtain ⟨z, hz⟩ := hρ u4c
  set T₀ := Subgroup.closure {x, y, z} with hT₀def
  have hT₀ : T₀.map ρ = ⊤ := by
    rw [hT₀def, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton, hx, hy, hz, closure_u4abc]
  have hdecomp : ∀ t : T, ∃ t₀ ∈ T₀, ρ (t₀⁻¹ * t) = 1 := fun t => by
    have : ρ t ∈ T₀.map ρ := hT₀ ▸ mem_top _
    obtain ⟨t₀, ht₀, h⟩ := this
    exact ⟨t₀, ht₀, by rw [map_mul, map_inv, h, inv_mul_cancel]⟩
  have hcommT₀ : commutator T ≤ T₀ := by
    rw [_root_.commutator_def, commutator_le]
    intro g _ h _
    obtain ⟨g₀, hg₀, hg⟩ := hdecomp g
    obtain ⟨h₀, hh₀, hh⟩ := hdecomp h
    have e1 : ⁅g, h⁆ = ⁅g₀, h₀⁆ := by
      calc ⁅g, h⁆ = ⁅g₀ * (g₀⁻¹ * g), h₀ * (h₀⁻¹ * h)⁆ := by
            rw [mul_inv_cancel_left, mul_inv_cancel_left]
        _ = ⁅g₀, h₀⁆ := by
            rw [CentralExtensions.commutator_mul_center_left _ _ _ (hCc _ hg),
              CentralExtensions.commutator_mul_center_right _ _ _ (hCc _ hh)]
    rw [e1, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₀ hh₀) (inv_mem hg₀)) (inv_mem hh₀)
  have hgen : T₀ = ⊤ := by
    rw [eq_top_iff]
    intro t _
    obtain ⟨t₀, ht₀, h⟩ := hdecomp t
    rw [show t = t₀ * (t₀⁻¹ * t) by group]
    exact mul_mem ht₀ (hcommT₀ (hCd _ h))
  set D := ⁅x, y⁆ with hDdef
  set E := ⁅y, z⁆ with hEdef
  have hxx : x * x ∈ center T := hCc _ (by rw [map_mul, hx, u4a_mul_self])
  have hyy : y * y ∈ center T := hCc _ (by rw [map_mul, hy, u4b_mul_self])
  have hzz : z * z ∈ center T := hCc _ (by rw [map_mul, hz, u4c_mul_self])
  have hρq : ρ ⁅x, z⁆ = 1 := by rw [map_commutatorElement, hx, hz, u4_comm_ac]
  have hρu : ρ ⁅D, x⁆ = 1 := by
    rw [map_commutatorElement, hDdef, map_commutatorElement, hx, hy, u4_comm_da]
  have hρu' : ρ ⁅D, y⁆ = 1 := by
    rw [map_commutatorElement, hDdef, map_commutatorElement, hx, hy, u4_comm_db]
  have hρv : ρ ⁅E, y⁆ = 1 := by
    rw [map_commutatorElement, hEdef, map_commutatorElement, hy, hz, u4_comm_eb]
  have hρv' : ρ ⁅E, z⁆ = 1 := by
    rw [map_commutatorElement, hEdef, map_commutatorElement, hy, hz, u4_comm_ec]
  have hρh : ρ ⁅D, E⁆ = 1 := by
    rw [map_commutatorElement, hDdef, hEdef, map_commutatorElement, map_commutatorElement, hx,
      hy, hz, u4_comm_de]
  have hsqD := commutatorElement_commutatorElement_eq_sq (mem_center_iff.mp hxx y).symm
    (mem_center_iff.mp hyy x).symm
  have hsqE := commutatorElement_commutatorElement_eq_sq (mem_center_iff.mp hyy z).symm
    (mem_center_iff.mp hzz y).symm
  have hu'u : ⁅D, y⁆ = ⁅D, x⁆ := hsqD.2.trans hsqD.1.symm
  have hv'v : ⁅E, z⁆ = ⁅E, y⁆ := hsqE.2.trans hsqE.1.symm
  have hqc := hCc _ hρq
  have huc := hCc _ hρu
  have hvc := hCc _ hρv
  have hhc := hCc _ hρh
  have hq2 : ⁅x, z⁆ ^ 2 = 1 := by
    have h := commutatorElement_mul_left_eq x x z
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hxx z).symm,
      LinearFieldFourKernel.conj_of_mem_center x hqc] at h
    rw [sq]
    exact h.symm
  have hu2 : ⁅D, x⁆ ^ 2 = 1 := by
    have h := commutatorElement_mul_right_eq D x x
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hxx D),
      LinearFieldFourKernel.conj_of_mem_center x huc] at h
    rw [sq]
    exact h.symm
  have hv2 : ⁅E, y⁆ ^ 2 = 1 := by
    have h := commutatorElement_mul_right_eq E z z
    have hv'c : ⁅E, z⁆ ∈ center T := hv'v ▸ hvc
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hzz E),
      LinearFieldFourKernel.conj_of_mem_center z hv'c, hv'v] at h
    rw [sq]
    exact h.symm
  have hh2 : ⁅D, E⁆ ^ 2 = 1 := by
    have h := commutatorElement_mul_left_eq D D E
    have hDD : D * D ∈ center T := by rw [← sq, ← hsqD.1]; exact huc
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hDD E).symm,
      LinearFieldFourKernel.conj_of_mem_center D hhc] at h
    rw [sq]
    exact h.symm
  set G₀ := Subgroup.closure {⁅x, z⁆, ⁅D, x⁆, ⁅E, y⁆, ⁅D, E⁆} with hG₀def
  obtain ⟨hG₀ea, hG₀card⟩ := closure_four_central_involutions hqc huc hvc hhc hq2 hu2 hv2 hh2
  have hG₀c : G₀ ≤ center T := by
    rw [hG₀def, closure_le]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hqc
    · exact huc
    · exact hvc
    · exact hhc
  have hG₀ρ : G₀ ≤ ρ.ker := by
    rw [hG₀def, closure_le]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hρq
    · exact hρu
    · exact hρv
    · exact hρh
  have : G₀.Normal := normal_of_le_center hG₀c
  let π := QuotientGroup.mk' G₀
  let ρ' : T ⧸ G₀ →* U4 := QuotientGroup.lift G₀ ρ hG₀ρ
  have hρ'π : ∀ t, ρ' (π t) = ρ t := fun t => rfl
  have hπ1 : ∀ t ∈ G₀, π t = 1 := fun t ht => (QuotientGroup.eq_one_iff t).mpr ht
  have hmemG : ∀ {t : T}, t ∈ ({⁅x, z⁆, ⁅D, x⁆, ⁅E, y⁆, ⁅D, E⁆} : Set T) → t ∈ G₀ :=
    fun ht => subset_closure ht
  have hcen : ∀ t ∈ center T, π t ∈ center (T ⧸ G₀) := fun t ht => mem_center_iff.mpr fun g => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective G₀ g
    rw [← map_mul, ← map_mul, mem_center_iff.mp ht g]
  have hgen' : Subgroup.closure {π x, π y, π z} = ⊤ := by
    have h := MonoidHom.map_closure π {x, y, z}
    rw [← hT₀def, hgen, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective G₀),
      Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton] at h
    exact h.symm
  have hcore : ∀ {g : T ⧸ G₀}, g ∈ commutator (T ⧸ G₀) → ρ' g = 1 → g = 1 := fun hg hρg =>
    stem_quotient_core hgen' (by rw [← map_mul]; exact hcen _ hxx)
    (by rw [← map_mul]; exact hcen _ hyy) (by rw [← map_mul]; exact hcen _ hzz)
    (by rw [← map_commutatorElement]; exact hπ1 _ (hmemG (Set.mem_insert _ _)))
    (by rw [← map_commutatorElement, ← map_commutatorElement]
        exact hπ1 _ (hmemG (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
    (by rw [← map_commutatorElement, ← map_commutatorElement, hu'u]
        exact hπ1 _ (hmemG (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
    (by rw [← map_commutatorElement, ← map_commutatorElement]
        exact hπ1 _ (hmemG (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_insert _ _)))))
    (by rw [← map_commutatorElement, ← map_commutatorElement, hv'v]
        exact hπ1 _ (hmemG (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_insert _ _)))))
    (by rw [← map_commutatorElement, ← map_commutatorElement, ← map_commutatorElement]
        exact hπ1 _ (hmemG (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ rfl)))))
    ρ' (by rw [hρ'π, hx]) (by rw [hρ'π, hy]) (by rw [hρ'π, hz]) hg hρg
  have hCG : ρ.ker ≤ G₀ := by
    intro c hc
    have h1 : π c ∈ commutator (T ⧸ G₀) := by
      have hmap : (commutator T).map π ≤ commutator (T ⧸ G₀) := by
        rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
        exact Subgroup.commutator_mono le_top le_top
      exact hmap (mem_map_of_mem π (hCd c hc))
    exact (QuotientGroup.eq_one_iff c).mp (hcore h1 ((hρ'π c).trans hc))
  have hCeq : ρ.ker = G₀ := le_antisymm hCG hG₀ρ
  rw [hCeq]
  exact ⟨hG₀ea, hG₀card⟩

theorem perfect_cover_kernel_bound_of_sylow {P Q : Type*} [Group P] [Group Q] [Finite P]
    [Finite Q] [Group.IsPerfect P] (η : P →* Q) (hη : Function.Surjective η) (hK : η.ker ≤ center P)
    (h2 : IsPGroup 2 η.ker) (S : Sylow 2 Q) (eS : (S : Subgroup Q) ≃* U4) :
    IsElementaryAbelian 2 η.ker ∧ Nat.card η.ker ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Subgroup P := (S : Subgroup Q).comap η with hTdef
  have hTp : IsPGroup 2 T := S.isPGroup'.comap_of_ker_isPGroup η h2
  have hTi : ¬ 2 ∣ T.index := by
    rw [hTdef, Subgroup.index_comap_of_surjective _ hη]
    exact S.not_dvd_index
  let TS : Sylow 2 P := hTp.toSylow hTi
  have hKT : η.ker ≤ ⁅T, T⁆ := by
    have h := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived TS η.ker hK h2
    rwa [map_subtype_commutator] at h
  let ρ : T →* U4 := eS.toMonoidHom.comp (η.subgroupComap (S : Subgroup Q))
  have hρ : Function.Surjective ρ :=
    eS.surjective.comp (η.subgroupComap_surjective _ hη)
  have hker : ρ.ker = η.ker.subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    change eS (η.subgroupComap (S : Subgroup Q) t) = 1 ↔ η t = 1
    rw [MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hC : ρ.ker ≤ center T ⊓ commutator T := by
    rw [hker]
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht
    refine ⟨mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp (hK ht) g), ?_⟩
    have h := hKT ht
    rw [← map_subtype_commutator] at h
    obtain ⟨t', ht', heq⟩ := h
    rwa [show t = t' from Subtype.ext heq.symm]
  obtain ⟨hea, hcard⟩ := stem_kernel_bound ρ hρ hC
  have hKle : η.ker ≤ T := fun k hk => by
    change η k ∈ (S : Subgroup Q)
    rw [MonoidHom.mem_ker.mp hk]
    exact one_mem _
  let e : ρ.ker ≃* η.ker :=
    (MulEquiv.subgroupCongr hker).trans (Subgroup.subgroupOfEquivOfLe hKle)
  exact ⟨isElementaryAbelian_of_injective (f := e.symm.toMonoidHom) e.symm.injective,
    (Nat.card_congr e.toEquiv).symm.le.trans hcard⟩

@[expose] def unitriangularRingEquiv {R R' : Type*} [Field R] [Field R'] (σ : R ≃+* R') (n : ℕ) :
    unitriangular n R ≃* unitriangular n R' where
  toFun u := ⟨SpecialLinearGroup.map σ.toRingHom u, by
    obtain ⟨hl, hd⟩ := mem_unitriangular.mp u.2
    refine mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
    · change σ (((u : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) i j) = 0
      rw [hl i j hij, map_zero]
    · change σ (((u : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) i i) = 1
      rw [hd i, map_one]⟩
  invFun u := ⟨SpecialLinearGroup.map σ.symm.toRingHom u, by
    obtain ⟨hl, hd⟩ := mem_unitriangular.mp u.2
    refine mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
    · change σ.symm (((u : SpecialLinearGroup (Fin n) R') : Matrix (Fin n) (Fin n) R') i j) = 0
      rw [hl i j hij, map_zero]
    · change σ.symm (((u : SpecialLinearGroup (Fin n) R') : Matrix (Fin n) (Fin n) R') i i) = 1
      rw [hd i, map_one]⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    change σ.symm (σ _) = _
    rw [RingEquiv.symm_apply_apply]
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    change σ (σ.symm _) = _
    rw [RingEquiv.apply_symm_apply]
  map_mul' u v := by
    apply Subtype.ext
    exact map_mul (SpecialLinearGroup.map σ.toRingHom) (u : SpecialLinearGroup (Fin n) R) v

theorem exists_sylow_mulEquiv_U4_of_lieModel {Q : Type} [Group Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSL 4 2 1) :
    ∃ S : Sylow 2 Q, Nonempty ((S : Subgroup Q) ≃* U4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hQ
  have := finite_field_prime_power_characteristic (K := F) Nat.prime_two le_rfl hcard
  have := Fintype.ofFinite F
  have hF : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hcard, pow_one]
  let σ : ZMod 2 ≃+* F := ZMod.ringEquiv F hF
  obtain ⟨SU, hSU⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 4) (by norm_num)
  let f : projectiveSL 4 F →* Q := e.symm.toMonoidHom
  have hf : Function.Surjective f := e.symm.surjective
  let S : Sylow 2 Q := Sylow.mapSurjective hf SU
  refine ⟨S, ⟨?_⟩⟩
  have hS : (S : Subgroup Q) = (projUnitriangular 4 F).map f := by
    rw [Sylow.coe_mapSurjective, hSU]
  exact (((MulEquiv.subgroupCongr hS).trans
    ((projUnitriangular 4 F).equivMapOfInjective f e.symm.injective).symm).trans
      (unitriangularEquivProj (K := F) 4).symm).trans (unitriangularRingEquiv σ.symm 4)

theorem linear_four_cover_kernel_bound {P : Type*} {Q : Type} [Group P] [Group Q] [Finite P]
    [Finite Q] [Group.IsPerfect P] (η : P →* Q) (hη : Function.Surjective η)
    (hK : η.ker ≤ center P) (h2 : IsPGroup 2 η.ker) (hQ : CFSG.Blueprint.LieModel Q .PSL 4 2 1) :
    IsElementaryAbelian 2 η.ker ∧ Nat.card η.ker ≤ 16 := by
  obtain ⟨S, ⟨eS⟩⟩ := exists_sylow_mulEquiv_U4_of_lieModel hQ
  exact perfect_cover_kernel_bound_of_sylow η hη hK h2 S eS

theorem binary_unitriangular_four_stem_kernel_and_linear_four_cover_bound :
    (∀ {T : Type*} [Group T] [Finite T] (ρ : T →* U4), Function.Surjective ρ →
      ρ.ker ≤ center T ⊓ commutator T → IsElementaryAbelian 2 ρ.ker ∧ Nat.card ρ.ker ≤ 16) ∧
    (∀ {P Q : Type*} [Group P] [Group Q] [Finite P] [Finite Q] [Group.IsPerfect P]
      (η : P →* Q), Function.Surjective η → η.ker ≤ center P → IsPGroup 2 η.ker →
      (∃ S : Sylow 2 Q, Nonempty ((S : Subgroup Q) ≃* U4)) →
      IsElementaryAbelian 2 η.ker ∧ Nat.card η.ker ≤ 16) ∧
    (∀ {P : Type*} {Q : Type} [Group P] [Group Q] [Finite P] [Finite Q] [Group.IsPerfect P]
      (η : P →* Q), Function.Surjective η → η.ker ≤ center P → IsPGroup 2 η.ker →
      CFSG.Blueprint.LieModel Q .PSL 4 2 1 →
      IsElementaryAbelian 2 η.ker ∧ Nat.card η.ker ≤ 16) :=
  ⟨fun ρ hρ hC => stem_kernel_bound ρ hρ hC,
    fun η hη hK h2 ⟨S, ⟨eS⟩⟩ => perfect_cover_kernel_bound_of_sylow η hη hK h2 S eS,
    fun η hη hK h2 hQ => linear_four_cover_kernel_bound η hη hK h2 hQ⟩

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
