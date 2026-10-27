module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerS3

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

namespace OddAbelianSetting

variable [CharP k 2] [Finite V] {G N A : Subgroup (V ≃ₗ[k] V)} {ι : Type*}
  {g : ι → V ≃ₗ[k] V} [Fintype ι] (h : OddAbelianSetting G N A) (F : ConjFamily G N A g)

include h F

omit [CharP k 2] [Finite V] [Fintype ι] in
theorem natA_comm (i : ι) : ∀ a ∈ natA A g i, ∀ b ∈ natA A g i, a * b = b * a := by
  intro a ha b hb
  have hel := (h.conj (G.inv_mem (F.mem i))).A_elem
  exact congrArg Subtype.val (hel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

omit [Fintype ι] in
theorem S_commutator_mem (i : ι) {x y : V ≃ₗ[k] V} (hx : x ∈ natS N A g i)
    (hy : y ∈ natS N A g i) : ⁅x, y⁆ ∈ natL N A g i :=
  commutator_mem_of_sup (h.planeData_family F i).A_norm (h.natA_comm F i) hx hy

theorem B_derived_ge : natD N A g ≤ ⁅natB G N A, natB G N A⁆ := by
  refine iSup_le fun i => ?_
  have pd := h.planeData_family F i
  have h1 : natL N A g i ≤ natB G N A :=
    (le_sup_left : natL N A g i ≤ natS N A g i).trans (h.S_le_B F i)
  have h2 : natA A g i ≤ natB G N A :=
    (le_sup_right : natA A g i ≤ natS N A g i).trans (h.S_le_B F i)
  calc natL N A g i = ⁅natL N A g i, natA A g i⁆ := pd.L_perf.symm
    _ ≤ ⁅natB G N A, natB G N A⁆ := Subgroup.commutator_mono h1 h2

theorem B_derived_le : ⁅natB G N A, natB G N A⁆ ≤ natD N A g := by
  classical
  have hDG : natD N A g ≤ G := (h.D_le_N F).trans h.N_le
  have hDnorm : ∀ x ∈ G, ∀ d ∈ natD N A g, x * d * x⁻¹ ∈ natD N A g := fun x hx d hd =>
    (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hDG).1 (h.D_normal F) hx) d).1 hd
  have hBG : ∀ x ∈ (⨆ i, natS N A g i : Subgroup (V ≃ₗ[k] V)), x ∈ G := fun x hx => by
    rw [← h.B_eq F] at hx
    exact h.natB_le hx
  have hSD : ∀ i, ∀ x ∈ natS N A g i, ∀ y ∈ natS N A g i, ⁅x, y⁆ ∈ natD N A g :=
    fun i x hx y hy => le_iSup (natL N A g) i (h.S_commutator_mem F i hx hy)
  have inner : ∀ i, ∀ x ∈ natS N A g i, ∀ y ∈ (⨆ j, natS N A g j : Subgroup (V ≃ₗ[k] V)),
      ⁅x, y⁆ ∈ natD N A g := by
    intro i x hx y hy
    refine (Subgroup.iSup_induction (natS N A g) hy
      (C := fun y => y ∈ G ∧ ⁅x, y⁆ ∈ natD N A g) ?_ ?_ ?_).2
    · intro j y' hy'
      refine ⟨hBG y' (le_iSup (natS N A g) j hy'), ?_⟩
      by_cases hji : j = i
      · subst hji
        exact hSD j x hx y' hy'
      · have e : x * y' = y' * x := (h.S_comm F (Ne.symm hji) x hx y' hy')
        have : ⁅x, y'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 e
        rw [this]
        exact Subgroup.one_mem _
    · exact ⟨G.one_mem, by simp⟩
    · rintro y y' ⟨hyG, hy1⟩ ⟨hy'G, hy2⟩
      refine ⟨G.mul_mem hyG hy'G, ?_⟩
      have e : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (natD N A g).mul_mem hy1 (hDnorm y hyG _ hy2)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [h.B_eq F] at hx hy
  refine (Subgroup.iSup_induction (natS N A g) hx
    (C := fun x => x ∈ G ∧ ∀ y ∈ (⨆ j, natS N A g j : Subgroup (V ≃ₗ[k] V)),
      ⁅x, y⁆ ∈ natD N A g) ?_ ?_ ?_).2 y hy
  · intro i x' hx'
    exact ⟨hBG x' (le_iSup (natS N A g) i hx'), fun y' hy' => inner i x' hx' y' hy'⟩
  · exact ⟨G.one_mem, fun y' _ => by simp⟩
  · rintro x x' ⟨hxG, hx1⟩ ⟨hx'G, hx2⟩
    refine ⟨G.mul_mem hxG hx'G, fun y' hy' => ?_⟩
    have e : ⁅x * x', y'⁆ = x * ⁅x', y'⁆ * x⁻¹ * ⁅x, y'⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (natD N A g).mul_mem (hDnorm x hxG _ (hx2 y' hy')) (hx1 y' hy')

theorem B_derived : ⁅natB G N A, natB G N A⁆ = natD N A g :=
  le_antisymm (h.B_derived_le F) (h.B_derived_ge F)

theorem W_le_of (i : ι) : natI N A g i ≤ natW N A g := by
  have hW : natW N A g = ⨆ i, natI N A g i := (h.famData F).W_eq
  rw [hW]
  exact le_iSup (natI N A g) i

theorem exists_D_agree {n : V ≃ₗ[k] V}
    (hn : ∀ i, ∃ l ∈ natL N A g i, ∀ w ∈ natI N A g i, n w = l w) :
    ∃ d ∈ natD N A g, ∀ i, ∀ w ∈ natI N A g i, d w = n w := by
  classical
  have fd := h.famData F
  choose l hlL hl using hn
  have key : ∀ s : Finset ι, ∃ d ∈ natD N A g,
      (∀ j ∈ s, ∀ w ∈ natI N A g j, d w = n w) ∧ (∀ j ∉ s, ∀ w ∈ natI N A g j, d w = w) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, Subgroup.one_mem _, by simp, by simp⟩
    | insert j s hj ih =>
      obtain ⟨d, hdD, hd1, hd2⟩ := ih
      obtain ⟨hWj, -⟩ := h.S_action F j
      have hlj : l j ∈ natS N A g j := (le_sup_left : natL N A g j ≤ natS N A g j) (hlL j)
      refine ⟨d * l j, (natD N A g).mul_mem hdD (le_iSup (natL N A g) j (hlL j)), ?_, ?_⟩
      · intro j' hj' w hw
        rcases Finset.mem_insert.1 hj' with hj'j | hj's
        · subst hj'j
          have hlw : l j' w ∈ natI N A g j' := hWj (l j') hlj w hw
          show d (l j' w) = n w
          rw [hd2 j' hj (l j' w) hlw, hl j' w hw]
        · have hne : j' ≠ j := fun e => hj (e ▸ hj's)
          have e1 : l j w = w := fd.L_fix_I j j' (Ne.symm hne) (l j) (hlL j) w hw
          show d (l j w) = n w
          rw [e1]
          exact hd1 j' hj's w hw
      · intro j' hj' w hw
        have hne : j' ≠ j := fun e => hj' (Finset.mem_insert.2 (Or.inl e))
        have hns : j' ∉ s := fun e => hj' (Finset.mem_insert_of_mem e)
        have e1 : l j w = w := fd.L_fix_I j j' (Ne.symm hne) (l j) (hlL j) w hw
        show d (l j w) = w
        rw [e1]
        exact hd2 j' hns w hw
  obtain ⟨d, hdD, hd1, -⟩ := key Finset.univ
  exact ⟨d, hdD, fun i w hw => hd1 i (Finset.mem_univ i) w hw⟩

theorem N_decomp {n : V ≃ₗ[k] V} (hn : n ∈ N) :
    ∃ d ∈ natD N A g, ∀ i, ∀ w ∈ natI N A g i, d w = n w := by
  classical
  have fd := h.famData F
  refine h.exists_D_agree F fun j => ?_
  have pd := h.planeData_family F j
  have hmem : n ∈ natL N A g j ⊔
      (N ⊓ Subgroup.centralizer (natA A g j : Set (V ≃ₗ[k] V))) := by
    rw [← pd.N_eq]
    exact hn
  have hnorm : N ⊓ Subgroup.centralizer (natA A g j : Set (V ≃ₗ[k] V)) ≤
      Subgroup.normalizer (natL N A g j : Set (V ≃ₗ[k] V)) := by
    intro c hc
    have hcent : c ∈ Subgroup.centralizer (natL N A g j : Set (V ≃ₗ[k] V)) :=
      Subgroup.mem_centralizer_iff.2 fun x hx => fd.N_comm x (fd.L_le j hx) c hc.1
    exact Subgroup.centralizer_le_normalizer _ hcent
  obtain ⟨l, hl, c, hc, rfl⟩ := mem_sup_mul hnorm hmem
  have hcI : ∀ w ∈ natI N A g j, c w = w := by
    have : c ∈ N ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natI N A g j) := by
      rw [← pd.cent_eq]
      exact hc
    exact fun w hw => this.2 w hw
  exact ⟨l, hl, fun w hw => by
    show l (c w) = l w
    rw [hcI w hw]⟩

theorem N_eq_sup :
    natD N A g ⊔ (N ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g)) = N := by
  refine le_antisymm (sup_le (h.D_le_N F) inf_le_left) ?_
  intro n hn
  obtain ⟨d, hdD, hd⟩ := h.N_decomp F hn
  have e : n = d * (d⁻¹ * n) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hdD) (Subgroup.mem_sup_right ⟨?_, ?_⟩)
  · exact N.mul_mem (N.inv_mem (h.D_le_N F hdD)) hn
  · intro w hw
    have hW : natW N A g = ⨆ i, natI N A g i := (h.famData F).W_eq
    rw [hW] at hw
    refine fix_iSup_of_fix (x := d⁻¹ * n) (U := natI N A g) (fun i w' hw' => ?_) w hw
    show d⁻¹ (n w') = w'
    rw [← hd i w' hw']
    exact gl_inv_apply d w'

theorem N_disjoint :
    Disjoint (natD N A g) (N ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g)) := by
  rw [Subgroup.disjoint_def]
  intro x hxD hxC
  exact (h.famData F).faithful x hxD (fun w hw => hxC.2 w hw)

theorem C_eq : N ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g) =
    N ⊓ Subgroup.centralizer (natB G N A : Set (V ≃ₗ[k] V)) := by
  have fd := h.famData F
  ext n
  constructor
  · rintro ⟨hnN, hnW⟩
    refine ⟨hnN, ?_⟩
    show n ∈ Subgroup.centralizer (natB G N A : Set (V ≃ₗ[k] V))
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [h.B_eq F] at hb
    refine Subgroup.iSup_induction (natS N A g) hb (C := fun b => b * n = n * b) ?_ ?_ ?_
    · intro i b' hb'
      have pd := h.planeData_family F i
      obtain ⟨l, hl, a, ha, rfl⟩ := mem_sup_mul pd.A_norm hb'
      have hnl : l * n = n * l := fd.N_comm l (fd.L_le i hl) n hnN
      have hna : a * n = n * a := by
        have hnI : n ∈ N ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natI N A g i) :=
          ⟨hnN, fun w hw => hnW w (h.W_le_of F i hw)⟩
        rw [← pd.cent_eq] at hnI
        exact Subgroup.mem_centralizer_iff.1 hnI.2 a ha
      calc l * a * n = l * (a * n) := mul_assoc _ _ _
        _ = l * (n * a) := by rw [hna]
        _ = (l * n) * a := (mul_assoc _ _ _).symm
        _ = (n * l) * a := by rw [hnl]
        _ = n * (l * a) := mul_assoc _ _ _
    · simp
    · intro x y hx hy
      rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  · rintro ⟨hnN, hnB⟩
    refine ⟨hnN, ?_⟩
    have hW : natW N A g = ⨆ i, natI N A g i := fd.W_eq
    intro w hw
    rw [hW] at hw
    refine fix_iSup_of_fix (x := n) (U := natI N A g) (fun i w' hw' => ?_) w hw
    have pd := h.planeData_family F i
    have hAB : natA A g i ≤ natB G N A :=
      (le_sup_right : natA A g i ≤ natS N A g i).trans (h.S_le_B F i)
    have hnA : n ∈ N ⊓ Subgroup.centralizer (natA A g i : Set (V ≃ₗ[k] V)) :=
      ⟨hnN, Subgroup.mem_centralizer_iff.2 fun a ha => (Subgroup.mem_centralizer_iff.1 hnB) a (hAB ha)⟩
    rw [pd.cent_eq] at hnA
    exact hnA.2 w' hw'

theorem naturalS3Factors : NaturalS3Factors G N A g := by
  have fd := h.famData F
  have hk : Nat.card k = 2 := (h.planeData (L := ⁅N, A⁆) rfl).choose_spec.card_k
  exact
    { card_k := hk
      card_L := fun i => (h.planeData_family F i).card_L
      card_A := fun i => (h.planeData_family F i).card_A
      finrank_I := fun i => (h.planeData_family F i).finrank_I
      L_comm := fd.L_comm
      L_indep := fd.L_indep
      D_le_N := h.D_le_N F
      D_normal := h.D_normal F
      D_elem := h.D_elem F
      card_D := h.card_D F
      I_indep := fd.I_indep
      W_eq := fd.W_eq
      V_compl := fd.compl
      S_comm := fun i j hij => h.S_comm F hij
      S_indep := h.S_indep F
      B_eq := h.B_eq F
      B_le := h.natB_le
      B_normal := h.natB_normal
      LA_le_B := LA_le_B
      S_action := h.S_action F
      S_fix_I := fun i j hij => h.S_fix_I F hij
      S_fix_C := h.S_fix_C F
      S_choice := fun x hx i hxi => h.S_choice F hx hxi
      S_perm := fun x hx i => h.S_perm F hx i
      S_trans := OddAbelianSetting.S_trans F
      B_derived := h.B_derived F
      S_le_B := h.S_le_B F
      S_normal_B := h.S_normal_B F
      N_eq := h.N_eq_sup F
      N_disjoint := h.N_disjoint F
      C_eq := h.C_eq F }

end OddAbelianSetting

end CFSG.QuasithinUnique.Setup.Layer
