module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Planes
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Main
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Final
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp)
open scoped IsMulCommutative

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem iSupIndep_biSup_fiber {ι κ : Type*} [Finite ι] {α : Type*}
    [CompleteLattice α] [IsModularLattice α] {f : ι → α} (h : iSupIndep f) (g : ι → κ) :
    iSupIndep (fun o : κ => ⨆ i : {i // g i = o}, f i.1) := by
  classical
  rw [iSupIndep_def]
  intro o
  have hd := h.disjoint_biSup_biSup' (f := f) (s := {i | g i = o}) (t := {i | g i ≠ o})
    (by rw [Set.disjoint_left]; intro a ha; exact fun hcon => hcon ha) (Set.toFinite _)
  have e1 : (⨆ i : {i // g i = o}, f i.1) = ⨆ i ∈ {i | g i = o}, f i :=
    iSup_subtype'' {i | g i = o} f
  have e2 : (⨆ (o' : κ) (_ : o' ≠ o), ⨆ i : {i // g i = o'}, f i.1)
      = ⨆ i ∈ {i | g i ≠ o}, f i := by
    apply le_antisymm
    · refine iSup_le fun o' => iSup_le fun ho' => iSup_le fun i => ?_
      refine le_iSup₂_of_le i.1 ?_ le_rfl
      change g i.1 ≠ o
      rw [show g i.1 = o' from i.2]
      exact ho'
    · rw [show (⨆ i ∈ {i | g i ≠ o}, f i) = ⨆ i : {i // g i ≠ o}, f i.1 from
        (iSup_subtype'' {i | g i ≠ o} f).symm]
      refine iSup_le fun i => ?_
      refine le_trans (le_iSup (fun i' : {i' // g i' = g i.1} => f i'.1) ⟨i.1, rfl⟩) ?_
      have h1 : (⨆ (_ : g i.1 ≠ o), (⨆ i' : {i' // g i' = g i.1}, f i'.1))
          = ⨆ i' : {i' // g i' = g i.1}, f i'.1 := iSup_pos i.2
      rw [← h1]
      exact le_iSup (fun o' : κ => ⨆ (_ : o' ≠ o), ⨆ i' : {i' // g i' = o'}, f i'.1) (g i.1)
  rw [e1, e2]
  exact hd

private theorem iSup_biSup_fiber_eq {ι κ : Type*} {α : Type*} [CompleteLattice α]
    (f : ι → α) (g : ι → κ) :
    (⨆ o : κ, ⨆ i : {i // g i = o}, f i.1) = ⨆ i, f i := by
  apply le_antisymm
  · refine iSup_le fun o => iSup_le fun i => ?_
    exact le_iSup f i.1
  · refine iSup_le fun i => ?_
    refine le_trans (le_iSup (fun i' : {i' // g i' = g i} => f i'.1) ⟨i, rfl⟩) ?_
    exact le_iSup (fun o : κ => ⨆ i' : {i' // g i' = o}, f i'.1) (g i)

private theorem prod_coe_mem {G : Type*} [Group G] {E : Subgroup G} [IsMulCommutative ↥E]
    {ι : Type*} (s : Finset ι) (f : ι → ↥E) (x : ι → G) (hf : ∀ q, (f q : G) = x q)
    (H : Subgroup G) (hx : ∀ q, x q ∈ H) :
    ((∏ q ∈ s, f q : ↥E) : G) ∈ H := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Subgroup.coe_mul]
      exact H.mul_mem (by rw [hf a]; exact hx a) ih

private theorem prod_coe_fixes {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} [IsMulCommutative ↥E]
    {ι : Type*} (s : Finset ι) (f : ι → ↥E) (Y : Submodule (ZMod 2) V)
    (h : ∀ q ∈ s, ∀ y ∈ Y, (f q : V ≃ₗ[ZMod 2] V) y = y) :
    ∀ y ∈ Y, ((∏ q ∈ s, f q : ↥E) : V ≃ₗ[ZMod 2] V) y = y := by
  classical
  induction s using Finset.induction_on with
  | empty => intro y _; simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Subgroup.coe_mul]
      intro y hy
      rw [LinearEquiv.mul_apply, ih (fun q hq => h q (Finset.mem_insert_of_mem hq)) y hy]
      exact h a (Finset.mem_insert_self a s) y hy

private theorem pow_apply_fixes {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (n : ℕ) {f : V ≃ₗ[ZMod 2] V} {X : Submodule (ZMod 2) V} (h : ∀ v ∈ X, f v = v) :
    ∀ v ∈ X, (f ^ n) v = v := by
  induction n with
  | zero => intro v _; simp
  | succ n ih =>
      intro v hv
      rw [pow_succ, LinearEquiv.mul_apply, h v hv]
      exact ih v hv

private theorem pow_apply_of_eq {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {f g : V ≃ₗ[ZMod 2] V} {X : Submodule (ZMod 2) V}
    (h : ∀ v ∈ X, f v = g v) (hg : ∀ v ∈ X, g v ∈ X) :
    ∀ n, ∀ v ∈ X, (f ^ n) v = (g ^ n) v := by
  intro n
  induction n with
  | zero => intro v _; simp
  | succ n ih =>
      intro v hv
      rw [pow_succ, pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h v hv]
      exact ih (g v) (hg v hv)

theorem lin_two_std_form {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ (Module.finrank (ZMod 2) V / 2) ≤ Nat.card E) :
    ∃ (x : Fin (Module.finrank (ZMod 2) V / 2) → V ≃ₗ[ZMod 2] V)
      (P : Fin (Module.finrank (ZMod 2) V / 2) → Submodule (ZMod 2) V)
      (V0 : Submodule (ZMod 2) V), LinTwoStdFrame E x P V0 := by
  classical
  haveI : IsMulCommutative ↥E := hE.1
  haveI : Fintype E := Fintype.ofFinite E
  have hcard' : 3 ^ (Module.finrank (ZMod 2) V / 2) ≤ Fintype.card E := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨k, X, ρf, hXprop, hind, hsup, hρf, hPcard, hpe⟩ := exists_struct E hE hcard'
  let D : PieceData E X ρf :=
    ⟨hE, fun i => (hXprop i).1, fun i => (hXprop i).2, hind, hsup, hρf⟩
  have hdual : DualData E X ρf := dual_of_struct D hpe
  let r := Module.finrank (ZMod 2) V / 2
  have hPcard' : Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} = r := hPcard
  let eqv : {i // Module.finrank (ZMod 2) (X i) = 2} ≃ Fin r :=
    Fintype.equivFinOfCardEq hPcard'
  let g : Fin k → Option (Fin r) := fun i =>
    if h : Module.finrank (ZMod 2) (X i) = 2 then some (eqv ⟨i, h⟩) else none
  let P : Fin r → Submodule (ZMod 2) V := fun q => X (eqv.symm q).1
  let V0 : Submodule (ZMod 2) V := ⨆ i : {i // g i = none}, X i.1
  have hg_symm : ∀ q : Fin r, g (eqv.symm q).1 = some q := by
    intro q
    have h2 : Module.finrank (ZMod 2) (X (eqv.symm q).1) = 2 := (eqv.symm q).2
    have hsome : g (eqv.symm q).1 = some (eqv ⟨(eqv.symm q).1, h2⟩) := by
      change (if h : Module.finrank (ZMod 2) (X (eqv.symm q).1) = 2 then
        some (eqv ⟨(eqv.symm q).1, h⟩) else none) = some (eqv ⟨(eqv.symm q).1, h2⟩)
      rw [dif_pos h2]
    rw [hsome]
    have hsub : (⟨(eqv.symm q).1, h2⟩ :
        {i // Module.finrank (ZMod 2) (X i) = 2}) = eqv.symm q := Subtype.ext rfl
    rw [hsub, Equiv.apply_symm_apply]
  have hP_eq' : ∀ q : Fin r, X (eqv.symm q).1 = ⨆ i : {i // g i = some q}, X i.1 := by
    intro q
    apply le_antisymm
    · exact le_iSup (fun i : {i // g i = some q} => X i.1) ⟨(eqv.symm q).1, hg_symm q⟩
    · refine iSup_le fun i => ?_
      have hi : i.1 = (eqv.symm q).1 := by
        have hgi : g i.1 = some q := i.2
        by_cases h2 : Module.finrank (ZMod 2) (X i.1) = 2
        · have hsome : g i.1 = some (eqv ⟨i.1, h2⟩) := by
            change (if h : Module.finrank (ZMod 2) (X i.1) = 2 then
              some (eqv ⟨i.1, h⟩) else none) = some (eqv ⟨i.1, h2⟩)
            rw [dif_pos h2]
          have heq : eqv ⟨i.1, h2⟩ = q := Option.some.inj (hsome ▸ hgi)
          have hsub : (⟨i.1, h2⟩ :
              {i // Module.finrank (ZMod 2) (X i) = 2}) = eqv.symm q := by
            rw [← Equiv.symm_apply_apply eqv ⟨i.1, h2⟩, heq]
          exact congrArg Subtype.val hsub
        · have hnone : g i.1 = none := by
            change (if h : Module.finrank (ZMod 2) (X i.1) = 2 then
              some (eqv ⟨i.1, h⟩) else none) = none
            rw [dif_neg h2]
          rw [hnone] at hgi
          exact absurd hgi (by simp)
      rw [hi]
  have hdual' : ∀ q : Fin r, ∃ e : V ≃ₗ[ZMod 2] V, e ∈ E ∧
      (∀ v ∈ X (eqv.symm q).1, e v = ρf (eqv.symm q).1 v) ∧
      (∀ l, l ≠ (eqv.symm q).1 → ∀ v ∈ X l, e v = v) :=
    fun q => hdual (eqv.symm q).1 (eqv.symm q).2
  choose x hx using hdual'
  have hxmem : ∀ q, x q ∈ E := fun q => (hx q).1
  have hxgen : ∀ q, ∀ v ∈ X (eqv.symm q).1, x q v = ρf (eqv.symm q).1 v :=
    fun q => (hx q).2.1
  have hxtriv : ∀ q, ∀ l, l ≠ (eqv.symm q).1 → ∀ v ∈ X l, x q v = v :=
    fun q => (hx q).2.2
  have hYeq : (fun o : Option (Fin r) => o.elim V0 P)
      = fun o : Option (Fin r) => ⨆ i : {i // g i = o}, X i.1 := by
    funext o
    cases o with
    | none => rfl
    | some q => exact hP_eq' q
  have hInd : iSupIndep (fun o : Option (Fin r) => o.elim V0 P) := by
    rw [hYeq]
    exact iSupIndep_biSup_fiber D.ind g
  have hSup : iSup (fun o : Option (Fin r) => o.elim V0 P) = ⊤ := by
    rw [hYeq]
    rw [iSup_biSup_fiber_eq X g, D.sup]
  have hInt : DirectSum.IsInternal (fun o : Option (Fin r) => o.elim V0 P) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
      (fun o : Option (Fin r) => o.elim V0 P)).2 ⟨hInd, hSup⟩
  refine ⟨x, P, V0, ?_⟩
  refine ⟨?_, hInt, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply le_antisymm
    ·
      intro gE hgE
      let kf : Fin r → Fin 3 := fun q => expo ρf X (eqv.symm q).1 gE
      let xe : Fin r → ↥E := fun q => ⟨x q, hxmem q⟩
      let QE : ↥E := ∏ q, (xe q) ^ (kf q : ℕ)
      have hPmem : (QE : V ≃ₗ[ZMod 2] V) ∈ ⨆ q, Subgroup.zpowers (x q) := by
        refine prod_coe_mem Finset.univ (fun q => (xe q) ^ (kf q : ℕ))
          (fun q => x q ^ (kf q : ℕ)) ?_ (⨆ q, Subgroup.zpowers (x q)) ?_
        · intro q
          rw [Subgroup.coe_pow]
        · intro q
          exact Subgroup.pow_mem _ (Subgroup.mem_iSup_of_mem q (Subgroup.mem_zpowers (x q))) _
      have hgP : gE = (QE : V ≃ₗ[ZMod 2] V) := by
        apply LinearEquiv.ext
        intro v
        have hv : v ∈ ⨆ i, X i := by rw [D.sup]; trivial
        refine Submodule.iSup_induction X
          (motive := fun v => gE v = (QE : V ≃ₗ[ZMod 2] V) v) hv ?_ ?_ ?_
        · intro i w hw
          by_cases h2 : Module.finrank (ZMod 2) (X i) = 2
          ·
            let q0 : Fin r := eqv ⟨i, h2⟩
            have hq0val : (eqv.symm q0).1 = i := by
              change (eqv.symm (eqv ⟨i, h2⟩)).1 = i
              rw [Equiv.symm_apply_apply]
            have hk0 : kf q0 = expo ρf X i gE := by
              change expo ρf X (eqv.symm q0).1 gE = expo ρf X i gE
              rw [hq0val]
            have hxgen0 : ∀ v ∈ X i, x q0 v = ρf i v := by
              intro v hv
              have h1 : v ∈ X (eqv.symm q0).1 := by rwa [hq0val]
              have := hxgen q0 v h1
              rwa [hq0val] at this
            have hpres : ∀ v ∈ X i, ρf i v ∈ X i := D.inv i (ρf i) (D.gen_mem i)
            have hg_eq : gE w = (ρf i ^ (kf q0 : ℕ)) w := by
              have := expo_spec (pow_on_plane D h2 gE hgE) w hw
              rwa [← hk0] at this
            have hfix_rest : ∀ y ∈ X i,
                ((∏ q ∈ Finset.univ.erase q0, (xe q) ^ (kf q : ℕ) : ↥E) :
                  V ≃ₗ[ZMod 2] V) y = y := by
              refine prod_coe_fixes (Finset.univ.erase q0)
                (fun q => (xe q) ^ (kf q : ℕ)) (X i) ?_
              intro q hq y hy
              have hqq0 : q ≠ q0 := (Finset.mem_erase.1 hq).1
              have hne : (eqv.symm q).1 ≠ i := by
                intro heq
                apply hqq0
                have hsub : (eqv.symm q :
                    {i // Module.finrank (ZMod 2) (X i) = 2}) = eqv.symm q0 := by
                  apply Subtype.ext
                  rw [heq, hq0val]
                have := congrArg eqv hsub
                rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
              rw [Subgroup.coe_pow]
              exact pow_apply_fixes (kf q : ℕ) (hxtriv q i (Ne.symm hne)) y hy
            have hQE_eq : (QE : V ≃ₗ[ZMod 2] V) w = (ρf i ^ (kf q0 : ℕ)) w := by
              change ((∏ q, (xe q) ^ (kf q : ℕ) : ↥E) : V ≃ₗ[ZMod 2] V) w
                = (ρf i ^ (kf q0 : ℕ)) w
              have hsplit : (∏ q, (xe q) ^ (kf q : ℕ) : ↥E)
                  = (xe q0) ^ (kf q0 : ℕ) * ∏ q ∈ Finset.univ.erase q0,
                      (xe q) ^ (kf q : ℕ) := by
                conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ q0)]
                rw [Finset.prod_insert (Finset.notMem_erase q0 Finset.univ)]
              rw [hsplit, Subgroup.coe_mul, LinearEquiv.mul_apply, Subgroup.coe_pow]
              rw [hfix_rest w hw]
              exact pow_apply_of_eq hxgen0 hpres (kf q0 : ℕ) w hw
            rw [hg_eq, hQE_eq]
          ·
            have hg_eq : gE w = w := D.line_triv h2 gE hgE w hw
            have hQE_eq : (QE : V ≃ₗ[ZMod 2] V) w = w := by
              change ((∏ q, (xe q) ^ (kf q : ℕ) : ↥E) : V ≃ₗ[ZMod 2] V) w = w
              refine prod_coe_fixes Finset.univ (fun q => (xe q) ^ (kf q : ℕ)) (X i) ?_ w hw
              intro q _ y hy
              have hne : (eqv.symm q).1 ≠ i := by
                intro heq
                exact h2 (heq ▸ (eqv.symm q).2)
              rw [Subgroup.coe_pow]
              exact pow_apply_fixes (kf q : ℕ) (hxtriv q i (Ne.symm hne)) y hy
            rw [hg_eq, hQE_eq]
        · simp
        · intro a b ha hb; rw [map_add, map_add, ha, hb]
      rw [hgP]
      exact hPmem
    ·
      exact iSup_le fun q => Subgroup.zpowers_le.2 (hxmem q)
  ·
    intro q
    exact (eqv.symm q).2
  ·
    intro q
    exact pow3_eq_one_of_mem D.ab (hxmem q)
  ·
    intro q
    change LinearMap.range ((x q : V →ₗ[ZMod 2] V) - LinearMap.id) = P q
    exact range_sub_eq_plane D (eqv.symm q).2 (hxmem q) (hxgen q) (hxtriv q)
  ·
    intro q v hv
    have hv' : v ∈ ⨆ i : {i // g i = none}, X i.1 := hv
    refine Submodule.iSup_induction (fun i : {i // g i = none} => X i.1)
      (motive := fun v => x q v = v) hv' ?_ ?_ ?_
    · intro i w hw
      have hni : Module.finrank (ZMod 2) (X i.1) ≠ 2 := by
        intro h2
        have hsome : g i.1 = some (eqv ⟨i.1, h2⟩) := by
          change (if h : Module.finrank (ZMod 2) (X i.1) = 2 then
            some (eqv ⟨i.1, h⟩) else none) = some (eqv ⟨i.1, h2⟩)
          rw [dif_pos h2]
        have hi2 : g i.1 = none := i.2
        rw [hsome] at hi2
        nomatch hi2
      have hne : i.1 ≠ (eqv.symm q).1 := by
        intro heq
        exact hni (heq.symm ▸ (eqv.symm q).2)
      exact hxtriv q i.1 hne w hw
    · simp
    · intro a b ha hb; rw [map_add, ha, hb]
  ·
    intro q q' hqq' v hv
    have hne : (eqv.symm q).1 ≠ (eqv.symm q').1 := by
      intro heq
      apply hqq'
      have hsub : (eqv.symm q :
          {i // Module.finrank (ZMod 2) (X i) = 2}) = eqv.symm q' := Subtype.ext heq
      have := congrArg eqv hsub
      rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact hxtriv q (eqv.symm q').1 (Ne.symm hne) v hv

theorem lin_two_std_form_of_bmax (hV : 3 ≤ Module.finrank (ZMod 2) V)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hA : GLAIsBmax 3 A) :
    ∃ (x : Fin (Module.finrank (ZMod 2) V / 2) → V ≃ₗ[ZMod 2] V)
      (P : Fin (Module.finrank (ZMod 2) V / 2) → Submodule (ZMod 2) V)
      (V0 : Submodule (ZMod 2) V), LinTwoStdFrame A x P V0 :=
  lin_two_std_form (lin_two_bmax_card hV hA).1 (le_of_eq (lin_two_bmax_card hV hA).2.symm)

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
