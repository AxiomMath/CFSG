module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8b
public import CFSG.LargeExtraspecial.PSL10USimple
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCyclicKernel
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnAPI

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8

open CFSG.Open Module CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

section Unitary

variable {E : Type} [Field E] (hE : UnitaryFieldData 2 1 E) {W : Type} [AddCommGroup W]
  [Module E W] [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E}

theorem card_unitary_one (hsymm : Hf.IsSymm) (hsep : Hf.SeparatingLeft)
    (hn : finrank E W = 1) : Nat.card (sesqUnitaryGroup Hf) = 3 := by
  have h := (CFSG.LinearGroups.unitary_full_group_order hE hsymm hsep hn (by norm_num)).1
  norm_num [Finset.prod_Icc_succ_top] at h
  exact_mod_cast h

theorem card_unitary_two (hsymm : Hf.IsSymm) (hsep : Hf.SeparatingLeft)
    (hn : finrank E W = 2) : Nat.card (sesqUnitaryGroup Hf) = 18 := by
  have h := (CFSG.LinearGroups.unitary_full_group_order hE hsymm hsep hn (by norm_num)).1
  norm_num [Finset.prod_Icc_succ_top] at h
  exact_mod_cast h

theorem card_unitary_three (hsymm : Hf.IsSymm) (hsep : Hf.SeparatingLeft)
    (hn : finrank E W = 3) : Nat.card (sesqUnitaryGroup Hf) = 648 := by
  have h := (CFSG.LinearGroups.unitary_full_group_order hE hsymm hsep hn (by norm_num)).1
  norm_num [Finset.prod_Icc_succ_top] at h
  exact_mod_cast h

theorem card_special_unitary_four (hsymm : Hf.IsSymm) (hsep : Hf.SeparatingLeft)
    (hn : finrank E W = 4) : Nat.card (sesqSpecialUnitaryGroup Hf) = 25920 := by
  have h := (CFSG.LinearGroups.unitary_full_group_order hE hsymm hsep hn (by norm_num)).2.1
  norm_num [Finset.prod_Icc_succ_top] at h
  exact_mod_cast h

theorem pPrimeCore_of_unitary_four (hsymm : Hf.IsSymm) (hsep : Hf.SeparatingLeft)
    (hn : finrank E W = 4) {X : Type} [Group X] [Finite X]
    (ι : X →* sesqUnitaryGroup Hf) (hι : Function.Injective ι)
    (L : Subgroup X) (hLp : Group.IsPerfect ↥L) (hL : 25920 ∣ Nat.card ↥L) :
    CFSG.pPrimeCore 3 X = ⊥ := by
  obtain ⟨-, -, -, hrc, hker, -, -⟩ :=
    CFSG.LinearGroups.unitary_full_group_order hE hsymm hsep hn (by norm_num)
  have hSUcard := card_special_unitary_four hE hsymm hsep hn
  set f : X →* Eˣ := (CFSG.LinearGroups.unitaryDet Hf).comp ι with hf
  have hrange : CFSG.pPrimeCore 3 ↥f.range = ⊥ := by
    apply pPrimeCore_eq_bot_of_exponent
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨x, hx⟩ := g.2
    have hmem : g.1 ∈ (CFSG.LinearGroups.unitaryDet Hf).range := ⟨ι x, hx⟩
    have h1 := pow_card_eq_one' (G := ↥(CFSG.LinearGroups.unitaryDet Hf).range)
      (x := ⟨g.1, hmem⟩)
    rw [hrc] at h1
    apply Subtype.ext
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hLker : L.map ι ≤ (CFSG.LinearGroups.unitaryDet Hf).ker := by
    rintro _ ⟨l, hl, rfl⟩
    let g : ↥L →* Eˣ := (CFSG.LinearGroups.unitaryDet Hf).comp (ι.comp L.subtype)
    have h1 : (⟨l, hl⟩ : ↥L) ∈ commutator ↥L := by
      rw [hLp.commutator_eq_top]; exact Subgroup.mem_top _
    exact Abelianization.commutator_subset_ker g h1
  have hkercard : Nat.card ↥(CFSG.LinearGroups.unitaryDet Hf).ker = 25920 := by
    rw [hker, ← hSUcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).toEquiv
  haveI : Finite ↥(CFSG.LinearGroups.unitaryDet Hf).ker :=
    Nat.finite_of_card_ne_zero (by rw [hkercard]; norm_num)
  have hLeq : L.map ι = (CFSG.LinearGroups.unitaryDet Hf).ker := by
    refine Subgroup.eq_of_le_of_card_ge hLker ?_
    rw [Subgroup.card_map_of_injective hι, hkercard]
    exact Nat.le_of_dvd Nat.card_pos hL
  have hfker : ∀ x : X, x ∈ f.ker → (ι x : LinearMap.GeneralLinearGroup E W) ∈
      sesqSpecialUnitaryGroup Hf := by
    intro x hx
    rw [mem_sesqSpecialUnitaryGroup]
    refine ⟨(ι x).2, ?_⟩
    have h1 : CFSG.LinearGroups.unitaryDet Hf (ι x) = 1 := hx
    have := congrArg (fun u : Eˣ => (u : E)) h1
    simpa [CFSG.LinearGroups.unitaryDet_apply] using this
  let φ : ↥f.ker →* ↥(sesqSpecialUnitaryGroup Hf) :=
    (((sesqUnitaryGroup Hf).subtype.comp ι).comp f.ker.subtype).codRestrict
      (sesqSpecialUnitaryGroup Hf) (fun x => hfker x.1 x.2)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h0 := congrArg Subtype.val hab
    exact Subtype.ext (hι (Subtype.ext h0))
  have hφsurj : Function.Surjective φ := by
    intro y
    have hyGU : (y : LinearMap.GeneralLinearGroup E W) ∈ sesqUnitaryGroup Hf :=
      sesqSpecialUnitaryGroup_le Hf y.2
    have hy : (⟨y.1, hyGU⟩ : ↥(sesqUnitaryGroup Hf)) ∈ (CFSG.LinearGroups.unitaryDet Hf).ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact y.2
    rw [← hLeq] at hy
    obtain ⟨l, hl, hly⟩ := hy
    have hlker : l ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      show CFSG.LinearGroups.unitaryDet Hf (ι l) = 1
      rw [hly]
      exact hLker ⟨l, hl, hly⟩
    refine ⟨⟨l, hlker⟩, Subtype.ext ?_⟩
    have h3 := congrArg Subtype.val hly
    exact h3
  let e := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  haveI : Finite ↥(sesqSpecialUnitaryGroup Hf) :=
    Nat.finite_of_card_ne_zero (by rw [hSUcard]; norm_num)
  haveI := CFSG.LargeExtraspecial.S14.PSLPSU10.isSimpleGroup_sesqSpecialUnitaryGroup hE hsymm hsep
    hn (by norm_num) (by norm_num)
  have hker' : CFSG.pPrimeCore 3 ↥f.ker = ⊥ :=
    pPrimeCore_eq_bot_of_mulEquiv e (pPrimeCore_eq_bot_of_simple (by rw [hSUcard]; norm_num))
  exact pPrimeCore_eq_bot_of_ker_range f hker' hrange

end Unitary


theorem card_sp_one : Nat.card (StatedSp 1 (ZMod 2)) = 6 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod]
  decide

theorem card_sp_two : Nat.card (StatedSp 2 (ZMod 2)) = 720 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod,
    show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  norm_num

theorem card_sp_three : Nat.card (StatedSp 3 (ZMod 2)) = 1451520 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod,
    show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.prod_insert (by norm_num),
    Finset.prod_pair (by norm_num)]
  norm_num

theorem isSimpleGroup_sp_three : IsSimpleGroup (StatedSp 3 (ZMod 2)) := by
  have : IsSimpleGroup (StatedProj (StatedSp 3 (ZMod 2))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) 3 (by norm_num)
      (Or.inr (Or.inr ⟨Nat.card_zmod 2, le_rfl⟩))
  exact CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.projEquiv.isSimpleGroup

theorem not_comm_of_simple_of_card {T : Type*} [Group T] [IsSimpleGroup T]
    (h : ¬ (Nat.card T).Prime) : ¬ ∀ a b : T, a * b = b * a := by
  intro hcomm
  letI : CommGroup T := { (inferInstance : Group T) with mul_comm := hcomm }
  exact h ((CommGroup.is_simple_iff_prime_card (α := T)).1 inferInstance)

theorem pPrimeCore_centralizer_sp8 {s : StatedSp 4 (ZMod 2)} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (hq : HasU4Quot (Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2))))) :
    CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2)))) = ⊥ := by
  obtain ⟨s₀, m, A₀, A₁, hc⟩ := exists_class hs3 hs1
  obtain ⟨E, _, hE, W, _, _, _, Hf, hsymm, hsep, hdim, ⟨e₁⟩⟩ := hc.unitary
  have hsum := hc.sum_eq
  have hpos : 25920 ≤ Nat.card ↥(Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2)))) :=
    Nat.le_of_dvd Nat.card_pos hq.dvd_card
  have hbound : Nat.card ↥(Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2)))) ≤
      Nat.card ↥A₀ * Nat.card ↥A₁ := by
    rw [hc.centralizer_eq]
    exact card_sup_le hc.commute
  have hA₁ : Nat.card ↥A₁ = Nat.card (sesqUnitaryGroup Hf) := Nat.card_congr e₁.toEquiv
  have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by have := hc.one_le; omega
  rcases hm with rfl | rfl | rfl | rfl
  ·
    have hs₀ : s₀ = 3 := by omega
    subst hs₀
    obtain ⟨-, e₀⟩ := hc.fixed.resolve_left (by omega)
    obtain ⟨e₀⟩ := e₀
    haveI := isSimpleGroup_sp_three
    haveI : IsSimpleGroup ↥A₀ := e₀.isSimpleGroup
    have hcard₀ : Nat.card ↥A₀ = 1451520 := by
      rw [Nat.card_congr e₀.toEquiv]; exact card_sp_three
    have hcard₁ : Nat.card ↥A₁ = 3 := by rw [hA₁]; exact card_unitary_one hE hsymm hsep hdim
    have hZ : Subgroup.center ↥A₀ = ⊥ :=
      center_eq_bot_of_simple_of_not_comm (not_comm_of_simple_of_card (by rw [hcard₀]; norm_num))
    have hOA₀ : CFSG.pPrimeCore 3 ↥A₀ = ⊥ :=
      pPrimeCore_eq_bot_of_simple (by rw [hcard₀]; norm_num)
    have hC := hc.centralizer_eq
    refine pPrimeCore_eq_bot_of_normal_in _ (fun _ : Unit => A₀) (fun _ => ?_) (fun _ x hx k hk => ?_)
      (fun _ => hOA₀) (fun g hg hcen => ?_)
    · rw [hC]; exact le_sup_left
    · rw [hC] at hx
      exact conj_mem_of_mem_sup hc.commute hx hk
    · rw [hC] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc.commute hg
      have ha1 : a = 1 := by
        have hmem : (⟨a, ha⟩ : ↥A₀) ∈ Subgroup.center ↥A₀ := by
          rw [Subgroup.mem_center_iff]
          intro k
          apply Subtype.ext
          have h1 := hcen () k.1 k.2
          have h2 : (k : StatedSp 4 (ZMod 2)) * b = b * k := hc.commute k k.2 b hb
          show (k : StatedSp 4 (ZMod 2)) * a = a * k
          have h3 : (k * a) * b = (a * k) * b := by
            calc (k * a) * b = k * (a * b) := by rw [mul_assoc]
              _ = (a * b) * k := h1.symm
              _ = a * (b * k) := by rw [mul_assoc]
              _ = a * (k * b) := by rw [h2]
              _ = (a * k) * b := by rw [mul_assoc]
          exact mul_right_cancel h3
        rw [hZ, Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      subst ha1
      refine ⟨1, ?_⟩
      have h1 := pow_card_eq_one' (G := ↥A₁) (x := ⟨b, hb⟩)
      rw [hcard₁] at h1
      have h2 := congrArg Subtype.val h1
      simpa using h2
  ·
    have hs₀ : s₀ = 2 := by omega
    subst hs₀
    obtain ⟨-, e₀⟩ := hc.fixed.resolve_left (by omega)
    obtain ⟨e₀⟩ := e₀
    have hcard₀ : Nat.card ↥A₀ = 720 := by
      rw [Nat.card_congr e₀.toEquiv]; exact card_sp_two
    rw [hA₁, card_unitary_two hE hsymm hsep hdim, hcard₀] at hbound
    omega
  ·
    have hs₀ : s₀ = 1 := by omega
    subst hs₀
    obtain ⟨-, e₀⟩ := hc.fixed.resolve_left (by omega)
    obtain ⟨e₀⟩ := e₀
    have hcard₀ : Nat.card ↥A₀ = 6 := by
      rw [Nat.card_congr e₀.toEquiv]; exact card_sp_one
    rw [hA₁, card_unitary_three hE hsymm hsep hdim, hcard₀] at hbound
    omega
  ·
    have hs₀ : s₀ = 0 := by omega
    subst hs₀
    have hA₀ : A₀ = ⊥ := (hc.fixed.resolve_right (by omega)).2
    have hC : Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2))) = A₁ := by
      rw [hc.centralizer_eq, hA₀, bot_sup_eq]
    obtain ⟨L, hLC, hLp, hLd⟩ := hq.exists_perfect
    have hCA : Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2))) ≤ A₁ := hC.le
    let ι : ↥(Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2)))) →* sesqUnitaryGroup Hf :=
      e₁.toMonoidHom.comp (Subgroup.inclusion hCA)
    have hι : Function.Injective ι :=
      e₁.injective.comp (Subgroup.inclusion_injective hCA)
    refine pPrimeCore_of_unitary_four hE hsymm hsep hdim ι hι
      (L.subgroupOf (Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2))))) ?_ ?_
    · rw [Subgroup.isPerfect_iff]
      exact subgroupOf_perfect hLC hLp
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLC).toEquiv]
      exact hLd

end CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8

end
