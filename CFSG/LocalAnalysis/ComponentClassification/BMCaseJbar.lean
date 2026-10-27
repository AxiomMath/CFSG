module

public import CFSG.LocalAnalysis.ComponentClassification.BMCaseCo2Local
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseExtraspecial
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseLinear
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Monster.Existence.TwoB

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B
  CFSG.Monster.B.Short

section Image

variable (v : L2)

theorem wAct_inv_mul (k : Kstab v) : wAct v k⁻¹ * wAct v k = 1 := by
  have h := congrArg MulOpposite.unop (map_mul (KvAct v) k k⁻¹)
  rw [mul_inv_cancel, map_one] at h
  exact h.symm

@[expose] def wActUnit (k : Kstab v) : LinearMap.GeneralLinearGroup (ZMod 2) (Wv v) :=
  ⟨wAct v k, wAct v k⁻¹, by simpa using wAct_inv_mul v k⁻¹, wAct_inv_mul v k⟩

@[expose] def wActOpHom : Kstab v →* (LinearMap.GeneralLinearGroup (ZMod 2) (Wv v))ᵐᵒᵖ where
  toFun k := MulOpposite.op (wActUnit v k)
  map_one' := by
    rw [← MulOpposite.op_one]
    congr 1
    exact Units.ext (congrArg MulOpposite.unop (map_one (KvAct v)))
  map_mul' k k' := by
    rw [← MulOpposite.op_mul]
    congr 1
    exact Units.ext (congrArg MulOpposite.unop (map_mul (KvAct v) k k'))

@[expose] def wActImage : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Wv v)) :=
  (wActOpHom v).range.unop

theorem mem_wActImage {v : L2} {g : LinearMap.GeneralLinearGroup (ZMod 2) (Wv v)} :
    g ∈ wActImage v ↔ ∃ k : Kstab v, (g : Module.End (ZMod 2) (Wv v)) = wAct v k := by
  rw [wActImage, Subgroup.mem_unop, MonoidHom.mem_range]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, congrArg Units.val (MulOpposite.op_injective hk).symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, congrArg MulOpposite.op (Units.ext hk.symm)⟩

theorem natCard_wActImage (hinj : Function.Injective (KvAct v)) :
    Nat.card (wActImage v) = Nat.card (Kstab v) := by
  have hinj' : Function.Injective (wActOpHom v) := fun k k' h =>
    hinj (congrArg MulOpposite.op (congrArg Units.val (MulOpposite.op_injective h)))
  have h1 : Nat.card (wActImage v) = Nat.card (wActOpHom v).range := by
    rw [wActImage]
    calc Nat.card ((wActOpHom v).range.unop) = Nat.card ((wActOpHom v).range.unop.op) :=
          Nat.card_congr (Subgroup.equivOp _)
      _ = Nat.card (wActOpHom v).range := by rw [Subgroup.op_unop]
  rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv]

end Image

theorem wActImage_centralizer_pow_three {v : L2} (hv : ∃ u ∈ minVecs, classOf u = v)
    (a : LinearMap.GeneralLinearGroup (ZMod 2) (Wv v))
    (ha : a ∈ Subgroup.centralizer
      (wActImage v : Set (LinearMap.GeneralLinearGroup (ZMod 2) (Wv v)))) : a ^ 3 = 1 := by
  obtain ⟨u, hu, rfl⟩ := hv
  obtain ⟨hinj, hdim, hirr⟩ := Co2.native_short_stabilizer_irreducible hu
  have hcard := (Co2.native_short_stabilizer_simple.1 u hu).2.2
  refine pow_three_eq_one_of_dim_twentytwo hdim _ (fun U hU => hirr U fun k w hw => ?_) ?_ a ha
  · exact hU (wActUnit _ k) (mem_wActImage.2 ⟨k, rfl⟩) w hw
  · rw [natCard_wActImage _ hinj, hcard]
    norm_num

theorem wActImage_irreducible {v : L2} (hv : ∃ u ∈ minVecs, classOf u = v)
    (U : Submodule (ZMod 2) (Wv v))
    (hU : ∀ k ∈ wActImage v, ∀ w ∈ U, (k : Wv v →ₗ[ZMod 2] Wv v) w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  obtain ⟨u, hu, rfl⟩ := hv
  exact (Co2.native_short_stabilizer_irreducible hu).2.2 U fun k w hw =>
    hU (wActUnit _ k) (mem_wActImage.2 ⟨k, rfl⟩) w hw

theorem exists_mul_ne_mul_of_not_prime {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hc }
  exact h IsSimpleGroup.prime_card

@[expose] def xJ : Jbar := ⟨xbar, xbar_mem_Jbar⟩

@[expose] def ebarJEquiv : Ebar.subgroupOf Jbar ≃* Ebar :=
  Subgroup.subgroupOfEquivOfLe Ebar_le_Jbar

theorem coe_ebarJEquiv (q : Ebar.subgroupOf Jbar) :
    ((ebarJEquiv q : Ebar) : Cbar) = ((q : Jbar) : Cbar) := rfl

theorem map_subtype_zpowers_xJ :
    (Subgroup.zpowers xJ).map Jbar.subtype = Subgroup.zpowers xbar :=
  MonoidHom.map_zpowers _ _

theorem map_center_ebarJ :
    (Subgroup.center (Ebar.subgroupOf Jbar)).map (Ebar.subgroupOf Jbar).subtype =
      Subgroup.zpowers xJ := by
  apply Subgroup.map_injective Jbar.subtype_injective
  rw [map_subtype_zpowers_xJ, Subgroup.map_map, ← map_center_Ebar,
    ← Existence.center_map_mulEquiv ebarJEquiv, Subgroup.map_map]
  rfl

theorem centralizer_ebarJ :
    Subgroup.centralizer ((Ebar.subgroupOf Jbar : Subgroup Jbar) : Set Jbar) =
      Subgroup.zpowers xJ := by
  apply Subgroup.map_injective Jbar.subtype_injective
  rw [map_subtype_zpowers_xJ, ← centralizer_Ebar]
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g.2, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
    have h := Subgroup.mem_centralizer_iff.1 hg ⟨e, Ebar_le_Jbar he⟩
      (Subgroup.mem_subgroupOf.2 he)
    exact congrArg Subtype.val h
  · rintro ⟨hgJ, hgc⟩
    refine ⟨⟨g, hgJ⟩, Subgroup.mem_centralizer_iff.2 fun q hq => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hgc q (Subgroup.mem_subgroupOf.1 hq))

theorem mem_ebarJ_of_conj (h : Jbar)
    (hh : ∀ q ∈ Ebar.subgroupOf Jbar, h * q * h⁻¹ * q⁻¹ ∈
      (Subgroup.center (Ebar.subgroupOf Jbar)).map (Ebar.subgroupOf Jbar).subtype) :
    h ∈ Ebar.subgroupOf Jbar := by
  rw [map_center_ebarJ] at hh
  have hinv : ((h⁻¹ : Jbar) : Cbar) ∈ Ebar := by
    refine mem_Ebar_of_conj_trivial (h⁻¹ : Jbar).2 fun e he => ?_
    have hc := hh ⟨e, Ebar_le_Jbar he⟩ (Subgroup.mem_subgroupOf.2 he)
    have hc' : ((h : Cbar) * e * (h : Cbar)⁻¹ * e⁻¹) ∈ Subgroup.zpowers xbar := by
      rw [← map_subtype_zpowers_xJ]
      exact ⟨_, hc, rfl⟩
    rw [← map_center_Ebar] at hc'
    obtain ⟨c, hcZ, hce⟩ := hc'
    have hconj : ((h⁻¹ : Jbar) : Cbar)⁻¹ * e * ((h⁻¹ : Jbar) : Cbar) =
        (h : Cbar) * e * (h : Cbar)⁻¹ := by
      simp only [InvMemClass.coe_inv, inv_inv]
    have hmem : (h : Cbar) * e * (h : Cbar)⁻¹ ∈ Ebar := hconj ▸ conj_mem_Ebar (h⁻¹ : Jbar).2 he
    have hc1 : psiBar c = 1 := by rw [← MonoidHom.mem_ker, ker_psiBar]; exact hcZ
    have hcd : c = ⟨(h : Cbar) * e * (h : Cbar)⁻¹, hmem⟩ * (⟨e, he⟩ : Ebar)⁻¹ :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv]; exact hce)
    rw [hcd, map_mul, map_inv, mul_inv_eq_one] at hc1
    have e1 : (⟨((h⁻¹ : Jbar) : Cbar)⁻¹ * e * ((h⁻¹ : Jbar) : Cbar),
        conj_mem_Ebar (h⁻¹ : Jbar).2 he⟩ : Ebar) = ⟨(h : Cbar) * e * (h : Cbar)⁻¹, hmem⟩ :=
      Subtype.ext hconj
    rw [e1, hc1]
  have : ((h : Jbar) : Cbar) ∈ Ebar := by
    have := Ebar.inv_mem hinv
    simpa using this
  exact Subgroup.mem_subgroupOf.2 this

@[expose] def jbarQuotKvEquiv : Jbar ⧸ Ebar.subgroupOf Jbar ≃* Kstab (phi0 (coordOf rStar)) :=
  (QuotientGroup.quotientMulEquivOfEq ker_jbarToKv.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective jbarToKv jbarToKv_surjective)

@[expose] def psiJ : Ebar.subgroupOf Jbar →* Multiplicative (Wv (phi0 (coordOf rStar))) :=
  psiBar.comp ebarJEquiv.toMonoidHom

theorem psiJ_conj (g : Jbar) (q : Ebar.subgroupOf Jbar) :
    psiJ (MulAut.conjNormal g⁻¹ q) =
      Multiplicative.ofAdd (wAct _ (jbarToKv g) (Multiplicative.toAdd (psiJ q))) := by
  have hq : ((q : Jbar) : Cbar) ∈ Ebar := Subgroup.mem_subgroupOf.1 q.2
  have h := psiBar_conj g.2 hq
  have e1 : ebarJEquiv (MulAut.conjNormal g⁻¹ q) =
      ⟨(g : Cbar)⁻¹ * ((q : Jbar) : Cbar) * g, conj_mem_Ebar g.2 hq⟩ := by
    apply Subtype.ext
    rw [coe_ebarJEquiv, MulAut.conjNormal_apply]
    simp
  have e2 : ebarJEquiv q = ⟨((q : Jbar) : Cbar), hq⟩ := rfl
  change psiBar (ebarJEquiv (MulAut.conjNormal g⁻¹ q)) =
    Multiplicative.ofAdd (wAct _ (jbarToKv g) (Multiplicative.toAdd (psiBar (ebarJEquiv q))))
  rw [e1, e2, h]

theorem model_conj_of_right_action {H L : Type*} [Group H] [Group L] {Q : Subgroup H} [Q.Normal]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (ψ : Q →* Multiplicative W)
    (π : H →* L) (hπ : Function.Surjective π) (act : L → Module.End (ZMod 2) W)
    (hconj : ∀ (g : H) (q : Q), ψ (MulAut.conjNormal g⁻¹ q) =
      Multiplicative.ofAdd (act (π g) (Multiplicative.toAdd (ψ q))))
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))
    (hK : ∀ k ∈ K, ∃ l : L, (k : Module.End (ZMod 2) W) = act l) :
    ∀ k ∈ K, ∃ h : H, ∀ q : Q, ψ (MulAut.conjNormal h q) =
      Multiplicative.ofAdd ((k : W →ₗ[ZMod 2] W) (Multiplicative.toAdd (ψ q))) := by
  intro k hk
  obtain ⟨l, hl⟩ := hK k hk
  obtain ⟨g, rfl⟩ := hπ l
  refine ⟨g⁻¹, fun q => ?_⟩
  rw [hconj, hl]

theorem mulEquiv_mem_center_iff {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    e a ∈ Subgroup.center B ↔ a ∈ Subgroup.center A := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h a'
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e a')
  · intro h b
    obtain ⟨a', rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, h a']

theorem ker_psiJ : psiJ.ker = Subgroup.center (Ebar.subgroupOf Jbar) := by
  ext q
  rw [MonoidHom.mem_ker, ← mulEquiv_mem_center_iff ebarJEquiv, ← ker_psiBar, MonoidHom.mem_ker]
  rfl

theorem jbar_perfect_and_inner :
    Group.IsPerfect Jbar ∧ ∀ α : MulAut Jbar, ∃ g : Jbar, α = MulAut.conj g := by
  have hv : ∃ u ∈ minVecs, classOf u = phi0 (coordOf rStar) :=
    ⟨vMinus 0 1, vMinus_mem (by decide), phi0_coordOf_rStar.symm⟩
  have hQ : IsExtraspecialPGroup 2 (Ebar.subgroupOf Jbar) :=
    Existence.IsExtraspecialPGroup.of_mulEquiv ebarJEquiv.symm Ebar_extraspecial.1
  have hcardQ : Nat.card (Ebar.subgroupOf Jbar) = 2 ^ 23 :=
    (Nat.card_congr ebarJEquiv.toEquiv).trans Ebar_extraspecial.2
  obtain ⟨hKs, hKc⟩ := Kstab_rStar_simple
  have hsimple : IsSimpleGroup (Jbar ⧸ Ebar.subgroupOf Jbar) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hKs jbarQuotKvEquiv
  have hcardJE : Nat.card (Jbar ⧸ Ebar.subgroupOf Jbar) = 42305421312000 :=
    (Nat.card_congr jbarQuotKvEquiv.toEquiv).trans hKc
  have hnab : ∃ a b : Jbar ⧸ Ebar.subgroupOf Jbar, a * b ≠ b * a :=
    exists_mul_ne_mul_of_not_prime (by rw [hcardJE]; norm_num)
  have hinn := CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner_model
    (Jbar ⧸ Ebar.subgroupOf Jbar) Co2Catalog.jbarQuotEquiv
  have hψker : psiJ.ker = Subgroup.center (Ebar.subgroupOf Jbar) := ker_psiJ
  have h23 : 23 ∣ Nat.card (Jbar ⧸ Ebar.subgroupOf Jbar) := by rw [hcardJE]; norm_num
  have hCQ := centralizer_ebarJ.trans map_center_ebarJ.symm
  have hψ : Function.Surjective psiJ := psiBar_surjective.comp ebarJEquiv.surjective
  exact perfect_and_inner_of_model hQ (Or.inl hcardQ) hCQ mem_ebarJ_of_conj hsimple hnab hinn
    h23 psiJ hψ hψker (wActImage _)
    (model_conj_of_right_action psiJ jbarToKv jbarToKv_surjective (wAct _) psiJ_conj
      (wActImage _) fun _ hk => mem_wActImage.1 hk)
    (wActImage_irreducible hv) (wActImage_centralizer_pow_three hv)

end CFSG.ComponentClassification.BMCase
