module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCBasic
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus
public import CFSG.LocalAnalysis.ComponentInitial.GroupComponents
public import CFSG.Walter.Ree.Model.Fusion

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Walter.Ree.Model
open scoped MatrixGroups

theorem oddReeInvolutionSLForm_holds
    :
    ∀ (J : Type) [Group J] (n p f : ℕ), Blueprint.LieModel J .twistedG2 n p f →
      ∀ t : J, orderOf t = 2 → ∀ R : Subgroup J, R ≤ centralizer ({t} : Set J) →
        IsPComponent 2 (R.subgroupOf (centralizer ({t} : Set J))) →
          IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ t ∉ R := by
  intro J _ n p f hm t ht R hR hRc
  have hRT : ReeTitsModel J .twistedG2 p f := by
    rcases hm with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
    · exact h
    · exact absurd ht' (by decide)
  obtain ⟨-, -, hp3, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier J p f hRT
  subst hp3
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := hRT
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  set Γ := ReeTag.G2.reeGamma K a' with hΓ
  set t₀ : Γ := E t with ht₀def
  have ht₂ : orderOf (t₀ : ModGL ReeTag.G2.tag K) = 2 := by
    rw [Subgroup.orderOf_coe, ht₀def, MulEquiv.orderOf_eq, ht]
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨g, hgΓ, hgt⟩ :=
    (small_Ree_prime_field_involution_fusion a' K hK' w₀ hw₀).2.2.2.2.2 t₀ t₀.2 ht₂
  set C := smallReeInvCentralizer a' K with hCdef
  have hCmap : (Γ ⊓ centralizer {(t₀ : ModGL ReeTag.G2.tag K)}).map
      (MulAut.conj g).toMonoidHom = C := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
      LieType.Chevalley.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hgΓ),
      LocalAnalysis.ComponentInitial.map_centralizer_singleton, MulAut.conj_apply, hgt]
    rfl
  have hΓmap : (centralizer ({t₀} : Set Γ)).map Γ.subtype =
      Γ ⊓ centralizer {(t₀ : ModGL ReeTag.G2.tag K)} := by
    rw [LocalAnalysis.ComponentInitial.map_centralizer_singleton_of_injective
      Γ.subtype_injective, Subgroup.range_subtype]
    rfl
  set H := centralizer ({t} : Set J) with hHdef
  let Θ : H ≃* C :=
    ((H.equivMapOfInjective E.toMonoidHom E.injective).trans (MulEquiv.subgroupCongr
      (LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv E t))).trans
      ((((centralizer ({t₀} : Set Γ)).equivMapOfInjective Γ.subtype
        Γ.subtype_injective).trans (MulEquiv.subgroupCongr hΓmap)).trans
          (((Γ ⊓ centralizer {(t₀ : ModGL ReeTag.G2.tag K)}).equivMapOfInjective
            (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
            (MulEquiv.subgroupCongr hCmap)))
  obtain ⟨ψ, hψC, -, -, -, -, -, ⟨hsup, -, hcent⟩, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a' K hK' w₀ hw₀
  set h := smallReeH a' K (-1)
  rw [← hCdef] at hsup
  simp only [← hCdef] at hψC
  have hLC : ψ.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    exact hψC x
  have htC : h ∈ C := hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
  set N := ψ.range.subgroupOf C with hNdef
  have hNn : N.Normal := by
    rw [hNdef, Subgroup.normal_subgroupOf_iff_le_normalizer hLC, ← hsup]
    exact sup_le (hcent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hT : Subgroup.zpowers (⟨h, htC⟩ : C) ⊔ N = ⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hNdef, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hLC, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hsup
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' N).comp (Subgroup.zpowers (⟨h, htC⟩ : C)).subtype) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hc : c ∈ (Subgroup.zpowers (⟨h, htC⟩ : C) ⊔ N : Subgroup C) := hT ▸ Subgroup.mem_top c
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hc
    obtain ⟨x, hx, n, hn, rfl⟩ := hc
    refine ⟨⟨x, hx⟩, ?_⟩
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    change QuotientGroup.mk' N x = QuotientGroup.mk' N (x * n)
    rw [map_mul, hn1, mul_one]
  have : IsCyclic (C ⧸ N) := isCyclic_of_surjective _ hsurj
  have hsolv : Group.IsSolvable (C ⧸ N) :=
    Group.isSolvable_of_comm fun x y => IsMulCommutative.is_comm.comm x y
  have hq27 : 27 ≤ Nat.card K := by
    rw [hK']
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * a' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 K le_rfl (Or.inr hK2) (Or.inr hK3)
  have hsimp : IsSimpleGroup ψ.range := e.symm.isSimpleGroup
  have hnab : ∃ x y : ψ.range, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian K hK2 hK3
    exact ⟨e x, e y, fun h' => hxy (e.injective (by rw [map_mul, map_mul, h']))⟩
  have hqs : IsQuasisimple ψ.range :=
    LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hnab
  set R' := (R.subgroupOf H).map Θ.toMonoidHom with hR'def
  have hR'c : IsPComponent 2 R' :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Θ hRc
  have hR'N : R' ≤ N := by
    have hperf := CatalogueBAlternating.pComponent_perfect hR'c
    intro y hy
    have hf := MonoidHom.range_eq_bot_iff.1
      (LieType.Chevalley.OddToralOrdinary.range_eq_bot_of_commutator_eq_top
        (Group.isPerfect_def.mp hperf) ((QuotientGroup.mk' N).comp R'.subtype))
    have hy' : (QuotientGroup.mk' N) y = 1 := DFunLike.congr_fun hf ⟨y, hy⟩
    exact (QuotientGroup.eq_one_iff y).1 hy'
  set R'' := R'.map C.subtype with hR''def
  have hR''L : R'' ≤ ψ.range := by
    rintro _ ⟨y, hy, rfl⟩
    exact hR'N hy
  have hR''c : IsPComponent 2 (R''.subgroupOf C) := by
    have hsub : (R'.map C.subtype).subgroupOf C = R' :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective R'
    rw [hR''def, hsub]
    exact hR'c
  have hR''eq : R'' = ψ.range := Burgoyne.C.eq_of_le_of_isQuasisimple hR''L hLC hR''c hqs
  let eR : R ≃* ψ.range :=
    ((((Subgroup.subgroupOfEquivOfLe hR).symm.trans
      ((R.subgroupOf H).equivMapOfInjective _ Θ.injective)).trans
        (R'.equivMapOfInjective _ C.subtype_injective)).trans (MulEquiv.subgroupCongr hR''eq))
  have hRs : IsSimpleGroup R := eR.isSimpleGroup
  have hRnab : ∃ x y : R, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨eR.symm x, eR.symm y, fun h' => hxy (eR.symm.injective (by
      rw [map_mul, map_mul, h']))⟩
  refine ⟨hRs, hRnab, fun htR => ?_⟩
  have hcen : (⟨t, htR⟩ : R) ∈ center R := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hR y.2))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center R) with hb | hb
  · rw [hb, mem_bot] at hcen
    have h1 : t = 1 := congrArg Subtype.val hcen
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · obtain ⟨x, y, hxy⟩ := hRnab
    exact hxy ((mem_center_iff.1 (hb ▸ mem_top y)) x)

end CFSG.ComponentClassification.CatLeafProof
