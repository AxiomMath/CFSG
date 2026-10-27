module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec36
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LieType.SeitzGeneration
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv
  exists_coe_add_of_isCompl)

namespace LinEngine

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {p : ℕ}

theorem mapsTo_blockSpace_of_commute (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D : HypBlocks.Hyperplane A p} {k : V ≃ₗ[F] V}
    (hk : k * HypBlocks.blockEnd A hp hpF hA t ht D =
      HypBlocks.blockEnd A hp hpF hA t ht D * k) :
    ∀ u ∈ HypBlocks.blockSpace A D.1, k u ∈ HypBlocks.blockSpace A D.1 := by
  set gD := HypBlocks.blockEnd A hp hpF hA t ht D with hgD
  intro u hu
  rw [← range_blockEnd_sub_one A hp hpF hA t ht D] at hu ⊢
  obtain ⟨x, rfl⟩ := hu
  refine ⟨k x, ?_⟩
  have h : k (gD x) = gD (k x) := by
    have h' := congrArg (fun f : V ≃ₗ[F] V => f x) hk
    simpa only [LinearEquiv.mul_apply, hgD] using h'
  have hstep1 : k (((gD : V →ₗ[F] V) - 1) x) = k (gD x) - k x := by
    rw [LinearMap.sub_apply]
    simp
  have hstep3 : gD (k x) - k x = ((gD : V →ₗ[F] V) - 1) (k x) := by
    rw [LinearMap.sub_apply]
    simp
  have hmid : k (gD x) - k x = gD (k x) - k x := by rw [h]
  exact (hstep1.trans (hmid.trans hstep3)).symm


noncomputable def toJsubHom [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hAdet : A ≤ LinearEquiv.det.ker) (D : HypBlocks.Hyperplane A p) :
    ↥D.1 →* ↥(Jsub A hp hpF hA t ht D) where
  toFun a :=
    ⟨⟨((a : ↥A) : V ≃ₗ[F] V), MonoidHom.mem_ker.mp (hAdet (a : ↥A).2)⟩, by
      refine mem_Jsub.mpr ⟨?_, ?_⟩
      · intro u hu
        exact (HypBlocks.mem_blockSpace A).mp hu |>.1 (a : ↥A) a.2
      · intro s hs
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact HypBlocks.blockEnd_commute A hp hpF hA t ht D (a : ↥A)⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem toJsubHom_injective [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hAdet : A ≤ LinearEquiv.det.ker) (D : HypBlocks.Hyperplane A p) :
    Function.Injective (toJsubHom A hp hpF hA t ht hAdet D) := by
  intro a b hab
  have h := congrArg
    (fun g : ↥(Jsub A hp hpF hA t ht D) => ((g : SpecialLinearGroup F V) : V ≃ₗ[F] V)) hab
  exact Subtype.ext (Subtype.ext h)

theorem dvd_card_Jsub [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hAdet : A ≤ LinearEquiv.det.ker) {k : ℕ} (hk : Nat.card A = p ^ k) (hk3 : 3 ≤ k)
    (D : HypBlocks.Hyperplane A p) :
    p ∣ Nat.card ↥(Jsub A hp hpF hA t ht D) := by
  have hcardD : Nat.card ↥D.1 = p ^ (k - 1) := by
    have h := Subgroup.card_mul_index D.1
    rw [D.2, hk] at h
    have h' : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    rw [h'] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos h
  have hinj := toJsubHom_injective A hp hpF hA t ht hAdet D
  have hdvd : Nat.card ↥D.1 ∣ Nat.card ↥(Jsub A hp hpF hA t ht D) := by
    have h := Subgroup.card_subgroup_dvd_card (MonoidHom.range (toJsubHom A hp hpF hA t ht hAdet D))
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h
    exact h
  rw [hcardD] at hdvd
  exact (dvd_pow_self p (by omega : k - 1 ≠ 0)).trans hdvd

noncomputable def toLsubHom [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hAdet : A ≤ LinearEquiv.det.ker) (D E : HypBlocks.Hyperplane A p) :
    ↥(D.1 ⊓ E.1) →* ↥(Lsub A hp hpF hA t ht D E) where
  toFun a :=
    ⟨⟨((a : ↥A) : V ≃ₗ[F] V), MonoidHom.mem_ker.mp (hAdet (a : ↥A).2)⟩, by
      refine mem_Lsub.mpr ⟨?_, ?_⟩
      · intro u hu
        obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
        rw [map_add, (HypBlocks.mem_blockSpace A).mp hx |>.1 (a : ↥A) a.2.1,
          (HypBlocks.mem_blockSpace A).mp hy |>.1 (a : ↥A) a.2.2]
      · intro s hs
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact HypBlocks.blockEnd_commute A hp hpF hA t ht D (a : ↥A)
        · exact HypBlocks.blockEnd_commute A hp hpF hA t ht E (a : ↥A)⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem toLsubHom_injective [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hAdet : A ≤ LinearEquiv.det.ker) (D E : HypBlocks.Hyperplane A p) :
    Function.Injective (toLsubHom A hp hpF hA t ht hAdet D E) := by
  intro a b hab
  have h := congrArg (fun g : ↥(Lsub A hp hpF hA t ht D E) =>
    ((g : SpecialLinearGroup F V) : V ≃ₗ[F] V)) hab
  exact Subtype.ext (Subtype.ext h)

theorem dvd_card_Lsub [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hAdet : A ≤ LinearEquiv.det.ker) {k : ℕ} (hk : Nat.card A = p ^ k) (hk3 : 3 ≤ k)
    {D E : HypBlocks.Hyperplane A p} (hDE : D ≠ E) :
    p ∣ Nat.card ↥(Lsub A hp hpF hA t ht D E) := by
  haveI : IsMulCommutative ↥A := hA.1
  have hcardDE : Nat.card ↥(D.1 ⊓ E.1) = p ^ (k - 2) := by
    have hprod : Nat.card ↥(D.1 ⊓ E.1) * (D.1 ⊓ E.1).index = Nat.card A :=
      Subgroup.card_mul_index (D.1 ⊓ E.1)
    have hsup : D.1 ⊔ E.1 = ⊤ := by
      refine HyperBlocks.sup_eq_of_ne_relIndex_prime hp le_top le_top ?_ ?_ ?_
      · rw [Subgroup.relIndex_top_right]; exact D.2
      · rw [Subgroup.relIndex_top_right]; exact E.2
      · exact fun h => hDE (Subtype.ext h)
    have hindex : (D.1 ⊓ E.1).index = p ^ 2 := by
      rw [Subgroup.index_inf, ← Subgroup.relIndex_sup_left E.1 D.1, hsup,
        Subgroup.relIndex_top_right, D.2, E.2]
      ring
    rw [hindex, hk] at hprod
    have h' : p ^ k = p ^ (k - 2) * p ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ k)]
    rw [h'] at hprod
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) hprod
  have hinj := toLsubHom_injective A hp hpF hA t ht hAdet D E
  have hdvd : Nat.card ↥(D.1 ⊓ E.1) ∣ Nat.card ↥(Lsub A hp hpF hA t ht D E) := by
    have h := Subgroup.card_subgroup_dvd_card
      (MonoidHom.range (toLsubHom A hp hpF hA t ht hAdet D E))
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h
    exact h
  rw [hcardDE] at hdvd
  exact (dvd_pow_self p (by omega : k - 2 ≠ 0)).trans hdvd


noncomputable def blockEndSL [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hpd : ¬ p ∣ Fintype.card F - 1) (D : HypBlocks.Hyperplane A p) :
    SpecialLinearGroup F V :=
  ⟨HypBlocks.blockEnd A hp hpF hA t ht D, blockEnd_mem_specialLinear A hp hpF hA t ht hpd D⟩

theorem mem_centralizer_blockEndSL_iff [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hpd : ¬ p ∣ Fintype.card F - 1) (D : HypBlocks.Hyperplane A p)
    {g : SpecialLinearGroup F V} :
    g ∈ Subgroup.centralizer ({blockEndSL A hp hpF hA t ht hpd D} : Set (SpecialLinearGroup F V)) ↔
      (g : V ≃ₗ[F] V) * HypBlocks.blockEnd A hp hpF hA t ht D =
        HypBlocks.blockEnd A hp hpF hA t ht D * (g : V ≃ₗ[F] V) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact congrArg (fun x : SpecialLinearGroup F V => (x : V ≃ₗ[F] V)) h
  · intro h
    exact Subtype.ext h

theorem normal_Jsub [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hpd : ¬ p ∣ Fintype.card F - 1) (D : HypBlocks.Hyperplane A p) :
    ((Jsub A hp hpF hA t ht D).subgroupOf
      (Subgroup.centralizer
        ({blockEndSL A hp hpF hA t ht hpd D} : Set (SpecialLinearGroup F V)))).Normal := by
  have hle : Jsub A hp hpF hA t ht D ≤
      Subgroup.centralizer
        ({blockEndSL A hp hpF hA t ht hpd D} : Set (SpecialLinearGroup F V)) := by
    intro g hg
    rw [mem_centralizer_blockEndSL_iff]
    exact (mem_Jsub.mp hg).2 _ (Set.mem_singleton _)
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h k hh hk
  rw [mem_centralizer_blockEndSL_iff] at hk
  rw [mem_Jsub] at hh ⊢
  have hk_inv : (k : V ≃ₗ[F] V)⁻¹ * HypBlocks.blockEnd A hp hpF hA t ht D =
      HypBlocks.blockEnd A hp hpF hA t ht D * (k : V ≃ₗ[F] V)⁻¹ := by
    have h : Commute (k : V ≃ₗ[F] V) (HypBlocks.blockEnd A hp hpF hA t ht D) := hk
    exact h.inv_left
  refine ⟨?_, ?_⟩
  · intro u hu
    have hkU : (k : V ≃ₗ[F] V) u ∈ HypBlocks.blockSpace A D.1 :=
      mapsTo_blockSpace_of_commute A hp hpF hA t ht hk u hu
    have hkUinv : (k : V ≃ₗ[F] V)⁻¹ u ∈ HypBlocks.blockSpace A D.1 :=
      mapsTo_blockSpace_of_commute A hp hpF hA t ht hk_inv u hu
    change ((k : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V) * (k : V ≃ₗ[F] V)⁻¹) u = u
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hh.1 _ hkUinv]
    exact (k : V ≃ₗ[F] V).apply_symm_apply u
  · intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have hhgD : (h : V ≃ₗ[F] V) * HypBlocks.blockEnd A hp hpF hA t ht D =
        HypBlocks.blockEnd A hp hpF hA t ht D * (h : V ≃ₗ[F] V) :=
      hh.2 _ (Set.mem_singleton _)
    calc ((k : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V) * (k : V ≃ₗ[F] V)⁻¹) *
          HypBlocks.blockEnd A hp hpF hA t ht D
        = (k : V ≃ₗ[F] V) * ((h : V ≃ₗ[F] V) *
            ((k : V ≃ₗ[F] V)⁻¹ * HypBlocks.blockEnd A hp hpF hA t ht D)) := by group
      _ = (k : V ≃ₗ[F] V) * ((h : V ≃ₗ[F] V) *
            (HypBlocks.blockEnd A hp hpF hA t ht D * (k : V ≃ₗ[F] V)⁻¹)) := by rw [hk_inv]
      _ = (k : V ≃ₗ[F] V) * (((h : V ≃ₗ[F] V) * HypBlocks.blockEnd A hp hpF hA t ht D) *
            (k : V ≃ₗ[F] V)⁻¹) := by group
      _ = (k : V ≃ₗ[F] V) * ((HypBlocks.blockEnd A hp hpF hA t ht D * (h : V ≃ₗ[F] V)) *
            (k : V ≃ₗ[F] V)⁻¹) := by rw [hhgD]
      _ = ((k : V ≃ₗ[F] V) * HypBlocks.blockEnd A hp hpF hA t ht D) * (h : V ≃ₗ[F] V) *
            (k : V ≃ₗ[F] V)⁻¹ := by group
      _ = (HypBlocks.blockEnd A hp hpF hA t ht D * (k : V ≃ₗ[F] V)) * (h : V ≃ₗ[F] V) *
            (k : V ≃ₗ[F] V)⁻¹ := by rw [hk]
      _ = HypBlocks.blockEnd A hp hpF hA t ht D *
            ((k : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V) * (k : V ≃ₗ[F] V)⁻¹) := by group


theorem normal_Lsub [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hpd : ¬ p ∣ Fintype.card F - 1) {D E : HypBlocks.Hyperplane A p} (hDE : D ≠ E) :
    ((Lsub A hp hpF hA t ht D E).subgroupOf
      (Jsub A hp hpF hA t ht D ⊓
        Subgroup.centralizer
          ({blockEndSL A hp hpF hA t ht hpd E} : Set (SpecialLinearGroup F V)))).Normal := by
  have hgD : HypBlocks.blockEnd A hp hpF hA t ht D = blockEndSL A hp hpF hA t ht hpd D := rfl
  have hgE : HypBlocks.blockEnd A hp hpF hA t ht E = blockEndSL A hp hpF hA t ht hpd E := rfl
  have hle : Lsub A hp hpF hA t ht D E ≤
      Jsub A hp hpF hA t ht D ⊓
        Subgroup.centralizer
          ({blockEndSL A hp hpF hA t ht hpd E} : Set (SpecialLinearGroup F V)) := by
    intro g hg
    obtain ⟨hfix, hcomm⟩ := mem_Lsub.mp hg
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [mem_Jsub]
      refine ⟨fun u hu => hfix u (Submodule.mem_sup_left hu), fun s hs => ?_⟩
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact hcomm _ (Set.mem_insert _ _)
    · rw [mem_centralizer_blockEndSL_iff]
      exact hcomm _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h k hh hk
  obtain ⟨hkJ, hkC⟩ := Subgroup.mem_inf.mp hk
  rw [mem_centralizer_blockEndSL_iff] at hkC
  have hkD : (k : V ≃ₗ[F] V) * HypBlocks.blockEnd A hp hpF hA t ht D =
      HypBlocks.blockEnd A hp hpF hA t ht D * (k : V ≃ₗ[F] V) :=
    (mem_Jsub.mp hkJ).2 _ (Set.mem_singleton _)
  have hkE : (k : V ≃ₗ[F] V) * HypBlocks.blockEnd A hp hpF hA t ht E =
      HypBlocks.blockEnd A hp hpF hA t ht E * (k : V ≃ₗ[F] V) := hkC
  have hkDinv : (k : V ≃ₗ[F] V)⁻¹ * HypBlocks.blockEnd A hp hpF hA t ht D =
      HypBlocks.blockEnd A hp hpF hA t ht D * (k : V ≃ₗ[F] V)⁻¹ :=
    (show Commute (k : V ≃ₗ[F] V) (HypBlocks.blockEnd A hp hpF hA t ht D) from hkD).inv_left
  have hkEinv : (k : V ≃ₗ[F] V)⁻¹ * HypBlocks.blockEnd A hp hpF hA t ht E =
      HypBlocks.blockEnd A hp hpF hA t ht E * (k : V ≃ₗ[F] V)⁻¹ :=
    (show Commute (k : V ≃ₗ[F] V) (HypBlocks.blockEnd A hp hpF hA t ht E) from hkE).inv_left
  have hkU : ∀ u ∈ HypBlocks.blockSpace A D.1 ⊔ HypBlocks.blockSpace A E.1,
      (k : V ≃ₗ[F] V) u ∈ HypBlocks.blockSpace A D.1 ⊔ HypBlocks.blockSpace A E.1 := by
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (mapsTo_blockSpace_of_commute A hp hpF hA t ht hkD a ha))
      (Submodule.mem_sup_right (mapsTo_blockSpace_of_commute A hp hpF hA t ht hkE b hb))
  have hkUinv : ∀ u ∈ HypBlocks.blockSpace A D.1 ⊔ HypBlocks.blockSpace A E.1,
      (k : V ≃ₗ[F] V)⁻¹ u ∈ HypBlocks.blockSpace A D.1 ⊔ HypBlocks.blockSpace A E.1 := by
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (mapsTo_blockSpace_of_commute A hp hpF hA t ht hkDinv a ha))
      (Submodule.mem_sup_right (mapsTo_blockSpace_of_commute A hp hpF hA t ht hkEinv b hb))
  obtain ⟨hhfix, hhcomm⟩ := mem_Lsub.mp hh
  have hhD : (h : V ≃ₗ[F] V) * HypBlocks.blockEnd A hp hpF hA t ht D =
      HypBlocks.blockEnd A hp hpF hA t ht D * (h : V ≃ₗ[F] V) :=
    hhcomm _ (Set.mem_insert _ _)
  have hhE : (h : V ≃ₗ[F] V) * HypBlocks.blockEnd A hp hpF hA t ht E =
      HypBlocks.blockEnd A hp hpF hA t ht E * (h : V ≃ₗ[F] V) :=
    hhcomm _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [mem_Lsub]
  refine ⟨?_, ?_⟩
  · intro u hu
    have hku : (k : V ≃ₗ[F] V)⁻¹ u ∈
        HypBlocks.blockSpace A D.1 ⊔ HypBlocks.blockSpace A E.1 := hkUinv u hu
    change ((k : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V) * (k : V ≃ₗ[F] V)⁻¹) u = u
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hhfix _ hku]
    exact (k : V ≃ₗ[F] V).apply_symm_apply u
  · intro s hs
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    have hconjD : Commute ((k : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V) * (k : V ≃ₗ[F] V)⁻¹)
        (HypBlocks.blockEnd A hp hpF hA t ht D) :=
      (show Commute (k : V ≃ₗ[F] V) (HypBlocks.blockEnd A hp hpF hA t ht D) from hkD).mul_left
        (show Commute (h : V ≃ₗ[F] V) (HypBlocks.blockEnd A hp hpF hA t ht D) from hhD)
        |>.mul_left
        (show Commute (k : V ≃ₗ[F] V)⁻¹ (HypBlocks.blockEnd A hp hpF hA t ht D) from
          (show Commute (k : V ≃ₗ[F] V) (HypBlocks.blockEnd A hp hpF hA t ht D) from hkD).inv_left)
    have hconjE : Commute ((k : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V) * (k : V ≃ₗ[F] V)⁻¹)
        (HypBlocks.blockEnd A hp hpF hA t ht E) :=
      (show Commute (k : V ≃ₗ[F] V) (HypBlocks.blockEnd A hp hpF hA t ht E) from hkE).mul_left
        (show Commute (h : V ≃ₗ[F] V) (HypBlocks.blockEnd A hp hpF hA t ht E) from hhE)
        |>.mul_left
        (show Commute (k : V ≃ₗ[F] V)⁻¹ (HypBlocks.blockEnd A hp hpF hA t ht E) from
          (show Commute (k : V ≃ₗ[F] V) (HypBlocks.blockEnd A hp hpF hA t ht E) from hkE).inv_left)
    rcases hs with rfl | rfl
    · exact hconjD.eq
    · exact hconjE.eq


theorem Lsub_le_inf [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hpd : ¬ p ∣ Fintype.card F - 1) {D E : HypBlocks.Hyperplane A p} (hDE : D ≠ E) :
    Lsub A hp hpF hA t ht D E ≤
      Jsub A hp hpF hA t ht D ⊓
        Subgroup.centralizer
          ({blockEndSL A hp hpF hA t ht hpd E} : Set (SpecialLinearGroup F V)) := by
  intro g hg
  obtain ⟨hfix, hcomm⟩ := mem_Lsub.mp hg
  rw [Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [mem_Jsub]
    refine ⟨fun u hu => hfix u (Submodule.mem_sup_left hu), fun s hs => ?_⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hcomm _ (Set.mem_insert _ _)
  · rw [mem_centralizer_blockEndSL_iff]
    exact hcomm _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem card_center_Lsub_dvd [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D E : HypBlocks.Hyperplane A p} (hDE : D ≠ E) :
    Nat.card (Subgroup.center ↥(Lsub A hp hpF hA t ht D E)) ∣ Fintype.card F - 1 := by
  rw [Nat.card_congr (Subgroup.centerCongr (LsubEquiv A hp hpF hA t ht hDE)).toEquiv,
    ← Nat.card_eq_fintype_card]
  exact card_center_specialLinearGroup_dvd (F := F) (V := V)
    (W := HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D) ⊓
      HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht E))

theorem dvd_card_quotient_center_Lsub [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hAdet : A ≤ LinearEquiv.det.ker) (hpd : ¬ p ∣ Fintype.card F - 1)
    {k : ℕ} (hk : Nat.card A = p ^ k) (hk3 : 3 ≤ k)
    {D E : HypBlocks.Hyperplane A p} (hDE : D ≠ E) :
    p ∣ Nat.card (↥(Lsub A hp hpF hA t ht D E) ⧸
      Subgroup.center ↥(Lsub A hp hpF hA t ht D E)) := by
  have hL : p ∣ Nat.card ↥(Lsub A hp hpF hA t ht D E) :=
    dvd_card_Lsub A hp hpF hA t ht hAdet hk hk3 hDE
  have hZ : ¬ p ∣ Nat.card (Subgroup.center ↥(Lsub A hp hpF hA t ht D E)) :=
    fun h => hpd (h.trans (card_center_Lsub_dvd A hp hpF hA t ht hDE))
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center ↥(Lsub A hp hpF hA t ht D E))
  rw [hcard] at hL
  rcases (Nat.Prime.dvd_mul hp).1 hL with h | h
  · exact h
  · exact absurd h hZ

theorem glaPComponent_Jsub [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hAdet : A ≤ LinearEquiv.det.ker) (hpd : ¬ p ∣ Fintype.card F - 1)
    {k : ℕ} (hk : Nat.card A = p ^ k) (hk3 : 3 ≤ k) (D : HypBlocks.Hyperplane A p)
    (hq : CFSG.IsQuasisimple
      (SpecialLinearGroup F ↥(HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D)))) :
    GLAPComponent p
      (Subgroup.centralizer
        ({blockEndSL A hp hpF hA t ht hpd D} : Set (SpecialLinearGroup F V)))
      (Jsub A hp hpF hA t ht D) := by
  haveI : Fintype V := by
    classical
    haveI : Module.Free F V := Module.Free.of_divisionRing F V
    exact Fintype.ofEquiv (Fin (Module.finrank F V) → F)
      (Module.finBasis F V).equivFun.symm.toEquiv
  haveI : Finite (SpecialLinearGroup F V) := inferInstance
  have hle : Jsub A hp hpF hA t ht D ≤
      Subgroup.centralizer
        ({blockEndSL A hp hpF hA t ht hpd D} : Set (SpecialLinearGroup F V)) := by
    intro g hg
    rw [mem_centralizer_blockEndSL_iff]
    exact (mem_Jsub.mp hg).2 _ (Set.mem_singleton _)
  exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp
    (isQuasisimple_Jsub A hp hpF hA t ht D hq)
    (dvd_card_Jsub A hp hpF hA t ht hAdet hk hk3 D) hle
    (normal_Jsub A hp hpF hA t ht hpd D)

theorem glaPLayer_Jsub_inf_centralizer [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hAdet : A ≤ LinearEquiv.det.ker) (hpd : ¬ p ∣ Fintype.card F - 1)
    {k : ℕ} (hk : Nat.card A = p ^ k) (hk3 : 3 ≤ k)
    {D E : HypBlocks.Hyperplane A p} (hDE : D ≠ E)
    (hq : CFSG.IsQuasisimple
      (SpecialLinearGroup F ↥(HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D) ⊓
        HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht E)))) :
    GLAPLayer p
      (Jsub A hp hpF hA t ht D ⊓
        Subgroup.centralizer
          ({blockEndSL A hp hpF hA t ht hpd E} : Set (SpecialLinearGroup F V))) ≠ ⊥ := by
  haveI : Fintype V := by
    classical
    haveI : Module.Free F V := Module.Free.of_divisionRing F V
    exact Fintype.ofEquiv (Fin (Module.finrank F V) → F)
      (Module.finBasis F V).equivFun.symm.toEquiv
  exact glaPLayer_ne_bot_of_normal_quasisimple hp
    (Lsub_le_inf A hp hpF hA t ht hpd hDE)
    (normal_Lsub A hp hpF hA t ht hpd hDE)
    (isQuasisimple_Lsub A hp hpF hA t ht hDE hq)
    (dvd_card_quotient_center_Lsub A hp hpF hA t ht hAdet hpd hk hk3 hDE)

end LinEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F



