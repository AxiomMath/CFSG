module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.GH74.Defs
public import CFSG.Open.Catalog

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] [Finite Γ₁] [Finite Γ₂] {f : Γ₁ →* Γ₂}

theorem isElemAbelian_map (hf : Function.Injective f) (p : ℕ) (E : Subgroup Γ₁) :
    IsElemAbelian p (E.map f) ↔ IsElemAbelian p E := by
  constructor
  · intro h
    haveI : IsMulCommutative (E.map f) := h.1
    refine ⟨IsMulCommutative.of_setLike_mul_comm ?_, ?_⟩
    · intro a ha b hb
      apply hf
      rw [map_mul, map_mul]
      exact setLike_mul_comm (s := E.map f) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    · intro x hx
      apply hf
      simpa using h.2 (f x) (show f x ∈ E.map f from ⟨x, hx, rfl⟩)
  · intro h
    haveI : IsMulCommutative E := h.1
    refine ⟨inferInstance, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simpa using congrArg f (h.2 x hx)

private lemma isElementaryAbelian_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (p : ℕ)
    (e : X ≃* Y) (h : IsElementaryAbelian p X) : IsElementaryAbelian p Y where
  toIsMulCommutative := ⟨⟨fun a b => by
    have := h.toIsMulCommutative
    apply e.symm.injective
    rw [map_mul, map_mul, mul_comm' (e.symm a)]⟩⟩
  exponent_dvd_p := Monoid.exponent_eq_of_mulEquiv e ▸ h.exponent_dvd_p

private lemma pRank_congr_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ) :
    pRank p X = pRank p Y := by
  unfold pRank
  congr 1
  ext r
  constructor
  · rintro ⟨A, hA, hc⟩
    exact ⟨A.map e.toMonoidHom,
      isElementaryAbelian_of_mulEquiv p (A.equivMapOfInjective e.toMonoidHom e.injective) hA,
      by rw [Subgroup.card_map_of_injective e.injective, hc]⟩
  · rintro ⟨A, hA, hc⟩
    exact ⟨A.map e.symm.toMonoidHom,
      isElementaryAbelian_of_mulEquiv p
        (A.equivMapOfInjective e.symm.toMonoidHom e.symm.injective) hA,
      by rw [Subgroup.card_map_of_injective e.symm.injective, hc]⟩

theorem pRank_map (hf : Function.Injective f) (p : ℕ) (V : Subgroup Γ₁) :
    pRank p (V.map f) = pRank p V :=
  (pRank_congr_of_mulEquiv (Subgroup.equivMapOfInjective V f hf) p).symm

private lemma map_upperCentralSeries_equiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (n : ℕ) :
    (Subgroup.upperCentralSeries H n).map (e : H →* K) = Subgroup.upperCentralSeries K n := by
  rw [← Subgroup.comap_upperCentralSeries (G := K) e n]
  exact Subgroup.map_comap_eq_self_of_surjective e.surjective _

theorem zSeries_map (hf : Function.Injective f) (n : ℕ) (T : Subgroup Γ₁) :
    zSeries n (T.map f) = (zSeries n T).map f := by
  let e := Subgroup.equivMapOfInjective T f hf
  have he : (T.map f).subtype.comp (e : ↥T →* ↥(T.map f)) = f.comp T.subtype := by
    ext x
    exact Subgroup.coe_equivMapOfInjective_apply T f hf x
  calc zSeries n (T.map f)
      = (Subgroup.upperCentralSeries ↥(T.map f) n).map (T.map f).subtype := rfl
    _ = ((Subgroup.upperCentralSeries ↥T n).map (e : ↥T →* ↥(T.map f))).map
          (T.map f).subtype := by rw [map_upperCentralSeries_equiv e n]
    _ = (Subgroup.upperCentralSeries ↥T n).map
          ((T.map f).subtype.comp (e : ↥T →* ↥(T.map f))) := by rw [Subgroup.map_map]
    _ = (Subgroup.upperCentralSeries ↥T n).map (f.comp T.subtype) := by rw [he]
    _ = ((Subgroup.upperCentralSeries ↥T n).map T.subtype).map f := by rw [Subgroup.map_map]
    _ = (zSeries n T).map f := rfl

theorem omega1_map (hf : Function.Injective f) (T : Subgroup Γ₁) :
    omega1 (T.map f) = (omega1 T).map f := by
  rw [omega1, omega1, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, hy2⟩
    obtain ⟨x, hxT, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, ⟨hxT, hf (by simpa using hy2)⟩, rfl⟩
  · rintro ⟨x, ⟨hxT, hx2⟩, rfl⟩
    exact ⟨⟨x, hxT, rfl⟩, by simpa using congrArg f hx2⟩

theorem thompsonSubgroup_map (hf : Function.Injective f) (T : Subgroup Γ₁) :
    thompsonSubgroup (T.map f) = (thompsonSubgroup T).map f := by
  show ambientMaxCardThompson (T.map f) = (ambientMaxCardThompson T).map f
  exact (CFSG.map_ambientMaxCardThompson_of_injective f T (hf.comp T.subtype_injective)).symm

private def IsMaxAb (T U : Subgroup Γ₁) : Prop :=
  U ≤ T ∧ IsMulCommutative U ∧
    ∀ V : Subgroup Γ₁, V ≤ T → IsMulCommutative V → pRank 2 V ≤ pRank 2 U

private lemma thompsonRank_eq_sSup (T : Subgroup Γ₁) :
    thompsonRank T = sSup {U : Subgroup Γ₁ | IsMaxAb T U} := by
  rw [thompsonRank]
  apply le_antisymm
  · exact iSup_le fun U => iSup_le fun hU => iSup_le fun hc => iSup_le fun hm =>
      le_sSup ⟨hU, hc, hm⟩
  · exact sSup_le fun U hU => le_iSup_of_le U (le_iSup_of_le hU.1 (le_iSup_of_le hU.2.1
      (le_iSup_of_le hU.2.2 le_rfl)))

private lemma isMaxAb_map (hf : Function.Injective f) {T U : Subgroup Γ₁} (h : IsMaxAb T U) :
    IsMaxAb (T.map f) (U.map f) := by
  refine ⟨Subgroup.map_mono h.1, ?_, ?_⟩
  · haveI : IsMulCommutative U := h.2.1
    exact inferInstance
  · intro V' hV'T hV'c
    have hV'eq : (V'.comap f).map f = V' :=
      Subgroup.map_comap_eq_self (le_trans hV'T (Subgroup.map_le_range f T))
    have hVle : V'.comap f ≤ T := by
      rw [← Subgroup.comap_map_eq_self_of_injective hf T]
      exact Subgroup.comap_mono hV'T
    have hVc : IsMulCommutative (V'.comap f) := by
      haveI : IsMulCommutative V' := hV'c
      exact Subgroup.comap_injective_isMulCommutative V' hf
    calc pRank 2 V' = pRank 2 ((V'.comap f).map f) := by rw [hV'eq]
      _ = pRank 2 (V'.comap f) := pRank_map hf 2 _
      _ ≤ pRank 2 U := h.2.2 _ hVle hVc
      _ = pRank 2 (U.map f) := (pRank_map hf 2 U).symm

private lemma isMaxAb_comap (hf : Function.Injective f) {T : Subgroup Γ₁} {U' : Subgroup Γ₂}
    (h : IsMaxAb (T.map f) U') : IsMaxAb T (U'.comap f) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Subgroup.comap_map_eq_self_of_injective hf T]
    exact Subgroup.comap_mono h.1
  · haveI : IsMulCommutative U' := h.2.1
    exact Subgroup.comap_injective_isMulCommutative U' hf
  · intro V hVT hVc
    have hU'eq : (U'.comap f).map f = U' :=
      Subgroup.map_comap_eq_self (le_trans h.1 (Subgroup.map_le_range f T))
    have hVc' : IsMulCommutative (V.map f) := by
      haveI : IsMulCommutative V := hVc
      exact inferInstance
    calc pRank 2 V = pRank 2 (V.map f) := (pRank_map hf 2 V).symm
      _ ≤ pRank 2 U' := h.2.2 _ (Subgroup.map_mono hVT) hVc'
      _ = pRank 2 ((U'.comap f).map f) := by rw [hU'eq]
      _ = pRank 2 (U'.comap f) := pRank_map hf 2 _

theorem thompsonRank_map (hf : Function.Injective f) (T : Subgroup Γ₁) :
    thompsonRank (T.map f) = (thompsonRank T).map f := by
  apply le_antisymm
  · rw [thompsonRank_eq_sSup (T.map f), thompsonRank_eq_sSup T]
    refine sSup_le fun U' hU' => ?_
    rw [← Subgroup.map_comap_eq_self (le_trans hU'.1 (Subgroup.map_le_range f T))]
    exact Subgroup.map_mono (le_sSup (isMaxAb_comap hf hU'))
  · rw [thompsonRank_eq_sSup T, sSup_eq_iSup', Subgroup.map_iSup]
    refine iSup_le fun U => ?_
    rw [thompsonRank_eq_sSup (T.map f)]
    exact le_sSup (isMaxAb_map hf U.2)

theorem maxElemAbelian_map (hf : Function.Injective f) (T : Subgroup Γ₁) :
    maxElemAbelian (T.map f) = Subgroup.map f '' maxElemAbelian T := by
  ext Y
  constructor
  · intro hY
    have hYeq : (Y.comap f).map f = Y :=
      Subgroup.map_comap_eq_self (le_trans hY.1 (Subgroup.map_le_range f T))
    refine ⟨Y.comap f, ⟨?_, ?_, ?_⟩, hYeq⟩
    · rw [← Subgroup.comap_map_eq_self_of_injective hf T]
      exact Subgroup.comap_mono hY.1
    · exact (isElemAbelian_map hf 2 (Y.comap f)).mp (hYeq.symm ▸ hY.2.1)
    · intro Y' hY'le hY'T hY'c
      have h := hY.2.2 (Y'.map f) (hYeq ▸ Subgroup.map_mono hY'le)
        (Subgroup.map_mono hY'T) ((isElemAbelian_map hf 2 Y').mpr hY'c)
      exact Subgroup.map_injective hf (h.trans hYeq.symm)
  · rintro ⟨Y₁, hY₁, rfl⟩
    refine ⟨Subgroup.map_mono hY₁.1, (isElemAbelian_map hf 2 Y₁).mpr hY₁.2.1, ?_⟩
    intro Y' hle hY'T hY'c
    have hY'eq : (Y'.comap f).map f = Y' :=
      Subgroup.map_comap_eq_self (le_trans hY'T (Subgroup.map_le_range f T))
    have hY'T' : Y'.comap f ≤ T := by
      rw [← Subgroup.comap_map_eq_self_of_injective hf T]
      exact Subgroup.comap_mono hY'T
    have hY'c' : IsElemAbelian 2 (Y'.comap f) :=
      (isElemAbelian_map hf 2 (Y'.comap f)).mp (hY'eq.symm ▸ hY'c)
    have hY₁le : Y₁ ≤ Y'.comap f :=
      (Subgroup.map_le_map_iff_of_injective hf).mp (by rw [hY'eq]; exact hle)
    have h := hY₁.2.2 (Y'.comap f) hY₁le hY'T' hY'c'
    rw [← hY'eq, h]

private lemma sectionalTwoRankLE_equiv_forward {X X' : Type} [Group X] [Group X']
    (e : X ≃* X') {r : ℕ} (h : GH74.SectionalTwoRankLE X r) :
    GH74.SectionalTwoRankLE X' r := by
  intro P' hP'
  have hP : IsPGroup 2 (P'.comap e.toMonoidHom) :=
    hP'.comap_of_injective e.toMonoidHom e.injective
  obtain ⟨s, hsc, hcl⟩ := h (P'.comap e.toMonoidHom) hP
  refine ⟨s.map e.toEmbedding, ?_, ?_⟩
  · rw [Finset.card_map]; exact hsc
  · calc Subgroup.closure (↑(s.map e.toEmbedding) : Set X')
        = Subgroup.closure (e.toMonoidHom '' (↑s : Set X)) := by
            congr 1
            ext y
            simp [Finset.mem_map]
      _ = (Subgroup.closure (↑s : Set X)).map e.toMonoidHom :=
            (MonoidHom.map_closure e.toMonoidHom (↑s : Set X)).symm
      _ = (P'.comap e.toMonoidHom).map e.toMonoidHom := by rw [hcl]
      _ = P' := Subgroup.map_comap_eq_self_of_surjective e.surjective P'

theorem sectionalTwoRank_equiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X') :
    GH74.sectionalTwoRank X = GH74.sectionalTwoRank X' := by
  unfold GH74.sectionalTwoRank
  congr 1
  ext r
  exact ⟨sectionalTwoRankLE_equiv_forward e, sectionalTwoRankLE_equiv_forward e.symm⟩

theorem sectionalTwoRank_map (hf : Function.Injective f) (T : Subgroup Γ₁) :
    GH74.sectionalTwoRank ↥(T.map f) = GH74.sectionalTwoRank ↥T :=
  (sectionalTwoRank_equiv (Subgroup.equivMapOfInjective T f hf)).symm

end CFSG.OddStandard.HigherRank.YamadaG23
