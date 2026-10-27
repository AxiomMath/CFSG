module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.C35Bridge
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OrthConcl
public import CFSG.Quasithin.H13.U5ParLineQuot
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieClsA
public import CFSG.Quasithin.Background.Omega4AutOn

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit
  CFSG.Quasithin.H13.U5Par CFSG.Quasithin.H13.F431.Un CFSG.Quasithin.H13.F431.Un.L5
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

private theorem hypProj_injectiveOn_Vsub :
    Function.Injective ((hypProj h 2 1).comp (Vsub h).subtype) := by
  intro a b e
  exact Subtype.ext (eq_of_proj_eq_Vsub a.2 b.2 e)

private noncomputable def eV : ↥(Vsub h) ≃* ↥((Vsub h).map (hypProj h 2 1)) :=
  CFSG.RankThree.PartOne.U5K.equivMapOfInjOn (hypProj h 2 1) (hypProj_injectiveOn_Vsub h)

private theorem eV_apply (v : ↥(Vsub h)) :
    ((eV h v : ↥((Vsub h).map (hypProj h 2 1))) : hypPSU h 2 1) =
      hypProj h 2 1 (v : hypSU h 2 1) := by
  have h := CFSG.RankThree.PartOne.U5K.subtype_comp_equivMapOfInjOn
    (f := hypProj h 2 1) (T := Vsub h) (hypProj_injectiveOn_Vsub h)
  exact DFunLike.congr_fun h v

private noncomputable def yHom : ↥(Vsub h) →* Multiplicative (Matrix (Fin 2) (Fin 2) K) where
  toFun v := Multiplicative.ofAdd (Yof (v : hypSU h 2 1))
  map_one' := by
    rw [Subgroup.coe_one]
    exact congrArg Multiplicative.ofAdd (Yof_one_Vsub (h := h))
  map_mul' v w := by
    rw [Subgroup.coe_mul]
    exact congrArg Multiplicative.ofAdd (Yof_mul v.2 w.2)

private theorem yHom_injective : Function.Injective (yHom h) := by
  intro v w e
  have hY : Yof (v : hypSU h 2 1) = Yof (w : hypSU h 2 1) := by
    simpa [yHom] using congrArg Multiplicative.toAdd e
  exact Subtype.ext (Yof_ext v.2 w.2 (by rw [hY]) (by rw [hY]) (by rw [hY]))

private theorem yHom_image (X : Matrix (Fin 2) (Fin 2) K) :
    (∃ v : ↥(Vsub h), Multiplicative.toAdd (yHom h v) = X) ↔
      X.map (· ^ 2 ^ f) = X.transpose := by
  constructor
  · rintro ⟨v, rfl⟩
    exact (isHerm_iff_map_frob (h := h) (Yof (v : hypSU h 2 1))).1 (herm_Yof v.2)
  · intro hX
    obtain ⟨v, hv, hvm⟩ := exists_mem_Vsub (hK := h) ((isHerm_iff_map_frob (h := h) X).2 hX)
    refine ⟨⟨v, hv⟩, ?_⟩
    change Yof (v : hypSU h 2 1) = X
    rw [Yof_eq hvm]

private theorem yHom_conj {g v w : hypSU h 2 1} (hg : g ∈ Ssub h ⊔ N₁sub h)
    (hv : v ∈ Vsub h) (hw : w ∈ Vsub h) (hconj : w = g * v * g⁻¹) :
    Multiplicative.toAdd (yHom h ⟨w, hw⟩) =
      (blkA (mat g) : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd (yHom h ⟨v, hv⟩) *
        ((blkA (mat g)).map (· ^ 2 ^ f)).transpose := by
  have hgu : g ∈ u5LnStab h := sup_le_u5LnStab h hg
  have hY := Yof_conj_of_mem_u5LnStab (h := h) hgu hv
  rw [← hconj] at hY
  have hmap : (blkA (mat g)).map h.bar = (blkA (mat g)).map (· ^ 2 ^ f) := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, UnitaryFieldData.bar_apply]
  rwa [hmap] at hY

private noncomputable def beta : ↥((Vsub h).map (hypProj h 2 1)) →*
    Multiplicative (Matrix (Fin 2) (Fin 2) K) :=
  (yHom h).comp (eV h).symm.toMonoidHom

private theorem beta_apply (v : ↥(Vsub h)) :
    Multiplicative.toAdd (beta h ⟨hypProj h 2 1 (v : hypSU h 2 1),
      Subgroup.mem_map_of_mem _ v.2⟩) = Yof (v : hypSU h 2 1) := by
  have hev : eV h v = ⟨hypProj h 2 1 (v : hypSU h 2 1),
      Subgroup.mem_map_of_mem _ v.2⟩ :=
    Subtype.ext (eV_apply h v)
  change Multiplicative.toAdd (yHom h ((eV h).symm
    ⟨hypProj h 2 1 (v : hypSU h 2 1), Subgroup.mem_map_of_mem _ v.2⟩)) = _
  rw [← hev, MulEquiv.symm_apply_apply]
  simp [yHom]

private theorem beta_injective : Function.Injective (beta h) :=
  (yHom_injective h).comp (eV h).symm.injective

private theorem beta_image (X : Matrix (Fin 2) (Fin 2) K) :
    (∃ v : ↥((Vsub h).map (hypProj h 2 1)),
      Multiplicative.toAdd (beta h v) = X) ↔ X.map (· ^ 2 ^ f) = X.transpose := by
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨u, rfl⟩ := (eV h).surjective v
    have hβ : beta h (eV h u) = yHom h u := by
      change yHom h ((eV h).symm (eV h u)) = yHom h u
      rw [MulEquiv.symm_apply_apply]
    rw [hβ]
    exact (isHerm_iff_map_frob (h := h) (Yof (u : hypSU h 2 1))).1 (herm_Yof u.2)
  · intro hX
    obtain ⟨u, hu⟩ := (yHom_image h X).2 hX
    refine ⟨eV h u, ?_⟩
    have hβ : beta h (eV h u) = yHom h u := by
      change yHom h ((eV h).symm (eV h u)) = yHom h u
      rw [MulEquiv.symm_apply_apply]
    rw [hβ]
    exact hu

private noncomputable def lineAlpha (hf : 2 ≤ f) :
    ↥(perfectCore (u5LnP h)) →* Matrix.SpecialLinearGroup (Fin 2) K :=
  (lnSL h).comp (perfEquiv h hf).symm.toMonoidHom

private theorem lineAlpha_eq_lnSL (hf : 2 ≤ f) (g : ↥(Ssub h ⊔ N₁sub h)) :
    lineAlpha h hf (perfEquiv h hf g) = lnSL h g := by
  change lnSL h ((perfEquiv h hf).symm (perfEquiv h hf g)) = lnSL h g
  rw [MulEquiv.symm_apply_apply]

private theorem lineAlpha_eq_of_eq (hf : 2 ≤ f) {ℓ : ↥(perfectCore (u5LnP h))}
    {g : ↥(Ssub h ⊔ N₁sub h)} (hg : (ℓ : hypPSU h 2 1) =
      hypProj h 2 1 (g : hypSU h 2 1)) :
    lineAlpha h hf ℓ = lnSL h g := by
  have hfg : perfEquiv h hf g = ℓ := Subtype.ext hg.symm
  rw [← hfg, lineAlpha_eq_lnSL]

private theorem lineAlpha_surjective (hf : 2 ≤ f) :
    Function.Surjective (lineAlpha h hf) := by
  intro A
  obtain ⟨g, hg⟩ := lnSL_surjective h A
  exact ⟨perfEquiv h hf g, by rw [lineAlpha_eq_lnSL, hg]⟩

private theorem lineAlpha_trivial_on_V (hf : 2 ≤ f) {ℓ : ↥(perfectCore (u5LnP h))}
    (hℓ : lineAlpha h hf ℓ = 1) {v : ↥((Vsub h).map (hypProj h 2 1))} :
    (ℓ : hypPSU h 2 1) * v * (ℓ : hypPSU h 2 1)⁻¹ = v := by
  obtain ⟨g, hgP, hgℓ⟩ : ∃ g ∈ Ssub h ⊔ N₁sub h,
      hypProj h 2 1 g = (ℓ : hypPSU h 2 1) := by
    have hmem : (ℓ : hypPSU h 2 1) ∈ (Ssub h ⊔ N₁sub h).map (hypProj h 2 1) := by
      rw [← perfectCore_u5LnP h hf]
      exact ℓ.2
    exact hmem
  have hαg : lineAlpha h hf ℓ = lnSL h ⟨g, hgP⟩ := lineAlpha_eq_of_eq h hf hgℓ.symm
  have hgS : g ∈ Ssub h :=
    (lnSL_eq_one_iff h ⟨g, hgP⟩).1 (by rw [← hαg]; exact hℓ)
  obtain ⟨w, hw, hwv⟩ := v.2
  have hv' : v = ⟨hypProj h 2 1 w, Subgroup.mem_map_of_mem _ hw⟩ := Subtype.ext hwv.symm
  rw [hv']
  have hcomm : g * w = w * g :=
    (commute_Vsub_iff (Ssub_le_Usub hgS)).2 hgS w hw
  rw [← hgℓ]
  calc hypProj h 2 1 g * hypProj h 2 1 w * (hypProj h 2 1 g)⁻¹
      = hypProj h 2 1 (g * w * g⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = hypProj h 2 1 w := by rw [hcomm, mul_inv_cancel_right]

private theorem beta_conj (hf : 2 ≤ f) {ℓ : ↥(perfectCore (u5LnP h))}
    {g : ↥(Ssub h ⊔ N₁sub h)} (hgℓ : (ℓ : hypPSU h 2 1) =
      hypProj h 2 1 (g : hypSU h 2 1))
    {v w : ↥((Vsub h).map (hypProj h 2 1))}
    (hw : (w : hypPSU h 2 1) = (ℓ : hypPSU h 2 1) * v * (ℓ : hypPSU h 2 1)⁻¹) :
    Multiplicative.toAdd (beta h w) =
      ((lineAlpha h hf ℓ : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) *
        Multiplicative.toAdd (beta h v) *
        (((lineAlpha h hf ℓ : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f)).transpose := by
  obtain ⟨v₀, hv₀, hvπ⟩ := v.2
  obtain ⟨w₀, hw₀, hwπ⟩ := w.2
  have hv' : v = ⟨hypProj h 2 1 v₀, Subgroup.mem_map_of_mem _ hv₀⟩ := Subtype.ext hvπ.symm
  have hw' : w = ⟨hypProj h 2 1 w₀, Subgroup.mem_map_of_mem _ hw₀⟩ := Subtype.ext hwπ.symm
  rw [hv', hw']
  have hgu : (g : hypSU h 2 1) ∈ u5LnStab h := sup_le_u5LnStab h g.2
  have hgwV : (g : hypSU h 2 1) * v₀ * (g : hypSU h 2 1)⁻¹ ∈ Vsub h :=
    conj_mem_Vsub_of_mem_u5LnStab (h := h) hgu hv₀
  have hweq : hypProj h 2 1 w₀ = hypProj h 2 1
      ((g : hypSU h 2 1) * v₀ * (g : hypSU h 2 1)⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    simpa [hgℓ, hvπ, hwπ] using hw
  have hconj : w₀ = (g : hypSU h 2 1) * v₀ * (g : hypSU h 2 1)⁻¹ :=
    eq_of_proj_eq_Vsub hw₀ hgwV hweq
  have hY := yHom_conj (h := h) (g := (g : hypSU h 2 1)) g.2 hv₀ hw₀ hconj
  rw [beta_apply h ⟨v₀, hv₀⟩, beta_apply h ⟨w₀, hw₀⟩,
    lineAlpha_eq_of_eq h hf hgℓ, lnSL_coe]
  exact hY

theorem KConfig.u5_line {f : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    {L V : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.hypPSU h 2 1)}
    (hc : KConfig (CFSG.ClassicalGroups.UnitaryFlag.hypPSU h 2 1) L V
      (CFSG.Quasithin.H13.Sec53F.Unit.u5LnP h)) :
    ConclKLeft (CFSG.ClassicalGroups.UnitaryFlag.hypPSU h 2 1) L V
        (CFSG.Quasithin.H13.Sec53F.Unit.u5LnP h) ∧
      CFSG.Quasithin.IsPSL 2 2 (2 * f) (CFSG.Quasithin.ModO2 L) := by
  haveI := h.finite
  haveI : CharP K 2 := h.charP
  haveI := finite_hypPSU_five h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : L = perfectCore (u5LnP h) :=
    hc.eq_perfectCore_of_simple (isSimpleGroup_modO2_perfectCore_u5LnP h hf)
  subst hL
  have hpsl : CFSG.Quasithin.IsPSL 2 2 (2 * f)
      (CFSG.Quasithin.ModO2 (perfectCore (u5LnP h))) :=
    isPSL_modO2_perfectCore_u5LnP h hf
  have hVZ : V ≤ CFSG.Quasithin.centerOf (pCoreOf 2 (perfectCore (u5LnP h))) := by
    rw [CFSG.Quasithin.centerOf]
    exact le_inf hc.le_pCoreOf (Subgroup.le_centralizer_iff.mpr hc.pCoreOf_le)
  have hVW : V ≤ (Vsub h).map (hypProj h 2 1) := by
    rw [pCoreOf_perfectCore_u5LnP h hf, centerOf_S_eq] at hVZ
    simpa [v5Y] using hVZ
  have hV : V = (Vsub h).map (hypProj h 2 1) := by
    let R : Subgroup (hypSU h 2 1) := V.comap (hypProj h 2 1) ⊓ Vsub h
    have hRV : R ≤ Vsub h := inf_le_right
    have hRinv : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K, ∀ r ∈ R,
        lev ((A : Matrix (Fin 2) (Fin 2) K)) (by simp) * r *
          (lev ((A : Matrix (Fin 2) (Fin 2) K)) (by simp))⁻¹ ∈ R := by
      intro A r hr
      have hA : IsUnit ((A : Matrix (Fin 2) (Fin 2) K)).det := by simp
      have hlevN : lev (hK := h) (A : Matrix (Fin 2) (Fin 2) K) hA ∈ N₁sub h :=
        ⟨A, (lev_eq_leviSU A hA).symm⟩
      have hℓL : hypProj h 2 1 (lev (hK := h) (A : Matrix (Fin 2) (Fin 2) K) hA) ∈
          perfectCore (u5LnP h) := by
        rw [perfectCore_u5LnP h hf]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_right hlevN)
      have hpπ : hypProj h 2 1 (lev (hK := h) (A : Matrix (Fin 2) (Fin 2) K) hA) ∈
          Subgroup.normalizer (V : Set (hypPSU h 2 1)) := hc.le_normalizer hℓL
      have hconjV : hypProj h 2 1
          (lev (hK := h) (A : Matrix (Fin 2) (Fin 2) K) hA * r *
            (lev (hK := h) (A : Matrix (Fin 2) (Fin 2) K) hA)⁻¹) ∈ V := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hpπ (hypProj h 2 1 r)).mp hr.1
      refine ⟨Subgroup.mem_comap.mpr hconjV, ?_⟩
      exact conj_mem_Vsub_of_mem_u5LnStab (h := h)
        (lev_mem_u5LnStab (h := h) (A : Matrix (Fin 2) (Fin 2) K) hA) hr.2
    rcases Vsub_irreducible R hRV hRinv with hbot | htop
    · exfalso
      apply hc.ne_bot
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hVW hx
      have hwR : w ∈ R := by
        refine ⟨Subgroup.mem_comap.mpr hx, hw⟩
      rw [hbot, Subgroup.mem_bot] at hwR
      rw [hwR, map_one, Subgroup.mem_bot]
    · apply le_antisymm hVW
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hx
      have hwR : w ∈ R := by
        rw [htop]
        exact hw
      exact hwR.1
  subst hV
  haveI : IsMulCommutative ↥((Vsub h).map (hypProj h 2 1)) := hc.elemAbelian.1
  have hαV : ∀ ℓ : ↥(perfectCore (u5LnP h)), lineAlpha h hf ℓ = 1 →
      ∀ v ∈ (Vsub h).map (hypProj h 2 1),
        (ℓ : hypPSU h 2 1) * v * (ℓ : hypPSU h 2 1)⁻¹ = v := by
    intro ℓ hℓ v hv
    exact lineAlpha_trivial_on_V h hf hℓ (v := ⟨v, hv⟩)
  have hβeq : ∀ (ℓ : ↥(perfectCore (u5LnP h)))
      (v w : ↥((Vsub h).map (hypProj h 2 1))),
      (w : hypPSU h 2 1) = ℓ * v * ℓ⁻¹ →
      Multiplicative.toAdd (beta h w) =
        ((lineAlpha h hf ℓ : Matrix.SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) *
          Multiplicative.toAdd (beta h v) *
          (((lineAlpha h hf ℓ : Matrix.SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f)).transpose := by
    intro ℓ v w hw
    obtain ⟨g, hgP, hgℓ⟩ : ∃ g ∈ Ssub h ⊔ N₁sub h,
        hypProj h 2 1 g = (ℓ : hypPSU h 2 1) := by
      have hmem : (ℓ : hypPSU h 2 1) ∈ (Ssub h ⊔ N₁sub h).map (hypProj h 2 1) := by
        rw [← perfectCore_u5LnP h hf]
        exact ℓ.2
      exact hmem
    exact beta_conj h hf (g := ⟨g, hgP⟩) hgℓ.symm hw
  have hO : BinaryOrthogonalFour (V := ↥((Vsub h).map (hypProj h 2 1)))
      (autOn (perfectCore (u5LnP h)) ((Vsub h).map (hypProj h 2 1))) ⊤ ⊥ f :=
    CFSG.Quasithin.binaryOrthogonalFour_autOn (m := f) hc.le_normalizer h.card
      (lineAlpha h hf) (lineAlpha_surjective h hf) hαV (beta h) (beta_injective h)
      (beta_image h) hβeq
  exact ⟨conclKLeft_of_binaryOrthogonalFour (m := f) (by omega) hpsl hO, hpsl⟩

end CFSG.SectionRank.QTK.Insp443

end
