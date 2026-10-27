module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15A3ActionK
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15A3Instantiate
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15NoXBlockBorel

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.C1
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN
open CFSG.HardMathSupport.Curtis.Proving
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem toStar_out_eq {T : Subgroup X} (q : X ⧸ gnC T) : toStar T q.out = q := by
  simpa only [toStar, QuotientGroup.mk'_apply] using Quotient.out_eq' q

theorem toStar_out_mem {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (l : ↥Ls) :
    toStar T ((l : X ⧸ gnC T).out) ∈ Ls := by
  rw [toStar_out_eq]
  exact l.2

theorem toStar_mem_Ls_of_mem_gnImg_le_center {T : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {K : Subgroup X}
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    {x : X} (hx : x ∈ K) : toStar T x ∈ Ls :=
  (Subgroup.map_subtype_le (Subgroup.center ↥Ls))
    (hKcen (Subgroup.mem_map_of_mem (toStar T) hx))

theorem toStar_mem_center_of_mem_gnImg_le_center {T : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {K : Subgroup X}
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    {x : X} (hx : x ∈ K) :
    (⟨toStar T x, toStar_mem_Ls_of_mem_gnImg_le_center hKcen hx⟩ : ↥Ls) ∈
      Subgroup.center ↥Ls := by
  obtain ⟨c, hc, hcval⟩ := Subgroup.mem_map.mp
    (hKcen (Subgroup.mem_map_of_mem (toStar T) hx))
  have hceq : (⟨toStar T x,
      toStar_mem_Ls_of_mem_gnImg_le_center hKcen hx⟩ : ↥Ls) = c := by
    apply Subtype.ext
    exact hcval.symm
  rwa [hceq]

theorem conj_mem_sup_gnC_of_toStar_mem {T : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {K : Subgroup X}
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    {x k : X} (hx : toStar T x ∈ Ls) (hk : k ∈ K) :
    x * k * x⁻¹ ∈ K ⊔ gnC T := by
  have hkcenter := toStar_mem_center_of_mem_gnImg_le_center hKcen hk
  have hcomm_sub : (⟨toStar T x, hx⟩ : ↥Ls) * ⟨toStar T k,
      toStar_mem_Ls_of_mem_gnImg_le_center hKcen hk⟩ =
      ⟨toStar T k, toStar_mem_Ls_of_mem_gnImg_le_center hKcen hk⟩ *
        ⟨toStar T x, hx⟩ :=
    Subgroup.mem_center_iff.mp hkcenter _
  have hcomm : toStar T x * toStar T k = toStar T k * toStar T x :=
    congrArg (fun z : ↥Ls => (z : X ⧸ gnC T)) hcomm_sub
  have hone : toStar T (x * k * x⁻¹ * k⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hc : x * k * x⁻¹ * k⁻¹ ∈ gnC T :=
    (QuotientGroup.eq_one_iff _).mp hone
  have e : x * k * x⁻¹ = (x * k * x⁻¹ * k⁻¹) * k := by group
  rw [e]
  exact (K ⊔ gnC T).mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hk)

theorem map_conj_K_le_sup_gnC {T : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {K : Subgroup X}
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    {x : X} (hx : toStar T x ∈ Ls) :
    K.map (MulAut.conj x).toMonoidHom ≤ K ⊔ gnC T := by
  rintro y ⟨k, hk, rfl⟩
  simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
    conj_mem_sup_gnC_of_toStar_mem hKcen hx hk

theorem map_conj_blockU_le {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {H K : Subgroup X} (hX : GNSetting X T)
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T)
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    {x : X} (hx : toStar T x ∈ Ls) :
    (blockU K).map (MulAut.conj x).toMonoidHom ≤ blockU K := by
  haveI : (gnV T).Normal := normal_gnV T
  have hUeq : ⁅gnV T, K⁆ = blockU K := commutator_gnV_eq_blockU_q hX hQH hK hKC
  rw [← hUeq]
  calc
    ⁅gnV T, K⁆.map (MulAut.conj x).toMonoidHom =
        ⁅(gnV T).map (MulAut.conj x).toMonoidHom,
          K.map (MulAut.conj x).toMonoidHom⁆ :=
      Subgroup.map_commutator (H₁ := gnV T) (H₂ := K)
        (f := (MulAut.conj x).toMonoidHom)
    _ = ⁅gnV T, K.map (MulAut.conj x).toMonoidHom⁆ := by
      have hVmap : (gnV T).map (MulAut.conj x).toMonoidHom = gnV T := by
        simpa [MulEquiv.coe_toMonoidHom] using
          Subgroup.Normal.map_conj_eq (H := gnV T) x
      rw [hVmap]
    _ ≤ ⁅gnV T, K ⊔ gnC T⁆ :=
      Subgroup.commutator_mono le_rfl (map_conj_K_le_sup_gnC hKcen hx)
    _ = ⁅gnV T, K⁆ ⊔ ⁅gnV T, gnC T⁆ := Subgroup.commutator_sup_left _ _ _
    _ = ⁅gnV T, K⁆ := by
      have hVC : ⁅gnV T, gnC T⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
        exact le_rfl
      rw [hVC, sup_bot_eq]

theorem map_conj_blockU_eq {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {H K : Subgroup X} (hX : GNSetting X T)
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T)
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    {x : X} (hx : toStar T x ∈ Ls) :
    (blockU K).map (MulAut.conj x).toMonoidHom = blockU K := by
  refine le_antisymm (map_conj_blockU_le hX hQH hK hKC hKcen hx) ?_
  intro u hu
  have hxinv : toStar T x⁻¹ ∈ Ls := Ls.inv_mem hx
  have hinv := map_conj_blockU_le hX hQH hK hKC hKcen hxinv
  have hmem : (MulAut.conj x⁻¹).toMonoidHom u ∈ blockU K :=
    hinv (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
  refine Subgroup.mem_map.mpr ⟨(MulAut.conj x⁻¹).toMonoidHom u, hmem, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem map_conj_blockZ_le {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {H K : Subgroup X} (hX : GNSetting X T)
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T)
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    {x : X} (hx : toStar T x ∈ Ls) :
    (blockZ K).map (MulAut.conj x).toMonoidHom ≤ blockZ K := by
  rintro w ⟨z, hz, rfl⟩
  rw [blockZ] at hz ⊢
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact map_conj_blockU_le hX hQH hK hKC hKcen hx
      (Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hz.1)
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkinv : x⁻¹ * k * x ∈ K ⊔ gnC T := by
      simpa only [inv_inv] using
        conj_mem_sup_gnC_of_toStar_mem hKcen (Ls.inv_mem hx) hk
    obtain ⟨k₀, hk₀, c, hc, hkc⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := K) (t := gnC T)).mp hkinv
    have hzV : z ∈ gnV T := blockU_le_gnV_q hX hQH hK hKC hz.1
    have hzk : z * k₀ = k₀ * z :=
      (Subgroup.mem_centralizer_iff.mp hz.2 k₀ hk₀).symm
    have hzc : z * c = c * z :=
      Subgroup.mem_centralizer_iff.mp hc z hzV
    have hzcomm : z * (x⁻¹ * k * x) = (x⁻¹ * k * x) * z := by
      calc
        z * (x⁻¹ * k * x) = z * (k₀ * c) := by rw [hkc]
        _ = (z * k₀) * c := by group
        _ = (k₀ * z) * c := by rw [hzk]
        _ = k₀ * (z * c) := by group
        _ = k₀ * (c * z) := by rw [hzc]
        _ = (k₀ * c) * z := by group
        _ = (x⁻¹ * k * x) * z := by rw [hkc]
    calc
      k * (MulAut.conj x z) = x * ((x⁻¹ * k * x) * z) * x⁻¹ := by
        simp only [MulAut.conj_apply]
        group
      _ = x * (z * (x⁻¹ * k * x)) * x⁻¹ := by rw [← hzcomm]
      _ = (MulAut.conj x z) * k := by
        simp only [MulAut.conj_apply]
        group

@[expose] noncomputable def conjEndUZBy (K : Subgroup X) {x : X}
    (hxU : x ∈ Subgroup.normalizer (blockU K : Set X))
    (hxZ : (blockZ K).map (MulAut.conj x).toMonoidHom ≤ blockZ K) :
    UZ K →* UZ K :=
  QuotientGroup.map ((blockZ K).subgroupOf (blockU K))
    ((blockZ K).subgroupOf (blockU K))
    (CFSG.SL2MinimalFaithful.conjAut hxU).toMonoidHom
    (fun z hz => by
      have hmem : ((CFSG.SL2MinimalFaithful.conjAut hxU z : blockU K) : X) ∈
          (blockZ K).map (MulAut.conj x) := by
        refine Subgroup.mem_map.mpr ⟨(z : X), hz, ?_⟩
        rfl
      exact hxZ hmem)

@[simp] theorem conjEndUZBy_mk (K : Subgroup X) {x : X}
    (hxU : x ∈ Subgroup.normalizer (blockU K : Set X))
    (hxZ : (blockZ K).map (MulAut.conj x).toMonoidHom ≤ blockZ K) (u : blockU K) :
    conjEndUZBy K hxU hxZ (QuotientGroup.mk u) =
      QuotientGroup.mk ((CFSG.SL2MinimalFaithful.conjAut hxU) u) :=
  rfl

@[expose] noncomputable def conjAutUZBy (K : Subgroup X) {x : X}
    (hxU : x ∈ Subgroup.normalizer (blockU K : Set X))
    (hxZ : (blockZ K).map (MulAut.conj x).toMonoidHom ≤ blockZ K)
    (hxUinv : x⁻¹ ∈ Subgroup.normalizer (blockU K : Set X))
    (hxZinv : (blockZ K).map (MulAut.conj x⁻¹).toMonoidHom ≤ blockZ K) :
    MulAut (UZ K) where
  toFun := conjEndUZBy K hxU hxZ
  invFun := conjEndUZBy K hxUinv hxZinv
  left_inv q := by
    induction q using QuotientGroup.induction_on with
    | H u =>
      change conjEndUZBy K hxUinv hxZinv
        (conjEndUZBy K hxU hxZ (QuotientGroup.mk u)) = QuotientGroup.mk u
      rw [conjEndUZBy_mk, conjEndUZBy_mk]
      have h : (CFSG.SL2MinimalFaithful.conjAut hxUinv)
          ((CFSG.SL2MinimalFaithful.conjAut hxU) u) = u := by
        apply Subtype.ext
        rw [CFSG.SL2MinimalFaithful.conjAut_apply,
          CFSG.SL2MinimalFaithful.conjAut_apply]
        group
      rw [h]
  right_inv q := by
    induction q using QuotientGroup.induction_on with
    | H u =>
      change conjEndUZBy K hxU hxZ
        (conjEndUZBy K hxUinv hxZinv (QuotientGroup.mk u)) = QuotientGroup.mk u
      rw [conjEndUZBy_mk, conjEndUZBy_mk]
      have h : (CFSG.SL2MinimalFaithful.conjAut hxU)
          ((CFSG.SL2MinimalFaithful.conjAut hxUinv) u) = u := by
        apply Subtype.ext
        rw [CFSG.SL2MinimalFaithful.conjAut_apply,
          CFSG.SL2MinimalFaithful.conjAut_apply]
        group
      rw [h]
  map_mul' := map_mul _

@[simp] theorem conjAutUZBy_apply_mk (K : Subgroup X) {x : X}
    (hxU : x ∈ Subgroup.normalizer (blockU K : Set X))
    (hxZ : (blockZ K).map (MulAut.conj x).toMonoidHom ≤ blockZ K)
    (hxUinv : x⁻¹ ∈ Subgroup.normalizer (blockU K : Set X))
    (hxZinv : (blockZ K).map (MulAut.conj x⁻¹).toMonoidHom ≤ blockZ K) (u : blockU K) :
    conjAutUZBy K hxU hxZ hxUinv hxZinv (QuotientGroup.mk u) =
      QuotientGroup.mk ((CFSG.SL2MinimalFaithful.conjAut hxU) u) :=
  conjEndUZBy_mk K hxU hxZ u

noncomputable abbrev componentConjAut {T : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {H K : Subgroup X}
    (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K) (hKC : ¬ K ≤ gnC T)
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    (x : X) (hx : toStar T x ∈ Ls) : MulAut (UZ K) :=
  conjAutUZBy K
    (by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      simpa [MulEquiv.coe_toMonoidHom] using
        map_conj_blockU_eq hX hQH hK hKC hKcen hx)
    (map_conj_blockZ_le hX hQH hK hKC hKcen hx)
    (by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      simpa [MulEquiv.coe_toMonoidHom] using
        map_conj_blockU_eq hX hQH hK hKC hKcen (Ls.inv_mem hx))
    (map_conj_blockZ_le hX hQH hK hKC hKcen (Ls.inv_mem hx))

theorem componentConjAut_eq_of_toStar_eq {T : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {H K : Subgroup X} (hX : GNSetting X T)
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T)
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    {x y : X} (hx : toStar T x ∈ Ls) (hy : toStar T y ∈ Ls)
    (hxy : toStar T x = toStar T y) :
    componentConjAut hX hQH hK hKC hKcen x hx =
      componentConjAut hX hQH hK hKC hKcen y hy := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H u =>
    simp only [componentConjAut, conjAutUZBy_apply_mk]
    congr 1
    apply Subtype.ext
    have hc : x * y⁻¹ ∈ gnC T := by
      apply (QuotientGroup.eq_one_iff _).mp
      change toStar T (x * y⁻¹) = 1
      rw [map_mul, map_inv, hxy]
      group
    have hcV : (u : X) ∈ gnV T := blockU_le_gnV_q hX hQH hK hKC u.2
    have hzc : x * y⁻¹ * (u : X) = (u : X) * (x * y⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hc (u : X) hcV).symm
    have hyN : y ∈ Subgroup.normalizer (blockU K : Set X) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      simpa [MulEquiv.coe_toMonoidHom] using
        map_conj_blockU_eq hX hQH hK hKC hKcen hy
    have hyuU : (MulAut.conj y) u ∈ blockU K :=
      (Subgroup.mem_normalizer_iff.mp hyN u).mp u.2
    have hyuV : ((MulAut.conj y) u : X) ∈ gnV T :=
      blockU_le_gnV_q hX hQH hK hKC hyuU
    have hcyu : x * y⁻¹ * (y * (u : X) * y⁻¹) =
        (y * (u : X) * y⁻¹) * (x * y⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hc _ hyuV).symm
    rw [CFSG.SL2MinimalFaithful.conjAut_apply,
      CFSG.SL2MinimalFaithful.conjAut_apply]
    calc
      x * (u : X) * x⁻¹ =
          (x * y⁻¹) * (y * (u : X) * y⁻¹) * (x * y⁻¹)⁻¹ := by group
      _ = y * (u : X) * y⁻¹ := by rw [hcyu]; group

theorem componentConjAut_one {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {H K : Subgroup X} (hX : GNSetting X T)
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T)
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    (hx : toStar T (1 : X) ∈ Ls) :
    componentConjAut hX hQH hK hKC hKcen (1 : X) hx = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H u =>
    simp only [componentConjAut, conjAutUZBy_apply_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [CFSG.SL2MinimalFaithful.conjAut_apply]
    group

theorem componentConjAut_mul {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {H K : Subgroup X} (hX : GNSetting X T)
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T)
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    (x y : X) (hx : toStar T x ∈ Ls) (hy : toStar T y ∈ Ls)
    (hxy : toStar T (x * y) ∈ Ls) :
    componentConjAut hX hQH hK hKC hKcen (x * y) hxy =
      componentConjAut hX hQH hK hKC hKcen x hx *
        componentConjAut hX hQH hK hKC hKcen y hy := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H u =>
    simp only [componentConjAut, conjAutUZBy_apply_mk, MulAut.mul_apply]
    congr 1
    apply Subtype.ext
    rw [CFSG.SL2MinimalFaithful.conjAut_apply,
      CFSG.SL2MinimalFaithful.conjAut_apply,
      CFSG.SL2MinimalFaithful.conjAut_apply]
    group

theorem componentConjAut_eq_conjAction_UZ {T : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {H K : Subgroup X} (hX : GNSetting X T)
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T)
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    (k : K) :
    componentConjAut hX hQH hK hKC hKcen (k : X)
        (toStar_mem_Ls_of_mem_gnImg_le_center hKcen k.2) =
      conjAction_UZ K k := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H u =>
    simp only [componentConjAut, conjAutUZBy_apply_mk, conjAction_UZ_mk]
    rfl

@[expose] noncomputable def component_action_UZ {T : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {H K : Subgroup X}
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤)
    (hKle : K ≤ borelPre T Ls) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K) (hKC : ¬ K ≤ gnC T)
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype) :
    ↥Ls →* MulAut (UZ K) where
  toFun l :=
    componentConjAut hX hQH hK hKC hKcen
      (l : X ⧸ gnC T).out (toStar_out_mem l)
  map_one' := by
    have h1 : componentConjAut hX hQH hK hKC hKcen
        ((1 : ↥Ls) : X ⧸ gnC T).out (toStar_out_mem (1 : ↥Ls)) =
      componentConjAut hX hQH hK hKC hKcen (1 : X)
        (by rw [map_one]; exact Ls.one_mem) :=
      componentConjAut_eq_of_toStar_eq hX hQH hK hKC hKcen _ _
        (by rw [toStar_out_eq, map_one]; rfl)
    rw [componentConjAut_one hX hQH hK hKC hKcen
      (by rw [map_one]; exact Ls.one_mem)] at h1
    exact h1
  map_mul' l l' := by
    have hxy : toStar T ((l : X ⧸ gnC T).out * (l' : X ⧸ gnC T).out) ∈ Ls := by
      rw [map_mul, toStar_out_eq, toStar_out_eq]
      exact Ls.mul_mem l.2 l'.2
    have h1 : componentConjAut hX hQH hK hKC hKcen
        (((l * l' : ↥Ls) : X ⧸ gnC T).out) (toStar_out_mem (l * l')) =
      componentConjAut hX hQH hK hKC hKcen
        ((l : X ⧸ gnC T).out * (l' : X ⧸ gnC T).out) hxy :=
      componentConjAut_eq_of_toStar_eq hX hQH hK hKC hKcen _ _ (by
        rw [toStar_out_eq, map_mul, toStar_out_eq, toStar_out_eq]; rfl)
    have h2 := componentConjAut_mul hX hQH hK hKC hKcen
      ((l : X ⧸ gnC T).out) ((l' : X ⧸ gnC T).out)
      (toStar_out_mem l) (toStar_out_mem l') hxy
    exact h1.trans h2

theorem conjAction_UZ_eq_component_action {T : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {H K : Subgroup X}
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤)
    (hKle : K ≤ borelPre T Ls) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K) (hKC : ¬ K ≤ gnC T)
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    (k : K) :
    conjAction_UZ K k =
      component_action_UZ hX hLs hKle hQH hK hKC hKcen
        (exists_map_to_component hKcen k) := by
  have hkLs : toStar T (k : X) ∈ Ls :=
    toStar_mem_Ls_of_mem_gnImg_le_center hKcen k.2
  have hclass : toStar T
      ((exists_map_to_component hKcen k : ↥Ls) : X ⧸ gnC T).out =
      toStar T (k : X) := by
    rw [toStar_out_eq, exists_map_to_component_apply]
    rfl
  have h1 : componentConjAut hX hQH hK hKC hKcen
      ((exists_map_to_component hKcen k : ↥Ls) : X ⧸ gnC T).out
      (toStar_out_mem (exists_map_to_component hKcen k)) =
    componentConjAut hX hQH hK hKC hKcen (k : X) hkLs :=
    componentConjAut_eq_of_toStar_eq hX hQH hK hKC hKcen _ _ hclass
  symm
  unfold component_action_UZ
  change componentConjAut hX hQH hK hKC hKcen
      ((exists_map_to_component hKcen k : ↥Ls) : X ⧸ gnC T).out
      (toStar_out_mem (exists_map_to_component hKcen k)) =
    conjAction_UZ K k
  rw [h1, componentConjAut_eq_conjAction_UZ]

theorem false_of_isAltType_of_component_action {T : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {H K : Subgroup X}
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤)
    (hKle : K ≤ borelPre T Ls) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K) (hKC : ¬ K ≤ gnC T)
    (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    (hAlt : IsAltType K 3) : False :=
  a3_final hAlt (component_perfect hLs)
    (component_action_UZ hX hLs hKle hQH hK hKC hKcen)
    (exists_map_to_component hKcen)
    (MonoidHom.ext fun k => by
      simpa using conjAction_UZ_eq_component_action hX hLs hKle hQH hK hKC hKcen k)

end CFSG.LocalAnalysis.RankThreeUC.S15

end
