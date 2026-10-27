module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F8Cj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F8Ct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F8Sy
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F8Cu
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F9Na
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F9Nb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F5Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F2Str

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84f_NK_of (F : Sec8T84Base) (hI : Asc82Step84IK) (h811 : Asc82Lemma811K)
    (hSw : Sec8T84OuterSwaps) (hP : Sec8T84FactP) (hT : Asc82Step84TK) :
    ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Catalog G →
      ∀ (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
        Sec8E G t L S z g B E → S ⊓ L ≤ normalizer (E : Set G) →
          ∃ (B' E' T : Subgroup G) (γ : G), Sec8E G t L S z g B' E' ∧
            S ⊓ L ≤ normalizer (E' : Set G) ∧ IsSylow2Of T (normalizer (E' : Set G)) ∧
              S ⊓ normalizer (E' : Set G) ≤ T ∧ γ ∈ S ⊓ normalizer (T : Set G) ∧ γ ∉ T ∧
                InducesOutsideGStar L 6 (-1) γ ∧ S = zpowers t ⊔ zpowers γ ⊔ (S ⊓ L) := by
  intro G _ _ hKP t L S z g B E hE hgood
  have hctx : Sec8Ctx G t L S z g B := hE.ctx
  have hS : IsSylow2Of S (centralizer ({t} : Set G)) := hctx.sylow
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hctx.involution]
    exact pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htS : t ∈ S := sec4_t_mem_S hS hctx.involution
  have htN : t ∈ normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      exact hE.t_norm e he
    · intro he
      have h := hE.t_norm (t * e * t⁻¹) he
      have hkey : t * (t * e * t⁻¹) * t⁻¹ = e := by
        rw [htinv]
        calc t * (t * e * t) * t = (t * t) * e * (t * t) := by group
          _ = e := by rw [ht2]; group
      rwa [hkey] at h
  have h2grp : IsPGroup 2 ↥(S ⊓ normalizer (E : Set G)) := hS.2.1.to_le inf_le_left
  obtain ⟨T, hTsyl, hST⟩ :=
    exists_isSylow2Of_ge (H := normalizer (E : Set G)) h2grp inf_le_right
  have hTS : ¬ IsSylow2Of T ⊤ := hT G hKP t L S z g B E hE hgood T hTsyl hST
  have htT : t ∈ T := hST ⟨htS, htN⟩
  obtain ⟨Y1, Y2, hXO⟩ := h811 G hKP t L S z g B E hE
  obtain ⟨F1, D⟩ := sec8t84_tdata_of hP ht2 hE.elem hXO hTsyl htT
  have hrk : ∀ R : Subgroup G, R ≤ centralizer ({t} : Set G) → ¬ IsElemAb2 R 8 :=
    sec8t84_no_E8_cent_t F hI hKP hctx
  obtain ⟨c, hcC, hcN, hcT, hc2⟩ := sec8t84_exists_c D hrk hTsyl hTS
  obtain ⟨hM0S_raw, hM0L_raw, hS9, hS'9_raw⟩ :=
    sec8t84_S_card F hI hKP hE hgood hST D hcC hcT hcN hc2
  let M0 : Subgroup G := T ⊓ centralizer ({t} : Set G)
  have hM0eq : M0 = T ⊓ centralizer ({t} : Set G) := rfl
  have hM0S : S ⊓ normalizer (E : Set G) = M0 := by rw [hM0eq]; exact hM0S_raw
  have hM0L : M0 = zpowers t ⊔ (S ⊓ L) := by rw [hM0eq]; exact hM0L_raw
  let S' : Subgroup G := M0 ⊔ zpowers c
  have hS'2 : IsPGroup 2 S' := by
    show IsPGroup 2 ↥(M0 ⊔ zpowers c)
    exact hc2
  have hS'9 : Nat.card S' = 2 ^ 9 := by
    show Nat.card ↥(M0 ⊔ zpowers c) = 2 ^ 9
    exact hS'9_raw
  obtain ⟨γ, hγS, hγout, hSγ, -, -⟩ := sec8t84_gamma0 F hI hKP hctx
  have hSL : S ≤ normalizer (L : Set G) :=
    fun x hx => sec4_mem_normalizer F.h36 hctx.toSec3SettingLB x (hS.1 hx)
  have hSN : S ≤ normalizer (M0 : Set G) := by
    rw [hM0L]
    exact sec8t84_S_le_normalizer hS.1 hSL
  have hM0_le_C : M0 ≤ centralizer ({t} : Set G) := by rw [hM0eq]; exact inf_le_right
  have hM0_le_T : M0 ≤ T := by rw [hM0eq]; exact inf_le_left
  have hM0_le_S : M0 ≤ S := by rw [← hM0S]; exact inf_le_left
  have hSL_M0 : S ⊓ L ≤ M0 := by rw [hM0L]; exact le_sup_right
  have hcM0 : c ∈ normalizer (M0 : Set G) := by
    rw [hM0eq]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hcN, Subgroup.le_normalizer hcC⟩
  have hS'N : S' ≤ normalizer (M0 : Set G) := by
    show M0 ⊔ zpowers c ≤ normalizer (M0 : Set G)
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hcM0)
  have hS'C : S' ≤ centralizer ({t} : Set G) := by
    show M0 ⊔ zpowers c ≤ centralizer ({t} : Set G)
    exact sup_le hM0_le_C (Subgroup.zpowers_le.mpr hcC)
  have hS'T : S' ≤ normalizer (T : Set G) := by
    show M0 ⊔ zpowers c ≤ normalizer (T : Set G)
    exact sup_le (hM0_le_T.trans Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr hcN)
  obtain ⟨v, hvC, hvN, hSv⟩ :=
    sec8t84_conj_u hS hS'C hS'2 (hS'9.trans hS9.symm) hSN hS'N
  obtain ⟨hT', hSNT', hSNE', hSTE'⟩ :=
    sec8t84_NK_conj hTsyl hM0eq hS'C hS'2 hS'T (show M0 ≤ S' from le_sup_left) hvN hSv
  have hvNL : v ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer F.h36 hctx.toSec3SettingLB v hvC
  have hLv : L.map (MulAut.conj v).toMonoidHom = L := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hvNL :
      L.map (MulAut.conj v) = L)
  have hBvL : B.map (MulAut.conj v).toMonoidHom ≤ L := by
    rw [← hLv]
    exact Subgroup.map_mono (f := (MulAut.conj v).toMonoidHom) (hctx.B_le.trans inf_le_left)
  have hB_SL : B ≤ S ⊓ L :=
    le_inf (hctx.B_le.trans inf_le_right) (hctx.B_le.trans inf_le_left)
  have hB_M0 : B ≤ M0 := hB_SL.trans hSL_M0
  have hM0v : M0.map (MulAut.conj v).toMonoidHom = M0 := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hvN :
      M0.map (MulAut.conj v) = M0)
  have hBvS : B.map (MulAut.conj v).toMonoidHom ≤ S :=
    (Subgroup.map_mono (f := (MulAut.conj v).toMonoidHom) hB_M0).trans
      (hM0v.le.trans hM0_le_S)
  have hBv : B.map (MulAut.conj v).toMonoidHom ≤ L ⊓ S := le_inf hBvL hBvS
  have hSL_NE : S ⊓ L ≤
      normalizer ((E.map (MulAut.conj v).toMonoidHom : Subgroup G) : Set G) :=
    hSL_M0.trans (hSNE'.symm.le.trans inf_le_right)
  have hγ_not_T : γ ∉ T.map (MulAut.conj v).toMonoidHom := by
    intro hγT
    have hγNE : γ ∈
        normalizer ((E.map (MulAut.conj v).toMonoidHom : Subgroup G) : Set G) := hT'.1 hγT
    have hγM0 : γ ∈ M0 := hSNE' ▸ ⟨hγS, hγNE⟩
    have hγTC : γ ∈ T ⊓ centralizer ({t} : Set G) := by rw [← hM0eq]; exact hγM0
    exact sec8t84_gamma_not_cent hSw hE hTsyl.1 hγout hγTC
  exact ⟨B.map (MulAut.conj v).toMonoidHom, E.map (MulAut.conj v).toMonoidHom,
    T.map (MulAut.conj v).toMonoidHom, γ, sec8E_conj_cent hE hvC hBv, hSL_NE, hT',
    hSTE', ⟨hγS, hSNT' hγS⟩, hγ_not_T, hγout, hSγ⟩

end CFSG.OddStandard.SmallF3.Omega
