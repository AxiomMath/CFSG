module

public import CFSG.Quasithin.Background.StrongFFStarTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftXEmbed
public import CFSG.Quasithin.Background.HTransport
public import CFSG.Quasithin.Background.C58Push
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin CFSG.Quasithin.B2F

section Top

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem mem_frattini_comap_congr {X : Type*} [Group X] {N₁ N₂ : Subgroup X} [N₁.Normal]
    [N₂.Normal] (h : N₁ = N₂) (x : X) :
    QuotientGroup.mk' N₁ x ∈ frattini (X ⧸ N₁) ↔ QuotientGroup.mk' N₂ x ∈ frattini (X ⧸ N₂) := by
  subst h
  rfl

omit [Finite Γ] in
theorem cjSub_eq_thompsonJ_of {X : Subgroup Γ} (hX : X = thompsonJ X) (l : Γ) :
    cjSub l X = thompsonJ (cjSub l X) := by
  conv_lhs => rw [hX]
  exact thompsonJ_map_mulEquiv (MulAut.conj l) X

theorem twoResidual_top_eq_pResidualOf :
    twoResidual (⊤ : Subgroup Γ) = pResidualOf 2 (⊤ : Subgroup Γ) := by
  rw [twoResidual_eq_oddOrderSubgroup, pResidualOf_top_eq_closure_odd]
  unfold oddOrderSubgroup
  congr 1
  ext x
  simp

theorem baum_sylow_of_top {T M V : Subgroup Γ} (hV : IsElemAbelian 2 V)
    (hmin : MinParabolic (⊤ : Subgroup Γ) T M) (hred : IsTwoReducedIn (⊤ : Subgroup Γ) V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ))
    (hnost : ∀ B, ¬ IsStrongFFStarOffender (autI hV T) B)
    (hsyl : IsSylowTwoOf (autI hV (baum T))
      (autI hV (twoResidual (⊤ : Subgroup Γ)) ⊔ autI hV (baum T)))
    {g : Γ} (hgL : g ∈ twoResidual (⊤ : Subgroup Γ))
    (hgen : autI hV (twoResidual (⊤ : Subgroup Γ)) ≤
      autI hV (thompsonJ T) ⊔ autI hV (cjSub g (thompsonJ T)))
    (hrank : 2 * rkIdx (fixV (autI hV (thompsonJ T))) ≤
      rkIdx (fixV (autI hV (twoResidual (⊤ : Subgroup Γ))))) :
    IsSylowTwoOf (baum T) (twoResidual (⊤ : Subgroup Γ) ⊔ baum T) := by
  have hVN : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hred.2.1)
  have hTs : IsSylowTwoOf T (⊤ : Subgroup Γ) := hmin.isSylow
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hTs)
  have hTn : ¬ T.Normal := fun hn =>
    hmin.not_normal (fun x _ => by rw [Subgroup.normalizer_eq_top_iff.2 hn]; exact Subgroup.mem_top x)
  have hVH : ¬ (⊤ : Subgroup Γ) ≤ Subgroup.centralizer (V : Set Γ) := fun h =>
    hJ ((thompsonJ_le_self T).trans (le_top.trans h))
  obtain ⟨hLR, hCR, hQC, hCJ, hPL, -, hD⟩ :=
    minimal_parabolic_reduced_module_Frattini_kernel_production hTs hTn hmin.le hmin.maximal.1
      (fun Y hTY hY => hmin.le_of_lt hTY hY) hred hVH
  have hLeq : twoResidual (⊤ : Subgroup Γ) = oddOrderSubgroup (⊤ : Subgroup Γ) :=
    twoResidual_eq_oddOrderSubgroup _
  rw [hLeq] at hsyl hgL hgen hrank ⊢
  set L := oddOrderSubgroup (⊤ : Subgroup Γ) with hLdef
  have hL : L = pResidualOf 2 (⊤ : Subgroup Γ) := by
    rw [← hLeq]; exact twoResidual_top_eq_pResidualOf
  have hQn : (CFSG.pCore 2 Γ).Normal := CFSG.pCore_normal
  have hQeq : T ⊓ Subgroup.centralizer (V : Set Γ) = CFSG.pCore 2 Γ := hCR
  have hLT : L ⊔ T = ⊤ := hLR
  have ha₁ : pCoreOf 2 L ≤ T ⊓ Subgroup.centralizer (V : Set Γ) := by
    rw [hQeq]
    have h1 : pCoreOf 2 L = L ⊓ CFSG.pCore 2 Γ := by
      unfold pCoreOf
      exact hPL
    rw [h1]
    exact inf_le_right
  have ha₂ : L ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set Γ) : Subgroup Γ) : Set Γ) := by
    rw [hQeq]
    exact fun x _ => Subgroup.mem_normalizer_iff.2 fun z => by
      constructor
      · intro hz; exact hQn.conj_mem z hz x
      · intro hz
        have := hQn.conj_mem _ hz x⁻¹
        simpa [mul_assoc] using this
  have hb : L ⊓ Subgroup.centralizer (V : Set Γ) ≤ oTwoPhi L := by
    intro x ⟨hxL, hxC⟩
    have h1 := hD (Subgroup.centralizer (V : Set Γ)) hCJ
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨x, hxL⟩ : ↥L) ∈
        (( Subgroup.centralizer (V : Set Γ)).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.2 hxC, rfl⟩
    have h3 := h1 h2
    have h4 := (mem_frattini_comap_congr (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥L)
      ⟨x, hxL⟩).1 h3
    exact ⟨⟨x, hxL⟩, h4, rfl⟩
  have hN : ∀ x : Γ, x ∈ Subgroup.normalizer (V : Set Γ) := fun x => by
    rw [Subgroup.normalizer_eq_top_iff.2 hVN]
    exact Subgroup.mem_top x
  have hJJ : thompsonJ T = thompsonJ (thompsonJ T) := (thompsonJ_thompsonJ T).symm
  have hgLi : g⁻¹ ∈ L := L.inv_mem hgL
  have hrk1 : rkIdx (fixV (autI hV (cjSub g (thompsonJ T)))) =
      rkIdx (fixV (autI hV (thompsonJ T))) := by
    have e1 := rkIdx_fixV_autI hV (Y := thompsonJ T) (fun x _ => hN x)
    have e2 := rkIdx_fixV_autI hV (Y := cjSub g (thompsonJ T)) (fun x _ => hN x)
    rw [rk_inf_centralizer_cjSub (hN g)] at e2
    omega
  have hde : ∃ (n : ℕ) (X : Fin n → Subgroup Γ),
      (∀ i, ∃ l ∈ L, cjSub l (X i) ≤ T) ∧ (∀ i, X i = thompsonJ (X i)) ∧
      (∀ i, Open.pRank 2 (X i) = Open.pRank 2 T) ∧ autI hV L ≤ ⨆ i, autI hV (X i) ∧
      ∑ i, rkIdx (fixV (autI hV (X i))) ≤ rkIdx (fixV (autI hV L)) ∧
      thompsonJ T ≤ ⨆ i, X i := by
    refine ⟨2, ![thompsonJ T, cjSub g (thompsonJ T)], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · refine ⟨1, L.one_mem, fun x hx => ?_⟩
        have hx' : (1 : Γ)⁻¹ * x * 1 ∈ thompsonJ T := mem_cjSub.1 hx
        simpa using thompsonJ_le_self T hx'
      · exact ⟨g⁻¹, hgLi, by
          show cjSub g⁻¹ (cjSub g (thompsonJ T)) ≤ T
          rw [cjSub_inv_cjSub]; exact thompsonJ_le_self T⟩
    · intro i
      fin_cases i
      · exact hJJ
      · exact cjSub_eq_thompsonJ_of hJJ g
    · intro i
      fin_cases i
      · exact pRank_thompsonJ T
      · exact (pRank_cjSub g _).trans (pRank_thompsonJ T)
    · refine hgen.trans (sup_le ?_ ?_)
      · exact le_iSup (fun i => autI hV (![thompsonJ T, cjSub g (thompsonJ T)] i)) 0
      · exact le_iSup (fun i => autI hV (![thompsonJ T, cjSub g (thompsonJ T)] i)) 1
    · rw [Fin.sum_univ_two]
      show rkIdx (fixV (autI hV (thompsonJ T))) + rkIdx (fixV (autI hV (cjSub g (thompsonJ T)))) ≤ _
      rw [hrk1]
      omega
    · exact le_iSup (fun i => (![thompsonJ T, cjSub g (thompsonJ T)] : Fin 2 → Subgroup Γ) i) 0
  obtain ⟨-, -, h3⟩ := B2_18 hV hVN hL hTs.2.1 hVT ha₁ ha₂ hb hnost hde
  have hsylC : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set Γ))
      ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set Γ)) := by
    rw [hLT, top_inf_eq]
    have := B6.isSylowTwoOf_inf_normal hTs le_top (by
      rw [Subgroup.normalizer_eq_top_iff.2 (inferInstance : (Subgroup.centralizer (V : Set Γ)).Normal)])
    exact this
  exact (h3 hsylC).2 hsyl

end Top

section Transport

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem isStrongFFStarOffender_map_congrHom_iff' (e : V ≃* W) {X A : Subgroup (MulAut V)} :
    IsStrongFFStarOffender (X.map (CFSG.Quasithin.H.congrHom e))
        (A.map (CFSG.Quasithin.H.congrHom e)) ↔ IsStrongFFStarOffender X A :=
  CFSG.Quasithin.isStrongFFStarOffender_map_congr_equiv_iff e

theorem no_strong_of_map (e : V ≃* W) {X : Subgroup (MulAut V)}
    (h : ∀ B, ¬ IsStrongFFStarOffender X B) :
    ∀ B', ¬ IsStrongFFStarOffender (X.map (CFSG.Quasithin.H.congrHom e)) B' := by
  intro B' hB'
  have hle : B' ≤ X.map (CFSG.Quasithin.H.congrHom e) := hB'.1.1
  obtain ⟨B, -, rfl⟩ := CFSG.Quasithin.H.exists_eq_map_congrHom e hle
  exact h B ((isStrongFFStarOffender_map_congrHom_iff' e).1 hB')

end Transport

section Sub

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

theorem thompsonJ_subgroupOf (hTH : T ≤ H) :
    thompsonJ (T.subgroupOf H) = (thompsonJ T).subgroupOf H := by
  have h1 : (thompsonJ (T.subgroupOf H)).map H.subtype = thompsonJ T := by
    rw [← thompsonJ_map_of_injective' H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hTH]
  have h2 : ((thompsonJ T).subgroupOf H).map H.subtype = thompsonJ T :=
    Subgroup.map_subgroupOf_eq_of_le ((thompsonJ_le_self T).trans hTH)
  exact Subgroup.map_injective H.subtype_injective (h1.trans h2.symm)

theorem baum_subgroupOf (hTH : T ≤ H) : baum (T.subgroupOf H) = (baum T).subgroupOf H := by
  have h1 : (baum (T.subgroupOf H)).map H.subtype = baum T := by
    rw [← baum_map_of_injective H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hTH]
  have h2 : ((baum T).subgroupOf H).map H.subtype = baum T :=
    Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hTH)
  exact Subgroup.map_injective H.subtype_injective (h1.trans h2.symm)

theorem cjSub_subgroupOf (g : H) (K : Subgroup G) :
    cjSub g (K.subgroupOf H) = (cjSub (g : G) K).subgroupOf H := by
  ext x
  simp only [mem_cjSub, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]

noncomputable def modEquiv (hV : IsElemAbelian 2 V) (hV' : IsElemAbelian 2 (V.subgroupOf H))
    (hVH : V ≤ H) : IntMod V hV ≃* IntMod (V.subgroupOf H) hV' :=
  CFSG.QuasithinUnique.Setup.Lift.vEquiv hVH

theorem map_autI_subgroupOf (hV : IsElemAbelian 2 V) (hV' : IsElemAbelian 2 (V.subgroupOf H))
    (hVH : V ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G)) {K : Subgroup G} (hKH : K ≤ H) :
    (autI hV K).map (CFSG.Quasithin.H.congrHom (modEquiv hV hV' hVH)) =
      autI hV' (K.subgroupOf H) :=
  (CFSG.QuasithinUnique.Setup.Lift.autOn_subgroupOf hVH hHN hKH).symm

end Sub

section Final

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

theorem isSylowTwoOf_baum_of_nat (hV : IsElemAbelian 2 V) (hmin : MinParabolic H T M)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hnost : ∀ B, ¬ IsStrongFFStarOffender (autI hV T) B)
    (hS : autI hV (baum T) = autI hV (thompsonJ T))
    (hsyl : IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)))
    (hLJ : autI hV (twoResidual H) ≤ autI hV (thompsonJ H))
    {g : G} (hgL : g ∈ twoResidual H)
    (hgen : autI hV (twoResidual H) ≤
      autI hV (thompsonJ T) ⊔ autI hV (cjSub g (thompsonJ T)))
    (hrank : 2 * rkIdx (fixV (autI hV (thompsonJ T))) ≤
      rkIdx (fixV (autI hV (twoResidual H)))) :
    IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) := by
  have hTH : T ≤ H := hmin.isSylow.1
  have hVH : V ≤ H := hred.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hJH : thompsonJ T ≤ H := (thompsonJ_le_self T).trans hTH
  have hBH : baum T ≤ H := inf_le_left.trans hTH
  have hgH : g ∈ H := hKH hgL
  have hred' := C58.isTwoReducedIn_top_subgroupOf hred
  have hV' : IsElemAbelian 2 (V.subgroupOf H) := hred'.2.2.1
  set e := modEquiv hV hV' hVH with he
  have T1 : ∀ {K : Subgroup G}, K ≤ H →
      (autI hV K).map (CFSG.Quasithin.H.congrHom e) = autI hV' (K.subgroupOf H) :=
    fun hKH => map_autI_subgroupOf hV hV' hVH hHN hKH
  have hcjH : cjSub g (thompsonJ T) ≤ H := cjSub_le (Subgroup.le_normalizer hgH) hJH
  have hsyl2 : IsSylowTwoOf (autI hV (baum T)) (autI hV (twoResidual H) ⊔ autI hV (baum T)) := by
    rw [hS]
    have hle : autI hV (twoResidual H) ⊔ autI hV (thompsonJ T) ≤ autI hV (thompsonJ H) :=
      sup_le hLJ hsyl.1
    refine ⟨le_sup_right, hsyl.2.1, fun h2 => hsyl.2.2 ?_⟩
    have h2' : 2 ∣ (autI hV (thompsonJ T)).relIndex
        (autI hV (twoResidual H) ⊔ autI hV (thompsonJ T)) := h2
    show 2 ∣ (autI hV (thompsonJ T)).relIndex (autI hV (thompsonJ H))
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hle]
    exact h2'.mul_right _
  have hmain := baum_sylow_of_top (Γ := ↥H) (T := T.subgroupOf H) (M := M.subgroupOf H)
    (V := V.subgroupOf H) hV' hmin.subgroupOf hred' ?_ ?_ ?_ (g := ⟨g, hgH⟩) ?_ ?_ ?_
  · have h1 := X35.isSylowTwoOf_map_of_injective H.subtype_injective hmain
    rw [baum_subgroupOf hTH, B6.twoResidual_top_eq_subgroupOf, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hKH, Subgroup.map_subgroupOf_eq_of_le hBH] at h1
    exact h1
  ·
    intro h
    apply hJ
    intro j hj
    have hjH : j ∈ H := hJH hj
    have hj' : (⟨j, hjH⟩ : H) ∈ thompsonJ (T.subgroupOf H) := by
      rw [thompsonJ_subgroupOf hTH]
      exact Subgroup.mem_subgroupOf.2 hj
    exact (BlueprintB2.mem_centralizer_subgroupOf_iff hVH ⟨j, hjH⟩).1 (h hj')
  · rw [← T1 hTH]
    exact no_strong_of_map e hnost
  · rw [baum_subgroupOf hTH, B6.twoResidual_top_eq_subgroupOf, ← T1 hBH, ← T1 hKH,
      ← Subgroup.map_sup]
    exact X35.isSylowTwoOf_map_of_injective (CFSG.Quasithin.H.congrHom_injective e) hsyl2
  · rw [B6.twoResidual_top_eq_subgroupOf]
    exact Subgroup.mem_subgroupOf.2 hgL
  · rw [B6.twoResidual_top_eq_subgroupOf, thompsonJ_subgroupOf hTH,
      cjSub_subgroupOf ⟨g, hgH⟩, ← T1 hKH, ← T1 hJH, ← T1 hcjH, ← Subgroup.map_sup]
    exact Subgroup.map_mono hgen
  · rw [B6.twoResidual_top_eq_subgroupOf, thompsonJ_subgroupOf hTH, ← T1 hKH, ← T1 hJH,
      CFSG.Quasithin.H.rkIdx_fixV_map_congrHom, CFSG.Quasithin.H.rkIdx_fixV_map_congrHom]
    exact hrank

end Final

end CFSG.AGLEmbeddingD2.Tits.E23
