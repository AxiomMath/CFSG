module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Lift.Step
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.Main
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.CardOne
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.MinParLift
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymOverMain
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteen

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Lift

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.GN CFSG.AGLEmbeddingD2.McLaughlin.A7Six Equiv Equiv.Perm
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

namespace SevenCtx0

noncomputable def wP_mulEquiv_of_le_alternating (c : SevenCtx0 T L)
    {A : Subgroup (Perm (Fin 7))} (hA : A ≤ alternatingGroup (Fin 7)) :
    ↥(c.wP A) ≃* ↥A := by
  classical
  let e : ↥(c.wP A) →* Perm (Fin 7) :=
    ((alternatingGroup (Fin 7)).subtype.comp c.eL.toMonoidHom).comp
      (Subgroup.inclusion (c.wP_le_L A))
  have he : ∀ x : ↥(c.wP A), e x ∈ A := by
    intro x
    obtain ⟨hxL, hxA⟩ := (c.mem_wP).1 x.2
    have h1 : (⟨(x : X ⧸ gnC T), (c.wP_le_L A) x.2⟩ : ↥L) =
        ⟨(x : X ⧸ gnC T), hxL⟩ := Subtype.ext rfl
    have h2 : e x = ((c.eL ⟨(x : X ⧸ gnC T), (c.wP_le_L A) x.2⟩ :
        alternatingGroup (Fin 7)) : Perm (Fin 7)) := rfl
    rw [h2, h1]
    exact hxA
  let f : ↥(c.wP A) →* ↥A := e.codRestrict A he
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    have h1 : ((f x : ↥A) : Perm (Fin 7)) = ((f y : ↥A) : Perm (Fin 7)) :=
      congrArg (fun z : ↥A => (z : Perm (Fin 7))) hxy
    have h2 : ((c.eL ⟨(x : X ⧸ gnC T), (c.wP_le_L A) x.2⟩ :
        alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        ((c.eL ⟨(y : X ⧸ gnC T), (c.wP_le_L A) y.2⟩ :
        alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
      simpa [f, e] using h1
    have h3 : c.eL ⟨(x : X ⧸ gnC T), (c.wP_le_L A) x.2⟩ =
        c.eL ⟨(y : X ⧸ gnC T), (c.wP_le_L A) y.2⟩ := Subtype.ext h2
    exact Subtype.ext (congrArg (fun z : ↥L => (z : X ⧸ gnC T)) (c.eL.injective h3))
  · intro a
    let w : ↥L := c.eL.symm ⟨(a : Perm (Fin 7)), hA a.2⟩
    have hw : (w : X ⧸ gnC T) ∈ c.wP A := by
      refine (c.mem_wP).2 ⟨w.2, ?_⟩
      rw [show (⟨(w : X ⧸ gnC T), w.2⟩ : ↥L) = w from Subtype.ext rfl,
        MulEquiv.apply_symm_apply]
      exact a.2
    refine ⟨⟨(w : X ⧸ gnC T), hw⟩, ?_⟩
    apply Subtype.ext
    show ((c.eL ⟨(w : X ⧸ gnC T), (c.wP_le_L A) hw⟩ :
      alternatingGroup (Fin 7)) : Perm (Fin 7)) = (a : Perm (Fin 7))
    rw [show (⟨(w : X ⧸ gnC T), (c.wP_le_L A) hw⟩ : ↥L) = w from Subtype.ext rfl]
    exact congrArg Subtype.val (c.eL.apply_symm_apply ⟨(a : Perm (Fin 7)), hA a.2⟩)

theorem le_normalizer_wP (c : SevenCtx0 T L) {R : Subgroup X} (hRL : R ≤ nL T L)
    {A : Subgroup (Perm (Fin 7))}
    (hRA : c.img R ≤ Subgroup.normalizer (A : Set (Perm (Fin 7)))) :
    R.map (QuotientGroup.mk' (gnC T)) ≤
      Subgroup.normalizer (c.wP A : Set (X ⧸ gnC T)) := by
  classical
  set π := QuotientGroup.mk' (gnC T)
  set Rs : Subgroup (X ⧸ gnC T) := R.map π with hRs
  have hRLs : Rs ≤ nLs T L := by
    rintro _ ⟨r, hr, rfl⟩
    exact hRL hr
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ Rs, ∀ w ∈ c.wP A, g * w * g⁻¹ ∈ c.wP A := by
    intro g hg w hw
    obtain ⟨hwL, hwA⟩ := (c.mem_wP).1 hw
    obtain ⟨t, ht, rfl⟩ := hg
    have hgwL : π t * w * (π t)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hRLs ⟨t, ht, rfl⟩) w).1 hwL
    refine (c.mem_wP).2 ⟨hgwL, ?_⟩
    have hθt : c.θs ⟨π t, hRLs ⟨t, ht, rfl⟩⟩ = c.θ ⟨t, hRL ht⟩ := rfl
    have hnorm : c.θ ⟨t, hRL ht⟩ ∈ Subgroup.normalizer (A : Set (Perm (Fin 7))) :=
      hRA ((c.mem_img hRL).2 ⟨t, ht, rfl⟩)
    rw [c.hθs ⟨π t, hRLs ⟨t, ht, rfl⟩⟩ ⟨w, hwL⟩ ⟨_, hgwL⟩ rfl, hθt]
    exact (Subgroup.mem_normalizer_iff.1 hnorm _).1 hwA
  intro w
  constructor
  · exact key r hr w
  · intro h
    have := key r⁻¹ (Rs.inv_mem hr) _ h
    simpa [mul_assoc] using this

theorem wP_sup_eq (c : SevenCtx0 T L) {R : Subgroup X} (hRL : R ≤ nL T L)
    {P A : Subgroup (Perm (Fin 7))} (hPA7 : P ≤ alternatingGroup (Fin 7))
    (hPAR : P = A ⊔ c.img R)
    (hRA : c.img R ≤ Subgroup.normalizer (A : Set (Perm (Fin 7))))
    (hQL : ∀ σ ∈ c.img R, ∃ (t : X) (ht : t ∈ R),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c.θ ⟨t, hRL ht⟩ = σ) :
    c.wP P ⊔ R.map (QuotientGroup.mk' (gnC T)) =
      c.wP A ⊔ R.map (QuotientGroup.mk' (gnC T)) := by
  classical
  set π := QuotientGroup.mk' (gnC T)
  have hRLs : R.map π ≤ nLs T L := by
    rintro _ ⟨r, hr, rfl⟩
    exact hRL hr
  have hAP : A ≤ P := by
    rw [hPAR]
    exact le_sup_left
  have hA7 : A ≤ alternatingGroup (Fin 7) := hAP.trans hPA7
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    intro x hx
    obtain ⟨hxL, hxP⟩ := (c.mem_wP).1 hx
    have hxP' : ((c.eL ⟨x, hxL⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈
        (A : Set (Perm (Fin 7))) * (c.img R : Set (Perm (Fin 7))) := by
      have h1 : ((c.eL ⟨x, hxL⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈
          A ⊔ c.img R := by
        rw [← hPAR]
        exact hxP
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A (c.img R) hRA] at h1
      exact h1
    obtain ⟨a, haA, σ, hσR, hx_eq⟩ := hxP'
    obtain ⟨t, htR, htL, htσ⟩ := hQL σ hσR
    let w : X ⧸ gnC T := (c.eL.symm ⟨a, hA7 haA⟩ : ↥L)
    have hwL : w ∈ L := (c.eL.symm ⟨a, hA7 haA⟩).2
    have hwA : w ∈ c.wP A := by
      refine (c.mem_wP).2 ⟨hwL, ?_⟩
      rw [show (⟨w, hwL⟩ : ↥L) = c.eL.symm ⟨a, hA7 haA⟩ from Subtype.ext rfl,
        MulEquiv.apply_symm_apply]
      exact haA
    have hyR : π t ∈ R.map π := ⟨t, htR, rfl⟩
    have hyL : π t ∈ L := htL
    have hyθ : c.θs ⟨π t, hRLs hyR⟩ = σ := by
      change c.θ ⟨t, hRL htR⟩ = σ
      exact htσ
    have hwyL : w * π t ∈ L := L.mul_mem hwL hyL
    have hwy : w * π t ∈ c.wP A ⊔ R.map π :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hwA) (Subgroup.mem_sup_right hyR)
    have heq : (⟨x, hxL⟩ : ↥L) = ⟨w * π t, hwyL⟩ := by
      apply c.eL.injective
      apply Subtype.ext
      have h1 : ((c.eL ⟨w * π t, hwyL⟩ : alternatingGroup (Fin 7)) :
          Perm (Fin 7)) = a * σ := by
        rw [show (⟨w * π t, hwyL⟩ : ↥L) = ⟨w, hwL⟩ * ⟨π t, hyL⟩ from Subtype.ext rfl,
          map_mul]
        change ((c.eL ⟨w, hwL⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) *
          ((c.eL ⟨π t, hyL⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) = a * σ
        rw [show c.eL ⟨w, hwL⟩ = ⟨a, hA7 haA⟩ from
          c.eL.apply_symm_apply ⟨a, hA7 haA⟩,
          ← c.θs_of_mem_L (y := ⟨π t, hRLs hyR⟩) hyL, hyθ]
      rw [← hx_eq, h1]
    have hx_eq' : x = w * π t := by
      simpa using congrArg (fun z : ↥L => (z : X ⧸ gnC T)) heq
    rw [hx_eq']
    exact hwy
  · refine sup_le ?_ le_sup_right
    intro x hx
    exact Subgroup.mem_sup_left ((c.mem_wP).2 ⟨((c.mem_wP).1 hx).1,
      hAP ((c.mem_wP).1 hx).2⟩)

private theorem card_lt_two_wP (c : SevenCtx0 T L) {R H M : Subgroup X}
    {P A : Subgroup (Perm (Fin 7))} (hminH : MinParabolic H R M) (hF : CharTwo H)
    (hRL : R ≤ nL T L) (hPA7 : P ≤ alternatingGroup (Fin 7))
    (hPAR : P = A ⊔ c.img R)
    (hRA : c.img R ≤ Subgroup.normalizer (A : Set (Perm (Fin 7))))
    (hQL : ∀ σ ∈ c.img R, ∃ (t : X) (ht : t ∈ R),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c.θ ⟨t, hRL ht⟩ = σ)
    (hA5 : Nonempty (↥A ≃* alternatingGroup (Fin 5)))
    (hmap : H.map (QuotientGroup.mk' (gnC T)) =
      c.wP P ⊔ R.map (QuotientGroup.mk' (gnC T)))
    (hRp : IsPGroup 2 (R.map (QuotientGroup.mk' (gnC T)))) :
    ∀ (V : Subgroup X) (hV : IsElemAbelian 2 V), V = VZ R H →
      ∀ I, E23FamGen H R V hV I →
        (∀ Kf ∈ I, ∃ n : ℕ, 2 ≤ n ∧
          CFSG.Quasithin.E2.IsL2Natural Kf (fixV (autI hV (twoResidual H))) n) →
        twoResidual H ≤ thompsonJ H → I.card < 2 := by
  classical
  intro V hV hVZ I hFam hnat hJ
  have hAP : A ≤ P := by
    rw [hPAR]
    exact le_sup_left
  have hA7 : A ≤ alternatingGroup (Fin 7) := hAP.trans hPA7
  have hA5q : CFSG.Open.IsQuasisimple (alternatingGroup (Fin 5)) :=
    CFSG.CGT.PushingUpLit.BHS.isQuasisimple_alternatingGroup (n := 5) (by norm_num)
  let eA : ↥(c.wP A) ≃* alternatingGroup (Fin 5) :=
    (c.wP_mulEquiv_of_le_alternating hA7).trans hA5.some
  have hQA : CFSG.Open.IsQuasisimple ↥(c.wP A) :=
    CFSG.CGT.PushingUpLit.BHS.isQuasisimple_of_mulEquiv' eA.symm hA5q
  have hmapA : H.map (QuotientGroup.mk' (gnC T)) =
      c.wP A ⊔ R.map (QuotientGroup.mk' (gnC T)) := by
    rw [hmap, c.wP_sup_eq hRL hPA7 hPAR hRA hQL]
  exact Tits.GN516.card_lt_two_of_sup_image hminH hF
    (QuotientGroup.mk' (gnC T)) hQA hRp (c.le_normalizer_wP hRL hRA) hmapA hV hVZ hFam hnat hJ

theorem step_nonsolv (c : SevenCtx0 T L)
    (hX : GNSetting X T) {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂)
    (hDL : gnD T ⊓ lT T L ≤ gnC T) {R : Subgroup X} (hRL : R ≤ nL T L) (hRT : R ≤ T)
    (hCR : T ⊓ gnC T ≤ R) (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R) (hbR : baum T ≤ R)
    {P Pm A : Subgroup (Perm (Fin 7))} (hmin : MinParabolic P (c.img R) Pm)
    (hPA7 : P ≤ alternatingGroup (Fin 7)) (hA5 : Nonempty (↥A ≃* alternatingGroup (Fin 5)))
    (hPAR : P = A ⊔ c.img R) (hRA : c.img R ≤ Subgroup.normalizer (A : Set (Perm (Fin 7))))
    (hQL : ∀ σ ∈ c.img R, ∃ (t : X) (ht : t ∈ R),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c.θ ⟨t, hRL ht⟩ = σ) :
    c.wP P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c.wP P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)) := by
  classical
  set π := QuotientGroup.mk' (gnC T)
  set Rs : Subgroup (X ⧸ gnC T) := R.map π with hRs
  have hRLs : Rs ≤ nLs T L := by
    rintro _ ⟨r, hr, rfl⟩
    exact hRL hr
  have hRp : IsPGroup 2 Rs := (hX.sylow.2.1.to_le hRT).map π
  have hQ : c.imgS Rs = c.img R := c.imgS_map R hRL
  have hQL' : ∀ σ ∈ c.img R ⊓ alternatingGroup (Fin 7), ∃ (y : X ⧸ gnC T)
      (hy : y ∈ Rs ⊓ L), c.θs ⟨y, hRLs hy.1⟩ = σ := by
    intro σ hσ
    obtain ⟨t, ht, htL, htσ⟩ := hQL σ hσ.1
    exact ⟨π t, ⟨⟨t, ht, rfl⟩, htL⟩, htσ⟩
  obtain ⟨hminWs, himg, hker⟩ :=
    c.minParabolic_wP_gen hRLs hRp hQ hmin (Or.inl hPA7) hQL'
  obtain ⟨H, M, hminH, hF, hRH, hmap⟩ :=
    Tits.GN516.exists_minParabolic_lift_of_le hX hRT hCR hQR hminWs
  have hcard := c.card_lt_two_wP hminH hF hRL hPA7 hPAR hRA hQL hA5 hmap hRp
  have hQL_inf : ∀ σ ∈ c.img R ⊓ alternatingGroup (Fin 7), ∃ (t : X) (ht : t ∈ R),
      π t ∈ L ∧ c.θ ⟨t, hRL ht⟩ = σ := fun σ hσ => hQL σ hσ.1
  have hQP : c.img R ≤ P := hmin.isSylow.1
  have hPQ : P ≠ c.img R := by
    intro h
    exact hmin.not_normal (h ▸ Subgroup.le_normalizer)
  rcases Tits.GN516.concl1Gen_over_weak_or_sym Tits.E23.e23NonsolvGen hP hX.sylow.2.1
    hbR hRT hminH hF hcard with hC | ⟨hJ, hV, hSym⟩
  · exact c.escape_of_concl1Gen hX hDL hRL hRT hQR hQP hPQ hQL_inf hminH hRH hmap himg hker hC
  · exact c.escape_of_concl1Gen hX hDL hRL hRT hQR hQP hPQ hQL_inf hminH hRH hmap himg hker
      (Tits.GN516.concl1Gen_of_symCase_all hP hX.sylow.2.1 hbR hRT hminH hF hJ hV hSym)

end SevenCtx0

end CFSG.AGLEmbeddingD2.McLaughlin.A7Lift
