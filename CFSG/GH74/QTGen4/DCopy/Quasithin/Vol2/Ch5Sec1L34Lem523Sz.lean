module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523Sz
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem523F
public import CFSG.Quasithin.Background.A3Structure36AList
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SzOff

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem sqtkGroup_G₁_F4 (h5114 : Stmt5_1_14_first_F4) :
    SQTKGroup ↥(Subgroup.centralizer (Z₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  have hTG₁ : T ≤ Subgroup.centralizer (Z₁ : Set G) :=
    s.hyp.hyp.hStar.1.1.trans (s.H_le_centralizer_F4 h5114)
  have hZ1T : Z₁ ≤ T := s.Z₁_le_Z.trans (quasithinOmegaOneCenter_le_self T)
  have hZ1O : Z₁ ≤ pCoreOf 2 (Subgroup.centralizer (Z₁ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hZ1T.trans hTG₁)
      (Subgroup.centralizer_le_normalizer _) (hh.sylow.1.to_le hZ1T)
  refine sqtkGroup_of_pCoreOf_ne_bot hh.qtke hh.simple hh.nonabelian fun hb => ?_
  have := hZ1O hz
  rw [hb, Subgroup.mem_bot] at this
  exact hz1 this

theorem isQuotientOfSQTK_autOn_G₁_F4 (h5114 : Stmt5_1_14_first_F4) :
    IsQuotientOfSQTKTC ↥(autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))))) := by
  have hSQ := s.sqtkGroup_G₁_F4 h5114
  exact ⟨↥(Subgroup.centralizer (Z₁ : Set G)), inferInstance, inferInstance,
    fun p hp hp2 => hSQ.1 p hp hp2, hSQ.2,
    tildeAct Z₁ _ (Subgroup.centralizer_le_normalizer _) _
      (tildeOf_le_normalizer_tildeOf (le_normalizer_conjClosure _ _)),
    tildeAct_surjective _ _⟩

theorem suzukiModel_of_le_autOn_C₁_F4 (h5114 : Stmt5_1_14_first_F4) (h516 : Stmt5_1_16_F4)
    (hA23 : A23SQTKListFact) (hSzF : SimpleThreePrimeSuzukiFact)
    {Lc : Subgroup (MulAut ↥(tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G)))))}
    (hLc : Lc ≤ autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G) ⊓
      centralizerModO2 (oTwoUpper H)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))))
    (hq : CFSG.IsQuasisimple ↥Lc) : ∃ k : ℕ, SuzukiModel (↥Lc ⧸ Subgroup.center ↥Lc) 2 k := by
  have hG₁N : Subgroup.centralizer (Z₁ : Set G) ≤ Subgroup.normalizer (Z₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hG₁tU := tildeOf_le_normalizer_tildeOf (Z₁ := Z₁)
    (le_normalizer_conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))
  set φ := tildeAct Z₁ _ hG₁N _ hG₁tU with hφ
  have hφs : Function.Surjective φ := tildeAct_surjective _ _
  set ψ := (autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
    (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))))).subtype.comp
    φ with hψ
  have hLcG : Lc ≤ autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))) :=
    hLc.trans (autOn_le_autOn _ (tildeOf_mono inf_le_left))

  set Hs : Subgroup ↥(Subgroup.centralizer (Z₁ : Set G)) := Lc.comap ψ with hHs
  let π : ↥Hs →* ↥Lc ⧸ Subgroup.center ↥Lc :=
    (QuotientGroup.mk' (Subgroup.center ↥Lc)).comp
      ((ψ.comp Hs.subtype).codRestrict Lc (fun x => x.2))
  have hπs : Function.Surjective π := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥Lc) q
    obtain ⟨x, hx⟩ := hφs ⟨y, hLcG hy⟩
    have hxH : x ∈ Hs := by
      show ψ x ∈ Lc
      rw [hψ, MonoidHom.comp_apply, hx]
      exact hy
    refine ⟨⟨x, hxH⟩, ?_⟩
    show QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _
    congr 1
    apply Subtype.ext
    show ψ x = y
    rw [hψ, MonoidHom.comp_apply, hx]
    rfl
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπs
  have hsimple : IsSimpleGroup (↥Lc ⧸ Subgroup.center ↥Lc) := hq.2.1
  have hsimple' : IsSimpleGroup (↥Hs ⧸ π.ker) := by
    have := hsimple
    exact MulEquiv.isSimpleGroup e
  have hnab : ∃ a b : ↥Hs ⧸ π.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hlist : A23List (↥Lc ⧸ Subgroup.center ↥Lc) :=
    A36A.a23List_of_mulEquiv e.symm (hA23 _ (s.sqtkGroup_G₁_F4 h5114) Hs π.ker hsimple' hnab)

  have h3 : ¬ 3 ∣ Nat.card (↥Lc ⧸ Subgroup.center ↥Lc) := by
    intro h3
    apply s.not_three_dvd_card_autOn_C₁_F4 h516
    exact h3.trans ((Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective _)).trans
      (Subgroup.card_dvd_of_le hLc))
  exact hSzF _ hsimple hlist h3

theorem false_of_le_centralizer_of_D38_F4
    (h38 : D38Top) (hA23 : A23SQTKListFact) (hSzF : SimpleThreePrimeSuzukiFact)
    (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) (h516 : Stmt5_1_16_F4) (h521 : Stmt5_1_21_F4)
    (hnot : ¬ Concl5_1_14_four T L V B D n)
    (hU : IsElemAbelian 2 (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G)))))
    {A : Subgroup (MulAut ↥(tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G)))))}
    (hA : A ∈ @QhatStar _ (commGroupOfElemAbelian hU) _
      (autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
        (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))))))
    (hlt : qhatInt (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))) hU < 2)
    (hAC : A ≤ Subgroup.centralizer (autOn (tildeOf Z₁ (oTwoUpper H))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))) :
      Set (MulAut ↥(tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
        (Subgroup.centralizer (Z₁ : Set G))))))) : False := by
  let := commGroupOfElemAbelian hU
  have hV : ∀ v : ↥(tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G)))), v ^ 2 = 1 :=
    fun v => Subtype.ext (by simpa using hU.2 v v.2)
  have hlt' : qhatOf (autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))))) <
      (2 : WithTop ℚ) := hlt
  obtain ⟨r, hr'⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt')
  have hr2 : r < 2 := by
    rw [← hr'] at hlt'
    have h' : ((r : ℚ) : WithTop ℚ) < ((2 : ℚ) : WithTop ℚ) := by simpa using hlt'
    exact WithTop.coe_lt_coe.mp h'
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hAC₁ : A ≤ autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G) ⊓
      centralizerModO2 (oTwoUpper H)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))) :=
    fun a ha => s.mem_autOn_C₁_of_mem_centralizer_F4 h5114 hF h521 hnot (hA2.1 ha) (hAC ha)
  have hG₁C₁ : Subgroup.centralizer (Z₁ : Set G) ≤ Subgroup.normalizer
      ((Subgroup.centralizer (Z₁ : Set G) ⊓ centralizerModO2 (oTwoUpper H) : Subgroup G) :
        Set G) := by
    intro g hg
    have hgK := (s.centralizer_Z₁_le_normalizer_K_F4 h5114) hg
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg)
    have h2 := Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_centralizerModO2 (oTwoUpper H) hgK)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => ⟨(h1 y).mp hy.1, (h2 y).mp hy.2⟩,
      fun hy => ⟨(h1 y).mpr hy.1, (h2 y).mpr hy.2⟩⟩
  obtain ⟨Lc, hLcC, hLc, hLq, hLA⟩ := exists_cComp_of_mem_QhatStar hV hr'.symm hr2 hA
    (autOn_le_autOn _ (tildeOf_mono inf_le_left))
    (autOn_le_normalizer_autOn_of_normalizes (tildeOf_le_normalizer_tildeOf hG₁C₁))
    (s.pCoreOf_autOn_G₁_eq_bot_F4 h5114 hF) (s.not_three_dvd_card_autOn_C₁_F4 h516) hAC₁
  exact false_of_qhatStar_of_suzuki h38 hV (s.isQuotientOfSQTK_autOn_G₁_F4 h5114) hr'.symm hr2 hA
    hLc hLq (s.suzukiModel_of_le_autOn_C₁_F4 h5114 h516 hA23 hSzF hLcC hLq) hLA

end Setup521

end Setting

theorem stmt5_1_23_faithful_sz_of_F4
    (h38 : D38Top) (hA23 : A23SQTKListFact) (hSzF : SimpleThreePrimeSuzukiFact)
    (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) (h516 : Stmt5_1_16_F4) (h520 : Stmt5_1_20_F4)
    (h521 : Stmt5_1_21_F4) : Stmt5_1_23_faithful_sz_F4 := by
  intro G _ _ T M L V H B D D₃ Z₁ n hyp not59 hmod hl34 hnot hD₃ h3 hz1 hU A hA hlt _ hAC
  have s : Setup521 G T M L V H B D D₃ Z₁ n :=
    ⟨⟨hyp, not59, hmod, hl34⟩, hD₃, h3,
      (h520 G T M L V H B D n hyp not59 hmod hl34 hnot D₃ hD₃ h3).1, hz1⟩
  exact s.false_of_le_centralizer_of_D38_F4 h38 hA23 hSzF h5114 hF h516 h521 hnot hU hA hlt hAC

theorem stmt5_1_23_faithful_of_D38_F4
    (h38 : D38Top) (hA23 : A23SQTKListFact) (hSzF : SimpleThreePrimeSuzukiFact)
    (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) (h516 : Stmt5_1_16_F4) (h520 : Stmt5_1_20_F4)
    (h521 : Stmt5_1_21_F4) : Stmt5_1_23_faithful_F4 :=
  stmt5_1_23_faithful_of_F4 h5114 hF h516 h520 h521
    (stmt5_1_23_faithful_sz_of_F4 h38 hA23 hSzF h5114 hF h516 h520 h521)

theorem stmt5_1_23_of_D38_F4
    (h5114 : Stmt5_1_14_first_F4) (h510 : Stmt5_1_10_F4) (h516 : Stmt5_1_16_F4) (h520 : Stmt5_1_20_F4)
    (h521 : Stmt5_1_21_F4) (hF : L2TorusFact) (hD : D310L34Fact) (hB : B45L34Fact)
    (hoff : Stmt5_1_23_offender_F4) (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : SimpleThreePrimeSuzukiFact) : Stmt5_1_23_F4 :=
  stmt5_1_23_of_inputs_F4 h5114 h510 h520 h521 hF hD hB hoff
    (stmt5_1_23_faithful_of_D38_F4 h38 hA23 hSzF h5114 hF h516 h520 h521)

end CFSG.Quasithin.H13
