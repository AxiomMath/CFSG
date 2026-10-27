module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523F
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Inputs523Sz
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem523

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem almostSpecialHyp_G₁_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    AlmostSpecialHyp (conjClosure Z₁ D₃) Z₁ ⊥ T (Subgroup.centralizer (Z₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  obtain ⟨d, hd, hd1⟩ := s.exists_d
  have hTG₁ : T ≤ Subgroup.centralizer (Z₁ : Set G) :=
    s.hyp.hyp.hStar.1.1.trans (s.H_le_centralizer_F4 h5114)
  have hl1 : lOne (⊥ : Subgroup G) Z₁ = ⊥ := le_bot_iff.mp ((oTwoUpper_le _).trans inf_le_left)
  have hZ1T : Z₁ ≤ T := s.Z₁_le_Z.trans (quasithinOmegaOneCenter_le_self T)
  have hZ1O : Z₁ ≤ pCoreOf 2 (Subgroup.centralizer (Z₁ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hZ1T.trans hTG₁)
      (Subgroup.centralizer_le_normalizer _) (hh.sylow.1.to_le hZ1T)
  have hO₁ : pCoreOf 2 (Subgroup.centralizer (Z₁ : Set G)) ≠ ⊥ := fun hb => by
    have := hZ1O hz
    rw [hb, Subgroup.mem_bot] at this
    exact hz1 this
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq hh.sylow
  have hSG₁ : (S : Subgroup G) ≤ Subgroup.centralizer (Z₁ : Set G) := by rw [hS]; exact hTG₁
  exact
    { elemAbelian := s.isElemAbelian_V₂
      ne_bot := fun hb => hz1 (by rw [hb] at hz; exact Subgroup.mem_bot.mp hz)
      le_V := le_conjClosure Z₁ D₃
      oTwo_eq := (le_bot_iff.mp (oTwoUpper_le ⊥)).symm
      V_le_T := s.V₂_le_T
      T_le_normV₁ := s.T_le_normalizer_Z₁
      T_le_normV := s.T_le_normalizer_V₂ hF
      T_le_normL := fun t _ => Subgroup.mem_normalizer_iff.mpr fun x => by
        simp only [Subgroup.mem_bot]
        constructor
        · rintro rfl
          group
        · intro hx
          have e : x = t⁻¹ * (t * x * t⁻¹) * t := by group
          rw [e, hx]
          group
      sylow_LT := by
        rw [bot_sup_eq]
        exact hh.isSylowTwoOf le_rfl
      H_le := Subgroup.centralizer_le_normalizer _
      lOne_sup_le := by
        rw [hl1, bot_sup_eq]
        exact hTG₁
      sylow_H := hh.isSylowTwoOf hTG₁
      charTwo := charTwo_of_le hh.qtke.2.1 S hSG₁ le_rfl ⟨hSG₁, hO₁⟩
      irred := by
        rw [hl1, bot_sup_eq]
        exact ⟨s.Z₁_lt_V₂_F4 hz hz1 hd hd1 h5114, s.T_le_normalizer_V₂ hF, s.T_le_normalizer_Z₁,
          fun W hW1 hW2 _ => s.eq_or_eq_F4 hz hz1 hd hd1 h5114 hF hW1 hW2⟩ }

theorem pCoreOf_autOn_G₁_eq_bot_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    pCoreOf 2 (autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))))) = ⊥ :=
  Setup.pCoreOf_autOn_eq_bot (s.almostSpecialHyp_G₁_F4 h5114 hF).G22_four

theorem mem_autOn_C₁_of_mem_centralizer_F4
    (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) (h521 : Stmt5_1_21_F4)
    (hnot : ¬ Concl5_1_14_four T L V B D n)
    {a : MulAut ↥(tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G))))}
    (ha : a ∈ autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))))
    (hac : a ∈ Subgroup.centralizer (autOn (tildeOf Z₁ (oTwoUpper H))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))) :
      Set (MulAut ↥(tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
        (Subgroup.centralizer (Z₁ : Set G))))))) :
    a ∈ autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G) ⊓ centralizerModO2 (oTwoUpper H)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHG₁ : H ≤ Subgroup.centralizer (Z₁ : Set G) := s.H_le_centralizer_F4 h5114
  have hG₁K : Subgroup.centralizer (Z₁ : Set G) ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    s.centralizer_Z₁_le_normalizer_K_F4 h5114
  have hHN : H ≤ Subgroup.normalizer (Z₁ : Set G) := s.H_le_normalizer_Z₁_F4 h5114
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKN : oTwoUpper H ≤ Subgroup.normalizer (Z₁ : Set G) := hKH.trans hHN
  have hKG₁ : oTwoUpper H ≤ Subgroup.centralizer (Z₁ : Set G) := hKH.trans hHG₁
  have hG₁tU : tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)) ≤ Subgroup.normalizer
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))) :
        Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)) :=
    tildeOf_le_normalizer_tildeOf (le_normalizer_conjClosure _ _)
  have hUHtU : tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H) ≤
      tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))) :=
    tildeOf_mono (conjClosure_mono le_rfl hHG₁)
  have hHtUH : tildeOf Z₁ H ≤ Subgroup.normalizer
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H) :
        Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)) :=
    tildeOf_le_normalizer_tildeOf (le_normalizer_conjClosure _ H)
  have hker := s.ker_tildeAct_K_F4 le_rfl hHtUH (s.not_tildeOf_K_le_centralizer_F4 h5114 hF) h5114
    h521 hnot
  obtain ⟨⟨y, hyN⟩, hyG, rfl⟩ := Subgroup.mem_map.mp ha
  rw [Subgroup.mem_subgroupOf] at hyG
  obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hyG
  have hxK : (x : G) ∈ Subgroup.normalizer (oTwoUpper H : Set G) := hG₁K hx
  refine Subgroup.mem_map.mpr ⟨⟨tmk Z₁ x, hyN⟩, Subgroup.mem_subgroupOf.mpr
    (secMk_mem_secImg ⟨hx, hxK, normalizer_le_normalizer_pCoreOf 2 _ hxK, fun k hk => ?_⟩),
    rfl⟩

  have hkt : tmk Z₁ ⟨k, hKN hk⟩ ∈ tildeOf Z₁ (oTwoUpper H) := secMk_mem_secImg hk
  have hktN := hG₁tU (tildeOf_mono hKG₁ hkt)
  have hc := commutator_mem_centralizer_of_mem_centralizer_autOn hyN hac hkt hktN
  have hcK : (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ oTwoUpper H :=
    (oTwoUpper H).mul_mem ((Subgroup.mem_normalizer_iff.mp hxK k).mp hk)
      ((oTwoUpper H).inv_mem hk)
  have hcC : tmk Z₁ ⟨(x : G) * k * (x : G)⁻¹ * k⁻¹, hKN hcK⟩ ∈ Subgroup.centralizer
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H) :
        Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)) := by
    have e : tmk Z₁ ⟨(x : G) * k * (x : G)⁻¹ * k⁻¹, hKN hcK⟩ =
        tmk Z₁ x * tmk Z₁ ⟨k, hKN hk⟩ * (tmk Z₁ x)⁻¹ * (tmk Z₁ ⟨k, hKN hk⟩)⁻¹ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact Subgroup.centralizer_le hUHtU hc
  have hcmem : (⟨(x : G) * k * (x : G)⁻¹ * k⁻¹, hcK⟩ : ↥(oTwoUpper H)) ∈
      CFSG.pCore 2 ↥(oTwoUpper H) := by
    rw [← hker, mem_ker_tildeAct]
    exact hcC
  exact ⟨_, by rwa [← CFSG.pCore_eq_open], rfl⟩

theorem not_three_dvd_card_autOn_C₁_F4 (h516 : Stmt5_1_16_F4) :
    ¬ 3 ∣ Nat.card ↥(autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G) ⊓
      centralizerModO2 (oTwoUpper H)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))))) := by
  set N := Subgroup.normalizer (Z₁ : Set G) with hNdef
  set G₁ := Subgroup.centralizer (Z₁ : Set G) with hG₁def
  set C₁ := G₁ ⊓ centralizerModO2 (oTwoUpper H) with hC₁
  set Ut := tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) G₁) with hUt
  have hle : tildeOf Z₁ C₁ ≤ Subgroup.normalizer (Ut : Set _) :=
    (tildeOf_mono inf_le_left).trans
      (tildeOf_le_normalizer_tildeOf (le_normalizer_conjClosure _ G₁))
  intro h3
  apply (h516 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).1
  have e1 : Nat.card ↥(autOn (tildeOf Z₁ C₁) Ut) ∣ Nat.card ↥(tildeOf Z₁ C₁) := by
    have h := Subgroup.card_map_dvd ((tildeOf Z₁ C₁).subgroupOf
      (Subgroup.normalizer (Ut : Set _))) (conjAct Ut)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
    exact h
  have e2 : Nat.card ↥(tildeOf Z₁ C₁) ∣ Nat.card ↥C₁ := by
    have h := Subgroup.card_map_dvd (C₁.subgroupOf N) (secMk N Z₁)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans (Subgroup.centralizer_le_normalizer _))).toEquiv] at h
    exact h
  have e3 : Nat.card ↥C₁ ∣ Nat.card ↥(centralizerModO2 (oTwoUpper H)) :=
    Subgroup.card_dvd_of_le inf_le_right
  exact h3.trans (e1.trans (e2.trans e3))

theorem false_of_isSolvable_F4
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
    (hsolv : Group.IsSolvable ↥(autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G) ⊓
      centralizerModO2 (oTwoUpper H)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))))))
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
  exact false_of_le_of_isSolvable hV hr'.symm hr2 hA (autOn_le_autOn _ (tildeOf_mono inf_le_left))
    (autOn_le_normalizer_autOn_of_normalizes (tildeOf_le_normalizer_tildeOf hG₁C₁))
    (s.pCoreOf_autOn_G₁_eq_bot_F4 h5114 hF) (s.not_three_dvd_card_autOn_C₁_F4 h516) hsolv hAC₁

end Setup521

end Setting

theorem stmt5_1_23_faithful_of_F4
    (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) (h516 : Stmt5_1_16_F4) (h520 : Stmt5_1_20_F4)
    (h521 : Stmt5_1_21_F4) (hsz : Stmt5_1_23_faithful_sz_F4) : Stmt5_1_23_faithful_F4 := by
  intro G _ _ T M L V H B D D₃ Z₁ n hyp not59 hmod hl34 hnot hD₃ h3 hz1 hU A hA hlt
  have s : Setup521 G T M L V H B D D₃ Z₁ n :=
    ⟨⟨hyp, not59, hmod, hl34⟩, hD₃, h3,
      (h520 G T M L V H B D n hyp not59 hmod hl34 hnot D₃ hD₃ h3).1, hz1⟩
  by_cases hsolv : Group.IsSolvable ↥(autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G) ⊓
      centralizerModO2 (oTwoUpper H)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))))
  · exact fun hAC => s.false_of_isSolvable_F4 h5114 hF h516 h521 hnot hU hA hlt hsolv hAC
  · exact hsz G T M L V H B D D₃ Z₁ n hyp not59 hmod hl34 hnot hD₃ h3 hz1 hU A hA hlt hsolv

end CFSG.Quasithin.H13
