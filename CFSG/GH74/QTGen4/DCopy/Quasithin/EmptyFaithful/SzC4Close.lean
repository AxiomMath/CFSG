module

public import CFSG.Quasithin.EmptyFaithful.SzC4Close
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SBd4Close
public import CFSG.GH74.QTGen4.DCopy.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
open scoped commutatorElement Pointwise

namespace SzC4

section Main

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

open CFSG.Quasithin.S153D in

theorem exists_c134CaseCorr_of_ctx_S_F4 (hMS : MS93.AS_C_1_34_corr_F4) {T Mc M V₁ V₂ Yp I L : Subgroup G}
    {t : G} (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G)) :
    ∃ i : ℕ, MS93.IsC134CaseCorr i (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L := by
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hMSp : IsMSPair (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) := isMSPair_sup_S c hq hV hYY hSL
  have hcomp : L ∈ cComp (L ⊔ Sgp153 T V₁) := SBd5.mem_cComp_sup' hLI hSL
  have hset : ((L ⊔ Sgp153 T V₁ : Subgroup G) : Set G) = (L : Set G) * (Sgp153 T V₁ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L _ hSL
  obtain ⟨e⟩ := hq
  let α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hα : IsModO2Surj L α := by
    refine ⟨e.surjective.comp (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)), ?_⟩
    show (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).ker = CFSG.pCore 2 ↥L
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) e.toMonoidHom
      e.injective, QuotientGroup.ker_mk']
  exact hMS G (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L hMSp hcomp hset
    ⟨1, ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩

open CFSG.Quasithin.S153D in

theorem l3ClosingQ_holds_corr_F4 (hMS : MS93.AS_C_1_34_corr_F4) (hN : L3YCCommNotCentral)
    (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK) : L3ClosingQ_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hq c12 hV hYY hSL t' ht'T ht'S hswap
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  obtain ⟨hLc, hLn, -, -, -, hLq⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  have hYpL : Yp ≤ Subgroup.normalizer (L : Set G) := Yp_le_normalizer h37 h38 hh c.ctx.inH hLI
  have hRN : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := c.c16.R_norm
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp :=
    pCoreOf_sup_R153_le c.facts hLI hLq hRN
  have hlab := SBd5.l3YLLabel_of_l3 h113 h37 h38 SBd3.l3SolvableOverSylow_holds G T Mc M V₁ V₂ Yp
    I L t c hq c12 hV hYY
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp hh.decomp
  have hSV₁ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₁ : Set G) := inf_le_right
  have hSV₂ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) := by
    obtain ⟨hc1, -⟩ := szN3_conj_V_swap hyp hh.decomp ht'T ht'S
    intro s hs
    have h1 : t'⁻¹ * s * t' ∈ Sgp153 T V₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hTS (inv_mem ht'T)) s).mp hs
      simpa using this
    rw [← hc1]
    exact SBd4.mem_normalizer_conjSub (hSV₁ h1)
  have hSYL : Sgp153 T V₁ ≤ Subgroup.normalizer (YL153 Yp L : Set G) := by
    rcases hlab with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact szN3_S_le_normalizer_oTwoUpper hyp inf_le_left hSV₁
    · rw [h1]; exact szN3_S_le_normalizer_oTwoUpper hyp inf_le_left hSV₂
  have hidx : (Sgp153 T V₁).relIndex T = 2 := hh.decomp.relIndex_nS hyp
  have hprod : ∀ a ∈ T, ∀ b ∈ T, a ∉ Sgp153 T V₁ → b ∉ Sgp153 T V₁ → a * b ∈ Sgp153 T V₁ := by
    intro a ha b hb haS hbS
    have h2 : ((Sgp153 T V₁).subgroupOf T).index = 2 := hidx
    have h3 := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    have hiff : (⟨a, ha⟩ * ⟨b, hb⟩ : ↥T) ∈ (Sgp153 T V₁).subgroupOf T := by
      rw [h3]
      exact iff_of_false (fun h => haS h) (fun h => hbS h)
    exact hiff
  have ht'2 : t' * t' ∈ Sgp153 T V₁ := hprod t' ht'T t' ht'T ht'S ht'S

  have hTRn : Yp ⊔ T ≤ Subgroup.normalizer (R153 T V₁ Yp : Set G) :=
    (Hyp15310.lemma_15_3_11_five_case_one h113 hh hYY).2.2.1
  have hR2 : IsPGroup 2 ↥(R153 T V₁ Yp) := pCoreOf_isPGroup 2 (Yp ⊔ Sgp153 T V₁)
  have hRS : R153 T V₁ Yp ≤ Sgp153 T V₁ := by
    intro r hr
    have hr' := c.facts.R_eq ▸ hr
    refine ⟨hr'.1, ?_⟩
    have h1 : r ∈ Subgroup.centralizer (V₁ : Set G) :=
      Subgroup.centralizer_le hh.decomp.le₁ hr'.2
    exact Subgroup.centralizer_le_normalizer (V₁ : Set G) h1
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hyp.qtfe.sylow.1.to_le inf_le_left
  have hSTle : Sgp153 T V₁ ≤ T := inf_le_left
  set R : Subgroup G := R153 T V₁ Yp with hR
  set O : Subgroup G := pCoreOf 2 (L ⊔ R) with hOdef
  set Q : Subgroup G := ⁅O, L⁆ with hQ
  set W : Subgroup G := WL153 T M L with hW
  have hOL : L ≤ Subgroup.normalizer (O : Set G) := fun l hl =>
    le_normalizer_pCoreOf 2 (L ⊔ R) (Subgroup.mem_sup_left hl)
  have hYpR : Yp ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hTRn
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := le_sup_right.trans hTRn
  have hNO : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) → g ∈ Subgroup.normalizer (R : Set G) →
      g ∈ Subgroup.normalizer (O : Set G) := fun g h1 h2 =>
    normalizer_le_normalizer_pCoreOf 2 (L ⊔ R)
      (Subgroup.inf_normalizer_le_normalizer_sup L R ⟨h1, h2⟩)
  have hQO : Q ≤ O := by
    refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    have h1 : l * x⁻¹ * l⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hOL hl) _).mp (O.inv_mem hx)
    have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
    rw [commutatorElement_def, e]
    exact O.mul_mem hx h1
  have hQR : Q ≤ R := hQO.trans hO
  have hQS : Q ≤ Sgp153 T V₁ := hQR.trans hRS
  have hRQ : R ≤ Subgroup.normalizer (Q : Set G) := fun r hr =>
    SBd5.mem_normalizer_commutator_of (hNO r (hRN hr) (Subgroup.le_normalizer hr)) (hRN hr)
  have hSQ : Sgp153 T V₁ ≤ Subgroup.normalizer (Q : Set G) := fun s hs =>
    SBd5.mem_normalizer_commutator_of (hNO s (hSL hs) (hTR (hSTle hs))) (hSL hs)
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := fun l hl =>
    SBd5.mem_normalizer_commutator_of (hOL hl) (Subgroup.le_normalizer hl)
  have hWc : W ≤ centerOf O := WL_le_centerOf hh c.ctx c.facts hLI hO
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := fun l hl =>
    le_normalizer_conjClosure (VZ T M) L hl
  have hWab : IsElemAbelian 2 W := c.c16.reduced_LR.2.2.1
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => by
    have := hWab.1
    exact setLike_mul_comm hx hy
  have hUQ : ⁅W, L⁆ ≤ Q := Subgroup.commutator_mono (fun x hx => (hWc hx).1) le_rfl
  have hUW : ⁅W, L⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hLW
  have hUc : ∀ u ∈ ⁅W, L⁆, ∀ q ∈ Q, u * q = q * u := fun u hu q hq' =>
    (Subgroup.mem_centralizer_iff.mp (hWc (hUW hu)).2 q (hQO hq')).symm
  have hVab : ∀ a ∈ VZ T M, ∀ b ∈ VZ T M, a * b = b * a := fun a ha b hb => by
    have := hyp.elemAbelian.1
    exact setLike_mul_comm ha hb
  have hYLle : YL153 Yp L ≤ Yp ⊓ L := oTwoUpper_le _
  have hYL153 : YL153 Yp L ≤ Y153 Mc M := (hYLle.trans inf_le_left).trans (le_of_eq hYY)

  have hx₀ : ∃ x₀ ∈ ⁅W, L⁆, x₀ ≠ 1 ∧ ∀ y ∈ YC153 Yp L, y * x₀ * y⁻¹ = x₀ := by
    have hVLU : ⁅VZ T M, YL153 Yp L⁆ ≤ ⁅W, L⁆ :=
      Subgroup.commutator_mono (le_conjClosure (VZ T M) L) (hYLle.trans inf_le_right)
    have hYLN := Hyp153.Y153_le_normalizer_V h113 hyp hh.decomp
    have hVn : ∃ Vn : Subgroup G, ⁅VZ T M, YL153 Yp L⁆ ≤ Vn ∧
        YC153 Yp L ≤ Subgroup.centralizer (Vn : Set G) := by
      rcases hlab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨V₂, SBd6.comm_le_of_decomp hVab hh.decomp.sup ?_ (fun y hy => hYLN.2 (hYL153 hy)), ?_⟩
        · rw [h1]; exact (oTwoUpper_le _).trans inf_le_right
        · rw [h2]; exact (oTwoUpper_le _).trans inf_le_right
      · refine ⟨V₁, SBd6.comm_le_of_decomp hVab (by rw [sup_comm]; exact hh.decomp.sup) ?_
          (fun y hy => hYLN.1 (hYL153 hy)), ?_⟩
        · rw [h1]; exact (oTwoUpper_le _).trans inf_le_right
        · rw [h2]; exact (oTwoUpper_le _).trans inf_le_right
    obtain ⟨Vn, hcomm, hYCc⟩ := hVn
    obtain ⟨x₀, hx₀mem, hx₀ne⟩ : ∃ x₀ ∈ ⁅VZ T M, YL153 Yp L⁆, x₀ ≠ 1 := by
      by_contra h
      push Not at h
      exact hV (eq_bot_iff.mpr (fun x hx => Subgroup.mem_bot.mpr (h x hx)))
    refine ⟨x₀, hVLU hx₀mem, hx₀ne, fun y hy => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp (hYCc hy) x₀ (hcomm hx₀mem)
    calc y * x₀ * y⁻¹ = x₀ * y * y⁻¹ := by rw [← this]
      _ = x₀ := by group
  have hyfacts : ∀ y ∈ centralizerSection Yp L (pCoreOf 2 L), y ∈ Subgroup.normalizer (L : Set G) ∧
      y ∈ Subgroup.normalizer (Q : Set G) ∧ (∀ x ∈ L, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L) := by
    intro y hy
    obtain ⟨hyYp, hyL, -, hyc⟩ := hy
    exact ⟨hyL, SBd5.mem_normalizer_commutator_of (hNO y hyL (hYpR hyYp)) hyL, hyc⟩
  have hbotN : ∀ g : G, g ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro g
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp [Subgroup.mem_bot]

  have hy3 : ∃ y₃ ∈ YL153 Yp L, orderOf y₃ = 3 := by
    have h3 : 3 ∣ Nat.card ↥(YL153 Yp L) := dvd_of_one_le_padicValNat (by rw [c12.2.1])
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    exact ⟨x, x.2, by rw [← Subgroup.orderOf_coe] at hx; exact hx⟩

  have hQ'R : ∀ q' ∈ B6.conjSub t' Q, q' ∈ R := by
    intro q' hq'
    have hq : t'⁻¹ * q' * t' ∈ Q := B6.mem_conjSub.mp hq'
    have h1 : t'⁻¹ * q' * t' ∈ R := hQR hq
    have h2 := (Subgroup.mem_normalizer_iff.mp (hTR ht'T) _).mp h1
    have e : t' * (t'⁻¹ * q' * t') * t'⁻¹ = q' := by group
    rwa [e] at h2

  have hold : (∀ y ∈ centralizerSection Yp L (pCoreOf 2 L), Odd (orderOf y) →
        ∀ q ∈ Q, y * q * y⁻¹ = q) →
      (∃ (n k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (C : Subgroup G)
        (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)), 0 < k ∧ Fintype.card F = 2 ^ n ∧
          IsModO2Surj L α ∧ IsSumOfNaturalModulesVia L Q C α false k ∧
          (∀ g : G, g ∈ Subgroup.normalizer (Q : Set G) → g ∈ Subgroup.normalizer (L : Set G) →
            g ∈ Subgroup.normalizer (C : Set G))) →
      ∀ q' ∈ B6.conjSub t' Q, ∀ l ∈ L, q' * l * q'⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    rintro hYCgen ⟨n, k, F, _, _, C, α, hk0, hFc, hα, hZ, hCN⟩

    have hYCQ : YC153 Yp L ≤ Subgroup.centralizer (Q : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hyX, hyodd⟩
      refine Subgroup.mem_centralizer_iff.mpr fun q hq' => ?_
      have := hYCgen y hyX hyodd q hq'
      calc q * y = (y * q * y⁻¹) * y := by rw [this]
        _ = y * q := by group

    have hYLQ' : ∀ y ∈ YL153 Yp L, ∀ q' ∈ B6.conjSub t' Q, q' * y = y * q' := by
      intro y hy q' hq'
      have hq : t'⁻¹ * q' * t' ∈ Q := B6.mem_conjSub.mp hq'
      have hyC : t'⁻¹ * y * t' ∈ YC153 Yp L := by
        rw [← hswap, B6.mem_conjSub]
        have e : t'⁻¹ * (t'⁻¹ * y * t') * t' = (t' * t')⁻¹ * y * (t' * t') := by
          simp only [mul_inv_rev, mul_assoc]
        rw [e]
        exact (Subgroup.mem_normalizer_iff''.mp (hSYL ht'2) y).mp hy
      have hcomm := Subgroup.mem_centralizer_iff.mp (hYCQ hyC) (t'⁻¹ * q' * t') hq
      calc q' * y = t' * ((t'⁻¹ * q' * t') * (t'⁻¹ * y * t')) * t'⁻¹ := by group
        _ = t' * ((t'⁻¹ * y * t') * (t'⁻¹ * q' * t')) * t'⁻¹ := by rw [hcomm]
        _ = y * q' := by group
    intro q' hq'
    obtain ⟨y₃, hy₃, hy₃3⟩ := hy3
    have hq'R := hQ'R q' hq'
    have hr2 : ∃ m : ℕ, q' ^ (2 ^ m) = 1 := by
      obtain ⟨m, hm⟩ := hR2 ⟨q', hq'R⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    exact SBd6.comm_mem_pCore_of_module hk0 hFc hα hq hZ (hRQ hq'R) (hRN hq'R)
      (hCN q' (hRQ hq'R) (hRN hq'R)) (hYLle hy₃).2 (hYLQ' y₃ hy₃ q' hq') hy₃3 hr2

  have hΩ : ∀ n' ∈ Sgp153 T V₁, (∀ s ∈ Sgp153 T V₁, s * n' * s⁻¹ = n') → n' * n' = 1 →
      n' ∈ VZ T M := by
    intro n' hn' hnc hn2
    have h8 := (hyp.lemma_15_3_8 hh.decomp).1
    have hmem : n' ∈ omegaOneCenterOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) :=
      Subgroup.subset_closure ⟨⟨hn', Subgroup.mem_centralizer_iff.mpr fun s hs => by
        have := hnc s hs
        exact mul_inv_eq_iff_eq_mul.mp this⟩, by rw [pow_two]; exact hn2⟩
    rw [h8] at hmem
    exact hmem.1

  have hCnt : ⁅VZ T M, YC153 Yp L⁆ ≠ ⊥ := by
    intro hb
    apply hV
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun v hv y hy => ?_
    have hMN := hyp.le_normalizer (hyp.T_le ht'T)
    have hv' : t' * v * t'⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hMN v).mp hv
    have hy' : t' * y * t'⁻¹ ∈ YC153 Yp L := by
      rw [← hswap, B6.mem_conjSub]
      have e : t'⁻¹ * (t' * y * t'⁻¹) * t' = y := by group
      rw [e]
      exact hy
    have h1 : ⁅t' * v * t'⁻¹, t' * y * t'⁻¹⁆ ∈ (⊥ : Subgroup G) :=
      hb ▸ Subgroup.commutator_mem_commutator hv' hy'
    rw [Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    have e : ⁅v, y⁆ = t'⁻¹ * ⁅t' * v * t'⁻¹, t' * y * t'⁻¹⁆ * t' := by
      simp only [commutatorElement_def]
      group
    rw [e, h1]
    group
  have hYLgen : ∀ K : Subgroup G, (∀ y ∈ YL153 Yp L, Odd (orderOf y) → y ∈ K) →
      YL153 Yp L ≤ K := by
    intro K hK
    refine (Subgroup.closure_le K).mpr ?_
    rintro y ⟨hyX, hyodd⟩
    exact hK y (mem_oTwoUpper_of_odd hyX hyodd) hyodd
  have hYCgen : ∀ K : Subgroup G, (∀ y ∈ YC153 Yp L, Odd (orderOf y) → y ∈ K) →
      YC153 Yp L ≤ K := by
    intro K hK
    refine (Subgroup.closure_le K).mpr ?_
    rintro y ⟨hyX, hyodd⟩
    exact hK y (mem_oTwoUpper_of_odd hyX hyodd) hyodd
  have hsqV : ∀ a ∈ VZ T M, a * a = 1 := fun a ha => by
    have := hyp.elemAbelian.2 a ha
    rw [pow_two] at this
    exact this
  have hVfix : ∀ n' ∈ VZ T M, (∀ y ∈ YL153 Yp L, y * n' * y⁻¹ = n') →
      (∀ y ∈ YC153 Yp L, y * n' * y⁻¹ = n') → n' = 1 := by
    have hYLN := Hyp153.Y153_le_normalizer_V h113 hyp hh.decomp
    rcases hlab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine fixed_in_V_false hh.decomp.sup hVab hh.decomp.card₁ hh.decomp.card₂ hsqV ?_ ?_ ?_ ?_
        hYLgen hYCgen hV hCnt
      · rw [h1]; exact (oTwoUpper_le _).trans inf_le_right
      · exact fun y hy => hYLN.2 (hYL153 hy)
      · rw [h2]; exact (oTwoUpper_le _).trans inf_le_right
      · intro y hy
        apply hYLN.1
        rw [h2] at hy
        exact ((oTwoUpper_le _).trans inf_le_left) hy
    · refine fixed_in_V_false (by rw [sup_comm]; exact hh.decomp.sup) hVab hh.decomp.card₂
        hh.decomp.card₁ hsqV ?_ ?_ ?_ ?_ hYLgen hYCgen hV hCnt
      · rw [h1]; exact (oTwoUpper_le _).trans inf_le_right
      · exact fun y hy => hYLN.1 (hYL153 hy)
      · rw [h2]; exact (oTwoUpper_le _).trans inf_le_right
      · intro y hy
        apply hYLN.2
        rw [h2] at hy
        exact ((oTwoUpper_le _).trans inf_le_left) hy

  obtain ⟨i, hi⟩ := exists_c134CaseCorr_of_ctx_S_F4 hMS c hq hV hYY hSL
  have hQeq : c134Q (L ⊔ Sgp153 T V₁) L = Q := by
    rw [c134Q_sup_eq hperf hSL hRN]
    rfl
  have hQ'comm : ∀ q' ∈ B6.conjSub t' Q, ∀ l ∈ L, q' * l * q'⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    match i, hi with
    | 0, hi => exact hi.elim
    | 1, hi =>
      obtain ⟨-, n, F, _, _, hFc, hNS⟩ := hi
      obtain ⟨α, hαs, hαk, hZ⟩ :=
        (isNaturalSection_iff_isSumOfNaturalModules_one (CFSG.pCore 2 ↥L)
          (CFSG.Assembly.LowTwoRank.StatedSL 3 F) bot_le).mp hNS
      rw [hQeq] at hZ
      refine hold (fun y hy hodd => ?_) ⟨n, 1, F, inferInstance, inferInstance, ⊥, α, Nat.one_pos,
        hFc, ⟨hαs, hαk⟩, hZ, fun g _ _ => hbotN g⟩
      obtain ⟨hyL, hyQ, hyc⟩ := hyfacts y hy
      obtain ⟨x₀, hx₀U, hx₀ne, hx₀fix⟩ := hx₀
      rcases SBd5.kc_of_module (A := Q) (Or.inl rfl) hFc ⟨hαs, hαk⟩ hq hZ hyQ hyL hyc hodd le_rfl
        with h | h
      · exact h
      · exact fun q _ => (hx₀ne (h x₀ (hUQ hx₀U) (hx₀fix y (mem_oTwoUpper_of_odd hy hodd)))).elim
    | 2, hi =>
      obtain ⟨⟨n, F, _, _, α, hFc, hα, hZ⟩, -⟩ := hi
      rw [hQeq] at hZ
      refine hold (fun y hy hodd => ?_) ⟨n, 2, F, inferInstance, inferInstance, ⊥, α, Nat.two_pos,
        hFc, hα, hZ, fun g _ _ => hbotN g⟩
      obtain ⟨hyL, hyQ, hyc⟩ := hyfacts y hy
      obtain ⟨x₀, hx₀U, hx₀ne, hx₀fix⟩ := hx₀
      rcases SBd5.kc_of_module (A := Q) (Or.inr rfl) hFc hα hq hZ hyQ hyL hyc hodd le_rfl
        with h | h
      · exact h
      · exact fun q _ => (hx₀ne (h x₀ (hUQ hx₀U) (hx₀fix y (mem_oTwoUpper_of_odd hy hodd)))).elim
    | 3, hi =>
      obtain ⟨⟨n, F, _, _, α, hFc, hα, hZ1, hZ2⟩, -⟩ := hi
      rw [hQeq] at hZ1 hZ2
      have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
      obtain ⟨x₀, hx₀U, hx₀ne, hx₀fix⟩ := hx₀
      have hx₀Z : x₀ ∈ centerOf Q := ⟨hUQ hx₀U, Subgroup.mem_centralizer_iff.mpr fun q hq' =>
        (hUc x₀ hx₀U q hq').symm⟩

      have hYCZ : ∀ y ∈ YC153 Yp L, ∀ z ∈ centerOf Q, y * z * y⁻¹ = z := by
        have hcl : YC153 Yp L ≤ Subgroup.centralizer ((centerOf Q : Subgroup G) : Set G) := by
          refine (Subgroup.closure_le _).mpr ?_
          rintro y ⟨hyX, hyodd⟩
          obtain ⟨hyL, hyQ, hyc⟩ := hyfacts y hyX
          have hyZ : y ∈ Subgroup.normalizer ((centerOf Q : Subgroup G) : Set G) :=
            Subgroup.inf_normalizer_le_normalizer_inf
              ⟨hyQ, S153F.mem_normalizer_centralizer_of_mem_normalizer hyQ⟩
          rcases SBd5.kc_of_module (A := centerOf Q) (Or.inl rfl) hFc hα hq hZ1 hyZ hyL hyc hyodd
            le_rfl with h | h
          · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
            have := h z hz
            exact (mul_inv_eq_iff_eq_mul.mp this).symm
          · exact absurd (h x₀ hx₀Z (hx₀fix y (mem_oTwoUpper_of_odd hyX hyodd))) hx₀ne
        intro y hy z hz
        have := Subgroup.mem_centralizer_iff.mp (hcl hy) z hz
        calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [← this]
          _ = z := by group
      have hYLL : YL153 Yp L ≤ L := fun y hy => (hYLle hy).2
      have hYLQ : YL153 Yp L ≤ Subgroup.normalizer (Q : Set G) := fun y hy =>
        SBd5.mem_normalizer_commutator_of
          (hNO y (Subgroup.le_normalizer (hYLle hy).2) (hYpR (hYLle hy).1))
          (Subgroup.le_normalizer (hYLle hy).2)
      have hQYLN : Q ≤ Subgroup.normalizer (YL153 Yp L : Set G) := fun q hq' => hSYL (hQS hq')
      have hQYL : Q ≤ YL153 Yp L :=
        case3_Q_le_of_fixed hF hα hZ1 hZ2 hS2 hQS hSQ hSYL hYLL hYLQ hQYLN hΩ hVfix hYCZ
      intro q' hq' l hl
      have hq'YC : q' ∈ YC153 Yp L := by
        rw [← hswap, B6.mem_conjSub]
        exact hQYL (B6.mem_conjSub.mp hq')
      have hq'CS : q' ∈ centralizerSection Yp L (pCoreOf 2 L) := oTwoUpper_le _ hq'YC
      obtain ⟨-, -, hyc⟩ := hyfacts q' hq'CS
      have h1 := (pCoreOf 2 L).inv_mem (hyc l hl)
      have e : (l * q' * l⁻¹ * q'⁻¹)⁻¹ = q' * l * q'⁻¹ * l⁻¹ := by group
      rwa [e] at h1
    | 4, hi =>
      exfalso
      have hi4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L := hi
      obtain ⟨⟨n, F, _, _, α, hFc, hα, hE2, -, hCU, hU, -⟩, -⟩ := hi
      unfold c134CQ at hE2
      rw [hQeq] at hE2
      have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
      have hn1 : n = 1 := by
        have h2 : 2 ^ n = 2 ^ 1 := by rw [← hFc, hF]; norm_num
        exact Nat.pow_right_injective (le_refl 2) h2
      subst hn1
      obtain ⟨hC4', hCsq'⟩ := isE2_card_sq hE2
      have hC4 : Nat.card ↥(Q ⊓ Subgroup.centralizer (L : Set G)) = 4 := by
        rw [hC4']
        norm_num
      have hCsq : ∀ c ∈ Q ⊓ Subgroup.centralizer (L : Set G), c * c = 1 := fun c hc =>
        congrArg Subtype.val (hCsq' ⟨c, hc⟩)
      have hC1 : Q ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
        intro hb
        rw [hb, Subgroup.card_bot] at hC4
        omega
      have hSC : Sgp153 T V₁ ≤
          Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
        fun s hs => Subgroup.inf_normalizer_le_normalizer_inf ⟨hSQ hs,
          S153F.mem_normalizer_centralizer_of_mem_normalizer (hSL hs)⟩
      obtain ⟨c₀, hc₀C, hc₀1, hc₀sq, hc₀S⟩ :=
        SzC4.exists_fixed_involution hS2 (inf_le_left.trans hQS) hSC hC1 hCsq
      have hc₀V : c₀ ∈ VZ T M :=
        hΩ c₀ (inf_le_left.trans hQS hc₀C) (fun s hs => mul_inv_eq_iff_eq_mul.mpr (hc₀S s hs)) hc₀sq
      have hYLL : YL153 Yp L ≤ L := fun y hy => (hYLle hy).2
      have hc₀YL : ∀ y ∈ YL153 Yp L, y * c₀ * y⁻¹ = c₀ := fun y hy =>
        mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hc₀C.2 y (hYLL hy))

      have hYLN := Hyp153.Y153_le_normalizer_V h113 hyp hh.decomp
      obtain ⟨Vc, Vn, hsup, hc4, hn4, hYLc, hYLn, hYCn, hYCc⟩ : ∃ Vc Vn : Subgroup G,
          Vc ⊔ Vn = VZ T M ∧ Nat.card Vc = 4 ∧ Nat.card Vn = 4 ∧
          YL153 Yp L ≤ Subgroup.centralizer (Vc : Set G) ∧
          YL153 Yp L ≤ Subgroup.normalizer (Vn : Set G) ∧
          YC153 Yp L ≤ Subgroup.centralizer (Vn : Set G) ∧
          YC153 Yp L ≤ Subgroup.normalizer (Vc : Set G) := by
        rcases hlab with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine ⟨V₁, V₂, hh.decomp.sup, hh.decomp.card₁, hh.decomp.card₂, ?_,
            fun y hy => hYLN.2 (hYL153 hy), ?_, ?_⟩
          · rw [h1]; exact (oTwoUpper_le _).trans inf_le_right
          · rw [h2]; exact (oTwoUpper_le _).trans inf_le_right
          · intro y hy
            apply hYLN.1
            rw [h2] at hy
            exact ((oTwoUpper_le _).trans inf_le_left) hy
        · refine ⟨V₂, V₁, by rw [sup_comm]; exact hh.decomp.sup, hh.decomp.card₂,
            hh.decomp.card₁, ?_, fun y hy => hYLN.1 (hYL153 hy), ?_, ?_⟩
          · rw [h1]; exact (oTwoUpper_le _).trans inf_le_right
          · rw [h2]; exact (oTwoUpper_le _).trans inf_le_right
          · intro y hy
            apply hYLN.2
            rw [h2] at hy
            exact ((oTwoUpper_le _).trans inf_le_left) hy
      have hc₀Vc : c₀ ∈ Vc :=
        SzC4.fixed_mem_Vc hsup hVab hn4 hsqV hYLc hYLn hYLgen hV hc₀V hc₀YL

      have hYCC : ∀ y ∈ YC153 Yp L, ∀ x ∈ Q ⊓ Subgroup.centralizer (L : Set G),
          y * x * y⁻¹ ∈ Q ⊓ Subgroup.centralizer (L : Set G) := by
        have hle : YC153 Yp L ≤
            Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
          refine (Subgroup.closure_le _).mpr ?_
          rintro y ⟨hyX, -⟩
          obtain ⟨hyL, hyQ, -⟩ := hyfacts y hyX
          exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hyQ,
            S153F.mem_normalizer_centralizer_of_mem_normalizer hyL⟩
        intro y hy x hx
        exact (Subgroup.mem_normalizer_iff.mp (hle hy) x).mp hx
      have hVcC : Vc ≤ Q ⊓ Subgroup.centralizer (L : Set G) :=
        SzC4.Vc_le_of_moved hsup hVab hc4 hsqV hYCn hYCc hYCgen hCnt hYCC hc₀C hc₀Vc hc₀1
      have hcomm : ⁅VZ T M, YC153 Yp L⁆ ≤ Vc :=
        SBd6.comm_le_of_decomp hVab (by rw [sup_comm]; exact hsup) hYCn hYCc
      refine hN G T Mc M V₁ V₂ Yp I L t c hq c12 hV hYY hSL t' ht'T ht'S hswap hi4 ?_
      intro x hx
      have hxC := hVcC (hcomm hx)
      rw [c134CQ, hQeq]
      exact hxC
    | 5, hi =>
      obtain ⟨⟨α, hα, hC2, hZ⟩, -⟩ := hi
      unfold c134CQ at hC2 hZ
      rw [hQeq] at hC2 hZ
      have hCcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a :=
        SBd6.case5_comm hα hZ hC2 inf_le_right hUQ hUc
          (fun l hl => SBd5.mem_normalizer_commutator_of (hLW hl) (Subgroup.le_normalizer hl))
          (SBd5.commutator_commutator_eq_self hperf hLW hWcomm)
          (by
            intro h0
            apply not_le_centralizer_WL hh hLle hLn
            have h1 : ⁅L, W⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h0
            exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)
      refine hold (fun y hy hodd => ?_) ⟨1, 1, ZMod 2, inferInstance, inferInstance,
        Q ⊓ Subgroup.centralizer (L : Set G), α, Nat.one_pos, by simp, hα, hZ, fun g hgQ hgL => ?_⟩
      · obtain ⟨hyL, hyQ, hyc⟩ := hyfacts y hy
        have hyC : y ∈ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
          Subgroup.inf_normalizer_le_normalizer_inf
            ⟨hyQ, S153F.mem_normalizer_centralizer_of_mem_normalizer hyL⟩
        exact SBd5.kc_of_module5 hα hC2 hZ hyQ hyC hyL hyc hodd le_rfl
          (fun a ha q hq' => hCcomm a ha q hq')
      · exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hgQ, S153F.mem_normalizer_centralizer_of_mem_normalizer hgL⟩
    | n + 6, hi => exact hi.elim
  have hcomm2 : ⁅B6.conjSub t' Q, L⁆ ≤ pCoreOf 2 L := by
    refine Subgroup.commutator_le.mpr fun q' hq' l hl => ?_
    exact hQ'comm q' hq' l hl
  have hcomm3 : ⁅⁅B6.conjSub t' Q, L⁆, L⁆ ≤ Q := by
    refine (Subgroup.commutator_mono hcomm2 le_rfl).trans ?_
    exact Subgroup.commutator_mono (pCoreOf_le_pCoreOf_sup hRN) le_rfl
  have hQ'N : B6.conjSub t' Q ≤ Subgroup.normalizer (Q : Set G) := fun q' hq' =>
    hRQ (hQ'R q' hq')
  exact SBd6.commutator_le_of_double_le hperf hQ'N hLQ hcomm3

end Main

end SzC4

end CFSG.Quasithin
