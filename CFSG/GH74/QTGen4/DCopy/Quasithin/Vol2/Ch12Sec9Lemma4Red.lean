module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Red
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneHat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneModel
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneSixStmt
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9List
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

@[expose] def Case1294Five_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1291 G T L V 4 →
    ∀ V₁ V₂ K₁ : Subgroup G, Setting1282One G T L V 4 V₁ V₂ → lOne L V₁ ≤ K₁ →
      quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) →
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
      ∀ D : HatModelU (u128 V V₁), G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))) →
        (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) ≤ 2 → False

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

open L1294 L1297 in

theorem lemma12_9_4_of_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h5 : Lemma12_8_8_five_F4)
    (h1293 : Lemma12_9_3K1_F4) (h12hat : Lemma12_8_12_hat_F4) (h13six : Lemma12_8_13_six_hat_F4)
    (hInsp : G112Inspect1294) (hFive : Case1294Five_F4) : Lemma12_9_4_F4 := by
  classical
  intro G _ _ T L V n hcx V₁ hV₁
  by_contra hU
  have h := hcx.hyp
  have hyp := h.hyp
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨hVT, hTV⟩ := hyp.le_and_normalizes_F4 h1222
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1

  obtain ⟨V₂, hV₂⟩ := exists_tsub hyp.sylow.1 hsq hab hTV hcard 2
    (by rcases hcx.n45 with h | h <;> omega)
  have hV₁₂ : V₁ ≤ V₂ := by
    rcases tinv_comparable_of_hyp1281One_F4 h1222 h hV₁.1 hV₂.1 hV₁.2.2 hV₂.2.2 with hle | hle
    · exact hle
    · exfalso
      have h1 := Subgroup.card_le_of_le hle
      rw [hV₁.2.1, hV₂.2.1] at h1
      norm_num at h1
  have hs : Setting1282One G T L V n V₁ V₂ := ⟨h, hV₁, hV₂, hV₁₂, hU⟩

  have hL₁n : ¬ Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer (lOne L V₁ : Set G) := fun h1 => by
    have := h5 G T L V n V₁ V₂ hs h1
    rcases hcx.n45 with h | h <;> omega

  obtain ⟨K₁, hLK, hK, hK₁n, hcases⟩ := h1293 G T L V n hcx V₁ hV₁
  have hlist : IsList1293Two (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨
      (n = 4 ∧ IsList1293Three (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :=
    hcases.resolve_left fun heq => hL₁n (heq ▸ hK₁n)
  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    le_of_mem_cComp (show K₁ ∈ cComp _ from hK)

  obtain ⟨D⟩ := hs.exists_hatModelU_F4 h1222 h12213
  set U := u128 V V₁ with hUdef
  have hA := hs.almostSpecial_F4 h1222 h12213
  have hG₁U : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_conjClosure V _
  have hK₁U : K₁ ≤ Subgroup.normalizer (U : Set G) := hK₁G₁.trans hG₁U
  have hZ : V₁ ≤ centerOf U := hs.le_centerOf_F4 h1222 h12213
  obtain ⟨g, hgP, hgN⟩ := exist1282g_F4 h1222 G T L V n h V₁ hV₁
  obtain ⟨a, haV₂, haV₁⟩ : ∃ a ∈ V₂, a ∉ V₁ := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show V₂ ≤ V₁ from fun x hx => hall x hx)
    rw [hV₁.2.1, hV₂.2.1] at h1
    norm_num at h1
  obtain ⟨-, hG111, hfix⟩ := h12hat G T L V n V₁ V₂ hs g hgP hgN a haV₂ haV₁ D
  set Γ := D.img (Subgroup.normalizer (V₁ : Set G)) with hΓ

  have hsqtk : IsQuotientOfSQTKTauCeti ↥Γ := by
    have := hyp.simple
    have hcore := CFSG.QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke
    have hP : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ ⊥ := by
      intro hb
      have h1 := LieType.BorelTits.le_pCoreOf_normalizer 2 V₁ (IsPGroup.of_card hV₁.2.1)
      rw [hb, le_bot_iff] at h1
      rw [h1, Subgroup.card_bot] at hV₁2
      norm_num at hV₁2
    exact isQuotientOfSQTK_img D hG₁U (hcore.1 _ hP)

  have hQtriv : ∀ q ∈ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)),
      ∀ hq : q ∈ Subgroup.normalizer (U : Set G), D.ρ ⟨q, hq⟩ = 1 := by
    intro q hqQ hq
    have hqN : q ∈ Subgroup.normalizer (V₁ : Set G) := LieType.BorelTits.pCoreOf_le 2 _ hqQ
    have hcomm : ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ V₁ := by
      intro u hu
      have hU' := hA.G22_one.2
      have huN : u ∈ Subgroup.normalizer (V₁ : Set G) := hA.conjClosure_le_N hu
      have hmemY := (secImg_le_iff.1 hU') ⟨u, huN⟩ hu
      have hqQ' : tmk V₁ ⟨q, hqN⟩ ∈ tildeOf V₁ (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) :=
        secMk_mem_secImg hqQ
      have hxy : tmk V₁ ⟨q, hqN⟩ * tmk V₁ ⟨u, huN⟩ = tmk V₁ ⟨u, huN⟩ * tmk V₁ ⟨q, hqN⟩ :=
        mem_centralizer_of_mem_omegaOneCenterOf hmemY hqQ'
      exact commutator_mem_of_secMk_commute hxy
    refine LinearEquiv.ext fun w => ?_
    obtain ⟨u, hu, rfl⟩ := D.π_surj w
    change D.ρ ⟨q, hq⟩ (D.π u) = D.π u
    rw [D.ρ_π ⟨q, hq⟩ u hu, D.π_eq_iff _ ((Subgroup.mem_normalizer_iff.1 hq u).1 hu) u hu]
    have hc := hcomm u hu
    have hcZ := hZ hc
    have e : (q * u * q⁻¹)⁻¹ * u = u⁻¹ * (q * u * q⁻¹ * u⁻¹)⁻¹ * u := by group
    rw [e]
    have hcZ' := (centerOf U).inv_mem hcZ
    have hcomm' := Subgroup.mem_centralizer_iff.1 hcZ'.2 u hu
    rw [show u⁻¹ * (q * u * q⁻¹ * u⁻¹)⁻¹ * u = (q * u * q⁻¹ * u⁻¹)⁻¹ by
      rw [mul_assoc, ← hcomm', ← mul_assoc, inv_mul_cancel, one_mul]]
    exact hcZ'

  set φK := D.ρ.comp (Subgroup.inclusion hK₁U) with hφK
  have hO₂K : CFSG.pCore 2 ↥K₁ ≤ φK.ker := by
    intro k hk
    have hk' : (k : G) ∈ pCoreOf 2 K₁ := by
      refine ⟨k, ?_, rfl⟩
      rw [SetLike.mem_coe, open_pCore_eq]
      exact hk
    have hK₁n' : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G) := hK₁n
    have hO₂ : pCoreOf 2 K₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((LieType.BorelTits.pCoreOf_le 2 K₁).trans hK₁G₁)
        (hK₁n'.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁))
        (LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
    rw [MonoidHom.mem_ker]
    exact hQtriv _ (hO₂ hk') _
  set ψ := QuotientGroup.lift (CFSG.pCore 2 ↥K₁) φK hO₂K with hψ
  have hψrange : ψ.range = D.img K₁ := by
    rw [img_eq_range D hK₁U]
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H k => exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨QuotientGroup.mk k, rfl⟩
  have hψΓ : ψ.range ≤ Γ := by
    rw [hψrange]
    exact img_mono D hK₁G₁
  have hΓψ : Γ ≤ Subgroup.normalizer (ψ.range : Set _) := by
    rw [hψrange]
    exact img_le_normalizer D hK₁n

  have hL₁U : lOne L V₁ ≤ Subgroup.normalizer (U : Set G) :=
    ((oTwoUpper_le _).trans inf_le_right).trans hG₁U
  have hL₁V : lOne L V₁ ≤ Subgroup.normalizer (V : Set G) :=
    ((oTwoUpper_le _).trans inf_le_left).trans hyp.irrPlus.2.2.1
  have hVZ := lemma12_8_8_three_F4 h1222 h12213 hs
  have haV := hV₂.1 haV₂
  obtain ⟨u', hu'V, hu'V₁, hu'a⟩ : ∃ u' ∈ V, u' ∉ V₁ ∧ u' * a⁻¹ ∉ V₁ := by
    by_contra hall
    push Not at hall

    have hle : V ≤ V₂ := by
      intro x hx
      by_cases hxV₁ : x ∈ V₁
      · exact hV₁₂ hxV₁
      · have := V₂.mul_mem (hV₁₂ (hall x hx hxV₁)) haV₂
        rwa [inv_mul_cancel_right] at this
    have h1 := Subgroup.card_le_of_le hle
    rw [hcard, hV₂.2.1] at h1
    have hn3 : 3 ≤ n := by rcases hcx.n45 with h | h <;> omega
    have h2 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  obtain ⟨σ, hσ, hσa⟩ := exists_mem_lOne_conj h hV₁ haV hu'V haV₁ hu'V₁
  have hψne : ψ.range ≠ ⊥ := by
    intro hb
    have hσρ : D.ρ ⟨σ, hL₁U hσ⟩ ∈ ψ.range := by
      rw [hψrange]
      exact ⟨⟨σ, hL₁U hσ⟩, Subgroup.mem_subgroupOf.2 (hLK hσ), rfl⟩
    rw [hb, Subgroup.mem_bot] at hσρ
    have h1 : D.ρ ⟨σ, hL₁U hσ⟩ (D.π a) = D.π a := by rw [hσρ]; rfl
    rw [D.ρ_π _ a (le_conjClosure V _ haV), D.π_eq_iff _ ((Subgroup.mem_normalizer_iff.1
      (hL₁U hσ) a).1 (le_conjClosure V _ haV)) a (le_conjClosure V _ haV)] at h1

    have hσaV : σ * a * σ⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hL₁V hσ) a).1 haV
    have h2 : (σ * a * σ⁻¹)⁻¹ * a ∈ V ⊓ zU128 V V₁ :=
      ⟨V.mul_mem (V.inv_mem hσaV) haV, h1⟩
    rw [hVZ] at h2
    have hba : (σ * a * σ⁻¹)⁻¹ * a = a * (σ * a * σ⁻¹)⁻¹ := hab _ (V.inv_mem hσaV) a haV
    rw [hba] at h2
    have h3 := V₁.mul_mem h2 hσa
    rw [show a * (σ * a * σ⁻¹)⁻¹ * (σ * a * σ⁻¹ * u'⁻¹) = a * u'⁻¹ by group] at h3
    apply hu'a
    have h4 := V₁.inv_mem h3
    rwa [show (a * u'⁻¹)⁻¹ = u' * a⁻¹ by group] at h4

  have hQlist : IsList1293Two (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨
      IsList1293Three (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := hlist.imp_right fun h1 => h1.2
  obtain ⟨hnot2, hconcl⟩ := hInsp _ D.B Γ (D.π a)
    (D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g))
    (D.img (CFSG.conjugate (w128 V V₁ V₂) g)) (D.img (CFSG.conjugate (zU128 V V₁) g)) hG111
    hsqtk hfix _ ψ hQlist hψΓ hΓψ hψne

  obtain ⟨hn4, -⟩ := hlist.resolve_left hnot2
  subst hn4

  have hTG₁ : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (V₁ : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hV₁.2.2
  have hS := isSylowTwoOf_img D hTG₁ hG₁U
  have hLtψ : D.img (lOne L V₁) ≤ ψ.range := by
    rw [hψrange]
    exact img_mono D hLK
  have hTL₁ : T ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
    le_normalizer_lOne hyp.normalizes hV₁.2.2
  have hSLt := img_le_normalizer D (U := U) (K := lOne L V₁) hTL₁

  have hLt3 : Nonempty (↥(D.img (lOne L V₁)) ⧸ CFSG.pCore 2 ↥(D.img (lOne L V₁)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    set f := (D.ρ.comp (Subgroup.inclusion hL₁U)).rangeRestrict with hf
    have hfs : Function.Surjective f := MonoidHom.rangeRestrict_surjective _
    have hk : IsPGroup 2 f.ker := by
      have hodd : ∀ y ∈ f.ker, Odd (orderOf y) → y = 1 := by
        intro y hy hyodd
        have hy1 : D.ρ ⟨(y : G), hL₁U y.2⟩ = 1 := by
          have := congrArg Subtype.val ((MonoidHom.mem_ker).1 hy)
          exact this
        have hyV₁ : (y : G) ∈ Subgroup.normalizer (V₁ : Set G) :=
          (oTwoUpper_le _).trans inf_le_right y.2
        have hyc : ∀ v ∈ V, (y : G) * v * (y : G)⁻¹ * v⁻¹ ∈ V₁ := by
          intro v hv
          have h1 : D.ρ ⟨(y : G), hL₁U y.2⟩ (D.π v) = D.π v := by rw [hy1]; rfl
          rw [D.ρ_π _ v (le_conjClosure V _ hv), D.π_eq_iff _ ((Subgroup.mem_normalizer_iff.1
            (hL₁U y.2) v).1 (le_conjClosure V _ hv)) v (le_conjClosure V _ hv)] at h1
          have hyv : (y : G) * v * (y : G)⁻¹ ∈ V :=
            (Subgroup.mem_normalizer_iff.1 (hL₁V y.2) v).1 hv
          have h2 : ((y : G) * v * (y : G)⁻¹)⁻¹ * v ∈ V ⊓ zU128 V V₁ :=
            ⟨V.mul_mem (V.inv_mem hyv) hv, h1⟩
          rw [hVZ] at h2
          have h3 := V₁.inv_mem h2
          rw [show (((y : G) * v * (y : G)⁻¹)⁻¹ * v)⁻¹ = v⁻¹ * ((y : G) * v * (y : G)⁻¹) by group]
            at h3
          have h4 : v⁻¹ * ((y : G) * v * (y : G)⁻¹) = (y : G) * v * (y : G)⁻¹ * v⁻¹ := by
            rw [hab v⁻¹ (V.inv_mem hv) _ hyv]
          rwa [h4] at h3
        have hodd' : Odd (orderOf (y : G)) := by
          rwa [Subgroup.orderOf_coe]
        have hyC := mem_centralizer_of_odd_of_commutator_mem hV₁.1 hV₁2 hsq hyV₁ hyc hodd'
        have hyO : (y : G) ∈ pCoreOf 2 L := by
          rw [← inf_centralizer_eq_pCoreOf_F4 h1222 h]
          exact ⟨(oTwoUpper_le _).trans inf_le_left y.2, hyC⟩
        have h1 := eq_one_of_odd_orderOf_of_mem (LieType.BorelTits.pCoreOf_isPGroup 2 L) hyO
          hodd'
        exact Subtype.ext h1
      exact isPGroup_two_of_odd_orderOf_eq_one hodd
    obtain ⟨e⟩ := exists_pCore_quotient_mulEquiv f hfs hk
    obtain ⟨e'⟩ := lOne_quotient_mulEquiv_F4 h1222 h hn hV₁
    rw [img_eq_range D hL₁U]
    exact ⟨e.symm.trans e'⟩

  rcases hconcl _ _ hS hLtψ hSLt hLt3 with h4 | ⟨h5', hQ4, hψeq⟩
  · exact h13six G T L V 4 V₁ V₂ hs le_rfl D h4
  · exact hFive G T L V hcx V₁ V₂ K₁ hs hLK hK hQ4 D h5' (hψrange ▸ hψeq)

end CFSG.Quasithin.H13
