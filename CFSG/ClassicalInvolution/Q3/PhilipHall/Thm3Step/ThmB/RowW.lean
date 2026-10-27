module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.Std
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3QuotRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace Std

variable {K J : Subgroup G} {z j : G} (h : Std Ω K J z j)
include h

theorem exists_twin_of_aViol {M N : Subgroup G} {m n : G} (hM : M ∈ Ω) (hv : AViol Ω M N m n) :
    (∃ g : G, g * z * g⁻¹ = n) ∧ ∃ L ∈ twinSet Ω M, n ∈ M ⊔ L := by
  obtain ⟨M', u, v, d⟩ := exists_LJ h.hΩ hM hv.mem (WR1.inA_of_aViol hv) hv.hzK hv.hzJ
    (fun L hL => h.isPGroup hL)
  refine ⟨h.exists_conj hv.mem hv.hzJ, M', ?_, d.j_mem_KK'⟩
  rw [d.tor.htw]
  exact Or.inr rfl

end Std

section Six

variable {K J K' : Subgroup G} {z j u v : G}

theorem top_eq_pairNormalizers (h : Std Ω K J z j) (d : LJ Ω K J K' z j u v)
    (hE : ∀ t : G, (∃ g : G, g * z * g⁻¹ = t) → (∃ L ∈ twinSet Ω K, t ∈ L ⊔ K) →
      t ∈ Subgroup.closure ({z, j} : Set G)) :
    pairNormalizers K J z j = ⊤ := by
  set Y := pairNormalizers K J z j with hY
  set Z := (Subgroup.closure ({z, j} : Set G) : Subgroup G) with hZ
  have htwK : twinSet Ω K = {K, K'} := d.tor.htw
  have htwle : ∀ L ∈ twinSet Ω K, L ≤ Y := by
    intro L hL
    rw [htwK] at hL
    rcases hL with rfl | rfl
    · exact d.K_le_Y
    · exact d.K'_le_Y
  have hconj : ∀ {M : Subgroup G} {m : G}, M ∈ Ω → IsUniqueInvolution M m → m ∈ Z →
      ∃ y ∈ Y, conjSub y M ∈ twinSet Ω K := by
    intro M m hM hm hmZ
    have hm' : m = z ∨ m = j ∨ m = z * j := by
      rcases d.mem_Z_cases hmZ with h1 | h1
      · exact absurd h1 hm.ne_one
      · exact h1
    obtain ⟨y, hy, hym⟩ := d.exists_conj_z hm'
    refine ⟨y, hy, h.hΩ.hyp.conjInvariant y M hM, z, h.hz, ?_⟩
    rw [← hym]
    exact hm.conj y
  have hstep : ∀ {M N : Subgroup G}, M ∈ Ω → (∃ m, IsUniqueInvolution M m ∧ m ∈ Z) →
      aGraphAdj Ω M N → ∃ n, IsUniqueInvolution N n ∧ n ∈ Z := by
    have hA : ∀ {M N : Subgroup G} {m n : G}, M ∈ Ω → m ∈ Z → AViol Ω M N m n → n ∈ Z := by
      intro M N m n hM hmZ hv
      obtain ⟨y, hy, hyM⟩ := hconj hM hv.hzK hmZ
      obtain ⟨⟨g, hg⟩, L, hL, hnL⟩ := h.exists_twin_of_aViol hM hv
      have hLy : conjSub y L ∈ twinSet Ω K := by
        have h1 : conjSub y L ∈ twinSet Ω (conjSub y M) := by
          rw [twinSet_conjSub h.hΩ.hyp.conjInvariant]
          exact ⟨L, hL, rfl⟩
        rwa [twinSet_eq_twinSet_of_mem hyM] at h1
      have hKK : ∀ L₀ ∈ twinSet Ω K, L₀ ≤ K ⊔ K' := by
        intro L₀ hL₀
        rw [htwK] at hL₀
        rcases hL₀ with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      have hyn : y * n * y⁻¹ ∈ K' ⊔ K := by
        rw [sup_comm]
        have h1 : y * n * y⁻¹ ∈ conjSub y (M ⊔ L) := conj_mem_conjSub hnL
        rw [Sec7.conjSub_sup_eq] at h1
        exact sup_le (hKK _ hyM) (hKK _ hLy) h1
      have hyZ : y * n * y⁻¹ ∈ Z := hE _ ⟨y * g, by rw [← hg]; group⟩
        ⟨K', by rw [htwK]; exact Or.inr rfl, hyn⟩
      have hyi : y⁻¹ ∈ Subgroup.normalizer (Z : Set G) :=
        (Subgroup.normalizer _).inv_mem (d.Y_le_N_Z hy)
      have h2 := (Subgroup.mem_normalizer_iff.mp hyi (y * n * y⁻¹)).mp hyZ
      simpa [mul_assoc] using h2
    rintro M N hM ⟨m, hm, hmZ⟩ ⟨hNΩ, ⟨m', n', hv⟩ | ⟨n', m', hv⟩ | ⟨⟨-, w, hwM, hwN⟩, -⟩⟩
    · rw [hm.eq hv.hzK] at hmZ
      exact ⟨n', hv.hzJ, hA hM hmZ hv⟩
    · have hv' := aViol_symm' h.hΩ.hyp hNΩ hv
      rw [hm.eq hv'.hzK] at hmZ
      exact ⟨n', hv'.hzJ, hA hM hmZ hv'⟩
    · exact ⟨w, hwN, (hm.eq hwM) ▸ hmZ⟩
  have hall : ∀ M ∈ aStar Ω K, ∃ m, IsUniqueInvolution M m ∧ m ∈ Z := by
    intro M hMA
    induction hMA with
    | refl => exact ⟨z, h.hz, Subgroup.subset_closure (by simp)⟩
    | tail hab hbc ih =>
      rename_i b c
      have hb : b ∈ Ω := by
        rcases Relation.ReflTransGen.cases_tail hab with rfl | ⟨_, _, hb⟩
        · exact h.hK
        · exact hb.1
      exact hstep hb ih hbc
  have hle : ∀ M ∈ Ω, M ≤ Y := by
    intro M hM
    obtain ⟨m, hm, hmZ⟩ := hall M (h.hall.symm ▸ hM)
    obtain ⟨y, hy, hyM⟩ := hconj hM hm hmZ
    have h1 := conjSub_mono (n := y⁻¹) (htwle _ hyM)
    rwa [conjSub_inv_conjSub, conjSub_eq_self_of_mem (Y.inv_mem hy)] at h1
  rw [eq_top_iff, ← h.hgen]
  exact iSup₂_le hle

theorem wSet_eq (h : Std Ω K J z j) (d : LJ Ω K J K' z j u v)
    (hY : pairNormalizers K J z j = ⊤) :
    WSet Ω = {Subgroup.zpowers u ⊔ Subgroup.zpowers v} := by
  set UV := (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) with hUV
  have hYall : ∀ g : G, g ∈ pairNormalizers K J z j := fun g => hY ▸ Subgroup.mem_top g
  haveI hUVn : UV.Normal :=
    ⟨fun x hx g => (Subgroup.mem_normalizer_iff.mp (d.Y_le_N_UV (hYall g)) x).mp hx⟩
  have hUV2 : IsPGroup 2 UV := d.tor.UV_isPGroup
  have key : ∀ W ∈ WSet Ω, W = UV := by
    rintro W ⟨η, ⟨S, hη, hinv⟩, rfl⟩
    have hUVS : UV ≤ (S : Subgroup G) := hUV2.le_sylow_of_normal S
    have hUin : Subgroup.zpowers u ∈ UinS Ω (S : Subgroup G) :=
      ⟨d.tor.hU, le_sup_left.trans hUVS⟩
    have hVin : Subgroup.zpowers v ∈ UinS Ω (S : Subgroup G) :=
      ⟨d.tor.hV, le_sup_right.trans hUVS⟩
    obtain ⟨V₁, hV₁, hV₁K⟩ :=
      Sec6Gen.exists_mem_of_mem_etaSet h.hΩ.hyp hη d.tor.hK hUin d.tor.hUK
    obtain ⟨V₂, hV₂, hV₂J⟩ :=
      Sec6Gen.exists_mem_of_mem_etaSet h.hΩ.hyp hη d.tor.hJ hVin d.tor.hVJ
    have hW : (⨆ U ∈ η, U) ∈ WSet Ω := ⟨η, ⟨S, hη, hinv⟩, rfl⟩
    have hle : ∀ U ∈ η, U ≤ ⨆ U ∈ η, U := fun U hU =>
      le_iSup₂ (f := fun V (_ : V ∈ η) => V) U hU
    have hab := Q3CL.Thompson.commutes_of_mem_WSet h.hΩ.hyp hW
    have hV₁U := (hη.1 hV₁).1
    have hV₂U := (hη.1 hV₂).1
    have hV₁4 := card_of_mem_USet h.hΩ hV₁U
    have hV₂4 := card_of_mem_USet h.hΩ hV₂U
    have hzW : z ∈ ⨆ U ∈ η, U := hle V₁ hV₁ (d.tor.hz.mem_of_le hV₁K
      (Sec6Gen.isPGroup_of_mem_USet h.hΩ.hyp hV₁U) (by omega))
    have hjW : j ∈ ⨆ U ∈ η, U := hle V₂ hV₂ (d.tor.hj.mem_of_le hV₂J
      (Sec6Gen.isPGroup_of_mem_USet h.hΩ.hyp hV₂U) (by omega))
    have hWZ : ∀ w ∈ ⨆ U ∈ η, U, w ∈ Subgroup.centralizer
        ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) := fun w hw =>
      d.tor.mem_C_Z_of_comm (hab w hw z hzW) (hab w hw j hjW)
    have hcyc : ∀ {V₀ : Subgroup G}, V₀ ∈ USet Ω → V₀ ≤ ⨆ U ∈ η, U → V₀ ≤ UV := by
      intro V₀ hV₀ hV₀W
      obtain ⟨-, -, -, -, -, -, hc, -, -⟩ := Sec6Gen.exists_data_of_mem_USet h.hΩ.hyp hV₀
      obtain ⟨g, hg⟩ := Sec7.exists_zpowers_eq hc
      have hg4 : orderOf g = 4 := by rw [← Nat.card_zpowers, hg, card_of_mem_USet h.hΩ hV₀]
      have hgg : g * g ≠ 1 := by
        intro h1
        have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
        rw [hg4] at h2
        norm_num at h2
      rw [← hg, Subgroup.zpowers_le]
      by_contra hgX
      have hgW : g ∈ ⨆ U ∈ η, U := hV₀W (hg ▸ Subgroup.mem_zpowers g)
      exact hgg (d.inv_of_not_mem (hYall g) (hWZ g hgW) hgX).2
    have hV₁eq : V₁ = Subgroup.zpowers u := by
      rw [← d.K_inf_UV]
      exact Subgroup.eq_of_le_of_card_ge (le_inf hV₁K (hcyc hV₁U (hle V₁ hV₁)))
        (by rw [d.K_inf_UV, d.card_U, hV₁4])
    have hV₂eq : V₂ = Subgroup.zpowers v := by
      rw [← d.J_inf_UV]
      exact Subgroup.eq_of_le_of_card_ge (le_inf hV₂J (hcyc hV₂U (hle V₂ hV₂)))
        (by rw [d.J_inf_UV, d.card_V, hV₂4])
    have hUW : Subgroup.zpowers u ≤ ⨆ U ∈ η, U := hV₁eq ▸ hle V₁ hV₁
    have hVW : Subgroup.zpowers v ≤ ⨆ U ∈ η, U := hV₂eq ▸ hle V₂ hV₂
    refine le_antisymm (fun w hw => ?_) (sup_le hUW hVW)
    by_contra hwX
    have huW : u ∈ ⨆ U ∈ η, U := hUW (Subgroup.mem_zpowers u)
    have h1 := (d.inv_of_not_mem (hYall w) (hWZ w hw) hwX).1 u
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
    have h2 : w * u * w⁻¹ = u := by rw [hab w hw u huW]; group
    rw [h2] at h1
    apply d.tor.u_sq_ne
    calc u * u = u * u⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel u
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet h.hΩ.hyp S₀
  have hW₀ : (⨆ U ∈ η, U) ∈ WSet Ω := ⟨η, ⟨S₀, hη, hinv⟩, rfl⟩
  ext W
  constructor
  · exact key W
  · intro hW
    rw [Set.mem_singleton_iff] at hW
    rw [hW, ← key _ hW₀]
    exact hW₀

theorem quot_d12 (d : LJ Ω K J K' z j u v) (hY : pairNormalizers K J z j = ⊤)
    [(Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G).Normal] :
    Nonempty ((G ⧸ (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G)) ≃*
      DihedralGroup 6) := by
  obtain ⟨φ, hφ, hker⟩ := d.quot
  have hYall : ∀ g : G, g ∈ pairNormalizers K J z j := fun g => hY ▸ Subgroup.mem_top g
  let ι : G →* ↥(pairNormalizers K J z j) :=
    (MonoidHom.id G).codRestrict (pairNormalizers K J z j) hYall
  let ψ : G →* DihedralGroup 6 := φ.comp ι
  have hψ : Function.Surjective ψ := by
    intro e
    obtain ⟨y, rfl⟩ := hφ e
    exact ⟨y, congrArg φ (Subtype.ext rfl)⟩
  have hkerψ : ψ.ker = (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) := by
    ext g
    change φ (ι g) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf, d.X_eq]
    rfl
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

end Six

noncomputable def secQuotTopEquiv (hO : classicalInvolutionOddCore G = ⊥) :
    G ≃* SecQuot (⊤ : Subgroup G) :=
  MulEquiv.ofBijective ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(⊤ : Subgroup G))).comp
    Subgroup.topEquiv.symm.toMonoidHom) (by
      have hO' : classicalInvolutionOddCore ↥(⊤ : Subgroup G) = ⊥ :=
        TL4.oddCore_eq_bot_of_normal hO inferInstance
      refine ⟨fun x y hxy => ?_, fun q => ?_⟩
      · have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(⊤ : Subgroup G)))
            (Subgroup.topEquiv.symm x) = QuotientGroup.mk' _ (Subgroup.topEquiv.symm y) := hxy
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hO',
          Subgroup.mem_bot, inv_mul_eq_one] at h1
        exact Subgroup.topEquiv.symm.injective h1
      · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
        exact ⟨Subgroup.topEquiv x, rfl⟩)

theorem oddQuotientFamily_restrict_top (hO : classicalInvolutionOddCore G = ⊥) :
    oddQuotientFamily (restrictFamily Ω ⊤) =
      PhilipHall.Frame.Thm3Quot.famMap (secQuotTopEquiv hO) Ω := by
  have hmap : ∀ L : Subgroup G, L.map (secQuotTopEquiv hO).toMonoidHom =
      (L.subgroupOf ⊤).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(⊤ : Subgroup G))) := by
    intro L
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_top x⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : G), Subgroup.mem_subgroupOf.mp hx, rfl⟩
  ext L'
  constructor
  · rintro ⟨_, ⟨L, hL, -, rfl⟩, rfl⟩
    exact ⟨L, hL, hmap L⟩
  · rintro ⟨L, hL, rfl⟩
    exact ⟨_, ⟨L, hL, le_top, rfl⟩, (hmap L).symm⟩

theorem thm3RowW_top (hO : classicalInvolutionOddCore G = ⊥) {W : Subgroup G} [W.Normal]
    (hW : WSet Ω = {W}) (hD : Nonempty ((G ⧸ W) ≃* DihedralGroup 6)) : Thm3RowW Ω ⊤ := by
  set e := secQuotTopEquiv hO
  obtain ⟨q⟩ := hD
  haveI : (W.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ e.surjective
  refine ⟨W.map e.toMonoidHom, inferInstance, ?_, ⟨?_⟩⟩
  · rw [oddQuotientFamily_restrict_top hO, PhilipHall.Frame.Thm3Quot.wSet_map_equiv, hW,
      Set.image_singleton]
  · exact (QuotientGroup.congr W (W.map e.toMonoidHom) e rfl).symm.trans q

theorem rowW_of_e4 (hΩ : TypeRHyp Ω) (hO : classicalInvolutionOddCore G = ⊥)
    {K J : Subgroup G} (hK : K ∈ Ω) {z j : G} (hz : IsUniqueInvolution K z)
    (hzO : TightInO2 z) (hv : AViol Ω K J z j) (hall : aStar Ω K = Ω) (hgen : omegaGen Ω = ⊤)
    (hE : ∀ t : G, (∃ g : G, g * z * g⁻¹ = t) → (∃ L ∈ twinSet Ω K, t ∈ L ⊔ K) →
      t ∈ Subgroup.closure ({z, j} : Set G)) :
    Thm3RowW Ω ⊤ := by
  have h : Std Ω K J z j := ⟨hΩ, hO, hK, hz, hzO, hv, hall, hgen⟩
  obtain ⟨K', u, v, d⟩ := exists_LJ hΩ hK hv.mem (WR1.inA_of_aViol hv) hz hv.hzJ
    (fun L hL => h.isPGroup hL)
  have hY := top_eq_pairNormalizers h d hE
  have hYall : ∀ g : G, g ∈ pairNormalizers K J z j := fun g => hY ▸ Subgroup.mem_top g
  haveI : (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G).Normal :=
    ⟨fun x hx g => (Subgroup.mem_normalizer_iff.mp (d.Y_le_N_UV (hYall g)) x).mp hx⟩
  exact thm3RowW_top hO (wSet_eq h d hY) (quot_d12 d hY)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
