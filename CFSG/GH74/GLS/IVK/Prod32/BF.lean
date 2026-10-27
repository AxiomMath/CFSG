module

public import CFSG.GH74.GLS.IVK.Prod32.BFCtx
public import CFSG.GH74.GLS.IVK.Prod32.Transport

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank Matrix
open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass squareClassMap)
open scoped commutatorElement

section BFMain

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H} {T : Subgroup H} {a : H}
  {F : Type} [Field F] [Finite F]

structure BFSetup (h : Hyp H K₁ K₂ z T a) (ê₁ : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F)
    (ê₂ : ↥K₂ ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F) (σ : F ≃+* F) (t h' : H) : Prop where
  act₁ : SLAct K₁ a ê₁ σ
  act₂ : SLAct K₂ a ê₂ σ
  σ_ne : σ ≠ 1
  htT : t ∈ T
  htN : t ∉ normalizer (K₁ : Set H)
  hV : (t * a * t⁻¹) * a ∈ K₁ ⊔ K₂
  hcoord : ∀ (x : H) (hx : x ∈ normalizer (K₁ : Set H))
      (hx' : t⁻¹ * x * t ∈ normalizer (K₁ : Set H)),
      coordHom K₂ ê₂ hF ⟨x, h.setting.normalizer₁₂ hx⟩ = coordHom K₁ ê₁ hF ⟨t⁻¹ * x * t, hx'⟩
  hh' : h' ∈ T1 T K₁
  hP' : a⁻¹ * (h' * t * h'⁻¹ * t⁻¹) ∈ P T K₁ K₂

variable {h : Hyp H K₁ K₂ z T a} {ê₁ : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F}
  {ê₂ : ↥K₂ ≃* SpecialLinearGroup (Fin 2) F} {hF : GoodF F} {σ : F ≃+* F} {t h' : H}
  {Yx Ax : Subgroup (SquareClass F × (F ≃+* F))}

theorem BFSetup.E2_eq (c : BFSetup h ê₁ ê₂ hF σ t h') (x : H) (hx : x ∈ T1 T K₁) :
    E2 h.setting T ê₂ hF ⟨x, hx⟩ =
      E1 K₁ T ê₁ hF ⟨t⁻¹ * x * t, T1_conj_inv_mem h.setting c.htT c.htN hx⟩ := by
  rw [E2_apply, E1_apply]
  exact c.hcoord x hx.2 (T1_conj_inv_mem h.setting c.htT c.htN hx).2

theorem BFSetup.abs (c : BFSetup h ê₁ ê₂ hF σ t h')
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H))) :
    BFAbs (E1 K₁ T ê₁ hF) (E2 h.setting T ê₂ hF) ⟨a, h.a_mem⟩ ⟨h', c.hh'⟩ σ :=
  bfAbs_of_ctx h hP₂ ê₁ hF c.act₁ c.σ_ne ê₂ c.act₂ c.htT c.htN c.hcoord c.hh' c.hP'

theorem P_eq_preSub (h : Hyp H K₁ K₂ z T a)
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (ê₁ : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F) :
    P T K₁ K₂ = preSub (E1 K₁ T ê₁ hF) ⊥ := by
  ext x
  rw [mem_preSub]
  constructor
  · intro hx
    have hxT : x ∈ T1 T K₁ := P_le_T1 h.setting hx
    exact ⟨hxT, by rw [Subgroup.mem_bot]; exact (E1_eq_one_iff h hP₂ ê₁ hF ⟨x, hxT⟩).mpr hx⟩
  · rintro ⟨hxT, hx⟩
    rw [Subgroup.mem_bot] at hx
    exact (E1_eq_one_iff h hP₂ ê₁ hF ⟨x, hxT⟩).mp hx

theorem P_eq_inter (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (d : BFDec (E1 K₁ T ê₁ hF) (E2 h.setting T ê₂ hF) σ Yx Ax) :
    P T K₁ K₂ = preSub (E1 K₁ T ê₁ hF) Yx ⊓ preSub (E1 K₁ T ê₁ hF) Ax := by
  rw [P_eq_preSub h hP₂ ê₁ hF, ← preSub_inf, d.inf]

theorem prod_eq_T1 (d : BFDec (E1 K₁ T ê₁ hF) (E2 h.setting T ê₂ hF) σ Yx Ax) :
    preSub (E1 K₁ T ê₁ hF) Yx ⊔ preSub (E1 K₁ T ê₁ hF) Ax = T1 T K₁ := by
  rw [← preSub_sup _ qc_comm d.Yx_le d.Ax_le, d.sup, preSub_range]

theorem BFSetup.mem_A (c : BFSetup h ê₁ ê₂ hF σ t h')
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (d : BFDec (E1 K₁ T ê₁ hF) (E2 h.setting T ê₂ hF) σ Yx Ax) :
    a ∈ preSub (E1 K₁ T ê₁ hF) Ax := by
  refine mem_preSub.mpr ⟨h.a_mem, ?_⟩
  have := (c.abs hP₂).ua
  rw [this]; exact d.s_mem

theorem BFSetup.Y_norm (c : BFSetup h ê₁ ê₂ hF σ t h')
    (d : BFDec (E1 K₁ T ê₁ hF) (E2 h.setting T ê₂ hF) σ Yx Ax) :
    ∀ s ∈ T, ∀ y ∈ preSub (E1 K₁ T ê₁ hF) Yx, s * y * s⁻¹ ∈ preSub (E1 K₁ T ê₁ hF) Yx := by
  have hS := h.setting
  have conjT1 : ∀ s' ∈ T1 T K₁, ∀ y ∈ preSub (E1 K₁ T ê₁ hF) Yx,
      s' * y * s'⁻¹ ∈ preSub (E1 K₁ T ê₁ hF) Yx := by
    intro s' hs' y hy
    obtain ⟨hyT, huy⟩ := mem_preSub.mp hy
    have hmem : s' * y * s'⁻¹ ∈ T1 T K₁ :=
      (T1 T K₁).mul_mem ((T1 T K₁).mul_mem hs' hyT) ((T1 T K₁).inv_mem hs')
    refine mem_preSub.mpr ⟨hmem, ?_⟩
    have e : E1 K₁ T ê₁ hF (⟨s', hs'⟩ * ⟨y, hyT⟩ * ⟨s', hs'⟩⁻¹) = E1 K₁ T ê₁ hF ⟨y, hyT⟩ := by
      rw [map_mul, map_mul, map_inv, qc_comm (E1 K₁ T ê₁ hF ⟨s', hs'⟩), mul_assoc, mul_inv_cancel,
        mul_one]
    have e2 : (⟨s' * y * s'⁻¹, hmem⟩ : ↥(T1 T K₁)) = ⟨s', hs'⟩ * ⟨y, hyT⟩ * ⟨s', hs'⟩⁻¹ := rfl
    rw [e2, e]; exact huy
  have conjt : ∀ y ∈ preSub (E1 K₁ T ê₁ hF) Yx, t * y * t⁻¹ ∈ preSub (E1 K₁ T ê₁ hF) Yx := by
    intro y hy
    obtain ⟨hyT, huy⟩ := mem_preSub.mp hy
    refine mem_preSub.mpr ⟨T1_conj_mem hS c.htT c.htN hyT, ?_⟩
    rw [E1_conj_t hS ê₁ hF c.htT c.htN hyT, ← c.E2_eq y hyT, d.fix ⟨y, hyT⟩ huy]
    exact huy
  intro s hs y hy
  by_cases hsN : s ∈ normalizer (K₁ : Set H)
  · exact conjT1 s ⟨hs, hsN⟩ y hy
  · have hidx := hS.index_eq_two c.htN
    have hs' : t⁻¹ * s ∈ normalizer (K₁ : Set H) := by
      rcases mem_or_of_index_two (N := normalizer (K₁ : Set H)) hidx c.htN s with h1 | h1
      · exact absurd h1 hsN
      · exact h1
    have hs'T : t⁻¹ * s ∈ T1 T K₁ := ⟨T.mul_mem (T.inv_mem c.htT) hs, hs'⟩
    have := conjt _ (conjT1 _ hs'T y hy)
    have e : s * y * s⁻¹ = t * ((t⁻¹ * s) * y * (t⁻¹ * s)⁻¹) * t⁻¹ := by group
    rw [e]; exact this

theorem relIndex_Y_le (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (d : BFDec (E1 K₁ T ê₁ hF) (E2 h.setting T ê₂ hF) σ Yx Ax) :
    (P T K₁ K₂).relIndex (preSub (E1 K₁ T ê₁ hF) Yx) ≤ 2 := by
  rw [P_eq_preSub h hP₂ ê₁ hF, relIndex_preSub _ d.Yx_le]
  exact d.card_Y

theorem BFSetup.Cd (c : BFSetup h ê₁ ê₂ hF σ t h')
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (d : BFDec (E1 K₁ T ê₁ hF) (E2 h.setting T ê₂ hF) σ Yx Ax) :
    Cd T K₁ K₂ (preSub (E1 K₁ T ê₁ hF) Ax) a := by
  have hPe := P_eq_preSub h hP₂ ê₁ hF
  obtain ⟨c', hc'S, hAe⟩ := preSub_cyclic (E1 K₁ T ê₁ hF) d.Ax_le d.cyc
  refine ⟨c.mem_A hP₂ d, ⟨(c' : H), mem_preSub.mpr ⟨c'.2, hc'S⟩, ?_⟩, ?_⟩
  · rw [hPe]; exact hAe
  · rw [hPe, relIndex_preSub _ d.Ax_le]; exact d.card_A

theorem BFSetup.comm_t_mem (c : BFSetup h ê₁ ê₂ hF σ t h')
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H))) {y : H}
    (hy : y ∈ T1 T K₁) (hfix : E2 h.setting T ê₂ hF ⟨y, hy⟩ = E1 K₁ T ê₁ hF ⟨y, hy⟩) :
    t * y * t⁻¹ * y⁻¹ ∈ K₁ ⊔ K₂ := by
  have h1 := E1_conj_t h.setting ê₁ hF c.htT c.htN hy
  rw [← c.E2_eq y hy, hfix] at h1
  have h2 := (E1_eq_iff h hP₂ ê₁ hF ⟨y, hy⟩ ⟨t * y * t⁻¹, T1_conj_mem h.setting c.htT c.htN hy⟩).mp
    h1.symm
  have h3 := h.setting.normal.conj_mem _ h2.2 y
  have e : y * (y⁻¹ * (t * y * t⁻¹)) * y⁻¹ = t * y * t⁻¹ * y⁻¹ := by group
  rw [e] at h3; exact h3

theorem BFSetup.Ce (c : BFSetup h ê₁ ê₂ hF σ t h')
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (h2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7)
    (d : BFDec (E1 K₁ T ê₁ hF) (E2 h.setting T ê₂ hF) σ Yx Ax) :
    Ce T K₁ K₂ (preSub (E1 K₁ T ê₁ hF) Yx) (preSub (E1 K₁ T ê₁ hF) Ax) a := by
  have hS := h.setting
  refine ⟨fun y hy b hb => ?_, fun g => ⟨fun y hy => ?_, ?_⟩⟩
  · obtain ⟨hyT, -⟩ := mem_preSub.mp hy
    obtain ⟨hbT, -⟩ := mem_preSub.mp hb
    have hmem : ⁅y, b⁆ ∈ T1 T K₁ := by
      rw [commutatorElement_def]
      exact (T1 T K₁).mul_mem ((T1 T K₁).mul_mem ((T1 T K₁).mul_mem hyT hbT) ((T1 T K₁).inv_mem hyT))
        ((T1 T K₁).inv_mem hbT)
    have e : E1 K₁ T ê₁ hF ⟨⁅y, b⁆, hmem⟩ = 1 := by
      have e2 : (⟨⁅y, b⁆, hmem⟩ : ↥(T1 T K₁)) = ⁅(⟨y, hyT⟩ : ↥(T1 T K₁)), (⟨b, hbT⟩ : ↥(T1 T K₁))⁆ := rfl
      rw [e2, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (qc_comm _ _)
    exact (E1_eq_one_iff h hP₂ ê₁ hF _).mp e
  · obtain ⟨hyT, huy⟩ := mem_preSub.mp hy
    exact comm_mem_of_t hS h2A7 c.htN hyT.2 (c.comm_t_mem hP₂ hyT (d.fix ⟨y, hyT⟩ huy)) g
  · have hha : t * a * t⁻¹ * a⁻¹ ∈ K₁ ⊔ K₂ := by rw [h.a_inv]; exact c.hV
    exact comm_mem_of_t hS h2A7 c.htN h.a_mem.2 hha g

theorem BFSetup.Cf (c : BFSetup h ê₁ ê₂ hF σ t h')
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (d : BFDec (E1 K₁ T ê₁ hF) (E2 h.setting T ê₂ hF) σ Yx Ax) :
    Cf T (preSub (E1 K₁ T ê₁ hF) Yx) := by
  refine ⟨h', c.hh'.1, t, c.htT, fun hc => ?_⟩
  have hPY : P T K₁ K₂ ≤ preSub (E1 K₁ T ê₁ hF) Yx := (P_eq_inter (h := h) hP₂ d).le.trans inf_le_left
  rw [commutatorElement_def] at hc
  have h1 : (a⁻¹ * (h' * t * h'⁻¹ * t⁻¹))⁻¹ ∈ preSub (E1 K₁ T ê₁ hF) Yx :=
    hPY ((P T K₁ K₂).inv_mem c.hP')
  have h2 : a ∈ preSub (E1 K₁ T ê₁ hF) Yx := by
    have := (preSub (E1 K₁ T ê₁ hF) Yx).mul_mem hc h1
    have e : h' * t * h'⁻¹ * t⁻¹ * (a⁻¹ * (h' * t * h'⁻¹ * t⁻¹))⁻¹ = a := by group
    rwa [e] at this
  have : a ∈ P T K₁ K₂ := by rw [P_eq_inter (h := h) hP₂ d]; exact ⟨h2, c.mem_A hP₂ d⟩
  exact h.a_not_mem_K this.2


theorem diag_of_dec
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (d : BFDec (E1 K₁ T ê₁ hF) (E2 h.setting T ê₂ hF) σ Yx Ax)
    (hne : P T K₁ K₂ ≠ preSub (E1 K₁ T ê₁ hF) Yx) :
    ∃ y ∈ preSub (E1 K₁ T ê₁ hF) Yx,
      DiagOutE K₁ (ê₁.trans (specialLinearGroupEquivStatedSL 2 F)) y ∧
      DiagOutE K₂ (ê₂.trans (specialLinearGroupEquivStatedSL 2 F)) y ∧ y * y ∈ K₁ ⊔ K₂ ∧
      preSub (E1 K₁ T ê₁ hF) Yx = P T K₁ K₂ ⊔ zpowers y := by
  have hS := h.setting
  have hYx : Yx ≠ ⊥ := fun hb => hne (by rw [P_eq_preSub h hP₂ ê₁ hF, hb])
  obtain ⟨y₀, hYeq, hy₀2, hy₀1⟩ := d.gen hYx
  have hy₀Y : y₀ ∈ Yx := by rw [hYeq]; exact Subgroup.mem_zpowers y₀
  obtain ⟨y', hy'⟩ := d.Yx_le hy₀Y
  have hy'Y : E1 K₁ T ê₁ hF y' ∈ Yx := by rw [hy']; exact hy₀Y
  have hfix : E2 h.setting T ê₂ hF y' = E1 K₁ T ê₁ hF y' := d.fix y' hy'Y
  have hy02 : y₀ * y₀ = 1 := Prod.ext (squareClass_sq hF _) (by simp [hy₀2])
  refine ⟨(y' : H), mem_preSub.mpr ⟨y'.2, hy'Y⟩, ?_, ?_, ?_, ?_⟩
  · refine diagOutE_of_coord ê₁ hF y'.2.2 ?_ ?_
    · show (E1 K₁ T ê₁ hF y').2 = 1
      rw [hy']; exact hy₀2
    · show (E1 K₁ T ê₁ hF y').1 ≠ 1
      rw [hy']; exact hy₀1
  · refine diagOutE_of_coord ê₂ hF (hS.normalizer₁₂ y'.2.2) ?_ ?_
    · show (E2 h.setting T ê₂ hF y').2 = 1
      rw [hfix, hy']; exact hy₀2
    · show (E2 h.setting T ê₂ hF y').1 ≠ 1
      rw [hfix, hy']; exact hy₀1
  · have : E1 K₁ T ê₁ hF (y' * y') = 1 := by rw [map_mul, hy', hy02]
    exact ((E1_eq_one_iff h hP₂ ê₁ hF _).mp this).2
  · rw [P_eq_preSub h hP₂ ê₁ hF, hYeq, ← hy']
    exact preSub_zpowers _ y'

theorem exists_r (hF : GoodF F) (hdvd : 4 ∣ Nat.card (F ≃+* F)) :
    ∃ r : ℕ, IsPrimePow r ∧ Odd r ∧ Nat.card F = r ^ 4 := by
  obtain ⟨p, n, hp, hpodd, hn, hcard⟩ := CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hF.odd
  have hn' : Nat.card (F ≃+* F) = n :=
    CFSG.Semidihedral.SemilinearOuterQuotient.fieldAut_card F hp hcard
  rw [hn'] at hdvd
  obtain ⟨m, rfl⟩ := hdvd
  have hm : m ≠ 0 := by rintro rfl; omega
  refine ⟨p ^ m, hp.isPrimePow.pow hm, hpodd.pow, ?_⟩
  rw [hcard, ← pow_mul, mul_comm]

omit [Finite H] in
theorem SLAct.triv_of_one {K : Subgroup H} {a : H} {ê : ↥K ≃* SpecialLinearGroup (Fin 2) F}
    (hact : SLAct K a ê (1 : F ≃+* F)) : ∀ y ∈ K, a * y * a⁻¹ = y := by
  intro y hy
  have h3 := hact.act ⟨y, hy⟩ (hact.norm y hy)
  have : CFSG.GH74.GLS.IVK.Lifted.slFieldAut (1 : F ≃+* F) (ê ⟨y, hy⟩) = ê ⟨y, hy⟩ := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  rw [this] at h3
  exact congrArg Subtype.val (ê.injective h3)


theorem not_double_cover (h : Hyp H K₁ K₂ z T a) (h2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7)
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (h7 : IsDoubleCoverOfAlt ↥K₁ 7) : False := by
  have hS := h.setting
  obtain ⟨t, htT, htN⟩ : ∃ t ∈ T, t ∉ normalizer (K₁ : Set H) := by
    have := h.T1_lt h2A7
    obtain ⟨t, htT, htn⟩ := Set.exists_of_ssubset this
    exact ⟨t, htT, fun hh => htn ⟨htT, hh⟩⟩
  obtain ⟨h', hh', hP', -, -⟩ := h.exists_comm_rep h2A7 htT htN
  have hidx : (CFSG.GH74.GLS.Stage1.Thm2.Recip.innOf ↥K₁).index = 2 := (h2A7 ↥K₁ h7).2.2.2.1
  let ω : ↥(T1 T K₁) →* MulAut ↥K₁ := K₁.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)
  have hω : ∀ x : ↥(T1 T K₁),
      ω x ∈ CFSG.GH74.GLS.Stage1.Thm2.Recip.innOf ↥K₁ ↔ (x : H) ∈ P T K₁ K₂ := by
    intro x
    rw [← h.inner_iff_mem_P hP₂ x.2]
    constructor
    · rintro ⟨κ, hκ⟩
      refine ⟨(κ : H), κ.2, fun y hy => ?_⟩
      have h1 := congrArg (fun f : MulAut ↥K₁ => ((f ⟨y, hy⟩ : ↥K₁) : H)) hκ
      simp only [MulAut.conj_apply, Subgroup.coe_mul, InvMemClass.coe_inv] at h1
      exact h1.symm
    · rintro ⟨k, hk, hkx⟩
      refine ⟨⟨k, hk⟩, ?_⟩
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      simp only [MulAut.conj_apply, Subgroup.coe_mul, InvMemClass.coe_inv]
      exact (hkx y y.2).symm
  have hωa : ω ⟨a, h.a_mem⟩ ∉ CFSG.GH74.GLS.Stage1.Thm2.Recip.innOf ↥K₁ :=
    fun hin => h.a_not_mem_K ((hω _).mp hin).2
  have hdich : ∀ x : ↥(T1 T K₁), (x : H) ∈ P T K₁ K₂ ∨ a⁻¹ * (x : H) ∈ P T K₁ K₂ := by
    intro x
    by_cases hx : ω x ∈ CFSG.GH74.GLS.Stage1.Thm2.Recip.innOf ↥K₁
    · exact Or.inl ((hω x).mp hx)
    · right
      have h1 : ω ((⟨a, h.a_mem⟩ : ↥(T1 T K₁))⁻¹ * x) ∈
          CFSG.GH74.GLS.Stage1.Thm2.Recip.innOf ↥K₁ := by
        rw [map_mul, map_inv, Subgroup.mul_mem_iff_of_index_two hidx]
        exact iff_of_false (fun hh => hωa (by simpa using Subgroup.inv_mem _ hh)) hx
      exact (hω _).mp h1
  rcases hdich ⟨h', hh'⟩ with hh | hh
  · have h1 : h' * t * h'⁻¹ * t⁻¹ ∈ P T K₁ K₂ := by
      have := (P T K₁ K₂).mul_mem hh (P_conj_mem hS htT ((P T K₁ K₂).inv_mem hh))
      simpa [mul_assoc] using this
    have h2 : a ∈ P T K₁ K₂ := by
      have := (P T K₁ K₂).mul_mem h1 ((P T K₁ K₂).inv_mem hP')
      have e : h' * t * h'⁻¹ * t⁻¹ * (a⁻¹ * (h' * t * h'⁻¹ * t⁻¹))⁻¹ = a := by group
      rwa [e] at this
    exact h.a_not_mem_K h2.2
  · have e : a⁻¹ * (h' * t * h'⁻¹ * t⁻¹) =
        ((a⁻¹ * h') * t * (a⁻¹ * h')⁻¹ * t⁻¹) * (t * a⁻¹ * t⁻¹) := by group
    have h1 : (a⁻¹ * h') * t * (a⁻¹ * h')⁻¹ * t⁻¹ ∈ P T K₁ K₂ := by
      have := (P T K₁ K₂).mul_mem hh (P_conj_mem hS htT ((P T K₁ K₂).inv_mem hh))
      simpa [mul_assoc] using this
    have h2 : t * a⁻¹ * t⁻¹ ∈ P T K₁ K₂ := by
      rw [e] at hP'
      have := (P T K₁ K₂).mul_mem ((P T K₁ K₂).inv_mem h1) hP'
      simpa [mul_assoc] using this
    have h3 : a⁻¹ ∈ P T K₁ K₂ := by
      have := P_conj_inv_mem hS htT h2
      simpa [mul_assoc] using this
    have h4 : a ∈ P T K₁ K₂ := by simpa using (P T K₁ K₂).inv_mem h3
    exact h.a_not_mem_K h4.2


structure BFOut (K₁ K₂ : Subgroup H) (z : H) (T : Subgroup H) (a : H) (Y A : Subgroup H) (r : ℕ)
    {F : Type} [Field F] [Finite F] (e₁ : ↥K₁ ≃* SL2 F) (e₂ : ↥K₂ ≃* SL2 F) (σ : F ≃+* F) : Prop where
  Y_le : Y ≤ T1 T K₁
  A_le : A ≤ T1 T K₁
  prod : Y ⊔ A = T1 T K₁
  inter : P T K₁ K₂ = Y ⊓ A
  Cb : Cb K₁ K₂ r
  Y_norm : ∀ s ∈ T, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y
  Y_index : (P T K₁ K₂).relIndex Y ≤ 2
  Cd : Cd T K₁ K₂ A a
  Ce : Ce T K₁ K₂ Y A a
  Cf : Cf T Y
  lang : LangHyp K₁ K₂ z a e₁ e₂ σ σ
  card : Nat.card F = r ^ 4
  three_le : 3 ≤ r
  diag : P T K₁ K₂ ≠ Y → ∃ y ∈ Y, DiagOutE K₁ e₁ y ∧ DiagOutE K₂ e₂ y ∧ y * y ∈ K₁ ⊔ K₂ ∧
    Y = P T K₁ K₂ ⊔ zpowers y

theorem prod3_bf (h : Hyp H K₁ K₂ z T a) (h2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7)
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H))) :
    ∃ (Y A : Subgroup H) (r : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (e₁ : ↥K₁ ≃* SL2 F)
      (e₂ : ↥K₂ ≃* SL2 F) (σ : F ≃+* F), BFOut K₁ K₂ z T a Y A r e₁ e₂ σ := by
  classical
  have hS := h.setting
  rcases hS.type₁ with hsl | h7
  swap
  · exact (not_double_cover h h2A7 hP₂ h7).elim
  obtain ⟨F, _, _, ê₁, σ, hF, hact₁⟩ := h.f₁.exists_slAct hsl
  obtain ⟨t, htT, htN⟩ : ∃ t ∈ T, t ∉ normalizer (K₁ : Set H) := by
    have := h.T1_lt h2A7
    obtain ⟨t, htT, htn⟩ := Set.exists_of_ssubset this
    exact ⟨t, htT, fun hh => htn ⟨htT, hh⟩⟩
  obtain ⟨h', hh', hP', hV, hV'⟩ := h.exists_comm_rep h2A7 htT htN
  have hσ : σ ≠ 1 := by
    intro hσ1
    subst hσ1
    exact (h.nontrivial_both h2A7).1 hact₁.triv_of_one
  obtain ⟨ê₂, hact₂, hcoord⟩ := exists_transport h ê₁ hF hact₁ hσ htN hV'
  have c : BFSetup h ê₁ ê₂ hF σ t h' := ⟨hact₁, hact₂, hσ, htT, htN, hV, hcoord, hh', hP'⟩
  have hb := c.abs hP₂
  have hΓ : ∃ m, Nat.card ↥(T1 T K₁) = 2 ^ m := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.exists_card_eq h.sylow.isPGroup.to_inf_left
  obtain ⟨Yx, Ax, d⟩ := hb.main hF hΓ
  have hAdvd : Nat.card Ax ∣ Nat.card (F ≃+* F) :=
    Subgroup.card_dvd_of_injective ((MonoidHom.snd (SquareClass F) (F ≃+* F)).comp Ax.subtype) (by
      rw [injective_iff_map_eq_one]
      intro p hp
      exact Subtype.ext (d.inj p p.2 hp))
  obtain ⟨r, hrpp, hrodd, hrcard⟩ := exists_r hF (d.dvd_A.trans hAdvd)
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hb.σ_sq) hσ
  refine ⟨preSub (E1 K₁ T ê₁ hF) Yx, preSub (E1 K₁ T ê₁ hF) Ax, r, F, inferInstance, inferInstance,
    ê₁.trans (specialLinearGroupEquivStatedSL 2 F), ê₂.trans (specialLinearGroupEquivStatedSL 2 F), σ, ?_⟩
  exact
    { Y_le := preSub_le _ _
      A_le := preSub_le _ _
      prod := prod_eq_T1 (h := h) d
      inter := P_eq_inter (h := h) hP₂ d
      Cb := ⟨hrpp, hrodd, ⟨F, inferInstance, inferInstance, hrcard,
          ⟨ê₁.trans (specialLinearGroupEquivStatedSL 2 F)⟩⟩,
        ⟨F, inferInstance, inferInstance, hrcard, ⟨ê₂.trans (specialLinearGroupEquivStatedSL 2 F)⟩⟩⟩
      Y_norm := c.Y_norm d
      Y_index := relIndex_Y_le (h := h) hP₂ d
      Cd := c.Cd hP₂ d
      Ce := c.Ce hP₂ h2A7 d
      Cf := c.Cf hP₂ d
      lang := langHyp_of_slAct hS h.a_mul_a ê₁ ê₂ hF hσ2 hact₁ hact₂
      card := hrcard
      three_le := by
        obtain ⟨k, hk⟩ := hrodd
        have := hrpp.two_le
        omega
      diag := fun hne => diag_of_dec (h := h) hP₂ d hne }

end BFMain

end CFSG.GH74.GLS.IVK.Prod3
