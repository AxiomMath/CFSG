module

public import CFSG.LieType.Chevalley.C2E6FieldExtensionResidue
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FieldExtension

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open Matrix CFSG.LocalAnalysis.ComponentInitial

@[expose] noncomputable def barSUHom : SU6 →* SU6 :=
  (barSL.comp SU6.subtype).codRestrict SU6 fun h => barSL_mem_SU6 h.2

theorem barSUHom_apply (h : SU6) : barSUHom h = barSU h :=
  rfl

theorem barSUHom_barSUHom (h : SU6) : barSUHom (barSUHom h) = h := by
  apply Subtype.ext
  apply Subtype.ext
  change (((h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map bar).map bar = _
  ext i j
  exact bar_bar _

@[expose] noncomputable def frobSU : MulAut SU6 :=
  { barSUHom with
    invFun := barSUHom
    left_inv := barSUHom_barSUHom
    right_inv := barSUHom_barSUHom }

theorem frobSU_apply (h : SU6) : frobSU h = barSU h :=
  rfl

abbrev ZSU : Subgroup SU6 := (LinearFlag.scalars 6 K).subgroupOf SU6

theorem frobSU_mem_ZSU {z : SU6} (hz : z ∈ ZSU) : frobSU z ∈ ZSU := by
  rw [Subgroup.mem_subgroupOf] at hz ⊢
  obtain ⟨c, hc6, hcz⟩ := LinearFlag.mem_scalars.mp hz
  refine LinearFlag.mem_scalars.mpr ⟨Units.map barHom.toMonoidHom c, ?_, ?_⟩
  · rw [← map_pow, hc6, map_one]
  · change ((z : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map bar = _
    rw [hcz, scalar_apply, scalar_apply, diagonal_map bar_zero]
    rfl

theorem map_frobSU_ZSU : ZSU.map frobSU.toMonoidHom = ZSU := by
  refine le_antisymm ?_ fun z hz => ⟨frobSU z, frobSU_mem_ZSU hz, barSUHom_barSUHom z⟩
  rintro _ ⟨z, hz, rfl⟩
  exact frobSU_mem_ZSU hz

@[expose] noncomputable def frobAut : MulAut (SU6 ⧸ ZSU) :=
  QuotientGroup.congr ZSU ZSU frobSU map_frobSU_ZSU

theorem frobAut_mk (h : SU6) : frobAut (h : SU6 ⧸ ZSU) = (barSU h : SU6 ⧸ ZSU) :=
  QuotientGroup.congr_mk _ _ _ _ h

theorem frobAut_mul_self : frobAut * frobAut = 1 := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with | H h => ?_
  rw [MulAut.mul_apply, frobAut_mk, frobAut_mk, MulAut.one_apply, ← barSUHom_apply,
    ← barSUHom_apply, barSUHom_barSUHom]

theorem bUp_zero_mulVec_uVec_one (a : K) :
    ((bUp 0 a : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ uVec 1 =
      uVec 1 + a • uVec 0 := by
  rw [bUp_mulVec]
  funext i
  fin_cases i <;> simp

theorem barSU_bUpSU (a : K) :
    barSU (bUpSU 0 (a := a) (Or.inl (by decide))) = bUpSU 0 (a := bar a) (Or.inl (by decide)) := by
  apply Subtype.ext
  change barSL (upAdj 0 a * upAdj 4 (bar a)) = upAdj 0 (bar a) * upAdj 4 (bar (bar a))
  rw [map_mul, barSL_upAdj, barSL_upAdj]

theorem frobAut_ne_one : frobAut ≠ 1 := by
  intro h
  set g : SU6 := bUpSU 0 (a := ω) (Or.inl (by decide))
  have e := MulEquiv.congr_fun h (g : SU6 ⧸ ZSU)
  rw [frobAut_mk, MulAut.one_apply, barSU_bUpSU, QuotientGroup.eq, Subgroup.mem_subgroupOf] at e
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.mp e
  have hmat : ((bUp 0 ω : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((bUp 0 (bar ω) : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        scalar (Fin 6) (c : K) := by
    rw [← hc]
    change _ = ((bUp 0 (bar ω) * ((bUp 0 (bar ω))⁻¹ * bUp 0 ω) : SpecialLinearGroup (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K)
    rw [mul_inv_cancel_left]
  have hv := congrArg (· *ᵥ uVec 1) hmat
  have hd : (diagonal fun _ : Fin 6 => (c : K)) *ᵥ uVec 1 = (c : K) • uVec 1 := by
    funext i
    rw [mulVec_diagonal]
    rfl
  rw [← mulVec_mulVec, scalar_apply, hd, mulVec_smul, bUp_zero_mulVec_uVec_one,
    bUp_zero_mulVec_uVec_one] at hv
  have key : ∀ c : K, (uVec 1 + ω • uVec 0 : Fin 6 → K) 0 =
      (c • (uVec 1 + bar ω • uVec 0) : Fin 6 → K) 0 → (uVec 1 + ω • uVec 0 : Fin 6 → K) 1 =
        (c • (uVec 1 + bar ω • uVec 0) : Fin 6 → K) 1 → False := by
    decide
  exact key c (congrFun hv 0) (congrFun hv 1)


abbrev frobGroup : Subgroup (MulAut (SU6 ⧸ ZSU)) := Subgroup.zpowers frobAut

theorem orderOf_frobAut : orderOf frobAut = 2 :=
  orderOf_eq_prime (by rw [pow_two, frobAut_mul_self]) frobAut_ne_one

theorem mem_frobGroup_iff {f : MulAut (SU6 ⧸ ZSU)} : f ∈ frobGroup ↔ f = 1 ∨ f = frobAut := by
  constructor
  · intro hf
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    rw [← zpow_mod_orderOf, orderOf_frobAut]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  · rintro (rfl | rfl)
    exacts [one_mem _, Subgroup.mem_zpowers _]

abbrev SUFrob : Type := (SU6 ⧸ ZSU) ⋊[frobGroup.subtype] frobGroup

@[expose] noncomputable def qSmul (q : SU6 ⧸ ZSU) (F : IsoFlag6) : IsoFlag6 :=
  Quotient.liftOn' q (fun h => h • F) fun h h' hh' => by
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hh'
    have := smul_eq_of_mem_scalars hh' F
    rw [mul_smul, inv_smul_eq_iff] at this
    exact this.symm

theorem qSmul_mk (h : SU6) (F : IsoFlag6) : qSmul (h : SU6 ⧸ ZSU) F = h • F :=
  rfl

theorem qSmul_mul (q q' : SU6 ⧸ ZSU) (F : IsoFlag6) :
    qSmul (q * q') F = qSmul q (qSmul q' F) := by
  induction q using QuotientGroup.induction_on with | H h => ?_
  induction q' using QuotientGroup.induction_on with | H h' => ?_
  rw [← QuotientGroup.mk_mul, qSmul_mk, qSmul_mk, qSmul_mk, mul_smul]

theorem frobFlag_frobFlag (F : IsoFlag6) : frobFlag (frobFlag F) = F := by
  refine IsoFlag6.ext (funext fun k => ?_)
  rw [frobFlag_sub, frobFlag_sub]
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rw [frob6_frob6]
    exact hw
  · intro hv
    exact ⟨frob6 v, ⟨v, hv, rfl⟩, frob6_frob6 v⟩

open _root_.Classical in
@[expose] noncomputable def frobAct (f : frobGroup) (F : IsoFlag6) : IsoFlag6 :=
  if (f : MulAut (SU6 ⧸ ZSU)) = 1 then F else frobFlag F

theorem frobAct_of_eq_one {f : frobGroup} (hf : (f : MulAut (SU6 ⧸ ZSU)) = 1) (F : IsoFlag6) :
    frobAct f F = F := by
  simp [frobAct, hf]

theorem frobAct_of_eq_frobAut {f : frobGroup} (hf : (f : MulAut (SU6 ⧸ ZSU)) = frobAut)
    (F : IsoFlag6) : frobAct f F = frobFlag F := by
  simp [frobAct, hf, frobAut_ne_one]

theorem frobAct_mul (f f' : frobGroup) (F : IsoFlag6) :
    frobAct (f * f') F = frobAct f (frobAct f' F) := by
  rcases mem_frobGroup_iff.mp f.2 with h | h <;> rcases mem_frobGroup_iff.mp f'.2 with h' | h'
  · rw [frobAct_of_eq_one h, frobAct_of_eq_one h', frobAct_of_eq_one (by simp [h, h'])]
  · rw [frobAct_of_eq_one h, frobAct_of_eq_frobAut h', frobAct_of_eq_frobAut (by simp [h, h'])]
  · rw [frobAct_of_eq_frobAut h, frobAct_of_eq_one h', frobAct_of_eq_frobAut (by simp [h, h'])]
  · rw [frobAct_of_eq_frobAut h, frobAct_of_eq_frobAut h', frobFlag_frobFlag,
      frobAct_of_eq_one (by simp [h, h', frobAut_mul_self])]

theorem frobAct_qSmul (f : frobGroup) (q : SU6 ⧸ ZSU) (G : IsoFlag6) :
    frobAct f (qSmul q G) = qSmul ((f : MulAut (SU6 ⧸ ZSU)) q) (frobAct f G) := by
  induction q using QuotientGroup.induction_on with | H h => ?_
  rcases mem_frobGroup_iff.mp f.2 with hf | hf
  · rw [frobAct_of_eq_one hf, frobAct_of_eq_one hf, hf, MulAut.one_apply]
  · rw [frobAct_of_eq_frobAut hf, frobAct_of_eq_frobAut hf, hf, frobAut_mk, qSmul_mk, qSmul_mk,
      frobFlag_smul]

instance : MulAction SUFrob IsoFlag6 where
  smul a F := qSmul a.left (frobAct a.right F)
  one_smul F := by
    change qSmul 1 (frobAct 1 F) = F
    rw [frobAct_of_eq_one rfl, ← QuotientGroup.mk_one, qSmul_mk, one_smul]
  mul_smul a a' F := by
    change qSmul (a * a').left (frobAct (a * a').right F) =
      qSmul a.left (frobAct a.right (qSmul a'.left (frobAct a'.right F)))
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, qSmul_mul, frobAct_mul,
      frobAct_qSmul]
    rfl

theorem SUFrob_smul_def (a : SUFrob) (F : IsoFlag6) : a • F = qSmul a.left (frobAct a.right F) :=
  rfl

@[expose] def lineFlag (v : Fin 6 → K) (hv : v ∈ preSpan 2) (hv0 : v ≠ 0) : IsoFlag6 where
  sub := ![Submodule.span K {v}, preSpan 2, preSpan 3]
  finrank_sub k := by
    fin_cases k
    · exact finrank_span_singleton hv0
    · exact finrank_preSpan (by norm_num)
    · exact finrank_preSpan (by norm_num)
  mono := by
    refine Fin.monotone_iff_le_succ.mpr fun i => ?_
    fin_cases i
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hv
    · exact fun w hw j hj => hw j (by omega)
  isotropic v hv w hw := herm6_eq_zero_of_mem_preSpan hv hw

theorem exists_eq_smul_of_fix {h : SU6} {v : Fin 6 → K} (hv : v ∈ preSpan 2) (hv0 : v ≠ 0)
    (H : h • frobFlag (lineFlag v hv hv0) = lineFlag v hv hv0) :
    ∃ c : K, suLin h (frob6 v) = c • v := by
  have e := congrArg (fun F : IsoFlag6 => F.sub 0) H
  have hmem : suLin h (frob6 v) ∈ Submodule.span K {v} := by
    change _ ∈ (lineFlag v hv hv0).sub 0
    rw [← e]
    exact Submodule.mem_map_of_mem (Submodule.mem_map_of_mem
      (Submodule.mem_span_singleton_self v))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, hc.symm⟩

theorem frob6_uVec (i : Fin 6) : frob6 (uVec i) = uVec i := by
  funext j
  rw [frob6_apply]
  by_cases h : j = i
  · subst h
    simp [bar_one]
  · simp [h, bar_zero]

theorem not_forall_smul_frobFlag (h : SU6) : ¬ ∀ F : IsoFlag6, h • frobFlag F = F := by
  intro H
  have h0 : uVec 0 ∈ preSpan 2 := uVec_mem_preSpan (by decide)
  have h1 : uVec 1 ∈ preSpan 2 := uVec_mem_preSpan (by decide)
  have hne : ∀ c : K, uVec 0 + c • uVec 1 ≠ 0 := fun c e => by
    have := congrFun e 0
    simp at this
  obtain ⟨a, ha⟩ := exists_eq_smul_of_fix h0 (fun e => by simpa using congrFun e 0) (H _)
  obtain ⟨b, hb⟩ := exists_eq_smul_of_fix h1 (fun e => by simpa using congrFun e 1) (H _)
  obtain ⟨c, hc⟩ := exists_eq_smul_of_fix (add_mem h0 (Submodule.smul_mem _ 1 h1)) (hne 1) (H _)
  obtain ⟨d, hd⟩ := exists_eq_smul_of_fix (add_mem h0 (Submodule.smul_mem _ ω h1)) (hne ω) (H _)
  rw [frob6_uVec] at ha hb
  rw [map_add, map_smulₛₗ, frob6_uVec, frob6_uVec, map_add, map_smul, ha, hb] at hc hd
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    have := congrFun ((suLin h).injective (ha.trans (map_zero _).symm)) 0
    simp at this
  have key : ∀ a b c d : K, a ≠ 0 →
      (a • uVec 0 + barHom 1 • b • uVec 1 : Fin 6 → K) 0 = (c • (uVec 0 + 1 • uVec 1)) 0 →
      (a • uVec 0 + barHom 1 • b • uVec 1 : Fin 6 → K) 1 = (c • (uVec 0 + 1 • uVec 1)) 1 →
      (a • uVec 0 + barHom ω • b • uVec 1 : Fin 6 → K) 0 = (d • (uVec 0 + ω • uVec 1)) 0 →
      (a • uVec 0 + barHom ω • b • uVec 1 : Fin 6 → K) 1 = (d • (uVec 0 + ω • uVec 1)) 1 →
      False := by
    decide
  exact key a b c d ha0 (congrFun hc 0) (congrFun hc 1) (congrFun hd 0) (congrFun hd 1)

theorem eq_one_of_forall_smul_SUFrob {a : SUFrob} (h : ∀ F : IsoFlag6, a • F = F) : a = 1 := by
  obtain ⟨q, f⟩ := a
  induction q using QuotientGroup.induction_on with | H g => ?_
  rcases mem_frobGroup_iff.mp f.2 with hf | hf
  · have hg : ∀ F : IsoFlag6, g • F = F := fun F => by
      have := h F
      rwa [SUFrob_smul_def, frobAct_of_eq_one hf, qSmul_mk] at this
    refine SemidirectProduct.ext ((QuotientGroup.eq_one_iff g).mpr ?_) (Subtype.ext hf)
    exact Subgroup.mem_subgroupOf.mpr (mem_scalars_of_forall_smul_eq g hg)
  · exfalso
    exact not_forall_smul_frobFlag g fun F => by
      have := h F
      rwa [SUFrob_smul_def, frobAct_of_eq_frobAut hf, qSmul_mk] at this


abbrev frobHom :
    betaGroup →* frobGroup :=
  betaGroupHom ⟨frobAut, Subgroup.mem_zpowers frobAut⟩ (Subtype.ext frobAut_mul_self)

theorem frobHom_eq_one_iff
    (b : betaGroup) : frobHom b = 1 ↔ (b : MulAut stdGroup) = 1 := by
  rcases mem_betaGroup_iff.mp b.2 with h | h
  · rw [betaGroupHom_of_eq_one _ h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [betaGroupHom_of_eq_betaG _ h, h]
    exact ⟨fun e => absurd (congrArg Subtype.val e) frobAut_ne_one,
      fun e => absurd e betaG_ne_one⟩

abbrev suQ :
    nativeParabolic firstJ →* SU6 ⧸ ZSU :=
  leviSUEquiv.toMonoidHom.comp (leviProj two_mem_firstJ)

theorem leviSUEquiv_eq_suOf
    (l : stdLevi firstJ) : leviSUEquiv l = (suOf l : SU6 ⧸ ZSU) := by
  rw [← leviSUEquiv_liftSU, liftSU_suOf]

theorem leviSUEquiv_betaGL
    (l : stdLevi firstJ) :
    leviSUEquiv ⟨betaGL l, betaGL_mem_stdLevi l.2⟩ = frobAut (leviSUEquiv l) := by
  rw [← liftSU_barSU, leviSUEquiv_liftSU, leviSUEquiv_eq_suOf, frobAut_mk]

theorem suQ_betaPar
    (b : betaGroup) (p : nativeParabolic firstJ) :
    suQ (betaPar b p) = ((frobHom b : frobGroup) : MulAut (SU6 ⧸ ZSU)) (suQ p) := by
  rcases mem_betaGroup_iff.mp b.2 with h | h
  · rw [betaGroupHom_of_eq_one _ h]
    have e : betaPar b p = p := Subtype.ext (by simp [h])
    rw [e]
    rfl
  · rw [betaGroupHom_of_eq_betaG _ h]
    have e' : betaPar b p = ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩ :=
      Subtype.ext (by simp [h, coe_betaG_apply])
    have e : leviProj two_mem_firstJ (betaPar b p) =
        ⟨betaGL (leviProj two_mem_firstJ p : ModGL Tag.E6 K),
          betaGL_mem_stdLevi (leviProj two_mem_firstJ p).2⟩ := by
      apply Subtype.ext
      rw [e']
      exact leviProj_betaGL two_mem_firstJ p
    change leviSUEquiv (leviProj two_mem_firstJ (betaPar b p)) =
      frobAut (leviSUEquiv (leviProj two_mem_firstJ p))
    rw [e, leviSUEquiv_betaGL]

@[expose] noncomputable def thetaFirst :
    parStar firstJ →* SUFrob where
  toFun γ := ⟨suQ (parLeft γ), frobHom γ.1.right⟩
  map_one' := SemidirectProduct.ext (map_one suQ) (map_one frobHom)
  map_mul' γ γ' := SemidirectProduct.ext (by
      change suQ (parLeft (γ * γ')) =
        suQ (parLeft γ) * ((frobHom γ.1.right : frobGroup) : MulAut (SU6 ⧸ ZSU))
          (suQ (parLeft γ'))
      rw [parStar_left_mul, map_mul, suQ_betaPar]) (map_mul frobHom _ _)

theorem thetaFirst_left
    (γ : parStar firstJ) : (thetaFirst γ).left = suQ (parLeft γ) :=
  rfl

theorem thetaFirst_right
    (γ : parStar firstJ) : (thetaFirst γ).right = frobHom γ.1.right :=
  rfl

theorem residueFlag_betaPar_first
    (b : betaGroup) (p : nativeParabolic firstJ) :
    residueFlag (QuotientGroup.mk (betaPar b p)) =
      frobAct (frobHom b) (residueFlag (QuotientGroup.mk p)) := by
  rcases mem_betaGroup_iff.mp b.2 with h | h
  · rw [betaGroupHom_of_eq_one _ h, frobAct_of_eq_one rfl]
    have e : betaPar b p = p := Subtype.ext (by simp [h])
    rw [e]
  · rw [betaGroupHom_of_eq_betaG _ h, frobAct_of_eq_frobAut rfl]
    have e : betaPar b p = ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩ :=
      Subtype.ext (by simp [h, coe_betaG_apply])
    rw [e]
    exact residueFlag_betaGL p

theorem residueFlag_parSmul_first
    (γ : parStar firstJ) (y : ParabolicCosets firstJ) :
    residueFlag (parSmul γ y) = thetaFirst γ • residueFlag y := by
  induction y using QuotientGroup.induction_on with | H p => ?_
  rw [parSmul_mk, parMap_eq_mul, ← smul_eq_mul, ← MulAction.Quotient.smul_mk,
    residueFlag_smul (parLeft γ) (psiA_suOf _), residueFlag_betaPar_first, SUFrob_smul_def,
    thetaFirst_left, thetaFirst_right]
  change _ = qSmul (leviSUEquiv (leviProj two_mem_firstJ (parLeft γ))) _
  rw [leviSUEquiv_eq_suOf, qSmul_mk]

theorem thetaFirst_eq_one_iff
    (γ : parStar firstJ) :
    thetaFirst γ = 1 ↔ (γ.1.right : MulAut stdGroup) = 1 ∧
      (γ.1.left : ModGL Tag.E6 K) ∈ stdRadical firstJ := by
  constructor
  · intro h
    have hl : suQ (parLeft γ) = 1 := congrArg SemidirectProduct.left h
    have hr : frobHom γ.1.right = 1 := congrArg SemidirectProduct.right h
    refine ⟨(frobHom_eq_one_iff _).1 hr, ?_⟩
    rw [← leviProj_eq_one_iff two_mem_firstJ (parLeft γ)]
    exact leviSUEquiv.injective (hl.trans (map_one _).symm)
  · rintro ⟨h1, h2⟩
    refine SemidirectProduct.ext ?_ ((frobHom_eq_one_iff _).2 h1)
    change leviSUEquiv (leviProj two_mem_firstJ (parLeft γ)) = 1
    rw [(leviProj_eq_one_iff two_mem_firstJ (parLeft γ)).2 h2, map_one]

theorem suQ_parLeft_leviStar
    (l : stdLevi firstJ) (b : betaGroup) :
    suQ (parLeft (leviStar two_mem_firstJ l b)) = leviSUEquiv l := by
  change leviSUEquiv (leviProj two_mem_firstJ (parLeft (leviStar two_mem_firstJ l b))) = _
  congr 1
  exact leviProj_of_mem two_mem_firstJ l.2 _

theorem thetaFirst_surjective
    : Function.Surjective thetaFirst := by
  rintro ⟨q, f⟩
  rcases mem_frobGroup_iff.mp f.2 with hf | hf
  · refine ⟨leviStar two_mem_firstJ (leviSUEquiv.symm q) 1, SemidirectProduct.ext ?_ ?_⟩
    · rw [thetaFirst_left, suQ_parLeft_leviStar, MulEquiv.apply_symm_apply]
    · rw [thetaFirst_right, map_one]
      exact Subtype.ext hf.symm
  · refine ⟨leviStar two_mem_firstJ (leviSUEquiv.symm q) betaElt, SemidirectProduct.ext ?_ ?_⟩
    · rw [thetaFirst_left, suQ_parLeft_leviStar, MulEquiv.apply_symm_apply]
    · rw [thetaFirst_right, betaGroupHom_of_eq_betaG _ rfl]
      exact Subtype.ext hf.symm

theorem forall_smul_eq_iff_first
    (γ : parStar firstJ) :
    (∀ x ∈ baseResidue firstJ, γ.1 • x = x) ↔
      (γ.1.right : MulAut stdGroup) = 1 ∧ (γ.1.left : ModGL Tag.E6 K) ∈ stdRadical firstJ := by
  rw [forall_smul_eq_iff, ← thetaFirst_eq_one_iff]
  constructor
  · intro h
    refine eq_one_of_forall_smul_SUFrob fun F => ?_
    obtain ⟨y, rfl⟩ := residueFlag.surjective F
    rw [← residueFlag_parSmul_first, h y]
  · intro h y
    apply residueFlag.injective
    rw [residueFlag_parSmul_first, h, one_smul]


theorem SUFrob_smul_one (h : SU6) (F : IsoFlag6) : (⟨(h : SU6 ⧸ ZSU), 1⟩ : SUFrob) • F = h • F := by
  rw [SUFrob_smul_def, frobAct_of_eq_one rfl, qSmul_mk]

theorem SUFrob_smul_frob (h : SU6) (F : IsoFlag6) :
    (⟨(h : SU6 ⧸ ZSU), ⟨frobAut, Subgroup.mem_zpowers _⟩⟩ : SUFrob) • F = h • frobFlag F := by
  rw [SUFrob_smul_def, frobAct_of_eq_frobAut rfl, qSmul_mk]

theorem thetaFirst_right_of_eq_one
    {γ : parStar firstJ}
    (h : (γ.1.right : MulAut stdGroup) = 1) : (thetaFirst γ).right = 1 :=
  betaGroupHom_of_eq_one _ h

theorem thetaFirst_right_of_eq_betaG
    {γ : parStar firstJ}
    (h : (γ.1.right : MulAut stdGroup) = betaG) :
    ((thetaFirst γ).right : MulAut (SU6 ⧸ ZSU)) = frobAut :=
  congrArg Subtype.val (betaGroupHom_of_eq_betaG _ h)

end CFSG.LieType.Chevalley.C2E6Std.FieldExtension
