module

public import CFSG.RankThree.PartOne.SEITZ8.D4BigCell
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddSpan

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ8
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.LieType.Universal

variable {K : Type} [Field K]

theorem pmone_sigma {σ : K →+* K} {ε : K} (hε : PMOne ε) : σ ε = ε := by
  rcases hε with rfl | rfl <;> simp

section Borel


theorem posRoot_mem_omegaH_odd {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (hpos : 0 < ht γ)
    (c : K) : xPar (rootOperatorFamily d4) γ c ∈ omegaH K := by
  obtain ⟨h1, h2⟩ := posRoot_fix_d4 (K := K) hγ hpos c
  obtain ⟨p, hp, rfl⟩ := exists_pos_of_isRoot hγ
  have hpd : p ∈ dpos := pos_dpos p hp hpos
  refine ⟨1, ?_, ?_, ?_⟩
  · simpa using h1
  · intro x
    simpa using h2 x
  · intro c'
    by_cases h22 : p = 22
    · subst h22
      show xd 22 c * xd 22 c' * (xd 22 c)⁻¹ = xd 22 (((1 : Kˣ) : K) * c')
      rw [Units.val_one, one_mul]
      calc xd 22 c * xd 22 c' * (xd 22 c)⁻¹ = xd 22 (c + c') * (xd 22 c)⁻¹ := by rw [← xd_add]
        _ = xd 22 (c' + c) * (xd 22 c)⁻¹ := by rw [add_comm]
        _ = xd 22 c' * xd 22 c * (xd 22 c)⁻¹ := by rw [xd_add]
        _ = xd 22 c' := by group
    · have hcomm := commute_genO (K := K) (repCheck_22 p hpd h22) c c'
      show xd p c * xd 22 c' * (xd p c)⁻¹ = xd 22 (((1 : Kˣ) : K) * c')
      rw [Units.val_one, one_mul, hcomm.eq]
      group

theorem borel_le_omegaH_odd :
    borel (adjDatum (rootOperatorFamily d4) K) (torus (τ := d4) K) ≤ omegaH K := by
  refine sup_le ?_ ?_
  · refine iSup_le fun i => ?_
    rintro _ ⟨t, rfl⟩
    exact torus_mem_omegaH i t
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγR, hγp⟩ := hγ
    intro x hx
    have hγ' : IsRoot d4 γ := by rwa [adjDatum_roots] at hγR
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ' x).1 hx
    exact posRoot_mem_omegaH_odd hγ' hγp c

end Borel

section Stab

variable {σ : K →+* K}

theorem borel_stab_tw_odd (hσ : ∀ c, σ (σ (σ c)) = c) {b : twistedGroup σ}
    (hb : b ∈ borel (twistedDatum σ) (hHat σ)) :
    ∃ χ : Kˣ, σ (χ : K) = χ ∧
      (b : adjointGroup d4 K) • (rv 22 : RootModule d4 K) = (χ : K) • rv 22 ∧
      (∀ x : RootModule d4 K, coordAt (d4Root 23) ((b : adjointGroup d4 K) • x) =
        ((χ⁻¹ : Kˣ) : K) * coordAt (d4Root 23) x) ∧
      ∀ c : K, (b : adjointGroup d4 K) * xe 22 c * (b : adjointGroup d4 K)⁻¹ =
        xe 22 ((χ : K) * c) := by
  have hbD : (b : adjointGroup d4 K) ∈ omegaH K := borel_le_omegaH_odd (borel_twisted_le σ hb)
  obtain ⟨χ, a1, b1, c1⟩ := hbD
  refine ⟨χ, ?_, a1, b1, c1⟩
  have hF : twistC .D4 K σ (b : adjointGroup d4 K) = b :=
    (mem_twistFixed ..).1 (twistedGroup_le_twistFixed σ b.2)
  have h22 : IsRoot d4 (d4Root 22) := SEITZ8.isRoot_d4 (by norm_num)
  have hfix : rho (d4Root 22) = d4Root 22 := rho_dict.2.2.1
  have hsg := twistSign_of_rho_eq σ hσ h22 hfix
  have hFx : ∀ c : K, twistC .D4 K σ (xe 22 c : adjointGroup d4 K) = xe 22 (σ c) := fun c => by
    show twistC .D4 K σ (xPar (rootOperatorFamily d4) (d4Root 22) c) = _
    rw [twistC_xPar σ h22, hfix, hsg, one_mul]
  have h1 := congrArg (twistC .D4 K σ) (c1 1)
  rw [map_mul, map_mul, map_inv, hF, hFx, hFx, map_one, mul_one] at h1
  have h2 := c1 1
  rw [mul_one] at h2
  rw [h2] at h1
  exact (xPar_injective h22 h1).symm

end Stab

section Weyl


theorem weylElement_conj_xd_odd (i : Fin d4.rank) {p q : ℕ} (hp : p < 24)
    (h : reflect d4 i (d4Root p) = d4Root q) :
    ∃ ε : K, PMOne ε ∧ ∀ c : K,
      weylElement d4 K i * xd p c * (weylElement d4 K i)⁻¹ = xd q (ε * c) := by
  have hγ : IsRoot d4 (d4Root p) := SEITZ8.isRoot_d4 hp
  have hq : IsRoot d4 (d4Root q) := h ▸ IsRoot.reflect i hγ
  refine ⟨(((rootOperatorFamily d4).sign i ⟨d4Root p, hγ⟩ : ℤ) : K), ?_, fun c => ?_⟩
  · rcases (rootOperatorFamily d4).sign_eq i ⟨d4Root p, hγ⟩ with h1 | h1 <;> rw [h1] <;>
      simp [PMOne]
  · have hF := (rootOperatorFamily d4).weylElement_mul_eltElement_mul_inv (K := K) i
      ⟨d4Root p, hγ⟩ c
    have e : simple d4 i • (⟨d4Root p, hγ⟩ : Root d4) = ⟨d4Root q, hq⟩ := by
      rw [simple_smul_eq_sRoot]
      exact Subtype.ext h
    rw [e] at hF
    simpa [xd, xPar_of_isRoot hγ, xPar_of_isRoot hq] using hF

@[expose] def RootMove (m : adjointGroup d4 K) (p q : ℕ) : Prop :=
  RvMove m p q ∧ ∃ ε : K, PMOne ε ∧ ∀ c : K, m * xd p c * m⁻¹ = xd q (ε * c)

theorem RootMove.comp {a b : adjointGroup d4 K} {p q s : ℕ} (ha : RootMove a p q)
    (hb : RootMove b q s) : RootMove (b * a) p s := by
  obtain ⟨ha1, ε₁, h₁, ha2⟩ := ha
  obtain ⟨hb1, ε₂, h₂, hb2⟩ := hb
  refine ⟨ha1.comp hb1, ε₂ * ε₁, h₂.mul h₁, fun c => ?_⟩
  rw [show b * a * xd p c * (b * a)⁻¹ = b * (a * xd p c * a⁻¹) * b⁻¹ by group, ha2, hb2,
    mul_assoc]

theorem weylElement_rootMove (i : Fin d4.rank) {p q : ℕ} (hp : p < 24)
    (h : reflect d4 i (d4Root p) = d4Root q) :
    RootMove (weylElement d4 K i : adjointGroup d4 K) p q := by
  obtain ⟨ε, hε, h2⟩ := weylElement_conj_xd_odd (K := K) i hp h
  exact ⟨weylElement_rvMove i hp h, ε, hε, h2⟩

theorem long_step_zero' : ∀ p ∈ longPos, ∃ q ∈ longPos,
    reflect d4 (nd 2) (d4Root p) = d4Root q := long_step_zero

theorem long_step_one' : ∀ p ∈ longPos, ∃ q₃ < 24, ∃ q₁ < 24, ∃ q ∈ longPos,
    reflect d4 (nd 3) (d4Root p) = d4Root q₃ ∧ reflect d4 (nd 1) (d4Root q₃) = d4Root q₁ ∧
      reflect d4 (nd 0) (d4Root q₁) = d4Root q := long_step_one

theorem gen_stab_odd (i : Fin (Tag.rank .G2)) {t : ℕ} (ht : t ∈ longPos) :
    ∃ q ∈ longPos, RootMove (nHatE K i : adjointGroup d4 K) t q := by
  have ht24 : t < 24 := lt_of_mem_longPos ht
  match i with
  | ⟨0, _⟩ =>
    obtain ⟨q, hq, hr⟩ := long_step_zero' t ht
    refine ⟨q, hq, ?_⟩
    rw [show (⟨0, by decide⟩ : Fin (Tag.rank .G2)) = ng 0 from rfl, nHatE_zero]
    exact weylElement_rootMove (nd 2) ht24 hr
  | ⟨1, _⟩ =>
    obtain ⟨q₃, hq₃, q₁, hq₁, q, hq, h3, h1, h0⟩ := long_step_one' t ht
    refine ⟨q, hq, ?_⟩
    rw [show (⟨1, by decide⟩ : Fin (Tag.rank .G2)) = ng 1 from rfl, nHatE_one]
    have := ((weylElement_rootMove (K := K) (nd 3) ht24 h3).comp
      (weylElement_rootMove (K := K) (nd 1) hq₃ h1)).comp
      (weylElement_rootMove (K := K) (nd 0) hq₁ h0)
    rw [← mul_assoc] at this
    exact this

theorem listProd_stab_odd (ω : List (Fin (Tag.rank .G2))) :
    ∃ t ∈ longPos, RootMove ((ω.map (nHatE K)).prod : adjointGroup d4 K) 22 t := by
  induction ω with
  | nil =>
    refine ⟨22, by simp [longPos], ?_⟩
    exact ⟨⟨1, Or.inl rfl, by simp⟩, 1, Or.inl rfl, fun c => by simp⟩
  | cons i ω ih =>
    obtain ⟨t, ht, h⟩ := ih
    obtain ⟨q, hq, hs⟩ := gen_stab_odd (K := K) i ht
    refine ⟨q, hq, ?_⟩
    rw [List.map_cons, List.prod_cons]
    exact h.comp hs

set_option linter.overlappingInstances false in
theorem listProd_stab_tw_odd (ω : List (Fin (Tag.rank .G2))) {σ : K →+* K} :
    ∃ t ∈ longPos, RootMove ((((ω.map (nHat σ)).prod : twistedGroup σ)) : adjointGroup d4 K) 22
      t := by
  obtain ⟨t, ht, h⟩ := listProd_stab_odd (K := K) ω
  refine ⟨t, ht, ?_⟩
  rw [coe_listProd_nHat]
  exact h

end Weyl

section BigCell

variable {σ : K →+* K}

theorem nrep_stab_tw_odd (hσ : ∀ c, σ (σ (σ c)) = c)
    (w : (coxeterMatrix (twistedDatum σ).isFiniteType).Group) :
    ∃ t ∈ longPos, RootMove
      ((nrep (twistedDatum_isCTGroupDatum σ hσ) w : twistedGroup σ) : adjointGroup d4 K) 22 t := by
  obtain ⟨ω, hω, rfl⟩ :=
    ((coxeterMatrix (twistedDatum σ).isFiniteType).toCoxeterSystem).exists_isReduced w
  rw [nrep_wordProd (twistedDatum_isCTGroupDatum σ hσ) hω]
  exact listProd_stab_tw_odd ω

theorem reflect_W_check' :
    reflect d4 (nd 3) (d4Root 2) = d4Root 9 ∧ reflect d4 (nd 1) (d4Root 9) = d4Root 15 ∧
    reflect d4 (nd 0) (d4Root 15) = d4Root 19 ∧ reflect d4 (nd 2) (d4Root 19) = d4Root 22 ∧
    reflect d4 (nd 3) (d4Root 8) = d4Root 16 ∧ reflect d4 (nd 1) (d4Root 16) = d4Root 20 ∧
    reflect d4 (nd 0) (d4Root 20) = d4Root 21 ∧ reflect d4 (nd 2) (d4Root 21) = d4Root 23 := by
  decide +kernel

theorem Wt_rootMove_B : RootMove (Wt : adjointGroup d4 K) 2 22 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := reflect_W_check'
  have := (((weylElement_rootMove (K := K) (nd 3) (p := 2) (by decide) h1).comp
    (weylElement_rootMove (K := K) (nd 1) (p := 9) (by decide) h2)).comp
    (weylElement_rootMove (K := K) (nd 0) (p := 15) (by decide) h3)).comp
    (weylElement_rootMove (K := K) (nd 2) (p := 19) (by decide) h4)
  have e : (Wt : adjointGroup d4 K) = weylElement d4 K (nd 2) * (weylElement d4 K (nd 0) *
      (weylElement d4 K (nd 1) * weylElement d4 K (nd 3))) := by
    unfold Wt
    group
  rw [e]
  exact this

theorem Wt_rootMove_Bneg : RootMove (Wt : adjointGroup d4 K) 8 23 := by
  obtain ⟨-, -, -, -, h1, h2, h3, h4⟩ := reflect_W_check'
  have := (((weylElement_rootMove (K := K) (nd 3) (p := 8) (by decide) h1).comp
    (weylElement_rootMove (K := K) (nd 1) (p := 16) (by decide) h2)).comp
    (weylElement_rootMove (K := K) (nd 0) (p := 20) (by decide) h3)).comp
    (weylElement_rootMove (K := K) (nd 2) (p := 21) (by decide) h4)
  have e : (Wt : adjointGroup d4 K) = weylElement d4 K (nd 2) * (weylElement d4 K (nd 0) *
      (weylElement d4 K (nd 1) * weylElement d4 K (nd 3))) := by
    unfold Wt
    group
  rw [e]
  exact this

theorem psiB_upper_odd (hσ : ∀ c, σ (σ (σ c)) = c) :
    ∃ ε : K, PMOne ε ∧ ∀ c : fixedField σ,
      ((psiB σ hσ (sl2Upper c) : twistedGroup σ) : adjointGroup d4 K) = xd 22 (ε * (c : K)) := by
  obtain ⟨-, ε, hε, h⟩ := Wt_rootMove_B (K := K)
  refine ⟨ε, hε, fun c => ?_⟩
  have e : xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) (c : K) = xd 2 (c : K) := by
    simp only [xd, d4Root_dict.1]
  simp only [psiB, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_mul, Subgroup.coe_inv, Wg_val, slLong_val, slLongE_upper]
  rw [e]
  exact h c

theorem psiB_lower_odd (hσ : ∀ c, σ (σ (σ c)) = c) :
    ∃ ε : K, PMOne ε ∧ ∀ c : fixedField σ,
      ((psiB σ hσ (sl2Lower c) : twistedGroup σ) : adjointGroup d4 K) = xd 23 (ε * (c : K)) := by
  obtain ⟨-, ε, hε, h⟩ := Wt_rootMove_Bneg (K := K)
  refine ⟨ε, hε, fun c => ?_⟩
  have e : xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) (c : K) = xd 8 (c : K) := by
    simp only [xd, d4Root_dict.2.1]
  simp only [psiB, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_mul, Subgroup.coe_inv, Wg_val, slLong_val, slLongE_lower]
  rw [e]
  exact h c

theorem bigCell_tw_odd (hσ : ∀ c, σ (σ (σ c)) = c) (g : twistedGroup σ)
    (hne0 : coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) ≠ 0) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) →* twistedGroup σ,
      ∃ μ₁ μ₂ : fixedField σ, μ₁ ≠ 0 ∧ μ₂ ≠ 0 ∧
        (∃ ε : K, PMOne ε ∧ (μ₁ : K) * (μ₂ : K) =
          ε * coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K))) ∧
        (∀ c : fixedField σ, ψ (sl2Upper (μ₁ * c)) = psiB σ hσ (sl2Upper c)) ∧
        (∀ c : fixedField σ,
          ψ (sl2Lower (μ₂ * c)) = g * psiB σ hσ (sl2Upper c) * g⁻¹) := by
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hext := twistedDatum_steinbergExtras σ hσ
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hg⟩ := exists_mem_bruhatCell hct hext g
  obtain ⟨χ₁, hχ₁, a1, bb1, c1⟩ := borel_stab_tw_odd hσ hb₁
  obtain ⟨χ₂, hχ₂, a2, bb2, c2⟩ := borel_stab_tw_odd hσ hb₂
  obtain ⟨t, ht, ⟨e₁, he₁, hv⟩, e₂, he₂, hc⟩ := nrep_stab_tw_odd (K := K) hσ w
  obtain ⟨εu, hεu, hu⟩ := psiB_upper_odd (K := K) hσ
  obtain ⟨εl, hεl, hl⟩ := psiB_lower_odd (K := K) hσ
  set n : adjointGroup d4 K := ((nrep hct w : twistedGroup σ) : adjointGroup d4 K) with hn
  have hgc : (g : adjointGroup d4 K) = (b₁ : adjointGroup d4 K) * n * (b₂ : adjointGroup d4 K) := by
    rw [hg]
    rfl
  have hlam : coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) =
      ((χ₁⁻¹ : Kˣ) : K) * ((χ₂ : K) * (e₁ * coordAt (d4Root 23) (rv t : RootModule d4 K))) := by
    rw [hgc, mul_smul, mul_smul, a2, smul_smul_comm' n (χ₂ : K) (rv 22 : RootModule d4 K), hv,
      bb1, coordAt_smul, coordAt_smul]
  have ht23 : t = 23 := by
    by_contra hne
    apply hne0
    have h1 : d4Root 23 ≠ d4Root t := fun h => hne (d4Root_inj t (lt_of_mem_longPos ht) 23
      (by norm_num) h.symm)
    rw [hlam, rv, coordAt_rootVec_ne h1]
    simp
  subst ht23
  have hμ₁ : σ (((χ₁⁻¹ : Kˣ)) : K) = ((χ₁⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hχ₁]
  have hμ₂ : σ (εl * (e₂ * (εu * (χ₂ : K)))) = εl * (e₂ * (εu * (χ₂ : K))) := by
    rw [map_mul, map_mul, map_mul, pmone_sigma hεl, pmone_sigma he₂, pmone_sigma hεu, hχ₂]
  have hεl0 : εl ≠ 0 := by rcases hεl with rfl | rfl <;> simp
  have he₂0 : e₂ ≠ 0 := by rcases he₂ with rfl | rfl <;> simp
  have hεu0 : εu ≠ 0 := by rcases hεu with rfl | rfl <;> simp
  refine ⟨(MulAut.conj b₁).toMonoidHom.comp (psiB σ hσ), ⟨((χ₁⁻¹ : Kˣ) : K), hμ₁⟩,
    ⟨εl * (e₂ * (εu * (χ₂ : K))), hμ₂⟩, fun h => Units.ne_zero χ₁⁻¹ (congrArg Subtype.val h),
    fun h => mul_ne_zero hεl0 (mul_ne_zero he₂0 (mul_ne_zero hεu0 (Units.ne_zero χ₂)))
      (congrArg Subtype.val h),
    ⟨εl * e₂ * εu * e₁, ((hεl.mul he₂).mul hεu).mul he₁, ?_⟩, fun c => ?_, fun c => ?_⟩
  · show ((χ₁⁻¹ : Kˣ) : K) * (εl * (e₂ * (εu * (χ₂ : K)))) = _
    rw [hlam, rv, coordAt_rootVec_self (SEITZ8.isRoot_d4 (by norm_num))]
    calc ((χ₁⁻¹ : Kˣ) : K) * (εl * (e₂ * (εu * (χ₂ : K))))
        = (e₁ * e₁) * (((χ₁⁻¹ : Kˣ) : K) * (εl * (e₂ * (εu * (χ₂ : K))))) := by
          rw [he₁.sq, one_mul]
      _ = _ := by ring
  · apply Subtype.ext
    have e1 : ((⟨((χ₁⁻¹ : Kˣ) : K), hμ₁⟩ * c : fixedField σ) : K) =
        ((χ₁⁻¹ : Kˣ) : K) * (c : K) := rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hu, hu, e1]
    show (b₁ : adjointGroup d4 K) * xe 22 (εu * (((χ₁⁻¹ : Kˣ) : K) * (c : K))) *
      (b₁ : adjointGroup d4 K)⁻¹ = xe 22 (εu * (c : K))
    rw [c1]
    congr 1
    calc (χ₁ : K) * (εu * (((χ₁⁻¹ : Kˣ) : K) * (c : K)))
        = εu * (((χ₁ : Kˣ) : K) * ((χ₁⁻¹ : Kˣ) : K)) * (c : K) := by ring
      _ = εu * (c : K) := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · apply Subtype.ext
    have e2 : ((⟨εl * (e₂ * (εu * (χ₂ : K))), hμ₂⟩ * c : fixedField σ) : K) =
        (εl * (e₂ * (εu * (χ₂ : K)))) * (c : K) := rfl
    have hR : ((g * psiB σ hσ (sl2Upper c) * g⁻¹ : twistedGroup σ) : adjointGroup d4 K) =
        (g : adjointGroup d4 K) * xd 22 (εu * (c : K)) * (g : adjointGroup d4 K)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hu]
    have hL : (((MulAut.conj b₁).toMonoidHom.comp (psiB σ hσ)) (sl2Lower
        (⟨εl * (e₂ * (εu * (χ₂ : K))), hμ₂⟩ * c)) : adjointGroup d4 K) =
        (b₁ : adjointGroup d4 K) * xd 23 (εl * ((εl * (e₂ * (εu * (χ₂ : K)))) * (c : K))) *
          (b₁ : adjointGroup d4 K)⁻¹ := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hl, e2]
    rw [hL, hR, hgc]
    have e : (b₁ : adjointGroup d4 K) * n * (b₂ : adjointGroup d4 K) * xd 22 (εu * (c : K)) *
        ((b₁ : adjointGroup d4 K) * n * (b₂ : adjointGroup d4 K))⁻¹ =
        (b₁ : adjointGroup d4 K) * (n * ((b₂ : adjointGroup d4 K) * xe 22 (εu * (c : K)) *
          (b₂ : adjointGroup d4 K)⁻¹) * n⁻¹) * (b₁ : adjointGroup d4 K)⁻¹ := by
      group
    rw [e, c2, hc]
    congr 3
    calc εl * (εl * (e₂ * (εu * (χ₂ : K))) * (c : K))
        = (εl * εl) * (e₂ * (εu * (χ₂ : K))) * (c : K) := by ring
      _ = e₂ * ((χ₂ : K) * (εu * (c : K))) := by rw [hεl.sq]; ring

end BigCell

end CFSG.HardMathSupport.Seitz.TrialityOdd
