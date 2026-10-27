module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz6
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz5
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs245b
public import CFSG.HardMathSupport.Dickson.Bal207.RankSyl
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4SocleFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex IsL2EightIndex Seitz2310CubeSimple)

open CFSG.AGLEmbeddingD2 (KFactSeitzRankTwo IsD2SeitzException)

open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple ambiguousChev)

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

open GL83.CompFam

set_option linter.unusedSectionVars false

section Dispatch


theorem le_glbCore_of_index_cube (h2 : KFactSeitzRankTwo) (hQ : SeitzQuasiAt 3)
    (hRes : InputsSeitz5.Input23_19ExcRes) {X : Type} [Group X] [Finite X]
    (hKX : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcore : GLAPPrimeCore p X = ⊥)
    {B : Subgroup X} (hB : IsElemAbelian p B) (hB4 : 4 ≤ CFSG.Open.pRank p B)
    (hrk : CFSG.Open.pRank p B = CFSG.Open.pRank p (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (haut : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)))
    (hsmall : p ^ (CFSG.Open.pRank p B - 2) * Nat.card (cen B K) < Nat.card (stab B K))
    (d : TauCeti.ValidLieTypeIndex) (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : p ≠ d.1.characteristic) : K ≤ GLBCore p 2 B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3le : p ^ 3 * Nat.card (cen B K) ≤ Nat.card (stab B K) :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by omega))).trans
      (InputsSeitz3.pow_succ_mul_le hp hB hsmall)
  have hL34 : ¬ (p = 3 ∧ IsLThreeFour (↥K ⧸ Subgroup.center ↥K)) := by
    rintro ⟨rfl, h⟩
    have h1 := InputsSeitz3.pRank_mulAut_le_two_of_l34 hK.2.2.1 h
    omega
  by_cases hgood : ¬ ExcIndex p d.1
  · obtain ⟨E, hEN, hEC, hEcard⟩ := InputsSeitz3.exists_faithful hp hB h3le
    have hEB : E ≤ B := hEN.trans inf_le_left
    have hENK : E ≤ Subgroup.normalizer (K : Set X) := hEN.trans inf_le_right
    have hEel : IsElemAbelian p E := elem_mono hB hEB
    have hgen := hQ p hp hp2 ↥K hK.2.2 d ⟨e⟩ hpd hL34 _ (InputsSeitz3.isElemAbelian_autIm hEel K)
      (by rw [InputsSeitz3.card_autIm hENK hEC, hEcard]) (Or.inl hgood)
    exact InputsSeitz3.le_glbCore_of_centGenI hp hEB hEel hEcard.ge
      (InputsSeitz3.le_centGenI_of_autIm hENK hEC hgen)
  have hexc : ExcIndex p d.1 := not_not.1 hgood
  by_cases hsix : IsSixIndex d.1 ∧ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range
  · obtain ⟨E, hEN, hEC, hEcard⟩ := InputsSeitz3.exists_faithful hp hB h3le
    have hEB : E ≤ B := hEN.trans inf_le_left
    have hENK : E ≤ Subgroup.normalizer (K : Set X) := hEN.trans inf_le_right
    have hEel : IsElemAbelian p E := elem_mono hB hEB
    have hgen := hQ p hp hp2 ↥K hK.2.2 d ⟨e⟩ hpd hL34 _ (InputsSeitz3.isElemAbelian_autIm hEel K)
      (by rw [InputsSeitz3.card_autIm hENK hEC, hEcard])
      (Or.inr ⟨hsix.1, (InputsSeitz5.autIm_mono hEB K).trans hsix.2⟩)
    exact InputsSeitz3.le_glbCore_of_centGenI hp hEB hEel hEcard.ge
      (InputsSeitz3.le_centGenI_of_autIm hENK hEC hgen)
  by_cases hroute : Subgroup.center ↥K = ⊥ ∧ cen B K ≠ ⊥ ∧ ¬ IsD2SeitzException p d.1
  · obtain ⟨hZ, hC1, hnd⟩ := hroute
    obtain ⟨E₂, hE₂N, hE₂C, hE₂card⟩ := InputsSeitz3.exists_faithful hp hB (k := 2)
      ((Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by norm_num))).trans h3le)
    have hE₂B : E₂ ≤ B := hE₂N.trans inf_le_left
    have hE₂NK : E₂ ≤ Subgroup.normalizer (K : Set X) := hE₂N.trans inf_le_right
    have hE₂el : IsElemAbelian p E₂ := elem_mono hB hE₂B
    have hgen := InputsSeitz3.seitzHyperGamma_eq_top_of_plane h2 hp hp2 hZ d e hpd hnd
      (InputsSeitz3.isElemAbelian_autIm hE₂el K) (by rw [InputsSeitz3.card_autIm hE₂NK hE₂C, hE₂card])
    have hE₂cen : E₂ ⊓ cen B K = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_left _ (inf_le_right : cen B K ≤ _)).trans hE₂C.le)
    exact InputsSeitz3.le_glbCore_of_centGenI_central hp hB hE₂B inf_le_left inf_le_right hE₂cen hC1
      hE₂card.ge (InputsSeitz3.le_centGenI_of_autIm hE₂NK hE₂C hgen)
  have hsm : ¬ (d.1 = .tits ∨ d.1 = .suzuki 2 ∨ IsL2EightIndex d.1) := fun h => by
    have h1 := InputsSeitz5.pRank_mulAut_le_two_of_small hK.2.2 d e hexc h
    omega
  refine hRes X hKX p hp hp2 hcore B hB hB4 hrk K hK haut hsmall d ⟨e⟩ hexc
    (fun h => hsm (Or.inl h)) (fun h => hsm (Or.inr (Or.inl h))) (fun h => hsm (Or.inr (Or.inr h)))
    (fun h6 hin => hsix ⟨h6, hin⟩) ?_
  by_cases hZ : Subgroup.center ↥K = ⊥
  · by_cases hC1 : cen B K = ⊥
    · exact Or.inr (Or.inl hC1)
    · exact Or.inr (Or.inr (by by_contra hnd; exact hroute ⟨hZ, hC1, hnd⟩))
  · exact Or.inl hZ

theorem input23_19ChevCore_of_seitzQuasiAt (h2 : KFactSeitzRankTwo)
    (hQ : SeitzQuasiAt 3) (hRes : InputsSeitz5.Input23_19ExcRes) : InputsSeitz.Input23_19ChevCore := by
  intro X _ _ hKX p hp hp2 hcore B hB hB4 hrk K hK hch haut
  haveI : Fact p.Prime := ⟨hp⟩
  have hBcard : Nat.card B = p ^ CFSG.Open.pRank p B := GL83.PiGen.card_eq_pow_pRank hB
  by_cases hsmall : Nat.card (stab B K) ≤ p ^ (CFSG.Open.pRank p B - 2) * Nat.card (cen B K)
  · exact InputsSeitz.le_glbCore_of_card_stab_le hp hB hK 2 (CFSG.Open.pRank p B - 2) (by omega)
      (by rw [hBcard]; exact Nat.pow_le_pow_right hp.pos (by omega)) hsmall
  push Not at hsmall
  have hdisp : ∀ (d : TauCeti.ValidLieTypeIndex),
      (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) → p ≠ d.1.characteristic →
        K ≤ GLBCore p 2 B := fun d e hpd =>
    le_glbCore_of_index_cube h2 hQ hRes hKX hp hp2 hcore hB hB4 hrk hK haut hsmall d e hpd
  obtain ⟨q, -, hqp, hc⟩ := hch
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  rcases hc with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · rcases i with ⟨r, hr⟩ | ⟨n, hn⟩ | d | s
    · exact hi.elim
    · exact hi.elim
    · have hdq : d.1.characteristic = q := hi
      exact hdisp d e (fun h => hqp (hdq.symm.trans h.symm))
    · exact hi.elim
  · rcases i with ⟨r, hr⟩ | ⟨n, hn⟩ | d | s
    · exact hi.elim
    · exact InputsSeitz.le_glbCore_of_alt hp hp2 hB hB4 hrk hK ⟨e⟩
    · by_cases hpd : p = d.1.characteristic
      swap
      · exact hdisp d e hpd
      exfalso
      obtain ⟨d1, hv⟩ := d
      cases d1 with
      | A k q' =>
        rcases k with _ | _ | k
        · simp [ambiguousChev] at hi
        · have hi' : (q'.card = 7 ∧ q = 2) ∨ (q'.card = 8 ∧ q = 3) := by
            simpa [ambiguousChev] using hi
          rcases hi' with ⟨h7, -⟩ | ⟨h8, -⟩
          · have hq7 : q'.p = 7 :=
              Claims1116c.p_eq_of_card_eq (k := 1) (by norm_num) (by rw [h7]; norm_num)
            have hp7 : p = 7 := by rw [hpd]; simpa using hq7
            subst hp7
            have h1 := Claims1116c.pRank_aut_le_one hp hperf e
              (dvd_of_eq (Claims1116c.card_mulAut_L27 (q' := q') (hv := hv) h7 (MulEquiv.refl _)))
              (by norm_num)
            omega
          · have hq2 : q'.p = 2 :=
              Claims1116c.p_eq_of_card_eq (k := 3) Nat.prime_two (by rw [h8]; norm_num)
            exact hp2 (by rw [hpd]; simpa using hq2)
        · simp [ambiguousChev] at hi
      | twistedA k q' =>
        rcases k with _ | _ | _ | _ | k
        · simp [ambiguousChev] at hi
        · simp [ambiguousChev] at hi
        · have hi' : q'.card = 3 ∧ q = 2 := by simpa [ambiguousChev] using hi
          have hq3 : q'.p = 3 :=
            Claims1116c.p_eq_of_card_eq (k := 1) Nat.prime_three (by rw [hi'.1]; norm_num)
          have hp3 : p = 3 := by rw [hpd]; simpa using hq3
          subst hp3
          have hexp : q'.exponent = 1 := by
            have h1 : 3 ^ q'.exponent = 3 ^ 1 := by
              rw [← hq3, ← TauCeti.PrimePower.card_def, hi'.1, hq3, pow_one]
            exact Nat.pow_right_injective (by norm_num) h1
          have h1 := (InputsSeitz5.pRank_mulAut_le_quot Nat.prime_three hperf).trans
            (CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_two_of_unitaryThree
              CFSG.AGLEmbedding.kFactUnitaryAutElemRank ⟨q', hq3, rfl⟩ (by simp [hexp]) e)
          omega
        · have hi' : q'.card = 2 ∧ q = 3 := by simpa [ambiguousChev] using hi
          have hq2 : q'.p = 2 :=
            Claims1116c.p_eq_of_card_eq (k := 1) Nat.prime_two (by rw [hi'.1]; norm_num)
          exact hp2 (by rw [hpd]; simpa using hq2)
        · simp [ambiguousChev] at hi
      | _ => simp [ambiguousChev] at hi
    · exact hi.elim

end Dispatch

section Narrow2319

variable {X : Type} [Group X] [Finite X]

theorem comm_of_ne_comp {K L : Subgroup X} (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤)
    (hne : K ≠ L) : ∀ x ∈ K, ∀ y ∈ L, x * y = y * x := by
  intro x hx y hy
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne K L hK hL hne
  have hxc : x ∈ Subgroup.centralizer (L : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hx
  exact (Subgroup.mem_centralizer_iff.1 hxc y hy).symm

theorem three_mul_pRank_le_of_not_mem {p : ℕ} (hp : p.Prime) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥K)) {b : X} (hb : b ∉ Subgroup.normalizer (K : Set X))
    (hbb : b * b ∉ Subgroup.normalizer (K : Set X)) :
    3 * CFSG.Open.pRank p K ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set K₁ := cj b K with hK₁def
  set K₂ := cj (b * b) K with hK₂def
  have hK₁ : IsComponentOf K₁ ⊤ := isComponentOf_cj hK b
  have hK₂ : IsComponentOf K₂ ⊤ := isComponentOf_cj hK (b * b)
  have h01 : K ≠ K₁ := fun h => hb (cj_eq_iff_mem_normalizer.1 h.symm)
  have h02 : K ≠ K₂ := fun h => hbb (cj_eq_iff_mem_normalizer.1 h.symm)
  have h12 : K₁ ≠ K₂ := by
    intro h
    apply h01
    have h' := congrArg (cj b⁻¹) h
    rw [hK₁def, hK₂def, cj_inv_cj, cj_mul, cj_inv_cj] at h'
    exact h'
  have hc01 := comm_of_ne_comp hK hK₁ h01
  have hc02 := comm_of_ne_comp hK hK₂ h02
  have hc12 := comm_of_ne_comp hK₁ hK₂ h12
  obtain ⟨E₀, hE₀K, hE₀, hE₀c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt K
  set r := CFSG.Open.pRank p K with hr
  set E₁ := cj b E₀ with hE₁def
  set E₂ := cj (b * b) E₀ with hE₂def
  have hE₁K : E₁ ≤ K₁ := cj_mono b hE₀K
  have hE₂K : E₂ ≤ K₂ := cj_mono (b * b) hE₀K
  have hE₁ : IsElemAbelian p E₁ := CFSG.SectionRank.isElemAbelian_map hE₀ _
  have hE₂ : IsElemAbelian p E₂ := CFSG.SectionRank.isElemAbelian_map hE₀ _
  have hE₁c : Nat.card E₁ = p ^ r := by
    show Nat.card (E₀.map (MulAut.conj b).toMonoidHom) = _
    rw [Subgroup.card_map_of_injective (MulAut.conj b).injective, hE₀c]
  have hE₂c : Nat.card E₂ = p ^ r := by
    show Nat.card (E₀.map (MulAut.conj (b * b)).toMonoidHom) = _
    rw [Subgroup.card_map_of_injective (MulAut.conj (b * b)).injective, hE₀c]
  have hc : ∀ x ∈ E₀, ∀ y ∈ E₁, x * y = y * x := fun x hx y hy => hc01 x (hE₀K hx) y (hE₁K hy)
  have hd01 : E₀ ⊓ E₁ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rw [Subgroup.mem_bot]
    exact InputsSeitz.eq_one_of_mem_center hp hZ (hE₀K hx.1)
      (fun y hy => (hc01 y hy x (hE₁K hx.2)).symm) (hE₀.2 x hx.1)
  have hE01 : IsElemAbelian p (E₀ ⊔ E₁) := CFSG.Open.IsElemAbelian.sup_of_commute hE₀ hE₁ hc
  have hE01c : Nat.card (E₀ ⊔ E₁ : Subgroup X) = p ^ (r + r) := by
    rw [card_sup_of_commute_of_inf_eq_bot hc hd01, hE₀c, hE₁c, pow_add]
  have hE01C : E₀ ⊔ E₁ ≤ Subgroup.centralizer (K₂ : Set X) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_iff.2 fun y hy => (hc02 x (hE₀K hx) y hy).symm
    · exact Subgroup.mem_centralizer_iff.2 fun y hy => (hc12 x (hE₁K hx) y hy).symm
  have hc' : ∀ x ∈ E₀ ⊔ E₁, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (hE01C hx) y (hE₂K hy)).symm
  have hd : (E₀ ⊔ E₁) ⊓ E₂ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rw [Subgroup.mem_bot]
    obtain ⟨hx01, hx2⟩ := hx
    set g := b * b with hg
    have hy : g⁻¹ * x * g ∈ E₀ := mem_cj.1 hx2
    have hyc : ∀ k ∈ K, (g⁻¹ * x * g) * k = k * (g⁻¹ * x * g) := by
      intro k hk
      have hk2 : g * k * g⁻¹ ∈ K₂ := mul_mem_cj hk
      have h1 : g * k * g⁻¹ * x = x * (g * k * g⁻¹) :=
        Subgroup.mem_centralizer_iff.1 (hE01C hx01) _ hk2
      calc (g⁻¹ * x * g) * k = g⁻¹ * (x * (g * k * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * k * g⁻¹ * x) * g := by rw [h1]
        _ = k * (g⁻¹ * x * g) := by group
    have h1 : g⁻¹ * x * g = 1 :=
      InputsSeitz.eq_one_of_mem_center hp hZ (hE₀K hy) (fun k hk => hyc k hk) (hE₀.2 _ hy)
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have := InputsSeitz.add_le_pRank_of_commute hp hE01 hE₂ hc' hd hE01c hE₂c
  omega

section Ree32


open CFSG.ComponentClassification.OuterAutomorphisms (Outer) 
in
theorem pRank_five_mulAut_le_three_of_ree32 {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .reeF4 2)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut K)) ≤ 3 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine (InputsSeitz5.pRank_mulAut_le_quot Nat.prime_five hq.1).trans ?_
  have hs : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.exists_noncomm_quot hq
  have hZ := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple hs hnab
  refine (CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_add_pRank_outer Nat.prime_five hZ).trans ?_
  have hdR : CFSG.AGLEmbedding.IsReeFFourFiveIndex d := hd
  have h1 : CFSG.Open.pRank 5 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 2 := by
    refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
    have h := CFSG.HardMathSupport.Malle.LocalAction.pRank_le_two_of_isPGroup hdR ⟨e⟩ E
      (CFSG.Open.IsElemAbelian.isPGroup hE)
    rw [GL83.PiGen.card_eq_pow_pRank hE]
    exact Nat.pow_le_pow_right (by norm_num) h
  have h2 : CFSG.Open.pRank 5 (⊤ : Subgroup (Outer (K ⧸ Subgroup.center K))) ≤ 1 := by
    obtain ⟨F, _, _, _, hF, ⟨eΓ⟩⟩ := CFSG.HardMathSupport.Malle.LocalAction.exists_reeGamma_model hdR ⟨e⟩
    obtain ⟨hcyc, -⟩ := CFSG.AGLEmbedding.outer_reeGamma (a := 2) (K := F) (by norm_num) hF
    let eO := CFSG.ComponentClassification.OuterAutomorphisms.equivalence eΓ
    haveI : IsCyclic (Outer (K ⧸ Subgroup.center K)) :=
      isCyclic_of_surjective eO.symm.toMonoidHom eO.symm.surjective
    exact CFSG.LocalAnalysis.RankFourTheoremC.pRank_le_one_of_isCyclic Nat.prime_five inferInstance
  omega

theorem false_of_ree32_faithful (hGA : GriessMultipliersAllModels) (hcore : GLAPPrimeCore 5 X = ⊥)
    {B : Subgroup X} (hB : IsElemAbelian 5 B) (hB4 : 4 ≤ CFSG.Open.pRank 5 B)
    (hrk : CFSG.Open.pRank 5 B = CFSG.Open.pRank 5 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤)
    (hsmall : 5 ^ (CFSG.Open.pRank 5 B - 2) * Nat.card (cen B K) < Nat.card (stab B K))
    (d : TauCeti.ValidLieTypeIndex) (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : d.1 = .reeF4 2) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp : Nat.Prime 5 := Nat.prime_five
  have hpd : 5 ≠ d.1.characteristic := by
    rw [hd, TauCeti.LieTypeIndex.characteristic_reeF4]
    decide
  have hZ : ¬ 5 ∣ Nat.card (Subgroup.center ↥K) := fun hz => by
    have h := CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGA hp (by norm_num)
      hK.2.2 d e hpd hz
    rw [hd] at h
    simp [CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex] at h
  have hcen1 : Nat.card (cen B K) = 1 := by
    show Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) = 1
    rw [hC, Subgroup.card_bot]
  have hstab3 : Nat.card (stab B K) ≤ 5 ^ 3 := by
    have h1 := card_stab_le hB K
    rw [hcen1, mul_one] at h1
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) (pRank_five_mulAut_le_three_of_ree32 hK.2.2 d hd e))
  rw [hcen1, mul_one] at hsmall
  have hm4 : CFSG.Open.pRank 5 B = 4 := by
    have h := hsmall.trans_le hstab3
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 5)).1 h
    omega
  have hBcard : Nat.card B = 5 ^ CFSG.Open.pRank 5 B := GL83.PiGen.card_eq_pow_pRank hB
  obtain ⟨b, hbB, hbN⟩ : ∃ b ∈ B, b ∉ Subgroup.normalizer (K : Set X) := by
    by_contra hall
    push Not at hall
    have hst : stab B K = B := inf_eq_left.2 hall
    rw [hst, hBcard, hm4] at hstab3
    norm_num at hstab3
  have hb5 : b ^ 5 = 1 := hB.2 b hbB
  have hbb : b * b ∉ Subgroup.normalizer (K : Set X) := by
    intro h
    apply hbN
    have h3 : (b * b) ^ 3 = b := by
      rw [← pow_two, ← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_succ, hb5, one_mul]
    rw [← h3]
    exact Subgroup.pow_mem _ h 3
  have hK2 : 2 ≤ CFSG.Open.pRank 5 K := by
    obtain ⟨E, hE, hEc⟩ := CFSG.HardMathSupport.Dickson.Bal207.bal207RankSyl_holds 5 d
      (by rw [hd]; simp [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Index])
      (by
        rintro ⟨-, h⟩
        rw [hd] at h
        simp [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux.IsSuzuki2Index] at h)
    exact InputsSeitz.le_pRank_of_quot hp hZ (CFSG.SectionRank.isElemAbelian_map hE e.symm.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective e.symm.injective, hEc])
  have h3 := three_mul_pRank_le_of_not_mem hp hK hZ hbN hbb
  omega

end Ree32

@[expose] def Input23_19ExcThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → GLAPPrimeCore 3 X = ⊥ →
    ∀ B : Subgroup X, IsElemAbelian 3 B → 4 ≤ CFSG.Open.pRank 3 B →
      CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) →
      3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ExcIndex 3 d.1 → d.1 ≠ .tits → ¬ IsL2EightIndex d.1 →
        (IsSixIndex d.1 → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        ((Subgroup.center ↥K ≠ ⊥ ∧ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1) ∨
          B ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∨ IsD2SeitzException 3 d.1) →
        K ≤ GLBCore 3 2 B

theorem input23_19ExcThree_of_res (h : InputsSeitz5.Input23_19ExcRes) : Input23_19ExcThree := by
  intro X _ _ hKX hcore B hB hB4 hrk K hK haut hsmall d hd hexc htits hl28 hsix hrest
  refine h X hKX 3 Nat.prime_three (by norm_num) hcore B hB hB4 hrk K hK haut hsmall d hd hexc htits
    (fun hs => ?_) hl28 hsix ?_
  · rw [hs] at hexc
    have := InputsSeitz5.eq_five_of_excIndex_suzuki hexc
    omega
  · rcases hrest with ⟨hZ, -⟩ | hC | hD
    · exact Or.inl hZ
    · exact Or.inr (Or.inl hC)
    · exact Or.inr (Or.inr hD)

theorem dvd_card_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p ↥P) (h1 : P ≠ ⊥) : p ∣ Nat.card P := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact absurd (Subgroup.eq_bot_of_card_eq _ hk) h1
  · rw [hk]
    exact dvd_pow_self p (Nat.succ_ne_zero k)

section Assemble2319


theorem input23_19ExcRes_of_three (hGA : GriessMultipliersAllModels) (h : Input23_19ExcThree) :
    InputsSeitz5.Input23_19ExcRes := by
  intro X _ _ hKX p hp hp2 hcore B hB hB4 hrk K hK haut hsmall d hd hexc htits hsz hl28 hsix hrest
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hd
  have hd2 : d.1.characteristic = 2 := InputsSeitz5.characteristic_eq_two_of_excIndex hexc
  have hpd : p ≠ d.1.characteristic := by rw [hd2]; exact hp2
  have hZp : IsPGroup p ↥(Subgroup.center ↥K) := Inputs245b.isPGroup_center_of_component hp hcore hK
  by_cases hp3 : p = 3
  · subst hp3
    refine h X hKX hcore B hB hB4 hrk K hK haut hsmall d ⟨e⟩ hexc htits hl28 hsix ?_
    rcases hrest with hZ | hC | hD
    · exact Or.inl ⟨hZ, CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGA hp hp2
        hK.2.2 d e hpd (dvd_card_of_isPGroup hZp hZ)⟩
    · exact Or.inr (Or.inl hC)
    · exact Or.inr (Or.inr hD)
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := fun h4 => by subst h4; exact absurd hp (by decide)
      omega
    obtain ⟨rfl, hd1⟩ := InputsSeitz3.excIndex_ge_five hp5 hexc
    have hdR : d.1 = .reeF4 2 := by
      rcases hd1 with h1 | h1 | h1
      · exact absurd h1 htits
      · exact absurd h1 hsz
      · exact h1
    exfalso
    rcases hrest with hZ | hC | hD
    · have h1 := CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGA hp hp2 hK.2.2 d e
        hpd (dvd_card_of_isPGroup hZp hZ)
      rw [hdR] at h1
      simp [CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex] at h1
    · exact false_of_ree32_faithful hGA hcore hB hB4 hrk hK hsmall d e hdR hC
    · rw [hdR] at hD
      simp [IsD2SeitzException] at hD

end Assemble2319

end Narrow2319

section AltRank

open Equiv Equiv.Perm MulAction

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem le_glbCore_of_alt_of_rank (hp : p.Prime) (hp2 : p ≠ 2)
    {B K : Subgroup X} (hB : IsElemAbelian p B) (hB4 : 4 ≤ CFSG.Open.pRank p B)
    (hK : IsComponentOf K ⊤) {n : ℕ} (hn6 : n ≠ 6) (hA : IsAltType n (↥K ⧸ Subgroup.center ↥K))
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hnc : n / p + CFSG.Open.pRank p (cen B K) ≤ CFSG.Open.pRank p B) :
    K ≤ GLBCore p 2 B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set m := CFSG.Open.pRank p B with hm
  have hBcard : Nat.card B = p ^ m := GL83.PiGen.card_eq_pow_pRank hB
  by_cases hsmall : Nat.card (stab B K) ≤ p ^ (m - 2) * Nat.card (cen B K)
  · refine InputsSeitz.le_glbCore_of_card_stab_le hp hB hK 2 (m - 2) (by omega) ?_ hsmall
    rw [hBcard]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  push Not at hsmall
  obtain ⟨e⟩ := hA
  have hq : CFSG.Open.IsQuasisimple K := hK.2.2
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  have hn5 : 5 ≤ n := SchurFacts.five_le_of_isAltType hq ⟨e⟩
  set π := GL83.PiGen.permHom (GL83.PiGen.stab_le_normalizer B K) hn5 hn6 e with hπ
  have hAC : Nat.card (stab B K) = Nat.card (cen B K) * Nat.card π.range :=
    GL83.PiGen.card_stab_eq_mul hn5 hn6 e
  have hAel : IsElemAbelian p (stab B K) := elem_mono hB inf_le_left
  have hRel : IsElemAbelian p π.range := GL83.PiGen.isElemAbelian_range hAel π
  obtain ⟨j, hj⟩ := GL83.CompFam.exists_card_eq_pow hRel
  have hjm : m - 1 ≤ j := by
    have h1 : p ^ (m - 2) * Nat.card (cen B K) < p ^ j * Nat.card (cen B K) := by
      calc p ^ (m - 2) * Nat.card (cen B K) < Nat.card (stab B K) := hsmall
        _ = p ^ j * Nat.card (cen B K) := by rw [hAC, hj, mul_comm]
    have h2 : p ^ (m - 2) < p ^ j := lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 h2
    omega
  have hn7 : n ≠ 7 := by
    rintro rfl
    have hdvd : Nat.card π.range ∣ Nat.card (Perm (Fin 7)) := Subgroup.card_subgroup_dvd_card _
    rw [hj, Nat.card_perm, Nat.card_fin] at hdvd
    have h7 : Nat.factorial 7 = 5040 := by decide
    rw [h7] at hdvd
    exact InputsSeitz.not_pow_three_dvd_10080 hp hp2
      (((pow_dvd_pow p (by omega)).trans hdvd).trans (by norm_num))
  have hZ2 : Nat.card (Subgroup.center K) ∣ 2 := by
    have h := SchurFacts.card_center_dvd_of_isAltType hq ⟨e⟩
    rwa [if_neg (by omega)] at h
  have hstab : stab B K = B := inf_eq_left.2 hBN
  have hAcard : Nat.card (stab B K) = p ^ m := by rw [hstab, hBcard]
  have hker : Nat.card π.ker = Nat.card (cen B K) := by
    have h1 := Subgroup.card_ker_mul_card_range π
    rw [hAC] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hCel : IsElemAbelian p (cen B K) := elem_mono hB inf_le_left
  obtain ⟨c, hc⟩ := GL83.CompFam.exists_card_eq_pow hCel
  have hjc : j + c = m := by
    have h1 : p ^ m = p ^ (c + j) := by rw [← hAcard, hAC, hc, hj, pow_add]
    have := Nat.pow_right_injective hp.two_le h1
    omega
  have hcr : CFSG.Open.pRank p (cen B K) = c := by
    have h1 := GL83.PiGen.card_eq_pow_pRank hCel
    rw [hc] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  have hnj : n / p ≤ j := by omega
  have hRcomm : ∀ x ∈ π.range, ∀ y ∈ π.range, x * y = y * x := fun x hx y hy =>
    elem_comm hRel hx hy
  have horb : ∀ ω : Fin n, Nat.card (orbit π.range ω) ≤ p :=
    Claims138.card_orbit_le_of_rank hp hp3 hRel hj hnj
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : Fin n, ω₀ ∉ GL83.PiGen.fixSet π.range := by
    by_contra h
    push Not at h
    have hbot : π.range = ⊥ :=
      CFSG.AGLEmbedding.eq_bot_of_forall_apply_eq fun g hg a => (h a) g hg
    have h1 : Nat.card π.range = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hj] at h1
    rcases Nat.pow_eq_one.1 h1 with h | h
    · exact hp.one_lt.ne' h
    · omega
  have horb3 : ∀ ω : Fin n, ω ∉ GL83.PiGen.fixSet π.range → 3 ≤ (orbit π.range ω).ncard := by
    intro ω hω
    obtain ⟨s, hs⟩ := (CFSG.Open.IsElemAbelian.isPGroup hRel).card_orbit ω
    have hle := horb ω
    rw [GL83.PiGen.mem_fixSet] at hω
    push Not at hω
    obtain ⟨g, hg, hgω⟩ := hω
    have h2 : 2 ≤ (orbit π.range ω).ncard := by
      have hsub : ({ω, g ω} : Set (Fin n)) ⊆ orbit π.range ω := by
        intro x hx
        rcases hx with rfl | hx
        · exact mem_orbit_self x
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact mem_orbit ω (⟨g, hg⟩ : π.range)
      have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_pair (Ne.symm hgω)] at h3
    rw [← Nat.card_coe_set_eq] at h2 ⊢
    rw [hs] at h2 hle ⊢
    rcases s with _ | _ | s
    · simp at h2
    · simpa using hp3
    · exfalso
      have h5 : p ^ 2 ≤ p ^ (s + 1 + 1) := Nat.pow_le_pow_right hp.pos (by omega)
      have h6 : p < p ^ 2 := by nlinarith
      omega
  have hZΓ : ∀ z : ↥K, z ∈ Subgroup.center ↥K → (z : X) ∈ GLBCore p 2 B := by
    intro z hz
    have hzc : (z : X) ∈ Subgroup.centralizer (B : Set X) :=
      Subgroup.mem_centralizer_iff.2 fun b hb => InputsSeitz.comm_of_center_card_dvd_two hZ2 (hBN hb) hz
    have hN : Subgroup.normalizer (B : Set X) ≤ GLBCore p 2 B := le_sSup ⟨B, le_rfl, by omega, rfl⟩
    exact hN (Subgroup.centralizer_le_normalizer _ hzc)
  set φ : ↥K →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))) with hφ
  have hAlt : alternatingGroup (Fin n) ≤ ((GLBCore p 2 B).subgroupOf K).map φ := by
    refine Claims138.alternatingGroup_le_of_pairs hRcomm horb3 hω₀ fun ω ω' _ => ?_
    set V := Claims138.pairStab π.range ω ω' with hV
    have hVR : V ≤ π.range := Claims138.pairStab_le π.range ω ω'
    set W : Subgroup ↥(stab B K) := V.comap π with hW
    have hWcard : Nat.card W = Nat.card (cen B K) * Nat.card V := by
      have h1 := Subgroup.card_ker_mul_card_range (π.comp W.subtype)
      have hrange : (π.comp W.subtype).range = V := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype, hW, Subgroup.map_comap_eq_self hVR]
      have hle : π.ker ≤ W := fun x hx => by
        show π x ∈ V
        rw [MonoidHom.mem_ker.1 hx]
        exact one_mem V
      have hkerW : (π.comp W.subtype).ker = π.ker.subgroupOf W := by
        ext x
        simp [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      rw [hrange, hkerW, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hker] at h1
      exact h1.symm
    have hRV : Nat.card π.range ≤ p ^ 2 * Nat.card V := Claims138.card_le_pairStab hRcomm horb ω ω'
    set W' : Subgroup X := W.map (stab B K).subtype with hW'
    have hW'B : W' ≤ B := (Subgroup.map_subtype_le W).trans inf_le_left
    have hW'card : Nat.card W' = Nat.card W :=
      Subgroup.card_map_of_injective (stab B K).subtype_injective
    have hW'el : IsElemAbelian p W' := elem_mono hB hW'B
    have hW'rk : 2 ≤ CFSG.Open.pRank p W' := by
      obtain ⟨w, hw⟩ := GL83.CompFam.exists_card_eq_pow hW'el
      have h1 : p ^ m ≤ p ^ (2 + w) := by
        calc p ^ m = Nat.card (stab B K) := hAcard.symm
          _ = Nat.card (cen B K) * Nat.card π.range := hAC
          _ ≤ Nat.card (cen B K) * (p ^ 2 * Nat.card V) := Nat.mul_le_mul_left _ hRV
          _ = p ^ 2 * (Nat.card (cen B K) * Nat.card V) := by ring
          _ = p ^ (2 + w) := by rw [← hWcard, ← hW'card, hw, pow_add]
      have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
      have h3 := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hW'el hw
      omega
    intro σ hσ
    have hσA : σ ∈ alternatingGroup (Fin n) := (GL83.mem_altOn.1 hσ).1
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσA⟩)
    have hek : (e (QuotientGroup.mk k) : Perm (Fin n)) = σ := by
      rw [hk]
      simp
    refine ⟨k, ?_, ?_⟩
    · show (k : X) ∈ GLBCore p 2 B
      have hkC : (k : X) ∈ Subgroup.centralizer (W' : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨w, hw, rfl⟩
        obtain ⟨y, hy, hspec⟩ :=
          GL83.PiGen.permHom_spec (GL83.PiGen.stab_le_normalizer B K) hn5 hn6 e w k
        have hspec' : π w * (e (QuotientGroup.mk k) : Perm (Fin n)) * (π w)⁻¹ =
            (e (QuotientGroup.mk y) : Perm (Fin n)) := hspec
        have hπw : π w ∈ V := hw
        have hdisj : Perm.Disjoint (π w) σ := by
          intro x
          by_cases hx : x ∈ GL83.PiGen.fixSet V
          · exact Or.inl (hx (π w) hπw)
          · exact Or.inr ((GL83.mem_altOn.1 hσ).2 x hx)
        have hcomm : π w * σ = σ * π w := hdisj.commute.eq
        have hey : (e (QuotientGroup.mk y) : Perm (Fin n)) = σ := by
          rw [← hspec', hek, hcomm, mul_inv_cancel_right]
        have hmk : (QuotientGroup.mk y : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk k :=
          e.injective (Subtype.ext (hey.trans hek.symm))
        have hz : k⁻¹ * y ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hmk.symm
        have hwB : ((w : ↥(stab B K)) : X) ∈ B := (Subgroup.mem_inf.1 w.2).1
        have hwN : ((w : ↥(stab B K)) : X) ∈ Subgroup.normalizer (K : Set X) :=
          (Subgroup.mem_inf.1 w.2).2
        have hwkz : ((w : ↥(stab B K)) : X) * (k : X) * ((w : ↥(stab B K)) : X)⁻¹ =
            (k : X) * ((k⁻¹ * y : ↥K) : X) := by
          rw [← hy]
          simp
        have hwz : ((w : ↥(stab B K)) : X) * ((k⁻¹ * y : ↥K) : X) =
            ((k⁻¹ * y : ↥K) : X) * ((w : ↥(stab B K)) : X) :=
          InputsSeitz.comm_of_center_card_dvd_two hZ2 hwN hz
        have hz2 : ((k⁻¹ * y : ↥K) : X) ^ 2 = 1 := by
          have hd : orderOf (k⁻¹ * y) ∣ 2 :=
            (Subgroup.orderOf_dvd_natCard (Subgroup.center ↥K) hz).trans hZ2
          have h1 := orderOf_dvd_iff_pow_eq_one.1 hd
          have h2 := congrArg (Subtype.val : ↥K → X) h1
          simpa using h2
        have hz1 := InputsSeitz.eq_one_of_conj_eq_mul hp hp2 (hB.2 _ hwB) hwkz hwz hz2
        rw [hz1, mul_one] at hwkz
        show ((w : ↥(stab B K)) : X) * (k : X) = (k : X) * ((w : ↥(stab B K)) : X)
        calc ((w : ↥(stab B K)) : X) * (k : X) =
            ((w : ↥(stab B K)) : X) * k * ((w : ↥(stab B K)) : X)⁻¹ * w := by group
          _ = k * w := by rw [hwkz]
      have hN : Subgroup.normalizer (W' : Set X) ≤ GLBCore p 2 B := le_sSup ⟨W', hW'B, hW'rk, rfl⟩
      exact hN (Subgroup.centralizer_le_normalizer _ hkC)
    · exact hek
  intro x hx
  have hφx : φ ⟨x, hx⟩ ∈ alternatingGroup (Fin n) := (e (QuotientGroup.mk ⟨x, hx⟩)).2
  obtain ⟨y, hyΓ, hyx⟩ := hAlt hφx
  have hyx' : (e (QuotientGroup.mk y) : Perm (Fin n)) = e (QuotientGroup.mk ⟨x, hx⟩) := hyx
  have hmk : (QuotientGroup.mk y : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk ⟨x, hx⟩ :=
    e.injective (Subtype.ext hyx')
  have hz := QuotientGroup.eq.1 hmk
  have hx' : x = (y : X) * ((y⁻¹ * ⟨x, hx⟩ : ↥K) : X) := by simp
  rw [hx']
  exact (GLBCore p 2 B).mul_mem hyΓ (hZΓ _ hz)

theorem lift_mem_glbCore (hp : p.Prime) (hp2 : p ≠ 2) {B K : Subgroup X} (hB : IsElemAbelian p B)
    (hK : IsComponentOf K ⊤) {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n))
    (hZ2 : Nat.card (Subgroup.center K) ∣ 2)
    {V : Subgroup (Perm (Fin n))}
    (hVR : V ≤ (GL83.PiGen.permHom (GL83.PiGen.stab_le_normalizer B K) hn5 hn6 e).range)
    (hVc : p ^ 2 ≤ Nat.card (cen B K) * Nat.card V) {σ : Perm (Fin n)}
    (hσV : ∀ v ∈ V, v * σ = σ * v) (k : ↥K)
    (hek : (e (QuotientGroup.mk k) : Perm (Fin n)) = σ) : (k : X) ∈ GLBCore p 2 B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple K := hK.2.2
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  set π := GL83.PiGen.permHom (GL83.PiGen.stab_le_normalizer B K) hn5 hn6 e with hπ
  have hAC : Nat.card (stab B K) = Nat.card (cen B K) * Nat.card π.range :=
    GL83.PiGen.card_stab_eq_mul hn5 hn6 e
  have hker : Nat.card π.ker = Nat.card (cen B K) := by
    have h1 := Subgroup.card_ker_mul_card_range π
    rw [hAC] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  set W : Subgroup ↥(stab B K) := V.comap π with hW
  have hWcard : Nat.card W = Nat.card (cen B K) * Nat.card V := by
    have h1 := Subgroup.card_ker_mul_card_range (π.comp W.subtype)
    have hrange : (π.comp W.subtype).range = V := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hW, Subgroup.map_comap_eq_self hVR]
    have hle : π.ker ≤ W := fun x hx => by
      show π x ∈ V
      rw [MonoidHom.mem_ker.1 hx]
      exact one_mem V
    have hkerW : (π.comp W.subtype).ker = π.ker.subgroupOf W := by
      ext x
      simp [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rw [hrange, hkerW, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hker] at h1
    exact h1.symm
  set W' : Subgroup X := W.map (stab B K).subtype with hW'
  have hW'B : W' ≤ B := (Subgroup.map_subtype_le W).trans inf_le_left
  have hW'card : Nat.card W' = Nat.card W :=
    Subgroup.card_map_of_injective (stab B K).subtype_injective
  have hW'el : IsElemAbelian p W' := elem_mono hB hW'B
  have hW'rk : 2 ≤ CFSG.Open.pRank p W' := by
    obtain ⟨w, hw⟩ := GL83.CompFam.exists_card_eq_pow hW'el
    have h1 : p ^ 2 ≤ p ^ w := by
      rw [← hw, hW'card, hWcard]
      exact hVc
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    have h3 := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hW'el hw
    omega
  have hkC : (k : X) ∈ Subgroup.centralizer (W' : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨y, hy, hspec⟩ :=
      GL83.PiGen.permHom_spec (GL83.PiGen.stab_le_normalizer B K) hn5 hn6 e w k
    have hspec' : π w * (e (QuotientGroup.mk k) : Perm (Fin n)) * (π w)⁻¹ =
        (e (QuotientGroup.mk y) : Perm (Fin n)) := hspec
    have hπw : π w ∈ V := hw
    have hcomm : π w * σ = σ * π w := hσV _ hπw
    have hey : (e (QuotientGroup.mk y) : Perm (Fin n)) = σ := by
      rw [← hspec', hek, hcomm, mul_inv_cancel_right]
    have hmk : (QuotientGroup.mk y : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk k :=
      e.injective (Subtype.ext (hey.trans hek.symm))
    have hz : k⁻¹ * y ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hmk.symm
    have hwB : ((w : ↥(stab B K)) : X) ∈ B := (Subgroup.mem_inf.1 w.2).1
    have hwN : ((w : ↥(stab B K)) : X) ∈ Subgroup.normalizer (K : Set X) :=
      (Subgroup.mem_inf.1 w.2).2
    have hwkz : ((w : ↥(stab B K)) : X) * (k : X) * ((w : ↥(stab B K)) : X)⁻¹ =
        (k : X) * ((k⁻¹ * y : ↥K) : X) := by
      rw [← hy]
      simp
    have hwz : ((w : ↥(stab B K)) : X) * ((k⁻¹ * y : ↥K) : X) =
        ((k⁻¹ * y : ↥K) : X) * ((w : ↥(stab B K)) : X) :=
      InputsSeitz.comm_of_center_card_dvd_two hZ2 hwN hz
    have hz2 : ((k⁻¹ * y : ↥K) : X) ^ 2 = 1 := by
      have hd : orderOf (k⁻¹ * y) ∣ 2 :=
        (Subgroup.orderOf_dvd_natCard (Subgroup.center ↥K) hz).trans hZ2
      have h1 := orderOf_dvd_iff_pow_eq_one.1 hd
      have h2 := congrArg (Subtype.val : ↥K → X) h1
      simpa using h2
    have hz1 := InputsSeitz.eq_one_of_conj_eq_mul hp hp2 (hB.2 _ hwB) hwkz hwz hz2
    rw [hz1, mul_one] at hwkz
    show ((w : ↥(stab B K)) : X) * (k : X) = (k : X) * ((w : ↥(stab B K)) : X)
    calc ((w : ↥(stab B K)) : X) * (k : X) =
        ((w : ↥(stab B K)) : X) * k * ((w : ↥(stab B K)) : X)⁻¹ * w := by group
      _ = k * w := by rw [hwkz]
  have hN : Subgroup.normalizer (W' : Set X) ≤ GLBCore p 2 B := le_sSup ⟨W', hW'B, hW'rk, rfl⟩
  exact hN (Subgroup.centralizer_le_normalizer _ hkC)

theorem mem_map_of_commute (hp : p.Prime) (hp2 : p ≠ 2) {B K : Subgroup X} (hB : IsElemAbelian p B)
    (hK : IsComponentOf K ⊤) {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n))
    (hZ2 : Nat.card (Subgroup.center K) ∣ 2)
    {V : Subgroup (Perm (Fin n))}
    (hVR : V ≤ (GL83.PiGen.permHom (GL83.PiGen.stab_le_normalizer B K) hn5 hn6 e).range)
    (hVc : p ^ 2 ≤ Nat.card (cen B K) * Nat.card V) {σ : Perm (Fin n)}
    (hσA : σ ∈ alternatingGroup (Fin n)) (hσV : ∀ v ∈ V, v * σ = σ * v) :
    σ ∈ ((GLBCore p 2 B).subgroupOf K).map ((alternatingGroup (Fin n)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)))) := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσA⟩)
  have hek : (e (QuotientGroup.mk k) : Perm (Fin n)) = σ := by
    rw [hk]
    simp
  exact ⟨k, lift_mem_glbCore hp hp2 hB hK hn5 hn6 e hZ2 hVR hVc hσV k hek, hek⟩

theorem le_glbCore_of_alt_le {B K : Subgroup X} (hB2 : 2 ≤ CFSG.Open.pRank p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) {n : ℕ}
    (e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n))
    (hZ2 : Nat.card (Subgroup.center K) ∣ 2)
    (hAlt : alternatingGroup (Fin n) ≤ ((GLBCore p 2 B).subgroupOf K).map
      ((alternatingGroup (Fin n)).subtype.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))))) :
    K ≤ GLBCore p 2 B := by
  have hZΓ : ∀ z : ↥K, z ∈ Subgroup.center ↥K → (z : X) ∈ GLBCore p 2 B := by
    intro z hz
    have hzc : (z : X) ∈ Subgroup.centralizer (B : Set X) :=
      Subgroup.mem_centralizer_iff.2 fun b hb => InputsSeitz.comm_of_center_card_dvd_two hZ2 (hBN hb) hz
    have hN : Subgroup.normalizer (B : Set X) ≤ GLBCore p 2 B := le_sSup ⟨B, le_rfl, hB2, rfl⟩
    exact hN (Subgroup.centralizer_le_normalizer _ hzc)
  intro x hx
  have hφx : ((alternatingGroup (Fin n)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)))) ⟨x, hx⟩ ∈ alternatingGroup (Fin n) :=
    (e (QuotientGroup.mk ⟨x, hx⟩)).2
  obtain ⟨y, hyΓ, hyx⟩ := hAlt hφx
  have hyx' : (e (QuotientGroup.mk y) : Perm (Fin n)) = e (QuotientGroup.mk ⟨x, hx⟩) := hyx
  have hmk : (QuotientGroup.mk y : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk ⟨x, hx⟩ :=
    e.injective (Subtype.ext hyx')
  have hz := QuotientGroup.eq.1 hmk
  have hx' : x = (y : X) * ((y⁻¹ * ⟨x, hx⟩ : ↥K) : X) := by simp
  rw [hx']
  exact (GLBCore p 2 B).mul_mem hyΓ (hZΓ _ hz)

theorem le_glbCore_of_alt_pairs (hp : p.Prime) (hp2 : p ≠ 2) {B K : Subgroup X}
    (hB : IsElemAbelian p B) (hB2 : 2 ≤ CFSG.Open.pRank p B) (hK : IsComponentOf K ⊤) {n : ℕ}
    (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n))
    (hZ2 : Nat.card (Subgroup.center K) ∣ 2) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hR1 : (GL83.PiGen.permHom (GL83.PiGen.stab_le_normalizer B K) hn5 hn6 e).range ≠ ⊥)
    (hpair : ∀ ω ω' : Fin n, p ^ 2 ≤ Nat.card (cen B K) * Nat.card (Claims138.pairStab
      (GL83.PiGen.permHom (GL83.PiGen.stab_le_normalizer B K) hn5 hn6 e).range ω ω')) :
    K ≤ GLBCore p 2 B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set π := GL83.PiGen.permHom (GL83.PiGen.stab_le_normalizer B K) hn5 hn6 e with hπ
  have hAel : IsElemAbelian p (stab B K) := elem_mono hB inf_le_left
  have hRel : IsElemAbelian p π.range := GL83.PiGen.isElemAbelian_range hAel π
  have hRcomm : ∀ x ∈ π.range, ∀ y ∈ π.range, x * y = y * x := fun x hx y hy =>
    elem_comm hRel hx hy
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : Fin n, ω₀ ∉ GL83.PiGen.fixSet π.range := by
    by_contra h
    push Not at h
    exact hR1 (CFSG.AGLEmbedding.eq_bot_of_forall_apply_eq fun g hg a => (h a) g hg)
  have horb3 : ∀ ω : Fin n, ω ∉ GL83.PiGen.fixSet π.range → 3 ≤ (orbit π.range ω).ncard := by
    intro ω hω
    obtain ⟨s, hs⟩ := (CFSG.Open.IsElemAbelian.isPGroup hRel).card_orbit ω
    rw [GL83.PiGen.mem_fixSet] at hω
    push Not at hω
    obtain ⟨g, hg, hgω⟩ := hω
    have h2 : 2 ≤ (orbit π.range ω).ncard := by
      have hsub : ({ω, g ω} : Set (Fin n)) ⊆ orbit π.range ω := by
        intro x hx
        rcases hx with rfl | hx
        · exact mem_orbit_self x
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact mem_orbit ω (⟨g, hg⟩ : π.range)
      have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_pair (Ne.symm hgω)] at h3
    rw [← Nat.card_coe_set_eq] at h2 ⊢
    rw [hs] at h2 ⊢
    rcases s with _ | s
    · simp at h2
    · calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (s + 1) := Nat.pow_le_pow_right hp.pos (by omega)
  refine le_glbCore_of_alt_le hB2 hBN e hZ2 ?_
  refine Claims138.alternatingGroup_le_of_pairs hRcomm horb3 hω₀ fun ω ω' _ => ?_
  intro σ hσ
  refine mem_map_of_commute hp hp2 hB hK hn5 hn6 e hZ2 (Claims138.pairStab_le π.range ω ω') (hpair ω ω')
    (GL83.mem_altOn.1 hσ).1 fun v hv => ?_
  have hdisj : Perm.Disjoint v σ := by
    intro x
    by_cases hx : x ∈ GL83.PiGen.fixSet (Claims138.pairStab π.range ω ω')
    · exact Or.inl (hx v hv)
    · exact Or.inr ((GL83.mem_altOn.1 hσ).2 x hx)
  exact hdisj.commute.eq

section Orbits

variable {n : ℕ}

theorem stabIn_eq_of_mem_orbit {R : Subgroup (Perm (Fin n))}
    (hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) {ω ω' : Fin n} (h : ω' ∈ orbit R ω) :
    GL83.PiGen.stabIn R ω' = GL83.PiGen.stabIn R ω := by
  have key : ∀ {a b : Fin n}, b ∈ orbit R a → GL83.PiGen.stabIn R a ≤ GL83.PiGen.stabIn R b := by
    intro a b hb v hv
    obtain ⟨g, rfl⟩ := hb
    obtain ⟨w, hw, rfl⟩ := hv
    have hw' : (w : Perm (Fin n)) a = a := MulAction.mem_stabilizer_iff.1 hw
    refine ⟨w, MulAction.mem_stabilizer_iff.2 ?_, rfl⟩
    show (w : Perm (Fin n)) ((g : Perm (Fin n)) a) = (g : Perm (Fin n)) a
    exact CFSG.AGLEmbedding.apply_apply_eq_of_commute hRcomm w.2 g.2 hw'
  exact le_antisymm (key (mem_orbit_symm.1 h)) (key h)

theorem card_le_mul_pairStab {R : Subgroup (Perm (Fin n))}
    (hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (ω ω' : Fin n) :
    Nat.card R ≤ Nat.card (orbit R ω) * Nat.card (orbit R ω') *
      Nat.card (Claims138.pairStab R ω ω') := by
  have h1 := GL83.PiGen.card_mul_card_stabIn R ω
  have h2 := GL83.PiGen.card_mul_card_stabIn R ω'
  have hN : GL83.PiGen.stabIn R ω ≤
      Subgroup.normalizer (GL83.PiGen.stabIn R ω' : Set (Perm (Fin n))) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hRcomm y (GL83.PiGen.stabIn_le R _ hy) x (GL83.PiGen.stabIn_le R _ hx)
  have h3 := Claims138.card_sup_mul_card_inf hN
  have h4 : Nat.card ↥(GL83.PiGen.stabIn R ω ⊔ GL83.PiGen.stabIn R ω') ≤ Nat.card R :=
    Subgroup.card_le_of_le (sup_le (GL83.PiGen.stabIn_le R _) (GL83.PiGen.stabIn_le R _))
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have key : Nat.card R * Nat.card R ≤ (Nat.card (orbit R ω) * Nat.card (orbit R ω') *
      Nat.card (Claims138.pairStab R ω ω')) * Nat.card R := by
    calc Nat.card R * Nat.card R
        = (Nat.card (orbit R ω) * Nat.card (GL83.PiGen.stabIn R ω)) *
          (Nat.card (orbit R ω') * Nat.card (GL83.PiGen.stabIn R ω')) := by rw [← h1, ← h2]
      _ = Nat.card (orbit R ω) * Nat.card (orbit R ω') *
          (Nat.card (GL83.PiGen.stabIn R ω) * Nat.card (GL83.PiGen.stabIn R ω')) := by ring
      _ = Nat.card (orbit R ω) * Nat.card (orbit R ω') *
          (Nat.card ↥(GL83.PiGen.stabIn R ω ⊔ GL83.PiGen.stabIn R ω') *
            Nat.card (Claims138.pairStab R ω ω')) := by rw [← h3]; rfl
      _ ≤ Nat.card (orbit R ω) * Nat.card (orbit R ω') *
          (Nat.card R * Nat.card (Claims138.pairStab R ω ω')) := by gcongr
      _ = (Nat.card (orbit R ω) * Nat.card (orbit R ω') *
          Nat.card (Claims138.pairStab R ω ω')) * Nat.card R := by ring
  exact Nat.le_of_mul_le_mul_right key hRpos

theorem three_mul_add_four_le_pow {a : ℕ} (ha : 3 ≤ a) : 3 * a + 4 ≤ 3 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

theorem three_mul_le_pow (a : ℕ) : 3 * a ≤ 3 ^ a := by
  rcases Nat.lt_or_ge a 3 with h | h
  · interval_cases a <;> norm_num
  · have := three_mul_add_four_le_pow h
    omega

theorem orbit_shape {t : ℕ} (hn : n = 3 * t) {R : Subgroup (Perm (Fin n))} (hR : IsElemAbelian 3 R)
    (hcard : 3 ^ (t - 1) ≤ Nat.card R) :
    (∀ ω : Fin n, Nat.card (orbit R ω) ≤ 9) ∧
    (∀ ω ω' : Fin n, Nat.card (orbit R ω) = 9 → Nat.card (orbit R ω') = 9 → ω' ∈ orbit R ω) ∧
    (∀ ω ω' : Fin n, Nat.card (orbit R ω) = 9 → 3 ≤ Nat.card (orbit R ω')) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRp : IsPGroup 3 R := CFSG.Open.IsElemAbelian.isPGroup hR
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy => elem_comm hR hx hy
  let Q := MulAction.orbitRel.Quotient R (Fin n)
  haveI : Fintype Q := Fintype.ofFinite Q
  have hmem : ∀ q : Q, (Quotient.out q : Fin n) ∈ q.orbit := fun q =>
    MulAction.orbitRel.Quotient.mem_orbit.2 (Quotient.out_eq' q)
  have hex : ∀ q : Q, ∃ s, Nat.card q.orbit = 3 ^ s := fun q => by
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
    exact hRp.card_orbit _
  choose a ha using hex
  have horb : ∀ ω : Fin n, Nat.card (orbit R ω) = 3 ^ a (Quotient.mk'' ω) := fun ω => by
    rw [← ha]
    rfl
  have hsum : ∑ q : Q, 3 ^ a q = n := by
    have h1 := Nat.card_congr (MulAction.selfEquivSigmaOrbits' R (Fin n))
    rw [Nat.card_sigma, Nat.card_fin] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun q _ => (ha q).symm
  let f : R → (q : Q) → q.orbit := fun r q =>
    ⟨r • (Quotient.out q : Fin n), MulAction.orbitRel.Quotient.mapsTo_smul_orbit r q (hmem q)⟩
  have hf : Function.Injective f := by
    intro r r' h
    have hq : ∀ q : Q, r • (Quotient.out q : Fin n) = r' • (Quotient.out q : Fin n) := fun q =>
      congrArg Subtype.val (congrFun h q)
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have hx : x ∈ MulAction.orbitRel.Quotient.orbit (Quotient.mk'' x : Q) :=
      MulAction.orbitRel.Quotient.mem_orbit.2 rfl
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'] at hx
    have hqx := hq (Quotient.mk'' x)
    obtain ⟨y, hy⟩ : ∃ y : Fin n, y = Quotient.out (Quotient.mk'' x : Q) := ⟨_, rfl⟩
    rw [← hy] at hx hqx
    obtain ⟨g, hg⟩ := hx
    have hrg : r * g = g * r := Subtype.ext (hRcomm _ r.2 _ g.2)
    have hr'g : r' * g = g * r' := Subtype.ext (hRcomm _ r'.2 _ g.2)
    have hg' : g • y = x := hg
    have e1 : r • x = g • (r • y) := by rw [← hg', smul_smul, smul_smul, hrg]
    have e2 : r' • x = g • (r' • y) := by rw [← hg', smul_smul, smul_smul, hr'g]
    have e3 : r • x = r' • x := by rw [e1, e2, hqx]
    exact e3
  have hprod : Nat.card R ≤ 3 ^ (∑ q : Q, a q) := by
    have h1 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_pi] at h1
    rw [← Finset.prod_pow_eq_pow_sum]
    exact h1.trans (le_of_eq (Finset.prod_congr rfl fun q _ => ha q))
  have hrank : t - 1 ≤ ∑ q : Q, a q :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 (hcard.trans hprod)
  set F : Q → ℕ := fun q => 3 ^ a q - 3 * a q with hF
  have hFsum : ∑ q : Q, F q + 3 * ∑ q : Q, a q = n := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← hsum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have := three_mul_le_pow (a q)
    simp only [hF]
    omega
  have hF3 : ∑ q : Q, F q ≤ 3 := by omega
  have hFq : ∀ q, F q ≤ 3 := fun q =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)).trans hF3
  have hF2 : ∀ q q', q ≠ q' → F q + F q' ≤ 3 := fun q q' hqq' => by
    have h1 : ∑ i ∈ ({q, q'} : Finset Q), F i ≤ ∑ q : Q, F q :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _
    rw [Finset.sum_pair hqq'] at h1
    omega
  have ha2 : ∀ q, a q ≤ 2 := fun q => by
    by_contra h
    push Not at h
    have h1 := three_mul_add_four_le_pow (show 3 ≤ a q by omega)
    have h2 := hFq q
    simp only [hF] at h2
    omega
  have hF_of : ∀ q, a q = 2 → F q = 3 := fun q h => by simp only [hF, h]; norm_num
  refine ⟨fun ω => ?_, fun ω ω' h1 h2 => ?_, fun ω ω' h1 => ?_⟩
  · rw [horb]
    calc 3 ^ a (Quotient.mk'' ω) ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (ha2 _)
      _ = 9 := by norm_num
  · rw [horb] at h1 h2
    have e1 : a (Quotient.mk'' ω) = 2 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ a (Quotient.mk'' ω) = 3 ^ 2 by rw [h1])
    have e2 : a (Quotient.mk'' ω') = 2 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ a (Quotient.mk'' ω') = 3 ^ 2 by rw [h2])
    by_contra hne
    have hq : (Quotient.mk'' ω : Q) ≠ Quotient.mk'' ω' := by
      intro h
      apply hne
      have := Quotient.exact' h.symm
      exact this
    have := hF2 _ _ hq
    rw [hF_of _ e1, hF_of _ e2] at this
    omega
  · rw [horb] at h1 ⊢
    have e1 : a (Quotient.mk'' ω) = 2 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ a (Quotient.mk'' ω) = 3 ^ 2 by rw [h1])
    by_contra hlt
    push Not at hlt
    have e2 : a (Quotient.mk'' ω') = 0 := by
      by_contra h0
      have : 3 ^ 1 ≤ 3 ^ a (Quotient.mk'' ω') := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hq : (Quotient.mk'' ω : Q) ≠ Quotient.mk'' ω' := by
      intro h
      rw [h, e2] at e1
      omega
    have := hF2 _ _ hq
    rw [hF_of _ e1] at this
    simp only [hF, e2] at this
    omega

end Orbits

section Cycles

variable {α : Type*} [DecidableEq α]

theorem pow_three_apply {x : Perm α} (hx3 : x ^ 3 = 1) (a : α) : x (x (x a)) = a := by
  have h := congrArg (fun f : Perm α => f a) hx3
  simpa [pow_succ, Perm.mul_apply] using h

theorem cyc_ne {x : Perm α} (hx3 : x ^ 3 = 1) {a : α} (ha : x a ≠ a) :
    a ≠ x a ∧ a ≠ x (x a) ∧ x a ≠ x (x a) := by
  have h3 := pow_three_apply hx3 a
  refine ⟨fun h => ha h.symm, fun h => ?_, fun h => ha (x.injective h).symm⟩
  apply ha
  have : x a = x (x (x a)) := by rw [← h]
  rw [this, h3]

theorem cyc_disj {x : Perm α} (hx3 : x ^ 3 = 1) {a b : α} (h0 : b ≠ a) (h1 : b ≠ x a)
    (h2 : b ≠ x (x a)) :
    x b ≠ a ∧ x b ≠ x a ∧ x b ≠ x (x a) ∧ x (x b) ≠ a ∧ x (x b) ≠ x a ∧ x (x b) ≠ x (x a) := by
  have ha3 := pow_three_apply hx3 a
  have hb3 := pow_three_apply hx3 b
  refine ⟨fun h => h2 ?_, fun h => h0 (x.injective h), fun h => h1 (x.injective h), fun h => h1 ?_,
    fun h => h2 ?_, fun h => h0 (x.injective (x.injective h))⟩
  · rw [← h, hb3]
  · rw [← hb3, h]
  · rw [← hb3, x.injective h]

def cycSwap (x : Perm α) (a b : α) : Perm α :=
  swap a b * swap (x a) (x b) * swap (x (x a)) (x (x b))

structure TwoCyc (x : Perm α) (a b : α) : Prop where
  ab : a ≠ b
  axb : a ≠ x b
  axxb : a ≠ x (x b)
  xab : x a ≠ b
  xaxb : x a ≠ x b
  xaxxb : x a ≠ x (x b)
  xxab : x (x a) ≠ b
  xxaxb : x (x a) ≠ x b
  xxaxxb : x (x a) ≠ x (x b)
  a1 : a ≠ x a
  a2 : a ≠ x (x a)
  a3 : x a ≠ x (x a)
  b1 : b ≠ x b
  b2 : b ≠ x (x b)
  b3 : x b ≠ x (x b)

theorem TwoCyc.mk' {x : Perm α} (hx3 : x ^ 3 = 1) {a b : α} (ha : x a ≠ a) (hb : x b ≠ b)
    (h0 : b ≠ a) (h1 : b ≠ x a) (h2 : b ≠ x (x a)) : TwoCyc x a b := by
  obtain ⟨a1, a2, a3⟩ := cyc_ne hx3 ha
  obtain ⟨b1, b2, b3⟩ := cyc_ne hx3 hb
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := cyc_disj hx3 h0 h1 h2
  exact ⟨Ne.symm h0, Ne.symm d1, Ne.symm d4, Ne.symm h1, Ne.symm d2, Ne.symm d5, Ne.symm h2,
    Ne.symm d3, Ne.symm d6, a1, a2, a3, b1, b2, b3⟩

theorem cycSwap_apply_of_ne {x : Perm α} {a b y : α} (h1 : y ≠ a) (h2 : y ≠ b) (h3 : y ≠ x a)
    (h4 : y ≠ x b) (h5 : y ≠ x (x a)) (h6 : y ≠ x (x b)) : cycSwap x a b y = y := by
  simp only [cycSwap, Perm.mul_apply]
  rw [swap_apply_of_ne_of_ne h5 h6, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]

theorem cycSwap_apply_left {x : Perm α} {a b : α} (h : TwoCyc x a b) : cycSwap x a b a = b := by
  simp only [cycSwap, Perm.mul_apply]
  rw [swap_apply_of_ne_of_ne h.a2 h.axxb, swap_apply_of_ne_of_ne h.a1 h.axb, swap_apply_left]

theorem cycSwap_apply_one {x : Perm α} {a b : α} (h : TwoCyc x a b) : cycSwap x a b (x a) = x b := by
  simp only [cycSwap, Perm.mul_apply]
  rw [swap_apply_of_ne_of_ne h.a3 h.xaxxb, swap_apply_left,
    swap_apply_of_ne_of_ne (Ne.symm h.axb) (Ne.symm h.b1)]

theorem cycSwap_apply_two {x : Perm α} {a b : α} (h : TwoCyc x a b) :
    cycSwap x a b (x (x a)) = x (x b) := by
  simp only [cycSwap, Perm.mul_apply]
  rw [swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm h.xaxxb) (Ne.symm h.b3),
    swap_apply_of_ne_of_ne (Ne.symm h.axxb) (Ne.symm h.b2)]

theorem cycSwap_apply_right {x : Perm α} {a b : α} (h : TwoCyc x a b) : cycSwap x a b b = a := by
  simp only [cycSwap, Perm.mul_apply]
  rw [swap_apply_of_ne_of_ne (Ne.symm h.xxab) h.b2, swap_apply_of_ne_of_ne (Ne.symm h.xab) h.b1,
    swap_apply_right]

theorem cycSwap_apply_right_one {x : Perm α} {a b : α} (h : TwoCyc x a b) :
    cycSwap x a b (x b) = x a := by
  simp only [cycSwap, Perm.mul_apply]
  rw [swap_apply_of_ne_of_ne (Ne.symm h.xxaxb) h.b3, swap_apply_right,
    swap_apply_of_ne_of_ne (Ne.symm h.a1) h.xab]

theorem cycSwap_apply_right_two {x : Perm α} {a b : α} (h : TwoCyc x a b) :
    cycSwap x a b (x (x b)) = x (x a) := by
  simp only [cycSwap, Perm.mul_apply]
  rw [swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm h.a3) h.xxaxb,
    swap_apply_of_ne_of_ne (Ne.symm h.a2) h.xxab]

theorem sign_cycSwap {x : Perm α} [Fintype α] {a b : α} (h : TwoCyc x a b) :
    Perm.sign (cycSwap x a b) = -1 := by
  simp only [cycSwap, Perm.sign_mul, Perm.sign_swap h.ab, Perm.sign_swap h.xaxb,
    Perm.sign_swap h.xxaxxb]
  decide

theorem cycSwap_commute {x : Perm α} (hx3 : x ^ 3 = 1) {a b : α} (h : TwoCyc x a b) :
    x * cycSwap x a b = cycSwap x a b * x := by
  have ha3 := pow_three_apply hx3 a
  have hb3 := pow_three_apply hx3 b
  have d1 : Commute (swap a b) (swap (x a) (x b)) :=
    (Perm.disjoint_swap_swap (by simp [h.ab, h.a1, h.axb, Ne.symm h.xab, h.b1, h.xaxb])).commute
  have d2 : Commute (swap a b) (swap (x (x a)) (x (x b))) :=
    (Perm.disjoint_swap_swap (by simp [h.ab, h.a2, h.axxb, Ne.symm h.xxab, h.b2, h.xxaxxb])).commute
  have key : x * cycSwap x a b * x⁻¹ = cycSwap x a b := by
    unfold cycSwap
    have e : x * (swap a b * swap (x a) (x b) * swap (x (x a)) (x (x b))) * x⁻¹ =
        (x * swap a b * x⁻¹) * (x * swap (x a) (x b) * x⁻¹) *
          (x * swap (x (x a)) (x (x b)) * x⁻¹) := by group
    rw [e, ← swap_apply_apply, ← swap_apply_apply, ← swap_apply_apply, ha3, hb3]
    rw [mul_assoc, ← d2.eq, ← mul_assoc, ← d1.eq, mul_assoc]
  calc x * cycSwap x a b = x * cycSwap x a b * x⁻¹ * x := by group
    _ = cycSwap x a b * x := by rw [key]

end Cycles

section AltPred

theorem mem_stabIn_iff {n : ℕ} {R : Subgroup (Perm (Fin n))} {x : Perm (Fin n)} (hx : x ∈ R)
    (ω : Fin n) : x ∈ GL83.PiGen.stabIn R ω ↔ x ω = ω := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact MulAction.mem_stabilizer_iff.1 hr
  · intro h
    exact ⟨⟨x, hx⟩, MulAction.mem_stabilizer_iff.2 h, rfl⟩

theorem mem_orbit_of_mem {n : ℕ} {R : Subgroup (Perm (Fin n))} {x : Perm (Fin n)} (hx : x ∈ R)
    {α y : Fin n} (hy : y ∈ orbit R α) : x y ∈ orbit R α := by
  rw [← MulAction.orbit_eq_iff.2 hy]
  exact MulAction.mem_orbit y (⟨x, hx⟩ : R)

theorem le_glbCore_of_alt_twelve {B K : Subgroup X} (hB : IsElemAbelian 3 B)
    (hB2 : 2 ≤ CFSG.Open.pRank 3 B) (hK : IsComponentOf K ⊤)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 12))
    (hZ2 : Nat.card (Subgroup.center K) ∣ 2) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hcen : 3 ≤ Nat.card (cen B K))
    (hR27 : Nat.card (GL83.PiGen.permHom (GL83.PiGen.stab_le_normalizer B K) (by norm_num)
      (by norm_num) e).range = 27) {α : Fin 12}
    (hα : Nat.card (orbit (GL83.PiGen.permHom (GL83.PiGen.stab_le_normalizer B K) (by norm_num)
      (by norm_num) e).range α) = 9) :
    K ≤ GLBCore 3 2 B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := GL83.PiGen.permHom (GL83.PiGen.stab_le_normalizer B K) (by norm_num : 5 ≤ 12)
    (by norm_num : (12 : ℕ) ≠ 6) e with hπ
  set R := π.range with hR
  have hAel : IsElemAbelian 3 (stab B K) := elem_mono hB inf_le_left
  have hRel : IsElemAbelian 3 R := GL83.PiGen.isElemAbelian_range hAel π
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy => elem_comm hRel hx hy
  obtain ⟨hle9, huniq, hnofix⟩ := orbit_shape (n := 12) (t := 4) rfl hRel (by rw [hR27]; norm_num)
  set O : Set (Fin 12) := orbit R α with hO
  have hαO : α ∈ O := MulAction.mem_orbit_self α
  have hstabα : Nat.card (GL83.PiGen.stabIn R α) = 3 := by
    have h := GL83.PiGen.card_mul_card_stabIn R α
    rw [hR27, hα] at h
    omega
  have hfixO : ∀ v ∈ GL83.PiGen.stabIn R α, ∀ y ∈ O, v y = y := by
    intro v hv y hy
    have h := stabIn_eq_of_mem_orbit hRcomm hy
    rw [← h] at hv
    exact GL83.PiGen.mem_fixSet_stabIn R y v hv
  set Γ' := ((GLBCore 3 2 B).subgroupOf K).map ((alternatingGroup (Fin 12)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)))) with hΓ'
  have hmem : ∀ {V : Subgroup (Perm (Fin 12))}, V ≤ R → 3 ≤ Nat.card V →
      ∀ {σ : Perm (Fin 12)}, σ ∈ alternatingGroup (Fin 12) → (∀ v ∈ V, v * σ = σ * v) → σ ∈ Γ' := by
    intro V hVR hV3 σ hσA hσV
    refine mem_map_of_commute Nat.prime_three (by norm_num) hB hK (by norm_num) (by norm_num) e hZ2 hVR
      ?_ hσA hσV
    calc 3 ^ 2 = 3 * 3 := by norm_num
      _ ≤ Nat.card (cen B K) * Nat.card V := Nat.mul_le_mul hcen hV3
  have hAltO : GL83.altOn O ≤ Γ' := by
    intro σ hσ
    refine hmem (GL83.PiGen.stabIn_le R α) (by rw [hstabα]) (GL83.mem_altOn.1 hσ).1 fun v hv => ?_
    have hdisj : Perm.Disjoint v σ := by
      intro y
      by_cases hy : y ∈ O
      · exact Or.inl (hfixO v hv y hy)
      · exact Or.inr ((GL83.mem_altOn.1 hσ).2 y hy)
    exact hdisj.commute.eq
  obtain ⟨π₀, hπ₀⟩ : ∃ y : Fin 12, y ∉ O := by
    by_contra h
    push Not at h
    have h1 : Nat.card ↥O = Nat.card (Fin 12) := Nat.card_congr (Equiv.subtypeUnivEquiv h)
    have h2 : Nat.card ↥O = 9 := hα
    rw [h2, Nat.card_fin] at h1
    omega
  have horbπ : Nat.card (orbit R π₀) = 3 := by
    have h1 := hle9 π₀
    have h2 := hnofix α π₀ hα
    obtain ⟨s, hs⟩ := (CFSG.Open.IsElemAbelian.isPGroup hRel).card_orbit π₀
    have h9 : Nat.card (orbit R π₀) ≠ 9 := fun h => hπ₀ (huniq α π₀ hα h)
    rw [hs] at h1 h2 h9 ⊢
    rcases s with _ | _ | _ | s
    · norm_num at h2
    · norm_num
    · norm_num at h9
    · exfalso
      have : 3 ^ 3 ≤ 3 ^ (s + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hstabπ : Nat.card (GL83.PiGen.stabIn R π₀) = 9 := by
    have h := GL83.PiGen.card_mul_card_stabIn R π₀
    rw [hR27, horbπ] at h
    omega
  obtain ⟨x, hxR, hxα, hxπ⟩ : ∃ x ∈ R, x ∉ GL83.PiGen.stabIn R α ∧ x ∉ GL83.PiGen.stabIn R π₀ := by
    have h1 : ¬ R ≤ GL83.PiGen.stabIn R α := fun h => by
      have := Subgroup.card_le_of_le h
      rw [hR27, hstabα] at this
      omega
    have h2 : ¬ R ≤ GL83.PiGen.stabIn R π₀ := fun h => by
      have := Subgroup.card_le_of_le h
      rw [hR27, hstabπ] at this
      omega
    obtain ⟨y, hyR, hy⟩ : ∃ y ∈ R, y ∉ GL83.PiGen.stabIn R α := by
      by_contra hc
      push Not at hc
      exact h1 hc
    obtain ⟨y', hy'R, hy'⟩ : ∃ y ∈ R, y ∉ GL83.PiGen.stabIn R π₀ := by
      by_contra hc
      push Not at hc
      exact h2 hc
    by_cases hyπ : y ∈ GL83.PiGen.stabIn R π₀
    · by_cases hy'α : y' ∈ GL83.PiGen.stabIn R α
      · refine ⟨y * y', R.mul_mem hyR hy'R, fun h => hy ?_, fun h => hy' ?_⟩
        · have := (GL83.PiGen.stabIn R α).mul_mem h ((GL83.PiGen.stabIn R α).inv_mem hy'α)
          simpa using this
        · have := (GL83.PiGen.stabIn R π₀).mul_mem ((GL83.PiGen.stabIn R π₀).inv_mem hyπ) h
          simpa using this
      · exact ⟨y', hy'R, hy'α, hy'⟩
    · exact ⟨y, hyR, hy, hyπ⟩
  have hx3 : x ^ 3 = 1 := hRel.2 x hxR
  have hmoveO : ∀ y ∈ O, x y ≠ y := fun y hy h => hxα (by
    rw [← stabIn_eq_of_mem_orbit hRcomm hy]
    exact (mem_stabIn_iff hxR y).2 h)
  have hxπ' : x π₀ ≠ π₀ := fun h => hxπ ((mem_stabIn_iff hxR π₀).2 h)
  have hxO : ∀ y ∈ O, x y ∈ O := fun y hy => mem_orbit_of_mem hxR hy
  have hnotO : ∀ y, y ∉ O → x y ∉ O := fun y hy hxy => hy (by
    have h := mem_orbit_of_mem (R.inv_mem hxR) hxy
    simpa using h)
  obtain ⟨β, hβO, hβ⟩ : ∃ β ∈ O, β ≠ α ∧ β ≠ x α ∧ β ≠ x (x α) := by
    by_contra h
    push Not at h
    have hsub : O ⊆ ↑({α, x α, x (x α)} : Finset (Fin 12)) := fun y hy => by
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hne
      push Not at hne
      exact hne.2.2 (h y hy hne.1 hne.2.1)
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
    have h2 : Nat.card ↥O = 9 := hα
    have h3 : ({α, x α, x (x α)} : Finset (Fin 12)).card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨γ, hγO, hγ⟩ : ∃ γ ∈ O, γ ≠ α ∧ γ ≠ x α ∧ γ ≠ x (x α) ∧ γ ≠ β ∧ γ ≠ x β ∧
      γ ≠ x (x β) := by
    by_contra h
    push Not at h
    have hsub : O ⊆ ↑({α, x α, x (x α), β, x β, x (x β)} : Finset (Fin 12)) := fun y hy => by
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hne
      push Not at hne
      exact hne.2.2.2.2.2 (h y hy hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1)
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
    have h2 : Nat.card ↥O = 9 := hα
    have h3 : ({α, x α, x (x α), β, x β, x (x β)} : Finset (Fin 12)).card ≤ 6 := Finset.card_le_six
    omega
  have hxαO := hxO α hαO
  have hxxαO := hxO _ hxαO
  have hxπ₀ := hnotO π₀ hπ₀
  have hxxπ₀ := hnotO _ hxπ₀
  have hne : ∀ {y z : Fin 12}, y ∈ O → z ∉ O → y ≠ z := fun hy hz h => hz (h ▸ hy)
  have tc1 : TwoCyc x π₀ α := TwoCyc.mk' hx3 hxπ' (hmoveO α hαO) (hne hαO hπ₀) (hne hαO hxπ₀)
    (hne hαO hxxπ₀)
  have tc2 : TwoCyc x β γ := TwoCyc.mk' hx3 (hmoveO β hβO) (hmoveO γ hγO) hγ.2.2.2.1 hγ.2.2.2.2.1
    hγ.2.2.2.2.2
  have tcαβ : TwoCyc x α β := TwoCyc.mk' hx3 (hmoveO α hαO) (hmoveO β hβO) hβ.1 hβ.2.1 hβ.2.2
  have tcαγ : TwoCyc x α γ := TwoCyc.mk' hx3 (hmoveO α hαO) (hmoveO γ hγO) hγ.1 hγ.2.1 hγ.2.2.1
  set g := cycSwap x π₀ α * cycSwap x β γ with hg
  have hgA : g ∈ alternatingGroup (Fin 12) := by
    rw [Perm.mem_alternatingGroup, hg, Perm.sign_mul, sign_cycSwap tc1, sign_cycSwap tc2]
    decide
  have hgx : x * g = g * x := by
    rw [hg, ← mul_assoc, cycSwap_commute hx3 tc1, mul_assoc, cycSwap_commute hx3 tc2, mul_assoc]
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 (fun h => hxπ' (by rw [h]; rfl))
  have hgΓ : g ∈ Γ' := by
    refine hmem ((Subgroup.zpowers_le).2 hxR) (by rw [hxcard]) hgA fun v hv => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (Commute.zpow_left (show Commute x g from hgx) k).eq
  have hg2 : ∀ y, (y = α ∨ y = x α ∨ y = x (x α)) → cycSwap x β γ y = y := by
    rintro y (rfl | rfl | rfl)
    · exact cycSwap_apply_of_ne tcαβ.ab tcαγ.ab tcαβ.axb tcαγ.axb tcαβ.axxb tcαγ.axxb
    · exact cycSwap_apply_of_ne tcαβ.xab tcαγ.xab tcαβ.xaxb tcαγ.xaxb tcαβ.xaxxb tcαγ.xaxxb
    · exact cycSwap_apply_of_ne tcαβ.xxab tcαγ.xxab tcαβ.xxaxb tcαγ.xxaxb tcαβ.xxaxxb
        tcαγ.xxaxxb
  have hgP : ∀ y, y ∉ O → y ∈ g '' O := by
    intro y hy
    have hcount : y = π₀ ∨ y = x π₀ ∨ y = x (x π₀) := by
      have h7 : (Oᶜ : Set (Fin 12)).ncard = 3 := by
        have h := Set.ncard_add_ncard_compl O
        rw [Nat.card_fin, ← Nat.card_coe_set_eq, show Nat.card ↥O = 9 from hα] at h
        omega
      have hsub2 : ({π₀, x π₀, x (x π₀)} : Set (Fin 12)) ⊆ Oᶜ := by
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl
        · exact hπ₀
        · exact hxπ₀
        · exact hxxπ₀
      have h3 : ({π₀, x π₀, x (x π₀)} : Set (Fin 12)).ncard = 3 :=
        Set.ncard_eq_three.2 ⟨_, _, _, tc1.a1, tc1.a2, tc1.a3, rfl⟩
      have heq := Set.eq_of_subset_of_ncard_le hsub2 (by rw [h3, h7])
      have hy' : y ∈ (Oᶜ : Set (Fin 12)) := hy
      rw [← heq] at hy'
      simpa using hy'
    rcases hcount with rfl | rfl | rfl
    · refine ⟨α, hαO, ?_⟩
      rw [hg, Perm.mul_apply, hg2 α (Or.inl rfl), cycSwap_apply_right tc1]
    · refine ⟨x α, hxαO, ?_⟩
      rw [hg, Perm.mul_apply, hg2 (x α) (Or.inr (Or.inl rfl)), cycSwap_apply_right_one tc1]
    · refine ⟨x (x α), hxxαO, ?_⟩
      rw [hg, Perm.mul_apply, hg2 (x (x α)) (Or.inr (Or.inr rfl)), cycSwap_apply_right_two tc1]
  have hgγ : g γ = β := by
    rw [hg, Perm.mul_apply, cycSwap_apply_right tc2]
    exact cycSwap_apply_of_ne (hne hβO hπ₀) hβ.1 (hne hβO hxπ₀) hβ.2.1 (hne hβO hxxπ₀) hβ.2.2
  have hAltgO : GL83.altOn (g '' O) ≤ Γ' := by
    intro σ hσ
    have hσA := (GL83.mem_altOn.1 hσ).1
    have hconj : g⁻¹ * σ * g ∈ GL83.altOn O := by
      refine GL83.mem_altOn.2 ⟨?_, fun y hy => ?_⟩
      · exact (alternatingGroup (Fin 12)).mul_mem ((alternatingGroup (Fin 12)).mul_mem
          ((alternatingGroup (Fin 12)).inv_mem hgA) hσA) hgA
      · have hgy : g y ∉ g '' O := fun ⟨z, hz, hzy⟩ => hy (g.injective hzy ▸ hz)
        simp only [Perm.mul_apply, (GL83.mem_altOn.1 hσ).2 _ hgy, Perm.coe_inv, Equiv.symm_apply_apply]
    have h1 := hAltO hconj
    have h2 : σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
    rw [h2]
    exact Γ'.mul_mem (Γ'.mul_mem hgΓ h1) (Γ'.inv_mem hgΓ)
  refine le_glbCore_of_alt_le hB2 hBN e hZ2 ?_
  set S : Fin 2 → Set (Fin 12) := ![O, g '' O] with hS
  have hS3 : ∀ i, 3 ≤ (S i).ncard := by
    intro i
    fin_cases i
    · show 3 ≤ O.ncard
      rw [← Nat.card_coe_set_eq]
      have : Nat.card ↥O = 9 := hα
      omega
    · show 3 ≤ (g '' O).ncard
      rw [Set.ncard_image_of_injective _ g.injective, ← Nat.card_coe_set_eq]
      have : Nat.card ↥O = 9 := hα
      omega
  have hcover : (⋃ i, S i) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ?_
    by_cases hy : y ∈ O
    · exact ⟨0, hy⟩
    · exact ⟨1, hgP y hy⟩
  have hconn : ∀ i j, Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j := by
    have h01 : (S 0 ∩ S 1).Nonempty := ⟨β, hβO, γ, hγO, hgγ⟩
    have h10 : (S 1 ∩ S 0).Nonempty := ⟨β, ⟨γ, hγO, hgγ⟩, hβO⟩
    intro i j
    fin_cases i <;> fin_cases j
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single h01
    · exact Relation.ReflTransGen.single h10
    · exact Relation.ReflTransGen.refl
  refine le_trans (le_of_eq (GL83.iSup_altOn_eq_alternatingGroup hS3 hcover hconn).symm) ?_
  refine iSup_le fun i => ?_
  fin_cases i
  · exact hAltO
  · exact hAltgO

theorem le_glbCore_of_alt_pred {B K : Subgroup X}
    (hB : IsElemAbelian 3 B) (hB2 : 2 ≤ CFSG.Open.pRank 3 B) (hK : IsComponentOf K ⊤) {n : ℕ}
    (hn12 : 12 ≤ n) (hn3 : n % 3 = 0) (hA : IsAltType n (↥K ⧸ Subgroup.center ↥K))
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hc1 : 1 ≤ CFSG.Open.pRank 3 (cen B K))
    (hrk : CFSG.Open.pRank 3 B + 1 = n / 3 + CFSG.Open.pRank 3 (cen B K)) :
    K ≤ GLBCore 3 2 B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hA
  have hq : CFSG.Open.IsQuasisimple K := hK.2.2
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  have hn5 : 5 ≤ n := by omega
  have hn6 : n ≠ 6 := by omega
  have hZ2 : Nat.card (Subgroup.center K) ∣ 2 := by
    have h := SchurFacts.card_center_dvd_of_isAltType hq ⟨e⟩
    rwa [if_neg (by omega)] at h
  set π := GL83.PiGen.permHom (GL83.PiGen.stab_le_normalizer B K) hn5 hn6 e with hπ
  have hAC : Nat.card (stab B K) = Nat.card (cen B K) * Nat.card π.range :=
    GL83.PiGen.card_stab_eq_mul hn5 hn6 e
  have hAel : IsElemAbelian 3 (stab B K) := elem_mono hB inf_le_left
  have hRel : IsElemAbelian 3 π.range := GL83.PiGen.isElemAbelian_range hAel π
  have hRcomm : ∀ x ∈ π.range, ∀ y ∈ π.range, x * y = y * x := fun x hx y hy => elem_comm hRel hx hy
  have hCel : IsElemAbelian 3 (cen B K) := elem_mono hB inf_le_left
  have hstab : stab B K = B := inf_eq_left.2 hBN
  obtain ⟨t, rfl⟩ : ∃ t, n = 3 * t := ⟨n / 3, by omega⟩
  have ht3 : 3 * t / 3 = t := by omega
  rw [ht3] at hrk
  have hR : Nat.card π.range = 3 ^ (t - 1) := by
    have h1 : Nat.card (stab B K) = 3 ^ CFSG.Open.pRank 3 B := by
      rw [hstab]
      exact GL83.PiGen.card_eq_pow_pRank hB
    have h2 := GL83.PiGen.card_eq_pow_pRank hCel
    rw [h1, h2] at hAC
    have hm : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (cen B K) + (t - 1) := by omega
    rw [hm, pow_add] at hAC
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) hAC).symm
  have hcen3 : 3 ≤ Nat.card (cen B K) := by
    rw [GL83.PiGen.card_eq_pow_pRank hCel]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hc1
  obtain ⟨hle9, huniq, -⟩ := orbit_shape rfl hRel (le_of_eq hR.symm)
  have hsz : ∀ y : Fin (3 * t), Nat.card (orbit π.range y) = 1 ∨ Nat.card (orbit π.range y) = 3 ∨
      Nat.card (orbit π.range y) = 9 := by
    intro y
    obtain ⟨s, hs⟩ := (CFSG.Open.IsElemAbelian.isPGroup hRel).card_orbit y
    have h := hle9 y
    rw [hs] at h ⊢
    rcases s with _ | _ | _ | s
    · norm_num
    · norm_num
    · norm_num
    · exfalso
      have : 3 ^ 3 ≤ 3 ^ (s + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  by_cases h12 : t = 4 ∧ ∃ α : Fin (3 * t), Nat.card (orbit π.range α) = 9
  · obtain ⟨rfl, α, hα⟩ := h12
    exact le_glbCore_of_alt_twelve hB hB2 hK e hZ2 hBN hcen3 (by rw [hR]; norm_num) hα
  refine le_glbCore_of_alt_pairs Nat.prime_three (by norm_num) hB hB2 hK hn5 hn6 e hZ2 hBN ?_ ?_
  · intro hbot
    have h1 : Nat.card π.range = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hR] at h1
    have : 3 ^ 1 ≤ 3 ^ (t - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  intro ω ω'
  suffices h : 3 ≤ Nat.card (Claims138.pairStab π.range ω ω') by
    calc 3 ^ 2 = 3 * 3 := by norm_num
      _ ≤ _ := Nat.mul_le_mul hcen3 h
  have h27 : 27 ≤ 3 ^ (t - 1) := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (t - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_contra hlt
  push Not at hlt
  have hb : Nat.card (Claims138.pairStab π.range ω ω') ≤ 2 := by omega
  by_cases hω' : ω' ∈ orbit π.range ω
  · have heq : Claims138.pairStab π.range ω ω' = GL83.PiGen.stabIn π.range ω := by
      rw [Claims138.pairStab, stabIn_eq_of_mem_orbit hRcomm hω', inf_idem]
    rw [heq] at hb
    have h1 := GL83.PiGen.card_mul_card_stabIn π.range ω
    rw [hR] at h1
    have h2 := Nat.mul_le_mul (hle9 ω) hb
    omega
  · have h1 := card_le_mul_pairStab hRcomm ω ω'
    rw [hR] at h1
    by_cases ht4 : t = 4
    · subst ht4
      have hno9 : ∀ y, Nat.card (orbit π.range y) ≠ 9 := fun y hy => h12 ⟨rfl, y, hy⟩
      have hprod : Nat.card (orbit π.range ω) * Nat.card (orbit π.range ω') ≤ 9 := by
        rcases hsz ω with h | h | h <;> rcases hsz ω' with h' | h' | h' <;>
          first | exact absurd h (hno9 ω) | exact absurd h' (hno9 ω') | (rw [h, h']; try norm_num)
      have h2 := Nat.mul_le_mul hprod hb
      rw [show 3 ^ (4 - 1) = 27 by norm_num] at h1
      omega
    · have h81 : 81 ≤ 3 ^ (t - 1) := by
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ 3 ^ (t - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hprod : Nat.card (orbit π.range ω) * Nat.card (orbit π.range ω') ≤ 27 := by
        rcases hsz ω with h | h | h <;> rcases hsz ω' with h' | h' | h' <;>
          first | exact absurd (huniq ω ω' h h') hω' | (rw [h, h']; try norm_num)
      have h2 := Nat.mul_le_mul hprod hb
      omega

end AltPred

end AltRank

section Rank3


theorem rank3CuResExc_of_res_cube (hQ : SeitzQuasiAt 3) (hX : InputsSeitz5.Rank3CuResExcRes) :
    InputsSeitz3.Rank3CuResExc := by
  intro G _ _ m p B M E A D T R L0 d h h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal htype
  have h139b' := h139b
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hB4 : 4 ≤ CFSG.Open.pRank 3 B := Claims1310.pRank_B_eq h ▸ h.standing.four_le
  rcases htype with ⟨n, hA⟩ | ⟨i, ⟨e⟩, hi3, hexc, hrest⟩
  · have hq := Lemma1313.isQuasisimple_barOf_of_pComp hKc
    have hn5 : 5 ≤ n := SchurFacts.five_le_of_isAltType hq hA
    have hPi : ¬ (n % 3 = 2 ∨ n = 7) := by
      intro hn
      apply hpi
      obtain ⟨eA⟩ := hA
      refine ⟨hq, glaPPrimeCore_quotient_eq_bot hp, ?_⟩
      rcases hn with hn | rfl
      · obtain ⟨k, rfl⟩ : ∃ k, n = k * 3 + 2 := ⟨n / 3, by omega⟩
        exact Or.inl ⟨k, ⟨eA⟩⟩
      · exact Or.inr (Or.inr ⟨rfl, ⟨eA⟩⟩)
    have hn6 : n ≠ 6 := by
      rintro rfl
      obtain ⟨eA⟩ := hA
      have h1 := InputsSeitz.pRank_aut_le_two_of_alt6 hp (by norm_num) hq.1 eA
      omega
    exact hX h h139b' hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal
      (Or.inl ⟨n, by omega, fun h => hPi (Or.inl h), hA⟩)
  have hsm : ¬ (i.1 = .tits ∨ i.1 = .suzuki 2 ∨ IsL2EightIndex i.1) := fun hs => by
    have h1 := InputsSeitz5.pRank_mulAut_le_two_of_small (Lemma1313.isQuasisimple_barOf_of_pComp hKc) i e
      hexc hs
    omega
  by_cases hsix : IsSixIndex i.1 ∧ InputsSeitz3.autIm (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤
      (MulAut.conj : ↥(barX 3 (Cg u) Kc) →* MulAut ↥(barX 3 (Cg u) Kc)).range
  swap
  · exact hX h h139b' hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal
      (Or.inr ⟨i, ⟨e⟩, hi3, hexc, fun h' => hsm (Or.inl h'), fun h' => hsm (Or.inr (Or.inr h')),
        fun h6 hin => hsix ⟨h6, hin⟩, hrest⟩)
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  have hBC : B ≤ Cg u := Prop1310a5b.le_cg_of_mem hBel huB
  have hnorm : ∀ E' : Subgroup G, E' ≤ B → 2 ≤ CFSG.Open.pRank 3 E' →
      Subgroup.normalizer (E' : Set G) ≤ M :=
    fun E' hE' hr => (normalizer_le_glbCore hE' hr).trans h.uniq.clause_d
  have hcore : GLAPPrimeCoreOf 3 (Cg u) ≤ M := le_sup_left.trans (h.uniq.clause_a u huB hu1)
  have hpi3 : 3 ≠ i.1.characteristic := fun h => hi3 h.symm
  have eK : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX hp hKc.1 hKc.2.1
  have hqK : CFSG.Open.IsQuasisimple ↥(barX 3 (Cg u) Kc) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eK.symm (Lemma1313.isQuasisimple_barOf_of_pComp hKc)
  have eZ : ↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc) ≃*
      (TauCeti.CFSGIndex.lie i).Group :=
    (Lemma1315b.centerQuotEquiv eK.symm).trans e
  have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hBtrk : CFSG.Open.pRank 3 (barX 3 (Cg u) B) = CFSG.Open.pRank 3 B :=
    rank_barX_of_isPGroup hp (CFSG.Open.IsElemAbelian.isPGroup hBel) hBC
  have hBtN : barX 3 (Cg u) B ≤
      Subgroup.normalizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :=
    barX_le_normalizer hN
  have hstab : stab (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) = barX 3 (Cg u) B := inf_eq_left.2 hBtN
  have hcen3 : Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ≤ 3 := by
    obtain ⟨c, hc⟩ : ∃ c, Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) = 3 ^ c :=
      GL83.CompFam.exists_card_eq_pow (elem_mono hBtel inf_le_left)
    have hcr : c ≤ 1 :=
      (CFSG.SectionRank.le_pRank (by norm_num) le_rfl (elem_mono hBtel inf_le_left) hc).trans hcen
    rw [hc]
    calc 3 ^ c ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hcr
      _ = 3 := by norm_num
  have h3le : 3 ^ 3 * Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ≤
      Nat.card (stab (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) := by
    rw [hstab, GL83.PiGen.card_eq_pow_pRank hBtel, hBtrk]
    calc 3 ^ 3 * Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ≤ 3 ^ 3 * 3 :=
          Nat.mul_le_mul_left _ hcen3
      _ = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 B := Nat.pow_le_pow_right (by norm_num) hB4
  have hL34b : ¬ IsLThreeFour (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc)) := fun h => by
    have h1 := InputsSeitz3.pRank_mulAut_le_two_of_l34 (Lemma1313.isQuasisimple_barOf_of_pComp hKc).1 h
    omega
  have hL34 : ¬ (3 = 3 ∧
      IsLThreeFour (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc))) :=
    fun h => hL34b (InputsSeitz3.isLThreeFour_congr (Lemma1315b.centerQuotEquiv eK) h.2)
  obtain ⟨Ee, hEN, hEC, hEcard⟩ := InputsSeitz3.exists_faithful hp hBtel h3le
  have hEB : Ee ≤ barX 3 (Cg u) B := hEN.trans inf_le_left
  have hENK := hEN.trans inf_le_right
  have hEel : IsElemAbelian 3 Ee := elem_mono hBtel hEB
  have hgen := hQ 3 hp (by norm_num) _ hqK i ⟨eZ⟩ hpi3 hL34 _ (InputsSeitz3.isElemAbelian_autIm hEel _)
    (by rw [InputsSeitz3.card_autIm hENK hEC, hEcard])
    (Or.inr ⟨hsix.1, (InputsSeitz5.autIm_mono hEB _).trans hsix.2⟩)
  exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc
    (InputsSeitz3.le_glbCore_of_centGenI hp hEB hEel hEcard.ge
      (InputsSeitz3.le_centGenI_of_autIm hENK hEC hgen))

theorem rank3CuRes_of_seitzQuasiAt (h2 : KFactSeitzRankTwo) (hQ : SeitzQuasiAt 3)
    (hX0 : InputsSeitz5.Rank3CuResExcRes) : Claims1310.Rank3CuRes := by
  have hX : InputsSeitz3.Rank3CuResExc := rank3CuResExc_of_res_cube hQ hX0
  intro G _ _ m p B M E A D T R L0 d h h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal
  have h139b' := h139b
  have hgood0 := hgood
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hS : GLStanding G m 3 := h.standing
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  have hBC : B ≤ Cg u := Prop1310a5b.le_cg_of_mem hBel huB
  have hBm : CFSG.Open.pRank 3 B = m := Claims1310.pRank_B_eq h
  have hB4 : 4 ≤ CFSG.Open.pRank 3 B := hBm ▸ hS.four_le
  have hnorm : ∀ E' : Subgroup G, E' ≤ B → 2 ≤ CFSG.Open.pRank 3 E' →
      Subgroup.normalizer (E' : Set G) ≤ M :=
    fun E' hE' hr => (normalizer_le_glbCore hE' hr).trans h.uniq.clause_d
  have hcore : GLAPPrimeCoreOf 3 (Cg u) ≤ M := le_sup_left.trans (h.uniq.clause_a u huB hu1)
  rcases hgood with hAlt | ⟨q, hq3, hL⟩ | hA2
  · exact hX h h139b' hU u hu hu1 hlt Kc hKc hgood0 hN haut hcen hpi hbal (Or.inl hAlt)
  swap
  · exfalso
    have h1 := InputsSeitz.pRank_top_le_of_forall hp hA2
    omega
  obtain ⟨i, ⟨e⟩, hiq⟩ := hL
  have hiq' : i.1.characteristic = q := hiq
  have hi3 : i.1.characteristic ≠ 3 := hiq' ▸ hq3
  have hpi3 : 3 ≠ i.1.characteristic := fun h => hi3 h.symm
  have eK : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX hp hKc.1 hKc.2.1
  have hqK : CFSG.Open.IsQuasisimple ↥(barX 3 (Cg u) Kc) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eK.symm (Lemma1313.isQuasisimple_barOf_of_pComp hKc)
  have eZ : ↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc) ≃*
      (TauCeti.CFSGIndex.lie i).Group :=
    (Lemma1315b.centerQuotEquiv eK.symm).trans e
  have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hBtrk : CFSG.Open.pRank 3 (barX 3 (Cg u) B) = CFSG.Open.pRank 3 B :=
    rank_barX_of_isPGroup hp (CFSG.Open.IsElemAbelian.isPGroup hBel) hBC
  have hBtN : barX 3 (Cg u) B ≤
      Subgroup.normalizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :=
    barX_le_normalizer hN
  have hstab : stab (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) = barX 3 (Cg u) B := inf_eq_left.2 hBtN
  have hcen3 : Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ≤ 3 := by
    obtain ⟨c, hc⟩ : ∃ c, Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) = 3 ^ c :=
      GL83.CompFam.exists_card_eq_pow (elem_mono hBtel inf_le_left)
    have hcr : c ≤ 1 :=
      (CFSG.SectionRank.le_pRank (by norm_num) le_rfl (elem_mono hBtel inf_le_left) hc).trans hcen
    rw [hc]
    calc 3 ^ c ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hcr
      _ = 3 := by norm_num
  have h3le : 3 ^ 3 * Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ≤
      Nat.card (stab (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) := by
    rw [hstab, GL83.PiGen.card_eq_pow_pRank hBtel, hBtrk]
    calc 3 ^ 3 * Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ≤ 3 ^ 3 * 3 :=
          Nat.mul_le_mul_left _ hcen3
      _ = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 B := Nat.pow_le_pow_right (by norm_num) hB4
  have hL34b : ¬ IsLThreeFour (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc)) := fun h => by
    have h1 := InputsSeitz3.pRank_mulAut_le_two_of_l34 (Lemma1313.isQuasisimple_barOf_of_pComp hKc).1 h
    omega
  by_cases hgood' : ¬ ExcIndex 3 i.1
  · obtain ⟨Ee, hEN, hEC, hEcard⟩ := InputsSeitz3.exists_faithful hp hBtel h3le
    have hEB : Ee ≤ barX 3 (Cg u) B := hEN.trans inf_le_left
    have hENK := hEN.trans inf_le_right
    have hEel : IsElemAbelian 3 Ee := elem_mono hBtel hEB
    have hL34 : ¬ (3 = 3 ∧
        IsLThreeFour (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc))) :=
      fun h => hL34b (InputsSeitz3.isLThreeFour_congr (Lemma1315b.centerQuotEquiv eK) h.2)
    have hgen := hQ 3 hp (by norm_num) _ hqK i ⟨eZ⟩ hpi3 hL34 _ (InputsSeitz3.isElemAbelian_autIm hEel _)
      (by rw [InputsSeitz3.card_autIm hENK hEC, hEcard]) (Or.inl hgood')
    exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc
      (InputsSeitz3.le_glbCore_of_centGenI hp hEB hEel hEcard.ge
        (InputsSeitz3.le_centGenI_of_autIm hENK hEC hgen))
  have hexc : ExcIndex 3 i.1 := not_not.1 hgood'
  by_cases hroute : Subgroup.center (barOf 3 Kc) = ⊥ ∧
      cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≠ ⊥ ∧ ¬ IsD2SeitzException 3 i.1
  · obtain ⟨hZ, hC1, hnd⟩ := hroute
    have hZt : Subgroup.center ↥(barX 3 (Cg u) Kc) = ⊥ := by
      rw [← Subgroup.map_center_eq eK, hZ, Subgroup.map_bot]
    obtain ⟨E₂, hE₂N, hE₂C, hE₂card⟩ := InputsSeitz3.exists_faithful hp hBtel (k := 2)
      ((Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by norm_num))).trans h3le)
    have hE₂B : E₂ ≤ barX 3 (Cg u) B := hE₂N.trans inf_le_left
    have hE₂NK := hE₂N.trans inf_le_right
    have hE₂el : IsElemAbelian 3 E₂ := elem_mono hBtel hE₂B
    have hgen := InputsSeitz3.seitzHyperGamma_eq_top_of_plane h2 hp (by norm_num) hZt i eZ hpi3 hnd
      (InputsSeitz3.isElemAbelian_autIm hE₂el _) (by rw [InputsSeitz3.card_autIm hE₂NK hE₂C, hE₂card])
    have hE₂cen : E₂ ⊓ cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_left _ (inf_le_right :
        cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤ _)).trans hE₂C.le)
    exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc
      (InputsSeitz3.le_glbCore_of_centGenI_central hp hBtel hE₂B inf_le_left inf_le_right hE₂cen hC1
        hE₂card.ge (InputsSeitz3.le_centGenI_of_autIm hE₂NK hE₂C hgen))
  refine hX h h139b' hU u hu hu1 hlt Kc hKc hgood0 hN haut hcen hpi hbal
    (Or.inr ⟨i, ⟨e⟩, hi3, hexc, ?_⟩)
  by_cases hZ : Subgroup.center (barOf 3 Kc) = ⊥
  · by_cases hC1 : cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) = ⊥
    · exact Or.inr (Or.inl hC1)
    · exact Or.inr (Or.inr (by by_contra hnd; exact hroute ⟨hZ, hC1, hnd⟩))
  · exact Or.inl hZ

end Rank3

section AltFour

open Equiv Equiv.Perm

theorem pow_three_eq_one_mult {s : ℕ} (u : Multiplicative (Fin s → ZMod 3)) : u ^ 3 = 1 := by
  rw [← ofAdd_toAdd u, ← ofAdd_nsmul]
  have : 3 • Multiplicative.toAdd u = 0 := by
    ext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [this]
  rfl

theorem exists_elem_three_normalizing_four (n : ℕ) (hn : 4 ≤ n) :
    ∃ W V : Subgroup ↥(alternatingGroup (Fin n)), IsElemAbelian 3 W ∧ Nat.card W = 3 ^ ((n - 1) / 3) ∧
      IsPGroup 2 ↥V ∧ V ≠ ⊥ ∧ W ≤ Subgroup.normalizer (V : Set ↥(alternatingGroup (Fin n))) := by
  classical
  set s := (n - 4) / 3 with hs
  have hs1 : (n - 1) / 3 = s + 1 := by omega
  obtain ⟨emb⟩ : Nonempty ((Fin 4 ⊕ (Fin s × ZMod 3)) ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card]
      omega)
  let ψ : ↥(alternatingGroup (Fin 4)) × Multiplicative (Fin s → ZMod 3) →*
      Perm (Fin 4) × Perm (Fin s × ZMod 3) :=
    MonoidHom.prodMap (alternatingGroup (Fin 4)).subtype GL83.PiGen.shiftHom
  let φ : ↥(alternatingGroup (Fin 4)) × Multiplicative (Fin s → ZMod 3) →* Perm (Fin n) :=
    (Equiv.Perm.extendDomainHom emb.toEquivRange).comp
      ((Equiv.Perm.sumCongrHom (Fin 4) (Fin s × ZMod 3)).comp ψ)
  have hψ : Function.Injective ψ := by
    rw [show ⇑ψ = Prod.map _ _ from MonoidHom.coe_prodMap _ _]
    exact Prod.map_injective.2 ⟨Subtype.val_injective, GL83.PiGen.shiftHom_injective⟩
  have hφ : Function.Injective φ :=
    (Equiv.Perm.extendDomainHom_injective _).comp (Equiv.Perm.sumCongrHom_injective.comp hψ)
  have hφA : ∀ h, φ h ∈ alternatingGroup (Fin n) := by
    rintro ⟨a, x⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    have e1 : φ (a, x) = Equiv.Perm.extendDomain (Equiv.Perm.sumCongr (a : Perm (Fin 4))
        (GL83.PiGen.shiftHom x)) emb.toEquivRange := rfl
    rw [e1, Equiv.Perm.sign_extendDomain, Equiv.Perm.sign_sumCongr]
    have ha : Equiv.Perm.sign (a : Perm (Fin 4)) = 1 := Equiv.Perm.mem_alternatingGroup.1 a.2
    have hx : GL83.PiGen.shiftHom x ∈ alternatingGroup (Fin s × ZMod 3) :=
      GL83.PiGen.mem_alternatingGroup_of_pow_eq_one (by decide : Odd 3)
        (by rw [← map_pow, pow_three_eq_one_mult x, map_one])
    rw [ha, Equiv.Perm.mem_alternatingGroup.1 hx, one_mul]
  let φA := φ.codRestrict (alternatingGroup (Fin n)) hφA
  have hφAinj : Function.Injective φA := fun a b h => hφ (congrArg Subtype.val h)
  have hcmem : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 4) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    simp
  let c : ↥(alternatingGroup (Fin 4)) := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, hcmem⟩
  have hc3 : c ^ 3 = 1 := by
    apply Subtype.ext
    show (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) ^ 3 = 1
    decide
  have hc1 : c ≠ 1 := by
    intro h
    have h' : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) = 1 := congrArg Subtype.val h
    exact absurd h' (by decide)
  have hZcard : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  set W₀ : Subgroup (↥(alternatingGroup (Fin 4)) × Multiplicative (Fin s → ZMod 3)) :=
    (Subgroup.zpowers c).prod ⊤ with hW₀
  set V₀ : Subgroup (↥(alternatingGroup (Fin 4)) × Multiplicative (Fin s → ZMod 3)) :=
    (alternatingGroup.kleinFour (Fin 4)).prod ⊥ with hV₀
  have h4 : Nat.card (Fin 4) = 4 := Nat.card_fin 4
  haveI := alternatingGroup.normal_kleinFour h4
  have hV₀N : V₀.Normal := Subgroup.prod_normal _ _
  have hW₀el : IsElemAbelian 3 W₀ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨⟨a1, a2⟩, ha⟩ := a
      obtain ⟨⟨b1, b2⟩, hb⟩ := b
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_prod.1 ha).1
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_prod.1 hb).1
      have hi' : c ^ i = a1 := hi
      have hj' : c ^ j = b1 := hj
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      refine Prod.ext ?_ (mul_comm a2 b2)
      show a1 * b1 = b1 * a1
      rw [← hi', ← hj']
      exact (Commute.zpow_zpow_self c i j).eq
    · obtain ⟨x1, x2⟩ := x
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_prod.1 hx).1
      have hi' : c ^ i = x1 := hi
      refine Prod.ext ?_ (pow_three_eq_one_mult x2)
      show x1 ^ 3 = 1
      rw [← hi', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hW₀card : Nat.card W₀ = 3 ^ (s + 1) := by
    rw [hW₀, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hZcard,
      Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
      Nat.card_fin, pow_succ, mul_comm]
  have hV₀card : Nat.card V₀ = 4 := by
    rw [hV₀, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      alternatingGroup.kleinFour_card_of_card_eq_four h4, Subgroup.card_bot, mul_one]
  refine ⟨W₀.map φA, V₀.map φA, CFSG.SectionRank.isElemAbelian_map hW₀el φA, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hφAinj, hW₀card, hs1]
  · refine IsPGroup.map ?_ φA
    exact IsPGroup.of_card (n := 2) (by rw [hV₀card]; norm_num)
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hφAinj]
    intro h
    rw [h, Subgroup.card_bot] at hV₀card
    omega
  · refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map φA)
    rw [Subgroup.normalizer_eq_top]
    exact le_top

theorem le_of_normalizes_bar {G : Type} [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 3)
    (C : Subgroup G) {F V : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C)} (hF : IsElemAbelian 3 F)
    (hV : IsPGroup 2 ↥V) (hV1 : V ≠ ⊥)
    (hFV : F ≤ Subgroup.normalizer (V : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)))
    {k : ℕ} (hFk : Nat.card F = 3 ^ k) : k ≤ m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN3 : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥C) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  obtain ⟨S, hSel, hSmap, hScard⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.exists_elemAbelian_lift (GLAPPrimeCore 3 ↥C) hN3 hF
  set H : Subgroup ↥C := V.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)) with hH
  have hHcard : Nat.card H = Nat.card (GLAPPrimeCore 3 ↥C) * Nat.card V :=
    QuotientGroup.card_preimage_mk (GLAPPrimeCore 3 ↥C) (V : Set (↥C ⧸ GLAPPrimeCore 3 ↥C))
  have hSH : S ≤ Subgroup.normalizer (H : Set ↥C) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hsF : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) s ∈ F := hSmap ▸ Subgroup.mem_map_of_mem _ hs
    have := Subgroup.mem_normalizer_iff.1 (hFV hsF) (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) x)
    simp only [hH, Subgroup.mem_comap, map_mul, map_inv]
    exact this
  have hH3 : ¬ 3 ∣ Nat.card H := by
    rw [hHcard]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h1 | h1
    · exact hN3 h1
    · obtain ⟨j, hj⟩ := hV.exists_card_eq
      rw [hj] at h1
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow h1)
      omega
  have hHeven : Even (Nat.card H) := by
    rw [hHcard, even_iff_two_dvd]
    exact Dvd.dvd.mul_left (dvd_card_of_isPGroup hV hV1) _
  obtain ⟨T, hT1, -, hT2, hST⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.exists_twoGroup_normalized_of_coprime_even
      Nat.prime_three (by norm_num) (CFSG.Open.IsElemAbelian.isPGroup hSel) hSH hH3 hHeven
  have hT'1 : T.map C.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective]
    exact hT1
  have hT'2 : IsPGroup 2 ↥(T.map C.subtype) := hT2.map _
  have hS'T' : S.map C.subtype ≤ Subgroup.normalizer ((T.map C.subtype : Subgroup G) : Set G) :=
    (Subgroup.map_mono hST).trans (Subgroup.le_normalizer_map _)
  have h1 := CFSG.HardMathSupport.Solomon.LocalBalance.pRank_le_glaTwoLocalRank_of_normalizes
    Nat.prime_three hT'1 hT'2 hS'T'
  rw [hS.rank_eq] at h1
  have hS'el : IsElemAbelian 3 (S.map C.subtype) := CFSG.SectionRank.isElemAbelian_map hSel _
  have hS'c : Nat.card (S.map C.subtype) = 3 ^ k := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hScard, hFk]
  exact (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hS'el hS'c).trans h1

theorem alt_rank_bound {G : Type} [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 3) {u : G}
    {B Kc : Subgroup G} (hBel : IsElemAbelian 3 B) {n : ℕ} (hn4 : 4 ≤ n)
    (eA : ↥(barX 3 (Cg u) Kc) ≃* ↥(alternatingGroup (Fin n))) :
    (n - 1) / 3 + CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
      Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨W, V, hWel, hWc, hV2, hV1, hWV⟩ := exists_elem_three_normalizing_four n hn4
  set Kt := barX 3 (Cg u) Kc with hKt
  set Ct := barX 3 (Cg u) B ⊓ Subgroup.centralizer ((Kt : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
    Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) with hCt
  set ι : ↥(alternatingGroup (Fin n)) →* (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)) :=
    Kt.subtype.comp eA.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := Kt.subtype_injective.comp eA.symm.injective
  have hιK : ∀ x, ι x ∈ Kt := fun x => (eA.symm x).2
  set Wt := W.map ι with hWt
  set Vt := V.map ι with hVt
  have hWtK : Wt ≤ Kt := by rintro _ ⟨x, -, rfl⟩; exact hιK x
  have hVtK : Vt ≤ Kt := by rintro _ ⟨x, -, rfl⟩; exact hιK x
  have hCtel : IsElemAbelian 3 Ct := elem_mono (isElemAbelian_barX hBel) inf_le_left
  have hWtel : IsElemAbelian 3 Wt := CFSG.SectionRank.isElemAbelian_map hWel ι
  have hWtc : Nat.card Wt = 3 ^ ((n - 1) / 3) := by
    rw [Subgroup.card_map_of_injective hιinj, hWc]
  have hCtc := GL83.PiGen.card_eq_pow_pRank hCtel
  have hcomm : ∀ x ∈ Wt, ∀ y ∈ Ct, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 hy.2 x (hWtK hx))
  have hZ : ∀ k : ↥(alternatingGroup (Fin n)), (∀ k' : ↥(alternatingGroup (Fin n)), k * k' = k' * k) → k = 1 := by
    intro k hk
    have hmem : k ∈ Subgroup.center ↥(alternatingGroup (Fin n)) :=
      Subgroup.mem_center_iff.2 fun g => (hk g).symm
    rw [alternatingGroup.center_eq_bot (by simpa using hn4)] at hmem
    exact hmem
  have hd : Wt ⊓ Ct = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rw [Subgroup.mem_bot]
    obtain ⟨⟨w, -, rfl⟩, hxC⟩ := hx
    have hw : w = 1 := hZ w fun k' => by
      apply eA.symm.injective
      apply Subtype.ext
      have h1 := Subgroup.mem_centralizer_iff.1 hxC.2 (ι k') (hιK k')
      simp only [hι, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom] at h1
      simp only [map_mul, Subgroup.coe_mul]
      exact h1.symm
    rw [hw, map_one]
  have hFel : IsElemAbelian 3 (Wt ⊔ Ct) := CFSG.Open.IsElemAbelian.sup_of_commute hWtel hCtel hcomm
  have hFc : Nat.card (Wt ⊔ Ct : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) =
      3 ^ ((n - 1) / 3 + CFSG.Open.pRank 3 Ct) := by
    rw [card_sup_of_commute_of_inf_eq_bot hcomm hd, hWtc, hCtc, pow_add]
  have hFV : Wt ⊔ Ct ≤ Subgroup.normalizer (Vt : Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) := by
    refine sup_le ((Subgroup.map_mono hWV).trans (Subgroup.le_normalizer_map _)) ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.1 hy.2 x (hVtK hx)
  have hVt2 : IsPGroup 2 ↥Vt := hV2.map ι
  have hVt1 : Vt ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hιinj]
    exact hV1
  exact le_of_normalizes_bar hS (Cg u) hFel hVt2 hVt1 hFV hFc

end AltFour

theorem cen_bar_ne_bot {G : Type} [Group G] [Finite G] {B : Subgroup G} (hBel : IsElemAbelian 3 B) {u : G}
    (huB : u ∈ B) (hu1 : u ≠ 1) (Kc : Subgroup G) :
    barX 3 (Cg u) B ⊓ Subgroup.centralizer ((barX 3 (Cg u) Kc :
      Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) : Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have huC : u ∈ Cg u := Subgroup.mem_centralizer_iff.2 fun g hg => by rw [Set.mem_singleton_iff.1 hg]
  have hū1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg u)) (⟨u, huC⟩ : ↥(Cg u)) ≠ 1 := by
    intro h1
    have hmem : (⟨u, huC⟩ : ↥(Cg u)) ∈ GLAPPrimeCore 3 ↥(Cg u) := (QuotientGroup.eq_one_iff _).1 h1
    have hN3 : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥(Cg u)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
    have hord : orderOf (⟨⟨u, huC⟩, hmem⟩ : ↥(GLAPPrimeCore 3 ↥(Cg u))) = 3 := by
      refine orderOf_eq_prime (Subtype.ext (Subtype.ext (by simpa using hBel.2 u huB))) fun h => hu1 ?_
      simpa using congrArg (fun x : ↥(GLAPPrimeCore 3 ↥(Cg u)) => ((x : ↥(Cg u)) : G)) h
    have hdvd := orderOf_dvd_natCard (⟨⟨u, huC⟩, hmem⟩ : ↥(GLAPPrimeCore 3 ↥(Cg u)))
    rw [hord] at hdvd
    exact hN3 hdvd
  have hūB : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg u)) (⟨u, huC⟩ : ↥(Cg u)) ∈ barX 3 (Cg u) B :=
    Subgroup.mem_map.2 ⟨⟨u, huC⟩, huB, rfl⟩
  have hūC : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg u)) (⟨u, huC⟩ : ↥(Cg u)) ∈
      Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 k.2 u (Set.mem_singleton u)).symm
  intro hbot
  have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg u)) (⟨u, huC⟩ : ↥(Cg u)) ∈
      (⊥ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) := hbot ▸ ⟨hūB, hūC⟩
  exact hū1 (Subgroup.mem_bot.1 hmem)

theorem one_le_pRank_cen_bar {G : Type} [Group G] [Finite G] {B : Subgroup G} (hBel : IsElemAbelian 3 B)
    {u : G} (huB : u ∈ B) (hu1 : u ≠ 1) (Kc : Subgroup G) :
    1 ≤ CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓ Subgroup.centralizer ((barX 3 (Cg u) Kc :
      Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) : Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hel : IsElemAbelian 3 (barX 3 (Cg u) B ⊓ Subgroup.centralizer ((barX 3 (Cg u) Kc :
      Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) : Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) :=
    elem_mono (isElemAbelian_barX hBel) inf_le_left
  have hcard := GL83.PiGen.card_eq_pow_pRank hel
  by_contra h0
  rw [show CFSG.Open.pRank 3 _ = 0 by omega, pow_zero] at hcard
  exact cen_bar_ne_bot hBel huB hu1 Kc (Subgroup.eq_bot_of_card_eq _ hcard)

@[expose] def Rank3CuResExcTwo : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139b p M D → ∀ {U : Subgroup G}, IsU1312 p B M D L0 d U →
      ∀ u ∈ U, u ≠ 1 →
        CFSG.Open.pRank 3 B < CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) →
        ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc → Prop1310a5b.Good2319 (barOf 3 Kc) →
          B ≤ Subgroup.normalizer (Kc : Set G) →
          CFSG.Open.pRank 3 B < 2 + CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 Kc))) →
          CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
            Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
              Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1 →
          ¬ IsPiGroup 3 (barOf 3 Kc) →
          IsStronglyLocallyOneBalanced 3 B u Kc →
          (∃ i : TauCeti.ValidLieTypeIndex,
              Nonempty (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group) ∧
              i.1.characteristic ≠ 3 ∧
              ExcIndex 3 i.1 ∧ i.1 ≠ .tits ∧ ¬ IsL2EightIndex i.1 ∧
              (IsSixIndex i.1 → ¬ InputsSeitz3.autIm (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤
                (MulAut.conj : ↥(barX 3 (Cg u) Kc) →* MulAut ↥(barX 3 (Cg u) Kc)).range) ∧
              ((Subgroup.center (barOf 3 Kc) ≠ ⊥ ∧
                  CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 i.1) ∨
                IsD2SeitzException 3 i.1)) →
          Kc ≤ M

theorem rank3CuResExcRes_of_two (hGA : GriessMultipliersAllModels)
    (hX : Rank3CuResExcTwo) : InputsSeitz5.Rank3CuResExcRes := by
  intro G _ _ m p B M E A D T R L0 d h h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal htype
  have h139b' := h139b
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  rcases htype with ⟨n, hn9, hn3, hA⟩ | ⟨i, ⟨e⟩, hi3, hexc, htits, hl28, hsix, hrest⟩
  ·
    have hBC : B ≤ Cg u := Prop1310a5b.le_cg_of_mem hBel huB
    have hBm : CFSG.Open.pRank 3 B = m := Claims1310.pRank_B_eq h
    have hB4 : 4 ≤ CFSG.Open.pRank 3 B := hBm ▸ h.standing.four_le
    have hnorm : ∀ E' : Subgroup G, E' ≤ B → 2 ≤ CFSG.Open.pRank 3 E' →
        Subgroup.normalizer (E' : Set G) ≤ M :=
      fun E' hE' hr => (normalizer_le_glbCore hE' hr).trans h.uniq.clause_d
    have hcore : GLAPPrimeCoreOf 3 (Cg u) ≤ M := le_sup_left.trans (h.uniq.clause_a u huB hu1)
    have eK : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX hp hKc.1 hKc.2.1
    have hKt : IsComponentOf (barX 3 (Cg u) Kc) ⊤ :=
      Lemma1314.isComponentOf_barX_of_glaPComponent hKc
    have hAt : IsAltType n (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc)) := by
      obtain ⟨eA⟩ := hA
      exact ⟨(Lemma1315b.centerQuotEquiv eK.symm).trans eA⟩
    have hZt : Subgroup.center ↥(barX 3 (Cg u) Kc) = ⊥ := by
      have hZ2 := SchurFacts.card_center_dvd_of_isAltType hKt.2.2 hAt
      rw [if_neg (by omega)] at hZ2
      have hZp : IsPGroup 3 ↥(Subgroup.center ↥(barX 3 (Cg u) Kc)) :=
        Inputs245b.isPGroup_center_of_component hp (glaPPrimeCore_quotient_eq_bot hp) hKt
      by_contra hne
      have h3 := (dvd_card_of_isPGroup hZp hne).trans hZ2
      omega
    obtain ⟨eA⟩ := hAt
    have hbound := alt_rank_bound h.standing hBel (n := n) (by omega)
      ((InputsSeitz3.equivCenterQuot hZt).trans eA)
    have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
    have hBtrk : CFSG.Open.pRank 3 (barX 3 (Cg u) B) = CFSG.Open.pRank 3 B :=
      rank_barX_of_isPGroup hp (CFSG.Open.IsElemAbelian.isPGroup hBel) hBC
    have hBtN : barX 3 (Cg u) B ≤
        Subgroup.normalizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
          Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :=
      barX_le_normalizer hN
    have hc1 := one_le_pRank_cen_bar hBel huB hu1 Kc
    by_cases hcase : n / 3 + CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
        Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
          Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ CFSG.Open.pRank 3 B
    · have hgam := le_glbCore_of_alt_of_rank hp (by norm_num) hBtel (hBtrk ▸ hB4) hKt
        (by omega : n ≠ 6) ⟨eA⟩ hBtN (by rw [hBtrk]; exact hcase)
      exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc hgam
    · have hrk : CFSG.Open.pRank 3 B + 1 = n / 3 + CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
          Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
            Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) := by
        omega
      have hgam := le_glbCore_of_alt_pred hBtel (by rw [hBtrk]; omega) hKt (n := n) (by omega)
        (by omega) ⟨eA⟩ hBtN hc1 (by rw [hBtrk]; exact hrk)
      exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc hgam
  · refine hX h h139b' hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal
      ⟨i, ⟨e⟩, hi3, hexc, htits, hl28, hsix, ?_⟩
    rcases hrest with hZ | hC | hD
    · have hq := Lemma1313.isQuasisimple_barOf_of_pComp hKc
      have hZp : IsPGroup 3 ↥(Subgroup.center (barOf 3 Kc)) :=
        SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot hp (glaPPrimeCore_quotient_eq_bot hp)
      exact Or.inl ⟨hZ, CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGA hp
        (by norm_num) hq i e (fun h => hi3 h.symm) (dvd_card_of_isPGroup hZp hZ)⟩
    · exact absurd hC (cen_bar_ne_bot hBel huB hu1 Kc)
    · exact Or.inr hD

theorem rank3CuResExcTwo_of_res (h : InputsSeitz5.Rank3CuResExcRes) : Rank3CuResExcTwo := by
  intro G _ _ m p B M E A D T R L0 d hc h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal htype
  refine h hc h139b hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal (Or.inr ?_)
  obtain ⟨i, hi, hi3, hexc, htits, hl28, hsix, hrest⟩ := htype
  refine ⟨i, hi, hi3, hexc, htits, hl28, hsix, ?_⟩
  rcases hrest with ⟨hZ, -⟩ | hD
  · exact Or.inl hZ
  · exact Or.inr (Or.inr hD)

section Assembled


theorem input23_19ChevCore_of_three (h2 : KFactSeitzRankTwo)
    (hQ : SeitzQuasiAt 3) (hGA : GriessMultipliersAllModels) (hX : Input23_19ExcThree) :
    InputsSeitz.Input23_19ChevCore :=
  input23_19ChevCore_of_seitzQuasiAt h2 hQ (input23_19ExcRes_of_three hGA hX)

theorem rank3CuRes_of_two (h2 : KFactSeitzRankTwo) (hQ : SeitzQuasiAt 3)
    (hGA : GriessMultipliersAllModels) (hX : Rank3CuResExcTwo) : Claims1310.Rank3CuRes :=
  rank3CuRes_of_seitzQuasiAt h2 hQ (rank3CuResExcRes_of_two hGA hX)

end Assembled

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz6

end
