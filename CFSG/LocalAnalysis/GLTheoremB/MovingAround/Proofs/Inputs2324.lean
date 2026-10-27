module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CentGenPair
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13b
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNN
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi23FiveGen
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs123b
public import CFSG.Sporadic.FischerOddCore.Fi23Aut

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
open GL83.CompFam
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf)

section General

variable {Y : Type} [Group Y] [Finite Y]

theorem isGMinusOne_of_isInGMinusOne {p : ℕ} {B K : Subgroup Y} (h : IsInGMinusOne p B K) :
    Lemma1314.IsGMinusOne p B K := by
  have key : ∀ (r : ℕ) (X : Subgroup Y), Lemma1314.GammaPrimeOf p B r X = gammaPrimeIn p r B X := by
    intro r X
    unfold Lemma1314.GammaPrimeOf gammaPrimeIn
    exact iSup_congr fun A => iSup_congr fun _ => inf_comm _ _
  unfold Lemma1314.IsGMinusOne Lemma1314.IsGClass
  rw [key]
  exact h

theorem isInGMinusOne_of_pRank_le_one {p : ℕ} {B L : Subgroup Y}
    (h : CFSG.Open.pRank p B ≤ 1) : IsInGMinusOne p B L := by
  unfold IsInGMinusOne
  rw [show CFSG.Open.pRank p B - 1 = 0 by omega]
  refine le_antisymm ?_ (by unfold gammaPrimeIn; exact iSup₂_le fun _ _ => inf_le_left)
  refine le_trans ?_ (i224_le_gammaPrimeIn (p := p) (E := ⊥) (B := B) bot_le (Nat.zero_le _))
  intro x hx
  refine ⟨hx, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
  rw [hg, one_mul, mul_one]

theorem isInGMinusOne_of_card_stab_le {p : ℕ} (hp : p.Prime) {B K : Subgroup Y}
    (hB : IsElemAbelian p B) (hK : IsComponentOf K ⊤) (h1 : 1 ≤ CFSG.Open.pRank p B)
    (hA : Nat.card (stab B K) ≤ p * Nat.card (cen B K)) : IsInGMinusOne p B K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hF := isFam_conjSet hB hK
  obtain ⟨m, hm⟩ := GL83.CompFam.exists_card_eq_pow hB
  have hpm : CFSG.Open.pRank p B = m := i224_pRank_eq hp hB hm
  have hm1 : 1 ≤ m := hpm ▸ h1
  have hBc : p ^ ((CFSG.Open.pRank p B - 1) + 1) ≤ Nat.card B := by
    rw [hm, hpm, Nat.sub_add_cancel hm1]
  have h := hF.layer_le_centGen (CFSG.Open.pRank p B - 1) (mem_conjSet_self B K) le_rfl hBc
    (by rw [pow_one]; exact hA)
  rw [layer_conjSet_eq_bClosure] at h
  unfold IsInGMinusOne
  refine le_antisymm (h.trans (iSup₂_le fun E hEB => iSup_le fun hEk => ?_)) ?_
  · have hEel : IsElemAbelian p E := elem_mono hB hEB
    obtain ⟨j, hj⟩ := GL83.CompFam.exists_card_eq_pow hEel
    have hj' : CFSG.Open.pRank p B - 1 ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hj ▸ hEk)
    exact i224_le_gammaPrimeIn hEB (hj'.trans (i224_pRank_eq hp hEel hj).ge)
  · unfold gammaPrimeIn
    exact iSup₂_le fun _ _ => inf_le_left

theorem le_gammaPrimeIn_of_centGen {p : ℕ} (hp : p.Prime) {B K : Subgroup Y}
    (hB : IsElemAbelian p B) (hinn : ∀ φ : MulAut ↥K, ∃ g : ↥K, φ = MulAut.conj g)
    (hZ : Subgroup.center ↥K = ⊥) (h3 : ¬ p ^ 3 ∣ Nat.card ↥K)
    (hCG : CFSG.HardMathSupport.Dickson.I271.CentGen p ↥K)
    (hA : p * Nat.card (cen B K) < Nat.card (stab B K)) :
    K ≤ gammaPrimeIn p (CFSG.Open.pRank p (stab B K) - 1) (stab B K) K := by
  haveI : Fact p.Prime := ⟨hp⟩
  set A : Subgroup Y := stab B K with hAdef
  have hAN : A ≤ Subgroup.normalizer (K : Set Y) := inf_le_right
  have hAel : IsElemAbelian p A := elem_mono hB inf_le_left
  have hCA : cen B K ≤ A := cen_le_stab B K
  let ψ : ↥A →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
  have hψ : ∀ (a : ↥A) (k : ↥K), ((ψ a k : ↥K) : Y) = (a : Y) * k * (a : Y)⁻¹ := by
    intro a k
    simp only [ψ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion]
  have hker : ∀ a : ↥A, ψ a = 1 → (a : Y) ∈ cen B K := by
    intro a ha
    rw [mem_cen]
    refine ⟨(mem_stab.1 a.2).1, fun x hx => ?_⟩
    have h2 := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : Y)) ha
    simp only [MulAut.one_apply] at h2
    rw [hψ] at h2
    calc (a : Y) * x = (a : Y) * x * (a : Y)⁻¹ * (a : Y) := by group
      _ = x * (a : Y) := by rw [h2]
  have hkerc : Nat.card ψ.ker ≤ Nat.card (cen B K) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨a, ha, rfl⟩
    exact hker a ha
  have hinj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := congrArg (fun φ : MulAut ↥K => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hZ] at hgZ
    exact Subgroup.mem_bot.1 hgZ
  have hrange : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, a', rfl⟩
      apply Subtype.ext
      show ψ a * ψ a' = ψ a' * ψ a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (elem_comm hAel a.2 a'.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (hAel.2 a a.2)
      rw [this, map_one]
  set P : Subgroup ↥K := ψ.range.comap (MulAut.conj : ↥K →* MulAut ↥K) with hPdef
  have hPmap : P.map (MulAut.conj : ↥K →* MulAut ↥K) = ψ.range := by
    rw [hPdef, Subgroup.map_comap_eq]
    refine inf_eq_right.2 ?_
    intro φ _
    obtain ⟨g, rfl⟩ := hinn φ
    exact ⟨g, rfl⟩
  have hPcardr : Nat.card P = Nat.card ψ.range := by
    rw [← hPmap, Subgroup.card_map_of_injective hinj]
  have hPel : IsElemAbelian p P := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have hx : MulAut.conj (x : ↥K) ∈ ψ.range := x.2
      have hy : MulAut.conj (y : ↥K) ∈ ψ.range := y.2
      simp only [Subgroup.coe_mul, map_mul]
      exact elem_comm hrange hx hy
    · rw [map_pow, hrange.2 _ hx, map_one]
  have hAcard : Nat.card A = Nat.card ψ.ker * Nat.card ψ.range :=
    (Subgroup.card_ker_mul_card_range ψ).symm
  obtain ⟨j, hj⟩ := GL83.CompFam.exists_card_eq_pow hPel
  have hj2 : j ≤ 2 := by
    by_contra hlt
    apply h3
    exact (hj ▸ pow_dvd_pow p (by omega : 3 ≤ j)).trans (Subgroup.card_subgroup_dvd_card P)
  have hj2' : 2 ≤ j := by
    by_contra hlt
    have hr : Nat.card ψ.range ≤ p := by
      rw [← hPcardr, hj]
      calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    have : Nat.card A ≤ p * Nat.card (cen B K) := by
      rw [hAcard, mul_comm p]
      exact Nat.mul_le_mul hkerc hr
    omega
  have hPcard : Nat.card P = p ^ 2 := by rw [hj, show j = 2 by omega]
  have hgen := hCG P hPel hPcard
  have key : ∀ σ ∈ {σ : ↥K | ∃ e ∈ P, e ≠ 1 ∧ σ * e = e * σ},
      (σ : Y) ∈ gammaPrimeIn p (CFSG.Open.pRank p A - 1) A K := by
    rintro σ ⟨x, hxP, hx1, hσx⟩
    have hxr : MulAut.conj x ∈ ψ.range := hxP
    obtain ⟨a, ha⟩ := hxr
    have haC : (a : Y) ∉ cen B K := by
      intro hac
      have h1 : ψ a = 1 := by
        refine MulEquiv.ext fun k => Subtype.ext ?_
        rw [hψ, MulAut.one_apply, (mem_cen.1 hac).2 k k.2]
        group
      rw [h1] at ha
      exact hx1 (hinj (ha.symm.trans (map_one _).symm))
    set E : Subgroup Y := cen B K ⊔ Subgroup.zpowers (a : Y) with hEdef
    have hEA : E ≤ A := sup_le hCA ((Subgroup.zpowers_le).2 a.2)
    have hEcard : Nat.card E = p * Nat.card (cen B K) := card_sup_zpowers hAel hCA a.2 haC
    have hEel : IsElemAbelian p E := elem_mono hAel hEA
    have hrk : CFSG.Open.pRank p A - 1 ≤ CFSG.Open.pRank p E := by
      rw [i224_card_le_iff hp hAel hEel, hAcard, hEcard]
      have hr2 : Nat.card ψ.range = p ^ 2 := by rw [← hPcardr, hPcard]
      rw [hr2]
      calc Nat.card ψ.ker * p ^ 2 ≤ Nat.card (cen B K) * p ^ 2 := Nat.mul_le_mul_right _ hkerc
        _ = p * (p * Nat.card (cen B K)) := by ring
    have hσa : (a : Y) * σ = σ * (a : Y) := by
      have h1 := congrArg (fun φ : MulAut ↥K => ((φ σ : ↥K) : Y)) ha
      simp only [MulAut.conj_apply] at h1
      rw [hψ] at h1
      have h2 : x * σ * x⁻¹ = σ := by rw [← hσx]; group
      rw [h2] at h1
      calc (a : Y) * σ = (a : Y) * σ * (a : Y)⁻¹ * (a : Y) := by group
        _ = σ * (a : Y) := by rw [h1]
    have hEc : E ≤ Subgroup.centralizer ({(σ : Y)} : Set Y) := by
      refine sup_le (fun c hc => Subgroup.mem_centralizer_singleton_iff.2 ((mem_cen.1 hc).2 σ σ.2))
        ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 hσa))
    have hσE : (σ : Y) ∈ Subgroup.centralizer (E : Set Y) :=
      Subgroup.mem_centralizer_iff.2 fun e he => Subgroup.mem_centralizer_singleton_iff.1 (hEc he)
    exact i224_le_gammaPrimeIn hEA hrk ⟨σ.2, hσE⟩
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥K) ∈ Subgroup.closure {σ : ↥K | ∃ e ∈ P, e ≠ 1 ∧ σ * e = e * σ} := by
    rw [hgen]
    exact Subgroup.mem_top _
  have hmem := Subgroup.mem_map_of_mem K.subtype hy'
  rw [MonoidHom.map_closure] at hmem
  refine (Subgroup.closure_le _).2 ?_ hmem
  rintro _ ⟨σ, hσ, rfl⟩
  exact key σ hσ

theorem model_facts_of_equiv {Y' S : Type*} [Group Y'] [Group S] (e : Y' ≃* S) {p : ℕ}
    (hinnS : ∀ φ : MulAut S, ∃ g : S, φ = MulAut.conj g) (hZS : Subgroup.center S = ⊥)
    (h3S : ¬ p ^ 3 ∣ Nat.card S) (hCGS : CFSG.HardMathSupport.Dickson.I271.CentGen p S) :
    (∀ φ : MulAut Y', ∃ g : Y', φ = MulAut.conj g) ∧ Subgroup.center Y' = ⊥ ∧
      ¬ p ^ 3 ∣ Nat.card Y' ∧ CFSG.HardMathSupport.Dickson.I271.CentGen p Y' := by
  refine ⟨CFSG.Sporadic.FischerOddCore.mulAut_eq_conj_of_mulEquiv e hinnS, ?_, ?_,
    CFSG.HardMathSupport.Dickson.I271.CentGen.of_mulEquiv e.symm hCGS⟩
  · have h := Subgroup.map_center_eq e
    rw [hZS] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h
  · rw [Nat.card_congr e.toEquiv]
    exact h3S

theorem isGMinusOne_of_facts {p : ℕ} (hp : p.Prime) (hcore : GLAPPrimeCore p Y = ⊥) {K B : Subgroup Y}
    (hK : IsComponentOf K ⊤) (hB : IsElemAbelian p B)
    (hinn : ∀ φ : MulAut ↥K, ∃ g : ↥K, φ = MulAut.conj g) (hZ : Subgroup.center ↥K = ⊥)
    (h3 : ¬ p ^ 3 ∣ Nat.card ↥K) (hCG : CFSG.HardMathSupport.Dickson.I271.CentGen p ↥K) :
    Lemma1314.IsGMinusOne p B K := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply isGMinusOne_of_isInGMinusOne
  by_cases h1 : CFSG.Open.pRank p B ≤ 1
  · exact isInGMinusOne_of_pRank_le_one h1
  have h1' : 1 ≤ CFSG.Open.pRank p B := by omega
  by_cases hA : Nat.card (stab B K) ≤ p * Nat.card (cen B K)
  · exact isInGMinusOne_of_card_stab_le hp hB hK h1' hA
  have hA' : p * Nat.card (cen B K) < Nat.card (stab B K) := not_le.1 hA
  have hgen := le_gammaPrimeIn_of_centGen hp hB hinn hZ h3 hCG hA'
  have hL : GLAPComponent p ⊤ K :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_glaPComponent_of_isComponentOf hcore hK
  have hrank : 1 ≤ CFSG.Open.pRank p (stab B K) := by
    have hAel : IsElemAbelian p (stab B K) := elem_mono hB inf_le_left
    obtain ⟨a, ha⟩ := GL83.CompFam.exists_card_eq_pow hAel
    rw [i224_pRank_eq hp hAel ha]
    by_contra h0
    have ha0 : a = 0 := by omega
    rw [ha0, pow_zero] at ha
    have hc : 0 < Nat.card (cen B K) := Nat.card_pos
    have hp1 := hp.one_lt
    nlinarith
  exact input22_4_general hp le_top hB hL hrank hgen

end General

@[expose] def Fi23FiveLayer : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSporType .Fi23 S → ∀ x : S, orderOf x = 5 →
    ∃ Λ : Subgroup S, GLAPComponent 5 (Subgroup.centralizer ({x} : Set S)) Λ ∧
      (∀ H : Subgroup S, GLAPComponent 5 (Subgroup.centralizer ({x} : Set S)) H → H = Λ) ∧
      IsAltType 7 ↥Λ ∧ x ∉ Λ

@[expose] def Input23_24Fi23LocQ : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSporType .Fi23 Y → ∀ A : Subgroup (MulAut Y),
    IsElemAbelian 5 A → Nat.card A = 5 ^ 2 →
      ((⊤ : Subgroup Y) ≤ ⨆ (α : MulAut Y) (_ : α ∈ A) (_ : α ≠ 1),
          GLAPLayer 5 (CFSG.LocalAnalysis.GLTheoremB.MovingAround.fixSub α)) ∧
      ∀ α ∈ A, α ≠ 1 → ∀ J : Subgroup Y,
        GLAPComponent 5 (CFSG.LocalAnalysis.GLTheoremB.MovingAround.fixSub α) J →
          IsAltType 7 (barOf 5 J)

section Loc

theorem fixSub_conj {S : Type} [Group S] (y : S) :
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.fixSub (MulAut.conj y) =
      Subgroup.centralizer ({y} : Set S) := by
  ext k
  rw [CFSG.LocalAnalysis.GLTheoremB.MovingAround.mem_fixSub, MulAut.conj_apply,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc k * y = y * k * y⁻¹ * y := by rw [h]
      _ = y * k := by group
  · intro h
    calc y * k * y⁻¹ = k * y * y⁻¹ := by rw [h]
      _ = k := by group

theorem card_of_isAltType_seven {S : Type*} [Group S] (h : IsAltType 7 S) : Nat.card S = 2520 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem isAltType_barOf_of_isAltType {S : Type} [Group S] {Λ : Subgroup S} (h : IsAltType 7 ↥Λ) :
    IsAltType 7 (barOf 5 Λ) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard := card_of_isAltType_seven h
  haveI : Finite ↥Λ := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥Λ := e.isSimpleGroup
  have hcore : GLAPPrimeCore 5 ↥Λ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 5 ↥Λ) with h0 | h0
    · exact h0
    · exfalso
      have hcop : Nat.Coprime 5 (Nat.card (GLAPPrimeCore 5 ↥Λ)) := CFSG.pPrimeCore_coprime_card
      rw [h0, Subgroup.card_top, hcard] at hcop
      norm_num at hcop
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).trans e⟩

theorem glaPLayer_eq_of_unique {S : Type} [Group S] {p : ℕ} {X Λ : Subgroup S}
    (hΛ : GLAPComponent p X Λ) (hu : ∀ H : Subgroup S, GLAPComponent p X H → H = Λ) :
    GLAPLayer p X = Λ :=
  le_antisymm (sSup_le fun H hH => (hu H hH).le) (le_sSup hΛ)

theorem map_glaPLayer_centralizer {S : Type} [Group S] [Finite S] (p : ℕ) (n y : S) :
    (GLAPLayer p (Subgroup.centralizer ({y} : Set S))).map (MulAut.conj n).toMonoidHom =
      GLAPLayer p (Subgroup.centralizer ({n * y * n⁻¹} : Set S)) := by
  have hc : GLBConj n⁻¹ (Subgroup.centralizer ({y} : Set S)) =
      Subgroup.centralizer ({n * y * n⁻¹} : Set S) := by
    ext x
    rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc x * (n * y * n⁻¹) = n * ((n⁻¹ * x * n⁻¹⁻¹) * y) * n⁻¹ := by group
        _ = n * (y * (n⁻¹ * x * n⁻¹⁻¹)) * n⁻¹ := by rw [h]
        _ = n * y * n⁻¹ * x := by group
    · intro h
      calc n⁻¹ * x * n⁻¹⁻¹ * y = n⁻¹ * (x * (n * y * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * y * n⁻¹) * x) * n := by rw [h]
        _ = y * (n⁻¹ * x * n⁻¹⁻¹) := by group
  have h1 := CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.glaPLayer_gLBConj p n⁻¹
    (Subgroup.centralizer ({y} : Set S))
  rw [hc] at h1
  rw [h1]
  unfold GLBConj
  rw [inv_inv]

theorem normalizer_le_normalizer_layers {S : Type} [Group S] [Finite S] (p : ℕ) (P : Subgroup S) :
    Subgroup.normalizer (P : Set S) ≤ Subgroup.normalizer (((⨆ (y : S) (_ : y ∈ P) (_ : y ≠ 1),
      GLAPLayer p (Subgroup.centralizer ({y} : Set S))) : Subgroup S) : Set S) := by
  set X : Subgroup S := ⨆ (y : S) (_ : y ∈ P) (_ : y ≠ 1),
    GLAPLayer p (Subgroup.centralizer ({y} : Set S)) with hX
  have key : ∀ n ∈ Subgroup.normalizer (P : Set S), X.map (MulAut.conj n).toMonoidHom ≤ X := by
    intro n hn
    rw [hX, Subgroup.map_iSup]
    refine iSup_le fun y => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hy => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hy1 => ?_
    rw [map_glaPLayer_centralizer]
    have hy' : n * y * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hn y).1 hy
    have hy1' : n * y * n⁻¹ ≠ 1 := by
      intro h
      apply hy1
      calc y = n⁻¹ * (n * y * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
    exact le_iSup₂_of_le (n * y * n⁻¹) hy' (le_iSup_of_le hy1' le_rfl)
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (key n hn) fun x hx => ?_
  have h2 := key n⁻¹ (inv_mem hn)
  refine ⟨n⁻¹ * x * n, h2 ⟨x, hx, ?_⟩, ?_⟩
  · show n⁻¹ * x * n⁻¹⁻¹ = n⁻¹ * x * n
    rw [inv_inv]
  · show n * (n⁻¹ * x * n) * n⁻¹ = x
    group

theorem factorization_eq_one_of {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h1 : p ∣ n)
    (h2 : ¬ p ^ 2 ∣ n) : n.factorization p = 1 := by
  have a := (hp.pow_dvd_iff_le_factorization hn).1 (by rw [pow_one]; exact h1)
  have b : ¬ 2 ≤ n.factorization p := fun h => h2 ((hp.pow_dvd_iff_le_factorization hn).2 h)
  omega

theorem centralizer_le_normalizer_sup {S : Type} [Group S] [Finite S] (h3 : ¬ 5 ^ 3 ∣ Nat.card S)
    {P : Subgroup S} (hPel : IsElemAbelian 5 P) (hPcard : Nat.card P = 5 ^ 2) {y : S} (hyP : y ∈ P)
    (hy1 : y ≠ 1) {Λ : Subgroup S} (hΛC : Λ ≤ Subgroup.centralizer ({y} : Set S))
    (hΛn : Subgroup.centralizer ({y} : Set S) ≤ Subgroup.normalizer (Λ : Set S))
    (hΛcard : Nat.card Λ = 2520) (hyΛ : y ∉ Λ) :
    Subgroup.centralizer ({y} : Set S) ≤ Subgroup.normalizer (P : Set S) ⊔ Λ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set C : Subgroup S := Subgroup.centralizer ({y} : Set S) with hCdef
  have hPC : P ≤ C := fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (elem_comm hPel hq hyP)
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hCfac : (Nat.card C).factorization 5 = 2 := by
    have hdvd : 5 ^ 2 ∣ Nat.card C := hPcard ▸ Subgroup.card_dvd_of_le hPC
    have hndvd : ¬ 5 ^ 3 ∣ Nat.card C := fun h => h3 (h.trans (Subgroup.card_subgroup_dvd_card C))
    have a := (Nat.prime_five.pow_dvd_iff_le_factorization hC0).1 hdvd
    have b : ¬ 3 ≤ (Nat.card C).factorization 5 := fun h =>
      hndvd ((Nat.prime_five.pow_dvd_iff_le_factorization hC0).2 h)
    omega
  have hP'card : Nat.card (P.subgroupOf C) = 5 ^ (Nat.card C).factorization 5 := by
    rw [hCfac, ← hPcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  set SX : Sylow 5 ↥C := Sylow.ofCard (P.subgroupOf C) hP'card with hSX
  have hSXc : (SX : Subgroup ↥C) = P.subgroupOf C := Sylow.coe_ofCard _ _
  set F : Subgroup ↥C := Λ.subgroupOf C with hF
  haveI hFn : F.Normal := ⟨fun n hn c => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hΛn c.2) n).1 hn⟩
  have hFcard : Nat.card F = 2520 := by
    rw [← hΛcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛC).toEquiv
  set T : Sylow 5 ↥F := CFSG.QuasiDihedralFusion.sylowInfNormal SX F with hT
  have hTcard : Nat.card T = 5 := by
    rw [Sylow.card_eq_multiplicity, hFcard,
      factorization_eq_one_of Nat.prime_five (by norm_num) (by norm_num) (by norm_num), pow_one]
  have hTne : (T : Subgroup ↥F) ≠ ⊥ := by
    intro h0
    have h1 : Nat.card (T : Subgroup ↥F) = 1 := by rw [h0, Subgroup.card_bot]
    have h2 : Nat.card (T : Subgroup ↥F) = 5 := hTcard
    omega
  obtain ⟨⟨w₁, hw₁T⟩, hw₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hTne
  have hw₁1' : w₁ ≠ 1 := fun h => hw₁1 (Subtype.ext h)
  have hw₁SX : (w₁ : ↥C) ∈ (SX : Subgroup ↥C) := by
    have := hw₁T
    rw [hT, CFSG.QuasiDihedralFusion.sylowInfNormal_coe, Subgroup.mem_subgroupOf] at this
    exact this
  set wY : S := ((w₁ : ↥C) : S) with hwY
  have hwP : wY ∈ P := by
    have := hw₁SX
    rw [hSXc, Subgroup.mem_subgroupOf] at this
    exact this
  have hwΛ : wY ∈ Λ := Subgroup.mem_subgroupOf.1 w₁.2
  have hwY1 : wY ≠ 1 := by
    intro h
    apply hw₁1'
    exact Subtype.ext (Subtype.ext h)
  have hyord : orderOf y = 5 := orderOf_eq_prime (hPel.2 y hyP) hy1
  have hwz : wY ∉ Subgroup.zpowers y := by
    intro hz
    have hmem : wY ∈ Λ ⊓ Subgroup.zpowers y := ⟨hwΛ, hz⟩
    rw [GL83.CompFam.inf_zpowers_eq_bot hyord hyΛ, Subgroup.mem_bot] at hmem
    exact hwY1 hmem
  have hyw : y * wY = wY * y := elem_comm hPel hyP hwP
  have hPeq : Subgroup.closure ({y, wY} : Set S) = P := by
    have hle : Subgroup.closure ({y, wY} : Set S) ≤ P :=
      (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hyP, Set.singleton_subset_iff.2 hwP⟩)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hPcard, CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.card_closure_pair_eq_sq
      (hPel.2 y hyP) (hPel.2 wY hwP) hyw hy1 hwz]
  have hfr := Sylow.normalizer_sup_eq_top (CFSG.QuasiDihedralFusion.sylowInfNormal SX F)
  rw [CFSG.QuasiDihedralFusion.sylowInfNormal_coe, Subgroup.subgroupOf_map_subtype] at hfr
  have hnorm : ∀ n : ↥C, n ∈ Subgroup.normalizer
      ((((SX : Subgroup ↥C) ⊓ F : Subgroup ↥C)) : Set ↥C) →
      (n : S) ∈ Subgroup.normalizer (P : Set S) := by
    intro n hn
    have hwC : (w₁ : ↥C) ∈ (SX : Subgroup ↥C) ⊓ F := ⟨hw₁SX, w₁.2⟩
    have h1 := ((Subgroup.mem_normalizer_iff.1 hn) (w₁ : ↥C)).1 hwC
    have h2 : (n : S) * wY * (n : S)⁻¹ ∈ P := by
      have h3' : n * (w₁ : ↥C) * n⁻¹ ∈ (SX : Subgroup ↥C) := (Subgroup.mem_inf.1 h1).1
      rw [hSXc, Subgroup.mem_subgroupOf] at h3'
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h3'
    have hny : (n : S) * y * (n : S)⁻¹ = y := by
      have := Subgroup.mem_centralizer_singleton_iff.1 n.2
      rw [this]
      group
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : P.map (MulAut.conj (n : S)).toMonoidHom ≤ P := by
      rw [← hPeq, MonoidHom.map_closure, Set.image_pair]
      refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩)
      · show (MulAut.conj (n : S)) y ∈ Subgroup.closure ({y, wY} : Set S)
        rw [MulAut.conj_apply, hny]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · show (MulAut.conj (n : S)) wY ∈ Subgroup.closure ({y, wY} : Set S)
        rw [MulAut.conj_apply, hPeq]
        exact h2
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj (n : S)).injective]
  intro c hc
  have hcT : (⟨c, hc⟩ : ↥C) ∈ Subgroup.normalizer
      ((((SX : Subgroup ↥C) ⊓ F : Subgroup ↥C)) : Set ↥C) ⊔ F := by
    rw [hfr]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem C.subtype hcT
  rw [Subgroup.map_sup] at hmap
  have hle : (Subgroup.normalizer ((((SX : Subgroup ↥C) ⊓ F : Subgroup ↥C)) : Set ↥C)).map C.subtype ⊔
      F.map C.subtype ≤ Subgroup.normalizer (P : Set S) ⊔ Λ := by
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      exact hnorm n hn
    · rw [hF, Subgroup.subgroupOf_map_subtype]
      exact inf_le_left
  exact hle hmap

theorem top_le_layers {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (h3 : ¬ 5 ^ 3 ∣ Nat.card S) (hCG : CFSG.HardMathSupport.Dickson.I271.CentGen 5 S)
    (hF : ∀ x : S, orderOf x = 5 →
      ∃ Λ : Subgroup S, GLAPComponent 5 (Subgroup.centralizer ({x} : Set S)) Λ ∧
        (∀ H : Subgroup S, GLAPComponent 5 (Subgroup.centralizer ({x} : Set S)) H → H = Λ) ∧
        IsAltType 7 ↥Λ ∧ x ∉ Λ)
    {P : Subgroup S} (hPel : IsElemAbelian 5 P) (hPcard : Nat.card P = 5 ^ 2) :
    (⊤ : Subgroup S) ≤ ⨆ (y : S) (_ : y ∈ P) (_ : y ≠ 1),
      GLAPLayer 5 (Subgroup.centralizer ({y} : Set S)) := by
  set X : Subgroup S := ⨆ (y : S) (_ : y ∈ P) (_ : y ≠ 1),
    GLAPLayer 5 (Subgroup.centralizer ({y} : Set S)) with hX
  have hord : ∀ y ∈ P, y ≠ 1 → orderOf y = 5 := fun y hy hy1 => orderOf_eq_prime (hPel.2 y hy) hy1
  have hCle : ∀ y ∈ P, y ≠ 1 →
      Subgroup.centralizer ({y} : Set S) ≤ Subgroup.normalizer (P : Set S) ⊔ X := by
    intro y hy hy1
    obtain ⟨Λ, hΛc, hu, h7, hyΛ⟩ := hF y (hord y hy hy1)
    have hlayer := glaPLayer_eq_of_unique hΛc hu
    have hΛn : Subgroup.centralizer ({y} : Set S) ≤ Subgroup.normalizer (Λ : Set S) := by
      rw [← hlayer]
      exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.le_normalizer_glaPLayer 5 _
    refine (centralizer_le_normalizer_sup h3 hPel hPcard hy hy1 hΛc.1 hΛn
      (card_of_isAltType_seven h7) hyΛ).trans (sup_le_sup_left ?_ _)
    rw [← hlayer]
    exact le_iSup₂_of_le y hy (le_iSup_of_le hy1 le_rfl)
  have htop : (⊤ : Subgroup S) ≤ Subgroup.normalizer (P : Set S) ⊔ X := by
    rw [← hCG P hPel hPcard, Subgroup.closure_le]
    rintro σ ⟨y, hy, hy1, hσy⟩
    exact hCle y hy hy1 (Subgroup.mem_centralizer_singleton_iff.2 hσy)
  have hnorm : Subgroup.normalizer (X : Set S) = ⊤ :=
    eq_top_iff.2 (htop.trans (sup_le (normalizer_le_normalizer_layers 5 P) (Subgroup.le_normalizer)))
  haveI hXn : X.Normal := Subgroup.normalizer_eq_top_iff.1 hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with h0 | h0
  · exfalso
    have hPne : P ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hPcard
      norm_num at hPcard
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hPne
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨Λ, hΛc, hu, h7, -⟩ := hF y (hord y hy hy1')
    have hle : Λ ≤ X := by
      rw [← glaPLayer_eq_of_unique hΛc hu]
      exact le_iSup₂_of_le y hy (le_iSup_of_le hy1' le_rfl)
    rw [h0, le_bot_iff] at hle
    have hc := card_of_isAltType_seven h7
    rw [hle, Subgroup.card_bot] at hc
    norm_num at hc
  · exact h0.ge

theorem locQ_of_facts {Y' : Type} [Group Y'] [Finite Y']
    (hinn : ∀ φ : MulAut Y', ∃ g : Y', φ = MulAut.conj g) (hZ : Subgroup.center Y' = ⊥)
    (hs : IsSimpleGroup Y') (h3 : ¬ 5 ^ 3 ∣ Nat.card Y')
    (hCG : CFSG.HardMathSupport.Dickson.I271.CentGen 5 Y')
    (hF : ∀ x : Y', orderOf x = 5 →
      ∃ Λ : Subgroup Y', GLAPComponent 5 (Subgroup.centralizer ({x} : Set Y')) Λ ∧
        (∀ H : Subgroup Y', GLAPComponent 5 (Subgroup.centralizer ({x} : Set Y')) H → H = Λ) ∧
        IsAltType 7 ↥Λ ∧ x ∉ Λ)
    {A : Subgroup (MulAut Y')} (hAel : IsElemAbelian 5 A) (hAcard : Nat.card A = 5 ^ 2) :
    ((⊤ : Subgroup Y') ≤ ⨆ (α : MulAut Y') (_ : α ∈ A) (_ : α ≠ 1),
        GLAPLayer 5 (CFSG.LocalAnalysis.GLTheoremB.MovingAround.fixSub α)) ∧
      ∀ α ∈ A, α ≠ 1 → ∀ J : Subgroup Y',
        GLAPComponent 5 (CFSG.LocalAnalysis.GLTheoremB.MovingAround.fixSub α) J →
          IsAltType 7 (barOf 5 J) := by
  have hinj : Function.Injective (MulAut.conj : Y' →* MulAut Y') := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ Subgroup.center Y' := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := congrArg (fun φ : MulAut Y' => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hZ] at hgZ
    exact Subgroup.mem_bot.1 hgZ
  set P : Subgroup Y' := A.comap (MulAut.conj : Y' →* MulAut Y') with hPdef
  have hPmap : P.map (MulAut.conj : Y' →* MulAut Y') = A := by
    rw [hPdef, Subgroup.map_comap_eq]
    refine inf_eq_right.2 ?_
    intro φ _
    obtain ⟨g, rfl⟩ := hinn φ
    exact ⟨g, rfl⟩
  have hPcard : Nat.card P = 5 ^ 2 := by
    rw [← hAcard, ← hPmap, Subgroup.card_map_of_injective hinj]
  have hPel : IsElemAbelian 5 P := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have hx : MulAut.conj (x : Y') ∈ A := x.2
      have hy : MulAut.conj (y : Y') ∈ A := y.2
      simp only [Subgroup.coe_mul, map_mul]
      exact elem_comm hAel hx hy
    · rw [map_pow, hAel.2 _ hx, map_one]
  refine ⟨(top_le_layers hs h3 hCG hF hPel hPcard).trans
    (iSup₂_le fun y hy => iSup_le fun hy1 => ?_), ?_⟩
  · have hα : MulAut.conj y ∈ A := hy
    have hα1 : MulAut.conj y ≠ 1 := fun h => hy1 (hinj (h.trans (map_one _).symm))
    rw [← fixSub_conj]
    exact le_iSup₂_of_le (MulAut.conj y) hα (le_iSup_of_le hα1 le_rfl)
  · intro α hα hα1 J hJ
    obtain ⟨y, rfl⟩ := hinn α
    have hy1 : y ≠ 1 := fun h => hα1 (by rw [h, map_one])
    have hyord : orderOf y = 5 :=
      orderOf_eq_prime (hinj (by rw [map_pow, hAel.2 _ hα, map_one])) hy1
    rw [fixSub_conj] at hJ
    obtain ⟨Λ, -, hu, h7, -⟩ := hF y hyord
    rw [hu J hJ]
    exact isAltType_barOf_of_isAltType h7

theorem input23_24Fi23Loc_of_Q (h : Input23_24Fi23LocQ) : Lemma1314c.Input23_24Fi23Loc := by
  intro G _ _ C L U hL hsp hUC hUel hUcard hUN hfaith
  have hp : Nat.Prime 5 := Nat.prime_five
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hfaith' : ∀ x ∈ U, x ∈ centBar 5 ⊤ L → x = 1 := by
    intro x hxU hx
    have hxc : x ∈ centBar 5 U L := Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, hxU⟩
    rw [hfaith] at hxc
    exact Subgroup.mem_bot.1 hxc
  have hAel : IsElemAbelian 5 (autBar 5 U L) := Lemma123.isElemAbelian_autBar hUel
  have hAcard : Nat.card (autBar 5 U L) = 5 ^ 2 := by
    rw [Inputs123b.card_autBar hUN hfaith', hUcard]
  obtain ⟨hgen, hty⟩ := h (barOf 5 L) hsp (autBar 5 U L) hAel hAcard
  refine ⟨?_, ?_⟩
  · set W : Subgroup G := ⨆ z ∈ U, ⨆ (_ : z ≠ 1), ⨆ (H : Subgroup G)
      (_ : GLAPComponent 5 (C ⊓ Subgroup.centralizer ({z} : Set G)) H ∧ H ≤ L), H with hW
    have hWL : W ≤ L := iSup₂_le fun z _ => iSup_le fun _ => iSup₂_le fun H hH => hH.2
    have hlayer : ∀ z ∈ U, z ≠ 1 → GLAPLayer 5 (L ⊓ Subgroup.centralizer ({z} : Set G)) ≤ W := by
      intro z hz hz1
      refine sSup_le fun J hJ => ?_
      have hsn : CFSG.Open.IsSubnormal (L ⊓ Subgroup.centralizer ({z} : Set G))
          (C ⊓ Subgroup.centralizer ({z} : Set G)) := hL.2.1.inf _
      have hJ' : GLAPComponent 5 (C ⊓ Subgroup.centralizer ({z} : Set G)) J :=
        CFSG.LocalAnalysis.GLTheoremA.glaPComponent_of_isSubnormal' hp hsn hJ
      have hJL : J ≤ L := hJ.1.trans inf_le_left
      exact le_iSup₂_of_le z hz (le_iSup_of_le hz1 (le_iSup₂_of_le J ⟨hJ', hJL⟩ le_rfl))
    have htop : barX 5 L W = ⊤ := by
      refine eq_top_iff.2 (hgen.trans (iSup_le fun α => iSup_le fun hα => iSup_le fun hα1 => ?_))
      obtain ⟨b, hbB, hbN, hb1, rfl⟩ := Inputs123b.exists_of_mem_autBar hUN hα hα1
      exact (Inputs123b.layer_fixSub_le hp hbN (hUel.2 b hbB)).trans
        (barX_mono (hlayer b hbB hb1))
    have hcov := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barX_eq_top_iff 5 hWL).1 htop
    exact ((CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barX_eq_iff_cov hp hL.2.1 hWL).2
      hcov).ge
  · intro z hz hz1 H hH hHL
    have hzN : z ∈ Subgroup.normalizer (L : Set G) := hUN hz
    have hz5 : z ^ 5 = 1 := hUel.2 z hz
    have hHL' : GLAPComponent 5 (L ⊓ Subgroup.centralizer ({z} : Set G)) H :=
      glaPComponent_of_le hp hH (le_inf hHL (hH.1.trans inf_le_right)) (inf_le_inf_right _ hL.1)
    obtain ⟨Q, hQ, ⟨eH⟩⟩ := Inputs123b.exists_component_image hp hzN hz5 hHL'
    have hα : barAut 5 L ⟨z, hzN⟩ ∈ autBar 5 U L := by
      rw [Inputs123b.autBar_eq_range hUN]
      exact ⟨⟨z, hz⟩, rfl⟩
    have hα1 : barAut 5 L ⟨z, hzN⟩ ≠ 1 := by
      intro h0
      apply hz1
      have hinj := Inputs123b.injective_barAut hUN hfaith'
      have h1 : ((barAut 5 L).comp (Subgroup.inclusion hUN)) ⟨z, hz⟩ = 1 := h0
      exact congrArg Subtype.val (hinj (h1.trans (map_one _).symm))
    exact Lemma1314.isAltType_of_equiv eH (hty _ hα hα1 Q hQ)

end Loc

section Fi23


theorem fi23_facts {Y' : Type} [Group Y'] (hsp : IsSporType .Fi23 Y') :
    (∀ φ : MulAut Y', ∃ g : Y', φ = MulAut.conj g) ∧ Subgroup.center Y' = ⊥ ∧
      ¬ 5 ^ 3 ∣ Nat.card Y' ∧ CFSG.HardMathSupport.Dickson.I271.CentGen 5 Y' ∧ IsSimpleGroup Y' := by
  obtain ⟨e₁⟩ := hsp
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
  have e₂ : Y' ≃* Blueprint.NativeSporadic.Fi23 := e₁.trans b.symm
  have e : Y' ≃* ↥CFSG.Sporadic.Fi23.J := e₂.trans CFSG.Sporadic.Fi23.fi23EquivJ
  have hJ := CFSG.Sporadic.Fi23.fi23_complete CFSG.Fischer.polarFacts CFSG.Fischer.hyperovalFacts
    (CFSG.Sporadic.Fi22.fi22Facts CFSG.Fischer.polarFacts CFSG.Fischer.hyperovalFacts)
  have h3 : ¬ 5 ^ 3 ∣ Nat.card ↥CFSG.Sporadic.Fi23.J := by
    rw [CFSG.Sporadic.Fi23.card_J]
    norm_num
  obtain ⟨h1, h2, h3', h4⟩ := @model_facts_of_equiv Y' ↥CFSG.Sporadic.Fi23.J _
    CFSG.Sporadic.Fi23.J.toGroup e 5 hJ CFSG.Sporadic.Fi23.center_J h3
    CFSG.HardMathSupport.Dickson.I271.centGen_fi23J_five
  exact ⟨h1, h2, h3', h4, @MulEquiv.isSimpleGroup Y' _ ↥CFSG.Sporadic.Fi23.J
    CFSG.Sporadic.Fi23.J.toGroup CFSG.Sporadic.Fi23.isSimpleGroup_J e⟩

theorem input23_24Fi23_holds : Lemma1314.Input23_24Fi23 := by
  intro Y _ _ hcore K B hK hB hsp
  obtain ⟨hinn, hZ, h3, hCG, -⟩ := fi23_facts hsp
  exact isGMinusOne_of_facts Nat.prime_five hcore hK hB hinn hZ h3 hCG

theorem input23_24Fi23LocQ_of_layer (hF : Fi23FiveLayer) : Input23_24Fi23LocQ := by
  intro Y _ _ hsp A hAel hAcard
  obtain ⟨hinn, hZ, h3, hCG, hs⟩ := fi23_facts hsp
  exact locQ_of_facts hinn hZ hs h3 hCG (hF Y hsp) hAel hAcard

theorem input23_24Fi23Loc_of_layer (hF : Fi23FiveLayer) : Lemma1314c.Input23_24Fi23Loc :=
  input23_24Fi23Loc_of_Q (input23_24Fi23LocQ_of_layer hF)

end Fi23

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324

end
