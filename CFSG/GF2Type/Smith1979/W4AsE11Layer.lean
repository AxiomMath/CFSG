module

public import CFSG.GF2Type.Smith1979.W4AsE11Iso
public import CFSG.LargeExtraspecial.S111SJMain
public import CFSG.LargeExtraspecial.S11MaParity

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module CFSG.Open CFSG.ComponentClassification CFSG.GH74.Uniqueness.Bender
  CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S11
open scoped MatrixGroups

@[expose] def L28NoSmallFaithful : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ⧸ center K ≃* PSL(2, GaloisField 2 3)) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (ρ : K →* (V ≃ₗ[ZMod 2] V)), Function.Injective ρ → 6 ≤ finrank (ZMod 2) V

@[expose] def L216NoPlusEmbedding : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ⧸ center K ≃* PSL(2, GaloisField 2 4)) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (Q : QuadraticForm (ZMod 2) V), Q.polarBilin.Nondegenerate →
      finrank (ZMod 2) V = 8 →
      (∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 4 ∧ ∀ v ∈ W, Q v = 0) →
      ∀ ρ : K →* (V ≃ₗ[ZMod 2] V), (∀ k v, Q (ρ k v) = Q v) → ¬ Function.Injective ρ

@[expose] def J1NoFaithfulEight : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ⧸ center K ≃* goldschmidtJ1) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V],
      finrank (ZMod 2) V = 8 → ∀ ρ : K →* (V ≃ₗ[ZMod 2] V), ¬ Function.Injective ρ

@[expose] def ReeNoFaithfulEight : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (m : ℕ), 1 ≤ m →
    Nat.card (K ⧸ center K) = ordRee (3 ^ (2 * m + 1)) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V],
      finrank (ZMod 2) V = 8 → ∀ ρ : K →* (V ≃ₗ[ZMod 2] V), ¬ Function.Injective ρ

structure LayerSurvivorsW4 : Prop where
  l28 : L28NoSmallFaithful
  l216 : L216NoPlusEmbedding
  j1 : J1NoFaithfulEight
  ree : ReeNoFaithfulEight

section Layer

variable {X : Type} [Group X] {E O L : Subgroup X} {w : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : X →* (V ≃ₗ[ZMod 2] V)} {a : V}

theorem false_of_nonBender_layer_w4 [Finite X] [FiniteDimensional (ZMod 2) V] [E.Normal]
    (C : LayerCfg E O L w ρ a) (hw : w = 4) (hS : LayerSurvivorsW4)
    (h : (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (E ⧸ center E ≃* PSL(2, GaloisField p f))) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card (E ⧸ center E) = ordRee (3 ^ (2 * m + 1))) ∨
      Nonempty (E ⧸ center E ≃* goldschmidtJ1)) : False := by
  have hfr : finrank (ZMod 2) V = 8 := by rw [C.finrank_eq, hw]
  have hinj : Function.Injective (ρ.comp E.subtype) := C.rho_inj.comp Subtype.val_injective
  rcases h with ⟨p, f, hp, hpodd, hf, h5, hmod, ⟨e⟩⟩ | ⟨m, hm, hcard⟩ | hJ
  ·
    have hKcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
    have hfodd : Odd f :=
      ComponentClassification.AschbacherToolkit.Goldschmidt.odd_of_pow_mod_eight hpodd hmod
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    set A' : Subgroup (MulAut (CFSG.GorensteinWalter.PSL2 (GaloisField p f))) :=
      (L.map (barAct E)).map (MulAut.congr e).toMonoidHom with hA'
    have hA'sq : ∀ α ∈ A', α * α = 1 := by
      rintro _ ⟨α, hα, rfl⟩
      rw [← map_mul, C.lam_sq hα, map_one]
    have h4 := ComponentClassification.AschbacherToolkit.Goldschmidt.card_le_four_of_sq_eq_one
      hKcard hp2 hfodd (by rw [hKcard]; omega) A' hA'sq
    rw [hA', Subgroup.card_map_of_injective (MulAut.congr e).injective] at h4
    have h8 : Nat.card (L.map (barAct E)) = 8 := by
      rw [C.card_lam, hw]
      norm_num
    omega
  · exact hS.ree E m hm hcard V hfr (ρ.comp E.subtype) hinj
  · exact hS.j1 E hJ V hfr (ρ.comp E.subtype) hinj

theorem false_of_bender_layer_w4 [Finite X]
    [FiniteDimensional (ZMod 2) V] [E.Normal] [O.Normal] (C : LayerCfg E O L w ρ a)
    (hw : w = 4) (hS : LayerSurvivorsW4) (Q : QuadraticForm (ZMod 2) V)
    (hQnd : Q.polarBilin.Nondegenerate) (hQρ : ∀ x v, Q (ρ x v) = Q v)
    (hQW : ∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 4 ∧ ∀ v ∈ W, Q v = 0)
    {f i e : ℕ} (hB : BenderType (E ⧸ center E) f i e) : False := by
  subst hw
  obtain ⟨hw2, hw1⟩ := C.width_le hB
  have h2 := hB.two_le
  have hmod : 2 * i * f ≠ 6 → 2 * i * f ≤ 8 := fun h6 => by
    have h := two_mul_le_finrank_of_benderType (ρ.comp E.subtype)
      (C.rho_inj.comp Subtype.val_injective) hB h6
    rw [C.finrank_eq] at h
    omega
  rcases hB.cases' with ⟨hi, he, -⟩ | ⟨hi, -, a', ha', hfa⟩ | ⟨hi, -, -⟩
  ·
    subst hi
    subst he
    have hf3 : 3 ≤ f := by
      have := hw1 (by norm_num)
      omega
    have hf4 : f ≤ 4 := by
      by_contra hcon
      have := hmod (by omega)
      omega
    obtain ⟨eB⟩ : Nonempty (E ⧸ center E ≃* CFSG.Theory.Comparator.PSL2Model f) := by
      cases hB with
      | linear n hn e => exact ⟨e⟩
    by_cases hall : ∀ l ∈ L.map (barAct E), ∃ q, l = MulAut.conj q
    · by_cases hO : O = ⊥
      · exact C.false_of_inner_of_O_eq_bot hB hall hO
      · refine C.false_of_inner_of_O_ne_bot_of_noModule hall hO ?_
        intro Y _ _ _ ρY hρY hYw
        have hf : f = 3 ∨ f = 4 := by omega
        rcases hf with rfl | rfl
        · have := hS.l28 E ⟨eB⟩ Y ρY hρY
          omega
        · have hD := two_mul_le_finrank_of_benderType ρY hρY hB (by norm_num)
          rw [hYw] at hD
          omega
    · push Not at hall
      obtain ⟨l, hl, hl'⟩ := hall
      obtain ⟨-, rfl⟩ := C.eq_four_of_field hB hl fun ⟨g, hg⟩ => hl' g (by
        ext x
        rw [hg, MulAut.conj_apply])
      exact hS.l216 E ⟨eB⟩ V Q hQnd (C.finrank_eq.trans (by norm_num)) hQW (ρ.comp E.subtype)
        (fun k v => hQρ _ v) (C.rho_inj.comp Subtype.val_injective)
  ·
    subst hi
    have := hmod (by omega)
    omega
  ·
    subst hi
    have := hmod (by omega)
    omega

theorem false_of_goldschmidtSimpleType_layer_w4
    [Finite X] [FiniteDimensional (ZMod 2) V] [E.Normal] [O.Normal]
    (C : LayerCfg E O L w ρ a) (hw : w = 4) (hS : LayerSurvivorsW4)
    (Q : QuadraticForm (ZMod 2) V) (hQnd : Q.polarBilin.Nondegenerate)
    (hQρ : ∀ x v, Q (ρ x v) = Q v)
    (hQW : ∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 4 ∧ ∀ v ∈ W, Q v = 0)
    (hG : goldschmidtSimpleType (E ⧸ center E)) : False := by
  have hBen : ∀ _ : CFSG.BenderSuzuki.IsBenderGroup (E ⧸ center E), False := fun hB => by
    obtain ⟨n, i, e, h⟩ := isBenderGroup_iff_exists_benderType.mp hB
    exact false_of_bender_layer_w4 C hw hS Q hQnd hQρ hQW h
  rcases hG with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | h
  · exact hBen (.isPSL2 f (by omega) e)
  · exact hBen (CFSG.CGT.Timmesfeld75.isBenderGroup_of_mulEquiv_sz hn e)
  · exact hBen (CFSG.ComponentClassification.Asc76X.isBenderGroup_of_mulEquiv_psu3 hf e)
  · exact false_of_nonBender_layer_w4 C hw hS h

end Layer

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem eq_one_of_mem_Lbar_of_commute_w4 (hy : Hyp S g) (hirr : ¬ S.IsReducible)
    (hw : S.width = 4)
    (h55 : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 ∧
      CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) ∧
      timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar)
    {x : S.Mbar} (hx : (x : S.O) ∈ S.Lbar g)
    (hxE : ∀ e ∈ timmesfeldLayer S.Mbar, e * x = x * e) : x = 1 := by
  by_contra hx1
  have hx2 : x * x = 1 := Subtype.ext (S4.mul_self_of_mem_Lbar S hy.hyp4.conj_mem hx)
  refine false_of_isolated_w4 hy hirr hw hx (fun h => hx1 (Subtype.ext h)) fun m hm hc => ?_
  have h := conj_eq_of_mem_centralizer (S5.timmesfeldOddCore_normal S.Mbar)
    (Layer.normal S.Mbar) h55.1 h55.2.2 (fun _ hv2 hv => eq_one_of_mem_centralizer_fstar hv2 hv)
    hx2 hxE ⟨m, hm⟩ (Subtype.ext (by simpa using hc))
  simpa using congrArg Subtype.val h

@[expose] def ShultF6ResidualEW4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G),
    Hyp S g → ¬ S.IsReducible → S.width = 4 →
    (∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) →
    ∀ (P : Sylow 2 S.Mbar) (t : S.Mbar), (t : S.O) ∈ S.Lbar g → t ≠ 1 →
      t ∈ (P : Subgroup S.Mbar) → (∀ x ∈ (P : Subgroup S.Mbar), x * t = t * x) →
      IsMulCommutative (wcl t) → wcl t ≤ P →
      (∀ a ∈ wcl t, ∀ x : S.Mbar, x⁻¹ * a * x ∈ (P : Subgroup S.Mbar) → x⁻¹ * a * x ∈ wcl t) →
      GoldschmidtConcl S.Mbar P (wcl t) →
      (Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 ∧ CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) ∧
        timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar) →
      (∃ s ∈ wclSet t, s ≠ t) →
      (¬ ∀ e ∈ timmesfeldLayer S.Mbar, e * t = t * e) →
      False

theorem shultF6ResidualEW4_of (hL : LayerSurvivorsW4) :
    ShultF6ResidualEW4 := by
  intro G _ _ _ S g hy hirr hw hT P t ht ht1 htP htc hab hWP hcl hGo h55 hni hmove
  have := S5.timmesfeldOddCore_normal S.Mbar
  have htK : t ∈ normalClosure (wcl t : Set S.Mbar) :=
    subset_normalClosure (self_mem_wcl t)
  have hEK := le_of_not_commute h55.2.1 htK hmove
  obtain ⟨-, -, hG⟩ := hGo
  have hGT := goldschmidtSimpleType_of_le h55.2.1 hEK hG
  have hLag := hy.isLagrangian_clSub hy.hyp4.conj_mem hy.hyp4.conj_ne
  refine false_of_goldschmidtSimpleType_layer_w4
    (layerCfg_of' hy hirr (by omega) hT h55
      (fun hx hxE => eq_one_of_mem_Lbar_of_commute_w4 hy hirr hw h55 hx hxE))
    hw hL S.q S.q_nondegenerate
    (fun x v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (x : S.O).2 v)
    ⟨S.clSub (S.QG ⊓ S.Qa g), ?_, fun v hv => hLag.1 v hv⟩ hGT
  have h1 := hLag.2
  rw [S.finrank_Qt_eq_two_mul_width, hw] at h1
  omega

end CFSG.GF2Type.Smith1979.W4As
