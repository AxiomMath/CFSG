module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DL28Bnd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamOutBCD
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04BCRes
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265D

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.LocalAnalysis.GLTheoremA (rk2DiagIndex)

theorem s265d_catalogIs_of_equiv {X Y : Type} [Group X] [Group Y] {Q : TauCeti.CFSGIndex → Prop}
    (e : X ≃* Y) (h : catalogIs X Q) : catalogIs Y Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

private theorem congr_conj' {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (s : X) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  show e (MulAut.conj s (e.symm y)) = MulAut.conj (e s) y
  simp [MulAut.conj_apply]

private theorem psl2_inner_card_le {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) [NeZero (p : K)]
    {E : Subgroup (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))} (hE : IsElemAbelian p E)
    (hin : E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) : Nat.card E ≤ p := by
  have hE' : CFSG.IsElementaryAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).2 hE
  obtain ⟨A', hA'el, hA'c⟩ := CFSG.RankThree.PartOne.K133.exists_elemAb_card_eq_of_le_inner
    (CFSG.GorensteinWalter.psl2_center_eq_bot K) hE' hin
  have hle := CFSG.RankThree.PartOne.K133.psl2_elemAb_card_le hp hp2 A' hA'el
  rw [hA'c] at hle
  exact hle

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_noninner_of_l28 {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL 3 S B T x D K) (hL : catalogIs (PSimple 3 K) tyL28) :
    ∃ β ∈ B, ∃ hβ : β ∈ Subgroup.normalizer (K : Set Ω), β ∉ D ∧
      chevAut 3 K ⟨β, hβ⟩ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 K) := by
  have cfg := h.cfg
  obtain ⟨hDB, -, hDcard, -, -, hKcomp, -⟩ := cfg.std
  have hNA := h.nlAct (three_dvd_card_of_l28 hL)
  have hBN : B ≤ Subgroup.normalizer (K : Set Ω) := hNA.norm
  by_contra hcon
  push Not at hcon
  obtain ⟨F, _, _, hF, ⟨ePSL⟩⟩ := s265d_l28_psl_model hL
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3)
    (by rw [← Nat.card_eq_fintype_card]; exact hF)
  haveI : NeZero ((3 : ℕ) : F) :=
    ⟨fun h3 => by have := (CharP.cast_eq_zero_iff F 2 3).1 h3; omega⟩
  let φ : ↥B →* MulAut (PSimple 3 K) := (chevAut 3 K).comp (Subgroup.inclusion hBN)
  have hφ1 : ∀ b : ↥B, φ b = 1 ↔ (b : Ω) ∈ D := fun b => hNA.ker b b.2 (hBN b.2)
  have hker : φ.ker = D.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, hφ1, Subgroup.mem_subgroupOf]
  have hkc : Nat.card φ.ker = 3 ^ 2 := by
    rw [hker, ← hDcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range φ
  have hr9 : 9 ≤ Nat.card φ.range := by
    have h81 : 3 ^ 4 ≤ Nat.card φ.ker * Nat.card φ.range := hmul ▸ cfg.big
    rw [hkc] at h81
    omega
  have hinn : ∀ b : ↥B, φ b ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 K) := by
    intro b
    by_cases hbD : (b : Ω) ∈ D
    · rw [(hφ1 b).2 hbD]
      exact Subgroup.one_mem _
    · exact hcon b b.2 (hBN b.2) hbD
  let Ψ : ↥B →* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    (MulAut.congr ePSL).toMonoidHom.comp φ
  have hcomm : ∀ a c : ↥B, a * c = c * a := fun a c => cfg.elem.1.is_comm.comm a c
  have hXel : IsElemAbelian 3 Ψ.range := by
    refine ⟨⟨⟨fun a c => ?_⟩⟩, ?_⟩
    · obtain ⟨_, b, rfl⟩ := a
      obtain ⟨_, c, rfl⟩ := c
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul, hcomm])
    · rintro _ ⟨b, rfl⟩
      have hb : b ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact cfg.elem.2 _ b.2)
      rw [← map_pow, hb, map_one]
  have hXcard : Nat.card Ψ.range = Nat.card φ.range := by
    rw [MonoidHom.range_comp, Subgroup.card_map_of_injective
      (f := (MulAut.congr ePSL).toMonoidHom) (MulAut.congr ePSL).injective]
  have hXin : Ψ.range ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨s, hs⟩ := hinn b
    refine ⟨ePSL s, ?_⟩
    show MulAut.conj (ePSL s) = MulAut.congr ePSL (φ b)
    rw [← hs, congr_conj']
  have := psl2_inner_card_le Nat.prime_three (by norm_num) hXel hXin
  omega

theorem s265d_chevSimple_of_l28 {R : Type} [Group R] (h : catalogIs R tyL28) : IsChevSimple 2 R := by
  left
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  refine ⟨i, ?_, ⟨e⟩⟩
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | A r q =>
      rcases r with _ | _ | r
      · exact hi.elim
      · have hq : q.card = 8 := hi
        obtain ⟨h1, -⟩ := s265d_pp_eq Nat.prime_two (s := 3) (by norm_num) (hq.trans (by norm_num))
        simpa [onLie, TauCeti.LieTypeIndex.characteristic_A] using h1
      · exact hi.elim
    | _ => exact hi.elim

theorem cfg_of_qsnl {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) :
    S171.Cfg Ω 3 B x S := by
  have cfg := h.cfg
  have hSN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 cfg.normal) ▸ Subgroup.mem_top g
  refine S171.cfg_mk Nat.prime_three (by norm_num) cfg.elem cfg.big cfg.xB cfg.x1 hSN cfg.quasi
    cfg.chev ?_ ?_ ?_
  · exact Subgroup.mem_centralizer_iff.2 fun s _ => cfg.xcen s
  · intro S' hS' hp
    exact cfg.cyc S' (fun g hg => centMod_of_mem_centralizer (hS' hg)) hp
  · exact (innDiagOn_iff cfg.comp cfg.quasi).2 cfg.inn

theorem maxG_of_qsnl {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) :
    S171.MaxG 3 B := fun _ _ hE hU2 hU hEU =>
  (card_le_pow_glaTwoLocalRank Nat.prime_three hE hU hU2 hEU).trans h.cfg.rank

section Marks


private theorem tag_A1_aux {lab : LargeEvenLabel} {R : Type} [Group R]
    (hL : CFSG.Blueprint.LieModel R .PSL 2 2 3) (hM : MarkedModel lab R)
    (hder : lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der) :
    lab.tag = .A ∧ lab.rank = 1 := by
  obtain ⟨tg, r, nn⟩ := lab
  dsimp only at hder ⊢
  have hchar : markChar ⟨tg, r, nn⟩ = 2 := by
    cases tg <;> simp_all [markChar]
  have hM' : CFSG.Blueprint.LieModel R (markTag ⟨tg, r, nn⟩) (markRank ⟨tg, r, nn⟩) 2
      (markDeg ⟨tg, r, nn⟩) := by
    unfold MarkedModel at hM
    rwa [hchar] at hM
  obtain ⟨e1, e2, e3⟩ := CFSG.SeitzReduction.RankOne.sl2EvenTypeDet R 3 _ _ _ hL hM'.admissible hM'
  cases tg
  · simp only [markTag, markRank, markDeg] at e1 e2 e3
    exact ⟨rfl, by omega⟩
  all_goals first
    | exact absurd rfl hder.1
    | exact absurd rfl hder.2.1
    | exact absurd rfl hder.2.2
    | (exfalso; simp only [markTag, markRank, markDeg] at e1 e2 e3; first | (cases e1) | omega)
    | (exfalso; simp only [markTag, markRank, markDeg] at e1 e2 e3; split_ifs at e1 e2 e3 <;> first | omega | (cases e1))

private theorem not_dvd_rk2DiagIndex_of_l28 {lab : LargeEvenLabel} {R : Type} [Group R]
    (hL : CFSG.Blueprint.LieModel R .PSL 2 2 3) (hM : MarkedModel lab R) :
    ¬ 3 ∣ rk2DiagIndex lab := by
  by_cases hd : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der
  · have h1 : rk2DiagIndex lab = 1 := by
      rcases hd with h | h | h <;> simp [rk2DiagIndex, h]
    rw [h1]
    norm_num
  · push Not at hd
    obtain ⟨htag, hrank⟩ := tag_A1_aux hL hM hd
    have h1 : rk2DiagIndex lab = Nat.gcd (lab.rank + 1) (2 ^ lab.n - 1) := by
      simp [rk2DiagIndex, htag]
    rw [h1, hrank]
    intro h3
    have := h3.trans (Nat.gcd_dvd_left (1 + 1) (2 ^ lab.n - 1))
    omega


theorem l28_not_innDiagOn {Ω : Type} [Group Ω] [Finite Ω] {X K : Subgroup Ω}
    (hK : GLAPComponent 3 X K) (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hL : catalogIs (PSimple 3 K) tyL28) {β : Ω} (hβ : β ∈ Subgroup.normalizer (K : Set Ω))
    (hβ3 : β ^ 3 = 1)
    (hni : chevAut 3 K ⟨β, hβ⟩ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 K)) :
    ¬ InnDiagOn 3 (Subgroup.zpowers β) K := by
  intro hid
  have hmark : InnerDiagMarking (Subgroup.zpowers β) K := (innDiagOn_iff hK hKq).2 hid
  obtain ⟨-, lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_markedModel hmark
  haveI : Nontrivial (PSimple 3 K) := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [s265d_card_l28 hL]
    norm_num
  obtain ⟨eK⟩ := SF.nonempty_centerQuot_equiv_pSimple (p := 3) hKq
  have hpd : ¬ 3 ∣ rk2DiagIndex lab := by
    obtain ⟨R₀, _, I₀, F₀, hs₀, hna₀, θ₀, hP₀, hM₀⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    have hR₀ : catalogIs R₀ tyL28 := s265d_catalogIs_of_equiv (eK.symm.trans θ₀) hL
    exact not_dvd_rk2DiagIndex_of_l28 (Or.inl ⟨by decide, s265d_l28_stated hR₀⟩) hM₀
  have hstep : GLARawDatum lab (fun R _ I F =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃* R,
          (Subgroup.zpowers β ≤ Subgroup.normalizer (K : Set Ω) ∧
            ∀ a ∈ Subgroup.zpowers β, ∃ φ ∈ I, LargeEvenInduces θ
              (fun l l' => (l' : Ω) = a⁻¹ * l * a) φ) ∧
          CFSG.StandardType.MarkedModel lab R) ∧
      (∀ E : Subgroup (MulAut R),
        E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) →
          IsPGroup 3 E → E ≤ (MulAut.conj : R →* MulAut R).range)) :=
    CFSG.LocalAnalysis.GLTheoremA.rk2_pSubgroup_le_inn' (lab := lab) hlab Nat.prime_three
      (by norm_num) hpd (fun R _ I F =>
        (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃* R,
            (Subgroup.zpowers β ≤ Subgroup.normalizer (K : Set Ω) ∧
              ∀ a ∈ Subgroup.zpowers β, ∃ φ ∈ I, LargeEvenInduces θ
                (fun l l' => (l' : Ω) = a⁻¹ * l * a) φ) ∧
            CFSG.StandardType.MarkedModel lab R)) hraw
  obtain ⟨R, hR, I, F, hQ, hIinn⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hstep
  obtain ⟨hs, hna, θ, hP, hM⟩ := hQ
  obtain ⟨φ, hφI, hφind⟩ := hP.2 β (Subgroup.mem_zpowers β)
  have hφpow : φ ^ 3 = 1 := T171Sh.largeEvenInduces_pow_eq_one hβ hφind hβ3
  have hφp : IsPGroup 3 (Subgroup.zpowers φ) := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf φ)
      (orderOf_dvd_of_pow_eq_one hφpow) with h1 | hp'
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hp', pow_one])
  have hle : Subgroup.zpowers φ ≤
      Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) :=
    Subgroup.zpowers_le_of_mem (Subgroup.subset_closure (Set.mem_union_left _ hφI))
  have hinner : φ ∈ Set.range (MulAut.conj : R →* MulAut R) :=
    hIinn (Subgroup.zpowers φ) hle hφp (Subgroup.mem_zpowers φ)
  obtain ⟨r, hr⟩ := hinner
  have hind : InducesInnerMod 3 K β :=
    T171Sh.inducesInnerMod_of_marked_conj (R := R) (θ := θ) (r := r) hβ
      (Group.isPerfect_def.mpr hKq.1) (by rw [hr]; exact hφind)
  exact hni ((chevAut_mem_inner_iff Nat.prime_three hK hβ).2 hind)


end Marks

end CFSG.LocalAnalysis.GLTheoremA.S265D

end
