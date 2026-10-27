module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.Char3Bridge
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Descend
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Outer
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.RankThree.PartTwo.KFacts
open CFSG.HardMathSupport.Dickson.Sec6.I923 (FamOK)

theorem t6char3_fixSubgroup_conj_eq_centralizer {G : Type*} [Group G] (u : G) :
    fixSubgroup (MulAut.conj u) = Subgroup.centralizer ({u} : Set G) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem s1431_false_of_char3_inner_of_index (hKD : KDCharP 3) {P : Type} [Group P] [Finite P]
    {A : Subgroup (MulAut P)} {ψ : MulAut P} {J : Subgroup P} {q : ℕ} (c : S1431Cfg P A ψ J q)
    (hZ : Subgroup.center P = ⊥) (hinn : IsInnerAut ψ) (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1.characteristic = 3) (e : P ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  obtain ⟨x, rfl⟩ := hinn
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv P e.toEquiv
  have h3 : MulAut.conj x ^ 3 = (1 : MulAut P) := c.elemAbelian.2 _ c.mem
  have hx3 : x ^ 3 = 1 := by
    have hc : x ^ 3 ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut P => φ g)
        (show (MulAut.conj (x ^ 3) : MulAut P) = 1 by rw [map_pow]; exact h3)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * x ^ 3 = (x ^ 3 * g * (x ^ 3)⁻¹) * x ^ 3 := by rw [h]
        _ = x ^ 3 * g := by group
    rwa [hZ, Subgroup.mem_bot] at hc
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact c.ne_one (map_one _)
  have hord : orderOf (e x) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hx3 hx1
  have hker : (e : P →* (TauCeti.CFSGIndex.lie d).Group).ker ≤ Subgroup.center P := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le
  have hcomm : ∀ y : P, (e : P →* (TauCeti.CFSGIndex.lie d).Group) (MulAut.conj x y) =
      (MulAut.conj (e x) : MulAut (TauCeti.CFSGIndex.lie d).Group)
        ((e : P →* (TauCeti.CFSGIndex.lie d).Group) y) := fun y => by
    simp [MulAut.conj_apply]
  have hcomp := glaPComponent_map_fixSubgroup (e : P →* (TauCeti.CFSGIndex.lie d).Group) hker
    (MulAut.conj x) (MulAut.conj (e x)) hcomm e.surjective Nat.prime_three c.comp
  rw [t6char3_fixSubgroup_conj_eq_centralizer] at hcomp
  have hle : J.map (e : P →* (TauCeti.CFSGIndex.lie d).Group) ≤
      GLAPLayer 3 (Subgroup.centralizer ({e x} : Set (TauCeti.CFSGIndex.lie d).Group)) :=
    le_sSup hcomp
  rw [hKD d hd (e x) hord, le_bot_iff] at hle
  exact glaPComponent_ne_bot' c.comp
    ((Subgroup.map_eq_bot_iff_of_injective J
      (f := (e : P →* (TauCeti.CFSGIndex.lie d).Group)) e.injective).1 hle)

theorem t6char3_card_stated_psl_two_ge {F : Type} [Field F] [Finite F] (hF : 64 ≤ Nat.card F) :
    131040 ≤ Nat.card (StatedProj (StatedSL 2 F)) := by
  rw [← Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj 2 F).toEquiv,
    OrderReductions.LinearOrders.card_projectiveSpecialLinear F 2 (by norm_num)]
  simp only [Finset.Icc_self, Finset.prod_singleton]
  generalize Nat.card F = q at hF ⊢
  have h1 : 2 * (2 - 1) / 2 = 1 := by norm_num
  rw [h1, pow_one]
  have hg : Nat.gcd 2 (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hgpos : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [Nat.le_div_iff_mul_le hgpos]
  have h4095 : 4095 ≤ q ^ 2 - 1 := by
    have : 64 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hF 2
    omega
  calc 131040 * Nat.gcd 2 (q - 1) ≤ 131040 * 2 := Nat.mul_le_mul_left _ hg
    _ = 64 * 4095 := by norm_num
    _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hF h4095

theorem s1431_false_of_card_lt {P : Type} [Group P] [Finite P] {A : Subgroup (MulAut P)}
    {ψ : MulAut P} {J : Subgroup P} {q : ℕ} (c : S1431Cfg P A ψ J q) (hq : 64 ≤ q)
    (hP : Nat.card P < 131040) : False := by
  obtain ⟨F, hF, hFin, hFcard, ⟨g⟩⟩ := c.typeL2
  have h1 : Nat.card (StatedProj (StatedSL 2 F)) ≤ Nat.card P := by
    rw [← Nat.card_congr g.toEquiv]
    calc Nat.card (barOf 3 J ⧸ Subgroup.center (barOf 3 J))
        ≤ Nat.card (barOf 3 J) :=
          Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      _ ≤ Nat.card J := Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      _ ≤ Nat.card P := Subgroup.card_le_card_group J
  have h2 := t6char3_card_stated_psl_two_ge (F := F) (by rw [hFcard]; exact hq)
  omega

private theorem t6char3_lieOrd_psl_two_nine :
    EvenSmallLie.CatalogOrders.lieOrd .PSL 2 (3 ^ 2) = 360 := by decide

private theorem t6char3_lieOrd_psp_two_three :
    EvenSmallLie.CatalogOrders.lieOrd .PSp 2 (3 ^ 1) = 25920 := by decide

theorem s1431_false_of_dup_char3 {P : Type} [Group P] [Finite P] {A : Subgroup (MulAut P)}
    {ψ : MulAut P} {J : Subgroup P} {q : ℕ} (c : S1431Cfg P A ψ J q) (hq : 64 ≤ q)
    {t : StatedLieTag} {n f : ℕ} (hm : StatedClassicalModel P t n 3 f)
    (hdup : (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSp ∧ n = 2 ∧ f = 1)) : False := by
  rcases hdup with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have h := EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hm
    rw [t6char3_lieOrd_psl_two_nine] at h
    exact s1431_false_of_card_lt c hq (by omega)
  · have h := EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hm
    rw [t6char3_lieOrd_psp_two_three] at h
    exact s1431_false_of_card_lt c hq (by omega)

theorem s1431_false_of_char3_inner_of_bridges (hKD : KDCharP 3) {P : Type} [Group P] [Finite P]
    {A : Subgroup (MulAut P)} {ψ : MulAut P} {J : Subgroup P} {q : ℕ} (c : S1431Cfg P A ψ J q)
    (hq : 64 ≤ q) {t : StatedLieTag} {n f : ℕ}
    (hB : t ∈ classicalTags ∨ CFSG.TauCetiBridge.TypewiseBridges)
    (hm : CFSG.Blueprint.LieModel P t n 3 f) (hZ : Subgroup.center P = ⊥) (hinn : IsInnerAut ψ) :
    False := by
  by_cases hdup : (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSp ∧ n = 2 ∧ f = 1)
  · refine s1431_false_of_dup_char3 c hq (hm.statedClassicalModel_of_ne_zero ?_) hdup
    rcases hdup with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> norm_num
  · have hnd := not_tauCetiDuplicate_three_iff.2 (not_or.1 hdup)
    obtain ⟨d, hd, ⟨e⟩⟩ : ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 3 ∧
        Nonempty (P ≃* (TauCeti.CFSGIndex.lie d).Group) := by
      rcases hB with ht | hB
      · exact exists_tauCeti_index_of_statedClassicalModel (hm.statedClassicalModel ht) hnd
      · exact exists_tauCeti_index_of_blueprint_lieModel_odd hB hm (by norm_num) hnd
    exact s1431_false_of_char3_inner_of_index hKD c hZ hinn d hd e

theorem t6char3_center_quotient_eq_bot {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) :
    Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
  obtain ⟨a, b, hab⟩ := CFSG.HardMathSupport.Dickson.Sec6.I923.exists_not_comm_of_quasisimple hY
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Y ⧸ Subgroup.center Y))
    with h | h
  · exact h
  · exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm hab

theorem y1431_false_of_char3_of_bridges (hKD : KDCharP 3) {V : InndiagVocab} {Y : Type}
    [Group Y] [Finite Y] {Â : Subgroup (MulAut Y)} {ξ : MulAut Y} {J : Subgroup Y} {q q0 : ℕ}
    (c : Y1431Cfg V Y Â ξ J q) (hq0 : 4 ≤ q0) (hqq : q = q0 ^ 3) {P : Type} [Group P]
    (e : (Y ⧸ Subgroup.center Y) ≃* P) (hξ : IsInnerAut (MulAut.congr e (centerDescend Y ξ)))
    {t : StatedLieTag} {n f : ℕ} (hB : t ∈ classicalTags ∨ CFSG.TauCetiBridge.TypewiseBridges)
    (hm : CFSG.Blueprint.LieModel P t n 3 f) : False := by
  haveI : Finite P := Finite.of_equiv _ e.toEquiv
  have hq : 64 ≤ q := by
    rw [hqq]
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q0 ^ 3 := Nat.pow_le_pow_left hq0 3
  have hZ : Subgroup.center P = ⊥ := by
    rw [← Subgroup.map_center_eq e, t6char3_center_quotient_eq_bot c.quasisimple,
      Subgroup.map_bot]
  exact s1431_false_of_char3_inner_of_bridges hKD (c.descend e) hq hB hm hZ hξ

theorem y1431NoCfgAt_char3_of_bridges (hKD : KDCharP 3) {Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hB : (∀ t n p f, Fam t n p f → t ∈ classicalTags) ∨ CFSG.TauCetiBridge.TypewiseBridges)
    (hp3 : ∀ t n p f, Fam t n p f → p = 3)
    (hOK : ∀ (P : Type) [Group P] [Finite P] (t : StatedLieTag) (n p f : ℕ),
      StatedLieAdmissible t n p f → t ≠ .Tits → Fam t n p f → CFSG.Blueprint.LieModel P t n p f →
        FamOK P) : Y1431NoCfgAt Fam := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain rfl := hp3 t n p f hF
  refine y1431_false_of_char3_of_bridges hKD c hq0 hqq (MulEquiv.refl _)
    (c.inner_of_famOK hq0 hqq (MulEquiv.refl _) (hOK _ t n 3 f hadm ht hF hm))
    (hB.imp (fun h => h t n 3 f hF) id) hm

end CFSG.HardMathSupport.Dickson.Sec6.I1431
