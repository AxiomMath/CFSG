module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Five

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Dickson.I271.TabCo1 (CompGood)

variable {Good : ∀ (T : Type) [Group T], Prop}

@[expose] def GRow (Good : ∀ (T : Type) [Group T], Prop) (s : TauCeti.SporadicName) (p : ℕ) :
    Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent p (fixSubgroup β) J → Good (PSimple p J)

theorem grow_of_model
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (h : ∀ k : Q, orderOf k = p → CompGood (Good := Good) p k) : GRow Good s p := by
  intro S _ _ ⟨e⟩ hp hp2 β hβ hβ1 K hK
  let φ : S ≃* Q := e.trans b.symm
  haveI : IsSimpleGroup S := (MulEquiv.isSimpleGroup_congr φ).2 inferInstance
  have hncS : ∃ a c : S, a * c ≠ c * a := by
    obtain ⟨a, c, hac⟩ := hnc
    refine ⟨φ.symm a, φ.symm c, fun h' => hac ?_⟩
    have := congrArg φ h'
    simpa using this
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h' | h'
    · exact h'
    · obtain ⟨a, c, hac⟩ := hncS
      exact absurd ((Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top c)) a) hac
  have hout := hOut S inferInstance hncS s ⟨e⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, rfl, hxp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hcen hout β hβ
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hβ1 (map_one MulAut.conj)
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  rw [KDSpor.fixSubgroup_conj_eq] at hK
  have hk : orderOf (φ x) = p := by rw [MulEquiv.orderOf_eq, hxo]
  have := CFSG.HardMathSupport.Dickson.I271.TabCo1.CompGood.of_mulEquiv hGood hp φ.symm (h _ hk)
  rw [MulEquiv.symm_apply_apply] at this
  exact this K hK

theorem compGood_of_shapeRkAt {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Rk : ∀ (T : Type) [Group T], Prop} {k : Q}
    (h : CFSG.HardMathSupport.Dickson.I271.ShapeRkAt p Good Rk k) :
    CompGood (Good := Good) p k := by
  intro I hI
  rcases h with hc | ⟨J, -, huniq, hg, -⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hg

theorem compGood_of_centShape {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q) {k : Q} (hk : orderOf k = p) :
    CompGood (Good := Good) p k := by
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; exact hp.one_lt.ne' hk.symm
  intro I hI
  rcases h k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k) with hc | ⟨J, -, huniq, hg⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hg

theorem compGood_dvd_of_card_dvd {p N : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q] {k : Q}
    (hk : orderOf k = p) (hC : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ p * N) :
    CompGood (Good := fun T _ => Nat.card T ∣ N) p k := fun I hI =>
  Nat.dvd_of_mul_dvd_mul_left hp.pos
    ((CFSG.LocalAnalysis.GLTheoremA.I1416Rows.prime_mul_card_pSimple_dvd_cent hp hk hI.1).trans hC)

theorem altRow_of_grow {m : ℕ} (hm : 5 ≤ m) {s : TauCeti.SporadicName}
    (hG : ∀ (T : Type) [Group T], Good T → Nonempty (T ≃* alternatingGroup (Fin m)) → False)
    (h : GRow Good s 3) : AltRow m s := fun S _ _ he β hβ hβ1 J hJ hA =>
  hG _ (h S he Nat.prime_three (by norm_num) β hβ hβ1 J hJ) (pSimple_equiv_of_isAltPType hm hA)

theorem nineRow_of_grow {s : TauCeti.SporadicName}
    (hG : ∀ (T : Type) [Group T], Good T → Nonempty (T ≃* alternatingGroup (Fin 9)) → False)
    (h : GRow Good s 3) : NineRow s := fun S _ _ he β hβ hβ1 J hJ hA =>
  hG _ (h S he Nat.prime_three (by norm_num) β hβ hβ1 J hJ) hA

theorem not_equiv_alt_of_card {T : Type} [Group T] {m : ℕ} (hm : 2 ≤ m)
    (h : Nat.card T ≠ m.factorial / 2) : Nonempty (T ≃* alternatingGroup (Fin m)) → False :=
  fun ⟨e⟩ => h ((Nat.card_congr e.toEquiv).trans
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt m hm))

end CFSG.LocalAnalysis.GLTheoremA.SporAltRows
