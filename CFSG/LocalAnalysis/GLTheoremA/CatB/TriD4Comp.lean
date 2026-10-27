module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoF4
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocalBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Orb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvB
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS5
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Local
public import Certificates.Data.U62Rank.Check
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA
import Certificates.Certificate9530

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

local notation "fixC" => CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup

private theorem exp_eq_twelve_d4 {m N : ℕ} {Z : ℕ → Prop} (hP : Profile m N Z)
    (hm : m = 174182400) : N = 12 := by
  obtain ⟨r, hr, hmr⟩ := hP.two
  exact eq_of_two_pow_mul_odd hr (by decide : Odd 42525)
    ((hmr.symm.trans hm).trans (by norm_num : (174182400 : ℕ) = 2 ^ 12 * 42525))

private theorem le_four_d4 {n f : ℕ} (hf : 1 ≤ f) (hN : f * (n * (n + 1) / 2) = 12) :
    n ≤ 4 := by
  by_contra hlt
  push Not at hlt
  have h15 : 15 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
  have := Nat.le_mul_of_pos_left (n * (n + 1) / 2) hf
  omega

private theorem ordA_ne_d4 {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    ordA n (2 ^ f) ≠ 174182400 := by
  intro h
  have hN := exp_eq_twelve_d4 (profile_ordA hn hf) h
  have hn4 := le_four_d4 hf hN
  interval_cases n
  · obtain rfl : f = 12 := by omega
    exact absurd h (by decide +kernel)
  · obtain rfl : f = 4 := by omega
    exact absurd h (by decide +kernel)
  · obtain rfl : f = 2 := by omega
    exact absurd h (by decide +kernel)
  · omega

private theorem ordTwistedA_ne_d4 {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) :
    ordTwistedA n (2 ^ f) ≠ 174182400 := by
  intro h
  have hN := exp_eq_twelve_d4 (profile_ordTwistedA hn hf) h
  have hn4 := le_four_d4 hf hN
  interval_cases n
  · obtain rfl : f = 4 := by omega
    exact absurd h (by decide +kernel)
  · obtain rfl : f = 2 := by omega
    exact absurd h (by decide +kernel)
  · omega

private theorem ordBC_ne_d4 {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) :
    ordBC n (2 ^ f) ≠ 174182400 := by
  intro h
  have hN := exp_eq_twelve_d4 (profile_ordBC hf) h
  have hn3 : n ≤ 3 := by
    by_contra hlt
    have h16 : 4 * 4 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.le_mul_of_pos_left (n * n) hf
    omega
  interval_cases n
  · obtain rfl : f = 3 := by omega
    exact absurd h (by decide +kernel)
  · omega

private theorem card_isD4two_cat {T : Type} [Group T] (h : catalogIs T S9.isD4two) :
    Nat.card T = 174182400 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | D r q =>
      rcases r with _ | _ | _ | _ | _ | r <;> try exact False.elim hi
      have hq : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hi
      have hp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (by
        rw [← hq]
        exact dvd_pow_self q.p q.exponent_pos.ne')
      have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD _ q hv e
      rw [hp] at hm hq
      rw [(card_statedClassicalModel_two hm).2.2.2.1 rfl, hq]
      decide +kernel
    | _ => exact False.elim hi
  | _ => exact False.elim hi

@[expose] def ComponentsNoD4 {S : Type} [Group S] (β : MulAut S) : Prop :=
  ∀ K : Subgroup S, IsComponentOf K (fixC β) → Nat.card (↥K ⧸ Subgroup.center ↥K) ≠ 174182400

theorem ComponentsNoD4.of_congr {S G : Type} [Group S] [Group G] (e : S ≃* G) {β : MulAut S}
    (h : ComponentsNoD4 (MulAut.congr e β)) : ComponentsNoD4 β := by
  intro K hK
  have hfix : fixC (MulAut.congr e β) = (fixC β).map (e : S →* G) := by
    ext x
    rw [mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [mem_fixSubgroup]
    show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hmapc : IsComponentOf (K.map (e : S →* G)) (fixC (MulAut.congr e β)) := by
    rw [hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK
  obtain ⟨g⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv
    (K.equivMapOfInjective (e : S →* G) e.injective)
  rw [Nat.card_congr g.toEquiv]
  exact h _ hmapc

theorem false_of_componentsNoD4 {S : Type} [Group S] [Finite S] {α : MulAut S}
    (hlayer : PerfectInLayer α) (hno : ComponentsNoD4 α) {J : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup α) J) (hT : catalogIs (PSimple 3 J) S9.isD4two) :
    False := by
  have hfix : fixSubgroup α = fixC α := Subgroup.ext fun _ => Iff.rfl
  rw [hfix] at hJ
  have hJle := hlayer J hJ.1 (glaPComponent_perfect hJ)
  have hJc := (glaPComponent_isComponent_of_le_layer hJ hJle).1
  have hcard := card_isD4two_cat hT
  haveI : Nontrivial (PSimple 3 J) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  obtain ⟨φ⟩ := CFSG.LocalAnalysis.GLTheoremA.I1431C2.nonempty_centerQuot_equiv_psimple hJc.2.2
    inferInstance
  exact hno J hJc ((Nat.card_congr φ.toEquiv).trans hcard)

theorem card_centerQuot_sl_ne {m k : ℕ} {E : Type} [Field E] [Finite E] (hm : 2 ≤ m)
    (hk : 1 ≤ k) (hE : Nat.card E = 2 ^ k) (hm4 : m = 2 → 4 ≤ Nat.card E) {X : Type}
    [Group X] (eX : X ≃* Matrix.SpecialLinearGroup (Fin m) E) :
    Nat.card (X ⧸ Subgroup.center X) ≠ 174182400 := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl m eX
  have h23 : ∀ c, c = 2 ∨ c = 3 → (m, 2 ^ k) ≠ (2, c) := fun c hc h => by
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    have := hm4 rfl
    omega
  have hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL m 2 k :=
    ⟨⟨Nat.prime_two, hk, hm, h23 2 (Or.inl rfl), h23 3 (Or.inr rfl)⟩, E, inferInstance,
      inferInstance, hE, ⟨e⟩⟩
  rw [(card_statedClassicalModel_two hmodel).1 rfl]
  exact ordA_ne_d4 (by omega) hk

theorem card_centerQuot_su_ne {m k q' : ℕ} {E : Type} [Field E] [Finite E] (hm : 3 ≤ m)
    (hk : 1 ≤ k) (hq' : q' = 2 ^ k) (hmq : (m, q') ≠ (3, 2)) (hE : Nat.card E = q' ^ 2)
    {X : Type} [Group X] (eX : X ≃* ↥(StatedSU m q' E)) :
    Nat.card (X ⧸ Subgroup.center X) ≠ 174182400 := by
  subst hq'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hZ⟩ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := k) hE hm hmq
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv eX
  have hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU m 2 k :=
    ⟨⟨Nat.prime_two, hk, hm, hmq⟩, E, inferInstance, inferInstance, hE,
      ⟨e.trans (QuotientGroup.quotientMulEquivOfEq hZ)⟩⟩
  rw [(card_statedClassicalModel_two hmodel).2.1 rfl]
  exact ordTwistedA_ne_d4 (by omega) hk

theorem card_centerQuot_sp_ne {s k : ℕ} {K : Type} [Field K] [Finite K] (hs : 2 ≤ s)
    (hk : 1 ≤ k) (hK : Nat.card K = 2 ^ k) (hne : ¬(s = 2 ∧ Nat.card K = 2)) {X : Type}
    [Group X] (eX : X ≃* StatedSp s K) : Nat.card (X ⧸ Subgroup.center X) ≠ 174182400 := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp hs hne
    (CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK) eX
  have h2 : (s, 2 ^ k) ≠ (2, 2) := fun h => by
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    exact hne ⟨rfl, hK.trans h2⟩
  have hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSp s 2 k :=
    ⟨⟨Nat.prime_two, hk, hs, h2⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  rw [(card_statedClassicalModel_two hmodel).2.2.1 rfl]
  exact ordBC_ne_d4 hs hk

theorem card_centerQuot_spFourTwo_ne {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {X : Type} [Group X] (eX : X ≃* ↥(commutator (StatedSp 2 K))) :
    Nat.card (X ⧸ Subgroup.center X) ≠ 174182400 := by
  intro h
  have h720 : Nat.card (StatedSp 2 K) = 720 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hK]
    norm_num
  have hd : Nat.card (X ⧸ Subgroup.center X) ∣ 720 := by
    rw [← h720]
    refine (Subgroup.card_quotient_dvd_card _).trans ?_
    rw [Nat.card_congr eX.toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [h] at hd
  exact absurd (Nat.le_of_dvd (by norm_num) hd) (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end
