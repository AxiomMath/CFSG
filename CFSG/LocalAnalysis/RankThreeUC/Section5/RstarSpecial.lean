module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.SpecialCommutatorCenterEqCentralizerAndExponentPowerTwo
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
import all CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.LocalAnalysis.RankThreeUC.Section5.RstarNontrivial
public import CFSG.LocalAnalysis.RankThreeUC.Section5.QuotientJoinFaithful

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.RstarSpecial

open CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.Local

open scoped commutatorElement

theorem frattini_map_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (frattini X).map e.toMonoidHom = frattini Y := by
  exact (Subgroup.map_equiv_eq_comap_symm e _).trans
    ((MulEquiv.comapSubgroup e.symm).map_radical)

theorem special_map {X Y : Type} [Group X] [Group Y] (f : X →* Y) (hf : Function.Injective f)
    (E : Subgroup X) (hE : Section3.CoprimeSpecialGroups.IsSpecialPGroup E) :
    Section3.CoprimeSpecialGroups.IsSpecialPGroup (E.map f) := by
  let e : E ≃* E.map f := Subgroup.equivMapOfInjective E f hf
  have hc : (Subgroup.center E).map e.toMonoidHom = Subgroup.center (E.map f) :=
    Subgroup.map_center_eq e
  have hcomm : (commutator E).map e.toMonoidHom = commutator (E.map f) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top_of_surjective _ e.surjective]
  have hfr := frattini_map_equiv e
  have hcomp : (E.map f).subtype.comp e.toMonoidHom = f.comp E.subtype := by
    ext x; rfl
  have key : ∀ C : Subgroup E, ((C.map e.toMonoidHom).map (E.map f).subtype) =
      (C.map E.subtype).map f := by
    intro C
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  unfold Section3.CoprimeSpecialGroups.IsSpecialPGroup at hE ⊢
  obtain ⟨h1, h2⟩ := hE
  rw [← hc, ← hcomm, ← hfr, key, key, key, h1]
  exact ⟨rfl, by rw [← h2, ← h1]⟩

theorem «structure» {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {q : ℕ} (hq : q.Prime) {A : Subgroup G}
    (hAB : A ≤ B) (hA : Nat.card A = q) :
    Section3.CoprimeSpecialGroups.IsSpecialPGroup (R P T B A) ∧ ¬ IsMulCommutative (R P T B A) ∧
      (commutator (R P T B A)).map (R P T B A).subtype ≤ Z P T B := by
  haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hc.oddPrimeClassTwoAction.setting.odd (by decide)
  have hqp : q ≠ p := PrimeActionFixedFree.q_ne_p hc hq hAB hA
  have hq2 : q ≠ 2 := PrimeActionFixedFree.q_ne_two hc hAB hA
  set K' : Subgroup (MulAut ↥P) := Sstar P T B ⊔ Bstar P A with hK'
  have hRle : R P T B A ≤ K' := (RstarCoprime.R_le hc hAB).trans le_sup_left
  have hBle : Bstar P A ≤ K' := le_sup_right
  have hinj := QuotientJoinFaithful.injective hc hq hAB hA
  have hR0 := RstarNontrivial.ne_bot hc hq hAB hA
  have hRp := RstarCoprime.isPGroup hc hAB
  have hgen := RstarCoprime.generated hc hq hAB hA
  set D : Subgroup K' := (Bstar P A).subgroupOf K' with hD
  set E : Subgroup K' := (R P T B A).subgroupOf K' with hE
  have hEmap : E.map K'.subtype = R P T B A := by
    rw [hE, Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.mpr hRle
  have hDmap : D.map K'.subtype = Bstar P A := by
    rw [hD, Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.mpr hBle
  have hDcard : Nat.card D = q := by
    rw [← PrimeActionFixedFree.card_image hc hq hAB hA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv
  have hCV : (⨅ d ∈ D, LinearMap.ker ((sigma p P).comp K'.subtype d - LinearMap.id)) =
      (⊥ : Submodule (ZMod p) (W P)) := by
    have hfix := PrimeActionFixedFree.fixedSpace_eq_bot hc hq hAB hA
    rw [eq_bot_iff, ← hfix]
    intro v hv
    rw [BinaryRepresentations.mem_fixedSpace_iff]
    intro d hd
    have hdD : (⟨d, hBle hd⟩ : K') ∈ D := hd
    have h1 := (Submodule.mem_iInf _).1 hv ⟨d, hBle hd⟩
    have h2 := (Submodule.mem_iInf _).1 h1 hdD
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h2
    exact h2
  have hE1 : E ≠ ⊥ := by
    intro h
    apply hR0
    rw [← hEmap, h, Subgroup.map_bot]
  have hEq : IsPGroup 2 E := hRp.comap_of_injective K'.subtype Subtype.coe_injective
  obtain ⟨n, hn⟩ := hEq.exists_card_eq
  have hEF : (Nat.card E : ZMod p) ≠ 0 := by
    rw [hn]; push_cast
    refine pow_ne_zero _ ?_
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
    have h2 := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this
    exact hp2 h2
  have hrF : (q : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff q p).1 h
    exact hqp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hq).1 this).symm
  have hDE : ⁅D, E⁆ = E := by
    apply Subgroup.map_injective (f := K'.subtype) Subtype.coe_injective
    rw [Subgroup.map_commutator, hEmap, hDmap, Subgroup.commutator_comm]
    exact hgen
  have hρ : Function.Injective ((sigma p P).comp K'.subtype) := hinj
  have hmain := CFSG.GroupTheory.CoprimeActionSupport.FixedFreePrimeGeneratedPGroupSpecial.special_and_center
    ((sigma p P).comp K'.subtype) hρ Nat.prime_two hq (Ne.symm hq2) D hDcard hCV E hE1 hEq hEF hrF hDE
  have hnon := CFSG.GroupTheory.CoprimeActionSupport.FixedFreePrimeGeneratedPGroupSpecial.nonabelian
    ((sigma p P).comp K'.subtype) hρ Nat.prime_two hq (Ne.symm hq2) D hDcard hCV E hE1 hEq hEF hrF hDE
  have hsp := special_map K'.subtype Subtype.coe_injective E hmain.1
  rw [hEmap] at hsp
  refine ⟨hsp, ?_, ?_⟩
  · intro hcomm
    apply hnon
    refine ⟨⟨fun x y => ?_⟩⟩
    have hx : ((x : K') : MulAut ↥P) ∈ R P T B A := x.2
    have hy : ((y : K') : MulAut ↥P) ∈ R P T B A := y.2
    have := hcomm.is_comm.comm ⟨((x : K') : MulAut ↥P), hx⟩ ⟨((y : K') : MulAut ↥P), hy⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : R P T B A => ((z : MulAut ↥P))) this
  · have hSle : R P T B A ≤ Sstar P T B := RstarCoprime.R_le hc hAB
    have h513 := (special_commutator_center_eq_centralizer_and_exponent_power_two hc).1.1.1
    rw [Subgroup.map_subtype_commutator]
    calc ⁅R P T B A, R P T B A⁆ ≤ ⁅Sstar P T B, Sstar P T B⁆ := Subgroup.commutator_mono hSle hSle
      _ = (commutator (Sstar P T B)).map (Sstar P T B).subtype :=
          (Subgroup.map_subtype_commutator _).symm
      _ = (Subgroup.center (Sstar P T B)).map (Sstar P T B).subtype := h513.symm
      _ = Z P T B := rfl

end CFSG.LocalAnalysis.RankThreeUC.Section5.RstarSpecial
