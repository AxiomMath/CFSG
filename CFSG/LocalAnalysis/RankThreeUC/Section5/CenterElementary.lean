module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.SpecialCommutatorCenterEqCentralizerAndExponentPowerTwo
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
import all CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Local.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CenterElementary

open CFSG.LocalAnalysis.RankThreeUC.Section5

open scoped commutatorElement

theorem center_sq_eq_one {X : Type} [Group X] [Finite X] (S : Subgroup X)
    (hS : IsPGroup 2 S) (hsp : Section3.CoprimeSpecialGroups.IsSpecialPGroup S) :
    ∀ z ∈ Subgroup.center S, z ^ 2 = 1 := by
  obtain ⟨h1, h2⟩ := hsp
  have hinj : Function.Injective S.subtype := Subtype.val_injective
  have hcc : commutator S = Subgroup.center S := by
    have := h1.symm
    exact (Subgroup.map_injective hinj this)
  have hfc : frattini S = Subgroup.center S := Subgroup.map_injective hinj h2.symm
  have hsq : ∀ x : S, x ^ 2 ∈ Subgroup.center S := fun x => by
    rw [← hfc]
    haveI : Fact (IsPGroup 2 S) := ⟨hS⟩
    exact CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) x
  have hcomm : ∀ x y : S, ⁅x, y⁆ ^ 2 = 1 := fun x y => by
    have hz : ⁅x, y⁆ ∈ Subgroup.center S := by
      rw [← hcc]; exact Subgroup.commutator_mem_commutator trivial trivial
    have := Section3.CoprimeSpecialGroups.comm_pow_pow hz 2 1
    rw [pow_one, mul_one] at this
    rw [← this]
    exact commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp (hsq x)) y).symm
  intro z hz
  rw [← hcc, commutator, Subgroup.commutator_def] at hz
  induction hz using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a, _, b, _, rfl⟩ := hg
    exact hcomm a b
  | one => simp
  | mul a b ha hb iha ihb =>
    have hbc : b ∈ Subgroup.center S := by
      rw [← hcc]; exact (Subgroup.closure_le _).mpr (fun g hg => by
        obtain ⟨a, _, b, _, rfl⟩ := hg; exact Subgroup.commutator_mem_commutator trivial trivial) hb
    have : a * b = b * a := (Subgroup.mem_center_iff.mp hbc a)
    rw [pow_two, mul_assoc, ← mul_assoc b, ← this, mul_assoc a, ← mul_assoc, ← pow_two, iha, one_mul, ← pow_two, ihb]
  | inv a ha iha =>
    rw [inv_pow, iha, inv_one]

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hcCounterexample58 : ExtraspecialBinaryActionCounterexample G p P T B e ρ) :
    CFSG.Open.IsElemAbelian 2 (Local.Z (P := P) (T := T) (B := B)) := by
  have hsp := (special_commutator_center_eq_centralizer_and_exponent_power_two hcCounterexample58).1.1
  have hS := SstarQuotientFaithful.isPGroup hcCounterexample58
  have hsq := center_sq_eq_one _ hS hsp
  refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha, ha'⟩ := u.2
    obtain ⟨b, hb, hb'⟩ := v.2
    apply Subtype.ext
    show (u : MulAut P) * v = v * u
    have := (Subgroup.mem_center_iff.mp ha b)
    rw [← ha', ← hb']
    exact congrArg Subtype.val this.symm
  · rintro x ⟨a, ha, rfl⟩
    have := congrArg Subtype.val (hsq a ha)
    simpa using this

end CFSG.LocalAnalysis.RankThreeUC.Section5.CenterElementary
