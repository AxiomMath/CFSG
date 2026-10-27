module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Representations.CoprimePrimeAutFixedConjugacyClasses
public import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
import CFSG.FeitThompson.OddOrder.CoprimePlaneFixedDerivedWitness
import CFSG.FeitThompson.OddOrder.PSubgroupInSigmaCoreOfMaximal
import CFSG.FeitThompson.OddOrder.SimpleSolvableNormalizerProper
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable
import CFSG.FeitThompson.Foundations.AbelianSolvable

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson.Prep05 Subgroup

universe u

variable {G : Type*} [Group G]

theorem map_autFixedSubgroup_conjOnNormalized {H A : Subgroup G}
    (hAn : A ≤ normalizer (H : Set G)) (a : ↥A) :
    (autFixedSubgroup (conjOnNormalized H hAn a)).map H.subtype =
      centralizerIn H (zpowers (a : G)) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.coe_subtype, mem_autFixedSubgroup, centralizerIn_eq,
    Subgroup.mem_inf, zpowers_eq_closure, Subgroup.centralizer_closure,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    have h : (a : G) * (z : G) * (a : G)⁻¹ = (z : G) := by
      rw [← conjOnNormalized_apply_coe hAn a z, hz]
    calc (z : G) * (a : G) = ((a : G) * z * (a : G)⁻¹) * a := by rw [h]
      _ = (a : G) * z := by group
  · rintro ⟨hyH, hcomm⟩
    refine ⟨⟨y, hyH⟩, Subtype.ext ?_, rfl⟩
    rw [conjOnNormalized_apply_coe]
    calc (a : G) * y * (a : G)⁻¹ = ((y : G) * a) * (a : G)⁻¹ := by rw [← hcomm]
      _ = y := by group

theorem exists_mem_orderOf_eq_not_centralizerIn_le_commutator [Finite G] {p : ℕ} (hp : p.Prime)
    {H A : Subgroup G} (hAn : A ≤ normalizer (H : Set G)) (hplane : IsPPlane p A)
    [Group.IsSolvable ↥H] (hH : H ≠ ⊥) (hpH : ¬ p ∣ Nat.card ↥H) :
    ∃ x ∈ A, orderOf x = p ∧ ¬ centralizerIn H (zpowers x) ≤ ⁅H, H⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).2 hH
  obtain ⟨hAab, hAcard⟩ := hplane
  have hexp : ∀ a : ↥A, a ^ p = 1 := fun a =>
    Subtype.ext (by simpa using hAab.pow_eq_one (a : G) a.2)
  obtain ⟨a, ha1, hna⟩ := exists_ne_one_autFixedSubgroup_not_le_commutator hp hAcard hexp
    (conjOnNormalized H hAn) hpH
  have hx1 : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hord : orderOf (a : G) = p :=
    orderOf_eq_prime (by simpa using congrArg Subtype.val (hexp a)) hx1
  refine ⟨(a : G), a.2, hord, fun hle => hna ?_⟩
  rw [← Subgroup.map_le_map_iff_of_injective H.subtype_injective,
    map_autFixedSubgroup_conjOnNormalized, Subgroup.map_subtype_commutator]
  exact hle

theorem FPF_complement_plane_centralizer_witness :
    Statements.FPF_complement_plane_centralizer_witness.{u} := by
  intro G _ _ hG M hM hHbot p hp hpH P hPM hPp hplane huniq
  have := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hAP, hAplane⟩ := hplane
  have hpP : p ∣ Nat.card ↥P :=
    dvd_trans (hAplane.2 ▸ dvd_pow_self p two_ne_zero) (Subgroup.card_dvd_of_le hAP)
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hpP
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpP)
  obtain ⟨L, hL, hPL⟩ := exists_isCoatom_le_sigmaCore_of_isPGroup hna hG.odd_natCard
    hG.isSolvable_of_ne_top hp hPbot hPp
  have hLM : L ≠ M := fun h =>
    hpH (dvd_trans hpP (Subgroup.card_dvd_of_le (h ▸ hPL)))
  have hMsolv := hG.isSolvable_of_ne_top M hM.1
  have : Group.IsSolvable ↥(sigmaCore M) := isSolvable_of_le (sigmaCore_le M)
  have hAn : A ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    (hAP.trans hPM).trans (le_normalizer_sigmaCore M)
  obtain ⟨x, hxA, hord, hxder⟩ :=
    exists_mem_orderOf_eq_not_centralizerIn_le_commutator hp hAn hAplane hHbot hpH
  have hxP : x ∈ P := hAP hxA
  have hxne : centralizerIn (sigmaCore M) (zpowers x) ≠ ⊥ := fun h => hxder (h ▸ bot_le)
  have hu := huniq x hxP hord hxne
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hzbot : (zpowers x : Subgroup G) ≠ ⊥ := fun h => hx1 (Subgroup.zpowers_eq_bot.mp h)
  have : Group.IsSolvable ↥(zpowers x : Subgroup G) := isSolvable_of_isMulCommutative
  have hNlt : normalizer ((zpowers x : Subgroup G) : Set G) < ⊤ :=
    normalizer_coe_lt_top_of_isSolvable hna hzbot
  have hCN : centralizer ({x} : Set G) ≤ normalizer ((zpowers x : Subgroup G) : Set G) := by
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hNM : normalizer ((zpowers x : Subgroup G) : Set G) ≤ M := hu.le_of_ne_top hCN hNlt.ne
  exact ⟨L, hL, x, hxP, hord, hPL, hxder, hNM, fun hCL => hLM (hu.eq_of_isCoatom hL hCL)⟩

end

end CFSG.FeitThompson.Proofs
