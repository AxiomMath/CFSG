module

public import CFSG.HardMathSupport.Curtis.Proving.SchurStepDComm
public import CFSG.HardMathSupport.Curtis.Proving.SchurStepDAction
public import CFSG.HardMathSupport.Curtis.Proving.SchurCommute

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def preimSub (L : Subgroup G) [Fact (IsShort2 L)]
    (W : Submodule (ZMod 2) (Additive (UZ L))) : Subgroup G where
  carrier := {x | ∃ h : x ∈ blockU L, piU L ⟨x, h⟩ ∈ W}
  one_mem' := ⟨(blockU L).one_mem, by
    have h0 : piU L (1 : ↥(blockU L)) = 0 :=
      (piU_eq_zero_iff (L := L) 1).2 (blockZ L).one_mem
    change piU L (1 : ↥(blockU L)) ∈ W
    rw [h0]
    exact W.zero_mem⟩
  mul_mem' := by
    rintro x y ⟨hx, hWx⟩ ⟨hy, hWy⟩
    refine ⟨(blockU L).mul_mem hx hy, ?_⟩
    change piU L (⟨x, hx⟩ * ⟨y, hy⟩) ∈ W
    rw [piU_mul]
    exact W.add_mem hWx hWy
  inv_mem' := by
    rintro x ⟨hx, hWx⟩
    refine ⟨(blockU L).inv_mem hx, ?_⟩
    change piU L (⟨x, hx⟩⁻¹) ∈ W
    rw [piU_inv]
    exact W.neg_mem hWx

@[expose] def actionSet (L : Subgroup G) [Fact (IsShort2 L)] :
    Set (Module.End (ZMod 2) (Additive (UZ L))) :=
  {t | ∃ (l : G) (hl : l ∈ Subgroup.normalizer (L : Set G)), l ∈ L ∧ t = rhoLin hl}

theorem le_normalizer_preimSub {L : Subgroup G} [Fact (IsShort2 L)]
    {W : Submodule (ZMod 2) (Additive (UZ L))}
    (hW : ∀ t ∈ actionSet L, ∀ w ∈ W, t w ∈ W) :
    L ≤ Subgroup.normalizer (preimSub L W : Set G) := by
  have fwd : ∀ l ∈ L, ∀ x ∈ preimSub L W, l * x * l⁻¹ ∈ preimSub L W := by
    intro l hl x hx
    obtain ⟨hxU, hWx⟩ := hx
    have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
    refine ⟨blockU_conj_mem_normalizer hlN hxU, ?_⟩
    have h := hW (rhoLin hlN) ⟨l, hlN, hl, rfl⟩ _ hWx
    rw [rhoLin_piU] at h
    exact h
  intro l hl
  refine Subgroup.mem_normalizer_iff.2 (fun h => ⟨fun hh => fwd l hl h hh, fun hh => ?_⟩)
  have h' := fwd l⁻¹ (L.inv_mem hl) _ hh
  have e : l⁻¹ * (l * h * l⁻¹) * l⁻¹⁻¹ = h := by group
  rw [e] at h'
  exact h'

theorem irred_UZ {L : Subgroup G} [Fact (IsShort2 L)]
    (W : Submodule (ZMod 2) (Additive (UZ L)))
    (hW : ∀ t ∈ actionSet L, ∀ w ∈ W, t w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hL : IsShort2 L := Fact.out
  have hZS : blockZ L ≤ preimSub L W := by
    intro z hz
    have hzU : z ∈ blockU L := (Subgroup.mem_inf.1 hz).1
    refine ⟨hzU, ?_⟩
    rw [(piU_eq_zero_iff (L := L) ⟨z, hzU⟩).2 hz]
    exact W.zero_mem
  have hSU : preimSub L W ≤ blockU L := fun x hx => hx.1
  rcases hL.2.2.2.2.2 (preimSub L W) hZS hSU (le_normalizer_preimSub hW) with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨u, rfl⟩ := piU_surj (L := L) w
    have huS : (u : G) ∈ preimSub L W := ⟨u.2, hw⟩
    rw [h] at huS
    rw [Submodule.mem_bot]
    exact (piU_eq_zero_iff u).2 huS
  · right
    rw [eq_top_iff]
    intro w _
    obtain ⟨u, rfl⟩ := piU_surj (L := L) w
    have huS : (u : G) ∈ preimSub L W := by
      rw [h]
      exact u.2
    obtain ⟨_, hWu⟩ := huS
    exact hWu

theorem rhoLin_comm_Q {M L Q : Subgroup G} [Fact (IsShort2 L)] (hML : IsTwoPrimeComponent M L)
    (hQM : Q ≤ M) (hQN : Q ≤ Subgroup.normalizer (L : Set G))
    (hcent : barM M Q ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {a l : G} (ha : a ∈ Q) (hl : l ∈ L) (hlN : l ∈ Subgroup.normalizer (L : Set G)) :
    rhoLin hlN * rhoLin (hQN ha) = rhoLin (hQN ha) * rhoLin hlN :=
  rhoLin_comm (hQN ha) hlN
    (fun u => conjU_comm_of_centralizes (hQN ha) hlN (comm_mem_blockQ hML hQM hQN hcent ha hl) u)

theorem mul_inv_mem_blockZ_of_inv_mul {L : Subgroup G} (hL : IsShort2 L) {x u : G}
    (hx : x ∈ blockU L) (hu : u ∈ blockU L) (h : x⁻¹ * u ∈ blockZ L) :
    x * u⁻¹ ∈ blockZ L := by
  have hc : x * u = u * x := blockU_comm hL hx hu
  have e : x * u⁻¹ = (x⁻¹ * u)⁻¹ := by
    calc x * u⁻¹ = u⁻¹ * (u * x) * u⁻¹ := by group
      _ = u⁻¹ * (x * u) * u⁻¹ := by rw [hc]
      _ = u⁻¹ * x := by group
      _ = (x⁻¹ * u)⁻¹ := by group
  rw [e]
  exact (blockZ L).inv_mem h

theorem commutator_le_actsTrivSubgroup [Finite G] {M L Q : Subgroup G}
    (hML : IsTwoPrimeComponent M L) (hL : IsShort2 L) (hQM : Q ≤ M)
    (hQN : Q ≤ Subgroup.normalizer (L : Set G))
    (hcent : barM M Q ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ⁅Q, Q⁆ ≤ actsTrivSubgroup L := by
  haveI : Fact (IsShort2 L) := ⟨hL⟩
  haveI : Nontrivial (Additive (UZ L)) := by
    obtain ⟨u, hu, hnot⟩ := SetLike.exists_of_lt hL.2.2.2.2.1
    exact ⟨⟨piU L ⟨u, hu⟩, 0, fun h => hnot ((piU_eq_zero_iff ⟨u, hu⟩).1 h)⟩⟩
  haveI : Finite (Additive (UZ L)) := inferInstance
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haN : a ∈ Subgroup.normalizer (L : Set G) := hQN ha
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hQN hb
  have hS : rhoLin haN * rhoLin hbN = rhoLin hbN * rhoLin haN :=
    commute_of_mem_centralizer_of_irreducible (T := actionSet L) (irred_UZ (L := L))
      (f := rhoLin haN) (g := rhoLin hbN)
      (by rintro t ⟨l, hlN, hl, rfl⟩; exact rhoLin_comm_Q hML hQM hQN hcent ha hl hlN)
      (by rintro t ⟨l, hlN, hl, rfl⟩; exact rhoLin_comm_Q hML hQM hQN hcent hb hl hlN)
  rw [commutatorElement_def]
  refine mem_actsTrivSubgroup_iff.2
    (And.intro (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ haN hbN)
      (Subgroup.inv_mem _ haN)) (Subgroup.inv_mem _ hbN)) (fun u hu => ?_))
  have hba : b * a ∈ Subgroup.normalizer (L : Set G) := Subgroup.mul_mem _ hbN haN
  have hinv : (b * a)⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hba
  have key : piU L (conjU haN (conjU hbN (conjU hinv ⟨u, hu⟩))) =
      piU L (conjU hbN (conjU haN (conjU hinv ⟨u, hu⟩))) := by
    have h := congrArg (fun φ : Module.End (ZMod 2) (Additive (UZ L)) =>
      φ (piU L (conjU hinv ⟨u, hu⟩))) hS
    simpa only [Module.End.mul_apply, rhoLin_piU] using h
  have hrhs : conjU hbN (conjU haN (conjU hinv ⟨u, hu⟩)) = ⟨u, hu⟩ :=
    Subtype.ext (by
      simp only [conjU_coe, inv_inv]
      group)
  have hmain : piU L (conjU haN (conjU hbN (conjU hinv ⟨u, hu⟩))) = piU L ⟨u, hu⟩ := by
    rw [key, hrhs]
  have hX : ((conjU haN (conjU hbN (conjU hinv ⟨u, hu⟩)) : ↥(blockU L)) : G) =
      a * b * a⁻¹ * b⁻¹ * u * (a * b * a⁻¹ * b⁻¹)⁻¹ := by
    simp only [conjU_coe, inv_inv]
    group
  have hZ := mem_blockZ_of_piU_eq (conjU haN (conjU hbN (conjU hinv ⟨u, hu⟩))).2 hu hmain
  have hgoal := mul_inv_mem_blockZ_of_inv_mul hL
    (conjU haN (conjU hbN (conjU hinv ⟨u, hu⟩))).2 hu hZ
  rw [← hX]
  exact hgoal

end CFSG.HardMathSupport.Curtis.Proving

end
