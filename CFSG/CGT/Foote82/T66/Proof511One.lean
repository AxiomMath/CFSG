module

public import CFSG.CGT.Foote82.T66.Proof511Core
public import CFSG.CGT.Foote82.T66.CitedCaseI

public section

namespace CFSG.CGT.Foote82.Proof511

open Subgroup CFSG.Open CFSG.Quasithin.G11

@[expose] def NotPSL43 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (J : Subgroup (GLV V))
    (c : GLV V), CFSG.IsQuasisimple ↥J → Odd (Nat.card ↥(Subgroup.center ↥J)) →
    ∀ hc : c ∈ J, orderOf c = 3 → (⟨c, hc⟩ : ↥J) ∉ Subgroup.center ↥J →
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) = 2 →
    ¬ CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 3 1

@[expose] def PSp43Cover : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.IsQuasisimple J → Odd (Nat.card (Subgroup.center J)) →
    CFSG.Blueprint.LieModel (J ⧸ Subgroup.center J) .PSp 2 3 1 → Subgroup.center J = ⊥

theorem alt_simple_nonab {k : ℕ} (hk : k = 6 ∨ k = 7) :
    IsSimpleGroup (alternatingGroup (Fin k)) ∧
      ∃ a b : alternatingGroup (Fin k), a * b ≠ b * a := by
  refine ⟨alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega), ?_⟩
  rcases hk with rfl | rfl
  · refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
      ⟨Equiv.swap 0 1 * Equiv.swap 0 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
      fun h => ?_⟩
    have h' := congrArg Subtype.val h
    revert h'
    decide
  · refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
      ⟨Equiv.swap 0 1 * Equiv.swap 0 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
      fun h => ?_⟩
    have h' := congrArg Subtype.val h
    revert h'
    decide

theorem exists_threeCycle {k : ℕ} (hk : 3 ≤ k) {M : Type*} [Group M]
    (e : M ≃* alternatingGroup (Fin k)) :
    ∃ c : M, ((e c : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)).IsThreeCycle ∧
      orderOf c = 3 := by
  have h3 : (Equiv.swap (⟨0, by omega⟩ : Fin k) ⟨1, by omega⟩ *
      Equiv.swap (⟨0, by omega⟩ : Fin k) ⟨2, by omega⟩).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  refine ⟨e.symm ⟨_, h3.mem_alternatingGroup⟩, by simpa using h3, ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, h3.orderOf]

variable {G : Type} [Group G] [Finite G]

theorem caseILemma511_of_inputs
    (hM : CFSG.GH74.ModelsFormStatement)
    (hGLS : CFSG.ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hM22 : SporSqOne .M22) (hM23 : SporSqOne .M23) (hJ2 : SporSqOne .J2) (hJ3 : SporSqOne .J3)
    (hMcL : SporSqOne .McL) (hU4 : PSU4SqOne) (hPSL43 : NotPSL43) (hPSp43 : PSp43Cover) :
    CaseILemma511 := by
  intro V _ _ _ J X L z k e hJX hJn hJi hJq hZ hCJ _ hzX hz hL hk _ h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (GLV V) :=
    Finite.of_injective (fun f : GLV V => (f : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  obtain ⟨hAs, hAn⟩ := alt_simple_nonab hk
  have hLs : IsSimpleGroup ↥L := e.isSimpleGroup
  have hLn : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hAn
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have h : Hyp X J L z := ⟨hJX, hJn, hJi, hCJ, hJq, hZ, hzX, hz, hL, hLs, hLn⟩
  have hk' : Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥L ≃* alternatingGroup (Fin 7)) := by
    rcases hk with rfl | rfl
    · exact Or.inl ⟨e⟩
    · exact Or.inr ⟨e⟩
  refine ⟨fun hS => ?_, fun hS => ?_⟩
  ·
    obtain ⟨m, P, Q, hm, hP, hPi, hQ, hQi, ⟨eP⟩⟩ := hS
    let P₀ : Sylow 2 ↥J := hP.toSylow hPi
    let Q₀ : Sylow 2 (Equiv.Perm (Fin m)) := hQ.toSylow hQi
    have hQ₀ : IsA10Type ↥(Q₀ : Subgroup (Equiv.Perm (Fin m))) := by
      rcases hm with rfl | rfl
      · exact isA10Type_of_perm8 Q₀
      · exact isA10Type_of_perm9 Q₀
    have hsyl : ∀ P' : Sylow 2 ↥J, IsA10Type ↥(P' : Subgroup ↥J) := by
      intro P'
      obtain ⟨eQ⟩ := hQ₀
      exact ⟨((Sylow.equiv P' P₀).trans eP).trans eQ⟩
    rcases reduce_a' hM hGLS hO hM22 hM23 hJ2 hJ3 hMcL hU4 h hk' hsyl with h10 | h11 | hPSL
    · exact Or.inl h10
    · exact Or.inr h11
    · exfalso
      obtain ⟨c, hc3, hco⟩ := exists_threeCycle (by omega) e
      have hcJ : (c : GLV V) ∈ J := h.le_J c.2
      refine hPSL43 V J (c : GLV V) hJq hZ hcJ (by rw [Subgroup.orderOf_coe, hco]) ?_
        (h3 c hc3) hPSL
      intro hcen
      have hcL : c ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨(g : GLV V), h.le_J g.2⟩)
        exact Subtype.ext this
      rw [center_eq_bot_of_simple hLn, Subgroup.mem_bot] at hcL
      rw [hcL, orderOf_one] at hco
      exact absurd hco (by norm_num)
  ·
    obtain ⟨m, P, Q, hm, hP, hPi, hQ, hQi, ⟨eP⟩⟩ := hS
    let P₀ : Sylow 2 ↥J := hP.toSylow hPi
    let Q₀ : Sylow 2 ↥(alternatingGroup (Fin m)) := hQ.toSylow hQi
    have hQ₀ : CFSG.GH74.Uniqueness.SU.SU5.IsA8Type ↥(Q₀ : Subgroup ↥(alternatingGroup (Fin m))) := by
      rcases hm with rfl | rfl
      · exact ⟨Q₀, ⟨MulEquiv.refl _⟩⟩
      · exact isA8Type_of_alt9 Q₀
    have hsyl : ∀ P' : Sylow 2 ↥J,
        CFSG.GH74.Uniqueness.SU.SU5.IsA8Type ↥(P' : Subgroup ↥J) := by
      intro P'
      obtain ⟨Q', ⟨eQ⟩⟩ := hQ₀
      exact ⟨Q', ⟨((Sylow.equiv P' P₀).trans eP).trans eQ⟩⟩
    rcases reduce_b' hM h hk' hsyl with h8 | h9 | hPSp
    · exact Or.inl h8
    · exact Or.inr (Or.inl h9)
    · refine Or.inr (Or.inr ?_)
      have hbot := hPSp43 ↥J hJq hZ hPSp
      have hcard := CFSG.GH74.card_of_lieModel_PSp (by norm_num) (by norm_num) hPSp
      have h1 : Nat.card ↥J = Nat.card (↥J ⧸ Subgroup.center ↥J) :=
        (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hbot).trans
          QuotientGroup.quotientBot).toEquiv).symm
      rw [h1, hcard]
      decide

end CFSG.CGT.Foote82.Proof511
