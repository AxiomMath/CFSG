module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Solv

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_normal_of_quotient {H : Type} [Group H] (N : Subgroup H) [N.Normal]
    [Group.IsSolvable ↥N] [Group.IsSolvable (H ⧸ N)] : Group.IsSolvable H :=
  Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem solvable_of_odd (X : Type) [Group X] [Finite X] (h : Odd (Nat.card X)) : Group.IsSolvable X :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ h

theorem pPrimeCore_two_solvable (X : Type) [Group X] [Finite X] : Group.IsSolvable ↥(pPrimeCore 2 X) :=
  solvable_of_odd _ (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X)))

theorem Cen_solvable_of_bar (z : G) (h : Group.IsSolvable (CentralizerBar z)) : Group.IsSolvable ↥(Cen z) := by
  have := pPrimeCore_two_solvable ↥(Cen z)
  exact isSolvable_of_normal_of_quotient (pPrimeCore 2 ↥(Cen z))

theorem solvable_of_cover {z : G} {M : Subgroup G} (hCM : Cen z ≤ M) (hC : Group.IsSolvable ↥(Cen z))
    (hcov : ∀ h ∈ M, ∃ c ∈ Cen z, ∃ o ∈ pPrimeCoreOf 2 M, h = c * o) : Group.IsSolvable ↥M := by
  have hO := pPrimeCore_two_solvable ↥M
  let φ : ↥(Cen z) →* ↥M ⧸ pPrimeCore 2 ↥M := (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hCM)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) y
    obtain ⟨c, hc, o, ho, hco⟩ := hcov (h : G) h.2
    obtain ⟨o', ho', rfl⟩ := ho
    refine ⟨⟨c, hc⟩, ?_⟩
    show QuotientGroup.mk' (pPrimeCore 2 ↥M) (Subgroup.inclusion hCM ⟨c, hc⟩) = QuotientGroup.mk' (pPrimeCore 2 ↥M) h
    have : h = Subgroup.inclusion hCM ⟨c, hc⟩ * o' := by
      apply Subtype.ext
      simpa using hco
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) o' = 1 := (QuotientGroup.eq_one_iff o').mpr ho'
    rw [this, map_mul, h1, mul_one]
  have : Group.IsSolvable (↥M ⧸ pPrimeCore 2 ↥M) := Group.isSolvable_of_surjective hφ
  exact isSolvable_of_normal_of_quotient (pPrimeCore 2 ↥M)

end Solv

section M12

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem bar_solvable_of_m12 (h : Stage1M12 G z S) : Group.IsSolvable (CentralizerBar z) := by
  obtain ⟨A, B, hAB, ⟨eA⟩, ⟨eB⟩, hAn⟩ := h.W_shape
  obtain ⟨hWn, ⟨e⟩⟩ := h.quot
  have hq8 : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by simp [Nat.card_eq_fintype_card, QuaternionGroup.card])
  have hA2 : IsPGroup 2 ↥A := hq8.of_equiv eA.symm
  have hB2 : IsPGroup 2 ↥B := hq8.of_equiv eB.symm
  have hW2 : IsPGroup 2 ↥(WBar z) := by
    intro y
    have hy : (y : CentralizerBar z) ∈ A ⊔ B := by rw [hAB.1]; exact y.2
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    obtain ⟨n, hn⟩ := hA2 ⟨a, ha⟩
    obtain ⟨m, hm⟩ := hB2 ⟨b, hb⟩
    have hn' : a ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hm' : b ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hc : Commute a b := hAB.2.1 a ha b hb
    refine ⟨n + m, Subtype.ext ?_⟩
    have ha1 : a ^ 2 ^ (n + m) = 1 := by rw [pow_add, pow_mul, hn', one_pow]
    have hb1 : b ^ 2 ^ (n + m) = 1 := by rw [pow_add, mul_comm, pow_mul, hm', one_pow]
    have : ((y : CentralizerBar z)) ^ 2 ^ (n + m) = 1 := by
      rw [← hab, hc.mul_pow, ha1, hb1, mul_one]
    simpa using this
  have hWs : Group.IsSolvable ↥(WBar z) := by
    have := hW2.isNilpotent
    infer_instance
  have hQs : Group.IsSolvable (CentralizerBar z ⧸ WBar z) := by
    have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have := hWn
  exact isSolvable_of_normal_of_quotient (WBar z)

theorem cen_solvable_of_m12 (ctx : Stage2Ctx G z Kind.m12 S) : Group.IsSolvable ↥(Cen z) := by
  cases ctx.data with
  | m12 h => exact Cen_solvable_of_bar z (bar_solvable_of_m12 h)

theorem not_solvable_of_quasisimple {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) :
    ¬ Group.IsSolvable K := by
  obtain ⟨hperf, hsimple, -⟩ := hK
  have : Group.IsPerfect K := hperf
  have : Nontrivial (K ⧸ center K) := hsimple.toNontrivial
  have : Nontrivial K := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center K))
  exact Group.IsPerfect.not_isSolvable K

theorem not_solvable_centralizer_of_nonCentral {x : G} (h : M12NonCentral x) :
    ¬ Group.IsSolvable ↥(centralizer ({x} : Set G)) := by
  intro hsolv
  obtain ⟨K, y, q, ⟨-, hK⟩, -⟩ := h
  obtain ⟨K', hK'c, -, -, -⟩ := hK
  have h1 : Group.IsSolvable (↥(centralizer ({x} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({x} : Set G))) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  have h2 : Group.IsSolvable ↥K' := inferInstance
  exact not_solvable_of_quasisimple hK'c.1 h2

end M12

end CFSG.GH74.GLS.Stage2.Bender.Thm1
