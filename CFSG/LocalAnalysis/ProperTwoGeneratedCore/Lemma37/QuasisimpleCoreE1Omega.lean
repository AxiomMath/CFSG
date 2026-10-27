module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1OmegaAct

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open Equiv Equiv.Perm CFSG.Sporadic.Th.Max3

@[expose] def altRep4A : alternatingGroup (Fin 9) :=
  ⟨altRep4, mem_alternatingGroup.mpr sign_altRep4⟩

theorem card_centralizer_altRep4_perm :
    Nat.card (Subgroup.centralizer ({altRep4} : Set (Perm (Fin 9)))) = 384 := by
  rw [nat_card_centralizer, cycleType_altRep4]
  decide

theorem card_centralizer_altRep4 :
    Nat.card (Subgroup.centralizer ({altRep4A} : Set (alternatingGroup (Fin 9)))) = 192 := by
  set C := Subgroup.centralizer ({altRep4} : Set (Perm (Fin 9)))
  let f : C →* ℤˣ := sign.comp C.subtype
  have hsurj : Function.Surjective f := by
    intro ε
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨swap 0 1, Subgroup.mem_centralizer_singleton_iff.mpr swap_mul_altRep4⟩,
        sign_swap (show (0 : Fin 9) ≠ 1 by decide)⟩
  have hker : Nat.card f.ker * 2 = 384 := by
    rw [← card_centralizer_altRep4_perm, ← Subgroup.card_mul_index f.ker, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_eq_fintype_card (α := ℤˣ),
      Fintype.card_units_int]
  have heq : Nat.card (Subgroup.centralizer ({altRep4A} : Set (alternatingGroup (Fin 9)))) =
      Nat.card f.ker := Nat.card_congr
    { toFun := fun a => ⟨⟨(a : alternatingGroup (Fin 9)), Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp a.2))⟩,
        mem_alternatingGroup.mp (a : alternatingGroup (Fin 9)).2⟩
      invFun := fun c => ⟨⟨((c : C) : Perm (Fin 9)), mem_alternatingGroup.mpr c.2⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
          (Subgroup.mem_centralizer_singleton_iff.mp (c : C).2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  omega

theorem sign_conj_perm {α : Type*} [Fintype α] [DecidableEq α] (g σ : Perm α) :
    sign (g * σ * g⁻¹) = sign σ := by
  rw [map_mul, map_mul, map_inv, mul_comm (sign g), mul_assoc, mul_inv_cancel, mul_one]

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
  (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
    s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s)
  (hOu : CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) = ⊥)
  (hOz : CFSG.pPrimeCore 2
    (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) = ⊥)
include d htype hOu hOz

theorem exists_phiZ
    : ∃ φ : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} →*
      alternatingGroup (Fin 9),
    Function.Injective φ ∧ φ.range = Subgroup.centralizer {altRep4A} ∧ φ (d.wordZ 40) = altRep4A ∧
    (∀ s : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}, s ≠ 1 →
      CaseC3.Genuine (Subgroup.center J) (s : J ⧸ Subgroup.center J) →
      ((φ s : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2, 2, 2}) ∧
    (∀ s : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}, s * s = 1 →
      ¬ CaseC3.Genuine (Subgroup.center J) (s : J ⧸ Subgroup.center J) →
      ((φ s : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2}) := by
  have hb := d.caseC3BCD
  set ψ := d.psiZ htype hOu hOz
  have hz1 : d.wordZ 40 ≠ 1 := fun h => d.forty_ne_one (congrArg Subtype.val h)
  have hzz : ψ (d.wordZ 40) * ψ (d.wordZ 40) = 1 := by
    rw [← map_mul, d.wordZ_mul, show c3Mul 40 40 = 0 from c3Mul_forty_forty,
      show d.wordZ 0 = 1 from Subtype.ext CaseC3BCD.caseC3Word_zero, map_one]
  obtain ⟨hzct, hzsign⟩ := cycleType_of_existsUnique_fixed hzz
    (d.existsUnique_psiZ_fixed htype hOu hOz hb.genuine_forty hz1)
  have hψz1 : ψ (d.wordZ 40) ≠ 1 := fun h =>
    hz1 (d.psiZ_injective htype hOu hOz (h.trans (map_one ψ).symm))
  have hzord : orderOf (ψ (d.wordZ 40)) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hzz) hψz1
  obtain ⟨g, -, hg⟩ := exists_conj_eq_of_orderOf_eq_two (mem_alternatingGroup.mpr hzsign) hzord
  have hg4 : g * ψ (d.wordZ 40) * g⁻¹ = altRep4 := by
    rcases hg with hg | hg
    · exfalso
      have h := congrArg Perm.cycleType hg
      rw [cycleType_conj, hzct, cycleType_altRep2] at h
      exact absurd h (by decide)
    · exact hg
  let φ' : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} →* Perm (Fin 9) :=
    (MulAut.conj g).toMonoidHom.comp ψ
  have hφ'A : ∀ s, φ' s ∈ alternatingGroup (Fin 9) := fun s => by
    rw [mem_alternatingGroup]
    change sign (g * ψ s * g⁻¹) = 1
    rw [sign_conj_perm, d.sign_psiZ htype hOu hOz s]
  let φ := φ'.codRestrict (alternatingGroup (Fin 9)) hφ'A
  have hφapp : ∀ s, ((φ s : alternatingGroup (Fin 9)) : Perm (Fin 9)) = g * ψ s * g⁻¹ :=
    fun _ => rfl
  have hinj : Function.Injective φ := fun s t h => by
    apply d.psiZ_injective htype hOu hOz
    have h' := congrArg Subtype.val h
    rw [hφapp, hφapp] at h'
    exact mul_left_cancel (mul_right_cancel h')
  have hφz : φ (d.wordZ 40) = altRep4A := Subtype.ext (by rw [hφapp, hg4]; rfl)
  have hle : φ.range ≤ Subgroup.centralizer {altRep4A} := by
    rintro _ ⟨s, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hφz, ← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp s.2))
  have hrange : φ.range = Subgroup.centralizer {altRep4A} := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_centralizer_altRep4, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      d.card_centralizer_forty_of_pPrimeCore htype hOz]
  refine ⟨φ, hinj, hrange, hφz, fun s hs1 hgen => ?_, fun s hss hgen => ?_⟩
  · rw [hφapp, cycleType_conj]
    have hss : s * s = 1 := Subtype.ext (CaseC3.mul_self_of_genuine hgen)
    exact (cycleType_of_existsUnique_fixed (by rw [← map_mul, hss, map_one])
      (d.existsUnique_psiZ_fixed htype hOu hOz hgen hs1)).1
  · rw [hφapp, cycleType_conj]
    have hs1 : s ≠ 1 := fun h => hgen (by rw [h]; exact ⟨1, QuotientGroup.mk_one _, mul_one 1⟩)
    obtain ⟨i, j, hij, hi, hj⟩ := d.exists_two_psiZ_fixed htype hOu hOz hss hgen
    exact cycleType_of_two_fixed (by rw [← map_mul, hss, map_one])
      (fun h => hs1 (d.psiZ_injective htype hOu hOz (h.trans (map_one ψ).symm)))
      (d.sign_psiZ htype hOu hOz s) hij hi hj

@[expose] noncomputable def phiZ :
    Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} →*
      alternatingGroup (Fin 9) :=
  Classical.choose (d.exists_phiZ htype hOu hOz)

theorem phiZ_spec :
    Function.Injective (d.phiZ htype hOu hOz) ∧
    (d.phiZ htype hOu hOz).range = Subgroup.centralizer {altRep4A} ∧
    d.phiZ htype hOu hOz (d.wordZ 40) = altRep4A ∧
    (∀ s : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}, s ≠ 1 →
      CaseC3.Genuine (Subgroup.center J) (s : J ⧸ Subgroup.center J) →
      ((d.phiZ htype hOu hOz s : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType =
        {2, 2, 2, 2}) ∧
    (∀ s : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}, s * s = 1 →
      ¬ CaseC3.Genuine (Subgroup.center J) (s : J ⧸ Subgroup.center J) →
      ((d.phiZ htype hOu hOz s : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2}) :=
  Classical.choose_spec (d.exists_phiZ htype hOu hOz)

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
