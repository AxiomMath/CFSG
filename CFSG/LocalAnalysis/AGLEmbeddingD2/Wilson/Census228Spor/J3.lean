module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.J3A6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.Alt6Count
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalBridge
public import Certificates.Certificate12638

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open CFSG.Sporadic.Schreier (j3P)
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native

theorem closure_j3tD_le_centralizer :
    closure (Set.range j3tD) ≤ centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) := by
  rw [closure_le]
  rintro _ ⟨i, rfl⟩
  have h := Certificates.certificate12638
  have hx := rep_of_validA (j3tReps_spec (c := 0) (by norm_num)).1
  have hd := rep_of_validA (j3tDGens_valid i.val i.2)
  have hi := allLt_spec h i.2
  have := eq_of_eqA (rep_compA hx hd) (rep_compA hd hx) hi
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact this.symm

theorem card_centralizer_j3P (x₀ : ↥j3P) {c : Equiv.Perm (Fin 6156)} {e : ℕ} (hc3 : c ^ 3 = 1)
    (he : e = 1 ∨ e = 2) (hx₀ : (x₀ : Equiv.Perm (Fin 6156)) = c ^ e) :
    Nat.card (centralizer ({x₀} : Set ↥j3P)) =
      Nat.card (centralizer ({c} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156))) := by
  have h := CFSG.Quasithin.Kleidman.map_centralizer_of_injective
    (f := j3P.subtype) j3P.subtype_injective x₀
  rw [Subgroup.range_subtype] at h
  rw [← Subgroup.card_map_of_injective j3P.subtype_injective, h]
  have : j3P.subtype x₀ = c ^ e := hx₀
  rw [this, CFSG.Quasithin.Kleidman.centralizer_pow_eq hc3 he]

theorem card_centralizer_XA :
    Nat.card (centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓
    j3P : Subgroup (Equiv.Perm (Fin 6156))) = 1080 := by
  rw [← j3t_caseA.1]; exact j3t_caseA.2

theorem card_centralizer_XB :
    Nat.card (centralizer ({j3tXB} : Set (Equiv.Perm (Fin 6156))) ⊓
    j3P : Subgroup (Equiv.Perm (Fin 6156))) = 243 := by
  rw [← j3t_caseB.1]; exact j3t_caseB.2

theorem threeFiveData228_j3P :
    ThreeFiveData228 ↥j3P := by
  have h1080 : (1080 : ℕ).factorization 5 = 1 := by
    rw [Nat.factorization_def _ (by norm_num : Nat.Prime 5)]
    decide +kernel
  refine threeFiveData228_of_alt6' (a := 1080) h1080 ?_
  intro x k hx hk hxk
  have hxo : orderOf (x : Equiv.Perm (Fin 6156)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨k₁, hk₁, c, hc, e, he, hxe⟩ := j3t_fusion x.2 hxo
  set k' : ↥j3P := ⟨k₁, hk₁⟩ with hk'def
  set x₀ : ↥j3P := k'⁻¹ * x * k' with hx₀def
  have hx₀ : (x₀ : Equiv.Perm (Fin 6156)) = c ^ e := by
    have : (x₀ : Equiv.Perm (Fin 6156)) = k₁⁻¹ * (x : Equiv.Perm (Fin 6156)) * k₁ := rfl
    rw [this, hxe]
    group
  have hC : centralizer ({x} : Set ↥j3P) =
      (centralizer ({x₀} : Set ↥j3P)).map (MulAut.conj k').toMonoidHom := by
    have := CFSG.LargeExtraspecial.AS35W.centralizer_map (MulAut.conj k') x₀
    have hx : (MulAut.conj k') x₀ = x := by
      simp only [MulAut.conj_apply, hx₀def]
      group
    rw [hx] at this
    exact this
  have hc3 : c ^ 3 = 1 := by
    rcases hc with rfl | rfl
    · exact (j3tReps_spec (by norm_num : 0 < 2)).2
    · exact (j3tReps_spec (by norm_num : 1 < 2)).2
  have hcard := card_centralizer_j3P x₀ hc3 he hx₀
  rcases hc with rfl | rfl
  ·
    obtain ⟨eD⟩ := nonempty_mulEquiv_D_alt6
    have hDle : closure (Set.range j3tD) ≤ j3P := by
      rw [closure_le]
      rintro _ ⟨i, rfl⟩
      exact j3tD_mem i
    refine ⟨x₀, k', (Subgroup.inclusion hDle).comp eD.symm.toMonoidHom, ?_, ?_, ?_, hC⟩
    · exact (Subgroup.inclusion_injective hDle).comp eD.symm.injective
    · intro h
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hmem : ((eD.symm h : closure (Set.range j3tD)) : Equiv.Perm (Fin 6156)) ∈
          centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) :=
        closure_j3tD_le_centralizer (eD.symm h).2
      rw [← CFSG.Quasithin.Kleidman.centralizer_pow_eq hc3 he] at hmem
      rw [Subgroup.mem_centralizer_singleton_iff] at hmem
      show ((eD.symm h : closure (Set.range j3tD)) : Equiv.Perm (Fin 6156)) *
        (x₀ : Equiv.Perm (Fin 6156)) = (x₀ : Equiv.Perm (Fin 6156)) *
          ((eD.symm h : closure (Set.range j3tD)) : Equiv.Perm (Fin 6156))
      rw [hx₀]
      exact hmem
    · rw [hcard]; exact card_centralizer_XA
  ·
    exfalso
    have h243 : Nat.card (centralizer ({x} : Set ↥j3P)) = 243 := by
      rw [hC, Subgroup.card_map_of_injective (MulAut.conj k').injective, hcard]
      exact card_centralizer_XB
    have hkC : k ∈ centralizer ({x} : Set ↥j3P) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxk.symm
    have hdvd := orderOf_dvd_natCard (⟨k, hkC⟩ : centralizer ({x} : Set ↥j3P))
    rw [Subgroup.orderOf_mk, hk, h243] at hdvd
    omega

theorem threeFiveData228_J3 :
    ThreeFiveData228 (NativeSporadic.Carrier .J3) :=
  threeFiveData228_of_mulEquiv (CFSG.Sporadic.Schreier.j3PermEquiv).symm threeFiveData228_j3P

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
