module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemRuFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSOutModel

public section

namespace CFSG.EvenSporadicStandard.Induction.TMemRu

open Subgroup CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.Solomon78

@[expose] def tmE : Subgroup (Equiv.Perm (Fin 4060)) :=
  ruP ⊓ centralizer ({ruA0} : Set (Equiv.Perm (Fin 4060)))

theorem factorization_two_29120' : (29120 : ℕ).factorization 2 = 6 := by
  have h : (29120 : ℕ) = 2 ^ 6 * 455 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem dvd_29120 {n : ℕ} (h64 : 64 ∣ n) (h5 : 5 ∣ n) (h7 : 7 ∣ n) (h13 : 13 ∣ n) :
    29120 ∣ n := by
  have h1 : 64 * 5 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h64 h5
  have h2 : 64 * 5 * 7 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h7
  have h3 : 64 * 5 * 7 * 13 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h13
  simpa using h3

theorem not_conj_of_fixed {α : Type*} {a z : Equiv.Perm α} (hfpf : ∀ p, a p ≠ p)
    (hz : ∃ p, z p = p) (x : Equiv.Perm α) : x * a * x⁻¹ ≠ z := by
  intro hx
  obtain ⟨p, hp⟩ := hz
  rw [← hx] at hp
  have h1 : x (a (x.symm p)) = p := hp
  have h2 : a (x.symm p) = x.symm p := by
    have := congrArg x.symm h1
    rwa [Equiv.symm_apply_apply] at this
  exact hfpf (x.symm p) h2

section Model


theorem ruOutRowModel {D : Subgroup (Equiv.Perm (Fin 4060))}
    (hq : Quot2Data tmE.subtype D) (hD : Nat.card D = 29120) :
    Nonempty (OutRowModel ruP tmE tmE.subtype D ruA0) := by
  obtain ⟨A, B, z, l, S, hAP, hBP, hAc, hBc, hA5, hB7, hAB13, ha0, hfpf, hzmem, hz2, hz1, hzfix,
    hlP, hlc, hgen, hSD, hScard, hSz, hScov⟩ := tmRu_facts
  have hAE : A ∈ tmE := ⟨hAP, mem_centralizer_singleton_iff.2 hAc⟩
  have hBE : B ∈ tmE := ⟨hBP, mem_centralizer_singleton_iff.2 hBc⟩
  have hAodd : Odd (orderOf (⟨A, hAE⟩ : ↥tmE)) := by
    rw [Subgroup.orderOf_mk, hA5]
    decide
  have hBodd : Odd (orderOf (⟨B, hBE⟩ : ↥tmE)) := by
    rw [Subgroup.orderOf_mk, hB7]
    decide
  have hAD : A ∈ D := hq.mem_of_odd hAodd
  have hBD : B ∈ D := hq.mem_of_odd hBodd
  have hle : Subgroup.closure {A, B} ≤ D := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hAD
    · exact hBD
  have hAmem : A ∈ Subgroup.closure {A, B} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hBmem : B ∈ Subgroup.closure {A, B} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hABmem : A * B ∈ Subgroup.closure {A, B} := Subgroup.mul_mem _ hAmem hBmem
  have hdvd : 29120 ∣ Nat.card (Subgroup.closure {A, B}) := by
    refine dvd_29120 ?_ ?_ ?_ ?_
    · have := Subgroup.card_dvd_of_le hSD
      rwa [hScard] at this
    · have := Subgroup.orderOf_dvd_natCard _ hAmem
      rwa [hA5] at this
    · have := Subgroup.orderOf_dvd_natCard _ hBmem
      rwa [hB7] at this
    · have := Subgroup.orderOf_dvd_natCard _ hABmem
      rwa [hAB13] at this
  have hge : Nat.card D ≤ Nat.card (Subgroup.closure {A, B}) := by
    rw [hD]
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have hcl : Subgroup.closure {A, B} = D := Subgroup.eq_of_le_of_card_ge hle hge
  have h2D : twoAdic D = 6 := by
    unfold twoAdic
    rw [hD, factorization_two_29120']
  have hS64 : Nat.card S = 2 ^ twoAdic D := by
    rw [h2D, hScard]
    norm_num
  have hSD' : S ≤ D := hcl ▸ hSD
  refine ⟨{ quot := hq
            A := A
            B := B
            z := z
            l := l
            t_mem := tmA0_mem
            E_iff := ?_
            A_mem := hAE
            B_mem := hBE
            A_odd := hAodd
            B_odd := hBodd
            gen_card := ?_
            z_mem := hzmem
            z_sq := hz2
            z_ne := hz1
            z_two := fun _ _ => twoAdic_le_of_sylow_centralizer hSD' hS64 hSz
            l_mem := hlP
            l_conj := hlc
            gen := hgen
            z_not_conj := ?_
            D_fuse := twoCentralFused_of_sylow hSD' hS64 (ζ := z) ?_ }⟩
  · intro y
    simp only [tmE, Subgroup.mem_inf, mem_centralizer_singleton_iff]
  · show Nat.card ↥(Subgroup.closure {A, B}) = Nat.card D
    rw [hcl]
  · exact fun x _ => not_conj_of_fixed hfpf hzfix x
  · intro x hx hx2 hx1 hxc
    obtain ⟨c, hc, hcx⟩ := hScov x hx hx2 hx1 hxc
    exact ⟨c, hcl ▸ hc, hcx⟩

end Model

end CFSG.EvenSporadicStandard.Induction.TMemRu
