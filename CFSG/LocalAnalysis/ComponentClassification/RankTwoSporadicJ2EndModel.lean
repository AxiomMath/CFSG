module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2EndTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicEndgame
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsTransfer

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J2

open Subgroup CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Fischer CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.J2Cover.Kernel
open CFSG.ComponentClassification.RankTwoSporadic.Endgame
open scoped commutatorElement

theorem commutatorElement_mem_P (x y : ↥R) :
    ⁅x, y⁆ ∈ P.subgroupOf R := by
  have h2 : (P.subgroupOf R).index = 2 := relIndex_P_R
  rw [commutatorElement_def, mul_mem_iff_of_index_two h2, mul_mem_iff_of_index_two h2,
    mul_mem_iff_of_index_two h2, inv_mem_iff, inv_mem_iff]
  tauto

@[expose] noncomputable def j2e0 : Equiv.Perm (Fin 315) := permOfArr 315 j2E0[0]!

structure J2EndFacts : Prop where
  le_P : j2E0Sub ≤ P
  fixCount_eq : ∀ e ∈ j2E0Sub, e ≠ 1 → Models.fixCount e = 15
  exists_conj : ∃ a₀ ∈ P,
    (∀ e ∈ j2E0Sub, ∀ e' ∈ j2E0Sub, e * (a₀⁻¹ * e' * a₀) = a₀⁻¹ * e' * a₀ * e) ∧
    a₀⁻¹ * j2e0 * a₀ ∉ j2E0Sub ∧
    ∃ x : Fin 8 → Equiv.Perm (Fin 315), (∀ i, x i ∈ P ∧ ∀ e ∈ j2E0Sub, x i * e = e * x i) ∧
      tree3 x = j2e0 * (a₀⁻¹ * j2e0 * a₀)
  exists_permA : ∃ c₀ ∈ P, c₀ * j2e0 * c₀⁻¹ = permA
  fixCount_ne : ∀ z ∈ ⁅centralizerIn P permA, centralizerIn P permA⁆, z ^ 2 = 1 → z ≠ 1 →
    Models.fixCount z ≠ 15

theorem getElem!_mem_toList {c : ArrCert} {i : ℕ} (hi : i < c.pts.size) :
    c.pts[i]! ∈ c.pts.toList := by
  rw [getElem!_pos c.pts i hi]
  exact Array.getElem_mem_toList hi

theorem mem_of_inEnum {gs : Array (Array ℕ)} {c : ArrCert} (hc : enumOK 315 gs j2PS c = true)
    {t : Array ℕ} {x : Equiv.Perm (Fin 315)} (ht : Rep 315 t x) (h : inEnum c t = true) :
    x ∈ closure (permsA 315 gs) :=
  enumOK_mem_of_any j2PS_lt hc ht h

theorem j2EndFacts_of_check
    {a0 c0 : Array Nat} {xs gN : Array (Array Nat)} (h : j2EndCheck j2E0 a0 c0 xs gN = true) :
    J2EndFacts := by
  simp only [j2EndCheck, j2EndE0OK, j2EndConjOK, j2EndDerOK, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hcE, hP0⟩, hfix⟩, ⟨⟨⟨⟨⟨ha0v, ha0P⟩, hcomm⟩, hnot⟩, ⟨hxs, htree⟩⟩,
    ⟨⟨hc0v, hc0P⟩, hc0e⟩⟩⟩, ⟨⟨⟨⟨⟨hcN, hs0⟩, hs1⟩, hnorm⟩, hss⟩, hinv⟩⟩ := h
  have hE0 : 0 < j2E0.size := by decide
  have hrep : ∀ k < j2E0.size, Rep 315 j2E0[k]! (permOfArr 315 j2E0[k]!) := fun k hk =>
    rep_of_validA (enumOK_gens_valid hcE hk)
  have he : Rep 315 j2E0[0]! j2e0 := hrep 0 hE0
  set a₀ := permOfArr 315 a0 with ha₀
  have hra : Rep 315 a0 a₀ := rep_of_validA ha0v
  set f := (MulAut.conj a₀⁻¹).toMonoidHom with hf
  have hfa : ∀ g, f g = a₀⁻¹ * g * a₀ := fun g => by simp [hf]
  have hconjE : ∀ e' ∈ j2E0Sub, a₀⁻¹ * e' * a₀ ∈ closure (f '' permsA 315 j2E0) := by
    intro e' he'
    have h1 := mem_map_of_mem f he'
    rw [j2E0Sub, MonoidHom.map_closure] at h1
    rwa [hfa] at h1
  refine ⟨?_, ?_, ⟨a₀, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  ·
    rw [j2E0Sub, closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact (j2InP_iff _ _ (hrep k hk)).mp (allLt_spec hP0 hk)
  ·
    intro e hE he1
    obtain ⟨i, hi, hri⟩ := enumOK_exists_rep j2PS_lt hcE hE
    have h1 := allLt_spec hfix hi
    rw [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · exact absurd (eq_of_eqA hri rep_idA h1) he1
    · rw [Models.fixCount_eq hri]
      exact beq_iff_eq.mp h1
  · exact (j2InP_iff _ _ hra).mp ha0P
  ·
    intro e hE e' hE'
    refine commute_of_mem_closure ?_ hE (hconjE e' hE')
    rintro _ ⟨i, hi, rfl⟩ _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    have h1 := allLt_spec (allLt_spec hcomm hi) hj
    rw [hfa]
    exact eq_of_eqA (rep_compA (hrep i hi) (rep_conjInvA ha0v (hrep j hj)))
      (rep_compA (rep_conjInvA ha0v (hrep j hj)) (hrep i hi)) h1
  ·
    intro hmem
    obtain ⟨i, hi, hri⟩ := enumOK_exists_rep j2PS_lt hcE hmem
    have h1 : inEnum (enumBfs 315 j2E0 j2PS j2Fuel) (conjInvA 315 a0 j2E0[0]!) = true := by
      rw [inEnum, List.any_eq_true]
      exact ⟨_, getElem!_mem_toList hi, (eqA_iff (rep_conjInvA ha0v he) hri).mpr rfl⟩
    rw [h1] at hnot
    exact Bool.noConfusion hnot
  ·
    simp only [treeOK, Bool.and_eq_true, beq_iff_eq] at htree
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsz, hxv⟩, h0⟩, h1⟩, h2⟩, h3⟩, hm0⟩, hm1⟩, htop⟩ := htree
    have hrx : ∀ i : Fin 8, Rep 315 xs[(i : ℕ)]! (permOfArr 315 xs[(i : ℕ)]!) := fun i =>
      rep_of_validA (allLt_spec hxv i.2)
    refine ⟨fun i => permOfArr 315 xs[(i : ℕ)]!, fun i => ⟨?_, ?_⟩, ?_⟩
    · have := allLt_spec hxs (show (i : ℕ) < xs.size by rw [hsz]; exact i.2)
      rw [Bool.and_eq_true] at this
      exact (j2InP_iff _ _ (hrx i)).mp this.1
    · intro e hE
      have hgen : ∀ g ∈ permsA 315 j2E0, permOfArr 315 xs[(i : ℕ)]! * g =
          g * permOfArr 315 xs[(i : ℕ)]! := by
        rintro _ ⟨j, hj, rfl⟩
        have := allLt_spec hxs (show (i : ℕ) < xs.size by rw [hsz]; exact i.2)
        rw [Bool.and_eq_true] at this
        exact eq_of_eqA (rep_compA (hrx i) (hrep j hj)) (rep_compA (hrep j hj) (hrx i))
          (allLt_spec this.2 hj)
      exact (commute_of_mem_closure (S := permsA 315 j2E0)
        (T := {permOfArr 315 xs[(i : ℕ)]!}) (fun g hg _ ht => by
          rw [Set.mem_singleton_iff] at ht
          rw [ht]
          exact (hgen g hg).symm) hE (subset_closure rfl)).symm
    ·
      have hv : ∀ i < 8, validA 315 xs[i]! = true := fun i hi => allLt_spec hxv hi
      have e0 := permOfArr_eq_of_rep (rep_commutatorA (hv 0 (by norm_num)) (hv 1 (by norm_num)))
      have e1 := permOfArr_eq_of_rep (rep_commutatorA (hv 2 (by norm_num)) (hv 3 (by norm_num)))
      have e2 := permOfArr_eq_of_rep (rep_commutatorA (hv 4 (by norm_num)) (hv 5 (by norm_num)))
      have e3 := permOfArr_eq_of_rep (rep_commutatorA (hv 6 (by norm_num)) (hv 7 (by norm_num)))
      have f0 := permOfArr_eq_of_rep (rep_commutatorA h0 h1)
      have f1 := permOfArr_eq_of_rep (rep_commutatorA h2 h3)
      have htgt : Rep 315 (compA 315 j2E0[0]! (conjInvA 315 a0 j2E0[0]!))
          (j2e0 * (a₀⁻¹ * j2e0 * a₀)) := rep_compA he (rep_conjInvA ha0v he)
      have := eq_of_eqA (rep_commutatorA hm0 hm1) htgt htop
      rw [f0, f1, e0, e1, e2, e3] at this
      exact this
  ·
    refine ⟨permOfArr 315 c0, (j2InP_iff _ _ (rep_of_validA hc0v)).mp hc0P, ?_⟩
    exact eq_of_eqA (rep_conjA hc0v he) rep_permA hc0e
  ·
    have hrs : ∀ i < 2, Rep 315 cent2BStrong[i]! (permOfArr 315 cent2BStrong[i]!) := by
      intro i hi
      interval_cases i
      · exact rep_of_validA hs0
      · exact rep_of_validA hs1
    have hvs : ∀ i < 2, validA 315 cent2BStrong[i]! = true := by
      intro i hi
      interval_cases i
      · exact hs0
      · exact hs1
    set N := closure (permsA 315 gN) with hN
    have hrg : ∀ j < gN.size, Rep 315 gN[j]! (permOfArr 315 gN[j]!) := fun j hj =>
      rep_of_validA (enumOK_gens_valid hcN hj)
    have hconjN : ∀ i < 2, ∀ n ∈ N, permOfArr 315 cent2BStrong[i]! * n *
        (permOfArr 315 cent2BStrong[i]!)⁻¹ ∈ N ∧
        (permOfArr 315 cent2BStrong[i]!)⁻¹ * n * permOfArr 315 cent2BStrong[i]! ∈ N := by
      intro i hi n hn
      set s := permOfArr 315 cent2BStrong[i]!
      have hm1 : N.map (MulAut.conj s).toMonoidHom ≤ N := by
        rw [hN, MonoidHom.map_closure, closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        have h1 := allLt_spec (allLt_spec hnorm hi) hj
        rw [Bool.and_eq_true] at h1
        exact mem_of_inEnum hcN (rep_conjA (hvs i hi) (hrg j hj)) h1.1
      have hm2 : N.map (MulAut.conj s⁻¹).toMonoidHom ≤ N := by
        rw [hN, MonoidHom.map_closure, closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        have h1 := allLt_spec (allLt_spec hnorm hi) hj
        rw [Bool.and_eq_true] at h1
        have := mem_of_inEnum hcN (rep_conjInvA (hvs i hi) (hrg j hj)) h1.2
        simpa [MulAut.conj_apply] using this
      refine ⟨?_, ?_⟩
      · simpa [MulAut.conj_apply] using hm1 (mem_map_of_mem _ hn)
      · simpa [MulAut.conj_apply] using hm2 (mem_map_of_mem _ hn)
    have hC : centralizerIn P permA =
        closure {g | ∃ i < 2, permOfArr 315 cent2BStrong[i]! = g} := by
      rw [centralizerIn_P_permA.1, cent2BChain, ofArrays_originalSubgroup]
    have hsN : ⁅permOfArr 315 cent2BStrong[0]!, permOfArr 315 cent2BStrong[1]!⁆ ∈ N :=
      mem_of_inEnum hcN (rep_commutatorA hs0 hs1) hss
    have hder : ⁅centralizerIn P permA, centralizerIn P permA⁆ ≤ N := by
      rw [hC]
      refine commutator_closure_le ?_ ?_
      · rintro _ ⟨i, hi, rfl⟩ n hn
        exact hconjN i hi n hn
      · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
        interval_cases i <;> interval_cases j
        · rw [commutatorElement_self]; exact one_mem N
        · exact hsN
        · rw [← commutatorElement_inv]; exact inv_mem hsN
        · rw [commutatorElement_self]; exact one_mem N
    intro z hz hz2 hz1
    obtain ⟨i, hi, hri⟩ := enumOK_exists_rep j2PS_lt hcN (hder hz)
    have h1 := allLt_spec hinv hi
    simp only [Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h1
    rcases h1 with (h1 | h1) | h1
    · have : eqA 315 (compA 315 (enumBfs 315 gN j2PS j2Fuel).pts[i]!
          (enumBfs 315 gN j2PS j2Fuel).pts[i]!) (idA 315) = true :=
        (eqA_iff (rep_compA hri hri) rep_idA).mpr (by rw [← sq]; exact hz2)
      rw [this] at h1
      exact Bool.noConfusion h1
    · exact absurd (eq_of_eqA hri rep_idA h1) hz1
    · rw [Models.fixCount_eq hri]
      exact h1

theorem endFacts_of_j2EndFacts (h : J2EndFacts) :
    EndFacts R P j2E0Sub j2e0 (fun σ => Models.fixCount σ = 15) where
  le_P := h.le_P
  mem := subset_closure ⟨0, by decide, rfl⟩
  Q_of_mem := h.fixCount_eq
  Q_conj := fun g _ x hx => by
    rw [Models.fixCount_conj]
    exact hx
  exists_conj := h.exists_conj
  not_Q := by
    obtain ⟨c₀, hc₀P, hc₀⟩ := h.exists_permA
    intro z hz' hz2 hz1 hQ
    have hle : P ⊓ Subgroup.centralizer (j2E0Sub : Set (Equiv.Perm (Fin 315))) ≤
        P ⊓ Subgroup.centralizer {j2e0} :=
      inf_le_inf_left _ (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr (subset_closure ⟨0, by decide, rfl⟩)))
    have hz := Subgroup.commutator_mono hle hle hz'
    have hmap : (P ⊓ Subgroup.centralizer {j2e0}).map (MulAut.conj c₀).toMonoidHom ≤
        centralizerIn P permA := by
      rintro _ ⟨y, ⟨hyP, hyC⟩, rfl⟩
      refine mem_centralizerIn.mpr ⟨?_, ?_⟩
      · change c₀ * y * c₀⁻¹ ∈ P
        exact P.mul_mem (P.mul_mem hc₀P hyP) (P.inv_mem hc₀P)
      · change c₀ * y * c₀⁻¹ * permA = permA * (c₀ * y * c₀⁻¹)
        have hyc : y * j2e0 = j2e0 * y := mem_centralizer_singleton_iff.mp hyC
        rw [← hc₀]
        calc c₀ * y * c₀⁻¹ * (c₀ * j2e0 * c₀⁻¹) = c₀ * (y * j2e0) * c₀⁻¹ := by group
          _ = c₀ * (j2e0 * y) * c₀⁻¹ := by rw [hyc]
          _ = c₀ * j2e0 * c₀⁻¹ * (c₀ * y * c₀⁻¹) := by group
    have hz' : c₀ * z * c₀⁻¹ ∈ ⁅centralizerIn P permA, centralizerIn P permA⁆ := by
      have h1 : (MulAut.conj c₀).toMonoidHom z ∈
          (⁅P ⊓ Subgroup.centralizer {j2e0}, P ⊓ Subgroup.centralizer {j2e0}⁆).map
            (MulAut.conj c₀).toMonoidHom := mem_map_of_mem _ hz
      rw [Subgroup.map_commutator] at h1
      exact commutator_mono hmap hmap h1
    refine h.fixCount_ne _ hz' ?_ ?_ ?_
    · rw [conj_pow, hz2, mul_one, mul_inv_cancel]
    · intro h1
      apply hz1
      have := congrArg (fun y => c₀⁻¹ * y * c₀) h1
      simpa [mul_assoc] using this
    · rw [Models.fixCount_conj]
      exact hQ

end CFSG.ComponentClassification.RankTwoSporadic.J2
