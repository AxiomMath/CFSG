module

public import CFSG.LargeExtraspecial.AS35WSp4
public import CFSG.LargeExtraspecial.AS35WL5U5
public import CFSG.LargeExtraspecial.AS35WComp
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank

namespace AS35W

variable {K : Type} [Field K] [Finite K]

theorem card_SL2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
    Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [LinearFlag.card_SL_eq (by norm_num)]
  simp

theorem sq_dvd_card_X0 (hodd : Odd (Nat.card K)) : Nat.card K ^ 2 ∣ Nat.card (X0 K) := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  set φ := (proj 2 K).comp (blkSL K)
  have hX0 : X0 K = φ.range := by
    have e : centralizer ({T1 K} : Set (StatedSp 2 K)) = (blkSL K).range := by
      ext x
      exact mem_centralizer_T1_iff h2
    rw [X0, e, MonoidHom.range_comp]
  have hker : Nat.card φ.ker ≤ 2 := by
    have hsub : ∀ x ∈ φ.ker, x ∈ ({1, ((negOneSL : Matrix.SpecialLinearGroup (Fin 2) K),
        (negOneSL : Matrix.SpecialLinearGroup (Fin 2) K))} :
        Finset (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)) := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have := (proj_blkSL_eq_one_iff x).1 hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases this with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
      · left
        exact Prod.ext (Subtype.ext h1) (Subtype.ext h1')
      · right
        exact Prod.ext (Subtype.ext (h1.trans rfl)) (Subtype.ext (h1'.trans rfl))
    exact (card_le_of_forall_mem _ _ hsub).trans Finset.card_le_two
  have hmul := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, Nat.card_prod, card_SL2] at hmul
  rw [hX0]
  have hdvd : Nat.card K ^ 2 ∣ Nat.card φ.ker * Nat.card φ.range := by
    rw [hmul]
    exact Dvd.intro ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - 1)) (by ring)
  refine (Nat.Coprime.dvd_of_dvd_mul_left ?_ hdvd)
  have hk : Nat.card φ.ker = 1 ∨ Nat.card φ.ker = 2 := by
    have := Nat.card_pos (α := φ.ker)
    omega
  rcases hk with hk | hk
  · rw [hk]; exact Nat.coprime_one_right _
  · rw [hk]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_right.mpr hodd)

theorem lsub_perfect (hK : 4 ≤ Nat.card K) : ⁅Lsub K, Lsub K⁆ = Lsub K := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have htop : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  rw [Lsub, MonoidHom.range_eq_map, Subgroup.map_map, ← map_commutator, htop]

theorem conj_mem_Lsub (hodd : Odd (Nat.card K)) (hK : 4 ≤ Nat.card K)
    {c : StatedProj (StatedSp 2 K)} (hc : c ∈ centralizer ({u2 K} : Set _))
    {n : StatedProj (StatedSp 2 K)} (hn : n ∈ Lsub K) : c * n * c⁻¹ ∈ Lsub K := by
  set φ := (MulAut.conj c).toMonoidHom
  have hM : (Lsub K).map φ ≤ centralizer {u2 K} := by
    rintro _ ⟨m, hm, rfl⟩
    exact (centralizer _).mul_mem ((centralizer _).mul_mem hc (Lsub_le_centralizer hm))
      ((centralizer _).inv_mem hc)
  have hperf : ⁅(Lsub K).map φ, (Lsub K).map φ⁆ = (Lsub K).map φ := by
    rw [← map_commutator, lsub_perfect hK]
  exact perfect_le_L (two_ne_zero_of_odd_card hodd) hM hperf ⟨n, hn, rfl⟩

open CFSG.ComponentClassification.CatFactsSmall.PSp43 in
theorem sp4W2Input :
    Sp4W2Input := by
  intro X _ _ p f hp hp2 hf h
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data h
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := CFSG.GH74.Generic.eq_three_of_pow_eq_three hp hf h3
    obtain ⟨e'⟩ := equiv_of_lieModel h
    exact W2Good.of_mulEquiv e' w2Good_QP45
  intro z hz
  exfalso
  have : Finite (StatedProj (StatedSp 2 K)) := Finite.of_equiv X e.toEquiv
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have hz' := hz.map e
  obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hodd (u := e z)
    (by rw [MulEquiv.orderOf_eq]; exact hz.orderOf_eq)
  have hz'' := hz'.map (MulAut.conj g⁻¹)
  have hgz : MulAut.conj g⁻¹ (e z) = g⁻¹ * e z * g := by rw [MulAut.conj_apply, inv_inv]
  rw [hgz] at hz''
  rcases hg with hg | hg <;> rw [hg] at hz''
  · have hdvd := (sq_dvd_card_X0 hodd).trans (hz''.card_dvd_of_le X0_le_centralizer)
    rw [hK] at hdvd
    exact h3 (eq_three_of_sq_dvd hp hp2 hf hdvd)
  · have h3' : Nat.card K ≠ 3 := hK ▸ h3
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have hK4 : 4 ≤ Nat.card K := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hs := isSimpleGroup_Lsub hK4
    have hne : Lsub K ≠ ⊥ := by
      have := hs
      exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance
    exact hz''.false_of_simple (Lsub K) Lsub_le_centralizer
      (fun c hc n hn => conj_mem_Lsub hodd hK4 hc hn) hs
      (exists_noncomm_of_perfect (lsub_perfect hK4) hne)

end AS35W

end CFSG.LargeExtraspecial
