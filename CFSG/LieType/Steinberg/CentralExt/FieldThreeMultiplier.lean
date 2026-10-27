module

public import CFSG.LieType.Steinberg.CentralExt.E6E7Multiplier
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LieType.Steinberg.CentralExt.SpinTorus

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg.CentralExt.AdjointClosed

namespace CFSG.LieType.Steinberg.CentralExt.FieldThree

theorem exists_even_odd {ι : Type*} [Fintype ι] [DecidableEq ι] {u v : ι → ℤ}
    (hv : ∃ j, ¬ 2 ∣ v j) (huv : ∃ i, ¬ 2 ∣ (u i - v i)) :
    ∃ m : ι → ℤ, 2 ∣ ∑ j, m j * u j ∧ ¬ 2 ∣ ∑ j, m j * v j := by
  have hsingle : ∀ (w : ι → ℤ) (j : ι), ∑ l, (Pi.single j 1 : ι → ℤ) l * w l = w j := by
    intro w j
    simp [Pi.single_apply]
  by_cases hA : ∃ j, ¬ 2 ∣ v j ∧ 2 ∣ u j
  · obtain ⟨j, hvj, huj⟩ := hA
    exact ⟨Pi.single j 1, by rw [hsingle]; exact huj, by rw [hsingle]; exact hvj⟩
  · push Not at hA
    obtain ⟨i, hi⟩ := huv
    obtain ⟨j, hj⟩ := hv
    have huj : ¬ 2 ∣ u j := hA j hj
    have hvi : 2 ∣ v i := by
      by_contra h
      exact hi (by have := hA i h; omega)
    have hui : ¬ 2 ∣ u i := by omega
    refine ⟨Pi.single i 1 + Pi.single j 1, ?_, ?_⟩
    · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hsingle]
      omega
    · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hsingle]
      omega

variable {τ : Tag}

theorem two_ne_zero_of_card_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    (2 : K) ≠ 0 := fun h0 => by
  have hev := (SpinTorus.two_eq_zero_iff_even_card).1 h0
  rw [hK] at hev
  exact absurd hev (by decide)

theorem neg_one_ne_one_of_card_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    (-1 : Kˣ) ≠ 1 := fun h => by
  apply two_ne_zero_of_card_three hK
  have := congrArg (fun u : Kˣ => (u : K)) h
  simp only [Units.val_neg, Units.val_one] at this
  linear_combination -this

theorem cartanCoord_sub (γ δ : Fin τ.rank → ℤ) (i : Fin τ.rank) :
    cartanCoord (γ - δ) i = cartanCoord γ i - cartanCoord δ i := by
  simp only [cartanCoord, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

section Parity

theorem two_dvd_iform_self (v : Fin τ.rank → ℤ) : 2 ∣ iform v v := by
  have key : ((iform v v : ℤ) : ZMod 2) = 0 := by
    simp only [iform, Int.cast_sum, Int.cast_mul]
    rw [← Finset.sum_product']
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ -
      simp only
      rw [symmetrizedCartan_symm τ j i]
      ring_nf
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [show ((v i : ZMod 2) * ((τ.symmetrizedCartan i j : ℤ) : ZMod 2) * (v j : ZMod 2) * 2) = 0 by
        rw [h2, mul_zero]]
    · rintro ⟨i, j⟩ - hne heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      apply hne
      simp only
      rw [symmetrizedCartan_apply, Tag.cartan_self]
      push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, mul_zero, mul_zero, zero_mul]
    · intro _ _
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    · intro _ _
      rfl
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 key

open Matrix in
theorem exists_sep_neg_one {k : Type} [Field k] (h2 : (2 : k) ≠ 0)
    (hsym : ∀ i, τ.symmetrizer i i = 1) {e : ℤ} (he : ¬ 2 ∣ e)
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hB : B * τ.cartan = e • 1)
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hli : LinIndepPair γ δ) :
    ∃ t : Fin τ.rank → kˣ, rootChar k γ t = 1 ∧ rootChar k δ t ≠ 1 := by
  have hnorm : ∀ {β : Fin τ.rank → ℤ}, IsRoot τ β → iform β β = 2 := fun hβ => by
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hβ
    rw [hj, hsym]
    norm_num
  have hlift : ∀ z : Fin τ.rank → ℤ, (∀ i, 2 ∣ cartanCoord z i) → ∀ a, 2 ∣ z a := by
    intro z hz a
    have h1 : (B *ᵥ (τ.cartan *ᵥ z)) a = e * z a := by
      rw [Matrix.mulVec_mulVec, hB, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
        smul_eq_mul]
    have h2' : 2 ∣ (B *ᵥ (τ.cartan *ᵥ z)) a := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (hz i) _
    rw [h1] at h2'
    exact (Int.prime_two.dvd_mul.1 h2').resolve_left he
  have hdouble : ∀ z : Fin τ.rank → ℤ, (∀ a, 2 ∣ z a) → ∃ y, z = (2 : ℤ) • y := by
    intro z hz
    choose y hy using hz
    exact ⟨y, funext fun a => by simp [hy a]⟩
  have hv : ∃ j, ¬ 2 ∣ cartanCoord δ j := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy⟩ := hdouble δ (hlift δ hcon)
    have hn := hnorm hδ
    rw [hy, iform_smul_left, iform_smul_right] at hn
    omega
  have hne : γ ≠ δ := fun h => by
    have := hli 1 (-1) (by rw [h]; simp)
    omega
  have hne' : γ ≠ -δ := fun h => by
    have := hli 1 1 (by rw [h]; simp)
    omega
  have huv : ∃ i, ¬ 2 ∣ (cartanCoord γ i - cartanCoord δ i) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy⟩ := hdouble (γ - δ) (hlift (γ - δ) fun i => by
      rw [cartanCoord_sub]
      exact hcon i)
    have hcs := iform_sq_lt hγ hδ hne hne'
    rw [hnorm hγ, hnorm hδ] at hcs
    have hval : iform (γ - δ) (γ - δ) = 4 - 2 * iform γ δ := by
      rw [iform_sub_left, iform_sub_right, iform_sub_right, hnorm hγ, hnorm hδ, iform_comm δ γ]
      ring
    rw [hy, iform_smul_left, iform_smul_right] at hval
    obtain ⟨c, hc⟩ := two_dvd_iform_self y
    have hs : iform γ δ ≤ 1 ∧ -1 ≤ iform γ δ := ⟨by nlinarith, by nlinarith⟩
    omega
  obtain ⟨m, hmu, hmv⟩ := exists_even_odd hv huv
  refine ⟨tvec (-1) m, ?_, ?_⟩
  · rw [rootChar_tvec]
    exact Even.neg_one_zpow (even_iff_two_dvd.2 hmu)
  · rw [rootChar_tvec, Odd.neg_one_zpow (Int.not_even_iff_odd.1 fun h => hmv
      (even_iff_two_dvd.1 h))]
    intro h
    apply h2
    have := congrArg (fun u : kˣ => (u : k)) h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this

end Parity

section E8

variable {K : Type} [Field K] [Finite K]

theorem e8_three_exists_section_of_central (hK : Nat.card K = 3) {E : Type*} [Group E]
    {π : E →* adjointGroup .E8 K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : adjointGroup .E8 K →* E, ∀ g, π (σ g) = g := by
  obtain ⟨-, ⟨O⟩, hP, -⟩ := e8_conclusionB K
  obtain ⟨C, -, hC⟩ := e8_commutatorFormula K O
  have hBA : cartanInvE8 * Tag.cartan .E8 = (1 : ℤ) • 1 := by
    rw [one_smul]
    exact mul_eq_one_comm.1 cartan_mul_cartanInvE8
  exact exists_section_of_torus_of_sep (isFiniteType_cartan .E8)
    (RG := rootGroup (rootOperatorFamily .E8) K) (by omega) (neg_one_ne_one_of_card_three hK)
    (adjDatum_roots _ K) (e8_chevalleyExtras K O C hC) hP torusAdjHom
    (fun t γ _ c => torusAdj_conj_xPar t γ c)
    (fun _ hγ => exists_unitVec cartan_mul_cartanInvE8 hγ)
    (fun _ _ hγ hδ hli => exists_sep_neg_one (two_ne_zero_of_card_three hK)
      (fun i => by simp [Tag.symmetrizer]) (by decide) hBA hγ hδ hli) hπ hcen

end E8

section E8Multiplier

variable {K : Type} [Field K] [Finite K]

theorem e8_three_hopfMultiplier (hK : Nat.card K = 3) :
    commutator (AdjointQuotient .E8 K) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E8 K)) := by
  have : Group.IsPerfect ↥(adjointGroup .E8 K) := isPerfect_e8 K
  exact AdjointClosed.hopfMultiplier_subsingleton center_adjointGroup_eq_bot
    fun π hπ hcen => e8_three_exists_section_of_central hK hπ hcen

end E8Multiplier

section E6

@[expose] def e6BMat : Matrix (Fin (Tag.rank .E6)) (Fin (Tag.rank .E6)) ℤ :=
  Matrix.of MinusculeClosed.e6B

theorem e6BMat_mul_cartan : e6BMat * Tag.cartan .E6 = (3 : ℤ) • 1 := by
  decide +kernel

theorem e6_three_exists_section_of_central
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {E : Type*} [Group E]
    {π : E →* e6Data_valid.minGroup K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : e6Data_valid.minGroup K →* E, ∀ g, π (σ g) = g := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card_three hK
  have hw : (-1 : Kˣ) ≠ 1 := neg_one_ne_one_of_card_three hK
  obtain ⟨-, ⟨O⟩, hP, -⟩ := e6_conclusionB K
  obtain ⟨C, -, hC⟩ := e6Datum_commutatorFormula K _ (roots_eq isFiniteType_cartan_E6) O
  exact exists_section_of_torus_of_sep isFiniteType_cartan_E6 (RG := e6Data_valid.rootGroup K)
    (by omega) hw (e6Data_valid.minDatum_roots isFiniteType_cartan_E6 K)
    (e6_chevalleyExtras K O C hC) hP (MinusculeClosed.minTorus e6Data_valid K)
    (fun t _ hγ c => MinusculeClosed.minTorus_conj_xm e6Data_valid K t hγ c)
    (fun _ hγ => exists_unitVec_of_neighbour neighbour_E6 hγ)
    (fun _ _ hγ hδ hli => exists_sep_neg_one h2 (fun i => by simp [Tag.symmetrizer])
      (by decide) e6BMat_mul_cartan hγ hδ hli) hπ hcen

variable {K : Type} [Field K] [Finite K]

theorem e6_three_hopfMultiplier (hK : Nat.card K = 3) :
    commutator (AdjointQuotient .E6 K) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E6 K) ≃*
        Multiplicative (ZMod (Nat.gcd 3 (Nat.card K - 1)))) := by
  have : Group.IsPerfect ↥(e6Data_valid.minGroup K) := isPerfect_e6 K
  have hker : (e6Isogeny K).ker = Subgroup.center ↥(e6Data_valid.minGroup K) :=
    le_antisymm (ker_le_center_of_isQuasisimple (isQuasisimple_e6 K) (e6Isogeny_ne_one K))
      (MinusculeClosed.center_le_ker_of_surjective (e6Isogeny_surjective K)
        center_adjointGroup_eq_bot)
  obtain ⟨hperf, ⟨e⟩⟩ := MinusculeClosed.hopfMultiplier_of_isogeny (e6Isogeny K)
    (e6Isogeny_surjective K) hker center_adjointGroup_eq_bot
    fun π hπ hcen => e6_three_exists_section_of_central hK hπ hcen
  obtain ⟨hcard, hcyc⟩ := MinusculeClosed.card_center_e6 K
  rw [← hcard]
  exact ⟨hperf, ⟨e.trans (zmodCyclicMulEquiv hcyc).symm⟩⟩

end E6

end CFSG.LieType.Steinberg.CentralExt.FieldThree
