module

public import CFSG.LieType.Steinberg.CentralExt.FieldThreeMultiplier

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg.CentralExt.AdjointClosed

namespace CFSG.LieType.Steinberg.CentralExt.FieldThree

variable {τ : Tag}

theorem cartanCoord_add (γ δ : Fin τ.rank → ℤ) (i : Fin τ.rank) :
    cartanCoord (γ + δ) i = cartanCoord γ i + cartanCoord δ i := by
  simp only [cartanCoord, Pi.add_apply, mul_add, Finset.sum_add_distrib]

section Parity

theorem iform_eq_sum_cartanCoord (y u : Fin τ.rank → ℤ) :
    iform y u = ∑ i, y i * τ.symmetrizer i i * cartanCoord u i := by
  simp only [iform, cartanCoord, symmetrizedCartan_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem two_dvd_iform_of_cartanCoord {u : Fin τ.rank → ℤ} (hu : ∀ i, 2 ∣ cartanCoord u i)
    (y : Fin τ.rank → ℤ) : 2 ∣ iform y u := by
  rw [iform_eq_sum_cartanCoord]
  exact Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (hu i) _

theorem exists_sep_neg_one_of_mod_eight {k : Type} [Field k] (h2 : (2 : k) ≠ 0)
    (hsym : ∀ i, τ.symmetrizer i i = 1)
    (hker : ∀ z : Fin τ.rank → ℤ, (∀ i, 2 ∣ cartanCoord z i) →
      iform z z % 8 = 0 ∨ iform z z % 8 = 6)
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hli : LinIndepPair γ δ) :
    ∃ t : Fin τ.rank → kˣ, rootChar k γ t = 1 ∧ rootChar k δ t ≠ 1 := by
  have hnorm : ∀ {β : Fin τ.rank → ℤ}, IsRoot τ β → iform β β = 2 := fun hβ => by
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hβ
    rw [hj, hsym]
    norm_num
  have hv : ∃ j, ¬ 2 ∣ cartanCoord δ j := by
    by_contra hcon
    push Not at hcon
    have := hker δ hcon
    rw [hnorm hδ] at this
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
    have hm := hker (γ - δ) fun i => by
      rw [cartanCoord_sub]
      exact hcon i
    have hp := hker (γ + δ) fun i => by
      rw [cartanCoord_add]
      have := hcon i
      omega
    have hcs := iform_sq_lt hγ hδ hne hne'
    rw [hnorm hγ, hnorm hδ] at hcs
    have hval : iform (γ - δ) (γ - δ) = 4 - 2 * iform γ δ := by
      rw [iform_sub_left, iform_sub_right, iform_sub_right, hnorm hγ, hnorm hδ, iform_comm δ γ]
      ring
    have hval' : iform (γ + δ) (γ + δ) = 4 + 2 * iform γ δ := by
      rw [iform_add_left, iform_add_right, iform_add_right, hnorm hγ, hnorm hδ, iform_comm δ γ]
      ring
    rw [hval] at hm
    rw [hval'] at hp
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

theorem e7_two_dvd_or {z : Fin (Tag.rank .E7) → ℤ} (hz : ∀ i, 2 ∣ cartanCoord z i) :
    (∀ a, 2 ∣ z a) ∨ ∀ a, 2 ∣ (z - MinusculeClosed.e7c) a := by
  have hrow : ∀ i : Fin 7, 2 ∣ ∑ j : Fin 7, Tag.cartanE 7 i j * z j := hz
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  have h3 := hrow 3
  have h4 := hrow 4
  have h5 := hrow 5
  have h6 := hrow 6
  simp only [Fin.sum_univ_seven, Tag.cartanE] at h0 h1 h2 h3 h4 h5 h6
  norm_num at h0 h1 h2 h3 h4 h5 h6
  rcases Int.emod_two_eq_zero_or_one (z (1 : Fin 7)) with he | ho
  · left
    have key : ∀ a : Fin 7, 2 ∣ z a := by
      intro a
      fin_cases a <;> simp <;> omega
    exact key
  · right
    have key : ∀ a : Fin 7, 2 ∣ (z - MinusculeClosed.e7c) a := by
      intro a
      show 2 ∣ z a - MinusculeClosed.e7c a
      fin_cases a <;> simp [MinusculeClosed.e7c] <;> omega
    exact key

theorem e7_iform_e7c : iform (τ := .E7) MinusculeClosed.e7c MinusculeClosed.e7c = 6 := by
  decide +kernel

theorem e7_cartanCoord_e7c : ∀ i, 2 ∣ cartanCoord (τ := .E7) MinusculeClosed.e7c i := by
  decide +kernel

theorem e7_iform_mod_eight (z : Fin (Tag.rank .E7) → ℤ) (hz : ∀ i, 2 ∣ cartanCoord z i) :
    iform z z % 8 = 0 ∨ iform z z % 8 = 6 := by
  rcases e7_two_dvd_or hz with he | ho
  · choose y hy using he
    have hzy : z = (2 : ℤ) • y := funext fun a => by simp [hy a]
    obtain ⟨c, hc⟩ := two_dvd_iform_self y
    left
    rw [hzy, iform_smul_left, iform_smul_right, hc]
    omega
  · choose y hy using ho
    have hzy : z = MinusculeClosed.e7c + (2 : ℤ) • y := funext fun a => by
      have := hy a
      simp only [Pi.sub_apply] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      omega
    obtain ⟨c, hc⟩ := two_dvd_iform_self y
    obtain ⟨d, hd⟩ := two_dvd_iform_of_cartanCoord e7_cartanCoord_e7c y
    have hsy : iform MinusculeClosed.e7c y = 2 * d := by rw [iform_comm, hd]
    right
    rw [hzy]
    simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right, e7_iform_e7c,
      hsy, hd, hc]
    omega

end Parity

section E7

theorem e7_three_exists_section_of_central
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {E : Type*} [Group E]
    {π : E →* e7Data_valid.minGroup K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : e7Data_valid.minGroup K →* E, ∀ g, π (σ g) = g := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card_three hK
  have hw : (-1 : Kˣ) ≠ 1 := neg_one_ne_one_of_card_three hK
  obtain ⟨-, ⟨O⟩, hP, -⟩ := e7_conclusionB K
  obtain ⟨C, -, hC⟩ := e7Datum_commutatorFormula K _ (roots_eq isFiniteType_cartan_E7) O
  exact exists_section_of_torus_of_sep isFiniteType_cartan_E7 (RG := e7Data_valid.rootGroup K)
    (by omega) hw (e7Data_valid.minDatum_roots isFiniteType_cartan_E7 K)
    (e7_chevalleyExtras K O C hC) hP (MinusculeClosed.minTorus e7Data_valid K)
    (fun t _ hγ c => MinusculeClosed.minTorus_conj_xm e7Data_valid K t hγ c)
    (fun _ hγ => exists_unitVec_of_neighbour neighbour_E7 hγ)
    (fun _ _ hγ hδ hli => exists_sep_neg_one_of_mod_eight h2 (fun i => by simp [Tag.symmetrizer])
      e7_iform_mod_eight hγ hδ hli) hπ hcen

variable {K : Type} [Field K] [Finite K]

theorem e7_three_hopfMultiplier (hK : Nat.card K = 3) :
    commutator (AdjointQuotient .E7 K) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E7 K) ≃*
        Multiplicative (ZMod (Nat.gcd 2 (Nat.card K - 1)))) := by
  have : Group.IsPerfect ↥(e7Data_valid.minGroup K) := isPerfect_e7 K
  have hker : (e7Isogeny K).ker = Subgroup.center ↥(e7Data_valid.minGroup K) :=
    le_antisymm (ker_le_center_of_isQuasisimple (isQuasisimple_e7 K) (exists_e7Isogeny_ne_one K))
      (MinusculeClosed.center_le_ker_of_surjective (e7Isogeny_surjective K)
        center_adjointGroup_eq_bot)
  obtain ⟨hperf, ⟨e⟩⟩ := MinusculeClosed.hopfMultiplier_of_isogeny (e7Isogeny K)
    (e7Isogeny_surjective K) hker center_adjointGroup_eq_bot
    fun π hπ hcen => e7_three_exists_section_of_central hK hπ hcen
  obtain ⟨hcard, hcyc⟩ := MinusculeClosed.card_center_e7 K
  rw [← hcard]
  exact ⟨hperf, ⟨e.trans (zmodCyclicMulEquiv hcyc).symm⟩⟩

end E7

end CFSG.LieType.Steinberg.CentralExt.FieldThree
