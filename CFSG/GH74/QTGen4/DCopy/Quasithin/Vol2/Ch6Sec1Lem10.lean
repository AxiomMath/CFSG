module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem10
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem two_le_rParam_F4 (h311 : Theorem311Stmt) (h432 : Stmt4_3_2_F4) (h : Hyp611Nat G T M L V n) :
    (2 : ℕ∞) ≤ rParam V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE := h.hypE61_F4 h432
  obtain ⟨U₀, hU₀V, hU₀, hTU₀⟩ := h.exists_hyperplane_normalized
  have hVcard : Nat.card V = 2 ^ n * 2 ^ n := h.natural.card_eq
  have hU₀card : Nat.card U₀ * 2 = 2 ^ n * 2 ^ n := by
    have := card_mul_relIndex_of_le hU₀V
    rw [hU₀, hVcard] at this
    exact this
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hU₀1 : U₀ ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hU₀card
    nlinarith

  have hCM : M ⊓ Subgroup.centralizer (U₀ : Set G) ≤ M ⊓ Subgroup.centralizer (V : Set G) := by
    rintro m ⟨hmM, hmC⟩
    refine ⟨hmM, ?_⟩
    by_contra hmV
    have hmN : m ∈ Subgroup.normalizer (V : Set G) :=
      (h.normalizer_le hU₀1 hU₀V ⟨hmM, Subgroup.centralizer_le_normalizer _ hmC⟩).2
    have hle := h.data.card_fixed_le_two_pow ⟨m, hmN⟩ (h.normal hmM) hmV
    have hsub : U₀ ≤ V ⊓ Subgroup.centralizer ({m} : Set G) := fun u hu =>
      ⟨hU₀V hu, Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        exact (Subgroup.mem_centralizer_iff.mp hmC u hu).symm⟩
    have := (Subgroup.card_le_of_le hsub).trans hle
    nlinarith
  have hres : twoPrimeResidual (M ⊓ Subgroup.centralizer (U₀ : Set G)) ≤
      M ⊓ Subgroup.centralizer (V : Set G) := (twoPrimeResidual_le_self _).trans hCM
  have hCU₀M := E6.e6_13 h311 hE hU₀V hU₀1 hres hTU₀
  have hCU₀N : Subgroup.centralizer (U₀ : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    fun c hc => (h.normalizer_le hU₀1 hU₀V ⟨hCU₀M hc, Subgroup.centralizer_le_normalizer _ hc⟩).2
  unfold rParam
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hCU⟩ := hU
  have hrel : U.relIndex V ∣ 2 ^ (n + n) := by
    rw [pow_add, ← hVcard]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrel
  have hm : mQuot V U = j := by
    unfold mQuot
    rw [hj, padicValNat.prime_pow]
  rw [hm]
  by_contra hlt
  push Not at hlt
  have hj2 : j < 2 := by exact_mod_cast hlt
  interval_cases j
  ·
    have hVU : V ≤ U := Subgroup.relIndex_eq_one.mp (by rw [hj]; rfl)
    have hUV' : U = V := le_antisymm hUV hVU
    rw [hUV'] at hCU
    exact hCU (Subgroup.centralizer_le_normalizer _)
  · obtain ⟨l, hlL, hUl⟩ := h.exists_conj_hyperplane hUV hU₀V (by rw [hj]; rfl) hU₀
    apply hCU
    have hlN : l ∈ Subgroup.normalizer (V : Set G) := h.data.le_normalizer hlL
    rw [hUl, ← E3.conjSubgroup_centralizer]
    calc conjSubgroup (Subgroup.centralizer (U₀ : Set G)) l ≤
        conjSubgroup (Subgroup.normalizer (V : Set G)) l := E3.conjSubgroup_mono_left l hCU₀N
      _ = Subgroup.normalizer (V : Set G) :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hlN)

end Hyp611Nat

theorem stmt6_1_10_F4 (h311 : Theorem311Stmt) (h432 : Stmt4_3_2_F4) (hE63 : Ch6InE63) :
    Stmt6_1_10_F4 := by
  intro G _ _ T M L V n h
  have hE := h.hypE61_F4 h432
  have hm : ∀ hV : IsElemAbelian 2 V, mParam (autI hV M) = n := fun hV =>
    h.mParam_autI hV h.L_le inf_le_left
  have hmtop : ∀ hV : IsElemAbelian 2 V, mParam (autI hV ⊤) = n := fun hV =>
    h.mParam_autI hV le_top (inf_le_right.trans hE.normalizer_le)
  have hr : (n : ℕ∞) ≤ rParam V := by
    rcases eq_or_lt_of_le h.two_le with hn | hn
    · subst hn
      exact_mod_cast h.two_le_rParam_F4 h311 h432
    · have := (hE63 G T M V hE h.toHyp611.isElemAbelian
        (by rw [hm]; exact hn)).1
      rwa [hm] at this
  have hs : ∀ hV : IsElemAbelian 2 V, sParam hV = n := fun hV => by
    unfold sParam
    rw [hmtop hV, min_eq_right hr]
    rfl
  exact ⟨hr, fun hV => ⟨hs hV, hm hV⟩, fun g hgN hgC => h.mQuot_conj_eq hs hgN hgC⟩

end CFSG.Quasithin.H13
