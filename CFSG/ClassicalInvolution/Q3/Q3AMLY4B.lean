module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY4A
public import CFSG.ClassicalInvolution.Q3.Q3AM289Lay

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.LY4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3AM (nbrLayer exactCore3_le_nbrLayer nbrLayer_le_centralizer
  conj_mem_nbrLayer conj_mem_oddCoreOf_of_mem_self)
open scoped commutatorElement

section Frame


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem eq_or_eq_of_mem_RSet_of_le (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) {P : Subgroup G}
    (hP : P ∈ RSet Ω) (hPS : P ≤ (S : Subgroup G)) : P = R ∨ P = T := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  by_contra hcon
  push Not at hcon
  obtain ⟨M, hM, hPM⟩ := exists_isSylow2In_of_mem_RSet hP
  have hMK : M ≠ K := by
    rintro rfl
    exact hcon.1 (T8R.eq_of_isSylow2In_of_le_sylow hPM hRsyl hPS hRS)
  have hcomm : Commutes P R :=
    l6_7_proved G Ω hΩ S P hP R hRΩ hPS hRS hcon.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hRΩ; omega)
  have hPc : P ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx z hzR)
  have hP8 := hΩ.eight_le_of_mem_RSet hP
  have hPN : P ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hK hM (Ne.symm hMK) hs.hz hPM.1 hPM.2.1
      (by omega) hPc
  have hMnbr : M ∈ omegaNbr Ω K := ⟨hM, hMK, P, hP, hPM.1, hPN⟩
  have hPY : P ≤ nbrLayer Ω K z := (le_inf hPM.1 hPc).trans (exactCore3_le_nbrLayer hMnbr)
  have hQT : (S : Subgroup G) ⊓ nbrLayer Ω K z = T := sylow_inf_layer hs hY
  have hcardP : Nat.card P = Nat.card T :=
    Disconnected.AschTight.Sec6Gen.natCard_isSylow2In_eq hΩ hM hJΩ hPM hTsyl
  have hPleT : P ≤ T := hQT ▸ le_inf hPS hPY
  have hPT : P = T := Subgroup.eq_of_le_of_card_ge hPleT (le_of_eq hcardP.symm)
  exact hcon.2 hPT

theorem fix_or_swap (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) :
    (conjSub s R = R ∧ conjSub s T = T) ∨ (conjSub s R = T ∧ conjSub s T = R) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRT := T8R.R_ne_T hs
  have hcl := hΩ.conjInvariant
  have hsS' : ∀ P ≤ (S : Subgroup G), conjSub s P ≤ (S : Subgroup G) := by
    intro P hP
    have := conjSub_mono (n := s) hP
    rwa [conjSub_eq_self_of_mem hsS] at this
  have hR' := eq_or_eq_of_mem_RSet_of_le hs hY (RSet.conj hcl hRΩ s) (hsS' R hRS)
  have hT' := eq_or_eq_of_mem_RSet_of_le hs hY (RSet.conj hcl hTΩ s) (hsS' T hTS)
  rcases hR' with hR' | hR'
  · left
    refine ⟨hR', ?_⟩
    rcases hT' with hT' | hT'
    · exact absurd ((conjSub_inj s).mp (hT'.trans hR'.symm)).symm hRT
    · exact hT'
  · right
    refine ⟨hR', ?_⟩
    rcases hT' with hT' | hT'
    · exact hT'
    · exact absurd ((conjSub_inj s).mp (hT'.trans hR'.symm)) (Ne.symm hRT)

theorem conj_zt_of_mem_sylow (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) : s * (z * t) * s⁻¹ = z * t := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have h8R := hΩ.eight_le_of_mem_RSet hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hTΩ
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  rcases fix_or_swap hs hY hsS with ⟨hR', hT'⟩ | ⟨hR', hT'⟩
  · have hK' : conjSub s K = K := Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hK hRΩ hRK hR'
    have hJ' : conjSub s J = J := Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hJΩ hTΩ hTJ hT'
    have h1 := hs.hz.conj_eq hK'
    have h2 := hs.ht.conj_eq hJ'
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = z * t := by rw [h1, h2]
  · have hK' : conjSub s K = J := hΩ.eq_of_le_of_le (hcl s K hK) hJΩ hTsyl.2.1 (by omega)
      (hR' ▸ conjSub_mono (n := s) hRK) hTJ
    have hJ' : conjSub s J = K := hΩ.eq_of_le_of_le (hcl s J hJΩ) hK hRsyl.2.1 (by omega)
      (hT' ▸ conjSub_mono (n := s) hTJ) hRK
    have h1 : s * z * s⁻¹ = t := (hs.ht.eq (hK' ▸ hs.hz.conj s)).symm
    have h2 : s * t * s⁻¹ = z := (hs.hz.eq (hJ' ▸ hs.ht.conj s)).symm
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = t * z := by rw [h1, h2]
      _ = z * t := hzt.symm

theorem mul_inv_mem_oddCoreOf_nbr (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) {L : Subgroup G}
    (hL : L ∈ omegaNbr Ω K) {y : G} (hy : IsUniqueInvolution L y) :
    y * t⁻¹ ∈ oddCoreOf (nbrLayer Ω K z) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨x, hxY, hLx⟩ := exists_conj_of_nbr_thin hΩ hs.hz hs.hJ hL hY
  have hyx : y = x * t * x⁻¹ := hy.eq (hLx ▸ hs.ht.conj x)
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have htc : t ∈ exactCore3 z J :=
    ⟨hs.ht.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  have hN : exactCore3 z J ≤ Subgroup.normalizer (oddCoreOf (nbrLayer Ω K z) : Set G) :=
    fun w hw => mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer (exactCore3_le_nbrLayer hs.hJ hw))
  have hxX' : x ∈ oddCoreOf (nbrLayer Ω K z) ⊔ exactCore3 z J := by
    rw [sup_comm, ← hY]
    exact hxY
  obtain ⟨o, ho, j, hj, rfl⟩ :=
    Disconnected.AschTight.Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hN hxX'
  have hjt : j * t * j⁻¹ = t := hs.ht.conj_eq (conjSub_eq_self_of_mem hj.1)
  have htn := hN htc
  have h1 : t * o⁻¹ * t⁻¹ ∈ oddCoreOf (nbrLayer Ω K z) :=
    (Subgroup.mem_normalizer_iff.mp htn o⁻¹).mp ((oddCoreOf (nbrLayer Ω K z)).inv_mem ho)
  have h2 : y * t⁻¹ = o * (t * o⁻¹ * t⁻¹) := by
    rw [hyx]
    calc o * j * t * (o * j)⁻¹ * t⁻¹ = o * (j * t * j⁻¹) * o⁻¹ * t⁻¹ := by group
      _ = o * (t * o⁻¹ * t⁻¹) := by rw [hjt]; group
  rw [h2]
  exact (oddCoreOf (nbrLayer Ω K z)).mul_mem ho h1

theorem conj_zt_mul_inv_mem_oddCoreOf (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) {y : G}
    (hy : y ∈ Subgroup.centralizer ({z} : Set G)) :
    y * (z * t) * y⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (nbrLayer Ω K z) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hyK : conjSub y K = K := centralizer_conjSub_eq hs hK hs.hz y hy
  have hJy : conjSub y J ∈ omegaNbr Ω K := hyK ▸ omegaNbr_conj hΩ.conjInvariant hs.hJ y
  have h1 := mul_inv_mem_oddCoreOf_nbr hs hY hJy (hs.ht.conj y)
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hy
    calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [this]
      _ = z := by group
  have hzX : z ∈ Subgroup.normalizer ((nbrLayer Ω K z : Subgroup G) : Set G) :=
    centralizer_le_normalizer_layer hs hK hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hzN := mem_normalizer_oddCore_of_mem_normalizer hzX
  have h2 : z * (y * t * y⁻¹ * t⁻¹) * z⁻¹ ∈ oddCoreOf (nbrLayer Ω K z) :=
    (Subgroup.mem_normalizer_iff.mp hzN _).mp h1
  have e : y * (z * t) * y⁻¹ * (z * t)⁻¹ = z * (y * t * y⁻¹ * t⁻¹) * z⁻¹ := by
    calc y * (z * t) * y⁻¹ * (z * t)⁻¹ = (y * z * y⁻¹) * (y * t * y⁻¹) * t⁻¹ * z⁻¹ := by group
      _ = z * (y * t * y⁻¹ * t⁻¹) * z⁻¹ := by rw [hyz]; group
  rw [e]
  exact h2

theorem thin_conj (hΩ : HypOmegaMod Ω) {K J : Subgroup G} {z : G}
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) (n : G) :
    nbrLayer Ω (conjSub n K) (n * z * n⁻¹) =
      exactCore3 (n * z * n⁻¹) (conjSub n J) ⊔
        oddCoreOf (nbrLayer Ω (conjSub n K) (n * z * n⁻¹)) := by
  rw [Q3AM.nbrLayer_conj hΩ.conjInvariant n K z, exactCore3_conjSub n z J, oddCoreOf_conjSub_eq]
  conv_lhs => rw [hY]
  exact Asc77.conjSub_sup n _ _

theorem thin_swap (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) :
    nbrLayer Ω J t = exactCore3 t K ⊔ oddCoreOf (nbrLayer Ω J t) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨g, hg⟩ := hs.stand.trans J hs.hJ.1
  have hgz : g * z * g⁻¹ = t := (hs.ht.eq (hg ▸ hs.hz.conj g)).symm
  have hKJ : K ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm (l6_2) hΩ hs.stand.mem hs.hJ.1 hs.hJ
  have hN₁ : conjSub g J ∈ omegaNbr Ω J := hg ▸ omegaNbr_conj hΩ.conjInvariant hs.hJ g
  have h1 := thin_conj hΩ hY g
  rw [hg, hgz] at h1
  obtain ⟨y, hyY, hyK⟩ := exists_conj_of_nbr_thin hΩ hs.ht hN₁ hKJ h1
  have hyC : y ∈ Subgroup.centralizer ({t} : Set G) := nbrLayer_le_centralizer Ω J t hyY
  have hyt : y * t * y⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hyC
    calc y * t * y⁻¹ = (t * y) * y⁻¹ := by rw [this]
      _ = t := by group
  have hcore : exactCore3 t K = conjSub y (exactCore3 t (conjSub g J)) := by
    have := exactCore3_conjSub y t (conjSub g J)
    rwa [hyt, hyK] at this
  have hYn : conjSub y (nbrLayer Ω J t) = nbrLayer Ω J t := conjSub_eq_self_of_mem hyY
  have hOn : conjSub y (oddCoreOf (nbrLayer Ω J t)) = oddCoreOf (nbrLayer Ω J t) := by
    rw [← oddCoreOf_conjSub_eq, hYn]
  calc nbrLayer Ω J t = conjSub y (nbrLayer Ω J t) := hYn.symm
    _ = conjSub y (exactCore3 t (conjSub g J) ⊔ oddCoreOf (nbrLayer Ω J t)) := by rw [← h1]
    _ = exactCore3 t K ⊔ oddCoreOf (nbrLayer Ω J t) := by
      rw [Asc77.conjSub_sup, hOn, hcore]

theorem not_mem_omegaNbr_of_four_le (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) {M : Subgroup G}
    (hM : M ∈ Ω) (h4 : 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G))) (hMJ : M ≠ J) :
    M ∉ omegaNbr Ω K := by
  intro hmem
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution hM
  obtain ⟨x, hxMS, hx4⟩ := exists_orderOf_four_of_four_le hu inf_le_left
    (S.isPGroup'.to_inf_right) h4
  have hxx : x * x = u := by
    have hx2 : (x * x) * (x * x) = 1 := by
      have h4' : x ^ 4 = (x * x) * (x * x) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [← h4', ← hx4]
      exact pow_orderOf_eq_one x
    rcases hu.unique _ (M.mul_mem hxMS.1 hxMS.1) hx2 with h | h
    · exfalso
      have h2 : x ^ 2 = 1 := by rw [pow_two]; exact h
      have h3 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [hx4] at h3
      omega
    · exact h
  have huS : u ∈ (S : Subgroup G) := hxx ▸ S.mul_mem hxMS.2 hxMS.2
  have hzu : z * u = u * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hmem hu
  have hua : u * (z * t) * u⁻¹ = z * t := conj_zt_of_mem_sylow hs hY huS
  have hut : u * t = t * u := by
    have e : t = z * (z * t) := by
      calc t = (z * z) * t := by rw [hs.hz.sq, one_mul]
        _ = z * (z * t) := by rw [mul_assoc]
    have h1 : Commute u (z * t) := by
      calc u * (z * t) = (u * (z * t) * u⁻¹) * u := by group
        _ = (z * t) * u := by rw [hua]
    have h2 : Commute u z := hzu.symm
    have h3 : Commute u (z * (z * t)) := h2.mul_right h1
    rw [← e] at h3
    exact h3
  have hO := mul_inv_mem_oddCoreOf_nbr hs hY hmem hu
  have ht2 : t * t = 1 := hs.ht.sq
  have hsq : (u * t⁻¹) * (u * t⁻¹) = 1 := by
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    rw [ht']
    calc u * t * (u * t) = (u * u) * (t * t) := by
          calc u * t * (u * t) = u * (t * u) * t := by group
            _ = u * (u * t) * t := by rw [← hut]
            _ = (u * u) * (t * t) := by group
      _ = 1 := by rw [hu.sq, ht2, one_mul]
  have h1 : u * t⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hO
      (ExactLayer.isPGroup_zpowers_of_sq_eq_one hsq)
  have hut' : u = t := by
    have : u = t⁻¹⁻¹ := by
      calc u = (u * t⁻¹) * t := by group
        _ = t := by rw [h1, one_mul]
        _ = t⁻¹⁻¹ := by rw [inv_inv]
    rw [this, inv_inv]
  apply hMJ
  have := hnt J hs.hJ.1 M ⟨hM, t, hs.ht, hut' ▸ hu⟩
  exact this

end Frame

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.LY4
