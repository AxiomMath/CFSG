module

public import CFSG.ClassicalInvolution.Q3.Q3CLFrame
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
import CFSG.ClassicalInvolution.Asc77.AscT8FourGen
public import CFSG.ClassicalInvolution.Q3.Q3T8Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.GH74.Uniqueness CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8
  CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc

namespace T8

abbrev IsFrameInv := @CFSG.ClassicalInvolution.Asc77.T8.IsFrameInv

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_orderFour_centralizes_one_of_three (hΩ : HypOmegaGen Ω)
    {L : Subgroup G} (hL : L ∈ Ω) {b : G} (hb : IsUniqueInvolution L b) {S₀ : Subgroup G}
    (hS₀ : IsPGroup 2 S₀) {d u : G} (hd : d ∈ S₀) (hu : u ∈ S₀) (hdL : conjSub d L = L)
    (huL : conjSub u L = L) :
    ∃ x ∈ L, orderOf x = 4 ∧
      (x * d = d * x ∨ x * u = u * x ∨ x * (d * u) = (d * u) * x) := by
  have hcl : Subgroup.closure {d, u} ≤ S₀ := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hd
    · exact hu
  have hclN : Subgroup.closure {d, u} ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact mem_normalizer_iff_conjSub_eq.mpr hdL
    · exact mem_normalizer_iff_conjSub_eq.mpr huL
  obtain ⟨x, hxL, hxo, hx⟩ := Q3CL.T8.exists_orderFour_acting_by_sign hΩ hL hb (hS₀.to_le hcl)
    (fun q hq => mem_normalizer_iff_conjSub_eq.mp (hclN hq))
  refine ⟨x, hxL, hxo, ?_⟩
  have hdm : d ∈ Subgroup.closure {d, u} := Subgroup.subset_closure (by simp)
  have hum : u ∈ Subgroup.closure {d, u} := Subgroup.subset_closure (by simp)
  have hcomm : ∀ w : G, w * x * w⁻¹ = x → x * w = w * x := fun w h => by
    calc x * w = (w * x * w⁻¹) * w := by rw [h]
      _ = w * x := by group
  rcases hx d hdm with h | h
  · exact Or.inl (hcomm d h)
  rcases hx u hum with h' | h'
  · exact Or.inr (Or.inl (hcomm u h'))
  · refine Or.inr (Or.inr (hcomm (d * u) ?_))
    calc d * u * x * (d * u)⁻¹ = d * (u * x * u⁻¹) * d⁻¹ := by group
      _ = d * x⁻¹ * d⁻¹ := by rw [h']
      _ = (d * x * d⁻¹)⁻¹ := by group
      _ = x := by rw [h, inv_inv]

theorem exists_orderFour_centralizes_mul_conj (hΩ : HypOmegaGen Ω) {M P : Subgroup G} {S : Sylow 2
    G} (hM : M ∈ Ω) (hP : P ∈ RSet Ω)
    (hPM : P ≤ M) (hPS : P ≤ (S : Subgroup G)) {m : G} (hm : IsUniqueInvolution M m) {b : G}
    (hbS : b ∈ (S : Subgroup G)) (hbP : conjSub b P ≠ P) {L : Subgroup G} (hL : L ∈ Ω)
    (hb : IsUniqueInvolution L b)
    (hCb : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ x ∈ L, orderOf x = 4 ∧ x * (m * (b * m * b⁻¹)) = (m * (b * m * b⁻¹)) * x := by
  have hPsyl : IsSylow2In P M := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hM hP hPM
  have h8 : 8 ≤ Nat.card P := hΩ.eight_le_of_mem_RSet hP
  obtain ⟨r, hrP, hro⟩ := exists_orderOf_four_of_four_le hm hPM hPsyl.2.1 (by omega)
  have hPb : conjSub b P ∈ RSet Ω := RSet.conj hΩ.conjInvariant hP b
  have hPbS : conjSub b P ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := b) hPS
    rwa [conjSub_eq_self_of_mem hbS] at this
  have hcomm : Commutes P (conjSub b P) :=
    l6_7_proved G Ω hΩ S P hP _ hPb hPS hPbS (Ne.symm hbP)
  have hr4 : (r * r) * (r * r) = 1 := by
    have h4 : r ^ 4 = (r * r) * (r * r) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← h4, ← hro]
    exact pow_orderOf_eq_one r
  have hrr : r * r = m := by
    rcases hm.unique _ (M.mul_mem (hPM hrP) (hPM hrP)) hr4 with h | h
    · exfalso
      have h2 : r ^ 2 = 1 := by rw [pow_two]; exact h
      have h4 : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [hro] at h4
      omega
    · exact h
  have hbb : b * b = 1 := hb.sq
  have hbb' : b⁻¹ * b⁻¹ = 1 := by rw [← mul_inv_rev, hbb, inv_one]
  obtain ⟨r', hr'⟩ : ∃ r', r' = b * r * b⁻¹ := ⟨_, rfl⟩
  have hr'mem : r' ∈ conjSub b P := hr' ▸ conj_mem_conjSub hrP
  have hrr' : r * r' = r' * r := hcomm r hrP r' hr'mem
  have hbr' : b * r' * b⁻¹ = r := by
    rw [hr']
    calc b * (b * r * b⁻¹) * b⁻¹ = (b * b) * r * (b⁻¹ * b⁻¹) := by group
      _ = r := by rw [hbb, hbb']; group
  have hbq : b * (r * r') = (r * r') * b := by
    calc b * (r * r') = (b * r * b⁻¹) * (b * r' * b⁻¹) * b := by group
      _ = r' * r * b := by rw [← hr', hbr']
      _ = (r * r') * b := by rw [hrr']
  have hqL : conjSub (r * r') L = L := by
    refine mem_normalizer_iff_conjSub_eq.mp (hCb ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hbq.symm
  have hqS : r * r' ∈ (S : Subgroup G) := S.mul_mem (hPS hrP) (hPbS hr'mem)
  have hq2 : IsPGroup 2 (Subgroup.zpowers (r * r')) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hqS)
  obtain ⟨x, hxL, hxo, hx⟩ := Q3CL.T8.exists_orderFour_centralizes_sq hΩ hL hb hq2 hqL
  have hsq : (r * r') * (r * r') = m * (b * m * b⁻¹) := by
    have h1 : r' * r' = b * m * b⁻¹ := by
      calc r' * r' = (b * r * b⁻¹) * (b * r * b⁻¹) := by rw [← hr']
        _ = b * (r * r) * b⁻¹ := by group
        _ = b * m * b⁻¹ := by rw [hrr]
    calc (r * r') * (r * r') = r * (r' * r) * r' := by group
      _ = r * (r * r') * r' := by rw [← hrr']
      _ = (r * r) * (r' * r') := by group
      _ = m * (b * m * b⁻¹) := by rw [hrr, h1]
  exact ⟨x, hxL, hxo, hsq ▸ hx⟩

theorem mem_dComp_of_four_le_card (hΩ : HypOmegaGen Ω)
    {K : Subgroup G} (hcomp : dComp Ω K = dstarComp Ω K) (hK : K ∈ Ω)
    (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z : G} (hz : IsUniqueInvolution K z)
    {R : Subgroup G} (hR : R ∈ RSet Ω) (hRK : R ≤ K) {S : Sylow 2 G}
    (hRS : R ≤ (S : Subgroup G)) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hWS : W ≤ (S : Subgroup G)) {L : Subgroup G} (hL : L ∈ Ω)
    (hLS : 4 ≤ Nat.card ↥(L ⊓ (S : Subgroup G))) : L ∈ dComp Ω K := by
  obtain ⟨η, hη, rfl⟩ := hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (le_iSup₂_of_le V hV le_rfl).trans hWS
  obtain ⟨S', hS'η, hS'inv⟩ := id hη
  have h8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hR
  have hKS : 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le (by omega) (h8.trans (Subgroup.card_le_of_le (le_inf hRK hRS)))
  have hUK := l6_11_proved G Ω hΩ S η hη hηS K hK hKS
  have hUL := l6_11_proved G Ω hΩ S η hη hηS L hL (by omega)
  have hab := ((l6_9_proved G Ω hΩ S').2 η hS'η hS'inv).1
  have hUSet : ∀ U ∈ η, U ∈ USet Ω := fun U hU => (hS'η.1 hU).1
  by_cases hLK : L = K
  · rw [hLK]
    exact Relation.ReflTransGen.refl
  have hUKord : 4 ≤ Nat.card ↥(K ⊓ ⨆ V ∈ η, V) := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet (hUSet _ hUK)
    exact h4
  have hUK2 : IsPGroup 2 ↥(K ⊓ ⨆ V ∈ η, V) := S.isPGroup'.to_le (inf_le_right.trans hWS)
  have hzU : z ∈ K ⊓ ⨆ V ∈ η, V := T3.mem_of_isPGroup hz inf_le_left hUK2 (by omega)
  have hUN : (L ⊓ ⨆ V ∈ η, V) ≤ Subgroup.normalizer (K : Set G) := by
    intro y hy
    refine centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hnt hz ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hab y hy.2 z hzU.2
  have hstar : L ∈ omegaStarNbr Ω K :=
    ⟨hL, hLK, L ⊓ ⨆ V ∈ η, V, hUSet _ hUL, inf_le_left, hUN⟩
  rw [hcomp]
  exact Relation.ReflTransGen.single ⟨hL, Or.inl hstar⟩

theorem exists_conj_mem_dComp (hΩ : HypOmegaGen Ω)
    {K : Subgroup G} (hcomp : dComp Ω K = dstarComp Ω K) (hK : K ∈ Ω)
    (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z : G} (hz : IsUniqueInvolution K z)
    {R : Subgroup G} (hR : R ∈ RSet Ω) (hRK : R ≤ K) {S : Sylow 2 G}
    (hRS : R ≤ (S : Subgroup G)) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hWS : W ≤ (S : Subgroup G)) (hSH : (S : Subgroup G) ≤ H274 Ω K z) {L : Subgroup G}
    (hL : L ∈ Ω) {x : G} (hxL : x ∈ L) (hxo : orderOf x = 4) (hxH : x ∈ H274 Ω K z) :
    ∃ y ∈ H274 Ω K z, conjSub y L ∈ dComp Ω K := by
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hxo]; norm_num)
  obtain ⟨y, hyH, hyS⟩ := exists_conj_into_sylow S hSH hxH hx2
  refine ⟨y, hyH, mem_dComp_of_four_le_card hΩ hcomp hK hnt hz hR hRK hRS hW hWS
    (hΩ.conjInvariant y L hL) ?_⟩
  have hle : Subgroup.zpowers (y * x * y⁻¹) ≤ conjSub y L ⊓ (S : Subgroup G) :=
    le_inf (Subgroup.zpowers_le.mpr (conj_mem_conjSub hxL)) (Subgroup.zpowers_le.mpr hyS)
  have hord : orderOf (y * x * y⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj y) x
    rw [MulAut.conj_apply, hxo] at this
    exact this
  have := Subgroup.card_le_of_le hle
  rwa [Nat.card_zpowers, hord] at this

theorem mem_H274_of_conj_mem_sylow {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8Frame Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {g : G}
    (hg : g⁻¹ * z * g ∈ (S : Subgroup G)) : g ∈ H274 Ω K z := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  have htrans := hs.trans
  have hz := hs.hz
  have ht := hs.ht
  have hJ := hs.hJ
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hJ.1
  have hJc : J ∈ dComp Ω K := mem_dComp_of_mem_omegaNbr hJ
  have hntJ : ∀ J' ∈ twinSet Ω J, J' = J :=
    noTwins_of_mem hΩ.conjInvariant htrans hs.noTwins hJΩ
  have hSH : (S : Subgroup G) ≤ H274 Ω K z :=
    (sylow_le_sigmaNorm hΩ hK hRΩ hRK hRS hz).trans (sigmaNorm_le_H274 K z)
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H274 Ω K z :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hz).trans
      ((normalizer_le_sigmaNorm hΩ.conjInvariant hK).trans (sigmaNorm_le_H274 K z))
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ H274 Ω K z :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJΩ hntJ ht).trans
      ((normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hJc).trans (sigmaNorm_le_H274 K z))
  have hCzt : Subgroup.centralizer ({z * t} : Set G) ≤ H274 Ω K z :=
    centralizer_mul_le_H274 hJ ht
  obtain ⟨b, hbdef⟩ : ∃ b, b = g⁻¹ * z * g := ⟨_, rfl⟩
  rw [← hbdef] at hg
  obtain ⟨L, hLdef⟩ : ∃ L, L = conjSub g⁻¹ K := ⟨_, rfl⟩
  have hLΩ : L ∈ Ω := hLdef ▸ hΩ.conjInvariant g⁻¹ K hK
  have hb : IsUniqueInvolution L b := by
    have := hz.conj g⁻¹
    rwa [inv_inv, ← hbdef, ← hLdef] at this
  have hntL : ∀ L' ∈ twinSet Ω L, L' = L :=
    noTwins_of_mem hΩ.conjInvariant htrans hs.noTwins hLΩ
  have hCb : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hLΩ hntL hb
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have hzR : z ∈ R := T3.mem_of_isPGroup hz hRK hRsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hRΩ; omega)
  have htT : t ∈ T := T3.mem_of_isPGroup ht hTJ hTsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hTΩ; omega)
  have key : ∃ x ∈ L, orderOf x = 4 ∧ x ∈ H274 Ω K z := by
    by_cases hRb : conjSub b R = R
    swap
    · have hKb : conjSub b K ∈ omegaNbr Ω K :=
        conjSub_mem_omegaNbr hΩ hK hRΩ hRK hRS hz hg hRb
      obtain ⟨x, hxL, hxo, hxc⟩ := exists_orderFour_centralizes_mul_conj hΩ hK hRΩ hRK hRS
        hz hg hRb hLΩ hb hCb
      exact ⟨x, hxL, hxo, centralizer_mul_le_H274 hKb (hz.conj b)
        (Subgroup.mem_centralizer_singleton_iff.mpr hxc)⟩
    by_cases hTb : conjSub b T = T
    swap
    · have hJb : conjSub b J ∈ omegaNbr Ω J :=
        conjSub_mem_omegaNbr hΩ hJΩ hTΩ hTJ hTS ht hg hTb
      obtain ⟨x, hxL, hxo, hxc⟩ := exists_orderFour_centralizes_mul_conj hΩ hJΩ hTΩ hTJ hTS
        ht hg hTb hLΩ hb hCb
      exact ⟨x, hxL, hxo, centralizer_mul_le_H274_of_mem_dComp hΩ.conjInvariant hK htrans hJc hz
        ht hJb (ht.conj b) (Subgroup.mem_centralizer_singleton_iff.mpr hxc)⟩
    have hKb : conjSub b K = K := Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hK hRΩ hRK hRb
    have hJb : conjSub b J = J := Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hJΩ hTΩ hTJ hTb
    have hbz : b * z * b⁻¹ = z := hz.conj_eq hKb
    have hbt : b * t * b⁻¹ = t := ht.conj_eq hJb
    have hzb : z ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * b = (b * z * b⁻¹) * b := by rw [hbz]
        _ = b * z := by group
    have htb : t ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * b = (b * t * b⁻¹) * b := by rw [hbt]
        _ = b * t := by group
    obtain ⟨x, hxL, hxo, hxc⟩ := exists_orderFour_centralizes_one_of_three hΩ hLΩ hb
      S.isPGroup' (hRS hzR) (hTS htT) (mem_normalizer_iff_conjSub_eq.mp (hCb hzb))
      (mem_normalizer_iff_conjSub_eq.mp (hCb htb))
    refine ⟨x, hxL, hxo, ?_⟩
    rcases hxc with h | h | h
    · exact hCz (Subgroup.mem_centralizer_singleton_iff.mpr h)
    · exact hCt (Subgroup.mem_centralizer_singleton_iff.mpr h)
    · exact hCzt (Subgroup.mem_centralizer_singleton_iff.mpr h)
  obtain ⟨x, hxL, hxo, hxH⟩ := key
  obtain ⟨y, hyH, hyc⟩ := exists_conj_mem_dComp hΩ hcomp hK hs.noTwins hz hRΩ hRK hRS
    hs.hW.1 hs.hW.2.1 hSH hLΩ hxL hxo hxH
  have hyN : y * g⁻¹ ∈ sigmaNorm Ω K := by
    rw [mem_sigmaNorm_iff hΩ.conjInvariant hK, conjSub_mul, ← hLdef]
    exact hyc
  have h1 : g⁻¹ ∈ H274 Ω K z := by
    have := (H274 Ω K z).mul_mem ((H274 Ω K z).inv_mem hyH) (sigmaNorm_le_H274 K z hyN)
    simpa using this
  simpa using (H274 Ω K z).inv_mem h1

theorem mem_H274_of_conj_mem_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8Frame Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {g : G}
    (hg : g⁻¹ * z * g ∈ H274 Ω K z) : g ∈ H274 Ω K z := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  have hSH : (S : Subgroup G) ≤ H274 Ω K z :=
    (sylow_le_sigmaNorm hΩ hK hRΩ hRK hRS hs.hz).trans (sigmaNorm_le_H274 K z)
  have hb : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
    have := hs.hz.conj g⁻¹
    rwa [inv_inv] at this
  have hb2 : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * z * g)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [pow_two]; exact hb.sq) hb.ne_one)
  obtain ⟨y, hyH, hyS⟩ := exists_conj_into_sylow S hSH hg hb2
  have h1 : (g * y⁻¹)⁻¹ * z * (g * y⁻¹) ∈ (S : Subgroup G) := by
    have : (g * y⁻¹)⁻¹ * z * (g * y⁻¹) = y * (g⁻¹ * z * g) * y⁻¹ := by group
    rwa [this]
  have h2 := mem_H274_of_conj_mem_sylow hs hcomp h1
  have : g = (g * y⁻¹) * y := by group
  rw [this]
  exact (H274 Ω K z).mul_mem h2 hyH

theorem fixesUniqueCoset_z {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8Frame Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) :
    FixesUniqueCoset z (H274 Ω K z) := by
  have hzH : z ∈ H274 Ω K z :=
    sigmaNorm_le_H274 K z (normalizer_le_sigmaNorm hs.hyp.conjInvariant hs.mem
      (Subgroup.le_normalizer hs.hz.mem))
  show ∃! c : G ⧸ H274 Ω K z, z • c = c
  refine ⟨((1 : G) : G ⧸ H274 Ω K z), ?_, fun c hc => ?_⟩
  · show z • ((1 : G) : G ⧸ H274 Ω K z) = ((1 : G) : G ⧸ H274 Ω K z)
    rw [CFSG.StronglyEmbedded.UniqueCoset.smul_coe_eq_iff]
    simpa using hzH
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    have hc' : z • (x : G ⧸ H274 Ω K z) = x := hc
    have hx := (CFSG.StronglyEmbedded.UniqueCoset.smul_coe_eq_iff _ z x).mp hc'
    have hxH := mem_H274_of_conj_mem_H274 hs hcomp hx
    rw [QuotientGroup.eq]
    simpa using (H274 Ω K z).inv_mem hxH

theorem sylow_le_H274_of_mem {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8Frame Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {S₂ : Sylow 2 G}
    {X M : Subgroup G} (hX : X ∈ RSet Ω) (hXS : X ≤ (S₂ : Subgroup G)) (hM : M ∈ Ω)
    (hXM : X ≤ M) {zM : G} (hzM : IsUniqueInvolution M zM) (hzH : zM ∈ H274 Ω K z) :
    (S₂ : Subgroup G) ≤ H274 Ω K z := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  obtain ⟨g, hg⟩ := hs.trans M hM
  have hzM' : zM = g * z * g⁻¹ := by
    have := hs.hz.conj g
    rw [hg] at this
    exact hzM.eq this
  have hgH : g⁻¹ ∈ H274 Ω K z := by
    refine mem_H274_of_conj_mem_H274 hs hcomp ?_
    rw [inv_inv, ← hzM']
    exact hzH
  have hgH' : g ∈ H274 Ω K z := by simpa using (H274 Ω K z).inv_mem hgH
  have hS₂ : (S₂ : Subgroup G) ≤ sigmaNorm Ω M :=
    sylow_le_sigmaNorm hΩ hM hX hXM hXS hzM
  intro s hsS
  have hsM : s ∈ sigmaNorm Ω M := hS₂ hsS
  have hsM' : conjSub s M ∈ dComp Ω M := (mem_sigmaNorm_iff hΩ.conjInvariant hM).1 hsM
  have h1 : g⁻¹ * s * g ∈ sigmaNorm Ω K := by
    rw [mem_sigmaNorm_iff hΩ.conjInvariant hK]
    have h2 := mem_dComp_conjSub hΩ.conjInvariant hsM' g⁻¹
    have e1 : conjSub g⁻¹ M = K := by rw [← hg, conjSub_inv_conjSub]
    have e2 : conjSub (g⁻¹ * s * g) K = conjSub g⁻¹ (conjSub s M) := by
      rw [conjSub_mul, conjSub_mul, hg]
    rw [e2]
    rwa [e1] at h2
  have h3 := (H274 Ω K z).mul_mem ((H274 Ω K z).mul_mem hgH' (sigmaNorm_le_H274 K z h1)) hgH
  simpa [mul_assoc] using h3

theorem exists_mul_self_ne_one_of_mem_RSet (hΩ : HypOmegaGen Ω) {X : Subgroup G} (hX : X ∈ RSet Ω)
    : ∃ x ∈ X, x * x ≠ 1 := by
  classical
  obtain ⟨M, hM, hXM⟩ := exists_isSylow2In_of_mem_RSet hX
  obtain ⟨zM, hzM⟩ := hΩ.exists_uniqueInvolution hM
  have h8 := hΩ.eight_le_of_mem_RSet hX
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun x : ↥X => decide ((x : G) = 1)) := by
    intro a b hab
    simp only [decide_eq_decide] at hab
    by_cases ha : (a : G) = 1
    · exact Subtype.ext (ha.trans (hab.1 ha).symm)
    · have hb : (b : G) ≠ 1 := fun h => ha (hab.2 h)
      have ha' := hzM.unique a (hXM.1 a.2) (hcon a a.2)
      have hb' := hzM.unique b (hXM.1 b.2) (hcon b b.2)
      exact Subtype.ext ((ha'.resolve_left ha).trans (hb'.resolve_left hb).symm)
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem sylow_le_H274_of_good_four {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8Frame Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    {S₂ : Sylow 2 G} {u v : G} (hu : u ∈ (S₂ : Subgroup G)) (hv : v ∈ (S₂ : Subgroup G))
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hc : u * v = v * u) (hgu : Subgroup.centralizer ({u} : Set G) ≤ H274 Ω K z)
    (hgv : Subgroup.centralizer ({v} : Set G) ≤ H274 Ω K z)
    (hguv : Subgroup.centralizer ({u * v} : Set G) ≤ H274 Ω K z) :
    (S₂ : Subgroup G) ≤ H274 Ω K z := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S S₂
  have hXR : conjSub g R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hRΩ g
  have hXS : conjSub g R ≤ (S₂ : Subgroup G) := by
    have := conjSub_mono (n := g) hRS
    rwa [hg] at this
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_mul_self_ne_one_of_mem_RSet hΩ hXR
  have h310 := lemma_3_10 (S := (S₂ : Subgroup G)) S₂.isPGroup'
    (Δ := {Y | Y ∈ RSet Ω ∧ Y ≤ (S₂ : Subgroup G)}) (fun Y hY => hY.2)
    (fun Y hY s hs' => ⟨RSet.conj hΩ.conjInvariant hY.1 s, by
      have := conjSub_mono (n := s) hY.2
      rwa [conjSub_eq_self_of_mem hs'] at this⟩)
    (fun Y hY Y' hY' hne => l6_7_proved G Ω hΩ S₂ Y hY.1 Y' hY'.1 hY.2 hY'.2 hne)
    hu hv hu1 hv1 huv hu2 hv2 hc ⟨hXR, hXS⟩ ⟨x₀, hx₀, Or.inl hx₀1⟩
  have hγ : gamma1 (Subgroup.closure ({u, v} : Set G)) (S₂ : Subgroup G) ≤ H274 Ω K z := by
    refine iSup₂_le fun w hw => iSup_le fun hw1 => inf_le_right.trans ?_
    rcases mem_closure_pair_involutions hu2 hv2 hc hw with h | h | h | h
    · exact absurd h hw1
    · rw [h]; exact hgu
    · rw [h]; exact hgv
    · rw [h]; exact hguv
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h310
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyH : y ∈ H274 Ω K z := hγ hy.1
  obtain ⟨M, hM, hXM⟩ := exists_isSylow2In_of_mem_RSet hXR
  obtain ⟨zM, hzM⟩ := hΩ.exists_uniqueInvolution hM
  have hyX : y ∈ conjSub g R := hy.2
  have hzMy : zM ∈ Subgroup.zpowers y := by
    refine mem_of_isPGroup_of_unique_involution_subgroup (J := M) (fun t' ht' hord => ?_)
      (Subgroup.zpowers_le.mpr (hXM.1 hyX)) (hXM.2.1.to_le (Subgroup.zpowers_le.mpr hyX)) ?_
    · have h2 : t' * t' = 1 := by
        have := pow_orderOf_eq_one t'
        rwa [hord, pow_two] at this
      rcases hzM.unique t' ht' h2 with h | h
      · rw [h, orderOf_one] at hord
        omega
      · exact h
    · intro h
      exact hy1' (by simpa using h)
  have hzMH : zM ∈ H274 Ω K z := (Subgroup.zpowers_le.mpr hyH) hzMy
  exact sylow_le_H274_of_mem hs hcomp hXR hXS hM hXM.1 hzM hzMH

theorem le_centralizer_mul {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8Frame Ω K J S R T W z t) :
    R ≤ Subgroup.centralizer ({z * t} : Set G) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRne : R ≠ T := by
    intro hRT
    have hRsyl := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.mem hRΩ hRK
    have h8 := hΩ.eight_le_of_mem_RSet hRΩ
    have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
    have hzJ : z ∈ J := hTJ (hRT ▸ hzR)
    rcases hs.ht.unique z hzJ hs.hz.sq with h | h
    · exact hs.hz.ne_one h
    · have hJtw : J ∈ twinSet Ω K := ⟨hs.hJ.1, z, hs.hz, h ▸ hs.ht⟩
      exact hs.hJ.2.1 (hs.noTwins J hJtw)
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : r * z = z * r := by
    have := hs.hz.conj_eq (n := r) (conjSub_eq_self_of_mem (hRK hr))
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [this]
  have h2 : r * t = t * r := by
    have hRsyl := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hTΩ hTJ
    have h8 := hΩ.eight_le_of_mem_RSet hTΩ
    have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hRsyl.2.1 (by omega)
    exact l6_7_proved G Ω hΩ S R hRΩ T hTΩ hRS hTS hRne r hr t htT
  calc r * (z * t) = (r * z) * t := by group
    _ = (z * r) * t := by rw [h1]
    _ = z * (r * t) := by group
    _ = z * (t * r) := by rw [h2]
    _ = (z * t) * r := by group

theorem exists_sylow_centralizer {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8Frame Ω K J S R T W z t) :
    ∃ S' : Sylow 2 G, R ≤ (S' : Subgroup G) ∧
      IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer ({z * t} : Set G))
        (Subgroup.centralizer ({z * t} : Set G)) := by
  have hR2 : IsPGroup 2 R := S.isPGroup'.to_le hs.hR.2.2
  obtain ⟨V, hV, hRV⟩ := IsSylow2In.exists_ge hR2 (le_centralizer_mul hs)
  obtain ⟨S', hVS'⟩ := IsPGroup.exists_le_sylow hV.2.1
  refine ⟨S', hRV.trans hVS', ?_⟩
  have hp2 : IsPGroup 2 ↥((S' : Subgroup G) ⊓ Subgroup.centralizer ({z * t} : Set G)) :=
    S'.isPGroup'.to_le inf_le_left
  have heq := hV.eq_of_le hp2 inf_le_right (le_inf hVS' hV.1)
  rw [heq]
  exact hV

theorem sylow_le_H274_of_ge {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8Frame Ω K J S R T W z t) {S' : Sylow 2 G} (hRS' : R ≤ (S' : Subgroup G)) :
    (S' : Subgroup G) ≤ H274 Ω K z :=
  (sylow_le_sigmaNorm hs.hyp hs.mem hs.hR.1 hs.hR.2.1
    hRS' hs.hz).trans (sigmaNorm_le_H274 K z)

theorem not_commute_of_not_mem_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8Frame Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {g w : G}
    (hg : g ∉ H274 Ω K z) (hw : IsConj z w) (hwH : w ∈ H274 Ω K z) :
    g⁻¹ * (z * t) * g * w ≠ w * (g⁻¹ * (z * t) * g) := by
  intro hcom
  obtain ⟨c, rfl⟩ := isConj_iff.1 hw
  have hcH : c ∈ H274 Ω K z := by
    have h := mem_H274_of_conj_mem_H274 hs hcomp (g := c⁻¹) (by simpa using hwH)
    simpa using (H274 Ω K z).inv_mem h
  have ha' : (g * c)⁻¹ * (z * t) * (g * c) * z = z * ((g * c)⁻¹ * (z * t) * (g * c)) := by
    have e1 : (g * c)⁻¹ * (z * t) * (g * c) * z
        = c⁻¹ * (g⁻¹ * (z * t) * g * (c * z * c⁻¹)) * c := by group
    have e2 : z * ((g * c)⁻¹ * (z * t) * (g * c))
        = c⁻¹ * ((c * z * c⁻¹) * (g⁻¹ * (z * t) * g)) * c := by group
    rw [e1, e2, hcom]
  have hy : (g * c) * z * (g * c)⁻¹ ∈ Subgroup.centralizer ({z * t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g * c) * z * (g * c)⁻¹ * (z * t)
        = (g * c) * (z * ((g * c)⁻¹ * (z * t) * (g * c))) * (g * c)⁻¹ := by group
      _ = (g * c) * (((g * c)⁻¹ * (z * t) * (g * c)) * z) * (g * c)⁻¹ := by rw [ha']
      _ = (z * t) * ((g * c) * z * (g * c)⁻¹) := by group
  have hyH : (g * c) * z * (g * c)⁻¹ ∈ H274 Ω K z := centralizer_mul_le_H274 hs.hJ hs.ht hy
  have hgc : g * c ∈ H274 Ω K z := by
    have h := mem_H274_of_conj_mem_H274 hs hcomp (g := (g * c)⁻¹) (by simpa using hyH)
    simpa using (H274 Ω K z).inv_mem h
  apply hg
  have : g = (g * c) * c⁻¹ := by group
  rw [this]
  exact (H274 Ω K z).mul_mem hgc ((H274 Ω K z).inv_mem hcH)

theorem frame_facts {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8Frame Ω K J S R T W z t) {S' : Sylow 2 G}
    (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {X M : Subgroup G} {x : G} (hXS : X ≤ (S' : Subgroup G))
    (hM : M ∈ Ω) (hXM : IsSylow2In X M) (hXΩ : X ∈ RSet Ω) (hx : IsUniqueInvolution M x) :
    x ∈ X ∧ x ∈ H274 Ω K z ∧ IsConj z x ∧ (∀ y ∈ X, x * y = y * x) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have h8 := hΩ.eight_le_of_mem_RSet hXΩ
  have hxX : x ∈ X := T3.mem_of_isPGroup hx hXM.1 hXM.2.1 (by omega)
  refine ⟨hxX, hS'H (hXS hxX), ?_, fun y hy => ?_⟩
  · obtain ⟨c, hc⟩ := hs.trans M hM
    have h1 : IsUniqueInvolution M (c * z * c⁻¹) := hc ▸ hs.hz.conj c
    exact isConj_iff.2 ⟨c, (hx.eq h1).symm⟩
  · have h := hx.conj_eq (n := y) (conjSub_eq_self_of_mem (hXM.1 hy))
    calc x * y = (y * x * y⁻¹) * y := by rw [h]
      _ = y * x := by group

theorem conjSub_ne_of_not_mem_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8Frame Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    {S' : Sylow 2 G} (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {g : G} (hg : g ∉ H274 Ω K z)
    {X M : Subgroup G} {x : G} (hXS : X ≤ (S' : Subgroup G)) (hM : M ∈ Ω)
    (hXM : IsSylow2In X M) (hXΩ : X ∈ RSet Ω) (hx : IsUniqueInvolution M x) :
    conjSub (g⁻¹ * (z * t) * g) X ≠ X := by
  intro h
  obtain ⟨-, hxH, hxc, -⟩ := frame_facts hs hS'H hXS hM hXM hXΩ hx
  have hdx : (g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹ = x := by
    have hmem : (g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹ ∈ conjSub (g⁻¹ * (z * t) * g) X :=
      conj_mem_conjSub (frame_facts hs hS'H hXS hM hXM hXΩ hx).1
    rw [h] at hmem
    have hsq : (g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹ *
        ((g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹) = 1 := by
      calc (g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹ *
          ((g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹)
          = (g⁻¹ * (z * t) * g) * (x * x) * (g⁻¹ * (z * t) * g)⁻¹ := by group
        _ = 1 := by rw [hx.sq]; group
    rcases hx.unique _ (hXM.1 hmem) hsq with h1 | h1
    · exfalso
      apply hx.ne_one
      calc x = (g⁻¹ * (z * t) * g)⁻¹ * ((g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹) *
            (g⁻¹ * (z * t) * g) := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  apply not_commute_of_not_mem_H274 hs hcomp hg hxc hxH
  calc g⁻¹ * (z * t) * g * x = (g⁻¹ * (z * t) * g * x * (g⁻¹ * (z * t) * g)⁻¹) *
        (g⁻¹ * (z * t) * g) := by group
    _ = x * (g⁻¹ * (z * t) * g) := by rw [hdx]

theorem exists_normalized_conj {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8Frame Ω K J S R T W z t) {S' : Sylow 2 G}
    (hS'a : IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer ({z * t} : Set G))
      (Subgroup.centralizer ({z * t} : Set G)))
    (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {g : G} (hg : g ∉ H274 Ω K z)
    (hgH : g⁻¹ * (z * t) * g ∈ H274 Ω K z) :
    ∃ g' : G, g' ∉ H274 Ω K z ∧ g'⁻¹ * (z * t) * g' ∈ (S' : Subgroup G) ∧
      ∀ s ∈ (S' : Subgroup G), (g'⁻¹ * (z * t) * g') * s = s * (g'⁻¹ * (z * t) * g') →
        g' * s * g'⁻¹ ∈ (S' : Subgroup G) := by
  have ha2 : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hs.hyp hs.hz hs.hJ hs.ht
  have haC : Subgroup.centralizer ({z * t} : Set G) ≤ H274 Ω K z :=
    centralizer_mul_le_H274 hs.hJ hs.ht
  have hd₀2 : (g⁻¹ * (z * t) * g) * (g⁻¹ * (z * t) * g) = 1 := by
    calc (g⁻¹ * (z * t) * g) * (g⁻¹ * (z * t) * g) = g⁻¹ * (z * t * (z * t)) * g := by group
      _ = 1 := by rw [ha2]; group
  obtain ⟨y, hyH, hyS⟩ := exists_conj_into_sylow S' hS'H hgH (isPGroup_zpowers_of_sq hd₀2)
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = g * y⁻¹ := ⟨_, rfl⟩
  have hd₁ : g₁⁻¹ * (z * t) * g₁ = y * (g⁻¹ * (z * t) * g) * y⁻¹ := by rw [hg₁]; group
  have hd₁S : g₁⁻¹ * (z * t) * g₁ ∈ (S' : Subgroup G) := hd₁ ▸ hyS
  have hg₁H : g₁ ∉ H274 Ω K z := by
    intro h
    apply hg
    have : g = g₁ * y := by rw [hg₁]; group
    rw [this]
    exact (H274 Ω K z).mul_mem h hyH
  obtain ⟨d₁, hd₁def⟩ : ∃ d₁, d₁ = g₁⁻¹ * (z * t) * g₁ := ⟨_, rfl⟩
  rw [← hd₁def] at hd₁S
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G,
      D = conjSub g₁ ((S' : Subgroup G) ⊓ Subgroup.centralizer ({d₁} : Set G)) := ⟨_, rfl⟩
  have hD2 : IsPGroup 2 ↥D := by
    rw [hD]
    exact (S'.isPGroup'.to_le inf_le_left).map _
  have hDC : D ≤ Subgroup.centralizer ({z * t} : Set G) := by
    rw [hD]
    rintro x ⟨s, hs', rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsc := Subgroup.mem_centralizer_singleton_iff.1 hs'.2
    have ha_eq : z * t = g₁ * d₁ * g₁⁻¹ := by rw [hd₁def]; group
    show g₁ * s * g₁⁻¹ * (z * t) = (z * t) * (g₁ * s * g₁⁻¹)
    rw [ha_eq]
    calc g₁ * s * g₁⁻¹ * (g₁ * d₁ * g₁⁻¹) = g₁ * (s * d₁) * g₁⁻¹ := by group
      _ = g₁ * (d₁ * s) * g₁⁻¹ := by rw [hsc]
      _ = g₁ * d₁ * g₁⁻¹ * (g₁ * s * g₁⁻¹) := by group
  obtain ⟨V, hV, hDV⟩ := IsSylow2In.exists_ge hD2 hDC
  obtain ⟨c, hcC, hcV⟩ := exists_conj_of_isSylow2In hS'a hV
  have hca : c * (z * t) = (z * t) * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  have hd₂ : (c⁻¹ * g₁)⁻¹ * (z * t) * (c⁻¹ * g₁) = d₁ := by
    calc (c⁻¹ * g₁)⁻¹ * (z * t) * (c⁻¹ * g₁) = g₁⁻¹ * (c * (z * t) * c⁻¹) * g₁ := by group
      _ = g₁⁻¹ * (z * t) * g₁ := by rw [hca]; group
      _ = d₁ := hd₁def.symm
  refine ⟨c⁻¹ * g₁, ?_, by rw [hd₂]; exact hd₁S, ?_⟩
  · intro h
    apply hg₁H
    have : g₁ = c * (c⁻¹ * g₁) := by group
    rw [this]
    exact (H274 Ω K z).mul_mem (haC hcC) h
  · intro s hsS hsd
    rw [hd₂] at hsd
    have hsc : s ∈ Subgroup.centralizer ({d₁} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hsd.symm
    have h1 : g₁ * s * g₁⁻¹ ∈ D := by
      rw [hD]
      exact conj_mem_conjSub ⟨hsS, hsc⟩
    have h2 : g₁ * s * g₁⁻¹ ∈ conjSub c ((S' : Subgroup G) ⊓
        Subgroup.centralizer ({z * t} : Set G)) := hcV ▸ hDV h1
    have h3 := (mem_conjSub_iff.1 h2).1
    have : (c⁻¹ * g₁) * s * (c⁻¹ * g₁)⁻¹ = c⁻¹ * (g₁ * s * g₁⁻¹) * c := by group
    rw [this]
    exact h3

theorem eight_le_card_RSet {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8Frame Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {S' : Sylow 2 G}
    (hRS' : R ≤ (S' : Subgroup G)) (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {g : G}
    (hg : g ∉ H274 Ω K z) (hdS : g⁻¹ * (z * t) * g ∈ (S' : Subgroup G))
    (hCS : ∀ s ∈ (S' : Subgroup G), (g⁻¹ * (z * t) * g) * s = s * (g⁻¹ * (z * t) * g) →
      g * s * g⁻¹ ∈ (S' : Subgroup G)) :
    8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S' : Subgroup G)} := by
  classical
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  obtain ⟨d, hd⟩ : ∃ d, d = g⁻¹ * (z * t) * g := ⟨_, rfl⟩
  have hfree : conjSub d R ≠ R := by
    rw [hd]
    exact conjSub_ne_of_not_mem_H274 hs hcomp hS'H hg hRS' hK hRsyl hRΩ hs.hz
  rw [← hd] at hdS hCS
  have hdd : d * d = 1 := by
    rw [hd]
    calc g⁻¹ * (z * t) * g * (g⁻¹ * (z * t) * g) = g⁻¹ * (z * t * (z * t)) * g := by group
      _ = 1 := by rw [Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht]; group
  have hR'Ω : conjSub d R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hRΩ d
  have hR'S : conjSub d R ≤ (S' : Subgroup G) := by
    have := conjSub_mono (n := d) hRS'
    rwa [conjSub_eq_self_of_mem hdS] at this
  have hcomm : Commutes R (conjSub d R) :=
    l6_7_proved G Ω hΩ S' R hRΩ _ hR'Ω hRS' hR'S (Ne.symm hfree)
  have hM : conjSub d K ∈ omegaNbr Ω K :=
    conjSub_mem_omegaNbr hΩ hK hRΩ hRK hRS' hs.hz hdS hfree
  have hCe : Subgroup.centralizer ({z * (d * z * d⁻¹)} : Set G) ≤ H274 Ω K z :=
    centralizer_mul_le_H274 hM (hs.hz.conj d)
  have hq₀ : ∀ r : ↥R, g * ((r : G) * (d * r * d⁻¹)) * g⁻¹ ∈ (S' : Subgroup G) := by
    intro r
    have hrS : (r : G) ∈ (S' : Subgroup G) := hRS' r.2
    have hr'S : d * r * d⁻¹ ∈ (S' : Subgroup G) :=
      S'.mul_mem (S'.mul_mem hdS hrS) (S'.inv_mem hdS)
    exact hCS _ (S'.mul_mem hrS hr'S)
      (commute_mul_conj hdd (hcomm r r.2 _ (conj_mem_conjSub r.2)))
  let F : ↥R → {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S' : Subgroup G)} := fun r =>
    ⟨conjSub (g * ((r : G) * (d * r * d⁻¹)) * g⁻¹) R, RSet.conj hΩ.conjInvariant hRΩ _, by
      have := conjSub_mono (n := g * ((r : G) * (d * r * d⁻¹)) * g⁻¹) hRS'
      rwa [conjSub_eq_self_of_mem (hq₀ r)] at this⟩
  have hinj : Function.Injective F := by
    intro r r' hrr
    have h1 : conjSub (g * ((r : G) * (d * r * d⁻¹)) * g⁻¹) R =
        conjSub (g * ((r' : G) * (d * r' * d⁻¹)) * g⁻¹) R := congrArg Subtype.val hrr
    by_contra hne
    have hρR : (r : G)⁻¹ * r' ∈ R := R.mul_mem (R.inv_mem r.2) r'.2
    have hρ1 : (r : G)⁻¹ * r' ≠ 1 := fun h => hne (Subtype.ext (inv_mul_eq_one.mp h))
    have h2 : conjSub ((g * ((r : G) * (d * r * d⁻¹)) * g⁻¹)⁻¹ *
        (g * ((r' : G) * (d * r' * d⁻¹)) * g⁻¹)) R = R := by
      rw [conjSub_mul, ← h1, conjSub_inv_conjSub]
    have hc : ((r : G)⁻¹ * r') * (d * r * d⁻¹)⁻¹ = (d * r * d⁻¹)⁻¹ * ((r : G)⁻¹ * r') :=
      hcomm _ hρR _ ((conjSub d R).inv_mem (conj_mem_conjSub r.2))
    have hκ : (g * ((r : G) * (d * r * d⁻¹)) * g⁻¹)⁻¹ * (g * ((r' : G) * (d * r' * d⁻¹)) * g⁻¹)
        = g * (((r : G)⁻¹ * r') * (d * ((r : G)⁻¹ * r') * d⁻¹)) * g⁻¹ := by
      calc _ = g * ((d * r * d⁻¹)⁻¹ * ((r : G)⁻¹ * r') * (d * r' * d⁻¹)) * g⁻¹ := by group
        _ = g * (((r : G)⁻¹ * r') * (d * r * d⁻¹)⁻¹ * (d * r' * d⁻¹)) * g⁻¹ := by rw [← hc]
        _ = _ := by group
    rw [hκ] at h2
    have hρ'R : d * ((r : G)⁻¹ * r') * d⁻¹ ∈ conjSub d R := conj_mem_conjSub hρR
    obtain ⟨n, hn⟩ := exists_pow_orderOf_eq_two hRsyl.2.1
      (x := (⟨(r : G)⁻¹ * r', hρR⟩ : ↥R)) (fun h => hρ1 (congrArg Subtype.val h))
    have hn' : orderOf (((r : G)⁻¹ * r') ^ n) = 2 := by
      rw [← hn, ← Subgroup.orderOf_coe]
      rfl
    have hρn : ((r : G)⁻¹ * r') ^ n = z := by
      have hsq : ((r : G)⁻¹ * r') ^ n * ((r : G)⁻¹ * r') ^ n = 1 := by
        rw [← pow_two]
        have := pow_orderOf_eq_one (((r : G)⁻¹ * r') ^ n)
        rwa [hn'] at this
      rcases hs.hz.unique _ (hRK (R.pow_mem hρR n)) hsq with h | h
      · rw [h, orderOf_one] at hn'
        omega
      · exact h
    have hκn : (((r : G)⁻¹ * r') * (d * ((r : G)⁻¹ * r') * d⁻¹)) ^ n = z * (d * z * d⁻¹) := by
      rw [Commute.mul_pow (hcomm _ hρR _ hρ'R), conj_pow, hρn]
    have hN : g * (z * (d * z * d⁻¹)) * g⁻¹ ∈ Subgroup.normalizer (R : Set G) := by
      have h3 : g * (((r : G)⁻¹ * r') * (d * ((r : G)⁻¹ * r') * d⁻¹)) * g⁻¹ ∈
          Subgroup.normalizer (R : Set G) := mem_normalizer_iff_conjSub_eq.mpr h2
      have h4 := Subgroup.pow_mem _ h3 n
      rwa [conj_pow, hκn] at h4
    have h8 := hΩ.eight_le_of_mem_RSet hRΩ
    have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
    have hzc := conj_eq_of_conjSub_eq hs.hz hRK hzR (mem_normalizer_iff_conjSub_eq.mp hN)
    have hzc' : (g * (z * (d * z * d⁻¹)) * g⁻¹) * z = z * (g * (z * (d * z * d⁻¹)) * g⁻¹) := by
      calc (g * (z * (d * z * d⁻¹)) * g⁻¹) * z
          = ((g * (z * (d * z * d⁻¹)) * g⁻¹) * z * (g * (z * (d * z * d⁻¹)) * g⁻¹)⁻¹) *
            (g * (z * (d * z * d⁻¹)) * g⁻¹) := by group
        _ = z * (g * (z * (d * z * d⁻¹)) * g⁻¹) := by rw [hzc]
    have hyC : g⁻¹ * z * g ∈ Subgroup.centralizer ({z * (d * z * d⁻¹)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * z * g * (z * (d * z * d⁻¹))
          = g⁻¹ * (z * (g * (z * (d * z * d⁻¹)) * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * (z * (d * z * d⁻¹)) * g⁻¹) * z) * g := by rw [hzc']
        _ = (z * (d * z * d⁻¹)) * (g⁻¹ * z * g) := by group
    exact hg (mem_H274_of_conj_mem_H274 hs hcomp (hCe hyC))
  have h8 := hΩ.eight_le_of_mem_RSet hRΩ
  have := Nat.card_le_card_of_injective F hinj
  omega

theorem IsFrameInv.mem (hΩ : HypOmegaGen Ω) {X : Subgroup G} {x : G}
    (hX : X ∈ RSet Ω) (h : IsFrameInv Ω X x) : x ∈ X := by
  obtain ⟨M, hM, hXM, hx⟩ := h
  have h8 := hΩ.eight_le_of_mem_RSet hX
  exact T3.mem_of_isPGroup hx hXM.1 hXM.2.1 (by omega)

theorem IsFrameInv.ne {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8Frame Ω K J S R T W z t) {X Y : Subgroup G} {x y : G} (hx : IsFrameInv Ω X x)
    (hy : IsFrameInv Ω Y y) (hXY : X ≠ Y) (hc : Commutes X Y) : x ≠ y := by
  intro hxy
  obtain ⟨M, hM, hXM, hxM⟩ := hx
  obtain ⟨N, hN, hYN, hyN⟩ := hy
  have hNM : N ∈ twinSet Ω M := ⟨hN, x, hxM, hxy ▸ hyN⟩
  have hNM' : N = M := noTwins_of_mem hs.hyp.conjInvariant hs.trans hs.noTwins hM N hNM
  rw [hNM'] at hYN
  exact hXY (eq_of_commutes_isSylow2In hXM hYN hc).symm

theorem exists_four_group {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8Frame Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {S' : Sylow 2 G}
    (hRS' : R ≤ (S' : Subgroup G)) (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {g : G}
    (hg : g ∉ H274 Ω K z) (hdS : g⁻¹ * (z * t) * g ∈ (S' : Subgroup G))
    (hcount : 8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S' : Subgroup G)}) :
    ∃ u v : G, u ∈ (S' : Subgroup G) ∧ v ∈ (S' : Subgroup G) ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧
      u * u = 1 ∧ v * v = 1 ∧ u * v = v * u ∧
      (g⁻¹ * (z * t) * g) * u = u * (g⁻¹ * (z * t) * g) ∧
      (g⁻¹ * (z * t) * g) * v = v * (g⁻¹ * (z * t) * g) ∧
      (∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, u * y = y * u) ∧
      (∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, v * y = y * v) := by
  obtain ⟨hRΩ, hRK, -⟩ := hs.hR
  exact CFSG.ClassicalInvolution.Asc77.T8.exists_four_group_gen hs.hyp.conjInvariant hs.mem hs.hz
    hRΩ (Q3CL.T3.isSylow2In_of_mem_RSet_of_le hs.hyp hs.mem hRΩ hRK) hRS'
    (fun hM => hs.hyp.exists_uniqueInvolution hM)
    (Q3CL.T8.mul_self_zt hs.hyp hs.hz hs.hJ hs.ht)
    (fun hXS hM hXM hXΩ hx => conjSub_ne_of_not_mem_H274 hs hcomp hS'H hg hXS hM hXM hXΩ hx)
    (fun hX hY hXS hYS hXY => l6_7_proved G Ω hs.hyp S' _ hX _ hY hXS hYS hXY)
    (fun hX hx => IsFrameInv.mem hs.hyp hX hx)
    (fun hx hy hXY hc => IsFrameInv.ne hs hx hy hXY hc)
    hdS hcount

theorem mem_H274_of_min {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8Frame Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    (hmin : ∀ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) →
      8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)} →
        ∀ x : G, x ∈ (S₂ : Subgroup G) → x * x = 1 → x ≠ 1 →
          (∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) →
            Subgroup.centralizer ({x} : Set G) ≤ H274 Ω K z)
    {g : G} (hgH : g⁻¹ * (z * t) * g ∈ H274 Ω K z) : g ∈ H274 Ω K z := by
  by_contra hg
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.mem hRΩ hRK
  have h8 := hΩ.eight_le_of_mem_RSet hRΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  obtain ⟨S', hRS', hS'a⟩ := exists_sylow_centralizer hs
  have hS'H := sylow_le_H274_of_ge hs hRS'
  obtain ⟨g', hg', hdS, hCS⟩ := exists_normalized_conj hs hS'a hS'H hg hgH
  have hcount := eight_le_card_RSet hs hcomp hRS' hS'H hg' hdS hCS
  obtain ⟨u, v, huS, hvS, hu1, hv1, huv, hu2, hv2, hc, hdu, hdv, hcu, hcv⟩ :=
    exists_four_group hs hcomp hRS' hS'H hg' hdS hcount
  obtain ⟨S₃, hS₃⟩ : ∃ S₃ : Sylow 2 G, (S₃ : Subgroup G) = conjSub g'⁻¹ (S' : Subgroup G) :=
    ⟨g'⁻¹ • S', by
      rw [Sylow.coe_subgroup_smul]
      ext x
      simp [conjSub, Subgroup.pointwise_smul_def]⟩
  have hu₃ : u ∈ (S₃ : Subgroup G) := by
    rw [hS₃, mem_conjSub_iff]
    simpa using hCS u huS hdu
  have hv₃ : v ∈ (S₃ : Subgroup G) := by
    rw [hS₃, mem_conjSub_iff]
    simpa using hCS v hvS hdv
  have hgood := sylow_le_H274_of_good_four hs hcomp hu₃ hv₃ hu1 hv1 huv hu2 hv2 hc
    (hmin S' hRS' hcount u huS hu2 hu1 hcu) (hmin S' hRS' hcount v hvS hv2 hv1 hcv)
    (hmin S' hRS' hcount (u * v) (S'.mul_mem huS hvS) (mul_self_of_commute hu2 hv2 hc)
      (mul_ne_one_of_ne hu2 huv)
      (fun Y hY hYS y hy => mul_comm_mul (hcu Y hY hYS y hy) (hcv Y hY hYS y hy)))
  have hz₃ : g'⁻¹ * z * g' ∈ (S₃ : Subgroup G) := by
    rw [hS₃]
    simpa using conj_mem_conjSub (n := g'⁻¹) (hRS' hzR)
  exact hg' (mem_H274_of_conj_mem_H274 hs hcomp (hgood hz₃))

theorem isConj_or_mem_omegaNbr {K : Subgroup G} {z : G} (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω)
    (hA : AEmpty Ω K)
    (hnt : ∀ K' ∈ twinSet Ω K, K' = K) (hz : IsUniqueInvolution K z) {g : G}
    (hne : g⁻¹ * z * g ≠ z) (hcomm : z * (g⁻¹ * z * g) = g⁻¹ * z * g * z) :
    IsConj z (z * (g⁻¹ * z * g)) ∨ conjSub g⁻¹ K ∈ omegaNbr Ω K := by
  obtain ⟨b, hbdef⟩ : ∃ b, b = g⁻¹ * z * g := ⟨_, rfl⟩
  rw [← hbdef] at hne hcomm ⊢
  obtain ⟨L, hLdef⟩ : ∃ L, L = conjSub g⁻¹ K := ⟨_, rfl⟩
  rw [← hLdef]
  have hLΩ : L ∈ Ω := hLdef ▸ hΩ.conjInvariant g⁻¹ K hK
  have hb : IsUniqueInvolution L b := by
    have := hz.conj g⁻¹
    rwa [inv_inv, ← hbdef, ← hLdef] at this
  have hbz : IsConj z b := isConj_iff.mpr ⟨g⁻¹, by rw [hbdef, inv_inv]⟩
  have hLK : L ≠ K := by
    intro h
    rcases hz.unique b (h ▸ hb.mem) hb.sq with h1 | h1
    · exact hb.ne_one h1
    · exact hne h1
  have hLtw : L ∉ twinSet Ω K := fun h => hLK (hnt L h)
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hnt hz
  have hbC : b ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hb2 : IsPGroup 2 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [pow_two]; exact hb.sq) hb.ne_one)
  have hbLC : Subgroup.zpowers b ≤ L ⊓ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hb.mem, hbC⟩
  obtain ⟨V, hV, hbV⟩ := IsSylow2In.exists_ge hb2 hbLC
  have h62 := Sec6Gen.l6_2Gen G Ω hΩ K hK z hz L hLΩ hLtw b hb V hV
    (hbV (Subgroup.mem_zpowers b))
  rcases h62 with ⟨-, h1⟩ | ⟨hVb, -, R', hR'Ω, hR'K, hVR', hsd⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, -⟩
  · exact absurd (mem_normalizer_iff_conjSub_eq.mp (hCz hbC)) h1
  · left
    have hR'syl : IsSylow2In R' K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hR'Ω hR'K
    have h8 := hΩ.eight_le_of_mem_RSet hR'Ω
    have hzR' : z ∈ R' := T3.mem_of_isPGroup hz hR'K hR'syl.2.1 (by omega)
    have hz' : IsUniqueInvolution R' z := uniqueInvolution_restrict hz hR'K hzR'
    have hbR' : b ∉ R' := by
      intro h
      rcases hz.unique b (hR'K h) hb.sq with h1 | h1
      · exact hb.ne_one h1
      · exact hne h1
    rw [hVb] at hVR' hsd
    obtain ⟨r, -, hr⟩ := exists_conj_eq_mul_of_isSemidihedral hR'syl.2.1 hz' hb.sq hbR'
      (hVR' (Subgroup.mem_zpowers b)) hsd
    exact hbz.trans (isConj_iff.mpr ⟨r, hr⟩)
  · have hLs : L ∈ omegaStarNbr Ω K := ⟨hLΩ, hLK, V, hVU, hV.1.trans inf_le_left, hVN⟩
    by_cases hω : L ∈ omegaNbr Ω K
    · exact Or.inr hω
    · exact Or.inl (isConj_mul_of_aEmpty hA hLs hω hz hb hcomm hne hbz)
  · right
    exact ⟨hLΩ, hLK, V, hVR, hV.1.trans inf_le_left, (hV.1.trans inf_le_right).trans hCz⟩

end T8

end CFSG.ClassicalInvolution.Q3.Q3CL.Frame
