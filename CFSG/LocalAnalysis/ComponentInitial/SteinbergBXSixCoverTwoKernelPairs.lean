module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXSixCoverTwoKernel

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial

namespace SixCoverTwoKernel

open Subgroup SevenTransvectionE7
open scoped commutatorElement

private def toTwo : List (List ℕ) :=
  [[], [3], [], [1], [6], [14, 9], [4], [4, 1], [14, 4], [11], [9, 1], [9], [14], [11, 4], [12],
    [12, 1], [19, 1], [19], [20, 4], [17], [22], [22, 1], [20], [17, 4], [27, 1], [27], [57, 33],
    [25], [30], [30, 1], [28], [20, 9], [51, 17], [35], [33, 1], [33], [38], [46, 9], [36], [36, 1],
    [46, 4], [43], [41, 1], [41], [46], [43, 4], [44], [44, 1], [51, 1], [51], [52, 4], [49], [54],
    [54, 1], [52], [49, 4], [59, 1], [59], [41, 17], [57], [62], [62, 1], [60], [52, 9]]

private def toEight : List (List ℕ) :=
  [[], [], [], [], [], [13], [], [15], [], [], [7, 5], [], [], [5], [], [7], [29, 5], [], [31, 5],
    [], [], [29], [], [31], [53, 37], [], [55, 37], [], [], [21], [], [23], [61, 21], [], [63, 21],
    [], [], [45], [], [47], [37, 5], [], [39, 5], [], [], [37], [], [39], [61, 5], [], [63, 5], [],
    [], [61], [], [63], [37, 21], [], [39, 21], [], [], [53], [], [55]]

private theorem toTwo_check : ∀ a, a < 64 → a ≠ 0 →
    (toTwo.getD a []).foldl (fun x c => tauL c x) a = 2 := by
  decide

private theorem toTwo_lt : ∀ a, a < 64 → ∀ c ∈ toTwo.getD a [], c < 64 := by
  decide

private theorem toEight_check : ∀ b, b < 64 → b ≠ 0 → b ≠ 2 → pairing (bitVec 2) (bitVec b) = 0 →
    (toEight.getD b []).foldl (fun x c => tauL c x) b = 8 := by
  decide

private theorem toEight_lt : ∀ b, b < 64 → ∀ c ∈ toEight.getD b [], c < 64 := by
  decide

private theorem toEight_moves_orth : ∀ b, b < 64 → b ≠ 0 → b ≠ 2 →
    pairing (bitVec 2) (bitVec b) = 0 →
    ∀ c ∈ toEight.getD b [], pairing (bitVec 2) (bitVec c) = 0 := by
  decide

section Labels

private def labelTransvection (c : ℕ) :
    LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2) :=
  binarySymplecticTransvection b0 b0_isAlt (bitVec c)

private theorem labelTransvection_injective (c : ℕ) :
    Function.Injective fun v =>
      (labelTransvection c : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) v := by
  intro x y h
  change (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 6 → ZMod 2)
    (labelTransvection c)) x =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 6 → ZMod 2)
        (labelTransvection c)) y at h
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 6 → ZMod 2)
    (labelTransvection c)).injective h

private theorem bitVec_tauL_eq_transvection (c x : ℕ) :
    bitVec (tauL c x) =
      (labelTransvection c : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) (bitVec x) := by
  rw [bitVec_tauL]
  rfl

private theorem bitVec_tauL_ne_zero {c x : ℕ} (hx : bitVec x ≠ 0) :
    bitVec (tauL c x) ≠ 0 := by
  rw [bitVec_tauL_eq_transvection]
  exact fun h => hx (labelTransvection_injective c (by
    simpa only [LinearMap.map_zero] using h))

private theorem tauL_injOn {c x y : ℕ} (hx : x < 64) (hy : y < 64) (h : tauL c x = tauL c y) :
    x = y := by
  apply bitVec_injOn hx hy
  have h' : bitVec (tauL c x) = bitVec (tauL c y) := congrArg bitVec h
  exact labelTransvection_injective c (by
    rwa [bitVec_tauL_eq_transvection, bitVec_tauL_eq_transvection] at h')

private theorem tauL_lt {c x : ℕ} (hc : c < 64) (hx : x < 64) : tauL c x < 64 := by
  unfold tauL
  split_ifs with h
  · have h' := Nat.xor_lt_two_pow (n := 6) hx hc
    norm_num at h'
    exact h'
  · exact hx

private theorem foldl_tauL_lt {cs : List ℕ} (hcs : ∀ c ∈ cs, c < 64) {x : ℕ} (hx : x < 64) :
    cs.foldl (fun x c => tauL c x) x < 64 := by
  induction cs generalizing x with
  | nil => simpa using hx
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact ih (fun d hd => hcs d (List.mem_cons_of_mem _ hd))
      (tauL_lt (hcs c (List.mem_cons_self ..)) hx)

private theorem foldl_tauL_injOn {cs : List ℕ} (hcs : ∀ c ∈ cs, c < 64) {x y : ℕ} (hx : x < 64)
    (hy : y < 64) (h : cs.foldl (fun x c => tauL c x) x = cs.foldl (fun x c => tauL c x) y) :
    x = y := by
  induction cs generalizing x y with
  | nil => simpa using h
  | cons c cs ih =>
    simp only [List.foldl_cons] at h
    exact tauL_injOn hx hy (ih (fun d hd => hcs d (List.mem_cons_of_mem _ hd))
      (tauL_lt (hcs c (List.mem_cons_self ..)) hx)
      (tauL_lt (hcs c (List.mem_cons_self ..)) hy) h)

private theorem foldl_tauL_ne_zero {cs : List ℕ} {x : ℕ} (hx : bitVec x ≠ 0) :
    bitVec (cs.foldl (fun x c => tauL c x) x) ≠ 0 := by
  induction cs generalizing x with
  | nil => simpa using hx
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact ih (bitVec_tauL_ne_zero hx)

private theorem pairing_tauL_tauL (c x y : ℕ) :
    pairing (bitVec (tauL c x)) (bitVec (tauL c y)) = pairing (bitVec x) (bitVec y) := by
  have hg : ∀ u v : Fin 6 → ZMod 2,
      b0 ((labelTransvection c : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) u)
        ((labelTransvection c : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) v) = b0 u v :=
    (mem_bilinIsometryGroup (R := ZMod 2) (M := Fin 6 → ZMod 2) (B := b0)
      (g := labelTransvection c)).mp
      (BinarySymplecticTransvection.transvection_mem_bilinIsometryGroup b0_isAlt (bitVec c))
  rw [bitVec_tauL_eq_transvection, bitVec_tauL_eq_transvection, ← b0_apply, ← b0_apply, hg]

private theorem tauL_eq_of_pairing_eq_zero {c x : ℕ} (h : pairing (bitVec c) (bitVec x) = 0) :
    tauL c x = x := by
  have h' : pairing (bitVec x) (bitVec c) = 0 := by
    rw [← b0_apply, ← b0_symm, b0_apply]
    exact h
  unfold tauL
  rw [if_neg]
  intro h1
  rw [h'] at h1
  exact zero_ne_one h1

private theorem foldl_tauL_eq_of_pairing_eq_zero {cs : List ℕ} {a : ℕ}
    (h : ∀ c ∈ cs, pairing (bitVec a) (bitVec c) = 0) :
    cs.foldl (fun x c => tauL c x) a = a := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have hca : tauL c a = a := tauL_eq_of_pairing_eq_zero (by
      rw [← b0_apply, ← b0_symm, b0_apply]
      exact h c (List.mem_cons_self ..))
    rw [hca]
    exact ih fun d hd => h d (List.mem_cons_of_mem _ hd)

end Labels

section Lifts

variable {E : Type*} [Group E]
  {ρ : E →* LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2)}
  (hρ : ρ.range = bilinIsometryGroup b0) (hC : ρ.ker ≤ center E)

include hρ hC in
private theorem pairing_and_commutatorElement_foldl_tauL_eq {cs : List ℕ} {a b : ℕ}
    (hab : pairing (bitVec a) (bitVec b) = 0) :
    pairing (bitVec (cs.foldl (fun x c => tauL c x) a))
        (bitVec (cs.foldl (fun x c => tauL c x) b)) = 0 ∧
      ⁅liftT hρ (bitVec (cs.foldl (fun x c => tauL c x) a)),
        liftT hρ (bitVec (cs.foldl (fun x c => tauL c x) b))⁆ =
        ⁅liftT hρ (bitVec a), liftT hρ (bitVec b)⁆ := by
  induction cs generalizing a b with
  | nil => exact ⟨hab, rfl⟩
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have horth0 : pairing (bitVec (tauL c a)) (bitVec (tauL c b)) = 0 := by
      rw [pairing_tauL_tauL, hab]
    obtain ⟨ih1, ih2⟩ := ih horth0
    refine ⟨ih1, ?_⟩
    rw [ih2]
    rw [bitVec_tauL, bitVec_tauL]
    exact commutatorElement_liftT_conj hρ hC (by rwa [b0_apply]) (bitVec c)

include hρ hC in
theorem commutatorElement_liftT_eq_of_orth {a b : Fin 6 → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (h0 : b0 a b = 0) :
    ⁅liftT hρ a, liftT hρ b⁆ = ⁅liftT hρ (bitVec 2), liftT hρ (bitVec 8)⁆ := by
  obtain ⟨m, hm, hm0, rfl⟩ := exists_bitVec_eq ha
  obtain ⟨n, hn, hn0, rfl⟩ := exists_bitVec_eq hb
  have hmn : m ≠ n := fun h => hab (by rw [h])
  set cs1 := toTwo.getD m [] with hcs1
  set m1 := cs1.foldl (fun x c => tauL c x) m with hm1
  set n1 := cs1.foldl (fun x c => tauL c x) n with hn1
  have hm1eq : m1 = 2 := toTwo_check m hm hm0
  have hcs1lt : ∀ c ∈ cs1, c < 64 := toTwo_lt m hm
  have hn1lt : n1 < 64 := foldl_tauL_lt hcs1lt hn
  have hn1bv : bitVec n1 ≠ 0 := foldl_tauL_ne_zero hb
  have hn1ne0 : n1 ≠ 0 := by
    intro h
    exact hn1bv (by rw [h]; funext i; simp [bitVec])
  have hpair0 : pairing (bitVec m) (bitVec n) = 0 := by rwa [b0_apply] at h0
  have hphase1 := pairing_and_commutatorElement_foldl_tauL_eq hρ hC hpair0 (cs := cs1)
  have hpair1 : pairing (bitVec 2) (bitVec n1) = 0 := by
    have h' := hphase1.1
    rw [← hm1, ← hn1] at h'
    simpa only [hm1eq] using h'
  have hn1ne2 : n1 ≠ 2 := by
    intro h
    have heq : cs1.foldl (fun x c => tauL c x) m = cs1.foldl (fun x c => tauL c x) n := by
      rw [← hm1, ← hn1, hm1eq, h]
    exact hmn (foldl_tauL_injOn hcs1lt hm hn heq)
  set cs2 := toEight.getD n1 [] with hcs2
  have hcs2lt : ∀ c ∈ cs2, c < 64 := toEight_lt n1 hn1lt
  have hcs2orth : ∀ c ∈ cs2, pairing (bitVec 2) (bitVec c) = 0 :=
    toEight_moves_orth n1 hn1lt hn1ne0 hn1ne2 hpair1
  have hn2eq : cs2.foldl (fun x c => tauL c x) n1 = 8 :=
    toEight_check n1 hn1lt hn1ne0 hn1ne2 hpair1
  have hfix2 : cs2.foldl (fun x c => tauL c x) 2 = 2 :=
    foldl_tauL_eq_of_pairing_eq_zero hcs2orth
  have hphase2 := pairing_and_commutatorElement_foldl_tauL_eq hρ hC hpair1 (cs := cs2)
  calc
    ⁅liftT hρ (bitVec m), liftT hρ (bitVec n)⁆ =
        ⁅liftT hρ (bitVec m1), liftT hρ (bitVec n1)⁆ := hphase1.2.symm
    _ = ⁅liftT hρ (bitVec 2), liftT hρ (bitVec n1)⁆ := by rw [hm1eq]
    _ = ⁅liftT hρ (bitVec (cs2.foldl (fun x c => tauL c x) 2)),
          liftT hρ (bitVec (cs2.foldl (fun x c => tauL c x) n1))⁆ := hphase2.2.symm
    _ = ⁅liftT hρ (bitVec 2), liftT hρ (bitVec 8)⁆ := by rw [hfix2, hn2eq]

end Lifts

section Bound

variable {E : Type*} [Group E]
  {ρ : E →* LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2)}
  (hρ : ρ.range = bilinIsometryGroup b0) (hC : ρ.ker ≤ center E)
  (h2 : ∀ c ∈ ρ.ker, c ^ 2 = 1)

include hρ hC h2 in
theorem card_quotient_zpowers_liftT_sq_le
    [Finite E] [Group.IsPerfect E] :
    Nat.card (E ⧸ zpowers (liftT hρ (bitVec 2) ^ 2)) ≤ 1451520 := by
  classical
  set lam := liftT hρ (bitVec 2) ^ 2 with hlam
  have hlamC : lam ∈ ρ.ker := liftT_sq_mem hρ (bitVec 2)
  set N := zpowers lam with hN
  have hNZ : N ≤ center E := zpowers_le.mpr (hC hlamC)
  have : N.Normal := normal_of_le_center hNZ
  have hR : closure (Set.range (genL hρ)) = ⊤ := by
    have hmap : ρ.range ≤ (closure (Set.range (genL hρ))).map ρ := by
      rw [hρ, ← closure_tau_vE, MonoidHom.map_closure, ← Set.range_comp]
      refine closure_mono fun g hg => ?_
      obtain ⟨i, rfl⟩ := hg
      exact ⟨i, map_genL hρ i⟩
    have hlift : ∀ e : E, ∃ r ∈ closure (Set.range (genL hρ)), ρ r = ρ e := fun e => by
      obtain ⟨r, hr, hre⟩ := hmap ⟨e, rfl⟩
      exact ⟨r, hr, hre⟩
    have hcomm : commutator E ≤ closure (Set.range (genL hρ)) := by
      rw [commutator_eq_closure, closure_le]
      rintro _ ⟨e₁, e₂, rfl⟩
      obtain ⟨r₁, hr₁, h₁⟩ := hlift e₁
      obtain ⟨r₂, hr₂, h₂⟩ := hlift e₂
      rw [SetLike.mem_coe, commutatorElement_eq_of_map_eq ρ hC h₁ h₂, commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hr₁ hr₂) (inv_mem hr₁)) (inv_mem hr₂)
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := E)]
    exact hcomm
  obtain ⟨hsq, hcube, hnon⟩ := genL_rels hρ hC h2
  have hmk : (lam : E ⧸ N) = 1 := (QuotientGroup.eq_one_iff lam).mpr (mem_zpowers lam)
  set y : Fin 7 → E ⧸ N := fun i => QuotientGroup.mk (genL hρ i) with hy
  have hfam : IsW7Family y := by
    refine ⟨fun i => ?_, fun i j hij => ?_, fun i k hne hik => ?_⟩
    · rw [hy, ← QuotientGroup.mk_pow, hsq i, hmk]
    · rw [hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, hcube i j hij,
        QuotientGroup.mk_one]
    · rw [hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, hnon i k hne hik, hmk]
  have hgen : closure (Set.range y) = ⊤ := by
    have h1 : Set.range y = (QuotientGroup.mk' N) '' Set.range (genL hρ) := by
      rw [← Set.range_comp]
      rfl
    rw [h1, ← MonoidHom.map_closure, hR, ← MonoidHom.range_eq_map,
      QuotientGroup.range_mk']
  exact card_le_of_perfect inferInstance hgen hfam

include hρ hC h2 in
theorem liftT_sq_ne_one_of_card_ker_eq_two
    [Finite E] [Group.IsPerfect E]
    (hker : Nat.card ρ.ker = 2) : liftT hρ (bitVec 2) ^ 2 ≠ 1 := by
  intro hlam
  have hle := card_quotient_zpowers_liftT_sq_le hρ hC h2
  have hz : zpowers (liftT hρ (bitVec 2) ^ 2 : E) = ⊥ := by
    rw [hlam, Subgroup.zpowers_one_eq_bot]
  rw [hz] at hle
  have hle' : Nat.card E ≤ 1451520 := by
    rwa [Nat.card_congr (QuotientGroup.quotientBot (G := E)).toEquiv] at hle
  have hE := ρ.ker.card_mul_index
  rw [Subgroup.index_ker, hρ, card_bilinIsometryGroup_b0, hker] at hE
  have hEcard : Nat.card E = 2 * 1451520 := by
    rw [← hE]
  omega

end Bound

end SixCoverTwoKernel

end CFSG.LocalAnalysis.ComponentInitial
