module

public import CFSG.ClassicalInvolution.AschTight.S1916Omega3

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W : Subgroup G}

theorem sd_normalizer_eq (hd : Sec19Data p f K z S W) :
    Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
  normalizer_eq_centralizer_of_tight hd.tight.toTightBranch

theorem sd_le_centralizer_K (hd : Sec19Data p f K z S W) :
    K ≤ Subgroup.centralizer ({z} : Set G) :=
  le_centralizer_of_tight hd.tight.toTightBranch

theorem sd_le_centralizer_Y (_hd : Sec19Data p f K z S W) :
    sec19Y K z ≤ Subgroup.centralizer ({z} : Set G) :=
  (sec19Y_le_sec19X K z).trans (sec19X_le_centralizer K z)

theorem sd_centralizer_le_normalizer_Y (hd : Sec19Data p f K z S W) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (sec19Y K z : Set G) := by
  intro c hc
  refine mem_normalizer_iff_conjSub_eq.mpr (conjSub_sec19Y hc ?_)
  rw [sd_normalizer_eq hd]
  exact hc

theorem sd_isSylow2In_R (hd : Sec19Data p f K z S W) :
    IsSylow2In ((S : Subgroup G) ⊓ K) K :=
  isSylow2In_inf S hd.hSz (sd_le_centralizer_K hd) (sd_normalizer_eq hd).ge

theorem sd_isSylow2In_Q (hd : Sec19Data p f K z S W) :
    IsSylow2In ((S : Subgroup G) ⊓ sec19Y K z) (sec19Y K z) :=
  isSylow2In_inf S hd.hSz (sd_le_centralizer_Y hd) (sd_centralizer_le_normalizer_Y hd)

omit [Finite G] in
theorem mem_normalizer_inf_of_mem {H : Subgroup G} {s : G} (hs : s ∈ (S : Subgroup G))
    (hH : s ∈ Subgroup.normalizer (H : Set G)) :
    s ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ H : Subgroup G) : Set G) :=
  mem_normalizer_inf (Subgroup.le_normalizer hs) hH

theorem sd_commute_R_Q (hd : Sec19Data p f K z S W) :
    ∀ r ∈ (S : Subgroup G) ⊓ K, ∀ q ∈ (S : Subgroup G) ⊓ sec19Y K z, r * q = q * r := by
  intro r hr q hq
  have hqN : q ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    mem_normalizer_inf_of_mem hq.1 (sd_normalizer_eq hd ▸ hd.hSz hq.1)
  exact (commute_of_mem_centralizerModOdd hq.2 inf_le_right (S.isPGroup'.to_le inf_le_left) hqN
    hr).symm

theorem sd_inf_sup_R_Q (hd : Sec19Data p f K z S W) :
    (S : Subgroup G) ⊓ (K ⊔ sec19Y K z) =
      ((S : Subgroup G) ⊓ K) ⊔ ((S : Subgroup G) ⊓ sec19Y K z) :=
  inf_sup_eq_sup_inf S hd.hSz (sd_le_centralizer_K hd) (sd_le_centralizer_Y hd)
    (sd_normalizer_eq hd).ge (sd_centralizer_le_normalizer_Y hd)

theorem sd_mem_S (hd : Sec19Data p f K z S W) : z ∈ (S : Subgroup G) := by
  have hzK := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_mul_self_eq_one hzK.sq hzK.ne_one
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
    fun s hs => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hs)).symm
          k).eq))
  have h2 : IsPGroup 2 ↥((S : Subgroup G) ⊔ Subgroup.zpowers z) :=
    S.isPGroup'.to_sup_of_normal_right' hz2 hSN
  have h3 := S.is_maximal' h2 le_sup_left
  exact h3 ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem sd_mem_R (hd : Sec19Data p f K z S W) : z ∈ (S : Subgroup G) ⊓ K :=
  ⟨sd_mem_S hd, (isUniqueInvolution_of_tight hd.tight.toTightBranch).mem⟩

theorem sd_mem_Y (hd : Sec19Data p f K z S W) : z ∈ sec19Y K z := by
  have hzK := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hzX : z ∈ sec19X K z := le_sec19X hd.tight.branch.member hzK.mem
  have hzN : z ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer hzK.mem
  refine ⟨hzX, hzN, mem_normalizer_oddCoreOf_of_mem_normalizer hzN, fun l hl => ?_⟩
  have hc : z * l = l * z :=
    (Subgroup.mem_centralizer_singleton_iff.mp ((sd_le_centralizer_K hd) hl)).symm
  rw [commutatorElement_def, hc, mul_inv_cancel_right, mul_inv_cancel]
  exact (oddCoreOf K).one_mem

theorem sd_mem_Q (hd : Sec19Data p f K z S W) : z ∈ (S : Subgroup G) ⊓ sec19Y K z :=
  ⟨sd_mem_S hd, sd_mem_Y hd⟩

theorem sd_isUniqueInvolution_R (hd : Sec19Data p f K z S W) :
    IsUniqueInvolution ((S : Subgroup G) ⊓ K) z := by
  have hzK := isUniqueInvolution_of_tight hd.tight.toTightBranch
  exact ⟨sd_mem_R hd, hzK.ne_one, hzK.sq, fun y hy hy2 => hzK.unique y hy.2 hy2⟩

theorem sd_noncomm_R (hd : Sec19Data p f K z S W) :
    ∃ x ∈ (S : Subgroup G) ⊓ K, ∃ y ∈ (S : Subgroup G) ⊓ K, x * y ≠ y * x := by
  have hR := sd_isSylow2In_R hd
  have hRmem : (S : Subgroup G) ⊓ K ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) hR
  exact (exists_ne_comm_of_mem_rSet hd.tight.branch.odd hd.tight.branch.five
    hd.tight.branch.member hRmem).1

omit [Finite G] in
theorem IsQuaternionSub.noncomm {P : Subgroup G} (hP : IsQuaternionSub P) :
    ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  obtain ⟨a, b, ha4, -, -, hbab, hcl⟩ := hP
  have haP : a ∈ P := hcl ▸ Subgroup.subset_closure (by simp)
  have hbP : b ∈ P := hcl ▸ Subgroup.subset_closure (by simp)
  refine ⟨b, hbP, a, haP, fun h => ?_⟩
  have h1 : a⁻¹ = a := by rw [← hbab, h]; group
  have h2 : a ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← h1]
    exact inv_mul_cancel a
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
  omega

theorem sd_isUniqueInvolution_Q (hd : Sec19Data p f K z S W)
    (hQ : IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z)) :
    IsUniqueInvolution ((S : Subgroup G) ⊓ sec19Y K z) z := by
  have hzK := isUniqueInvolution_of_tight hd.tight.toTightBranch
  refine ⟨sd_mem_Q hd, hzK.ne_one, hzK.sq, fun y hy hy2 => ?_⟩
  by_cases hy1 : y = 1
  · exact Or.inl hy1
  · exact Or.inr (IsQuaternionSub.eq_of_mul_self_eq_one hQ hy (sd_mem_Q hd) hy2 hzK.sq hy1
      hzK.ne_one)

theorem sd_yPrimeData (hd : Sec19Data p f K z S W)
    (hQ : IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z))
    (hcard : Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = Nat.card ↥((S : Subgroup G) ⊓ K)) :
    YPrimeData K z (conjClosure (Subgroup.centralizer ({z} : Set G))
      ((S : Subgroup G) ⊓ sec19Y K z)) ((S : Subgroup G) ⊓ sec19Y K z) := by
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set Q := (S : Subgroup G) ⊓ sec19Y K z with hQdef
  have hQY : Q ≤ sec19Y K z := inf_le_right
  have hY'Y : conjClosure C Q ≤ sec19Y K z := conjClosure_le_of_normalizes hQY fun c hc =>
    mem_normalizer_iff_conjSub_eq.mp (sd_centralizer_le_normalizer_Y hd hc)
  have hQ2 : IsPGroup 2 Q := S.isPGroup'.to_le inf_le_left
  refine ⟨fun c hc => mem_normalizer_iff_conjSub_eq.mpr (conjSub_conjClosure hc),
    hY'Y.trans (sd_le_centralizer_Y hd),
    IsSylow2In.of_le (sd_isSylow2In_Q hd) (le_conjClosure C Q) hY'Y, sd_isUniqueInvolution_Q hd hQ,
    IsQuaternionSub.noncomm hQ, fun R' hR' => ?_, closure_twoElements_eq_conjClosure hQ2,
    fun y hy k hk => (hY'Y hy).2.2.2 k hk⟩
  rw [hR'.natCard_eq (sd_isSylow2In_R hd), hcard]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
