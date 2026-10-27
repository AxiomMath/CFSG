module

public import CFSG.ClassicalInvolution.AschTight.S1911Case2a

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem exists_pow_eq_t (hd : Sec19DataT p f K z S W L t V) {v : G} (hvV : v ∈ V)
    (hV : V = Subgroup.zpowers v) :
    ∃ k : ℕ, 2 ≤ k ∧ Nat.card V = 2 ^ k ∧ orderOf v = 2 ^ k ∧ v ^ 2 ^ (k - 1) = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := S.isPGroup'.to_le (hd.leW.trans hd.hWS)
  obtain ⟨k, hk⟩ := hV2.exists_card_eq
  have h4 := four_le_card hd
  have hk2 : 2 ≤ k := by
    by_contra h
    have h1 : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hk] at h1
    omega
  have hvord : orderOf v = 2 ^ k := by rw [← Nat.card_zpowers, ← hV, hk]
  have hkm : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  refine ⟨k, hk2, hk, hvord, ?_⟩
  have h1 : v ^ 2 ^ (k - 1) * v ^ 2 ^ (k - 1) = 1 := by
    rw [← pow_add, ← two_mul, ← hkm, ← hvord, pow_orderOf_eq_one]
  have h2 : v ^ 2 ^ (k - 1) ≠ 1 := by
    intro h
    have h3 := orderOf_le_of_pow_eq_one (by positivity) h
    rw [hvord, hkm] at h3
    have h5 : 0 < 2 ^ (k - 1) := by positivity
    omega
  rcases hd.invL.unique _ (le_member hd (V.pow_mem hvV _)) h1 with h | h
  · exact absurd h h2
  · exact h

theorem conj_eq_inv_of_conj_eq_mul (hd : Sec19DataT p f K z S W L t V) {r : G}
    (hr : r ∈ (S : Subgroup G) ⊓ K) (hrt : r * t * r⁻¹ = t * z) :
    ∀ u ∈ K ⊓ W, r * u * r⁻¹ = u⁻¹ := by
  have hd0 := hd.toSec19Data
  have hcomm := comm_of_mem hd0
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  have hrW : r ∉ W := by
    intro hrW
    have h1 : r * t * r⁻¹ = t := by rw [hcomm r hrW t (mem_W hd)]; group
    rw [h1] at hrt
    exact hI.ne_one (mul_eq_left.mp hrt.symm)
  have hrU : r ∉ K ⊓ W := fun h => hrW h.2
  have hr2 : r * r ∈ K ⊓ W := by
    have h := inv_mul_mem_of_not_mem_of_card_two_mul hUR (card_inf_eq hd0)
      (((S : Subgroup G) ⊓ K).inv_mem hr) hr
      (fun h => hrU (by simpa using (K ⊓ W).inv_mem h)) hrU
    simpa using h
  obtain ⟨v, hvV, hV⟩ := exists_eq_zpowers_V hd
  have hvK : v ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_mem_W hd0 (hd.leW hvV)
  obtain ⟨d, hd_def⟩ : ∃ d, d = r * v * r⁻¹ * v⁻¹ := ⟨_, rfl⟩
  have hdK : d ∈ K := by
    have h1 : v * r⁻¹ * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hvK _).mp (K.inv_mem hr.2)
    rw [hd_def, show r * v * r⁻¹ * v⁻¹ = r * (v * r⁻¹ * v⁻¹) by group]
    exact K.mul_mem hr.2 h1
  have hrvW : r * v * r⁻¹ ∈ W := by
    have h1 : r * v * r⁻¹ ∈ conjSub r W := mem_conjSub_iff.mpr (by
      rw [show r⁻¹ * (r * v * r⁻¹) * r = v by group]
      exact hd.leW hvV)
    rwa [conjSub_eq_of_mem_inf hd0 hr] at h1
  have hdW : d ∈ W := hd_def ▸ W.mul_mem hrvW (W.inv_mem (hd.leW hvV))
  have hdU : d ∈ K ⊓ W := ⟨hdK, hdW⟩
  have hrv : r * v * r⁻¹ = d * v := by rw [hd_def]; group
  have hrd : r * d * r⁻¹ = d⁻¹ := by
    have h1 : r * r * v = v * (r * r) := hcomm _ hr2.2 v (hd.leW hvV)
    have h3 : r * d * r⁻¹ * (d * v) = v := by
      calc r * d * r⁻¹ * (d * v) = r * d * r⁻¹ * (r * v * r⁻¹) := by rw [hrv]
        _ = r * (d * v) * r⁻¹ := by group
        _ = r * (r * v * r⁻¹) * r⁻¹ := by rw [hrv]
        _ = r * r * v * (r * r)⁻¹ := by group
        _ = v := by rw [h1]; group
    calc r * d * r⁻¹ = r * d * r⁻¹ * (d * v) * v⁻¹ * d⁻¹ := by group
      _ = d⁻¹ := by rw [h3]; group
  obtain ⟨k, hk2, hk, -, hvt⟩ := exists_pow_eq_t hd hvV hV
  have hdv : Commute d v := hcomm d hdW v (hd.leW hvV)
  have hdm : d ^ 2 ^ (k - 1) = z := by
    have h1 : r * t * r⁻¹ = d ^ 2 ^ (k - 1) * t := by
      rw [← hvt, ← conj_pow, hrv, hdv.mul_pow]
    rw [h1] at hrt
    have h2 : d ^ 2 ^ (k - 1) * t = t * d ^ 2 ^ (k - 1) :=
      hcomm _ (W.pow_mem hdW _) t (mem_W hd)
    rw [h2] at hrt
    exact mul_left_cancel hrt
  have hUcard : Nat.card ↥(K ⊓ W) = 2 ^ k := by rw [card_inf_eq_card hd, hk]
  have hdfin : d ^ 2 ^ (k - 1 + 1) = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := ↥(K ⊓ W)) (x := ⟨d, hdU⟩))
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, hUcard] at h
    rwa [show k - 1 + 1 = k by omega]
  have hdord : orderOf d = 2 ^ k := by
    have h := orderOf_eq_prime_pow (p := 2) (n := k - 1) (x := d)
      (by rw [hdm]; exact hI.ne_one) hdfin
    rwa [show k - 1 + 1 = k by omega] at h
  have hUeq : K ⊓ W = Subgroup.zpowers d := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdU) ?_).symm
    rw [Nat.card_zpowers, hdord, hUcard]
  intro u hu
  rw [hUeq] at hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [← conj_zpow, hrd, inv_zpow]

theorem mem_centralizer_inf_of_comm (hd : Sec19DataT p f K z S W L t V) {w r : G} (hwW : w ∈ W)
    (hr : r ∈ (S : Subgroup G) ⊓ K) (hrU : r ∉ K ⊓ W) (hwr : w * r = r * w) :
    w ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  have hd0 := hd.toSec19Data
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  exact mem_centralizer_of_comm hUR (card_inf_eq hd0) hr hrU
    (fun u hu => comm_of_mem hd0 w hwW u hu.2) hwr

theorem le_normalizer_W_of_case2 (hd : Sec19DataT p f K z S W L t V)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) :
    (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
  have hd0 := hd.toSec19Data
  have hcomm := comm_of_mem hd0
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  intro s hs
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  have hsP : conjSub s ((S : Subgroup G) ⊓ K ⊔ V) = (S : Subgroup G) ⊓ K ⊔ V := by
    rw [← inf_sec19X_eq_of_case2 hd h1]
    exact conjSub_eq_of_mem_normalizer (le_normalizer_inf_sec19X hd hs)
  have hW'P : conjSub s W ≤ (S : Subgroup G) ⊓ K ⊔ V := hsP ▸ conjSub_mono (le_inf_sup hd)
  have hcardW' : Nat.card ↥(conjSub s W) = Nat.card W := natCard_conjSub _ s
  by_contra hne
  have hnle : ¬ conjSub s W ≤ W := fun hle => hne (Subgroup.eq_of_le_of_card_ge hle hcardW'.ge)
  obtain ⟨y, hyW', hyW⟩ := Set.not_subset.mp hnle
  obtain ⟨r, hr, hrt⟩ := exists_conj_eq_mul hd
  have hrW : r ∉ W := by
    intro hrW
    have h2 : r * t * r⁻¹ = t := by rw [hcomm r hrW t (mem_W hd)]; group
    rw [h2] at hrt
    exact hI.ne_one (mul_eq_left.mp hrt.symm)
  have hyr : y⁻¹ * r ∈ W := inv_mul_mem_of_not_mem_of_card_two_mul (le_inf_sup hd)
    (card_inf_sup hd) (hW'P hyW') (Subgroup.mem_sup_left hr) hyW hrW
  have hint : W ⊓ conjSub s W ≤ W ⊓ sec19Y K z := by
    rintro w ⟨hwW, hwW'⟩
    rw [inf_sec19Y_eq hd0]
    refine ⟨hwW, mem_centralizer_inf_of_comm hd hwW hr (fun h => hrW h.2) ?_⟩
    have hwy : w * y = y * w := by
      have h2 := hcomm _ (mem_conjSub_iff.mp hwW') _ (mem_conjSub_iff.mp hyW')
      calc w * y = s * (s⁻¹ * w * s * (s⁻¹ * y * s)) * s⁻¹ := by group
        _ = s * (s⁻¹ * y * s * (s⁻¹ * w * s)) * s⁻¹ := by rw [h2]
        _ = y * w := by group
    have hwyr := hcomm w hwW _ hyr
    calc w * r = w * (y * (y⁻¹ * r)) := by group
      _ = y * w * (y⁻¹ * r) := by rw [← mul_assoc, hwy]
      _ = y * (y⁻¹ * r * w) := by rw [mul_assoc, hwyr]
      _ = r * w := by group
  have hidx : W.relIndex ((S : Subgroup G) ⊓ K ⊔ V) = 2 := by
    have h2 := Subgroup.relIndex_mul_card W ((S : Subgroup G) ⊓ K ⊔ V)
    rw [inf_eq_left.mpr (le_inf_sup hd), card_inf_sup hd] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hle2 : W.relIndex (conjSub s W) ≤ 2 := by
    have h2 := Subgroup.relIndex_le_of_le_right (H := W) hW'P (by rw [hidx]; norm_num)
    rwa [hidx] at h2
  have h2 := Subgroup.relIndex_mul_card W (conjSub s W)
  rw [hcardW'] at h2
  have h3 : Nat.card ↥(W ⊓ conjSub s W) ≤ Nat.card ↥(W ⊓ sec19Y K z) :=
    Subgroup.card_le_of_le hint
  rw [card_inf_sec19Y hd] at h3
  have h4 := card_eq_mul hd
  rw [card_inf_eq_card hd] at h4
  have h5 := four_le_card hd
  have h6 : Nat.card W ≤ 2 * Nat.card V := by
    calc Nat.card W = W.relIndex (conjSub s W) * Nat.card ↥(W ⊓ conjSub s W) := h2.symm
      _ ≤ 2 * Nat.card V := Nat.mul_le_mul hle2 h3
  rw [h4] at h6
  nlinarith

theorem conj_t_eq_or (hd : Sec19DataT p f K z S W L t V)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) {s : G} (hsS : s ∈ (S : Subgroup G)) :
    s * t * s⁻¹ = t ∨ s * t * s⁻¹ = t * z := by
  have htW : s * t * s⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_W_of_case2 hd h1 hsS) t).mp (mem_W hd)
  have h2 : s * t * s⁻¹ * (s * t * s⁻¹) = 1 := by
    rw [show s * t * s⁻¹ * (s * t * s⁻¹) = s * (t * t) * s⁻¹ by group, hd.invL.sq]
    group
  have h3 : s * t * s⁻¹ ≠ 1 := fun h => hd.invL.ne_one (by
    calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
      _ = 1 := by rw [h]; group)
  rcases invol_mem_W hd htW h2 h3 with h | h | h
  · exfalso
    have hsz : s * z * s⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hsS)]
      group
    apply hd.ne
    calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
      _ = s⁻¹ * (s * z * s⁻¹) * s := by rw [h, hsz]
      _ = z := by group
  · exact Or.inl h
  · exact Or.inr h

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
