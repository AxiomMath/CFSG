module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43MasonStep
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43MasonBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Parity

public section

universe u

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace GMS43

theorem exists_isConj_iff_mul_zpow_aux (n : ℕ) : ∀ {Q : Type u} [Group Q] [Finite Q],
    Nat.card Q = n → IsPGroup 2 Q → ∀ {j z : Q}, j * j = 1 →
    (∀ a b : Q, a * j = j * a → b * j = j * b → a * b = b * a) →
    (∀ y : Q, y * j = j * y → y * y = 1 → y = 1 ∨ y = j ∨ y = z ∨ y = j * z) →
    ∃ w : Q, ∀ x : Q, IsConj j x ↔ ∃ i : ℤ, x = j * w ^ i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ hn hP j z hj hC hinv
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hjZ : j ∈ center Q
  · refine ⟨1, fun x => ?_⟩
    simp only [one_zpow, mul_one, exists_const]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      rw [← hc, mem_center_iff.mp hjZ c, mul_assoc, mul_inv_cancel, mul_one]
    · rintro rfl
      exact IsConj.refl _
  have hj1 : j ≠ 1 := fun h => hjZ (h ▸ one_mem _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hzj : Nat.card (zpowers j) = 2 ^ 1 := by
    rw [Nat.card_zpowers, pow_one, orderOf_eq_prime (by rw [pow_two]; exact hj) hj1]
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    have hdvd : Nat.card (zpowers j) ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card _
    rw [hzj, hk] at hdvd
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 1 with h | h
      · obtain rfl : k = 0 := by omega
        norm_num at hdvd
      · omega
    have htop : zpowers j = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hzj, hk, hk1])
    apply hjZ
    rw [mem_center_iff]
    intro g
    have hg : g ∈ zpowers j := htop ▸ mem_top g
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (Commute.refl j) i).eq
  obtain ⟨M, hMcard, hjMle⟩ := Sylow.exists_subgroup_card_pow_prime_le 2 (n := 1) (m := k - 1)
    (by rw [hk]; exact pow_dvd_pow 2 (by omega)) (zpowers j) hzj (by omega)
  have hM2 : M.index = 2 := by
    have h1 := Subgroup.card_mul_index M
    rw [hMcard, hk, show k = k - 1 + 1 by omega, pow_succ, Nat.add_sub_cancel] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hMn : M.Normal := Subgroup.normal_of_index_eq_two hM2
  have hjM : j ∈ M := hjMle (mem_zpowers j)
  have hlt : Nat.card M < n := by
    rw [hMcard, ← hn, hk]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨z', hz'⟩ : ∃ z' : M, z ∈ M → (z' : Q) = z := by
    by_cases hz : z ∈ M
    · exact ⟨⟨z, hz⟩, fun _ => rfl⟩
    · exact ⟨1, fun h => absurd h hz⟩
  obtain ⟨w, hw⟩ := ih (Nat.card M) hlt rfl (hP.to_subgroup M) (j := ⟨j, hjM⟩) (z := z')
    (Subtype.ext hj)
    (fun a b ha hb => Subtype.ext (hC a b (congrArg Subtype.val ha) (congrArg Subtype.val hb)))
    (by
      intro y hyj hyy
      rcases hinv y (congrArg Subtype.val hyj) (congrArg Subtype.val hyy) with h | h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · have hz : z ∈ M := h ▸ y.2
        exact Or.inr (Or.inr (Or.inl (Subtype.ext (h.trans (hz' hz).symm))))
      · have hz : z ∈ M := by
          have h2 := y.2
          rw [h] at h2
          exact (Subgroup.mul_mem_cancel_left M hjM).mp h2
        refine Or.inr (Or.inr (Or.inr (Subtype.ext ?_)))
        rw [h, Subgroup.coe_mul, hz' hz])
  have hMD : ∀ y : Q, (∃ h ∈ M, h * j * h⁻¹ = y) ↔ ∃ i : ℤ, y = j * (w : Q) ^ i := by
    intro y
    constructor
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨i, hi⟩ := (hw ⟨h * j * h⁻¹, M.mul_mem (M.mul_mem hh hjM) (M.inv_mem hh)⟩).mp
        ((isConj_subtype_iff _ _).mpr ⟨h, hh, rfl⟩)
      refine ⟨i, ?_⟩
      have h2 := congrArg Subtype.val hi
      rw [Subgroup.coe_mul, SubgroupClass.coe_zpow] at h2
      exact h2
    · rintro ⟨i, rfl⟩
      obtain ⟨h, hh, hh'⟩ := (isConj_subtype_iff _ _).mp ((hw (⟨j, hjM⟩ * w ^ i)).mpr ⟨i, rfl⟩)
      refine ⟨h, hh, ?_⟩
      rw [hh', Subgroup.coe_mul, SubgroupClass.coe_zpow]
  by_cases hCM : ∀ c : Q, c * j = j * c → c ∈ M
  ·
    obtain ⟨g, hgM⟩ : ∃ g : Q, g ∉ M := by
      by_contra hall
      push Not at hall
      have htop : M = ⊤ := eq_top_iff.mpr fun g _ => hall g
      rw [htop, Subgroup.index_top] at hM2
      norm_num at hM2
    have hg2 : g * g ∈ M := (Subgroup.mul_mem_iff_of_index_two hM2).mpr (iff_of_false hgM hgM)
    have hwidx : 2 * orderOf (w : Q) = (centralizer ({j} : Set Q)).index := by
      have hcl : conjugatesOf (⟨j, hjM⟩ : M) = {y : M | ∃ i : ℤ, y = ⟨j, hjM⟩ * w ^ i} :=
        Set.ext hw
      have h1 : (centralizer ({(⟨j, hjM⟩ : M)} : Set M)).index = orderOf w := by
        rw [Subgroup.index_centralizer_eq_ncard, hcl, ncard_mul_zpow]
      have h2 : centralizer ({(⟨j, hjM⟩ : M)} : Set M) =
          (centralizer ({j} : Set Q)).subgroupOf M := by
        ext y
        rw [mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
        constructor
        · intro hy
          exact congrArg Subtype.val hy
        · intro hy
          exact Subtype.ext hy
      have h3 := Subgroup.relIndex_mul_index (H := centralizer ({j} : Set Q)) (K := M)
        (fun c hc => hCM c (mem_centralizer_singleton_iff.mp hc))
      rw [Subgroup.orderOf_coe, ← h1, h2, ← h3, hM2, mul_comm]
      rfl
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hP) (w : Q)
    have hnot : ∀ i : ℤ, g * j * g⁻¹ ≠ j * (w : Q) ^ i := by
      intro i hi
      have hsub : conjugatesOf j ⊆ {y : Q | ∃ i : ℤ, y = j * (w : Q) ^ i} := by
        intro y hy
        obtain ⟨h, rfl⟩ := isConj_iff.mp hy
        rw [Set.mem_ofPred_eq, ← hMD]
        by_cases hh : h ∈ M
        · exact ⟨h, hh, rfl⟩
        · obtain ⟨h', hh', hh'j⟩ := (hMD _).mpr ⟨i, hi⟩
          have hhg : h * g⁻¹ ∈ M := (Subgroup.mul_mem_iff_of_index_two hM2).mpr
            (iff_of_false hh fun h2 => hgM (inv_mem_iff.mp h2))
          refine ⟨h * g⁻¹ * h', M.mul_mem hhg hh', ?_⟩
          calc h * g⁻¹ * h' * j * (h * g⁻¹ * h')⁻¹ = h * g⁻¹ * (h' * j * h'⁻¹) * g * h⁻¹ := by
                group
            _ = h * j * h⁻¹ := by rw [hh'j]; group
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [← Subgroup.index_centralizer_eq_ncard, ncard_mul_zpow, ← hwidx] at h1
      have h2 : 0 < orderOf (w : Q) := orderOf_pos _
      omega
    obtain ⟨x, -, -, -, -, huniq, hxc⟩ := exists_conj_partner_mem_center hP hj hj1 hjZ hinv
    have hord := orderOf_mul_conj_eq hj hC hinv hMn hjM hg2 hMD hm hnot huniq
      (fun s => mem_center_iff.mp hxc s)
    refine ⟨j * (g * j * g⁻¹), fun y => isConj_iff_of_orderOf_eq_index
      (isConj_mul_zpow hj (isConj_iff.mpr ⟨g, rfl⟩)) ?_ y⟩
    rw [hord, pow_succ, ← hm, mul_comm, hwidx]
  ·
    push Not at hCM
    obtain ⟨c, hcj, hcM⟩ := hCM
    refine ⟨w, fun y => ?_⟩
    rw [← hMD y]
    constructor
    · intro hy
      obtain ⟨h, rfl⟩ := isConj_iff.mp hy
      by_cases hh : h ∈ M
      · exact ⟨h, hh, rfl⟩
      · refine ⟨h * c, (Subgroup.mul_mem_iff_of_index_two hM2).mpr (iff_of_false hh hcM), ?_⟩
        calc h * c * j * (h * c)⁻¹ = h * (c * j) * c⁻¹ * h⁻¹ := by group
          _ = h * j * h⁻¹ := by rw [hcj]; group
    · rintro ⟨h, -, rfl⟩
      exact isConj_iff.mpr ⟨h, rfl⟩

variable {P : Type*} [Group P] [Finite P]

theorem exists_isConj_iff_mul_zpow' (hP : IsPGroup 2 P) {j z : P} (hj : j * j = 1)
    (hC : ∀ a b : P, a * j = j * a → b * j = j * b → a * b = b * a)
    (hinv : ∀ y : P, y * j = j * y → y * y = 1 → y = 1 ∨ y = j ∨ y = z ∨ y = j * z) :
    ∃ w : P, orderOf w = (centralizer ({j} : Set P)).index ∧
      ∀ x : P, IsConj j x ↔ ∃ i : ℤ, x = j * w ^ i := by
  obtain ⟨w, hw⟩ := exists_isConj_iff_mul_zpow_aux (Nat.card P) rfl hP hj hC hinv
  refine ⟨w, ?_, hw⟩
  have hcl : conjugatesOf j = {x : P | ∃ i : ℤ, x = j * w ^ i} := Set.ext hw
  rw [Subgroup.index_centralizer_eq_ncard, hcl, ncard_mul_zpow]

theorem ncard_le_two_mul_of_mul_mem {S T : Set P} (x₀ : P)
    (h : ∀ y ∈ S, y ∉ T → x₀ * y ∈ T) : S.ncard ≤ 2 * T.ncard := by
  have hsub : S ⊆ T ∪ (fun t => x₀⁻¹ * t) '' T := by
    intro y hy
    by_cases hyT : y ∈ T
    · exact Or.inl hyT
    · exact Or.inr ⟨x₀ * y, h y hy hyT, inv_mul_cancel_left x₀ y⟩
  calc S.ncard ≤ (T ∪ (fun t => x₀⁻¹ * t) '' T).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ T.ncard + ((fun t => x₀⁻¹ * t) '' T).ncard := Set.ncard_union_le _ _
    _ = 2 * T.ncard := by rw [Set.ncard_image_of_injective _ (mul_right_injective x₀⁻¹), two_mul]

theorem card_le_of_forall_not_isConj' (hP : IsPGroup 2 P) {j z : P} (hj : j * j = 1)
    (hC : ∀ a b : P, a * j = j * a → b * j = j * b → a * b = b * a)
    (hinv : ∀ y : P, y * j = j * y → y * y = 1 → y = 1 ∨ y = j ∨ y = z ∨ y = j * z)
    {Y : Subgroup P} (hY : ∀ y ∈ Y, y * y = 1) (hYj : ∀ y ∈ Y, ¬ IsConj j y) :
    Nat.card Y ≤ 8 ∧
      (Y ⊓ centralizer ({j} : Set P) = ⊥ → Nat.card Y ≤ 4 ∧
        (Nat.card Y = 4 → ∃ y ∈ Y, orderOf (j * y) = 2 * (centralizer ({j} : Set P)).index)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  have hcardY : Nat.card Y = (Y : Set P).ncard := Nat.card_coe_set_eq (Y : Set P)
  have hjY : ∀ y ∈ Y, y ≠ j := fun y hy h => hYj y hy (by rw [h])
  by_cases hjZ : j ∈ center P
  · have hYsub : (Y : Set P) ⊆ {1, z, j * z} := by
      intro y hy
      rcases hinv y (mem_center_iff.mp hjZ y) (hY y hy) with h | h | h | h
      · simp [h]
      · exact absurd h (hjY y hy)
      · simp [h]
      · simp [h]
    have h3 : Nat.card Y ≤ 3 := by
      rw [hcardY]
      refine (Set.ncard_le_ncard hYsub (Set.toFinite _)).trans ?_
      refine (Set.ncard_insert_le _ _).trans ?_
      have h4 := Set.ncard_insert_le z {j * z}
      rw [Set.ncard_singleton] at h4
      omega
    refine ⟨by omega, fun hYC => ?_⟩
    have hCtop : centralizer ({j} : Set P) = ⊤ :=
      eq_top_iff.mpr fun g _ => mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hjZ g)
    rw [hCtop, inf_top_eq] at hYC
    rw [hYC, Subgroup.card_bot]
    exact ⟨by norm_num, fun h => by norm_num at h⟩
  obtain ⟨w, hwidx, hw⟩ := exists_isConj_iff_mul_zpow' hP hj hC hinv
  obtain ⟨n, hn⟩ := hP.index (centralizer ({j} : Set P))
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      apply hjZ
      rw [h0, pow_zero, Subgroup.index_eq_one] at hn
      rw [mem_center_iff]
      intro g
      exact mem_centralizer_singleton_iff.mp (hn ▸ mem_top g)
    · exact h0
  have hwn : orderOf w = 2 ^ n := hwidx.trans hn
  set ρ := w ^ (2 ^ (n - 1)) with hρdef
  obtain ⟨hρ2, hρ1⟩ := rho_mul_self_and_ne_one hn1 hwn hρdef.symm
  have hρz : w ^ ((2 : ℤ) ^ (n - 1)) = ρ := by
    rw [hρdef, ← zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  have hcl : ∀ i : ℤ, IsConj j (j * w ^ i) := fun i => (hw _).mpr ⟨i, rfl⟩
  have hjw1 : IsConj j (j * w) := by simpa using hcl 1
  have hjw : j * w * j⁻¹ = w⁻¹ := by
    obtain ⟨h, hh⟩ := isConj_iff.mp hjw1
    have h1 : j * w * (j * w) = 1 := by
      rw [← hh, show h * j * h⁻¹ * (h * j * h⁻¹) = h * (j * j) * h⁻¹ by group, hj]
      group
    rw [hjinv]
    calc j * w * j = j * w * (j * w) * w⁻¹ := by group
      _ = w⁻¹ := by rw [h1, one_mul]
  have hjwz : ∀ e : ℤ, j * w ^ e * j⁻¹ = w ^ (-e) := fun e => by
    rw [← conj_zpow, hjw, inv_zpow, zpow_neg]
  have hwj : ∀ e : ℤ, w ^ e * j = j * w ^ (-e) := fun e => by
    calc w ^ e * j = j * (j * w ^ e * j⁻¹) := by
          rw [hjinv, ← mul_assoc, ← mul_assoc, hj, one_mul]
      _ = j * w ^ (-e) := by rw [hjwz]
  have hnorm : ∀ h : P, ∃ k : ℤ, h * w * h⁻¹ = w ^ k ∧ Odd k := by
    intro h
    obtain ⟨a, ha⟩ := (hw (h * j * h⁻¹)).mp (isConj_iff.mpr ⟨h, rfl⟩)
    obtain ⟨c, hc⟩ := (hw (h * (j * w) * h⁻¹)).mp (hjw1.trans (isConj_iff.mpr ⟨h, rfl⟩))
    have hk : h * w * h⁻¹ = w ^ (-a + c) := by
      calc h * w * h⁻¹ = (h * j * h⁻¹)⁻¹ * (h * (j * w) * h⁻¹) := by group
        _ = (j * w ^ a)⁻¹ * (j * w ^ c) := by rw [ha, hc]
        _ = w ^ (-a + c) := by group
    refine ⟨-a + c, hk, ?_⟩
    rcases Int.even_or_odd (-a + c) with ⟨l, hl⟩ | hodd
    · exfalso
      apply hρ1
      have h1 : (h * w * h⁻¹) ^ (2 ^ (n - 1)) = 1 := by
        rw [hk, hl, ← zpow_natCast, ← zpow_mul]
        have h2n : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn1]
        rw [show (l + l) * ((2 ^ (n - 1) : ℕ) : ℤ) = ((2 ^ n : ℕ) : ℤ) * l by
          rw [h2n]; push_cast; ring, zpow_mul, zpow_natCast, ← hwn, pow_orderOf_eq_one, one_zpow]
      rw [conj_pow, ← hρdef] at h1
      calc ρ = h⁻¹ * (h * ρ * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    · exact hodd
  have hρj : ρ * j = j * ρ := by
    have h1 : j * ρ * j⁻¹ = ρ := by
      rw [hρdef, ← conj_pow, hjw, inv_pow, ← hρdef, inv_eq_of_mul_eq_one_right hρ2]
    calc ρ * j = j * ρ * j⁻¹ * j := by rw [h1]
      _ = j * ρ := by group
  have hinv' : ∀ v : P, v * j = j * v → v * v = 1 → v = 1 ∨ v = j ∨ v = ρ ∨ v = j * ρ := by
    have hρne : ρ ≠ j := by
      intro h
      apply hjZ
      have h1 : IsConj j 1 := by
        have h2 := hcl ((2 : ℤ) ^ (n - 1))
        rwa [hρz, h, hj] at h2
      rw [isConj_one_left.mp h1]
      exact one_mem _
    have hzρ : z = ρ ∨ z = j * ρ := by
      rcases hinv ρ hρj hρ2 with h | h | h | h
      · exact absurd h hρ1
      · exact absurd h hρne
      · exact Or.inl h.symm
      · right
        rw [h, ← mul_assoc, hj, one_mul]
    intro v hvj hvv
    rcases hinv v hvj hvv with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hzρ with h' | h' <;> rw [h, h'] <;> simp
    · rcases hzρ with h' | h' <;> rw [h, h']
      · simp
      · rw [← mul_assoc, hj, one_mul]
        simp
  have hform : ∀ y ∈ Y, ∀ (e : ℤ) (d : P), y = w ^ e * d → d * j = j * d → d * d = 1 →
      y * j = j * y := by
    intro y hy e d hyed hdj hdd
    have hpow : ∀ f : ℤ, y = w ^ f → y * j = j * y := by
      intro f hf
      have h1 : w ^ f * w ^ f = 1 := by rw [← hf]; exact hY y hy
      rcases zpow_eq_one_or_eq_of_mul_self hn1 hwn hρdef.symm h1 with h | h <;> rw [hf, h]
      · group
      · exact hρj
    rcases hinv' d hdj hdd with h | h | h | h
    · exact hpow e (by rw [hyed, h, mul_one])
    · exact absurd (by rw [hyed, h, hwj]; exact hcl _) (hYj y hy)
    · exact hpow (e + 2 ^ (n - 1)) (by rw [hyed, h, ← hρz, ← zpow_add])
    · refine absurd ?_ (hYj y hy)
      rw [hyed, h, ← mul_assoc, hwj, mul_assoc, ← hρz, ← zpow_add]
      exact hcl _
  have hpar : ∀ y : P, (∃ b : ℤ, y * j * y⁻¹ = j * w ^ (2 * b)) ∨
      (∃ b : ℤ, y * j * y⁻¹ = j * w ^ (2 * b + 1)) := by
    intro y
    obtain ⟨a, ha⟩ := (hw _).mp (isConj_iff.mpr ⟨y, rfl⟩)
    obtain ⟨b, rfl | rfl⟩ := Int.even_or_odd' a
    · exact Or.inl ⟨b, ha⟩
    · exact Or.inr ⟨b, ha⟩
  have hoo : ∀ y₁ y₂ : P, (∃ b : ℤ, y₁ * j * y₁⁻¹ = j * w ^ (2 * b + 1)) →
      (∃ b : ℤ, y₂ * j * y₂⁻¹ = j * w ^ (2 * b + 1)) →
      ∃ b : ℤ, y₁ * y₂ * j * (y₁ * y₂)⁻¹ = j * w ^ (2 * b) := by
    rintro y₁ y₂ ⟨b₁, h₁⟩ ⟨b₂, h₂⟩
    obtain ⟨k, hk, l, rfl⟩ := hnorm y₁
    refine ⟨b₁ + b₂ * (2 * l + 1) + l + 1, ?_⟩
    calc y₁ * y₂ * j * (y₁ * y₂)⁻¹ = y₁ * (y₂ * j * y₂⁻¹) * y₁⁻¹ := by group
      _ = (y₁ * j * y₁⁻¹) * (y₁ * w * y₁⁻¹) ^ (2 * b₂ + 1) := by rw [h₂, conj_zpow]; group
      _ = j * w ^ (2 * b₁ + 1) * (w ^ (2 * l + 1)) ^ (2 * b₂ + 1) := by rw [h₁, hk]
      _ = j * w ^ (2 * (b₁ + b₂ * (2 * l + 1) + l + 1)) := by
          rw [← zpow_mul, mul_assoc, ← zpow_add,
            show 2 * b₁ + 1 + (2 * l + 1) * (2 * b₂ + 1) = 2 * (b₁ + b₂ * (2 * l + 1) + l + 1) by
              ring]
  have hc : ∀ y ∈ Y, ∀ b : ℤ, y * j * y⁻¹ = j * w ^ (2 * b) → ¬ y * j = j * y →
      w ^ b * y * j = j * (w ^ b * y) ∧ w ^ b * y * (w ^ b * y) = ρ := by
    intro y hy b hb hyC
    have hcj : w ^ b * y * j = j * (w ^ b * y) := by
      have h1 : w ^ b * y * j * (w ^ b * y)⁻¹ = j := by
        calc w ^ b * y * j * (w ^ b * y)⁻¹ = w ^ b * (y * j * y⁻¹) * w ^ (-b) := by group
          _ = w ^ b * j * w ^ b := by rw [hb]; group
          _ = j := by rw [hwj, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
      calc w ^ b * y * j = w ^ b * y * j * (w ^ b * y)⁻¹ * (w ^ b * y) := by group
        _ = j * (w ^ b * y) := by rw [h1]
    obtain ⟨k, hk, -⟩ := hnorm y
    have hyy := hY y hy
    have hcc : w ^ b * y * (w ^ b * y) = w ^ (b + k * b) := by
      calc w ^ b * y * (w ^ b * y) = w ^ b * (y * w ^ b * y⁻¹) * (y * y) := by group
        _ = w ^ (b + k * b) := by
            rw [← conj_zpow, hk, hyy, mul_one, ← zpow_mul, ← zpow_add]
    have hcC : w ^ (b + k * b) * j = j * w ^ (b + k * b) := by
      rw [← hcc]
      calc w ^ b * y * (w ^ b * y) * j = w ^ b * y * (w ^ b * y * j) := by group
        _ = w ^ b * y * (j * (w ^ b * y)) := by rw [hcj]
        _ = (w ^ b * y * j) * (w ^ b * y) := by group
        _ = j * (w ^ b * y) * (w ^ b * y) := by rw [hcj]
        _ = j * (w ^ b * y * (w ^ b * y)) := by group
    have hc2 : w ^ (b + k * b) * w ^ (b + k * b) = 1 := by
      have h1 : j * w ^ (b + k * b) * j⁻¹ = w ^ (b + k * b) := by
        rw [← hcC, mul_assoc, mul_inv_cancel, mul_one]
      rw [hjwz] at h1
      calc w ^ (b + k * b) * w ^ (b + k * b) = w ^ (b + k * b) * w ^ (-(b + k * b)) := by
            rw [h1]
        _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
    refine ⟨hcj, ?_⟩
    rcases zpow_eq_one_or_eq_of_mul_self hn1 hwn hρdef.symm hc2 with h | h
    · exfalso
      apply hyC
      refine hform y hy (-b) (w ^ b * y) (by group) hcj ?_
      rw [hcc, h]
    · rw [hcc, h]
  have hkey : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, ∀ b₁ b₂ : ℤ, y₁ * j * y₁⁻¹ = j * w ^ (2 * b₁) →
      y₂ * j * y₂⁻¹ = j * w ^ (2 * b₂) → ¬ y₁ * j = j * y₁ → ¬ y₂ * j = j * y₂ →
      y₁ * y₂ * j = j * (y₁ * y₂) := by
    intro y₁ hy₁ y₂ hy₂ b₁ b₂ hb₁ hb₂ hy₁C hy₂C
    obtain ⟨hc₁j, hc₁c⟩ := hc y₁ hy₁ b₁ hb₁ hy₁C
    obtain ⟨hc₂j, hc₂c⟩ := hc y₂ hy₂ b₂ hb₂ hy₂C
    set c₁ := w ^ b₁ * y₁ with hc₁
    set c₂ := w ^ b₂ * y₂ with hc₂
    obtain ⟨k, hk, -⟩ := hnorm c₁
    refine hform _ (Y.mul_mem hy₁ hy₂) (-b₁ + -(k * b₂)) (c₁ * c₂) ?_ ?_ ?_
    · calc y₁ * y₂ = w ^ (-b₁) * (c₁ * w ^ (-b₂) * c₁⁻¹) * (c₁ * c₂) := by
            rw [hc₁, hc₂]; group
        _ = w ^ (-b₁ + -(k * b₂)) * (c₁ * c₂) := by
            rw [← conj_zpow, hk, ← zpow_mul, ← zpow_add, show k * -b₂ = -(k * b₂) by ring]
    · calc c₁ * c₂ * j = c₁ * (c₂ * j) := by group
        _ = j * (c₁ * c₂) := by rw [hc₂j, ← mul_assoc, hc₁j, mul_assoc]
    · calc c₁ * c₂ * (c₁ * c₂) = c₁ * (c₂ * c₁) * c₂ := by group
        _ = c₁ * c₁ * (c₂ * c₂) := by rw [hC c₂ c₁ hc₂j hc₁j]; group
        _ = 1 := by rw [hc₁c, hc₂c, hρ2]
  set T₂ : Set P := {y | y ∈ Y ∧ ∃ b : ℤ, y * j * y⁻¹ = j * w ^ (2 * b)} with hT₂
  set T₁ : Set P := {y | y ∈ Y ∧ y * j = j * y} with hT₁
  have hodd : ∀ y ∈ (Y : Set P), y ∉ T₂ → ∃ b : ℤ, y * j * y⁻¹ = j * w ^ (2 * b + 1) :=
    fun y hy hyT => (hpar y).resolve_left fun h => hyT ⟨hy, h⟩
  have h1 : (Y : Set P).ncard ≤ 2 * T₂.ncard := by
    by_cases hex : ∃ y₀ ∈ (Y : Set P), y₀ ∉ T₂
    · obtain ⟨y₀, hy₀, hy₀T⟩ := hex
      exact ncard_le_two_mul_of_mul_mem y₀ fun y hy hyT =>
        ⟨Y.mul_mem hy₀ hy, hoo y₀ y (hodd y₀ hy₀ hy₀T) (hodd y hy hyT)⟩
    · push Not at hex
      exact ncard_le_two_mul_of_mul_mem 1 fun y hy hyT => absurd (hex y hy) hyT
  have h2 : T₂.ncard ≤ 2 * T₁.ncard := by
    by_cases hex : ∃ y₀ ∈ T₂, y₀ ∉ T₁
    · obtain ⟨y₀, ⟨hy₀, b₀, hb₀⟩, hy₀T⟩ := hex
      refine ncard_le_two_mul_of_mul_mem y₀ fun y hy hyT => ?_
      obtain ⟨hyY, b, hb⟩ := hy
      exact ⟨Y.mul_mem hy₀ hyY, hkey y₀ hy₀ y hyY b₀ b hb₀ hb (fun h => hy₀T ⟨hy₀, h⟩)
        (fun h => hyT ⟨hyY, h⟩)⟩
    · push Not at hex
      exact ncard_le_two_mul_of_mul_mem 1 fun y hy hyT => absurd (hex y hy) hyT
  have hT₁ρ : T₁ ⊆ {1, ρ} := by
    rintro y ⟨hy, hyj⟩
    rcases hinv' y hyj (hY y hy) with h | h | h | h
    · simp [h]
    · exact absurd h (hjY y hy)
    · simp [h]
    · exact absurd (by rw [h, ← hρz]; exact hcl _) (hYj y hy)
  have h3 : T₁.ncard ≤ 2 := by
    refine (Set.ncard_le_ncard hT₁ρ (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  refine ⟨by rw [hcardY]; omega, fun hYC => ?_⟩
  have hT₁1 : T₁.ncard ≤ 1 := by
    have hsub : T₁ ⊆ {1} := by
      rintro y ⟨hy, hyj⟩
      have hyC : y ∈ Y ⊓ centralizer ({j} : Set P) := ⟨hy, mem_centralizer_singleton_iff.mpr hyj⟩
      rw [hYC] at hyC
      exact Subgroup.mem_bot.mp hyC
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (by rw [Set.ncard_singleton])
  refine ⟨by rw [hcardY]; omega, fun h4 => ?_⟩
  obtain ⟨y₀, hy₀, hy₀T⟩ : ∃ y₀ ∈ (Y : Set P), y₀ ∉ T₂ := by
    by_contra hex
    push Not at hex
    have h5 : (Y : Set P).ncard ≤ T₂.ncard :=
      Set.ncard_le_ncard (fun y hy => hex y hy) (Set.toFinite _)
    rw [← hcardY] at h5
    omega
  obtain ⟨b, hb⟩ := hodd y₀ hy₀ hy₀T
  refine ⟨y₀, hy₀, ?_⟩
  have hy₀inv : y₀⁻¹ = y₀ := inv_eq_of_mul_eq_one_right (hY y₀ hy₀)
  have hsq : (j * y₀) ^ 2 = w ^ (2 * b + 1) := by
    rw [pow_two]
    calc j * y₀ * (j * y₀) = j * (y₀ * j * y₀⁻¹) := by rw [hy₀inv]; group
      _ = w ^ (2 * b + 1) := by rw [hb, ← mul_assoc, hj, one_mul]
  have hpow : (j * y₀) ^ (2 ^ n) = ρ := by
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn1]
    rw [h2n, pow_mul, hsq, ← zpow_natCast, ← zpow_mul, mul_comm (2 * b + 1), zpow_mul,
      zpow_natCast, ← hρdef]
    exact (zpow_eq_of_mul_self hρ2 _).2 ⟨b, rfl⟩
  rw [hn, ← pow_succ']
  apply orderOf_eq_prime_pow
  · rw [hpow]
    exact hρ1
  · rw [pow_succ, pow_mul, hpow, pow_two, hρ2]

end GMS43

end CFSG.SeitzReduction.RankOne
