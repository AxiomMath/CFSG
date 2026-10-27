module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Natural
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Quasithin

variable {W : Type*} [CommGroup W]

private theorem exists_zpowers_eq_oTwoUpper {G : Type*} [Group G] {L : Subgroup G}
    (hL : Nat.card L = 6) : ∃ a : G, a ^ 3 = 1 ∧ oTwoUpper L = Subgroup.zpowers a := by
  have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 (by rw [hL]; norm_num)
  have hidx : (Subgroup.zpowers g).index = 2 := by
    have h := (Subgroup.zpowers g).index_mul_card
    rw [Nat.card_zpowers, hg, hL] at h
    omega
  refine ⟨(g : G), ?_, le_antisymm ((Subgroup.closure_le _).mpr ?_) ?_⟩
  · have h3 : g ^ 3 = 1 := hg ▸ pow_orderOf_eq_one g
    exact congrArg Subtype.val h3
  · rintro x ⟨hxL, hxo⟩
    have hcop : Nat.Coprime 2 (orderOf (⟨x, hxL⟩ : L)) := by
      rw [Subgroup.orderOf_mk]
      exact Nat.coprime_two_left.mpr hxo
    have hmem : (⟨x, hxL⟩ : L) ∈ Subgroup.zpowers g :=
      (Subgroup.zpowers_le.mpr (Subgroup.sq_mem_of_index_two hidx _))
        (A4.mem_zpowers_pow_of_coprime hcop)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
  · refine Subgroup.zpowers_le.mpr (mem_oTwoUpper_of_odd g.2 ?_)
    rw [Subgroup.orderOf_coe, hg]
    decide

private theorem zpow_emod_three {G : Type*} [Group G] {a : G} (ha : a ^ 3 = 1) (n : ℤ) :
    a ^ n = a ^ (n % 3) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
  rw [zpow_add, zpow_mul]
  have : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha
  rw [this, one_zpow, mul_one]

private theorem exists_eq_sq_pow {G : Type*} [Group G] {c : G} {k : ℕ} (hck : c ^ 3 ^ k = 1) :
    ∃ m : ℕ, c = (c ^ 2) ^ m := by
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  refine ⟨m + 1, ?_⟩
  calc c = c * c ^ 3 ^ k := by rw [hck, mul_one]
    _ = (c ^ 2) ^ (m + 1) := by
        rw [hm, ← pow_succ', ← pow_mul]
        exact congrArg (c ^ ·) (by omega)

private theorem commute_of_conj_eq_inv {G : Type*} [Group G] {c a : G} {k : ℕ}
    (hck : c ^ 3 ^ k = 1) (h : c * a * c⁻¹ = a⁻¹) : Commute c a := by
  have h2 : Commute (c ^ 2) a := by
    show c ^ 2 * a = a * c ^ 2
    have : c * c * a * (c * c)⁻¹ = a :=
      calc c * c * a * (c * c)⁻¹ = c * (c * a * c⁻¹) * c⁻¹ := by group
        _ = c * a⁻¹ * c⁻¹ := by rw [h]
        _ = (c * a * c⁻¹)⁻¹ := by group
        _ = a := by rw [h, inv_inv]
    rw [pow_two]
    exact mul_inv_eq_iff_eq_mul.mp this
  obtain ⟨m, hm⟩ := exists_eq_sq_pow hck
  have := h2.pow_left m
  rwa [← hm] at this

private theorem commute_of_mem_oTwoUpper {G : Type*} [Group G] {L : Subgroup G}
    (hL : Nat.card L = 6) {c : G} (hc : c ∈ Subgroup.normalizer (L : Set G)) {k : ℕ}
    (hck : c ^ 3 ^ k = 1) {x : G} (hx : x ∈ oTwoUpper L) : Commute c x := by
  obtain ⟨a, ha3, hO⟩ := exists_zpowers_eq_oTwoUpper hL
  have ha : a ∈ oTwoUpper L := hO ▸ Subgroup.mem_zpowers a
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hO ▸ conj_mem_oTwoUpper hc ha)
  rw [zpow_emod_three ha3] at hn
  have hca : Commute c a := by
    have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h3 with h3 | h3 | h3
    · rw [h3, zpow_zero] at hn
      have : a = 1 := by simpa using hn.symm
      rw [this]
      exact Commute.one_right c
    · rw [h3, zpow_one] at hn
      exact mul_inv_eq_iff_eq_mul.mp hn.symm
    · refine commute_of_conj_eq_inv hck ?_
      rw [← hn, h3]
      rw [zpow_two]
      exact eq_inv_of_mul_eq_one_left (by simpa [pow_succ, mul_assoc] using ha3)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hO ▸ hx)
  exact hca.zpow_right j

private theorem sq_mem_oTwoUpper_of_card_eq_six {G : Type*} [Group G] {L : Subgroup G}
    (hL : Nat.card L = 6) {l : G} (hl : l ∈ L) : l ^ 2 ∈ oTwoUpper L := by
  have h6 : l ^ 6 = 1 := by
    have h : (⟨l, hl⟩ : L) ^ Nat.card L = 1 := pow_card_eq_one'
    rw [hL] at h
    exact congrArg Subtype.val h
  refine mem_oTwoUpper_of_odd (L.pow_mem hl 2) ?_
  have : orderOf (l ^ 2) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← pow_mul]; exact h6)
  exact Odd.of_dvd_nat (by decide) this

private theorem sq_mem_iSup_oTwoUpper {Ω : Type*} [Group Ω] (𝓕 : Finset (Subgroup Ω))
    (hsq : ∀ H ∈ 𝓕, ∀ x ∈ H, x ^ 2 ∈ oTwoUpper H)
    (hc : ∀ H ∈ 𝓕, ∀ H' ∈ 𝓕, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a) :
    ∀ x ∈ ⨆ H ∈ 𝓕, H, x ^ 2 ∈ ⨆ H ∈ 𝓕, oTwoUpper H := by
  classical
  induction 𝓕 using Finset.induction_on with
  | empty =>
    intro x hx
    have : (⨆ H ∈ (∅ : Finset (Subgroup Ω)), H) = ⊥ := by simp
    rw [this, Subgroup.mem_bot] at hx
    rw [hx, one_pow]
    exact Subgroup.one_mem _
  | insert H₀ 𝓕 hH₀ ih =>
    intro x hx
    rw [Finset.iSup_insert] at hx
    have hsq' : ∀ H ∈ 𝓕, ∀ x ∈ H, x ^ 2 ∈ oTwoUpper H :=
      fun H hH => hsq H (Finset.mem_insert_of_mem hH)
    have hc' : ∀ H ∈ 𝓕, ∀ H' ∈ 𝓕, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a :=
      fun H hH H' hH' => hc H (Finset.mem_insert_of_mem hH) H' (Finset.mem_insert_of_mem hH')
    have hK : (⨆ H ∈ 𝓕, H) ≤ Subgroup.centralizer (H₀ : Set Ω) := by
      refine iSup₂_le fun H hH b hb => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hne : H₀ ≠ H := fun h => hH₀ (h ▸ hH)
      exact hc H₀ (Finset.mem_insert_self _ _) H (Finset.mem_insert_of_mem hH) hne a ha b hb
    have hnorm : (⨆ H ∈ 𝓕, H) ≤ Subgroup.normalizer (H₀ : Set Ω) :=
      hK.trans (Subgroup.centralizer_le_normalizer _)
    have hx' : x ∈ ((H₀ ⊔ ⨆ H ∈ 𝓕, H : Subgroup Ω) : Set Ω) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left H₀ _ hnorm] at hx'
    obtain ⟨h, hh, k, hk, rfl⟩ := hx'
    have hcomm : Commute h k := Subgroup.mem_centralizer_iff.1 (hK hk) h hh
    rw [hcomm.mul_pow, Finset.iSup_insert]
    exact Subgroup.mul_mem_sup (hsq H₀ (Finset.mem_insert_self _ _) h hh) (ih hsq' hc' k hk)

private theorem mem_normalizer_of_conjAut_eq {c : MulAut W} {L : Subgroup (MulAut W)}
    (h : B1.conjAut c L = L) : c ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h2 : c * y * c⁻¹ ∈ B1.conjAut c L ↔ y ∈ L := by
    rw [B1.mem_conjAut]
    simp [mul_assoc]
  rw [h] at h2
  exact h2.symm

structure BlockData (X : Subgroup (MulAut W)) (I : Finset (Subgroup (MulAut W))) : Prop where
  comm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  indep : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥
  natural : ∀ L ∈ I, ActsAsNaturalL2 L (commV L)
  vindep : ∀ L ∈ I, commV L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L' = ⊥
  perm : ∀ g ∈ X, ∀ L ∈ I, B1.conjAut g L ∈ I ∧
    (commV L).map g.toMonoidHom = commV (B1.conjAut g L)
  le : (⨆ L ∈ I, L) ≤ X

namespace BlockData

variable {X : Subgroup (MulAut W)} {I : Finset (Subgroup (MulAut W))}

theorem comm_of_normalizes (hI : BlockData X I) {c y : MulAut W}
    (hcI : ∀ L ∈ I, B1.conjAut c L = L) (hc3 : ∃ k : ℕ, c ^ 3 ^ k = 1)
    (hy : y ∈ ⨆ L ∈ I, L) (hy3 : ∃ m : ℕ, y ^ 3 ^ m = 1) : c * y = y * c := by
  obtain ⟨k, hk⟩ := hc3
  obtain ⟨m, hm⟩ := hy3
  have hcard : ∀ L ∈ I, Nat.card L = 6 := fun L hL =>
    (S1417.card_of_actsAsNaturalL2 (hI.natural L hL)).1
  have hD : (⨆ L ∈ I, oTwoUpper L) ≤ Subgroup.centralizer ({c} : Set (MulAut W)) := by
    refine iSup₂_le fun L hL x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (commute_of_mem_oTwoUpper (hcard L hL) (mem_normalizer_of_conjAut_eq (hcI L hL)) hk
      hx).eq
  have hsq : y ^ 2 ∈ ⨆ L ∈ I, oTwoUpper L :=
    sq_mem_iSup_oTwoUpper I
      (fun L hL _ hl => sq_mem_oTwoUpper_of_card_eq_six (hcard L hL) hl) hI.comm y hy
  obtain ⟨j, hj⟩ : Odd ((3 : ℕ) ^ m) := Odd.pow (by decide)
  have hyj : y * (y ^ 2) ^ j = 1 := by
    rw [← pow_mul, ← pow_succ', ← hj]
    exact hm
  have hyD : y ∈ ⨆ L ∈ I, oTwoUpper L := by
    rw [eq_inv_of_mul_eq_one_left hyj]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hsq j)
  exact Subgroup.mem_centralizer_iff.mp (hD hyD) c rfl

end BlockData

end CFSG.LocalAnalysis.RankThreeUC
