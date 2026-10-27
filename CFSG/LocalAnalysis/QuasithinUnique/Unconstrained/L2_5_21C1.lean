module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21C
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Asc75
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

open scoped Pointwise

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def CaseCClaim1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G) (R : Subgroup ↥(autOn N.S N.K)),
    Lv2520 N t zK → OutFamily N.K N.H → CaseCParams N t zK R →
    ∀ i ∈ N.SC, i ≠ 1 → i * i = 1 → IsComponentIn N.K (Subgroup.centralizer ({i} : Set G))

@[expose] def CaseCClaim2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G) (R : Subgroup ↥(autOn N.S N.K)),
    Lv2520 N t zK → OutFamily N.K N.H → CaseCParams N t zK R →
    (∀ i ∈ N.SC, i ≠ 1 → i * i = 1 → IsComponentIn N.K (Subgroup.centralizer ({i} : Set G))) →
    ∀ i ∈ N.SC, i ≠ 1 → i * i = 1 →
      Subgroup.centralizer ({i} : Set G) ≤ Subgroup.normalizer (N.K : Set G)

@[expose] def CaseCGeneration : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G) (R : Subgroup ↥(autOn N.S N.K)),
    Lv2520 N t zK → OutFamily N.K N.H → CaseCParams N t zK R →
    N.K ≤ Subgroup.closure
      {k : G | k ∈ N.K ∧ ∃ j ∈ N.SCx, j ≠ 1 ∧ j * j = 1 ∧ k * j = j * k}

@[expose] def CaseCGlobal : Prop :=
  Asc75Lemma34Disjoint → ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G)
    (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G) (R : Subgroup ↥(autOn N.S N.K)),
    Lv2520 N t zK → OutFamily N.K N.H → CaseCParams N t zK R → IsL2pType ↥N.K →
    (∀ i ∈ N.SC, i ≠ 1 → i * i = 1 → IsComponentIn N.K (Subgroup.centralizer ({i} : Set G))) →
    (∀ i ∈ N.SC, i ≠ 1 → i * i = 1 →
      Subgroup.centralizer ({i} : Set G) ≤ Subgroup.normalizer (N.K : Set G)) →
    CFSG.conjugate N.K N.x ≠ N.K →
    (∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) → False

section Rank3

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_of_commuting {p : ℕ} (hp : p.Prime) {X Y N : Subgroup G}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hbot : X ⊓ Y = ⊥)
    {x₁ a b : G} (hx₁ : x₁ ∈ X) (ha : a ∈ Y) (hb : b ∈ Y)
    (hox : orderOf x₁ = p) (hoa : orderOf a = p) (hob : orderOf b = p)
    (hab : a * b = b * a) (hba : b ∉ Subgroup.zpowers a)
    (hN₁ : x₁ ∈ N) (hNa : a ∈ N) (hNb : b ∈ N) : 3 ≤ CFSG.Assembly.pRank p N := by
  have : Fact p.Prime := ⟨hp⟩
  have hcardx : Nat.card (Subgroup.zpowers x₁) = p := by rw [Nat.card_zpowers, hox]
  have hcarda : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hoa]
  have hcardb : Nat.card (Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hob]
  have hcab : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Subgroup.zpowers b, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((Commute.zpow_zpow (show Commute a b from hab) i j).eq)
  have hAB : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) ∣ p := by
      rw [← hcardb]; exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact hne (Subgroup.card_eq_one.mp h1)
    · have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers b = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hcardb])
      apply hba
      have : Subgroup.zpowers b ≤ Subgroup.zpowers a := by
        rw [← heq]; exact inf_le_left
      exact this (Subgroup.mem_zpowers b)
  obtain ⟨hY₀card, hY₀set⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers a) (Subgroup.zpowers b) hcab
  rw [hAB, Subgroup.card_bot, mul_one, hcarda, hcardb] at hY₀card
  set Y₀ : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hY₀
  have hY₀Y : Y₀ ≤ Y := sup_le ((Subgroup.zpowers_le).mpr ha) ((Subgroup.zpowers_le).mpr hb)
  have hcx : ∀ u ∈ Subgroup.zpowers x₁, ∀ v ∈ Y₀, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ((Commute.zpow_left (show Commute x₁ v from hXY x₁ hx₁ v (hY₀Y hv)) i).eq)
  obtain ⟨hEcard, hEset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers x₁) Y₀ hcx
  have hxY : Subgroup.zpowers x₁ ⊓ Y₀ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc Subgroup.zpowers x₁ ⊓ Y₀ ≤ X ⊓ Y := inf_le_inf ((Subgroup.zpowers_le).mpr hx₁) hY₀Y
      _ = ⊥ := hbot
  rw [hxY, Subgroup.card_bot, mul_one, hcardx, hY₀card] at hEcard
  set E : Subgroup G := Subgroup.zpowers x₁ ⊔ Y₀ with hE
  have hEcard' : Nat.card E = p ^ 3 := by rw [hEcard]; ring
  have hmemE : ∀ w ∈ E, ∃ i j k : ℤ, w = x₁ ^ i * (a ^ j * b ^ k) := by
    intro w hw
    have hw' : w ∈ ((Subgroup.zpowers x₁ : Set G) * (Y₀ : Set G)) := by
      rw [← hEset]; exact hw
    obtain ⟨u, hu, v, hv, rfl⟩ := hw'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hv' : v ∈ ((Subgroup.zpowers a : Set G) * (Subgroup.zpowers b : Set G)) := by
      rw [← hY₀set]; exact hv
    obtain ⟨u', hu', v', hv', rfl⟩ := hv'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv'
    exact ⟨i, j, k, rfl⟩
  have hcomm3 : ∀ i j k : ℤ, ∀ i' j' k' : ℤ,
      (x₁ ^ i * (a ^ j * b ^ k)) * (x₁ ^ i' * (a ^ j' * b ^ k')) =
        (x₁ ^ i' * (a ^ j' * b ^ k')) * (x₁ ^ i * (a ^ j * b ^ k)) := by
    intro i j k i' j' k'
    have hxa : ∀ n m : ℤ, x₁ ^ n * a ^ m = a ^ m * x₁ ^ n := fun n m =>
      (Commute.zpow_zpow (show Commute x₁ a from hXY x₁ hx₁ a ha) n m).eq
    have hxb : ∀ n m : ℤ, x₁ ^ n * b ^ m = b ^ m * x₁ ^ n := fun n m =>
      (Commute.zpow_zpow (show Commute x₁ b from hXY x₁ hx₁ b hb) n m).eq
    have hab' : ∀ n m : ℤ, a ^ n * b ^ m = b ^ m * a ^ n := fun n m =>
      (Commute.zpow_zpow (show Commute a b from hab) n m).eq
    have hxx : ∀ n m : ℤ, x₁ ^ n * x₁ ^ m = x₁ ^ m * x₁ ^ n := fun n m =>
      (Commute.zpow_zpow (Commute.refl x₁) n m).eq
    have haa : ∀ n m : ℤ, a ^ n * a ^ m = a ^ m * a ^ n := fun n m =>
      (Commute.zpow_zpow (Commute.refl a) n m).eq
    have hbb : ∀ n m : ℤ, b ^ n * b ^ m = b ^ m * b ^ n := fun n m =>
      (Commute.zpow_zpow (Commute.refl b) n m).eq
    have e1 : (x₁ ^ i * (a ^ j * b ^ k)) * (x₁ ^ i' * (a ^ j' * b ^ k')) =
        (x₁ ^ i * x₁ ^ i') * ((a ^ j * a ^ j') * (b ^ k * b ^ k')) := by
      calc (x₁ ^ i * (a ^ j * b ^ k)) * (x₁ ^ i' * (a ^ j' * b ^ k'))
          = x₁ ^ i * (a ^ j * (b ^ k * x₁ ^ i')) * (a ^ j' * b ^ k') := by group
        _ = x₁ ^ i * (a ^ j * (x₁ ^ i' * b ^ k)) * (a ^ j' * b ^ k') := by rw [← hxb]
        _ = x₁ ^ i * ((a ^ j * x₁ ^ i') * b ^ k) * (a ^ j' * b ^ k') := by group
        _ = x₁ ^ i * ((x₁ ^ i' * a ^ j) * b ^ k) * (a ^ j' * b ^ k') := by rw [← hxa]
        _ = (x₁ ^ i * x₁ ^ i') * (a ^ j * (b ^ k * (a ^ j' * b ^ k'))) := by group
        _ = (x₁ ^ i * x₁ ^ i') * (a ^ j * ((b ^ k * a ^ j') * b ^ k')) := by group
        _ = (x₁ ^ i * x₁ ^ i') * (a ^ j * ((a ^ j' * b ^ k) * b ^ k')) := by rw [← hab']
        _ = (x₁ ^ i * x₁ ^ i') * ((a ^ j * a ^ j') * (b ^ k * b ^ k')) := by group
    have e2 : (x₁ ^ i' * (a ^ j' * b ^ k')) * (x₁ ^ i * (a ^ j * b ^ k)) =
        (x₁ ^ i' * x₁ ^ i) * ((a ^ j' * a ^ j) * (b ^ k' * b ^ k)) := by
      calc (x₁ ^ i' * (a ^ j' * b ^ k')) * (x₁ ^ i * (a ^ j * b ^ k))
          = x₁ ^ i' * (a ^ j' * (b ^ k' * x₁ ^ i)) * (a ^ j * b ^ k) := by group
        _ = x₁ ^ i' * (a ^ j' * (x₁ ^ i * b ^ k')) * (a ^ j * b ^ k) := by rw [← hxb]
        _ = x₁ ^ i' * ((a ^ j' * x₁ ^ i) * b ^ k') * (a ^ j * b ^ k) := by group
        _ = x₁ ^ i' * ((x₁ ^ i * a ^ j') * b ^ k') * (a ^ j * b ^ k) := by rw [← hxa]
        _ = (x₁ ^ i' * x₁ ^ i) * (a ^ j' * (b ^ k' * (a ^ j * b ^ k))) := by group
        _ = (x₁ ^ i' * x₁ ^ i) * (a ^ j' * ((b ^ k' * a ^ j) * b ^ k)) := by group
        _ = (x₁ ^ i' * x₁ ^ i) * (a ^ j' * ((a ^ j * b ^ k') * b ^ k)) := by rw [← hab']
        _ = (x₁ ^ i' * x₁ ^ i) * ((a ^ j' * a ^ j) * (b ^ k' * b ^ k)) := by group
    rw [e1, e2, hxx i i', haa j j', hbb k k']
  have hcommE : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, j, k, rfl⟩ := hmemE u hu
    obtain ⟨i', j', k', rfl⟩ := hmemE v hv
    exact hcomm3 i j k i' j' k'
  have hpow : ∀ (g : G) (n : ℤ), g ^ p = 1 → (g ^ n) ^ p = 1 := by
    intro g n hg
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  have hxp : x₁ ^ p = 1 := by rw [← hox]; exact pow_orderOf_eq_one x₁
  have hap : a ^ p = 1 := by rw [← hoa]; exact pow_orderOf_eq_one a
  have hbp : b ^ p = 1 := by rw [← hob]; exact pow_orderOf_eq_one b
  have hexpE : ∀ w ∈ E, w ^ p = 1 := by
    intro w hw
    obtain ⟨i, j, k, rfl⟩ := hmemE w hw
    have hc : Commute (x₁ ^ i) (a ^ j * b ^ k) := by
      have h1 : Commute (x₁ ^ i) (a ^ j) :=
        (Commute.zpow_zpow (show Commute x₁ a from hXY x₁ hx₁ a ha) i j)
      have h2 : Commute (x₁ ^ i) (b ^ k) :=
        (Commute.zpow_zpow (show Commute x₁ b from hXY x₁ hx₁ b hb) i k)
      exact h1.mul_right h2
    have hc2 : Commute (a ^ j) (b ^ k) :=
      Commute.zpow_zpow (show Commute a b from hab) j k
    rw [hc.mul_pow, hc2.mul_pow, hpow x₁ i hxp, hpow a j hap, hpow b k hbp]
    simp
  have hEN : E ≤ N := by
    refine sup_le ((Subgroup.zpowers_le).mpr hN₁) (sup_le ((Subgroup.zpowers_le).mpr hNa)
      ((Subgroup.zpowers_le).mpr hNb))
  have hElem : CFSG.Assembly.IsElemAbelian p E :=
    ⟨IsMulCommutative.mk (Std.Commutative.mk fun u v => Subtype.ext (hcommE u u.2 v v.2)), hexpE⟩
  unfold CFSG.Assembly.pRank
  apply le_csSup
  · refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E', _, _, hk⟩
    calc k ≤ p ^ k := (Nat.lt_pow_self hp.one_lt).le
      _ = Nat.card E' := hk.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group E'
  · exact ⟨E, hEN, hElem, hEcard'⟩

end Rank3

section Alt6

theorem exists_commuting_order_three_alt6 :
    ∃ a b : alternatingGroup (Fin 6), a * b = b * a ∧ orderOf a = 3 ∧ orderOf b = 3 ∧
      b ∉ Subgroup.zpowers a := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let a : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let b : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  have ha3 : a ^ 3 = 1 := by decide
  have hb3 : b ^ 3 = 1 := by decide
  have ha1 : a ≠ 1 := by decide
  have hb1 : b ≠ 1 := by decide
  have hab : a * b = b * a := by decide
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  refine ⟨a, b, hab, hoa, hob, ?_⟩
  intro hmem
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hmod : a ^ (n % 3) = a ^ n := by
    have := zpow_mod_orderOf a n
    rwa [hoa] at this
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rw [← hmod] at hn
  rcases hcases with h | h | h
  · rw [h] at hn
    have : (1 : alternatingGroup (Fin 6)) = b := by simpa using hn
    exact hb1 this.symm
  · rw [h] at hn
    have : a = b := by simpa using hn
    exact absurd this (by decide)
  · rw [h] at hn
    have : a * a = b := by simpa [zpow_two, sq] using hn
    exact absurd this (by decide)


end Alt6

section Commuting

theorem conj_conj_aux {G : Type} [Group G] (x y z : G) :
    x * ((x * y * x⁻¹) * (x⁻¹ * z * x) * (x * y * x⁻¹)⁻¹) * x⁻¹ =
      (x * (x * y * x⁻¹) * x⁻¹) * z * (x * (x * y * x⁻¹) * x⁻¹)⁻¹ := by
  simp only [mul_inv_rev, inv_inv, mul_assoc]

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G}

theorem Lv2520.SCx_eq_inf_centralizer (h : Lv2520 N t zK) :
    N.SCx = N.S ⊓ Subgroup.centralizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G) := by
  have hSx : CFSG.conjugate N.S N.x = N.S :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr N.x_mem.2
  have hSC : N.SC = N.S ⊓ Subgroup.centralizer (N.K : Set G) := by
    unfold Notation25.SC
    rw [h.concl2520]
  unfold Notation25.SCx
  rw [hSC, BenderBranch.conjugate_inf, BenderBranch.conjugate_centralizer, hSx]

theorem Lv2520.conjugate_K_ne (h : Lv2520 N t zK) : CFSG.conjugate N.K N.x ≠ N.K := by
  intro heq
  have h1 : N.SCx = N.SC := by
    rw [h.SCx_eq_inf_centralizer, heq]
    unfold Notation25.SC
    rw [h.concl2520]
  have h2 := h.SCx_inf_SC
  rw [h1, inf_idem] at h2
  exact h.facts254.SC_ne_bot h2

theorem Lv2520.caseC_K_le_normalizer_conj (_h : Lv2520 N t zK)
    (hnorm : ∀ i ∈ N.SC, i ≠ 1 → i * i = 1 →
      Subgroup.centralizer ({i} : Set G) ≤ Subgroup.normalizer (N.K : Set G))
    (hgen : N.K ≤ Subgroup.closure
      {k : G | k ∈ N.K ∧ ∃ j ∈ N.SCx, j ≠ 1 ∧ j * j = 1 ∧ k * j = j * k}) :
    N.K ≤ Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G) := by
  refine hgen.trans ((Subgroup.closure_le _).mpr ?_)
  rintro k ⟨hkK, j, hjB, hj1, hj2, hkj⟩
  have hi : N.x * j * N.x⁻¹ ∈ N.SC := Notation25.mem_SCx.mp hjB
  have hi1 : N.x * j * N.x⁻¹ ≠ 1 := by
    intro h1
    apply hj1
    calc j = N.x⁻¹ * (N.x * j * N.x⁻¹) * N.x := by group
      _ = 1 := by rw [h1]; group
  have hi2 : (N.x * j * N.x⁻¹) * (N.x * j * N.x⁻¹) = 1 := by
    calc (N.x * j * N.x⁻¹) * (N.x * j * N.x⁻¹) = N.x * (j * j) * N.x⁻¹ := by group
      _ = 1 := by rw [hj2]; group
  have hcent : N.x * k * N.x⁻¹ ∈ Subgroup.centralizer ({N.x * j * N.x⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc N.x * k * N.x⁻¹ * (N.x * j * N.x⁻¹) = N.x * (k * j) * N.x⁻¹ := by group
      _ = N.x * (j * k) * N.x⁻¹ := by rw [hkj]
      _ = N.x * j * N.x⁻¹ * (N.x * k * N.x⁻¹) := by group
  have hn := hnorm _ hi hi1 hi2 hcent
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro y
  rw [BenderBranch.mem_conjugate_iff, BenderBranch.mem_conjugate_iff]
  have h3 := (Subgroup.mem_normalizer_iff.mp hn) (N.x * y * N.x⁻¹)
  have e : (N.x * k * N.x⁻¹) * (N.x * y * N.x⁻¹) * (N.x * k * N.x⁻¹)⁻¹ =
      N.x * (k * y * k⁻¹) * N.x⁻¹ := by group
  rw [e] at h3
  exact h3

theorem Lv2520.conjugate_K_le_normalizer (h : Lv2520 N t zK)
    (hKN : N.K ≤ Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G)) :
    CFSG.conjugate N.K N.x ≤ Subgroup.normalizer (N.K : Set G) := by
  intro y hy
  rw [BenderBranch.mem_conjugate_iff] at hy
  have h1 : N.x * y * N.x⁻¹ ∈ Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G) :=
    hKN hy
  have h2 : N.x * (N.x * y * N.x⁻¹) * N.x⁻¹ ∈ Subgroup.normalizer (N.K : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro z
    have h3 := h1 (N.x⁻¹ * z * N.x)
    rw [BenderBranch.mem_conjugate_iff, BenderBranch.mem_conjugate_iff] at h3
    have e1 : N.x * (N.x⁻¹ * z * N.x) * N.x⁻¹ = z := by group
    have e2 := conj_conj_aux N.x y z
    rw [e1, e2] at h3
    exact h3
  have hx2 : N.x * N.x ∈ Subgroup.normalizer (N.K : Set G) := by
    have : N.x ^ 2 ∈ N.S := N.x_sq
    rw [pow_two] at this
    exact h.S_le_normalizer this
  have e : N.x * (N.x * y * N.x⁻¹) * N.x⁻¹ = (N.x * N.x) * y * (N.x * N.x)⁻¹ := by group
  rw [e] at h2
  have h4 : y = (N.x * N.x)⁻¹ * ((N.x * N.x) * y * (N.x * N.x)⁻¹) * (N.x * N.x) := by group
  rw [h4]
  exact (Subgroup.normalizer (N.K : Set G)).mul_mem
    ((Subgroup.normalizer (N.K : Set G)).mul_mem
      ((Subgroup.normalizer (N.K : Set G)).inv_mem hx2) h2) hx2

theorem Lv2520.K_inf_conjugate_eq_bot (h : Lv2520 N t zK)
    (hKN : N.K ≤ Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G)) :
    N.K ⊓ CFSG.conjugate N.K N.x = ⊥ := by
  have hsimple : IsSimpleGroup ↥N.K := h.facts258.simple
  have hnormal : ((N.K ⊓ CFSG.conjugate N.K N.x).subgroupOf N.K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hk' : k ∈ Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G) :=
      hKN hk
    have h1 := (Subgroup.mem_normalizer_iff.mp hk') y
    have h2 : y ∈ N.K ↔ k * y * k⁻¹ ∈ N.K :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk)) y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨h2.mp hy1, h1.mp hy2⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨h2.mpr hy1, h1.mpr hy2⟩
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · rw [Subgroup.subgroupOf_eq_bot] at hbot
    have h1 := disjoint_iff.mp hbot
    rwa [inf_eq_left.mpr (inf_le_left : N.K ⊓ CFSG.conjugate N.K N.x ≤ N.K)] at h1
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at htop
    have hle : N.K ≤ CFSG.conjugate N.K N.x := fun k hk => (htop hk).2
    have hcard : Nat.card ↥(CFSG.conjugate N.K N.x) ≤ Nat.card ↥N.K := by
      rw [BenderBranch.card_conjugate]
    exact h.conjugate_K_ne (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem Lv2520.caseC_commute (h : Lv2520 N t zK)
    (hKN : N.K ≤ Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G)) :
    ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k := by
  have hKx := h.conjugate_K_le_normalizer hKN
  have hinf := h.K_inf_conjugate_eq_bot hKN
  intro k hk k' hk'
  have h1 : k * k' * k⁻¹ ∈ CFSG.conjugate N.K N.x := by
    have hk'' : k ∈ Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G) := hKN hk
    exact (Subgroup.mem_normalizer_iff.mp hk'' k').mp hk'
  have h2 : k' * k⁻¹ * k'⁻¹ ∈ N.K := by
    have hk'N : k' ∈ Subgroup.normalizer (N.K : Set G) := hKx hk'
    have := (Subgroup.mem_normalizer_iff.mp hk'N k⁻¹).mp (N.K.inv_mem hk)
    exact this
  have hc1 : k * k' * k⁻¹ * k'⁻¹ ∈ CFSG.conjugate N.K N.x :=
    (CFSG.conjugate N.K N.x).mul_mem h1 ((CFSG.conjugate N.K N.x).inv_mem hk')
  have hc2 : k * k' * k⁻¹ * k'⁻¹ ∈ N.K := by
    have e : k * k' * k⁻¹ * k'⁻¹ = k * (k' * k⁻¹ * k'⁻¹) := by group
    rw [e]
    exact N.K.mul_mem hk h2
  have hc : k * k' * k⁻¹ * k'⁻¹ ∈ N.K ⊓ CFSG.conjugate N.K N.x := ⟨hc2, hc1⟩
  rw [hinf, Subgroup.mem_bot] at hc
  calc k * k' = (k * k' * k⁻¹ * k'⁻¹) * (k' * k) := by group
    _ = k' * k := by rw [hc, one_mul]

theorem Lv2520.caseC_not_A6 (h : Lv2520 N t zK)
    (hKN : N.K ≤ Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G))
    (e6 : ↥N.K ≃* alternatingGroup (Fin 6)) : False := by
  have hcomm := h.caseC_commute hKN
  have hinf := h.K_inf_conjugate_eq_bot hKN
  have he : CFSG.Assembly.evenRank G ≤ 2 := hs.setting.qtke.2.2
  obtain ⟨E, hESK, hE4⟩ := h.exists_four_SK
  have hEK : E ≤ N.K := hESK.trans N.SK_le_K
  have hE2 : IsPGroup 2 ↥E := N.tuple.sylow.isPGroup.to_le (hESK.trans N.SK_le_S)
  have hE0 : E ≠ ⊥ := by
    intro hbot
    have := hE4.2
    rw [hbot, Subgroup.card_bot] at this
    omega
  obtain ⟨eN⟩ := h.facts258.four_normalizer E hEK hE4
  have h3 : 3 ∣ Nat.card ↥(N.K ⊓ Subgroup.normalizer (E : Set G)) := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₁, hx₁⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨a', b', hab', hoa', hob', hba'⟩ := exists_commuting_order_three_alt6
  set a₀ : G := ((e6.symm a' : ↥N.K) : G) with ha₀
  set b₀ : G := ((e6.symm b' : ↥N.K) : G) with hb₀
  have ha₀K : a₀ ∈ N.K := (e6.symm a').2
  have hb₀K : b₀ ∈ N.K := (e6.symm b').2
  have hab₀ : a₀ * b₀ = b₀ * a₀ := by
    have := congrArg (fun z : ↥N.K => (z : G)) (show e6.symm a' * e6.symm b' = e6.symm b' * e6.symm a' by
      rw [← map_mul, ← map_mul, hab'])
    exact this
  have hoa₀ : orderOf a₀ = 3 := by
    rw [ha₀, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hoa']
  have hob₀ : orderOf b₀ = 3 := by
    rw [hb₀, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hob']
  have hba₀ : b₀ ∉ Subgroup.zpowers a₀ := by
    intro hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hba'
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    apply e6.symm.injective
    apply Subtype.ext
    rw [map_zpow, Subgroup.coe_zpow]
    exact hn
  set a : G := N.x⁻¹ * a₀ * N.x with ha
  set b : G := N.x⁻¹ * b₀ * N.x with hb
  have haX : a ∈ CFSG.conjugate N.K N.x := by
    rw [BenderBranch.mem_conjugate_iff]
    have : N.x * (N.x⁻¹ * a₀ * N.x) * N.x⁻¹ = a₀ := by group
    rw [ha, this]; exact ha₀K
  have hbX : b ∈ CFSG.conjugate N.K N.x := by
    rw [BenderBranch.mem_conjugate_iff]
    have : N.x * (N.x⁻¹ * b₀ * N.x) * N.x⁻¹ = b₀ := by group
    rw [hb, this]; exact hb₀K
  have hoa : orderOf a = 3 := by
    have := orderOf_injective (MulAut.conj N.x⁻¹).toMonoidHom (MulAut.conj N.x⁻¹).injective a₀
    rw [hoa₀.symm, ← this]
    simp [ha]
  have hob : orderOf b = 3 := by
    have := orderOf_injective (MulAut.conj N.x⁻¹).toMonoidHom (MulAut.conj N.x⁻¹).injective b₀
    rw [hob₀.symm, ← this]
    simp [hb]
  have hab : a * b = b * a := by
    calc a * b = N.x⁻¹ * (a₀ * b₀) * N.x := by rw [ha, hb]; group
      _ = N.x⁻¹ * (b₀ * a₀) * N.x := by rw [hab₀]
      _ = b * a := by rw [ha, hb]; group
  have hba : b ∉ Subgroup.zpowers a := by
    intro hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hba₀
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    have h1 : N.x * a ^ n * N.x⁻¹ = a₀ ^ n := by
      have := conj_zpow (a := N.x) (b := a) (i := n)
      rw [← this, ha]
      congr 1
      group
    have h2 : N.x * b * N.x⁻¹ = b₀ := by rw [hb]; group
    calc a₀ ^ n = N.x * a ^ n * N.x⁻¹ := h1.symm
      _ = N.x * b * N.x⁻¹ := by rw [hn]
      _ = b₀ := h2
  have hxN : (x₁ : G) ∈ Subgroup.normalizer (E : Set G) := (x₁.2).2
  have hx₁K : (x₁ : G) ∈ N.K := (x₁.2).1
  have hox : orderOf (x₁ : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx₁
  have hcent : ∀ y ∈ CFSG.conjugate N.K N.x, y ∈ Subgroup.normalizer (E : Set G) := by
    intro y hy
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact hcomm e (hEK he) y hy
  have hrank := three_le_pRank_of_commuting Nat.prime_three (X := N.K)
    (Y := CFSG.conjugate N.K N.x) (N := Subgroup.normalizer (E : Set G)) hcomm hinf hx₁K haX hbX
    hox hoa hob hab hba hxN (hcent a haX) (hcent b hbX)
  have hloc : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (E : Set G)) := ⟨E, hE0, hE2, rfl⟩
  have hle : CFSG.Assembly.pRank 3 (Subgroup.normalizer (E : Set G)) ≤
      CFSG.Assembly.evenRank G :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) _ hloc
  omega

end Commuting

theorem lemma2521CaseC_of_parts (hAsc : Asc75Lemma34Disjoint) (h1 : CaseCClaim1) (h2 : CaseCClaim2)
    (hgen : CaseCGeneration) (hglobal : CaseCGlobal) : Lemma2521CaseC := by
  intro G _ _ T M hs N t zK R h hfam hp
  have hc1 := h1 G T M hs N t zK R h hfam hp
  have hc2 := h2 G T M hs N t zK R h hfam hp hc1
  have hg := hgen G T M hs N t zK R h hfam hp
  have hKN := h.caseC_K_le_normalizer_conj hc2 hg
  have hcomm := h.caseC_commute hKN
  have hne := h.conjugate_K_ne
  have hL2p : IsL2pType ↥N.K := by
    rcases hfam with hL | ⟨⟨e6⟩, -⟩
    · exact hL
    · exact (h.caseC_not_A6 hKN e6).elim
  exact hglobal hAsc G T M hs N t zK R h hfam hp hL2p hc1 hc2 hne hcomm

end CFSG.QuasithinUnique
