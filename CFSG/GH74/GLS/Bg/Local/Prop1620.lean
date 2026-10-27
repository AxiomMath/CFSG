module

public import CFSG.GH74.GLS.Bg.Local.Prop1620Aux
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ExtB
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution

public section

namespace CFSG.GH74.GLS.Bg.Glauberman

open Subgroup CFSG.QuasithinUnique

variable {G : Type*} [Group G]

structure StrongClosed (P A : Subgroup G) : Prop where
  le : A ≤ P
  isPGroup : IsPGroup 2 P
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  closed : ∀ a ∈ A, ∀ g : G, g * a * g⁻¹ ∈ P → g * a * g⁻¹ ∈ A

namespace StrongClosed

variable {P A D : Subgroup G}

theorem two_pow (h : StrongClosed P A) (hD : D ≤ P) : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k = 1 :=
  fun _ hd => exists_pow_two_pow_eq_one h.isPGroup (hD hd)

theorem le_normalizer [Finite G] (h : StrongClosed P A) : P ≤ normalizer (A : Set G) := by
  intro p hp
  exact mem_normalizer_of_conj_mem fun a ha => h.closed a ha p (mul_mem (mul_mem hp (h.le ha))
    (inv_mem hp))

theorem conj_mem_inf (h : StrongClosed P A) (hDP : D ≤ P) {y b : G}
    (hy : y ∈ normalizer (D : Set G)) (hb : b ∈ A ⊓ D) : y * b * y⁻¹ ∈ A ⊓ D := by
  have hD : y * b * y⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hy b).mp hb.2
  exact ⟨h.closed b hb.1 y (hDP hD), hD⟩

theorem comm_mem_inf (h : StrongClosed P A) (hDP : D ≤ P) {a d : G} (ha : a ∈ A)
    (haN : a ∈ normalizer (D : Set G)) (hd : d ∈ D) : a * d * a⁻¹ * d⁻¹ ∈ A ⊓ D := by
  rw [Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · have h1 : d * a⁻¹ * d⁻¹ ∈ A :=
      h.closed a⁻¹ (inv_mem ha) d (mul_mem (mul_mem (hDP hd) (inv_mem (h.le ha)))
        (inv_mem (hDP hd)))
    have := mul_mem ha h1
    simpa [mul_assoc] using this
  · have h1 : a * d * a⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp haN d).mp hd
    exact mul_mem h1 (inv_mem hd)

theorem inf_normalizer_le_stabSub (h : StrongClosed P A) (hDP : D ≤ P) :
    A ⊓ normalizer (D : Set G) ≤ stabSub D (A ⊓ D) := by
  intro a ha
  exact ⟨ha.2, fun d hd => h.comm_mem_inf hDP ha.1 ha.2 hd,
    fun b hb => h.comm a ha.1 b hb.1⟩

end StrongClosed

theorem eq_one_of_odd_card {R : Subgroup G} (hodd : Odd (Nat.card R)) {r : G} (hr : r ∈ R)
    {j : ℕ} (hj : r ^ 2 ^ j = 1) : r = 1 := by
  have h1 : orderOf r ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hr
  have h2 : orderOf r ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
  have hcop : Nat.Coprime (Nat.card R) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem exists_pow_mem_oddCoreIn [Finite G] {D B : Subgroup G} (hBD : B ≤ D)
    (hDp : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k = 1)
    (hC : Subgroup.centralizer (D : Set G) ≤ oddCoreIn (normalizer (D : Set G)) ⊔ D)
    (hRC : oddCoreIn (normalizer (D : Set G)) ≤ Subgroup.centralizer (D : Set G)) {t : G}
    (ht : t ∈ stabSub D B) : ∃ k : ℕ, t ^ 2 ^ k ∈ oddCoreIn (normalizer (D : Set G)) := by
  obtain ⟨k₁, hk₁⟩ := exists_pow_two_pow_comm hBD hDp ht
  have hu : t ^ 2 ^ k₁ ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hk₁ d hd).symm
  obtain ⟨r, hr, d₁, hd₁, hrd⟩ :=
    mem_sup_iff_mul (hRC.trans (Subgroup.centralizer_le_normalizer _)) (hC hu)
  have hcomm : Commute r d₁ := (Subgroup.mem_centralizer_iff.mp (hRC hr) d₁ hd₁).symm
  obtain ⟨l, hl⟩ := hDp d₁ hd₁
  refine ⟨k₁ + l, ?_⟩
  have : t ^ 2 ^ (k₁ + l) = r ^ 2 ^ l := by
    rw [pow_add, pow_mul, hrd, hcomm.mul_pow, hl, mul_one]
  rw [this]
  exact Subgroup.pow_mem _ hr _

theorem inf_normalizer_le [Finite G] {P A D : Subgroup G} (h : StrongClosed P A)
    (hD : IsAGMember P D) : A ⊓ normalizer (D : Set G) ≤ D := by
  obtain ⟨hDP, -, -, hQ, hC, hRC, -⟩ := hD
  have hRN : oddCoreIn (normalizer (D : Set G)) ≤ normalizer (D : Set G) := oddCoreIn_le _
  have hNR : normalizer (D : Set G) ≤ normalizer (oddCoreIn (normalizer (D : Set G)) : Set G) :=
    le_normalizer_oddCoreIn _
  have hDp := h.two_pow hDP
  have hBD : A ⊓ D ≤ D := inf_le_right
  have hBnorm : ∀ y ∈ normalizer (D : Set G), ∀ b ∈ A ⊓ D, y * b * y⁻¹ ∈ A ⊓ D :=
    fun y hy b hb => h.conj_mem_inf hDP hy hb
  have hTN : stabSub D (A ⊓ D) ≤ normalizer (D : Set G) := fun x hx => hx.1
  have hTnorm : ∀ y ∈ normalizer (D : Set G), ∀ t ∈ stabSub D (A ⊓ D),
      y * t * y⁻¹ ∈ stabSub D (A ⊓ D) := fun y hy t ht => conj_mem_stabSub hBnorm hy ht
  have hTR : stabSub D (A ⊓ D) ≤ normalizer (oddCoreIn (normalizer (D : Set G)) : Set G) :=
    hTN.trans hNR
  have hRnorm : ∀ y ∈ normalizer (D : Set G), ∀ r ∈ oddCoreIn (normalizer (D : Set G)),
      y * r * y⁻¹ ∈ oddCoreIn (normalizer (D : Set G)) :=
    fun y hy r hr => (Subgroup.mem_normalizer_iff.mp (hNR hy) r).mp hr
  have hfwd : ∀ n ∈ normalizer (D : Set G),
      ∀ x ∈ stabSub D (A ⊓ D) ⊔ oddCoreIn (normalizer (D : Set G)),
      n * x * n⁻¹ ∈ stabSub D (A ⊓ D) ⊔ oddCoreIn (normalizer (D : Set G)) := by
    intro n hn x hx
    obtain ⟨t, ht, r, hr, rfl⟩ := mem_sup_iff_mul hTR hx
    have : n * (t * r) * n⁻¹ = (n * t * n⁻¹) * (n * r * n⁻¹) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left (hTnorm n hn t ht))
      (Subgroup.mem_sup_right (hRnorm n hn r hr))
  have hQN : stabSub D (A ⊓ D) ⊔ oddCoreIn (normalizer (D : Set G)) ≤ normalizer (D : Set G) :=
    sup_le hTN hRN
  have hQnormal : ((stabSub D (A ⊓ D) ⊔ oddCoreIn (normalizer (D : Set G))).subgroupOf
      (normalizer (D : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQN]
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hfwd n hn x hx, fun hx => ?_⟩
    have := hfwd n⁻¹ (inv_mem hn) _ hx
    have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
    rwa [e] at this
  have hQ2 : ∀ x ∈ stabSub D (A ⊓ D) ⊔ oddCoreIn (normalizer (D : Set G)),
      ∃ k : ℕ, x ^ 2 ^ k ∈ oddCoreIn (normalizer (D : Set G)) := by
    intro x hx
    obtain ⟨t, ht, r, hr, rfl⟩ := mem_sup_iff_mul hTR hx
    obtain ⟨k, hk⟩ := exists_pow_mem_oddCoreIn hBD hDp hC hRC ht
    obtain ⟨r', hr', hr'eq⟩ := exists_mul_pow_eq (hTR ht) hr (2 ^ k)
    exact ⟨k, by rw [hr'eq]; exact mul_mem hk hr'⟩
  have hTQ := hQ _ le_sup_right hQN hQnormal hQ2
  intro a ha
  have haT : a ∈ stabSub D (A ⊓ D) := h.inf_normalizer_le_stabSub hDP ha
  have haRD := hTQ (Subgroup.mem_sup_left haT)
  obtain ⟨r, hr, d₁, hd₁, hrd⟩ := mem_sup_iff_mul hRN haRD
  have hcomm : Commute r d₁ := (Subgroup.mem_centralizer_iff.mp (hRC hr) d₁ hd₁).symm
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one h.isPGroup (h.le ha.1)
  obtain ⟨l, hl⟩ := hDp d₁ hd₁
  have h1 : a ^ 2 ^ (k + l) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
  have h2 : d₁ ^ 2 ^ (k + l) = 1 := by rw [pow_add, mul_comm, pow_mul, hl, one_pow]
  have h3 : r ^ 2 ^ (k + l) = 1 := by
    rw [hrd, hcomm.mul_pow, h2, mul_one] at h1
    exact h1
  have hr1 : r = 1 := eq_one_of_odd_card (odd_card_oddCoreIn _) hr h3
  rw [hrd, hr1, one_mul]
  exact hd₁

theorem le_of_isAGMember [Finite G] {P A D : Subgroup G} (h : StrongClosed P A)
    (hD : IsAGMember P D) : A ≤ D := by
  have hDP : D ≤ P := hD.1
  have hDA : D ≤ normalizer (A : Set G) := hDP.trans h.le_normalizer
  have hKP : D ⊔ A ≤ P := sup_le hDP h.le
  by_contra hAD
  have hKD : ¬ D ⊔ A ≤ D := fun hle => hAD (le_sup_right.trans hle)
  have : Group.IsNilpotent ↥(D ⊔ A) := (h.isPGroup.to_le hKP).isNilpotent
  have hlt : D.subgroupOf (D ⊔ A) < ⊤ :=
    lt_top_iff_ne_top.mpr fun htop => hKD (Subgroup.subgroupOf_eq_top.mp htop)
  obtain ⟨x, hxN, hxH⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hxD : (x : G) ∉ D := fun hx => hxH (Subgroup.mem_subgroupOf.mpr hx)
  have hxnorm : (x : G) ∈ normalizer (D : Set G) := by
    refine mem_normalizer_of_conj_mem fun d hd => ?_
    have hy : (⟨d, Subgroup.mem_sup_left hd⟩ : ↥(D ⊔ A)) ∈ D.subgroupOf (D ⊔ A) :=
      Subgroup.mem_subgroupOf.mpr hd
    have := Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hxN _).mp hy)
    simpa using this
  obtain ⟨d, hd, a, ha, hxda⟩ := mem_sup_iff_mul hDA x.2
  have haN : a ∈ normalizer (D : Set G) := by
    have : a = d⁻¹ * x := by rw [hxda]; group
    rw [this]
    exact mul_mem (inv_mem (Subgroup.le_normalizer hd)) hxnorm
  have haD : a ∈ D := inf_normalizer_le h hD ⟨ha, haN⟩
  exact hxD (by rw [hxda]; exact mul_mem hd haD)

theorem normalizer_le_of_le [Finite G] {P A D : Subgroup G} (h : StrongClosed P A)
    (hDP : D ≤ P) (hAD : A ≤ D) : normalizer (D : Set G) ≤ normalizer (A : Set G) := by
  intro n hn
  refine mem_normalizer_of_conj_mem fun a ha => ?_
  exact h.closed a ha n (hDP ((Subgroup.mem_normalizer_iff.mp hn a).mp (hAD ha)))

end CFSG.GH74.GLS.Bg.Glauberman

namespace CFSG.GH74.GLS.Bg

open Subgroup CFSG.QuasithinUnique CFSG.GH74.GLS.Stage1.Thm6.Sec13

theorem ig_16_20 : IG_16_20 := by
  intro G _ _ P A hP hAP hcomm hclosed u hu g hg
  have hT : IsSylowTwoOf P ⊤ := ⟨hP.1, hP.2.1, hP.2.2⟩
  have hSC : Glauberman.StrongClosed P A := ⟨hAP, hP.2.1, hcomm, hclosed⟩
  have hPM : P ≤ normalizer (A : Set G) := hSC.le_normalizer
  have hAG : ∀ D : Subgroup G, IsAGMember P D →
      normalizer (D : Set G) ≤ normalizer (A : Set G) := fun D hD =>
    Glauberman.normalizer_le_of_le hSC hD.1 (Glauberman.le_of_isAGMember hSC hD)
  obtain ⟨k, hk⟩ := Glauberman.exists_pow_two_pow_eq_one hP.2.1 hu
  obtain ⟨m, hm, hmeq⟩ := exists_conj_eq_of_ag hT hPM hAG (x := u) (g := g⁻¹) (hPM hu) ⟨k, hk⟩
    (by simpa using hPM hg)
  exact ⟨m⁻¹, inv_mem hm, by simpa using hmeq.symm⟩

end CFSG.GH74.GLS.Bg
