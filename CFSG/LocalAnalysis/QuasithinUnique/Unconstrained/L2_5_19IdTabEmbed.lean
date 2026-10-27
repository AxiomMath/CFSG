module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open scoped commutatorElement

theorem card_of_psl_three_four_or_j2 {Q : Type} [Group Q]
    (h : StatedClassicalModel Q .PSL 3 2 2 ∨ Nonempty (Q ≃* NativeSporadic.Carrier .J2)) :
    Nat.card Q = 20160 ∨ Nat.card Q = 604800 := by
  rcases h with h | he
  · exact Or.inl (card_of_psl_three_four h)
  · obtain ⟨e⟩ := he
    refine Or.inr ?_
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2

theorem eq_seven_of_prime_dvd {p N : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hN : N = 20160 ∨ N = 604800)
    (hd : p ∣ N) : p = 7 := by
  have key : ∀ a b c : ℕ, p ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 → p = 7 := by
    intro a b c h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
          omega
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
          omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
        omega
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h
  rcases hN with rfl | rfl
  · exact key 6 2 1 (by simpa using hd)
  · exact key 7 3 2 (by simpa using hd)

theorem exists_prime_dvd_card_of_isL2pType {X : Type} [Group X] (h : IsL2pType X) :
    ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ p ∣ Nat.card X := by
  obtain ⟨F, _, _, p, hp, hp7, hF, -, ⟨e⟩⟩ := Out21.model_of_isL2pType h
  exact ⟨p, hp.out, hp7, Out21.prime_dvd_card_of_equiv hp7 hF e⟩

section Pair

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_mul_dvd_of_commuting {X A B : Subgroup G} (hAX : A ≤ X) (hBX : B ≤ X)
    (hc : ⁅A, B⁆ = ⊥) (hA : Subgroup.center ↥A = ⊥) (hB : Subgroup.center ↥B = ⊥) :
    Nat.card ↥A * Nat.card ↥B ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), (a : G) * b = b * a := fun a b =>
    BenderBranch.commute_of_commutator_eq_bot hc a.2 b.2
  let ψ : ↥A × ↥B →* ↥X := MonoidHom.mk'
    (fun p => ⟨(p.1 : G) * (p.2 : G), X.mul_mem (hAX p.1.2) (hBX p.2.2)⟩) (by
      intro p q
      apply Subtype.ext
      show ((p.1 * q.1 : ↥A) : G) * ((p.2 * q.2 : ↥B) : G) = ((p.1 : G) * p.2) * ((q.1 : G) * q.2)
      push_cast
      calc (p.1 : G) * q.1 * (p.2 * q.2) = p.1 * (q.1 * p.2) * q.2 := by group
        _ = p.1 * (p.2 * q.1) * q.2 := by rw [hcomm q.1 p.2]
        _ = _ := by group)
  let φ : ↥A × ↥B →* ↥X ⧸ Subgroup.center ↥X := (QuotientGroup.mk' (Subgroup.center ↥X)).comp ψ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    have hz : ψ (a, b) ∈ Subgroup.center ↥X := by
      have := h
      simpa [φ] using this
    have hzc : ∀ g : ↥X, g * ψ (a, b) = ψ (a, b) * g := Subgroup.mem_center_iff.mp hz
    have hzG : ∀ g : G, g ∈ X → g * ((a : G) * b) = ((a : G) * b) * g := fun g hg =>
      congrArg Subtype.val (hzc ⟨g, hg⟩)
    have ha : a = 1 := by
      have : a ∈ Subgroup.center ↥A := by
        rw [Subgroup.mem_center_iff]
        intro a'
        apply Subtype.ext
        have h1 := hzG (a' : G) (hAX a'.2)
        have h2 : (a' : G) * a * b = a * a' * b := by
          calc (a' : G) * a * b = a' * (a * b) := by group
            _ = (a * b) * a' := h1
            _ = a * (b * a') := by group
            _ = a * (a' * b) := by rw [← hcomm a' b]
            _ = a * a' * b := by group
        exact mul_right_cancel h2
      rw [hA] at this
      exact Subgroup.mem_bot.mp this
    have hb : b = 1 := by
      have : b ∈ Subgroup.center ↥B := by
        rw [Subgroup.mem_center_iff]
        intro b'
        apply Subtype.ext
        have h1 := hzG (b' : G) (hBX b'.2)
        rw [ha] at h1
        simpa using h1
      rw [hB] at this
      exact Subgroup.mem_bot.mp this
    rw [ha, hb]
    rfl
  have := Subgroup.card_dvd_of_injective φ hinj
  rwa [Nat.card_prod] at this

theorem tabNonEmbed_no_pair
    : ∀ (G : Type) [Group G] [Finite G] (X A B : Subgroup G),
    CFSG.IsQuasisimple ↥X → IsPGroup 2 (Subgroup.center ↥X) →
    (StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨
      Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.Carrier .J2)) →
    A ≤ X → B ≤ X → ⁅A, B⁆ = ⊥ → A ⊓ B = ⊥ → IsL2pType ↥A → IsL2pType ↥B → False := by
  intro G _ _ X A B _ _ hM hAX hBX hc _ hA hB
  have hMcard := card_of_psl_three_four_or_j2 hM
  have hdvd := card_mul_dvd_of_commuting hAX hBX hc
    (center_eq_bot_of_simple_nonabelian (l2pFacts _ hA).simple (l2pFacts _ hA).nonabelian)
    (center_eq_bot_of_simple_nonabelian (l2pFacts _ hB).simple (l2pFacts _ hB).nonabelian)
  obtain ⟨pA, hpA, hpA7, hpAd⟩ := exists_prime_dvd_card_of_isL2pType hA
  obtain ⟨pB, hpB, hpB7, hpBd⟩ := exists_prime_dvd_card_of_isL2pType hB
  have hAM : Nat.card ↥A ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := (Dvd.intro _ rfl).trans hdvd
  have hBM : Nat.card ↥B ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := (Dvd.intro_left _ rfl).trans hdvd
  have e7A := eq_seven_of_prime_dvd hpA hpA7 hMcard (hpAd.trans hAM)
  have e7B := eq_seven_of_prime_dvd hpB hpB7 hMcard (hpBd.trans hBM)
  subst e7A e7B
  have h49 : 7 * 7 ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := (Nat.mul_dvd_mul hpAd hpBd).trans hdvd
  omega

end Pair

section Comp

variable {G : Type} [Group G]

@[expose] noncomputable def toCentralQuot {X Y : Subgroup G} (hYX : Y ≤ X) :
    ↥Y →* ↥X ⧸ Subgroup.center ↥X :=
  (QuotientGroup.mk' (Subgroup.center ↥X)).comp (Subgroup.inclusion hYX)

theorem ker_toCentralQuot_le {X Y : Subgroup G} (hYX : Y ≤ X) :
    (toCentralQuot hYX).ker ≤ Subgroup.center ↥Y := by
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have hz : Subgroup.inclusion hYX y ∈ Subgroup.center ↥X := by
    simpa [toCentralQuot] using hy
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y'
  apply Subtype.ext
  exact congrArg (Subtype.val : ↥X → G) (hz (Subgroup.inclusion hYX y'))

theorem card_center_quot_dvd {X Y : Subgroup G} (hYX : Y ≤ X) :
    Nat.card (↥Y ⧸ Subgroup.center ↥Y) ∣ Nat.card (toCentralQuot hYX).range ∧
      Nat.card (toCentralQuot hYX).range ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := by
  refine ⟨?_, Subgroup.card_subgroup_dvd_card _⟩
  have h := Subgroup.index_dvd_of_le (ker_toCentralQuot_le hYX)
  rw [Subgroup.index_ker] at h
  exact h

theorem mem_zpowers_involution {i g : G} (hi2 : i * i = 1) (hg : g ∈ Subgroup.zpowers i) :
    g = 1 ∨ g = i := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hsq : i ^ (2 : ℤ) = 1 := by rw [zpow_two, hi2]
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
  · left
    rw [hn, zpow_mul, hsq, one_zpow]
  · right
    rw [hn, zpow_add_one, zpow_mul, hsq, one_zpow, one_mul]

theorem conj_mem_center {X : Subgroup G} {i z : G} (hi : i ∈ Subgroup.normalizer (X : Set G))
    (hz : z ∈ X ⊓ Subgroup.centralizer (X : Set G)) :
    i * z * i⁻¹ ∈ X ⊓ Subgroup.centralizer (X : Set G) := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hi z).mp hz.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro g hg
  have hg' : i⁻¹ * g * i ∈ X := by
    refine (Subgroup.mem_normalizer_iff.mp hi (i⁻¹ * g * i)).mpr ?_
    have : i * (i⁻¹ * g * i) * i⁻¹ = g := by group
    rw [this]
    exact hg
  have hc : (i⁻¹ * g * i) * z = z * (i⁻¹ * g * i) := Subgroup.mem_centralizer_iff.mp hz.2 _ hg'
  calc g * (i * z * i⁻¹) = i * ((i⁻¹ * g * i) * z) * i⁻¹ := by group
    _ = i * (z * (i⁻¹ * g * i)) * i⁻¹ := by rw [hc]
    _ = (i * z * i⁻¹) * g := by group

theorem commutator_mem_center {X : Subgroup G} {i y z : G} (hi : i ∈ Subgroup.normalizer (X : Set G))
    (hyX : y ∈ X) (hyi : y * i = i * y) (hz : z ∈ X ⊓ Subgroup.centralizer (X : Set G)) :
    ⁅y * z, i⁆ ∈ X ⊓ Subgroup.centralizer (X : Set G) := by
  have hc : y⁻¹ * i⁻¹ = i⁻¹ * y⁻¹ :=
    (Commute.inv_inv (show Commute y i from hyi)).eq
  have hw := conj_mem_center hi ((X ⊓ Subgroup.centralizer (X : Set G)).inv_mem hz)
  have hzw : z * (i * z⁻¹ * i⁻¹) ∈ X ⊓ Subgroup.centralizer (X : Set G) :=
    (X ⊓ Subgroup.centralizer (X : Set G)).mul_mem hz hw
  have key : ⁅y * z, i⁆ = y * (z * (i * z⁻¹ * i⁻¹)) * y⁻¹ := by
    rw [commutatorElement_def]
    calc y * z * i * (y * z)⁻¹ * i⁻¹ = y * z * i * (z⁻¹ * (y⁻¹ * i⁻¹)) := by group
      _ = y * z * i * (z⁻¹ * (i⁻¹ * y⁻¹)) := by rw [hc]
      _ = y * (z * (i * z⁻¹ * i⁻¹)) * y⁻¹ := by group
  have hy := Subgroup.mem_centralizer_iff.mp hzw.2 y hyX
  have hfin : y * (z * (i * z⁻¹ * i⁻¹)) * y⁻¹ = z * (i * z⁻¹ * i⁻¹) := by
    rw [hy, mul_inv_cancel_right]
  rw [key, hfin]
  exact hzw

theorem false_of_surjective_toCentralQuot {X Y : Subgroup G} {i : G}
    (hXq : CFSG.IsQuasisimple ↥X) (hi : i ∈ Subgroup.normalizer (X : Set G)) (hi2 : i * i = 1)
    (hcomm : ⁅X, Subgroup.zpowers i⁆ = X) (hYX : Y ≤ X)
    (hYi : Y ≤ Subgroup.centralizer ({i} : Set G))
    (hsurj : Function.Surjective (toCentralQuot hYX)) : False := by
  have hdec : ∀ x ∈ X, ⁅x, i⁆ ∈ X ⊓ Subgroup.centralizer (X : Set G) := by
    intro x hx
    obtain ⟨y, hy⟩ := hsurj (QuotientGroup.mk (⟨x, hx⟩ : ↥X))
    have hy' : ((Subgroup.inclusion hYX y : ↥X) : ↥X ⧸ Subgroup.center ↥X) =
        QuotientGroup.mk (⟨x, hx⟩ : ↥X) := by simpa [toCentralQuot] using hy
    have hz0 : (Subgroup.inclusion hYX y)⁻¹ * (⟨x, hx⟩ : ↥X) ∈ Subgroup.center ↥X :=
      QuotientGroup.eq.mp hy'
    have hzmem : (((Subgroup.inclusion hYX y)⁻¹ * (⟨x, hx⟩ : ↥X) : ↥X) : G) ∈
        X ⊓ Subgroup.centralizer (X : Set G) := by
      refine ⟨(((Subgroup.inclusion hYX y)⁻¹ * (⟨x, hx⟩ : ↥X) : ↥X)).2,
        Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz0 ⟨h, hh⟩)
    have hxy : x = (y : G) * (((Subgroup.inclusion hYX y)⁻¹ * (⟨x, hx⟩ : ↥X) : ↥X) : G) := by
      have := congrArg Subtype.val (mul_inv_cancel_left (Subgroup.inclusion hYX y) (⟨x, hx⟩ : ↥X))
      exact this.symm
    have hyi : (y : G) * i = i * y := Subgroup.mem_centralizer_singleton_iff.mp (hYi y.2)
    rw [hxy]
    exact commutator_mem_center hi (hYX y.2) hyi hzmem
  have hle : ⁅X, Subgroup.zpowers i⁆ ≤ X ⊓ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx g hg
    rcases mem_zpowers_involution hi2 hg with rfl | rfl
    · rw [commutatorElement_one_right]
      exact Subgroup.one_mem _
    · exact hdec x hx
  rw [hcomm] at hle
  obtain ⟨a, b, hab⟩ := hXq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have : (b' : ↥X) * a' = a' * b' := Subtype.ext ((Subgroup.mem_centralizer_iff.mp
    (hle a'.2).2 b' b'.2))
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]

omit [Group G] in
@[expose] def J2NoL34Component : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X Y : Subgroup G) (i : G), CFSG.IsQuasisimple ↥X →
    IsPGroup 2 (Subgroup.center ↥X) →
    Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.Carrier .J2) →
    i ∈ Subgroup.normalizer (X : Set G) → i * i = 1 → ⁅X, Subgroup.zpowers i⁆ = X →
    IsComponentIn Y (X ⊓ Subgroup.centralizer ({i} : Set G)) →
      ¬ StatedClassicalModel (↥Y ⧸ Subgroup.center ↥Y) .PSL 3 2 2

variable [Finite G]

theorem surjective_toCentralQuot_of_card_eq {X Y : Subgroup G} (hYX : Y ≤ X)
    (h : Nat.card (↥Y ⧸ Subgroup.center ↥Y) = Nat.card (↥X ⧸ Subgroup.center ↥X)) :
    Function.Surjective (toCentralQuot hYX) := by
  obtain ⟨h1, h2⟩ := card_center_quot_dvd hYX
  rw [h] at h1
  have hr : Nat.card (toCentralQuot hYX).range = Nat.card (↥X ⧸ Subgroup.center ↥X) :=
    Nat.dvd_antisymm h2 h1
  have : (toCentralQuot hYX).range = ⊤ := Subgroup.eq_top_of_card_eq _ hr
  exact MonoidHom.range_eq_top.mp this

theorem tabNonEmbed_no_comp_of_residual (hR : J2NoL34Component) :
    ∀ (G : Type) [Group G] [Finite G] (X Y : Subgroup G) (i : G), CFSG.IsQuasisimple ↥X →
    IsPGroup 2 (Subgroup.center ↥X) →
    (StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨
      Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.Carrier .J2)) →
    i ∈ Subgroup.normalizer (X : Set G) → i * i = 1 → ⁅X, Subgroup.zpowers i⁆ = X →
    IsComponentIn Y (X ⊓ Subgroup.centralizer ({i} : Set G)) →
      ¬ (StatedClassicalModel (↥Y ⧸ Subgroup.center ↥Y) .PSL 3 2 2 ∨
        Nonempty ((↥Y ⧸ Subgroup.center ↥Y) ≃* NativeSporadic.Carrier .J2)) := by
  intro G _ _ X Y i hXq hZ2 hM hi hi2 hcomm hY hYcase
  have hYX : Y ≤ X := hY.1.trans inf_le_left
  have hYi : Y ≤ Subgroup.centralizer ({i} : Set G) := hY.1.trans inf_le_right
  obtain ⟨h1, h2⟩ := card_center_quot_dvd hYX
  have hdvd := h1.trans h2
  have hcentral : Nat.card (↥Y ⧸ Subgroup.center ↥Y) = Nat.card (↥X ⧸ Subgroup.center ↥X) →
      False := fun h =>
    false_of_surjective_toCentralQuot hXq hi hi2 hcomm hYX hYi
      (surjective_toCentralQuot_of_card_eq hYX h)
  have hcY := card_of_psl_three_four_or_j2 hYcase
  rcases hM with hM4 | hMJ
  ·
    have hb : Nat.card (↥X ⧸ Subgroup.center ↥X) = 20160 := card_of_psl_three_four hM4
    rcases hcY with h | h
    · exact hcentral (h.trans hb.symm)
    · rw [h, hb] at hdvd
      omega
  ·
    rcases hYcase with hY4 | hYJ
    · exact hR G X Y i hXq hZ2 hMJ hi hi2 hcomm hY hY4
    · exact hcentral (by
        have e1 : Nat.card (↥Y ⧸ Subgroup.center ↥Y) = 604800 := by
          obtain ⟨e⟩ := hYJ
          rw [Nat.card_congr e.toEquiv]
          exact CFSG.Sporadic.J2.card_J2
        have e2 : Nat.card (↥X ⧸ Subgroup.center ↥X) = 604800 := by
          obtain ⟨e⟩ := hMJ
          rw [Nat.card_congr e.toEquiv]
          exact CFSG.Sporadic.J2.card_J2
        rw [e1, e2])

end Comp

theorem tabNonEmbed_of_residual
    (hR : J2NoL34Component) : TabNonEmbed where
  no_pair := tabNonEmbed_no_pair
  no_comp := tabNonEmbed_no_comp_of_residual hR

end CFSG.QuasithinUnique.Id2519
