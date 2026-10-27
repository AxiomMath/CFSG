module

public import CFSG.GH74.Generic.BProg.Vocab
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.Walter.J1Props.Facts
public import CFSG.Walter.Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS5

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open CFSG.Walter CFSG.Walter.J1Props CFSG.Open
open scoped commutatorElement

section Gen

variable {X : Type*} [Group X]

theorem mem_zpowers_of_two {u a : X} (hu : orderOf u = 2) (ha : a ∈ zpowers u) : a = 1 ∨ a = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have h2 : ((orderOf u : ℕ) : ℤ) = 2 := by rw [hu]; rfl
  have hk := zpow_mod_orderOf u k
  rw [h2] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left; rw [← hk, h0, zpow_zero]
  · right; rw [← hk, h1, zpow_one]

theorem mem_sup_of_commute {A B : Subgroup X}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {z : X} (hz : z ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, z = a * b := by
  have hA : A ≤ Subgroup.normalizer (B : Set X) := fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun b hb => (h a ha b hb).symm)
  have := Subgroup.coe_mul_of_left_le_normalizer_right A B hA
  rw [← SetLike.mem_coe, this] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_sup_zpowers_of_two {u : X} (hu2 : orderOf u = 2) {L : Subgroup X}
    (hLu : L ≤ centralizer ({u} : Set X)) {g : X} (hg : g ∈ zpowers u ⊔ L) :
    (∃ l ∈ L, g = l) ∨ ∃ l ∈ L, g = u * l := by
  have hcomm : ∀ a ∈ zpowers u, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hbu : b * u = u * b := Subgroup.mem_centralizer_singleton_iff.1 (hLu hb)
    exact ((Commute.zpow_left (show Commute u b from hbu.symm) k).eq)
  obtain ⟨a, ha, l, hl, rfl⟩ := mem_sup_of_commute hcomm hg
  rcases mem_zpowers_of_two hu2 ha with rfl | rfl
  · exact Or.inl ⟨l, hl, by simp⟩
  · exact Or.inr ⟨l, hl, rfl⟩

theorem commutator_mul_left_of_commute {a b c : X} (hab : Commute a b) (hac : Commute a c) :
    ⁅a * b, c⁆ = ⁅b, c⁆ := by
  have h1 : a * (b * c * b⁻¹) * a⁻¹ = b * c * b⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hab.mul_right hac).mul_right hab.inv_right
  calc ⁅a * b, c⁆ = (a * (b * c * b⁻¹) * a⁻¹) * c⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅b, c⁆ := by rw [h1]; simp only [commutatorElement_def]

theorem commutator_mul_right_of_commute {a b c : X} (hab : Commute a b) (hac : Commute a c) :
    ⁅c, a * b⁆ = ⁅c, b⁆ := by
  rw [← commutatorElement_inv, commutator_mul_left_of_commute hab hac, commutatorElement_inv]

theorem isPComponent_of_pPrimeCore_eq_bot {H : Type*} [Group H] (hO : pPrimeCore 2 H = ⊥)
    {L : Subgroup H} (hn : L.Normal) (hq : IsQuasisimple ↥L) : IsPComponent 2 L := by
  have hinj : Function.Injective (QuotientGroup.mk' (pPrimeCore 2 H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO]
  refine ⟨L.map (QuotientGroup.mk' (pPrimeCore 2 H)), ⟨?_, ?_⟩, hn.isSubnormal, rfl, ?_⟩
  · exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.equivMapOfInjective L _ hinj)).1 hq
  · exact (hn.map _ (QuotientGroup.mk'_surjective _)).isSubnormal
  · intro J hJ _ hmap
    exact (ne_of_lt hJ) (Subgroup.map_injective hinj hmap)

structure IsSplit (n : ℕ) (u : X) (L H : Subgroup X) : Prop where
  ord : orderOf u = 2
  le_cent : L ≤ centralizer ({u} : Set X)
  not_mem : u ∉ L
  eq_sup : H = zpowers u ⊔ L
  simple : IsSimpleGroup ↥L
  nonabelian : ∃ a b : ↥L, a * b ≠ b * a
  card : Nat.card ↥L = n
  even : 2 ∣ n

theorem IsSplit.of_equiv_alternating {u : X} {L H : Subgroup X} (hord : orderOf u = 2)
    (hle : L ≤ centralizer ({u} : Set X)) (hnm : u ∉ L) (heq : H = zpowers u ⊔ L)
    (e : ↥L ≃* alternatingGroup (Fin 5)) : IsSplit 60 u L H := by
  have hs : IsSimpleGroup ↥L := by
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact MulEquiv.isSimpleGroup e
  have hcard : Nat.card ↥L = 60 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  refine ⟨hord, hle, hnm, heq, hs, ?_, hcard, by norm_num⟩
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative ↥L := ⟨⟨fun a b => hcon a b⟩⟩
  have := IsSimpleGroup.prime_card (α := ↥L)
  rw [hcard] at this
  exact absurd this (by norm_num)

namespace IsSplit

variable {n : ℕ} {u : X} {L H : Subgroup X}

theorem quasisimple (h : IsSplit n u L H) : IsQuasisimple ↥L := by
  have := h.simple
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.nonabelian).1

theorem le_H (h : IsSplit n u L H) : L ≤ H := by
  rw [h.eq_sup]; exact le_sup_right

theorem commutator_mem (h : IsSplit n u L H) {g₁ g₂ : X} (h₁ : g₁ ∈ H) (h₂ : g₂ ∈ H) :
    ⁅g₁, g₂⁆ ∈ L := by
  rw [h.eq_sup] at h₁ h₂
  have hcu : ∀ l ∈ L, Commute u l := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.1 (h.le_cent hl)).symm
  have hLL : ∀ l₁ ∈ L, ∀ l₂ ∈ L, ⁅l₁, l₂⁆ ∈ L := fun l₁ hl₁ l₂ hl₂ => by
    simp only [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hl₁ hl₂) (L.inv_mem hl₁)) (L.inv_mem hl₂)
  rcases mem_sup_zpowers_of_two h.ord h.le_cent h₁ with ⟨l₁, hl₁, hg₁⟩ | ⟨l₁, hl₁, hg₁⟩ <;>
  rcases mem_sup_zpowers_of_two h.ord h.le_cent h₂ with ⟨l₂, hl₂, hg₂⟩ | ⟨l₂, hl₂, hg₂⟩ <;>
  rw [hg₁, hg₂]
  · exact hLL _ hl₁ _ hl₂
  · rw [commutator_mul_right_of_commute (hcu l₂ hl₂) (hcu l₁ hl₁)]
    exact hLL _ hl₁ _ hl₂
  · rw [commutator_mul_left_of_commute (hcu l₁ hl₁) (hcu l₂ hl₂)]
    exact hLL _ hl₁ _ hl₂
  · rw [commutator_mul_left_of_commute (hcu l₁ hl₁) ((Commute.refl u).mul_right (hcu l₂ hl₂)),
      commutator_mul_right_of_commute (hcu l₂ hl₂) (hcu l₁ hl₁)]
    exact hLL _ hl₁ _ hl₂

theorem le_of_perfect' (h : IsSplit n u L H) {P : Subgroup X} (hPH : P ≤ H) (hP : ⁅P, P⁆ = P) :
    P ≤ L := by
  rw [← hP, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  exact h.commutator_mem (hPH hg₁) (hPH hg₂)

theorem le_of_perfect (h : IsSplit n u L H) {P : Subgroup ↥H} (hP : Group.IsPerfect ↥P) :
    P ≤ L.subgroupOf H := by
  have h1 : ⁅P, P⁆ ≤ L.subgroupOf H := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [Subgroup.mem_subgroupOf]
    exact h.commutator_mem g₁.2 g₂.2
  rwa [Subgroup.commutator_eq_self] at h1

variable [Finite X]

theorem card_le_of_isPCompIn (h : IsSplit n u L H) {L' : Subgroup X} (hL' : IsPCompIn 2 H L') :
    Nat.card ↥L' ≤ Nat.card ↥L := by
  have hperf : Group.IsPerfect ↥(L'.subgroupOf H) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hL'.2
  have h1 := h.le_of_perfect hperf
  have h2 : L' ≤ L := fun g hg =>
    Subgroup.mem_subgroupOf.1
      (h1 (Subgroup.mem_subgroupOf.2 hg : (⟨g, hL'.1 hg⟩ : ↥H) ∈ L'.subgroupOf H))
  exact Subgroup.card_le_of_le h2

theorem pPrimeCore_eq_bot (h : IsSplit n u L H) : pPrimeCore 2 ↥H = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLH : L ≤ H := h.le_H
  set N : Subgroup ↥H := pPrimeCore 2 ↥H with hN
  have hNodd : ∀ n ∈ N, Odd (orderOf n) := by
    intro n hn
    have hdvd : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
    have hcop : Nat.Coprime 2 (Nat.card N) := CFSG.pPrimeCore_coprime_card
    exact Nat.coprime_two_left.1 (hcop.coprime_dvd_right hdvd)
  have step1 : ∀ n ∈ N, (n : X) ∈ L := by
    intro n hn
    have hodd := hNodd n hn
    have hnH : (n : X) ∈ zpowers u ⊔ L := h.eq_sup ▸ n.2
    rcases mem_sup_zpowers_of_two h.ord h.le_cent hnH with ⟨l, hl, hnl⟩ | ⟨l, hl, hnl⟩
    · rw [hnl]; exact hl
    · exfalso
      obtain ⟨k, hk⟩ := hodd
      have hcu : Commute u l := (Subgroup.mem_centralizer_singleton_iff.1 (h.le_cent hl)).symm
      have hu2 : u ^ 2 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one u
      have h1 : (n : X) ^ (2 * k + 1) = 1 := by
        rw [← hk, ← Subgroup.orderOf_coe]; exact pow_orderOf_eq_one _
      rw [hnl, hcu.mul_pow, pow_succ u, pow_mul, hu2, one_pow, one_mul] at h1
      apply h.not_mem
      have : u = (l ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact L.inv_mem (L.pow_mem hl _)
  set ι : ↥L →* ↥H := Subgroup.inclusion hLH with hι
  have hN₁ : (N.comap ι).Normal := Subgroup.Normal.comap inferInstance ι
  have := h.simple
  have := hN₁
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap ι) with hb | ht
  · rw [eq_bot_iff]
    intro n hn
    have : (⟨(n : X), step1 n hn⟩ : ↥L) ∈ N.comap ι := hn
    rw [hb, Subgroup.mem_bot] at this
    have h2 : ι ⟨(n : X), step1 n hn⟩ = 1 := by rw [this, map_one]
    have : n = ι ⟨(n : X), step1 n hn⟩ := rfl
    rw [this, h2]
    exact Subgroup.one_mem _
  · exfalso
    have h2L : 2 ∣ Nat.card ↥L := by rw [h.card]; exact h.even
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 h2L
    have hxN : ι x ∈ N := by
      have : x ∈ N.comap ι := by rw [ht]; trivial
      exact this
    have hodd := hNodd _ hxN
    rw [orderOf_injective ι (Subgroup.inclusion_injective hLH) x, hx] at hodd
    exact absurd hodd (by decide)

theorem isPCompIn (h : IsSplit n u L H) : IsPCompIn 2 H L := by
  refine ⟨h.le_H, ?_⟩
  have hnorm : (L.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer h.le_H, h.eq_sup]
    exact sup_le (Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun l hl =>
        Subgroup.mem_centralizer_singleton_iff.1 (h.le_cent hl)))) Subgroup.le_normalizer
  exact isPComponent_of_pPrimeCore_eq_bot h.pPrimeCore_eq_bot hnorm
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.le_H).symm
      h.quasisimple)

theorem isPCompIn_self (h : IsSplit n u L H) : IsPCompIn 2 L L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_rfl, ?_⟩
  rw [Subgroup.subgroupOf_self]
  have hO : pPrimeCore 2 ↥L = ⊥ := by
    have := h.simple
    have hn : (pPrimeCore 2 ↥L).Normal := CFSG.pPrimeCore_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥L) with hb | ht
    · exact hb
    · exfalso
      have hc : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥L)) := CFSG.pPrimeCore_coprime_card
      rw [ht, Subgroup.card_top, h.card] at hc
      have := hc.eq_one_of_dvd h.even
      omega
  refine isPComponent_of_pPrimeCore_eq_bot hO inferInstance ?_
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h.quasisimple

theorem pLayerOf_ne_bot (h : IsSplit n u L H) : pLayerOf 2 H ≠ ⊥ := by
  intro hbot
  have h1 : L ≤ pLayerOf 2 H := le_sSup h.isPCompIn
  rw [hbot, le_bot_iff] at h1
  have : Nat.card ↥L = 1 := by rw [h1]; exact Subgroup.card_bot
  rw [h.card] at this
  have h2 := h.even
  omega

end IsSplit

end Gen

section J1

theorem isElementaryAbelian_two_of_isKleinFour {G : Type*} [Group G] [hK : IsKleinFour G] :
    CFSG.IsElementaryAbelian 2 G :=
  { toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by rw [hK.exponent_two] }

theorem walterJ1_exists_four :
    ∃ V : Subgroup walterJ1, CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  obtain ⟨h1, h2, -, h4, -⟩ := rels_F
  obtain ⟨n1, n2, n3, -⟩ := ne_one_F
  have hK := CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions xJ x'J h1 h2 n1 n2
    n3 h4
  exact ⟨_, isElementaryAbelian_two_of_isKleinFour (hK := hK), hK.card_four⟩

theorem walterJ1_center :
    ∀ z : walterJ1, (∀ g : walterJ1, g * z = z * g) → z = 1 := by
  intro z hz
  have hs : IsSimpleGroup walterJ1 := J1_simple
  have hZ : Subgroup.center walterJ1 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center walterJ1) with h | h
    · exact h
    · exfalso
      have h1 : Subgroup.centralizer ({tJ} : Set walterJ1) = ⊤ := by
        rw [eq_top_iff]
        intro g _
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.1 (by rw [h]; exact Subgroup.mem_top g) tJ).symm
      have h2 := card_centralizer_of_orderOf_eq_two (x := tJ) orderOf_tJ
      rw [h1, Subgroup.card_top, J1_card] at h2
      omega
  have : z ∈ Subgroup.center walterJ1 := Subgroup.mem_center_iff.2 fun g => (hz g)
  rwa [hZ, Subgroup.mem_bot] at this

theorem walterJ1_split (u : walterJ1) (hu : orderOf u = 2) :
    ∃ L : Subgroup walterJ1, L ≤ Subgroup.centralizer ({u} : Set walterJ1) ∧ u ∉ L ∧
      Subgroup.centralizer ({u} : Set walterJ1) = Subgroup.zpowers u ⊔ L ∧
      Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨g, hg⟩ := jankoHyp.exists_conj_eq_t hu
  set h := jankoHyp.conj g⁻¹ with hh
  have ht : h.t = u := by
    rw [hh, CFSG.Walter.J1.JankoHyp.conj_t, ← hg]
    group
  refine ⟨h.F, ?_, ?_, ?_, ⟨h.iso⟩⟩
  · rw [← ht]; exact h.le_centralizer
  · rw [← ht]; exact h.t_not_mem
  · rw [← ht]; exact h.centralizer_eq

theorem exists_four_of_equiv {J : Type*} [Group J] (e : J ≃* walterJ1) :
    ∃ V : Subgroup J, CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  obtain ⟨V', hV', hc⟩ := walterJ1_exists_four
  refine ⟨V'.map e.symm.toMonoidHom, ?_, ?_⟩
  · have := hV'
    exact CFSG.IsElementaryAbelian.map e.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.symm.injective, hc]

theorem exists_four_of_isSporadic {J : Type} [Group J] (h : NativeSporadic.IsSporadic J .J1) :
    ∃ V : Subgroup J, CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  obtain ⟨e⟩ := h
  exact exists_four_of_equiv (e.trans walterJ1EquivNative.symm)

theorem center_of_equiv {J : Type*} [Group J] (e : J ≃* walterJ1) :
    ∀ z : J, (∀ g : J, g * z = z * g) → z = 1 := by
  intro z hz
  apply e.injective
  rw [map_one]
  apply walterJ1_center
  intro g
  have := congrArg e (hz (e.symm g))
  simpa using this

theorem center_of_isSporadic {J : Type} [Group J]
    (h : NativeSporadic.IsSporadic J .J1) : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1 := by
  obtain ⟨e⟩ := h
  exact center_of_equiv (e.trans walterJ1EquivNative.symm)

end J1

section SplitLike

variable {X : Type} [Group X]

structure SplitLike (n : ℕ) (Y : Subgroup X) : Prop where
  center : ∀ z ∈ Y, (∀ g ∈ Y, g * z = z * g) → z = 1
  split : ∀ u ∈ Y, orderOf u = 2 →
    ∃ L : Subgroup X, L ≤ Y ∧ IsSplit n u L (centralizer ({u} : Set X) ⊓ Y)

theorem SplitLike.of_equiv {Y : Subgroup X} (e : ↥Y ≃* walterJ1) :
    SplitLike 60 Y := by
  refine ⟨fun z hz hcomm => ?_, fun u hu hu2 => ?_⟩
  · have := center_of_equiv e ⟨z, hz⟩ (fun g => Subtype.ext (hcomm g g.2))
    exact congrArg Subtype.val this
  · set u₀ : ↥Y := ⟨u, hu⟩ with hu₀
    have hu₀2 : orderOf (e u₀) = 2 := by
      rw [MulEquiv.orderOf_eq, hu₀, Subgroup.orderOf_mk]; exact hu2
    obtain ⟨L', hL1, hL2, hL3, hL4⟩ := walterJ1_split (e u₀) hu₀2
    set L'' : Subgroup ↥Y := L'.map e.symm.toMonoidHom with hL''
    set L : Subgroup X := L''.map Y.subtype with hL
    have hLY : L ≤ Y := Subgroup.map_subtype_le _
    have hLmem : ∀ l ∈ L, ∃ l' ∈ L', ((e.symm l' : ↥Y) : X) = l := by
      rintro _ ⟨a, ⟨l', hl', rfl⟩, rfl⟩
      exact ⟨l', hl', rfl⟩
    have hLc : L ≤ centralizer ({u} : Set X) := by
      intro l hl
      obtain ⟨l', hl', rfl⟩ := hLmem l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hL1 hl')
      have h2 := congrArg e.symm h1
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h2
      exact congrArg Subtype.val h2
    have hLn : u ∉ L := by
      intro huL
      obtain ⟨l', hl', hl'u⟩ := hLmem u huL
      apply hL2
      have : e.symm l' = u₀ := Subtype.ext hl'u
      have h3 : l' = e u₀ := by rw [← this]; simp
      rwa [← h3]
    obtain ⟨e₂⟩ := hL4
    refine ⟨L, hLY, IsSplit.of_equiv_alternating hu2 hLc hLn ?_
      (((Subgroup.equivMapOfInjective L'' Y.subtype Y.subtype_injective).symm.trans
        ((e.symm.subgroupMap L').symm)).trans e₂)⟩
    · apply le_antisymm
      · intro g hg
        have hgY : g ∈ Y := hg.2
        have hgc : (⟨g, hgY⟩ : ↥Y) * u₀ = u₀ * ⟨g, hgY⟩ :=
          Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hg.1)
        have h1 : e ⟨g, hgY⟩ ∈ Subgroup.centralizer ({e u₀} : Set walterJ1) := by
          rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hgc]
        rw [hL3] at h1
        have h2 : (⟨g, hgY⟩ : ↥Y) ∈ (zpowers (e u₀) ⊔ L').map e.symm.toMonoidHom :=
          ⟨_, h1, by simp⟩
        rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h2
        have h3 : g ∈ (zpowers (e.symm.toMonoidHom (e u₀)) ⊔ L'').map Y.subtype :=
          ⟨_, h2, rfl⟩
        rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h3
        simpa using h3
      · refine sup_le ?_ (le_inf hLc hLY)
        exact Subgroup.zpowers_le.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, hu⟩

end SplitLike

section SplitLikeConsequences

variable {X : Type} [Group X] [Finite X] {n : ℕ} {Y : Subgroup X} (hY : SplitLike n Y)
include hY

theorem SplitLike.isPCompIn_of_le_centralizer {u d : X} {L : Subgroup X} (hdY : d ∈ Y)
    (hd2 : orderOf d = 2) (hLY : L ≤ Y) (hL : IsSplit n u L (centralizer ({u} : Set X) ⊓ Y))
    (hLd : L ≤ centralizer ({d} : Set X)) :
    IsPCompIn 2 (centralizer ({d} : Set X) ⊓ Y) L := by
  obtain ⟨Ld, hLdY, hsp⟩ := hY.split d hdY hd2
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hL.quasisimple.1
  have hle : L ≤ Ld := hsp.le_of_perfect' (le_inf hLd hLY) hperf
  have heq : L = Ld := Subgroup.eq_of_le_of_card_ge hle (by rw [hL.card, hsp.card])
  rw [heq]
  exact hsp.isPCompIn

theorem SplitLike.subtermRel {u : X} {L : Subgroup X} (hu : u ∈ Y) (hLY : L ≤ Y)
    (hL : IsSplit n u L (centralizer ({u} : Set X) ⊓ Y)) : SubtermRel Y u L := by
  refine ⟨hL.ord, Subgroup.le_normalizer hu, Or.inl ⟨hL.isPCompIn, ?_⟩⟩
  intro z hz hz2
  have hYu : Y ⊔ zpowers u = Y := sup_eq_left.2 (Subgroup.zpowers_le.2 hu)
  rw [hYu] at hz
  have hcomm : ∀ a ∈ centralizer (L : Set X) ⊓ Y, ∀ b ∈ centralizer (Y : Set X), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb a ha.2
  obtain ⟨d, hd, w, hw, rfl⟩ := mem_sup_of_commute hcomm hz
  have hdY : d ∈ Y := hd.2
  have hdw : Commute d w := hcomm d hd w hw
  have hwY : ∀ g ∈ Y, Commute g w := fun g hg => Subgroup.mem_centralizer_iff.1 hw g hg
  have hd2sq : d ^ 2 = 1 := by
    have h1 : (d * w) ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one _
    rw [hdw.mul_pow] at h1
    have h3 : d ^ 2 = (w ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
    apply hY.center (d ^ 2) (Subgroup.pow_mem Y hdY 2)
    intro g hg
    rw [h3]
    exact ((hwY g hg).pow_right 2).inv_right.eq
  by_cases hd1 : d = 1
  · right
    rw [hd1, one_mul]
    exact hw
  · left
    have hd2 : orderOf d = 2 := orderOf_eq_prime hd2sq hd1
    have hLd : L ≤ centralizer ({d} : Set X) := fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hd.1 l hl)
    have hcent : centralizer ({d * w} : Set X) ⊓ Y = centralizer ({d} : Set X) ⊓ Y := by
      ext g
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨h1, hg⟩
        refine ⟨?_, hg⟩
        have h2 : g * d * w = d * g * w := by
          calc g * d * w = g * (d * w) := by rw [mul_assoc]
            _ = d * w * g := h1
            _ = d * (w * g) := by rw [mul_assoc]
            _ = d * (g * w) := by rw [(hwY g hg).eq]
            _ = d * g * w := by rw [mul_assoc]
        exact mul_right_cancel h2
      · rintro ⟨h1, hg⟩
        refine ⟨?_, hg⟩
        calc g * (d * w) = g * d * w := by rw [mul_assoc]
          _ = d * g * w := by rw [h1]
          _ = d * (g * w) := by rw [mul_assoc]
          _ = d * (w * g) := by rw [(hwY g hg).eq]
          _ = d * w * g := by rw [mul_assoc]
    rw [hcent]
    exact hY.isPCompIn_of_le_centralizer hdY hd2 hLY hL hLd

theorem SplitLike.exists_pair {u : X} (hu : u ∈ Y) (hu2 : orderOf u = 2) :
    ∃ L : Subgroup X, L ≤ Y ∧ IsSplit n u L (centralizer ({u} : Set X) ⊓ Y) ∧ SubtermRel Y u L := by
  obtain ⟨L, hLY, hL⟩ := hY.split u hu hu2
  exact ⟨L, hLY, hL, hY.subtermRel hu hLY hL⟩

end SplitLikeConsequences


end CFSG.GH74.Generic.BProg.B1.PilotS5
