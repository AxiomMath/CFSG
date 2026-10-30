module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.Quasithin.Background.F918V5GComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open
open scoped commutatorElement

variable {H : Type*} [Group H]

private theorem l94c_le_normalizer_of_comm {A S : Subgroup H}
    (h : ∀ a ∈ A, ∀ y ∈ S, y * a = a * y) : S ≤ Subgroup.normalizer (A : Set H) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have e : y * g * y⁻¹ = g := by
      have hyg := h g hg y hy
      calc y * g * y⁻¹ = g * y * y⁻¹ := by rw [hyg]
        _ = g := by group
    rw [e]
    exact hg
  · intro hg
    have hc := h (y * g * y⁻¹) hg y hy
    have e : y * g * y⁻¹ = g := by
      calc y * g * y⁻¹ = y⁻¹ * (y * (y * g * y⁻¹)) := by group
        _ = y⁻¹ * (y * g * y⁻¹ * y) := by rw [hc]
        _ = g := by group
    rw [e] at hg
    exact hg

private theorem l94c_mem_sup_mul {B C : Subgroup H}
    (hB : B ≤ Subgroup.normalizer (C : Set H)) {x : H} (hx : x ∈ B ⊔ C) :
    ∃ b ∈ B, ∃ c ∈ C, x = b * c := by
  let M : Subgroup H :=
    { carrier := {x | ∃ b ∈ B, ∃ c ∈ C, x = b * c}
      mul_mem' := by
        rintro _ _ ⟨b₁, hb₁, c₁, hc₁, rfl⟩ ⟨b₂, hb₂, c₂, hc₂, rfl⟩
        have hc : b₂⁻¹ * c₁ * b₂ ∈ C := by
          refine (Subgroup.mem_normalizer_iff.1 (hB hb₂) (b₂⁻¹ * c₁ * b₂)).2 ?_
          have e : b₂ * (b₂⁻¹ * c₁ * b₂) * b₂⁻¹ = c₁ := by group
          rw [e]
          exact hc₁
        exact ⟨b₁ * b₂, mul_mem hb₁ hb₂, (b₂⁻¹ * c₁ * b₂) * c₂, mul_mem hc hc₂, by group⟩
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨b, hb, c, hc, rfl⟩
        have hc' : b * c⁻¹ * b⁻¹ ∈ C :=
          (Subgroup.mem_normalizer_iff.1 (hB hb) (c⁻¹)).1 (inv_mem hc)
        exact ⟨b⁻¹, inv_mem hb, b * c⁻¹ * b⁻¹, hc', by group⟩ }
  have hsup : B ⊔ C ≤ M :=
    sup_le (fun b hb => ⟨b, hb, 1, one_mem _, (mul_one b).symm⟩)
      (fun c hc => ⟨1, one_mem _, c, hc, (one_mul c).symm⟩)
  exact hsup hx

private theorem l94c_normalizer_sup {P A B : Subgroup H}
    (hA : P ≤ Subgroup.normalizer (A : Set H)) (hB : P ≤ Subgroup.normalizer (B : Set H)) :
    P ≤ Subgroup.normalizer ((A ⊔ B : Subgroup H) : Set H) := by
  intro g hg
  have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hA hg)
  have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hB hg)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, h1, h2]

private theorem l94c_normalizer_inf {P A B : Subgroup H}
    (hA : P ≤ Subgroup.normalizer (A : Set H)) (hB : P ≤ Subgroup.normalizer (B : Set H)) :
    P ≤ Subgroup.normalizer ((A ⊓ B : Subgroup H) : Set H) := by
  intro g hg
  have hA' := Subgroup.mem_normalizer_iff.1 (hA hg)
  have hB' := Subgroup.mem_normalizer_iff.1 (hB hg)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA' h, hB' h]

private theorem l94c_conj_mem_centralizer {K : Subgroup H} {s : H}
    (hs : s ∈ Subgroup.normalizer (K : Set H)) {c : H}
    (hc : c ∈ Subgroup.centralizer (K : Set H)) :
    s * c * s⁻¹ ∈ Subgroup.centralizer (K : Set H) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro h hh
  have hh' : s⁻¹ * h * s ∈ K := by
    refine (Subgroup.mem_normalizer_iff.1 hs (s⁻¹ * h * s)).2 ?_
    have e : s * (s⁻¹ * h * s) * s⁻¹ = h := by group
    rw [e]
    exact hh
  calc h * (s * c * s⁻¹) = s * ((s⁻¹ * h * s) * c) * s⁻¹ := by group
    _ = s * (c * (s⁻¹ * h * s)) * s⁻¹ := by rw [hc _ hh']
    _ = s * c * s⁻¹ * h := by group

private theorem l94c_mem_normalizer_centralizer {K : Subgroup H} {t : H}
    (ht : t ∈ Subgroup.normalizer (K : Set H)) :
    t ∈ Subgroup.normalizer ((Subgroup.centralizer (K : Set H) : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact l94c_conj_mem_centralizer ht hc
  · intro hc
    have h := l94c_conj_mem_centralizer (inv_mem ht) hc
    have e : t⁻¹ * (t * c * t⁻¹) * t⁻¹⁻¹ = c := by group
    rwa [e] at h

private theorem l94c_card_eq [Finite H] {K₁ K₂ B : Subgroup H}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinf : K₁ ⊓ K₂ = ⊥)
    (hB : B ≤ K₁ ⊔ K₂) (hBn : B ≤ Subgroup.normalizer (K₂ : Set H)) :
    Nat.card B = Nat.card (K₁ ⊓ (B ⊔ K₂) : Subgroup H) * Nat.card (B ⊓ K₂ : Subgroup H) := by
  have hK₁N : K₁ ≤ Subgroup.normalizer (K₂ : Set H) :=
    l94c_le_normalizer_of_comm (fun a ha y hy => (hcomm y hy a ha))
  have h1 : Nat.card (B ⊔ K₂ : Subgroup H) * Nat.card (B ⊓ K₂ : Subgroup H)
      = Nat.card B * Nat.card K₂ := by
    have := card_sup_mul_card_inf_of_le_normalizer hBn
    rw [sup_comm, inf_comm] at this
    rw [this, mul_comm]
  set S : Subgroup H := B ⊔ K₂ with hS
  set A₁ : Subgroup H := K₁ ⊓ S with hA₁
  have hA₁S : A₁ ⊔ K₂ = S := by
    apply le_antisymm
    · exact sup_le inf_le_right le_sup_right
    · refine sup_le ?_ le_sup_right
      intro b hb
      obtain ⟨k, hk, c, hc, hbkc⟩ := l94c_mem_sup_mul hK₁N (hB hb)
      have hkS : k ∈ S := by
        have e : k = b * c⁻¹ := by rw [hbkc]; group
        rw [e]
        exact mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right (inv_mem hc))
      rw [hbkc]
      exact mul_mem (Subgroup.mem_sup_left (show k ∈ A₁ from ⟨hk, hkS⟩)) (Subgroup.mem_sup_right hc)
  have hK₂N : K₂ ≤ Subgroup.normalizer (A₁ : Set H) :=
    l94c_le_normalizer_of_comm (fun a ha y hy => (hcomm a ((show A₁ ≤ K₁ from inf_le_left) ha) y hy).symm)
  have hinf2 : A₁ ⊓ K₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz1 : z ∈ K₁ ⊓ K₂ := ⟨(show A₁ ≤ K₁ from inf_le_left) hz.1, hz.2⟩
    rw [hinf] at hz1
    exact hz1
  have h2 : Nat.card (A₁ ⊔ K₂ : Subgroup H) * Nat.card (A₁ ⊓ K₂ : Subgroup H)
      = Nat.card A₁ * Nat.card K₂ := card_sup_mul_card_inf_of_le_normalizer hK₂N
  rw [hinf2, Subgroup.card_bot, mul_one, hA₁S] at h2
  have hK₂pos : 0 < Nat.card K₂ := Nat.card_pos
  rw [h2] at h1
  have h3 : (Nat.card A₁ * Nat.card (B ⊓ K₂ : Subgroup H)) * Nat.card K₂
      = Nat.card B * Nat.card K₂ := by
    rw [← h1]
    ring
  exact (Nat.eq_of_mul_eq_mul_right hK₂pos h3).symm

private theorem l94c_center_trivial {K : Subgroup H} (hKs : IsSimpleGroup K)
    {y : H} (hyK : y ∈ K) (hy3 : orderOf y = 3) {W : Subgroup H} (hWK : W ≤ K)
    (hW2 : IsPGroup 2 W) (hW : W ≠ ⊥) :
    ∀ k ∈ K, (∀ g ∈ K, g * k = k * g) → k = 1 := by
  have hZ : Subgroup.center K ≠ ⊤ := by
    intro hZtop
    have hcomm : ∀ a b : K, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.center K := by
        rw [hZtop]
        exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.1 ha) b).symm
    haveI hWn : (W.subgroupOf K).Normal :=
      ⟨fun n hn g => by
        have e : g * n * g⁻¹ = n := by
          rw [hcomm g n]
          group
        rw [e]
        exact hn⟩
    rcases hKs.eq_bot_or_eq_top_of_normal (W.subgroupOf K) with h | h
    · apply hW
      rw [eq_bot_iff]
      intro w hw
      have hwK : (⟨w, hWK hw⟩ : K) ∈ W.subgroupOf K := Subgroup.mem_subgroupOf.2 hw
      rw [h, Subgroup.mem_bot] at hwK
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hwK)
    · have hyW : y ∈ W := by
        have hyWK : (⟨y, hyK⟩ : K) ∈ W.subgroupOf K := by
          rw [h]
          exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.1 hyWK
      obtain ⟨n, hn⟩ := hW2 ⟨y, hyW⟩
      have hpow : y ^ 2 ^ n = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      have hdvd : 3 ∣ 2 ^ n := by
        have := orderOf_dvd_of_pow_eq_one hpow
        rwa [hy3] at this
      have h23 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      norm_num at h23
  have hZbot : Subgroup.center K = ⊥ := by
    rcases hKs.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exact h
    · exact absurd h hZ
  intro k hk hcomm'
  have hmem : (⟨k, hk⟩ : K) ∈ Subgroup.center K := by
    refine Subgroup.mem_center_iff.2 (fun g => Subtype.ext ?_)
    simp only [Subgroup.coe_mul]
    exact hcomm' g g.2
  rw [hZbot, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

private theorem l94c_comm_of_elemAbelian {S : Subgroup H} (hS : IsElemAbelian 3 S) {a b : H}
    (ha : a ∈ S) (hb : b ∈ S) : a * b = b * a := by
  have h := hS.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val h

private theorem l94c_isElemAbelian_sup {S T : Subgroup H} (hS : IsElemAbelian 3 S)
    (hT : IsElemAbelian 3 T) (hST : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    IsElemAbelian 3 (S ⊔ T) := by
  have hSN : S ≤ Subgroup.normalizer (T : Set H) :=
    l94c_le_normalizer_of_comm (fun a ha y hy => hST y hy a ha)
  have hcomm : ∀ x ∈ S ⊔ T, ∀ y ∈ S ⊔ T, x * y = y * x := by
    intro x hx y hy
    obtain ⟨s, hs, t, ht, rfl⟩ := l94c_mem_sup_mul hSN hx
    obtain ⟨s', hs', t', ht', rfl⟩ := l94c_mem_sup_mul hSN hy
    have e1 : t * s' = s' * t := (hST s' hs' t ht).symm
    have e2 : t' * s = s * t' := (hST s hs t' ht').symm
    have c1 : s * t * (s' * t') = (s * s') * (t * t') := by
      calc s * t * (s' * t') = s * (t * s') * t' := by group
        _ = s * (s' * t) * t' := by rw [e1]
        _ = (s * s') * (t * t') := by group
    have c2 : s' * t' * (s * t) = (s' * s) * (t' * t) := by
      calc s' * t' * (s * t) = s' * (t' * s) * t := by group
        _ = s' * (s * t') * t := by rw [e2]
        _ = (s' * s) * (t' * t) := by group
    rw [c1, c2, l94c_comm_of_elemAbelian hS hs hs', l94c_comm_of_elemAbelian hT ht ht']
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, ?_⟩
  intro x hx
  obtain ⟨s, hs, t, ht, rfl⟩ := l94c_mem_sup_mul hSN hx
  have hc : Commute s t := hST s hs t ht
  rw [hc.mul_pow, hS.2 s hs, hT.2 t ht, one_mul]

private theorem l94c_isElemAbelian_zpowers {g : H} (hg : g ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers g) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · simp only [Subgroup.coe_mul]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
    rw [← hm, ← hn]
    exact ((Commute.refl g).zpow_zpow m n).eq
  · intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← hm]
    have h1 : (g ^ m) ^ (3:ℕ) = (g ^ (3:ℕ)) ^ m := by
      rw [← zpow_natCast, ← zpow_natCast g, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [h1, hg, one_zpow]

private theorem l94c_isElemAbelian_proj {K₁ K₂ B : Subgroup H}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinf : K₁ ⊓ K₂ = ⊥)
    (hB : IsElemAbelian 3 B) (hBn : B ≤ Subgroup.normalizer (K₂ : Set H)) :
    IsElemAbelian 3 (K₁ ⊓ (B ⊔ K₂)) := by
  have hdec : ∀ a ∈ K₁ ⊓ (B ⊔ K₂), ∃ c ∈ K₂, a * c⁻¹ ∈ B := by
    intro a ha
    obtain ⟨b, hb, c, hc, habc⟩ := l94c_mem_sup_mul hBn (Subgroup.mem_inf.1 ha).2
    refine ⟨c, hc, ?_⟩
    have e : a * c⁻¹ = b := by
      rw [habc]
      group
    rw [e]
    exact hb
  have hcommA : ∀ a₁ ∈ K₁ ⊓ (B ⊔ K₂), ∀ a₂ ∈ K₁ ⊓ (B ⊔ K₂), a₁ * a₂ = a₂ * a₁ := by
    intro a₁ ha₁ a₂ ha₂
    have ha₁' : a₁ ∈ K₁ := (Subgroup.mem_inf.1 ha₁).1
    have ha₂' : a₂ ∈ K₁ := (Subgroup.mem_inf.1 ha₂).1
    obtain ⟨c₁, hc₁, hb₁⟩ := hdec a₁ ha₁
    obtain ⟨c₂, hc₂, hb₂⟩ := hdec a₂ ha₂
    have hk₁ : c₁⁻¹ ∈ K₂ := inv_mem hc₁
    have hk₂ : c₂⁻¹ ∈ K₂ := inv_mem hc₂
    have hBc : (a₁ * c₁⁻¹) * (a₂ * c₂⁻¹) = (a₂ * c₂⁻¹) * (a₁ * c₁⁻¹) :=
      l94c_comm_of_elemAbelian hB hb₁ hb₂
    have c1 : c₁⁻¹ * a₂ = a₂ * c₁⁻¹ := (hcomm a₂ ha₂' c₁⁻¹ hk₁).symm
    have c2 : c₂⁻¹ * a₁ = a₁ * c₂⁻¹ := (hcomm a₁ ha₁' c₂⁻¹ hk₂).symm
    have L : (a₁ * c₁⁻¹) * (a₂ * c₂⁻¹) = (a₁ * a₂) * (c₁⁻¹ * c₂⁻¹) := by
      calc (a₁ * c₁⁻¹) * (a₂ * c₂⁻¹) = a₁ * (c₁⁻¹ * a₂) * c₂⁻¹ := by group
        _ = a₁ * (a₂ * c₁⁻¹) * c₂⁻¹ := by rw [c1]
        _ = (a₁ * a₂) * (c₁⁻¹ * c₂⁻¹) := by group
    have R : (a₂ * c₂⁻¹) * (a₁ * c₁⁻¹) = (a₂ * a₁) * (c₂⁻¹ * c₁⁻¹) := by
      calc (a₂ * c₂⁻¹) * (a₁ * c₁⁻¹) = a₂ * (c₂⁻¹ * a₁) * c₁⁻¹ := by group
        _ = a₂ * (a₁ * c₂⁻¹) * c₁⁻¹ := by rw [c2]
        _ = (a₂ * a₁) * (c₂⁻¹ * c₁⁻¹) := by group
    have E : (a₁ * a₂) * (c₁⁻¹ * c₂⁻¹) = (a₂ * a₁) * (c₂⁻¹ * c₁⁻¹) := by
      rw [← L, ← R]
      exact hBc
    have hz : (a₂ * a₁)⁻¹ * (a₁ * a₂) = (c₂⁻¹ * c₁⁻¹) * (c₁⁻¹ * c₂⁻¹)⁻¹ := by
      calc (a₂ * a₁)⁻¹ * (a₁ * a₂)
          = (a₂ * a₁)⁻¹ * ((a₁ * a₂) * (c₁⁻¹ * c₂⁻¹)) * (c₁⁻¹ * c₂⁻¹)⁻¹ := by group
        _ = (a₂ * a₁)⁻¹ * ((a₂ * a₁) * (c₂⁻¹ * c₁⁻¹)) * (c₁⁻¹ * c₂⁻¹)⁻¹ := by rw [E]
        _ = (c₂⁻¹ * c₁⁻¹) * (c₁⁻¹ * c₂⁻¹)⁻¹ := by group
    have hzK₁ : (a₂ * a₁)⁻¹ * (a₁ * a₂) ∈ K₁ :=
      mul_mem (inv_mem (mul_mem ha₂' ha₁')) (mul_mem ha₁' ha₂')
    have hzK₂ : (a₂ * a₁)⁻¹ * (a₁ * a₂) ∈ K₂ := by
      rw [hz]
      exact mul_mem (mul_mem hk₂ hk₁) (inv_mem (mul_mem hk₁ hk₂))
    have hz1 : (a₂ * a₁)⁻¹ * (a₁ * a₂) ∈ K₁ ⊓ K₂ := ⟨hzK₁, hzK₂⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hz1
    exact hz1.symm
  have hexp : ∀ a ∈ K₁ ⊓ (B ⊔ K₂), a ^ 3 = 1 := by
    intro a ha
    have ha' : a ∈ K₁ := (Subgroup.mem_inf.1 ha).1
    obtain ⟨c, hc, hbB⟩ := hdec a ha
    have hcm : Commute a c⁻¹ := hcomm a ha' c⁻¹ (inv_mem hc)
    have hpow := hB.2 _ hbB
    rw [hcm.mul_pow] at hpow
    have h3 : a ^ 3 = ((c⁻¹) ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    have h2K : a ^ 3 ∈ K₂ := by
      rw [h3]
      exact inv_mem (pow_mem (inv_mem hc) 3)
    have hmem : a ^ 3 ∈ K₁ ⊓ K₂ := ⟨pow_mem ha' 3, h2K⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hmem
  exact ⟨⟨⟨fun a b => Subtype.ext (hcommA a a.2 b b.2)⟩⟩, hexp⟩

theorem l94_decomp_or_large {H : Type*} [Group H] [Finite H] {K Bb Tb : Subgroup H} {xb : H}
    (hK : IsComponentOf K ⊤) (hKs : IsSimpleGroup K)
    (hy : ∃ y ∈ K, orderOf y = 3 ∧ ∃ W : Subgroup H, W ≤ K ∧ IsPGroup 2 W ∧ W ≠ ⊥ ∧
      y ∈ Subgroup.normalizer (W : Set H))
    (hB : IsElemAbelian 3 Bb) (hBK : Bb ≤ Subgroup.normalizer (K : Set H))
    (hinner : Bb ≤ K ⊔ Subgroup.centralizer (K : Set H))
    (hxB : xb ∈ Bb) (hxZ : xb ∈ Subgroup.center H)
    (hBR : Bb ⊓ Subgroup.centralizer (K : Set H) = Subgroup.zpowers xb)
    (hT2 : IsPGroup 2 Tb) (hTne : Tb ≠ ⊥) (hBT : Bb ≤ Subgroup.normalizer (Tb : Set H))
    (hTB : ⁅Tb, Bb⁆ = Tb) :
    Bb = (Bb ⊓ K) ⊔ Subgroup.zpowers xb ∨
      ∃ P W : Subgroup H, IsElemAbelian 3 P ∧ IsPGroup 2 W ∧ W ≠ ⊥ ∧
        P ≤ Subgroup.normalizer (W : Set H) ∧ Nat.card Bb < Nat.card P := by
  classical
  obtain ⟨y, hyK, hy3, W, hWK, hW2, hWne, hyW⟩ := hy
  set C : Subgroup H := Subgroup.centralizer (K : Set H) with hCdef
  have hKC : ∀ x ∈ K, ∀ c ∈ C, x * c = c * x :=
    fun x hx c hc => Subgroup.mem_centralizer_iff.1 hc x hx
  have hKZ := l94c_center_trivial hKs hyK hy3 hWK hW2 hWne
  have hKC_bot : K ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzK, hzC⟩ := Subgroup.mem_inf.1 hz
    exact Subgroup.mem_bot.2 (hKZ z hzK (fun g hg => hKC g hg z hzC))
  have hCK_bot : C ⊓ K = ⊥ := by
    rw [inf_comm]
    exact hKC_bot
  have hKC' : ∀ x ∈ K, ∀ c ∈ C, x * c = c * x := hKC
  have hCK' : ∀ x ∈ C, ∀ c ∈ K, x * c = c * x := fun x hx c hc => (hKC c hc x hx).symm
  have hCN : K ≤ Subgroup.normalizer (C : Set H) :=
    l94c_le_normalizer_of_comm (fun a ha u hu => hKC u hu a ha)
  have hKCN : K ⊔ C ≤ Subgroup.normalizer (C : Set H) :=
    sup_le hCN Subgroup.le_normalizer
  have hBN_C : Bb ≤ Subgroup.normalizer (C : Set H) := hinner.trans hKCN
  have hxbBC : xb ∈ Bb ⊓ C := by
    rw [hBR]
    exact Subgroup.mem_zpowers xb
  have hxbC : xb ∈ C := (Subgroup.mem_inf.1 hxbBC).2
  have hzpxb_le : Subgroup.zpowers xb ≤ Subgroup.center H := Subgroup.zpowers_le.2 hxZ
  have hzpxb_comm : ∀ a : H, ∀ u ∈ Subgroup.zpowers xb, u * a = a * u :=
    fun a u hu => (Subgroup.mem_center_iff.1 (hzpxb_le hu) a).symm
  have hxb3 : xb ^ 3 = 1 := hB.2 xb hxB
  have hzpxb_el : IsElemAbelian 3 (Subgroup.zpowers xb) := l94c_isElemAbelian_zpowers hxb3
  have hBcard : Nat.card Bb = Nat.card (K ⊓ (Bb ⊔ C) : Subgroup H) * Nat.card (Bb ⊓ C : Subgroup H) :=
    l94c_card_eq hKC' hKC_bot hinner hBN_C
  have hAK_el : IsElemAbelian 3 (K ⊓ (Bb ⊔ C) : Subgroup H) :=
    l94c_isElemAbelian_proj hKC' hKC_bot hB hBN_C
  have hAKK : K ⊓ (Bb ⊔ C) ≤ K := inf_le_left
  by_cases hTN : Tb ≤ Subgroup.normalizer (K : Set H)
  ·
    have hTD : Tb ≤ K ⊔ C := by
      have hcomm_br : ⁅Tb, Bb⁆ ≤ K ⊔ C := by
        rw [Subgroup.commutator_le]
        intro t ht b hb
        rw [commutatorElement_def]
        have htK : t ∈ Subgroup.normalizer (K : Set H) := hTN ht
        have htC : t ∈ Subgroup.normalizer (C : Set H) := l94c_mem_normalizer_centralizer htK
        have htD : t ∈ Subgroup.normalizer ((K ⊔ C : Subgroup H) : Set H) :=
          l94c_normalizer_sup (P := Subgroup.zpowers t)
            (Subgroup.zpowers_le.2 htK) (Subgroup.zpowers_le.2 htC) (Subgroup.mem_zpowers t)
        have hbD : t * b * t⁻¹ ∈ K ⊔ C := (Subgroup.mem_normalizer_iff.1 htD b).1 (hinner hb)
        exact mul_mem hbD (inv_mem (hinner hb))
      rw [← hTB]
      exact hcomm_br
    have hTBN : Tb ≤ Subgroup.normalizer (C : Set H) := hTD.trans hKCN
    have hTD' : Tb ≤ C ⊔ K := by
      rw [sup_comm]
      exact hTD
    set AK : Subgroup H := K ⊓ (Bb ⊔ C) with hAKdef
    set AR : Subgroup H := C ⊓ (Bb ⊔ K) with hARdef
    set TK : Subgroup H := K ⊓ (Tb ⊔ C) with hTKdef
    set TR : Subgroup H := C ⊓ (Tb ⊔ K) with hTRdef
    have hAKK : AK ≤ K := inf_le_left
    have hAKC : AK ≤ Bb ⊔ C := inf_le_right
    have hARC : AR ≤ C := inf_le_left
    have hARK : AR ≤ Bb ⊔ K := inf_le_right
    have hTKK : TK ≤ K := inf_le_left
    have hTKC : TK ≤ Tb ⊔ C := inf_le_right
    have hTRC : TR ≤ C := inf_le_left
    have hTRK : TR ≤ Tb ⊔ K := inf_le_right
    have hTcard1 : Nat.card Tb = Nat.card TK * Nat.card (Tb ⊓ C : Subgroup H) :=
      l94c_card_eq hKC' hKC_bot hTD hTBN
    have hTcard2 : Nat.card Tb = Nat.card TR * Nat.card (Tb ⊓ K : Subgroup H) :=
      l94c_card_eq hCK' hCK_bot hTD' hTN
    have hAR_el : IsElemAbelian 3 AR := l94c_isElemAbelian_proj hCK' hCK_bot hB hBK
    have hBN_TK : Bb ≤ Subgroup.normalizer (TK : Set H) :=
      l94c_normalizer_inf hBK (l94c_normalizer_sup hBT hBN_C)
    have hBN_TR : Bb ≤ Subgroup.normalizer (TR : Set H) :=
      l94c_normalizer_inf hBN_C (l94c_normalizer_sup hBT hBK)
    have hK_TR : K ≤ Subgroup.normalizer (TR : Set H) :=
      l94c_le_normalizer_of_comm (fun a ha u hu => hKC u hu a (hTRC ha))
    have hC_TK : C ≤ Subgroup.normalizer (TK : Set H) :=
      l94c_le_normalizer_of_comm (fun a ha u hu => hCK' u hu a (hTKK ha))
    have hAK_TK : AK ≤ Subgroup.normalizer (TK : Set H) := hAKC.trans (sup_le hBN_TK hC_TK)
    have hAK_TR : AK ≤ Subgroup.normalizer (TR : Set H) := hAKK.trans hK_TR
    have hAR_TK : AR ≤ Subgroup.normalizer (TK : Set H) := hARC.trans hC_TK
    have hAR_TR : AR ≤ Subgroup.normalizer (TR : Set H) := hARK.trans (sup_le hBN_TR hK_TR)
    have hP_TK : AK ⊔ AR ≤ Subgroup.normalizer (TK : Set H) := sup_le hAK_TK hAR_TK
    have hP_TR : AK ⊔ AR ≤ Subgroup.normalizer (TR : Set H) := sup_le hAK_TR hAR_TR
    have hP_W : AK ⊔ AR ≤ Subgroup.normalizer ((TK ⊔ TR : Subgroup H) : Set H) :=
      l94c_normalizer_sup hP_TK hP_TR
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hT2
    have hTK2 : Nat.card TK ∣ 2 ^ k := by
      rw [← hk]
      exact Dvd.intro _ hTcard1.symm
    have hTR2 : Nat.card TR ∣ 2 ^ k := by
      rw [← hk]
      exact Dvd.intro _ hTcard2.symm
    have hTKTR_bot : TK ⊓ TR = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hz
      have hz0 : z ∈ K ⊓ C := ⟨hTKK h1, hTRC h2⟩
      rw [hKC_bot, Subgroup.mem_bot] at hz0
      exact hz0
    have hTRN : TR ≤ Subgroup.normalizer (TK : Set H) := hTRC.trans hC_TK
    have hTKTR_card : Nat.card (TK ⊔ TR : Subgroup H) = Nat.card TK * Nat.card TR := by
      have h := card_sup_mul_card_inf_of_le_normalizer hTRN
      rw [hTKTR_bot, Subgroup.card_bot, mul_one] at h
      exact h
    have hTKTR2 : IsPGroup 2 (TK ⊔ TR : Subgroup H) := by
      apply IsPGroup.of_card_dvd_pow (n := k + k)
      rw [hTKTR_card, pow_add]
      exact mul_dvd_mul hTK2 hTR2
    have hTW : Tb ≤ TK ⊔ TR := by
      intro t ht
      obtain ⟨k₀, hk₀, c, hc, htkc⟩ := l94c_mem_sup_mul hCN (hTD ht)
      have e1 : k₀ = t * c⁻¹ := by
        rw [htkc]
        group
      have e2 : c = k₀⁻¹ * t := by
        rw [htkc]
        group
      have hk₀TK : k₀ ∈ TK :=
        Subgroup.mem_inf.2 ⟨hk₀, by
          rw [e1]
          exact mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right (inv_mem hc))⟩
      have hcTR : c ∈ TR :=
        Subgroup.mem_inf.2 ⟨hc, by
          rw [e2]
          exact mul_mem (Subgroup.mem_sup_right (inv_mem hk₀)) (Subgroup.mem_sup_left ht)⟩
      rw [htkc]
      exact mul_mem (Subgroup.mem_sup_left hk₀TK) (Subgroup.mem_sup_right hcTR)
    have hTKTRne : TK ⊔ TR ≠ ⊥ := by
      intro h
      apply hTne
      rw [eq_bot_iff]
      intro t ht
      have h' := hTW ht
      rw [h] at h'
      exact h'
    by_cases hAR : AR = Subgroup.zpowers xb
    · left
      apply le_antisymm
      · intro b hb
        obtain ⟨k₀, hk₀, c, hc, hbkc⟩ := l94c_mem_sup_mul hCN (hinner hb)
        have hcAR : c ∈ AR := by
          have e : c = k₀⁻¹ * b := by
            rw [hbkc]
            group
          refine Subgroup.mem_inf.2 ⟨hc, ?_⟩
          rw [e]
          exact mul_mem (Subgroup.mem_sup_right (inv_mem hk₀)) (Subgroup.mem_sup_left hb)
        have hcz : c ∈ Subgroup.zpowers xb := by
          rw [← hAR]
          exact hcAR
        have hcB : c ∈ Bb := (Subgroup.zpowers_le.2 hxB) hcz
        have hk₀B : k₀ ∈ Bb ⊓ K := by
          refine Subgroup.mem_inf.2 ⟨?_, hk₀⟩
          have e : k₀ = b * c⁻¹ := by
            rw [hbkc]
            group
          rw [e]
          exact mul_mem hb (inv_mem hcB)
        rw [hbkc]
        exact mul_mem (Subgroup.mem_sup_left hk₀B) (Subgroup.mem_sup_right hcz)
      · exact sup_le inf_le_left (Subgroup.zpowers_le.2 hxB)
    · right
      have hzpAR : Subgroup.zpowers xb ≤ AR :=
        Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hxbC, Subgroup.mem_sup_left hxB⟩)
      have hltAR : Subgroup.zpowers xb < AR := lt_of_le_of_ne hzpAR (fun h => hAR h.symm)
      have hcardAR : Nat.card (Subgroup.zpowers xb : Subgroup H) < Nat.card AR :=
        Subgroup.card_lt_of_lt hltAR
      have hAR_N : AR ≤ Subgroup.normalizer (AK : Set H) :=
        l94c_le_normalizer_of_comm (fun a ha u hu => hCK' u (hARC hu) a (hAKK ha))
      have hinterAA : AK ⊓ AR = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hz
        have hz0 : z ∈ K ⊓ C := ⟨hAKK h1, hARC h2⟩
        rw [hKC_bot, Subgroup.mem_bot] at hz0
        exact hz0
      have hcardP : Nat.card (AK ⊔ AR : Subgroup H) = Nat.card AK * Nat.card AR := by
        have h := card_sup_mul_card_inf_of_le_normalizer hAR_N
        rw [hinterAA, Subgroup.card_bot, mul_one] at h
        exact h
      have hAKpos : 0 < Nat.card AK := Nat.card_pos
      have hlt : Nat.card Bb < Nat.card (AK ⊔ AR : Subgroup H) := by
        rw [hcardP, hBcard, hBR]
        exact (Nat.mul_lt_mul_left hAKpos).2 hcardAR
      exact ⟨AK ⊔ AR, TK ⊔ TR, l94c_isElemAbelian_sup hAK_el hAR_el
        (fun s hs r hr => hKC s (hAKK hs) r (hARC hr)), hTKTR2, hTKTRne, hP_W, hlt⟩
  ·
    obtain ⟨t, htT, htN⟩ : ∃ t ∈ Tb, t ∉ Subgroup.normalizer (K : Set H) := by
      by_contra hcon
      push Not at hcon
      exact hTN (fun t ht => hcon t ht)
    set K' : Subgroup H := K.map (MulAut.conj t).toMonoidHom with hK'def
    have hK' : IsComponentOf K' ⊤ := CFSG.Quasithin.F918V5G.isComponentOf_map_conj hK (Subgroup.mem_top t)
    have hKK' : K ≠ K' := by
      intro h
      apply htN
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h.symm
    have hcommK' : ∀ x ∈ K, ∀ z ∈ K', x * z = z * x :=
      (CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hK hK').resolve_left hKK'
    have hKK'bot : K ⊓ K' = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzK, hzK'⟩ := Subgroup.mem_inf.1 hz
      exact Subgroup.mem_bot.2 (hKZ z hzK (fun g hg => hcommK' g hg z hzK'))
    have hy'K' : t * y * t⁻¹ ∈ K' := Subgroup.mem_map.2 ⟨y, hyK, rfl⟩
    set y' : H := t * y * t⁻¹ with hy'def
    have hy'ord : orderOf y' = 3 :=
      (orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective y).trans hy3
    have hy'cube : y' ^ 3 = 1 := by
      rw [← hy'ord]
      exact pow_orderOf_eq_one y'
    have hzpy'K' : Subgroup.zpowers y' ≤ K' := Subgroup.zpowers_le.2 hy'K'
    set W' : Subgroup H := W.map (MulAut.conj t).toMonoidHom with hW'def
    have hW'K' : W' ≤ K' := Subgroup.map_mono hWK
    have hW'2 : IsPGroup 2 W' := hW2.map _
    have hW'ne : W' ≠ ⊥ := by
      intro h
      apply hWne
      exact (Subgroup.map_eq_bot_iff_of_injective W (MulAut.conj t).injective).1 h
    have hmemW' : ∀ h : H, h ∈ W' ↔ t⁻¹ * h * t ∈ W := by
      intro h
      constructor
      · intro hh
        obtain ⟨w, hw, hwh⟩ := Subgroup.mem_map.1 hh
        have hwh' : t * w * t⁻¹ = h := hwh
        rw [← hwh']
        have e : t⁻¹ * (t * w * t⁻¹) * t = w := by group
        rw [e]
        exact hw
      · intro hh
        exact Subgroup.mem_map.2 ⟨t⁻¹ * h * t, hh, by show t * (t⁻¹ * h * t) * t⁻¹ = h; group⟩
    have hy'N : y' ∈ Subgroup.normalizer (W' : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [hmemW' h, hmemW' (y' * h * y'⁻¹)]
      have e : t⁻¹ * (y' * h * y'⁻¹) * t = y * (t⁻¹ * h * t) * y⁻¹ := by
        rw [hy'def]
        group
      rw [e]
      exact Subgroup.mem_normalizer_iff.1 hyW (t⁻¹ * h * t)
    have hAK_N : K ⊓ (Bb ⊔ C) ≤ Subgroup.normalizer (W' : Set H) :=
      l94c_le_normalizer_of_comm (fun a ha u hu => hcommK' u (hAKK hu) a (hW'K' ha))
    have hzpy'_N : Subgroup.zpowers y' ≤ Subgroup.normalizer (W' : Set H) :=
      Subgroup.zpowers_le.2 hy'N
    have hxb_N : Subgroup.zpowers xb ≤ Subgroup.normalizer (W' : Set H) :=
      l94c_le_normalizer_of_comm (fun a _ u hu => hzpxb_comm a u hu)
    have hAKy : IsElemAbelian 3 (K ⊓ (Bb ⊔ C) ⊔ Subgroup.zpowers y' : Subgroup H) :=
      l94c_isElemAbelian_sup hAK_el (l94c_isElemAbelian_zpowers hy'cube)
        (fun s hs u hu => hcommK' s (hAKK hs) u (hzpy'K' hu))
    have hP : IsElemAbelian 3
        ((K ⊓ (Bb ⊔ C) ⊔ Subgroup.zpowers y') ⊔ Subgroup.zpowers xb : Subgroup H) :=
      l94c_isElemAbelian_sup hAKy hzpxb_el (fun s _ u hu => (hzpxb_comm s u hu).symm)
    have hinfA : (K ⊓ (Bb ⊔ C)) ⊓ Subgroup.zpowers y' = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
      have hz0 : z ∈ K ⊓ K' := ⟨(Subgroup.mem_inf.1 hz1).1, hzpy'K' hz2⟩
      rw [hKK'bot] at hz0
      exact hz0
    have hinfB : (K ⊓ (Bb ⊔ C) ⊔ Subgroup.zpowers y') ⊓ Subgroup.zpowers xb = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
      have hzc : ∀ g : H, g * z = z * g := Subgroup.mem_center_iff.1 (hzpxb_le hz2)
      have hsub : K ⊓ (Bb ⊔ C) ⊔ Subgroup.zpowers y' ≤ K ⊔ K' :=
        sup_le ((inf_le_left : K ⊓ (Bb ⊔ C) ≤ K).trans le_sup_left) (hzpy'K'.trans le_sup_right)
      have hKN_K' : K ≤ Subgroup.normalizer (K' : Set H) :=
        l94c_le_normalizer_of_comm (fun a ha u hu => hcommK' u hu a ha)
      obtain ⟨k, hk, k', hk', hzkk'⟩ := l94c_mem_sup_mul hKN_K' (hsub hz1)
      have hk1 : k = 1 := by
        have hinv : k⁻¹ = 1 := by
          apply hKZ k⁻¹ (inv_mem hk)
          intro g hg
          have hk'eq : k' = k⁻¹ * z := by
            rw [hzkk']
            group
          have e1 : g * k⁻¹ * z = k⁻¹ * g * z := by
            calc g * k⁻¹ * z = g * (k⁻¹ * z) := by group
              _ = g * k' := by rw [hk'eq]
              _ = k' * g := hcommK' g hg k' hk'
              _ = k⁻¹ * z * g := by rw [hk'eq]
              _ = k⁻¹ * (z * g) := by group
              _ = k⁻¹ * (g * z) := by rw [hzc g]
              _ = k⁻¹ * g * z := by group
          exact mul_right_cancel e1
        exact inv_eq_one.1 hinv
      rw [hk1, one_mul] at hzkk'
      have hzK' : z ∈ K' := by
        rw [hzkk']
        exact hk'
      have hzK : z ∈ K := by
        obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.1 hzK'
        have hxeq' : t * x * t⁻¹ = z := hxeq
        have hxz : x = z := by
          calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
            _ = t⁻¹ * z * t := by rw [hxeq']
            _ = z := by rw [mul_assoc, ← hzc t, inv_mul_cancel_left]
        rw [← hxz]
        exact hx
      have hz0 : z ∈ K ⊓ K' := ⟨hzK, hzK'⟩
      rw [hKK'bot, Subgroup.mem_bot] at hz0
      exact hz0
    have hcard1 : Nat.card (K ⊓ (Bb ⊔ C) ⊔ Subgroup.zpowers y' : Subgroup H)
        = Nat.card (K ⊓ (Bb ⊔ C) : Subgroup H) * 3 := by
      have h := card_sup_mul_card_inf_of_le_normalizer (A := K ⊓ (Bb ⊔ C))
        (B := Subgroup.zpowers y')
        (l94c_le_normalizer_of_comm (fun a ha u hu => (hcommK' a (hAKK ha) u (hzpy'K' hu)).symm))
      rw [hinfA, Subgroup.card_bot, mul_one, Nat.card_zpowers, hy'ord] at h
      exact h
    have hcard2 : Nat.card ((K ⊓ (Bb ⊔ C) ⊔ Subgroup.zpowers y') ⊔ Subgroup.zpowers xb : Subgroup H)
        = Nat.card (K ⊓ (Bb ⊔ C) ⊔ Subgroup.zpowers y' : Subgroup H)
          * Nat.card (Subgroup.zpowers xb : Subgroup H) := by
      have h := card_sup_mul_card_inf_of_le_normalizer (A := K ⊓ (Bb ⊔ C) ⊔ Subgroup.zpowers y')
        (B := Subgroup.zpowers xb) (l94c_le_normalizer_of_comm (fun a _ u hu => hzpxb_comm a u hu))
      rw [hinfB, Subgroup.card_bot, mul_one] at h
      exact h
    have hBcard' : Nat.card Bb = Nat.card (K ⊓ (Bb ⊔ C) : Subgroup H) * Nat.card (Subgroup.zpowers xb : Subgroup H) := by
      rw [hBcard, hBR]
    have hpos : 0 < Nat.card Bb := Nat.card_pos
    right
    refine ⟨(K ⊓ (Bb ⊔ C) ⊔ Subgroup.zpowers y') ⊔ Subgroup.zpowers xb, W', hP, hW'2, hW'ne,
      sup_le (sup_le hAK_N hzpy'_N) hxb_N, ?_⟩
    rw [hcard2, hcard1]
    rw [hBcard'] at hpos ⊢
    nlinarith [hpos]

end CFSG.LocalAnalysis.GLTheoremA
