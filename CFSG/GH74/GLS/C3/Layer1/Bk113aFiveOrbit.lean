module

public import CFSG.GH74.GLS.C3.Layer1.BkP46Cnt

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Action

variable (R Q : Subgroup G)

omit [Finite G] in
theorem cj_mem_NRConj (s : ↥(normalizer (R : Set G))) (Q' : ↥(NRConj R Q)) :
    Th2.cj (s : G) (Q' : Subgroup G) ∈ NRConj R Q := by
  obtain ⟨g, hg, hgQ⟩ := Q'.2
  refine ⟨g * (s : G)⁻¹, (normalizer _).mul_mem hg ((normalizer _).inv_mem s.2), ?_⟩
  rw [hgQ]
  ext z
  rw [Th2.mem_cj_iff, mem_conjugate_iff', mem_conjugate_iff']
  have e : g * ((s : G)⁻¹ * z * (s : G)) * g⁻¹ = (g * (s : G)⁻¹) * z * (g * (s : G)⁻¹)⁻¹ := by
    group
  rw [e]

noncomputable instance NRConj.instMulAction :
    MulAction ↥(normalizer (R : Set G)) ↥(NRConj R Q) where
  smul s Q' := ⟨Th2.cj (s : G) (Q' : Subgroup G), cj_mem_NRConj R Q s Q'⟩
  one_smul Q' := Subtype.ext (by
    ext z
    show z ∈ Th2.cj (((1 : ↥(normalizer (R : Set G)))) : G) (Q' : Subgroup G) ↔
      z ∈ (Q' : Subgroup G)
    rw [Th2.mem_cj_iff]
    simp)
  mul_smul s t Q' := Subtype.ext (by
    ext z
    show z ∈ Th2.cj ((s * t : ↥(normalizer (R : Set G))) : G) (Q' : Subgroup G) ↔
      z ∈ Th2.cj (s : G) (Th2.cj (t : G) (Q' : Subgroup G))
    rw [Th2.mem_cj_iff, Th2.mem_cj_iff, Th2.mem_cj_iff]
    have e : ((s * t : ↥(normalizer (R : Set G))) : G)⁻¹ * z *
        ((s * t : ↥(normalizer (R : Set G))) : G) =
        (t : G)⁻¹ * ((s : G)⁻¹ * z * (s : G)) * (t : G) := by
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
    rw [e])

omit [Finite G] in
theorem coe_smul_NRConj (s : ↥(normalizer (R : Set G))) (Q' : ↥(NRConj R Q)) :
    ((s • Q' : ↥(NRConj R Q)) : Subgroup G) = Th2.cj (s : G) (Q' : Subgroup G) := rfl

omit [Finite G] in
theorem NRConj.mem_self : Q ∈ NRConj R Q :=
  ⟨1, one_mem _, (conjugate_eq_of_mem_normalizer' (one_mem _)).symm⟩

omit [Finite G] in
theorem NRConj.isPretransitive :
    MulAction.IsPretransitive ↥(normalizer (R : Set G)) ↥(NRConj R Q) := by
  refine ⟨fun Q₁ Q₂ => ?_⟩
  obtain ⟨g₁, hg₁, h₁⟩ := Q₁.2
  obtain ⟨g₂, hg₂, h₂⟩ := Q₂.2
  refine ⟨⟨g₂⁻¹ * g₁, (normalizer _).mul_mem ((normalizer _).inv_mem hg₂) hg₁⟩, ?_⟩
  apply Subtype.ext
  rw [coe_smul_NRConj, h₁, h₂]
  ext z
  rw [Th2.mem_cj_iff, mem_conjugate_iff', mem_conjugate_iff']
  have e : g₁ * ((g₂⁻¹ * g₁)⁻¹ * z * (g₂⁻¹ * g₁)) * g₁⁻¹ = g₂ * z * g₂⁻¹ := by group
  rw [e]

omit [Finite G] in
theorem NRConj_le' (hQR : Q ≤ R) (hQ4 : Nat.card ↥Q = 4) {Q' : Subgroup G}
    (hQ' : Q' ∈ NRConj R Q) : Q' ≤ R ∧ Nat.card ↥Q' = 4 := by
  obtain ⟨g, hg, rfl⟩ := hQ'
  refine ⟨fun z hz => ?_, by rw [card_conjugate', hQ4]⟩
  have h1 : g * z * g⁻¹ ∈ R := hQR (mem_conjugate_iff'.1 hz)
  have h2 := (Subgroup.mem_normalizer_iff.1 ((normalizer _).inv_mem hg) (g * z * g⁻¹)).1 h1
  have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
  rwa [e] at h2

omit [Finite G] in
theorem NRConj.eq_of_inf_ne_bot
    (hTI : ∀ n ∈ normalizer (R : Set G), conjugate Q n ≠ Q → conjugate Q n ⊓ Q = ⊥)
    {g₁ g₂ : G} (hg₁ : g₁ ∈ normalizer (R : Set G)) (hg₂ : g₂ ∈ normalizer (R : Set G))
    (hne : conjugate Q g₁ ⊓ conjugate Q g₂ ≠ ⊥) : conjugate Q g₁ = conjugate Q g₂ := by
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hu₁ : g₁ * u * g₁⁻¹ ∈ Q := mem_conjugate_iff'.1 hu.1
  have hu₂ : g₂ * u * g₂⁻¹ ∈ Q := mem_conjugate_iff'.1 hu.2
  have hhN : g₂ * g₁⁻¹ ∈ normalizer (R : Set G) :=
    (normalizer _).mul_mem hg₂ ((normalizer _).inv_mem hg₁)
  have hne' : Q ⊓ conjugate Q (g₂ * g₁⁻¹) ≠ ⊥ := by
    intro hbot
    have hmem : g₁ * u * g₁⁻¹ ∈ Q ⊓ conjugate Q (g₂ * g₁⁻¹) := by
      refine ⟨hu₁, mem_conjugate_iff'.2 ?_⟩
      have e : (g₂ * g₁⁻¹) * (g₁ * u * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹ = g₂ * u * g₂⁻¹ := by group
      rw [e]
      exact hu₂
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hu1
    apply Subtype.ext
    have : u = g₁⁻¹ * (g₁ * u * g₁⁻¹) * g₁ := by group
    show u = 1
    rw [this, hmem]
    group
  have hTI' : conjugate Q (g₂ * g₁⁻¹) = Q := by
    by_contra hne''
    have h := hTI (g₂ * g₁⁻¹) hhN hne''
    apply hne'
    rwa [inf_comm]
  ext z
  rw [mem_conjugate_iff', mem_conjugate_iff']
  have hiff : ∀ v, v ∈ Q ↔ (g₂ * g₁⁻¹) * v * (g₂ * g₁⁻¹)⁻¹ ∈ Q := by
    intro v
    have := (Subgroup.ext_iff.1 hTI' v)
    rw [mem_conjugate_iff'] at this
    exact this.symm
  rw [hiff (g₁ * z * g₁⁻¹)]
  have e : (g₂ * g₁⁻¹) * (g₁ * z * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹ = g₂ * z * g₂⁻¹ := by group
  rw [e]

end Action

theorem eq_P_of_w_normalizes' {P Q : Subgroup G} {w : G} (hCD : CommDisj P Q)
    (hPcard : Nat.card ↥P = 4) (hwP : ∀ p ∈ P, w * p * w⁻¹ ∈ P)
    (hwQ : ∀ q ∈ Q, w * q = q * w) (hwfpf : ∀ p ∈ P, w * p * w⁻¹ = p → p = 1)
    {Q₃ : Subgroup G} (hQ₃R : Q₃ ≤ P ⊔ Q) (hQ₃c : Nat.card ↥Q₃ = 4)
    (hQ₃Q : Q₃ ⊓ Q = ⊥) (hwQ₃ : w ∈ normalizer (Q₃ : Set G)) : Q₃ = P := by
  have hwQ' : ∀ q ∈ Q, w * q * w⁻¹ = q := fun q hq => by
    rw [hwQ q hq]
    group
  have hcent : ∀ c ∈ Q₃, w * c * w⁻¹ = c → c = 1 := by
    intro c hc hwc
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hCD.comm (hQ₃R hc)
    have h1 : w * p * w⁻¹ = p := by
      have e : w * (p * q) * w⁻¹ = (w * p * w⁻¹) * (w * q * w⁻¹) := by group
      rw [e, hwQ' q hq] at hwc
      exact mul_right_cancel hwc
    have hp1 := hwfpf p hp h1
    subst hp1
    have hqQ₃ : q ∈ Q₃ ⊓ Q := ⟨by simpa using hc, hq⟩
    rw [hQ₃Q, Subgroup.mem_bot] at hqQ₃
    rw [hqQ₃]
    group
  let d : ↥Q₃ → ↥Q₃ := fun q' => ⟨(q' : G)⁻¹ * (w * q' * w⁻¹),
    Q₃.mul_mem (Q₃.inv_mem q'.2) ((Subgroup.mem_normalizer_iff.1 hwQ₃ q').1 q'.2)⟩
  have hdinj : Function.Injective d := by
    intro a₁ b₁ hab
    have h1 : (a₁ : G)⁻¹ * (w * a₁ * w⁻¹) = (b₁ : G)⁻¹ * (w * b₁ * w⁻¹) := congrArg Subtype.val hab
    have hc : w * ((a₁ : G) * (b₁ : G)⁻¹) * w⁻¹ = (a₁ : G) * (b₁ : G)⁻¹ := by
      have e1 : w * a₁ * w⁻¹ = a₁ * ((b₁ : G)⁻¹ * (w * b₁ * w⁻¹)) := by
        calc w * a₁ * w⁻¹ = a₁ * ((a₁ : G)⁻¹ * (w * a₁ * w⁻¹)) := by group
          _ = _ := by rw [h1]
      calc w * ((a₁ : G) * (b₁ : G)⁻¹) * w⁻¹ = (w * a₁ * w⁻¹) * (w * b₁ * w⁻¹)⁻¹ := by group
        _ = (a₁ : G) * (b₁ : G)⁻¹ := by rw [e1]; group
    have hmem : (a₁ : G) * (b₁ : G)⁻¹ ∈ Q₃ := Q₃.mul_mem a₁.2 (Q₃.inv_mem b₁.2)
    have h2 := hcent _ hmem hc
    apply Subtype.ext
    have : (a₁ : G) = (a₁ * (b₁ : G)⁻¹) * b₁ := by group
    rw [this, h2]
    group
  have hdsurj : Function.Surjective d := Finite.injective_iff_surjective.1 hdinj
  have hle : Q₃ ≤ P := by
    intro q' hq'
    obtain ⟨a', ha'⟩ := hdsurj ⟨q', hq'⟩
    have hq'eq : q' = (a' : G)⁻¹ * (w * a' * w⁻¹) := (congrArg Subtype.val ha').symm
    obtain ⟨p, hp, q, hq, hpq⟩ := mem_sup_of_commute hCD.comm (hQ₃R a'.2)
    have hu : p⁻¹ * (w * p * w⁻¹) ∈ P := P.mul_mem (P.inv_mem hp) (hwP p hp)
    have hcomm : q⁻¹ * (p⁻¹ * (w * p * w⁻¹)) * q = p⁻¹ * (w * p * w⁻¹) := by
      have := hCD.comm _ hu q hq
      calc q⁻¹ * (p⁻¹ * (w * p * w⁻¹)) * q = q⁻¹ * ((p⁻¹ * (w * p * w⁻¹)) * q) := by group
        _ = q⁻¹ * (q * (p⁻¹ * (w * p * w⁻¹))) := by rw [this]
        _ = _ := by group
    have hz : (a' : G)⁻¹ * (w * a' * w⁻¹) = q⁻¹ * (p⁻¹ * (w * p * w⁻¹)) * q := by
      rw [hpq]
      have e : w * (p * q) * w⁻¹ = (w * p * w⁻¹) * (w * q * w⁻¹) := by group
      rw [e, hwQ' q hq]
      group
    rw [hq'eq, hz, hcomm]
    exact hu
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hPcard, hQ₃c])

theorem five_orbit_false {P Q T : Subgroup G} {w : G}
    (hCD : CommDisj P Q) (hP4 : Nat.card ↥P = 4) (hQ4 : Nat.card ↥Q = 4)
    (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hR16 : Nat.card ↥(P ⊔ Q) = 16)
    (hTSyl : IsSylowOf 2 T ⊤) (hTN : T ≤ normalizer ((P ⊔ Q : Subgroup G) : Set G))
    (hTQ : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) (hT32 : Nat.card ↥T ≤ 32)
    (hTI : ∀ n ∈ normalizer ((P ⊔ Q : Subgroup G) : Set G), conjugate Q n ≠ Q →
      conjugate Q n ⊓ Q = ⊥)
    (hex : ∃ n ∈ normalizer ((P ⊔ Q : Subgroup G) : Set G), conjugate Q n ≠ Q)
    (hwR : w ∈ normalizer ((P ⊔ Q : Subgroup G) : Set G)) (hwP : ∀ p ∈ P, w * p * w⁻¹ ∈ P)
    (hwQ : ∀ q ∈ Q, w * q = q * w) (hwfpf : ∀ p ∈ P, w * p * w⁻¹ = p → p = 1)
    (hw3 : ∃ e : ℕ, w ^ (3 ^ e) = 1) : False := by
  classical
  set R : Subgroup G := P ⊔ Q with hRdef
  set N : Subgroup G := normalizer (R : Set G) with hNdef
  have hQR : Q ≤ R := le_sup_right
  have hRN : R ≤ N := Subgroup.le_normalizer
  have hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hCD.comm ha
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_sup_of_commute hCD.comm hb
    calc p * q * (p' * q') = p * (q * p') * q' := by group
      _ = p * (p' * q) * q' := by rw [← hCD.comm p' hp' q hq]
      _ = (p * p') * (q * q') := by group
      _ = (p' * p) * (q' * q) := by rw [hPab p hp p' hp', hQab q hq q' hq']
      _ = p' * (p * q') * q := by group
      _ = p' * (q' * p) * q := by rw [hCD.comm p hp q' hq']
      _ = p' * q' * (p * q) := by group
  have hwQN : w ∈ normalizer (Q : Set G) := mem_normalizer_of_conj_le (fun q hq => by
    have : w * q * w⁻¹ = q := by rw [hwQ q hq]; group
    rw [this]; exact hq)
  have hTQN : T ≤ normalizer (Q : Set G) := fun t ht =>
    mem_normalizer_of_conj_le (fun q hq => hTQ t ht q hq)
  have hTI' : ∀ g₁ ∈ N, ∀ g₂ ∈ N, conjugate Q g₁ ⊓ conjugate Q g₂ ≠ ⊥ →
      conjugate Q g₁ = conjugate Q g₂ := fun g₁ hg₁ g₂ hg₂ h =>
    NRConj.eq_of_inf_ne_bot R Q hTI hg₁ hg₂ h
  have hle5 : Nat.card ↥(NRConj R Q) ≤ 5 := by
    refine card_le_five_of_disjoint hR16 (fun Q' hQ' => (NRConj_le' R Q hQR hQ4 hQ').1)
      (fun Q' hQ' => (NRConj_le' R Q hQR hQ4 hQ').2) (fun Q₁ h₁ Q₂ h₂ hne => ?_)
    by_contra hbot
    obtain ⟨g₁, hg₁, rfl⟩ := h₁
    obtain ⟨g₂, hg₂, rfl⟩ := h₂
    exact hne (hTI' g₁ hg₁ g₂ hg₂ hbot)
  have hge2 : 2 ≤ Nat.card ↥(NRConj R Q) := by
    obtain ⟨n, hn, hne⟩ := hex
    have h1 : Q ∈ NRConj R Q := NRConj.mem_self R Q
    have h2 : conjugate Q n ∈ NRConj R Q := ⟨n, hn, rfl⟩
    have : Nontrivial ↥(NRConj R Q) :=
      ⟨⟨⟨Q, h1⟩, ⟨conjugate Q n, h2⟩, fun h => hne (congrArg Subtype.val h).symm⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.2 this
  have := NRConj.isPretransitive R Q
  let b : ↥(NRConj R Q) := ⟨Q, NRConj.mem_self R Q⟩
  have hodd : Odd (Nat.card ↥(NRConj R Q)) := by
    have h1 : (MulAction.stabilizer ↥N b).index = Nat.card ↥(NRConj R Q) :=
      MulAction.index_stabilizer_of_transitive _ b
    have hstab : T.subgroupOf N ≤ MulAction.stabilizer ↥N b := by
      intro t ht
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      rw [coe_smul_NRConj]
      exact Th2.cj_eq_of_mem_normalizer (hTQN (Subgroup.mem_subgroupOf.1 ht))
    have hdvd : (MulAction.stabilizer ↥N b).index ∣ (T.subgroupOf N).index :=
      Subgroup.index_dvd_of_le hstab
    have hTidx : ¬ 2 ∣ (T.subgroupOf N).index := by
      have h := (isSylowOf_iff.1 hTSyl).2.2
      rw [Subgroup.relIndex_top_right] at h
      intro hd
      exact h (hd.trans (Subgroup.relIndex_dvd_index_of_le hTN))
    have h2 : ¬ 2 ∣ Nat.card ↥(NRConj R Q) := by
      rw [← h1]
      exact fun hd => hTidx (hd.trans hdvd)
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h2)
  have hk : Nat.card ↥(NRConj R Q) = 3 ∨ Nat.card ↥(NRConj R Q) = 5 := by
    obtain ⟨m, hm⟩ := hodd
    omega
  let ρ : ↥N →* Equiv.Perm ↥(NRConj R Q) := MulAction.toPermHom ↥N ↥(NRConj R Q)
  let wN : ↥N := ⟨w, hwR⟩
  let σ : Equiv.Perm ↥(NRConj R Q) := ρ wN
  have hσ : ∀ Q' : ↥(NRConj R Q), σ Q' = wN • Q' := fun _ => rfl
  have hfixed : ∀ Q' : ↥(NRConj R Q), σ Q' = Q' →
      (Q' : Subgroup G) = Q ∨ (Q' : Subgroup G) = P := by
    intro Q' hQ'
    by_cases hQQ : (Q' : Subgroup G) = Q
    · exact Or.inl hQQ
    · right
      obtain ⟨g, hg, hgQ⟩ := Q'.2
      have hwN' : w ∈ normalizer ((Q' : Subgroup G) : Set G) := by
        refine Th2.mem_normalizer_of_cj_eq ?_
        have := congrArg Subtype.val ((hσ Q').symm.trans hQ')
        rwa [coe_smul_NRConj] at this
      have hne : conjugate Q g ≠ Q := fun h => hQQ (hgQ.trans h)
      have hTIg : conjugate Q g ⊓ Q = ⊥ := hTI g hg hne
      have hQ'Q : (Q' : Subgroup G) ⊓ Q = ⊥ := by rw [hgQ]; exact hTIg
      exact eq_P_of_w_normalizes' hCD hP4 hwP hwQ hwfpf
        (NRConj_le' R Q hQR hQ4 Q'.2).1 (NRConj_le' R Q hQR hQ4 Q'.2).2 hQ'Q hwN'
  have hfixQ : σ b = b := by
    rw [hσ]
    apply Subtype.ext
    rw [coe_smul_NRConj]
    exact Th2.cj_eq_of_mem_normalizer hwQN
  have : Fintype ↥(NRConj R Q) := Fintype.ofFinite _
  obtain ⟨e, he⟩ := hw3
  have hσe : σ ^ (3 ^ e) = 1 := by
    have h1 : wN ^ (3 ^ e) = 1 := Subtype.ext (by simpa using he)
    show ρ wN ^ (3 ^ e) = 1
    rw [← map_pow, h1, map_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ3 : IsPGroup 3 ↥(Subgroup.zpowers σ) := by
    have h1 : orderOf σ ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hσe
    obtain ⟨k, -, hk3⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk3])
  have hmod := hσ3.card_modEq_card_fixedPoints (α := ↥(NRConj R Q))
  have hfixcard : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers σ) ↥(NRConj R Q)) =
      Nat.card {Q' : ↥(NRConj R Q) // σ Q' = Q'} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun Q' => ?_))
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro h g
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 g.2
      show (g : Equiv.Perm ↥(NRConj R Q)) Q' = Q'
      rw [← hj]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h j
  rw [hfixcard] at hmod
  have hf1 : 1 ≤ Nat.card {Q' : ↥(NRConj R Q) // σ Q' = Q'} :=
    Nat.card_pos_iff.2 ⟨⟨⟨b, hfixQ⟩⟩, inferInstance⟩
  have hf2 : Nat.card {Q' : ↥(NRConj R Q) // σ Q' = Q'} ≤ 2 := by
    have hinj : Function.Injective
        (fun Q' : {Q' : ↥(NRConj R Q) // σ Q' = Q'} => decide ((Q'.1 : Subgroup G) = Q)) := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      by_cases hx : (x.1 : Subgroup G) = Q
      · have hy : (y.1 : Subgroup G) = Q := by
          by_contra hy
          simp [hx, hy] at hxy
        rw [hx, hy]
      · have hy : ¬ (y.1 : Subgroup G) = Q := by
          intro hy
          simp [hx, hy] at hxy
        rw [(hfixed x.1 x.2).resolve_left hx, (hfixed y.1 y.2).resolve_left hy]
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hk5 : Nat.card ↥(NRConj R Q) = 5 := by
    rcases hk with hk | hk
    · rw [hk] at hmod
      unfold Nat.ModEq at hmod
      omega
    · exact hk
  have : Nontrivial ↥(NRConj R Q) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  have hfix2 : Nat.card {Q' : ↥(NRConj R Q) // σ Q' = Q'} = 2 := by
    rw [hk5] at hmod
    unfold Nat.ModEq at hmod
    omega
  have hthree : σ.IsThreeCycle := by
    have hX : Fintype.card ↥(NRConj R Q) = 5 := by rw [← Nat.card_eq_fintype_card]; exact hk5
    have hF : Fintype.card {Q' : ↥(NRConj R Q) // σ Q' = Q'} = 2 := by
      rw [← Nat.card_eq_fintype_card]; exact hfix2
    have hsupp : σ.support.card = 3 := by
      have h1 := Fintype.card_subtype_compl (fun Q' : ↥(NRConj R Q) => σ Q' = Q')
      have h2 : σ.support = Finset.univ.filter (fun Q' => ¬ σ Q' = Q') := rfl
      have h3 : Fintype.card {Q' : ↥(NRConj R Q) // ¬ σ Q' = Q'} = σ.support.card := by
        rw [h2, Fintype.card_subtype]
      omega
    exact card_support_eq_three_iff.1 hsupp
  let H : Subgroup (Equiv.Perm ↥(NRConj R Q)) := ρ.range
  have hσH : σ ∈ H := ⟨wN, rfl⟩
  have : MulAction.IsPretransitive ↥H ↥(NRConj R Q) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨s, hs⟩ := MulAction.exists_smul_eq ↥N x y
    exact ⟨⟨ρ s, s, rfl⟩, hs⟩
  have : MulAction.IsPreprimitive ↥H ↥(NRConj R Q) :=
    MulAction.IsPreprimitive.of_prime_card (by rw [hk5]; exact Nat.prime_five)
  have hA : alternatingGroup ↥(NRConj R Q) ≤ H :=
    Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem ‹_› hthree hσH
  have h60 : 60 ∣ Nat.card ↥H := by
    have h1 := Subgroup.card_dvd_of_le hA
    have h2 : Nat.card ↥(alternatingGroup ↥(NRConj R Q)) = 60 := by
      have hX : Fintype.card ↥(NRConj R Q) = 5 := by rw [← Nat.card_eq_fintype_card]; exact hk5
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, hX]
      decide
    rwa [h2] at h1
  have h4 : 4 ∣ Nat.card ↥H := (Dvd.intro _ (by norm_num : 4 * 15 = 60)).trans h60
  have hker : R.subgroupOf N ≤ ρ.ker := by
    intro r hr
    rw [MonoidHom.mem_ker]
    have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.1 hr
    refine Equiv.ext (fun Q' => ?_)
    apply Subtype.ext
    show ((r • Q' : ↥(NRConj R Q)) : Subgroup G) = (Q' : Subgroup G)
    rw [coe_smul_NRConj]
    have hrN : (r : G) ∈ normalizer ((Q' : Subgroup G) : Set G) :=
      mem_normalizer_of_conj_le (fun z hz => by
        have hzR : z ∈ R := (NRConj_le' R Q hQR hQ4 Q'.2).1 hz
        have : (r : G) * z * (r : G)⁻¹ = z := by
          rw [hRab _ hrR z hzR]; group
        rw [this]; exact hz)
    exact Th2.cj_eq_of_mem_normalizer hrN
  have h16 : 16 ∣ Nat.card ↥ρ.ker := by
    have h1 := Subgroup.card_dvd_of_le hker
    have h2 : Nat.card ↥(R.subgroupOf N) = Nat.card ↥R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv
    rwa [h2, hR16] at h1
  have h64 : 64 ∣ Nat.card ↥N := by
    have h1 : Nat.card ↥ρ.ker * Nat.card ↥H = Nat.card ↥N := Subgroup.card_ker_mul_card_range ρ
    rw [← h1]
    have h2 := Nat.mul_dvd_mul h16 h4
    simpa using h2
  have hTidx : ¬ 2 ∣ (T.subgroupOf N).index := by
    have h := (isSylowOf_iff.1 hTSyl).2.2
    rw [Subgroup.relIndex_top_right] at h
    intro hd
    exact h (hd.trans (Subgroup.relIndex_dvd_index_of_le hTN))
  have hNT := Subgroup.card_mul_index (T.subgroupOf N)
  have hTcard : Nat.card ↥(T.subgroupOf N) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  rw [hTcard] at hNT
  have hcop : Nat.Coprime 64 (T.subgroupOf N).index := by
    have : Nat.Coprime 2 (T.subgroupOf N).index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hTidx
    simpa using Nat.Coprime.pow_left 6 this
  rw [← hNT] at h64
  have h64T : 64 ∣ Nat.card ↥T := hcop.dvd_of_dvd_mul_right h64
  have := Nat.le_of_dvd Nat.card_pos h64T
  omega

end CFSG.GH74.GLS.C3.Layer1.Bk
