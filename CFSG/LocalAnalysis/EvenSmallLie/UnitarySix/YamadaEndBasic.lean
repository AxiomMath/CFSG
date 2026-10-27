module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.Defs

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem le_derivedSeries_of_perfect {Q : Type*} [Group Q] {X : Subgroup Q} (hX : ⁅X, X⁆ = X)
    (n : ℕ) : X ≤ derivedSeries Q n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [derivedSeries_succ, ← hX]
    exact commutator_mono ih ih

theorem eq_bot_of_perfect_of_isSolvable {Q : Type*} [Group Q] [Group.IsSolvable Q] {X : Subgroup Q}
    (hX : ⁅X, X⁆ = X) : X = ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := Q)
  exact le_bot_iff.mp (hn ▸ le_derivedSeries_of_perfect hX n)

theorem le_of_perfect_of_le_sup {N G₀ K : Subgroup G} [Group.IsSolvable N]
    (hN : N ≤ normalizer (G₀ : Set G)) (hK : ⁅K, K⁆ = K) (hKle : K ≤ N ⊔ G₀) : K ≤ G₀ := by
  set M := N ⊔ G₀ with hM
  have hG₀M : G₀ ≤ M := le_sup_right
  have hMN : M ≤ normalizer (G₀ : Set G) := sup_le hN le_normalizer
  have hnormal : (G₀.subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer hG₀M).mpr hMN
  set q : M →* M ⧸ G₀.subgroupOf M := QuotientGroup.mk' _ with hq
  have hsurj : Function.Surjective (q.comp (inclusion (le_sup_left : N ≤ M))) := by
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (G₀.subgroupOf M) y
    have hm : (m : G) ∈ (N : Set G) * (G₀ : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right N G₀ hN]
      exact m.2
    obtain ⟨a, ha, g, hg, hag⟩ := hm
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [MonoidHom.comp_apply, hq, QuotientGroup.mk'_apply, QuotientGroup.eq]
    change (⟨a, le_sup_left (a := N) ha⟩ : M)⁻¹ * m ∈ G₀.subgroupOf M
    rw [mem_subgroupOf]
    simp only [coe_mul, coe_inv]
    rw [← hag]
    simpa using hg
  have hsolv : Group.IsSolvable (M ⧸ G₀.subgroupOf M) := Group.isSolvable_of_surjective hsurj
  set K' := K.subgroupOf M with hK'
  have hK'perf : ⁅K', K'⁆ = K' := by
    apply map_injective M.subtype_injective
    rw [map_commutator, hK', subgroupOf_map_subtype, inf_of_le_left hKle, hK]
  have himg : ⁅K'.map q, K'.map q⁆ = K'.map q := by
    rw [← map_commutator, hK'perf]
  have hbot := eq_bot_of_perfect_of_isSolvable himg
  intro k hk
  have hk' : (⟨k, hKle hk⟩ : M) ∈ K' := hk
  have h1 : q ⟨k, hKle hk⟩ = 1 := by
    have : q ⟨k, hKle hk⟩ ∈ K'.map q := mem_map_of_mem q hk'
    rwa [hbot, mem_bot] at this
  have h2 : (⟨k, hKle hk⟩ : M) ∈ G₀.subgroupOf M := by
    rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h2

theorem eq_top_of_normal_of_not_le_center {X : Type*} [Group X] (hX : CFSG.Open.IsQuasisimple X)
    {N : Subgroup X} [hN : N.Normal] (hNZ : ¬ N ≤ center X) : N = ⊤ := by
  obtain ⟨hperf, hsimple⟩ := hX
  have hmap : (N.map (QuotientGroup.mk' (center X))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center X)))
    with h | h
  · exfalso
    apply hNZ
    intro x hx
    have hx' := mem_map_of_mem (QuotientGroup.mk' (center X)) hx
    rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  · have hsplit : ∀ x : X, ∃ n ∈ N, n⁻¹ * x ∈ center X := fun x => by
      have hx : QuotientGroup.mk' (center X) x ∈ N.map (QuotientGroup.mk' (center X)) :=
        h ▸ mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      exact ⟨n, hn, QuotientGroup.eq.mp hnx⟩
    refine eq_top_iff.mpr ?_
    rw [← hperf, commutator_def, commutator_le]
    intro x _ y _
    obtain ⟨n, hn, hz⟩ := hsplit x
    obtain ⟨n', hn', hz'⟩ := hsplit y
    rw [← QuotientGroup.eq_one_iff (N := N)]
    have hx : (x : X ⧸ N) = ((n⁻¹ * x : X) : X ⧸ N) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff n).mpr hn,
        inv_one, one_mul]
    have hy : (y : X ⧸ N) = ((n'⁻¹ * y : X) : X ⧸ N) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff n').mpr hn',
        inv_one, one_mul]
    have hc : ⁅n⁻¹ * x, n'⁻¹ * y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz _).symm
    change QuotientGroup.mk' N ⁅x, y⁆ = 1
    rw [map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hx, hy,
      ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, ← map_commutatorElement, hc,
      map_one]

theorem mem_of_mul_central_odd [Finite G] {A Z : Subgroup G} (hZ : Odd (Nat.card Z))
    {a z : G} (ha : a ∈ A) (hz : z ∈ Z) (hcomm : a * z = z * a) {k : ℕ}
    (hk : (a * z) ^ (2 ^ k) = 1) : a * z ∈ A := by
  set m := Nat.card Z with hm
  have hzm : z ^ m = 1 := by
    have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    exact congrArg Subtype.val this
  have hpow : (a * z) ^ m = a ^ m := by
    rw [(show Commute a z from hcomm).mul_pow, hzm, mul_one]
  have hcop : Nat.Coprime m (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hZ)
  have hord : orderOf (a * z) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop' : Nat.Coprime m (orderOf (a * z)) := Nat.Coprime.coprime_dvd_right hord hcop
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop'
  rw [← hn, hpow, ← pow_mul]
  exact pow_mem ha _

theorem commutator_eq_self_of_quasisimple {Q : Subgroup G} (hQ : CFSG.Open.IsQuasisimple Q) :
    ⁅Q, Q⁆ = Q := by
  have h := congrArg (map Q.subtype) hQ.1
  rwa [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h

theorem not_le_centralizer_self_of_quasisimple {Q : Subgroup G}
    (hQ : CFSG.Open.IsQuasisimple Q) : ¬ Q ≤ centralizer (Q : Set G) := by
  intro h
  have hbot : ⁅Q, Q⁆ = ⊥ := (commutator_eq_bot_iff_le_centralizer).mpr h
  rw [commutator_eq_self_of_quasisimple hQ] at hbot
  have : Subsingleton Q := by
    rw [hbot]
    infer_instance
  have hs := hQ.2
  have : Nontrivial (Q ⧸ center Q) := hs.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ center Q)
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [Subsingleton.elim a' b'])

theorem eq_of_le_of_not_le_centralizer {Q N : Subgroup G} (hQ : CFSG.Open.IsQuasisimple Q)
    (hNQ : N ≤ Q) (hQN : Q ≤ normalizer (N : Set G)) (hNZ : ¬ N ≤ centralizer (Q : Set G)) :
    N = Q := by
  have hnormal : (N.subgroupOf Q).Normal := (normal_subgroupOf_iff_le_normalizer hNQ).mpr hQN
  have hnot : ¬ N.subgroupOf Q ≤ center Q := by
    intro h
    apply hNZ
    intro n hn
    rw [mem_centralizer_iff]
    intro q hq
    have hz := h (show (⟨n, hNQ hn⟩ : Q) ∈ N.subgroupOf Q from hn)
    have := (mem_center_iff.mp hz) ⟨q, hq⟩
    exact congrArg Subtype.val this
  have htop := eq_top_of_normal_of_not_le_center hQ hnot
  refine le_antisymm hNQ fun q hq => ?_
  have : (⟨q, hq⟩ : Q) ∈ N.subgroupOf Q := htop ▸ mem_top _
  exact this

theorem commutator_le_inf_of_le_normalizer {A B : Subgroup G}
    (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G)) : ⁅A, B⁆ ≤ A ⊓ B := by
  rw [commutator_le]
  intro a ha b hb
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    have : b * a⁻¹ * b⁻¹ ∈ A := (mem_normalizer_iff.mp (hBA hb) _).mp (A.inv_mem ha)
    simpa [mul_assoc] using A.mul_mem ha this
  · rw [commutatorElement_def]
    have : a * b * a⁻¹ ∈ B := (mem_normalizer_iff.mp (hAB ha) _).mp hb
    exact B.mul_mem this (B.inv_mem hb)

theorem eq_of_quasisimple_of_commutator_ne_bot {G₁ Q : Subgroup G}
    (h₁ : CFSG.Open.IsQuasisimple G₁) (hQ : CFSG.Open.IsQuasisimple Q)
    (hQG : Q ≤ normalizer (G₁ : Set G)) (hGQ : G₁ ≤ normalizer (Q : Set G))
    (hne : ⁅Q, G₁⁆ ≠ ⊥) : Q = G₁ := by
  have hle : ⁅Q, G₁⁆ ≤ Q ⊓ G₁ := commutator_le_inf_of_le_normalizer hQG hGQ
  have hQN : Q ≤ normalizer ((Q ⊓ G₁ : Subgroup G) : Set G) := by
    intro q hq
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxQ, hxG⟩
      exact ⟨Q.mul_mem (Q.mul_mem hq hxQ) (Q.inv_mem hq),
        (mem_normalizer_iff.mp (hQG hq) x).mp hxG⟩
    · rintro ⟨hxQ, hxG⟩
      refine ⟨?_, (mem_normalizer_iff.mp (hQG hq) x).mpr hxG⟩
      have := Q.mul_mem (Q.mul_mem (Q.inv_mem hq) hxQ) hq
      simpa [mul_assoc] using this
  have hnotZ : ¬ (Q ⊓ G₁ : Subgroup G) ≤ centralizer (Q : Set G) := by
    intro hZ
    apply hne
    have h1 : ⁅⁅Q, G₁⁆, Q⁆ = ⊥ :=
      (commutator_eq_bot_iff_le_centralizer).mpr (hle.trans hZ)
    have h2 : ⁅⁅G₁, Q⁆, Q⁆ = ⊥ := by rw [commutator_comm G₁ Q]; exact h1
    have h3 := commutator_commutator_eq_bot_of_rotate (H₁ := Q) (H₂ := Q) (H₃ := G₁) h1 h2
    rwa [commutator_eq_self_of_quasisimple hQ] at h3
  have hQG₁ : Q ≤ G₁ := by
    have := eq_of_le_of_not_le_centralizer hQ inf_le_left hQN hnotZ
    rw [← this]
    exact inf_le_right
  exact eq_of_le_of_not_le_centralizer h₁ hQG₁ hGQ fun hc => hne
    ((commutator_eq_bot_iff_le_centralizer).mpr hc)

theorem mem_centralizer_sup {A B : Subgroup G} {y : G} (hA : ∀ a ∈ A, a * y = y * a)
    (hB : ∀ b ∈ B, b * y = y * b) : y ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hle : A ⊔ B ≤ centralizer ({y} : Set G) :=
    sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (hA a ha))
      (fun b hb => mem_centralizer_singleton_iff.mpr (hB b hb))
  rw [mem_centralizer_iff]
  intro z hz
  exact mem_centralizer_singleton_iff.mp (hle hz)

theorem eq_or_eq_of_quasisimple_of_le_sup {G₁ G₂ Q : Subgroup G}
    (h₁ : CFSG.Open.IsQuasisimple G₁) (h₂ : CFSG.Open.IsQuasisimple G₂)
    (hQ : CFSG.Open.IsQuasisimple Q) (hc : ⁅G₁, G₂⁆ = ⊥) (hQle : Q ≤ G₁ ⊔ G₂)
    (hQn : G₁ ⊔ G₂ ≤ normalizer (Q : Set G)) : Q = G₁ ∨ Q = G₂ := by
  have h12 : G₁ ≤ centralizer (G₂ : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  have h21 : G₂ ≤ centralizer (G₁ : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp (by rw [commutator_comm]; exact hc)
  have hn₁ : G₁ ⊔ G₂ ≤ normalizer (G₁ : Set G) :=
    sup_le le_normalizer (h21.trans (centralizer_le_normalizer _))
  have hn₂ : G₁ ⊔ G₂ ≤ normalizer (G₂ : Set G) :=
    sup_le (h12.trans (centralizer_le_normalizer _)) le_normalizer
  by_cases hne₁ : ⁅Q, G₁⁆ = ⊥
  · by_cases hne₂ : ⁅Q, G₂⁆ = ⊥
    · exfalso
      apply not_le_centralizer_self_of_quasisimple hQ
      intro q hq
      have hq1 := (commutator_eq_bot_iff_le_centralizer).mp hne₁ hq
      have hq2 := (commutator_eq_bot_iff_le_centralizer).mp hne₂ hq
      have hcen := mem_centralizer_sup (A := G₁) (B := G₂) (y := q)
        (fun a ha => mem_centralizer_iff.mp hq1 a ha) (fun b hb => mem_centralizer_iff.mp hq2 b hb)
      rw [mem_centralizer_iff] at hcen ⊢
      exact fun z hz => hcen z (hQle hz)
    · exact Or.inr (eq_of_quasisimple_of_commutator_ne_bot h₂ hQ (hQle.trans hn₂)
        (le_sup_right.trans hQn) hne₂)
  · exact Or.inl (eq_of_quasisimple_of_commutator_ne_bot h₁ hQ (hQle.trans hn₁)
      (le_sup_left.trans hQn) hne₁)

@[expose] def diagHom (Q₁ : Subgroup G) (t : G)
    (hc : ∀ u ∈ Q₁, ∀ v ∈ Q₁, v * (t * u * t⁻¹) = t * u * t⁻¹ * v) : Q₁ →* G where
  toFun u := u * (t * u * t⁻¹)
  map_one' := by simp
  map_mul' u v := by
    simp only [coe_mul]
    have h := hc u u.2 v v.2
    calc (u : G) * v * (t * (u * v) * t⁻¹) = u * (v * (t * u * t⁻¹)) * (t * v * t⁻¹) := by
          group
      _ = u * (t * u * t⁻¹ * v) * (t * v * t⁻¹) := by rw [h]
      _ = u * (t * u * t⁻¹) * (v * (t * v * t⁻¹)) := by group

theorem diagHom_apply {Q₁ : Subgroup G} {t : G}
    (hc : ∀ u ∈ Q₁, ∀ v ∈ Q₁, v * (t * u * t⁻¹) = t * u * t⁻¹ * v) (u : Q₁) :
    diagHom Q₁ t hc u = u * (t * u * t⁻¹) := rfl

theorem diagHom_mem_centralizer {Q₁ : Subgroup G} {t : G}
    (hc : ∀ u ∈ Q₁, ∀ v ∈ Q₁, v * (t * u * t⁻¹) = t * u * t⁻¹ * v) (ht : t * t = 1) (u : Q₁) :
    diagHom Q₁ t hc u ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_singleton_iff, diagHom_apply]
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h := hc u u.2 u u.2
  calc (u : G) * (t * u * t⁻¹) * t = t * u * t⁻¹ * u * t := by rw [h]
    _ = t * (u * (t * u * t⁻¹)) := by rw [ht']; group

theorem le_closure_sup_diag {Q₁ : Subgroup G} {t x : G}
    (hc : ∀ u ∈ Q₁, ∀ v ∈ Q₁, v * (t * u * t⁻¹) = t * u * t⁻¹ * v)
    (hQ₂ : CFSG.Open.IsQuasisimple (Q₁.map (MulAut.conj t).toMonoidHom))
    (hx : x ∈ Q₁ ⊔ Q₁.map (MulAut.conj t).toMonoidHom)
    (hxJ : x ∉ (diagHom Q₁ t hc).range ⊔
      centralizer ((Q₁ ⊔ Q₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    Q₁ ⊔ Q₁.map (MulAut.conj t).toMonoidHom ≤ closure {x} ⊔ (diagHom Q₁ t hc).range := by
  set Q₂ := Q₁.map (MulAut.conj t).toMonoidHom with hQ₂def
  set J := (diagHom Q₁ t hc).range with hJ
  set W := closure {x} ⊔ J with hW
  have hconj : ∀ q ∈ Q₂, ∃ p ∈ Q₁, t * p * t⁻¹ = q := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  have hcomm : ∀ u ∈ Q₁, ∀ v ∈ Q₂, u * v = v * u := by
    intro u hu v hv
    obtain ⟨p, hp, rfl⟩ := hconj v hv
    exact hc p hp u hu
  have hQ₁C : Q₁ ≤ centralizer (Q₂ : Set G) := fun u hu =>
    mem_centralizer_iff.mpr fun v hv => (hcomm u hu v hv).symm
  have hdiag : ∀ p ∈ Q₁, p * (t * p * t⁻¹) ∈ W := fun p hp =>
    mem_sup_right ⟨⟨p, hp⟩, rfl⟩
  have hx' : x ∈ (Q₁ : Set G) * (Q₂ : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right Q₁ Q₂ (hQ₁C.trans (centralizer_le_normalizer _))]
    exact hx
  obtain ⟨u, hu, v, hv, huv⟩ := hx'
  simp only at huv
  subst huv
  set y := (u * v)⁻¹ * (u * (t * u * t⁻¹)) with hy
  have hyQ₂ : y ∈ Q₂ := by
    have : y = v⁻¹ * (t * u * t⁻¹) := by rw [hy]; group
    rw [this]
    exact Q₂.mul_mem (Q₂.inv_mem hv) ⟨u, hu, rfl⟩
  have hyW : y ∈ W :=
    W.mul_mem (W.inv_mem (mem_sup_left (subset_closure rfl))) (hdiag u hu)
  have hyZ : y ∉ centralizer (Q₂ : Set G) := by
    intro hyc
    apply hxJ
    have hyM : y ∈ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) :=
      mem_centralizer_sup (fun a ha => hcomm a ha y hyQ₂)
        (fun b hb => mem_centralizer_iff.mp hyc b hb)
    have : u * v = (u * (t * u * t⁻¹)) * y⁻¹ := by rw [hy]; group
    rw [this]
    exact mul_mem (mem_sup_left ⟨⟨u, hu⟩, rfl⟩) (mem_sup_right (inv_mem hyM))
  have hfwd : ∀ q ∈ Q₂, ∀ w ∈ W ⊓ Q₂, q * w * q⁻¹ ∈ W ⊓ Q₂ := by
    rintro q hq w ⟨hwW, hwQ⟩
    refine ⟨?_, Q₂.mul_mem (Q₂.mul_mem hq hwQ) (Q₂.inv_mem hq)⟩
    obtain ⟨p, hp, rfl⟩ := hconj q hq
    have hpc : p * (t * p * t⁻¹ * w * (t * p * t⁻¹)⁻¹) =
        (t * p * t⁻¹ * w * (t * p * t⁻¹)⁻¹) * p :=
      hcomm p hp _ (Q₂.mul_mem (Q₂.mul_mem hq hwQ) (Q₂.inv_mem hq))
    have : t * p * t⁻¹ * w * (t * p * t⁻¹)⁻¹ =
        (p * (t * p * t⁻¹)) * w * (p * (t * p * t⁻¹))⁻¹ := by
      calc t * p * t⁻¹ * w * (t * p * t⁻¹)⁻¹
          = (t * p * t⁻¹ * w * (t * p * t⁻¹)⁻¹ * p) * p⁻¹ := by group
        _ = (p * (t * p * t⁻¹ * w * (t * p * t⁻¹)⁻¹)) * p⁻¹ := by rw [hpc]
        _ = (p * (t * p * t⁻¹)) * w * (p * (t * p * t⁻¹))⁻¹ := by group
    rw [this]
    exact W.mul_mem (W.mul_mem (hdiag p hp) hwW) (W.inv_mem (hdiag p hp))
  have hnorm : Q₂ ≤ normalizer ((W ⊓ Q₂ : Subgroup G) : Set G) := by
    intro q hq
    rw [mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hfwd q hq w hw, fun hw => ?_⟩
    have := hfwd q⁻¹ (Q₂.inv_mem hq) _ hw
    simpa [mul_assoc] using this
  have hQ₂W : Q₂ ≤ W := by
    have := eq_of_le_of_not_le_centralizer hQ₂ inf_le_right hnorm
      (fun h => hyZ (h ⟨hyW, hyQ₂⟩))
    rw [← this]
    exact inf_le_left
  refine sup_le (fun p hp => ?_) hQ₂W
  have : p = (p * (t * p * t⁻¹)) * (t * p * t⁻¹)⁻¹ := by group
  rw [this]
  exact W.mul_mem (hdiag p hp) (W.inv_mem (hQ₂W ⟨p, hp, rfl⟩))

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
