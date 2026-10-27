module

public import CFSG.GH74.AS16.E2.Outer2

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.LiteratureLocal.TightCommuting CFSG.ABGLocalTools
open CFSG.GH74.E2 hiding Hyp
open CFSG.GH74.AS16 (Pair LNormal InDelta lemma1642_one lemma1642_three lemma1642_four
  lemma1652_one delta_nonempty inDelta_rightConjugate conjugate_centralizer
  conjugate_centralizer_singleton isCompIn_conj conjugate_eq_self_iff zpow_eq_one_or_self)
open CFSG.GH74.Uniqueness (S_CorZD)

section Finish

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem Cfg.central_of_unique (h : Cfg G T z L) {s : G} (hsQ : s ∈ (T : Subgroup G) ⊓ L)
    (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1)
    (hsc : ∀ q ∈ (T : Subgroup G) ⊓ L, q * s = s * q)
    (hsu : ∀ a ∈ (T : Subgroup G) ⊓ L, (∀ q ∈ (T : Subgroup G) ⊓ L, q * a = a * q) → a ^ 2 = 1 →
      a = 1 ∨ a = s) : ∀ t ∈ (T : Subgroup G), t * s = s * t := by
  intro t ht
  have htN : t ∈ normalizer (L : Set G) := h.le_normalizer ht
  have htN' : t⁻¹ ∈ normalizer (L : Set G) := (normalizer (L : Set G)).inv_mem htN
  have hmem : t * s * t⁻¹ ∈ (T : Subgroup G) ⊓ L :=
    ⟨(T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hsQ.1) ((T : Subgroup G).inv_mem ht),
      (mem_normalizer_iff.1 htN s).1 hsQ.2⟩
  have hc : ∀ q ∈ (T : Subgroup G) ⊓ L, q * (t * s * t⁻¹) = (t * s * t⁻¹) * q := by
    intro q hq
    have hq' : t⁻¹ * q * t ∈ (T : Subgroup G) ⊓ L := by
      refine ⟨(T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem ht) hq.1) ht, ?_⟩
      have := (mem_normalizer_iff.1 htN' q).1 hq.2
      simpa using this
    have h1 := hsc _ hq'
    calc q * (t * s * t⁻¹) = t * ((t⁻¹ * q * t) * s) * t⁻¹ := by group
      _ = t * (s * (t⁻¹ * q * t)) * t⁻¹ := by rw [h1]
      _ = (t * s * t⁻¹) * q := by group
  have hsq : (t * s * t⁻¹) ^ 2 = 1 := by
    calc (t * s * t⁻¹) ^ 2 = t * s ^ 2 * t⁻¹ := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hs2]; group
  rcases hsu _ hmem hc hsq with h1 | h1
  · exfalso
    apply hs1
    have : s = t⁻¹ * (t * s * t⁻¹) * t := by group
    rw [this, h1]
    group
  · calc t * s = (t * s * t⁻¹) * t := by group
      _ = s * t := by rw [h1]

theorem Cfg.finish (h : Cfg G T z L) (hterm : GLS.IsTerminalPair 2 z L) (hZ : center ↥L = ⊥)
    (hR3 : Rank3Sub L) (hSy : OuterSylow L ((T : Subgroup G) ⊓ L))
    {K' R : Subgroup G} (hK' : InDelta (centralizer (L : Set G)) K')
    (hR : IsSylowOf 2 R (K' ⊓ normalizer (centralizer (L : Set G) : Set G)))
    (hRT : R ≤ (T : Subgroup G)) {x : G} (hxR : x ∈ R) (hx1 : x ≠ 1)
    (hxZ : ∀ t ∈ (T : Subgroup G), t * x = x * t)
    (hTC : ∀ g : G, K' = rightConjugate (centralizer (L : Set G)) g →
      g ∈ normalizer ((T : Subgroup G) : Set G) →
      IsCyclic ↥((T : Subgroup G) ⊓ centralizer (L : Set G))) : False := by
  classical
  have hstd := h.isStandard' hterm hZ hR3
  have hN := h.lNormal
  have hZ' := center_trivial hZ
  have hRD : R ⊓ centralizer (L : Set G) = ⊥ :=
    (lemma1642_one h.pair hN hstd hK' hR hRT).inf_eq_bot
  obtain ⟨g, hgK, hTg⟩ := lemma1642_four h.pair hN hstd hK'
  have hgT : g ∈ normalizer ((T : Subgroup G) : Set G) :=
    lemma1652_one hstd hK' hR ⟨x, hxR, hx1, hxZ⟩ hTg
  have hTCc := hTC g hgK hgT
  have hKT : K' ⊓ (T : Subgroup G) = R := lemma1642_three h.pair hN hstd hR hRT
  obtain ⟨s, hsQ, hs1, hs2, hsc, hsu, hcent, a, haL, b, hbL, ha3, hb3, has, hbs, hab⟩ :=
    hSy.exists_s
  have hsT := h.central_of_unique hsQ hs1 hs2 hsc hsu
  have hzT : z ∈ (T : Subgroup G) := h.pair.mem_sylow
  have hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t := h.pair.central
  have hzD : z ∈ centralizer (L : Set G) := h.pair.mem_centralizer
  have hzo : orderOf z = 2 := h.pair.orderOf_eq
  have hz2 : z ^ 2 = 1 := hzo ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzo
    omega
  have hzTC : z ∈ (T : Subgroup G) ⊓ centralizer (L : Set G) := ⟨hzT, hzD⟩
  have hzL : ∀ l ∈ L, l * z = z * l := fun l hl => mem_centralizer_iff.1 hzD l hl
  have hszc : s * z = z * s := hzL s hsQ.2
  have hzNL : z ∉ L := fun hzl => hz1 (hZ' z hzl hzD)
  have hzsNL : z * s ∉ L := by
    intro hzs
    apply hzNL
    have : z = (z * s) * s⁻¹ := by group
    rw [this]
    exact L.mul_mem hzs (L.inv_mem hsQ.2)
  have hgT' : g⁻¹ ∈ normalizer ((T : Subgroup G) : Set G) :=
    (normalizer ((T : Subgroup G) : Set G)).inv_mem hgT
  have hconjT : ∀ w ∈ (T : Subgroup G), g * w * g⁻¹ ∈ (T : Subgroup G) ∧
      g⁻¹ * w * g ∈ (T : Subgroup G) := by
    intro w hw
    refine ⟨(mem_normalizer_iff.1 hgT w).1 hw, ?_⟩
    have := (mem_normalizer_iff.1 hgT' w).1 hw
    simpa using this
  have hconjZ : ∀ w ∈ (T : Subgroup G), (∀ t ∈ (T : Subgroup G), t * w = w * t) →
      (∀ t ∈ (T : Subgroup G), t * (g * w * g⁻¹) = (g * w * g⁻¹) * t) ∧
      (∀ t ∈ (T : Subgroup G), t * (g⁻¹ * w * g) = (g⁻¹ * w * g) * t) := by
    intro w hw hwc
    constructor
    · intro t ht
      have h1 := hwc _ (hconjT t ht).2
      calc t * (g * w * g⁻¹) = g * ((g⁻¹ * t * g) * w) * g⁻¹ := by group
        _ = g * (w * (g⁻¹ * t * g)) * g⁻¹ := by rw [h1]
        _ = (g * w * g⁻¹) * t := by group
    · intro t ht
      have h1 := hwc _ (hconjT t ht).1
      calc t * (g⁻¹ * w * g) = g⁻¹ * ((g * t * g⁻¹) * w) * g := by group
        _ = g⁻¹ * (w * (g * t * g⁻¹)) * g := by rw [h1]
        _ = (g⁻¹ * w * g) * t := by group
  have hZT : ∀ w ∈ (T : Subgroup G), (∀ t ∈ (T : Subgroup G), t * w = w * t) → w ^ 2 = 1 →
      w = 1 ∨ w = z ∨ w = s ∨ w = z * s := by
    intro w hw hwc hw2
    have hwN : w ∈ normalizer (L : Set G) := h.le_normalizer hw
    obtain ⟨a₀, ha₀Q, ha₀c, ha₀D⟩ := hcent w hwN (fun q hq => (hwc q hq.1).symm)
    set d : G := a₀⁻¹ * w with hd
    have hdT : d ∈ (T : Subgroup G) :=
      (T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem ha₀Q.1) hw
    have hdTC : d ∈ (T : Subgroup G) ⊓ centralizer (L : Set G) := ⟨hdT, ha₀D⟩
    have hwd : w = a₀ * d := by rw [hd]; group
    have hcomm : a₀ * d = d * a₀ := mem_centralizer_iff.1 ha₀D a₀ ha₀Q.2
    have hcm : Commute a₀ d := hcomm
    have h1 : a₀ ^ 2 * d ^ 2 = 1 := by
      rw [← hcm.mul_pow, ← hwd]
      exact hw2
    have ha₀2 : a₀ ^ 2 = 1 := by
      have e1 : a₀ ^ 2 = (d ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
      apply hZ' _ (L.pow_mem ha₀Q.2 2)
      rw [e1]
      exact (centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).pow_mem ha₀D 2)
    have hd2 : d ^ 2 = 1 := by rw [ha₀2, one_mul] at h1; exact h1
    have hd' : d = 1 ∨ d = z := by
      have := cyclic_pow_two_eq_one (X := ↥((T : Subgroup G) ⊓ centralizer (L : Set G)))
        (z := ⟨z, hzTC⟩) (c := ⟨d, hdTC⟩) (Subtype.ext (by simpa using hz2))
        (fun h1 => hz1 (congrArg Subtype.val h1)) (Subtype.ext (by simpa using hd2))
      rcases this with h1 | h1
      · exact Or.inl (congrArg Subtype.val h1)
      · exact Or.inr (congrArg Subtype.val h1)
    rcases hsu a₀ ha₀Q ha₀c ha₀2 with h2 | h2 <;> rcases hd' with h3 | h3
    · left; rw [hwd, h2, h3]; group
    · right; left; rw [hwd, h2, h3]; group
    · right; right; left; rw [hwd, h2, h3]; group
    · right; right; right; rw [hwd, h2, h3, hszc]
  set u : G := g⁻¹ * z * g with hu
  have huT : u ∈ (T : Subgroup G) := (hconjT z hzT).2
  have huK : u ∈ K' := by
    rw [hgK, mem_rightConjugate_iff]
    have : g * u * g⁻¹ = z := by rw [hu]; group
    rw [this]
    exact hzD
  have huR : u ∈ R := by rw [← hKT]; exact ⟨huK, huT⟩
  have huo : orderOf u = 2 := by
    rw [hu]
    calc orderOf (g⁻¹ * z * g) = orderOf ((MulAut.conj g⁻¹) z) := by simp
      _ = orderOf z := (MulAut.conj g⁻¹).orderOf_eq z
      _ = 2 := hzo
  have hu2 : u ^ 2 = 1 := huo ▸ pow_orderOf_eq_one u
  have huz : u ≠ z := by
    intro hu'
    have : z ∈ R ⊓ centralizer (L : Set G) := ⟨by rw [← hu']; exact huR, hzD⟩
    rw [hRD, mem_bot] at this
    exact hz1 this
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at huo
    omega
  have huc := (hconjZ z hzT hzc).2
  have huS : u = s ∨ u = z * s := by
    rcases hZT u huT huc hu2 with h1 | h1 | h1 | h1
    · exact absurd h1 hu1
    · exact absurd h1 huz
    · exact Or.inl h1
    · exact Or.inr h1
  have hcomu : ∀ c ∈ L, c * s = s * c → c * u = u * c := by
    intro c hc hcs
    have hcz : c * z = z * c := hzL c hc
    rcases huS with h1 | h1
    · rw [h1]
      exact hcs
    · rw [h1]
      calc c * (z * s) = (c * z) * s := by group
        _ = (z * c) * s := by rw [hcz]
        _ = z * (c * s) := by group
        _ = z * (s * c) := by rw [hcs]
        _ = (z * s) * c := by group
  have hcmem : ∀ c ∈ L, orderOf c = 3 → c * s = s * c → g * c * g⁻¹ ∈ L := by
    intro c hc hc3 hcs
    have hrD : (g⁻¹)⁻¹ * u * g⁻¹ ∈ centralizer (L : Set G) := by
      have : (g⁻¹)⁻¹ * u * g⁻¹ = z := by rw [hu]; group
      rw [this]
      exact hzD
    have := h.three_mem_conj hterm hZ' hR3 (g := g⁻¹) (r := u) huo hrD hc3 (hcomu c hc hcs)
    simpa using this
  have hga := hcmem a haL ha3 has
  have hgb := hcmem b hbL hb3 hbs
  have hgsL : g * s * g⁻¹ ∈ L := by
    have e : g * s * g⁻¹ = ((g * a * g⁻¹) * (g * b * g⁻¹)) ^ 3 := by
      rw [← hab]
      have e1 : (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      rw [e1, conj_pow]
    rw [e]
    exact L.pow_mem (L.mul_mem hga hgb) 3
  have hgsT : g * s * g⁻¹ ∈ (T : Subgroup G) := (hconjT s hsQ.1).1
  have hgsc := (hconjZ s hsQ.1 hsT).1
  have hgs2 : (g * s * g⁻¹) ^ 2 = 1 := by
    calc (g * s * g⁻¹) ^ 2 = g * s ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hs2]; group
  have hgs1 : g * s * g⁻¹ ≠ 1 := by
    intro h1
    apply hs1
    have : s = g⁻¹ * (g * s * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hgs : g * s * g⁻¹ = s := by
    rcases hZT _ hgsT hgsc hgs2 with h1 | h1 | h1 | h1
    · exact absurd h1 hgs1
    · exact absurd (by rw [← h1]; exact hgsL) hzNL
    · exact h1
    · exact absurd (by rw [← h1]; exact hgsL) hzsNL
  have hz₂T : g * z * g⁻¹ ∈ (T : Subgroup G) := (hconjT z hzT).1
  have hz₂c := (hconjZ z hzT hzc).1
  have hz₂2 : (g * z * g⁻¹) ^ 2 = 1 := by
    calc (g * z * g⁻¹) ^ 2 = g * z ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hz2]; group
  have hz₂z : g * z * g⁻¹ ≠ z := by
    intro h1
    apply huz
    show g⁻¹ * z * g = z
    calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [h1]
      _ = z := by group
  have hz₂S : g * z * g⁻¹ = z * s := by
    rcases hZT _ hz₂T hz₂c hz₂2 with h1 | h1 | h1 | h1
    · exfalso
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · exact absurd h1 hz₂z
    · exfalso
      apply hzNL
      have e : z = s := by
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = g⁻¹ * (g * s * g⁻¹) * g := by rw [h1, hgs]
          _ = s := by group
      rw [e]
      exact hsQ.2
    · exact h1
  have hgzs : g * (z * s) * g⁻¹ = z := by
    calc g * (z * s) * g⁻¹ = (g * z * g⁻¹) * (g * s * g⁻¹) := by group
      _ = (z * s) * s := by rw [hz₂S, hgs]
      _ = z * s ^ 2 := by rw [pow_two, mul_assoc]
      _ = z := by rw [hs2]; group
  set N' : Subgroup G := normalizer ((T : Subgroup G) : Set G) with hN'
  have hodd : ¬ 2 ∣ ((T : Subgroup G).subgroupOf N').index := by
    have hTle : (T : Subgroup G) ≤ N' := Subgroup.le_normalizer
    have hSyl' := CFSG.ABGLocalTools.IsSylowOf.of_le (isSylowOf_top T) hTle le_top
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hSyl'
    exact hSyl'.2.2
  set m : ℕ := ((T : Subgroup G).subgroupOf N').index with hm
  have hgm : g ^ m ∈ (T : Subgroup G) := by
    have h1 : ((⟨g, hgT⟩ : N') : N' ⧸ (T : Subgroup G).subgroupOf N') ^
        Nat.card (N' ⧸ (T : Subgroup G).subgroupOf N') = 1 := pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    have h2 : ((⟨g, hgT⟩ : N') ^ m : N') ∈ (T : Subgroup G).subgroupOf N' := h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hφ : ∀ k : ℕ, (MulAut.conj g ^ (2 * k + 1)) z = z * s := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, pow_one]
      exact hz₂S
    | succ k ih =>
      have e : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      have h2 : (MulAut.conj g ^ 2) z = z := by
        rw [pow_two, MulAut.mul_apply]
        have e1 : (MulAut.conj g) z = z * s := hz₂S
        rw [e1]
        simpa [MulAut.conj_apply] using hgzs
      rw [e, pow_add, MulAut.mul_apply, h2]
      exact ih
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = 2 * k + 1 := ⟨m / 2, by omega⟩
  have h1 : (MulAut.conj g ^ m) z = z := by
    have hc : g ^ m * z = z * g ^ m := hzc _ hgm
    have e1 : (MulAut.conj g ^ m) z = g ^ m * z * (g ^ m)⁻¹ := by
      rw [← map_pow]
      exact MulAut.conj_apply (g ^ m) z
    rw [e1, hc]
    group
  rw [hk, hφ k] at h1
  apply hs1
  have : z * s = z * 1 := by rw [h1, mul_one]
  exact mul_left_cancel this

end Finish

end CFSG.GH74.AS16.E2
