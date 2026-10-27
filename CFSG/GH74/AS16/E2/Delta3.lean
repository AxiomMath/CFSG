module

public import CFSG.GH74.AS16.E2.Std
public import CFSG.GH74.AS16.E2.Data2
public import CFSG.GH74.AS16.Notation1641
public import CFSG.GH74.AS16.DeltaNonempty

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.LiteratureLocal.TightCommuting CFSG.ABGLocalTools
open CFSG.GH74.E2 hiding Hyp
open CFSG.GH74.AS16 (Pair LNormal InDelta lemma1642_one delta_nonempty inDelta_rightConjugate
  conjugate_centralizer conjugate_centralizer_singleton isCompIn_conj conjugate_eq_self_iff
  zpow_eq_one_or_self)
open CFSG.GH74.Uniqueness (S_CorZD)

section Pure

variable {G : Type*} [Group G]

theorem eq_one_or_of_card_two {X : Subgroup G} (hcard : Nat.card X = 2) {z : G} (hz : z ∈ X)
    (hz1 : z ≠ 1) : ∀ x ∈ X, x = 1 ∨ x = z := by
  have hfin : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hord : orderOf z = 2 := by
    have hdvd : orderOf z ∣ 2 := hcard ▸ Subgroup.orderOf_dvd_natCard X hz
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  have hz2 : z ^ 2 = 1 := hord ▸ pow_orderOf_eq_one z
  have hX : zpowers z = X := by
    refine Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 hz) ?_
    rw [Nat.card_zpowers, hord, hcard]
  intro x hx
  rw [← hX] at hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  exact zpow_eq_one_or_self hz2 k

theorem subset_pair_of_cent3 {L R : Subgroup G} {v j : G}
    (hvL : v ∈ L) (hjD : j ∈ centralizer (L : Set G)) (hrR : v * j ∈ R)
    (hRD : R ⊓ centralizer (L : Set G) = ⊥)
    (hdec : ∀ ρ ∈ R, ∃ a ∈ L, ∃ d ∈ centralizer (L : Set G), ρ = a * d)
    (hcomm : ∀ ρ ∈ R, ∀ c ∈ L, orderOf c = 3 → c * v = v * c → ρ * c = c * ρ)
    (hcent3 : ∀ a ∈ L,
      (∀ c ∈ L, orderOf c = 3 → c * v = v * c → a * c = c * a) → a = 1 ∨ a = v) :
    ∀ ρ ∈ R, ρ = 1 ∨ ρ = v * j := by
  intro ρ hρ
  obtain ⟨a, haL, d, hdD, rfl⟩ := hdec ρ hρ
  have hdc : ∀ c ∈ L, c * d = d * c := fun c hc => mem_centralizer_iff.1 hdD c hc
  have hnot : ∀ c ∈ L, orderOf c = 3 → c * v = v * c → a * c = c * a := by
    intro c hc hc3 hcv
    have h1 := hcomm _ hρ c hc hc3 hcv
    have h2 : a * c * d = c * a * d := by
      calc a * c * d = a * (c * d) := by group
        _ = a * (d * c) := by rw [hdc c hc]
        _ = (a * d) * c := by group
        _ = c * (a * d) := h1
        _ = c * a * d := by group
    exact mul_right_cancel h2
  rcases hcent3 a haL hnot with h | h
  · left
    have hmem : a * d ∈ R ⊓ centralizer (L : Set G) := ⟨hρ, by rw [h, one_mul]; exact hdD⟩
    rw [hRD, Subgroup.mem_bot] at hmem
    exact hmem
  · right
    have hdj : v * d = d * v := hdc v hvL
    have hjv : v * j = j * v := mem_centralizer_iff.1 hjD v hvL
    have hmem : (v * d) * (v * j)⁻¹ ∈ R ⊓ centralizer (L : Set G) := by
      refine ⟨R.mul_mem (h ▸ hρ) (R.inv_mem hrR), ?_⟩
      have e : (v * d) * (v * j)⁻¹ = d * j⁻¹ := by
        calc (v * d) * (v * j)⁻¹ = v * (d * j⁻¹) * v⁻¹ := by group
          _ = (v * (d * j⁻¹)) * v⁻¹ := rfl
          _ = d * j⁻¹ := by
            have : v * (d * j⁻¹) = (d * j⁻¹) * v := by
              have hj' : v * j⁻¹ = j⁻¹ * v := by
                have : Commute v j := hjv
                exact this.inv_right.eq
              calc v * (d * j⁻¹) = (v * d) * j⁻¹ := by group
                _ = (d * v) * j⁻¹ := by rw [hdj]
                _ = d * (v * j⁻¹) := by group
                _ = d * (j⁻¹ * v) := by rw [hj']
                _ = (d * j⁻¹) * v := by group
            rw [this]; group
      rw [e]
      exact (centralizer (L : Set G)).mul_mem hdD ((centralizer (L : Set G)).inv_mem hjD)
    rw [hRD, Subgroup.mem_bot] at hmem
    rw [h]
    exact mul_inv_eq_one.1 hmem

theorem card_eq_two_of_cent [Finite G] {TC R : Subgroup G} {z v j : G}
    (hcard : Nat.card ↥(TC ⊓ centralizer (R : Set G)) = 2)
    (hz : z ∈ TC ⊓ centralizer (R : Set G)) (hz1 : z ≠ 1)
    (hj : j ∈ TC ⊓ centralizer (R : Set G))
    (hzTC : ∀ c ∈ TC, c * z = z * c) (hvc : ∀ c ∈ TC, c * v = v * c)
    (hRsub : ∀ ρ ∈ R, ρ = 1 ∨ ρ = v * j) : Nat.card ↥TC = 2 := by
  have hjz : j = 1 ∨ j = z := eq_one_or_of_card_two hcard hz hz1 j hj
  have hjc : ∀ c ∈ TC, c * j = j * c := by
    intro c hc
    rcases hjz with h | h
    · rw [h]; simp
    · rw [h]; exact hzTC c hc
  have hle : TC ≤ centralizer (R : Set G) := by
    intro c hc
    rw [mem_centralizer_iff]
    intro ρ hρ
    rcases hRsub ρ hρ with h | h
    · rw [h]; simp
    · rw [h]
      calc v * j * c = v * (j * c) := by group
        _ = v * (c * j) := by rw [hjc c hc]
        _ = (v * c) * j := by group
        _ = (c * v) * j := by rw [hvc c hc]
        _ = c * (v * j) := by group
  have : TC ⊓ centralizer (R : Set G) = TC := inf_eq_left.2 hle
  rw [this] at hcard
  exact hcard

end Pure

section Conj

variable {G : Type} [Group G]

theorem exists_delta_sylow_le_T [Finite G] {T : Sylow 2 G} {z : G} {L K' : Subgroup G}
    (hp : Pair T z L) (hN : LNormal z L) (hS : IsStandardSubgroup L)
    (hK' : InDelta (centralizer (L : Set G)) K') :
    ∃ K'' R : Subgroup G, InDelta (centralizer (L : Set G)) K'' ∧
      IsSylowOf 2 R (K'' ⊓ normalizer (centralizer (L : Set G) : Set G)) ∧
      R ≤ (T : Subgroup G) := by
  set C : Subgroup G := centralizer (L : Set G) with hC
  obtain ⟨R₀, hR₀⟩ := exists_isSylowOf 2 (K' ⊓ normalizer (C : Set G))
  have hH : normalizer (C : Set G) = normalizer (L : Set G) := hS.2.2.2.1
  have hR₀H : R₀ ≤ normalizer (L : Set G) := hH ▸ (hR₀.le.trans inf_le_right)
  obtain ⟨T', hT', hR₀T'⟩ := exists_isSylowOf_ge hR₀H hR₀.isPGroup
  obtain ⟨k, hk, hkconj⟩ := (hp.isSylowOf_normalizer hN).exists_mem_conj hT'
  have hkC : k ∈ normalizer (C : Set G) := hH ▸ hk
  have hRle : rightConjugate R₀ k ≤ (T : Subgroup G) := by
    intro y hy
    have hy' : k * y * k⁻¹ ∈ R₀ := (mem_rightConjugate_iff R₀ k y).mp hy
    have h1 := (hkconj (k * y * k⁻¹)).mp (hR₀T' hy')
    have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    rw [e] at h1
    exact h1
  have hN' : rightConjugate (normalizer (C : Set G)) k = normalizer (C : Set G) :=
    (rightConjugate_eq_self_iff _ k).mpr (le_normalizer hkC)
  have hinfeq : rightConjugate (K' ⊓ normalizer (C : Set G)) k =
      rightConjugate K' k ⊓ normalizer (C : Set G) := by rw [rightConjugate_inf, hN']
  refine ⟨rightConjugate K' k, rightConjugate R₀ k, inDelta_rightConjugate hK' hkC, ?_, hRle⟩
  rw [← hinfeq]
  refine isSylowOf_of_card (rightConjugate_mono k hR₀.le) ?_
  rw [rightConjugate_card, rightConjugate_card, hR₀.card_eq]

theorem map_conj_centralizer (L : Subgroup G) (g : G) :
    (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have h1 := mem_centralizer_iff.1 hy l hl
    show g * l * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * l * g⁻¹)
    calc g * l * g⁻¹ * (g * y * g⁻¹) = g * (l * y) * g⁻¹ := by group
      _ = g * (y * l) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * (g * l * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, mem_centralizer_iff.2 fun l hl => ?_,
      by show g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩
    have := mem_centralizer_iff.1 hx (g * l * g⁻¹) ⟨l, hl, rfl⟩
    calc l * (g⁻¹ * x * g) = g⁻¹ * ((g * l * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * l * g⁻¹)) * g := by rw [this]
      _ = (g⁻¹ * x * g) * l := by group

theorem map_conj_eq_conjugate (H : Subgroup G) (g : G) :
    H.map (MulAut.conj g).toMonoidHom = conjugate H g⁻¹ := by
  simp [conjugate]

end Conj

section Main

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem Cfg.card_tC_eq_two (hZD : S_CorZD) (h : Cfg G T z L)
    (hterm : GLS.IsTerminalPair 2 z L) (hZ : center ↥L = ⊥) (hL3 : Local3Sub L)
    (hinn : InnerAction (T : Subgroup G) L) :
    Nat.card ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) = 2 := by
  classical
  have he := h.quasithin
  have hZ' := center_trivial hZ
  have hstd := h.isStandard hterm hZ hL3
  have hN := h.lNormal
  obtain ⟨K₀, hK₀⟩ := delta_nonempty hZD h.hyp.simple h.hyp.nonabelian hstd
  obtain ⟨K', R, hK', hR, hRT⟩ := exists_delta_sylow_le_T h.pair hN hstd hK₀
  have h1 := lemma1642_one h.pair hN hstd hK' hR hRT
  have hdec := h.decomp_of_inner hZ hinn
  obtain ⟨⟨g, hg⟩, hne, hev⟩ := hK'
  have hRne : R ≠ ⊥ := ne_bot_of_isSylowOf_even hR hev
  have hRK' : R ≤ K' := hR.le.trans inf_le_left
  obtain ⟨r, hrR, hr2⟩ : ∃ r ∈ R, orderOf r = 2 := by
    have h2 : 2 ∣ Nat.card R := by
      rcases hR.isPGroup.card_eq_or_dvd with h1 | h'
      · exact absurd (Subgroup.eq_bot_of_card_eq R h1) hRne
      · exact h'
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 2 h2
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  have hr1 : r ≠ 1 := by
    intro h'
    rw [h', orderOf_one] at hr2
    omega
  have hr2' : r ^ 2 = 1 := hr2 ▸ pow_orderOf_eq_one r
  obtain ⟨v, hvTL, j, hjTC, hrvj⟩ := hdec r (hRT hrR)
  have hvL : v ∈ L := hvTL.2
  have hjD : j ∈ centralizer (L : Set G) := hjTC.2
  have hvj : v * j = j * v := mem_centralizer_iff.1 hjD v hvL
  have hRD : R ⊓ centralizer (L : Set G) = ⊥ := h1.inf_eq_bot
  have hv2 : v ^ 2 = 1 := by
    have hc : Commute v j := hvj
    have e : v ^ 2 * j ^ 2 = 1 := by rw [← hc.mul_pow 2, ← hrvj]; exact hr2'
    have e1 : v ^ 2 = (j ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left e
    have h2L : v ^ 2 ∈ L := L.pow_mem hvL 2
    have h2C : v ^ 2 ∈ centralizer (L : Set G) := by
      rw [e1]
      exact (centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).pow_mem hjD 2)
    exact hZ' _ h2L h2C
  have hv1 : v ≠ 1 := by
    intro hv
    have : r ∈ R ⊓ centralizer (L : Set G) := ⟨hrR, by rw [hrvj, hv, one_mul]; exact hjD⟩
    rw [hRD, Subgroup.mem_bot] at this
    exact hr1 this
  have hvo : orderOf v = 2 := orderOf_eq_prime hv2 hv1
  set L' : Subgroup G := L.map (MulAut.conj g).toMonoidHom with hL'
  have hK'C : K' = centralizer (L' : Set G) := by
    rw [hg, hL']
    exact map_conj_centralizer L g
  have hrL' : r ∈ centralizer (L' : Set G) := by rw [← hK'C]; exact hRK' hrR
  have hrK : r ∈ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]; exact hRK' hrR
  obtain ⟨y, hyD, hyr⟩ := hrK
  have hy2 : orderOf y = 2 := by
    rw [← hr2, ← hyr]
    exact ((MulAut.conj g).orderOf_eq y).symm
  have hcomp : IsCompCen r L' := by
    have h3 := isCompIn_conj (hterm.2.2.2 y hy2 hyD) g⁻¹
    rw [conjugate_centralizer_singleton, ← map_conj_eq_conjugate] at h3
    have e : g⁻¹⁻¹ * y * g⁻¹ = r := by
      rw [inv_inv]
      exact hyr
    rw [e] at h3
    exact h3
  have hcenN : ∀ x : G, x * r = r * x → x ∈ normalizer (L' : Set G) := by
    intro x hx
    have hxC : x ∈ Cen r := mem_Cen'.2 hx
    have hc := conjugate_eq_of_unique hcomp
      (fun K'' hK'' => h.uniq r hr2 K'' L' hK'' hcomp) hxC
    exact (conjugate_eq_self_iff L' x).1 hc
  have hZ'' : ∀ x ∈ L', x ∈ centralizer (L' : Set G) → x = 1 := by
    intro x hxL hxC
    obtain ⟨l, hl, rfl⟩ := hxL
    have hxK : (MulAut.conj g).toMonoidHom l ∈ K' := by rw [hK'C]; exact hxC
    rw [hg] at hxK
    obtain ⟨y', hy', hyx⟩ := hxK
    have hl1 : l ∈ centralizer (L : Set G) := by
      have : y' = l := (MulAut.conj g).injective hyx
      rw [← this]; exact hy'
    have := hZ' l hl hl1
    rw [this]; simp
  have hcl : ∀ c ∈ L, orderOf c = 3 → c * v = v * c → c ∈ L' := by
    intro c hcL hc3 hcv
    have hcj : c * j = j * c := mem_centralizer_iff.1 hjD c hcL
    have hcr : c * r = r * c := by
      rw [hrvj]
      calc c * (v * j) = (c * v) * j := by group
        _ = (v * c) * j := by rw [hcv]
        _ = v * (c * j) := by group
        _ = v * (j * c) := by rw [hcj]
        _ = (v * j) * c := by group
    exact mem_of_order_three he hr2 hrL' hZ'' (hL3.elemAb9_conj g) (hL3.inner3_conj g) hcenN hc3 hcr
  have hRsub : ∀ ρ ∈ R, ρ = 1 ∨ ρ = v * j := by
    refine subset_pair_of_cent3 hvL hjD (hrvj ▸ hrR) hRD ?_ ?_ (hL3.cent3 v hvL hvo)
    · intro ρ hρ
      obtain ⟨s, hs, c, hc, hρe⟩ := hdec ρ (hRT hρ)
      exact ⟨s, hs.2, c, hc.2, hρe⟩
    · intro ρ hρ c hcL hc3 hcv
      have hcL' := hcl c hcL hc3 hcv
      have hρC : ρ ∈ centralizer (L' : Set G) := by rw [← hK'C]; exact hRK' hρ
      exact (mem_centralizer_iff.1 hρC c hcL').symm
  have hRcard : Nat.card ↥R = 2 := by
    have hR' : R = zpowers r := by
      apply le_antisymm
      · intro ρ hρ
        rcases hRsub ρ hρ with h' | h'
        · rw [h']; exact one_mem _
        · rw [h', ← hrvj]; exact mem_zpowers r
      · exact (zpowers_le).2 hrR
    rw [hR', Nat.card_zpowers, hr2]
  set TC : Subgroup G := (T : Subgroup G) ⊓ centralizer (L : Set G) with hTC
  have hXcard : Nat.card ↥(TC ⊓ centralizer (R : Set G)) = 2 := by
    have e1 : Nat.card ↥(TC ⊓ centralizer (R : Set G)) = Nat.card ↥(TC ⊓ normalizer (K' : Set G)) := by
      rw [← h1.normalizer_eq_centralizer, h1.normalizer_eq]
    rw [e1, ← h1.card_eq, hRcard]
  have hzTC : z ∈ TC := ⟨h.pair.mem_sylow, h.pair.mem_centralizer⟩
  have hz1 : z ≠ 1 := by
    intro h'
    have := h.pair.orderOf_eq
    rw [h', orderOf_one] at this
    omega
  have hzX : z ∈ TC ⊓ centralizer (R : Set G) :=
    ⟨hzTC, mem_centralizer_iff.2 fun ρ hρ => h.pair.central ρ (hRT hρ)⟩
  have hjX : j ∈ TC ⊓ centralizer (R : Set G) := by
    refine ⟨hjTC, mem_centralizer_iff.2 fun ρ hρ => ?_⟩
    rcases hRsub ρ hρ with h' | h'
    · rw [h']; simp
    · rw [h']
      calc v * j * j = v * (j * j) := by group
        _ = (j * v) * j := by rw [← hvj]; group
        _ = j * (v * j) := by group
  refine card_eq_two_of_cent hXcard hzX hz1 hjX (fun c hc => h.pair.central c hc.1) ?_ hRsub
  intro c hc
  exact (mem_centralizer_iff.1 hc.2 v hvL).symm

end Main

end CFSG.GH74.AS16.E2
