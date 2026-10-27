module

public import CFSG.GH74.AS16.E2.OuterLift
public import CFSG.GH74.AS16.E2.Outer3

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.LiteratureLocal.TightCommuting CFSG.ABGLocalTools
open CFSG.GH74.E2 hiding Hyp
open CFSG.GH74.AS16 (Pair LNormal InDelta lemma1642_one lemma1642_three lemma1642_four
  lemma1652_one lemma1644_one delta_nonempty inDelta_rightConjugate conjugate_centralizer
  conjugate_centralizer_singleton isCompIn_conj conjugate_eq_self_iff zpow_eq_one_or_self)
open CFSG.GH74.Uniqueness (S_CorZD)

section Aux

variable {G : Type*} [Group G]

theorem conj_mem_centralizer' {L : Subgroup G} {x d : G} (hx : x ∈ normalizer (L : Set G))
    (hd : d ∈ centralizer (L : Set G)) : x * d * x⁻¹ ∈ centralizer (L : Set G) := by
  refine mem_centralizer_iff.2 fun l hl => ?_
  have hl' : x⁻¹ * l * x ∈ L := by
    have := (mem_normalizer_iff.1 ((normalizer (L : Set G)).inv_mem hx) l).1 hl
    simpa using this
  have h1 := mem_centralizer_iff.1 hd _ hl'
  calc l * (x * d * x⁻¹) = x * ((x⁻¹ * l * x) * d) * x⁻¹ := by group
    _ = x * (d * (x⁻¹ * l * x)) * x⁻¹ := by rw [h1]
    _ = (x * d * x⁻¹) * l := by group

theorem isCyclic_of_le_of_isCyclic {A B : Subgroup G} (hAB : A ≤ B) (hB : IsCyclic ↥B) :
    IsCyclic ↥A := by
  have := hB
  exact isCyclic_of_injective (Subgroup.inclusion hAB) (Subgroup.inclusion_injective hAB)

theorem eq_of_mul_eq_of_trivial {L : Subgroup G}
    (hZ : ∀ x ∈ L, x ∈ centralizer (L : Set G) → x = 1) {a v b j : G} (ha : a ∈ L) (hv : v ∈ L)
    (hb : b ∈ centralizer (L : Set G)) (hj : j ∈ centralizer (L : Set G)) (h : a * b = v * j) :
    a = v ∧ b = j := by
  have h1 : v⁻¹ * a = j * b⁻¹ := by
    calc v⁻¹ * a = v⁻¹ * (a * b) * b⁻¹ := by group
      _ = v⁻¹ * (v * j) * b⁻¹ := by rw [h]
      _ = j * b⁻¹ := by group
  have hL : v⁻¹ * a ∈ L := L.mul_mem (L.inv_mem hv) ha
  have hD : v⁻¹ * a ∈ centralizer (L : Set G) := by
    rw [h1]
    exact (centralizer (L : Set G)).mul_mem hj ((centralizer (L : Set G)).inv_mem hb)
  have h2 : v = a := inv_mul_eq_one.1 (hZ _ hL hD)
  refine ⟨h2.symm, ?_⟩
  rw [← h2] at h
  exact mul_left_cancel h

end Aux


section TC

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem Cfg.tC_cyclic_of_R (h : Cfg G T z L) (hterm : GLS.IsTerminalPair 2 z L)
    (hZ : center ↥L = ⊥) (hR3 : Rank3Sub L) {K' R : Subgroup G}
    (hK' : InDelta (centralizer (L : Set G)) K')
    (hR : IsSylowOf 2 R (K' ⊓ normalizer (centralizer (L : Set G) : Set G)))
    (hRT : R ≤ (T : Subgroup G)) (hRcyc : IsCyclic ↥R) :
    ∀ g : G, K' = rightConjugate (centralizer (L : Set G)) g →
      g ∈ normalizer ((T : Subgroup G) : Set G) →
      IsCyclic ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  intro g hgK hgT
  have hstd := h.isStandard' hterm hZ hR3
  have hN := h.lNormal
  have h1 := lemma1642_one h.pair hN hstd hK' hR hRT
  have hKT : K' ⊓ (T : Subgroup G) = R := lemma1642_three h.pair hN hstd hR hRT
  have hTg : rightConjugate (T : Subgroup G) g = T := (rightConjugate_eq_self_iff _ g).2 hgT
  have hRc : R = rightConjugate ((T : Subgroup G) ⊓ centralizer (L : Set G)) g := by
    rw [← hKT, hgK, rightConjugate_inf, hTg]
    exact inf_comm _ _
  have hcard : Nat.card ↥R = Nat.card ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
    rw [hRc, rightConjugate_card]
  obtain ⟨e⟩ := h1.equiv
  have hNcard : Nat.card ↥(((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
      normalizer (R : Set G)) = Nat.card ↥R := (Nat.card_congr e.toEquiv).symm
  have hNeq : ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ normalizer (R : Set G) =
      (T : Subgroup G) ⊓ centralizer (L : Set G) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hNcard, hcard])
  have := hRcyc
  have hcycN : IsCyclic ↥(((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
      normalizer (R : Set G)) := isCyclic_of_injective e.symm.toMonoidHom e.symm.injective
  rw [hNeq] at hcycN
  exact hcycN

end TC

section Main

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem Cfg.false_of_outer (hZD : S_CorZD) (h : Cfg G T z L) (hterm : GLS.IsTerminalPair 2 z L)
    (hZ : center ↥L = ⊥) (hR3 : Rank3Sub L) (hO : OuterSub L)
    (hSm : SmallTable L ((T : Subgroup G) ⊓ L)) (hSy : OuterSylow L ((T : Subgroup G) ⊓ L))
    (hcyc : IsCyclic ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) ∨ OuterCyc L) : False := by
  classical
  have hstd := h.isStandard' hterm hZ hR3
  have hN := h.lNormal
  have hZ' := center_trivial hZ
  obtain ⟨K', R, hK', hR, hRT, hinn⟩ := h.exists_inner_delta hZD hterm hZ hR3 hO
  have h1 := lemma1642_one h.pair hN hstd hK' hR hRT
  have hRD : R ⊓ centralizer (L : Set G) = ⊥ := h1.inf_eq_bot
  have hK'0 := hK'
  obtain ⟨⟨g₀, hg₀⟩, hne, hev⟩ := hK'0
  have hRK' : R ≤ K' := hR.le.trans inf_le_left
  have hRne : R ≠ ⊥ := ne_bot_of_isSylowOf_even hR hev
  have hmemK : ∀ x ∈ R, g₀⁻¹ * x * g₀ ∈ centralizer (L : Set G) := by
    intro x hx
    have hx' := hRK' hx
    rw [hg₀] at hx'
    exact mem_conj_centralizer hx'
  have hTle : (T : Subgroup G) ≤ normalizer (L : Set G) := h.le_normalizer
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
  obtain ⟨r₀, hr₀R, hr₀2⟩ : ∃ r ∈ R, orderOf r = 2 := by
    have h2 : 2 ∣ Nat.card R := by
      rcases hR.isPGroup.card_eq_or_dvd with h1 | h'
      · exact absurd (Subgroup.eq_bot_of_card_eq R h1) hRne
      · exact h'
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 2 h2
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  have hr₀1 : r₀ ≠ 1 := by
    intro h'
    rw [h', orderOf_one] at hr₀2
    omega
  have hr₀2' : r₀ ^ 2 = 1 := hr₀2 ▸ pow_orderOf_eq_one r₀
  have hr₀in : InnerAt L r₀ := hinn r₀ hr₀R hr₀2
  obtain ⟨v, hvTL, j, hjTC, hr₀vj⟩ := h.decomp_inner0 hZ r₀ (hRT hr₀R) hr₀in
  have hvL : v ∈ L := hvTL.2
  have hjD : j ∈ centralizer (L : Set G) := hjTC.2
  have hjT : j ∈ (T : Subgroup G) := hjTC.1
  have hvj : v * j = j * v := mem_centralizer_iff.1 hjD v hvL
  have hv2 : v ^ 2 = 1 := by
    have hc : Commute v j := hvj
    have e : v ^ 2 * j ^ 2 = 1 := by rw [← hc.mul_pow 2, ← hr₀vj]; exact hr₀2'
    have e1 : v ^ 2 = (j ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left e
    have h2L : v ^ 2 ∈ L := L.pow_mem hvL 2
    have h2C : v ^ 2 ∈ centralizer (L : Set G) := by
      rw [e1]
      exact (centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).pow_mem hjD 2)
    exact hZ' _ h2L h2C
  have hj2 : j ^ 2 = 1 := by
    have hc : Commute v j := hvj
    have e : v ^ 2 * j ^ 2 = 1 := by rw [← hc.mul_pow 2, ← hr₀vj]; exact hr₀2'
    rwa [hv2, one_mul] at e
  have hv1 : v ≠ 1 := by
    intro hv
    have : r₀ ∈ R ⊓ centralizer (L : Set G) := ⟨hr₀R, by rw [hr₀vj, hv, one_mul]; exact hjD⟩
    rw [hRD, Subgroup.mem_bot] at this
    exact hr₀1 this
  have hvo : orderOf v = 2 := orderOf_eq_prime hv2 hv1
  have hvR : v * j ∈ R := hr₀vj ▸ hr₀R
  have hfixR : ∀ ρ ∈ R, ∀ c ∈ L, orderOf c = 3 → c * v = v * c → ρ * c = c * ρ := by
    intro ρ hρ c hcL hc3 hcv
    have hcj : c * j = j * c := mem_centralizer_iff.1 hjD c hcL
    have hcr : c * r₀ = r₀ * c := by
      rw [hr₀vj]
      calc c * (v * j) = (c * v) * j := by group
        _ = (v * c) * j := by rw [hcv]
        _ = v * (c * j) := by group
        _ = v * (j * c) := by rw [hcj]
        _ = (v * j) * c := by group
    have hc' := h.three_mem_conj hterm hZ' hR3 hr₀2 (hmemK r₀ hr₀R) hc3 hcr
    have hcomm := mem_centralizer_iff.1 (hmemK ρ hρ) _ hc'
    calc ρ * c = g₀ * ((g₀⁻¹ * ρ * g₀) * (g₀⁻¹ * c * g₀)) * g₀⁻¹ := by group
      _ = g₀ * ((g₀⁻¹ * c * g₀) * (g₀⁻¹ * ρ * g₀)) * g₀⁻¹ := by rw [hcomm]
      _ = c * ρ := by group
  have hsq := fun ρ (hρ : ρ ∈ R) =>
    hO.inner_sq v hvL hvo ρ (hTle (hRT hρ)) (hfixR ρ hρ)
  have hD1 : ∀ x ∈ R, x ∈ centralizer (L : Set G) → x = 1 := by
    intro x hx hxD
    have : x ∈ R ⊓ centralizer (L : Set G) := ⟨hx, hxD⟩
    rwa [hRD, Subgroup.mem_bot] at this
  have hkey : ∀ x ∈ R, v⁻¹ * x ∈ centralizer (L : Set G) → x = v * j := fun x hx hxD =>
    eq_mul_of_inv_mul_mem hvL hjD hRD hvR hx hxD
  have hsqR : ∀ ρ ∈ R, ρ ^ 2 = 1 ∨ ρ ^ 2 = v * j := by
    intro ρ hρ
    rcases (hsq ρ hρ).1 with h' | h'
    · exact Or.inl (hD1 _ (R.pow_mem hρ 2) h')
    · exact Or.inr (hkey _ (R.pow_mem hρ 2) h')
  have hinvR : ∀ ρ ∈ R, ρ ^ 2 = 1 → ρ = 1 ∨ ρ = v * j := by
    intro ρ hρ hρ2
    by_cases hρ1 : ρ = 1
    · exact Or.inl hρ1
    · have hρo : orderOf ρ = 2 := orderOf_eq_prime hρ2 hρ1
      rcases (hsq ρ hρ).2 (hinn ρ hρ hρo) (by rw [hρ2]; exact one_mem _) with h' | h'
      · exact Or.inl (hD1 ρ hρ h')
      · exact Or.inr (hkey ρ hρ h')
  obtain ⟨s, hsQ, hs1, hs2, hsc, hsu, hcent, hword⟩ := hSy.exists_s
  have hsT := h.central_of_unique hsQ hs1 hs2 hsc hsu
  by_cases h4 : ∃ ρ ∈ R, ρ ^ 2 = v * j
  ·
    obtain ⟨ρ, hρR, hρ2⟩ := h4
    have hρT : ρ ∈ (T : Subgroup G) := hRT hρR
    have hρN : ρ ∈ normalizer (L : Set G) := hTle hρT
    have hRcyc : IsCyclic ↥R := by
      rcases hcyc with hC | hC
      · obtain ⟨e⟩ := h1.equiv
        have : IsCyclic ↥(((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ normalizer (R : Set G)) :=
          isCyclic_of_le_of_isCyclic inf_le_left hC
        have := this
        exact isCyclic_of_injective e.toMonoidHom e.injective
      · exact hC R (hRT.trans hTle) hRD v hvL hvo hfixR
    have hρ1 : ρ ^ 2 ≠ 1 := by
      rw [hρ2]
      intro h'
      apply hr₀1
      rw [hr₀vj]
      exact h'
    have hρ4 : ρ ^ 4 = 1 := by
      calc ρ ^ 4 = (ρ ^ 2) ^ 2 := by rw [← pow_mul]
        _ = (v * j) ^ 2 := by rw [hρ2]
        _ = 1 := by rw [← hr₀vj]; exact hr₀2'
    have hρo : orderOf ρ = 4 := by
      have h1' : ¬ ρ ^ 2 ^ 1 = 1 := by simpa using hρ1
      have h2' : ρ ^ 2 ^ (1 + 1) = 1 := by simpa using hρ4
      have := orderOf_eq_prime_pow h1' h2'
      simpa using this
    have hRρ : R = zpowers ρ := by
      have hcard : Nat.card ↥R = 4 := by
        obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥R)
        have h44 : γ ^ 4 = 1 := by
          have h1' : (γ : G) ^ 4 = 1 := by
            rcases hsqR γ γ.2 with h' | h'
            · calc (γ : G) ^ 4 = ((γ : G) ^ 2) ^ 2 := by rw [← pow_mul]
                _ = 1 := by rw [h']; simp
            · calc (γ : G) ^ 4 = ((γ : G) ^ 2) ^ 2 := by rw [← pow_mul]
                _ = 1 := by rw [h', ← hr₀vj]; exact hr₀2'
          exact Subtype.ext (by simpa using h1')
        have hdvd1 : Nat.card ↥R ∣ 4 := hγ ▸ orderOf_dvd_of_pow_eq_one h44
        have hdvd2 : 4 ∣ Nat.card ↥R := hρo ▸ Subgroup.orderOf_dvd_natCard R hρR
        exact Nat.dvd_antisymm hdvd1 hdvd2
      refine (Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 hρR) ?_).symm
      rw [Nat.card_zpowers, hρo, hcard]
    have hjρ : ρ * j = j * ρ := by
      have hρjD : ρ * j * ρ⁻¹ ∈ centralizer (L : Set G) := conj_mem_centralizer' hρN hjD
      have hρvL : ρ * v * ρ⁻¹ ∈ L := (mem_normalizer_iff.1 hρN v).1 hvL
      have h1' : (ρ * v * ρ⁻¹) * (ρ * j * ρ⁻¹) = v * j := by
        calc (ρ * v * ρ⁻¹) * (ρ * j * ρ⁻¹) = ρ * (v * j) * ρ⁻¹ := by group
          _ = ρ * ρ ^ 2 * ρ⁻¹ := by rw [hρ2]
          _ = ρ ^ 2 := by group
          _ = v * j := hρ2
      have := (eq_of_mul_eq_of_trivial hZ' hρvL hvL hρjD hjD h1').2
      calc ρ * j = (ρ * j * ρ⁻¹) * ρ := by group
        _ = j * ρ := by rw [this]
    have hjX : j ∈ ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ centralizer (R : Set G) := by
      refine ⟨hjTC, mem_centralizer_iff.2 fun x hx => ?_⟩
      rw [hRρ] at hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      exact ((Commute.zpow_left (show Commute ρ j from hjρ) k)).eq
    have hzX : z ∈ ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ centralizer (R : Set G) :=
      ⟨hzTC, mem_centralizer_iff.2 fun x hx => hzc x (hRT hx)⟩
    have hXcyc : IsCyclic ↥(((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
        centralizer (R : Set G)) := by
      rw [← h1.normalizer_eq_centralizer]
      obtain ⟨e⟩ := h1.equiv
      have := hRcyc
      exact isCyclic_of_injective e.symm.toMonoidHom e.symm.injective
    have hjz : j = 1 ∨ j = z := by
      have := cyclic_pow_two_eq_one
        (X := ↥(((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ centralizer (R : Set G)))
        (z := ⟨z, hzX⟩) (c := ⟨j, hjX⟩) (Subtype.ext (by simpa using hz2))
        (fun h' => hz1 (congrArg Subtype.val h')) (Subtype.ext (by simpa using hj2))
      rcases this with h' | h'
      · exact Or.inl (congrArg Subtype.val h')
      · exact Or.inr (congrArg Subtype.val h')
    have hjt : ∀ t ∈ (T : Subgroup G), t * j = j * t := by
      intro t ht
      rcases hjz with h' | h'
      · rw [h']
        simp
      · rw [h']
        exact hzc t ht
    have hx1 : v * j ≠ 1 := by rw [← hr₀vj]; exact hr₀1
    by_cases hρin : InnerAt L ρ
    ·
      obtain ⟨a, haTL, d, hdTC, hρad⟩ := h.decomp_inner0 hZ ρ hρT hρin
      have haL : a ∈ L := haTL.2
      have hdD : d ∈ centralizer (L : Set G) := hdTC.2
      have had : a * d = d * a := mem_centralizer_iff.1 hdD a haL
      have hρ2' : a ^ 2 * d ^ 2 = v * j := by
        rw [← hρ2, hρad]
        have hc : Commute a d := had
        rw [← hc.mul_pow 2]
      have hav := eq_of_mul_eq_of_trivial hZ' (L.pow_mem haL 2) hvL
        ((centralizer (L : Set G)).pow_mem hdD 2) hjD hρ2'
      have ha2 : a ^ 2 = v := hav.1
      have ha4 : orderOf a = 4 := by
        have h1' : ¬ a ^ 2 ^ 1 = 1 := by
          rw [pow_one, ha2]
          exact hv1
        have h2' : a ^ 2 ^ (1 + 1) = 1 := by
          have h4 : a ^ 4 = (a ^ 2) ^ 2 := by rw [← pow_mul]
          rw [ha2, hv2] at h4
          simpa using h4
        have := orderOf_eq_prime_pow h1' h2'
        simpa using this
      have hfixa : ∀ c ∈ L, orderOf c = 3 → c * a ^ 2 = a ^ 2 * c → c * a = a * c := by
        intro c hcL hc3 hca
        rw [ha2] at hca
        have h1' := hfixR ρ hρR c hcL hc3 hca
        rw [hρad] at h1'
        have hcd : c * d = d * c := mem_centralizer_iff.1 hdD c hcL
        have h2' : a * c * d = c * a * d := by
          calc a * c * d = a * (c * d) := by group
            _ = a * (d * c) := by rw [hcd]
            _ = (a * d) * c := by group
            _ = c * (a * d) := h1'
            _ = c * a * d := by group
        exact (mul_right_cancel h2').symm
      obtain ⟨k, hkL, hkTL, hkc⟩ := hSy.conj4 a haTL ha4 hfixa
      have hconjpow : ∀ n : ℕ, (k⁻¹ * a * k) ^ n = k⁻¹ * a ^ n * k := by
        intro n
        have := conj_pow (a := k⁻¹) (b := a) (i := n)
        simpa using this
      have hsa : (k⁻¹ * a * k) ^ 2 = s := by
        have hcentral : ∀ y ∈ (T : Subgroup G) ⊓ L,
            y * (k⁻¹ * a * k) ^ 2 = (k⁻¹ * a * k) ^ 2 * y := by
          intro y hy
          rw [pow_two]
          calc y * ((k⁻¹ * a * k) * (k⁻¹ * a * k)) = (y * (k⁻¹ * a * k)) * (k⁻¹ * a * k) := by group
            _ = ((k⁻¹ * a * k) * y) * (k⁻¹ * a * k) := by rw [hkc y hy]
            _ = (k⁻¹ * a * k) * (y * (k⁻¹ * a * k)) := by group
            _ = (k⁻¹ * a * k) * ((k⁻¹ * a * k) * y) := by rw [hkc y hy]
            _ = ((k⁻¹ * a * k) * (k⁻¹ * a * k)) * y := by group
        have hconjv : ∀ n : ℕ, (k⁻¹ * v * k) ^ n = k⁻¹ * v ^ n * k := by
          intro n
          have := conj_pow (a := k⁻¹) (b := v) (i := n)
          simpa using this
        have hsq2 : ((k⁻¹ * a * k) ^ 2) ^ 2 = 1 := by
          rw [hconjpow 2, ha2, hconjv 2, hv2]
          group
        have hne : (k⁻¹ * a * k) ^ 2 ≠ 1 := by
          rw [hconjpow 2, ha2]
          intro h'
          apply hv1
          calc v = k * (k⁻¹ * v * k) * k⁻¹ := by group
            _ = 1 := by rw [h']; group
        exact (hsu _ (((T : Subgroup G) ⊓ L).pow_mem hkTL 2) hcentral hsq2).resolve_left hne
      have hv₀ : k⁻¹ * v * k = s := by
        rw [← ha2, ← hconjpow 2]
        exact hsa
      have hkN : k ∈ normalizer (centralizer (L : Set G) : Set G) := by
        rw [hstd.2.2.2.1]
        exact Subgroup.le_normalizer hkL
      obtain ⟨hK'', hR''⟩ := delta_triple_conj hK' hR hkN
      have hkj : k * j = j * k := mem_centralizer_iff.1 hjD k hkL
      have hkd : k * d = d * k := mem_centralizer_iff.1 hdD k hkL
      have hR''T : rightConjugate R k ≤ (T : Subgroup G) := by
        intro y hy
        have hy' : k * y * k⁻¹ ∈ R := (mem_rightConjugate_iff R k y).1 hy
        rw [hRρ] at hy'
        obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hy'
        have e1 : (k⁻¹ * ρ * k) ^ m = k⁻¹ * ρ ^ m * k := by
          have := conj_zpow (a := k⁻¹) (b := ρ) (i := m)
          simpa using this
        have e2 : k⁻¹ * ρ * k = (k⁻¹ * a * k) * d := by
          rw [hρad]
          calc k⁻¹ * (a * d) * k = k⁻¹ * a * (d * k) := by group
            _ = k⁻¹ * a * (k * d) := by rw [hkd]
            _ = (k⁻¹ * a * k) * d := by group
        have hyd : y = ((k⁻¹ * a * k) * d) ^ m := by
          calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
            _ = k⁻¹ * ρ ^ m * k := by rw [← hm]
            _ = (k⁻¹ * ρ * k) ^ m := e1.symm
            _ = ((k⁻¹ * a * k) * d) ^ m := by rw [e2]
        rw [hyd]
        exact (T : Subgroup G).zpow_mem ((T : Subgroup G).mul_mem hkTL.1 hdTC.1) m
      have hxR : s * j ∈ rightConjugate R k := by
        rw [mem_rightConjugate_iff]
        have : k * (s * j) * k⁻¹ = v * j := by
          calc k * (s * j) * k⁻¹ = (k * s * k⁻¹) * (k * j * k⁻¹) := by group
            _ = v * j := by
              have e1 : k * s * k⁻¹ = v := by rw [← hv₀]; group
              have e2 : k * j * k⁻¹ = j := by rw [hkj]; group
              rw [e1, e2]
        rw [this]
        exact hvR
      have hx1' : s * j ≠ 1 := by
        intro h'
        have : s = j⁻¹ := eq_inv_of_mul_eq_one_left h'
        apply hs1
        apply hZ' s hsQ.2
        rw [this]
        exact (centralizer (L : Set G)).inv_mem hjD
      have hxZ' : ∀ t ∈ (T : Subgroup G), t * (s * j) = (s * j) * t := by
        intro t ht
        calc t * (s * j) = (t * s) * j := by group
          _ = (s * t) * j := by rw [hsT t ht]
          _ = s * (t * j) := by group
          _ = s * (j * t) := by rw [hjt t ht]
          _ = (s * j) * t := by group
      have hR''cyc : IsCyclic ↥(rightConjugate R k) := by
        have := hRcyc
        exact isCyclic_of_injective (CFSG.GH74.AS16.rightConjugateEquiv R k).symm.toMonoidHom
          (CFSG.GH74.AS16.rightConjugateEquiv R k).symm.injective
      exact h.finish hterm hZ hR3 hSy hK'' hR'' hR''T hxR hx1' hxZ'
        (h.tC_cyclic_of_R hterm hZ hR3 hK'' hR'' hR''T hR''cyc)
    ·
      have hρnorm : ∀ q ∈ (T : Subgroup G) ⊓ L, ρ * q * ρ⁻¹ ∈ (T : Subgroup G) ⊓ L := by
        intro q hq
        exact ⟨(T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hρT hq.1)
          ((T : Subgroup G).inv_mem hρT), (mem_normalizer_iff.1 hρN q).1 hq.2⟩
      have hvj' : v⁻¹ * ρ ^ 2 ∈ centralizer (L : Set G) := by
        rw [hρ2]
        have : v⁻¹ * (v * j) = j := by group
        rw [this]
        exact hjD
      have hvc := hSy.sq ρ hρN hρin hρnorm v hvTL hvo (hfixR ρ hρR) hvj'
      have hvs : v = s := (hsu v hvTL hvc hv2).resolve_left hv1
      have hxZ : ∀ t ∈ (T : Subgroup G), t * (v * j) = (v * j) * t := by
        intro t ht
        rw [hvs]
        calc t * (s * j) = (t * s) * j := by group
          _ = (s * t) * j := by rw [hsT t ht]
          _ = s * (t * j) := by group
          _ = s * (j * t) := by rw [hjt t ht]
          _ = (s * j) * t := by group
      exact h.finish hterm hZ hR3 hSy hK' hR hRT hvR hx1 hxZ
        (h.tC_cyclic_of_R hterm hZ hR3 hK' hR hRT hRcyc)
  ·
    push Not at h4
    have hRsub : ∀ ρ ∈ R, ρ = 1 ∨ ρ = v * j := fun ρ hρ =>
      hinvR ρ hρ ((hsqR ρ hρ).resolve_right (h4 ρ hρ))
    have hRcard : Nat.card ↥R = 2 := by
      have hR' : R = zpowers r₀ := by
        apply le_antisymm
        · intro ρ hρ
          rcases hRsub ρ hρ with h' | h'
          · rw [h']
            exact one_mem _
          · rw [h', ← hr₀vj]
            exact mem_zpowers r₀
        · exact (zpowers_le).2 hr₀R
      rw [hR', Nat.card_zpowers, hr₀2]
    have hX := lemma1644_one h.pair hN hstd hK' hR hRT hRcard
    have hXcard : Nat.card ↥(((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
        centralizer (R : Set G)) = 2 := by
      rw [hX, Nat.card_zpowers, hzo]
    have hzX : z ∈ ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ centralizer (R : Set G) :=
      ⟨hzTC, mem_centralizer_iff.2 fun x hx => hzc x (hRT hx)⟩
    have hjX : j ∈ ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ centralizer (R : Set G) := by
      refine ⟨hjTC, mem_centralizer_iff.2 fun ρ hρ => ?_⟩
      rcases hRsub ρ hρ with h' | h'
      · rw [h']
        simp
      · rw [h']
        calc v * j * j = v * (j * j) := by group
          _ = (j * v) * j := by rw [← hvj]; group
          _ = j * (v * j) := by group
    have hTCcard := card_eq_two_of_cent hXcard hzX hz1 hjX (fun c hc => h.pair.central c hc.1)
      (fun c hc => (mem_centralizer_iff.1 hc.2 v hvL).symm) hRsub
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hTCcyc : IsCyclic ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) :=
      isCyclic_of_prime_card hTCcard
    have hjz : j = 1 ∨ j = z := eq_one_or_of_card_two hTCcard hzTC hz1 j hjTC
    have hjt : ∀ t ∈ (T : Subgroup G), t * j = j * t := by
      intro t ht
      rcases hjz with h' | h'
      · rw [h']
        simp
      · rw [h']
        exact hzc t ht
    obtain ⟨k, hkL, hkTL, hkc⟩ := hSm.conj_central v hvTL hv2
    have hv₀2 : (k⁻¹ * v * k) ^ 2 = 1 := by
      calc (k⁻¹ * v * k) ^ 2 = k⁻¹ * v ^ 2 * k := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hv2]; group
    have hv₀1 : k⁻¹ * v * k ≠ 1 := by
      intro h'
      apply hv1
      have : v = k * (k⁻¹ * v * k) * k⁻¹ := by group
      rw [this, h']
      group
    have hv₀ : k⁻¹ * v * k = s := (hsu _ hkTL hkc hv₀2).resolve_left hv₀1
    have hkN : k ∈ normalizer (centralizer (L : Set G) : Set G) := by
      rw [hstd.2.2.2.1]
      exact Subgroup.le_normalizer hkL
    obtain ⟨hK'', hR''⟩ := delta_triple_conj hK' hR hkN
    have hkj : k * j = j * k := mem_centralizer_iff.1 hjD k hkL
    have hR''T : rightConjugate R k ≤ (T : Subgroup G) := by
      intro y hy
      have hy' : k * y * k⁻¹ ∈ R := (mem_rightConjugate_iff R k y).1 hy
      rcases hRsub _ hy' with h' | h'
      · have : y = 1 := by
          calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
            _ = 1 := by rw [h']; group
        rw [this]
        exact one_mem _
      · have : y = s * j := by
          calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
            _ = k⁻¹ * (v * j) * k := by rw [h']
            _ = (k⁻¹ * v * k) * (k⁻¹ * j * k) := by group
            _ = s * j := by
              rw [hv₀]
              have : k⁻¹ * j * k = j := by
                calc k⁻¹ * j * k = k⁻¹ * (j * k) := by group
                  _ = k⁻¹ * (k * j) := by rw [hkj]
                  _ = j := by group
              rw [this]
        rw [this]
        exact (T : Subgroup G).mul_mem hsQ.1 hjT
    have hxR : s * j ∈ rightConjugate R k := by
      rw [mem_rightConjugate_iff]
      have : k * (s * j) * k⁻¹ = v * j := by
        calc k * (s * j) * k⁻¹ = (k * s * k⁻¹) * (k * j * k⁻¹) := by group
          _ = v * j := by
            have e1 : k * s * k⁻¹ = v := by rw [← hv₀]; group
            have e2 : k * j * k⁻¹ = j := by rw [hkj]; group
            rw [e1, e2]
      rw [this]
      exact hvR
    have hx1 : s * j ≠ 1 := by
      intro h'
      have : s = j⁻¹ := eq_inv_of_mul_eq_one_left h'
      apply hs1
      apply hZ' s hsQ.2
      rw [this]
      exact (centralizer (L : Set G)).inv_mem hjD
    have hxZ : ∀ t ∈ (T : Subgroup G), t * (s * j) = (s * j) * t := by
      intro t ht
      calc t * (s * j) = (t * s) * j := by group
        _ = (s * t) * j := by rw [hsT t ht]
        _ = s * (t * j) := by group
        _ = s * (j * t) := by rw [hjt t ht]
        _ = (s * j) * t := by group
    exact h.finish hterm hZ hR3 hSy hK'' hR'' hR''T hxR hx1 hxZ (fun _ _ _ => hTCcyc)

end Main

end CFSG.GH74.AS16.E2
