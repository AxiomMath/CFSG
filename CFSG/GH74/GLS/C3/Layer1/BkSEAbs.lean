module

public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.RankThree.PartTwo.Sec10.Item10Std
public import CFSG.GH74.GLS.C3.Layer1.BkW5Odd

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools Equiv Perm CFSG.GH74.GLS.C3.Layer2

open Subgroup CFSG CFSG.ABGLocalTools Equiv Perm CFSG.GH74.GLS.C3.Layer2

@[expose] def stdAlt (n : ℕ) : Subgroup (alternatingGroup (Fin (n + 4))) where
  carrier := {σ | ∀ i : Fin (n + 4), n ≤ i.val → (σ : Perm (Fin (n + 4))) i = i}
  mul_mem' := by
    intro σ τ hσ hτ i hi
    show (σ : Perm (Fin (n + 4))) ((τ : Perm (Fin (n + 4))) i) = i
    rw [hτ i hi, hσ i hi]
  one_mem' := fun i _ => rfl
  inv_mem' := by
    intro σ hσ i hi
    show ((σ : Perm (Fin (n + 4)))⁻¹) i = i
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hσ i hi).symm

theorem threeCycle_mem_stdAlt {n : ℕ} (i p q : Fin (n + 4)) (hi : i.val < n) (hp : p.val < n)
    (hq : q.val < n) (hip : i ≠ p) (hiq : i ≠ q) (_hpq : p ≠ q) :
    (⟨swap i p * swap i q, by
        rw [mem_alternatingGroup, map_mul, sign_swap hip, sign_swap hiq]
        decide⟩ : alternatingGroup (Fin (n + 4))) ∈ stdAlt n := by
  intro k hk
  have hki : k ≠ i := by
    intro h; rw [h] at hk; omega
  have hkp : k ≠ p := by
    intro h; rw [h] at hk; omega
  have hkq : k ≠ q := by
    intro h; rw [h] at hk; omega
  show swap i p (swap i q k) = k
  rw [swap_apply_of_ne_of_ne hki hkq, swap_apply_of_ne_of_ne hki hkp]

theorem fixes_of_commute_stdAlt {n : ℕ} (hn : 4 ≤ n) (σ : Perm (Fin (n + 4)))
    (hσ : ∀ τ ∈ stdAlt n, σ * (τ : Perm (Fin (n + 4))) = (τ : Perm (Fin (n + 4))) * σ)
    (i : Fin (n + 4)) (hi : i.val < n) : σ i = i := by
  by_contra hne
  set j := σ i with hj
  obtain ⟨p, q, hpq, hp4, hq4, hpi, hpj, hqi, hqj⟩ : ∃ p q : ℕ, p ≠ q ∧ p < 4 ∧ q < 4 ∧
      p ≠ i.val ∧ p ≠ j.val ∧ q ≠ i.val ∧ q ≠ j.val := by
    have hcard : 2 ≤ ((Finset.range 4) \ {i.val, j.val}).card := by
      have h1 : (Finset.range 4).card - ({i.val, j.val} : Finset ℕ).card ≤
          ((Finset.range 4) \ {i.val, j.val}).card := Finset.le_card_sdiff _ _
      have h2 : ({i.val, j.val} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_range] at h1
      omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 (by omega : 1 < ((Finset.range 4) \ {i.val, j.val}).card)
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton,
      not_or] at hp hq
    exact ⟨p, q, hpq, hp.1, hq.1, hp.2.1, hp.2.2, hq.2.1, hq.2.2⟩
  let P : Fin (n + 4) := ⟨p, by omega⟩
  let Qp : Fin (n + 4) := ⟨q, by omega⟩
  have hPn : P.val < n := by show p < n; omega
  have hQn : Qp.val < n := by show q < n; omega
  have hiP : i ≠ P := fun h => hpi (congrArg Fin.val h).symm
  have hiQ : i ≠ Qp := fun h => hqi (congrArg Fin.val h).symm
  have hPQ : P ≠ Qp := fun h => hpq (congrArg Fin.val h)
  have hjP : j ≠ P := fun h => hpj (congrArg Fin.val h).symm
  have hjQ : j ≠ Qp := fun h => hqj (congrArg Fin.val h).symm
  have hcomm := hσ _ (threeCycle_mem_stdAlt i P Qp hi hPn hQn hiP hiQ hPQ)
  have hci : (swap i P * swap i Qp) i = Qp := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hiQ.symm hPQ.symm]
  have hcj : (swap i P * swap i Qp) j = j := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hne hjQ, swap_apply_of_ne_of_ne hne hjP]
  have h1 : σ ((swap i P * swap i Qp) i) = (swap i P * swap i Qp) (σ i) :=
    congrArg (fun f : Perm (Fin (n + 4)) => f i) hcomm
  rw [hci, ← hj, hcj] at h1
  exact hiQ (σ.injective (h1.trans hj)).symm

theorem isConj_of_isConj_mk {N : Type} [Group N] [Finite N] (O : Subgroup N) [O.Normal]
    (hO : Odd (Nat.card O)) {s t : N} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hc : IsConj (QuotientGroup.mk s : N ⧸ O) (QuotientGroup.mk t)) : IsConj s t := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  obtain ⟨c0, rfl⟩ := QuotientGroup.mk_surjective c
  have hmk : (QuotientGroup.mk (c0 * s * c0⁻¹) : N ⧸ O) = QuotientGroup.mk t := by
    rw [← hc]
    simp [QuotientGroup.mk_mul]
  have hsu : (c0 * s * c0⁻¹)⁻¹ * t ∈ O := QuotientGroup.eq.1 hmk
  have hs' : orderOf (c0 * s * c0⁻¹) = 2 := by
    rw [← hs]
    exact (SemiconjBy.orderOf_eq c0 (by
      change c0 * s = c0 * s * c0⁻¹ * c0
      group)).symm
  have hP : ∀ {y : N}, orderOf y = 2 → IsPGroup 2 ↥(zpowers y) := by
    intro y hy
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hy]
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_of_coset (C := ⊤) (W := O) (B₁ := zpowers (c0 * s * c0⁻¹))
    (B₂ := zpowers t) (fun c _ w hw => (inferInstance : O.Normal).conj_mem w hw c) hO
    (Subgroup.mem_top _) (mem_zpowers _) (hP hs') (mem_zpowers t) (hP ht) hsu
  refine isConj_iff.2 ⟨g⁻¹ * c0, ?_⟩
  calc g⁻¹ * c0 * s * (g⁻¹ * c0)⁻¹ = g⁻¹ * (c0 * s * c0⁻¹) * g := by group
    _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hg]
    _ = t := by group

theorem isStronglyEmbeddedOrder_of_involutions {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hM : M ≠ ⊤) (heven : ∃ t ∈ M, orderOf t = 2)
    (hfus : ∀ t ∈ M, orderOf t = 2 → ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  refine ⟨hM, ?_, ?_⟩
  · obtain ⟨t, htM, ht⟩ := heven
    have : orderOf (⟨t, htM⟩ : M) ∣ Nat.card M := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, ht] at this
    exact even_iff_two_dvd.mpr this
  · intro g hg
    by_contra hodd
    have hev : Even (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))) :=
      Nat.not_odd_iff_even.mp hodd
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom))
      2 (even_iff_two_dvd.mp hev)
    have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
    obtain ⟨htM, m, hm, hmt⟩ := t.2
    have hconj : g⁻¹ * (t : G) * g ∈ M := by
      have e : g⁻¹ * (t : G) * g = m := by
        rw [← hmt]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hm
    exact hg (hfus _ htM ht2 g hconj)

section NLevel

variable {M : Type} [Group M] [Finite M]

abbrev piO (M : Type) [Group M] : M →* M ⧸ pPrimeCore 2 M := QuotientGroup.mk' (pPrimeCore 2 M)

theorem map_le_of_sylow {n : ℕ} (H : Subgroup (M ⧸ pPrimeCore 2 M))
    (e : ↥H ≃* alternatingGroup (Fin (n + 4))) (hH : H.IsSubnormal) {S : Subgroup M}
    (hS : IsSylowOf 2 S ⊤)
    (hScard : Nat.card S ≤ 2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2) :
    S.map (piO M) ≤ H ∧
      Nat.card (S.map (piO M)) = 2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set k := (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 with hk
  have hsurj : Function.Surjective (piO M) := QuotientGroup.mk'_surjective _
  have hSyl : IsSylowOf 2 (S.map (piO M)) ⊤ := by
    have := CFSG.RankThree.PartTwo.Sec12.IsSylowOf.map hS (piO M)
    rwa [Subgroup.map_top_of_surjective _ hsurj] at this
  have hinf := CFSG.RankThree.PartTwo.Sec10.IsSylowOf.inf_of_isSubnormal hSyl hH
  have hcardH : Nat.card H = Nat.card (alternatingGroup (Fin (n + 4))) := Nat.card_congr e.toEquiv
  have hinfcard : Nat.card ↥(S.map (piO M) ⊓ H) = 2 ^ k := by rw [hinf.card_eq, hcardH]
  have hSb : Nat.card (S.map (piO M)) ≤ 2 ^ k :=
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd S (piO M))).trans hScard
  have heq : S.map (piO M) ⊓ H = S.map (piO M) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hinfcard]; exact hSb)
  refine ⟨inf_eq_left.1 heq, ?_⟩
  have := hinfcard
  rw [heq] at this
  exact this

theorem numMoved_le_four_of_commute {n : ℕ} (hn : 4 ≤ n) (σ : Perm (Fin (n + 4)))
    (hσ : ∀ τ ∈ stdAlt n, σ * (τ : Perm (Fin (n + 4))) = (τ : Perm (Fin (n + 4))) * σ) :
    numMoved σ ≤ 4 := by
  have hsub : (Finset.univ.filter fun a => σ a ≠ a) ⊆
      Finset.Ici (⟨n, by omega⟩ : Fin (n + 4)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_Ici]
    by_contra hlt
    exact ha (fixes_of_commute_stdAlt hn σ hσ a (by simpa [Fin.le_def] using hlt))
  calc numMoved σ ≤ (Finset.Ici (⟨n, by omega⟩ : Fin (n + 4))).card := Finset.card_le_card hsub
    _ = 4 := by simp [Fin.card_Ici]

theorem orderOf_piO_of_orderOf_two {M : Type} [Group M] [Finite M] {t : M} (ht : orderOf t = 2) :
    orderOf (piO M t) = 2 := by
  have hsq : (piO M t) ^ 2 = 1 := by
    rw [← map_pow]
    have : t ^ 2 = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [ht] at h
    rw [this, map_one]
  have hne : piO M t ≠ 1 := by
    intro h1
    have hmem : t ∈ pPrimeCore 2 M := (QuotientGroup.eq_one_iff t).1 h1
    have hd := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 M) hmem
    rw [ht] at hd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact absurd (Nat.Coprime.eq_one_of_dvd pPrimeCore_coprime_card hd) (by norm_num)
  exact orderOf_eq_prime hsq hne

end NLevel

section NLevel2

variable {M : Type} [Group M] [Finite M]

theorem n_level {n : ℕ} (hn : n = 5 ∨ n = 7)
    (H : Subgroup (M ⧸ pPrimeCore 2 M)) (e : ↥H ≃* alternatingGroup (Fin (n + 4)))
    (hH : H.IsSubnormal) {S Q Kb : Subgroup M} (hS : IsSylowOf 2 S ⊤)
    (hScard : Nat.card S ≤ 2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2)
    (hKe : ((Kb.map (piO M)).subgroupOf H).map e.toMonoidHom = stdAlt n)
    (hQS : Q ≤ S) (hQ2 : ∀ q ∈ Q, q * q = 1)
    (hQK : ∀ q ∈ Q, ∀ k ∈ Kb, piO M q * piO M k = piO M k * piO M q)
    {x v : M} (hxQ : x ∈ Q) (hx : orderOf x = 2) (hv : orderOf v = 2) (hvS : v ∈ S)
    (hvc : ∀ s ∈ S, s * v = v * s) (hxv : ¬ IsConj x v) :
    (∀ u ∈ S, orderOf u = 2 → IsConj u x ∨ IsConj u v) ∧ (∀ q ∈ Q, q ≠ 1 → IsConj q x) ∧
      ∃ v'' : alternatingGroup (Fin (n + 4)), CFSG.GH74.IsCentralInvolution v'' ∧
        ∃ ι : ↥(centralizer ({v''} : Set (alternatingGroup (Fin (n + 4))))) →*
            ↥(centralizer ({piO M v} : Set (M ⧸ pPrimeCore 2 M))), Function.Injective ι := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn4 : 4 ≤ n := by omega
  have hn11 : n + 4 ≤ 11 := by omega
  obtain ⟨hSH, hSπcard⟩ := map_le_of_sylow H e hH hS hScard
  let toH : ↥S →* ↥H :=
    ((piO M).comp S.subtype).codRestrict H (fun s => hSH ⟨s.1, s.2, rfl⟩)
  let toA : ↥S →* alternatingGroup (Fin (n + 4)) := e.toMonoidHom.comp toH
  have htoH : ∀ s : S, ((toH s : ↥H) : M ⧸ pPrimeCore 2 M) = piO M s.1 := fun s => rfl
  have hord : ∀ s : S, orderOf s.1 = 2 → orderOf (toA s) = 2 := by
    intro s hs
    have h1 : orderOf (toH s) = 2 := by
      rw [← Subgroup.orderOf_coe, htoH]
      exact orderOf_piO_of_orderOf_two hs
    show orderOf (e (toH s)) = 2
    rw [MulEquiv.orderOf_eq]
    exact h1
  have hnm : ∀ s : S, orderOf s.1 = 2 →
      numMoved (toA s : Perm (Fin (n + 4))) = 4 ∨ numMoved (toA s : Perm (Fin (n + 4))) = 8 :=
    fun s hs => numMoved_eq_of_involution_alternating (n + 4) hn11 (toA s) (hord s hs)
  have hodd : Odd (Nat.card (pPrimeCore 2 M)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hconj : ∀ s t : S, orderOf s.1 = 2 → orderOf t.1 = 2 →
      numMoved (toA s : Perm (Fin (n + 4))) = numMoved (toA t : Perm (Fin (n + 4))) →
        IsConj s.1 t.1 := by
    intro s t hs ht hst
    have h1 : IsConj (toA s) (toA t) :=
      isConj_alternating_of_numMoved_eq (n + 4) _ _ (hord s hs) (hord t ht) hst
    have h2 : IsConj (toH s) (toH t) := by
      have h2' : IsConj (e.symm (toA s)) (e.symm (toA t)) := e.symm.toMonoidHom.map_isConj h1
      have e1 : e.symm (toA s) = toH s := e.symm_apply_apply (toH s)
      have e2 : e.symm (toA t) = toH t := e.symm_apply_apply (toH t)
      rwa [e1, e2] at h2'
    have h3 : IsConj (piO M s.1) (piO M t.1) := H.subtype.map_isConj h2
    exact isConj_of_isConj_mk (pPrimeCore 2 M) hodd hs ht h3
  let x₀ : ↥S := ⟨x, hQS hxQ⟩
  let v₀ : ↥S := ⟨v, hvS⟩
  have hxne : numMoved (toA x₀ : Perm (Fin (n + 4))) ≠ numMoved (toA v₀ : Perm (Fin (n + 4))) :=
    fun h => hxv (hconj x₀ v₀ hx hv h)
  have hu_cls : ∀ u ∈ S, orderOf u = 2 → IsConj u x ∨ IsConj u v := by
    intro u hu hu2
    let u₀ : ↥S := ⟨u, hu⟩
    have h1 := hnm u₀ hu2
    have h2 := hnm x₀ hx
    have h3 := hnm v₀ hv
    by_cases hc : numMoved (toA u₀ : Perm (Fin (n + 4))) = numMoved (toA x₀ : Perm (Fin (n + 4)))
    · exact Or.inl (hconj u₀ x₀ hu2 hx hc)
    · right
      apply hconj u₀ v₀ hu2 hv
      omega
  have hq4 : ∀ (q : M) (hq : q ∈ Q), orderOf q = 2 →
      numMoved (toA ⟨q, hQS hq⟩ : Perm (Fin (n + 4))) = 4 := by
    intro q hq hq2
    have hle : numMoved (toA ⟨q, hQS hq⟩ : Perm (Fin (n + 4))) ≤ 4 := by
      apply numMoved_le_four_of_commute hn4
      intro τ hτ
      rw [← hKe] at hτ
      obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.1 hτ
      obtain ⟨k, hk, hkκ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hκ)
      have hc : toH ⟨q, hQS hq⟩ * κ = κ * toH ⟨q, hQS hq⟩ := by
        apply Subtype.ext
        show piO M q * (κ : M ⧸ pPrimeCore 2 M) = (κ : M ⧸ pPrimeCore 2 M) * piO M q
        rw [← hkκ]
        exact hQK q hq k hk
      have h2 : e (toH ⟨q, hQS hq⟩) * e κ = e κ * e (toH ⟨q, hQS hq⟩) := by
        rw [← map_mul, ← map_mul, hc]
      exact congrArg Subtype.val h2
    rcases hnm ⟨q, hQS hq⟩ hq2 with h | h
    · exact h
    · omega
  have hQord : ∀ q ∈ Q, q ≠ 1 → orderOf q = 2 := fun q hq hq1 =>
    orderOf_eq_prime (by rw [sq]; exact hQ2 q hq) hq1
  have hcls2 : ∀ q ∈ Q, q ≠ 1 → IsConj q x := by
    intro q hq hq1
    exact hconj ⟨q, hQS hq⟩ x₀ (hQord q hq hq1) hx
      ((hq4 q hq (hQord q hq hq1)).trans (hq4 x hxQ hx).symm)
  let SA : Subgroup (alternatingGroup (Fin (n + 4))) :=
    ((S.map (piO M)).subgroupOf H).map e.toMonoidHom
  have hSAcard : Nat.card SA = 2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 := by
    rw [Subgroup.card_map_of_injective e.injective, ← hSπcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv
  let PA : Sylow 2 (alternatingGroup (Fin (n + 4))) := Sylow.ofCard SA hSAcard
  have hPA : (PA : Subgroup (alternatingGroup (Fin (n + 4)))) = SA := Sylow.coe_ofCard SA hSAcard
  have hv'' : toA v₀ ∈ SA :=
    ⟨toH v₀, Subgroup.mem_subgroupOf.2 ⟨v, hvS, rfl⟩, rfl⟩
  refine ⟨hu_cls, hcls2, toA v₀, ⟨hord v₀ hv, PA, ?_, ?_⟩, ?_⟩
  · rw [hPA]
    exact hv''
  · intro s hs
    rw [hPA] at hs
    obtain ⟨ŝ, hŝ, rfl⟩ := hs
    obtain ⟨s0, hs0, hs0e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hŝ)
    have hc : ŝ * toH v₀ = toH v₀ * ŝ := by
      apply Subtype.ext
      show (ŝ : M ⧸ pPrimeCore 2 M) * piO M v = piO M v * (ŝ : M ⧸ pPrimeCore 2 M)
      rw [← hs0e, ← map_mul, ← map_mul, hvc s0 hs0]
    show e ŝ * e (toH v₀) = e (toH v₀) * e ŝ
    rw [← map_mul, ← map_mul, hc]
  · let f : ↥(centralizer ({toA v₀} : Set (alternatingGroup (Fin (n + 4))))) →*
        (M ⧸ pPrimeCore 2 M) :=
      (H.subtype.comp e.symm.toMonoidHom).comp (centralizer ({toA v₀} : Set _)).subtype
    have hf : ∀ c, f c ∈ centralizer ({piO M v} : Set (M ⧸ pPrimeCore 2 M)) := by
      intro c
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc := Subgroup.mem_centralizer_singleton_iff.1 c.2
      have h1 := congrArg e.symm hc
      have e1 : e.symm (toA v₀) = toH v₀ := e.symm_apply_apply (toH v₀)
      rw [map_mul, map_mul, e1] at h1
      exact congrArg Subtype.val h1
    refine ⟨f.codRestrict _ hf, ?_⟩
    intro c₁ c₂ h
    have h1 := congrArg Subtype.val h
    have h2 : (e.symm c₁.1 : ↥H) = e.symm c₂.1 := Subtype.ext h1
    exact Subtype.ext (e.symm.injective h2)

end NLevel2

end CFSG.GH74.GLS.C3.Layer1.Bk
