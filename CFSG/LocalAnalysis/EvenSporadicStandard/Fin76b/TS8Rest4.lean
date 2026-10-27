module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Rest

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

section Odd

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {z t : G} {T : Subgroup G}

omit [Finite G] in
theorem OuterConfig.odd_mem_A (h : OuterConfig G A z t T) {n : G}
    (hn : n ∈ centralizer ({z} : Set G)) (hodd : Odd (orderOf n)) : n ∈ A := by
  have hK : n ∈ A ⊔ zpowers z := by
    have h2 : ((A ⊔ zpowers z).subgroupOf (centralizer ({z} : Set G))).index = 2 := h.index_two
    have hsq := Subgroup.sq_mem_of_index_two h2 (⟨n, hn⟩ : centralizer ({z} : Set G))
    have hsq' : n ^ 2 ∈ A ⊔ zpowers z := by
      have := mem_subgroupOf.1 hsq
      simpa using this
    obtain ⟨k, hk⟩ := hodd
    have h1 : n ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one n
    have e : n = (n ^ 2) ^ (k + 1) := by
      calc n = n ^ (2 * k + 1) * n := by rw [h1, one_mul]
        _ = n ^ (2 * k + 1 + 1) := (pow_succ n (2 * k + 1)).symm
        _ = n ^ (2 * (k + 1)) := by congr 1
        _ = (n ^ 2) ^ (k + 1) := pow_mul n 2 (k + 1)
    rw [e]
    exact pow_mem hsq' _
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (zpowers_le.2 h.z_cent) hK
  rcases mem_zpowers_sq_eq_one h.z_sq hc with hc1 | hc1
  · subst hc1
    simpa using ha
  · subst hc1
    exfalso
    obtain ⟨k, hk⟩ := hodd
    have hcomm : Commute a c := h.z_comm_of_mem_A ha
    have hz2 : c ^ 2 = 1 := by rw [pow_two]; exact h.z_sq
    have h1 : (a * c) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
    have hcpow : c ^ (2 * k + 1) = c := by rw [pow_succ, pow_mul, hz2, one_pow, one_mul]
    rw [hcomm.mul_pow, hcpow] at h1
    have h3 : c = (a ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_right h1
    exact h.z_not_mem_A (by rw [h3]; exact inv_mem (pow_mem ha _))

end Odd

section Shape

variable {G : Type*} [Group G] {z t : G}

theorem center_S_gen {S : Subgroup G} (hSD : Nonempty (↥S ≃* DihedralGroup 4)) (htS : t ∈ S)
    (hSt : ∀ s ∈ S, s * t = t * s) (ht2 : t * t = 1) (ht1 : t ≠ 1) {c : G} (hcS : c ∈ S)
    (hc : ∀ s ∈ S, c * s = s * c) : c = 1 ∨ c = t := by
  obtain ⟨eS, hc_cen, hc_sq, hc_ne⟩ := tD8_gen hSD htS hSt ht2 ht1
  have hx : ∀ y, y * eS ⟨c, hcS⟩ = eS ⟨c, hcS⟩ * y := by
    intro y
    obtain ⟨u, rfl⟩ := eS.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg eS (Subtype.ext (hc u u.2).symm)
  rcases d8_center _ hc_cen hc_sq hc_ne _ hx with h1 | h1
  · left
    have := eS.injective (h1.trans (map_one eS).symm)
    exact congrArg Subtype.val this
  · right
    have := eS.injective h1
    exact congrArg Subtype.val this

theorem exists_alpha_gen {S : Subgroup G} (hSD : Nonempty (↥S ≃* DihedralGroup 4)) (htS : t ∈ S)
    (hzS : z ∈ S) (hSt : ∀ s ∈ S, s * t = t * s) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzt : z ≠ t) : ∃ α, AlphaSpec S z t α := by
  obtain ⟨eS, hc_cen, hc_sq, hc_ne⟩ := tD8_gen hSD htS hSt ht2 ht1
  set c : DihedralGroup 4 := eS ⟨t, htS⟩ with hc
  set d : DihedralGroup 4 := eS ⟨z, hzS⟩ with hd
  have hd_sq : d * d = 1 := by
    rw [hd, ← map_mul, ← map_one eS]
    exact congrArg eS (Subtype.ext hz2)
  have hd_ne : d ≠ 1 := by
    intro h1
    apply hz1
    have := eS.injective (h1.trans (map_one eS).symm)
    exact congrArg Subtype.val this
  have hdc : d ≠ c := by
    intro h1
    apply hzt
    have := eS.injective h1
    exact congrArg Subtype.val this
  obtain ⟨a, ha2, had, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    d8_exists c d hc_cen hc_sq hc_ne hd_sq hd_ne hdc
  have hlist := d8_list c d a hc_cen hc_sq hc_ne hd_sq hd_ne hdc ha2 had
  let ι : DihedralGroup 4 → G := fun x => ((eS.symm x : S) : G)
  have ι_mul : ∀ x y, ι (x * y) = ι x * ι y := fun x y => by
    simp [ι, map_mul, Subgroup.coe_mul]
  have ι_inj : ∀ x y, ι x = ι y → x = y := fun x y hxy =>
    eS.symm.injective (Subtype.ext hxy)
  have ι_c : ι c = t := by simp [ι, hc]
  have ι_d : ι d = z := by simp [ι, hd]
  have ι_one : ι 1 = 1 := by simp [ι]
  have ι_mem : ∀ x, ι x ∈ S := fun x => (eS.symm x).2
  have ne_of : ∀ x y, x ≠ y → ι x ≠ ι y := fun x y hxy hh => hxy (ι_inj x y hh)
  refine ⟨ι a, ⟨ι_mem a, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [← ι_mul, ha2, ι_one]
  · rw [← ι_d, ← ι_c, ← ι_mul, ← ι_mul, ← ι_mul, had]
  · rw [← ι_one]; exact ne_of _ _ h1
  · rw [← ι_c]; exact ne_of _ _ h2
  · rw [← ι_d]; exact ne_of _ _ h3
  · rw [← ι_d, ← ι_c, ← ι_mul]; exact ne_of _ _ h4
  · rw [← ι_d, ← ι_mul, ← ι_one]; exact ne_of _ _ h5
  · rw [← ι_d, ← ι_mul, ← ι_c]; exact ne_of _ _ h6
  · rw [← ι_d, ← ι_mul]; exact ne_of _ _ h7
  · rw [← ι_d, ← ι_c, ← ι_mul, ← ι_mul]; exact ne_of _ _ h8
  · rw [← ι_d, ← ι_mul]; exact ne_of _ _ h9
  · rw [← ι_d, ← ι_c, ← ι_mul, ← ι_mul]; exact ne_of _ _ h10
  · intro s hs
    have hx := hlist (eS ⟨s, hs⟩)
    have hs' : ι (eS ⟨s, hs⟩) = s := by simp [ι]
    rw [← hs']
    rcases hx with hx | hx | hx | hx | hx | hx | hx | hx
    · left; rw [hx, ι_one]
    · right; left; rw [hx, ι_c]
    · right; right; left; rw [hx, ι_d]
    · right; right; right; left; rw [hx, ι_mul, ι_d, ι_c]
    · right; right; right; right; left; rw [hx]
    · right; right; right; right; right; left; rw [hx, ι_mul, ι_c]
    · right; right; right; right; right; right; left; rw [hx, ι_mul, ι_d]
    · right; right; right; right; right; right; right; rw [hx, ι_mul, ι_mul, ι_d, ι_c]

end Shape

section CentU

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}

omit [Finite G] in
theorem outer_cent_U (h : OuterE G L z t T E) (hW : WFacts L t E) {S : Subgroup G}
    (hSC : S ≤ centralizer (E : Set G)) (hzS : z ∈ S) (htS : t ∈ S)
    (hD8 : Nonempty (S ≃* DihedralGroup 4))
    (hodd : ∃ N : Subgroup (centralizer (E : Set G)), N.Normal ∧
      (∀ x, x ∈ N ↔ Odd (orderOf x)) ∧
      N ⊓ S.subgroupOf (centralizer (E : Set G)) = ⊥ ∧
      (N : Set (centralizer (E : Set G))) *
        (S.subgroupOf (centralizer (E : Set G)) : Set (centralizer (E : Set G))) = Set.univ)
    {c : G} (hc : ∀ u ∈ S ⊔ E, c * u = u * c) : c = 1 ∨ c = t := by
  obtain ⟨N, hNn, hNodd, hNS, hNprod⟩ := hodd
  have hcfg := h.cfg
  have hEt : t ∈ E := h.econfig.t_mem
  have hSt : ∀ s ∈ S, s * t = t * s := fun s hs => (mem_centralizer_iff.1 (hSC hs) t hEt).symm
  have hcCE : c ∈ centralizer (E : Set G) :=
    mem_centralizer_iff.2 fun e he => (hc e (mem_sup_right he)).symm
  have hmem : (⟨c, hcCE⟩ : ↥(centralizer (E : Set G))) ∈
      (N : Set ↥(centralizer (E : Set G))) *
        (S.subgroupOf (centralizer (E : Set G)) : Set ↥(centralizer (E : Set G))) := by
    rw [hNprod]; exact Set.mem_univ _
  obtain ⟨n', hn', s', hs', hns⟩ := Set.mem_mul.1 hmem
  have hcns : (n' : G) * (s' : G) = c := congrArg Subtype.val hns
  have hs : (s' : G) ∈ S := mem_subgroupOf.1 hs'
  have hn_odd : Odd (orderOf (n' : G)) := by
    rw [Subgroup.orderOf_coe]; exact (hNodd n').1 hn'
  set n : G := (n' : G) with hn_def
  set s : G := (s' : G) with hs_def
  let zc : ↥(centralizer (E : Set G)) := ⟨z, hSC hzS⟩
  have hcz : c * z = z * c := hc z (mem_sup_left hzS)
  have hm1 : (zc⁻¹ * n'⁻¹ * zc⁻¹⁻¹) * n' ∈ N :=
    mul_mem (hNn.conj_mem _ (inv_mem hn') _) hn'
  have hmG : z⁻¹ * n⁻¹ * z * n = z⁻¹ * s * z * s⁻¹ := by
    have h1 : n * s * z = z * (n * s) := by rw [hcns]; exact hcz
    calc z⁻¹ * n⁻¹ * z * n = z⁻¹ * (n⁻¹ * (z * (n * s)) * s⁻¹) := by group
      _ = z⁻¹ * (n⁻¹ * (n * s * z) * s⁻¹) := by rw [h1]
      _ = z⁻¹ * s * z * s⁻¹ := by group
  have hmS : (zc⁻¹ * n'⁻¹ * zc⁻¹⁻¹) * n' ∈ S.subgroupOf (centralizer (E : Set G)) := by
    rw [mem_subgroupOf]
    have : (((zc⁻¹ * n'⁻¹ * zc⁻¹⁻¹) * n' : ↥(centralizer (E : Set G))) : G) =
        z⁻¹ * n⁻¹ * z * n := by
      simp [zc, hn_def]
    rw [this, hmG]
    exact mul_mem (mul_mem (mul_mem (inv_mem hzS) hs) hzS) (inv_mem hs)
  have hm_one : (zc⁻¹ * n'⁻¹ * zc⁻¹⁻¹) * n' = 1 := by
    have : (zc⁻¹ * n'⁻¹ * zc⁻¹⁻¹) * n' ∈ N ⊓ S.subgroupOf (centralizer (E : Set G)) :=
      ⟨hm1, hmS⟩
    rw [hNS, mem_bot] at this
    exact this
  have hmG1 : z⁻¹ * n⁻¹ * z * n = 1 := by
    have := congrArg (fun y : ↥(centralizer (E : Set G)) => (y : G)) hm_one
    simpa [zc, hn_def] using this
  have hnz : z * n = n * z := by
    have h1 : n⁻¹ * z * n = z := by
      have : z⁻¹ * (n⁻¹ * z * n) = 1 := by rw [← hmG1]; group
      exact (inv_mul_eq_one.1 this).symm
    calc z * n = n * (n⁻¹ * z * n) := by group
      _ = n * z := by rw [h1]
  have hsz : s * z = z * s := by
    have h1 : z⁻¹ * s * z * s⁻¹ = 1 := by rw [← hmG, hmG1]
    have h2 : z⁻¹ * s * z = s := by
      have := congrArg (· * s) h1
      simpa using this
    calc s * z = z * (z⁻¹ * s * z) := by group
      _ = z * s := by rw [h2]
  have hnL : n ∈ L := hcfg.odd_mem_A (mem_centralizer_singleton_iff.2 hnz.symm) hn_odd
  have ht_order : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hcfg.t_sq) hcfg.t_ne
  have hn1 : n = 1 := by
    rcases hW.cent n hnL (fun e he => (mem_centralizer_iff.1 n'.2 e he).symm) with h1 | h1
    · exact h1
    · exfalso
      rw [h1, ht_order] at hn_odd
      exact absurd hn_odd (by decide)
  have hcs : c = s := by rw [← hcns, hn1, one_mul]
  have hcS : c ∈ S := hcs ▸ hs
  exact center_S_gen hD8 htS hSt hcfg.t_sq hcfg.t_ne hcS (fun u hu => hc u (mem_sup_left hu))

end CentU

@[expose] def Fin76bOuterS8₄ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T E : Subgroup G) (Q : Sylow 2 G)
    (x : G) (B : Subgroup G) (β : G), StdHyp G L → (IsSporadic L .J2 ∨ IsSporadic L .J3) →
    (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2 →
    OuterE G L z t T E → Nat.card (MulAut ↥E) = 1920 → Nat.card ↥T = 512 → WFacts L t E →
    (∀ m ∈ normalizer (E : Set G), ∃ c ∈ centralizer (E : Set G),
      ∃ n ∈ normalizer (E : Set G), n ∈ centralizer ({z} : Set G) ∧ m = c * n) →
    (∀ v ∈ centralizer (E : Set G), v * z = z * v → v = 1 ∨ v = z ∨ v = t ∨ v = t * z) →
    OuterB L t B β → Nat.card ↥(E ⊓ centralizer ({β} : Set G)) = 8 →
    (∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
      z ∈ S → OuterSylowFacts z E S ∧ ∀ b ∈ B, ∀ s ∈ S, b * s = s * b) →
    T ≤ (Q : Subgroup G) → x ∈ (Q : Subgroup G) → x ∉ T →
    x ∈ normalizer (T : Set G) → x * z * x⁻¹ = z * t → x * t * x⁻¹ = t →
    (∀ q ∈ (Q : Subgroup G), q * t = t * q) → (Q : Subgroup G) ⊓ centralizer ({z} : Set G) = T →
    z ∈ (commutator ↥(centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype →
    (∃ hz : z ∈ centralizer ({β} : Set G), Lemma96Conclusion ↥(centralizer ({β} : Set G))
      (QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))))) →
    (∀ y ∈ centralizer ({z} : Set G), y * y ∈ L) →
    (∃ σ ∈ T, σ * σ = 1 ∧ σ ∉ L ⊔ zpowers z) → (∀ g : G, g * z * g⁻¹ ∉ L) →
    (∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ centralizer (E : Set G) ∧
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) ∧
      z ∈ S ∧ Nonempty (S ≃* DihedralGroup 4) ∧ (∃ α : G, AlphaSpec S z t α) ∧
      (∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t) ∧
      (∃ N : Subgroup (centralizer (E : Set G)), N.Normal ∧ (∀ x, x ∈ N ↔ Odd (orderOf x)) ∧
        N ⊓ S.subgroupOf (centralizer (E : Set G)) = ⊥ ∧
        (N : Set (centralizer (E : Set G))) *
          (S.subgroupOf (centralizer (E : Set G)) : Set (centralizer (E : Set G))) =
            Set.univ) ∧
      (∀ b ∈ B, ∀ s ∈ S, b * s = s * b) ∧
      (∀ c : G, (∀ u ∈ S ⊔ E, c * u = u * c) → c = 1 ∨ c = t) ∧
      (∀ g : G, g * z * g⁻¹ ∈ S ⊔ E →
        ∃ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), m * z * m⁻¹ = g * z * g⁻¹)) →
    False

theorem fin76bOuterS8₃_of_s8₄ (h4 : Fin76bOuterS8₄) : Fin76bOuterS8₃ := by
  intro G _ _ L z t T E Q x B β h hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
    hxz hxt htQ hQz hcomm hconc hsq hσ h98 hS3
  obtain ⟨S, hS2, hSC, hSmax, hzS, hD8, h67, hodd, hBS, h112⟩ := hS3
  have hcfg := hE.cfg
  have htE : t ∈ E := hE.econfig.t_mem
  have htc : ∀ e ∈ E, e * t = t * e := fun e he => hcfg.t_central e (hE.E_le_T he)
  have htS : t ∈ S := mem_of_maximal hS2 hSC hSmax hcfg.t_sq htE htc
  have hSt : ∀ s ∈ S, s * t = t * s := fun s hs => (mem_centralizer_iff.1 (hSC hs) t htE).symm
  have hα := exists_alpha_gen hD8 htS hzS hSt hcfg.t_sq hcfg.t_ne hcfg.z_sq hcfg.z_ne hcfg.z_ne_t
  exact h4 G L z t T E Q x B β h hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
    hxz hxt htQ hQz hcomm hconc hsq hσ h98
    ⟨S, hS2, hSC, hSmax, hzS, hD8, hα, h67, hodd, hBS,
      fun c hc => outer_cent_U hE hW hSC hzS htS hD8 hodd hc, h112⟩

end CFSG.EvenSporadicStandard.Fin76b
