module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerCheckFacts
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTransfer

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G}

theorem two_mul_card_le {H R : Subgroup G} (hHR : H ≤ R) {c : G} (hcR : c ∈ R) (hcH : c ∉ H) :
    2 * Nat.card H ≤ Nat.card R := by
  have h := relIndex_mul_card (H := H) (K := R)
  rw [inf_of_le_left hHR] at h
  have h1 : H.relIndex R ≠ 1 := fun h1 => hcH (relIndex_eq_one.1 h1 hcR)
  have h0 : H.relIndex R ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := R)).ne' h.symm
  rw [← h]
  have : 2 ≤ H.relIndex R := by omega
  exact Nat.mul_le_mul_right _ this

theorem card_le_of_isSylowIn {P H R : Subgroup G}
    (hP : CFSG.GH74.GLS.Bg.Thompson.IsSylowIn 2 P H) (hRH : R ≤ H) (hR : IsPGroup 2 R) :
    Nat.card R ≤ Nat.card P := by
  obtain ⟨hPH, -, hodd⟩ := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hR
  have h1 : Nat.card R ∣ Nat.card H := card_dvd_of_le hRH
  have h2 := relIndex_mul_card (H := P) (K := H)
  rw [inf_of_le_left hPH] at h2
  rw [← h2, ha] at h1
  have hcop : Nat.Coprime (2 ^ a) (P.relIndex H) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have h3 : 2 ^ a ∣ Nat.card P := hcop.dvd_of_dvd_mul_left h1
  rw [ha]
  exact Nat.le_of_dvd Nat.card_pos h3

abbrev conjMap (g : G) (S : Subgroup G) : Subgroup G := S.map (MulAut.conj g).toMonoidHom

theorem card_conjMap (g : G) (S : Subgroup G) : Nat.card (conjMap g S) = Nat.card S :=
  card_map_of_injective (MulAut.conj g).injective

theorem conjMap_le_cent {g x : G} {S : Subgroup G} (hS : S ≤ centralizer {x}) :
    conjMap g S ≤ centralizer {g * x * g⁻¹} := by
  rintro _ ⟨s, hs, rfl⟩
  have h := mem_centralizer_singleton_iff.1 (hS hs)
  rw [mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * s * g⁻¹ * (g * x * g⁻¹) = g * (s * x) * g⁻¹ := by group
    _ = g * (x * s) * g⁻¹ := by rw [h]
    _ = g * x * g⁻¹ * (g * s * g⁻¹) := by group

variable (ht : CentHyp t)
include ht

theorem pinv_of_conj {K : Subgroup G} (hK : IsPGroup 2 K) {g x : G} (hx : x = g * t * g⁻¹)
    (h8 : 2 ^ 8 ≤ Nat.card (K ⊓ centralizer {x} : Subgroup G)) :
    PInv (K ⊓ centralizer {x} : Subgroup G) := by
  subst hx
  have hS : conjMap g⁻¹ (K ⊓ centralizer {g * t * g⁻¹}) ≤ centralizer {t} := by
    have h := conjMap_le_cent (g := g⁻¹) (x := g * t * g⁻¹)
      (S := K ⊓ centralizer {g * t * g⁻¹}) inf_le_right
    rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at h
  have hp : IsPGroup 2 (conjMap g⁻¹ (K ⊓ centralizer {g * t * g⁻¹})) :=
    (hK.to_le inf_le_left).map _
  have hcard := card_conjMap g⁻¹ (K ⊓ centralizer {g * t * g⁻¹})
  have hle := ht.card_le _ hS hp
  have h8' : Nat.card (conjMap g⁻¹ (K ⊓ centralizer {g * t * g⁻¹})) = 2 ^ 8 := by omega
  have hP := ht.pinv _ hS hp h8'
  exact pinv_of_mulEquiv ((K ⊓ centralizer {g * t * g⁻¹}).equivMapOfInjective _
    (MulAut.conj g⁻¹).injective).symm hP

theorem pinvol_t {K : Subgroup G} (hK : IsPGroup 2 K) (htK : t ∈ K) (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) (hC : Nat.card (K ⊓ centralizer {t} : Subgroup G) = 2 ^ 8) :
    IsPInvol K t :=
  ⟨htK, ht2, ht1, pinv_of_conj ht hK (g := 1) (by group) hC.ge⟩

theorem index_even_of_transfer [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {K Q : Subgroup G} (hK : IsPGroup 2 K) (htK : t ∈ K) (ht2 : t ^ 2 = 1)
    (hC : Nat.card (K ⊓ centralizer {t} : Subgroup G) = 2 ^ 8) (hQK : Q ≤ K)
    (hQ : Q.relIndex K = 2) (htQ : t ∉ Q) (hQP : ∀ x ∈ Q, ¬ IsPInvol K x) : 2 ∣ K.index := by
  by_contra hidx
  obtain ⟨g, hgQ, hext, -⟩ :=
    CFSG.ComponentClassification.HarrisLit.HarrisEnd.exists_extremal_conj_of_relIndex_two hnab
      hK hidx hQK hQ htK htQ ht2
  apply hQP _ hgQ
  have hxK : g⁻¹ * t * g ∈ K := hQK hgQ
  have h8 : 2 ^ 8 ≤ Nat.card (K ⊓ centralizer {g⁻¹ * t * g} : Subgroup G) := by
    have hR : conjMap g⁻¹ (K ⊓ centralizer {t}) ≤ centralizer {g⁻¹ * t * g} := by
      have h := conjMap_le_cent (g := g⁻¹) (x := t) (S := K ⊓ centralizer {t}) inf_le_right
      rwa [inv_inv] at h
    have hRp : IsPGroup 2 (conjMap g⁻¹ (K ⊓ centralizer {t})) := (hK.to_le inf_le_left).map _
    have := card_le_of_isSylowIn hext hR hRp
    rwa [card_conjMap, hC] at this
  refine ⟨hxK, ?_, ?_, pinv_of_conj ht hK (g := g⁻¹) (by group) h8⟩
  · rw [show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by group, conj_pow, ht2]
    group
  · intro h1
    apply htQ
    have : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    rw [this, h1, mul_one, mul_inv_cancel]
    exact one_mem Q

omit ht in
theorem exists_normalizer_sq {K : Subgroup G} (hK : IsPGroup 2 K) (hidx : 2 ∣ K.index) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ K ≤ P ∧ ∃ y ∈ P, y ∈ normalizer (K : Set G) ∧ y ∉ K ∧
      y ^ 2 ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hKP⟩ := hK.exists_le_sylow
  have hne : K.subgroupOf (P : Subgroup G) ≠ ⊤ := by
    intro htop
    have hPK : (P : Subgroup G) ≤ K := fun x hx => by
      have h : (⟨x, hx⟩ : P) ∈ K.subgroupOf (P : Subgroup G) := by rw [htop]; trivial
      exact mem_subgroupOf.1 h
    have h := le_antisymm hKP hPK
    exact P.not_dvd_index (h ▸ hidx)
  have hnil : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent (G := P) _ (lt_of_le_of_ne le_top hne)
  obtain ⟨⟨y₀, hy₀P⟩, hy₀N, hy₀K⟩ := SetLike.exists_of_lt hlt
  have hy₀N' : y₀ ∈ normalizer (K : Set G) := by
    have h : (⟨y₀, hy₀P⟩ : P) ∈ (normalizer (K : Set G)).subgroupOf (P : Subgroup G) := by
      rw [subgroupOf_normalizer_eq hKP]
      exact hy₀N
    exact mem_subgroupOf.1 h
  have hy₀K' : y₀ ∉ K := fun h => hy₀K (mem_subgroupOf.2 h)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') ⟨y₀, hy₀P⟩
  have hm' : orderOf y₀ = 2 ^ m := by rw [← hm, Subgroup.orderOf_mk]
  have hex : ∃ j, y₀ ^ (2 ^ (j + 1)) ∈ K := by
    refine ⟨m, ?_⟩
    rw [pow_succ, pow_mul, ← hm', pow_orderOf_eq_one, one_pow]
    exact one_mem K
  classical
  obtain ⟨j, hjK, hmin⟩ : ∃ j, y₀ ^ (2 ^ (j + 1)) ∈ K ∧ ∀ i < j, y₀ ^ (2 ^ (i + 1)) ∉ K :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hjK' : y₀ ^ (2 ^ j) ∉ K := by
    rcases j with _ | j'
    · rw [pow_zero, pow_one]
      exact hy₀K'
    · exact hmin j' (by omega)
  refine ⟨P, P.isPGroup', hKP, y₀ ^ (2 ^ j), pow_mem hy₀P _, pow_mem hy₀N' _, hjK', ?_⟩
  rw [← pow_mul, ← pow_succ]
  exact hjK

theorem level1_step [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {K Q : Subgroup G}
    (hK : IsPGroup 2 K) (htK : t ∈ K) (ht2 : t ^ 2 = 1) (hQK : Q ≤ K) (hQ : Q.relIndex K = 2)
    (htQ : t ∉ Q)
    (hin : ∀ x ∈ Q, x ^ 2 = 1 → x ≠ 1 →
      2 ^ 8 ≤ Nat.card (K ⊓ centralizer {x} : Subgroup G) ∧
        ¬ PInv (K ⊓ centralizer {x} : Subgroup G))
    (hout : ∀ x ∈ K, x ^ 2 = 1 → x ≠ 1 → x ∉ Q → ∃ k ∈ K, x = k * t * k⁻¹) :
    ∃ c ∈ normalizer (K : Set G), c ∉ K ∧ c ^ 2 ∈ K ∧ c * t = t * c := by
  have ht1 : t ≠ 1 := fun h => htQ (h ▸ one_mem Q)
  have hno : ∀ g : G, g * t * g⁻¹ ∉ Q := by
    intro g hg
    have hx2 : (g * t * g⁻¹) ^ 2 = 1 := by rw [conj_pow, ht2]; group
    have hx1 : g * t * g⁻¹ ≠ 1 := fun h => ht1 (by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
    obtain ⟨h8, hnot⟩ := hin _ hg hx2 hx1
    exact hnot (pinv_of_conj ht hK rfl h8)
  have hidx : 2 ∣ K.index := by
    by_contra hidx
    obtain ⟨g, hgQ, -, -⟩ :=
      CFSG.ComponentClassification.HarrisLit.HarrisEnd.exists_extremal_conj_of_relIndex_two hnab
        hK hidx hQK hQ htK htQ ht2
    exact hno g⁻¹ (by rwa [inv_inv])
  obtain ⟨-, -, -, y, -, hyN, hyK, hy2⟩ := exists_normalizer_sq hK hidx
  have hxK : y⁻¹ * t * y ∈ K := inv_conj_mem hyN htK
  have hx2 : (y⁻¹ * t * y) ^ 2 = 1 := by
    rw [show y⁻¹ * t * y = y⁻¹ * t * y⁻¹⁻¹ by group, conj_pow, ht2]; group
  have hx1 : y⁻¹ * t * y ≠ 1 := fun h => ht1 (by
    calc t = y * (y⁻¹ * t * y) * y⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hxQ : y⁻¹ * t * y ∉ Q := by
    have := hno y⁻¹
    rwa [inv_inv] at this
  obtain ⟨k, hk, hxk⟩ := hout _ hxK hx2 hx1 hxQ
  refine ⟨y * k, mul_mem hyN (le_normalizer hk), fun h => hyK ?_, ?_, ?_⟩
  · rw [show y = y * k * k⁻¹ by group]
    exact mul_mem h (inv_mem hk)
  · rw [show (y * k) ^ 2 = y ^ 2 * (y⁻¹ * k * y) * k by rw [sq, sq]; group]
    exact mul_mem (mul_mem hy2 (inv_conj_mem hyN hk)) hk
  · calc y * k * t = y * (k * t * k⁻¹) * k := by group
      _ = y * (y⁻¹ * t * y) * k := by rw [hxk]
      _ = t * (y * k) := by group

theorem level2_step [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {K Q : Subgroup G}
    (hK : IsPGroup 2 K) (htK : t ∈ K) (ht2 : t ^ 2 = 1)
    (hC : Nat.card (K ⊓ centralizer {t} : Subgroup G) = 2 ^ 8) (hQK : Q ≤ K)
    (hQ : Q.relIndex K = 2) (htQ : t ∉ Q) (hQP : ∀ x ∈ Q, ¬ IsPInvol K x) {x₀ : G}
    (hcls : ∀ x, IsPInvol K x → (∃ k ∈ K, x = k * t * k⁻¹) ∨ ∃ k ∈ K, x = k * x₀ * k⁻¹) :
    (∀ k ∈ K, x₀ ≠ k * t * k⁻¹) ∧
      ∃ c ∈ normalizer (K : Set G), c ∉ K ∧ c ^ 2 ∈ K ∧ c * x₀ * c⁻¹ = t := by
  have ht1 : t ≠ 1 := fun h => htQ (h ▸ one_mem Q)
  have hidx := index_even_of_transfer ht hnab hK htK ht2 hC hQK hQ htQ hQP
  obtain ⟨P, hP, hKP, y, hyP, hyN, hyK, hy2⟩ := exists_normalizer_sq hK hidx
  have hx : IsPInvol K (y⁻¹ * t * y) := by
    have := pinvol_conj (inv_mem hyN) (pinvol_t ht hK htK ht2 ht1 hC)
    rwa [inv_inv] at this
  have hnt : ∀ k ∈ K, y⁻¹ * t * y ≠ k * t * k⁻¹ := by
    intro k hk hxk
    have hc : y * k * t = t * (y * k) := by
      calc y * k * t = y * (k * t * k⁻¹) * k := by group
        _ = y * (y⁻¹ * t * y) * k := by rw [hxk]
        _ = t * (y * k) := by group
    have hcK : y * k ∉ K := fun h => hyK (by
      rw [show y = y * k * k⁻¹ by group]; exact mul_mem h (inv_mem hk))
    have hcP : y * k ∈ P := mul_mem hyP (hKP hk)
    have hle : K ⊓ centralizer {t} ≤ P ⊓ centralizer {t} := inf_le_inf_right _ hKP
    have hcR : y * k ∈ P ⊓ centralizer {t} := mem_inf.2 ⟨hcP, mem_centralizer_singleton_iff.2 hc⟩
    have h2 := two_mul_card_le hle hcR (fun h => hcK (mem_inf.1 h).1)
    have h3 := ht.card_le _ inf_le_right (hP.to_le inf_le_left)
    rw [hC] at h2
    omega
  refine ⟨fun k hk hx₀ => ?_, ?_⟩
  ·
    rcases hcls _ hx with ⟨k', hk', hxk⟩ | ⟨k', hk', hxk⟩
    · exact hnt k' hk' hxk
    · exact hnt (k' * k) (mul_mem hk' hk) (by rw [hxk, hx₀]; group)
  · rcases hcls _ hx with ⟨k, hk, hxk⟩ | ⟨k, hk, hxk⟩
    · exact absurd hxk (hnt k hk)
    · refine ⟨y * k, mul_mem hyN (le_normalizer hk), fun h => hyK ?_, ?_, ?_⟩
      · rw [show y = y * k * k⁻¹ by group]
        exact mul_mem h (inv_mem hk)
      · rw [show (y * k) ^ 2 = y ^ 2 * (y⁻¹ * k * y) * k by rw [sq, sq]; group]
        exact mul_mem (mul_mem hy2 (inv_conj_mem hyN hk)) hk
      · calc y * k * x₀ * (y * k)⁻¹ = y * (k * x₀ * k⁻¹) * y⁻¹ := by group
          _ = y * (y⁻¹ * t * y) * y⁻¹ := by rw [hxk]
          _ = t := by group

theorem level3_false [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {K Q : Subgroup G}
    (hK : IsPGroup 2 K) (htK : t ∈ K) (ht2 : t ^ 2 = 1)
    (hC : Nat.card (K ⊓ centralizer {t} : Subgroup G) = 2 ^ 8) (hQK : Q ≤ K)
    (hQ : Q.relIndex K = 2) (htQ : t ∉ Q)
    (hcls : ∀ x, IsPInvol K x → ∃ k ∈ K, x = k * t * k⁻¹) : False := by
  have hn : (Q.subgroupOf K).Normal := normal_of_index_eq_two hQ
  have hQP : ∀ x ∈ Q, ¬ IsPInvol K x := by
    intro x hxQ hx
    obtain ⟨k, hk, rfl⟩ := hcls x hx
    apply htQ
    have h := hn.conj_mem ⟨k * t * k⁻¹, hQK hxQ⟩ (mem_subgroupOf.2 hxQ) ⟨k⁻¹, inv_mem hk⟩
    rw [mem_subgroupOf] at h
    simpa [mul_assoc] using h
  have h := (level2_step ht hnab hK htK ht2 hC hQK hQ htQ hQP (x₀ := t)
    (fun x hx => Or.inl (hcls x hx))).1 1 (one_mem K)
  exact h (by group)

end CFSG.OddStandard.AltStdSmall4.Tower
