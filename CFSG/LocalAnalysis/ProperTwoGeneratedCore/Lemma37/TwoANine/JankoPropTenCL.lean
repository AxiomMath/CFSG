module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTenFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTenCoprime

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G]

variable {z : G} {fr : JankoFrame G z}

namespace Hyp

theorem C₁_inf_t_le (h : Hyp fr) :
    centralizer (fr.P₁ : Set G) ⊓ centralizer ({fr.t} : Set G) ≤ fr.At ⊔ fr.F₁ := by
  rintro x ⟨hxC, hxt⟩
  rw [centralizer_P₁_eq h] at hxC
  have hFM : fr.F ≤ normalizer (fr.M : Set G) :=
    fr.F_le_centralizer.trans (C₁_le_normalizer_M fr)
  have hx' : x ∈ ((fr.M ⊔ fr.F : Subgroup G) : Set G) := hxC
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hFM] at hx'
  obtain ⟨m, hm, f, hf, rfl⟩ := Set.mem_mul.mp hx'
  have htx : fr.t * (m * f) * fr.t⁻¹ = m * f := by
    rw [← mem_centralizer_singleton_iff.mp hxt]; group
  have hm' : fr.t * m * fr.t⁻¹ ∈ fr.M := conj_mem_of_le_normalizer le_rfl
    (t_mem_normalizer_M fr) hm
  have hf' : fr.t * f * fr.t⁻¹ ∈ fr.F := conj_mem_of_le_normalizer le_rfl
    fr.t_mem_normalizer_F hf
  have hmf : m⁻¹ * (fr.t * m * fr.t⁻¹) = f * (fr.t * f * fr.t⁻¹)⁻¹ := by
    have : (fr.t * m * fr.t⁻¹) * (fr.t * f * fr.t⁻¹) = m * f := by rw [← htx]; group
    calc m⁻¹ * (fr.t * m * fr.t⁻¹) = m⁻¹ * ((fr.t * m * fr.t⁻¹) * (fr.t * f * fr.t⁻¹)) *
          (fr.t * f * fr.t⁻¹)⁻¹ := by group
      _ = f * (fr.t * f * fr.t⁻¹)⁻¹ := by rw [this]; group
  have h1 : m⁻¹ * (fr.t * m * fr.t⁻¹) ∈ fr.M ⊓ fr.F :=
    ⟨fr.M.mul_mem (fr.M.inv_mem hm) hm', hmf ▸ fr.F.mul_mem hf (fr.F.inv_mem hf')⟩
  rw [M_inf_F h, mem_bot] at h1
  have hmt : fr.t * m * fr.t⁻¹ = m := by
    rw [← mul_left_cancel_iff (a := m⁻¹), h1, inv_mul_cancel]
  have hft : fr.t * f * fr.t⁻¹ = f := by
    have h2 : f * (fr.t * f * fr.t⁻¹)⁻¹ = 1 := hmf ▸ h1
    rw [mul_inv_eq_one] at h2
    exact h2.symm
  have hmA : m ∈ fr.At := ⟨hm, mem_centralizer_singleton_iff.mpr (by
    calc m * fr.t = fr.t * m * fr.t⁻¹ * fr.t := by rw [hmt]
      _ = fr.t * m := by group)⟩
  have hfF : f ∈ fr.F₁ := by
    rw [fr.F₁_eq]
    refine ⟨hf, mem_centralizer_singleton_iff.mpr ?_⟩
    calc f * fr.t = fr.t * f * fr.t⁻¹ * fr.t := by rw [hft]
      _ = fr.t * f := by group
  exact mul_mem (mem_sup_left hmA) (mem_sup_right hfF)

theorem card_At_sup_F₁
    (h : Hyp fr) : Nat.card (fr.At ⊔ fr.F₁ : Subgroup G) = 216 := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    (F₁_le_normalizer_At fr) ?_, card_At h, fr.card_F₁]
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hxA, hxF⟩
  have : x ∈ fr.M ⊓ fr.F := ⟨At_le_M fr hxA, F₁_le_F fr hxF⟩
  rwa [M_inf_F h] at this

theorem card_le_of_le_C₁_t
    (h : Hyp fr) {R : Subgroup G} (hR : IsPGroup 3 R)
    (hRC : R ≤ centralizer (fr.P₁ : Set G)) (hRt : R ≤ centralizer ({fr.t} : Set G)) :
    Nat.card R ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : Nat.card R ∣ 216 :=
    card_At_sup_F₁ h ▸ Subgroup.card_dvd_of_le ((le_inf hRC hRt).trans (C₁_inf_t_le h))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
  rw [hk] at hdvd ⊢
  have hk3 : k ≤ 3 := by
    by_contra hcon
    have : 3 ^ 4 ∣ 216 := (pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at this
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 27 := by norm_num

theorem false_of_sylow
    (h : Hyp fr) (N₀ : Sylow 3 G) (y : G) (hy : IsConj y fr.s₁)
    (hZ : (N₀ : Subgroup G) ⊓ centralizer ((N₀ : Subgroup G) : Set G) = zpowers y)
    (Q : Subgroup G) (hQA : Q ≤ fr.At) (hQ3 : Nat.card Q = 3) (X₀ : Subgroup G)
    (hX₀ : IsPGroup 3 X₀) (hX₀P₁ : X₀ ≤ normalizer (fr.P₁ : Set G))
    (hX₀Q : X₀ ≤ normalizer (Q : Set G)) (htX₀ : fr.t ∈ normalizer (X₀ : Set G))
    (hcard : Nat.card X₀ * 3 = Nat.card N₀) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hqQ, hq1⟩ := Walter.J1.exists_ne_one_of_card hQ3 (by norm_num)
  have hQq : Q = zpowers q := Walter.J1.eq_zpowers_of_card_prime Nat.prime_three hQ3 hqQ hq1
  have hqA : q ∈ fr.At := hQA hqQ
  have hq3 : orderOf q = 3 := by rw [← Nat.card_zpowers, ← hQq, hQ3]
  have hqs₃ : IsConj q fr.s₃ := isConj_of_mem_At h hqA hq1
  have hX₀C₁ : X₀ ≤ centralizer (fr.P₁ : Set G) := by
    rw [fr.P₁_eq] at hX₀P₁ ⊢
    exact le_centralizer_of_isPGroup fr.orderOf_s₁ hX₀ hX₀P₁
  have hX₀CQ : X₀ ≤ centralizer (Q : Set G) := by
    rw [hQq] at hX₀Q ⊢
    exact le_centralizer_of_isPGroup hq3 hX₀ hX₀Q
  have hCQq : centralizer (Q : Set G) ≤ centralizer ({q} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hqQ)
  have hCQ2 : ∀ B : Subgroup G, B ≤ centralizer (Q : Set G) → IsPGroup 2 B → Nat.card B ≤ 2 :=
    fun B hB hB2 => h.p7.card_le_two q hqs₃ B (hB.trans hCQq) hB2
  obtain ⟨W, hWC, hCW, hWodd, hW⟩ := exists_oddNormal hCQ2
  have hQC : Q ≤ centralizer (Q : Set G) := by
    rw [hQq]; exact Subgroup.le_centralizer _
  have hX₀W : X₀ ≤ W := hW X₀ hX₀CQ (odd_card_of_isPGroup (by decide) hX₀)
  have hQ3' : IsPGroup 3 Q := IsPGroup.of_card (n := 1) (by rw [hQ3, pow_one])
  have hQW : Q ≤ W := hW Q hQC (by rw [hQ3]; decide)
  have hWQ : W ≤ normalizer (Q : Set G) :=
    hWC.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨S, hS⟩ := (hX₀.comap_subtype (K := W)).exists_le_sylow
  set X' := (S : Subgroup W).map W.subtype with hX'
  have hX₀X' : X₀ ≤ X' := fun x hx => ⟨⟨x, hX₀W hx⟩, hS hx, rfl⟩
  have hX'3 : IsPGroup 3 X' := S.isPGroup'.map _
  have hX'syl : IsSylowOf W 3 X' := ⟨S, rfl⟩
  have hQX' : Q ≤ X' := le_isSylowOf_of_le_normalizer hX'syl hQ3' hQW hWQ
  have hX'C : X' ≤ centralizer (Q : Set G) := (map_subtype_le _).trans hWC
  have hX'eq : X' = X₀ := by
    by_contra hne
    have hlt : Nat.card X₀ < Nat.card X' :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hX₀X' (Ne.symm hne))
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hX'3
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hX₀
    have hge : Nat.card N₀ ≤ Nat.card X' := by
      rw [← hcard, hb, ha]
      rw [hb, ha] at hlt
      have hba : b < a := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
      calc 3 ^ b * 3 = 3 ^ (b + 1) := (pow_succ 3 b).symm
        _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) hba
    have hle : Nat.card X' ≤ Nat.card N₀ := by
      obtain ⟨N', hN'⟩ := hX'3.exists_le_sylow
      calc Nat.card X' ≤ Nat.card N' := Subgroup.card_le_of_le hN'
        _ = Nat.card N₀ := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    have hX'card : Nat.card X' = 3 ^ (Nat.card G).factorization 3 := by
      rw [← Sylow.card_eq_multiplicity N₀]; omega
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G N₀ (Sylow.ofCard X' hX'card)
    have hgN : (N₀ : Subgroup G).map (MulAut.conj g).toMonoidHom = X' := by
      have := congrArg (fun P : Sylow 3 G => (P : Subgroup G)) hg
      simp only [Sylow.coe_ofCard] at this
      rw [← this, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    have hqZ : g⁻¹ * q * g ∈ (N₀ : Subgroup G) ⊓ centralizer ((N₀ : Subgroup G) : Set G) := by
      refine ⟨mem_map_conj_iff.mp (by rw [hgN]; exact hQX' hqQ), mem_centralizer_iff.mpr ?_⟩
      intro n hn
      have hgn : g * n * g⁻¹ ∈ X' := by rw [← hgN]; exact ⟨n, hn, rfl⟩
      have hc := mem_centralizer_iff.mp (hX'C hgn) q hqQ
      calc n * (g⁻¹ * q * g) = g⁻¹ * ((g * n * g⁻¹) * q) * g := by group
        _ = g⁻¹ * (q * (g * n * g⁻¹)) * g := by rw [← hc]
        _ = g⁻¹ * q * g * n := by group
    rw [hZ] at hqZ
    have hy3 : orderOf y = 3 := (orderOf_eq_of_isConj hy).trans fr.orderOf_s₁
    have hne1 : g⁻¹ * q * g ≠ 1 := fun h1 => hq1 (by
      have := congrArg (fun x => g * x * g⁻¹) h1
      simpa [mul_assoc] using this)
    have hqg : IsConj q (g⁻¹ * q * g) := isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩
    have hs₁ : IsConj fr.s₁⁻¹ fr.s₁ := isConj_iff.mpr ⟨fr.t, by
      rw [show fr.t * fr.s₁⁻¹ * fr.t⁻¹ = (fr.t * fr.s₁ * fr.t⁻¹)⁻¹ by group, fr.t_mul_s₁,
        inv_inv]⟩
    have hqs₁ : IsConj q fr.s₁ := by
      rcases mem_zpowers_three hy3 hqZ with h1 | h1 | h1
      · exact absurd h1 hne1
      · exact hqg.trans (h1 ▸ hy)
      · obtain ⟨c, hc⟩ := isConj_iff.mp hy
        have hyinv : IsConj y⁻¹ fr.s₁⁻¹ := isConj_iff.mpr ⟨c, by rw [← hc]; group⟩
        exact hqg.trans (h1 ▸ hyinv.trans hs₁)
    exact h.p7.not_isConj_s₁_s₃ (hqs₁.symm.trans hqs₃)
  have hX₀syl : IsSylowOf W 3 X₀ := hX'eq ▸ hX'syl
  have htQ : fr.t ∈ centralizer (Q : Set G) := mem_centralizer_iff.mpr fun a ha =>
    mem_centralizer_singleton_iff.mp (At_le_t fr (hQA ha))
  have htW : fr.t ∈ normalizer (W : Set G) := hCW htQ
  have h162 : Nat.card (centralizer ({q} : Set G) ⊓ centralizer ({fr.t} : Set G) :
      Subgroup G) = 162 :=
    (h.p7.isConj_s₃_iff fr.t fr.orderOf_t q (At_le_t fr hqA) (pow_three_of_mem_At h hqA)).mp
      hqs₃
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := (centralizer ({q} : Set G) ⊓ centralizer ({fr.t} : Set G) : Subgroup G)) 3 (n := 4)
    (by rw [h162]; norm_num)
  set Z₀ := K.map (centralizer ({q} : Set G) ⊓ centralizer ({fr.t} : Set G)).subtype
  have hZ₀card : Nat.card Z₀ = 81 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]; norm_num
  have hZ₀3 : IsPGroup 3 Z₀ := IsPGroup.of_card (n := 4) (by rw [hZ₀card]; norm_num)
  have hZ₀CQ : Z₀ ≤ centralizer (Q : Set G) := (map_subtype_le _).trans
    (inf_le_left.trans (by rw [hQq]; exact centralizer_singleton_le q))
  have hZ₀W : Z₀ ≤ W := hW Z₀ hZ₀CQ (by rw [hZ₀card]; decide)
  have hZ₀t : Z₀ ≤ centralizer ({fr.t} : Set G) := (map_subtype_le _).trans inf_le_right
  have h81 := card_le_of_coprime (t_mul_t fr) hWodd htW hX₀syl htX₀ hZ₀3 hZ₀W hZ₀t
  rw [hZ₀card] at h81
  have h27 := card_le_of_le_C₁_t h hX₀.to_inf_left (inf_le_left.trans hX₀C₁) inf_le_right
  omega

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen
