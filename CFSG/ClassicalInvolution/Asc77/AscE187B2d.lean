module

public import CFSG.ClassicalInvolution.Asc77.AscE187B2c
public import CFSG.ClassicalInvolution.Asc77.AscE187B2a
public import CFSG.ClassicalInvolution.Asc77.AscE187B2b
public import CFSG.ClassicalInvolution.Asc77.AscE187Delta

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem E187C.exists_two_twins_of {z : G} (hc : ConjInvariant Ω)
    (h8R : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → 8 ≤ Nat.card Q)
    (hbadc : ∀ {g' : G}, g' ∉ H → ∀ M ∈ Ω, IsUniqueInvolution M (g' * z * g'⁻¹) →
      ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    (hK : K ∈ Ω) {g t : G} (hz : IsUniqueInvolution K z)
    (hzH : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hSylz : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (hg : g ∉ H) (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t)
    (hdel : t * t = 1 → ¬ t * z = z * t →
      ∃ B : Subgroup G, ∃ b : G, B ≤ (S : Subgroup G) ∧ B ≤ Subgroup.centralizer ({t} : Set G) ∧
        IsUniqueInvolution B b ∧ 8 ≤ Nat.card B ∧ b = z * (t * z * t⁻¹) ∧ b ∈ W ∧
        Subgroup.centralizer ({b} : Set G) ≤ H)
    {K' : Subgroup G} :
    ∃ (B : Subgroup G) (b : G) (g' : G), B ≤ (S : Subgroup G) ∧
      B ≤ Subgroup.centralizer ({t} : Set G) ∧ IsUniqueInvolution B b ∧ 8 ≤ Nat.card B ∧
      b = z * (t * z * t⁻¹) ∧ b ∈ W ∧ Subgroup.centralizer ({b} : Set G) ≤ H ∧
      t = g' * z * g'⁻¹ ∧ g' ∉ H ∧ (∀ β ∈ B, g'⁻¹ * β * g' ∈ (S : Subgroup G)) ∧
      ∃ β₃ ∈ B, ∃ β₄ ∈ B, conjSub (g'⁻¹ * β₃ * g') K ≠ conjSub (g'⁻¹ * β₄ * g') K ∧
        conjSub (g'⁻¹ * β₃ * g') K ≠ K ∧ conjSub (g'⁻¹ * β₃ * g') K ≠ K' ∧
        conjSub (g'⁻¹ * β₄ * g') K ≠ K ∧ conjSub (g'⁻¹ * β₄ * g') K ≠ K' := by
  classical
  classical
  have ht2 : t * t = 1 := by
    rw [ht]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  obtain ⟨B, b, hBS, hBt, hBb, hB8, hbdef, hbW, hbH⟩ := hdel ht2 hnc
  have hBp : IsPGroup 2 B := S.isPGroup'.to_le hBS
  have hB'z : conjSub g⁻¹ B ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hβt := Subgroup.mem_centralizer_singleton_iff.mp (hBt hx)
    have e1 : g⁻¹ * (t * (g * x * g⁻¹)) * g = z * x := by rw [ht]; group
    have e2 : g⁻¹ * ((g * x * g⁻¹) * t) * g = x * z := by rw [ht]; group
    rw [← e1, ← e2, hβt]
  obtain ⟨c₀, hc₀, hBc₀⟩ := exists_conj_of_isSylow2In hSylz (isPGroup_conjSub g⁻¹ hBp) hB'z
  have hc₀cent := Subgroup.mem_centralizer_singleton_iff.mp hc₀
  have hc₀H : c₀ ∈ H := hzH hc₀
  have hg'H : g * c₀ ∉ H := by
    intro hh
    apply hg
    have : g = (g * c₀) * c₀⁻¹ := by group
    rw [this]
    exact H.mul_mem hh (H.inv_mem hc₀H)
  have ht' : t = (g * c₀) * z * (g * c₀)⁻¹ := by
    rw [ht]
    have : c₀ * z * c₀⁻¹ = z := by rw [hc₀cent]; group
    calc g * z * g⁻¹ = g * (c₀ * z * c₀⁻¹) * g⁻¹ := by rw [this]
      _ = (g * c₀) * z * (g * c₀)⁻¹ := by group
  have hBg' : ∀ β ∈ B, (g * c₀)⁻¹ * β * (g * c₀) ∈ (S : Subgroup G) := by
    intro β hβ
    have hx : g⁻¹ * β * g ∈ conjSub g⁻¹ B := by
      rw [mem_conjSub_iff, inv_inv]
      have : g * (g⁻¹ * β * g) * g⁻¹ = β := by group
      rw [this]
      exact hβ
    have := hBc₀ hx
    rw [mem_conjSub_iff] at this
    have e : c₀⁻¹ * (g⁻¹ * β * g) * c₀ = (g * c₀)⁻¹ * β * (g * c₀) := by group
    rw [e] at this
    exact this.1
  obtain ⟨g', ht', hg'H, hBg'⟩ : ∃ g' : G, t = g' * z * g'⁻¹ ∧ g' ∉ H ∧
      ∀ β ∈ B, g'⁻¹ * β * g' ∈ (S : Subgroup G) := ⟨g * c₀, ht', hg'H, hBg'⟩
  have hK₁ : conjSub g' K ∈ Ω := hc g' K hK
  have hK₁t : IsUniqueInvolution (conjSub g' K) t := by
    rw [ht']
    exact hz.conj g'
  have hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H := by
    have := hbadc hg'H
    rwa [← ht'] at this
  have hN : ∀ β ∈ B, conjSub β (conjSub g' K) = conjSub g' K → β = 1 ∨ β = b := by
    intro β hβB hβK
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy, hy4⟩ := exists_orderOf_four_in_zpowers hBp hBb hβB hcon.1 hcon.2
    have hyB : y ∈ B := (Subgroup.zpowers_le.mpr hβB) hy
    have hyK : conjSub y (conjSub g' K) = conjSub g' K := by
      have hle : Subgroup.zpowers β ≤
          Subgroup.normalizer ((conjSub g' K : Subgroup G) : Set G) := by
        rw [Subgroup.zpowers_le]
        exact mem_normalizer_iff_conjSub_eq.mpr hβK
      exact mem_normalizer_iff_conjSub_eq.mp (hle hy)
    have hy2 : IsPGroup 2 (Subgroup.zpowers y) := isPGroup_zpowers_of_orderOf_four hy4
    obtain ⟨v, hvK, hv4, hvc⟩ := E187C.exists_v_sq_centralizes_of h8R hK₁ hK₁t hy2 hyK
    have hyyb : y * y = b := by
      have h4 : y ^ 4 = 1 := by rw [← hy4]; exact pow_orderOf_eq_one y
      have hsq : (y * y) * (y * y) = 1 := by
        calc (y * y) * (y * y) = y ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = 1 := h4
      rcases hBb.unique (y * y) (B.mul_mem hyB hyB) hsq with h' | h'
      · exfalso
        have : y ^ 2 = 1 := by rw [pow_two]; exact h'
        have := orderOf_dvd_of_pow_eq_one this
        rw [hy4] at this
        omega
      · exact h'
    rw [hyyb] at hvc
    exact hbad _ hK₁ hK₁t v hvK hv4 (hbH (Subgroup.mem_centralizer_singleton_iff.mpr hvc.symm))
  have : Fintype ↥B := Fintype.ofFinite _
  let m' : ↥B → Subgroup G := fun β => conjSub (g'⁻¹ * (β : G) * g') K
  have hm' : ∀ β : ↥B, m' β = conjSub g'⁻¹ (conjSub (β : G) (conjSub g' K)) := fun β => by
    simp only [m']
    rw [conjSub_mul, conjSub_mul]
  have hfib : ∀ y ∈ (Finset.univ : Finset ↥B).image m',
      ((Finset.univ : Finset ↥B).filter (fun β => m' β = y)).card ≤ 2 := by
    intro y hy
    obtain ⟨β₀, -, rfl⟩ := Finset.mem_image.mp hy
    have hsub : (Finset.univ : Finset ↥B).filter (fun β => m' β = m' β₀) ⊆
        {β₀, β₀ * ⟨b, hBb.mem⟩} := by
      intro β hβ
      rw [Finset.mem_filter] at hβ
      have h1 : conjSub (β : G) (conjSub g' K) = conjSub (β₀ : G) (conjSub g' K) := by
        have := hβ.2
        rw [hm', hm'] at this
        exact conjSub_injective g'⁻¹ this
      have h2 : conjSub ((β₀ : G)⁻¹ * β) (conjSub g' K) = conjSub g' K := by
        rw [conjSub_mul, h1, conjSub_inv_conjSub]
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases hN _ (B.mul_mem (B.inv_mem β₀.2) β.2) h2 with h3 | h3
      · left
        apply Subtype.ext
        calc (β : G) = (β₀ : G) * ((β₀ : G)⁻¹ * β) := by group
          _ = β₀ := by rw [h3, mul_one]
      · right
        apply Subtype.ext
        show (β : G) = (β₀ : G) * b
        calc (β : G) = (β₀ : G) * ((β₀ : G)⁻¹ * β) := by group
          _ = (β₀ : G) * b := by rw [h3]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hcard := Finset.card_le_mul_card_image (Finset.univ : Finset ↥B) 2 hfib
  have hBcard : 8 ≤ (Finset.univ : Finset ↥B).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hB8
  set T := (Finset.univ : Finset ↥B).image m' with hT
  have hT4 : 4 ≤ T.card := by omega
  have hT2 : 1 < ((T.erase K).erase K').card := by
    have h1 := Finset.pred_card_le_card_erase (s := T) (a := K)
    have h2 := Finset.pred_card_le_card_erase (s := T.erase K) (a := K')
    omega
  obtain ⟨K₃, hK₃, K₄, hK₄, hne34⟩ := Finset.one_lt_card.mp hT2
  rw [Finset.mem_erase, Finset.mem_erase] at hK₃ hK₄
  obtain ⟨hK₃K', hK₃K, hK₃T⟩ := hK₃
  obtain ⟨hK₄K', hK₄K, hK₄T⟩ := hK₄
  obtain ⟨β₃, -, rfl⟩ := Finset.mem_image.mp hK₃T
  obtain ⟨β₄, -, rfl⟩ := Finset.mem_image.mp hK₄T
  exact ⟨B, b, g', hBS, hBt, hBb, hB8, hbdef, hbW, hbH, ht', hg'H, hBg', β₃, β₃.2, β₄, β₄.2,
    hne34, hK₃K, hK₃K', hK₄K, hK₄K'⟩


theorem MinCex.exists_two_twins (h : E187Hyps p f) (c : MinCex p f Ω K S R W H) {z g t : G}
    (hz : IsUniqueInvolution K z) (hzW : z ∈ W) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hSylz : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (hg : g ∉ H) (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t)
    {K' : Subgroup G} :
    ∃ (B : Subgroup G) (b : G) (g' : G), B ≤ (S : Subgroup G) ∧
      B ≤ Subgroup.centralizer ({t} : Set G) ∧ IsUniqueInvolution B b ∧ 8 ≤ Nat.card B ∧
      b = z * (t * z * t⁻¹) ∧ b ∈ W ∧ Subgroup.centralizer ({b} : Set G) ≤ H ∧
      t = g' * z * g'⁻¹ ∧ g' ∉ H ∧ (∀ β ∈ B, g'⁻¹ * β * g' ∈ (S : Subgroup G)) ∧
      ∃ β₃ ∈ B, ∃ β₄ ∈ B, conjSub (g'⁻¹ * β₃ * g') K ≠ conjSub (g'⁻¹ * β₄ * g') K ∧
        conjSub (g'⁻¹ * β₃ * g') K ≠ K ∧ conjSub (g'⁻¹ * β₃ * g') K ≠ K' ∧
        conjSub (g'⁻¹ * β₄ * g') K ≠ K ∧ conjSub (g'⁻¹ * β₄ * g') K ≠ K' := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hA : EtaAbelian Ω := h.etaAbelian hp hq hΩ
  have hM : EtaMeet Ω := h.etaMeet hp hq hΩ
  exact E187C.exists_two_twins_of hΩ.conjInvariant (fun hQ => hΩ.eight_le_of_mem_RSet hp hQ)
    (fun hg' => c.hbad_of_conj hA hM hz hg') c.stand.mem hz hzH hSylz hg ht htS hnc
    (fun ht2 hnc => c.exists_delta h hz hzW ht2 htS hnc)

end CFSG.ClassicalInvolution.Asc77
