module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma

open CFSG.Open Subgroup

private def PairFacts {K : Type} [Group K] (S A : Subgroup K) : Prop :=
  A ≤ S ∧ IsElemAbelian 3 A ∧ Nat.card A = 27 ∧
    (∀ r ∈ S, r ∉ A → ∃ g ∈ normalizer (A : Set K), g * r * g⁻¹ ∉ S) ∧
    (∀ a ∈ A, a ≠ 1 → ∃ g₁ ∈ normalizer (A : Set K), ∃ g₂ ∈ normalizer (A : Set K),
      g₁ * a * g₁⁻¹ ∉ zpowers a ∧ g₂ * a * g₂⁻¹ ∉ zpowers a ∧
        g₂ * a * g₂⁻¹ ∉ zpowers (g₁ * a * g₁⁻¹))

private theorem PairFacts.map {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {S A : Subgroup K} (h : PairFacts S A) :
    PairFacts (S.map e.toMonoidHom) (A.map e.toMonoidHom) := by
  obtain ⟨hAS, hA, hAc, h1, h2⟩ := h
  have hN : ∀ g ∈ normalizer (A : Set K),
      e g ∈ normalizer ((A.map e.toMonoidHom : Subgroup K') : Set K') := by
    intro g hg
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hg
  have hmem : ∀ (H : Subgroup K) (x : K), e x ∈ H.map e.toMonoidHom ↔ x ∈ H := by
    intro H x
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hz : ∀ x : K, zpowers (e x) = (zpowers x).map e.toMonoidHom := fun x =>
    (MonoidHom.map_zpowers e.toMonoidHom x).symm
  have hc : ∀ g x : K, e g * e x * (e g)⁻¹ = e (g * x * g⁻¹) := by
    intro g x
    simp only [map_mul, map_inv]
  refine ⟨Subgroup.map_mono hAS, hA.map _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hAc]
  · intro r' hr' hr'A
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hr'
    have hrA : r ∉ A := fun h => hr'A (Subgroup.mem_map_of_mem _ h)
    obtain ⟨g, hg, hgr⟩ := h1 r hr hrA
    refine ⟨e g, hN g hg, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, hc, hmem]
    exact hgr
  · intro a' ha' ha'1
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    rw [MulEquiv.coe_toMonoidHom] at ha'1 ⊢
    have ha1 : a ≠ 1 := fun h => ha'1 (by rw [h, map_one])
    obtain ⟨g₁, hg₁, g₂, hg₂, k₁, k₂, k₃⟩ := h2 a ha ha1
    refine ⟨e g₁, hN g₁ hg₁, e g₂, hN g₂ hg₂, ?_, ?_, ?_⟩
    · rw [hc, hz, hmem]
      exact k₁
    · rw [hc, hz, hmem]
      exact k₂
    · rw [hc, hc, hz, hmem]
      exact k₃

private theorem map_symm_map {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (H : Subgroup K) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_map_equiv,
    MulEquiv.symm_apply_apply]

theorem SolvSigmaSylowFacts.of_mulEquiv {K K' : Type} [Group K] [Group K'] [Finite K]
    (e : K ≃* K') (h : SolvSigmaSylowFacts K') : SolvSigmaSylowFacts K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro S
  obtain ⟨A', hA'⟩ := h (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  refine ⟨A'.map e.symm.toMonoidHom, ?_⟩
  have h' := PairFacts.map e.symm (S := (S : Subgroup K).map e.toMonoidHom) (A := A') hA'
  rwa [map_symm_map] at h'

private theorem mem_zpowers_cases {K : Type} [Group K] {u x : K} (hu : u ^ 3 = 1)
    (hx : x ∈ zpowers u) : x = 1 ∨ x = u ∨ x = u * u := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have h3 : u ^ (3 : ℤ) = 1 := by rw [zpow_ofNat, hu]
  have hk : u ^ k = u ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [hk]
  rcases hr with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right; rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]

private theorem zpowers_eq_of_mem {K : Type} [Group K] [Finite K] {x y : K} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) (h : x ∈ zpowers y) : zpowers x = zpowers y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr h) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hy3)

private theorem conj_not_mem_zpowers {K : Type} [Group K] {S₀ : Subgroup K}
    (hS₀c : Nat.card S₀ = 81) {τ b : K} (hτ : τ ∈ S₀) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hτb : τ * b ≠ b * τ) : τ * b * τ⁻¹ ∉ zpowers b := by
  intro hm
  have hτ81 : τ ^ 81 = 1 := by
    have h := pow_card_eq_one' (G := S₀) (x := ⟨τ, hτ⟩)
    rw [hS₀c] at h
    simpa using congrArg Subtype.val h
  rcases mem_zpowers_cases hb3 hm with h | h | h
  · apply hb1
    have h' : τ * b = τ * 1 := by rw [mul_one]; exact mul_inv_eq_one.mp h
    exact mul_left_cancel h'
  · exact hτb (mul_inv_eq_iff_eq_mul.mp h)
  ·
    have hb4 : b * b * (b * b) = b := by
      calc b * b * (b * b) = b ^ 3 * b := by rw [pow_three]; simp only [mul_assoc]
        _ = b := by rw [hb3, one_mul]
    have h2 : τ ^ 2 * b * (τ ^ 2)⁻¹ = b := by
      calc τ ^ 2 * b * (τ ^ 2)⁻¹ = τ * (τ * b * τ⁻¹) * τ⁻¹ := by
            rw [pow_two, mul_inv_rev]; simp only [mul_assoc]
        _ = τ * (b * b) * τ⁻¹ := by rw [h]
        _ = (τ * b * τ⁻¹) * (τ * b * τ⁻¹) := by group
        _ = b * b * (b * b) := by rw [h]
        _ = b := hb4
    have hc : Commute (τ ^ 2) b := mul_inv_eq_iff_eq_mul.mp h2
    have hτe : τ = (τ ^ 2) ^ 41 := by
      rw [← pow_mul, show 2 * 41 = 81 + 1 by norm_num, pow_add, hτ81, one_mul, pow_one]
    apply hτb
    rw [hτe]
    exact (hc.pow_left 41).eq

private theorem pairFacts_of_data {K : Type} [Group K] [Finite K] {S₀ A₀ : Subgroup K}
    (hS₀c : Nat.card S₀ = 81) (hA₀S₀ : A₀ ≤ S₀) (hA₀ : IsElemAbelian 3 A₀)
    (hA₀c : Nat.card A₀ = 27) {σ z f : K} (hσ : σ ∈ S₀) (hσA : σ ∉ A₀) (hz : z ∈ A₀)
    (hz1 : z ≠ 1) (hzσ : σ * z = z * σ) (hCσ : ∀ b ∈ A₀, σ * b = b * σ → b ∈ zpowers z)
    (hf : f ∈ normalizer (A₀ : Set K)) (hfz : f * z * f⁻¹ ∉ zpowers z) :
    PairFacts S₀ A₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnormal : (A₀.subgroupOf S₀).Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    have h := (A₀.subgroupOf S₀).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hA₀S₀).toEquiv, hA₀c, hS₀c] at h
    rw [hS₀c, show (81 : ℕ).minFac = 3 by norm_num]
    omega
  have hnorm : ∀ s ∈ S₀, ∀ a ∈ A₀, s * a * s⁻¹ ∈ A₀ := by
    intro s hs a ha
    have := hnormal.conj_mem ⟨a, hA₀S₀ ha⟩ (mem_subgroupOf.mpr ha) ⟨s, hs⟩
    rw [mem_subgroupOf] at this
    simpa using this
  have hSN : ∀ s ∈ S₀, s ∈ normalizer (A₀ : Set K) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hnorm s hs x hx, fun hx => ?_⟩
    have h := hnorm s⁻¹ (S₀.inv_mem hs) _ hx
    have he : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
    rw [he] at h
    exact h
  have hfA : ∀ a ∈ A₀, f * a * f⁻¹ ∈ A₀ := fun a ha => (mem_normalizer_iff.mp hf a).mp ha
  have hcomm : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA₀.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h3 : ∀ a ∈ A₀, a ^ 3 = 1 := hA₀.2
  have hgen : ∀ r ∈ S₀, r ∉ A₀ → A₀ ⊔ zpowers r = S₀ := by
    intro r hr hrA
    have hle : A₀ ⊔ zpowers r ≤ S₀ := sup_le hA₀S₀ (zpowers_le.mpr hr)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hS₀c]
    have hd : Nat.card ↥(A₀ ⊔ zpowers r) ∣ 81 := hS₀c ▸ Subgroup.card_dvd_of_le hle
    have hd27 : 27 ∣ Nat.card ↥(A₀ ⊔ zpowers r) := hA₀c ▸ Subgroup.card_dvd_of_le le_sup_left
    have hne : Nat.card ↥(A₀ ⊔ zpowers r) ≠ 27 := by
      intro h27
      apply hrA
      have hAe : A₀ = A₀ ⊔ zpowers r :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h27, hA₀c])
      rw [hAe]
      exact (le_sup_right : zpowers r ≤ A₀ ⊔ zpowers r) (mem_zpowers r)
    obtain ⟨k, hk⟩ := hd27
    have hk3 : k ∣ 3 := by
      have h' : 27 * k ∣ 27 * 3 := by rw [← hk]; exact hd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp h'
    have hk13 : k = 1 ∨ k = 3 := (Nat.dvd_prime Nat.prime_three).mp hk3
    omega
  have hzS : ∀ s ∈ S₀, s * z = z * s := by
    have hle : S₀ ≤ centralizer {z} := by
      rw [← hgen σ hσ hσA]
      refine sup_le (fun a ha => ?_) (zpowers_le.mpr ?_)
      · rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact hcomm z hz a ha
      · rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact hzσ.symm
    intro s hs
    exact ((mem_centralizer_iff.mp (hle hs)) z rfl).symm
  have hzpσ : ∀ w ∈ zpowers z, σ * w = w * σ := by
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact (Commute.zpow_right hzσ k).eq
  have hσz : ∀ b : K, σ * b * σ⁻¹ ∈ zpowers z → b ∈ zpowers z := by
    intro b hb
    have h := hzpσ _ hb
    have he : b = σ * b * σ⁻¹ := by
      calc b = σ⁻¹ * ((σ * b * σ⁻¹) * σ) := by group
        _ = σ⁻¹ * (σ * (σ * b * σ⁻¹)) := by rw [← h]
        _ = σ * b * σ⁻¹ := by group
    rw [he]
    exact hb
  have hσb : ∀ b ∈ A₀, b ∉ zpowers z → σ * b ≠ b * σ := fun b hb hbz h => hbz (hCσ b hb h)
  have hne1 : ∀ b : K, b ∉ zpowers z → b ≠ 1 := fun b hbz h => hbz (h ▸ one_mem _)
  refine ⟨hA₀S₀, hA₀, hA₀c, ?_, ?_⟩
  ·
    intro r hr hrA
    refine ⟨f, hf, fun hfr => hfz ?_⟩
    set φ : K →* K := (MulAut.conj f).toMonoidHom with hφ
    have hφx : ∀ x : K, φ x = f * x * f⁻¹ := fun x => rfl
    have hle : S₀.map φ ≤ S₀ := by
      conv_lhs => rw [← hgen r hr hrA, Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le ?_ (zpowers_le.mpr ?_)
      · rintro _ ⟨a, ha, rfl⟩
        rw [hφx]
        exact hA₀S₀ (hfA a ha)
      · rw [hφx]
        exact hfr
    have heq : S₀.map φ = S₀ := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj f).injective]
    have hσ' : σ ∈ S₀.map φ := by rw [heq]; exact hσ
    obtain ⟨s, hs, hsσ⟩ := Subgroup.mem_map.mp hσ'
    rw [hφx] at hsσ
    refine hCσ _ (hfA z hz) ?_
    rw [← hsσ]
    calc f * s * f⁻¹ * (f * z * f⁻¹) = f * (s * z) * f⁻¹ := by group
      _ = f * (z * s) * f⁻¹ := by rw [hzS s hs]
      _ = f * z * f⁻¹ * (f * s * f⁻¹) := by group
  ·
    intro a ha ha1
    by_cases haz : a ∈ zpowers z
    ·
      have hza : zpowers a = zpowers z := zpowers_eq_of_mem (h3 a ha) ha1 (h3 z hz) haz
      set b := f * a * f⁻¹ with hb
      have hbA : b ∈ A₀ := hfA a ha
      have hbz : b ∉ zpowers z := by
        intro hbz
        apply hfz
        have hb1 : b ≠ 1 := by
          intro h1
          apply ha1
          have h' : f * a = f * 1 := by rw [mul_one]; exact mul_inv_eq_one.mp h1
          exact mul_left_cancel h'
        have hbf : b ∈ zpowers (f * z * f⁻¹) := by
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp haz
          refine mem_zpowers_iff.mpr ⟨k, ?_⟩
          rw [hb, conj_zpow]
        have hfz3 : (f * z * f⁻¹) ^ 3 = 1 := h3 _ (hfA z hz)
        have hbe : zpowers b = zpowers (f * z * f⁻¹) :=
          zpowers_eq_of_mem (h3 b hbA) hb1 hfz3 hbf
        have : zpowers (f * z * f⁻¹) ≤ zpowers z := hbe ▸ zpowers_le.mpr hbz
        exact this (mem_zpowers _)
      refine ⟨f, hf, σ * f, mul_mem (hSN σ hσ) hf, ?_, ?_, ?_⟩
      · rw [hza]
        exact hbz
      · have he : σ * f * a * (σ * f)⁻¹ = σ * b * σ⁻¹ := by rw [hb]; group
        rw [he, hza]
        exact fun h => hbz (hσz b h)
      · have he : σ * f * a * (σ * f)⁻¹ = σ * b * σ⁻¹ := by rw [hb]; group
        rw [he]
        exact conj_not_mem_zpowers hS₀c hσ (h3 b hbA) (hne1 b hbz) (hσb b hbA hbz)
    ·
      have hσ2 : σ * σ ∈ S₀ := mul_mem hσ hσ
      have hσ2a : σ * σ * a ≠ a * (σ * σ) := by
        intro h
        have hτ81 : σ ^ 81 = 1 := by
          have h' := pow_card_eq_one' (G := S₀) (x := ⟨σ, hσ⟩)
          rw [hS₀c] at h'
          simpa using congrArg Subtype.val h'
        have hc : Commute (σ * σ) a := h
        have hσe : σ = (σ * σ) ^ 41 := by
          rw [← pow_two, ← pow_mul, show 2 * 41 = 81 + 1 by norm_num, pow_add, hτ81, one_mul,
            pow_one]
        apply hσb a ha haz
        rw [hσe]
        exact (hc.pow_left 41).eq
      refine ⟨σ, hSN σ hσ, σ * σ, mul_mem (hSN σ hσ) (hSN σ hσ), ?_, ?_, ?_⟩
      · exact conj_not_mem_zpowers hS₀c hσ (h3 a ha) ha1 (hσb a ha haz)
      · exact conj_not_mem_zpowers hS₀c hσ2 (h3 a ha) ha1 hσ2a
      · intro hm
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hm
        apply conj_not_mem_zpowers hS₀c hσ (h3 a ha) ha1 (hσb a ha haz)
        refine mem_zpowers_iff.mpr ⟨k, ?_⟩
        have h1 : (σ * a * σ⁻¹) ^ k = σ * a ^ k * σ⁻¹ := conj_zpow
        rw [h1] at hk
        have h2 : σ * a ^ k * σ⁻¹ = σ * (σ * a * σ⁻¹) * σ⁻¹ := by rw [hk]; group
        have h3' := mul_left_cancel (mul_right_cancel h2)
        exact h3'

theorem solvSigmaSylowFacts_of_data {K : Type} [Group K] [Finite K] {S₀ A₀ : Subgroup K}
    (hS₀ : IsPGroup 3 S₀) (hS₀i : ¬ 3 ∣ S₀.index) (hS₀c : Nat.card S₀ = 81)
    (hA₀S₀ : A₀ ≤ S₀) (hA₀ : IsElemAbelian 3 A₀) (hA₀c : Nat.card A₀ = 27)
    {σ z f : K} (hσ : σ ∈ S₀) (hσA : σ ∉ A₀) (hz : z ∈ A₀) (hz1 : z ≠ 1)
    (hzσ : σ * z = z * σ) (hCσ : ∀ b ∈ A₀, σ * b = b * σ → b ∈ zpowers z)
    (hf : f ∈ normalizer (A₀ : Set K)) (hfz : f * z * f⁻¹ ∉ zpowers z) :
    SolvSigmaSylowFacts K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h0 := pairFacts_of_data hS₀c hA₀S₀ hA₀ hA₀c hσ hσA hz hz1 hzσ hCσ hf hfz
  intro S
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow (MulEquiv.refl K) hS₀ hS₀i S
  refine ⟨A₀.map Φ.toMonoidHom, ?_⟩
  rw [hΦ]
  exact h0.map Φ

theorem solvSigmaSylowFacts_of_data_of_le {G : Type} [Group G] [Finite G] {H S₀ A₀ : Subgroup G}
    (hS₀H : S₀ ≤ H) (hS₀c : Nat.card S₀ = 81) (hS₀i : ¬ 3 ∣ (S₀.subgroupOf H).index)
    (hA₀S₀ : A₀ ≤ S₀) (hA₀ : IsElemAbelian 3 A₀) (hA₀c : Nat.card A₀ = 27)
    {σ z f : G} (hσ : σ ∈ S₀) (hσA : σ ∉ A₀) (hz : z ∈ A₀) (hz1 : z ≠ 1)
    (hzσ : σ * z = z * σ) (hCσ : ∀ b ∈ A₀, σ * b = b * σ → b ∈ zpowers z)
    (hfH : f ∈ H) (hf : f ∈ normalizer (A₀ : Set G)) (hfz : f * z * f⁻¹ ∉ zpowers z) :
    SolvSigmaSylowFacts H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA₀H : A₀ ≤ H := hA₀S₀.trans hS₀H
  have hc81 : Nat.card (S₀.subgroupOf H) = 81 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hS₀H).toEquiv, hS₀c]
  have hval : ∀ (x : H) (k : ℤ), ((x ^ k : H) : G) = (x : G) ^ k := fun x k => by
    simp only [SubgroupClass.coe_zpow]
  refine solvSigmaSylowFacts_of_data (S₀ := S₀.subgroupOf H) (A₀ := A₀.subgroupOf H)
    (σ := ⟨σ, hS₀H hσ⟩) (z := ⟨z, hA₀H hz⟩) (f := ⟨f, hfH⟩)
    (IsPGroup.of_card (n := 4) (by rw [hc81]; norm_num)) hS₀i hc81
    (fun x hx => mem_subgroupOf.mpr (hA₀S₀ (mem_subgroupOf.mp hx))) (hA₀.subgroupOf H)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hA₀H).toEquiv, hA₀c])
    (mem_subgroupOf.mpr hσ) (fun h => hσA (mem_subgroupOf.mp h)) (mem_subgroupOf.mpr hz)
    (fun h => hz1 (congrArg Subtype.val h)) (Subtype.ext hzσ) ?_ ?_ ?_
  · intro b hb hc
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hCσ b (mem_subgroupOf.mp hb) (congrArg Subtype.val hc))
    refine mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [hval]
    exact hk
  · rw [mem_normalizer_iff]
    intro x
    rw [mem_subgroupOf, mem_subgroupOf]
    exact (mem_normalizer_iff.mp hf x).trans (by simp)
  · intro hm
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hm
    apply hfz
    refine mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    rw [hval] at this
    simpa using this

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma
