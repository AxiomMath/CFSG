module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenHypAux
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenCop
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open

private theorem le_normalizer_centralizer {G : Type*} [Group G] {A T : Subgroup G}
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    A ≤ Subgroup.normalizer (Subgroup.centralizer (T : Set G) : Set G) := by
  intro a ha
  have hT := Subgroup.mem_normalizer_iff.1 (hAT ha)
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx t ht
    have h1 := hx _ ((hT _).2 (by rwa [show a * (a⁻¹ * t * a) * a⁻¹ = t by group]))
    calc t * (a * x * a⁻¹) = a * (a⁻¹ * t * a * x) * a⁻¹ := by group
      _ = a * (x * (a⁻¹ * t * a)) * a⁻¹ := by rw [h1]
      _ = a * x * a⁻¹ * t := by group
  · intro hx t ht
    have h1 := hx _ ((hT t).1 ht)
    have h2 : a * (t * x) * a⁻¹ = a * (x * t) * a⁻¹ := by
      calc a * (t * x) * a⁻¹ = a * t * a⁻¹ * (a * x * a⁻¹) := by group
        _ = a * x * a⁻¹ * (a * t * a⁻¹) := h1
        _ = a * (x * t) * a⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem eq_or_eq_of_hyperplane {G : Type*} [Group G] [Finite G] {p k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : ∀ j, 0 < j → j < k → ¬ 2 ^ j ≡ 1 [MOD p])
    {R Z B H W : Subgroup G} (hR : timmesfeldIsExtraspecial ↥R)
    (hZ : Z = (Subgroup.center ↥R).map R.subtype) (hB : IsElemAbelian p B)
    (hBR : B ≤ Subgroup.normalizer (R : Set G))
    (hCB : R ⊓ Subgroup.centralizer (B : Set G) ≤ Z) (hHB : H ≤ B)
    (hHc : Nat.card H * p = Nat.card B)
    (hRH : Nat.card ↥(R ⊓ Subgroup.centralizer (H : Set G)) ≤ 2 ^ (k + 1))
    (hZW : Z ≤ W) (hWR : W ≤ R ⊓ Subgroup.centralizer (H : Set G))
    (hBW : B ≤ Subgroup.normalizer (W : Set G)) :
    W = Z ∨ W = R ⊓ Subgroup.centralizer (H : Set G) := by
  have hp : p.Prime := Fact.out
  obtain ⟨b, hbB, hbH⟩ : ∃ b ∈ B, b ∉ H := by
    by_contra! hc
    have h1 := Subgroup.card_le_of_le (fun x hx => hc x hx : B ≤ H)
    have h2 := Nat.card_pos (α := H)
    have h3 := hp.two_le
    nlinarith
  have hbZ : Subgroup.zpowers b ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.zpowers_le.2 (normalizer_le_centralizer_center hR hZ (hBR hbB))
  have hfix : W ⊓ Subgroup.centralizer (Subgroup.zpowers b : Set G) = Z := by
    refine le_antisymm (fun w hw => ?_) (le_inf hZW (Subgroup.le_centralizer_iff.1 hbZ))
    obtain ⟨hwW, hwb⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨hwR, hwH⟩ := Subgroup.mem_inf.1 (hWR hwW)
    exact hCB (Subgroup.mem_inf.2 ⟨hwR, mem_centralizer_of_hyperplane hp hHB hHc hbB hbH hwH
      (Subgroup.mem_centralizer_iff.1 hwb b (Subgroup.mem_zpowers b))⟩)
  have hbp : IsPGroup p (Subgroup.zpowers b) :=
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p B hB).to_le
      (Subgroup.zpowers_le.2 hbB)
  have hmod := CFSG.SignalizerFunctor.Helpers.centralizer_card_modEq p hp (Subgroup.zpowers b) W
    hbp (Subgroup.zpowers_le.2 (hBW hbB))
  have hZc := card_center_map_eq_two hR hZ
  rw [hfix, hZc] at hmod
  obtain ⟨n, hn⟩ := (hR.1.to_le (hWR.trans inf_le_left)).exists_card_eq
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := by
    refine ⟨n - 1, ?_⟩
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have := Subgroup.card_le_of_le hZW
      rw [hn, hZc, h0] at this
      norm_num at this
    · omega
  have hj : 2 ^ j ≡ 1 [MOD p] := by
    refine Nat.ModEq.cancel_left_of_coprime (c := 2)
      ((Nat.coprime_primes hp Nat.prime_two).2 hp2) ?_
    rw [mul_one, ← pow_succ', ← hn]
    exact hmod
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · left
    subst hj0
    exact (Subgroup.eq_of_le_of_card_ge hZW (by rw [hn, hZc]; norm_num)).symm
  · by_cases hjk : j < k
    · exact absurd hj (hk j hj0 hjk)
    · right
      refine Subgroup.eq_of_le_of_card_ge hWR ?_
      rw [hn]
      exact hRH.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

private theorem le_of_comm_hyperplane {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {R Z B H : Subgroup G}
    (hR : timmesfeldIsExtraspecial ↥R) (hZ : Z = (Subgroup.center ↥R).map R.subtype)
    (hB : IsElemAbelian p B) (hBR : B ≤ Subgroup.normalizer (R : Set G))
    (hCB : R ⊓ Subgroup.centralizer (B : Set G) ≤ Z) (hHB : H ≤ B)
    (hHc : Nat.card H * p = Nat.card B)
    (hab : ∀ x ∈ R ⊓ Subgroup.centralizer (H : Set G),
      ∀ y ∈ R ⊓ Subgroup.centralizer (H : Set G), x * y = y * x) :
    R ⊓ Subgroup.centralizer (H : Set G) ≤ Z := by
  have hp : p.Prime := Fact.out
  have hB1 : B ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hHc
    have h1 := Nat.card_pos (α := H)
    have h2 := hp.two_le
    nlinarith
  have hNC := normalizer_le_centralizer_center hR hZ
  have hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r := fun z hz r hr =>
    (mem_center_map_iff.1 (hZ ▸ hz)).2 r hr
  have hBp := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p B hB
  intro x hx
  obtain ⟨hxR, hxH⟩ := Subgroup.mem_inf.1 hx
  have hRx : R ≤ Subgroup.centralizer ({x} : Set G) := by
    refine le_of_hyperplane_centralizers hp hB hB1 hBR
      (coprime_card_of_le_isPGroup_two hp hp2 hR.1 le_rfl)
      fun H' hH'B hH'c y hy => Subgroup.mem_centralizer_singleton_iff.2 ?_
    by_cases hHH : H' = H
    · subst hHH
      exact (hab x hx y hy).symm
    obtain ⟨b, hbH, hbH'⟩ : ∃ b ∈ H, b ∉ H' := by
      by_contra! hc
      exact hHH (Subgroup.eq_of_le_of_card_ge (fun c hc' => hc c hc')
        (Nat.eq_of_mul_eq_mul_right hp.pos (hH'c.trans hHc.symm)).le).symm
    have hbB := hHB hbH
    have hBC : B ≤ Subgroup.centralizer (H' : Set G) := fun c hc =>
      Subgroup.mem_centralizer_iff.2 fun h hh => hB.comm (hH'B hh) hc
    have hbQ : b ∈ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (H' : Set G) :
        Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hBR hbB,
        le_normalizer_centralizer (hBC.trans (Subgroup.centralizer_le_normalizer _)) hbB⟩
    refine (commute_of_trivial_free (P := R ⊓ Subgroup.centralizer (H : Set G)) (Z := Z)
      (hBp.to_le (Subgroup.zpowers_le.2 hbB)) hbQ
      (coprime_card_of_le_isPGroup_two hp hp2 hR.1 inf_le_left) (fun q hq hbq => ?_)
      (fun w hw => Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hw).2 b hbH)
      (fun w hw q hq => ?_)
      (fun z hz => (Subgroup.mem_centralizer_iff.1 (hNC (hBR hbB)) z hz).symm)
      (fun z hz q hq => hZc z hz q (Subgroup.mem_inf.1 hq).1)
      (fun z hz w hw => hZc z hz w (Subgroup.mem_inf.1 hw).1) x hx y hy).symm
    · obtain ⟨hqR, hqH'⟩ := Subgroup.mem_inf.1 hq
      exact hCB (Subgroup.mem_inf.2
        ⟨hqR, mem_centralizer_of_hyperplane hp hH'B hH'c hbB hbH' hqH' hbq⟩)
    · rw [hZ]
      exact comm_mem_center_map hR (Subgroup.mem_inf.1 hw).1 (Subgroup.mem_inf.1 hq).1
  rw [hZ]
  exact mem_center_map_iff.2
    ⟨hxR, fun r hr => Subgroup.mem_centralizer_singleton_iff.1 (hRx hr)⟩

theorem radical_le_of_hyperplane_bound {G : Type*} [Group G] [Finite G] {p k : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hk : ∀ j, 0 < j → j < k → ¬ 2 ^ j ≡ 1 [MOD p])
    {R Z B T : Subgroup G} (hR : timmesfeldIsExtraspecial ↥R)
    (hZ : Z = (Subgroup.center ↥R).map R.subtype) (hB : IsElemAbelian p B)
    (hBR : B ≤ Subgroup.normalizer (R : Set G))
    (hCB : R ⊓ Subgroup.centralizer (B : Set G) ≤ Z)
    (hH : ∀ H : Subgroup G, H ≤ B → Nat.card H * p = Nat.card B →
      Nat.card ↥(R ⊓ Subgroup.centralizer (H : Set G)) ≤ 2 ^ (k + 1))
    (hZT : Z ≤ T) (hTR : T ≤ R) (hBT : B ≤ Subgroup.normalizer (T : Set G)) :
    ∀ s ∈ T, (∀ t ∈ T, s * t = t * s) → s ∈ Z := by
  have hp : p.Prime := Fact.out
  intro s hs hsc
  by_cases hB1 : B = ⊥
  · refine hCB (Subgroup.mem_inf.2 ⟨hTR hs, Subgroup.mem_centralizer_iff.2 fun c hc => ?_⟩)
    rw [hB1, SetLike.mem_coe, Subgroup.mem_bot] at hc
    rw [hc, one_mul, mul_one]
  have hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r := fun z hz r hr =>
    (mem_center_map_iff.1 (hZ ▸ hz)).2 r hr
  have hBZT : B ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) :
      Set G) :=
    (le_inf hBT (le_normalizer_centralizer hBT)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hsZT : s ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_inf.2 ⟨hs, Subgroup.mem_centralizer_iff.2 fun t ht => (hsc t ht).symm⟩
  refine le_of_hyperplane_centralizers hp hB hB1 hBZT
    (coprime_card_of_le_isPGroup_two hp hp2 hR.1 (inf_le_left.trans hTR))
    (fun H hHB hHc => ?_) hsZT
  have hBC : B ≤ Subgroup.centralizer (H : Set G) := fun c hc =>
    Subgroup.mem_centralizer_iff.2 fun h hh => hB.comm (hHB hh) hc
  have hBN := le_normalizer_centralizer (hBC.trans (Subgroup.centralizer_le_normalizer _))
  have hZT' : Z ≤ T ⊓ Subgroup.centralizer (T : Set G) := le_inf hZT fun z hz =>
    Subgroup.mem_centralizer_iff.2 fun t ht => hZc z hz t (hTR ht)
  have hZH : Z ≤ Subgroup.centralizer (H : Set G) := Subgroup.le_centralizer_iff.1
    ((hHB.trans hBR).trans (normalizer_le_centralizer_center hR hZ))
  rcases eq_or_eq_of_hyperplane hp2 hk hR hZ hB hBR hCB hHB hHc (hH H hHB hHc) (le_inf hZT' hZH)
      (inf_le_inf_right _ (inf_le_left.trans hTR))
      ((le_inf hBZT hBN).trans Subgroup.inf_normalizer_le_normalizer_inf) with h | h
  · exact h.le
  rw [h]
  refine le_of_comm_hyperplane hp2 hR hZ hB hBR hCB hHB hHc fun x hx y hy => ?_
  rw [← h] at hx hy
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2 y
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hy).1).1).symm

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
