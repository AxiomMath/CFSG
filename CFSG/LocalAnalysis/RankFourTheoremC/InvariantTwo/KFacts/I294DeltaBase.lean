module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294Assembly

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

@[expose] def KDInndiagAt (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ γ α : MulAut K, (∃ k : ℕ, α ^ p ^ k = 1) →
    (∃ k : ℕ, (γ * α * γ⁻¹ * α⁻¹) ^ p ^ k = 1) →
      γ * α * γ⁻¹ * α⁻¹ ∈ (MulAut.conj : K →* MulAut K).range

theorem kdInndiagP5_of_at
    (h : ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L → ¬ IsLinearOrUnitaryAt p L →
        KDInndiagAt p L) :
    KDInndiagP5 := by
  intro p hp h5 L _ _ hs hn hc hl
  exact h p hp h5 L hs hn hc hl

@[expose] def DeltaTowerAt (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∃ D : Subgroup (MulAut K),
    (∀ γ α : MulAut K, (∃ k : ℕ, α ^ p ^ k = 1) → γ * α * γ⁻¹ * α⁻¹ ∈ D) ∧
    ∀ δ ∈ D, (∃ k : ℕ, δ ^ p ^ k = 1) → δ ∈ (MulAut.conj : K →* MulAut K).range

theorem DeltaTowerAt.kdInndiagAt {p : ℕ} {K : Type*} [Group K] (h : DeltaTowerAt p K) :
    KDInndiagAt p K := by
  obtain ⟨D, hD, hp⟩ := h
  intro γ α hα hδ
  exact hp _ (hD γ α hα) hδ

theorem eq_conj_of_congr_eq_conj_aux {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    {σ : MulAut K} {g : L} (h : MulAut.congr e σ = MulAut.conj g) :
    σ = MulAut.conj (e.symm g) := by
  ext x
  have h1 : e (σ x) = g * e x * g⁻¹ := by
    have h2 := congrArg (fun φ : MulAut L => φ (e x)) h
    simpa [MulAut.conj_apply] using h2
  rw [MulAut.conj_apply]
  apply e.injective
  rw [h1]
  simp

theorem DeltaTowerAt.of_mulEquiv {p : ℕ} {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (h : DeltaTowerAt p L) : DeltaTowerAt p K := by
  obtain ⟨D, hD, hp⟩ := h
  refine ⟨D.comap (MulAut.congr e).toMonoidHom, fun γ α ⟨k, hk⟩ => ?_, fun δ hδ ⟨k, hk⟩ => ?_⟩
  · have hk' : (MulAut.congr e α) ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
    change MulAut.congr e (γ * α * γ⁻¹ * α⁻¹) ∈ D
    simpa only [map_mul, map_inv] using hD (MulAut.congr e γ) (MulAut.congr e α) ⟨k, hk'⟩
  · have hk' : (MulAut.congr e δ) ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
    obtain ⟨g, hg⟩ := hp (MulAut.congr e δ) hδ ⟨k, hk'⟩
    exact ⟨e.symm g, (eq_conj_of_congr_eq_conj_aux e hg.symm).symm⟩

theorem mem_inner_of_pElement_of_not_dvd {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    (D : Subgroup (MulAut K)) (hcard : ¬ p ∣ Nat.card (D ⧸ (inner K).subgroupOf D))
    {δ : MulAut K} (hδ : δ ∈ D) {k : ℕ} (hk : δ ^ p ^ k = 1) : δ ∈ inner K := by
  set N := (inner K).subgroupOf D with hN
  let x : D ⧸ N := QuotientGroup.mk ⟨δ, hδ⟩
  have hδk : (⟨δ, hδ⟩ : D) ^ p ^ k = 1 := Subtype.ext (by simpa using hk)
  have hx : x ^ p ^ k = 1 := by
    change (QuotientGroup.mk (⟨δ, hδ⟩ : D) : D ⧸ N) ^ p ^ k = 1
    rw [← QuotientGroup.mk_pow, hδk, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (p ^ k) (Nat.card (D ⧸ N)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hcard)
  have h4 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hx)
    (orderOf_dvd_natCard x)
  have h5 : x = 1 := orderOf_eq_one_iff.1 h4
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h5)

theorem DeltaTowerAt.of_card_not_dvd {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    (D : Subgroup (MulAut K))
    (hD : ∀ γ α : MulAut K, (∃ k : ℕ, α ^ p ^ k = 1) → γ * α * γ⁻¹ * α⁻¹ ∈ D)
    (hcard : ¬ p ∣ Nat.card (D ⧸ (inner K).subgroupOf D)) : DeltaTowerAt p K :=
  ⟨D, hD, fun _ hδ ⟨_, hk⟩ => mem_inner_of_pElement_of_not_dvd hp D hcard hδ hk⟩

theorem DeltaTowerAt.of_pComm {K : Type*} [Group K] {p : ℕ}
    (h : ∀ γ α : MulAut K, (∃ k : ℕ, α ^ p ^ k = 1) →
      γ * α * γ⁻¹ * α⁻¹ ∈ (MulAut.conj : K →* MulAut K).range) : DeltaTowerAt p K :=
  ⟨(MulAut.conj : K →* MulAut K).range, h, fun _ hδ _ => hδ⟩

theorem DeltaTowerAt.of_outerComm {K : Type*} [Group K] {p : ℕ}
    (h : ∀ γ α : MulAut K, γ * α * γ⁻¹ * α⁻¹ ∈ (MulAut.conj : K →* MulAut K).range) :
    DeltaTowerAt p K :=
  DeltaTowerAt.of_pComm fun γ α _ => h γ α

theorem DeltaTowerAt.of_pElem_inner {K : Type*} [Group K] {p : ℕ}
    (h : ∀ α : MulAut K, (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ (MulAut.conj : K →* MulAut K).range) :
    DeltaTowerAt p K :=
  ⟨⊤, fun _ _ _ => trivial, fun δ _ hδ => h δ hδ⟩

theorem DeltaTowerAt.of_not_dvd_card_outer {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (Outer K)) : DeltaTowerAt p K := by
  refine DeltaTowerAt.of_pElem_inner fun α ⟨k, hk⟩ => ?_
  have hcop : Nat.Coprime (p ^ k) (Nat.card (Outer K)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
  have h1 : (QuotientGroup.mk α : Outer K) ^ p ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
  have h4 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_natCard (QuotientGroup.mk α : Outer K))
  exact (QuotientGroup.eq_one_iff (N := inner K) α).1 (orderOf_eq_one_iff.1 h4)

theorem DeltaTowerAt.of_isPGroup_outer {K : Type*} [Group K] {r p : ℕ} (hr : r.Prime)
    (hp : p.Prime) (hrp : r ≠ p) (h : IsPGroup r (Outer K)) : DeltaTowerAt p K := by
  refine DeltaTowerAt.of_pElem_inner fun α ⟨k, hk⟩ => ?_
  obtain ⟨n, hn⟩ := h (QuotientGroup.mk α)
  have h1 : (QuotientGroup.mk α : Outer K) ^ p ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (r ^ n) (p ^ k) :=
    Nat.Coprime.pow n k ((Nat.coprime_primes hr hp).2 hrp)
  have hord : orderOf (QuotientGroup.mk α : Outer K) = 1 :=
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hn) hcop).eq_one_of_dvd
      (orderOf_dvd_of_pow_eq_one h1)
  exact (QuotientGroup.eq_one_iff (N := inner K) α).1 (orderOf_eq_one_iff.1 hord)

theorem DeltaTowerAt.of_outer_hom {K : Type*} [Group K] {C : Type*} [Group C]
    (hC : ∀ a b : C, a * b = b * a) (Φ : Outer K →* C) {p : ℕ} (hp : p.Prime)
    (hker : ¬ p ∣ Nat.card Φ.ker) : DeltaTowerAt p K := by
  set π : MulAut K →* Outer K := QuotientGroup.mk' (inner K) with hπ
  refine ⟨(Φ.comp π).ker, fun γ α _ => ?_, fun δ hδ ⟨k, hk⟩ => ?_⟩
  · rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hC ((Φ.comp π) γ) ((Φ.comp π) α)]
    group
  · have hδ' : π δ ∈ Φ.ker := hδ
    let x : Φ.ker := ⟨π δ, hδ'⟩
    have hx : x ^ p ^ k = 1 := Subtype.ext (by simp [x, ← map_pow, hk])
    have hcop : Nat.Coprime (p ^ k) (Nat.card Φ.ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hker)
    have h4 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hx)
      (orderOf_dvd_natCard x)
    have h5 : π δ = 1 := congrArg Subtype.val (orderOf_eq_one_iff.1 h4)
    exact (QuotientGroup.eq_one_iff (N := inner K) δ).1 h5

end CFSG.LocalAnalysis.RankFourTheoremC
