module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocalThreeB
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.BRank0
public import CFSG.GroupTheory.ThreeTranspositions.StrongSup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Timmesfeld.SporadicBalance

private theorem pureB_exists_hom_conj {G : Type*} [Group G] {t x c : G} (hc : c * t * c⁻¹ = x)
    {D : Subgroup G} (hDt : D ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ φ : D →* Subgroup.centralizer ({x} : Set G),
      Function.Injective φ ∧ ∀ d : D, IsConj (d : G) (φ d : G) := by
  refine ⟨((MulAut.conj c).toMonoidHom.comp D.subtype).codRestrict _ fun d => ?_,
    fun d₁ d₂ h => ?_, fun d => isConj_iff.2 ⟨c, rfl⟩⟩
  · have h : (d : G) * t = t * d := Subgroup.mem_centralizer_singleton_iff.1 (hDt d.2)
    show c * (d : G) * c⁻¹ ∈ _
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    calc c * d * c⁻¹ * (c * t * c⁻¹) = c * (d * t) * c⁻¹ := by group
      _ = c * (t * d) * c⁻¹ := by rw [h]
      _ = c * t * c⁻¹ * (c * d * c⁻¹) := by group
  · have h' : c * (d₁ : G) * c⁻¹ = c * d₂ * c⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))

private theorem pureB_injective_comp {H K P : Type*} [Group H] [Group K] [Group P] {F : H →* K}
    (hker : Nat.card F.ker = 2 ^ 23) {φ : P →* H} (hφ : Function.Injective φ)
    (h3 : ∀ p : P, p ^ 3 = 1) : Function.Injective (F.comp φ) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  have hmem : φ p ∈ F.ker := MonoidHom.mem_ker.2 hp
  have h1 : orderOf (φ p) ∣ 2 ^ 23 := by
    rw [← hker]
    exact Subgroup.orderOf_dvd_natCard F.ker hmem
  have h2 : orderOf (φ p) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, h3, map_one])
  have h4 : orderOf (φ p) ∣ Nat.gcd 3 (2 ^ 23) := Nat.dvd_gcd h2 h1
  rw [show Nat.gcd 3 (2 ^ 23) = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact hφ (h4.trans (map_one φ).symm)

private theorem pureB_isElemAbelian_range {G K : Type*} [Group G] [Group K] {D : Subgroup G}
    (hD : IsElemAbelian 3 D) (f : D →* K) : IsElemAbelian 3 f.range := by
  haveI := hD.1
  refine ⟨Subgroup.range_isMulCommutative f, ?_⟩
  rintro _ ⟨d, rfl⟩
  rw [← map_pow, show d ^ 3 = 1 from Subtype.ext (by simpa using hD.2 d d.2), map_one]

private theorem pureB_exists_isConj {H K P P₀ : Type*} [Group H] [Finite H] [Group K] [Group P]
    [Group P₀] {F : H →* K} (hF : Function.Surjective F) (hker : ¬ 3 ∣ Nat.card F.ker)
    (φ : P →* H) (φ₀ : P₀ →* H) (h3 : ∀ q : P₀, q ^ 3 = 1) {k : K}
    (hk : (F.comp φ).range.map (MulAut.conj k).toMonoidHom = (F.comp φ₀).range) (q : P₀) :
    ∃ p : P, IsConj (φ p) (φ₀ q) := by
  obtain ⟨k', rfl⟩ := hF k
  have hR : IsPGroup 3 φ₀.range :=
    IsPGroup.of_surjective (fun q => ⟨1, by rw [pow_one]; exact h3 q⟩) φ₀.rangeRestrict
      φ₀.rangeRestrict_surjective
  have hle : φ₀.range ≤ φ.range.map (MulAut.conj k').toMonoidHom ⊔ F.ker := by
    rintro _ ⟨q', rfl⟩
    have hmem : F (φ₀ q') ∈ (F.comp φ).range.map (MulAut.conj (F k')).toMonoidHom := by
      rw [hk]
      exact ⟨q', rfl⟩
    obtain ⟨_, ⟨p, rfl⟩, hp⟩ := hmem
    have hz : k' * φ p * k'⁻¹ ∈ φ.range.map (MulAut.conj k').toMonoidHom :=
      ⟨φ p, ⟨p, rfl⟩, rfl⟩
    have hFz : F (k' * φ p * k'⁻¹) = F (φ₀ q') := by
      rw [← hp]
      simp
    have hn : (k' * φ p * k'⁻¹)⁻¹ * φ₀ q' ∈ F.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hFz, inv_mul_cancel]
    have h := Subgroup.mul_mem_sup hz hn
    rwa [mul_inv_cancel_left] at h
  obtain ⟨n, -, hn⟩ :=
    CFSG.GroupTheory.ThreeTranspositions.exists_mem_conj_le_of_isPGroup_of_le_sup
      Nat.prime_three hker hR hle
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := hn (φ₀ q) ⟨q, rfl⟩
  have hp' : k' * φ p * k'⁻¹ = n⁻¹ * φ₀ q * n := hp
  refine ⟨p, isConj_iff.2 ⟨n * k', ?_⟩⟩
  calc n * k' * φ p * (n * k')⁻¹ = n * (k' * φ p * k'⁻¹) * n⁻¹ := by group
    _ = φ₀ q := by rw [hp']; group


theorem babyNoPureFourAt_one_of
    (hCo : ∀ A₁ A₂ : Subgroup NativeSporadic.Co2, IsElemAbelian 3 A₁ → IsElemAbelian 3 A₂ →
      Nat.card A₁ = 3 ^ 4 → Nat.card A₂ = 3 ^ 4 → ∃ k, A₁.map (MulAut.conj k).toMonoidHom = A₂)
    (hD0 : ∃ t₁ : NativeSporadic.B, BabyInv 1 t₁ ∧ ∃ D₀ : Subgroup NativeSporadic.B,
      D₀ ≤ Subgroup.centralizer ({t₁} : Set NativeSporadic.B) ∧ IsElemAbelian 3 D₀ ∧
      Nat.card D₀ = 3 ^ 4 ∧ ∃ y ∈ D₀, IsConj y (BThreeFi23.phiB (BThreeFi23.t3 0))) :
    BabyNoPureFourAt 1 := by
  intro t ht D hDt hD hDcard
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨t₁, ht₁, D₀, hD₀t, hD₀, hD₀card, y, hy, hyc⟩ := hD0
  obtain ⟨F, hF, hker⟩ := exists_hom_centralizer_xB
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 1 t xB ht babyInv_one_xB)
  obtain ⟨c₁, hc₁⟩ :=
    isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 1 t₁ xB ht₁ babyInv_one_xB)
  obtain ⟨φ, hφ, hφc⟩ := pureB_exists_hom_conj hc hDt
  obtain ⟨φ₀, hφ₀, hφ₀c⟩ := pureB_exists_hom_conj hc₁ hD₀t
  have h3 : ∀ d : D, d ^ 3 = 1 := fun d => Subtype.ext (by simpa using hD.2 d d.2)
  have h3₀ : ∀ d : D₀, d ^ 3 = 1 := fun d => Subtype.ext (by simpa using hD₀.2 d d.2)
  have hinj := pureB_injective_comp hker hφ h3
  have hinj₀ := pureB_injective_comp hker hφ₀ h3₀
  obtain ⟨k, hk⟩ := hCo _ _ (pureB_isElemAbelian_range hD (F.comp φ))
    (pureB_isElemAbelian_range hD₀ (F.comp φ₀))
    ((Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hDcard)
    ((Nat.card_congr (MonoidHom.ofInjective hinj₀).toEquiv).symm.trans hD₀card)
  obtain ⟨d, hd⟩ := pureB_exists_isConj hF (by rw [hker]; norm_num) φ φ₀ h3₀ hk ⟨y, hy⟩
  have hd' : IsConj (φ d : NativeSporadic.B) (φ₀ ⟨y, hy⟩ : NativeSporadic.B) :=
    (Subgroup.centralizer ({xB} : Set NativeSporadic.B)).subtype.map_isConj hd
  have hdy : IsConj (d : NativeSporadic.B) (BThreeFi23.phiB (BThreeFi23.t3 0)) :=
    ((hφc d).trans hd').trans ((hφ₀c ⟨y, hy⟩).symm.trans hyc)
  have hrk : BSevenLocal.rk (d : NativeSporadic.B) = 2862 := by
    obtain ⟨g, hg⟩ := isConj_iff.1 hdy
    rw [← BSevenLocal.rk_conj g, hg]
    exact CFSG.HardMathSupport.Solomon.Coordinator.B3B.rk_phiB_t3_zero
  refine ⟨(d : NativeSporadic.B), d.2, fun h1 => ?_, fun h3B => ?_⟩
  · rw [h1] at hrk
    simp [BSevenLocal.rk] at hrk
  · obtain ⟨g, hg⟩ := isConj_iff.1 h3B
    have e := BSevenLocal.rk_conj g (d : NativeSporadic.B)
    rw [hg, BSevenLocal.rk_phiB_t3_one.1] at e
    omega

end CFSG.LocalAnalysis.GLTheoremA.H1017
