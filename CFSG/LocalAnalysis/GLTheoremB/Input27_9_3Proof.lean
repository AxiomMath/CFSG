module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Main
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open GL83.PiGen

section Acts

variable {X : Type*} [Group X] {K T : Subgroup X} {n : ℕ}

theorem implements_of_congr_eq (e : ↥K ≃* ↥(alternatingGroup (Fin n))) {t : X}
    (ht : t ∈ Subgroup.normalizer (K : Set X)) {σ : Equiv.Perm (Fin n)}
    (h : MulAut.congr e (K.normalizerMonoidHom ⟨t, ht⟩) = MulAut.conjNormal σ) :
    Implements e t σ := by
  intro x
  refine ⟨K.normalizerMonoidHom ⟨t, ht⟩ x,
    Subgroup.normalizerMonoidHom_apply_apply_coe K _ x, ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥(alternatingGroup (Fin n)) =>
    ((φ (e x) : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))) h
  simp only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  exact h1.symm

theorem transposition_data (hTN : T ≤ Subgroup.normalizer (K : Set X))
    (e : ↥K ≃* ↥(alternatingGroup (Fin n))) (τ : Equiv.Perm (Fin n))
    (hact : ActsLike T K e
      (Subgroup.zpowers (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ))) :
    (∀ t ∈ T, ∃ j : ℤ, Implements e t (τ ^ j)) ∧ ∃ t ∈ T, Implements e t τ := by
  have hmem : ∀ {t : X} (ht : t ∈ T), MulAut.congr e (K.normalizerMonoidHom ⟨t, hTN ht⟩) ∈
      Subgroup.zpowers (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ) := by
    intro t ht
    rw [← hact]
    exact ⟨K.normalizerMonoidHom ⟨t, hTN ht⟩,
      ⟨⟨t, hTN ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩, rfl⟩
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hmem ht)
    refine ⟨j, implements_of_congr_eq e (hTN ht) ?_⟩
    rw [← hj, map_zpow]
  · have h1 : (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ) ∈
        (inducedAutGroup T K).map (MulAut.congr e).toMonoidHom := by
      rw [hact]
      exact Subgroup.mem_zpowers _
    obtain ⟨c, hc, hc'⟩ := h1
    obtain ⟨t', ht', hct'⟩ := hc
    refine ⟨(t' : X), Subgroup.mem_subgroupOf.1 ht', implements_of_congr_eq e t'.2 ?_⟩
    rw [← hct'] at hc'
    exact hc'

end Acts

section AltFacts

variable {L : Type*} [Group L]

theorem center_eq_bot_of_mulEquiv_alt {n : ℕ} (hn : 4 ≤ n) (e : L ≃* alternatingGroup (Fin n)) :
    Subgroup.center L = ⊥ := by
  have h1 : (Subgroup.center L).map (e : L →* alternatingGroup (Fin n)) = ⊥ := by
    rw [Subgroup.map_center_eq e, alternatingGroup.center_eq_bot (by simpa using hn)]
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1

theorem alt_facts {p k' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk' : 1 ≤ k')
    (e : L ≃* alternatingGroup (Fin (k' * p + 2))) :
    IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ p ∣ Nat.card L ∧ Subgroup.center L = ⊥ := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hm5 : 5 ≤ k' * p + 2 := by
    have : 1 * 3 ≤ k' * p := Nat.mul_le_mul hk' hp3
    omega
  have hcardm : Nat.card (Fin (k' * p + 2)) = k' * p + 2 := by simp
  have hs : IsSimpleGroup (alternatingGroup (Fin (k' * p + 2))) :=
    alternatingGroup.isSimpleGroup (by omega)
  refine ⟨e.isSimpleGroup, ?_, ?_, center_eq_bot_of_mulEquiv_alt (by omega) e⟩
  · by_contra hcomm
    have hc : IsMulCommutative L := isMulCommutative_iff.mpr
      (fun a b => not_ne_iff.mp (fun hne => hcomm ⟨a, b, hne⟩))
    have hc' : IsMulCommutative (alternatingGroup (Fin (k' * p + 2))) :=
      ⟨⟨fun a b => e.symm.injective (by
        rw [map_mul, map_mul]
        exact mul_comm' (e.symm a) (e.symm b))⟩⟩
    have := alternatingGroup.isMulCommutative_iff_card_le_three.1 hc'
    omega
  · rw [Nat.card_congr e.toEquiv]
    have h2 := two_mul_nat_card_alternatingGroup (α := Fin (k' * p + 2))
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin (k' * p + 2))), Fintype.card_perm,
      Fintype.card_fin] at h2
    have hple : p ≤ k' * p := Nat.le_mul_of_pos_left p hk'
    have hdvd : p ∣ (k' * p + 2).factorial := Nat.dvd_factorial hp.pos (by omega)
    rw [← h2] at hdvd
    exact ((Nat.Prime.dvd_mul hp).1 hdvd).resolve_left fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)

theorem isPiGroup_of_equiv_alt [Finite L] {p k' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk' : 1 ≤ k')
    (e : L ≃* alternatingGroup (Fin (k' * p + 2))) : IsPiGroup p L := by
  obtain ⟨hs, hnc, hdvd, hZ⟩ := alt_facts hp hp2 hk' e
  refine ⟨isQuasisimple_of_simple_nonabelian hnc, ?_,
    Or.inl ⟨k', ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).trans e⟩⟩⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p L) with h | h
  · exact h
  · exfalso
    have hcop := coprime_card_glaPPrimeCore hp L
    rw [h, Subgroup.card_top] at hcop
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdvd)

end AltFacts

theorem input27_9_3_alt {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) {B : Subgroup X} (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) {T : Subgroup X}
    (hTN : T ≤ Subgroup.normalizer (K : Set X)) (hBT : B ≤ Subgroup.normalizer (T : Set X))
    (hact : ActsAsTransposition p T K) (hrank : GLATwoLocalRank p X ≤ CFSG.Open.pRank p B)
    {D : Subgroup X} (hDB : D ≤ B) (hD : IsPPlane p D) :
    ∃ (𝒟 : Set X) (Kf : X → Subgroup X),
      (∀ d ∈ 𝒟, d ∈ D ∧ d ≠ 1) ∧
      (∀ d ∈ 𝒟, GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set X)) (Kf d) ∧
        B ⊔ T ≤ Subgroup.normalizer (Kf d : Set X) ∧ IsPiGroup p ↥(Kf d) ∧
        ¬ T ≤ Subgroup.centralizer (Kf d : Set X)) ∧
      K = ⨆ d ∈ 𝒟, Kf d := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk, e, τ, hτ, -, hactL⟩ := hact
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hn5 : 5 ≤ k * p + 2 := by
    have h13 : 1 * 3 ≤ k * p := Nat.mul_le_mul hk hp3
    omega
  have hn6 : k * p + 2 ≠ 6 := by
    intro h
    have hdvd : p ∣ 4 := ⟨k, by have := mul_comm k p; omega⟩
    have : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p
    · exact absurd hdvd (by norm_num)
    · exact absurd hp (by norm_num)
  have hZ : Subgroup.center K = ⊥ := center_eq_bot_of_mulEquiv_alt (by omega) e
  obtain ⟨hT, hTτ⟩ := transposition_data hTN e τ hactL
  obtain ⟨𝒟, Kf, h1, h2, h3⟩ := exists_subAlt_family hp3 hk rfl hn5 hn6 hZ hK e hB hBN hrank hBT
    hTN hτ hT hTτ hDB hD.2
  refine ⟨𝒟, Kf, h1, fun d hd => ?_, h3⟩
  obtain ⟨hle, hnorm, ⟨k', hk', ⟨eq⟩⟩, hBT', hcent⟩ := h2 d hd
  obtain ⟨hs, hnc, hdvd, -⟩ := alt_facts hp hp2 hk' eq
  refine ⟨?_, hBT', isPiGroup_of_equiv_alt hp hp2 hk' eq, hcent⟩
  exact glaPComponent_of_normal_simple hp hle hnorm hnc hdvd

@[expose] def Input27_9_3Transv : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      ∀ B : Subgroup X, IsElemAbelian p B → B ≤ Subgroup.normalizer (K : Set X) →
        ∀ T : Subgroup X, IsPGroup 2 T → T ≤ Subgroup.normalizer (K : Set X) →
          B ≤ Subgroup.normalizer (T : Set X) →
          ActsAsTransvection p T K →
          ∀ D : Subgroup X, D ≤ B → IsPPlane p D →
            ∃ (𝒟 : Set X) (Kf : X → Subgroup X),
              (∀ d ∈ 𝒟, d ∈ D ∧ d ≠ 1) ∧
              (∀ d ∈ 𝒟, GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set X)) (Kf d) ∧
                B ⊔ T ≤ Subgroup.normalizer (Kf d : Set X) ∧ IsPiGroup p ↥(Kf d) ∧
                ¬ T ≤ Subgroup.centralizer (Kf d : Set X)) ∧
              K = ⨆ d ∈ 𝒟, Kf d

theorem input27_9_3_of_transv (h : Input27_9_3Transv) : Input27_9_3 := by
  intro X _ _ p hp hp2 K hK B hB hBN T hT2 hTN hBT hcase D hDB hD
  rcases hcase with ⟨hact, hrank⟩ | hact
  · exact input27_9_3_alt hp hp2 hK hB hBN hTN hBT hact hrank hDB hD
  · exact h X p hp hp2 K hK B hB hBN T hT2 hTN hBT hact D hDB hD

end CFSG.LocalAnalysis.GLTheoremB
