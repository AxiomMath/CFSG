module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenOdd

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def OddNode {K : Type*} [Group K] (R : Subgroup K) (p : ℕ) : Prop :=
  ∃ w ∈ R, ∃ m ∈ R, w ^ p = 1 ∧ w ≠ 1 ∧ m * w * m⁻¹ = w⁻¹

theorem not_mem_center_of_inverted {K : Type*} [Group K] {p : ℕ} (hp : Odd p) {w m : K}
    (hw : w ^ p = 1) (hw1 : w ≠ 1) (hm : m * w * m⁻¹ = w⁻¹) : w ∉ Subgroup.center K := by
  intro hc
  have h1 : m * w * m⁻¹ = w := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_center_iff.1 hc m
  have h3 : w ^ 2 = 1 := by
    have : w = w⁻¹ := h1.symm.trans hm
    calc w ^ 2 = w * w⁻¹ := by rw [pow_two]; nth_rewrite 2 [this]; rfl
      _ = 1 := mul_inv_cancel w
  have hd1 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one h3
  have hd2 : orderOf w ∣ p := orderOf_dvd_of_pow_eq_one hw
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.2 hp
  exact hw1 (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2))

section Main

variable {W : Type} [Group W] [Finite W] {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem chevGen_centre_of_nodes {L S₀ : Subgroup W} (hL : Open.IsQuasisimple ↥L)
    (hS : IsSylowTwoOf S₀ L) {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M)
    (h3 : ∀ i, HasInvolThree D i)
    (hnodes : ∀ i, ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card (Subgroup.center ↥L) →
      OddNode (rankOne D.rootGroup i) p) :
    ∃ P : Fin D.rank → Subgroup W, (∀ i, IsMinOverBorel L S₀ (P i)) ∧
      L = ⨆ i, pElementSubgroup 2 (P i) ∧
      ∀ i, ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card (Subgroup.center ↥L) →
        ∃ x ∈ pElementSubgroup 2 (P i), orderOf x = p ∧
          x ∉ (Subgroup.center ↥L).map L.subtype := by
  classical
  obtain ⟨π', hπ', P, hmin, hgen, h3el, hlift⟩ := chevGen_data hL hS h h3
  refine ⟨P, hmin, hgen, ?_⟩
  intro i p hp hp2 hpZ
  set Z := Subgroup.center ↥L with hZ
  set q : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hqdef
  have hqker : q.ker = Z := by rw [hqdef, QuotientGroup.ker_mk']
  by_cases hp3 : p = 3
  · subst hp3
    exact h3el i
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
    omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, hwR, m, hmR, hwp, hw1, hm⟩ := hnodes i p hp hp5 hpZ
  set G : Subgroup ↥L := (pElementSubgroup 2 (P i)).subgroupOf L with hG
  set T : Subgroup K := (G.map q).comap π' with hT
  have hroot2 : ∀ γ : Fin D.rank → ℤ, γ ∈ D.roots → ∀ x ∈ D.rootGroup γ, ∃ k : ℕ, x ^ 2 ^ k = 1 :=
    fun γ hγ x hx => by
      obtain ⟨k, hk⟩ := hπ'.pGroup γ hγ ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hαroot : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots ∧
      (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    ⟨(RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i,
      (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)⟩
  have hrankT : rankOne D.rootGroup i ≤ T := by
    have hroot : ∀ γ : Fin D.rank → ℤ, γ ∈ D.roots → D.rootGroup γ ≤ rankOne D.rootGroup i →
        D.rootGroup γ ≤ T := by
      intro γ hγ hγL x hx
      obtain ⟨a, haq, haW, -⟩ := hlift i x (hroot2 γ hγ x hx) (hγL hx)
      exact ⟨a, Subgroup.mem_subgroupOf.2 haW, haq⟩
    show D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) ≤ T
    exact sup_le (hroot _ hαroot.1 le_sup_left) (hroot _ hαroot.2 le_sup_right)
  obtain ⟨a, haG, haq⟩ := hrankT hwR
  obtain ⟨b, hbG, hbq⟩ := hrankT hmR
  have hker : ∀ z, q z = 1 → z ∈ Subgroup.center ↥L := fun z hz => by
    have h0 : z ∈ q.ker := hz
    rw [hqker] at h0; exact h0
  have hwK : w ∉ Subgroup.center K := not_mem_center_of_inverted hpodd hwp hw1 hm
  have hπw : π' w ≠ 1 := fun h1 => hwK (hπ'.ker_central w h1)
  obtain ⟨y, hyG, hyp, hyq⟩ := exists_prime_order_inverted q hker G hp hp2 haG hbG
    (by rw [haq, ← map_pow, hwp, map_one])
    (by rw [map_mul, map_mul, map_inv, haq, hbq]
        simpa [map_mul, map_inv] using congrArg π' hm)
  have hy1 : y ≠ 1 := fun h1 => hπw (by rw [← haq, ← hyq, h1, map_one])
  refine ⟨(y : W), ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.1 hyG
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hyp hy1
  · rintro ⟨z, hz, hzy⟩
    have hzy' : z = y := Subtype.ext hzy
    subst hzy'
    have : q z = 1 := by rw [← MonoidHom.mem_ker, hqker]; exact hz
    exact hπw (by rw [← haq, ← hyq, this])

end Main

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
