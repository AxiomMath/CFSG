module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111BaseIndexKappa

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ}

structure Hyp93At (p : ℕ) (M N : Subgroup G) : Prop where
  fac : ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ k : N,
    QuotientGroup.mk' (primeComplementCore (G := N) p) k ∈ d1KBar p M N ∧ x = m * k
  core_le : (primeComplementCore (G := N) p).map N.subtype ≤ M

@[expose] def Hyp917At (p : ℕ) (M H N : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ∃ W : Subgroup G, ∃ hW : W ≤ H ⊓ N,
    (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K ∧
    ((W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≤ d1KBar p M N ∨
      (∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y) ∨ d1Kappa p M H < d1Kappa p M N)

@[expose] def Hyp917EqAt (p : ℕ) (M H N : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ∃ W : Subgroup G, ∃ hW : W ≤ H ⊓ N,
    (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K ∧
    ((W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) = d1KBar p M N ∨
      (∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y))

theorem noPPrime_of_normal {H : Subgroup G} (K : Subgroup (H ⧸ primeComplementCore (G := H) p))
    [K.Normal] (V : Subgroup K) (hV : V.Normal) (hcop : p.Coprime (Nat.card V)) : V = ⊥ := by
  set A : Subgroup K := primeComplementCore (G := K) p
  have : A.Characteristic := primeComplementCore_characteristic p
  have hVA : V ≤ A := normal_coprime_le_primeComplementCore p V hV hcop
  have hAn : (A.map K.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hAcop : p.Coprime (Nat.card (A.map K.subtype)) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact primeComplementCore_coprime p
  have hAbot : A.map K.subtype = ⊥ := by
    have := normal_coprime_le_primeComplementCore p _ hAn hAcop
    rwa [primeComplementCore_quotient_eq_bot, le_bot_iff] at this
  rw [eq_bot_iff]
  intro v hv
  have : (v : H ⧸ primeComplementCore (G := H) p) ∈ A.map K.subtype := ⟨v, hVA hv, rfl⟩
  rw [hAbot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (Subtype.ext this)

theorem card_le_card_map_of_noPPrime {H N W : Subgroup G} (hW : W ≤ H ⊓ N)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hWK : (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K)
    (hKp : ∀ V : Subgroup K, V.Normal → p.Coprime (Nat.card V) → V = ⊥) :
    Nat.card K ≤
      Nat.card ((W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p))) := by
  set πH := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set πN := QuotientGroup.mk' (primeComplementCore (G := N) p)
  have hWH : W ≤ H := hW.trans inf_le_left
  have hWN : W ≤ N := hW.trans inf_le_right
  set fH : W →* H ⧸ primeComplementCore (G := H) p := πH.comp (Subgroup.inclusion hWH)
  set fN : W →* N ⧸ primeComplementCore (G := N) p := πN.comp (Subgroup.inclusion hWN)
  have hrH : fH.range = K := by
    rw [← hWK]
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Subgroup.inclusion hWH w, Subgroup.mem_subgroupOf.mpr w.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩
  have hrN : fN.range = (W.subgroupOf N).map πN := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Subgroup.inclusion hWN w, Subgroup.mem_subgroupOf.mpr w.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩
  have hψ : ∀ w, fH w ∈ K := fun w => hrH ▸ ⟨w, rfl⟩
  set ψ : W →* K := fH.codRestrict K hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨k, hk⟩
    rw [← hrH] at hk
    obtain ⟨w, hw⟩ := hk
    exact ⟨w, Subtype.ext hw⟩
  have hcopN : p.Coprime (Nat.card fN.ker) := by
    set g : fN.ker →* primeComplementCore (G := N) p :=
      ((Subgroup.inclusion hWN).comp fN.ker.subtype).codRestrict _
        (fun w => (QuotientGroup.eq_one_iff _).mp w.2)
    have hinj : Function.Injective g := by
      intro a b hab
      have := congrArg (fun x : primeComplementCore (G := N) p => ((x : N) : G)) hab
      exact Subtype.ext (Subtype.ext this)
    exact (primeComplementCore_coprime (G := N) p).coprime_dvd_right
      (Subgroup.card_dvd_of_injective g hinj)
  have hV : fN.ker.map ψ = ⊥ := by
    refine hKp _ (Subgroup.Normal.map inferInstance ψ hψs) ?_
    exact hcopN.coprime_dvd_right (Subgroup.card_map_dvd _ _)
  have hker : fN.rangeRestrict.ker ≤ fH.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.ker_rangeRestrict]
    intro w hw
    have hψw : ψ w ∈ fN.ker.map ψ := ⟨w, hw, rfl⟩
    rw [hV, Subgroup.mem_bot] at hψw
    exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hψw)
  obtain ⟨φ, -, hφs, -⟩ := exists_surjective_comp_eq fN.rangeRestrict fN.rangeRestrict_surjective
    fH.rangeRestrict fH.rangeRestrict_surjective hker
  calc Nat.card K = Nat.card fH.range := by rw [hrH]
    _ ≤ Nat.card fN.range := Nat.card_le_card_of_surjective φ hφs
    _ = Nat.card ((W.subgroupOf N).map πN) := by rw [hrN]

theorem factor_of_map_eq {M H N W : Subgroup G} (hN : Hyp93At p M N) (hW : W ≤ H ⊓ N)
    (heq : d1KBar p M N ≤
      (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p))) :
    ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y := by
  intro x hx
  obtain ⟨m, hm, k, hk, rfl⟩ := hN.fac x hx
  obtain ⟨w, hwW, hwk⟩ := heq hk
  have hwN : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hwW
  have ho1 : QuotientGroup.mk' (primeComplementCore (G := N) p) (k * w⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hwk, mul_inv_cancel]
  have ho : k * w⁻¹ ∈ primeComplementCore (G := N) p := (QuotientGroup.eq_one_iff _).mp ho1
  have hoM : ((k * w⁻¹ : N) : G) ∈ M := hN.core_le ⟨_, ho, rfl⟩
  refine ⟨m * ((k * w⁻¹ : N) : G), ⟨N.mul_mem hm.1 (k * w⁻¹).2, M.mul_mem hm.2 hoM⟩, w,
    hW hwN, ?_⟩
  simp [mul_assoc]

theorem factor_of_le_d1KBar {M H N W : Subgroup G} (hN : Hyp93At p M N) (hW : W ≤ H ⊓ N)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hWK : (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K)
    (hKp : ∀ V : Subgroup K, V.Normal → p.Coprime (Nat.card V) → V = ⊥)
    (hκ : d1Kappa p M H ≤ Nat.card K)
    (hle : (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≤
      d1KBar p M N)
    (hNH : d1Kappa p M N ≤ d1Kappa p M H) :
    ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y := by
  refine factor_of_map_eq hN hW (Subgroup.eq_of_le_of_card_ge hle ?_).ge
  have := card_le_card_map_of_noPPrime hW hWK hKp
  unfold d1Kappa at hNH hκ
  omega

theorem aglRankTwoFactorAt_of_at {M H B : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hat : ∀ N T : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → B ≤ N → AGLCovers p H N K →
      B ≤ T → T ≤ N → T ≤ M → IsPGroup p T →
      (∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) →
      (T = B ∨ Open.pRank p T ≤ 2) → Hyp93At p M N ∧ Hyp917EqAt p M H N K) :
    AGLRankTwoFactorAt p M H B K := by
  intro N T hN hNM hBN hcov hBT hTN hTM hT hmax hor
  obtain ⟨h93, W, hW, -, heq | hfac⟩ := hat N T hN hNM hBN hcov hBT hTN hTM hT hmax hor
  · exact factor_of_map_eq h93 hW heq.ge
  · exact hfac

theorem Hyp917At.toEq {M H N : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (h : Hyp917At p M H N K)
    (hKp : ∀ V : Subgroup K, V.Normal → p.Coprime (Nat.card V) → V = ⊥)
    (hκ : d1Kappa p M H ≤ Nat.card K) (hNH : d1Kappa p M N ≤ d1Kappa p M H) :
    Hyp917EqAt p M H N K := by
  obtain ⟨W, hW, hWK, hle | hfac | hlt⟩ := h
  · refine ⟨W, hW, hWK, Or.inl (Subgroup.eq_of_le_of_card_ge hle ?_)⟩
    have := card_le_card_map_of_noPPrime hW hWK hKp
    unfold d1Kappa at hNH hκ
    omega
  · exact ⟨W, hW, hWK, Or.inr hfac⟩
  · exact absurd hNH (not_le.mpr hlt)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
