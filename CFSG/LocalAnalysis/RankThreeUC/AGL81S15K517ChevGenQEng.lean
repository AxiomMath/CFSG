module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517ChevGenQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenCentre

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517ChevGenQ

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

@[expose] def HasQModel (Y : Type) [Group Y] (N : ℕ) : Prop :=
  ∃ (K : Type) (_ : Group K) (_ : Finite K) (D : UniversalRootDatum K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) (π : K →* Y) (M : ℕ),
    BorelQuotient D n H π M ∧ (∀ i, HasInvolThree D i) ∧
    ∀ i, ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ N → OddNode (rankOne D.rootGroup i) p

section Engine

variable {W : Type} [Group W] [Finite W] {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem exists_pElement_of_nodes {L S₀ : Subgroup W} (hL : Open.IsQuasisimple ↥L)
    (hS : IsSylowTwoOf S₀ L) {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M)
    (h3 : ∀ i, HasInvolThree D i) {N : ℕ} (hN : ¬ 2 ∣ N)
    (hnodes : ∀ i, ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ N → OddNode (rankOne D.rootGroup i) p) :
    ∃ P : Fin D.rank → Subgroup W, (∀ i, IsMinOverBorel L S₀ (P i)) ∧
      L = ⨆ i, pElementSubgroup 2 (P i) ∧
      ∀ i, ∀ p : ℕ, p.Prime → p ∣ N → ∃ x ∈ pElementSubgroup 2 (P i), orderOf x = p := by
  classical
  obtain ⟨π', hπ', P, hmin, hgen, -, hlift⟩ := chevGen_data hL hS h h3
  refine ⟨P, hmin, hgen, ?_⟩
  intro i p hp hpN
  have hp2 : p ≠ 2 := fun h2 => hN (h2 ▸ hpN)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  haveI : Fact p.Prime := ⟨hp⟩
  set Z := Subgroup.center ↥L with hZ
  set q : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hqdef
  obtain ⟨w, hwR, m, hmR, hwp, hw1, hm⟩ := hnodes i p hp hp2 hpN
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
  have hwK : w ∉ Subgroup.center K := not_mem_center_of_inverted hpodd hwp hw1 hm
  have hπw : π' w ≠ 1 := fun h1 => hwK (hπ'.ker_central w h1)
  have hqa : orderOf (q a) = p := by
    rw [haq]
    exact orderOf_eq_prime (by rw [← map_pow, hwp, map_one]) hπw
  have hpa : p ∣ orderOf a := hqa ▸ orderOf_map_dvd q a
  refine ⟨((a ^ (orderOf a / p) : ↥L) : W), Subgroup.mem_subgroupOf.1
    (Subgroup.pow_mem G haG (orderOf a / p)), ?_⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div (orderOf_pos a).ne' hpa

theorem psSet_of_nodes {S₀ L : Subgroup W} {m : ℕ} {Q : Subgroup W → Prop}
    {P : Fin m → Subgroup W} (hmin : ∀ i, IsMinOverBorel L S₀ (P i))
    (hgen : L = ⨆ i, pElementSubgroup 2 (P i)) (hQ : ∀ i, Q (P i)) :
    ∃ Ps : Set (Subgroup W), (∀ P ∈ Ps, IsMinOverBorel L S₀ P) ∧
      L = ⨆ P ∈ Ps, pElementSubgroup 2 P ∧ ∀ P ∈ Ps, Q P := by
  refine ⟨Set.range P, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hmin i
  · rw [hgen]
    refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun Q hQ => ?_)
    · exact le_iSup₂ (f := fun (Q : Subgroup W) (_ : Q ∈ Set.range P) => pElementSubgroup 2 Q)
        (P i) ⟨i, rfl⟩
    · obtain ⟨i, rfl⟩ := hQ
      exact le_iSup (fun i => pElementSubgroup 2 (P i)) i
  · rintro _ ⟨i, rfl⟩
    exact hQ i

theorem chevGenQ_of_hasQModel {L S₀ : Subgroup W} (hL : Open.IsQuasisimple ↥L)
    (hS : IsSylowTwoOf S₀ L) {N : ℕ} (hN : ¬ 2 ∣ N)
    (h : HasQModel (↥L ⧸ Subgroup.center ↥L) N) :
    ∃ Ps : Set (Subgroup W), (∀ P ∈ Ps, IsMinOverBorel L S₀ P) ∧
      L = ⨆ P ∈ Ps, pElementSubgroup 2 P ∧
      ∀ P ∈ Ps, ∀ p : ℕ, p.Prime → p ∣ N → ∃ x ∈ pElementSubgroup 2 P, orderOf x = p := by
  obtain ⟨K, _, _, D, n, H, π, M, hπ, h3, hnodes⟩ := h
  obtain ⟨P, hmin, hgen, hQ⟩ := exists_pElement_of_nodes hL hS hπ h3 hN hnodes
  exact psSet_of_nodes hmin hgen hQ

end Engine

theorem two_dvd_and_pos_indexQ {d : TauCeti.LieTypeIndex} (h : IsRankTwoPlus d) :
    2 ∣ KFactsPair.indexQ d ∧ 0 < KFactsPair.indexQ d := by
  have key : ∀ q : TauCeti.PrimePower, q.p = 2 → 2 ∣ q.card ∧ 0 < q.card := fun q hq => by
    rw [TauCeti.PrimePower.card_def, hq]
    exact ⟨dvd_pow_self 2 q.exponent_pos.ne', pow_pos two_pos _⟩
  cases d with
  | A l q => exact key q h.1
  | twistedA l q => exact key q h.1
  | B l q => exact key q h.1
  | D l q => exact key q h.1
  | twistedD l q => exact key q h.1
  | G2 q => exact key q h
  | _ => exact h.elim

theorem not_two_dvd_indexQ_sq_sub_one {d : TauCeti.LieTypeIndex} (h : IsRankTwoPlus d) :
    ¬ 2 ∣ KFactsPair.indexQ d ^ 2 - 1 := by
  obtain ⟨⟨k, hk⟩, hQ⟩ := two_dvd_and_pos_indexQ h
  have hk0 : 0 < k := by omega
  have h4 : KFactsPair.indexQ d ^ 2 = 4 * (k * k) := by rw [hk]; ring
  have : 0 < k * k := Nat.mul_pos hk0 hk0
  omega

theorem kFactChevGenQOn_of_models {R : TauCeti.LieTypeIndex → Prop}
    (hM : ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 → R d.1 → ∀ (Y : Type) [Group Y],
      (Y ≃* (TauCeti.CFSGIndex.lie d).Group) → HasQModel Y (KFactsPair.indexQ d.1 ^ 2 - 1)) :
    KFactChevGenQOn R := by
  intro Y _ _ L S₀ hL hS d hd hR ⟨e⟩
  exact chevGenQ_of_hasQModel hL hS (not_two_dvd_indexQ_sq_sub_one hd) (hM d hd hR _ e)

end CFSG.LocalAnalysis.RankThreeUC.S15.K517ChevGenQ
