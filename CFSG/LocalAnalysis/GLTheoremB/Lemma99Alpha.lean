module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Lift

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem exists_glaPComponent_lift (hp : p.Prime) {M L : Subgroup G} {d : G} (hdM : d ∈ M)
    (hLM : L ≤ M) (hdL : d ∈ Subgroup.normalizer (L : Set G))
    (hd : IsPGroup p (Subgroup.zpowers d)) {K' : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)}
    (hK' : GLAPComponent p (barX p M L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M))) K') :
    ∃ K : Subgroup G, GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) K ∧
      barX p M K = K' := by
  have : Fact p.Prime := ⟨hp⟩
  set A : Subgroup G := L ⊓ Subgroup.centralizer ({d} : Set G) with hA
  have hAM : A ≤ M := inf_le_left.trans hLM
  set ψ : ↥M →* ↥M ⧸ GLAPPrimeCore p ↥M := QuotientGroup.mk' (GLAPPrimeCore p ↥M) with hψ
  set A₀ : Subgroup ↥M := A.subgroupOf M with hA₀
  have hker : Nat.Coprime p (Nat.card ↥(A₀ ⊓ ψ.ker)) := by
    rw [hψ, QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card
  have hmap : A₀.map ψ = barX p M L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
    barX_inf_centralizer hp hdM hLM hdL hd
  have hK'' : GLAPComponent p (A₀.map ψ) K' := by
    rw [hmap]
    exact hK'
  obtain ⟨K₀, hK₀, hK₀map⟩ := exists_glaPComponent_map_eq hp ψ hker hK''
  have hker2 : Nat.Coprime p (Nat.card ↥(A₀ ⊓ M.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hK1 := glaPComponent_map hp M.subtype hker2 hK₀
  rw [hA₀, Subgroup.map_subgroupOf_eq_of_le hAM] at hK1
  refine ⟨K₀.map M.subtype, hK1, ?_⟩
  have hsub : (K₀.map M.subtype).subgroupOf M = K₀ :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K₀
  show ((K₀.map M.subtype).subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) = K'
  rw [hsub]
  exact hK₀map

@[expose] def Lemma99Data (p : ℕ) (B M D L : Subgroup G) : Prop :=
  ∃ (D₀ : Set G) (K : G → Subgroup G),
    (∀ d ∈ D₀, d ∈ D ∧ d ≠ 1) ∧
    (∀ d ∈ D₀, GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) (K d) ∧
      IsPiGroup p ↥(barX p M (K d)) ∧ B ≤ Subgroup.normalizer (K d : Set G) ∧
      barX p M (gammaD D) ≤ Subgroup.normalizer ((barX p M (K d) :
        Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) ∧
      ¬ barX p M (gammaD D) ≤ Subgroup.centralizer ((barX p M (K d) :
        Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))) ∧
    barX p M L = ⨆ d ∈ D₀, barX p M (K d)

end Lift

section Acts

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem card_barX_of_isPGroup {p : ℕ} (hp : p.Prime) {C E : Subgroup G} (hE : IsPGroup p E)
    (hEC : E ≤ C) : Nat.card (barX p C E) = Nat.card E := by
  set f := (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (E.subgroupOf C).subtype with hf
  have hfi := injective_barX_comp hp hE hEC
  have hrange : f.range = barX p C E := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv]

theorem lemma99Data_of_acts (i279 : Input27_9_3) (hSt : GLStanding G m p) {B M : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M) {D : Subgroup G} (hDB : D ≤ B)
    (hD : IsPPlane p D) {L : Subgroup G} (hL : GLAPComponent p M L) (hΓM : gammaD D ≤ M)
    (hΓN : barX p M (gammaD D) ≤ Subgroup.normalizer ((barX p M L :
      Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hact : ActsAsTransposition p (barX p M (gammaD D)) (barX p M L) ∨
      ActsAsTransvection p (barX p M (gammaD D)) (barX p M L)) :
    Lemma99Data p B M D L := by
  have hp := hSt.prime
  have hp2 := hSt.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hSt hB hM
  have hDM : D ≤ M := hDB.trans hBM
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian' hB.1.1
  set Γ := gammaD D with hΓ
  have hΓ2 : IsPGroup 2 Γ := isPGroup_gammaD D
  have hBD : B ≤ Subgroup.normalizer (D : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer (D : Set G) (Subgroup.mem_centralizer_iff.2 fun y hy =>
      elemAbelian_comm hB.1.1 (hDB hy) hb)
  have hBΓ : B ≤ Subgroup.normalizer (Γ : Set G) := fun b hb =>
    normalizer_le_normalizer_gammaD D (hBD hb)
  have hBel : IsElemAbelian p (barX p M B) := isElemAbelian_barX hB.1.1
  have hBK : barX p M B ≤ Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)) := barX_le_normalizer hBL
  have hT2 : IsPGroup 2 (barX p M Γ) :=
    IsPGroup.map (hΓ2.of_equiv (Subgroup.subgroupOfEquivOfLe hΓM).symm)
      (QuotientGroup.mk' (GLAPPrimeCore p ↥M))
  have hBT : barX p M B ≤ Subgroup.normalizer ((barX p M Γ : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)) := barX_le_normalizer hBΓ
  have hDB' : barX p M D ≤ barX p M B := barX_mono p hDB
  have hD' : IsPPlane p (barX p M D) := by
    refine ⟨isElemAbelian_barX hD.1, ?_⟩
    rw [card_barX_of_isPGroup hp (isPGroup_of_isElemAbelian' hD.1) hDM]
    exact hD.2
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥M) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hrank : GLATwoLocalRank p (↥M ⧸ GLAPPrimeCore p ↥M) ≤ CFSG.Open.pRank p (barX p M B) := by
    refine (glaTwoLocalRank_quotient_le hp hp2 _ hN).trans
      ((glaTwoLocalRank_subgroup_le hp.one_lt M).trans ?_)
    rw [hSt.rank_eq, rank_barX_of_isPGroup hp hBp hBM]
    exact hSt.le_pRank' hB
  have hact' : (ActsAsTransposition p (barX p M Γ) (barX p M L) ∧
      GLATwoLocalRank p (↥M ⧸ GLAPPrimeCore p ↥M) ≤ CFSG.Open.pRank p (barX p M B)) ∨
      ActsAsTransvection p (barX p M Γ) (barX p M L) :=
    hact.imp (fun h => ⟨h, hrank⟩) id
  obtain ⟨𝒟, Kf, h𝒟, hKf, hgen⟩ := i279 (↥M ⧸ GLAPPrimeCore p ↥M) p hp hp2 (barX p M L) hL.2.2.1
    (barX p M B) hBel hBK (barX p M Γ) hT2 hΓN hBT hact' (barX p M D) hDB' hD'
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥M) with hπ
  set D₀ : Set G := {d | ∃ hd : d ∈ D, d ≠ 1 ∧ π ⟨d, hDM hd⟩ ∈ 𝒟} with hD₀
  have hex : ∀ d : G, ∃ K : Subgroup G, d ∈ D₀ → GLAPComponent p
      (L ⊓ Subgroup.centralizer ({d} : Set G)) K ∧
      ∀ hdM : d ∈ M, barX p M K = Kf (π ⟨d, hdM⟩) := by
    intro d
    by_cases hd : d ∈ D₀
    · obtain ⟨hdD, hd1, hd𝒟⟩ := hd
      have hdM : d ∈ M := hDM hdD
      have hdB : d ∈ B := hDB hdD
      have hdz : IsPGroup p (Subgroup.zpowers d) := hBp.to_le ((Subgroup.zpowers_le).2 hdB)
      have hdL : d ∈ Subgroup.normalizer (L : Set G) := hBL hdB
      obtain ⟨K, hK, hKbar⟩ := exists_glaPComponent_lift hp hdM hL.1 hdL hdz (hKf _ hd𝒟).1
      exact ⟨K, fun _ => ⟨hK, fun _ => hKbar⟩⟩
    · exact ⟨⊥, fun h => absurd h hd⟩
  choose K hK using hex
  refine ⟨D₀, K, fun d hd => ⟨hd.1, hd.2.1⟩, fun d hd => ?_, ?_⟩
  · obtain ⟨hdD, hd1, hd𝒟⟩ := hd
    have hdM : d ∈ M := hDM hdD
    have hdB : d ∈ B := hDB hdD
    have hK1 := hK d ⟨hdD, hd1, hd𝒟⟩
    have hbar : barX p M (K d) = Kf (π ⟨d, hdM⟩) := hK1.2 hdM
    obtain ⟨-, hBTK, hKπ, hnc⟩ := hKf _ hd𝒟
    have hAM : L ⊓ Subgroup.centralizer ({d} : Set G) ≤ M := inf_le_left.trans hL.1
    refine ⟨hK1.1, ?_, ?_, ?_, ?_⟩
    · rw [hbar]
      exact hKπ
    · intro b hb
      have hbM : b ∈ M := hBM hb
      have hbA : b ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) :
          Set G) :=
        mem_normalizer_inf (hBL hb) (Subgroup.le_normalizer
          (le_centralizer_of_mem hB.1.1 hdB hb))
      refine mem_normalizer_iff_gLBConj_eq.2 (gLBConj_eq_of_barX_eq hp hAM hK1.1 hbM hbA ?_)
      rw [hbar]
      exact mem_normalizer_iff_gLBConj_eq.1
        (hBTK (le_sup_left (a := barX p M B) ⟨⟨b, hbM⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩))
    · rw [hbar]
      exact le_sup_right.trans hBTK
    · rw [hbar]
      exact hnc
  ·
    refine le_antisymm ?_ (iSup₂_le fun d hd => ?_)
    · rw [hgen]
      refine iSup₂_le fun d' hd' => ?_
      obtain ⟨y, hy, rfl⟩ := (h𝒟 d' hd').1
      have hyD : (y : G) ∈ D := (Subgroup.mem_subgroupOf).1 hy
      have hy1 : (y : G) ≠ 1 := fun h => (h𝒟 _ hd').2 (by
        have : y = 1 := Subtype.ext h
        simp [this])
      have hmem : (y : G) ∈ D₀ := ⟨hyD, hy1, hd'⟩
      have hbar : barX p M (K (y : G)) = Kf (π y) := (hK _ hmem).2 y.2
      exact le_iSup₂_of_le (y : G) hmem hbar.ge
    · obtain ⟨hdD, hd1, hd𝒟⟩ := hd
      have hdM : d ∈ M := hDM hdD
      have hbar : barX p M (K d) = Kf (π ⟨d, hdM⟩) := (hK d ⟨hdD, hd1, hd𝒟⟩).2 hdM
      rw [hbar]
      exact ((hKf _ hd𝒟).1.1).trans inf_le_left

end Acts

end CFSG.LocalAnalysis.GLTheoremB
