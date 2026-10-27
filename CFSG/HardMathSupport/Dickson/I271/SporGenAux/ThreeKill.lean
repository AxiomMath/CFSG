module

public import CFSG.HardMathSupport.Dickson.I271.SporGen
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGen

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.RankThree.PartTwo.Sec4.Item434SporGen
  CFSG.RankThree.PartTwo.Sec4 CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.StrongP

section Rank

variable {p : ℕ} {S : Type*} [Group S] [Finite S]

theorem autRankLe2_of_noCube (hp : p.Prime) (h : NoElemAbelianCubeAut p S) : AutRankLe2 p S := by
  intro E hE
  have : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut S) :=
    Finite.of_injective (fun σ : MulAut S => (σ : S → S)) DFunLike.coe_injective
  obtain ⟨j, hj⟩ := i271_exists_card_eq hp hE
  by_contra hlt
  push Not at hlt
  have hj3 : 3 ≤ j := by
    by_contra hj'
    push Not at hj'
    have : j ≤ 2 := by omega
    exact absurd (hj ▸ Nat.pow_le_pow_right hp.pos this) (not_le.2 hlt)
  have hdvd : p ^ 3 ∣ Nat.card E := by rw [hj]; exact pow_dvd_pow p hj3
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  have hD : IsElemAbelian p (K'.map E.subtype) :=
    CFSG.Open.IsElemAbelian.mono hE (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  exact h _ hD (by rw [Subgroup.card_map_of_injective E.subtype_injective, hK'])

theorem autRankLe2_of_offPair {name : TauCeti.SporadicName} (hp : p.Prime) (hp2 : p ≠ 2)
    (hnot : ¬ SporadicOnePair name p) {C : Type} [Group C] (hOff : OffPair name C) (f : S ≃* C)
    (hcen : Subgroup.center S = ⊥) (hout : Nat.card (Outer S) ≤ 2) : AutRankLe2 p S := by
  refine autRankLe2_of_noCube hp ?_
  rcases hOff p hp hp2 hnot with h3 | ⟨h4, hpair⟩
  · exact noElemAbelianCubeAut_of_not_dvd hp hp2 hcen hout (by rwa [Nat.card_congr f.toEquiv])
  · have hpair' : HasNoncommPair p S :=
      HasNoncommPair.map f.symm.toMonoidHom f.symm.injective hpair
    exact noElemAbelianCubeAut_of_noncomm hp hp2 hcen hout (by rwa [Nat.card_congr f.toEquiv])
      hpair'

end Rank

section Plane

variable {S : Type*} [Group S]

theorem planeKill_three_of_kill9 {X : Type*} [Group X] (f : S ≃* X)
    (hcen : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (hK : ∀ P : Subgroup X, IsElemAbelian 3 P → Nat.card P = 9 → FixGen P ∨ NoSignalizer P) :
    PlaneKill 3 S := by
  intro E hE hE9
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hcen
  have hEinn : ∀ φ ∈ E, φ ∈ (MulAut.conj : S →* MulAut S).range := fun φ hφ =>
    Item434Kit.mem_range_conj_of_pow_three hout (hE.2 φ hφ)
  set PS : Subgroup S := E.comap (MulAut.conj : S →* MulAut S) with hPS
  have hPSE : PS.map (MulAut.conj : S →* MulAut S) = E := by
    rw [hPS, Subgroup.map_comap_eq]
    exact inf_eq_right.2 fun φ hφ => hEinn φ hφ
  have hPSel : IsElemAbelian 3 PS :=
    Item434Kit.isElemAbelian_of_map_injective hinj (hPSE ▸ hE)
  have hPScard : Nat.card PS = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hPSE]
    exact hE9
  set PX : Subgroup X := PS.map f.toMonoidHom with hPX
  have hPXel : IsElemAbelian 3 PX := CFSG.Open.IsElemAbelian.map hPSel _
  have hPXcard : Nat.card PX = 9 := by
    rw [hPX, Subgroup.card_map_of_injective f.injective]
    exact hPScard
  rcases hK PX hPXel hPXcard with hF | hN
  · left
    obtain ⟨T, hT, hTo⟩ := hF
    refine ⟨f.symm '' T, ?_, ?_⟩
    · rw [eq_top_iff]
      intro s _
      have h1 : f s ∈ Subgroup.closure T := hT (Subgroup.mem_top _)
      have h2 : s ∈ (Subgroup.closure T).map f.symm.toMonoidHom :=
        ⟨f s, h1, by simp⟩
      rwa [MonoidHom.map_closure] at h2
    · rintro _ ⟨σ, hσ, rfl⟩
      obtain ⟨hco, q, hq, hq1, hqσ⟩ := hTo σ hσ
      refine ⟨by rw [MulEquiv.orderOf_eq]; exact hco, ?_⟩
      obtain ⟨qs, hqs, rfl⟩ := hq
      refine ⟨MulAut.conj qs, ?_, ?_, ?_⟩
      · rw [← hPSE]
        exact Subgroup.mem_map_of_mem _ hqs
      · intro h1
        apply hq1
        have : qs = 1 := hinj (by rw [h1, map_one])
        simp [this]
      · have h3 : qs * f.symm σ = f.symm σ * qs := by
          apply f.injective
          simpa using hqσ
        simp only [MulAut.conj_apply]
        calc qs * f.symm σ * qs⁻¹ = (f.symm σ * qs) * qs⁻¹ := by rw [h3]
          _ = f.symm σ := by group
  · right
    intro T hTcop hET
    set g : MulAut S ≃* MulAut X := MulAut.congr f with hg
    set Y : Subgroup (MulAut X) := T.map g.toMonoidHom with hY
    have hY3 : ¬ 3 ∣ Nat.card Y := by
      rw [hY, Subgroup.card_map_of_injective g.injective]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hTcop
    have hPY : PX.map (MulAut.conj : X →* MulAut X) ≤ Subgroup.normalizer (Y : Set (MulAut X)) := by
      rintro _ ⟨x, ⟨qs, hqs, rfl⟩, rfl⟩
      have hc : (MulAut.conj (f.toMonoidHom qs) : MulAut X) = g (MulAut.conj qs) := by
        ext y
        simp [hg, MulAut.conj_apply, MulAut.congr_apply]
      have hqE : (MulAut.conj qs : MulAut S) ∈ E := by
        rw [← hPSE]
        exact Subgroup.mem_map_of_mem _ hqs
      rw [show (MulAut.conj : X →* MulAut X) (f.toMonoidHom qs) = g (MulAut.conj qs) from hc]
      exact Subgroup.le_normalizer_map g.toMonoidHom (Subgroup.mem_map_of_mem _ (hET hqE))
    have hY1 := hN Y hY3 hPY
    rw [hY, Subgroup.map_eq_bot_iff_of_injective _ g.injective] at hY1
    exact hY1

end Plane

theorem sporPlaneKill_three (hOut : SporadicOuterLeTwo) {s : TauCeti.SporadicName}
    (hnot : ¬ SporadicOnePair s 3) {X : Type} [Group X] (bX : X ≃* Spor s)
    (hK : ∀ P : Subgroup X, IsElemAbelian 3 P → Nat.card P = 9 → FixGen P ∨ NoSignalizer P)
    {C : Type} [Group C] (bC : C ≃* Spor s) (hOff : OffPair s C) : SporPlaneKill s 3 := by
  intro S _ _ hsimple hnab ⟨e⟩
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer S) ≤ 2 := hOut S hsimple hnab s ⟨e⟩
  have hout3 : ¬ 3 ∣ Nat.card (Outer S) := by
    intro hd
    have hpos : 0 < Nat.card (Outer S) := Nat.card_pos
    have := Nat.le_of_dvd hpos hd
    omega
  exact ⟨autRankLe2_of_offPair Nat.prime_three (by norm_num) hnot hOff (e.trans bC.symm) hcen hout,
    planeKill_three_of_kill9 (e.trans bX.symm) hcen hout3 hK⟩


theorem planeKill_of_noSig_model {p : ℕ} {S X : Type*} [Group S] [Group X] (f : S ≃* X)
    (hK : ∀ R Y : Subgroup (MulAut X), IsElemAbelian p R → Nat.card R = p ^ 2 →
      ¬ p ∣ Nat.card Y → R ≤ Subgroup.normalizer (Y : Set (MulAut X)) → Y = ⊥)
    (hp : p.Prime) : PlaneKill p S := by
  intro E hE hE9
  right
  intro T hTcop hET
  set g : MulAut S ≃* MulAut X := MulAut.congr f with hg
  have hR : IsElemAbelian p (E.map g.toMonoidHom) := CFSG.Open.IsElemAbelian.map hE _
  have hRcard : Nat.card (E.map g.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective g.injective]
    exact hE9
  have hY3 : ¬ p ∣ Nat.card (T.map g.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective g.injective]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hTcop
  have hRY : E.map g.toMonoidHom ≤ Subgroup.normalizer ((T.map g.toMonoidHom : Subgroup _) : Set _) := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.le_normalizer_map g.toMonoidHom (Subgroup.mem_map_of_mem _ (hET he))
  have := hK _ _ hR hRcard hY3 hRY
  rwa [Subgroup.map_eq_bot_iff_of_injective _ g.injective] at this

theorem sporPlaneKill_of_noSig_model (hOut : SporadicOuterLeTwo) {s : TauCeti.SporadicName}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hnot : ¬ SporadicOnePair s p)
    {X : Type} [Group X] (bX : X ≃* Spor s)
    (hK : ∀ R Y : Subgroup (MulAut X), IsElemAbelian p R → Nat.card R = p ^ 2 →
      ¬ p ∣ Nat.card Y → R ≤ Subgroup.normalizer (Y : Set (MulAut X)) → Y = ⊥)
    {C : Type} [Group C] (bC : C ≃* Spor s) (hOff : OffPair s C) : SporPlaneKill s p := by
  intro S _ _ hsimple hnab ⟨e⟩
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer S) ≤ 2 := hOut S hsimple hnab s ⟨e⟩
  exact ⟨autRankLe2_of_offPair hp hp2 hnot hOff (e.trans bC.symm) hcen hout,
    planeKill_of_noSig_model (e.trans bX.symm) hK hp⟩

end CFSG.HardMathSupport.Dickson.I271
