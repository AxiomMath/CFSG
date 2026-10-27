module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairModels
public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinLevi

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits CFSG.Timmesfeld

section Datum

variable {F : Type} [Field F] [Finite F]

theorem standardPair_minusDatum {n : ℕ} (hn : 4 ≤ n) (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    IsPartner (Twisted.minusDatum n hirr).isFiniteType
      (Pi.single (⟨0, by show 0 < n - 1; omega⟩ : Fin (Twisted.minusDatum n hirr).rank) 1)
      (Pi.single (⟨1, by show 1 < n - 1; omega⟩ : Fin (Twisted.minusDatum n hirr).rank) 1) ∧
    ∃ W, LinearBlockStandardPair F W
      (rankOne (Twisted.minusDatum n hirr).rootGroup ⟨0, by show 0 < n - 1; omega⟩)
      (rankOne (Twisted.minusDatum n hirr).rootGroup ⟨1, by show 1 < n - 1; omega⟩) := by
  have hi : (0 : ℕ) + 1 < n - 1 := by omega
  have hj : (1 : ℕ) + 1 < n - 1 := by omega
  refine ⟨isPartner_single_single _ ?_ ?_, ?_⟩
  · show cartanB (n - 1) ⟨0, by omega⟩ ⟨1, by omega⟩ = -1
    simp [cartanB, Fin.ext_iff]
    omega
  · show cartanB (n - 1) ⟨1, by omega⟩ ⟨0, by omega⟩ = -1
    simp [cartanB, Fin.ext_iff]
    omega
  obtain ⟨emb, hinj, hb1, hb2⟩ := exists_sl3_minus h2 hn b c
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) rfl hi hj
  have hset : ∀ (k : Fin (n - 1)) (hk : k.val + 1 < n - 1),
      ((Twisted.minusDatum n hirr).rootGroup (Pi.single k 1) : Set _) =
        Set.range fun x => rLong n b c hk (tv 0 1 x) := fun k hk =>
    Set.ext fun g => ⟨fun hg => (rLong_param_upper hirr hk g hg).imp fun _ h => h,
      fun ⟨x, hx⟩ => hx ▸ rLong_upper hirr hk x⟩
  have hset' : ∀ (k : Fin (n - 1)) (hk : k.val + 1 < n - 1),
      ((Twisted.minusDatum n hirr).rootGroup (-Pi.single k 1) : Set _) =
        Set.range fun x => rLong n b c hk (tv 1 0 x) := fun k hk =>
    Set.ext fun g => ⟨fun hg => (rLong_param_lower hirr hk g hg).imp fun _ h => h,
      fun ⟨x, hx⟩ => hx ▸ rLong_lower hirr hk x⟩
  refine ⟨_, linearBlockStandardPair_sup (hset ⟨0, by omega⟩ hi) (hset' ⟨0, by omega⟩ hi)
    (hset ⟨1, by omega⟩ hj) (hset' ⟨1, by omega⟩ hj) emb ?_ ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
    exact bot_le
  · intro x
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← blk_zero_tv01 (F := F) x, ← MonoidHom.comp_apply, hb1]
    · rw [← blk_zero_tv10 (F := F) x, ← MonoidHom.comp_apply, hb1]
    · rw [← blk_one_tv01 (F := F) x, ← MonoidHom.comp_apply, hb2]
    · rw [← blk_one_tv10 (F := F) x, ← MonoidHom.comp_apply, hb2]

end Datum

theorem exists_standardPair_partner_POmegaMinus (n p f : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaMinus n p f)
    {γ : Fin (modelUniv .POmegaMinus n p f hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .POmegaMinus n p f hp.out).D γ) :
    ∃ δ : Fin (modelUniv .POmegaMinus n p f hp.out).D.rank → ℤ,
      IsLongestRoot (modelUniv .POmegaMinus n p f hp.out).D δ ∧
      IsPartner (modelUniv .POmegaMinus n p f hp.out).D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W
        ((modelUniv .POmegaMinus n p f hp.out).D.rootGroup γ ⊔
          (modelUniv .POmegaMinus n p f hp.out).D.rootGroup (-γ))
        ((modelUniv .POmegaMinus n p f hp.out).D.rootGroup δ ⊔
          (modelUniv .POmegaMinus n p f hp.out).D.rootGroup (-δ)) := by
  have hn : 4 ≤ n := hadm.2.2
  obtain ⟨hp01, hpair⟩ := standardPair_minusDatum (F := GaloisField p f) hn
    (two_ne_zero_galoisField f hp2) (minusCoeffs_irr p f)
  exact exists_standardPair_partner_of_nodes
    (hasBruhatDatum .POmegaMinus n p f hp.out trivial hadm)
    (cartanOK .POmegaMinus n p f hp.out trivial hadm)
    (isLongestRoot_single .POmegaMinus n p f hp.out trivial hadm ⟨0, by show 0 < n - 1; omega⟩
      (by show 0 + 2 < n; omega))
    (isLongestRoot_single .POmegaMinus n p f hp.out trivial hadm ⟨1, by show 1 < n - 1; omega⟩
      (by show 1 + 2 < n; omega)) hp01 hpair hγ

end CFSG.ClassicalInvolution.ModelFacts
