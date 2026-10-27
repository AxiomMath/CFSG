module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieThreeFam
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieThreeModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Dickson.Sec6.I923 (center_eq_bot_of_simple)

theorem lieS3_fix_conj {G : Type} [Group G] (x : G) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set G) := by
  ext g
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem lieS3_congr_conj {G H : Type} [Group G] [Group H] (e : G ≃* H) (x : G) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.conj_apply]

theorem lieS3_false_of_inner
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 3) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) {a : S} (ha3 : MulAut.conj a ^ 3 = 1)
    (ha1 : MulAut.conj a ≠ 1) (hc : CompOfType S (MulAut.conj a) isL2three6) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv S e.toEquiv
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple hnab
  have hA3 : a ^ 3 = 1 := by
    have hcen : a ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := DFunLike.congr_fun ((map_pow (MulAut.conj : S →* MulAut S) a 3).trans ha3) g
      rw [MulAut.conj_apply, MulAut.one_apply] at hg
      exact (mul_inv_eq_iff_eq_mul.1 hg).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hcen
  have hA1 : a ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have hu : orderOf (e a) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hA3 hA1
  have hKD := CFSG.LocalAnalysis.GLTheoremA.kdCharP_of_lieQConstrainedInner Nat.prime_three
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrainedInner_three_holds
  have hlay : TypeLayer isL2three6 (MulAut.congr e (MulAut.conj a)) False := by
    rw [lieS3_congr_conj]
    intro A hA _
    rw [lieS3_fix_conj] at hA
    have hle : A ≤ GLAPLayer 3
        (Subgroup.centralizer ({e a} : Set (TauCeti.CFSGIndex.lie d).Group)) := le_sSup hA
    rw [hKD d hd (e a) hu, le_bot_iff] at hle
    exact Lemma510Ns.glaPComponent_ne_bot hA hle
  obtain ⟨J, hJ, hT⟩ := hc
  exact typeLayer_congr e hlay J hJ hT

theorem lieS3_holds :
    LieS3 := by
  intro S _ _ hs hnab d hc ⟨e⟩ α hα3 hα1 hcomp
  haveI := hs
  have hne : d.1.characteristic ≠ 2 := by omega
  obtain ⟨t, n, f, hm, ht, hA⟩ := lieS3_exists_model d hne e
  rw [hc] at hm
  by_cases hPSL : t = .PSL ∧ n = 2
  · obtain ⟨q, hv, rfl⟩ := hA hPSL.1 hPSL.2
    have hm' : CFSG.Models.LieModel S .PSL 2 q.p q.exponent := CFSG.Models.lieModel_A 1 q hv e
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hm'.2.resolve_right (fun h => absurd h.1 (by norm_num))
    have hK18 := lieS3_A1 eK hα3 hα1 hcomp
    show q.card = 3 ^ 18
    rw [TauCeti.PrimePower.card_def, ← hK]
    exact hK18
  · by_cases hinn : ∃ a : S, MulAut.conj a = α
    · obtain ⟨a, rfl⟩ := hinn
      exact (lieS3_false_of_inner d hc hnab e hα3 hα1 hcomp).elim
    · push Not at hinn
      have hNo := lieS3_noL2Layer hm.admissible ht hPSL hm hα3 fun ⟨a, ha⟩ => hinn a ha
      exact (lieS3_false_of_noL2Layer hNo hcomp).elim

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
