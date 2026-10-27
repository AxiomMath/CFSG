module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Defs
import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4OrthInner
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnOrth
import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFIso
import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedOrthogonal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner exists_pow_eq_one_of_mem_inner)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed (mem_inner_of_mem_innAutDerived_omegaPlus
  mem_inner_of_mem_innAutDerived_omegaMinus)

private theorem exists_conj_of_inner {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) {n : ℕ}
    (hG : StatedClassicalModel S t n 2 1) {α β : MulAut S} (hα : α ∈ inner S) (hα3 : α ^ 3 = 1)
    (hα1 : α ≠ 1) (hβ : β ∈ inner S) (hβ3 : β ^ 3 = 1) (hαβ : Commute α β) {J : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup α) J) (hT : catalogIs (PSimple 3 J) S9.isD4two) :
    ∃ j ∈ J, ∀ y ∈ J, β y = j * y * j⁻¹ := by
  have hZ : Subgroup.center S = ⊥ := by
    haveI := hs
    obtain ⟨a, b, hab⟩ := hnab
    exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative fun h =>
      hab (h.is_comm.comm a b)
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr fun h => by
      have h1 := DFunLike.congr_fun hg h
      rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [hZ] at hgZ
    exact hgZ
  obtain ⟨a, ha3, rfl⟩ := exists_pow_eq_one_of_mem_inner hZ hα hα3
  obtain ⟨b, hb3, rfl⟩ := exists_pow_eq_one_of_mem_inner hZ hβ hβ3
  have ha1 : a ≠ 1 := fun h => hα1 (by rw [h, map_one])
  have hab : a * b = b * a := hinj (by rw [map_mul, map_mul]; exact hαβ.eq)
  obtain ⟨j, hj, h⟩ := exists_conj_of_inner_omega_two ht hG ha3 ha1 hb3 hab hJ hT
  exact ⟨j, hj, fun y hy => by rw [MulAut.conj_apply]; exact h y hy⟩

theorem triD4NoD_holds : TriD4NoD := by
  rintro S _ _ hs hnab ⟨d, hv⟩ ⟨n, q, rfl⟩ - hf ⟨e⟩ α β hα hα3 hα1 hβ hβ3 hαβ J hJ hT _
  have hq : q.card = 2 := hf
  obtain ⟨hq2, hq1⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (pow_one 2).symm)
  obtain ⟨hadm, hG | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_D n q hv e
  · rw [hq2, hq1] at hG
    have h4 : 4 ≤ n := hadm.2.2
    rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
    ·
      exfalso
      have hS : Nat.card S = ordD 4 2 := by
        rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hG).2.2.2.1 rfl, pow_one]
      have hP : Nat.card (PSimple 3 J) = ordD 4 2 := by
        rw [(CFSG.Timmesfeld.card_statedClassicalModel_two (D4XF.statedModel_of_d4two hT)).2.2.2.1
          rfl, pow_one]
      have h1 : Nat.card (PSimple 3 J) ≤ Nat.card J :=
        Nat.card_le_card_of_surjective _ (chevQuotHom_surjective 3 J)
      have h2 : Nat.card J ≤ Nat.card (fixSubgroup α) := Subgroup.card_le_of_le hJ.1
      have htop : fixSubgroup α = ⊤ := Subgroup.eq_top_of_le_card (H := fixSubgroup α) (by omega)
      refine hα1 (MulEquiv.ext fun y => ?_)
      have hy : y ∈ fixSubgroup α := by
        rw [htop]
        exact Subgroup.mem_top y
      exact mem_fixSubgroup.mp hy
    · exact exists_conj_of_inner (Or.inl rfl) hs hnab hG
        (mem_inner_of_mem_innAutDerived_omegaPlus hG h5 Nat.prime_three (by norm_num) hα hα3)
        hα3 hα1
        (mem_inner_of_mem_innAutDerived_omegaPlus hG h5 Nat.prime_three (by norm_num) hβ hβ3)
        hβ3 hαβ hJ hT
  · have h4 : 4 ≤ n := hadm.2.2
    omega

theorem triD4NoTwistedD_holds : TriD4NoTwistedD := by
  rintro S _ _ hs hnab ⟨d, hv⟩ ⟨n, q, rfl⟩ - hf ⟨e⟩ α β hα hα3 hα1 hβ hβ3 hαβ J hJ hT _
  have hq : q.card = 2 := hf
  obtain ⟨hq2, hq1⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (pow_one 2).symm)
  obtain ⟨hadm, hG | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_twistedD n q hv e
  · rw [hq2, hq1] at hG
    exact exists_conj_of_inner (Or.inr rfl) hs hnab hG
      (mem_inner_of_mem_innAutDerived_omegaMinus hG Nat.prime_three (by norm_num) hα hα3)
      hα3 hα1
      (mem_inner_of_mem_innAutDerived_omegaMinus hG Nat.prime_three (by norm_num) hβ hβ3)
      hβ3 hαβ hJ hT
  · have h4 : 4 ≤ n := hadm.2.2
    omega

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end
