module

public import CFSG.LocalAnalysis.RankThreeUC.K518HAModel
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoData

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.Tits.GN516

section SL2Nodes

variable {K Y : Type} [Group K] [Finite K] [Group Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

omit [Finite K] in
theorem sl2_equiv_rankOne_of_range {i : Fin D.rank} {F : Type} [Field F]
    {φ : Matrix.SpecialLinearGroup (Fin 2) F →* K} (hφ : Function.Injective φ)
    (hr : rankOne D.rootGroup i = φ.range) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(rankOne D.rootGroup i)) :=
  ⟨(MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hr.symm)⟩

theorem nodeData_of_sl2 (h : BorelQuotient D n H π M) {i : Fin D.rank} {F : Type} [Field F]
    [Finite F] [CharP F 2]
    (e : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(rankOne D.rootGroup i))
    (hM : M ∣ Nat.card F ^ 2 - 1) :
    RkKind ↥(rankOne D.rootGroup i) ∧ π.ker ⊓ rankOne D.rootGroup i = ⊥ ∧
      M ∣ Nat.card ↥(rankOne D.rootGroup i) ∧ Subgroup.center ↥(rankOne D.rootGroup i) = ⊥ := by
  have hc : Subgroup.center ↥(rankOne D.rootGroup i) = ⊥ := center_eq_bot_of_sl2_equiv e.symm
  refine ⟨Or.inl ⟨F, inferInstance, inferInstance, inferInstance, ⟨e.symm⟩⟩, ?_, ?_, hc⟩
  · refine eq_bot_iff.2 fun z hz => ?_
    have hzc : z ∈ Subgroup.center K := h.ker_central z hz.1
    have hzL : (⟨z, hz.2⟩ : ↥(rankOne D.rootGroup i)) ∈ Subgroup.center ↥(rankOne D.rootGroup i) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_center_iff.1 hzc (g : K)))
    rw [hc, Subgroup.mem_bot] at hzL
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hzL
  · rw [← Nat.card_congr e.toEquiv, card_sl2]
    exact hM.trans (dvd_mul_left _ _)

theorem center_inf_eq_bot_of_center_eq_bot {L : Subgroup K} (hc : Subgroup.center ↥L = ⊥) :
    Subgroup.center K ⊓ L = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  have hzL : (⟨z, hz.2⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 hz.1 (g : K))
  rw [hc, Subgroup.mem_bot] at hzL
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hzL

theorem ker_inf_eq_bot_of_center_inf (h : BorelQuotient D n H π M) {L : Subgroup K}
    (hc : Subgroup.center K ⊓ L = ⊥) : π.ker ⊓ L = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  have : z ∈ Subgroup.center K ⊓ L := ⟨h.ker_central z hz.1, hz.2⟩
  rwa [hc] at this

theorem hasRkModel_of_nodes (h : BorelQuotient D n H π M)
    (hnode : ∀ i, RkKind ↥(rankOne D.rootGroup i) ∧ π.ker ⊓ rankOne D.rootGroup i = ⊥ ∧
      M ∣ Nat.card ↥(rankOne D.rootGroup i))
    (hcent : ∀ i j : Fin D.rank, i ≠ j → Subgroup.center ↥(rankOne D.rootGroup i) = ⊥ ∨
      Subgroup.center ↥(rankOne D.rootGroup j) = ⊥) : HasRkModel Y :=
  ⟨K, inferInstance, inferInstance, D, n, H, π, M, h, fun i => (hnode i).1,
    fun i => (hnode i).2.1, fun i => (hnode i).2.2, hcent⟩

theorem hasRkModel_of_sl2_nodes (h : BorelQuotient D n H π M)
    (hnodes : ∀ i : Fin D.rank, ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(rankOne D.rootGroup i)) ∧
        M ∣ Nat.card F ^ 2 - 1) :
    HasRkModel Y := by
  choose F _ _ _ he hM using hnodes
  have hd := fun i => nodeData_of_sl2 h (he i).some (hM i)
  exact ⟨K, inferInstance, inferInstance, D, n, H, π, M, h, fun i => (hd i).1,
    fun i => (hd i).2.1, fun i => (hd i).2.2.1, fun i j _ => Or.inl (hd i).2.2.2⟩

end SL2Nodes

section Families

open CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Spin

theorem hasRkModel_psl {Y : Type} [Group Y] {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) : HasRkModel Y := by
  refine hasRkModel_of_sl2_nodes (borelQuotient_sl e) fun i => ?_
  obtain ⟨φ, hφ, hx, hy⟩ := SL.rankOne (F := F) i
  exact ⟨F, inferInstance, inferInstance, inferInstance,
    sl2_equiv_rankOne_of_range hφ (rankOne_eq_range_of_sl2 SL.isParametrization hx hy),
    sub_one_dvd_sq_sub_one _⟩

theorem hasRkModel_of_model_psp {Y : Type} [Group Y] {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSp n 2 f) : HasRkModel Y := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  refine hasRkModel_of_sl2_nodes (borelQuotient_sp e) fun i => ?_
  obtain ⟨φ, hφ, hx, hy⟩ := Sp.rankOne (F := F) i
  exact ⟨F, inferInstance, inferInstance, inferInstance,
    sl2_equiv_rankOne_of_range hφ (rankOne_eq_range_of_sl2 Sp.isParametrization hx hy),
    sub_one_dvd_sq_sub_one _⟩

theorem hasRkModel_of_model_pomegaPlus {Y : Type} [Group Y] {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .POmegaPlus n 2 f) : HasRkModel Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  refine hasRkModel_of_sl2_nodes (borelQuotient_spinPlus hn3 e) fun i => ?_
  obtain ⟨φ, hφ, hx, hy⟩ := SpinPlus.rankOne (K := F) hn3 i
  exact ⟨F, inferInstance, inferInstance, inferInstance,
    sl2_equiv_rankOne_of_range hφ
      (rankOne_eq_range_of_sl2 (SpinPlus.isParametrization (K := F) hn3) hx hy),
    sub_one_dvd_sq_sub_one _⟩


section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.AGLEmbedding.LeviBlock


set_option linter.unusedSectionVars false

theorem hasRkModel_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {Y : Type} [Group Y]
    (e : Y ≃* CFSG.Blueprint.AdjointQuotient .G2 K) : HasRkModel Y := by
  refine hasRkModel_of_sl2_nodes (borelQuotient_g2 e) fun i => ?_
  obtain ⟨e'⟩ := nonempty_sl2_mulEquiv_rankOne_g2 (F := K) i
  exact ⟨K, inferInstance, inferInstance, inferInstance, ⟨e'⟩, sub_one_dvd_sq_sub_one _⟩

end G2

end Families

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
