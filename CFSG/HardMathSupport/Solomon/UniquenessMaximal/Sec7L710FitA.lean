module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

private theorem centralizer_normal_of_normal {Q : Type} [Group Q] (N : Subgroup Q) [N.Normal] :
    (Subgroup.centralizer (N : Set Q)).Normal := by
  refine ⟨fun c hc g n hn => ?_⟩
  have hn' : g⁻¹ * n * g ∈ N := by
    simpa [mul_assoc] using (inferInstance : N.Normal).conj_mem n hn g⁻¹
  have := Subgroup.mem_centralizer_iff.1 hc _ hn'
  calc n * (g * c * g⁻¹) = g * ((g⁻¹ * n * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * n * g)) * g⁻¹ := by rw [this]
    _ = g * c * g⁻¹ * n := by group

private theorem normal_le_of_isPGroup {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    {R B : Subgroup Q} [R.Normal] (hR : IsPGroup p R) (hB : IsPGroup p B) (hBi : ¬ p ∣ B.index) :
    R ≤ B :=
  hR.le_sylow_of_normal (hB.toSylow hBi)

theorem commutes_of_centralizes_normal {Q : Type} [Group Q] [Finite Q] (N T B : Subgroup Q)
    [N.Normal]
    (hNc : ∀ x ∈ N, (∀ n ∈ N, x * n = n * x) → x = 1)
    (hQ : ∀ q : Q, q ∈ N ⊔ T ⊔ B)
    (hT : IsPGroup 2 T) (hB : IsPGroup 3 B) (hBi : ¬ 3 ∣ B.index)
    (hBT : B ≤ Subgroup.normalizer (T : Set Q))
    (hcore : GLAPPrimeCore 3 Q = ⊥) {b : Q} (hb : b ∈ B) (hbN : ∀ n ∈ N, b * n = n * b) :
    ∀ t ∈ T, b * t * b⁻¹ * t⁻¹ = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup Q := Subgroup.centralizer (N : Set Q) with hC
  have hCn : C.Normal := centralizer_normal_of_normal N
  have hTs : Group.IsSolvable ↥T := by have := hT.isNilpotent; infer_instance
  have hBs : Group.IsSolvable ↥B := by have := hB.isNilpotent; infer_instance
  have hTBs : Group.IsSolvable ↥(T ⊔ B) := isSolvable_sup T B hBT
  have hQNs : Group.IsSolvable (Q ⧸ N) := by
    refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' N).comp (T ⊔ B).subtype) ?_
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have hq : q ∈ N ⊔ (T ⊔ B) := by rw [← sup_assoc]; exact hQ q
    obtain ⟨n, hn, y, hy, hny⟩ := Subgroup.mem_sup_of_normal_left.1 hq
    refine ⟨⟨y, hy⟩, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, Subgroup.coe_subtype]
    rw [← hny, QuotientGroup.eq]
    simpa [mul_assoc] using (inferInstance : N.Normal).conj_mem n hn y⁻¹
  have hCs : Group.IsSolvable ↥C := by
    refine Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.mk' N).comp C.subtype) ?_
    intro x y hxy
    have hxy' : ((x : Q))⁻¹ * y ∈ N := QuotientGroup.eq.1 hxy
    have hcomm : ∀ n ∈ N, ((x : Q)⁻¹ * y) * n = n * ((x : Q)⁻¹ * y) := by
      intro n hn
      have h1 := Subgroup.mem_centralizer_iff.1 x.2 n hn
      have h2 := Subgroup.mem_centralizer_iff.1 y.2 n hn
      have h1' : (x : Q)⁻¹ * n = n * (x : Q)⁻¹ := by
        calc (x : Q)⁻¹ * n = (x : Q)⁻¹ * (n * x) * (x : Q)⁻¹ := by group
          _ = (x : Q)⁻¹ * (x * n) * (x : Q)⁻¹ := by rw [h1]
          _ = n * (x : Q)⁻¹ := by group
      calc ((x : Q)⁻¹ * y) * n = (x : Q)⁻¹ * (y * n) := by group
        _ = (x : Q)⁻¹ * (n * y) := by rw [h2]
        _ = (n * (x : Q)⁻¹) * y := by rw [← mul_assoc, h1']
        _ = n * ((x : Q)⁻¹ * y) := by group
    have := hNc _ hxy' hcomm
    exact Subtype.ext (inv_mul_eq_one.1 this)
  have hCtop : Subgroup.normalizer (C : Set Q) = ⊤ := Subgroup.normalizer_eq_top_iff.2 hCn
  have hC3 : GLAPPrimeCore 3 ↥C = ⊥ := by
    have h1 : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (C : Set Q) := hCtop ▸ le_rfl
    have h2 := le_normalizer_glaPPrimeCoreOf_of_le' (p := 3) h1
    have hEn : (GLAPPrimeCoreOf 3 C).Normal :=
      Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 h2)
    have hEc : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 C)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
        (not_dvd_card_glaPPrimeCoreOf Nat.prime_three C)
    have hE : GLAPPrimeCoreOf 3 C ≤ GLAPPrimeCore 3 Q := le_sSup ⟨hEn, hEc⟩
    rw [hcore, le_bot_iff] at hE
    exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 hE
  have hF : CFSG.fittingSubgroup ↥C = CFSG.pCore 3 ↥C := CFSG.Fitting_eq_pcore ↥C 3 hC3
  have hcent := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hCs
  set R : Subgroup Q := pCoreOf 3 C with hR
  have hRn' : Subgroup.normalizer (R : Set Q) = ⊤ :=
    top_le_iff.1 (hCtop ▸ CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 3 C)
  have hRn : R.Normal := Subgroup.normalizer_eq_top_iff.1 hRn'
  have hR3 : IsPGroup 3 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 C
  have hRB : R ≤ B := normal_le_of_isPGroup hR3 hB hBi
  have hdisj : Disjoint R T := IsPGroup.disjoint_of_ne 3 2 (by norm_num) R T hR3 hT
  have key : ∀ q ∈ T, q ∈ C → q = 1 := by
    intro q hqT hqC
    have hx : (⟨q, hqC⟩ : ↥C) ∈ Subgroup.centralizer (CFSG.fittingSubgroup ↥C : Set ↥C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hfR : (f : Q) ∈ R := by
        rw [hF] at hf
        exact ⟨f, hf, rfl⟩
      have hrB : (f : Q) ∈ B := hRB hfR
      have hc1 : (f : Q) * q * (f : Q)⁻¹ * q⁻¹ ∈ T :=
        T.mul_mem (by
          have := Subgroup.mem_normalizer_iff.1 (hBT hrB) q
          exact this.1 hqT) (T.inv_mem hqT)
      have hc2 : (f : Q) * q * (f : Q)⁻¹ * q⁻¹ ∈ R := by
        have := hRn.conj_mem _ (R.inv_mem hfR) q
        have h3 := R.mul_mem hfR this
        simpa [mul_assoc] using h3
      have h1 := Subgroup.disjoint_def.1 hdisj hc2 hc1
      apply Subtype.ext
      show (f : Q) * q = q * (f : Q)
      calc (f : Q) * q = ((f : Q) * q * (f : Q)⁻¹ * q⁻¹) * (q * (f : Q)) := by group
        _ = q * (f : Q) := by rw [h1, one_mul]
    have hxF := hcent hx
    have hqR : q ∈ R := by
      rw [hF] at hxF
      exact ⟨_, hxF, rfl⟩
    exact Subgroup.disjoint_def.1 hdisj hqR hqT
  intro t ht
  have hbC : b ∈ C := Subgroup.mem_centralizer_iff.2 fun n hn => (hbN n hn).symm
  have hc1 : b * t * b⁻¹ * t⁻¹ ∈ T :=
    T.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBT hb) t).1 ht) (T.inv_mem ht)
  have hc2 : b * t * b⁻¹ * t⁻¹ ∈ C := by
    have := hCn.conj_mem _ (C.inv_mem hbC) t
    simpa [mul_assoc] using C.mul_mem hbC this
  exact key _ hc1 hc2

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
