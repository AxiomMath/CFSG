module

public import CFSG.Open.LocalVocabulary
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalAveraging

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open Module
open scoped Matrix

private theorem finrank_sup_add_le {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι] (C : Submodule K V) (W : ι → Submodule K V)
    (S : Finset ι) (hC : ∀ i ∈ S, C ≤ W i) :
    finrank K ↥(C ⊔ ⨆ i ∈ S, W i) + S.card * finrank K C ≤
      ∑ i ∈ S, finrank K (W i) + finrank K C := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.card_empty, zero_mul, add_zero, zero_add]
    exact Submodule.finrank_mono
      (sup_le le_rfl (iSup₂_le fun i hi => absurd hi (Finset.notMem_empty i)))
  | insert j S hj ih =>
    have ih' := ih fun i hi => hC i (Finset.mem_insert_of_mem hi)
    have hCj := hC j (Finset.mem_insert_self j S)
    rw [Finset.iSup_insert, Finset.sum_insert hj, Finset.card_insert_of_notMem hj,
      ← sup_assoc, sup_comm C (W j), sup_assoc]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (W j) (C ⊔ ⨆ i ∈ S, W i)
    have h2 : finrank K C ≤ finrank K ↥(W j ⊓ (C ⊔ ⨆ i ∈ S, W i)) :=
      Submodule.finrank_mono (le_inf hCj le_sup_left)
    rw [add_one_mul]
    omega

variable {n : ℕ}

private noncomputable def rhoBW (A : Subgroup (GL (Fin n) (ZMod 2))) :
    ↥A →* Module.End (ZMod 2) (Fin n → ZMod 2) where
  toFun a := Matrix.mulVecLin ((a : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
  map_one' := LinearMap.ext fun v => by simp
  map_mul' a b := LinearMap.ext fun v => by simp

private def fixBW (A : Subgroup (GL (Fin n) (ZMod 2))) (M : Subgroup ↥A) :
    Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {v | ∀ g ∈ M, rhoBW A g v = v}
  add_mem' {u w} hu hw := by
    intro g hg
    rw [map_add, hu g hg, hw g hg]
  zero_mem' := by
    intro g _
    exact map_zero _
  smul_mem' c {v} hv := by
    intro g hg
    rw [map_smul, hv g hg]

private theorem fixBW_top_le (A : Subgroup (GL (Fin n) (ZMod 2))) (M : Subgroup ↥A) :
    fixBW A ⊤ ≤ fixBW A M := by
  intro v hv g _
  exact hv g (Subgroup.mem_top g)

private theorem iSup_fixBW_eq_top {A : Subgroup (GL (Fin n) (ZMod 2))}
    {S : Finset (Subgroup ↥A)} (hS : S.Nonempty)
    {f : Subgroup ↥A → Module.End (ZMod 2) (Fin n → ZMod 2)}
    {T : Module.End (ZMod 2) (Fin n → ZMod 2)} {c : ZMod 2}
    (hf : ∀ M ∈ S, ∀ v, f M v ∈ fixBW A M) (hT : ∀ v, T v ∈ fixBW A ⊤)
    (hsum : ∑ M ∈ S, f M = 1 + c • T) : ⨆ M ∈ S, fixBW A M = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  have hv : v = ∑ M ∈ S, f M v - c • T v := by
    rw [← LinearMap.sum_apply, hsum]
    simp
  obtain ⟨M₀, hM₀⟩ := hS
  rw [hv]
  refine Submodule.sub_mem _ (Submodule.sum_mem _ fun M hM => ?_) (Submodule.smul_mem _ _ ?_)
  · exact le_iSup₂ (f := fun M (_ : M ∈ S) => fixBW A M) M hM (hf M hM v)
  · exact le_iSup₂ (f := fun M (_ : M ∈ S) => fixBW A M) M₀ hM₀ (fixBW_top_le A M₀ (hT v))

private theorem natCard_fixBW (A : Subgroup (GL (Fin n) (ZMod 2))) (M : Subgroup ↥A) :
    Nat.card ↥(fixBW A M) = 2 ^ finrank (ZMod 2) ↥(fixBW A M) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

private theorem le_of_iSup_fixBW_eq_top {A : Subgroup (GL (Fin n) (ZMod 2))} {p m : ℕ}
    (S : Finset (Subgroup ↥A)) (hS : S.card = p + 1) (hgen : ⨆ M ∈ S, fixBW A M = ⊤)
    (hM : ∀ M ∈ S, finrank (ZMod 2) ↥(fixBW A M) ≤ m) :
    n + finrank (ZMod 2) ↥(fixBW A ⊤) * p ≤ m * (p + 1) := by
  classical
  have hdim := finrank_sup_add_le (fixBW A ⊤) (fixBW A) S fun M _ => fixBW_top_le A M
  rw [hgen, sup_top_eq, finrank_top, Module.finrank_fin_fun, hS] at hdim
  have hsumle := Finset.sum_le_card_nsmul S _ m hM
  rw [hS, smul_eq_mul] at hsumle
  nlinarith

theorem card_fixed_pow_mul_le {n p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (GL (Fin n) (ZMod 2))} (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (hfix : ∀ a ∈ A, a ≠ 1 → Nat.card {v : Fin n → ZMod 2 //
      (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v} ≤ 2 ^ m) :
    2 ^ n * Nat.card {v : Fin n → ZMod 2 // ∀ a ∈ A,
      (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v} ^ p ≤ 2 ^ (m * (p + 1)) := by
  classical
  have hp : p.Prime := Fact.out
  have hexp : ∀ g : ↥A, g ^ p = 1 := fun g => Subtype.ext (by simpa using hA.2 g g.2)
  have hpK : ((p : ℕ) : ZMod 2) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff_even, hp.even_iff]
    exact hp2
  have hsum := CFSG.RankThree.Classical.sum_avgOp_lines (ρ := rhoBW A) hp hexp hAc hpK
  have hLs := CFSG.RankThree.Classical.card_subgroups_natCard_eq_prime hp hexp hAc
  have hgen := iSup_fixBW_eq_top (Finset.card_pos.1 (by rw [hLs]; omega))
    (fun M _ v => by
      intro g hg
      exact CFSG.RankThree.Classical.apply_avgOp hg v)
    (fun v => by
      intro g _
      exact CFSG.RankThree.Classical.apply_avgOp (Subgroup.mem_top g) v) hsum
  have hfixM : ∀ M : Subgroup ↥A, Nat.card M = p → finrank (ZMod 2) ↥(fixBW A M) ≤ m := by
    intro M hMc
    obtain ⟨g, hgM, hg1⟩ : ∃ g ∈ M, g ≠ 1 := by
      by_contra! h
      rw [(Subgroup.eq_bot_iff_forall M).2 h, Subgroup.card_bot] at hMc
      exact hp.one_lt.ne hMc
    have hle : Nat.card ↥(fixBW A M) ≤ Nat.card {v : Fin n → ZMod 2 //
        ((g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v} :=
      Nat.card_le_card_of_injective (fun x => ⟨x.1, x.2 g hgM⟩) fun x y h =>
        Subtype.ext (Subtype.mk.inj h)
    have h2 : 2 ^ finrank (ZMod 2) ↥(fixBW A M) ≤ 2 ^ m := by
      rw [← natCard_fixBW]
      exact hle.trans (hfix g g.2 fun h => hg1 (Subtype.ext h))
    exact (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).1 h2
  have hC : Nat.card {v : Fin n → ZMod 2 // ∀ a ∈ A,
      (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v} = Nat.card ↥(fixBW A ⊤) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v =>
      ⟨fun h => by
        intro g _
        exact h g g.2, fun h a ha => h ⟨a, ha⟩ (Subgroup.mem_top _)⟩)
  rw [hC, natCard_fixBW, ← pow_mul, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (le_of_iSup_fixBW_eq_top _ hLs hgen fun M hM =>
    hfixM M (Finset.mem_filter.1 hM).2)

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
