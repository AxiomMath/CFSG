module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneNodes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverFamilies
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSimple

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.HallHigman CFSG.QuasithinUnique CFSG.AGLEmbedding.BlockCyc
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

section Ctx

variable {W : Type} [Group W] [Finite W]

structure CoverCtxOne (L S₀ A₁ A₂ : Subgroup W) : Prop where
  syl : IsSylowTwoOf S₀ L
  cov : CoveredByTwo L S₀ A₁ A₂
  solv₁ : SolvFree ((A₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
  solv₂ : SolvFree ((A₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))

variable {L S₀ A₁ A₂ : Subgroup W} {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem CoverCtxOne.cover (ctx : CoverCtxOne L S₀ A₁ A₂)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M) :
    ∃ π' : K →* ↥L ⧸ Subgroup.center ↥L, BorelQuotient D n H π' M ∧
      ∀ i, (rankOne D.rootGroup i).map π' ≤
          (A₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ∨
        (rankOne D.rootGroup i).map π' ≤
          (A₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
  obtain ⟨π', h', hT⟩ := exists_conj_borelQuotient ctx.syl h
  exact ⟨π', h', fun i => cover_of_borelQuotient ctx.syl ctx.cov h' hT i⟩

theorem CoverCtxOne.false_five (ctx : CoverCtxOne L S₀ A₁ A₂)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π 1)
    {exc : Fin D.rank → Fin D.rank → Prop} (hL : TwoLevi D exc) (h3 : ∀ i, HasOrderThree D i)
    (h3nc : ∀ i, HasOrderThreeNC D i)
    (h6 : ∀ i, Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    (hA2 : ∀ i j, i ≠ j → D.cartan i j ≠ 0 → ¬ exc i j →
      D.cartan i j = -1 ∧ D.cartan j i = -1)
    (hexc : ∀ i j, exc i j → ¬ IsPSolvable 3 ↥(rankOne D.rootGroup i ⊔ rankOne D.rootGroup j))
    (htri : ∀ i j l : Fin D.rank, i ≠ j → i ≠ l → j ≠ l → D.cartan i j ≠ 0 → D.cartan j l ≠ 0 →
      D.cartan i l ≠ 0 → False)
    (h27 : E27Free ((A₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ∧
      E27Free ((A₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))))
    (hrank : 5 ≤ D.rank) : False := by
  obtain ⟨π', h', hcov⟩ := ctx.cover h
  exact false_of_five_nodes h' hL h3 h3nc h6 hA2 hexc htri ctx.solv₁ h27.1 ctx.solv₂ h27.2 hcov
    hrank

end Ctx

section SL

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {m : ℕ} {F : Type} [Field F]
  [Finite F] [CharP F 2]

theorem sl_adj {i j : Fin m} (hij : i ≠ j) (hA : (SpecialLinear.rootDatum m F).cartan i j ≠ 0) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
  by_contra hn
  apply hA
  show CartanMatrix.A m i j = 0
  simp [CartanMatrix.A, Fin.ext_iff, hv]
  omega

theorem sl_cartan_neg_one {i j : Fin m} (hij : i ≠ j)
    (hA : (SpecialLinear.rootDatum m F).cartan i j ≠ 0) :
    (SpecialLinear.rootDatum m F).cartan i j = -1 ∧ (SpecialLinear.rootDatum m F).cartan j i = -1 := by
  have hadj := sl_adj (F := F) hij hA
  have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
  constructor
  · show CartanMatrix.A m i j = -1
    simp [CartanMatrix.A, Fin.ext_iff, hv]
    omega
  · show CartanMatrix.A m j i = -1
    simp [CartanMatrix.A, Fin.ext_iff, Ne.symm hv]
    omega

theorem sl_triangle_free {i j l : Fin m} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (h1 : (SpecialLinear.rootDatum m F).cartan i j ≠ 0)
    (h2 : (SpecialLinear.rootDatum m F).cartan j l ≠ 0)
    (h3 : (SpecialLinear.rootDatum m F).cartan i l ≠ 0) : False := by
  have a1 := sl_adj (F := F) hij h1
  have a2 := sl_adj (F := F) hjl h2
  have a3 := sl_adj (F := F) hil h3
  omega

theorem CoverCtxOne.false_sl_five (ctx : CoverCtxOne L S₀ A₁ A₂)
    (h27 : E27Free ((A₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ∧
      E27Free ((A₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))))
    (hF : Nat.card F = 2) (hm : 5 ≤ m)
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* ↥L ⧸ Subgroup.center ↥L) :
    False := by
  have h := borelQuotient_sl e
  have hM : Nat.card F - 1 = 1 := by omega
  rw [hM] at h
  refine ctx.false_five h (twoLevi_sl hF) (fun i => (hasSL2Node_sl i).hasOrderThree)
    (fun i => (hasSL2Node_sl i).hasOrderThreeNC) (fun i => ?_)
    (fun i j hij hA _ => sl_cartan_neg_one hij hA) (fun _ _ h => h.elim)
    (fun i j l hij hil hjl h1 h2 h3 => sl_triangle_free hij hil hjl h1 h2 h3) h27 hm
  obtain ⟨φ, hφ, hx, hy⟩ := SL.rankOne (F := F) i
  exact rankOne_six_of_sl2 hF SL.isParametrization hφ hx hy

end SL

section Sp

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic
open CFSG.LieType.Universal.Symplectic.SpExtras (ne_succ')

theorem sp_tail_not_isPSolvable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    {k : Fin n} (hk2 : k.val + 2 = n) :
    ¬ IsPSolvable 3 ↥(rankOne (rootGroup n K) k ⊔
      rankOne (rootGroup n K) ⟨k.val + 1, by omega⟩) := by
  have hk : k.val + 1 < n := by omega
  have hlong : ¬(⟨k.val + 1, hk⟩ : Fin n).val + 1 < n := by
    simp only
    omega
  have hsup : rankOne (rootGroup n K) k ⊔ rankOne (rootGroup n K) ⟨k.val + 1, hk⟩ =
      (spEmbed (K := K) (pairMap k ⟨k.val + 1, hk⟩) (pairMap_injective (ne_succ' hk))).range := by
    rw [← range_shortBlock_eq_rankOne hk, ← range_longBlock_eq_rankOne hlong]
    exact shortBlock_sup_longBlock (ne_succ' hk)
  have := Fintype.ofFinite K
  have hK2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  set θ := spEmbed (K := K) (pairMap k ⟨k.val + 1, hk⟩) (pairMap_injective (ne_succ' hk)) with hθ
  have hθinj : Function.Injective θ := spEmbed_injective (pairMap_injective (ne_succ' hk))
  let Φ : θ.range ≃* Equiv.Perm (Fin 6) :=
    (MonoidHom.ofInjective hθinj).symm.trans (CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm K hK2)
  rw [hsup]
  intro hs
  exact not_isPSolvable_perm_six
    (Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv Φ hs)

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {n : ℕ} {F : Type} [Field F]
  [Finite F] [CharP F 2]

theorem sp_adj {i j : Fin n} (hij : i ≠ j) (hA : (rootDatum n F).cartan i j ≠ 0) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
  by_contra hn
  apply hA
  show cartanC n i j = 0
  simp [cartanC, Fin.ext_iff, hv]
  omega

theorem sp_cartan_neg_one {i j : Fin n} (hij : i ≠ j) (hA : (rootDatum n F).cartan i j ≠ 0)
    (hnt : ¬ spTail n i j) :
    (rootDatum n F).cartan i j = -1 ∧ (rootDatum n F).cartan j i = -1 := by
  have hadj := sp_adj (F := F) hij hA
  unfold spTail at hnt
  rcases hadj with h | h
  · have hj : j.val + 1 < n := by omega
    exact cartanC_succ h hj
  · have hi : i.val + 1 < n := by omega
    exact (cartanC_succ h hi).symm

theorem sp_triangle_free {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (h1 : (rootDatum n F).cartan i j ≠ 0) (h2 : (rootDatum n F).cartan j l ≠ 0)
    (h3 : (rootDatum n F).cartan i l ≠ 0) : False := by
  have a1 := sp_adj (F := F) hij h1
  have a2 := sp_adj (F := F) hjl h2
  have a3 := sp_adj (F := F) hil h3
  omega

theorem CoverCtxOne.false_sp_five (ctx : CoverCtxOne L S₀ A₁ A₂)
    (h27 : E27Free ((A₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ∧
      E27Free ((A₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))))
    (hF : Nat.card F = 2) (hn : 5 ≤ n)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSp n F)) : False := by
  have h := borelQuotient_sp e
  have hM : Nat.card F - 1 = 1 := by omega
  rw [hM] at h
  refine ctx.false_five h (twoLevi_sp hF) (fun i => (hasSL2Node_sp i).hasOrderThree)
    (fun i => (hasSL2Node_sp i).hasOrderThreeNC) (fun i => ?_)
    (fun i j hij hA hnt => sp_cartan_neg_one hij hA hnt) (fun i j hij => ?_)
    (fun i j l hij hil hjl h1 h2 h3 => sp_triangle_free hij hil hjl h1 h2 h3) h27 hn
  · obtain ⟨φ, hφ, hx, hy⟩ := Sp.rankOne (F := F) i
    exact rankOne_six_of_sl2 hF Sp.isParametrization hφ hx hy
  · rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hi1 : i.val + 1 < n := by omega
      have hk : j = ⟨i.val + 1, hi1⟩ := Fin.ext (by simp; omega)
      subst hk
      exact sp_tail_not_isPSolvable hF h1
    · have hj1 : j.val + 1 < n := by omega
      have hk : i = ⟨j.val + 1, hj1⟩ := Fin.ext (by simp; omega)
      subst hk
      rw [sup_comm]
      exact sp_tail_not_isPSolvable hF h1

end Sp

section SpinPlus

open CFSG.LieType.Universal.Spin

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {n : ℕ} {F : Type} [Field F]
  [Finite F] [CharP F 2]

theorem cartanD_triangle_free {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (h1 : cartanD n i j ≠ 0) (h2 : cartanD n j l ≠ 0) (h3 : cartanD n i l ≠ 0) : False := by
  simp only [cartanD, Matrix.of_apply, hij, hil, hjl, ↓reduceIte] at h1 h2 h3
  have hv1 : i.val ≠ j.val := fun e => hij (Fin.ext e)
  have hv2 : i.val ≠ l.val := fun e => hil (Fin.ext e)
  have hv3 : j.val ≠ l.val := fun e => hjl (Fin.ext e)
  split_ifs at h1 h2 h3 <;> omega

theorem CoverCtxOne.false_spinPlus_five (ctx : CoverCtxOne L S₀ A₁ A₂)
    (h27 : E27Free ((A₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ∧
      E27Free ((A₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))))
    (hF : Nat.card F = 2) (hn : 5 ≤ n)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) : False := by
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have h3n : 3 ≤ n := by omega
  have h := borelQuotient_spinPlus h3n e
  have hM : Nat.card F - 1 = 1 := by omega
  rw [hM] at h
  refine ctx.false_five h (twoLevi_spinPlus hF h3n h.ct h.extras)
    (fun i => (hasSL2Node_spinPlus h3n i).hasOrderThree)
    (fun i => (hasSL2Node_spinPlus h3n i).hasOrderThreeNC) (fun i => ?_)
    (fun i j hij hA _ => cartanD_eq_neg_one hij hA) (fun _ _ h => h.elim)
    (fun i j l hij hil hjl h1 h2 h3 => cartanD_triangle_free hij hil hjl h1 h2 h3) h27 hn
  obtain ⟨φ, hφ, hx, hy⟩ := SpinPlus.rankOne (K := F) h3n i
  exact rankOne_six_of_sl2 hF (SpinPlus.isParametrization (K := F) h3n) hφ hx hy

end SpinPlus

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
