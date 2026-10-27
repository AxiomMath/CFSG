module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexBlockOK
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCover
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTower
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusHas
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)

theorem orthMinus_leviInnAt_of_index
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} [L.Normal] (hPL : P ≤ L)
    {E : Type} [Group E] [Finite E] (ρ : E →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center E) (Q : Subgroup E) (hQ : Q = coverSub ρ P)
    {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]
    [∀ j, Finite (G j)] (S H : ∀ j, Subgroup (G j)) (β : ↥Q →* ∀ j, G j)
    (h2 : IsPGroup 2 β.ker) (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hqs : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) ∨ Group.IsSolvable ↥(S j))
    (hH : ∀ (x : ↥Q) (j : ι), β x j ∈ H j)
    (hblock : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → BlockOK (H j) (S j))
    (hZ : ∀ (j : ι) (A : Subgroup (G j)), A ≤ S j → IsElemAbelian 3 A → Nat.card A = 9 →
      ∀ x : ↥Q, ρ (x : E) = 1 → β x ∈ A.map (MonoidHom.mulSingle G j) → x = 1)
    (hrk : Open.pRank 3 (perfectJoin P) ≤ 1) : LeviInnAt P := by
  classical
  set e := Fintype.equivFin ι
  set π : (∀ j, G j) →* ∀ i, G (e.symm i) :=
    MonoidHom.pi fun i => Pi.evalMonoidHom G (e.symm i) with hπ
  have hπinj : Function.Injective π := by
    intro x y hxy
    funext j
    obtain ⟨i, rfl⟩ := e.symm.surjective j
    exact congrFun hxy i
  have hπsingle : ∀ (i : Fin (Fintype.card ι)) (y : G (e.symm i)),
      π (Pi.mulSingle (e.symm i) y) = Pi.mulSingle (M := fun i => G (e.symm i)) i y := by
    intro i y
    funext i'
    change Pi.mulSingle (e.symm i) y (e.symm i') =
      Pi.mulSingle (M := fun i => G (e.symm i)) i y i'
    by_cases hi : i' = i
    · subst hi
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne (e.symm.injective.ne hi), Pi.mulSingle_eq_of_ne hi]
  have hker' : (π.comp β).ker = β.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, ← map_one π, hπinj.eq_iff]
  refine leviInnAt_of_levi_data (G := fun i => G (e.symm i)) hPL ρ hρ hker Q hQ
    (fun i => S (e.symm i)) (fun i => H (e.symm i)) (π.comp β) (hker' ▸ h2) ?_ ?_
    (fun i => hqs _) (fun x i => hH x (e.symm i)) (fun i => hblock _)
    (fun i A hA hAe hAc x hx hxA => ?_) hrk
  · rw [Subgroup.pi_le_iff]
    rintro i _ ⟨y, hy, rfl⟩
    have hmem : Pi.mulSingle (e.symm i) y ∈ Subgroup.pi Set.univ S := by
      refine (Subgroup.mem_pi _).mpr fun j _ => ?_
      by_cases hj : j = e.symm i
      · subst hj
        rw [Pi.mulSingle_eq_same]
        exact hy
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact Subgroup.one_mem _
    obtain ⟨x, hx⟩ := hS hmem
    exact ⟨x, by rw [MonoidHom.comp_apply, hx, hπsingle]; rfl⟩
  · rw [MonoidHom.range_comp, ← Subgroup.map_commutator]
    rintro _ ⟨z, hz, rfl⟩
    refine (Subgroup.mem_pi _).mpr fun i _ => ?_
    exact (Subgroup.mem_pi _).mp (hc hz) (e.symm i) trivial
  · obtain ⟨y, hy, hyx⟩ := hxA
    refine hZ (e.symm i) A hA hAe hAc x hx ⟨y, hy, hπinj ?_⟩
    rw [MonoidHom.comp_apply] at hyx
    rw [← hyx]
    exact hπsingle i y

theorem orthMinus_blockOK_of_sq_mem {G : Type*} [Group G] {H S : Subgroup G}
    (hsq : ∀ g ∈ H, g ^ 2 ∈ S) : BlockOK H S := by
  intro g hg hn k hk
  left
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨b, hb⟩ := hodd.add_one
  refine ⟨g ^ (3 ^ k + 1), ?_, fun s hs => ?_⟩
  · rw [hb, ← two_mul, pow_mul]
    exact S.pow_mem (hsq g hg) b
  · have h1 := hk _ (hn s hs)
    calc g * s * g⁻¹ = g ^ 3 ^ k * (g * s * g⁻¹) * (g ^ 3 ^ k)⁻¹ := h1.symm
      _ = g ^ (3 ^ k + 1) * s * (g ^ (3 ^ k + 1))⁻¹ := by
        rw [pow_succ, mul_inv_rev]
        simp only [mul_assoc]

section Residual

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

open Module QuadraticMap in
theorem orthMinus_sq_mem_orthResDer (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    {g : ((Fin m ⊕ Fin m → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin m ⊕ Fin m → K) × (Fin 2 → K))}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))) :
    g ^ 2 ∈ orthResDer K b c m := by
  have hnd := nondegenerate_polarBilin_quadTail (r := m) (nondegenerate_minusTailForm hirr)
  by_cases h3 : 3 ≤ m
  · obtain ⟨-, -, -, -, -, hsq, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd
        ⟨tailFlag K (Fin 2 → K) m 3, finrank_tailFlag h3,
          fun x hx => quadTail_eq_zero_of_mem_tailFlag hx⟩
    exact hsq g hg
  · have hfr : finrank K ((Fin m ⊕ Fin m → K) × (Fin 2 → K)) = 2 * m + 2 := by
      rw [finrank_tailSpace, finrank_fin_two_fun]
    obtain ⟨-, -, -, hidx, -⟩ :=
      CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
        (quadTail m (minusTailForm K b c)) hnd (by omega) fun U hU =>
          exists_minusTail_ne_zero hirr U (by omega)
    haveI : (⁅TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)),
        TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))⁆.subgroupOf
          (TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)))).Normal :=
      Subgroup.normal_of_index_eq_two hidx
    have := Subgroup.pow_index_mem (⁅TauCeti.QuadraticMap.orthogonalGroup
      (quadTail m (minusTailForm K b c)), TauCeti.QuadraticMap.orthogonalGroup
        (quadTail m (minusTailForm K b c))⁆.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup
          (quadTail m (minusTailForm K b c)))) ⟨g, hg⟩
    rw [hidx] at this
    exact this

theorem orthMinus_blockOK_orthResDer (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (m : ℕ)
    (hq : CFSG.Open.IsQuasisimple ↥(orthResDer K b c m)) :
    BlockOK (TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)))
      (orthResDer K b c m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact absurd hq (orthMinus_not_isQuasisimple_of_comm (comm_orthResDer_zero hirr))
  · exact orthMinus_blockOK_of_sq_mem fun g hg => orthMinus_sq_mem_orthResDer hirr hm hg

variable {r s : ℕ} {d : Fin (s + 1) → ℕ}

variable (K r d) in
@[expose] noncomputable def orthMinus_leviOver (b c : K) : ∀ j, Subgroup (orthLeviGroup K r d j)
  | .inl _ => ⊤
  | .inr _ => TauCeti.QuadraticMap.orthogonalGroup
      (quadTail (r - d (Fin.last s)) (minusTailForm K b c))

theorem orthMinus_blockOK_orthLeviBlock (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (j : Fin s ⊕ Unit) (hq : CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c j)) :
    BlockOK (orthMinus_leviOver K r d b c j) (orthLeviBlock K r d b c j) := by
  rcases j with l | u
  · change BlockOK ⊤ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range
    change CFSG.Open.IsQuasisimple ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range at hq
    have hm := two_le_of_isQuasisimple_specialLinear
      (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K)
        (d l.succ - d l.castSucc)).symm hq)
    exact blockOK_gl_sl _ hm
  · exact orthMinus_blockOK_orthResDer hirr _ hq

end Residual

theorem leviInnOn_orthMinus
    (hGA : GriessAllModelsStatement) : LeviInnOn (IsLieOf IdxTwistedD) := by
  intro Y _ _ L P hCP hC hLn _ _ hrk
  haveI := hLn
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  obtain ⟨dI, hdI, ⟨e⟩⟩ := id hC
  obtain ⟨K, _, _, _, b, c, r, s, d, ρ, hr, hirr, hcuts, hρ, -⟩ :=
    exists_orthCover_of_twistedD hZ hCP dI hdI e
  have : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  refine orthMinus_leviInnAt_of_index hCP.parab.1 ρ.toMonoidHom ρ.surjective (fun x hx => ?_) _
    hρ.symm (orthLeviBlock K r d b c) (orthMinus_leviOver K r d b c) (orthLeviHom b c hcuts)
    (isPGroup_ker_orthLeviHom hcuts)
    (pi_orthLeviBlock_le_range hcuts hr (commutator_orthogonalGroup_quadTail_minus hr hirr))
    (commutator_range_orthLeviHom_le hcuts) (isQuasisimple_or_isSolvable_orthLeviBlock hirr)
    (fun x j => ?_) (fun j hq => orthMinus_blockOK_orthLeviBlock hirr j hq)
    (fun j A _ _ _ x hx _ => ?_) hrk
  · have : x = 1 := ρ.injective (by rw [MonoidHom.mem_ker] at hx; exact hx.trans (map_one _).symm)
    rw [this]
    exact Subgroup.one_mem _
  · rcases j with l | u
    · exact Subgroup.mem_top _
    · exact orthResHom_mem_orthogonalGroup hcuts x
  · exact Subtype.ext (ρ.injective (hx.trans (map_one ρ).symm))

theorem fieldIndexOn_orthMinus
    (hGA : GriessAllModelsStatement) : FieldIndexOn (IsLieOf IdxTwistedD) :=
  fieldIndexOn_of_outPNice (fun _ _ _ _ _ _ hC _ => outPNice_three_of_idxTwistedD hC)
    (leviInnOn_orthMinus hGA)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
