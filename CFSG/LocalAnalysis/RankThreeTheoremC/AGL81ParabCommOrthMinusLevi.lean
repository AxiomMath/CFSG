module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusHat
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
  (range_le_wSup isQuasisimple_or_perm_three)
open scoped commutatorElement

theorem pi_mulSingle_conj {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
    (a : ∀ i, G i) (i : ι) (x : G i) :
    a * Pi.mulSingle i x * a⁻¹ = Pi.mulSingle i (a i * x * (a i)⁻¹) := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.mulSingle_eq_of_ne h]

namespace OmCover

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {r : ℕ} {K : Type} [Field K] [Finite K]
  [CharP K 2] {b c : K} {s : ℕ} {d : Fin (s + 1) → ℕ} (C : OmCover Y P r K b c d)
  (hd : OrthCuts r d) (hPY : P ≤ Y)

include hd hPY in
theorem toHat_range_normal {D : Type} [Group D] (ψ : D →* ↥(orthParab r (minusTailForm K b c) d))
    (h : ∀ (q : ↥(orthParab r (minusTailForm K b c) d)) (x : D), ∃ x' : D,
      orthLeviHom b c hd (q * ψ x * q⁻¹) = orthLeviHom b c hd (ψ x')) :
    (C.toHat.comp ψ).range.Normal := by
  refine ⟨?_⟩
  rintro _ ⟨x, rfl⟩ g
  obtain ⟨q, rfl⟩ := C.toHat_surjective hPY g
  obtain ⟨x', hx'⟩ := h q x
  refine ⟨x', ?_⟩
  have hker : q * ψ x * q⁻¹ * (ψ x')⁻¹ ∈ C.toHat.ker := by
    refine C.ker_orthLeviHom_le_ker_toHat hd hPY ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx', mul_inv_cancel]
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hker
  simp only [MonoidHom.comp_apply, map_mul, map_inv] at hker ⊢
  rw [← hker]

include hd hPY in
theorem toHat_orthLeviSL_mem_wSup (hr : 3 ≤ r) (l : Fin s)
    (B : SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K) :
    C.toHat (orthLeviSL hd (minusTailForm K b c) hr l B) ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  by_cases hk : 2 ≤ d l.succ - d l.castSucc
  · set ψ : SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
      ↥(orthParab r (minusTailForm K b c) d) := orthLeviSL hd (minusTailForm K b c) hr l with hψ
    have hnorm : (C.toHat.comp ψ).range.Normal := by
      refine C.toHat_range_normal hd hPY ψ (fun q x => ?_)
      obtain ⟨x', hx'⟩ := Sp.conj_mem_range_toGL (orthLeviHom b c hd q (.inl l))
        (⟨x, rfl⟩ : SpecialLinearGroup.toGL x ∈
          (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
            GL (Fin (d l.succ - d l.castSucc)) K).range)
      refine ⟨x', ?_⟩
      simp only [hψ]
      rw [map_mul, map_mul, map_inv, orthLeviHom_orthLeviSL, orthLeviHom_orthLeviSL,
        pi_mulSingle_conj]
      congr 1
      rw [← hx']
    have h := range_le_wSup (CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' (X := ↥P) 2)
      (MonoidHom.id (SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K))
      Function.surjective_id (C.toHat.comp ψ) (by rw [MonoidHom.ker_id]; exact bot_le) hnorm
      (isQuasisimple_or_perm_three hk (MulEquiv.refl _))
    exact h ⟨B, rfl⟩
  · haveI := LeviBlock.subsingleton_specialLinear_of_lt_two (K := K)
      (m := d l.succ - d l.castSucc) (by omega)
    rw [Subsingleton.elim B 1, map_one, map_one]
    exact one_mem _

@[expose] noncomputable def resLeviE (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) :
    ↥(orthResDer K b c (r - d (Fin.last s))) →*
      ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) :=
  ((orthLeviRes K (Fin 2 → K) hd.last).comp
    (orthResDer K b c (r - d (Fin.last s))).subtype).codRestrict
    (orthElementaryGroup (quadTail r (minusTailForm K b c))) fun B => by
      rw [← commutator_orthogonalGroup_quadTail_minus hr hirr]
      exact orthLeviRes_mem_commutator hd.last B.2

@[expose] noncomputable def resLevi (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) :
    ↥(orthResDer K b c (r - d (Fin.last s))) →* ↥(orthParab r (minusTailForm K b c) d) :=
  (resLeviE hd hr hirr).codRestrict (orthParab r (minusTailForm K b c) d) fun B =>
    mem_orthParab.2 fun i => map_tailFlag_orthLeviRes hd.last
      (hd.mono.monotone (Fin.le_last i)) _

theorem orthLeviHom_conj_resLevi (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (q : ↥(orthParab r (minusTailForm K b c) d))
    (x : ↥(orthResDer K b c (r - d (Fin.last s))))
    (hx : orthResHom (minusTailForm K b c) hd q *
        ((x : ↥(orthResDer K b c (r - d (Fin.last s)))) : _ ≃ₗ[K] _) *
        (orthResHom (minusTailForm K b c) hd q)⁻¹ ∈ orthResDer K b c (r - d (Fin.last s))) :
    orthLeviHom b c hd (q * resLevi hd hr hirr x * q⁻¹) =
      orthLeviHom b c hd (resLevi hd hr hirr ⟨_, hx⟩) := by
  have e1 : orthLeviHom b c hd (resLevi hd hr hirr x) =
      Pi.mulSingle (M := orthLeviGroup K r d) (.inr ()) ((x : ↥(orthResDer K b c
        (r - d (Fin.last s)))) : _ ≃ₗ[K] _) :=
    orthLeviHom_orthLeviResElt hd (commutator_orthogonalGroup_quadTail_minus hr hirr) x
  have e2 : orthLeviHom b c hd (resLevi hd hr hirr ⟨_, hx⟩) =
      Pi.mulSingle (M := orthLeviGroup K r d) (.inr ())
        (orthResHom (minusTailForm K b c) hd q * ((x : ↥(orthResDer K b c
          (r - d (Fin.last s)))) : _ ≃ₗ[K] _) * (orthResHom (minusTailForm K b c) hd q)⁻¹) :=
    orthLeviHom_orthLeviResElt hd (commutator_orthogonalGroup_quadTail_minus hr hirr) ⟨_, hx⟩
  rw [map_mul, map_mul, map_inv, e1, e2, pi_mulSingle_conj]
  rfl

include hd hPY in
theorem toHat_resLevi_mem_wSup (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (hm : 1 ≤ r - d (Fin.last s)) (B : ↥(orthResDer K b c (r - d (Fin.last s)))) :
    C.toHat (resLevi hd hr hirr B) ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  obtain ⟨f, hK⟩ : ∃ f, Nat.card K = 2 ^ f := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨hsimple, hnc, -⟩ := orthResDer_facts hK hm hirr
  have hq : CFSG.Open.IsQuasisimple ↥(orthResDer K b c (r - d (Fin.last s))) :=
    (orthMinus_isQuasisimple_of_simple hnc).1
  have hnorm : (C.toHat.comp (resLevi hd hr hirr)).range.Normal := by
    refine C.toHat_range_normal hd hPY (resLevi hd hr hirr) (fun q x => ?_)
    have hgO := orthResHom_mem_orthogonalGroup hd q
    have hmem : orthResHom (minusTailForm K b c) hd q * (x : _ ≃ₗ[K] _) *
        (orthResHom (minusTailForm K b c) hd q)⁻¹ ∈ orthResDer K b c (r - d (Fin.last s)) := by
      have hx := orthDerived_le_orthogonalGroup_of_commutator _ x.2
      have hc : ⁅orthResHom (minusTailForm K b c) hd q, (x : _ ≃ₗ[K] _)⁆ ∈
          orthDerived (quadTail (r - d (Fin.last s)) (minusTailForm K b c)) :=
        Subgroup.commutator_mem_commutator hgO hx
      have : orthResHom (minusTailForm K b c) hd q * (x : _ ≃ₗ[K] _) *
          (orthResHom (minusTailForm K b c) hd q)⁻¹ =
          ⁅orthResHom (minusTailForm K b c) hd q, (x : _ ≃ₗ[K] _)⁆ * (x : _ ≃ₗ[K] _) := by
        rw [commutatorElement_def]
        group
      rw [this]
      exact Subgroup.mul_mem _ hc x.2
    exact ⟨⟨_, hmem⟩, orthLeviHom_conj_resLevi hd hr hirr q x hmem⟩
  have h := range_le_wSup (CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' (X := ↥P) 2)
    (MonoidHom.id ↥(orthResDer K b c (r - d (Fin.last s)))) Function.surjective_id
    (C.toHat.comp (resLevi hd hr hirr)) (by rw [MonoidHom.ker_id]; exact bot_le) hnorm
    (Or.inl hq)
  exact h ⟨B, rfl⟩

end OmCover

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
