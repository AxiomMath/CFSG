module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer
import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields

public section

namespace CFSG.AGLEmbedding

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.RankThree.PartTwo.KFacts

private noncomputable def fieldPart (K : Type) [Field K] [Finite K] :
    MulAut (PSL2 K) →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom

section Field

variable {K : Type} [Field K] [Finite K]

private theorem fieldPart_conj (x : PSL2 K) : fieldPart K (MulAut.conj x) = 1 := by
  have h : semilinearEquivAut K (SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL x)) = MulAut.conj x := by
    change semilinearAction K _ = _
    rw [semilinearAction_inl, pglAction_toPGL]
  rw [fieldPart, MonoidHom.comp_apply, ← h]
  simp

private theorem exists_conj_eq_of_fieldPart_eq_one {α : MulAut (PSL2 K)}
    (h : fieldPart K α = 1) {m : ℕ} (hm : Odd m) (hα : α ^ m = 1) :
    ∃ x : PSL2 K, MulAut.conj x = α := by
  obtain ⟨g, hg⟩ := mem_range_pglAction_of_rightHom_eq_one h
  have hg' : g ^ m = 1 := pglAction_injective (by rw [map_pow, hg, hα, map_one])
  obtain ⟨x, hx⟩ := exists_toPGL_eq_of_pow_odd hm hg'
  exact ⟨x, by rw [← hg, ← hx, pglAction_toPGL]⟩

private theorem conj_injective :
    Function.Injective (MulAut.conj : PSL2 K →* MulAut (PSL2 K)) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp (eq_bot_iff.mpr fun x hx => ?_)
  have hc : x ∈ Subgroup.center (PSL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hx) y
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  rwa [psl2_center_eq_bot K] at hc

end Field

private theorem mul_conj_mul_inv {G : Type*} [Group G] (y : MulAut G) (t : G) :
    y * MulAut.conj t * y⁻¹ = MulAut.conj (y t) := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem kFactL2AutElemRank : KFactL2AutElemRank := by
  intro p n _ hp2 hn E hE
  have hp : p.Prime := Fact.out
  set ψ := fieldPart (GaloisField p n)
  have hcard : Nat.card E = Nat.card (E.map ψ) * Nat.card (ψ.ker ⊓ E : Subgroup _) := by
    rw [← Subgroup.relIndex_ker, Subgroup.relIndex_mul_card]
  have hcyc : IsCyclic (GaloisField p n ≃+* GaloisField p n) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp _
      (GaloisField.card p n (by omega))).2
  have himg : Nat.card (E.map ψ) ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨_, e, he, rfl⟩ := y
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, ← map_pow, hE.2 e he, map_one, OneMemClass.coe_one]
  set F₀ := E.comap (MulAut.conj : PSL2GF p n →* MulAut (PSL2GF p n))
  have hker : Nat.card (ψ.ker ⊓ E : Subgroup _) ≤ Nat.card F₀ := by
    calc Nat.card (ψ.ker ⊓ E : Subgroup _) ≤ Nat.card (F₀.map MulAut.conj) :=
          Subgroup.card_le_of_le fun e he => ?_
      _ = Nat.card F₀ := Subgroup.card_map_of_injective conj_injective
    obtain ⟨x, hx⟩ := exists_conj_eq_of_fieldPart_eq_one he.1 (hp.odd_of_ne_two hp2) (hE.2 e he.2)
    exact ⟨x, show MulAut.conj x ∈ E from hx ▸ he.2, hx⟩
  have hF₀p : IsPGroup p F₀ := by
    intro x
    refine ⟨1, Subtype.ext (conj_injective ?_)⟩
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, map_pow, map_one]
    exact hE.2 _ x.2
  obtain ⟨T, hT⟩ := hF₀p.exists_le_sylow
  have hTcard := (psl2GF_sylow p n hn T).2
  have hF₀T : Nat.card F₀ ≤ p ^ n := hTcard ▸ Subgroup.card_le_of_le hT
  by_cases hψ : ∀ e ∈ E, ψ e = 1
  · have h1 : Nat.card (E.map ψ) = 1 := by
      rw [Subgroup.card_eq_one, Subgroup.map_eq_bot_iff]
      exact fun e he => hψ e he
    rw [hcard, h1, one_mul]
    exact hker.trans hF₀T
  · simp only [not_forall] at hψ
    obtain ⟨y, hy, hy1⟩ := hψ
    have hlt : F₀ < T := by
      refine lt_of_le_of_ne hT fun hEq => hy1 ?_
      have hfix : ∀ t ∈ (T : Subgroup (PSL2GF p n)), y t = t := by
        intro t ht
        have htE : MulAut.conj t ∈ E := by
          rw [← SetLike.mem_coe, ← hEq] at ht
          exact ht
        have hcomm : y * MulAut.conj t = MulAut.conj t * y :=
          congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨_, htE⟩)
        apply conj_injective
        rw [← mul_conj_mul_inv, hcomm, mul_inv_cancel_right]
      obtain ⟨u, -, hu⟩ := kFactL2UnipotentCentralizer p n hp2 hn T y hfix
      exact (congrArg ψ hu).trans (fieldPart_conj u)
    have hlt' : Nat.card F₀ < p ^ n := hTcard ▸ Subgroup.card_lt_of_lt hlt
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp (hTcard ▸ Subgroup.card_dvd_of_le hT)
    have hkn : k < n := by
      rcases Nat.lt_or_ge k n with h | h
      · exact h
      · exact absurd (hk' ▸ hlt') (by rw [show k = n by omega]; exact lt_irrefl _)
    have hF₀ : Nat.card F₀ * p ≤ p ^ n := by
      rw [hk', ← pow_succ]
      exact Nat.pow_le_pow_right hp.pos hkn
    calc Nat.card E = Nat.card (E.map ψ) * Nat.card (ψ.ker ⊓ E : Subgroup _) := hcard
      _ ≤ p * Nat.card F₀ := Nat.mul_le_mul (Nat.le_of_dvd hp.pos himg) hker
      _ ≤ p ^ n := by rw [mul_comm]; exact hF₀

end CFSG.AGLEmbedding
