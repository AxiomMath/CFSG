module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430ClsRed
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430ONModel
import CFSG.RankThree.Native.ONTripleUnique
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCoverCert

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

attribute [local irreducible] dotProduct

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.RankThree.Native.ONTriple (GM xG nonempty_equiv_FHat modelEquiv)

set_option linter.unusedSectionVars false


private theorem exists_embedding {Q : Type} [Group Q] [Finite Q] {K I₀ : Subgroup Q} {y : Q}
    (hM : I1430Model K I₀ y) (hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) (sporIs .ONan))
    (h3 : Nat.card (Subgroup.center ↥K) = 3) :
    ∃ ι : GM →* Q, Function.Injective ι ∧ ι.range = K ∧
      ∀ x, y * ι x * y⁻¹ = ι (xG 0 * x * (xG 0)⁻¹) := by
  obtain ⟨hKn, hq, -, -, hy3, hyC, -, -, -⟩ := hM
  haveI := hKn
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have eK : Subgroup.center ↥K ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq h3
    (by rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rw [sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  obtain ⟨f⟩ := nonempty_equiv_FHat (Subgroup.center ↥K) eK (e.trans b.symm)
  obtain ⟨ψ⟩ : Nonempty (↥K ≃* GM) := ⟨f.trans modelEquiv⟩
  obtain ⟨α, hα⟩ : ∃ α : MulAut ↥K, ∀ k : ↥K, ((α k : ↥K) : Q) = y * k * y⁻¹ :=
    ⟨MulAut.conjNormal y, fun k => MulAut.conjNormal_apply y k⟩
  obtain ⟨β, hβ⟩ : ∃ β : GM ≃* GM, ∀ x, β x = ψ (α (ψ.symm x)) :=
    ⟨(ψ.symm.trans α).trans ψ, fun x => rfl⟩
  have hα3 : ∀ k : ↥K, α (α (α k)) = k := fun k => Subtype.ext (by
    rw [hα, hα, hα]
    calc y * (y * (y * (k : Q) * y⁻¹) * y⁻¹) * y⁻¹ = y ^ 3 * k * (y ^ 3)⁻¹ := by
          rw [pow_three]; group
      _ = k := by rw [hy3, one_mul, inv_one, mul_one])
  have hβ3 : ∀ x, β (β (β x)) = x := fun x => by
    simp only [hβ, MulEquiv.symm_apply_apply, hα3, MulEquiv.apply_symm_apply]
  have hβ1 : ∃ x, β x ≠ x := by
    by_contra hall
    apply hyC
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : β (ψ ⟨k, hk⟩) = ψ ⟨k, hk⟩ := by
      by_contra hne
      exact hall ⟨_, hne⟩
    rw [hβ, MulEquiv.symm_apply_apply] at h
    have h' : y * k * y⁻¹ = k := by
      have := hα ⟨k, hk⟩
      rw [ψ.injective h] at this
      exact this.symm
    calc k * y = y * k * y⁻¹ * y := by rw [h']
      _ = y * k := by group
  obtain ⟨m, hm⟩ := i1430ON_exists_conj_x0 β hβ3 hβ1
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : ↥K ≃* GM, ∀ k, ψ' k = m⁻¹ * ψ k * m :=
    ⟨ψ.trans (MulAut.conj m⁻¹), fun k => by rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]⟩
  refine ⟨K.subtype.comp ψ'.symm.toMonoidHom, K.subtype_injective.comp ψ'.symm.injective, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact (ψ'.symm x).2
    · intro hq
      exact ⟨ψ' ⟨q, hq⟩, by simp⟩
  · intro x
    obtain ⟨k, rfl⟩ := ψ'.surjective x
    show y * ((ψ'.symm (ψ' k) : ↥K) : Q) * y⁻¹ = ((ψ'.symm (xG 0 * ψ' k * (xG 0)⁻¹) : ↥K) : Q)
    rw [MulEquiv.symm_apply_apply, ← hα]
    congr 1
    apply ψ'.injective
    rw [MulEquiv.apply_symm_apply, hψ', hψ',
      show ψ (α k) = β (ψ k) by rw [hβ, MulEquiv.symm_apply_apply], hm]
    group

theorem i1430ONCover_holds :
    I1430ONCover := by
  intro Q _ _ K I₀ y hM hcat
  have hdvd : Nat.card (Subgroup.center ↥K) ∣ 3 := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    rw [sporIs] at hi
    subst hi
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    have hq : CFSG.IsQuasisimple ↥K := ⟨⟨hM.2.1.1⟩, hM.2.1.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hM.2.1⟩
    have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq
      (X := CFSG.Blueprint.NativeSporadic.Carrier .ONan) (e.trans b.symm)
    rwa [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover.nativeRow_ONan] at h
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · exact h1
  · exfalso
    obtain ⟨ι, hι, hK, hy⟩ := exists_embedding hM hcat h3
    obtain ⟨-, -, -, -, -, -, hI, hT, -⟩ := hM
    have h := i1430ON_card_center_pQuot ι hι hK hy hI
    rw [hT.2] at h
    exact absurd h (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
