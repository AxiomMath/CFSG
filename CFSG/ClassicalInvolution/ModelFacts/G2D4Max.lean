module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4Block
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Model

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

section Group

variable {K : Type} [Group K]

theorem normalizer_le_centralizer {R : Subgroup K} {c : K} (h : IsUniqueInvolution R c) :
    Subgroup.normalizer (R : Set K) ≤ Subgroup.centralizer ({c} : Set K) := by
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := h.conj_eq (normalizer_iff_conjSub_eq.mp hn)
  calc n * c = n * c * n⁻¹ * n := by group
    _ = c * n := by rw [h1]

theorem normalizer_eq_centralizer_of_isCoatom {R : Subgroup K} {c : K}
    (h : IsUniqueInvolution R c) (hZ : Subgroup.center K = ⊥)
    (hcoatom : IsCoatom (Subgroup.normalizer (R : Set K))) :
    Subgroup.normalizer (R : Set K) = Subgroup.centralizer ({c} : Set K) := by
  rcases hcoatom.le_iff.mp (normalizer_le_centralizer h) with htop | heq
  · exfalso
    have hc : c ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({c} : Set K) := by
        rw [htop]
        exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [hZ] at hc
    exact h.ne_one (Subgroup.mem_bot.mp hc)
  · exact heq.symm

theorem conjSub_eq_of_same_involution {R : Subgroup K} {c g : K} (h : IsUniqueInvolution R c)
    (hg : IsUniqueInvolution (conjSub g R) c) (hZ : Subgroup.center K = ⊥)
    (hcoatom : IsCoatom (Subgroup.normalizer (R : Set K))) : conjSub g R = R := by
  have hc : g * c * g⁻¹ = c := (hg.eq (h.conj g)).symm
  have hgc : g ∈ Subgroup.centralizer ({c} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * c = g * c * g⁻¹ * g := by group
      _ = c * g := by rw [hc]
  rw [← normalizer_eq_centralizer_of_isCoatom h hZ hcoatom] at hgc
  exact normalizer_iff_conjSub_eq.mp hgc

theorem isCoatom_map_of_bijective {H : Type} [Group H] (ψ : H →* K) (hinj : Function.Injective ψ)
    (hsurj : Function.Surjective ψ) {A : Subgroup H} (hA : IsCoatom A) : IsCoatom (A.map ψ) := by
  refine ⟨fun htop => hA.1 ?_, fun B hB => ?_⟩
  · rw [← Subgroup.comap_map_eq_self_of_injective hinj A, htop, Subgroup.comap_top]
  · have h1 : A ≤ B.comap ψ := Subgroup.map_le_iff_le_comap.mp hB.le
    have h2 : A < B.comap ψ := by
      refine lt_of_le_of_ne h1 fun h => ?_
      have := Subgroup.map_comap_eq_self_of_surjective hsurj B
      rw [← h] at this
      exact hB.ne this
    have h3 : B.comap ψ = ⊤ := hA.2 _ h2
    calc B = (B.comap ψ).map ψ := (Subgroup.map_comap_eq_self_of_surjective hsurj B).symm
      _ = ⊤ := by
        rw [h3, Subgroup.map_top]
        exact MonoidHom.range_eq_top.mpr hsurj

theorem normalizer_map_of_bijective {H : Type} [Group H] (ψ : H →* K)
    (hinj : Function.Injective ψ) (hsurj : Function.Surjective ψ) (A : Subgroup H) :
    Subgroup.normalizer ((A.map ψ : Subgroup K) : Set K) =
      (Subgroup.normalizer (A : Set H)).map ψ := by
  have h := Subgroup.map_equiv_normalizer_eq A (MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩)
  have e : (MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).toMonoidHom = ψ := MonoidHom.ext fun _ => rfl
  rw [e] at h
  exact h.symm

end Group

section Model

variable {p : ℕ} [Fact p.Prime]

@[expose] def G2D4MaxNormalizer (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), StatedLieAdmissible t n p e → p ≠ 2 →
    ((t = .G2 ∧ 5 ≤ p ^ e) ∨ t = .trialityD4) →
      ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
        IsCoatom (Subgroup.normalizer (R : Set (modelUniv t n p e Fact.out).K))

theorem normalizer_eq_centralizer_model (hM : G2D4MaxNormalizer p) {t : StatedLieTag} {n e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2)
    (ht : (t = .G2 ∧ 5 ≤ p ^ e) ∨ t = .trialityD4)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    {c : (modelUniv t n p e Fact.out).K} (hc : IsUniqueInvolution R c) :
    Subgroup.normalizer (R : Set (modelUniv t n p e Fact.out).K) =
      Subgroup.centralizer ({c} : Set (modelUniv t n p e Fact.out).K) :=
  normalizer_eq_centralizer_of_isCoatom hc
    (CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2
      (by rcases ht with ⟨h, -⟩ | h; exacts [Or.inl h, Or.inr h]) n hadm.2.1)
    (hM t n e hadm hp2 ht R hR)

end Model

end CFSG.ClassicalInvolution.G2D4Models
