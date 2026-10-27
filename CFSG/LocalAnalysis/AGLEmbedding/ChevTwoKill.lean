module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

theorem three_le_pRank_of_weakCore_eq_top {Y : Type*} [Group Y] [Finite Y] [Nontrivial Y]
    {p : ℕ} (hp : p.Prime) {P : Subgroup Y} (h : GLBWeakCore p P = ⊤) : 3 ≤ Open.pRank p P := by
  by_contra hlt
  have hbot : GLBWeakCore p P ≤ ⊥ := by
    rw [PreuniquenessRankFour.Helpers.weakCore_le_iff]
    intro Q hQP _ h3
    have := h3.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp (sup_le hQP inf_le_left))
    omega
  rw [h] at hbot
  exact bot_ne_top (le_bot_iff.mp hbot).symm

section Kill

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {X₀ : Subgroup X}

theorem false_of_le_of_three_le_pRank (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    [K.Normal] (hK : K ≤ X₀) (h3 : 3 ≤ Open.pRank p K) : False := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ X₀ := by
    by_contra hall
    push Not at hall
    exact h.ne_top (eq_top_iff.mpr fun x _ => hall x)
  have hKx : K ≤ X₀ ⊓ GLBConj x X₀ := by
    refine le_inf hK fun k hk => ⟨x * k * x⁻¹, hK (Subgroup.Normal.conj_mem ‹_› k hk x), ?_⟩
    simp [mul_assoc]
  have h2 := (PreuniquenessRankFour.Helpers.pRank_mono p h.prime hKx).trans
    (h.pRank_inf_conj_le x hx)
  omega

theorem false_of_le_of_normal_sup [Fact p.Prime] (h : ReducedNongeneration p X R X₀)
    {K : Subgroup X} (hK : K ≤ X₀) (hN : (K ⊔ (R : Subgroup X)).Normal) : False := by
  have hp : p.Prime := Fact.out
  have hNR : Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ X₀ :=
    (PreuniquenessRankFour.Helpers.normalizer_le_weakCore_of_rank p hp _
      h.three_le_pRank).trans h.weakCore_le
  have hRX : (R : Subgroup X) ≤ X₀ := Subgroup.le_normalizer.trans hNR
  have hinf : (R : Subgroup X) ⊓ (K ⊔ (R : Subgroup X)) = R := inf_eq_left.mpr le_sup_right
  have := hN
  exact not_le_of_normalizer_inf_le R (N := K ⊔ (R : Subgroup X)) (by rw [hinf]; exact hNR)
    h.ne_top (sup_le hK hRX)

end Kill

section Normal

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem normal_sup_ker_of_le_normal {L : Type*} [Group L] (ψ : X →* L) (R : Sylow p X)
    {S : Subgroup L} [S.Normal] (hS : IsPGroup p S) (hRS : (R : Subgroup X).map ψ ≤ S) :
    ((R : Subgroup X) ⊔ ψ.ker).Normal := by
  set f := ψ.rangeRestrict
  have hf : Function.Surjective f := ψ.rangeRestrict_surjective
  set B : Subgroup ψ.range := S.comap ψ.range.subtype
  have hB : IsPGroup p B := hS.comap_of_injective _ ψ.range.subtype_injective
  have : B.Normal := Subgroup.Normal.comap ‹_› _
  have hBR : B ≤ (R.mapSurjective hf : Subgroup ψ.range) := hB.le_sylow_of_normal _
  have hRB : (R.mapSurjective hf : Subgroup ψ.range) ≤ B := by
    rw [Sylow.coe_mapSurjective]
    rintro _ ⟨r, hr, rfl⟩
    exact hRS ⟨r, hr, rfl⟩
  have hcomap : (R : Subgroup X) ⊔ ψ.ker = (R.mapSurjective hf : Subgroup ψ.range).comap f := by
    rw [Sylow.coe_mapSurjective, Subgroup.comap_map_eq, MonoidHom.ker_rangeRestrict]
  rw [hcomap, le_antisymm hRB hBR]
  exact Subgroup.Normal.comap ‹_› f

theorem normal_sup_of_outer {L : Type*} [Group L] (K : Subgroup X) [K.Normal]
    [Group.IsPerfect K] (e : K ⧸ Subgroup.center K ≃* L) (R : Sylow p X)
    (hCR : Subgroup.centralizer (K : Set X) ≤ R)
    (hOut : ∀ S : Sylow p (Outer L), (S : Subgroup (Outer L)).Normal) :
    (K ⊔ (R : Subgroup X)).Normal := by
  let ψ : X →* Outer L := (equivalence e).toMonoidHom.comp ((centerQuotientOuterHom K).comp
    ((QuotientGroup.mk' (inner K)).comp MulAut.conjNormal))
  have hψ : ∀ x : X, ψ x = equivalence e (centerQuotientOuterHom K
      (QuotientGroup.mk' (inner K) (MulAut.conjNormal x))) := fun _ => rfl
  have hKker : K ≤ ψ.ker := by
    intro k hk
    have h1 : (MulAut.conjNormal k : MulAut K) ∈ inner K :=
      ⟨⟨k, hk⟩, MulEquiv.ext fun y => Subtype.ext (by simp [MulAut.conjNormal_apply])⟩
    have h2 : QuotientGroup.mk' (inner K) (MulAut.conjNormal k) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h1
    rw [MonoidHom.mem_ker, hψ, h2, map_one, map_one]
  have hker : ψ.ker ≤ K ⊔ Subgroup.centralizer (K : Set X) := by
    intro x hx
    have h1 : QuotientGroup.mk' (inner K) (MulAut.conjNormal x) = 1 := by
      apply centerQuotient_outer_injective K
      apply (equivalence e).injective
      rw [map_one, map_one, ← hψ]
      exact hx
    obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff _).mp h1
    have hc : (k : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := congrArg (fun f : MulAut K => ((f ⟨y, hy⟩ : K) : X)) hk
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h
      calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * (k * y * (k : X)⁻¹) * x := by group
        _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h]
        _ = (k : X)⁻¹ * x * y := by group
    have e' : x = (k : X) * ((k : X)⁻¹ * x) := by group
    rw [e']
    exact Subgroup.mul_mem_sup k.2 hc
  obtain ⟨S, hS⟩ := (R.isPGroup'.map ψ).exists_le_sylow
  have := hOut S
  have heq : K ⊔ (R : Subgroup X) = (R : Subgroup X) ⊔ ψ.ker :=
    le_antisymm (sup_le (hKker.trans le_sup_right) le_sup_left)
      (sup_le le_sup_right (hker.trans (sup_le le_sup_left (hCR.trans le_sup_right))))
  rw [heq]
  exact normal_sup_ker_of_le_normal ψ R S.isPGroup' hS

end Normal

namespace D1ComponentConfig

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Sylow p G}
  {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem false_of_weakCore_eq_top (hcfg : D1ComponentConfig p P M H R Rbar)
    (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (htop : ∀ T : Sylow p K, GLBWeakCore p (T : Subgroup K) = ⊤) : False := by
  have hp : p.Prime := Fact.out
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  obtain ⟨T₀, hT₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have hle := le_of_weakCore_eq_top hcfg.red T₀ hT₀ (htop T₀)
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have : Nontrivial K := (QuotientGroup.mk'_surjective (Subgroup.center K)).nontrivial
  have h3 := three_le_pRank_of_weakCore_eq_top hp (htop T₀)
  rw [← PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp K.subtype
    K.subtype_injective, hT₀] at h3
  exact false_of_le_of_three_le_pRank hcfg.red hle
    (h3.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp inf_le_right))

theorem false_of_le_weakCore {T : Type*} [Group T] (hcfg : D1ComponentConfig p P M H R Rbar)
    (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    (e : K ⧸ Subgroup.center K ≃* T)
    (hOut : ∀ S : Sylow p (Outer T), (S : Subgroup (Outer T)).Normal)
    (hW : K ≤ GLBWeakCore p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p))) : False := by
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hCR := IsPGroup.le_sylow_of_normal (hcfg.isPGroup_centralizer hK huniq hcent) Rbar
  exact false_of_le_of_normal_sup hcfg.red (hW.trans hcfg.red.weakCore_le)
    (normal_sup_of_outer K e Rbar hCR hOut)

end D1ComponentConfig

end CFSG.AGLEmbedding
