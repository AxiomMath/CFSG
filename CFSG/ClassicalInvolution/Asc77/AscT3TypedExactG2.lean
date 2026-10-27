module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactA
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactD4
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Twin

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models
open scoped commutatorElement

section Model

variable {p : ℕ} [Fact p.Prime]

theorem centralizer_le_normalizer_of_g2 {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ}
    (hp : p ≠ 2) (ht : t = .G2) (hadm : StatedLieAdmissible t n p e)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    {c : (modelUniv t n p e Fact.out).K} (hc : IsUniqueInvolution R c) :
    Subgroup.centralizer ({c} : Set (modelUniv t n p e Fact.out).K) ≤
      Subgroup.normalizer (R : Set (modelUniv t n p e Fact.out).K) := by
  subst ht
  have hn : n = 0 := hadm.2.2.1
  subst hn
  intro g hg
  have hg' : g * c = c * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hgc : g * c * g⁻¹ = c := by rw [hg']; group
  have h1 : IsUniqueInvolution (conjSub g R) c := by
    have := hc.conj g
    rwa [hgc] at this
  exact normalizer_iff_conjSub_eq.mpr (noTwins_g2 hp hadm.2.1 R hR c hc g h1)

theorem sup_centralizer_eq_top_of_g2 (hgen : G2CentralizersGenerate p)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ} (ht : t = .G2)
    (hadm : StatedLieAdmissible t n p e) (hp : p ≠ 2) (hq : 5 ≤ p ^ e)
    {u v : (modelUniv t n p e Fact.out).K} (hu : u * u = 1) (hv : v * v = 1) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huv : u ≠ v) (hcomm : u * v = v * u) :
    Subgroup.centralizer ({u} : Set (modelUniv t n p e Fact.out).K) ⊔
      Subgroup.centralizer ({v} : Set (modelUniv t n p e Fact.out).K) = ⊤ := by
  subst ht
  have hn : n = 0 := hadm.2.2.1
  subst hn
  exact hgen e hadm hp hq u v hu hv hu1 hv1 huv hcomm

end Model

section Stabilizer

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}
  {z j a : X}

theorem QuotViol.mem_of_invariant_g2 (hgen : G2CentralizersGenerate p) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ) {i : Fin D.card}
    (hG2 : D.tag i = .G2) {R S : Subgroup (D.model i).K} (hR : R ∈ D.cls i)
    (h : QuotViol Φ (R.map (D.hom i)) (S.map (D.hom i)) z j a) {C : Set (Subgroup X)}
    (hnorm : ∀ M ∈ C, ∀ x : X, conjSub x M = M → x ∈ conjStab C)
    (htwin : ∀ M ∈ C, ∀ M' ∈ twinSet Φ M, M' ≠ M → M' ∈ C)
    (hKC : R.map (D.hom i) ∈ C) (hJC : S.map (D.hom i) ∈ C) {R' : Subgroup (D.model i).K}
    (hR' : R' ∈ D.cls i) : R'.map (D.hom i) ∈ C := by
  set ψ := D.hom i with hψ
  have hi : D.tag i = .G2 ∨ D.tag i = .trialityD4 := Or.inl hG2
  have hef : D.exp i = f := by
    rcases D.exp_eq i with h' | ⟨h', -⟩
    · exact h'
    · exact absurd (hG2.symm.trans h') (by decide)
  have hq' : 5 ≤ p ^ D.exp i := by rw [hef]; exact hq
  have hinj : Function.Injective ψ := hom_injective_of_g2d4 hp D hi
  set Sg : Subgroup (D.model i).K := (conjStab C).comap ψ with hSg
  have hN : Subgroup.normalizer (R : Set (D.model i).K) ≤ Sg := by
    intro g hg
    refine hnorm _ hKC _ ?_
    rw [← AscQuot.map_conjSub, mem_normalizer_iff_conjSub_eq.mp hg]
  obtain ⟨c, hcz, hc⟩ := isUniqueInvolution_of_map hinj h.hz
  have hrange : R.map ψ ⊔ S.map ψ ≤ ψ.range :=
    sup_le (Subgroup.map_le_range _ _) (Subgroup.map_le_range _ _)
  obtain ⟨a₀, ha₀⟩ := hrange (mem_sup_of_mem_pairNormalizers h.ha)
  have haC : a ∈ conjStab C := by
    have : pairNormalizers (R.map ψ) (S.map ψ) z j ≤ conjStab C := by
      unfold pairNormalizers
      refine sup_le (inf_le_left.trans ?_) (inf_le_left.trans ?_)
      · intro x hx
        exact hnorm _ hKC x (conjSub_eq_self_of_mem hx)
      · intro x hx
        exact hnorm _ hJC x (conjSub_eq_self_of_mem hx)
    exact this h.ha
  have ha₀S : a₀ ∈ Sg := by
    show ψ a₀ ∈ conjStab C
    rw [ha₀]
    exact haC
  have hVn : pairNormalizers (R.map ψ) (S.map ψ) z j ≤
      Subgroup.normalizer ((Subgroup.closure {z, j} : Subgroup X) : Set X) :=
    sup_le inf_le_right inf_le_right
  have haV : a * z * a⁻¹ ∈ (Subgroup.closure {z, j} : Subgroup X) :=
    (Subgroup.mem_normalizer_iff.mp (hVn h.ha) z).mp (Subgroup.subset_closure (by simp))
  have hVc : (Subgroup.closure {z, j} : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h.comm.symm
  have hazc : a * z * a⁻¹ * z = z * (a * z * a⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hVc haV)
  have haz : a * z * a⁻¹ ≠ z := by
    intro h2
    have h3 : a * z * a⁻¹ = a * j * a⁻¹ := h2.trans h.haj.symm
    exact h.ne (mul_left_cancel (mul_right_cancel h3))
  have hc'z : ψ (a₀ * c * a₀⁻¹) = a * z * a⁻¹ := by
    rw [map_mul, map_mul, map_inv, hcz, ha₀]
  have hc'sq : a₀ * c * a₀⁻¹ * (a₀ * c * a₀⁻¹) = 1 := by
    calc a₀ * c * a₀⁻¹ * (a₀ * c * a₀⁻¹) = a₀ * (c * c) * a₀⁻¹ := by group
      _ = 1 := by rw [hc.sq]; group
  have hc'1 : a₀ * c * a₀⁻¹ ≠ 1 := by
    intro h1
    apply hc.ne_one
    calc c = a₀⁻¹ * (a₀ * c * a₀⁻¹) * a₀ := by group
      _ = 1 := by rw [h1]; group
  have hcc' : c ≠ a₀ * c * a₀⁻¹ := by
    intro e
    apply haz
    rw [← hc'z, ← e, hcz]
  have hcomm : c * (a₀ * c * a₀⁻¹) = a₀ * c * a₀⁻¹ * c := by
    apply hinj
    have h1 : ψ (c * (a₀ * c * a₀⁻¹)) = z * (a * z * a⁻¹) := by rw [map_mul, hc'z, hcz]
    have h2 : ψ (a₀ * c * a₀⁻¹ * c) = a * z * a⁻¹ * z := by rw [map_mul, hc'z, hcz]
    rw [h1, h2]
    exact hazc.symm
  have hCS : Subgroup.centralizer ({c} : Set (D.model i).K) ≤ Sg :=
    (centralizer_le_normalizer_of_g2 hp hG2 (D.admissible i) hR.1 hc).trans hN
  have hCS' : Subgroup.centralizer ({a₀ * c * a₀⁻¹} : Set (D.model i).K) ≤ Sg := by
    intro x hx
    have hx' : x * (a₀ * c * a₀⁻¹) = a₀ * c * a₀⁻¹ * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    have hy : a₀⁻¹ * x * a₀ ∈ Subgroup.centralizer ({c} : Set (D.model i).K) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc a₀⁻¹ * x * a₀ * c = a₀⁻¹ * (x * (a₀ * c * a₀⁻¹)) * a₀ := by group
        _ = a₀⁻¹ * (a₀ * c * a₀⁻¹ * x) * a₀ := by rw [hx']
        _ = c * (a₀⁻¹ * x * a₀) := by group
    have := Sg.mul_mem (Sg.mul_mem ha₀S (hCS hy)) (Sg.inv_mem ha₀S)
    have e : a₀ * (a₀⁻¹ * x * a₀) * a₀⁻¹ = x := by group
    rwa [e] at this
  have hSgtop : Sg = ⊤ := by
    have h1 := sup_centralizer_eq_top_of_g2 hgen hG2 (D.admissible i) hp hq' hc.sq hc'sq
      hc.ne_one hc'1 hcc' hcomm
    rw [eq_top_iff, ← h1]
    exact sup_le hCS hCS'
  have hall : ∀ g : (D.model i).K, ψ g ∈ conjStab C := fun g => by
    have : g ∈ Sg := hSgtop ▸ Subgroup.mem_top g
    exact this
  have hK'Φ : R'.map ψ ∈ Φ := hR'.2
  obtain ⟨z', hz'⟩ := hΦ.exists_uniqueInvolution hp hq hK'Φ
  obtain ⟨c₂, -, hc₂⟩ := isUniqueInvolution_of_map hinj hz'
  obtain ⟨g, hg⟩ := Balance.Bootstrap.twoClassInvolutionsConj p (D.tag i) (D.rank i) (D.exp i) hp
    hi (D.admissible i) R hR.1 R' hR'.1 c hc.mem c₂ hc₂.mem hc.sq hc₂.sq hc.ne_one hc₂.ne_one
    (fun y hy => hc.commute_of_mem hy) (fun y hy => hc₂.commute_of_mem hy)
  have hc'' : IsUniqueInvolution (conjSub g R) c₂ := by
    have := hc.conj g
    rwa [hg] at this
  have hK''C : (conjSub g R).map ψ ∈ C := by
    rw [AscQuot.map_conjSub]
    exact (hall g _).mpr hKC
  by_cases hRR : R' = conjSub g R
  · rw [hRR]
    exact hK''C
  · have hne : R'.map ψ ≠ (conjSub g R).map ψ := fun e => hRR (Subgroup.map_injective hinj e)
    exact htwin _ hK''C _ ⟨hK'Φ, ψ c₂, isUniqueInvolution_map_of_inj hinj hc'',
      isUniqueInvolution_map_of_inj hinj hc₂⟩ hne

end Stabilizer

section Consequences

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}
  {z j a : X} (hgen : G2CentralizersGenerate p) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
  (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ) {i : Fin D.card} (hG2 : D.tag i = .G2)

include hgen hp hq hΦ hG2

theorem QuotViol.mem_aStar_of_g2 {R S : Subgroup (D.model i).K} (hR : R ∈ D.cls i)
    (h : QuotViol Φ (R.map (D.hom i)) (S.map (D.hom i)) z j a)
    (hJ : S.map (D.hom i) ∈ aStar Φ (R.map (D.hom i))) {R' : Subgroup (D.model i).K}
    (hR' : R' ∈ D.cls i) : R'.map (D.hom i) ∈ aStar Φ (R.map (D.hom i)) :=
  h.mem_of_invariant_g2 hgen hp hq hΦ D hG2 hR
    (fun _ hM _ hx => mem_conjStab_aStar hΦ.conjInvariant h.mem_left hM hx)
    (fun _ hM _ ht hne => hM.tail ⟨ht.1, Or.inr (Or.inr ⟨ht, hne⟩)⟩)
    Relation.ReflTransGen.refl hJ hR'

theorem aStar_eq_compMembers {R S : Subgroup (D.model i).K} (hR : R ∈ D.cls i)
    (h : QuotViol Φ (R.map (D.hom i)) (S.map (D.hom i)) z j a)
    (hJ : S.map (D.hom i) ∈ aStar Φ (R.map (D.hom i))) :
    aStar Φ (R.map (D.hom i)) = compMembers D i := by
  ext M
  constructor
  · exact aStar_subset_compMembers hp hq hΦ D (Or.inl hG2) ⟨R, hR, rfl⟩
  · rintro ⟨R', hR', rfl⟩
    exact h.mem_aStar_of_g2 hgen hp hq hΦ D hG2 hR hJ hR'

theorem QuotViol.mem_dstarComp_of_g2 {R S : Subgroup (D.model i).K} (hR : R ∈ D.cls i)
    (h : QuotViol Φ (R.map (D.hom i)) (S.map (D.hom i)) z j a) {R' : Subgroup (D.model i).K}
    (hR' : R' ∈ D.cls i) : R'.map (D.hom i) ∈ dstarComp Φ (R.map (D.hom i)) :=
  h.mem_of_invariant_g2 hgen hp hq hΦ D hG2 hR
    (fun _ hM _ hx => mem_conjStab_dstarComp hΦ.conjInvariant h.mem_left hM hx)
    (fun _ hM _ ht hne => by
      obtain ⟨hM'Φ, zz, hzM, hzM'⟩ := ht
      exact hM.tail ⟨hM'Φ, Or.inl (omegaNbr_subset_omegaStarNbr hp hΦ _
        (twin_mem_omegaNbr hΦ (mem_dstarComp_symm h.mem_left hM).1 hM'Φ hne hzM hzM'))⟩)
    Relation.ReflTransGen.refl (Relation.ReflTransGen.single ⟨h.mem_right, Or.inl h.star⟩) hR'

end Consequences

theorem QuotViol.dstarConnected_of_split {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime]
    {Φ : Set (Subgroup X)} {z j a : X} (hgen : G2CentralizersGenerate p)
    (hD4 : D4NormalizerMax p) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ)
    (D : OmegaLie p f Φ) {K J : Subgroup X} (h : QuotViol Φ K J z j a) : DStarConnected Φ := by
  obtain ⟨i, R, S, hR, hS, rfl, rfl⟩ := h.exists_components D
  have hG2 : D.tag i = .G2 := by
    by_contra hne
    by_cases hD : D.tag i = .trialityD4
    · exact h.false_of_trialityD4 hD4 hp hq hΦ D hD hR hS
    · exact h.false_of_classical hp hq hΦ D hne hD hR hS
  refine dstarConnected_of_pivot h.mem_left fun M hMΦ => ?_
  obtain ⟨i', R', hR'f, hMR'⟩ := D.fundamental M hMΦ
  by_cases hii : i' = i
  · subst hii
    have hR'cls : R' ∈ D.cls i' := ⟨hR'f, hMR' ▸ hMΦ⟩
    rw [hMR']
    exact h.mem_dstarComp_of_g2 hgen hp hq hΦ D hG2 hR hR'cls
  · refine mem_dstarComp_of_commutes hp hΦ hMΦ ?_
    rw [hMR']
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact D.commute i' i hii x y

end CFSG.ClassicalInvolution.Asc77.T3Typed
