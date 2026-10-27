module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedClass
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Max
public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsTriality

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models
open scoped commutatorElement

section Stab

variable {X : Type} [Group X]

@[expose] def conjStab (C : Set (Subgroup X)) : Subgroup X where
  carrier := {g | ∀ M, conjSub g M ∈ C ↔ M ∈ C}
  one_mem' := fun M => by simp
  mul_mem' := by
    intro g g' hg hg' M
    rw [conjSub_mul]
    exact (hg _).trans (hg' M)
  inv_mem' := by
    intro g hg M
    have := hg (conjSub g⁻¹ M)
    rw [conjSub_conjSub_inv] at this
    exact this.symm

theorem mem_conjStab_iff {C : Set (Subgroup X)} {g : X} :
    g ∈ conjStab C ↔ ∀ M, conjSub g M ∈ C ↔ M ∈ C := Iff.rfl

variable {Φ : Set (Subgroup X)}

theorem mem_conjStab_dstarComp (hΦ : ConjInvariant Φ) {K J : Subgroup X} (hK : K ∈ Φ)
    (hJ : J ∈ dstarComp Φ K) {x : X} (hx : conjSub x J = J) : x ∈ conjStab (dstarComp Φ K) := by
  obtain ⟨-, hKJ⟩ := mem_dstarComp_symm hK hJ
  have fwd : ∀ y : X, conjSub y J = J → ∀ M, M ∈ dstarComp Φ K →
      conjSub y M ∈ dstarComp Φ K := by
    intro y hy M hM
    have h2 := dstarComp_conj hΦ (hKJ.trans hM) y
    rw [hy] at h2
    exact hJ.trans h2
  have hx' : conjSub x⁻¹ J = J := by
    calc conjSub x⁻¹ J = conjSub x⁻¹ (conjSub x J) := by rw [hx]
      _ = J := conjSub_inv_conjSub x J
  intro M
  constructor
  · intro hM
    have := fwd x⁻¹ hx' _ hM
    rwa [conjSub_inv_conjSub] at this
  · exact fwd x hx M

end Stab

section Involution

variable {H G : Type} [Group H] [Group G]

theorem isUniqueInvolution_of_map {ψ : H →* G} (hinj : Function.Injective ψ) {R : Subgroup H}
    {z : G} (hz : IsUniqueInvolution (R.map ψ) z) :
    ∃ c : H, ψ c = z ∧ IsUniqueInvolution R c := by
  obtain ⟨c, hcR, hcz⟩ := hz.mem
  refine ⟨c, hcz, hcR, fun h => hz.ne_one ?_, hinj ?_, fun y hy hy2 => ?_⟩
  · rw [← hcz, h, map_one]
  · rw [map_mul, hcz, hz.sq, map_one]
  · have h1 : ψ y * ψ y = 1 := by rw [← map_mul, hy2, map_one]
    rcases hz.unique (ψ y) (Subgroup.mem_map_of_mem ψ hy) h1 with h2 | h2
    · left
      exact hinj (h2.trans (map_one ψ).symm)
    · right
      exact hinj (h2.trans hcz.symm)

theorem isUniqueInvolution_map_of_inj {ψ : H →* G} (hinj : Function.Injective ψ) {R : Subgroup H}
    {c : H} (hc : IsUniqueInvolution R c) : IsUniqueInvolution (R.map ψ) (ψ c) where
  mem := Subgroup.mem_map_of_mem ψ hc.mem
  ne_one := fun h => hc.ne_one (hinj (h.trans (map_one ψ).symm))
  sq := by rw [← map_mul, hc.sq, map_one]
  unique := by
    rintro _ ⟨r, hr, rfl⟩ hy
    have h1 : r * r = 1 := hinj (by rw [map_mul, hy, map_one])
    rcases hc.unique r hr h1 with h2 | h2
    · left
      rw [h2, map_one]
    · right
      rw [h2]

end Involution

section Component

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}
  {z j a : X}

theorem QuotViol.mem_dstarComp_of_g2d4 (hM : G2D4MaxNormalizer p) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ) {i : Fin D.card}
    (hi : D.tag i = .G2 ∨ D.tag i = .trialityD4) {R S : Subgroup (D.model i).K}
    (hR : R ∈ D.cls i) (h : QuotViol Φ (R.map (D.hom i)) (S.map (D.hom i)) z j a)
    {R' : Subgroup (D.model i).K} (hR' : R' ∈ D.cls i) :
    R'.map (D.hom i) ∈ dstarComp Φ (R.map (D.hom i)) := by
  set ψ := D.hom i with hψ
  have he : 1 ≤ D.exp i := (D.admissible i).2.1
  have hker := D.ker_le_center i
  have hinj : Function.Injective ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp hi (D.rank i) he ψ hker
  have hcoatom : IsCoatom (Subgroup.normalizer (R : Set (D.model i).K)) := by
    refine hM (D.tag i) (D.rank i) (D.exp i) (D.admissible i) hp ?_ R hR.1
    rcases hi with h' | h'
    · refine Or.inl ⟨h', ?_⟩
      rcases D.exp_eq i with h'' | ⟨h'', -⟩
      · rw [h'']
        exact hq
      · exact absurd (h'.symm.trans h'') (by decide)
    · exact Or.inr h'
  set C : Set (Subgroup X) := dstarComp Φ (R.map ψ) with hC
  have hKC : R.map ψ ∈ C := Relation.ReflTransGen.refl
  have hJC : S.map ψ ∈ C := Relation.ReflTransGen.single ⟨h.mem_right, Or.inl h.star⟩
  set Sg : Subgroup (D.model i).K := (conjStab C).comap ψ with hSg
  have hN : Subgroup.normalizer (R : Set (D.model i).K) ≤ Sg := by
    intro g hg
    refine mem_conjStab_dstarComp hΦ.conjInvariant h.mem_left hKC ?_
    rw [← AscQuot.map_conjSub, mem_normalizer_iff_conjSub_eq.mp hg]
  have hrange : R.map ψ ⊔ S.map ψ ≤ ψ.range :=
    sup_le (Subgroup.map_le_range _ _) (Subgroup.map_le_range _ _)
  obtain ⟨a₀, ha₀⟩ := hrange (mem_sup_of_mem_pairNormalizers h.ha)
  have haC : a ∈ conjStab C := by
    have : pairNormalizers (R.map ψ) (S.map ψ) z j ≤ conjStab C := by
      unfold pairNormalizers
      refine sup_le (inf_le_left.trans ?_) (inf_le_left.trans ?_)
      · intro x hx
        exact mem_conjStab_dstarComp hΦ.conjInvariant h.mem_left hKC (conjSub_eq_self_of_mem hx)
      · intro x hx
        exact mem_conjStab_dstarComp hΦ.conjInvariant h.mem_left hJC (conjSub_eq_self_of_mem hx)
    exact this h.ha
  have ha₀S : a₀ ∈ Sg := by
    show ψ a₀ ∈ conjStab C
    rw [ha₀]
    exact haC
  have ha₀N : a₀ ∉ Subgroup.normalizer (R : Set (D.model i).K) := by
    intro hn
    have hconj : conjSub a (R.map ψ) = R.map ψ := by
      rw [← ha₀, ← AscQuot.map_conjSub, mem_normalizer_iff_conjSub_eq.mp hn]
    have h1 : a * z * a⁻¹ = z := h.hz.conj_eq hconj
    have h3 : a * z * a⁻¹ = a * j * a⁻¹ := h1.trans h.haj.symm
    exact h.ne (mul_left_cancel (mul_right_cancel h3))
  have hlt : Subgroup.normalizer (R : Set (D.model i).K) < Sg :=
    lt_of_le_of_ne hN fun e => ha₀N (e ▸ ha₀S)
  have hSgtop : Sg = ⊤ := hcoatom.2 Sg hlt
  have hall : ∀ g : (D.model i).K, ψ g ∈ conjStab C := fun g => by
    have : g ∈ Sg := hSgtop ▸ Subgroup.mem_top g
    exact this
  have hK'Φ : R'.map ψ ∈ Φ := hR'.2
  obtain ⟨z', hz'⟩ := hΦ.exists_uniqueInvolution hp hq hK'Φ
  obtain ⟨c', -, hc'⟩ := isUniqueInvolution_of_map hinj hz'
  obtain ⟨c₀, -, hc₀⟩ := isUniqueInvolution_of_map hinj h.hz
  obtain ⟨g, hg⟩ := Balance.Bootstrap.twoClassInvolutionsConj p (D.tag i) (D.rank i) (D.exp i) hp hi
    (D.admissible i) R hR.1 R' hR'.1 c₀ hc₀.mem c' hc'.mem hc₀.sq hc'.sq hc₀.ne_one hc'.ne_one
    (fun y hy => hc₀.commute_of_mem hy) (fun y hy => hc'.commute_of_mem hy)
  set R'' : Subgroup (D.model i).K := conjSub g R with hR''
  have hR''cls : R'' ∈ D.cls i := D.cls_conj hΦ.conjInvariant i hR g
  have hc'' : IsUniqueInvolution R'' c' := by
    have := hc₀.conj g
    rwa [hg] at this
  have hK''C : R''.map ψ ∈ C := by
    rw [hR'', AscQuot.map_conjSub]
    exact (hall g _).mpr hKC
  by_cases hRR : R' = R''
  · rw [hRR]
    exact hK''C
  · have hne : R'.map ψ ≠ R''.map ψ := fun e => hRR (Subgroup.map_injective hinj e)
    have hmem : R'.map ψ ∈ omegaNbr Φ (R''.map ψ) :=
      twin_mem_omegaNbr hΦ hR''cls.2 hK'Φ hne (isUniqueInvolution_map_of_inj hinj hc'')
        (isUniqueInvolution_map_of_inj hinj hc')
    exact hK''C.tail ⟨hK'Φ, Or.inl (omegaNbr_subset_omegaStarNbr hp hΦ _ hmem)⟩

theorem mem_dstarComp_of_commutes (hp : p ≠ 2) (hΦ : HypOmegaMod p f Φ) {K M : Subgroup X}
    (hM : M ∈ Φ) (hc : Commutes M K) : M ∈ dstarComp Φ K := by
  by_cases hMK : M = K
  · subst hMK
    exact Relation.ReflTransGen.refl
  · have hcomm : ⁅M, K⁆ ≤ K := Subgroup.commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc x hx y hy)]
      exact K.one_mem
    have hMN : M ≤ Subgroup.normalizer (K : Set X) := le_normalizer_of_commutator_le hcomm
    obtain ⟨R, hR, hRM, -⟩ := exists_mem_RSet_ge hM (isPGroup_two_bot' (G := X)) bot_le
    have hnb : M ∈ omegaNbr Φ K := ⟨hM, hMK, R, hR, hRM.1, hRM.1.trans hMN⟩
    exact Relation.ReflTransGen.single ⟨hM, Or.inl (omegaNbr_subset_omegaStarNbr hp hΦ K hnb)⟩

theorem QuotViol.dstarConnected (hM : G2D4MaxNormalizer p) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ) {K J : Subgroup X}
    (h : QuotViol Φ K J z j a) : DStarConnected Φ := by
  obtain ⟨i, R, S, hR, hS, rfl, rfl⟩ := h.exists_components D
  by_cases hi : D.tag i = .G2 ∨ D.tag i = .trialityD4
  · refine dstarConnected_of_pivot h.mem_left fun M hMΦ => ?_
    obtain ⟨i', R', hR'f, hMR'⟩ := D.fundamental M hMΦ
    by_cases hii : i' = i
    · subst hii
      have hR'cls : R' ∈ D.cls i' := ⟨hR'f, hMR' ▸ hMΦ⟩
      rw [hMR']
      exact h.mem_dstarComp_of_g2d4 hM hp hq hΦ D hi hR hR'cls
    · refine mem_dstarComp_of_commutes hp hΦ hMΦ ?_
      rw [hMR']
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact D.commute i' i hii x y
  · exact (h.false_of_classical hp hq hΦ D (fun e => hi (Or.inl e)) (fun e => hi (Or.inr e))
      hR hS).elim

end Component

end CFSG.ClassicalInvolution.Asc77.T3Typed
