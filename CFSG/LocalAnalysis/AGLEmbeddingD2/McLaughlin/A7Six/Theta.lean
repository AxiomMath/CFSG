module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7Gen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7Nat

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Cooperstein.Coordinator
open Equiv Equiv.Perm

variable {X : Type} [Group X]

abbrev nL (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Subgroup X :=
  (Subgroup.normalizer (L : Set (X ⧸ gnC T))).comap (QuotientGroup.mk' (gnC T))

abbrev lT (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Subgroup X :=
  L.comap (QuotientGroup.mk' (gnC T))

abbrev nV (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Subgroup X := ⁅gnV T, lT T L⁆

abbrev nLs (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Subgroup (X ⧸ gnC T) :=
  Subgroup.normalizer (L : Set (X ⧸ gnC T))

@[expose] def πN (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : ↥(nL T L) →* ↥(nLs T L) :=
  ((QuotientGroup.mk' (gnC T)).comp (nL T L).subtype).codRestrict (nLs T L) (fun g => g.2)

@[simp] theorem coe_πN (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) (g : ↥(nL T L)) :
    ((πN T L g : ↥(nLs T L)) : X ⧸ gnC T) = QuotientGroup.mk' (gnC T) (g : X) := rfl

theorem exists_thetaS (T : Subgroup X) (L : Subgroup (X ⧸ gnC T))
    (eL : ↥L ≃* alternatingGroup (Fin 7)) :
    ∃ θ : ↥(nLs T L) →* Perm (Fin 7),
      (∀ (y : ↥(nLs T L)) (l l' : ↥L), (l' : X ⧸ gnC T) = (y : X ⧸ gnC T) * l * (y : X ⧸ gnC T)⁻¹ →
          (eL l' : Perm (Fin 7)) = θ y * eL l * (θ y)⁻¹) ∧
      (∀ (y : ↥(nLs T L)) (l : ↥L), (l : X ⧸ gnC T) = y → θ y = eL l) ∧
      (∀ y : ↥(nLs T L), θ y = 1 ↔ ∀ l ∈ L, (y : X ⧸ gnC T) * l * (y : X ⧸ gnC T)⁻¹ = l) := by
  set N : Subgroup (X ⧸ gnC T) := nLs T L
  set Ls : Subgroup ↥N := L.subgroupOf N
  let φL : ↥Ls ≃* alternatingGroup (Fin 7) :=
    (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).trans eL
  obtain ⟨e, he1, he2, he3, he4⟩ := FiveThreeAlt.exists_conj_embedding7 Ls φL
  have hφL : ∀ x : ↥Ls, (φL x : alternatingGroup (Fin 7)) =
      eL ⟨((x : ↥N) : X ⧸ gnC T), x.2⟩ := fun _ => rfl
  refine ⟨e, fun y l l' hl' => ?_, fun y l hl => ?_, fun y => ?_⟩
  · have hlN : (l : X ⧸ gnC T) ∈ N := Subgroup.le_normalizer l.2
    let x : ↥Ls := ⟨⟨l, hlN⟩, l.2⟩
    have h := he2 y x
    have hconj : MulAut.conjNormal y x = ⟨⟨l', Subgroup.le_normalizer l'.2⟩, l'.2⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hl']
    rw [hconj] at h
    simpa [hφL] using h
  · have hgN : y ∈ Ls := by
      show (y : X ⧸ gnC T) ∈ L
      rw [← hl]
      exact l.2
    have h := he1 ⟨y, hgN⟩
    rw [h, hφL]
    congr 2
    exact Subtype.ext (by rw [hl])
  · constructor
    · intro h l hl
      have h1 := he3 y h ⟨⟨l, Subgroup.le_normalizer hl⟩, hl⟩
      have h2 := congrArg (fun z : ↥N => (z : X ⧸ gnC T)) h1
      simpa using h2
    · intro h
      refine he4 y fun x => ?_
      apply Subtype.ext
      have := h ((x : ↥N) : X ⧸ gnC T) x.2
      simpa using this

theorem altAct_faithful {σ : Perm (Fin 7)} (h : ∀ v : altHeart 7, altAct σ v = v) : σ = 1 := by
  classical
  have key : ∀ i j : Fin 7, i ≠ j → σ i = i ∨ σ i = j := by
    intro i j hij
    let x0 : Fin 7 → ZMod 2 := Pi.single i 1 + Pi.single j 1
    have hx0 : x0 ∈ evenWeight 7 := by
      show ∑ k, x0 k = 0
      simp only [x0, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
      simp only [Finset.mem_univ, ite_true]
      decide
    let x : evenWeight 7 := ⟨x0, hx0⟩
    have h1 := h (QuotientAddGroup.mk x)
    rw [altAct_mk] at h1
    have h2 : evenWeightPerm σ x = x := by
      have h3 := QuotientAddGroup.eq.1 h1
      rw [EightFive.evenWeightOnes_seven, AddSubgroup.mem_bot] at h3
      have h4 : -(evenWeightPerm σ x) + x = 0 := h3
      rw [neg_add_eq_zero] at h4
      exact h4
    have h5 := congrArg (fun y : evenWeight 7 => (y : Fin 7 → ZMod 2) (σ i)) h2
    simp only [evenWeightPerm_apply] at h5
    rw [show σ⁻¹ (σ i) = i from by simp] at h5
    have hxi : x0 i = 1 := by
      simp [x0, hij]
    have h6 : x0 (σ i) = 1 := by rw [← hxi]; exact h5.symm
    by_contra hne
    push Not at hne
    have : x0 (σ i) = 0 := by
      simp [x0, hne.1, hne.2]
    rw [this] at h6
    exact absurd h6 (by decide)
  refine Equiv.ext fun i => ?_
  rw [one_apply]
  obtain ⟨j, hj⟩ : ∃ j : Fin 7, j ≠ i := ⟨if i = 0 then 1 else 0, by split_ifs <;> omega⟩
  obtain ⟨k, hk, hkj⟩ : ∃ k : Fin 7, k ≠ i ∧ k ≠ j := by
    by_contra hcon
    push Not at hcon
    have : (Finset.univ : Finset (Fin 7)) ⊆ {i, j} := fun k _ => by
      by_cases hki : k = i
      · simp [hki]
      · simp [hcon k hki]
    have := Finset.card_le_card this
    rw [Finset.card_univ, Fintype.card_fin] at this
    have h2 := Finset.card_le_two (a := i) (b := j)
    omega
  rcases key i j hj.symm with h1 | h1
  · exact h1
  rcases key i k hk.symm with h2 | h2
  · exact h2
  exact absurd (h1.symm.trans h2) hkj.symm

structure SixCtx (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) where
  eL : ↥L ≃* alternatingGroup (Fin 7)
  θs : ↥(nLs T L) →* Perm (Fin 7)
  hθs : ∀ (y : ↥(nLs T L)) (l l' : ↥L), (l' : X ⧸ gnC T) = (y : X ⧸ gnC T) * l *
    (y : X ⧸ gnC T)⁻¹ → (eL l' : Perm (Fin 7)) = θs y * eL l * (θs y)⁻¹
  hθsL : ∀ (y : ↥(nLs T L)) (l : ↥L), (l : X ⧸ gnC T) = y → θs y = eL l
  hθs1 : ∀ y : ↥(nLs T L), θs y = 1 ↔ ∀ l ∈ L, (y : X ⧸ gnC T) * l * (y : X ⧸ gnC T)⁻¹ = l
  φ : ↥(nV T L) →* Multiplicative (altHeart 7)
  hφ : Function.Bijective φ
  hφe : ∀ (g : ↥(nL T L)) (u v : ↥(nV T L)), (v : X) = (g : X) * u * (g : X)⁻¹ →
    Multiplicative.toAdd (φ v) = altAct (θs (πN T L g)) (Multiplicative.toAdd (φ u))

@[expose] def SixCtx.θ {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)} (c : SixCtx T L) :
    ↥(nL T L) →* Perm (Fin 7) :=
  c.θs.comp (πN T L)

namespace SixCtx

variable {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)} (c : SixCtx T L)

theorem hθL (g : ↥(nL T L)) (l : ↥L) (h : (l : X ⧸ gnC T) = QuotientGroup.mk' (gnC T) (g : X)) :
    c.θ g = c.eL l :=
  c.hθsL _ l h

theorem hθ1 (g : ↥(nL T L)) : c.θ g = 1 ↔ ∀ l ∈ L, QuotientGroup.mk' (gnC T) (g : X) * l *
    (QuotientGroup.mk' (gnC T) (g : X))⁻¹ = l :=
  c.hθs1 _

theorem hφe' (g : ↥(nL T L)) (u v : ↥(nV T L)) (h : (v : X) = (g : X) * u * (g : X)⁻¹) :
    Multiplicative.toAdd (c.φ v) = altAct (c.θ g) (Multiplicative.toAdd (c.φ u)) :=
  c.hφe g u v h

theorem nL_le_normalizer_nV (hV : (gnV T).Normal) :
    nL T L ≤ Subgroup.normalizer (nV T L : Set X) := by
  intro g hg
  have hLn : g ∈ Subgroup.normalizer (lT T L : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hg' := Subgroup.mem_normalizer_iff.1 (Subgroup.mem_comap.1 hg)
      (QuotientGroup.mk' (gnC T) x)
    simp only [lT, Subgroup.mem_comap, map_mul, map_inv] at hg' ⊢
    exact hg'
  have hVn : g ∈ Subgroup.normalizer (gnV T : Set X) :=
    (Subgroup.normalizer_eq_top_iff.mpr hV).symm ▸ Subgroup.mem_top g
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hVn, Subgroup.mem_normalizer_iff_map_conj_eq.mp hLn]

theorem theta_eq_one_iff (hV : (gnV T).Normal) (g : ↥(nL T L)) :
    c.θ g = 1 ↔ ∀ u ∈ nV T L, (g : X) * u * (g : X)⁻¹ = u := by
  have hN := nL_le_normalizer_nV (L := L) hV g.2
  constructor
  · intro h u hu
    have hv : (g : X) * u * (g : X)⁻¹ ∈ nV T L := (Subgroup.mem_normalizer_iff.1 hN u).1 hu
    have h1 := c.hφe' g ⟨u, hu⟩ ⟨_, hv⟩ rfl
    rw [h, altAct_one] at h1
    have h2 : c.φ ⟨_, hv⟩ = c.φ ⟨u, hu⟩ := Multiplicative.toAdd.injective h1
    exact congrArg Subtype.val (c.hφ.1 h2)
  · intro h
    apply altAct_faithful
    intro v
    obtain ⟨u, hu⟩ := c.hφ.2 (Multiplicative.ofAdd v)
    have h1 := c.hφe' g u u (h u u.2).symm
    rw [hu] at h1
    simpa using h1.symm

end SixCtx

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
