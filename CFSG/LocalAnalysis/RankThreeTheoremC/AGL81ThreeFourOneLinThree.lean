module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoCriteria
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesLinThree
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.Milestones.ASVolI.F411.aL3Core
import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3
  CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

section Model

variable {F : Type} [Field F]

private def axisHeis : Subgroup (Heis F) where
  carrier := {x | x.a = 0}
  mul_mem' {x y} hx hy := by
    change (x * y).a = 0
    rw [Heis.mul_a, hx, hy, add_zero]
  one_mem' := Heis.one_a
  inv_mem' {x} hx := by
    change (x⁻¹).a = 0
    rw [Heis.inv_a, hx, neg_zero]

private def axisPlane : Subgroup (projectiveSL 3 F) := (axisHeis (F := F)).map theta

private theorem mem_axisPlane {y : projectiveSL 3 F} :
    y ∈ axisPlane (F := F) ↔ ∃ x : Heis F, x.a = 0 ∧ theta x = y :=
  mem_map

private theorem theta_mem_axisPlane {x : Heis F} (hx : x.a = 0) : theta x ∈ axisPlane (F := F) :=
  mem_axisPlane.mpr ⟨x, hx, rfl⟩

private theorem axis_mul_comm {x y : Heis F} (hx : x.a = 0) (hy : y.a = 0) : x * y = y * x :=
  Heis.ext (by simp [add_comm]) (by simp [add_comm]) (by simp [hx, hy, add_comm])

private theorem theta_injective : Function.Injective (theta (F := F)) := fun x y h =>
  heisEquivBar.injective (Subtype.ext h)

private theorem commute_of_commute_theta (p : ℕ) [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    {g : SpecialLinearGroup (Fin 3) F} {x : Heis F}
    (h : proj 3 F g * theta x = theta x * proj 3 F g) : g * heisSL x = heisSL x * g := by
  have hzp : heisSL x ^ p ^ 1 = 1 := by
    rw [pow_one, ← map_pow, Heis.pow_prime_eq_one Fact.out hp2, map_one]
  have hgz : g * heisSL x * g⁻¹ = heisSL x := by
    refine ASVolI.burnsideF411a_eq_of_proj_eq p (by norm_num) 1 ?_ hzp ?_
    · rw [conj_pow, hzp, mul_one, mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv]
      change proj 3 F g * theta x * (proj 3 F g)⁻¹ = theta x
      rw [h, mul_inv_cancel_right]
  calc g * heisSL x = g * heisSL x * g⁻¹ * g := by group
    _ = heisSL x * g := by rw [hgz]

private theorem lower_entries_of_commute {g : SpecialLinearGroup (Fin 3) F} {x : Heis F}
    (hxa : x.a = 0) (hx1 : x ≠ 1) (h : g * heisSL x = heisSL x * g) :
    (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have hmat : (g : Matrix (Fin 3) (Fin 3) F) * heisMat x =
      heisMat x * (g : Matrix (Fin 3) (Fin 3) F) := by
    have h' := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) h
    simpa [coe_heisSL] using h'
  have e : ∀ i j : Fin 3, ((g : Matrix (Fin 3) (Fin 3) F) * heisMat x) i j =
      (heisMat x * (g : Matrix (Fin 3) (Fin 3) F)) i j := fun i j => by rw [hmat]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [heisMat, Matrix.mul_apply, Fin.sum_univ_three, hxa] at e00 e01 e10 e11
  by_cases hc : x.c = 0
  · have hb : x.b ≠ 0 := fun hb => hx1 (Heis.ext (by simp [hxa]) (by simp [hb]) (by simp [hc]))
    exact ⟨e10.resolve_left hb, e11.resolve_left hb⟩
  · exact ⟨e00.resolve_left hc, e01.resolve_left hc⟩

private theorem mul_heisMat_mul_axis {G H : Matrix (Fin 3) (Fin 3) F} (hGH : G * H = 1)
    (h20 : G 2 0 = 0) (h21 : G 2 1 = 0) (k20 : H 2 0 = 0) (k21 : H 2 1 = 0) {y : Heis F}
    (hya : y.a = 0) :
    G * heisMat y * H = heisMat ⟨0, (G * heisMat y * H) 1 2, (G * heisMat y * H) 0 2⟩ := by
  have key : G * heisMat y * H = 1 + G * (heisMat y - 1) * H := by
    rw [mul_sub, sub_mul, mul_one, hGH, add_sub_cancel]
  rw [key]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisMat, Matrix.mul_apply, Fin.sum_univ_three, hya, h20, h21, k20, k21]

private theorem conj_heisSL_axis {g : SpecialLinearGroup (Fin 3) F}
    (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (k20 : ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (k21 : ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    {y : Heis F} (hya : y.a = 0) :
    ∃ y' : Heis F, y'.a = 0 ∧ heisSL y' = g * heisSL y * g⁻¹ := by
  have hGH : (g : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
    congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F))
      (mul_inv_cancel g)
  exact ⟨_, rfl, Subtype.ext (mul_heisMat_mul_axis hGH h20 h21 k20 k21 hya).symm⟩

private theorem centralizer_le_normalizer_axisPlane (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2) {x : Heis F} (hxa : x.a = 0) (hx1 : x ≠ 1) :
    centralizer ({theta x} : Set (projectiveSL 3 F)) ≤
      normalizer (axisPlane (F := F) : Set (projectiveSL 3 F)) := by
  have hconj : ∀ y ∈ centralizer ({theta x} : Set (projectiveSL 3 F)), ∀ w ∈ axisPlane (F := F),
      y * w * y⁻¹ ∈ axisPlane (F := F) := by
    intro y hy w hw
    obtain ⟨g, rfl⟩ := proj_surjective 3 F y
    have hc : g * heisSL x = heisSL x * g :=
      commute_of_commute_theta p hp2 (mem_centralizer_singleton_iff.mp hy)
    have hc' : g⁻¹ * heisSL x = heisSL x * g⁻¹ := (Commute.inv_left hc :)
    obtain ⟨h20, h21⟩ := lower_entries_of_commute hxa hx1 hc
    obtain ⟨k20, k21⟩ := lower_entries_of_commute hxa hx1 hc'
    obtain ⟨v, hva, rfl⟩ := mem_axisPlane.mp hw
    obtain ⟨v', hv'a, hv'⟩ := conj_heisSL_axis h20 h21 k20 k21 hva
    refine mem_axisPlane.mpr ⟨v', hv'a, ?_⟩
    change proj 3 F (heisSL v') = proj 3 F g * proj 3 F (heisSL v) * (proj 3 F g)⁻¹
    rw [hv', map_mul, map_mul, map_inv]
  intro y hy
  rw [mem_normalizer_iff]
  intro w
  refine ⟨hconj y hy w, fun hw => ?_⟩
  have e : y⁻¹ * (y * w * y⁻¹) * y⁻¹⁻¹ = w := by group
  rw [← e]
  exact hconj y⁻¹ (inv_mem hy) _ hw

private theorem centralizer_axisPlane_le (p : ℕ) [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) :
    centralizer (axisPlane (F := F) : Set (projectiveSL 3 F)) ≤ axisPlane (F := F) := by
  intro y hy
  obtain ⟨g, rfl⟩ := proj_surjective 3 F y
  have h1 := commute_of_commute_theta p hp2
    (mem_centralizer_iff.mp hy _ (theta_mem_axisPlane (x := ⟨0, 1, 0⟩) rfl)).symm
  have h2 := commute_of_commute_theta p hp2
    (mem_centralizer_iff.mp hy _ (theta_mem_axisPlane (x := ⟨0, 0, 1⟩) rfl)).symm
  have hm1 : (g : Matrix (Fin 3) (Fin 3) F) * heisMat (⟨0, 1, 0⟩ : Heis F) =
      heisMat (⟨0, 1, 0⟩ : Heis F) * (g : Matrix (Fin 3) (Fin 3) F) := by
    have h' := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F))
      h1
    simpa [coe_heisSL] using h'
  have hm2 : (g : Matrix (Fin 3) (Fin 3) F) * heisMat (⟨0, 0, 1⟩ : Heis F) =
      heisMat (⟨0, 0, 1⟩ : Heis F) * (g : Matrix (Fin 3) (Fin 3) F) := by
    have h' := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F))
      h2
    simpa [coe_heisSL] using h'
  have e1 : ∀ i j : Fin 3, ((g : Matrix (Fin 3) (Fin 3) F) * heisMat (⟨0, 1, 0⟩ : Heis F)) i j =
      (heisMat (⟨0, 1, 0⟩ : Heis F) * (g : Matrix (Fin 3) (Fin 3) F)) i j := fun i j => by
    rw [hm1]
  have e2 : ∀ i j : Fin 3, ((g : Matrix (Fin 3) (Fin 3) F) * heisMat (⟨0, 0, 1⟩ : Heis F)) i j =
      (heisMat (⟨0, 0, 1⟩ : Heis F) * (g : Matrix (Fin 3) (Fin 3) F)) i j := fun i j => by
    rw [hm2]
  have g01 := e1 0 2
  have g20 := e1 1 0
  have g21 := e1 1 1
  have g11 := e1 1 2
  have g00 := e2 0 2
  have g10 := e2 1 2
  simp [heisMat, Matrix.mul_apply, Fin.sum_univ_three] at g01 g20 g21 g11 g00 g10
  set a := (g : Matrix (Fin 3) (Fin 3) F) 2 2 with ha
  have g11' : (g : Matrix (Fin 3) (Fin 3) F) 1 1 = a := by linear_combination g11
  have g00' : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = a := by linear_combination g00
  have hdet : a ^ 3 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_three, g01, g20, g21, g10, g11', g00'] at h
    linear_combination h
  have ha0 : a ≠ 0 := by
    rintro h0
    rw [h0] at hdet
    simp at hdet
  let u : Fˣ := Units.mk0 a ha0
  have hu3 : u ^ 3 = 1 := Units.ext (by simpa [u] using hdet)
  have hmat : (g : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) (u : F) *
      heisMat (⟨0, (g : Matrix (Fin 3) (Fin 3) F) 1 2 / a,
        (g : Matrix (Fin 3) (Fin 3) F) 0 2 / a⟩ : Heis F) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisMat, Matrix.mul_apply, Fin.sum_univ_three, scalar_apply, u, g01, g20, g21, g11',
        g00', g10, ha0] <;>
      first | exact ha.symm | field_simp
  have hfac : g = scalarElement u hu3 * heisSL ⟨0, (g : Matrix (Fin 3) (Fin 3) F) 1 2 / a,
      (g : Matrix (Fin 3) (Fin 3) F) 0 2 / a⟩ :=
    Subtype.ext hmat
  rw [hfac, map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars u hu3), one_mul]
  exact theta_mem_axisPlane rfl

private def primeAxis (p : ℕ) [CharP F p] :
    Multiplicative (ZMod p × ZMod p) →* Heis F where
  toFun t := ⟨0, ZMod.castHom (dvd_refl p) F (Multiplicative.toAdd t).1,
    ZMod.castHom (dvd_refl p) F (Multiplicative.toAdd t).2⟩
  map_one' := by ext <;> simp
  map_mul' s t := by ext <;> simp

private theorem primeAxis_a (p : ℕ) [CharP F p]
    (t : Multiplicative (ZMod p × ZMod p)) : (primeAxis (F := F) p t).a = 0 :=
  rfl

private theorem primeAxis_injective (p : ℕ) [Fact p.Prime] [CharP F p] :
    Function.Injective (primeAxis (F := F) p) := by
  intro s t h
  have h1 := congrArg Heis.b h
  have h2 := congrArg Heis.c h
  have hinj := (ZMod.castHom (dvd_refl p) F).injective
  apply Multiplicative.toAdd.injective
  exact Prod.ext (hinj h1) (hinj h2)

variable [Finite F]

theorem eq_bot_of_coprime_of_projUnitriangular_le_normalizer (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2) {E : Subgroup (projectiveSL 3 F)} (hE : Nat.Coprime p (Nat.card E))
    (hUE : projUnitriangular 3 F ≤ normalizer (E : Set (projectiveSL 3 F))) : E = ⊥ := by
  have hp : p.Prime := Fact.out
  set B : Subgroup (projectiveSL 3 F) := (theta.comp (primeAxis (F := F) p)).range
  have hinj : Function.Injective (theta.comp (primeAxis (F := F) p)) :=
    theta_injective.comp (primeAxis_injective p)
  have hQU : axisPlane (F := F) ≤ projUnitriangular 3 F := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := mem_axisPlane.mp hy
    exact mem_map_of_mem _ (heisSL_mem_unitriangular x)
  have hBQ : B ≤ axisPlane (F := F) := by
    rintro _ ⟨t, rfl⟩
    exact theta_mem_axisPlane (primeAxis_a p t)
  have hpow : ∀ x : Heis F, theta x ^ p = 1 := fun x => by
    rw [← map_pow, Heis.pow_prime_eq_one hp hp2, map_one]
  refine eq_bot_of_sig (K := ⊤) (B := B) (Q := axisPlane (F := F)) hp ?_ ?_ ?_ le_top ?_ ?_
    (centralizer_axisPlane_le p hp2) hE (hBQ.trans (hQU.trans hUE)) (hQU.trans hUE)
  · rintro _ ⟨t, rfl⟩
    exact hpow _
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod, sq]
  · rintro ⟨y, hy⟩
    obtain ⟨x, -, rfl⟩ := mem_axisPlane.mp hy
    exact ⟨1, Subtype.ext (by simpa using hpow x)⟩
  · intro y hy
    obtain ⟨x, hxa, rfl⟩ := mem_axisPlane.mp hy
    rw [mem_centralizer_iff]
    rintro _ ⟨t, rfl⟩
    change theta (primeAxis p t) * theta x = theta x * theta (primeAxis p t)
    rw [← map_mul, ← map_mul, axis_mul_comm (primeAxis_a p t) hxa]
  · rintro _ ⟨t, rfl⟩ hb1
    refine inf_le_right.trans (centralizer_le_normalizer_axisPlane p hp2 (primeAxis_a p t) ?_)
    rintro h1
    apply hb1
    change theta (primeAxis p t) = 1
    rw [h1, map_one]

theorem mulAut_eq_bot_of_isPGroup_of_le_normalizer_projUnitriangular (p : ℕ) [Fact p.Prime]
    [CharP F p] (hp2 : p ≠ 2) {q : ℕ} (hq : q.Prime) (hpq : p ≠ q)
    (V : Subgroup (MulAut (projectiveSL 3 F))) (hV : IsPGroup q V)
    (hUV : ∀ u ∈ projUnitriangular 3 F,
      MulAut.conj u ∈ normalizer (V : Set (MulAut (projectiveSL 3 F)))) : V = ⊥ := by
  have hp : p.Prime := Fact.out
  have hZ : center (projectiveSL 3 F) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := F) p (n := 3) (by norm_num)
  have hUp : IsPGroup p (projUnitriangular 3 F) := by
    rw [← hS]
    exact S.isPGroup'
  have hzU : theta (⟨0, 0, 1⟩ : Heis F) ∈ projUnitriangular 3 F :=
    mem_map_of_mem _ (heisSL_mem_unitriangular _)
  have hUz : projUnitriangular 3 F ≤
      centralizer ({theta (⟨0, 0, 1⟩ : Heis F)} : Set (projectiveSL 3 F)) := by
    intro u hu
    obtain ⟨y, rfl⟩ := exists_theta_of_mem_bar hu
    exact mem_centralizer_singleton_iff.mpr (Commute.map (mem_center_iff.mp
      (Heis.mem_center.mpr ⟨rfl, rfl⟩ : (⟨0, 0, 1⟩ : Heis F) ∈ center (Heis F)) y :
        Commute y (⟨0, 0, 1⟩ : Heis F)) theta)
  refine mulAut_eq_bot_of_central hZ hq hzU hUz ?_ (fun E hE hUE _ => ?_) V hV hUV
  · exact mulAut_forall_eq_bot_of_selfCentralizing hZ hp hq hpq hUp le_rfl
      (centralizer_theta_le_normalizer p hp2)
      (inf_le_right.trans (centralizer_map_conj_projUnitriangular_le p))
  · refine eq_bot_of_coprime_of_projUnitriangular_le_normalizer p hp2 ?_ hUE
    refine coprime_card_of_isPGroup hp hq hpq fun x => ⟨1, Subtype.ext ?_⟩
    simpa using hE.2 x x.2

end Model

private theorem signalizerThreeOn_of_sylow {p : ℕ} [Fact p.Prime] {M : Type} [Group M] [Finite M]
    (S : Sylow p M)
    (h : ∀ V : Subgroup (MulAut M), IsPGroup 3 V →
      (∀ u ∈ (S : Subgroup M), MulAut.conj u ∈ normalizer (V : Set (MulAut M))) → V = ⊥)
    {K : Type} [Group K] [Finite K] (e : K ≃* M) : SignalizerThreeOn p K := by
  intro T W hW hTW
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e S.isPGroup' S.not_dvd_index T
  set ψ : MulAut K ≃* MulAut M := MulAut.congr Φ.symm with hψ
  have hψc : ∀ r : M, ψ (MulAut.conj (Φ r)) = MulAut.conj r := by
    intro r
    ext a
    simp [hψ, MulAut.conj_apply]
  refine (map_eq_bot_iff_of_injective (H := W) (f := ψ.toMonoidHom) ψ.injective).1
    (h _ (hW.map _) fun r hr => ?_)
  have hrT : Φ r ∈ (T : Subgroup K) := by
    rw [hΦ]
    exact ⟨r, hr, rfl⟩
  have hN : MulAut.conj (Φ r) ∈ normalizer (W : Set (MulAut K)) := by
    rw [mem_normalizer_iff]
    intro w
    refine ⟨hTW _ hrT w, fun hw => ?_⟩
    have e : MulAut.conj (Φ r)⁻¹ * (MulAut.conj (Φ r) * w * (MulAut.conj (Φ r))⁻¹) *
        (MulAut.conj (Φ r)⁻¹)⁻¹ = w := by
      rw [map_inv]
      group
    rw [← e]
    exact hTW _ (inv_mem hrT) _ hw
  rw [← map_equiv_normalizer_eq, ← hψc r]
  exact ⟨_, hN, rfl⟩

theorem signalizerThreeLinThree_holds : SignalizerThreeLinThree := by
  intro p hp hp5 q d hqp _ hd K _ _ ⟨e⟩
  obtain ⟨x, hv⟩ := d
  change x = _ at hd
  subst hd hqp
  haveI : Fact q.p.Prime := ⟨hp⟩
  let eM : TauCeti.ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩ ≃*
      projectiveSL 3 (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (GaloisField q.p q.exponent))
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := GaloisField q.p q.exponent) q.p (n := 3)
    (by norm_num)
  refine signalizerThreeOn_of_sylow S (fun V hV hUV => ?_) (e.trans eM)
  rw [hS] at hUV
  exact mulAut_eq_bot_of_isPGroup_of_le_normalizer_projUnitriangular q.p (by omega)
    Nat.prime_three (by omega) V hV hUV

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
