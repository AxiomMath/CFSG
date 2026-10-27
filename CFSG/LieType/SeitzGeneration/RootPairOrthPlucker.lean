module

public import CFSG.LieType.SeitzGeneration.RootPairOrthGen
public import CFSG.LieType.SeitzGeneration.RootPairOrthTailCenter

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical2 (orthDerived)

namespace RootPairOrth

section Algebra

variable {K : Type} [Field K] {k : Subfield K} {ι : Type}

theorem dual_mem_of_plucker (star : ι → ι) (hss : ∀ a, star (star a) = a) (W : ι → ι → K)
    (hpl : ∀ a b c e, W a b * W c e - W a c * W b e + W a e * W b c = 0)
    (hO : ∀ r s, s ≠ star r → W r s ∈ k)
    (hS : ∀ a j, j ≠ a → j ≠ star a → W a (star a) + W j (star j) ∈ k)
    {a j l : ι} (hja : j ≠ a) (hjs : j ≠ star a) (hla : l ≠ a) (hls : l ≠ star a)
    (hlj : l ≠ j) (hljs : l ≠ star j) : W a (star a) ∈ k := by
  have hinj : ∀ x y, star x = star y → x = y := fun x y h => by rw [← hss x, h, hss y]
  have hsym : ∀ x y, x ≠ star y → y ≠ star x := fun x y h h' => h (by rw [h', hss])
  have hAv : ∀ z x, (x ≠ z ∧ x ≠ star z) → (z ≠ x ∧ z ≠ star x) := fun z x h =>
    ⟨h.1.symm, hsym x z h.2⟩
  have hAs : ∀ z x, (x ≠ z ∧ x ≠ star z) → (star x ≠ z ∧ star x ≠ star z) := fun z x h =>
    ⟨fun h' => h.2 (by rw [← h', hss]), fun h' => h.1 (hinj _ _ h')⟩
  have claim1 : ∀ m c d, c ≠ m → c ≠ star m → d ≠ m → d ≠ star m → d ≠ star c → W c d ≠ 0 →
      W m (star m) ∈ k := by
    intro m c d hcm hcs hdm hds hdc hne
    have h1 := hpl m (star m) c d
    have e1 : W m c ∈ k := hO m c hcs
    have e2 : W (star m) d ∈ k := hO (star m) d (by rw [hss]; exact hdm)
    have e3 : W m d ∈ k := hO m d hds
    have e4 : W (star m) c ∈ k := hO (star m) c (by rw [hss]; exact hcm)
    have e5 : W c d ∈ k := hO c d hdc
    have : W m (star m) = (W m c * W (star m) d - W m d * W (star m) c) / W c d := by
      field_simp
      linear_combination h1
    rw [this]
    exact k.div_mem (k.sub_mem (k.mul_mem e1 e2) (k.mul_mem e3 e4)) e5
  have claim2 : ∀ x y z, (y ≠ x ∧ y ≠ star x) → (z ≠ x ∧ z ≠ star x) → (z ≠ y ∧ z ≠ star y) →
      (∀ c d, (c ≠ z ∧ c ≠ star z) → (d ≠ z ∧ d ≠ star z) → d ≠ star c → W c d = 0) →
      W x (star x) * W y (star y) = 0 := by
    intro x y z hyx hzx hzy hl
    have h1 := hpl x (star x) y (star y)
    have hxz := hAv x z hzx
    have hyz := hAv y z hzy
    have e1 : W x y = 0 := hl x y hxz hyz hyx.2
    have e2 : W (star x) (star y) = 0 :=
      hl (star x) (star y) (hAs z x hxz) (hAs z y hyz)
        (by rw [hss]; exact fun h => hyx.2 (by rw [← h, hss]))
    have e3 : W x (star y) = 0 := hl x (star y) hxz (hAs z y hyz) (fun h => hyx.1 (hinj _ _ h))
    have e4 : W (star x) y = 0 :=
      hl (star x) y (hAs z x hxz) hyz (by rw [hss]; exact hyx.1)
    rw [e1, e2, e3, e4] at h1
    simpa using h1
  have haj : a ≠ j ∧ a ≠ star j := ⟨hja.symm, hsym j a hjs⟩
  have hal : a ≠ l ∧ a ≠ star l := ⟨hla.symm, hsym l a hls⟩
  by_cases hC : ∃ c d, (c ≠ l ∧ c ≠ star l) ∧ (d ≠ l ∧ d ≠ star l) ∧ d ≠ star c ∧ W c d ≠ 0
  · obtain ⟨c, d, hc, hd, hdc, hne⟩ := hC
    have hl := claim1 l c d hc.1 hc.2 hd.1 hd.2 hdc hne
    have := k.sub_mem (hS a l hla hls) hl
    simpa using this
  · have hP : ∀ c d, (c ≠ l ∧ c ≠ star l) → (d ≠ l ∧ d ≠ star l) → d ≠ star c → W c d = 0 :=
      fun c d hc hd hdc => by
        by_contra hne
        exact hC ⟨c, d, hc, hd, hdc, hne⟩
    have hprod := claim2 a j l ⟨hja, hjs⟩ ⟨hla, hls⟩ ⟨hlj, hljs⟩ hP
    by_cases h0 : W a (star a) = 0
    · rw [h0]; exact k.zero_mem
    · have hj0 : W j (star j) = 0 := (mul_eq_zero.mp hprod).resolve_left h0
      have := hS a j hja hjs
      rwa [hj0, add_zero] at this

end Algebra

section Plucker

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : HypCoord Q)
  {k : Subfield K} {g : Matrix (Fin d) (Fin d) K} {μ : K}

theorem phi_plucker (a b c e : Fin d) (x₀ y₀ : Fin d → K) :
    Phi Q g μ (Pi.single a 1) (Pi.single b 1) x₀ y₀ *
        Phi Q g μ (Pi.single c 1) (Pi.single e 1) x₀ y₀ -
      Phi Q g μ (Pi.single a 1) (Pi.single c 1) x₀ y₀ *
        Phi Q g μ (Pi.single b 1) (Pi.single e 1) x₀ y₀ +
      Phi Q g μ (Pi.single a 1) (Pi.single e 1) x₀ y₀ *
        Phi Q g μ (Pi.single b 1) (Pi.single c 1) x₀ y₀ = 0 := by
  simp only [Phi]; ring

include S in
theorem HypCoord.phi_dual_row_pl (hall : ∀ a, a ∈ S.hyp) {x₀ y₀ : Fin d → K}
    (hcol : ∀ x y : Fin d → K, IsBasicT S x y → Phi Q g μ x y x₀ y₀ ∈ k) (a : Fin d) :
    Phi Q g μ (Pi.single a 1) (Pi.single (S.star a) 1) x₀ y₀ ∈ k := by
  obtain ⟨j, l, hj, hl, hja, hjs, hla, hls, hlj, hljs⟩ := S.exists_three_T (hall a)
  refine dual_mem_of_plucker S.star (fun a => S.star_star a (hall a))
    (fun r s => Phi Q g μ (Pi.single r 1) (Pi.single s 1) x₀ y₀)
    (fun a b c e => phi_plucker a b c e x₀ y₀)
    (fun r s hs => hcol _ _ (IsBasicT.single (hall r) (hall s) hs)) (fun a j hja hjs => ?_)
    hja hjs hla hls hlj hljs
  have ha := hall a
  have hj := hall j
  rw [S.phi_row_identity_T g μ ha hj]
  refine k.sub_mem (k.sub_mem (hcol _ _ (IsBasicT.single ha hj hjs))
    (hcol _ _ (IsBasicT.single (S.star_mem j hj) (S.star_mem a ha) ?_)))
    (hcol _ _ (IsBasicT.plane ha hj hja hjs))
  rw [S.star_star j hj]
  exact Ne.symm hjs

include S in
theorem HypCoord.phi_coord_mem_pl (hall : ∀ a, a ∈ S.hyp) (hμ : μ ≠ 0)
    (hg : ∀ v, Q (g *ᵥ v) = μ * Q v) (hdet : IsUnit g.det)
    (hP : ∀ x y x₀ y₀ : Fin d → K, IsBasicT S x y → IsBasicT S x₀ y₀ →
      Phi Q g μ x y x₀ y₀ ∈ k) (r s c c' : Fin d) :
    Phi Q g μ (Pi.single r 1) (Pi.single s 1) (Pi.single c 1) (Pi.single c' 1) ∈ k := by
  have full : ∀ (g' : Matrix (Fin d) (Fin d) K) (μ' : K) (x₀ y₀ : Fin d → K),
      (∀ x y : Fin d → K, IsBasicT S x y → Phi Q g' μ' x y x₀ y₀ ∈ k) →
      ∀ r s : Fin d, Phi Q g' μ' (Pi.single r 1) (Pi.single s 1) x₀ y₀ ∈ k := by
    intro g' μ' x₀ y₀ hcol r s
    by_cases hs : s = S.star r
    · subst hs
      exact S.phi_dual_row_pl (g := g') (μ := μ') hall hcol r
    · exact hcol _ _ (IsBasicT.single (hall r) (hall s) hs)
  have stepA : ∀ x₀ y₀ : Fin d → K, IsBasicT S x₀ y₀ → ∀ r s : Fin d,
      Phi Q g μ (Pi.single r 1) (Pi.single s 1) x₀ y₀ ∈ k := fun x₀ y₀ hb r s =>
    full g μ x₀ y₀ (fun x y hxy => hP x y x₀ y₀ hxy hb) r s
  rw [phi_symm hμ hg hdet]
  refine full g⁻¹ μ⁻¹ (Pi.single r 1) (Pi.single s 1) (fun x y hxy => ?_) c c'
  rw [← phi_symm hμ hg hdet]
  exact stepA x y hxy r s

include S in
theorem HypCoord.rational_of_coord_phi
    (hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k)
    (hnd : (polarBilin Q).Nondegenerate) {σ : K →+* K} (hσ : ∀ x, σ x = x ↔ x ∈ k)
    (hμ : μ ≠ 0) (hdet : g.det ≠ 0)
    (hcoord : ∀ r s c c' : Fin d,
      Phi Q g μ (Pi.single r 1) (Pi.single s 1) (Pi.single c 1) (Pi.single c' 1) ∈ k) :
    ∃ a : K, a ≠ 0 ∧ ∀ r c, σ (g r c) = a * g r c := by
  set G := gramMat Q with hGdef
  have hGdet : G.det ≠ 0 := gramMat_det_ne hnd
  have hG' : ∀ r c, (G * g) r c = polar Q (Pi.single r 1) (g *ᵥ Pi.single c 1) := by
    intro r c
    rw [← gramMat_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  have hdetG' : (G * g).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hGdet hdet
  have hmin : ∀ r s c c', μ⁻¹ * ((G * g) r c * (G * g) s c' - (G * g) r c' * (G * g) s c) ∈ k := by
    intro r s c c'
    have h := hcoord r s c c'
    simp only [Phi] at h
    simpa only [hG'] using h
  have hcard : 3 ≤ Fintype.card (Fin d) := by
    rw [Fintype.card_fin]
    have h1 := S.card_hyp
    have h2' := S.hyp.card_le_univ
    rw [Fintype.card_fin] at h2'
    omega
  obtain ⟨a, ha, heig⟩ := rational_of_minors hcard hσ hμ hdetG' hmin
  refine ⟨a, ha, fun r c => ?_⟩
  have hGfix : ∀ r e, σ (G r e) = G r e := fun r e => (hσ _).mpr (hPk r e)
  have key : ∀ c, G *ᵥ (fun e => σ (g e c) - a * g e c) = 0 := by
    intro c
    funext r
    have h1 := heig r c
    rw [Matrix.mul_apply, map_sum] at h1
    simp only [map_mul, hGfix] at h1
    show ∑ e, G r e * (σ (g e c) - a * g e c) = 0
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [h1, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun e _ => by ring
  have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hGdet (key c)) r
  exact sub_eq_zero.mp this

end Plucker

section Pair

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem orthPair_of_hyp_pl (S : HypCoord Q)
    (hall : ∀ a, a ∈ S.hyp) (hext : IsExtension k Q₀ Q) (hder : elementaryGroup Q = orthDerived Q)
    (hnd : (polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdeg : Module.finrank k K = p)
    (hK : Nat.card K = Nat.card k ^ p) (hk3 : 3 ≤ Nat.card k)
    (hsetup : ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
      SubfieldSetup k Q₀ Q σ p)
    (gp : similarityPairs Q) (hgp : gp.val.right = 1)
    (hne : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≠
      subfieldFixedGroup k Q₀ Q) :
    Subgroup.closure ((subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) ∪
      ((subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom :
        Set (matrixProjectiveDerived Q))) = ⊤ := by
  have hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k := fun a =>
    Q_isRat_mem hext (isRat_single k a)
  have hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k := fun a b =>
    polar_isRat_mem hext (isRat_single k a) (isRat_single k b)
  refine orthPair_of_basic (IsBasicT S)
    (fun x y h => ⟨(h.isRat k hQk).1, (h.isRat k hQk).2, h.isTS⟩) ?_ ?_ hext hder hp hp2 hdeg hK
    hk3 hsetup gp hgp hne
  · intro σ hσk g μ hμ hdet hgμ hP
    exact S.rational_of_coord_phi hPk hnd (σ := σ.toRingHom) (fun x => (hσk x).symm) hμ hdet
      (fun r s c c' => S.phi_coord_mem_pl hall hμ hgμ (isUnit_iff_ne_zero.mpr hdet) hP r s c c')
  · intro H hH hrat x y hxy hne' hline
    exact S.elementaryGroup_le_of_basic_line_T H hnd hH hrat hxy hne' hline

end Pair

end RootPairOrth

end CFSG.LieType.SeitzGeneration
