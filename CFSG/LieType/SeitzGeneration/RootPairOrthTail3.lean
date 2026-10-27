module

public import CFSG.LieType.SeitzGeneration.RootPairOrthTail2
public import CFSG.LieType.SeitzGeneration.RootPairOrthPlucker

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical2 (orthDerived)

namespace RootPairOrth

section Mixed

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : HypCoord Q)

@[expose] def yMix (a j t t' : Fin d) : Fin d → K :=
  xi S j (Pi.single t' 1) -
    polar Q (Pi.single t 1 : Fin d → K) (Pi.single t' 1) • (Pi.single (S.star a) 1 : Fin d → K)

variable (Q) in
inductive IsTail3 (S : HypCoord Q) : (Fin d → K) → (Fin d → K) → Prop
  | mk {a j t t' : Fin d} : a ∈ S.hyp → j ∈ S.hyp → j ≠ a → j ≠ S.star a → t ∉ S.hyp →
      t' ∉ S.hyp → IsTail3 S (xi S a (Pi.single t 1)) (yMix S a j t t')

theorem xi_apply_self {a : Fin d} (ha : a ∈ S.hyp) {w : Fin d → K} (hw : w a = 0) :
    xi S a w a = 1 := by
  have : (Pi.single (S.star a) 1 : Fin d → K) a = 0 := single_apply_ne (S.star_ne a ha).symm
  simp [xi, hw, this]

theorem xi_apply_ne {a j : Fin d} (hja : a ≠ j) (hjs : a ≠ S.star j) {w : Fin d → K}
    (hw : w a = 0) : xi S j w a = 0 := by
  simp [xi, hw, single_apply_ne hja, single_apply_ne hjs]

theorem polar_xi_tail {j : Fin d} (hj : j ∈ S.hyp) {w : Fin d → K} (w' : Fin d → K)
    (hw : IsTailVec S w) : polar Q (xi S j w') w = polar Q w' w := by
  have h1 : polar Q (Pi.single j 1 : Fin d → K) w = 0 := by
    rw [S.polar_single j hj]; exact hw _ (S.star_mem j hj)
  have h2 : polar Q (Pi.single (S.star j) 1 : Fin d → K) w = 0 := by
    rw [S.polar_single _ (S.star_mem j hj), S.star_star j hj]; exact hw _ hj
  simp only [xi, polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul, h1, h2]
  ring

theorem IsTail3.isTS {S : HypCoord Q} {x y : Fin d → K} (h : IsTail3 Q S x y) : IsTS Q x y := by
  cases h with
  | mk ha hj hja hjs ht ht' =>
    rename_i a j t t'
    have has := S.star_mem a ha
    have htv := isTailVec_single S ht
    have htv' := isTailVec_single S ht'
    have hya : (xi S j (Pi.single t' 1 : Fin d → K)) a = 0 :=
      xi_apply_ne S hja.symm (fun h => hjs (by rw [h, S.star_star j hj])) (htv' a ha)
    have hq : Q (Pi.single (S.star a) 1 : Fin d → K) = 0 := S.Q_single _ has
    have hpq : polar Q (xi S j (Pi.single t' 1 : Fin d → K)) (Pi.single (S.star a) 1) = 0 := by
      rw [S.polar_single_right has, S.star_star a ha]; exact hya
    have hxa : polar Q (xi S a (Pi.single t 1 : Fin d → K)) (Pi.single (S.star a) 1) = 1 := by
      rw [S.polar_single_right has, S.star_star a ha]; exact xi_apply_self S ha (htv a ha)
    have hxy : polar Q (xi S a (Pi.single t 1 : Fin d → K)) (xi S j (Pi.single t' 1)) =
        polar Q (Pi.single t 1 : Fin d → K) (Pi.single t' 1) :=
      S.polar_xi_xi ha hj hja hjs htv htv'
    refine ⟨S.Q_xi ha htv, ?_, ?_⟩
    · rw [yMix, sub_eq_add_neg, QuadraticMap.map_add Q, S.Q_xi hj htv', QuadraticMap.map_neg,
        QuadraticMap.map_smul, hq, polar_neg_right, polar_smul_right, hpq]
      simp
    · rw [yMix, polar_sub_right, polar_smul_right, hxy, hxa, smul_eq_mul]
      ring

theorem IsTail3.isRat {S : HypCoord Q} {k : Subfield K}
    (hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k)
    (hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k) {x y : Fin d → K}
    (h : IsTail3 Q S x y) : IsRat k x ∧ IsRat k y := by
  cases h with
  | mk ha hj hja hjs ht ht' =>
    rename_i a j t t'
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [xi, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact k.sub_mem (k.add_mem (isRat_single k a i) (isRat_single k t i))
        (k.mul_mem (hQk t) (isRat_single k _ i))
    · simp only [yMix, xi, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact k.sub_mem (k.sub_mem (k.add_mem (isRat_single k j i) (isRat_single k t' i))
        (k.mul_mem (hQk t') (isRat_single k _ i))) (k.mul_mem (hPk t t') (isRat_single k _ i))

end Mixed

section Rows

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : HypCoord Q)
  {k : Subfield K} {g : Matrix (Fin d) (Fin d) K} {μ : K}

include S in
theorem HypCoord.phi_dual_row_plT {x₀ y₀ : Fin d → K}
    (hcol : ∀ x y : Fin d → K, IsBasicT S x y → Phi Q g μ x y x₀ y₀ ∈ k) {a : Fin d}
    (ha : a ∈ S.hyp) : Phi Q g μ (Pi.single a 1) (Pi.single (S.star a) 1) x₀ y₀ ∈ k := by
  obtain ⟨j, l, hj, hl, hja, hjs, hla, hls, hlj, hljs⟩ := S.exists_three_T ha
  let st : S.hyp → S.hyp := fun x => ⟨S.star x.1, S.star_mem x.1 x.2⟩
  have hsum : ∀ a j : S.hyp, j ≠ a → j ≠ st a →
      Phi Q g μ (Pi.single a.1 1) (Pi.single (S.star a.1) 1) x₀ y₀ +
        Phi Q g μ (Pi.single j.1 1) (Pi.single (S.star j.1) 1) x₀ y₀ ∈ k := by
    intro a j hja hjs
    have hja' : j.1 ≠ a.1 := fun h => hja (Subtype.ext h)
    have hjs' : j.1 ≠ S.star a.1 := fun h => hjs (Subtype.ext h)
    rw [S.phi_row_identity_T g μ a.2 j.2]
    refine k.sub_mem (k.sub_mem (hcol _ _ (IsBasicT.single a.2 j.2 hjs'))
      (hcol _ _ (IsBasicT.single (S.star_mem j.1 j.2) (S.star_mem a.1 a.2) ?_)))
      (hcol _ _ (IsBasicT.plane a.2 j.2 hja' hjs'))
    rw [S.star_star j.1 j.2]
    exact Ne.symm hjs'
  exact dual_mem_of_plucker (k := k) st (fun x => Subtype.ext (S.star_star x.1 x.2))
    (fun r s : S.hyp => Phi Q g μ (Pi.single r.1 1) (Pi.single s.1 1) x₀ y₀)
    (fun a b c e => phi_plucker a.1 b.1 c.1 e.1 x₀ y₀)
    (fun r s hs => hcol _ _ (IsBasicT.single r.2 s.2 (fun h => hs (Subtype.ext h)))) hsum
    (a := ⟨a, ha⟩) (j := ⟨j, hj⟩) (l := ⟨l, hl⟩) (fun h => hja (congrArg Subtype.val h))
    (fun h => hjs (congrArg Subtype.val h)) (fun h => hla (congrArg Subtype.val h))
    (fun h => hls (congrArg Subtype.val h)) (fun h => hlj (congrArg Subtype.val h))
    (fun h => hljs (congrArg Subtype.val h))

include S in
theorem HypCoord.phi_tail_tail3 (hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k)
    (hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k) {x₀ y₀ : Fin d → K}
    (hHH : ∀ a b, a ∈ S.hyp → b ∈ S.hyp →
      Phi Q g μ (Pi.single a 1) (Pi.single b 1) x₀ y₀ ∈ k)
    (hHT : ∀ a t, a ∈ S.hyp → t ∉ S.hyp →
      Phi Q g μ (Pi.single a 1) (Pi.single t 1) x₀ y₀ ∈ k)
    (hcol3 : ∀ x y : Fin d → K, IsTail3 Q S x y → Phi Q g μ x y x₀ y₀ ∈ k) {t t' : Fin d}
    (ht : t ∉ S.hyp) (ht' : t' ∉ S.hyp) :
    Phi Q g μ (Pi.single t 1) (Pi.single t' 1) x₀ y₀ ∈ k := by
  obtain ⟨a, ha⟩ : ∃ a, a ∈ S.hyp := by
    have := S.card_hyp
    exact Finset.card_pos.mp (by omega)
  obtain ⟨j, -, hj, -, hja, hjs, -, -, -, -⟩ := S.exists_three_T ha
  have has := S.star_mem a ha
  have hjst := S.star_mem j hj
  obtain ⟨W, hW⟩ : ∃ W : Fin d → Fin d → K, ∀ r s,
      W r s = Phi Q g μ (Pi.single r 1) (Pi.single s 1) x₀ y₀ := ⟨_, fun _ _ => rfl⟩
  have hTH : ∀ a t, a ∈ S.hyp → t ∉ S.hyp → W t a ∈ k := fun a t ha ht => by
    rw [hW, phi_swap]; exact k.neg_mem (hHT a t ha ht)
  have hHH' : ∀ a b, a ∈ S.hyp → b ∈ S.hyp → W a b ∈ k := fun a b ha hb => by
    rw [hW]; exact hHH a b ha hb
  have hHT' : ∀ a t, a ∈ S.hyp → t ∉ S.hyp → W a t ∈ k := fun a t ha ht => by
    rw [hW]; exact hHT a t ha ht
  have hxy := hcol3 _ _ (IsTail3.mk ha hj hja hjs ht ht')
  have hmaster : W t t' = Phi Q g μ (xi S a (Pi.single t 1)) (yMix S a j t t') x₀ y₀ -
      (W a j + W a t' - Q (Pi.single t' 1 : Fin d → K) * W a (S.star j) -
        polar Q (Pi.single t 1 : Fin d → K) (Pi.single t' 1) * W a (S.star a) + W t j -
        Q (Pi.single t' 1 : Fin d → K) * W t (S.star j) -
        polar Q (Pi.single t 1 : Fin d → K) (Pi.single t' 1) * W t (S.star a) -
        Q (Pi.single t 1 : Fin d → K) * W (S.star a) j -
        Q (Pi.single t 1 : Fin d → K) * W (S.star a) t' +
        Q (Pi.single t 1 : Fin d → K) * Q (Pi.single t' 1 : Fin d → K) *
          W (S.star a) (S.star j)) := by
    simp only [hW, Phi, yMix, xi, polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul]
    ring
  rw [← hW, hmaster]
  refine k.sub_mem hxy ?_
  have m1 := k.add_mem (hHH' a j ha hj) (hHT' a t' ha ht')
  have m2 := k.sub_mem m1 (k.mul_mem (hQk t') (hHH' a _ ha hjst))
  have m3 := k.sub_mem m2 (k.mul_mem (hPk t t') (hHH' a _ ha has))
  have m4 := k.add_mem m3 (hTH j t hj ht)
  have m5 := k.sub_mem m4 (k.mul_mem (hQk t') (hTH _ t hjst ht))
  have m6 := k.sub_mem m5 (k.mul_mem (hPk t t') (hTH _ t has ht))
  have m7 := k.sub_mem m6 (k.mul_mem (hQk t) (hHH' _ j has hj))
  have m8 := k.sub_mem m7 (k.mul_mem (hQk t) (hHT' _ t' has ht'))
  exact k.add_mem m8 (k.mul_mem (k.mul_mem (hQk t) (hQk t')) (hHH' _ _ has hjst))

include S in
theorem HypCoord.phi_row_ext_M3 (hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k)
    (hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k) {x₀ y₀ : Fin d → K}
    (hcol : ∀ x y : Fin d → K, IsBasicT S x y → Phi Q g μ x y x₀ y₀ ∈ k)
    (hcol3 : ∀ x y : Fin d → K, IsTail3 Q S x y → Phi Q g μ x y x₀ y₀ ∈ k) (r s : Fin d) :
    Phi Q g μ (Pi.single r 1) (Pi.single s 1) x₀ y₀ ∈ k := by
  have hHH : ∀ a b, a ∈ S.hyp → b ∈ S.hyp →
      Phi Q g μ (Pi.single a 1) (Pi.single b 1) x₀ y₀ ∈ k := by
    intro a b ha hb
    by_cases hbs : b = S.star a
    · subst hbs
      exact S.phi_dual_row_plT hcol ha
    · exact hcol _ _ (IsBasicT.single ha hb hbs)
  have hHT : ∀ a t, a ∈ S.hyp → t ∉ S.hyp →
      Phi Q g μ (Pi.single a 1) (Pi.single t 1) x₀ y₀ ∈ k := fun a t ha ht =>
    S.phi_hyp_tail hQk hcol hHH ha ht
  by_cases hr : r ∈ S.hyp <;> by_cases hs : s ∈ S.hyp
  · exact hHH r s hr hs
  · exact hHT r s hr hs
  · rw [phi_swap]
    exact k.neg_mem (hHT s r hs hr)
  · exact S.phi_tail_tail3 hQk hPk hHH hHT hcol3 hr hs

include S in
theorem HypCoord.phi_coord_mem_M3 (hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k)
    (hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k) (hμ : μ ≠ 0)
    (hg : ∀ v, Q (g *ᵥ v) = μ * Q v) (hdet : IsUnit g.det)
    (hP : ∀ x y x₀ y₀ : Fin d → K, (IsBasicT S x y ∨ IsTail3 Q S x y) →
      (IsBasicT S x₀ y₀ ∨ IsTail3 Q S x₀ y₀) → Phi Q g μ x y x₀ y₀ ∈ k) (r s c c' : Fin d) :
    Phi Q g μ (Pi.single r 1) (Pi.single s 1) (Pi.single c 1) (Pi.single c' 1) ∈ k := by
  have full : ∀ (g' : Matrix (Fin d) (Fin d) K) (μ' : K) (x₀ y₀ : Fin d → K),
      (∀ x y : Fin d → K, (IsBasicT S x y ∨ IsTail3 Q S x y) → Phi Q g' μ' x y x₀ y₀ ∈ k) →
      ∀ r s : Fin d, Phi Q g' μ' (Pi.single r 1) (Pi.single s 1) x₀ y₀ ∈ k :=
    fun g' μ' x₀ y₀ hcol =>
    S.phi_row_ext_M3 hQk hPk (fun x y hxy => hcol x y (Or.inl hxy))
      (fun x y hxy => hcol x y (Or.inr hxy))
  have stepA : ∀ x₀ y₀ : Fin d → K, (IsBasicT S x₀ y₀ ∨ IsTail3 Q S x₀ y₀) → ∀ r s : Fin d,
      Phi Q g μ (Pi.single r 1) (Pi.single s 1) x₀ y₀ ∈ k := fun x₀ y₀ hb r s =>
    full g μ x₀ y₀ (fun x y hxy => hP x y x₀ y₀ hxy hb) r s
  rw [phi_symm hμ hg hdet]
  refine full g⁻¹ μ⁻¹ (Pi.single r 1) (Pi.single s 1) (fun x y hxy => ?_) c c'
  rw [← phi_symm hμ hg hdet]
  exact stepA x y hxy r s

end Rows

section Generation3

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : HypCoord Q)
  {k : Subfield K} (H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)))

include S in
theorem HypCoord.elementaryGroup_le_of_tail3_line (hnd : (polarBilin Q).Nondegenerate)
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hrat : ∀ u w : Fin d → K, IsRat k u → IsRat k w → Q u = 0 → polar Q u w = 0 →
      eichler Q u w ∈ H)
    {x y : Fin d → K} (hxy : IsTail3 Q S x y) (hline : ∀ r : K, eichler Q x (r • y) ∈ H) :
    elementaryGroup Q ≤ H := by
  cases hxy with
  | mk ha hj hja hjs ht ht' =>
    rename_i a j t t'
    have has := S.star_mem a ha
    have htv := isTailVec_single S ht
    have htv' := isTailVec_single S ht'
    have hE1pol : polar Q (Pi.single (S.star a) 1 : Fin d → K) (Pi.single t 1) = 0 := by
      rw [S.polar_single _ has, S.star_star a ha]; exact htv a ha
    have hE1 : eichler Q (Pi.single (S.star a) 1 : Fin d → K) (Pi.single t 1) ∈ H :=
      hrat _ _ (isRat_single k _) (isRat_single k _) (S.Q_single _ has) hE1pol
    set E1 := eichler Q (Pi.single (S.star a) 1 : Fin d → K) (Pi.single t 1) with hE1def
    have hya : (xi S j (Pi.single t' 1 : Fin d → K)) a = 0 :=
      xi_apply_ne S hja.symm (fun h => hjs (by rw [h, S.star_star j hj])) (htv' a ha)
    have e1a : E1 (Pi.single a 1) = xi S a (Pi.single t 1) := by
      rw [hE1def, eichler_apply (S.Q_single _ has) hE1pol, S.polar_single_right has,
        S.star_star a ha, S.polar_single a ha, htv _ has]
      simp [xi]
    have e1y : E1 (xi S j (Pi.single t' 1)) = yMix S a j t t' := by
      have hcomm : polar Q (Pi.single t' 1 : Fin d → K) (Pi.single t 1) =
          polar Q (Pi.single t 1 : Fin d → K) (Pi.single t' 1) := polar_comm _ _ _
      rw [hE1def, eichler_apply (S.Q_single _ has) hE1pol, S.polar_single_right has,
        S.star_star a ha, hya, polar_xi_tail S hj _ htv, hcomm]
      simp [yMix]
    have hline' : ∀ r : K, eichler Q (Pi.single a 1 : Fin d → K)
        (r • xi S j (Pi.single t' 1)) ∈ H := by
      intro r
      have h3 := eichler_conj (hH (H.inv_mem hE1)) (xi S a (Pi.single t 1)) (r • yMix S a j t t')
      rw [map_smul, inv_apply_of_apply_eq E1 e1y, inv_apply_of_apply_eq E1 e1a] at h3
      rw [← h3]
      exact H.mul_mem (H.mul_mem (H.inv_mem hE1) (hline r)) (H.inv_mem (H.inv_mem hE1))
    have hne : (Pi.single a 1 : Fin d → K) ≠ xi S j (Pi.single t' 1) := fun h => by
      have := congrFun h j
      rw [xi_apply_self S hj (htv' j hj), single_apply_ne hja] at this
      exact zero_ne_one this
    exact S.elementaryGroup_le_of_basic_line_T H hnd hH hrat (IsBasicT.tail1 ha hj hja hjs ht')
      hne hline'

end Generation3

section Pair3

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem orthPair_of_hypCoord_M3 (S : HypCoord Q)
    (hext : IsExtension k Q₀ Q) (hder : elementaryGroup Q = orthDerived Q)
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
  refine orthPair_of_basic (fun x y => IsBasicT S x y ∨ IsTail3 Q S x y) ?_ ?_ ?_ hext hder hp hp2
    hdeg hK hk3 hsetup gp hgp hne
  · intro x y h
    rcases h with h | h
    · exact ⟨(h.isRat k hQk).1, (h.isRat k hQk).2, h.isTS⟩
    · exact ⟨(h.isRat hQk hPk).1, (h.isRat hQk hPk).2, h.isTS⟩
  · intro σ hσk g μ hμ hdet hgμ hP
    exact S.rational_of_coord_phi hPk hnd (σ := σ.toRingHom) (fun x => (hσk x).symm) hμ hdet
      (fun r s c c' => S.phi_coord_mem_M3 hQk hPk hμ hgμ (isUnit_iff_ne_zero.mpr hdet) hP r s c c')
  · intro H hH hrat x y hxy hne' hline
    rcases hxy with hxy | hxy
    · exact S.elementaryGroup_le_of_basic_line_T H hnd hH hrat hxy hne' hline
    · exact S.elementaryGroup_le_of_tail3_line H hnd hH hrat hxy hline

end Pair3

end RootPairOrth

end CFSG.LieType.SeitzGeneration
