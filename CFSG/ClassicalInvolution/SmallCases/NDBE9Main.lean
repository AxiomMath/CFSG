module

public import CFSG.ClassicalInvolution.SmallCases.NDBE4SVert
public import CFSG.ClassicalInvolution.SmallCases.NDBE9Lay
public import CFSG.ClassicalInvolution.Asc77.AscT7OA
public import CFSG.ClassicalInvolution.Asc77.AscT7OF

public section

namespace CFSG.ClassicalInvolution.NDB.SpinVertex

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalGroups.Orthogonal.Small CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
  CFSG.ClassicalInvolution.Asc77 CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.NDB.SpinStd
  CFSG.ClassicalInvolution.NDB.FourFrame QuadraticMap
  CFSG.ClassicalInvolution.ModelFacts.Orth15.T7O CFSG.ClassicalInvolution.NDB.SpinOuter
open scoped MatrixGroups

section Acts

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {X : Type} [Group X]

theorem actsAs_e (e : ↥(elementaryGroup Q) →* X) (a : ↥(elementaryGroup Q)) :
    ActsAs e (e a) (a : V ≃ₗ[F] V) := by
  intro g h hgh
  rw [e_conj]
  congr 1
  exact Subtype.ext hgh.symm

theorem actsAs_mul {e : ↥(elementaryGroup Q) →* X} {y₁ y₂ : X} {A₁ A₂ : V ≃ₗ[F] V}
    (h₁ : ActsAs e y₁ A₁) (h₂ : ActsAs e y₂ A₂)
    (hA₂ : A₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : ActsAs e (y₁ * y₂) (A₁ * A₂) := by
  intro g h hgh
  set g' : ↥(elementaryGroup Q) := ⟨A₂ * g * A₂⁻¹, conj_mem_elementaryGroup hA₂ g.2⟩ with hg'
  have e₂ := h₂ g g' rfl
  have e₁ := h₁ g' h (by
    rw [hgh]
    show A₁ * A₂ * (g : V ≃ₗ[F] V) * (A₁ * A₂)⁻¹ = A₁ * (A₂ * (g : V ≃ₗ[F] V) * A₂⁻¹) * A₁⁻¹
    group)
  calc y₁ * y₂ * e g * (y₁ * y₂)⁻¹ = y₁ * (y₂ * e g * y₂⁻¹) * y₁⁻¹ := by group
    _ = y₁ * e g' * y₁⁻¹ := by rw [e₂]
    _ = e h := e₁

theorem eq_one_of_actsAs_scalar {e : ↥(elementaryGroup Q) →* X}
    (hcent : ∀ x : X, (∀ y ∈ e.range, x * y = y * x) → x = 1) {y : X} {c : V ≃ₗ[F] V}
    (hc : c ∈ scalars F V) (hy : ActsAs e y c) : y = 1 := by
  apply hcent
  rintro _ ⟨g, rfl⟩
  have h1 := hy g g (by rw [commute_of_mem_scalars hc, mul_assoc, mul_inv_cancel, mul_one])
  calc y * e g = y * e g * y⁻¹ * y := by group
    _ = e g * y := by rw [h1]

theorem splitInv_of_involution (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : F) ≠ 0)
    {w : V ≃ₗ[F] V} (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hw2 : w * w = 1) :
    SplitInv Q (minusSp w) (plusSp w) w where
  ndS := polarNondegOn_of_isCompl hQ (isCompl_plusSp_minusSp h2 hw2).symm
    (fun a ha b hb => by rw [polar_comm]; exact polar_plusSp_minusSp h2 hwO hb ha)
  ndT := polarNondegOn_of_isCompl hQ (isCompl_plusSp_minusSp h2 hw2)
    (fun a ha b hb => polar_plusSp_minusSp h2 hwO ha hb)
  orth := fun a ha b hb => by rw [polar_comm]; exact polar_plusSp_minusSp h2 hwO hb ha
  top := (isCompl_plusSp_minusSp h2 hw2).symm.sup_eq_top
  negS := fun _ ha => mem_minusSp.mp ha
  fixT := fun _ ha => mem_plusSp.mp ha

end Acts

section Outer

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

theorem alphaOf_outer (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (fr : Frame Q) (hV : 7 ≤ Module.finrank F (ι → F))
    [Finite H] {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (hlift : LiftSim Q ψ) {R R' : Subgroup (spinGroup Q)}
    (hRfr : R.map (spinAction Q) = fr.La.range) (hR'fr : R'.map (spinAction Q) = fr.swap.La.range)
    {x : spinGroup Q} (hxR : x ∈ R) (hx : spinAction Q x = fr.La (-1)) (hx2 : x * x = 1)
    {v : H} (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * ψ r = ψ r * v) (hvR' : ∀ r ∈ R', v * ψ r = ψ r * v)
    (hout : ∀ y : spinGroup Q, toInducedAutOn ψ.range ⟨v, hv⟩ ≠
      toInducedAutOn ψ.range ⟨ψ y, mem_normalizer_range ψ y⟩) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩,
      toInducedAutOn ψ.range ⟨v, hv⟩} : Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hE : ∀ s, spinAction Q s ∈ elementaryGroup Q := fun s => hrange ▸ ⟨s, rfl⟩
  obtain ⟨α, w, hα', -, hwiso, hwspan, hθw, hw2⟩ :=
    exists_lift hodd h5 hQ hrange fr hV hψ hlift hRfr hR'fr hv hv2 hvR hvR'
  obtain ⟨e, he, hkerE, hnorm, hcent⟩ := exists_hom_spin hodd hQ (by omega) hrange ψ hψ
  have := hnorm
  have hzE : fr.La (-1) ∈ elementaryGroup Q := fr.La_mem_elementaryGroup (-1)
  have hez : e ⟨fr.La (-1), hzE⟩ = toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ := by
    rw [← he x (hE x)]
    congr 1
    exact Subtype.ext hx.symm
  have hαψ : ∀ s, ψ.rangeRestrict (α s) =
      ((toInducedAutOn ψ.range ⟨v, hv⟩ : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range)
        (ψ.rangeRestrict s) := fun s => Subtype.ext (hα' s)
  have hact : ActsAs e (toInducedAutOn ψ.range ⟨v, hv⟩) w := fun g h hgh =>
    conj_e_of_lift e he hrange _ α w hαψ hθw g h hgh
  have hactz : ActsAs e (toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩)
      (fr.La (-1)) := by
    rw [← hez]
    exact actsAs_e e ⟨fr.La (-1), hzE⟩
  have hzO : fr.La (-1) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fr.La_mem_orthogonalGroup (-1)
  have hactzv := actsAs_mul hactz hact hwiso
  have hz2 : toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ *
      toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ = 1 := by
    rw [← map_mul]
    have : (⟨ψ x, mem_normalizer_range ψ x⟩ * ⟨ψ x, mem_normalizer_range ψ x⟩ :
        ↥(Subgroup.normalizer (ψ.range : Set H))) = 1 :=
      Subtype.ext (show ψ x * ψ x = 1 by rw [← map_mul, hx2, map_one])
    rw [this, map_one]
  have hv2' : toInducedAutOn ψ.range ⟨v, hv⟩ * toInducedAutOn ψ.range ⟨v, hv⟩ = 1 := by
    rw [← map_mul]
    have : (⟨v, hv⟩ * ⟨v, hv⟩ : ↥(Subgroup.normalizer (ψ.range : Set H))) = 1 := Subtype.ext hv2
    rw [this, map_one]
  have hzv : toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ *
      toInducedAutOn ψ.range ⟨v, hv⟩ = toInducedAutOn ψ.range ⟨v, hv⟩ *
        toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hvR x hxR).symm
  have htriv : toInducedAutOn ψ.range ⟨ψ 1, mem_normalizer_range ψ 1⟩ = 1 := by
    have : (⟨ψ 1, mem_normalizer_range ψ 1⟩ : ↥(Subgroup.normalizer (ψ.range : Set H))) = 1 :=
      Subtype.ext (map_one ψ)
    rw [this, map_one]
  have hv1 : toInducedAutOn ψ.range ⟨v, hv⟩ ≠ 1 := fun h => hout 1 (h.trans htriv.symm)
  have hvz : toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ *
      toInducedAutOn ψ.range ⟨v, hv⟩ ≠ 1 := fun h =>
    hout x ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hz2))
  have hD : LocalData e ⟨fr.La (-1), hzE⟩ fr.span fr.perp :=
    ⟨splitInv_frame fr hQ, hkerE, T7O.span_ne_bot fr, T7O.perp_ne_bot fr (by omega)⟩
  have hz1 : toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ ≠ 1 := by
    rw [← hez]
    exact hD.ne_one h2
  have hwz := comm_La_neg_one fr hwiso hwspan
  have hu2 : fr.La (-1) * w * (fr.La (-1) * w) = 1 := by
    calc fr.La (-1) * w * (fr.La (-1) * w) = fr.La (-1) * (w * fr.La (-1)) * w := by group
      _ = fr.La (-1) * (fr.La (-1) * w) * w := by rw [hwz]
      _ = (fr.La (-1) * fr.La (-1)) * (w * w) := by group
      _ = 1 := by rw [fr.La_neg_one_mul_self, hw2, one_mul]
  have huO : fr.La (-1) * w ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hzO hwiso
  have hsw := splitInv_of_involution hQ h2 hwiso hw2
  have hsu := splitInv_of_involution hQ h2 huO hu2
  have hspan_ne : fr.span ≠ ⊥ := T7O.span_ne_bot fr
  have hspan₁ : fr.span ≤ plusSp w := fun y hy => mem_plusSp.mpr (hwspan y hy)
  have hspan₂ : fr.span ≤ minusSp (fr.La (-1) * w) := fun y hy => mem_minusSp.mpr (by
    rw [LinearEquiv.mul_apply, hwspan y hy, La_neg_one_of_mem_span fr hy])
  have hS₁ : minusSp w ≠ ⊥ := by
    intro hbot
    have h1 : w = 1 := eq_one_of_minusSp_eq_bot h2 hw2 hbot
    rw [h1] at hact
    exact hv1 (eq_one_of_actsAs_scalar hcent (Subgroup.one_mem _) hact)
  have hT₁ : plusSp w ≠ ⊥ := fun h => hspan_ne (eq_bot_iff.mpr (hspan₁.trans h.le))
  have hS₂ : minusSp (fr.La (-1) * w) ≠ ⊥ := fun h =>
    hspan_ne (eq_bot_iff.mpr (hspan₂.trans h.le))
  have hT₂ : plusSp (fr.La (-1) * w) ≠ ⊥ := by
    intro hbot
    have hbot' : plusSp w ⊓ fr.perp = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hy₁, hy₂⟩
      have hy : y ∈ plusSp (fr.La (-1) * w) := mem_plusSp.mpr (by
        rw [LinearEquiv.mul_apply, mem_plusSp.mp hy₁, La_neg_one_of_mem_perp fr hy₂])
      rw [hbot] at hy
      exact hy
    have hneg := mul_La_neg_one_eq_neg h2 fr hwiso hw2 hwspan hbot'
    rw [← hwz, hneg] at hactzv
    exact hvz (eq_one_of_actsAs_scalar hcent neg_mem_scalars hactzv)
  have hz₁ : toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ ∈
      img e (elemOn Q (minusSp w) ⊔ elemOn Q (plusSp w)) := by
    rw [← hez]
    exact (mem_img_iff e).mpr ⟨⟨fr.La (-1), hzE⟩,
      Subgroup.mem_sup_right (elemOn_mono hspan₁ (La_mem_elemOn fr (-1))), rfl⟩
  have hz₂ : toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ ∈
      img e (elemOn Q (minusSp (fr.La (-1) * w)) ⊔ elemOn Q (plusSp (fr.La (-1) * w))) := by
    rw [← hez]
    exact (mem_img_iff e).mpr ⟨⟨fr.La (-1), hzE⟩,
      Subgroup.mem_sup_left (elemOn_mono hspan₂ (La_mem_elemOn fr (-1))), rfl⟩
  have d₁ := layerData_of_split h2 e hkerE hwiso hsw hS₁ hT₁ hact
    (layerGenOn_of_regular hodd h5 hsw.ndS) (layerGenOn_of_regular hodd h5 hsw.ndT)
    (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩,
      toInducedAutOn ψ.range ⟨v, hv⟩} : Set ↥(inducedAutOn ψ.range))) (by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_sup_right hz₁
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have d₂ := layerData_of_split h2 e hkerE huO hsu hS₂ hT₂ hactzv
    (layerGenOn_of_regular hodd h5 hsu.ndS) (layerGenOn_of_regular hodd h5 hsu.ndT)
    (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩,
      toInducedAutOn ψ.range ⟨v, hv⟩} : Set ↥(inducedAutOn ψ.range))) (by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_sup_right hz₂
      · have hmem := mul_mem (Subgroup.mem_sup_right hz₂) (Subgroup.mem_sup_left
          (Subgroup.mem_zpowers (toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ *
            toInducedAutOn ψ.range ⟨v, hv⟩)))
        rwa [← mul_assoc, hz2, one_mul] at hmem)
  exact alphaOf_klein_outer_of_oddCore e.range hz2 hv2' hzv hz1 hv1 hvz d₁ d₂
    (oddCore_frame_eq_one hodd h5 hQ hrange fr hV hψ
      (CFSG.ClassicalInvolution.G2D4Models.Twin.LiftSim.liftSimFr hlift) hx)

end Outer

end CFSG.ClassicalInvolution.NDB.SpinVertex
