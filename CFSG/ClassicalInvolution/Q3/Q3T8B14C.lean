module

public import CFSG.ClassicalInvolution.Q3.Q3T8B14A
public import CFSG.ClassicalInvolution.Q3.Q3NMRows
public import CFSG.ClassicalInvolution.Q3.Q3CHHyp51
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Facts
public import CFSG.ClassicalInvolution.Q3.Q3KBLie
public import CFSG.ClassicalInvolution.Q3.Q3NMOrth
public import CFSG.ClassicalInvolution.Q3.Q3NMTwin
public import CFSG.ClassicalInvolution.Q3.Q3TIRed

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups commutatorElement

local notation "𝔽₃" => GaloisField 3 1

section Lie


theorem range_normal_of_lieSystem {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : CFSG.ClassicalInvolution.Q3.LieSystemData3 ι X Φ) (j : ι) :
    ((D.hom j).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ (⨆ i, (D.hom i).range : Subgroup X) := by
    simp [D.generate]
  have key : ∀ g ∈ (⨆ i, (D.hom i).range : Subgroup X), ∀ m ∈ (D.hom j).range,
      g * m * g⁻¹ ∈ (D.hom j).range := by
    intro g hg
    induction hg using Subgroup.iSup_induction' with
    | hp i x hx =>
      intro m hm
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hm
      by_cases hij : i = j
      · subst hij
        exact ⟨a * b * a⁻¹, by simp⟩
      · have h := D.commute i j hij a b
        rw [h, mul_assoc, mul_inv_cancel, mul_one]
        exact ⟨b, rfl⟩
    | h1 =>
      intro m hm
      simpa using hm
    | hmul u v _ _ hu hv =>
      intro m hm
      have := hu _ (hv m hm)
      simpa [mul_assoc] using this
  exact key g hg n hn

end Lie

section Quasisimple

theorem comm_mul_central_left {S : Type} [Group S] {x y c : S} (hc : c ∈ Subgroup.center S) :
    ⁅x * c, y⁆ = ⁅x, y⁆ := by
  have hcy : c * y = y * c := (Subgroup.mem_center_iff.mp hc y).symm
  have h : c * y * c⁻¹ = y := by rw [hcy, mul_inv_cancel_right]
  calc ⁅x * c, y⁆ = x * (c * y * c⁻¹) * x⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, y⁆ := by rw [h, commutatorElement_def]

theorem comm_mul_central_right {S : Type} [Group S] {x y c : S} (hc : c ∈ Subgroup.center S) :
    ⁅x, y * c⁆ = ⁅x, y⁆ := by
  have hcx : c * x⁻¹ = x⁻¹ * c := (Subgroup.mem_center_iff.mp hc x⁻¹).symm
  have h : c * x⁻¹ * c⁻¹ = x⁻¹ := by rw [hcx, mul_inv_cancel_right]
  calc ⁅x, y * c⁆ = x * y * (c * x⁻¹ * c⁻¹) * y⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, y⁆ := by rw [h, commutatorElement_def]

theorem eq_top_of_normal_of_quasisimple {S Q : Type} [Group S] [Group Q]
    (hS : CFSG.Open.IsQuasisimple S) (ψ : S →* Q) (hψ : Function.Surjective ψ)
    {N : Subgroup Q} (hN : N.Normal) (hnc : ¬ N ≤ Subgroup.center Q) : N = ⊤ := by
  classical
  set N' : Subgroup S := N.comap ψ with hN'
  have hN'n : N'.Normal := hN.comap ψ
  have : IsSimpleGroup (S ⧸ Subgroup.center S) := hS.2
  set π := QuotientGroup.mk' (Subgroup.center S) with hπ
  have hnorm : (N'.map π).Normal := Subgroup.Normal.map hN'n π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map π) with h | h
  · exfalso
    apply hnc
    intro n hn
    obtain ⟨s, rfl⟩ := hψ n
    have hs : s ∈ N' := hn
    have h1 : π s ∈ N'.map π := Subgroup.mem_map_of_mem _ hs
    rw [h, Subgroup.mem_bot] at h1
    have hsc : s ∈ Subgroup.center S := (QuotientGroup.eq_one_iff s).mp h1
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨s', rfl⟩ := hψ q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hsc s']
  · have decomp : ∀ a : S, ∃ n ∈ N', ∃ c ∈ Subgroup.center S, a = n * c := by
      intro a
      have ha : π a ∈ N'.map π := by rw [h]; trivial
      obtain ⟨n, hn, hna⟩ := Subgroup.mem_map.mp ha
      refine ⟨n, hn, n⁻¹ * a, ?_, by group⟩
      exact QuotientGroup.eq.mp hna
    have hle : commutator S ≤ N' := by
      refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
      obtain ⟨n₁, hn₁, c₁, hc₁, rfl⟩ := decomp a
      obtain ⟨n₂, hn₂, c₂, hc₂, rfl⟩ := decomp b
      rw [comm_mul_central_left hc₁, comm_mul_central_right hc₂, commutatorElement_def]
      have h3 : n₂ * n₁⁻¹ * n₂⁻¹ ∈ N' := hN'n.conj_mem _ (N'.inv_mem hn₁) n₂
      have : n₁ * n₂ * n₁⁻¹ * n₂⁻¹ = n₁ * (n₂ * n₁⁻¹ * n₂⁻¹) := by group
      rw [this]
      exact N'.mul_mem hn₁ h3
    rw [hS.1] at hle
    rw [eq_top_iff]
    intro q _
    obtain ⟨s, rfl⟩ := hψ q
    exact hle (Subgroup.mem_top s)

theorem centralizes_of_perfect {H : Type} [Group H] {L : Subgroup H} (hL : commutator ↥L = ⊤)
    {x e : H} (he : e ∈ Subgroup.center H)
    (h : ∀ g ∈ L, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x * e) : ∀ g ∈ L, g * x = x * g := by
  have hd : ∀ g : ↥L, (g : H) * x * (g : H)⁻¹ * x⁻¹ ∈ Subgroup.center H := by
    intro g
    rcases h g g.2 with h1 | h1
    · rw [h1, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [h1]
      have hex : x * e = e * x := Subgroup.mem_center_iff.mp he x
      rw [hex, mul_inv_cancel_right]
      exact he
  let δ : ↥L →* ↥(Subgroup.center H) :=
    { toFun := fun g => ⟨(g : H) * x * (g : H)⁻¹ * x⁻¹, hd g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun g k => by
        apply Subtype.ext
        have hk := hd k
        have hg := hd g
        have e1 : (k : H) * x * (k : H)⁻¹ = ((k : H) * x * (k : H)⁻¹ * x⁻¹) * x := by group
        have hgk : (g : H) * ((k : H) * x * (k : H)⁻¹ * x⁻¹) =
            ((k : H) * x * (k : H)⁻¹ * x⁻¹) * (g : H) := Subgroup.mem_center_iff.mp hk g
        have e2 : (g : H) * ((k : H) * x * (k : H)⁻¹ * x⁻¹) * (g : H)⁻¹ =
            (k : H) * x * (k : H)⁻¹ * x⁻¹ := by
          rw [hgk, mul_inv_cancel_right]
        show ((g * k : ↥L) : H) * x * ((g * k : ↥L) : H)⁻¹ * x⁻¹ =
          ((g : H) * x * (g : H)⁻¹ * x⁻¹) * ((k : H) * x * (k : H)⁻¹ * x⁻¹)
        calc ((g * k : ↥L) : H) * x * ((g * k : ↥L) : H)⁻¹ * x⁻¹
            = (g : H) * ((k : H) * x * (k : H)⁻¹) * (g : H)⁻¹ * x⁻¹ := by
              simp only [Subgroup.coe_mul]
              group
          _ = (g : H) * (((k : H) * x * (k : H)⁻¹ * x⁻¹) * x) * (g : H)⁻¹ * x⁻¹ := by rw [← e1]
          _ = ((g : H) * ((k : H) * x * (k : H)⁻¹ * x⁻¹) * (g : H)⁻¹) *
                ((g : H) * x * (g : H)⁻¹ * x⁻¹) := by group
          _ = ((k : H) * x * (k : H)⁻¹ * x⁻¹) * ((g : H) * x * (g : H)⁻¹ * x⁻¹) := by rw [e2]
          _ = ((g : H) * x * (g : H)⁻¹ * x⁻¹) * ((k : H) * x * (k : H)⁻¹ * x⁻¹) :=
              Subgroup.mem_center_iff.mp hg _ }
  have hker : ∀ a b : ↥L, δ ⁅a, b⁆ = 1 := fun a b => by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subtype.ext (Subgroup.mem_center_iff.mp (δ a).2 (δ b : H)).symm)
  have hle : commutator ↥L ≤ δ.ker := Subgroup.commutator_le.mpr fun a _ b _ => hker a b
  rw [hL] at hle
  intro g hg
  have h1 : δ ⟨g, hg⟩ = 1 := hle (Subgroup.mem_top _)
  have h2 : g * x * g⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h1
  have h3 : g * x * g⁻¹ = x := mul_inv_eq_one.mp h2
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h3]

end Quasisimple

section Conj

variable {H : Type} [Group H]

theorem conjOnNormalizer_mul_central {L : Subgroup H}
    (y : ↥(Subgroup.normalizer (L : Set H))) {d e : H}
    (hd : d ∈ Subgroup.normalizer (L : Set H)) (he : e ∈ Subgroup.center H)
    (hye : (y : H) = d * e) : conjOnNormalizer L y = conjOnNormalizer L ⟨d, hd⟩ := by
  refine MulEquiv.ext fun q => Subtype.ext ?_
  have hey : e * (q : H) = q * e := (Subgroup.mem_center_iff.mp he q).symm
  show (y : H) * q * (y : H)⁻¹ = d * q * d⁻¹
  rw [hye, mul_inv_rev, mul_assoc d e, hey]
  group

end Conj

section Class

variable {H : Type} [Group H]


@[expose] def PSL4Class (ψ : SL(4, 𝔽₃) →* H) (τ : MulAut ↥ψ.range) : Prop :=
  τ ∈ innSubgroup ↥ψ.range ∨ ∃ D : GL (Fin 4) 𝔽₃, D * D = 1 ∧
    ∀ x, τ (ψ.rangeRestrict x) = ψ.rangeRestrict (conjSLAut D x)

theorem autOddFreeOn_psl4 [Finite H] (ψ : SL(4, 𝔽₃) →* H)
    (hker : ψ.ker ≤ Subgroup.center SL(4, 𝔽₃)) : AutOddFreeOn ↥ψ.range (PSL4Class ψ) :=
  autOddFreeOn_PSL (m := 3) (by norm_num) ψ.rangeRestrict ψ.rangeRestrict_surjective
    (by rwa [MonoidHom.ker_rangeRestrict])

theorem psl4Class_inducedImage [Finite H] (ψ : SL(4, 𝔽₃) →* H) (E : Subgroup H) {zb w : H}
    {y' : SL(4, 𝔽₃)} {D : GL (Fin 4) 𝔽₃} (hD2 : D * D = 1) (hy'2 : y' * y' = 1)
    (hDy : (D : Matrix (Fin 4) (Fin 4) 𝔽₃) * (y' : Matrix (Fin 4) (Fin 4) 𝔽₃) =
      (y' : Matrix (Fin 4) (Fin 4) 𝔽₃) * D)
    (hzb : zb ∈ ψ.range) (hzy : ∃ e' ∈ Subgroup.center H, zb = ψ y' * e')
    (hwN : w ∈ Subgroup.normalizer (ψ.range : Set H))
    (hw : ∀ g, w * ψ g * w⁻¹ = ψ (conjSLAut D g))
    (hE : ∀ e ∈ E, ∃ d ∈ ({1, zb, w, zb * w} : Set H), ∃ e' ∈ Subgroup.center H, e = d * e') :
    ∀ x ∈ inducedImage ψ.range E, x ≠ 1 →
      PSL4Class ψ ((x : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range) := by
  classical
  intro x hx hx1
  obtain ⟨y, hyE, rfl⟩ := Subgroup.mem_map.mp hx
  have hyE' : (y : H) ∈ E := hyE
  obtain ⟨d, hd, e', he', hye⟩ := hE _ hyE'
  have hxy : (((toInducedAutOn ψ.range y : ↥(inducedAutOn ψ.range))) : MulAut ↥ψ.range) =
      conjOnNormalizer ψ.range y := rfl
  rw [hxy]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with h1 | h2 | h3 | h4
  · exfalso
    apply hx1
    apply Subtype.ext
    show conjOnNormalizer ψ.range y = 1
    rw [conjOnNormalizer_eq_conj y (Subgroup.one_mem _) he' (by rw [hye, h1])]
    exact map_one _
  · rw [h2] at hye
    left
    rw [conjOnNormalizer_eq_conj y hzb he' hye]
    exact ⟨⟨zb, hzb⟩, rfl⟩
  · rw [h3] at hye
    right
    rw [conjOnNormalizer_mul_central y hwN he' hye]
    exact ⟨D, hD2, fun g => Subtype.ext (hw g)⟩
  · rw [h4] at hye
    right
    obtain ⟨e'', he'', hzbe⟩ := hzy
    have hew : e'' * w = w * e'' := (Subgroup.mem_center_iff.mp he'' w).symm
    have hy2 : (y : H) = (ψ y' * w) * (e'' * e') := by
      rw [hye, hzbe]
      calc ψ y' * e'' * w * e' = ψ y' * (e'' * w) * e' := by rw [mul_assoc (ψ y') e'' w]
        _ = ψ y' * (w * e'') * e' := by rw [hew]
        _ = ψ y' * w * (e'' * e') := by simp only [mul_assoc]
    have hdN : ψ y' * w ∈ Subgroup.normalizer (ψ.range : Set H) :=
      Subgroup.mul_mem _ (Subgroup.le_normalizer ⟨y', rfl⟩) hwN
    rw [conjOnNormalizer_mul_central y hdN (Subgroup.mul_mem _ he'' he') hy2]
    have hcomm : D * Matrix.SpecialLinearGroup.toGL y' = Matrix.SpecialLinearGroup.toGL y' * D :=
      Units.ext hDy
    have hDD : (Matrix.SpecialLinearGroup.toGL y' * D) * (Matrix.SpecialLinearGroup.toGL y' * D) =
        1 := by
      calc Matrix.SpecialLinearGroup.toGL y' * D * (Matrix.SpecialLinearGroup.toGL y' * D)
          = Matrix.SpecialLinearGroup.toGL y' * (D * Matrix.SpecialLinearGroup.toGL y') * D := by
            group
        _ = Matrix.SpecialLinearGroup.toGL y' * (Matrix.SpecialLinearGroup.toGL y' * D) * D := by
            rw [hcomm]
        _ = (Matrix.SpecialLinearGroup.toGL y' * Matrix.SpecialLinearGroup.toGL y') * (D * D) := by
            group
        _ = 1 := by rw [← map_mul, hy'2, map_one, hD2, mul_one]
    refine ⟨Matrix.SpecialLinearGroup.toGL y' * D, hDD, fun g => Subtype.ext ?_⟩
    show ψ y' * w * ψ g * (ψ y' * w)⁻¹ =
      ψ (conjSLAut (Matrix.SpecialLinearGroup.toGL y' * D) g)
    have h5 : ψ y' * w * ψ g * (ψ y' * w)⁻¹ = ψ y' * (w * ψ g * w⁻¹) * (ψ y')⁻¹ := by group
    rw [h5, hw g, conjSLAut_mul, E4G3.conjSLAut_toGL]
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

end Class

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
