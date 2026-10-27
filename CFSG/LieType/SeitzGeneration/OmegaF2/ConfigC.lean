module

public import CFSG.LieType.SeitzGeneration.OmegaF2.ConfigB
public import CFSG.LieType.SeitzGeneration.OmegaF2.ConfigA

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.LieType.SeitzGeneration.RootPairOrth

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {k : Subfield K}
  {Q₀ : QuadraticForm k (Fin d → k)}

private theorem configC_solve2 {a b A B C D : K} (h1 : a * A + b * B = 0)
    (h2 : a * C + b * D = 0) (hdet : A * D - B * C ≠ 0) : a = 0 ∧ b = 0 := by
  have ha : a * (A * D - B * C) = 0 := by linear_combination D * h1 - B * h2
  have hb : b * (A * D - B * C) = 0 := by linear_combination A * h2 - C * h1
  exact ⟨(mul_eq_zero.mp ha).resolve_right hdet, (mul_eq_zero.mp hb).resolve_right hdet⟩

private theorem configC_coeff_five {x y w c₁ c₂ : Fin d → K}
    (hind : LinearIndependent K ![x, y, w, c₁, c₂]) {a b c e f : K}
    (h : a • x + b • y + c • w + e • c₁ + f • c₂ = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 ∧ f = 0 := by
  have hg := Fintype.linearIndependent_iff.mp hind ![a, b, c, e, f]
    (by simpa [Fin.sum_univ_five] using h)
  exact ⟨hg 0, hg 1, hg 2, hg 3, hg 4⟩

private theorem configC_mem_span_four {x y c₁ c₂ v : Fin d → K}
    (h : v ∈ Submodule.span K ({x, y, c₁, c₂} : Set (Fin d → K))) :
    ∃ a b p q : K, v = a • x + b • y + p • c₁ + q • c₂ := by
  obtain ⟨a, z, hz, rfl⟩ := Submodule.mem_span_insert.mp h
  obtain ⟨b, z', hz', rfl⟩ := Submodule.mem_span_insert.mp hz
  obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.mp hz'
  exact ⟨a, b, p, q, by abel⟩

theorem linearIndependent_five {x y w c₁ c₂ : Fin d → K} (hx : Q x = 0) (hy : Q y = 0)
    (hxy : polar Q x y = 0) (hc₁ : Q c₁ = 0) (hc₂ : Q c₂ = 0) (hc₁₂ : polar Q c₁ c₂ = 0)
    (hΔ : pairDet Q c₁ c₂ x y ≠ 0) (hwx : polar Q w x = 0) (hwy : polar Q w y = 0)
    (hwc₁ : polar Q w c₁ = 0) (hwc₂ : polar Q w c₂ = 0) (hw : w ≠ 0) :
    LinearIndependent K ![x, y, w, c₁, c₂] := by
  have hΔ₁ : polar Q x c₁ * polar Q y c₂ - polar Q y c₁ * polar Q x c₂ ≠ 0 := by
    intro h
    apply hΔ
    unfold pairDet
    linear_combination h
  have hΔ₂ : polar Q x c₁ * polar Q y c₂ - polar Q x c₂ * polar Q y c₁ ≠ 0 := hΔ
  have hpc₁ : polar Q c₁ c₁ = 0 := by rw [polar_self, hc₁, smul_zero]
  have hpc₂ : polar Q c₂ c₂ = 0 := by rw [polar_self, hc₂, smul_zero]
  have hpx : polar Q x x = 0 := by rw [polar_self, hx, smul_zero]
  have hpy : polar Q y y = 0 := by rw [polar_self, hy, smul_zero]
  have hc₂₁ : polar Q c₂ c₁ = 0 := by rw [polar_comm]; exact hc₁₂
  have hxw : polar Q x w = 0 := by rw [polar_comm]; exact hwx
  have hyw : polar Q y w = 0 := by rw [polar_comm]; exact hwy
  have hyx : polar Q y x = 0 := by rw [polar_comm]; exact hxy
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • x + g 1 • y + g 2 • w + g 3 • c₁ + g 4 • c₂ = 0 := by
    simpa [Fin.sum_univ_five] using hg
  have e1 := congrArg (fun v => polar Q v c₁) hg'
  have e2 := congrArg (fun v => polar Q v c₂) hg'
  have e3 := congrArg (fun v => polar Q x v) hg'
  have e4 := congrArg (fun v => polar Q y v) hg'
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
    polar_zero_left, polar_zero_right, smul_eq_mul, hwc₁, hwc₂, hpc₁, hpc₂, hc₂₁, hc₁₂,
    hpx, hpy, hxy, hxw, hyw, hyx, mul_zero, add_zero, zero_add] at e1 e2 e3 e4
  obtain ⟨h0, h1⟩ := configC_solve2 e1 e2 hΔ₁
  obtain ⟨h3, h4⟩ := configC_solve2 e3 e4 hΔ₂
  have hw2 : g 2 • w = 0 := by
    rw [h0, h1, h3, h4] at hg'
    simpa using hg'
  have h2 : g 2 = 0 := (smul_eq_zero.mp hw2).resolve_right hw
  intro i
  fin_cases i <;> simp [h0, h1, h2, h3, h4]

variable (S : HypCoord Q)

theorem exists_perp_singular (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q)
    (htail : TailAnisotropic S) {c₁ c₂ : Fin d → K} (hbad : BadPlane Q k c₁ c₂)
    {x y : Fin d → K} (hx : IsRat k x) (hy : IsRat k y) (hQx : Q x = 0) (hQy : Q y = 0)
    (hxy : polar Q x y = 0) (hΔ : pairDet Q c₁ c₂ x y ≠ 0) :
    ∃ w : Fin d → K, IsRat k w ∧ Q w = 0 ∧ polar Q w x = 0 ∧ polar Q w y = 0 ∧
      polar Q w c₁ = 0 ∧ polar Q w c₂ = 0 ∧ w ≠ 0 := by
  obtain ⟨h, hh, a, ha, b, hb, _hba, _hbs, hxh, ε, _hε, hyh⟩ :=
    exists_move_plane S hk hext htail hx hy hQx hQy hxy (linearIndependent_of_pairDet_ne hΔ).1
  obtain ⟨c, hcH, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, S.star a, S.star b} : Finset (Fin d))) (t := S.hyp)
    (lt_of_le_of_lt Finset.card_le_four (by have := S.card_hyp; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hca, hcb, hcsa, hcsb⟩ := hc
  have hiso : ∀ v, Q (h v) = Q v := fun v =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (ratEichlerGroup_le_orthogonalGroup hh) v
  have hpolar : ∀ u v, polar Q (h u) (h v) = polar Q u v := by
    intro u v
    unfold polar
    rw [← map_add h u v]
    simp only [hiso]
  have hzr : IsRat k (h⁻¹ (Pi.single c 1 : Fin d → K)) :=
    ratEichlerGroup_isRat hext (inv_mem hh) (isRat_single k c)
  have hhz : h (h⁻¹ (Pi.single c 1 : Fin d → K)) = Pi.single c 1 := h.apply_symm_apply _
  generalize h⁻¹ (Pi.single c 1 : Fin d → K) = z at hzr hhz
  have hac : S.star a ≠ c := Ne.symm hcsa
  have hbc : S.star b ≠ c := Ne.symm hcsb
  have hQz : Q z = 0 := by
    rw [← hiso z, hhz]
    exact S.Q_single c hcH
  have hxz : polar Q x z = 0 := by
    rw [← hpolar x z, hxh, hhz, S.polar_single a ha, Pi.single_apply, if_neg hac]
  have hyz : polar Q y z = 0 := by
    rw [← hpolar y z, hyh, hhz]
    simp [polar_add_left, polar_smul_left, S.polar_single a ha, S.polar_single b hb,
      Pi.single_apply, hac, hbc]
  obtain ⟨hα, hβ⟩ := hbad x y z hx hy hzr hQx hQy hQz hxy hxz hyz hΔ
  obtain ⟨hrad1, hrad2, hrad3⟩ := radical_vector_perp hQx hQy hQz hxy hxz hyz
    (pairDet Q c₁ c₂ y z / pairDet Q c₁ c₂ x y) (pairDet Q c₁ c₂ z x / pairDet Q c₁ c₂ x y)
  obtain ⟨hp1, hp2⟩ := polar_radical_vector (z := z) hΔ
  refine ⟨z + (pairDet Q c₁ c₂ y z / pairDet Q c₁ c₂ x y) • x +
    (pairDet Q c₁ c₂ z x / pairDet Q c₁ c₂ x y) • y, ?_, hrad1, hrad2, hrad3, hp1, hp2, ?_⟩
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact k.add_mem (k.add_mem (hzr i) (k.mul_mem hα (hx i))) (k.mul_mem hβ (hy i))
  · intro hw0
    have hsum : h (z + (pairDet Q c₁ c₂ y z / pairDet Q c₁ c₂ x y) • x +
        (pairDet Q c₁ c₂ z x / pairDet Q c₁ c₂ x y) • y) = 0 := by
      rw [hw0, map_zero]
    simp only [map_add, map_smul, hhz, hxh, hyh] at hsum
    have hc := congrFun hsum c
    simp [Pi.single_apply, hca, hcb] at hc

theorem mem_span_of_three {x y w c₁ c₂ v : Fin d → K}
    (hind : LinearIndependent K ![x, y, w, c₁, c₂])
    (h1 : v ∈ Submodule.span K {x, y, c₁, c₂}) (h2 : v ∈ Submodule.span K {x + w, y, c₁, c₂})
    (h3 : v ∈ Submodule.span K {x, y + w, c₁, c₂}) : v ∈ Submodule.span K {c₁, c₂} := by
  obtain ⟨a, b, p, q, hv1⟩ := configC_mem_span_four h1
  obtain ⟨a', b', p', q', hv2⟩ := configC_mem_span_four h2
  obtain ⟨a'', b'', p'', q'', hv3⟩ := configC_mem_span_four h3
  have hr1 := configC_coeff_five hind (a := a - a') (b := b - b') (c := -a') (e := p - p')
    (f := q - q') (by linear_combination (norm := module) hv2 - hv1)
  have hr2 := configC_coeff_five hind (a := a - a'') (b := b - b'') (c := -b'')
    (e := p - p'') (f := q - q'') (by linear_combination (norm := module) hv3 - hv1)
  have ha' : a' = 0 := neg_eq_zero.mp hr1.2.2.1
  have hb'' : b'' = 0 := neg_eq_zero.mp hr2.2.2.1
  subst ha' hb''
  have hr3 := configC_coeff_five hind (a := -a'') (b := b') (c := 0) (e := p' - p'')
    (f := q' - q'') (by linear_combination (norm := module) hv3 - hv2)
  have hb' : b' = 0 := hr3.2.1
  subst hb'
  refine Submodule.mem_span_pair.mpr ⟨p', q', ?_⟩
  rw [hv2]
  simp

theorem sigma_stable_of_bad [CharP K 2] (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q)
    (hnd : (polarBilin Q).Nondegenerate) (htail : TailAnisotropic S) {σ : K ≃+* K}
    (hσk : ∀ x, x ∈ k ↔ σ x = x) {c₁ c₂ : Fin d → K} (hc₁ : Q c₁ = 0) (hc₂ : Q c₂ = 0)
    (hc₁₂ : polar Q c₁ c₂ = 0) (hind : LinearIndependent K ![c₁, c₂])
    (hbad : BadPlane Q k c₁ c₂) :
    sigmaVec σ c₁ ∈ Submodule.span K {c₁, c₂} ∧ sigmaVec σ c₂ ∈ Submodule.span K {c₁, c₂} := by
  obtain ⟨x, y, hx, hy, hQx, hQy, hxy, hΔ⟩ :=
    exists_rational_plane_pairDet_ne S hext hnd htail hc₁ hc₂ hc₁₂ hind
  obtain ⟨w, hwr, hQw, hwx, hwy, hwc₁, hwc₂, hw0⟩ :=
    exists_perp_singular S hk hext htail hbad hx hy hQx hQy hxy hΔ
  have hind5 := linearIndependent_five hQx hQy hxy hc₁ hc₂ hc₁₂ hΔ hwx hwy hwc₁ hwc₂ hw0
  have hxw : polar Q x w = 0 := by rw [polar_comm]; exact hwx
  have hyw : polar Q y w = 0 := by rw [polar_comm]; exact hwy
  have hQxw : Q (x + w) = 0 := by
    simp [QuadraticMap.map_add, hQx, hQw, hxw]
  have hQyw : Q (y + w) = 0 := by
    simp [QuadraticMap.map_add, hQy, hQw, hyw]
  have hxyw : polar Q (x + w) y = 0 := by simp [polar_add_left, hxy, hwy]
  have hxyw' : polar Q x (y + w) = 0 := by simp [polar_add_right, hxy, hxw]
  have hΔw : pairDet Q c₁ c₂ (x + w) y ≠ 0 := by
    have e : pairDet Q c₁ c₂ (x + w) y = pairDet Q c₁ c₂ x y := by
      simp only [pairDet, polar_add_left, hwc₁, hwc₂, add_zero]
    rw [e]
    exact hΔ
  have hΔw' : pairDet Q c₁ c₂ x (y + w) ≠ 0 := by
    have e : pairDet Q c₁ c₂ x (y + w) = pairDet Q c₁ c₂ x y := by
      simp only [pairDet, polar_add_left, hwc₁, hwc₂, add_zero]
    rw [e]
    exact hΔ
  have hA := sigmaVec_mem_span_of_bad S hk hext hnd htail hσk hc₁ hc₂ hc₁₂ hbad hx hy
    hQx hQy hxy hΔ
  have hB := sigmaVec_mem_span_of_bad S hk hext hnd htail hσk hc₁ hc₂ hc₁₂ hbad
    (IsRat.add hx hwr) hy hQxw hQy hxyw hΔw
  have hC := sigmaVec_mem_span_of_bad S hk hext hnd htail hσk hc₁ hc₂ hc₁₂ hbad
    hx (IsRat.add hy hwr) hQx hQyw hxyw' hΔw'
  exact ⟨mem_span_of_three hind5 hA.1 hB.1 hC.1, mem_span_of_three hind5 hA.2 hB.2 hC.2⟩

end CFSG.LieType.SeitzGeneration.OmegaF2
