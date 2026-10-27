module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Frame

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Lemma52Proof
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement MatrixGroups
open CFSG.ClassicalGroups.Orthogonal.Small QuadraticMap

section Abstract

variable {S G₀ H : Type} [Group S] [Group G₀] [Group H]

theorem eq_one_of_perfect_center' {K G : Type*} [Group K] [Group.IsPerfect K] [Group G]
    (f : K →* Subgroup.center G) : f = 1 := by
  have hp : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  ext x
  have h1 : (⟨f x, x, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val h1

theorem mem_center_of_commutators_central [Group.IsPerfect S] {s : S}
    (h : ∀ t : S, ⁅s, t⁆ ∈ Subgroup.center S) : s ∈ Subgroup.center S := by
  have h1 : (QuotientGroup.mk' (Subgroup.center S) s) ∈
      Subgroup.center (S ⧸ Subgroup.center S) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center S) y
    have e1 : s * t = ⁅s, t⁆ * (t * s) := by simp only [commutatorElement_def]; group
    have e2 : QuotientGroup.mk' (Subgroup.center S) ⁅s, t⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (h t)
    have h3 : QuotientGroup.mk' (Subgroup.center S) (s * t) =
        QuotientGroup.mk' (Subgroup.center S) (t * s) := by
      rw [e1, map_mul, e2, one_mul]
    calc QuotientGroup.mk' (Subgroup.center S) t * QuotientGroup.mk' (Subgroup.center S) s
        = QuotientGroup.mk' (Subgroup.center S) (t * s) := (map_mul _ _ _).symm
      _ = QuotientGroup.mk' (Subgroup.center S) (s * t) := h3.symm
      _ = QuotientGroup.mk' (Subgroup.center S) s * QuotientGroup.mk' (Subgroup.center S) t :=
        map_mul _ _ _
  rw [Group.IsPerfect.center_quotient_center_eq_bot S, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff s).mp h1

theorem mem_normalizer_range (ψ : S →* H) (s : S) :
    ψ s ∈ Subgroup.normalizer (ψ.range : Set H) :=
  Subgroup.le_normalizer (⟨s, rfl⟩ : ψ s ∈ ψ.range)

theorem exists_hom_inducedAutOn [Group.IsPerfect S] (π : S →* G₀)
    (hπ : Function.Surjective π) (hπk : π.ker ≤ Subgroup.center S) (ψ : S →* H)
    (hψ : ψ.ker ≤ Subgroup.center S) :
    ∃ e : G₀ →* ↥(inducedAutOn ψ.range),
      (∀ s, e (π s) = toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩) ∧
      (∀ g, e g = 1 → g ∈ Subgroup.center G₀) ∧ e.range.Normal ∧
      ∀ x : ↥(inducedAutOn ψ.range), (∀ y ∈ e.range, x * y = y * x) → x = 1 := by
  classical
  set L : Subgroup H := ψ.range with hL
  let ε : S →* ↥(inducedAutOn L) :=
    (toInducedAutOn L).comp (ψ.codRestrict (Subgroup.normalizer (L : Set H))
      (fun s => mem_normalizer_range ψ s))
  have hεapply : ∀ s, ε s = toInducedAutOn L ⟨ψ s, mem_normalizer_range ψ s⟩ := fun s => rfl
  have hεk : π.ker ≤ ε.ker := by
    intro s hs
    rw [MonoidHom.mem_ker, hεapply]
    apply toInducedAutOn_eq_one_of_commute
    rintro _ ⟨t, rfl⟩
    have hc := Subgroup.mem_center_iff.mp (hπk hs) t
    show ψ s * ψ t = ψ t * ψ s
    rw [← map_mul, ← map_mul, hc]
  let e := MonoidHom.liftOfSurjective π hπ ⟨ε, hεk⟩
  have he : ∀ s, e (π s) = ε s := fun s =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨ε, hεk⟩ s
  refine ⟨e, fun s => (he s).trans (hεapply s), ?_, ?_, ?_⟩
  ·
    intro g hg
    obtain ⟨s, rfl⟩ := hπ g
    rw [he, hεapply] at hg
    have hcomm := commute_of_toInducedAutOn_eq_one L (mem_normalizer_range ψ s) hg
    have hs : s ∈ Subgroup.center S := by
      refine mem_center_of_commutators_central fun t => hψ ?_
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm (ψ t) ⟨t, rfl⟩)
    rw [Subgroup.mem_center_iff]
    intro g'
    obtain ⟨t, rfl⟩ := hπ g'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hs t]
  ·
    refine ⟨fun y hy x => ?_⟩
    obtain ⟨g, rfl⟩ := hy
    obtain ⟨s, rfl⟩ := hπ g
    obtain ⟨n, rfl⟩ := MonoidHom.rangeRestrict_surjective (conjOnNormalizer L) x
    have hmem : (n : H) * ψ s * (n : H)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp n.2 (ψ s)).mp ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := hmem
    refine ⟨π s', ?_⟩
    have : (⟨ψ s', mem_normalizer_range ψ s'⟩ : ↥(Subgroup.normalizer (L : Set H))) =
        n * ⟨ψ s, mem_normalizer_range ψ s⟩ * n⁻¹ := Subtype.ext hs'
    rw [he s', hεapply s', this, he s, hεapply s]
    simp only [map_mul, map_inv]
    rfl
  ·
    intro x hx
    obtain ⟨n, rfl⟩ := MonoidHom.rangeRestrict_surjective (conjOnNormalizer L) x
    have hmemL : ∀ s, (n : H) * ψ s * (n : H)⁻¹ * (ψ s)⁻¹ ∈ L := fun s =>
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp n.2 (ψ s)).mp ⟨s, rfl⟩) (L.inv_mem ⟨s, rfl⟩)
    have hcent : ∀ s, (⟨(n : H) * ψ s * (n : H)⁻¹ * (ψ s)⁻¹, hmemL s⟩ : ↥L) ∈
        Subgroup.center ↥L := by
      intro s
      set m : ↥(Subgroup.normalizer (L : Set H)) := ⟨ψ s, mem_normalizer_range ψ s⟩ with hm
      have hxc := hx (ε s) ⟨π s, he s⟩
      rw [hεapply] at hxc
      have hcomm : toInducedAutOn L n * toInducedAutOn L m =
          toInducedAutOn L m * toInducedAutOn L n :=
        hxc
      have h1 : toInducedAutOn L (n * m * n⁻¹ * m⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hcomm]
        group
      have hc := commute_of_toInducedAutOn_eq_one L (n * m * n⁻¹ * m⁻¹).2 h1
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g.1 g.2).symm
    have hct : ∀ s t : S, ψ s * ((n : H) * ψ t * (n : H)⁻¹ * (ψ t)⁻¹) =
        ((n : H) * ψ t * (n : H)⁻¹ * (ψ t)⁻¹) * ψ s := fun s t => by
      have := Subgroup.mem_center_iff.mp (hcent t) ⟨ψ s, ⟨s, rfl⟩⟩
      exact congrArg Subtype.val this
    let f : S →* ↥(Subgroup.center ↥L) :=
      { toFun := fun s => ⟨⟨(n : H) * ψ s * (n : H)⁻¹ * (ψ s)⁻¹, hmemL s⟩, hcent s⟩
        map_one' := Subtype.ext (Subtype.ext (by simp))
        map_mul' := fun s t => Subtype.ext (Subtype.ext (by
          show (n : H) * ψ (s * t) * (n : H)⁻¹ * (ψ (s * t))⁻¹ =
            ((n : H) * ψ s * (n : H)⁻¹ * (ψ s)⁻¹) * ((n : H) * ψ t * (n : H)⁻¹ * (ψ t)⁻¹)
          calc (n : H) * ψ (s * t) * (n : H)⁻¹ * (ψ (s * t))⁻¹
              = ((n : H) * ψ s * (n : H)⁻¹ * (ψ s)⁻¹) *
                (ψ s * ((n : H) * ψ t * (n : H)⁻¹ * (ψ t)⁻¹) * (ψ s)⁻¹) := by
                simp only [map_mul, mul_inv_rev]; group
            _ = _ := by rw [hct s t, mul_inv_cancel_right])) }
    have hf : f = 1 := eq_one_of_perfect_center' f
    have hcommn : ∀ y ∈ L, (n : H) * y = y * (n : H) := by
      rintro _ ⟨s, rfl⟩
      have := congrArg
        (fun φ : S →* ↥(Subgroup.center ↥L) => ((φ s : ↥(Subgroup.center ↥L)) : ↥L)) hf
      have h2 : (n : H) * ψ s * (n : H)⁻¹ * (ψ s)⁻¹ = 1 := congrArg Subtype.val (this)
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
      exact h2
    exact toInducedAutOn_eq_one_of_commute L n.2 hcommn

end Abstract

section Spin

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [Finite F] [FiniteDimensional F V]

theorem exists_hom_spin (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank F V) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] {H : Type} [Group H] (ψ : spinGroup Q →* H)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) :
    ∃ e : ↥(elementaryGroup Q) →* ↥(inducedAutOn ψ.range),
      (∀ (s : spinGroup Q) (hs : spinAction Q s ∈ elementaryGroup Q),
        e ⟨spinAction Q s, hs⟩ = toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩) ∧
      KerScalar Q e ∧ e.range.Normal ∧
      ∀ x : ↥(inducedAutOn ψ.range), (∀ y ∈ e.range, x * y = y * x) → x = 1 := by
  have hmem : ∀ s : spinGroup Q, spinAction Q s ∈ elementaryGroup Q := fun s => by
    rw [← hrange]; exact ⟨s, rfl⟩
  let π : spinGroup Q →* ↥(elementaryGroup Q) := (spinAction Q).codRestrict _ hmem
  have hπ : Function.Surjective π := by
    rintro ⟨g, hg⟩
    rw [← hrange] at hg
    obtain ⟨s, rfl⟩ := hg
    exact ⟨s, rfl⟩
  have hπk : π.ker ≤ Subgroup.center (spinGroup Q) := fun s hs =>
    ker_spinAction_le_center Q (by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact congrArg Subtype.val hs)
  obtain ⟨e, he, hker, hnorm, hcent⟩ := exists_hom_inducedAutOn π hπ hπk ψ hψ
  refine ⟨e, fun s hs => he s, ?_, hnorm, hcent⟩
  intro g hg
  have hgc := hker g hg
  have h2 := two_ne_zero_of_odd_card hodd
  have hA := hasAnisoPerp_of_three_le_finrank hQ h3
  obtain ⟨P, -, -⟩ := CFSG.ClassicalInvolution.Asc77.exists_hypPair_le hodd
    (polarNondegOn_top hQ) (by rwa [finrank_top])
  refine mem_scalars_of_commute_eichler h2 hQ hA P (elementaryGroup_le_orthogonalGroup Q g.2) ?_
  intro u w _ _
  have := Subgroup.mem_center_iff.mp hgc ⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩
  exact (congrArg Subtype.val this).symm

theorem alphaOf_spin_frame_eq_bot (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (fr : Frame Q) {A A' : SL(2, F)}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1) (hV : 7 ≤ Module.finrank F V)
    {s₁ s₂ : spinGroup Q} (hs₁ : spinAction Q s₁ = twinInv fr A A')
    (hs₂ : spinAction Q s₂ = fr.La (-1)) {H : Type} [Group H] [Finite H]
    (ψ : spinGroup Q →* H) (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ s₁, mem_normalizer_range ψ s₁⟩,
      toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩} :
        Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  obtain ⟨e, he, hker, hnorm, hcent⟩ :=
    exists_hom_spin hodd hQ (by omega) hrange ψ hψ
  have : Finite ↥(inducedAutOn ψ.range) := inferInstance
  have := hnorm
  have key := alphaOf_frame_twin_eq_bot fr hodd h5 hQ hA hA' hV e hker hcent
  have hm₁ : spinAction Q s₁ ∈ elementaryGroup Q := hs₁ ▸ twinInv_mem_elementaryGroup fr A A'
  have hm₂ : spinAction Q s₂ ∈ elementaryGroup Q := hs₂ ▸ fr.La_mem_elementaryGroup (-1)
  have h₁ : e ⟨twinInv fr A A', twinInv_mem_elementaryGroup fr A A'⟩ =
      toInducedAutOn ψ.range ⟨ψ s₁, mem_normalizer_range ψ s₁⟩ := by
    have : (⟨twinInv fr A A', twinInv_mem_elementaryGroup fr A A'⟩ : ↥(elementaryGroup Q)) =
        ⟨spinAction Q s₁, hm₁⟩ := Subtype.ext hs₁.symm
    rw [this]
    exact he s₁ hm₁
  have h₂ : e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩ =
      toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩ := by
    have : (⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩ : ↥(elementaryGroup Q)) =
        ⟨spinAction Q s₂, hm₂⟩ := Subtype.ext hs₂.symm
    rw [this]
    exact he s₂ hm₂
  rw [h₁, h₂] at key
  exact key

end Spin

end CFSG.ClassicalInvolution.ModelFacts.Orth15
