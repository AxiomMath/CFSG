module

public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.PPrime

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped MatrixGroups commutatorElement

theorem ne_zero_of_five_le_pow {p f : ℕ} (hq : 5 ≤ p ^ f) : f ≠ 0 := by
  rintro rfl
  simp at hq

section Lift

theorem exists_lift_of_noCover {X₀ : Type} [Group X₀] [Finite X₀] [Group.IsPerfect X₀]
    (hX₀ : NoCover.{0} Odd X₀) {Y X : Type} [Group Y] [Finite Y] [Group X] (π : Y →* X)
    (hcen : π.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card π.ker)) (θ : X₀ →* X)
    (hθ : θ.range ≤ π.range) : ∃ θ' : X₀ →* Y, π.comp θ' = θ := by
  classical
  let P : Subgroup (X₀ × Y) :=
    (θ.comp (MonoidHom.fst _ _)).eqLocus (π.comp (MonoidHom.snd _ _))
  have hmemP : ∀ x : X₀ × Y, x ∈ P ↔ θ x.1 = π x.2 := fun x => Iff.rfl
  let pr : P →* X₀ := (MonoidHom.fst _ _).comp P.subtype
  have hpr : Function.Surjective pr := by
    intro s
    obtain ⟨y, hy⟩ := hθ ⟨s, rfl⟩
    exact ⟨⟨(s, y), (hmemP _).mpr hy.symm⟩, rfl⟩
  have hker : ∀ q : P, q ∈ pr.ker → π (q : X₀ × Y).2 = 1 := by
    intro q hq
    have h1 : (q : X₀ × Y).1 = 1 := hq
    have := (hmemP _).mp q.2
    rw [h1, map_one] at this
    exact this.symm
  have hcen' : pr.ker ≤ Subgroup.center P := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro r
    have h1 : (q : X₀ × Y).1 = 1 := hq
    have h2 : (q : X₀ × Y).2 ∈ Subgroup.center Y :=
      hcen (MonoidHom.mem_ker.mpr (hker q hq))
    apply Subtype.ext
    apply Prod.ext
    · simp [h1]
    · exact (Subgroup.mem_center_iff.mp h2 _)
  have hodd' : Odd (Nat.card pr.ker) := by
    refine hodd.of_dvd_nat ?_
    let g : pr.ker →* π.ker :=
      { toFun := fun q => ⟨(q.1 : X₀ × Y).2, MonoidHom.mem_ker.mpr (hker q.1 q.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Subgroup.card_dvd_of_injective g fun q₁ q₂ h => ?_
    have h1 : (q₁.1 : X₀ × Y).1 = 1 := q₁.2
    have h2 : (q₂.1 : X₀ × Y).1 = 1 := q₂.2
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (h1.trans h2.symm) (congrArg Subtype.val h)
  have hsurj' := surjective_comp_commutator' pr hpr
  have hperf : Group.IsPerfect (commutator P) := isPerfect_commutator' pr hpr hcen'
  have hcen'' : (pr.comp (commutator P).subtype).ker ≤ Subgroup.center (commutator P) := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hcen' hq) (r : P))
  have hodd'' : Odd (Nat.card (pr.comp (commutator P).subtype).ker) := by
    refine hodd'.of_dvd_nat ?_
    let g : (pr.comp (commutator P).subtype).ker →* pr.ker :=
      { toFun := fun q => ⟨(q.1 : P), q.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Subgroup.card_dvd_of_injective g fun q₁ q₂ h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : pr.ker => (x : P)) h))
  have hbot := hX₀ ↥(commutator P) (pr.comp (commutator P).subtype) hsurj' hcen'' hodd''
  have hinj : Function.Injective (pr.comp (commutator P).subtype) :=
    (MonoidHom.ker_eq_bot_iff _).mp hbot
  let e : commutator P ≃* X₀ := MulEquiv.ofBijective _ ⟨hinj, hsurj'⟩
  refine ⟨(MonoidHom.snd _ _).comp (P.subtype.comp ((commutator P).subtype.comp
    e.symm.toMonoidHom)), ?_⟩
  ext s
  have h1 : pr ((e.symm s : commutator P) : P) = s := e.apply_symm_apply s
  have h2 := (hmemP _).mp ((e.symm s : commutator P) : P).2
  have h3 : ((e.symm s : commutator P) : P).1.1 = s := h1
  rw [h3] at h2
  exact h2.symm

end Lift

section Member

variable {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal]

theorem exists_lift_map_eq {X₀ : Type} [Group X₀] [Finite X₀] [Group.IsPerfect X₀]
    (hX₀ : NoCover.{0} Odd X₀) (hOc : O ≤ Subgroup.center Y) (hOodd : Odd (Nat.card O))
    (θbar : X₀ →* Y ⧸ O) (hker : θbar.ker ≤ Subgroup.center X₀) {P : Subgroup X₀}
    (hP : P ≤ ⁅P, P⁆) {K : Subgroup Y} (hK : K ≤ ⁅K, K⁆)
    (hKP : K.map (QuotientGroup.mk' O) = P.map θbar) :
    ∃ θ : X₀ →* Y, (QuotientGroup.mk' O).comp θ = θbar ∧ θ.ker ≤ Subgroup.center X₀ ∧
      K = P.map θ := by
  have hπker : (QuotientGroup.mk' O).ker ≤ Subgroup.center Y := by
    rw [QuotientGroup.ker_mk']
    exact hOc
  have hπodd : Odd (Nat.card (QuotientGroup.mk' O).ker) := by
    rw [QuotientGroup.ker_mk']
    exact hOodd
  obtain ⟨θ, hθ⟩ := exists_lift_of_noCover hX₀ (QuotientGroup.mk' O) hπker hπodd θbar
    (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective O)]; exact le_top)
  refine ⟨θ, hθ, ?_, ?_⟩
  · intro x hx
    apply hker
    rw [MonoidHom.mem_ker, ← hθ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one]
  · have hmap : (P.map θ).map (QuotientGroup.mk' O) = P.map θbar := by
      rw [Subgroup.map_map, hθ]
    have hperf : P.map θ ≤ ⁅P.map θ, P.map θ⁆ := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.map_mono hP
    exact eq_of_map_mk_eq_of_central hOc hK hperf (hKP.trans hmap.symm)

end Member

theorem nonempty_equiv_of_map_eq {S X₀ Y : Type*} [Group S] [Group X₀] [Group Y] (β : S →* X₀)
    (θ : X₀ →* Y) (hinj : Function.Injective (θ.comp β)) {K : Subgroup Y}
    (hK : K = β.range.map θ) : Nonempty (K ≃* S) :=
  ⟨(MulEquiv.subgroupCongr (hK.trans (MonoidHom.range_comp θ β).symm)).trans
    (MonoidHom.ofInjective hinj).symm⟩

theorem oddCore_eq_bot_of_equiv {K S : Type*} [Group K] [Finite K] [Group S] (e : K ≃* S)
    (e' : K ⧸ classicalInvolutionOddCore K ≃* S) : classicalInvolutionOddCore K = ⊥ := by
  have : Finite S := Finite.of_equiv K e.toEquiv
  have h1 : Nat.card K = Nat.card S := Nat.card_congr e.toEquiv
  have h2 : Nat.card (K ⧸ classicalInvolutionOddCore K) = Nat.card S := Nat.card_congr e'.toEquiv
  have h3 := (classicalInvolutionOddCore K).card_eq_card_quotient_mul_card_subgroup
  have hpos : 0 < Nat.card S := Nat.card_pos
  have h4 : Nat.card (classicalInvolutionOddCore K) = 1 := by
    rw [h1, h2] at h3
    have h5 : Nat.card S * Nat.card (classicalInvolutionOddCore K) = Nat.card S * 1 := by
      rw [mul_one]
      exact h3.symm
    exact Nat.eq_of_mul_eq_mul_left hpos h5
  exact Subgroup.card_eq_one.mp h4

end CFSG.ClassicalInvolution.Balance
