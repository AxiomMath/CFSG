module

public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofKlein

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

section

open CFSG Subgroup
open scoped commutatorElement

@[expose] def HasSimpleQuotient3Quart (H : Type*) [Group H] : Prop :=
  ∃ (M : Subgroup H) (_ : M.Normal), Group.IsSolvable M ∧ IsSimpleGroup (H ⧸ M) ∧
    3 ^ 4 ∣ Nat.card (H ⧸ M)

theorem eq_one_of_perfect_of_hasSimpleQuotient {H K : Type*} [Group H] [Finite H] [Group K]
    (hH : Group.IsPerfect H) (h3 : HasSimpleQuotient3Quart H) (f : H →* K)
    (hf : ¬ 3 ^ 4 ∣ Nat.card f.range) : f = 1 := by
  obtain ⟨M, hMn, hMs, hsimple, hdvd⟩ := h3
  have := hH
  by_contra hne
  have hex : ∃ x, f x ≠ 1 := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    exact hne (MonoidHom.ext fun x => by simpa using hall x)
  have hK : f.ker ≤ M :=
    CFSG.RankThree.PartTwo.Sec11.LSSolvableProof.ker_le_of_perfect hMs hsimple f hex
  have h1 : M.index ∣ f.ker.index := Subgroup.index_dvd_of_le hK
  rw [Subgroup.index_ker] at h1
  exact hf (hdvd.trans h1)

theorem perm_eq_one_of_perfect {H α : Type*} [Group H] [Finite H] [Finite α]
    (hH : Group.IsPerfect H) (h3 : HasSimpleQuotient3Quart H) (hα : Nat.card α ≤ 8)
    (φ : H →* Equiv.Perm α) : φ = 1 := by
  refine eq_one_of_perfect_of_hasSimpleQuotient hH h3 φ ?_
  intro hd
  have h1 : Nat.card φ.range ∣ Nat.card (Equiv.Perm α) := Subgroup.card_subgroup_dvd_card _
  rw [Nat.card_perm] at h1
  have h2 : Nat.factorial (Nat.card α) ∣ Nat.factorial 8 := Nat.factorial_dvd_factorial hα
  have h4 : 3 ^ 4 ∣ Nat.factorial 8 := hd.trans (h1.trans h2)
  revert h4
  decide

theorem HasSimpleQuotient3Quart.of_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') :
    HasSimpleQuotient3Quart H → HasSimpleQuotient3Quart H' := by
  rintro ⟨M, hMn, hMs, hsimple, hdvd⟩
  have hM'n : (M.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hMn e.toMonoidHom e.surjective
  let e' : M ≃* M.map e.toMonoidHom := Subgroup.equivMapOfInjective M e.toMonoidHom e.injective
  have hsolv : Group.IsSolvable (M.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (f := e'.toMonoidHom) e'.surjective
  let q : H ⧸ M ≃* H' ⧸ M.map e.toMonoidHom :=
    QuotientGroup.congr M (M.map e.toMonoidHom) e rfl
  refine ⟨M.map e.toMonoidHom, hM'n, hsolv, MulEquiv.isSimpleGroup q.symm, ?_⟩
  rw [Nat.card_congr q.symm.toEquiv]
  exact hdvd

theorem commutator_eq_one_of_perfect_centralizer {Λ : Type*} [Group Λ] {Z : Subgroup Λ} [Z.Normal]
    (hZ : Z ≤ center Λ) {y : Λ}
    (hC : Group.IsPerfect (centralizer ({(QuotientGroup.mk y : Λ ⧸ Z)} : Set (Λ ⧸ Z))))
    {g : Λ} (hg : ⁅g, y⁆ ∈ Z) : ⁅g, y⁆ = 1 := by
  set π : Λ →* Λ ⧸ Z := QuotientGroup.mk' Z with hπ
  set C : Subgroup (Λ ⧸ Z) := centralizer ({π y} : Set (Λ ⧸ Z)) with hCdef
  have : Group.IsPerfect C := hC
  set Γ : Subgroup Λ := C.comap π
  have hZc : ∀ z ∈ Z, ∀ x : Λ, x * z = z * x := fun z hz x =>
    Subgroup.mem_center_iff.mp (hZ hz) x
  have h1 : ∀ z : Λ, π z = 1 ↔ z ∈ Z := fun z => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have key : ∀ x : Λ, π x ∈ C ↔ π ⁅x, y⁆ = 1 := by
    intro x
    rw [hCdef, Subgroup.mem_centralizer_iff, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    constructor
    · intro h
      exact (h (π y) (Set.mem_singleton _)).symm
    · intro h m hm
      rw [Set.mem_singleton_iff.mp hm]
      exact h.symm
  have hΓiff : ∀ x : Λ, x ∈ Γ ↔ ⁅x, y⁆ ∈ Z := fun x => (key x).trans (h1 _)
  have hΓmap : Γ.map π = C :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) C
  have hQmap : (⁅Γ, Γ⁆ : Subgroup Λ).map π = C := by
    rw [Subgroup.map_commutator, hΓmap]
    exact Subgroup.commutator_eq_self
  have hmul : ∀ x ∈ Γ, ∀ x' ∈ Γ, ⁅x * x', y⁆ = ⁅x', y⁆ * ⁅x, y⁆ := by
    intro x _ x' hx'
    have hv := (hΓiff x').mp hx'
    have e1 : x' * y * x'⁻¹ = ⁅x', y⁆ * y := by
      rw [commutatorElement_def]; group
    have e2 : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      rw [commutatorElement_def]; group
    calc ⁅x * x', y⁆ = x * (x' * y * x'⁻¹) * x⁻¹ * y⁻¹ := by
          rw [commutatorElement_def]; group
      _ = x * (⁅x', y⁆ * y) * x⁻¹ * y⁻¹ := by rw [e1]
      _ = (x * ⁅x', y⁆) * y * x⁻¹ * y⁻¹ := by group
      _ = (⁅x', y⁆ * x) * y * x⁻¹ * y⁻¹ := by rw [hZc _ hv x]
      _ = ⁅x', y⁆ * (x * y * x⁻¹) * y⁻¹ := by group
      _ = ⁅x', y⁆ * (⁅x, y⁆ * y) * y⁻¹ := by rw [e2]
      _ = ⁅x', y⁆ * ⁅x, y⁆ := by group
  have hinv : ∀ a ∈ Γ, ⁅a⁻¹, y⁆ = ⁅a, y⁆⁻¹ := by
    intro a ha
    have h1' := hmul a⁻¹ (Γ.inv_mem ha) a ha
    rw [inv_mul_cancel, commutatorElement_one_left] at h1'
    exact eq_inv_of_mul_eq_one_right h1'.symm
  have hcomm : ∀ a ∈ Γ, ∀ b ∈ Γ, ⁅⁅a, b⁆, y⁆ = 1 := by
    intro a ha b hb
    have hA := (hΓiff a).mp ha
    have e1 : ⁅a * b * a⁻¹ * b⁻¹, y⁆ = ⁅b⁻¹, y⁆ * (⁅a⁻¹, y⁆ * (⁅b, y⁆ * ⁅a, y⁆)) := by
      rw [hmul (a * b * a⁻¹) (Γ.mul_mem (Γ.mul_mem ha hb) (Γ.inv_mem ha)) b⁻¹ (Γ.inv_mem hb),
        hmul (a * b) (Γ.mul_mem ha hb) a⁻¹ (Γ.inv_mem ha), hmul a ha b hb]
    rw [commutatorElement_def a b, e1, hinv a ha, hinv b hb, hZc ⁅a, y⁆ hA ⁅b, y⁆]
    group
  have hQK : ⁅Γ, Γ⁆ ≤ Subgroup.centralizer ({y} : Set Λ) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (commutatorElement_eq_one_iff_mul_comm.mp (hcomm a ha b hb)).symm
  have hgΓ : g ∈ Γ := (hΓiff g).mpr hg
  have hgC : π g ∈ C := hgΓ
  rw [← hQmap] at hgC
  obtain ⟨q, hq, hqg⟩ := Subgroup.mem_map.mp hgC
  have hz : q⁻¹ * g ∈ Z := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hqg
    exact hqg
  have hqΓ : q ∈ Γ := Subgroup.commutator_le_self Γ hq
  have hz1 : ⁅q⁻¹ * g, y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hZc _ hz y).symm
  have hzΓ : q⁻¹ * g ∈ Γ := (hΓiff _).mpr (by rw [hz1]; exact Z.one_mem)
  have hq1 : ⁅q, y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (hQK hq) y (Set.mem_singleton y)).symm
  have key2 := hmul q hqΓ (q⁻¹ * g) hzΓ
  rw [mul_inv_cancel_left, hz1, hq1, mul_one] at key2
  exact key2

end

end CFSG.ComponentClassification.GrSLit.L34Sec5S
