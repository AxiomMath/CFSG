module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.RouteD.LieBridge

open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

section Quotient

variable {Y : Type*} [Group Y] {O : Subgroup Y} [O.Normal]

theorem commute_of_map_commute (hO : O ≤ Subgroup.center Y) {A : Subgroup Y} (hA : A ≤ ⁅A, A⁆)
    {y : Y} (h : ∀ a ∈ A, QuotientGroup.mk' O y * QuotientGroup.mk' O a =
      QuotientGroup.mk' O a * QuotientGroup.mk' O y) : ∀ a ∈ A, y * a = a * y := by
  have hc : ∀ a ∈ A, ⁅y, a⁆ ∈ Subgroup.center Y := fun a ha => hO <| by
    rw [← QuotientGroup.eq_one_iff (N := O), ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact h a ha
  let f : A →* Y :=
    { toFun := fun a => ⁅y, (a : Y)⁆
      map_one' := by simp
      map_mul' := fun a a' => by
        obtain ⟨c, hcc⟩ : ∃ c, c = ⁅y, (a' : Y)⁆ := ⟨_, rfl⟩
        have hcen : ∀ g : Y, g * c = c * g := hcc ▸ Subgroup.mem_center_iff.mp (hc a' a'.2)
        have e : (a' : Y) * y⁻¹ * (a' : Y)⁻¹ = y⁻¹ * c := by
          rw [hcc, commutatorElement_def]
          group
        calc ⁅y, ((a * a' : A) : Y)⁆ = y * (a : Y) * ((a' : Y) * y⁻¹ * (a' : Y)⁻¹) * (a : Y)⁻¹ := by
              rw [commutatorElement_def]
              simp only [Subgroup.coe_mul]
              group
          _ = y * (a : Y) * (y⁻¹ * c) * (a : Y)⁻¹ := by rw [e]
          _ = ⁅y, (a : Y)⁆ * (a : Y) * c * (a : Y)⁻¹ := by
              rw [commutatorElement_def]
              group
          _ = ⁅y, (a : Y)⁆ * ((a : Y) * c) * (a : Y)⁻¹ := by group
          _ = ⁅y, (a : Y)⁆ * (c * (a : Y)) * (a : Y)⁻¹ := by rw [hcen]
          _ = ⁅y, (a : Y)⁆ * c := by group
          _ = ⁅y, (a : Y)⁆ * ⁅y, (a' : Y)⁆ := by rw [hcc] }
  have hker : ⁅A, A⁆ ≤ f.ker.map A.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha a' ha'
    refine ⟨⁅(⟨a, ha⟩ : A), ⟨a', ha'⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.mp (hc a ha) (f ⟨a', ha'⟩)).symm
  intro a ha
  obtain ⟨k, hk, hka⟩ := hker (hA ha)
  have hk' : k = ⟨a, ha⟩ := Subtype.ext hka
  rw [hk', SetLike.mem_coe, MonoidHom.mem_ker] at hk
  change ⁅y, a⁆ = 1 at hk
  exact commutatorElement_eq_one_iff_mul_comm.mp hk

theorem commutes_of_map_commutes (hO : O ≤ Subgroup.center Y) {A B : Subgroup Y}
    (hA : A ≤ ⁅A, A⁆)
    (h : Commutes (A.map (QuotientGroup.mk' O)) (B.map (QuotientGroup.mk' O))) : Commutes A B := by
  intro a ha b hb
  exact (commute_of_map_commute hO hA (y := b)
    (fun a' ha' => (h _ ⟨a', ha', rfl⟩ _ ⟨b, hb, rfl⟩).symm) a ha).symm

theorem centralizer_map_le (hO : O ≤ Subgroup.center Y) {S : Subgroup Y} (hS : S ≤ ⁅S, S⁆) :
    Subgroup.centralizer ((S.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)) ≤
      (Subgroup.centralizer (S : Set Y)).map (QuotientGroup.mk' O) := by
  intro yq hyq
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O yq
  refine ⟨y, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro s hs
  exact (commute_of_map_commute hO hS (y := y)
    (fun a ha => (Subgroup.mem_centralizer_iff.mp hyq _ ⟨a, ha, rfl⟩).symm) s hs).symm

theorem isSolvable_centralizer_map (hO : O ≤ Subgroup.center Y) {S : Subgroup Y}
    (hS : S ≤ ⁅S, S⁆) (h : Group.IsSolvable ↥(Subgroup.centralizer (S : Set Y))) :
    Group.IsSolvable ↥(Subgroup.centralizer
      ((S.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O))) := by
  let g : ↥(Subgroup.centralizer (S : Set Y)) →*
      ↥(Subgroup.centralizer ((S.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O))) :=
    ((QuotientGroup.mk' O).domRestrict (Subgroup.centralizer (S : Set Y))).codRestrict _
      (fun c => by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨s, hs, rfl⟩
        have := Subgroup.mem_centralizer_iff.mp c.2 s hs
        change QuotientGroup.mk' O s * QuotientGroup.mk' O (c : Y) =
          QuotientGroup.mk' O (c : Y) * QuotientGroup.mk' O s
        rw [← map_mul, ← map_mul, this])
  have hsurj : Function.Surjective g := by
    intro c
    obtain ⟨y, hy, hyc⟩ := centralizer_map_le hO hS c.2
    exact ⟨⟨y, hy⟩, Subtype.ext hyc⟩
  exact Group.isSolvable_of_surjective hsurj

end Quotient

section Kernel

variable {K X : Type*} [Group K] [Group X]

theorem isSolvable_centralizer_of_ker_le_center (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K)
    (R : Subgroup K)
    (h : Group.IsSolvable ↥(Subgroup.centralizer ((R.map ψ : Subgroup X) : Set X))) :
    Group.IsSolvable ↥(Subgroup.centralizer (R : Set K)) := by
  let g : ↥(Subgroup.centralizer (R : Set K)) →*
      ↥(Subgroup.centralizer ((R.map ψ : Subgroup X) : Set X)) :=
    (ψ.domRestrict (Subgroup.centralizer (R : Set K))).codRestrict _
      (fun c => by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨r, hr, rfl⟩
        have := Subgroup.mem_centralizer_iff.mp c.2 r hr
        change ψ r * ψ (c : K) = ψ (c : K) * ψ r
        rw [← map_mul, ← map_mul, this])
  have hcomm : Group.IsSolvable ↥g.ker := by
    refine Group.isSolvable_of_comm fun a b => ?_
    apply Subtype.ext
    apply Subtype.ext
    have ha : ((a : ↥(Subgroup.centralizer (R : Set K))) : K) ∈ ψ.ker := by
      have := a.2
      rw [MonoidHom.mem_ker] at this ⊢
      exact congrArg Subtype.val this
    have hb : ((b : ↥(Subgroup.centralizer (R : Set K))) : K) ∈ ψ.ker := by
      have := b.2
      rw [MonoidHom.mem_ker] at this ⊢
      exact congrArg Subtype.val this
    exact Subgroup.mem_center_iff.mp (hker hb) _
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (fun x hx => ⟨⟨x, hx⟩, rfl⟩)

end Kernel

end CFSG.ClassicalInvolution.RouteD.LieBridge
