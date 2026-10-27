module

public import CFSG.HardMathSupport.Solomon.Coordinator.PSL2CentDefs
public import CFSG.HardMathSupport.Solomon.Proving.PSL2CommutantAffine

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open Matrix CFSG.HardMathSupport.Solomon.Proving.PSL2Even

namespace Aux

theorem conj_inv_rel {G : Type*} [Group G] (A g c : G) (hc : c ∈ Subgroup.center G)
    (hg : g * A = c * (A * g)) : g⁻¹ * A = c⁻¹ * (A * g⁻¹) := by
  have hc' := Subgroup.mem_center_iff.mp hc
  have h1 : A * g⁻¹ = c * (g⁻¹ * A) := by
    calc A * g⁻¹ = g⁻¹ * (g * A) * g⁻¹ := by group
      _ = g⁻¹ * (c * (A * g)) * g⁻¹ := by rw [hg]
      _ = g⁻¹ * c * A := by group
      _ = c * (g⁻¹ * A) := by rw [hc' g⁻¹, mul_assoc]
  rw [h1, ← mul_assoc, inv_mul_cancel, one_mul]

theorem comm_of_central_relation {G : Type*} [Group G] (A B D z w : G)
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G)
    (hB : B * A = z * (A * B)) (hD : D * A = w * (A * D)) :
    (B * D * B⁻¹ * D⁻¹) * A = A * (B * D * B⁻¹ * D⁻¹) := by
  have hB' := conj_inv_rel A B z hz hB
  have hD' := conj_inv_rel A D w hw hD
  have hwi := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hw)
  have hzi := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz)
  have hwc := Subgroup.mem_center_iff.mp hw
  have key : ∀ Y : G, w⁻¹ * z⁻¹ * (w * Y) = z⁻¹ * Y := fun Y => by
    calc w⁻¹ * z⁻¹ * (w * Y) = w⁻¹ * (z⁻¹ * w) * Y := by group
      _ = w⁻¹ * (w * z⁻¹) * Y := by rw [hzi w]
      _ = z⁻¹ * Y := by group
  have e : B * (w * (A * D)) * B⁻¹ * D⁻¹ = w * (B * A * D * B⁻¹ * D⁻¹) := by
    calc B * (w * (A * D)) * B⁻¹ * D⁻¹ = (B * w) * (A * D) * B⁻¹ * D⁻¹ := by group
      _ = (w * B) * (A * D) * B⁻¹ * D⁻¹ := by rw [hwc B]
      _ = w * (B * A * D * B⁻¹ * D⁻¹) := by group
  have e2 : B * A * D * B⁻¹ * D⁻¹ = z * (A * (B * D * B⁻¹ * D⁻¹)) := by
    calc B * A * D * B⁻¹ * D⁻¹ = (B * A) * (D * B⁻¹ * D⁻¹) := by group
      _ = z * (A * B) * (D * B⁻¹ * D⁻¹) := by rw [hB]
      _ = z * (A * (B * D * B⁻¹ * D⁻¹)) := by group
  calc (B * D * B⁻¹ * D⁻¹) * A = B * D * B⁻¹ * (D⁻¹ * A) := by group
    _ = B * D * B⁻¹ * (w⁻¹ * (A * D⁻¹)) := by rw [hD']
    _ = w⁻¹ * (B * D * (B⁻¹ * A) * D⁻¹) := by
        rw [← mul_assoc (B * D * B⁻¹) w⁻¹, hwi (B * D * B⁻¹)]; group
    _ = w⁻¹ * (B * D * (z⁻¹ * (A * B⁻¹)) * D⁻¹) := by rw [hB']
    _ = w⁻¹ * (z⁻¹ * (B * D * (A * B⁻¹) * D⁻¹)) := by
        rw [← mul_assoc (B * D) z⁻¹ (A * B⁻¹), hzi (B * D)]
        group
    _ = w⁻¹ * z⁻¹ * (B * (D * A) * B⁻¹ * D⁻¹) := by group
    _ = w⁻¹ * z⁻¹ * (B * (w * (A * D)) * B⁻¹ * D⁻¹) := by rw [hD]
    _ = w⁻¹ * z⁻¹ * (w * (B * A * D * B⁻¹ * D⁻¹)) := by rw [e]
    _ = z⁻¹ * (B * A * D * B⁻¹ * D⁻¹) := key _
    _ = A * (B * D * B⁻¹ * D⁻¹) := by rw [e2, ← mul_assoc, inv_mul_cancel, one_mul]

theorem isSolvable_of_comm_normal {G : Type*} [Group G] (C K : Subgroup G) (hKC : K ≤ C)
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcomm : ∀ g ∈ C, ∀ h ∈ C, g * h * g⁻¹ * h⁻¹ ∈ K) : Group.IsSolvable C := by
  have : (K.subgroupOf C).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h1 := hcomm g.1 g.2 n.1 (hKC hn)
      have h2 : g.1 * n.1 * g.1⁻¹ = (g.1 * n.1 * g.1⁻¹ * n.1⁻¹) * n.1 := by group
      rw [show ((g * n * g⁻¹ : C) : G) = g.1 * n.1 * g.1⁻¹ from rfl, h2]
      exact K.mul_mem h1 hn⟩
  have : Group.IsSolvable (K.subgroupOf C) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext (hK a.1.1
      (Subgroup.mem_subgroupOf.mp a.2) b.1.1 (Subgroup.mem_subgroupOf.mp b.2)))
  have : Group.IsSolvable (C ⧸ K.subgroupOf C) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := hcomm _ (C.inv_mem h.2) _ (C.inv_mem g.2)
    convert this using 1
    simp [mul_inv_rev]
    group
  exact Group.isSolvable_of_subgroup_quotient (K.subgroupOf C)

end Aux

open Aux

theorem psl2CentSolvable_holds : Coordinator.PSL2CentSolvable := by
  intro F _ _ x hx
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  have hA : ∀ r : F, (A : Matrix (Fin 2) (Fin 2) F) ≠ r • 1 := by
    intro r hr
    apply hx
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, hr, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  have hcoe : ∀ X Y : Matrix.SpecialLinearGroup (Fin 2) F, X * Y = Y * X →
      (X : Matrix (Fin 2) (Fin 2) F) * Y = Y * X := fun X Y h => by
    have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) h
    simpa using this
  set C := Subgroup.centralizer ({QuotientGroup.mk A} :
    Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) with hCdef
  set K := (Subgroup.centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).map
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) with hKdef
  refine Aux.isSolvable_of_comm_normal C K ?_ ?_ ?_
  ·
    intro y hy
    obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.mp hy
    have hBA : A * B = B * A := (Subgroup.mem_centralizer_iff.mp hB) A rfl
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    simp only [QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hBA]
  ·
    intro a ha b hb
    obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨D, hD, rfl⟩ := Subgroup.mem_map.mp hb
    have hBA : A * B = B * A := (Subgroup.mem_centralizer_iff.mp hB) A rfl
    have hDA : A * D = D * A := (Subgroup.mem_centralizer_iff.mp hD) A rfl
    have hmat : (B : Matrix (Fin 2) (Fin 2) F) * D = D * B :=
      mul_comm_of_commute_nonscalar (A : Matrix (Fin 2) (Fin 2) F) B D hA
        (hcoe _ _ hBA).symm (hcoe _ _ hDA).symm
    simp only [QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext hmat)
  ·
    intro g hg h hh
    obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨D, rfl⟩ := QuotientGroup.mk_surjective h
    have hBr : QuotientGroup.mk A * QuotientGroup.mk B = QuotientGroup.mk B * QuotientGroup.mk A :=
      (Subgroup.mem_centralizer_iff.mp hg) _ (Set.mem_singleton _)
    have hDr : QuotientGroup.mk A * QuotientGroup.mk D = QuotientGroup.mk D * QuotientGroup.mk A :=
      (Subgroup.mem_centralizer_iff.mp hh) _ (Set.mem_singleton _)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hBr hDr
    have hBrel : B * A = ((A * B)⁻¹ * (B * A)) * (A * B) := by
      calc B * A = (A * B) * ((A * B)⁻¹ * (B * A)) := by group
        _ = ((A * B)⁻¹ * (B * A)) * (A * B) :=
          (Subgroup.mem_center_iff.mp hBr (A * B))
    have hDrel : D * A = ((A * D)⁻¹ * (D * A)) * (A * D) := by
      calc D * A = (A * D) * ((A * D)⁻¹ * (D * A)) := by group
        _ = ((A * D)⁻¹ * (D * A)) * (A * D) :=
          (Subgroup.mem_center_iff.mp hDr (A * D))
    have hEC : B * D * B⁻¹ * D⁻¹ ∈ Subgroup.centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      rw [hk]
      exact (comm_of_central_relation A B D _ _ hBr hDr hBrel hDrel).symm
    exact Subgroup.mem_map.mpr ⟨_, hEC, by
      simp [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
