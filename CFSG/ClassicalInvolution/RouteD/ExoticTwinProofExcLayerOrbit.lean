module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerBasic
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedTotalComponents

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

section Commutators

variable {G : Type*} [Group G]

theorem commutator_mul_mul_eq {A B : Subgroup G} (h : A ≤ Subgroup.centralizer (B : Set G))
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) {a' b' : G} (ha' : a' ∈ B) (hb' : b' ∈ B) :
    ⁅a * a', b * b'⁆ = ⁅a, b⁆ * ⁅a', b'⁆ := by
  let φ : ↥A × ↥B →* G := MonoidHom.noncommCoprod A.subtype B.subtype fun x y =>
    (Subgroup.mem_centralizer_iff.mp (h x.2) _ y.2).symm
  have hφ : ∀ (x : ↥A) (y : ↥B), φ (x, y) = (x : G) * (y : G) := fun x y => rfl
  have hx : ⁅((⟨a, ha⟩ : ↥A), (⟨a', ha'⟩ : ↥B)), ((⟨b, hb⟩ : ↥A), (⟨b', hb'⟩ : ↥B))⁆ =
      (⁅(⟨a, ha⟩ : ↥A), ⟨b, hb⟩⁆, ⁅(⟨a', ha'⟩ : ↥B), ⟨b', hb'⟩⁆) := by
    ext <;> simp [commutatorElement_def]
  have h1 := map_commutatorElement φ (⟨a, ha⟩, ⟨a', ha'⟩) (⟨b, hb⟩, ⟨b', hb'⟩)
  rw [hx, hφ, hφ, hφ] at h1
  simpa [commutatorElement_def] using h1.symm

end Commutators

section Datum

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p k)

theorem le_orbitGroupC_of_perfect {J₁ J₂ : Set.range D.classOrbit} (hne : J₁ ≠ J₂)
    (hJ : ∀ J : Set.range D.classOrbit, J = J₁ ∨ J = J₂)
    {P : Subgroup (adjointGroup τ k)} (hPX : P ≤ D.totalFixedGroup) (hPperf : P ≤ ⁅P, P⁆)
    (hPC : P ≤ Subgroup.centralizer ((D.withOrbit J₁).orbitGroupC : Set (adjointGroup τ k))) :
    P ≤ (D.withOrbit J₂).orbitGroupC := by
  classical
  have hΓC₁ := (D.withOrbit J₁).commutator_fixedGroup_le
  have hΓC₂ := (D.withOrbit J₂).commutator_fixedGroup_le
  have hC₁ := (D.withOrbit J₁).orbitGroupC_le_fixedGroup
  have hC₂ := (D.withOrbit J₂).orbitGroupC_le_fixedGroup
  have hΓ : (D.withOrbit J₁).fixedGroup ≤
      Subgroup.centralizer ((D.withOrbit J₂).fixedGroup : Set (adjointGroup τ k)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (D.commute_of_ne hne ((D.withOrbit J₁).mem_fixedGroup.1 hx).1
      ((D.withOrbit J₂).mem_fixedGroup.1 hy).1).symm.eq
  have hcomm : ∀ x ∈ (D.withOrbit J₁).fixedGroup ⊔ (D.withOrbit J₂).fixedGroup,
      ∀ y ∈ (D.withOrbit J₁).fixedGroup ⊔ (D.withOrbit J₂).fixedGroup,
        ⁅x, y⁆ ∈ (D.withOrbit J₁).orbitGroupC ⊔ (D.withOrbit J₂).orbitGroupC := by
    intro x hx y hy
    obtain ⟨a, ha, a', ha', rfl⟩ := (mem_sup_iff_of_le_centralizer hΓ).mp hx
    obtain ⟨b, hb, b', hb', rfl⟩ := (mem_sup_iff_of_le_centralizer hΓ).mp hy
    rw [commutator_mul_mul_eq hΓ ha hb ha' hb']
    exact Subgroup.mul_mem_sup (hΓC₁ (Subgroup.commutator_mem_commutator ha hb))
      (hΓC₂ (Subgroup.commutator_mem_commutator ha' hb'))
  have hPS : P ≤ D.kernelFixedGroup := hPperf.trans (Subgroup.commutator_le.2 fun x hx y hy =>
    D.commutatorElement_mem_kernelFixedGroup (hPX hx) (hPX hy))
  have hPU : ⁅P, P⁆ ≤ D.orbitFixedJoin := Subgroup.commutator_le.2 fun x hx y hy =>
    D.commutatorElement_mem_orbitFixedJoin (hPS hx) (hPS hy)
  have hU : D.orbitFixedJoin ≤
      (D.withOrbit J₁).fixedGroup ⊔ (D.withOrbit J₂).fixedGroup :=
    iSup_le fun J' => (hJ J').elim (fun h => h ▸ le_sup_left) (fun h => h ▸ le_sup_right)
  have hPU' : P ≤ (D.withOrbit J₁).fixedGroup ⊔ (D.withOrbit J₂).fixedGroup :=
    hPperf.trans (hPU.trans hU)
  have hPCC : P ≤ (D.withOrbit J₁).orbitGroupC ⊔ (D.withOrbit J₂).orbitGroupC :=
    hPperf.trans (Subgroup.commutator_le.2 fun x hx y hy => hcomm x (hPU' hx) y (hPU' hy))
  exact le_of_perfect_of_le_sup_of_commutes
    (fun x hx => Subgroup.centralizer_le hC₂ (hΓ (hC₁ hx))) hPCC hPperf hPC

end Datum

end CFSG.ClassicalInvolution.RouteD.Exotic
