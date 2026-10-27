module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem prod_zpow_prod_zpow_of_mul_eq_one {G : Type*} [CommGroup G] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℤ} (hAB : A * B = 1) (e : Fin n → G) (a : Fin n) :
    ∏ b, (∏ c, e c ^ B b c) ^ A a b = e a := by
  simp only [← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  simp only [prod_zpow_eq_zpow_sum]
  have h : ∀ c, ∑ b, B b c * A a b = (A * B) a c := fun c => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  simp only [h, hAB, Matrix.one_apply]
  rw [Finset.prod_eq_single a (fun c _ hc => by
    rw [ite_eq_right_iff.2 (fun h => absurd h.symm hc), zpow_zero])
    (fun ha => absurd (Finset.mem_univ a) ha)]
  simp

theorem e6_cartan_orbit_sum (a b : Fin TwistTag.E6.foldedTag.rank) :
    ∑ j ∈ Finset.univ.filter (fun j => TwistTag.E6.orbitIndex j = b),
      TwistTag.E6.tag.cartan j (TwistTag.E6.orbitMin a) = Tag.F4.cartan a b := by
  fin_cases a <;> fin_cases b <;> decide

variable {K : Type} [Field K]

@[expose] def e6TorusParam (e : Fin TwistTag.E6.foldedTag.rank → Kˣ) :
    Fin TwistTag.E6.foldedTag.rank → Kˣ :=
  fun b => ∏ c, e c ^ cartanInvF4 b c

theorem cartanChar_e6TorusParam (e : Fin TwistTag.E6.foldedTag.rank → Kˣ)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    cartanChar (fun i => e6TorusParam e (TwistTag.E6.orbitIndex i)) (TwistTag.E6.orbitMin a) =
      e a := by
  unfold cartanChar
  rw [← Finset.prod_fiberwise Finset.univ TwistTag.E6.orbitIndex]
  have h : ∀ c : Fin TwistTag.E6.foldedTag.rank,
      ∏ j ∈ Finset.univ.filter (fun j => TwistTag.E6.orbitIndex j = c),
        e6TorusParam e (TwistTag.E6.orbitIndex j) ^
          TwistTag.E6.tag.cartan j (TwistTag.E6.orbitMin a) =
      e6TorusParam e c ^ Tag.F4.cartan a c := fun c => by
    rw [← e6_cartan_orbit_sum a c, ← prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [Finset.prod_congr rfl fun c _ => h c]
  exact prod_zpow_prod_zpow_of_mul_eq_one cartan_mul_cartanInv_F4 e a

variable (K)

theorem e6_graphFixedTorus_le_graphFixedRootGroup :
    graphFixedTorus TwistTag.E6 K (RingHom.id K) ≤
      graphFixedRootGroup TwistTag.E6 K (RingHom.id K) := by
  intro h hh
  obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  have hl := compat_of_twistHom_rootDiagUnit
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K (RingHom.id K)).1 hhΓ).2
  set W := e6TorusParam (fun c => l (TwistTag.E6.orbitMin c))
  have hb : ∀ i, (fun i => W (TwistTag.E6.orbitIndex i)) (TwistTag.E6.perm i) =
      Units.map (RingHom.id K).toMonoidHom ((fun i => W (TwistTag.E6.orbitIndex i)) i) :=
    fun i => by
      simp only [TwistTag.orbitIndex_perm]
      rfl
  obtain ⟨w, hw⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := RingHom.id K)
    (b := fun i => W (TwistTag.E6.orbitIndex i)) hb
  have key : cartanChar (compatDiag TwistTag.E6 (RingHom.id K) w) = l := by
    rw [hw]
    exact eq_of_compat_of_orbitMin (cartanChar_perm hb) hl fun a => cartanChar_e6TorusParam _ a
  rw [← key, ← list_prod_orbitH_eq_rootDiagUnit]
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact orbitH_mem_graphFixedRootGroup _ _ _ _

theorem e6_twistedFixedGroup_id_eq_graphFixedRootGroup :
    twistedFixedGroup TwistTag.E6 K (RingHom.id K) =
      graphFixedRootGroup TwistTag.E6 K (RingHom.id K) := by
  refine le_antisymm (fun g hg => ?_) (graphFixedRootGroup_le _ _ _)
  have hg' : g ∈ (twistedFixedGroup TwistTag.E6 K (RingHom.id K) :
      Set (ModGL TwistTag.E6.tag K)) := hg
  rw [coe_twistedFixedGroup_eq_mul (fun x => ⟨x, rfl⟩)] at hg'
  obtain ⟨h, hh, c, hc, rfl⟩ := hg'
  exact mul_mem (e6_graphFixedTorus_le_graphFixedRootGroup K hh) hc

end CFSG.LieType.Chevalley
