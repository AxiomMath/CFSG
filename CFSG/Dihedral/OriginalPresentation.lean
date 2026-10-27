module

public import CFSG.Dihedral.BlueprintDefs
import all CFSG.Dihedral.BlueprintDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem r_mem_sylow : d.r ∈ (d.S : Subgroup G) := by
  rw [← d.generators]
  exact Subgroup.subset_closure (by simp)

theorem s_mem_sylow : d.s ∈ (d.S : Subgroup G) := by
  rw [← d.generators]
  exact Subgroup.subset_closure (by simp)

theorem s_sq : d.s ^ 2 = 1 := by
  simpa [d.order_s] using pow_orderOf_eq_one d.s

theorem s_inv : d.s⁻¹ = d.s :=
  inv_eq_of_mul_eq_one_right (by simpa [pow_two] using d.s_sq)

theorem s_not_mem_rotation : d.s ∉ Subgroup.zpowers d.r := by
  rintro ⟨k, hk⟩
  have hcomm : Commute d.r d.s := by
    rw [← hk]
    exact (Commute.refl d.r).zpow_right k
  have hrinv : d.r = d.r⁻¹ := by
    calc
      d.r = d.s * d.r * d.s := by rw [← hcomm.eq, mul_assoc]; simp [← pow_two, d.s_sq]
      _ = d.r⁻¹ := d.dihedral
  have hr2 : d.r ^ 2 = 1 := by
    calc
      d.r ^ 2 = d.r * d.r := pow_two _
      _ = d.r⁻¹ * d.r := congrArg (fun x => x * d.r) hrinv
      _ = 1 := inv_mul_cancel _
  have hdiv : 2 ^ (d.n - 1) ∣ 2 := by
    simpa [d.order_r] using orderOf_dvd_of_pow_eq_one hr2
  have hfour : 4 ≤ 2 ^ (d.n - 1) := by
    calc
      4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (d.n - 1) := Nat.pow_le_pow_right (by decide) (by have := d.three_le; omega)
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

theorem sylow_mulEquiv_dihedral :
    Nonempty ((d.S : Subgroup G) ≃* DihedralGroup (2 ^ (d.n - 1))) := by
  let rho : (d.S : Subgroup G) := ⟨d.r, d.r_mem_sylow⟩
  let sigma : (d.S : Subgroup G) := ⟨d.s, d.s_mem_sylow⟩
  have hgen : (⊤ : Subgroup (d.S : Subgroup G)) =
      Subgroup.zpowers rho ⊔ Subgroup.zpowers sigma := by
    apply Subgroup.map_injective (d.S : Subgroup G).subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_sup,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    change (d.S : Subgroup G) = Subgroup.zpowers d.r ⊔ Subgroup.zpowers d.s
    rw [← d.generators, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    rfl
  have hs2 : sigma ^ 2 = 1 := Subtype.ext d.s_sq
  have hrel : sigma * rho * sigma⁻¹ = rho⁻¹ := by
    apply Subtype.ext
    change d.s * d.r * d.s⁻¹ = d.r⁻¹
    rw [d.s_inv]
    exact d.dihedral
  have hnot : sigma ∉ Subgroup.zpowers rho := by
    intro h
    exact d.s_not_mem_rotation (by
      rcases Subgroup.mem_zpowers_iff.mp h with ⟨k, hk⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩)
  have hrorder : orderOf rho = 2 ^ (d.n - 1) :=
    (Subgroup.orderOf_coe rho).symm.trans d.order_r
  rw [← hrorder]
  exact dihedral_of_generators_of_not_mem rho sigma hgen hs2 hrel hnot

theorem reflection_mem_sylow (i : Fin 2) :
    d.s * d.r ^ i.val ∈ (d.S : Subgroup G) :=
  d.S.mul_mem d.s_mem_sylow (d.S.pow_mem d.r_mem_sylow _)

theorem reflection_not_mem_rotation (i : Fin 2) :
    d.s * d.r ^ i.val ∉ Subgroup.zpowers d.r := by
  intro hu
  apply d.s_not_mem_rotation
  have hm := (Subgroup.zpowers d.r).mul_mem hu
    ((Subgroup.zpowers d.r).inv_mem ((Subgroup.zpowers d.r).pow_mem (Subgroup.mem_zpowers _) i.val))
  simpa [mul_assoc] using hm

theorem reflection_sq (i : Fin 2) : (d.s * d.r ^ i.val) ^ 2 = 1 := by
  fin_cases i
  · simpa using d.s_sq
  · simp only [pow_one]
    rw [pow_two]
    calc
      (d.s * d.r) * (d.s * d.r) = (d.s * d.r * d.s) * d.r := by group
      _ = 1 := by rw [d.dihedral]; simp

theorem t_isInvolution (hn : d.n = 3) :
    BenderSuzuki.PFAppendixIII.IsInvolution d.t := by
  have hr4 : d.r ^ 4 = 1 := by
    have h := pow_orderOf_eq_one d.r
    simpa [d.order_r, hn] using h
  have ht : d.t = d.r ^ 2 := by simp [t, hn]
  constructor
  · intro h1
    have hdiv := orderOf_dvd_of_pow_eq_one (ht.symm.trans h1)
    simp [d.order_r, hn] at hdiv
  · rw [ht, ← pow_mul]
    exact hr4

theorem V_isKleinFour (hn : d.n = 3) (i : Fin 2) : IsKleinFour (d.V i) := by
  let u := d.s * d.r ^ i.val
  have ht := d.t_isInvolution hn
  have hu : BenderSuzuki.PFAppendixIII.IsInvolution u := by
    refine ⟨?_, d.reflection_sq i⟩
    intro h1
    exact d.reflection_not_mem_rotation i (by change u ∈ _; rw [h1]; exact Subgroup.one_mem _)
  have htu : d.t ≠ u := by
    intro h
    exact d.reflection_not_mem_rotation i (by
      change u ∈ _
      rw [← h]
      exact (Subgroup.zpowers d.r).pow_mem (Subgroup.mem_zpowers _) _)
  have huC : u ∈ d.C := by
    rw [d.decomposition]
    exact Subgroup.mem_sup_right (d.reflection_mem_sylow i)
  have hcomm : Commute d.t u := by
    have hcent : u ∈ Subgroup.centralizer ({d.t} : Set G) := by
      simpa only [d.centralizer, t] using huC
    exact (Subgroup.mem_centralizer_singleton_iff.mp hcent).symm
  let W := kleinFourOfCommutingInvolutions d.t u
    (by simpa [pow_two] using ht.2) (by simpa [pow_two] using hu.2) hcomm
  have hW : IsKleinFour W := isKleinFour_kleinFourOfCommutingInvolutions d.t u
    (by simpa [pow_two] using ht.2) (by simpa [pow_two] using hu.2)
    ht.1 hu.1 htu hcomm
  have htV : d.t ∈ d.V i := Subgroup.subset_closure (by simp)
  have huV : u ∈ d.V i := Subgroup.subset_closure (by simp [u])
  have heq : d.V i = W := by
    apply le_antisymm
    · apply (Subgroup.closure_le W).mpr
      intro x hx
      change x ∈ ({d.t, u} : Set G) at hx
      change x ∈ ({d.t * u, d.t, u, 1} : Set G)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    · intro x hx
      change x ∈ ({d.t * u, d.t, u, 1} : Set G) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (d.V i).mul_mem htV huV
      · exact htV
      · exact huV
      · exact (d.V i).one_mem
  rwa [heq]

theorem V_le_sylow (i : Fin 2) : d.V i ≤ (d.S : Subgroup G) := by
  apply (Subgroup.closure_le (d.S : Subgroup G)).mpr
  intro x hx
  change x ∈ ({d.t, d.s * d.r ^ i.val} : Set G) at hx
  rcases hx with rfl | h
  · exact d.S.pow_mem d.r_mem_sylow _
  · rw [Set.mem_singleton_iff] at h
    rw [h]
    exact d.reflection_mem_sylow i

end CFSG.DihedralBlueprint.OriginalData
