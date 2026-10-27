module

public import CFSG.ClassicalInvolution.Balance.WeakFrameExistsBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.TwoGroupCase.Fusion
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12

open CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ComponentClassification.M12Cover

variable {G : Type} [Group G] {N : Subgroup G} [N.Normal]

@[expose] noncomputable def phi (e : ↥N ≃* ↥NativeSporadic.M12) :
    G →* MulAut ↥NativeSporadic.M12 :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := N))

theorem phi_apply (e : ↥N ≃* ↥NativeSporadic.M12) (x : G) (n : ↥N) :
    phi e x (e n) = e (MulAut.conjNormal x n) := by
  simp [phi, MulAut.congr_apply]

theorem phi_injective (e : ↥N ≃* ↥NativeSporadic.M12)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) : Function.Injective (phi e) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [← hC, Subgroup.mem_centralizer_iff]
  intro n hn
  have h1 := phi_apply e x ⟨n, hn⟩
  rw [hx, MulAut.one_apply] at h1
  have h3 := congrArg Subtype.val (e.injective h1)
  rw [MulAut.conjNormal_apply] at h3
  calc n * x = (x * n * x⁻¹) * x := by rw [← h3]
    _ = x * n := by group

theorem phi_of_mem (e : ↥N ≃* ↥NativeSporadic.M12) (n : ↥N) :
    phi e (n : G) = MulAut.conj (e n) := by
  ext w
  obtain ⟨m, rfl⟩ := e.surjective w
  rw [phi_apply, MulAut.conj_apply]
  rw [← map_mul, ← map_inv, ← map_mul]
  congr 1

theorem mem_of_phi_eq (e : ↥N ≃* ↥NativeSporadic.M12)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {x : G} {g : ↥NativeSporadic.M12}
    (h : phi e x = MulAut.conj g) : x ∈ N := by
  have h1 : phi e x = phi e (e.symm g : N) := by rw [phi_of_mem, MulEquiv.apply_symm_apply, h]
  rw [phi_injective e hC h1]
  exact (e.symm g).2


theorem exists_phi_eq_beta (e : ↥N ≃* ↥NativeSporadic.M12)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {x : G} (hx : x ∉ N) :
    ∃ g, phi e x = MulAut.conj g * beta := by
  obtain ⟨g, h | h⟩ := exists_conj_or_conj_mul_beta (phi e x)
  · exact absurd (mem_of_phi_eq e hC h) hx
  · exact ⟨g, h⟩

theorem beta_mul_conj (g : ↥NativeSporadic.M12) :
    beta * MulAut.conj g = MulAut.conj (beta g) * beta := by
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem mul_mem_of_not_mem (e : ↥N ≃* ↥NativeSporadic.M12)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {x y : G} (hx : x ∉ N) (hy : y ∉ N) :
    x * y ∈ N := by
  obtain ⟨g, hg⟩ := exists_phi_eq_beta e hC hx
  obtain ⟨h, hh⟩ := exists_phi_eq_beta e hC hy
  refine mem_of_phi_eq e hC (g := g * beta h) ?_
  rw [map_mul, hg, hh, map_mul, mul_assoc, ← mul_assoc beta, beta_mul_conj, mul_assoc,
    beta_mul_self, mul_one]

theorem mul_self_mem (e : ↥N ≃* ↥NativeSporadic.M12)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) (x : G) : x * x ∈ N := by
  by_cases hx : x ∈ N
  · exact N.mul_mem hx hx
  · exact mul_mem_of_not_mem e hC hx hx

theorem mem_of_odd (e : ↥N ≃* ↥NativeSporadic.M12)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {x : G} (hx : Odd (orderOf x)) : x ∈ N := by
  obtain ⟨k, hk⟩ := hx
  have h1 : x = (x * x) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [h1]
  exact N.pow_mem (mul_self_mem e hC x) _

theorem oddCoreImg_centralizer_eq_bot [Finite G] (e : ↥N ≃* ↥NativeSporadic.M12)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {z : G} (hzN : z ∈ N) (hz : orderOf z = 2) :
    oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
  have hu2 : orderOf (e ⟨z, hzN⟩) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz]
  have hmap : ((N ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf N).map e.toMonoidHom =
      Subgroup.centralizer ({e ⟨z, hzN⟩} : Set ↥NativeSporadic.M12) := by
    ext d
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : e.symm d * ⟨z, hzN⟩ = ⟨z, hzN⟩ * e.symm d := Subtype.ext h.2
      have h2 := congrArg e h1
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    · intro h
      refine ⟨(e.symm d).2, ?_⟩
      have h1 : e (e.symm d * ⟨z, hzN⟩) = e (⟨z, hzN⟩ * e.symm d) := by
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact h
      exact congrArg Subtype.val (e.injective h1)
  let ψ : ↥(N ⊓ Subgroup.centralizer ({z} : Set G)) ≃*
      ↥(Subgroup.centralizer ({e ⟨z, hzN⟩} : Set ↥NativeSporadic.M12)) :=
    (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans
      ((e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap))
  have hcore : CFSG.oddCore ↥(N ⊓ Subgroup.centralizer ({z} : Set G)) = ⊥ :=
    ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv ψ.symm
      (Sporadic.Schreier.m12_inner_oddCore _ hu2)
  have hO : Balance.oddCoreIn (N ⊓ Subgroup.centralizer ({z} : Set G)) = ⊥ := by
    show (CFSG.oddCore _).map _ = ⊥
    rw [hcore, Subgroup.map_bot]
  have hle : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤
      Balance.oddCoreIn (N ⊓ Subgroup.centralizer ({z} : Set G)) := by
    intro x hx
    refine Balance.inf_oddCoreIn_le inf_le_right
      ⟨⟨mem_of_odd e hC ?_, Balance.oddCoreIn_le _ hx⟩, hx⟩
    exact (Balance.odd_card_oddCoreIn _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
  show Balance.oddCoreIn _ = ⊥
  rw [← le_bot_iff, ← hO]
  exact hle

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12
