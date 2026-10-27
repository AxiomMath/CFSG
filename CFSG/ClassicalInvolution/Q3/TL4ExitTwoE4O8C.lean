module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoE4A
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.E4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.EvenSmallLie.OmegaEight

section Model

variable {G : Type} [Group G] {N : Subgroup G} [N.Normal] (e : ↥N ≃* ↥omegaT)

@[expose] noncomputable def phiA : G →* ↥autT :=
  autEquiv.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)

@[expose] noncomputable def phi : G →* Equiv.Perm (Fin 360) := autT.subtype.comp (phiA e)

theorem phi_mem_autT (g : G) : phi e g ∈ autT := (phiA e g).2

theorem phi_injective (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    Function.Injective (phi e) :=
  Subtype.val_injective.comp (autEquiv.symm.injective.comp
    ((MulAut.congr e).injective.comp (conjNormal_injective hC)))

theorem phi_of_mem (n : ↥N) : phi e n = ((e n : ↥omegaT) : Equiv.Perm (Fin 360)) := by
  have h : phiA e n = ⟨e n, omegaT_le_autT (e n).2⟩ := by
    apply autEquiv.injective
    rw [phiA, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    ext y
    rw [autEquiv_apply]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, MulEquiv.trans_apply, MulAut.conjNormal_val, MulAut.conj_apply, map_mul,
      map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [phi, MonoidHom.comp_apply, h]
  rfl

theorem exists_of_mem_omegaT {x : Equiv.Perm (Fin 360)} (hx : x ∈ omegaT) :
    ∃ n : ↥N, phi e n = x := by
  obtain ⟨n, hn⟩ := e.surjective ⟨x, hx⟩
  exact ⟨n, by rw [phi_of_mem, hn]⟩

theorem mem_of_phi_mem (hC : Subgroup.centralizer (N : Set G) = ⊥) {g : G}
    (h : phi e g ∈ omegaT) : g ∈ N := by
  obtain ⟨n, hn⟩ := exists_of_mem_omegaT e h
  rw [← phi_injective e hC hn]
  exact n.2

theorem phi_mem_omegaT_of_mem {g : G} (hg : g ∈ N) : phi e g ∈ omegaT := by
  rw [show g = ((⟨g, hg⟩ : ↥N) : G) from rfl, phi_of_mem]
  exact (e ⟨g, hg⟩).2

include e in
theorem index_dvd_six [Finite G] (hC : Subgroup.centralizer (N : Set G) = ⊥) : N.index ∣ 6 := by
  have h1 : Nat.card G = Nat.card (phiA e).range :=
    (Nat.card_congr (MonoidHom.ofInjective (fun a b h => phi_injective e hC
      (congrArg Subtype.val h))).toEquiv)
  have h2 : Nat.card (phiA e).range ∣ Nat.card autT := Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card ↥N = Nat.card omegaT := Nat.card_congr e.toEquiv
  have hpos : 0 < Nat.card ↥N := Nat.card_pos
  rw [← h1, card_autT_eq, ← h3, ← N.index_mul_card] at h2
  exact Nat.dvd_of_mul_dvd_mul_right hpos h2

end Model

section Members

variable {G : Type} [Group G]

theorem q8_involution_eq {K : Subgroup G} {z : G} (eK : ↥K ≃* QuaternionGroup 2)
    (hz : IsUniqueInvolution K z) : ((eK.symm (QuaternionGroup.a 2) : ↥K) : G) = z := by
  have hmem := (eK.symm (QuaternionGroup.a 2)).2
  refine ((hz.unique _ hmem ?_).resolve_left ?_)
  · rw [← Subgroup.coe_mul, ← map_mul, show QuaternionGroup.a 2 * QuaternionGroup.a 2 =
      (1 : QuaternionGroup 2) by decide, map_one, Subgroup.coe_one]
  · intro h
    have h1 : eK.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
    rw [MulEquiv.symm_apply_eq, map_one] at h1
    exact absurd h1 (by decide)

theorem q8_sq {K : Subgroup G} {z : G} (eK : ↥K ≃* QuaternionGroup 2)
    (hz : IsUniqueInvolution K z) {y : G} (hy : y ∈ K) (hy1 : y ≠ 1) (hyz : y ≠ z) :
    y * y = z := by
  have key : ∀ a : QuaternionGroup 2, a ≠ 1 → a ≠ QuaternionGroup.a 2 →
      a * a = QuaternionGroup.a 2 := by decide
  have hz' := q8_involution_eq eK hz
  have hne1 : eK ⟨y, hy⟩ ≠ 1 := fun h => hy1 (by
    have := congrArg Subtype.val (eK.injective (h.trans (map_one eK).symm))
    exact this)
  have hnez : eK ⟨y, hy⟩ ≠ QuaternionGroup.a 2 := fun h => hyz (by
    rw [← hz', ← h, MulEquiv.symm_apply_apply])
  have h := key _ hne1 hnez
  rw [← hz']
  have h2 : eK.symm (eK ⟨y, hy⟩ * eK ⟨y, hy⟩) = eK.symm (QuaternionGroup.a 2) := by rw [h]
  rw [map_mul, MulEquiv.symm_apply_apply] at h2
  exact congrArg Subtype.val h2

theorem mem_zpowers_of_comm {K : Subgroup G} (eK : ↥K ≃* QuaternionGroup 2) {u y : G}
    (hu : u ∈ K) (hy : y ∈ K) (hu2 : u * u ≠ 1) (hyu : y * u = u * y) :
    y = 1 ∨ y = u ∨ y = u * u ∨ y = u * u * u := by
  have key : ∀ a b : QuaternionGroup 2, a * a ≠ 1 → b * a = a * b →
      b = 1 ∨ b = a ∨ b = a * a ∨ b = a * a * a := by decide
  have h1 : eK ⟨u, hu⟩ * eK ⟨u, hu⟩ ≠ 1 := by
    rw [← map_mul, ← map_one eK]
    intro h
    exact hu2 (congrArg Subtype.val (eK.injective h))
  have h2 : eK ⟨y, hy⟩ * eK ⟨u, hu⟩ = eK ⟨u, hu⟩ * eK ⟨y, hy⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyu
  rcases key _ _ h1 h2 with h | h | h | h
  · left
    have := congrArg (fun b => ((eK.symm b : ↥K) : G)) h
    simpa using this
  · right; left
    have := congrArg (fun b => ((eK.symm b : ↥K) : G)) h
    simpa using this
  · right; right; left
    have := congrArg (fun b => ((eK.symm b : ↥K) : G)) h
    simpa [← map_mul] using this
  · right; right; right
    have := congrArg (fun b => ((eK.symm b : ↥K) : G)) h
    simpa [← map_mul] using this

end Members

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.E4
