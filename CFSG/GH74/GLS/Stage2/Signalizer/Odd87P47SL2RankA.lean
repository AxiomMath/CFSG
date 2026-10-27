module

public import CFSG.GH74.GLS.IVK.L2.BorelStd
public import CFSG.GH74.GLS.IVK.L2.FieldProj

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.L2Borel
open scoped Pointwise

namespace SL2Rank

theorem card_le_two_of_cyclic_sq {G : Type*} [Group G] [IsCyclic G] (H : Subgroup G)
    (hH : ∀ x ∈ H, x * x = 1) : Nat.card H ≤ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have h1 : orderOf g = Nat.card H := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : g ^ 2 = 1 := by
    apply Subtype.ext
    simpa [sq] using hH g.1 g.2
  rw [← h1]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)

variable {F : Type} [Field F] [Finite F]

theorem exists_unit_of_fieldProj_eq_one {K : Type} [Group K] (e : K ≃* L2 F) {W : Subgroup K}
    (hW : IsStd e W) {α : MulAut K} (hα : α ∈ MulAction.stabilizer (MulAut K) W)
    (h1 : fieldProj e α = 1) : ∃ a : Fˣ, ∀ t : F, α (wt e t) = wt e ((a : F) * t) := by
  obtain ⟨a, b, σ, hασ⟩ := exists_bor_decomp hW hα
  have hσ : σ = 1 := by
    have h := congrArg (fieldProj e) hασ
    rw [map_mul, fieldProj_innDiagHom, fieldProj_fieldAutHom, h1] at h
    simpa using h.symm
  refine ⟨a, fun t => ?_⟩
  rw [hασ, action_wt (e := e) a b σ t, hσ]
  simp

theorem card_le_four_of_stab [IsCyclic (F ≃+* F)] {K : Type} [Group K] (e : K ≃* L2 F)
    {W : Subgroup K} (hW : IsStd e W) (hodd : Odd (Nat.card F)) (D : Subgroup (MulAut K))
    (hD : D ≤ MulAction.stabilizer (MulAut K) W) (hsq : ∀ α ∈ D, α * α = 1) :
    Nat.card D ≤ 4 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  let f : D →* (F ≃+* F) := (fieldProj e).comp D.subtype
  have hcard := Subgroup.card_ker_mul_card_range f
  have hr : Nat.card f.range ≤ 2 := by
    apply card_le_two_of_cyclic_sq
    rintro _ ⟨x, rfl⟩
    show f x * f x = 1
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hsq x.1 x.2)
    rw [this, map_one]
  have hker : ∀ α : f.ker, ∃ a : Fˣ, ∀ t : F, α.1.1 (wt e t) = wt e ((a : F) * t) := fun α =>
    exists_unit_of_fieldProj_eq_one e hW (hD α.1.2) (MonoidHom.mem_ker.1 α.2)
  have hwt : ∀ α : f.ker, α.1.1 (wt e 1) = wt e 1 ∨ α.1.1 (wt e 1) = wt e (-1) := by
    intro α
    obtain ⟨a, ha⟩ := hker α
    have h1 : α.1.1 (wt e 1) = wt e (a : F) := by rw [ha]; simp
    have haa : (a : F) * (a : F) = 1 := by
      have h3 : α.1.1 (α.1.1 (wt e 1)) = wt e 1 := by
        have := congrArg (fun β : MulAut K => β (wt e 1)) (hsq α.1.1 α.1.2)
        simpa using this
      rw [h1, ha] at h3
      exact wt_injective e h2 h3
    have hpm : (a : F) = 1 ∨ (a : F) = -1 := by
      have : ((a : F) - 1) * ((a : F) + 1) = 0 := by linear_combination haa
      rcases mul_eq_zero.1 this with h | h
      · left
        linear_combination h
      · right
        linear_combination h
    rcases hpm with h | h
    · left
      rw [h1, h]
    · right
      rw [h1, h]
  have hinj : Function.Injective (fun α : f.ker => α.1.1 (wt e 1)) := by
    intro α β hαβ
    obtain ⟨a, ha⟩ := hker α
    obtain ⟨b, hb⟩ := hker β
    have hab : (a : F) = b := by
      have h := hαβ
      simp only at h
      rw [ha, hb, mul_one, mul_one] at h
      exact wt_injective e h2 h
    have hγD : α.1.1⁻¹ * β.1.1 ∈ D := mul_mem (inv_mem α.1.2) β.1.2
    have hγtriv : ∀ t : F, (α.1.1⁻¹ * β.1.1) (wt e t) = wt e t := by
      intro t
      rw [MulAut.mul_apply, hb, ← hab, ← ha]
      simp
    obtain ⟨c, hc⟩ := trivial_action hW h2 (hD hγD) hγtriv
    have hord2 : orderOf (α.1.1⁻¹ * β.1.1) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq _ hγD)
    have hordF : orderOf (α.1.1⁻¹ * β.1.1) ∣ Nat.card F := by
      rw [hc]
      exact (orderOf_map_dvd (MulAut.conj : K →* MulAut K) _).trans (orderOf_wt_dvd e h2 c)
    have hg : Nat.gcd 2 (Nat.card F) = 1 := Nat.coprime_two_left.2 hodd
    have hγ1 : α.1.1⁻¹ * β.1.1 = 1 :=
      orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hg ▸ Nat.dvd_gcd hord2 hordF))
    apply Subtype.ext
    apply Subtype.ext
    exact (inv_mul_eq_one.1 hγ1)
  have hk : Nat.card f.ker ≤ 2 := by
    let g : f.ker → ({wt e 1, wt e (-1)} : Set K) := fun α => ⟨α.1.1 (wt e 1), hwt α⟩
    have hg : Function.Injective g := fun α β h => hinj (congrArg Subtype.val h)
    have h := Nat.card_le_card_of_injective g hg
    have h2' : Nat.card ({wt e 1, wt e (-1)} : Set K) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      exact (Set.ncard_insert_le _ _).trans (by simp)
    omega
  calc Nat.card D = Nat.card f.ker * Nat.card f.range := hcard.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul hk hr
    _ = 4 := rfl

end SL2Rank

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
