
module

public import CFSG.Sporadic.Co1.Module.InvGroupBase
public import CFSG.Certificates.Kernel.Co1M.PairCount

@[expose] public section

namespace CFSG.KC.Co1Orb

open CFSG.Blueprint CFSG.Sporadic.Co1.Module CFSG.Sporadic.SmallF2 CFSG.KC.PairCount

theorem co1Act_add' (g : NativeSporadic.Co1) (a b : Vec24) :
    co1Act g (a + b) = co1Act g a + co1Act g b := by
  unfold co1Act
  rw [Matrix.mulVec_add]

theorem vec_two (a b : Vec24) : a + b + a = b := by
  funext j
  have hz : ∀ c e : ZMod 2, c + e + c = e := by decide
  exact hz (a j) (b j)

theorem vec_inj (a : Vec24) : Function.Injective (a + ·) := by
  intro x y e
  funext j
  have hz : ∀ c e f : ZMod 2, c + e = c + f → e = f := by decide
  exact hz (a j) (x j) (y j) (congrFun e j)

theorem orb_card (v : Vec24) :
    (orb co1Act v).card = (MulAction.orbit Jmat v).ncard := by
  have e : (↑(orb co1Act v) : Set Vec24) = MulAction.orbit Jmat v := by
    rw [← range_co1Act]
    ext x
    rw [Finset.mem_coe, mem_orb, Set.mem_range]
  rw [← e, Set.ncard_coe_finset]

theorem orb_eq_of_mem {v w : Vec24} (h : w ∈ orb co1Act v) : orb co1Act w = orb co1Act v := by
  obtain ⟨g, rfl⟩ := mem_orb.1 h
  ext x
  rw [mem_orb, mem_orb]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k * g, co1Act_mul k g v⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k * g⁻¹, ?_⟩
    rw [co1Act_mul, ← co1Act_mul g⁻¹ g, inv_mul_cancel, co1Act_one]

theorem lower_bound {w u : Vec24} {k : Nat} (hu : u ∈ orb co1Act v₂)
    (hw : v₂ + u ∈ orb co1Act w) (H : Finset Vec24)
    (hH : ∀ h ∈ H, ∃ x, co1Act x v₂ = v₂ ∧ co1Act x u = h) (hk : k ≤ H.card)
    (hc : ((orb co1Act v₂).filter fun a => v₂ + u + a ∈ orb co1Act v₂).card ≤ 552) :
    (orb co1Act v₂).card * k ≤ (orb co1Act w).card * 552 := by
  have h := @card_mul_le NativeSporadic.Co1 Vec24 inferInstance inferInstance inferInstance
    inferInstance co1Act co1Act_mul co1Act_one co1Act_add' vec_two vec_inj v₂ u hu H hH
  rw [orb_eq_of_mem hw] at h
  calc (orb co1Act v₂).card * k ≤ (orb co1Act v₂).card * H.card := Nat.mul_le_mul_left _ hk
    _ ≤ _ := h
    _ ≤ _ := Nat.mul_le_mul_left _ hc

theorem card_vec24 : Fintype.card Vec24 = 2 ^ 24 := by
  simp [Vec24, ZMod.card]

end CFSG.KC.Co1Orb

end
