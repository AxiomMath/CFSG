module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsPair
public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsRestrict

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6.Diag.Cons

theorem diagModCore_of (hsel : DiagMod_sel) (hs2 : DiagMod_s2) (hb : DiagBoundSL)
    (hid : DiagMod_ident) : DiagMod_core := by
  intro V _ _ hV K K' Y t h n hn hsec
  have hsec' := hsec
  obtain ⟨-, θY, -⟩ := hsec'
  obtain ⟨⟨θK⟩, hdisj⟩ := hs2 V hV K K' Y t h n hn ⟨θY⟩
  refine ⟨⟨θK⟩, hdisj, fun W hW => ?_⟩
  obtain ⟨y₀, hy₀Y, hy₀1, hy₀odd⟩ := exists_odd_order_ne_one (by omega : 1 ≤ n) θY
  let S : Set (MulAut V) := {y | y ∈ Y ∧ y ≠ 1 ∧ Odd (orderOf y)}
  have hSY : S ⊆ (Y : Set (MulAut V)) := fun y hy => hy.1
  have hgen : Subgroup.closure S = Y := by
    refine closure_eq_of_conj_invariant h.simpleY hSY ⟨y₀, ⟨hy₀Y, hy₀1, hy₀odd⟩, hy₀1⟩ ?_
    rintro s ⟨hsY, hs1, hsodd⟩ g hg
    refine ⟨Y.mul_mem (Y.mul_mem hg hsY) (Y.inv_mem hg), ?_, ?_⟩
    · intro h1
      apply hs1
      have : s = g⁻¹ * (g * s * g⁻¹) * g := by group
      rw [this, h1]
      group
    · rw [orderOf_conj_eq]
      exact hsodd
  obtain ⟨y, ⟨hyY, hy1, hyodd⟩, w, hwW, hyw⟩ := (hsel V hV K K' Y t h W hW).1 S hSY hgen
  obtain ⟨hinf, hcardW⟩ := (hsel V hV K K' Y t h W hW).2 y hyY ⟨w, hwW, hyw⟩
  have hup := hb V hV Y n hn hsec y hyY hyodd
  have hlow := two_pow_le_card_of_minInv hV h.quasi (fixV_eq_bot h) (f := n) (by omega) θK hW
  have hWcard : Nat.card ↥W = 2 ^ (2 * n) := by omega
  have hcomm_card : Nat.card ↥W = Nat.card ↥(commV (Subgroup.zpowers y)) := by omega
  have hle : commV (Subgroup.zpowers y) ≤ W ⊔ diagImg y W :=
    commV_zpowers_le_sup hinf hcomm_card
  obtain ⟨k, hk, hyk⟩ := (h.Y_mem y).mp hyY
  have hk₀ : t * k * t⁻¹ ∈ K' := conj_mem_K' h.toDiagPre hk
  have hcomm₀ : ∀ x ∈ K, x * (t * k * t⁻¹) = (t * k * t⁻¹) * x :=
    fun x hx => h.comm x hx _ hk₀
  have hyimg : diagImg y W = diagImg (t * k * t⁻¹) W := by
    rw [hyk]
    exact diagImg_mul_eq hW.2.1 hk hcomm₀
  have hinf' : W ⊓ diagImg (t * k * t⁻¹) W = ⊥ := by rwa [hyimg] at hinf
  have hAinv : GInv K (W ⊔ diagImg (t * k * t⁻¹) W) :=
    ginv_sup hW.2.1 (ginv_diagImg hW.2.1 hcomm₀)
  have hyA : ∀ v : V, (k * (t * k * t⁻¹)) v * v⁻¹ ∈ W ⊔ diagImg (t * k * t⁻¹) W := by
    intro v
    have h1 : y v * v⁻¹ ∈ commV (Subgroup.zpowers y) :=
      Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y, v, rfl⟩
    have h2 := hle h1
    rw [hyimg] at h2
    rwa [hyk] at h2
  have hcommK : commV K ≤ W ⊔ diagImg (t * k * t⁻¹) W :=
    commV_le_of_diag_invariant h.toDiagPre (center_eq_bot_of_equiv_sl2 θK) hAinv hk
      (by rw [← hyk]; exact hy1) hyA
  have htop : W ⊔ diagImg (t * k * t⁻¹) W = ⊤ := by
    rw [eq_top_iff, ← commV_K_eq_top h]
    exact hcommK
  obtain ⟨θ, hθ⟩ := hid V hV K K' n hn h.comm ⟨θK⟩ (card_K' h.toDiagPre) W hW
    (exists_move h hW.1) hWcard _ hk₀ hinf' htop
  exact ⟨θ, hθ, _, hk₀, hinf', htop⟩

end CFSG.CGT.PushingUpLit.CGT6
