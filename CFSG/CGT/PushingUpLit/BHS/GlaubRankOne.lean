module

public import CFSG.CGT.PushingUpLit.BHS.GlaubOmega
public import CFSG.Timmesfeld.RankOne.Lift

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Timmesfeld CFSG.CGT.PushingUpLit.BHS.Glauberman

namespace Glauberman

variable {Γ : Type*} [Group Γ]

theorem subgroupOf_map_conj {G H : Subgroup Γ} (x : ↥G) :
    (H.subgroupOf G).map (MulAut.conj x).toMonoidHom =
      (H.map (MulAut.conj (x : Γ)).toMonoidHom).subgroupOf G := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(z : Γ), hz, by simp⟩
  · rintro ⟨w, hw, hwy⟩
    refine ⟨⟨(x : Γ)⁻¹ * (y : Γ) * (x : Γ), ?_⟩, ?_, ?_⟩
    · exact G.mul_mem (G.mul_mem (G.inv_mem x.2) y.2) x.2
    · show (x : Γ)⁻¹ * (y : Γ) * (x : Γ) ∈ H
      have : (x : Γ)⁻¹ * (y : Γ) * (x : Γ) = w := by
        rw [← hwy]
        group
      rw [this]
      exact hw
    · apply Subtype.ext
      simp [mul_assoc]

end Glauberman

variable {V : Type} [CommGroup V]

namespace GlPair

variable [Finite V] {G M S A : Subgroup (MulAut V)} {k : MulAut V} (h : GlPair G M S A k)

include h

theorem isElemAbRankOne :
    IsElemAbRankOne (A.subgroupOf G) ((A.map (MulAut.conj k).toMonoidHom).subgroupOf G) where
  gen := by
    rw [← Subgroup.subgroupOf_sup h.A_le_G h.B_le_G, h.sup_eq, Subgroup.subgroupOf_self]
  ne := by
    intro heq
    apply h.hAk
    intro b hb
    have hbG : b ∈ G := h.B_le_G hb
    have : (⟨b, hbG⟩ : ↥G) ∈ (A.map (MulAut.conj k).toMonoidHom).subgroupOf G := hb
    rw [← heq] at this
    exact h.A_le_M this
  comm := fun a ha a' ha' => Subtype.ext (h.el.1 _ ha _ ha')
  sq := fun a ha => Subtype.ext (by simpa [pow_two] using h.el.2 _ ha)
  moufang := by
    intro a ha ha1
    have ha1' : (a : MulAut V) ≠ 1 := fun h0 => ha1 (Subtype.ext h0)
    obtain ⟨b, hb, hb1, hrel⟩ := h.exists_moufang ha ha1'
    refine ⟨⟨b, h.B_le_G hb⟩, hb, fun h0 => hb1 (congrArg Subtype.val h0), ?_⟩
    rw [subgroupOf_map_conj, subgroupOf_map_conj]
    exact congrArg (fun X => X.subgroupOf G) hrel
  moufang' := by
    intro b hb hb1
    have hb1' : (b : MulAut V) ≠ 1 := fun h0 => hb1 (Subtype.ext h0)
    obtain ⟨a, ha, ha1, hrel⟩ := h.exists_moufang' hb hb1'
    refine ⟨⟨a, h.A_le_G ha⟩, ha, fun h0 => ha1 (congrArg Subtype.val h0), ?_⟩
    rw [subgroupOf_map_conj, subgroupOf_map_conj]
    exact congrArg (fun X => X.subgroupOf G) hrel

omit [Finite V] in
theorem card_subgroupOf_A : Nat.card (A.subgroupOf G) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.A_le_G).toEquiv

theorem exists_mulEquiv_SL2 (hq : 4 ≤ Nat.card A) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card A = 2 ^ n ∧
      ∃ φ : ↥G ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        (A.subgroupOf G).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
        ((A.map (MulAut.conj k).toMonoidHom).subgroupOf G).map φ.toMonoidHom =
          lowerUnipotent (GaloisField 2 n) := by
  obtain ⟨n, hn2, hn, φ, hA, hB⟩ :=
    rankOne_mulEquiv_SL2 h.isElemAbRankOne (by rwa [h.card_subgroupOf_A])
  exact ⟨n, hn2, by rwa [h.card_subgroupOf_A] at hn, φ, hA, hB⟩

theorem card_G_eq_six (hq : Nat.card A = 2) : Nat.card G = 6 := by
  exact rankOne_two h.isElemAbRankOne (by rwa [h.card_subgroupOf_A])

end GlPair

end CFSG.CGT.PushingUpLit.BHS
