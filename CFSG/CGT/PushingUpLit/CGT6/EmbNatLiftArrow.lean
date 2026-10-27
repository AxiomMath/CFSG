module

public import CFSG.CGT.PushingUpLit.CGT6.EmbNatLiftShort
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatLift

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp
open scoped commutatorElement

variable {V : Type} [CommGroup V] {X Y : Subgroup (MulAut V)} {a b : ℕ}

theorem pCore_alt_eq_bot_of_pos (hb : 1 ≤ b) :
    pCore 2 (alternatingGroup (Fin (2 * b + 1))) = ⊥ := by
  by_cases h2 : 2 ≤ b
  · exact pCore_alt_eq_bot h2
  · have hb1 : b = 1 := by omega
    subst hb1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcard : Nat.card (alternatingGroup (Fin (2 * 1 + 1))) = 3 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp
      (pCore_isPGroup (p := 2) (G := alternatingGroup (Fin (2 * 1 + 1))))
    have hd := Subgroup.card_subgroup_dvd_card (pCore 2 (alternatingGroup (Fin (2 * 1 + 1))))
    rw [hn, hcard] at hd
    have hn0 : n = 0 := by
      by_contra hne
      have h2d : 2 ∣ 2 ^ n := dvd_pow_self 2 hne
      have := h2d.trans hd
      omega
    apply Subgroup.eq_bot_of_card_eq
    rw [hn, hn0, pow_zero]

theorem nonempty_equiv_alt_of_stab {m : ℕ} (F : Finset (Fin m)) {n : ℕ} (h : m - F.card = n) :
    Nonempty (↥(altStabilizer m F) ≃* alternatingGroup (Fin n)) := by
  subst h
  exact ⟨altStabilizerEquiv F⟩

theorem arrowNat_yuHol_of_natSection (hV : ∀ v : V, v ^ 2 = 1) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hba : b ≤ a) (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥)
    (F : Finset (Fin (2 * a + 1))) (hF : F.card = (2 * a + 1) - (2 * b + 1)) (hYX : Y ≤ X)
    (hY : (Y.subgroupOf X).map θ.toMonoidHom = altStabilizer (2 * a + 1) F) :
    ArrowNat (yuHol Y) (yuHol X) := by
  have hpX := natLift_pCore_bot ha θ
  have hcard : (2 * a + 1) - F.card = 2 * b + 1 := by omega
  obtain ⟨eS⟩ := nonempty_equiv_alt_of_stab F hcard
  let eY : ↥Y ≃* alternatingGroup (Fin (2 * b + 1)) :=
    (((Subgroup.subgroupOfEquivOfLe hYX).symm.trans
      (Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective)).trans
      (MulEquiv.subgroupCongr hY)).trans eS
  have hpY : pCore 2 ↥Y = ⊥ := pCore_eq_bot_of_equiv eY (pCore_alt_eq_bot_of_pos hb)
  right
  refine ⟨a, b, (yuTop' X hV hpX).trans θ, F, ⟨(yuTop' Y hV hpY).trans eY⟩,
    natLift_naturalAltWith hV ha θ hnat, hF, ?_, ?_, ?_⟩
  · rw [natLift_shortU hV ha θ hnat]
    rintro g ⟨x, hx, rfl⟩
    have hxP : x ∈ pCore 2 ↥(yuHol Y) := Subgroup.commutator_le_left _ _ hx
    rw [pCore_yuHol Y hV, hpY, MonoidHom.comap_bot, ker_yuProj] at hxP
    obtain ⟨u, rfl⟩ := hxP
    exact ⟨yuInc X ⟨(u : V), commV_mono hYX u.2⟩, ⟨_, rfl⟩, rfl⟩
  · exact fun x hx => ⟨commV_mono hYX hx.1, hYX hx.2⟩
  · have h1 := yuTop'_image X hV hpX Y
    have h2 : (((yuHol Y).subgroupOf (yuHol X)).map
        (QuotientGroup.mk' (pCore 2 ↥(yuHol X)))).map
        ((yuTop' X hV hpX).trans θ).toMonoidHom = (Y.subgroupOf X).map θ.toMonoidHom := by
      rw [← h1]
      simp only [Subgroup.map_map]
      rfl
    rw [h2, hY]

theorem natLift_holds : NatLiftStatement := by
  intro V _ _ hV X Y a b ha hb hba θ hnat F hF hYX hY
  exact ⟨inClassX_yuHol_of_natSection hV ha θ hnat,
    arrowNat_yuHol_of_natSection hV ha hb hba θ hnat F hF hYX hY⟩

end CFSG.CGT.PushingUpLit.CGT6
