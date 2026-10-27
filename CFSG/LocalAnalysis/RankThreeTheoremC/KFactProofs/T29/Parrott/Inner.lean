module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeLinFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeLinSix
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniPSU67
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeSpMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmSeven
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmMinusMain
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

section Transport

theorem le_pRank_centralizer_of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (g : G) : CFSG.Open.pRank 3 (centralizer ({e g} : Set H)) ≤
      CFSG.Open.pRank 3 (centralizer ({g} : Set G)) := by
  refine (CFSG.SectionRank.pRank_le_map (by norm_num) e.symm.toMonoidHom e.symm.injective _).trans
    (CFSG.SectionRank.pRank_mono (by norm_num) ?_)
  rintro _ ⟨h, hh, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hh
  rw [mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom]
  calc e.symm h * g = e.symm (h * e g) := by rw [map_mul, MulEquiv.symm_apply_apply]
    _ = e.symm (e g * h) := by rw [hh]
    _ = g * e.symm h := by rw [map_mul, MulEquiv.symm_apply_apply]

theorem le_pRank_centralizer_of_subgroup {X : Type*} [Group X] [Finite X] (L : Subgroup X)
    (l : ↥L) : CFSG.Open.pRank 3 (centralizer ({l} : Set ↥L)) ≤
      CFSG.Open.pRank 3 (centralizer ({(l : X)} : Set X)) := by
  refine (CFSG.SectionRank.pRank_le_map (by norm_num) L.subtype L.subtype_injective _).trans
    (CFSG.SectionRank.pRank_mono (by norm_num) ?_)
  rintro _ ⟨h, hh, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hh
  rw [mem_centralizer_singleton_iff]
  exact congrArg Subtype.val hh

end Transport

@[expose] def IsRankThreeIndex : LieTypeIndex → Prop
  | .A r q => (r = 3 ∧ q.card % 3 = 1) ∨ ((r = 5 ∨ r = 6) ∧ q.card % 3 = 2)
  | .twistedA r q => (r = 3 ∧ q.card % 3 = 2) ∨ ((r = 5 ∨ r = 6) ∧ q.card % 3 = 1)
  | .B r _ => r = 3
  | .C r _ => r = 3
  | .twistedD r _ => r = 4
  | _ => False

@[expose] def InnerRankThreeAt (d : ValidLieTypeIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (CFSGIndex.lie d).Group) →
    ∀ x : K, orderOf x = 3 → 3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set K))

section Families

theorem not_three_dvd_prime_pow {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : ¬ 3 ∣ p ^ f := by
  intro h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm

theorem innerRankThreeAt_of_isRankThreeIndex (d : ValidLieTypeIndex)
    (hch : d.1.characteristic ≠ 3) (hd : IsRankThreeIndex d.1) : InnerRankThreeAt d := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_A] using hch
    intro K _ _ ⟨e⟩ x hx
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    have hfx : orderOf (f x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
    refine le_trans ?_ (le_pRank_centralizer_of_mulEquiv f x)
    have hFq : Nat.card F = q.card := hF.trans (PrimePower.card_def q).symm
    rcases hd with ⟨rfl, hq⟩ | ⟨hr, hq⟩
    · exact i294CrossModelPSL4_holds F (by omega) (f x) hfx
    · have hF3 : ¬ 3 ∣ Nat.card F := by
        rw [hF]; exact not_three_dvd_prime_pow q.prime_p hp3
      rcases hr with rfl | rfl
      · exact i294CrossModelPSL67_holds F hF3 (by omega) 6 (Or.inl rfl) (f x) hfx
      · exact i294CrossModelPSL67_holds F hF3 (by omega) 7 (Or.inr rfl) (f x) hfx
  | twistedA r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_twistedA] using hch
    intro K _ _ ⟨e⟩ x hx
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    have hfx : orderOf (f x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
    refine le_trans ?_ (le_pRank_centralizer_of_mulEquiv f x)
    have hq3 : ¬ 3 ∣ q.p ^ q.exponent := not_three_dvd_prime_pow q.prime_p hp3
    have hqc : q.card = q.p ^ q.exponent := PrimePower.card_def q
    rcases hd with ⟨rfl, hq⟩ | ⟨hr, hq⟩
    · exact i294CrossModelPSU4_holds _ F hF (by omega) (f x) hfx
    · rcases hr with rfl | rfl
      · exact i294CrossModelPSU67_holds _ F hF hq3 (by omega) 6 (Or.inl rfl) (f x) hfx
      · exact i294CrossModelPSU67_holds _ F hF hq3 (by omega) 7 (Or.inr rfl) (f x) hfx
  | B r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_B] using hch
    obtain rfl : r = 3 := hd
    intro K _ _ ⟨e⟩ x hx
    have hfx : ∀ {M : Type} [Group M] (f : K ≃* M), orderOf (f x) = 3 := fun f => by
      rw [MulEquiv.orderOf_eq]; exact hx
    by_cases hp2 : q.p = 2
    · obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hp2 le_rfl e
      refine le_trans ?_ (le_pRank_centralizer_of_mulEquiv f x)
      exact i294CrossModelPSp6_holds F (by rw [hF]; exact not_three_dvd_prime_pow q.prime_p hp3)
        (f x) (hfx f)
    · obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv hp2 le_rfl e
      refine le_trans ?_ (le_pRank_centralizer_of_mulEquiv f x)
      have hodd : Odd (Nat.card F) := by
        rw [hF]; exact (q.prime_p.odd_of_ne_two hp2).pow
      exact i294CrossModelPOmega7_holds F
        (by rw [hF]; exact not_three_dvd_prime_pow q.prime_p hp3) hodd (f x) (hfx f)
  | C r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_C] using hch
    obtain rfl : r = 3 := hd
    intro K _ _ ⟨e⟩ x hx
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC 3 q hv e
    have hfx : orderOf (f x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
    refine le_trans ?_ (le_pRank_centralizer_of_mulEquiv f x)
    exact i294CrossModelPSp6_holds F (by rw [hF]; exact not_three_dvd_prime_pow q.prime_p hp3)
      (f x) hfx
  | twistedD r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_twistedD] using hch
    obtain rfl : r = 4 := hd
    intro K _ _ ⟨e⟩ x hx
    obtain ⟨-, F, _, _, hF, b, c, hbc, ⟨f⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD 4 q hv e
    have hfx : orderOf (f x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
    refine le_trans ?_ (le_pRank_centralizer_of_mulEquiv f x)
    exact i294CrossModelPOmegaMinus4_holds F
      (by rw [hF]; exact not_three_dvd_prime_pow q.prime_p hp3) b c hbc (f x) hfx
  | D r q => exact hd.elim
  | E6 q => exact hd.elim
  | E7 q => exact hd.elim
  | E8 q => exact hd.elim
  | F4 q => exact hd.elim
  | G2 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | suzuki k => exact hd.elim
  | reeG2 k => exact hd.elim
  | reeF4 k => exact hd.elim
  | tits => exact hd.elim

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
