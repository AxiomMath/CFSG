module

public import CFSG.Quasithin.H13.L32A755d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A753j

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Orbit

namespace Ctx753

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G}

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem natural_sec_F4
    (C : Ctx753 T L V K) (h38 : Lemma14_7_38_F4) :
    M753.IrrBetween (autIH (fsuV1 T V) V (hz T V) K) (fixV (autIH (fsuV1 T V) V (hz T V) K)) ⊤ ∧
      Nat.card (Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))) = 2 ^ 6 ∧
      G2NaturalDerived (autSec (autIH (fsuV1 T V) V (hz T V) K) ⊤
        (fixV (autIH (fsuV1 T V) V (hz T V) K))) ⊤ ⊥ 1 ∧
      ∃ k ∈ autIH (fsuV1 T V) V (hz T V) K,
        ∃ v ∈ (⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V)))),
          k v * v⁻¹ ∉ fixV (autIH (fsuV1 T V) V (hz T V) K) := by
  have hsq : ∀ v : ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))), v ^ 2 = 1 := fun v => by
    have h := (Fact.out : IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V)))).2
      v.1 v.2
    exact Subtype.ext (by simpa using h)
  have hP := C.b42TypeU33_autK
  rcases M753.structure_fixV hsq hP C.commV_autK C.index_fixV_autK_le with
    ⟨hirr, h64, hnat⟩ | ⟨J, hKJ, hC₀J, -, hirr₁, -, hnt₁, hnt₂, h64₁, hnat₁, h64₂, hnat₂⟩
  · refine ⟨hirr, h64, hnat, ?_⟩
    by_contra h
    push Not at h
    have htop := M753.trivial_of_le hP h
    apply absurd (B42U33.card_of_b42TypeU33 hP)
    have hK1 : autIH (fsuV1 T V) V (hz T V) K = ⊥ := by
      rw [eq_bot_iff]
      intro k' hk'
      rw [Subgroup.mem_bot]
      exact MulEquiv.ext fun v => htop (Subgroup.mem_top v) k' hk'
    rw [hK1, Subgroup.card_bot]
    norm_num
  · exact (C.not_two_factor_F4 h38 hKJ hC₀J.le hirr₁ hnt₁ hnt₂ h64₁ hnat₁ h64₂ hnat₂).elim

theorem exists_coord755_F4
    (C : Ctx753 T L V K) (h38 : Lemma14_7_38_F4) :
    ∃ e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ,
      (autSec (autIH (fsuV1 T V) V (hz T V) K) ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))).map
          (MulAut.congr e).toMonoidHom = (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) ∧
        (∀ x ∈ autSec (autIH (fsuV1 T V) V (hz T V) (hz T V)) ⊤
            (fixV (autIH (fsuV1 T V) V (hz T V) K)),
          MulAut.congr e x ∈ (g2QAct (ZMod 2)).range) ∧
        (autSec (autIH (fsuV1 T V) V (hz T V) T) ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))).map
            (MulAut.congr e).toMonoidHom ≤ sSubG.map (g2QAct (ZMod 2)) ∧
        ∀ i ∈ M755.innerS, g2QAct (ZMod 2) (sEltG i) ∈
          (autSec (autIH (fsuV1 T V) V (hz T V) T) ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))).map
            (MulAut.congr e).toMonoidHom := by
  obtain ⟨-, -, hnat, -⟩ := C.natural_sec_F4 h38
  have hXJ : autIH (fsuV1 T V) V (hz T V) (hz T V) ≤ stabSub ⊤ := fun x _ v => by simp
  have hXC : autIH (fsuV1 T V) V (hz T V) (hz T V) ≤
      stabSub (fixV (autIH (fsuV1 T V) V (hz T V) K)) := M753.le_stabSub_fixV C.autH_le_normalizer
  have hKX := autSec_mono C.autK_le_autH ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))
  have hXN := M755.autSec_le_normalizer C.autK_le_autH C.autH_le_normalizer hXJ hXC
  have hsyl := M755.isSylowTwoOf_autSec C.isSylowTwoOf_autT hXJ hXC
  obtain ⟨e, hKe, hXe, hTbS⟩ := M3330.exists_coordT hXN hnat hsyl.1 hsyl.2.1
  exact ⟨e, hKe, hXe, hTbS, fun i hi => M755.mem_map_of_inner hKX hKe hXe hTbS hsyl hi⟩

end Ctx753

end CFSG.Quasithin.H13.L32A
