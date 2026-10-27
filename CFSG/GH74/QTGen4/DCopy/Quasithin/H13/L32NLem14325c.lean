module

public import CFSG.Quasithin.H13.L32NLem14325c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneStatements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14325

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace Ctx14325

variable (C : Ctx14325 G T L V V₂ g D)
include C

theorem relIndex_inf_conj_F4 (h12810 : Lemma12_8_10_F4) :
    (centerOf (fsuU T V) ⊓ CFSG.conjugate (fsuU T V) g).relIndex (centerOf (fsuU T V)) =
      Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) := by
  obtain ⟨h1, h2, -, -, -, h6⟩ := h12810 G T L V 3 (fsuV1 T V) V₂ C.setting g C.gP C.gN
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := h6
  set ZI := centerOf (i128 T L V (fsuV1 T V)) with hZI
  set Zg := CFSG.conjugate (centerOf (fsuU T V)) g with hZg
  have heq : Zg ⊓ centralizerMod (centerOf (fsuU T V)) (l32nH T V) (fsuU T V) =
      ZI ⊔ CFSG.conjugate (fsuV1 T V) g := by
    rw [e1, e2, e3, e4, e5]
  have hN : Zg ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    C.zUg_le.trans (L14332.l32nH_le_normalizer_fsuU T V)
  have hker : ∀ x ∈ Zg, (∃ hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G),
      D.ρ ⟨x, hxN⟩ = 1) ↔ x ∈ ZI ⊔ CFSG.conjugate (fsuV1 T V) g := by
    intro x hx
    rw [← heq]
    constructor
    · rintro ⟨hxN, h1⟩
      refine Subgroup.mem_inf.mpr ⟨hx, C.zUg_le hx,
        L14332.normalizer_le_normalizer_centerOf _ hxN, fun u hu => ?_⟩
      exact (L128A.HatU.rho_eq_one_iff D ⟨x, hxN⟩).mp h1 u hu
    · intro h1
      obtain ⟨-, ⟨-, -, h2⟩⟩ := Subgroup.mem_inf.mp h1
      exact ⟨hN hx, (L128A.HatU.rho_eq_one_iff D ⟨x, hN hx⟩).mpr h2⟩
  rw [L128A.HatU.card_img_eq_relIndex D hN hker]

  have hgI : g ∈ Subgroup.normalizer (ZI : Set G) :=
    L14332.normalizer_le_normalizer_centerOf _ (le_normalizer_conjClosure _ _ C.gP)
  have hconj : CFSG.conjugate (ZI ⊔ fsuV1 T V) g = ZI ⊔ CFSG.conjugate (fsuV1 T V) g := by
    unfold CFSG.conjugate
    rw [Subgroup.map_sup]
    congr 1
    have := conjugate_eq_of_mem_normalizer hgI
    unfold CFSG.conjugate at this
    exact this
  have hZ0 : centerOf (fsuU T V) ⊓ CFSG.conjugate (fsuU T V) g = ZI ⊔ fsuV1 T V := by
    change zU128 V (fsuV1 T V) ⊓ CFSG.conjugate (u128 V (fsuV1 T V)) g = ZI ⊔ fsuV1 T V
    rw [h1, h2]
  rw [hZ0, ← hconj, hZg]
  unfold CFSG.conjugate
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]

theorem relIndex_centralizer_le_F4 (h12810 : Lemma12_8_10_F4) {x : G}
    (hx : x ∈ CFSG.conjugate (centerOf (fsuU T V)) g) :
    (vH T L V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (vH T L V) ≤
      Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) := by
  set Z₀ := centerOf (fsuU T V) ⊓ CFSG.conjugate (fsuU T V) g with hZ₀
  have hle : vH T L V ⊓ Z₀ ≤ vH T L V ⊓ Subgroup.centralizer ({x} : Set G) := by
    rintro z ⟨hzV, hzZ⟩
    refine ⟨hzV, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (comm_of_mem_conj hx hzZ).symm
  rw [← C.relIndex_inf_conj_F4 h12810]
  calc (vH T L V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (vH T L V)
      ≤ (vH T L V ⊓ Z₀).relIndex (vH T L V) :=
        Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
    _ = Z₀.relIndex (vH T L V) := by rw [inf_comm, Subgroup.inf_relIndex_right]
    _ ≤ Z₀.relIndex (centerOf (fsuU T V)) :=
        Subgroup.relIndex_le_of_le_right C.vH_le Subgroup.index_ne_zero_of_finite

end Ctx14325

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

end L14325

end CFSG.Quasithin.H13
