module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.ClassicalGL

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13

open Subgroup CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalGL

theorem card_SL_inf_centralizer_thirteen {P : Subgroup G33} (hP : Nat.card P = 13) :
    Nat.card ↥(SL33 ⊓ Subgroup.centralizer (P : Set G33)) = 13 := by
  set C := Subgroup.centralizer (P : Set G33) with hC
  let f : ↥C →* (ZMod 3)ˣ := (Matrix.GeneralLinearGroup.det : G33 →* (ZMod 3)ˣ).comp C.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hm : (-1 : G33) ∈ C := neg_one_mem_centralizer _
  have hr : f.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have hu : u = 1 ∨ u = -1 := by
      have : ∀ v : ZMod 3, IsUnit v → v = 1 ∨ v = -1 := by decide
      rcases this u.val u.isUnit with h1 | h1
      · exact Or.inl (Units.ext h1)
      · exact Or.inr (Units.ext h1)
    rcases hu with rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨⟨-1, hm⟩, det_neg_one⟩
  have hker : Nat.card f.ker = Nat.card ↥(SL33 ⊓ C) := by
    have h2 : f.ker = SL33.subgroupOf C := rfl
    rw [h2, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  rw [hr, Subgroup.card_top, card_units_zmod3, card_centralizer_13 hP, hker] at h1
  omega

theorem sl33_centralizer_zpowers {D : G33} (hDS : D ∈ SL33) (hD : orderOf D = 13) {c : G33}
    (hcS : c ∈ SL33) (hc : c * D = D * c) : c ∈ Subgroup.zpowers D := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  set P : Subgroup G33 := Subgroup.zpowers D with hPdef
  have hP : Nat.card P = 13 := by rw [hPdef, Nat.card_zpowers, hD]
  have hPS : P ≤ SL33 ⊓ Subgroup.centralizer (P : Set G33) := by
    refine le_inf ?_ (le_centralizer_of_card_13 hP)
    rw [hPdef, Subgroup.zpowers_le]
    exact hDS
  have heq : P = SL33 ⊓ Subgroup.centralizer (P : Set G33) :=
    Subgroup.eq_of_le_of_card_ge hPS (by rw [card_SL_inf_centralizer_thirteen hP, hP])
  have hcC : c ∈ Subgroup.centralizer (P : Set G33) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (show g ∈ Subgroup.zpowers D from hg)
    exact ((Commute.zpow_right hc k).eq).symm
  have hmem : c ∈ SL33 ⊓ Subgroup.centralizer (P : Set G33) := ⟨hcS, hcC⟩
  rw [← heq] at hmem
  exact hmem

theorem sl33_centralizer_thirteen (d : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))
    (hd : orderOf d = 13) (c : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))
    (hc : c * d = d * c) : c ∈ Subgroup.zpowers d := by
  let ι : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) →* G33 :=
    Matrix.SpecialLinearGroup.toGL
  have hι : Function.Injective ι := Matrix.SpecialLinearGroup.toGL_injective
  have hmemS : ∀ A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3), ι A ∈ SL33 := by
    intro A
    have h1 : ι A ∈ CFSG.Open.StatedSL 3 (ZMod 3) := by
      rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
      exact MonoidHom.mem_range.2 ⟨A, rfl⟩
    rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det] at h1
    exact h1
  have hD : orderOf (ι d) = 13 := by
    rw [orderOf_injective ι hι d, hd]
  have hcz := sl33_centralizer_zpowers (hmemS d) hD (hmemS c) (by rw [← map_mul, hc, map_mul])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcz
  exact Subgroup.mem_zpowers_iff.2 ⟨k, hι (by rw [map_zpow, hk])⟩

@[expose] def SL33Thirteen : Prop :=
  ∀ d : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3), orderOf d = 13 →
    ∀ T : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)), Nat.card T = 27 →
      ¬ ∀ t ∈ T, d * t * d⁻¹ ∈ T

theorem centralizer_thirteen_of_equiv {G : Type*} [Group G] {Q : Subgroup G}
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) {d : G} (hdQ : d ∈ Q)
    (hd : orderOf d = 13) {w : G} (hwQ : w ∈ Q) (hw : w * d = d * w) :
    w ∈ Subgroup.zpowers d := by
  set u : Q := ⟨d, hdQ⟩ with hu_def
  set v : Q := ⟨w, hwQ⟩ with hv_def
  have hu : orderOf u = 13 := (Subgroup.orderOf_mk d hdQ).trans hd
  have hu' : orderOf (e u) = 13 := by
    rw [← hu]
    exact orderOf_injective e.toMonoidHom e.injective u
  have hvu : v * u = u * v := Subtype.ext hw
  have hcomm : e v * e u = e u * e v := by
    rw [← map_mul, hvu, map_mul]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (sl33_centralizer_thirteen (e u) hu' (e v) hcomm)
  have hv : v = u ^ k := e.injective (by rw [map_zpow, hk])
  have hw' : w = d ^ k := by
    have := congrArg Subtype.val hv
    simpa [hu_def, hv_def] using this
  rw [hw']
  exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩

theorem not_normalizes_of_equiv (hSL : SL33Thirteen) {G : Type*} [Group G] {Q : Subgroup G}
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) {d : G} (hdQ : d ∈ Q)
    (hd : orderOf d = 13) {T : Subgroup G} (hTQ : T ≤ Q) (hT : Nat.card T = 27) :
    ¬ ∀ t ∈ T, d * t * d⁻¹ ∈ T := by
  intro hnorm
  set u : Q := ⟨d, hdQ⟩ with hu_def
  let T' : Subgroup Q := T.subgroupOf Q
  let T'' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) := T'.map e.toMonoidHom
  have hT'card : Nat.card T' = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTQ).toEquiv, hT]
  have hT'' : Nat.card T'' = 27 := by
    rw [← hT'card]
    exact Nat.card_congr (Subgroup.equivMapOfInjective T' e.toMonoidHom e.injective).toEquiv.symm
  have hu : orderOf u = 13 := (Subgroup.orderOf_mk d hdQ).trans hd
  have hord : orderOf (e u) = 13 := by
    rw [← hu]
    exact orderOf_injective e.toMonoidHom e.injective u
  have hnorm' : ∀ t ∈ T'', e u * t * (e u)⁻¹ ∈ T'' := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    refine Subgroup.mem_map.2 ⟨u * s * u⁻¹, ?_, ?_⟩
    · apply Subgroup.mem_subgroupOf.2
      have h1 := hnorm (s : G) (Subgroup.mem_subgroupOf.1 hs)
      simpa [hu_def] using h1
    · simp [map_mul, map_inv]
  exact hSL (e u) hord T'' hT'' hnorm'

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13
