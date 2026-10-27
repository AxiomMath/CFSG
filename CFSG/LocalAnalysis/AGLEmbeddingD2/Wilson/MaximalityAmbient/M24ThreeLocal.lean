module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24KFact
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.McL

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.M24ThreeLocal

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 CFSG.AGLEmbeddingD2.Wilson.ThreeCore
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Blueprint
  CFSG.RankThree.PartTwo.Sec21 Subgroup Equiv
open CFSG.AGLEmbeddingD2.Wilson.Census219 CFSG.AGLEmbeddingD2.Wilson.Census424Rest

section Aut


theorem mulAut_eq_inner_of_m24 {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.M24)
    (τ : MulAut X) : τ ∈ (MulAut.conj : X →* MulAut X).range := by
  have hZ : Subgroup.center X = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [m24_center_eq_bot'] at h
    exact Subgroup.map_injective (f := (e : X →* NativeSporadic.M24)) e.injective
      (by rw [h, Subgroup.map_bot])
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center X := Subgroup.mem_center_iff.2 fun x => by
      have := congrArg (fun α : MulAut X => α x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g = (g * x * g⁻¹) * g := by rw [this]
        _ = g * x := by group
    rw [hZ] at hc
    exact Subgroup.mem_bot.1 hc
  have hcardX : Nat.card X = Nat.card NativeSporadic.M24 := Nat.card_congr e.toEquiv
  have hcardA : Nat.card (MulAut X) ≤ Nat.card X := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, hcardX]
    exact m24_mulAut_card
  have hr : Nat.card (MulAut.conj : X →* MulAut X).range = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have htop : (MulAut.conj : X →* MulAut X).range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ (le_antisymm
      (Nat.card_le_card_of_injective (Subgroup.subtype _) (Subgroup.subtype_injective _)) ?_)
    rw [hr]
    exact hcardA
  rw [htop]
  trivial

end Aut

section Cent


theorem m24_card_centralizer_three {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.M24)
    {c : X} (hc3 : orderOf c = 3) :
    (Nat.card (centralizer ({c} : Set X)) = 1080 ∧
        Nat.card (Subgroup.center (centralizer ({c} : Set X))) = 3) ∨
      Nat.card (centralizer ({c} : Set X)) = 504 := by
  have hb3 : (e c) ^ 3 = 1 := by
    rw [← map_pow, show c ^ 3 = 1 by rw [← hc3]; exact pow_orderOf_eq_one c, map_one]
  have hord : orderOf ((e c : NativeSporadic.M24) : Equiv.Perm (Fin 24)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hc3]
  obtain ⟨r, hr, g, hg, hgr⟩ := m24_cover (e c).2 hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    let gP : NativeSporadic.M24 := ⟨g, hg⟩
    let φ : X ≃* NativeSporadic.M24 := e.trans (MulAut.conj gP⁻¹)
    have hφ : φ c = m24y := by
      apply Subtype.ext
      show g⁻¹ * ((e c : NativeSporadic.M24) : Equiv.Perm (Fin 24)) * g = permOfArr 24 m24xA
      rw [hgr]
      show g⁻¹ * (g * permOfArr 24 m24xA * g⁻¹) * g = permOfArr 24 m24xA
      group
    obtain ⟨-, ⟨e'⟩, hQ⟩ := m24_layer
    let ε : centralizer ({c} : Set X) ≃* centralizer ({m24y} : Set NativeSporadic.M24) :=
      (centralizerEquivOfMulEquiv φ c).trans (MulEquiv.subgroupCongr (by rw [hφ]))
    let f : centralizer ({c} : Set X) ≃* ↥m24TcQ := ε.trans e'
    refine ⟨?_, ?_⟩
    · rw [Nat.card_congr f.toEquiv]
      exact card_m24TcQ
    · have h1 := Subgroup.map_center_eq f
      have h2 : Nat.card ↥((Subgroup.center (centralizer ({c} : Set X))).map f.toMonoidHom) =
          Nat.card (Subgroup.center (centralizer ({c} : Set X))) :=
        Subgroup.card_map_of_injective f.injective
      rw [← h2]
      have h3 : (Subgroup.center (centralizer ({c} : Set X))).map f.toMonoidHom =
          Subgroup.center ↥m24TcQ := h1
      rw [h3]
      exact hQ.1
  · right
    calc Nat.card ↥(centralizer ({c} : Set X))
        = Nat.card ↥((centralizer ({c} : Set X)).map e.toMonoidHom) :=
          (Subgroup.card_map_of_injective e.injective).symm
      _ = Nat.card ↥(centralizer ({e c} : Set NativeSporadic.M24)) := by
          rw [Proving.centralizer_map_mulEquiv_wilson e c]
      _ = Nat.card ↥((centralizer ({e c} : Set NativeSporadic.M24)).map
            NativeSporadic.M24.subtype) :=
          (Subgroup.card_map_of_injective NativeSporadic.M24.subtype_injective).symm
      _ = Nat.card ↥(NativeSporadic.M24 ⊓
            centralizer ({((e c : NativeSporadic.M24) : Equiv.Perm (Fin 24))} :
              Set (Equiv.Perm (Fin 24)))) := by
          rw [CFSG.Sporadic.SmallOddCore.map_subtype_centralizer]
      _ = Nat.card ↥(centralizer ({((e c : NativeSporadic.M24) : Equiv.Perm (Fin 24))} :
            Set (Equiv.Perm (Fin 24))) ⊓ NativeSporadic.M24) := by rw [inf_comm]
      _ = Nat.card ↥(centralizer ({tp 24 m24Row3B.rep} : Set (Equiv.Perm (Fin 24))) ⊓
            NativeSporadic.M24) := (card_centralizer_inf_conj NativeSporadic.M24 hg hgr.symm).symm
      _ = 504 := by rw [inf_comm]; exact m24_threeSpec_rowB

theorem m24_centralizer_eq_of_le {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.M24)
    {c : X} (hc3 : orderOf c = 3) {P : Subgroup X} (hP : P ≤ centralizer ({c} : Set X))
    (hcard : 1080 ≤ Nat.card P) :
    P = centralizer ({c} : Set X) ∧ centralizer (P : Set X) = zpowers c := by
  set C : Subgroup X := centralizer ({c} : Set X) with hC
  rcases m24_card_centralizer_three e hc3 with ⟨h1080, h3⟩ | h504
  · have hPC : P = C := Subgroup.eq_of_le_of_card_ge hP (by rw [h1080]; exact hcard)
    refine ⟨hPC, ?_⟩
    rw [hPC]
    have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
    set Zc : Subgroup X := (Subgroup.center C).map C.subtype with hZc
    have hZcard : Nat.card Zc = 3 := by
      rw [hZc, Subgroup.card_map_of_injective C.subtype_injective]
      exact h3
    have hcZ : c ∈ Zc := ⟨⟨c, hcC⟩, Subgroup.mem_center_iff.2 fun y => by
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.1 y.2
      exact this, rfl⟩
    have hzp : zpowers c ≤ Zc := (Subgroup.zpowers_le).2 hcZ
    have hzcard : Nat.card (zpowers c) = 3 := by rw [Nat.card_zpowers, hc3]
    have hZeq : Zc = zpowers c :=
      (Subgroup.eq_of_le_of_card_ge hzp (by rw [hZcard, hzcard])).symm
    apply le_antisymm
    · intro x hx
      have hxC : x ∈ C := by
        rw [Subgroup.mem_centralizer_iff] at hx
        exact Subgroup.mem_centralizer_singleton_iff.2 (by
          have := hx c hcC
          exact this.symm)
      rw [← hZeq]
      refine ⟨⟨x, hxC⟩, Subgroup.mem_center_iff.2 fun y => ?_, rfl⟩
      apply Subtype.ext
      have := hx y.1 y.2
      exact this
    · refine (Subgroup.zpowers_le).2 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_centralizer_singleton_iff.1 hy
      exact this
  · exfalso
    have h := Subgroup.card_le_of_le hP
    change Nat.card P ≤ Nat.card ↥(centralizer ({c} : Set X)) at h
    omega

end Cent

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.M24ThreeLocal
