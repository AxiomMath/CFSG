module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitBasic
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainLink
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInStage1D

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

section Group

variable {G : Type*} [Group G]

variable {ε : Eps} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p : Fin 6 → G} {u : Fin 6 → G}

theorem UData.card_le_of_abelian_of [Finite G] (hR : RadicalData ε L U Q P a ψ p)
    (hPQ : ∀ x ∈ P, x ∈ centralizer (Q : Set G) → x ∈ Q) (hu : UData ε U Q ψ u) {A : Subgroup G}
    (hAU : A ≤ U) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ 64 := by
  classical
  have hAN' : A ≤ normalizer (Q : Set G) := fun x hx => hR.P_le_normalizer (hR.U_le_P (hAU hx))
  set X : Finset ℕ := (Finset.range 64).filter
    fun i => ∃ x ∈ A, ∀ v, lin ψ x v = s0Mat ε i *ᵥ v with hXdef
  have hmemX : ∀ {i}, i ∈ X ↔ i < 64 ∧ ∃ x ∈ A, ∀ v, lin ψ x v = s0Mat ε i *ᵥ v := by
    intro i
    rw [hXdef, Finset.mem_filter, Finset.mem_range]
  have hX64 : ∀ i ∈ X, i < 64 := fun i hi => (hmemX.1 hi).1
  have h0 : 0 ∈ X :=
    hmemX.2 ⟨by norm_num, 1, one_mem _, fun v => by rw [hR.lin_one, s0Mat_zero, one_mulVec]⟩
  have hmul : ∀ i ∈ X, ∀ j ∈ X, tabGet (mulTab ε) i j ∈ X := by
    intro i hi j hj
    obtain ⟨hi64, x, hx, hxi⟩ := hmemX.1 hi
    obtain ⟨hj64, y, hy, hyj⟩ := hmemX.1 hj
    refine hmemX.2 ⟨tab_lt ε hi64 hj64, x * y, mul_mem hx hy, fun v => ?_⟩
    rw [hR.lin_mul (hAN' hx) (hAN' hy), hyj, hxi, mulVec_mulVec, s0Mat_mul ε hi64 hj64]
  have hcomm : ∀ i ∈ X, ∀ j ∈ X, tabGet (mulTab ε) i j = tabGet (mulTab ε) j i := by
    intro i hi j hj
    obtain ⟨hi64, x, hx, hxi⟩ := hmemX.1 hi
    obtain ⟨hj64, y, hy, hyj⟩ := hmemX.1 hj
    refine tab_comm_of_commute ε hi64 hj64 (Matrix.ext_iff_mulVec.2 fun v => ?_)
    have e1 : lin ψ (x * y) v = (s0Mat ε i * s0Mat ε j) *ᵥ v := by
      rw [hR.lin_mul (hAN' hx) (hAN' hy), hyj, hxi, mulVec_mulVec]
    have e2 : lin ψ (y * x) v = (s0Mat ε j * s0Mat ε i) *ᵥ v := by
      rw [hR.lin_mul (hAN' hy) (hAN' hx), hxi, hyj, mulVec_mulVec]
    rw [← e1, ← e2, hAc x hx y hy]
  have hb := (abel_facts ε).2.2.2 _ (maskOf_mem_abelMasks ε hX64 h0 hmul hcomm)
  rw [popcount64_maskOf hX64, fixMask_maskOf ε hX64] at hb
  let φ : A →* Equiv.Perm V6 := hR.linHom.comp (Subgroup.inclusion hAN')
  have hφ : ∀ (x : A) v, φ x v = lin ψ x v := fun x v => rfl
  have hrange : Nat.card φ.range ≤ X.card := by
    have : ∀ σ : φ.range, ∃ i : X, ∀ v, (σ : Equiv.Perm V6) v = s0Mat ε i *ᵥ v := by
      rintro ⟨σ, x, rfl⟩
      obtain ⟨i, hi, hxi⟩ := hu.exists_s0 hR (hAU x.2)
      exact ⟨⟨i, hmemX.2 ⟨hi, x, x.2, hxi⟩⟩, fun v => by rw [hφ]; exact hxi v⟩
    choose f hf using this
    have hinj : Function.Injective f := by
      intro σ τ h
      exact Subtype.ext (Equiv.ext fun v => by rw [hf σ v, hf τ v, h])
    have := Nat.card_le_card_of_injective f hinj
    rwa [Nat.card_eq_finsetCard] at this
  have hker : Nat.card φ.ker ≤
      (Finset.univ.filter fun v : V6 => ∀ i ∈ X, s0Mat ε i *ᵥ v = v).card := by
    have hQ : ∀ x : φ.ker, ((x : A) : G) ∈ Q := by
      intro x
      have h1 : ∀ v, lin ψ (x : A) v = v := fun v => by
        rw [← hφ, MonoidHom.mem_ker.1 x.2]; rfl
      refine hPQ _ (hR.U_le_P (hAU (x : A).2)) (mem_centralizer_iff.2 fun q hq => ?_)
      obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
      have := (hR.lin_eq_iff (hAN' (x : A).2) v v).1 (h1 v)
      calc ψ v * ((x : A) : G) = (x : A) * ψ v * ((x : A) : G)⁻¹ * (x : A) := by rw [this]
        _ = (x : A) * ψ v := by group
    have hfix : ∀ x : φ.ker, coord ψ ((x : A) : G) ∈
        Finset.univ.filter fun v : V6 => ∀ i ∈ X, s0Mat ε i *ᵥ v = v := by
      intro x
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i hi => ?_⟩
      obtain ⟨-, y, hy, hyi⟩ := hmemX.1 hi
      rw [← hyi, hR.lin_eq_iff (hAN' hy), hR.ψ_coord (hQ x)]
      rw [hAc y hy _ (x : A).2, mul_inv_cancel_right]
    let f : φ.ker → {v // v ∈ Finset.univ.filter fun v : V6 => ∀ i ∈ X, s0Mat ε i *ᵥ v = v} :=
      fun x => ⟨_, hfix x⟩
    have hinj : Function.Injective f := by
      intro x y h
      have h' : coord ψ ((x : A) : G) = coord ψ ((y : A) : G) := congrArg Subtype.val h
      have := congrArg ψ h'
      rw [hR.ψ_coord (hQ x), hR.ψ_coord (hQ y)] at this
      exact Subtype.ext (Subtype.ext this)
    have := Nat.card_le_card_of_injective f hinj
    rwa [Nat.card_eq_finsetCard] at this
  have hcard : Nat.card A = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hcard]
  calc Nat.card φ.ker * Nat.card φ.range ≤
        (Finset.univ.filter fun v : V6 => ∀ i ∈ X, s0Mat ε i *ᵥ v = v).card * X.card :=
        Nat.mul_le_mul hker hrange
    _ ≤ 64 := by rw [mul_comm]; exact hb

theorem uData_of_link (h : LinkFacts ε L U Q P a ψ p u) : UData ε U Q ψ u :=
  ⟨h.u_mem, fun k v => by rw [h.u_act, urRows_eq_uRows], h.U_le⟩

end Group

end CFSG.EvenSmallLie.OmegaEight.Chain

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn.SetupX

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

variable {G : Type} [Group G] {ε : Eps} {t : G}
  {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G} {x₀ : G}

theorem relIndex_U_TH [Finite G] (hS : SetupX ε t L H₀ U Q P a ψ p u x₀) :
    U.relIndex (U ⊔ zpowers x₀ ⊔ zpowers t) = 4 := by
  have hU2 : Nat.card (U ⊔ zpowers x₀ : Subgroup G) = 2 * Nat.card U :=
    Stage0.card_sup_zpowers hS.inputs.outer.sq hS.inputs.outer.normalizes_U
      fun h => hS.inputs.outer.not_mem (hS.rad.U_le_L h)
  have hT := hS.sp.card_sup hS.S₀_le_H₀
  have hm := relIndex_mul_card (H := U) (K := U ⊔ zpowers x₀ ⊔ zpowers t)
  rw [inf_of_le_left (le_sup_left.trans le_sup_left), hT, hU2] at hm
  have hpos : 0 < Nat.card U := Nat.card_pos
  nlinarith

theorem abelBound [Finite G] (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
    {B : Subgroup G} (hBC : B ≤ centralizer ({t} : Set G)) (hB2 : IsPGroup 2 B)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) : Nat.card B ≤ 256 := by
  have hR := hS.rad
  have hu := uData_of_link hS.inputs.link
  obtain ⟨k, -, hkB⟩ := exists_conj_le_of_maximal hS.TH_le_centralizer hS.isPGroup_TH
    (fun T hT hT2 hDT => hS.sylow_TH T hT hT2 hDT) hBC hB2
  set B' : Subgroup G := B.map (MulAut.conj k).toMonoidHom with hB'
  have hcardB : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hB'D : B' ≤ U ⊔ zpowers x₀ ⊔ zpowers t := by
    rintro _ ⟨x, hx, rfl⟩
    exact hkB x hx
  have hB'c : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show k * x * k⁻¹ * (k * y * k⁻¹) = k * (x * y) * k⁻¹ by group, hBc x hx y hy]
    group
  have hA : Nat.card (U ⊓ B' : Subgroup G) ≤ 64 :=
    hu.card_le_of_abelian_of hR (fun x hx hc => hS.mem_Q_of_mem_P hx hc) inf_le_left
      fun x hx y hy => hB'c x hx.2 y hy.2
  have hUD := hS.relIndex_U_TH
  have hidx : U.relIndex B' ≤ 4 :=
    (relIndex_le_of_le_right hB'D (by rw [hUD]; norm_num)).trans hUD.le
  have hm := relIndex_mul_card (H := U) (K := B')
  rw [← hcardB, ← hm]
  calc U.relIndex B' * Nat.card (U ⊓ B' : Subgroup G) ≤ 4 * 64 := Nat.mul_le_mul hidx hA
    _ = 256 := by norm_num

end CFSG.EvenSmallLie.OmegaEight.SplitIn.SetupX
