module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionArms
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.OutSmallSporadic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.CenterFree
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.HSThreeCent

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier

private lemma card_centralizer_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card (centralizer ({e x} : Set H)) = Nat.card (centralizer ({x} : Set G)) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun y => ⟨e.symm y, ?_⟩
      invFun := fun y => ⟨e y, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg e.symm (Subgroup.mem_centralizer_singleton_iff.mp y.2)
    simpa using h
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg e (Subgroup.mem_centralizer_singleton_iff.mp y.2)
    simpa using h
  · intro y
    apply Subtype.ext
    simp
  · intro y
    apply Subtype.ext
    simp

theorem nonempty_mulEquiv_hsR
    {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hC : centralizer (N : Set Y) ≤ N) (hZ : center ↥N = ⊥) (hN : IsSporadic N .HS)
    (hidx : N.index = 2) : Nonempty (Y ≃* ↥hsR) := by
  obtain ⟨e⟩ := hN
  let θ : ↥N ≃* ↥hsP := e.trans hsPermEquiv
  have h := hs_autModel
  have hC' : centralizer (N : Set Y) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxN : x ∈ N := hC hx
    have hxc : (⟨x, hxN⟩ : ↥N) ∈ center ↥N := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hx (z : Y) z.2
    rw [hZ] at hxc
    simpa using Subgroup.mem_bot.mp hxc
  let ι : Y →* Equiv.Perm (Fin 3850) := h.embed N θ
  let ι' : Y →* ↥hsR := ι.codRestrict hsR (fun x => h.embed_mem N θ x)
  have hι'inj : Function.Injective ι' :=
    (MonoidHom.injective_codRestrict ι hsR (fun x => h.embed_mem N θ x)).mpr
      (h.embed_injective N θ hC')
  have hcardY : Nat.card Y = 88704000 := by
    have h1 : Nat.card Y = Nat.card ↥N * N.index := (Subgroup.card_mul_index (H := N)).symm
    rw [h1, hidx, Nat.card_congr θ.toEquiv, card_hsP]
  obtain ⟨-, -, -, -, -, -, -, -, hRcard, -⟩ := hs_normalizing_model
  have hle : Nat.card ↥hsR ≤ Nat.card Y := by rw [hcardY, hRcard]
  exact ⟨MulEquiv.ofBijective ι' (hι'inj.bijective_of_nat_card_le hle)⟩

theorem false_of_mulEquiv_hsR
    {Y : Type} [Group Y]
    [Finite Y] (e : Y ≃* ↥hsR) (P : Subgroup Y) (hP : Nat.card P = 9)
    (hPc : ∀ a ∈ P, a ≠ 1 → Nat.card (centralizer ({a} : Set Y)) = 360) : False := by
  obtain ⟨hxmem, hx3, hcent⟩ := hs_three_centralizer
  let x' : ↥hsR := ⟨tp 3850 (hsCentTbl 32), hxmem⟩
  let y₀ : Y := e.symm x'
  have hy3 : orderOf y₀ = 3 := by
    simpa [y₀, x'] using hx3
  have hcent' : 720 ≤ Nat.card (centralizer ({x'} : Set ↥hsR)) := by
    have hmap := map_subtype_centralizer hsR x'
    have hc := Subgroup.card_map_of_injective (K := centralizer ({x'} : Set ↥hsR))
      hsR.subtype_injective
    rw [hmap] at hc
    rw [← hc]
    simpa [x'] using hcent
  have hycent : Nat.card (centralizer ({y₀} : Set Y)) =
      Nat.card (centralizer ({x'} : Set ↥hsR)) := by
    simpa [y₀] using card_centralizer_mulEquiv e.symm x'
  have hycent720 : 720 ≤ Nat.card (centralizer ({y₀} : Set Y)) := by
    rw [hycent]
    exact hcent'
  have hcardY : Nat.card Y = 88704000 := by
    rw [Nat.card_congr e.toEquiv]
    obtain ⟨-, -, -, -, -, -, -, -, hRcard, -⟩ := hs_normalizing_model
    exact hRcard
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hPpow : Nat.card P = 3 ^ 2 := by rw [hP]; norm_num
  have hk : ¬ 3 ^ (2 + 1) ∣ Nat.card Y := by rw [hcardY]; norm_num
  obtain ⟨g, hg⟩ := exists_conj_mem_of_card_eq_pow (p := 3) (k := 2) hPpow hk (x := y₀) hy3
  let a : Y := g * y₀ * g⁻¹
  have haP : a ∈ P := by simpa [a] using hg
  have ha3 : orderOf a = 3 := by
    have h1 : a = MulAut.conj g y₀ := by simp [a, MulAut.conj_apply]
    rw [h1, MulEquiv.orderOf_eq, hy3]
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ha3
    omega
  have hca : Nat.card (centralizer ({a} : Set Y)) = Nat.card (centralizer ({y₀} : Set Y)) := by
    simpa [a, MulAut.conj_apply] using card_centralizer_mulAut (MulAut.conj g) y₀
  have hPca := hPc a haP ha1
  omega

theorem inspectionArm_hs :
    InspectionArm fun N _ => IsSporadic N .HS := by
  intro Y _ _ N hN hC hQ P hPab hP3 hP9 hPc hw
  haveI := hN
  have hZ : center ↥N = ⊥ := center_eq_bot_of_isSporadic_hs hQ
  have hidx0 : N.index ≤ 2 := index_le_of_card_mulAut_le hC hZ (card_mulAut_le_of_isSporadic_hs hQ)
  have hidxne : N.index ≠ 0 := by
    intro h0
    have hcard := Subgroup.card_mul_index (H := N)
    rw [h0, mul_zero] at hcard
    have := Finite.card_pos (α := Y)
    omega
  have hcases : N.index = 1 ∨ N.index = 2 := by omega
  rcases hcases with h1 | h2
  · have hNtop : N = ⊤ := Subgroup.index_eq_one.mp h1
    obtain ⟨eN⟩ := hQ
    exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hNtop.symm)).trans eN⟩
  · exfalso
    obtain ⟨e⟩ := nonempty_mulEquiv_hsR hC hZ hQ h2
    exact false_of_mulEquiv_hsR e P hP9 hPc

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
