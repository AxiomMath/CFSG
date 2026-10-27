module

public import CFSG.ClassicalInvolution.Q3.TL3T41
public import CFSG.ClassicalInvolution.Q3.TL3T39

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE

variable {G : Type} [Group G] [Finite G]

theorem exists_aeIdent_span {r : ℕ} {Ω : Set (Subgroup G)} (hD : ThmDHyp r Ω)
    (hbelow : ThmDAbsBelow r (Nat.card G)) (h8 : ∀ L ∈ Ω, Nat.card L = 8)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hlt : Nat.card ↥(pSpan P) < Nat.card G)
    (htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L')
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hns : ∃ L ∈ P, ∃ L' ∈ P, L ≠ L')
    (h5 : ∃ x ∈ pSpan P, x ^ 5 = 1 ∧ ∃ w ∈ pSpan P, x * w ≠ w * x)
    (h3 : ∃ L ∈ P, ∃ y ∈ pSpan P, y ^ 3 = 1 ∧ conjSub y L = L ∧ ¬ ∀ l ∈ L, y * l = l * y) :
    ∃ m : ℕ, 5 ≤ m ∧ Nonempty (AEIdent P m) := by
  classical
  set Y := pSpan P with hY
  set R := classicalInvolutionOddCore ↥Y with hR
  set q := QuotientGroup.mk' R with hq
  have hLY : ∀ M ∈ P, M ≤ Y := fun M hM => le_pSpan hM
  have hO := thmDHypO_restrict (r := r) hD.hyp hD.two hD.card hD.aEmpty hD.inO2 hPΩ hinv
  have hRc : R ≤ Subgroup.center ↥Y := oddCore_le_center hD.hyp hD.two hD.inO2 hPΩ hinv
  have hRK : ∀ K ∈ restrictFamily P Y, R ⊓ K = ⊥ := fun K hK =>
    oddCore_inf_eq_bot (hO.two K hK)
  have hQ := thmDHypO_quotZ hO hRc hRK
  have hmemY : ∀ M ∈ P, M.subgroupOf Y ∈ restrictFamily P Y := fun M hM =>
    ⟨M, hM, hLY M hM, rfl⟩
  have hcent : ∀ x : ↥Y, q x = 1 → ∀ w : ↥Y, x * w = w * x := by
    intro x hx w
    have hxR : x ∈ R := (QuotientGroup.eq_one_iff x).mp hx
    exact (Subgroup.mem_center_iff.mp (hRc hxR) w).symm
  obtain ⟨x, hxY, hx5, w, hwY, hxw⟩ := h5
  have hqx : q ⟨x, hxY⟩ ≠ 1 := fun h => hxw (congrArg Subtype.val (hcent _ h ⟨w, hwY⟩))
  have hqx5 : q ⟨x, hxY⟩ ^ 5 = 1 := by
    rw [← map_pow, show (⟨x, hxY⟩ : ↥Y) ^ 5 = 1 from Subtype.ext (by simpa using hx5), map_one]
  have hodd : classicalInvolutionOddCore ↥(pSpan (quotFamZ R (restrictFamily P Y))) = ⊥ := by
    rw [hQ.gen]
    exact classicalInvolutionOddCore_eq_bot_of_mulEquiv Subgroup.topEquiv.symm
      (QuaternionStructure.oddCore_quotient_oddCore_eq_bot _)
  have hc2 := isPGroup_center_of_oddCore hodd
  have hxbar : q ⟨x, hxY⟩ ∈ pSpan (quotFamZ R (restrictFamily P Y)) := by
    rw [hQ.gen]
    exact Subgroup.mem_top _
  have hx5' : (⟨q ⟨x, hxY⟩, hxbar⟩ : ↥(pSpan (quotFamZ R (restrictFamily P Y)))) ^ 5 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hqx5)
  rcases thmDConcl_spanQuot hD hbelow hPΩ hlt htrans hinv with
    hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | ⟨I⟩ | ⟨m, hm, ⟨I⟩⟩ | ⟨I⟩
  ·
    exfalso
    obtain ⟨L, hL, L', hL', hne⟩ := hns
    have h1 := hsing _ ⟨_, hmemY L hL, rfl⟩ _ ⟨_, hmemY L' hL', rfl⟩
    have h2 := eq_of_map_eq hO.hyp hO.two hRc hRK (hmemY L hL) (hmemY L' hL') h1
    have h2' := Subgroup.subgroupOf_inj.mp h2
    rw [inf_eq_left.mpr (hLY L hL), inf_eq_left.mpr (hLY L' hL')] at h2'
    exact hne h2'
  ·
    exfalso
    obtain ⟨L₀, hL₀, -⟩ := hns
    have hr : 2 ^ r = 8 := by rw [← hD.card L₀ (hPΩ hL₀), h8 L₀ (hPΩ hL₀)]
    obtain ⟨L₁, hL₁, y₀, hy₀Y, hy₀3, hy₀L, hy₀c⟩ := h3
    refine wSet_ne_singleton hQ.hyp hQ.two (fun J hJ => by rw [hQ.card J hJ, hr])
      ⟨_, ⟨_, hmemY L₀ hL₀, rfl⟩⟩ ?_ W hW
    rintro _ ⟨_, ⟨L, hL, -, rfl⟩, rfl⟩ U hUL hUi hUc
    obtain ⟨t, htY, htL⟩ := htrans L₁ hL₁ L hL
    set y := t * y₀ * t⁻¹ with hy
    have hyY : y ∈ Y := Y.mul_mem (Y.mul_mem htY hy₀Y) (Y.inv_mem htY)
    have hy3 : y ^ 3 = 1 := by rw [hy, conj_pow, hy₀3, mul_one, mul_inv_cancel]
    have hyL : conjSub y L = L := by
      rw [hy, conjSub_mul, conjSub_mul, ← htL, conjSub_inv_conjSub, hy₀L]
    have hyc : ¬ ∀ l ∈ L, y * l = l * y := by
      intro hc
      apply hy₀c
      intro l hl
      have hl' : t * l * t⁻¹ ∈ L := by
        rw [← htL]
        exact conj_mem_conjSub hl
      have e := hc _ hl'
      calc y₀ * l = t⁻¹ * (y * (t * l * t⁻¹)) * t := by rw [hy]; group
        _ = t⁻¹ * ((t * l * t⁻¹) * y) * t := by rw [e]
        _ = l * y₀ := by rw [hy]; group
    refine ⟨q ⟨y, hyY⟩, ?_, ?_⟩
    · rw [← TwistQ.conjSub_map, conjSub_subgroupOf, hyL]
    · intro hyU
      apply hyc
      have hyL' : conjSub (q ⟨y, hyY⟩) ((L.subgroupOf Y).map q) = (L.subgroupOf Y).map q := by
        rw [← TwistQ.conjSub_map, conjSub_subgroupOf, hyL]
      have hcard : Nat.card ↥((L.subgroupOf Y).map q) = 8 := by
        rw [hQ.card _ ⟨_, hmemY L hL, rfl⟩, hr]
      have hy3' : q ⟨y, hyY⟩ ^ 3 = 1 := by
        rw [← map_pow, show (⟨y, hyY⟩ : ↥Y) ^ 3 = 1 from Subtype.ext (by simpa using hy3),
          map_one]
      have hcL := comm_of_pow_three_of_conjSub_eq hcard hUL hUi hUc hy3' hyL' hyU
      intro l hl
      have hlY : l ∈ Y := hLY L hL hl
      have h1 := hcL (q ⟨l, hlY⟩) ⟨⟨l, hlY⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      set c : ↥Y := ⟨y, hyY⟩ * ⟨l, hlY⟩ * ⟨y, hyY⟩⁻¹ * ⟨l, hlY⟩⁻¹ with hc
      have hcR : c ∈ R := by
        refine (QuotientGroup.eq_one_iff c).mp ?_
        show q (⟨y, hyY⟩ * ⟨l, hlY⟩ * ⟨y, hyY⟩⁻¹ * ⟨l, hlY⟩⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      have hcL' : c ∈ L.subgroupOf Y := by
        rw [Subgroup.mem_subgroupOf]
        show y * l * y⁻¹ * l⁻¹ ∈ L
        have h2 : y * l * y⁻¹ ∈ L := by
          rw [← hyL]
          exact conj_mem_conjSub hl
        exact L.mul_mem h2 (L.inv_mem hl)
      have hc1 : c = 1 := by
        have h3' : c ∈ R ⊓ L.subgroupOf Y := ⟨hcR, hcL'⟩
        rwa [hRK _ (hmemY L hL), Subgroup.mem_bot] at h3'
      have hc1' : y * l * y⁻¹ * l⁻¹ = 1 := congrArg Subtype.val hc1
      calc y * l = y * l * y⁻¹ * l⁻¹ * l * y := by group
        _ = l * y := by rw [hc1', one_mul]
  ·
    exact absurd (E8Struct.pow_five hE hqx5) hqx
  ·
    exfalso
    obtain ⟨I⟩ := I
    have hk : IsPGroup 2 I.φ.ker := hc2.to_le I.ker_le
    have := I.pow_five hk (fun h hh h5' => aeBarOver_pow_five
      (fun σ hσ hσ5 => l32_pow_five hσ hσ5) hh h5') hx5'
    exact hqx (congrArg Subtype.val this)
  ·
    exact ⟨m, hm, ⟨AEIdent.ofSpanQuot hD hPΩ hinv I⟩⟩
  ·
    exfalso
    obtain ⟨I⟩ := I
    have hk : IsPGroup 2 I.φ.ker := hc2.to_le I.ker_le
    have := I.pow_five hk (fun h hh h5' => aeBarOver_pow_five
      (fun σ hσ hσ5 => agl32_pow_five hσ hσ5) hh h5') hx5'
    exact hqx (congrArg Subtype.val this)

end CFSG.ClassicalInvolution.Q3.TC.Thin
