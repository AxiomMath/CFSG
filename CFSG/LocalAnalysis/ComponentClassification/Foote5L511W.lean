module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511V

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter CFSG.GH74.GLS.IVK.Lifted

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
include h

omit [Finite 𝕊] in
theorem card_le_four_of_dsd_Q_L511W (hDQ : DSDData ↥Q) {b : G} (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hbz : b ≠ z) {W : Subgroup G} (hW2 : IsPGroup 2 W) (hWC : W ≤ coreActionKernel L)
    (hWz : W ≤ centralizer ({z} : Set G)) (hWb : W ≤ centralizer ({b} : Set G)) (hbW : b ∈ W) :
    Nat.card W ≤ 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQz : Q ≤ centralizer ({z} : Set G) := fun q hq =>
    mem_centralizer_singleton_iff.mpr (h.zS q (h.QS hq))
  have hQsyl : IsSylowOf 2 Q (coreActionKernel L ⊓ centralizer ({z} : Set G)) :=
    h.sylQ.of_le (le_inf h.Q_le hQz) inf_le_left
  obtain ⟨k, hk, hkW⟩ := exists_conj_le_of_isSylowOf hQsyl (le_inf hWC hWz) hW2
  have hkz : k * z = z * k := mem_centralizer_singleton_iff.mp (mem_inf.mp hk).2
  set b₁ := k⁻¹ * b * k with hb₁
  have hb₁Q : b₁ ∈ Q := hkW b hbW
  have hb₁2 : b₁ * b₁ = 1 := by
    rw [hb₁, show k⁻¹ * b * k * (k⁻¹ * b * k) = k⁻¹ * (b * b) * k by group, hb2]
    group
  have hb₁1 : b₁ ≠ 1 := fun h1 => hb1 (by
    calc b = k * b₁ * k⁻¹ := by rw [hb₁]; group
      _ = 1 := by rw [h1]; group)
  have hb₁z : z ≠ b₁ := fun h1 => hbz (by
    calc b = k * b₁ * k⁻¹ := by rw [hb₁]; group
      _ = k * z * k⁻¹ := by rw [h1]
      _ = z := by rw [hkz, mul_inv_cancel_right])
  have hz1 : z ≠ 1 := fun h1 => by
    have h2 := h.z2
    rw [h1, orderOf_one] at h2
    omega
  have hzb₁ : z * b₁ = b₁ * z := (h.zS b₁ (h.QS hb₁Q)).symm
  have hsub : ∀ x ∈ conjugate W k, x ∈ ({z * b₁, z, b₁, 1} : Finset G) := by
    intro x hx
    have hw := mem_conjugate_iff.mp hx
    have hxQ : x ∈ Q := by
      have h1 := hkW _ hw
      rwa [show k⁻¹ * (k * x * k⁻¹) * k = x by group] at h1
    have hwz := mem_centralizer_singleton_iff.mp (hWz hw)
    have hwb := mem_centralizer_singleton_iff.mp (hWb hw)
    have hxz : x * z = z * x := by
      calc x * z = k⁻¹ * ((k * x * k⁻¹) * z) * k := by
            rw [show k⁻¹ * ((k * x * k⁻¹) * z) * k = x * (k⁻¹ * z * k) by group,
              show k⁻¹ * z * k = z by rw [mul_assoc, ← hkz]; group]
        _ = k⁻¹ * (z * (k * x * k⁻¹)) * k := by rw [hwz]
        _ = z * x := by
            rw [show k⁻¹ * (z * (k * x * k⁻¹)) * k = (k⁻¹ * z * k) * x by group,
              show k⁻¹ * z * k = z by rw [mul_assoc, ← hkz]; group]
    have hxb : x * b₁ = b₁ * x := by
      calc x * b₁ = k⁻¹ * ((k * x * k⁻¹) * b) * k := by rw [hb₁]; group
        _ = k⁻¹ * (b * (k * x * k⁻¹)) * k := by rw [hwb]
        _ = b₁ * x := by rw [hb₁]; group
    rcases mem_of_commute_four_of_dsd_L512 h.isPGroup_Q hDQ h.zQ hb₁Q h.z_mul_self hb₁2 hz1
      hb₁1 hb₁z hzb₁ hxQ hxz hxb with h1 | h1 | h1 | h1 <;> rw [h1] <;> simp
  rw [← card_conjugate_eq_card W k]
  exact (SmallLocal.card_le_of_forall_mem_finset _ hsub).trans Finset.card_le_four

include ε in
theorem false_of_card_le_four_L511W {b : G} (hbQ : b ∈ Q) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hbz : b ≠ z)
    (hW4 : ∀ W : Subgroup G, IsPGroup 2 W → W ≤ coreActionKernel L →
      W ≤ centralizer ({z} : Set G) → W ≤ centralizer ({b} : Set G) → b ∈ W → Nat.card W ≤ 4)
    {T' : Subgroup G} (hT'2 : IsPGroup 2 T') (hT'C : T' ≤ centralizer ({b} : Set G))
    (hT'card : Nat.card T' = 2 * Nat.card S) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := h.sec4
  have hbS := h.QS hbQ
  have hb2' : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have hbC : b ∈ coreActionKernel L := h.Q_le hbQ
  obtain ⟨hfix, hLb, hLbF⟩ := footeFixed_eq_footeF h4.hLB h4.hGA h4.hGC h4.hSA
    h4.footeFamilyType h4.huniq h4.hrank2 h.pmax h.memF hb2' hbC
  obtain ⟨εb, hεb⟩ := exists_actG_eq_of_footeFixed hfix h.zL hb2' hbC hLb ε
  have hCbN := le_normalizer_of_mem_footeFamilyOf h4.huniq hLb hLbF
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hhalf := h.two_mul_twoPart_le_L511V hbQ hb2 hb1 hbz hT'2 hT'C (by omega)
  obtain ⟨T'', hT'', hST''⟩ := exists_isSylowOf_ge_of_le (X := centralizer ({b} : Set G))
    (A := S ⊓ centralizer ({b} : Set G)) inf_le_right (h.isPGroup_S.to_le inf_le_left)
  have hT''C := hT''.le
  have hT''N := hT''C.trans hCbN
  have hT''2 := hT''.isPGroup
  have hT''card : 2 * Nat.card S ≤ Nat.card T'' := by
    rw [← hT'card, hT''.card_eq]
    exact card_le_twoPart hT'2 hT'C
  have hzb : z * b = b * z := (h.zS b hbS).symm
  have hzT : z ∈ T'' := hST'' (mem_inf.mpr ⟨h.zS_mem, mem_centralizer_singleton_iff.mpr hzb⟩)
  have hbT : b ∈ T'' := hST'' (mem_inf.mpr ⟨hbS, mem_centralizer_singleton_iff.mpr rfl⟩)
  have hzC : z ∈ coreActionKernel (footeF L₀ b) :=
    (h.mem_coreActionKernel_footeF_iff hbC hb2' (h.S_le h.zS_mem)
      (mem_centralizer_singleton_iff.mpr hzb)).mpr (h.Q_le h.zQ)
  have hbC' : b ∈ coreActionKernel (footeF L₀ b) :=
    (h.mem_coreActionKernel_footeF_iff hbC hb2' (h.S_le hbS)
      (mem_centralizer_singleton_iff.mpr rfl)).mpr hbC
  have hz1 : z ≠ 1 := fun h1 => by
    have h2 := h.z2
    rw [h1, orderOf_one] at h2
    omega
  have hTC : ∀ g ∈ T'', ∀ x ∈ coreActionKernel (footeF L₀ b),
      g * x * g⁻¹ ∈ coreActionKernel (footeF L₀ b) := by
    intro g hg x hx
    have hgN := hT''N hg
    have hxN : x ∈ normalizer (footeF L₀ b : Set G) := (mem_coreActionKernel.mp hx).1
    rw [← actG_eq_one_iff εb (mul_mem (mul_mem hgN hxN) (inv_mem hgN)),
      actG_mul εb (mul_mem hgN hxN) (inv_mem hgN), actG_mul εb hgN hxN,
      (actG_eq_one_iff εb hxN).mpr hx, actG_inv εb hgN, mul_one, mul_inv_cancel]
  have horb := card_lt_card_inf_mul_card_centralizer_L511V hzT hzC hz1 hTC
  set P := T'' ⊓ centralizer ({z} : Set G) with hP
  have hPN : P ≤ normalizer (L : Set G) := inf_le_right.trans h.centralizer_le_normalizer
  have hPNb : P ≤ normalizer (footeF L₀ b : Set G) := inf_le_left.trans hT''N
  have hP2 : IsPGroup 2 P := hT''2.to_le inf_le_left
  have hPcard := card_eq_card_inf_mul_card_actImage εb hPNb
  have himg : actImage (footeF L₀ b) εb P = actImage L ε P := by
    ext α
    rw [mem_actImage εb hPNb, mem_actImage ε hPN]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, (hεb p (hPN hp) (hPNb hp) (hT''C (mem_inf.mp hp).1)).symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, hεb p (hPN hp) (hPNb hp) (hT''C (mem_inf.mp hp).1)⟩
  have hSz : IsSylowOf 2 S (centralizer ({z} : Set G)) :=
    h.sylS.of_le h.S_le_centralizer h.centralizer_le_normalizer
  have hPS := card_actImage_le_of_isSylowOf_L511V ε h.centralizer_le_normalizer hSz inf_le_right
    hP2
  rw [himg] at hPcard
  have hW4' : Nat.card ↥(P ⊓ coreActionKernel (footeF L₀ b)) ≤ 4 := by
    refine hW4 _ (hP2.to_le inf_le_left) ?_
      (inf_le_left.trans inf_le_right) (inf_le_left.trans (inf_le_left.trans hT''C))
      (mem_inf.mpr ⟨mem_inf.mpr ⟨hbT, mem_centralizer_singleton_iff.mpr hzb.symm⟩, hbC'⟩)
    intro w hw
    have hwP := (mem_inf.mp hw).1
    exact (h.mem_coreActionKernel_footeF_iff hbC hb2' (hPN hwP)
      (hT''C (mem_inf.mp hwP).1)).mp (mem_inf.mp hw).2
  have hS := card_eq_card_inf_mul_card_actImage ε h.S_le
  rw [h.inf_coreActionKernel] at hS
  have hX : 2 * Nat.card ↥(T'' ⊓ coreActionKernel (footeF L₀ b)) ≤ Nat.card Q :=
    (Nat.mul_le_mul_left 2 (card_le_twoPart (hT''2.to_le inf_le_left) inf_le_right)).trans hhalf
  have e1 : Nat.card P ≤ 4 * Nat.card (actImage L ε S) := by
    rw [hPcard]
    exact Nat.mul_le_mul hW4' hPS
  obtain ⟨x, hx⟩ : ∃ x, Nat.card ↥(T'' ⊓ coreActionKernel (footeF L₀ b)) = x := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, Nat.card (actImage L ε S) = σ := ⟨_, rfl⟩
  rw [hx] at hX horb
  rw [hσ] at e1 hS
  have hlt : x * Nat.card P < x * Nat.card P := calc
    _ ≤ x * (4 * σ) := Nat.mul_le_mul_left _ e1
    _ = 2 * ((2 * x) * σ) := by ring
    _ ≤ 2 * (Nat.card Q * σ) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hX)
    _ = 2 * Nat.card S := by rw [hS]
    _ ≤ Nat.card T'' := hT''card
    _ < _ := horb
  exact lt_irrefl _ hlt

end Sec5

end CFSG.ComponentClassification.Foote5
