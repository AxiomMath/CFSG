module

public import CFSG.Sporadic.Fi24.EdgeCent
public import CFSG.Sporadic.Fi24.Out
public import CFSG.Sporadic.Fi24.Complete
public import CFSG.Sporadic.Fi24.Ext

public section

namespace CFSG.EvenSporadicStandard.Solomon78.Fi24Row

open CFSG.Sporadic CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Sporadic.Fi24

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Edge


local notation "W" => (LocalClass D24 tR ∩ LocalClass D24 xb)

theorem mul_mem_JR_of_not_mem {x y : R} (hx : x ∉ JR) (hy : y ∉ JR) : x * y ∈ JR :=
  (Subgroup.mul_mem_iff_of_index_two index_JR).2 (iff_of_false hx hy)

variable (ψ : ↥W ≃ Fi22.D)
  (hψc : ∀ x y : ↥W, (x : R) * y = y * x ↔ (ψ x : Fi22.J) * ψ y = ψ y * ψ x)
  (hψt : ∀ x y : ↥W, ∃ h : (x : R) * y * x ∈ W, (ψ ⟨_, h⟩ : Fi22.J) = ψ x * ψ y * ψ x)
  (hfix22 : ∀ g : Fi22.J, g ^ 2 = 1 → g ≠ 1 →
    Nat.card {x : Fi22.D // g * (x : Fi22.J) * g⁻¹ = x} ∈ ({54, 182, 694} : Set ℕ))
  (hcent22 : ∀ (χ : Fi22.D) (σ : Equiv.Perm Fi22.D),
    (∀ g : Fi22.J, g * χ = χ * g →
      σ * Pair.conjPerm Fi22.pair_D g = Pair.conjPerm Fi22.pair_D g * σ) →
    σ = 1 ∨ σ = Pair.conjPerm Fi22.pair_D (χ : Fi22.J))
  {e : J} (he : EdgeSwap e)

noncomputable abbrev ρE : ↥(Subgroup.centralizer ({tR * xb} : Set R)) →* tauGroup Fi22.pair_D :=
  edgeHom pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt
    Fi22.center_eq_bot

include hfix22 he in
theorem edge_surj : Function.Surjective (edgeHomC pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24
    tR_ne_xb tR_xb_comm ψ hψc hψt Fi22.center_eq_bot (inf_le_left : CE ≤ _)) :=
  edgeHomC_surjective pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ
    hψc hψt Fi22.center_eq_bot Fi22.index_innerTau_range (inf_le_left : CE ≤ _) commutator_LE
    (by rw [Fi22.card_tauGroup]; exact card_LE) (fun ℓ hℓ h => eq_of_mem_LE_centralizes hℓ h)
    (jR_mem_CE he) (edgeHom_swap_not_mem he ψ hψc hψt hfix22)

include ψ hψc in
theorem edge_hW : ∀ w ∈ W, ∃ w' ∈ W, w * w' ≠ w' * w :=
  exists_not_commute_of_edgeEquiv Fi22.pair_D ψ hψc Fi22.center_eq_bot

include ψ hψc hψt hfix22 he in
theorem edge_center {z : R} (hz : z ∈ CE) (hc : ∀ c ∈ CE, z * c = c * z) :
    z = 1 ∨ z = tR * xb := by
  have h := center_edgeC pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt
    Fi22.center_eq_bot (inf_le_left : CE ≤ _) (edge_surj ψ hψc hψt hfix22 he)
    (card_CE he (edge_hW ψ hψc)) tR_mul_xb_mem_CE (z := ⟨z, hz⟩)
    (Subgroup.mem_center_iff.2 fun c => Subtype.ext (hc c c.2).symm)
  exact h

theorem tR_mul_mem_JR_of_mem {p : R} (hp : p ∈ D24) : tR * p ∈ JR :=
  mul_mem_JR_of_not_mem tR_not_mem_JR (not_mem_JR_of_mem_D24 hp)

theorem mem_CE_iff {x : R} : x ∈ CE ↔ x * (tR * xb) = (tR * xb) * x ∧ x ∈ JR := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem mem_LE_iff {x : R} :
    x ∈ Fi24.LE ↔ (x * (tR * xb) = (tR * xb) * x ∧ x ∈ JR) ∧ x * tR = tR * x := by
  rw [Subgroup.mem_inf, mem_CE_iff, Subgroup.mem_centralizer_singleton_iff]

theorem tR_mul_mem_LE {p : R} (hp : p ∈ W) : tR * p ∈ Fi24.LE := by
  have hpT : p * tR = tR * p := hp.1.2.2
  have hpx : p * xb = xb * p := hp.2.2.2
  rw [mem_LE_iff]
  refine ⟨⟨?_, tR_mul_mem_JR_of_mem hp.1.1⟩, ?_⟩
  · calc tR * p * (tR * xb) = tR * (p * tR) * xb := by group
      _ = tR * (tR * p) * xb := by rw [hpT]
      _ = (tR * tR) * (p * xb) := by group
      _ = (tR * tR) * (xb * p) := by rw [hpx]
      _ = tR * xb * (tR * p) := by
        calc (tR * tR) * (xb * p) = tR * (tR * xb) * p := by group
          _ = tR * (xb * tR) * p := by rw [tR_xb_comm]
          _ = tR * xb * (tR * p) := by group
  · calc tR * p * tR = tR * (p * tR) := by group
      _ = tR * (tR * p) := by rw [hpT]
      _ = tR * tR * p := by group
      _ = tR * (tR * p) := by group

include hfix22 he in
theorem edge_surj' (σ : tauGroup Fi22.pair_D) :
    ∃ c : ↥CE, ρE ψ hψc hψt (Subgroup.inclusion (inf_le_left : CE ≤ _) c) = σ :=
  edge_surj ψ hψc hψt hfix22 he σ

include ψ hψc hψt hfix22 he in
theorem edge_no_outer {w : R} (hwJ : w ∉ JR) (hc : ∀ c ∈ CE, c * w = w * c) : False := by
  have hab : w ∈ Subgroup.centralizer ({tR * xb} : Set R) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc _ tR_mul_xb_mem_CE).symm
  have h1 : ρE ψ hψc hψt ⟨w, hab⟩ = 1 := by
    have hcen : ρE ψ hψc hψt ⟨w, hab⟩ ∈ Subgroup.center (tauGroup Fi22.pair_D) := by
      rw [Subgroup.mem_center_iff]
      intro σ
      obtain ⟨c, rfl⟩ := edge_surj' ψ hψc hψt hfix22 he σ
      have hcw : Subgroup.inclusion (inf_le_left : CE ≤ _) c * (⟨w, hab⟩ : ↥(Subgroup.centralizer
          ({tR * xb} : Set R))) = ⟨w, hab⟩ * Subgroup.inclusion (inf_le_left : CE ≤ _) c :=
        Subtype.ext (hc c c.2)
      exact ((map_mul (ρE ψ hψc hψt) _ _).symm.trans
        ((congrArg (ρE ψ hψc hψt) hcw).trans (map_mul (ρE ψ hψc hψt) _ _)))
    rwa [center_tauGroup_eq_bot Fi22.pair_D Fi22.center_eq_bot, Subgroup.mem_bot] at hcen
  have hW : ∀ q ∈ W, w * q * w⁻¹ = q :=
    (edgeHom_eq_one_iff pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt
      Fi22.center_eq_bot ⟨w, hab⟩).1 h1
  rcases conj_eq_or_of_commute_mul pair_R tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm
      (edge_hW ψ hψc) (g := w) (Subgroup.mem_centralizer_singleton_iff.1 hab) with
    ⟨hT, hx⟩ | ⟨hT, hx⟩
  · have hwT : w * tR = tR * w := by
      calc w * tR = w * tR * w⁻¹ * w := by group
        _ = tR * w := by rw [hT]
    have hwx : w * xb = xb * w := by
      calc w * xb = w * xb * w⁻¹ * w := by group
        _ = xb * w := by rw [hx]
    have hm : tR * w ∈ Fi24.LE := by
      rw [mem_LE_iff]
      refine ⟨⟨?_, mul_mem_JR_of_not_mem tR_not_mem_JR hwJ⟩, ?_⟩
      · calc tR * w * (tR * xb) = tR * (w * tR) * xb := by group
          _ = tR * (tR * w) * xb := by rw [hwT]
          _ = (tR * tR) * (w * xb) := by group
          _ = (tR * tR) * (xb * w) := by rw [hwx]
          _ = tR * (tR * xb) * w := by group
          _ = tR * (xb * tR) * w := by rw [tR_xb_comm]
          _ = tR * xb * (tR * w) := by group
      · calc tR * w * tR = tR * (w * tR) := by group
          _ = tR * (tR * w) := by rw [hwT]
    have hcentW : ∀ q ∈ W, tR * w * q * (tR * w)⁻¹ = q := by
      intro q hq
      calc tR * w * q * (tR * w)⁻¹ = tR * (w * q * w⁻¹) * tR⁻¹ := by group
        _ = tR * q * tR := by rw [hW q hq, tR_inv]
        _ = (q * tR) * tR := by rw [hq.1.2.2]
        _ = q := by rw [mul_assoc, tR_mul_tR, mul_one]
    have hJ := hc (jR e) (jR_mem_CE he)
    rcases eq_of_mem_LE_centralizes hm hcentW with h | h
    · have hw : w = tR := by
        calc w = tR * (tR * w) := by rw [tR_mul_tR_mul]
          _ = tR := by rw [h, mul_one]
      rw [hw] at hJ
      apply tR_ne_xb
      calc tR = jR e * tR * (jR e)⁻¹ := by rw [hJ]; group
        _ = xb := he.swap_tR
    · have hw : w = xb := by
        calc w = tR * (tR * w) := by rw [tR_mul_tR_mul]
          _ = tR * (tR * xb) := by rw [h]
          _ = xb := by rw [tR_mul_tR_mul]
      rw [hw] at hJ
      apply tR_ne_xb
      calc tR = jR e * xb * (jR e)⁻¹ := by rw [← he.swap_xb]
        _ = xb := by rw [hJ]; group
  · obtain ⟨y, hy⟩ := Pair.nonempty Fi22.pair_D
    set p : R := ((ψ.symm ⟨y, hy⟩ : ↥W) : R) with hpdef
    have hp : p ∈ W := (ψ.symm ⟨y, hy⟩).2
    have hpw : w * p * w⁻¹ = p := hW p hp
    have hcTp := hc _ (Subgroup.mem_inf.1 (tR_mul_mem_LE hp)).1
    have e1 : w * (tR * p) * w⁻¹ = tR * p := by rw [← hcTp]; group
    have e2 : w * tR * w⁻¹ = tR := by
      calc w * tR * w⁻¹ = (w * (tR * p) * w⁻¹) * (w * p * w⁻¹)⁻¹ := by group
        _ = (tR * p) * p⁻¹ := by rw [e1, hpw]
        _ = tR := by group
    exact tR_ne_xb (e2.symm.trans hT)

include ψ hψc hψt in
theorem LE_trans_W {x x' : R} (hx : x ∈ W) (hx' : x' ∈ W) :
    ∃ ℓ ∈ Fi24.LE, ℓ * x * ℓ⁻¹ = x' := by
  have hrangeL := range_edgeHomL pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ
    hψc hψt Fi22.center_eq_bot Fi22.index_innerTau_range (inf_le_left : CE ≤ _) commutator_LE
    (by rw [Fi22.card_tauGroup]; exact card_LE) (fun ℓ hℓ h => eq_of_mem_LE_centralizes hℓ h)
  obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj Fi22.pair_D (ψ ⟨x, hx⟩).2 (ψ ⟨x', hx'⟩).2)
  have hmem : innerTau Fi22.pair_D g ∈ (innerTau Fi22.pair_D).range := ⟨g, rfl⟩
  rw [← hrangeL] at hmem
  obtain ⟨ℓ, hℓ⟩ := hmem
  refine ⟨(ℓ : R), ℓ.2, ?_⟩
  have h1 := edgeHom_apply pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
    hψt Fi22.center_eq_bot (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) ⟨x, hx⟩
  have h2 : ((ρE ψ hψc hψt (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) :
      tauGroup Fi22.pair_D) : Equiv.Perm Fi22.D) (ψ ⟨x, hx⟩) = ψ ⟨x', hx'⟩ := by
    have h0 : ρE ψ hψc hψt (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) =
        innerTau Fi22.pair_D g := hℓ
    rw [h0]
    apply Subtype.ext
    show g * (ψ ⟨x, hx⟩ : Fi22.J) * g⁻¹ = ψ ⟨x', hx'⟩
    exact hg
  have h3 := ψ.injective (h1.symm.trans h2)
  have h4 := congrArg Subtype.val h3
  rw [edgeHomW_val] at h4
  exact h4

include ψ hψc hψt he in
theorem swap_base {p : R} (hp : p ∈ W) :
    ∃ s ∈ JR, s * tR * s⁻¹ = xb ∧ s * xb * s⁻¹ = tR ∧ s * p * s⁻¹ = p := by
  have hCE := jR_mem_CE he
  have hcomm : jR e * (tR * xb) = tR * xb * jR e := ((mem_CE_iff).1 hCE).1
  have hq : jR e * p * (jR e)⁻¹ ∈ W :=
    conj_mem_edge pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
      Fi22.center_eq_bot hcomm hp
  obtain ⟨ℓ, hℓ, hℓp⟩ := LE_trans_W ψ hψc hψt hq hp
  have hℓJ : ℓ ∈ JR := (mem_LE_iff.1 hℓ).1.2
  have hℓT : ℓ * tR = tR * ℓ := (mem_LE_iff.1 hℓ).2
  have hℓx : ℓ * xb = xb * ℓ := commute_xb_of_mem_LE hℓ
  refine ⟨ℓ * jR e, JR.mul_mem hℓJ (jR_mem_JR e), ?_, ?_, ?_⟩
  · calc ℓ * jR e * tR * (ℓ * jR e)⁻¹ = ℓ * (jR e * tR * (jR e)⁻¹) * ℓ⁻¹ := by group
      _ = ℓ * xb * ℓ⁻¹ := by rw [he.swap_tR]
      _ = xb := by rw [hℓx]; group
  · calc ℓ * jR e * xb * (ℓ * jR e)⁻¹ = ℓ * (jR e * xb * (jR e)⁻¹) * ℓ⁻¹ := by group
      _ = ℓ * tR * ℓ⁻¹ := by rw [he.swap_xb]
      _ = tR := by rw [hℓT]; group
  · calc ℓ * jR e * p * (ℓ * jR e)⁻¹ = ℓ * (jR e * p * (jR e)⁻¹) * ℓ⁻¹ := by group
      _ = p := hℓp

include ψ hψc hψt he in
theorem swap_triple {x₁ x₂ x₃ : R} (h₁ : x₁ ∈ D24) (h₂ : x₂ ∈ LocalClass D24 x₁)
    (h₃ : x₃ ∈ LocalClass D24 x₁ ∩ LocalClass D24 x₂) :
    ∃ s ∈ JR, s * x₁ * s⁻¹ = x₂ ∧ s * x₂ * s⁻¹ = x₁ ∧ s * x₃ * s⁻¹ = x₃ := by
  obtain ⟨g, hg1, hg2⟩ := exists_conj_pair h₁ h₂
  have hp : jR g * x₃ * (jR g)⁻¹ ∈ W := by
    refine ⟨?_, ?_⟩
    · rw [← hg1]; exact (Pair.conj_mem_localClass_iff pair_R (jR g)).2 h₃.1
    · rw [← hg2]; exact (Pair.conj_mem_localClass_iff pair_R (jR g)).2 h₃.2
  obtain ⟨s, hs, hs1, hs2, hs3⟩ := swap_base ψ hψc hψt he hp
  refine ⟨(jR g)⁻¹ * s * jR g, JR.mul_mem (JR.mul_mem (JR.inv_mem (jR_mem_JR g)) hs)
    (jR_mem_JR g), ?_, ?_, ?_⟩
  · calc (jR g)⁻¹ * s * jR g * x₁ * ((jR g)⁻¹ * s * jR g)⁻¹
        = (jR g)⁻¹ * (s * (jR g * x₁ * (jR g)⁻¹) * s⁻¹) * jR g := by group
      _ = x₂ := by rw [hg1, hs1, ← hg2]; group
  · calc (jR g)⁻¹ * s * jR g * x₂ * ((jR g)⁻¹ * s * jR g)⁻¹
        = (jR g)⁻¹ * (s * (jR g * x₂ * (jR g)⁻¹) * s⁻¹) * jR g := by group
      _ = x₁ := by rw [hg2, hs2, ← hg1]; group
  · calc (jR g)⁻¹ * s * jR g * x₃ * ((jR g)⁻¹ * s * jR g)⁻¹
        = (jR g)⁻¹ * (s * (jR g * x₃ * (jR g)⁻¹) * s⁻¹) * jR g := by group
      _ = x₃ := by rw [hs3]; group

end Edge

end CFSG.EvenSporadicStandard.Solomon78.Fi24Row
