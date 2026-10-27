module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi24RowEdge

public section

namespace CFSG.EvenSporadicStandard.Solomon78.Fi24Row

open CFSG.Sporadic CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Sporadic.Fi24

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Edge


local notation "W" => (LocalClass D24 tR ∩ LocalClass D24 xb)

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

include ψ hψc hψt in
theorem rhoE_tR_mul {p : R} (hp : p ∈ W) (hTp : tR * p ∈ CE) :
    ((ρE ψ hψc hψt ⟨tR * p, (Subgroup.mem_inf.1 hTp).1⟩ : tauGroup Fi22.pair_D) :
      Equiv.Perm Fi22.D) = Pair.conjPerm Fi22.pair_D (ψ ⟨p, hp⟩ : Fi22.J) := by
  refine Equiv.ext fun x => ?_
  obtain ⟨w, rfl⟩ := ψ.surjective x
  have h1 := edgeHom_apply pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
    hψt Fi22.center_eq_bot ⟨tR * p, (Subgroup.mem_inf.1 hTp).1⟩ w
  obtain ⟨hw', hw''⟩ := hψt ⟨p, hp⟩ w
  have e1 : ((edgeHomW pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
      Fi22.center_eq_bot ⟨tR * p, (Subgroup.mem_inf.1 hTp).1⟩ w : ↥W) : R) = p * w * p := by
    rw [edgeHomW_val]
    have hwT : (w : R) * tR = tR * w := w.2.1.2.2
    have hpT : p * tR = tR * p := hp.1.2.2
    show tR * p * w * (tR * p)⁻¹ = p * w * p
    have hc : tR * (p * w * p) = (p * w * p) * tR := by
      calc tR * (p * w * p) = (tR * p) * w * p := by group
        _ = (p * tR) * w * p := by rw [hpT]
        _ = p * (tR * w) * p := by group
        _ = p * (w * tR) * p := by rw [hwT]
        _ = p * w * (tR * p) := by group
        _ = p * w * (p * tR) := by rw [hpT]
        _ = p * w * p * tR := by group
    calc tR * p * w * (tR * p)⁻¹ = tR * (p * w * p⁻¹) * tR⁻¹ := by group
      _ = tR * (p * w * p) * tR := by rw [Pair.inv_eq pair_R hp.1.1, tR_inv]
      _ = (p * w * p) * tR * tR := by rw [hc]
      _ = p * w * p := by rw [mul_assoc _ tR tR, tR_mul_tR, mul_one]
  have e2 : edgeHomW pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
      Fi22.center_eq_bot ⟨tR * p, (Subgroup.mem_inf.1 hTp).1⟩ w = ⟨p * w * p, hw'⟩ :=
    Subtype.ext e1
  apply Subtype.ext
  rw [Pair.conjPerm_apply, Pair.inv_eq Fi22.pair_D (ψ ⟨p, hp⟩).2]
  have h3 := congrArg Subtype.val h1
  rw [e2] at h3
  exact h3.trans hw''

include ψ hψc hψt hfix22 hcent22 he in
theorem edge_Y {p : R} (hp : p ∈ W) {y : R} (hy : y ∈ CE)
    (hcomm : ∀ ℓ ∈ Fi24.LE, ℓ * p * ℓ⁻¹ = p → y * ℓ = ℓ * y) :
    y = 1 ∨ y = tR * xb ∨ y = tR * p ∨ y = p * xb := by
  have hy1 : y ∈ Subgroup.centralizer ({tR * xb} : Set R) := (Subgroup.mem_inf.1 hy).1
  have hrangeL := range_edgeHomL pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ
    hψc hψt Fi22.center_eq_bot Fi22.index_innerTau_range (inf_le_left : CE ≤ _) commutator_LE
    (by rw [Fi22.card_tauGroup]; exact card_LE) (fun ℓ hℓ h => eq_of_mem_LE_centralizes hℓ h)
  have hsurj := edge_surj ψ hψc hψt hfix22 he
  have hker := edgeHomC_ker pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
    hψt Fi22.center_eq_bot (inf_le_left : CE ≤ _) hsurj (card_CE he (edge_hW ψ hψc))
    tR_mul_xb_mem_CE
  set χ := ψ ⟨p, hp⟩
  have hσ : ∀ g : Fi22.J, g * χ = χ * g →
      ((ρE ψ hψc hψt ⟨y, hy1⟩ : tauGroup Fi22.pair_D) : Equiv.Perm Fi22.D) *
          Pair.conjPerm Fi22.pair_D g =
        Pair.conjPerm Fi22.pair_D g * ((ρE ψ hψc hψt ⟨y, hy1⟩ : tauGroup Fi22.pair_D) :
          Equiv.Perm Fi22.D) := by
    intro g hg
    have hmem : innerTau Fi22.pair_D g ∈ (innerTau Fi22.pair_D).range := ⟨g, rfl⟩
    rw [← hrangeL] at hmem
    obtain ⟨ℓ, hℓ⟩ := hmem
    have hfix : (ℓ : R) * p * (ℓ : R)⁻¹ = p := by
      have h1 := edgeHom_apply pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
        hψt Fi22.center_eq_bot (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) ⟨p, hp⟩
      have h2 : ((ρE ψ hψc hψt (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) :
          tauGroup Fi22.pair_D) : Equiv.Perm Fi22.D) χ = χ := by
        have h0 : ρE ψ hψc hψt (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) =
            innerTau Fi22.pair_D g := hℓ
        rw [h0]
        apply Subtype.ext
        show g * (χ : Fi22.J) * g⁻¹ = χ
        rw [hg, mul_inv_cancel_right]
      have h3 := ψ.injective (h1.symm.trans h2)
      have h4 := congrArg Subtype.val h3
      rw [edgeHomW_val] at h4
      exact h4
    have hyℓ := hcomm ℓ ℓ.2 hfix
    have : ρE ψ hψc hψt ⟨y, hy1⟩ *
        ρE ψ hψc hψt (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) =
        ρE ψ hψc hψt (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) *
          ρE ψ hψc hψt ⟨y, hy1⟩ := by
      rw [← map_mul, ← map_mul]
      refine congrArg (ρE ψ hψc hψt) (Subtype.ext ?_)
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hyℓ
    have h' := Subtype.ext_iff.1 this
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
    have hℓ' : ((ρE ψ hψc hψt (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) :
        tauGroup Fi22.pair_D) : Equiv.Perm Fi22.D) = Pair.conjPerm Fi22.pair_D g := by
      have h0 := Subtype.ext_iff.1 hℓ
      exact h0
    rw [hℓ'] at h'
    exact h'
  have hTp : tR * p ∈ CE := (Subgroup.mem_inf.1 (tR_mul_mem_LE hp)).1
  rcases hcent22 χ _ hσ with h | h
  · have h1 := hker ⟨y, hy⟩ (Subtype.ext h)
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have hρ := rhoE_tR_mul ψ hψc hψt hp hTp
    have h2 : ρE ψ hψc hψt ⟨y, hy1⟩ = ρE ψ hψc hψt ⟨tR * p, (Subgroup.mem_inf.1 hTp).1⟩ :=
      Subtype.ext (h.trans hρ.symm)
    have h3 := hker (⟨tR * p, hTp⟩⁻¹ * ⟨y, hy⟩) (by
      let a : ↥(Subgroup.centralizer ({tR * xb} : Set R)) := ⟨tR * p, (Subgroup.mem_inf.1 hTp).1⟩
      let b : ↥(Subgroup.centralizer ({tR * xb} : Set R)) := ⟨y, hy1⟩
      have e : Subgroup.inclusion (inf_le_left : CE ≤ _) (⟨tR * p, hTp⟩⁻¹ * ⟨y, hy⟩) = a⁻¹ * b :=
        rfl
      show ρE ψ hψc hψt (Subgroup.inclusion (inf_le_left : CE ≤ _) (⟨tR * p, hTp⟩⁻¹ * ⟨y, hy⟩)) = 1
      rw [e]
      exact ((map_mul (ρE ψ hψc hψt) a⁻¹ b).trans (congrArg (· * ρE ψ hψc hψt b)
        (map_inv (ρE ψ hψc hψt) a))).trans (by rw [h2]; exact inv_mul_cancel _))
    have hTp_inv : (tR * p)⁻¹ = p * tR := by
      rw [mul_inv_rev, tR_inv, Pair.inv_eq pair_R hp.1.1]
    have hpT : p * tR = tR * p := hp.1.2.2
    rcases h3 with h3 | h3
    · right; right; left
      have h3' : (tR * p)⁻¹ * y = 1 := h3
      calc y = (tR * p) * ((tR * p)⁻¹ * y) := by group
        _ = tR * p := by rw [h3', mul_one]
    · right; right; right
      have h3' : (tR * p)⁻¹ * y = tR * xb := h3
      calc y = (tR * p) * ((tR * p)⁻¹ * y) := by group
        _ = (tR * p) * (tR * xb) := by rw [h3']
        _ = p * xb := by
          calc (tR * p) * (tR * xb) = (p * tR) * (tR * xb) := by rw [hpT]
            _ = p * (tR * tR) * xb := by group
            _ = p * xb := by rw [tR_mul_tR, mul_one]

include ψ hψc hψt hfix22 hcent22 he in
theorem edge_houter {p : R} (hp : p ∈ W) {z : R} (hzJ : z ∈ JR) (hz1 : z ≠ 1)
    (hzp : z * p = p * z) (hzw : z * (tR * xb * p) = (tR * xb * p) * z)
    (hcent : ∀ y ∈ JR, y * (tR * xb * p) = (tR * xb * p) * y → y * z = z * y) : False := by
  have hpT : p * tR = tR * p := hp.1.2.2
  have hpx : p * xb = xb * p := hp.2.2.2
  have hpne : p ≠ tR := hp.1.2.1
  have hpxne : p ≠ xb := hp.2.2.1
  have hzab : z * (tR * xb) = (tR * xb) * z := by
    have h1 : z * (tR * xb) * p = (tR * xb) * z * p := by
      calc z * (tR * xb) * p = z * (tR * xb * p) := by group
        _ = (tR * xb * p) * z := hzw
        _ = (tR * xb) * (p * z) := by group
        _ = (tR * xb) * (z * p) := by rw [hzp]
        _ = (tR * xb) * z * p := by group
    exact mul_right_cancel h1
  have hzCE : z ∈ CE := mem_CE_iff.2 ⟨hzab, hzJ⟩
  have hY := edge_Y ψ hψc hψt hfix22 hcent22 he hp hzCE (fun ℓ hℓ hfix => by
    obtain ⟨⟨hℓa, hℓJ⟩, hℓT⟩ := mem_LE_iff.1 hℓ
    have hℓp : ℓ * p = p * ℓ := by
      calc ℓ * p = ℓ * p * ℓ⁻¹ * ℓ := by group
        _ = p * ℓ := by rw [hfix]
    have hℓw : ℓ * (tR * xb * p) = (tR * xb * p) * ℓ := by
      calc ℓ * (tR * xb * p) = ℓ * (tR * xb) * p := by group
        _ = (tR * xb) * ℓ * p := by rw [hℓa]
        _ = (tR * xb) * (ℓ * p) := by group
        _ = (tR * xb) * (p * ℓ) := by rw [hℓp]
        _ = (tR * xb * p) * ℓ := by group
    exact (hcent ℓ hℓJ hℓw).symm)
  have hxbmem : xb ∈ LocalClass D24 tR ∩ LocalClass D24 p :=
    ⟨xb_mem_localClass, xb_mem_D24, hpxne.symm, hpx.symm⟩
  have hpmem : p ∈ LocalClass D24 tR ∩ LocalClass D24 xb := hp
  obtain ⟨s₁, hs₁J, hs₁1, hs₁2, hs₁3⟩ := swap_triple ψ hψc hψt he tR_mem_D24 hp.1 hxbmem
  obtain ⟨s₂, hs₂J, hs₂1, hs₂2, hs₂3⟩ := swap_triple ψ hψc hψt he tR_mem_D24 xb_mem_localClass hpmem
  have hw₁ : s₁ * (tR * xb * p) = (tR * xb * p) * s₁ := by
    have : s₁ * (tR * xb * p) * s₁⁻¹ = tR * xb * p := by
      calc s₁ * (tR * xb * p) * s₁⁻¹ = (s₁ * tR * s₁⁻¹) * (s₁ * xb * s₁⁻¹) * (s₁ * p * s₁⁻¹) := by
            group
        _ = p * xb * tR := by rw [hs₁1, hs₁3, hs₁2]
        _ = tR * xb * p := by
          calc p * xb * tR = xb * p * tR := by rw [hpx]
            _ = xb * (p * tR) := by group
            _ = xb * (tR * p) := by rw [hpT]
            _ = (xb * tR) * p := by group
            _ = (tR * xb) * p := by rw [tR_xb_comm]
    calc s₁ * (tR * xb * p) = s₁ * (tR * xb * p) * s₁⁻¹ * s₁ := by group
      _ = (tR * xb * p) * s₁ := by rw [this]
  have hw₂ : s₂ * (tR * xb * p) = (tR * xb * p) * s₂ := by
    have : s₂ * (tR * xb * p) * s₂⁻¹ = tR * xb * p := by
      calc s₂ * (tR * xb * p) * s₂⁻¹ = (s₂ * tR * s₂⁻¹) * (s₂ * xb * s₂⁻¹) * (s₂ * p * s₂⁻¹) := by
            group
        _ = xb * tR * p := by rw [hs₂1, hs₂3, hs₂2]
        _ = tR * xb * p := by rw [tR_xb_comm]
    calc s₂ * (tR * xb * p) = s₂ * (tR * xb * p) * s₂⁻¹ * s₂ := by group
      _ = (tR * xb * p) * s₂ := by rw [this]
  rcases hY with h | h | h | h
  · exact hz1 h
  ·
    have hc := hcent s₁ hs₁J hw₁
    rw [h] at hc
    have : s₁ * (tR * xb) * s₁⁻¹ = tR * xb := by
      calc s₁ * (tR * xb) * s₁⁻¹ = tR * xb * s₁ * s₁⁻¹ := by rw [← hc]
        _ = tR * xb := by group
    have h2 : s₁ * (tR * xb) * s₁⁻¹ = p * xb := by
      calc s₁ * (tR * xb) * s₁⁻¹ = (s₁ * tR * s₁⁻¹) * (s₁ * xb * s₁⁻¹) := by group
        _ = p * xb := by rw [hs₁1, hs₁3]
    exact hpne (mul_right_cancel (h2.symm.trans this))
  ·
    have hc := hcent s₂ hs₂J hw₂
    rw [h] at hc
    have : s₂ * (tR * p) * s₂⁻¹ = tR * p := by
      calc s₂ * (tR * p) * s₂⁻¹ = tR * p * s₂ * s₂⁻¹ := by rw [← hc]
        _ = tR * p := by group
    have h2 : s₂ * (tR * p) * s₂⁻¹ = xb * p := by
      calc s₂ * (tR * p) * s₂⁻¹ = (s₂ * tR * s₂⁻¹) * (s₂ * p * s₂⁻¹) := by group
        _ = xb * p := by rw [hs₂1, hs₂3]
    exact tR_ne_xb (mul_right_cancel (this.symm.trans h2))
  ·
    have hc := hcent s₁ hs₁J hw₁
    rw [h] at hc
    have : s₁ * (p * xb) * s₁⁻¹ = p * xb := by
      calc s₁ * (p * xb) * s₁⁻¹ = p * xb * s₁ * s₁⁻¹ := by rw [← hc]
        _ = p * xb := by group
    have h2 : s₁ * (p * xb) * s₁⁻¹ = tR * xb := by
      calc s₁ * (p * xb) * s₁⁻¹ = (s₁ * p * s₁⁻¹) * (s₁ * xb * s₁⁻¹) := by group
        _ = tR * xb := by rw [hs₁2, hs₁3]
    exact hpne (mul_right_cancel (this.symm.trans h2))

end Edge

section Wrappers

variable (hPF : PolarFacts)
  (hfix22 : ∀ g : Fi22.J, g ^ 2 = 1 → g ≠ 1 →
    Nat.card {x : Fi22.D // g * (x : Fi22.J) * g⁻¹ = x} ∈ ({54, 182, 694} : Set ℕ))
  (hcent22 : ∀ (χ : Fi22.D) (σ : Equiv.Perm Fi22.D),
    (∀ g : Fi22.J, g * χ = χ * g →
      σ * Pair.conjPerm Fi22.pair_D g = Pair.conjPerm Fi22.pair_D g * σ) →
    σ = 1 ∨ σ = Pair.conjPerm Fi22.pair_D (χ : Fi22.J))
  {e : J} (he : EdgeSwap e)

include hPF hfix22 he in
theorem fi24_ci_tJ {z : R} (hzJ : z ∈ JR) (hza : z * (tR * xb) = tR * xb * z)
    (hc : ∀ y ∈ JR, y * (tR * xb) = tR * xb * y → z * y = y * z) : z = 1 ∨ z = tR * xb := by
  obtain ⟨ψ, hψc, hψt⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 hPF) ⟨tR, tR_mem_D24⟩ ⟨xb, xb_mem_D24⟩ tR_ne_xb
    tR_xb_comm
  exact edge_center ψ hψc hψt hfix22 he (mem_CE_iff.2 ⟨hza, hzJ⟩) fun c hc' =>
    hc c (mem_CE_iff.1 hc').2 (mem_CE_iff.1 hc').1

include hPF hfix22 he in
theorem fi24_ol_tJ {w : R} (hwJ : w ∉ JR) :
    ¬ ∀ y ∈ JR, y * (tR * xb) = tR * xb * y → y * w = w * y := by
  intro h
  obtain ⟨ψ, hψc, hψt⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 hPF) ⟨tR, tR_mem_D24⟩ ⟨xb, xb_mem_D24⟩ tR_ne_xb
    tR_xb_comm
  exact edge_no_outer ψ hψc hψt hfix22 he hwJ fun c hc' =>
    h c (mem_CE_iff.1 hc').2 (mem_CE_iff.1 hc').1

include hPF hfix22 hcent22 he in
theorem fi24_ho_edge {p : R} (hp : p ∈ LocalClass D24 tR ∩ LocalClass D24 xb) {z : R}
    (hzJ : z ∈ JR) (hz1 : z ≠ 1) (hzp : z * p = p * z)
    (hzw : z * (tR * xb * p) = (tR * xb * p) * z)
    (hcent : ∀ y ∈ JR, y * (tR * xb * p) = (tR * xb * p) * y → y * z = z * y) : False := by
  obtain ⟨ψ, hψc, hψt⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 hPF) ⟨tR, tR_mem_D24⟩ ⟨xb, xb_mem_D24⟩ tR_ne_xb
    tR_xb_comm
  exact edge_houter ψ hψc hψt hfix22 hcent22 he hp hzJ hz1 hzp hzw hcent

end Wrappers

end CFSG.EvenSporadicStandard.Solomon78.Fi24Row
