module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Block

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem IsA4Block.mem_of_centralizes [Finite G] {L U : Subgroup G} (h : IsA4Block L U) {l : G}
    (hl : l ∈ L) (hc : ∀ u ∈ U, l * u = u * l) : l ∈ U := by
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  obtain ⟨u₀, hu₀U, hu₀1⟩ : ∃ u₀ ∈ U, u₀ ≠ 1 := by
    by_contra hcon
    have hle : U ≤ ⊥ := fun u hu => by
      rw [Subgroup.mem_bot]
      by_contra h'
      exact hcon ⟨u, hu, h'⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [h.card_U, Subgroup.card_bot] at h1
    omega
  have hlmem : l ∈ ((zpowers c ⊔ U : Subgroup G) : Set G) := by
    have : l ∈ zpowers c ⊔ U := by rw [sup_comm, ← hLc]; exact hl
    exact this
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (zpowers c) U (zpowers_le.mpr hcN)] at hlmem
  obtain ⟨y, hy, u', hu', hyu0⟩ := hlmem
  have hyu : y * u' = l := hyu0
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hck : ∀ u ∈ U, c ^ k * u = u * c ^ k := by
    intro u hu
    have h1 := hc u hu
    have h2 : u'⁻¹ * u = u * u'⁻¹ := h.comm_U u'⁻¹ (inv_mem hu') u hu
    calc c ^ k * u = (c ^ k * u') * (u'⁻¹ * u) := by group
      _ = l * (u * u'⁻¹) := by rw [hyu, h2]
      _ = (l * u) * u'⁻¹ := by group
      _ = (u * l) * u'⁻¹ := by rw [h1]
      _ = u * (c ^ k * u' * u'⁻¹) := by rw [← hyu]; group
      _ = u * c ^ k := by group
  have hk : c ^ k = c ^ (k % 3) := by
    have := zpow_mod_orderOf c k
    rw [hc3] at this
    simpa using this.symm
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h0 | h0
  · have : c ^ k = 1 := by rw [hk, h0, zpow_zero]
    rw [← hyu, this, one_mul]
    exact hu'
  · exfalso
    have hcc : c * u₀ = u₀ * c := by
      have := hck u₀ hu₀U
      rwa [hk, h0, zpow_one] at this
    apply hcfp u₀ hu₀U hu₀1
    calc c * u₀ * c⁻¹ = u₀ * c * c⁻¹ := by rw [hcc]
      _ = u₀ := by group
  · exfalso
    have hcc2 : c ^ 2 * u₀ = u₀ * c ^ 2 := by
      have := hck u₀ hu₀U
      rw [hk, h0] at this
      simpa [zpow_two, pow_two] using this
    have hc4 : c = c ^ 2 * c ^ 2 := by
      calc c = c * c ^ 3 := by rw [hc3', mul_one]
        _ = c ^ 2 * c ^ 2 := by group
    apply hcfp u₀ hu₀U hu₀1
    have hcc : c * u₀ = u₀ * c := by
      calc c * u₀ = (c ^ 2 * c ^ 2) * u₀ := by rw [← hc4]
        _ = c ^ 2 * (c ^ 2 * u₀) := by group
        _ = c ^ 2 * (u₀ * c ^ 2) := by rw [hcc2]
        _ = (c ^ 2 * u₀) * c ^ 2 := by group
        _ = (u₀ * c ^ 2) * c ^ 2 := by rw [hcc2]
        _ = u₀ * (c ^ 2 * c ^ 2) := by group
        _ = u₀ * c := by rw [← hc4]
    calc c * u₀ * c⁻¹ = u₀ * c * c⁻¹ := by rw [hcc]
      _ = u₀ := by group

theorem IsA4Block.eq_or_eq_of_le_sup [Finite G] {L U U₂ X : Subgroup G} (h : IsA4Block L U)
    (hUU₂ : ∀ u ∈ U, ∀ v ∈ U₂, u * v = v * u) (hL₂ : ∀ l ∈ L, ∀ v ∈ U₂, l * v = v * l)
    (hX : X ≤ U ⊔ U₂) (hX4 : Nat.card X = 4) (hU₂4 : Nat.card U₂ = 4)
    (hLX : L ≤ normalizer (X : Set G)) : X = U ∨ X = U₂ := by
  have hUN : U ≤ normalizer (U₂ : Set G) := C5.le_normalizer_of_commute hUU₂
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  have hLUN : L ≤ normalizer (U : Set G) := by
    rw [hLc]; exact sup_le Subgroup.le_normalizer (zpowers_le.mpr hcN)
  by_cases hex : ∃ x ∈ X, ∃ u ∈ U, ∃ v ∈ U₂, u * v = x ∧ u ≠ 1
  · left
    obtain ⟨x, hxX, u, hu, v, hv, hxuv, hu1⟩ := hex
    have hcX : c * x * c⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hLX hcL) x).mp hxX
    have hcv : c * v = v * c := hL₂ c hcL v hv
    have hvc : v * c⁻¹ = c⁻¹ * v := by
      calc v * c⁻¹ = c⁻¹ * (c * v) * c⁻¹ := by group
        _ = c⁻¹ * (v * c) * c⁻¹ := by rw [hcv]
        _ = c⁻¹ * v := by group
    have hcu : c * u * c⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hcN u).mp hu
    obtain ⟨w, hw⟩ : ∃ w, w = u⁻¹ * (c * u * c⁻¹) := ⟨_, rfl⟩
    have hwU : w ∈ U := by rw [hw]; exact mul_mem (inv_mem hu) hcu
    have hwv : w * v = v * w := hUU₂ w hwU v hv
    have hxw : x⁻¹ * (c * x * c⁻¹) = w := by
      rw [← hxuv]
      calc (u * v)⁻¹ * (c * (u * v) * c⁻¹) = v⁻¹ * (u⁻¹ * (c * u * (v * c⁻¹))) := by group
        _ = v⁻¹ * (u⁻¹ * (c * u * (c⁻¹ * v))) := by rw [hvc]
        _ = v⁻¹ * (w * v) := by rw [hw]; group
        _ = v⁻¹ * (v * w) := by rw [hwv]
        _ = w := by group
    have hwX : w ∈ X := by rw [← hxw]; exact mul_mem (inv_mem hxX) hcX
    have hw1 : w ≠ 1 := by
      intro h1
      apply hcfp u hu hu1
      calc c * u * c⁻¹ = u * (u⁻¹ * (c * u * c⁻¹)) := by group
        _ = u := by rw [← hw, h1]; group
    have hLN : L ≤ normalizer ((X ⊓ U : Subgroup G) : Set G) := fun g hg =>
      C5.mem_normalizer_inf (hLX hg) (hLUN hg)
    have hUle : U ≤ X ⊓ U := h.le_of_mem hLN ⟨hwX, hwU⟩ hwU hw1
    exact (Subgroup.eq_of_le_of_card_ge (le_trans hUle inf_le_left)
      (by rw [hX4, h.card_U])).symm
  · right
    have hle : X ≤ U₂ := by
      intro x hx
      have hx' : x ∈ ((U ⊔ U₂ : Subgroup G) : Set G) := hX hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right U U₂ hUN] at hx'
      obtain ⟨u, hu, v, hv, huv0⟩ := hx'
      have huv : u * v = x := huv0
      have hu1 : u = 1 := by
        by_contra h1
        exact hex ⟨x, hx, u, hu, v, hv, huv, h1⟩
      rw [← huv, hu1, one_mul]
      exact hv
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hX4, hU₂4])

theorem IsA4Block.eq_of_le_sup [Finite G] {L U L₂ U₂ M : Subgroup G} (hL : IsA4Block L U)
    (hL₂ : IsA4Block L₂ U₂) (hM : IsA4Block M U)
    (hcomm : ∀ a ∈ L, ∀ b ∈ L₂, a * b = b * a) (hinf : L ⊓ L₂ = ⊥)
    (hMle : M ≤ L ⊔ L₂) (hMN : L₂ ≤ normalizer (M : Set G)) : M = L := by
  obtain ⟨c', hc'M, hc'3, hc'N, hc'fp, hMc⟩ := hM.exists_c
  have hc'mem : c' ∈ ((L ⊔ L₂ : Subgroup G) : Set G) := hMle hc'M
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L L₂
    (C5.le_normalizer_of_commute hcomm)] at hc'mem
  obtain ⟨a, ha, b, hb, hab0⟩ := hc'mem
  have hab : a * b = c' := hab0
  have hb1 : b = 1 := by
    refine hL₂.center_L b hb fun l' hl' => ?_
    obtain ⟨κ, hκ⟩ : ∃ κ, κ = l' * b * l'⁻¹ * b⁻¹ := ⟨_, rfl⟩
    have hal : a * l' = l' * a := hcomm a ha l' hl'
    have hκL₂ : κ ∈ L₂ := by
      rw [hκ]
      exact mul_mem (mul_mem (mul_mem hl' hb) (inv_mem hl')) (inv_mem hb)
    have haκ : a * κ = κ * a := hcomm a ha κ hκL₂
    have hκM : κ ∈ M := by
      have h1 : l' * c' * l'⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hMN hl') c').mp hc'M
      have h2 : l' * c' * l'⁻¹ * c'⁻¹ ∈ M := mul_mem h1 (inv_mem hc'M)
      have e : l' * c' * l'⁻¹ * c'⁻¹ = κ := by
        rw [← hab]
        calc l' * (a * b) * l'⁻¹ * (a * b)⁻¹ = (l' * a) * b * l'⁻¹ * b⁻¹ * a⁻¹ := by group
          _ = (a * l') * b * l'⁻¹ * b⁻¹ * a⁻¹ := by rw [hal]
          _ = a * κ * a⁻¹ := by rw [hκ]; group
          _ = κ := by rw [haκ]; group
      rw [← e]; exact h2
    have hκU : κ ∈ U :=
      hM.mem_of_centralizes hκM fun u hu => (hcomm u (hL.le hu) κ hκL₂).symm
    have hκ1 : κ = 1 := by
      have : κ ∈ L ⊓ L₂ := ⟨hL.le hκU, hκL₂⟩
      rw [hinf] at this
      exact this
    calc b * l' = (l' * b * l'⁻¹ * b⁻¹)⁻¹ * (l' * b) := by group
      _ = l' * b := by rw [← hκ, hκ1]; group
  have hc'a : c' = a := by rw [← hab, hb1, mul_one]
  have hle : M ≤ L := by
    rw [hMc]
    exact sup_le hL.le ((Subgroup.zpowers_le).mpr (hc'a ▸ ha))
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hM.card_L, hL.card_L])

theorem IsA4Block.exists_inner [Finite G] {L U : Subgroup G} (h : IsA4Block L U) {g : G}
    (hgL : g ∈ normalizer (L : Set G)) (hgU : ∀ u ∈ U, g * u = u * g) :
    ∃ u ∈ U, ∀ l ∈ L, g * l * g⁻¹ = u * l * u⁻¹ := by
  classical
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hgc : g * c * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hgL c).mp hcL
  have hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hcN u).mp hu
  have hcinv : ∀ u ∈ U, c⁻¹ * u * c ∈ U := fun u hu => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hcN) u).mp hu
    simpa using this
  obtain ⟨u₁, hu₁U, hu₁⟩ : ∃ u₁ ∈ U, g * c * g⁻¹ = c * u₁ := by
    refine ⟨c⁻¹ * (g * c * g⁻¹), ?_, by group⟩
    refine h.mem_of_centralizes (mul_mem (inv_mem hcL) hgc) fun u hu => ?_
    have hgu : g⁻¹ * u * g = u := by
      calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
        _ = g⁻¹ * (g * u) := by rw [hgU u hu]
        _ = u := by group
    have hgcu : g * (c * u * c⁻¹) * g⁻¹ = c * u * c⁻¹ := by
      calc g * (c * u * c⁻¹) * g⁻¹ = (c * u * c⁻¹) * g * g⁻¹ := by rw [hgU _ (hcU u hu)]
        _ = c * u * c⁻¹ := by group
    have e1 : (g * c * g⁻¹) * u = (c * u * c⁻¹) * (g * c * g⁻¹) := by
      calc (g * c * g⁻¹) * u = g * c * (g⁻¹ * u * g) * g⁻¹ := by group
        _ = g * (c * u * c⁻¹) * c * g⁻¹ := by rw [hgu]; group
        _ = (g * (c * u * c⁻¹) * g⁻¹) * (g * c * g⁻¹) := by group
        _ = (c * u * c⁻¹) * (g * c * g⁻¹) := by rw [hgcu]
    calc c⁻¹ * (g * c * g⁻¹) * u = c⁻¹ * ((g * c * g⁻¹) * u) := by group
      _ = c⁻¹ * ((c * u * c⁻¹) * (g * c * g⁻¹)) := by rw [e1]
      _ = u * (c⁻¹ * (g * c * g⁻¹)) := by group
  let φ : U → U := fun u => ⟨c⁻¹ * (u : G) * c * (u : G)⁻¹, mul_mem (hcinv _ u.2) (inv_mem u.2)⟩
  have hfp' : ∀ w ∈ U, w ≠ 1 → c⁻¹ * w * c ≠ w := by
    intro w hw hw1 hcw
    apply hcfp w hw hw1
    calc c * w * c⁻¹ = c * (c⁻¹ * w * c) * c⁻¹ := by rw [hcw]
      _ = w := by group
  have hφinj : Function.Injective φ := by
    intro u v huv
    have h1 : c⁻¹ * (u : G) * c * (u : G)⁻¹ = c⁻¹ * (v : G) * c * (v : G)⁻¹ :=
      congrArg Subtype.val huv
    have ha : c⁻¹ * (u : G) * c ∈ U := hcinv _ u.2
    have ha' : c⁻¹ * (v : G) * c ∈ U := hcinv _ v.2
    have h2 : c⁻¹ * ((u : G) * (v : G)⁻¹) * c = (u : G) * (v : G)⁻¹ := by
      have e0 : c⁻¹ * (u : G) * c = (c⁻¹ * (v : G) * c) * ((v : G)⁻¹ * (u : G)) := by
        calc c⁻¹ * (u : G) * c = (c⁻¹ * (u : G) * c * (u : G)⁻¹) * (u : G) := by group
          _ = (c⁻¹ * (v : G) * c * (v : G)⁻¹) * (u : G) := by rw [h1]
          _ = (c⁻¹ * (v : G) * c) * ((v : G)⁻¹ * (u : G)) := by group
      have e1 : c⁻¹ * ((u : G) * (v : G)⁻¹) * c =
          (c⁻¹ * (u : G) * c) * (c⁻¹ * (v : G) * c)⁻¹ := by group
      rw [e1, e0]
      have hc1 : (c⁻¹ * (v : G) * c) * ((v : G)⁻¹ * (u : G)) =
          ((v : G)⁻¹ * (u : G)) * (c⁻¹ * (v : G) * c) :=
        h.comm_U _ ha' _ (mul_mem (inv_mem v.2) u.2)
      rw [hc1]
      calc (v : G)⁻¹ * (u : G) * (c⁻¹ * (v : G) * c) * (c⁻¹ * (v : G) * c)⁻¹ = (v : G)⁻¹ * (u : G) := by
            group
        _ = (u : G) * (v : G)⁻¹ := h.comm_U _ (inv_mem v.2) _ u.2
    by_contra hne
    have hw1 : (u : G) * (v : G)⁻¹ ≠ 1 := by
      intro h3
      apply hne
      apply Subtype.ext
      exact mul_inv_eq_one.mp h3
    exact hfp' _ (mul_mem u.2 (inv_mem v.2)) hw1 h2
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hφinj) ⟨u₁, hu₁U⟩
  have hu' : c⁻¹ * (u : G) * c * (u : G)⁻¹ = u₁ := congrArg Subtype.val hu
  refine ⟨u, u.2, fun l hl => ?_⟩
  have hLE : L ≤ MonoidHom.eqLocus (MulAut.conj g).toMonoidHom (MulAut.conj (u : G)).toMonoidHom := by
    rw [hLc]
    refine sup_le (fun v hv => ?_) ((Subgroup.zpowers_le).mpr ?_)
    · show g * v * g⁻¹ = (u : G) * v * (u : G)⁻¹
      rw [show g * v * g⁻¹ = v by rw [hgU v hv]; group, h.comm_U (u : G) u.2 v hv]
      group
    · show g * c * g⁻¹ = (u : G) * c * (u : G)⁻¹
      rw [hu₁, ← hu']
      group
  exact hLE hl

end CFSG.QuasithinUnique.DoubleA3
