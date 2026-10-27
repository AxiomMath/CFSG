module

public import CFSG.LocalAnalysis.QuasithinUnique.ONanLemma
public import Mathlib

public section

namespace CFSG.Goldschmidt.G2

open Module CFSG.QuasithinUnique
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

section Basic

@[expose] def fixSp (η : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V :=
  LinearMap.ker ((η : V →ₗ[ZMod 2] V) - LinearMap.id)

@[expose] def comSp (η : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V :=
  LinearMap.range ((η : V →ₗ[ZMod 2] V) - LinearMap.id)

theorem mem_fixSp {η : V ≃ₗ[ZMod 2] V} {v : V} : v ∈ fixSp η ↔ η v = v := by
  simp [fixSp, sub_eq_zero]

theorem mem_comSp {η : V ≃ₗ[ZMod 2] V} {v : V} : v ∈ comSp η ↔ ∃ u, η u - u = v := by
  simp [comSp]

theorem add_self (v : V) : v + v = 0 := (ONan.add_eq_zero_iff_eq v v).mpr rfl

theorem neg_eq (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, add_self]

theorem sub_eq_add (u v : V) : u - v = u + v := by
  rw [sub_eq_add_neg, neg_eq]

theorem odd_nsmul {n : ℕ} (hn : Odd n) (v : V) : n • v = v := by
  obtain ⟨t, rfl⟩ := hn
  rw [add_nsmul, mul_comm, mul_nsmul, two_nsmul, add_self, zero_add, one_nsmul]

theorem apply_mem_comSp {η g : V ≃ₗ[ZMod 2] V} (hg : g * η = η * g) {v : V}
    (hv : v ∈ comSp η) : g v ∈ comSp η := by
  obtain ⟨u, rfl⟩ := mem_comSp.mp hv
  refine mem_comSp.mpr ⟨g u, ?_⟩
  have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f u) hg
  simp only [LinearEquiv.mul_apply] at this
  rw [map_sub, ← this]

theorem apply_mem_fixSp {η g : V ≃ₗ[ZMod 2] V} (hg : g * η = η * g) {v : V}
    (hv : v ∈ fixSp η) : g v ∈ fixSp η := by
  rw [mem_fixSp] at hv ⊢
  have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hg
  simp only [LinearEquiv.mul_apply] at this
  rw [← this, hv]

theorem mul_comm_of_mem_zpowers {η g : V ≃ₗ[ZMod 2] V} (hg : g ∈ Subgroup.zpowers η) :
    g * η = η * g := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact ((Commute.refl η).zpow_left i).eq

theorem apply_eq_of_mem_zpowers {η g : V ≃ₗ[ZMod 2] V} (hg : g ∈ Subgroup.zpowers η) {v : V}
    (hv : v ∈ fixSp η) : g v = v := by
  have hη : η ∈ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v := by
    rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]
    exact mem_fixSp.mp hv
  have := (Subgroup.zpowers_le.mpr hη) hg
  rwa [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def] at this

theorem pow_apply_eq_add_nsmul {η : V ≃ₗ[ZMod 2] V} {u v : V} (hu : η u = u + v)
    (hv : η v = v) (i : ℕ) : (η ^ i) u = u + i • v := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_nsmul, hu, hv, succ_nsmul]
    abel

theorem isCompl_comSp_fixSp [Finite V] {η : V ≃ₗ[ZMod 2] V} (hodd : Odd (orderOf η)) :
    IsCompl (comSp η) (fixSp η) := by
  rw [Submodule.isCompl_iff_disjoint]
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨u, rfl⟩ := mem_comSp.mp hv
    have hfix : η (η u - u) = η u - u := mem_fixSp.mp hv'
    have hu : η u = u + (η u - u) := by abel
    have h1 := pow_apply_eq_add_nsmul hu hfix (orderOf η)
    rw [pow_orderOf_eq_one, LinearEquiv.coe_one, id, odd_nsmul hodd] at h1
    have h2 : u + (η u - u) - u = u - u := by rw [← h1]
    simpa using h2
  · rw [comSp, fixSp, LinearMap.finrank_range_add_finrank_ker]

theorem card_nonzero_add_one [Finite V] (S : Submodule (ZMod 2) V) :
    Nat.card {v : V // v ∈ S ∧ v ≠ 0} + 1 = Nat.card S := by
  classical
  have e : {v : V // v ∈ S ∧ v ≠ 0} ≃ {x : S // x ≠ 0} :=
    { toFun := fun v => ⟨⟨v.1, v.2.1⟩, fun h0 => v.2.2 (congrArg Subtype.val h0)⟩
      invFun := fun x => ⟨x.1, x.1.2, fun h0 => x.2 (Subtype.ext h0)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, ← Nat.card_congr (Equiv.optionSubtypeNe (0 : S)), Finite.card_option]

theorem card_nonzero_smul [Finite V] (x : V ≃ₗ[ZMod 2] V) (S : Submodule (ZMod 2) V) :
    Nat.card {v : V // v ∈ x • S ∧ v ≠ 0} = Nat.card {v : V // v ∈ S ∧ v ≠ 0} := by
  have h1 := card_nonzero_add_one (x • S)
  have h2 := card_nonzero_add_one S
  have h3 : Nat.card (x • S : Submodule (ZMod 2) V) = Nat.card S := by
    rw [ONan.natCard_submodule, ONan.natCard_submodule, ONan.finrank_smul]
  omega

theorem exists_pow_eq_of_mem_zpowers [Finite V] {η g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ Subgroup.zpowers η) : ∃ k : ℕ, η ^ k = g := by
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective
  exact (mem_powers_iff_mem_zpowers.mpr hg)

end Basic

structure LinHyp (X : Subgroup (V ≃ₗ[ZMod 2] V)) (η : V ≃ₗ[ZMod 2] V) : Prop where
  mem : η ∈ X
  odd : Odd (orderOf η)
  ne_one : η ≠ 1
  fixSp_ne_bot : fixSp η ≠ ⊥
  trans : ∀ b ∈ comSp η, ∀ c ∈ comSp η, b ≠ 0 → c ≠ 0 → ∃ k : ℕ, (η ^ k) b = c
  ti : ∀ x ∈ X, x • fixSp η ≠ fixSp η → x • fixSp η ⊓ fixSp η = ⊥

namespace LinHyp

variable [Finite V] {X : Subgroup (V ≃ₗ[ZMod 2] V)} {η : V ≃ₗ[ZMod 2] V} (h : LinHyp X η)
include h

theorem isCompl : IsCompl (comSp η) (fixSp η) := isCompl_comSp_fixSp h.odd

theorem exists_add (v : V) : ∃ d ∈ comSp η, ∃ w ∈ fixSp η, d + w = v := by
  have hv : v ∈ comSp η ⊔ fixSp η := h.isCompl.sup_eq_top ▸ Submodule.mem_top
  exact Submodule.mem_sup.mp hv

theorem add_inj {d d' w w' : V} (hd : d ∈ comSp η) (hd' : d' ∈ comSp η) (hw : w ∈ fixSp η)
    (hw' : w' ∈ fixSp η) (heq : d + w = d' + w') : d = d' ∧ w = w' := by
  have h1 : d - d' = w' - w := by
    rw [sub_eq_sub_iff_add_eq_add, heq, add_comm]
  have h2 : d - d' ∈ comSp η ⊓ fixSp η := ⟨(comSp η).sub_mem hd hd', h1 ▸ (fixSp η).sub_mem hw' hw⟩
  rw [h.isCompl.inf_eq_bot, Submodule.mem_bot, h1, sub_eq_zero] at h2
  refine ⟨?_, h2.symm⟩
  rw [h2] at heq
  exact add_right_cancel heq

omit [Finite V] in
theorem exists_zpowers {b c : V} (hb : b ∈ comSp η) (hc : c ∈ comSp η) (hb0 : b ≠ 0)
    (hc0 : c ≠ 0) : ∃ g ∈ Subgroup.zpowers η, g b = c := by
  obtain ⟨k, hk⟩ := h.trans b hb c hc hb0 hc0
  exact ⟨η ^ k, Subgroup.npow_mem_zpowers η k, hk⟩

theorem eq_one_of_apply_eq {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ Subgroup.zpowers η) {d : V}
    (hd : d ∈ comSp η) (hd0 : d ≠ 0) (hgd : g d = d) : g = 1 := by
  ext v
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_add v
  rw [map_add, apply_eq_of_mem_zpowers hg hb, LinearEquiv.coe_one, id]
  congr 1
  by_cases ha0 : a = 0
  · rw [ha0, map_zero]
  obtain ⟨k, rfl⟩ := h.trans d hd a ha hd0 ha0
  have hcomm : g * η ^ k = η ^ k * g := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((Commute.refl η).zpow_left i).pow_right k |>.eq
  have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f d) hcomm
  simp only [LinearEquiv.mul_apply] at this
  rw [this, hgd]

theorem mem_fixSp_of_apply_eq {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ Subgroup.zpowers η) (hg1 : g ≠ 1)
    {v : V} (hgv : g v = v) : v ∈ fixSp η := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_add v
  have hga : g a ∈ comSp η := apply_mem_comSp (mul_comm_of_mem_zpowers hg) ha
  rw [map_add, apply_eq_of_mem_zpowers hg hb] at hgv
  have h1 := (h.add_inj hga ha hb hb hgv).1
  by_cases ha0 : a = 0
  · rw [ha0, zero_add]; exact hb
  · exact absurd (h.eq_one_of_apply_eq hg ha ha0 h1) hg1

omit [Finite V] in
theorem comSp_ne_bot : comSp η ≠ ⊥ := by
  intro hD
  apply h.ne_one
  ext v
  have : η v - v ∈ comSp η := mem_comSp.mpr ⟨v, rfl⟩
  rw [hD, Submodule.mem_bot, sub_eq_zero] at this
  simpa using this

theorem card_zpowers {d₀ : V} (hd₀ : d₀ ∈ comSp η) (hd₀0 : d₀ ≠ 0) :
    Nat.card (Subgroup.zpowers η) = Nat.card {v : V // v ∈ comSp η ∧ v ≠ 0} := by
  refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨(g : V ≃ₗ[ZMod 2] V) d₀,
    apply_mem_comSp (mul_comm_of_mem_zpowers g.2) hd₀, fun h0 => hd₀0 ?_⟩) ⟨?_, ?_⟩)
  · simpa using congrArg (fun v => (g : V ≃ₗ[ZMod 2] V)⁻¹ v) h0
  · intro g g' hgg
    have h1 : (g : V ≃ₗ[ZMod 2] V) d₀ = (g' : V ≃ₗ[ZMod 2] V) d₀ := congrArg Subtype.val hgg
    have hmem : (g' : V ≃ₗ[ZMod 2] V)⁻¹ * g ∈ Subgroup.zpowers η :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ g'.2) g.2
    have h2 : ((g' : V ≃ₗ[ZMod 2] V)⁻¹ * g) d₀ = d₀ := by
      rw [LinearEquiv.mul_apply, h1]
      simp
    have h3 := h.eq_one_of_apply_eq hmem hd₀ hd₀0 h2
    rw [inv_mul_eq_one] at h3
    exact Subtype.ext h3.symm
  · rintro ⟨v, hv, hv0⟩
    obtain ⟨g, hg, hgv⟩ := h.exists_zpowers hd₀ hv hd₀0 hv0
    exact ⟨⟨g, hg⟩, Subtype.ext hgv⟩

theorem card_zpowers_add_one : Nat.card (Subgroup.zpowers η) + 1 = Nat.card (comSp η) := by
  obtain ⟨d₀, hd₀, hd₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.comSp_ne_bot
  rw [h.card_zpowers hd₀ hd₀0, card_nonzero_add_one]

theorem two_le_finrank_comSp : 2 ≤ finrank (ZMod 2) (comSp η) := by
  by_contra hlt
  have h1 : 1 ≤ finrank (ZMod 2) (comSp η) := Submodule.one_le_finrank_iff.mpr h.comSp_ne_bot
  have hfin : finrank (ZMod 2) (comSp η) = 1 := by omega
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.comSp_ne_bot
  have hηd : η d ∈ comSp η := apply_mem_comSp rfl hd
  have hηd0 : η d ≠ 0 := fun h0 => hd0 (by simpa using congrArg η.symm h0)
  have hline : η d = d := by
    have hd' : (⟨d, hd⟩ : comSp η) ≠ 0 := fun h0 => hd0 (congrArg Subtype.val h0)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hd').mp hfin ⟨η d, hηd⟩
    have hc' : c • d = η d := congrArg Subtype.val hc
    rcases ONan.zmod_smul_eq c d with h0 | h1
    · exact absurd (hc'.symm.trans h0) hηd0
    · exact hc'.symm.trans h1
  exact h.ne_one (h.eq_one_of_apply_eq (Subgroup.mem_zpowers η) hd hd0 hline)

omit [Finite V] h in
theorem smul_fixSp_of_mem_zpowers {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ Subgroup.zpowers η) :
    g • fixSp η = fixSp η := by
  ext v
  rw [ONan.mem_smul_iff]
  constructor
  · intro hv
    have h1 : g⁻¹ v = v := by
      have := apply_eq_of_mem_zpowers hg hv
      simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at this
      exact this.symm
    rwa [h1] at hv
  · intro hv
    rw [apply_eq_of_mem_zpowers (Subgroup.inv_mem _ hg) hv]
    exact hv

omit [Finite V] in
theorem smul_eq_of_inf_ne_bot {x y : V ≃ₗ[ZMod 2] V} (hx : x ∈ X) (hy : y ∈ X)
    (hne : x • fixSp η ⊓ y • fixSp η ≠ ⊥) : x • fixSp η = y • fixSp η := by
  by_contra hxy
  apply hne
  have h1 : (y⁻¹ * x) • fixSp η ≠ fixSp η := by
    intro h2
    apply hxy
    rw [mul_smul, inv_smul_eq_iff] at h2
    exact h2
  have h2 := h.ti _ (X.mul_mem (X.inv_mem hy) hx) h1
  rw [Submodule.eq_bot_iff] at h2 ⊢
  intro v hv
  obtain ⟨hvx, hvy⟩ := Submodule.mem_inf.mp hv
  have hv' : y⁻¹ v ∈ (y⁻¹ * x) • fixSp η ⊓ fixSp η := by
    refine Submodule.mem_inf.mpr ⟨?_, (ONan.mem_smul_iff _ _ _).mp hvy⟩
    rw [ONan.mem_smul_iff]
    simpa using (ONan.mem_smul_iff _ _ _).mp hvx
  have := h2 _ hv'
  simpa using congrArg y this

omit [Finite V] in
theorem zpowers_le : Subgroup.zpowers η ≤ X := Subgroup.zpowers_le.mpr h.mem

theorem sub_mem_comSp {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ Subgroup.zpowers η) (v : V) :
    g v - v ∈ comSp η := by
  obtain ⟨d, hd, w, hw, rfl⟩ := h.exists_add v
  rw [map_add, apply_eq_of_mem_zpowers hg hw, add_sub_add_right_eq_sub]
  exact (comSp η).sub_mem (apply_mem_comSp (mul_comm_of_mem_zpowers hg) hd) hd

theorem card_compl :
    Nat.card {v : V // v ∉ fixSp η ∧ v ∉ comSp η} =
      Nat.card {d : V // d ∈ comSp η ∧ d ≠ 0} * Nat.card {w : V // w ∈ fixSp η ∧ w ≠ 0} := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ⟨p.1.1 + p.2.1, fun hW => p.1.2.2 ?_, fun hD => p.2.2.2 ?_⟩) ⟨?_, ?_⟩)
  · have h1 : p.1.1 = p.1.1 + p.2.1 - p.2.1 := by abel
    have h2 : p.1.1 ∈ comSp η ⊓ fixSp η := ⟨p.1.2.1, h1 ▸ (fixSp η).sub_mem hW p.2.2.1⟩
    rwa [h.isCompl.inf_eq_bot, Submodule.mem_bot] at h2
  · have h1 : p.2.1 = p.1.1 + p.2.1 - p.1.1 := by abel
    have h2 : p.2.1 ∈ comSp η ⊓ fixSp η := ⟨h1 ▸ (comSp η).sub_mem hD p.1.2.1, p.2.2.1⟩
    rwa [h.isCompl.inf_eq_bot, Submodule.mem_bot] at h2
  · rintro ⟨⟨d, hd⟩, ⟨w, hw⟩⟩ ⟨⟨d', hd'⟩, ⟨w', hw'⟩⟩ heq
    have := h.add_inj hd.1 hd'.1 hw.1 hw'.1 (congrArg Subtype.val heq)
    obtain ⟨rfl, rfl⟩ := this
    rfl
  · rintro ⟨v, hvW, hvD⟩
    obtain ⟨d, hd, w, hw, rfl⟩ := h.exists_add v
    refine ⟨⟨⟨d, hd, fun h0 => hvW ?_⟩, ⟨w, hw, fun h0 => hvD ?_⟩⟩, rfl⟩
    · rw [h0, zero_add]; exact hw
    · rw [h0, add_zero]; exact hd

end LinHyp

end CFSG.Goldschmidt.G2
