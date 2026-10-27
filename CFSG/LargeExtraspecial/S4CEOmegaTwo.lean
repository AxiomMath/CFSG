module

public import CFSG.LargeExtraspecial.S4CEOmegaFlag
public import CFSG.LargeExtraspecial.S4CEOmegaFrame
public import CFSG.LargeExtraspecial.S4CEOmegaModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions

theorem card_map_of_inf_ker_eq_bot {G H : Type*} [Group G] [Group H] (f : G →* H)
    {U : Subgroup G} (hU : U ⊓ f.ker = ⊥) : Nat.card (U.map f) = Nat.card U := by
  have hinj : Function.Injective (f.comp U.subtype) := by
    intro x y hxy
    have hmem : (x : G) * (y : G)⁻¹ ∈ U ⊓ f.ker := by
      refine mem_inf.mpr ⟨mul_mem x.2 (inv_mem y.2), ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact mul_inv_eq_one.mpr hxy
    rw [hU, mem_bot, mul_inv_eq_one] at hmem
    exact Subtype.ext hmem
  have hr : U.map f = (f.comp U.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem conj_mem_pointRadical_of_mem [FiniteDimensional (ZMod 2) V]
    (hQ : Q.polarBilin.Nondegenerate) {m t : V ≃ₗ[ZMod 2] V}
    (hm : m ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {b : V} (hb0 : b ≠ 0) (hb : Q b = 0)
    (ht : t ∈ pointRadical Q b) : m * t * m⁻¹ ∈ pointRadical Q (m b) := by
  obtain ⟨u, hu, rfl⟩ := (mem_pointRadical_iff hQ hb0 hb).mp ht
  rw [eichler_conj hm]
  exact eichler_mem_pointRadical (by rw [map_of_mem hm, hb]) (by rw [polar_map_of_mem hm, hu])

theorem pointRadical_le_map_conj [FiniteDimensional (ZMod 2) V]
    (hQ : Q.polarBilin.Nondegenerate) {m : V ≃ₗ[ZMod 2] V}
    (hm : m ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {b : V} (hb0 : b ≠ 0) (hb : Q b = 0) :
    pointRadical Q (m b) ≤ (pointRadical Q b).map (MulAut.conj m).toMonoidHom := by
  intro x hx
  have hmb0 : m b ≠ 0 := fun h0 => hb0 (m.map_eq_zero_iff.mp h0)
  have hmb : Q (m b) = 0 := by rw [map_of_mem hm, hb]
  have h1 := conj_mem_pointRadical_of_mem hQ (inv_mem hm) hmb0 hmb hx
  rw [inv_apply_self', inv_inv] at h1
  exact ⟨m⁻¹ * x * m, h1, by simp [mul_assoc]⟩

@[expose] noncomputable def flagLift {K : Type*} [Group K] (π : K →* (V ≃ₗ[ZMod 2] V))
    (E : Subgroup K) (a : V) (P : ℕ → HypPair Q) (i : ℕ) : Subgroup K :=
  Ept π E a (P i).e ⊓ (flagRoot P i).comap π

namespace CEHyp

variable [FiniteDimensional (ZMod 2) V] {K : Type*} [Group K] {π : K →* (V ≃ₗ[ZMod 2] V)}
  {E : Subgroup K} {a : V} {E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem exists_apply_eq_frame (hQ : Q.polarBilin.Nondegenerate) (h5 : 5 ≤ finrank (ZMod 2) V)
    (h : CEHyp π E a (omegaGroup Q hQ) E₀) {r : ℕ} (F : WittFrame Q a r) (i : ℕ) :
    ∃ k, π k a = (F.P i).e := by
  obtain ⟨g, hg, hga⟩ := O62.exists_mem_omegaGroup_apply_eq hQ h5 F.a_ne_zero
    (F.P i).e_ne_zero (by rw [F.map_a, (F.P i).Q_e])
  obtain ⟨k, rfl⟩ : g ∈ π.range := h.range_eq ▸ hg
  exact ⟨k, hga⟩

section Lift

variable (hQ : Q.polarBilin.Nondegenerate) (h5 : 5 ≤ finrank (ZMod 2) V)
  (h : CEHyp π E a (omegaGroup Q hQ) (pointRadical Q a)) {r : ℕ} (F : WittFrame Q a r)
include h5 h F

theorem flagRoot_le_map_Ept (i : ℕ) : flagRoot F.P i ≤ (Ept π E a (F.P i).e).map π := by
  obtain ⟨k, hk⟩ := h.exists_apply_eq_frame hQ h5 F i
  rw [h.map_Ept hk]
  refine (flagRoot_le_pointRadical i).trans ?_
  have hm : π k ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    omegaGroup_le Q hQ (h.range_eq ▸ ⟨k, rfl⟩)
  rw [← hk]
  exact pointRadical_le_map_conj hQ hm F.a_ne_zero F.map_a

theorem map_flagLift (i : ℕ) : (flagLift π E a F.P i).map π = flagRoot F.P i := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_inf.mp hy).2
  · obtain ⟨y, hy, rfl⟩ := h.flagRoot_le_map_Ept hQ h5 F i hx
    exact ⟨y, mem_inf.mpr ⟨hy, hx⟩, rfl⟩

theorem flagLift_inf_ker (i : ℕ) : flagLift π E a F.P i ⊓ π.ker = ⊥ := by
  rw [eq_bot_iff]
  refine (inf_le_inf_right _ inf_le_left).trans ?_
  rw [h.Ept_inf_ker (h.exists_apply_eq_frame hQ h5 F i)]

theorem card_flagLift (i : ℕ) : Nat.card (flagLift π E a F.P i) = Nat.card (flagRoot F.P i) := by
  rw [← h.map_flagLift hQ h5 F i, card_map_of_inf_ker_eq_bot π (h.flagLift_inf_ker hQ h5 F i)]

theorem flagLift_le_normalizer {i j : ℕ} (hij : i < j) (hj : j < r) :
    flagLift π E a F.P j ≤ normalizer (flagLift π E a F.P i : Set K) := by
  intro x hx
  obtain ⟨-, hxR⟩ := mem_inf.mp hx
  have hxe : π x (F.P i).e = (F.P i).e := flagRoot_apply_e F.orth hij hj hxR
  have hNE := h.mem_normalizer_Ept (h.exists_apply_eq_frame hQ h5 F i) hxe
  have hNR := flagRoot_le_normalizer F.orth hij hj hxR
  rw [mem_normalizer_iff] at hNE hNR ⊢
  intro y
  rw [flagLift, mem_inf, mem_inf, mem_comap, mem_comap, hNE y, hNR (π y), map_mul, map_mul,
    map_inv]

theorem exists_sylow_lift [Finite K] (hdim : finrank (ZMod 2) V = 2 * (r + 1)) :
    ∃ U : Subgroup K, U ⊓ π.ker = ⊥ ∧ Nat.card U = 2 ^ (r * (r + 1)) := by
  set U : Subgroup K := ⨆ i : Fin r, flagLift π E a F.P i with hUdef
  have hmap : U.map π = ⨆ i : Fin r, flagRoot F.P i := by
    rw [hUdef, Subgroup.map_iSup]
    exact iSup_congr fun i => h.map_flagLift hQ h5 F i
  have hle : Nat.card U ≤ 2 ^ (r * (r + 1)) := by
    calc Nat.card U ≤ ∏ i : Fin r, Nat.card (flagLift π E a F.P i) :=
          card_iSup_le_prod _ fun i j hij => h.flagLift_le_normalizer hQ h5 F hij j.2
      _ = ∏ i : Fin r, Nat.card (flagRoot F.P i) :=
          Finset.prod_congr rfl fun i _ => h.card_flagLift hQ h5 F i
      _ = 2 ^ (r * (r + 1)) := prod_card_flagRoot F.orth hdim
  have hcardmap : Nat.card (U.map π) = 2 ^ (r * (r + 1)) := by
    rw [hmap]
    exact card_iSup_flagRoot F.orth hdim
  have hU : U ⊓ π.ker = ⊥ := inf_ker_eq_bot_of_card_le π (hle.trans hcardmap.ge)
  exact ⟨U, hU, by rw [← card_map_of_inf_ker_eq_bot π hU, hcardmap]⟩

end Lift

theorem odd_card_ker_of_omega [Finite K] (hQ : Q.polarBilin.Nondegenerate) (ha0 : a ≠ 0)
    (ha : Q a = 0) (h6 : 6 ≤ finrank (ZMod 2) V)
    (h : CEHyp π E a (omegaGroup Q hQ) (pointRadical Q a)) : Odd (Nat.card π.ker) := by
  obtain ⟨n, hn⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have hdim : finrank (ZMod 2) V = 2 * (r + 1) := by omega
  obtain ⟨F⟩ := exists_wittFrame hQ ha0 ha (r := r) (by omega) hdim
  have hperf := pointRadical_le_commutator hQ (by omega : 2 ≤ r) F
  obtain ⟨M, hModd, hcard⟩ := card_omegaGroup_eq hQ (n := r + 1) (by omega) hdim
  obtain ⟨U, hU, hUcard⟩ := h.exists_sylow_lift hQ (by omega) F hdim
  refine h.odd_card_ker hperf hU hModd ?_
  rw [hcard, hUcard, Nat.add_sub_cancel, mul_comm (r + 1) r]

end CEHyp

end CFSG.LargeExtraspecial.S4
