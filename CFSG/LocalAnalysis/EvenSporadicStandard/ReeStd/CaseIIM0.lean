module

import CFSG.LocalAnalysis.EvenSporadicStandard.J1.CaseIIM0
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.RC

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

namespace LocalSetting

theorem z_ne_sq (H : LocalSetting G) (y : G) : y * y ≠ H.z := by
  intro hy
  have hcomm : y * H.z = H.z * y := by
    calc y * H.z = y * (y * y) := by rw [hy]
      _ = (y * y) * y := by group
      _ = H.z * y := by rw [hy]
  have hy4 : y ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    rw [pow_two, pow_two]
    rw [hy, H.z_mul_self]
  have hP : IsPGroup 2 (zpowers y) := isPGroup_zpowers (k := 2) hy4
  have hPC : zpowers y ≤ centralizer ({H.z} : Set G) :=
    zpowers_le.2 (mem_centralizer_singleton_iff.2 hcomm)
  have hsq := (H.star hP hPC).2 y (mem_zpowers y)
  rw [hy] at hsq
  exact H.z_ne_one hsq

end LocalSetting

namespace Stage

variable {H : LocalSetting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem sq_mem_of_mem {y : G} (hy : y * y ∈ S) : y * y ∈ Λ := by
  by_contra hΛ
  obtain ⟨c, hc⟩ := _root_.isConj_iff.1 (h.conj _ hy hΛ)
  refine H.z_ne_sq (c⁻¹ * y * c) ?_
  calc c⁻¹ * y * c * (c⁻¹ * y * c) = c⁻¹ * (y * y) * c := by group
    _ = H.z := by rw [← hc]; group

include h in
theorem exists_M0 (hcase : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ H.RC S → P ≤ S)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hST : S ≤ T) (hTN : T ≤ normalizer (S : Set G))
    (hTcard : Nat.card T = 8 * Nat.card S) :
    ∃ M₀ : Subgroup G, M₀ ≤ T ∧ Λ ≤ M₀ ∧ H.z ∉ M₀ ∧ M₀.relIndex T = 2 := by
  have hΛT : Λ ≤ T := h.le.trans hST
  have hzT : H.z ∈ T := hST h.z_mem
  have hTE : T ≤ normalizer (H.E : Set G) := fun t ht =>
    mem_normalizer_iff.2 fun e => ⟨fun he => h.N_conj_E (hTN ht) he, fun he => by
      have := h.N_conj_E (inv_mem (hTN ht)) he
      simpa [mul_assoc] using this⟩
  set ρ : T →* MulAut H.E := H.E.normalizerMonoidHom.comp (Subgroup.inclusion hTE)
  have hρapp : ∀ (t : T) (e : H.E), ((ρ t e : H.E) : G) = t * e * (t : G)⁻¹ := fun t e => rfl
  have hker : ∀ t : T, ρ t = 1 ↔ (t : G) ∈ S := by
    intro t
    constructor
    · intro h1
      have hc : (t : G) ∈ centralizer (H.E : Set G) := by
        refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
        have h2 := congrArg (fun φ : MulAut H.E => ((φ ⟨e, he⟩ : H.E) : G)) h1
        simp only [hρapp, MulAut.one_apply] at h2
        calc e * t = (t * e * (t : G)⁻¹) * t := by rw [h2]
          _ = t * e := by group
      have hR : (t : G) ∈ H.RC S := ⟨hc, hTN t.2⟩
      exact hcase (zpowers (t : G)) (hT.to_le (zpowers_le.2 t.2)) (zpowers_le.2 hR)
        (mem_zpowers _)
    · intro hs
      have hc : (t : G) ∈ centralizer (H.E : Set G) := (h.S_le_RC hs).1
      refine MulEquiv.ext fun e => Subtype.ext ?_
      rw [hρapp]
      have := Subgroup.mem_centralizer_iff.1 hc e e.2
      show (t : G) * e * (t : G)⁻¹ = e
      rw [← this]
      group
  have hkercard : Nat.card ρ.ker = Nat.card S :=
    Nat.card_congr ⟨fun t => ⟨t.1.1, (hker t.1).1 t.2⟩,
      fun s => ⟨⟨s.1, hST s.2⟩, (hker ⟨s.1, hST s.2⟩).2 s.2⟩, fun t => rfl, fun s => rfl⟩
  have hrange : Nat.card ρ.range = 8 := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    rw [hkercard, hTcard] at h1
    have hpos : 0 < Nat.card S := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm _ _))
  have hEcomm : ∀ a b : H.E, a * b = b * a := fun a b => Subtype.ext (H.E_comm a.2 b.2)
  have hEsq : ∀ a : H.E, a * a = 1 := fun a => Subtype.ext (H.sq_E a a.2)
  obtain ⟨α, β, hαP, hβP, hα, hβ, hαβ, hgen⟩ :=
    J1Std.exists_dihedral_pair H.card_E hEcomm hEsq hrange
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hαP
  obtain ⟨s', rfl⟩ := MonoidHom.mem_range.1 hβP
  have hsq : ∀ t : T, ρ t * ρ t = 1 → (t : G) * t ∈ Λ := fun t ht =>
    h.sq_mem_of_mem ((hker (t * t)).1 (by rw [map_mul]; exact ht))
  have h4 : (ρ s * ρ s') ^ 4 = 1 := hαβ ▸ pow_orderOf_eq_one _
  have hy : ρ ((s * s') ^ 2) * ρ ((s * s') ^ 2) = 1 := by
    rw [map_pow, ← pow_add, map_mul]
    exact h4
  have hab4 : (s * s') ^ 4 ∈ Λ.subgroupOf T := by
    have : (s * s') ^ 4 = (s * s') ^ 2 * (s * s') ^ 2 := by rw [← pow_add]
    rw [this]
    exact hsq _ hy
  have : (Λ.subgroupOf T).Normal := ⟨fun n hn g => h.N_normalizes_Λ (hTN g.2) hn⟩
  have hN : Λ.subgroupOf T ≤ ρ.ker := fun n hn => (hker n).2 (h.le hn)
  have hNcard : Nat.card (Λ.subgroupOf T) = Nat.card Λ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛT).toEquiv
  have hTc : Nat.card T = 16 * Nat.card (Λ.subgroupOf T) := by
    rw [hTcard, hNcard, h.card_S]
    ring
  obtain ⟨M, hNM, hzM, hMi⟩ := J1Std.exists_index_two_avoiding_of_normal ρ (Λ.subgroupOf T) hN
    hrange hTc (a := s) (b := s') (c := ⟨H.z, hzT⟩) (hsq s hα) (hsq s' hβ) hab4 hgen
    ((hker _).2 h.z_mem) (fun hzN => h.z_not_mem hzN)
  refine ⟨M.map T.subtype, Subgroup.map_subtype_le M, fun l hl => ?_, ?_, ?_⟩
  · exact ⟨⟨l, hΛT hl⟩, hNM hl, rfl⟩
  · rintro ⟨t, htM, hteq⟩
    exact hzM (by
      have : t = ⟨H.z, hzT⟩ := Subtype.ext hteq
      rwa [this] at htM)
  · have : (M.map T.subtype).relIndex T = M.index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        comap_map_eq_self_of_injective T.subtype_injective]
    rw [this, hMi]

end Stage

end CFSG.EvenSporadicStandard.ReeStd
