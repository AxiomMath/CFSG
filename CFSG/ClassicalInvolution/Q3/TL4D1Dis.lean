module

public import CFSG.ClassicalInvolution.Q3.TL4D1OutB
public import CFSG.ClassicalInvolution.Q3.TL4D1FinB
public import CFSG.ClassicalInvolution.Q3.TL4D1Comp
public import CFSG.ClassicalInvolution.Q3.TL4D1Core

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

theorem false_of_core (hF : D1Facts) {G : Type} [Group G] [Finite G]
    (hD2 : ThmDAbsBelow 3 (Nat.card G + 1)) {Δ : Set (Subgroup G)} (h : T4Hyp 3 G Δ)
    (hall : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → TightInO2 z) {J L : Subgroup G}
    (hJ : J ∈ Δ) (hL : L ∈ Δ) (hnc : ¬ ∃ g : G, conjSub g J = L) {u v : G}
    (hu : IsUniqueInvolution J u) (hv : IsUniqueInvolution L v)
    (hvJ : v ∉ Subgroup.normalizer (J : Set G)) (hJL : J ⊔ L = ⊤) : False := by
  have h2 : ∀ K ∈ Δ, IsPGroup 2 K := fun K hK => h.isPGroup_of_all hall hK
  have huv : u * v ≠ v * u := fun hc => hvJ (h.tight J hJ u hu
    (Subgroup.mem_centralizer_singleton_iff.mpr hc.symm))
  have hthinJ : ∀ x ∈ J, x ∈ pCore 2 G → x = 1 ∨ x = u := fun x hx hxQ =>
    h.mem_of_mem_normal_two hJ hL hu hv (h2 L hL) huv pCore_normal pCore_isPGroup hx hxQ
  have hthinL : ∀ T : Subgroup G, T.Normal → IsPGroup 2 T → ∀ x ∈ L, x ∈ T →
      x = 1 ∨ x = v := fun T hTn hT2 x hx hxT =>
    h.mem_of_mem_normal_two hL hJ hv hu (h2 J hJ) (Ne.symm huv) hTn hT2 hx hxT
  obtain ⟨X, sX⟩ := exists_d1Sub hF h hall hD2 hJ hu hthinJ
  obtain ⟨Y, sY⟩ := exists_d1Sub hF h hall hD2 hL hv
    (fun x hx hxQ => hthinL _ pCore_normal pCore_isPGroup x hx hxQ)
  have hXtop : X = ⊤ := by
    rcases eq_or_comm_mem_pCore sX.sub sY.sub sX.pack sY.pack with hXY | hc
    · rw [eq_top_iff, ← hJL]
      exact sup_le sX.le (hXY ▸ sY.le)
    · exfalso
      apply sX.pack.not_two
      set π := QuotientGroup.mk' (pCore 2 G) with hπ
      have hJ2 : IsPGroup 2 ↥(J.map π) := (h2 J hJ).map _
      have hL2 : IsPGroup 2 ↥(L.map π) := (h2 L hL).map _
      have hN : J.map π ≤ Subgroup.normalizer ((L.map π : Subgroup _) : Set (G ⧸ pCore 2 G)) := by
        rintro _ ⟨a, ha, rfl⟩
        have hca : ∀ b ∈ L, π a * π b = π b * π a := fun b hb => by
          have h1 : π (a * b * a⁻¹ * b⁻¹) = 1 :=
            (QuotientGroup.eq_one_iff _).mpr (hc a (sX.le ha) b (sY.le hb))
          rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
          calc π a * π b = π a * π b * (π a)⁻¹ * (π b)⁻¹ * (π b * π a) := by group
            _ = π b * π a := by rw [h1, one_mul]
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨b, hb, rfl⟩
          rw [hca b hb, mul_inv_cancel_right]
          exact ⟨b, hb, rfl⟩
        · rintro ⟨b, hb, hbe⟩
          have hy : y = π b := by
            calc y = (π a)⁻¹ * (π a * y * (π a)⁻¹) * π a := by group
              _ = (π a)⁻¹ * (π b * π a) := by rw [← hbe]; group
              _ = (π a)⁻¹ * (π a * π b) := by rw [hca b hb]
              _ = π b := by group
          rw [hy]
          exact ⟨b, hb, rfl⟩
      have hsup : IsPGroup 2 ↥(J.map π ⊔ L.map π) := hJ2.to_sup_of_normal_right' hL2 hN
      have hG2 : IsPGroup 2 ↥((J.map π ⊔ L.map π).comap π) :=
        hsup.comap_of_ker_isPGroup π (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
      have htop : (J.map π ⊔ L.map π).comap π = ⊤ := by
        rw [eq_top_iff, ← hJL]
        exact sup_le (fun x hx => Subgroup.mem_sup_left (Subgroup.mem_map_of_mem π hx))
          (fun x hx => Subgroup.mem_sup_right (Subgroup.mem_map_of_mem π hx))
      exact (htop ▸ hG2).to_le le_top
  rcases sX.out with ⟨E, hE⟩ | ⟨n, 𝒜, M, hn, hMem, ⟨I⟩⟩
  · rw [hXtop] at hE
    exact false_of_e8_top hE (hall J hJ u hu) (hall L hL v hv) huv
  · refine false_of_ident_top h hall ?_ (sX.span.trans hXtop) hn hMem I hL ?_ hv ?_ hthinL
    · rintro _ ⟨x, -, rfl⟩
      exact h.hyp.conjInvariant x J hJ
    · rintro ⟨x, -, hx⟩
      exact hnc ⟨x, hx⟩
    · by_contra hc
      push Not at hc
      apply hvJ
      rw [Subgroup.mem_normalizer_iff]
      intro j
      rw [← hc j, mul_inv_cancel_right]

theorem d1Core3_of_facts (hF : D1Facts) (n : ℕ) : D1Core3 n :=
  fun _ _ _ _ _ hD2 _ h hall _ hJ _ hL hnc _ _ hu hv hvJ _ hJL _ _ _ =>
    false_of_core hF hD2 h hall hJ hL hnc hu hv hvJ hJL

end CFSG.ClassicalInvolution.Q3.TL4
