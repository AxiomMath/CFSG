module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2CaseA

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

section SmallCentralizer

theorem two_group_cent_two {R : Type} [Group R] [Finite R] (hR : IsPGroup 2 R) {z : R}
    (hzz : z * z = 1) (hz1 : z ≠ 1) (hC : Nat.card ↥(centralizer ({z} : Set R)) ≤ 2) :
    Nat.card R ≤ 2 := by
  classical
  have hnt : Nontrivial R := ⟨⟨z, 1, hz1⟩⟩
  obtain ⟨c, hcZ, hc1, hcc⟩ := exists_central_involution hR hnt
  have hcz : c = z := by
    by_contra hne
    have hmem : ∀ a ∈ ({1, z, c} : Finset R), a ∈ centralizer ({z} : Set R) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact one_mem _
      · rw [mem_centralizer_iff]; intro w hw; rw [Set.mem_singleton_iff] at hw; rw [hw]
      · rw [mem_centralizer_iff]; intro w hw; rw [Set.mem_singleton_iff] at hw; rw [hw]
        exact (mem_center_iff.1 hcZ) z
    have hcard : ({1, z, c} : Finset R).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · exact fun h => hne (Finset.mem_singleton.1 h).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hz1.symm, hc1.symm⟩
    have hle : ({1, z, c} : Finset R).card ≤ Nat.card (centralizer ({z} : Set R)) := by
      have := Set.ncard_le_ncard (s := (({1, z, c} : Finset R) : Set R))
        (t := (centralizer ({z} : Set R) : Set R)) (fun a ha => hmem a (by simpa using ha))
        (Set.toFinite _)
      rw [Set.ncard_coe_finset] at this
      rwa [← Nat.card_coe_set_eq] at this
    omega
  have hzc : z ∈ center R := hcz ▸ hcZ
  have : centralizer ({z} : Set R) = ⊤ := by
    rw [centralizer_eq_top_iff_subset]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]; exact hzc
  rw [this, Subgroup.card_top] at hC
  exact hC

variable {M N : Subgroup G}

theorem ambient_small [Finite G] (hN : NormIn N M) (h2 : IsPGroup 2 ↥M) {z : G} (hzM : z ∈ M)
    (hzz : z * z ∈ N) (hzN : z ∉ N) (hC : Nat.card (cenMod M N z hN.norm) ≤ 2 * Nat.card N) :
    Nat.card M ≤ 2 * Nat.card N := by
  have := hN.normal
  have hR2 : IsPGroup 2 (↥M ⧸ N.subgroupOf M) := h2.to_quotient _
  let z' : ↥M := ⟨z, hzM⟩
  have hzb2 : qm M N z' * qm M N z' = 1 := by
    rw [← map_mul]
    exact qm_eq_one.2 (by simpa using hzz)
  have hzb1 : qm M N z' ≠ 1 := fun h => hzN (qm_eq_one.1 h)
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hCR : Nat.card ↥(centralizer ({qm M N z'} : Set (↥M ⧸ N.subgroupOf M))) ≤ 2 := by
    have h := card_cenMod_eq hN.le hN.norm hzM
    rw [h] at hC
    have : Nat.card N * Nat.card ↥(centralizer ({qm M N z'} : Set (↥M ⧸ N.subgroupOf M))) ≤
        Nat.card N * 2 := by linarith
    exact Nat.le_of_mul_le_mul_left this hNpos
  have h1 := two_group_cent_two hR2 hzb2 hzb1 hCR
  have h2' := card_QR (M := M) hN.le
  calc Nat.card M = Nat.card (↥M ⧸ N.subgroupOf M) * Nat.card N := h2'.symm
    _ ≤ 2 * Nat.card N := Nat.mul_le_mul_right _ h1

theorem exists_invol_mod [Finite G] {S M : Subgroup G} (hS : IsPGroup 2 ↥S) (hlt : M < S) :
    ∃ b ∈ S, b ∉ M ∧ (∀ m, m ∈ M ↔ b * m * b⁻¹ ∈ M) ∧ b * b ∈ M := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hnS, hnM, hnN⟩ := exists_mem_normalizer_not_mem hS hlt
  let U : Subgroup G := S ⊓ normalizer (M : Set G)
  have hMU : M ≤ U := fun m hm => ⟨hlt.le hm, (Subgroup.le_normalizer hm)⟩
  have hnU : n ∈ U := ⟨hnS, hnN⟩
  have hU : NormIn M U := ⟨hMU, fun u hu m hm => by
    have := (mem_normalizer_iff.1 hu.2 m).1 hm
    exact this⟩
  have := hU.normal
  have hU2 : IsPGroup 2 ↥U := hS.to_le inf_le_left
  have hQ2 : IsPGroup 2 (↥U ⧸ M.subgroupOf U) := hU2.to_quotient _
  have hcard : 2 ∣ Nat.card (↥U ⧸ M.subgroupOf U) := by
    rcases hQ2.card_eq_or_dvd with h | h
    · exfalso
      have hsub : Subsingleton (↥U ⧸ M.subgroupOf U) := (Nat.card_eq_one_iff_unique.1 h).1
      have h1 : qm U M ⟨n, hnU⟩ = qm U M 1 := Subsingleton.elim _ _
      have h2 := qm_eq_iff.1 h1
      have : (⟨n, hnU⟩ : ↥U).1⁻¹ * (1 : ↥U).1 ∈ M := h2
      simp at this
      exact hnM this
    · exact h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥U ⧸ M.subgroupOf U) 2 hcard
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective u
  refine ⟨b.1, b.2.1, ?_, ?_, ?_⟩
  · intro hbM
    have h1 : qm U M b = 1 := qm_eq_one.2 hbM
    have : orderOf (qm U M b) = 1 := by rw [h1]; exact orderOf_one
    rw [show (qm U M b) = (b : ↥U ⧸ M.subgroupOf U) from rfl] at this
    omega
  · intro m
    have := (mem_normalizer_iff.1 b.2.2 m)
    exact this
  · have h2 : (b : ↥U ⧸ M.subgroupOf U) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hu])
    have h3 : qm U M (b * b) = 1 := by
      rw [map_mul]
      have : (b : ↥U ⧸ M.subgroupOf U) * b = 1 := by rwa [pow_two] at h2
      exact this
    exact qm_eq_one.1 h3

end SmallCentralizer


namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem cenMod_eq_Hs [Finite G] (h10 : IG_10_31) {M : Subgroup G} (hMS : M ≤ S)
    (hHsM : H ⊔ T ≤ M) (hMn : ∀ m ∈ M, ∀ n ∈ Hzero H f, m * n * m⁻¹ ∈ Hzero H f) :
    cenMod M (Hzero H f) x hMn = H ⊔ T := by
  ext g
  constructor
  · rintro ⟨hgM, hg⟩
    obtain ⟨k, hk, hkg⟩ := IsFreeConj.lift c.c2 h10 c.isFree_x hg
    have hkgS : k * g ∈ S := S.mul_mem (c.P_le_S hk) (hMS hgM)
    have hkgC : k * g ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      calc x * (k * g) = (x * (k * g) * x⁻¹) * x := by group
        _ = (k * g) * x := by rw [hkg]
    have hkgT : k * g ∈ T := by
      rw [c.T_eq_cent]
      exact ⟨hkgS, hkgC⟩
    have : g = k⁻¹ * (k * g) := by group
    rw [this]
    exact (H ⊔ T).mul_mem ((H ⊔ T).inv_mem (Subgroup.mem_sup_left (c.c2.c3.H0_le hk)))
      (Subgroup.mem_sup_right hkgT)
  · intro hg
    refine ⟨hHsM hg, ?_⟩
    obtain ⟨p, hp, t, ht, rfl⟩ := c.Hstar_decomp g hg
    have hxt : x * t * x⁻¹ = t := by
      have := c.c2.c3.T_comm_x ht
      calc x * t * x⁻¹ = (t * x) * x⁻¹ := by rw [← this]
        _ = t := by group
    have e : x * (p * t) * x⁻¹ * (p * t)⁻¹ = (x * p * x⁻¹) * p⁻¹ := by
      calc x * (p * t) * x⁻¹ * (p * t)⁻¹ = (x * p * x⁻¹) * (x * t * x⁻¹) * t⁻¹ * p⁻¹ := by group
        _ = (x * p * x⁻¹) * t * t⁻¹ * p⁻¹ := by rw [hxt]
        _ = (x * p * x⁻¹) * p⁻¹ := by group
    rw [e]
    exact (Hzero H f).mul_mem (c.c2.c3.H0_norm_H x c.c2.c3.x_mem_H p hp) ((Hzero H f).inv_mem hp)

theorem false_of_beta [Finite G] (h10 : IG_10_31) (h15 : IG_15_15)
    (hS0 : S ≤ S0 S (Hzero H f)) (hlt : H ⊔ T < S) : False := by
  have hP := c.c2.c3
  have hSn : ∀ m ∈ S, ∀ n ∈ Hzero H f, m * n * m⁻¹ ∈ Hzero H f :=
    fun m hm n hn => ((mem_S0.1 (hS0 hm)).2 n).1 hn
  have hn : NormIn (Hzero H f) S := ⟨c.P_le_S, hSn⟩
  have hcen : cenMod S (Hzero H f) x hSn = H ⊔ T := c.cenMod_eq_Hs h10 le_rfl c.le hSn
  have hxS : x ∈ S := c.x_mem_S
  have hxx : x * x ∈ Hzero H f := by rw [hP.x_sq]; exact one_mem _
  have hlt' := Subgroup.card_lt_of_lt hlt
  rcases c.card_Hs_cases with ⟨h8, hHs⟩ | ⟨h16, h64⟩
  ·
    have hsmall := ambient_small hn c.S_two hxS hxx hP.x_notin_H0 (by
      rw [hcen, hHs, c.card_H, c.c2.P_card])
    rw [hHs, c.card_H] at hlt'
    rw [c.c2.P_card] at hsmall
    omega
  ·
    have h128 : 128 ≤ Nat.card S := by
      obtain ⟨j, hj⟩ := c.S_two.exists_card_eq (p := 2)
      rw [h64] at hlt'
      rw [hj] at hlt' ⊢
      by_contra hcon
      push Not at hcon
      have : j < 7 := by
        by_contra hj7
        push Not at hj7
        have : 2 ^ 7 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj7
        omega
      have : j ≤ 6 := by omega
      have : 2 ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) this
      omega
    obtain ⟨Q, hPQ, hQS, hQn, hQidx, hxQ, hQinv⟩ := ambient_cyclic_index_two hn c.S_two hxS hxx
      hP.x_notin_H0 (by rw [hcen, h64, c.c2.P_card]) (by rw [c.c2.P_card]; omega)
    obtain ⟨w, hwQ, hext⟩ := transfer_index_two h15 hP.out.simple hP.out.nonabelian c.syl hQS hQidx
      hxS hxQ hP.x_sq
    have hyS : w * x * w⁻¹ ∈ S := hQS hwQ
    have hfree : IsFreeConj x (Hzero H f) (w * x * w⁻¹) := ⟨⟨w, rfl⟩, hSn _ hyS⟩
    have hy2 := hfree.sq c.c2
    have hcentral : ∀ s ∈ S, (w * x * w⁻¹) * s * (w * x * w⁻¹)⁻¹ * s⁻¹ ∈ Hzero H f := by
      intro s hs
      have := hQinv _ hwQ (by rw [hy2]; exact one_mem _) s hs
      exact this
    have hcover : ∀ s ∈ S, ∃ n ∈ Hzero H f, ∃ c' ∈ S ⊓ centralizer ({w * x * w⁻¹} : Set G),
        s = n * c' := by
      intro s hs
      obtain ⟨k, hk, hkg⟩ := hfree.lift c.c2 h10 (hcentral s hs)
      refine ⟨k⁻¹, (Hzero H f).inv_mem hk, k * s, ⟨S.mul_mem (c.P_le_S hk) hs, ?_⟩, by group⟩
      show k * s ∈ centralizer ({w * x * w⁻¹} : Set G)
      rw [mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      calc (w * x * w⁻¹) * (k * s) = ((w * x * w⁻¹) * (k * s) * (w * x * w⁻¹)⁻¹) * (w * x * w⁻¹) := by
            group
        _ = (k * s) * (w * x * w⁻¹) := by rw [hkg]
    have hcard := card_mul_inf_le hcover
    have hcap : Hzero H f ⊓ (S ⊓ centralizer ({w * x * w⁻¹} : Set G)) =
        Hzero H f ⊓ centralizer ({w * x * w⁻¹} : Set G) := by
      ext g
      simp only [mem_inf]
      constructor
      · rintro ⟨hg, -, hgc⟩; exact ⟨hg, hgc⟩
      · rintro ⟨hg, hgc⟩; exact ⟨hg, c.P_le_S hg, hgc⟩
    rw [hcap, hfree.card4 c.c2, card_extremal hP.out hext.2, h16, c.c2.P_card] at hcard
    omega

end Ctx2S


namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem false_of_gamma [Finite G] (h10 : IG_10_31) (hlt1 : S0 S (Hzero H f) < S) : False := by
  have hP := c.c2.c3
  have hn0 := c.normIn_S0
  have hS0n : ∀ m ∈ S0 S (Hzero H f), ∀ n ∈ Hzero H f, m * n * m⁻¹ ∈ Hzero H f := hn0.norm
  obtain ⟨b, hbS, hbS0, hbN, hbb⟩ := exists_invol_mod c.S_two hlt1
  have hbN' : ∀ m ∈ S0 S (Hzero H f), b⁻¹ * m * b ∈ S0 S (Hzero H f) := by
    intro m hm
    apply (hbN _).2
    have e : b * (b⁻¹ * m * b) * b⁻¹ = m := by group
    rw [e]; exact hm
  have hbb' : ∀ q ∈ Hzero H f, (b * b) * q * (b * b)⁻¹ ∈ Hzero H f := hS0n _ hbb
  have hbb'' : ∀ q ∈ Hzero H f, (b * b)⁻¹ * q * ((b * b)⁻¹)⁻¹ ∈ Hzero H f :=
    hS0n _ ((S0 S (Hzero H f)).inv_mem hbb)
  let P' : Subgroup G := cj b (Hzero H f)
  have hmemP' : ∀ a : G, a ∈ P' ↔ b⁻¹ * a * b ∈ Hzero H f := fun a => mem_cj
  have hP'S0 : P' ≤ S0 S (Hzero H f) := by
    intro a ha
    have h1 : b⁻¹ * a * b ∈ S0 S (Hzero H f) := hn0.le ((hmemP' a).1 ha)
    have h2 := (hbN _).1 h1
    have e : b * (b⁻¹ * a * b) * b⁻¹ = a := by group
    rwa [e] at h2
  have hP'norm : ∀ m ∈ S0 S (Hzero H f), ∀ a ∈ P', m * a * m⁻¹ ∈ P' := by
    intro m hm a ha
    rw [hmemP']
    have h1 := hS0n _ (hbN' m hm) _ ((hmemP' a).1 ha)
    have e : b⁻¹ * (m * a * m⁻¹) * b = (b⁻¹ * m * b) * (b⁻¹ * a * b) * (b⁻¹ * m * b)⁻¹ := by group
    rw [e]; exact h1
  have hP'sq : ∀ a ∈ P', a * a = 1 := by
    intro a ha
    have h1 := c.c2.P_sq _ ((hmemP' a).1 ha)
    have e : b⁻¹ * (a * a) * b = (b⁻¹ * a * b) * (b⁻¹ * a * b) := by group
    have h2 : b⁻¹ * (a * a) * b = 1 := by rw [e, h1]
    have h3 : b⁻¹ * (a * a) = b⁻¹ := mul_inv_eq_one.1 (by simpa using h2)
    exact mul_eq_left.1 h3
  have hP'comm : ∀ a ∈ P', ∀ a' ∈ P', a * a' = a' * a := by
    intro a ha a' ha'
    have h1 := c.c2.P_comm _ ((hmemP' a).1 ha) _ ((hmemP' a').1 ha')
    have e1 : b⁻¹ * (a * a') * b = (b⁻¹ * a * b) * (b⁻¹ * a' * b) := by group
    have e2 : b⁻¹ * (a' * a) * b = (b⁻¹ * a' * b) * (b⁻¹ * a * b) := by group
    have h2 : b⁻¹ * (a * a') * b = b⁻¹ * (a' * a) * b := by rw [e1, e2, h1]
    exact mul_left_cancel (mul_right_cancel h2)
  have hP'card : Nat.card P' = 16 := by
    show Nat.card (cj b (Hzero H f)) = 16
    rw [card_cj, c.c2.P_card]
  have hP'ne : P' ≠ Hzero H f := by
    intro heq
    apply hbS0
    rw [mem_S0]
    refine ⟨hbS, fun q => ?_⟩
    constructor
    · intro hq
      have : b * q * b⁻¹ ∈ P' := by
        rw [hmemP']
        have e : b⁻¹ * (b * q * b⁻¹) * b = q := by group
        rw [e]; exact hq
      rwa [heq] at this
    · intro hq
      have : b * q * b⁻¹ ∈ P' := by rw [heq]; exact hq
      have := (hmemP' _).1 this
      have e : b⁻¹ * (b * q * b⁻¹) * b = q := by group
      rwa [e] at this
  have hP'el : IsElemAb2 P' := fun a ha => ⟨hP'sq a ha, fun b' hb' => hP'comm a ha b' hb'⟩
  let Hw : Subgroup G :=
    { carrier := {a | ∃ p ∈ Hzero H f, ∃ p' ∈ P', a = p * p'}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro a₁ a₂ ⟨p₁, hp₁, q₁, hq₁, rfl⟩ ⟨p₂, hp₂, q₂, hq₂, rfl⟩
        refine ⟨p₁ * (q₁ * p₂ * q₁⁻¹),
          (Hzero H f).mul_mem hp₁ (hS0n q₁ (hP'S0 hq₁) p₂ hp₂), q₁ * q₂, P'.mul_mem hq₁ hq₂,
          by group⟩
      inv_mem' := by
        rintro a ⟨p, hp, q, hq, rfl⟩
        refine ⟨q⁻¹ * p⁻¹ * q⁻¹⁻¹, hS0n q⁻¹ (hP'S0 (P'.inv_mem hq)) p⁻¹ ((Hzero H f).inv_mem hp),
          q⁻¹, P'.inv_mem hq, by group⟩ }
  have hwP : Hzero H f ≤ Hw := fun p hp => ⟨p, hp, 1, one_mem _, by simp⟩
  have hwP' : P' ≤ Hw := fun p' hp' => ⟨1, one_mem _, p', hp', by simp⟩
  have hwS0 : Hw ≤ S0 S (Hzero H f) := by
    rintro _ ⟨p, hp, q, hq, rfl⟩
    exact (S0 S (Hzero H f)).mul_mem (hn0.le hp) (hP'S0 hq)
  have hwn : ∀ m ∈ S0 S (Hzero H f), ∀ k ∈ Hw, m * k * m⁻¹ ∈ Hw := by
    rintro m hm _ ⟨p, hp, q, hq, rfl⟩
    exact ⟨m * p * m⁻¹, hS0n m hm p hp, m * q * m⁻¹, hP'norm m hm q hq, by group⟩
  have hbw : ∀ k ∈ Hw, b * k * b⁻¹ ∈ Hw := by
    rintro _ ⟨p, hp, q, hq, rfl⟩
    have h1 : b * p * b⁻¹ ∈ P' := by
      rw [hmemP']
      have e : b⁻¹ * (b * p * b⁻¹) * b = p := by group
      rw [e]; exact hp
    have h2 : b * q * b⁻¹ ∈ Hzero H f := by
      have := hbb' _ ((hmemP' q).1 hq)
      have e : b * (b⁻¹ * q * b) * b⁻¹ = q := by group
      have e2 : (b * b) * (b⁻¹ * q * b) * (b * b)⁻¹ = b * q * b⁻¹ := by group
      rwa [e2] at this
    have e : b * (p * q) * b⁻¹ = (b * p * b⁻¹) * (b * q * b⁻¹) := by group
    rw [e]
    exact Hw.mul_mem (hwP' h1) (hwP h2)
  have hbw' : ∀ k ∈ Hw, b⁻¹ * k * b ∈ Hw := by
    rintro _ ⟨p, hp, q, hq, rfl⟩
    have h1 : b⁻¹ * p * b ∈ P' := by
      rw [hmemP']
      have := hbb'' _ hp
      have e : b⁻¹ * (b⁻¹ * p * b) * b = (b * b)⁻¹ * p * ((b * b)⁻¹)⁻¹ := by
        rw [inv_inv, mul_inv_rev]; simp only [mul_assoc]
      rw [e]; exact this
    have h2 : b⁻¹ * q * b ∈ Hzero H f := (hmemP' q).1 hq
    have e : b⁻¹ * (p * q) * b = (b⁻¹ * p * b) * (b⁻¹ * q * b) := by group
    rw [e]
    exact Hw.mul_mem (hwP' h1) (hwP h2)
  have hHwHs : ¬ Hw ≤ H ⊔ T := by
    intro h
    exact hP'ne (c.uniq_E (hwP'.trans h) hP'el hP'card)
  have hKsq : ∀ k ∈ Hw, k * k ∈ Hzero H f := by
    rintro _ ⟨p, hp, q, hq, rfl⟩
    have hq2 := hP'sq q hq
    have h1 := hS0n q (hP'S0 hq) p hp
    have e : p * q * (p * q) = p * (q * p * q⁻¹) * (q * q) := by group
    rw [e, hq2, mul_one]
    exact (Hzero H f).mul_mem hp h1
  have hKc : ∀ k ∈ Hw, ∀ l ∈ Hw, k * l * k⁻¹ * l⁻¹ ∈ Hzero H f := by
    rintro _ ⟨p₁, hp₁, a, ha, rfl⟩ _ ⟨p₂, hp₂, c', hc', rfl⟩
    have hu : p₁ * (a * p₂ * a⁻¹) ∈ Hzero H f :=
      (Hzero H f).mul_mem hp₁ (hS0n a (hP'S0 ha) p₂ hp₂)
    have hv : p₂ * (c' * p₁ * c'⁻¹) ∈ Hzero H f :=
      (Hzero H f).mul_mem hp₂ (hS0n c' (hP'S0 hc') p₁ hp₁)
    have hkl : (p₁ * a) * (p₂ * c') = (p₁ * (a * p₂ * a⁻¹)) * (a * c') := by group
    have hlk : (p₂ * c') * (p₁ * a) = (p₂ * (c' * p₁ * c'⁻¹)) * (c' * a) := by group
    have hac : a * c' = c' * a := hP'comm a ha c' hc'
    have e : (p₁ * a) * (p₂ * c') * (p₁ * a)⁻¹ * (p₂ * c')⁻¹ =
        ((p₁ * a) * (p₂ * c')) * ((p₂ * c') * (p₁ * a))⁻¹ := by group
    rw [e, hkl, hlk, hac]
    have e2 : (p₁ * (a * p₂ * a⁻¹)) * (c' * a) * ((p₂ * (c' * p₁ * c'⁻¹)) * (c' * a))⁻¹ =
        (p₁ * (a * p₂ * a⁻¹)) * (p₂ * (c' * p₁ * c'⁻¹))⁻¹ := by group
    rw [e2]
    exact (Hzero H f).mul_mem hu ((Hzero H f).inv_mem hv)
  have hKz : ∃ k ∈ Hw, x * k * x⁻¹ * k⁻¹ ∉ Hzero H f := by
    obtain ⟨k, hk, hkH⟩ := IsConcreteLE.not_le_iff_exists.1 hHwHs
    refine ⟨k, hk, fun h => hkH ?_⟩
    rw [← c.cenMod_S0_eq h10]
    exact ⟨hwS0 hk, h⟩
  have hxx : x * x ∈ Hzero H f := by rw [hP.x_sq]; exact one_mem _
  obtain ⟨hxHw, hHwcard, hdich, hcen2⟩ := ambient_klein hn0 c.S0_two c.x_mem_S0 hxx
    hP.x_notin_H0 (c.cenMod_card_le h10) hwS0 hwP hwn hKsq hKc hKz
  have hxN : x ∈ normalizer (Hw : Set G) :=
    mem_normalizer_of_involution hP.x_sq (hwn x c.x_mem_S0)
  have hfree0 : FreeSec2 x ⊥ (Hzero H f) := c.isFree_x.freeSec c.c2
  have hfree1 : FreeSec2 x (Hzero H f) Hw := by
    refine ⟨hwP, ?_, hKsq, fun g hg => hP.H0_norm_H x hP.x_mem_H g hg,
      fun g hg => hwn x c.x_mem_S0 g hg, ?_⟩
    · intro a ha b' hb'
      exact hKc a ha b' hb'
    · have hF : Nat.card (fixSec x (Hzero H f) Hw) =
          Nat.card (cenMod Hw (Hzero H f) x (fun k hk n hn => hn0.norm k (hwS0 hk) n hn)) :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun g => Iff.rfl))
      rw [hF, hcen2, hHwcard]
      ring
  have hconj := h10 G Hw x 2 (fun i => if i = 0 then ⊥ else if i = 1 then Hzero H f else Hw)
    hP.x_sq hxN hxHw (by simp) (by simp) (by
      intro i hi
      interval_cases i
      · simpa using hfree0
      · simpa using hfree1)
  have hxb : x * b * x⁻¹ * b⁻¹ ∈ Hw := by
    have he : b * x * b⁻¹ ∈ S0 S (Hzero H f) := (hbN x).1 c.x_mem_S0
    rcases hdich _ he with h | h
    · exfalso
      apply hxHw
      have := hbw' _ h
      have e : b⁻¹ * (b * x * b⁻¹) * b = x := by group
      rwa [e] at this
    · have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hP.x_sq
      have hxe := hwn x c.x_mem_S0 _ h
      have e : x * b * x⁻¹ * b⁻¹ = x * ((b * x * b⁻¹) * x) * x⁻¹ := by
        calc x * b * x⁻¹ * b⁻¹ = x * b * x * b⁻¹ := by rw [hxi]
          _ = x * ((b * x * b⁻¹) * x) * x⁻¹ := by group
      rw [e]
      exact hxe
  obtain ⟨k, hkHw, hk⟩ := lift_cent hP.x_sq (fun n hn => hwn x c.x_mem_S0 n hn) hconj hxb
  have hkS : k * b ∈ S := S.mul_mem (mem_S0.1 (hwS0 hkHw)).1 hbS
  have hkC : k * b ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    calc x * (k * b) = (x * (k * b) * x⁻¹) * x := by group
      _ = (k * b) * x := by rw [hk]
  have hkT : k * b ∈ T := by
    rw [c.T_eq_cent]
    exact ⟨hkS, hkC⟩
  apply hbS0
  have : b = k⁻¹ * (k * b) := by group
  rw [this]
  exact (S0 S (Hzero H f)).mul_mem ((S0 S (Hzero H f)).inv_mem (hwS0 hkHw)) (c.T_le_S0 hkT)

end Ctx2S

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
