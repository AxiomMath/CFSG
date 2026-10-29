module

public import CFSG.ClassicalInvolution.Q3.Sec13End15A
import CFSG.ClassicalInvolution.Q3.Sec13EndS3E8

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

private theorem e15d1_z_mem (s : TwinSit Ω K K' z) : z ∈ zGroup Ω :=
  Subgroup.subset_closure ⟨K, s.mem, s.isInv⟩

private theorem e15d1_conj_mem_twinSet (h : EndHyp Ω) (s : TwinSit Ω K K' z) {r : G}
    (hr : r * z = z * r) {L : Subgroup G} (hL : L ∈ Ω) (hLz : IsUniqueInvolution L z) :
    conjSub r L ∈ twinSet Ω K := by
  have hz' : r * z * r⁻¹ = z := by rw [hr, mul_inv_cancel_right]
  have hinv := hLz.conj r
  rw [hz'] at hinv
  exact ⟨h.thmD.hyp.conjInvariant r L hL, z, s.isInv, hinv⟩

theorem conjSub_mem_twinSet_of_mem_zGroup (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    {d : G} (hd : d ∈ zGroup Ω) : conjSub d K ∈ twinSet Ω K :=
  e15d1_conj_mem_twinSet h s (h.zGroup_comm h9 d hd z (e15d1_z_mem s)) s.mem s.isInv

theorem exists_mem_zGroup_swap (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) : ∃ d ∈ zGroup Ω, conjSub d K = K' := by
  by_contra hcon
  push Not at hcon
  have hnorm : ∀ d ∈ zGroup Ω, d ∈ Subgroup.normalizer (K : Set G) := by
    intro d hd
    rw [mem_normalizer_iff_conjSub_eq]
    have hc := h.conjSub_mem_twinSet_of_mem_zGroup h9 s hd
    rw [s.twin] at hc
    rcases Set.mem_insert_iff.mp hc with h1 | h1
    · exact h1
    · exact absurd (Set.mem_singleton_iff.mp h1) (hcon d hd)
  have hle : zGroup Ω ≤ eGroup Ω K := by
    unfold zGroup
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨M, hM, hu⟩
    exact h.mem_eGroup_of_normalizes h9 s.mem hM hu
      (hnorm u (Subgroup.subset_closure ⟨M, hM, hu⟩))
  exact h13 (le_antisymm hle (h.eGroup_le_zGroup s.mem))

theorem natCard_zGroup_eq_two_mul (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) :
    Nat.card (zGroup Ω) = 2 * Nat.card ↥(zGroup Ω ⊓ Subgroup.normalizer (K : Set G)) := by
  obtain ⟨d₀, hd₀, hsw⟩ := h.exists_mem_zGroup_swap h9 s h13
  have hrel : (Subgroup.normalizer (K : Set G)).relIndex (zGroup Ω) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨d₀, hd₀, fun b hb => ?_⟩
    have hbb : b * b = 1 := h.zGroup_mul_self h9 b hb
    have hc := h.conjSub_mem_twinSet_of_mem_zGroup h9 s hb
    rw [s.twin] at hc
    have hN1 : b ∈ Subgroup.normalizer (K : Set G) ↔ conjSub b K = K :=
      mem_normalizer_iff_conjSub_eq
    have hN2 : b * d₀ ∈ Subgroup.normalizer (K : Set G) ↔ conjSub b K' = K := by
      rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, hsw]
    rw [hN1, hN2]
    rcases Set.mem_insert_iff.mp hc with h1 | h1
    · rw [h1]
      have hne : conjSub b K' ≠ K := fun h2 => s.ne (conjSub_injective b (h1.trans h2.symm))
      simp [Xor, hne]
    · have h1' : conjSub b K = K' := Set.mem_singleton_iff.mp h1
      have h2 : conjSub b K' = K := by
        rw [← h1', ← conjSub_mul, hbb, conjSub_one]
      rw [h2, h1']
      simp [Xor, s.ne.symm]
  have hcard := Subgroup.relIndex_mul_card (H := Subgroup.normalizer (K : Set G))
    (K := zGroup Ω)
  rw [hrel, inf_comm] at hcard
  exact hcard.symm

theorem commutator_mem_sup_twin (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z) {d k : G}
    (hd : d ∈ zGroup Ω) (hk : k ∈ K) : d * k * d⁻¹ * k⁻¹ ∈ zGroup Ω ⊓ (K ⊔ K') := by
  have hN := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hdk : d * k * d⁻¹ ∈ K ⊔ K' := by
    have hmem : d * k * d⁻¹ ∈ conjSub d K := conj_mem_conjSub hk
    have hc := h.conjSub_mem_twinSet_of_mem_zGroup h9 s hd
    rw [s.twin] at hc
    rcases Set.mem_insert_iff.mp hc with h1 | h1
    · rw [h1] at hmem
      exact Subgroup.mem_sup_left hmem
    · rw [Set.mem_singleton_iff.mp h1] at hmem
      exact Subgroup.mem_sup_right hmem
  refine Subgroup.mem_inf.mpr
    ⟨?_, (K ⊔ K').mul_mem hdk ((K ⊔ K').inv_mem (Subgroup.mem_sup_left hk))⟩
  have e : d * k * d⁻¹ * k⁻¹ = d * (k * d⁻¹ * k⁻¹) := by group
  rw [e]
  exact (zGroup Ω).mul_mem hd (hN.conj_mem d⁻¹ ((zGroup Ω).inv_mem hd) k)

theorem commutator_mem_zpowers_of_mem_normalizer (h : EndHyp Ω) (h9 : Perp9 Ω)
    (s : TwinSit Ω K K' z) {d k : G} (hd : d ∈ zGroup Ω)
    (hdN : d ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K) :
    d * k * d⁻¹ * k⁻¹ ∈ Subgroup.zpowers z := by
  have htD : d * k * d⁻¹ * k⁻¹ ∈ zGroup Ω :=
    (Subgroup.mem_inf.mp (h.commutator_mem_sup_twin h9 s hd hk)).1
  have hdk : d * k * d⁻¹ ∈ K := by
    have h1 : conjSub d K = K := mem_normalizer_iff_conjSub_eq.mp hdN
    have h2 := conj_mem_conjSub (n := d) hk
    rwa [h1] at h2
  have htK : d * k * d⁻¹ * k⁻¹ ∈ K := K.mul_mem hdk (K.inv_mem hk)
  rcases s.isInv.unique _ htK (h.zGroup_mul_self h9 _ htD) with h2 | h2
  · rw [h2]; exact Subgroup.one_mem _
  · rw [h2]; exact Subgroup.mem_zpowers z

theorem swap_commutator (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z) {d₀ : G}
    (hd₀ : d₀ ∈ zGroup Ω) (hsw : conjSub d₀ K = K') {k : G} (hk : k ∈ K) :
    d₀ * k * d₀⁻¹ * k⁻¹ ∈ zGroup Ω ⊓ Subgroup.normalizer (K : Set G) ∧
      ∀ k₁ ∈ K, (d₀ * k * d₀⁻¹ * k⁻¹) * k₁ * (d₀ * k * d₀⁻¹ * k⁻¹)⁻¹ * k₁⁻¹ =
        k⁻¹ * k₁ * k * k₁⁻¹ := by
  have hk' : d₀ * k * d₀⁻¹ ∈ K' := by
    rw [← hsw]; exact conj_mem_conjSub hk
  obtain ⟨b, hb⟩ : ∃ b : G, b = d₀ * k * d₀⁻¹ * k⁻¹ := ⟨_, rfl⟩
  rw [← hb]
  have hbD : b ∈ zGroup Ω := by
    rw [hb]; exact (Subgroup.mem_inf.mp (h.commutator_mem_sup_twin h9 s hd₀ hk)).1
  have hbb : b * b = 1 := h.zGroup_mul_self h9 b hbD
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hkey : ∀ k₁ ∈ K, b * k₁ * b⁻¹ = k⁻¹ * k₁ * k := by
    intro k₁ hk₁
    have hx : k⁻¹ * k₁ * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk) hk₁) hk
    have hc := s.commutes h _ hx _ hk'
    rw [hb]
    calc d₀ * k * d₀⁻¹ * k⁻¹ * k₁ * (d₀ * k * d₀⁻¹ * k⁻¹)⁻¹
        = (d₀ * k * d₀⁻¹) * (k⁻¹ * k₁ * k) * (d₀ * k * d₀⁻¹)⁻¹ := by group
      _ = (k⁻¹ * k₁ * k) * (d₀ * k * d₀⁻¹) * (d₀ * k * d₀⁻¹)⁻¹ := by rw [← hc]
      _ = k⁻¹ * k₁ * k := by group
  refine ⟨Subgroup.mem_inf.mpr ⟨hbD, ?_⟩, fun k₁ hk₁ => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hkey x hx]
      exact K.mul_mem (K.mul_mem (K.inv_mem hk) hx) hk
    · intro hy
      have hxx : x = b * (b * x * b⁻¹) * b⁻¹ := by
        rw [hbi]
        calc x = (b * b) * x * (b * b) := by rw [hbb]; group
          _ = b * (b * x * b) * b := by group
      have h3 : x = k⁻¹ * (b * x * b⁻¹) * k := hxx.trans (hkey _ hy)
      rw [h3]
      exact K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk
  · rw [hkey k₁ hk₁]

private theorem e15d1_center_le (h : EndHyp Ω) {L : Subgroup G} (hL : L ∈ Ω) {u : G}
    (hu : IsUniqueInvolution L u) {c : G} (hc : c ∈ L) (hcc : ∀ y ∈ L, c * y = y * c) :
    c ∈ Subgroup.zpowers u := by
  have hq : IsQuatSub L :=
    Sec6Gen.isQuatSub_of_mem_RSet h.thmD.hyp (TC.mem_RSet_of_isPGroup hL (h.thmD.two L hL))
  rcases hu.unique c hc (IsQuatSub.sq_eq_one_of_central hq hc hcc) with h1 | h1
  · rw [h1]; exact Subgroup.one_mem _
  · rw [h1]; exact Subgroup.mem_zpowers u

theorem inf_centralizer_zGroup_eq_zpowers (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) :
    K ⊓ Subgroup.centralizer (zGroup Ω : Set G) = Subgroup.zpowers z := by
  obtain ⟨d₀, hd₀, hsw⟩ := h.exists_mem_zGroup_swap h9 s h13
  apply le_antisymm
  · intro k hk
    obtain ⟨hkK, hkC⟩ := Subgroup.mem_inf.mp hk
    have hcK : ∀ k₁ ∈ K, k * k₁ = k₁ * k := by
      intro k₁ hk₁
      have hbD : d₀ * k₁ * d₀⁻¹ * k₁⁻¹ ∈ zGroup Ω :=
        (Subgroup.mem_inf.mp (h.commutator_mem_sup_twin h9 s hd₀ hk₁)).1
      have hbk : (d₀ * k₁ * d₀⁻¹ * k₁⁻¹) * k = k * (d₀ * k₁ * d₀⁻¹ * k₁⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hkC) _ hbD
      have h6 := (h.swap_commutator h9 s hd₀ hsw hk₁).2 k hkK
      have h7 : (d₀ * k₁ * d₀⁻¹ * k₁⁻¹) * k * (d₀ * k₁ * d₀⁻¹ * k₁⁻¹)⁻¹ * k⁻¹ = 1 := by
        rw [hbk]; group
      have h8 : k₁⁻¹ * k * k₁ * k⁻¹ = 1 := h6.symm.trans h7
      have h8' : k₁⁻¹ * k * k₁ = k := mul_inv_eq_one.mp h8
      calc k * k₁ = k₁ * (k₁⁻¹ * k * k₁) := by group
        _ = k₁ * k := by rw [h8']
    exact e15d1_center_le h s.mem s.isInv hkK hcK
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨s.isInv.mem, Subgroup.mem_centralizer_iff.mpr
      fun d hd => h.zGroup_comm h9 d hd z (e15d1_z_mem s)⟩

theorem inf_centralizer_twin_eq (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) :
    zGroup Ω ⊓ Subgroup.centralizer (K' : Set G) = zGroup Ω ⊓ Subgroup.centralizer (K : Set G) := by
  obtain ⟨d₀, hd₀, hsw⟩ := h.exists_mem_zGroup_swap h9 s h13
  have key : ∀ d ∈ zGroup Ω, ∀ L : Subgroup G,
      d ∈ Subgroup.centralizer (conjSub d₀ L : Set G) ↔ d ∈ Subgroup.centralizer (L : Set G) := by
    intro d hd L
    have hc : d₀ * d = d * d₀ := h.zGroup_comm h9 d₀ hd₀ d hd
    have e1 : d₀⁻¹ * d * d₀ = d := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hcL x hx
      have h1 := hcL _ (conj_mem_conjSub hx)
      calc x * d = x * (d₀⁻¹ * d * d₀) := by rw [e1]
        _ = d₀⁻¹ * ((d₀ * x * d₀⁻¹) * d) * d₀ := by group
        _ = d₀⁻¹ * (d * (d₀ * x * d₀⁻¹)) * d₀ := by rw [h1]
        _ = (d₀⁻¹ * d * d₀) * x := by group
        _ = d * x := by rw [e1]
    · intro hcK y hy
      have hy' := mem_conjSub_iff.mp hy
      have h1 := hcK _ hy'
      have e2 : d₀ * d * d₀⁻¹ = d := by rw [hc, mul_inv_cancel_right]
      calc y * d = y * (d₀ * d * d₀⁻¹) := by rw [e2]
        _ = d₀ * ((d₀⁻¹ * y * d₀) * d) * d₀⁻¹ := by group
        _ = d₀ * (d * (d₀⁻¹ * y * d₀)) * d₀⁻¹ := by rw [h1]
        _ = (d₀ * d) * (d₀⁻¹ * y * d₀) * d₀⁻¹ := by group
        _ = (d * d₀) * (d₀⁻¹ * y * d₀) * d₀⁻¹ := by rw [hc]
        _ = d * y := by group
  rw [← hsw]
  ext d
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr_right fun hd => key d hd K

private theorem e15d2_zpowers_one_or {z x : G} (hz2 : z * z = 1)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · left
    rw [hm, zpow_mul, zpow_two, hz2, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]

private theorem e15d2_comm_of_one_or {z x y : G} (hx : x = 1 ∨ x = z)
    (hy : y = 1 ∨ y = z) : x * y = y * x := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

private theorem e15d2_q8_rel {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    z * i = i * z ∧ z * j = j * z ∧ j * (z * i) = i * j ∧ i⁻¹ * j * i * j⁻¹ = z ∧
      j⁻¹ * i * j * i⁻¹ = z := by
  have hzi : z * i = i * z := by
    rw [← hQ.sq_i]
    group
  have hzj : z * j = j * z := by
    rw [← hQ.sq_j]
    group
  have h2 : j * (z * i) = i * j := by
    calc j * (z * i) = j * z * i := by group
      _ = j * (j * j) * i := by rw [hQ.sq_j]
      _ = (j * j) * (j * i) := by group
      _ = z * (z * (i * j)) := by rw [hQ.sq_j, hQ.comm]
      _ = (z * z) * (i * j) := by group
      _ = i * j := by rw [hQ.inv.sq, one_mul]
  have hzi' : i⁻¹ * z * i = z := by
    rw [← hQ.sq_i]
    group
  have h3 : i⁻¹ * j * i * j⁻¹ = z := by
    calc i⁻¹ * j * i * j⁻¹ = i⁻¹ * (j * i) * j⁻¹ := by group
      _ = i⁻¹ * (z * (i * j)) * j⁻¹ := by rw [hQ.comm]
      _ = (i⁻¹ * z * i) * j * j⁻¹ := by group
      _ = z := by rw [hzi']; group
  have h4 : j⁻¹ * i * j * i⁻¹ = z := by
    calc j⁻¹ * i * j * i⁻¹ = j⁻¹ * (i * j) * i⁻¹ := by group
      _ = j⁻¹ * (j * (z * i)) * i⁻¹ := by rw [h2]
      _ = z := by group
  exact ⟨hzi, hzj, h2, h3, h4⟩

private theorem e15d2_center {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) {x : G}
    (hx : x ∈ K) (hc : ∀ y ∈ K, y * x = x * y) : x = 1 ∨ x = z := by
  obtain ⟨hzi, -, h2, -, -⟩ := e15d2_q8_rel hQ
  have hzz := hQ.inv.sq
  have hnot : ∀ w : G, z * w = w → False := fun w hw =>
    hQ.inv.ne_one (mul_right_cancel (hw.trans (one_mul w).symm))
  have e3 : i * (i * j) = z * j := by
    rw [← mul_assoc, hQ.sq_i]
  have h5 : i * j * i = j := by
    calc i * j * i = i * (j * i) := by group
      _ = i * (z * (i * j)) := by rw [hQ.comm]
      _ = z * (i * (i * j)) := by rw [← mul_assoc, ← hzi, mul_assoc]
      _ = z * (z * j) := by rw [e3]
      _ = j := by rw [← mul_assoc, hzz, one_mul]
  have e4 : i * (z * (i * j)) = z * (z * j) := by
    rw [← mul_assoc, ← hzi, mul_assoc, e3]
  have e5 : z * (i * j) * i = z * j := by
    rw [mul_assoc, h5]
  have e6a : i * (z * j) = z * (i * j) := by
    rw [← mul_assoc i z j, ← hzi, mul_assoc z i j]
  have e6b : z * j * i = i * j := by
    rw [mul_assoc z j i, hQ.comm, ← mul_assoc z z (i * j), hzz, one_mul]
  rcases hQ.nf x hx with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    have h6 := hc j hQ.mem_j
    rw [h1, hQ.comm] at h6
    exact hnot _ h6
  · exfalso
    have h6 := hc j hQ.mem_j
    rw [h1, h2, mul_assoc z i j] at h6
    exact hnot _ h6.symm
  · exfalso
    have h6 := hc i hQ.mem_i
    rw [h1, hQ.comm] at h6
    exact hnot _ h6.symm
  · exfalso
    have h6 := hc i hQ.mem_i
    rw [h1, e6a, e6b] at h6
    exact hnot _ h6
  · exfalso
    have h6 := hc i hQ.mem_i
    rw [h1, h5, e3] at h6
    exact hnot _ h6
  · exfalso
    have h6 := hc i hQ.mem_i
    rw [h1, e4, e5] at h6
    have h7 : z * j = j := by
      calc z * j = z * (z * j) := h6.symm
        _ = (z * z) * j := by group
        _ = j := by rw [hzz, one_mul]
    exact hnot _ h7

private theorem e15d2_commute_of_gens {K : Subgroup G} {z i j c : G} (hQ : Q8Data K z i j)
    (hcz : c * z = z * c) (hci : c * i = i * c) (hcj : c * j = j * c) :
    c ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hcz' : Commute c z := hcz
  have hci' : Commute c i := hci
  have hcj' : Commute c j := hcj
  have hcy : Commute c y := by
    rcases hQ.nf y hy with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
    · exact Commute.one_right c
    · exact hcz'
    · exact hci'
    · exact hcz'.mul_right hci'
    · exact hcj'
    · exact hcz'.mul_right hcj'
    · exact hci'.mul_right hcj'
    · exact hcz'.mul_right (hci'.mul_right hcj')
  exact hcy.symm.eq

private theorem e15d2_mem_sup_decomp {K K' : Subgroup G} (hc : Commutes K K') {x : G}
    (hx : x ∈ K ⊔ K') : ∃ k ∈ K, ∃ k' ∈ K', x = k * k' := by
  let P : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ k' ∈ K', x = k * k'}
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, k₁', hk₁', rfl⟩ ⟨k₂, hk₂, k₂', hk₂', rfl⟩
        refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, k₁' * k₂', K'.mul_mem hk₁' hk₂', ?_⟩
        have e := hc k₂ hk₂ k₁' hk₁'
        calc k₁ * k₁' * (k₂ * k₂') = k₁ * (k₁' * k₂) * k₂' := by group
          _ = k₁ * (k₂ * k₁') * k₂' := by rw [← e]
          _ = k₁ * k₂ * (k₁' * k₂') := by group
      one_mem' := ⟨1, K.one_mem, 1, K'.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, hk, k', hk', rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, k'⁻¹, K'.inv_mem hk', ?_⟩
        have e := hc k hk k' hk'
        calc (k * k')⁻¹ = k'⁻¹ * k⁻¹ := by group
          _ = k⁻¹ * k'⁻¹ := by
            have e' : (k' * k)⁻¹ = (k * k')⁻¹ := by rw [e]
            rw [mul_inv_rev, mul_inv_rev] at e'
            exact e'.symm }
  have hle : K ⊔ K' ≤ P := by
    refine sup_le (fun k hk => ⟨k, hk, 1, K'.one_mem, by simp⟩)
      (fun k' hk' => ⟨1, K.one_mem, k', hk', by simp⟩)
  exact hle hx

private theorem e15d2_centralizer_le_normalizer (K : Subgroup G) :
    Subgroup.centralizer (K : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  have hx' := Subgroup.mem_centralizer_iff.mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have e : x * n * x⁻¹ = n := by
      rw [← hx' n hn]
      group
    rw [e]
    exact hn
  · intro hn
    have e3 : x⁻¹ * (x * n * x⁻¹) * x = x * n * x⁻¹ := by
      calc x⁻¹ * (x * n * x⁻¹) * x = x⁻¹ * ((x * n * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * n * x⁻¹)) := by rw [hx' _ hn]
        _ = x * n * x⁻¹ := by group
    have key : n = x * n * x⁻¹ := by
      calc n = x⁻¹ * (x * n * x⁻¹) * x := by group
        _ = x * n * x⁻¹ := e3
    rw [key]
    exact hn

private theorem e15d2_sup_le_normalizer (h : EndHyp Ω) (s : TwinSit Ω K K' z) :
    K ⊔ K' ≤ Subgroup.normalizer (K : Set G) := by
  refine sup_le (fun k hk => Subgroup.le_normalizer hk) (fun k' hk' => ?_)
  apply e15d2_centralizer_le_normalizer K
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact s.commutes h k hk k' hk'

private theorem e15d2_exists_pair (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {i j : G} (hQ : Q8Data K z i j) {p q : G}
    (hp : p = 1 ∨ p = z) (hq : q = 1 ∨ q = z) :
    ∃ d ∈ zGroup Ω ⊓ (K ⊔ K'), dComm d i = p ∧ dComm d j = q := by
  obtain ⟨d₀, hd₀, hsw⟩ := h.exists_mem_zGroup_swap h9 s h13
  obtain ⟨hBi_N, hBi_eq⟩ := h.swap_commutator h9 s hd₀ hsw hQ.mem_i
  obtain ⟨hBj_N, hBj_eq⟩ := h.swap_commutator h9 s hd₀ hsw hQ.mem_j
  have hBi_S := h.commutator_mem_sup_twin h9 s hd₀ hQ.mem_i
  have hBj_S := h.commutator_mem_sup_twin h9 s hd₀ hQ.mem_j
  obtain ⟨-, -, -, hr3, hr4⟩ := e15d2_q8_rel hQ
  have vi_i : dComm (d₀ * i * d₀⁻¹ * i⁻¹) i = 1 := by
    unfold dComm
    rw [hBi_eq i hQ.mem_i]
    group
  have vi_j : dComm (d₀ * i * d₀⁻¹ * i⁻¹) j = z := by
    unfold dComm
    rw [hBi_eq j hQ.mem_j]
    exact hr3
  have vj_i : dComm (d₀ * j * d₀⁻¹ * j⁻¹) i = z := by
    unfold dComm
    rw [hBj_eq i hQ.mem_i]
    exact hr4
  have vj_j : dComm (d₀ * j * d₀⁻¹ * j⁻¹) j = 1 := by
    unfold dComm
    rw [hBj_eq j hQ.mem_j]
    group
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · refine ⟨1, one_mem _, ?_, ?_⟩
    · rw [hp]
      simp [dComm]
    · rw [hq]
      simp [dComm]
  · refine ⟨d₀ * i * d₀⁻¹ * i⁻¹, hBi_S, ?_, ?_⟩
    · rw [hp, vi_i]
    · rw [hq, vi_j]
  · refine ⟨d₀ * j * d₀⁻¹ * j⁻¹, hBj_S, ?_, ?_⟩
    · rw [hp, vj_i]
    · rw [hq, vj_j]
  · refine ⟨(d₀ * j * d₀⁻¹ * j⁻¹) * (d₀ * i * d₀⁻¹ * i⁻¹), mul_mem hBj_S hBi_S, ?_, ?_⟩
    · rw [dComm_mul_left hQ.inv (Subgroup.mem_inf.mp hBj_N).2 (Or.inl vi_i), vi_i, vj_i, hp,
        one_mul]
    · rw [dComm_mul_left hQ.inv (Subgroup.mem_inf.mp hBj_N).2 (Or.inr vi_j), vi_j, vj_j, hq,
        mul_one]

private theorem e15d2_card_eq_four_mul (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    {i j : G} (hQ : Q8Data K z i j) {S : Subgroup G} (hSD : S ≤ zGroup Ω)
    (hSN : S ≤ Subgroup.normalizer (K : Set G))
    (hsurj : ∀ p q : G, (p = 1 ∨ p = z) → (q = 1 ∨ q = z) →
      ∃ d ∈ S, dComm d i = p ∧ dComm d j = q) :
    Nat.card ↥S = 4 * Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set G)) := by
  have hzz := hQ.inv.sq
  have hz1 := hQ.inv.ne_one
  have hpi : ∀ d ∈ S, dComm d i ∈ Subgroup.zpowers z := fun d hd =>
    h.commutator_mem_zpowers_of_mem_normalizer h9 s (hSD hd) (hSN hd) hQ.mem_i
  have hpj : ∀ d ∈ S, dComm d j ∈ Subgroup.zpowers z := fun d hd =>
    h.commutator_mem_zpowers_of_mem_normalizer h9 s (hSD hd) (hSN hd) hQ.mem_j
  have hmul_i : ∀ a b : S, dComm ((a * b : S) : G) i = dComm (a : G) i * dComm (b : G) i := by
    intro a b
    rw [Subgroup.coe_mul, dComm_mul_left hQ.inv (hSN a.2)
      (e15d2_zpowers_one_or hzz (hpi b b.2))]
    exact (e15d2_comm_of_one_or (e15d2_zpowers_one_or hzz (hpi a a.2))
      (e15d2_zpowers_one_or hzz (hpi b b.2))).symm
  have hmul_j : ∀ a b : S, dComm ((a * b : S) : G) j = dComm (a : G) j * dComm (b : G) j := by
    intro a b
    rw [Subgroup.coe_mul, dComm_mul_left hQ.inv (hSN a.2)
      (e15d2_zpowers_one_or hzz (hpj b b.2))]
    exact (e15d2_comm_of_one_or (e15d2_zpowers_one_or hzz (hpj a a.2))
      (e15d2_zpowers_one_or hzz (hpj b b.2))).symm
  let f₁ : S →* Subgroup.zpowers z :=
    MonoidHom.mk' (fun d => ⟨dComm (d : G) i, hpi d d.2⟩) (fun a b => Subtype.ext (hmul_i a b))
  let f₂ : S →* Subgroup.zpowers z :=
    MonoidHom.mk' (fun d => ⟨dComm (d : G) j, hpj d d.2⟩) (fun a b => Subtype.ext (hmul_j a b))
  let φ : S →* Subgroup.zpowers z × Subgroup.zpowers z := f₁.prod f₂
  have hφ : ∀ d : S, φ d = 1 ↔ dComm (d : G) i = 1 ∧ dComm (d : G) j = 1 := by
    intro d
    constructor
    · intro hd
      exact ⟨congrArg (fun x => ((x.1 : Subgroup.zpowers z) : G)) hd,
        congrArg (fun x => ((x.2 : Subgroup.zpowers z) : G)) hd⟩
    · rintro ⟨h1, h2⟩
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hker : φ.ker = (S ⊓ Subgroup.centralizer (K : Set G)).subgroupOf S := by
    ext d
    rw [MonoidHom.mem_ker, hφ, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨d.2, ?_⟩
      have hc : ∀ k ∈ K, dComm (d : G) k = 1 ∨ dComm (d : G) k = z := fun k hk =>
        e15d2_zpowers_one_or hzz
          (h.commutator_mem_zpowers_of_mem_normalizer h9 s (hSD d.2) (hSN d.2) hk)
      have hall : ∀ k ∈ K, dComm (d : G) k = 1 := fun k hk =>
        dComm_eq_one_of_gens hQ (hSN d.2) hc h1 h2 hk
      exact Subgroup.mem_centralizer_iff.mpr (fun k hk =>
        (dComm_eq_one_iff.mp (hall k hk)).symm)
    · rintro ⟨-, hC⟩
      exact ⟨dComm_eq_one_iff.mpr (Subgroup.mem_centralizer_iff.mp hC i hQ.mem_i).symm,
        dComm_eq_one_iff.mpr (Subgroup.mem_centralizer_iff.mp hC j hQ.mem_j).symm⟩
  have hcard_ker : Nat.card ↥φ.ker = Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hsurjφ : Function.Surjective φ := by
    rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    obtain ⟨d, hd, e1, e2⟩ :=
      hsurj p q (e15d2_zpowers_one_or hzz hp) (e15d2_zpowers_one_or hzz hq)
    exact ⟨⟨d, hd⟩, Prod.ext (Subtype.ext e1) (Subtype.ext e2)⟩
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hsurjφ
  have hidx := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, Subgroup.card_top, card_zpowers_prod_eq_four hzz hz1,
    hcard_ker] at hidx
  rw [← hidx]
  ring

private theorem e15d2_natCard_normalizer (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) :
    Nat.card ↥(zGroup Ω ⊓ Subgroup.normalizer (K : Set G)) =
      4 * Nat.card ↥(zGroup Ω ⊓ Subgroup.centralizer (K : Set G)) := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen s.isInv (h.isQuatSub_of_mem s.mem) (h.card_eq_eight s.mem)
  have hQ : Q8Data K z i j := ⟨s.isInv, hi, hj, hii, hjj, hji, hNF⟩
  have hsup := e15d2_sup_le_normalizer h s
  have hS := e15d2_card_eq_four_mul h h9 s hQ (S := zGroup Ω ⊓ Subgroup.normalizer (K : Set G))
    inf_le_left inf_le_right (fun p q hp hq => by
      obtain ⟨d, hd, e1, e2⟩ := e15d2_exists_pair h h9 s h13 hQ hp hq
      exact ⟨d, ⟨(Subgroup.mem_inf.mp hd).1, hsup (Subgroup.mem_inf.mp hd).2⟩, e1, e2⟩)
  have hC : zGroup Ω ⊓ Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer (K : Set G)
      = zGroup Ω ⊓ Subgroup.centralizer (K : Set G) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, hx.2⟩
    · intro hx
      exact ⟨⟨hx.1, e15d2_centralizer_le_normalizer K hx.2⟩, hx.2⟩
  rw [hS, hC]

theorem natCard_zGroup_eq_eight_mul (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) :
    Nat.card (zGroup Ω) = 8 * Nat.card ↥(zGroup Ω ⊓ Subgroup.centralizer (K : Set G)) := by
  rw [h.natCard_zGroup_eq_two_mul h9 s h13, e15d2_natCard_normalizer h h9 s h13]
  ring

theorem natCard_zGroup_inf_sup_twin (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) : Nat.card ↥(zGroup Ω ⊓ (K ⊔ K')) = 8 := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen s.isInv (h.isQuatSub_of_mem s.mem) (h.card_eq_eight s.mem)
  have hQ : Q8Data K z i j := ⟨s.isInv, hi, hj, hii, hjj, hji, hNF⟩
  obtain ⟨hzi, hzj, -, -, -⟩ := e15d2_q8_rel hQ
  have hzz := hQ.inv.sq
  have hz1 := hQ.inv.ne_one
  have hsup := e15d2_sup_le_normalizer h s
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, s.mem, s.isInv⟩
  have hS := e15d2_card_eq_four_mul h h9 s hQ (S := zGroup Ω ⊓ (K ⊔ K')) inf_le_left
    (le_trans inf_le_right hsup) (fun p q hp hq => e15d2_exists_pair h h9 s h13 hQ hp hq)
  have hz_mem : z ∈ zGroup Ω ⊓ (K ⊔ K') ⊓ Subgroup.centralizer (K : Set G) :=
    ⟨⟨hzD, (le_sup_left : K ≤ K ⊔ K') s.isInv.mem⟩, e15d2_commute_of_gens hQ rfl hzi hzj⟩
  have hT : zGroup Ω ⊓ (K ⊔ K') ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨hxD, hxS⟩, hxC⟩ := hx
      obtain ⟨k, hk, k', hk', rfl⟩ := e15d2_mem_sup_decomp (s.commutes h) hxS
      have hk'C : k' ∈ Subgroup.centralizer (K : Set G) :=
        Subgroup.mem_centralizer_iff.mpr (fun y hy => s.commutes h y hy k' hk')
      have hkC : k ∈ Subgroup.centralizer (K : Set G) := by
        have := Subgroup.mul_mem _ hxC (Subgroup.inv_mem _ hk'C)
        simpa using this
      have hk1 : k = 1 ∨ k = z :=
        e15d2_center hQ hk (fun y hy => Subgroup.mem_centralizer_iff.mp hkC y hy)
      have hkD : k ∈ zGroup Ω := by
        rcases hk1 with h1 | h1 <;> rw [h1]
        · exact one_mem _
        · exact hzD
      have hk'D : k' ∈ zGroup Ω := by
        have := mul_mem (inv_mem hkD) hxD
        simpa using this
      have hk'sq : k' * k' = 1 := h.zGroup_mul_self h9 k' hk'D
      have hk'1 : k' = 1 ∨ k' = z := s.mem_twin.2.unique k' hk' hk'sq
      have hkzp : k ∈ Subgroup.zpowers z := by
        rcases hk1 with h1 | h1 <;> rw [h1]
        · exact one_mem _
        · exact Subgroup.mem_zpowers z
      have hk'zp : k' ∈ Subgroup.zpowers z := by
        rcases hk'1 with h1 | h1 <;> rw [h1]
        · exact one_mem _
        · exact Subgroup.mem_zpowers z
      exact mul_mem hkzp hk'zp
    · exact Subgroup.zpowers_le.mpr hz_mem
  rw [hS, hT, card_zpowers_of_involution hzz hz1]

private theorem e15d1_odd_centralizes (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    {d₀ : G} (hd₀ : d₀ ∈ zGroup Ω) (hsw : conjSub d₀ K = K') {r : G}
    (hr : r ∈ Subgroup.centralizer (zGroup Ω : Set G)) (hodd : Odd (orderOf r)) :
    r ∈ Subgroup.centralizer (K : Set G) := by
  have hzD : z ∈ zGroup Ω := e15d1_z_mem s
  have hrD : ∀ d ∈ zGroup Ω, r * d = d * r := fun d hd =>
    ((Subgroup.mem_centralizer_iff.mp hr) d hd).symm
  have hrz : r * z = z * r := hrD z hzD
  obtain ⟨m, hm⟩ := hodd
  have hpow : r = (r * r) ^ (m + 1) := by
    have h1 : r ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one r
    have h2 : (r * r) ^ (m + 1) = r ^ (2 * m + 2) := by
      rw [← sq, ← pow_mul, show 2 * (m + 1) = 2 * m + 2 by ring]
    rw [h2, show 2 * m + 2 = (2 * m + 1) + 1 by ring, pow_succ, h1, one_mul]
  have hrK : conjSub r K = K := by
    have hK1 : conjSub r K ∈ twinSet Ω K := e15d1_conj_mem_twinSet h s hrz s.mem s.isInv
    have hK2 : conjSub r K' ∈ twinSet Ω K :=
      e15d1_conj_mem_twinSet h s hrz s.mem_twin.1 s.mem_twin.2
    rw [s.twin] at hK1 hK2
    rcases Set.mem_insert_iff.mp hK1 with h1 | h1
    · exact h1
    exfalso
    have h1' : conjSub r K = K' := Set.mem_singleton_iff.mp h1
    have h2 : conjSub r K' = K := by
      rcases Set.mem_insert_iff.mp hK2 with h2 | h2
      · exact h2
      · exfalso
        have h3 : conjSub r K' = conjSub r K := by
          rw [Set.mem_singleton_iff.mp h2, h1']
        exact s.ne ((conjSub_injective r) h3).symm
    have hrr : conjSub (r * r) K = K := by rw [conjSub_mul, h1', h2]
    have hall : ∀ j : ℕ, conjSub ((r * r) ^ j) K = K := by
      intro j
      induction j with
      | zero => rw [pow_zero, conjSub_one]
      | succ j ih => rw [pow_succ, conjSub_mul, hrr, ih]
    have hfin := hall (m + 1)
    rw [← hpow, h1'] at hfin
    exact s.ne hfin.symm
  have hKz : ∀ k₁ ∈ K, r * k₁ * r⁻¹ ∈ K := fun k₁ hk₁ => by
    have h1 := conj_mem_conjSub (n := r) hk₁
    rwa [hrK] at h1
  have hcen : ∀ k₁ ∈ K, k₁⁻¹ * (r * k₁ * r⁻¹) ∈ Subgroup.zpowers z := by
    intro k₁ hk₁
    have hk₁' : r * k₁ * r⁻¹ ∈ K := hKz k₁ hk₁
    have hE4 : ∀ w ∈ K, (r * k₁ * r⁻¹) * w * (r * k₁ * r⁻¹)⁻¹ = k₁ * w * k₁⁻¹ := by
      intro w hw
      obtain ⟨b, hb⟩ : ∃ b : G, b = d₀ * w * d₀⁻¹ * w⁻¹ := ⟨_, rfl⟩
      obtain ⟨hbDN, hcomm⟩ := h.swap_commutator h9 s hd₀ hsw hw
      rw [← hb] at hbDN hcomm
      have hbD : b ∈ zGroup Ω := (Subgroup.mem_inf.mp hbDN).1
      have hbN : b ∈ Subgroup.normalizer (K : Set G) := (Subgroup.mem_inf.mp hbDN).2
      have htz : b * k₁ * b⁻¹ * k₁⁻¹ ∈ Subgroup.zpowers z :=
        h.commutator_mem_zpowers_of_mem_normalizer h9 s hbD hbN hk₁
      have htD : b * k₁ * b⁻¹ * k₁⁻¹ ∈ zGroup Ω := (Subgroup.zpowers_le.mpr hzD) htz
      have hrb : r * b * r⁻¹ = b := by rw [hrD b hbD, mul_inv_cancel_right]
      have hrbi : r * b⁻¹ * r⁻¹ = b⁻¹ := by
        rw [hrD b⁻¹ (inv_mem hbD), mul_inv_cancel_right]
      have hrt : r * (b * k₁ * b⁻¹ * k₁⁻¹) * r⁻¹
          = b * (r * k₁ * r⁻¹) * b⁻¹ * (r * k₁ * r⁻¹)⁻¹ := by
        calc r * (b * k₁ * b⁻¹ * k₁⁻¹) * r⁻¹
            = (r * b * r⁻¹) * (r * k₁ * r⁻¹) * (r * b⁻¹ * r⁻¹) * (r * k₁⁻¹ * r⁻¹) := by group
          _ = b * (r * k₁ * r⁻¹) * b⁻¹ * (r * k₁ * r⁻¹)⁻¹ := by rw [hrb, hrbi]; group
      have hrt' : r * (b * k₁ * b⁻¹ * k₁⁻¹) * r⁻¹ = b * k₁ * b⁻¹ * k₁⁻¹ := by
        rw [hrD _ htD, mul_inv_cancel_right]
      have hE : b * (r * k₁ * r⁻¹) * b⁻¹ * (r * k₁ * r⁻¹)⁻¹ = b * k₁ * b⁻¹ * k₁⁻¹ :=
        hrt.symm.trans hrt'
      have hE4w : w⁻¹ * ((r * k₁ * r⁻¹) * w * (r * k₁ * r⁻¹)⁻¹)
          = w⁻¹ * (k₁ * w * k₁⁻¹) := by
        calc w⁻¹ * ((r * k₁ * r⁻¹) * w * (r * k₁ * r⁻¹)⁻¹)
            = w⁻¹ * (r * k₁ * r⁻¹) * w * (r * k₁ * r⁻¹)⁻¹ := by group
          _ = b * (r * k₁ * r⁻¹) * b⁻¹ * (r * k₁ * r⁻¹)⁻¹ := (hcomm _ hk₁').symm
          _ = b * k₁ * b⁻¹ * k₁⁻¹ := hE
          _ = w⁻¹ * k₁ * w * k₁⁻¹ := hcomm k₁ hk₁
          _ = w⁻¹ * (k₁ * w * k₁⁻¹) := by group
      exact mul_left_cancel hE4w
    have hcomm' : ∀ w ∈ K, (k₁⁻¹ * (r * k₁ * r⁻¹)) * w = w * (k₁⁻¹ * (r * k₁ * r⁻¹)) := by
      intro w hw
      have h1 := hE4 w hw
      calc k₁⁻¹ * (r * k₁ * r⁻¹) * w
          = k₁⁻¹ * ((r * k₁ * r⁻¹) * w * (r * k₁ * r⁻¹)⁻¹) * (r * k₁ * r⁻¹) := by group
        _ = k₁⁻¹ * (k₁ * w * k₁⁻¹) * (r * k₁ * r⁻¹) := by rw [h1]
        _ = w * (k₁⁻¹ * (r * k₁ * r⁻¹)) := by group
    exact e15d1_center_le h s.mem s.isInv (K.mul_mem (K.inv_mem hk₁) hk₁') hcomm'
  have hsq2 : ∀ k₁ ∈ K, (r * r) * k₁ * (r * r)⁻¹ = k₁ := by
    intro k₁ hk₁
    obtain ⟨c, hc⟩ : ∃ c : G, c = k₁⁻¹ * (r * k₁ * r⁻¹) := ⟨_, rfl⟩
    have hcz : c ∈ Subgroup.zpowers z := by rw [hc]; exact hcen k₁ hk₁
    have hcD : c ∈ zGroup Ω := (Subgroup.zpowers_le.mpr hzD) hcz
    have hcc : c * c = 1 := h.zGroup_mul_self h9 c hcD
    have hrc : r * c * r⁻¹ = c := by rw [hrD c hcD, mul_inv_cancel_right]
    have hrk : r * k₁ * r⁻¹ = k₁ * c := by rw [hc, mul_inv_cancel_left]
    calc (r * r) * k₁ * (r * r)⁻¹ = r * (r * k₁ * r⁻¹) * r⁻¹ := by group
      _ = r * (k₁ * c) * r⁻¹ := by rw [hrk]
      _ = (r * k₁ * r⁻¹) * (r * c * r⁻¹) := by group
      _ = (k₁ * c) * c := by rw [hrk, hrc]
      _ = k₁ := by rw [mul_assoc, hcc, mul_one]
  have hT : r * r ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hsq2 x hx
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  rw [hpow]
  exact pow_mem hT (m + 1)

theorem eq_one_of_odd_mem_centralizer_zGroup (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {r : G}
    (hr : r ∈ Subgroup.centralizer (zGroup Ω : Set G)) (hodd : Odd (orderOf r)) : r = 1 := by
  obtain ⟨d₀, hd₀, hsw⟩ := h.exists_mem_zGroup_swap h9 s h13
  have hD := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hall : ∀ L ∈ Ω, L ≤ Subgroup.centralizer ({r} : Set G) := by
    intro L hL x hx
    obtain ⟨g, rfl⟩ := h.thmD.trans K s.mem L hL
    have hr' : g⁻¹ * r * g ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 := (Subgroup.mem_centralizer_iff.mp hr) (g * d * g⁻¹) (hD.conj_mem d hd g)
      calc d * (g⁻¹ * r * g) = g⁻¹ * ((g * d * g⁻¹) * r) * g := by group
        _ = g⁻¹ * (r * (g * d * g⁻¹)) * g := by rw [h1]
        _ = g⁻¹ * r * g * d := by group
    have hord : orderOf (g⁻¹ * r * g) = orderOf r := by
      have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective r
      simpa [MulAut.conj_apply] using this
    have hK' := e15d1_odd_centralizes h h9 s hd₀ hsw hr' (by rw [hord]; exact hodd)
    have hy := mem_conjSub_iff.mp hx
    have hc := Subgroup.mem_centralizer_iff.mp hK' (g⁻¹ * x * g) hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * r = g * (g⁻¹ * x * g * (g⁻¹ * r * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * r * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = r * x := by group
  have hcenter : r ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ pSpan Ω := by rw [h.thmD.gen]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp (pSpan_le hall hg)
  have hbot : r ∈ (⊥ : Subgroup G) := by rw [← h.center]; exact hcenter
  exact Subgroup.mem_bot.mp hbot

private theorem e15d1_exists_two_pow {D : Subgroup G} {x : G} (hx : x ∈ D)
    (hodd : ∀ y ∈ D, Odd (orderOf y) → y = 1) : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hym : (x ^ (2 ^ k)) ^ m = 1 := by
    rw [← pow_mul, ← hkm, pow_orderOf_eq_one]
  have hodd' : Odd (orderOf (x ^ (2 ^ k))) :=
    hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hym)
  exact ⟨k, hodd _ (pow_mem hx _) hodd'⟩

theorem centralizer_zGroup_eq_pCore (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) :
    Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G := by
  have hD := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  apply le_antisymm
  · haveI := hD
    have hpg : IsPGroup 2 ↥(Subgroup.centralizer (zGroup Ω : Set G)) := by
      intro g
      obtain ⟨k, hk⟩ := e15d1_exists_two_pow g.2
        (fun y hy hodd => eq_one_of_odd_mem_centralizer_zGroup h h9 s h13 hy hodd)
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    exact (le_sSup ⟨inferInstance, hpg⟩ : Subgroup.centralizer (zGroup Ω : Set G) ≤ pCore 2 G)
  · exact h.pCore_le_centralizer_zGroup h9

private theorem e15d2_pCore_conj {q : G} (hq : q ∈ pCore 2 G) (g : G) :
    g * q * g⁻¹ ∈ pCore 2 G :=
  (CFSG.pCore_normal (p := 2) (G := G)).conj_mem q hq g

private theorem e15d2_dComm_mem_one_or (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {i : G} (hi : i ∈ K) {x : G}
    (hxQ : x ∈ pCore 2 G) (hxN : x ∈ Subgroup.normalizer (K : Set G)) :
    dComm x i = 1 ∨ dComm x i = z := by
  have h1 : dComm x i ∈ K := dComm_mem hxN hi
  have h2 : dComm x i ∈ pCore 2 G := by
    have e : dComm x i = x * (i * x⁻¹ * i⁻¹) := by
      unfold dComm
      group
    rw [e]
    exact mul_mem hxQ (e15d2_pCore_conj (inv_mem hxQ) i)
  have h3 : dComm x i ∈ K ⊓ Subgroup.centralizer (zGroup Ω : Set G) :=
    Subgroup.mem_inf.mpr ⟨h1, h.pCore_le_centralizer_zGroup h9 h2⟩
  rw [h.inf_centralizer_zGroup_eq_zpowers h9 s h13] at h3
  exact e15d2_zpowers_one_or s.isInv.sq h3

theorem pCore_eq_zGroup_mul_centralizer (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {q : G} (hq : q ∈ pCore 2 G) :
    ∃ d ∈ zGroup Ω, ∃ c ∈ pCore 2 G, c ∈ Subgroup.centralizer (K : Set G) ∧ q = d * c := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen s.isInv (h.isQuatSub_of_mem s.mem) (h.card_eq_eight s.mem)
  have hQ : Q8Data K z i j := ⟨s.isInv, hi, hj, hii, hjj, hji, hNF⟩
  have hzz := hQ.inv.sq
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, s.mem, s.isInv⟩
  obtain ⟨t, ht, q', hq'Q, hq'N, hqe⟩ : ∃ t ∈ zGroup Ω, ∃ q' ∈ pCore 2 G,
      q' ∈ Subgroup.normalizer (K : Set G) ∧ q = t * q' := by
    have hqC : q ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
      h.pCore_le_centralizer_zGroup h9 hq
    have hzq : z * q = q * z := Subgroup.mem_centralizer_iff.mp hqC z hzD
    have hmem : conjSub q K ∈ twinSet Ω K := by
      refine ⟨h.thmD.hyp.conjInvariant q K s.mem, z, s.isInv, ?_⟩
      have h1 := s.isInv.conj q
      have hqz : q * z * q⁻¹ = z := by
        rw [← hzq]
        group
      rwa [hqz] at h1
    rw [s.twin] at hmem
    rcases Set.mem_insert_iff.mp hmem with hA | hB
    · exact ⟨1, one_mem _, q, hq, mem_normalizer_iff_conjSub_eq.mpr hA, (one_mul q).symm⟩
    · have hB' : conjSub q K = K' := Set.mem_singleton_iff.mp hB
      obtain ⟨d₀, hd₀, hsw⟩ := h.exists_mem_zGroup_swap h9 s h13
      have hd₀d₀ : d₀ * d₀ = 1 := h.zGroup_mul_self h9 d₀ hd₀
      have hK'' : conjSub d₀ K' = K := by
        rw [← hsw, ← conjSub_mul, hd₀d₀, conjSub_one]
      have hq'N : d₀ * q ∈ Subgroup.normalizer (K : Set G) := by
        rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, hB', hK'']
      refine ⟨d₀, hd₀, d₀ * q, mul_mem (h.zGroup_le_pCore hd₀) hq, hq'N, ?_⟩
      rw [← mul_assoc, hd₀d₀, one_mul]
  obtain ⟨b, hb, c, hcQ, hcC, hq'eq⟩ : ∃ b ∈ zGroup Ω, ∃ c ∈ pCore 2 G,
      c ∈ Subgroup.centralizer (K : Set G) ∧ q' = b * c := by
    have hP1 := e15d2_dComm_mem_one_or h h9 s h13 hQ.mem_i hq'Q hq'N
    have hP2 := e15d2_dComm_mem_one_or h h9 s h13 hQ.mem_j hq'Q hq'N
    obtain ⟨b, hbS, e1, e2⟩ := e15d2_exists_pair h h9 s h13 hQ hP1 hP2
    have hbD : b ∈ zGroup Ω := (Subgroup.mem_inf.mp hbS).1
    have hbQ : b ∈ pCore 2 G := h.zGroup_le_pCore hbD
    have hbb : b * b = 1 := h.zGroup_mul_self h9 b hbD
    have hcQ : b * q' ∈ pCore 2 G := mul_mem hbQ hq'Q
    have hcz : b * q' * z = z * (b * q') :=
      (Subgroup.mem_centralizer_iff.mp (h.pCore_le_centralizer_zGroup h9 hcQ) z hzD).symm
    have hPi : dComm q' i ∈ zGroup Ω := by
      rcases hP1 with h1 | h1 <;> rw [h1]
      · exact one_mem _
      · exact hzD
    have hPj : dComm q' j ∈ zGroup Ω := by
      rcases hP2 with h1 | h1 <;> rw [h1]
      · exact one_mem _
      · exact hzD
    have hPPi : dComm q' i * dComm q' i = 1 := by
      rcases hP1 with h1 | h1 <;> rw [h1]
      · exact one_mul 1
      · exact hzz
    have hPPj : dComm q' j * dComm q' j = 1 := by
      rcases hP2 with h1 | h1 <;> rw [h1]
      · exact one_mul 1
      · exact hzz
    have eqi : q' * i = dComm q' i * i * q' := by
      unfold dComm
      group
    have eqj : q' * j = dComm q' j * j * q' := by
      unfold dComm
      group
    have eqbi : b * i = dComm b i * i * b := by
      unfold dComm
      group
    have eqbj : b * j = dComm b j * j * b := by
      unfold dComm
      group
    have hci : b * q' * i = i * (b * q') := by
      calc b * q' * i = b * (q' * i) := by group
        _ = b * (dComm q' i * i * q') := by rw [eqi]
        _ = (b * dComm q' i) * i * q' := by group
        _ = (dComm q' i * b) * i * q' := by rw [h.zGroup_comm h9 b hbD _ hPi]
        _ = dComm q' i * (b * i) * q' := by group
        _ = dComm q' i * (dComm b i * i * b) * q' := by rw [eqbi]
        _ = dComm q' i * (dComm q' i * i * b) * q' := by rw [e1]
        _ = (dComm q' i * dComm q' i) * i * (b * q') := by group
        _ = i * (b * q') := by rw [hPPi, one_mul]
    have hcj : b * q' * j = j * (b * q') := by
      calc b * q' * j = b * (q' * j) := by group
        _ = b * (dComm q' j * j * q') := by rw [eqj]
        _ = (b * dComm q' j) * j * q' := by group
        _ = (dComm q' j * b) * j * q' := by rw [h.zGroup_comm h9 b hbD _ hPj]
        _ = dComm q' j * (b * j) * q' := by group
        _ = dComm q' j * (dComm b j * j * b) * q' := by rw [eqbj]
        _ = dComm q' j * (dComm q' j * j * b) * q' := by rw [e2]
        _ = (dComm q' j * dComm q' j) * j * (b * q') := by group
        _ = j * (b * q') := by rw [hPPj, one_mul]
    have hcC : b * q' ∈ Subgroup.centralizer (K : Set G) :=
      e15d2_commute_of_gens hQ hcz hci hcj
    exact ⟨b, hbD, b * q', hcQ, hcC, by rw [← mul_assoc, hbb, one_mul]⟩
  refine ⟨t * b, mul_mem ht hb, c, hcQ, hcC, ?_⟩
  rw [hqe, hq'eq, mul_assoc]

theorem pCore_commutator_mem_zGroup (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {q : G} (hq : q ∈ pCore 2 G) (g : G) :
    g * q * g⁻¹ * q⁻¹ ∈ zGroup Ω := by
  have hDN : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hK_case : ∀ q' ∈ pCore 2 G, ∀ k ∈ K, k * q' * k⁻¹ * q'⁻¹ ∈ zGroup Ω := by
    intro q' hq' k hk
    obtain ⟨d, hd, c, hcQ, hcC, rfl⟩ := pCore_eq_zGroup_mul_centralizer h h9 s h13 hq'
    have hck : c * k⁻¹ * c⁻¹ = k⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.mp hcC k⁻¹ (K.inv_mem hk)]
      group
    have e : k * (d * c) * k⁻¹ * (d * c)⁻¹ = (k * d * k⁻¹) * d⁻¹ := by
      calc k * (d * c) * k⁻¹ * (d * c)⁻¹ = k * d * (c * k⁻¹ * c⁻¹) * d⁻¹ := by group
        _ = k * d * k⁻¹ * d⁻¹ := by rw [hck]
    rw [e]
    exact mul_mem (hDN.conj_mem d hd k) (inv_mem hd)
  have hmem_case : ∀ L ∈ Ω, ∀ l ∈ L, ∀ q' ∈ pCore 2 G,
      l * q' * l⁻¹ * q'⁻¹ ∈ zGroup Ω := by
    intro L hL l hl q' hq'
    obtain ⟨t, rfl⟩ := h.thmD.trans K s.mem L hL
    have hk : t⁻¹ * l * t ∈ K := mem_conjSub_iff.mp hl
    have hq'' : t⁻¹ * q' * t ∈ pCore 2 G := by
      have := e15d2_pCore_conj hq' t⁻¹
      rwa [inv_inv] at this
    have key := hK_case (t⁻¹ * q' * t) hq'' (t⁻¹ * l * t) hk
    have e : l * q' * l⁻¹ * q'⁻¹ = t * ((t⁻¹ * l * t) * (t⁻¹ * q' * t) * (t⁻¹ * l * t)⁻¹ *
        (t⁻¹ * q' * t)⁻¹) * t⁻¹ := by
      group
    rw [e]
    exact hDN.conj_mem _ key t
  let N : Subgroup G :=
    { carrier := {x | x * q * x⁻¹ * q⁻¹ ∈ zGroup Ω}
      mul_mem' := fun {a b} ha hb => by
        show a * b * q * (a * b)⁻¹ * q⁻¹ ∈ zGroup Ω
        have e : a * b * q * (a * b)⁻¹ * q⁻¹ =
            a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ * (a * q * a⁻¹ * q⁻¹) := by
          group
        rw [e]
        exact mul_mem (hDN.conj_mem _ hb a) ha
      one_mem' := by
        show (1 : G) * q * (1 : G)⁻¹ * q⁻¹ ∈ zGroup Ω
        rw [show (1 : G) * q * (1 : G)⁻¹ * q⁻¹ = 1 by group]
        exact one_mem _
      inv_mem' := fun {a} ha => by
        show a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ ∈ zGroup Ω
        have e : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = a⁻¹ * (a * q * a⁻¹ * q⁻¹)⁻¹ * a := by
          group
        rw [e]
        have := hDN.conj_mem _ (inv_mem ha) a⁻¹
        rwa [inv_inv] at this }
  have hN : pSpan Ω ≤ N := pSpan_le fun L hL l hl => hmem_case L hL l hl q hq
  have hg : g ∈ N := hN (by rw [h.thmD.gen]; exact Subgroup.mem_top g)
  exact hg

private theorem e15d2_eq_one_of_conj (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {x : G}
    (hx : ∀ g : G, g * x * g⁻¹ ∈ Subgroup.centralizer (K : Set G)) : x = 1 := by
  have hcx : ∀ L ∈ Ω, L ≤ Subgroup.centralizer ({x} : Set G) := by
    intro L hL l hl
    obtain ⟨t, rfl⟩ := h.thmD.trans K hK L hL
    have hk : t⁻¹ * l * t ∈ K := mem_conjSub_iff.mp hl
    have hw := hx t⁻¹
    rw [inv_inv] at hw
    have hw' := Subgroup.mem_centralizer_iff.mp hw
    have hkw : (t⁻¹ * l * t) * (t⁻¹ * x * t) = (t⁻¹ * x * t) * (t⁻¹ * l * t) := hw' _ hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc l * x = t * ((t⁻¹ * l * t) * (t⁻¹ * x * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * x * t) * (t⁻¹ * l * t)) * t⁻¹ := by rw [hkw]
      _ = x * l := by group
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← h.thmD.gen]
    exact pSpan_le hcx
  have hcenter : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top g))
  rw [h.center, Subgroup.mem_bot] at hcenter
  exact hcenter

theorem pCore_comm_mul_self (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) :
    ∀ a ∈ pCore 2 G, ∀ b ∈ pCore 2 G, a * b = b * a ∧ a * a = 1 := by
  have hC : ∀ x ∈ pCore 2 G, ∀ d ∈ zGroup Ω, d * x = x * d := fun x hx d hd =>
    Subgroup.mem_centralizer_iff.mp (h.pCore_le_centralizer_zGroup h9 hx) d hd
  have hsq : ∀ a ∈ pCore 2 G, a * a ∈ Subgroup.centralizer (K : Set G) := by
    intro a ha
    obtain ⟨d, hd, c, hcQ, hcC, rfl⟩ := pCore_eq_zGroup_mul_centralizer h h9 s h13 ha
    have hdc : d * c = c * d := hC c hcQ d hd
    have e : d * c * (d * c) = c * c := by
      calc d * c * (d * c) = d * (c * d) * c := by group
        _ = d * (d * c) * c := by rw [← hdc]
        _ = (d * d) * (c * c) := by group
        _ = c * c := by rw [h.zGroup_mul_self h9 d hd, one_mul]
    rw [e]
    exact mul_mem hcC hcC
  have hcomm : ∀ a ∈ pCore 2 G, ∀ b ∈ pCore 2 G,
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    intro a ha b hb
    obtain ⟨d₁, hd₁, c₁, hc₁Q, hc₁C, rfl⟩ := pCore_eq_zGroup_mul_centralizer h h9 s h13 ha
    obtain ⟨d₂, hd₂, c₂, hc₂Q, hc₂C, rfl⟩ := pCore_eq_zGroup_mul_centralizer h h9 s h13 hb
    have h12 : c₁ * d₂ = d₂ * c₁ := (hC c₁ hc₁Q d₂ hd₂).symm
    have h21 : c₂ * d₁ = d₁ * c₂ := (hC c₂ hc₂Q d₁ hd₁).symm
    have hdd : d₁ * d₂ = d₂ * d₁ := h.zGroup_comm h9 d₁ hd₁ d₂ hd₂
    have hab : d₁ * c₁ * (d₂ * c₂) = (d₁ * d₂) * (c₁ * c₂) := by
      calc d₁ * c₁ * (d₂ * c₂) = d₁ * (c₁ * d₂) * c₂ := by group
        _ = d₁ * (d₂ * c₁) * c₂ := by rw [h12]
        _ = (d₁ * d₂) * (c₁ * c₂) := by group
    have hba : d₂ * c₂ * (d₁ * c₁) = (d₁ * d₂) * (c₂ * c₁) := by
      calc d₂ * c₂ * (d₁ * c₁) = d₂ * (c₂ * d₁) * c₁ := by group
        _ = d₂ * (d₁ * c₂) * c₁ := by rw [h21]
        _ = (d₂ * d₁) * (c₂ * c₁) := by group
        _ = (d₁ * d₂) * (c₂ * c₁) := by rw [hdd]
    have hX : d₁ * d₂ ∈ zGroup Ω := mul_mem hd₁ hd₂
    have hXc₁ : Commute (d₁ * d₂) c₁ := hC c₁ hc₁Q (d₁ * d₂) hX
    have hXc₂ : Commute (d₁ * d₂) c₂ := hC c₂ hc₂Q (d₁ * d₂) hX
    have hXY : Commute (d₁ * d₂) (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) :=
      ((hXc₁.mul_right hXc₂).mul_right hXc₁.inv_right).mul_right hXc₂.inv_right
    have e : d₁ * c₁ * (d₂ * c₂) * (d₁ * c₁)⁻¹ * (d₂ * c₂)⁻¹ =
        (d₁ * d₂) * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * (d₁ * d₂)⁻¹ := by
      calc d₁ * c₁ * (d₂ * c₂) * (d₁ * c₁)⁻¹ * (d₂ * c₂)⁻¹
          = (d₁ * c₁ * (d₂ * c₂)) * (d₂ * c₂ * (d₁ * c₁))⁻¹ := by group
        _ = ((d₁ * d₂) * (c₁ * c₂)) * ((d₁ * d₂) * (c₂ * c₁))⁻¹ := by rw [hab, hba]
        _ = (d₁ * d₂) * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * (d₁ * d₂)⁻¹ := by group
    have hXY' : (d₁ * d₂) * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * (d₁ * d₂)⁻¹ =
        c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by
      rw [hXY.eq]
      group
    rw [e, hXY']
    exact mul_mem (mul_mem (mul_mem hc₁C hc₂C) (inv_mem hc₁C)) (inv_mem hc₂C)
  have hconj : ∀ x ∈ pCore 2 G, ∀ g : G, g * x * g⁻¹ ∈ pCore 2 G := fun x hx g =>
    e15d2_pCore_conj hx g
  intro a ha b hb
  constructor
  · have hall : ∀ g : G, g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
      intro g
      have := hcomm (g * a * g⁻¹) (hconj a ha g) (g * b * g⁻¹) (hconj b hb g)
      have e : g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ =
          g * a * g⁻¹ * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by
        group
      rw [e]
      exact this
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := e15d2_eq_one_of_conj h s.mem hall
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  · have hall : ∀ g : G, g * (a * a) * g⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
      intro g
      have := hsq (g * a * g⁻¹) (hconj a ha g)
      have e : g * (a * a) * g⁻¹ = g * a * g⁻¹ * (g * a * g⁻¹) := by
        group
      rw [e]
      exact this
    exact e15d2_eq_one_of_conj h s.mem hall

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
