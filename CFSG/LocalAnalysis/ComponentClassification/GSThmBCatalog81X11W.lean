module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11C

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem X11.ncard_conj_mul_card {G : Type*} [Group G] [Finite G] (S : Subgroup G) (w : G) :
    {x : G | ∃ s ∈ S, s * w * s⁻¹ = x}.ncard * Nat.card ↥(S ⊓ centralizer ({w} : Set G)) =
      Nat.card S := by
  let _ : MulAction ↥S G := MulAction.compHom G (MulAut.conj.comp S.subtype)
  have hsmul : ∀ (s : ↥S) (x : G), s • x = (s : G) * x * (s : G)⁻¹ := fun _ _ => rfl
  have horb : MulAction.orbit ↥S w = {x : G | ∃ s ∈ S, s * w * s⁻¹ = x} := by
    ext x
    simp only [MulAction.mem_orbit_iff, hsmul, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, s.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  have hstab : MulAction.stabilizer ↥S w = (centralizer ({w} : Set G)).subgroupOf S := by
    ext s
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc (s : G) * w = (s : G) * w * (s : G)⁻¹ * s := by group
        _ = w * s := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  have hcard : Nat.card ((centralizer ({w} : Set G)).subgroupOf S) =
      Nat.card ↥(S ⊓ centralizer ({w} : Set G)) := by
    rw [← inf_subgroupOf_right, inf_comm]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← horb, ← MulAction.index_stabilizer, ← hcard, ← hstab, Subgroup.index_mul_card]

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁} {v : H} (hv : d.IsV v)

section Swap

variable {w : H} (hwU : w ∈ h.U81 v) (hwS : w ∉ h.S)
include hv hwU hwS

theorem conj_w_mem_Pv {π : H} (hπ : π ∈ h.P) : w⁻¹ * π * w ∈ conjugate h.P v := by
  obtain ⟨s, hs, rfl⟩ := (mem_U_cases hv hwU).resolve_left hwS
  rw [mem_conjugate_iff, show v * ((s * v)⁻¹ * π * (s * v)) * v⁻¹ = s⁻¹ * π * s⁻¹⁻¹ by group]
  exact h.toHyp52.conj_mem_P' (inv_mem hs) hπ

theorem conj_w_mem_P {π : H} (hπ : π ∈ conjugate h.P v) : w⁻¹ * π * w ∈ h.P := by
  obtain ⟨s, hs, rfl⟩ := (mem_U_cases hv hwU).resolve_left hwS
  have h1 := h.toHyp52.sec8_conj_mem_conjugate_P hv.mem_N (inv_mem hs) hπ
  rw [mem_conjugate_iff] at h1
  have h2 := h.toHyp52.conj_mem_P' (inv_mem hv.sq_mem) h1
  rwa [show (v * v)⁻¹ * (v * (s⁻¹ * π * s⁻¹⁻¹) * v⁻¹) * (v * v)⁻¹⁻¹ =
    (s * v)⁻¹ * π * (s * v) by group] at h2

theorem conj_w_a : w⁻¹ * h.a * w = d.z := by
  obtain ⟨s, hs, rfl⟩ := (mem_U_cases hv hwU).resolve_left hwS
  have h1 : s⁻¹ * h.a * s = h.a := by rw [mul_assoc, ← h.toHyp52.comm_a hs, inv_mul_cancel_left]
  rw [show (s * v)⁻¹ * h.a * (s * v) = v⁻¹ * (s⁻¹ * h.a * s) * v by group, h1, hv.conj_a]

theorem eq_one_of_mem_P_of_comm {π : H} (hπ : π ∈ h.P) (hc : π * w = w * π) : π = 1 := by
  have h1 : w⁻¹ * π * w = π := by rw [mul_assoc, hc, inv_mul_cancel_left]
  have h2 := conj_w_mem_Pv hv hwU hwS hπ
  rw [h1] at h2
  have h3 : π ∈ h.P ⊓ conjugate h.P v := mem_inf.mpr ⟨hπ, h2⟩
  rwa [P_inf_Pv hv, mem_bot] at h3

end Swap

section Count

variable (I : In81) (hst : d.Stage7 v)
  (hJ : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2)
include hv I hst hJ

theorem F32_eq_and_card :
    h.F32 = h.PPv v ⊔ zpowers d.sigma ∧ Nat.card h.F32 = 2 * (Nat.card h.P * Nat.card h.P) := by
  have F := hst.facts
  have hvF : v ∈ normalizer (h.F32 : Set H) := h.normalizer_S_le_normalizer_F32 hv.mem_N
  have hPvF : conjugate h.P v ≤ h.F32 := fun q hq =>
    (mem_normalizer_iff.mp hvF q).mpr (hst.P_le_F (mem_conjugate_iff.mp hq))
  have hσ : d.sigma ∉ h.PPv v := fun hσ =>
    asigma_not_mem_PPv hv I hst (mul_mem (mem_sup_left h.toHyp52.a_mem_P) hσ)
  have h1 : h.PPv v < h.PPv v ⊔ zpowers d.sigma :=
    lt_of_le_of_ne le_sup_left fun he => hσ (he ▸ mem_sup_right (mem_zpowers _))
  have h2 : h.PPv v ⊔ zpowers d.sigma ≤ h.F32 :=
    sup_le (sup_le hst.P_le_F hPvF) (zpowers_le.mpr (sigma_mem_F I F))
  obtain ⟨y, hyS, -, -, hyσ, -, -⟩ := hst.y
  have hyF : y ∉ h.F32 := by
    intro hyF
    have hc := mem_centralizer_singleton_iff.mp (d.F32_le_centralizer_sigma I.rk I.j I.c I.b1
      I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F hyF)
    have : y⁻¹ * d.sigma * y = d.sigma := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    rw [hyσ] at this
    apply d.z_ne_a
    calc d.z = d.z * (h.a * d.z * d.sigma * d.sigma⁻¹) := by
          rw [this, mul_inv_cancel, mul_one]
      _ = d.z * (h.a * d.z) := by rw [mul_inv_cancel_right]
      _ = h.a := by rw [← mul_assoc, d.z_comm_a, mul_assoc, d.z_mul_self, mul_one]
  have h3 : h.F32 < h.F32 ⊔ zpowers y :=
    lt_of_le_of_ne le_sup_left fun he => hyF (he ▸ mem_sup_right (mem_zpowers _))
  have c1 := X11.two_mul_card_le_of_lt h1
  have c2 := Subgroup.card_le_of_le h2
  have c3 := X11.two_mul_card_le_of_lt h3
  have c4 := Subgroup.card_le_of_le (sup_le h.F32_le_S (zpowers_le.mpr hyS))
  rw [card_PPv hv] at c1
  have hS := (card_P_eq_and_card_S hv I hst hJ).2
  have hcard : Nat.card h.F32 = 2 * (Nat.card h.P * Nat.card h.P) := by omega
  exact ⟨(eq_of_le_of_card_ge h2 (by omega)).symm, hcard⟩

theorem mem_F32_cases {f : H} (hf : f ∈ h.F32) :
    ∃ π ∈ h.P, ∃ π' ∈ conjugate h.P v, f = π * π' ∨ f = π * π' * d.sigma := by
  rw [(F32_eq_and_card hv I hst hJ).1, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _
      (zpowers_le.mpr (U_le_normalizer_PPv hv (mem_sup_left d.sigma_mem_S)))] at hf
  obtain ⟨x, hx, k, hk, rfl⟩ := hf
  obtain ⟨π, hπ, π', hπ', rfl⟩ := (mem_PPv_iff hv).mp hx
  rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hk with rfl | rfl
  · exact ⟨π, hπ, π', hπ', Or.inl (mul_one _)⟩
  · exact ⟨π, hπ, π', hπ', Or.inr rfl⟩

variable {w : H} (hwU : w ∈ h.U81 v) (hwS : w ∉ h.S)
include hwU hwS

omit hwS in
theorem conj_mem_F32 {s : H} (hs : s ∈ h.S) : w⁻¹ * (s * w * s⁻¹) ∈ h.F32 := by
  obtain ⟨hP8, hS⟩ := card_P_eq_and_card_S hv I hst hJ
  have hidx : (h.F32.subgroupOf h.S).index = 2 := by
    have h1 := (h.F32.subgroupOf h.S).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe h.F32_le_S).toEquiv,
      (F32_eq_and_card hv I hst hJ).2, hS, hP8] at h1
    norm_num at h1
    omega
  have hUN : h.U81 v ≤ normalizer (h.S : Set H) := sup_le le_normalizer (zpowers_le.mpr hv.mem_N)
  have hs' : w⁻¹ * s * w ∈ h.S := by
    have := (mem_normalizer_iff.mp (inv_mem (hUN hwU)) s).mp hs
    rwa [inv_inv] at this
  have key := mul_mem_iff_of_index_two hidx (a := ⟨w⁻¹ * s * w, hs'⟩) (b := ⟨s⁻¹, inv_mem hs⟩)
  simp only [mem_subgroupOf, coe_mul] at key
  have hwF : w⁻¹ * s * w ∈ h.F32 ↔ s ∈ h.F32 := by
    have := mem_normalizer_iff.mp (inv_mem (U_le_normalizer_F hv hwU)) s
    rw [inv_inv] at this
    exact this.symm
  rw [show w⁻¹ * (s * w * s⁻¹) = w⁻¹ * s * w * s⁻¹ by group, key, hwF, inv_mem_iff]

variable (hw2 : w * w = 1) (hwc : w * (h.a * d.sigma) = h.a * d.sigma * w)
include hw2 hwc

theorem mem_range_of_mul_self {f : H} (hf : f ∈ h.F32) (hf2 : w * f * (w * f) = 1) :
    w * f ∈ Set.range (fun π : ↥h.P => w * ((π : H) * (w⁻¹ * π * w)⁻¹)) ∪
      Set.range (fun π : ↥h.P => w * ((π : H) * (w⁻¹ * π * w * d.z⁻¹)⁻¹ * d.sigma)) := by
  have F := hst.facts
  have winv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hf2' : w⁻¹ * f * w * f = 1 := by
    calc w⁻¹ * f * w * f = w * f * (w * f) := by rw [winv]; group
      _ = 1 := hf2
  have hvF : v ∈ normalizer (h.F32 : Set H) := h.normalizer_S_le_normalizer_F32 hv.mem_N
  have hPvF : conjugate h.P v ≤ h.F32 := fun q hq =>
    (mem_normalizer_iff.mp hvF q).mpr (hst.P_le_F (mem_conjugate_iff.mp hq))
  obtain ⟨π, hπ, π', hπ', rfl | rfl⟩ := mem_F32_cases hv I hst hJ hf
  ·
    left
    have hA := conj_w_mem_Pv hv hwU hwS hπ
    have hB := conj_w_mem_P hv hwU hwS hπ'
    have e1 := comm_P_Pv hv hπ hA
    have e2 := comm_P_Pv hv hB hA
    have key : (w⁻¹ * π' * w * π) * (w⁻¹ * π * w * π') = 1 := by
      calc (w⁻¹ * π' * w * π) * (w⁻¹ * π * w * π') =
            w⁻¹ * π' * w * (π * (w⁻¹ * π * w)) * π' := by group
        _ = w⁻¹ * π' * w * ((w⁻¹ * π * w) * π) * π' := by rw [e1]
        _ = ((w⁻¹ * π' * w) * (w⁻¹ * π * w)) * π * π' := by group
        _ = ((w⁻¹ * π * w) * (w⁻¹ * π' * w)) * π * π' := by rw [e2]
        _ = w⁻¹ * (π * π') * w * (π * π') := by group
        _ = 1 := hf2'
    have h1 : w⁻¹ * π * w * π' ∈ h.P ⊓ conjugate h.P v := by
      refine mem_inf.mpr ⟨?_, mul_mem hA hπ'⟩
      rw [eq_inv_of_mul_eq_one_right key]
      exact inv_mem (mul_mem hB hπ)
    rw [P_inf_Pv hv, mem_bot] at h1
    exact ⟨⟨π, hπ⟩, by rw [eq_inv_of_mul_eq_one_right h1]⟩
  ·
    right
    have hA := conj_w_mem_Pv hv hwU hwS hπ
    have hB := conj_w_mem_P hv hwU hwS hπ'
    have hz := inv_mem (z_mem_Pv hv)
    have e2 := comm_P_Pv hv hB hA
    have e3 := comm_P_Pv hv (mul_mem h.toHyp52.a_mem_P hπ) (mul_mem hA hz)
    have hwc' : w⁻¹ * (h.a * d.sigma) * w = h.a * d.sigma := by
      rw [mul_assoc, ← hwc, inv_mul_cancel_left]
    have hwσ : w⁻¹ * d.sigma * w = d.z⁻¹ * (h.a * d.sigma) := by
      calc w⁻¹ * d.sigma * w = (w⁻¹ * h.a * w)⁻¹ * (w⁻¹ * (h.a * d.sigma) * w) := by group
        _ = d.z⁻¹ * (h.a * d.sigma) := by rw [conj_w_a hv hwU hwS, hwc']
    have hσπ : π * π' * d.sigma = d.sigma * (π * π') :=
      mem_centralizer_iff.mp (mem_inf.mp (sigma_mem_ZF I F)).2 _
        (mul_mem (hst.P_le_F hπ) (hPvF hπ'))
    have key : (w⁻¹ * π' * w * h.a * π) * (w⁻¹ * π * w * d.z⁻¹ * π') = 1 := by
      calc (w⁻¹ * π' * w * h.a * π) * (w⁻¹ * π * w * d.z⁻¹ * π') =
            w⁻¹ * π' * w * ((h.a * π) * (w⁻¹ * π * w * d.z⁻¹)) * π' := by group
        _ = w⁻¹ * π' * w * ((w⁻¹ * π * w * d.z⁻¹) * (h.a * π)) * π' := by rw [e3]
        _ = ((w⁻¹ * π' * w) * (w⁻¹ * π * w)) * d.z⁻¹ * h.a * π * π' := by group
        _ = ((w⁻¹ * π * w) * (w⁻¹ * π' * w)) * d.z⁻¹ * h.a * π * π' := by rw [e2]
        _ = (w⁻¹ * π * w) * (w⁻¹ * π' * w) * (d.z⁻¹ * (h.a * d.sigma)) *
              (d.sigma * (π * π')) := by
            rw [show (w⁻¹ * π * w) * (w⁻¹ * π' * w) * (d.z⁻¹ * (h.a * d.sigma)) *
              (d.sigma * (π * π')) = (w⁻¹ * π * w) * (w⁻¹ * π' * w) * d.z⁻¹ * h.a *
                (d.sigma * d.sigma) * π * π' by group, d.sigma_mul_self]
            group
        _ = w⁻¹ * (π * π' * d.sigma) * w * (π * π' * d.sigma) := by
            rw [← hwσ, ← hσπ]
            group
        _ = 1 := hf2'
    have h1 : w⁻¹ * π * w * d.z⁻¹ * π' ∈ h.P ⊓ conjugate h.P v := by
      refine mem_inf.mpr ⟨?_, mul_mem (mul_mem hA hz) hπ'⟩
      rw [eq_inv_of_mul_eq_one_right key]
      exact inv_mem (mul_mem (mul_mem hB h.toHyp52.a_mem_P) hπ)
    rw [P_inf_Pv hv, mem_bot] at h1
    exact ⟨⟨π, hπ⟩, by rw [eq_inv_of_mul_eq_one_right h1]⟩

theorem conj_or_le_sup :
    (∃ s ∈ h.S, s * w * s⁻¹ = w * (h.a * d.sigma)) ∨
      h.S ≤ h.P ⊔ (h.S ⊓ centralizer ({w} : Set H)) := by
  obtain ⟨hP8, hS⟩ := card_P_eq_and_card_S hv I hst hJ
  set C := h.S ⊓ centralizer ({w} : Set H) with hC
  by_cases hlarge : 4 * Nat.card h.P ≤ Nat.card C
  · right
    have hdisj : Disjoint h.P C := by
      rw [disjoint_iff, eq_bot_iff]
      intro π hπ
      obtain ⟨hπP, hπC⟩ := mem_inf.mp hπ
      exact mem_bot.mpr (eq_one_of_mem_P_of_comm hv hwU hwS hπP
        (mem_centralizer_singleton_iff.mp (mem_inf.mp hπC).2))
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer h.P C
      (inf_le_left.trans h.S_le_normalizer_P) hdisj
    have hle : h.P ⊔ C ≤ h.S := sup_le inf_le_left inf_le_left
    exact (eq_of_le_of_card_ge hle (by rw [hcard, hS]; nlinarith)).ge
  · left
    push Not at hlarge
    have hdvd : Nat.card C ∣ 2 ^ 8 := by
      have h1 := Subgroup.card_dvd_of_le (inf_le_left : C ≤ h.S)
      rw [hS, hP8] at h1
      norm_num at h1 ⊢
      exact h1
    obtain ⟨k, hk, hCk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hC16 : Nat.card C ≤ 16 := by
      rw [hP8, hCk] at hlarge
      rw [hCk]
      have hk4 : k ≤ 4 := by
        by_contra hk5
        have := Nat.pow_le_pow_right (by norm_num : 2 > 0) (show 5 ≤ k by omega)
        norm_num at this
        omega
      calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
        _ = 16 := by norm_num
    set g₀ : ↥h.P → H := fun π => w * ((π : H) * (w⁻¹ * π * w)⁻¹) with hg₀
    set g₁ : ↥h.P → H := fun π => w * ((π : H) * (w⁻¹ * π * w * d.z⁻¹)⁻¹ * d.sigma) with hg₁
    have hX : (Set.range g₀ ∪ Set.range g₁).ncard ≤ 16 := by
      have h1 := Set.ncard_union_le (Set.range g₀) (Set.range g₁)
      have h2 : ∀ g : ↥h.P → H, (Set.range g).ncard ≤ 8 := fun g => by
        rw [← Nat.card_coe_set_eq, ← hP8]
        exact Finite.card_range_le g
      have := h2 g₀
      have := h2 g₁
      omega
    have hO : {x : H | ∃ s ∈ h.S, s * w * s⁻¹ = x} ⊆ Set.range g₀ ∪ Set.range g₁ := by
      rintro x ⟨s, hs, rfl⟩
      have h1 := mem_range_of_mul_self hv I hst hJ hwU hwS hw2 hwc
        (conj_mem_F32 hv I hst hJ hwU hs) (by
          rw [mul_inv_cancel_left]
          calc s * w * s⁻¹ * (s * w * s⁻¹) = s * (w * w) * s⁻¹ := by group
            _ = 1 := by rw [hw2, mul_one, mul_inv_cancel])
      rwa [mul_inv_cancel_left] at h1
    have horb := X11.ncard_conj_mul_card h.S w
    rw [← hC, hS, hP8] at horb
    have hO16 : 16 ≤ {x : H | ∃ s ∈ h.S, s * w * s⁻¹ = x}.ncard := by
      by_contra hlt
      have h1 : {x : H | ∃ s ∈ h.S, s * w * s⁻¹ = x}.ncard ≤ 15 := by omega
      have := Nat.mul_le_mul h1 hC16
      omega
    have heq := Set.eq_of_subset_of_ncard_le hO (hX.trans hO16)
    have hmem : w * (h.a * d.sigma) ∈ Set.range g₀ ∪ Set.range g₁ :=
      mem_range_of_mul_self hv I hst hJ hwU hwS hw2 hwc
        (mem_inf.mp (asigma_mem_ZF I hst.facts)).1 (by
          calc w * (h.a * d.sigma) * (w * (h.a * d.sigma)) =
                h.a * d.sigma * w * (w * (h.a * d.sigma)) := by rw [← hwc]
            _ = h.a * d.sigma * (w * w) * (h.a * d.sigma) := by group
            _ = 1 := by rw [hw2, mul_one, asigma_mul_self])
    rw [← heq] at hmem
    exact hmem

end Count

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
