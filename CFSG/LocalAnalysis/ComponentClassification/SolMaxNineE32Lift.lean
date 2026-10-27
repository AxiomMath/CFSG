module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineE32Transport

public section

namespace CFSG.ComponentClassification.SolMax.NineE32

open Equiv Subgroup

variable {X : Type} [Group X]

namespace Frame

variable {H : Subgroup X} {φ : ↥H →* A9 × Multiplicative (ZMod 2)} {t : X} (F : Frame H φ t)
include F

omit F in
theorem phi_mul {x y : X} (hx : x ∈ H) (hy : y ∈ H) :
    φ ⟨x * y, mul_mem hx hy⟩ = φ ⟨x, hx⟩ * φ ⟨y, hy⟩ :=
  map_mul φ ⟨x, hx⟩ ⟨y, hy⟩

omit F in
theorem phi_inv {x : X} (hx : x ∈ H) : φ ⟨x⁻¹, inv_mem hx⟩ = (φ ⟨x, hx⟩)⁻¹ :=
  map_inv φ ⟨x, hx⟩

omit F in
theorem phi_conj {x y : X} (hx : x ∈ H) (hy : y ∈ H) :
    φ ⟨x * y * x⁻¹, mul_mem (mul_mem hx hy) (inv_mem hx)⟩ =
      φ ⟨x, hx⟩ * φ ⟨y, hy⟩ * (φ ⟨x, hx⟩)⁻¹ := by
  rw [phi_mul (mul_mem hx hy) (inv_mem hx), phi_mul hx hy, phi_inv]

omit F in
theorem conj_A₀ {u : alternatingGroup (Fin 9) × Multiplicative (ZMod 2)} (hu : u ∈ A₀)
    (v : Multiplicative W) : u * enc v * u⁻¹ = enc v := by
  obtain ⟨w, rfl⟩ := hu
  rw [← map_mul, ← map_inv, ← map_mul, mul_comm w v, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_normalizing [Finite X] (hφ : Function.Surjective φ)
    {y : alternatingGroup (Fin 9) × Multiplicative (ZMod 2)}
    {f : Multiplicative W → Multiplicative W}
    (hf : ∀ v, y * enc v * y⁻¹ = enc (f v)) :
    ∃ n ∈ H, ∀ v, n * F.κ v * n⁻¹ = F.κ (f v) := by
  obtain ⟨h, rfl⟩ := hφ y
  set B : Subgroup X := F.κ.range.map (MulAut.conj (h : X)).toMonoidHom with hB
  have hBP : B ≤ (A₀.comap φ).map H.subtype := by
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    refine mem_P_iff.mpr ⟨mul_mem (mul_mem h.2 (F.mem v)) (inv_mem h.2), ?_⟩
    show φ ⟨(h : X) * F.κ v * (h : X)⁻¹, mul_mem (mul_mem h.2 (F.mem v)) (inv_mem h.2)⟩ ∈ A₀
    rw [phi_conj h.2 (F.mem v), F.phi, hf]
    exact ⟨_, rfl⟩
  have hBcard : Nat.card B = 32 := by
    rw [hB, ← F.card_range]
    exact Nat.card_congr ((MulAut.conj (h : X)).subgroupMap F.κ.range).toEquiv.symm
  obtain ⟨c, hcP, hc⟩ := F.exists_conj_eq hBP hBcard
  obtain ⟨hcH, hcA⟩ := mem_P_iff.mp hcP
  refine ⟨c * h, mul_mem hcH h.2, fun v => ?_⟩
  have hmem : c * h * F.κ v * (c * h)⁻¹ ∈ F.κ.range := by
    rw [← hc]
    refine ⟨h * F.κ v * (h : X)⁻¹, ⟨F.κ v, ⟨v, rfl⟩, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨w, hw⟩ := hmem
  rw [← hw]
  congr 1
  apply enc_injective
  rw [← F.phi w, ← hf v]
  have h1 : (⟨F.κ w, F.mem w⟩ : ↥H) = ⟨c * h * F.κ v * (c * h)⁻¹,
      mul_mem (mul_mem (mul_mem hcH h.2) (F.mem v)) (inv_mem (mul_mem hcH h.2))⟩ :=
    Subtype.ext hw
  rw [h1, phi_conj (mul_mem hcH h.2) (F.mem v), phi_mul hcH h.2, F.phi]
  have h2 := conj_A₀ hcA (f v)
  rw [← hf v] at h2
  simp only [Subtype.coe_eta]
  rw [mul_inv_rev]
  calc φ ⟨c, hcH⟩ * φ h * enc v * ((φ h)⁻¹ * (φ ⟨c, hcH⟩)⁻¹)
      = φ ⟨c, hcH⟩ * (φ h * enc v * (φ h)⁻¹) * (φ ⟨c, hcH⟩)⁻¹ := by group
    _ = φ h * enc v * (φ h)⁻¹ := h2

omit F in
theorem cycleType_of_involution {σ : Perm (Fin 9)} (h2 : σ * σ = 1) :
    σ.cycleType = Multiset.replicate (σ.support.card / 2) 2 := by
  have hall : ∀ x ∈ σ.cycleType, x = 2 := by
    intro x hx
    have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h2])
    have h2le := Perm.two_le_of_mem_cycleType hx
    have hle := Nat.le_of_dvd (by norm_num) ((Perm.dvd_of_mem_cycleType hx).trans hord)
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.mpr hall
  have hsum := Perm.sum_cycleType σ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hrep]
  congr 1
  omega

omit F in
theorem exists_conj_mW {σ : Perm (Fin 9)} (h2 : σ * σ = 1) (h8 : σ.support.card = 8) :
    ∃ c : Perm (Fin 9), c ∈ alternatingGroup (Fin 9) ∧ c * σ * c⁻¹ = encPerm mW := by
  have hm2 : encPerm mW * encPerm mW = 1 := by decide
  have hm8 : (encPerm mW).support.card = 8 := by decide
  have hconj : IsConj σ (encPerm mW) := by
    rw [Perm.isConj_iff_cycleType_eq, cycleType_of_involution h2, cycleType_of_involution hm2,
      h8, hm8]
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  by_cases hs : Perm.sign c = 1
  · exact ⟨c, (Perm.mem_alternatingGroup).mpr hs, hc⟩
  · refine ⟨swap 0 1 * c, ?_, ?_⟩
    · rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (by decide)]
      have := Int.units_eq_one_or (Perm.sign c)
      rcases this with h | h
      · exact absurd h hs
      · rw [h]
        decide
    · have hcomm : swap (0 : Fin 9) 1 * encPerm mW * (swap 0 1)⁻¹ = encPerm mW := by decide
      rw [mul_inv_rev, show swap 0 1 * c * σ * (c⁻¹ * (swap (0 : Fin 9) 1)⁻¹) =
        swap 0 1 * (c * σ * c⁻¹) * (swap 0 1)⁻¹ by group, hc, hcomm]

theorem exists_conj_coord [Finite X] (hφ : Function.Surjective φ) {s : X} (hs : s ∈ H)
    (hs2 : s * s = 1) (h8 : ((φ ⟨s, hs⟩).1 : Perm (Fin 9)).support.card = 8) :
    ∃ c ∈ H, c * s * c⁻¹ = F.κ (Multiplicative.ofAdd mW) ∨
      c * s * c⁻¹ = F.κ (Multiplicative.ofAdd sW) := by
  set σ : Perm (Fin 9) := ((φ ⟨s, hs⟩).1 : Perm (Fin 9)) with hσ
  have hσ2 : σ * σ = 1 := by
    have : φ ⟨s, hs⟩ * φ ⟨s, hs⟩ = 1 := by
      rw [← phi_mul hs hs]
      have : (⟨s * s, mul_mem hs hs⟩ : ↥H) = 1 := Subtype.ext hs2
      rw [this, map_one]
    exact congrArg (fun p : A9 × Multiplicative (ZMod 2) => ((p.1 : A9) : Perm (Fin 9))) this
  obtain ⟨c₀, hc₀A, hc₀⟩ := exists_conj_mW hσ2 h8
  set e : ZMod 2 := Multiplicative.toAdd (φ ⟨s, hs⟩).2 with he
  set w : W := (1, 0, 1, 0, e) with hw
  have hy : ((⟨c₀, hc₀A⟩ : A9), (1 : Multiplicative (ZMod 2))) * φ ⟨s, hs⟩ *
      ((⟨c₀, hc₀A⟩ : A9), (1 : Multiplicative (ZMod 2)))⁻¹ = enc (Multiplicative.ofAdd w) := by
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp only [Prod.fst_mul, Prod.fst_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [enc_apply_fst, ← hσ, hc₀]
      rfl
    · simp only [Prod.snd_mul, Prod.snd_inv, one_mul, inv_one, mul_one]
      rw [enc_apply_snd]
      rfl
  obtain ⟨h, hh⟩ := hφ ((⟨c₀, hc₀A⟩ : A9), (1 : Multiplicative (ZMod 2)))
  have hsP : (h : X) * s * (h : X)⁻¹ ∈ (A₀.comap φ).map H.subtype := by
    refine mem_P_iff.mpr ⟨mul_mem (mul_mem h.2 hs) (inv_mem h.2), ?_⟩
    rw [phi_conj h.2 hs, Subtype.coe_eta, hh, hy]
    exact ⟨_, rfl⟩
  have hs2' : ((h : X) * s * (h : X)⁻¹) ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq, show (h : X) * s * (h : X)⁻¹ * ((h : X) * s * (h : X)⁻¹) =
      (h : X) * (s * s) * (h : X)⁻¹ by group, hs2, mul_one, mul_inv_cancel]
  obtain ⟨c, hcP, hcs⟩ := F.exists_conj_mem hsP hs2'
  obtain ⟨hcH, hcA⟩ := mem_P_iff.mp hcP
  obtain ⟨u, hu⟩ := hcs
  have hu' : u = Multiplicative.ofAdd w := by
    apply enc_injective
    rw [← F.phi u]
    have h1 : (⟨F.κ u, F.mem u⟩ : ↥H) = ⟨c * ((h : X) * s * (h : X)⁻¹) * c⁻¹,
        mul_mem (mul_mem hcH (mul_mem (mul_mem h.2 hs) (inv_mem h.2))) (inv_mem hcH)⟩ :=
      Subtype.ext hu
    rw [h1, phi_conj hcH (mul_mem (mul_mem h.2 hs) (inv_mem h.2)), phi_conj h.2 hs,
      Subtype.coe_eta, hh, hy, conj_A₀ hcA]
  refine ⟨c * h, mul_mem hcH h.2, ?_⟩
  have hfinal : c * h * s * (c * h)⁻¹ = F.κ (Multiplicative.ofAdd w) := by
    rw [← hu', hu]
    group
  have he01 : e = 0 ∨ e = 1 := by generalize e = e'; revert e'; decide
  rcases he01 with h0 | h1
  · left
    rw [hfinal, hw, h0]
    rfl
  · right
    rw [hfinal, hw, h1]
    rfl

theorem exists_conj_of_elem [Finite X] (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker))
    (hφt : ∀ htH : t ∈ H, φ ⟨t, htH⟩ = (1, Multiplicative.ofAdd 1))
    {B : Subgroup X} (hBH : B ≤ H) (hB2 : ∀ b ∈ B, b * b = 1) (hBcard : Nat.card B = 32)
    (htB : t ∈ B) :
    ∃ c ∈ H, B.map (MulAut.conj c).toMonoidHom = F.κ.range ∧ c * t * c⁻¹ = t := by
  have htH : t ∈ H := hBH htB
  set B' : Subgroup ↥H := B.subgroupOf H with hB'
  have hB'card : Nat.card B' = 32 := by
    rw [hB', ← hBcard]
    exact Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv
  have hinj : Function.Injective (φ.comp B'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hk : (b : ↥H) ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq]
      exact Subtype.ext (hB2 _ b.2)
    exact Subtype.ext (eq_one_of_mem_ker hodd hb hk)
  set Bbar := (φ.comp B'.subtype).range with hBbar
  have hBbarcard : Nat.card Bbar = 32 := by
    rw [hBbar, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hB'card]
  have hBbar2 : ∀ x ∈ Bbar, x * x = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (Subtype.ext (hB2 _ b.2))
    rw [this, map_one]
  have hzB : ((1 : A9), Multiplicative.ofAdd (1 : ZMod 2)) ∈ Bbar :=
    ⟨⟨⟨t, htH⟩, htB⟩, by rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hφt htH]⟩
  obtain ⟨y, hy⟩ := exists_conj_A₀ hBbar2 hBbarcard hzB
  obtain ⟨h, hh⟩ := hφ y
  set B₂ : Subgroup X := B.map (MulAut.conj (h : X)).toMonoidHom with hB₂
  have hB₂P : B₂ ≤ (A₀.comap φ).map H.subtype := by
    rintro _ ⟨b, hb, rfl⟩
    refine mem_P_iff.mpr ⟨mul_mem (mul_mem h.2 (hBH hb)) (inv_mem h.2), ?_⟩
    show φ ⟨(h : X) * b * (h : X)⁻¹, mul_mem (mul_mem h.2 (hBH hb)) (inv_mem h.2)⟩ ∈ A₀
    rw [phi_conj h.2 (hBH hb), Subtype.coe_eta, hh]
    rw [← hy]
    exact ⟨φ ⟨b, hBH hb⟩, ⟨⟨⟨b, hBH hb⟩, hb⟩, rfl⟩, rfl⟩
  have hB₂card : Nat.card B₂ = 32 := by
    rw [hB₂, ← hBcard]
    exact Nat.card_congr ((MulAut.conj (h : X)).subgroupMap B).toEquiv.symm
  obtain ⟨c, hcP, hc⟩ := F.exists_conj_eq hB₂P hB₂card
  obtain ⟨hcH, hcA⟩ := mem_P_iff.mp hcP
  refine ⟨c * h, mul_mem hcH h.2, ?_, ?_⟩
  · rw [← hc, hB₂, map_map]
    congr 1
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    group
  ·
    have hmem : c * h * t * (c * h)⁻¹ ∈ F.κ.range := by
      rw [← hc]
      refine ⟨h * t * (h : X)⁻¹, ⟨t, htB, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    obtain ⟨u, hu⟩ := hmem
    have hu' : u = Multiplicative.ofAdd tW := by
      apply enc_injective
      rw [← F.phi u, enc_tW]
      have h1 : (⟨F.κ u, F.mem u⟩ : ↥H) = ⟨c * h * t * (c * h)⁻¹,
          mul_mem (mul_mem (mul_mem hcH h.2) htH) (inv_mem (mul_mem hcH h.2))⟩ :=
        Subtype.ext hu
      rw [h1, phi_conj (mul_mem hcH h.2) htH, hφt htH]
      have hcen : ∀ q : A9 × Multiplicative (ZMod 2),
          q * ((1 : A9), Multiplicative.ofAdd (1 : ZMod 2)) * q⁻¹ =
            ((1 : A9), Multiplicative.ofAdd (1 : ZMod 2)) := by
        intro q
        refine Prod.ext ?_ ?_
        · simp
        · simp only [Prod.snd_mul, Prod.snd_inv]
          rw [mul_comm q.2, mul_assoc, mul_inv_cancel, mul_one]
      exact hcen _
    rw [← hu, hu', F.ht]

end Frame

end CFSG.ComponentClassification.SolMax.NineE32
