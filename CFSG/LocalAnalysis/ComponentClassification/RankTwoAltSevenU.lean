module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenH

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools

theorem exists_perm_four_of_fix {n : ℕ} (h : 4 ≤ n) {π : Perm (Fin n)}
    (hπ : ∀ i : Fin n, 4 ≤ (i : ℕ) → π i = i) :
    ∃ π' : Perm (Fin 4), viaEmbeddingHom (fourEmb h) π' = π := by
  have hlt : ∀ σ : Perm (Fin n), (∀ i : Fin n, 4 ≤ (i : ℕ) → σ i = i) →
      ∀ i : Fin n, (i : ℕ) < 4 → (σ i : ℕ) < 4 := by
    intro σ hσ i hi
    by_contra hge
    push Not at hge
    have := hσ (σ i) hge
    have hii : σ i = i := σ.injective this
    rw [hii] at hge
    omega
  have hπinv : ∀ i : Fin n, 4 ≤ (i : ℕ) → π⁻¹ i = i := fun i hi =>
    (Perm.inv_eq_iff_eq).mpr (hπ i hi).symm
  let f : Fin 4 → Fin 4 := fun j => ⟨π (fourEmb h j), hlt π hπ _ (by simp [fourEmb_apply])⟩
  let g : Fin 4 → Fin 4 := fun j => ⟨π⁻¹ (fourEmb h j), hlt π⁻¹ hπinv _ (by simp [fourEmb_apply])⟩
  have hemb : ∀ j : Fin 4, fourEmb h (f j) = π (fourEmb h j) := fun j => Fin.ext (by
    simp [f, fourEmb_apply])
  have hemb' : ∀ j : Fin 4, fourEmb h (g j) = π⁻¹ (fourEmb h j) := fun j => Fin.ext (by
    simp [g, fourEmb_apply])
  let π' : Perm (Fin 4) :=
    { toFun := f
      invFun := g
      left_inv := fun j => (fourEmb h).injective (by rw [hemb', hemb]; simp)
      right_inv := fun j => (fourEmb h).injective (by rw [hemb, hemb']; simp) }
  refine ⟨π', Equiv.ext fun i => ?_⟩
  by_cases hi : (i : ℕ) < 4
  · have hi' : fourEmb h ⟨i, hi⟩ = i := Fin.ext rfl
    rw [← hi', viaEmbeddingHom_apply_image]
    exact hemb ⟨i, hi⟩
  · have hnot : i ∉ Set.range (fourEmb h) := by
      rintro ⟨j, rfl⟩
      exact hi (by rw [fourEmb_apply]; exact j.2)
    rw [viaEmbeddingHom_apply_of_notMem _ _ hnot, hπ i (by omega)]

theorem p123_eq_via :
    viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 7)) (swap 1 2 * swap 2 3) = p123 := by
  rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  rfl

theorem perm_four_cases_of_commute : ∀ π' : Perm (Fin 4),
    π' * (swap 1 2 * swap 2 3) = (swap 1 2 * swap 2 3) * π' →
      π' = 1 ∨ π' = swap 1 2 * swap 2 3 ∨ π' = (swap 1 2 * swap 2 3)⁻¹ := by decide

theorem perm_cases_of_fix_of_commute {π : Perm (Fin 7)} (hπ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → π i = i)
    (hc : π * p123 = p123 * π) : π = 1 ∨ π = p123 ∨ π = p123⁻¹ := by
  obtain ⟨π', rfl⟩ := exists_perm_four_of_fix (by norm_num) hπ
  have hc' : π' * (swap 1 2 * swap 2 3) = (swap 1 2 * swap 2 3) * π' := by
    apply viaEmbeddingHom_injective (fourEmb (by norm_num : 4 ≤ 7))
    rw [map_mul (viaEmbeddingHom _) π', map_mul (viaEmbeddingHom _) _ π', p123_eq_via]
    exact hc
  rcases perm_four_cases_of_commute π' hc' with h | h | h <;> rw [h]
  · left; exact map_one _
  · right; left; exact p123_eq_via
  · right; right; rw [map_inv, p123_eq_via]

@[expose] def a012 : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 1 2, mem_alternatingGroup.mpr (by decide)⟩

theorem a012_mem_rootAlt : a012 ∈ rootAlt 7 := by
  rw [mem_rootAlt_iff (by norm_num)]
  refine ⟨swap 0 1 * swap 1 2, mem_alternatingGroup.mpr (by decide), ?_⟩
  rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  rfl

theorem restrictO_q4523 : restrictO q4523 = swap 4 5 := by
  have hst : StabO q4523 := by decide
  ext i
  by_cases hi : 4 ≤ (i : ℕ)
  · rw [restrictO_apply_of_ge hst hi]
    revert hi
    revert i
    decide
  · rw [restrictO_apply_of_lt hst (by omega)]
    revert hi
    revert i
    decide

namespace Seven

variable {G : Type} [Group G] {A B : Subgroup G}
  {ψA : A ≃* alternatingGroup (Fin 7)} {ψB : B ≃* alternatingGroup (Fin 7)}

theorem overlap (hco : AltCoords 7 A B ψA ψB)
    (hodd : Odd (Nat.card (centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G))) :
    (ψA.symm a456 : G) = (ψB.symm a456 : G) := by
  have hYT := hco.2.2.1
  have hC5B := hco.2.2.2.2.2.2.2.2
  set uA : G := (ψA.symm a456 : G) with huA
  set uB : G := (ψB.symm a456 : G) with huB
  have huB_mem : uB ∈ B := (ψB.symm a456).2
  obtain ⟨hNu, hactu⟩ := actPerm_of_stab hco (σ := a456) (by decide) (by decide)
  rw [show ((a456 : alternatingGroup (Fin 7)) : Perm (Fin 7)) = p456 from rfl, restrictO_p456]
    at hactu
  obtain ⟨hNx, hactx⟩ := actPerm_of_stab hco (σ := a4523) (by decide) (by decide)
  rw [show ((a4523 : alternatingGroup (Fin 7)) : Perm (Fin 7)) = q4523 from rfl,
    restrictO_q4523] at hactx
  have hactuB := actPerm_inner (ψB := ψB) a456
  have hkC : uA * uB⁻¹ ∈ centralizer (B : Set G) := by
    have h1 : actPerm ψB (Or.inr le_rfl)
        ⟨uA * uB⁻¹, mul_mem hNu (inv_mem (le_normalizer huB_mem))⟩ = 1 := by
      have : (⟨uA * uB⁻¹, mul_mem hNu (inv_mem (le_normalizer huB_mem))⟩ :
          normalizer (B : Set G)) = ⟨uA, hNu⟩ * (⟨uB, le_normalizer huB_mem⟩)⁻¹ := rfl
      rw [this, map_mul, map_inv, hactu, hactuB]
      exact mul_inv_cancel _
    exact (actPerm_eq_one_iff _ _ _).mp h1
  set k := uA * uB⁻¹ with hk
  set w : G := (ψA.symm a123 : G) with hw
  have hwC : w ∈ centralizer (B : Set G) := hYT ⟨ψA.symm a123, ⟨a123, a123_mem_rootAlt, rfl⟩, rfl⟩
  have hAmul : ∀ a b : alternatingGroup (Fin 7),
      ((ψA.symm (a * b) : A) : G) = (ψA.symm a : G) * (ψA.symm b : G) := fun a b => by
    rw [map_mul]; rfl
  have hAinv : ∀ a : alternatingGroup (Fin 7),
      ((ψA.symm a⁻¹ : A) : G) = ((ψA.symm a : A) : G)⁻¹ := fun a => by
    rw [map_inv]; rfl
  have huw : uA * w = w * uA := by
    rw [huA, hw, ← hAmul, ← hAmul]
    congr 2
    exact Subtype.ext (by decide)
  have huBw : uB * w = w * uB := (mem_centralizer_iff.mp hwC) uB huB_mem
  have hkw : k * w = w * k := by
    have h1 : uB⁻¹ * w = w * uB⁻¹ := by
      calc uB⁻¹ * w = uB⁻¹ * (w * uB) * uB⁻¹ := by group
        _ = uB⁻¹ * (uB * w) * uB⁻¹ := by rw [huBw]
        _ = w * uB⁻¹ := by group
    calc k * w = uA * (uB⁻¹ * w) := by rw [hk]; group
      _ = uA * w * uB⁻¹ := by rw [h1]; group
      _ = w * k := by rw [huw, hk]; group
  obtain ⟨hkN, π, hπfix, hπact⟩ := hC5B k hkC
  have hactk : actPerm ψA (Or.inr le_rfl) ⟨k, hkN⟩ = π := actPerm_eq_of _ _ _ _ fun a => by
    obtain ⟨ha, hae⟩ := hπact a
    exact hae
  have hπc : π * p123 = p123 * π := by
    have h1 := actPerm_spec ψA (Or.inr le_rfl) ⟨k, hkN⟩ (ψA.symm a123)
    have h2 : (⟨k * (ψA.symm a123 : G) * k⁻¹, (mem_normalizer_iff.mp hkN _).mp
        (ψA.symm a123).2⟩ : A) = ψA.symm a123 :=
      Subtype.ext (by show k * w * k⁻¹ = w; rw [hkw, mul_inv_cancel_right])
    rw [h2, MulEquiv.apply_symm_apply, hactk] at h1
    have h1' : p123 = π * p123 * π⁻¹ := h1
    calc π * p123 = π * p123 * π⁻¹ * π := by group
      _ = p123 * π := by rw [← h1']
  have hcases := perm_cases_of_fix_of_commute hπfix hπc
  have hπalt : π ∈ alternatingGroup (Fin 7) := by
    rcases hcases with h | h | h <;> rw [h] <;> exact mem_alternatingGroup.mpr (by decide)
  set ωa : alternatingGroup (Fin 7) := ⟨π, hπalt⟩ with hωa
  have hωroot : ωa ∈ rootAlt 7 := by
    rcases hcases with h | h | h
    · have : ωa = 1 := Subtype.ext h
      rw [this]; exact one_mem _
    · have : ωa = a123 := Subtype.ext h
      rw [this]; exact a123_mem_rootAlt
    · have : ωa = a123⁻¹ := Subtype.ext h
      rw [this]; exact inv_mem a123_mem_rootAlt
  set ω : G := (ψA.symm ωa : G) with hω
  have hωC : ω ∈ centralizer (B : Set G) := hYT ⟨ψA.symm ωa, ⟨ωa, hωroot, rfl⟩, rfl⟩
  have hωA : ω ∈ A := (ψA.symm ωa).2
  have hactω := actPerm_inner (ψB := ψA) ωa
  have hk0A : k * ω⁻¹ ∈ centralizer (A : Set G) := by
    have h1 : actPerm ψA (Or.inr le_rfl)
        ⟨k * ω⁻¹, mul_mem hkN (inv_mem (le_normalizer hωA))⟩ = 1 := by
      have : (⟨k * ω⁻¹, mul_mem hkN (inv_mem (le_normalizer hωA))⟩ : normalizer (A : Set G)) =
          ⟨k, hkN⟩ * (⟨ω, le_normalizer hωA⟩)⁻¹ := rfl
      rw [this, map_mul, map_inv, hactk, hactω]
      exact mul_inv_cancel _
    exact (actPerm_eq_one_iff _ _ _).mp h1
  have hk0B : k * ω⁻¹ ∈ centralizer (B : Set G) := mul_mem hkC (inv_mem hωC)
  set k₀ := k * ω⁻¹ with hk₀
  have hkk : k = k₀ * ω := by rw [hk₀]; group
  set xq : G := (ψA.symm a4523 : G) with hxq
  have hxqA : xq ∈ A := (ψA.symm a4523).2
  have hconjA : ∀ a b : alternatingGroup (Fin 7), a * b * a⁻¹ = b⁻¹ →
      (ψA.symm a : G) * (ψA.symm b : G) * (ψA.symm a : G)⁻¹ = (ψA.symm b : G)⁻¹ := by
    intro a b h
    rw [← hAinv, ← hAmul, ← hAmul, h, hAinv]
  have hxu : xq * uA * xq⁻¹ = uA⁻¹ := hconjA _ _ (Subtype.ext (by decide))
  have hxω : xq * ω * xq⁻¹ = ω⁻¹ := hconjA _ _ (Subtype.ext (by
    rcases hcases with h | h | h <;>
      simp only [hωa, Subgroup.coe_mul, Subgroup.coe_inv, h] <;> decide))
  have hxk₀ : xq * k₀ * xq⁻¹ = k₀ := by
    rw [(mem_centralizer_iff.mp hk0A) xq hxqA, mul_inv_cancel_right]
  have hBconj : ∀ (y : normalizer (B : Set G)) (σ : Perm (Fin 7)),
      actPerm ψB (Or.inr le_rfl) y = σ → ∀ b c : alternatingGroup (Fin 7),
        σ * (b : Perm (Fin 7)) * σ⁻¹ = c →
          (y : G) * (ψB.symm b : G) * (y : G)⁻¹ = (ψB.symm c : G) := by
    intro y σ hy b c hbc
    have h1 := actPerm_spec ψB (Or.inr le_rfl) y (ψB.symm b)
    rw [hy, MulEquiv.apply_symm_apply, hbc] at h1
    have h2 : ψB ⟨(y : G) * (ψB.symm b : G) * (y : G)⁻¹, _⟩ = c := Subtype.ext h1
    have h3 := congrArg (fun z => ((ψB.symm z : B) : G)) h2
    simpa using h3
  have hxuB : xq * uB * xq⁻¹ = uB⁻¹ := by
    have := hBconj ⟨xq, hNx⟩ _ hactx a456 a456⁻¹ (by decide)
    rw [this, map_inv]
    rfl
  have huuB : uA * uB * uA⁻¹ = uB := hBconj ⟨uA, hNu⟩ _ hactu a456 a456 (by decide)
  have e1 : xq * k * xq⁻¹ = k⁻¹ := by
    have : xq * k * xq⁻¹ = (xq * uA * xq⁻¹) * (xq * uB * xq⁻¹)⁻¹ := by rw [hk]; group
    rw [this, hxu, hxuB, inv_inv, hk, mul_inv_rev, inv_inv]
    calc uA⁻¹ * uB = uA⁻¹ * (uA * uB * uA⁻¹) := by rw [huuB]
      _ = uB * uA⁻¹ := by group
  have e2 : xq * k * xq⁻¹ = k₀ * ω⁻¹ := by
    have : xq * k * xq⁻¹ = (xq * k₀ * xq⁻¹) * (xq * ω * xq⁻¹) := by rw [hkk]; group
    rw [this, hxk₀, hxω]
  have hk₀ω : k₀ * ω = ω * k₀ := ((mem_centralizer_iff.mp hk0A) ω hωA).symm
  have e3 : k⁻¹ = k₀⁻¹ * ω⁻¹ := by
    rw [hkk, mul_inv_rev]
    calc ω⁻¹ * k₀⁻¹ = (k₀ * ω)⁻¹ := by group
      _ = (ω * k₀)⁻¹ := by rw [hk₀ω]
      _ = k₀⁻¹ * ω⁻¹ := by group
  have hk₀sq : k₀ * k₀ = 1 := by
    have h1 : k₀ * ω⁻¹ = k₀⁻¹ * ω⁻¹ := e2.symm.trans (e1.trans e3)
    have h2 : k₀ = k₀⁻¹ := mul_right_cancel h1
    calc k₀ * k₀ = k₀ * k₀⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel k₀
  have hk₀1 : k₀ = 1 := by
    have hdvd := Subgroup.orderOf_dvd_natCard _ (mem_inf.mpr ⟨hk0A, hk0B⟩)
    have hoddo : Odd (orderOf k₀) := Odd.of_dvd_nat hodd hdvd
    have hd2 : orderOf k₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hk₀sq)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hoddo
      exact absurd hoddo (by decide)
  have hkω : k = ω := by rw [hkk, hk₀1, one_mul]
  have huB' : uB = ω⁻¹ * uA := by
    rw [hk] at hkω
    calc uB = (uA * uB⁻¹)⁻¹ * uA := by group
      _ = ω⁻¹ * uA := by rw [hkω]
  have hcC : (ψA.symm a012 : G) ∈ centralizer (B : Set G) :=
    hYT ⟨ψA.symm a012, ⟨a012, a012_mem_rootAlt, rfl⟩, rfl⟩
  have hc := (mem_centralizer_iff.mp hcC) uB huB_mem
  rw [huB', huA, hω, ← hAinv, ← hAmul, ← hAmul, ← hAmul] at hc
  have hc' := congrArg Subtype.val (ψA.symm.injective (Subtype.ext hc))
  have hπ1 : π = 1 := by
    rcases hcases with h | h | h
    · exact h
    · exfalso
      revert hc'
      simp only [hωa, Subgroup.coe_mul, Subgroup.coe_inv, h]
      decide
    · exfalso
      revert hc'
      simp only [hωa, Subgroup.coe_mul, Subgroup.coe_inv, h]
      decide
  have hω1 : ω = 1 := by
    rw [hω]
    have : ωa = 1 := Subtype.ext hπ1
    rw [this, map_one]
    rfl
  rw [huB', hω1, inv_one, one_mul]

end Seven

end CFSG.ComponentClassification.RankTwoAlt
