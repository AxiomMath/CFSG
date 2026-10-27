module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Pairs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Defs

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup

namespace BCAltThree

def edgeEnd (p : Fin 3 × Fin 2) : Fin 4 × Fin 4 :=
  (![![(0, 1), (2, 3)], ![(0, 2), (1, 3)], ![(0, 3), (1, 2)]] :
    Fin 3 → Fin 2 → Fin 4 × Fin 4) p.1 p.2

def edgeIdx (x y : Fin 4) : Fin 3 × Fin 2 :=
  (![![(0, 0), (0, 0), (1, 0), (2, 0)], ![(0, 0), (0, 0), (2, 1), (1, 1)],
    ![(1, 0), (2, 1), (0, 0), (0, 1)], ![(2, 0), (1, 1), (0, 1), (0, 0)]] :
    Fin 4 → Fin 4 → Fin 3 × Fin 2) x y

def edgeFun (g : Perm (Fin 4)) (p : Fin 3 × Fin 2) : Fin 3 × Fin 2 :=
  edgeIdx (g (edgeEnd p).1) (g (edgeEnd p).2)

theorem edgeFun_inv : ∀ g : Perm (Fin 4), ∀ p, edgeFun g⁻¹ (edgeFun g p) = p := by
  decide +kernel

def edgePerm (g : Perm (Fin 4)) : Perm (Fin 3 × Fin 2) where
  toFun := edgeFun g
  invFun := edgeFun g⁻¹
  left_inv p := edgeFun_inv g p
  right_inv p := by simpa using edgeFun_inv g⁻¹ p

theorem edgePerm_mul : ∀ g h : Perm (Fin 4), edgePerm (g * h) = edgePerm g * edgePerm h := by
  decide +kernel

def edgeHom : Perm (Fin 4) →* Perm (Fin 3 × Fin 2) :=
  MonoidHom.mk' edgePerm edgePerm_mul

theorem edgeHom_eq_one : ∀ g : Perm (Fin 4), edgeHom g = 1 → g = 1 := by
  decide +kernel

theorem edgeHom_injective : Function.Injective edgeHom :=
  (injective_iff_map_eq_one edgeHom).2 edgeHom_eq_one

theorem edgeHom_comm :
    ∀ g : Perm (Fin 4), edgeHom g * swapSecond 3 = swapSecond 3 * edgeHom g := by
  decide +kernel

theorem sign_edgeHom : ∀ g : Perm (Fin 4), sign (edgeHom g) = 1 := by
  decide +kernel

theorem cent_decomp : ∀ μ : Perm (Fin 3 × Fin 2), μ * swapSecond 3 = swapSecond 3 * μ →
    ∃ k : Perm (Fin 4), μ = edgeHom k ∨ μ = edgeHom k * swapSecond 3 := by
  decide +kernel

def pairSwap (i : Fin 3) : Perm (Fin 3 × Fin 2) := swap (i, 0) (i, 1)

theorem edgeHom_involution : ∀ g : Perm (Fin 4), sign g = 1 → g ≠ 1 → g * g = 1 →
    edgeHom g = pairSwap 1 * pairSwap 2 ∨ edgeHom g = pairSwap 0 * pairSwap 2 ∨
      edgeHom g = pairSwap 0 * pairSwap 1 := by
  decide +kernel

theorem nodup_pairs :
    ∀ i j : Fin 3, i ≠ j → [((i, 0) : Fin 3 × Fin 2), (i, 1), (j, 0), (j, 1)].Nodup := by
  decide +kernel

theorem cycleType_pairSwap_mul {i j : Fin 3} (hij : i ≠ j) :
    (pairSwap i * pairSwap j).cycleType = {2, 2} :=
  cycleType_swap_mul_swap_of_nodup (nodup_pairs i j hij)

theorem apply_inv_self' {γ : Type*} (g : Perm γ) (x : γ) : g (g⁻¹ x) = x := g.apply_symm_apply x

section ViaEmbedding

variable {α β : Type*}

theorem exists_induced (ι : α ↪ β) (ν : Perm β)
    (hν : ∀ y, ν y ∈ Set.range ι ↔ y ∈ Set.range ι) :
    ∃ μ : Perm α, ∀ a, ν (ι a) = ι (μ a) := by
  classical
  have hmem : ∀ a, ∃ b, ι b = ν (ι a) := fun a => (hν (ι a)).2 ⟨a, rfl⟩
  choose μ hμ using hmem
  have hinj : Function.Injective μ := fun a b hab =>
    ι.injective (ν.injective (by rw [← hμ a, ← hμ b, hab]))
  have hsurj : Function.Surjective μ := by
    intro b
    have h1 : ν (ν⁻¹ (ι b)) ∈ Set.range ι := by
      rw [apply_inv_self']
      exact ⟨b, rfl⟩
    obtain ⟨c, hc⟩ := (hν _).1 h1
    refine ⟨c, ι.injective ?_⟩
    rw [hμ c, hc, apply_inv_self']
  exact ⟨Equiv.ofBijective μ ⟨hinj, hsurj⟩, fun a => (hμ a).symm⟩

theorem conj_viaEmbedding (ι : α ↪ β) (ν : Perm β)
    (hν : ∀ y, ν y ∈ Set.range ι ↔ y ∈ Set.range ι) (μ : Perm α)
    (hμ : ∀ a, ν (ι a) = ι (μ a)) (g : Perm α) :
    ν * g.viaEmbedding ι * ν⁻¹ = (μ * g * μ⁻¹).viaEmbedding ι := by
  refine Equiv.Perm.ext fun y => ?_
  by_cases hy : y ∈ Set.range ι
  · obtain ⟨a, rfl⟩ := hy
    have h1 : ν⁻¹ (ι a) = ι (μ⁻¹ a) := by
      apply ν.injective
      rw [apply_inv_self', hμ, apply_inv_self']
    have e1 : g.viaEmbedding ι (ν⁻¹ (ι a)) = ι (g (μ⁻¹ a)) := by
      rw [h1, Equiv.Perm.viaEmbedding_apply]
    have e2 : (μ * g * μ⁻¹).viaEmbedding ι (ι a) = ι (μ (g (μ⁻¹ a))) :=
      (Equiv.Perm.viaEmbedding_apply (μ * g * μ⁻¹) ι a).trans rfl
    rw [Perm.mul_apply, Perm.mul_apply, e1, hμ, e2]
  · have h1 : ν⁻¹ y ∉ Set.range ι := by
      intro h
      apply hy
      have := (hν (ν⁻¹ y)).2 h
      rwa [apply_inv_self'] at this
    rw [Perm.mul_apply, Perm.mul_apply, Equiv.Perm.viaEmbedding_apply_of_notMem g ι _ h1,
      apply_inv_self', Equiv.Perm.viaEmbedding_apply_of_notMem _ ι y hy]

end ViaEmbedding

section Std

variable {n : ℕ} (h : 2 * 3 ≤ n)

@[expose] noncomputable def toSym : Perm (Fin 4) →* Perm (Fin n) :=
  (Equiv.Perm.viaEmbeddingHom (pairEmb n 3 h)).comp edgeHom

theorem toSym_eq (x : Perm (Fin 4)) :
    toSym h x = (edgeHom x).viaEmbedding (pairEmb n 3 h) := rfl

theorem toSym_apply_pair (x : Perm (Fin 4)) (p : Fin 3 × Fin 2) :
    toSym h x (pairEmb n 3 h p) = pairEmb n 3 h (edgeHom x p) :=
  Equiv.Perm.viaEmbedding_apply (edgeHom x) (pairEmb n 3 h) p

theorem toSym_apply_of_notMem (x : Perm (Fin 4)) {y : Fin n}
    (hy : y ∉ Set.range (pairEmb n 3 h)) : toSym h x y = y :=
  Equiv.Perm.viaEmbedding_apply_of_notMem (edgeHom x) (pairEmb n 3 h) y hy

theorem toSym_injective : Function.Injective (toSym h) :=
  (Equiv.Perm.viaEmbeddingHom_injective (pairEmb n 3 h)).comp edgeHom_injective

theorem sign_toSym (x : Perm (Fin 4)) : sign (toSym h x) = 1 := by
  rw [toSym_eq, Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain, sign_edgeHom]

theorem cycleType_toSym (x : Perm (Fin 4)) :
    (toSym h x).cycleType = (edgeHom x).cycleType := by
  rw [toSym_eq]
  unfold Equiv.Perm.viaEmbedding
  classical
  convert Equiv.Perm.cycleType_extendDomain
    (Equiv.ofInjective (pairEmb n 3 h).1 (pairEmb n 3 h).2) (g := edgeHom x) using 3

theorem stdInv_apply_pair' (p : Fin 3 × Fin 2) :
    stdInv n 3 h (pairEmb n 3 h p) = pairEmb n 3 h (swapSecond 3 p) := by
  rcases p with ⟨i, j⟩
  exact stdInv_apply_pair i j

theorem toSym_comm (x : Perm (Fin 4)) :
    toSym h x * stdInv n 3 h = stdInv n 3 h * toSym h x := by
  refine Equiv.Perm.ext fun y => ?_
  by_cases hy : y ∈ Set.range (pairEmb n 3 h)
  · obtain ⟨p, rfl⟩ := hy
    have hc : edgeHom x (swapSecond 3 p) = swapSecond 3 (edgeHom x p) :=
      congrArg (fun f : Perm (Fin 3 × Fin 2) => f p) (edgeHom_comm x)
    rw [Perm.mul_apply, Perm.mul_apply, stdInv_apply_pair', toSym_apply_pair, toSym_apply_pair,
      stdInv_apply_pair', hc]
  · have hy' : stdInv n 3 h y = y := stdInv_apply_of_notMem y hy
    rw [Perm.mul_apply, Perm.mul_apply, hy', toSym_apply_of_notMem h x hy, hy']

theorem toSym_conj_mem {ν : Perm (Fin n)} (hν : ν * stdInv n 3 h = stdInv n 3 h * ν)
    {x : Perm (Fin 4)} (hx : x ∈ alternatingGroup (Fin 4)) :
    ν * toSym h x * ν⁻¹ ∈ (alternatingGroup (Fin 4)).map (toSym h) := by
  have hνinv : ν⁻¹ * stdInv n 3 h = stdInv n 3 h * ν⁻¹ := (Commute.inv_left hν).eq
  have hrange : ∀ y, ν y ∈ Set.range (pairEmb n 3 h) ↔ y ∈ Set.range (pairEmb n 3 h) := by
    intro y
    constructor
    · intro hy
      simpa using mem_range_pairEmb_of_comm hνinv hy
    · intro hy
      exact mem_range_pairEmb_of_comm hν hy
  obtain ⟨μ, hμ⟩ := exists_induced (pairEmb n 3 h) ν hrange
  have hν' : ∀ z, ν (stdInv n 3 h z) = stdInv n 3 h (ν z) := fun z => by
    simpa using congrArg (fun f : Perm (Fin n) => f z) hν
  have hμS : μ * swapSecond 3 = swapSecond 3 * μ := by
    refine Equiv.Perm.ext fun p => ?_
    apply (pairEmb n 3 h).injective
    calc pairEmb n 3 h ((μ * swapSecond 3) p) = ν (pairEmb n 3 h (swapSecond 3 p)) :=
          (hμ _).symm
      _ = ν (stdInv n 3 h (pairEmb n 3 h p)) := by rw [stdInv_apply_pair']
      _ = stdInv n 3 h (ν (pairEmb n 3 h p)) := hν' _
      _ = stdInv n 3 h (pairEmb n 3 h (μ p)) := by rw [hμ]
      _ = pairEmb n 3 h (swapSecond 3 (μ p)) := stdInv_apply_pair' h _
      _ = pairEmb n 3 h ((swapSecond 3 * μ) p) := rfl
  obtain ⟨k, hk⟩ := cent_decomp μ hμS
  have hxT : edgeHom x * swapSecond 3 = swapSecond 3 * edgeHom x := edgeHom_comm x
  have hconj : μ * edgeHom x * μ⁻¹ = edgeHom (k * x * k⁻¹) := by
    rcases hk with rfl | rfl
    · simp only [map_mul, map_inv]
    · have hc : swapSecond 3 * edgeHom x * (swapSecond 3)⁻¹ = edgeHom x := by
        rw [← hxT, mul_inv_cancel_right]
      simp only [map_mul, map_inv]
      calc edgeHom k * swapSecond 3 * edgeHom x * (edgeHom k * swapSecond 3)⁻¹
          = edgeHom k * (swapSecond 3 * edgeHom x * (swapSecond 3)⁻¹) * (edgeHom k)⁻¹ := by
            group
        _ = edgeHom k * edgeHom x * (edgeHom k)⁻¹ := by rw [hc]
  have hfin : toSym h (k * x * k⁻¹) = ν * toSym h x * ν⁻¹ := by
    rw [toSym_eq h (k * x * k⁻¹), ← hconj, toSym_eq h x]
    exact (conj_viaEmbedding (pairEmb n 3 h) ν hrange μ hμ (edgeHom x)).symm
  exact ⟨k * x * k⁻¹, (inferInstance : (alternatingGroup (Fin 4)).Normal).conj_mem x hx k, hfin⟩

theorem cycleType_eq_of_mem_map {a : Perm (Fin n)}
    (ha : a ∈ (alternatingGroup (Fin 4)).map (toSym h)) (ha1 : a ≠ 1) (ha2 : a * a = 1) :
    a.cycleType = {2, 2} := by
  obtain ⟨x, hx, rfl⟩ := ha
  have hx1 : x ≠ 1 := fun e => ha1 (by rw [e, map_one])
  have hx2 : x * x = 1 := by
    apply toSym_injective h
    rw [map_mul, ha2, map_one]
  rw [cycleType_toSym]
  rcases edgeHom_involution x (Perm.mem_alternatingGroup.1 hx) hx1 hx2 with e | e | e
  · rw [e]
    exact cycleType_pairSwap_mul (by decide)
  · rw [e]
    exact cycleType_pairSwap_mul (by decide)
  · rw [e]
    exact cycleType_pairSwap_mul (by decide)

end Std

def Alt4Data {n : ℕ} (σ : Perm (Fin n)) : Prop :=
  ∃ W₀ : Subgroup (Perm (Fin n)), W₀ ≤ alternatingGroup (Fin n) ∧
    Nonempty (↥W₀ ≃* alternatingGroup (Fin 4)) ∧
    (∀ a ∈ W₀, a ≠ 1 → a * a = 1 → a.cycleType = {2, 2}) ∧ (∀ a ∈ W₀, a * σ = σ * a) ∧
    (∀ ν : Perm (Fin n), ν * σ = σ * ν → ∀ a ∈ W₀, ν * a * ν⁻¹ ∈ W₀)

theorem alt4Data_stdInv {n : ℕ} (h : 2 * 3 ≤ n) : Alt4Data (stdInv n 3 h) := by
  refine ⟨(alternatingGroup (Fin 4)).map (toSym h), ?_,
    ⟨(Subgroup.equivMapOfInjective _ (toSym h) (toSym_injective h)).symm⟩,
    fun a ha ha1 ha2 => cycleType_eq_of_mem_map h ha ha1 ha2, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact Perm.mem_alternatingGroup.2 (sign_toSym h x)
  · rintro _ ⟨x, -, rfl⟩
    exact toSym_comm h x
  · rintro ν hν _ ⟨x, hx, rfl⟩
    exact toSym_conj_mem h hν hx

theorem alt4Data_of_conj {n : ℕ} {σ σ' g : Perm (Fin n)} (hg : g * σ * g⁻¹ = σ')
    (H : Alt4Data σ') : Alt4Data σ := by
  obtain ⟨W, hWA, ⟨e⟩, hW3, hWc, hWn⟩ := H
  have hmem : ∀ a, a ∈ W.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * a * g⁻¹ ∈ W := by
    intro a
    constructor
    · rintro ⟨w, hw, rfl⟩
      have e1 : g * (MulAut.conj g⁻¹).toMonoidHom w * g⁻¹ = w := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e1]
      exact hw
    · intro ha
      refine ⟨g * a * g⁻¹, ha, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  refine ⟨W.map (MulAut.conj g⁻¹).toMonoidHom, ?_,
    ⟨(MulEquiv.subgroupMap (MulAut.conj g⁻¹) W).symm.trans e⟩, ?_, ?_, ?_⟩
  · intro a ha
    have h1 := (inferInstance : (alternatingGroup (Fin n)).Normal).conj_mem _
      (hWA ((hmem a).1 ha)) g⁻¹
    have e1 : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by group
    rwa [e1] at h1
  · intro a ha ha1 ha2
    have hw := (hmem a).1 ha
    have hw1 : g * a * g⁻¹ ≠ 1 := fun e1 => ha1 (by
      have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
      rw [this, e1]
      group)
    have hw2 : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
      calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    exact (cycleType_conj (σ := a) (τ := g)).symm.trans (hW3 _ hw hw1 hw2)
  · intro a ha
    have hw := hWc _ ((hmem a).1 ha)
    rw [← hg] at hw
    have h2 : g * (a * σ) * g⁻¹ = g * (σ * a) * g⁻¹ := by
      calc g * (a * σ) * g⁻¹ = g * a * g⁻¹ * (g * σ * g⁻¹) := by group
        _ = g * σ * g⁻¹ * (g * a * g⁻¹) := hw
        _ = g * (σ * a) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  · intro ν hν a ha
    refine (hmem _).2 ?_
    have hν' : g * ν * g⁻¹ * σ' = σ' * (g * ν * g⁻¹) := by
      rw [← hg]
      calc g * ν * g⁻¹ * (g * σ * g⁻¹) = g * (ν * σ) * g⁻¹ := by group
        _ = g * (σ * ν) * g⁻¹ := by rw [hν]
        _ = g * σ * g⁻¹ * (g * ν * g⁻¹) := by group
    have h3 := hWn _ hν' _ ((hmem a).1 ha)
    have e1 : g * (ν * a * ν⁻¹) * g⁻¹ =
        g * ν * g⁻¹ * (g * a * g⁻¹) * (g * ν * g⁻¹)⁻¹ := by group
    rw [e1]
    exact h3

end BCAltThree

open BCAltThree in
theorem exists_alt4_three {n : ℕ} {σ : Perm (Fin n)} (hσ2 : σ * σ = 1) (h3 : transCount σ = 3) :
    ∃ W₀ : Subgroup (Perm (Fin n)), W₀ ≤ alternatingGroup (Fin n) ∧
      Nonempty (↥W₀ ≃* alternatingGroup (Fin 4)) ∧
      (∀ a ∈ W₀, a ≠ 1 → a * a = 1 → a.cycleType = {2, 2}) ∧ (∀ a ∈ W₀, a * σ = σ * a) ∧
      (∀ ν : Perm (Fin n), ν * σ = σ * ν → ∀ a ∈ W₀, ν * a * ν⁻¹ ∈ W₀) := by
  have h2 : 2 ∣ σ.support.card := Equiv.Perm.two_dvd_card_support (by rw [pow_two]; exact hσ2)
  have hcard : σ.support.card = 2 * 3 := by
    have : σ.support.card / 2 = 3 := h3
    omega
  have hn : 2 * 3 ≤ n := by
    have := Finset.card_le_univ σ.support
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨g, hg⟩ := exists_conj_stdInv (h := hn) hσ2 hcard
  exact alt4Data_of_conj hg (alt4Data_stdInv hn)

end CFSG.OddStandard.Solomon75
