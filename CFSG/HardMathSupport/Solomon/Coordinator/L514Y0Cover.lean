module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514Y0Mat
public import CFSG.HardMathSupport.Solomon.Coordinator.L514Y0Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.L514VInnL2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open scoped commutatorElement

section Data

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {hK : PiField π p f K} {σ : K ≃+* K}

structure Y0Data (d : FrobData hK σ) where
  η : Kˣ
  e₀ : (↥d.K₀)ˣ
  hη9 : η ^ 9 = 1
  hη3 : (η : K) ^ 3 = ((e₀ : ↥d.K₀) : K)
  he3 : e₀ ^ 3 = 1
  he1 : e₀ ≠ 1
  hunit : π = false → (η : K) ^ (p ^ f + 1) = 1
  h3 : (3 : K) ≠ 0

theorem l514y0_nine_dvd_card (hK : PiField π p f K) {q₀ : ℕ} (hq : p ^ f = q₀ ^ 3)
    (h₀ : ModThree π q₀) : 9 ∣ Nat.card K - 1 ∧ (π = false → 9 ∣ p ^ f + 1) := by
  obtain ⟨h1, h2⟩ := l514y0_nine_dvd π hq h₀
  cases π
  · have hc : Nat.card K = (p ^ f) ^ 2 := by rw [hK.card, piCard, Bool.cond_false]
    have h8 := h2 rfl
    have h9 : 9 ∣ p ^ f + 1 := by omega
    refine ⟨?_, fun _ => h9⟩
    rw [hc]
    obtain ⟨m, hm⟩ := h9
    have hpos : 1 ≤ p ^ f := Nat.one_le_pow _ _ hK.prime.pos
    have : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
      zify [hpos, Nat.one_le_pow _ _ hK.prime.pos, show 1 ≤ (p ^ f) ^ 2 from Nat.one_le_pow _ _ hpos]
      ring
    rw [this, hm]
    exact ⟨m * (p ^ f - 1), by ring⟩
  · have hc : Nat.card K = p ^ f := by rw [hK.card]; rfl
    have h1' := h1 rfl
    refine ⟨?_, fun h => absurd h (by simp)⟩
    rw [hc]
    omega

theorem exists_y0Data (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (d : FrobData hK σ) :
    Nonempty (Y0Data d) := by
  have := hK.finite
  have hmod₀ := d.modThree hq
  obtain ⟨τ, hτ3, hτ1⟩ := exists_tau d.hP hmod₀
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ3
  set e₀ : (↥d.K₀)ˣ := Units.mk0 τ hτ0 with he₀
  have hζ3 : ((τ : d.K₀) : K) ^ 3 = 1 := by
    have := congrArg (fun x : d.K₀ => (x : K)) hτ3
    simpa using this
  have hζ1 : ((τ : d.K₀) : K) ≠ 1 := fun h => hτ1 (Subtype.ext (by simpa using h))
  obtain ⟨h9, h9'⟩ := l514y0_nine_dvd_card hK d.pow_eq hmod₀
  obtain ⟨η, hη9, hη3⟩ := l514y0_exists_eta h9 hζ3 hζ1
  refine ⟨⟨η, e₀, hη9, hη3, ?_, ?_, fun hf => ?_, ?_⟩⟩
  · apply Units.ext
    simpa [he₀] using hτ3
  · intro h
    apply hτ1
    have := congrArg Units.val h
    simpa [he₀] using this
  · obtain ⟨m, hm⟩ := h9' hf
    have : (η : K) ^ 9 = 1 := by simpa using congrArg Units.val hη9
    rw [hm, pow_mul, this, one_pow]
  · intro h
    have hp := hK.charP
    have h1 : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).1 (by exact_mod_cast h)
    have h2 : p = 3 := (Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_three).1 h1
    subst h2
    have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := hK.one_le; omega)
    cases π
    · change 3 ^ f % 3 = 2 at hq
      omega
    · change 3 ^ f % 3 = 1 at hq
      omega

end Data

section Elt

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {hK : PiField π p f K} {σ : K ≃+* K}

theorem l514y0_hπ (hK : PiField π p f K) : π = false → UnitaryFieldData p f K := fun h => by
  subst h; exact hK.unitary

theorem l514y0_subGL_diagE (S : Subfield K) (e : Sˣ) :
    subGL S (diagE e) = diagE (Units.map (S.subtype : S →* K) e) := by
  apply Units.ext
  rw [coe_subGL, coe_diagE, coe_diagE, Matrix.diagonal_map (map_zero _)]
  congr 1
  ext i
  fin_cases i <;> simp

theorem l514y0_eta_pow_eq {d : FrobData hK σ} (D : Y0Data d) :
    D.η ^ 3 = Units.map (d.K₀.subtype : ↥d.K₀ →* K) D.e₀ :=
  Units.ext (by simpa using D.hη3)

@[expose] noncomputable def Y0Data.elt {d : FrobData hK σ} (D : Y0Data d) :
    ↥(slPi π 3 (p ^ f) K) :=
  ⟨l514y0_D D.η, l514y0_D_mem_slPi (l514y0_hπ hK) D.hunit⟩

theorem Y0Data.coe_elt {d : FrobData hK σ} (D : Y0Data d) :
    ((D.elt : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) = l514y0_D D.η := rfl

theorem l514y0_mem_center_of_eq_scalar (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {s : ↥(slPi π 3 (p ^ f) K)}
    {c : Kˣ} (h : (s : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c) :
    s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) := by
  rw [center_slPi_eq hK hq, Subgroup.mem_subgroupOf]
  exact ⟨c, h.symm⟩

theorem l514y0_exists_scalar_of_mem_center (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {s : ↥(slPi π 3 (p ^ f) K)}
    (h : s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K)) :
    ∃ c : Kˣ, (s : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
  rw [center_slPi_eq hK hq, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.symm⟩

variable {Y : Type} [Group Y] (ν : ↥(slPi π 3 (p ^ f) K) →* Y)
  (hker : ν.ker = Subgroup.center ↥(slPi π 3 (p ^ f) K))

theorem Y0Data.elt_cube_mem_center (hq : ModThree π (p ^ f)) {d : FrobData hK σ} (D : Y0Data d) :
    D.elt ^ 3 ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) := by
  refine l514y0_mem_center_of_eq_scalar hK hq (c := D.η⁻¹ ^ 3) ?_
  rw [Subgroup.coe_pow, Y0Data.coe_elt, l514y0_D_cube D.η D.hη9]

include hker in
theorem Y0Data.nu_elt_cube (hq : ModThree π (p ^ f)) {d : FrobData hK σ} (D : Y0Data d) :
    ν D.elt ^ 3 = 1 := by
  rw [← map_pow]
  exact MonoidHom.mem_ker.1 (hker ▸ D.elt_cube_mem_center hq)

include hker in
theorem Y0Data.nu_elt_ne_one (hq : ModThree π (p ^ f)) {d : FrobData hK σ} (D : Y0Data d) :
    ν D.elt ≠ 1 := by
  intro h
  have hz : D.elt ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) := hker ▸ MonoidHom.mem_ker.2 h
  obtain ⟨c, hc⟩ := l514y0_exists_scalar_of_mem_center hK hq hz
  have h3 : D.η ^ 3 ≠ 1 := by
    intro h1
    have := D.he1
    apply this
    apply Units.ext
    apply Subtype.ext
    have e1 : (D.η : K) ^ 3 = 1 := by simpa using congrArg Units.val h1
    have := D.hη3
    rw [e1] at this
    simpa using this.symm
  exact l514y0_D_not_scalar D.η h3 c (by rw [← Y0Data.coe_elt]; exact hc)

theorem Y0Data.eta_cube_ne_one {d : FrobData hK σ} (D : Y0Data d) : D.η ^ 3 ≠ 1 := by
  intro h1
  apply D.he1
  apply Units.ext
  apply Subtype.ext
  have e1 : (D.η : K) ^ 3 = 1 := by simpa using congrArg Units.val h1
  have := D.hη3
  rw [e1] at this
  simpa using this.symm

theorem Y0Data.eta_cube_cube {d : FrobData hK σ} (D : Y0Data d) : (D.η ^ 3) ^ 3 = 1 := by
  rw [← pow_mul]; exact D.hη9

theorem Y0Data.frob_elt (hq : ModThree π (p ^ f)) {d : FrobData hK σ} (D : Y0Data d) :
    ∃ z ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K),
      frobSL hK σ D.elt = z * D.elt := by
  have hfix : σ ((D.η : K) ^ 3) = (D.η : K) ^ 3 := by
    rw [D.hη3]
    exact (d.hKσ _).1 (D.e₀ : ↥d.K₀).2
  obtain ⟨c, hc3, hc⟩ := l514y0_frobGL_D σ D.η hfix
  have hcK : (c : K) ^ 3 = 1 := by simpa using congrArg Units.val hc3
  have hmem : GeneralLinearGroup.scalar (Fin 3) c ∈ slPi π 3 (p ^ f) K :=
    l514y0_scalar_mem_slPi (l514y0_hπ hK) hc3 (fun hf => by
      have hq' : ModThree false (p ^ f) := by subst hf; exact hq
      exact pow_succ_eq_one_of_modThree hq' hcK)
  refine ⟨⟨_, hmem⟩, l514y0_mem_center_of_eq_scalar hK hq rfl, ?_⟩
  apply Subtype.ext
  rw [coe_frobSL, Subgroup.coe_mul, Y0Data.coe_elt]
  exact hc

include hker in
theorem Y0Data.nu_frob_elt (hq : ModThree π (p ^ f)) {d : FrobData hK σ} (D : Y0Data d)
    {α : MulAut Y} (hαν : ∀ s, ν (frobSL hK σ s) = α (ν s)) : α (ν D.elt) = ν D.elt := by
  obtain ⟨z, hz, hzD⟩ := D.frob_elt hq
  rw [← hαν, hzD, map_mul, MonoidHom.mem_ker.1 (hker ▸ hz), one_mul]

include hker in
theorem Y0Data.exists_lift_commute (hq : ModThree π (p ^ f)) {d : FrobData hK σ} (D : Y0Data d)
    (hν : Function.Surjective ν) {u : Y} (hu : u * ν D.elt = ν D.elt * u) :
    ∃ s : ↥(slPi π 3 (p ^ f) K), ν s = u ∧
      Commute (s : GL (Fin 3) K) (l514y0_D D.η) := by
  obtain ⟨s, rfl⟩ := hν u
  refine ⟨s, rfl, ?_⟩
  have h1 : ν (s * D.elt * s⁻¹ * D.elt⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hu]
    group
  have h2 : s * D.elt * s⁻¹ * D.elt⁻¹ ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) :=
    hker ▸ MonoidHom.mem_ker.2 h1
  obtain ⟨c, hc⟩ := l514y0_exists_scalar_of_mem_center hK hq h2
  have hc' : (s : GL (Fin 3) K) * l514y0_D D.η * (s : GL (Fin 3) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) c * l514y0_D D.η := by
    have e : (s : GL (Fin 3) K) * l514y0_D D.η * (s : GL (Fin 3) K)⁻¹ * (l514y0_D D.η)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) c := by
      have := hc
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, Y0Data.coe_elt] using this
    calc (s : GL (Fin 3) K) * l514y0_D D.η * (s : GL (Fin 3) K)⁻¹
        = (s : GL (Fin 3) K) * l514y0_D D.η * (s : GL (Fin 3) K)⁻¹ * (l514y0_D D.η)⁻¹ *
            l514y0_D D.η := by group
      _ = GeneralLinearGroup.scalar (Fin 3) c * l514y0_D D.η := by rw [e]
  have hc1 : c = 1 := l514y0_scalar_eq_one_of_conj D.η D.h3 D.eta_cube_ne_one D.eta_cube_cube
    s c hc'
  rw [hc1, map_one, one_mul] at hc'
  have : (s : GL (Fin 3) K) * l514y0_D D.η = l514y0_D D.η * s := by
    calc (s : GL (Fin 3) K) * l514y0_D D.η
        = (s : GL (Fin 3) K) * l514y0_D D.η * (s : GL (Fin 3) K)⁻¹ * s := by group
      _ = l514y0_D D.η * s := by rw [hc']
  exact this

@[expose] noncomputable def l514y0_blockSL (d : FrobData hK σ) :
    ↥(slPi π 2 (p ^ d.f₀) d.K₀) →* ↥(slPi π 3 (p ^ d.f₀) d.K₀) where
  toFun B := ⟨blockHom (B : GL (Fin 2) d.K₀),
    blockHom_mem_slPi d.hP (slPi_le_glPi (l514y0_hπ d.hP) B.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem l514y0_coe_blockSL (d : FrobData hK σ) (B : ↥(slPi π 2 (p ^ d.f₀) d.K₀)) :
    ((l514y0_blockSL d B : ↥(slPi π 3 (p ^ d.f₀) d.K₀)) : GL (Fin 3) d.K₀) =
      blockHom (B : GL (Fin 2) d.K₀) := rfl

@[expose] noncomputable def l514y0_Φ (d : FrobData hK σ) (ν : ↥(slPi π 3 (p ^ f) K) →* Y) :
    ↥(slPi π 2 (p ^ d.f₀) d.K₀) →* Y :=
  ν.comp (d.incl.comp (l514y0_blockSL d))

theorem l514y0_commute_incl_blockSL {d : FrobData hK σ} (D : Y0Data d)
    (B : ↥(slPi π 2 (p ^ d.f₀) d.K₀)) :
    Commute ((d.incl (l514y0_blockSL d B) : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K)
      (l514y0_D D.η) := by
  rw [l514y0_commute_D_iff, l514y0_eta_pow_eq D, ← l514y0_subGL_diagE]
  have h := blockHom_commute D.e₀ (B : GL (Fin 2) d.K₀)
  have h2 := congrArg (subGL d.K₀) h
  rw [map_mul, map_mul] at h2
  exact h2

theorem Y0Data.range_le {d : FrobData hK σ} (D : Y0Data d)
    {α : MulAut Y} (hαν : ∀ s, ν (frobSL hK σ s) = α (ν s)) :
    (l514y0_Φ d ν).range ≤ fixedSub α ⊓ Subgroup.centralizer {ν D.elt} := by
  rintro _ ⟨B, rfl⟩
  have hfix : d.incl (l514y0_blockSL d B) ∈ fixSub (frobSL hK σ) := by
    rw [d.fixSub_eq]; exact ⟨_, rfl⟩
  refine ⟨?_, ?_⟩
  · show α (ν (d.incl (l514y0_blockSL d B))) = ν (d.incl (l514y0_blockSL d B))
    rw [← hαν, mem_fixSub.1 hfix]
  · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    show ν (d.incl (l514y0_blockSL d B)) * ν D.elt = ν D.elt * ν (d.incl (l514y0_blockSL d B))
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Y0Data.coe_elt]
    exact (l514y0_commute_incl_blockSL D B).eq

theorem l514y0_det_commutator_eq_one {K : Type} [Field K] (a b : GL (Fin 2) K) :
    GeneralLinearGroup.det ⁅a, b⁆ = 1 := by
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)

theorem l514y0_blockHom_entry {K : Type} [Field K] (B : GL (Fin 2) K) :
    ((blockHom B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 =
      (((GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) := by
  rw [coe_blockHom]
  simp [blockMat]

theorem l514y0_entry_commutator {K : Type} [Field K] {s₁ s₂ : GL (Fin 3) K}
    (h₁ : ∃ B : GL (Fin 2) K, blockHom B = s₁) (h₂ : ∃ B : GL (Fin 2) K, blockHom B = s₂) :
    ((⁅s₁, s₂⁆ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
  obtain ⟨B₁, rfl⟩ := h₁
  obtain ⟨B₂, rfl⟩ := h₂
  rw [← map_commutatorElement, l514y0_blockHom_entry, l514y0_det_commutator_eq_one]
  simp

include hker in
theorem Y0Data.commutator_le (hq : ModThree π (p ^ f)) {d : FrobData hK σ} (D : Y0Data d)
    (hν : Function.Surjective ν) {α : MulAut Y}
    (hαν : ∀ s, ν (frobSL hK σ s) = α (ν s)) :
    ⁅fixedSub α ⊓ Subgroup.centralizer {ν D.elt}, fixedSub α ⊓ Subgroup.centralizer {ν D.elt}⁆ ≤
      (l514y0_Φ d ν).range := by
  rw [Subgroup.commutator_le]
  intro u₁ hu₁ u₂ hu₂
  obtain ⟨s₁, hs₁, hc₁⟩ := D.exists_lift_commute ν hker hq hν
    (Subgroup.mem_centralizer_singleton_iff.1 hu₁.2)
  obtain ⟨s₂, hs₂, hc₂⟩ := D.exists_lift_commute ν hker hq hν
    (Subgroup.mem_centralizer_singleton_iff.1 hu₂.2)
  have hf₁ : ν s₁ ∈ fixSubgroup α := by
    show α (ν s₁) = ν s₁
    rw [hs₁]; exact hu₁.1
  have hf₂ : ν s₂ ∈ fixSubgroup α := by
    show α (ν s₂) = ν s₂
    rw [hs₂]; exact hu₂.1
  have hcomm : ⁅s₁, s₂⁆ ∈ fixSubgroup (frobSL hK σ) :=
    comm_mem_fixSubgroup ν hker.le (frobSL hK σ) α hαν hf₁ hf₂
  have hcomm' : ⁅s₁, s₂⁆ ∈ fixSub (frobSL hK σ) := hcomm
  rw [d.fixSub_eq] at hcomm'
  obtain ⟨t, ht⟩ := hcomm'
  have hGL : ((⁅s₁, s₂⁆ : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
      ⁅(s₁ : GL (Fin 3) K), (s₂ : GL (Fin 3) K)⁆ := by
    simp [commutatorElement_def]
  have hcD : Commute ((⁅s₁, s₂⁆ : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) (l514y0_D D.η) := by
    rw [hGL, commutatorElement_def]
    exact (((hc₁.mul_left hc₂).mul_left hc₁.inv_left).mul_left hc₂.inv_left)
  have hxe : (diagE (Units.map (d.K₀.subtype : ↥d.K₀ →* K) D.e₀) : GL (Fin 3) K) =
      subGL d.K₀ (diagE D.e₀) := (l514y0_subGL_diagE d.K₀ D.e₀).symm
  have htc : Commute (t : GL (Fin 3) d.K₀) (diagE D.e₀) := by
    have h1 : Commute (subGL d.K₀ (t : GL (Fin 3) d.K₀))
        (diagE (Units.map (d.K₀.subtype : ↥d.K₀ →* K) D.e₀)) := by
      rw [← l514y0_eta_pow_eq D, ← l514y0_commute_D_iff]
      have h2 : ((d.incl t : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
          subGL d.K₀ (t : GL (Fin 3) d.K₀) := d.coe_incl t
      rw [← h2, ht]
      exact hcD
    rw [hxe] at h1
    apply subGL_injective d.K₀
    rw [map_mul, map_mul]
    exact h1.eq
  have htmem : (t : GL (Fin 3) d.K₀) ∈ slPi π 3 (p ^ d.f₀) d.K₀ ⊓
      Subgroup.centralizer {diagE D.e₀} :=
    ⟨t.2, Subgroup.mem_centralizer_singleton_iff.2 htc.eq⟩
  rw [centralizer_diagE_eq d.hP D.he1] at htmem
  obtain ⟨B, hB, hBt⟩ := htmem
  have hdiag : ∀ s : ↥(slPi π 3 (p ^ f) K), Commute (s : GL (Fin 3) K) (l514y0_D D.η) →
      ∃ B : GL (Fin 2) K, blockHom B = (s : GL (Fin 3) K) := by
    intro s hs
    have hmem : (s : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagE (D.η ^ 3)} :=
      ⟨s.2, Subgroup.mem_centralizer_singleton_iff.2 ((l514y0_commute_D_iff D.η _).1 hs).eq⟩
    rw [centralizer_diagE_eq hK D.eta_cube_ne_one] at hmem
    obtain ⟨B, -, hB⟩ := hmem
    exact ⟨B, hB⟩
  have h00 : ((⁅(s₁ : GL (Fin 3) K), (s₂ : GL (Fin 3) K)⁆ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 0 = 1 :=
    l514y0_entry_commutator (hdiag s₁ hc₁) (hdiag s₂ hc₂)
  have hent : ((⁅(s₁ : GL (Fin 3) K), (s₂ : GL (Fin 3) K)⁆ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 0 =
      (((t : GL (Fin 3) d.K₀) : Matrix (Fin 3) (Fin 3) d.K₀) 0 0 : K) := by
    rw [← hGL, ← ht, d.coe_incl, coe_subGL]
    rfl
  rw [h00, ← hBt, coe_blockHom] at hent
  have hdet : ((GeneralLinearGroup.det B)⁻¹ : (↥d.K₀)ˣ) = 1 := by
    apply Units.ext
    apply Subtype.ext
    simp only [blockMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one] at hent
    simpa using hent.symm
  have hBdet : GeneralLinearGroup.det B = 1 := inv_eq_one.1 hdet
  have hBsl : B ∈ slPi π 2 (p ^ d.f₀) d.K₀ := by
    rw [mem_slPi_iff (l514y0_hπ d.hP)]
    refine ⟨hB, ?_⟩
    have := congrArg Units.val hBdet
    simpa [GeneralLinearGroup.val_det_apply] using this
  refine ⟨⟨B, hBsl⟩, ?_⟩
  show ν (d.incl (l514y0_blockSL d ⟨B, hBsl⟩)) = ⁅u₁, u₂⁆
  have : d.incl (l514y0_blockSL d ⟨B, hBsl⟩) = ⁅s₁, s₂⁆ := by
    rw [← ht]
    congr 1
    apply Subtype.ext
    rw [l514y0_coe_blockSL]
    exact hBt
  rw [this, map_commutatorElement, hs₁, hs₂]

@[expose] def l514y0_diag2 {K : Type} [Field K] (a b : Kˣ) : GL (Fin 2) K :=
  ⟨Matrix.diagonal ![(a : K), b], Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K)],
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp,
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp⟩

theorem l514y0_coe_diag2 {K : Type} [Field K] (a b : Kˣ) :
    ((l514y0_diag2 a b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![(a : K), b] := rfl

theorem l514y0_diag2_mem_slPi (hπ : π = false → UnitaryFieldData p f K) {a b : Kˣ}
    (hab : (a : K) * b = 1)
    (hu : π = false → (a : K) ^ (p ^ f + 1) = 1 ∧ (b : K) ^ (p ^ f + 1) = 1) :
    l514y0_diag2 a b ∈ slPi π 2 (p ^ f) K := by
  rw [mem_slPi_iff hπ]
  refine ⟨?_, ?_⟩
  · cases π
    · have h := hπ rfl
      obtain ⟨ha, hb⟩ := hu rfl
      rw [mem_glPi_false h, l514y0_coe_diag2]
      have e1 : h.bar (a : K) * a = 1 := by rw [h.bar_apply, ← pow_succ]; exact ha
      have e2 : h.bar (b : K) * b = 1 := by rw [h.bar_apply, ← pow_succ]; exact hb
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.diagonal_apply, e1, e2]
    · exact mem_glPi_true _ _
  · rw [l514y0_coe_diag2, Matrix.det_diagonal, Fin.prod_univ_two]
    simpa using hab

theorem l514y0_diag2_pow_three {K : Type} [Field K] {a b : Kˣ} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    l514y0_diag2 a b ^ 3 = (1 : GL (Fin 2) K) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, l514y0_coe_diag2, Matrix.diagonal_pow, Units.val_one]
  have ha' : (a : K) ^ 3 = 1 := by simpa using congrArg Units.val ha
  have hb' : (b : K) ^ 3 = 1 := by simpa using congrArg Units.val hb
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [ha', hb']

theorem l514y0_two_lt (hq : ModThree π (p ^ f)) (d : FrobData hK σ)
    (hq₂ : π = false → p ^ d.f₀ ≠ 2) : 2 < p ^ d.f₀ := by
  have hmod := d.modThree hq
  have h2 : 2 ≤ p ^ d.f₀ := by
    have := Nat.one_lt_pow (Nat.pos_iff_ne_zero.1 d.hP.one_le) d.hP.prime.one_lt
    omega
  cases π
  · have := hq₂ rfl
    change p ^ d.f₀ % 3 = 2 at hmod
    omega
  · change p ^ d.f₀ % 3 = 1 at hmod
    omega

include hker in
theorem Y0Data.exists_order_three (hq : ModThree π (p ^ f)) {d : FrobData hK σ} (D : Y0Data d) :
    ∃ A : ↥(slPi π 2 (p ^ d.f₀) d.K₀), l514y0_Φ d ν A ^ 3 = 1 ∧ l514y0_Φ d ν A ≠ 1 := by
  have hπ₀ := l514y0_hπ d.hP
  have hq₀ := d.modThree hq
  have he3K : ((D.e₀ : ↥d.K₀) : ↥d.K₀) ^ 3 = 1 := by simpa using congrArg Units.val D.he3
  have hmem : l514y0_diag2 D.e₀ D.e₀⁻¹ ∈ slPi π 2 (p ^ d.f₀) d.K₀ :=
    l514y0_diag2_mem_slPi hπ₀ (by simp) (fun hf => by
      have hq₀' : ModThree false (p ^ d.f₀) := by subst hf; exact hq₀
      have h1 := pow_succ_eq_one_of_modThree hq₀' he3K
      refine ⟨h1, ?_⟩
      simp only [Units.val_inv_eq_inv_val]
      rw [inv_pow, h1, inv_one])
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [← map_pow]
    have : (⟨_, hmem⟩ : ↥(slPi π 2 (p ^ d.f₀) d.K₀)) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact l514y0_diag2_pow_three D.he3 (by rw [inv_pow, D.he3, inv_one])
    rw [this, map_one]
  · intro h1
    have hz : d.incl (l514y0_blockSL d ⟨_, hmem⟩) ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) :=
      hker ▸ MonoidHom.mem_ker.2 h1
    obtain ⟨c, hc⟩ := l514y0_exists_scalar_of_mem_center hK hq hz
    rw [d.coe_incl, l514y0_coe_blockSL] at hc
    have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hc
    have h11 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) hc
    simp only [coe_subGL, Matrix.map_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h00 h11
    rw [coe_blockHom] at h00 h11
    simp [blockMat, l514y0_coe_diag2] at h00 h11
    apply D.he1
    apply Units.ext
    apply Subtype.ext
    have : ((D.e₀ : ↥d.K₀) : K) = 1 := by rw [h11, ← h00]
    simpa using this

include hker in
theorem Y0Data.range_quasisimple (hq : ModThree π (p ^ f)) {d : FrobData hK σ}
    (hq₂ : π = false → p ^ d.f₀ ≠ 2) (D : Y0Data d) :
    CFSG.Open.IsQuasisimple ↥(l514y0_Φ d ν).range ∧
      3 ∣ Nat.card ↥(l514y0_Φ d ν).range := by
  have hq₀ := d.modThree hq
  have h2 := l514y0_two_lt hq d hq₂
  have hW := isQuasisimple_slPi_two d.hP hq₀ h2
  obtain ⟨A, hA3, hA1⟩ := D.exists_order_three ν hker hq
  refine ⟨isQuasisimple_open (CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hW
    (MonoidHom.rangeRestrict_surjective _) ⟨A, fun h => hA1 (by simpa using congrArg Subtype.val h)⟩),
    ?_⟩
  have hmem : l514y0_Φ d ν A ∈ (l514y0_Φ d ν).range := ⟨A, rfl⟩
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf (⟨_, hmem⟩ : ↥(l514y0_Φ d ν).range) = 3 :=
    orderOf_eq_prime (Subtype.ext hA3) (fun h => hA1 (congrArg Subtype.val h))
  have := orderOf_dvd_natCard (⟨_, hmem⟩ : ↥(l514y0_Φ d ν).range)
  rwa [ho] at this

end Elt

section TypeL2

alias l514y0_nonempty_barEquiv_of_surjective := l514vinn_nonempty_barEquiv_of_surjective
alias l514y0_exists_slPiTwo_proj := l514vinn_exists_slPiTwo_proj
alias l514y0_isTypeL2_of_range_slPiTwo := l514vinn_isTypeL2_of_range_slPiTwo

end TypeL2

section Cover

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {hK : PiField π p f K} {σ : K ≃+* K}
  {Y : Type} [Group Y] [Finite Y] (ν : ↥(slPi π 3 (p ^ f) K) →* Y)
  (hker : ν.ker = Subgroup.center ↥(slPi π 3 (p ^ f) K))

include hker in
theorem l514y0_cover (hq : ModThree π (p ^ f)) (d : FrobData hK σ)
    (hq₂ : π = false → p ^ d.f₀ ≠ 2) (hν : Function.Surjective ν) {α : MulAut Y}
    (hαν : ∀ s, ν (frobSL hK σ s) = α (ν s)) :
    ∃ y : Y, y ^ 3 = 1 ∧ y ≠ 1 ∧ α y = y ∧ ∃ r0 : ℕ, p ^ f = r0 ^ 3 ∧
      ∃ L : Subgroup Y, (∀ J : Subgroup Y,
        GLAPComponent 3 (fixedSub α ⊓ Subgroup.centralizer {y}) J ↔ J = L) ∧
        IsTypeL2 r0 (barOf 3 L) := by
  obtain ⟨D⟩ := exists_y0Data hK hq d
  have hq₀ := d.modThree hq
  have h2 := l514y0_two_lt hq d hq₂
  obtain ⟨hqs, h3⟩ := D.range_quasisimple ν hker hq hq₂
  have hcomp := l514y0_comp_iff (D.range_le ν hαν) (D.commutator_le ν hker hq hν hαν)
    hqs h3
  refine ⟨ν D.elt, D.nu_elt_cube ν hker hq, D.nu_elt_ne_one ν hker hq,
    D.nu_frob_elt ν hker hq hαν, p ^ d.f₀, d.pow_eq, (l514y0_Φ d ν).range, hcomp, ?_⟩
  exact l514y0_isTypeL2_of_range_slPiTwo d.hP hq₀ h2 (l514y0_Φ d ν) rfl
    (isQuasisimple_quotient_of_glaPComponent ((hcomp _).2 rfl))

end Cover




end CFSG.HardMathSupport.Solomon.Coordinator
