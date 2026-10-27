module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyOutPerm
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyOut

open Subgroup Equiv Equiv.Perm

@[expose] def restrictAut {G : Type} [Group G] (β : MulAut G) (M : Subgroup G)
    (h : M.map β.toMonoidHom = M) : MulAut ↥M :=
  (β.subgroupMap M).trans (MulEquiv.subgroupCongr h)

theorem restrictAut_apply {G : Type} [Group G] (β : MulAut G) (M : Subgroup G)
    (h : M.map β.toMonoidHom = M) (y : ↥M) : ((restrictAut β M h y : ↥M) : G) = β (y : G) := rfl

theorem card_range_conj {M : Type} [Group M] [Finite M] :
    Nat.card (MulAut.conj : M →* MulAut M).range = Nat.card (M ⧸ center M) := by
  have hker : (MulAut.conj : M →* MulAut M).ker = center M := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h y
      have := congrArg (fun φ : MulAut M => φ y) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    · intro h
      ext y
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [← h y]; group
  have e := (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivRange (MulAut.conj : M →* MulAut M))
  exact (Nat.card_congr e.toEquiv).symm


theorem aut_restrict_inner {G : Type} [Group G] (x : G) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (n : G) (hn : n * x * n⁻¹ = x⁻¹)
    [Finite ↥(centralizer ({x} : Set G))]
    (hAut : Nat.card (MulAut ↥(centralizer ({x} : Set G))) ≤
      2 * Nat.card (↥(centralizer ({x} : Set G)) ⧸ center ↥(centralizer ({x} : Set G))))
    (α : MulAut G) (hα : α x = x) :
    ∃ m ∈ centralizer ({x} : Set G), ∀ y ∈ centralizer ({x} : Set G), α y = m * y * m⁻¹ := by
  classical
  set M : Subgroup G := centralizer ({x} : Set G) with hM
  have hxM : x ∈ M := mem_centralizer_singleton_iff.mpr rfl
  have hαM : M.map α.toMonoidHom = M := by
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, hM, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hα, ← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨α.symm y, ?_, by simp⟩
      apply α.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hα]
      exact hy
  have hn' : n⁻¹ * x * n = x⁻¹ := by
    have h1 : n⁻¹ * x⁻¹ * n = x := by
      calc n⁻¹ * x⁻¹ * n = n⁻¹ * (n * x * n⁻¹) * n := by rw [hn]
        _ = x := by group
    calc n⁻¹ * x * n = (n⁻¹ * x⁻¹ * n)⁻¹ := by group
      _ = x⁻¹ := by rw [h1]
  have hnM : n ∈ normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [hM, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h3 : Commute y x⁻¹ := Commute.inv_right_iff.mpr (show Commute y x from h)
      have h2 : y * (n⁻¹ * x * n) = (n⁻¹ * x * n) * y := by rw [hn']; exact h3.eq
      calc n * y * n⁻¹ * x = n * (y * (n⁻¹ * x * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * x * n) * y) * n⁻¹ := by rw [h2]
        _ = x * (n * y * n⁻¹) := by group
    · intro h
      have h2 : y * (n⁻¹ * x * n) = (n⁻¹ * x * n) * y := by
        calc y * (n⁻¹ * x * n) = n⁻¹ * (n * y * n⁻¹ * x) * n := by group
          _ = n⁻¹ * (x * (n * y * n⁻¹)) * n := by rw [h]
          _ = (n⁻¹ * x * n) * y := by group
      rw [hn'] at h2
      have h3 : Commute y x⁻¹ := h2
      exact (Commute.inv_right_iff.mp h3).eq
  let cn : MulAut ↥M := M.normalizerMonoidHom ⟨n, hnM⟩
  have hcn : ∀ y : ↥M, ((cn y : ↥M) : G) = n * (y : G) * n⁻¹ := fun y => rfl
  let I : Subgroup (MulAut ↥M) := (MulAut.conj : ↥M →* MulAut ↥M).range
  have hx_inv : x = x⁻¹ → False := by
    intro h3
    have h4 : x ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr h3
    apply hx1
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx3, h4]; simp
  have hcI : cn ∉ I := by
    rintro ⟨m, hm⟩
    have h1 := congrArg (fun φ : MulAut ↥M => ((φ ⟨x, hxM⟩ : ↥M) : G)) hm
    simp only [MulAut.conj_apply, hcn] at h1
    have h2 : (m : G) * x * (m : G)⁻¹ = x := by
      have := mem_centralizer_singleton_iff.mp m.2
      calc (m : G) * x * (m : G)⁻¹ = x * (m : G) * (m : G)⁻¹ := by rw [this]
        _ = x := by group
    apply hx_inv
    have h5 : (m : G) * x * (m : G)⁻¹ = n * x * n⁻¹ := h1
    rw [h2, hn] at h5
    exact h5
  have hI : Nat.card I = Nat.card (↥M ⧸ center ↥M) := card_range_conj
  have hIdx : I.index ≤ 2 := by
    have h1 : Nat.card I * I.index = Nat.card (MulAut ↥M) := Subgroup.card_mul_index I
    have hpos : 0 < Nat.card I := Nat.card_pos
    by_contra hlt
    have h3 : 3 ≤ I.index := by omega
    have h4 : Nat.card I * 3 ≤ Nat.card I * I.index := Nat.mul_le_mul_left _ h3
    have h5 : Nat.card I * 3 ≤ 2 * Nat.card I :=
      calc Nat.card I * 3 ≤ Nat.card (MulAut ↥M) := h1 ▸ h4
        _ ≤ 2 * Nat.card (↥M ⧸ center ↥M) := hAut
        _ = 2 * Nat.card I := by rw [hI]
    omega
  have hidx2 : I.index = 2 := by
    have h1 : I.index ≠ 1 := fun h =>
      hcI ((Subgroup.index_eq_one.mp h) ▸ Subgroup.mem_top cn)
    have h0 : I.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx2
  have key : ∀ β : MulAut ↥M, β ∈ I ∨ β * cn⁻¹ ∈ I := by
    intro β
    by_cases hβ : β ∈ I
    · exact Or.inl hβ
    · right
      have h1 : β * a ∈ I := by
        rcases ha β with h | h
        · exact h.1
        · exact absurd h.1 hβ
      have h2 : cn * a ∈ I := by
        rcases ha cn with h | h
        · exact h.1
        · exact absurd h.1 hcI
      have := I.mul_mem h1 (I.inv_mem h2)
      simpa [mul_assoc] using this
  let αM : MulAut ↥M := restrictAut α M hαM
  have hαMx : ((αM ⟨x, hxM⟩ : ↥M) : G) = x := hα
  rcases key αM with h | h
  · obtain ⟨m, hm⟩ := h
    refine ⟨(m : G), m.2, fun y hy => ?_⟩
    have := congrArg (fun φ : MulAut ↥M => ((φ ⟨y, hy⟩ : ↥M) : G)) hm
    simpa [MulAut.conj_apply, αM, restrictAut_apply] using this.symm
  · exfalso
    obtain ⟨m, hm⟩ := h
    have hcnx : ((cn ⟨x, hxM⟩ : ↥M) : G) = x⁻¹ := by rw [hcn]; exact hn
    have h1 := congrArg (fun φ : MulAut ↥M => ((φ (cn ⟨x, hxM⟩) : ↥M) : G)) hm
    have h2 : (m : G) * x * (m : G)⁻¹ = x := by
      have := mem_centralizer_singleton_iff.mp m.2
      calc (m : G) * x * (m : G)⁻¹ = x * (m : G) * (m : G)⁻¹ := by rw [this]
        _ = x := by group
    have h3 : (αM * cn⁻¹) (cn ⟨x, hxM⟩) = αM ⟨x, hxM⟩ := by simp
    simp only [MulAut.conj_apply] at h1
    rw [h3] at h1
    have h4 : (m : G) * (cn ⟨x, hxM⟩ : G) * (m : G)⁻¹ = x := by
      have := h1
      simpa [hαMx] using this
    rw [hcnx] at h4
    apply hx_inv
    calc x = (m : G) * x⁻¹ * (m : G)⁻¹ := h4.symm
      _ = ((m : G) * x * (m : G)⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [h2]


theorem mulAut_eq_one_of_central_quot {C : Type} [Group C] (hC : Group.IsPerfect C)
    (β : MulAut C) (hβ : ∀ c : C, c⁻¹ * β c ∈ center C) : β = 1 := by
  let ζ : C →* center C :=
    { toFun := fun c => ⟨c⁻¹ * β c, hβ c⟩
      map_one' := by ext; simp
      map_mul' := fun c d => by
        apply Subtype.ext
        have hc : c⁻¹ * β c ∈ center C := hβ c
        have h1 := Subgroup.mem_center_iff.mp hc d⁻¹
        calc (c * d)⁻¹ * β (c * d) = d⁻¹ * (c⁻¹ * β c) * β d := by simp [mul_assoc]
          _ = (c⁻¹ * β c) * d⁻¹ * β d := by rw [h1]
          _ = _ := by simp [mul_assoc] }
  have hker : commutator C ≤ ζ.ker := Abelianization.commutator_subset_ker ζ
  rw [hC.commutator_eq_top] at hker
  ext c
  have : ζ c = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top c))
  have h2 : c⁻¹ * β c = 1 := congrArg Subtype.val this
  have : β c = c := by
    have := congrArg (fun z => c * z) h2
    simpa using this
  simpa using this

section Rigid

variable {G : Type} [Group G]

theorem map_centralizer_of_fix (t : G) (β : MulAut G) (hβ : β t = t) :
    (centralizer ({t} : Set G)).map β.toMonoidHom = centralizer ({t} : Set G) := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hβ, ← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨β.symm y, ?_, by simp⟩
    apply β.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hβ]
    exact hy

theorem exists_perm_of_fix {t : G} (ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11))
    (hρr : ∀ σ : Perm (Fin 11), σ ∈ ρ.range ↔ σ ∈ alternatingGroup (Fin 11))
    (hρk : ρ.ker =
      zpowers (⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({t} : Set G))))
    (β : MulAut G) (hβ : β t = t) :
    ∃ σ : Perm (Fin 11), ∀ c c' : ↥(centralizer ({t} : Set G)),
      (c' : G) = β (c : G) → ρ c' = σ * ρ c * σ⁻¹ := by
  classical
  have hβC := map_centralizer_of_fix t β hβ
  let T0 : ↥(centralizer ({t} : Set G)) := ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩
  let βC : MulAut ↥(centralizer ({t} : Set G)) := restrictAut β _ hβC
  have hβT0 : βC T0 = T0 := Subtype.ext hβ
  have hker : ∀ c : ↥(centralizer ({t} : Set G)), ρ (βC c) = 1 ↔ ρ c = 1 := by
    intro c
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hρk]
    have hmap : (zpowers T0).map βC.toMonoidHom = zpowers T0 := by
      rw [MonoidHom.map_zpowers]
      simp [hβT0]
    have h2 : βC c ∈ zpowers T0 ↔ c ∈ (zpowers T0).map βC.symm.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      simp
    have hmap' : (zpowers T0).map βC.symm.toMonoidHom = zpowers T0 := by
      rw [MonoidHom.map_zpowers]
      have : βC.symm T0 = T0 := by rw [MulEquiv.symm_apply_eq]; exact hβT0.symm
      simp [this]
    rw [hmap'] at h2
    exact h2
  obtain ⟨σ, hσ⟩ := exists_perm_conj_of_aut ρ hρr βC hker
  refine ⟨σ, fun c c' hc => ?_⟩
  have : c' = βC c := Subtype.ext hc
  rw [this]
  exact hσ c

end Rigid

section Assembly

variable {G : Type} [Group G]

theorem allInner_of_rigid [Finite G]
    (t : G) (ht : orderOf t = 2) (hfus : ∀ u : G, orderOf u = 2 → ∃ g : G, g * t * g⁻¹ = u)
    (ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11))
    (hρr : ∀ σ : Perm (Fin 11), σ ∈ ρ.range ↔ σ ∈ alternatingGroup (Fin 11))
    (hρk : ρ.ker =
      zpowers (⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({t} : Set G))))
    (hperf : Group.IsPerfect ↥(centralizer ({t} : Set G)))
    (x₁ : ↥(centralizer ({t} : Set G))) (hx3 : x₁ ^ 3 = 1)
    (hxρ : ρ x₁ = swap 0 2 * swap 0 1)
    (huniq : ∀ a b : ↥(centralizer ({t} : Set G)), a ^ 3 = 1 → b ^ 3 = 1 → ρ a = ρ b → a = b)
    (hAut : Nat.card (MulAut ↥(centralizer ({(x₁ : G)} : Set G))) ≤
      2 * Nat.card (↥(centralizer ({(x₁ : G)} : Set G)) ⧸
        center ↥(centralizer ({(x₁ : G)} : Set G))))
    (hgen : centralizer ({t} : Set G) ⊔ centralizer ({(x₁ : G)} : Set G) = ⊤)
    (α : MulAut G) : ∃ g : G, α = MulAut.conj g := by
  classical
  have hxG3 : (x₁ : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have hx1 : (x₁ : G) ≠ 1 := by
    intro h
    have h1 : x₁ = 1 := Subtype.ext h
    rw [h1, map_one] at hxρ
    exact (by decide : (1 : Perm (Fin 11)) ≠ swap 0 2 * swap 0 1) hxρ
  obtain ⟨n, hn⟩ : ∃ n : G, n * (x₁ : G) * n⁻¹ = (x₁ : G)⁻¹ := by
    have hτ : (swap 0 1 * swap 3 4 : Perm (Fin 11)) ∈ alternatingGroup (Fin 11) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    obtain ⟨c, hc⟩ := (hρr _).mpr hτ
    refine ⟨(c : G), ?_⟩
    have h1 : c * x₁ * c⁻¹ = x₁⁻¹ := by
      apply huniq
      · simp [hx3]
      · simp [hx3]
      · rw [map_mul, map_mul, map_inv, map_inv, hc, hxρ]
        decide
    have := congrArg Subtype.val h1
    simpa using this
  have htα : orderOf (α t) = 2 := by rw [MulEquiv.orderOf_eq, ht]
  obtain ⟨g₀, hg₀⟩ := hfus (α t) htα
  set α₀ : MulAut G := MulAut.conj g₀⁻¹ * α with hα₀
  have hα₀t : α₀ t = t := by
    rw [hα₀, MulAut.mul_apply, MulAut.conj_apply, ← hg₀]
    group
  obtain ⟨σ, hσ⟩ := exists_perm_of_fix ρ hρr hρk α₀ hα₀t
  have hCα₀ : (α₀ (x₁ : G)) ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h := x₁.2
    rw [mem_centralizer_singleton_iff] at h
    have h2 := congrArg α₀ h
    rwa [map_mul, map_mul, hα₀t] at h2
  set a : ↥(centralizer ({t} : Set G)) := ⟨α₀ (x₁ : G), hCα₀⟩ with ha
  have ha3 : a ^ 3 = 1 := by
    apply Subtype.ext
    show (α₀ (x₁ : G)) ^ 3 = 1
    rw [← map_pow, hxG3, map_one]
  have haρ : ρ a = σ * (swap 0 2 * swap 0 1) * σ⁻¹ := by
    rw [hσ x₁ a rfl, hxρ]
  have hcyc : (σ * (swap 0 2 * swap 0 1) * σ⁻¹ : Perm (Fin 11)).cycleType = {3} := by
    rw [Equiv.Perm.cycleType_conj]
    exact x1p_cycleType rfl
  obtain ⟨τ, hτ, hτy⟩ := exists_even_conj_x1p (x1p := swap 0 2 * swap 0 1) rfl hcyc
  obtain ⟨c, hc⟩ := (hρr τ).mpr hτ
  set α₁ : MulAut G := MulAut.conj (c : G) * α₀ with hα₁
  have hα₁t : α₁ t = t := by
    rw [hα₁, MulAut.mul_apply, hα₀t, MulAut.conj_apply]
    have := mem_centralizer_singleton_iff.mp c.2
    calc (c : G) * t * (c : G)⁻¹ = t * (c : G) * (c : G)⁻¹ := by rw [this]
      _ = t := by group
  have hα₁x : α₁ (x₁ : G) = (x₁ : G) := by
    have hb : c * a * c⁻¹ = x₁ := by
      apply huniq
      · simp [ha3]
      · exact hx3
      · rw [map_mul, map_mul, map_inv, hc, haρ, hxρ]
        simpa [mul_assoc] using hτy
    have := congrArg Subtype.val hb
    simpa [hα₁, MulAut.mul_apply, MulAut.conj_apply, ha] using this
  have hAut' : Nat.card (MulAut ↥(centralizer ({(x₁ : G)} : Set G))) ≤
      2 * Nat.card (↥(centralizer ({(x₁ : G)} : Set G)) ⧸
        center ↥(centralizer ({(x₁ : G)} : Set G))) := hAut
  obtain ⟨m, hmM, hm⟩ := aut_restrict_inner (x₁ : G) hxG3 hx1 n hn hAut' α₁ hα₁x
  set α₂ : MulAut G := MulAut.conj m⁻¹ * α₁ with hα₂
  have hα₂M : ∀ y ∈ centralizer ({(x₁ : G)} : Set G), α₂ y = y := by
    intro y hy
    rw [hα₂, MulAut.mul_apply, hm y hy, MulAut.conj_apply]
    group
  have htM : t ∈ centralizer ({(x₁ : G)} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h := x₁.2
    rw [mem_centralizer_singleton_iff] at h
    exact h.symm
  have hα₂t : α₂ t = t := hα₂M t htM
  obtain ⟨σ₂, hσ₂⟩ := exists_perm_of_fix ρ hρr hρk α₂ hα₂t
  have hcomm : ∀ a ∈ alternatingGroup (Fin 11),
      a * (swap 0 2 * swap 0 1) = (swap 0 2 * swap 0 1) * a → σ₂ * a = a * σ₂ := by
    intro a ha hax
    obtain ⟨c, hc⟩ := (hρr a).mpr ha
    have hb : c * x₁ * c⁻¹ = x₁ := by
      apply huniq
      · simp [hx3]
      · exact hx3
      · rw [map_mul, map_mul, map_inv, hc, hxρ]
        calc a * (swap 0 2 * swap 0 1) * a⁻¹ = (swap 0 2 * swap 0 1) * a * a⁻¹ := by rw [hax]
          _ = swap 0 2 * swap 0 1 := by group
    have hcM : (c : G) ∈ centralizer ({(x₁ : G)} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 := congrArg Subtype.val hb
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc (c : G) * x₁ = (c : G) * x₁ * (c : G)⁻¹ * c := by group
        _ = x₁ * c := by rw [h1]
    have h2 := hσ₂ c c (hα₂M c hcM).symm
    rw [hc] at h2
    have h3 : σ₂ * a = a * σ₂ := by
      calc σ₂ * a = (σ₂ * a * σ₂⁻¹) * σ₂ := by group
        _ = a * σ₂ := by rw [← h2]
    exact h3
  obtain ⟨k, hk0⟩ := eq_zpowers_of_commute_of_alt (x1p := swap 0 2 * swap 0 1) rfl hcomm
  have hk : (swap 0 2 * swap 0 1 : Perm (Fin 11)) ^ k = σ₂ := hk0
  set w : G := (x₁ : G) ^ k with hw
  have hxt : (x₁ : G) * t = t * (x₁ : G) := mem_centralizer_singleton_iff.mp x₁.2
  have hwt : w * t = t * w := ((show Commute (x₁ : G) t from hxt).zpow_left k).eq
  set β : MulAut G := MulAut.conj w⁻¹ * α₂ with hβ
  have hβt : β t = t := by
    rw [hβ, MulAut.mul_apply, hα₂t, MulAut.conj_apply]
    calc w⁻¹ * t * w⁻¹⁻¹ = w⁻¹ * (t * w) := by group
      _ = w⁻¹ * (w * t) := by rw [hwt]
      _ = t := by group
  have hβC := map_centralizer_of_fix t β hβt
  let wC : ↥(centralizer ({t} : Set G)) := x₁ ^ k
  have hwC : ((wC : ↥(centralizer ({t} : Set G))) : G) = w := by
    simp [wC, hw]
  have hρw : ρ wC = σ₂ := by rw [map_zpow, hxρ, hk]
  have hcenter : zpowers (⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ :
      ↥(centralizer ({t} : Set G))) ≤ center ↥(centralizer ({t} : Set G)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp y.2)
  have hβ1 : restrictAut β _ hβC = 1 := by
    apply mulAut_eq_one_of_central_quot hperf
    intro c
    apply hcenter
    rw [← hρk, MonoidHom.mem_ker, map_mul, map_inv]
    have hα₂C := map_centralizer_of_fix t α₂ hα₂t
    set d : ↥(centralizer ({t} : Set G)) := restrictAut α₂ _ hα₂C c with hd
    have hdc : ((d : ↥(centralizer ({t} : Set G))) : G) = α₂ (c : G) := rfl
    have hρd := hσ₂ c d hdc
    have hc'' : restrictAut β _ hβC c = wC⁻¹ * d * wC := by
      apply Subtype.ext
      show β (c : G) = ((wC⁻¹ * d * wC : ↥(centralizer ({t} : Set G))) : G)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hwC, hdc, hβ, MulAut.mul_apply,
        MulAut.conj_apply, inv_inv]
    rw [hc'', map_mul, map_mul, map_inv, hρd, hρw, ← hk]
    group
  have hβCfix : ∀ g ∈ centralizer ({t} : Set G), β g = g := by
    intro g hg
    have := congrArg (fun φ : MulAut ↥(centralizer ({t} : Set G)) => (φ ⟨g, hg⟩ : G)) hβ1
    simpa [restrictAut_apply] using this
  have hβMfix : ∀ y ∈ centralizer ({(x₁ : G)} : Set G), β y = y := by
    intro y hy
    rw [hβ, MulAut.mul_apply, hα₂M y hy, MulAut.conj_apply]
    have hyx : y * (x₁ : G) = (x₁ : G) * y := mem_centralizer_singleton_iff.mp hy
    have hyw : y * w = w * y := ((show Commute y (x₁ : G) from hyx).zpow_right k).eq
    calc w⁻¹ * y * w⁻¹⁻¹ = w⁻¹ * (y * w) := by group
      _ = w⁻¹ * (w * y) := by rw [hyw]
      _ = y := by group
  have hF : ∀ g : G, β g = g := by
    intro g
    let F : Subgroup G := MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id G)
    have hCF : centralizer ({t} : Set G) ≤ F := fun g hg => hβCfix g hg
    have hMF : centralizer ({(x₁ : G)} : Set G) ≤ F := fun y hy => hβMfix y hy
    have hg : g ∈ centralizer ({t} : Set G) ⊔ centralizer ({(x₁ : G)} : Set G) := by
      rw [hgen]; trivial
    exact sup_le hCF hMF hg
  refine ⟨(w⁻¹ * m⁻¹ * (c : G) * g₀⁻¹)⁻¹, ?_⟩
  ext y
  have h := hF y
  simp only [hβ, hα₂, hα₁, hα₀, MulAut.mul_apply, MulAut.conj_apply] at h
  have h' : (w⁻¹ * m⁻¹ * (c : G) * g₀⁻¹) * α y * (w⁻¹ * m⁻¹ * (c : G) * g₀⁻¹)⁻¹ = y := by
    calc (w⁻¹ * m⁻¹ * (c : G) * g₀⁻¹) * α y * (w⁻¹ * m⁻¹ * (c : G) * g₀⁻¹)⁻¹
        = w⁻¹ * (m⁻¹ * ((c : G) * (g₀⁻¹ * α y * g₀⁻¹⁻¹) * (c : G)⁻¹) * m⁻¹⁻¹) * w⁻¹⁻¹ := by group
      _ = y := h
  rw [MulAut.conj_apply]
  calc α y = (w⁻¹ * m⁻¹ * (c : G) * g₀⁻¹)⁻¹ *
        ((w⁻¹ * m⁻¹ * (c : G) * g₀⁻¹) * α y * (w⁻¹ * m⁻¹ * (c : G) * g₀⁻¹)⁻¹) *
        (w⁻¹ * m⁻¹ * (c : G) * g₀⁻¹) := by group
    _ = (w⁻¹ * m⁻¹ * (c : G) * g₀⁻¹)⁻¹ * y * (w⁻¹ * m⁻¹ * (c : G) * g₀⁻¹)⁻¹⁻¹ := by
      rw [h']; simp

end Assembly


end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyOut
