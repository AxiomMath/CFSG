module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.A6Sylow
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofThreeFive
public import CFSG.LargeExtraspecial.AS35WDefs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open Equiv Subgroup CFSG.RankThree.PartTwo.Sec21

theorem le_card_sylow_alt6 : 36 ≤ Nat.card (Sylow 5 (alternatingGroup (Fin 6))) := by
  obtain ⟨h1', h2'⟩ := normalizer_index_zpowers sigma0 orderOf_sigma0
  have hN0 : Nat.card (nz sigma0) ≤ 10 := card_normalizer_sigma0_le
  rw [h1']
  by_contra hlt
  push Not at hlt
  nlinarith

theorem card_normalizer_zpowers_subgroupOf {X : Type*} [Group X] {C : Subgroup X} {k : X}
    (hk : k ∈ C) :
    Nat.card (Subgroup.normalizer ((Subgroup.zpowers (⟨k, hk⟩ : C) : Subgroup C) : Set C)) =
      Nat.card (C ⊓ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X) :
        Subgroup X) := by
  have hz : ∀ h : C, h ∈ Subgroup.zpowers (⟨k, hk⟩ : C) ↔ (h : X) ∈ Subgroup.zpowers k := by
    intro h
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hkz : ∀ y : X, y ∈ Subgroup.zpowers k → y ∈ C := by
    rintro y ⟨n, rfl⟩
    exact C.zpow_mem hk n
  have hfwd : ∀ g : Subgroup.normalizer ((Subgroup.zpowers (⟨k, hk⟩ : C) : Subgroup C) : Set C),
      ((g.1 : C) : X) ∈ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X) := by
    intro g
    have hg := Subgroup.mem_normalizer_iff.mp g.2
    show ((g.1 : C) : X) ∈ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyC := hkz y hy
      have := (hg ⟨y, hyC⟩).mp ((hz ⟨y, hyC⟩).mpr hy)
      exact (hz _).mp this
    · intro hy
      have hyC : ((g.1 : C) : X) * y * ((g.1 : C) : X)⁻¹ ∈ C := hkz _ hy
      have hy' : y ∈ C := by
        have := C.mul_mem (C.mul_mem (C.inv_mem g.1.2) hyC) g.1.2
        simpa [mul_assoc] using this
      have h2 : (⟨y, hy'⟩ : C) ∈ Subgroup.zpowers (⟨k, hk⟩ : C) := by
        refine (hg ⟨y, hy'⟩).mpr ((hz _).mpr ?_)
        simpa using hy
      exact (hz _).mp h2
  have hbwd : ∀ (y : X)
      (hy : y ∈ C ⊓ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X)),
      (⟨y, (Subgroup.mem_inf.mp hy).1⟩ : C) ∈
        Subgroup.normalizer ((Subgroup.zpowers (⟨k, hk⟩ : C) : Subgroup C) : Set C) := by
    intro y hy
    have hyN := Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hy).2
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hz, hz]
    exact hyN (h : X)
  refine Nat.card_congr
    { toFun := fun g => ⟨((g.1 : C) : X), (g.1 : C).2, hfwd g⟩
      invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩, hbwd y.1 y.2⟩
      left_inv := fun g => rfl
      right_inv := fun y => rfl }

theorem card_inf_normalizer_mul_le_of_alt6 {X : Type*} [Group X] [Finite X] {C : Subgroup X}
    (ι : alternatingGroup (Fin 6) →* X) (hι : Function.Injective ι) (hιC : ∀ g, ι g ∈ C)
    (hfac : (Nat.card C).factorization 5 = 1) {k : X} (hk : k ∈ C) (hk5 : orderOf k = 5) :
    36 * Nat.card (C ⊓ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X) :
      Subgroup X) ≤ Nat.card C := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let k' : C := ⟨k, hk⟩
  have hk'5 : orderOf k' = 5 := by rw [Subgroup.orderOf_mk, hk5]
  have hcardP : Nat.card (Subgroup.zpowers k') = 5 ^ (Nat.card C).factorization 5 := by
    rw [Nat.card_zpowers, hk'5, hfac, pow_one]
  let P0 : Sylow 5 C := Sylow.ofCard (Subgroup.zpowers k') hcardP
  have hP0 : (P0 : Subgroup C) = Subgroup.zpowers k' := rfl
  have h1 := P0.card_eq_index_normalizer
  have hP0' : (P0 : Set C) = ((Subgroup.zpowers k' : Subgroup C) : Set C) := by
    rw [← hP0]; rfl
  rw [hP0'] at h1
  have h2 := (Subgroup.normalizer ((Subgroup.zpowers k' : Subgroup C) : Set C)).card_mul_index
  rw [card_normalizer_zpowers_subgroupOf hk] at h2
  let ι' : alternatingGroup (Fin 6) →* C := ι.codRestrict C hιC
  have hι' : Function.Injective ι' := fun a b h => hι (congrArg Subtype.val h)
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := card_alt_six'
  have h360 : (360 : ℕ).factorization 5 = 1 := by
    rw [Nat.factorization_def _ (by norm_num : Nat.Prime 5)]
    decide +kernel
  let f : Sylow 5 (alternatingGroup (Fin 6)) → Sylow 5 C := fun Q =>
    Sylow.ofCard ((Q : Subgroup (alternatingGroup (Fin 6))).map ι') (by
      rw [Subgroup.card_map_of_injective hι', Sylow.card_eq_multiplicity, hA6, hfac, h360])
  have hf : Function.Injective f := by
    intro Q Q' h
    have h' : ((Q : Subgroup (alternatingGroup (Fin 6))).map ι') =
        ((Q' : Subgroup (alternatingGroup (Fin 6))).map ι') := congrArg (fun S : Sylow 5 C => (S : Subgroup C)) h
    exact Sylow.ext (Subgroup.map_injective hι' h')
  have h36 : 36 ≤ Nat.card (Sylow 5 C) :=
    le_card_sylow_alt6.trans (Nat.card_le_card_of_injective f hf)
  rw [h1] at h36
  set N := Nat.card (C ⊓ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X) :
    Subgroup X)
  calc 36 * N ≤ ((Subgroup.normalizer ((Subgroup.zpowers k' : Subgroup C) : Set C)).index) * N :=
        Nat.mul_le_mul_right _ h36
    _ = Nat.card C := by rw [mul_comm]; exact h2

theorem mem_zpowers_conj_iff {X : Type*} [Group X] (g k h : X) :
    h ∈ Subgroup.zpowers (g * k * g⁻¹) ↔ g⁻¹ * h * g ∈ Subgroup.zpowers k := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    simp only [conj_zpow]
    group
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' : k ^ n = g⁻¹ * h * g := hn
    show (g * k * g⁻¹) ^ n = h
    rw [conj_zpow, hn']
    group

theorem card_conj_data {X : Type*} [Group X] (g x k : X) :
    Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set X) ⊓
        Subgroup.normalizer ((Subgroup.zpowers (g * k * g⁻¹) : Subgroup X) : Set X) :
        Subgroup X) =
      Nat.card (Subgroup.centralizer ({x} : Set X) ⊓
        Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X) : Subgroup X) ∧
    Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set X)) =
      Nat.card (Subgroup.centralizer ({x} : Set X)) := by
  have hiffC : ∀ y : X, y ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set X) ↔
      g⁻¹ * y * g ∈ Subgroup.centralizer ({x} : Set X) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h]
        _ = x * (g⁻¹ * y * g) := by group
    · intro h
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
        _ = g * x * g⁻¹ * y := by group
  have hiffN : ∀ y : X,
      y ∈ Subgroup.normalizer ((Subgroup.zpowers (g * k * g⁻¹) : Subgroup X) : Set X) ↔
        g⁻¹ * y * g ∈ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X) := by
    intro y
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h h'
      have := h (g * h' * g⁻¹)
      rw [mem_zpowers_conj_iff, mem_zpowers_conj_iff] at this
      have e1 : g⁻¹ * (g * h' * g⁻¹) * g = h' := by group
      have e2 : g⁻¹ * (y * (g * h' * g⁻¹) * y⁻¹) * g = g⁻¹ * y * g * h' * (g⁻¹ * y * g)⁻¹ := by
        group
      rw [e1, e2] at this
      exact this
    · intro h h'
      have := h (g⁻¹ * h' * g)
      rw [mem_zpowers_conj_iff, mem_zpowers_conj_iff]
      have e2 : g⁻¹ * (y * h' * y⁻¹) * g = g⁻¹ * y * g * (g⁻¹ * h' * g) * (g⁻¹ * y * g)⁻¹ := by
        group
      rw [e2]
      exact this
  set S0 : Subgroup X := Subgroup.centralizer ({x} : Set X) ⊓
    Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X)
  have hmap1 : Subgroup.centralizer ({g * x * g⁻¹} : Set X) ⊓
      Subgroup.normalizer ((Subgroup.zpowers (g * k * g⁻¹) : Subgroup X) : Set X) =
      S0.map (MulAut.conj g).toMonoidHom := by
    ext y
    rw [Subgroup.mem_inf, hiffC, hiffN, Subgroup.mem_map]
    constructor
    · intro hy
      refine ⟨g⁻¹ * y * g, Subgroup.mem_inf.mpr hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨z, hz, rfl⟩
      have := Subgroup.mem_inf.mp hz
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
      rw [e]
      exact this
  have hmap2 : Subgroup.centralizer ({g * x * g⁻¹} : Set X) =
      (Subgroup.centralizer ({x} : Set X)).map (MulAut.conj g).toMonoidHom := by
    ext y
    rw [hiffC, Subgroup.mem_map]
    constructor
    · intro hy
      refine ⟨g⁻¹ * y * g, hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨z, hz, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
      rw [e]
      exact hz
  exact ⟨by rw [hmap1, Subgroup.card_map_of_injective (MulAut.conj g).injective],
    by rw [hmap2, Subgroup.card_map_of_injective (MulAut.conj g).injective]⟩

theorem card_conj_inf {X : Type*} [Group X] (C₀ : Subgroup X) (g k : X) :
    Nat.card ((C₀.map (MulAut.conj g).toMonoidHom) ⊓
        Subgroup.normalizer ((Subgroup.zpowers (g * k * g⁻¹) : Subgroup X) : Set X) :
        Subgroup X) =
      Nat.card (C₀ ⊓ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X) :
        Subgroup X) := by
  have hiffN : ∀ y : X,
      y ∈ Subgroup.normalizer ((Subgroup.zpowers (g * k * g⁻¹) : Subgroup X) : Set X) ↔
        g⁻¹ * y * g ∈ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X) := by
    intro y
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h h'
      have := h (g * h' * g⁻¹)
      rw [mem_zpowers_conj_iff, mem_zpowers_conj_iff] at this
      have e1 : g⁻¹ * (g * h' * g⁻¹) * g = h' := by group
      have e2 : g⁻¹ * (y * (g * h' * g⁻¹) * y⁻¹) * g = g⁻¹ * y * g * h' * (g⁻¹ * y * g)⁻¹ := by
        group
      rw [e1, e2] at this
      exact this
    · intro h h'
      have := h (g⁻¹ * h' * g)
      rw [mem_zpowers_conj_iff, mem_zpowers_conj_iff]
      have e2 : g⁻¹ * (y * h' * y⁻¹) * g = g⁻¹ * y * g * (g⁻¹ * h' * g) * (g⁻¹ * y * g)⁻¹ := by
        group
      rw [e2]
      exact this
  set S0 : Subgroup X := C₀ ⊓ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X)
  have hmap : (C₀.map (MulAut.conj g).toMonoidHom) ⊓
      Subgroup.normalizer ((Subgroup.zpowers (g * k * g⁻¹) : Subgroup X) : Set X) =
      S0.map (MulAut.conj g).toMonoidHom := by
    ext y
    rw [Subgroup.mem_inf, hiffN, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, Subgroup.mem_inf.mpr ⟨hz, ?_⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy
      have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
      rw [e] at hy
      exact hy
    · rintro ⟨z, hz, rfl⟩
      have := Subgroup.mem_inf.mp hz
      refine ⟨⟨z, this.1, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
      rw [e]
      exact this.2
  rw [hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem threeFiveData228_of_alt6' {X : Type} [Group X] [Finite X] {a : ℕ}
    (hfac : a.factorization 5 = 1)
    (hdata : ∀ x k : X, orderOf x = 3 → orderOf k = 5 → x * k = k * x →
      ∃ (x₀ g : X) (ι : alternatingGroup (Fin 6) →* X), Function.Injective ι ∧
        (∀ h, ι h ∈ Subgroup.centralizer ({x₀} : Set X)) ∧
        Nat.card (Subgroup.centralizer ({x₀} : Set X)) = a ∧
        Subgroup.centralizer ({x} : Set X) =
          (Subgroup.centralizer ({x₀} : Set X)).map (MulAut.conj g).toMonoidHom) :
    ThreeFiveData228 X := by
  intro x k hx hk hxk
  obtain ⟨x₀, g, ι, hι, hιC, hcard, hC⟩ := hdata x k hx hk hxk
  have hkC : k ∈ Subgroup.centralizer ({x} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxk.symm
  rw [hC] at hkC
  obtain ⟨k', hk'C, hk'⟩ := Subgroup.mem_map.mp hkC
  have hkk : k = g * k' * g⁻¹ := by simpa [MulAut.conj_apply] using hk'.symm
  have hk'5 : orderOf k' = 5 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) k'
    have h' : (MulAut.conj g) k' = k := hk'
    rw [← this, h', hk]
  have hfac' : (Nat.card (Subgroup.centralizer ({x₀} : Set X))).factorization 5 = 1 := by
    rw [hcard]; exact hfac
  have h36 := card_inf_normalizer_mul_le_of_alt6 ι hι hιC hfac' hk'C hk'5
  have hpos : 0 < Nat.card (Subgroup.centralizer ({x₀} : Set X) ⊓
      Subgroup.normalizer ((Subgroup.zpowers k' : Subgroup X) : Set X) : Subgroup X) :=
    Nat.card_pos
  have h1 := card_conj_inf (Subgroup.centralizer ({x₀} : Set X)) g k'
  have h2 : Nat.card ((Subgroup.centralizer ({x₀} : Set X)).map (MulAut.conj g).toMonoidHom) =
      Nat.card (Subgroup.centralizer ({x₀} : Set X)) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [hC, hkk, h1, h2]
  omega

theorem threeFiveData228_of_alt6 {X : Type} [Group X] [Finite X] (x₀ : X) {a : ℕ}
    (hconj : ∀ x : X, orderOf x = 3 → ∃ g : X, x = g * x₀ * g⁻¹)
    (hcard : Nat.card (Subgroup.centralizer ({x₀} : Set X)) = a)
    (hfac : a.factorization 5 = 1) (ι : alternatingGroup (Fin 6) →* X)
    (hι : Function.Injective ι) (hιC : ∀ g, ι g ∈ Subgroup.centralizer ({x₀} : Set X)) :
    ThreeFiveData228 X := by
  intro x k hx hk hxk
  obtain ⟨g, rfl⟩ := hconj x hx
  set k' : X := g⁻¹ * k * g with hk'
  have hkk : k = g * k' * g⁻¹ := by rw [hk']; group
  have hk'5 : orderOf k' = 5 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) k
    rw [← hk, ← this]
    simp [hk']
  have hcomm : x₀ * k' = k' * x₀ := by
    calc x₀ * k' = g⁻¹ * ((g * x₀ * g⁻¹) * k) * g := by rw [hk']; group
      _ = g⁻¹ * (k * (g * x₀ * g⁻¹)) * g := by rw [hxk]
      _ = k' * x₀ := by rw [hk']; group
  have hk'C : k' ∈ Subgroup.centralizer ({x₀} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  obtain ⟨h1, h2⟩ := card_conj_data g x₀ k'
  rw [← hkk] at h1
  rw [h1, h2]
  have hfac' : (Nat.card (Subgroup.centralizer ({x₀} : Set X))).factorization 5 = 1 := by
    rw [hcard]; exact hfac
  have h36 := card_inf_normalizer_mul_le_of_alt6 ι hι hιC hfac' hk'C hk'5
  have hpos : 0 < Nat.card (Subgroup.centralizer ({x₀} : Set X) ⊓
      Subgroup.normalizer ((Subgroup.zpowers k' : Subgroup X) : Set X) : Subgroup X) :=
    Nat.card_pos
  omega

theorem threeFiveData228_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : ThreeFiveData228 S) : ThreeFiveData228 T := by
  intro x k hx hk hxk
  set x' : S := e.symm x with hx'
  set k' : S := e.symm k with hk'
  have hxe : x = e x' := by simp [hx']
  have hke : k = e k' := by simp [hk']
  have hx3 : orderOf x' = 3 := by rw [hx', MulEquiv.orderOf_eq]; exact hx
  have hk5 : orderOf k' = 5 := by rw [hk', MulEquiv.orderOf_eq]; exact hk
  have hcomm : x' * k' = k' * x' := by
    apply e.injective
    rw [map_mul, map_mul, ← hxe, ← hke]
    exact hxk
  have h1 := h x' k' hx3 hk5 hcomm
  have hC : Subgroup.centralizer ({x} : Set T) =
      (Subgroup.centralizer ({x'} : Set S)).map e.toMonoidHom := by
    rw [hxe]; exact CFSG.LargeExtraspecial.AS35W.centralizer_map e x'
  have hN : Subgroup.normalizer ((Subgroup.zpowers k : Subgroup T) : Set T) =
      (Subgroup.normalizer ((Subgroup.zpowers k' : Subgroup S) : Set S)).map e.toMonoidHom := by
    rw [Subgroup.map_normalizer_eq_of_bijective _ e.bijective, hke, MonoidHom.map_zpowers]
    rfl
  have hcard : Nat.card (Subgroup.centralizer ({x} : Set T) ⊓
      Subgroup.normalizer ((Subgroup.zpowers k : Subgroup T) : Set T) : Subgroup T) =
      Nat.card (Subgroup.centralizer ({x'} : Set S) ⊓
        Subgroup.normalizer ((Subgroup.zpowers k' : Subgroup S) : Set S) : Subgroup S) := by
    rw [hC, hN, ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
      Subgroup.card_map_of_injective e.injective]
  rw [hcard, hC, Subgroup.card_map_of_injective e.injective]
  exact h1

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
