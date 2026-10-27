module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

section Elementary

variable {G : Type*} [Group G]

theorem card_le_sq_card_inf_centralizer [Finite G] {A : Subgroup G} (hA : IsElemAbelian 2 A)
    {f : G} (hfA : f ∈ Subgroup.normalizer (A : Set G)) (hf2 : f ^ 2 = 1) :
    Nat.card A ≤ Nat.card (A ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) ^ 2 := by
  have hconj : ∀ a ∈ A, f * a * f⁻¹ ∈ A := fun a ha => (Subgroup.mem_normalizer_iff.mp hfA a).mp ha
  let θ : A →* G :=
    { toFun := fun a => (a : G) * (f * a * f⁻¹)
      map_one' := by simp
      map_mul' := fun a b => by
        have hX : f * (a : G) * f⁻¹ ∈ A := hconj a a.2
        have hcm : (b : G) * (f * a * f⁻¹) = (f * a * f⁻¹) * b := IsElemAbelian.comm hA b.2 hX
        calc ((a * b : A) : G) * (f * ((a * b : A) : G) * f⁻¹)
            = a * (b * (f * a * f⁻¹)) * (f * b * f⁻¹) := by simp only [Subgroup.coe_mul]; group
          _ = (a * (f * a * f⁻¹)) * (b * (f * b * f⁻¹)) := by rw [hcm]; group }
  have hker : θ.ker = (A ⊓ Subgroup.centralizer ({f} : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    have ha2 : (a : G) ^ 2 = 1 := hA.2 a a.2
    have hainv : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)
    constructor
    · intro h
      have h' : (a : G) * (f * a * f⁻¹) = 1 := h
      have h1 : f * a * f⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h'
      rw [hainv] at h1
      refine ⟨a.2, ?_⟩
      calc (a : G) * f = f * a * f⁻¹ * f := by rw [h1]
        _ = f * a := by group
    · rintro ⟨-, h⟩
      have h' : (a : G) * f = f * a := h
      show (a : G) * (f * a * f⁻¹) = 1
      have h1 : f * (a : G) * f⁻¹ = a := by rw [← h']; group
      rw [h1]
      simpa [pow_two] using ha2
  have hrange : θ.range ≤ A ⊓ Subgroup.centralizer ({f} : Set G) := by
    rintro _ ⟨a, rfl⟩
    have hX : f * (a : G) * f⁻¹ ∈ A := hconj a a.2
    refine ⟨A.mul_mem a.2 hX, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hcm : (a : G) * (f * a * f⁻¹) = (f * a * f⁻¹) * a := IsElemAbelian.comm hA a.2 hX
    have hfX : f * (f * (a : G) * f⁻¹) * f⁻¹ = a := by
      have hff : f * f = 1 := by simpa [pow_two] using hf2
      calc f * (f * (a : G) * f⁻¹) * f⁻¹ = (f * f) * a * (f * f)⁻¹ := by group
        _ = a := by rw [hff]; simp
    have hθ : f * ((a : G) * (f * a * f⁻¹)) * f⁻¹ = (a : G) * (f * a * f⁻¹) := by
      calc f * ((a : G) * (f * a * f⁻¹)) * f⁻¹
          = (f * a * f⁻¹) * (f * (f * a * f⁻¹) * f⁻¹) := by group
        _ = (f * a * f⁻¹) * a := by rw [hfX]
        _ = (a : G) * (f * a * f⁻¹) := hcm.symm
    show (a : G) * (f * a * f⁻¹) * f = f * ((a : G) * (f * a * f⁻¹))
    calc (a : G) * (f * a * f⁻¹) * f = (f * ((a : G) * (f * a * f⁻¹)) * f⁻¹) * f := by rw [hθ]
      _ = f * ((a : G) * (f * a * f⁻¹)) := by group
  have hcard := Subgroup.card_ker_mul_card_range θ
  have h1 : Nat.card θ.ker = Nat.card (A ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h2 : Nat.card θ.range ≤ Nat.card (A ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le hrange
  rw [← hcard, h1, pow_two]
  exact Nat.mul_le_mul_left _ h2

theorem card_mul_set_mul_card_inf [Finite G] (A B : Subgroup G) :
    Nat.card ((A : Set G) * (B : Set G)) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  classical
  let product : Set G := (A : Set G) * (B : Set G)
  let : Fintype product := Fintype.ofFinite _
  let mulMap : A × B → product := fun p => ⟨(p.1 : G) * p.2, Set.mul_mem_mul p.1.2 p.2.2⟩
  have hfiber : ∀ g : product,
      Nat.card {p : A × B // mulMap p = g} = Nat.card (A ⊓ B : Subgroup G) := by
    intro g
    obtain ⟨a₀, ha₀, b₀, hb₀, hg⟩ := g.2
    refine Nat.card_congr
      { toFun := fun p => ⟨(a₀⁻¹ * p.1.1 : G), ?_⟩
        invFun := fun c => ⟨(⟨a₀ * c, A.mul_mem ha₀ c.2.1⟩, ⟨(c : G)⁻¹ * b₀,
          B.mul_mem (B.inv_mem c.2.2) hb₀⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · obtain ⟨⟨a, b⟩, hp⟩ := p
      have hab : (a : G) * b = a₀ * b₀ := by
        have := congrArg Subtype.val hp
        simpa [mulMap, ← hg] using this
      refine ⟨A.mul_mem (A.inv_mem ha₀) a.2, ?_⟩
      have : a₀⁻¹ * (a : G) = b₀ * (b : G)⁻¹ := by
        calc a₀⁻¹ * (a : G) = a₀⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = b₀ * (b : G)⁻¹ := by rw [hab]; group
      rw [this]
      exact B.mul_mem hb₀ (B.inv_mem b.2)
    · apply Subtype.ext
      simp only [mulMap]
      calc (a₀ * (c : G)) * ((c : G)⁻¹ * b₀) = a₀ * b₀ := by group
        _ = g := hg
    · rintro ⟨⟨a, b⟩, hp⟩
      have hab : (a : G) * b = a₀ * b₀ := by
        have := congrArg Subtype.val hp
        simpa [mulMap, ← hg] using this
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        simp
      · apply Subtype.ext
        have : (b : G) = (a : G)⁻¹ * (a₀ * b₀) := by rw [← hab]; group
        simp [this]
        group
    · rintro ⟨c, hc⟩
      apply Subtype.ext
      simp
  have hcard := Nat.card_congr (Equiv.sigmaFiberEquiv mulMap)
  rw [Nat.card_sigma, Nat.card_prod] at hcard
  simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] at hcard
  exact hcard

theorem card_sq_eq_and_mul_eq [Finite G] {U V R : Subgroup G} (hU : IsElemAbelian 2 U) {f : G}
    (hfU : f ∈ Subgroup.normalizer (U : Set G)) (hf2 : f ^ 2 = 1)
    (hsymm : Nat.card (V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) =
      Nat.card (U ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G))
    (hUR : U ⊓ Subgroup.centralizer ({f} : Set G) ≤ R)
    (hVR : V ⊓ Subgroup.centralizer ({f} : Set G) ≤ R)
    (hnum : Nat.card (R ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) *
      Nat.card (U ⊓ V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) ≤ Nat.card U) :
    Nat.card U = Nat.card (U ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) ^ 2 ∧
      ((U ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) : Set G) *
          ((V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) : Set G) =
        ((R ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) : Set G) ∧
      Nat.card (R ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) *
        Nat.card (U ⊓ V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) = Nat.card U := by
  set C := Subgroup.centralizer ({f} : Set G) with hC
  set Uf := U ⊓ C with hUf
  set Vf := V ⊓ C with hVf
  set Rf := R ⊓ C with hRf
  have h1 : Nat.card U ≤ Nat.card Uf ^ 2 := card_le_sq_card_inf_centralizer hU hfU hf2
  have h2 := card_mul_set_mul_card_inf Uf Vf
  have hint : Uf ⊓ Vf = U ⊓ V ⊓ C := by
    rw [hUf, hVf]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rw [hint] at h2
  have hsub : ((Uf : Set G) * (Vf : Set G)) ⊆ (Rf : Set G) := by
    rintro _ ⟨u, hu, v, hv, rfl⟩
    exact Rf.mul_mem ⟨hUR hu, hu.2⟩ ⟨hVR hv, hv.2⟩
  have h3 : Nat.card ((Uf : Set G) * (Vf : Set G)) ≤ Nat.card Rf := by
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hpos : 0 < Nat.card (U ⊓ V ⊓ C : Subgroup G) := Nat.card_pos
  have h4 : Nat.card Uf ^ 2 = Nat.card ((Uf : Set G) * (Vf : Set G)) *
      Nat.card (U ⊓ V ⊓ C : Subgroup G) := by rw [pow_two]; nth_rewrite 2 [← hsymm]; exact h2.symm
  have h5 : Nat.card ((Uf : Set G) * (Vf : Set G)) * Nat.card (U ⊓ V ⊓ C : Subgroup G) ≤
      Nat.card Rf * Nat.card (U ⊓ V ⊓ C : Subgroup G) := Nat.mul_le_mul_right _ h3
  have hU2 : Nat.card U = Nat.card Uf ^ 2 := by omega
  have hcardeq : Nat.card ((Uf : Set G) * (Vf : Set G)) = Nat.card Rf := by
    have : Nat.card Rf * Nat.card (U ⊓ V ⊓ C : Subgroup G) =
        Nat.card ((Uf : Set G) * (Vf : Set G)) * Nat.card (U ⊓ V ⊓ C : Subgroup G) := by omega
    exact (Nat.eq_of_mul_eq_mul_right hpos this).symm
  refine ⟨hU2, ?_, ?_⟩
  · apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcardeq]
    rfl
  · rw [← hcardeq, hU2]
    exact h4.symm

theorem conjR_inf_centralizer (X : Subgroup G) (x s : G) :
    conjR X x ⊓ Subgroup.centralizer ({s} : Set G) =
      conjR (X ⊓ Subgroup.centralizer ({x * s * x⁻¹} : Set G)) x := by
  ext y
  rw [mem_conjR, Subgroup.mem_inf, Subgroup.mem_inf, mem_conjR,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h
    have h' : y * s = s * y := h
    calc x * y * x⁻¹ * (x * s * x⁻¹) = x * (y * s) * x⁻¹ := by group
      _ = x * (s * y) * x⁻¹ := by rw [h']
      _ = x * s * x⁻¹ * (x * y * x⁻¹) := by group
  · intro h
    have h' : x * y * x⁻¹ * (x * s * x⁻¹) = x * s * x⁻¹ * (x * y * x⁻¹) := h
    show y * s = s * y
    calc y * s = x⁻¹ * (x * y * x⁻¹ * (x * s * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * s * x⁻¹ * (x * y * x⁻¹)) * x := by rw [h']
      _ = s * y := by group

theorem inf_centralizer_eq_conjR {X : Subgroup G} {c f : G}
    (hc : c ∈ Subgroup.normalizer (X : Set G)) :
    X ⊓ Subgroup.centralizer ({c⁻¹ * f * c} : Set G) =
      conjR (X ⊓ Subgroup.centralizer ({f} : Set G)) c := by
  ext y
  rw [mem_conjR, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  have hX : y ∈ X ↔ c * y * c⁻¹ ∈ X := Subgroup.mem_normalizer_iff.mp hc y
  refine and_congr hX ?_
  constructor
  · intro h
    have h' : y * (c⁻¹ * f * c) = (c⁻¹ * f * c) * y := h
    calc c * y * c⁻¹ * f = c * (y * (c⁻¹ * f * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * f * c) * y) * c⁻¹ := by rw [h']
      _ = f * (c * y * c⁻¹) := by group
  · intro h
    have h' : c * y * c⁻¹ * f = f * (c * y * c⁻¹) := h
    show y * (c⁻¹ * f * c) = (c⁻¹ * f * c) * y
    calc y * (c⁻¹ * f * c) = c⁻¹ * (c * y * c⁻¹ * f) * c := by group
      _ = c⁻¹ * (f * (c * y * c⁻¹)) * c := by rw [h']
      _ = (c⁻¹ * f * c) * y := by group

theorem card_inf_centralizer_conj {X : Subgroup G} {c f : G}
    (hc : c ∈ Subgroup.normalizer (X : Set G)) :
    Nat.card (X ⊓ Subgroup.centralizer ({c⁻¹ * f * c} : Set G) : Subgroup G) =
      Nat.card (X ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) := by
  rw [inf_centralizer_eq_conjR hc, card_conjR]

theorem card_inf_centralizer_sup_le [Finite G] {A B : Subgroup G} {f : G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥)
    (hfA : f ∈ Subgroup.normalizer (A : Set G)) (hfB : f ∈ Subgroup.normalizer (B : Set G)) :
    Nat.card ((A ⊔ B) ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) ≤
      Nat.card (A ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) *
        Nat.card (B ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) := by
  set C := Subgroup.centralizer ({f} : Set G) with hC
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := le_normalizer_of_commute hAB
  have hXY : ∀ y ∈ B ⊓ C, ∀ x ∈ A ⊓ C, y * x = x * y := fun y hy x hx => (hAB x hx.1 y hy.1).symm
  have hXN : A ⊓ C ≤ Subgroup.normalizer ((B ⊓ C : Subgroup G) : Set G) :=
    le_normalizer_of_commute hXY
  have hXYinf : (A ⊓ C) ⊓ (B ⊓ C) = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf inf_le_left inf_le_left
  have hle : (A ⊔ B) ⊓ C ≤ (A ⊓ C) ⊔ (B ⊓ C) := by
    rintro k ⟨hk, hkC⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hBA).mp hk
    have hkf : f * (a * b) * f⁻¹ = a * b := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hkC
      calc f * (a * b) * f⁻¹ = (a * b) * f * f⁻¹ := by rw [← this]
        _ = a * b := by group
    have ha' : f * a * f⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hfA a).mp ha
    have hb' : f * b * f⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hfB b).mp hb
    obtain ⟨h1, h2⟩ := unique_decomp hinf ha' ha hb' hb
      (by rw [← hkf]; group)
    refine Subgroup.mul_mem_sup ⟨ha, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      ⟨hb, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · calc a * f = (f * a * f⁻¹) * f := by rw [h1]
        _ = f * a := by group
    · calc b * f = (f * b * f⁻¹) * f := by rw [h2]
        _ = f * b := by group
  have h1 := card_sup_mul_card_inf hXN
  rw [hXYinf, Subgroup.card_bot, mul_one] at h1
  calc Nat.card ((A ⊔ B) ⊓ C : Subgroup G) ≤ Nat.card ((A ⊓ C) ⊔ (B ⊓ C) : Subgroup G) :=
        Subgroup.card_le_of_le hle
    _ = _ := h1

end Elementary

end CFSG.QuasithinUnique.Lin2
