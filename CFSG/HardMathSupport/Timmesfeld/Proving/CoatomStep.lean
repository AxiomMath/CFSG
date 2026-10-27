module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreConj

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {G : Type*} [Group G]

abbrev conjSetAction (H : Subgroup G) (S : Set G)
    (hS : ∀ g ∈ H, ∀ x ∈ S, g * x * g⁻¹ ∈ S) : MulAction H S where
  smul g x := ⟨(g : G) * (x : G) * (g : G)⁻¹, hS g g.2 x x.2⟩
  one_smul x := Subtype.ext (by
    change (1 : G) * (x : G) * (1 : G)⁻¹ = x
    group)
  mul_smul a b x := Subtype.ext (by
    change ((a * b : H) : G) * (x : G) * ((a * b : H) : G)⁻¹ =
      (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group)

theorem exists_fixed_of_coprime_card {p : ℕ} (hp : p.Prime) {H : Type*} [Group H] [Finite H]
    (hH : IsPGroup p H) {Ω : Type*} [MulAction H Ω] [Finite Ω]
    (hcop : Nat.Coprime p (Nat.card Ω)) : ∃ x : Ω, ∀ h : H, h • x = x := by
  have := Fact.mk hp
  have hmod := hH.card_modEq_card_fixedPoints Ω
  by_contra hne
  have hempty : IsEmpty (MulAction.fixedPoints H Ω) :=
    ⟨fun x => hne ⟨x.1, fun h => MulAction.mem_fixedPoints.1 x.2 h⟩⟩
  rw [Nat.card_of_isEmpty (α := MulAction.fixedPoints H Ω)] at hmod
  have hdvd : p ∣ Nat.card Ω := Nat.modEq_zero_iff_dvd.1 hmod
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hdvd

theorem normalizer_GLAPPrimeCoreOf {p : ℕ} [Finite G] (hp : p.Prime) {C : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (C : Set G)) :
    y ∈ Subgroup.normalizer ((GLAPPrimeCoreOf p C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact GLAPPrimeCoreOf_conj_mem_of_mem_normalizer hp hy h
  · intro hh
    have h' := GLAPPrimeCoreOf_conj_mem_of_mem_normalizer hp (inv_mem hy) _ hh
    have e : y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h := by group
    rwa [e] at h'

theorem coprime_card_fibre [Finite G] {Z : Type*} [Group Z] (φ : G →* Z) {p : ℕ} (hp : p.Prime)
    {C : Subgroup G} {d : G} (hd : d ∈ GLAPPrimeCoreOf p C) :
    Nat.Coprime p (Nat.card {x : G // x ∈ GLAPPrimeCoreOf p C ∧ φ x = φ d}) := by
  have hmem : ∀ x : {x : G // x ∈ GLAPPrimeCoreOf p C ∧ φ x = φ d},
      d⁻¹ * (x : G) ∈ GLAPPrimeCoreOf p C ⊓ φ.ker := fun x => by
    refine Subgroup.mem_inf.2 ⟨(GLAPPrimeCoreOf p C).mul_mem ((GLAPPrimeCoreOf p C).inv_mem hd)
      x.2.1, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, x.2.2, inv_mul_cancel]
  have hmem' : ∀ y : ↥(GLAPPrimeCoreOf p C ⊓ φ.ker),
      d * (y : G) ∈ GLAPPrimeCoreOf p C ∧ φ (d * (y : G)) = φ d := fun y => by
    have hy := Subgroup.mem_inf.1 y.2
    refine ⟨(GLAPPrimeCoreOf p C).mul_mem hd hy.1, ?_⟩
    rw [map_mul, MonoidHom.mem_ker.1 hy.2, mul_one]
  have hK : Nat.card ↥(GLAPPrimeCoreOf p C ⊓ φ.ker) ∣ Nat.card ↥(GLAPPrimeCoreOf p C) :=
    Subgroup.card_dvd_of_le inf_le_left
  have hcop' : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p C ⊓ φ.ker)) :=
    Nat.Coprime.coprime_dvd_right hK (coprime_card_GLAPPrimeCoreOf hp C)
  have e : Nat.card {x : G // x ∈ GLAPPrimeCoreOf p C ∧ φ x = φ d} =
      Nat.card ↥(GLAPPrimeCoreOf p C ⊓ φ.ker) :=
    Nat.card_congr (Equiv.mk (fun x => ⟨d⁻¹ * (x : G), hmem x⟩)
      (fun y => ⟨d * (y : G), hmem' y⟩)
      (fun x => Subtype.ext (by simp)) (fun y => Subtype.ext (by simp)))
  rw [e]
  exact hcop'

theorem mem_normalizer_self_of_mem {H : Subgroup G} {g : G} (hg : g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
  · intro hx
    have e : x = g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) hx) (H.inv_mem (H.inv_mem hg))

theorem map_GLAPPrimeCoreOf_centralizer_of_coatom [Finite G] {Z : Type*} [Group Z]
    (φ : G →* Z) {p : ℕ} (hp : p.Prime) {A P : Subgroup G} (hAP : A ≤ P)
    (hP : IsPGroup p ↥P) (hcoat : IsCoatom (A.subgroupOf P))
    (hAn : ∀ g ∈ P, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hφ : ∀ b ∈ P, ∃ a ∈ A, φ b = φ a) :
    (GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G))).map φ ≤
      (GLAPPrimeCoreOf p (Subgroup.centralizer (P : Set G))).map φ := by
  have := Fact.mk hp
  intro z hz
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hz
  obtain ⟨b, hbP, hbA⟩ : ∃ b ∈ P, b ∉ A := by
    by_contra h
    have h' : ∀ x ∈ P, x ∈ A := fun x hx => by
      by_contra hxA
      exact h ⟨x, hx, hxA⟩
    apply hcoat.1
    rw [eq_top_iff]
    intro x _
    exact Subgroup.mem_subgroupOf.2 (h' x.1 x.2)
  obtain ⟨a, haA, hab⟩ := hφ b hbP
  set n : G := a⁻¹ * b with hn_def
  have hnP : n ∈ P := P.mul_mem (P.inv_mem (hAP haA)) hbP
  have hφn : φ n = 1 := by
    rw [hn_def, map_mul, map_inv, hab, inv_mul_cancel]
  have hnA : n ∉ A := by
    intro hnA
    apply hbA
    have hb : b = a * n := by rw [hn_def]; group
    rw [hb]
    exact A.mul_mem haA hnA
  have hnN : n ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hAn n hnP x
    · intro hx
      have h := hAn n⁻¹ (P.inv_mem hnP) _ hx
      have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
      rwa [e] at h
  have hnO : n ∈ Subgroup.normalizer
      ((GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) : Subgroup G) : Set G) :=
    normalizer_GLAPPrimeCoreOf hp (mem_normalizer_centralizer_of_mem_normalizer hnN)
  have hPn : IsPGroup p ↥(Subgroup.zpowers n) := by
    obtain ⟨k, hk⟩ := hP (⟨n, hnP⟩ : P)
    have hk' : n ^ (p ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk')
    exact IsPGroup.iff_card.2 ⟨j, by rw [Nat.card_zpowers, hj]⟩
  set S : Set G := {x | x ∈ GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) ∧ φ x = φ d}
    with hS_def
  have hcopS : Nat.Coprime p (Nat.card S) := coprime_card_fibre φ hp hd
  have hφg : ∀ g ∈ Subgroup.zpowers n, φ g = 1 := by
    intro g hg
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [map_zpow, hφn, one_zpow]
  have hSinv : ∀ g ∈ Subgroup.zpowers n, ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
    intro g hg x hx
    obtain ⟨hxO, hxφ⟩ := hx
    have hgN : g ∈ Subgroup.normalizer
        ((GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.2 hnO hg
    refine ⟨(Subgroup.mem_normalizer_iff.1 hgN x).1 hxO, ?_⟩
    rw [map_mul, map_mul, map_inv, hφg g hg, hxφ]
    group
  let : MulAction ↥(Subgroup.zpowers n) S := conjSetAction (Subgroup.zpowers n) S hSinv
  obtain ⟨⟨s, hsS⟩, hfixs⟩ := exists_fixed_of_coprime_card hp hPn hcopS
  have hns : n * s * n⁻¹ = s := congrArg Subtype.val (hfixs ⟨n, Subgroup.mem_zpowers n⟩)
  have hnsc : n * s = s * n := mul_inv_eq_iff_eq_mul.1 hns
  have hsCA : s ∈ Subgroup.centralizer (A : Set G) :=
    GLAPPrimeCoreOf_le _ hsS.1
  have hsA : ∀ a ∈ A, a * s = s * a := fun a ha => Subgroup.mem_centralizer_iff.1 hsCA a ha
  have hsCP : ∀ x ∈ P, x * s = s * x := centralizes_of_isCoatom hcoat hnP hnA hsA hnsc
  have hsC : s ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun h hh => hsCP h hh)
  have hgCA : ∀ g ∈ Subgroup.centralizer (P : Set G), g ∈ Subgroup.centralizer (A : Set G) :=
    fun g hg => Subgroup.mem_centralizer_iff.2 (fun a ha => Subgroup.mem_centralizer_iff.1 hg a (hAP ha))
  have hnorm : ∀ g ∈ Subgroup.centralizer (P : Set G), ∀ x ∈
      GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) ⊓ Subgroup.centralizer (P : Set G),
      g * x * g⁻¹ ∈
        GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) ⊓ Subgroup.centralizer (P : Set G) := by
    intro g hg x hx
    obtain ⟨hxO, hxC⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨GLAPPrimeCoreOf_conj_mem_of_mem_normalizer hp
      (mem_normalizer_self_of_mem (hgCA g hg)) x hxO, ?_⟩
    exact (Subgroup.centralizer (P : Set G)).mul_mem
      ((Subgroup.centralizer (P : Set G)).mul_mem hg hxC) ((Subgroup.centralizer (P : Set G)).inv_mem hg)
  have hcop' : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) ⊓
      Subgroup.centralizer (P : Set G))) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_GLAPPrimeCoreOf hp _)
  have hle := le_GLAPPrimeCoreOf_of_normal (p := p) (C := Subgroup.centralizer (P : Set G))
    inf_le_right hnorm hcop'
  have hsO : s ∈ GLAPPrimeCoreOf p (Subgroup.centralizer (P : Set G)) :=
    hle (Subgroup.mem_inf.2 ⟨hsS.1, hsC⟩)
  exact Subgroup.mem_map.2 ⟨s, hsO, hsS.2⟩

end CFSG.HardMathSupport.Timmesfeld.Proving

end
