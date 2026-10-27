module

public import CFSG.LocalAnalysis.GH72.GL42Bridge
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.LocalAnalysis.GH72.G3a
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseGen
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.LocalAnalysis.GH72.DDAut
public import CFSG.LocalAnalysis.GH72.G3bEight

public section

namespace CFSG.GH72

open Subgroup
open MulAction
open CFSG.CGT.Foote81L6 (mem_sup_iff_of_le_normalizer le_normalizer_of_comm)
open CFSG.CGT.Foote81L6.TStruct
open scoped Pointwise


theorem exists_conj_extremal_univ {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS : IsPGroup 2 S) {u v h : G}
    (hv : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ Subgroup.centralizer ({v} : Set G))
      (Subgroup.centralizer ({v} : Set G)))
    (huv : h⁻¹ * v * h = u) :
    ∃ g : G, g⁻¹ * u * g = v ∧
      ∀ c ∈ S ⊓ Subgroup.centralizer ({u} : Set G),
        g⁻¹ * c * g ∈ S ⊓ Subgroup.centralizer ({v} : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := S ⊓ Subgroup.centralizer ({u} : Set G)
  set P' : Subgroup G := P.map (MulAut.conj h).toMonoidHom
  have hP'K : P' ≤ Subgroup.centralizer ({v} : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    have hcu : c * u = u * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    change h * c * h⁻¹ * v = v * (h * c * h⁻¹)
    have hv' : v = h * u * h⁻¹ := by rw [← huv]; group
    rw [hv']
    calc h * c * h⁻¹ * (h * u * h⁻¹) = h * (c * u) * h⁻¹ := by group
      _ = h * (u * c) * h⁻¹ := by rw [hcu]
      _ = h * u * h⁻¹ * (h * c * h⁻¹) := by group
  have hP' : IsPGroup 2 P' := (hS.to_le inf_le_left).map _
  obtain ⟨c, hcK, hc⟩ :=
    CFSG.OddStandard.Seitz77.exists_conj_le_of_isSylowOf hv hP' hP'K
  refine ⟨h⁻¹ * c⁻¹, ?_, fun x hx => ?_⟩
  · have hcv : c * v = v * c := Subgroup.mem_centralizer_singleton_iff.mp hcK
    rw [← huv]
    calc (h⁻¹ * c⁻¹)⁻¹ * (h⁻¹ * v * h) * (h⁻¹ * c⁻¹) = c * v * c⁻¹ := by group
      _ = v := by rw [hcv]; group
  · have hx' : h * x * h⁻¹ ∈ P' := ⟨x, hx, rfl⟩
    have := hc (h * x * h⁻¹) hx'
    rwa [show c * (h * x * h⁻¹) * c⁻¹ =
      (h⁻¹ * c⁻¹)⁻¹ * x * (h⁻¹ * c⁻¹) by group] at this


theorem normalizer_le_centralizer_of_ambient {X : Type*} [Group X] {L P : Subgroup X}
    (hPL : P ≤ L)
    (h : Subgroup.normalizer (P : Set X) ⊓ L ≤ Subgroup.centralizer (P : Set X)) :
    Subgroup.normalizer (P.subgroupOf L : Set L) ≤
      Subgroup.centralizer (P.subgroupOf L : Set L) := by
  intro x hx
  have hxN : (x : X) ∈ Subgroup.normalizer (P : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      have hpL : p ∈ L := hPL hp
      have hq : (⟨p, hpL⟩ : L) ∈ P.subgroupOf L := hp
      have hconj := (Subgroup.mem_normalizer_iff.mp hx ⟨p, hpL⟩).mp hq
      exact hconj
    · intro hp
      have hq : (⟨x * p * x⁻¹, hPL hp⟩ : L) ∈ P.subgroupOf L := hp
      have hxinv : x⁻¹ ∈ Subgroup.normalizer (P.subgroupOf L : Set L) :=
        Subgroup.inv_mem (H := Subgroup.normalizer (P.subgroupOf L : Set L)) hx
      have := (Subgroup.mem_normalizer_iff.mp hxinv
        ⟨x * p * x⁻¹, hPL hp⟩).mp hq
      simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  have hxcent : (x : X) ∈ Subgroup.centralizer (P : Set X) := h ⟨hxN, x.2⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  apply Subtype.ext
  have hqP : (q : X) ∈ P := hq
  exact Subgroup.mem_centralizer_iff.mp hxcent (q : X) hqP



theorem transvection_conj_apply {A : Type*} [Group A] {τ x : MulAut A} {z : A}
    (h : ∀ v : A, v⁻¹ * τ v = 1 ∨ v⁻¹ * τ v = z) :
    ∀ v : A, v⁻¹ * (x * τ * x⁻¹) v = 1 ∨ v⁻¹ * (x * τ * x⁻¹) v = x z := by
  intro v
  have hv := h (x⁻¹ v)
  have hkey : v⁻¹ * (x * τ * x⁻¹) v =
      x ((x⁻¹ v)⁻¹ * τ (x⁻¹ v)) := by
    have hvx : x (x⁻¹ v) = v := by simp
    calc v⁻¹ * (x * τ * x⁻¹) v
        = (x (x⁻¹ v))⁻¹ * x (τ (x⁻¹ v)) := by
          rw [hvx]
          rfl
      _ = x ((x⁻¹ v)⁻¹ * τ (x⁻¹ v)) := by
          rw [← map_inv, ← map_mul]
  rw [hkey]
  rcases hv with h0 | hz
  · left
    rw [h0, map_one]
  · right
    rw [hz]

theorem transvection_center_unique {A : Type*} [Group A] {τ : MulAut A} {z z' : A}
    (h : ∀ v : A, v⁻¹ * τ v = 1 ∨ v⁻¹ * τ v = z)
    (h' : ∀ v : A, v⁻¹ * τ v = 1 ∨ v⁻¹ * τ v = z')
    {w : A} (hw : w⁻¹ * τ w = z) (hz1 : z ≠ 1) : z = z' := by
  rcases h' w with h0 | hz
  · exact absurd (hw.symm.trans h0) hz1
  · exact hw.symm.trans hz

theorem displacement_mul_of_comm {G : Type*} [Group G] {A : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {f : G}
    (hf : f ∈ Subgroup.normalizer (A : Set G)) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    (x * y)⁻¹ * (f * (x * y) * f⁻¹) =
      (x⁻¹ * (f * x * f⁻¹)) * (y⁻¹ * (f * y * f⁻¹)) := by
  have hPx : f * x * f⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hf x).mp hx
  have hPy : f * y * f⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hf y).mp hy
  have hxy_inv : y⁻¹ * x⁻¹ = x⁻¹ * y⁻¹ := by
    have h := hcomm x hx y hy
    have := congrArg Inv.inv h
    simpa [mul_inv_rev] using this
  have hyPx_inv : y⁻¹ * (f * x * f⁻¹) = (f * x * f⁻¹) * y⁻¹ := by
    have h := hcomm y hy (f * x * f⁻¹) hPx
    calc y⁻¹ * (f * x * f⁻¹)
        = y⁻¹ * ((f * x * f⁻¹) * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * (f * x * f⁻¹)) * y⁻¹ := by rw [← h]
      _ = (f * x * f⁻¹) * y⁻¹ := by group
  have hdecomp : f * (x * y) * f⁻¹ = (f * x * f⁻¹) * (f * y * f⁻¹) := by group
  rw [hdecomp, mul_inv_rev]
  calc
    y⁻¹ * x⁻¹ * ((f * x * f⁻¹) * (f * y * f⁻¹))
        = x⁻¹ * (y⁻¹ * (f * x * f⁻¹)) * (f * y * f⁻¹) := by
          rw [hxy_inv]
          group
    _ = x⁻¹ * ((f * x * f⁻¹) * y⁻¹) * (f * y * f⁻¹) := by rw [hyPx_inv]
    _ = (x⁻¹ * (f * x * f⁻¹)) * (y⁻¹ * (f * y * f⁻¹)) := by group

namespace Sec3Setting

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_normalizer_of_isConj_center (𝔖 : Sec3Setting G) {A : Subgroup G}
    (hAS : A ≤ (𝔖.S : Subgroup G)) (hA : IsE16 A) {v w : G} (hv : v ∈ A) (hw : w ∈ A)
    (hwS : (𝔖.S : Subgroup G) ≤ C w) (hv2 : orderOf v = 2) (hw2 : orderOf w = 2)
    (hconj : IsConj v w) :
    ∃ g ∈ normalizer (A : Set G), g * v * g⁻¹ = w := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htop : CFSG.ABGLocalTools.IsSylowOf 2 (𝔖.S : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, 𝔖.S.isPGroup', by simpa using 𝔖.S.not_dvd_index⟩
  have hwsyl : CFSG.ABGLocalTools.IsSylowOf 2
      ((𝔖.S : Subgroup G) ⊓ C w) (C w) := by
    have h := htop.of_le hwS le_top
    simpa [inf_eq_left.mpr hwS] using h
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hch : c⁻¹ * w * c = v := by
    calc c⁻¹ * w * c = c⁻¹ * (c * v * c⁻¹) * c := by rw [hc]
      _ = v := by group
  obtain ⟨g, hgv, hgC⟩ := exists_conj_extremal_univ
    (S := (𝔖.S : Subgroup G)) 𝔖.S.isPGroup' hwsyl hch
  have hAconv : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ (𝔖.S : Subgroup G) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have haC : a ∈ Subgroup.centralizer ({v} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨v, hv⟩))
    have hmem := (hgC a (Subgroup.mem_inf.mpr ⟨hAS ha, haC⟩)).1
    change (MulAut.conj g⁻¹) a ∈ (𝔖.S : Subgroup G)
    rw [MulAut.conj_apply, inv_inv]
    exact hmem
  have hB : IsE16 (A.map (MulAut.conj g⁻¹).toMonoidHom) :=
    hA.map _ (MulAut.conj g⁻¹).injective
  obtain ⟨s, hsS, hsmap⟩ := lemma_3_1 𝔖 A (A.map (MulAut.conj g⁻¹).toMonoidHom)
    hAS hAconv hA hB g⁻¹ rfl
  have hcomp : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hBmapA : (A.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj s⁻¹).toMonoidHom = A := by
    calc (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom
        = (A.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom := by
          rw [hsmap]
      _ = A.map ((MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom) :=
          Subgroup.map_map (K := A) (f := (MulAut.conj s).toMonoidHom)
            (g := (MulAut.conj s⁻¹).toMonoidHom)
      _ = A.map (MonoidHom.id G) := by rw [hcomp]
      _ = A := Subgroup.map_id A
  refine ⟨s⁻¹ * g⁻¹, ?_, ?_⟩
  · refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨?_, ?_⟩
    · intro hx
      refine hBmapA ▸ Subgroup.mem_map.mpr
        ⟨g⁻¹ * x * g, Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩, ?_⟩
      show (MulAut.conj s⁻¹) (g⁻¹ * x * g) = (s⁻¹ * g⁻¹) * x * (s⁻¹ * g⁻¹)⁻¹
      rw [MulAut.conj_apply]
      group
    · intro hx
      have hxA' : s⁻¹ * (g⁻¹ * x * g) * s ∈ A := by
        rw [show s⁻¹ * (g⁻¹ * x * g) * s = (s⁻¹ * g⁻¹) * x * (s⁻¹ * g⁻¹)⁻¹ by group]
        exact hx
      rw [← hBmapA] at hxA'
      obtain ⟨b, hb, hbs⟩ := Subgroup.mem_map.mp hxA'
      have hbs' : s⁻¹ * b * s = s⁻¹ * (g⁻¹ * x * g) * s := by
        have h := hbs
        change (MulAut.conj s⁻¹) b = s⁻¹ * (g⁻¹ * x * g) * s at h
        rw [MulAut.conj_apply] at h
        simpa using h
      have hbg : b = g⁻¹ * x * g := mul_left_cancel (mul_right_cancel hbs')
      rw [hbg] at hb
      obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.mp hb
      have hag' : g⁻¹ * a * g = g⁻¹ * x * g := by
        have h := hag
        change (MulAut.conj g⁻¹) a = g⁻¹ * x * g at h
        rw [MulAut.conj_apply] at h
        simpa using h
      have hax : a = x := mul_left_cancel (mul_right_cancel hag')
      simpa [← hax] using ha
  · calc (s⁻¹ * g⁻¹) * v * (s⁻¹ * g⁻¹)⁻¹
        = s⁻¹ * (g⁻¹ * v * g) * s := by group
      _ = s⁻¹ * w * s := by rw [hgv]
      _ = w := by
        have hws : s * w = w * s := Subgroup.mem_centralizer_singleton_iff.mp (hwS hsS)
        calc s⁻¹ * w * s = s⁻¹ * (w * s) := by group
          _ = s⁻¹ * (s * w) := by rw [← hws]
          _ = w := by group


theorem lemma_3_10 (𝔖 : Sec3Setting G) (h₁ : IsDihNonab 𝔖.S₁)
    (h₂ : ∀ x ∈ 𝔖.S₁, ∀ y ∈ 𝔖.S₁, orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ Subgroup.centralizer ((𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) : Subgroup G) : Set G),
        g * x * g⁻¹ = y)
    (h₃ : ∀ x ∈ 𝔖.S₂, ∀ y ∈ 𝔖.S₂, orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ Subgroup.centralizer ((𝔖.S₁ ⊓ Subgroup.centralizer (𝔖.S₁ : Set G) : Subgroup G) : Set G),
        g * x * g⁻¹ = y)
    (A : Subgroup G) (hAS : A ≤ 𝔖.S) (hA : IsE16 A) :
    (∃ Q : Subgroup G, Subgroup.centralizer (A : Set G) ≤ Q ∧
      Q ≤ Subgroup.normalizer (A : Set G) ∧
      (Q.subgroupOf (Subgroup.normalizer (A : Set G))).Normal ∧
      (Subgroup.centralizer (A : Set G)).relIndex Q = 9 ∧
      ∃ n : ℕ, Q.relIndex (Subgroup.normalizer (A : Set G)) = 2 ^ n) ∧
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((𝔖.S₁ ⊓ A : Subgroup G) : Set G) ∧
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((𝔖.S₂ ⊓ A : Subgroup G) : Set G) ∧
    ∀ v ∈ A, ∀ w ∈ A, orderOf v = 2 → orderOf w = 2 → v ∉ 𝔖.S₁ → v ∉ 𝔖.S₂ → w ∉ 𝔖.S₁ →
      w ∉ 𝔖.S₂ → ∃ g ∈ Subgroup.normalizer (A : Set G), g * v * g⁻¹ = w := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh₁ := h₁
  obtain ⟨k₁, hk₁, ⟨e₁⟩⟩ := hh₁
  obtain ⟨k₂, hk₂, ⟨e₂⟩⟩ := 𝔖.decomp.dih₂
  let z₁ : G := ((e₁.symm (CFSG.CGT.Foote81L6.zc k₁) : ↥𝔖.S₁) : G)
  let z₂ : G := ((e₂.symm (CFSG.CGT.Foote81L6.zc k₂) : ↥𝔖.S₂) : G)
  have hk₁1 : 1 ≤ k₁ := by omega
  have hk₂1 : 1 ≤ k₂ := by omega
  have hz₁S₁ : z₁ ∈ 𝔖.S₁ := (e₁.symm (CFSG.CGT.Foote81L6.zc k₁)).2
  have hz₂S₂ : z₂ ∈ 𝔖.S₂ := (e₂.symm (CFSG.CGT.Foote81L6.zc k₂)).2
  have hz₁2 : z₁ * z₁ = 1 := by
    change ((e₁.symm (CFSG.CGT.Foote81L6.zc k₁) : ↥𝔖.S₁) : G) *
      ((e₁.symm (CFSG.CGT.Foote81L6.zc k₁) : ↥𝔖.S₁) : G) = 1
    rw [← Subgroup.coe_mul, dih_symm_zc_mul_self e₁ hk₁1, Subgroup.coe_one]
  have hz₂2 : z₂ * z₂ = 1 := by
    change ((e₂.symm (CFSG.CGT.Foote81L6.zc k₂) : ↥𝔖.S₂) : G) *
      ((e₂.symm (CFSG.CGT.Foote81L6.zc k₂) : ↥𝔖.S₂) : G) = 1
    rw [← Subgroup.coe_mul, dih_symm_zc_mul_self e₂ hk₂1, Subgroup.coe_one]
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    exact dih_symm_zc_ne_one e₁ hk₁1 (Subtype.ext h)
  have hz₂1 : z₂ ≠ 1 := by
    intro h
    exact dih_symm_zc_ne_one e₂ hk₂1 (Subtype.ext h)
  have hz₁ord : orderOf z₁ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hz₁2) hz₁1
  have hz₂ord : orderOf z₂ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hz₂2) hz₂1
  have hz₁_centS₁ : ∀ y ∈ 𝔖.S₁, y * z₁ = z₁ * y := by
    intro y hy
    exact congrArg Subtype.val
      ((Subgroup.mem_center_iff.mp (dih_symm_zc_mem_center e₁ hk₁1)) ⟨y, hy⟩)
  have hz₂_centS₂ : ∀ y ∈ 𝔖.S₂, y * z₂ = z₂ * y := by
    intro y hy
    exact congrArg Subtype.val
      ((Subgroup.mem_center_iff.mp (dih_symm_zc_mem_center e₂ hk₂1)) ⟨y, hy⟩)
  have hz₁_centS : (𝔖.S : Subgroup G) ≤ C z₁ := by
    intro x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := 𝔖.decomp.mem_iff.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : x₁ * z₁ = z₁ * x₁ := hz₁_centS₁ x₁ hx₁
    have h2 : x₂ * z₁ = z₁ * x₂ := (𝔖.decomp.comm hz₁S₁ hx₂).symm
    calc (x₁ * x₂) * z₁ = x₁ * (x₂ * z₁) := by group
      _ = x₁ * (z₁ * x₂) := by rw [h2]
      _ = (x₁ * z₁) * x₂ := by group
      _ = (z₁ * x₁) * x₂ := by rw [h1]
      _ = z₁ * (x₁ * x₂) := by group
  have hz₂_centS : (𝔖.S : Subgroup G) ≤ C z₂ := by
    intro x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := 𝔖.decomp.mem_iff.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : x₁ * z₂ = z₂ * x₁ := 𝔖.decomp.comm hx₁ hz₂S₂
    have h2 : x₂ * z₂ = z₂ * x₂ := hz₂_centS₂ x₂ hx₂
    calc (x₁ * x₂) * z₂ = x₁ * (x₂ * z₂) := by group
      _ = x₁ * (z₂ * x₂) := by rw [h2]
      _ = (x₁ * z₂) * x₂ := by group
      _ = (z₂ * x₁) * x₂ := by rw [h1]
      _ = z₂ * (x₁ * x₂) := by group
  have hz₁S : z₁ ∈ (𝔖.S : Subgroup G) := 𝔖.decomp.le_left hz₁S₁
  have hz₂S : z₂ ∈ (𝔖.S : Subgroup G) := 𝔖.decomp.le_right hz₂S₂
  have hz₁A : z₁ ∈ A := 𝔖.decomp.center_le hAS hA hz₁S hz₁_centS
  have hz₂A : z₂ ∈ A := 𝔖.decomp.center_le hAS hA hz₂S hz₂_centS
  have hz₁z₂ : z₁ ≠ z₂ := by
    intro h
    have hmem : z₁ ∈ 𝔖.S₁ ⊓ 𝔖.S₂ := ⟨hz₁S₁, h ▸ hz₂S₂⟩
    rw [𝔖.decomp.inf_eq] at hmem
    exact hz₁1 (Subgroup.mem_bot.mp hmem)
  let A₁ : Subgroup G := A ⊓ 𝔖.S₁
  let A₂ : Subgroup G := A ⊓ 𝔖.S₂
  have hAsplit : A = A₁ ⊔ A₂ := (𝔖.decomp.e16_split hAS hA).1
  have hV₁ : IsFourIn 𝔖.S₁ A₁ := (𝔖.decomp.e16_split hAS hA).2.1
  have hV₂ : IsFourIn 𝔖.S₂ A₂ := (𝔖.decomp.e16_split hAS hA).2.2
  have hz₁A₁ : z₁ ∈ A₁ := ⟨hz₁A, hz₁S₁⟩
  have hz₂A₂ : z₂ ∈ A₂ := ⟨hz₂A, hz₂S₂⟩
  have hA₁2 : ∀ x ∈ A₁, x * x = 1 := hV₁.2.1
  have hA₂2 : ∀ x ∈ A₂, x * x = 1 := hV₂.2.1
  have hA₁card : Nat.card A₁ = 4 := hV₁.2.2
  have hA₂card : Nat.card A₂ = 4 := hV₂.2.2
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA₁A₂comm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x := fun x hx y hy =>
    𝔖.decomp.comm hx.2 hy.2
  obtain ⟨f₁, hf₁S₁, f₂, hf₂S₂, hf₁2, hf₂2, hN₁, hN₂, hNS, hFA, hF4⟩ :=
    𝔖.decomp.exists_normalizer_e16 h₁ hAS hA
  let F : Subgroup G := Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂
  have hf₁F : f₁ ∈ F := Subgroup.mem_sup_left (Subgroup.mem_zpowers f₁)
  have hf₂F : f₂ ∈ F := Subgroup.mem_sup_right (Subgroup.mem_zpowers f₂)
  have hF_le_K : F ≤ Subgroup.normalizer (A : Set G) := by
    have hFK : F ≤ (𝔖.S : Subgroup G) ⊓ Subgroup.normalizer (A : Set G) := by
      rw [hNS]
      exact le_sup_right
    exact fun x hx => (hFK hx).2
  have hf₁K : f₁ ∈ Subgroup.normalizer (A : Set G) := hF_le_K hf₁F
  have hf₂K : f₂ ∈ Subgroup.normalizer (A : Set G) := hF_le_K hf₂F
  have hf₁N : f₁ ∈ normalizer (A₁ : Set G) := by
    have h : f₁ ∈ A₁ ⊔ Subgroup.zpowers f₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers f₁)
    rw [← hN₁] at h
    exact h.2
  have hf₂N : f₂ ∈ normalizer (A₂ : Set G) := by
    have h : f₂ ∈ A₂ ⊔ Subgroup.zpowers f₂ := Subgroup.mem_sup_right (Subgroup.mem_zpowers f₂)
    rw [← hN₂] at h
    exact h.2
  have hf₁f₂ : f₁ * f₂ = f₂ * f₁ := 𝔖.decomp.comm hf₁S₁ hf₂S₂
  have hFcard : Nat.card F = 4 := hF4.card_four
  have hf₁1 : f₁ ≠ 1 := by
    intro h
    have hle : F ≤ Subgroup.zpowers f₂ := by
      change Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ ≤ Subgroup.zpowers f₂
      rw [h]
      simp
    have hf₂sq : f₂ ^ 2 = 1 := by rw [pow_two]; exact hf₂2
    have hcard2 : Nat.card (Subgroup.zpowers f₂) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hf₂sq)
    have : Nat.card F ≤ 2 :=
      (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)).trans hcard2
    omega
  have hf₂1 : f₂ ≠ 1 := by
    intro h
    have hle : F ≤ Subgroup.zpowers f₁ := by
      change Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ ≤ Subgroup.zpowers f₁
      rw [h]
      simp
    have hf₁sq : f₁ ^ 2 = 1 := by rw [pow_two]; exact hf₁2
    have hcard2 : Nat.card (Subgroup.zpowers f₁) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hf₁sq)
    have : Nat.card F ≤ 2 :=
      (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)).trans hcard2
    omega
  have htrans₁ : ∀ a ∈ A, a⁻¹ * (f₁ * a * f₁⁻¹) = 1 ∨
      a⁻¹ * (f₁ * a * f₁⁻¹) = z₁ := by
    intro x hx
    have hxsplit : x ∈ A₁ ⊔ A₂ := hAsplit ▸ hx
    obtain ⟨u, hu, v, hv, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hA₁A₂comm)).1 hxsplit
    have huA : u ∈ A := hAsplit ▸ Subgroup.mem_sup_left hu
    have hvA : v ∈ A := hAsplit ▸ Subgroup.mem_sup_right hv
    have hfv : f₁ * v * f₁⁻¹ = v := by
      rw [𝔖.decomp.comm hf₁S₁ hv.2]
      group
    have hux : f₁ * u * f₁⁻¹ = u ∨ f₁ * u * f₁⁻¹ = u * z₁ :=
      CFSG.CGT.Foote81L6.TStruct.conj_of_mem_inf_normalizer_four e₁ hk₁1 hV₁
        ⟨hf₁S₁, hf₁N⟩ hu
    have hdisp := displacement_mul_of_comm hAcomm hf₁K huA hvA
    have hdv : v⁻¹ * (f₁ * v * f₁⁻¹) = 1 := by rw [hfv]; group
    rw [hdisp, hdv, mul_one]
    rcases hux with h | h
    · left; rw [h]; group
    · right; rw [h]; group
  have htrans₂ : ∀ a ∈ A, a⁻¹ * (f₂ * a * f₂⁻¹) = 1 ∨
      a⁻¹ * (f₂ * a * f₂⁻¹) = z₂ := by
    intro x hx
    have hxsplit : x ∈ A₁ ⊔ A₂ := hAsplit ▸ hx
    obtain ⟨u, hu, v, hv, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hA₁A₂comm)).1 hxsplit
    have huA : u ∈ A := hAsplit ▸ Subgroup.mem_sup_left hu
    have hvA : v ∈ A := hAsplit ▸ Subgroup.mem_sup_right hv
    have hfu : f₂ * u * f₂⁻¹ = u := by
      rw [← 𝔖.decomp.comm hu.2 hf₂S₂]
      group
    have hux : f₂ * v * f₂⁻¹ = v ∨ f₂ * v * f₂⁻¹ = v * z₂ :=
      CFSG.CGT.Foote81L6.TStruct.conj_of_mem_inf_normalizer_four e₂ hk₂1 hV₂
        ⟨hf₂S₂, hf₂N⟩ hv
    have hdisp := displacement_mul_of_comm hAcomm hf₂K huA hvA
    have hdu : u⁻¹ * (f₂ * u * f₂⁻¹) = 1 := by rw [hfu]; group
    rw [hdisp, hdu, one_mul]
    rcases hux with h | h
    · left; rw [h]; group
    · right; rw [h]; group
  have hf₁C : f₁ ∉ Subgroup.centralizer (A : Set G) := by
    intro h
    have hf₁inf : f₁ ∈ (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (A : Set G) :=
      ⟨𝔖.decomp.le_left hf₁S₁, h⟩
    rw [𝔖.decomp.inf_centralizer_e16 hAS hA] at hf₁inf
    exact hf₁1 (by
      have : f₁ ∈ A ⊓ F := ⟨hf₁inf, hf₁F⟩
      rw [hFA] at this
      exact Subgroup.mem_bot.mp this)
  have hf₂C : f₂ ∉ Subgroup.centralizer (A : Set G) := by
    intro h
    have hf₂inf : f₂ ∈ (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (A : Set G) :=
      ⟨𝔖.decomp.le_right hf₂S₂, h⟩
    rw [𝔖.decomp.inf_centralizer_e16 hAS hA] at hf₂inf
    exact hf₂1 (by
      have : f₂ ∈ A ⊓ F := ⟨hf₂inf, hf₂F⟩
      rw [hFA] at this
      exact Subgroup.mem_bot.mp this)
  obtain ⟨c, hcA₂, hcN₂⟩ :=
    CFSG.CGT.Foote81L6.TStruct.exists_conj_of_not_mem_four e₂ hk₂1 hV₂
      ⟨hf₂S₂, hf₂N⟩ (by
        intro h
        have : f₂ ∈ A ⊓ F := ⟨h.1, hf₂F⟩
        rw [hFA] at this
        exact hf₂1 (Subgroup.mem_bot.mp this))
  obtain ⟨a, haA₁, haN₁⟩ :=
    CFSG.CGT.Foote81L6.TStruct.exists_conj_of_not_mem_four e₁ hk₁1 hV₁
      ⟨hf₁S₁, hf₁N⟩ (by
        intro h
        have : f₁ ∈ A ⊓ F := ⟨h.1, hf₁F⟩
        rw [hFA] at this
        exact hf₁1 (Subgroup.mem_bot.mp this))
  have hcA : c ∈ A := hAsplit ▸ Subgroup.mem_sup_right hcA₂
  have haA : a ∈ A := hAsplit ▸ Subgroup.mem_sup_left haA₁
  have hc_fixed : f₁ * c * f₁⁻¹ = c := by
    rw [𝔖.decomp.comm hf₁S₁ hcA₂.2]
    group
  have ha_moved : f₁ * a * f₁⁻¹ ≠ a := by
    intro h
    have h' : a * z₁ = a := by rw [← haN₁, h]
    exact hz₁1 (mul_left_cancel (a := a) (by simpa using h'))
  have htrans_c : f₂ * c * f₂⁻¹ ≠ c := by
    intro h
    have h' : c * z₂ = c * 1 := by rw [← hcN₂, h, mul_one]
    exact hz₂1 (mul_left_cancel h')
  have h₁₂ : Nat.card (A ⊓ Subgroup.centralizer ({f₁ * f₂} : Set G) : Subgroup G) = 4 :=
    CFSG.GH72.card_inf_centralizer_mul_eq_four_of_transvections hA
      (by simpa using hf₁K) (by simpa using hf₂K) hf₁f₂ hz₁A hz₂A htrans₁ hf₁C htrans₂ hf₂C
      hz₁z₂ hcA hc_fixed htrans_c
  have ha1 : a ≠ 1 := by
    intro h
    rw [h] at haN₁
    exact dih_symm_zc_ne_one e₁ hk₁1 (Subtype.ext (by simpa using haN₁.symm))
  have hc1 : c ≠ 1 := by
    intro h
    rw [h] at hcN₂
    exact dih_symm_zc_ne_one e₂ hk₂1 (Subtype.ext (by simpa using hcN₂.symm))
  have haord : orderOf a = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hA₁2 a haA₁) ha1
  have hcord : orderOf c = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hA₂2 c hcA₂) hc1
  obtain ⟨g₁, hg₁, hg₁a⟩ := h₂ a haA₁.2 z₁ hz₁S₁ haord hz₁ord
  have hconj_a : ∃ g ∈ Subgroup.normalizer (A : Set G), g * a * g⁻¹ = z₁ :=
    exists_conj_mem_normalizer_of_isConj_center 𝔖 hAS hA haA hz₁A hz₁_centS haord hz₁ord
      (isConj_iff.mpr ⟨g₁, hg₁a⟩)
  obtain ⟨g₂, hg₂, hg₂c⟩ := h₃ c hcA₂.2 z₂ hz₂S₂ hcord hz₂ord
  have hconj_c : ∃ g ∈ Subgroup.normalizer (A : Set G), g * c * g⁻¹ = z₂ :=
    exists_conj_mem_normalizer_of_isConj_center 𝔖 hAS hA hcA hz₂A hz₂_centS hcord hz₂ord
      (isConj_iff.mpr ⟨g₂, hg₂c⟩)

  let K : Subgroup G := Subgroup.normalizer (A : Set G)
  let Cc : Subgroup G := Subgroup.centralizer (A : Set G)
  let φ : K →* MulAut A := A.normalizerMonoidHom
  let L : Subgroup (MulAut A) := φ.range
  let Psub : Subgroup (MulAut A) := (F.subgroupOf K).map φ
  have hPsub_le_L : Psub ≤ L := Subgroup.map_le_range (f := φ) (F.subgroupOf K)
  have hφker : φ.ker = Cc.subgroupOf K := by
    change (A.normalizerMonoidHom).ker = Cc.subgroupOf K
    rw [Subgroup.normalizerMonoidHom_ker]
  have hFC : F ⊓ Cc = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxC⟩
    have hxS : x ∈ (𝔖.S : Subgroup G) := by
      have hFK : F ≤ (𝔖.S : Subgroup G) ⊓ K := by
        rw [hNS]
        exact le_sup_right
      exact (hFK hxF).1
    have hxAC : x ∈ A := by
      have hx : x ∈ (𝔖.S : Subgroup G) ⊓ Cc := ⟨hxS, hxC⟩
      rwa [𝔖.decomp.inf_centralizer_e16 hAS hA] at hx
    exact Subgroup.mem_bot.mp (by
      have : x ∈ A ⊓ F := ⟨hxAC, hxF⟩
      rwa [hFA] at this)
  have hker_bot : (Cc.subgroupOf K) ⊓ (F.subgroupOf K) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxC, hxF⟩
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (by
      have hxG : (x : G) ∈ F ⊓ Cc :=
        ⟨Subgroup.mem_subgroupOf.mp hxF, Subgroup.mem_subgroupOf.mp hxC⟩
      rwa [hFC] at hxG)
  have hPsub_card : Nat.card Psub = 4 := by
    change Nat.card ((F.subgroupOf K).map φ) = 4
    rw [← Subgroup.relIndex_ker (f := φ) (K := F.subgroupOf K), hφker]
    have hmul := Subgroup.relIndex_mul_card (H := Cc.subgroupOf K) (K := F.subgroupOf K)
    rw [hker_bot, Subgroup.card_bot, mul_one] at hmul
    rw [hmul]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF_le_K).toEquiv, hFcard]
  let P : Subgroup G := (𝔖.S : Subgroup G) ⊓ K
  have hP_sylow : CFSG.ABGLocalTools.IsSylowOf 2 P K :=
    𝔖.decomp.isSylowOf_normalizer_e16 hAS hA
  have hP_card : Nat.card P = 64 :=
    𝔖.decomp.card_inf_normalizer_e16_of_isDihNonab h₁ hAS hA
  have hP_notdvd : ¬ 2 ∣ P.relIndex K := by
    have := (CFSG.ABGLocalTools.isSylowOf_iff.mp hP_sylow).2.2
    simpa using this
  have hP_odd : Odd (P.relIndex K) := by
    rcases Nat.even_or_odd (P.relIndex K) with he | ho
    · exact absurd (even_iff_two_dvd.mp he) hP_notdvd
    · exact ho
  have hP_eq : P = A ⊔ F := by
    change (𝔖.S : Subgroup G) ⊓ K = A ⊔ F
    exact hNS
  have hKnormC : K ≤ Subgroup.normalizer (Cc : Set G) := by
    have hNC : (Cc.subgroupOf K).Normal := by
      change (Subgroup.centralizer (A : Set G)).subgroupOf
        (Subgroup.normalizer (A : Set G)) |>.Normal
      infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (A : Set G))).mp hNC
  have hPnormC : P ≤ Subgroup.normalizer (Cc : Set G) := fun x hx => hKnormC hx.2
  have hA_le_C : A ≤ Cc := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hAcomm x hx y hy).symm
  have hrel_sup : Cc.relIndex (P ⊔ Cc) = 4 := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := P) (K := Cc) hPnormC).2
    rw [h]
    have hPC : P ⊓ Cc = A := by
      change ((𝔖.S : Subgroup G) ⊓ K) ⊓ Cc = A
      have hKC : K ⊓ Cc = Cc := inf_eq_right.mpr fun x hx =>
        Subgroup.centralizer_le_normalizer (A : Set G) hx
      rw [inf_assoc, hKC]
      exact 𝔖.decomp.inf_centralizer_e16 hAS hA
    rw [hPC]
    have hAP : A ≤ P := by rw [hP_eq]; exact le_sup_left
    have hmul : A.relIndex P * Nat.card A = Nat.card P := by
      simpa [inf_eq_left.mpr hAP] using (Subgroup.relIndex_mul_card (H := A) (K := P))
    rw [hA.2, hP_card] at hmul
    omega
  have hPC_odd : Odd ((P ⊔ Cc).relIndex K) := by
    have hdvd : (P ⊔ Cc).relIndex K ∣ P.relIndex K :=
      Subgroup.relIndex_dvd_of_le_left (H := P) (K := P ⊔ Cc) (L := K) le_sup_left
    exact hP_odd.of_dvd_nat hdvd
  have hL_card : Nat.card L = Cc.relIndex K := by
    change Nat.card φ.range = Cc.relIndex K
    rw [← Subgroup.index_ker φ, hφker]
    rfl
  have hL_card' : Nat.card L = 4 * (P ⊔ Cc).relIndex K := by
    rw [hL_card, ← Subgroup.relIndex_mul_relIndex (H := Cc) (K := P ⊔ Cc) (L := K)
      (show Cc ≤ P ⊔ Cc from le_sup_right)
      (show P ⊔ Cc ≤ K from sup_le inf_le_right fun x hx =>
        Subgroup.centralizer_le_normalizer (A : Set G) hx), hrel_sup]
  have hPsub_relIndex_card : Psub.relIndex L * Nat.card Psub = Nat.card L := by
    simpa [inf_eq_left.mpr hPsub_le_L] using
      (Subgroup.relIndex_mul_card (H := Psub) (K := L))
  have hPsub_relIndex_odd : Odd (Psub.relIndex L) := by
    have hmul : Psub.relIndex L * 4 = 4 * (P ⊔ Cc).relIndex K := by
      rw [← hPsub_card, hPsub_relIndex_card, hL_card', hPsub_card]
    have hcancel : Psub.relIndex L = (P ⊔ Cc).relIndex K := by omega
    rw [hcancel]
    exact hPC_odd
  have hPsub_sylow : CFSG.ABGLocalTools.IsSylowOf 2 Psub L := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hPsub_le_L, ?_, ?_⟩
    · exact IsPGroup.of_card (n := 2) (by rw [hPsub_card]; norm_num)
    · rintro ⟨k, hk⟩
      obtain ⟨m, hm⟩ := hPsub_relIndex_odd
      omega
  let τ₁ : MulAut A := φ ⟨f₁, hf₁K⟩
  let τ₂ : MulAut A := φ ⟨f₂, hf₂K⟩
  have hτ₁2 : τ₁ * τ₁ = 1 := by
    change φ ⟨f₁, hf₁K⟩ * φ ⟨f₁, hf₁K⟩ = 1
    have hmul : (⟨f₁, hf₁K⟩ : K) * ⟨f₁, hf₁K⟩ = 1 := Subtype.ext hf₁2
    rw [← map_mul, hmul, map_one]
  have hτ₂2 : τ₂ * τ₂ = 1 := by
    change φ ⟨f₂, hf₂K⟩ * φ ⟨f₂, hf₂K⟩ = 1
    have hmul : (⟨f₂, hf₂K⟩ : K) * ⟨f₂, hf₂K⟩ = 1 := Subtype.ext hf₂2
    rw [← map_mul, hmul, map_one]
  have hτ₁1 : τ₁ ≠ 1 := by
    intro h
    exact hf₁C ((normalizerMonoidHom_eq_one_iff hf₁K).mp h)
  have hτ₂1 : τ₂ ≠ 1 := by
    intro h
    exact hf₂C ((normalizerMonoidHom_eq_one_iff hf₂K).mp h)
  have hτcomm : τ₁ * τ₂ = τ₂ * τ₁ := by
    change φ ⟨f₁, hf₁K⟩ * φ ⟨f₂, hf₂K⟩ = φ ⟨f₂, hf₂K⟩ * φ ⟨f₁, hf₁K⟩
    have hmul : (⟨f₁, hf₁K⟩ : K) * ⟨f₂, hf₂K⟩ = ⟨f₂, hf₂K⟩ * ⟨f₁, hf₁K⟩ :=
      Subtype.ext hf₁f₂
    rw [← map_mul, ← map_mul, hmul]
  have hτ₁trans : ∀ v : A, v⁻¹ * τ₁ v = 1 ∨ v⁻¹ * τ₁ v = ⟨z₁, hz₁A⟩ :=
    normalizerMonoidHom_transvection hf₁K hz₁A htrans₁
  have hτ₂trans : ∀ v : A, v⁻¹ * τ₂ v = 1 ∨ v⁻¹ * τ₂ v = ⟨z₂, hz₂A⟩ :=
    normalizerMonoidHom_transvection hf₂K hz₂A htrans₂
  have hτ₁displ : (⟨a, haA⟩ : A)⁻¹ * τ₁ ⟨a, haA⟩ = ⟨z₁, hz₁A⟩ := by
    apply Subtype.ext
    change a⁻¹ * (f₁ * a * f₁⁻¹) = z₁
    rw [haN₁]
    group
    rfl
  have hτ₂displ : (⟨c, hcA⟩ : A)⁻¹ * τ₂ ⟨c, hcA⟩ = ⟨z₂, hz₂A⟩ := by
    apply Subtype.ext
    change c⁻¹ * (f₂ * c * f₂⁻¹) = z₂
    rw [hcN₂]
    group
    rfl
  have hτ₁z1 : (⟨z₁, hz₁A⟩ : A) ≠ 1 := fun h => hz₁1 (congrArg Subtype.val h)
  have hτ₂z1 : (⟨z₂, hz₂A⟩ : A) ≠ 1 := fun h => hz₂1 (congrArg Subtype.val h)
  have hz₁_sub : (Subgroup.zpowers f₁).subgroupOf K =
      Subgroup.zpowers (⟨f₁, hf₁K⟩ : K) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers_iff.mpr
        ⟨n, congrArg Subtype.val hn⟩)
  have hz₂_sub : (Subgroup.zpowers f₂).subgroupOf K =
      Subgroup.zpowers (⟨f₂, hf₂K⟩ : K) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers_iff.mpr
        ⟨n, congrArg Subtype.val hn⟩)
  have hPsub_eq : Psub = Subgroup.zpowers τ₁ ⊔ Subgroup.zpowers τ₂ := by
    change (F.subgroupOf K).map φ = _
    have hFsub : F.subgroupOf K = (Subgroup.zpowers f₁).subgroupOf K ⊔
        (Subgroup.zpowers f₂).subgroupOf K := by
      change (Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂).subgroupOf K = _
      rw [Subgroup.subgroupOf_sup (Subgroup.zpowers_le.mpr hf₁K)
        (Subgroup.zpowers_le.mpr hf₂K)]
    rw [hFsub, hz₁_sub, hz₂_sub, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
  have hτ₁P : τ₁ ∈ Psub := by
    rw [hPsub_eq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers τ₁)
  have hτ₂P : τ₂ ∈ Psub := by
    rw [hPsub_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τ₂)
  have hPsub_mem : ∀ y ∈ Psub, y = 1 ∨ y = τ₁ ∨ y = τ₂ ∨ y = τ₁ * τ₂ := by
    intro y hy
    rw [hPsub_eq] at hy
    have hcomm : ∀ u ∈ Subgroup.zpowers τ₁, ∀ v ∈ Subgroup.zpowers τ₂, u * v = v * u :=
      fun u hu v hv => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        exact (show Commute τ₁ τ₂ from hτcomm).zpow_zpow m n |>.eq
    obtain ⟨u, hu, v, hv, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcomm)).1 hy
    rcases eq_one_or_eq_of_mem_zpowers hτ₁2 hu with hu1 | hu1 <;>
      rcases eq_one_or_eq_of_mem_zpowers hτ₂2 hv with hv1 | hv1
    · exact Or.inl (by simp [hu1, hv1])
    · exact Or.inr (Or.inr (Or.inl (by simp [hu1, hv1])))
    · exact Or.inr (Or.inl (by simp [hu1, hv1]))
    · exact Or.inr (Or.inr (Or.inr (by simp [hu1, hv1])))
  have hprod_a : (⟨a, haA⟩ : A)⁻¹ * (τ₁ * τ₂) ⟨a, haA⟩ = ⟨z₁, hz₁A⟩ := by
    apply Subtype.ext
    change a⁻¹ * (f₁ * (f₂ * a * f₂⁻¹) * f₁⁻¹) = z₁
    have hfa : f₂ * a * f₂⁻¹ = a := by
      rw [← 𝔖.decomp.comm haA₁.2 hf₂S₂]
      group
    rw [hfa, haN₁]
    group
    rfl
  have hprod_c : (⟨c, hcA⟩ : A)⁻¹ * (τ₁ * τ₂) ⟨c, hcA⟩ = ⟨z₂, hz₂A⟩ := by
    apply Subtype.ext
    change c⁻¹ * (f₁ * (f₂ * c * f₂⁻¹) * f₁⁻¹) = z₂
    have hf₁z₂ : f₁ * z₂ * f₁⁻¹ = z₂ := by
      rw [𝔖.decomp.comm hf₁S₁ hz₂S₂]
      group
    have hfc₂ : f₂ * c * f₂⁻¹ = c * z₂ := by simpa using hcN₂
    rw [hfc₂]
    calc c⁻¹ * (f₁ * (c * z₂) * f₁⁻¹)
        = c⁻¹ * ((f₁ * c * f₁⁻¹) * (f₁ * z₂ * f₁⁻¹)) := by group
      _ = c⁻¹ * (c * z₂) := by rw [hc_fixed, hf₁z₂]
      _ = z₂ := by group
      _ = z₂ := rfl
  have hnot_swap₁ : ∀ x : MulAut A, x ∈ L → x * τ₁ * x⁻¹ = τ₂ → False := by
    intro x hxL hx
    have hconj := transvection_conj_apply (x := x) hτ₁trans
    have hconj' : ∀ v : A, v⁻¹ * τ₂ v = 1 ∨ v⁻¹ * τ₂ v = x ⟨z₁, hz₁A⟩ := by
      intro v
      have := hconj v
      rwa [hx] at this
    have huniq := transvection_center_unique hτ₂trans hconj' hτ₂displ hτ₂z1
    have hxz : x ⟨z₁, hz₁A⟩ = ⟨z₂, hz₂A⟩ := huniq.symm
    obtain ⟨k, hkx⟩ := MonoidHom.mem_range.mp hxL
    have hzconj : IsConj z₁ z₂ := by
      refine isConj_iff.mpr ⟨k, ?_⟩
      have h' : (x ⟨z₁, hz₁A⟩ : G) = z₂ := congrArg Subtype.val hxz
      rw [← hkx] at h'
      change k * z₁ * k⁻¹ = z₂ at h'
      exact h'
    exact hz₁z₂ (lemma_3_8 𝔖 h₁ z₁ hz₁S z₂ hz₂S hz₁_centS hz₂_centS hz₁ord hzconj)
  have hnot_swap₂ : ∀ x : MulAut A, x ∈ L → x * τ₂ * x⁻¹ = τ₁ → False := by
    intro x hxL hx
    have hconj := transvection_conj_apply (x := x) hτ₂trans
    have hconj' : ∀ v : A, v⁻¹ * τ₁ v = 1 ∨ v⁻¹ * τ₁ v = x ⟨z₂, hz₂A⟩ := by
      intro v
      have := hconj v
      rwa [hx] at this
    have huniq := transvection_center_unique hτ₁trans hconj' hτ₁displ hτ₁z1
    have hxz : x ⟨z₂, hz₂A⟩ = ⟨z₁, hz₁A⟩ := huniq.symm
    obtain ⟨k, hkx⟩ := MonoidHom.mem_range.mp hxL
    have hzconj : IsConj z₂ z₁ := by
      refine isConj_iff.mpr ⟨k, ?_⟩
      have h' : (x ⟨z₂, hz₂A⟩ : G) = z₁ := congrArg Subtype.val hxz
      rw [← hkx] at h'
      change k * z₂ * k⁻¹ = z₁ at h'
      exact h'
    exact hz₁z₂ (by
      have := lemma_3_8 𝔖 h₁ z₂ hz₂S z₁ hz₁S hz₂_centS hz₁_centS hz₂ord hzconj
      exact this.symm)
  have hnot_prod₁ : ∀ x : MulAut A, x * τ₁ * x⁻¹ = τ₁ * τ₂ → False := by
    intro x hx
    have hconj := transvection_conj_apply (x := x) hτ₁trans
    have hconj' : ∀ v : A, v⁻¹ * (τ₁ * τ₂) v = 1 ∨
        v⁻¹ * (τ₁ * τ₂) v = x ⟨z₁, hz₁A⟩ := by
      intro v
      have := hconj v
      rwa [hx] at this
    have ha := hconj' ⟨a, haA⟩
    have hc := hconj' ⟨c, hcA⟩
    rw [hprod_a] at ha
    rw [hprod_c] at hc
    have hza : x ⟨z₁, hz₁A⟩ = ⟨z₁, hz₁A⟩ := by
      rcases ha with h | h
      · exact absurd (congrArg Subtype.val h) hz₁1
      · exact h.symm
    have hzc : x ⟨z₁, hz₁A⟩ = ⟨z₂, hz₂A⟩ := by
      rcases hc with h | h
      · exact absurd (congrArg Subtype.val h) hz₂1
      · exact h.symm
    exact hz₁z₂ (Subtype.ext_iff.mp (hza.symm.trans hzc))
  have hnot_prod₂ : ∀ x : MulAut A, x * τ₂ * x⁻¹ = τ₁ * τ₂ → False := by
    intro x hx
    have hconj := transvection_conj_apply (x := x) hτ₂trans
    have hconj' : ∀ v : A, v⁻¹ * (τ₁ * τ₂) v = 1 ∨
        v⁻¹ * (τ₁ * τ₂) v = x ⟨z₂, hz₂A⟩ := by
      intro v
      have := hconj v
      rwa [hx] at this
    have ha := hconj' ⟨a, haA⟩
    have hc := hconj' ⟨c, hcA⟩
    rw [hprod_a] at ha
    rw [hprod_c] at hc
    have hza : x ⟨z₂, hz₂A⟩ = ⟨z₁, hz₁A⟩ := by
      rcases ha with h | h
      · exact absurd (congrArg Subtype.val h) hz₁1
      · exact h.symm
    have hzc : x ⟨z₂, hz₂A⟩ = ⟨z₂, hz₂A⟩ := by
      rcases hc with h | h
      · exact absurd (congrArg Subtype.val h) hz₂1
      · exact h.symm
    exact hz₁z₂ (congrArg Subtype.val (hza.symm.trans hzc))
  have hNambient : Subgroup.normalizer (Psub : Set (MulAut A)) ⊓ L ≤
      Subgroup.centralizer (Psub : Set (MulAut A)) := by
    rintro x ⟨hxN, hxL⟩
    rw [Subgroup.mem_centralizer_iff]
    have hx1mem : x * τ₁ * x⁻¹ ∈ Psub :=
      (Subgroup.mem_normalizer_iff.mp hxN τ₁).mp hτ₁P
    have hx2mem : x * τ₂ * x⁻¹ ∈ Psub :=
      (Subgroup.mem_normalizer_iff.mp hxN τ₂).mp hτ₂P
    have hx1ne : x * τ₁ * x⁻¹ ≠ 1 := by
      intro h
      apply hτ₁1
      have := congrArg (fun z : MulAut A => x⁻¹ * z * x) h
      simpa [mul_assoc] using this
    have hx2ne : x * τ₂ * x⁻¹ ≠ 1 := by
      intro h
      apply hτ₂1
      have := congrArg (fun z : MulAut A => x⁻¹ * z * x) h
      simpa [mul_assoc] using this
    rcases hPsub_mem _ hx1mem with h1 | h1 | h1 | h1
    · exfalso; exact absurd h1 hx1ne
    · rcases hPsub_mem _ hx2mem with h2 | h2 | h2 | h2
      · exfalso; exact absurd h2 hx2ne
      · exfalso; exact hnot_swap₂ x hxL h2
      ·
        have hxτ₁ : x * τ₁ = τ₁ * x := by
          calc x * τ₁ = x * τ₁ * x⁻¹ * x := by group
            _ = τ₁ * x := by rw [h1]
        have hxτ₂ : x * τ₂ = τ₂ * x := by
          calc x * τ₂ = x * τ₂ * x⁻¹ * x := by group
            _ = τ₂ * x := by rw [h2]
        intro y hy
        rcases hPsub_mem y hy with hy1 | hy1 | hy1 | hy1
        · rw [hy1]; simp
        · rw [hy1]; exact hxτ₁.symm
        · rw [hy1]; exact hxτ₂.symm
        · rw [hy1]
          calc τ₁ * τ₂ * x = τ₁ * (τ₂ * x) := by group
            _ = τ₁ * (x * τ₂) := by rw [hxτ₂]
            _ = (τ₁ * x) * τ₂ := by group
            _ = (x * τ₁) * τ₂ := by rw [hxτ₁]
            _ = x * (τ₁ * τ₂) := by group
      · exfalso; exact hnot_prod₂ x h2
    · exfalso; exact hnot_swap₁ x hxL h1
    · exfalso; exact hnot_prod₁ x h1
  have hNL : Subgroup.normalizer (Psub.subgroupOf L : Set L) ≤
      Subgroup.centralizer (Psub.subgroupOf L : Set L) :=
    normalizer_le_centralizer_of_ambient hPsub_le_L hNambient
  obtain ⟨Psyl, hPsyl_coe⟩ := hPsub_sylow.exists_sylow_eq_subgroupOf
  have hN_syl : Subgroup.normalizer (Psyl : Set L) ≤ Subgroup.centralizer (Psyl : Set L) := by
    have hcoe : (Psyl : Set L) = (Psub.subgroupOf L : Set L) :=
      congrArg (fun K : Subgroup L => (K : Set L)) hPsyl_coe
    rw [hcoe]
    exact hNL
  obtain ⟨Qbar, hQbar_normal, hQbar_notdvd, hQbar_index, -, -, hQbar_compl, -, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement Psyl hN_syl
  let QbarAmb : Subgroup (MulAut A) := Qbar.map L.subtype
  let Q : Subgroup G := (QbarAmb.comap φ).map K.subtype
  have hQ_le_K : Q ≤ K := Subgroup.map_subtype_le _
  have hC_le_Q : Cc ≤ Q := by
    intro x hx
    have hxK : x ∈ K := Subgroup.centralizer_le_normalizer (A : Set G) hx
    have hxφ : φ ⟨x, hxK⟩ = 1 :=
      (normalizerMonoidHom_eq_one_iff hxK).mpr hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
    change φ ⟨x, hxK⟩ ∈ Qbar.map L.subtype
    rw [hxφ]
    exact Subgroup.mem_map_of_mem _ Qbar.one_mem

  have hQsub_eq : Q.subgroupOf K = QbarAmb.comap φ := by
    change Subgroup.comap K.subtype ((QbarAmb.comap φ).map K.subtype) = QbarAmb.comap φ
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hQbarAmb_le_L : QbarAmb ≤ L := by
    rintro y ⟨q, hq, rfl⟩
    exact q.2
  have hQbarAmb_conj : ∀ l ∈ L, ∀ q ∈ QbarAmb, l * q * l⁻¹ ∈ QbarAmb := by
    intro l hl q hq
    obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hq
    have hconj : (⟨l, hl⟩ : L) * q' * (⟨l, hl⟩ : L)⁻¹ ∈ Qbar :=
      hQbar_normal.conj_mem q' hq' ⟨l, hl⟩
    exact Subgroup.mem_map_of_mem L.subtype hconj
  have hQbarAmb_norm : L ≤ Subgroup.normalizer (QbarAmb : Set (MulAut A)) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact hQbarAmb_conj l hl q hq
    · intro hq
      have := hQbarAmb_conj l⁻¹ (Subgroup.inv_mem (H := L) hl) (l * q * l⁻¹) hq
      simpa [mul_assoc] using this
  have hQnorm_sub : (Q.subgroupOf K).Normal := by
    rw [hQsub_eq]
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_comap] at hn ⊢
    have hφk : φ k ∈ L := MonoidHom.mem_range.mpr ⟨k, rfl⟩
    have h := hQbarAmb_conj (φ k) hφk (φ n) hn
    simpa [map_mul, map_inv] using h
  have hK_normalizes_Q : K ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le_K).mp hQnorm_sub
  have hf₁Q : f₁ ∈ Subgroup.normalizer (Q : Set G) := hK_normalizes_Q hf₁K
  have hf₂Q : f₂ ∈ Subgroup.normalizer (Q : Set G) := hK_normalizes_Q hf₂K
  have hQ_index_card : Cc.relIndex Q = Nat.card Qbar := by
    calc Cc.relIndex Q = (Cc.subgroupOf K).relIndex (Q.subgroupOf K) :=
          (Subgroup.relIndex_subgroupOf (H := Cc) (K := Q) (L := K) hQ_le_K).symm
      _ = (φ.ker).relIndex (QbarAmb.comap φ) := by rw [hQsub_eq, hφker]
      _ = Nat.card ((QbarAmb.comap φ).map φ) := Subgroup.relIndex_ker (f := φ) _
      _ = Nat.card QbarAmb := by rw [Subgroup.map_comap_eq_self hQbarAmb_le_L]
      _ = Nat.card Qbar := Subgroup.card_map_of_injective L.subtype_injective
  have hQbar_odd : Odd (Nat.card Qbar) := by
    rcases Nat.even_or_odd (Nat.card Qbar) with he | ho
    · exact absurd (even_iff_two_dvd.mp he) hQbar_notdvd
    · exact ho
  have hQ_index_odd : Odd (Cc.relIndex Q) := hQ_index_card ▸ hQbar_odd
  have hQbarAmb_card' : Nat.card QbarAmb = Nat.card Qbar :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hno : ∀ q ∈ Q, (∀ a ∈ A, q * ((f₁ * f₂) * a * (f₁ * f₂)⁻¹) * q⁻¹ =
      (f₁ * f₂) * (q * a * q⁻¹) * (f₁ * f₂)⁻¹) → q ∈ Cc := by
    intro q hq hcomm
    by_contra hqC
    have hqK : q ∈ K := hQ_le_K hq
    let σ : MulAut A := φ ⟨q, hqK⟩
    have hσ1 : σ ≠ 1 := by
      intro h
      exact hqC ((normalizerMonoidHom_eq_one_iff hqK).mp h)
    have hσmem : σ ∈ QbarAmb := by
      have hqsub : (⟨q, hqK⟩ : K) ∈ Q.subgroupOf K := hq
      rw [hQsub_eq] at hqsub
      exact Subgroup.mem_comap.mp hqsub
    have hQbarAmb_card : Nat.card QbarAmb = Nat.card Qbar :=
      Subgroup.card_map_of_injective L.subtype_injective
    have hσodd : Odd (orderOf σ) :=
      hQbar_odd.of_dvd_nat (hQbarAmb_card ▸
        Subgroup.orderOf_dvd_natCard (s := QbarAmb) (x := σ) hσmem)
    have hσcomm : σ * A.normalizerMonoidHom ⟨f₁ * f₂, mul_mem hf₁K hf₂K⟩ =
        A.normalizerMonoidHom ⟨f₁ * f₂, mul_mem hf₁K hf₂K⟩ * σ := by
      rw [normalizerMonoidHom_commute_iff (mul_mem hf₁K hf₂K) hqK]
      exact hcomm
    have hh2 : A.normalizerMonoidHom ⟨f₁ * f₂, mul_mem hf₁K hf₂K⟩ *
        A.normalizerMonoidHom ⟨f₁ * f₂, mul_mem hf₁K hf₂K⟩ = 1 := by
      have hmul : (⟨f₁ * f₂, mul_mem hf₁K hf₂K⟩ : K) *
          ⟨f₁ * f₂, mul_mem hf₁K hf₂K⟩ = 1 := by
        apply Subtype.ext
        show (f₁ * f₂) * (f₁ * f₂) = 1
        calc (f₁ * f₂) * (f₁ * f₂) = f₁ * (f₂ * f₁) * f₂ := by group
          _ = f₁ * (f₁ * f₂) * f₂ := by rw [hf₁f₂]
          _ = (f₁ * f₁) * (f₂ * f₂) := by group
          _ = 1 := by rw [hf₁2, hf₂2, one_mul]
      rw [← map_mul, hmul, map_one]
    have hfixcard : Nat.card (fixedBy A (A.normalizerMonoidHom
        ⟨f₁ * f₂, mul_mem hf₁K hf₂K⟩)) = 4 := by
      rw [card_fixedBy_normalizerMonoidHom (mul_mem hf₁K hf₂K), h₁₂]
    have he₁ : A.normalizerMonoidHom ⟨f₁ * f₂, mul_mem hf₁K hf₂K⟩
        ⟨z₁, hz₁A⟩ = ⟨z₁, hz₁A⟩ := by
      apply Subtype.ext
      change (f₁ * f₂) * z₁ * (f₁ * f₂)⁻¹ = z₁
      have h1z : f₁ * z₁ * f₁⁻¹ = z₁ := by rw [hz₁_centS₁ f₁ hf₁S₁]; group
      have h2z : f₂ * z₁ * f₂⁻¹ = z₁ := by rw [← 𝔖.decomp.comm hz₁S₁ hf₂S₂]; group
      calc (f₁ * f₂) * z₁ * (f₁ * f₂)⁻¹ = f₁ * (f₂ * z₁ * f₂⁻¹) * f₁⁻¹ := by group
        _ = f₁ * z₁ * f₁⁻¹ := by rw [h2z]
        _ = z₁ := h1z
    have he₂ : A.normalizerMonoidHom ⟨f₁ * f₂, mul_mem hf₁K hf₂K⟩
        ⟨z₂, hz₂A⟩ = ⟨z₂, hz₂A⟩ := by
      apply Subtype.ext
      change (f₁ * f₂) * z₂ * (f₁ * f₂)⁻¹ = z₂
      have h1z : f₁ * z₂ * f₁⁻¹ = z₂ := by rw [𝔖.decomp.comm hf₁S₁ hz₂S₂]; group
      have h2z : f₂ * z₂ * f₂⁻¹ = z₂ := by rw [hz₂_centS₂ f₂ hf₂S₂]; group
      calc (f₁ * f₂) * z₂ * (f₁ * f₂)⁻¹ = f₁ * (f₂ * z₂ * f₂⁻¹) * f₁⁻¹ := by group
        _ = f₁ * z₂ * f₁⁻¹ := by rw [h2z]
        _ = z₂ := h1z
    have he₁1 : (⟨z₁, hz₁A⟩ : A) ≠ 1 := hτ₁z1
    have he₂1 : (⟨z₂, hz₂A⟩ : A) ≠ 1 := hτ₂z1
    have hh2apply : ∀ v : A, A.normalizerMonoidHom ⟨f₁ * f₂, mul_mem hf₁K hf₂K⟩
        (A.normalizerMonoidHom ⟨f₁ * f₂, mul_mem hf₁K hf₂K⟩ v) = v := by
      intro v
      have := congrArg (fun e : MulAut A => e v) hh2
      simpa [MulAut.mul_apply] using this
    obtain ⟨n, hn⟩ := CFSG.GH72.exists_zpow_apply_eq_of_commute_of_card_fixedBy_eq_four
      (mul_self_eq_one_of_isE16 hA) hh2apply hfixcard hσcomm hσodd hσ1 he₁ he₁1 he₂ he₂1
    have hconjz : IsConj z₁ z₂ := by
      refine isConj_iff.mpr ⟨q ^ n, ?_⟩
      have hcoe : ((σ ^ n) ⟨z₁, hz₁A⟩ : G) = z₂ := congrArg Subtype.val hn
      have hσpow : σ ^ n = φ (⟨q, hqK⟩ ^ n) := by rw [map_zpow]
      rw [hσpow] at hcoe
      change q ^ n * z₁ * (q ^ n)⁻¹ = z₂ at hcoe
      exact hcoe
    have := lemma_3_8 𝔖 h₁ z₁ hz₁S z₂ hz₂S hz₁_centS hz₂_centS hz₁ord hconjz
    exact hz₁z₂ this
  have hGL := relIndex_mem_of_transvections hA hf₁K hf₂K hf₁f₂ hz₁A hz₂A htrans₁ hf₁C
    htrans₂ hf₂C h₁₂ hQ_le_K hQ_index_odd hf₁Q hf₂Q
  obtain ⟨h139, h3case, h9case⟩ := hGL
  have hPsub_e1 : ∀ τ ∈ Psub, τ ⟨z₁, hz₁A⟩ = ⟨z₁, hz₁A⟩ := by
    have hτ₁e : τ₁ ⟨z₁, hz₁A⟩ = ⟨z₁, hz₁A⟩ := by
      apply Subtype.ext
      change f₁ * z₁ * f₁⁻¹ = z₁
      rw [hz₁_centS₁ f₁ hf₁S₁]; group
    have hτ₂e : τ₂ ⟨z₁, hz₁A⟩ = ⟨z₁, hz₁A⟩ := by
      apply Subtype.ext
      change f₂ * z₁ * f₂⁻¹ = z₁
      rw [← 𝔖.decomp.comm hz₁S₁ hf₂S₂]; group
    intro τ hτ
    rw [hPsub_eq] at hτ
    obtain ⟨u, hu, v, hv, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm (fun u hu v hv => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        exact (show Commute τ₁ τ₂ from hτcomm).zpow_zpow m n |>.eq))).1 hτ
    have hve : v ⟨z₁, hz₁A⟩ = ⟨z₁, hz₁A⟩ := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact mem_fixedBy_zpow (g := τ₂) (show ⟨z₁, hz₁A⟩ ∈ fixedBy A τ₂ from hτ₂e) n
    have hue : u ⟨z₁, hz₁A⟩ = ⟨z₁, hz₁A⟩ := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact mem_fixedBy_zpow (g := τ₁) (show ⟨z₁, hz₁A⟩ ∈ fixedBy A τ₁ from hτ₁e) n
    rw [MulAut.mul_apply, hve, hue]
  have hPsub_e2 : ∀ τ ∈ Psub, τ ⟨z₂, hz₂A⟩ = ⟨z₂, hz₂A⟩ := by
    have hτ₁e : τ₁ ⟨z₂, hz₂A⟩ = ⟨z₂, hz₂A⟩ := by
      apply Subtype.ext
      change f₁ * z₂ * f₁⁻¹ = z₂
      rw [𝔖.decomp.comm hf₁S₁ hz₂S₂]; group
    have hτ₂e : τ₂ ⟨z₂, hz₂A⟩ = ⟨z₂, hz₂A⟩ := by
      apply Subtype.ext
      change f₂ * z₂ * f₂⁻¹ = z₂
      rw [hz₂_centS₂ f₂ hf₂S₂]; group
    intro τ hτ
    rw [hPsub_eq] at hτ
    obtain ⟨u, hu, v, hv, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm (fun u hu v hv => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        exact (show Commute τ₁ τ₂ from hτcomm).zpow_zpow m n |>.eq))).1 hτ
    have hve : v ⟨z₂, hz₂A⟩ = ⟨z₂, hz₂A⟩ := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact mem_fixedBy_zpow (g := τ₂) (show ⟨z₂, hz₂A⟩ ∈ fixedBy A τ₂ from hτ₂e) n
    have hue : u ⟨z₂, hz₂A⟩ = ⟨z₂, hz₂A⟩ := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact mem_fixedBy_zpow (g := τ₁) (show ⟨z₂, hz₂A⟩ ∈ fixedBy A τ₁ from hτ₁e) n
    rw [MulAut.mul_apply, hve, hue]
  have hL_decomp : L = QbarAmb ⊔ Psub := by
    calc L = (⊤ : Subgroup L).map L.subtype := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = (Qbar ⊔ Psyl).map L.subtype := by rw [hQbar_compl.sup_eq_top]
      _ = QbarAmb ⊔ Psub := by
          rw [Subgroup.map_sup, hPsyl_coe, Subgroup.map_subgroupOf_eq_of_le hPsub_le_L]
  have haz : a ≠ z₁ := by
    intro h
    apply ha_moved
    rw [h]
    show f₁ * z₁ * f₁⁻¹ = z₁
    rw [hz₁_centS₁ f₁ hf₁S₁]
    group
  have hcz : c ≠ z₂ := by
    intro h
    apply htrans_c
    rw [h]
    show f₂ * z₂ * f₂⁻¹ = z₂
    rw [hz₂_centS₂ f₂ hf₂S₂]
    group
  have hQbar_stab_e1 : (∀ q ∈ Q, q * z₁ * q⁻¹ = z₁) →
      QbarAmb ≤ MulAction.stabilizer (MulAut A) (⟨z₁, hz₁A⟩ : A) := by
    intro hfix y hy
    obtain ⟨qbar, hqbar, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp qbar.2
    have hkcomap : (k : K) ∈ QbarAmb.comap φ := by
      rw [Subgroup.mem_comap, hk]
      exact Subgroup.mem_map_of_mem L.subtype hqbar
    rw [← hQsub_eq] at hkcomap
    have hkQ : (k : G) ∈ Q := Subgroup.mem_subgroupOf.mp hkcomap
    have hkfix : (k : G) * z₁ * (k : G)⁻¹ = z₁ := hfix (k : G) hkQ
    rw [MulAction.mem_stabilizer_iff]
    change qbar.1 ⟨z₁, hz₁A⟩ = ⟨z₁, hz₁A⟩
    rw [← hk]
    apply Subtype.ext
    change (k : G) * z₁ * (k : G)⁻¹ = z₁
    exact hkfix
  have hQbar_stab_e2 : (∀ q ∈ Q, q * z₂ * q⁻¹ = z₂) →
      QbarAmb ≤ MulAction.stabilizer (MulAut A) (⟨z₂, hz₂A⟩ : A) := by
    intro hfix y hy
    obtain ⟨qbar, hqbar, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp qbar.2
    have hkcomap : (k : K) ∈ QbarAmb.comap φ := by
      rw [Subgroup.mem_comap, hk]
      exact Subgroup.mem_map_of_mem L.subtype hqbar
    rw [← hQsub_eq] at hkcomap
    have hkQ : (k : G) ∈ Q := Subgroup.mem_subgroupOf.mp hkcomap
    have hkfix : (k : G) * z₂ * (k : G)⁻¹ = z₂ := hfix (k : G) hkQ
    rw [MulAction.mem_stabilizer_iff]
    change qbar.1 ⟨z₂, hz₂A⟩ = ⟨z₂, hz₂A⟩
    rw [← hk]
    apply Subtype.ext
    change (k : G) * z₂ * (k : G)⁻¹ = z₂
    exact hkfix
  have hPsub_stab_e1 : Psub ≤ MulAction.stabilizer (MulAut A) (⟨z₁, hz₁A⟩ : A) := by
    intro τ hτ
    rw [MulAction.mem_stabilizer_iff]
    exact hPsub_e1 τ hτ
  have hPsub_stab_e2 : Psub ≤ MulAction.stabilizer (MulAut A) (⟨z₂, hz₂A⟩ : A) := by
    intro τ hτ
    rw [MulAction.mem_stabilizer_iff]
    exact hPsub_e2 τ hτ
  have hL_stab_e1 : (∀ q ∈ Q, q * z₁ * q⁻¹ = z₁) → L ≤
      MulAction.stabilizer (MulAut A) (⟨z₁, hz₁A⟩ : A) := by
    intro hfix
    rw [hL_decomp]
    exact sup_le (hQbar_stab_e1 hfix) hPsub_stab_e1
  have hL_stab_e2 : (∀ q ∈ Q, q * z₂ * q⁻¹ = z₂) → L ≤
      MulAction.stabilizer (MulAut A) (⟨z₂, hz₂A⟩ : A) := by
    intro hfix
    rw [hL_decomp]
    exact sup_le (hQbar_stab_e2 hfix) hPsub_stab_e2
  have hKfix_of_e1 : L ≤ MulAction.stabilizer (MulAut A) (⟨z₁, hz₁A⟩ : A) →
      ∀ k ∈ K, k * z₁ * k⁻¹ = z₁ := by
    intro hstab k hk
    have hφk : φ ⟨k, hk⟩ ∈ L := MonoidHom.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩
    have hkstab := hstab hφk
    rw [MulAction.mem_stabilizer_iff] at hkstab
    have hcoe : ((φ ⟨k, hk⟩) ⟨z₁, hz₁A⟩ : G) = z₁ := congrArg Subtype.val hkstab
    change k * z₁ * k⁻¹ = z₁ at hcoe
    exact hcoe
  have hKfix_of_e2 : L ≤ MulAction.stabilizer (MulAut A) (⟨z₂, hz₂A⟩ : A) →
      ∀ k ∈ K, k * z₂ * k⁻¹ = z₂ := by
    intro hstab k hk
    have hφk : φ ⟨k, hk⟩ ∈ L := MonoidHom.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩
    have hkstab := hstab hφk
    rw [MulAction.mem_stabilizer_iff] at hkstab
    have hcoe : ((φ ⟨k, hk⟩) ⟨z₂, hz₂A⟩ : G) = z₂ := congrArg Subtype.val hkstab
    change k * z₂ * k⁻¹ = z₂ at hcoe
    exact hcoe
  have hcontra_e1 : L ≤ MulAction.stabilizer (MulAut A) (⟨z₁, hz₁A⟩ : A) → False := by
    intro hstab
    obtain ⟨k, hkK, hka⟩ := hconj_a
    have hkz : k * z₁ * k⁻¹ = z₁ := hKfix_of_e1 hstab k hkK
    have hz : k⁻¹ * z₁ * k = z₁ := by
      have := congrArg (fun x => k⁻¹ * x * k) hkz
      simpa [mul_assoc] using this.symm
    have : a = z₁ := by
      calc a = k⁻¹ * z₁ * k := by rw [← hka]; group
        _ = z₁ := hz
    exact haz this
  have hcontra_e2 : L ≤ MulAction.stabilizer (MulAut A) (⟨z₂, hz₂A⟩ : A) → False := by
    intro hstab
    obtain ⟨k, hkK, hkc⟩ := hconj_c
    have hkz : k * z₂ * k⁻¹ = z₂ := hKfix_of_e2 hstab k hkK
    have hz : k⁻¹ * z₂ * k = z₂ := by
      have := congrArg (fun x => k⁻¹ * x * k) hkz
      simpa [mul_assoc] using this.symm
    have : c = z₂ := by
      calc c = k⁻¹ * z₂ * k := by rw [← hkc]; group
        _ = z₂ := hz
    exact hcz this
  have hQ9 : Cc.relIndex Q = 9 := by
    obtain h1 | h3 | h9 := h139
    ·
      have hQeq : Q = Cc := by
        have hsub : Q ≤ Cc := by
          have hidx : (Cc.subgroupOf Q).index = 1 := by
            rw [← Subgroup.relIndex, h1]
          exact Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp hidx)
        exact le_antisymm hsub hC_le_Q
      have hQbar_card1 : Nat.card Qbar = 1 := by
        rw [← hQ_index_card, hQeq, Subgroup.relIndex_self]
      have hLcard : Nat.card L = 4 := by
        have hcard := hQbar_compl.card_mul_card
        rw [hPsyl_coe] at hcard
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPsub_le_L).toEquiv,
          hPsub_card] at hcard
        rw [hQbar_card1, one_mul] at hcard
        exact hcard.symm
      have hL_eq : L = Psub := by
        refine (Subgroup.eq_of_le_of_card_ge hPsub_le_L ?_).symm
        rw [hLcard, hPsub_card]
      exfalso
      exact hcontra_e1 (hL_eq ▸ hPsub_stab_e1)
    ·
      rcases h3case h3 with ⟨f, hf, hcomm⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl | rfl
      · have hfix : ∀ q ∈ Q, q * z₁ * q⁻¹ = z₁ := by
          intro q hq
          exact conj_eq_of_commute_of_transvection hA hf₁K hz₁A htrans₁ hf₁C
            (hQ_le_K hq) (hcomm q hq)
        exfalso
        exact hcontra_e1 (hL_stab_e1 hfix)
      · have hfix : ∀ q ∈ Q, q * z₂ * q⁻¹ = z₂ := by
          intro q hq
          exact conj_eq_of_commute_of_transvection hA hf₂K hz₂A htrans₂ hf₂C
            (hQ_le_K hq) (hcomm q hq)
        exfalso
        exact hcontra_e2 (hL_stab_e2 hfix)
      ·
        have hQne : Q ≠ Cc := by
          intro hQC
          have hidx : Cc.relIndex Q = 1 := by rw [hQC, Subgroup.relIndex_self]
          rw [h3] at hidx
          norm_num at hidx
        obtain ⟨q, hqQ, hqC⟩ : ∃ q ∈ Q, q ∉ Cc := by
          by_contra h
          apply hQne
          exact le_antisymm (fun q hq => by
            by_contra hqC
            exact h ⟨q, hq, hqC⟩) hC_le_Q
        exfalso
        exact hqC (hno q hqQ (hcomm q hqQ))
    · exact h9
  obtain ⟨u₁, hu₁Q, u₂, hu₂Q, hu₁C, hu₂C, hu₁f, hu₂f, hrep⟩ := h9case hQ9 hno
  let σ₁ : MulAut A := φ ⟨u₁, hQ_le_K hu₁Q⟩
  let σ₂ : MulAut A := φ ⟨u₂, hQ_le_K hu₂Q⟩
  have hσ₁mem : σ₁ ∈ QbarAmb := by
    have hqsub : (⟨u₁, hQ_le_K hu₁Q⟩ : K) ∈ Q.subgroupOf K := hu₁Q
    rw [hQsub_eq] at hqsub
    exact Subgroup.mem_comap.mp hqsub
  have hσ₂mem : σ₂ ∈ QbarAmb := by
    have hqsub : (⟨u₂, hQ_le_K hu₂Q⟩ : K) ∈ Q.subgroupOf K := hu₂Q
    rw [hQsub_eq] at hqsub
    exact Subgroup.mem_comap.mp hqsub
  have hσ₁1 : σ₁ ≠ 1 := by
    intro h
    exact hu₁C ((normalizerMonoidHom_eq_one_iff (hQ_le_K hu₁Q)).mp h)
  have hσ₂1 : σ₂ ≠ 1 := by
    intro h
    exact hu₂C ((normalizerMonoidHom_eq_one_iff (hQ_le_K hu₂Q)).mp h)
  have hQbarAmb_card9 : Nat.card QbarAmb = 9 := by
    rw [hQbarAmb_card', ← hQ_index_card, hQ9]
  have hσ₁odd : Odd (orderOf σ₁) :=
    hQbar_odd.of_dvd_nat (hQbarAmb_card' ▸
      Subgroup.orderOf_dvd_natCard (s := QbarAmb) (x := σ₁) hσ₁mem)
  have hσ₂odd : Odd (orderOf σ₂) :=
    hQbar_odd.of_dvd_nat (hQbarAmb_card' ▸
      Subgroup.orderOf_dvd_natCard (s := QbarAmb) (x := σ₂) hσ₂mem)
  haveI : IsMulCommutative ↥QbarAmb :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by
      rw [hQbarAmb_card9]; norm_num)
  have hσcomm : σ₁ * σ₂ = σ₂ * σ₁ :=
    congrArg Subtype.val (IsMulCommutative.is_comm.comm
      ⟨σ₁, hσ₁mem⟩ ⟨σ₂, hσ₂mem⟩)
  have hσ₁z : σ₁ ⟨z₁, hz₁A⟩ = ⟨z₁, hz₁A⟩ := by
    apply Subtype.ext
    change u₁ * z₁ * u₁⁻¹ = z₁
    exact conj_eq_of_commute_of_transvection hA hf₁K hz₁A htrans₁ hf₁C
      (hQ_le_K hu₁Q) hu₁f
  have hσ₂z : σ₂ ⟨z₂, hz₂A⟩ = ⟨z₂, hz₂A⟩ := by
    apply Subtype.ext
    change u₂ * z₂ * u₂⁻¹ = z₂
    exact conj_eq_of_commute_of_transvection hA hf₂K hz₂A htrans₂ hf₂C
      (hQ_le_K hu₂Q) hu₂f
  have hu₁z : u₁ * z₁ * u₁⁻¹ = z₁ := congrArg Subtype.val hσ₁z
  have hu₂z : u₂ * z₂ * u₂⁻¹ = z₂ := congrArg Subtype.val hσ₂z
  obtain ⟨hXcard, hXinv, hXorb⟩ :=
    conj_orbit_eq_of_relIndex_eq_nine hA hQ_le_K hQ9 hu₁Q hu₁C hz₁A hz₁1 hu₁z
  set X : Subgroup G := A ⊓ centralizer {u₁} with hX
  have ha_orbit : a ∈ {b : G | ∃ g ∈ Q, g * z₁ * g⁻¹ = b} := by
    obtain ⟨k, hkK, hka⟩ := hconj_a
    let k' : K := ⟨k⁻¹, Subgroup.inv_mem (H := K) hkK⟩
    have ha_e1 : a = (φ k') ⟨z₁, hz₁A⟩ := by
      have hca : (φ k') ⟨z₁, hz₁A⟩ = ⟨a, haA⟩ := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        dsimp only [k']
        rw [← hka]; group
      exact (congrArg Subtype.val hca).symm
    have hxdecomp : φ k' ∈ QbarAmb ⊔ Psub := by
      rw [← hL_decomp]
      exact MonoidHom.mem_range.mpr ⟨k', rfl⟩
    obtain ⟨qbar, hqbar, p, hp, hqp⟩ :=
      (mem_sup_iff_of_le_normalizer (show Psub ≤
        Subgroup.normalizer (QbarAmb : Set (MulAut A)) from
          fun x hx => hQbarAmb_norm (hPsub_le_L hx))).1 hxdecomp
    have hQmap : (Q.subgroupOf K).map φ = QbarAmb := by
      rw [hQsub_eq, Subgroup.map_comap_eq_self hQbarAmb_le_L]
    rw [← hQmap] at hqbar
    obtain ⟨q, hqQ, hqφ⟩ := Subgroup.mem_map.mp hqbar
    have hqbar_e1 : (qbar ⟨z₁, hz₁A⟩ : G) = q * z₁ * q⁻¹ := by
      rw [← hqφ]
      rfl
    have hp_e1 : p ⟨z₁, hz₁A⟩ = ⟨z₁, hz₁A⟩ := hPsub_e1 p hp
    refine ⟨q, hqQ, ?_⟩
    have h1 : a = ((φ k') ⟨z₁, hz₁A⟩ : G) := ha_e1
    have h2 : ((φ k') ⟨z₁, hz₁A⟩ : G) =
        (((qbar * p) ⟨z₁, hz₁A⟩ : A) : G) := by rw [hqp]
    have h3 : (((qbar * p) ⟨z₁, hz₁A⟩ : A) : G) =
        ((qbar ⟨z₁, hz₁A⟩ : A) : G) := by rw [MulAut.mul_apply, hp_e1]
    have h4 : ((qbar ⟨z₁, hz₁A⟩ : A) : G) = q * z₁ * q⁻¹ := hqbar_e1
    exact (h1.trans (h2.trans (h3.trans h4))).symm
  have haX : a ∈ X := by
    have hset := hXorb
    have : a ∈ ((X : Set G) \ {1}) := by
      rw [← hset]
      exact ha_orbit
    exact this.1
  have hz₁X : z₁ ∈ X := by
    refine Subgroup.mem_inf.mpr ⟨hz₁A, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := congrArg (fun x => x * u₁) hu₁z
    simpa [mul_assoc] using hcomm.symm
  have hA₁cardX : Nat.card X = 4 := hXcard
  have hA₁_le_X : A₁ ≤ X := by
    haveI : Fintype A₁ := Fintype.ofFinite A₁
    haveI : IsKleinFour ↥A₁ := isKleinFour_of_isFourIn hV₁
    intro y hy
    have hy' : (⟨y, hy⟩ : A₁) ∈ (Finset.univ : Finset A₁) := Finset.mem_univ _
    have huniv := IsKleinFour.eq_finset_univ (G := ↥A₁)
      (x := (⟨z₁, hz₁A₁⟩ : A₁)) (y := (⟨a, haA₁⟩ : A₁))
      (by intro h; exact hz₁1 (congrArg Subtype.val h))
      (by intro h; exact ha1 (congrArg Subtype.val h)) (by
        intro h
        exact haz (congrArg Subtype.val h).symm)
    rw [← huniv] at hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
    rcases hy' with h1 | h2 | h3 | h4
    · have : y = z₁ * a := congrArg Subtype.val h1
      rw [this]
      exact X.mul_mem hz₁X haX
    · have : y = z₁ := congrArg Subtype.val h2
      rwa [this]
    · have : y = a := congrArg Subtype.val h3
      rwa [this]
    · have : y = 1 := congrArg Subtype.val h4
      rw [this]
      exact X.one_mem
  have hXeq : X = A₁ := by
    exact (Subgroup.eq_of_le_of_card_ge hA₁_le_X (by rw [hA₁cardX, hA₁card])).symm
  have hQX : ∀ q ∈ Q, ∀ x ∈ A₁, q * x * q⁻¹ ∈ A₁ := by
    intro q hq x hx
    rw [← hXeq] at hx ⊢
    exact hXinv q hq x hx
  obtain ⟨hYcard, hYinv, hYorb⟩ :=
    conj_orbit_eq_of_relIndex_eq_nine hA hQ_le_K hQ9 hu₂Q hu₂C hz₂A hz₂1 hu₂z
  set Y : Subgroup G := A ⊓ centralizer {u₂} with hY
  have hc_orbit : c ∈ {b : G | ∃ g ∈ Q, g * z₂ * g⁻¹ = b} := by
    obtain ⟨k, hkK, hkc⟩ := hconj_c
    let k' : K := ⟨k⁻¹, Subgroup.inv_mem (H := K) hkK⟩
    have hc_e1 : c = (φ k') ⟨z₂, hz₂A⟩ := by
      have hca : (φ k') ⟨z₂, hz₂A⟩ = ⟨c, hcA⟩ := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        dsimp only [k']
        rw [← hkc]; group
      exact (congrArg Subtype.val hca).symm
    have hxdecomp : φ k' ∈ QbarAmb ⊔ Psub := by
      rw [← hL_decomp]
      exact MonoidHom.mem_range.mpr ⟨k', rfl⟩
    obtain ⟨qbar, hqbar, p, hp, hqp⟩ :=
      (mem_sup_iff_of_le_normalizer (show Psub ≤
        Subgroup.normalizer (QbarAmb : Set (MulAut A)) from
          fun x hx => hQbarAmb_norm (hPsub_le_L hx))).1 hxdecomp
    have hQmap : (Q.subgroupOf K).map φ = QbarAmb := by
      rw [hQsub_eq, Subgroup.map_comap_eq_self hQbarAmb_le_L]
    rw [← hQmap] at hqbar
    obtain ⟨q, hqQ, hqφ⟩ := Subgroup.mem_map.mp hqbar
    have hqbar_e1 : (qbar ⟨z₂, hz₂A⟩ : G) = q * z₂ * q⁻¹ := by
      rw [← hqφ]
      rfl
    have hp_e1 : p ⟨z₂, hz₂A⟩ = ⟨z₂, hz₂A⟩ := hPsub_e2 p hp
    refine ⟨q, hqQ, ?_⟩
    have h1 : c = ((φ k') ⟨z₂, hz₂A⟩ : G) := hc_e1
    have h2 : ((φ k') ⟨z₂, hz₂A⟩ : G) =
        (((qbar * p) ⟨z₂, hz₂A⟩ : A) : G) := by rw [hqp]
    have h3 : (((qbar * p) ⟨z₂, hz₂A⟩ : A) : G) =
        ((qbar ⟨z₂, hz₂A⟩ : A) : G) := by rw [MulAut.mul_apply, hp_e1]
    have h4 : ((qbar ⟨z₂, hz₂A⟩ : A) : G) = q * z₂ * q⁻¹ := hqbar_e1
    exact (h1.trans (h2.trans (h3.trans h4))).symm
  have hcY : c ∈ Y := by
    have : c ∈ ((Y : Set G) \ {1}) := by
      rw [← hYorb]
      exact hc_orbit
    exact this.1
  have hz₂Y : z₂ ∈ Y := by
    refine Subgroup.mem_inf.mpr ⟨hz₂A, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := congrArg (fun x => x * u₂) hu₂z
    simpa [mul_assoc] using hcomm.symm
  have hA₂_le_Y : A₂ ≤ Y := by
    haveI : Fintype A₂ := Fintype.ofFinite A₂
    haveI : IsKleinFour ↥A₂ := isKleinFour_of_isFourIn hV₂
    intro y hy
    have hy' : (⟨y, hy⟩ : A₂) ∈ (Finset.univ : Finset A₂) := Finset.mem_univ _
    have huniv := IsKleinFour.eq_finset_univ (G := ↥A₂)
      (x := (⟨z₂, hz₂A₂⟩ : A₂)) (y := (⟨c, hcA₂⟩ : A₂))
      (by intro h; exact hz₂1 (congrArg Subtype.val h))
      (by intro h; exact hc1 (congrArg Subtype.val h)) (by
        intro h
        exact hcz (congrArg Subtype.val h).symm)
    rw [← huniv] at hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
    rcases hy' with h1 | h2 | h3 | h4
    · have : y = z₂ * c := congrArg Subtype.val h1
      rw [this]
      exact Y.mul_mem hz₂Y hcY
    · have : y = z₂ := congrArg Subtype.val h2
      rwa [this]
    · have : y = c := congrArg Subtype.val h3
      rwa [this]
    · have : y = 1 := congrArg Subtype.val h4
      rw [this]
      exact Y.one_mem
  have hYeq : Y = A₂ := by
    exact (Subgroup.eq_of_le_of_card_ge hA₂_le_Y (by rw [hYcard, hA₂card])).symm
  have hQY : ∀ q ∈ Q, ∀ y ∈ A₂, q * y * q⁻¹ ∈ A₂ := by
    intro q hq y hy
    rw [← hYeq] at hy ⊢
    exact hYinv q hq y hy
  have memA_of_A₁ : ∀ {x : G}, x ∈ A₁ → x ∈ A := fun hx => (Subgroup.mem_inf.mp hx).1
  have memA_of_A₂ : ∀ {x : G}, x ∈ A₂ → x ∈ A := fun hx => (Subgroup.mem_inf.mp hx).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨Q, hC_le_Q, hQ_le_K, hQnorm_sub, hQ9, 2, ?_⟩
    have hmul : Cc.relIndex Q * Q.relIndex K = Cc.relIndex K :=
      Subgroup.relIndex_mul_relIndex (H := Cc) (K := Q) (L := K) hC_le_Q hQ_le_K
    have hLcard : Nat.card L = Cc.relIndex K := hL_card
    have hcard := hQbar_compl.card_mul_card
    have hPsyl_card : Nat.card (Psyl : Subgroup L) = 4 := by
      rw [hPsyl_coe, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPsub_le_L).toEquiv,
        hPsub_card]
    rw [hPsyl_card, ← hQ_index_card, hQ9] at hcard
    rw [hLcard, ← hmul, hQ9] at hcard
    change Q.relIndex K = 2 ^ 2
    omega
  ·
    have hA₁_eq : A₁ = 𝔖.S₁ ⊓ A := by
      change A ⊓ 𝔖.S₁ = 𝔖.S₁ ⊓ A
      exact inf_comm A 𝔖.S₁
    rw [← hA₁_eq]
    let Stab₁ : Subgroup (MulAut A) :=
      MulAction.stabilizer (MulAut A) (A₁.subgroupOf A)
    have hstab₁_of : ∀ q : MulAut A,
        (∀ x : A, (x : G) ∈ A₁ → q x ∈ A₁.subgroupOf A) → q ∈ Stab₁ := by
      intro q hq
      rw [MulAction.mem_stabilizer_iff]
      have hle : (A₁.subgroupOf A).map q.toMonoidHom ≤ A₁.subgroupOf A := by
        rintro x ⟨y, hy, rfl⟩
        exact hq y (Subgroup.mem_subgroupOf.mp hy)
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      have hcard : Nat.card ((A₁.subgroupOf A).map q.toMonoidHom) =
          Nat.card (A₁.subgroupOf A) :=
        Subgroup.card_map_of_injective (f := q.toMonoidHom) q.injective
      change Nat.card (A₁.subgroupOf A) ≤
        Nat.card ((A₁.subgroupOf A).map q.toMonoidHom)
      rw [hcard]
    have hτ₁_stab : τ₁ ∈ Stab₁ := by
      apply hstab₁_of
      intro x hx
      have hxN : f₁ * (x : G) * f₁⁻¹ ∈ A₁ :=
        (Subgroup.mem_normalizer_iff.mp hf₁N (x : G)).mp hx
      exact Subgroup.mem_subgroupOf.mpr hxN
    have hτ₂_stab : τ₂ ∈ Stab₁ := by
      apply hstab₁_of
      intro x hx
      have hfix : τ₂ x = x := by
        apply Subtype.ext
        change f₂ * (x : G) * f₂⁻¹ = (x : G)
        rw [← 𝔖.decomp.comm hx.2 hf₂S₂]; group
      rw [hfix]
      exact Subgroup.mem_subgroupOf.mpr hx
    have hPsub_stab₁ : Psub ≤ Stab₁ := by
      rw [hPsub_eq]
      exact sup_le (Subgroup.zpowers_le.mpr hτ₁_stab) (Subgroup.zpowers_le.mpr hτ₂_stab)
    have hQbar_stab₁ : QbarAmb ≤ Stab₁ := by
      intro q hq
      have hQmap : (Q.subgroupOf K).map φ = QbarAmb := by
        rw [hQsub_eq, Subgroup.map_comap_eq_self hQbarAmb_le_L]
      rw [← hQmap] at hq
      obtain ⟨kq, hkqQ, hkq⟩ := Subgroup.mem_map.mp hq
      rw [← hkq]
      apply hstab₁_of
      intro x hx
      exact hQX (kq : G) (Subgroup.mem_subgroupOf.mp hkqQ) (x : G) hx
    have hL_stab₁ : L ≤ Stab₁ := by
      rw [hL_decomp]
      exact sup_le hQbar_stab₁ hPsub_stab₁
    intro k hk
    have hkK : k ∈ K := hk
    have hφkL : φ ⟨k, hkK⟩ ∈ L := MonoidHom.mem_range.mpr ⟨⟨k, hkK⟩, rfl⟩
    have hφkstab : φ ⟨k, hkK⟩ ∈ Stab₁ := hL_stab₁ hφkL
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : (⟨x, memA_of_A₁ hx⟩ : A) ∈ A₁.subgroupOf A := hx
      have hmap := (MulAction.mem_stabilizer_iff.mp hφkstab)
      have hmem : (φ ⟨k, hkK⟩) ⟨x, memA_of_A₁ hx⟩ ∈ A₁.subgroupOf A := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ hx'
      have hmemG : ((φ ⟨k, hkK⟩) ⟨x, memA_of_A₁ hx⟩ : G) ∈ A₁ :=
        Subgroup.mem_subgroupOf.mp hmem
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hmemG
      exact hmemG
    · intro hx
      have hk'inv : k⁻¹ ∈ K := Subgroup.inv_mem (H := K) hkK
      have hφkinvL : φ ⟨k⁻¹, hk'inv⟩ ∈ L :=
        MonoidHom.mem_range.mpr ⟨⟨k⁻¹, hk'inv⟩, rfl⟩
      have hφkinvstab : φ ⟨k⁻¹, hk'inv⟩ ∈ Stab₁ := hL_stab₁ hφkinvL
      have hx' : (⟨k * x * k⁻¹, memA_of_A₁ hx⟩ : A) ∈ A₁.subgroupOf A := hx
      have hmap := (MulAction.mem_stabilizer_iff.mp hφkinvstab)
      have hmem : (φ ⟨k⁻¹, hk'inv⟩) ⟨k * x * k⁻¹, memA_of_A₁ hx⟩ ∈ A₁.subgroupOf A := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ hx'
      have hmemG : ((φ ⟨k⁻¹, hk'inv⟩) ⟨k * x * k⁻¹, memA_of_A₁ hx⟩ : G) ∈ A₁ :=
        Subgroup.mem_subgroupOf.mp hmem
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hmemG
      simpa [mul_assoc] using hmemG
  ·
    have hA₂_eq : A₂ = 𝔖.S₂ ⊓ A := by
      change A ⊓ 𝔖.S₂ = 𝔖.S₂ ⊓ A
      exact inf_comm A 𝔖.S₂
    rw [← hA₂_eq]
    let Stab₂ : Subgroup (MulAut A) :=
      MulAction.stabilizer (MulAut A) (A₂.subgroupOf A)
    have hstab₂_of : ∀ q : MulAut A,
        (∀ x : A, (x : G) ∈ A₂ → q x ∈ A₂.subgroupOf A) → q ∈ Stab₂ := by
      intro q hq
      rw [MulAction.mem_stabilizer_iff]
      have hle : (A₂.subgroupOf A).map q.toMonoidHom ≤ A₂.subgroupOf A := by
        rintro x ⟨y, hy, rfl⟩
        exact hq y (Subgroup.mem_subgroupOf.mp hy)
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      have hcard : Nat.card ((A₂.subgroupOf A).map q.toMonoidHom) =
          Nat.card (A₂.subgroupOf A) :=
        Subgroup.card_map_of_injective (f := q.toMonoidHom) q.injective
      change Nat.card (A₂.subgroupOf A) ≤
        Nat.card ((A₂.subgroupOf A).map q.toMonoidHom)
      rw [hcard]
    have hτ₁_stab₂ : τ₁ ∈ Stab₂ := by
      apply hstab₂_of
      intro x hx
      have hfix : τ₁ x = x := by
        apply Subtype.ext
        change f₁ * (x : G) * f₁⁻¹ = (x : G)
        rw [𝔖.decomp.comm hf₁S₁ hx.2]; group
      rw [hfix]
      exact hx
    have hτ₂_stab₂ : τ₂ ∈ Stab₂ := by
      apply hstab₂_of
      intro x hx
      have hxN : f₂ * (x : G) * f₂⁻¹ ∈ A₂ :=
        (Subgroup.mem_normalizer_iff.mp hf₂N (x : G)).mp hx
      exact Subgroup.mem_subgroupOf.mpr hxN
    have hPsub_stab₂ : Psub ≤ Stab₂ := by
      rw [hPsub_eq]
      exact sup_le (Subgroup.zpowers_le.mpr hτ₁_stab₂) (Subgroup.zpowers_le.mpr hτ₂_stab₂)
    have hQbar_stab₂ : QbarAmb ≤ Stab₂ := by
      intro q hq
      have hQmap : (Q.subgroupOf K).map φ = QbarAmb := by
        rw [hQsub_eq, Subgroup.map_comap_eq_self hQbarAmb_le_L]
      rw [← hQmap] at hq
      obtain ⟨kq, hkqQ, hkq⟩ := Subgroup.mem_map.mp hq
      rw [← hkq]
      apply hstab₂_of
      intro x hx
      exact hQY (kq : G) (Subgroup.mem_subgroupOf.mp hkqQ) (x : G) hx
    have hL_stab₂ : L ≤ Stab₂ := by
      rw [hL_decomp]
      exact sup_le hQbar_stab₂ hPsub_stab₂
    intro k hk
    have hkK : k ∈ K := hk
    have hφkL : φ ⟨k, hkK⟩ ∈ L := MonoidHom.mem_range.mpr ⟨⟨k, hkK⟩, rfl⟩
    have hφkstab : φ ⟨k, hkK⟩ ∈ Stab₂ := hL_stab₂ hφkL
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : (⟨x, memA_of_A₂ hx⟩ : A) ∈ A₂.subgroupOf A := hx
      have hmap := (MulAction.mem_stabilizer_iff.mp hφkstab)
      have hmem : (φ ⟨k, hkK⟩) ⟨x, memA_of_A₂ hx⟩ ∈ A₂.subgroupOf A := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ hx'
      have hmemG : ((φ ⟨k, hkK⟩) ⟨x, memA_of_A₂ hx⟩ : G) ∈ A₂ :=
        Subgroup.mem_subgroupOf.mp hmem
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hmemG
      exact hmemG
    · intro hx
      have hk'inv : k⁻¹ ∈ K := Subgroup.inv_mem (H := K) hkK
      have hφkinvL : φ ⟨k⁻¹, hk'inv⟩ ∈ L :=
        MonoidHom.mem_range.mpr ⟨⟨k⁻¹, hk'inv⟩, rfl⟩
      have hφkinvstab : φ ⟨k⁻¹, hk'inv⟩ ∈ Stab₂ := hL_stab₂ hφkinvL
      have hx' : (⟨k * x * k⁻¹, memA_of_A₂ hx⟩ : A) ∈ A₂.subgroupOf A := hx
      have hmap := (MulAction.mem_stabilizer_iff.mp hφkinvstab)
      have hmem : (φ ⟨k⁻¹, hk'inv⟩) ⟨k * x * k⁻¹, memA_of_A₂ hx⟩ ∈ A₂.subgroupOf A := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ hx'
      have hmemG : ((φ ⟨k⁻¹, hk'inv⟩) ⟨k * x * k⁻¹, memA_of_A₂ hx⟩ : G) ∈ A₂ :=
        Subgroup.mem_subgroupOf.mp hmem
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hmemG
      simpa [mul_assoc] using hmemG
  ·
    have hA₁A₂bot : A₁ ⊓ A₂ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ 𝔖.S₁ ⊓ 𝔖.S₂ := ⟨hx.1.2, hx.2.2⟩
      rw [𝔖.decomp.inf_eq] at this
      exact this
    have htrans := exists_conj_eq_of_relIndex_eq_nine hA hQ_le_K hQ9
      (show A₁ ≤ A from inf_le_left) (show A₂ ≤ A from inf_le_left)
      hA₁card hA₂card hA₁A₂bot hQX hQY
    intro v hv w hw hv2 hw2 hvS₁ hvS₂ hwS₁ hwS₂
    have hvA₁ : v ∉ A₁ := fun h => hvS₁ h.2
    have hvA₂ : v ∉ A₂ := fun h => hvS₂ h.2
    have hwA₁ : w ∉ A₁ := fun h => hwS₁ h.2
    have hwA₂ : w ∉ A₂ := fun h => hwS₂ h.2
    obtain ⟨q, hqQ, hq⟩ := htrans v hv w hw hvA₁ hvA₂ hwA₁ hwA₂
    exact ⟨q, hQ_le_K hqQ, hq⟩

end Sec3Setting

end CFSG.GH72
