module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Main1

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup
open scoped Classical

namespace AutHyp

variable {Y : Type*} [Group Y] {S J : Subgroup (MulAut Y)} (A : AutHyp Y S J)
include A

theorem conj_mem_J {s : MulAut Y} (hs : s ∈ S) {a : MulAut Y} (ha : a ∈ J) :
    s * a * s⁻¹ ∈ J := by
  have hK : J.map (MulAut.conj s).toMonoidHom = J := by
    refine A.J_unique _ ?_ ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact S.mul_mem (S.mul_mem hs (A.J_le hx)) (S.inv_mem hs)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc s * x * s⁻¹ * (s * y * s⁻¹) = s * (x * y) * s⁻¹ := by group
        _ = s * (y * x) * s⁻¹ := by rw [A.J_comm x hx y hy]
        _ = s * y * s⁻¹ * (s * x * s⁻¹) := by group
    · rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc s * x * s⁻¹ * (s * x * s⁻¹) = s * (x * x) * s⁻¹ := by group
        _ = 1 := by rw [A.J_sq x hx]; group
    · rw [← Nat.card_congr (Subgroup.equivMapOfInjective J (MulAut.conj s).toMonoidHom
        (MulAut.conj s).injective).toEquiv, A.card_J]
  have : s * a * s⁻¹ ∈ J.map (MulAut.conj s).toMonoidHom := ⟨a, ha, by simp [MulAut.conj_apply]⟩
  rwa [hK] at this

theorem S_le_normalizer : S ≤ normalizer (J : Set (MulAut Y)) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => A.conj_mem_J hs ha, fun ha => ?_⟩
  have := A.conj_mem_J (S.inv_mem hs) ha
  rwa [show s⁻¹ * (s * a * s⁻¹) * s⁻¹⁻¹ = a by group] at this

end AutHyp

namespace MainCtx

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {Y : Type} [Group Y]
  {S J : Subgroup (MulAut Y)} (C : MainCtx G L t Y S J)
include C

theorem pi_tH : C.π tH = 1 := C.hπ.pi_t

theorem t_sq : t * t = 1 := by
  simpa using congrArg Subtype.val C.hπ.t_sq

theorem t_ne : t ≠ 1 := fun h => C.hπ.t_ne (Subtype.ext h)

theorem mem_pre_coe {B : Subgroup (MulAut Y)} (h : ↥(centralizer ({t} : Set G))) :
    (h : G) ∈ C.pre B ↔ C.π h ∈ B := by
  rw [mem_pre]
  refine ⟨fun ⟨h', hB, hh⟩ => ?_, fun hB => ⟨h, hB, rfl⟩⟩
  have : h' = h := Subtype.ext hh
  rwa [this] at hB

theorem pre_mono {B B' : Subgroup (MulAut Y)} (h : B ≤ B') : C.pre B ≤ C.pre B' := by
  intro x hx
  obtain ⟨h', hB, rfl⟩ := C.mem_pre.1 hx
  exact (C.mem_pre_coe h').2 (h hB)

theorem card_pre [Finite G] (B : Subgroup (MulAut Y)) :
    Nat.card (C.pre B) = 2 * Nat.card B := by
  rw [← C.hπ.card_comap B]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ (centralizer ({t} : Set G)).subtype
    (centralizer ({t} : Set G)).subtype_injective).toEquiv).symm

theorem t_mem_pre {B : Subgroup (MulAut Y)} : t ∈ C.pre B :=
  (C.mem_pre_coe (B := B) tH).2 (by rw [C.pi_tH]; exact B.one_mem)

theorem E_sq {x : G} (hx : x ∈ C.pre J) : x * x = 1 := by
  obtain ⟨h, hJ, rfl⟩ := C.mem_pre.1 hx
  simpa using congrArg Subtype.val (C.hπ.sq_of_mem_J C.A hJ)

theorem E_comm {x y : G} (hx : x ∈ C.pre J) (hy : y ∈ C.pre J) : x * y = y * x := by
  obtain ⟨h, hJ, rfl⟩ := C.mem_pre.1 hx
  obtain ⟨h', hJ', rfl⟩ := C.mem_pre.1 hy
  simpa using congrArg Subtype.val (C.hπ.comm_of_mem_J C.A hJ hJ')

theorem card_E [Finite G] : Nat.card (C.pre J) = 64 := by
  rw [C.card_pre, C.A.card_J]

omit C in
theorem conj_mem_H_iff (h : ↥(centralizer ({t} : Set G))) (x : G) :
    (h : G) * x * (h : G)⁻¹ ∈ centralizer ({t} : Set G) ↔ x ∈ centralizer ({t} : Set G) := by
  constructor
  · intro hx
    have := (centralizer ({t} : Set G)).mul_mem
      ((centralizer ({t} : Set G)).mul_mem ((centralizer ({t} : Set G)).inv_mem h.2) hx) h.2
    rwa [show (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * (h : G) = x by group] at this
  · intro hx
    exact (centralizer ({t} : Set G)).mul_mem
      ((centralizer ({t} : Set G)).mul_mem h.2 hx) ((centralizer ({t} : Set G)).inv_mem h.2)

theorem coe_mem_normalizer_iff (h : ↥(centralizer ({t} : Set G))) :
    (h : G) ∈ normalizer ((C.pre J : Subgroup G) : Set G) ↔
      C.π h ∈ normalizer (J : Set (MulAut Y)) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hn a
    obtain ⟨x, rfl⟩ := C.hπ.surj a
    have h1 := hn (x : G)
    have e : (h : G) * (x : G) * (h : G)⁻¹ =
        ((h * x * h⁻¹ : ↥(centralizer ({t} : Set G))) : G) := rfl
    rw [e, C.mem_pre_coe, C.mem_pre_coe] at h1
    simpa [map_mul, map_inv] using h1
  · intro hn x
    by_cases hx : x ∈ centralizer ({t} : Set G)
    · lift x to ↥(centralizer ({t} : Set G)) using hx
      have e : (h : G) * (x : G) * (h : G)⁻¹ =
          ((h * x * h⁻¹ : ↥(centralizer ({t} : Set G))) : G) := rfl
      rw [e, C.mem_pre_coe, C.mem_pre_coe]
      simpa [map_mul, map_inv] using hn (C.π x)
    · have h1 : x ∉ C.pre J := fun hx' => hx (C.pre_le_H J hx')
      have h2 : (h : G) * x * (h : G)⁻¹ ∉ C.pre J := fun hx' =>
        hx ((MainCtx.conj_mem_H_iff h x).1 (C.pre_le_H J hx'))
      exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩

theorem normalizer_inf_H :
    normalizer ((C.pre J : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) =
      C.pre (normalizer (J : Set (MulAut Y))) := by
  ext x
  constructor
  · rintro ⟨hxN, hxH⟩
    exact (C.mem_pre_coe (B := normalizer (J : Set (MulAut Y))) ⟨x, hxH⟩).2
      ((C.coe_mem_normalizer_iff ⟨x, hxH⟩).1 hxN)
  · intro hx
    obtain ⟨h, hh, rfl⟩ := C.mem_pre.1 hx
    exact ⟨(C.coe_mem_normalizer_iff h).2 hh, h.2⟩

theorem card_N0 [Finite G] :
    Nat.card ↥(normalizer ((C.pre J : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G)) = 7680 := by
  rw [C.normalizer_inf_H, C.card_pre, C.A.data.card_normalizer]

theorem pre_S_le_normalizer : C.pre S ≤ normalizer ((C.pre J : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨h, hS, rfl⟩ := C.mem_pre.1 hx
  exact (C.coe_mem_normalizer_iff h).2 (C.A.S_le_normalizer hS)

theorem E_le_pre_S : C.pre J ≤ C.pre S := C.pre_mono C.A.J_le

theorem E_cent {n : G} (hc : ∀ x ∈ C.pre J, n * x = x * n) : n ∈ C.pre J := by
  have hnH : n ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hc t C.t_mem_pre)
  lift n to ↥(centralizer ({t} : Set G)) using hnH
  rw [C.mem_pre_coe]
  refine C.A.data.centralizer_le _ fun a ha => ?_
  obtain ⟨x, rfl⟩ := C.hπ.surj a
  have h2 : n * x = x * n := Subtype.ext (hc _ ((C.mem_pre_coe x).2 ha))
  rw [← map_mul, ← map_mul, h2]

variable [Fintype G]

theorem mem_pset_coe (B : Set (MulAut Y)) (h : ↥(centralizer ({t} : Set G))) :
    (h : G) ∈ C.pset B ↔ C.π h ∈ B := by
  rw [mem_pset]
  refine ⟨fun ⟨h', hh', hB⟩ => ?_, fun hB => ⟨h, rfl, hB⟩⟩
  have : h' = h := Subtype.ext hh'
  rwa [this] at hB

theorem disjoint_pset {B B' : Set (MulAut Y)} (hd : Disjoint B B') :
    Disjoint (C.pset B) (C.pset B') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨h, rfl, hB⟩ := C.mem_pset.1 hx
  exact Set.disjoint_left.1 hd hB ((C.mem_pset_coe B' h).1 hx')

theorem tmul_pset (B : Set (MulAut Y)) {x : G} (hx : x ∈ C.pset B) : t * x ∈ C.pset B := by
  obtain ⟨h, rfl, hB⟩ := C.mem_pset.1 hx
  exact (C.mem_pset_coe B (tH * h)).2 (by rw [map_mul, C.pi_tH, one_mul]; exact hB)

theorem trans_pset {B : Set (MulAut Y)}
    (hB : ∀ x ∈ B, ∀ y ∈ B, ∃ d ∈ normalizer (J : Set (MulAut Y)), d * x * d⁻¹ = y) :
    ∀ x ∈ C.pset B, ∀ y ∈ C.pset B, ∃ n ∈ normalizer ((C.pre J : Subgroup G) : Set G),
      n * t = t * n ∧ (n * x * n⁻¹ = y ∨ n * x * n⁻¹ = t * y) := by
  intro x hx y hy
  obtain ⟨hx', rfl, hxB⟩ := C.mem_pset.1 hx
  obtain ⟨hy', rfl, hyB⟩ := C.mem_pset.1 hy
  obtain ⟨d, hd, hdxy⟩ := hB _ hxB _ hyB
  obtain ⟨n₀, rfl⟩ := C.hπ.surj d
  refine ⟨(n₀ : G), (C.coe_mem_normalizer_iff n₀).2 hd,
    Subgroup.mem_centralizer_singleton_iff.1 n₀.2, ?_⟩
  have hπ : C.π (n₀ * hx' * n₀⁻¹) = C.π hy' := by
    rw [map_mul, map_mul, map_inv]; exact hdxy
  rcases C.hπ.eq_or_eq_mul_t hπ with h3 | h3
  · exact Or.inl (congrArg Subtype.val h3)
  · right
    have h4 : (n₀ : G) * hx' * (n₀ : G)⁻¹ = hy' * t := congrArg Subtype.val h3
    rw [h4]
    exact Subgroup.mem_centralizer_singleton_iff.1 hy'.2

theorem fix_pset {R : Set (MulAut Y)}
    (hR : ∀ α : MulAut Y, (∀ x ∈ R, α * x = x * α) → α ∈ J) {n : G} (hnt : n * t = t * n)
    (hfix : ∀ x ∈ C.pset R, n * x * n⁻¹ = x) : n ∈ C.pre J := by
  have hnH : n ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hnt
  lift n to ↥(centralizer ({t} : Set G)) using hnH
  rw [C.mem_pre_coe]
  refine hR _ fun a ha => ?_
  obtain ⟨x, rfl⟩ := C.hπ.surj a
  have h1 := hfix _ ((C.mem_pset_coe R x).2 ha)
  have h2 : n * x = x * n := by
    apply Subtype.ext
    calc (n : G) * x = ((n : G) * x * (n : G)⁻¹) * n := by group
      _ = x * n := by rw [h1]
  rw [← map_mul, ← map_mul, h2]

end MainCtx

end CFSG.EvenSporadicStandard.M22Std
