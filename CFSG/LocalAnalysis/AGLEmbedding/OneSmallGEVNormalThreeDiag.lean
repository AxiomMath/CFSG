module

public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtBlocks
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

omit [Finite G] in
theorem barM_self_eq_top (M : Subgroup G) : barM M M = ⊤ := by
  rw [barM, Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

namespace D1MSideAt

variable {S : Subgroup G}

theorem mem_normalizer_of_fixed (h : D1MSideAt M S) (hp : p.Prime)
    (hp2 : p ≠ 2) {z : G} (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z))
    (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (S : Set G)) {d : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hd : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ * d *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩)⁻¹ = d) :
    d ∈ Subgroup.normalizer (barM M (S) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hdM : d ∈ barM M M := by rw [barM_self_eq_top]; exact Subgroup.mem_top d
  have h1 := fixed_le_barM_normalizer_inf_of_twoCore_le h.twoCore_M_le hp hp2 hzM hz hCz (L := M) d hdM hd
  exact barM_le_normalizer_barM (inf_le_left :
    Subgroup.normalizer (S : Set G) ⊓ M ≤ Subgroup.normalizer (S : Set G)) h1

theorem not_mem_centralizer_block (h : D1MSideAt M S) (hp : p.Prime)
    (hp2 : p ≠ 2) {z : G} (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z))
    (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (S : Set G)) {L : Subgroup G}
    (hL : IsWeakSBlock M (S) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  intro hc
  apply h.barM_ne_of_isWeakSBlock hL
  refine le_antisymm (barM_mono inf_le_right) fun l hl =>
    fixed_le_barM_normalizer_inf_of_twoCore_le h.twoCore_M_le hp hp2 hzM hz hCz l hl ?_
  rw [← Subgroup.mem_centralizer_iff.mp hc l hl, mul_inv_cancel_right]

theorem mem_normalizer_block_of_cube_of_inner (h : D1MSideAt M S) (hp : p.Prime)
    (hp2 : p ≠ 2) (h86 : Asc81bEightSix) {z : G}
    (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z)) (hz3 : z ^ 3 = 1)
    (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (S : Set G)) {L : Subgroup G}
    (hL : IsWeakSBlock M (S) L)
    (hinner : ∀ l ∈ barM M L,
      (∀ s ∈ barM M S, ∃ s' ∈ barM M S, ∀ y ∈ barM M L,
        (l * s * l⁻¹) * y * (l * s * l⁻¹)⁻¹ = s' * y * s'⁻¹) →
      l ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L)) :
    z ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hzL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set zb := mk ⟨z, hzM⟩ with hzb
  have hzS : z ∈ Subgroup.normalizer (S : Set G) :=
    hCz ⟨hzM, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hz3' : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hinj := injective_conj_pow_of_not_mem_normalizer hz3' hzL
  set Lj : Fin 3 → Subgroup G := fun j => L.map (MulAut.conj (z ^ (j : ℕ))).toMonoidHom
    with hLjdef
  have hLj : ∀ j, IsWeakSBlock M S (Lj j) := fun j =>
    hL.map_conj (M.pow_mem hzM _) (Subgroup.pow_mem _ hzS _)
  have hzbj : ∀ k : ℕ, mk ⟨z ^ k, M.pow_mem hzM k⟩ = zb ^ k := fun k => by
    rw [hzb, ← map_pow]; rfl
  have hbar : ∀ j : Fin 3, barM M (Lj j) =
      (barM M L).map (MulAut.conj (zb ^ (j : ℕ))).toMonoidHom := fun j => by
    rw [barM_map_conj (M.pow_mem hzM _), hzbj]
  have hne : ∀ i j : Fin 3, i ≠ j → barM M (Lj i) ≠ barM M (Lj j) := fun i j hij he =>
    hij (hinj ((hLj i).toIsTwoPrimeComponent.eq_of_barM_eq (hLj j).toIsTwoPrimeComponent he))
  have hcomm : ∀ i j : Fin 3, i ≠ j → ∀ a ∈ barM M (Lj i), ∀ b ∈ barM M (Lj j),
      a * b = b * a := fun i j hij a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (le_centralizer_of_component_ne (hLj j).component
      (hLj i).component (hne j i (Ne.symm hij)) hb) a ha
  have hL0 : barM M (Lj 0) = barM M L := by
    rw [hbar]
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hy
      exact ⟨y, hy, by simp⟩
  have hmemj : ∀ (j : Fin 3) (x : ↥M ⧸ CFSG.pCore 2 ↥M), x ∈ barM M L →
      zb ^ (j : ℕ) * x * (zb ^ (j : ℕ))⁻¹ ∈ barM M (Lj j) := fun j x hx => by
    rw [hbar]; exact ⟨x, hx, rfl⟩
  have hzb3 : zb ^ 3 = 1 := by
    rw [← hzbj 3]
    have h1 : (⟨z ^ 3, M.pow_mem hzM 3⟩ : M) = 1 := Subtype.ext hz3
    rw [h1, map_one]
  have key : ∀ x ∈ barM M L, x ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
    intro x hx
    set x₂ := zb ^ ((1 : Fin 3) : ℕ) * x * (zb ^ ((1 : Fin 3) : ℕ))⁻¹ with hx₂
    set x₃ := zb ^ ((2 : Fin 3) : ℕ) * x * (zb ^ ((2 : Fin 3) : ℕ))⁻¹ with hx₃
    have hx₂L := hmemj 1 x hx
    have hx₃L := hmemj 2 x hx
    have hxL0 : x ∈ barM M (Lj 0) := hL0 ▸ hx
    have hc12 : x * x₂ = x₂ * x := hcomm 0 1 (by decide) x hxL0 x₂ hx₂L
    have hc13 : x * x₃ = x₃ * x := hcomm 0 2 (by decide) x hxL0 x₃ hx₃L
    have hfix : zb * (x * (x₂ * x₃)) * zb⁻¹ = x * (x₂ * x₃) := by
      have e1 : zb * x * zb⁻¹ = x₂ := by simp [hx₂]
      have e2 : zb * x₂ * zb⁻¹ = x₃ := by simp [hx₂, hx₃, pow_two, mul_assoc]
      have e3 : zb * x₃ * zb⁻¹ = x := by
        have : zb * x₃ * zb⁻¹ = zb ^ 3 * x * (zb ^ 3)⁻¹ := by
          simp [hx₃, pow_succ, mul_assoc]
        rw [this, hzb3]; group
      calc zb * (x * (x₂ * x₃)) * zb⁻¹
          = (zb * x * zb⁻¹) * ((zb * x₂ * zb⁻¹) * (zb * x₃ * zb⁻¹)) := by group
        _ = x₂ * (x₃ * x) := by rw [e1, e2, e3]
        _ = x * (x₂ * x₃) := by rw [← hc13, ← mul_assoc, ← hc12, mul_assoc]
    have hdN := h.mem_normalizer_of_fixed hp hp2 hzM hz hCz hfix
    refine hinner x hx fun s hs => ?_
    set e := x₂ * x₃ with he
    set d := x * e with hd
    refine ⟨d * s * d⁻¹, (Subgroup.mem_normalizer_iff.mp hdN s).mp hs, fun y hy => ?_⟩
    have hsL : s ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      h86 G M S h.isKGroup h.hyp _ hL.component hs
    have heC : ∀ w ∈ barM M L, e * w = w * e := by
      intro w hw
      have hw0 : w ∈ barM M (Lj 0) := hL0 ▸ hw
      have h2 : x₂ * w = w * x₂ := (hcomm 0 1 (by decide) w hw0 x₂ hx₂L).symm
      have h3 : x₃ * w = w * x₃ := (hcomm 0 2 (by decide) w hw0 x₃ hx₃L).symm
      rw [he, mul_assoc, h3, ← mul_assoc, h2, mul_assoc]
    have hy' : x⁻¹ * y * x ∈ barM M L := by
      have := (barM M L).mul_mem ((barM M L).mul_mem ((barM M L).inv_mem hx) hy) hx
      simpa [mul_assoc] using this
    have hw : s * (x⁻¹ * y * x) * s⁻¹ ∈ barM M L := (Subgroup.mem_normalizer_iff.mp hsL _).mp hy'
    have h1 : e⁻¹ * (x⁻¹ * y * x) * e = x⁻¹ * y * x := by
      rw [mul_assoc, ← heC _ hy']; group
    calc x * s * x⁻¹ * y * (x * s * x⁻¹)⁻¹ = x * (s * (x⁻¹ * y * x) * s⁻¹) * x⁻¹ := by group
      _ = x * ((s * (x⁻¹ * y * x) * s⁻¹) * e) * e⁻¹ * x⁻¹ := by group
      _ = x * (e * (s * (x⁻¹ * y * x) * s⁻¹)) * e⁻¹ * x⁻¹ := by rw [heC _ hw]
      _ = x * e * s * (e⁻¹ * (x⁻¹ * y * x) * e) * s⁻¹ * e⁻¹ * x⁻¹ := by rw [h1]; group
      _ = d * s * d⁻¹ * y * (d * s * d⁻¹)⁻¹ := by rw [hd]; group
  exact h.barM_ne_of_isWeakSBlock hL (le_antisymm (barM_mono inf_le_right) key)

end D1MSideAt

theorem D1PhaseThree.not_mem_centralizer_block (h : D1PhaseThree p P M H R) (hp : p.Prime)
    (hp2 : p ≠ 2) {z : G} (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z))
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  h.toMSideAt.not_mem_centralizer_block hp hp2 hzM hz
    (fun _ hx => localGroup_le_normalizer_pCoreOf 2 H (hCz hx.2)) hL

theorem D1PhaseThree.mem_normalizer_block_of_cube (h : D1PhaseThree p P M H R) (hp : p.Prime)
    (hp2 : p ≠ 2) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) {z : G}
    (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z)) (hz3 : z ^ 3 = 1)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : z ∈ Subgroup.normalizer (L : Set G) :=
  h.toMSideAt.mem_normalizer_block_of_cube_of_inner hp hp2 h86 hzM hz hz3
    (fun _ hx => localGroup_le_normalizer_pCoreOf 2 H (hCz hx.2)) hL
    (stmtBlockInnerNormalizer_of h h84 h86 hD2 hL)

end CFSG.AGLEmbedding
