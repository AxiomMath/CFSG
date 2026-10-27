module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Defs
public import CFSG.GH74.GLS.IVK.L2.Lemma13
public import CFSG.GH74.GLS.IVK.L2.Hilbert90
public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.GH74.GLS.IVK.L2.FieldProj
public import CFSG.GH74.GLS.IVK.A7.Core

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.Outer

open Subgroup
open scoped MatrixGroups

section Transport

variable {G : Type} [Group G] {L : Subgroup G}

theorem conjNormal_sq [L.Normal] {t : G} (ht : t ^ 2 = 1) :
    (MulAut.conjNormal (H := L) t) ^ 2 = 1 := by
  rw [← map_pow, ht, map_one]

theorem conjNormal_not_inner [L.Normal] (hC : centralizer (L : Set G) = ⊥) {t : G}
    (htL : t ∉ L) :
    (MulAut.conjNormal (H := L) t) ∉ CFSG.GH74.GLS.IVK.innAut L := by
  rintro ⟨g, hg⟩
  apply htL
  have hmem : (g : G)⁻¹ * t ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    have h1 := congrArg (fun a : MulAut L => ((a ⟨l, hl⟩ : L) : G)) hg
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc l * ((g : G)⁻¹ * t) = (g : G)⁻¹ * (g * l * (g : G)⁻¹) * t := by group
      _ = (g : G)⁻¹ * (t * l * t⁻¹) * t := by rw [h1]
      _ = ((g : G)⁻¹ * t) * l := by group
  rw [hC, mem_bot] at hmem
  have : t = g := by
    calc t = (g : G) * ((g : G)⁻¹ * t) := by group
      _ = g := by rw [hmem, mul_one]
  rw [this]
  exact g.2

theorem card_fixed [L.Normal] (t : G) :
    Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup L (MulAut.conjNormal (H := L) t)) =
      Nat.card ↥(L ⊓ centralizer ({t} : Set G)) := by
  have h : (L ⊓ centralizer ({t} : Set G)).subgroupOf L =
      CFSG.GH74.GLS.fixedSubgroup L (MulAut.conjNormal (H := L) t) := by
    ext l
    simp only [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    refine ⟨fun ⟨_, h⟩ => ?_, fun h => ⟨l.2, ?_⟩⟩
    · show (MulAut.conjNormal t) l = l
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, ← h]
      group
    · have h1 : (MulAut.conjNormal t) l = l := h
      have h2 := congrArg Subtype.val h1
      rw [MulAut.conjNormal_apply] at h2
      calc (l : G) * t = (t * l * t⁻¹) * t := by rw [h2]
        _ = t * l := by group
  have h2 := Nat.card_congr
    (subgroupOfEquivOfLe (inf_le_left : L ⊓ centralizer ({t} : Set G) ≤ L)).toEquiv
  rw [h] at h2
  exact h2

end Transport

section L2

open CFSG.GH74.GLS.IVK

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

theorem mem_innDiagSub_of_card_ringAut (e : K ≃* L2 F) (h : Nat.card (F ≃+* F) = 1)
    (y : MulAut K) : y ∈ innDiagSub e := by
  rw [mem_innDiagSub_iff]
  have := (Nat.card_eq_one_iff_unique.1 h).1
  exact Subsingleton.elim _ _

theorem card_fixed_diag [Finite K] (hF : L2Field F) (e : K ≃* L2 F) {y : MulAut K}
    (hy2 : y ^ 2 = 1) (hyD : y ∈ innDiagSub e) (hyI : y ∉ innAut K) {ε : ℤ}
    (hε1 : ε = 1 ∨ ε = -1) (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) {d : ℕ}
    (hd : (d : ℤ) = Nat.card F + ε) :
    Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup K y) = d := by
  have hy1 : y ≠ 1 := fun h => hyI (h ▸ one_mem _)
  have hy2' : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  obtain ⟨k, hk, hk2, ⟨ψ⟩⟩ := (ivk_1_3b_dihedral hF e ε hε1 hε d hd y hyD hyI hy2').2
  haveI : NeZero k := ⟨by omega⟩
  rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
  omega

theorem card_fixed_conj {a y f : MulAut K} (h : a⁻¹ * y * a = f) :
    Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup K y) =
      Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup K f) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (a⁻¹ : MulAut K).toEquiv fun k => ?_)
  subst h
  show y k = k ↔ (a⁻¹ * y * a) (a⁻¹ k) = a⁻¹ k
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
  exact ⟨fun h => by rw [h], fun h => (a⁻¹ : MulAut K).injective h⟩

theorem card_fixed_not_diag (e : K ≃* L2 F) {y : MulAut K} (hy2 : y ^ 2 = 1)
    (hyD : y ∉ innDiagSub e) :
    ∃ q₀ : ℕ, q₀ ^ 2 = Nat.card F ∧
      Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup K y) = q₀ * (q₀ ^ 2 - 1) := by
  classical
  have hσ1 : fieldProj e y ≠ 1 := fun h => hyD ((mem_innDiagSub_iff e y).2 h)
  have hy1 : y ≠ 1 := fun h => hσ1 (by rw [h, map_one])
  have hy2' : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  have hord : orderOf (thetaAut e y) = 2 := by rw [MulEquiv.orderOf_eq]; exact hy2'
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr (thetaAut e y) hord hσ1
  have hay : (innDiagHom e C)⁻¹ * y * innDiagHom e C = fieldAutHom e (fieldProj e y) := by
    apply (thetaAut e).injective
    rw [map_mul, map_mul, map_inv, thetaAut_innDiagHom, thetaAut_fieldAutHom]
    exact hC
  have hσ2 : fieldProj e y ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  have hσo : orderOf (fieldProj e y) = 2 := orderOf_eq_prime hσ2 hσ1
  refine ⟨Nat.card (fixedField (fieldProj e y)), ?_, ?_⟩
  · have := fixedField_card_pow (fieldProj e y)
    rwa [hσo] at this
  · rw [card_fixed_conj hay]
    exact card_fixedSubgroup_of_even e (fieldProj e y) (by rw [hσo]; exact even_two)

end L2

section A7

open Equiv Equiv.Perm

variable {K : Type} [Group K]

theorem card_fixed_A7 (e : K ≃* alternatingGroup (Fin 7)) {y : MulAut K} (hy : y ^ 2 = 1)
    (hy1 : y ≠ 1) :
    Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup K y) = 24 ∨
      Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup K y) = 120 := by
  classical
  have hbij : Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)) :
      Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7))) :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)
  obtain ⟨σ, hσ⟩ := hbij.2 (MulAut.congr e y)
  have hy'2 : (MulAut.congr e y) ^ 2 = 1 := by rw [← map_pow, hy, map_one]
  have hσ2 : σ ^ 2 = 1 := by
    apply hbij.1
    rw [map_pow, hσ, hy'2, map_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hy1
    have h1 : MulAut.congr e y = 1 := by rw [← hσ, map_one]
    exact (MulAut.congr e).injective (h1.trans (map_one _).symm)
  let ψ : K →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom
  have hψinj : Function.Injective ψ := (Subgroup.subtype_injective _).comp e.injective
  have hψy : ∀ k : K, ψ (y k) = σ * ψ k * σ⁻¹ := by
    intro k
    have h1 : e (y k) = MulAut.congr e y (e k) := by simp [MulAut.congr_apply]
    show ((e (y k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      σ * ((e k : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ⁻¹
    rw [h1, ← hσ, MulAut.conjNormal_apply]
  have hmap : (CFSG.GH74.GLS.fixedSubgroup K y).map ψ =
      centralizer ({σ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : y k = k := hk
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, (e k).2⟩
      have := hψy k
      rw [hk'] at this
      calc ψ k * σ = σ * ψ k * σ⁻¹ * σ := by rw [← this]
        _ = σ * ψ k := by group
    · rintro ⟨hxc, hxA⟩
      refine ⟨e.symm ⟨x, hxA⟩, ?_, by simp [ψ]⟩
      show y (e.symm ⟨x, hxA⟩) = e.symm ⟨x, hxA⟩
      apply hψinj
      rw [hψy]
      have hx : σ * x = x * σ := (Subgroup.mem_centralizer_singleton_iff.1 hxc).symm
      have : ψ (e.symm ⟨x, hxA⟩) = x := by simp [ψ]
      rw [this]
      calc σ * x * σ⁻¹ = x * σ * σ⁻¹ := by rw [hx]
        _ = x := by group
  have hcard : Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup K y) =
      Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) :=
    (Subgroup.card_map_of_injective hψinj).symm.trans (by rw [hmap])
  rw [hcard]
  rcases CFSG.GH74.GLS.IVK.A7.involution_cycleType σ hσ2 hσ1 with h2 | h22 | h222
  · exact Or.inr (CFSG.GH74.GLS.IVK.A7.card_centralizer_A7_two h2 hσ2 hσ1)
  · exact Or.inl (CFSG.GH74.GLS.IVK.A7.card_centralizer_A7_two_two h22 hσ2 hσ1)
  · exact Or.inl (CFSG.GH74.GLS.IVK.A7.card_centralizer_A7_two_two_two h222 hσ2 hσ1)

end A7

section Assembly

open CFSG.GH74.GLS.IVK

variable {G : Type} [Group G] {L : Subgroup G}

theorem card_outer_diag [L.Normal] [Finite L] (hC : centralizer (L : Set G) = ⊥) {t : G}
    (ht : t ^ 2 = 1) (htL : t ∉ L) {F : Type} [Field F] [Finite F] (hF : L2Field F)
    (e : ↥L ≃* L2 F) (hD : MulAut.conjNormal (H := L) t ∈ innDiagSub e) {ε : ℤ}
    (hε1 : ε = 1 ∨ ε = -1) (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) {d : ℕ}
    (hd : (d : ℤ) = Nat.card F + ε) :
    Nat.card ↥(L ⊓ centralizer ({t} : Set G)) = d := by
  rw [← card_fixed]
  exact card_fixed_diag hF e (conjNormal_sq ht) hD (conjNormal_not_inner hC htL) hε1 hε hd

theorem pglTwoSquareOuter_of_diag [L.Normal] (hC : centralizer (L : Set G) = ⊥) {t : G}
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9) (e : ↥L ≃* L2 F)
    (hD : MulAut.conjNormal (H := L) t ∈ innDiagSub e)
    (hI : MulAut.conjNormal (H := L) t ∉ innAut L) : PGLTwoSquareOuter L t := by
  obtain ⟨B, hB⟩ := hD
  have hBout : B ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    fun h => hI (hB ▸ (innDiagHom_mem_innAut_iff e B).2 h)
  letI : Fintype F := Fintype.ofFinite F
  refine ⟨inferInstance, hC, F, inferInstance, inferInstance, 3, by decide, ?_, toPSL e, B,
    hBout, ?_⟩
  · rw [← Nat.card_eq_fintype_card, hF]
    norm_num
  · intro x z hz
    have h1 : z = MulAut.conjNormal t x := Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hz)
    rw [h1, ← hB]
    exact toPGL_toPSL_innDiagHom e B x

end Assembly

end CFSG.LocalAnalysis.EvenBN.Tits.I21.Outer

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open
open scoped MatrixGroups

section SectionSeven

open I21.Outer CFSG.GH74.GLS.IVK

theorem sec622_outer_L2_five {G : Type} [Group G] [Finite G] {L : Subgroup G} (hLn : L.Normal)
    (hC : centralizer (L : Set G) = ⊥) (hL : IsPSLTwo L 5) {t : G} (ht : t ^ 2 = 1)
    (htL : t ∉ L) : Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 6 := by
  haveI := hLn
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  let e2 : ↥L ≃* L2 F := e.trans (L2.equivPSL F).symm
  have hF' : L2Field F := ⟨by rw [hF]; decide, by rw [hF]; decide⟩
  have hring : Nat.card (F ≃+* F) = 1 := card_ringAut F 5 1 (by norm_num) (by simpa using hF)
  exact card_outer_diag hC ht htL hF' e2 (mem_innDiagSub_of_card_ringAut e2 hring _)
    (ε := 1) (Or.inl rfl) (by rw [hF]; decide) (d := 6) (by rw [hF]; norm_num)

theorem sec622_outer_L2_seven {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hLn : L.Normal) (hC : centralizer (L : Set G) = ⊥) (hL : IsPSLTwo L 7) {t : G}
    (ht : t ^ 2 = 1) (htL : t ∉ L) :
    Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 6 := by
  haveI := hLn
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  let e2 : ↥L ≃* L2 F := e.trans (L2.equivPSL F).symm
  have hF' : L2Field F := ⟨by rw [hF]; decide, by rw [hF]; decide⟩
  have hring : Nat.card (F ≃+* F) = 1 := card_ringAut F 7 1 (by norm_num) (by simpa using hF)
  exact card_outer_diag hC ht htL hF' e2 (mem_innDiagSub_of_card_ringAut e2 hring _)
    (ε := -1) (Or.inr rfl) (by rw [hF]; decide) (d := 6) (by rw [hF]; norm_num)

theorem sec622_outer_L2_nine {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hLn : L.Normal) (hC : centralizer (L : Set G) = ⊥) (hL : IsPSLTwo L 9) {t : G}
    (ht : t ^ 2 = 1) (htL : t ∉ L) :
    (Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 10 ∧ PGLTwoSquareOuter L t) ∨
      Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 24 := by
  haveI := hLn
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  let e2 : ↥L ≃* L2 F := e.trans (L2.equivPSL F).symm
  have hF' : L2Field F := ⟨by rw [hF]; decide, by rw [hF]; decide⟩
  by_cases hD : MulAut.conjNormal (H := L) t ∈ innDiagSub e2
  · left
    exact ⟨card_outer_diag hC ht htL hF' e2 hD (ε := 1) (Or.inl rfl) (by rw [hF]; decide)
      (d := 10) (by rw [hF]; norm_num),
      pglTwoSquareOuter_of_diag hC hF e2 hD (conjNormal_not_inner hC htL)⟩
  · right
    obtain ⟨q₀, hq₀, hcard⟩ := card_fixed_not_diag e2 (conjNormal_sq ht) hD
    have h3 : q₀ = 3 := by
      have h : q₀ ^ 2 = 3 ^ 2 := by rw [hq₀, hF]; norm_num
      exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h
    rw [← card_fixed, hcard, h3]
    norm_num

theorem sec622_outer_A7 {G : Type} [Group G] [Finite G] {L : Subgroup G} (hLn : L.Normal)
    (hC : centralizer (L : Set G) = ⊥) (hL : Nonempty (L ≃* alternatingGroup (Fin 7)))
    {t : G} (ht : t ^ 2 = 1) (htL : t ∉ L) :
    Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 24 ∨
      Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 120 := by
  haveI := hLn
  obtain ⟨e⟩ := hL
  have hy1 : MulAut.conjNormal (H := L) t ≠ 1 := fun h =>
    conjNormal_not_inner hC htL (h ▸ one_mem _)
  rw [← card_fixed]
  exact card_fixed_A7 e (conjNormal_sq ht) hy1

end SectionSeven

end CFSG.LocalAnalysis.EvenBN.Tits
