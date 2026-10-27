module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeNodeChart
public import CFSG.ClassicalInvolution.RouteD.TypeCChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock planeTorus longInv suppGroup coords
  shortBlock planeTorusElt IsAdaptedShortIn transvOne)
open CFSG.ClassicalInvolution.RouteD.LeviModel
open CFSG.ClassicalInvolution.WeakCT (torusHom diagTorus2 mem_diagTorus2_iff torusHom_injective)
open scoped MatrixGroups

section Torus

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem Frame.Tf_mul_comm (Fr : Frame p f m Ω K z) {i j : Fin (m + 1)} {x y : G}
    (hx : x ∈ Fr.Tf i) (hy : y ∈ Fr.Tf j) : x * y = y * x := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨s, rfl⟩ := mem_diagTorus2_iff.mp hA
    obtain ⟨t, rfl⟩ := mem_diagTorus2_iff.mp hB
    have : torusHom (GaloisField p f) s * torusHom (GaloisField p f) t =
        torusHom (GaloisField p f) t * torusHom (GaloisField p f) s := by
      rw [← map_mul, ← map_mul, mul_comm]
    calc Fr.ι i (torusHom (GaloisField p f) s) * Fr.ι i (torusHom (GaloisField p f) t)
        = Fr.ι i (torusHom (GaloisField p f) s * torusHom (GaloisField p f) t) :=
          (map_mul _ _ _).symm
      _ = Fr.ι i (torusHom (GaloisField p f) t * torusHom (GaloisField p f) s) := by rw [this]
      _ = Fr.ι i (torusHom (GaloisField p f) t) * Fr.ι i (torusHom (GaloisField p f) s) :=
          map_mul _ _ _
  · exact Fr.commute i j hij x (Frame.Tf_le i hx) y (Frame.Tf_le j hy)

end Torus

private theorem unit_mul_self_ne_one {F : Type} [Field F] {a : Fˣ}
    (ha : (a : F) ≠ ((a⁻¹ : Fˣ) : F)) : a * a ≠ 1 := by
  intro h
  exact ha (by rw [inv_eq_of_mul_eq_one_right h])

section Params

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

structure LeviParams (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z) where
  LF₂ : LocalFrameI Fr 2
  LF₀ : LocalFrameI Fr 0
  a : (GaloisField p f)ˣ
  b : (GaloisField p f)ˣ
  ha : (a : GaloisField p f) ≠ ((a⁻¹ : (GaloisField p f)ˣ) : GaloisField p f)
  hb : (b : GaloisField p f) ≠ ((b⁻¹ : (GaloisField p f)ˣ) : GaloisField p f)
  common : LF₂.layerSp S (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a)) =
    LF₀.layerSp S (longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) b))

namespace LeviParams

variable {S : CSetupW p f 2 Ω K z} {Fr : Frame p f 2 Ω K z} (P : LeviParams S Fr)

@[expose] noncomputable def ψ₂ : StatedSp 2 (GaloisField p f) →* G := P.LF₂.layerSp S

@[expose] noncomputable def ψ₀ : StatedSp 2 (GaloisField p f) →* G := P.LF₀.layerSp S

@[expose] noncomputable def x₀ : G := P.ψ₂ (longBlock (GaloisField p f) 2 0
  (torusHom (GaloisField p f) P.a))

@[expose] noncomputable def x₁ : G := P.ψ₂ (longBlock (GaloisField p f) 2 1
  (torusHom (GaloisField p f) P.a))

@[expose] noncomputable def x₂ : G := P.ψ₀ (longBlock (GaloisField p f) 2 1
  (torusHom (GaloisField p f) P.b))

@[expose] noncomputable def T₀ : Subgroup G := leviNode (Mf Fr 0 1) (P.x₀ * P.x₁)

@[expose] noncomputable def T₁ : Subgroup G := leviNode (Mf Fr 1 2) (P.x₁ * P.x₂)

theorem ψ₂_injective : Function.Injective P.ψ₂ := P.LF₂.layerSp_injective S

theorem ψ₀_injective : Function.Injective P.ψ₀ := P.LF₀.layerSp_injective S

theorem ψ₂_range : P.ψ₂.range = Mf Fr 0 1 := P.LF₂.layerSp_range S

theorem ψ₀_range : P.ψ₀.range = Mf Fr 1 2 := P.LF₀.layerSp_range S

theorem ψ₂_longInv (c : Fin 2) :
    P.ψ₂ (longInv (GaloisField p f) 2 c) = Fr.zf ((2 : Fin 3).succAbove c) :=
  P.LF₂.layerSp_longInv S c

theorem ψ₀_longInv (c : Fin 2) :
    P.ψ₀ (longInv (GaloisField p f) 2 c) = Fr.zf ((0 : Fin 3).succAbove c) :=
  P.LF₀.layerSp_longInv S c

theorem ψ₂_torus (c : Fin 2) (s : (GaloisField p f)ˣ) :
    P.ψ₂ (longBlock (GaloisField p f) 2 c (torusHom (GaloisField p f) s)) ∈
      Fr.Tf ((2 : Fin 3).succAbove c) := by
  have h : P.ψ₂ (longBlock (GaloisField p f) 2 c (torusHom (GaloisField p f) s)) ∈
      (planeTorus (GaloisField p f) 2 c).map P.ψ₂ :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map.mpr ⟨_, ⟨s, rfl⟩, rfl⟩)
  rwa [LeviParams.ψ₂, P.LF₂.map_layerSp_planeTorus S c] at h

theorem ψ₀_torus (c : Fin 2) (s : (GaloisField p f)ˣ) :
    P.ψ₀ (longBlock (GaloisField p f) 2 c (torusHom (GaloisField p f) s)) ∈
      Fr.Tf ((0 : Fin 3).succAbove c) := by
  have h : P.ψ₀ (longBlock (GaloisField p f) 2 c (torusHom (GaloisField p f) s)) ∈
      (planeTorus (GaloisField p f) 2 c).map P.ψ₀ :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map.mpr ⟨_, ⟨s, rfl⟩, rfl⟩)
  rwa [LeviParams.ψ₀, P.LF₀.map_layerSp_planeTorus S c] at h

theorem x₀_mem : P.x₀ ∈ Fr.Tf 0 := P.ψ₂_torus 0 P.a

theorem x₁_mem : P.x₁ ∈ Fr.Tf 1 := P.ψ₂_torus 1 P.a

theorem x₂_mem : P.x₂ ∈ Fr.Tf 2 := P.ψ₀_torus 1 P.b

theorem hn01 : ¬ Mf Fr 0 1 ≤ Subgroup.centralizer ({P.x₀ * P.x₁} : Set G) :=
  P.LF₂.not_le_centralizer_levi S P.ha

theorem hz01 : ¬ (Mf Fr 0 1 ⊓ Subgroup.centralizer ({P.x₀ * P.x₁} : Set G) ≤
    Subgroup.centralizer ({Fr.zf 0} : Set G)) :=
  P.LF₂.not_inf_le_centralizer_levi S P.a

theorem hn12 : ¬ Mf Fr 1 2 ≤ Subgroup.centralizer ({P.x₁ * P.x₂} : Set G) := by
  have h := P.LF₀.not_le_centralizer_levi S P.hb
  rw [← P.common] at h
  exact h

theorem hz12 : ¬ (Mf Fr 1 2 ⊓ Subgroup.centralizer ({P.x₁ * P.x₂} : Set G) ≤
    Subgroup.centralizer ({Fr.zf 1} : Set G)) := by
  have h := P.LF₀.not_inf_le_centralizer_levi S P.b
  rw [← P.common] at h
  exact h

theorem T₀_eq : P.T₀ = (shortBlock (GaloisField p f) fin_two_zero_ne_one).range.map P.ψ₂ :=
  P.LF₂.leviNode_layerSp S P.ha

theorem T₁_eq : P.T₁ = (shortBlock (GaloisField p f) fin_two_zero_ne_one).range.map P.ψ₀ := by
  have h := P.LF₀.leviNode_layerSp S P.hb
  rw [← P.common] at h
  exact h

theorem T₀_le : P.T₀ ≤ Mf Fr 0 1 := leviNode_le _ _

theorem T₁_le : P.T₁ ≤ Mf Fr 1 2 := leviNode_le _ _

theorem isAdaptedShortIn₀ :
    IsAdaptedShortIn (Mf Fr 0 1) (Fr.Tf 0) (Fr.Tf 1) (Fr.zf 0) P.T₀ :=
  ⟨P.x₀, P.x₀_mem, P.x₁, P.x₁_mem, P.hn01, P.hz01, rfl⟩

theorem isAdaptedShortIn₁ :
    IsAdaptedShortIn (Mf Fr 1 2) (Fr.Tf 1) (Fr.Tf 2) (Fr.zf 1) P.T₁ :=
  ⟨P.x₁, P.x₁_mem, P.x₂, P.x₂_mem, P.hn12, P.hz12, rfl⟩

theorem isShortNode₀ : IsShortNodeAt Fr 0 1 P.T₀ := ⟨P.T₀_le, P.isAdaptedShortIn₀⟩

theorem isShortNode₁ : IsShortNodeAt Fr 1 2 P.T₁ := ⟨P.T₁_le, P.isAdaptedShortIn₁⟩

end LeviParams

theorem exists_leviParams (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z) :
    Nonempty (LeviParams S Fr) := by
  obtain ⟨LF₂⟩ := exists_localFrameIW S Fr 2
  obtain ⟨LF₀⟩ := exists_localFrameIW S Fr 0
  obtain ⟨a, ha⟩ := S.hex
  have hmem : LF₂.layerSp S (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a)) ∈
      (planeTorus (GaloisField p f) 2 0).map (LF₀.layerSp S) := by
    rw [LF₀.map_layerSp_planeTorus S 0]
    have h : LF₂.layerSp S (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a)) ∈
        (planeTorus (GaloisField p f) 2 1).map (LF₂.layerSp S) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map.mpr ⟨_, ⟨a, rfl⟩, rfl⟩)
    rw [LF₂.map_layerSp_planeTorus S 1] at h
    exact h
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨b, rfl⟩ := mem_diagTorus2_iff.mp hA
  refine ⟨⟨LF₂, LF₀, a, b, ha, ?_, hux.symm⟩⟩
  intro hb
  have hbb : b * b = 1 := by
    have : b = b⁻¹ := Units.ext hb
    rw [mul_eq_one_iff_eq_inv]
    exact this
  have h1 : LF₂.layerSp S (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) (a * a))) =
      1 := by
    have e1 : longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) (a * a)) =
        longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a) *
          longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a) := by
      rw [map_mul, map_mul]
    have e2 : longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) (b * b)) =
        longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) b) *
          longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) b) := by
      rw [map_mul, map_mul]
    rw [e1, map_mul, ← hux, ← map_mul, ← e2, hbb]
    simp
  have h2 := LF₂.layerSp_injective S (h1.trans (map_one (LF₂.layerSp S)).symm)
  have h3 := Models.SymplecticPairs.longBlock_injective (K := GaloisField p f) (n := 2) 1
    (h2.trans (map_one _).symm)
  have h4 := torusHom_injective (h3.trans (map_one _).symm)
  exact unit_mul_self_ne_one ha h4

end Params

end CFSG.ClassicalInvolution.RouteD
