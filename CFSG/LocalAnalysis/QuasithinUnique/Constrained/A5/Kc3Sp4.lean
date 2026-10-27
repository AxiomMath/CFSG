module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.QuasithinUnique.A5

open scoped Matrix

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.A5.Kc3J

section Form

open Matrix

variable {F : Type} [Field F]

@[expose] noncomputable def glEnd (ι : Type) [Fintype ι] [DecidableEq ι] :
    GL ι F →* Module.End F (ι → F) where
  toFun g := Matrix.toLin' (g : Matrix ι ι F)
  map_one' := by
    show Matrix.toLin' (1 : Matrix ι ι F) = 1
    rw [Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    show Matrix.toLin' ((g : Matrix ι ι F) * (h : Matrix ι ι F)) =
      Matrix.toLin' (g : Matrix ι ι F) * Matrix.toLin' (h : Matrix ι ι F)
    rw [Matrix.toLin'_mul]
    rfl

theorem glEnd_apply (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι F) (w : ι → F) :
    glEnd ι g w = (g : Matrix ι ι F) *ᵥ w := by
  simp [glEnd, Matrix.toLin'_apply]

theorem glEnd_injective (ι : Type) [Fintype ι] [DecidableEq ι] :
    Function.Injective (glEnd (F := F) ι) := by
  intro g h hgh
  apply Units.ext
  apply Matrix.toLin'.injective
  exact hgh

@[expose] def symJ (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) (1 : Matrix (Fin 2) (Fin 2) F) (-1) 0

@[expose] noncomputable def sympB (F : Type) [Field F] :
    LinearMap.BilinForm F (Fin 2 ⊕ Fin 2 → F) :=
  Matrix.toBilin' (symJ F)

theorem sympB_apply (x y : Fin 2 ⊕ Fin 2 → F) : sympB F x y = x ⬝ᵥ (symJ F) *ᵥ y := by
  simp [sympB, Matrix.toBilin'_apply']

theorem neg_one_matrix [CharP F 2] : (-1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.one_apply]
  split_ifs
  · exact CharTwo.neg_eq 1
  · exact neg_zero

theorem symJ_transpose [CharP F 2] : (symJ F)ᵀ = symJ F := by
  rw [symJ, Matrix.fromBlocks_transpose]
  simp [neg_one_matrix]

theorem symJ_mul_self [CharP F 2] : symJ F * symJ F = 1 := by
  rw [symJ, Matrix.fromBlocks_multiply]
  simp [neg_one_matrix]

theorem sympB_symm [CharP F 2] (x y : Fin 2 ⊕ Fin 2 → F) : sympB F x y = sympB F y x := by
  have h : x ᵥ* symJ F = symJ F *ᵥ x := by
    have := Matrix.vecMul_transpose (symJ F) x
    rwa [symJ_transpose] at this
  rw [sympB_apply, sympB_apply, Matrix.dotProduct_mulVec, h, dotProduct_comm]

theorem sympB_nd [CharP F 2] (x : Fin 2 ⊕ Fin 2 → F) (h : ∀ y, sympB F x y = 0) : x = 0 := by
  funext j
  have h1 := h (symJ F *ᵥ Pi.single j 1)
  rw [sympB_apply, Matrix.mulVec_mulVec, symJ_mul_self, Matrix.one_mulVec] at h1
  simpa using h1

theorem sympB_iso [CharP F 2] (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (hg : gᵀ * symJ F * g = symJ F) (x y : Fin 2 ⊕ Fin 2 → F) :
    sympB F (g *ᵥ x) (g *ᵥ y) = sympB F x y := by
  rw [sympB_apply, sympB_apply, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg,
    ← Matrix.dotProduct_mulVec]

end Form

theorem kc3ForS_psp4 : Kc3ForS Kc3PSp4 := by
  classical
  intro G _ _ K L S₀ T₀ hq hmod hZ hLK hD hperf hSL hS hT hST hTK hTS
  exfalso
  obtain ⟨f, hf2, -, F, hFf, hFfin, hF, ⟨e⟩⟩ := hmod
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, α, hα, hαQ, β, hβ⟩ := hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  let ρ₀ : StatedProj (StatedSp 2 F) →* GL (Fin 2 ⊕ Fin 2) F :=
    QuotientGroup.lift _ (StatedSp 2 F).subtype (by
      intro x hx
      have hx' : x ∈ spScalars 2 F := hx
      rw [spScalars_eq_bot] at hx'
      rw [MonoidHom.mem_ker]
      have : x = 1 := Subgroup.mem_bot.1 hx'
      rw [this]
      rfl)
  have hρ₀inj : Function.Injective ρ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : (s : GL (Fin 2 ⊕ Fin 2) F) = 1 := hx
    have : s = 1 := Subtype.ext h1
    simp [this]
  have hρ₀sp : ∀ x, ((ρ₀ x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
      symJ F * ((ρ₀ x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      symJ F := by
    intro x
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    exact mem_statedSp_iff.1 s.2
  let ρ : ↥K →* Module.End F (Fin 2 ⊕ Fin 2 → F) :=
    (glEnd (F := F) (Fin 2 ⊕ Fin 2)).comp (ρ₀.comp e.toMonoidHom)
  have hρinj : Function.Injective ρ :=
    (glEnd_injective (F := F) (Fin 2 ⊕ Fin 2)).comp (hρ₀inj.comp e.injective)
  have hρapp : ∀ (k : ↥K) (w : Fin 2 ⊕ Fin 2 → F), ρ k w =
      ((ρ₀ (e k) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w :=
    fun k w => glEnd_apply _ _ w
  have hVK : V ≤ K := hVQ.trans (hQL.trans hLK)
  set V' : Subgroup ↥K := V.subgroupOf K with hV'
  have hV2 : IsPGroup 2 ↥V := hQ2.to_le hVQ
  have hV'2 : IsPGroup 2 V' := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVK).symm
  have hnt : ∀ v : ↥V', ρ v = 1 → v = 1 := by
    intro v hv
    have : (v : ↥K) = 1 := hρinj (by rw [hv, map_one])
    exact Subtype.ext this
  have hW4 : Module.finrank F (Fin 2 ⊕ Fin 2 → F) = 4 := by
    simp
  obtain ⟨C, A, hC, hAC, hA0, hAg, hspan⟩ :=
    Kc3J.partA ((Subgroup.subgroupOfEquivOfLe hVK).trans β) ρ hW4 hV'2 hnt
      (delta5Norm_of_d5 hLK hVQ hQL hLV α hα β hβ)
  refine Kc3J.no_symplectic hW4 (sympB F) (sympB_symm) (sympB_nd) C hC A hAC hA0 ?_ hspan
  intro i x y
  obtain ⟨g, hg, hgi⟩ := hAg i
  have hgx : ∀ w, w + A i w = ρ g w := by
    intro w
    rw [hgi]
    simp
  rw [hgx x, hgx y, hρapp, hρapp]
  exact sympB_iso _ (hρ₀sp _) x y

theorem kc3For_psp4
    : Kc3For Kc3PSp4 := kc3For_of_simple isoInv_psp4 kc3ForS_psp4

end CFSG.QuasithinUnique.A5
