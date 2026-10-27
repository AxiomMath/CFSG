module

public import CFSG.ClassicalInvolution.WeakCT.B2Hom
public import CFSG.ClassicalGroups.Symplectic.Model

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open CFSG.LieType.Universal.Symplectic (rootDatum cartanC)
open CFSG.Assembly.LowTwoRank (StatedSp StatedScalars)
open scoped commutatorElement MatrixGroups

section Blocks

variable (F : Type) [Field F]

noncomputable def spBlock (i : Fin 2) : SL(2, F) →* StatedSp 2 F :=
  Classical.choose (Steinberg.Sp.rankOne (n := 2) (F := F) i)

variable {F}

theorem spBlock_injective (i : Fin 2) : Function.Injective (spBlock F i) :=
  (Classical.choose_spec (Steinberg.Sp.rankOne (n := 2) (F := F) i)).1

theorem spBlock_upper (i : Fin 2) (c : F) :
    spBlock F i (tv 0 1 c) = Steinberg.Sp.x 2 F (Pi.single i 1) c := by
  rw [tv01_eq_sl2Upper]
  exact (Classical.choose_spec (Steinberg.Sp.rankOne (n := 2) (F := F) i)).2.1 c

theorem spBlock_lower (i : Fin 2) (c : F) :
    spBlock F i (tv 1 0 c) = Steinberg.Sp.x 2 F (-Pi.single i 1) c := by
  rw [tv10_eq_sl2Lower]
  exact (Classical.choose_spec (Steinberg.Sp.rankOne (n := 2) (F := F) i)).2.2 c

theorem hom_ext_sl2 {G : Type*} [Group G] {f g : SL(2, F) →* G}
    (hu : ∀ c, f (tv 0 1 c) = g (tv 0 1 c)) (hv : ∀ c, f (tv 1 0 c) = g (tv 1 0 c)) : f = g := by
  refine MonoidHom.ext fun A => ?_
  have hA : A ∈ Subgroup.closure ({g | ∃ c : F, g = tv 0 1 c} ∪ {g | ∃ c : F, g = tv 1 0 c}) := by
    rw [closure_tv_two]
    trivial
  induction hA using Subgroup.closure_induction with
  | mem y hy => rcases hy with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;> [exact hu c; exact hv c]
  | one => rw [map_one, map_one]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]
  | inv y _ hy => rw [map_inv, map_inv, hy]

end Blocks

section Hom

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {s l : Fin D.rank}

theorem coords_single_zero : coords (Pi.single (0 : Fin 2) (1 : ℤ)) = (1, 0) := by
  simp [coords]

theorem coords_single_one : coords (Pi.single (1 : Fin 2) (1 : ℤ)) = (0, 1) := by
  simp [coords]

theorem coords_neg_single_zero : coords (-Pi.single (0 : Fin 2) (1 : ℤ)) = (-1, 0) := by
  simp [coords]

theorem coords_neg_single_one : coords (-Pi.single (1 : Fin 2) (1 : ℤ)) = (0, -1) := by
  simp [coords]

theorem single_mem_sp_roots (i : Fin 2) :
    (Pi.single i (1 : ℤ) : Fin 2 → ℤ) ∈ (Steinberg.Sp.Φ 2 F).roots :=
  single_mem_roots (D := rootDatum 2 F) i

theorem neg_single_mem_sp_roots (i : Fin 2) :
    (-Pi.single i (1 : ℤ) : Fin 2 → ℤ) ∈ (Steinberg.Sp.Φ 2 F).roots :=
  neg_mem_roots (D := rootDatum 2 F) (single_mem_roots (D := rootDatum 2 F) i)

theorem hom_block_eq {φ : StatedSp 2 F →* K} {e : ℤ × ℤ → F}
    (he1 : e (1, 0) = 1) (he2 : e (-1, 0) = 1) (he3 : e (0, 1) = 1) (he4 : e (0, -1) = 1)
    (hφ : ∀ γ ∈ (Steinberg.Sp.Φ 2 F).roots, ∀ c : F,
      φ (Steinberg.Sp.x 2 F γ c) = x (pair s l (coords γ)) (e (coords γ) * c))
    {ρs ρl : SL(2, F) →* K}
    (hs : ∀ c, ρs (tv 0 1 c) = x (sroot s) c ∧ ρs (tv 1 0 c) = x (-sroot s) c)
    (hl : ∀ c, ρl (tv 0 1 c) = x (sroot l) c ∧ ρl (tv 1 0 c) = x (-sroot l) c) :
    φ.comp (spBlock F 0) = ρs ∧ φ.comp (spBlock F 1) = ρl := by
  have rS0 : (Pi.single (0 : Fin 2) (1 : ℤ)) ∈ (Steinberg.Sp.Φ 2 F).roots :=
    single_mem_roots (D := rootDatum 2 F) (spS (F := F))
  have rS1 : (Pi.single (1 : Fin 2) (1 : ℤ)) ∈ (Steinberg.Sp.Φ 2 F).roots :=
    single_mem_roots (D := rootDatum 2 F) (spL (F := F))
  have rN0 : (-Pi.single (0 : Fin 2) (1 : ℤ)) ∈ (Steinberg.Sp.Φ 2 F).roots :=
    neg_mem_roots (D := rootDatum 2 F) rS0
  have rN1 : (-Pi.single (1 : Fin 2) (1 : ℤ)) ∈ (Steinberg.Sp.Φ 2 F).roots :=
    neg_mem_roots (D := rootDatum 2 F) rS1
  refine ⟨hom_ext_sl2 (fun c => ?_) (fun c => ?_), hom_ext_sl2 (fun c => ?_) (fun c => ?_)⟩
  · rw [MonoidHom.comp_apply, spBlock_upper, hφ _ rS0, coords_single_zero, he1, one_mul,
      (hs c).1, ← pair_one_zero s l]
  · rw [MonoidHom.comp_apply, spBlock_lower, hφ _ rN0, coords_neg_single_zero, he2, one_mul,
      (hs c).2, ← pair_neg_one_zero s l]
  · rw [MonoidHom.comp_apply, spBlock_upper, hφ _ rS1, coords_single_one, he3, one_mul,
      (hl c).1, ← pair_zero_one s l]
  · rw [MonoidHom.comp_apply, spBlock_lower, hφ _ rN1, coords_neg_single_one, he4, one_mul,
      (hl c).2, ← pair_zero_neg_one s l]

theorem hom_weylElement {φ : StatedSp 2 F →* K} {e : ℤ × ℤ → F}
    (he1 : e (1, 0) = 1) (he2 : e (-1, 0) = 1)
    (hφ : ∀ γ ∈ (Steinberg.Sp.Φ 2 F).roots, ∀ c : F,
      φ (Steinberg.Sp.x 2 F γ c) = x (pair s l (coords γ)) (e (coords γ) * c)) :
    φ (Steinberg.weylElement (Steinberg.Sp.x 2 F) (0 : Fin 2) 1) =
      Steinberg.weylElement x s 1 := by
  have rS0 : (Pi.single (0 : Fin 2) (1 : ℤ)) ∈ (Steinberg.Sp.Φ 2 F).roots :=
    single_mem_roots (D := rootDatum 2 F) (spS (F := F))
  have rN0 : (-Pi.single (0 : Fin 2) (1 : ℤ)) ∈ (Steinberg.Sp.Φ 2 F).roots :=
    neg_mem_roots (D := rootDatum 2 F) rS0
  unfold Steinberg.weylElement
  rw [map_mul, map_mul]
  have h1 : φ (Steinberg.Sp.x 2 F (Pi.single (0 : Fin 2) 1) ((1 : Fˣ) : F)) =
      x (Pi.single s 1) 1 := by
    rw [hφ _ rS0, coords_single_zero, he1, pair_one_zero]
    simp
  have h2 : φ (Steinberg.Sp.x 2 F (-Pi.single (0 : Fin 2) 1) (-(((1 : Fˣ)⁻¹ : Fˣ) : F))) =
      x (-Pi.single s 1) (-1) := by
    rw [hφ _ rN0, coords_neg_single_zero, he2, pair_neg_one_zero]
    simp
  rw [h1, h2]
  simp

end Hom


section Center

variable {F : Type} [Field F]

open CFSG.ClassicalGroups.Symplectic in
theorem center_sp_scalar {g : StatedSp 2 F} (hg : g ∈ Subgroup.center (StatedSp 2 F)) :
    ∃ c : Fˣ, (c : F) ^ 2 = 1 ∧
      (((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        Matrix.scalar (Fin 2 ⊕ Fin 2) (c : F) := by
  rw [Symplectic.center_eq] at hg
  obtain ⟨a, ha⟩ : ((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedScalars (Fin 2 ⊕ Fin 2) F :=
    hg
  have hmat : (((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2)
      (Fin 2 ⊕ Fin 2) F) = Matrix.scalar (Fin 2 ⊕ Fin 2) (a : F) := by
    rw [← ha]
    rfl
  refine ⟨a, ?_, hmat⟩
  have hsp : (((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2)
      (Fin 2 ⊕ Fin 2) F) ∈ Matrix.symplecticGroup (Fin 2) F := by
    exact TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.1
      ((statedSp_eq_GLSymplectic (n := 2) (K := F)).le g.2)
  rw [hmat] at hsp
  exact (scalar_mem_symplecticGroup_iff (by norm_num) _).1 hsp

theorem center_sp_eq {g h : StatedSp 2 F} (hg : g ∈ Subgroup.center (StatedSp 2 F))
    (hh : h ∈ Subgroup.center (StatedSp 2 F)) (hg1 : g ≠ 1) (hh1 : h ≠ 1) : g = h := by
  have key : ∀ g : StatedSp 2 F, g ∈ Subgroup.center (StatedSp 2 F) → g ≠ 1 →
      (((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        Matrix.scalar (Fin 2 ⊕ Fin 2) (-1 : F) := by
    intro g hg hg1
    obtain ⟨a, ha, hga⟩ := center_sp_scalar hg
    have hmul : ((a : F) - 1) * ((a : F) + 1) = 0 := by linear_combination ha
    rcases mul_eq_zero.1 hmul with h1 | h1
    · exfalso
      apply hg1
      have h2 : (a : F) = 1 := by linear_combination h1
      refine Subtype.ext (Units.ext ?_)
      rw [hga, h2]
      simp
    · rw [hga]
      congr 2
      linear_combination h1
  exact Subtype.ext (Units.ext ((key g hg hg1).trans (key h hh hh1).symm))

end Center

section C0

variable (F : Type) [Field F]

noncomputable def spC0 : StatedSp 2 F :=
  Steinberg.weylElement (Steinberg.Sp.x 2 F) (0 : Fin 2) 1 ^ 2

theorem exists_sp_chevalleyExtras :
    ∃ O : Steinberg.CommOrder (Steinberg.Sp.Φ 2 F),
      Steinberg.ChevalleyExtras (rootDatum 2 F) F (Steinberg.Sp.x 2 F) Steinberg.Sp.commC O := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (rootDatum 2 F).isFiniteType
    (Dv := (rootDatum 2 F).divisible) rfl
  exact ⟨O, Steinberg.Sp.chevalleyExtras le_rfl O _ (Steinberg.Sp.commutatorFormula O)⟩

theorem spC0_mem_center : spC0 F ∈ Subgroup.center (StatedSp 2 F) := by
  obtain ⟨O, hE'⟩ := exists_sp_chevalleyExtras F
  have hcomm : ∀ γ ∈ (Steinberg.Sp.Φ 2 F).roots, ∀ c : F,
      Commute (spC0 F) (Steinberg.Sp.x 2 F γ c) := by
    intro γ hγ c
    refine weylElement_sq_commute hE' (k := spS (F := F)) hγ ?_ c
    have h : ∑ j, (rootDatum 2 F).cartan spS j * γ j =
        ∑ j, (rootDatum 2 F).cartan spS j * (pair (spS (F := F)) spL (coords γ)) j := by
      rw [sp_pair_coords γ]
    rw [h, pairing_pair, (rootDatum 2 F).isFiniteType.apply_self, sp_cartan_01]
    exact ⟨(coords γ).1 - (coords γ).2, by ring⟩
  have hle : (⨆ γ ∈ (rootDatum 2 F).roots, (rootDatum 2 F).rootGroup γ) ≤
      Subgroup.centralizer {spC0 F} := by
    refine iSup₂_le fun γ hγ g hg => ?_
    obtain ⟨c, rfl⟩ := ((hE'.param γ hγ).1 g).1 hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (hcomm γ hγ c).eq
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer {spC0 F} := by
    refine hle ?_
    rw [show (⨆ γ ∈ (rootDatum 2 F).roots, (rootDatum 2 F).rootGroup γ) = ⊤ from
      (Symplectic.isCTGroupDatum 2 F).iSup_eq_top]
    trivial
  rw [Subgroup.mem_centralizer_iff] at hg
  exact (hg _ rfl).symm

end C0

section Inj

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {s l : Fin D.rank}

theorem hom_injective [Finite F] (hF : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0)
    (hE : Steinberg.ChevalleyExtras D F x C O) {φ : StatedSp 2 F →* K} {e : ℤ × ℤ → F}
    (he1 : e (1, 0) = 1) (he2 : e (-1, 0) = 1)
    (hφ : ∀ γ ∈ (Steinberg.Sp.Φ 2 F).roots, ∀ c : F,
      φ (Steinberg.Sp.x 2 F γ c) = x (pair s l (coords γ)) (e (coords γ) * c)) :
    Function.Injective φ := by
  have hC0 : φ (spC0 F) ≠ 1 := by
    unfold spC0
    rw [map_pow, hom_weylElement he1 he2 hφ]
    obtain ⟨ψ, hψ, -, -, hsq⟩ := weylElement_one_sq hE s
    rw [hsq]
    intro h
    have h1 : wS (1 : Fˣ) * wS (1 : Fˣ) = (1 : SL(2, F)) := hψ (by rw [h, map_one])
    have h3 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, wS, coe_sl2Upper, coe_sl2Lower,
      Matrix.mul_fin_two] at h3
    apply h2
    simp at h3
    linear_combination -h3
  have hC0' : spC0 F ≠ 1 := fun h => hC0 (by rw [h, map_one])
  have hq : IsQuasisimple (StatedSp 2 F) :=
    Symplectic.isQuasisimple 2 F (by norm_num) (Or.inl (Or.inr hF))
  have hker : φ.ker ≤ Subgroup.center (StatedSp 2 F) :=
    CurtisTits.ker_le_center_of_isQuasisimple hq ⟨spC0 F, hC0⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hg1
  have hgc : g ∈ Subgroup.center (StatedSp 2 F) := hker hg
  exact hC0 (by rw [← center_sp_eq hgc (spC0_mem_center F) hg1 hC0']; exact hg)

theorem exists_b2Levi [Finite F] (hF : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1) :
    ∃ φ : StatedSp 2 F →* K, Function.Injective φ ∧
      (∀ γ ∈ pairRoots D s l, ∀ g ∈ D.rootGroup γ, g ∈ φ.range) ∧
      (∀ c, φ (spBlock F 0 (tv 0 1 c)) = x (sroot s) c ∧
        φ (spBlock F 0 (tv 1 0 c)) = x (-sroot s) c ∧
        φ (spBlock F 1 (tv 0 1 c)) = x (sroot l) c ∧
        φ (spBlock F 1 (tv 1 0 c)) = x (-sroot l) c) := by
  obtain ⟨φ, e, hesq, he1, he2, he3, he4, hφ⟩ := exists_b2Hom hE hdiv hcsl hcls
  have hs : ∃ ρ : SL(2, F) →* K, ∀ c, ρ (tv 0 1 c) = x (sroot s) c ∧
      ρ (tv 1 0 c) = x (-sroot s) c := by
    obtain ⟨ρ, -, hu, hl⟩ := hE.rankOne s
    exact ⟨ρ, fun c => ⟨by rw [tv01_eq_sl2Upper, hu], by rw [tv10_eq_sl2Lower, hl]⟩⟩
  have hl : ∃ ρ : SL(2, F) →* K, ∀ c, ρ (tv 0 1 c) = x (sroot l) c ∧
      ρ (tv 1 0 c) = x (-sroot l) c := by
    obtain ⟨ρ, -, hu, hl⟩ := hE.rankOne l
    exact ⟨ρ, fun c => ⟨by rw [tv01_eq_sl2Upper, hu], by rw [tv10_eq_sl2Lower, hl]⟩⟩
  obtain ⟨ρs, hρs⟩ := hs
  obtain ⟨ρl, hρl⟩ := hl
  obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ hρs hρl
  refine ⟨φ, hom_injective hF h2 hE he1 he2 hφ, fun γ hγ g hg => ?_, fun c => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := pairRoots_subset_zB2 hdiv hcsl hcls hγ
    obtain ⟨c, rfl⟩ := ((hE.param _ (pair_mem_roots_zB2 hcsl hcls z hz)).1 g).1 hg
    refine ⟨Steinberg.Sp.x 2 F (pair (spS (F := F)) spL z) (e z * c), ?_⟩
    rw [hφ _ (pair_mem_sp_roots hz), sp_coords_pair, ← mul_assoc, hesq z hz, one_mul]
  · have h1 := congrArg (fun f : SL(2, F) →* K => f (tv 0 1 c)) hb0
    have h2 := congrArg (fun f : SL(2, F) →* K => f (tv 1 0 c)) hb0
    have h3 := congrArg (fun f : SL(2, F) →* K => f (tv 0 1 c)) hb1
    have h4 := congrArg (fun f : SL(2, F) →* K => f (tv 1 0 c)) hb1
    simp only [MonoidHom.comp_apply] at h1 h2 h3 h4
    exact ⟨h1.trans (hρs c).1, h2.trans (hρs c).2, h3.trans (hρl c).1, h4.trans (hρl c).2⟩

end Inj

end CFSG.ClassicalInvolution.WeakCT
