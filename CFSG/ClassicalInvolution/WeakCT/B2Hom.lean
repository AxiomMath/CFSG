module

public import CFSG.ClassicalInvolution.WeakCT.B2Match
public import CFSG.LieType.Steinberg.Classical.Symplectic

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open CFSG.LieType.Universal.Symplectic (rootDatum cartanC)
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped commutatorElement

section SpCoords

variable {F : Type} [Field F]

@[expose] def coords (γ : Fin 2 → ℤ) : ℤ × ℤ := (γ 0, γ 1)

theorem pair_coords (γ : Fin 2 → ℤ) : pair (0 : Fin 2) 1 (coords γ) = γ := by
  funext i
  fin_cases i <;> simp [coords, pair_apply]

theorem coords_pair (z : ℤ × ℤ) : coords (pair (0 : Fin 2) 1 z) = z := by
  simp [coords, pair_apply]

theorem coords_add (α β : Fin 2 → ℤ) : coords (α + β) = coords α + coords β := rfl

theorem coords_nsmul (n : ℕ) (α : Fin 2 → ℤ) : coords (n • α) = n • coords α := rfl

@[expose] def spS : Fin (rootDatum 2 F).rank := (0 : Fin 2)

@[expose] def spL : Fin (rootDatum 2 F).rank := (1 : Fin 2)

theorem sp_cartan_01 : (rootDatum 2 F).cartan spS spL = -2 := by
  show cartanC 2 0 1 = -2
  decide

theorem sp_cartan_10 : (rootDatum 2 F).cartan spL spS = -1 := by
  show cartanC 2 1 0 = -1
  decide

theorem sp_pair_coords (γ : Fin 2 → ℤ) : pair (spS (F := F)) spL (coords γ) = γ :=
  pair_coords γ

theorem sp_coords_pair (z : ℤ × ℤ) : coords (pair (spS (F := F)) spL z) = z :=
  coords_pair z

theorem coords_mem_zB2 {γ : Fin 2 → ℤ} (hγ : γ ∈ (Steinberg.Sp.Φ 2 F).roots) :
    coords γ ∈ zB2 :=
  mem_zB2_of_pair_mem (D := rootDatum 2 F) (s := spS) (l := spL) rfl sp_cartan_01 sp_cartan_10
    (by rw [sp_pair_coords]; exact hγ)

theorem pair_mem_sp_roots {z : ℤ × ℤ} (hz : z ∈ zB2) :
    pair (spS (F := F)) spL z ∈ (Steinberg.Sp.Φ 2 F).roots :=
  pair_mem_roots_zB2 (D := rootDatum 2 F) (s := spS) (l := spL) sp_cartan_01 sp_cartan_10 z hz

end SpCoords

section Lift

open CFSG.LieType.Steinberg

theorem lift_chevOf {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {k : Type*}
    [Field k] {G : Type*} [Group G] (y : (ι → ℤ) → k → G) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) (c : k) :
    FreeGroup.lift (chevEval y) (chevOf (Φ := Φ) γ c) = y γ c := by
  simp [chevOf, hγ, chevEval]

end Lift

section Main

open CFSG.LieType.Steinberg

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

def spTwist (x : (Fin D.rank → ℤ) → F → K) (s l : Fin D.rank) (e : ℤ × ℤ → F)
    (γ : Fin 2 → ℤ) (c : F) : K :=
  x (pair s l (coords γ)) (e (coords γ) * c)

theorem relations_hold (hE : ChevalleyExtras D F x C O) {s l : Fin D.rank}
    (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1)
    (O' : CommOrder (Steinberg.Sp.Φ 2 F)) (C' : (Fin 2 → ℤ) → (Fin 2 → ℤ) → ℕ × ℕ → ℤ)
    (e : ℤ × ℤ → F)
    (hmatch : ∀ z ∈ zB2, ∀ w ∈ zB2, z + w ≠ 0 → ∀ p ∈ eList z w,
      Cz F C s l z w p * e z ^ p.1 * e w ^ p.2 =
        e (p.1 • z + p.2 • w) * Cz F C' (0 : Fin 2) 1 z w p) :
    ∀ r ∈ relA (Steinberg.Sp.Φ 2 F) F ∪ relB (Steinberg.Sp.Φ 2 F) F O' C',
      FreeGroup.lift (chevEval (spTwist x s l e)) r = 1 := by
  have hcoord : ∀ γ ∈ (Steinberg.Sp.Φ 2 F).roots, pair s l (coords γ) ∈ D.roots := fun γ hγ =>
    pair_mem_roots_zB2 hcsl hcls _ (coords_mem_zB2 hγ)
  rintro r (⟨γ, hγ, c, d, rfl⟩ | ⟨α, hα, β, hβ, hαβ, c, d, rfl⟩)
  ·
    simp only [map_mul, map_inv, lift_chevOf _ hγ]
    unfold spTwist
    rw [mul_add, x_add' hE (hcoord γ hγ), mul_inv_cancel]
  ·
    have hz := coords_mem_zB2 hα
    have hw := coords_mem_zB2 hβ
    have hzw : coords α + coords β ≠ 0 := by
      intro h
      apply hαβ
      have h1 : pair (spS (F := F)) spL (coords α + coords β) = 0 := by rw [h, map_zero]
      rwa [map_add, sp_pair_coords, sp_pair_coords] at h1
    have hp : ∀ p ∈ O'.list α β, p.1 • α + p.2 • β ∈ (Steinberg.Sp.Φ 2 F).roots := fun p hp =>
      ((O'.mem_iff α hα β hβ hαβ p).1 hp).2.2
    have hperm : (O'.list α β).Perm (eList (coords α) (coords β)) := by
      refine (List.perm_ext_iff_of_nodup (O'.nodup α β) (nodup_eList _ _)).2 fun p => ?_
      rw [O'.mem_iff α hα β hβ hαβ, mem_eList hz hw hzw]
      refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩)
      · have := coords_mem_zB2 h
        rwa [coords_add, coords_nsmul, coords_nsmul] at this
      · have := pair_mem_sp_roots (F := F) h
        rwa [map_add, map_nsmul, map_nsmul, sp_pair_coords, sp_pair_coords] at this
    simp only [map_mul, map_inv, map_commutatorElement, lift_chevOf _ hα, lift_chevOf _ hβ,
      map_list_prod, List.map_map]
    rw [mul_inv_eq_one]
    have hterm : ∀ p ∈ O'.list α β, (⇑(FreeGroup.lift (chevEval (spTwist x s l e))) ∘
        fun p => chevOf (Φ := Steinberg.Sp.Φ 2 F) (p.1 • α + p.2 • β)
          (((C' α β p : ℤ) : F) * c ^ p.1 * d ^ p.2)) p =
        x (pair s l (p.1 • coords α + p.2 • coords β))
          (Cz F C s l (coords α) (coords β) p * (e (coords α) * c) ^ p.1 *
            (e (coords β) * d) ^ p.2) := by
      intro p hpl
      simp only [Function.comp]
      rw [lift_chevOf _ (hp p hpl)]
      unfold spTwist
      rw [coords_add, coords_nsmul, coords_nsmul]
      congr 1
      have hpe : p ∈ eList (coords α) (coords β) := hperm.mem_iff.1 hpl
      have hm := hmatch _ hz _ hw hzw p hpe
      have hCsp : Cz F C' (0 : Fin 2) 1 (coords α) (coords β) p = ((C' α β p : ℤ) : F) := by
        unfold Cz
        rw [pair_coords, pair_coords]
      rw [hCsp] at hm
      rw [mul_pow, mul_pow]
      linear_combination (-(c ^ p.1 * d ^ p.2)) * hm
    rw [List.map_congr_left hterm]
    exact comm_rel_perm hE hdiv hcsl hcls hz hw hzw hperm (e (coords α) * c) (e (coords β) * d)

theorem exists_b2Hom [Finite F] (hE : ChevalleyExtras D F x C O) {s l : Fin D.rank}
    (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1) :
    ∃ (φ : StatedSp 2 F →* K) (e : ℤ × ℤ → F), (∀ z ∈ zB2, e z * e z = 1) ∧
      e (1, 0) = 1 ∧ e (-1, 0) = 1 ∧ e (0, 1) = 1 ∧ e (0, -1) = 1 ∧
      ∀ γ ∈ (Steinberg.Sp.Φ 2 F).roots, ∀ c : F,
        φ (Steinberg.Sp.x 2 F γ c) = x (pair s l (coords γ)) (e (coords γ) * c) := by
  obtain ⟨O'⟩ := nonempty_commOrder_ofCartan (rootDatum 2 F).isFiniteType
    (Dv := (rootDatum 2 F).divisible) rfl
  obtain ⟨⟨C', -, hC'⟩, hpres⟩ := Steinberg.Sp.presentationB (F := F) (n := 2) le_rfl O'
  obtain ⟨hrel, hbij⟩ := hpres C' hC'
  have hE' := Steinberg.Sp.chevalleyExtras (F := F) (n := 2) le_rfl O' C' hC'
  obtain ⟨e, he1, he2, he3, he4, hesq, hmatch⟩ :=
    (B2Sys.ofHE hE s l hdiv hcsl hcls).exists_match
      (B2Sys.ofHE hE' spS spL rfl sp_cartan_01 sp_cartan_10)
  have hrelK := relations_hold hE hdiv hcsl hcls O' C' e hmatch
  refine ⟨(PresentedGroup.toGroup hrelK).comp
    (MulEquiv.ofBijective (PresentedGroup.toGroup hrel) hbij).symm.toMonoidHom, e, hesq, he1, he2,
    he3, he4, fun γ hγ c => ?_⟩
  have h1 : (PresentedGroup.toGroup hrel) (PresentedGroup.of (⟨γ, hγ⟩, c)) =
      Steinberg.Sp.x 2 F γ c := by
    rw [PresentedGroup.toGroup.of]
    rfl
  have h2 : (MulEquiv.ofBijective (PresentedGroup.toGroup hrel) hbij).symm
      (Steinberg.Sp.x 2 F γ c) = PresentedGroup.of (⟨γ, hγ⟩, c) := by
    rw [MulEquiv.symm_apply_eq]
    exact h1.symm
  show (PresentedGroup.toGroup hrelK) ((MulEquiv.ofBijective (PresentedGroup.toGroup hrel)
    hbij).symm (Steinberg.Sp.x 2 F γ c)) = _
  rw [h2, PresentedGroup.toGroup.of]
  rfl

end Main


end CFSG.ClassicalInvolution.WeakCT
