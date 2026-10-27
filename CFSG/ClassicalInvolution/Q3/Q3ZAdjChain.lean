module

public import CFSG.ClassicalInvolution.Q3.Q3ZAdjEval
public import CFSG.ClassicalInvolution.Q3.Q3ZMat
public import CFSG.ClassicalInvolution.Q3.Q3ZAut
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.WeakCT (blockSL)
open scoped MatrixGroups

theorem exists_mulEquiv_of_range_eq {H G : Type*} [Group H] [Group G] {f g : H →* G}
    (hf : Function.Injective f) (hg : Function.Injective g) (h : f.range = g.range) :
    ∃ α : H ≃* H, ∀ a, f (α a) = g a := by
  have hmem : ∀ a, g a ∈ f.range := fun a => h ▸ ⟨a, rfl⟩
  choose φ hφ using hmem
  have hφinj : Function.Injective φ := fun a b hab => hg (by rw [← hφ, ← hφ, hab])
  have hmul : ∀ a b, φ (a * b) = φ a * φ b := fun a b =>
    hf (by rw [map_mul, hφ, hφ, hφ, map_mul])
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨a, ha⟩ : f b ∈ g.range := h ▸ ⟨b, rfl⟩
    exact ⟨a, hf (by rw [hφ, ha])⟩
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' φ hmul) ⟨hφinj, hsurj⟩, hφ⟩

theorem mem_map_range {H G' G : Type*} [Group H] [Group G'] [Group G] (θ : G' →* G)
    (f : H →* G') (a : H) : θ (f a) ∈ f.range.map θ :=
  Subgroup.mem_map_of_mem θ (MonoidHom.mem_range.2 ⟨a, rfl⟩)

theorem adj_xpS_ne_one : xpS ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, ZMod 3) => (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1) h
  simp [coe_xpS] at this

theorem adj_autXp_eq : autXp = xpS := Subtype.ext rfl

theorem adj_autXm_eq : autXm = xmS := Subtype.ext rfl

theorem range_eq_closure_pair {H : Type*} [Group H] (φ : SL(2, ZMod 3) →* H) :
    φ.range = Subgroup.closure {φ xpS, φ xmS} := by
  rw [MonoidHom.range_eq_map, ← closure_xp_xm, MonoidHom.map_closure]
  congr 1
  simp

section Assembly

variable {G : Type} [Group G]

local notation "bA0" => (blockSL (ZMod 3) 3 2 0 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "bA1" => (blockSL (ZMod 3) 3 2 1 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "sB" =>
  (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))
local notation "lB2" => (longBlock (ZMod 3) 2 1 : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))
local notation "lB3" => (longBlock (ZMod 3) 3 2 : SL(2, ZMod 3) →* StatedSp 3 (ZMod 3))

theorem exists_hom_of_chain (U : Fin 3 → Subgroup G)
    (hcomm : ∀ a ∈ U 0, ∀ b ∈ U 2, a * b = b * a)
    (hU : ∀ g : Fin 12 → G, RelsHold g v6Words →
      ∃ ψ : StatedSp 3 (ZMod 3) →* G, ∀ i, ψ (v6Mat i) = g i)
    (hC : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → G,
      RelsHold g (v6aWords k) → ∀ i, g i = 1)
    (θA : SL(3, ZMod 3) →* G) (hιA : Function.Injective (θA.comp bA1))
    (hA0 : (bA0).range.map θA = U 0) (hA1 : (bA1).range.map θA = U 1)
    (θB : StatedSp 2 (ZMod 3) →* G) (hιB : Function.Injective (θB.comp sB))
    (hιL : Function.Injective (θB.comp lB2))
    (hB2 : (lB2).range.map θB = U 2) (hB1 : (sB).range.map θB = U 1) :
    ∃ ψ : StatedSp 3 (ZMod 3) →* G, (lB3).range.map ψ = U 2 ∧ ∃ x, ψ x ≠ 1 := by
  have hrA : (θA.comp bA1).range = U 1 := by rw [MonoidHom.range_comp]; exact hA1
  have hrB : (θB.comp sB).range = U 1 := by rw [MonoidHom.range_comp]; exact hB1
  obtain ⟨α, hα⟩ := exists_mulEquiv_of_range_eq hιA hιB (hrA.trans hrB.symm)
  have hα' : ∀ a, θA (bA1 (α a)) = θB (sB a) := hα
  have hU2 : U 2 ≠ ⊥ := by
    intro h
    have hmem : θB (lB2 xpS) ∈ U 2 := hB2 ▸ mem_map_range θB _ xpS
    rw [h, Subgroup.mem_bot] at hmem
    exact adj_xpS_ne_one (hιL (a₁ := xpS) (a₂ := 1) (by simpa using hmem))
  have hrelA : RelsHold (fun j => θA (a2Mat j)) a2Words := relsHold_hom θA a2_relsHold
  have m0p : θA (a2Mat 0) ∈ U 0 := by
    rw [a2Mat_zero, ← hA0]
    exact mem_map_range θA _ xpS
  have m0m : θA (a2Mat 1) ∈ U 0 := by
    rw [a2Mat_one, ← hA0]
    exact mem_map_range θA _ xmS
  rcases aut_dichotomy α with ⟨B, hBs, hBl⟩ | ⟨k, hk, ha, hb⟩
  ·
    let θB' : StatedSp 2 (ZMod 3) →* G := θB.comp (MulAut.conj B⁻¹).toMonoidHom
    have hθB' : ∀ x, θB' x = θB (B⁻¹ * x * B) := by
      intro x
      simp [θB']
    have hS : ∀ A, θB' (sB A) = θA (bA1 A) := by
      intro A
      have h1 := hBs (α.symm A)
      rw [α.apply_symm_apply] at h1
      have h2 : B⁻¹ * sB A * B = sB (α.symm A) := by
        rw [← h1]
        group
      rw [hθB', h2, ← hα' (α.symm A), α.apply_symm_apply]
    have hLconj : (lB2).range.map (MulAut.conj B⁻¹).toMonoidHom = (lB2).range := by
      ext x
      constructor
      · rintro ⟨y, ⟨A, rfl⟩, rfl⟩
        obtain ⟨A'', hA''⟩ := (hBl A).2
        exact ⟨A'', by
          show lB2 A'' = B⁻¹ * lB2 A * B⁻¹⁻¹
          rw [inv_inv, hA'']⟩
      · rintro ⟨A, rfl⟩
        obtain ⟨A', hA'⟩ := (hBl A).1
        refine ⟨lB2 A', ⟨A', rfl⟩, ?_⟩
        show B⁻¹ * lB2 A' * B⁻¹⁻¹ = lB2 A
        rw [← hA', inv_inv]
        group
    have hB2' : (lB2).range.map θB' = U 2 := by
      rw [← hB2]
      show (lB2).range.map (θB.comp (MulAut.conj B⁻¹).toMonoidHom) = _
      rw [← Subgroup.map_map, hLconj]
    have m2p : θB' (c2Mat 2) ∈ U 2 := by
      rw [c2Mat_two, ← hB2']
      exact mem_map_range θB' _ xpS
    have m3p : θB' (c2Mat 3) ∈ U 2 := by
      rw [c2Mat_three, ← hB2']
      exact mem_map_range θB' _ xmS
    have h45 : (fun j => θA (a2Mat j)) 4 = (fun j => θB' (c2Mat j)) 5 := by
      show θA (a2Mat 4) = θB' (c2Mat 5)
      rw [a2Mat_four, c2Mat_five, hS]
    have h56 : (fun j => θA (a2Mat j)) 5 = (fun j => θB' (c2Mat j)) 6 := by
      show θA (a2Mat 5) = θB' (c2Mat 6)
      rw [a2Mat_five, c2Mat_six, hS]
    have hrels := relsHold_v6 (fun j => θA (a2Mat j)) (fun j => θB' (c2Mat j)) hrelA
      (relsHold_hom θB' c2_relsHold) h45 h56 (hcomm _ m0p _ m2p) (hcomm _ m0p _ m3p)
      (hcomm _ m0m _ m2p) (hcomm _ m0m _ m3p)
    obtain ⟨ψ, hψ⟩ := hU _ hrels
    have hψ2 : ψ (lB3 xpS) = θB' (lB2 xpS) := by
      rw [← v6Mat_two, hψ 2]
      show θB' (c2Mat 2) = _
      rw [c2Mat_two]
    have hψ3 : ψ (lB3 xmS) = θB' (lB2 xmS) := by
      rw [← v6Mat_three, hψ 3]
      show θB' (c2Mat 3) = _
      rw [c2Mat_three]
    have hrange : (lB3).range.map ψ = U 2 := by
      rw [← hB2', ← MonoidHom.range_comp, ← MonoidHom.range_comp, range_eq_closure_pair,
        range_eq_closure_pair]
      simp only [MonoidHom.comp_apply, hψ2, hψ3]
    refine ⟨ψ, hrange, ?_⟩
    by_contra hall
    have hall' : ∀ x, ψ x = 1 := fun x => by
      by_contra hx
      exact hall ⟨x, hx⟩
    apply hU2
    rw [← hrange, eq_bot_iff]
    rintro _ ⟨_, _, rfl⟩
    simp [hall']
  ·
    exfalso
    have hrelC : RelsHold (fun j => θB (c2Mat j)) c2Words := relsHold_hom θB c2_relsHold
    have m2p : θB (c2Mat 2) ∈ U 2 := by
      rw [c2Mat_two, ← hB2]
      exact mem_map_range θB _ xpS
    have m3p : θB (c2Mat 3) ∈ U 2 := by
      rw [c2Mat_three, ← hB2]
      exact mem_map_range θB _ xmS
    have hp : gOf (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j)) xPlus =
        (θA.comp bA1) autXp := by
      show θA (a2Mat 4) = θA (bA1 autXp)
      rw [a2Mat_four, adj_autXp_eq]
    have hm : gOf (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j)) xMinus =
        (θA.comp bA1) autXm := by
      show θA (a2Mat 5) = θA (bA1 autXm)
      rw [a2Mat_five, adj_autXm_eq]
    have hga : evalW (gOf (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j))) (gluingA k) =
        θB (c2Mat 5) := by
      rw [evalW_gluingA_map (θA.comp bA1) _ hp hm k, ← ha]
      show θA (bA1 (α autXp)) = θB (c2Mat 5)
      rw [hα' autXp, c2Mat_five, adj_autXp_eq]
    have hgb : evalW (gOf (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j))) (gluingB k) =
        θB (c2Mat 6) := by
      rw [evalW_gluingB_map (θA.comp bA1) _ hp hm k, ← hb]
      show θA (bA1 (α autXm)) = θB (c2Mat 6)
      rw [hα' autXm, c2Mat_six, adj_autXm_eq]
    have hrels : RelsHold (gOf (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j))) (v6aWords k) :=
      relsHold_v6Glued _ _ hrelA hrelC (gluingA k) (gluingB k) hga hgb (hcomm _ m0p _ m2p)
        (hcomm _ m0p _ m3p) (hcomm _ m0m _ m2p) (hcomm _ m0m _ m3p)
    have h9 := hC k hk _ hrels 9
    have h9' : θA (bA1 xpS) = θA (bA1 1) := by
      have e : gOf (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j)) 9 = θA (bA1 xpS) := by
        show θA (a2Mat 4) = _
        rw [a2Mat_four]
      rw [e] at h9
      rw [h9, map_one, map_one]
    exact adj_xpS_ne_one (hιA (a₁ := xpS) (a₂ := 1) h9')

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3Z
