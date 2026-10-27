module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25E7
public import CFSG.ClassicalInvolution.Asc77.AscC5O10

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C5O (Om5Data Om5Centerless Om5InvFixFour Om5Interchange Om5ZSwap
  Om5USwapNotZ Om5ExcClass ModelFacts TwinShare M8GFacts Om5TwinComm Om5TwinCommSwap HasBigFix)
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.ExactLayer (isPGroup_zpowers_of_sq_eq_one)
open scoped commutatorElement


section Main

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Swaps
variable {τ σ : G}

theorem comm_mem_hInf_fix (hM : ModelFacts)
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) {x y : G}
    (hxS : x ∈ (S : Subgroup G)) (hyS : y ∈ (S : Subgroup G))
    (hxa : x * a = a * x) (hxz : x * z = z * x) (hxK : conjSub x K = K)
    (hya : y * a = a * y) (hyz : y * z = z * y) (hyK : conjSub y K = K) :
    x * y * x⁻¹ * y⁻¹ ∈ hSub D.ctx.hΩ a τ D.τC ⊓ hSub D.ctx.hΩ (a * z) σ D.σC := by
  classical
  have C := D.ctx
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaGen Ω := C.hΩ
  obtain ⟨hMa, hMaz⟩ := C.twinM_le
  obtain ⟨A₁, A₁', A₂, A₂', ⟨z₁, a₁, b₁, z₂, a₂, b₂, TS⟩, hA₁, hA₂, -, -⟩ :=
    C.exists_twinShareQ hMa hMaz
  have hcA : ∀ v : G, v * a = a * v → v * z = z * v →
      v ∈ Subgroup.centralizer ({a} : Set G) ∧ v ∈ Subgroup.centralizer ({a * z} : Set G) := by
    intro v hva hvz
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr hva,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc v * (a * z) = (v * a) * z := by group
      _ = a * (v * z) := by rw [hva]; group
      _ = a * z * v := by rw [hvz]; group
  obtain ⟨hxCa, hxCaz⟩ := hcA x hxa hxz
  obtain ⟨hyCa, hyCaz⟩ := hcA y hya hyz
  have hK'of : ∀ v : G, v * z = z * v → conjSub v K = K → conjSub v K' = K' := by
    intro v hvz hvK
    have hvz' : v * z * v⁻¹ = z := by rw [hvz]; group
    rcases P25S.conjSub_pair_of_central hs hvz' with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd (hvK.symm.trans h1) hs.hne.symm
  have hxK' := hK'of x hxz hxK
  have hyK' := hK'of y hyz hyK
  have hMv : ∀ v : G, v * a = a * v → conjSub v K = K → conjSub v K' = K' →
      ∀ m ∈ twinM a K K', v * m * v⁻¹ ∈ twinM a K K' := by
    intro v hva hvK hvK' m hm
    have hva' : v * a * v⁻¹ = a := by rw [hva]; group
    have h1 : conjSub v (TwinADescent.coreAt a K) = TwinADescent.coreAt a K := by
      rw [conjSub_coreAt_gen, hva', hvK]
    have h2 : conjSub v (TwinADescent.coreAt a K') = TwinADescent.coreAt a K' := by
      rw [conjSub_coreAt_gen, hva', hvK']
    have h3 : conjSub v (twinM a K K') = twinM a K K' := by
      unfold twinM
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, h1, h2]
    have : v * m * v⁻¹ ∈ conjSub v (twinM a K K') := ⟨m, hm, rfl⟩
    rwa [h3] at this
  have hxXa : conjSub x (layerX Ω a) = layerX Ω a := conjSub_layerX_of_mem hΩ hxCa
  have hxXaz : conjSub x (layerX Ω (a * z)) = layerX Ω (a * z) := conjSub_layerX_of_mem hΩ hxCaz
  have hyXa : conjSub y (layerX Ω a) = layerX Ω a := conjSub_layerX_of_mem hΩ hyCa
  have hyXaz : conjSub y (layerX Ω (a * z)) = layerX Ω (a * z) := conjSub_layerX_of_mem hΩ hyCaz
  have hcCa : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
    mul_mem (mul_mem (mul_mem hxCa hyCa) (inv_mem hxCa)) (inv_mem hyCa)
  have hcCaz : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({a * z} : Set G) :=
    mul_mem (mul_mem (mul_mem hxCaz hyCaz) (inv_mem hxCaz)) (inv_mem hyCaz)
  have hcXa : conjSub (x * y * x⁻¹ * y⁻¹) (layerX Ω a) = layerX Ω a :=
    conjSub_layerX_of_mem hΩ hcCa
  have hcXaz : conjSub (x * y * x⁻¹ * y⁻¹) (layerX Ω (a * z)) = layerX Ω (a * z) :=
    conjSub_layerX_of_mem hΩ hcCaz
  have hcS : x * y * x⁻¹ * y⁻¹ ∈ (S : Subgroup G) :=
    mul_mem (mul_mem (mul_mem hxS hyS) (inv_mem hxS)) (inv_mem hyS)
  obtain ⟨n, hn⟩ := S.isPGroup' ⟨x * y * x⁻¹ * y⁻¹, hcS⟩
  have hcn : (x * y * x⁻¹ * y⁻¹) ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hord : ∃ n : ℕ, ∀ e : layerBar Ω a,
      (fun e => (C25Y.layerAut (layerX Ω a) hxXa) ((C25Y.layerAut (layerX Ω a) hyXa)
        (((C25Y.layerAut (layerX Ω a) hxXa).symm) (((C25Y.layerAut (layerX Ω a) hyXa).symm) e)))) ^[2 ^ n] e =
        e := by
    refine ⟨n, fun e => ?_⟩
    have hfun : (fun e => (C25Y.layerAut (layerX Ω a) hxXa) ((C25Y.layerAut (layerX Ω a) hyXa)
        (((C25Y.layerAut (layerX Ω a) hxXa).symm) (((C25Y.layerAut (layerX Ω a) hyXa).symm) e)))) =
        ⇑(C25Y.layerAut (layerX Ω a) hcXa) := by
      funext e
      exact (layerAut_comm_apply _ hxXa hyXa hcXa e).symm
    rw [hfun]
    exact layerAut_iterate_eq_id _ hcXa hcn e
  obtain ⟨w, hw1, hw2⟩ := Q8.twinComm TS (C25Y.layerAut (layerX Ω a) hxXa)
    (C25Y.layerAut (layerX Ω a) hyXa) (C25Y.layerAut (layerX Ω (a * z)) hxXaz)
    (C25Y.layerAut (layerX Ω (a * z)) hyXaz) (hA₁ hxCa hxXa hxK) (hA₂ hxCaz hxXaz hxK)
    (hA₁ hyCa hyXa hyK) (hA₂ hyCaz hyXaz hyK)
    (fun m => ⟨⟨x * m * x⁻¹, hMv x hxa hxK hxK' m m.2⟩, rfl, rfl⟩)
    (fun m => ⟨⟨y * m * y⁻¹, hMv y hya hyK hyK' m m.2⟩, rfl, rfl⟩) hord
  have hwa : (w : G) ∈ layerX Ω a := hMa w.2
  have hwaz : (w : G) ∈ layerX Ω (a * z) := hMaz w.2
  have htriv : ∀ (b : G) (hcb : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({b} : Set G))
      (hwb : (w : G) ∈ layerX Ω b) (hMb : twinM a K K' ≤ layerX Ω b)
      (hxb : conjSub x (layerX Ω b) = layerX Ω b) (hyb : conjSub y (layerX Ω b) = layerX Ω b),
      (∀ e, C25Y.layerAut _ hxb (C25Y.layerAut _ hyb ((C25Y.layerAut _ hxb).symm
        ((C25Y.layerAut _ hyb).symm e))) = twinπ Ω b hMb w * e * (twinπ Ω b hMb w)⁻¹) →
      x * y * x⁻¹ * y⁻¹ * (w : G)⁻¹ ∈ trivialOnQuot (layerX Ω b) := by
    intro b hcb hwb hMb hxb hyb hw
    have hcX : conjSub (x * y * x⁻¹ * y⁻¹) (layerX Ω b) = layerX Ω b :=
      conjSub_layerX_of_mem hΩ hcb
    have hwi : conjSub (w : G)⁻¹ (layerX Ω b) = layerX Ω b :=
      conjSub_eq_self_of_mem (inv_mem hwb)
    have hcw : conjSub (x * y * x⁻¹ * y⁻¹ * (w : G)⁻¹) (layerX Ω b) = layerX Ω b := by
      rw [conjSub_mul, hwi, hcX]
    rw [← layerAut_eq_id_iff (layerX Ω b) hcw]
    intro e
    rw [layerAut_mul_apply _ hcX hwi hcw, layerAut_comm_apply _ hxb hyb hcX, hw,
      layerAut_of_mem _ (inv_mem hwb), twinπ_apply]
    have e1 : (QuotientGroup.mk ⟨(w : G)⁻¹, inv_mem hwb⟩ : layerBar Ω b) =
        (QuotientGroup.mk ⟨(w : G), hwb⟩)⁻¹ := by
      rw [← QuotientGroup.mk_inv]
      rfl
    rw [e1]
    group
  exact D.mem_hInf_of_triv hM hcCa hcCaz hwa hwaz
    (htriv a hcCa hwa hMa hxXa hyXa hw1) (htriv (a * z) hcCaz hwaz hMaz hxXaz hyXaz hw2)

theorem comm_mem_hInf_swap (hM : ModelFacts)
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) {g y : G}
    (hgS : g ∈ (S : Subgroup G)) (hyS : y ∈ (S : Subgroup G))
    (hga : g * a * g⁻¹ = a * z) (hgz : g * z = z * g) (hgK : conjSub g K = K)
    (hya : y * a = a * y) (hyz : y * z = z * y) (hyK : conjSub y K = K) :
    g * y * g⁻¹ * y⁻¹ ∈ hSub D.ctx.hΩ a τ D.τC ⊓ hSub D.ctx.hΩ (a * z) σ D.σC := by
  classical
  have C := D.ctx
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaGen Ω := C.hΩ
  obtain ⟨hMa, hMaz⟩ := C.twinM_le
  obtain ⟨A₁, A₁', A₂, A₂', ⟨z₁, a₁, b₁, z₂, a₂, b₂, TS⟩, hA₁, hA₂, hS₁, hS₂⟩ :=
    C.exists_twinShareQ hMa hMaz
  have hgz' : g * z * g⁻¹ = z := by rw [hgz]; group
  have hga' : g * (a * z) * g⁻¹ = a := by
    calc g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) := by group
      _ = a := by rw [hga, hgz', C.mul_z_mul_z]
  have hK'of : ∀ v : G, v * z * v⁻¹ = z → conjSub v K = K → conjSub v K' = K' := by
    intro v hvz hvK
    rcases P25S.conjSub_pair_of_central hs hvz with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd (hvK.symm.trans h1) hs.hne.symm
  have hgK' := hK'of g hgz' hgK
  have hyz' : y * z * y⁻¹ = z := by rw [hyz]; group
  have hyK' := hK'of y hyz' hyK
  have hyCa : y ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hya
  have hyCaz : y ∈ Subgroup.centralizer ({a * z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc y * (a * z) = (y * a) * z := by group
      _ = a * (y * z) := by rw [hya]; group
      _ = a * z * y := by rw [hyz]; group
  have hyXa : conjSub y (layerX Ω a) = layerX Ω a := conjSub_layerX_of_mem hΩ hyCa
  have hyXaz : conjSub y (layerX Ω (a * z)) = layerX Ω (a * z) := conjSub_layerX_of_mem hΩ hyCaz
  have hMv : ∀ (v b : G), v * a * v⁻¹ = b → TwinADescent.coreAt b K = TwinADescent.coreAt a K →
      TwinADescent.coreAt b K' = TwinADescent.coreAt a K' → conjSub v K = K → conjSub v K' = K' →
      ∀ m ∈ twinM a K K', v * m * v⁻¹ ∈ twinM a K K' := by
    intro v b hvb hb hb' hvK hvK' m hm
    have h1 : conjSub v (TwinADescent.coreAt a K) = TwinADescent.coreAt a K := by
      rw [conjSub_coreAt_gen, hvb, hvK, hb]
    have h2 : conjSub v (TwinADescent.coreAt a K') = TwinADescent.coreAt a K' := by
      rw [conjSub_coreAt_gen, hvb, hvK', hb']
    have h3 : conjSub v (twinM a K K') = twinM a K K' := by
      unfold twinM
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, h1, h2]
    have : v * m * v⁻¹ ∈ conjSub v (twinM a K K') := ⟨m, hm, rfl⟩
    rwa [h3] at this
  have hya' : y * a * y⁻¹ = a := by rw [hya]; group
  have hgyCaz : g * y * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h := Subgroup.mem_centralizer_singleton_iff.mp hyCaz
    calc g * y * g⁻¹ * a = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * (y * (a * z)) * g⁻¹ := by
          rw [show g⁻¹ * a * g = a * z by
            calc g⁻¹ * a * g = g⁻¹ * (g * (a * z) * g⁻¹) * g := by rw [hga']
              _ = a * z := by group]
      _ = g * ((a * z) * y) * g⁻¹ := by rw [h]
      _ = (g * (a * z) * g⁻¹) * (g * y * g⁻¹) := by group
      _ = a * (g * y * g⁻¹) := by rw [hga']
  have hgyCa : g * y * g⁻¹ ∈ Subgroup.centralizer ({a * z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h := Subgroup.mem_centralizer_singleton_iff.mp hyCa
    calc g * y * g⁻¹ * (a * z) = g * (y * (g⁻¹ * (a * z) * g)) * g⁻¹ := by group
      _ = g * (y * a) * g⁻¹ := by
          rw [show g⁻¹ * (a * z) * g = a by
            calc g⁻¹ * (a * z) * g = g⁻¹ * (g * a * g⁻¹) * g := by rw [hga]
              _ = a := by group]
      _ = g * (a * y) * g⁻¹ := by rw [h]
      _ = (g * a * g⁻¹) * (g * y * g⁻¹) := by group
      _ = a * z * (g * y * g⁻¹) := by rw [hga]
  have hcCa : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
    mul_mem hgyCaz (inv_mem hyCa)
  have hcCaz : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({a * z} : Set G) :=
    mul_mem hgyCa (inv_mem hyCaz)
  have hyia : conjSub y⁻¹ (layerX Ω a) = layerX Ω a := conjSub_layerX_of_mem hΩ (inv_mem hyCa)
  have hyiaz : conjSub y⁻¹ (layerX Ω (a * z)) = layerX Ω (a * z) :=
    conjSub_layerX_of_mem hΩ (inv_mem hyCaz)
  have hgyXa : conjSub (g * y * g⁻¹) (layerX Ω a) = layerX Ω a :=
    conjSub_layerX_of_mem hΩ hgyCaz
  have hgyXaz : conjSub (g * y * g⁻¹) (layerX Ω (a * z)) = layerX Ω (a * z) :=
    conjSub_layerX_of_mem hΩ hgyCa
  have hcXa : conjSub (g * y * g⁻¹ * y⁻¹) (layerX Ω a) = layerX Ω a :=
    conjSub_layerX_of_mem hΩ hcCa
  have hcS : g * y * g⁻¹ * y⁻¹ ∈ (S : Subgroup G) :=
    mul_mem (mul_mem (mul_mem hgS hyS) (inv_mem hgS)) (inv_mem hyS)
  obtain ⟨n, hn⟩ := S.isPGroup' ⟨g * y * g⁻¹ * y⁻¹, hcS⟩
  have hcn : (g * y * g⁻¹ * y⁻¹) ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hfun : ∀ e : layerBar Ω a, C25Y.layerAut (layerX Ω a) hcXa e =
      layerIso hΩ hga' (C25Y.layerAut (layerX Ω (a * z)) hyXaz
        ((layerIso hΩ hga').symm ((C25Y.layerAut (layerX Ω a) hyXa).symm e))) := by
    intro e
    rw [layerAut_mul_apply _ hgyXa hyia, ← layerAut_symm_apply _ hyXa hyia,
      layerAut_conj hΩ hga' hyXaz hgyXa]
  have hord : ∃ n : ℕ, ∀ e : layerBar Ω a,
      (fun e => layerIso hΩ hga' (C25Y.layerAut (layerX Ω (a * z)) hyXaz
        ((layerIso hΩ hga').symm ((C25Y.layerAut (layerX Ω a) hyXa).symm e)))) ^[2 ^ n] e = e := by
    refine ⟨n, fun e => ?_⟩
    have hfun' : (fun e => layerIso hΩ hga' (C25Y.layerAut (layerX Ω (a * z)) hyXaz
        ((layerIso hΩ hga').symm ((C25Y.layerAut (layerX Ω a) hyXa).symm e)))) =
        ⇑(C25Y.layerAut (layerX Ω a) hcXa) := by
      funext e
      exact (hfun e).symm
    rw [hfun']
    exact layerAut_iterate_eq_id _ hcXa hcn e
  obtain ⟨w, hw1, hw2⟩ := Q8.twinCommSwap TS (layerIso hΩ hga) (layerIso hΩ hga')
    (C25Y.layerAut (layerX Ω a) hyXa) (C25Y.layerAut (layerX Ω (a * z)) hyXaz)
    (hS₁ hga hgK) (hS₂ hga' hgK) (hA₁ hyCa hyXa hyK) (hA₂ hyCaz hyXaz hyK)
    (fun m => ⟨⟨g * m * g⁻¹, hMv g (a * z) hga (C.coreAt_az.1) (C.coreAt_az.2) hgK hgK' m m.2⟩,
      rfl, rfl⟩)
    (fun m => ⟨⟨y * m * y⁻¹, hMv y a hya' rfl rfl hyK hyK' m m.2⟩, rfl, rfl⟩) hord
  have hwa : (w : G) ∈ layerX Ω a := hMa w.2
  have hwaz : (w : G) ∈ layerX Ω (a * z) := hMaz w.2
  refine D.mem_hInf_of_triv hM hcCa hcCaz hwa hwaz
    (mul_inv_mem_trivialOnQuot _ hwa (conjSub_layerX_of_mem hΩ hcCa) fun e => ?_)
    (mul_inv_mem_trivialOnQuot _ hwaz (conjSub_layerX_of_mem hΩ hcCaz) fun e => ?_)
  · rw [hfun e, hw1]
    rfl
  · rw [layerAut_mul_apply _ hgyXaz hyiaz, ← layerAut_symm_apply _ hyXaz hyiaz,
      layerAut_conj hΩ hga hyXa hgyXaz, hw2]
    rfl

theorem comm_mem_hBig (hM : ModelFacts)
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) (hτS : τ ∈ (S : Subgroup G)) :
    ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈
      hBig D.ctx.hΩ z a τ σ D.τC D.σC := by
  classical
  have C := D.ctx
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaGen Ω := C.hΩ
  have hτH₀ : τ ∈ hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC :=
    ⟨mem_hSub_self hΩ D.τC, le_hSub_layer hΩ D.σC D.τX⟩
  have hH₀ : hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC ≤ hBig hΩ z a τ σ D.τC D.σC :=
    le_mulSub_left _
  have hSz : ∀ v ∈ (S : Subgroup G), v * z * v⁻¹ = z := by
    intro v hv
    rw [C.hyp.hzS v hv]
    group
  set N₀ := (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G) with hN₀
  have hNK : ∀ v ∈ N₀, conjSub v K = K := fun v hv => conjSub_eq_of_mem_normalizer hv.2
  have hfix : ∀ v ∈ N₀, v * a * v⁻¹ = a → v * a = a * v := by
    intro v _ h
    calc v * a = (v * a * v⁻¹) * v := by group
      _ = a * v := by rw [h]
  have hcomm : ∀ x ∈ N₀, ∀ y ∈ N₀, x * a * x⁻¹ = a ∨ y * a * y⁻¹ = a →
      x * y * x⁻¹ * y⁻¹ ∈ hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC := by
    intro x hx y hy hxy
    rcases C.hconj x hx.1 with hxa | hxa <;> rcases C.hconj y hy.1 with hya | hya
    · exact D.comm_mem_hInf_fix hM hx.1 hy.1 (hfix x hx hxa) (C.hyp.hzS x hx.1) (hNK x hx)
        (hfix y hy hya) (C.hyp.hzS y hy.1) (hNK y hy)
    ·
      have h := D.comm_mem_hInf_swap hM hy.1 hx.1 hya (C.hyp.hzS y hy.1) (hNK y hy)
        (hfix x hx hxa) (C.hyp.hzS x hx.1) (hNK x hx)
      have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem h
    · exact D.comm_mem_hInf_swap hM hx.1 hy.1 hxa (C.hyp.hzS x hx.1) (hNK x hx)
        (hfix y hy hya) (C.hyp.hzS y hy.1) (hNK y hy)
    · rcases hxy with h | h
      · rw [h] at hxa
        exact absurd (mul_left_cancel (a := a) (hxa.symm.trans (mul_one a).symm)) C.hz1
      · rw [h] at hya
        exact absurd (mul_left_cancel (a := a) (hya.symm.trans (mul_one a).symm)) C.hz1
  have hcommN : ∀ x ∈ N₀, ∀ y ∈ N₀, x * y * x⁻¹ * y⁻¹ ∈ hBig hΩ z a τ σ D.τC D.σC := by
    intro x hx y hy
    by_cases hxa : x * a * x⁻¹ = a
    · exact hH₀ (hcomm x hx y hy (Or.inl hxa))
    by_cases hya : y * a * y⁻¹ = a
    · exact hH₀ (hcomm x hx y hy (Or.inr hya))
    have hxa' : x * a * x⁻¹ = a * z := (C.hconj x hx.1).resolve_left hxa
    have hya' : y * a * y⁻¹ = a * z := (C.hconj y hy.1).resolve_left hya
    have hyx : y * x⁻¹ ∈ N₀ := mul_mem hy (inv_mem hx)
    have hyxa : (y * x⁻¹) * a * (y * x⁻¹)⁻¹ = a := by
      have h1 : x⁻¹ * a * x = a * z := by
        have hz' : x⁻¹ * z * x = z := by
          have := hSz x⁻¹ (inv_mem hx.1)
          rwa [inv_inv] at this
        calc x⁻¹ * a * x = x⁻¹ * (x * a * x⁻¹ * z⁻¹) * x := by rw [hxa']; group
          _ = a * (x⁻¹ * z * x)⁻¹ := by group
          _ = a * z := by rw [hz', inv_eq_of_mul_eq_one_right C.hz2]
      calc (y * x⁻¹) * a * (y * x⁻¹)⁻¹ = y * (x⁻¹ * a * x) * y⁻¹ := by group
        _ = y * (a * z) * y⁻¹ := by rw [h1]
        _ = (y * a * y⁻¹) * (y * z * y⁻¹) := by group
        _ = a := by rw [hya', hSz y hy.1, C.mul_z_mul_z]
    have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹) * x⁻¹ * (y * x⁻¹)⁻¹ := by group
    rw [e]
    exact hH₀ (hcomm x hx _ hyx (Or.inr hyxa))
  refine comm_mem_of_factor (fun s hs q hq => conj_mem_hBig hM D (hSz s hs) hq) inf_le_left
    (fun s hsS => ?_) hcommN
  by_cases hsK : conjSub s K = K
  · exact ⟨s, ⟨hsS, Generic.mem_normalizer_of_conjSub_eq hsK⟩, 1, one_mem _, (mul_one s).symm⟩
  · have hsK' : conjSub s K = K' := by
      rcases P25S.conjSub_pair_of_central hs (hSz s hsS) with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 hsK
      · exact h1
    have hsK'' : conjSub s K' = K := by
      rcases P25S.conjSub_pair_of_central hs (hSz s hsS) with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 hsK
      · exact h2
    refine ⟨s * τ, ⟨mul_mem hsS hτS, Generic.mem_normalizer_of_conjSub_eq ?_⟩, τ⁻¹,
      inv_mem (hH₀ hτH₀), by group⟩
    rw [conjSub_mul, D.τK, hsK'']

end Swaps

end Main


section Final


theorem _root_.CFSG.ClassicalInvolution.Q8P.Asc77.P25R.p25_endL_proved : P25_EndL := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a h4 hcl hbad hbad' h5 h5'
  have FD := fourData_of_four hyp h4 hcl hbad
  have C : Ctx Ω K K' W S R R' z t u₁ u₂ a :=
    ⟨hyp, FD.haA, FD.ha2, FD.ha1, FD.haz, FD.hconj, FD.hA0, hbad, hbad', h5, h5',
      TwinThmE.t4Supply_proved⟩
  have hM : ModelFacts := Q3T8.Asc77.C5O.modelFacts_proved
  rcases C.exists_swaps hM with ⟨τ, σ, D, hτS⟩ | ⟨τ, σ, D, hτS⟩
  · exact D.false_of_comm (D.comm_mem_hBig hM hτS) hM
  · exact D.false_of_comm (D.comm_mem_hBig hM hτS) hM

end Final

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL
