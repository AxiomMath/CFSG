module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelH0

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

section Main

variable {G : Type} [Group G] [Finite G]

theorem relIndex_autOn_seed {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (MulAut V)} (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    {Fs : Subgroup (MulAut V)} (hseed : DelSeed R V (Lc i) Fs) :
    (autOn (baum R) V).relIndex (Fs ⊔ autOn (baum R) V) = 3 := by
  have hX := ctx.hX
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hfin : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) DFunLike.coe_injective
  have hS2 : IsPGroup 2 (baum R) := ctx.setting.sylow.2.1.to_le inf_le_left
  have hDp : IsPGroup 2 (autOn (baum R) V) := by
    rw [autOn_eq_map_conjNormal V]
    exact hS2.map _
  exact relIndex_sup_seed hseed.card hDp hseed.normalized

theorem delMinPImageProp
    : DelMinPImageProp := by
  intro G _ _ R M V n F _ r Lc ctx i Fs P _ _ hseed _ hmin _
  refine ⟨?_⟩
  have hX := ctx.hX
  have hS := ctx.setting
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hbridge := even_SL2_original_bridge hS ctx.comps
  have hDmap : autOn (baum R) V = (baum R).map (MulAut.conjNormal (H := V)) :=
    autOn_eq_map_conjNormal V _
  have hDP : autOn (baum R) V ≤ autOn P V := autOn_le_autOn V hmin.S_le
  have hPN : autOn P V ≤ Fs ⊔ autOn (baum R) V :=
    (autOn_le_autOn V hmin.le).trans (autOn_delH0 ctx i hseed.le).le
  have hne : autOn P V ≠ autOn (baum R) V := by
    intro heq
    apply hmin.not_le
    intro x hx
    have hρx : MulAut.conjNormal (H := V) x ∈ autOn (baum R) V := by
      rw [← heq, autOn_eq_map_conjNormal V]
      exact Subgroup.mem_map_of_mem _ hx
    rw [hDmap] at hρx
    obtain ⟨s, hs, hsx⟩ := hρx
    have hk : s⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
      rw [← ker_conjNormal hX, MonoidHom.mem_ker, map_mul, map_inv, hsx, inv_mul_cancel]
    have hkM : s⁻¹ * x ∈ M := hbridge.C0_le_M ⟨Subgroup.mem_top _, hk⟩
    have hsM : s ∈ M := hS.max.1 ((inf_le_left : baum R ≤ R) hs)
    have hx' : x = s * (s⁻¹ * x) := by group
    rw [hx']
    exact M.mul_mem hsM hkM
  have h1 : (autOn (baum R) V).relIndex (autOn P V) * (autOn P V).relIndex
      (Fs ⊔ autOn (baum R) V) = (autOn (baum R) V).relIndex (Fs ⊔ autOn (baum R) V) :=
    Subgroup.relIndex_mul_relIndex _ _ _ hDP hPN
  rw [relIndex_autOn_seed ctx i hseed] at h1
  rcases (Nat.dvd_prime Nat.prime_three).1 (Dvd.intro _ h1) with h | h
  · exact absurd (le_antisymm (Subgroup.relIndex_eq_one.1 h) hDP) hne
  · have h2 : (autOn P V).relIndex (Fs ⊔ autOn (baum R) V) = 1 := by
      rw [h] at h1
      omega
    exact le_antisymm hPN (Subgroup.relIndex_eq_one.1 h2)

end Main

end CFSG.QuasithinUnique.Setup.Lift
