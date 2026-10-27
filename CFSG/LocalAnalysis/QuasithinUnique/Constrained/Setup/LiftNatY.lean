module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannOrig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

section Helpers

variable {G : Type} [Group G]

theorem oddOrderSubgroup_eq_of_perfect [Finite G] {D : Subgroup G} (hD : Group.IsPerfect ↥D) :
    oddOrderSubgroup D = D := by
  refine le_antisymm (oddOrderSubgroup_le D) ?_
  set N : Subgroup ↥D := (oddOrderSubgroup D).subgroupOf D with hN
  have hDN : D ≤ Subgroup.normalizer (oddOrderSubgroup D : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oddOrderSubgroup D)
  have hNn : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oddOrderSubgroup_le D)).mpr hDN
  have hQ2 : IsPGroup 2 (↥D ⧸ N) := by
    intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oddOrderSubgroup hh
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent (↥D ⧸ N) := hQ2.isNilpotent
  have hsolv : Group.IsSolvable (↥D ⧸ N) := inferInstance
  have := hD
  have hperf : Group.IsPerfect (↥D ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  by_contra hne
  have hN1 : N ≠ ⊤ := fun h => hne fun x hx => by
    have : (⟨x, hx⟩ : ↥D) ∈ N := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  have hnt : Nontrivial (↥D ⧸ N) := QuotientGroup.nontrivial_iff.mpr hN1
  exact Group.IsPerfect.not_isSolvable _ hsolv

theorem oddOrderSubgroup_mono {A B : Subgroup G} (h : A ≤ B) :
    oddOrderSubgroup A ≤ oddOrderSubgroup B :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

variable [Finite G] {V : Subgroup G}

omit [Finite G] in
theorem autOn_rhoPreimage_of_le {P : Subgroup G} (hP : P ≤ Subgroup.normalizer (V : Set G))
    {N : Subgroup (MulAut V)} (hN : N ≤ autOn P V) : autOn (rhoPreimage V P hP N) V = N := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨p, hpN, rfl⟩ := (mem_autOn_iff_rho hP (rhoPreimage_le hP N)).mp hφ
    exact mem_rhoPreimage.mp hpN
  · intro φ hφ
    obtain ⟨p, rfl⟩ := (mem_autOn_self_iff hP).mp (hN hφ)
    exact (mem_autOn_iff_rho hP (rhoPreimage_le hP N)).mpr ⟨p, mem_rhoPreimage.mpr hφ, rfl⟩

omit [Finite G] in
theorem mem_rhoPreimage_top (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    {N : Subgroup (MulAut V)} {x : G} :
    x ∈ rhoPreimage V ⊤ hX N ↔ rho V ⊤ hX ⟨x, Subgroup.mem_top x⟩ ∈ N :=
  mem_rhoPreimage (p := ⟨x, Subgroup.mem_top x⟩)

omit [Finite G] in
theorem rho_top_conj (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) (g x : G) :
    rho V ⊤ hX ⟨g⁻¹ * x * g, Subgroup.mem_top _⟩ =
      (rho V ⊤ hX ⟨g, Subgroup.mem_top g⟩)⁻¹ * rho V ⊤ hX ⟨x, Subgroup.mem_top x⟩ *
        rho V ⊤ hX ⟨g, Subgroup.mem_top g⟩ := by
  have : (⟨g⁻¹ * x * g, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup G)) =
      (⟨g, Subgroup.mem_top g⟩ : ↥(⊤ : Subgroup G))⁻¹ * ⟨x, Subgroup.mem_top x⟩ *
        ⟨g, Subgroup.mem_top g⟩ := rfl
  rw [this, map_mul, map_mul, map_inv]

omit [Finite G] in
theorem map_conj_rhoPreimage (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    (N : Subgroup (MulAut V)) (g : G) :
    (rhoPreimage V ⊤ hX N).map (MulAut.conj g).toMonoidHom =
      rhoPreimage V ⊤ hX (N.map (MulAut.conj (rho V ⊤ hX ⟨g, Subgroup.mem_top g⟩)).toMonoidHom) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_rhoPreimage_top, mem_rhoPreimage_top, Subgroup.mem_map_equiv]
  have h2 : (MulAut.conj (rho V ⊤ hX ⟨g, Subgroup.mem_top g⟩)).symm
      (rho V ⊤ hX ⟨x, Subgroup.mem_top x⟩) =
      (rho V ⊤ hX ⟨g, Subgroup.mem_top g⟩)⁻¹ * rho V ⊤ hX ⟨x, Subgroup.mem_top x⟩ *
        rho V ⊤ hX ⟨g, Subgroup.mem_top g⟩ := MulAut.conj_symm_apply _ _
  rw [h2, ← rho_top_conj hX g x]
  exact Iff.rfl

end Helpers

section Main

theorem natYProp
    : NatYProp := by
  intro G _ _ R M V n F _ r Lc ctx i
  have hS := ctx.setting
  have hX := ctx.hX
  have hbridge := even_SL2_original_bridge hS ctx.comps
  have hbaum := even_SL2_natural_baumann hS ctx.comps ctx.natural
  have hnormV : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ =>
    hX (Subgroup.mem_top x)
  have hDle : ∀ j, Lc j ≤ autOn (⊤ : Subgroup G) V := fun j => (ctx.comps.isComp j).1
  have hperf : ∀ j, Group.IsPerfect ↥(Lc j) := fun j => ⟨(ctx.comps.isComp j).2.2.1⟩
  have himgK : ∀ j, autOn (rhoPreimage V ⊤ hX (Lc j)) V = Lc j := fun j =>
    autOn_rhoPreimage_of_le hX (hDle j)
  have himgY : ∀ j, autOn (oddOrderSubgroup (rhoPreimage V ⊤ hX (Lc j))) V = Lc j := fun j => by
    rw [autOn_oddOrderSubgroup (hnormV _), himgK j]
    exact oddOrderSubgroup_eq_of_perfect (hperf j)
  refine ⟨oddOrderSubgroup_mono le_top, himgY i, ?_, ?_⟩
  ·
    have hSle : autOn (baum R) V ≤ Subgroup.normalizer (Lc i : Set (MulAut V)) := by
      rw [hbaum.baum_eq]
      refine ctx.natural.trans ?_
      rw [hbridge.K_eq, hbridge.K_prod]
      refine iSup_le fun j => ?_
      by_cases hji : j = i
      · subst hji
        exact Subgroup.le_normalizer
      · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (hbridge.commute j i hji)).trans (Subgroup.centralizer_le_normalizer _)
    have hSK : baum R ≤ Subgroup.normalizer (rhoPreimage V ⊤ hX (Lc i) : Set G) := by
      intro s hs
      rw [Subgroup.mem_normalizer_iff]
      intro k
      have hφ : rho V ⊤ hX ⟨s, Subgroup.mem_top s⟩ ∈ autOn (baum R) V :=
        (mem_autOn_iff_rho hX le_top).mpr ⟨⟨s, Subgroup.mem_top s⟩, hs, rfl⟩
      have h1 := Subgroup.mem_normalizer_iff.1 (hSle hφ) (rho V ⊤ hX ⟨k, Subgroup.mem_top k⟩)
      have h2 : rho V ⊤ hX ⟨s * k * s⁻¹, Subgroup.mem_top _⟩ =
          rho V ⊤ hX ⟨s, Subgroup.mem_top s⟩ * rho V ⊤ hX ⟨k, Subgroup.mem_top k⟩ *
            (rho V ⊤ hX ⟨s, Subgroup.mem_top s⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [mem_rhoPreimage_top, mem_rhoPreimage_top, h2]
      exact h1
    exact fun s hs => normalizer_le_normalizer_oddOrderSubgroup _ (hSK hs)
  ·
    intro hYM
    have hYj : ∀ j, oddOrderSubgroup (rhoPreimage V ⊤ hX (Lc j)) ≤ M := by
      intro j
      obtain ⟨t, ht, hconj⟩ := hbridge.transitive i j
      obtain ⟨p, hpR, rfl⟩ := (mem_autOn_iff_rho hX (le_top (a := R))).mp ht
      have hK : rhoPreimage V ⊤ hX (Lc j) =
          (rhoPreimage V ⊤ hX (Lc i)).map (MulAut.conj (p : G)).toMonoidHom := by
        rw [map_conj_rhoPreimage, hconj]
      rw [hK, ← oddOrderSubgroup_map_mulEquiv]
      rintro _ ⟨y, hy, rfl⟩
      have hrM : (p : G) ∈ M := hS.max.1 hpR
      show (p : G) * y * (p : G)⁻¹ ∈ M
      exact M.mul_mem (M.mul_mem hrM (hYM hy)) (M.inv_mem hrM)
    have hLM : oddOrderSubgroup (⊤ : Subgroup G) ≤ M := by
      intro x hx
      have hρx : rho V ⊤ hX ⟨x, Subgroup.mem_top x⟩ ∈ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V :=
        (mem_autOn_iff_rho hX (oddOrderSubgroup_le _)).mpr ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩
      have hautL : autOn (oddOrderSubgroup (⊤ : Subgroup G)) V =
          autOn (⨆ j, oddOrderSubgroup (rhoPreimage V ⊤ hX (Lc j))) V := by
        rw [autOn_iSup_of_le _ fun j => hnormV _, hbridge.K_eq, hbridge.K_prod]
        exact (iSup_congr fun j => (himgY j).symm)
      rw [hautL] at hρx
      obtain ⟨p, hpY, hpρ⟩ := (mem_autOn_iff_rho hX le_top).mp hρx
      have hpM : (p : G) ∈ M := by
        refine (iSup_le fun j => hYj j) hpY
      have hker : (p : G)⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
        have h1 : rho V ⊤ hX (p⁻¹ * ⟨x, Subgroup.mem_top x⟩) = 1 := by
          rw [map_mul, map_inv, hpρ, inv_mul_cancel]
        exact (rho_eq_one_iff hX _).mp h1
      have hkerM : (p : G)⁻¹ * x ∈ M := hbridge.C0_le_M ⟨Subgroup.mem_top _, hker⟩
      have : x = (p : G) * ((p : G)⁻¹ * x) := by group
      rw [this]
      exact M.mul_mem hpM hkerM
    have hRM : R ≤ M := hS.max.1
    have htop : (⊤ : Subgroup G) ≤ M := by
      rw [hbridge.X_eq]
      exact sup_le hLM hRM
    exact absurd (lt_of_lt_of_le hS.max.2.1 htop) (lt_irrefl _)

end Main

end CFSG.QuasithinUnique.Setup.Lift
