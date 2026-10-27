module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangTorusSylowFree

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

structure LangComponentPieces : Prop where
  subnormal : LangSubnormal
  inner : LangComponentsQuasisimple .inner
  suN : LangComponentsQuasisimple .suN
  twoD : LangComponentsQuasisimple .twoD
  exc : LangComponentsQuasisimple .exc

section Frame

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem localDeltaIn_eq_bot_of_frameBalanced_plane {M : Type*} [Group M] {Γ E : Subgroup M}
    (hbal : FrameBalanced p Γ E) (hp : p.Prime) (D₁ : Subgroup ↥Γ)
    (hE : ∀ x ∈ D₁, (x : M) ∈ E) (hpow : ∀ x ∈ D₁, x ^ p = 1) (hcard : Nat.card D₁ = p ^ 2)
    {H : Subgroup (MulAut ↥Γ)} (hH : innerAut ↥Γ ≤ H) :
    localDeltaIn p H (D₁.map (MulAut.conj : ↥Γ →* MulAut ↥Γ)) = ⊥ :=
  hbal D₁ hE hpow (by
    rw [hcard]
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)) H hH

theorem localDeltaIn_eq_bot_of_langSetup_plane_rigid (S : LangSetup τ L p) (hrig : SetupRigid S)
    (hcp : LangComponentPieces)
    (hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ))
    {D : Subgroup (MulAut ↥S.Γ)}
    (hD₀c : Nat.card (D.comap (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ)) = p ^ 2)
    (hDin : D ≤ innerAut ↥S.Γ)
    (hD₀p : ∀ x ∈ D.comap (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ), x ^ p = 1)
    (hpl : ∃ h ∈ S.Γ, ((D.comap (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ)).map S.Γ.subtype).map
      (MulAut.conj h).toMonoidHom ≤ S.E)
    {H : Subgroup (MulAut ↥S.Γ)} (hH : innerAut ↥S.Γ ≤ H) : localDeltaIn p H D = ⊥ := by
  classical
  have hp := S.hp
  have : Fact p.Prime := ⟨hp⟩
  have := S.finite_Γ
  set D₀ : Subgroup ↥S.Γ := D.comap (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) with hD₀
  have hDD : D₀.map (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) = D := Subgroup.map_comap_eq_self hDin
  obtain ⟨h, hhΓ, hhE⟩ := hpl
  set k : ↥S.Γ := ⟨h, hhΓ⟩ with hk
  set D₁ : Subgroup ↥S.Γ := D₀.map (MulAut.conj k).toMonoidHom with hD₁
  have hD₁E : ∀ x ∈ D₁, (x : ModGL τ L) ∈ S.E := by
    rintro _ ⟨x, hx, rfl⟩
    exact hhE ⟨(x : ModGL τ L), ⟨x, hx, rfl⟩, rfl⟩
  have hD₁p : ∀ x ∈ D₁, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hD₀p x hx, map_one]
  have hD₁c : Nat.card D₁ = p ^ 2 := by
    rw [hD₁, Subgroup.card_map_of_injective (MulAut.conj k).injective, hD₀c]
  refine localDeltaIn_eq_bot_of_map_conj (c := MulAut.conj k) (hH ⟨k, rfl⟩) ?_
  have hmap : D.map (MulAut.conj (MulAut.conj k)).toMonoidHom =
      D₁.map (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) := by
    conv_lhs => rw [← hDD]
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hmap]
  exact localDeltaIn_eq_bot_of_frameBalanced_plane
    (frameBalanced_of_langSetup S hrig hcp.subnormal hcp.inner hcp.suN hcp.twoD hcp.exc hinj)
    hp D₁ hD₁E hD₁p hD₁c hH

theorem innerPlaneBalance_of_langSetup_rigid (S : LangSetup τ L p)
    (hsyl : ∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ)
    (hrig : SetupRigid S) (hcp : LangComponentPieces)
    (hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ)) :
    InnerPlaneBalance p ↥S.Γ := by
  classical
  have hp := S.hp
  have : Fact p.Prime := ⟨hp⟩
  have := S.finite_Γ
  intro D hDin hDe hDc H hH
  set D₀ : Subgroup ↥S.Γ := D.comap (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) with hD₀
  have hDD : D₀.map (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) = D := Subgroup.map_comap_eq_self hDin
  have hD₀c : Nat.card D₀ = p ^ 2 := by
    rw [← hDc, ← hDD, Subgroup.card_map_of_injective hinj]
  have hD₀p : ∀ x ∈ D₀, x ^ p = 1 := by
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hDe.2 _ hx
  obtain ⟨h, hhΓ, hhE⟩ := S.exists_conj_le hsyl (F := D₀.map S.Γ.subtype)
    (Subgroup.map_subtype_le _)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hD₀p x hx, map_one])
  exact localDeltaIn_eq_bot_of_langSetup_plane_rigid S hrig hcp hinj hD₀c hDin hD₀p
    ⟨h, hhΓ, hhE⟩ hH

end Frame

end CFSG.HardMathSupport.Timmesfeld.LangTorus
