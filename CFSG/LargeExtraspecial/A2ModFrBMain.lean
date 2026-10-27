module

public import CFSG.LargeExtraspecial.A2ModFrBGen
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.LargeExtraspecial.A2ModSqueeze

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod.FrB

open Module CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.RankThree.OrthogonalInvolutions CFSG.Blueprint

section Lower

variable {X : Type} [Group X] [Finite X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem two_mul_le_finrank_commSpaceOf_top {n : ℕ}
    (hL : LieModel X .POmegaMinus n 2 1) (hρ : Function.Injective ρ) :
    2 * n ≤ finrank (ZMod 2) (commSpaceOf ρ ⊤) := by
  obtain ⟨hn, hcard⟩ := Ord.card_of_lieModel_POmegaMinus hL
  have hpos : 0 < 2 * n := by omega
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega)
    (by omega)
  have hp1 : p ∣ 2 ^ n + 1 := (hp.dvd_add_one_iff hpos n).mpr
    ⟨dvd_refl _, fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)⟩
  have hdvd : p ∣ Nat.card X := by
    rw [hcard, Ord.ordTwistedD_two_eq (by omega)]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hp1 _) _
  have : Fact p.Prime := ⟨hp.prime⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hgp : ρ g ^ p = 1 := by rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  have hne : ρ g ≠ 1 := by
    intro h
    have h1 : g = 1 := hρ (h.trans (map_one ρ).symm)
    rw [h1, orderOf_one] at hg
    exact hp.prime.one_lt.ne hg
  have h1 := dvd_two_pow_finrank_commSpace_sub_one hp.prime (hp.ne_two hpos) hgp
  have h2 := (hp.dvd_sub_one_iff hpos _).mp h1
  have h3 := Nat.le_of_dvd (one_le_finrank_commSpace hne) h2
  exact h3.trans (Submodule.finrank_mono (commSpace_le_commSpaceOf ρ (Subgroup.mem_top g)))

end Lower

section Model

variable {X : Type} [Group X] {n : ℕ} {K : Type} [Field K] [Finite K] {b c : K}

theorem lieModel_of_spin (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) (Ψ : spinGroup (quadMinus n K b c) →* X)
    (hsurj : Function.Surjective Ψ) (hker : Ψ.ker ≤ Subgroup.center _)
    (hZ : Subgroup.center X = ⊥) : LieModel X .POmegaMinus n 2 1 := by
  have hkerZ : Ψ.ker = Subgroup.center _ := by
    refine le_antisymm hker fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have : Ψ z ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := hsurj g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k]
    rwa [hZ, Subgroup.mem_bot] at this
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaMinus n 2 1 :=
    ⟨Nat.prime_two, le_rfl, hn⟩
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hkerZ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Ψ hsurj))
    (Or.inl ⟨by decide, statedClassicalModel_spin_quadMinus hadm (by rw [hK]; norm_num) hirr⟩)

end Model

section Upper

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}
  {n : ℕ} {K : Type} [Field K] [Finite K] {b c : K}

noncomputable abbrev longSub (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) (Ψ : spinGroup (quadMinus n K b c) →* X) : Subgroup X :=
  (Ψ.comp (leviZ n b c hn hirr hK)).range ⊔ Subgroup.zpowers (Ψ (nodeA b c hn)) ⊔
    Subgroup.zpowers (Ψ (nodeB b c hn))

theorem finrank_commSpaceOf_top_le_add_two (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)
    (Ψ : spinGroup (quadMinus n K b c) →* X) (hsurj : Function.Surjective Ψ)
    (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D) (hA : A2Action D Q ρ)
    (hmem : ∀ {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool), Ψ (lr n b c hij s t) ∈ D) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤
      finrank (ZMod 2) (commSpaceOf ρ (longSub hn hirr hK Ψ)) + 2 := by
  have h2 := two_eq_zero_of_card hK
  have hcls : ∀ x ∈ D, ∀ g : X, g * x * g⁻¹ ∈ D := fun x hx g => hDc g x hx
  set H := longSub hn hirr hK Ψ
  have htop : H ⊔ Subgroup.zpowers (Ψ (extra hn hirr planeOne)) ⊔
      Subgroup.zpowers (Ψ (extra hn hirr planeTwo)) = ⊤ := by
    have e : (genB hn hirr hK).map Ψ = H ⊔ Subgroup.zpowers (Ψ (extra hn hirr planeOne)) ⊔
        Subgroup.zpowers (Ψ (extra hn hirr planeTwo)) := by
      simp only [genB, H, longSub, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.range_comp]
    rw [← e, genB_eq_top, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hsurj]
  have hδ : Ψ (xδ (b := b) (c := c) hn) ∈ H := by
    have h := Subgroup.mem_map_of_mem Ψ (xδ_mem hn hirr hK)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_comp] at h
    exact Subgroup.mem_sup_left h
  have hextra : ∀ p : Fin 2 → K, Ψ (extra hn hirr p) ∈ D := fun p =>
    map_conj_mem Ψ hcls (hmem _ _ _) _
  have hcoll : ∀ p : Fin 2 → K, Ψ (extra hn hirr p) * Ψ (xδ hn) ∈ D := fun p => by
    rw [← map_mul, extra_mul_xδ hn hirr h2]
    exact map_conj_mem Ψ hcls (hmem _ _ _) _
  have e1 := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear (hextra planeOne)
    (hmem _ _ _) hδ (hcoll planeOne)
  have e2 := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear
    (H := H ⊔ Subgroup.zpowers (Ψ (extra hn hirr planeOne))) (hextra planeTwo)
    (hmem _ _ _) (Subgroup.mem_sup_left hδ) (hcoll planeTwo)
  rw [htop] at e2
  omega

theorem finrank_commSpaceOf_top_le_two_mul (hn : 6 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)
    (Ψ : spinGroup (quadMinus n K b c) →* X) (hsurj : Function.Surjective Ψ)
    (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D) (hA : A2Action D Q ρ) {i₀ j₀ : Fin (n - 1)}
    (h₀ : i₀ ≠ j₀) (hmem : Ψ (lr n b c h₀ true false) ∈ D) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 2 * n := by
  have hcls : ∀ x ∈ D, ∀ g : X, g * x * g⁻¹ ∈ D := fun x hx g => hDc g x hx
  have hall := fun {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) =>
    map_lr_mem Ψ hcls (by omega) hirr hK h₀ hmem hij s t
  have h := finrank_commSpaceOf_top_le_add_two (by omega) hirr hK Ψ hsurj hDc hA hall
  have hL := (isLeviNode (by omega) hirr hK Ψ hcls hall).finrank_commSpaceOf_eq hA (by omega)
  rw [longSub, hL] at h
  omega

end Upper

end CFSG.LargeExtraspecial.A2Mod.FrB
