module

public import CFSG.ClassicalInvolution.Asc77.AscT8T4
public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75
import CFSG.ClassicalInvolution.Asc77.AscT8T5Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8T3
public import CFSG.ClassicalInvolution.Asc77.AscT8Y6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8T

section Tri

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Hyp51Tri : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (M : Fin 3 → Subgroup G) (x : Fin 3 → G) (R : Fin 3 → Subgroup G),
    AscStand p f Ω (M 0) → (∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) → TriFrame Ω M x R →
      x 2 ∉ Subgroup.closure ({x 0, x 1} : Set G) →
        Hyp51 (Subgroup.closure ({x 0, x 1, x 2} : Set G))

end Tri

section Transfer

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem muAbelian_notE4_transfer {W W' : Subgroup G}
    (e : ↥(muGroup Ω W) ≃* ↥(muGroup Ω W'))
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) (hE4 : ¬ MuIsoE4 Ω W) :
    (∀ x ∈ muGroup Ω W', ∀ y ∈ muGroup Ω W', x * y = y * x) ∧ ¬ MuIsoE4 Ω W' :=
  CFSG.ClassicalInvolution.Asc77.T8T.muAbelian_notE4_transfer_gen e hab hE4

end Transfer

section Nbr

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem centralizer_le_normalizer_alpha_of_nbr [IsSimpleGroup G] (hD4 : Ih8D4Star p f)
    (h2 : C27_2 p f) (hA : C27_AlphaConst p f) (hH : Hyp51Tri p f)
    (hs : Std8 p f Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) (hE4 : ¬ MuIsoE4 Ω W)
    (hN : sigmaNorm Ω K ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G))
    {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) {s : G} (hs' : IsUniqueInvolution M s) :
    Subgroup.centralizer ({z * s} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨S', R', T', W', hstd⟩ :=
    c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
  obtain ⟨e⟩ := l7_5_2_proved p f hp hq G Ω hΩ W hs.hW.1 W' hstd.hW.1
  obtain ⟨hab', hE4'⟩ := muAbelian_notE4_transfer e hab hE4
  have hx : z * s * (z * s) = 1 := T8.mul_self_zt hp hΩ hs.hz hM hs'
  have hKx : T8.XMem Ω (z * s) K := T8.xMem_zt hstd
  have hcomp := h2 G Ω K M S' R' T' W' z s hstd hdisc
  have hconn := T8.dstarConnected_layerFamQ_of_abelian hD4 hstd hE4' hab'
  by_cases hE8 : ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω M → ∀ z' : G,
      IsUniqueInvolution K' z' → z' ≠ z * s
  · obtain ⟨K'', R'', z'', hF, hind⟩ := exists_triFrame_of_std8 hstd hE4' hab' hE8
    have hHyp : Hyp51 (Subgroup.closure ({z, s, z''} : Set G)) :=
      hH G Ω ![K, M, K''] ![z, s, z''] ![R', T', R''] hstd.stand hnt hF hind
    have hc01 : z * s = s * z := hF.comm hp hΩ 0 1
    have hc02 : z * z'' = z'' * z := hF.comm hp hΩ 0 2
    have hc12 : s * z'' = z'' * s := hF.comm hp hΩ 1 2
    have hz2 : z * z = 1 := hF.sq 0
    have hs2 : s * s = 1 := hF.sq 1
    have hz''2 : z'' * z'' = 1 := hF.sq 2
    have hz1 : z ≠ 1 := hF.ne_one 0
    have hs1 : s ≠ 1 := hF.ne_one 1
    have hz''1 : z'' ≠ 1 := hF.ne_one 2
    have hzs : z ≠ s := hF.x_ne hnt (i := 0) (j := 1) (by decide)
    have hB : IsElemAbelian 2 (Subgroup.closure ({z, s, z''} : Set G)) :=
      isElemAbelian_closure_three hz2 hs2 hz''2 hc01 hc02 hc12
    have hB8 : Nat.card ↥(Subgroup.closure ({z, s, z''} : Set G)) = 8 :=
      natCard_closure_three hz2 hs2 hz''2 hc01 hc02 hc12 hz1 hs1 hzs hz''1 hind
    have hDB : Subgroup.closure ({s, z} : Set G) ≤ Subgroup.closure ({z, s, z''} : Set G) := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with rfl | rfl <;> simp
    have hD : IsElemAbelian2 (Subgroup.closure ({s, z} : Set G)) 2 :=
      T7A.isElemAbelian2_closure_pair hs2 hz2 hs1 hz1 hzs.symm hc01.symm
    have h3 : ∀ A : Subgroup G, A ≤ Subgroup.closure ({z, s, z''} : Set G) →
        IsElemAbelian2 A 2 → alphaOf A = alphaOf (Subgroup.closure ({s, z} : Set G)) :=
      (lemma54_odd_and_eq hHyp hDB hD).2
    have hα : alphaOf (Subgroup.closure ({s, z} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) :=
      hA G Ω K hs.stand hs.noTwins hdisc ⟨W, hs.hW.1, hab, hE4⟩ z hs.hz M hM J hs.hJ s t hs'
        hs.ht
    intro c hc
    obtain ⟨ν, hν, hνc⟩ := exists_mul_mem_sigmaNorm_of_centralizer hstd hconn hcomp hc
    have hzsB : z * s ∈ Subgroup.closure ({z, s, z''} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    have hν' : ν ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({s, z} : Set G)) : Set G) :=
      oddCoreOf_centralizer_le_normalizer hB hB8 hzsB h3
        (oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ (z * s) hν)
    rw [hα] at hν'
    have hc' : c = ν⁻¹ * (ν * c) := by group
    rw [hc']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hν') (hN hνc)
  · push Not at hE8
    obtain ⟨K', hK', -, z', hz', hzt⟩ := hE8
    have hY : oddCoreOf (T8.layerJoin Ω (z * s)) ≤ sigmaNorm Ω K :=
      T8.oddCoreOf_layerJoin_le_of_zt hstd hK' (hzt ▸ hz')
    have hY1 : T8.layerJoin Ω (z * s) ≤ sigmaNorm Ω K :=
      T8.layerJoin_le_sigmaNorm_of_lift hp hq hΩ hx hKx hcomp hY hconn
    exact (T8.centralizer_le_sigmaNorm_of_layerJoin_le hstd hY1).trans hN

end Nbr

end T8T

end CFSG.ClassicalInvolution.Asc77
