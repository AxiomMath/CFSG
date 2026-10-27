module

public import CFSG.ClassicalInvolution.Asc77.AscT8V17
public import CFSG.ClassicalInvolution.Asc77.AscT8S26E4
public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75
import CFSG.StronglyEmbedded.UniqueCosetFixedEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.StronglyEmbedded.UniqueCoset

namespace T8X


variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem not_comm_of_muIsoWylD4 {W : Subgroup G} (h : MuIsoWylD4 Ω W) :
    ¬ ∀ x y : ↥(muGroup Ω W), x * y = y * x :=
  s26_not_comm_of_muIso (Or.inr (Or.inr h))

theorem not_comm_of_wset (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) (h : MuIsoWylD4 Ω W) {W' : Subgroup G}
    (hW' : W' ∈ WSet Ω) :
    ¬ ∀ x ∈ muGroup Ω W', ∀ y ∈ muGroup Ω W', x * y = y * x := by
  intro hc
  obtain ⟨e⟩ := l7_5_2_proved p f hp hq G Ω hΩ W hW W' hW'
  refine not_comm_of_muIsoWylD4 h fun a b => e.injective ?_
  rw [map_mul, map_mul]
  exact Subtype.ext (hc _ (e a).2 _ (e b).2)

variable {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem fixesUniqueCoset_of_comp [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hcomp : dComp Ω K = dstarComp Ω K) :
    FixesUniqueCoset (z * t) (T8.H274 Ω K z) := by
  have hmin' := c27_4M_proved (p := p) (f := f) G Ω K J S R T W z t hs hdisc
  have hzt : z * t ∈ T8.H274 Ω K z :=
    T8.centralizer_mul_le_H274 hs.hJ hs.ht (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  refine CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_mem hzt (fun g hg => ?_)
  exact T8.mem_H274_of_min hs hcomp hmin' hg

theorem H274_eq_top [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hcomp : dComp Ω K = dstarComp Ω K) : T8.H274 Ω K z = ⊤ := by
  by_contra hH
  have hz := hs.hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h1 : ∃! c : G ⧸ T8.H274 Ω K z, z • c = c := T8.fixesUniqueCoset_z hs hcomp
  have h2' : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ T8.H274 Ω K z, (z * (g⁻¹ * z * g)) • c = c := by
    intro g hne' hcomm
    rcases T8.isConj_or_mem_omegaNbr hs.stand hs.noTwins hz hne' hcomm with hconj | hnbr
    · exact CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_isConj hconj h1
    · have hb : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
        have := hz.conj g⁻¹
        rwa [inv_inv] at this
      obtain ⟨S', R', T', W', hstd⟩ := c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hz
        (conjSub g⁻¹ K) hnbr (g⁻¹ * z * g) hb
      exact fixesUniqueCoset_of_comp hstd hdisc hcomp
  have hKs := CFSG.StronglyEmbedded.UniqueCoset.not_isSolvable_of_mem hs.stand.hyp hs.stand.mem hz
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : Group.IsSolvable G := IsSimpleGroup.comm_iff_isSolvable.mp hcon
    exact hKs inferInstance
  have hTs : IsSimpleGroup ↥(⊤ : Subgroup G) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).isSimpleGroup
  have hTnab : ∃ x ∈ (⊤ : Subgroup G), ∃ y ∈ (⊤ : Subgroup G), x * y ≠ y * x := by
    obtain ⟨a, b, h⟩ := hnab
    exact ⟨a, Subgroup.mem_top a, b, Subgroup.mem_top b, h⟩
  have hTc : Subgroup.centralizer ((⊤ : Subgroup G) : Set G) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.1 hb a)
  exact CFSG.StronglyEmbedded.UniqueCoset.false_of_uniqueCoset_of_not_isSolvable hH hz2 h1 h2'
    hTs hTnab hTc (CFSG.StronglyEmbedded.UniqueCoset.le_centralizer_of_isUniqueInvolution hz) hKs

theorem centralizer_le_sigmaNorm_of_nonabelian [IsSimpleGroup G]
    (hs : Std8 p f Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (hcomp : dComp Ω K = dstarComp Ω K)
    (hab : ¬ ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) (hE4 : ¬ MuIsoE4 Ω W) :
    Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hKx : T8.XMem Ω (z * t) K := T8.xMem_zt hs
  have hlayer : T8.layerJoin Ω (z * t) ≤ sigmaNorm Ω K := by
    by_cases hconn : T3.DStarConnected (T8.layerFamQ Ω (z * t))
    · exact T8.layerJoin_le_sigmaNorm_of_lift hp hq hΩ hx hKx hcomp
        (T8.oddCoreOf_layerJoin_le_of_nonabelian hs hcomp hab) hconn
    · exact T8V.c27_Ysmall_proved G Ω K J S R T W z t hs hdisc hE4 hab hconn
  exact T8.centralizer_le_sigmaNorm_of_layerJoin_le hs hlayer

theorem false_of_dComp_eq [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hcomp : dComp Ω K = dstarComp Ω K) (hμ : MuIsoWylD4 Ω W) :
    False := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hz := hs.hz
  have hle : T8.H274 Ω K z ≤ sigmaNorm Ω K := by
    refine sup_le le_rfl (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => ?_)
    obtain ⟨S', R', T', W', hstd'⟩ :=
      c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hz M hM s hs'
    have hW' : W' ∈ WSet Ω := hstd'.hW.1
    have hab' := not_comm_of_wset hp hq hΩ hs.hW.1 hμ hW'
    have hE4' : ¬ MuIsoE4 Ω W' := fun h =>
      hab' fun x hx y hy => by
        obtain ⟨e⟩ := h
        have := e.injective (a₁ := ⟨x, hx⟩ * ⟨y, hy⟩) (a₂ := ⟨y, hy⟩ * ⟨x, hx⟩)
          (by rw [map_mul, map_mul]; exact mul_comm _ _)
        exact congrArg Subtype.val this
    exact centralizer_le_sigmaNorm_of_nonabelian hstd' hdisc hcomp hab' hE4'
  have htop : sigmaNorm Ω K = ⊤ := top_le_iff.mp (H274_eq_top hs hdisc hcomp ▸ hle)
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.stand.mem hs.stand.trans htop)

end T8X

end CFSG.ClassicalInvolution.Asc77
