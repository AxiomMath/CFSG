module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.ClassicalInvolution CFSG.RankThree.PartOne.TCX.Tri
  CFSG.HardMathSupport.Lang.Coordinator

set_option linter.unusedSectionVars false

section TwistedE6TwoDiagAux


theorem rootDiagUnit_zpowMatrix_cartan_mem_graphFixed {K : Type} [Field K] (σ : K ≃+* K)
    {c : Fin TwistTag.E6.tag.rank → Kˣ} (hc : c ∈ compatSubgroup (t := TwistTag.E6) σ.toRingHom) :
    rootDiagUnit TwistTag.E6.tag (zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan c) ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  have hT : (torusCoordHom TwistTag.E6.tag K c : ModGL TwistTag.E6.tag K) ∈
      compatTorus (t := TwistTag.E6) σ.toRingHom :=
    (mem_compatTorus σ.toRingHom).2 ⟨c, hc, rfl⟩
  have h := compatTorus_le_graphFixedRootGroup (t := TwistTag.E6) (K := K) σ.toRingHom hT
  rwa [torusCoordHom_eq_rootDiagUnit] at h

theorem compatDiagAutHom_mem_inner_of_zpowMatrix {K : Type} [Field K] (σ : K ≃+* K)
    (c : Fin TwistTag.E6.tag.rank → Kˣ) (hc : c ∈ compatSubgroup (t := TwistTag.E6) σ.toRingHom)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (hu : compatDiag TwistTag.E6 σ.toRingHom u =
      zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan c) :
    compatDiagAutHom TwistTag.E6 K σ.toRingHom u ∈ twistedE6Inn K σ := by
  have hmem := rootDiagUnit_zpowMatrix_cartan_mem_graphFixed σ hc
  rw [← hu] at hmem
  refine ⟨⟨_, hmem⟩, ?_⟩
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [coe_compatDiagAutHom]
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]

theorem card_twistedE6Diag_map_le_three (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2) :
    Nat.card ((twistedE6Diag K σ).map (QuotientGroup.mk' (twistedE6Inn K σ))) ≤ 3 := by
  classical
  have hq : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ.toRingHom c = c ^ 2 := fun c => hσ c
  set S : Subgroup (Fin TwistTag.E6.tag.rank → Kˣ) :=
    compatSubgroup (t := TwistTag.E6) σ.toRingHom with hS
  have hker : Nat.card ↥(S ⊓ (zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan).ker) = 3 := by
    rw [hS, card_compat_inf_ker_E6_of_card (σ := σ.toRingHom) hq hσ2]
    norm_num
  have hZS : ∀ c ∈ S, zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan c ∈ S := fun c hc =>
    zpowMatrix_cartan_mem_compatSubgroup hc
  let ζ0 : (∀ a : Fin TwistTag.E6.foldedTag.rank, (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) →*
      (Fin TwistTag.E6.tag.rank → Kˣ) :=
    MonoidHom.mk' (compatDiag TwistTag.E6 σ.toRingHom) fun u v => compatDiag_mul u v
  have hζ0 : ∀ u, ζ0 u ∈ S := fun u =>
    (mem_compatSubgroup σ.toRingHom).2 fun i => compatDiag_perm u i
  let ζS : (∀ a : Fin TwistTag.E6.foldedTag.rank,
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) →* S :=
    ζ0.codRestrict S hζ0
  let ZS : S →* S :=
    ((zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan).comp S.subtype).codRestrict S
      fun c => hZS c.1 c.2
  let R : Subgroup S := ZS.range
  let Ω : (∀ a : Fin TwistTag.E6.foldedTag.rank, (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) →*
      S ⧸ R :=
    (QuotientGroup.mk' R).comp ζS
  let π : MulAut (twistedE6RootGroup K σ) →* MulAut (twistedE6RootGroup K σ) ⧸
      twistedE6Inn K σ := QuotientGroup.mk' (twistedE6Inn K σ)
  let Λ := compatDiagAutHom TwistTag.E6 K σ.toRingHom
  have hΩ : Ω.ker ≤ (π.comp Λ).ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have h1 : ζS u ∈ R := (QuotientGroup.eq_one_iff (ζS u)).1 hu
    obtain ⟨s, hs⟩ := h1
    have hc : compatDiag TwistTag.E6 σ.toRingHom u =
        zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan s.1 := by
      have := congrArg Subtype.val hs
      exact this.symm
    have hmem := compatDiagAutHom_mem_inner_of_zpowMatrix σ s.1 s.2 u hc
    exact (QuotientGroup.eq_one_iff _).2 hmem
  have hidx : (π.comp Λ).ker.index ≤ Ω.ker.index := Subgroup.index_antitone hΩ
  have h2 : Ω.ker.index = Nat.card Ω.range := Subgroup.index_ker Ω
  have h3 : Nat.card Ω.range ≤ Nat.card (S ⧸ R) := Subgroup.card_le_card_group Ω.range
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have h5 : R.index = Nat.card ↥ZS.ker := by
    have e1 := Subgroup.card_mul_index ZS.ker
    have e2 := Subgroup.card_mul_index R
    have e3 : ZS.ker.index = Nat.card R := Subgroup.index_ker ZS
    rw [e3] at e1
    apply Nat.eq_of_mul_eq_mul_left hRpos
    calc Nat.card R * R.index = Nat.card S := e2
      _ = Nat.card ↥ZS.ker * Nat.card R := e1.symm
      _ = Nat.card R * Nat.card ↥ZS.ker := mul_comm _ _
  have h6 : Nat.card ↥ZS.ker = 3 := by
    have hmap : ZS.ker.map S.subtype = S ⊓ (zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan).ker := by
      ext x
      constructor
      · rintro ⟨s, hs, rfl⟩
        have h1 : ZS s = 1 := hs
        have h2 : zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan
            (s : Fin TwistTag.E6.tag.rank → Kˣ) = 1 := congrArg Subtype.val h1
        exact ⟨s.2, MonoidHom.mem_ker.2 h2⟩
      · rintro ⟨hxS, hx⟩
        have hx' : zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan x = 1 := MonoidHom.mem_ker.1 hx
        exact ⟨⟨x, hxS⟩, MonoidHom.mem_ker.2 (Subtype.ext hx'), rfl⟩
    rw [← Subgroup.card_map_of_injective S.subtype_injective, hmap, hker]
  have hmapR : (twistedE6Diag K σ).map π = (π.comp Λ).range :=
    (MonoidHom.range_comp π Λ).symm
  rw [hmapR, ← Subgroup.index_ker (π.comp Λ)]
  calc (π.comp Λ).ker.index ≤ Ω.ker.index := hidx
    _ = Nat.card Ω.range := h2
    _ ≤ Nat.card (S ⧸ R) := h3
    _ = R.index := rfl
    _ = Nat.card ↥ZS.ker := h5
    _ = 3 := h6

end TwistedE6TwoDiagAux

theorem twistedE6TwoDiagMeetsInn_holds :
    TwistedE6TwoDiagMeetsInn := by
  intro K _ _ hK σ hσ D hD hcard
  classical
  by_contra hno
  push Not at hno
  let π := QuotientGroup.mk' (twistedE6Inn K σ)
  have hinj : Function.Injective (π.domRestrict D) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨d, hd⟩ hk
    have hk' : π d = 1 := hk
    have hdN : d ∈ twistedE6Inn K σ := (QuotientGroup.eq_one_iff d).1 hk'
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hno d hd hdN)
  have himg : D.map π ≤ (twistedE6Diag K σ).map π := by
    rintro _ ⟨d, hd, rfl⟩
    have hdd : d ∈ ((twistedE6Inn K σ ⊔ twistedE6Diag K σ : Subgroup _) : Set _) := hD hd
    rw [Subgroup.normal_mul] at hdd
    obtain ⟨i, hi, r, hr, rfl⟩ := hdd
    refine ⟨r, hr, ?_⟩
    have hpi : π i = 1 := (QuotientGroup.eq_one_iff i).2 hi
    change π r = π (i * r)
    rw [map_mul, hpi, one_mul]
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (MulAut (twistedE6RootGroup K σ)) := inferInstance
  have hle : Nat.card (D.map π) ≤ 3 :=
    (Subgroup.card_le_of_le himg).trans (card_twistedE6Diag_map_le_three K hK σ hσ)
  have heq : Nat.card (D.map π) = Nat.card D := by
    rw [← MonoidHom.domRestrict_range]
    exact Nat.card_range_of_injective hinj
  rw [heq, hcard] at hle
  norm_num at hle

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
