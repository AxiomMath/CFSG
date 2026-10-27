module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZO2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Balance

section Cert

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23E8Z_secQ_isPGroup (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) : IsPGroup 2 (SecQ R u) := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hS := TwinPerpV3.layer_q8Section hc.std.perp hd.hu2
  have hΩs : HypOmegaGen (TwinDisc.secFam (Om R) u) := hS.hyp
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hτ₁, hτ₂, hdich⟩ := R56.u_trans_or_pair hT hc
  obtain ⟨htC, htH, hzz₁⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hJ₁ hτ₁
  obtain ⟨htC₂, htH₂, hzz₂⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hJ₂ hτ₂
  set tb : ↥(coreHull (Om R) u) ⧸ classicalInvolutionOddCore ↥(coreHull (Om R) u) :=
    QuotientGroup.mk (⟨⟨u * e, htC⟩, htH⟩ : ↥(coreHull (Om R) u)) with htb
  have hcen : ∀ y : SecQ R u, y * tb = tb * y := R56.secCentral_of_zStar hΩ h2 hc2 htC htH hZ
  have hall : ∀ M ∈ TwinDisc.secFam (Om R) u, IsUniqueInvolution M tb := by
    intro M hM
    rcases hdich with htr | hpair
    · obtain ⟨x, hx⟩ := htr _ (TwinDisc.secImg_mem_secFam hJ₁) M hM
      have hxt : x * tb * x⁻¹ = tb := by rw [hcen x, mul_inv_cancel_right]
      have h := hzz₁.conj x
      rwa [hx, hxt] at h
    · rcases hpair M hM with rfl | rfl
      · exact hzz₁
      · exact hzz₂
  have hCt : Subgroup.centralizer ({tb} : Set (SecQ R u)) = ⊤ :=
    eq_top_iff.mpr fun y _ => Subgroup.mem_centralizer_singleton_iff.mpr (hcen y)
  have hOtop : oddCoreIn (⊤ : Subgroup (SecQ R u)) = ⊥ := by
    have hn : (oddCoreIn (⊤ : Subgroup (SecQ R u))).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (normalizer_oddCoreIn ⊤))
    have hle : oddCoreIn (⊤ : Subgroup (SecQ R u)) ≤ classicalInvolutionOddCore (SecQ R u) :=
      le_sSup ⟨hn, odd_card_oddCoreIn _⟩
    rw [hS.oddFree] at hle
    exact le_bot_iff.mp hle
  have hθ : oddCoreIn (Subgroup.centralizer ({tb} : Set (SecQ R u))) = ⊥ := by
    rw [hCt]
    exact hOtop
  have hm2 : ∀ M ∈ TwinDisc.secFam (Om R) u, IsPGroup 2 ↥M := fun M hM =>
    isPGroup_of_oddCent hΩs hM (hall M hM) hθ (hS.two M hM)
  have hJ := TwinSecXg.twinJoin_isPGroup hΩs hm2 hzz₁
  have hgen : omegaGen (TwinDisc.secFam (Om R) u) ≤
      TwinSecXg.twinJoin (TwinDisc.secFam (Om R) u) (TwinDisc.secImg (Om R) u J₁) :=
    iSup₂_le fun M hM => TwinSecXg.le_twinJoin ⟨hM, tb, hzz₁, hall M hM⟩
  have hJ' : IsPGroup 2 ↥(omegaGen (TwinDisc.secFam (Om R) u)) := hJ.to_le hgen
  rw [hS.gen] at hJ'
  exact hJ'.of_equiv Subgroup.topEquiv

theorem p23E8Z_t_quiet (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) (htu : t ∈ Subgroup.centralizer ({u} : Set Y)) :
    ∀ L : Subgroup (OddQuot u), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk u ⟨t, htu⟩ * y = y * oddQuotMk u ⟨t, htu⟩ := by
  obtain ⟨_, _, _, _, _, vH, v', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hvH, hzv, -⟩ :=
    YGam.frame_at_u hc
  have hd := hc.data
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hHn : (coreHull (Om R) u).Normal := ⟨fun a ha g' => by
    have h := conj_mem_conjSub (n := g') ha
    rwa [conjSub_coreHull hΩ hc2 g'] at h⟩
  have hHs : IsSubnormal (coreHull (Om R) u) ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hHn.isSubnormal
  have hO2 : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u))
      (⟨(vH : ↥(Subgroup.centralizer ({u} : Set Y))), vH.2⟩ : ↥(coreHull (Om R) u))) :=
    ⟨⊤, inferInstance, (p23E8Z_secQ_isPGroup hT hc hZ).to_subgroup ⊤, Subgroup.mem_top _⟩
  have hv'C : v' ∈ Subgroup.centralizer ({u} : Set Y) := by
    rw [← hvH]
    exact YGam.hcoeHom_mem_centralizer (Om R) u vH
  have hvC : (vH : ↥(Subgroup.centralizer ({u} : Set Y))) = ⟨v', hv'C⟩ := Subtype.ext hvH
  have hq : ∀ L : Subgroup (OddQuot u), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk u ⟨v', hv'C⟩ * y = y * oddQuotMk u ⟨v', hv'C⟩ := by
    intro L hL
    have h := TL4.quiet_of_inO2_sub hHs vH.2 hO2 L hL
    rw [hvC] at h
    exact h
  have huC : u ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hucen : ∀ y : OddQuot u, oddQuotMk u ⟨u, huC⟩ * y = y * oddQuotMk u ⟨u, huC⟩ := by
    intro y
    obtain ⟨c, rfl⟩ : ∃ c, oddQuotMk u c = y := QuotientGroup.mk'_surjective _ y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm
  rcases hzv with h | h
  · have e : (⟨t, htu⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) = ⟨v', hv'C⟩ := Subtype.ext h
    rw [e]
    exact hq
  · have e : (⟨t, htu⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) = ⟨u, huC⟩ * ⟨v', hv'C⟩ :=
      Subtype.ext h
    intro L hL y hy
    rw [e, map_mul, mul_assoc, hq L hL y hy, ← mul_assoc, hucen y, mul_assoc]

theorem p23E8Z_oddCoreIn_eq (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u))
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({t} : Set Y)) =
      oddCoreIn (Subgroup.centralizer ({u} : Set Y)) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hK : tightCore R ∈ twinSet (Om R) (tightCore R) :=
    mem_twinSet_self (CoreAssembly.mem_conjClass_self _) hz
  have hKM : tightCore R ≤ TwinSecXg.twinJoin (Om R) (tightCore R) :=
    fun x hx => TwinSecXg.le_twinJoin hK hx
  have hK'M : K' ≤ TwinSecXg.twinJoin (Om R) (tightCore R) :=
    fun x hx => TwinSecXg.le_twinJoin hc.std.hK' hx
  have hut : u ∈ Subgroup.centralizer ({t} : Set Y) :=
    TwinSecXg.twinJoin_le_centralizer hz (sup_le hKM hK'M hd.hu)
  have htu : t ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hut).symm
  have hα' : alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ := by
    rw [Set.pair_comm]; exact hα
  have hqu := p23E8A_u_quiet hc hut
  have hqt := p23E8Z_t_quiet hT hc hZ htu
  have h1 : oddCoreIn (Subgroup.centralizer ({u} : Set Y)) ≤
      oddCoreIn (Subgroup.centralizer ({t} : Set Y)) :=
    TwinOdd.oddCent_le_of_alpha hut hd.hu2 hd.hu1 hα
      fun L hL _ ⟨y, hy, hne⟩ => (hne (hqu L hL y hy)).elim
  have h2 : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) ≤
      oddCoreIn (Subgroup.centralizer ({u} : Set Y)) :=
    TwinOdd.oddCent_le_of_alpha htu hz.sq hz.ne_one hα'
      fun L hL _ ⟨y, hy, hne⟩ => (hne (hqt L hL y hy)).elim
  exact le_antisymm h2 h1

theorem p23E8Z_oddCent_eq_bot_of_alpha (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u))
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
  have hC := CoreData.of_S hc.std.perp.core
  have hTwo := p23Two_of_thmEQ8 hE hcit hP Y R S t K' W u e g hc
  have heq := p23E8Z_oddCoreIn_eq hT hc hZ hα
  set N : Subgroup Y := oddCoreIn (Subgroup.centralizer ({t} : Set Y)) with hN
  have hnorm_of : ∀ x : Y, (∀ y ∈ N, x * y * x⁻¹ ∈ N) → (∀ y ∈ N, x⁻¹ * y * x ∈ N) →
      x ∈ Subgroup.normalizer (N : Set Y) := by
    intro x h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => h1 h hh, fun hh => ?_⟩
    have := h2 _ hh
    simpa [mul_assoc] using this
  have hCt : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (N : Set Y) := fun x hx =>
    hnorm_of x (fun y hy => conj_mem_oddCoreIn hx hy)
      (fun y hy => by
        have := conj_mem_oddCoreIn (Subgroup.inv_mem _ hx) hy
        simpa using this)
  have hCu : Subgroup.centralizer ({u} : Set Y) ≤ Subgroup.normalizer (N : Set Y) := fun x hx =>
    hnorm_of x (fun y hy => by rw [heq] at hy ⊢; exact conj_mem_oddCoreIn hx hy)
      (fun y hy => by
        rw [heq] at hy ⊢
        have := conj_mem_oddCoreIn (Subgroup.inv_mem _ hx) hy
        simpa using this)
  have htop : Subgroup.normalizer (N : Set Y) = ⊤ := by
    rw [eq_top_iff, ← hTwo]
    exact sup_le hCu hCt
  have hNn : N.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hle : N ≤ classicalInvolutionOddCore Y := le_sSup ⟨hNn, odd_card_oddCoreIn _⟩
  rw [hC.oddFree] at hle
  exact TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn (le_bot_iff.mp hle)

theorem p23E8Z_oddCoreIn_eq_bot_of_alpha (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u))
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
  TwinConnT.oddCoreIn_eq_bot_of_classicalOddCore
    (p23E8Z_oddCent_eq_bot_of_alpha hE hT hcit hP hc hZ hα)

theorem p23E8Z_members_isPGroup_of_alpha (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u))
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    ∀ J ∈ Om R, IsPGroup 2 ↥J := by
  have hC := CoreData.of_S hc.std.perp.core
  exact isPGroup_conjClass_of_oddCent hC.hyp (Inner.isUniqueInvolution_core hC.datum)
    (p23E8Z_oddCoreIn_eq_bot_of_alpha hE hT hcit hP hc hZ hα)
    (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)

theorem p23E8Z_cu_le_normalizer_alpha (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hc : P23Cfg n Y R S t K' W u e g) (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) :
    Subgroup.centralizer ({u} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) := by
  have hd := hc.data
  have hue2 : u * e * (u * e) = 1 := ue_sq hc
  have hue1 : u * e ≠ 1 := ue_ne_one hc
  have hu_ue : u * (u * e) = u * e * u :=
    (Subgroup.mem_centralizer_singleton_iff.mp (ue_comm_u hc)).symm
  have hu_ne : u ≠ u * e := by
    intro h
    exact hd.he1 (by simpa using congrArg (u⁻¹ * ·) h.symm)
  obtain ⟨-, hbal⟩ := hα Y R S t K' W u e g hc (Or.inl hZ)
  have hA1B : Subgroup.closure ({u, u * e} : Set Y) ≤ Subgroup.closure ({u * e, u, t} : Set Y) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
  have hA1 : alphaOf (Subgroup.closure ({u, u * e} : Set Y)) =
      alphaOf (Subgroup.closure ({u, t} : Set Y)) :=
    hbal _ hA1B (T7A.isElemAbelian2_closure_pair hd.hu2 hue2 hd.hu1 hue1 hu_ne hu_ue)
  have hO := oddCoreOf_centralizer_le_normalizer_alphaOf (c := u) (z := u * e) hue2 hd.hu1 hu_ue
  rw [← hA1]
  intro x hx
  obtain ⟨o, ho, hm⟩ := R56.p23_cu_split hT hc hZ hx
  have hoC : o ∈ Subgroup.centralizer ({u} : Set Y) := oddCoreOf_le_self _ ho
  have hmu : o⁻¹ * x ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hoC) hx
  have hmN := mem_normalizer_alphaOf_of_centralizes (c := u) (z := u * e)
    (Subgroup.mem_centralizer_singleton_iff.mp hmu) (Subgroup.mem_centralizer_singleton_iff.mp hm)
  have ex : x = o * (o⁻¹ * x) := by group
  rw [ex]
  exact Subgroup.mul_mem _ (hO ho) hmN

@[expose] def P23E8ZNormT (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        Subgroup.centralizer ({t} : Set Y) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y)

theorem p23E8ZAlpha_of_normT (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n)
    (hα : P23Alpha n) (hN : P23E8ZNormT n) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) (hA6 : SecAE R e 6) :
    alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ :=
  p23_alpha_eq_bot hc (p23Two_of_thmEQ8 hE hcit hP Y R S t K' W u e g hc)
    (hα Y R S t K' W u e g hc (Or.inl hZ)).1
    ⟨p23E8Z_cu_le_normalizer_alpha hT hα hc hZ, hN hcit hP Y R S t K' W u e g hc hno hZ hA6⟩

section O2

theorem p23E8Z_e_mem_O2_of_alpha (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u))
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set Y))).map
      (Subgroup.centralizer ({t} : Set Y)).subtype :=
  p23E8Z_e_mem_pCore hT hcit hP hc hZ (p23E8Z_oddCoreIn_eq_bot_of_alpha hE hT hcit hP hc hZ hα)

theorem p23E8Z_oddC_of_normT (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n)
    (hα : P23Alpha n) (hN : P23E8ZNormT n) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) (hA6 : SecAE R e 6) :
    oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥ ∧
      e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set Y))).map
        (Subgroup.centralizer ({t} : Set Y)).subtype := by
  have h1 := p23E8ZAlpha_of_normT hE hT hα hN hcit hP hc hno hZ hA6
  exact ⟨p23E8Z_oddCoreIn_eq_bot_of_alpha hE hT hcit hP hc hZ h1,
    p23E8Z_e_mem_O2_of_alpha hE hT hcit hP hc hZ h1⟩

end O2

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
