module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporComp
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.LyThree
public import CFSG.RankThree.PartTwo.KFacts.K426McL
import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCrit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

namespace LyNoPumpup

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Sporadic.Recognition.LyonsSims
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

private theorem isMulCommutative_of_card_le_two {Q : Type*} [Group Q] [Finite Q]
    (h : Nat.card Q ≤ 2) : IsMulCommutative Q := by
  have h1 : Nat.card Q = 1 ∨ Nat.card Q = 2 := by
    have := Nat.card_pos (α := Q)
    omega
  rcases h1 with h1 | h1
  · haveI : Subsingleton Q := (Nat.card_eq_one_iff_unique.1 h1).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : IsCyclic Q := isCyclic_of_prime_card (p := 2) h1
    infer_instance

private theorem commutator_mem_of_card_le {G : Type*} [Group G] [Finite G] {C Q : Subgroup G}
    (hQC : Q ≤ C) (hcard : Nat.card C ≤ 2 * Nat.card Q) {a b : G} (ha : a ∈ C) (hb : b ∈ C) :
    ⁅a, b⁆ ∈ Q := by
  set N : Subgroup ↥C := Q.subgroupOf C
  have hNcard : Nat.card N = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
  have hmul : N.index * Nat.card N = Nat.card C := Subgroup.index_mul_card N
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hidx : N.index ≤ 2 := by
    by_contra hcon
    have h3 : 3 ≤ N.index := by omega
    have : 3 * Nat.card Q ≤ N.index * Nat.card N := by
      rw [hNcard]
      exact Nat.mul_le_mul_right _ h3
    omega
  have hidx0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hnorm : N.Normal := by
    rcases (by omega : N.index = 1 ∨ N.index = 2) with h1 | h1
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h1
  have hcomm : IsMulCommutative (↥C ⧸ N) := by
    refine isMulCommutative_of_card_le_two ?_
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hle : commutator ↥C ≤ N := Subgroup.Normal.quotient_commutative_iff_commutator_le.1 hcomm
  have hmem : (⁅(⟨a, ha⟩ : ↥C), ⟨b, hb⟩⁆ : ↥C) ∈ commutator ↥C := by
    rw [commutator_eq_closure]
    exact Subgroup.subset_closure ⟨_, _, rfl⟩
  exact Subgroup.mem_subgroupOf.1 (hle hmem)

private theorem le_of_perfect_of_card_le {G : Type*} [Group G] [Finite G] {C Q K : Subgroup G}
    (hQC : Q ≤ C) (hcard : Nat.card C ≤ 2 * Nat.card Q) (hKC : K ≤ C) (hK : ⁅K, K⁆ = K) :
    K ≤ Q := by
  rw [← hK]
  exact Subgroup.commutator_le.2 fun a ha b hb =>
    commutator_mem_of_card_le hQC hcard (hKC ha) (hKC hb)

private theorem false_of_noA6_of_map {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    {C : Subgroup Y} (hC : NoA6 C) {K : Subgroup X} (hKC : K.map φ ≤ C)
    (f : K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hker : ∀ k : K, φ k = 1 → f k = 1) : False := by
  have hψ : Function.Surjective (φ.subgroupMap K) := φ.subgroupMap_surjective K
  have hle : (φ.subgroupMap K).ker ≤ f.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    apply hker
    have := congrArg Subtype.val hk
    simpa using this
  have hg : Function.Surjective (MonoidHom.liftOfSurjective (φ.subgroupMap K) hψ ⟨f, hle⟩) := by
    intro a
    obtain ⟨k, rfl⟩ := hf a
    exact ⟨φ.subgroupMap K k, by simp⟩
  exact hC _ hKC _ hg

private theorem noA6_centralizer_of_mulEquiv_mcl
    {G : Type*} [Group G] (φ : G ≃* NativeSporadic.McL) {s : G}
    (hs : orderOf s = 3) : NoA6 (Subgroup.centralizer ({s} : Set G)) := by
  intro K hK f hf
  have hKc : K.map (φ : G →* NativeSporadic.McL) ≤
      Subgroup.centralizer ({φ s} : Set NativeSporadic.McL) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hK hk)
    show φ k * φ s = φ s * φ k
    rw [← map_mul, ← map_mul, h]
  have hφs : orderOf (φ s) = 3 := by rw [MulEquiv.orderOf_eq]; exact hs
  have ψ : ↥K ≃* ↥(K.map (φ : G →* NativeSporadic.McL)) :=
    Subgroup.equivMapOfInjective K (φ : G →* NativeSporadic.McL) φ.injective
  exact mclThreeCentralizer (φ s) hφs _ hKc (f.comp (ψ.symm : _ →* _))
    (hf.comp ψ.symm.surjective)

private theorem hat_of_mulEquiv {X X' Q : Type*} [Group X] [Group X'] [Group Q] (e : X ≃* X')
    (h : commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
      Nonempty ((X ⧸ Subgroup.center X) ≃* Q)) :
    commutator X' = ⊤ ∧ Nat.card (Subgroup.center X') = 3 ∧
      Nonempty ((X' ⧸ Subgroup.center X') ≃* Q) := by
  obtain ⟨hc, hcard, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' :=
    Subgroup.map_center_eq e
  refine ⟨?_, ?_, ⟨(QuotientGroup.congr _ _ e hcen).symm.trans f⟩⟩
  · have h1 := congrArg (Subgroup.map e.toMonoidHom) hc
    rw [commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h1
    rw [commutator]
    exact h1
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hcard]

private theorem isHatSix_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : IsHatSix X) : IsHatSix X' := hat_of_mulEquiv e h

private theorem isComponentOf_map_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    {K C : Subgroup G} (h : IsComponentOf K C) :
    IsComponentOf (K.map φ.toMonoidHom) (C.map φ.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map φ.toMonoidHom,
    CFSG.Open.IsQuasisimple.of_mulEquiv (K.equivMapOfInjective _ φ.injective).symm h.2.2⟩

private theorem map_centralizer_singleton {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (d : G) : (Subgroup.centralizer ({d} : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ d} : Set H) := by
  ext h
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, hg]
  · intro hh
    refine ⟨φ.symm h, φ.injective ?_, φ.apply_symm_apply h⟩
    simpa [map_mul] using hh

private theorem noHatSix_of_isConj {S : Type*} [Group S] {s x : S} (hc : IsConj s x)
    (H : ∀ K : Subgroup S, IsComponentOf K (Subgroup.centralizer ({x} : Set S)) →
      IsHatSix ↥K → False)
    {K : Subgroup S} (hK : IsComponentOf K (Subgroup.centralizer ({s} : Set S)))
    (h : IsHatSix ↥K) : False := by
  obtain ⟨c, hcx⟩ := isConj_iff.1 hc
  let e : S ≃* S := MulAut.conj c
  have hes : e s = x := by
    show c * s * c⁻¹ = x
    exact hcx
  have hmap : (Subgroup.centralizer ({s} : Set S)).map e.toMonoidHom =
      Subgroup.centralizer ({x} : Set S) := by
    rw [map_centralizer_singleton e s, hes]
  have hK' : IsComponentOf (K.map e.toMonoidHom) (Subgroup.centralizer ({x} : Set S)) := by
    rw [← hmap]
    exact isComponentOf_map_mulEquiv e hK
  exact H _ hK' (isHatSix_of_mulEquiv (K.equivMapOfInjective e.toMonoidHom e.injective) h)

section


private theorem no_hatSix_of_class_one {S : Type} [Group S] [Finite S] {t : S}
    {ρ : ↥(Subgroup.centralizer ({t} : Set S)) →* Equiv.Perm (Fin 11)}
    {x₁ x₂ x₃ : ↥(Subgroup.centralizer ({t} : Set S))} (D : LyData S t ρ)
    (St : LyStd ρ x₁ x₂ x₃) {K : Subgroup S}
    (hK : IsComponentOf K (Subgroup.centralizer ({(x₁ : S)} : Set S))) (h : IsHatSix ↥K) :
    False := by
  have hperf := D.isPerfect_centralizer St
  have hcen := D.center_centralizer St
  have hc3 := D.card_center_centralizer St
  obtain ⟨eM⟩ := D.centQuot_mcl St.pow₁ St.rho₁
  have e : ↥(Subgroup.centralizer ({(x₁ : S)} : Set S)) ⧸
      Subgroup.center ↥(Subgroup.centralizer ({(x₁ : S)} : Set S)) ≃* NativeSporadic.McL :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans eM
  have hsimple : IsSimpleGroup (↥(Subgroup.centralizer ({(x₁ : S)} : Set S)) ⧸
      Subgroup.center ↥(Subgroup.centralizer ({(x₁ : S)} : Set S))) :=
    @MulEquiv.isSimpleGroup _ _ NativeSporadic.McL _ CFSG.Sporadic.McL.isSimpleGroup_McL e
  have hnab : ∃ a b : ↥(Subgroup.centralizer ({(x₁ : S)} : Set S)) ⧸
      Subgroup.center ↥(Subgroup.centralizer ({(x₁ : S)} : Set S)), a * b ≠ b * a :=
    LyMult.exists_noncomm_of_simple
      (by rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL]; norm_num)
  have hquasi : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({(x₁ : S)} : Set S)) :=
    ⟨hperf, hsimple, hnab⟩
  have hcard : Nat.card ↥(Subgroup.centralizer ({(x₁ : S)} : Set S)) = 2694384000 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(Subgroup.centralizer ({(x₁ : S)} : Set S)))
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL, hc3] at h1
    omega
  have hKC : K = Subgroup.centralizer ({(x₁ : S)} : Set S) :=
    component_eq_of_normal_quasisimple hK le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance) hquasi fun H hH _ => hH
  have h1080 := gfr2_card_isHatSix h
  rw [hKC, hcard] at h1080
  omega

private theorem no_hatSix_of_class_two {S : Type} [Group S] [Finite S] {t : S}
    {ρ : ↥(Subgroup.centralizer ({t} : Set S)) →* Equiv.Perm (Fin 11)}
    {x₁ x₂ x₃ : ↥(Subgroup.centralizer ({t} : Set S))} (D : LyData S t ρ)
    (St : LyStd ρ x₁ x₂ x₃)
    (hC : Nat.card ↥(Subgroup.centralizer ({(x₁ : S) * (x₂ : S)} : Set S)) ≤ 174960)
    (hQ : ∀ y : CentQuot (x₁ : S), orderOf y = 3 →
      NoA6 (Subgroup.centralizer ({y} : Set (CentQuot (x₁ : S))))) {K : Subgroup S}
    (hK : IsComponentOf K (Subgroup.centralizer ({(x₁ : S) * (x₂ : S)} : Set S)))
    (h : IsHatSix ↥K) : False := by
  classical
  set C₁ : Subgroup S := Subgroup.centralizer ({(x₁ : S)} : Set S)
  have hQC : QE (x₁ : S) (x₂ : S) ≤
      Subgroup.centralizer ({(x₁ : S) * (x₂ : S)} : Set S) := by
    intro g hg
    rw [mem_QE] at hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * ((x₁ : S) * (x₂ : S)) = (g * (x₁ : S)) * (x₂ : S) := by group
      _ = ((x₁ : S) * g) * (x₂ : S) := by rw [hg.1]
      _ = (x₁ : S) * (g * (x₂ : S)) := by group
      _ = (x₁ : S) * ((x₂ : S) * g) := by rw [hg.2]
      _ = (x₁ : S) * (x₂ : S) * g := by group
  have hQc : Nat.card ↥(QE (x₁ : S) (x₂ : S)) = 87480 := D.card_QE St
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.2.2.1⟩
  have hKQ : K ≤ QE (x₁ : S) (x₂ : S) :=
    le_of_perfect_of_card_le hQC (by omega) hK.1 hperf
  have hK1 : ∀ k ∈ K, (x₁ : S) * k = k * (x₁ : S) := fun k hk => (mem_QE.1 (hKQ hk)).1
  have hK2 : ∀ k ∈ K, (x₂ : S) * k = k * (x₂ : S) := fun k hk => (mem_QE.1 (hKQ hk)).2
  have hKC₁ : K ≤ C₁ := fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hK1 k hk).symm
  let φ : ↥C₁ →* CentQuot (x₁ : S) := QuotientGroup.mk' _
  have hy3 : orderOf (φ (D.x₂M St)) = 3 := D.orderOf_x₂Q St
  set K'' : Subgroup ↥C₁ := K.subgroupOf C₁
  have hKcent : K''.map φ ≤ Subgroup.centralizer ({φ (D.x₂M St)} : Set (CentQuot (x₁ : S))) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk' : (k : S) ∈ K := hk
    have : k * D.x₂M St = D.x₂M St * k := Subtype.ext (hK2 _ hk').symm
    rw [← map_mul, ← map_mul, this]
  obtain ⟨-, -, ⟨e6⟩⟩ := h
  let f₀ : ↥K →* alternatingGroup (Fin 6) :=
    e6.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  let ι : ↥K'' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC₁
  let f : ↥K'' →* alternatingGroup (Fin 6) := f₀.comp ι.toMonoidHom
  have hf : Function.Surjective f :=
    (e6.surjective.comp (QuotientGroup.mk'_surjective _)).comp ι.surjective
  refine false_of_noA6_of_map φ (hQ _ hy3) hKcent f hf ?_
  intro k hk
  show e6 (QuotientGroup.mk (ι k)) = 1
  have hmk : (QuotientGroup.mk k.1 : CentQuot (x₁ : S)) = 1 := hk
  have hz : (k.1 : S) ∈ Subgroup.zpowers (x₁ : S) := mem_zpowers_of_mk_eq_one (x₁ : S) hmk
  have hcen : ι k ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
    apply Subtype.ext
    show (y : S) * (k.1 : S) = (k.1 : S) * (y : S)
    rw [← hn]
    exact (Commute.zpow_right (show Commute (y : S) (x₁ : S) from (hK1 (y : S) y.2).symm) n).eq
  rw [(QuotientGroup.eq_one_iff (ι k)).2 hcen, map_one]

theorem ly_no_hatSix {S : Type} [Group S] [Finite S] (eT : S ≃* NativeSporadic.Carrier .Ly)
    {s : S} (hs : orderOf s = 3) {K : Subgroup S}
    (hK : IsComponentOf K (Subgroup.centralizer ({s} : Set S))) (h : IsHatSix ↥K) : False := by
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly ⟨eT⟩)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  have hord := LyCore.lyThreeBOrder_thm S ⟨eT⟩ t ρ D x₁ x₂ x₃ St
  rcases (lemma45_classes_of_certificate D St).1 s hs with hc | hc
  · exact noHatSix_of_isConj hc (fun K' hK' h' => no_hatSix_of_class_one D St hK' h') hK h
  · obtain ⟨eM⟩ := D.centQuot_mcl St.pow₁ St.rho₁
    exact noHatSix_of_isConj hc (fun K' hK' h' => no_hatSix_of_class_two D St hord
      (fun y hy => noA6_centralizer_of_mulEquiv_mcl eM hy) hK' h') hK h

end

end LyNoPumpup

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem sporNoPumpup_Ly
    (hSpM : SporadicMultipliers) (hOG : UniquenessMaximal.InputONGroup)
    (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) : SporNoPumpup .Ly := by
  have e0 : (TauCeti.CFSGIndex.sporadic .Ly).Group ≃* NativeSporadic.Carrier .Ly :=
    (hbr .Ly).some.symm
  haveI : Finite (NativeSporadic.Carrier .Ly) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card NativeSporadic.Ly ≠ 0
      rw [CFSG.Sporadic.Ly.card_Ly]
      norm_num)
  haveI : Finite (TauCeti.CFSGIndex.sporadic .Ly).Group := Finite.of_equiv _ e0.symm.toEquiv
  refine sporNoPumpup_of_components hSpM hOG hOut ?_ ?_ ?_ ?_
  · rw [Nat.card_congr e0.toEquiv]
    show Nat.card NativeSporadic.Ly = sporOrd .Ly
    rw [CFSG.Sporadic.Ly.card_Ly]
    norm_num [sporOrd, CFSG.Open.orderLy]
  · exact oPrimeCoreTrivialAt_Ly_three _ ⟨e0⟩
  · intro s hs K hK h
    rcases h with h | ⟨h, -⟩
    · exact LyNoPumpup.ly_no_hatSix e0 hs hK h
    · exact absurd h (by decide)
  · intro h
    exact absurd h (by decide)

end CFSG.HardMathSupport.Solomon.Coordinator
