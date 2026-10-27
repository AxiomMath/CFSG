module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.ComponentSection
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiComponent

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique.Setup
open scoped commutatorElement

theorem isCatalogGroup_centerQuotient {X : Type*} [Group X]
    (hX : CFSG.Open.IsKGroup X) {K : Subgroup X} (hK : CFSG.IsQuasisimple ↥K) :
    CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) := by
  have heq : ((Subgroup.center ↥K).map K.subtype).subgroupOf K = Subgroup.center ↥K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hle : (Subgroup.center ↥K).map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hnorm : (((Subgroup.center ↥K).map K.subtype).subgroupOf K).Normal := by
    rw [heq]; infer_instance
  let e0 : ↥K ⧸ ((Subgroup.center ↥K).map K.subtype).subgroupOf K ≃* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.quotientMulEquivOfEq heq
  have hsimple : IsSimpleGroup (↥K ⧸ ((Subgroup.center ↥K).map K.subtype).subgroupOf K) :=
    haveI := hK.2.1
    e0.isSimpleGroup
  have hnab : ∃ a b : ↥K ⧸ ((Subgroup.center ↥K).map K.subtype).subgroupOf K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hK.2.2
    exact ⟨e0.symm a, e0.symm b, fun h => hab (by simpa using congrArg e0 h)⟩
  obtain ⟨i, ⟨e⟩⟩ := hX K ((Subgroup.center ↥K).map K.subtype) hle hsimple hnab
  exact ⟨i, ⟨e0.symm.trans e⟩⟩

theorem commutator_eq_bot_of_isComponent_of_not_three_dvd
    (X : Type) [Group X] [Finite X] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ) (hK : CFSG.Open.IsKGroup X)
    (hO2 : CFSG.pCore 2 X = ⊥) (A : Subgroup X) (hAel : CFSG.IsElementaryAbelian 2 A)
    (hAbest : CFSG.RankThree.FFModules.IsBestOffender ρ A) (K : Subgroup X)
    (hKc : CFSG.IsComponent K) (hK3 : ¬ 3 ∣ Nat.card K) : ⁅K, A⁆ = ⊥ := by
  by_contra hKA
  have hKo : CFSG.Open.IsComponentOf K ⊤ := (CFSG.isComponent_iff_open K).mp hKc
  obtain ⟨V, _, _, f, E, hV, hf0, hirr, hEN, hE0, hEel, hEq, hoff⟩ :=
    GeneralFF.componentSectionProp X W ρ hρ hO2 A hAel hAbest K hKo hKA
  have hKq : CFSG.IsQuasisimple ↥K := hKc.1
  obtain ⟨hLq, ⟨e⟩⟩ := Family.quasisimple_range_centerQuotientEquiv hKq f hf0
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKq.2.1
  have hnab : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a := hKq.2.2
  have hcat : CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) :=
    isCatalogGroup_centerQuotient hK hKq
  have h3 : ¬ 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := fun h3 =>
    hK3 (h3.trans (Subgroup.card_quotient_dvd_card _))
  obtain ⟨f', -, a, ha, K₀, _, _, hf', hK₀, ⟨β⟩⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd
      (↥K ⧸ Subgroup.center ↥K) hnab hcat h3
  have : Nontrivial V := hirr.1
  have hK₀' : Nat.card K₀ = 2 ^ (2 * a + 1) := by rw [hK₀, hf']
  have hlt := (Family.suzuki_irreducible_normalizer_excludes a ha hK₀' V hV f.range hLq.1
    hirr.2 (e.trans β)).2.2.2.2 E hE0 hEel hEN
  omega

section Transport

open CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def binRep (θ : V ≃* Multiplicative W) (X : Subgroup (MulAut V)) :
    Representation (ZMod 2) ↥X W :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ((binPsi θ).toMonoidHom.comp X.subtype)

theorem binRep_apply (θ : V ≃* Multiplicative W) (X : Subgroup (MulAut V)) (x : ↥X) (w : W) :
    binRep θ X x w = binPsi θ (x : MulAut V) w := rfl

theorem binRep_injective (θ : V ≃* Multiplicative W) (X : Subgroup (MulAut V)) :
    Function.Injective (binRep θ X) := by
  intro x y h
  apply Subtype.ext
  apply (binPsi θ).injective
  refine LinearEquiv.ext fun w => ?_
  have := LinearMap.congr_fun h w
  rwa [binRep_apply, binRep_apply] at this

theorem card_fixSub_binRep (θ : V ≃* Multiplicative W) (X : Subgroup (MulAut V))
    (B : Subgroup ↥X) :
    Nat.card ↥(CFSG.RankThree.FFModules.fixSub (binRep θ X) B) =
      Nat.card ↥(fixV (B.map X.subtype)) := by
  rw [← natCard_fixGL_map θ (B.map X.subtype)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  simp only [CFSG.RankThree.FFModules.mem_fixSub]
  constructor
  · intro h a ⟨y, ⟨b, hb, hby⟩, hya⟩
    subst hya; subst hby
    exact h b hb
  · intro h b hb
    exact h _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩

end Transport

theorem commute_of_isFFStarOffender_of_isComponent
    {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (hK : CFSG.Open.IsKGroup ↥X)
    (hO2 : CFSG.pCore 2 ↥X = ⊥) {A : Subgroup (MulAut V)}
    (hA : CFSG.Quasithin.IsFFStarOffender X A) {K : Subgroup ↥X} (hKc : CFSG.IsComponent K)
    (hK3 : ¬ 3 ∣ Nat.card K) : ∀ a ∈ A, ∀ k ∈ K, a * (k : MulAut V) = (k : MulAut V) * a := by
  classical
  have hfin : Finite (MulAut V) :=
    Finite.of_injective (fun g : MulAut V => (g : V → V)) DFunLike.coe_injective
  have : Finite ↥X := inferInstance
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary
    (fun v : V => by simpa [sq] using hV v)
  obtain ⟨hAX, hA0, hAel, hAbest⟩ := hA
  set A' : Subgroup ↥X := A.subgroupOf X with hA'
  have hAmap : A'.map X.subtype = A := by
    rw [hA', Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.mpr hAX
  have hAel' : CFSG.IsElementaryAbelian 2 ↥A' := by
    refine Layer.Actor.isElementaryAbelian_two_of (fun a ha b hb => ?_) (fun a ha => ?_)
    · exact Subtype.ext (hAel.1 _ ha _ hb)
    · exact Subtype.ext (hAel.2 _ ha)
  have hbest : CFSG.RankThree.FFModules.IsBestOffender (binRep θ X) A' := by
    intro B hB
    have hBA : B.map X.subtype ≤ A := hAmap ▸ Subgroup.map_mono hB
    have h := hAbest _ hBA
    have e1 : Nat.card ↥B = Nat.card ↥(B.map X.subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective B X.subtype X.subtype_injective).toEquiv
    have e2 : Nat.card ↥A' = Nat.card ↥A :=
      (Nat.card_congr (Subgroup.equivMapOfInjective A' X.subtype X.subtype_injective).toEquiv).trans
        (by rw [hAmap])
    rw [card_fixSub_binRep θ X B, card_fixSub_binRep θ X A', hAmap, e2, e1]
    exact h
  intro a ha k hk
  have hcomm := commutator_eq_bot_of_isComponent_of_not_three_dvd ↥X W (binRep θ X)
    (binRep_injective θ X) hK hO2 A' hAel' hbest K hKc hK3
  have ha' : (⟨a, hAX ha⟩ : ↥X) ∈ A' := by rw [hA', Subgroup.mem_subgroupOf]; exact ha
  have h1 : ⁅k, (⟨a, hAX ha⟩ : ↥X)⁆ ∈ ⁅K, A'⁆ := Subgroup.commutator_mem_commutator hk ha'
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact (congrArg Subtype.val h1).symm

section ThreeConstrained

theorem le_pPrimeCore_of_isPerfect_of_le_Op {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime]
    {K : Subgroup X} (hK : Group.IsPerfect ↥K) (hKR : K ≤ CFSG.Op_p'p p X) :
    K ≤ CFSG.pPrimeCore p X := by
  classical
  have := hK
  let f : ↥K →* X ⧸ CFSG.pPrimeCore p X := (QuotientGroup.mk' _).comp K.subtype
  have hr : f.range ≤ CFSG.pCore p (X ⧸ CFSG.pPrimeCore p X) := by
    rintro _ ⟨k, rfl⟩
    exact hKR k.2
  have hp : IsPGroup p ↥f.range := CFSG.pCore_isPGroup.to_le hr
  have : Group.IsNilpotent ↥f.range := hp.isNilpotent
  have : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have hsub : Subsingleton ↥f.range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (G := ↥f.range) inferInstance
  intro k hk
  have h1 : f ⟨k, hk⟩ ∈ f.range := ⟨_, rfl⟩
  have h2 : (⟨f ⟨k, hk⟩, h1⟩ : ↥f.range) = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff k).mp (congrArg Subtype.val h2)

theorem not_three_dvd_card_of_isComponent {X : Type*} [Group X] [Finite X]
    (hX : CFSG.ABGLocalTools.IsPConstrained 3 X) {K : Subgroup X} (hK : CFSG.IsComponent K) :
    ¬ 3 ∣ Nat.card K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR : K ≤ CFSG.Op_p'p 3 X := by
    rcases CFSG.LocalCores.component_normal_subgroup hK
      (inferInstance : (CFSG.Op_p'p 3 X).Normal) with h | h
    · exact h
    · obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (CFSG.Op_p'p 3 X)
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact (h.trans (Subgroup.centralizer_le hP.le)).trans (hX P hP)
  have hle := le_pPrimeCore_of_isPerfect_of_le_Op hK.1.1 hR
  intro h3
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := X)) (h3.trans (Subgroup.card_dvd_of_le hle))

end ThreeConstrained

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81
