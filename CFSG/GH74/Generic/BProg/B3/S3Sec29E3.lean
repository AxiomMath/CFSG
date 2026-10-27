module

public import CFSG.GH74.Generic.BProg.B3.S3Boot152
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Th2P61A7
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
  CFSG.GH74.GLS.Th2.Bal CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

namespace S3Sec29E3

@[expose] def A7Dich : Prop :=
  ∀ E : Subgroup (Equiv.Perm (Fin 7)), CFSG.IsElementaryAbelian 2 ↥E → 2 ≤ pRank 2 ↥E →
    (alternatingGroup (Fin 7) ≤ ⨆ (F : Subgroup (Equiv.Perm (Fin 7))) (_ : F ≤ E)
      (_ : pRank 2 ↥E - 1 ≤ pRank 2 ↥F), centralizer (F : Set (Equiv.Perm (Fin 7))) ⊓
        alternatingGroup (Fin 7)) ∨
    ∃ F₀ : Subgroup (Equiv.Perm (Fin 7)), F₀ ≤ E ∧ GLS.Th2.Obs.IsRootFour F₀

section Generic

theorem card_eq_card_range_mul_card_ker {A B : Type*} [Group A] [Group B] (f : A →* B) :
    Nat.card A = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem card_comap_of_surjective {X Y : Type*} [Group X] [Group Y] [Finite X] (g : X →* Y)
    (hg : Function.Surjective g) (S : Subgroup Y) :
    Nat.card (S.comap g) = Nat.card S * Nat.card g.ker := by
  have hY : Finite Y := Finite.of_surjective g hg
  have h1 : Nat.card X = Nat.card Y * Nat.card g.ker := by
    have := card_eq_card_range_mul_card_ker g
    rwa [MonoidHom.range_eq_top.mpr hg, Subgroup.card_top] at this
  have h2 := Subgroup.card_mul_index (S.comap g)
  have h3 := Subgroup.card_mul_index S
  have h4 : (S.comap g).index = S.index := Subgroup.index_comap_of_surjective S hg
  have h5 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [h4] at h2
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h5)
  rw [h2, h1, ← h3]
  ring

theorem card_preimage_mul {M H : Type*} [Group M] [Finite M] [Group H] (ψ : M →* H)
    (B' : Subgroup M) (F : Subgroup H) (hF : F ≤ B'.map ψ) :
    Nat.card (B' ⊓ F.comap ψ : Subgroup M) * Nat.card (B'.map ψ) = Nat.card F * Nat.card B' := by
  set θ : ↥B' →* ↥(B'.map ψ) := ψ.subgroupMap B' with hθ
  have hθs : Function.Surjective θ := ψ.subgroupMap_surjective B'
  set S : Subgroup ↥(B'.map ψ) := F.subgroupOf (B'.map ψ) with hS
  have h1 := card_comap_of_surjective θ hθs S
  have h2 : Nat.card B' = Nat.card (B'.map ψ) * Nat.card θ.ker := by
    have := card_eq_card_range_mul_card_ker θ
    rwa [MonoidHom.range_eq_top.mpr hθs, Subgroup.card_top] at this
  have h3 : Nat.card S = Nat.card F := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv
  have h4 : (S.comap θ).map B'.subtype = B' ⊓ F.comap ψ := by
    ext m
    simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_inf, hS, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, hb⟩
    · rintro ⟨hm, hψ⟩
      exact ⟨⟨m, hm⟩, hψ, rfl⟩
  have h5 : Nat.card (B' ⊓ F.comap ψ : Subgroup M) = Nat.card (S.comap θ) := by
    rw [← h4, Subgroup.card_map_of_injective B'.subtype_injective]
  rw [h5, h1, h3, h2]
  ring

theorem map_inf_centralizer_eq {GroupType ImageType : Type*} [Group GroupType] [Group ImageType]
    (φ : GroupType →* ImageType) (hker : Odd (Nat.card φ.ker))
    (actor target : Subgroup GroupType) (hact : IsPGroup 2 actor)
    (hnorm : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    (target ⊓ Subgroup.centralizer (actor : Set GroupType)).map φ =
      target.map φ ⊓ Subgroup.centralizer (actor.map φ : Set ImageType) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _action := CFSG.SignalizerFunctor.Helpers.conjugationAction actor target hnorm
  apply le_antisymm
  · rintro imageElement ⟨element, member, rfl⟩
    refine ⟨⟨element, member.1, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro imageActor ⟨actorElement, actor_member, rfl⟩
    simpa only [map_mul] using congrArg φ
      (Subgroup.mem_centralizer_iff.mp member.2 actorElement actor_member)
  · intro imageElement member
    obtain ⟨element, element_member, image_eq⟩ := member.1
    let restricted := φ.domRestrict target
    let fibre : SubMulAction actor target :=
      ⟨{representative | restricted representative = imageElement}, by
        intro actorElement representative representative_member
        change φ (actorElement.val * representative.val * actorElement.val⁻¹) = imageElement
        rw [map_mul, map_mul, map_inv]
        change φ actorElement.val * restricted representative * (φ actorElement.val)⁻¹ =
          imageElement
        rw [representative_member]
        have commutes := Subgroup.mem_centralizer_iff.mp member.2
          (φ actorElement.val) (Subgroup.mem_map_of_mem φ actorElement.property)
        rw [commutes, mul_assoc, mul_inv_cancel, mul_one]⟩
    have fibre_card : Nat.card fibre = Nat.card restricted.ker := by
      have fibre_eq : {representative : target | restricted representative = imageElement} =
          restricted ⁻¹' {restricted (⟨element, element_member⟩ : target)} := by
        ext representative
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
        change (restricted representative = imageElement) ↔ restricted representative = φ element
        rw [image_eq]
      exact (Nat.card_congr (Set.equivOfEq fibre_eq)).trans
        (Nat.card_congr (restricted.fiberEquivKer (⟨element, element_member⟩ : target)))
    have hkerdvd : Nat.card restricted.ker ∣ Nat.card φ.ker := by
      let ι : restricted.ker →* φ.ker :=
        { toFun := fun x => ⟨x.1.1, MonoidHom.mem_ker.mp x.2⟩
          map_one' := rfl
          map_mul' := fun x y => rfl }
      refine Subgroup.card_dvd_of_injective ι fun x y hxy => ?_
      have h1 := congrArg (fun z : ↥φ.ker => (z : GroupType)) hxy
      exact Subtype.ext (Subtype.ext h1)
    have not_divides : ¬ 2 ∣ Nat.card fibre := by
      rw [fibre_card]
      exact Nat.prime_two.coprime_iff_not_dvd.mp
        ((Nat.coprime_two_left.mpr hker).of_dvd_right hkerdvd)
    obtain ⟨representative, fixed⟩ :=
      hact.nonempty_fixed_point_of_prime_not_dvd_card fibre not_divides
    refine ⟨representative.val.val, ⟨representative.val.property, ?_⟩, representative.property⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro actorElement actor_member
    have equality := congrArg (fun fixedElement : fibre => fixedElement.val.val)
      (fixed (⟨actorElement, actor_member⟩ : actor))
    change actorElement * representative.val.val * actorElement⁻¹ = representative.val.val
      at equality
    exact mul_inv_eq_iff_eq_mul.mp equality

theorem exists_lift {M : Type*} [Group M] [Finite M] (T O U : Subgroup M) [hO : O.Normal]
    (hOodd : Odd (Nat.card O)) (hU2 : IsPGroup 2 U) (hUT : U ≤ normalizer (T : Set M))
    {x : M} (hx : x ∈ T) (hcomm : ∀ u ∈ U, ⁅x, u⁆ ∈ O) :
    ∃ x' ∈ T, (∀ u ∈ U, x' * u = u * x') ∧ x⁻¹ * x' ∈ O := by
  have hker : Odd (Nat.card (QuotientGroup.mk' O).ker) := by
    rw [QuotientGroup.ker_mk']
    exact hOodd
  have h := map_inf_centralizer_eq (QuotientGroup.mk' O) hker U T hU2 hUT
  have hmem : (QuotientGroup.mk' O) x ∈ T.map (QuotientGroup.mk' O) ⊓
      Subgroup.centralizer ((U.map (QuotientGroup.mk' O) : Subgroup _) : Set (M ⧸ O)) := by
    refine ⟨⟨x, hx, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have h1 : (QuotientGroup.mk' O) ⁅x, u⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hcomm u hu)
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  rw [← h] at hmem
  obtain ⟨x', ⟨hx'T, hx'C⟩, hx'eq⟩ := hmem
  refine ⟨x', hx'T, fun u hu => (Subgroup.mem_centralizer_iff.mp hx'C u hu).symm, ?_⟩
  exact (QuotientGroup.eq).mp hx'eq.symm

end Generic

section Gamma

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_preimage {B M : Subgroup G} (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hB4 : pRank 2 ↥B = 4) (hBM : B ≤ M) (ψ : ↥M →* Equiv.Perm (Fin 7))
    (F : Subgroup (Equiv.Perm (Fin 7))) (hFE : F ≤ (B.subgroupOf M).map ψ)
    (hFr : pRank 2 ↥((B.subgroupOf M).map ψ) - 1 ≤ pRank 2 ↥F) :
    3 ≤ pRank 2 ↥(((B.subgroupOf M) ⊓ F.comap ψ).map M.subtype) := by
  classical
  obtain ⟨-, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  set B' : Subgroup ↥M := B.subgroupOf M with hB'
  set E : Subgroup (Equiv.Perm (Fin 7)) := B'.map ψ with hE
  set U : Subgroup ↥M := B' ⊓ F.comap ψ with hU
  have hB'sq : ∀ m ∈ B', m * m = 1 := fun m hm =>
    Subtype.ext (hBsq _ (Subgroup.mem_subgroupOf.mp hm))
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul, hB'sq m hm, map_one]
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := isElementaryAbelian_two_of_sq E hEsq
  have hFel : CFSG.IsElementaryAbelian 2 ↥F :=
    isElementaryAbelian_two_of_sq F (fun x hx => hEsq x (hFE hx))
  set Q : Subgroup G := U.map M.subtype with hQ
  have hQB : Q ≤ B := by
    rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hu.1
  have hQel : CFSG.IsElementaryAbelian 2 ↥Q := Th2Sig6.isElementaryAbelian_of_le hBel hQB
  have hcardQ : Nat.card Q = Nat.card U := Subgroup.card_map_of_injective M.subtype_injective
  have hcardB' : Nat.card B' = 16 := by
    rw [hB', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv,
      C3.Layer1.Back.card_eq_two_pow_pRank hBel, hB4]
    norm_num
  have h1 : Nat.card U * Nat.card E = Nat.card F * Nat.card B' := card_preimage_mul ψ B' F hFE
  rw [hcardB'] at h1
  have hEcard := C3.Layer1.Back.card_eq_two_pow_pRank hEel
  have hFcard := C3.Layer1.Back.card_eq_two_pow_pRank hFel
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have hEle : Nat.card E ≤ 2 * Nat.card F := by
    rw [hEcard, hFcard]
    calc 2 ^ pRank 2 ↥E ≤ 2 ^ (pRank 2 ↥F + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 * 2 ^ pRank 2 ↥F := by ring
  have h8 : 8 ≤ Nat.card U := by
    by_contra hlt
    push Not at hlt
    have h2 : Nat.card U * Nat.card E ≤ 7 * (2 * Nat.card F) := Nat.mul_le_mul (by omega) hEle
    omega
  have h9 : 2 ^ 3 ≤ 2 ^ pRank 2 ↥Q := by
    rw [← C3.Layer1.Back.card_eq_two_pow_pRank hQel, hcardQ]
    exact h8
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h9

theorem le_gammaK_of_generated {B J : Subgroup G} {y : G}
    (hcomp : IsPCompIn 2 (centralizer ({y} : Set G)) J) (hyB : y ∈ B)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB4 : pRank 2 ↥B = 4)
    (hBN : B ≤ normalizer (J : Set G)) (hcen : CenterlessBar J)
    (e : kBar J ≃* alternatingGroup (Fin 7))
    (hgen : alternatingGroup (Fin 7) ≤ ⨆ (F : Subgroup (Equiv.Perm (Fin 7)))
      (_ : F ≤ (B.subgroupOf (normalizer (J : Set G))).map (a7Act J e))
      (_ : pRank 2 ↥((B.subgroupOf (normalizer (J : Set G))).map (a7Act J e)) - 1 ≤ pRank 2 ↥F),
      centralizer (F : Set (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) :
    J ≤ gammaK 2 B 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  set M : Subgroup G := normalizer (J : Set G) with hM
  set ψ : ↥M →* Equiv.Perm (Fin 7) := a7Act J e with hψ
  set B' : Subgroup ↥M := B.subgroupOf M with hB'
  set E : Subgroup (Equiv.Perm (Fin 7)) := B'.map ψ with hE
  set Γ : Subgroup G := gammaK 2 B 3 with hΓ
  set O : Subgroup G := pPrimeCoreOf 2 J with hO
  have hOJ : O ≤ J := TwoThin.pPrimeCoreOf_le J
  have hOΓ : O ≤ Γ := (pPrimeCoreOf_le_of_pCompIn hcomp).trans
    (S3Boot152.pPrimeCoreOf_centralizer_le hBel hB4 (le_refl Γ) hyB)
  have hker : ∀ z : ↥M, ψ z = 1 → (z : G) ∈ J → (z : G) ∈ O := by
    intro z hz hzJ
    have h1 : (z : G) ∈ centralizerSection J (pPrimeCoreOf 2 J) :=
      (barAct_eq_one_iff z).mp ((a7Act_eq_one_iff e z).mp hz)
    exact mem_pPrimeCoreOf_of_commutators hcen hzJ (fun k hk => h1.2.2 k hk)
  have hψJ : ∀ (k : G) (hk : k ∈ J), ψ ⟨k, Subgroup.le_normalizer hk⟩ =
      ((e (QuotientGroup.mk (⟨k, hk⟩ : ↥J)) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) :=
    fun k hk => a7Act_of_mem e hk
  have hψO : ∀ (z : ↥M), (z : G) ∈ O → ψ z = 1 := by
    intro z hz
    have hzJ : (z : G) ∈ J := hOJ hz
    have h1 : ψ z = ψ ⟨(z : G), Subgroup.le_normalizer hzJ⟩ := rfl
    rw [h1, hψJ _ hzJ]
    obtain ⟨g, hg, hgz⟩ := hz
    have h2 : (QuotientGroup.mk (⟨(z : G), hzJ⟩ : ↥J) : kBar J) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      have : (⟨(z : G), hzJ⟩ : ↥J) = g := Subtype.ext hgz.symm
      rw [this]
      exact hg
    rw [h2, map_one]
    rfl
  have hOodd : Odd (Nat.card (O.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOJ.trans Subgroup.le_normalizer)).toEquiv]
    exact TwoThin.card_pPrimeCoreOf_odd J
  have hOn : (O.subgroupOf M).Normal := by
    refine ⟨fun n hn m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hmO : (m : G) ∈ normalizer (O : Set G) := TwoThin.mem_normalizer_pPrimeCoreOf m.2
    have := (Subgroup.mem_normalizer_iff.mp hmO (n : G)).mp hn
    simpa using this
  set T : Subgroup (Equiv.Perm (Fin 7)) := ((Γ ⊓ J).subgroupOf M).map ψ with hT
  have hgenT : ∀ F : Subgroup (Equiv.Perm (Fin 7)), F ≤ E → pRank 2 ↥E - 1 ≤ pRank 2 ↥F →
      centralizer (F : Set (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ≤ T := by
    intro F hFE hFr σ hσ
    obtain ⟨hσC, hσA⟩ := hσ
    obtain ⟨kb, hkb⟩ := e.surjective ⟨σ, hσA⟩
    induction kb using QuotientGroup.induction_on with | H k => ?_
    have hx₀J : (k : G) ∈ J := k.2
    set x₀ : ↥M := ⟨(k : G), Subgroup.le_normalizer hx₀J⟩ with hx₀
    have hσψ : ψ x₀ = σ := by
      rw [hx₀, hψJ _ hx₀J]
      exact congrArg Subtype.val hkb
    set U : Subgroup ↥M := B' ⊓ F.comap ψ with hU
    have hUsq : ∀ u ∈ U, u * u = 1 := fun u hu =>
      Subtype.ext (hBsq _ (Subgroup.mem_subgroupOf.mp hu.1))
    have hU2 : IsPGroup 2 ↥U := (isElementaryAbelian_two_of_sq U hUsq).isPGroup 2 _
    have hUT : U ≤ normalizer ((J.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
      intro u hu
      rw [Subgroup.mem_normalizer_iff]
      intro t
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have := Subgroup.mem_normalizer_iff.mp u.2 (t : G)
      simpa using this
    have hcomm : ∀ u ∈ U, ⁅x₀, u⁆ ∈ O.subgroupOf M := by
      intro u hu
      have hψu : ψ u ∈ F := hu.2
      have hcomm1 : ψ u * σ = σ * ψ u := Subgroup.mem_centralizer_iff.mp hσC _ hψu
      have h1 : ψ ⁅x₀, u⁆ = 1 := by
        rw [map_commutatorElement, hσψ]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm1.symm
      rw [Subgroup.mem_subgroupOf]
      refine hker _ h1 ?_
      have hc : ((⁅x₀, u⁆ : ↥M) : G) = (k : G) * ((u : G) * (k : G)⁻¹ * (u : G)⁻¹) := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hx₀]
        group
      rw [hc]
      exact J.mul_mem hx₀J ((Subgroup.mem_normalizer_iff.mp u.2 _).mp (J.inv_mem hx₀J))
    have hx₀T : x₀ ∈ J.subgroupOf M := hx₀J
    obtain ⟨x', hx'T, hx'C, hx'O⟩ := exists_lift (J.subgroupOf M) (O.subgroupOf M) U hOodd hU2 hUT
      hx₀T hcomm
    have hx'J : (x' : G) ∈ J := hx'T
    have hQB : U.map M.subtype ≤ B := by
      rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hu.1
    have hQr : 3 ≤ pRank 2 ↥(U.map M.subtype) :=
      three_le_pRank_preimage hBel hB4 hBN ψ F hFE hFr
    have hx'cent : (x' : G) ∈ centralizer ((U.map M.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, hu, rfl⟩
      exact congrArg Subtype.val (hx'C u hu).symm
    have hx'Γ : (x' : G) ∈ Γ :=
      (le_iSup₂_of_le (U.map M.subtype) hQB (le_iSup_of_le hQr le_rfl) :
        normalizer ((U.map M.subtype : Subgroup G) : Set G) ≤ Γ)
        (Subgroup.centralizer_le_normalizer _ hx'cent)
    have hψx' : ψ x' = σ := by
      have h1 : ψ (x₀⁻¹ * x') = 1 := hψO _ (Subgroup.mem_subgroupOf.mp hx'O)
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      exact h1.symm.trans hσψ
    exact Subgroup.mem_map.mpr ⟨x', Subgroup.mem_subgroupOf.mpr ⟨hx'Γ, hx'J⟩, hψx'⟩
  have hAT : alternatingGroup (Fin 7) ≤ T :=
    hgen.trans (iSup_le fun F => iSup_le fun hFE => iSup_le fun hFr => hgenT F hFE hFr)
  intro x hxJ
  set x₁ : ↥M := ⟨x, Subgroup.le_normalizer hxJ⟩ with hx₁
  have hψx : ψ x₁ ∈ alternatingGroup (Fin 7) := by
    rw [hx₁, hψJ x hxJ]
    exact (e _).2
  obtain ⟨m, hm, hψm⟩ := Subgroup.mem_map.mp (hAT hψx)
  have hmΓ : (m : G) ∈ Γ := (Subgroup.mem_subgroupOf.mp hm).1
  have hmJ : (m : G) ∈ J := (Subgroup.mem_subgroupOf.mp hm).2
  have hz1 : ψ (m⁻¹ * x₁) = 1 := by
    rw [map_mul, map_inv, hψm]
    exact inv_mul_cancel _
  have hzJ : ((m⁻¹ * x₁ : ↥M) : G) ∈ J := J.mul_mem (J.inv_mem hmJ) hxJ
  have hzO := hker _ hz1 hzJ
  have hx : x = (m : G) * ((m⁻¹ * x₁ : ↥M) : G) := by
    simp [hx₁]
  rw [hx]
  exact Γ.mul_mem hmΓ (hOΓ hzO)

end Gamma

section CaseB

variable {G : Type} [Group G] [Finite G]

theorem caseB (hDich : A7Dich) {B J : Subgroup G} {y : G}
    (hcomp : IsPCompIn 2 (centralizer ({y} : Set G)) J) (hyB : y ∈ B)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB4 : pRank 2 ↥B = 4)
    (hBN : B ≤ normalizer (J : Set G)) (hcen : CenterlessBar J)
    (e : kBar J ≃* alternatingGroup (Fin 7))
    (hcard : 2 ^ 2 * Nat.card ↥(B ⊓ centralizerSection J (pPrimeCoreOf 2 J)) ≤ Nat.card ↥B)
    (hnot : ¬ J ≤ gammaK 2 B 3) :
    ∃ F₀ F₁ : Subgroup (Equiv.Perm (Fin 7)), IsRootFour F₀ ∧
      (F₁ = ⊥ ∨ ∃ t : Equiv.Perm (Fin 7), t.IsSwap ∧ F₁ = zpowers t ∧
        ∀ i, (∃ f ∈ F₀, f i ≠ i) → t i = i) ∧
      (B.subgroupOf (normalizer (J : Set G))).map (a7Act J e) = F₀ ⊔ F₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  set M : Subgroup G := normalizer (J : Set G) with hM
  set ψ : ↥M →* Equiv.Perm (Fin 7) := a7Act J e with hψ
  set B' : Subgroup ↥M := B.subgroupOf M with hB'
  set E : Subgroup (Equiv.Perm (Fin 7)) := B'.map ψ with hE
  have hB'sq : ∀ m ∈ B', m * m = 1 := fun m hm =>
    Subtype.ext (hBsq _ (Subgroup.mem_subgroupOf.mp hm))
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul, hB'sq m hm, map_one]
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := isElementaryAbelian_two_of_sq E hEsq
  have hkerE : (B' ⊓ ψ.ker).map M.subtype = B ⊓ centralizerSection J (pPrimeCoreOf 2 J) := by
    ext x
    constructor
    · rintro ⟨m, ⟨hmB, hm1⟩, rfl⟩
      exact ⟨hmB, (barAct_eq_one_iff m).mp ((a7Act_eq_one_iff e m).mp hm1)⟩
    · rintro ⟨hxB, hxS⟩
      exact ⟨⟨x, hxS.1⟩, ⟨hxB, (a7Act_eq_one_iff e _).mpr ((barAct_eq_one_iff _).mpr hxS)⟩, rfl⟩
  have h1 : Nat.card (B' ⊓ (⊥ : Subgroup (Equiv.Perm (Fin 7))).comap ψ : Subgroup ↥M) * Nat.card E =
      Nat.card (⊥ : Subgroup (Equiv.Perm (Fin 7))) * Nat.card B' :=
    card_preimage_mul ψ B' ⊥ bot_le
  rw [MonoidHom.comap_bot, Subgroup.card_bot, one_mul] at h1
  have h2 : Nat.card (B' ⊓ ψ.ker : Subgroup ↥M) =
      Nat.card ↥(B ⊓ centralizerSection J (pPrimeCoreOf 2 J)) := by
    rw [← hkerE, Subgroup.card_map_of_injective M.subtype_injective]
  have h3 : Nat.card B' = Nat.card ↥B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  rw [h2, h3] at h1
  have hpos : 0 < Nat.card ↥(B ⊓ centralizerSection J (pPrimeCoreOf 2 J)) := Nat.card_pos
  have hE4 : 4 ≤ Nat.card E := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(B ⊓ centralizerSection J (pPrimeCoreOf 2 J)) * Nat.card E <
        2 ^ 2 * Nat.card ↥(B ⊓ centralizerSection J (pPrimeCoreOf 2 J)) := by
      rw [mul_comm]
      exact Nat.mul_lt_mul_of_pos_right (by omega) hpos
    omega
  have hE2 : 2 ≤ pRank 2 ↥E := by
    have h4 : 2 ^ 2 ≤ 2 ^ pRank 2 ↥E := by
      rw [← C3.Layer1.Back.card_eq_two_pow_pRank hEel]
      exact hE4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
  rcases hDich E hEel hE2 with hgen | ⟨F₀, hF₀E, hF₀⟩
  · exact absurd (le_gammaK_of_generated hcomp hyB hBel hB4 hBN hcen e hgen) hnot
  · obtain ⟨hEc, hE2'⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hEel
    by_cases hEF : E ≤ F₀
    · refine ⟨F₀, ⊥, hF₀, Or.inl rfl, ?_⟩
      rw [sup_bot_eq]
      exact le_antisymm hEF hF₀E
    · obtain ⟨t, ht, hdisj, hEeq⟩ := a7_E_structure hF₀ hF₀E hE2' hEc hEF
      exact ⟨F₀, zpowers t, hF₀, Or.inr ⟨t, ht, rfl, hdisj⟩, hEeq⟩

end CaseB

end S3Sec29E3

end CFSG.GH74.Generic.BProg.B3
