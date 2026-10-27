module

public import CFSG.CGT.PushingUpLit.EightOneWindowBasic

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.QuasithinUnique.Setup.Campbell CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement

namespace EightOneWindow

section Quotient

theorem sSup_ne_top_of_quotient_type {Q : Type*} [Group Q]
    (hQ : IsQuasisimple Q ∨ (Nat.card Q).Prime) {F : Set (Subgroup Q)}
    (hF : ∀ Y ∈ F, Y.Normal ∧ Y ≠ ⊤) : sSup F ≠ ⊤ := by
  intro htop
  rcases hQ with hq | hp
  · have hle : sSup F ≤ Subgroup.center Q := sSup_le fun Y hY =>
      ((CFSG.LocalCores.quasisimple_normal_subgroups hq (hF Y hY).1).resolve_left (hF Y hY).2)
    rw [htop, top_le_iff, Subgroup.center_eq_top_iff] at hle
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hle.is_comm.comm a b])
  · have : Fact (Nat.card Q).Prime := ⟨hp⟩
    have hle : sSup F ≤ ⊥ := sSup_le fun Y hY =>
      ((Subgroup.eq_bot_or_eq_top_of_prime_card Y).resolve_right (hF Y hY).2).le
    rw [htop, top_le_iff] at hle
    have h1 : Nat.card Q = 1 := by
      rw [← Subgroup.card_top (G := Q), ← hle, Subgroup.card_bot]
    exact hp.one_lt.ne' h1

theorem sSup_properNormal_ne_top {H : Type} [Group H] [Finite H] (hH : IsShortGroup H) :
    sSup {Y : Subgroup H | Y.Normal ∧ Y ≠ ⊤} ≠ ⊤ := by
  intro htop
  have hP : IsPGroup 2 (pCore 2 H) := pCore_isPGroup
  have hres : ∀ (N : Subgroup H) [N.Normal], IsPGroup 2 (H ⧸ N) → N = ⊤ := by
    intro N _ hN
    have hle : oResidualTwo H ≤ N := sInf_le ⟨inferInstance, hN⟩
    rw [hH.residual_eq, top_le_iff] at hle
    exact hle
  let π : H →* H ⧸ pCore 2 H := QuotientGroup.mk' (pCore 2 H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have key : ∀ Y ∈ {Y : Subgroup H | Y.Normal ∧ Y ≠ ⊤}, (Y.map π).Normal ∧ Y.map π ≠ ⊤ := by
    rintro Y ⟨hYn, hYtop⟩
    refine ⟨hYn.map π hπ, fun hmap => hYtop ?_⟩
    have := hYn
    refine hres Y ?_
    let f : pCore 2 H →* H ⧸ Y := (QuotientGroup.mk' Y).comp (pCore 2 H).subtype
    refine hP.of_surjective f fun q => ?_
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : π h ∈ Y.map π := by rw [hmap]; trivial
    obtain ⟨y, hy, hyh⟩ := h1
    have h2 : y⁻¹ * h ∈ pCore 2 H := (QuotientGroup.eq (s := pCore 2 H)).mp hyh
    refine ⟨⟨y⁻¹ * h, h2⟩, ?_⟩
    show ((y⁻¹ * h : H) : H ⧸ Y) = (h : H ⧸ Y)
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hYn.conj_mem y hy h⁻¹
  have hsup : sSup (Subgroup.map π '' {Y : Subgroup H | Y.Normal ∧ Y ≠ ⊤}) = ⊤ := by
    rw [sSup_image, ← (Subgroup.gc_map_comap π).l_sSup, htop, Subgroup.map_top_of_surjective π hπ]
  refine sSup_ne_top_of_quotient_type hH.quotient_type (fun Y hY => ?_) hsup
  obtain ⟨Y', hY', rfl⟩ := hY
  exact key Y' hY'

theorem characteristic_sSup_properNormal (H : Type*) [Group H] :
    (sSup {Y : Subgroup H | Y.Normal ∧ Y ≠ ⊤}).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  rw [(Subgroup.gc_map_comap φ.toMonoidHom).l_sSup]
  refine iSup₂_le fun Y hY => le_sSup ⟨hY.1.map φ.toMonoidHom φ.surjective, fun htop => hY.2 ?_⟩
  apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
  rw [htop, Subgroup.map_top_of_surjective _ φ.surjective]

end Quotient

section Commutator

variable {G : Type} [Group G]

theorem commutator_iSup_le {ι : Type*} {K E X : Subgroup G}
    (hE : K ≤ Subgroup.normalizer (E : Set G)) (A : ι → Subgroup G) (hA : ∀ i, A i ≤ K)
    (h : ∀ i, ⁅A i, X⁆ ≤ E) : ⁅⨆ i, A i, X⁆ ≤ E := by
  let T : Subgroup G :=
    { carrier := {a | a ∈ K ∧ ∀ x ∈ X, ⁅a, x⁆ ∈ E}
      one_mem' := ⟨one_mem K, fun x _ => by simp⟩
      mul_mem' := by
        rintro a₁ a₂ ⟨ha₁, h₁⟩ ⟨ha₂, h₂⟩
        refine ⟨mul_mem ha₁ ha₂, fun x hx => ?_⟩
        have e : ⁅a₁ * a₂, x⁆ = a₁ * ⁅a₂, x⁆ * a₁⁻¹ * ⁅a₁, x⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hE ha₁) _).mp (h₂ x hx)) (h₁ x hx)
      inv_mem' := by
        rintro a ⟨ha, h₁⟩
        refine ⟨inv_mem ha, fun x hx => ?_⟩
        have e : ⁅a⁻¹, x⁆ = a⁻¹ * (⁅a, x⁆)⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hE (inv_mem ha)) _).mp (inv_mem (h₁ x hx)) }
  have hT : ⨆ i, A i ≤ T := iSup_le fun i a ha =>
    ⟨hA i ha, fun x hx => h i (Subgroup.commutator_mem_commutator ha hx)⟩
  exact Subgroup.commutator_le.mpr fun a ha x hx => (hT ha).2 x hx

theorem conjugate_commutator_jIn [Finite G] (S X : Subgroup G) {k : G}
    (hk : k ∈ Subgroup.normalizer (X : Set G)) :
    conjugate ⁅jIn S, X⁆ k = ⁅jIn (conjugate S k), X⁆ := by
  have h1 : conjugate ⁅jIn S, X⁆ k = ⁅conjugate (jIn S) k, conjugate X k⁆ :=
    Subgroup.map_commutator _ _ _
  rw [h1, EightOneRel.conjugate_jIn, ThreeFromEight.conjugate_eq_self_of_mem_normalizer hk]

theorem jIn_le_iSup_conjugate [Finite G] {K S : Subgroup G} (hS : IsSylowOf 2 S K) :
    jIn K ≤ ⨆ k : K, jIn (conjugate S (k : G)) := by
  have hJK : jIn K = sSup (elemFamilyIn 2 K) := by
    rw [jIn_eq_elemThompsonIn, elemThompsonIn_eq]
  rw [hJK]
  refine sSup_le fun A hA => ?_
  obtain ⟨hAK, hAe, hAc⟩ := mem_elemFamilyIn.mp hA
  have hA2 : IsPGroup 2 A := by
    have := hAe
    exact IsElementaryAbelian.isPGroup 2 ↥A
  obtain ⟨S', hS', hAS'⟩ := Nine.exists_isSylowOf_ge hA2 hAK
  obtain ⟨k, hk, rfl⟩ := EightOneRel.exists_conjugate_eq_of_isSylowOf hS' hS
  have hr : pRank 2 ↥(conjugate S k) = pRank 2 ↥K := pRank_eq_of_isSylowOf hS'
  have hAfam : A ∈ elemFamilyIn 2 (conjugate S k) :=
    mem_elemFamilyIn.mpr ⟨hAS', hAe, by rw [hAc, hr]⟩
  have h1 := le_elemThompsonIn hAfam
  rw [← jIn_eq_elemThompsonIn] at h1
  exact h1.trans (le_iSup (fun k : K => jIn (conjugate S (k : G))) ⟨k, hk⟩)

end Commutator

end EightOneWindow

section LemmaJS

variable {G : Type} [Group G] [Finite G]

open EightOneWindow

theorem commutator_jIn_of_isSylowOf {X S : Subgroup G} (hX : InClassX ↥X)
    (hS : IsSylowOf 2 S (Subgroup.normalizer (X : Set G)))
    (h : X = ⁅jIn (Subgroup.normalizer (X : Set G)), X⁆) : X = ⁅jIn S, X⁆ := by
  have hSK : S ≤ Subgroup.normalizer (X : Set G) := hS.1
  have hZX : ⁅jIn S, X⁆ ≤ X :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp ((jIn_le S).trans hSK)
  refine le_antisymm ?_ hZX
  by_contra hne
  have hZne : ⁅jIn S, X⁆ ≠ X := fun h' => hne h'.symm.le
  have hE'top : sSup {Y : Subgroup ↥X | Y.Normal ∧ Y ≠ ⊤} ≠ ⊤ := sSup_properNormal_ne_top hX.1
  have hE'char : (sSup {Y : Subgroup ↥X | Y.Normal ∧ Y ≠ ⊤}).Characteristic :=
    characteristic_sSup_properNormal ↥X
  obtain ⟨E', hE'⟩ : ∃ E' : Subgroup ↥X, E' = sSup {Y : Subgroup ↥X | Y.Normal ∧ Y ≠ ⊤} :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G, E = E'.map X.subtype := ⟨_, rfl⟩
  rw [← hE'] at hE'top hE'char
  have hEX : E ≤ X := by
    rw [hE]
    exact Subgroup.map_subtype_le E'
  have hEsub : E.subgroupOf X = E' := by
    rw [hE]
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective E'
  have hKE : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    normalizer_le_normalizer_of_characteristic' hEX (by rw [hEsub]; exact hE'char)
  have hZE : ⁅jIn S, X⁆ ≤ E := by
    have hnormal : (⁅jIn S, X⁆.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZX).mpr
        (Subgroup.normalizer_commutator_ge_right _ _)
    have hne' : ⁅jIn S, X⁆.subgroupOf X ≠ ⊤ := fun htop =>
      hZne (le_antisymm hZX (Subgroup.subgroupOf_eq_top.mp htop))
    have h1 : ⁅jIn S, X⁆.subgroupOf X ≤ E' := by
      rw [hE']
      exact le_sSup ⟨hnormal, hne'⟩
    calc ⁅jIn S, X⁆ = (⁅jIn S, X⁆.subgroupOf X).map X.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hZX).symm
      _ ≤ E := by
          rw [hE]
          exact Subgroup.map_mono h1
  have hconj : ∀ k : Subgroup.normalizer (X : Set G), ⁅jIn (conjugate S (k : G)), X⁆ ≤ E := by
    intro k
    rw [← conjugate_commutator_jIn S X k.2]
    calc conjugate ⁅jIn S, X⁆ (k : G) ≤ conjugate E (k : G) := Subgroup.map_mono hZE
      _ = E := ThreeFromEight.conjugate_eq_self_of_mem_normalizer (hKE k.2)
  have hA : ∀ k : Subgroup.normalizer (X : Set G),
      jIn (conjugate S (k : G)) ≤ Subgroup.normalizer (X : Set G) := fun k =>
    (jIn_le _).trans (CFSG.GroupTheory.conjugate_le_of_mem hSK k.2)
  have hcomm := commutator_iSup_le hKE
    (fun k : Subgroup.normalizer (X : Set G) => jIn (conjugate S (k : G))) hA hconj
  have hXE : X ≤ E :=
    calc X = ⁅jIn (Subgroup.normalizer (X : Set G)), X⁆ := h
      _ ≤ ⁅⨆ k : Subgroup.normalizer (X : Set G), jIn (conjugate S (k : G)), X⁆ :=
          Subgroup.commutator_mono (jIn_le_iSup_conjugate hS) le_rfl
      _ ≤ E := hcomm
  exact hE'top (hEsub.symm.trans (Subgroup.subgroupOf_eq_top.mpr hXE))

end LemmaJS

end CFSG.CGT.PushingUpLit
