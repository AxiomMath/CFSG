module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoStageMRoot
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenDichAll
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenTransport

public section

namespace CFSG.OddStandard.AltStdCycTwo.StageM

open Subgroup AltStdSec

section Data

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

structure LiftData (e : L ≃* alternatingGroup (Fin n)) (z : G) : Prop where
  sq : z * z = 1
  canon : ∀ S : Finset (Fin n), S.card = 3 → ∃ Q : Subgroup G, CanonLift e z S Q
  root : ∀ S : Finset (Fin n), S.card = 3 →
    ∃ ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G, IsRootLift e z S ψ

end Data

section Disch

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {z : G}
  {e : L ≃* alternatingGroup (Fin n)}

theorem rootLift_bool_w (hz : z * z = 1) (hn : 11 ≤ n) {S : Finset (Fin n)}
    (hS : S.card = 3) {Q : Subgroup G} (hQ : CanonLift e z S Q)
    {ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G} (hψ : IsRootLift e z S ψ) :
    ∃ a : Bool, ∀ b, cjHom z a (ψ b) ∈ Q := by
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := G) e Sᶜ
  have hk : Sᶜ.card = n - 3 := by rw [card_compl_fin, hS]
  have hPC : ψ.range ≤ centralizer (corr (X := G) e (altSub S) : Set G) := by
    rintro _ ⟨b, rfl⟩
    exact hψ.cent b
  have hPP : ∀ a ∈ ψ.range, ∀ b ∈ ψ.range,
      a * (z * b * z⁻¹) = (z * b * z⁻¹) * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact hψ.comm a b
  let eP : ↥ψ.range ≃* alternatingGroup (Fin Sᶜ.card) :=
    (MonoidHom.ofInjective hψ.inj).symm.trans eB
  rcases hQ.absorb Sᶜ.card ψ.range (by omega) (by omega) (by omega) hPC ⟨eP⟩ hPP with hl | hr
  · exact ⟨false, fun b => hl ⟨b, rfl⟩⟩
  · refine ⟨true, fun b => ?_⟩
    obtain ⟨q, hq, hqb⟩ := hr ⟨b, rfl⟩
    have : z * ψ b * z⁻¹ = q := by
      rw [← hqb]
      show z * (z * q * z⁻¹) * z⁻¹ = q
      exact conj_conj_of_sq hz q
    show z * ψ b * z⁻¹ ∈ Q
    rw [this]; exact hq

theorem rootLift_rel_disjoint_w (hz : z * z = 1) (hn : 11 ≤ n) {S S' : Finset (Fin n)}
    (hS : S.card = 3) (hS' : S'.card = 3) (hdisj : Disjoint S S') {Q' : Subgroup G}
    (hQ' : CanonLift e z S' Q') {ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G}
    {ψ' : ↥(corr (X := G) e (altSub S'ᶜ)) →* G} (hψ : IsRootLift e z S ψ)
    (hψ' : IsRootLift e z S' ψ') :
    ∃ c : Bool, ∀ (x : G) (hx : x ∈ corr (X := G) e (altSub Sᶜ))
      (hx' : x ∈ corr (X := G) e (altSub S'ᶜ)), ψ ⟨x, hx⟩ = cjHom z c (ψ' ⟨x, hx'⟩) := by
  obtain ⟨U, hU⟩ : ∃ U : Finset (Fin n), U = (S ∪ S')ᶜ := ⟨_, rfl⟩
  have hUc : U.card = n - 6 := by
    rw [hU, card_compl_fin, Finset.card_union_of_disjoint hdisj, hS, hS']
  have hUS : U ⊆ Sᶜ := fun i hi => by
    simp only [hU, Finset.mem_compl, Finset.mem_union, not_or] at hi ⊢
    exact hi.1
  have hDB : corr (X := G) e (altSub U) ≤ corr (X := G) e (altSub Sᶜ) :=
    corr_mono e (altSub_mono hUS)
  have hS'S : S' ⊆ Sᶜ := fun i hi => by
    simp only [Finset.mem_compl]
    exact fun hiS => Finset.disjoint_left.1 hdisj hiS hi
  have hR'B : corr (X := G) e (altSub S') ≤ corr (X := G) e (altSub Sᶜ) :=
    corr_mono e (altSub_mono hS'S)
  have hUS' : Disjoint U S' := Finset.disjoint_left.2 fun i hi hi' => by
    simp only [hU, Finset.mem_compl, Finset.mem_union, not_or] at hi
    exact hi.2 hi'
  let P : Subgroup G := ((corr (X := G) e (altSub U)).subgroupOf
    (corr (X := G) e (altSub Sᶜ))).map ψ
  have hPC : P ≤ centralizer (corr (X := G) e (altSub S') : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_iff]
    intro r hr
    have hrr : ψ ⟨r, hR'B hr⟩ * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹) = r := hψ.diag ⟨r, hR'B hr⟩
    have hdc : d * ⟨r, hR'B hr⟩ = ⟨r, hR'B hr⟩ * d :=
      Subtype.ext (corr_comm e (T₁ := altSub U) (T₂ := altSub S')
        (fun g hg g' hg' => comm_of_altSub_disjoint hUS' hg hg') (d : G) hd r hr)
    have hψc := hψ.comm d ⟨r, hR'B hr⟩
    calc r * ψ d = (ψ ⟨r, hR'B hr⟩ * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹)) * ψ d := by rw [hrr]
      _ = ψ ⟨r, hR'B hr⟩ * ((z * ψ ⟨r, hR'B hr⟩ * z⁻¹) * ψ d) := by group
      _ = ψ ⟨r, hR'B hr⟩ * (ψ d * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹)) := by rw [hψc]
      _ = (ψ ⟨r, hR'B hr⟩ * ψ d) * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹) := by group
      _ = ψ (⟨r, hR'B hr⟩ * d) * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹) := by rw [map_mul]
      _ = ψ (d * ⟨r, hR'B hr⟩) * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹) := by rw [hdc]
      _ = (ψ d * ψ ⟨r, hR'B hr⟩) * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹) := by rw [map_mul]
      _ = ψ d * (ψ ⟨r, hR'B hr⟩ * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹)) := by group
      _ = ψ d * r := by rw [hrr]
  have hPP : ∀ a ∈ P, ∀ b ∈ P, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact hψ.comm a b
  obtain ⟨eD⟩ := exists_equiv_corr_altSub (X := G) e U
  let eP : ↥P ≃* alternatingGroup (Fin U.card) :=
    (Subgroup.equivMapOfInjective _ ψ hψ.inj).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hDB).trans eD)
  have hbool : ∃ a' : Bool, ∀ d : ↥(corr (X := G) e (altSub Sᶜ)),
      (d : G) ∈ corr (X := G) e (altSub U) → cjHom z a' (ψ d) ∈ Q' := by
    rcases hQ'.absorb U.card P (by omega) (by omega) (by omega) hPC ⟨eP⟩ hPP with hl | hr
    · exact ⟨false, fun d hd => hl ⟨d, hd, rfl⟩⟩
    · refine ⟨true, fun d hd => ?_⟩
      obtain ⟨q, hq, hqb⟩ := hr ⟨d, hd, rfl⟩
      have : z * ψ d * z⁻¹ = q := by
        rw [← hqb]
        show z * (z * q * z⁻¹) * z⁻¹ = q
        exact conj_conj_of_sq hz q
      show z * ψ d * z⁻¹ ∈ Q'
      rw [this]; exact hq
  obtain ⟨a', ha'⟩ := hbool
  obtain ⟨a, ha⟩ := rootLift_bool_w hz hn hS' hQ' hψ'
  refine ⟨xor a' a, fun x hx hx' => ?_⟩
  have hxD : x ∈ corr (X := G) e (altSub U) := by
    have := corr_inf_le e S S' ⟨hx, hx'⟩
    rwa [← hU] at this
  exact hQ'.eq_cj hz (hψ.comm _ _) (hψ'.comm _ _) (by rw [hψ.diag, hψ'.diag])
    (ha' ⟨x, hx⟩ hxD) (ha ⟨x, hx'⟩)

theorem rootLift_rel_local_w (P : LiftData e z) (hn : 11 ≤ n) {S S' : Finset (Fin n)}
    (hS : S.card = 3) (hS' : S'.card = 3) {ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G}
    {ψ' : ↥(corr (X := G) e (altSub S'ᶜ)) →* G} (hψ : IsRootLift e z S ψ)
    (hψ' : IsRootLift e z S' ψ') {T : Finset (Fin n)} (hT : T.card ≤ 3) {x : G}
    (hxS : x ∈ corr (X := G) e (altSub Sᶜ)) (hxS' : x ∈ corr (X := G) e (altSub S'ᶜ))
    (hxT : x ∈ corr (X := G) e (altSub T)) :
    ∃ c : Bool, ψ ⟨x, hxS⟩ = cjHom z c (ψ' ⟨x, hxS'⟩) := by
  classical
  have hz := P.sq
  by_cases hSS : Disjoint S S'
  · obtain ⟨Q', hQ'⟩ := P.canon S' hS'
    obtain ⟨c, hc⟩ := rootLift_rel_disjoint_w hz hn hS hS' hSS hQ' hψ hψ'
    exact ⟨c, hc x hxS hxS'⟩
  have hSS' : (S ∪ S').card ≤ 5 := by
    have h1 := Finset.card_union_add_card_inter S S'
    have h2 : (S ∩ S').Nonempty := Finset.not_disjoint_iff_nonempty_inter.1 hSS
    have h3 := h2.card_pos
    omega
  obtain ⟨S'', hS'', hdisj⟩ := exists_root_disjoint (S ∪ S' ∪ T) (by
    have h1 := Finset.card_union_le (S ∪ S') T
    omega)
  have hd1 : Disjoint S S'' := by
    refine Finset.disjoint_left.2 fun i hi hi' => ?_
    exact Finset.disjoint_left.1 hdisj hi' (by simp [hi])
  have hd2 : Disjoint S' S'' := by
    refine Finset.disjoint_left.2 fun i hi hi' => ?_
    exact Finset.disjoint_left.1 hdisj hi' (by simp [hi])
  have hTS'' : T ⊆ S''ᶜ := fun i hi => by
    simp only [Finset.mem_compl]
    exact fun hi' => Finset.disjoint_left.1 hdisj hi' (by simp [hi])
  have hxS'' : x ∈ corr (X := G) e (altSub S''ᶜ) := corr_mono e (altSub_mono hTS'') hxT
  obtain ⟨Q'', hQ''⟩ := P.canon S'' hS''
  obtain ⟨ψ'', hψ''⟩ := P.root S'' hS''
  obtain ⟨c₁, hc₁⟩ := rootLift_rel_disjoint_w hz hn hS hS'' hd1 hQ'' hψ hψ''
  obtain ⟨c₂, hc₂⟩ := rootLift_rel_disjoint_w hz hn hS' hS'' hd2 hQ'' hψ' hψ''
  refine ⟨xor c₁ c₂, ?_⟩
  have e1 := hc₁ x hxS hxS''
  have e2 := hc₂ x hxS' hxS''
  rw [e1, e2, cjHom_cjHom hz, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

theorem rootLift_rel_all_w (P : LiftData e z) (hn : 11 ≤ n) {S S' : Finset (Fin n)}
    (hS : S.card = 3) (hS' : S'.card = 3) {ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G}
    {ψ' : ↥(corr (X := G) e (altSub S'ᶜ)) →* G} (hψ : IsRootLift e z S ψ)
    (hψ' : IsRootLift e z S' ψ') :
    ∃ c : Bool, ∀ (x : G) (hx : x ∈ corr (X := G) e (altSub Sᶜ))
      (hx' : x ∈ corr (X := G) e (altSub S'ᶜ)), ψ ⟨x, hx⟩ = cjHom z c (ψ' ⟨x, hx'⟩) := by
  classical
  obtain ⟨U, hU⟩ : ∃ U : Finset (Fin n), U = (S ∪ S')ᶜ := ⟨_, rfl⟩
  have hUc : 5 ≤ U.card := by
    rw [hU, card_compl_fin]
    have := Finset.card_union_le S S'
    omega
  have hUS : U ⊆ Sᶜ := fun i hi => by
    simp only [hU, Finset.mem_compl, Finset.mem_union, not_or] at hi ⊢
    exact hi.1
  have hUS' : U ⊆ S'ᶜ := fun i hi => by
    simp only [hU, Finset.mem_compl, Finset.mem_union, not_or] at hi ⊢
    exact hi.2
  have hDB : corr (X := G) e (altSub U) ≤ corr (X := G) e (altSub Sᶜ) :=
    corr_mono e (altSub_mono hUS)
  have hDB' : corr (X := G) e (altSub U) ≤ corr (X := G) e (altSub S'ᶜ) :=
    corr_mono e (altSub_mono hUS')
  let φ : ↥(altSub U) →* ↥(corr (X := G) e (altSub U)) :=
    corrIn (X := G) e (altSub_le_alternatingGroup U)
  let F : ↥(altSub U) →* G := ψ.comp ((Subgroup.inclusion hDB).comp φ)
  let F' : ↥(altSub U) →* G := ψ'.comp ((Subgroup.inclusion hDB').comp φ)
  have hFinj : Function.Injective F :=
    hψ.inj.comp ((Subgroup.inclusion_injective hDB).comp (corrIn_injective (X := G) e _))
  obtain ⟨c, hc⟩ := exists_rel_of_cyc3 (by omega) (F := F) (F' := F') hFinj
    (fun x y => hψ'.comm _ _) (fun a b c ha hb hc hab hbc hac hmem => by
      have hxT : ((φ ⟨cyc3 a b c, hmem⟩ : ↥(corr (X := G) e (altSub U))) : G) ∈
          corr (X := G) e (altSub ({a, b, c} : Finset (Fin n))) := by
        show ((e.symm ⟨cyc3 a b c, altSub_le_alternatingGroup U hmem⟩ : L) : G) ∈ _
        apply mem_corr_of_mem
        simp only [MulEquiv.apply_symm_apply]
        exact cyc3_mem_altSub (by simp) (by simp) (by simp) hab hbc hac
      exact rootLift_rel_local_w P hn hS hS' hψ hψ' (T := {a, b, c})
        (Finset.card_le_three) (x := ((φ ⟨cyc3 a b c, hmem⟩ : ↥(corr (X := G) e (altSub U))) : G))
        (hDB (φ ⟨cyc3 a b c, hmem⟩).2) (hDB' (φ ⟨cyc3 a b c, hmem⟩).2) hxT)
  refine ⟨c, fun x hx hx' => ?_⟩
  have hxD : x ∈ corr (X := G) e (altSub U) := by
    have := corr_inf_le e S S' ⟨hx, hx'⟩
    rwa [← hU] at this
  obtain ⟨hxA, hxe⟩ := mem_corr.1 hxD
  have hφ : ((φ ⟨(e ⟨x, hxA⟩ : Equiv.Perm (Fin n)), hxe⟩ : ↥(corr (X := G) e (altSub U))) : G) =
      x := by
    show ((e.symm ⟨(e ⟨x, hxA⟩ : Equiv.Perm (Fin n)), _⟩ : L) : G) = x
    simp
  have h1 := hc ⟨(e ⟨x, hxA⟩ : Equiv.Perm (Fin n)), hxe⟩
  have h2 : F ⟨(e ⟨x, hxA⟩ : Equiv.Perm (Fin n)), hxe⟩ = ψ ⟨x, hx⟩ :=
    congrArg ψ (Subtype.ext hφ)
  have h3 : F' ⟨(e ⟨x, hxA⟩ : Equiv.Perm (Fin n)), hxe⟩ = ψ' ⟨x, hx'⟩ :=
    congrArg ψ' (Subtype.ext hφ)
  rw [h2, h3] at h1
  exact h1

end Disch

section Final

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}
  {e : L ≃* alternatingGroup (Fin n)}

theorem LiftData.rootDichotomy (P : LiftData e z) (hn : 11 ≤ n) : RootDichotomy e z := by
  intro S S' hS hS' ψ ψ' hψ hψ'
  obtain ⟨c, hc⟩ := rootLift_rel_all_w P hn hS hS' hψ hψ'
  cases c
  · exact Or.inl hc
  · exact Or.inr hc

theorem LiftData.exists_wreathPair (P : LiftData e z) (hn : 11 ≤ n) :
    ∃ H : Subgroup G, WreathPair L z n H := by
  have hdich := P.rootDichotomy hn
  choose ψ hψ using P.root
  let φ : RootFamily G n := fun S hS =>
    (ψ S hS).comp (corrIn (X := G) e (altSub_le_alternatingGroup Sᶜ))
  have hpre : φ.IsPreWLift z (embAlt e) := by
    refine ⟨P.sq, ?_, ?_, ?_⟩
    · intro S hS x
      exact (hψ S hS).diag (corrIn (X := G) e (altSub_le_alternatingGroup Sᶜ) x)
    · intro S hS x y
      exact (hψ S hS).comm _ _
    · intro S hS x hx
      have h1 := (hψ S hS).rigid _ hx
      exact corrIn_injective (X := G) e (altSub_le_alternatingGroup Sᶜ)
        (h1.trans (map_one _).symm)
  have hd : ∀ (S S' : Finset (Fin n)) (hS : S.card = 3) (hS' : S'.card = 3),
      RFSame φ S S' hS hS' ∨ RFOpp φ z S S' hS hS' := by
    intro S S' hS hS'
    rcases hdich S S' hS hS' (ψ S hS) (ψ S' hS') (hψ S hS) (hψ S' hS') with h1 | h1
    · left
      intro x hx hx'
      exact h1 _ (corrIn (X := G) e (altSub_le_alternatingGroup Sᶜ) ⟨x, hx⟩).2
        (corrIn (X := G) e (altSub_le_alternatingGroup S'ᶜ) ⟨x, hx'⟩).2
    · right
      intro x hx hx'
      exact h1 _ (corrIn (X := G) e (altSub_le_alternatingGroup Sᶜ) ⟨x, hx⟩).2
        (corrIn (X := G) e (altSub_le_alternatingGroup S'ᶜ) ⟨x, hx'⟩).2
  exact exists_wreathPair_of_dichotomy hn e hpre hd

end Final

section Transport

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

theorem caseIIIAt_transport_w (h : WeakShape z L n) (e : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) {S S' : Finset (Fin n)} (hS : S.card = 3) (hS' : S'.card = 3)
    (hIII : CaseIIIAt e z S) : CaseIIIAt e z S' := by
  obtain ⟨ht, hW⟩ := hIII
  have ht' : z ∈ centralizer (corr (X := G) e (altSub S') : Set G) :=
    mem_centralizer_corr_of_weakShape h e (altSub S')
  obtain ⟨π, hsign, hπ⟩ := exists_even_perm_of_card_eq (hS.trans hS'.symm)
    (by rw [card_compl_fin, hS]; omega)
  have hπA : π ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.2 hsign
  have hπc : ∀ x, x ∈ Sᶜ ↔ π x ∈ S'ᶜ := fun x => by simp [hπ x]
  set lg : G := ((e.symm ⟨π, hπA⟩ : L) : G) with hlg
  have hlgL : lg ∈ L := (e.symm ⟨π, hπA⟩ : L).2
  have hlz : lg * z * lg⁻¹ = z := by
    have := mem_centralizer_singleton_iff.1 (h.le_cent hlgL)
    rw [this]; group
  have hRS := corr_conj_iff (G := G) e hπA hπ
  have hBS := corr_conj_iff (G := G) e hπA hπc
  have hCC : ∀ x : G, x ∈ centralizer (corr (X := G) e (altSub S) : Set G) ↔
      lg * x * lg⁻¹ ∈ centralizer (corr (X := G) e (altSub S') : Set G) := by
    intro x
    rw [mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro hx r' hr'
      have hr : lg⁻¹ * r' * lg ∈ corr (X := G) e (altSub S) := by
        refine (hRS _).2 ?_
        have h3 : lg * (lg⁻¹ * r' * lg) * lg⁻¹ = r' := by group
        rw [h3]; exact hr'
      have := hx _ hr
      calc r' * (lg * x * lg⁻¹) = lg * ((lg⁻¹ * r' * lg) * x) * lg⁻¹ := by group
        _ = lg * (x * (lg⁻¹ * r' * lg)) * lg⁻¹ := by rw [this]
        _ = (lg * x * lg⁻¹) * r' := by group
    · intro hx r hr
      have := hx (lg * r * lg⁻¹) ((hRS r).1 hr)
      have h2 : lg * (r * x) * lg⁻¹ = lg * (x * r) * lg⁻¹ := by
        calc lg * (r * x) * lg⁻¹ = (lg * r * lg⁻¹) * (lg * x * lg⁻¹) := by group
          _ = (lg * x * lg⁻¹) * (lg * r * lg⁻¹) := this
          _ = lg * (x * r) * lg⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
  let cC : ↥(centralizer (corr (X := G) e (altSub S) : Set G)) ≃*
      ↥(centralizer (corr (X := G) e (altSub S') : Set G)) :=
    { toFun := fun x => ⟨lg * (x : G) * lg⁻¹, (hCC x).1 x.2⟩
      invFun := fun y => ⟨lg⁻¹ * (y : G) * lg, (hCC _).2 (by simp [mul_assoc])⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hodd := ClassicalInvolution.QuaternionStructure.oddCore_map_mulEquiv cC
  let Φ : Sec G (corr (X := G) e (altSub S)) ≃* Sec G (corr (X := G) e (altSub S')) :=
    QuotientGroup.congr _ _ cC hodd
  have hΦmk : ∀ x, Φ (QuotientGroup.mk x) = QuotientGroup.mk (cC x) := fun x => rfl
  have hΦz : Φ (QuotientGroup.mk ⟨z, ht⟩) = QuotientGroup.mk ⟨z, ht'⟩ := by
    rw [hΦmk]
    congr 1
    exact Subtype.ext hlz
  have hBsub : ((corr (X := G) e (altSub Sᶜ)).subgroupOf
        (centralizer (corr (X := G) e (altSub S) : Set G))).map cC.toMonoidHom =
      (corr (X := G) e (altSub S'ᶜ)).subgroupOf
        (centralizer (corr (X := G) e (altSub S') : Set G)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show lg * (x : G) * lg⁻¹ ∈ corr (X := G) e (altSub S'ᶜ)
      exact (hBS x).1 hx
    · intro hy
      refine ⟨cC.symm y, ?_, cC.apply_symm_apply y⟩
      show lg⁻¹ * (y : G) * lg ∈ corr (X := G) e (altSub Sᶜ)
      refine (hBS _).2 ?_
      have h3 : lg * (lg⁻¹ * (y : G) * lg) * lg⁻¹ = (y : G) := by group
      rw [h3]; exact hy
  have hΦA : (secComp e S).map Φ.toMonoidHom = secComp e S' := by
    unfold secComp
    rw [Subgroup.map_map, ← hBsub, Subgroup.map_map]
    congr 1
  have hmap := hW.map Φ
  rw [hΦz, hΦA] at hmap
  refine ⟨ht', ?_⟩
  have hc : n - S.card = n - S'.card := by rw [hS, hS']
  rw [← hc]
  exact hmap

theorem exists_wreathPair_of_caseIII_root_w (h : WeakShape z L n)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n)
    (hRD : ∀ S : Finset (Fin n), S.card = 3 →
      RootData L z (rootGroup e S) (corr (X := G) e (altSub Sᶜ)) (n - S.card))
    {S₀ : Finset (Fin n)} (hS₀ : S₀.card = 3) (hIII : CaseIIIAt e z S₀) :
    ∃ H : Subgroup G, WreathPair L z n H := by
  have hIII' : ∀ S : Finset (Fin n), S.card = 3 → CaseIIIAt e z S := fun S hS =>
    caseIIIAt_transport_w h e (by omega) hS₀ hS hIII
  have hz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.order, pow_two] at this
  have P : LiftData e z :=
    ⟨hz, fun S hS => exists_canon_w h e hn hS (hRD S hS) (hIII' S hS),
      fun S hS => exists_rootLift_w h e hn hS (hIII' S hS)⟩
  exact P.exists_wreathPair hn

end Transport

end CFSG.OddStandard.AltStdCycTwo.StageM
