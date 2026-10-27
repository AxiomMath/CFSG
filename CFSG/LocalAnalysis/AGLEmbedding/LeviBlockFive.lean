module

public import CFSG.Open.Defs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCover

public section

namespace CFSG.AGLEmbedding

open scoped commutatorElement

theorem fiveBlockSections :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]
      [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)} {X : Subgroup (∀ j, G j)},
      Subgroup.pi Set.univ S ≤ X → ⁅X, X⁆ ≤ Subgroup.pi Set.univ S →
      (∀ j, CFSG.Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j)) →
      (∀ j, CFSG.Open.IsQuasisimple (S j) →
        Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60 → Nat.card (S j) = 60) →
      ∀ (O : Subgroup (∀ j, G j)) (J : Fin 3 → Subgroup (∀ j, G j)), O ≤ X →
        X ≤ Subgroup.normalizer (O : Set (∀ j, G j)) →
        (∀ U : Subgroup (∀ j, G j), U ≤ X → ∀ (V : Subgroup U) [V.Normal], O.subgroupOf U ≤ V →
          IsSimpleGroup (U ⧸ V) → (∃ a b : U ⧸ V, a * b ≠ b * a) → Nat.card (U ⧸ V) = 60) →
        (∀ i, J i ≤ X ∧ ∃ φ : ↥(J i) →* alternatingGroup (Fin 5),
          Function.Surjective φ ∧ ∀ x : ↥(J i), φ x = 1 ↔ (x : ∀ j, G j) ∈ O) →
        (∀ i k, i ≠ k → ⁅J i, J k⁆ ≤ O) →
        3 ≤ Nat.card {j // CFSG.Open.IsQuasisimple (S j) ∧
          Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60 ∧
          ¬ (S j).map (MonoidHom.mulSingle G j) ≤ O} := by
  intro ι _ _ G _ _ S X hpi hcomm hS hcl O J hOX hXO hsec hJ hJc
  classical
  set P0 := Subgroup.pi Set.univ S with hP0
  set E : ι → Subgroup (∀ j, G j) := fun j => (S j).map (MonoidHom.mulSingle G j) with hE
  have hmemE : ∀ j (s : G j), s ∈ S j → Pi.mulSingle j s ∈ E j := fun j s hs => ⟨s, hs, rfl⟩
  have hEP : ∀ j, E j ≤ P0 := by
    rintro j _ ⟨s, hs, rfl⟩
    refine (Subgroup.mem_pi _).mpr fun i _ => ?_
    by_cases h : i = j
    · subst h; simpa using hs
    · simp [Pi.mulSingle_eq_of_ne h]
  have hconjO : ∀ x ∈ X, ∀ o ∈ O, x * o * x⁻¹ ∈ O := fun x hx o ho =>
    (Subgroup.mem_normalizer_iff.mp (hXO hx) o).mp ho
  have hcommO : ∀ x ∈ X, ∀ o ∈ O, ⁅o, x⁆ ∈ O := fun x hx o ho => by
    have h1 : x * o⁻¹ * x⁻¹ ∈ O := hconjO x hx _ (O.inv_mem ho)
    have e : ⁅o, x⁆ = o * (x * o⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact O.mul_mem ho h1
  have hEX : ∀ j, E j ≤ X := fun j => (hEP j).trans hpi
  let eE : ∀ j, ↥(S j) ≃* ↥(E j) := fun j =>
    (S j).equivMapOfInjective (MonoidHom.mulSingle G j) (Pi.mulSingle_injective j)
  have hcoordP : ∀ x ∈ P0, ∀ j, x j ∈ S j := fun x hx j => (Subgroup.mem_pi _).mp hx j trivial
  have h60 : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → ¬ E j ≤ O →
      Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60 := by
    intro j hq hnot
    have hqE : CFSG.Open.IsQuasisimple ↥(E j) := LeviBlock.isQuasisimple_of_mulEquiv (eE j) hq
    have hOn : (O.subgroupOf (E j)).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hconjO _ (hEX j g.2) _ hn⟩
    have hle : O.subgroupOf (E j) ≤ Subgroup.center ↥(E j) := by
      rcases CFSG.AGLEmbedding.le_center_or_eq_top_of_normal_quasisimple hqE (O.subgroupOf (E j))
        with h | h
      · exact h
      · exfalso
        apply hnot
        intro x hx
        have : (⟨x, hx⟩ : ↥(E j)) ∈ O.subgroupOf (E j) := h ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
    have : IsSimpleGroup (↥(E j) ⧸ Subgroup.center ↥(E j)) := hqE.2
    have h := hsec (E j) (hEX j) (Subgroup.center ↥(E j)) hle this
      (LeviBlock.exists_noncomm_centerQuotient hqE)
    rw [← h]
    exact Nat.card_congr
      (QuotientGroup.congr _ _ (eE j) (LeviBlock.map_center_mulEquiv (eE j))).toEquiv
  have hproj : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → ¬ E j ≤ O → ∀ y ∈ O, y ∈ P0 → y j = 1 := by
    intro j hq hnot y hyO hyP
    have h60j := h60 j hq hnot
    have hcard := hcl j hq h60j
    have hZ : Subgroup.center ↥(S j) = ⊥ := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(S j))
      rw [hcard, h60j] at this
      exact Subgroup.eq_bot_of_card_eq _ (by omega)
    set T : Subgroup ↥(S j) := ((O ⊓ P0).map (Pi.evalMonoidHom G j)).comap (S j).subtype with hT
    have hTn : T.Normal := ⟨fun t ht s => by
      obtain ⟨y', ⟨hy'O, hy'P⟩, hy'⟩ := ht
      set e : ∀ i, G i := Pi.mulSingle j (s : G j) with he
      have heX : e ∈ X := hEX j (hmemE j s s.2)
      refine ⟨e * y' * e⁻¹, ⟨hconjO _ heX _ hy'O, ?_⟩, ?_⟩
      · have heP : e ∈ P0 := hEP j (hmemE j s s.2)
        exact P0.mul_mem (P0.mul_mem heP hy'P) (P0.inv_mem heP)
      · simp only [Pi.evalMonoidHom_apply, Pi.mul_apply, Pi.inv_apply, he,
          Pi.mulSingle_eq_same]
        rw [show y' j = (t : G j) from hy']
        rfl⟩
    rcases CFSG.AGLEmbedding.le_center_or_eq_top_of_normal_quasisimple hq T with h | h
    · have hmem : (⟨y j, hcoordP y hyP j⟩ : ↥(S j)) ∈ T := ⟨y, ⟨hyO, hyP⟩, rfl⟩
      have := h hmem
      rw [hZ, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      apply hnot
      set K' : Subgroup ↥(S j) := O.comap ((MonoidHom.mulSingle G j).comp (S j).subtype)
      have hK' : commutator ↥(S j) ≤ K' := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        obtain ⟨y', ⟨hy'O, hy'P⟩, hy'⟩ := (h ▸ Subgroup.mem_top a : a ∈ T)
        have hbX : Pi.mulSingle j (b : G j) ∈ X := hEX j (hmemE j b b.2)
        have hc := hcommO _ hbX _ hy'O
        have heq : ⁅y', Pi.mulSingle j (b : G j)⁆ =
            Pi.mulSingle j (⁅(a : G j), (b : G j)⁆) := by
          funext i
          by_cases hij : i = j
          · subst hij
            simp only [commutatorElement_def, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same]
            rw [show y' i = (a : G i) from hy']
          · simp [commutatorElement_def, Pi.mulSingle_eq_of_ne hij]
        rw [heq] at hc
        change Pi.mulSingle j ((⁅a, b⁆ : ↥(S j)) : G j) ∈ O
        have hab : ((⁅a, b⁆ : ↥(S j)) : G j) = ⁅(a : G j), (b : G j)⁆ := by
          simp [commutatorElement_def]
        rw [hab]
        exact hc
      rw [hq.1] at hK'
      rintro _ ⟨s, hs, rfl⟩
      have hmem : (⟨s, hs⟩ : ↥(S j)) ∈ K' := top_le_iff.mp hK' ▸ Subgroup.mem_top _
      exact hmem
  set Bt := {j // CFSG.Open.IsQuasisimple ↥(S j) ∧
    Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60 ∧
    ¬ (S j).map (MonoidHom.mulSingle G j) ≤ O} with hBt
  let πB : ↥P0 →* (∀ j : Bt, ↥(S j.1)) :=
    { toFun := fun x j => ⟨x.1 j.1, hcoordP x.1 x.2 j.1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  set Dt := {j // ¬ CFSG.Open.IsQuasisimple ↥(S j)} with hDt
  let πD : ↥P0 →* (∀ j : Dt, ↥(S j.1)) :=
    { toFun := fun x j => ⟨x.1 j.1, hcoordP x.1 x.2 j.1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hsolD : Group.IsSolvable (∀ j : Dt, ↥(S j.1)) :=
    LeviBlock.isSolvable_pi fun j => (hS j.1).resolve_left j.2
  have hmemO : ∀ x ∈ P0, (∀ j : Bt, x j.1 = 1) → (∀ j : Dt, x j.1 = 1) → x ∈ O := by
    intro x hx hB hD
    rw [← Finset.noncommProd_mulSingle x]
    refine O.noncommProd_mem _ fun j _ => ?_
    by_cases hq : CFSG.Open.IsQuasisimple ↥(S j)
    · by_cases hEO : E j ≤ O
      · exact hEO (hmemE j _ (hcoordP x hx j))
      · rw [hB ⟨j, hq, h60 j hq hEO, hEO⟩, Pi.mulSingle_one]
        exact O.one_mem
    · rw [hD ⟨j, hq⟩, Pi.mulSingle_one]
      exact O.one_mem
  have hA5 : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hA5card : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hA5nc : ∃ a b : ↥(alternatingGroup (Fin 5)), a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup ↥(alternatingGroup (Fin 5)) :=
      { (inferInstance : Group ↥(alternatingGroup (Fin 5))) with mul_comm := hc }
    have hp : (Nat.card ↥(alternatingGroup (Fin 5))).Prime := IsSimpleGroup.prime_card
    rw [hA5card] at hp
    exact absurd hp (by decide)
  have hA5comm : commutator ↥(alternatingGroup (Fin 5)) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥(alternatingGroup (Fin 5)))
      with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hA5nc
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator ↥(alternatingGroup (Fin 5)) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h
  have hA5Z : Subgroup.center ↥(alternatingGroup (Fin 5)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(alternatingGroup (Fin 5)))
      with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hA5nc
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hstep : ∀ i, ∃ A : Subgroup (∀ j : Bt, ↥(S j.1)), Nat.card A = 60 ∧
      Subgroup.center ↥A = ⊥ ∧ ∀ a ∈ A, ∃ x ∈ ⁅J i, J i⁆, x ∈ P0 ∧
        ∀ j : Bt, ((a j : ↥(S j.1)) : G j.1) = x j.1 := by
    intro i
    obtain ⟨hJX, φ, hφ, hφO⟩ := hJ i
    set D := commutator ↥(J i) with hD
    have hDJ : ∀ d : ↥D, ((d : ↥(J i)) : ∀ j, G j) ∈ ⁅J i, J i⁆ := by
      intro d
      have h : D.map (J i).subtype = ⁅J i, J i⁆ := by
        rw [hD, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      rw [← h]
      exact ⟨d, d.2, rfl⟩
    have hDP : ∀ d : ↥D, ((d : ↥(J i)) : ∀ j, G j) ∈ P0 := fun d =>
      hcomm (Subgroup.commutator_mono hJX hJX (hDJ d))
    let incl : ↥D →* ↥P0 :=
      { toFun := fun d => ⟨((d : ↥(J i)) : ∀ j, G j), hDP d⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    set σ := πB.comp incl with hσ
    set φ' := φ.comp D.subtype with hφ'd
    have hφ' : Function.Surjective φ' := by
      have h : D.map φ = ⊤ := by
        rw [hD, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hφ,
          ← commutator_def, hA5comm]
      intro a
      obtain ⟨d, hd, hda⟩ := (h ▸ Subgroup.mem_top a : a ∈ D.map φ)
      exact ⟨⟨d, hd⟩, hda⟩
    have hker : σ.ker = φ'.ker := by
      apply le_antisymm
      · intro d hd
        set K := σ.ker with hK
        have : (K.map φ').Normal := (MonoidHom.normal_ker σ).map φ' hφ'
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map φ') with h | h
        · exact (Subgroup.map_eq_bot_iff _).mp h hd
        · exfalso
          let τ : ↥K →* (∀ j : Dt, ↥(S j.1)) := πD.comp (incl.comp K.subtype)
          have hτ : τ.rangeRestrict.ker ≤ (φ'.comp K.subtype).ker := by
            intro k hk
            rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hk
            rw [MonoidHom.mem_ker]
            have hkσ : σ (k : ↥D) = 1 := k.2
            have hx : (((k : ↥D) : ↥(J i)) : ∀ j, G j) ∈ O := by
              refine hmemO _ (hDP k) (fun j => ?_) (fun j => ?_)
              · have := congrArg Subtype.val (congrFun hkσ j)
                exact this
              · have := congrArg Subtype.val (congrFun hk j)
                exact this
            exact (hφO _).mpr hx
          have hsurj : Function.Surjective (φ'.comp K.subtype) := by
            intro a
            obtain ⟨k, hk, hka⟩ := (h ▸ Subgroup.mem_top a : a ∈ K.map φ')
            exact ⟨⟨k, hk⟩, hka⟩
          obtain ⟨g, hg, -⟩ := LeviBlock.exists_factor τ.rangeRestrict
            τ.rangeRestrict_surjective (φ'.comp K.subtype) hsurj hτ
          have : Group.IsSolvable ↥(alternatingGroup (Fin 5)) := Group.isSolvable_of_surjective hg
          obtain ⟨a, b, hab⟩ := hA5nc
          exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr this a b)
      · intro d hd
        rw [MonoidHom.mem_ker] at hd ⊢
        have hxO : (((d : ↥D) : ↥(J i)) : ∀ j, G j) ∈ O := (hφO _).mp hd
        funext j
        exact Subtype.ext (hproj j.1 j.2.1 j.2.2.2 _ hxO (hDP d))
    let iso : ↥σ.range ≃* ↥(alternatingGroup (Fin 5)) :=
      (QuotientGroup.quotientKerEquivRange σ).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans
          (QuotientGroup.quotientKerEquivOfSurjective φ' hφ'))
    refine ⟨σ.range, ?_, ?_, ?_⟩
    · rw [Nat.card_congr iso.toEquiv, hA5card]
    · rw [← LeviBlock.map_center_mulEquiv iso.symm, hA5Z, Subgroup.map_bot]
    · rintro a ⟨d, rfl⟩
      exact ⟨_, hDJ d, hDP d, fun j => rfl⟩
  choose A hAcard hAZ hAx using hstep
  have hAcomm : ∀ i k, i ≠ k → ∀ a ∈ A i, ∀ b ∈ A k, a * b = b * a := by
    intro i k hik a ha b hb
    obtain ⟨x, hxJ, hxP, hxa⟩ := hAx i a ha
    obtain ⟨y, hyJ, hyP, hyb⟩ := hAx k b hb
    have hJle : ∀ i, ⁅J i, J i⁆ ≤ J i := fun i => by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact (J i).mul_mem ((J i).mul_mem ((J i).mul_mem ha hb) ((J i).inv_mem ha))
        ((J i).inv_mem hb)
    have hxy : ⁅x, y⁆ ∈ O := hJc i k hik
      (Subgroup.commutator_mem_commutator (hJle i hxJ) (hJle k hyJ))
    have hxyP : ⁅x, y⁆ ∈ P0 := by
      rw [commutatorElement_def]
      exact P0.mul_mem (P0.mul_mem (P0.mul_mem hxP hyP) (P0.inv_mem hxP)) (P0.inv_mem hyP)
    funext j
    apply Subtype.ext
    have h1 := hproj j.1 j.2.1 j.2.2.2 _ hxy hxyP
    simp only [commutatorElement_def, Pi.mul_apply, Pi.inv_apply] at h1
    simp only [Pi.mul_apply, Subgroup.coe_mul, hxa j, hyb j]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hdvd := LeviBlock.card_mul_dvd_of_commute (A 0) (A 1) (A 2) (hAcomm 0 1 (by decide))
    (hAcomm 0 2 (by decide)) (hAcomm 1 2 (by decide)) (hAZ 0) (hAZ 1)
  rw [hAcard, hAcard, hAcard, Nat.card_pi] at hdvd
  have hprod : ∏ j : Bt, Nat.card ↥(S j.1) = 60 ^ Nat.card Bt := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_congr rfl fun j _ => hcl j.1 j.2.1 j.2.2.1
  rw [hprod] at hdvd
  by_contra hlt
  push Not at hlt
  have hle := Nat.le_of_dvd (by positivity) hdvd
  interval_cases h : Nat.card Bt <;> norm_num at hle

end CFSG.AGLEmbedding
