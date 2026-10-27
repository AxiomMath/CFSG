module

public import CFSG.LieType.Simplicity.ReeLarge

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree ReeTag
open scoped commutatorElement

section Generation

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

theorem normalClosure_sup_reeTorusPart_eq_top :
    Subgroup.normalClosure (reeUnipPart t K a : Set (reeFixed t K a)) ⊔ reeTorusPart t K a = ⊤ := by
  set R := Subgroup.normalClosure (reeUnipPart t K a : Set (reeFixed t K a))
  have hB : reeBorelPart t K a ≤ R ⊔ reeTorusPart t K a := by
    intro b hb
    obtain ⟨s, hs, c, hc, rfl⟩ := exists_mul_of_mem_reeBorelPart a hb
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.subset_normalClosure hs))
      (Subgroup.mem_sup_right hc)
  refine eq_top_of_reeBorelPart_le hB fun i => ?_
  obtain ⟨u, hu, huF, b₁, hb₁, hb₁F, b₂, hb₂, hb₂F, h⟩ := exists_nrep_blockElt_eq t K a i
  set r := nrepFixed t K a (reeOrbitWord_mem t i)
  have e : r = ⟨b₁, hb₁F⟩ * (r * ⟨u, huF⟩ * r⁻¹) * ⟨b₂, hb₂F⟩ := Subtype.ext h
  have huS : (⟨u, huF⟩ : reeFixed t K a) ∈ reeUnipPart t K a := hu
  rw [e]
  exact mul_mem (mul_mem (hB hb₁) (Subgroup.mem_sup_left
    (Subgroup.normalClosure_normal.conj_mem _ (Subgroup.subset_normalClosure huS) r))) (hB hb₂)

theorem isSolvable_reeBorelPart :
    Group.IsSolvable (reeBorelPart t K a) := by
  have : Group.IsSolvable (nativeData t.tag K).B := isSolvable_B t.prime
  let f : reeBorelPart t K a →* (nativeData t.tag K).B :=
    MonoidHom.codRestrict ((reeFixed t K a).subtype.comp (reeBorelPart t K a).subtype) _
      fun x => x.2
  refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y h => ?_
  exact Subtype.ext (Subtype.ext (congrArg (fun z : (nativeData t.tag K).B =>
    (z : adjointGroup t.tag K)) h))

theorem nontrivial_reeFixed :
    Nontrivial (reeFixed t K a) := by
  obtain ⟨u, -, hu1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left
    (reeUnipPart_ne_bot (t := t) (K := K) a)
  exact ⟨⟨u, 1, hu1⟩⟩

theorem not_normalClosure_le_reeBorelPart :
    ¬ Subgroup.normalClosure (reeUnipPart t K a : Set (reeFixed t K a)) ≤ reeBorelPart t K a := by
  intro h
  obtain ⟨u, hu, hu1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left
    (reeUnipPart_ne_bot (t := t) (K := K) a)
  have hn := h (Subgroup.normalClosure_normal.conj_mem u (Subgroup.subset_normalClosure hu)
    (reeLongRep t K a))
  exact hu1 (Subtype.ext (eq_one_of_nrep_longWord_conj_mem_B hu hn))

end Generation

section F4

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (a : ℕ)

theorem reeTorusPart_le_commutator_F4
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    reeTorusPart ReeTag.F4 K a ≤ commutator (reeFixed ReeTag.F4 K a) := by
  intro h hh
  set n := reeLongRep ReeTag.F4 K a
  have hinv : n * h * n⁻¹ = h⁻¹ := Subtype.ext (nrep_conj_of_mem_H
    (fun α => congrArg Subtype.val (wordProd_longWord_smul ReeTag.F4 α)) hh)
  have h2 : h⁻¹ * h⁻¹ ∈ commutator (reeFixed ReeTag.F4 K a) := by
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top n) (Subgroup.mem_top h)
    rwa [commutatorElement_def, hinv] at this
  have hsq : h * h ∈ commutator (reeFixed ReeTag.F4 K a) := by
    have := inv_mem h2
    rwa [mul_inv_rev, inv_inv] at this
  have hpow : h ^ (Nat.card K - 1) = 1 :=
    Subtype.ext (by simpa using (nativeRootSubgroups ReeTag.F4.tag K).pow_card_sub_one_eq_one hh)
  have hq : h = (h * h) ^ (2 ^ (2 * a)) := by
    rw [← sq, ← pow_mul]
    have e : 2 * 2 ^ (2 * a) = Nat.card K := by
      rw [hK]
      change 2 * 2 ^ (2 * a) = 2 ^ (2 * a + 1)
      ring
    rw [e]
    calc h = h ^ (Nat.card K - 1) * h := by rw [hpow, one_mul]
      _ = h ^ Nat.card K := by rw [← pow_succ, Nat.sub_add_cancel Nat.card_pos]
  rw [hq]
  exact pow_mem hsq _

theorem commutator_reeFixed_F4
    (ha : 1 ≤ a) (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    commutator (reeFixed ReeTag.F4 K a) = ⊤ := by
  rw [eq_top_iff, ← normalClosure_sup_reeTorusPart_eq_top (t := ReeTag.F4) (K := K) a]
  exact sup_le (Subgroup.normalClosure_le_normal (reeUnipPart_le_commutator a ha hK))
    (reeTorusPart_le_commutator_F4 a hK)

theorem isSimpleGroup_quotient_center_reeFixed_F4
    (ha : 1 ≤ a)
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    IsSimpleGroup (reeFixed ReeTag.F4 K a ⧸ Subgroup.center (reeFixed ReeTag.F4 K a)) := by
  have hperf : Group.IsPerfect (reeFixed ReeTag.F4 K a) := ⟨commutator_reeFixed_F4 a ha hK⟩
  have := nontrivial_reeFixed (t := ReeTag.F4) (K := K) a
  have hB := isSolvable_reeBorelPart (t := ReeTag.F4) (K := K) a
  have hgen : Subgroup.normalClosure (reeUnipPart ReeTag.F4 K a : Set (reeFixed ReeTag.F4 K a)) =
      ⊤ := CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf hB
    (sup_reeBorelPart_eq_top_F4 _ (not_normalClosure_le_reeBorelPart a))
  refine CFSG.LieType.TitsSimplicity.isSimpleGroup_quotient_center_of_forall hperf
    fun M hM => ?_
  by_cases hMB : M ≤ reeBorelPart ReeTag.F4 K a
  · exact .inl (le_center_of_le_reeBorelPart hgen M hMB)
  · exact .inr (CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf hB
      (sup_reeBorelPart_eq_top_F4 M hMB))

end F4

theorem fam_2f4_simplicity
    (G : Type) [Group G] (p f : ℕ)
    (h : CFSG.Blueprint.ReeTitsModel G .twistedF4 p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨hadm, a, hf, hmodel⟩ := h
  obtain ⟨-, -, -, hp, -, h3⟩ := hadm
  subst hp
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K ReeTag.F4.prime := hc
  have hK' : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1) := by
    rw [hK, hf]
    rfl
  have ha : 1 ≤ a := by omega
  have hperf := commutator_reeFixed_F4 a ha hK'
  have hs := isSimpleGroup_quotient_center_reeFixed_F4 a ha hK'
  let eΓ : commutator (reeFixed ReeTag.F4 K a) ≃* reeFixed ReeTag.F4 K a :=
    (MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv
  have e' := (e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K a)).trans
      ((reeFixed ReeTag.F4 K a).equivMapOfInjective _ Subtype.val_injective).symm))).trans
    (QuotientGroup.congr _ _ eΓ (Subgroup.map_center_eq _))
  have : Nontrivial G := e'.toEquiv.nontrivial
  exact ⟨inferInstance, IsSimpleGroup.isSimpleGroup_of_surjective e'.symm.toMonoidHom
    e'.symm.surjective⟩

end CFSG.LieType.Simplicity
