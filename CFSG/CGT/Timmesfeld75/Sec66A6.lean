module

public import CFSG.CGT.Timmesfeld75.Sec66Proved
public import CFSG.CGT.Timmesfeld75.A6Facts
public import CFSG.CGT.Timmesfeld75.A6Basic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {U Tb P : Subgroup G} {y y' : G} {q : ℕ}

theorem ncard_conjSet_top_eq_index {K : Type} [Group K] [Finite K] (V : Subgroup K) :
    (conjSet ⊤ V).ncard = (Subgroup.normalizer (V : Set K)).index := by
  have h1 := ncard_conjSet_mul_card ⊤ V
  have h2 : normIn ⊤ V = Subgroup.normalizer (V : Set K) := top_inf_eq _
  rw [h2, Subgroup.card_top] at h1
  have h3 := Subgroup.card_mul_index (Subgroup.normalizer (V : Set K))
  have hpos : 0 < Nat.card ↥(Subgroup.normalizer (V : Set K)) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [mul_comm, h1, h3]

theorem simple_equiv_alternating {K : Type} [Group K] [IsSimpleGroup K]
    (e0 : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  have hcenter : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exact h
    · exfalso
      have h1 : (Subgroup.center K).index = 1 := Subgroup.index_eq_one.2 h
      have h2 : Nat.card (K ⧸ Subgroup.center K) = 1 := by rw [← Subgroup.index_eq_card, h1]
      rw [Nat.card_congr e0.toEquiv, card_alternatingGroup_six] at h2
      omega
  exact ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hcenter.symm)).trans e0⟩

omit [Finite G] in
theorem card_le_card_map_mul [Finite G] {J U : Subgroup G} (hUJ : U ≤ J) {K : Type} [Group K]
    (π : ↥J →* K) {A : Subgroup G} (hA : ∀ u : ↥J, (u : G) ∈ U → π u = 1 → (u : G) ∈ A) :
    Nat.card ↥U ≤ Nat.card ↥((U.subgroupOf J).map π) * Nat.card ↥A := by
  let φ := π.domRestrict (U.subgroupOf J)
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [MonoidHom.domRestrict_range,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUJ).toEquiv] at h1
  have hker : Nat.card ↥φ.ker ≤ Nat.card ↥A := by
    refine Nat.card_le_card_of_injective
      (fun s => (⟨((s : ↥(U.subgroupOf J)) : ↥J).1, hA _ ?_ ?_⟩ : ↥A)) ?_
    · exact Subgroup.mem_subgroupOf.1 s.1.2
    · exact MonoidHom.mem_ker.1 s.2
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (Subtype.ext h1))
  rw [← h1]
  exact Nat.mul_le_mul_right _ hker |>.trans (by rw [mul_comm])

omit [Finite G] in
theorem ncard_conjSet_map_le [Finite G] {J U : Subgroup G} {K : Type} [Group K] [Finite K]
    (π : ↥J →* K) (hπ : Function.Surjective π) :
    (conjSet ⊤ ((U.subgroupOf J).map π)).ncard ≤
      {S : Subgroup G | ∃ j ∈ J, S = conjSubgroup j U}.ncard := by
  have hsub : conjSet ⊤ ((U.subgroupOf J).map π) ⊆
      (fun R : Subgroup G => (R.subgroupOf J).map π) '' {S | ∃ j ∈ J, S = conjSubgroup j U} := by
    rintro V' ⟨k, -, hk⟩
    obtain ⟨r, rfl⟩ := hπ k
    refine ⟨conjSubgroup (r : G) U, ⟨r, r.2, rfl⟩, ?_⟩
    show ((conjSubgroup (r : G) U).subgroupOf J).map π = V'
    rw [hk, ← conjSubgroup_subgroupOf J U r, map_conjSubgroup]
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))

theorem Sec66Cfg.noA6 [IsSimpleGroup G] (hF : A6KleinFacts) (h215 : Lemma215Stmt)
    (h26 : Lemma26Input) (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (c : Sec66Cfg U Tb P y y' q) :
    ¬ Nonempty (jQuot ↥(U ⊔ Tb ⊔ P) ⧸ Subgroup.center (jQuot ↥(U ⊔ Tb ⊔ P)) ≃*
      alternatingGroup (Fin 6)) := by
  rintro ⟨e0⟩
  obtain ⟨hK, hhyp, -, hker⟩ := c.jlemma h215 h26 hnab hind
  obtain ⟨a, ha2, haq, hcard, htr⟩ := c.trace_facts hnab
  obtain ⟨e⟩ := simple_equiv_alternating e0
  have hidx := hF _ ⟨e⟩ _ hhyp.1.1 hhyp.2.1
  have hV8 := card_le_eight_of_elemAbelian e hhyp.1.1
  have hUJ : U ≤ U ⊔ Tb ⊔ P := le_sup_left.trans le_sup_left
  have hU4 : Nat.card ↥U ≤ 8 * q := by
    have h1 := card_le_card_map_mul hUJ (jMap ↥(U ⊔ Tb ⊔ P))
      (A := normIn U Tb ⊓ normIn U P) (fun u hu hu1 => by
        have hmem := hker u (MonoidHom.mem_ker.2 hu1)
        exact ⟨mem_normIn.2 ⟨hu, mem_normalizer_iff_conjSubgroup_eq.2 (hmem 1)⟩,
          mem_normIn.2 ⟨hu, mem_normalizer_iff_conjSubgroup_eq.2 (hmem 2)⟩⟩)
    exact h1.trans (Nat.mul_le_mul hV8 c.cardA)
  have hq2 : q = 2 := by
    rw [c.cardU] at hU4
    have hq := c.hq
    have h4 : q ^ 3 = q * q ^ 2 := by ring
    by_contra hne
    have h5 : 3 ≤ q := by omega
    have h6 : 9 ≤ q ^ 2 := by nlinarith
    have h7 : q * 9 ≤ q * q ^ 2 := Nat.mul_le_mul_left q h6
    omega
  have ha : a = 2 := by omega
  have hTI : ∀ R ∈ sec66T U Tb P, ∀ S ∈ sec66T U Tb P, R ≠ S → R ⊓ S = ⊥ := by
    rintro R ⟨j₁, -, hR⟩ S ⟨j₂, -, hS⟩ hne
    exact inf_eq_bot_of_conj_conj c.wc hR hS hne
  have hbound := ncard_mul_pred_add_one_le (sec66Q U Tb P) (s := sec66T U Tb P) hTI htr
  rw [ha] at hbound hcard
  have hN : (Subgroup.normalizer (((U.subgroupOf (U ⊔ Tb ⊔ P)).map (jMap ↥(U ⊔ Tb ⊔ P)) :
      Subgroup (jQuot ↥(U ⊔ Tb ⊔ P))) : Set (jQuot ↥(U ⊔ Tb ⊔ P)))).index ≤
      (sec66T U Tb P).ncard :=
    (ncard_conjSet_top_eq_index _).symm.le.trans
      (ncard_conjSet_map_le (J := U ⊔ Tb ⊔ P) (U := U) (jMap ↥(U ⊔ Tb ⊔ P)) jMap_surjective)
  have h8 := hidx.trans hN
  norm_num at hbound hcard
  omega

theorem sec66A6Free_of_facts (hF : A6KleinFacts) : Sec66A6Free :=
  fun h215 h26 _ _ _ _ hnab hind _ _ _ _ _ _ c => c.noA6 hF h215 h26 hnab hind

theorem sec66_of_facts (h215 : Lemma215Stmt) (h26 : Lemma26Input) (hF : A6KleinFacts)
    (h62 : Sec62) (h63 : Sec63) : Sec66 :=
  sec66_proved h215 h26 (sec66A6Free_of_facts hF) h62 h63

end CFSG.CGT.Timmesfeld75
