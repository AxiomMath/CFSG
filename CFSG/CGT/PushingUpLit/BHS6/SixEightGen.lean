module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsCount
public import CFSG.CGT.PushingUpLit.BHS.SymNatSwaps
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.A1b CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement Pointwise

variable {n : ℕ}

theorem altOn_insert_le (H : Subgroup (Equiv.Perm (Fin n))) {S : Finset (Fin n)}
    (hS : 3 ≤ S.card) (hH : altOn S ≤ H) {p : Fin n} (hp : p ∉ S)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ H) (hσ3 : σ.IsThreeCycle)
    (hsupp : σ.support ⊆ insert p S) (hpσ : p ∈ σ.support) :
    altOn (insert p S) ≤ H := by
  classical
  set S' : Finset (Fin n) := insert p S with hS'
  have hcard : 3 ≤ Nat.card ↥S' := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hS', Finset.card_insert_of_notMem hp]
    omega
  let p' : ↥S' := ⟨p, Finset.mem_insert_self p S⟩
  have hcoatom := alternatingGroup.isCoatom_stabilizer_singleton (α := ↥S') hcard
    (s := {p'}) (Set.singleton_nonempty p') Set.subsingleton_singleton
  let K : Subgroup ↥(alternatingGroup ↥S') :=
    (H.comap (Equiv.Perm.ofSubtype : Equiv.Perm ↥S' →* Equiv.Perm (Fin n))).subgroupOf
      (alternatingGroup ↥S')
  have hle : MulAction.stabilizer ↥(alternatingGroup ↥S') ({p'} : Set ↥S') ≤ K := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff, Set.smul_set_singleton, Set.singleton_eq_singleton_iff]
      at hg
    show Equiv.Perm.ofSubtype (g : Equiv.Perm ↥S') ∈ H
    apply hH
    rw [mem_altOn]
    refine ⟨fun x hx => ?_, ?_⟩
    · by_cases hxS' : x ∈ S'
      · have hxp : x = p := by
          rcases Finset.mem_insert.mp hxS' with h | h
          · exact h
          · exact absurd h hx
        subst hxp
        rw [Equiv.Perm.ofSubtype_apply_of_mem _ hxS']
        exact congrArg Subtype.val hg
      · exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hxS'
    · rw [Equiv.Perm.sign_ofSubtype]
      exact Equiv.Perm.mem_alternatingGroup.mp g.2
  have h₁ : ∀ x, σ x ∈ S' ↔ x ∈ S' := by
    intro x
    by_cases hx : σ x = x
    · rw [hx]
    · have hxs : x ∈ σ.support := Equiv.Perm.mem_support.2 hx
      have hσxs : σ x ∈ σ.support := Equiv.Perm.apply_mem_support.2 hxs
      exact ⟨fun _ => hsupp hxs, fun _ => hsupp hσxs⟩
  have h₂ : ∀ x, σ x ≠ x → x ∈ S' := fun x hx => hsupp (Equiv.Perm.mem_support.2 hx)
  let σ'' : ↥(alternatingGroup ↥S') := ⟨σ.subtypePerm h₁, Equiv.Perm.mem_alternatingGroup.mpr (by
    have := (Equiv.Perm.sign_subtypePerm σ h₁ h₂).trans hσ3.sign
    convert this)⟩
  have hσK : σ'' ∈ K := by
    show Equiv.Perm.ofSubtype (σ.subtypePerm h₁) ∈ H
    rw [Equiv.Perm.ofSubtype_subtypePerm h₁ h₂]
    exact hσ
  have hσst : σ'' ∉ MulAction.stabilizer ↥(alternatingGroup ↥S') ({p'} : Set ↥S') := by
    intro h
    rw [MulAction.mem_stabilizer_iff, Set.smul_set_singleton, Set.singleton_eq_singleton_iff]
      at h
    have h' := congrArg Subtype.val h
    exact (Equiv.Perm.mem_support.1 hpσ) h'
  have hK : K = ⊤ := by
    rcases hcoatom.le_iff.mp hle with h | h
    · exact h
    · exact absurd (h ▸ hσK) hσst
  intro g hg
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
  have : (⟨g', hg'⟩ : ↥(alternatingGroup ↥S')) ∈ K := hK ▸ Subgroup.mem_top _
  exact this

theorem cyc_mul_cyc_inv {x y c s : Fin n} (hxy : x ≠ y) (hxc : x ≠ c) (hxs : x ≠ s) (hyc : y ≠ c)
    (hys : y ≠ s) (hcs : c ≠ s) : cyc x y c * (cyc x y s)⁻¹ = cyc y c s := by
  rw [cyc_inv]
  ext m
  simp only [cyc, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem support_cyc_subset (i j k : Fin n) : (cyc i j k).support ⊆ {i, j, k} := by
  intro m hm
  by_contra h
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  exact (Equiv.Perm.mem_support.1 hm) (cyc_apply_of_ne h.1 h.2.1 h.2.2)

theorem cyc_mem_altOn {S : Finset (Fin n)} {i j k : Fin n} (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : cyc i j k ∈ altOn S := by
  rw [mem_altOn]
  refine ⟨fun m hm => cyc_apply_of_ne ?_ ?_ ?_, (cyc_isThreeCycle hij hik hjk).sign⟩ <;>
    rintro rfl <;> contradiction

theorem altOn_three_le (H : Subgroup (Equiv.Perm (Fin n))) {x y c : Fin n} (hxy : x ≠ y)
    (hxc : x ≠ c) (hyc : y ≠ c) (hσ : cyc x y c ∈ H) : altOn {x, y, c} ≤ H := by
  classical
  have hcard : ({x, y, c} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.2 ⟨x, y, c, hxy, hxc, hyc, rfl⟩
  have hmem : cyc x y c ∈ altOn ({x, y, c} : Finset (Fin n)) :=
    cyc_mem_altOn (by simp) (by simp) (by simp) hxy hxc hyc
  have hz : Subgroup.zpowers (cyc x y c) ≤ altOn ({x, y, c} : Finset (Fin n)) :=
    (Subgroup.zpowers_le).2 hmem
  have hcz : Nat.card (altOn ({x, y, c} : Finset (Fin n))) ≤
      Nat.card (Subgroup.zpowers (cyc x y c)) := by
    rw [Nat.card_zpowers, (cyc_isThreeCycle hxy hxc hyc).orderOf, card_altOn (by omega), hcard]
    decide
  have heq := Subgroup.eq_of_le_of_card_ge hz hcz
  rw [← heq]
  exact (Subgroup.zpowers_le).2 hσ

theorem altOn_insert_pair_le (H : Subgroup (Equiv.Perm (Fin n))) {S : Finset (Fin n)}
    (hS : 3 ≤ S.card) (hH : altOn S ≤ H) {c : Fin n} (hc : c ∈ S) {x y : Fin n} (hx : x ∉ S)
    (hy : y ∉ S) (hxy : x ≠ y) (hσ : cyc x y c ∈ H) :
    altOn (insert x (insert y S)) ≤ H := by
  classical
  have hxc : x ≠ c := fun h => hx (h ▸ hc)
  have hyc : y ≠ c := fun h => hy (h ▸ hc)
  obtain ⟨s, hsc, hs⟩ : ∃ s, s ≠ c ∧ s ∈ S := by
    have : 0 < (S.erase c).card := by
      rw [Finset.card_erase_of_mem hc]
      omega
    obtain ⟨s, hs⟩ := Finset.card_pos.mp this
    exact ⟨s, (Finset.mem_erase.1 hs).1, (Finset.mem_erase.1 hs).2⟩
  obtain ⟨s'', hs''s, hs''c, hs''⟩ : ∃ s'', s'' ≠ s ∧ s'' ≠ c ∧ s'' ∈ S := by
    have : 0 < ((S.erase c).erase s).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hsc, hs⟩), Finset.card_erase_of_mem hc]
      omega
    obtain ⟨t, ht⟩ := Finset.card_pos.mp this
    have h1 := Finset.mem_erase.1 ht
    have h2 := Finset.mem_erase.1 h1.2
    exact ⟨t, h1.1, h2.1, h2.2⟩
  have hxS : x ≠ s := fun h => hx (h ▸ hs)
  have hyS : y ≠ s := fun h => hy (h ▸ hs)
  have hxS'' : x ≠ s'' := fun h => hx (h ▸ hs'')
  have hyS'' : y ≠ s'' := fun h => hy (h ▸ hs'')
  have hρ : cyc c s'' s ∈ H :=
    hH (cyc_mem_altOn hc hs'' hs (Ne.symm hs''c) (Ne.symm hsc) hs''s)
  have hρx : cyc c s'' s x = x := cyc_apply_of_ne hxc hxS'' hxS
  have hρy : cyc c s'' s y = y := cyc_apply_of_ne hyc hyS'' hyS
  have hρc : cyc c s'' s c = s := cyc_apply_first (Ne.symm hsc) hs''s
  have hσs : cyc x y s ∈ H := by
    have h1 : cyc c s'' s * cyc x y c * (cyc c s'' s)⁻¹ = cyc x y s := by
      rw [conj_cyc, hρx, hρy, hρc]
    rw [← h1]
    exact H.mul_mem (H.mul_mem hρ hσ) (H.inv_mem hρ)
  have hτ : cyc y c s ∈ H := by
    rw [← cyc_mul_cyc_inv hxy hxc hxS hyc hyS (Ne.symm hsc)]
    exact H.mul_mem hσ (H.inv_mem hσs)
  have hysupp : (cyc y c s).support ⊆ insert y S := by
    refine (support_cyc_subset y c s).trans ?_
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
    rcases hm with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hc
    · exact Or.inr hs
  have h1 : altOn (insert y S) ≤ H :=
    altOn_insert_le H hS hH hy hτ
      (cyc_isThreeCycle hyc (Ne.symm hyS |>.symm) (Ne.symm hsc).symm.symm) hysupp
      (Equiv.Perm.mem_support.2 (by
        rw [cyc_apply_first hyS (Ne.symm hsc)]
        exact Ne.symm hyS))
  have hxS₁ : x ∉ insert y S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hxy, hx⟩
  have hcard₁ : 3 ≤ (insert y S).card := by
    rw [Finset.card_insert_of_notMem hy]
    omega
  have hxsupp : (cyc x y c).support ⊆ insert x (insert y S) := by
    refine (support_cyc_subset x y c).trans ?_
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
    rcases hm with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hc)
  exact altOn_insert_le H hcard₁ h1 hxS₁ hσ (cyc_isThreeCycle hxy hxc hyc) hxsupp
    (Equiv.Perm.mem_support.2 (by
      rw [cyc_apply_first hxc hyc]
      exact Ne.symm hxc))

theorem alternatingGroup_le_of_cyc_mem (H : Subgroup (Equiv.Perm (Fin n)))
    {T' : Set (Equiv.Perm (Fin n))} (hs : ∀ t ∈ T', t.IsSwap)
    (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) (ht : T'.Nonempty)
    (hfix : ∃ c, ∀ t ∈ T', t c = c)
    (hH : ∀ t ∈ T', ∀ x, t x ≠ x → ∀ c, (∀ t' ∈ T', t' c = c) → cyc x (t x) c ∈ H) :
    alternatingGroup (Fin n) ≤ H := by
  classical
  have hfinT : T'.Finite := Set.toFinite T'
  obtain ⟨t₁, ht₁⟩ := ht
  obtain ⟨c₀, hc₀⟩ := hfix
  obtain ⟨x₁, y₁, hxy₁, ht₁eq⟩ := hs t₁ ht₁
  have hx₁ : t₁ x₁ ≠ x₁ := by
    rw [ht₁eq, Equiv.swap_apply_left]
    exact hxy₁.symm
  have hy₁ : t₁ x₁ = y₁ := by rw [ht₁eq, Equiv.swap_apply_left]
  have hy₁' : t₁ y₁ ≠ y₁ := by
    rw [ht₁eq, Equiv.swap_apply_right]
    exact hxy₁
  set Fx : Finset (Fin n) := Finset.univ.filter (fun c => ∀ t ∈ T', t c = c) with hFx
  have hmemFx : ∀ c, c ∈ Fx ↔ ∀ t ∈ T', t c = c := fun c => by simp [hFx]
  have hx₁c : x₁ ≠ c₀ := fun h => hx₁ (h ▸ hc₀ t₁ ht₁)
  have hy₁c : y₁ ≠ c₀ := fun h => hy₁' (h ▸ hc₀ t₁ ht₁)
  have hB : ∀ R : Finset (Fin n), (∀ c ∈ R, ∀ t ∈ T', t c = c) →
      altOn ({x₁, y₁, c₀} ∪ R) ≤ H := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.union_empty]
      exact altOn_three_le H hxy₁ hx₁c hy₁c (by
        have := hH t₁ ht₁ x₁ hx₁ c₀ hc₀
        rwa [hy₁] at this)
    | insert c' R hc'R ih =>
      intro hR
      have hRR : ∀ c ∈ R, ∀ t ∈ T', t c = c := fun c hc => hR c (Finset.mem_insert_of_mem hc)
      have hc'fix : ∀ t ∈ T', t c' = c' := hR c' (Finset.mem_insert_self _ _)
      by_cases hmem : c' ∈ ({x₁, y₁, c₀} : Finset (Fin n)) ∪ R
      · rw [Finset.union_insert, Finset.insert_eq_of_mem hmem]
        exact ih hRR
      · rw [Finset.union_insert]
        have hx₁c' : x₁ ≠ c' := fun h => hx₁ (h ▸ hc'fix t₁ ht₁)
        have hy₁c' : y₁ ≠ c' := fun h => hy₁' (h ▸ hc'fix t₁ ht₁)
        refine altOn_insert_le H ?_ (ih hRR) hmem (σ := cyc x₁ y₁ c') ?_ ?_ ?_ ?_
        · have : ({x₁, y₁, c₀} : Finset (Fin n)) ⊆ {x₁, y₁, c₀} ∪ R := Finset.subset_union_left
          calc 3 = ({x₁, y₁, c₀} : Finset (Fin n)).card :=
                (Finset.card_eq_three.2 ⟨x₁, y₁, c₀, hxy₁, hx₁c, hy₁c, rfl⟩).symm
            _ ≤ _ := Finset.card_le_card this
        · have := hH t₁ ht₁ x₁ hx₁ c' hc'fix
          rwa [hy₁] at this
        · exact cyc_isThreeCycle hxy₁ hx₁c' hy₁c'
        · refine (support_cyc_subset x₁ y₁ c').trans ?_
          intro m hm
          simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hm ⊢
          rcases hm with rfl | rfl | rfl
          · exact Or.inr (Or.inl (Or.inl rfl))
          · exact Or.inr (Or.inl (Or.inr (Or.inl rfl)))
          · exact Or.inl rfl
        · exact Equiv.Perm.mem_support.2 (by
            rw [cyc_apply_third]
            exact hy₁c')
  set S₁ : Finset (Fin n) := {x₁, y₁, c₀} ∪ Fx with hS₁
  have hS₁H : altOn S₁ ≤ H := hB Fx fun c hc => (hmemFx c).1 hc
  have hS₁card : 3 ≤ S₁.card := by
    calc 3 = ({x₁, y₁, c₀} : Finset (Fin n)).card :=
          (Finset.card_eq_three.2 ⟨x₁, y₁, c₀, hxy₁, hx₁c, hy₁c, rfl⟩).symm
      _ ≤ _ := Finset.card_le_card Finset.subset_union_left
  have hc₀S₁ : c₀ ∈ S₁ := by simp [hS₁]
  have hC : ∀ 𝒬 : Finset (Equiv.Perm (Fin n)), (∀ t ∈ 𝒬, t ∈ T') →
      altOn (S₁ ∪ 𝒬.biUnion Equiv.Perm.support) ≤ H := by
    intro 𝒬
    induction 𝒬 using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.biUnion_empty, Finset.union_empty]
      exact hS₁H
    | insert t 𝒬 htQ ih =>
      intro h𝒬
      have htT : t ∈ T' := h𝒬 t (Finset.mem_insert_self _ _)
      have h𝒬' : ∀ t' ∈ 𝒬, t' ∈ T' := fun t' h => h𝒬 t' (Finset.mem_insert_of_mem h)
      have hset : S₁ ∪ (insert t 𝒬).biUnion Equiv.Perm.support =
          (S₁ ∪ 𝒬.biUnion Equiv.Perm.support) ∪ t.support := by
        rw [Finset.biUnion_insert]
        ext m
        simp only [Finset.mem_union]
        tauto
      rw [hset]
      set S : Finset (Fin n) := S₁ ∪ 𝒬.biUnion Equiv.Perm.support with hS
      have hSH : altOn S ≤ H := ih h𝒬'
      have hS₁S : S₁ ⊆ S := Finset.subset_union_left
      obtain ⟨x, y, hxy, hteq⟩ := hs t htT
      have hsuppt : t.support = {x, y} := by
        rw [hteq]
        exact Equiv.Perm.support_swap hxy
      by_cases ht₁t : t = t₁
      · have hsub : t.support ⊆ S := by
          rw [ht₁t, ht₁eq, Equiv.Perm.support_swap hxy₁]
          intro m hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          apply hS₁S
          rcases hm with rfl | rfl <;> simp [hS₁]
        rw [Finset.union_eq_left.2 hsub]
        exact hSH
      · have hdisj : ∀ t' ∈ T', t' ≠ t → ∀ m, t m ≠ m → t' m = m := fun t' ht' hne m hm =>
          apply_eq_of_commute_swap (hs t htT) (hs t' ht') (hc t htT t' ht') (Ne.symm hne) hm
        have hxm : t x ≠ x := by
          rw [hteq, Equiv.swap_apply_left]
          exact hxy.symm
        have hym : t y ≠ y := by
          rw [hteq, Equiv.swap_apply_right]
          exact hxy
        have hnot : ∀ m, t m ≠ m → m ∉ S := by
          intro m hm hmS
          rcases Finset.mem_union.1 hmS with h | h
          · rcases Finset.mem_union.1 h with h' | h'
            · simp only [Finset.mem_insert, Finset.mem_singleton] at h'
              rcases h' with rfl | rfl | rfl
              · exact hx₁ (hdisj t₁ ht₁ (Ne.symm ht₁t) _ hm)
              · exact hy₁' (hdisj t₁ ht₁ (Ne.symm ht₁t) _ hm)
              · exact hm (hc₀ t htT)
            · exact hm ((hmemFx m).1 h' t htT)
          · obtain ⟨t', ht'Q, hmt'⟩ := Finset.mem_biUnion.1 h
            have hne : t' ≠ t := fun h => htQ (h ▸ ht'Q)
            exact (Equiv.Perm.mem_support.1 hmt') (hdisj t' (h𝒬' t' ht'Q) hne m hm)
        have hxS : x ∉ S := hnot x hxm
        have hyS : y ∉ S := hnot y hym
        have hσ : cyc x y c₀ ∈ H := by
          have := hH t htT x hxm c₀ hc₀
          rwa [hteq, Equiv.swap_apply_left] at this
        have hres := altOn_insert_pair_le H (hS₁card.trans (Finset.card_le_card hS₁S)) hSH
          (hS₁S hc₀S₁) hxS hyS hxy hσ
        have hset2 : S ∪ t.support = insert x (insert y S) := by
          rw [hsuppt]
          ext m
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hset2]
        exact hres
  have hU : S₁ ∪ (hfinT.toFinset).biUnion Equiv.Perm.support = Finset.univ := by
    refine Finset.eq_univ_iff_forall.2 fun m => ?_
    by_cases hm : ∀ t ∈ T', t m = m
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((hmemFx m).2 hm))
    · push Not at hm
      obtain ⟨t, htT, htm⟩ := hm
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨t, hfinT.mem_toFinset.2 htT, Equiv.Perm.mem_support.2 htm⟩)
  have hfin := hC hfinT.toFinset fun t ht => hfinT.mem_toFinset.1 ht
  rw [hU] at hfin
  intro g hg
  exact hfin (mem_altOn.2 ⟨fun x hx => absurd (Finset.mem_univ x) hx,
    Equiv.Perm.mem_alternatingGroup.1 hg⟩)
