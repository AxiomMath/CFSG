module

public import CFSG.Certificates.Kernel.SporSch.HNT0Replay
public import CFSG.Quasithin.Background.B2Thompson
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.KS.HNT0

open CFSG.Open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5
  CFSG.Sporadic.Co2Rank

section Abstract

variable {Γ : Type*} [Group Γ] {m : ℕ} {v : ℕ → Γ} {adj : ℕ → ℕ → Bool} {pr : ℕ → ℕ → ℕ}

theorem sinv_singleton (hs : Setting m v adj pr) {z : ℕ} (hz : z < m) : SInv m v [z] := by
  refine ⟨List.nodup_singleton _, by simpa using hz, ?_⟩
  have hz2 := (hs.sq z hz).1
  rintro x (rfl | ⟨i, hi, rfl⟩) y (rfl | ⟨j, hj, rfl⟩)
  · exact ⟨Or.inl (one_mul 1), rfl⟩
  · exact ⟨Or.inr ⟨j, hj, (one_mul _).symm⟩, by rw [one_mul, mul_one]⟩
  · exact ⟨Or.inr ⟨i, hi, (mul_one _).symm⟩, by rw [one_mul, mul_one]⟩
  · rw [List.mem_singleton] at hi hj
    subst hi hj
    exact ⟨Or.inl hz2, rfl⟩

theorem card_le_of_dfs [Finite Γ] (hs : Setting m v adj pr) {Q : Subgroup Γ} {z : ℕ}
    (hzm : z < m) (hzQ : ∀ x ∈ Q, x * v z = v z * x) (hzmem : v z ∈ Q)
    (hvQ : ∀ x ∈ Q, x ≠ 1 → x * x = 1 → ∃ a < m, v a = x)
    (hdfs : dfs adj pr 5 [z] ((List.range m).filter fun c => adj c z) 0 = true) :
    ∀ E : Subgroup Γ, E ≤ Q → IsElemAbelian 2 E → Nat.card E ≤ 64 := by
  classical
  intro E hEQ hE
  have hz2 : v z * v z = 1 := (hs.sq z hzm).1
  have hE' : IsElemAbelian 2 (E ⊔ Subgroup.zpowers (v z)) := by
    refine hE.sup_of_commute (isElemAbelian_zpowers (by rw [sq]; exact hz2)) fun a ha b hb => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hzQ a (hEQ ha)) k).eq
  have hE'Q : E ⊔ Subgroup.zpowers (v z) ≤ Q := sup_le hEQ (Subgroup.zpowers_le.2 hzmem)
  have : Fintype Γ := Fintype.ofFinite Γ
  set F : Finset Γ := Finset.univ.filter (· ∈ E ⊔ Subgroup.zpowers (v z)) with hF
  have hmemF : ∀ x, x ∈ F ↔ x ∈ E ⊔ Subgroup.zpowers (v z) := fun x => by simp [hF]
  have hsqF : ∀ x ∈ F, x * x = 1 := fun x hx => hE'.mul_self_eq_one ((hmemF x).1 hx)
  have hGood : GoodF m v F := by
    refine ⟨(hmemF 1).2 (one_mem _), fun x hx y hy => ?_, hsqF, fun x hx hx1 => ?_⟩
    · rw [hmemF] at hx hy ⊢
      exact ⟨mul_mem hx hy, hE'.comm hx hy⟩
    · exact hvQ x (hE'Q ((hmemF x).1 hx)) hx1 (hsqF x hx)
  have hbound := dfs_sound hs 5 [z] _ 0 F (sinv_singleton hs hzm)
    (fun c hc _ hadj => List.mem_filter.2 ⟨List.mem_range.2 hc,
      hadj z (List.mem_singleton_self _)⟩)
    hGood (fun i hi => by
      rw [List.mem_singleton] at hi
      subst hi
      exact (hmemF _).2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
    (fun i _ _ _ => Nat.zero_le i) hdfs
  have hFcard : F.card = Nat.card ↥(E ⊔ Subgroup.zpowers (v z)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc Nat.card E ≤ Nat.card ↥(E ⊔ Subgroup.zpowers (v z)) :=
        Subgroup.card_le_of_le le_sup_left
    _ = F.card := hFcard.symm
    _ ≤ 2 ^ 5 * ([z].length + 1) := hbound
    _ = 64 := by norm_num

theorem sinv_of_extOK (hs : Setting m v adj pr) :
    ∀ (cs S : List ℕ), SInv m v S → S ≠ [] → ExtOK adj pr S cs →
      SInv m v (cs.foldl (childS pr) S) ∧
        (cs.foldl (childS pr) S).length + 1 = 2 ^ cs.length * (S.length + 1)
  | [], S, hS, _, _ => ⟨hS, by simp⟩
  | c :: cs, S, hS, hne, hb => by
    simp only [ExtOK] at hb
    obtain ⟨hcS', hadj, hrest⟩ := hb
    have hcm : c < m := by
      obtain ⟨s, hs'⟩ := List.exists_mem_of_ne_nil S hne
      exact ((hs.adj_iff c s).1 (hadj s hs')).1
    obtain ⟨h1, h2⟩ := sinv_of_extOK hs cs (childS pr S c) (sinv_child hs hS hcm hcS' hadj)
      (by simp [childS]) hrest
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, card_childS, List.length_cons, pow_succ, mul_assoc]

def spanOf (hs : Setting m v adj pr) {S : List ℕ} (hS : SInv m v S) : Subgroup Γ where
  carrier := Sset v S
  mul_mem' hx hy := (hS.closed _ hx _ hy).1
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro x (rfl | ⟨i, hi, rfl⟩)
    · exact Or.inl inv_one
    · exact Or.inr ⟨i, hi, (inv_eq_of_mul_eq_one_left (hs.sq i (hS.lt i hi)).1).symm⟩

theorem mem_spanOf (hs : Setting m v adj pr) {S : List ℕ} (hS : SInv m v S) {x : Γ} :
    x ∈ spanOf hs hS ↔ x ∈ Sset v S := Iff.rfl

theorem isElemAbelian_spanOf (hs : Setting m v adj pr) {S : List ℕ} (hS : SInv m v S) :
    IsElemAbelian 2 (spanOf hs hS) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (hS.closed _ x.2 _ y.2).2⟩⟩, fun x hx => ?_⟩
  rw [sq]
  rcases hx with rfl | ⟨i, hi, rfl⟩
  · exact one_mul 1
  · exact (hs.sq i (hS.lt i hi)).1

theorem le_card_spanOf [Finite Γ] (hs : Setting m v adj pr) {S : List ℕ}
    (hS : SInv m v S) : S.length + 1 ≤ Nat.card (spanOf hs hS) := by
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hnd : (S.map v).Nodup := hS.nodup.map_on fun x hx y hy hxy =>
    hs.inj x y (hS.lt x hx) (hS.lt y hy) hxy
  have h1 : (1 : Γ) ∉ (S.map v).toFinset := by
    simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]
    exact fun i hi h => (hs.sq i (hS.lt i hi)).2 h
  calc S.length + 1 = (insert 1 (S.map v).toFinset).card := by
        rw [Finset.card_insert_of_notMem h1, List.toFinset_card_of_nodup hnd, List.length_map]
    _ ≤ (Finset.univ.filter (· ∈ spanOf hs hS)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, List.mem_toFinset, List.mem_map] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | ⟨i, hi, rfl⟩
        · exact one_mem _
        · exact Or.inr ⟨i, hi, rfl⟩

theorem rank_facts_of_ext [Finite Γ] (hs : Setting m v adj pr) {Q : Subgroup Γ} {z : ℕ}
    (hzm : z < m) (hzQ : ∀ x ∈ Q, x * v z = v z * x) (hzmem : v z ∈ Q)
    (hvQ : ∀ x ∈ Q, x ≠ 1 → x * x = 1 → ∃ a < m, v a = x) (hvmem : ∀ a < m, v a ∈ Q)
    (hdfs : dfs adj pr 5 [z] ((List.range m).filter fun c => adj c z) 0 = true)
    {EB : List (List ℕ)} {ZW : List ℕ} (hEB0 : EB ≠ []) (hZW : ZW.length = 3)
    (hEB : ∀ bs ∈ EB, bs.length = 5 ∧ ExtOK adj pr [z] bs)
    (hW : ∀ w < m, (∀ bs ∈ EB, ∀ s ∈ bs.foldl (childS pr) [z], adj w s = true ∨ w = s) →
      w ∈ ZW) :
    (∀ E : Subgroup Γ, E ≤ Q → IsElemAbelian 2 E → Nat.card E ≤ 64) ∧
    v z ∈ omegaOneCenterOf (thompsonJ Q) ∧ Nat.card (omegaOneCenterOf (thompsonJ Q)) ≤ 4 := by
  classical
  have hrank := card_le_of_dfs hs hzm hzQ hzmem hvQ hdfs
  refine ⟨hrank, ?_, ?_⟩
  · rw [(omegaOne_centralizer_thompsonJ Q).2]
    refine Subgroup.mem_iInf.2 fun A => Subgroup.mem_iInf.2 fun hA => ?_
    rw [eq_omegaOneOf_centralizer hA]
    refine Subgroup.subset_closure ⟨⟨hzmem, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩, ?_⟩
    · exact hzQ a (hA.1 ha)
    · rw [sq]
      exact (hs.sq z hzm).1
  · have hspan : ∀ bs ∈ EB, SInv m v (bs.foldl (childS pr) [z]) ∧
        (bs.foldl (childS pr) [z]).length + 1 = 64 := by
      intro bs hbs
      obtain ⟨hlen, hok⟩ := hEB bs hbs
      obtain ⟨h1, h2⟩ := sinv_of_extOK hs bs [z] (sinv_singleton hs hzm) (by simp) hok
      exact ⟨h1, by rw [h2, hlen]; rfl⟩
    have hmax : ∀ bs (hbs : bs ∈ EB), IsMaxElemAbelian Q (spanOf hs (hspan bs hbs).1) := by
      intro bs hbs
      refine ⟨?_, isElemAbelian_spanOf hs _, fun B hBQ hB => ?_⟩
      · rintro x (rfl | ⟨i, hi, rfl⟩)
        · exact one_mem _
        · exact hvmem i ((hspan bs hbs).1.lt i hi)
      · calc Nat.card B ≤ 64 := hrank B hBQ hB
          _ = (bs.foldl (childS pr) [z]).length + 1 := (hspan bs hbs).2.symm
          _ ≤ Nat.card (spanOf hs (hspan bs hbs).1) := le_card_spanOf hs _
    have hVle : ∀ bs (hbs : bs ∈ EB),
        omegaOneCenterOf (thompsonJ Q) ≤ spanOf hs (hspan bs hbs).1 := by
      intro bs hbs
      rw [(omegaOne_centralizer_thompsonJ Q).2]
      exact iInf₂_le _ (hmax bs hbs)
    obtain ⟨b0, hb0⟩ := List.exists_mem_of_ne_nil EB hEB0
    have hsub : ∀ x ∈ omegaOneCenterOf (thompsonJ Q), x = 1 ∨ ∃ w ∈ ZW, v w = x := by
      intro x hx
      rcases (mem_spanOf hs _).1 (hVle _ hb0 hx) with h1 | ⟨w, hw, rfl⟩
      · exact Or.inl h1
      · right
        have hwm := (hspan _ hb0).1.lt w hw
        refine ⟨w, hW w hwm fun bs hbs s hsT => ?_, rfl⟩
        by_cases hws : w = s
        · exact Or.inr hws
        · left
          have hxT := (mem_spanOf hs _).1 (hVle bs hbs hx)
          have hsT' : v s ∈ Sset v (bs.foldl (childS pr) [z]) := Or.inr ⟨s, hsT, rfl⟩
          obtain ⟨hprodT, hcomm⟩ := (hspan bs hbs).1.closed _ hxT _ hsT'
          have hsm := (hspan bs hbs).1.lt s hsT
          rw [hs.adj_iff]
          refine ⟨hwm, hsm, hcomm, ?_⟩
          rcases hprodT with h1 | ⟨k, hk, hkv⟩
          · exact absurd (hs.inj w s hwm hsm (mul_eq_one_imp (hs.sq s hsm).1 h1)) hws
          · exact ⟨k, (hspan bs hbs).1.lt k hk, hkv⟩
    have : Fintype Γ := Fintype.ofFinite Γ
    calc Nat.card (omegaOneCenterOf (thompsonJ Q))
        ≤ (insert 1 (ZW.map v).toFinset).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          simp only [Finset.mem_insert, List.mem_toFinset, List.mem_map]
          rcases hsub x hx with h1 | ⟨w, hw, hwx⟩
          · exact Or.inl h1
          · exact Or.inr ⟨w, hw, hwx⟩
      _ ≤ (ZW.map v).toFinset.card + 1 := Finset.card_insert_le _ _
      _ ≤ ZW.length + 1 := by
          have := List.toFinset_card_le (ZW.map v)
          rw [List.length_map] at this
          omega
      _ ≤ 4 := by omega

theorem rank_facts_of_replay [Finite Γ] {AL PR DF DFO : ℕ → ℕ}
    (hs : Setting m v (adjT AL m) (prT PR)) (hG : GraphFacts AL PR m) {Q : Subgroup Γ} {z n0 : ℕ}
    (hzm : z < m) (hzQ : ∀ x ∈ Q, x * v z = v z * x) (hzmem : v z ∈ Q)
    (hvQ : ∀ x ∈ Q, x ≠ 1 → x * x = 1 → ∃ a < m, v a = x) (hvmem : ∀ a < m, v a ∈ Q)
    (hroot : rootK AL DF DFO z n0 = true) (hsub : ∀ j < n0, subK AL PR DF DFO z j = true)
    {EB : List (List ℕ)} {ZW : List ℕ} (heb : ebK AL PR m z EB ZW = true) :
    (∀ E : Subgroup Γ, E ≤ Q → IsElemAbelian 2 E → Nat.card E ≤ 64) ∧
    v z ∈ omegaOneCenterOf (thompsonJ Q) ∧ Nat.card (omegaOneCenterOf (thompsonJ Q)) ≤ 4 := by
  obtain ⟨hl, hz, hb, hw⟩ := ebK_sound hG hzm heb
  refine rank_facts_of_ext hs hzm hzQ hzmem hvQ hvmem (dfs_of_replay hG hzm hroot hsub) ?_ hz hb hw
  rintro rfl
  simp at hl

end Abstract

section Enum

variable {Γ : Type*} [Group Γ] {V : Type*} [MulAction Γ V]
variable {pt : ℕ → V} {n N m ng : ℕ} {gens : ℕ → Γ} {ι : ℕ → Γ} {BP INV : List ℕ}
  {T IL AL PR DF DFO : ℕ → ℕ} {KB : ℕ}

theorem EnumFacts.rank_facts [Finite Γ] (hE : EnumFacts pt n N ng gens ι BP T)
    (hinj : ∀ k < N, ∀ l < N, ι k = ι l → k = l)
    (hcens : ∀ k < N, censK 8 255 BP T (maskL INV) k = true)
    (hinvL : invLK 8 255 BP N 24 T IL KB INV 0 0 = true) (hm : INV.length = m)
    (hm1024 : m ≤ 1024) (hadj : ∀ a < m, adjK m 8 255 BP 24 IL AL PR KB a = true) {z n0 : ℕ}
    (hzm : z < m)
    (hzQ : ∀ x ∈ genSub gens ng, x * ι (INV.getD z 0) = ι (INV.getD z 0) * x)
    (hroot : rootK AL DF DFO z n0 = true) (hsub : ∀ j < n0, subK AL PR DF DFO z j = true)
    {EB : List (List ℕ)} {ZW : List ℕ} (heb : ebK AL PR m z EB ZW = true) :
    (∀ E : Subgroup Γ, E ≤ genSub gens ng → IsElemAbelian 2 E → Nat.card E ≤ 64) ∧
    ι (INV.getD z 0) ∈ omegaOneCenterOf (thompsonJ (genSub gens ng)) ∧
    Nat.card (omegaOneCenterOf (thompsonJ (genSub gens ng))) ≤ 4 := by
  obtain ⟨hs, hhigh⟩ := hE.setting hinj hcens hinvL hm hadj
  have hG := GraphFacts.of_setting hs hm1024 hhigh fun a ha => adjK_low (hadj a ha)
  obtain ⟨-, hlt, -⟩ := invLK_spec INV 0 0 hinvL
  have hget : ∀ a < m, INV.getD a 0 ∈ INV := fun a ha => by
    have ha' : a < INV.length := by omega
    have e : INV.getD a 0 = INV[a] := by simp [List.getD_eq_getElem?_getD, ha']
    rw [e]
    exact List.getElem_mem ha'
  have hvmem : ∀ a < m, ι (INV.getD a 0) ∈ genSub gens ng := fun a ha =>
    hE.mem _ (hlt _ (hget a ha)).2
  have hvQ : ∀ x ∈ genSub gens ng, x ≠ 1 → x * x = 1 →
      ∃ a < m, ι (INV.getD a 0) = x := by
    intro x hx hx1 hxx
    obtain ⟨k, hk, rfl⟩ := hE.surj x hx
    have hkI := (hE.inv_iff hcens hk).1 ⟨hxx, hx1⟩
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hkI
    refine ⟨a, by omega, ?_⟩
    have e : INV.getD a 0 = INV[a] := by simp [List.getD_eq_getElem?_getD, ha]
    rw [e]
  exact rank_facts_of_replay (v := fun a => ι (INV.getD a 0)) hs hG hzm hzQ (hvmem z hzm) hvQ
    hvmem hroot hsub heb

end Enum

end CFSG.KS.HNT0

end
