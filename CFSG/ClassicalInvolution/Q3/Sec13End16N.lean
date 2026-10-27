module

public import CFSG.ClassicalInvolution.Q3.Sec13End16B
public import CFSG.ClassicalInvolution.Q3.Sec13End16M
import CFSG.ClassicalInvolution.Q3.Sec13End15H

public section

namespace CFSG.ClassicalInvolution.Q3.AE


open Wr

variable {n : ℕ}
private theorem e16n_kList_perm :
    ∀ k ∈ kList, k.perm = 1 ∨ k.perm = d₁ ∨ k.perm = d₂ ∨ k.perm = d₃ := by
  decide +kernel
private theorem e16n_kStarList_perm :
    ∀ k ∈ kStarList, k.perm = 1 ∨ k.perm = d₁ ∨ k.perm = d₂ ∨ k.perm = d₃ := by
  decide +kernel
private theorem e16n_d₁_no_fix : ∀ i : Fin 4, d₁ i ≠ i := by decide

private theorem e16n_memAt_perm {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} {a : Wr n}
    (ha : a ∈ memAt α h b) :
    a.perm = 1 ∨ ∃ d ∈ [d₁, d₂, d₃], a.perm = embedPerm (emb α h) d := by
  have key : ∀ k : Wr 4, (k.perm = 1 ∨ k.perm = d₁ ∨ k.perm = d₂ ∨ k.perm = d₃) →
      (embed (emb α h) k).perm = 1 ∨
        ∃ d ∈ [d₁, d₂, d₃], (embed (emb α h) k).perm = embedPerm (emb α h) d := by
    intro k hk
    rw [embed_perm]
    rcases hk with hk | hk | hk | hk
    · left
      rw [hk, embedPerm_one]
    · right
      exact ⟨d₁, by simp, by rw [hk]⟩
    · right
      exact ⟨d₂, by simp, by rw [hk]⟩
    · right
      exact ⟨d₃, by simp, by rw [hk]⟩
  cases b
  · obtain ⟨k, hk, rfl⟩ := ha
    exact key k (e16n_kStarList_perm k (mem_kQStar.mp hk))
  · obtain ⟨k, hk, rfl⟩ := ha
    exact key k (e16n_kList_perm k (mem_kQ.mp hk))

private theorem e16n_exists_memAt_perm (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∃ x ∈ memAt α h b, x.perm = embedPerm (emb α h) d₁ := by
  obtain ⟨k, hk, hkd⟩ := exists_mem_kQ_perm d₁ (by simp)
  obtain ⟨k', hk', hk'd⟩ := exists_mem_kQStar_perm d₁ (by simp)
  cases b
  · exact ⟨embed (emb α h) k', ⟨k', mem_kQStar.mpr hk', rfl⟩, by rw [embed_perm, hk'd]⟩
  · exact ⟨embed (emb α h) k, ⟨k, mem_kQ.mpr hk, rfl⟩, by rw [embed_perm, hkd]⟩

theorem card_inter_eq_two_of_normalizes {α β : Finset (Fin n)} {hα : α.card = 4}
    {hβ : β.card = 4} {b b' : Bool} {g : AEQ n} (hg : g ∈ memBar β hβ b') (hord : orderOf g = 4)
    (hnorm : ∀ x ∈ memBar α hα b, g * x * g⁻¹ ∈ memBar α hα b)
    (hnc : ∃ x ∈ memBar α hα b, ∃ y ∈ memBar β hβ b', x * y ≠ y * x) (hne : α ≠ β) :
    (α ∩ β).card = 2 := by
  classical
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨d, hd, hσ⟩ : ∃ d ∈ [d₁, d₂, d₃], a.perm = embedPerm (emb β hβ) d := by
    rcases e16n_memAt_perm ha with h1 | h1
    · exfalso
      have hsq : a * a = 1 := by
        refine Wr.ext (funext fun i => ?_) (by rw [mul_perm, h1, mul_one]; rfl)
        show a.vec i + a.vec (a.perm.symm i) = (1 : Wr n).vec i
        rw [h1]
        exact Wr.zmod_two_add_self _
      have h2 : mkQ n a ^ 2 = 1 := by
        rw [pow_two, ← map_mul, hsq, map_one]
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hord] at h3
      norm_num at h3
    · exact h1
  obtain ⟨x, hx, hxperm⟩ := e16n_exists_memAt_perm α hα b
  obtain ⟨y, hy, hyeq⟩ := hnorm _ ⟨x, hx, rfl⟩
  have hyeq' : mkQ n y = mkQ n (a * x * a⁻¹) := by
    rw [hyeq, map_mul, map_mul, map_inv]
  have hyperm : y.perm = a.perm * x.perm * a.perm⁻¹ := by
    have hp : (y⁻¹ * (a * x * a⁻¹)).perm = 1 := by
      rcases mkQ_eq_iff.mp hyeq' with h1 | h1 <;> rw [h1]
      · rfl
      · rfl
    rw [mul_perm, inv_perm, mul_perm, mul_perm, inv_perm] at hp
    exact inv_mul_eq_one.mp hp
  have hσα : ∀ p ∈ α, a.perm p ∈ α := by
    intro p hp
    by_contra hq
    have hq' : a.perm p ∉ Set.range (emb α hα) := by
      rw [range_emb]
      exact_mod_cast hq
    have h1 : y.perm (a.perm p) = a.perm p := (supportedOn_of_mem_memAt hy _ hq').2
    rw [hyperm] at h1
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h1
    have h2 : x.perm p = p := a.perm.injective h1
    have hp' : p ∈ Set.range (emb α hα) := by
      rw [range_emb]
      exact_mod_cast hp
    obtain ⟨i, rfl⟩ := hp'
    rw [hxperm, embedPerm_apply] at h2
    exact e16n_d₁_no_fix i ((emb α hα).injective h2)
  set T : Finset (Fin 4) := Finset.univ.filter (fun i => emb β hβ i ∈ α) with hTdef
  have hTinv : ∀ i ∈ T, d i ∈ T := by
    intro i hi
    have hi' : emb β hβ i ∈ α := (Finset.mem_filter.mp hi).2
    rw [hTdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 := hσα (emb β hβ i) hi'
    rw [hσ, embedPerm_apply] at h1
    exact h1
  have hTcard : T.card = 0 ∨ T.card = 2 ∨ T.card = 4 := by
    have hdec : ∀ S : Finset (Fin 4), ∀ e ∈ [d₁, d₂, d₃], (∀ i ∈ S, e i ∈ S) →
        S.card ≠ 1 ∧ S.card ≠ 3 := by
      decide
    have h := hdec T d hd hTinv
    have hle : T.card ≤ 4 := by simpa using Finset.card_le_univ T
    omega
  have hint : α ∩ β = T.map (emb β hβ) := by
    ext x
    rw [Finset.mem_inter, Finset.mem_map]
    constructor
    · rintro ⟨hxα, hxβ⟩
      have hx : x ∈ Set.range (emb β hβ) := by
        rw [range_emb]
        exact_mod_cast hxβ
      obtain ⟨i, rfl⟩ := hx
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxα⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(Finset.mem_filter.mp hi).2, ?_⟩
      have hm : emb β hβ i ∈ Set.range (emb β hβ) := Set.mem_range_self i
      rw [range_emb] at hm
      exact_mod_cast hm
  rw [hint, Finset.card_map]
  rcases hTcard with h0 | h2 | h4
  · exfalso
    have hT0 : T = ∅ := Finset.card_eq_zero.mp h0
    have hdisj : Disjoint α β := by
      rw [Finset.disjoint_iff_inter_eq_empty, hint, hT0, Finset.map_empty]
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact hxy (comm_memBar_of_disjoint hdisj b b' x hx y hy)
  · exact h2
  · exfalso
    have hTu : T = Finset.univ := Finset.eq_univ_of_card T (by simpa using h4)
    have hsub : β ⊆ α := by
      intro x hxβ
      have hx : x ∈ Set.range (emb β hβ) := by
        rw [range_emb]
        exact_mod_cast hxβ
      obtain ⟨i, rfl⟩ := hx
      have hi : i ∈ T := by
        rw [hTu]
        exact Finset.mem_univ _
      exact (Finset.mem_filter.mp hi).2
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm


theorem card_inter_eq_two_of_normalizes_of_le_seven {α β : Finset (Fin n)} {hα : α.card = 4}
    {hβ : β.card = 4} {b b' : Bool} {g : AEQ n} (hg : g ∈ memBar β hβ b') (hord : orderOf g = 4)
    (hnorm : ∀ x ∈ memBar α hα b, g * x * g⁻¹ ∈ memBar α hα b) (hn7 : n ≤ 7)
    (hne : α ≠ β) : (α ∩ β).card = 2 := by
  classical
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨d, hd, hσ⟩ : ∃ d ∈ [d₁, d₂, d₃], a.perm = embedPerm (emb β hβ) d := by
    rcases e16n_memAt_perm ha with h1 | h1
    · exfalso
      have hsq : a * a = 1 := by
        refine Wr.ext (funext fun i => ?_) (by rw [mul_perm, h1, mul_one]; rfl)
        show a.vec i + a.vec (a.perm.symm i) = (1 : Wr n).vec i
        rw [h1]
        exact Wr.zmod_two_add_self _
      have h2 : mkQ n a ^ 2 = 1 := by
        rw [pow_two, ← map_mul, hsq, map_one]
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hord] at h3
      norm_num at h3
    · exact h1
  obtain ⟨x, hx, hxperm⟩ := e16n_exists_memAt_perm α hα b
  obtain ⟨y, hy, hyeq⟩ := hnorm _ ⟨x, hx, rfl⟩
  have hyeq' : mkQ n y = mkQ n (a * x * a⁻¹) := by
    rw [hyeq, map_mul, map_mul, map_inv]
  have hyperm : y.perm = a.perm * x.perm * a.perm⁻¹ := by
    have hp : (y⁻¹ * (a * x * a⁻¹)).perm = 1 := by
      rcases mkQ_eq_iff.mp hyeq' with h1 | h1 <;> rw [h1]
      · rfl
      · rfl
    rw [mul_perm, inv_perm, mul_perm, mul_perm, inv_perm] at hp
    exact inv_mul_eq_one.mp hp
  have hσα : ∀ p ∈ α, a.perm p ∈ α := by
    intro p hp
    by_contra hq
    have hq' : a.perm p ∉ Set.range (emb α hα) := by
      rw [range_emb]
      exact_mod_cast hq
    have h1 : y.perm (a.perm p) = a.perm p := (supportedOn_of_mem_memAt hy _ hq').2
    rw [hyperm] at h1
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h1
    have h2 : x.perm p = p := a.perm.injective h1
    have hp' : p ∈ Set.range (emb α hα) := by
      rw [range_emb]
      exact_mod_cast hp
    obtain ⟨i, rfl⟩ := hp'
    rw [hxperm, embedPerm_apply] at h2
    exact e16n_d₁_no_fix i ((emb α hα).injective h2)
  set T : Finset (Fin 4) := Finset.univ.filter (fun i => emb β hβ i ∈ α) with hTdef
  have hTinv : ∀ i ∈ T, d i ∈ T := by
    intro i hi
    have hi' : emb β hβ i ∈ α := (Finset.mem_filter.mp hi).2
    rw [hTdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 := hσα (emb β hβ i) hi'
    rw [hσ, embedPerm_apply] at h1
    exact h1
  have hTcard : T.card = 0 ∨ T.card = 2 ∨ T.card = 4 := by
    have hdec : ∀ S : Finset (Fin 4), ∀ e ∈ [d₁, d₂, d₃], (∀ i ∈ S, e i ∈ S) →
        S.card ≠ 1 ∧ S.card ≠ 3 := by
      decide
    have h := hdec T d hd hTinv
    have hle : T.card ≤ 4 := by simpa using Finset.card_le_univ T
    omega
  have hint : α ∩ β = T.map (emb β hβ) := by
    ext x
    rw [Finset.mem_inter, Finset.mem_map]
    constructor
    · rintro ⟨hxα, hxβ⟩
      have hx : x ∈ Set.range (emb β hβ) := by
        rw [range_emb]
        exact_mod_cast hxβ
      obtain ⟨i, rfl⟩ := hx
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxα⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(Finset.mem_filter.mp hi).2, ?_⟩
      have hm : emb β hβ i ∈ Set.range (emb β hβ) := Set.mem_range_self i
      rw [range_emb] at hm
      exact_mod_cast hm
  rw [hint, Finset.card_map]
  rcases hTcard with h0 | h2 | h4
  · exfalso
    have hT0 : T = ∅ := Finset.card_eq_zero.mp h0
    have hdisj : Disjoint α β := by
      rw [Finset.disjoint_iff_inter_eq_empty, hint, hT0, Finset.map_empty]
    have h8 := Finset.card_union_of_disjoint hdisj
    rw [hα, hβ] at h8
    have hle := Finset.card_le_univ (α ∪ β)
    rw [Fintype.card_fin] at hle
    omega
  · exact h2
  · exfalso
    have hTu : T = Finset.univ := Finset.eq_univ_of_card T (by simpa using h4)
    have hsub : β ⊆ α := by
      intro x hxβ
      have hx : x ∈ Set.range (emb β hβ) := by
        rw [range_emb]
        exact_mod_cast hxβ
      obtain ⟨i, rfl⟩ := hx
      have hi : i ∈ T := by
        rw [hTu]
        exact Finset.mem_univ _
      exact (Finset.mem_filter.mp hi).2
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm


end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin hiding centMembers

variable {G : Type} [Group G] [Finite G]

section Vec

variable {Δ P : Set (Subgroup G)} {n : ℕ}

private theorem e16n_zmod2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem e16n_memBar_le (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    AE.memBar α h b ≤ (AE.aeSub n).map (AE.mkQ n) := by
  unfold AE.memBar
  apply Subgroup.map_mono
  unfold AE.memAt
  cases b
  · exact AE.memKStar_le_aeSub _
  · exact AE.memK_le_aeSub _

private theorem e16n_centralizer_eq_one (hn5 : 5 ≤ n) (x : AE.AEQ n)
    (hx : ∀ y ∈ (AE.aeSub n).map (AE.mkQ n), x * y = y * x) : x = 1 := by
  have hev : ∀ f : Fin n → ZMod 2, ∑ i, f i = 0 →
      x * AE.mkQ n (AE.Wr.ofVec f) = AE.mkQ n (AE.Wr.ofVec f) * x := by
    intro f hf
    apply hx
    refine ⟨AE.Wr.ofVec f, AE.mem_aeSub.mpr ⟨?_, ?_⟩, rfl⟩
    · exact hf
    · rw [AE.Wr.ofVec, Equiv.Perm.sign_one]
  obtain ⟨v, hv⟩ := AE.eq_vec_of_comm_vectors hn5 hev
  have hcm : ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      ∀ y ∈ AE.memBar α h b, AE.mkQ n (AE.Wr.ofVec v) * y = y * AE.mkQ n (AE.Wr.ofVec v) := by
    intro α h b y hy
    rw [← hv]
    exact hx y (e16n_memBar_le α h b hy)
  have hconst : ∀ i j : Fin n, v i = v j := by
    intro i j
    obtain ⟨α, hiα, -, hα⟩ := Finset.exists_subsuperset_card_eq (n := 4)
      (Finset.subset_univ ({i, j} : Finset (Fin n)))
      (Finset.card_le_two.trans (by norm_num))
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    have hc := (AE.vec_centralizes_memBar_iff hn5 α hα true v).mp (hcm α hα true)
    exact hc i (hiα (by simp)) j (hiα (by simp))
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  rcases e16n_zmod2 (v i₀) with h0 | h1
  · have hv0 : v = 0 := funext fun i => (hconst i i₀).trans h0
    rw [hv, hv0]
    rfl
  · have hv1 : v = fun _ => 1 := funext fun i => (hconst i i₀).trans h1
    rw [hv, hv1]
    have : AE.Wr.ofVec (fun _ : Fin n => (1 : ZMod 2)) = AE.Wr.allOnes n := rfl
    rw [this]
    exact (QuotientGroup.eq_one_iff _).mpr (AE.mem_piSub.mpr (Or.inr rfl))

private def e16n_ind (S : Finset (Fin n)) : Fin n → ZMod 2 := fun m => if m ∈ S then 1 else 0

private theorem e16n_zBar_eq (α : Finset (Fin n)) (h : α.card = 4) :
    AE.zBar α h = AE.mkQ n (AE.Wr.ofVec (e16n_ind α)) := by
  unfold AE.zBar
  congr 1
  refine AE.Wr.ext ?_ ?_
  · funext m
    show (AE.zOf (AE.emb α h)).vec m = if m ∈ α then 1 else 0
    rw [AE.zOf_vec_apply]
    simp [AE.range_emb]
  · show (AE.zOf (AE.emb α h)).perm = 1
    simp [AE.zOf, AE.embed_perm, AE.zQ, AE.embedPerm_one]

private theorem e16n_ofVec_add (f g : Fin n → ZMod 2) :
    AE.mkQ n (AE.Wr.ofVec (f + g)) = AE.mkQ n (AE.Wr.ofVec f) * AE.mkQ n (AE.Wr.ofVec g) := by
  rw [← map_mul]
  exact congrArg (AE.mkQ n) (AE.Wr.ext (funext fun m => rfl) rfl)

private theorem e16n_eq_vec_of_comm_zBar (hn5 : 5 ≤ n) (x : AE.AEQ n)
    (hx : ∀ (α : Finset (Fin n)) (h : α.card = 4), x * AE.zBar α h = AE.zBar α h * x) :
    ∃ v : Fin n → ZMod 2, x = AE.mkQ n (AE.Wr.ofVec v) := by
  classical
  let C : AddSubmonoid (Fin n → ZMod 2) :=
    { carrier := {f | x * AE.mkQ n (AE.Wr.ofVec f) = AE.mkQ n (AE.Wr.ofVec f) * x}
      add_mem' := fun {f g} hf hg => by
        have hf' : x * AE.mkQ n (AE.Wr.ofVec f) = AE.mkQ n (AE.Wr.ofVec f) * x := hf
        have hg' : x * AE.mkQ n (AE.Wr.ofVec g) = AE.mkQ n (AE.Wr.ofVec g) * x := hg
        show x * AE.mkQ n (AE.Wr.ofVec (f + g)) = AE.mkQ n (AE.Wr.ofVec (f + g)) * x
        rw [e16n_ofVec_add, ← mul_assoc, hf', mul_assoc, hg', ← mul_assoc]
      zero_mem' := by
        show x * AE.mkQ n (AE.Wr.ofVec 0) = AE.mkQ n (AE.Wr.ofVec 0) * x
        rw [show AE.Wr.ofVec (0 : Fin n → ZMod 2) = 1 from rfl, map_one, mul_one, one_mul] }
  have hsmul : ∀ (c : ZMod 2) (f : Fin n → ZMod 2), f ∈ C → c • f ∈ C := by
    intro c f hf
    rcases e16n_zmod2 c with rfl | rfl
    · rw [zero_smul]
      exact C.zero_mem
    · rw [one_smul]
      exact hf
  have hind : ∀ (α : Finset (Fin n)) (h : α.card = 4), e16n_ind α ∈ C := by
    intro α h
    show x * AE.mkQ n (AE.Wr.ofVec (e16n_ind α)) = AE.mkQ n (AE.Wr.ofVec (e16n_ind α)) * x
    rw [← e16n_zBar_eq]
    exact hx α h
  have hpair : ∀ i j : Fin n, i ≠ j →
      (fun m => (if m = i then (1 : ZMod 2) else 0) + (if m = j then 1 else 0)) ∈ C := by
    intro i j hij
    have hle := Finset.le_card_sdiff ({i, j} : Finset (Fin n)) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at hle
    have hc2 : ({i, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    obtain ⟨T, -, hTt, hT⟩ := Finset.exists_subsuperset_card_eq (n := 3)
      (Finset.empty_subset (Finset.univ \ ({i, j} : Finset (Fin n))))
      (by simp) (by omega)
    have hiT : i ∉ T := fun hi => (Finset.mem_sdiff.mp (hTt hi)).2 (by simp)
    have hjT : j ∉ T := fun hj => (Finset.mem_sdiff.mp (hTt hj)).2 (by simp)
    have hα : (insert i T).card = 4 := by rw [Finset.card_insert_of_notMem hiT, hT]
    have hβ : (insert j T).card = 4 := by rw [Finset.card_insert_of_notMem hjT, hT]
    have hsum : e16n_ind (insert i T) + e16n_ind (insert j T) =
        (fun m => (if m = i then (1 : ZMod 2) else 0) + (if m = j then 1 else 0)) := by
      funext m
      by_cases hmi : m = i <;> by_cases hmj : m = j <;> by_cases hmT : m ∈ T <;>
        simp [e16n_ind, Finset.mem_insert, hmi, hmj, hmT, hiT, hjT, hij, Ne.symm hij] <;> decide
    have h := C.add_mem (hind (insert i T) hα) (hind (insert j T) hβ)
    rw [hsum] at h
    exact h
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  have hdec : ∀ f : Fin n → ZMod 2, ∑ i, f i = 0 →
      f = ∑ k ∈ Finset.univ.erase i₀,
        f k • (fun m => (if m = k then (1 : ZMod 2) else 0) + (if m = i₀ then 1 else 0)) := by
    intro f hf
    have hsum : ∑ k ∈ Finset.univ.erase i₀, f k = f i₀ := by
      have h1 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i₀)
      rw [hf] at h1
      have h2 : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
      exact h2 _ _ h1
    funext m
    by_cases hm : m = i₀
    · subst hm
      simp [Finset.sum_apply, Finset.sum_mul, mul_add, Finset.sum_add_distrib, hsum]
    · simp [Finset.sum_apply, mul_add, Finset.sum_add_distrib, mul_ite, hm,
        Finset.sum_ite_eq', Finset.mem_erase]
  have hev : ∀ f : Fin n → ZMod 2, ∑ i, f i = 0 →
      x * AE.mkQ n (AE.Wr.ofVec f) = AE.mkQ n (AE.Wr.ofVec f) * x := by
    intro f hf
    have hfC : f ∈ C := by
      rw [hdec f hf]
      exact C.sum_mem fun k hk => hsmul _ _ (hpair k i₀ (Finset.ne_of_mem_erase hk))
    exact hfC
  obtain ⟨v, hv⟩ := AE.eq_vec_of_comm_vectors hn5 hev
  exact ⟨v, hv⟩

private theorem e16n_exists_noncomm {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) {L : Subgroup G} (hL : L ∈ Δ) :
    ∃ h ∈ L, ∃ w ∈ L, h * w ≠ w * h := by
  obtain ⟨-, P', hP', hnc⟩ := hΩ.omega1 L hL
  have hPL : P' = L := (hP'.2.2 L le_rfl (h2 L hL) hP'.1).symm
  rw [hPL] at hnc
  by_contra hcon
  push Not at hcon
  exact hnc ⟨⟨fun a b => Subtype.ext (hcon a.1 a.2 b.1 b.2)⟩⟩

private theorem e16n_le_of_noncentral {L' N : Subgroup G}
    (hex : ∃ h ∈ L', ∃ w ∈ L', h * w ≠ w * h)
    (hnc : ∀ v ∈ L', (∃ w ∈ L', v * w ≠ w * v) → v ∈ N) : L' ≤ N := by
  obtain ⟨h, hh, w₀, hw₀, hne⟩ := hex
  intro g hg
  by_cases hgc : ∃ w ∈ L', g * w ≠ w * g
  · exact hnc g hg hgc
  · push Not at hgc
    have hgh : ∃ w ∈ L', (g * h) * w ≠ w * (g * h) := by
      refine ⟨w₀, hw₀, fun e => hne ?_⟩
      have key : g * (h * w₀) = g * (w₀ * h) := by
        calc g * (h * w₀) = g * h * w₀ := (mul_assoc _ _ _).symm
          _ = w₀ * (g * h) := e
          _ = w₀ * g * h := (mul_assoc _ _ _).symm
          _ = g * w₀ * h := by rw [← hgc w₀ hw₀]
          _ = g * (w₀ * h) := mul_assoc _ _ _
      exact mul_left_cancel key
    have h1 := hnc (g * h) (L'.mul_mem hg hh) hgh
    have h2 := hnc h hh ⟨w₀, hw₀, hne⟩
    have := N.mul_mem h1 (N.inv_mem h2)
    simpa using this

private theorem e16n_commutes {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) {L L' : Subgroup G} (hL : L ∈ Δ) (hL' : L' ∈ Δ)
    (hne : L ≠ L') (hN : L' ≤ Subgroup.normalizer (L : Set G)) : Commutes L L' := by
  have hL2 := h2 L hL
  have hL'2 := h2 L' hL'
  obtain ⟨S, hS⟩ := (hL'2.to_sup_of_normal_right' hL2 hN).exists_le_sylow
  exact Q3CP.l67Gen G Δ hΩ S L (TC.mem_RSet_of_isPGroup hL hL2) L'
    (TC.mem_RSet_of_isPGroup hL' hL'2) (le_sup_right.trans hS) (le_sup_left.trans hS) hne

private theorem e16n_map_comm {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) {L L' : Subgroup G}
    (hcomm : Commutes L L') {x y : AE.AEQ n}
    (hx : x ∈ (L.subgroupOf (pSpan P)).map I.φ) (hy : y ∈ (L'.subgroupOf (pSpan P)).map I.φ) :
    x * y = y * x := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcomm a.1 (Subgroup.mem_subgroupOf.mp ha) b.1 (Subgroup.mem_subgroupOf.mp hb))

private theorem e16n_decomp {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) {L L' : Subgroup G}
    (hL' : L' ∈ P)
    (he : (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ) :
    ∀ l' ∈ L', ∃ y ∈ L, ∃ c : G, (∀ u ∈ pSpan P, c * u = u * c) ∧ l' = y * c := by
  intro l' hl'
  have hmem : I.φ ⟨l', le_pSpan hL' hl'⟩ ∈ (L.subgroupOf (pSpan P)).map I.φ := by
    rw [he]
    exact I.mem_map hL' hl'
  obtain ⟨y, hy, hyeq⟩ := hmem
  have hc : (y⁻¹ * ⟨l', le_pSpan hL' hl'⟩ : pSpan P) ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyeq, inv_mul_cancel]
  have hcz := I.ker_le hc
  rw [Subgroup.mem_center_iff] at hcz
  refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, (y : G)⁻¹ * l', ?_, ?_⟩
  · intro u hu
    have := congrArg Subtype.val (hcz ⟨u, hu⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk] at this
    exact this.symm
  · rw [mul_inv_cancel_left]

private theorem e16n_eq_of_map_eq {Δ P : Set (Subgroup G)} {n : ℕ} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ) (I : AEIdent P n) {L L' : Subgroup G}
    (hL : L ∈ P) (hL' : L' ∈ P)
    (he : (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ) : L = L' := by
  by_contra hne
  have hdec := e16n_decomp I hL' he
  have hN : L' ≤ Subgroup.normalizer (L : Set G) := by
    intro l' hl'
    obtain ⟨y, hy, c, hc, rfl⟩ := hdec l' hl'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hconj : ∀ x ∈ pSpan P, (y * c) * x * (y * c)⁻¹ = y * x * y⁻¹ := by
      intro x hx
      rw [mul_inv_rev, show y * c * x * (c⁻¹ * y⁻¹) = y * (c * x * c⁻¹) * y⁻¹ by group,
        hc x hx]
      group
    constructor
    · intro hxL
      rw [hconj x (le_pSpan hL hxL)]
      exact L.mul_mem (L.mul_mem hy hxL) (L.inv_mem hy)
    · intro hxL
      have hyc : y * c ∈ pSpan P := le_pSpan hL' hl'
      have hxX : x ∈ pSpan P := by
        have h1 : x = (y * c)⁻¹ * ((y * c) * x * (y * c)⁻¹) * (y * c) := by group
        rw [h1]
        exact (pSpan P).mul_mem ((pSpan P).mul_mem ((pSpan P).inv_mem hyc)
          (le_pSpan hL hxL)) hyc
      rw [hconj x hxX] at hxL
      have h2' : x = y⁻¹ * (y * x * y⁻¹) * y := by group
      rw [h2']
      exact L.mul_mem (L.mul_mem (L.inv_mem hy) hxL) hy
  have hcomm := e16n_commutes hΩ h2 (hPΔ hL) (hPΔ hL') hne hN
  obtain ⟨v, hv, w, hw, hvw⟩ := e16n_exists_noncomm hΩ h2 (hPΔ hL')
  apply hvw
  have hall : ∀ l' ∈ L', v * l' = l' * v := by
    intro l' hl'
    obtain ⟨y, hy, c, hc, rfl⟩ := hdec l' hl'
    have hvy : y * v = v * y := hcomm y hy v hv
    calc v * (y * c) = (v * y) * c := (mul_assoc _ _ _).symm
      _ = (y * v) * c := by rw [hvy]
      _ = y * (v * c) := mul_assoc _ _ _
      _ = y * (c * v) := by rw [hc v (le_pSpan hL' hv)]
      _ = (y * c) * v := (mul_assoc _ _ _).symm
  exact hall w hw

private theorem e16n_involution_map_ne_one {Δ P : Set (Subgroup G)} {n : ℕ} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ) (I : AEIdent P n) (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    {L : Subgroup G} (hL : L ∈ P) {z : G} (hz : IsUniqueInvolution L z) :
    I.φ ⟨z, le_pSpan hL hz.mem⟩ ≠ 1 := by
  intro hker
  obtain ⟨α, hα, b, hLα⟩ := I.label L hL
  have hzX : ∀ w ∈ pSpan P, z * w = w * z := by
    intro w hw
    have hcen : (⟨z, le_pSpan hL hz.mem⟩ : pSpan P) ∈ Subgroup.center (pSpan P) :=
      I.ker_le (MonoidHom.mem_ker.mpr hker)
    rw [Subgroup.mem_center_iff] at hcen
    have := congrArg Subtype.val (hcen ⟨w, hw⟩)
    simp only [Subgroup.coe_mul] at this
    exact this.symm
  have hNL : ∀ L' ∈ P, L' ≠ L → L' ≤ Subgroup.normalizer (L : Set G) := by
    intro L' hL' hne
    apply e16n_le_of_noncentral (e16n_exists_noncomm hΩ h2 (hPΔ hL'))
    intro v hv hvnc
    have hL'nc : ¬ ∀ w ∈ L', v * w = w * v := by
      intro h
      obtain ⟨w, hw, hne'⟩ := hvnc
      exact hne' (h w hw)
    exact hΩ.omega5 L (hPΔ hL) L' (hPΔ hL') (Ne.symm hne) z hz v hv hL'nc
      ((h2 L' (hPΔ hL')).to_le (Subgroup.zpowers_le.mpr hv)) (hzX v (le_pSpan hL' hv)).symm
  obtain ⟨β, hβ, hαβ⟩ : ∃ β : Finset (Fin n), ∃ _ : β.card = 4, β ≠ α := by
    obtain ⟨x, hx⟩ : ∃ x, x ∉ α := by
      by_contra hcon
      push Not at hcon
      have hu : α = Finset.univ := Finset.eq_univ_of_forall hcon
      rw [hu, Finset.card_univ, Fintype.card_fin] at hα
      omega
    obtain ⟨a, ha⟩ : α.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨insert x (α.erase a), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (fun h => hx (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem ha, hα]
    · intro heq
      apply hx
      rw [← heq]
      exact Finset.mem_insert_self _ _
  obtain ⟨L', hL', hL'map⟩ := I.label_surj β hβ true
  have hsq : AE.zBar α hα * AE.zBar α hα = 1 := by
    unfold AE.zBar
    rw [← map_mul]
    have hz0 : AE.zOf (AE.emb α hα) * AE.zOf (AE.emb α hα) = 1 := by
      calc AE.zOf (AE.emb α hα) * AE.zOf (AE.emb α hα)
          = AE.zOf (AE.emb α hα) * (AE.zOf (AE.emb α hα))⁻¹ := by rw [AE.zOf_inv]
        _ = 1 := mul_inv_cancel _
    rw [hz0, map_one]
  have hLL' : L' ≠ L := by
    rintro rfl
    have hz1 : AE.zBar α hα ∈ AE.memBar β hβ true := by
      rw [← hL'map, hLα]
      exact AE.zBar_mem_memBar α hα b
    rcases AE.eq_of_mem_memBar_mul_self hn5 hz1 hsq with h1 | h1
    · exact AE.zBar_ne_one hn5 α hα h1
    · exact hαβ (AE.eq_of_zBar_eq (by omega) h1).symm
  have hcomm := e16n_commutes hΩ h2 (hPΔ hL) (hPΔ hL') (Ne.symm hLL') (hNL L' hL' hLL')
  have hzmem : AE.zBar α hα ∈ (L.subgroupOf (pSpan P)).map I.φ := by
    rw [hLα]
    exact AE.zBar_mem_memBar α hα b
  have hc : ∀ y ∈ AE.memBar β hβ true, AE.zBar α hα * y = y * AE.zBar α hα := by
    intro y hy
    rw [← hL'map] at hy
    exact e16n_map_comm I hcomm hzmem hy
  have hdisj := AE.disjoint_of_zBar_comm (Ne.symm hαβ) hc
  have hcard := Finset.card_le_univ (α ∪ β)
  rw [Finset.card_union_of_disjoint hdisj, hα, hβ, Fintype.card_fin] at hcard
  omega

private theorem e16n_eq_one_of_map_eq_one {Δ P : Set (Subgroup G)} {n : ℕ} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ) (I : AEIdent P n) (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    {L : Subgroup G} (hL : L ∈ P) {g : G} (hg : g ∈ L)
    (hker : I.φ ⟨g, le_pSpan hL hg⟩ = 1) : g = 1 := by
  by_contra hg1
  obtain ⟨z, hz⟩ := (hΩ.omega1 L (hPΔ hL)).1
  have hA : IsPGroup 2 (Subgroup.zpowers g) :=
    (h2 L (hPΔ hL)).to_le (Subgroup.zpowers_le.mpr hg)
  have hne : Subgroup.zpowers g ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hg1
  have h2dvd : 2 ∣ Nat.card (Subgroup.zpowers g) := by
    rcases hA.card_eq_or_dvd with h | h
    · exfalso
      have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
      omega
    · exact h
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers g) 2 h2dvd
  have htG : orderOf (t : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact ht
  have htsq : (t : G) * (t : G) = 1 := by
    have := pow_orderOf_eq_one (t : G)
    rwa [htG, pow_two] at this
  have htne : (t : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htG
    norm_num at htG
  have htL : (t : G) ∈ L := Subgroup.zpowers_le.mpr hg t.2
  have htker : I.φ ⟨(t : G), le_pSpan hL htL⟩ = 1 := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp t.2
    have hXeq : (⟨(t : G), le_pSpan hL htL⟩ : pSpan P) =
        (⟨g, le_pSpan hL hg⟩ : pSpan P) ^ m :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
    rw [hXeq, map_zpow, hker, one_zpow]
  have htz : (t : G) = z := (hz.unique (t : G) htL htsq).resolve_left htne
  have hXeq : (⟨z, le_pSpan hL hz.mem⟩ : pSpan P) = ⟨(t : G), le_pSpan hL htL⟩ :=
    Subtype.ext htz.symm
  exact e16n_involution_map_ne_one hΩ h2 hPΔ I hn5 hn7 hL hz (by rw [hXeq, htker])

private theorem e16n_conj_mem {P : Set (Subgroup G)} {a : G} (hperm : ∀ L ∈ P, conjSub a L ∈ P) :
    ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P := by
  intro y hy
  have hle : pSpan P ≤ (pSpan P).comap (MulAut.conj a).toMonoidHom := by
    apply pSpan_le
    intro L hL w hw
    exact le_pSpan (hperm L hL) (conj_mem_conjSub hw)
  exact hle hy

private theorem e16n_center_le_ker {P : Set (Subgroup G)} {n : ℕ} (hn5 : 5 ≤ n) (I : AEIdent P n) :
    Subgroup.center (pSpan P) ≤ I.φ.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  refine e16n_centralizer_eq_one hn5 (I.φ z) fun m hm => ?_
  rw [← I.range_eq] at hm
  obtain ⟨y, rfl⟩ := hm
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y).symm]

private def e16n_conjEquiv {P : Set (Subgroup G)} {a : G}
    (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P)
    (ha' : ∀ y ∈ pSpan P, a⁻¹ * y * a⁻¹⁻¹ ∈ pSpan P) : pSpan P ≃* pSpan P where
  toFun y := ⟨a * y * a⁻¹, ha y y.2⟩
  invFun y := ⟨a⁻¹ * y * a⁻¹⁻¹, ha' y y.2⟩
  left_inv y := by
    ext
    simp [mul_assoc]
  right_inv y := by
    ext
    simp [mul_assoc]
  map_mul' y z := by
    ext
    simp [mul_assoc]

private theorem e16n_map_conjEquiv {P : Set (Subgroup G)} {a : G}
    (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P) (ha' : ∀ y ∈ pSpan P, a⁻¹ * y * a⁻¹⁻¹ ∈ pSpan P)
    (L : Subgroup G) :
    (L.subgroupOf (pSpan P)).map (e16n_conjEquiv ha ha').toMonoidHom =
      (conjSub a L).subgroupOf (pSpan P) := by
  ext w
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy
    rw [mem_conjSub_iff]
    have e : a⁻¹ * ((e16n_conjEquiv ha ha').toMonoidHom y : G) * a = y := by
      show a⁻¹ * (a * (y : G) * a⁻¹) * a = y
      group
    rw [e]
    exact hy
  · intro hw
    rw [mem_conjSub_iff] at hw
    have hw' : a⁻¹ * (w : G) * a⁻¹⁻¹ ∈ L := by
      rw [inv_inv]
      exact hw
    refine ⟨⟨a⁻¹ * (w : G) * a⁻¹⁻¹, ha' w w.2⟩, Subgroup.mem_subgroupOf.mpr hw', ?_⟩
    apply Subtype.ext
    show a * (a⁻¹ * (w : G) * a⁻¹⁻¹) * a⁻¹ = w
    group

private theorem e16n_exists_conj {P : Set (Subgroup G)} {n : ℕ}
    (hn5 : 5 ≤ n) (hn7 : n ≤ 7) (I : AEIdent P n) {a : G}
    (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P) (ha' : ∀ y ∈ pSpan P, a⁻¹ * y * a⁻¹⁻¹ ∈ pSpan P)
    (hperm : ∀ L ∈ P, conjSub a L ∈ P) :
    ∃ x : AE.AEQ n, ∀ (y : G) (hy : y ∈ pSpan P) (hy' : a * y * a⁻¹ ∈ pSpan P),
      I.φ ⟨a * y * a⁻¹, hy'⟩ = x * I.φ ⟨y, hy⟩ * x⁻¹ := by
  set c := e16n_conjEquiv ha ha' with hc_def
  have hZ := e16n_center_le_ker hn5 I
  obtain ⟨f, hf⟩ : ∃ f : ↥(pSpan P) →* ↥((AE.aeSub n).map (AE.mkQ n)),
      ∀ y, (f y : AE.AEQ n) = I.φ y :=
    ⟨I.φ.codRestrict _ fun y => by rw [← I.range_eq]; exact ⟨y, rfl⟩, fun _ => rfl⟩
  have hfs : Function.Surjective f := by
    rintro ⟨m, hm⟩
    rw [← I.range_eq] at hm
    obtain ⟨y, rfl⟩ := hm
    exact ⟨y, Subtype.ext (hf y)⟩
  have hfk : f.ker = Subgroup.center ↥(pSpan P) := by
    refine le_antisymm (fun y hy => I.ker_le ?_) fun y hy => ?_
    · rw [MonoidHom.mem_ker, ← hf, MonoidHom.mem_ker.mp hy]
      rfl
    · exact MonoidHom.mem_ker.mpr (Subtype.ext ((hf y).trans (MonoidHom.mem_ker.mp (hZ hy))))
  have hck : f.ker.map c.toMonoidHom = f.ker := by
    rw [hfk]
    exact Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (Subgroup.center ↥(pSpan P)).Characteristic) c
  obtain ⟨β, hβ⟩ : ∃ β : MulAut ↥((AE.aeSub n).map (AE.mkQ n)), ∀ y, β (f y) = f (c y) := by
    refine ⟨((QuotientGroup.quotientKerEquivOfSurjective f hfs).symm.trans
      (QuotientGroup.congr f.ker f.ker c hck)).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hfs), fun y => ?_⟩
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hfs).symm (f y) =
        (y : ↥(pSpan P) ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
    rfl
  have hsub : ∀ H : Subgroup ↥(pSpan P),
      (H.map I.φ).subgroupOf ((AE.aeSub n).map (AE.mkQ n)) = H.map f := by
    intro H
    ext m
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hym⟩
      exact ⟨y, hy, Subtype.ext ((hf y).trans hym)⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (hf y).symm⟩
  have hcomp : β.toMonoidHom.comp f = f.comp c.toMonoidHom := MonoidHom.ext hβ
  obtain ⟨x, hx⟩ := TL4.model117_proved n hn5 hn7 β fun α hα b => by
    obtain ⟨L, hL, hLe⟩ := I.label_surj α hα b
    obtain ⟨α', hα', b', hL'e⟩ := I.label (conjSub a L) (hperm L hL)
    refine ⟨α', hα', b', ?_⟩
    rw [← hLe, ← hL'e, hsub, hsub, Subgroup.map_map, hcomp, ← Subgroup.map_map,
      e16n_map_conjEquiv ha ha']
  refine ⟨x, fun y hy hy' => ?_⟩
  have h1 : I.φ ⟨a * y * a⁻¹, hy'⟩ = (f (c ⟨y, hy⟩) : AE.AEQ n) := (hf _).symm
  rw [h1, ← hβ, hx, hf]

private def e16n_IsConj {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (a : G) (x : AE.AEQ n) :
    Prop :=
  ∀ (y : G) (hy : y ∈ pSpan P) (hy' : a * y * a⁻¹ ∈ pSpan P),
    I.φ ⟨a * y * a⁻¹, hy'⟩ = x * I.φ ⟨y, hy⟩ * x⁻¹

private theorem e16n_eq_of_isConj {P : Set (Subgroup G)} {n : ℕ} (hn5 : 5 ≤ n) (I : AEIdent P n)
    {a : G} (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P) {x x' : AE.AEQ n}
    (h : e16n_IsConj I a x) (h' : e16n_IsConj I a x') : x = x' := by
  have hc : x'⁻¹ * x = 1 := by
    apply e16n_centralizer_eq_one hn5
    intro g hg
    have hg' : g ∈ I.φ.range := by
      rw [I.range_eq]
      exact hg
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hg'
    have h1 : I.φ ⟨a * w * a⁻¹, ha _ w.2⟩ = x * I.φ w * x⁻¹ := h w.1 w.2 (ha _ w.2)
    have h2 : I.φ ⟨a * w * a⁻¹, ha _ w.2⟩ = x' * I.φ w * x'⁻¹ := h' w.1 w.2 (ha _ w.2)
    have e : x * I.φ w * x⁻¹ = x' * I.φ w * x'⁻¹ := h1.symm.trans h2
    calc x'⁻¹ * x * I.φ w = x'⁻¹ * (x * I.φ w * x⁻¹) * x := by group
      _ = x'⁻¹ * (x' * I.φ w * x'⁻¹) * x := by rw [e]
      _ = I.φ w * (x'⁻¹ * x) := by group
  exact (inv_mul_eq_one.mp hc).symm

private theorem e16n_one_isConj {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) :
    e16n_IsConj I 1 (1 : AE.AEQ n) := by
  intro y hy hy'
  have e : (⟨1 * y * 1⁻¹, hy'⟩ : pSpan P) = ⟨y, hy⟩ := Subtype.ext (by simp)
  rw [e]
  simp

private theorem e16n_mul_isConj {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) {a b : G}
    (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P) (hb : ∀ y ∈ pSpan P, b * y * b⁻¹ ∈ pSpan P)
    {x x' : AE.AEQ n} (h : e16n_IsConj I a x) (h' : e16n_IsConj I b x') :
    e16n_IsConj I (a * b) (x * x') := by
  intro y hy hy'
  have e : (⟨a * b * y * (a * b)⁻¹, hy'⟩ : pSpan P) =
      ⟨a * (b * y * b⁻¹) * a⁻¹, ha _ (hb y hy)⟩ := Subtype.ext (by group)
  rw [e, h (b * y * b⁻¹) (hb y hy) (ha _ (hb y hy)), h' y hy (hb y hy)]
  group

private theorem e16n_isConj_one_of_centralizes {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n)
    {a : G} (hc : ∀ y ∈ pSpan P, a * y = y * a) : e16n_IsConj I a 1 := by
  intro y hy hy'
  have e : (⟨a * y * a⁻¹, hy'⟩ : pSpan P) = ⟨y, hy⟩ := Subtype.ext (by
    show a * y * a⁻¹ = y
    rw [hc y hy]
    group)
  rw [e]
  simp

private theorem e16n_sum_eq_zero_of_const {n : ℕ} (α : Finset (Fin n)) (hα : α.card = 4)
    (v : Fin n → ZMod 2) (hv : ∀ i ∈ α, ∀ j ∈ α, v i = v j) : ∑ i ∈ α, v i = 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ : α.Nonempty := Finset.card_pos.mp (by omega)
  have h1 : ∑ i ∈ α, v i = ∑ _i ∈ α, v i₀ := Finset.sum_congr rfl fun i hi => hv i hi i₀ hi₀
  rw [h1, Finset.sum_const, hα]
  have h4 : ∀ c : ZMod 2, (4 : ℕ) • c = 0 := by decide
  exact h4 _

private theorem e16n_normalizes_of_conjSub_eq {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n)
    {a : G} {x : AE.AEQ n} (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P)
    (h : e16n_IsConj I a x) {L : Subgroup G} (hL : conjSub a L = L) {α : Finset (Fin n)}
    {hα : α.card = 4} {b : Bool} (hLα : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b) :
    ∀ g ∈ AE.memBar α hα b, x * g * x⁻¹ ∈ AE.memBar α hα b := by
  rintro g hg
  rw [← hLα] at hg ⊢
  obtain ⟨u, hu, rfl⟩ := hg
  rw [← h u.1 u.2 (ha _ u.2)]
  have hmem : a * u.1 * a⁻¹ ∈ L := by
    have h1 : a * u.1 * a⁻¹ ∈ conjSub a L := conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hu)
    rw [hL] at h1
    exact h1
  exact ⟨⟨a * u.1 * a⁻¹, ha _ u.2⟩, Subgroup.mem_subgroupOf.mpr hmem, rfl⟩

private theorem e16n_commute_of_centralizes {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n)
    {a : G} {x : AE.AEQ n} (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P)
    (h : e16n_IsConj I a x) {L : Subgroup G} (hL : L ∈ P) {α : Finset (Fin n)}
    {hα : α.card = 4} {b : Bool} (hLα : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b)
    (hc : ∀ l ∈ L, a * l = l * a) : ∀ g ∈ AE.memBar α hα b, x * g = g * x := by
  rintro g hg
  rw [← hLα] at hg
  obtain ⟨u, hu, rfl⟩ := hg
  have e : a * u.1 * a⁻¹ = u.1 := by
    rw [hc u.1 (Subgroup.mem_subgroupOf.mp hu)]
    group
  have hh := h u.1 u.2 (ha _ u.2)
  have hu' : (⟨a * u.1 * a⁻¹, ha _ u.2⟩ : pSpan P) = u := Subtype.ext e
  rw [hu'] at hh
  calc x * I.φ u = (x * I.φ u * x⁻¹) * x := by group
    _ = I.φ u * x := by rw [← hh]

private theorem e16n_conjSub_eq_of_normalizes {Δ P : Set (Subgroup G)} {n : ℕ} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ) (I : AEIdent P n) {a : G} {x : AE.AEQ n}
    (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P)
    (ha' : ∀ y ∈ pSpan P, a⁻¹ * y * a⁻¹⁻¹ ∈ pSpan P)
    (hperm : ∀ L ∈ P, conjSub a L ∈ P) (h : e16n_IsConj I a x) (hxx : x * x = 1)
    {L : Subgroup G} (hL : L ∈ P) {α : Finset (Fin n)} {hα : α.card = 4} {b : Bool}
    (hLα : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b)
    (hnorm : ∀ g ∈ AE.memBar α hα b, x * g * x⁻¹ ∈ AE.memBar α hα b) : conjSub a L = L := by
  have hx_inv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hh : ∀ (y : G) (hy : y ∈ pSpan P) (hy' : a * y * a⁻¹ ∈ pSpan P),
      I.φ ⟨a * y * a⁻¹, hy'⟩ = x * I.φ ⟨y, hy⟩ * x⁻¹ := h
  have hmap : ((conjSub a L).subgroupOf (pSpan P)).map I.φ =
      (L.subgroupOf (pSpan P)).map I.φ := by
    apply le_antisymm
    · intro g hg
      obtain ⟨w, hw, rfl⟩ := hg
      have hw' : (w : G) ∈ conjSub a L := Subgroup.mem_subgroupOf.mp hw
      rw [mem_conjSub_iff] at hw'
      have hu : a⁻¹ * (w : G) * a⁻¹⁻¹ ∈ pSpan P := ha' _ w.2
      have key := hh (a⁻¹ * (w : G) * a⁻¹⁻¹) hu (ha _ hu)
      have hwe : (⟨a * (a⁻¹ * (w : G) * a⁻¹⁻¹) * a⁻¹, ha _ hu⟩ : pSpan P) = w :=
        Subtype.ext (by group)
      rw [hwe] at key
      have hum : (⟨a⁻¹ * (w : G) * a⁻¹⁻¹, hu⟩ : pSpan P) ∈ L.subgroupOf (pSpan P) := by
        rw [Subgroup.mem_subgroupOf]
        show a⁻¹ * (w : G) * a⁻¹⁻¹ ∈ L
        rw [inv_inv]
        exact hw'
      have hmemb : I.φ ⟨a⁻¹ * (w : G) * a⁻¹⁻¹, hu⟩ ∈ AE.memBar α hα b := by
        rw [← hLα]
        exact ⟨_, hum, rfl⟩
      rw [hLα, key]
      exact hnorm _ hmemb
    · intro g hg
      obtain ⟨u, hu, rfl⟩ := hg
      have hg' : x⁻¹ * I.φ u * x ∈ AE.memBar α hα b := by
        have h1 := hnorm _ (by rw [← hLα]; exact ⟨u, hu, rfl⟩)
        rw [hx_inv] at h1 ⊢
        exact h1
      rw [← hLα] at hg'
      obtain ⟨u', hu', hu'e⟩ := hg'
      have hw : a * u'.1 * a⁻¹ ∈ conjSub a L := by
        rw [mem_conjSub_iff]
        have e : a⁻¹ * (a * u'.1 * a⁻¹) * a = u'.1 := by group
        rw [e]
        exact Subgroup.mem_subgroupOf.mp hu'
      refine ⟨⟨a * u'.1 * a⁻¹, ha _ u'.2⟩, Subgroup.mem_subgroupOf.mpr hw, ?_⟩
      have e2 : I.φ ⟨u'.1, u'.2⟩ = I.φ u' := rfl
      rw [hh u'.1 u'.2 (ha _ u'.2), e2, hu'e]
      group
  exact e16n_eq_of_map_eq hΩ h2 hPΔ I (hperm L hL) hL hmap

private theorem e16n_centralizes_of_commute {Δ P : Set (Subgroup G)} {n : ℕ} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ) (I : AEIdent P n) (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    {a : G} {x : AE.AEQ n} (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P)
    (h : e16n_IsConj I a x) {L : Subgroup G} (hL : L ∈ P) (hLc : conjSub a L = L)
    {α : Finset (Fin n)} {hα : α.card = 4} {b : Bool}
    (hLα : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b)
    (hcomm : ∀ g ∈ AE.memBar α hα b, x * g = g * x) : ∀ l ∈ L, a * l = l * a := by
  intro l hl
  have hh : ∀ (y : G) (hy : y ∈ pSpan P) (hy' : a * y * a⁻¹ ∈ pSpan P),
      I.φ ⟨a * y * a⁻¹, hy'⟩ = x * I.φ ⟨y, hy⟩ * x⁻¹ := h
  have hlX : l ∈ pSpan P := le_pSpan hL hl
  have hmem : I.φ ⟨l, hlX⟩ ∈ AE.memBar α hα b := by
    rw [← hLα]
    exact ⟨⟨l, hlX⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hcomm' : x * I.φ ⟨l, hlX⟩ = I.φ ⟨l, hlX⟩ * x := hcomm _ hmem
  have hfix : I.φ ⟨a * l * a⁻¹, ha l hlX⟩ = I.φ ⟨l, hlX⟩ := by
    rw [hh l hlX (ha l hlX), hcomm', mul_assoc, mul_inv_cancel, mul_one]
  have hal : a * l * a⁻¹ ∈ L := hLc ▸ conj_mem_conjSub hl
  have hgL : (a * l * a⁻¹) * l⁻¹ ∈ L := L.mul_mem hal (L.inv_mem hl)
  have hker : I.φ ⟨(a * l * a⁻¹) * l⁻¹, le_pSpan hL hgL⟩ = 1 := by
    have e : (⟨(a * l * a⁻¹) * l⁻¹, le_pSpan hL hgL⟩ : pSpan P) =
        ⟨a * l * a⁻¹, ha l hlX⟩ * (⟨l, hlX⟩ : pSpan P)⁻¹ := Subtype.ext (by simp)
    rw [e, map_mul, map_inv, hfix, mul_inv_cancel]
  have hg1 := e16n_eq_one_of_map_eq_one hΩ h2 hPΔ I hn5 hn7 hL hgL hker
  rw [mul_inv_eq_one] at hg1
  calc a * l = a * l * a⁻¹ * a := by group
    _ = l * a := by rw [hg1]

private theorem e16n_centralizes_pSpan {Δ P : Set (Subgroup G)} {n : ℕ} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ) (I : AEIdent P n) (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    {a : G} (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P)
    (ha' : ∀ y ∈ pSpan P, a⁻¹ * y * a⁻¹⁻¹ ∈ pSpan P)
    (hperm : ∀ L ∈ P, conjSub a L ∈ P) (h : e16n_IsConj I a 1) :
    ∀ y ∈ pSpan P, a * y = y * a := by
  have hc : ∀ L ∈ P, ∀ l ∈ L, a * l = l * a := by
    intro L hL
    obtain ⟨α, hα, b, hLα⟩ := I.label L hL
    have hLc := e16n_conjSub_eq_of_normalizes hΩ h2 hPΔ I ha ha' hperm h (by simp) hL hLα
      (by intro g hg; simpa using hg)
    exact e16n_centralizes_of_commute hΩ h2 hPΔ I hn5 hn7 ha h hL hLc hLα
      (by intro g _; simp)
  have hcen : pSpan P ≤ Subgroup.centralizer ({a} : Set G) := by
    apply pSpan_le
    intro L hL l hl
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hc L hL l hl
  intro y hy
  have := Subgroup.mem_centralizer_iff.mp (hcen hy) a (Set.mem_singleton a)
  exact this

private theorem e16n_vec_sq {n : ℕ} (v : Fin n → ZMod 2) :
    AE.mkQ n (AE.Wr.ofVec v) * AE.mkQ n (AE.Wr.ofVec v) = 1 := by
  rw [← e16n_ofVec_add]
  have hvv : ∀ c : ZMod 2, c + c = 0 := by decide
  have hv : v + v = 0 := funext fun i => hvv (v i)
  rw [hv, show AE.Wr.ofVec (0 : Fin n → ZMod 2) = 1 from rfl, map_one]

theorem exists_vecHom_of_aeIdent (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) (A : Subgroup G)
    (hA : ∀ d ∈ A, (∀ L ∈ P, conjSub d L ∈ P) ∧
      ∀ L ∈ P, ∀ r : G, IsUniqueInvolution L r → d * r = r * d) :
    ∃ f : A →* AE.AEQ n,
      (∀ a : A, ∃ v : Fin n → ZMod 2, f a = AE.mkQ n (AE.Wr.ofVec v) ∧
        ∀ L ∈ P, ∀ (α : Finset (Fin n)) (hα : α.card = 4) (b : Bool),
          (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b →
            (conjSub (a : G) L = L ↔ ∑ i ∈ α, v i = 0) ∧
              ((∀ l ∈ L, (a : G) * l = l * a) ↔ ∀ i ∈ α, ∀ j ∈ α, v i = v j)) ∧
      ∀ a : A, f a = 1 ↔ ∀ x ∈ pSpan P, (a : G) * x = x * a := by
  classical
  have hperm : ∀ a : A, ∀ L ∈ P, conjSub (a : G) L ∈ P := fun a => (hA a a.2).1
  have hcen : ∀ a : A, ∀ L ∈ P, ∀ r : G, IsUniqueInvolution L r → (a : G) * r = r * a :=
    fun a => (hA a a.2).2
  have hX : ∀ a : A, ∀ y ∈ pSpan P, (a : G) * y * (a : G)⁻¹ ∈ pSpan P :=
    fun a => e16n_conj_mem (hperm a)
  have hX' : ∀ a : A, ∀ y ∈ pSpan P, (a : G)⁻¹ * y * (a : G)⁻¹⁻¹ ∈ pSpan P := by
    intro a
    have hinvA : (a : G)⁻¹ ∈ A := A.inv_mem a.2
    exact e16n_conj_mem (fun L hL => (hA _ hinvA).1 L hL)
  have hex : ∀ a : A, ∃ x : AE.AEQ n, e16n_IsConj I (a : G) x := fun a =>
    e16n_exists_conj hn5 hn7 I (hX a) (hX' a) (hperm a)
  choose xa hxa using hex
  have hone : xa 1 = 1 := by
    have h1 := hxa 1
    have h1' : e16n_IsConj I ((1 : A) : G) 1 := e16n_one_isConj I
    exact e16n_eq_of_isConj hn5 I (hX 1) h1 h1'
  have hmul : ∀ a b : A, xa (a * b) = xa a * xa b := by
    intro a b
    refine e16n_eq_of_isConj hn5 I (hX (a * b)) (hxa (a * b)) ?_
    exact e16n_mul_isConj I (hX a) (hX b) (hxa a) (hxa b)
  let f : A →* AE.AEQ n :=
    { toFun := xa
      map_one' := hone
      map_mul' := hmul }
  refine ⟨f, ?_, ?_⟩
  · intro a
    have hx := hxa a
    have hzb : ∀ (α : Finset (Fin n)) (hα : α.card = 4),
        xa a * AE.zBar α hα = AE.zBar α hα * xa a := by
      intro α hα
      obtain ⟨L, hL, hLα⟩ := I.label_surj α hα true
      obtain ⟨z, hz⟩ := (hΩ.omega1 L (hPΔ hL)).1
      have hzmem : I.φ ⟨z, le_pSpan hL hz.mem⟩ ∈ AE.memBar α hα true := by
        rw [← hLα]
        exact ⟨_, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
      have hsq : I.φ ⟨z, le_pSpan hL hz.mem⟩ * I.φ ⟨z, le_pSpan hL hz.mem⟩ = 1 := by
        rw [← map_mul]
        have e : (⟨z, le_pSpan hL hz.mem⟩ * ⟨z, le_pSpan hL hz.mem⟩ : pSpan P) = 1 :=
          Subtype.ext (by simp [hz.sq])
        rw [e, map_one]
      have hφz : I.φ ⟨z, le_pSpan hL hz.mem⟩ = AE.zBar α hα := by
        rcases AE.eq_of_mem_memBar_mul_self hn5 hzmem hsq with h1 | h1
        · exact absurd h1 (e16n_involution_map_ne_one hΩ h2 hPΔ I hn5 hn7 hL hz)
        · exact h1
      have hfix := hx z (le_pSpan hL hz.mem) (hX a z (le_pSpan hL hz.mem))
      have hzeq : (⟨(a : G) * z * (a : G)⁻¹, hX a z (le_pSpan hL hz.mem)⟩ : pSpan P) =
          ⟨z, le_pSpan hL hz.mem⟩ := by
        apply Subtype.ext
        show (a : G) * z * (a : G)⁻¹ = z
        rw [hcen a L hL z hz]
        group
      rw [hzeq, hφz] at hfix
      calc xa a * AE.zBar α hα = (xa a * AE.zBar α hα * (xa a)⁻¹) * xa a := by group
        _ = AE.zBar α hα * xa a := by rw [← hfix]
    obtain ⟨v, hv⟩ := e16n_eq_vec_of_comm_zBar hn5 (xa a) hzb
    have hxx : xa a * xa a = 1 := by
      rw [hv]
      exact e16n_vec_sq v
    have hnorm_iff := AE.vec_normalizes_memBar_iff hn5
    have hcent_iff := AE.vec_centralizes_memBar_iff hn5
    refine ⟨v, hv, ?_⟩
    intro L hL α hα b hLα
    have hLc_of_sum : ∑ i ∈ α, v i = 0 → conjSub (a : G) L = L := by
      intro hsum
      apply e16n_conjSub_eq_of_normalizes hΩ h2 hPΔ I (hX a) (hX' a) (hperm a) hx hxx hL hLα
      rw [hv]
      exact (hnorm_iff α hα b v).mpr hsum
    refine ⟨⟨fun hconj => ?_, hLc_of_sum⟩, ⟨fun hcen' => ?_, fun hconst => ?_⟩⟩
    · apply (hnorm_iff α hα b v).mp
      rw [← hv]
      exact e16n_normalizes_of_conjSub_eq I (hX a) hx hconj hLα
    · apply hcent_iff α hα b v |>.mp
      rw [← hv]
      exact e16n_commute_of_centralizes I (hX a) hx hL hLα hcen'
    · have hsum := e16n_sum_eq_zero_of_const α hα v hconst
      refine e16n_centralizes_of_commute hΩ h2 hPΔ I hn5 hn7 (hX a) hx hL
        (hLc_of_sum hsum) hLα ?_
      rw [hv]
      exact (hcent_iff α hα b v).mpr hconst
  · intro a
    constructor
    · intro hfa
      have hx1 : e16n_IsConj I (a : G) 1 := by
        have e : xa a = 1 := hfa
        have hx := hxa a
        rw [e] at hx
        exact hx
      exact e16n_centralizes_pSpan hΩ h2 hPΔ I hn5 hn7 (hX a) (hX' a) (hperm a) hx1
    · intro hc
      have h1 : e16n_IsConj I (a : G) 1 := e16n_isConj_one_of_centralizes I hc
      exact e16n_eq_of_isConj hn5 I (hX a) (hxa a) h1

end Vec

private theorem e16n_zBar_sq {n : ℕ} {α : Finset (Fin n)} (h h' : α.card = 4) :
    AE.zBar α h * AE.zBar α h' = 1 := by
  obtain rfl : h = h' := Subsingleton.elim _ _
  have hz0 : AE.zOf (AE.emb α h) * AE.zOf (AE.emb α h) = 1 := by
    calc AE.zOf (AE.emb α h) * AE.zOf (AE.emb α h)
        = AE.zOf (AE.emb α h) * (AE.zOf (AE.emb α h))⁻¹ := by rw [AE.zOf_inv]
      _ = 1 := mul_inv_cancel _
  unfold AE.zBar
  rw [← map_mul, hz0, map_one]

private theorem e16n_mem_normalizer_of_centralizes {L : Subgroup G} {g : G}
    (hg : ∀ k ∈ L, g * k = k * g) : g ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have e : g * k * g⁻¹ = k := by rw [hg k hk, mul_inv_cancel_right]
    rw [e]
    exact hk
  · intro hm
    have hgm : g * (g * k * g⁻¹) = (g * k * g⁻¹) * g := hg _ hm
    have e : k = g * k * g⁻¹ := by
      have h1 : g⁻¹ * ((g * k * g⁻¹) * g) = g⁻¹ * (g * (g * k * g⁻¹)) := by rw [hgm]
      calc k = g⁻¹ * ((g * k * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * k * g⁻¹)) := h1
        _ = g * k * g⁻¹ := by group
    exact e ▸ hm

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

theorem eq_of_dSet_subset_centMembers
    {K₂ K₂' W₂ : Subgroup G} {z₂ u₂ e₂ g₂ : G}
    (c : Sit16 Ω K K' W z u e g) (c₂ : Sit16 Ω K₂ K₂' W₂ z₂ u₂ e₂ g₂) (h : EndHyp Ω)
    (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    (hD : DSet Ω W₂ ⊆ centMembers Ω e) : e₂ = e := by
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have h2 : ∀ L ∈ Ω, IsPGroup 2 L := h.thmD.two
  have hPΔ : centMembers Ω e ⊆ Ω := fun L hL => hL.1
  have hn5 : (5 : ℕ) ≤ 6 := by norm_num
  have hn7 : (6 : ℕ) ≤ 7 := by norm_num
  have hK₂Ω : K₂ ∈ Ω := c₂.twin.mem
  have hz₂ : IsUniqueInvolution K₂ z₂ := c₂.twin.isInv
  have hKD₂ : K₂ ∈ DSet Ω W₂ := h.mem_dSet_of_mem c₂.data.hW hK₂Ω hz₂ c₂.data.hzW
  have hJ₂u : IsUniqueInvolution (conjSub g₂ K₂) (u₂ * e₂) := by
    have := c₂.twin.isInv.conj g₂
    rwa [c₂.data.hgt] at this
  have hJ₂Ω : conjSub g₂ K₂ ∈ Ω := h.thmD.hyp.conjInvariant g₂ K₂ hK₂Ω
  have he₂W : e₂ ∈ W₂ := by
    have hmem : e₂ ∈ Subgroup.closure ({e₂} : Set G) := Subgroup.subset_closure rfl
    rw [c₂.data.he] at hmem
    exact (Subgroup.mem_inf.mp hmem).1
  have ht₂W : u₂ * e₂ ∈ W₂ := W₂.mul_mem c₂.data.huW he₂W
  have hJ₂D : conjSub g₂ K₂ ∈ DSet Ω W₂ := h.mem_dSet_of_mem c₂.data.hW hJ₂Ω hJ₂u ht₂W
  have hK'mem : K₂' ∈ twinSet Ω K₂ := by
    rw [c₂.twin.twin]
    simp
  obtain ⟨hK'Ω, z', hz'K, hz'K'⟩ := hK'mem
  have hz'eq : z' = z₂ := hz'K.eq hz₂
  have hK'D : K₂' ∈ DSet Ω W₂ :=
    h.mem_dSet_of_mem c₂.data.hW hK'Ω (hz'eq ▸ hz'K') c₂.data.hzW
  have hMle : ∀ R ∈ DSet Ω W₂, R ≤ MGrp Ω W₂ := fun R hR =>
    le_iSup₂ (f := fun (R : Subgroup G) (_ : R ∈ DSet Ω W₂) => R) R hR
  have hu₂M : u₂ ∈ MGrp Ω W₂ :=
    (sup_le (hMle K₂ hKD₂) (hMle K₂' hK'D)) c₂.data.hu
  have ht₂M : u₂ * e₂ ∈ MGrp Ω W₂ := hMle _ hJ₂D hJ₂u.mem
  have he₂M : e₂ ∈ MGrp Ω W₂ := by
    have e : e₂ = u₂⁻¹ * (u₂ * e₂) := by group
    rw [e]
    exact (MGrp Ω W₂).mul_mem ((MGrp Ω W₂).inv_mem hu₂M) ht₂M
  have hMX : MGrp Ω W₂ ≤ pSpan (centMembers Ω e) := iSup₂_le fun R hR => le_pSpan (hD hR)
  have he₂X : e₂ ∈ pSpan (centMembers Ω e) := hMX he₂M
  have h13₂ : zGroup Ω ≠ eGroup Ω K₂ := by
    obtain ⟨n, hn⟩ := h.thmD.trans K c.twin.mem K₂ hK₂Ω
    rw [← hn]
    exact h.zGroup_ne_eGroup_conj c.twin.mem h13 n
  have he₂Λ : e₂ ∈ lambdaW Ω W₂ := e_mem_lambdaW c₂ h h9 h13₂
  have he₂Z : e₂ ∈ zGroup Ω := (Subgroup.mem_inf.mp he₂Λ).1
  have hcentM : ∀ k ∈ MGrp Ω W₂, k * e₂ = e₂ * k := fun k hk =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp he₂Λ).2 k hk
  obtain ⟨I, ψ, -, hψI, -, ⟨hei, heψ⟩, hzψ⟩ := exists_equiv_X c h h9 h13
  have hperm1 : (ψ ⟨e₂, he₂X⟩ : AE.Wr 6).perm = 1 := (hzψ ⟨e₂, he₂X⟩).mp he₂Z
  obtain ⟨v, hv⟩ : ∃ v : Fin 6 → ZMod 2, (ψ ⟨e₂, he₂X⟩ : AE.Wr 6) = AE.Wr.ofVec v :=
    ⟨(ψ ⟨e₂, he₂X⟩ : AE.Wr 6).vec, AE.Wr.ext rfl hperm1⟩
  have hφe₂ : I.φ ⟨e₂, he₂X⟩ = AE.mkQ 6 (AE.Wr.ofVec v) := by
    rw [← hψI, hv]
  have hconst : ∀ (R : Subgroup G) (hR : R ∈ DSet Ω W₂) (α : Finset (Fin 6)) (hα : α.card = 4)
      (b : Bool), (R.subgroupOf (pSpan (centMembers Ω e))).map I.φ = AE.memBar α hα b →
        ∀ i ∈ α, ∀ j ∈ α, v i = v j := by
    intro R hR α hα b hRα
    apply (AE.vec_centralizes_memBar_iff hn5 α hα b v).mp
    intro x hx
    rw [← hRα] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← hφe₂, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show e₂ * (y : G) = (y : G) * e₂
    exact (hcentM _ (hMle R hR (Subgroup.mem_subgroupOf.mp hy))).symm
  obtain ⟨α, hα, b, hKα⟩ := I.label K₂ (hD hKD₂)
  obtain ⟨β, hβ, b', hJβ⟩ := I.label (conjSub g₂ K₂) (hD hJ₂D)
  have hv_α := hconst K₂ hKD₂ α hα b hKα
  have hv_β := hconst (conjSub g₂ K₂) hJ₂D β hβ b' hJβ
  have hinv_map : ∀ (L : Subgroup G) (hL : L ∈ centMembers Ω e) {t : G}
      (ht : IsUniqueInvolution L t) {α : Finset (Fin 6)} {hα : α.card = 4} {b : Bool}
      (hLα : (L.subgroupOf (pSpan (centMembers Ω e))).map I.φ = AE.memBar α hα b),
      I.φ ⟨t, le_pSpan hL ht.mem⟩ = AE.zBar α hα := by
    intro L hL t ht α hα b hLα
    have hmem : I.φ ⟨t, le_pSpan hL ht.mem⟩ ∈ AE.memBar α hα b := by
      rw [← hLα]
      exact ⟨⟨t, le_pSpan hL ht.mem⟩, Subgroup.mem_subgroupOf.mpr ht.mem, rfl⟩
    have hsq : I.φ ⟨t, le_pSpan hL ht.mem⟩ * I.φ ⟨t, le_pSpan hL ht.mem⟩ = 1 := by
      rw [← map_mul]
      have e : (⟨t, le_pSpan hL ht.mem⟩ * ⟨t, le_pSpan hL ht.mem⟩ :
          pSpan (centMembers Ω e)) = 1 := Subtype.ext (by simp [ht.sq])
      rw [e, map_one]
    rcases AE.eq_of_mem_memBar_mul_self hn5 hmem hsq with h1 | h1
    · exact absurd h1 (e16n_involution_map_ne_one hΩ h2 hPΔ I hn5 hn7 hL ht)
    · exact h1
  have hαβ : α ≠ β := by
    intro hαβ
    subst hαβ
    have hφz₂ := hinv_map K₂ (hD hKD₂) hz₂ hKα
    have hφt₂ := hinv_map (conjSub g₂ K₂) (hD hJ₂D) hJ₂u hJβ
    obtain ⟨R₃, hR₃D, hR₃u⟩ := c₂.exists_dSet_zt h h9
    have hprod : I.φ ⟨z₂ * (u₂ * e₂), le_pSpan (hD hR₃D) hR₃u.mem⟩ = 1 := by
      have e : (⟨z₂ * (u₂ * e₂), le_pSpan (hD hR₃D) hR₃u.mem⟩ :
          pSpan (centMembers Ω e)) = ⟨z₂, le_pSpan (hD hKD₂) hz₂.mem⟩ *
            ⟨u₂ * e₂, le_pSpan (hD hJ₂D) hJ₂u.mem⟩ := Subtype.ext rfl
      rw [e, map_mul, hφz₂, hφt₂, e16n_zBar_sq]
    exact (e16n_involution_map_ne_one hΩ h2 hPΔ I hn5 hn7 (hD hR₃D) hR₃u) hprod
  have ht₂N : u₂ * e₂ ∈ Subgroup.normalizer (K₂ : Set G) := by
    have hu₂N : u₂ ∈ Subgroup.normalizer (K₂ : Set G) :=
      (sup_le (fun y hy => Subgroup.le_normalizer hy)
        (Asc77.AscL62.le_normalizer_of_commutes (c₂.twin.commutes h).symm)) c₂.data.hu
    have he₂N : e₂ ∈ Subgroup.normalizer (K₂ : Set G) :=
      e16n_mem_normalizer_of_centralizes fun k hk => (hcentM k (hMle K₂ hKD₂ hk)).symm
    exact (Subgroup.normalizer (K₂ : Set G)).mul_mem hu₂N he₂N
  have hJ₂notTwin : conjSub g₂ K₂ ∉ twinSet Ω K₂ := by
    rintro ⟨-, z', hz'K, hz'J⟩
    have h1 : u₂ * e₂ = z₂ := (hJ₂u.eq hz'J).trans (hz'K.eq hz₂)
    have h2' : e₂ = u₂ * z₂ := by
      rw [← h1, ← mul_assoc, c₂.data.hu2, one_mul]
    apply c₂.e_not_mem
    rw [h2']
    exact (K₂ ⊔ K₂').mul_mem c₂.data.hu (Subgroup.mem_sup_left hz₂.mem)
  have hJ₂star : conjSub g₂ K₂ ∈ omegaStarNbr Ω K₂ :=
    (h.mem_omegaStarNbr_or_twinSet h9 hK₂Ω hJ₂Ω hJ₂u ht₂N).resolve_right hJ₂notTwin
  have hJ₂n : conjSub g₂ K₂ ∉ omegaNbr Ω K₂ :=
    h.notMem_omegaNbr_of_notMem_twinSet h9 hK₂Ω hJ₂notTwin
  obtain ⟨-, -, hcJ, hnJ, -, -⟩ := pair_structure h hK₂Ω hJ₂star hJ₂n
  haveI := hcJ
  obtain ⟨xg, hxg⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := ↥(conjSub g₂ K₂ ⊓ Subgroup.normalizer (K₂ : Set G)))
  rw [hnJ] at hxg
  obtain ⟨x, hxJ, hxN, hxord⟩ : ∃ x : G, x ∈ conjSub g₂ K₂ ∧
      x ∈ Subgroup.normalizer (K₂ : Set G) ∧ orderOf x = 4 :=
    ⟨xg, (Subgroup.mem_inf.mp xg.2).1, (Subgroup.mem_inf.mp xg.2).2, by
      rw [Subgroup.orderOf_coe]
      exact hxg⟩
  have hxX : x ∈ pSpan (centMembers Ω e) := le_pSpan (hD hJ₂D) hxJ
  have hord4 : orderOf (I.φ ⟨x, hxX⟩) = 4 := by
    have hsq : ¬ (I.φ ⟨x, hxX⟩) ^ (2 ^ 1) = 1 := by
      intro hc
      rw [pow_one] at hc
      have hmem2 : x ^ 2 ∈ conjSub g₂ K₂ := (conjSub g₂ K₂).pow_mem hxJ 2
      have hx2 : x ^ 2 = 1 := by
        apply e16n_eq_one_of_map_eq_one hΩ h2 hPΔ I hn5 hn7 (hD hJ₂D) hmem2
        have e : (⟨x ^ 2, le_pSpan (hD hJ₂D) hmem2⟩ : pSpan (centMembers Ω e)) =
            ⟨x, hxX⟩ ^ 2 := Subtype.ext rfl
        rw [e, map_pow]
        exact hc
      have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
      rw [hxord] at hd
      norm_num at hd
    have h4 : (I.φ ⟨x, hxX⟩) ^ (2 ^ (1 + 1)) = 1 := by
      have e4 : (⟨x, hxX⟩ : pSpan (centMembers Ω e)) ^ (2 ^ (1 + 1)) = 1 := by
        apply Subtype.ext
        show x ^ (2 ^ (1 + 1)) = 1
        norm_num
        rw [← hxord]
        exact pow_orderOf_eq_one x
      rw [← map_pow, e4, map_one]
    rw [orderOf_eq_prime_pow hsq h4]
    norm_num
  have hgβ : I.φ ⟨x, hxX⟩ ∈ AE.memBar β hβ b' := by
    rw [← hJβ]
    exact ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.mpr hxJ, rfl⟩
  have hnorm : ∀ y ∈ AE.memBar α hα b,
      I.φ ⟨x, hxX⟩ * y * (I.φ ⟨x, hxX⟩)⁻¹ ∈ AE.memBar α hα b := by
    intro y hy
    rw [← hKα] at hy ⊢
    obtain ⟨k, hk, rfl⟩ := hy
    have hxk : x * (k : G) * x⁻¹ ∈ K₂ :=
      (Subgroup.mem_normalizer_iff.mp hxN k).mp (Subgroup.mem_subgroupOf.mp hk)
    refine ⟨⟨x * (k : G) * x⁻¹, le_pSpan (hD hKD₂) hxk⟩, Subgroup.mem_subgroupOf.mpr hxk, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hcard := AE.card_inter_eq_two_of_normalizes_of_le_seven hgβ hord4 hnorm
    (by norm_num) hαβ
  have hunion : α ∪ β = Finset.univ := by
    have h1 := Finset.card_union_add_card_inter α β
    rw [hα, hβ, hcard] at h1
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]
    omega
  obtain ⟨m, hm⟩ : (α ∩ β).Nonempty := by
    rw [← Finset.card_pos, hcard]
    norm_num
  have hmα : m ∈ α := (Finset.mem_inter.mp hm).1
  have hmβ : m ∈ β := (Finset.mem_inter.mp hm).2
  have hvm : ∀ i : Fin 6, v i = v m := by
    intro i
    have hi : i ∈ α ∪ β := by
      rw [hunion]
      exact Finset.mem_univ i
    rcases Finset.mem_union.mp hi with hiα | hiβ
    · exact hv_α i hiα m hmα
    · exact hv_β i hiβ m hmβ
  rcases e16n_zmod2 (v m) with h0 | h1
  · exfalso
    have hv0 : v = fun _ => 0 := funext fun i => (hvm i).trans h0
    have hψ1 : ψ ⟨e₂, he₂X⟩ = 1 := Subtype.ext (by rw [hv, hv0]; rfl)
    have hx1 : (⟨e₂, he₂X⟩ : pSpan (centMembers Ω e)) = 1 :=
      ψ.injective (hψ1.trans (map_one ψ).symm)
    exact c₂.data.he1 (congrArg Subtype.val hx1)
  · have hv1 : v = fun _ => 1 := funext fun i => (hvm i).trans h1
    have hψA : (ψ ⟨e₂, he₂X⟩ : AE.Wr 6) = (ψ ⟨e, hei⟩ : AE.Wr 6) := by
      rw [hv, heψ, hv1]
      rfl
    have hxe : (⟨e₂, he₂X⟩ : pSpan (centMembers Ω e)) = ⟨e, hei⟩ :=
      ψ.injective (Subtype.ext hψA)
    exact congrArg Subtype.val hxe

end Sit16

end CFSG.ClassicalInvolution.Q3.Sec13
