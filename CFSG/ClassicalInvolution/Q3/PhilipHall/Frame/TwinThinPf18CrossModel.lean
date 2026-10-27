module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Mem

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

variable {n : ℕ}

theorem exists_four_set (T U : Finset (Fin n)) (hTU : Disjoint T U) (hT : T.card ≤ 4)
    (hU : U.card + 4 ≤ n) : ∃ β : Finset (Fin n), T ⊆ β ∧ Disjoint β U ∧ β.card = 4 := by
  classical
  have hst : T ⊆ Uᶜ := Finset.subset_compl_iff_disjoint_right.mpr hTU
  have hcard : 4 ≤ (Uᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨β, hTβ, hβU, hβ⟩ := Finset.exists_subsuperset_card_eq hst hT hcard
  exact ⟨β, hTβ, Finset.disjoint_of_subset_left hβU disjoint_compl_left, hβ⟩

theorem perm_eq_one_of_four_sets (hn : 5 ≤ n) (σ : Equiv.Perm (Fin n))
    (h : ∀ β : Finset (Fin n), β.card = 4 →
      (∀ p, p ∈ β ↔ σ p ∈ β) ∨ (∀ p, p ∈ β ↔ σ p ∉ β)) : σ = 1 := by
  classical
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hall
    exact hne (Equiv.ext fun x => by by_contra hx; exact hall ⟨x, hx⟩)
  obtain ⟨y, hy⟩ : ∃ y, σ x = y := ⟨_, rfl⟩
  rw [hy] at hx
  have S1 : ∀ β : Finset (Fin n), β.card = 4 → x ∈ β → y ∈ β → ∀ p, p ∈ β ↔ σ p ∈ β := by
    intro β hβ hxβ hyβ
    rcases h β hβ with h1 | h2
    · exact h1
    · exact absurd hyβ (by rw [← hy]; exact (h2 x).mp hxβ)
  have S2 : σ y = x := by
    by_contra hyx
    have hyy : σ y ≠ y := by
      intro h'
      exact hx (σ.injective (by rw [hy]; exact h'.symm)).symm
    obtain ⟨β, hxyβ, hβq, hβ⟩ := exists_four_set ({x, y} : Finset (Fin n)) {σ y}
      (by
        rw [Finset.disjoint_singleton_right]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hyx, hyy⟩)
      (Finset.card_le_two.trans (by norm_num)) (by simp; omega)
    have hxβ : x ∈ β := hxyβ (by simp)
    have hyβ : y ∈ β := hxyβ (by simp)
    have := (S1 β hβ hxβ hyβ y).mp hyβ
    exact (Finset.disjoint_singleton_right.mp hβq) this
  have S3 : ∀ p, p ≠ x → p ≠ y → σ p = p := by
    intro p hpx hpy
    by_contra hp
    have hqx : σ p ≠ x := by
      intro h'
      exact hpy (σ.injective (by rw [h', S2]))
    have hqy : σ p ≠ y := by
      intro h'
      exact hpx (σ.injective (by rw [h', hy]))
    obtain ⟨β, hxyβ, hβq, hβ⟩ := exists_four_set ({x, y, p} : Finset (Fin n)) {σ p}
      (by
        rw [Finset.disjoint_singleton_right]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hqx, hqy, hp⟩)
      (Finset.card_le_three.trans (by norm_num)) (by simp; omega)
    have hxβ : x ∈ β := hxyβ (by simp)
    have hyβ : y ∈ β := hxyβ (by simp)
    have hpβ : p ∈ β := hxyβ (by simp)
    have := (S1 β hβ hxβ hyβ p).mp hpβ
    exact (Finset.disjoint_singleton_right.mp hβq) this
  obtain ⟨β, hxβ', hβy, hβ⟩ := exists_four_set ({x} : Finset (Fin n)) {y}
    (by
      rw [Finset.disjoint_singleton_right]
      simp only [Finset.mem_singleton]
      exact hx)
    (by simp) (by simp; omega)
  have hxβ : x ∈ β := hxβ' (by simp)
  have hyβ : y ∉ β := Finset.disjoint_singleton_right.mp hβy
  obtain ⟨a, haβ, hax⟩ : ∃ a ∈ β, a ≠ x := by
    by_contra hall
    have hsub : β ⊆ {x} := fun a ha => by
      by_contra hax
      exact hall ⟨a, ha, by simpa using hax⟩
    have := Finset.card_le_card hsub
    rw [hβ] at this
    simp at this
  have hay : a ≠ y := fun h' => hyβ (h' ▸ haβ)
  have hσa : σ a = a := S3 a hax hay
  rcases h β hβ with h1 | h2
  · exact hyβ (hy ▸ (h1 x).mp hxβ)
  · exact (h2 a).mp haβ (by rw [hσa]; exact haβ)

theorem mkQ_ofVec_eq_iff (u u' : Fin n → ZMod 2) :
    mkQ n (ofVec u') = mkQ n (ofVec u) ↔ (∀ x, u' x = u x) ∨ (∀ x, u' x = u x + 1) := by
  rw [mkQ_eq_iff]
  have hz2 : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
  have hz2' : ∀ a b : ZMod 2, a + b = 1 ↔ a = b + 1 := by decide
  have e : ∀ x, ((ofVec u')⁻¹ * ofVec u).vec x = u' x + u x := fun x => rfl
  have ep : ((ofVec u')⁻¹ * ofVec u).perm = 1 := by
    show (ofVec u').perm⁻¹ * (ofVec u).perm = 1
    simp [ofVec]
  constructor
  · rintro (h | h)
    · left
      intro x
      have := congrFun (congrArg Wr.vec h) x
      rw [e] at this
      exact (hz2 _ _).mp this
    · right
      intro x
      have := congrFun (congrArg Wr.vec h) x
      rw [e] at this
      exact (hz2' _ _).mp this
  · rintro (h | h)
    · left
      refine Wr.ext (funext fun x => ?_) ep
      rw [e]
      exact (hz2 _ _).mpr (h x)
    · right
      refine Wr.ext (funext fun x => ?_) ep
      rw [e]
      exact (hz2' _ _).mpr (h x)

theorem preserves_or_compl_of_cent_zBar (w : Wr n) (β : Finset (Fin n)) (hβ : β.card = 4)
    (h : mkQ n w * zBar β hβ * (mkQ n w)⁻¹ = zBar β hβ) :
    (∀ p, p ∈ β ↔ w.perm p ∈ β) ∨ (∀ p, p ∈ β ↔ w.perm p ∉ β) := by
  classical
  have h1 : mkQ n (w * zOf (emb β hβ) * w⁻¹) = mkQ n (zOf (emb β hβ)) := by
    simpa only [zBar, map_mul, map_inv] using h
  rw [zOf_eq_ofVec, conj_ofVec, mkQ_ofVec_eq_iff] at h1
  have hmem : ∀ x, x ∈ Set.range (emb β hβ) ↔ x ∈ β := fun x => by
    rw [range_emb]; exact Finset.mem_coe
  rcases h1 with h1 | h1
  · left
    intro p
    have := h1 (w.perm p)
    simp only [Equiv.symm_apply_apply, hmem] at this
    by_cases hp : p ∈ β <;> by_cases hq : w.perm p ∈ β <;> simp [hp, hq] at this ⊢
  · right
    intro p
    have := h1 (w.perm p)
    simp only [Equiv.symm_apply_apply, hmem] at this
    by_cases hp : p ∈ β <;> by_cases hq : w.perm p ∈ β <;> simp [hp, hq] at this ⊢
    all_goals first | exact absurd this (by decide) | skip

theorem perm_eq_one_of_cent_zBar (hn : 5 ≤ n) (w : Wr n)
    (h : ∀ (β : Finset (Fin n)) (hβ : β.card = 4),
      mkQ n w * zBar β hβ * (mkQ n w)⁻¹ = zBar β hβ) : w.perm = 1 :=
  perm_eq_one_of_four_sets hn w.perm fun β hβ => preserves_or_compl_of_cent_zBar w β hβ (h β hβ)

@[expose] def pairV (a b : Fin n) : Fin n → ZMod 2 := fun x => if x = a ∨ x = b then 1 else 0

theorem preserves_pair_of_cent_pairV (hn : 5 ≤ n) (w : Wr n) (a b : Fin n)
    (h : mkQ n w * mkQ n (ofVec (pairV a b)) * (mkQ n w)⁻¹ = mkQ n (ofVec (pairV a b))) :
    ∀ p, (p = a ∨ p = b) ↔ (w.perm p = a ∨ w.perm p = b) := by
  classical
  have hc : mkQ n (w * ofVec (pairV a b) * w⁻¹) = mkQ n (ofVec (pairV a b)) := by
    simpa only [map_mul, map_inv] using h
  rw [conj_ofVec, mkQ_ofVec_eq_iff] at hc
  rcases hc with hc | hc
  · intro p
    have := hc (w.perm p)
    simp only [Equiv.symm_apply_apply, pairV] at this
    by_cases hp : p = a ∨ p = b <;> by_cases hq : w.perm p = a ∨ w.perm p = b <;>
      simp_all
  · exfalso
    obtain ⟨p, hp⟩ : ∃ p : Fin n, p ∉ ({a, b, w.perm a, w.perm b} : Finset (Fin n)) := by
      have hlt : ({a, b, w.perm a, w.perm b} : Finset (Fin n)).card <
          (Finset.univ : Finset (Fin n)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        exact lt_of_le_of_lt Finset.card_le_four (by omega)
      obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      exact ⟨p, hp⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    have := hc p
    simp only [pairV] at this
    have hq1 : (w.perm.symm p = a ∨ w.perm.symm p = b) := by
      by_contra hq
      simp [hq, hp1, hp2] at this
    rcases hq1 with hq1 | hq1
    · exact hp3 (by rw [← hq1]; simp)
    · exact hp4 (by rw [← hq1]; simp)

theorem pairVec_decomp : ∀ i j : Fin 4, i ≠ j →
    ∃ k ∈ kList, ∃ k' ∈ kStarList, k * k'⁻¹ = (⟨vec4 [i, j], 1⟩ : Wr 4) := by decide +kernel

theorem embed_pairVec_vec (ι : Fin 4 ↪ Fin n) (i j : Fin 4) :
    (embed ι (⟨vec4 [i, j], 1⟩ : Wr 4)).vec = pairV (ι i) (ι j) := by
  classical
  funext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨l, rfl⟩ := hx
    rw [embed_vec, embedVec_apply]
    simp only [vec4, pairV, List.mem_cons, List.not_mem_nil, or_false, ι.injective.eq_iff]
  · rw [embed_vec_of_not_mem ι _ hx]
    have h1 : x ≠ ι i := fun h' => hx ⟨i, h'.symm⟩
    have h2 : x ≠ ι j := fun h' => hx ⟨j, h'.symm⟩
    simp [pairV, h1, h2]

theorem perm_fix_of_cent_memBar (hn : 5 ≤ n) (α : Finset (Fin n)) (hα : α.card = 4) (w : Wr n)
    (hB : ∀ c : Bool, ∀ x ∈ memBar α hα c, mkQ n w * x * (mkQ n w)⁻¹ = x) :
    ∀ i ∈ α, w.perm i = i := by
  classical
  have key : ∀ a ∈ α, ∀ b ∈ α, a ≠ b →
      ∀ p, (p = a ∨ p = b) ↔ (w.perm p = a ∨ w.perm p = b) := by
    intro a ha b hb hab
    obtain ⟨i, rfl⟩ : a ∈ Set.range (emb α hα) := by
      rw [range_emb]; exact Finset.mem_coe.mpr ha
    obtain ⟨j, rfl⟩ : b ∈ Set.range (emb α hα) := by
      rw [range_emb]; exact Finset.mem_coe.mpr hb
    have hij : i ≠ j := fun h' => hab (by rw [h'])
    obtain ⟨k, hk, k', hk', hkk'⟩ := pairVec_decomp i j hij
    have h1 := hB true _ (mkQ_embed_mem_true α hα hk)
    have h2 := hB false _ (mkQ_embed_mem_false α hα hk')
    set E : Wr n := embed (emb α hα) (⟨vec4 [i, j], 1⟩ : Wr 4) with hE
    have hEmk : mkQ n E = mkQ n (embed (emb α hα) k) * (mkQ n (embed (emb α hα) k'))⁻¹ := by
      rw [hE, ← hkk', map_mul, map_inv, map_mul, map_inv]
    have hEperm : E.perm = 1 := by
      rw [hE, embed_perm]
      exact embedPerm_one _
    have hEv : E = ofVec (pairV (emb α hα i) (emb α hα j)) := by
      have := embed_pairVec_vec (emb α hα) i j
      rw [← hE] at this
      rw [← this]
      exact Wr.ext rfl hEperm
    refine preserves_pair_of_cent_pairV hn w _ _ ?_
    rw [← hEv, hEmk]
    calc mkQ n w * (mkQ n (embed (emb α hα) k) * (mkQ n (embed (emb α hα) k'))⁻¹) *
          (mkQ n w)⁻¹
        = (mkQ n w * mkQ n (embed (emb α hα) k) * (mkQ n w)⁻¹) *
          (mkQ n w * mkQ n (embed (emb α hα) k') * (mkQ n w)⁻¹)⁻¹ := by group
      _ = _ := by rw [h1, h2]
  intro x hx
  by_contra hxx
  have hcard : 1 < (α.erase x).card := by
    rw [Finset.card_erase_of_mem hx, hα]; norm_num
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.mp hcard
  rw [Finset.mem_erase] at hb hc
  have k1 := (key x hx b hb.2 (Ne.symm hb.1) x).mp (Or.inl rfl)
  have k2 := (key x hx c hc.2 (Ne.symm hc.1) x).mp (Or.inl rfl)
  rcases k1 with k1 | k1
  · exact hxx k1
  · rcases k2 with k2 | k2
    · exact hxx k2
    · exact hbc (k1.symm.trans k2)

theorem conj_memBar_of_perm_one (hn : 5 ≤ n) (w : Wr n) (hw : w.perm = 1) (β : Finset (Fin n))
    (hβ : β.card = 4) (c : Bool) :
    (memBar β hβ c).map (MulAut.conj (mkQ n w)).toMonoidHom = memBar β hβ c ∨
      (memBar β hβ c).map (MulAut.conj (mkQ n w)).toMonoidHom = memBar β hβ (!c) := by
  obtain ⟨v, rfl⟩ : ∃ v, w = ofVec v := ⟨w.vec, Wr.ext rfl hw⟩
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) (∑ i, v (emb β hβ i)) with h0 | h1
  · exact Or.inl (conj_memBar_vec_even hn β hβ c v h0)
  · exact Or.inr (conj_memBar_vec_odd hn β hβ c v h1)

theorem comm_mem_vecBar (w a : Wr n) (hw : w.perm = 1) :
    mkQ n w * mkQ n a * (mkQ n w)⁻¹ * (mkQ n a)⁻¹ ∈ (vecSub n).map (mkQ n) := by
  have hwv : w ∈ vecSub n := hw
  have hwi : w⁻¹ ∈ vecSub n := (vecSub n).inv_mem hwv
  have h1 : a * w⁻¹ * a⁻¹ ∈ vecSub n := (vecSub_normal (n := n)).conj_mem _ hwi a
  refine ⟨w * (a * w⁻¹ * a⁻¹), (vecSub n).mul_mem hwv h1, ?_⟩
  simp only [map_mul, map_inv]
  group

theorem perm_eq_one_of_fix_four_fin5 (σ : Equiv.Perm (Fin 5)) (α : Finset (Fin 5)) (hα : α.card = 4)
    (h : ∀ i ∈ α, σ i = i) : σ = 1 := by
  classical
  have hc : (αᶜ).card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin, hα]
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  have hpα : p ∉ α := by
    have : p ∈ αᶜ := by rw [hp]; exact Finset.mem_singleton_self p
    exact Finset.mem_compl.mp this
  have hσp : σ p = p := by
    by_contra hne
    have hq : σ p ∈ α := by
      by_contra hq
      have : σ p ∈ αᶜ := Finset.mem_compl.mpr hq
      rw [hp, Finset.mem_singleton] at this
      exact hne this
    have h1 := h _ hq
    have e : σ p = p := σ.injective h1
    rw [e] at hq
    exact hpα hq
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ α
  · exact h x hx
  · have : x ∈ αᶜ := Finset.mem_compl.mpr hx
    rw [hp, Finset.mem_singleton] at this
    rw [this, hσp]
    rfl

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18
