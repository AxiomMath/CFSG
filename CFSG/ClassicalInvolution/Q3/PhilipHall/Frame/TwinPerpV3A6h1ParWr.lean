module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h1
public import CFSG.ClassicalInvolution.Q3.AE.Conj
public import CFSG.ClassicalInvolution.Q3.AE.PermElt
public import Certificates.Data.AE6ParData

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

section Over

theorem ofPerm_mem_aeSubOver_of_le {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : A ≤ alternatingGroup (Fin 8)) {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ A) :
    ofPerm σ ∈ aeSubOver A :=
  ⟨mem_aeSub.mpr ⟨by simp [wsum, ofPerm], Equiv.Perm.mem_alternatingGroup.mp (hA hσ)⟩, hσ⟩

@[expose] def aeSubOverEquiv (A : Subgroup (Equiv.Perm (Fin 8)))
    (hA : A ≤ alternatingGroup (Fin 8)) :
    ↥(aeSubOver A) ≃ {v : Fin 8 → ZMod 2 // ∑ i, v i = 0} × ↥A where
  toFun a := (⟨a.1.vec, (mem_aeSub.mp a.2.1).1⟩, ⟨a.1.perm, a.2.2⟩)
  invFun p := ⟨⟨p.1.1, p.2.1⟩,
    mem_aeSub.mpr ⟨p.1.2, Equiv.Perm.mem_alternatingGroup.mp (hA p.2.2)⟩, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_aeSubOver (A : Subgroup (Equiv.Perm (Fin 8))) (hA : A ≤ alternatingGroup (Fin 8)) :
    Nat.card (aeSubOver A) = 128 * Nat.card A := by
  rw [Nat.card_congr (aeSubOverEquiv A hA), Nat.card_prod, Nat.card_congr ae6EvenVecEquiv,
    Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem piSub_le_aeSubOver (A : Subgroup (Equiv.Perm (Fin 8))) : piSub 8 ≤ aeSubOver A := by
  intro a ha
  rcases mem_piSub.mp ha with rfl | rfl
  · exact (aeSubOver A).one_mem
  · exact ⟨allOnes_mem_aeSub8, A.one_mem⟩

theorem card_aeBarOver (A : Subgroup (Equiv.Perm (Fin 8))) (hA : A ≤ alternatingGroup (Fin 8)) :
    Nat.card (aeBarOver A) = 64 * Nat.card A := by
  have h1 := Subgroup.relIndex_mul_card (mkQ 8).ker (aeSubOver A)
  rw [Subgroup.relIndex_ker, QuotientGroup.ker_mk', inf_eq_left.mpr (piSub_le_aeSubOver A),
    card_piSub8, card_aeSubOver A hA] at h1
  show Nat.card ((aeSubOver A).map (mkQ 8)) = 64 * Nat.card A
  omega

theorem aeSubOver_alternating : aeSubOver (alternatingGroup (Fin 8)) = aeSub 8 := by
  refine le_antisymm inf_le_left fun a ha => ⟨ha, ?_⟩
  exact Equiv.Perm.mem_alternatingGroup.mpr (mem_aeSub.mp ha).2

theorem aeBarOver_alternating : aeBarOver (alternatingGroup (Fin 8)) = ae6AE8 := by
  rw [aeBarOver, aeSubOver_alternating]

theorem mkQ_mem_aeBarOver {A : Subgroup (Equiv.Perm (Fin 8))} {a : Wr 8}
    (ha : a ∈ aeSubOver A) : mkQ 8 a ∈ aeBarOver A :=
  ⟨a, ha, rfl⟩

theorem mem_aeSub_of_mkQ_mem {a : Wr 8} (ha : mkQ 8 a ∈ ae6AE8) : a ∈ aeSub 8 := by
  obtain ⟨b, hb, he⟩ := ha
  have hπ : b⁻¹ * a ∈ aeSub 8 := by
    rcases mkQ_eq_iff.mp he with h | h
    · rw [h]; exact (aeSub 8).one_mem
    · rw [h]; exact allOnes_mem_aeSub8
  have : a = b * (b⁻¹ * a) := by group
  rw [this]
  exact (aeSub 8).mul_mem hb hπ

theorem mem_aeSubOver_of_mkQ_mem {A : Subgroup (Equiv.Perm (Fin 8))} {a : Wr 8}
    (ha : mkQ 8 a ∈ aeBarOver A) : a ∈ aeSubOver A := by
  obtain ⟨b, hb, he⟩ := ha
  have hπ : b⁻¹ * a ∈ aeSubOver A := by
    rcases mkQ_eq_iff.mp he with h | h
    · rw [h]; exact (aeSubOver A).one_mem
    · rw [h]; exact piSub_le_aeSubOver A (Or.inr rfl)
  have : a = b * (b⁻¹ * a) := by group
  rw [this]
  exact (aeSubOver A).mul_mem hb hπ

theorem exists_eq_aeBarOver {S : Subgroup (Equiv.Perm (Fin 8))}
    (hS : S ≤ alternatingGroup (Fin 8)) {X : Subgroup (AEQ 8)} (hSX : aeBarOver S ≤ X)
    (hX : X ≤ ae6AE8) :
    ∃ A : Subgroup (Equiv.Perm (Fin 8)), S ≤ A ∧ A ≤ alternatingGroup (Fin 8) ∧
      X = aeBarOver A := by
  set Xt : Subgroup (Wr 8) := X.comap (mkQ 8) with hXt
  have hXt_le : Xt ≤ aeSub 8 := fun x hx => mem_aeSub_of_mkQ_mem (hX hx)
  refine ⟨Xt.map (permHom 8), ?_, ?_, ?_⟩
  · intro σ hσ
    have h1 : ofPerm σ ∈ Xt := hSX (mkQ_mem_aeBarOver (ofPerm_mem_aeSubOver_of_le hS hσ))
    exact ⟨ofPerm σ, h1, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mpr (mem_aeSub.mp (hXt_le hx)).2
  · have heq : Xt = aeSubOver (Xt.map (permHom 8)) := by
      refine le_antisymm (fun x hx => ⟨hXt_le hx, ⟨x, hx, rfl⟩⟩) ?_
      rintro a ⟨haS, ⟨x, hx, hxa⟩⟩
      have hb : a * x⁻¹ ∈ aeSubOver S := by
        refine ⟨(aeSub 8).mul_mem haS ((aeSub 8).inv_mem (hXt_le hx)), ?_⟩
        show (a * x⁻¹).perm ∈ S
        have : (a * x⁻¹).perm = 1 := by
          rw [mul_perm, inv_perm]
          have hxa' : x.perm = a.perm := hxa
          rw [hxa', mul_inv_cancel]
        rw [this]
        exact S.one_mem
      have hb' : a * x⁻¹ ∈ Xt := hSX (mkQ_mem_aeBarOver hb)
      have : a = (a * x⁻¹) * x := by group
      rw [this]
      exact Xt.mul_mem hb' hx
    calc X = Xt.map (mkQ 8) :=
          (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) X).symm
      _ = aeBarOver (Xt.map (permHom 8)) := by rw [aeBarOver, ← heq]

end Over

section ZBar

@[expose] def parInd (δ : Finset (Fin 8)) : Fin 8 → ZMod 2 := fun x => if x ∈ δ then 1 else 0

theorem zOf_emb_eq (δ : Finset (Fin 8)) (h : δ.card = 4) :
    zOf (emb δ h) = ofVec (parInd δ) := by
  refine Wr.ext (funext fun x => ?_) (zOf_perm _)
  rw [zOf_vec_apply]
  have hr : x ∈ Set.range (emb δ h) ↔ x ∈ δ := by rw [range_emb]; rfl
  by_cases hx : x ∈ δ
  · rw [if_pos (hr.mpr hx)]
    simp [hx, parInd, ofVec]
  · rw [if_neg fun h' => hx (hr.mp h')]
    simp [hx, parInd, ofVec]

theorem zBar_eq_mk (δ : Finset (Fin 8)) (h : δ.card = 4) :
    zBar δ h = mkQ 8 (ofVec (parInd δ)) := by
  rw [zBar, zOf_emb_eq]

theorem ofVec_mul_ofVec (v w : Fin 8 → ZMod 2) : ofVec v * ofVec w = ofVec (v + w) :=
  Wr.ext (funext fun _ => rfl) (one_mul 1)

theorem vec_of_mkQ_ofVec_eq {v w : Fin 8 → ZMod 2} (h : mkQ 8 (ofVec v) = mkQ 8 (ofVec w)) :
    (∀ x, v x + w x = 0) ∨ (∀ x, v x + w x = 1) := by
  rcases mkQ_eq_iff.mp h with h1 | h1
  · exact Or.inl fun x => congrFun (congrArg Wr.vec h1) x
  · exact Or.inr fun x => congrFun (congrArg Wr.vec h1) x

theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem eq_or_compl_of_zBar_eq {δ δ' : Finset (Fin 8)} {h : δ.card = 4} {h' : δ'.card = 4}
    (he : zBar δ h = zBar δ' h') : δ' = δ ∨ δ' = δᶜ := by
  rw [zBar_eq_mk, zBar_eq_mk] at he
  rcases vec_of_mkQ_ofVec_eq he with h1 | h1
  · left
    ext x
    have := h1 x
    by_cases hx : x ∈ δ <;> by_cases hx' : x ∈ δ' <;>
      simp only [parInd, hx, hx', if_true, if_false] at this <;> simp only [hx, hx'] <;>
      revert this <;> decide
  · right
    ext x
    have := h1 x
    rw [Finset.mem_compl]
    by_cases hx : x ∈ δ <;> by_cases hx' : x ∈ δ' <;>
      simp only [parInd, hx, hx', if_true, if_false] at this <;> simp only [hx, hx'] <;>
      revert this <;> decide

theorem card_symmDiff_of_zBar_mul {α β γ : Finset (Fin 8)} {hα : α.card = 4} {hβ : β.card = 4}
    {hγ : γ.card = 4} (he : zBar α hα * zBar β hβ = zBar γ hγ) : (symmDiff α β).card = 4 := by
  rw [zBar_eq_mk, zBar_eq_mk, zBar_eq_mk, ← map_mul, ofVec_mul_ofVec] at he
  rcases vec_of_mkQ_ofVec_eq he with h1 | h1
  · have hs : symmDiff α β = γ := by
      ext x
      have := h1 x
      rw [Finset.mem_symmDiff]
      by_cases hx : x ∈ α <;> by_cases hy : x ∈ β <;> by_cases hz : x ∈ γ <;>
        simp only [parInd, Pi.add_apply, hx, hy, hz, if_true, if_false] at this <;>
        simp only [hx, hy, hz] <;> revert this <;> decide
    rw [hs, hγ]
  · have hs : symmDiff α β = γᶜ := by
      ext x
      have := h1 x
      rw [Finset.mem_symmDiff, Finset.mem_compl]
      by_cases hx : x ∈ α <;> by_cases hy : x ∈ β <;> by_cases hz : x ∈ γ <;>
        simp only [parInd, Pi.add_apply, hx, hy, hz, if_true, if_false] at this <;>
        simp only [hx, hy, hz] <;> revert this <;> decide
    rw [hs, Finset.card_compl, hγ, Fintype.card_fin]

end ZBar

section Members

theorem kList_perm_vk : ∀ k ∈ kList, k.perm * k.perm = 1 ∧ (k.perm = 1 ∨ ∀ i, k.perm i ≠ i) := by
  decide +kernel

theorem kStarList_perm_vk :
    ∀ k ∈ kStarList, k.perm * k.perm = 1 ∧ (k.perm = 1 ∨ ∀ i, k.perm i ≠ i) := by
  decide +kernel

theorem exists_kList_perm : ∀ d : Equiv.Perm (Fin 4), d * d = 1 → (d = 1 ∨ ∀ i, d i ≠ i) →
    ∃ k ∈ kList, k.perm = d := by
  decide +kernel

theorem exists_kStarList_perm : ∀ d : Equiv.Perm (Fin 4), d * d = 1 → (d = 1 ∨ ∀ i, d i ≠ i) →
    ∃ k ∈ kStarList, k.perm = d := by
  decide +kernel

theorem vkPred_embedPerm {δ : Finset (Fin 8)} {ι : Fin 4 ↪ Fin 8}
    (hι : Set.range ι = (δ : Set (Fin 8))) {d : Equiv.Perm (Fin 4)} (hd2 : d * d = 1)
    (hd : d = 1 ∨ ∀ i, d i ≠ i) : Certificates.AE6Par.vkPred δ (embedPerm ι d) = true := by
  have hmem : ∀ i, ι i ∈ δ := fun i => by
    have : ι i ∈ Set.range ι := Set.mem_range_self i
    rw [hι] at this
    exact this
  have hrange : ∀ x ∈ δ, ∃ i, ι i = x := fun x hx => by
    have : x ∈ Set.range ι := by rw [hι]; exact hx
    exact this
  refine decide_eq_true ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    refine embedPerm_of_not_mem ι d ?_
    rw [hι]
    exact hx
  · intro x hx
    obtain ⟨i, rfl⟩ := hrange x hx
    rw [embedPerm_apply]
    exact hmem _
  · rw [← embedPerm_mul, hd2, embedPerm_one]
  · rcases hd with rfl | hd
    · left
      exact embedPerm_one ι
    · right
      intro x hx
      obtain ⟨i, rfl⟩ := hrange x hx
      rw [embedPerm_apply]
      exact fun h => hd i (ι.injective h)

theorem vkPred_perm_of_mem_memAt {δ : Finset (Fin 8)} {h : δ.card = 4} {c : Bool} {a : Wr 8}
    (ha : a ∈ memAt δ h c) : Certificates.AE6Par.vkPred δ a.perm = true := by
  cases c
  · obtain ⟨k, hk, rfl⟩ := ha
    obtain ⟨h1, h2⟩ := kStarList_perm_vk k hk
    exact vkPred_embedPerm (range_emb δ h) h1 h2
  · obtain ⟨k, hk, rfl⟩ := ha
    obtain ⟨h1, h2⟩ := kList_perm_vk k hk
    exact vkPred_embedPerm (range_emb δ h) h1 h2

theorem exists_mem_memAt_perm {δ : Finset (Fin 8)} (h : δ.card = 4) (c : Bool)
    {σ : Equiv.Perm (Fin 8)} (hσ : Certificates.AE6Par.vkPred δ σ = true) :
    ∃ a ∈ memAt δ h c, a.perm = σ := by
  obtain ⟨hout, hin, h2, h1⟩ := of_decide_eq_true hσ
  set ι := emb δ h with hιdef
  have hι : Set.range ι = (δ : Set (Fin 8)) := range_emb δ h
  have hmem : ∀ i, ι i ∈ δ := fun i => by
    have : ι i ∈ Set.range ι := Set.mem_range_self i
    rw [hι] at this
    exact this
  have hmap : ∀ i, σ (ι i) ∈ Set.range ι := fun i => by
    rw [hι]
    exact hin _ (hmem i)
  set d := localPerm ι σ hmap with hd
  have hspec : ∀ i, σ (ι i) = ι (d i) := localPerm_spec ι σ hmap
  have hd2 : d * d = 1 := by
    refine Equiv.ext fun i => ι.injective ?_
    have : (σ * σ) (ι i) = ι i := by rw [h2]; rfl
    rw [Equiv.Perm.mul_apply, hspec, hspec] at this
    rw [Equiv.Perm.mul_apply]
    exact this
  have hd1 : d = 1 ∨ ∀ i, d i ≠ i := by
    rcases h1 with rfl | h1
    · left
      refine Equiv.ext fun i => ι.injective ?_
      rw [← hspec]
      rfl
    · right
      intro i hi
      apply h1 _ (hmem i)
      rw [hspec, hi]
  have heq : ∀ k : Wr 4, k.perm = d → (embed ι k).perm = σ := by
    intro k hk
    refine Equiv.ext fun x => ?_
    rw [embed_perm, hk]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedPerm_apply, hspec]
    · rw [embedPerm_of_not_mem ι d hx]
      refine (hout x ?_).symm
      rw [← Finset.mem_coe, ← hι]
      exact hx
  cases c
  · obtain ⟨k, hk, hkd⟩ := exists_kStarList_perm d hd2 hd1
    exact ⟨embed ι k, ⟨k, hk, rfl⟩, heq k hkd⟩
  · obtain ⟨k, hk, hkd⟩ := exists_kList_perm d hd2 hd1
    exact ⟨embed ι k, ⟨k, hk, rfl⟩, heq k hkd⟩

@[expose] def pairVec (x y : Fin 8) : Fin 8 → ZMod 2 :=
  fun z => (if z = x then 1 else 0) + (if z = y then 1 else 0)

theorem local_pair : ∀ i j : Fin 4, i ≠ j →
    ∃ k ∈ kList, ∃ k' ∈ kStarList, k * k' = ofVec (vec4 [i, j]) := by
  decide +kernel

theorem embed_ofVec_vec4 (ι : Fin 4 ↪ Fin 8) {i j : Fin 4} (hij : i ≠ j) :
    embed ι (ofVec (vec4 [i, j])) = ofVec (pairVec (ι i) (ι j)) := by
  classical
  refine Wr.ext (funext fun z => ?_) (embedPerm_one ι)
  rw [embed_vec]
  by_cases hz : z ∈ Set.range ι
  · obtain ⟨k, rfl⟩ := hz
    rw [embedVec_apply]
    show vec4 [i, j] k = pairVec (ι i) (ι j) (ι k)
    simp only [vec4, pairVec, ι.injective.eq_iff, List.mem_cons, List.not_mem_nil, or_false]
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
  · rw [embedVec_of_not_mem ι _ hz]
    have h1 : z ≠ ι i := fun h => hz ⟨i, h.symm⟩
    have h2 : z ≠ ι j := fun h => hz ⟨j, h.symm⟩
    show (0 : ZMod 2) = pairVec (ι i) (ι j) z
    simp [pairVec, h1, h2]

theorem pairVec_mem_sup {δ : Finset (Fin 8)} (h : δ.card = 4) {x y : Fin 8} (hx : x ∈ δ)
    (hy : y ∈ δ) (hxy : x ≠ y) : ofVec (pairVec x y) ∈ memAt δ h true ⊔ memAt δ h false := by
  set ι := emb δ h
  have hι : Set.range ι = (δ : Set (Fin 8)) := range_emb δ h
  obtain ⟨i, rfl⟩ : ∃ i, ι i = x := by
    have : x ∈ Set.range ι := by rw [hι]; exact hx
    exact this
  obtain ⟨j, rfl⟩ : ∃ j, ι j = y := by
    have : y ∈ Set.range ι := by rw [hι]; exact hy
    exact this
  have hij : i ≠ j := fun h => hxy (by rw [h])
  obtain ⟨k, hk, k', hk', hkk⟩ := local_pair i j hij
  rw [← embed_ofVec_vec4 ι hij, ← hkk, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨k, hk, rfl⟩)
    (Subgroup.mem_sup_right ⟨k', hk', rfl⟩)

theorem ofVec_mem_of_pairs {H : Subgroup (Wr 8)}
    (hH : ∀ x y : Fin 8, x ≠ y → ofVec (pairVec x y) ∈ H) :
    ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → ofVec v ∈ H := by
  classical
  suffices key : ∀ m : ℕ, ∀ v : Fin 8 → ZMod 2,
      (Finset.univ.filter fun i => v i ≠ 0).card = m → ∑ i, v i = 0 → ofVec v ∈ H from
    fun v hv => key _ v rfl hv
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro v hm hv
    by_cases h0 : ∀ i, v i = 0
    · have : v = 0 := funext h0
      rw [this]
      exact H.one_mem
    · push Not at h0
      obtain ⟨x, hx⟩ := h0
      have hx1 : v x = 1 := (zmod2_eq_zero_or_one (v x)).resolve_left hx
      obtain ⟨y, hyx, hy⟩ : ∃ y, y ≠ x ∧ v y ≠ 0 := by
        by_contra hno
        push Not at hno
        have hsum : ∑ i, v i = v x := Finset.sum_eq_single x (fun b _ hb => hno b hb)
          (fun h => absurd (Finset.mem_univ x) h)
        rw [hv, hx1] at hsum
        exact absurd hsum (by decide)
      have hy1 : v y = 1 := (zmod2_eq_zero_or_one (v y)).resolve_left hy
      have hxy : x ≠ y := Ne.symm hyx
      set v' : Fin 8 → ZMod 2 := v + pairVec x y with hv'
      have hpp : pairVec x y + pairVec x y = 0 := funext fun z => zmod_two_add_self _
      have hvv : v = v' + pairVec x y := by
        rw [hv', add_assoc, hpp, add_zero]
      have hpsum : ∑ i, pairVec x y i = 0 := by
        simp only [pairVec, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact zmod_two_add_self _
      have hsum' : ∑ i, v' i = 0 := by
        rw [hv']
        simp only [Pi.add_apply]
        rw [Finset.sum_add_distrib, hv, hpsum, add_zero]
      have hpx : pairVec x y x = 1 := by simp [pairVec, hxy]
      have hpy : pairVec x y y = 1 := by simp [pairVec, hyx]
      have hpz : ∀ z, z ≠ x → z ≠ y → pairVec x y z = 0 := fun z h1 h2 => by
        simp [pairVec, h1, h2]
      have hsub : (Finset.univ.filter fun i => v' i ≠ 0) ⊂
          (Finset.univ.filter fun i => v i ≠ 0) := by
        refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨x, ?_, ?_⟩
        · intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
          intro hvz
          by_cases hzx : z = x
          · rw [hzx, hx1] at hvz
            exact absurd hvz (by decide)
          · by_cases hzy : z = y
            · rw [hzy, hy1] at hvz
              exact absurd hvz (by decide)
            · apply hz
              rw [hv', Pi.add_apply, hvz, hpz z hzx hzy, add_zero]
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hx
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
          rw [hv', Pi.add_apply, hx1, hpx]
          exact zmod_two_add_self _
      have hlt := Finset.card_lt_card hsub
      rw [hm] at hlt
      have h1 := ih _ hlt v' rfl hsum'
      rw [hvv, ← ofVec_mul_ofVec]
      exact H.mul_mem h1 (hH x y hxy)

theorem memAt_le_aeSub8 (δ : Finset (Fin 8)) (h : δ.card = 4) (c : Bool) :
    memAt δ h c ≤ aeSub 8 := by
  cases c
  · exact memKStar_le_aeSub _
  · exact memK_le_aeSub _

end Members

section Conj

theorem natCard_conjSub {G : Type*} [Group G] (g : G) (H : Subgroup G) :
    Nat.card (conjSub g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem ofPerm_conj_embed₂ {ι κ : Fin 4 ↪ Fin 8} {σ : Equiv.Perm (Fin 8)}
    {c : Equiv.Perm (Fin 4)} (hσ : ∀ i, σ (ι i) = κ (c i)) (a : Wr 4) :
    ofPerm σ * embed ι a * (ofPerm σ)⁻¹ = embed κ (ofPerm c * a * (ofPerm c)⁻¹) := by
  classical
  have hsymm : ∀ i, σ.symm (κ i) = ι (c.symm i) := by
    intro i
    apply σ.injective
    rw [Equiv.apply_symm_apply, hσ, Equiv.apply_symm_apply]
  have hout : ∀ x, x ∉ Set.range κ → σ.symm x ∉ Set.range ι := by
    rintro x hx ⟨i, hi⟩
    apply hx
    refine ⟨c i, ?_⟩
    rw [← hσ, hi, Equiv.apply_symm_apply]
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [ofPerm_conj_vec]
    by_cases hx : x ∈ Set.range κ
    · obtain ⟨i, rfl⟩ := hx
      rw [hsymm, embed_vec, embed_vec, embedVec_apply, embedVec_apply, ofPerm_conj_vec]
    · rw [embed_vec_of_not_mem ι _ (hout x hx), embed_vec_of_not_mem κ _ hx]
  · rw [ofPerm_conj_perm]
    show σ ((embed ι a).perm (σ⁻¹ x)) = (embed κ (ofPerm c * a * (ofPerm c)⁻¹)).perm x
    by_cases hx : x ∈ Set.range κ
    · obtain ⟨i, rfl⟩ := hx
      rw [Equiv.Perm.inv_def, hsymm, embed_perm, embed_perm, embedPerm_apply, embedPerm_apply,
        hσ, ofPerm_conj_perm]
      rfl
    · rw [Equiv.Perm.inv_def, embed_perm_of_not_mem ι _ (hout x hx), Equiv.apply_symm_apply,
        embed_perm_of_not_mem κ _ hx]

theorem conj_kList_cases : ∀ c : Equiv.Perm (Fin 4),
    (∀ k ∈ kList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kList) ∨
      (∀ k ∈ kList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kStarList) := by
  decide +kernel

theorem conj_kStarList_cases : ∀ c : Equiv.Perm (Fin 4),
    (∀ k ∈ kStarList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kStarList) ∨
      (∀ k ∈ kStarList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kList) := by
  decide +kernel

theorem card_map_perm (σ : Equiv.Perm (Fin 8)) {δ : Finset (Fin 8)} (h : δ.card = 4) :
    (δ.map σ.toEmbedding).card = 4 :=
  (Finset.card_map _).trans h

theorem conjSub_ofPerm_memBar (σ : Equiv.Perm (Fin 8)) {δ : Finset (Fin 8)} (h : δ.card = 4)
    (c : Bool) : ∃ c' : Bool, conjSub (mkQ 8 (ofPerm σ)) (memBar δ h c) =
      memBar (δ.map σ.toEmbedding) (card_map_perm σ h) c' := by
  classical
  set h' := card_map_perm σ h
  set ι := emb δ h with hι
  set κ := emb (δ.map σ.toEmbedding) h' with hκ
  have hmap : ∀ i, σ (ι i) ∈ Set.range κ := fun i => by
    rw [hκ, range_emb]
    have hi : ι i ∈ δ := by
      have := Set.mem_range_self (f := ι) i
      rwa [hι, range_emb] at this
    exact Finset.mem_map_of_mem _ hi
  choose f hf using hmap
  have hfinj : Function.Injective f := fun i j hij => by
    have h1 : σ (ι i) = σ (ι j) := by rw [← hf i, ← hf j, hij]
    exact ι.injective (σ.injective h1)
  set ρ := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  have hσ : ∀ i, σ (ι i) = κ (ρ i) := fun i => (hf i).symm
  obtain ⟨c', hc'⟩ : ∃ c' : Bool, ∀ k ∈ (bif c then kList else kStarList),
      ofPerm ρ * k * (ofPerm ρ)⁻¹ ∈ (bif c' then kList else kStarList) := by
    cases c
    · rcases conj_kStarList_cases ρ with h1 | h1
      · exact ⟨false, h1⟩
      · exact ⟨true, h1⟩
    · rcases conj_kList_cases ρ with h1 | h1
      · exact ⟨true, h1⟩
      · exact ⟨false, h1⟩
  refine ⟨c', ?_⟩
  have hle : conjSub (mkQ 8 (ofPerm σ)) (memBar δ h c) ≤ memBar (δ.map σ.toEmbedding) h' c' := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨k, hk, rfl⟩ : ∃ k ∈ (bif c then kList else kStarList), a = embed ι k := by
      cases c
      · obtain ⟨k, hk, rfl⟩ := ha
        exact ⟨k, hk, rfl⟩
      · obtain ⟨k, hk, rfl⟩ := ha
        exact ⟨k, hk, rfl⟩
    refine ⟨ofPerm σ * embed ι k * (ofPerm σ)⁻¹, ?_, ?_⟩
    · rw [ofPerm_conj_embed₂ hσ]
      have hk' := hc' k hk
      cases c'
      · exact ⟨_, hk', rfl⟩
      · exact ⟨_, hk', rfl⟩
    · show mkQ 8 (ofPerm σ * embed ι k * (ofPerm σ)⁻¹) =
        mkQ 8 (ofPerm σ) * mkQ 8 (embed ι k) * (mkQ 8 (ofPerm σ))⁻¹
      rw [map_mul, map_mul, map_inv]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [natCard_memBar (by norm_num) _ h' c', natCard_conjSub, natCard_memBar (by norm_num) δ h c]

theorem ofPerm_conj_ofVec (σ : Equiv.Perm (Fin 8)) (v : Fin 8 → ZMod 2) :
    ofPerm σ * ofVec v * (ofPerm σ)⁻¹ = ofVec fun x => v (σ.symm x) := by
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [ofPerm_conj_vec]
    rfl
  · rw [ofPerm_conj_perm]
    show σ * 1 * σ⁻¹ = 1
    rw [mul_one, mul_inv_cancel]

theorem parInd_comp_symm (σ : Equiv.Perm (Fin 8)) (δ : Finset (Fin 8)) :
    (fun x => parInd δ (σ.symm x)) = parInd (δ.map σ.toEmbedding) := by
  funext x
  simp only [parInd, Finset.mem_map_equiv]

theorem ofPerm_conj_zBar (σ : Equiv.Perm (Fin 8)) {δ : Finset (Fin 8)} (h : δ.card = 4) :
    mkQ 8 (ofPerm σ) * zBar δ h * (mkQ 8 (ofPerm σ))⁻¹ =
      zBar (δ.map σ.toEmbedding) (card_map_perm σ h) := by
  rw [zBar_eq_mk, zBar_eq_mk, ← map_inv, ← map_mul, ← map_mul, ofPerm_conj_ofVec,
    parInd_comp_symm]

theorem ofPerm_conj_mem_aeSub (σ : Equiv.Perm (Fin 8)) {a : Wr 8} (ha : a ∈ aeSub 8) :
    ofPerm σ * a * (ofPerm σ)⁻¹ ∈ aeSub 8 := by
  refine mem_aeSub.mpr ⟨?_, ?_⟩
  · unfold wsum
    simp only [ofPerm_conj_vec]
    rw [sum_perm_apply]
    exact (mem_aeSub.mp ha).1
  · rw [ofPerm_conj_perm, map_mul, map_mul, map_inv, (mem_aeSub.mp ha).2, mul_one,
      mul_inv_cancel]

theorem ofPerm_inv (σ : Equiv.Perm (Fin 8)) : (ofPerm σ)⁻¹ = ofPerm σ⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [ofPerm_mul, mul_inv_cancel, ofPerm_one])

theorem mkQ_ofPerm_inv (σ : Equiv.Perm (Fin 8)) :
    (mkQ 8 (ofPerm σ))⁻¹ = mkQ 8 (ofPerm σ⁻¹) := by
  rw [← map_inv, ofPerm_inv]

theorem conjSub_ofPerm_ae6AE8_le (σ : Equiv.Perm (Fin 8)) :
    conjSub (mkQ 8 (ofPerm σ)) ae6AE8 ≤ ae6AE8 := by
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  refine ⟨ofPerm σ * a * (ofPerm σ)⁻¹, ofPerm_conj_mem_aeSub σ ha, ?_⟩
  show mkQ 8 (ofPerm σ * a * (ofPerm σ)⁻¹) = mkQ 8 (ofPerm σ) * mkQ 8 a * (mkQ 8 (ofPerm σ))⁻¹
  rw [map_mul, map_mul, map_inv]

theorem conjSub_ofPerm_ae6AE8 (σ : Equiv.Perm (Fin 8)) :
    conjSub (mkQ 8 (ofPerm σ)) ae6AE8 = ae6AE8 := by
  refine le_antisymm (conjSub_ofPerm_ae6AE8_le σ) ?_
  calc ae6AE8 = conjSub (mkQ 8 (ofPerm σ)) (conjSub (mkQ 8 (ofPerm σ))⁻¹ ae6AE8) :=
        (conjSub_conjSub_inv _ _).symm
    _ ≤ conjSub (mkQ 8 (ofPerm σ)) ae6AE8 := by
        apply conjSub_mono
        rw [mkQ_ofPerm_inv]
        exact conjSub_ofPerm_ae6AE8_le σ⁻¹

end Conj

section Transport

theorem ae6ParM_le {a b : AEQ 8} {X : Subgroup (AEQ 8)}
    (hX : ∀ (δ : Finset (Fin 8)) (h : δ.card = 4) (c : Bool),
      (zBar δ h = a ∨ zBar δ h = b ∨ zBar δ h = a * b) → memBar δ h c ≤ X) :
    ae6ParM a b ≤ X :=
  iSup_le fun δ => iSup_le fun h => iSup_le fun c => iSup_le fun hz => hX δ h c hz

theorem memBar_le_ae6ParM {a b : AEQ 8} {δ : Finset (Fin 8)} (h : δ.card = 4) (c : Bool)
    (hz : zBar δ h = a ∨ zBar δ h = b ∨ zBar δ h = a * b) : memBar δ h c ≤ ae6ParM a b :=
  le_iSup_of_le δ (le_iSup_of_le h (le_iSup_of_le c (le_iSup_of_le hz le_rfl)))

theorem conjSub_ofPerm_ae6ParM_le (σ : Equiv.Perm (Fin 8)) (a b : AEQ 8) :
    conjSub (mkQ 8 (ofPerm σ)) (ae6ParM a b) ≤
      ae6ParM (mkQ 8 (ofPerm σ) * a * (mkQ 8 (ofPerm σ))⁻¹)
        (mkQ 8 (ofPerm σ) * b * (mkQ 8 (ofPerm σ))⁻¹) := by
  refine Subgroup.map_le_iff_le_comap.mpr (ae6ParM_le fun δ h c hz => ?_)
  refine Subgroup.map_le_iff_le_comap.mp ?_
  obtain ⟨c', hc'⟩ := conjSub_ofPerm_memBar σ h c
  refine (le_of_eq hc').trans (memBar_le_ae6ParM _ c' ?_)
  rw [← ofPerm_conj_zBar σ h]
  rcases hz with hz | hz | hz
  · exact Or.inl (by rw [hz])
  · exact Or.inr (Or.inl (by rw [hz]))
  · exact Or.inr (Or.inr (by rw [hz]; group))

theorem conjSub_ofPerm_ae6ParM (σ : Equiv.Perm (Fin 8)) (a b : AEQ 8) :
    conjSub (mkQ 8 (ofPerm σ)) (ae6ParM a b) =
      ae6ParM (mkQ 8 (ofPerm σ) * a * (mkQ 8 (ofPerm σ))⁻¹)
        (mkQ 8 (ofPerm σ) * b * (mkQ 8 (ofPerm σ))⁻¹) := by
  refine le_antisymm (conjSub_ofPerm_ae6ParM_le σ a b) ?_
  have h1 := conjSub_ofPerm_ae6ParM_le σ⁻¹ (mkQ 8 (ofPerm σ) * a * (mkQ 8 (ofPerm σ))⁻¹)
    (mkQ 8 (ofPerm σ) * b * (mkQ 8 (ofPerm σ))⁻¹)
  rw [← mkQ_ofPerm_inv] at h1
  have e : ∀ x : AEQ 8, (mkQ 8 (ofPerm σ))⁻¹ * (mkQ 8 (ofPerm σ) * x * (mkQ 8 (ofPerm σ))⁻¹) *
      (mkQ 8 (ofPerm σ))⁻¹⁻¹ = x := fun x => by group
  rw [e, e] at h1
  calc _ = conjSub (mkQ 8 (ofPerm σ)) (conjSub (mkQ 8 (ofPerm σ))⁻¹
        (ae6ParM (mkQ 8 (ofPerm σ) * a * (mkQ 8 (ofPerm σ))⁻¹)
          (mkQ 8 (ofPerm σ) * b * (mkQ 8 (ofPerm σ))⁻¹))) := (conjSub_conjSub_inv _ _).symm
    _ ≤ _ := conjSub_mono h1

theorem ae6ParFacts_conj {𝔐 : Subgroup (AEQ 8)} (hF : AE6ParFacts 𝔐) (σ : Equiv.Perm (Fin 8)) :
    AE6ParFacts (conjSub (mkQ 8 (ofPerm σ)) 𝔐) := by
  set g := mkQ 8 (ofPerm σ) with hg
  have hginv : g⁻¹ = mkQ 8 (ofPerm σ⁻¹) := mkQ_ofPerm_inv σ
  have hE : conjSub g ae6AE8 = ae6AE8 := conjSub_ofPerm_ae6AE8 σ
  have hE' : conjSub g⁻¹ ae6AE8 = ae6AE8 := by
    rw [hginv]
    exact conjSub_ofPerm_ae6AE8 σ⁻¹
  have hpull : ∀ X : Subgroup (AEQ 8), conjSub g 𝔐 ≤ X → X ≤ ae6AE8 →
      𝔐 ≤ conjSub g⁻¹ X ∧ conjSub g⁻¹ X ≤ ae6AE8 := by
    intro X h1 h2
    refine ⟨?_, ?_⟩
    · calc 𝔐 = conjSub g⁻¹ (conjSub g 𝔐) := (conjSub_inv_conjSub _ _).symm
        _ ≤ conjSub g⁻¹ X := conjSub_mono h1
    · calc conjSub g⁻¹ X ≤ conjSub g⁻¹ ae6AE8 := conjSub_mono h2
        _ = ae6AE8 := hE'
  refine ⟨?_, ?_, ?_⟩
  · rw [natCard_conjSub, hF.card]
  · intro X h1 h2
    obtain ⟨h1', h2'⟩ := hpull X h1 h2
    rcases hF.overg _ h1' h2' with h | h | h
    · left
      rw [← h, conjSub_conjSub_inv]
    · right; left
      rw [← conjSub_conjSub_inv g X, h, hE]
    · right; right
      rw [← natCard_conjSub g⁻¹ X, h]
  · intro X h1 h2 hX δ δ' h h' c c' hδ hδ'
    obtain ⟨h1', h2'⟩ := hpull X h1 h2
    have hX' : Nat.card (conjSub g⁻¹ X) = 86016 := by rw [natCard_conjSub, hX]
    obtain ⟨c₁, hc₁⟩ := conjSub_ofPerm_memBar σ⁻¹ h c
    obtain ⟨c₁', hc₁'⟩ := conjSub_ofPerm_memBar σ⁻¹ h' c'
    rw [← hginv] at hc₁ hc₁'
    obtain ⟨e, he, hee⟩ := hF.orbit _ h1' h2' hX' _ _ _ _ c₁ c₁'
      (by rw [← hc₁]; exact conjSub_mono hδ) (by rw [← hc₁']; exact conjSub_mono hδ')
    refine ⟨g * e * g⁻¹, ?_, ?_⟩
    · have := mem_conjSub_iff.mp he
      rwa [inv_inv] at this
    · rw [conjSub_mul, conjSub_mul, hc₁, hee, ← hc₁', conjSub_conjSub_inv]

end Transport

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
