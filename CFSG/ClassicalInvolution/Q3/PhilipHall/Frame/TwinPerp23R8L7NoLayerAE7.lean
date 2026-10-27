module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7NoLayerBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

section Support

variable {n : ℕ}

@[expose] def suppSub (n : ℕ) (s : Set (Fin n)) : Subgroup (Wr n) where
  carrier := {a | SupportedOn a s}
  mul_mem' {a b} ha hb := SupportedOn.mul ha hb
  one_mem' := supportedOn_one s
  inv_mem' {a} ha := SupportedOn.inv ha

theorem memAt_le_aeSub (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) : memAt α h b ≤ aeSub n := by
  cases b
  · exact memKStar_le_aeSub _
  · exact memK_le_aeSub _

theorem memBar_le_centralizer {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} {a : AEQ n}
    (hc : ∀ x ∈ memBar α h b, a * x = x * a) :
    memBar α h b ≤ Subgroup.centralizer ({a} : Set (AEQ n)) := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (hc x hx).symm

theorem ofPerm_supportedOn {σ : Equiv.Perm (Fin n)} {s : Set (Fin n)} (hσ : ∀ x ∉ s, σ x = x) :
    SupportedOn (ofPerm σ) s := fun x hx => ⟨rfl, hσ x hx⟩

end Support

section Weight2

theorem not_mem_Ea_of_weight_two {w : Wr 7} (hw : w ∈ aeSub 7) (hperm : w.perm = 1) {T : Finset (Fin 7)}
    (hT : ∀ x, w.vec x = if x ∈ T then 1 else 0) (h2 : T.card = 2) :
    mkQ 7 w ∉ Ea (aeMembers 7 Set.univ) (mkQ 7 w) := by
  have hle : Ea (aeMembers 7 Set.univ) (mkQ 7 w) ≤
      (aeSub 7 ⊓ suppSub 7 ((Tᶜ : Finset (Fin 7)) : Set (Fin 7))).map (mkQ 7) := by
    refine Ea_le fun M hM hMc => ?_
    obtain ⟨γ, -, hγc, b, rfl⟩ := hM
    have cγ := const_of_le_centralizer (by norm_num : 5 ≤ 7) hperm hMc
    have hγT : ∀ x ∈ γ, x ∉ T := by
      intro x hxγ hxT
      have hsub : γ ⊆ T := by
        intro y hy
        have h1 := cγ x hxγ y hy
        rw [hT x, if_pos hxT, hT y] at h1
        by_contra hyT
        rw [if_neg hyT] at h1
        exact absurd h1 (by decide)
      have := Finset.card_le_card hsub
      omega
    refine Subgroup.map_mono ?_
    intro m hm
    refine ⟨memAt_le_aeSub γ hγc b hm, ?_⟩
    have hs := supportedOn_of_mem_memAt hm
    rw [range_emb] at hs
    intro x hx
    refine hs x fun hxγ => hx ?_
    simpa using hγT x hxγ
  intro hmem
  obtain ⟨m, ⟨hmae, hmsupp⟩, hmq⟩ := hle hmem
  rcases mkQ_eq_iff.mp hmq with h1 | h1
  · have hmw : m = w := inv_mul_eq_one.mp h1
    subst hmw
    obtain ⟨p, hp⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
    have h3 := (hmsupp p (by simpa using hp)).1
    rw [hT p, if_pos hp] at h3
    exact absurd h3 (by decide)
  · have hw' : w = m * allOnes 7 := by
      calc w = m * (m⁻¹ * w) := by group
        _ = m * allOnes 7 := by rw [h1]
    have h4 : wsum w = 1 := by
      rw [hw', wsum_mul, hmae.1, zero_add]
      decide
    rw [hw.1] at h4
    exact absurd h4 (by decide)

end Weight2

section Layers

theorem layer_weight_six {w : Wr 7} (hw : w ∈ aeSub 7) (hL : ModelLayer 7 Set.univ (mkQ 7 w)) :
    w.perm = 1 ∧ ∃ p : Fin 7, ∀ x, w.vec x = if x = p then 0 else 1 := by
  obtain ⟨hne, -, hmem, hns⟩ := hL
  obtain ⟨α, -, α', -, hαα', hα, hα'⟩ := exists_pair_of_not_isSolvable hns
  have hperm : w.perm = 1 := perm_eq_one_of_pair (by norm_num) hw.2 hα hα' hαα'
  obtain ⟨hcard, c, hconst⟩ := exists_level_set (by norm_num) (by norm_num) hperm hα hα' hαα'
  obtain ⟨T, hT, ⟨m, hm⟩, hdich⟩ := weight_dichotomy hconst hw.1
  have hTle : T.card ≤ 7 := by
    have := Finset.card_le_univ T
    rwa [Fintype.card_fin] at this
  have hcases : T.card = 0 ∨ T.card = 2 ∨ T.card = 6 := by omega
  refine ⟨hperm, ?_⟩
  rcases hcases with h0 | h2 | h6
  · exact absurd (by rw [eq_one_of_weight_zero hperm hT h0, map_one]) hne
  · exact absurd hmem (not_mem_Ea_of_weight_two hw hperm hT h2)
  · have hc1 : Tᶜ.card = 1 := by rw [Finset.card_compl, Fintype.card_fin, h6]
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc1
    refine ⟨p, fun x => ?_⟩
    rw [hT x]
    by_cases hxp : x = p
    · subst hxp
      have hx : x ∈ Tᶜ := by rw [hp]; exact Finset.mem_singleton_self x
      have hxT : x ∉ T := Finset.mem_compl.mp hx
      simp [hxT]
    · have hxT : x ∈ T := by
        by_contra hxT
        have hx : x ∈ Tᶜ := Finset.mem_compl.mpr hxT
        rw [hp] at hx
        exact hxp (Finset.mem_singleton.mp hx)
      simp [hxT, hxp]

theorem not_mem_of_layer_cen {w : Wr 7} (hperm : w.perm = 1) {p : Fin 7}
    (hv : ∀ x, w.vec x = if x = p then 0 else 1) {α : Finset (Fin 7)} (h : α.card = 4)
    (hc : ∀ x ∈ memBar α h true, mkQ 7 w * x = x * mkQ 7 w) : p ∉ α := by
  intro hpα
  have cα := const_of_le_centralizer (by norm_num : 5 ≤ 7) hperm (memBar_le_centralizer hc)
  obtain ⟨y, hyα, hyp⟩ := Finset.exists_mem_ne (by omega : 1 < α.card) p
  have h1 := cα p hpα y hyα
  rw [hv p, hv y, if_pos rfl, if_neg hyp] at h1
  exact absurd h1 (by decide)

theorem ae7LayerOrbit_proved : AE7LayerOrbit := by
  intro α h a₁ a₂ ha₁ ha₂ hL₁ hL₂ hc₁ hc₂
  obtain ⟨w₁, hw₁, rfl⟩ := ha₁
  obtain ⟨w₂, hw₂, rfl⟩ := ha₂
  obtain ⟨hp₁, p, hv₁⟩ := layer_weight_six hw₁ hL₁
  obtain ⟨hp₂, q, hv₂⟩ := layer_weight_six hw₂ hL₂
  have hpα : p ∉ α := not_mem_of_layer_cen hp₁ hv₁ h (hc₁ true)
  have hqα : q ∉ α := not_mem_of_layer_cen hp₂ hv₂ h (hc₂ true)
  by_cases hpq : p = q
  · subst hpq
    have hww : w₁ = w₂ := Wr.ext (funext fun x => by rw [hv₁ x, hv₂ x]) (hp₁.trans hp₂.symm)
    refine ⟨1, Subgroup.one_mem _, by rw [orderOf_one]; exact odd_one,
      fun b x _ => by rw [one_mul, mul_one], ?_⟩
    rw [hww, inv_one, one_mul, mul_one]
  · have hαc : αᶜ.card = 3 := by rw [Finset.card_compl, Fintype.card_fin, h]
    obtain ⟨r, hrα, hrpq⟩ : ∃ r ∈ αᶜ, r ∉ ({p, q} : Finset (Fin 7)) := by
      apply Finset.exists_mem_notMem_of_card_lt_card
      rw [hαc, Finset.card_pair hpq]
      norm_num
    have hrp : r ≠ p := fun e => hrpq (by simp [e])
    have hrq : r ≠ q := fun e => hrpq (by simp [e])
    have hrα' : r ∉ α := Finset.mem_compl.mp hrα
    obtain ⟨c, hc⟩ : ∃ c : Equiv.Perm (Fin 7), c = Equiv.swap p q * Equiv.swap q r := ⟨_, rfl⟩
    have hcp : c p = q := by
      rw [hc, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpq hrp.symm, Equiv.swap_apply_left]
    have hsign : Equiv.Perm.sign c = 1 := by
      rw [hc, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hpq, Equiv.Perm.sign_swap hrq.symm]
      decide
    have hc3 : c ^ 3 = 1 := by
      have key : ∀ x y z : Fin 7, x ≠ y → y ≠ z → x ≠ z →
          (Equiv.swap x y * Equiv.swap y z) ^ 3 = 1 := by decide +kernel
      rw [hc]
      exact key p q r hpq hrq.symm hrp.symm
    have hmem : mkQ 7 (ofPerm c) ∈ (aeSub 7).map (mkQ 7) :=
      ⟨ofPerm c, ⟨by unfold wsum; exact Finset.sum_eq_zero fun _ _ => rfl, hsign⟩, rfl⟩
    have hodd : Odd (orderOf (mkQ 7 (ofPerm c))) := by
      have h3 : (mkQ 7 (ofPerm c)) ^ 3 = 1 := by
        rw [← map_pow, ofPerm_pow, hc3, ofPerm_one, map_one]
      exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)
    have hcomm : ∀ (b : Bool), ∀ x ∈ AE.memBar α h b,
        mkQ 7 (ofPerm c) * x = x * mkQ 7 (ofPerm c) := by
      rintro b _ ⟨m, hm, rfl⟩
      have hs := supportedOn_of_mem_memAt hm
      have hcs : SupportedOn (ofPerm c) (↑({p, q, r} : Finset (Fin 7)) : Set (Fin 7)) := by
        refine ofPerm_supportedOn fun x hx => ?_
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] at hx
        rw [hc, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx.2.1 hx.2.2,
          Equiv.swap_apply_of_ne_of_ne hx.1 hx.2.1]
      have hdisj : Disjoint (Set.range (emb α h)) (↑({p, q, r} : Finset (Fin 7)) : Set (Fin 7)) := by
        rw [range_emb, Set.disjoint_left]
        intro x hxα hxs
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hxs
        rcases hxs with rfl | rfl | rfl
        · exact hpα hxα
        · exact hqα hxα
        · exact hrα' hxα
      rw [← map_mul, ← map_mul, comm_of_disjoint hcs hs hdisj.symm]
    have hconj : mkQ 7 (ofPerm c) * mkQ 7 w₁ * (mkQ 7 (ofPerm c))⁻¹ = mkQ 7 w₂ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      refine Wr.ext (funext fun x => ?_) ?_
      · rw [ofPerm_conj_vec, hv₁ (c.symm x), hv₂ x]
        have hiff : c.symm x = p ↔ x = q := by rw [Equiv.symm_apply_eq, hcp]
        by_cases hxq : x = q
        · rw [if_pos (hiff.mpr hxq), if_pos hxq]
        · rw [if_neg fun h' => hxq (hiff.mp h'), if_neg hxq]
      · rw [ofPerm_conj_perm, hp₁, hp₂, mul_one, mul_inv_cancel]
    exact ⟨mkQ 7 (ofPerm c), hmem, hodd, hcomm, hconj⟩

end Layers

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
