module

public import CFSG.ClassicalInvolution.Q3.AE.Bar
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Model
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14Ae5Model
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AWM

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20

section Model

theorem perm_eq_one_of_fix_four {α : Finset (Fin 7)} (hα : α.card = 4) (σ : Equiv.Perm (Fin 7))
    (hfix : ∀ i ∈ α, σ i = i) (hsq : σ * σ = 1) (hsg : Equiv.Perm.sign σ = 1) : σ = 1 := by
  classical
  by_contra hne
  have hsq' : ∀ p, σ (σ p) = p := fun p => by
    have := congrArg (fun f : Equiv.Perm (Fin 7) => f p) hsq
    simpa using this
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hall
    exact hne (Equiv.ext fun x => by by_contra hx; exact hall ⟨x, hx⟩)
  have hout : ∀ p, σ p ≠ p → p ∉ α := fun p hp hpα => hp (hfix p hpα)
  have hout' : ∀ p, σ p ≠ p → σ p ∉ α := by
    intro p hp hpα
    have h1 := hfix _ hpα
    rw [hsq'] at h1
    exact hp h1.symm
  obtain ⟨y, hy⟩ : ∃ y, σ x = y := ⟨_, rfl⟩
  have hxy : x ≠ y := fun h => hx (hy.trans h.symm)
  have hyx : σ y = x := by rw [← hy, hsq']
  have hc : αᶜ.card = 3 := by rw [Finset.card_compl, Fintype.card_fin, hα]
  have hxc : x ∈ αᶜ := Finset.mem_compl.mpr (hout x hx)
  have hyc : y ∈ αᶜ := Finset.mem_compl.mpr (hy ▸ hout' x hx)
  have hlt : ({x, y} : Finset (Fin 7)).card < αᶜ.card := by
    rw [hc]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
  obtain ⟨r, hrc, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  obtain ⟨hrx, hry⟩ := hr
  have hrα : r ∉ α := Finset.mem_compl.mp hrc
  have hσr : σ r = r := by
    by_contra hne'
    have h1 : σ r ∉ α := hout' r hne'
    have h2 : σ r ≠ x := fun h => hry (by rw [← hsq' r, h, hy])
    have h3 : σ r ≠ y := fun h => hrx (σ.injective (by rw [h, hy]))
    have hsub : ({x, y, r, σ r} : Finset (Fin 7)) ⊆ αᶜ := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact hxc
      · exact hyc
      · exact hrc
      · exact Finset.mem_compl.mpr h1
    have n1 : x ∉ ({y, r, σ r} : Finset (Fin 7)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, Ne.symm hrx, Ne.symm h2⟩
    have n2 : y ∉ ({r, σ r} : Finset (Fin 7)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hry, Ne.symm h3⟩
    have hcard : ({x, y, r, σ r} : Finset (Fin 7)).card = 4 := by
      rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
        Finset.card_pair (fun h => hne' h.symm)]
    have := Finset.card_le_card hsub
    rw [hcard, hc] at this
    omega
  have hall : ∀ p, p ∉ α → p = x ∨ p = y ∨ p = r := by
    intro p hp
    have hsub : ({x, y, r} : Finset (Fin 7)) ⊆ αᶜ := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact hxc
      · exact hyc
      · exact hrc
    have n1 : y ∉ ({r} : Finset (Fin 7)) := by
      simp only [Finset.mem_singleton]
      exact Ne.symm hry
    have n0 : x ∉ ({y, r} : Finset (Fin 7)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, Ne.symm hrx⟩
    have hcard : ({x, y, r} : Finset (Fin 7)).card = 3 := by
      rw [Finset.card_insert_of_notMem n0, Finset.card_insert_of_notMem n1, Finset.card_singleton]
    have heq : ({x, y, r} : Finset (Fin 7)) = αᶜ :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hc])
    have : p ∈ αᶜ := Finset.mem_compl.mpr hp
    rw [← heq] at this
    simpa using this
  have hσ : σ = Equiv.swap x y := by
    refine Equiv.ext fun p => ?_
    by_cases hpα : p ∈ α
    · rw [hfix p hpα, Equiv.swap_apply_of_ne_of_ne]
      · exact fun h => hout x hx (h ▸ hpα)
      · exact fun h => hout' x hx (hy ▸ h ▸ hpα)
    · rcases hall p hpα with rfl | rfl | rfl
      · rw [Equiv.swap_apply_left, hy]
      · rw [Equiv.swap_apply_right, hyx]
      · rw [hσr, Equiv.swap_apply_of_ne_of_ne hrx hry]
  rw [hσ, Equiv.Perm.sign_swap hxy] at hsg
  exact absurd hsg (by decide)

theorem allOnes_not_mem_aeSub : allOnes 7 ∉ aeSub 7 := by
  intro h
  have h1 : wsum (allOnes 7) = 0 := h.1
  have h2 : wsum (allOnes 7) = 1 := by decide
  rw [h2] at h1
  exact absurd h1 (by decide)

theorem eq_one_of_mul_self_mkQ {a : Wr 7} (ha : a ∈ aeSub 7) (h : mkQ 7 a * mkQ 7 a = 1) :
    a * a = 1 := by
  have h1 : mkQ 7 (a * a) = 1 := by rw [map_mul]; exact h
  rcases (QuotientGroup.eq_one_iff (a * a)).mp h1 with h2 | h2
  · exact h2
  · exact absurd (h2 ▸ (aeSub 7).mul_mem ha ha) allOnes_not_mem_aeSub

theorem exists_three_elt_moving (α : Finset (Fin 7)) (hα : α.card = 4) {ε : AEQ 7}
    (hε : ε ∈ (aeSub 7).map (mkQ 7)) (hε2 : ε * ε = 1) (hε1 : ε ≠ 1) (hεz : ε ≠ zBar α hα)
    (hc : ∀ b : Bool, ∀ x ∈ memBar α hα b, ε * x = x * ε) :
    ∃ w : AEQ 7, w ∈ (aeSub 7).map (mkQ 7) ∧ w ^ 3 = 1 ∧ w * zBar α hα = zBar α hα * w ∧
      w * ε * w⁻¹ * ε⁻¹ ≠ 1 ∧ (w * ε * w⁻¹ * ε⁻¹) * (w * ε * w⁻¹ * ε⁻¹) = 1 := by
  classical
  obtain ⟨a, ha, rfl⟩ := hε
  have haa : a * a = 1 := eq_one_of_mul_self_mkQ ha hε2
  have hB : ∀ c : Bool, ∀ x ∈ memBar α hα c, mkQ 7 a * x * (mkQ 7 a)⁻¹ = x := by
    intro c x hx
    rw [hc c x hx]
    group
  have hfix := perm_fix_of_cent_memBar (by norm_num) α hα a hB
  have hperm : a.perm = 1 := by
    refine perm_eq_one_of_fix_four hα a.perm hfix ?_ ha.2
    rw [← mul_perm, haa, one_perm]
  have hav : a = ofVec a.vec := Wr.ext rfl hperm
  have hconst : ∀ x ∈ α, ∀ y ∈ α, a.vec x = a.vec y := by
    apply vec_const_of_cent_memBar (by norm_num) α hα true a.vec
    intro x hx
    rw [← hav]
    exact hc true x hx
  have hc3 : αᶜ.card = 3 := by rw [Finset.card_compl, Fintype.card_fin, hα]
  obtain ⟨r₁, r₂, r₃, h12, h13, h23, hαc⟩ := Finset.card_eq_three.mp hc3
  have hnα : ∀ x, x ∉ α ↔ x = r₁ ∨ x = r₂ ∨ x = r₃ := by
    intro x
    have : x ∈ αᶜ ↔ x ∈ ({r₁, r₂, r₃} : Finset (Fin 7)) := by rw [hαc]
    simpa using this
  have hr₁ : r₁ ∉ α := (hnα r₁).mpr (Or.inl rfl)
  have hr₂ : r₂ ∉ α := (hnα r₂).mpr (Or.inr (Or.inl rfl))
  have hr₃ : r₃ ∉ α := (hnα r₃).mpr (Or.inr (Or.inr rfl))
  obtain ⟨x₀, hx₀⟩ : α.Nonempty := Finset.card_pos.mp (by omega)
  have hsum : a.vec r₁ + (a.vec r₂ + a.vec r₃) = 0 := by
    have h1 : wsum a = 0 := ha.1
    unfold wsum at h1
    rw [← Finset.sum_add_sum_compl α a.vec, hαc] at h1
    have h2 : ∑ i ∈ α, a.vec i = 0 := by
      rw [Finset.sum_congr rfl (fun i hi => hconst i hi x₀ hx₀), Finset.sum_const, hα]
      generalize a.vec x₀ = c
      revert c
      decide
    rw [h2, zero_add, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton] at h1
    exact h1
  have hnc : ¬ (a.vec r₁ = a.vec r₂ ∧ a.vec r₂ = a.vec r₃) := by
    rintro ⟨e12, e23⟩
    have hz1 : a.vec r₁ = 0 := by
      rw [← e23, ← e12] at hsum
      generalize a.vec r₁ = c at hsum
      revert c
      decide
    have hvec0 : ∀ x ∉ α, a.vec x = 0 := by
      intro x hx
      rcases (hnα x).mp hx with rfl | rfl | rfl
      · exact hz1
      · rw [← e12]; exact hz1
      · rw [← e23, ← e12]; exact hz1
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (a.vec x₀) with h0 | h1
    · apply hε1
      have : a = 1 := by
        refine Wr.ext (funext fun x => ?_) hperm
        by_cases hx : x ∈ α
        · rw [hconst x hx x₀ hx₀, h0]; rfl
        · rw [hvec0 x hx]; rfl
      rw [this, map_one]
    · apply hεz
      have : a = zOf (emb α hα) := by
        refine Wr.ext (funext fun x => ?_) (hperm.trans (zOf_perm _).symm)
        have hmem : x ∈ Set.range (emb α hα) ↔ x ∈ α := by
          rw [range_emb]
          exact Finset.mem_coe
        rw [zOf_vec_apply]
        by_cases hx : x ∈ α
        · rw [if_pos (hmem.mpr hx), hconst x hx x₀ hx₀, h1]
        · rw [if_neg (fun h => hx (hmem.mp h)), hvec0 x hx]
      rw [this]
      rfl
  set ρ : Equiv.Perm (Fin 7) := threeCycle r₁ r₂ r₃ with hρ
  have hρmem : ofPerm ρ ∈ aeSub 7 := by
    refine ⟨?_, sign_threeCycle h12 h23⟩
    unfold wsum
    simp [ofPerm]
  have hρ3 : ρ ^ 3 = 1 := threeCycle_cubed h12 h23 h13
  have hρx : ∀ x ∈ α, ρ x = x := fun x hx =>
    threeCycle_of_ne (fun h => hr₁ (h ▸ hx)) (fun h => hr₂ (h ▸ hx)) (fun h => hr₃ (h ▸ hx))
  have hρs : ∀ x ∈ α, ρ.symm x = x := fun x hx => (Equiv.symm_apply_eq ρ).mpr (hρx x hx).symm
  have hρ1 : ρ.symm r₂ = r₁ := (Equiv.symm_apply_eq ρ).mpr (threeCycle_fst h12 h13).symm
  have hρ2 : ρ.symm r₃ = r₂ := (Equiv.symm_apply_eq ρ).mpr (threeCycle_snd h23 h13).symm
  refine ⟨mkQ 7 (ofPerm ρ), ⟨ofPerm ρ, hρmem, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ofPerm_pow, hρ3, ofPerm_one, map_one]
  ·
    have hsupp : SupportedOn (ofPerm ρ) ({r₁, r₂, r₃} : Set (Fin 7)) := by
      intro x hx
      refine ⟨rfl, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
      exact threeCycle_of_ne hx.1 hx.2.1 hx.2.2
    have hdisj : Disjoint ({r₁, r₂, r₃} : Set (Fin 7)) (Set.range (emb α hα)) := by
      rw [range_emb]
      refine Set.disjoint_left.mpr fun x hx hxα => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> contradiction
    have hcomm := comm_of_disjoint hsupp (zOf_supportedOn (emb α hα)) hdisj
    show mkQ 7 (ofPerm ρ) * mkQ 7 (zOf (emb α hα)) = mkQ 7 (zOf (emb α hα)) * mkQ 7 (ofPerm ρ)
    rw [← map_mul, ← map_mul, hcomm]
  ·
    have hb : (ofPerm ρ * a * (ofPerm ρ)⁻¹ * a⁻¹) =
        ofVec (fun x => a.vec (ρ.symm x) + a.vec x) := by
      have hp : (ofPerm ρ * a * (ofPerm ρ)⁻¹).perm = 1 := by
        rw [ofPerm_conj_perm, hperm]
        group
      refine Wr.ext (funext fun x => ?_) ?_
      · rw [mul_vec, ofPerm_conj_vec, hp]
        show a.vec (ρ.symm x) + a⁻¹.vec x = _
        rw [inv_vec, hperm]
        rfl
      · rw [mul_perm, hp, inv_perm, hperm]
        exact (by simp : (1 : Equiv.Perm (Fin 7)) * 1⁻¹ = 1)
    have hcomm : mkQ 7 (ofPerm ρ) * mkQ 7 a * (mkQ 7 (ofPerm ρ))⁻¹ * (mkQ 7 a)⁻¹ =
        mkQ 7 (ofVec (fun x => a.vec (ρ.symm x) + a.vec x)) := by
      rw [← hb]
      simp only [map_mul, map_inv]
    rw [hcomm]
    intro h1
    rcases (QuotientGroup.eq_one_iff _).mp h1 with h2 | h2
    ·
      have hv : ∀ x, a.vec (ρ.symm x) + a.vec x = 0 := fun x => by
        have := congrFun (congrArg Wr.vec h2) x
        exact this
      apply hnc
      have e1 := hv r₂
      have e2 := hv r₃
      rw [hρ1] at e1
      rw [hρ2] at e2
      constructor
      · generalize a.vec r₁ = u at e1 ⊢
        generalize a.vec r₂ = v at e1 ⊢
        revert u v
        decide
      · generalize a.vec r₂ = u at e2 ⊢
        generalize a.vec r₃ = v at e2 ⊢
        revert u v
        decide
    ·
      have h4 : a.vec (ρ.symm x₀) + a.vec x₀ = (allOnes 7).vec x₀ :=
        congrFun (congrArg Wr.vec h2) x₀
      have e3 : (allOnes 7).vec x₀ = 1 := rfl
      rw [e3, hρs x₀ hx₀] at h4
      generalize a.vec x₀ = u at h4
      revert u
      decide
  ·
    have hb : (ofPerm ρ * a * (ofPerm ρ)⁻¹ * a⁻¹) =
        ofVec (fun x => a.vec (ρ.symm x) + a.vec x) := by
      have hp : (ofPerm ρ * a * (ofPerm ρ)⁻¹).perm = 1 := by
        rw [ofPerm_conj_perm, hperm]
        group
      refine Wr.ext (funext fun x => ?_) ?_
      · rw [mul_vec, ofPerm_conj_vec, hp]
        show a.vec (ρ.symm x) + a⁻¹.vec x = _
        rw [inv_vec, hperm]
        rfl
      · rw [mul_perm, hp, inv_perm, hperm]
        exact (by simp : (1 : Equiv.Perm (Fin 7)) * 1⁻¹ = 1)
    have hcomm : mkQ 7 (ofPerm ρ) * mkQ 7 a * (mkQ 7 (ofPerm ρ))⁻¹ * (mkQ 7 a)⁻¹ =
        mkQ 7 (ofVec (fun x => a.vec (ρ.symm x) + a.vec x)) := by
      rw [← hb]
      simp only [map_mul, map_inv]
    rw [hcomm, ← map_mul]
    have : ofVec (fun x => a.vec (ρ.symm x) + a.vec x) *
        ofVec (fun x => a.vec (ρ.symm x) + a.vec x) = 1 := by
      refine Wr.ext (funext fun x => ?_) rfl
      show (a.vec (ρ.symm x) + a.vec x) + (a.vec (ρ.symm ((1 : Equiv.Perm (Fin 7)).symm x)) +
        a.vec ((1 : Equiv.Perm (Fin 7)).symm x)) = 0
      exact zmod_two_add_self _
    rw [this, map_one]

theorem eq_of_mkQ_eq_of_mem_aeSub {a b : Wr 7} (ha : a ∈ aeSub 7) (hb : b ∈ aeSub 7)
    (h : mkQ 7 a = mkQ 7 b) : a = b := by
  rcases mkQ_eq_iff.mp h with h1 | h1
  · exact inv_mul_eq_one.mp h1
  · exact absurd (h1 ▸ (aeSub 7).mul_mem ((aeSub 7).inv_mem ha) hb) allOnes_not_mem_aeSub

theorem mem_aeSub_of_mem_memAt {n : ℕ} {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} {a : Wr n}
    (ha : a ∈ memAt α h b) : a ∈ aeSub n := by
  cases b
  · exact memKStar_le_aeSub _ ha
  · exact memK_le_aeSub _ ha

theorem zOf_mem_aeSub {n : ℕ} (β : Finset (Fin n)) (hβ : β.card = 4) :
    zOf (emb β hβ) ∈ aeSub n :=
  mem_aeSub_of_mem_memAt (zOf_mem_memAt β hβ true)

theorem eq_of_supported_eq_zBar {a : Wr 7} (ha : a ∈ aeSub 7) {α β : Finset (Fin 7)}
    (hα : α.card = 4) (hβ : β.card = 4) (hs : SupportedOn a (↑α : Set (Fin 7)))
    (h : mkQ 7 a = zBar β hβ) : β = α := by
  have h1 : a = zOf (emb β hβ) := eq_of_mkQ_eq_of_mem_aeSub ha (zOf_mem_aeSub β hβ) h
  have hsub : β ⊆ α := by
    intro x hx
    by_contra hxα
    have h2 := (hs x (by exact_mod_cast hxα)).1
    rw [h1, zOf_vec_apply, if_pos (by rw [range_emb]; exact_mod_cast hx)] at h2
    exact absurd h2 (by decide)
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hα, hβ])

theorem eq_of_supported_eq_zBar_mul {a : Wr 7} (ha : a ∈ aeSub 7) {α β : Finset (Fin 7)}
    (hα : α.card = 4) (hβ : β.card = 4) (hs : SupportedOn a (↑α : Set (Fin 7)))
    (h : mkQ 7 a = zBar α hα * zBar β hβ) : β = α := by
  have hmem : zOf (emb α hα) * zOf (emb β hβ) ∈ aeSub 7 :=
    (aeSub 7).mul_mem (zOf_mem_aeSub α hα) (zOf_mem_aeSub β hβ)
  have h1 : a = zOf (emb α hα) * zOf (emb β hβ) := by
    refine eq_of_mkQ_eq_of_mem_aeSub ha hmem ?_
    rw [h, map_mul]
    rfl
  have hsub : β ⊆ α := by
    intro x hx
    by_contra hxα
    have h2 := (hs x (by exact_mod_cast hxα)).1
    have hxα' : x ∉ Set.range (emb α hα) := by rw [range_emb]; exact_mod_cast hxα
    have hxβ : x ∈ Set.range (emb β hβ) := by rw [range_emb]; exact_mod_cast hx
    have e1 : (zOf (emb α hα)).perm.symm x = x := by rw [zOf_perm]; rfl
    rw [h1, mul_vec, e1, zOf_vec_apply, zOf_vec_apply, if_neg hxα', if_pos hxβ] at h2
    exact absurd h2 (by decide)
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hα, hβ])

end Model

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AWM
