module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18CrossModel
public import CFSG.ClassicalInvolution.Q3.TL4D1MAMA

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

variable {n : ℕ}

theorem local_const_of_cent_kList :
    ∀ f : Fin 4 → ZMod 2, (∀ k ∈ kList, ofVec f * k * (ofVec f)⁻¹ = k) →
      f 0 = f 1 ∧ f 1 = f 2 ∧ f 2 = f 3 := by
  decide +kernel

theorem local_const_of_cent_kStarList :
    ∀ f : Fin 4 → ZMod 2, (∀ k ∈ kStarList, ofVec f * k * (ofVec f)⁻¹ = k) →
      f 0 = f 1 ∧ f 1 = f 2 ∧ f 2 = f 3 := by
  decide +kernel

theorem vec_const_of_cent_memBar (hn : 5 ≤ n) (δ : Finset (Fin n)) (hδ : δ.card = 4) (c : Bool)
    (f : Fin n → ZMod 2)
    (h : ∀ x ∈ memBar δ hδ c, mkQ n (ofVec f) * x = x * mkQ n (ofVec f)) :
    ∀ x ∈ δ, ∀ y ∈ δ, f x = f y := by
  classical
  set ι := emb δ hδ with hι
  have key : ∀ k : Wr 4, mkQ n (embed ι k) ∈ memBar δ hδ c →
      ofVec (fun i => f (ι i)) * k * (ofVec (fun i => f (ι i)))⁻¹ = k := by
    intro k hk
    have hx := h _ hk
    have hconj : mkQ n (ofVec f) * mkQ n (embed ι k) * (mkQ n (ofVec f))⁻¹ =
        mkQ n (embed ι k) := by
      rw [hx]; group
    rw [hι, conj_mkQ_embed_vec δ hδ f k] at hconj
    have := mkQ_inj_of_supportedOn hn (embed_supportedOn ι _) (embed_supportedOn ι _) hconj
    exact embed_injective ι this
  have hconst : f (ι 0) = f (ι 1) ∧ f (ι 1) = f (ι 2) ∧ f (ι 2) = f (ι 3) := by
    cases c
    · exact local_const_of_cent_kStarList (fun i => f (ι i)) fun k hk =>
        key k (mkQ_embed_mem_false δ hδ hk)
    · exact local_const_of_cent_kList (fun i => f (ι i)) fun k hk =>
        key k (mkQ_embed_mem_true δ hδ hk)
  have hrange : ∀ x ∈ δ, ∃ i, ι i = x := by
    intro x hx
    have : x ∈ Set.range ι := by
      rw [hι, range_emb]; exact_mod_cast hx
    exact this
  intro x hx y hy
  obtain ⟨i, rfl⟩ := hrange x hx
  obtain ⟨j, rfl⟩ := hrange y hy
  obtain ⟨h01, h12, h23⟩ := hconst
  fin_cases i <;> fin_cases j <;> simp_all

theorem perm_eq_one_of_pair_comm (hn : 7 ≤ n) (a c : Fin n) (σ : Equiv.Perm (Fin n))
    (ha : σ a = a) (hc : σ c = c)
    (h : ∀ p q : Fin n, p ≠ q → p ≠ a → p ≠ c → q ≠ a → q ≠ c →
      ∀ (δ : Finset (Fin n)) (hδ : δ.card = 4), a ∉ δ → c ∉ δ →
        ∀ x ∈ memBar δ hδ true,
          mkQ n (ofVec (TL4.pairVec (σ p) (σ q) + TL4.pairVec p q)) * x =
            x * mkQ n (ofVec (TL4.pairVec (σ p) (σ q) + TL4.pairVec p q))) :
    σ = 1 := by
  classical
  have hUcard' : 5 ≤ (Finset.univ \ {a, c} : Finset (Fin n)).card := by
    have h1 := Finset.le_card_sdiff ({a, c} : Finset (Fin n)) Finset.univ
    have h2 : ({a, c} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨U, hU⟩ : ∃ U : Finset (Fin n), U = Finset.univ \ {a, c} := ⟨_, rfl⟩
  have hmemU : ∀ x, x ∈ U ↔ x ≠ a ∧ x ≠ c := by
    intro x
    simp [hU]
  have hUcard : 5 ≤ U.card := by rw [hU]; exact hUcard'
  have hzero : ∀ p q : Fin n, p ≠ q → p ≠ a → p ≠ c → q ≠ a → q ≠ c → ∀ y ∈ U,
      (TL4.pairVec (σ p) (σ q) + TL4.pairVec p q) y = 0 := by
    intro p q hpq hpa hpc hqa hqc y hy
    have hlt : ({p, q, σ p, σ q} : Finset (Fin n)).card < U.card :=
      lt_of_le_of_lt Finset.card_le_four (by omega)
    obtain ⟨x₀, hx₀U, hx₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx₀
    obtain ⟨h1, h2, h3, h4⟩ := hx₀
    have hf0 : (TL4.pairVec (σ p) (σ q) + TL4.pairVec p q) x₀ = 0 := by
      simp [TL4.pairVec_apply, h1, h2, h3, h4]
    have hsub : ({x₀, y} : Finset (Fin n)) ⊆ U := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> assumption
    obtain ⟨δ, hxδ, hδU, hδ⟩ := Finset.exists_subsuperset_card_eq (n := 4) hsub
      (Finset.card_le_two.trans (by norm_num)) (by omega)
    have haδ : a ∉ δ := fun hh => ((hmemU a).mp (hδU hh)).1 rfl
    have hcδ : c ∉ δ := fun hh => ((hmemU c).mp (hδU hh)).2 rfl
    have hconst := vec_const_of_cent_memBar (by omega) δ hδ true _
      (h p q hpq hpa hpc hqa hqc δ hδ haδ hcδ) x₀ (hxδ (by simp)) y (hxδ (by simp))
    rw [← hconst, hf0]
  have hpair : ∀ p q : Fin n, p ≠ q → p ≠ a → p ≠ c → q ≠ a → q ≠ c → σ p = p ∨ σ p = q := by
    intro p q hpq hpa hpc hqa hqc
    by_contra hcon
    push Not at hcon
    obtain ⟨hσp, hσq⟩ := hcon
    have hσpa : σ p ≠ a := fun hh => hpa (σ.injective (hh.trans ha.symm))
    have hσpc : σ p ≠ c := fun hh => hpc (σ.injective (hh.trans hc.symm))
    have hmem : σ p ∈ U := (hmemU _).mpr ⟨hσpa, hσpc⟩
    have h0 := hzero p q hpq hpa hpc hqa hqc (σ p) hmem
    have hne : σ p ≠ σ q := fun hh => hpq (σ.injective hh)
    simp [TL4.pairVec_apply, hne, hσp, hσq] at h0
  have hfix : ∀ p ∈ U, σ p = p := by
    intro p hp
    obtain ⟨hpa, hpc⟩ := (hmemU p).mp hp
    have hlt1 : ({p} : Finset (Fin n)).card < U.card := by simp; omega
    obtain ⟨q, hqU, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt1
    have hlt2 : ({p, q} : Finset (Fin n)).card < U.card :=
      lt_of_le_of_lt Finset.card_le_two (by omega)
    obtain ⟨r, hrU, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt2
    simp only [Finset.mem_singleton] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    obtain ⟨hqa, hqc⟩ := (hmemU q).mp hqU
    obtain ⟨hra, hrc⟩ := (hmemU r).mp hrU
    have h1 := hpair p q (Ne.symm hq) hpa hpc hqa hqc
    have h2 := hpair p r (Ne.symm hr.1) hpa hpc hra hrc
    rcases h1 with h1 | h1
    · exact h1
    · rcases h2 with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) (Ne.symm hr.2)
  refine Equiv.ext fun x => ?_
  by_cases hxa : x = a
  · rw [hxa]; exact ha
  · by_cases hxc : x = c
    · rw [hxc]; exact hc
    · exact hfix x ((hmemU x).mpr ⟨hxa, hxc⟩)

theorem ofVec_inv_eq (v : Fin n → ZMod 2) : (ofVec v : Wr n)⁻¹ = ofVec v :=
  Wr.ext (funext fun _ => rfl) (by show ((ofVec v).perm)⁻¹ = 1; exact inv_one)

theorem mkQ_ofVec_of_const (hn : 5 ≤ n) (β : Finset (Fin n)) (hβ : β.card = 4) (f : Fin n → ZMod 2)
    (ε₁ ε₂ : ZMod 2) (h₁ : ∀ x ∈ β, f x = ε₁) (h₂ : ∀ x ∉ β, f x = ε₂) :
    mkQ n (ofVec f) = 1 ∨ mkQ n (ofVec f) = zBar β hβ := by
  classical
  have hz : zBar β hβ = mkQ n (ofVec (fun x => if x ∈ β then (1 : ZMod 2) else 0)) := by
    show mkQ n (zOf (emb β hβ)) = _
    rw [TwinThinPf10.zOf_eq_ofVec]
    congr 2
    funext x
    have : x ∈ Set.range (emb β hβ) ↔ x ∈ β := by rw [range_emb]; exact Finset.mem_coe
    simp only [this]
  have hone : ∀ v : Fin n → ZMod 2, (∀ x, v x = 0) → mkQ n (ofVec v) = 1 := by
    intro v hv
    have : ofVec v = (1 : Wr n) := Wr.ext (funext hv) rfl
    rw [this, map_one]
  have hall : ∀ v : Fin n → ZMod 2, (∀ x, v x = 1) → mkQ n (ofVec v) = 1 := by
    intro v hv
    have : ofVec v = allOnes n := Wr.ext (funext hv) rfl
    rw [this]
    exact (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)
  have hdec : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases hdec ε₁ with e1 | e1 <;> rcases hdec ε₂ with e2 | e2
  · left
    refine hone _ fun x => ?_
    by_cases hx : x ∈ β
    · rw [h₁ x hx, e1]
    · rw [h₂ x hx, e2]
  · right
    rw [hz, TwinThinPf18.mkQ_ofVec_eq_iff]
    right
    intro x
    by_cases hx : x ∈ β
    · rw [h₁ x hx, e1]; simp [hx]; decide
    · rw [h₂ x hx, e2]; simp [hx]
  · right
    rw [hz]
    congr 2
    funext x
    by_cases hx : x ∈ β
    · simp [h₁ x hx, e1, hx]
    · simp [h₂ x hx, e2, hx]
  · left
    refine hall _ fun x => ?_
    by_cases hx : x ∈ β
    · rw [h₁ x hx, e1]
    · rw [h₂ x hx, e2]

theorem eq_one_or_zBar_of_cent (hn : 8 ≤ n) (β : Finset (Fin n)) (hβ : β.card = 4) (w : Wr n)
    (h₁ : ∀ c : Bool, ∀ x ∈ memBar β hβ c, mkQ n w * x = x * mkQ n w)
    (h₂ : ∀ (δ : Finset (Fin n)) (hδ : δ.card = 4), Disjoint δ β →
      ∀ c : Bool, ∀ x ∈ memBar δ hδ c, mkQ n w * x = x * mkQ n w) :
    mkQ n w = 1 ∨ mkQ n w = zBar β hβ := by
  classical
  have hcent : ∀ (δ : Finset (Fin n)) (hδ : δ.card = 4),
      (∀ c : Bool, ∀ x ∈ memBar δ hδ c, mkQ n w * x = x * mkQ n w) → ∀ i ∈ δ, w.perm i = i := by
    intro δ hδ h i hi
    exact TwinThinPf18.perm_fix_of_cent_memBar (by omega) δ hδ w
      (fun c x hx => by rw [h c x hx]; group) i hi
  have hβc : 4 ≤ (βᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin, hβ]; omega
  have hext : ∀ T : Finset (Fin n), T ⊆ βᶜ → T.card ≤ 4 →
      ∃ δ : Finset (Fin n), T ⊆ δ ∧ δ ⊆ βᶜ ∧ δ.card = 4 :=
    fun T hT hc => Finset.exists_subsuperset_card_eq hT hc hβc
  have hdisj : ∀ δ : Finset (Fin n), δ ⊆ βᶜ → Disjoint δ β :=
    fun δ hδ => Finset.disjoint_of_subset_left hδ disjoint_compl_left
  have hperm : w.perm = 1 := by
    refine Equiv.ext fun i => ?_
    by_cases hi : i ∈ β
    · exact hcent β hβ (fun c x hx => h₁ c x hx) i hi
    · obtain ⟨δ, hTδ, hδc, hδ⟩ := hext {i} (by simpa using hi) (by simp)
      exact hcent δ hδ (fun c x hx => h₂ δ hδ (hdisj δ hδc) c x hx) i (hTδ (by simp))
  have hw : w = ofVec w.vec := Wr.ext rfl hperm
  have hconstβ : ∀ x ∈ β, ∀ y ∈ β, w.vec x = w.vec y := by
    refine vec_const_of_cent_memBar (by omega) β hβ true w.vec ?_
    intro x hx
    have := h₁ true x hx
    rwa [hw] at this
  have hconstβc : ∀ x ∈ βᶜ, ∀ y ∈ βᶜ, w.vec x = w.vec y := by
    intro x hx y hy
    have hsub : ({x, y} : Finset (Fin n)) ⊆ βᶜ := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
    obtain ⟨δ, hTδ, hδc, hδ⟩ := hext _ hsub (Finset.card_le_two.trans (by norm_num))
    refine vec_const_of_cent_memBar (by omega) δ hδ true w.vec ?_ x (hTδ (by simp)) y
      (hTδ (by simp))
    intro x' hx'
    have := h₂ δ hδ (hdisj δ hδc) true x' hx'
    rwa [hw] at this
  have hβne : β.Nonempty := Finset.card_pos.mp (by rw [hβ]; norm_num)
  have hβcne : (βᶜ).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x₀, hx₀⟩ := hβne
  obtain ⟨y₀, hy₀⟩ := hβcne
  have := mkQ_ofVec_of_const (by omega) β hβ w.vec (w.vec x₀) (w.vec y₀)
    (fun x hx => hconstβ x hx x₀ hx₀) (fun x hx => hconstβc x (Finset.mem_compl.mpr hx) y₀ hy₀)
  rwa [← hw] at this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20
