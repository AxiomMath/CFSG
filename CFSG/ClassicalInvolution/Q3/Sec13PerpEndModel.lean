module

public import CFSG.ClassicalInvolution.Q3.TL4D1MBase
public import CFSG.ClassicalInvolution.Q3.TL4D1Facts
public import CFSG.ClassicalInvolution.Q3.AE.PermElt

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG.ClassicalInvolution.Q3.AE

private theorem endm_mul_self_of_permBar {n : ℕ} {y : AEQ n} (h : TL4.permBar n y = 1) :
    y * y = 1 := by
  obtain ⟨a, rfl⟩ : ∃ a : Wr n, mkQ n a = y := QuotientGroup.mk_surjective y
  rw [TL4.permBar_mkQ] at h
  have ha : a = Wr.ofVec a.vec := Wr.ext rfl h
  rw [← map_mul, ha, TL4.ofVec_mul_ofVec]
  have h2 : a.vec + a.vec = 0 := funext fun i => Wr.zmod_two_add_self _
  rw [h2, show Wr.ofVec (0 : Fin n → ZMod 2) = 1 from rfl, map_one]

private theorem endm_permBar_pow_five {n : ℕ} {y : AEQ n} (h5 : orderOf y = 5) :
    TL4.permBar n y ^ 5 = 1 ∧ TL4.permBar n y ≠ 1 := by
  refine ⟨?_, fun h1 => ?_⟩
  · rw [← map_pow, ← h5, pow_orderOf_eq_one, map_one]
  · have h2 : orderOf y ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_two]
      exact endm_mul_self_of_permBar h1
    rw [h5] at h2
    norm_num at h2

private theorem endm_zmod2_eq : ∀ p q : ZMod 2, p + q = 0 → p = q := by decide

private theorem endm_zmod2_ne : ∀ p q : ZMod 2, p + q = 1 → p ≠ q := by decide

private theorem endm_comm_criterion {n : ℕ} (a : Wr n) (v : Fin n → ZMod 2)
    (h : mkQ n a * mkQ n (Wr.ofVec v) = mkQ n (Wr.ofVec v) * mkQ n a) :
    (∀ x, v (a.perm.symm x) = v x) ∨ (∀ x, v (a.perm.symm x) ≠ v x) := by
  have h2 : mkQ n (a * Wr.ofVec v * a⁻¹) = mkQ n (Wr.ofVec v) := by
    rw [map_mul, map_mul, map_inv, h, mul_inv_cancel_right]
  rw [TL4.conj_ofVec] at h2
  rcases mkQ_eq_iff.mp h2 with h3 | h3
  · left
    intro x
    have hz : v (a.perm.symm x) + v x = 0 := congrFun (congrArg Wr.vec h3) x
    exact endm_zmod2_eq _ _ hz
  · right
    intro x
    have hz : v (a.perm.symm x) + v x = 1 := congrFun (congrArg Wr.vec h3) x
    exact endm_zmod2_ne _ _ hz

private theorem endm_ofVec_mul_vec {n : ℕ} (v : Fin n → ZMod 2) (w : Wr n) (x : Fin n) :
    (Wr.ofVec v * w).vec x = v x + w.vec x := rfl

private theorem endm_mkQ_ofPerm_comm {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2)
    (hv : ∀ x, v (σ.symm x) = v x) :
    mkQ n (Wr.ofPerm σ) * mkQ n (Wr.ofVec v) = mkQ n (Wr.ofVec v) * mkQ n (Wr.ofPerm σ) := by
  rw [← map_mul, ← map_mul]
  congr 1
  refine Wr.ext (funext fun x => ?_) ?_
  · show (0 : ZMod 2) + v (σ.symm x) = v x + 0
    rw [zero_add, add_zero]
    exact hv x
  · show σ * 1 = 1 * σ
    rw [mul_one, one_mul]

private theorem endm_fix_pair {n : ℕ} {σ : Equiv.Perm (Fin n)} {i j : Fin n} (hi : σ i = i)
    (hj : σ j = j) (x : Fin n) :
    (Pi.single i 1 + Pi.single j 1 : Fin n → ZMod 2) (σ.symm x) =
      (Pi.single i 1 + Pi.single j 1 : Fin n → ZMod 2) x := by
  have h1 : σ.symm x = i ↔ x = i := by rw [Equiv.symm_apply_eq, hi]
  have h2 : σ.symm x = j ↔ x = j := by rw [Equiv.symm_apply_eq, hj]
  simp only [Pi.add_apply, Pi.single_apply, h1, h2]

section Perm

variable {n : ℕ}

private theorem endm_pow_eq_pow_mod {c : Equiv.Perm (Fin n)} (hc5 : c ^ 5 = 1) (e : ℕ) :
    c ^ e = c ^ (e % 5) := by
  conv_lhs => rw [← Nat.div_add_mod e 5]
  rw [pow_add, pow_mul, hc5, one_pow, one_mul]

private theorem endm_fix_of_pow {c : Equiv.Perm (Fin n)} (hc5 : c ^ 5 = 1) {x : Fin n}
    {k m t : ℕ} (hkm : k * m = 5 * t + 1) (hx : (c ^ k) x = x) : c x = x := by
  have h1 : c ^ (k * m) = c := by
    rw [hkm, pow_succ, pow_mul, hc5, one_pow, one_mul]
  calc c x = (c ^ (k * m)) x := by rw [h1]
    _ = x := by
      rw [pow_mul]
      exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hx m

private theorem endm_fix_of_pow' {c : Equiv.Perm (Fin n)} (hc5 : c ^ 5 = 1) {x : Fin n}
    {d : ℕ} (hd0 : 0 < d) (hd5 : d < 5) (hx : (c ^ d) x = x) : c x = x := by
  interval_cases d
  · simpa using hx
  · exact endm_fix_of_pow hc5 (k := 2) (m := 3) (t := 1) rfl hx
  · exact endm_fix_of_pow hc5 (k := 3) (m := 2) (t := 1) rfl hx
  · exact endm_fix_of_pow hc5 (k := 4) (m := 4) (t := 3) rfl hx

private def endmOrb (c : Equiv.Perm (Fin n)) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.image fun i : Fin 5 => (c ^ (i : ℕ)) x

private theorem mem_endmOrb {c : Equiv.Perm (Fin n)} {x y : Fin n} :
    y ∈ endmOrb c x ↔ ∃ i : ℕ, i < 5 ∧ (c ^ i) x = y := by
  unfold endmOrb
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    exact ⟨i, i.isLt, hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩

private theorem endm_pow_apply_ne {c : Equiv.Perm (Fin n)} (hc5 : c ^ 5 = 1) {x : Fin n}
    (hx : c x ≠ x) {a b : ℕ} (hab : a < b) (hb : b < 5) : (c ^ a) x ≠ (c ^ b) x := by
  intro h
  have hb' : (c ^ b) x = (c ^ a) ((c ^ (b - a)) x) := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hab.le]
  rw [hb'] at h
  have h2 : (c ^ (b - a)) x = x := ((c ^ a).injective h).symm
  exact hx (endm_fix_of_pow' hc5 (by omega) (by omega) h2)

private theorem endmOrb_card {c : Equiv.Perm (Fin n)} (hc5 : c ^ 5 = 1) {x : Fin n}
    (hx : c x ≠ x) : (endmOrb c x).card = 5 := by
  have hinj : Function.Injective fun i : Fin 5 => (c ^ (i : ℕ)) x := by
    intro i j hij
    have hij' : (c ^ (i : ℕ)) x = (c ^ (j : ℕ)) x := hij
    by_contra hne
    have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact (endm_pow_apply_ne hc5 hx h j.isLt hij').elim
    · exact (endm_pow_apply_ne hc5 hx h i.isLt hij'.symm).elim
  unfold endmOrb
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

private theorem endm_moved_mem_orbit {c : Equiv.Perm (Fin n)} (hn : n ≤ 7) (hc5 : c ^ 5 = 1)
    {x₀ x : Fin n} (h₀ : c x₀ ≠ x₀) (hx : c x ≠ x) : x ∈ endmOrb c x₀ := by
  by_contra hmem
  have hdisj : Disjoint (endmOrb c x₀) (endmOrb c x) := by
    rw [Finset.disjoint_left]
    intro y hy₀ hy
    obtain ⟨i, hi, rfl⟩ := mem_endmOrb.mp hy₀
    obtain ⟨j, hj, hjx⟩ := mem_endmOrb.mp hy
    apply hmem
    refine mem_endmOrb.mpr ⟨(5 - j + i) % 5, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← endm_pow_eq_pow_mod hc5]
    have h1 : x = (c ^ (5 - j)) ((c ^ j) x) := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hj.le, hc5,
        Equiv.Perm.one_apply]
    rw [h1, hjx, ← Equiv.Perm.mul_apply, ← pow_add]
  have hcard : (endmOrb c x₀ ∪ endmOrb c x).card = 10 := by
    rw [Finset.card_union_of_disjoint hdisj, endmOrb_card hc5 h₀, endmOrb_card hc5 hx]
  have hle := Finset.card_le_univ (endmOrb c x₀ ∪ endmOrb c x)
  rw [Fintype.card_fin, hcard] at hle
  omega

private theorem endm_sq_eq_pow {c σ : Equiv.Perm (Fin n)} (hn : n ≤ 7) (hc5 : c ^ 5 = 1)
    (hc1 : c ≠ 1) (hσ : Commute σ c) : ∃ A : ℕ, A < 5 ∧ σ ^ 2 = c ^ (2 * A) := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, c x₀ ≠ x₀ := by
    by_contra h
    exact hc1 (Equiv.ext fun x => by_contra fun hx => h ⟨x, hx⟩)
  have hcomm : ∀ y, c (σ y) = σ (c y) := fun y => by
    have h := congrArg (fun π : Equiv.Perm (Fin n) => π y) hσ.eq
    simpa [Equiv.Perm.mul_apply] using h.symm
  have hσx : σ x₀ ∈ endmOrb c x₀ := by
    apply endm_moved_mem_orbit hn hc5 hx₀
    rw [hcomm]
    exact fun h => hx₀ (σ.injective h)
  obtain ⟨A, hA5, ha⟩ := mem_endmOrb.mp hσx
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin n), τ = (c ^ A)⁻¹ * σ := ⟨_, rfl⟩
  have hca : Commute (c ^ A) c := (Commute.refl c).pow_left A
  have hτc : Commute τ c := by
    rw [hτ]
    exact (hca.inv_left).mul_left hσ
  have hτpow : ∀ i : ℕ, ∀ y, τ ((c ^ i) y) = (c ^ i) (τ y) := fun i y => by
    have h := congrArg (fun π : Equiv.Perm (Fin n) => π y) (hτc.pow_right i).eq
    simpa [Equiv.Perm.mul_apply] using h
  have hτx₀ : τ x₀ = x₀ := by
    rw [hτ, Equiv.Perm.mul_apply, ← ha, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have hfix : ∀ y ∈ endmOrb c x₀, τ y = y := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := mem_endmOrb.mp hy
    rw [hτpow, hτx₀]
  have hout : ∀ y, y ∉ endmOrb c x₀ → τ y ∉ endmOrb c x₀ := by
    intro y hy hτy
    apply hy
    have h2 : y = τ y := τ.injective (hfix _ hτy).symm
    rw [h2]
    exact hτy
  have hsq : ∀ x, τ (τ x) = x := by
    intro x
    by_cases hxO : x ∈ endmOrb c x₀
    · rw [hfix x hxO, hfix x hxO]
    · by_contra hne
      have hy : τ x ∉ endmOrb c x₀ := hout x hxO
      have hz : τ (τ x) ∉ endmOrb c x₀ := hout _ hy
      have hxy : x ≠ τ x := fun h => hne (by rw [← h]; exact h.symm)
      have hyz : τ x ≠ τ (τ x) := fun h => hxy (τ.injective h)
      have hxz : x ≠ τ (τ x) := fun h => hne h.symm
      have h3 : 2 < (endmOrb c x₀)ᶜ.card :=
        Finset.two_lt_card_iff.mpr ⟨x, τ x, τ (τ x), Finset.mem_compl.mpr hxO,
          Finset.mem_compl.mpr hy, Finset.mem_compl.mpr hz, hxy, hxz, hyz⟩
      rw [Finset.card_compl, Fintype.card_fin, endmOrb_card hc5 hx₀] at h3
      omega
  have hττ : τ * τ = 1 := Equiv.ext fun x => hsq x
  have hcτ : τ * c ^ A = c ^ A * τ := (hτc.pow_right A).eq
  have hστ : σ = c ^ A * τ := by rw [hτ, mul_inv_cancel_left]
  refine ⟨A, hA5, ?_⟩
  calc σ ^ 2 = (c ^ A * τ) * (c ^ A * τ) := by rw [sq, hστ]
    _ = c ^ A * ((τ * c ^ A) * τ) := by simp only [mul_assoc]
    _ = c ^ A * ((c ^ A * τ) * τ) := by rw [hcτ]
    _ = c ^ A * (c ^ A * (τ * τ)) := by simp only [mul_assoc]
    _ = c ^ (2 * A) := by rw [hττ, mul_one, ← pow_add, two_mul]

private theorem endm_sq_eq_one {c₁ c₂ σ : Equiv.Perm (Fin n)} (hn : n ≤ 7)
    (hc1 : c₁ ^ 5 = 1) (hc1' : c₁ ≠ 1) (hnc : c₁ * c₂ ≠ c₂ * c₁)
    (hσ1 : Commute σ c₁) (hσ2 : Commute σ c₂) : σ ^ 2 = 1 := by
  obtain ⟨A, hA5, hsq⟩ := endm_sq_eq_pow hn hc1 hc1' hσ1
  have hcomm : Commute (c₁ ^ (2 * A)) c₂ := by
    rw [← hsq]
    exact hσ2.pow_left 2
  have hcent : ∀ k m t : ℕ, k * m = 5 * t + 1 → Commute (c₁ ^ k) c₂ → False := by
    intro k m t hkm hk
    apply hnc
    have h := hk.pow_left m
    rw [← pow_mul, hkm, pow_succ, pow_mul, hc1, one_pow, one_mul] at h
    exact h.eq
  rw [hsq]
  interval_cases A
  · simp
  · exact (hcent (2 * 1) 3 1 rfl hcomm).elim
  · exact (hcent (2 * 2) 4 3 rfl hcomm).elim
  · exact (hcent (2 * 3) 1 1 rfl hcomm).elim
  · exact (hcent (2 * 4) 2 3 rfl hcomm).elim

end Perm

private theorem endm_embedPerm_swap {n : ℕ} (ι : Fin 4 ↪ Fin n) (i j : Fin 4) :
    embedPerm ι (Equiv.swap i j) = Equiv.swap (ι i) (ι j) := by
  classical
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨k, rfl⟩ := hx
    rw [embedPerm_apply, ι.injective.map_swap]
  · rw [embedPerm_of_not_mem ι _ hx, Equiv.swap_apply_of_ne_of_ne] <;> rintro rfl <;>
      exact hx ⟨_, rfl⟩

private def endm_dblTr (a b c d : Fin 5) (m : Fin 3) : Equiv.Perm (Fin 5) :=
  ![Equiv.swap a b * Equiv.swap c d, Equiv.swap a c * Equiv.swap b d,
    Equiv.swap a d * Equiv.swap b c] m

private theorem endm_embedPerm_three (ι : Fin 4 ↪ Fin 5) (m : Fin 3) :
    embedPerm ι (![d₁, d₂, d₃] m) = endm_dblTr (ι 0) (ι 1) (ι 2) (ι 3) m := by
  fin_cases m
  · show embedPerm ι d₁ = Equiv.swap (ι 0) (ι 1) * Equiv.swap (ι 2) (ι 3)
    rw [d₁, embedPerm_mul, endm_embedPerm_swap, endm_embedPerm_swap]
  · show embedPerm ι d₂ = Equiv.swap (ι 0) (ι 2) * Equiv.swap (ι 1) (ι 3)
    rw [d₂, embedPerm_mul, endm_embedPerm_swap, endm_embedPerm_swap]
  · show embedPerm ι d₃ = Equiv.swap (ι 0) (ι 3) * Equiv.swap (ι 1) (ι 2)
    rw [d₃, embedPerm_mul, endm_embedPerm_swap, endm_embedPerm_swap]

private def endm_pairOK (i j : Fin 5) (σ : Equiv.Perm (Fin 5)) : Prop :=
  (∀ x, (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) (σ.symm x) =
      (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) x) ∨
    (∀ x, (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) (σ.symm x) ≠
      (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) x)

private instance endm_pairOK_decidable (i j : Fin 5) (σ : Equiv.Perm (Fin 5)) :
    Decidable (endm_pairOK i j σ) := by
  unfold endm_pairOK
  infer_instance

private theorem endm_exists_not_pairOK : ∀ a b c d i j : Fin 5, a ≠ b → a ≠ c → a ≠ d →
    b ≠ c → b ≠ d → c ≠ d → i ≠ j → ∃ m : Fin 3, ¬ endm_pairOK i j (endm_dblTr a b c d m) := by
  decide +kernel

private theorem endm_three_cycle : ∀ k l p : Fin 5, k ≠ l → l ≠ p → k ≠ p →
    (Equiv.swap k l * Equiv.swap l p) ^ 3 = 1 := by
  decide +kernel

private def endm_Yw (k l p : Fin 5) : Wr 5 :=
  (Wr.ofVec (Pi.single p 1 + Pi.single k 1))⁻¹ *
    (Wr.ofPerm (Equiv.swap k l * Equiv.swap l p))⁻¹ *
    Wr.ofVec (Pi.single p 1 + Pi.single k 1) * Wr.ofPerm (Equiv.swap k l * Equiv.swap l p)

private theorem endm_Yw_spec : ∀ k l p : Fin 5, k ≠ l → k ≠ p → l ≠ p →
    (endm_Yw k l p).perm = 1 ∧
      ∀ x, (endm_Yw k l p).vec x = (Pi.single k 1 + Pi.single l 1 : Fin 5 → ZMod 2) x := by
  decide +kernel

private theorem endm_ind : ∀ i j k l x : Fin 5,
    i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l →
    (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) x +
        (Pi.single k 1 + Pi.single l 1 : Fin 5 → ZMod 2) x =
      if x = i ∨ x = j ∨ x = k ∨ x = l then 1 else 0 := by
  decide +kernel

private theorem endm_sum_pair : ∀ p k : Fin 5, p ≠ k →
    ∑ x, (Pi.single p 1 + Pi.single k 1 : Fin 5 → ZMod 2) x = 0 := by
  decide +kernel

private theorem endm_exists_mem_perm {β : Finset (Fin 5)} (hβ : β.card = 4) (b : Bool) :
    ∀ d ∈ [d₁, d₂, d₃],
      ∃ a : Wr 5, mkQ 5 a ∈ memBar β hβ b ∧ a.perm = embedPerm (emb β hβ) d := by
  intro d hd
  cases b
  · obtain ⟨k, hk, hkd⟩ := exists_mem_kQStar_perm d hd
    refine ⟨embed (emb β hβ) k, ?_, by rw [embed_perm, hkd]⟩
    exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_map.mpr ⟨k, mem_kQStar.mpr hk, rfl⟩, rfl⟩
  · obtain ⟨k, hk, hkd⟩ := exists_mem_kQ_perm d hd
    refine ⟨embed (emb β hβ) k, ?_, by rw [embed_perm, hkd]⟩
    exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_map.mpr ⟨k, mem_kQ.mpr hk, rfl⟩, rfl⟩

namespace AE5End

theorem not_centralizes_pair {β : Finset (Fin 5)} (hβ : β.card = 4) (b : Bool) {i j : Fin 5}
    (hij : i ≠ j) :
    ¬ ∀ y ∈ memBar β hβ b,
      y * mkQ 5 (Wr.ofVec (Pi.single i 1 + Pi.single j 1)) =
        mkQ 5 (Wr.ofVec (Pi.single i 1 + Pi.single j 1)) * y := by
  intro hall
  have hdbl : ∀ m : Fin 3, endm_pairOK i j (endm_dblTr (emb β hβ 0) (emb β hβ 1)
      (emb β hβ 2) (emb β hβ 3) m) := by
    intro m
    obtain ⟨a, ha, hap⟩ := endm_exists_mem_perm hβ b (![d₁, d₂, d₃] m)
      (by fin_cases m <;> simp)
    have hc := endm_comm_criterion a _ (hall _ ha)
    rw [hap, endm_embedPerm_three] at hc
    exact hc
  have hι := (emb β hβ).injective
  obtain ⟨m, hm⟩ := endm_exists_not_pairOK (emb β hβ 0) (emb β hβ 1) (emb β hβ 2)
    (emb β hβ 3) i j (hι.ne (by decide)) (hι.ne (by decide)) (hι.ne (by decide))
    (hι.ne (by decide)) (hι.ne (by decide)) (hι.ne (by decide)) hij
  exact hm (hdbl m)

theorem exists_three {α : Finset (Fin 5)} (hα : α.card = 4) {i j : Fin 5} (hi : i ∈ α)
    (hj : j ∈ α) (hij : i ≠ j) :
    ∃ h' ∈ TL4.aeModel 5, ∃ e ∈ TL4.aeModel 5, TL4.permBar 5 e = 1 ∧ orderOf h' = 3 ∧
      h' * mkQ 5 (Wr.ofVec (Pi.single i 1 + Pi.single j 1)) =
        mkQ 5 (Wr.ofVec (Pi.single i 1 + Pi.single j 1)) * h' ∧
      zBar α hα = mkQ 5 (Wr.ofVec (Pi.single i 1 + Pi.single j 1)) * (e⁻¹ * h'⁻¹ * e * h') := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨p, hp⟩ : ∃ p, αᶜ = {p} :=
    Finset.card_eq_one.mp (by rw [Finset.card_compl, hα, Fintype.card_fin])
  have hout : ∀ x, x ∉ α ↔ x = p := fun x => by
    rw [← Finset.mem_compl, hp, Finset.mem_singleton]
  have hpα : p ∉ α := (hout p).mpr rfl
  have hsub : ({i, j} : Finset (Fin 5)) ⊆ α :=
    Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hj⟩
  have hcard : (α \ {i, j}).card = 2 := by
    have h1 := Finset.card_sdiff_add_card_eq_card hsub
    rw [hα, Finset.card_pair hij] at h1
    omega
  obtain ⟨k, l, hkl, hkl'⟩ := Finset.card_eq_two.mp hcard
  have hk : k ∈ α \ {i, j} := by
    rw [hkl']
    exact Finset.mem_insert_self _ _
  have hl : l ∈ α \ {i, j} := by
    rw [hkl']
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨hkα, hk'⟩ := Finset.mem_sdiff.mp hk
  obtain ⟨hlα, hl'⟩ := Finset.mem_sdiff.mp hl
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk' hl'
  obtain ⟨hki, hkj⟩ := hk'
  obtain ⟨hli, hlj⟩ := hl'
  have hki' : i ≠ k := fun h => hki h.symm
  have hkj' : j ≠ k := fun h => hkj h.symm
  have hli' : i ≠ l := fun h => hli h.symm
  have hlj' : j ≠ l := fun h => hlj h.symm
  have hmem : ∀ x, x ∈ α ↔ x = i ∨ x = j ∨ x = k ∨ x = l := by
    intro x
    constructor
    · intro hx
      by_cases hxij : x = i ∨ x = j
      · tauto
      · have hx2 : x ∈ α \ {i, j} := Finset.mem_sdiff.mpr ⟨hx, by simpa using hxij⟩
        rw [hkl'] at hx2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
        tauto
    · rintro (h | h | h | h) <;> rw [h] <;> assumption
  have hkp : k ≠ p := fun h => hpα (by rw [← h]; exact hkα)
  have hlp : l ≠ p := fun h => hpα (by rw [← h]; exact hlα)
  have hip : i ≠ p := fun h => hpα (by rw [← h]; exact hi)
  have hjp : j ≠ p := fun h => hpα (by rw [← h]; exact hj)
  obtain ⟨σ, hσdef⟩ : ∃ σ : Equiv.Perm (Fin 5), σ = Equiv.swap k l * Equiv.swap l p :=
    ⟨_, rfl⟩
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσdef]
    exact endm_three_cycle k l p hkl hlp hkp
  have hσk : σ k = l := by
    rw [hσdef, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hkl hkp,
      Equiv.swap_apply_left]
  have hσi : σ i = i := by
    rw [hσdef, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hli' hip,
      Equiv.swap_apply_of_ne_of_ne hki' hli']
  have hσj : σ j = j := by
    rw [hσdef, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hlj' hjp,
      Equiv.swap_apply_of_ne_of_ne hkj' hlj']
  have hsign : Equiv.Perm.sign σ = 1 := by
    rw [hσdef, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hkl, Equiv.Perm.sign_swap hlp]
    norm_num
  have hpk : p ≠ k := Ne.symm hkp
  have hA : Wr.ofPerm σ ∈ AE.aeSub 5 :=
    AE.mem_aeSub.mpr ⟨by simp [Wr.wsum, Wr.ofPerm], hsign⟩
  have hB : Wr.ofVec (Pi.single p 1 + Pi.single k 1) ∈ AE.aeSub 5 :=
    AE.mem_aeSub.mpr ⟨by rw [TL4.wsum_ofVec]; exact endm_sum_pair p k hpk, Equiv.Perm.sign_one⟩
  have hpow : mkQ 5 (Wr.ofPerm σ) ^ 3 = 1 := by
    rw [← map_pow, ofPerm_pow, hσ3, ofPerm_one, map_one]
  have hne : mkQ 5 (Wr.ofPerm σ) ≠ 1 := by
    intro h
    have h2 := congrArg (TL4.permBar 5) h
    rw [TL4.permBar_mkQ, map_one] at h2
    have h3 : σ = 1 := h2
    exact hkl (by rw [← hσk, h3]; rfl)
  refine ⟨mkQ 5 (Wr.ofPerm σ), Subgroup.mem_map.mpr ⟨_, hA, rfl⟩,
    mkQ 5 (Wr.ofVec (Pi.single p 1 + Pi.single k 1)),
    Subgroup.mem_map.mpr ⟨_, hB, rfl⟩, ?_, orderOf_eq_prime hpow hne,
    endm_mkQ_ofPerm_comm σ _ (endm_fix_pair hσi hσj), ?_⟩
  · rw [TL4.permBar_mkQ]
    rfl
  · have hY : (mkQ 5 (Wr.ofVec (Pi.single p 1 + Pi.single k 1)))⁻¹ *
        (mkQ 5 (Wr.ofPerm σ))⁻¹ * mkQ 5 (Wr.ofVec (Pi.single p 1 + Pi.single k 1)) *
        mkQ 5 (Wr.ofPerm σ) = mkQ 5 (endm_Yw k l p) := by
      simp only [endm_Yw, map_mul, map_inv, hσdef]
    rw [hY, ← map_mul]
    unfold zBar
    congr 1
    obtain ⟨hYp, hYv⟩ := endm_Yw_spec k l p hkl hkp hlp
    refine Wr.ext (funext fun x => ?_) ?_
    · rw [zOf_vec_apply, endm_ofVec_mul_vec, hYv x]
      rw [endm_ind i j k l x ⟨hij, hki', hli', hkj', hlj', hkl⟩]
      have hr : x ∈ Set.range (emb α hα) ↔ x = i ∨ x = j ∨ x = k ∨ x = l := by
        rw [range_emb, Finset.mem_coe, hmem]
      by_cases h : x = i ∨ x = j ∨ x = k ∨ x = l
      · rw [if_pos h, if_pos (hr.mpr h)]
      · rw [if_neg h, if_neg (fun h' => h (hr.mp h'))]
    · rw [zOf_perm, Wr.mul_perm, hYp, mul_one]
      rfl

end AE5End

namespace AEQEnd

theorem pow_four_eq_one_of_comm_five {n : ℕ} (hn : n ≤ 7) {x y₁ y₂ : AEQ n}
    (h₁ : orderOf y₁ = 5) (h₂ : orderOf y₂ = 5)
    (hnc : TL4.permBar n y₁ * TL4.permBar n y₂ ≠ TL4.permBar n y₂ * TL4.permBar n y₁)
    (hx₁ : x * y₁ = y₁ * x) (hx₂ : x * y₂ = y₂ * x) : x ^ 4 = 1 := by
  obtain ⟨hc1, hc1'⟩ := endm_permBar_pow_five h₁
  have hσ1 : Commute (TL4.permBar n x) (TL4.permBar n y₁) := by
    have h := congrArg (TL4.permBar n) hx₁
    rw [map_mul, map_mul] at h
    exact h
  have hσ2 : Commute (TL4.permBar n x) (TL4.permBar n y₂) := by
    have h := congrArg (TL4.permBar n) hx₂
    rw [map_mul, map_mul] at h
    exact h
  have hsq : TL4.permBar n x ^ 2 = 1 :=
    endm_sq_eq_one hn hc1 hc1' hnc hσ1 hσ2
  have hxx : TL4.permBar n (x * x) = 1 := by
    rw [map_mul, ← sq]
    exact hsq
  calc x ^ 4 = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := endm_mul_self_of_permBar hxx

end AEQEnd

end CFSG.ClassicalInvolution.Q3.Sec13
