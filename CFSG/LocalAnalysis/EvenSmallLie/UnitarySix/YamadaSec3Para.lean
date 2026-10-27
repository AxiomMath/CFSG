module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Inter
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsSylow
import CFSG.Certificates.Kernel.RankThree.F2Perm

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd (conjR mem_conjR)
open CFSG.RankThree.Native.F2 (validA_of_rep)

theorem O_getElem' (c : ChainData) {i : ℕ} (hi : i < c.O.size) :
    c.O[i] = wA (c.gens[i]'(by rwa [ChainData.O_size] at hi)) := by
  simp [ChainData.O]

theorem conj_mem_grp {c : ChainData} {g : Equiv.Perm (Fin 693)}
    (h : ∀ w ∈ c.gens, g * wP w * g⁻¹ ∈ c.grp) : ∀ x ∈ c.grp, g * x * g⁻¹ ∈ c.grp := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact h w hw
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem mem_normalizer_grp {c : ChainData} {g : Equiv.Perm (Fin 693)}
    (h : ∀ w ∈ c.gens, g * wP w * g⁻¹ ∈ c.grp) : g ∈ Subgroup.normalizer (c.grp : Set _) :=
  YamadaInputs.mem_normalizer_of_conj_mem (conj_mem_grp h)

theorem grp_append {c c₁ c₂ : ChainData} (h : c.gens = c₁.gens ++ c₂.gens) :
    c.grp = c₁.grp ⊔ c₂.grp := by
  rw [ChainData.grp, ChainData.grp, ChainData.grp, ← Subgroup.closure_union]
  congr 1
  ext G
  simp [h, or_and_right, exists_or]


theorem rep_wA_gens {c : ChainData} (hg : c.GensOK) {w : List ℕ} (hw : w ∈ c.gens) :
    Rep 693 (wA w) (wP w) :=
  rep_wA tabs_check w (hg w hw)

theorem K1A1_fix0 : ∀ x ∈ chK1A1.grp, x 0 = 0 := by
  have h := fix_check
  unfold fixCheck at h
  simp only [Bool.and_eq_true] at h
  exact grp_fixO gensOK_chK1A1 (by norm_num) h.2

theorem ka1_spec : ∀ a ∈ chA1.grp, a = 1 ∨ (a ∉ chK1.grp ∧ pu₁ * a * pu₁⁻¹ ∉ chK1A1.grp) := by
  intro x hx
  obtain ⟨a, hX, h⟩ := ka1_check x hx
  unfold ka1At at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (eq_one_of_eqA hX h)
  · refine Or.inr ⟨fun hm => ?_, fun hm => ?_⟩
    · rw [mem_chK1_iff hX, h2] at hm
      exact Bool.false_ne_true hm
    · have := fix_of_conj K1A1_fix0 sIntFix_spec.2.1 hm
      exact h1 (by rw [hX.apply (by norm_num)]; exact congrArg Fin.val this)

theorem ka2_spec : ∀ a ∈ chA2.grp, a = 1 ∨ (a ∉ chK2.grp ∧ pu₂ * a * pu₂⁻¹ ∉ chK2A2.grp) := by
  intro x hx
  obtain ⟨a, hX, h⟩ := ka2_check x hx
  unfold ka2At at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (eq_one_of_eqA hX h)
  · refine Or.inr ⟨fun hm => ?_, fun hm => ?_⟩
    · rw [mem_chK2_iff hX, h1] at hm
      exact Bool.false_ne_true hm
    · rw [mem_chK2A2_iff (rep_conj valid_spec.2.1 rep_au₂ hX), h2] at hm
      exact Bool.false_ne_true hm

theorem uNorm_spec : (∀ w ∈ chK1.gens, pu₁ * wP w * pu₁⁻¹ ∈ chK1.grp) ∧
    ∀ w ∈ chK2.gens, pu₂ * wP w * pu₂⁻¹ ∈ chK2.grp := by
  have h := uNorm_check
  unfold uNormCheck at h
  simp only [Bool.and_eq_true] at h
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · exact (mem_chK1_iff (rep_conj valid_spec.1 rep_au₁ (rep_wA_gens gensOK_chK1 hw))).2
      (all_O_spec h.1 w hw)
  · exact (mem_chK2_iff (rep_conj valid_spec.2.1 rep_au₂ (rep_wA_gens gensOK_chK2 hw))).2
      (all_O_spec h.2 w hw)

theorem kNorm_spec : (∀ k ∈ chK1.gens, ∀ a ∈ chA1.gens, wP k * wP a * (wP k)⁻¹ ∈ chA1.grp) ∧
    ∀ k ∈ chK2.gens, ∀ a ∈ chA2.gens, wP k * wP a * (wP k)⁻¹ ∈ chA2.grp := by
  have h := kNorm_check
  unfold kNormCheck at h
  simp only [Bool.and_eq_true] at h
  refine ⟨fun k hk a ha => ?_, fun k hk a ha => ?_⟩
  · exact (mem_chA1_iff (rep_conj (all_O_spec valid_spec.2.2.2.2.2.2.2.2.1 k hk)
      (rep_wA_gens gensOK_chK1 hk) (rep_wA_gens gensOK_chA1 ha))).2
      (all_O_spec (all_O_spec h.1 k hk) a ha)
  · exact (mem_chA2_iff (rep_conj (all_O_spec valid_spec.2.2.2.2.2.2.2.2.2 k hk)
      (rep_wA_gens gensOK_chK2 hk) (rep_wA_gens gensOK_chA2 ha))).2
      (all_O_spec (all_O_spec h.2 k hk) a ha)

theorem fix_spec : (∀ w ∈ chS.gens, wP w 0 = 0) ∧
    (∀ p : Fin 693, p ≠ 0 → ∃ w ∈ chS.gens, wP w p ≠ p) ∧ ∀ w ∈ chK1A1.gens, wP w 0 = 0 := by
  have h := fix_check
  unfold fixCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun w hw => ?_, fun p hp => ?_, fun w hw => ?_⟩
  · have := all_O_spec h1 w hw
    simp only [beq_iff_eq] at this
    exact Fin.ext (by rw [← (rep_wA_gens gensOK_chS hw) 0]; exact this)
  · have := allLt_spec h2 p.2
    simp only [Bool.or_eq_true, beq_iff_eq, Array.any_eq_true, bne_iff_ne] at this
    rcases this with h0 | ⟨i, hi, hne⟩
    · exact absurd (Fin.ext h0) hp
    · have hi' : i < chS.gens.length := by rwa [ChainData.O_size] at hi
      refine ⟨chS.gens[i], List.getElem_mem hi', fun he => hne ?_⟩
      rw [O_getElem' chS hi, (rep_wA_gens gensOK_chS (List.getElem_mem hi')) p, he]
  · have := all_O_spec h3 w hw
    simp only [beq_iff_eq] at this
    exact Fin.ext (by rw [← (rep_wA_gens gensOK_chK1A1 hw) 0]; exact this)

theorem chT1_le_chK1 : chT1.grp ≤ chK1.grp := grp_le fun w hw => by
  have h := t1K1_check
  unfold t1K1Check at h
  exact (mem_chK1_iff (rep_wA_gens gensOK_chT1 hw)).2 (all_O_spec h w hw)

theorem chT1_eq_inf : chT1.grp = chS.grp ⊓ chK1.grp := by
  refine Subgroup.eq_of_le_of_card_ge (le_inf chT1_le_chS chT1_le_chK1) ?_
  rw [card_chT1]
  have h1 : Nat.card (chS.grp ⊓ chK1.grp : Subgroup _) ∣ 32768 :=
    card_chS ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card (chS.grp ⊓ chK1.grp : Subgroup _) ∣ 25920 :=
    card_chK1 ▸ Subgroup.card_dvd_of_le inf_le_right
  exact Nat.le_of_dvd (by norm_num) (Nat.dvd_gcd h1 h2)

theorem labT1_inv : ∀ y ∈ chT1.grp, ∀ p : Fin 693, labT1[(y p : ℕ)]! = labT1[(p : ℕ)]! := by
  have h := labT1_check
  unfold labT1Check at h
  simp only [Bool.and_eq_true] at h
  let H : Subgroup (Equiv.Perm (Fin 693)) :=
    { carrier := {y | ∀ p : Fin 693, labT1[(y p : ℕ)]! = labT1[(p : ℕ)]!}
      mul_mem' := fun {a b} ha hb p => by rw [Equiv.Perm.mul_apply, ha, hb]
      one_mem' := fun p => rfl
      inv_mem' := fun {a} ha p => by rw [← ha (a⁻¹ p), perm_apply_inv'] }
  have hle : chT1.grp ≤ H := grp_le fun w hw p => by
    have h3 := allLt_spec (all_O_spec h.2 w hw) p.2
    rw [beq_iff_eq, (rep_wA_gens gensOK_chT1 hw) p] at h3
    exact h3
  exact fun y hy => hle hy

theorem norm_spec : ∀ k ∈ chK1.grp, (∀ w ∈ chS.gens, k * wP w * k⁻¹ ∈ chS.grp) →
    k ∈ chSJ.grp := by
  intro x hx hn
  obtain ⟨a, hX, h⟩ := norm_check x hx
  have hv := validA_of_rep hX
  unfold normAt at h
  have hT : (chT1.O.all fun s => labT1[a[s[9]!]!]! == labT1[a[9]!]!) = true := by
    rw [Array.all_eq_true]
    intro j hj
    have hj' : j < chT1.gens.length := by rwa [ChainData.O_size] at hj
    have hw := List.getElem_mem hj'
    rw [O_getElem' chT1 hj, beq_iff_eq, (rep_wA_gens gensOK_chT1 hw).apply (by norm_num),
      hX.apply (Fin.isLt _), hX.apply (by norm_num)]
    have hy : x * wP chT1.gens[j] * x⁻¹ ∈ chT1.grp := by
      rw [chT1_eq_inf]
      exact ⟨conj_mem_grp hn _ (chT1_le_chS (wP_mem_grp hw)),
        chK1.grp.mul_mem (chK1.grp.mul_mem hx (chT1_le_chK1 (wP_mem_grp hw)))
          (chK1.grp.inv_mem hx)⟩
    have := labT1_inv _ hy (x 9)
    simp only [Equiv.Perm.mul_apply, perm_inv_apply'] at this
    simpa using this
  have hS : chS.O.all (fun s => siftA 693 lvS chS.B 0 (conjA 693 a s)) = true := by
    rw [Array.all_eq_true]
    intro j hj
    have hj' : j < chS.gens.length := by rwa [ChainData.O_size] at hj
    rw [O_getElem' chS hj]
    exact (mem_chS_iff (rep_conj hv hX (rep_wA_gens gensOK_chS (List.getElem_mem hj')))).1
      (hn _ (List.getElem_mem hj'))
  rw [hT, hS] at h
  simp only [Bool.not_true, Bool.false_or] at h
  exact (mem_chSJ_iff hX).2 h

theorem chK1A1_eq : chK1A1.grp = chK1.grp ⊔ chA1.grp := grp_append (by decide)

theorem chK2A2_eq : chK2A2.grp = chK2.grp ⊔ chA2.grp := grp_append (by decide)

theorem chK1_le_normalizer_A1 : chK1.grp ≤ Subgroup.normalizer (chA1.grp : Set _) :=
  (Subgroup.closure_le _).2 fun _ ⟨k, hk, hg⟩ => hg ▸ mem_normalizer_grp (kNorm_spec.1 k hk)

theorem chK2_le_normalizer_A2 : chK2.grp ≤ Subgroup.normalizer (chA2.grp : Set _) :=
  (Subgroup.closure_le _).2 fun _ ⟨k, hk, hg⟩ => hg ▸ mem_normalizer_grp (kNorm_spec.2 k hk)

theorem u₁_conj_K1 : ∀ x ∈ chK1.grp, pu₁ * x * pu₁⁻¹ ∈ chK1.grp := conj_mem_grp uNorm_spec.1

theorem u₂_conj_K2 : ∀ x ∈ chK2.grp, pu₂ * x * pu₂⁻¹ ∈ chK2.grp := conj_mem_grp uNorm_spec.2

theorem K1_inf_A1 : chK1.grp ⊓ chA1.grp = ⊥ := by
  rw [inf_comm]
  exact inf_eq_bot_of_forall fun a ha hk => (ka1_spec a ha).resolve_right fun h => h.1 hk

theorem K2_inf_A2 : chK2.grp ⊓ chA2.grp = ⊥ := by
  rw [inf_comm]
  exact inf_eq_bot_of_forall fun a ha hk => (ka2_spec a ha).resolve_right fun h => h.1 hk

theorem KA1_inf : (chK1.grp ⊔ chA1.grp) ⊓ conjR (chK1.grp ⊔ chA1.grp) pu₁ = chK1.grp := by
  apply le_antisymm
  · intro x hx0
    obtain ⟨hx, hx'⟩ := Subgroup.mem_inf.1 hx0
    rw [mem_conjR] at hx'
    have hx2 : x ∈ ((chK1.grp ⊔ chA1.grp : Subgroup _) : Set (Equiv.Perm (Fin 693))) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ chK1_le_normalizer_A1] at hx2
    obtain ⟨k, hk, a, ha, rfl⟩ := hx2
    have hka : pu₁ * a * pu₁⁻¹ ∈ chK1A1.grp := by
      rw [chK1A1_eq]
      have h1 : pu₁ * k * pu₁⁻¹ ∈ chK1.grp ⊔ chA1.grp := Subgroup.mem_sup_left (u₁_conj_K1 k hk)
      have e : pu₁ * a * pu₁⁻¹ = (pu₁ * k * pu₁⁻¹)⁻¹ * (pu₁ * (k * a) * pu₁⁻¹) := by group
      rw [e]
      exact mul_mem (inv_mem h1) hx'
    rcases ka1_spec a ha with rfl | ⟨-, h⟩
    · simpa using hk
    · exact absurd hka h
  · intro k hk
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left hk, ?_⟩
    rw [mem_conjR]
    exact Subgroup.mem_sup_left (u₁_conj_K1 k hk)

theorem KA2_inf : (chK2.grp ⊔ chA2.grp) ⊓ conjR (chK2.grp ⊔ chA2.grp) pu₂ = chK2.grp := by
  apply le_antisymm
  · intro x hx0
    obtain ⟨hx, hx'⟩ := Subgroup.mem_inf.1 hx0
    rw [mem_conjR] at hx'
    have hx2 : x ∈ ((chK2.grp ⊔ chA2.grp : Subgroup _) : Set (Equiv.Perm (Fin 693))) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ chK2_le_normalizer_A2] at hx2
    obtain ⟨k, hk, a, ha, rfl⟩ := hx2
    have hka : pu₂ * a * pu₂⁻¹ ∈ chK2A2.grp := by
      rw [chK2A2_eq]
      have h1 : pu₂ * k * pu₂⁻¹ ∈ chK2.grp ⊔ chA2.grp := Subgroup.mem_sup_left (u₂_conj_K2 k hk)
      have e : pu₂ * a * pu₂⁻¹ = (pu₂ * k * pu₂⁻¹)⁻¹ * (pu₂ * (k * a) * pu₂⁻¹) := by group
      rw [e]
      exact mul_mem (inv_mem h1) hx'
    rcases ka2_spec a ha with rfl | ⟨-, h⟩
    · simpa using hk
    · exact absurd hka h
  · intro k hk
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left hk, ?_⟩
    rw [mem_conjR]
    exact Subgroup.mem_sup_left (u₂_conj_K2 k hk)

theorem grp_fix {c : ChainData} {p : Fin 693} (h : ∀ w ∈ c.gens, wP w p = p) :
    ∀ x ∈ c.grp, x p = p := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact h w hw
  | one => rfl
  | mul x y _ _ hx hy => rw [Equiv.Perm.mul_apply, hy, hx]
  | inv x _ hx => rw [Equiv.Perm.inv_eq_iff_eq, hx]

theorem S_fix : ∀ s ∈ chS.grp, s 0 = 0 := grp_fix fix_spec.1

theorem K1A1_fix : ∀ x ∈ chK1A1.grp, x 0 = 0 := grp_fix fix_spec.2.2

theorem fix_unique {p : Fin 693} (h : ∀ s ∈ chS.grp, s p = p) : p = 0 := by
  by_contra hp
  obtain ⟨w, hw, hne⟩ := fix_spec.2.1 p hp
  exact hne (h _ (wP_mem_grp hw))

theorem normalizer_fix {x : Equiv.Perm (Fin 693)}
    (hx : x ∈ Subgroup.normalizer (chS.grp : Set (Equiv.Perm (Fin 693)))) : x 0 = 0 :=
  fix_unique fun s hs => by
    have h1 : x⁻¹ * s * x ∈ chS.grp := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hx) s).1 hs
      simpa using this
    have h2 := S_fix _ h1
    simp only [Equiv.Perm.mul_apply] at h2
    rw [Equiv.Perm.inv_eq_iff_eq] at h2
    exact h2

theorem chS_le_chSJ : chS.grp ≤ chSJ.grp := grp_le fun w hw => wP_mem_grp (by
  simp only [chS, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> simp [chSJ])

theorem chA1_le_chS : chA1.grp ≤ chS.grp := grp_le fun w hw => by
  simp only [chA1, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [wP_single] <;>
    exact gP_mem_chS (by norm_num)

theorem chA2_le_chS : chA2.grp ≤ chS.grp := grp_le fun w hw => by
  simp only [chA2, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [wP_single] <;>
    exact gP_mem_chS (by norm_num)

theorem mem_SJ_of_normalizer {x : Equiv.Perm (Fin 693)} (hx : x ∈ chK1A1.grp)
    (hn : x ∈ Subgroup.normalizer (chS.grp : Set (Equiv.Perm (Fin 693)))) : x ∈ chSJ.grp := by
  rw [chK1A1_eq] at hx
  have hx2 : x ∈ ((chK1.grp ⊔ chA1.grp : Subgroup _) : Set (Equiv.Perm (Fin 693))) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ chK1_le_normalizer_A1] at hx2
  obtain ⟨k, hk, a, ha, rfl⟩ := hx2
  have haS : a ∈ chS.grp := chA1_le_chS ha
  have hkn : k ∈ Subgroup.normalizer (chS.grp : Set (Equiv.Perm (Fin 693))) := by
    have : k = (k * a) * a⁻¹ := by group
    rw [this]
    exact mul_mem hn (inv_mem (Subgroup.le_normalizer haS))
  have hkSJ := norm_spec k hk fun w hw =>
    (Subgroup.mem_normalizer_iff.1 hkn _).1 (wP_mem_grp hw)
  exact mul_mem hkSJ (chS_le_chSJ haS)

theorem sNorm_j₀ : ∀ w ∈ chS.gens, pj₀ * wP w * pj₀⁻¹ ∈ chS.grp := fun w hw =>
  (mem_chS_iff (rep_conj valid_spec.2.2.2.1 rep_aj₀ (rep_wA_gens gensOK_chS hw))).2
    (all_O_spec (p := fun s => siftA 693 lvS chS.B 0 (conjA 693 aj₀ s))
      (Array.all_eq_true.2 fun _ hi => sNorm_spec.1 _ (Array.getElem_mem hi)) w hw)

theorem SJ_le_normalizer : chSJ.grp ≤ Subgroup.normalizer (chS.grp : Set (Equiv.Perm (Fin 693))) :=
  grp_le fun w hw => by
    simp only [chSJ, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact mem_normalizer_grp sNorm_j₀
      | exact Subgroup.le_normalizer (wP_mem_grp (by simp [chS]))

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
