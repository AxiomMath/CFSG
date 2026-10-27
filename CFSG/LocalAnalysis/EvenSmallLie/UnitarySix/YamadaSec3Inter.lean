module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Facts
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Tools
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndConj

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd (conjR mem_conjR)

@[expose] def pu₁ : Equiv.Perm (Fin 693) := wP [15, 16, 17, 16, 15]

@[expose] def pu₂ : Equiv.Perm (Fin 693) := wP [17, 16, 17, 15, 16, 17]

@[expose] def pw₀ : Equiv.Perm (Fin 693) := wP [15, 16, 17, 15, 16, 17, 15, 16, 17]

@[expose] def pj₀ : Equiv.Perm (Fin 693) := wP [15, 1, 15, 0, 1, 15, 1]

@[expose] def pab : Equiv.Perm (Fin 693) := wP [15, 16]

@[expose] def pba : Equiv.Perm (Fin 693) := wP [16, 15]

@[expose] def paba : Equiv.Perm (Fin 693) := wP [15, 16, 15]

@[expose] def pbcb : Equiv.Perm (Fin 693) := wP [16, 17, 16]

theorem rep_conj {u a : Array ℕ} {U X : Equiv.Perm (Fin 693)} (hu : validA 693 u = true)
    (hU : Rep 693 u U) (hX : Rep 693 a X) : Rep 693 (conjA 693 u a) (U * X * U⁻¹) := by
  have h := rep_conjA hu hX
  rwa [permOfArr_eq_of_rep hU] at h

theorem eq_one_of_eqA {a : Array ℕ} {X : Equiv.Perm (Fin 693)} (hX : Rep 693 a X)
    (h : eqA 693 a (idA 693) = true) : X = 1 :=
  (eqA_iff hX rep_idA).1 h

theorem wP_single (k : ℕ) : wP [k] = gP k := by simp [wP]

theorem grp_le {c : ChainData} {H : Subgroup (Equiv.Perm (Fin 693))}
    (h : ∀ w ∈ c.gens, wP w ∈ H) : c.grp ≤ H :=
  (Subgroup.closure_le _).2 fun _ ⟨w, hw, hG⟩ => hG ▸ h w hw

theorem wP_mem_grp {c : ChainData} {w : List ℕ} (hw : w ∈ c.gens) : wP w ∈ c.grp :=
  Subgroup.subset_closure ⟨w, hw, rfl⟩


theorem valid_spec : validA 693 au₁ = true ∧ validA 693 au₂ = true ∧ validA 693 aw₀ = true ∧
    validA 693 aj₀ = true ∧ validA 693 aab = true ∧ validA 693 aba = true ∧
    validA 693 aaba = true ∧ validA 693 abcb = true ∧ chK1.O.all (validA 693) = true ∧
    chK2.O.all (validA 693) = true := by
  have h := valid_check
  unfold validCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem rep_au₁ : Rep 693 au₁ pu₁ := rep_wA tabs_check _ (by decide)
theorem rep_au₂ : Rep 693 au₂ pu₂ := rep_wA tabs_check _ (by decide)
theorem rep_aw₀ : Rep 693 aw₀ pw₀ := rep_wA tabs_check _ (by decide)
theorem rep_aj₀ : Rep 693 aj₀ pj₀ := rep_wA tabs_check _ (by decide)
theorem rep_aab : Rep 693 aab pab := rep_wA tabs_check _ (by decide)
theorem rep_aba : Rep 693 aba pba := rep_wA tabs_check _ (by decide)
theorem rep_aaba : Rep 693 aaba paba := rep_wA tabs_check _ (by decide)
theorem rep_abcb : Rep 693 abcb pbcb := rep_wA tabs_check _ (by decide)

theorem all_O_spec {c : ChainData} {p : Array ℕ → Bool} (h : c.O.all p = true) :
    ∀ w ∈ c.gens, p (wA w) = true := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  have hi' : i < c.O.size := by rw [ChainData.O_size]; exact hi
  have := (Array.all_eq_true.1 h) i hi'
  have e : c.O[i] = wA c.gens[i] := by simp [ChainData.O]
  rwa [e] at this

theorem grp_fixO {c : ChainData} (hg : c.GensOK) {p : ℕ} (hp : p < 693)
    (h : (c.O.all fun s => s[p]! == p) = true) : ∀ x ∈ c.grp, x ⟨p, hp⟩ = ⟨p, hp⟩ := by
  intro x hx
  have hle : c.grp ≤ MulAction.stabilizer (Equiv.Perm (Fin 693)) (⟨p, hp⟩ : Fin 693) := by
    refine (Subgroup.closure_le _).2 fun G ⟨w, hw, hG⟩ => ?_
    rw [hG, SetLike.mem_coe, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    have h1 := all_O_spec h w hw
    rw [beq_iff_eq] at h1
    exact Fin.ext (by rw [← (rep_wA tabs_check w (hg w hw)) ⟨p, hp⟩]; exact h1)
  have := hle hx
  rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at this

theorem S_fix0 : ∀ x ∈ chS.grp, x 0 = 0 := by
  have h := fix_check
  unfold fixCheck at h
  simp only [Bool.and_eq_true] at h
  exact grp_fixO gensOK_chS (by norm_num) h.1.1

theorem sIntFix_spec : pu₂ 381 = 0 ∧ pu₁ 1 = 0 ∧ pw₀ 1 = 0 ∧ (∀ x ∈ chT2.grp, x 381 = 381) ∧
    ∀ x ∈ chT1.grp, x 1 = 1 := by
  have h := sIntFix_check
  unfold sIntFix at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, grp_fixO gensOK_chT2 (by norm_num) (by simpa using h4),
    grp_fixO gensOK_chT1 (by norm_num) (by simpa using h5)⟩
  · rw [← rep_au₂.apply (by norm_num)]; exact h1
  · rw [← rep_au₁.apply (by norm_num)]; exact h2
  · rw [← rep_aw₀.apply (by norm_num)]; exact h3

theorem perm_inv_apply' (g : Equiv.Perm (Fin 693)) (x : Fin 693) : g⁻¹ (g x) = x :=
  Equiv.symm_apply_apply g x

theorem perm_apply_inv' (g : Equiv.Perm (Fin 693)) (x : Fin 693) : g (g⁻¹ x) = x :=
  Equiv.apply_symm_apply g x

theorem fix_of_conj {H : Subgroup (Equiv.Perm (Fin 693))} (hH : ∀ y ∈ H, y 0 = 0)
    {g x : Equiv.Perm (Fin 693)} {q : Fin 693} (hq : g q = 0) (hm : g * x * g⁻¹ ∈ H) :
    x q = q := by
  have h := hH _ hm
  have hq' : g⁻¹ 0 = q := by rw [← hq, perm_inv_apply']
  simp only [Equiv.Perm.mul_apply, hq'] at h
  exact g.injective (h.trans hq.symm)

theorem fix_of_conj_mem {g x : Equiv.Perm (Fin 693)} {q : Fin 693} (hq : g q = 0)
    (hm : g * x * g⁻¹ ∈ chS.grp) : x q = q :=
  fix_of_conj S_fix0 hq hm

theorem sInt_spec : ∀ x ∈ chS.grp, (pu₂ * x * pu₂⁻¹ ∈ chS.grp ↔ x ∈ chT2.grp) ∧
    (pu₁ * x * pu₁⁻¹ ∈ chS.grp ↔ x ∈ chT1.grp) ∧ (x = 1 ∨ pw₀ * x * pw₀⁻¹ ∉ chS.grp) := by
  intro x hx
  obtain ⟨a, hX, h⟩ := sInt_check x hx
  obtain ⟨f2, f1, f0, fT2, fT1⟩ := sIntFix_spec
  unfold sIntAt at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  have e381 : a[381]! = (x 381 : ℕ) := hX.apply (by norm_num)
  have e1 : a[1]! = (x 1 : ℕ) := hX.apply (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · by_cases hq : x 381 = 381
    · rcases h1 with h1 | h1
      · exact absurd (by rw [e381, hq]; rfl) h1
      · rw [mem_chS_iff (rep_conj valid_spec.2.1 rep_au₂ hX), mem_chT2_iff hX, h1]
    · exact ⟨fun hm => absurd (fix_of_conj_mem f2 hm) hq, fun hm => absurd (fT2 x hm) hq⟩
  · by_cases hq : x 1 = 1
    · rcases h2 with h2 | ⟨h2, -⟩
      · exact absurd (by rw [e1, hq]; rfl) h2
      · rw [mem_chS_iff (rep_conj valid_spec.1 rep_au₁ hX), mem_chT1_iff hX, h2]
    · exact ⟨fun hm => absurd (fix_of_conj_mem f1 hm) hq, fun hm => absurd (fT1 x hm) hq⟩
  · by_cases hq : x 1 = 1
    · rcases h2 with h2 | ⟨-, h3 | h3⟩
      · exact absurd (by rw [e1, hq]; rfl) h2
      · exact Or.inl (eq_one_of_eqA hX h3)
      · refine Or.inr fun hm => ?_
        rw [mem_chS_iff (rep_conj valid_spec.2.2.1 rep_aw₀ hX), h3] at hm
        exact Bool.false_ne_true hm
    · exact Or.inr fun hm => hq (fix_of_conj_mem f0 hm)

theorem t2Int_spec : ∀ x ∈ chT2.grp, (pab * x * pab⁻¹ ∈ chT2.grp ↔ x ∈ chX1.grp) ∧
    (pba * x * pba⁻¹ ∈ chT2.grp ↔ x ∈ chX2.grp) ∧ (x = 1 ∨ paba * x * paba⁻¹ ∉ chT2.grp) := by
  intro x hx
  obtain ⟨a, hX, h⟩ := t2Int_check x hx
  unfold t2IntAt at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_chT2_iff (rep_conj valid_spec.2.2.2.2.1 rep_aab hX), mem_chX1_iff hX, h1]
  · rw [mem_chT2_iff (rep_conj valid_spec.2.2.2.2.2.1 rep_aba hX), mem_chX2_iff hX, h2]
  · rcases h3 with h3 | h3
    · exact Or.inl (eq_one_of_eqA hX h3)
    · refine Or.inr fun hm => ?_
      rw [mem_chT2_iff (rep_conj valid_spec.2.2.2.2.2.2.1 rep_aaba hX), h3] at hm
      exact Bool.false_ne_true hm

theorem t1Int_spec : ∀ x ∈ chT1.grp, (pbcb * x * pbcb⁻¹ ∈ chT1.grp ↔ x ∈ chX3.grp) := by
  intro x hx
  obtain ⟨a, hX, h⟩ := t1Int_check x hx
  unfold t1IntAt at h
  simp only [beq_iff_eq] at h
  rw [mem_chT1_iff (rep_conj valid_spec.2.2.2.2.2.2.2.1 rep_abcb hX), mem_chX3_iff hX, h]

theorem sNorm_spec : (∀ s ∈ chS.O, siftA 693 lvS chS.B 0 (conjA 693 aj₀ s) = true) ∧
    ∀ k < 15, siftA 693 lvS chS.B 0 (gA k) = true := by
  have h := sNorm_check
  unfold sNormCheck at h
  simp only [Bool.and_eq_true, Array.all_eq_true, List.all_eq_true, List.mem_range] at h
  refine ⟨fun s hs => ?_, h.2⟩
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hs
  exact h.1 i hi

theorem gP_mem_chS {k : ℕ} (hk : k < 15) : gP k ∈ chS.grp :=
  (mem_chS_iff (rep_gA tabs_check (by omega))).2 (sNorm_spec.2 k hk)

theorem chT2_le_chS : chT2.grp ≤ chS.grp := grp_le fun w hw => by
  simp only [chT2, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [wP_single] <;> exact gP_mem_chS (by norm_num)

theorem chT1_le_chS : chT1.grp ≤ chS.grp := grp_le fun w hw => by
  simp only [chT1, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [wP_single] <;> exact gP_mem_chS (by norm_num)

theorem chX1_le_chT2 : chX1.grp ≤ chT2.grp := grp_le fun w hw => wP_mem_grp (by
  simp only [chX1, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> simp [chT2])

theorem chX2_le_chT2 : chX2.grp ≤ chT2.grp := grp_le fun w hw => wP_mem_grp (by
  simp only [chX2, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> simp [chT2])

theorem chX3_le_chT1 : chX3.grp ≤ chT1.grp := grp_le fun w hw => wP_mem_grp (by
  simp only [chX3, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl
  simp [chT1])

theorem S_inf_u₂ : chS.grp ⊓ conjR chS.grp pu₂ = chT2.grp :=
  inf_eq_of_forall chT2_le_chS fun x hx => by rw [mem_conjR]; exact (sInt_spec x hx).1

theorem S_inf_u₁ : chS.grp ⊓ conjR chS.grp pu₁ = chT1.grp :=
  inf_eq_of_forall chT1_le_chS fun x hx => by rw [mem_conjR]; exact (sInt_spec x hx).2.1

theorem S_inf_w₀ : chS.grp ⊓ conjR chS.grp pw₀ = ⊥ :=
  inf_eq_bot_of_forall fun x hx hx' => by
    rw [mem_conjR] at hx'
    exact ((sInt_spec x hx).2.2.resolve_right (not_not.2 hx'))

theorem T2_inf_ab : chT2.grp ⊓ conjR chT2.grp pab = chX1.grp :=
  inf_eq_of_forall chX1_le_chT2 fun x hx => by rw [mem_conjR]; exact (t2Int_spec x hx).1

theorem T2_inf_ba : chT2.grp ⊓ conjR chT2.grp pba = chX2.grp :=
  inf_eq_of_forall chX2_le_chT2 fun x hx => by rw [mem_conjR]; exact (t2Int_spec x hx).2.1

theorem T2_inf_aba : chT2.grp ⊓ conjR chT2.grp paba = ⊥ :=
  inf_eq_bot_of_forall fun x hx hx' => by
    rw [mem_conjR] at hx'
    exact ((t2Int_spec x hx).2.2.resolve_right (not_not.2 hx'))

theorem T1_inf_bcb : chT1.grp ⊓ conjR chT1.grp pbcb = chX3.grp :=
  inf_eq_of_forall chX3_le_chT1 fun x hx => by rw [mem_conjR]; exact t1Int_spec x hx

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
