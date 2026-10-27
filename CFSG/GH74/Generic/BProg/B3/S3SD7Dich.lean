module

public import CFSG.GH74.Generic.BProg.B3.S3SD7DichP0
public import CFSG.GH74.GLS.C3.Layer1.Th2P61A7

public section

namespace CFSG.GH74.Generic.BProg.B3

open Equiv Equiv.Perm Subgroup CFSG.GH74.Generic.BProg.B3.S3SD7DichGen
  CFSG.GH74.Generic.BProg.B3.S3SD7DichP0

namespace S3SD7Dich

@[expose] def Join (E : Subgroup (Perm (Fin 7))) : Subgroup (Perm (Fin 7)) :=
  ⨆ (F : Subgroup (Perm (Fin 7))) (_ : F ≤ E) (_ : CFSG.pRank 2 ↥E - 1 ≤ CFSG.pRank 2 ↥F),
    centralizer (F : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)

@[expose] def A7Gen (E : Subgroup (Perm (Fin 7))) : Prop := alternatingGroup (Fin 7) ≤ Join E

@[expose] def HasRootFour (E : Subgroup (Perm (Fin 7))) : Prop :=
  ∃ F₀ : Subgroup (Perm (Fin 7)), F₀ ≤ E ∧ GLS.Th2.Obs.IsRootFour F₀

theorem le_join {E F : Subgroup (Perm (Fin 7))} (hFE : F ≤ E)
    (hr : CFSG.pRank 2 ↥E - 1 ≤ CFSG.pRank 2 ↥F) :
    centralizer (F : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ≤ Join E :=
  le_iSup_of_le F (le_iSup_of_le hFE (le_iSup_of_le hr le_rfl))

theorem cj_le_of_cj_le {σ : Perm (Fin 7)} {F' E : Subgroup (Perm (Fin 7))}
    (h : F' ≤ GLS.Th2.cj σ E) : GLS.Th2.cj σ⁻¹ F' ≤ E := by
  rw [GLS.Th2.cj_le_iff, inv_inv]
  exact h

theorem alt_conj_mem {x : Perm (Fin 7)} (hx : x ∈ alternatingGroup (Fin 7)) (g : Perm (Fin 7)) :
    g * x * g⁻¹ ∈ alternatingGroup (Fin 7) :=
  (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem x hx g

theorem join_cj_le (σ : Perm (Fin 7)) (E : Subgroup (Perm (Fin 7))) :
    Join (GLS.Th2.cj σ E) ≤ GLS.Th2.cj σ (Join E) := by
  refine iSup_le fun F' => iSup_le fun hF' => iSup_le fun hr x hx => ?_
  rw [GLS.Th2.mem_cj_iff]
  obtain ⟨hxc, hxA⟩ := Subgroup.mem_inf.1 hx
  have hFE : GLS.Th2.cj σ⁻¹ F' ≤ E := cj_le_of_cj_le hF'
  have hrk : CFSG.pRank 2 ↥E - 1 ≤ CFSG.pRank 2 ↥(GLS.Th2.cj σ⁻¹ F') := by
    have e1 : CFSG.pRank 2 ↥(GLS.Th2.cj σ E) = CFSG.pRank 2 ↥E := GLS.Th2.pRank_cj σ E
    have e2 : CFSG.pRank 2 ↥F' = CFSG.pRank 2 ↥(GLS.Th2.cj σ⁻¹ F') := by
      have := GLS.Th2.pRank_cj σ (GLS.Th2.cj σ⁻¹ F')
      rw [GLS.Th2.cj_inv_cj] at this
      exact this
    rw [← e1, ← e2]
    exact hr
  have hxF : σ⁻¹ * x * σ ∈ centralizer ((GLS.Th2.cj σ⁻¹ F' : Subgroup (Perm (Fin 7))) :
      Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hf' : σ * f * σ⁻¹ ∈ F' := by
        have := (GLS.Th2.mem_cj_iff σ⁻¹ F' f).1 hf
        simpa using this
      have hc := (Subgroup.mem_centralizer_iff.1 hxc) _ hf'
      calc f * (σ⁻¹ * x * σ) = σ⁻¹ * ((σ * f * σ⁻¹) * x) * σ := by group
        _ = σ⁻¹ * (x * (σ * f * σ⁻¹)) * σ := by rw [hc]
        _ = σ⁻¹ * x * σ * f := by group
    · have := alt_conj_mem hxA σ⁻¹
      simpa using this
  exact le_join hFE hrk hxF

theorem a7Gen_of_cj (σ : Perm (Fin 7)) (E : Subgroup (Perm (Fin 7))) (h : A7Gen (GLS.Th2.cj σ E)) :
    A7Gen E := by
  unfold A7Gen at h ⊢
  intro y hy
  have h3 := join_cj_le σ E (h (alt_conj_mem hy σ))
  rw [GLS.Th2.mem_cj_iff] at h3
  simpa [mul_assoc] using h3

theorem isRootFour_cj (τ : Perm (Fin 7)) {F : Subgroup (Perm (Fin 7))}
    (h : GLS.Th2.Obs.IsRootFour F) : GLS.Th2.Obs.IsRootFour (GLS.Th2.cj τ F) := by
  obtain ⟨hA, hcard, hsq, S, hS, hsupp⟩ := h
  unfold GLS.Th2.Obs.IsRootFour
  refine ⟨?_, ?_, ?_, S.map τ.toEmbedding, by simpa using hS, ?_⟩
  · intro x hx
    rw [GLS.Th2.mem_cj_iff] at hx
    have := alt_conj_mem (hA hx) τ
    simpa [mul_assoc] using this
  · rw [← hcard]
    exact (Nat.card_congr ((MulAut.conj τ).subgroupMap F).toEquiv).symm
  · intro x hx
    rw [GLS.Th2.mem_cj_iff] at hx
    have := hsq _ hx
    calc x * x = τ * ((τ⁻¹ * x * τ) * (τ⁻¹ * x * τ)) * τ⁻¹ := by group
      _ = 1 := by rw [this]; group
  · intro x hx hx1
    rw [GLS.Th2.mem_cj_iff] at hx
    have hy1 : τ⁻¹ * x * τ ≠ 1 := by
      intro e
      apply hx1
      calc x = τ * (τ⁻¹ * x * τ) * τ⁻¹ := by group
        _ = 1 := by rw [e]; group
    have h2 := hsupp _ hx hy1
    have hxe : x = τ * (τ⁻¹ * x * τ) * τ⁻¹ := by group
    rw [hxe, Equiv.Perm.support_conj, h2]

theorem hasRootFour_of_cj (σ : Perm (Fin 7)) (E : Subgroup (Perm (Fin 7)))
    (h : HasRootFour (GLS.Th2.cj σ E)) : HasRootFour E := by
  obtain ⟨F₀, hF₀, hF⟩ := h
  exact ⟨GLS.Th2.cj σ⁻¹ F₀, cj_le_of_cj_le hF₀, isRootFour_cj σ⁻¹ hF⟩

theorem r2_iff {g h : Perm (Fin 7)} : r2 g h = true ↔
    g ≠ 1 ∧ h ≠ 1 ∧ g ≠ h ∧ g * g = 1 ∧ h * h = 1 ∧ g * h = h * g := by
  simp only [r2, Bool.and_eq_true, Bool.not_eq_true', pe_eq_false_iff, pe_iff]
  tauto

theorem r3_iff {g h k : Perm (Fin 7)} : r3 g h k = true ↔ r2 g h = true ∧ k ≠ 1 ∧ k ≠ g ∧ k ≠ h ∧
    k ≠ g * h ∧ k * k = 1 ∧ g * k = k * g ∧ h * k = k * h := by
  simp only [r3, Bool.and_eq_true, Bool.not_eq_true', pe_eq_false_iff, pe_iff]
  tauto

theorem mem_suppL {x : Perm (Fin 7)} {i : Fin 7} : i ∈ suppL x ↔ x i ≠ i := by
  simp [suppL]

theorem support_eq (x : Perm (Fin 7)) : x.support = (suppL x).toFinset := by
  ext i
  simp [mem_suppL, Equiv.Perm.mem_support]

theorem suppL_nodup (x : Perm (Fin 7)) : (suppL x).Nodup :=
  (List.nodup_finRange 7).filter _

variable {E : Subgroup (Perm (Fin 7))}

theorem sq_of_mem [hE : CFSG.IsElementaryAbelian 2 ↥E] {x : Perm (Fin 7)} (hx : x ∈ E) :
    x * x = 1 := by
  have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x hx
  rwa [pow_two] at this

theorem comm_of_mem [hE : CFSG.IsElementaryAbelian 2 ↥E] {x y : Perm (Fin 7)} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := by
  have := (hE.toIsMulCommutative.is_comm).comm (⟨x, hx⟩ : E) ⟨y, hy⟩
  exact congrArg (fun z : E => (z : Perm (Fin 7))) this

theorem mem_join {F : Subgroup (Perm (Fin 7))} (hFE : F ≤ E)
    (hr : CFSG.pRank 2 ↥E - 1 ≤ CFSG.pRank 2 ↥F) {σ : Perm (Fin 7)}
    (hσ : σ ∈ centralizer (F : Set (Perm (Fin 7)))) (hA : σ ∈ alternatingGroup (Fin 7)) :
    σ ∈ Join E :=
  le_join hFE hr (Subgroup.mem_inf.2 ⟨hσ, hA⟩)

theorem pRank_zpowers [CFSG.IsElementaryAbelian 2 ↥E] {x : Perm (Fin 7)} (hxE : x ∈ E)
    (hx1 : x ≠ 1) : CFSG.pRank 2 ↥(zpowers x) = 1 := by
  have : CFSG.IsElementaryAbelian 2 ↥(zpowers x) := elemAb_of_le (E := E)
    ((Subgroup.zpowers_le).2 hxE)
  exact pRank_eq_of_card (by rw [card_zpowers_of_sq (sq_of_mem hxE) hx1, pow_one])

theorem pRank_V4_eq [CFSG.IsElementaryAbelian 2 ↥E] {x y : Perm (Fin 7)} {hx : x * x = 1}
    {hy : y * y = 1} {hxy : x * y = y * x} (hxE : x ∈ E) (hyE : y ∈ E) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hne : x ≠ y) : CFSG.pRank 2 ↥(V4 x y hx hy hxy) = 2 := by
  have : CFSG.IsElementaryAbelian 2 ↥(V4 x y hx hy hxy) := elemAb_of_le (E := E)
    (V4_le hxE hyE)
  exact pRank_eq_of_card (by rw [card_V4 hx1 hy1 hne]; norm_num)

theorem a7Gen_of_cand2 [CFSG.IsElementaryAbelian 2 ↥E] (hr : CFSG.pRank 2 ↥E = 2)
    {g h : Perm (Fin 7)} (hgE : g ∈ E) (hhE : h ∈ E) (hr2 : r2 g h = true)
    (hgen : genOKb (cand2 g h) = true) : A7Gen E := by
  obtain ⟨hg1, hh1, hgh, hg2, hh2, hc⟩ := r2_iff.1 hr2
  have hgh1 : g * h ≠ 1 := fun e =>
    hgh ((mul_eq_one_iff_eq_inv.1 e).trans (inv_eq_of_mul_eq_one_right hh2))
  unfold A7Gen
  refine alt_le_of_genOKb (H := Join E) ?_ hgen
  intro q hq
  rw [cand2, List.mem_filter] at hq
  obtain ⟨hqS, hqc⟩ := hq
  have hA := qp_mem_alt hqS
  have key : ∀ x ∈ E, x ≠ 1 → qp q * x = x * qp q → qp q ∈ Join E := by
    intro x hxE hx1 hcx
    have hz := pRank_zpowers hxE hx1
    exact mem_join ((Subgroup.zpowers_le).2 hxE) (by omega) (mem_centralizer_zpowers hcx) hA
  simp only [Bool.or_eq_true] at hqc
  rcases hqc with (h1 | h2) | h3
  · exact key g hgE hg1 (commb_iff.1 h1)
  · exact key h hhE hh1 (commb_iff.1 h2)
  · exact key (g * h) (mul_mem hgE hhE) hgh1 (commb_iff.1 h3)

theorem a7Gen_of_M1 [CFSG.IsElementaryAbelian 2 ↥E] (hr : CFSG.pRank 2 ↥E = 3)
    (hM : ∀ m ∈ M1l, m ∈ E) : A7Gen E := by
  unfold A7Gen
  refine alt_le_of_genOKb (H := Join E) ?_ L1_gen
  intro q hq
  rw [L1, List.mem_filter, List.any_eq_true] at hq
  obtain ⟨hqS, p, hp, hcp⟩ := hq
  rw [Bool.and_eq_true] at hcp
  have hA := qp_mem_alt hqS
  have hchk := List.all_eq_true.1 M1hyp_check p hp
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨hr2, hp1⟩, hp2⟩ := hchk
  obtain ⟨hx1, hy1, hne, hx2, hy2, hxy⟩ := r2_iff.1 hr2
  have hxE : p.1 ∈ E := hM _ (any_pe_iff.1 hp1)
  have hyE : p.2 ∈ E := hM _ (any_pe_iff.1 hp2)
  have hz := pRank_V4_eq (hx := hx2) (hy := hy2) (hxy := hxy) hxE hyE hx1 hy1 hne
  exact mem_join (V4_le (hx := hx2) (hy := hy2) (hxy := hxy) hxE hyE) (by omega)
    (mem_centralizer_V4 (hx := hx2) (hy := hy2) (hxy := hxy) (commb_iff.1 hcp.1)
      (commb_iff.1 hcp.2)) hA

theorem hasRootFour_of_rfb {g h : Perm (Fin 7)} (hgE : g ∈ E) (hhE : h ∈ E) (hr2 : r2 g h = true)
    (hrf : rfb g h = true) : HasRootFour E := by
  obtain ⟨hg1, hh1, hgh, hg2, hh2, hc⟩ := r2_iff.1 hr2
  simp only [rfb, Bool.and_eq_true, beq_iff_eq, evenB, decide_eq_true_eq] at hrf
  obtain ⟨⟨⟨⟨hlen, hsh⟩, hsgh⟩, hge⟩, hhe⟩ := hrf
  refine ⟨V4 g h hg2 hh2 hc, V4_le hgE hhE, ?_⟩
  unfold GLS.Th2.Obs.IsRootFour
  refine ⟨?_, card_V4 hg1 hh1 hgh, ?_, (suppL g).toFinset, ?_, ?_⟩
  · intro z hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact mem_alternatingGroup.2 hge
    · exact mem_alternatingGroup.2 hhe
    · exact mem_alternatingGroup.2 (by rw [map_mul, hge, hhe, mul_one])
  · intro z hz
    rcases hz with rfl | rfl | rfl | rfl
    · simp
    · exact hg2
    · exact hh2
    · exact sq_mul_of_comm hg2 hh2 hc
  · rw [List.toFinset_card_of_nodup (suppL_nodup g)]
    exact hlen
  · intro f hf hf1
    rcases hf with rfl | rfl | rfl | rfl
    · exact absurd rfl hf1
    · exact support_eq _
    · rw [support_eq, hsh]
    · rw [support_eq, hsgh]

theorem mem_E8 {g h k : Perm (Fin 7)} (hgE : g ∈ E) (hhE : h ∈ E) (hkE : k ∈ E) :
    ∀ e ∈ E8 g h k, e ∈ E := by
  intro e he
  simp only [E8, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [one_mem _, hgE, hhE, hkE, mul_mem hgE hhE, mul_mem hgE hkE, mul_mem hhE hkE,
    mul_mem (mul_mem hgE hhE) hkE]

theorem mem_of_sub8 {S : List (Perm (Fin 7))} {g h k : Perm (Fin 7)} (hgE : g ∈ E) (hhE : h ∈ E)
    (hkE : k ∈ E) (hs : sub8 S g h k = true) : ∀ m ∈ S, m ∈ E := by
  intro m hm
  have := List.all_eq_true.1 hs m hm
  exact mem_E8 hgE hhE hkE m (any_pe_iff.1 this)

theorem exists_r2 [CFSG.IsElementaryAbelian 2 ↥E] (hcard : 4 ≤ Nat.card ↥E) :
    ∃ g ∈ E, ∃ h ∈ E, r2 g h = true := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgE, hg1⟩ : ∃ g ∈ E, g ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hno
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hg2 : g * g = 1 := sq_of_mem hgE
  obtain ⟨h, hhE, hhg⟩ : ∃ h ∈ E, h ∉ zpowers g := by
    by_contra hno
    push Not at hno
    have hle : E ≤ zpowers g := fun x hx => hno x hx
    have := Subgroup.card_le_of_le hle
    rw [card_zpowers_of_sq hg2 hg1] at this
    omega
  have hh1 : h ≠ 1 := fun e => hhg (by rw [e]; exact one_mem _)
  have hgh : g ≠ h := fun e => hhg (by rw [← e]; exact Subgroup.mem_zpowers g)
  exact ⟨g, hgE, h, hhE, r2_iff.2 ⟨hg1, hh1, hgh, hg2, sq_of_mem hhE, comm_of_mem hgE hhE⟩⟩

theorem exists_r3 [CFSG.IsElementaryAbelian 2 ↥E] (hcard : 8 ≤ Nat.card ↥E) :
    ∃ g ∈ E, ∃ h ∈ E, ∃ k ∈ E, r3 g h k = true := by
  obtain ⟨g, hgE, h, hhE, hr2⟩ := exists_r2 (E := E) (by omega)
  obtain ⟨hg1, hh1, hgh, hg2, hh2, hc⟩ := r2_iff.1 hr2
  obtain ⟨k, hkE, hkV⟩ : ∃ k ∈ E, k ∉ V4 g h hg2 hh2 hc := by
    by_contra hno
    push Not at hno
    have := Subgroup.card_le_of_le (fun x hx => hno x hx : E ≤ V4 g h hg2 hh2 hc)
    rw [card_V4 hg1 hh1 hgh] at this
    omega
  rw [mem_V4] at hkV
  push Not at hkV
  obtain ⟨hk1, hkg, hkh, hkgh⟩ := hkV
  exact ⟨g, hgE, h, hhE, k, hkE, r3_iff.2 ⟨hr2, hk1, hkg, hkh, hkgh, sq_of_mem hkE,
    comm_of_mem hgE hkE, comm_of_mem hhE hkE⟩⟩

theorem rank2_case [CFSG.IsElementaryAbelian 2 ↥E] (hP : E ≤ P0) (hr : CFSG.pRank 2 ↥E = 2) :
    A7Gen E ∨ HasRootFour E := by
  have hcard : Nat.card ↥E = 4 := by rw [card_eq_two_pow_pRank (E := E), hr]; norm_num
  obtain ⟨g, hgE, h, hhE, hr2⟩ := exists_r2 (E := E) hcard.ge
  have hcan : ([g, h, g * h].any fun g' => [g, h, g * h].any fun h' => r2 g' h' && canon g' h') =
      true := by
    have := List.all_eq_true.1 (List.all_eq_true.1 canon_exists g (mem_P0.1 (hP hgE))) h
      (mem_P0.1 (hP hhE))
    rw [hr2] at this
    simpa using this
  rw [List.any_eq_true] at hcan
  obtain ⟨g', hg', hcan2⟩ := hcan
  rw [List.any_eq_true] at hcan2
  obtain ⟨h', hh', hcan3⟩ := hcan2
  rw [Bool.and_eq_true] at hcan3
  have hmem : ∀ z ∈ [g, h, g * h], z ∈ E := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    exacts [hgE, hhE, mul_mem hgE hhE]
  have hg'E := hmem g' hg'
  have hh'E := hmem h' hh'
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 good2_all g' (mem_P0.1 (hP hg'E))) h'
    (mem_P0.1 (hP hh'E))
  have hrc : (r2 g' h' && canon g' h') = true := by rw [Bool.and_eq_true]; exact hcan3
  rw [hrc] at h2
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h2
  rcases h2 with hrf | hgen
  · exact Or.inr (hasRootFour_of_rfb hg'E hh'E hcan3.1 hrf)
  · exact Or.inl (a7Gen_of_cand2 hr hg'E hh'E hcan3.1 hgen)

theorem rank3_case [CFSG.IsElementaryAbelian 2 ↥E] (hP : E ≤ P0) (hr : CFSG.pRank 2 ↥E = 3) :
    A7Gen E ∨ HasRootFour E := by
  have hcard : Nat.card ↥E = 8 := by rw [card_eq_two_pow_pRank (E := E), hr]; norm_num
  obtain ⟨g, hgE, h, hhE, k, hkE, hr3⟩ := exists_r3 (E := E) hcard.ge
  have hr2 : r2 g h = true := (r3_iff.1 hr3).1
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 cls3_all g (mem_P0.1 (hP hgE))) h
    (mem_P0.1 (hP hhE))
  rw [hr2] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.1 h1 k (mem_P0.1 (hP hkE))
  rw [hr3] at h2
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h2
  rcases h2 with hM | hV
  · exact Or.inl (a7Gen_of_M1 hr (mem_of_sub8 hgE hhE hkE hM))
  · have hVE := mem_of_sub8 hgE hhE hkE hV
    exact Or.inr (hasRootFour_of_rfb (hVE ub (by simp [Vbl])) (hVE vb (by simp [Vbl]))
      Vb_check.1 Vb_check.2)

theorem dich_of_le_P0 [CFSG.IsElementaryAbelian 2 ↥E] (hE2 : 2 ≤ CFSG.pRank 2 ↥E) (hP : E ≤ P0) :
    A7Gen E ∨ HasRootFour E := by
  have hcard := card_eq_two_pow_pRank (E := E)
  have hle : Nat.card ↥E ≤ 16 := by
    have := Subgroup.card_le_of_le hP
    rw [card_P0] at this
    exact this
  have h4 : CFSG.pRank 2 ↥E ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 5 ≤ 2 ^ CFSG.pRank 2 ↥E := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  have hcases : CFSG.pRank 2 ↥E = 2 ∨ CFSG.pRank 2 ↥E = 3 ∨ CFSG.pRank 2 ↥E = 4 := by omega
  rcases hcases with hr | hr | hr
  · exact rank2_case hP hr
  · exact rank3_case hP hr
  · exfalso
    have h16 : Nat.card ↥E = 16 := by rw [hcard, hr]; norm_num
    have hEP : E = P0 := Subgroup.eq_of_le_of_card_ge hP (by rw [card_P0, h16])
    obtain ⟨a, ha, b, hb, hab⟩ := P0_noncomm
    rw [← hEP] at ha hb
    exact hab (comm_of_mem ha hb)

theorem dich (E : Subgroup (Perm (Fin 7))) [CFSG.IsElementaryAbelian 2 ↥E]
    (hE2 : 2 ≤ CFSG.pRank 2 ↥E) : A7Gen E ∨ HasRootFour E := by
  obtain ⟨σ, hσ⟩ := exists_conj_le_P0 E (CFSG.IsElementaryAbelian.isPGroup 2 ↥E)
  have : CFSG.IsElementaryAbelian 2 ↥(GLS.Th2.cj σ E) := GLS.Th2.isElementaryAbelian_cj σ ‹_›
  have hE2' : 2 ≤ CFSG.pRank 2 ↥(GLS.Th2.cj σ E) := by rw [GLS.Th2.pRank_cj]; exact hE2
  rcases dich_of_le_P0 (E := GLS.Th2.cj σ E) hE2' hσ with h | h
  · exact Or.inl (a7Gen_of_cj σ E h)
  · exact Or.inr (hasRootFour_of_cj σ E h)

end S3SD7Dich

@[expose] def A7Dich : Prop :=
  ∀ E : Subgroup (Equiv.Perm (Fin 7)), CFSG.IsElementaryAbelian 2 ↥E → 2 ≤ CFSG.pRank 2 ↥E →
    (alternatingGroup (Fin 7) ≤ ⨆ (F : Subgroup (Equiv.Perm (Fin 7))) (_ : F ≤ E)
      (_ : CFSG.pRank 2 ↥E - 1 ≤ CFSG.pRank 2 ↥F), centralizer (F : Set (Equiv.Perm (Fin 7))) ⊓
        alternatingGroup (Fin 7)) ∨
    ∃ F₀ : Subgroup (Equiv.Perm (Fin 7)), F₀ ≤ E ∧ GLS.Th2.Obs.IsRootFour F₀

theorem a7_gen_dichotomy (E : Subgroup (Equiv.Perm (Fin 7))) (hE : CFSG.IsElementaryAbelian 2 ↥E)
    (hE2 : 2 ≤ CFSG.pRank 2 ↥E) :
    (alternatingGroup (Fin 7) ≤ ⨆ (F : Subgroup (Equiv.Perm (Fin 7))) (_ : F ≤ E)
      (_ : CFSG.pRank 2 ↥E - 1 ≤ CFSG.pRank 2 ↥F), centralizer (F : Set (Equiv.Perm (Fin 7))) ⊓
        alternatingGroup (Fin 7)) ∨
    ∃ F₀ : Subgroup (Equiv.Perm (Fin 7)), F₀ ≤ E ∧ GLS.Th2.Obs.IsRootFour F₀ := by
  have := hE
  exact S3SD7Dich.dich E hE2

theorem a7Dich_proved : A7Dich := fun E hE hE2 => a7_gen_dichotomy E hE hE2

end CFSG.GH74.Generic.BProg.B3
