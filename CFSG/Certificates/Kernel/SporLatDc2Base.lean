module

public import CFSG.Certificates.Kernel.SporLatDc2Clos

public section

namespace CFSG.KC.SLD2

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F
open CFSG.KC.SLDc (wordE sortedLt cntB sortedLt_nodup cntB_eq_length_filter)
open MulAction

namespace Dc2SoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] (P : Dc2SoundCtx Γ n)

theorem borb_facts {b : BOrb} (h : borbOK P.C P.D b = true) :
    (∀ p < n, ptOK P.C P.D b p = true) ∧ b.qs < n ∧ inO b b.qs = true ∧
    cntB (inO b) (List.range n) = b.osz ∧
    (∀ w ∈ b.kg, (∀ l ∈ w, l < P.C.ns) ∧ wordF P.C.L w b.qs = b.qs) ∧
    (∀ u ∈ b.kw, ∀ i ∈ u, i < b.kg.length) ∧
    sortedLt (b.kw.map fun u => P.D.sep.map (wordE P.C.L b.kg u)) = true ∧
    b.kw.length * b.osz = 2 ^ P.C.k := by
  unfold borbOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq, Nat.beq_eq,
    isS_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hn := P.hn
  rw [hn] at h1 h2 h4
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem ptOK_spec {b : BOrb} {p : ℕ} (h : ptOK P.C P.D b p = true) (hp : inO b p = true) :
    (∀ l < P.C.ns, inO b (P.C.L l p) = true) ∧ (p = b.qs ∨ (tl P.D b p < P.C.ns ∧
      inO b (P.C.L (tl P.D b p) p) = true ∧ dp P.D b (P.C.L (tl P.D b p) p) + 1 = dp P.D b p)) := by
  simp only [ptOK, hp, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  exact ⟨h.1, h.2.imp id fun h' => ⟨h'.1.1, h'.1.2, h'.2⟩⟩

variable {b : BOrb} (hb : borbOK P.C P.D b = true)

include hb

theorem inO_smul {s : Γ} (hs : s ∈ P.S) :
    ∀ q : Fin n, inO b q.val = true → inO b (s • q).val = true := by
  have hf := P.borb_facts hb
  refine P.smul_mem_take (α := Fin n) (F := {q : Fin n | inO b q.val = true})
    (fun l hl hl' q hq => ?_) hs
  have e : (P.els.getD l 1 • q).val = P.C.L l q.val := by
    rw [← act_eq, P.act_letter hl' q.isLt]
  show inO b (P.els.getD l 1 • q).val = true
  rw [e]
  exact (P.ptOK_spec (hf.1 _ q.isLt) hq).1 l hl

theorem inO_smul_iff {s : Γ} (hs : s ∈ P.S) (q : Fin n) :
    inO b (s • q).val = true ↔ inO b q.val = true :=
  ⟨fun h => by simpa using P.inO_smul hb (P.S.inv_mem hs) _ h, P.inO_smul hb hs q⟩

theorem exists_smul_eq_qs : ∀ q : Fin n, inO b q.val = true → ∃ s ∈ P.S, (s • q).val = b.qs := by
  have hf := P.borb_facts hb
  have hns : P.C.ns ≤ P.C.nl := le_trans P.ns_le P.nf_le
  suffices ∀ d, ∀ q : Fin n, dp P.D b q.val = d → inO b q.val = true →
      ∃ s ∈ P.S, (s • q).val = b.qs from fun q => this _ q rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro q hd hq
    rcases (P.ptOK_spec (hf.1 _ q.isLt) hq).2 with e | ⟨hl, hq', hdp⟩
    · exact ⟨1, P.S.one_mem, by rw [one_smul]; exact e⟩
    · have hl' : tl P.D b q.val < P.C.nl := lt_of_lt_of_le hl hns
      let q' : Fin n := ⟨P.C.L (tl P.D b q.val) q.val, P.letter_lt hl' q.isLt⟩
      have hlt : dp P.D b q'.val < d := by
        show dp P.D b (P.C.L (tl P.D b q.val) q.val) < d
        omega
      obtain ⟨s, hs, he⟩ := ih (dp P.D b q'.val) hlt q' rfl hq'
      refine ⟨s * P.els.getD (tl P.D b q.val) 1, P.S.mul_mem hs (P.getD_mem_take hl), ?_⟩
      have e : P.els.getD (tl P.D b q.val) 1 • q = q' :=
        Fin.ext (by rw [← act_eq, P.act_letter hl' q.isLt])
      rw [mul_smul, e]
      exact he

@[expose] def qsF : Fin n := ⟨b.qs, (P.borb_facts hb).2.1⟩

theorem orbit_qs : orbit P.S (P.qsF hb) = {q : Fin n | inO b q.val = true} := by
  ext q
  constructor
  · rintro ⟨⟨s, hs⟩, rfl⟩
    exact P.inO_smul hb hs _ (P.borb_facts hb).2.2.1
  · intro hq
    obtain ⟨s, hs, he⟩ := P.exists_smul_eq_qs hb q hq
    refine ⟨⟨s, hs⟩⁻¹, ?_⟩
    have e : s • q = P.qsF hb := Fin.ext he
    show s⁻¹ • P.qsF hb = q
    rw [← e, inv_smul_smul]

theorem ncard_orbit_qs : (orbit P.S (P.qsF hb)).ncard = b.osz := by
  rw [P.orbit_qs hb, ← (P.borb_facts hb).2.2.2.1, cntB_eq_length_filter,
    ← Set.ncard_image_of_injective _ Fin.val_injective,
    ← List.toFinset_card_of_nodup (List.nodup_range.filter _), ← Set.ncard_coe_finset]
  congr 1
  ext p
  simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_filter, List.mem_toFinset,
    List.mem_filter, List.mem_range, Finset.mem_coe]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.isLt, hq⟩
  · rintro ⟨hp, hq⟩
    exact ⟨⟨p, hp⟩, hq, rfl⟩

@[expose] def eltK (kg : List (List ℕ)) (u : List ℕ) : Γ :=
  (u.map fun i => P.elt (kg.getD i [])).prod

omit hb in
theorem act_eltK {kg : List (List ℕ)} (hkg : ∀ w ∈ kg, ∀ l ∈ w, l < P.C.nl) (u : List ℕ) :
    ∀ p < n, act n (P.eltK kg u) p = wordE P.C.L kg u p ∧ wordE P.C.L kg u p < n := by
  have hg : ∀ i, ∀ l ∈ kg.getD i [], l < P.C.nl := fun i l hl => by
    by_cases hi : i < kg.length
    · rw [List.getD_eq_getElem _ _ hi] at hl
      exact hkg _ (List.getElem_mem hi) l hl
    · rw [List.getD_eq_default _ _ (by omega)] at hl
      simp at hl
  induction u with
  | nil => intro p hp; exact ⟨by simp [eltK, act_one hp, wordE], hp⟩
  | cons i u ih =>
    intro p hp
    obtain ⟨e, hlt⟩ := ih p hp
    have h2 := P.act_wordF _ (hg i) _ hlt
    have e' : P.eltK kg (i :: u) = P.elt (kg.getD i []) * P.eltK kg u := by simp [eltK]
    rw [e', act_mul _ _ hp, e, h2.1]
    exact ⟨rfl, h2.2⟩

theorem closure_kg : Subgroup.closure (P.gens b.kg) = stabilizer Γ (P.qsF hb) ⊓ P.S := by
  classical
  obtain ⟨-, hq, -, -, hkg, hkw, hs, hk⟩ := P.borb_facts hb
  have hkgl : ∀ w ∈ b.kg, ∀ l ∈ w, l < P.C.nl := fun w hw l hl =>
    lt_of_lt_of_le ((hkg w hw).1 l hl) (le_trans P.ns_le P.nf_le)
  have hle : Subgroup.closure (P.gens b.kg) ≤ stabilizer Γ (P.qsF hb) ⊓ P.S := by
    rw [Subgroup.closure_le]
    rintro g ⟨w, hw, rfl⟩
    show P.elt w ∈ stabilizer Γ (P.qsF hb) ⊓ P.S
    rw [Subgroup.mem_inf, mem_stabilizer_iff]
    refine ⟨?_, P.elt_mem_S (hkg w hw).1⟩
    apply Fin.ext
    rw [← act_eq]
    exact (P.act_wordF w (hkgl w hw) _ hq).1.trans (hkg w hw).2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := card_eq_ncard_mul P.S (P.qsF hb)
  rw [card_stabilizer_eq, P.ncard_orbit_qs hb] at h1
  have hpos : 0 < b.osz := by
    rw [← P.ncard_orbit_qs hb]
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨_, mem_orbit_self _⟩
  have hS : Nat.card P.S = 2 ^ P.C.k := P.hk
  have hst : Nat.card (stabilizer Γ (P.qsF hb) ⊓ P.S : Subgroup Γ) = b.kw.length := by
    rw [hS, ← hk, mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  rw [hst]
  have hnd : (b.kw.map (P.eltK b.kg)).Nodup := by
    refine List.Nodup.of_map (fun g => P.D.sep.map (act n g)) ?_
    rw [List.map_map]
    convert sortedLt_nodup hs using 1
    refine List.map_congr_left fun u _ => List.map_congr_left fun p hp => ?_
    exact (P.act_eltK hkgl u p (P.sep_lt p hp)).1
  have hmem : ∀ g ∈ b.kw.map (P.eltK b.kg), g ∈ Subgroup.closure (P.gens b.kg) := by
    intro g hg
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hg
    refine (Subgroup.closure (P.gens b.kg)).list_prod_mem fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have hi' : i < b.kg.length := hkw u hu i hi
    refine Subgroup.subset_closure ⟨b.kg.getD i [], ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem _
  calc b.kw.length = (b.kw.map (P.eltK b.kg)).toFinset.card := by
        rw [List.toFinset_card_of_nodup hnd, List.length_map]
    _ = ((b.kw.map (P.eltK b.kg)).toFinset : Set Γ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ ((Subgroup.closure (P.gens b.kg) : Subgroup Γ) : Set Γ).ncard :=
        Set.ncard_le_ncard (fun g hg => hmem g (by simpa using hg)) (Set.toFinite _)
    _ = Nat.card (Subgroup.closure (P.gens b.kg)) := (Nat.card_coe_set_eq _).symm

end Dc2SoundCtx

end CFSG.KC.SLD2

end
