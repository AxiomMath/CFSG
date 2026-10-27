module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSPrime

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

@[expose] def stepP (smul : ℕ → ℕ → ℕ) (gs : List ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  if st.2 < gs.length then (gs.getD st.2 0, 2 ^ st.2) else (smul st.1 st.1, 0)

@[expose] def dblStep (smul : ℕ → ℕ → ℕ) (gs : List ℕ) (A : List (ℕ × ℕ × ℕ × ℕ)) (st : ℕ × ℕ) :
    List (ℕ × ℕ × ℕ × ℕ) :=
  A ++ A.map fun e => (smul e.1 (stepP smul gs st).1, 0, 0, e.2.2.2 ^^^ (stepP smul gs st).2)

@[expose] def dblL (smul : ℕ → ℕ → ℕ) (gs : List ℕ) (ps : List (ℕ × ℕ)) : List (ℕ × ℕ × ℕ × ℕ) :=
  ps.foldl (dblStep smul gs) [(0, 0, 0, 0)]

@[expose] def cntMask (n b : ℕ) (q : ℕ → Bool) (L : List (ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  (L.filter fun e => !chiV n b e.2.2.2 && q e.1).length

section Spec

variable {G : Type*} [Group G] {S : Subgroup G} {N : ℕ} {smul : ℕ → ℕ → ℕ}
  (Φ : CodeIso S N smul) (h0 : smul 0 0 = 0)

@[expose] noncomputable def elt (c : ℕ) : G := (Φ.g c : G)

theorem elt_mul {c d : ℕ} (hc : c < N) (hd : d < N) : elt Φ (smul c d) = elt Φ c * elt Φ d := by
  unfold elt
  rw [← Φ.f_g hc, ← Φ.f_g hd, ← Φ.map_mul, Φ.g_f, Φ.g_f, Φ.g_f, Subgroup.coe_mul]

include h0 in
theorem elt_zero : elt Φ 0 = 1 := by
  unfold elt
  rw [← Φ.f_one h0, Φ.g_f, Subgroup.coe_one]

variable {P : Subgroup G} {gs : List ℕ} {L : List (ℕ × ℕ × ℕ × ℕ)}

include Φ in
theorem smul_lt {c d : ℕ} (hc : c < N) (hd : d < N) : smul c d < N := by
  rw [← Φ.f_g hc, ← Φ.f_g hd, ← Φ.map_mul]
  exact Φ.lt _

include h0 in
theorem dbl_props {ps : List (ℕ × ℕ)} (hgs : ∀ g ∈ gs, g < N) (hgP : ∀ g ∈ gs, elt Φ g ∈ P)
    (hps : ∀ st ∈ ps, st.2 < gs.length ∨ (st.1 < N ∧ elt Φ st.1 ∈ P))
    (χ : G → Bool) (hχ : ∀ x ∈ P, ∀ y ∈ P, χ (x * y) = (χ x ^^ χ y)) {n b : ℕ}
    (hn : gs.length ≤ n) (hb : ∀ k < gs.length, χ (elt Φ (gs.getD k 0)) = b.testBit k) :
    ∀ e ∈ dblL smul gs ps, e.1 < N ∧ elt Φ e.1 ∈ P ∧ χ (elt Φ e.1) = chiV n b e.2.2.2 := by
  have hN : 0 < N := by
    have := Φ.lt 1
    omega
  have h1 : χ 1 = false := by
    have := hχ 1 P.one_mem 1 P.one_mem
    rw [mul_one] at this
    cases h : χ 1 <;> simp_all
  have hstep : ∀ st ∈ ps, (stepP smul gs st).1 < N ∧ elt Φ (stepP smul gs st).1 ∈ P ∧
      χ (elt Φ (stepP smul gs st).1) = chiV n b (stepP smul gs st).2 := by
    intro st hst
    unfold stepP
    split
    · rename_i hk
      have hgk : gs.getD st.2 0 ∈ gs := by
        rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
      exact ⟨hgs _ hgk, hgP _ hgk, by rw [hb _ hk, chiV_two_pow b (lt_of_lt_of_le hk hn)]⟩
    · rename_i hk
      obtain ⟨hs, hsP⟩ := (hps st hst).resolve_left hk
      refine ⟨smul_lt Φ hs hs, by rw [elt_mul Φ hs hs]; exact P.mul_mem hsP hsP, ?_⟩
      rw [elt_mul Φ hs hs, hχ _ hsP _ hsP, Bool.xor_self, chiV_zero]
  unfold dblL
  suffices ∀ A : List (ℕ × ℕ × ℕ × ℕ), (∀ e ∈ A, e.1 < N ∧ elt Φ e.1 ∈ P ∧
      χ (elt Φ e.1) = chiV n b e.2.2.2) → ∀ e ∈ ps.foldl (dblStep smul gs) A,
      e.1 < N ∧ elt Φ e.1 ∈ P ∧ χ (elt Φ e.1) = chiV n b e.2.2.2 by
    refine this _ fun e he => ?_
    rw [List.mem_singleton] at he
    subst he
    exact ⟨hN, by rw [elt_zero Φ h0]; exact P.one_mem, by rw [elt_zero Φ h0, h1, chiV_zero]⟩
  induction ps with
  | nil => exact fun A hA => hA
  | cons st ps ih =>
    intro A hA
    rw [List.foldl_cons]
    refine ih (fun st' hst' => hps st' (List.mem_cons_of_mem _ hst'))
      (fun st' hst' => hstep st' (List.mem_cons_of_mem _ hst')) _ fun e he => ?_
    obtain ⟨hp, hpP, hpχ⟩ := hstep st List.mem_cons_self
    unfold dblStep at he
    rcases List.mem_append.1 he with he | he
    · exact hA e he
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      obtain ⟨hal, haP, haχ⟩ := hA a ha
      refine ⟨smul_lt Φ hal hp, by rw [elt_mul Φ hal hp]; exact P.mul_mem haP hpP, ?_⟩
      rw [elt_mul Φ hal hp, hχ _ haP _ hpP, haχ, hpχ, chiV_xor]

theorem elt_inj {c d : ℕ} (hc : c < N) (hd : d < N) (h : elt Φ c = elt Φ d) : c = d := by
  unfold elt at h
  rw [← Φ.f_g hc, ← Φ.f_g hd, Subtype.ext h]

include h0 in
theorem elt_eq_one_iff {c : ℕ} (hc : c < N) : elt Φ c = 1 ↔ c = 0 := by
  constructor
  · intro h
    exact elt_inj Φ hc (lt_of_le_of_lt (Nat.zero_le c) hc) (h.trans (elt_zero Φ h0).symm)
  · rintro rfl; exact elt_zero Φ h0

include h0 in
theorem elt_sq_iff {c : ℕ} (hc : c < N) : elt Φ c * elt Φ c = 1 ↔ smul c c = 0 := by
  have hcc : smul c c < N := by
    rw [← Φ.f_g hc, ← Φ.map_mul]; exact Φ.lt _
  rw [← elt_mul Φ hc hc, elt_eq_one_iff Φ h0 hcc]

include h0 in
theorem elt_ord4_iff {c : ℕ} (hc : c < N) :
    (elt Φ c * elt Φ c ≠ 1 ∧ elt Φ c * elt Φ c * (elt Φ c * elt Φ c) = 1) ↔
      (smul c c ≠ 0 ∧ smul (smul c c) (smul c c) = 0) := by
  have hcc : smul c c < N := by
    rw [← Φ.f_g hc, ← Φ.map_mul]; exact Φ.lt _
  have hc4 : smul (smul c c) (smul c c) < N := by
    rw [← Φ.f_g hcc, ← Φ.map_mul]; exact Φ.lt _
  rw [← elt_mul Φ hc hc, ← elt_mul Φ hcc hcc, ne_eq, elt_eq_one_iff Φ h0 hcc,
    elt_eq_one_iff Φ h0 hc4]

include h0 in
theorem counts_of_index_two {ps : List (ℕ × ℕ)} (hL : L = dblL smul gs ps)
    (hgs : ∀ g ∈ gs, g < N) (hgP : ∀ g ∈ gs, elt Φ g ∈ P)
    (hps : ∀ st ∈ ps, st.2 < gs.length ∨ (st.1 < N ∧ elt Φ st.1 ∈ P))
    (hnd : (L.map Prod.fst).Nodup) (hcard : Nat.card P = L.length) (hPS : P ≤ S)
    {n : ℕ} (hn : gs.length ≤ n) {K : Subgroup G} (hKP : K ≤ P) (hK : K.relIndex P = 2) :
    ∃ b, b < 2 ^ gs.length ∧
      (∀ e ∈ L, elt Φ e.1 ∈ K ↔ chiV n b e.2.2.2 = false) ∧
      nInv K = cntMask n b (fun c => smul c c == 0 && c != 0) L ∧
      nOrd4 K = cntMask n b (fun c => smul c c != 0 && smul (smul c c) (smul c c) == 0) L := by
  classical
  set χ : G → Bool := fun x => decide (x ∉ K)
  have hχ : ∀ x ∈ P, ∀ y ∈ P, χ (x * y) = (χ x ^^ χ y) := by
    intro x hx y hy
    have h := mul_mem_iff_of_index_two (H := K.subgroupOf P) hK (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    simp only [mem_subgroupOf, Subgroup.coe_mul] at h
    simp only [χ]
    by_cases hxK : x ∈ K <;> by_cases hyK : y ∈ K <;> simp_all
  obtain ⟨b, hb, hbits⟩ := exists_bits (fun k => χ (elt Φ (gs.getD k 0))) gs.length
  have hD := dbl_props Φ h0 hgs hgP hps χ hχ hn (b := b) fun k hk => (hbits k hk).symm
  rw [← hL] at hD
  have hlt : ∀ e ∈ L, e.1 < N := fun e he => (hD e he).1
  have hLP : ∀ e ∈ L, elt Φ e.1 ∈ P := fun e he => (hD e he).2.1
  have hmemL : ∀ e ∈ L, elt Φ e.1 ∈ K ↔ chiV n b e.2.2.2 = false := by
    intro e he
    rw [← (hD e he).2.2]
    simp [χ]
  have hfinS : Finite S := Φ.finite
  have hfinP : Finite P := Finite.of_injective (fun x : P => (⟨x, hPS x.2⟩ : S))
    fun a b h => Subtype.ext (congrArg Subtype.val h :)
  have hLmem : ∀ i < L.length, L.getD i (0, 0, 0, 0) ∈ L := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  set f : Fin L.length → P := fun i => ⟨elt Φ (L.getD i (0, 0, 0, 0)).1, hLP _ (hLmem i i.2)⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    have h := elt_inj Φ (hlt _ (hLmem i i.2)) (hlt _ (hLmem j j.2)) (congrArg Subtype.val hij :)
    have hi' : (L.map Prod.fst)[i.1]'(by simp) = (L.map Prod.fst)[j.1]'(by simp) := by
      simpa [List.getD_eq_getElem _ _ i.2, List.getD_eq_getElem _ _ j.2] using h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 hi')
  have hfbij : Function.Bijective f :=
    hfinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])
  have hcover : ∀ x ∈ P, ∃ e ∈ L, elt Φ e.1 = x := by
    intro x hx
    obtain ⟨i, hi⟩ := hfbij.2 ⟨x, hx⟩
    exact ⟨_, hLmem i i.2, congrArg Subtype.val hi⟩
  have hLnd : L.Nodup := List.Nodup.of_map _ hnd
  have hcount : ∀ q : ℕ → Bool, ∀ Q : G → Prop, (∀ e ∈ L, Q (elt Φ e.1) ↔ q e.1 = true) →
      Nat.card {x : G // x ∈ K ∧ Q x} = cntMask n b q L := by
    intro q Q hQ
    unfold cntMask
    rw [← List.toFinset_card_of_nodup (hLnd.filter _), ← Nat.card_eq_finsetCard]
    refine Nat.card_congr
      { toFun := fun x => ⟨(hcover x.1 (hKP x.2.1)).choose, ?_⟩
        invFun := fun e => ⟨elt Φ e.1.1, ?_, ?_⟩
        left_inv := fun x => Subtype.ext (hcover x.1 (hKP x.2.1)).choose_spec.2
        right_inv := fun e => ?_ }
    · have hspec := (hcover x.1 (hKP x.2.1)).choose_spec
      rw [List.mem_toFinset, List.mem_filter]
      refine ⟨hspec.1, ?_⟩
      rw [Bool.and_eq_true, Bool.not_eq_true', ← hmemL _ hspec.1, ← hQ _ hspec.1, hspec.2]
      exact ⟨x.2.1, x.2.2⟩
    · obtain ⟨he, hp⟩ := List.mem_filter.1 (List.mem_toFinset.1 e.2)
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hp
      exact (hmemL _ he).2 hp.1
    · obtain ⟨he, hp⟩ := List.mem_filter.1 (List.mem_toFinset.1 e.2)
      rw [Bool.and_eq_true] at hp
      exact (hQ _ he).2 hp.2
    · apply Subtype.ext
      have hspec := (hcover (elt Φ e.1.1) (hLP _ (List.mem_filter.1 (List.mem_toFinset.1 e.2)).1)).choose_spec
      have he := (List.mem_filter.1 (List.mem_toFinset.1 e.2)).1
      exact List.inj_on_of_nodup_map hnd hspec.1 he
        (elt_inj Φ (hlt _ hspec.1) (hlt _ he) hspec.2)
  refine ⟨b, hb, hmemL, ?_, ?_⟩
  · unfold nInv
    have := hcount (fun c => smul c c == 0 && c != 0) (fun x => x * x = 1 ∧ x ≠ 1) fun e he => by
      rw [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, elt_sq_iff Φ h0 (hlt e he), ne_eq,
        elt_eq_one_iff Φ h0 (hlt e he)]
    rw [← this]
  · unfold nOrd4
    have := hcount (fun c => smul c c != 0 && smul (smul c c) (smul c c) == 0)
      (fun x => x * x ≠ 1 ∧ x * x * (x * x) = 1) fun e he => by
      rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, elt_ord4_iff Φ h0 (hlt e he)]
    rw [← this]

end Spec

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
