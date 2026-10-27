module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2PermSound
public import Certificates.Data.OverD2Perm

public section

namespace CFSG.AGLEmbedding.MaxD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open Certificates.MaxD2Perm Certificates.OverD2Perm
open Certificates.FusD2Perm (powT wordT)

section DoubleCosets

variable {Q : Type*} [Group Q]

theorem overgroups_of_doubleCosets [Finite Q] {G N : Subgroup Q} (hNG : N ≤ G)
    (g : ℕ → Q) (r : ℕ) (hg0 : g 0 = 1) (hgG : ∀ i ≤ r, g i ∈ G)
    (hsum : ∑ i ∈ Finset.range (r + 1),
      Nat.card N * Nat.card N / Nat.card (conjStab N (g i)) = Nat.card G)
    (hdisj : ∀ i ≤ r, ∀ j ≤ r, i < j → ∀ a ∈ N, (g i)⁻¹ * a * g j ∉ N)
    (hgen : ∀ i, 3 ≤ i → i ≤ r → G ≤ Subgroup.closure ((N : Set Q) ∪ {g i}))
    (hpair : G ≤ Subgroup.closure ((N : Set Q) ∪ {g 1, g 2})) :
    ∀ Y : Subgroup Q, N ≤ Y → Y ≤ G →
      Y = N ∨ Y = Subgroup.closure ((N : Set Q) ∪ {g 1}) ∨
        Y = Subgroup.closure ((N : Set Q) ∪ {g 2}) ∨ Y = G := by
  intro Y hNY hYG
  have hcov := exists_dcoset_of_sum hNG g r hgG hsum hdisj
  have key : ∀ y ∈ Y, ∃ i ≤ r, y ∈ dcoset N (g i) ∧ g i ∈ Y := by
    intro y hy
    obtain ⟨i, hi, a, ha, b, hb, hyab⟩ := hcov y (hYG hy)
    refine ⟨i, hi, ⟨a, ha, b, hb, hyab⟩, ?_⟩
    have : g i = a⁻¹ * y * b⁻¹ := by rw [hyab]; group
    rw [this]
    exact Y.mul_mem (Y.mul_mem (Y.inv_mem (hNY ha)) hy) (Y.inv_mem (hNY hb))
  have hle : ∀ K : Subgroup Q, (∀ i ≤ r, g i ∈ Y → dcoset N (g i) ⊆ K) → Y ≤ K := by
    intro K hK y hy
    obtain ⟨i, hi, hyi, hgi⟩ := key y hy
    exact hK i hi hgi hyi
  have hdc : ∀ (K : Subgroup Q) (j : ℕ), (N : Set Q) ⊆ K → g j ∈ K → dcoset N (g j) ⊆ K := by
    rintro K j hNK hj _ ⟨a, ha, b, hb, rfl⟩
    exact K.mul_mem (K.mul_mem (hNK ha) hj) (hNK hb)
  have hNU : ∀ j, (N : Set Q) ⊆ Subgroup.closure ((N : Set Q) ∪ {g j}) := fun j x hx =>
    Subgroup.subset_closure (Or.inl hx)
  have hgU : ∀ j, g j ∈ Subgroup.closure ((N : Set Q) ∪ {g j}) := fun j =>
    Subgroup.subset_closure (Or.inr rfl)
  have hdc0 : dcoset N (g 0) ⊆ (N : Set Q) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [hg0, mul_one]
    exact N.mul_mem ha hb
  have hge : ∀ j, g j ∈ Y → Subgroup.closure ((N : Set Q) ∪ {g j}) ≤ Y := by
    intro j hj
    rw [Subgroup.closure_le]
    rintro z (hz | rfl)
    · exact hNY hz
    · exact hj
  by_cases h3 : ∃ i, 3 ≤ i ∧ i ≤ r ∧ g i ∈ Y
  · obtain ⟨i, hi3, hir, hgi⟩ := h3
    exact Or.inr (Or.inr (Or.inr (le_antisymm hYG ((hgen i hi3 hir).trans (hge i hgi)))))
  · have h3' : ∀ i, 3 ≤ i → i ≤ r → g i ∉ Y := fun i hi3 hir hgi => h3 ⟨i, hi3, hir, hgi⟩
    by_cases h1 : g 1 ∈ Y <;> by_cases h2 : g 2 ∈ Y
    · refine Or.inr (Or.inr (Or.inr (le_antisymm hYG (hpair.trans ?_))))
      rw [Subgroup.closure_le]
      rintro z (hz | hz)
      · exact hNY hz
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact h1
        · exact h2
    · refine Or.inr (Or.inl (le_antisymm (hle _ ?_) (hge 1 h1)))
      intro i hi hgi
      rcases Nat.lt_or_ge i 3 with hlt | hge3
      · interval_cases i
        · exact hdc0.trans (hNU 1)
        · exact hdc _ 1 (hNU 1) (hgU 1)
        · exact absurd hgi h2
      · exact absurd hgi (h3' i hge3 hi)
    · refine Or.inr (Or.inr (Or.inl (le_antisymm (hle _ ?_) (hge 2 h2))))
      intro i hi hgi
      rcases Nat.lt_or_ge i 3 with hlt | hge3
      · interval_cases i
        · exact hdc0.trans (hNU 2)
        · exact absurd hgi h1
        · exact hdc _ 2 (hNU 2) (hgU 2)
      · exact absurd hgi (h3' i hge3 hi)
    · refine Or.inl (le_antisymm (hle _ ?_) hNY)
      intro i hi hgi
      rcases Nat.lt_or_ge i 3 with hlt | hge3
      · interval_cases i
        · exact hdc0
        · exact absurd hgi h1
        · exact absurd hgi h2
      · exact absurd hgi (h3' i hge3 hi)

theorem closure_dcoset_eq [Finite Q] {N : Subgroup Q} {g : Q}
    (hclosed : ∀ n ∈ N, g * n * g ∈ N ∨ g * n * g ∈ dcoset N g) :
    (Subgroup.closure ((N : Set Q) ∪ {g}) : Set Q) = (N : Set Q) ∪ dcoset N g := by
  apply Set.Subset.antisymm
  · intro h hh
    have hF : ((N : Set Q) ∪ dcoset N g).Finite := Set.toFinite _
    have key := CFSG.Perm.smul_mem_of_finite_of_mem_closure (G := Q) (X := Q)
      (S := (N : Set Q) ∪ {g}) (F := (N : Set Q) ∪ dcoset N g) hF ?_ hh (x := 1)
      (Or.inl N.one_mem)
    · simpa using key
    · rintro s (hs | hs) x (hx | hx)
      · exact Or.inl (N.mul_mem hs hx)
      · obtain ⟨a, ha, b, hb, rfl⟩ := hx
        refine Or.inr ⟨s * a, N.mul_mem hs ha, b, hb, ?_⟩
        simp [mul_assoc]
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact Or.inr ⟨1, N.one_mem, x, hx, by simp⟩
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        rcases hclosed a ha with h1 | ⟨a', ha', b', hb', h2⟩
        · refine Or.inl ?_
          have : s * (a * s * b) = (s * a * s) * b := by simp [mul_assoc]
          show s * (a * s * b) ∈ N
          rw [this]
          exact N.mul_mem h1 hb
        · refine Or.inr ⟨a', ha', b' * b, N.mul_mem hb' hb, ?_⟩
          show s * (a * s * b) = a' * s * (b' * b)
          have : s * (a * s * b) = (s * a * s) * b := by simp [mul_assoc]
          rw [this, h2]
          simp [mul_assoc]
  · rintro x (hx | ⟨a, ha, b, hb, rfl⟩)
    · exact Subgroup.subset_closure (Or.inl hx)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ha))
        (Subgroup.subset_closure (Or.inr rfl))) (Subgroup.subset_closure (Or.inl hb))

theorem card_closure_dcoset [Finite Q] {N : Subgroup Q} {g : Q} (hg : g ∉ N)
    (hclosed : ∀ n ∈ N, g * n * g ∈ N ∨ g * n * g ∈ dcoset N g) :
    Nat.card (Subgroup.closure ((N : Set Q) ∪ {g})) =
      Nat.card N + Nat.card N * Nat.card N / Nat.card (conjStab N g) := by
  have hdisj : Disjoint (N : Set Q) (dcoset N g) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨a, ha, b, hb, rfl⟩
    apply hg
    have : g = a⁻¹ * (a * g * b) * b⁻¹ := by group
    rw [this]
    exact N.mul_mem (N.mul_mem (N.inv_mem ha) hx) (N.inv_mem hb)
  have h1 : Nat.card (Subgroup.closure ((N : Set Q) ∪ {g})) =
      Nat.card ((N : Set Q) ∪ dcoset N g : Set Q) := by
    rw [← closure_dcoset_eq hclosed]
    rfl
  have h2 : Nat.card ((N : Set Q) ∪ dcoset N g : Set Q) =
      Nat.card (N : Set Q) + Nat.card (dcoset N g) := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  have h3 : Nat.card (dcoset N g) = Nat.card N * Nat.card N / Nat.card (conjStab N g) := by
    have hc : 0 < Nat.card (conjStab N g) := Nat.card_pos
    exact (Nat.div_eq_of_eq_mul_left hc (card_dcoset_mul N g).symm).symm
  rw [h1, h2, h3]
  rfl

end DoubleCosets

theorem getElem!_map_apply_of_lt {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α)
    {l : ℕ} (hl : l < a.size) : (a.map f)[l]! = f a[l]! := by
  rw [getElem!_pos (a.map f) l (by simpa using hl), getElem!_pos a l hl, Array.getElem_map]

section Perm

variable {D : Data} {S : List (Equiv.Perm (Fin D.n))}

theorem Gsub_le_of_genOK (hlen : S.length = D.gT.size)
    (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
    {H : Subgroup (Equiv.Perm (Fin D.n))} {gs gi : Array Tab} {L : List (Equiv.Perm (Fin D.n))}
    {ws : List (List ℤ)} (hL : ∀ g ∈ L, g ∈ H)
    (hgsL : ∀ j, TabRep (gs.getD j (idTab D.n)) (L.getD j 1))
    (hgiL : ∀ j, TabRep (gi.getD j (idTab D.n)) (L.getD j 1)⁻¹)
    (h : genOK D gs gi ws = true) : Gsub S ≤ H := by
  simp only [genOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at h
  obtain ⟨-, hwords⟩ := h
  unfold Gsub
  rw [Subgroup.closure_le]
  intro s hs
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  have hjg : j < D.gT.size := by omega
  have hword := hwords j hjg
  have hrw := wordT_rep L gs gi hgsL hgiL (ws[j]!)
  have hgj : TabRep D.gT[j]! S[j] := by
    have := hgs j
    rwa [show D.gT.getD j (idTab D.n) = D.gT[j]! by simp [hjg],
      show S.getD j 1 = S[j] by simp [hj]] at this
  have heq : wordVal L (ws[j]!) = S[j] := by
    rw [hword] at hrw
    exact hrw.perm_eq hgj
  rw [← heq]
  exact wordVal_mem L H hL _

theorem overgroups_N {pairW : List (List ℤ)}
    (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
    (hgi : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹)
    (hlen : S.length = D.gT.size) (hcard : Nat.card (Gsub S) = D.gOrder)
    (hN : checkN D = true) (hinvN : invsOK D.n (nGens D) (nGensI D) = true)
    (h : checkOverMax D pairW = true) :
    ∀ Y : Subgroup (Equiv.Perm (Fin D.n)), Nsub D S ≤ Y → Y ≤ Gsub S →
      Y = Nsub D S ∨
        Y = Subgroup.closure ((Nsub D S : Set (Equiv.Perm (Fin D.n))) ∪
          {(repElts D S).getD 1 1}) ∨
        Y = Subgroup.closure ((Nsub D S : Set (Equiv.Perm (Fin D.n))) ∪
          {(repElts D S).getD 2 1}) ∨ Y = Gsub S := by
  have hN' := enum_N hgs hgi hN
  simp only [checkOverMax, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hfp, hinvs⟩, hsum⟩, hdisj⟩, hgen⟩, hpair⟩ := h
  simp only [dcDisjoint, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hdisj
  simp only [genAfterOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hgen
  have hrsz : (repT D).size = D.repW.length + 1 := by simp [repT]
  have hrisz : (repI D).size = D.repW.length + 1 := by simp [repI, repT]
  have hrepT := repT_rep hgs hgi
  have hrepI := repI_rep hgs hgi hinvs
  have hxT : ∀ i, i < D.repW.length + 1 → TabRep (repT D)[i]! ((repElts D S).getD i 1) := by
    intro i hi
    have := hrepT i
    rwa [show (repT D).getD i (idTab D.n) = (repT D)[i]! by simp [hrsz, hi]] at this
  have hxI : ∀ i, i < D.repW.length + 1 → TabRep (repI D)[i]! ((repElts D S).getD i 1)⁻¹ := by
    intro i hi
    have := hrepI i
    rwa [show (repI D).getD i (idTab D.n) = (repI D)[i]! by simp [hrisz, hi]] at this
  have hlenE : (repElts D S).length = D.repW.length + 1 := by simp [repElts]
  set Ln := D.nW.map (wordVal S) with hLn
  have hszN : (nGens D).size = Ln.length := by simp [nGens, hLn]
  have hszNI : (nGensI D).size = Ln.length := by simp [nGensI, nGens, hLn]
  refine overgroups_of_doubleCosets Nsub_le_Gsub (fun i => (repElts D S).getD i 1)
    D.repW.length (by simp [repElts]) (fun i hi => repElts_mem (getD_mem_of_lt (by omega) 1))
    (by rw [sum_eq hgs hgi hN hfp hinvs hsum, hcard]) ?_ ?_ ?_
  · intro i hi j hj hij a ha hmem
    obtain ⟨k, hk, hka⟩ := hN'.exists_pos ha
    rcases hdisj i (by omega) j (by omega) with h | h
    · exact h hij
    · have hy := ((hxI i (by omega)).comp hka).comp (hxT j (by omega))
      have hmemT := (mem_enum_iff hN' hy).2 hmem
      have := (memFp_iff hfp _).2 hmemT
      rw [h k hk] at this
      exact Bool.noConfusion this
  · intro i hi3 hir
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 3 := ⟨i - 3, by omega⟩
    obtain ⟨hgl, hgw⟩ := hgen
    have hg3 := hgw i' (by omega)
    refine Gsub_le_of_genOK hlen hgs (L := Ln ++ [(repElts D S).getD (i' + 3) 1]) ?_ ?_ ?_ hg3
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact Subgroup.subset_closure (Or.inl (Subgroup.subset_closure hg))
      · rw [List.mem_singleton] at hg
        subst hg
        exact Subgroup.subset_closure (Or.inr rfl)
    · exact rep_append_singleton (fun x => x) rfl (rep_map_words S D.gT (giT D) hgs hgi D.nW)
        hszN (hxT (i' + 3) (by omega))
    · exact rep_append_singleton (fun x => x⁻¹) inv_one (nGensI_rep hgs hgi hinvN) hszNI
        (hxI (i' + 3) (by omega))
  · simp only [pairOK] at hpair
    have h1 : 1 < D.repW.length + 1 := by
      obtain ⟨hgl, -⟩ := hgen
      omega
    have h2 : 2 < D.repW.length + 1 := by
      obtain ⟨hgl, -⟩ := hgen
      omega
    have hsz1 : (nGens D ++ #[(repT D)[1]!]).size = (Ln ++ [(repElts D S).getD 1 1]).length := by
      rw [Array.size_append, List.length_append, hszN]
      rfl
    have hszi1 : (nGensI D ++ #[(repI D)[1]!]).size = (Ln ++ [(repElts D S).getD 1 1]).length := by
      rw [Array.size_append, List.length_append, hszNI]
      rfl
    refine Gsub_le_of_genOK hlen hgs
      (L := (Ln ++ [(repElts D S).getD 1 1]) ++ [(repElts D S).getD 2 1]) ?_ ?_ ?_ hpair
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · rcases List.mem_append.1 hg with hg | hg
        · exact Subgroup.subset_closure (Or.inl (Subgroup.subset_closure hg))
        · rw [List.mem_singleton] at hg
          subst hg
          exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
      · rw [List.mem_singleton] at hg
        subst hg
        exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
    · exact rep_append_singleton (fun x => x) rfl
        (rep_append_singleton (fun x => x) rfl (rep_map_words S D.gT (giT D) hgs hgi D.nW)
          hszN (hxT 1 h1)) hsz1 (hxT 2 h2)
    · exact rep_append_singleton (fun x => x⁻¹) inv_one
        (rep_append_singleton (fun x => x⁻¹) inv_one (nGensI_rep hgs hgi hinvN) hszNI
          (hxI 1 h1)) hszi1 (hxI 2 h2)

theorem card_closure_of_closedOK
    (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
    (hgi : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹)
    (hN : checkN D = true) {i c : ℕ} (h : closedOK D i c = true) :
    Nat.card (Subgroup.closure ((Nsub D S : Set (Equiv.Perm (Fin D.n))) ∪
      {(repElts D S).getD i 1})) = D.nOrder + D.nOrder * D.nOrder / c := by
  have hN' := enum_N hgs hgi hN
  simp only [closedOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    allBelow_eq_true, Bool.or_eq_true, anyBelow_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hi0, hir⟩, hfp⟩, hinvs⟩, hc⟩, hnot⟩, hall⟩ := h
  have hrsz : (repT D).size = D.repW.length + 1 := by simp [repT]
  have hrisz : (repI D).size = D.repW.length + 1 := by simp [repI, repT]
  have hi : i < D.repW.length + 1 := by omega
  have hx : TabRep (repT D)[i]! ((repElts D S).getD i 1) := by
    have := repT_rep hgs hgi i
    rwa [show (repT D).getD i (idTab D.n) = (repT D)[i]! by simp [hrsz, hi]] at this
  have hxi : TabRep (repI D)[i]! ((repElts D S).getD i 1)⁻¹ := by
    have := repI_rep hgs hgi hinvs i
    rwa [show (repI D).getD i (idTab D.n) = (repI D)[i]! by simp [hrisz, hi]] at this
  have hcount := conjCount_eq hgs hgi hN hfp (i := i) (by omega) hinvs
  rw [hc] at hcount
  set g := (repElts D S).getD i 1 with hg
  have hgN : g ∉ Nsub D S := by
    intro hgm
    have h1 := (memFp_iff hfp _).2 ((mem_enum_iff hN' hx).2 hgm)
    rw [h1] at hnot
    exact Bool.noConfusion hnot
  have hclosed : ∀ m ∈ Nsub D S, g * m * g ∈ Nsub D S ∨ g * m * g ∈ dcoset (Nsub D S) g := by
    intro m hm
    obtain ⟨k, hk, hkm⟩ := hN'.exists_pos hm
    have hy : TabRep (comp D.n (comp D.n (repT D)[i]! (nEnum D).tabs[k]!) (repT D)[i]!)
        (g * m * g) := (hx.comp hkm).comp hx
    rcases hall k hk with h1 | ⟨l, hl, h2⟩
    · exact Or.inl ((mem_enum_iff hN' hy).1 ((memFp_iff hfp _).1 h1))
    · refine Or.inr ?_
      obtain ⟨a', ha', hla⟩ := hN'.exists_elt hl
      rw [getElem!_map_apply_of_lt _ _ hl] at h2
      have hz := ((hxi.comp hla).comp hy)
      have hzN := (mem_enum_iff hN' hz).1 ((memFp_iff hfp _).1 h2)
      refine ⟨a'⁻¹, (Nsub D S).inv_mem ha', g⁻¹ * a' * (g * m * g), hzN, ?_⟩
      group
  rw [card_closure_dcoset hgN hclosed, ← hcount, card_N hgs hgi hN]

end Perm

section Degree

variable {n : ℕ} {S : List (Equiv.Perm (Fin n))} {D : Data}

theorem overgroups_of_check {pairW : List (List ℤ)} (hn : D.n = n)
    (hgs : ∀ j, TabRep (D.gT.getD j (idTab n)) (S.getD j 1))
    (hgi : ∀ j, TabRep ((giT D).getD j (idTab n)) (S.getD j 1)⁻¹)
    (hlen : S.length = D.gT.size) (hcard : Nat.card (Subgroup.closure {g | g ∈ S}) = D.gOrder)
    (hN : checkN D = true) (hinvN : invsOK n (nGens D) (nGensI D) = true)
    (h : checkOverMax D pairW = true) :
    ∀ Y : Subgroup (Equiv.Perm (Fin n)),
      Subgroup.closure {g | g ∈ D.nW.map (wordVal S)} ≤ Y → Y ≤ Subgroup.closure {g | g ∈ S} →
      Y = Subgroup.closure {g | g ∈ D.nW.map (wordVal S)} ∨
        Y = Subgroup.closure ((Subgroup.closure {g | g ∈ D.nW.map (wordVal S)} :
          Set (Equiv.Perm (Fin n))) ∪ {(1 :: D.repW.map (wordVal S)).getD 1 1}) ∨
        Y = Subgroup.closure ((Subgroup.closure {g | g ∈ D.nW.map (wordVal S)} :
          Set (Equiv.Perm (Fin n))) ∪ {(1 :: D.repW.map (wordVal S)).getD 2 1}) ∨
        Y = Subgroup.closure {g | g ∈ S} := by
  subst hn
  exact overgroups_N hgs hgi hlen hcard hN hinvN h

theorem card_closure_of_check (hn : D.n = n)
    (hgs : ∀ j, TabRep (D.gT.getD j (idTab n)) (S.getD j 1))
    (hgi : ∀ j, TabRep ((giT D).getD j (idTab n)) (S.getD j 1)⁻¹)
    (hN : checkN D = true) {i c : ℕ} (h : closedOK D i c = true) :
    Nat.card (Subgroup.closure ((Subgroup.closure {g | g ∈ D.nW.map (wordVal S)} :
      Set (Equiv.Perm (Fin n))) ∪ {(1 :: D.repW.map (wordVal S)).getD i 1})) =
        D.nOrder + D.nOrder * D.nOrder / c := by
  subst hn
  exact card_closure_of_closedOK hgs hgi hN h

end Degree

end CFSG.AGLEmbedding.MaxD2
