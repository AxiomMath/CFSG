module

public import CFSG.Certificates.Kernel.Stroth77.SplitSmall

public section

namespace CFSG.KC.Stroth77SP

open Equiv Equiv.Perm CFSG.CGT.Stroth77

theorem elS_1 : elS 1 = spX1 := by decide +kernel
theorem elS_2 : elS 2 = spY1 := by decide +kernel
theorem elS_4 : elS 4 = spUV := by decide +kernel
theorem elS_8 : elS 8 = spT := by decide +kernel
theorem elS_16 : elS 16 = spX := by decide +kernel
theorem elS_32 : elS 32 = spY := by decide +kernel
theorem elS_64 : elS 64 = spU := by decide +kernel
theorem elS_128 : elS 128 = spW := by decide +kernel

theorem ite_one_mem {H : Subgroup Msp} (p : Prop) [Decidable p] {m : Msp} (hm : m ∈ H) :
    (if p then m else 1) ∈ H := by
  split_ifs
  · exact hm
  · exact one_mem _

theorem ePhi_mem {H : Subgroup Msp} (h1 : spX1 ∈ H) (h2 : spY1 ∈ H) (h3 : spUV ∈ H)
    (h4 : spT ∈ H) (r : ℕ) : ePhi r ∈ H := by
  unfold ePhi
  exact mul_mem (mul_mem (mul_mem (ite_one_mem _ h1) (ite_one_mem _ h2)) (ite_one_mem _ h3))
    (ite_one_mem _ h4)

theorem pPhi_mem {H : Subgroup Msp} (h1 : spX ∈ H) (h2 : spY ∈ H) (h3 : spU ∈ H)
    (h4 : spW ∈ H) (r : ℕ) : pPhi r ∈ H := by
  unfold pPhi
  exact mul_mem (mul_mem (mul_mem (ite_one_mem _ h1) (ite_one_mem _ h2)) (ite_one_mem _ h3))
    (ite_one_mem _ h4)

theorem spPhi_mem {H : Subgroup Msp} (h1 : spX1 ∈ H) (h2 : spY1 ∈ H) (h3 : spX ∈ H)
    (h4 : spY ∈ H) (h5 : spW ∈ H) (r : ℕ) : spPhi r ∈ H := by
  unfold spPhi
  exact mul_mem (mul_mem (mul_mem (mul_mem (ite_one_mem _ h1) (ite_one_mem _ h2))
    (ite_one_mem _ h3)) (ite_one_mem _ h4)) (ite_one_mem _ h5)

theorem gen_mem {gens : List Msp} {g : Msp} (h : g ∈ gens) : g ∈ Subgroup.closure {g | g ∈ gens} :=
  Subgroup.subset_closure h

theorem card_of_param {H : Subgroup Msp} {n : ℕ} (F : ℕ → Msp)
    (hH : ∀ g, g ∈ H ↔ ∃ k < n, F k = g) (hinj : ∀ k < n, ∀ l < n, F k = F l → k = l) :
    Nat.card H = n := by
  have hset : (H : Set Msp) = F '' ↑(Finset.range n) := by
    ext g
    simp only [SetLike.mem_coe, hH, Set.mem_image, Finset.coe_range, Set.mem_Iio]
  have h1 : (H : Set Msp).ncard = n := by
    have hinj' : Set.InjOn F ↑(Finset.range n) := fun k hk l hl h =>
      hinj k (by simpa using hk) l (by simpa using hl) h
    rw [hset, hinj'.ncard_image,
      Set.ncard_coe_finset, Finset.card_range]
  rw [← Nat.card_coe_set_eq] at h1
  exact h1

theorem ncard_le_length (L : List ℕ) {S : Set Msp} (h : ∀ g ∈ S, ∃ m ∈ L, elS m = g) :
    S.ncard ≤ L.length := by
  have hsub : S ⊆ ↑(L.map elS).toFinset := by
    intro g hg
    obtain ⟨m, hm, rfl⟩ := h g hg
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨m, hm, rfl⟩
  calc S.ncard ≤ (↑(L.map elS).toFinset : Set Msp).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (L.map elS).toFinset.card := Set.ncard_coe_finset _
    _ ≤ (L.map elS).length := List.toFinset_card_le _
    _ = L.length := List.length_map _

variable {D : Tabs}

theorem elS_selK (r b g : ℕ) : elS (selK 0 r b g) = if r.testBit b then elS g else 1 := by
  by_cases h : r.testBit b <;> simp [selK, h, elS_zero]

theorem elS_phiS (ht : tabOK D = true) (r : ℕ) : elS (phiS D r) = spPhi r := by
  simp only [phiS, elS_mulS ht, elS_selK, elS_1, elS_2, elS_16, elS_32, elS_128, spPhi]

theorem elS_conjS (ht : tabOK D = true) (c d : ℕ) : elS (conjS D c d) = elS c * elS d * (elS c)⁻¹ := by
  rw [conjS, elS_mulS ht, elS_mulS ht, elS_invS ht]

theorem commS_iff (ht : tabOK D = true) {c d : ℕ} :
    commS D c d = true ↔ elS c * elS d = elS d * elS c := by
  rw [commS, beq_iff_eq, ← elS_mulS ht, ← elS_mulS ht]
  exact ⟨congrArg elS, elS_injective ht (mulS_lt c d) (mulS_lt d c)⟩

theorem closedP_true : ClosedP D fun _ => true := ⟨rfl, fun _ _ _ => ⟨rfl, fun _ _ _ => rfl⟩⟩

theorem mem_Tsp_iff (ht : tabOK D = true) {g : Msp} : g ∈ Tsp ↔ ∃ c < 256, elS c = g := by
  constructor
  · intro hg
    have hle : Tsp ≤ subS D (fun _ => true) ht closedP_true := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      simp only [Set.mem_setOf_eq, gensTsp, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, by norm_num, rfl, elS_1⟩
      · exact ⟨2, by norm_num, rfl, elS_2⟩
      · exact ⟨4, by norm_num, rfl, elS_4⟩
      · exact ⟨8, by norm_num, rfl, elS_8⟩
      · exact ⟨16, by norm_num, rfl, elS_16⟩
      · exact ⟨32, by norm_num, rfl, elS_32⟩
      · exact ⟨64, by norm_num, rfl, elS_64⟩
      · exact ⟨128, by norm_num, rfl, elS_128⟩
    obtain ⟨c, hc, -, h⟩ := hle hg
    exact ⟨c, hc, h⟩
  · rintro ⟨c, -, rfl⟩
    have hT : ∀ g ∈ gensTsp, g ∈ Tsp := fun g hg => gen_mem hg
    exact mul_mem
      (ePhi_mem (hT _ (by simp [gensTsp])) (hT _ (by simp [gensTsp])) (hT _ (by simp [gensTsp]))
        (hT _ (by simp [gensTsp])) _)
      (pPhi_mem (hT _ (by simp [gensTsp])) (hT _ (by simp [gensTsp])) (hT _ (by simp [gensTsp]))
        (hT _ (by simp [gensTsp])) _)

theorem card_Tsp (ht : tabOK D = true) : Nat.card Tsp = 256 :=
  card_of_param elS (fun _ => mem_Tsp_iff ht) fun _ hk _ hl h => elS_injective ht hk hl h

theorem lt_of_mem_l32 {r : ℕ} (h : r ∈ l32) : r < 32 := by
  simp only [l32, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem mem_l32 {r : ℕ} (h : r < 32) : r ∈ l32 := by
  simp only [l32, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem cl_facts (h : clOK D = true) :
    ClosedP D (memA D) ∧ ClosedP D memAE ∧ ClosedP D (fun c => decide (c < 16)) ∧
      ∀ a ∈ [1, 2, 16, 32, 128], memA D a = true := by
  simp only [clOK, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨closed_facts h.1.1.1, closed_facts h.1.1.2, closed_facts h.1.2, h.2⟩

theorem a_facts (h : aOK D = true) :
    (∀ c < 256, memA D c = true → ∃ r < 32, phiS D r = c) ∧
      (∀ r < 32, ∀ s < 32, phiS D r = phiS D s → r = s) ∧
      (∀ r < 32, mulS D (phiS D r) (phiS D r) = 0 ∧ ∀ s < 32, commS D (phiS D r) (phiS D s) = true) ∧
      (∀ c < 256, (∀ a ∈ [1, 2, 16, 32, 128], commS D c a = true) → memA D c = true) := by
  rw [aOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun c hc hm => ?_, fun r hr s hs he => ?_, fun r hr => ?_, fun c hc ha => ?_⟩
  · have := List.all_eq_true.1 h1 c (mem_l256 hc)
    rw [hm, beq_iff_eq, eq_comm, List.any_eq_true] at this
    obtain ⟨r, hr, he⟩ := this
    exact ⟨r, lt_of_mem_l32 hr, beq_iff_eq.1 he⟩
  · have := List.all_eq_true.1 (List.all_eq_true.1 h2 r (mem_l32 hr)) s (mem_l32 hs)
    simp only [he, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    exact this
  · have := List.all_eq_true.1 h3 r (mem_l32 hr)
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at this
    exact ⟨this.1, fun s hs => this.2 s (mem_l32 hs)⟩
  · have := List.all_eq_true.1 h4 c (mem_l256 hc)
    have ha' : ([1, 2, 16, 32, 128].all fun a => commS D c a) = true := List.all_eq_true.2 ha
    simp only [ha', Bool.not_true, Bool.false_or] at this
    exact this

theorem mem_Asp_iff (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true) {g : Msp} :
    g ∈ Asp ↔ ∃ r < 32, spPhi r = g := by
  constructor
  · intro hg
    have hg4 := (cl_facts hc).2.2.2
    have hle : Asp ≤ subS D (memA D) ht (cl_facts hc).1 := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      simp only [Set.mem_setOf_eq, gensAsp, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, by norm_num, hg4 1 (by simp), elS_1⟩
      · exact ⟨2, by norm_num, hg4 2 (by simp), elS_2⟩
      · exact ⟨16, by norm_num, hg4 16 (by simp), elS_16⟩
      · exact ⟨32, by norm_num, hg4 32 (by simp), elS_32⟩
      · exact ⟨128, by norm_num, hg4 128 (by simp), elS_128⟩
    obtain ⟨c, hc', hm, rfl⟩ := hle hg
    obtain ⟨r, hr, rfl⟩ := (a_facts ha).1 c hc' hm
    exact ⟨r, hr, (elS_phiS ht r).symm⟩
  · rintro ⟨r, -, rfl⟩
    have hA : ∀ g ∈ gensAsp, g ∈ Asp := fun g hg => gen_mem hg
    exact spPhi_mem (hA _ (by simp [gensAsp])) (hA _ (by simp [gensAsp]))
      (hA _ (by simp [gensAsp])) (hA _ (by simp [gensAsp])) (hA _ (by simp [gensAsp])) r

theorem spPhi_injective (ht : tabOK D = true) (ha : aOK D = true) {r s : ℕ} (hr : r < 32)
    (hs : s < 32) (h : spPhi r = spPhi s) : r = s := by
  rw [← elS_phiS ht, ← elS_phiS ht] at h
  exact (a_facts ha).2.1 r hr s hs (elS_injective ht (mulS_lt _ _) (mulS_lt _ _) h)

theorem card_Asp (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true) :
    Nat.card Asp = 32 :=
  card_of_param spPhi (fun _ => mem_Asp_iff ht hc ha) fun _ hk _ hl h =>
    spPhi_injective ht ha hk hl h

theorem Asp_comm (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true) {a b : Msp}
    (hxa : a ∈ Asp) (hxb : b ∈ Asp) : a * b = b * a := by
  obtain ⟨r, hr, rfl⟩ := (mem_Asp_iff ht hc ha).1 hxa
  obtain ⟨s, hs, rfl⟩ := (mem_Asp_iff ht hc ha).1 hxb
  rw [← elS_phiS ht, ← elS_phiS ht]
  exact (commS_iff ht).1 (((a_facts ha).2.2.1 r hr).2 s hs)

theorem Asp_sq (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true) {a : Msp}
    (hxa : a ∈ Asp) : a * a = 1 := by
  obtain ⟨r, hr, rfl⟩ := (mem_Asp_iff ht hc ha).1 hxa
  rw [← elS_phiS ht, ← elS_mulS ht, ((a_facts ha).2.2.1 r hr).1, elS_zero]

theorem mem_Asp_of_commute (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true)
    {s : Msp} (hs : s ∈ Tsp) (h : ∀ a ∈ Asp, s * a = a * s) : s ∈ Asp := by
  obtain ⟨c, hc', rfl⟩ := (mem_Tsp_iff ht).1 hs
  have hm : memA D c = true := by
    refine (a_facts ha).2.2.2 c hc' fun a hx => ?_
    have hx4 := (cl_facts hc).2.2.2 a hx
    have hlt : a < 256 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    obtain ⟨r, hr, hra⟩ := (a_facts ha).1 a hlt hx4
    refine (commS_iff ht).2 (h _ ((mem_Asp_iff ht hc ha).2 ⟨r, hr, ?_⟩))
    rw [← elS_phiS ht, hra]
  obtain ⟨r, hr, rfl⟩ := (a_facts ha).1 c hc' hm
  exact (mem_Asp_iff ht hc ha).2 ⟨r, hr, (elS_phiS ht r).symm⟩

theorem mem_Esp_iff (ht : tabOK D = true) (hc : clOK D = true) {g : Msp} :
    g ∈ Esp ↔ ∃ c < 16, elS c = g := by
  constructor
  · intro hg
    have hle : Esp ≤ subS D (fun c => decide (c < 16)) ht (cl_facts hc).2.2.1 := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      simp only [Set.mem_setOf_eq, gensEsp, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨1, by norm_num, rfl, elS_1⟩
      · exact ⟨2, by norm_num, rfl, elS_2⟩
      · exact ⟨4, by norm_num, rfl, elS_4⟩
      · exact ⟨8, by norm_num, rfl, elS_8⟩
    obtain ⟨c, -, hm, rfl⟩ := hle hg
    exact ⟨c, of_decide_eq_true hm, rfl⟩
  · rintro ⟨c, hc', rfl⟩
    have hE : ∀ g ∈ gensEsp, g ∈ Esp := fun g hg => gen_mem hg
    have h0 : c / 16 % 16 = 0 := by omega
    rw [elS, h0, pPhi_zero, mul_one]
    exact ePhi_mem (hE _ (by simp [gensEsp])) (hE _ (by simp [gensEsp]))
      (hE _ (by simp [gensEsp])) (hE _ (by simp [gensEsp])) _

theorem card_Esp (ht : tabOK D = true) (hc : clOK D = true) : Nat.card Esp = 16 :=
  card_of_param elS (fun _ => mem_Esp_iff ht hc) fun _ hk _ hl h =>
    elS_injective ht (by omega) (by omega) h

theorem red_facts (hr : redOK D = true) (hs : sgOK D = true) {c : ℕ} (hc : c < 256)
    (hm : memA D c = false) : ∃ s < 256, memA D (conjS D s c) = false ∧
      (sgOf D (cenS D l256 (conjS D s c))).length ≤ 16 := by
  have h1 := List.all_eq_true.1 hr c (mem_l256 hc)
  simp only [hm, Bool.false_or, List.any_eq_true] at h1
  obtain ⟨s, hs', hrep⟩ := h1
  have hslt : s < 256 := by
    simp only [l256, List.mem_flatMap, List.mem_map, l16, List.mem_cons, List.not_mem_nil,
      or_false] at hs'
    omega
  have hlt : conjS D s c < 256 := mulS_lt _ _
  have h2 := List.all_eq_true.1 hs _ (mem_l256 hlt)
  simp only [hrep, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h2
  exact ⟨s, hslt, h2.1, h2.2⟩

theorem Asp_unique (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true)
    (hr : redOK D = true) (hs : sgOK D = true) (B : Subgroup Msp) (hB : B ≤ Tsp)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hcard : Nat.card B = 32) : B = Asp := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcard, card_Asp ht hc ha])
  intro g hg
  by_contra hgA
  obtain ⟨c, hc', rfl⟩ := (mem_Tsp_iff ht).1 (hB hg)
  have hm : memA D c = false := by
    by_contra hm'
    obtain ⟨r, hr', rfl⟩ := (a_facts ha).1 c hc' (by simpa using hm')
    exact hgA ((mem_Asp_iff ht hc ha).2 ⟨r, hr', (elS_phiS ht r).symm⟩)
  obtain ⟨s, hs', -, hlen⟩ := red_facts hr hs hc' hm
  set t := elS s
  set k := conjS D s c
  have htT : t ∈ Tsp := (mem_Tsp_iff ht).2 ⟨s, hs', rfl⟩
  let f : Msp → Msp := fun b => t * b * t⁻¹
  have hf : Function.Injective f := fun x y h => by
    simpa [f] using h
  have hS : (f '' (B : Set Msp)).ncard = 32 := by
    rw [Set.ncard_image_of_injective _ hf, ← Nat.card_coe_set_eq]
    exact hcard
  have hfT : ∀ b ∈ B, ∃ m < 256, elS m = f b := fun b hb =>
    (mem_Tsp_iff ht).1 (mul_mem (mul_mem htT (hB hb)) (inv_mem htT))
  have hfc : ∀ b ∈ B, ∀ b' ∈ B, f b * f b' = f b' * f b := fun b hb b' hb' => by
    simp only [f, mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc b, hcomm b hb b' hb', mul_assoc]
  have hk : elS k = f (elS c) := elS_conjS ht s c
  have hC : ∀ b ∈ B, ∀ m < 256, elS m = f b → m ∈ cenS D l256 k := fun b hb m hm hmb => by
    simp only [cenS, List.mem_filter]
    refine ⟨mem_l256 hm, (commS_iff ht).2 ?_⟩
    rw [hk, hmb]
    exact hfc _ hg _ hb
  have hsg : ∀ b ∈ B, ∀ m < 256, elS m = f b → m ∈ sgOf D (cenS D l256 k) := fun b hb m hm hmb => by
    simp only [sgOf, List.mem_filter, decide_eq_true_eq]
    refine ⟨hC b hb m hm hmb, ?_⟩
    rw [← hS]
    refine ncard_le_length _ fun g' hg' => ?_
    obtain ⟨b', hb', rfl⟩ := hg'
    obtain ⟨m', hm', hm'b⟩ := hfT b' hb'
    refine ⟨m', List.mem_filter.2 ⟨hC b' hb' m' hm' hm'b, (commS_iff ht).2 ?_⟩, hm'b⟩
    rw [hmb, hm'b]
    exact hfc _ hb _ hb'
  have h32 : 32 ≤ (sgOf D (cenS D l256 k)).length := by
    rw [← hS]
    refine ncard_le_length _ fun g' hg' => ?_
    obtain ⟨b', hb', rfl⟩ := hg'
    obtain ⟨m', hm', hm'b⟩ := hfT b' hb'
    exact ⟨m', hsg b' hb' m' hm' hm'b, hm'b⟩
  omega

end CFSG.KC.Stroth77SP
