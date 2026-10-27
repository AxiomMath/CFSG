module

public import CFSG.Certificates.Kernel.Sp62Pk.Sound
public import Certificates.Data.Kernel.Sp6TwoK
public import Certificates.Data.Kernel.Sp6TwoT

public section

namespace CFSG.KC.Sp6Two

open CFSG.KD.Sp62 CFSG.KD.Sp6Two CFSG.KC.Sp62 CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

theorem tableG {start : List ℕ} {mul : List ℕ → List ℕ → List ℕ} {gens : List (List ℕ)}
    {fuel n k hiB hiS hiT : ℕ} {st : ℕ → ℕ → ℕ} {X PA PB C POS SRT SRI : ℕ → ℕ}
    (hk : gens.length = k) (hk0 : 0 < k) (hn : 0 < n) (hfuel : n ≤ fuel)
    (hst : ∀ x, canon6 x = true → ∀ s < k, ∀ d : List ℕ,
      canon6 (mul x (gens.getD s d)) = true ∧ pk (mul x (gens.getD s d)) = st (pk x) s)
    (h0 : canon6 start = true ∧ pk start = X 0)
    (hB : buildG st X PA PB n k hiB = true) (hBm : n - 1 ≤ 64 * hiB)
    (hS : stepG st X PA PB C POS n k hiS = true) (hSm : n * k ≤ 64 * hiS)
    (hT : CFSG.KD.G2Three.sortK X SRT SRI n hiT = true) (hTm : n ≤ 64 * hiT) :
    bfsParents start mul gens fuel = (List.range (n - 1)).map (fun i => (PA i, PB i)) ∧
    (∀ ps ∈ (List.range (n - 1)).map (fun i => (PA i, PB i)), ps.2 < k) ∧
    (build start mul gens ((List.range (n - 1)).map (fun i => (PA i, PB i)))).size = n ∧
    closedCheck mul gens (build start mul gens ((List.range (n - 1)).map
      (fun i => (PA i, PB i)))) = true ∧
    distinctCheck (build start mul gens ((List.range (n - 1)).map (fun i => (PA i, PB i)))) =
      true ∧
    ∀ t < n, canon6 ((build start mul gens ((List.range (n - 1)).map
        (fun i => (PA i, PB i)))).getD t []) = true ∧
      pk ((build start mul gens ((List.range (n - 1)).map
        (fun i => (PA i, PB i)))).getD t []) = X t := by
  have hBi := build_at6 hB hBm
  obtain ⟨hC0, hCn, hSi⟩ := step_facts6 hS hSm
  have hX := CFSG.KC.G2Three.sort_inj hT hTm
  generalize hPL : (List.range (n - 1)).map (fun i => (PA i, PB i)) = PL
  have hPLlen : PL.length = n - 1 := by rw [← hPL]; simp
  have hPLget : ∀ i < n - 1, PL.getD i (0, 0) = (PA i, PB i) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by rw [hPLlen]; exact hi)]
    simp [← hPL]
  have hPL2 : ∀ ps ∈ PL, ps.2 < k := by
    intro ps hps
    rw [← hPL] at hps
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hps
    exact (hBi i (List.mem_range.1 hi)).2.1
  have key := push_table6 (start := start) (K := k)
    (step := fun x ps => mul x (gens.getD ps.2 start))
    (stepP := fun x ps => st x ps.2) (X := X)
    (fun x ps hx hs => hst x hx ps.2 hs start) PL #[start]
    (fun i hi => by
      rw [hPLlen] at hi
      obtain ⟨h1, h2, h3⟩ := hBi i hi
      rw [hPLget i hi]
      simp only [List.size_toArray, List.length_singleton]
      exact ⟨by omega, h2, by rw [Nat.add_comm]; exact h3⟩)
    (fun t ht => by
      have : t = 0 := by simpa using ht
      subst this
      exact ⟨by simpa using h0.1, by simpa using h0.2⟩)
  simp only [List.size_toArray, List.length_singleton] at key
  have hEsz : (build start mul gens PL).size = n := key.1.trans (by rw [hPLlen]; omega)
  have hrec : ∀ t < n, canon6 ((build start mul gens PL).getD t start) = true ∧
      pk ((build start mul gens PL).getD t start) = X t :=
    fun t ht => key.2 t (by rw [hPLlen]; omega)
  have hrec' : ∀ t < n, canon6 ((build start mul gens PL).getD t []) = true ∧
      pk ((build start mul gens PL).getD t []) = X t := by
    intro t ht
    rw [CFSG.KC.G2Three.getD_irrel (by rw [hEsz]; exact ht) [] start]
    exact hrec t ht
  have hd : ∀ t < (build start mul gens PL).size, ∀ t' < (build start mul gens PL).size,
      (build start mul gens PL).getD t [] = (build start mul gens PL).getD t' [] → t = t' := by
    intro t ht t' ht' he
    rw [hEsz] at ht ht'
    exact hX t ht t' ht' (by rw [← (hrec' t ht).2, ← (hrec' t' ht').2, he])
  have hprod : ∀ h < n, ∀ s < k, (build start mul gens PL).getD (POS (h * k + s)) [] =
      mul ((build start mul gens PL).getD h []) (gens.getD s []) := by
    intro h hh s hs
    obtain ⟨hi, hdiv, hmod⟩ := CFSG.KC.G2Three.flat_facts hk0 hh hs
    obtain ⟨-, -, hp, hx, -, -⟩ := hSi _ hi
    rw [hdiv, hmod] at hx
    obtain ⟨ch, ph⟩ := hrec' h hh
    obtain ⟨cp, pp⟩ := hrec' _ hp
    obtain ⟨cm, pm⟩ := hst _ ch s hs []
    exact pk_inj cp cm (by rw [pp, hx, pm, ph])
  obtain ⟨C', hC'lo, hC'hi⟩ : ∃ C' : ℕ → ℕ, (∀ i ≤ n * k, C' i = C i) ∧
      ∀ i, n * k ≤ i → C' i = n := by
    refine ⟨fun i => if i ≤ n * k then C i else n, fun i hi => if_pos hi, fun i hi => ?_⟩
    by_cases h : i ≤ n * k
    · have e : i = n * k := by omega
      simp only [if_pos h]
      rw [e, hCn]
    · exact if_neg h
  have hstep : ∀ h < fuel, ∀ s < gens.length,
      CFSG.KC.G2Three.StepOK mul gens (build start mul gens PL) PL.toArray C' POS h s
        (h * gens.length + s) := by
    intro h _ s hs
    rw [hk] at hs ⊢
    by_cases hhn : h < n
    · obtain ⟨hi, hdiv, hmod⟩ := CFSG.KC.G2Three.flat_facts hk0 hhn hs
      obtain ⟨a, b, c, -, e, f⟩ := hSi _ hi
      rw [hdiv] at a
      unfold CFSG.KC.G2Three.StepOK
      rw [hC'lo _ hi.le, hC'lo (h * k + s + 1) hi]
      refine ⟨fun _ => ⟨b, by rw [hEsz]; exact c, hprod h hhn s hs, fun hpc => ?_,
        fun hlt => f (Nat.ne_of_lt hlt)⟩, fun hn' => absurd a hn'⟩
      obtain ⟨e1, e2, e3⟩ := e hpc
      rw [hdiv] at e2
      rw [hmod] at e3
      refine ⟨e1, ?_⟩
      have hlt : C (h * k + s) - 1 < n - 1 := by omega
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
        hPLget _ hlt, e2, e3]
    · have hnk : n * k ≤ h * k := Nat.mul_le_mul_right k (by omega)
      have hi : n * k ≤ h * k + s := by omega
      unfold CFSG.KC.G2Three.StepOK
      rw [hC'hi _ hi, hC'hi (h * k + s + 1) (by omega)]
      exact ⟨fun hlt => absurd hlt (by omega), fun _ => rfl⟩
  have hPs : PL.toArray.size + 1 = (build start mul gens PL).size := by
    rw [List.size_toArray, hPLlen, hEsz]
    omega
  have hpar : bfsParents start mul gens fuel = PL := by
    have hfk : n * k ≤ fuel * k := Nat.mul_le_mul_right k hfuel
    have := CFSG.KC.G2Three.bfsParents_replay (C := C') (POS := POS)
      (build_getD_zero start mul gens PL) (by omega) hd
      hPs (by rw [hC'lo 0 (by omega), hC0]) hstep
      (by rw [hk, hC'hi (fuel * k) hfk, hEsz])
    simpa using this
  refine ⟨hpar, hPL2, hEsz, CFSG.KC.G2Three.closedCheck_of fun v hv g hg' => ?_,
    CFSG.KC.G2Three.distinctCheck_of hd, hrec'⟩
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg'
  have hsk : s < k := by omega
  rw [hEsz] at hv
  refine ⟨POS (v * k + s), ?_, ?_⟩
  · rw [hEsz]
    exact (hSi _ (CFSG.KC.G2Three.flat_facts hk0 hv hsk).1).2.2.1
  · rw [hprod v hv s hsk, List.getD_eq_getElem _ _ hs]

theorem closureKG_ok {gens : List (List ℕ)} {G : ℕ → ℕ} {R : ℕ → ℕ} {o n k hiB hiS hiT : ℕ}
    (hk : gens.length = k) (hk0 : 0 < k) (hn : 0 < n) (hfuel : n ≤ 24000)
    (hg : ∀ s < k, canon6 (gens.getD s []) = true ∧ pk (gens.getD s []) = G s)
    (h : (Nat.beq (recX R o 0) ONE && tableKG R (rmulSt G) o n k hiB hiS hiT) = true)
    (hBm : n - 1 ≤ 64 * hiB) (hSm : n * k ≤ 64 * hiS) (hTm : n ≤ 64 * hiT) :
    closureOK gens (closureT gens) n = true ∧
      ∀ t < n, canon6 ((closureT gens).getD t []) = true ∧
        pk ((closureT gens).getD t []) = recX R o t := by
  simp only [tableKG, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, ⟨hB, hS⟩, hT⟩ := h
  obtain ⟨hpar, -, hsz, hcl, hdi, hrec⟩ := tableG (start := one6) (mul := mul6) (gens := gens)
    (fuel := 24000) hk hk0 hn hfuel
    (fun x hx s hs d => by
      rw [CFSG.KC.G2Three.listGetD_irrel (by rw [hk]; exact hs) d []]
      exact mulE ⟨hx, rfl⟩ (hg s hs))
    ⟨canon6_one6, by rw [pk_one6, h0]⟩ hB hBm hS hSm hT hTm
  have e : closureT gens = build one6 mul6 gens
      ((List.range (n - 1)).map (fun i => (recF R o 0 i, recF R o 1 i))) := by
    unfold closureT
    rw [hpar]
  rw [e]
  refine ⟨?_, hrec⟩
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨hsz, hcl⟩, hdi⟩, CFSG.KC.G2Three.allCheck_of fun t ht => (hrec t (by omega)).1⟩

theorem orbit6_rec {t0 : List ℕ} {gps : List (List ℕ)} {GA GB : ℕ → ℕ} {R : ℕ → ℕ}
    {fuel o a n hiB hiS hiT : ℕ} (hk : gps.length = 2) (hn : 0 < n) (hfuel : n ≤ fuel)
    (hg : ∀ s < 2, ∃ x y, gps.getD s [] = x ++ y ∧ (canon6 x = true ∧ pk x = GA s) ∧
      (canon6 y = true ∧ pk y = GB s))
    (ht0 : canon6 t0 = true ∧ pk t0 = R a)
    (h : (Nat.beq (recX R o 0) (R a) && tableK R (conjSt GA GB) o n hiB hiS hiT) = true)
    (hBm : n - 1 ≤ 64 * hiB) (hSm : n * 2 ≤ 64 * hiS) (hTm : n ≤ 64 * hiT) :
    orbitOK (orbitBuild6 t0 gps (orbitParents6 t0 gps fuel)) n = true ∧
      (orbitBuild6 t0 gps (orbitParents6 t0 gps fuel)).size = n ∧
      ∀ t < n, canon6 ((orbitBuild6 t0 gps (orbitParents6 t0 gps fuel)).getD t []) = true ∧
        pk ((orbitBuild6 t0 gps (orbitParents6 t0 gps fuel)).getD t []) = recX R o t := by
  simp only [tableK, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, ⟨hB, hS⟩, hT⟩ := h
  obtain ⟨hpar, hP2, hsz, -, hdi, hrec⟩ := table6 (start := t0)
    (mul := fun x gp => conjStep6 gp x) (gens := gps) (fuel := fuel) hk hn hfuel
    (fun x hx s hs d => by
      rw [CFSG.KC.G2Three.listGetD_irrel (by rw [hk]; exact hs) d []]
      obtain ⟨u, v, e, hu, hv⟩ := hg s hs
      rw [e]
      exact conj_pk hu hv ⟨hx, rfl⟩)
    ⟨ht0.1, by rw [ht0.2, h0]⟩ hB hBm hS hSm hT hTm
  have e : orbitBuild6 t0 gps (orbitParents6 t0 gps fuel) = build t0 (fun x gp => conjStep6 gp x)
      gps ((List.range (n - 1)).map (fun i => (recF R o 0 i, recF R o 1 i))) := by
    unfold orbitBuild6 orbitParents6 build
    rw [hpar]
    exact orbitBuild6_eq _ (fun ps hps => by rw [hk]; exact hP2 ps hps) _
  rw [e]
  simp only [orbitOK, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨hsz, hdi⟩, CFSG.KC.G2Three.allCheck_of fun t ht => (hrec t (by omega)).1⟩, hsz, hrec⟩

theorem pow512_pk {x : List ℕ} {A : ℕ} (hx : canon6 x = true ∧ pk x = A) :
    canon6 (pow512 x) = true ∧ pk (pow512 x) = P2K A 9 :=
  pow2k_pk hx 9

theorem centTest6 {E : Array (List ℕ)} {R : ℕ → ℕ} {o n hi PA PB T : ℕ} {t pa pb : List ℕ}
    (hpa : canon6 pa = true ∧ pk pa = PA) (hpb : canon6 pb = true ∧ pk pb = PB)
    (ht : canon6 t = true ∧ pk t = T) (hE : E.size = n)
    (hr : ∀ i < n, canon6 (E.getD i []) = true ∧ pk (E.getD i []) = recX R o i)
    (h : centK6 R o n PA PB T hi = true) (hm : n ≤ 64 * hi) :
    allCheck (centralP t pa pb) E = true := by
  refine CFSG.KC.G2Three.allCheck_of fun i hi' => ?_
  rw [hE] at hi'
  have hx := hr i hi'
  have hb := CFSG.KC.G2Three.allBelow_g2 h hm i hi'
  have ec : ∀ {b : List ℕ} {B : ℕ}, canon6 b = true ∧ pk b = B →
      commutes6 (E.getD i []) b = Nat.beq (MULF (recX R o i) B) (MULF B (recX R o i)) := by
    intro b B hbB
    unfold commutes6
    rw [beq_pk (mulE hx hbB).1 (mulE hbB hx).1, (mulE hx hbB).2, (mulE hbB hx).2]
  have ep : (pow512 (E.getD i []) == one6) = Nat.beq (P2K (recX R o i) 9) ONE := by
    rw [beq_pk (pow512_pk hx).1 canon6_one6, (pow512_pk hx).2, pk_one6]
  have e1 : (E.getD i [] == one6) = Nat.beq (recX R o i) ONE := by
    rw [beq_pk hx.1 canon6_one6, hx.2, pk_one6]
  have e2 : (E.getD i [] == t) = Nat.beq (recX R o i) T := by
    rw [beq_pk hx.1 ht.1, hx.2, ht.2]
  unfold centralP
  rw [ec hpa, ec hpb, ep, e1, e2]
  unfold centF at hb
  cases hq : (Nat.beq (MULF (recX R o i) PA) (MULF PA (recX R o i)) &&
      Nat.beq (MULF (recX R o i) PB) (MULF PB (recX R o i)) &&
      Nat.beq (P2K (recX R o i) 9) ONE)
  · rfl
  · rw [hq, cond_true] at hb
    simpa using hb

theorem found_of_inTab {O : Array (List ℕ)} {R : ℕ → ℕ} {o n i : ℕ} {u : List ℕ}
    (hO : O.size = n) (hr : ∀ t < n, canon6 (O.getD t []) = true ∧ pk (O.getD t []) = recX R o t)
    (hu : canon6 u = true) (h : inTab R o n i (pk u) = true) : found O (indexMap O) u = true := by
  simp only [inTab, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hi, he⟩ := h
  obtain ⟨c, p⟩ := hr i hi
  exact CFSG.KC.G2Three.found_indexMap.2 ⟨i, by rw [hO]; exact hi, pk_inj c hu (by rw [p, he])⟩

theorem invTest6 {S : Array (List ℕ)} {R I : ℕ → ℕ} {o n o0 n0 o1 n1 o2 n2 o3 n3 hi : ℕ}
    (hS : S.size = n)
    (hr : ∀ t < n, canon6 (S.getD t []) = true ∧ pk (S.getD t []) = recX R o t)
    (h0s : orbit0.size = n0)
    (h0r : ∀ t < n0, canon6 (orbit0.getD t []) = true ∧ pk (orbit0.getD t []) = recX R o0 t)
    (h1s : orbit1.size = n1)
    (h1r : ∀ t < n1, canon6 (orbit1.getD t []) = true ∧ pk (orbit1.getD t []) = recX R o1 t)
    (h2s : orbit2.size = n2)
    (h2r : ∀ t < n2, canon6 (orbit2.getD t []) = true ∧ pk (orbit2.getD t []) = recX R o2 t)
    (h3s : orbit3.size = n3)
    (h3r : ∀ t < n3, canon6 (orbit3.getD t []) = true ∧ pk (orbit3.getD t []) = recX R o3 t)
    (h : invK6 R I o n o0 n0 o1 n1 o2 n2 o3 n3 hi = true) (hm : n ≤ 64 * hi) :
    allCheck (invP (indexMap orbit0) (indexMap orbit1) (indexMap orbit2) (indexMap orbit3)) S =
      true := by
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  rw [hS] at ht
  obtain ⟨cx, px⟩ := hr t ht
  have hb := CFSG.KC.G2Three.allBelow_g2 h hm t ht
  have e1 : (mul6 (S.getD t []) (S.getD t []) == one6) =
      Nat.beq (MULF (recX R o t) (recX R o t)) ONE := by
    rw [beq_pk (mulE ⟨cx, px⟩ ⟨cx, px⟩).1 canon6_one6, (mulE ⟨cx, px⟩ ⟨cx, px⟩).2, pk_one6]
  have e2 : (S.getD t [] == one6) = Nat.beq (recX R o t) ONE := by
    rw [beq_pk cx canon6_one6, px, pk_one6]
  unfold invP
  rw [e1, e2]
  unfold invF at hb
  cases hq : Nat.beq (MULF (recX R o t) (recX R o t)) ONE
  · rfl
  · rw [hq, cond_true] at hb
    rw [← px] at hb
    simp only [Bool.or_eq_true] at hb
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true]
    rcases hb with (((hb | hb) | hb) | hb) | hb
    · exact Or.inl (Or.inl (Or.inl (Or.inl (by rw [← px]; exact hb))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (found_of_inTab h0s h0r cx hb))))
    · exact Or.inl (Or.inl (Or.inr (found_of_inTab h1s h1r cx hb)))
    · exact Or.inl (Or.inr (found_of_inTab h2s h2r cx hb))
    · exact Or.inr (found_of_inTab h3s h3r cx hb)

end CFSG.KC.Sp6Two

end
