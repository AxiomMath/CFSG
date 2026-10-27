module

public import CFSG.Certificates.Kernel.TcRes.MovedSound

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.TcRes.TK

@[expose] noncomputable def xs (u1 u2 i : ℕ) : ℕ := sel4 u1 u2 (lin u1 u2 1) (lin u1 u2 2) i

theorem cartanE_comm_ana (r : ℕ) (i j : Fin r) : Tag.cartanE r i j = Tag.cartanE r j i := by
  unfold Tag.cartanE
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem iform_comm_ana {τ : Tag} (hτ : τ = Tag.E6 ∨ τ = Tag.E8) (x y : Fin τ.rank → ℤ) :
    iform x y = iform y x := by
  have hB : ∀ i j, τ.symmetrizedCartan i j = τ.symmetrizedCartan j i := by
    rcases hτ with rfl | rfl <;> intro i j
    · change ((1 : Matrix (Fin 6) (Fin 6) ℤ) * Tag.cartanE 6) i j =
        ((1 : Matrix (Fin 6) (Fin 6) ℤ) * Tag.cartanE 6) j i
      rw [Matrix.one_mul]
      exact cartanE_comm_ana _ _ _
    · change ((1 : Matrix (Fin 8) (Fin 8) ℤ) * Tag.cartanE 8) i j =
        ((1 : Matrix (Fin 8) (Fin 8) ℤ) * Tag.cartanE 8) j i
      rw [Matrix.one_mul]
      exact cartanE_comm_ana _ _ _
  simp only [iform]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hB j i]
  ring

theorem ana_testBit_lt {N P x : ℕ} (hP : P < 2 ^ N) (h : P.testBit x = true) : x < N := by
  by_contra hx
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hP (Nat.pow_le_pow_right (by norm_num)
    (by omega)))] at h
  exact absurd h (by decide)

@[expose] def anaBlk {τ : Tag} (N : ℕ) (vec : ℕ → Fin τ.rank → ℤ) (ph : ℕ → ℕ) (S : Set ℕ)
    (J : ℕ → ℕ → Prop) (C r : ℕ) : Prop :=
  r ∈ mset N C ∧ mset N C ⊆ S ∧
    (∀ h ∈ mset N C, Relation.ReflTransGen
      (fun a b => a ∈ mset N C ∧ b ∈ mset N C ∧ iform (vec a) (vec b) ≠ 0) r h) ∧
    (∀ a ∈ mset N C, ∀ b ∈ S, iform (vec a) (vec b) ≠ 0 → b ∈ mset N C) ∧
    0 < olen ph C 12 r 1 ∧ (olen ph C 12 r 1 = 1 ∨ J C r)

@[expose] def AnaInv {τ : Tag} (N : ℕ) (vec : ℕ → Fin τ.rank → ℤ) (ph : ℕ → ℕ)
    (J : ℕ → ℕ → Prop) (P ADJ acc C rt NB : ℕ) : Prop :=
  (∀ x, acc.testBit x = true → C.testBit x = true ∨
      ∃ C0 r0, x ∈ mset N C0 ∧ anaBlk N vec ph (mset N P) J C0 r0) ∧
  (C ≠ 0 → C.testBit rt = true ∧ ∀ x, C.testBit x = true → P.testBit x = true ∧
      Relation.ReflTransGen
        (fun a b => a ∈ mset N C ∧ b ∈ mset N C ∧ iform (vec a) (vec b) ≠ 0) rt x ∧
      ∀ b, (fld ADJ N x).testBit b = true → NB.testBit b = true)

theorem anaBlk_of_fin {τ : Tag} {N : ℕ} {vec : ℕ → Fin τ.rank → ℤ} {ph : ℕ → ℕ}
    {J : ℕ → ℕ → Prop} {ADJ P mv C rt NB : ℕ} (hP : P < 2 ^ N)
    (hadj : ∀ a < N, ∀ b < N, iform (vec a) (vec b) ≠ 0 → (fld ADJ N a).testBit b = true)
    (hC : C ≠ 0)
    (hI : C.testBit rt = true ∧ ∀ x, C.testBit x = true → P.testBit x = true ∧
      Relation.ReflTransGen
        (fun a b => a ∈ mset N C ∧ b ∈ mset N C ∧ iform (vec a) (vec b) ≠ 0) rt x ∧
      ∀ b, (fld ADJ N x).testBit b = true → NB.testBit b = true)
    (hfin : finOK ph P mv C rt NB = true) (hol : 0 < olen ph C 12 rt 1)
    (hJ : olen ph C 12 rt 1 = 1 ∨ J C rt) : anaBlk N vec ph (mset N P) J C rt := by
  obtain ⟨hrt, hall⟩ := hI
  have hmem : ∀ x, x ∈ mset N C ↔ C.testBit x = true := fun x =>
    ⟨fun h => Lane.bit_iff.1 h.2, fun h => ⟨ana_testBit_lt hP (hall x h).1, Lane.bit_iff.2 h⟩⟩
  simp only [finOK, Lane.orB_eq_true, Lane.beq_eq_true, Lane.strictB_eq, Lane.andB_eq_true,
    Lane.nland] at hfin
  have hcl : (NB &&& P) &&& C = NB &&& P := by
    rcases hfin with h | ⟨h, -⟩
    · exact absurd h hC
    · exact h
  refine ⟨(hmem rt).2 hrt, fun x hx => ?_, fun h hh => (hall h ((hmem h).1 hh)).2.1,
    fun a ha b hb hab => ?_, hol, hJ⟩
  · have := (hall x ((hmem x).1 hx)).1
    exact ⟨ana_testBit_lt hP this, Lane.bit_iff.2 this⟩
  · have hNB := (hall a ((hmem a).1 ha)).2.2 b (hadj a ha.1 b hb.1 hab)
    have hbP := Lane.bit_iff.1 hb.2
    refine (hmem b).2 ?_
    have : ((NB &&& P) &&& C).testBit b = true := by
      rw [hcl, Nat.testBit_and, hNB, hbP]
      rfl
    rw [Nat.testBit_and, Bool.and_eq_true] at this
    exact this.2

theorem aWalk_succ (RT X Y ADJ POS DEC : ℕ) (ph LS : ℕ → ℕ) (q P u1 u2 A c rest C rt i : ℕ) :
    aWalk RT X Y ADJ POS DEC ph LS q P u1 u2 A (c + 1) rest C rt i =
      Bool.rec (motive := fun _ => Bool)
        (aWalk RT X Y ADJ POS DEC ph LS q P u1 u2 A c (rest >>> 14)
          (C ||| 1 <<< (rest &&& 127)) rt i)
        (Bool.rec (motive := fun _ => Bool)
          (compEnd RT X Y ADJ POS DEC ph LS q P u1 u2 A C rt i fun j =>
            aWalk RT X Y ADJ POS DEC ph LS q P u1 u2 A c (rest >>> 14) (1 <<< (rest &&& 127))
              (rest &&& 127) j)
          (aWalk RT X Y ADJ POS DEC ph LS q P u1 u2 A c (rest >>> 14) (1 <<< (rest &&& 127))
            (rest &&& 127) i)
          (Nat.beq C 0))
        (Nat.beq (rest &&& 127) ((rest >>> 7) &&& 127)) := by
  simp only [aWalk, Lane.strictB_eq]
  rfl

theorem compEnd_spec {RT X Y ADJ POS DEC : ℕ} {ph LS : ℕ → ℕ} {q P u1 u2 A C rt i : ℕ}
    {k : ℕ → Bool} (h : compEnd RT X Y ADJ POS DEC ph LS q P u1 u2 A C rt i k = true) :
    0 < olen ph C 12 rt 1 ∧ (olen ph C 12 rt 1 = 1 ∨
      ∃ jb, jbOK RT X Y ADJ POS DEC ph LS q P u1 u2 C rt jb = true) ∧ ∃ j, k j = true := by
  simp only [compEnd, Lane.strictB_eq, Lane.andB_eq_true, Lane.blt_eq_true, Lane.boolRec_true,
    Lane.beq_eq_true, Lane.beq_eq_false] at h
  obtain ⟨hpos, h1, h2⟩ := h
  by_cases he : olen ph C 12 rt 1 = 1
  · exact ⟨hpos, Or.inl he, _, h1 he⟩
  · obtain ⟨hj, hk⟩ := h2 he
    exact ⟨hpos, Or.inr ⟨_, hj⟩, _, hk⟩

theorem anaWalk_spec {vec : ℕ → Fin Tag.E6.rank → ℤ} {RT X Y ADJ POS DEC P mv q u1 u2 A : ℕ}
    {ph LS : ℕ → ℕ} (hP : P < 2 ^ 72)
    (hadj : ∀ a < 72, ∀ b < 72, iform (vec a) (vec b) ≠ 0 → (fld ADJ 72 a).testBit b = true)
    (hadj' : ∀ g < 72, ∀ pa < 72, (fld ADJ 72 g).testBit pa = true →
      iform (vec pa) (vec g) ≠ 0) :
    ∀ c rest acc C rt NB i,
      AnaInv 72 vec ph (fun C r => ∃ jb, jbOK RT X Y ADJ POS DEC ph LS q P u1 u2 C r jb = true)
        P ADJ acc C rt NB →
      entWalk ADJ ph P mv c rest acc C rt NB = true →
      aWalk RT X Y ADJ POS DEC ph LS q P u1 u2 A c rest C rt i = true →
      ∀ g, P.testBit g = true → ∃ C0 r0, g ∈ mset 72 C0 ∧ anaBlk 72 vec ph (mset 72 P)
        (fun C r => ∃ jb, jbOK RT X Y ADJ POS DEC ph LS q P u1 u2 C r jb = true) C0 r0 := by
  intro c
  induction c with
  | zero =>
    intro rest acc C rt NB i hI hE hA g hg
    change CFSG.TcRes.TK.andB (finOK ph P mv C rt NB) (Nat.beq acc P) = true at hE
    rw [Lane.andB_eq_true, Lane.beq_eq_true] at hE
    obtain ⟨hfin, hacc⟩ := hE
    rw [hacc] at hI
    have hA' : compEnd RT X Y ADJ POS DEC ph LS q P u1 u2 A C rt i
        (fun j => Nat.beq j (Nat.land A 255)) = true := hA
    obtain ⟨hol, hJ, -⟩ := compEnd_spec hA'
    rcases hI.1 g hg with h | h
    · have hC : C ≠ 0 := fun h0 => by
        rw [h0, Nat.zero_testBit] at h
        exact absurd h (by decide)
      exact ⟨C, rt, ⟨ana_testBit_lt hP hg, Lane.bit_iff.2 h⟩,
        anaBlk_of_fin hP hadj hC (hI.2 hC) hfin hol hJ⟩
    · exact h
  | succ c ih =>
    intro rest acc C rt NB i hI hE hA
    rw [entWalk_succ] at hE
    rw [aWalk_succ] at hA
    simp only [Lane.andB_eq_true, Lane.notB_eq_true, Lane.boolRec_true, Lane.beq_eq_true,
      Lane.beq_eq_false] at hE hA
    obtain ⟨hPg, -, hroot, hnon⟩ := hE
    rw [Lane.bit_iff] at hPg
    obtain ⟨hAroot, hAnon⟩ := hA
    by_cases hgp : (rest &&& 127) = ((rest >>> 7) &&& 127)
    · obtain ⟨hfin, hw⟩ := hroot hgp
      have key : ∀ j, (∀ x, C.testBit x = true → ∃ C0 r0, x ∈ mset 72 C0 ∧
            anaBlk 72 vec ph (mset 72 P) (fun C r => ∃ jb,
              jbOK RT X Y ADJ POS DEC ph LS q P u1 u2 C r jb = true) C0 r0) →
          aWalk RT X Y ADJ POS DEC ph LS q P u1 u2 A c (rest >>> 14) (1 <<< (rest &&& 127))
            (rest &&& 127) j = true →
          ∀ g, P.testBit g = true → ∃ C0 r0, g ∈ mset 72 C0 ∧ anaBlk 72 vec ph (mset 72 P)
            (fun C r => ∃ jb, jbOK RT X Y ADJ POS DEC ph LS q P u1 u2 C r jb = true) C0 r0 := by
        intro j hCb hw'
        refine ih _ _ _ _ _ j ⟨fun x hx => ?_, fun _ => ⟨?_, fun x hx => ?_⟩⟩ hw hw'
        · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
          rcases hx with hx | rfl
          · rcases hI.1 x hx with h | h
            · exact Or.inr (hCb x h)
            · exact Or.inr h
          · exact Or.inl (by rw [pow_testBit, decide_eq_true rfl])
        · rw [pow_testBit, decide_eq_true rfl]
        · rw [pow_testBit, decide_eq_true_eq] at hx
          subst hx
          exact ⟨hPg, Relation.ReflTransGen.refl, fun b hb => hb⟩
      by_cases hC : C = 0
      · refine key i (fun x hx => ?_) ((hAroot hgp).1 hC)
        rw [hC, Nat.zero_testBit] at hx
        exact absurd hx (by decide)
      · obtain ⟨hol, hJ, j, hj⟩ := compEnd_spec ((hAroot hgp).2 hC)
        exact key j (fun x hx => ⟨C, rt, ⟨ana_testBit_lt hP ((hI.2 hC).2 x hx).1,
          Lane.bit_iff.2 hx⟩, anaBlk_of_fin hP hadj hC (hI.2 hC) hfin hol hJ⟩) hj
    · obtain ⟨hCpa, hag, hw⟩ := hnon hgp
      rw [Lane.bit_iff] at hCpa hag
      have hC : C ≠ 0 := fun h0 => by
        rw [h0, Nat.zero_testBit] at hCpa
        exact absurd hCpa (by decide)
      obtain ⟨hrt, hall⟩ := hI.2 hC
      have hsub : ∀ y, y ∈ mset 72 C → y ∈ mset 72 (C ||| 1 <<< (rest &&& 127)) := fun y hy =>
        ⟨hy.1, by rw [Lane.bit_iff, testBit_or_pow, Lane.bit_iff.1 hy.2]; rfl⟩
      have hmono : ∀ y, Relation.ReflTransGen
          (fun a b => a ∈ mset 72 C ∧ b ∈ mset 72 C ∧ iform (vec a) (vec b) ≠ 0) rt y →
          Relation.ReflTransGen (fun a b => a ∈ mset 72 (C ||| 1 <<< (rest &&& 127)) ∧
            b ∈ mset 72 (C ||| 1 <<< (rest &&& 127)) ∧ iform (vec a) (vec b) ≠ 0) rt y :=
        fun y h => Relation.ReflTransGen.mono
          (fun a b hab => ⟨hsub a hab.1, hsub b hab.2.1, hab.2.2⟩) _ _ h
      have hgN : (rest &&& 127) < 72 := ana_testBit_lt hP hPg
      have hpaN : ((rest >>> 7) &&& 127) < 72 := ana_testBit_lt hP (hall _ hCpa).1
      refine ih _ _ _ _ _ i ⟨fun x hx => ?_, fun _ => ⟨?_, fun x hx => ?_⟩⟩ hw (hAnon hgp)
      · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
        rcases hx with hx | rfl
        · rcases hI.1 x hx with h | h
          · exact Or.inl (by rw [testBit_or_pow, h]; rfl)
          · exact Or.inr h
        · exact Or.inl (by rw [testBit_or_pow]; simp)
      · rw [testBit_or_pow, hrt]
        rfl
      · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
        rcases hx with hx | rfl
        · obtain ⟨h1, h2, h3⟩ := hall x hx
          exact ⟨h1, hmono x h2, fun b hb => by rw [Nat.testBit_or, h3 b hb]; rfl⟩
        · refine ⟨hPg, ?_, fun b hb => by rw [Nat.testBit_or, hb, Bool.or_true]⟩
          exact Relation.ReflTransGen.tail (hmono _ (hall _ hCpa).2.1)
            ⟨hsub _ ⟨hpaN, Lane.bit_iff.2 hCpa⟩, ⟨hgN, by rw [Lane.bit_iff, testBit_or_pow]; simp⟩,
              hadj' _ hgN _ hpaN hag⟩

theorem anaBlocks_of_checks {vec : ℕ → Fin Tag.E6.rank → ℤ} {rt : ℕ → ℕ → ℕ} {neg : ℕ → ℕ}
    {RT X Y ADJ POS DEC NEG PW e A : ℕ} {RC LS : ℕ → ℕ}
    (hD : DatumRaw Tag.E6 72 vec rt (fun g v => Nat.beq (fld (fld ADJ 72 g) 1 v) 1) neg)
    (hP : kmask RC (pu1 e) (pu2 e) < 2 ^ 72)
    (hpl : plOK RC ADJ PW NEG e = true) (hana : anaOK RT X Y ADJ POS DEC NEG PW RC LS e A = true) :
    ∀ g ∈ mset 72 (kmask RC (pu1 e) (pu2 e)), ∃ C r, g ∈ mset 72 C ∧ r ∈ mset 72 C ∧
      mset 72 C ⊆ mset 72 (kmask RC (pu1 e) (pu2 e)) ∧
      (∀ h ∈ mset 72 C, Relation.ReflTransGen
        (fun a b => a ∈ mset 72 C ∧ b ∈ mset 72 C ∧ iform (vec a) (vec b) ≠ 0) r h) ∧
      (∀ a ∈ mset 72 C, ∀ b ∈ mset 72 (kmask RC (pu1 e) (pu2 e)),
        iform (vec a) (vec b) ≠ 0 → b ∈ mset 72 C) ∧
      0 < olen (phq PW NEG (pq e)) C 12 r 1 ∧
      (olen (phq PW NEG (pq e)) C 12 r 1 = 1 ∨ ∃ jb, jbOK RT X Y ADJ POS DEC (phq PW NEG (pq e)) LS
        (pq e) (kmask RC (pu1 e) (pu2 e)) (pu1 e) (pu2 e) C r jb = true) := by
  have hsym := iform_comm_ana (τ := Tag.E6) (Or.inl rfl)
  simp only [plOK, anaOK, Lane.strictB_eq] at hpl hana
  intro g hg
  obtain ⟨C, r, hgC, hr, hsub, hpath, hcl, hol, hJ⟩ := anaWalk_spec (vec := vec) hP
    (fun a ha b hb h => Lane.fld_one_eq_one.1 (Lane.beq_eq_true.1
      ((hD.adj a ha b hb).2 (by rw [hsym]; exact h))))
    (fun g hg pa hpa h => (hD.adj g hg pa hpa).1 (Lane.beq_eq_true.2 (Lane.fld_one_eq_one.2 h)))
    _ _ 0 0 0 0 0 ⟨fun x hx => by rw [Nat.zero_testBit] at hx; exact absurd hx (by decide),
      fun h => absurd rfl h⟩ hpl hana g (Lane.bit_iff.1 hg.2)
  exact ⟨C, r, hgC, hr, hsub, hpath, hcl, hol, hJ⟩

theorem sel4_map (f : ℕ → ℕ) (a b c d i : ℕ) :
    f (sel4 a b c d i) = sel4 (f a) (f b) (f c) (f d) i := by
  simp only [sel4, brecN_eq, nbeq_eq]
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases h1 : i = 1
    · simp [h1]
    · by_cases h2 : i = 2
      · simp [h2]
      · simp [h0, h1, h2]

theorem leK_spec {LS : ℕ → ℕ} {q g0 jb j x : ℕ} {k : ℕ → ℕ → Bool}
    (h : leK LS q g0 jb j x k = true) :
    leQ (LS (fld jb 8 (Nat.add 128 j))) = q ∧ leX (LS (fld jb 8 (Nat.add 128 j))) = x ∧
      bit (leP (LS (fld jb 8 (Nat.add 128 j)))) g0 = true ∧
      k (leP (LS (fld jb 8 (Nat.add 128 j)))) (leD (LS (fld jb 8 (Nat.add 128 j)))) = true := by
  rw [leK, strictB_eq, andB_eq, andB_eq, andB_eq] at h
  simp only [Bool.and_eq_true, nbeq_eq, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

structure LineRaw (vec : ℕ → Fin Tag.E6.rank → ℤ) (RT : ℕ) (ph : ℕ → ℕ) (RC : ℕ → ℕ)
    (g0 x E : ℕ) : Prop where
  x_eq : leX E = x
  g0_mem : g0 ∈ mset 72 (leP E)
  comp : ∃ g1 r1, CompRaw vec (fun g v => rtv RT g v) ph 72 (mset 72 (kv RC x))
    (mset 72 (leP E)) g1 (leD E) r1
  kind : KindRaw vec (fun g v => rtv RT g v) ph (mset 72 (leP E)) (leD E)

theorem bit_zero (g : ℕ) : bit 0 g = false := by
  simp [bit, nblt_eq]

theorem jbOK_spec {vec : ℕ → Fin Tag.E6.rank → ℤ} {neg : ℕ → ℕ}
    {RT X Y ADJ POS DEC NEG PW V : ℕ} {RC LS : ℕ → ℕ} {q P u1 u2 C g0 jb : ℕ}
    (hvec : vec = vecOf 6 V)
    (hD : DatumRaw Tag.E6 72 vec (fun g v => rtv RT g v)
      (fun g v => Nat.beq (fld (fld ADJ 72 g) 1 v) 1) neg)
    (hX : ∀ v < 72, ∀ g < 72, (CFSG.TcRes.TK.dP 6 (fld X 192 v * fld Y 192 g) : ℤ) -
      dQ 6 (fld X 192 v * fld Y 192 g) = iform (vec v) (vec g))
    (hpos : ∀ g < 72, posOK V POS g = true) (hdec : ∀ g < 72, decOK RT X Y POS DEC g = true)
    (hph : ∀ g < 72, phq PW NEG q g < 72)
    (hsub : ∀ Φ, (Φ = P ∨ ∃ x, Φ = kv RC x) → ∀ a ∈ mset 72 Φ, ∀ b ∈ mset 72 Φ, ∀ c < 72,
      vec c = vec a - vec b → c ∈ mset 72 Φ)
    (hls : ∀ ℓ < 256, LS ℓ = 0 ∨ lineOK RT X Y ADJ POS DEC NEG PW RC (LS ℓ) = true)
    (h : jbOK RT X Y ADJ POS DEC (phq PW NEG q) LS q P u1 u2 C g0 jb = true) :
    ∃ dJ r0, CompRaw vec (fun g v => rtv RT g v) (phq PW NEG q) 72 (mset 72 P) (mset 72 C) g0
        dJ r0 ∧ KindRaw vec (fun g v => rtv RT g v) (phq PW NEG q) (mset 72 C) dJ ∧
      2 ≤ dE dJ ∧ ∃ E0 E1 E2 E3 : ℕ,
        (∀ i < 4, LineRaw vec RT (phq PW NEG q) RC g0 (xs u1 u2 i) (sel4 E0 E1 E2 E3 i)) ∧
        jok (q % 3) C dJ (sel4 (leP E0) (leP E1) (leP E2) (leP E3))
          (sel4 (leD E0) (leD E1) (leD E2) (leD E3)) = true := by
  obtain ⟨ψ, d, r0, hk, hc, hkd⟩ := compRaw_of_cbK hvec hD hX hpos hdec hph
    (hsub P (Or.inl rfl)) h
  simp only [andB_eq, Bool.and_eq_true, nbeq_eq, decide_eq_true_eq, nble_eq] at hk
  obtain ⟨rfl, hd2, hk⟩ := hk
  have hg0 : g0 < 72 := hc.g0_mem.1
  have hline : ∀ (ℓ x : ℕ), ℓ < 256 → leQ (LS ℓ) = q → leX (LS ℓ) = x →
      bit (leP (LS ℓ)) g0 = true → LineRaw vec RT (phq PW NEG q) RC g0 x (LS ℓ) := by
    intro ℓ x hℓ hq hx hb
    have hE0 : LS ℓ ≠ 0 := by
      intro h0
      rw [h0] at hb
      simp [leP, bit_zero] at hb
    have hlo := (hls ℓ hℓ).resolve_left hE0
    simp only [lineOK, strictB_eq, andB_eq, Bool.and_eq_true] at hlo
    obtain ⟨-, hcb⟩ := hlo
    rw [hq, hx] at hcb
    obtain ⟨ψ', d', r1, hk', hc', hkd'⟩ := compRaw_of_cbK hvec hD hX hpos hdec hph
      (hsub _ (Or.inr ⟨x, rfl⟩)) hcb
    simp only [andB_eq, Bool.and_eq_true, nbeq_eq, decide_eq_true_eq] at hk'
    obtain ⟨rfl, rfl⟩ := hk'
    exact ⟨hx, ⟨hg0, hb⟩, ⟨_, r1, hc'⟩, hkd'⟩
  obtain ⟨q0, x0, b0, hk⟩ := leK_spec hk
  obtain ⟨q1, x1, b1, hk⟩ := leK_spec hk
  obtain ⟨q2, x2, b2, hk⟩ := leK_spec hk
  obtain ⟨q3, x3, b3, hk⟩ := leK_spec hk
  refine ⟨d, r0, hc, hkd, hd2, _, _, _, _, fun i hi => ?_, hk⟩
  have h8 : ∀ j, fld jb 8 (Nat.add 128 j) < 256 := fun j =>
    lt_of_lt_of_eq (CFSG.KC.TcRes.Lane.fld_lt _ 8 _) (by norm_num)
  have l0 := hline _ _ (h8 _) q0 x0 b0
  have l1 := hline _ _ (h8 _) q1 x1 b1
  have l2 := hline _ _ (h8 _) q2 x2 b2
  have l3 := hline _ _ (h8 _) q3 x3 b3
  interval_cases i
  · exact l0
  · exact l1
  · exact l2
  · exact l3

@[expose] noncomputable def xs5 (c1 c2 i : ℕ) : ℕ :=
  sel6 c1 (lin5 c1 c2 0) (lin5 c1 c2 1) (lin5 c1 c2 2) (lin5 c1 c2 3) (lin5 c1 c2 4) i

theorem entWalk8_succ (ADJ : ℕ) (ph : ℕ → ℕ) (P mv c rest acc C rt NB : ℕ) :
    entWalk8 ADJ ph P mv (c + 1) rest acc C rt NB =
      CFSG.TcRes.TK.andB (bit P (rest &&& 255)) (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (bit acc (rest &&& 255)))
        (Bool.rec (motive := fun _ => Bool)
          (CFSG.TcRes.TK.andB (bit C ((rest >>> 8) &&& 255)) (CFSG.TcRes.TK.andB (bit (fld ADJ 240 (rest &&& 255))
              ((rest >>> 8) &&& 255))
            (entWalk8 ADJ ph P mv c (rest >>> 16) (acc ||| 1 <<< (rest &&& 255))
              (C ||| 1 <<< (rest &&& 255)) rt (NB ||| fld ADJ 240 (rest &&& 255)))))
          (CFSG.TcRes.TK.andB (finOK ph P mv C rt NB)
            (entWalk8 ADJ ph P mv c (rest >>> 16) (acc ||| 1 <<< (rest &&& 255))
              (1 <<< (rest &&& 255)) (rest &&& 255) (fld ADJ 240 (rest &&& 255))))
          (Nat.beq (rest &&& 255) ((rest >>> 8) &&& 255)))) := by
  simp only [entWalk8, Lane.strictB_eq]
  rfl

theorem aWalk8_succ (ADJ POS DEC : ℕ) (ph LS : ℕ → ℕ) (s P c1 c2 A c rest C rt i : ℕ) :
    aWalk8 ADJ POS DEC ph LS s P c1 c2 A (c + 1) rest C rt i =
      Bool.rec (motive := fun _ => Bool)
        (aWalk8 ADJ POS DEC ph LS s P c1 c2 A c (rest >>> 16) (C ||| 1 <<< (rest &&& 255)) rt i)
        (Bool.rec (motive := fun _ => Bool)
          (compEnd8 ADJ POS DEC ph LS s P c1 c2 A C rt i fun j =>
            aWalk8 ADJ POS DEC ph LS s P c1 c2 A c (rest >>> 16) (1 <<< (rest &&& 255))
              (rest &&& 255) j)
          (aWalk8 ADJ POS DEC ph LS s P c1 c2 A c (rest >>> 16) (1 <<< (rest &&& 255))
            (rest &&& 255) i)
          (Nat.beq C 0))
        (Nat.beq (rest &&& 255) ((rest >>> 8) &&& 255)) := by
  simp only [aWalk8, Lane.strictB_eq]
  rfl

theorem compEnd8_spec {ADJ POS DEC : ℕ} {ph LS : ℕ → ℕ} {s P c1 c2 A C rt i : ℕ}
    {k : ℕ → Bool} (h : compEnd8 ADJ POS DEC ph LS s P c1 c2 A C rt i k = true) :
    0 < olen ph C 12 rt 1 ∧ (olen ph C 12 rt 1 = 1 ∨
      ∃ blk, jb8OK ADJ POS DEC ph LS s P c1 c2 C rt blk = true) ∧ ∃ j, k j = true := by
  simp only [compEnd8, Lane.strictB_eq, Lane.andB_eq_true, Lane.blt_eq_true, Lane.boolRec_true,
    Lane.beq_eq_true, Lane.beq_eq_false] at h
  obtain ⟨hpos, h1, h2⟩ := h
  by_cases he : olen ph C 12 rt 1 = 1
  · exact ⟨hpos, Or.inl he, _, h1 he⟩
  · obtain ⟨hj, hk⟩ := h2 he
    exact ⟨hpos, Or.inr ⟨_, hj⟩, _, hk⟩

theorem ana8Walk_spec {vec : ℕ → Fin Tag.E8.rank → ℤ} {ADJ POS DEC P mv s c1 c2 A : ℕ}
    {ph LS : ℕ → ℕ} (hP : P < 2 ^ 240)
    (hadj : ∀ a < 240, ∀ b < 240, iform (vec a) (vec b) ≠ 0 → (fld ADJ 240 a).testBit b = true)
    (hadj' : ∀ g < 240, ∀ pa < 240, (fld ADJ 240 g).testBit pa = true →
      iform (vec pa) (vec g) ≠ 0) :
    ∀ c rest acc C rt NB i,
      AnaInv 240 vec ph (fun C r => ∃ blk, jb8OK ADJ POS DEC ph LS s P c1 c2 C r blk = true)
        P ADJ acc C rt NB →
      entWalk8 ADJ ph P mv c rest acc C rt NB = true →
      aWalk8 ADJ POS DEC ph LS s P c1 c2 A c rest C rt i = true →
      ∀ g, P.testBit g = true → ∃ C0 r0, g ∈ mset 240 C0 ∧ anaBlk 240 vec ph (mset 240 P)
        (fun C r => ∃ blk, jb8OK ADJ POS DEC ph LS s P c1 c2 C r blk = true) C0 r0 := by
  intro c
  induction c with
  | zero =>
    intro rest acc C rt NB i hI hE hA g hg
    change CFSG.TcRes.TK.andB (finOK ph P mv C rt NB) (Nat.beq acc P) = true at hE
    rw [Lane.andB_eq_true, Lane.beq_eq_true] at hE
    obtain ⟨hfin, hacc⟩ := hE
    rw [hacc] at hI
    have hA' : compEnd8 ADJ POS DEC ph LS s P c1 c2 A C rt i
        (fun j => Nat.beq j (Nat.land A 255)) = true := hA
    obtain ⟨hol, hJ, -⟩ := compEnd8_spec hA'
    rcases hI.1 g hg with h | h
    · have hC : C ≠ 0 := fun h0 => by
        rw [h0, Nat.zero_testBit] at h
        exact absurd h (by decide)
      exact ⟨C, rt, ⟨ana_testBit_lt hP hg, Lane.bit_iff.2 h⟩,
        anaBlk_of_fin hP hadj hC (hI.2 hC) hfin hol hJ⟩
    · exact h
  | succ c ih =>
    intro rest acc C rt NB i hI hE hA
    rw [entWalk8_succ] at hE
    rw [aWalk8_succ] at hA
    simp only [Lane.andB_eq_true, Lane.notB_eq_true, Lane.boolRec_true, Lane.beq_eq_true,
      Lane.beq_eq_false] at hE hA
    obtain ⟨hPg, -, hroot, hnon⟩ := hE
    rw [Lane.bit_iff] at hPg
    obtain ⟨hAroot, hAnon⟩ := hA
    by_cases hgp : (rest &&& 255) = ((rest >>> 8) &&& 255)
    · obtain ⟨hfin, hw⟩ := hroot hgp
      have key : ∀ j, (∀ x, C.testBit x = true → ∃ C0 r0, x ∈ mset 240 C0 ∧
            anaBlk 240 vec ph (mset 240 P) (fun C r => ∃ blk,
              jb8OK ADJ POS DEC ph LS s P c1 c2 C r blk = true) C0 r0) →
          aWalk8 ADJ POS DEC ph LS s P c1 c2 A c (rest >>> 16) (1 <<< (rest &&& 255))
            (rest &&& 255) j = true →
          ∀ g, P.testBit g = true → ∃ C0 r0, g ∈ mset 240 C0 ∧ anaBlk 240 vec ph (mset 240 P)
            (fun C r => ∃ blk, jb8OK ADJ POS DEC ph LS s P c1 c2 C r blk = true) C0 r0 := by
        intro j hCb hw'
        refine ih _ _ _ _ _ j ⟨fun x hx => ?_, fun _ => ⟨?_, fun x hx => ?_⟩⟩ hw hw'
        · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
          rcases hx with hx | rfl
          · rcases hI.1 x hx with h | h
            · exact Or.inr (hCb x h)
            · exact Or.inr h
          · exact Or.inl (by rw [pow_testBit, decide_eq_true rfl])
        · rw [pow_testBit, decide_eq_true rfl]
        · rw [pow_testBit, decide_eq_true_eq] at hx
          subst hx
          exact ⟨hPg, Relation.ReflTransGen.refl, fun b hb => hb⟩
      by_cases hC : C = 0
      · refine key i (fun x hx => ?_) ((hAroot hgp).1 hC)
        rw [hC, Nat.zero_testBit] at hx
        exact absurd hx (by decide)
      · obtain ⟨hol, hJ, j, hj⟩ := compEnd8_spec ((hAroot hgp).2 hC)
        exact key j (fun x hx => ⟨C, rt, ⟨ana_testBit_lt hP ((hI.2 hC).2 x hx).1,
          Lane.bit_iff.2 hx⟩, anaBlk_of_fin hP hadj hC (hI.2 hC) hfin hol hJ⟩) hj
    · obtain ⟨hCpa, hag, hw⟩ := hnon hgp
      rw [Lane.bit_iff] at hCpa hag
      have hC : C ≠ 0 := fun h0 => by
        rw [h0, Nat.zero_testBit] at hCpa
        exact absurd hCpa (by decide)
      obtain ⟨hrt, hall⟩ := hI.2 hC
      have hsub : ∀ y, y ∈ mset 240 C → y ∈ mset 240 (C ||| 1 <<< (rest &&& 255)) := fun y hy =>
        ⟨hy.1, by rw [Lane.bit_iff, testBit_or_pow, Lane.bit_iff.1 hy.2]; rfl⟩
      have hmono : ∀ y, Relation.ReflTransGen
          (fun a b => a ∈ mset 240 C ∧ b ∈ mset 240 C ∧ iform (vec a) (vec b) ≠ 0) rt y →
          Relation.ReflTransGen (fun a b => a ∈ mset 240 (C ||| 1 <<< (rest &&& 255)) ∧
            b ∈ mset 240 (C ||| 1 <<< (rest &&& 255)) ∧ iform (vec a) (vec b) ≠ 0) rt y :=
        fun y h => Relation.ReflTransGen.mono
          (fun a b hab => ⟨hsub a hab.1, hsub b hab.2.1, hab.2.2⟩) _ _ h
      have hgN : (rest &&& 255) < 240 := ana_testBit_lt hP hPg
      have hpaN : ((rest >>> 8) &&& 255) < 240 := ana_testBit_lt hP (hall _ hCpa).1
      refine ih _ _ _ _ _ i ⟨fun x hx => ?_, fun _ => ⟨?_, fun x hx => ?_⟩⟩ hw (hAnon hgp)
      · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
        rcases hx with hx | rfl
        · rcases hI.1 x hx with h | h
          · exact Or.inl (by rw [testBit_or_pow, h]; rfl)
          · exact Or.inr h
        · exact Or.inl (by rw [testBit_or_pow]; simp)
      · rw [testBit_or_pow, hrt]
        rfl
      · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
        rcases hx with hx | rfl
        · obtain ⟨h1, h2, h3⟩ := hall x hx
          exact ⟨h1, hmono x h2, fun b hb => by rw [Nat.testBit_or, h3 b hb]; rfl⟩
        · refine ⟨hPg, ?_, fun b hb => by rw [Nat.testBit_or, hb, Bool.or_true]⟩
          exact Relation.ReflTransGen.tail (hmono _ (hall _ hCpa).2.1)
            ⟨hsub _ ⟨hpaN, Lane.bit_iff.2 hCpa⟩, ⟨hgN, by rw [Lane.bit_iff, testBit_or_pow]; simp⟩,
              hadj' _ hgN _ hpaN hag⟩

theorem ana8Blocks_of_checks {vec : ℕ → Fin Tag.E8.rank → ℤ} {rt : ℕ → ℕ → ℕ} {neg : ℕ → ℕ}
    {ADJ POS DEC PW e A : ℕ} {RC BS LS : ℕ → ℕ}
    (hD : DatumRaw Tag.E8 240 vec rt (fun g v => Nat.beq (fld (fld ADJ 240 g) 1 v) 1) neg)
    (hP : kmask5 RC (BS (Nat.land (Nat.shiftRight e 20) 1)) (Nat.land e 1023)
      (Nat.land (Nat.shiftRight e 10) 1023) < 2 ^ 240)
    (hpl : pl5OK RC BS ADJ PW e = true) (hana : ana8OK ADJ POS DEC PW RC BS LS e A = true) :
    ∀ g ∈ mset 240 (kmask5 RC (BS (Nat.land (Nat.shiftRight e 20) 1)) (Nat.land e 1023)
      (Nat.land (Nat.shiftRight e 10) 1023)), ∃ C r, g ∈ mset 240 C ∧ r ∈ mset 240 C ∧
      mset 240 C ⊆ mset 240 (kmask5 RC (BS (Nat.land (Nat.shiftRight e 20) 1)) (Nat.land e 1023)
        (Nat.land (Nat.shiftRight e 10) 1023)) ∧
      (∀ h ∈ mset 240 C, Relation.ReflTransGen
        (fun a b => a ∈ mset 240 C ∧ b ∈ mset 240 C ∧ iform (vec a) (vec b) ≠ 0) r h) ∧
      (∀ a ∈ mset 240 C, ∀ b ∈ mset 240 (kmask5 RC (BS (Nat.land (Nat.shiftRight e 20) 1))
        (Nat.land e 1023) (Nat.land (Nat.shiftRight e 10) 1023)),
        iform (vec a) (vec b) ≠ 0 → b ∈ mset 240 C) ∧
      0 < olen (fun g => fld PW 8 g) C 12 r 1 ∧
      (olen (fun g => fld PW 8 g) C 12 r 1 = 1 ∨ ∃ blk, jb8OK ADJ POS DEC (fun g => fld PW 8 g)
        LS (Nat.land (Nat.shiftRight e 20) 1)
        (kmask5 RC (BS (Nat.land (Nat.shiftRight e 20) 1)) (Nat.land e 1023)
          (Nat.land (Nat.shiftRight e 10) 1023))
        (Nat.land e 1023) (Nat.land (Nat.shiftRight e 10) 1023) C r blk = true) := by
  have hsym := iform_comm_ana (τ := Tag.E8) (Or.inr rfl)
  simp only [pl5OK, ana8OK, Lane.strictB_eq] at hpl hana
  intro g hg
  obtain ⟨C, r, hgC, hr, hsub, hpath, hcl, hol, hJ⟩ := ana8Walk_spec (vec := vec) hP
    (fun a ha b hb h => Lane.fld_one_eq_one.1 (Lane.beq_eq_true.1
      ((hD.adj a ha b hb).2 (by rw [hsym]; exact h))))
    (fun g hg pa hpa h => (hD.adj g hg pa hpa).1 (Lane.beq_eq_true.2 (Lane.fld_one_eq_one.2 h)))
    _ _ 0 0 0 0 0 ⟨fun x hx => by rw [Nat.zero_testBit] at hx; exact absurd hx (by decide),
      fun h => absurd rfl h⟩ hpl hana g (Lane.bit_iff.1 hg.2)
  exact ⟨C, r, hgC, hr, hsub, hpath, hcl, hol, hJ⟩

theorem sel6_map (f : ℕ → ℕ) (a b c d e g i : ℕ) :
    f (sel6 a b c d e g i) = sel6 (f a) (f b) (f c) (f d) (f e) (f g) i := by
  simp only [sel6, brecN_eq, nbeq_eq, nblt_eq]
  by_cases h2 : i < 2
  · by_cases h0 : i = 0
    · simp [h2, h0]
    · simp [h2, h0]
  · simp only [h2, decide_false, cond_false]
    exact sel4_map f c d e g (i - 2)

theorem leK8_spec {LS : ℕ → ℕ} {s g0 blk j x : ℕ} {k : ℕ → ℕ → ℕ → Bool}
    (h : leK8 LS s g0 blk j x k = true) :
    Nat.land (LS (fld (Nat.shiftRight blk 128) 12 j)) 1 = s ∧
      Nat.land (Nat.shiftRight (LS (fld (Nat.shiftRight blk 128) 12 j)) 1) 1023 = x ∧
      bit (Nat.land (Nat.shiftRight (LS (fld (Nat.shiftRight blk 128) 12 j)) 35) M240) g0 = true ∧
      k (Nat.land (Nat.shiftRight (LS (fld (Nat.shiftRight blk 128) 12 j)) 35) M240)
        (Nat.land (Nat.shiftRight (LS (fld (Nat.shiftRight blk 128) 12 j)) 11) 16777215)
        (Nat.land (Nat.shiftRight (LS (fld (Nat.shiftRight blk 128) 12 j)) 275) 63) = true := by
  rw [leK8, strictB_eq, strictB_eq, andB_eq, andB_eq, andB_eq] at h
  simp only [Bool.and_eq_true, nbeq_eq, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

structure LineRaw8 (vec : ℕ → Fin Tag.E8.rank → ℤ) (RTs : ℕ → ℕ) (ph : ℕ → ℕ)
    (RC BS : ℕ → ℕ) (s g0 x E : ℕ) : Prop where
  x_eq : Nat.land (Nat.shiftRight E 1) 1023 = x
  g0_mem : g0 ∈ mset 240 (Nat.land (Nat.shiftRight E 35) M240)
  comp : ∃ g1 r1, CompRaw vec (fun g v => fld (RTs g) 8 v) ph 240 (mset 240 (kv8 RC (BS s) x))
    (mset 240 (Nat.land (Nat.shiftRight E 35) M240)) g1
    (Nat.land (Nat.shiftRight E 11) 16777215) r1
  ks : dKs (Nat.land (Nat.shiftRight E 11) 16777215) =
    ksOf (dR (Nat.land (Nat.shiftRight E 11) 16777215)) (CFSG.TcRes.TK.dN (Nat.land (Nat.shiftRight E 11) 16777215))
  flags : Nat.land (Nat.shiftRight E 275) 63 = flags5 (Nat.land (Nat.shiftRight E 11) 16777215)

theorem jb8OK_spec
    {vec : ℕ → Fin Tag.E8.rank → ℤ} {neg : ℕ → ℕ}
    {ADJ POS DEC PW V X Y : ℕ} {RTs QS MVS RC BS LS : ℕ → ℕ} {s P c1 c2 C g0 blk : ℕ}
    (hvec : vec = vecOf 8 V)
    (hD : DatumRaw Tag.E8 240 vec (fun g v => fld (RTs g) 8 v)
      (fun g v => Nat.beq (fld (fld ADJ 240 g) 1 v) 1) neg)
    (hX : ∀ v < 240, ∀ g < 240, (CFSG.TcRes.TK.dP 8 (fld X 256 v * fld Y 256 g) : ℤ) -
      dQ 8 (fld X 256 v * fld Y 256 g) = iform (vec v) (vec g))
    (hq : ∀ i < 240, qOK QS V i = true) (hmv : ∀ x < 240, mvOK QS Y MVS x = true)
    (hpos : ∀ g < 240, pos8OK V POS g = true) (hdec : ∀ g < 240, dec8OK QS MVS V POS DEC g = true)
    (hph : ∀ g < 240, fld PW 8 g < 240)
    (hsub : ∀ Φ, (Φ = P ∨ ∃ s' x, Φ = kv8 RC (BS s') x) → ∀ a ∈ mset 240 Φ, ∀ b ∈ mset 240 Φ,
      ∀ c < 240, vec c = vec a - vec b → c ∈ mset 240 Φ)
    (hls : ∀ ℓ < 4096, LS ℓ = 0 ∨ line8OK ADJ POS DEC PW RC BS (LS ℓ) = true)
    (hVl : ∀ i < 240, ∀ m < 8, fld (fld V 128 i) 16 m < 16)
    (hYc : ∀ g < 240, ∀ m : Fin Tag.E8.rank, (fld (fld Y 256 g) 16 (7 - m) : ℤ) -
      fld (fld Y 256 g) 16 (15 - m) = ∑ k, Tag.E8.symmetrizedCartan m k * vec g k)
    (hYl : ∀ g < 240, ∀ j, fld (fld Y 256 g) 16 j ≤ 3) (hQb : ∀ m < 8, QS m < 2 ^ (16 * 240))
    (h : jb8OK ADJ POS DEC (fun g => fld PW 8 g) LS s P c1 c2 C g0 blk = true) :
    ∃ dJ r0, CompRaw vec (fun g v => fld (RTs g) 8 v) (fun g => fld PW 8 g) 240 (mset 240 P)
        (mset 240 C) g0 dJ r0 ∧ dKs dJ = ksOf (dR dJ) (CFSG.TcRes.TK.dN dJ) ∧ 2 ≤ dE dJ ∧
      ∃ E0 E1 E2 E3 E4 E5 : ℕ,
        (∀ i < 6, LineRaw8 vec RTs (fun g => fld PW 8 g) RC BS s g0 (xs5 c1 c2 i)
          (sel6 E0 E1 E2 E3 E4 E5 i)) ∧
        jok5 s C dJ (sel6 (Nat.land (Nat.shiftRight E0 35) M240) (Nat.land (Nat.shiftRight E1 35) M240)
            (Nat.land (Nat.shiftRight E2 35) M240) (Nat.land (Nat.shiftRight E3 35) M240)
            (Nat.land (Nat.shiftRight E4 35) M240) (Nat.land (Nat.shiftRight E5 35) M240))
          (sel6 (Nat.land (Nat.shiftRight E0 11) 16777215) (Nat.land (Nat.shiftRight E1 11) 16777215)
            (Nat.land (Nat.shiftRight E2 11) 16777215) (Nat.land (Nat.shiftRight E3 11) 16777215)
            (Nat.land (Nat.shiftRight E4 11) 16777215) (Nat.land (Nat.shiftRight E5 11) 16777215))
          (sel6 (Nat.land (Nat.shiftRight E0 275) 63) (Nat.land (Nat.shiftRight E1 275) 63)
            (Nat.land (Nat.shiftRight E2 275) 63) (Nat.land (Nat.shiftRight E3 275) 63)
            (Nat.land (Nat.shiftRight E4 275) 63) (Nat.land (Nat.shiftRight E5 275) 63)) = true := by
  obtain ⟨ψ, d, r0, hk, hc, hks⟩ := compRaw_of_crK8 hvec hD hX hq hmv hpos hdec hph
    (hsub P (Or.inl rfl)) hVl hYc hYl hQb h
  simp only [andB_eq, Bool.and_eq_true, nbeq_eq, decide_eq_true_eq, nble_eq] at hk
  obtain ⟨rfl, hd2, hk⟩ := hk
  have hg0 : g0 < 240 := hc.g0_mem.1
  have hline : ∀ (ℓ x : ℕ), ℓ < 4096 → Nat.land (LS ℓ) 1 = s →
      Nat.land (Nat.shiftRight (LS ℓ) 1) 1023 = x →
      bit (Nat.land (Nat.shiftRight (LS ℓ) 35) M240) g0 = true →
      LineRaw8 vec RTs (fun g => fld PW 8 g) RC BS s g0 x (LS ℓ) := by
    intro ℓ x hℓ hs hx hb
    have hE0 : LS ℓ ≠ 0 := by
      intro h0
      rw [h0] at hb
      simp [bit_zero] at hb
    have hlo := (hls ℓ hℓ).resolve_left hE0
    rw [line8OK, strictB_eq, hs, hx] at hlo
    obtain ⟨ψ', d', r1, hk', hc', hks'⟩ := compRaw_of_crK8 hvec hD hX hq hmv hpos hdec hph
      (hsub _ (Or.inr ⟨s, x, rfl⟩)) hVl hYc hYl hQb hlo
    simp only [andB_eq, Bool.and_eq_true, nbeq_eq, decide_eq_true_eq] at hk'
    obtain ⟨rfl, rfl, hfl⟩ := hk'
    exact ⟨hx, ⟨hg0, hb⟩, ⟨_, r1, hc'⟩, hks', hfl.symm⟩
  obtain ⟨s0, x0, b0, hk⟩ := leK8_spec hk
  obtain ⟨s1, x1, b1, hk⟩ := leK8_spec hk
  obtain ⟨s2, x2, b2, hk⟩ := leK8_spec hk
  obtain ⟨s3, x3, b3, hk⟩ := leK8_spec hk
  obtain ⟨s4, x4, b4, hk⟩ := leK8_spec hk
  obtain ⟨s5, x5, b5, hk⟩ := leK8_spec hk
  refine ⟨d, r0, hc, hks, hd2, _, _, _, _, _, _, fun i hi => ?_, hk⟩
  have h12 : ∀ j, fld (Nat.shiftRight blk 128) 12 j < 4096 := fun j =>
    lt_of_lt_of_eq (CFSG.KC.TcRes.Lane.fld_lt _ 12 _) (by norm_num)
  have l0 := hline _ _ (h12 _) s0 x0 b0
  have l1 := hline _ _ (h12 _) s1 x1 b1
  have l2 := hline _ _ (h12 _) s2 x2 b2
  have l3 := hline _ _ (h12 _) s3 x3 b3
  have l4 := hline _ _ (h12 _) s4 x4 b4
  have l5 := hline _ _ (h12 _) s5 x5 b5
  interval_cases i
  · exact l0
  · exact l1
  · exact l2
  · exact l3
  · exact l4
  · exact l5

end CFSG.KC.TcRes

end
