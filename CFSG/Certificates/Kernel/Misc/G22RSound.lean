module

public import CFSG.Certificates.Kernel.Misc.G22CSound
public import CFSG.Quasithin.H13.L32NKGG22

public section

namespace CFSG.KC.G22C

open CFSG.KD.G22C CFSG.KD.G22W CFSG.KD.BfsK CFSG.KC.Mat8P CFSG.KC.G22W
  CFSG.Quasithin.H13.KGCert

@[expose] def RankF {α : Type} (m : α → α → α) (P : α → Prop) (a : α) : Prop :=
  ∀ b, P b → m a b = m b a → b ≠ a → ∀ c, P c → m a c = m c a → m b c = m c b → c ≠ a →
    c ≠ b → c ≠ m a b → ∀ e, P e → m a e = m e a → m b e = m e b → m c e = m e c →
      e = a ∨ e = b ∨ e = c ∨ e = m a b ∨ e = m a c ∨ e = m b c ∨ e = m (m a b) c

theorem rankB_iff {α : Type} {q : α → α → Bool} (hq : ∀ x y, q x y = true ↔ x = y)
    (m : α → α → α) (L : List α) (a : α) : rankB q m L a = true ↔ RankF m (· ∈ L) a := by
  simp only [rankB, List.all_eq_true, List.mem_filter, Bool.or_eq_true, hq, or_assoc]
  constructor
  · intro h b hb hab hba c hc hac hbc hca hcb hcab e he hae hbe hce
    have h1 := (h b ⟨hb, hab⟩).resolve_left hba
    have h2 := (((h1 c ⟨⟨hc, hac⟩, hbc⟩).resolve_left hca).resolve_left hcb).resolve_left hcab
    exact h2 e ⟨⟨⟨he, hae⟩, hbe⟩, hce⟩
  · rintro h b ⟨hb, hab⟩
    by_cases hba : b = a
    · exact Or.inl hba
    · refine Or.inr fun c hc => ?_
      obtain ⟨⟨hc, hac⟩, hbc⟩ := hc
      by_cases hca : c = a
      · exact Or.inl hca
      refine Or.inr ?_
      by_cases hcb : c = b
      · exact Or.inl hcb
      refine Or.inr ?_
      by_cases hcab : c = m a b
      · exact Or.inl hcab
      refine Or.inr fun e he => ?_
      obtain ⟨⟨⟨he, hae⟩, hbe⟩, hce⟩ := he
      exact h b hb hab hba c hc hac hbc hca hcb hcab e he hae hbe hce

theorem rankF_filter {α : Type} {m : α → α → α} {P : α → Prop} {a : α} :
    RankF m (fun x => P x ∧ m a x = m x a) a ↔ RankF m P a := by
  constructor
  · intro h b hb hab hba c hc hac hbc hca hcb hcab e he hae hbe hce
    exact h b ⟨hb, hab⟩ hab hba c ⟨hc, hac⟩ hac hbc hca hcb hcab e ⟨he, hae⟩ hae hbe hce
  · intro h b hb hab hba c hc hac hbc hca hcb hcab e he hae hbe hce
    exact h b hb.1 hab hba c hc.1 hac hbc hca hcb hcab e he.1 hae hbe hce

theorem rankF_map {α β : Type} {m : α → α → α} {n : β → β → β} {f : α → β} {S P : α → Prop}
    {Q : β → Prop} (hPS : ∀ x, P x → S x) (hmul : ∀ x y, S x → S y → S (m x y))
    (hhom : ∀ x y, S x → S y → f (m x y) = n (f x) (f y))
    (hinj : ∀ x y, S x → S y → f x = f y → x = y) (hPQ : ∀ x, P x → Q (f x))
    (hQP : ∀ z, Q z → ∃ x, P x ∧ f x = z) {a : α} (ha : S a) :
    RankF n Q (f a) ↔ RankF m P a := by
  have hne : ∀ x y, S x → S y → x ≠ y → f x ≠ f y := fun x y hx hy h e => h (hinj x y hx hy e)
  have hcm : ∀ x y, S x → S y → m x y = m y x → n (f x) (f y) = n (f y) (f x) := by
    intro x y hx hy h
    rw [← hhom x y hx hy, ← hhom y x hy hx, h]
  have hcm' : ∀ x y, S x → S y → n (f x) (f y) = n (f y) (f x) → m x y = m y x := by
    intro x y hx hy h
    exact hinj _ _ (hmul x y hx hy) (hmul y x hy hx) (by rw [hhom x y hx hy, hhom y x hy hx, h])
  constructor
  · intro h b hb hab hba c hc hac hbc hca hcb hcab e he hae hbe hce
    have sb := hPS b hb
    have sc := hPS c hc
    have se := hPS e he
    have sab := hmul a b ha sb
    have hr := h (f b) (hPQ b hb) (hcm a b ha sb hab) (hne b a sb ha hba) (f c) (hPQ c hc)
      (hcm a c ha sc hac) (hcm b c sb sc hbc) (hne c a sc ha hca) (hne c b sc sb hcb)
      (by rw [← hhom a b ha sb]; exact hne c _ sc sab hcab) (f e) (hPQ e he) (hcm a e ha se hae)
      (hcm b e sb se hbe) (hcm c e sc se hce)
    rw [← hhom a b ha sb, ← hhom a c ha sc, ← hhom b c sb sc, ← hhom _ c sab sc] at hr
    rcases hr with h | h | h | h | h | h | h
    · exact Or.inl (hinj _ _ se ha h)
    · exact Or.inr (Or.inl (hinj _ _ se sb h))
    · exact Or.inr (Or.inr (Or.inl (hinj _ _ se sc h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hinj _ _ se sab h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hinj _ _ se (hmul a c ha sc) h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hinj _ _ se (hmul b c sb sc) h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hinj _ _ se (hmul _ c sab sc) h))))))
  · intro h B hB hAB hBA C hC hAC hBC hCA hCB hCAB E hE hAE hBE hCE
    obtain ⟨b, hb, rfl⟩ := hQP B hB
    obtain ⟨c, hc, rfl⟩ := hQP C hC
    obtain ⟨e, he, rfl⟩ := hQP E hE
    have sb := hPS b hb
    have sc := hPS c hc
    have se := hPS e he
    have sab := hmul a b ha sb
    have hr := h b hb (hcm' a b ha sb hAB) (fun h => hBA (by rw [h])) c hc (hcm' a c ha sc hAC)
      (hcm' b c sb sc hBC) (fun h => hCA (by rw [h])) (fun h => hCB (by rw [h]))
      (fun h => hCAB (by rw [h, hhom a b ha sb])) e he (hcm' a e ha se hAE) (hcm' b e sb se hBE)
      (hcm' c e sc se hCE)
    rcases hr with h | h | h | h | h | h | h <;> subst h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hhom a b ha sb))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hhom a c ha sc)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hhom b c sb sc))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (by rw [hhom _ c sab sc, hhom a b ha sb]))))))

@[expose] def TM (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Prop := M ∈ g22Mats ∧ M * M = 1 ∧ M ≠ 1

theorem rank_conj {Y Y' : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hY : Y ∈ g22Mats) (hY' : Y' ∈ g22Mats)
    (h1 : Y * Y' = 1) (h2 : Y' * Y = 1) (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    RankF (· * ·) TM (Y * M * Y') ↔ RankF (· * ·) TM M := by
  have l1 : ∀ z : Matrix (Fin 6) (Fin 6) (ZMod 2), Y' * (Y * z) = z := fun z => by
    rw [← mul_assoc, h2, one_mul]
  have l2 : ∀ z : Matrix (Fin 6) (Fin 6) (ZMod 2), Y * (Y' * z) = z := fun z => by
    rw [← mul_assoc, h1, one_mul]
  refine rankF_map (m := (· * ·)) (n := (· * ·)) (f := fun x => Y * x * Y') (S := fun _ => True)
    (P := TM) (Q := TM) (fun _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun x y _ _ => ?_) (fun x y _ _ h => ?_) (fun x hx => ?_) (fun z hz => ?_) trivial
  · simp only [mul_assoc, l1]
  · have := congrArg (fun z => Y' * z * Y) h
    simpa only [mul_assoc, l1, h2, mul_one] using this
  · obtain ⟨hm, hxx, hx1⟩ := hx
    have l3 : x * (x * Y') = Y' := by rw [← mul_assoc, hxx, one_mul]
    refine ⟨g22Mats.mul_mem (g22Mats.mul_mem hY hm) hY', ?_, ?_⟩
    · simp only [mul_assoc, l1, l3, h1]
    · intro h
      apply hx1
      have := congrArg (fun z => Y' * z * Y) h
      simpa only [mul_assoc, l1, h2, mul_one, one_mul] using this
  · obtain ⟨hm, hzz, hz1⟩ := hz
    have l3 : z * (z * Y) = Y := by rw [← mul_assoc, hzz, one_mul]
    refine ⟨Y' * z * Y, ⟨g22Mats.mul_mem (g22Mats.mul_mem hY' hm) hY, ?_, ?_⟩, ?_⟩
    · simp only [mul_assoc, l2, l3, h2]
    · intro h
      apply hz1
      have := congrArg (fun w => Y * w * Y') h
      simpa only [mul_assoc, l2, h1, mul_one, one_mul] using this
    · simp only [mul_assoc, l2, h1, mul_one]

theorem mulC_mem_G {x y : List ℕ} (hx : x ∈ g22Elems)
    (hy : y ∈ g22Elems) : mulC x y ∈ g22Elems := by
  obtain ⟨z, hz, hze⟩ := (mem_g22Mats_iff (decodeC x * decodeC y)).1
    (g22Mats.mul_mem ((mem_g22Mats_iff _).2 ⟨x, hx, rfl⟩) ((mem_g22Mats_iff _).2 ⟨y, hy, rfl⟩))
  have : z = mulC x y := decodeC_injOn (validC_of_mem hz)
    (validC_mulC (validC_of_mem hx) (validC_of_mem hy))
    (by rw [hze, decodeC_mulC _ _ (validC_of_mem hy).1])
  exact this ▸ hz

theorem rank_list_mat {a : List ℕ} (ha : a ∈ g22Elems) :
    RankF (· * ·) TM (decodeC a) ↔ RankF mulC (· ∈ g22Invs) a := by
  refine rankF_map (S := (· ∈ g22Elems)) (fun x hx => (mem_invs.1 hx).1)
    (fun x y hx hy => mulC_mem_G hx hy) (fun x y _ hy => decodeC_mulC _ _ (validC_of_mem hy).1)
    (fun x y hx hy h => decodeC_injOn (validC_of_mem hx) (validC_of_mem hy) h)
    (fun x hx => ?_) (fun z hz => ?_) ha
  · obtain ⟨hx, hxx, hx1⟩ := mem_invs.1 hx
    refine ⟨(mem_g22Mats_iff _).2 ⟨x, hx, rfl⟩, ?_, ?_⟩
    · rw [← decodeC_mulC _ _ (validC_of_mem hx).1, hxx, decodeC_oneC]
    · intro h
      apply hx1
      exact decodeC_injOn (validC_of_mem hx) validC_oneC (by rw [h, decodeC_oneC])
  · obtain ⟨hm, hzz, hz1⟩ := hz
    obtain ⟨x, hx, rfl⟩ := (mem_g22Mats_iff _).1 hm
    refine ⟨x, mem_invs.2 ⟨hx, ?_, ?_⟩, rfl⟩
    · exact decodeC_injOn (validC_mulC (validC_of_mem hx) (validC_of_mem hx)) validC_oneC
        (by rw [decodeC_mulC _ _ (validC_of_mem hx).1, hzz, decodeC_oneC])
    · rintro rfl
      exact hz1 decodeC_oneC

@[expose] def GoodL (x : ℕ) : Prop := x < 2 ^ 64 ∧ unpackM x = colsK x ++ [64, 128] ∧ VC (colsK x)

theorem goodL_mul {x y : ℕ} (hx : GoodL x) (hy : GoodL y) :
    GoodL (mulP x y) ∧ colsK (mulP x y) = mulC (colsK x) (colsK y) := by
  have h1 := mulP_cols hx.2.1 rfl hy.2.1 hy.2.2
  have h2 := h1
  rw [unpackM_cols] at h2
  have h3 := (List.append_inj h2 (by rw [length_mulC]; rfl)).1
  refine ⟨⟨mulP_lt x y, by rw [h1, h3], ?_⟩, h3⟩
  rw [h3]
  exact validC_mulC hx.2.2 hy.2.2

theorem goodL_inj {x y : ℕ} (hx : GoodL x) (hy : GoodL y) (h : colsK x = colsK y) : x = y :=
  unpackM_inj hx.1 hy.1 (by rw [hx.2.1, hy.2.1, h])

theorem goodL_one : GoodL oneP :=
  ⟨oneP_lt, by rw [oneP_cols, colsK_oneP], by rw [colsK_oneP]; exact validC_oneC⟩

theorem goodL_of {x : ℕ} (hx : x < 2 ^ 64) (h : goodK x = true) : GoodL x :=
  ⟨hx, (good_facts h).1, (good_facts h).2⟩

theorem isInvP_iff {x : ℕ} (hx : GoodL x) :
    isInvP x = true ↔ mulC (colsK x) (colsK x) = oneC ∧ colsK x ≠ oneC := by
  have hm := goodL_mul hx hx
  simp only [isInvP, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [← hm.2, h1, colsK_oneP], fun h => ?_⟩
    have : x = oneP := goodL_inj hx goodL_one (by rw [h, colsK_oneP])
    rw [this] at h2
    simp at h2
  · rintro ⟨h1, h2⟩
    refine ⟨goodL_inj hm.1 goodL_one (by rw [hm.2, h1, colsK_oneP]), ?_⟩
    cases hb : Nat.beq x oneP
    · rfl
    · exact absurd (by rw [Nat.beq_eq.mp hb, colsK_oneP]) h2

theorem rank_rep {R C : ℕ → ℕ} {n : ℕ} (hEq : g22Elems = (List.range n).reverse.map (E R))
    (hg : ∀ t < n, GoodL (numX R t)) {c : Bool} (hp : cond c (C (Nat.add n 1)) (C n) < n)
    (hK : classK R C n c = true) (hR : rankK R C n c = true) :
    RankF mulC (· ∈ g22Invs) (colsK (repT R C n c)) := by
  set T := repT R C n c with hTdef
  have hT : GoodL T := hg _ hp
  have heqL : ∀ l l' : List ℕ, eqL l l' = true → l = l' := by
    intro l
    induction l with
    | nil => intro l' h; cases l' <;> simp_all [eqL]
    | cons x l ih =>
      intro l' h
      cases l' with
      | nil => simp [eqL] at h
      | cons y l' =>
        simp only [eqL, Bool.and_eq_true, Nat.beq_eq] at h
        rw [h.1, ih l' h.2]
  have hL := heqL _ _ hK
  have hr := (rankB_iff (q := Nat.beq) (fun x y => by rw [Nat.beq_eq]) mulP (clsL C n c) T).1 hR
  rw [← hL] at hr
  have memI : ∀ x, x ∈ invN R n ↔ ∃ t < n, numX R t = x ∧ isInvP x = true := by
    intro x
    simp only [invN, List.mem_filter, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hi⟩
      exact ⟨t, ht, rfl, hi⟩
    · rintro ⟨t, ht, rfl, hi⟩
      exact ⟨⟨t, ht, rfl⟩, hi⟩
  have memG : ∀ z, z ∈ g22Elems ↔ ∃ t < n, colsK (numX R t) = z := by
    intro z
    rw [hEq]
    exact mem_map_range
  have key := (rankF_map (m := mulP) (n := mulC) (f := colsK) (S := GoodL)
    (P := (· ∈ (invN R n).filter (commN T)))
    (Q := fun z => z ∈ g22Invs ∧ mulC (colsK T) z = mulC z (colsK T))
    (fun x hx => ?_) (fun x y hx hy => (goodL_mul hx hy).1) (fun x y hx hy => (goodL_mul hx hy).2)
    (fun x y hx hy h => goodL_inj hx hy h) (fun x hx => ?_) (fun z hz => ?_) hT).2 hr
  · exact rankF_filter.1 key
  · obtain ⟨t, ht, rfl, -⟩ := (memI x).1 (List.mem_filter.1 hx).1
    exact hg t ht
  · obtain ⟨hxI, hxc⟩ := List.mem_filter.1 hx
    obtain ⟨t, ht, rfl, hi⟩ := (memI _).1 hxI
    have hgx := hg t ht
    obtain ⟨h1, h2⟩ := (isInvP_iff hgx).1 hi
    refine ⟨mem_invs.2 ⟨(memG _).2 ⟨t, ht, rfl⟩, h1, h2⟩, ?_⟩
    simp only [commN, Nat.beq_eq] at hxc
    rw [← (goodL_mul hT hgx).2, ← (goodL_mul hgx hT).2, hxc]
  · obtain ⟨hzI, hzc⟩ := hz
    obtain ⟨hzG, hzz, hz1⟩ := mem_invs.1 hzI
    obtain ⟨t, ht, rfl⟩ := (memG _).1 hzG
    have hgx := hg t ht
    refine ⟨numX R t, List.mem_filter.2 ⟨(memI _).2 ⟨t, ht, rfl, (isInvP_iff hgx).2 ⟨hzz, hz1⟩⟩,
      ?_⟩, rfl⟩
    simp only [commN, Nat.beq_eq]
    exact goodL_inj (goodL_mul hT hgx).1 (goodL_mul hgx hT).1
      (by rw [(goodL_mul hT hgx).2, (goodL_mul hgx hT).2, hzc])

theorem rank_check {R C : ℕ → ℕ} {n hi : ℕ}
    (hEq : g22Elems = (List.range n).reverse.map (E R)) (hn : ∀ t < n, numX R t < 2 ^ 64)
    (hg : ∀ t < n, goodK (numX R t) = true)
    (hT0 : unpackM (repT R C n false) = t0C ++ [64, 128])
    (hT1 : unpackM (repT R C n true) = t1C ++ [64, 128])
    (hC : conjK R C n hi = true) (hm : n ≤ 64 * hi)
    (hK0 : classK R C n false = true) (hK1 : classK R C n true = true)
    (hR0 : rankK R C n false = true) (hR1 : rankK R C n true = true) : g22RankCheck = true := by
  have hgL : ∀ t < n, GoodL (numX R t) := fun t ht => goodL_of (hn t ht) (hg t ht)
  have hp : C n < n ∧ C (Nat.add n 1) < n := by
    simp only [conjK, Bool.and_eq_true, Nat.blt_eq] at hC
    exact hC.1
  have hmemT : ∀ c : Bool, colsK (repT R C n c) ∈ g22Elems := by
    intro c
    rw [hEq]
    cases c
    · exact mem_map_range.2 ⟨_, hp.1, rfl⟩
    · exact mem_map_range.2 ⟨_, hp.2, rfl⟩
  have hcolsT : ∀ c : Bool, colsK (repT R C n c) = cond c t1C t0C := by
    intro c
    cases c
    · exact eq_of_unpack hT0 (hgL _ hp.1).2.1
    · exact eq_of_unpack hT1 (hgL _ hp.2).2.1
  have hrep : ∀ c : Bool, RankF (· * ·) TM (decodeC (cond c t1C t0C)) := by
    intro c
    rw [← hcolsT c, rank_list_mat (hmemT c)]
    cases c
    · exact rank_rep hEq hgL hp.1 hK0 hR0
    · exact rank_rep hEq hgL hp.2 hK1 hR1
  have hfin : g22RankCheck = g22Invs.all (rankB (· == ·) mulC g22Invs) := rfl
  rw [hfin, List.all_eq_true]
  intro a ha
  refine (rankB_iff (fun x y => beq_iff_eq) mulC g22Invs a).2 ?_
  have haG := (mem_invs.1 ha).1
  rw [← rank_list_mat haG]
  obtain ⟨y, hy, y', hy', hyy', hc⟩ := conj_facts hEq hg hT0 hT1 hC hm a ha
  have hvy := (validC_of_mem hy).1
  have hvy' := (validC_of_mem hy').1
  have hY := (mem_g22Mats_iff (decodeC y)).2 ⟨y, hy, rfl⟩
  have hY' := (mem_g22Mats_iff (decodeC y')).2 ⟨y', hy', rfl⟩
  have h1 : decodeC y * decodeC y' = 1 := by rw [← decodeC_mulC _ _ hvy', hyy', decodeC_oneC]
  have h2 : decodeC y' * decodeC y = 1 := mul_eq_one_comm.1 h1
  have hconj : ∀ T : List ℕ, mulC y a = mulC T y →
      decodeC a = decodeC y' * decodeC T * decodeC y := by
    intro T h
    have e : decodeC y * decodeC a = decodeC T * decodeC y := by
      rw [← decodeC_mulC _ _ (validC_of_mem haG).1, h, decodeC_mulC _ _ hvy]
    rw [mul_assoc, ← e, ← mul_assoc, h2, one_mul]
  rcases hc with hc | hc
  · rw [hconj _ hc, rank_conj hY' hY h2 h1]
    exact hrep false
  · rw [hconj _ hc, rank_conj hY' hY h2 h1]
    exact hrep true

end CFSG.KC.G22C

end
