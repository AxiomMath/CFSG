module

public import CFSG.Certificates.Kernel.FixBoundK.MemberMath
public import CFSG.Certificates.Kernel.FixBoundK.PCard
public import CFSG.Certificates.Kernel.FixBoundK.Step

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.FixBoundK

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Quasithin.H.Mathieu CFSG.Monster.B.TwoA.Census CFSG.KLie.CT

@[expose] def BasicsSem : Prop :=
  ∀ B bs : List Nat, basicsOK B bs = true → bs.length = 2 ^ B.length ∧
    ∀ j < 2 ^ B.length, ∀ k, (bs.getD j 0).testBit k = true ↔
      k < 2 ^ B.length ∧ bvec 24 (actS B k) * bvec 24 (actS B j) ∈ C

theorem lt_of_and_full {A m : Nat} (h : A &&& (2 ^ m - 1) = A) : A < 2 ^ m := by
  rw [Nat.and_two_pow_sub_one_eq_mod] at h
  rw [← h]
  exact Nat.mod_lt _ (Nat.two_pow_pos m)

theorem lt_of_testBit {b m : Nat} (h : ∀ k, b.testBit k = true → k < m) : b < 2 ^ m := by
  refine Nat.lt_pow_two_of_testBit b fun k hk => ?_
  cases hb : b.testBit k
  · rfl
  · exact absurd (h k hb) (by omega)

theorem getD_mem {L : List Nat} {u : Nat} (hu : u < L.length) : L.getD u 0 ∈ L := by
  rw [List.getD_eq_getElem _ _ hu]
  exact List.getElem_mem hu

theorem fixBoundAt_rep (hbs : BasicsSem) {reps : List Rep} {gens : List (List (List Nat))}
    {ch : List (Nat × List Mem)} {fx : List FixD} {fc : List (List FamC)} {i n : Nat}
    (hfix : fixAt reps gens fx i = true) (hfam : famAt reps ch fc i = true)
    (hch : ∀ k < n, chAt reps ch k = true) (hn : ch.length ≤ n)
    (hgen : ∀ g ∈ gens.getD i [], ∃ σ : AutPerm, ImgL (σ : Equiv.Perm (Fin 24)) g)
    (hP : CFSG.Open.IsElemAbelian 2 (Subgroup.closure (GenSet (gens.getD i [])))) :
    FixBoundAt (Subgroup.closure (GenSet (gens.getD i []))) := by
  classical
  rw [fixAt, TrivSound.nthS_eq, TrivSound.nthS_eq, TrivSound.nthS_eq] at hfix
  rw [famAt, TrivSound.nthS_eq, TrivSound.nthS_eq] at hfam
  set p := reps.getD i repD with hp
  set x := fx.getD i fixD0 with hx
  obtain ⟨hlg, hlen, hsyn, hfx, hd, hspan, hpar, hys, hmws, hbas⟩ := fixRep_spec hfix
  rw [TrivSound.lenS_eq, TrivSound.lenS_eq] at hlen
  rw [TrivSound.lenS_eq] at hlg
  obtain ⟨hbl, hbit⟩ := hbs _ _ hbas
  obtain ⟨hFlen, hFeq⟩ := (spanChk_iff x.1 p.2.1 0).1 hspan
  rw [Nat.zero_add] at hFlen
  set K := x.1.length with hK
  set F := p.2.1 with hF
  set bs := p.2.2.1 with hbsdef
  set L := famL ch i with hL
  have hm : F.length = 2 ^ K := hFlen
  have hFj : ∀ j < F.length, F.getD j 0 = actS x.1 j := fun j hj => by
    rw [hFeq j hj, Nat.zero_add]
  have hbl' : bs.length = F.length := by rw [hbl, hm]
  have hbit' : ∀ j < F.length, ∀ k, (bs.getD j 0).testBit k = true ↔
      k < F.length ∧ bvec 24 (F.getD k 0) * bvec 24 (F.getD j 0) ∈ C := by
    intro j hj k
    rw [hbit j (by rw [← hm]; exact hj) k, hFj j hj, ← hm]
    constructor
    · rintro ⟨hk, h⟩
      exact ⟨hk, by rw [hFj k hk]; exact h⟩
    · rintro ⟨hk, h⟩
      rw [hFj k hk] at h
      exact ⟨hk, h⟩
  have hmemL : ∀ A ∈ L, ∃ sF fs,
      memberK p.1 F bs p.2.2.2.1 (2 ^ F.length - 1) A sF fs = true := by
    intro A hA
    obtain ⟨c, hc, hAc⟩ := List.mem_flatMap.1 hA
    by_cases hci : c.1 = i
    · rw [if_pos hci] at hAc
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hAc
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hc
      have h := hch k (lt_of_lt_of_le hk hn)
      simp only [chAt, TrivSound.nthS_eq] at h
      rw [List.getD_eq_getElem _ _ hk] at h
      rw [chunkK, chunkFull, TrivSound.allS_iff, hci, TrivSound.lenS_eq] at h
      exact ⟨e.2.1, e.2.2, h e he⟩
    · rw [if_neg hci] at hAc
      exact absurd hAc List.not_mem_nil
  have hA : ∀ A ∈ L, A < 2 ^ F.length := fun A hAL => by
    obtain ⟨sF, fs, h⟩ := hmemL A hAL
    exact lt_of_and_full (memberK_spec h).1
  have hbsb : ∀ b ∈ bs, b < 2 ^ F.length := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hb
    refine lt_of_testBit fun k hk => ?_
    have hj' : j < F.length := by rw [← hbl']; exact hj
    rw [← List.getD_eq_getElem _ 0 hj] at hk
    exact ((hbit' j hj' k).1 hk).1
  obtain ⟨-, hlast, hcl0⟩ := famRep_spec hm hbl' hbsb hA hfam
  have hclosed := famL_closed (K := K) (L := L) (bs := fun j => bs.getD j 0)
    (famBil (F := fun j => actS x.1 j) (fun j z _ _ => actS_xor x.1 j z) hbit)
    (fun u hu => famB0 (actS_zero x.1) hbit (by rw [← hm]; exact hA _ (getD_mem hu)))
    (by rw [← hm]; exact hcl0)
  have hcl : ∀ u < L.length, ∀ j < F.length, ∃ v < L.length,
      L.getD v 0 = L.getD u 0 &&& bs.getD j 0 := fun u hu j hj =>
    hclosed u hu j (by rw [← hm]; exact hj)
  have hfull : 2 ^ F.length - 1 ∈ L := List.mem_of_getLast? hlast
  have hr : Nat.card (Subgroup.closure (GenSet (gens.getD i []))) ≤ 2 ^ p.1 := by
    rw [← hlg]
    exact card_closure_GenSet_le hP
  exact fixBoundAt_of_members (L := L) (r := p.1) hgen hlen hsyn hfx hd hpar hys hspan hmws hbl'
    hbit' hcl hfull hmemL hr

theorem eqDec_length (X : Nat) : ∀ (l : List Nat) (i : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 24))
      (fun v _ ih i => bAnd(Nat.beq (Pair.ap X i) v, ih (Nat.succ i))) l i = true →
    i + l.length = 24
  | [], i, h => by
    have := Nat.eq_of_beq_eq_true h
    simpa using this
  | v :: l, i, h => by
    have h' : bAnd(Nat.beq (Pair.ap X i) v, List.rec (motive := fun _ => Nat → Bool)
        (fun i => Nat.beq i (nat_lit 24))
        (fun v _ ih i => bAnd(Nat.beq (Pair.ap X i) v, ih (Nat.succ i))) l (Nat.succ i)) = true := h
    rw [TrivSound.bAnd_eq, Bool.and_eq_true] at h'
    have := eqDec_length X l (Nat.succ i) h'.2
    simp only [List.length_cons]
    omega

theorem gensOK_length (IV R n : Nat) : ∀ (gl : List (List Nat)) (j : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (Pair.rk R))
      (fun g _ ih j => bAnd(Nat.blt (Pair.gI R j) n,
        bAnd(Pair.eqDec (Pair.ivc IV (Pair.gI R j)) g, ih (Nat.succ j)))) gl j = true →
    ∀ g ∈ gl, g.length = 24
  | [], _, _ => by simp
  | g :: gl, j, h => by
    have h' : bAnd(Nat.blt (Pair.gI R j) n,
        bAnd(Pair.eqDec (Pair.ivc IV (Pair.gI R j)) g, List.rec (motive := fun _ => Nat → Bool)
          (fun j => Nat.beq j (Pair.rk R))
          (fun g _ ih j => bAnd(Nat.blt (Pair.gI R j) n,
            bAnd(Pair.eqDec (Pair.ivc IV (Pair.gI R j)) g, ih (Nat.succ j)))) gl (Nat.succ j))) =
        true := h
    rw [TrivSound.bAnd_eq, Bool.and_eq_true, TrivSound.bAnd_eq, Bool.and_eq_true] at h'
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · have := eqDec_length _ g' 0 h'.2.1
      simpa using this
    · exact gensOK_length IV R n gl _ h'.2.2 g' hg'

theorem repOK_length {IV RG BP nB n t r : Nat} {gl : List (List Nat)}
    (h : Pair.repOK IV RG BP nB n t r gl = true) : ∀ g ∈ gl, g.length = 24 := by
  unfold Pair.repOK at h
  rw [TrivSound.strictK_eq] at h
  dsimp only at h
  rw [TrivSound.bAnd_eq, Bool.and_eq_true, TrivSound.bAnd_eq, Bool.and_eq_true] at h
  exact gensOK_length IV _ n gl 0 h.2.1

theorem imgL_of_getD {σ : Equiv.Perm (Fin 24)} {g : List Nat} (hl : g.length = 24)
    (h : ∀ i : Fin 24, (σ i : Nat) = g.getD i 0) : ImgL σ g := by
  refine ⟨hl, fun i => ?_⟩
  rw [h i, getElem!_pos g.toArray (i : Nat) (by simp [hl]), List.getElem_toArray,
    List.getD_eq_getElem _ _ (by rw [hl]; exact i.2)]

theorem src_genSet {rec : ℕ → ℕ} {IV IR RG CM BP nB : ℕ}
    {items : ℕ → List Pair.Item} (F : Pair.CheckFacts rec IV IR RG CM BP nB items) {t r : ℕ}
    {gl : List (List ℕ)} (ht : t ≤ 751) (ht0 : t ≠ 0)
    (h : Pair.repOK IV RG BP nB 191 (t - 1) r gl = true) :
    (∀ g ∈ gl, ∃ σ : AutPerm, ImgL (σ : Equiv.Perm (Fin 24)) g) ∧
      Subgroup.closure (Pair.srcSet IV RG t) =
        (Subgroup.closure (GenSet gl)).map AutPerm.subtype := by
  obtain ⟨hrk, hgl, hgen, -, -⟩ := Pair.repOK_spec h
  have hlen := repOK_length h
  have hR : Pair.srcR RG t = fget RG (t - 1) 56 := Pair.srcR_pos RG ht0
  have hrk' : ∀ j, j < r ↔ j < Pair.rk (Pair.srcR RG t) := fun j => by rw [hR, hrk]
  have himg : ∀ (j) (hj : j < gl.length), ImgL (Pair.srcGen IV RG t j) gl[j] := by
    intro j hj
    have hjr : j < r := by omega
    refine imgL_of_getD (hlen _ (List.getElem_mem hj)) fun p => ?_
    have e : gl[j]?.getD [] = gl[j] := by rw [List.getElem?_eq_getElem hj, Option.getD_some]
    rw [Pair.srcGen, Pair.cperm_apply (Pair.gen_perm F ht ((hrk' j).1 hjr)), hR, (hgen j hjr).2 p p.2, e]
  have hmemA : ∀ j < r, Pair.srcGen IV RG t j ∈ AutPerm := fun j hj =>
    sylowSub_le (Pair.gen_mem F ht ((hrk' j).1 hj))
  have hset : Subtype.val '' GenSet gl = Pair.srcSet IV RG t := by
    ext τ
    constructor
    · rintro ⟨σ, ⟨g, hg, hσ⟩, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
      exact ⟨j, (hrk' j).1 (by omega), imgL_unique (himg j hj) hσ⟩
    · rintro ⟨j, hj, rfl⟩
      have hjr : j < r := (hrk' j).2 hj
      have hjl : j < gl.length := by omega
      exact ⟨⟨_, hmemA j hjr⟩, ⟨gl[j], List.getElem_mem hjl, himg j hjl⟩, rfl⟩
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    exact ⟨⟨_, hmemA j (by omega)⟩, himg j hj⟩
  · rw [MonoidHom.map_closure, ← hset]
    rfl

theorem isElemAbelian_map {G H : Type*} [Group G] [Group H] (f : G →* H) {E : Subgroup G}
    (h : CFSG.Open.IsElemAbelian 2 E) : CFSG.Open.IsElemAbelian 2 (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, hx, rfl⟩ := a
    obtain ⟨_, y, hy, rfl⟩ := b
    apply Subtype.ext
    change f x * f y = f y * f x
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (h.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h.2 x hx, map_one]

theorem isElemAbelian_of_map {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {E : Subgroup G} (h : CFSG.Open.IsElemAbelian 2 (E.map f)) :
    CFSG.Open.IsElemAbelian 2 E := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (h.1.is_comm.comm ⟨f a, Subgroup.mem_map_of_mem f a.2⟩
      ⟨f b, Subgroup.mem_map_of_mem f b.2⟩)
  · rw [map_pow, map_one]
    exact h.2 _ (Subgroup.mem_map_of_mem f hx)

theorem fixBound_of_src {src : ℕ → Set (Equiv.Perm (Fin 24))}
    (hcomp : ∀ P : Subgroup (Equiv.Perm (Fin 24)), P ≤ sylowSub → CFSG.Open.IsElemAbelian 2 P →
      ∃ t ≤ 751, ∃ g ∈ sylowSub, conjG g P = Subgroup.closure (src t))
    (h0 : src 0 = ∅)
    (hrep : ∀ t ≤ 751, t ≠ 0 → ∃ gens : List (List Nat),
      Subgroup.closure (src t) = (Subgroup.closure (GenSet gens)).map AutPerm.subtype ∧
      (CFSG.Open.IsElemAbelian 2 (Subgroup.closure (GenSet gens)) →
        FixBoundAt (Subgroup.closure (GenSet gens))))
    (hbot : FixBoundAt ⊥) : FixBound := by
  refine fixBound_iff.2 fun P hPS hPE => ?_
  have hinj : Function.Injective AutPerm.subtype := Subtype.val_injective
  set P' := P.map AutPerm.subtype with hP'
  have hle : P' ≤ sylowSub := by
    rintro _ ⟨p, hp, rfl⟩
    exact hPS p hp
  obtain ⟨t, ht, g, hg, e⟩ := hcomp P' hle (isElemAbelian_map _ hPE)
  by_cases ht0 : t = 0
  · rw [ht0, h0, Subgroup.closure_empty] at e
    have hP'b : P' = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).1 e
    have hPb : P = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 hP'b
    rw [hPb]
    exact hbot
  · obtain ⟨gens, hcl, hfb⟩ := hrep t ht ht0
    set Q := Subgroup.closure (GenSet gens) with hQdef
    rw [hcl] at e
    set gA : AutPerm := ⟨g, sylowSub_le hg⟩ with hgA
    have hc1 : AutPerm.subtype.comp (MulAut.conj gA⁻¹).toMonoidHom =
        (MulAut.conj g⁻¹).toMonoidHom.comp AutPerm.subtype := MonoidHom.ext fun q => rfl
    have hc2 : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun q => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MonoidHom.id_apply]
        group
    have hmap : (conjSub gA⁻¹ Q).map AutPerm.subtype = P' := by
      change (Q.map (MulAut.conj gA⁻¹).toMonoidHom).map AutPerm.subtype = P'
      rw [Subgroup.map_map, hc1, ← Subgroup.map_map, ← e, conjG, Subgroup.map_map, hc2,
        Subgroup.map_id]
    have hPQ : P = conjSub gA⁻¹ Q := Subgroup.map_injective hinj (by rw [hmap])
    have hQ : CFSG.Open.IsElemAbelian 2 Q := isElemAbelian_of_map hinj (by
      rw [← e]
      exact isElemAbelian_map _ (isElemAbelian_map _ hPE))
    rw [hPQ]
    exact fixBoundAt_conj gA⁻¹ (hfb hQ)

end CFSG.KC.FixBoundK

end
