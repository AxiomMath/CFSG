module

public import CFSG.Certificates.Kernel.Mathieu.ChainSound
public import CFSG.Certificates.Kernel.SporSch.ChainKEnum
import CFSG.Certificates.Kernel.SporSch.ChainKOdd

public section

namespace CFSG.KC.MathieuK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.Mathieu
  CFSG.KS.SporSch.MOC CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier

variable {n w : Nat}

theorem prep_of_bind {X Xi : Nat} {l : List Nat} (hb : bindListK n w X l = true)
    (hp : permOK n w (mask w) (n * w) X Xi = true) :
    PRep n w X (arrPerm n l) ∧ imageList (arrPerm n l) = l ∧ X >>> (n * w) = 0 := by
  have ht := toArray_eq_of_bindListK hb
  have hr := rep_permOfArr (isInvA_unpack hp)
  have e : arrPerm n l = permOfArr n (unpack n w X) := by rw [arrPerm, ht]
  refine ⟨by rw [e]; exact prep_of_rep hr.1, ?_, (permOK_facts hp).1⟩
  rw [e, imageList_of_prep (prep_of_rep hr.1), ← ht]

theorem arrPerm_eq_of_bind {X : Nat} {l : List Nat} {g : Equiv.Perm (Fin n)}
    (ht : l.toArray = unpack n w X) (hg : PRep n w X g) : arrPerm n l = g := by
  rw [arrPerm, ht]
  exact permOfArr_eq_of_rep (rep_unpack hg)

theorem unpack_toList (P : Nat) : (unpack n w P).toList = unpackL n w P := by
  rw [unpack, Array.toList_ofFn, unpackL, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map]
  rfl

theorem wordValue_eq_evalCodes (S : List (Equiv.Perm (Fin n))) :
    ∀ wd : List ℤ, wordValue S wd = evalCodes S wd
  | [] => by simp [wordValue, evalCodes]
  | z :: wd => by
    rw [wordValue_cons, evalCodes, wordValue_eq_evalCodes S wd, letterValue_def]
    congr 1
    by_cases h : 0 < z
    · rw [if_pos h, if_pos h]
      congr 2
      omega
    · rw [if_neg h, if_neg h]
      congr 3
      omega

theorem letters_of_abOK : ∀ {wd : List Int}, abOK wd = true → ∀ l ∈ wd, l ≠ 0 ∧ l.natAbs ≤ 2
  | [], _, l, hl => absurd hl (List.not_mem_nil)
  | z :: wd, hw, l, hl => by
    rw [abOK_cons, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨h2, h5⟩, hw⟩ := hw
    rcases List.mem_cons.1 hl with rfl | hl
    · rcases l with k | k
      · have ec : icode (Int.ofNat k) = k + k := rfl
        rw [ec] at h2 h5
        refine ⟨fun e => ?_, ?_⟩
        · have : k = 0 := Int.ofNat_inj.1 e
          omega
        · change k ≤ 2
          omega
      · have ec : icode (Int.negSucc k) = k + 1 + (k + 1) + 1 := rfl
        rw [ec] at h2 h5
        exact ⟨Int.negSucc_ne_zero k, by change k + 1 ≤ 2; omega⟩
    · exact letters_of_abOK hw l hl

theorem prep_conjK {a b x : Equiv.Perm (Fin n)} {A Ai B Bi R : Nat} (hsz : szOK n w = true)
    (hA : imageList a = (unpack n w A).toList) (hB : imageList b = (unpack n w B).toList)
    (hAi : permOK n w (mask w) (n * w) A Ai = true) (hBi : permOK n w (mask w) (n * w) B Bi = true)
    (hR : PRep n w R x) {wd : List Int} (hw : abOK wd = true) :
    PRep n w (conjK n w A Ai B Bi R wd) ((wordValue [a, b] wd)⁻¹ * x * wordValue [a, b] wd) := by
  have hn := szOK_lt hsz
  have hf := szOK_facts hsz
  have hW := prep_of_imageList (abWordK_rep' hsz hA hB hAi hBi hw)
  rw [conjK, Orb.strictN_eq, wordValue_eq_evalCodes]
  exact prep_pcomp hn (prep_pcomp hn (prep_pinvS (by omega) hW).1 hR) hW

theorem baseVec_map [NeZero n] {B : List Nat} (h : ∀ x ∈ B, x < n) :
    (baseVec n B).toList.map Fin.val = B := by
  simp only [baseVec, Vector.toList_mk, List.toList_toArray, List.map_map]
  conv_rhs => rw [← List.map_id B]
  refine List.map_congr_left fun x hx => ?_
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt (h x hx)]

theorem baseVec_nodup [NeZero n] {B : List Nat} (h : ∀ x ∈ B, x < n) (hnd : B.Nodup) :
    (baseVec n B).toList.Nodup := by
  refine List.Nodup.of_map Fin.val ?_
  rw [baseVec_map h]
  exact hnd

theorem chainK_of [NeZero n] {gens : List (Equiv.Perm (Fin n))} {D : List (List Int)}
    {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat} {B : List Nat} (h : ∀ x ∈ B, x < n)
    (h1 : n + 1 < 2 ^ w) (h2 : n < 65536)
    (hgens : ∀ j < gens.length, imageList (gens.getD j 1) = (unpack n w (PS j)).toList)
    (hB : bindFromK w BP B 0 = true)
    (hK : RawK n w PS PSI LR TR TRI kS gens.length D B.length BP NS CH) :
    ChainK n w gens D (baseVec n B) PS PSI LR TR TRI kS BP NS CH := by
  refine ⟨Nat.pos_of_ne_zero (NeZero.ne n), h1, h2, hgens, ?_, hK.1, hK.2.1, hK.2.2.1,
    hK.2.2.2⟩
  rw [baseVec_map h]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [bindFromK_spec hB j h1, Nat.zero_add]
  simp

theorem elemOK_facts {x : List Nat} (h : elemOK n w x = true) :
    PRep n w (packL w x) (arrPerm n x) ∧ imageList (arrPerm n x) = x ∧
      x.toArray = unpack n w (packL w x) ∧ canonK n w (mask w) (n * w) (packL w x) = true := by
  simp only [elemOK, Bool.and_eq_true] at h
  obtain ⟨⟨hb, hp⟩, hc⟩ := h
  obtain ⟨h1, h2, -⟩ := prep_of_bind hb hp
  exact ⟨h1, h2, toArray_eq_of_bindListK hb, hc⟩

theorem chain_facts {gens : List (Equiv.Perm (Fin n))} {D : List (List Int)} {k : Nat}
    {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat} (hn : 1 ≤ n)
    (hbs : bv.toList.Nodup) (hQ : ChainK n w gens D bv PS PSI LR TR TRI kS BP NS CH) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) = ordK LR k ∧
      ∀ {x : List Nat}, elemOK n w x = true →
        siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 (packL w x) = true →
          arrPerm n x ∈ Subgroup.closure {g | g ∈ gens} := by
  obtain ⟨hV, hord⟩ := chainK_check hn hbs hQ
  have hsub := certificate_originalSubgroup hn gens D bv hbs
  refine ⟨?_, fun {x} hx hs => ?_⟩
  · rw [← hsub, ← RawSchreierDatum.orderCertificate_eq_card _ hV, hord]
  · obtain ⟨hP, -, -, hc⟩ := elemOK_facts hx
    have := chainK_sift hn hbs hQ (imageList_of_prep hP) hc hs
    rw [RawSchreierDatum.sift_eq_true_iff_mem_original _ hV, hsub] at this
    exact this

theorem repK_facts {gens : List (Equiv.Perm (Fin n))} {D : List (List Int)} {k : Nat}
    {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH p : Nat} (hn : 1 ≤ n)
    (hbs : bv.toList.Nodup) (hQ : ChainK n w gens D bv PS PSI LR TR TRI kS BP NS CH)
    (hp : 0 < p) {x : List Nat} (h : repK n w p LR TRI BP k x = true) :
    arrPerm n x ∈ Subgroup.closure {g | g ∈ gens} ∧ orderOf (arrPerm n x) = p ∧
      imageList (arrPerm n x) = x ∧
      ∀ y ∈ Subgroup.zpowers (arrPerm n x), y ≠ 1 → imageList (arrPerm n x) ≤ imageList y := by
  simp only [repK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨he, hs⟩, ho⟩, hlex⟩ := h
  obtain ⟨hP, himg, -, hc⟩ := elemOK_facts he
  have hsz := chainK_szOK hQ
  have sP := (PF.canon_facts hc).2.2.1
  have hord : orderOf (arrPerm n x) = p := by
    have := ordIs_eq hsz hP sP hp
    rw [ho] at this
    exact (decide_eq_true_iff.1 this.symm)
  refine ⟨(chain_facts hn hbs hQ).2 he hs, hord, himg, fun y hy hy1 => ?_⟩
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hord, Finset.mem_image] at hy
  obtain ⟨j, hj, rfl⟩ := hy
  rw [Finset.mem_range] at hj
  rcases hlex j hj with h0 | hle
  · subst h0
    exact absurd (pow_zero _) hy1
  · rw [himg, imageList_of_prep (prep_powK hsz hP j).1, unpack_toList]
    exact hle

theorem memL_eq {Y : Nat} {y : Equiv.Perm (Fin n)} (hw : 0 < w) (hY : PRep n w Y y)
    (sY : Y >>> (n * w) = 0) :
    ∀ {L : List (List Nat)}, (∀ x ∈ L, elemOK n w x = true) →
      memL Y (L.map (packL w)) = decide (y ∈ L.map (arrPerm n))
  | [], _ => by simp [memL]
  | x :: L, hL => by
    obtain ⟨hP, -, -, hc⟩ := elemOK_facts (hL x (List.mem_cons_self))
    rw [List.map_cons, memL, memL_eq hw hY sY (fun z hz => hL z (List.mem_cons_of_mem _ hz)),
      beq_prep hw hY hP sY (PF.canon_facts hc).2.2.1, List.map_cons, Bool.eq_iff_iff]
    simp

theorem cover_of_K {gens : List (Equiv.Perm (Fin n))} {D : List (List Int)} {k : Nat}
    {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH p : Nat} (hn : 1 ≤ n)
    (hbs : bv.toList.Nodup) (hQ : ChainK n w gens D bv PS PSI LR TR TRI kS BP NS CH)
    {L : List (List Nat)} (hL : ∀ x ∈ L, elemOK n w x = true)
    (hc : enumFrom n w (mask w) (n * w) LR TR (covK n w p (L.map (packL w))) k 0 (pidn n w) 0 =
      ordK LR k) :
    ∀ y ∈ Subgroup.closure {g | g ∈ gens}, y = 1 ∨ y ^ p ≠ 1 ∨
      ∃ j < p, j ≠ 0 ∧ y ^ j ∈ L.map (arrPerm n) := by
  have hsz := chainK_szOK hQ
  have hf := szOK_facts hsz
  have hw := PF.w_pos hf.2
  obtain ⟨hV, hord⟩ := chainK_check hn hbs hQ
  set Q := certificate hn gens D bv hbs
  set q : Equiv.Perm (Fin n) → Bool := fun y => decide (y = 1) || !decide (y ^ p = 1) ||
    (List.range p).any fun j => !Nat.beq j 0 && decide (y ^ j ∈ L.map (arrPerm n))
  have hpq : ∀ P x, PRep n w P x → P >>> (n * w) = 0 → covK n w p (L.map (packL w)) P = q x := by
    intro P x hP sP
    have pI := prep_pidn (n := n) hf.1 hf.2
    have sI := PF.pidn_shr (n := n) hf.1 hf.2
    simp only [covK, q]
    rw [beq_prep hw hP pI sP sI, beq_prep hw (prep_powK hsz hP p).1 pI (prep_powK hsz hP p).2 sI]
    congr 1
    congr 1
    funext j
    rw [memL_eq hw (prep_powK hsz hP j).1 (prep_powK hsz hP j).2 hL]
  have e := enumFrom_spec hQ hpq k 0 (by omega) (pidn n w) 1 0 (prep_pidn hf.1 hf.2)
    (PF.pidn_shr hf.1 hf.2)
  simp only [Nat.zero_add, one_mul, List.map_id'] at e
  rw [hc, ← enumeration_trL hQ hn hbs, ← hord, ← length_enumeration] at e
  have hall := List.countP_eq_length.1 e.symm
  intro y hy
  rw [← certificate_originalSubgroup hn gens D bv hbs, ← mem_enumeration_iff _ hV] at hy
  have := hall y hy
  simp only [q, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    List.any_eq_true, List.mem_range, Bool.and_eq_true] at this
  rcases this with (h | h) | ⟨j, hj, h0, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨j, hj, Nat.ne_of_beq_eq_false h0, h⟩)

@[expose] def NgOK (n w N A Ai B Bi : Nat) (ng : NormalGenRecord) : Prop :=
  ∃ (PS PSI LR TR TRI : Nat → Nat) (BP NS CH : Nat),
    RawK n w PS PSI LR TR TRI ng.chain.strongGenerators.length ng.chain.generators.length
      ng.chain.derivations ng.chain.base.length BP NS CH ∧
    ngB n w N A Ai B Bi PS BP LR ng = true

theorem ng_facts {a b : Equiv.Perm (Fin n)} {N A Ai B Bi : Nat} (hn : 1 ≤ n) (h2 : n < 65536)
    (hsz : szOK n w = true) (hG : Nat.card (Subgroup.closure {a, b}) = N)
    (hA : imageList a = (unpack n w A).toList) (hB : imageList b = (unpack n w B).toList)
    (hAi : permOK n w (mask w) (n * w) A Ai = true) (hBi : permOK n w (mask w) (n * w) B Bi = true)
    {ng : NormalGenRecord} (hx : elemOK n w ng.representative = true)
    (hxG : arrPerm n ng.representative ∈ Subgroup.closure {a, b}) (h : NgOK n w N A Ai B Bi ng) :
    (∀ wd ∈ ng.conjugators, ∀ l ∈ wd, l ≠ 0 ∧ l.natAbs ≤ [a, b].length) ∧
      Subgroup.closure {g | g ∈ ng.conjugates [a, b]} = Subgroup.closure {a, b} := by
  obtain ⟨PS, PSI, LR, TR, TRI, BP, NS, CH, hK, hb⟩ := h
  simp only [ngB, ngK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hdeg, hlen⟩, htake⟩, hS⟩, hBP⟩, hnd⟩, hprod⟩, hcl⟩, hab, hconj⟩ := hb
  have hf := szOK_facts hsz
  obtain ⟨hchk, horb⟩ := chain_of_K hn hf.2 h2 hdeg hlen htake hS hBP hnd hK
  set c := ng.chain
  set X := arrPerm n ng.representative
  set gs : List (Equiv.Perm (Fin n)) := [a, b]
  have hxP := (elemOK_facts hx).1
  refine ⟨fun wd hwd l hl => letters_of_abOK (hab wd hwd) l hl, ?_⟩
  obtain ⟨Q, -, -, hsub, hcard⟩ := ChainRecord.exists_records_of_check hchk
  have hgen : ∀ j (hj : j < c.generators.length) (hj' : j < ng.conjugators.length),
      arrPerm n c.generators[j] =
        (wordValue gs ng.conjugators[j])⁻¹ * X * wordValue gs ng.conjugators[j] := by
    intro j hj hj'
    have hjs : j < c.strongGenerators.length := by omega
    have eg : c.generators[j] = c.strongGenerators[j] := by
      have := congrArg (fun l => l[j]?) htake
      simp only [List.getElem?_take, if_pos hj, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem hjs] at this
      exact (Option.some.inj this).symm
    rw [eg]
    have hc := Nat.eq_of_beq_eq_true (hconj j hj')
    rw [List.getD_eq_getElem _ _ hj'] at hc
    have hbj := bindsL_spec hS j hjs
    rw [Nat.zero_add] at hbj
    refine arrPerm_eq_of_bind hbj ?_
    rw [hc]
    exact prep_conjK hsz hA hB hAi hBi hxP (hab _ (List.getElem_mem hj'))
  have hset : {g | ∃ x ∈ c.generators, arrPerm n x = g} = {g | g ∈ ng.conjugates gs} := by
    ext g
    simp only [Set.mem_ofPred_eq, NormalGenRecord.conjugates, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      exact ⟨ng.conjugators[j], List.getElem_mem (by omega), (hgen j hj (by omega)).symm⟩
    · rintro ⟨wd, hw, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
      exact ⟨c.generators[j], List.getElem_mem (by omega), hgen j (by omega) hj⟩
  rw [hset] at hsub
  have hgsG : ∀ g ∈ gs, g ∈ Subgroup.closure {a, b} := by
    intro g hg
    simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hle : Subgroup.closure {g | g ∈ ng.conjugates gs} ≤ Subgroup.closure {a, b} := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_ofPred_eq, NormalGenRecord.conjugates, List.mem_map] at hg
    obtain ⟨wd, -, rfl⟩ := hg
    have hw := wordValue_mem gs _ hgsG wd
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) hxG) hw
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hG, ← hsub, hcard, horb, hprod]

theorem sylowFacts_of_parts {G : Subgroup (Equiv.Perm (Fin n))} {N k : Nat}
    {gs : List (Equiv.Perm (Fin n))} {s : SylowRecord} (hp : s.prime.Prime)
    (hG : Nat.card G = N) (hgsG : ∀ g ∈ gs, g ∈ G)
    (hgen : ∀ a ∈ s.generators, imageList (arrPerm n a) = a) (hPG : s.subgroup n ≤ G)
    (hPcard : Nat.card (s.subgroup n) = s.prime ^ k) (hdiv : N % s.prime ^ k = 0)
    (hndiv : N % s.prime ^ (k + 1) ≠ 0)
    (hreps : ∀ x ∈ s.reps n, x ∈ s.subgroup n ∧ orderOf x = s.prime ∧
      ∀ y ∈ Subgroup.zpowers x, y ≠ 1 → imageList x ≤ imageList y)
    (hrnd : (s.reps n).Nodup)
    (hcov : ∀ Q : Subgroup (Equiv.Perm (Fin n)), Q ≤ s.subgroup n → Nat.card Q = s.prime →
      ∃ x ∈ s.reps n, x ∈ Q)
    (hngf : ∀ ng ∈ s.normalGeneration,
      (∀ wd ∈ ng.conjugators, ∀ l ∈ wd, l ≠ 0 ∧ l.natAbs ≤ gs.length) ∧
        Subgroup.closure {g | g ∈ ng.conjugates gs} = G) :
    SylowFacts G N gs s := by
  set p := s.prime
  have hfact : N.factorization p = k := factorization_eq_of_dvd hp hdiv hndiv
  have hc1 : Nat.card (s.subgroup n) = p ^ N.factorization p := by rw [hPcard, hfact]
  have hc2 : p ^ N.factorization p ∣ N := by
    rw [hfact]
    exact Nat.dvd_of_mod_eq_zero hdiv
  have hc3 : ¬p ^ (N.factorization p + 1) ∣ N := by
    rw [hfact]
    exact fun h => hndiv (Nat.mod_eq_zero_of_dvd h)
  refine ⟨hp, hgen, hPG, hc1, hc2, hc3, hrnd, hreps, ?_, hngf, ?_⟩
  · intro Q hQP hQ
    obtain ⟨x, hx, hxQ⟩ := hcov Q hQP hQ
    refine ⟨x, ⟨hx, hxQ⟩, fun x' ⟨hx', hx'Q⟩ => ?_⟩
    obtain ⟨-, ho, hl⟩ := hreps x hx
    obtain ⟨-, ho', hl'⟩ := hreps x' hx'
    exact (eq_of_lex_least hp ho ho' hQ hxQ hx'Q hl hl').symm
  · have : Fact p.Prime := ⟨hp⟩
    have hcardP' : Nat.card ((s.subgroup n).subgroupOf G) =
        p ^ (Nat.card G).factorization p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG).toEquiv, hPcard, hG, hfact]
    refine ⟨Sylow.ofCard _ hcardP', by
      rw [Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hPG], fun Q hQ hQcard => ?_⟩
    rw [Sylow.coe_ofCard] at hQ
    have hQ1 : Q.map G.subtype ≤ s.subgroup n := by
      have := Subgroup.map_mono (f := G.subtype) hQ
      rwa [Subgroup.map_subgroupOf_eq_of_le hPG] at this
    have hQ1card : Nat.card (Q.map G.subtype) = p := by
      rw [Subgroup.card_map_of_injective G.subtype_injective, hQcard]
    obtain ⟨x, hx, hxQ⟩ := hcov _ hQ1 hQ1card
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hxQ
    obtain ⟨ng, hng, hngx⟩ := List.mem_map.1 hx
    obtain ⟨-, hcl⟩ := hngf ng hng
    have hqx : (q : Equiv.Perm (Fin n)) = arrPerm n ng.representative := hngx.symm
    have hcl' : Subgroup.closure {y | ∃ g ∈ ng.conjugators.map (wordValue gs),
        g⁻¹ * (q : Equiv.Perm (Fin n)) * g = y} = G := by
      refine Eq.trans ?_ hcl
      congr 1
      ext y
      simp only [Set.mem_ofPred_eq, List.mem_map, NormalGenRecord.conjugates,
        exists_exists_and_eq_and]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, by rw [hqx]⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, by rw [hqx]⟩
    have hgsG' : ∀ g ∈ ng.conjugators.map (wordValue gs), g ∈ G := by
      intro g hg
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact wordValue_mem _ G hgsG w
    have htop := normalClosure_eq_top_of_conjugates q.2 _ hgsG' hcl'
    refine top_le_iff.1 ?_
    rw [← htop]
    refine Subgroup.normalClosure_mono ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hq

theorem sylowFacts_of_K [NeZero n] {a b : Equiv.Perm (Fin n)} {N k A Ai B Bi BP0 nb0 : Nat}
    {LR0 TRI0 : Nat → Nat} (hn : 1 ≤ n) (h2 : n < 65536) (hsz : szOK n w = true)
    (hG : Nat.card (Subgroup.closure {a, b}) = N)
    (hA : imageList a = (unpack n w A).toList) (hB : imageList b = (unpack n w B).toList)
    (hAi : permOK n w (mask w) (n * w) A Ai = true) (hBi : permOK n w (mask w) (n * w) B Bi = true)
    (hsiftG : ∀ {x : List Nat}, elemOK n w x = true →
      siftK n w (mask w) (n * w) (pidn n w) LR0 TRI0 BP0 nb0 0 (packL w x) = true →
        arrPerm n x ∈ Subgroup.closure {a, b})
    {s : SylowRecord} (hp : s.prime.Prime) {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}
    {Bl : List Nat} {D : List (List Int)} (hBlt : ∀ x ∈ Bl, x < n)
    (hBl : bindFromK w BP Bl 0 = true) (hnd : Bl.Nodup)
    (hK : RawK n w PS PSI LR TR TRI kS s.generators.length D Bl.length BP NS CH)
    (hs : sylowB n w N k LR0 TRI0 BP0 nb0 PS LR TR TRI BP Bl.length s = true)
    (hng : ∀ ng ∈ s.normalGeneration, NgOK n w N A Ai B Bi ng) :
    SylowFacts (Subgroup.closure {a, b}) N [a, b] s := by
  simp only [sylowB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hge, hps⟩, hsg⟩, hord⟩, hdiv⟩, hndiv⟩, hrep⟩, hrnd⟩, hcov⟩ := hs
  have hf := szOK_facts hsz
  set G := Subgroup.closure {a, b}
  set gensP := s.generators.map (arrPerm n)
  have hgensP : ∀ j < gensP.length, imageList (gensP.getD j 1) = (unpack n w (PS j)).toList := by
    intro j hj
    have hj' : j < s.generators.length := by simpa [gensP] using hj
    have e1 : gensP.getD j 1 = arrPerm n s.generators[j] := by
      rw [List.getD_eq_getElem _ _ hj, List.getElem_map]
    obtain ⟨-, himg, ht, -⟩ := elemOK_facts (hge _ (List.getElem_mem hj'))
    have e2 := Nat.eq_of_beq_eq_true (hps j hj')
    rw [List.getD_eq_getElem _ _ hj'] at e2
    rw [e1, himg, e2, ← ht]
  have hK' : RawK n w PS PSI LR TR TRI kS gensP.length D Bl.length BP NS CH := by
    simpa [gensP] using hK
  have hQ := chainK_of hBlt hf.2 h2 hgensP hBl hK'
  have hbs := baseVec_nodup hBlt hnd
  obtain ⟨hPc, hPmem⟩ := chain_facts hn hbs hQ
  have hPsub : Subgroup.closure {g | g ∈ gensP} = s.subgroup n := by
    rw [SylowRecord.subgroup]
    congr 1
    ext g
    simp [gensP]
  rw [hPsub] at hPc hPmem
  have hgsG : ∀ g ∈ [a, b], g ∈ G := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hPG : s.subgroup n ≤ G := by
    rw [SylowRecord.subgroup, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hsiftG (hge x hx) (hsg x hx)
  have hrepf := fun ng (hng : ng ∈ s.normalGeneration) =>
    repK_facts hn hbs hQ hp.pos (hrep ng hng)
  have hrepe : ∀ ng ∈ s.normalGeneration, elemOK n w ng.representative = true := by
    intro ng hng
    have := hrep ng hng
    simp only [repK, Bool.and_eq_true] at this
    exact this.1.1.1
  have hreps : ∀ x ∈ s.reps n, x ∈ s.subgroup n ∧ orderOf x = s.prime ∧
      ∀ y ∈ Subgroup.zpowers x, y ≠ 1 → imageList x ≤ imageList y := by
    intro x hx
    obtain ⟨ng, hng, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h1, h2, -, h4⟩ := hrepf ng hng
    rw [hPsub] at h1
    exact ⟨h1, h2, h4⟩
  have hrnd' : (s.reps n).Nodup := by
    have e : s.reps n = (s.normalGeneration.map (·.representative)).map (arrPerm n) := by
      simp [SylowRecord.reps]
    rw [e]
    refine (of_decide_eq_true hrnd).map_on ?_
    intro x hx y hy hxy
    obtain ⟨ng, hng, rfl⟩ := List.mem_map.1 hx
    obtain ⟨ng', hng', rfl⟩ := List.mem_map.1 hy
    rw [← (elemOK_facts (hrepe ng hng)).2.1, ← (elemOK_facts (hrepe ng' hng')).2.1, hxy]
  have hcov' := cover_of_K hn hbs hQ (L := s.normalGeneration.map (·.representative))
    (fun x hx => by
      obtain ⟨ng, hng, rfl⟩ := List.mem_map.1 hx
      exact hrepe ng hng) (Nat.eq_of_beq_eq_true hcov)
  rw [hPsub] at hcov'
  have hcovQ : ∀ Q : Subgroup (Equiv.Perm (Fin n)), Q ≤ s.subgroup n → Nat.card Q = s.prime →
      ∃ x ∈ s.reps n, x ∈ Q := by
    intro Q hQP hQ
    have : Nontrivial Q := by
      rw [← Finite.one_lt_card_iff_nontrivial, hQ]
      exact hp.one_lt
    obtain ⟨x, hxQ, hx1⟩ := Q.exists_ne_one_of_nontrivial
    have hxp : x ^ s.prime = 1 := by
      have := pow_card_eq_one' (G := Q) (x := ⟨_, hxQ⟩)
      rw [hQ] at this
      exact congrArg Subtype.val this
    rcases hcov' x (hQP hxQ) with h | h | ⟨j, -, -, hj⟩
    · exact absurd h hx1
    · exact absurd hxp h
    · refine ⟨x ^ j, ?_, Q.pow_mem hxQ j⟩
      simpa [SylowRecord.reps, List.map_map] using hj
  have hngf : ∀ ng ∈ s.normalGeneration,
      (∀ wd ∈ ng.conjugators, ∀ l ∈ wd, l ≠ 0 ∧ l.natAbs ≤ [a, b].length) ∧
        Subgroup.closure {g | g ∈ ng.conjugates [a, b]} = G := by
    intro ng hmem
    obtain ⟨h1, -, -, -⟩ := hrepf ng hmem
    rw [hPsub] at h1
    exact ng_facts hn h2 hsz hG hA hB hAi hBi (hrepe ng hmem) (hPG h1) (hng ng hmem)
  refine sylowFacts_of_parts hp hG hgsG (fun x hx => (elemOK_facts (hge x hx)).2.1) hPG
    (hPc.trans (Nat.eq_of_beq_eq_true hord)) (Nat.eq_of_beq_eq_true hdiv) ?_ hreps hrnd' hcovQ
    hngf
  intro h
  rw [h] at hndiv
  exact absurd hndiv (by decide)

theorem root_of_K {a b : Equiv.Perm (Fin n)} {BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {r : GroupRecord} (hn : 1 ≤ n) (h1 : n + 1 < 2 ^ w) (h2 : n < 65536) (hdeg : r.chain.degree = n)
    (hlen : r.chain.generators.length + r.chain.derivations.length =
      r.chain.strongGenerators.length)
    (hgen : r.chain.strongGenerators.take r.chain.generators.length = r.chain.generators)
    (hS : bindsL n w PS 0 r.chain.strongGenerators = true)
    (hB : bindFromK w BP r.chain.base 0 = true) (hnd : r.chain.base.Nodup)
    (hK : RawK n w PS PSI LR TR TRI r.chain.strongGenerators.length r.chain.generators.length
      r.chain.derivations r.chain.base.length BP NS CH)
    (hgens : r.chain.generators = [imageList a, imageList b]) :
    Nat.card (Subgroup.closure {a, b}) =
        ((List.range r.chain.base.length).map fun i => rcnt (LR i)).prod ∧
      imageList a = (unpack n w (PS 0)).toList ∧ imageList b = (unpack n w (PS 1)).toList ∧
      permOK n w (mask w) (n * w) (PS 0) (PSI 0) = true ∧
      permOK n w (mask w) (n * w) (PS 1) (PSI 1) = true ∧ szOK n w = true ∧
      ∀ {x : List Nat}, elemOK n w x = true →
        siftK n w (mask w) (n * w) (pidn n w) LR TRI BP r.chain.base.length 0 (packL w x) =
          true → arrPerm n x ∈ Subgroup.closure {a, b} := by
  obtain ⟨hchk, horb⟩ := chain_of_K hn h1 h2 hdeg hlen hgen hS hB hnd hK
  have hb := binds_of (by omega) h1 h2 hS hB
  obtain ⟨-, hcard, hsift⟩ := root_facts hchk
  rw [rootGroup_eq_closure hgens] at hcard hsift
  have hperm := (Orb.head_facts hK.1).1
  have hgl : r.chain.generators.length = 2 := by rw [hgens]; rfl
  have hsl : 2 ≤ r.chain.strongGenerators.length := by omega
  have hst : ∀ j < 2, r.chain.strongGenerators[j]! = r.chain.generators[j]! := by
    intro j hj
    have := congrArg (fun l => l[j]!) hgen
    rw [← this, List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
      List.getElem?_take, if_pos (by omega)]
  have himg : ∀ j < 2, r.chain.generators[j]! = (unpack n w (PS j)).toList := by
    intro j hj
    have hbj := bindsL_spec hS j (by omega)
    rw [Nat.zero_add] at hbj
    rw [← hst j hj, getElem!_pos _ j (by omega), ← hbj]
  have hsz : szOK n w = true := by
    have hh := hK.1
    unfold headK at hh
    rw [bAnd_eq, Bool.and_eq_true] at hh
    exact hh.1
  refine ⟨by rw [hcard, horb], ?_, ?_, Orb.allN_iff.1 hperm 0 (by omega),
    Orb.allN_iff.1 hperm 1 (by omega), hsz, fun {x} hx hs => ?_⟩
  · have := himg 0 (by omega)
    rw [hgens] at this
    exact this
  · have := himg 1 (by omega)
    rw [hgens] at this
    exact this
  · obtain ⟨hP, -, -, hc⟩ := elemOK_facts hx
    have hs' := siftK_sound hb hperm hK.2.1 rfl (range_of_canonK hc) hs
    exact (hsift _ _ (rep_unpack hP)).1 hs'

theorem ngOK_of_fam {N A Ai B Bi CH M : Nat} {L : List NormalGenRecord}
    {S SI LR TR TRI : Nat → Nat → Nat} {kS kO nb BP NS : Nat → Nat} {DF : List (List (List Int))}
    (hDF : DF = L.map (·.chain.derivations)) (hM : L.length = M)
    (hall : ∀ j < M, RawK n w (S j) (SI j) (LR j) (TR j) (TRI j) (kS j) (kO j) (DF.getD j [])
      (nb j) (BP j) (NS j) CH)
    (hb : (List.range L.length).all (fun j =>
      Nat.beq (kS j) (L.getD j default).chain.strongGenerators.length &&
      Nat.beq (kO j) (L.getD j default).chain.generators.length &&
      Nat.beq (nb j) (L.getD j default).chain.base.length &&
      ngB n w N A Ai B Bi (S j) (BP j) (LR j) (L.getD j default)) = true) :
    ∀ ng ∈ L, NgOK n w N A Ai B Bi ng := by
  intro ng hng
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hng
  have h := List.all_eq_true.1 hb j (List.mem_range.2 hj)
  rw [List.getD_eq_getElem _ _ hj] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hK := hall j (hM ▸ hj)
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, hDF,
    List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map] at hK
  exact ⟨_, _, _, _, _, _, _, _, hK, h4⟩

theorem sylows_of_fam [NeZero n] {a b : Equiv.Perm (Fin n)} {N A Ai B Bi BP0 nb0 : Nat}
    {LR0 TRI0 : Nat → Nat} (hn : 1 ≤ n) (h2 : n < 65536) (hsz : szOK n w = true)
    (hG : Nat.card (Subgroup.closure {a, b}) = N)
    (hA : imageList a = (unpack n w A).toList) (hB : imageList b = (unpack n w B).toList)
    (hAi : permOK n w (mask w) (n * w) A Ai = true) (hBi : permOK n w (mask w) (n * w) B Bi = true)
    (hsiftG : ∀ {x : List Nat}, elemOK n w x = true →
      siftK n w (mask w) (n * w) (pidn n w) LR0 TRI0 BP0 nb0 0 (packL w x) = true →
        arrPerm n x ∈ Subgroup.closure {a, b})
    {L : List SylowRecord} {ks : List Nat} {S SI LR TR TRI : Nat → Nat → Nat}
    {kS kO nb BP NS : Nat → Nat} {CH M : Nat} {DF : List (List (List Int))}
    {BL : List (List Nat)} (hM : L.length = M)
    (hall : ∀ j < M, RawK n w (S j) (SI j) (LR j) (TR j) (TRI j) (kS j) (kO j) (DF.getD j [])
      (nb j) (BP j) (NS j) CH)
    (hprime : ∀ s ∈ L, s.prime.Prime)
    (hb : (List.range L.length).all (fun j =>
      Nat.beq (kO j) (L.getD j default).generators.length &&
      Nat.beq (nb j) (BL.getD j []).length && (BL.getD j []).all (fun x => decide (x < n)) &&
      bindFromK w (BP j) (BL.getD j []) 0 && decide (BL.getD j []).Nodup &&
      sylowB n w N (ks.getD j 0) LR0 TRI0 BP0 nb0 (S j) (LR j) (TR j) (TRI j) (BP j) (nb j)
        (L.getD j default)) = true)
    (hng : ∀ j < L.length, ∀ ng ∈ (L.getD j default).normalGeneration,
      NgOK n w N A Ai B Bi ng) :
    ∀ s ∈ L, SylowFacts (Subgroup.closure {a, b}) N [a, b] s := by
  intro s hs
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  have h := List.all_eq_true.1 hb j (List.mem_range.2 hj)
  have hngj := hng j hj
  rw [List.getD_eq_getElem _ _ hj] at h hngj
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h3⟩, hlt⟩, hBP⟩, hnd⟩, hs'⟩ := h
  have hK := hall j (hM ▸ hj)
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h3] at hK
  rw [Nat.eq_of_beq_eq_true h3] at hs'
  exact sylowFacts_of_K hn h2 hsz hG hA hB hAi hBi hsiftG (hprime _ hs) hlt hBP hnd hK hs' hngj

end CFSG.KC.MathieuK

end
