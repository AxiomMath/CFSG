module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRu
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjT
public import CFSG.Certificates.Kernel.Census.BaseSound
public import CFSG.Certificates.Kernel.Census.RestrictSound
public import CFSG.Certificates.Kernel.Census.ToMainConj
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Certificates.Kernel.Census.SoundProof

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ru

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.KC.Census CFSG.KC.Census.Base CFSG.KC.Census.Restrict CFSG.Certificates
open scoped commutatorElement

@[expose] noncomputable def ruCheckR (d : ConjDataP) (ps : List ℕ) (e0 : Array ℕ) (L : ℕ → ℕ)
    (pe : Array ℕ) (O ix : ℕ) (xw : List (List ℕ))
    (wits : List (ℕ × ℕ × List (ℕ × List ℕ × List ℕ) × ℕ)) (em yw : List ℕ) : Bool :=
  conjTreeOKW 128 ps (fun a => eqA 128 a (idA 128)) (d.toMain 128 7) (e0.map (unpackP 128 7)) &&
    ps.all (fun p => Nat.blt p 128) &&
    Nat.beq d.xs.length 14 && Nat.beq e0.size 2 && Nat.beq em.length 2 &&
    eqA 128 (unpackP 128 7 e0[0]!) (pcA 128 (d.xs.map (unpackP 128 7)) em[0]!) &&
    eqA 128 (unpackP 128 7 e0[1]!) (pcA 128 (d.xs.map (unpackP 128 7)) em[1]!) &&
    (List.range 18).all (fun k => eqA 4060 (unpackP 4060 12 (L k)) (ruField4060 3)[k]!) &&
    invLB 12 18 L 4060 &&
    (List.range 128).all (fun q => Nat.blt (at' 12 O q) 4060 && Nat.beq (at' 7 ix (at' 12 O q)) q) &&
    Nat.beq xw.length 14 && xw.all (fun x => x.all fun k => Nat.blt k 36) &&
    pcRelB 12 L ruPS xw d.rs d.cjs &&
    (xw.zip d.xs).all (fun p => resB 12 L 7 128 O ix p.1 p.2) &&
    (List.range d.nodes.size).all (fun i => !d.nodes[i]!.wit.isMono || wits.any fun t => Nat.beq t.1 i) &&
    wits.all (fun t =>
      t.2.2.1.all (fun f => f.2.1.all (fun k => Nat.blt k 36) && f.2.2.all (fun k => Nat.blt k 36)) &&
      memA 128 (maskCert 128 (d.nodes[t.1]!.basis.map (unpackP 128 7)))
        (pcA 128 (d.xs.map (unpackP 128 7)) t.2.1) &&
      t.2.2.1.all (fun f => memA 128 (maskCert 128 (d.nodes[t.1]!.basis.map (unpackP 128 7)))
        (pcA 128 (d.xs.map (unpackP 128 7)) f.1)) &&
      witB 12 18 L ruPS xw t.2.1 t.2.2.1 t.2.2.2) &&
    Nat.beq pe.size 2 && yw.all (fun k => Nat.blt k 36) &&
    eqA 4060 (unpackP 4060 12 pe[0]!) ruE0[0]! && eqA 4060 (unpackP 4060 12 pe[1]!) ruE0[1]! &&
    (List.range 4060).all (fun b => Nat.blt (at' 12 pe[0]! b) 4060 &&
      Nat.blt (at' 12 pe[1]! b) 4060) &&
    conjB 12 L (List.range 4060) xw em[0]! yw pe[0]! &&
    conjB 12 L (List.range 4060) xw em[1]! yw pe[1]!

section P


theorem ruStrong_mem {k : ℕ} (hk : k < 18) : permOfArr 4060 (ruField4060 3)[k]! ∈ ruP := by
  have hc : k < ruChainJoin.strongCount := by
    change k < (ruField4060 3).size
    rw [ruField4060, Array.size_ofFn]
    exact hk
  have h := CFSG.Certificates.RawSchreierDatum.strong_get_mem_originalSubgroup ruChainJoin
    (ruChain_valid ruChainJoin_check.1) ⟨k, hc⟩
  have e : ruChainJoin.strong.get ⟨k, hc⟩ = permOfArr 4060 (ruField4060 3)[k]! :=
    CFSG.Certificates.RawSchreierDatum.ofArrays_strong_get _
  rw [ruP_eq_sup, ← ruChainJoin_sub]
  rwa [e] at h

theorem ruBase : BaseOf ruP ruPS := by
  refine ⟨ruPS_lt, fun g hg h => ?_⟩
  have hQ : ValidSchreier ruChainJoin := ruChain_valid ruChainJoin_check.1
  obtain ⟨hlev, hterm, -⟩ := RawSchreierDatum.schreier_chain_order ruChainJoin hQ
  have h1 := hlev ruChainJoin.baseCount le_rfl
  rw [hterm] at h1
  have e : ruChainJoin.base.toList = ruFinList 4060 (by decide) ruJoinBase :=
    RawSchreierDatum.ofArrays_base_toList
  have hmem : g ∈ ruChainJoin.originalSubgroup ⊓ fixingSubgroup (Equiv.Perm (Fin 4060))
      {b | b ∈ ruChainJoin.base.toList.take ruChainJoin.baseCount} := by
    rw [Subgroup.mem_inf]
    refine ⟨by rw [ruChainJoin_sub, ← ruP_eq_sup]; exact hg, ?_⟩
    rw [mem_fixingSubgroup_iff]
    intro b hb
    have hb' : b ∈ ruChainJoin.base.toList := List.mem_of_mem_take hb
    rw [e] at hb'
    have hlt : b.val ∈ ruPS := by
      simp only [ruFinList, ruJoinBase, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false] at hb'
      obtain ⟨x, hx, rfl⟩ := hb'
      rcases hx with rfl | rfl | rfl | rfl <;> simp [ruPS]
    exact h b.val b.2 hlt
  rw [← h1] at hmem
  exact Subgroup.mem_bot.1 hmem

@[expose] noncomputable def ruLet (k : ℕ) : Equiv.Perm (Fin 4060) :=
  if k < 18 then permOfArr 4060 (ruField4060 3)[k]! else (permOfArr 4060 (ruField4060 3)[k - 18]!)⁻¹

set_option maxRecDepth 100000 in
theorem ruLetters_of {L : ℕ → ℕ}
    (h1 : (List.range 18).all (fun k => eqA 4060 (unpackP 4060 12 (L k)) (ruField4060 3)[k]!) =
      true) (h2 : invLB 12 18 L 4060 = true) : Letters 4060 12 18 L ruLet := by
  have hinv : ∀ k < 18, ∀ p < 4060, at' 12 (L k) p < 4060 ∧
      at' 12 (L (18 + k)) (at' 12 (L k) p) = p := by
    intro k hk p hp
    unfold invLB at h2
    have := List.all_eq_true.1 (List.all_eq_true.1 h2 k (List.mem_range.2 hk)) p
      (List.mem_range.2 hp)
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at this
    exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩
  have hrep : ∀ k < 18, Rep 4060 (ruField4060 3)[k]! (permOfArr 4060 (ruField4060 3)[k]!) ∧
      ∀ p < 4060, ((ruField4060 3)[k]!)[p]! = at' 12 (L k) p := by
    intro k hk
    have he := List.all_eq_true.1 h1 k (List.mem_range.2 hk)
    have hget : ∀ p < 4060, ((ruField4060 3)[k]!)[p]! = at' 12 (L k) p := by
      intro p hp
      have := allLt_spec he hp
      rw [beq_iff_eq, SP.unpackP_get, if_pos hp] at this
      exact this.symm
    refine ⟨(rep_permOfArr (r := unpackP 4060 12 (L (18 + k))) ?_).1, hget⟩
    unfold isInvA
    rw [allLt_iff]
    intro i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [hget i hi, SP.unpackP_get, if_pos (hinv k hk i hi).1]
    exact hinv k hk i hi
  refine ⟨fun k hk p hp => ?_, fun k hk => ?_⟩
  · by_cases h18 : k < 18
    · rw [ruLet, if_pos h18, ← (hrep k h18).1.apply hp, (hrep k h18).2 p hp]
    · have hj : k - 18 < 18 := by omega
      rw [ruLet, if_neg h18]
      set g := permOfArr 4060 (ruField4060 3)[k - 18]!
      set q := g⁻¹ ⟨p, hp⟩
      have hq : at' 12 (L (k - 18)) q = p := by
        rw [← (hrep _ hj).2 q q.2, (hrep _ hj).1.apply q.2]
        change ((g (g⁻¹ ⟨p, hp⟩) : Fin 4060) : ℕ) = p
        simp
      have := (hinv _ hj q q.2).2
      rw [hq, show 18 + (k - 18) = k by omega] at this
      exact this
  · simp only [ruLet, if_pos hk, if_neg (show ¬ 18 + k < 18 by omega),
      show 18 + k - 18 = k by omega]

theorem ruLet_mem {k : ℕ} (hk : k < 2 * 18) : ruLet k ∈ ruP := by
  unfold ruLet
  split_ifs with h
  · exact ruStrong_mem h
  · exact ruP.inv_mem (ruStrong_mem (by omega))

end P

theorem map_pcG {G H : Type*} [Group G] [Group H] (φ : G →* H) :
    ∀ (l : List G) (m : ℕ), φ (pcG l m) = pcG (l.map φ) m
  | [], _ => map_one φ
  | x :: l, m => by
    rw [pcG, List.map_cons, pcG, map_mul, map_pcG φ l (m / 2)]
    split_ifs
    · rfl
    · rw [map_one]

theorem permOfArr_eq_of_rep_ruR {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    permOfArr n t = g := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := g.injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [permOfArr, dite_eq_left hc]
  change t[(x : ℕ)]! = _
  exact h x

theorem permsA_ruE0_pair :
    permsA 4060 ruE0 = {permOfArr 4060 ruE0[0]!, permOfArr 4060 ruE0[1]!} := by
  have hs : ruE0.size = 2 := rfl
  ext g
  simp only [permsA, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, hs]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩


set_option maxRecDepth 100000 in
theorem census_of_ruCheckR {d : ConjDataP} {ps : List ℕ} {e0 : Array ℕ} {L : ℕ → ℕ}
    {pe : Array ℕ} {O ix : ℕ} {xw : List (List ℕ)}
    {wits : List (ℕ × ℕ × List (ℕ × List ℕ × List ℕ) × ℕ)} {em yw : List ℕ}
    (h : ruCheckR d ps e0 L pe O ix xw wits em yw = true) :
    YCensus (ruP.subgroupOf ruP) (ExcClass ruP ruE0Sub) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold ruCheckR at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨htree, hps⟩, hlen⟩, he0s⟩, hems⟩, he00⟩, he01⟩, hlet⟩, hinvL⟩,
    hpts⟩, hxwl⟩, hxwk⟩, hrel⟩, hres⟩, hcov⟩, hwits⟩, hpes⟩, hywk⟩, hpe0⟩, hpe1⟩, hpel⟩, hc0⟩,
    hc1⟩ := h
  have hps' : ∀ p ∈ ps, p < 128 := fun p hp => Nat.blt_eq.mp (List.all_eq_true.1 hps p hp)
  have hlen' : d.xs.length = 14 := Nat.eq_of_beq_eq_true hlen
  have hxwl' : xw.length = 14 := Nat.eq_of_beq_eq_true hxwl
  have HL := ruLetters_of hlet hinvL
  have hℓ : ∀ k < 2 * 18, ruLet k ∈ ruP := fun k hk => ruLet_mem hk
  have hwok : ∀ x : List ℕ, (x.all fun k => Nat.blt k 36) = true → WordOK 18 x :=
    fun x hx k hk => Nat.blt_eq.mp (List.all_eq_true.1 hx k hk)
  have hxw : ∀ x ∈ xw, WordOK 18 x := fun x hx => hwok x (List.all_eq_true.1 hxwk x hx)
  obtain ⟨X, hXdef⟩ : ∃ X, X = xw.map (wordPerm ruLet) := ⟨_, rfl⟩
  have hXl : X.length = 14 := by rw [hXdef, List.length_map, hxwl']
  have hXP : ∀ g ∈ X, g ∈ ruP := fun g hg => by
    rw [hXdef] at hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
    exact wordPerm_mem HL hℓ (hxw x hx)
  have hrelX : PcRel X := hXdef ▸ pcRel_of_pcRelB HL ruBase hℓ xw d.rs d.cjs hxw hrel
  obtain ⟨S4, hS4def⟩ : ∃ S4 : Subgroup (Equiv.Perm (Fin 4060)), S4 = closure {a | a ∈ X} :=
    ⟨_, rfl⟩
  have hS4P : S4 ≤ ruP := hS4def ▸ (closure_le ruP).2 fun g hg => hXP g hg
  obtain ⟨xsU, hxsU⟩ : ∃ xsU, xsU = d.xs.map (unpackP 128 7) := ⟨_, rfl⟩
  have htm : (d.toMain 128 7).xs = xsU := by rw [hxsU]; rfl
  obtain ⟨hxv, -, -⟩ := pc_of_conjTreeOKW htree
  rw [htm] at hxv
  obtain ⟨S', hS'def⟩ : ∃ S', S' = pcSub 128 xsU := ⟨_, rfl⟩
  have hinW : ∀ a, validA 128 a = true → eqA 128 a (idA 128) = true → permOfArr 128 a ∈ S' :=
    fun a hv he => by
      rw [eq_of_eqA (rep_of_validA hv) rep_idA he]
      exact S'.one_mem
  have hSW : pcSub 128 (d.toMain 128 7).xs ≤ S' := by rw [hS'def, htm]
  obtain ⟨hS'card, htw⟩ := tree_of_conjTreeOKW hps' hinW hSW htree
  rw [htm, ← hS'def] at hS'card htw
  have hS'card' : Nat.card S' = 2 ^ 14 := by
    rw [hS'card, hxsU, List.length_map, hlen']
  have hpt : ∀ q < 128, at' 12 O q < 4060 ∧ at' 7 ix (at' 12 O q) = q := by
    intro q hq
    have := List.all_eq_true.1 hpts q (List.mem_range.2 hq)
    simp only [Bool.and_eq_true] at this
    exact ⟨Nat.blt_eq.mp this.1, Nat.eq_of_beq_eq_true this.2⟩
  have hOl : ∀ q < 128, at' 12 O q < 4060 := fun q hq => (hpt q hq).1
  have hOi : ∀ q < 128, at' 7 ix (at' 12 O q) = q := fun q hq => (hpt q hq).2
  let Of : Fin 128 → Fin 4060 := fun q => ⟨at' 12 O q, hOl q q.2⟩
  have hOf : Function.Injective Of := fun a b hab => by
    have := congrArg (fun x : Fin 4060 => at' 7 ix x.val) hab
    simp only [Of, hOi a a.2, hOi b b.2] at this
    exact Fin.ext this
  have hgen : ∀ j (hj : j < 14), ∃ hs : wordPerm ruLet xw[j] ∈ stab Of,
      resHom hOf ⟨_, hs⟩ = permOfArr 128 (unpackP 128 7 d.xs[j]) := by
    intro j hj
    have hj1 : j < xw.length := by omega
    have hj2 : j < d.xs.length := by omega
    have hr := List.all_eq_true.1 hres (xw[j], d.xs[j])
      (mem_zip_of_lt hj1 hj2)
    unfold resB at hr
    have hq : ∀ q : Fin 128, (wordPerm ruLet xw[j]) (Of q) =
        Of ⟨at' 7 d.xs[j] q, by have h7 := CFSG.KS.PackFld.pg_lt 7 d.xs[j] q.val; exact h7⟩ := by
      intro q
      have hq := List.all_eq_true.1 hr q.val (List.mem_range.2 q.2)
      simp only [Bool.and_eq_true] at hq
      have hw := wPt_eq HL xw[j] (hxw _ (List.getElem_mem hj1)) _ (hOl q q.2)
      rw [hw] at hq
      apply Fin.ext
      change _ = at' 12 O (at' 7 d.xs[j] q)
      rw [Nat.eq_of_beq_eq_true hq.2]
      exact (Nat.eq_of_beq_eq_true hq.1).symm
    have hs : wordPerm ruLet xw[j] ∈ stab Of := mem_stab_of_maps hOf fun q => ⟨_, hq q⟩
    refine ⟨hs, resHom_eq hOf fun q => ?_⟩
    have hv := hxv _ (by rw [hxsU]; exact List.mem_map_of_mem (List.getElem_mem hj2))
    have hrep := rep_of_validA hv
    rw [hq q]
    congr 1
    apply Fin.ext
    rw [← hrep.apply q.2, SP.unpackP_get, if_pos q.2]
  have hmemX : ∀ j (hj : j < 14), wordPerm ruLet xw[j] ∈ S4 := fun j hj => by
    rw [hS4def]
    refine subset_closure ?_
    rw [Set.mem_setOf_eq, hXdef]
    exact List.mem_map_of_mem (List.getElem_mem _)
  have hS4stab : S4 ≤ stab Of := by
    rw [hS4def, closure_le]
    intro g hg
    rw [Set.mem_setOf_eq, hXdef] at hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [List.getElem_map]
    exact (hgen j (by simpa [hxwl'] using hj)).1
  let f : ↥S4 →* Equiv.Perm (Fin 128) := (resHom hOf).comp (inclusion hS4stab)
  have hfgen : ∀ j (hj : j < 14), f ⟨_, hmemX j hj⟩ = permOfArr 128 (unpackP 128 7 d.xs[j]) :=
    fun j hj => (hgen j hj).2
  let XW : List ↥S4 := List.ofFn (n := 14) fun j => ⟨_, hmemX j.1 j.2⟩
  have hXW : XW.map S4.subtype = X := by
    rw [hXdef]
    apply List.ext_getElem
    · simp [XW, hxwl']
    · intro i h1 h2
      simp only [XW, List.getElem_map, List.getElem_ofFn]
      rfl
  have hfXW : XW.map f = xsU.map (permOfArr 128) := by
    apply List.ext_getElem
    · simp [XW, hxsU, hlen']
    · intro i h1 h2
      have hi : i < 14 := by simpa [XW] using h1
      simp only [XW, List.getElem_map, List.getElem_ofFn]
      rw [hfgen i hi]
      simp [hxsU]
  have hpcS : ∀ m, pcG X m = ((pcG XW m : ↥S4) : Equiv.Perm (Fin 4060)) := fun m => by
    rw [← hXW]
    exact (map_pcG S4.subtype XW m).symm
  have hfpc : ∀ m, f (pcG XW m) = pcG (xsU.map (permOfArr 128)) m := fun m => by
    rw [map_pcG, hfXW]
  have hXWgen : closure {a | a ∈ XW} = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    obtain ⟨m, -, hm⟩ := exists_pcG_of_pcRel hrelX g (hS4def ▸ g.2)
    have : g = pcG XW m := Subtype.ext (by rw [← hpcS, hm])
    rw [this]
    exact pcG_mem XW m
  have hrange : f.range = S' := by
    rw [MonoidHom.range_eq_map, ← hXWgen, MonoidHom.map_closure, hS'def, pcSub, ← hfXW]
    congr 1
    ext b
    simp
  have hcardS4 : Nat.card ↥S4 ≤ 2 ^ 14 := by
    have hsurj : Function.Surjective (fun m : Fin (2 ^ 14) => (pcG XW m : ↥S4)) := by
      intro g
      obtain ⟨m, hm, he⟩ := exists_pcG_of_pcRel hrelX g (hS4def ▸ g.2)
      exact ⟨⟨m, hXl ▸ hm⟩, Subtype.ext (by rw [← hpcS]; exact he)⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this
  have hinj : Function.Injective f :=
    injective_of_card_le_range f (by rw [hrange, hS'card']; exact hcardS4)
  have hS4card : Nat.card ↥S4 = 2 ^ 14 := by
    have := Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥S4)) (f := f) hinj
    rw [← MonoidHom.range_eq_map, hrange, hS'card', card_top] at this
    exact this.symm
  have hS4le : S4 ≤ ruP.subtype.range := by rwa [range_subtype]
  obtain ⟨SyP, hSPdef⟩ : ∃ SyP, SyP = S4.comap ruP.subtype := ⟨_, rfl⟩
  have hSPmap : SyP.map ruP.subtype = S4 := by rw [hSPdef]; exact map_comap_eq_self hS4le
  have hSPcard : Nat.card SyP = 2 ^ 14 := by
    rw [← card_map_of_injective ruP.subtype_injective, hSPmap, hS4card]
  have hSyl : IsSylowOf 2 SyP ⊤ := by
    rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card hSPcard, fun h2 => ?_⟩
    have h1 := SyP.card_mul_index
    rw [hSPcard, card_ruP] at h1
    have hidx : SyP.index = 8906625 := by omega
    rw [hidx] at h2
    norm_num at h2
  have hconjP : ∀ v ∈ ruP, ruP.map (MulAut.conj v).toMonoidHom = ruP := by
    intro v hv
    refine le_antisymm ?_ fun x hx => ⟨v⁻¹ * x * v, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hv hx) (inv_mem hv)
    · exact mul_mem (mul_mem (inv_mem hv) hx) hv
    · simp [MulAut.conj_apply, mul_assoc]
  refine yCensus_of_le_sylow ru_normal hSyl (fun E w h => excClass_of_map_conj h)
    fun E hES hE hE4 hnot => ?_
  obtain ⟨E4, hE4def⟩ : ∃ E4, E4 = E.map ruP.subtype := ⟨_, rfl⟩
  have hE4S : E4 ≤ S4 := by
    rw [hE4def, ← hSPmap]
    exact map_mono hES
  have hE4c : Nat.card E4 = Nat.card E := by
    rw [hE4def]
    exact card_map_of_injective ruP.subtype_injective
  have hE4a : IsElemAbelian 2 E4 := hE4def ▸ isElemAbelian_map hE _
  obtain ⟨EW, hEWdef⟩ : ∃ EW, EW = E4.subgroupOf S4 := ⟨_, rfl⟩
  have hEWmap : EW.map S4.subtype = E4 := by
    rw [hEWdef, subgroupOf_map_subtype, inf_eq_left.mpr hE4S]
  have hEWc : Nat.card EW = Nat.card E4 := by
    rw [← card_map_of_injective S4.subtype_injective, hEWmap]
  have hE'S : EW.map f ≤ S' := hrange ▸ map_le_range f EW
  have hE'a : IsElemAbelian 2 (EW.map f) :=
    isElemAbelian_map (hEWdef ▸ CFSG.Open.IsElemAbelian.subgroupOf hE4a S4) f
  have hE'c : Nat.card (EW.map f) = Nat.card E := by
    rw [card_map_of_injective hinj, hEWc, hE4c]
  have hmemE4 : ∀ g : ↥S4, f g ∈ EW.map f → (g : Equiv.Perm (Fin 4060)) ∈ E4 := by
    intro g hg
    obtain ⟨e, he, hfe⟩ := hg
    rw [← hinj hfe, ← hEWmap]
    exact ⟨e, he, rfl⟩
  suffices hY : YWitness ruP E4 by
    rw [← yWitness_map_iff ruP.subtype ruP.subtype_injective, subgroupOf_map_subtype, inf_idem,
      ← hE4def]
    exact hY
  have hnodes : (d.toMain 128 7).nodes = d.nodes.map (NodeP.toMain 128 7) := rfl
  have hpcf : ∀ m, pcG (xsU.map (permOfArr 128)) m = f (pcG XW m) := fun m => (hfpc m).symm
  have hrepc : ∀ m, Rep 128 (pcA 128 xsU m) (pcG (xsU.map (permOfArr 128)) m) :=
    fun m => rep_pcA hxv m
  rcases htw _ hE'S hE'a (hE'c ▸ hE4) with ⟨i, hi, hmono, s, hs, hsle⟩ | ⟨w, hw, heq⟩
  ·
    have hi' : i < d.nodes.size := by simpa [hnodes] using hi
    have hni : (d.toMain 128 7).nodes[i]! = (d.nodes[i]!).toMain 128 7 := by
      rw [hnodes]
      exact SP.map_get _ _ hi'
    have hmono' : d.nodes[i]!.wit.isMono = true := by
      rw [hni] at hmono
      simpa [NodeP.toMain, SP.isMono_toMain] using hmono
    have hc := List.all_eq_true.1 hcov i (List.mem_range.2 hi')
    rw [hmono'] at hc
    simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at hc
    obtain ⟨t, ht, hti⟩ := hc
    have hti' : t.1 = i := Nat.eq_of_beq_eq_true hti
    have hw : (((t.2.2.1.all fun f => (f.2.1.all fun k => Nat.blt k 36) &&
        f.2.2.all fun k => Nat.blt k 36) &&
        memA 128 (maskCert 128 (d.nodes[t.1]!.basis.map (unpackP 128 7)))
          (pcA 128 (d.xs.map (unpackP 128 7)) t.2.1) &&
        t.2.2.1.all fun f => memA 128 (maskCert 128 (d.nodes[t.1]!.basis.map (unpackP 128 7)))
          (pcA 128 (d.xs.map (unpackP 128 7)) f.1)) &&
        witB 12 18 L ruPS xw t.2.1 t.2.2.1 t.2.2.2) = true := List.all_eq_true.1 hwits t ht
    simp only [Bool.and_eq_true, List.all_eq_true] at hw
    obtain ⟨⟨⟨hfw, hme⟩, hmt⟩, hwb⟩ := hw
    have hfac : FacOK 18 t.2.2.1 := fun g hg => by
      have := hfw g hg
      exact ⟨fun k hk => Nat.blt_eq.mp (this.1 k hk), fun k hk => Nat.blt_eq.mp (this.2 k hk)⟩
    obtain ⟨y, hy, hyo⟩ := exists_order4_of_witB HL ruBase hℓ hxw hfac hwb
    rw [← hXdef] at hy
    obtain ⟨s4, rfl⟩ : ∃ s4, f s4 = s := by
      rw [← hrange] at hs
      exact hs
    have hbasis : (d.toMain 128 7).nodes[i]!.basis = d.nodes[t.1]!.basis.map (unpackP 128 7) := by
      rw [hni, hti']
      rfl
    have hgenE : ∀ m, memA 128 (maskCert 128 (d.nodes[t.1]!.basis.map (unpackP 128 7)))
        (pcA 128 xsU m) = true →
        (s4 : Equiv.Perm (Fin 4060)) * pcG X m * (s4 : Equiv.Perm (Fin 4060))⁻¹ ∈ E4 := by
      intro m hm
      rw [← hbasis] at hm
      have h1 := mem_nodeSub_of_conjTreeOKW hps' htree hi (hrepc m) hm
      rw [hpcf] at h1
      have h2 : f (s4 * pcG XW m * s4⁻¹) ∈ EW.map f := by
        refine hsle ⟨_, h1, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv]
      have := hmemE4 _ h2
      rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hpcS] at this
    have hKle : (closure (insert (pcG X t.2.1) ((t.2.2.1.map fun g => pcG X g.1).toFinset :
        Set (Equiv.Perm (Fin 4060))))).map (MulAut.conj (s4 : Equiv.Perm (Fin 4060))).toMonoidHom
          ≤ E4 := by
      rw [map_le_iff_le_comap, closure_le]
      intro g hg
      rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases hg with rfl | hg
      · exact hgenE _ (by rw [hxsU]; exact hme)
      · simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map] at hg
        obtain ⟨g', hg', rfl⟩ := hg
        exact hgenE _ (by rw [hxsU]; exact hmt g' hg')
    have hs4P : (s4 : Equiv.Perm (Fin 4060)) ∈ ruP := hS4P s4.2
    refine Or.inl ⟨(s4 : Equiv.Perm (Fin 4060)) * y * (s4 : Equiv.Perm (Fin 4060))⁻¹, ?_, ?_⟩
    · have hm : (s4 : Equiv.Perm (Fin 4060)) * y * (s4 : Equiv.Perm (Fin 4060))⁻¹ ∈
          (nE ruP _).map (MulAut.conj (s4 : Equiv.Perm (Fin 4060))).toMonoidHom :=
        ⟨y, hy, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      rw [map_nE _ (MulAut.conj (s4 : Equiv.Perm (Fin 4060))).injective, hconjP _ hs4P] at hm
      exact nE_mono ruP hKle hm
    · have ho := orderOf_injective (MulAut.conj (s4 : Equiv.Perm (Fin 4060))).toMonoidHom
        (MulAut.conj (s4 : Equiv.Perm (Fin 4060))).injective y
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at ho
      rw [ho, hyo]
  ·
    exfalso
    apply hnot
    obtain ⟨w4, rfl⟩ : ∃ w4, f w4 = w := by
      rw [← hrange] at hw
      exact hw
    have he0s' : e0.size = 2 := Nat.eq_of_beq_eq_true he0s
    have hems' : em.length = 2 := Nat.eq_of_beq_eq_true hems
    have he0p : ∀ k < 2, permOfArr 128 (e0.map (unpackP 128 7))[k]! = f (pcG XW em[k]!) := by
      intro k hk
      have hek : eqA 128 (unpackP 128 7 e0[k]!) (pcA 128 xsU em[k]!) = true := by
        interval_cases k
        · rw [hxsU]; exact he00
        · rw [hxsU]; exact he01
      rw [SP.map_get _ _ (by omega), ← hpcf]
      refine permOfArr_eq_of_rep_ruR (CFSG.RankThree.Native.rep_of_eqA (hrepc _) ?_)
      unfold eqA at hek ⊢
      rw [allLt_iff] at hek ⊢
      intro x hx
      have := hek x hx
      rw [beq_iff_eq] at this ⊢
      exact this.symm
    have hpermsA : permsA 128 (e0.map (unpackP 128 7)) =
        {f (pcG XW em[0]!), f (pcG XW em[1]!)} := by
      have hs : (e0.map (unpackP 128 7)).size = 2 := by rw [Array.size_map, he0s']
      ext g
      simp only [permsA, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, hs]
      constructor
      · rintro ⟨k, hk, rfl⟩
        interval_cases k
        · exact Or.inl (he0p 0 (by norm_num))
        · exact Or.inr (he0p 1 (by norm_num))
      · rintro (rfl | rfl)
        · exact ⟨0, by norm_num, he0p 0 (by norm_num)⟩
        · exact ⟨1, by norm_num, he0p 1 (by norm_num)⟩
    obtain ⟨E0W, hE0W⟩ : ∃ E0W : Subgroup ↥S4,
        E0W = closure {pcG XW em[0]!, pcG XW em[1]!} := ⟨_, rfl⟩
    have hEW : EW = E0W.map (MulAut.conj w4).toMonoidHom := by
      apply map_injective hinj
      rw [heq, hpermsA, map_map, hE0W, MonoidHom.map_closure, MonoidHom.map_closure,
        Set.image_pair, Set.image_pair]
      congr 1
      ext g
      simp [MulAut.conj_apply]
    obtain ⟨Y, hY⟩ : ∃ Y, Y = wordPerm ruLet yw := ⟨_, rfl⟩
    have hYP : Y ∈ ruP := hY ▸ wordPerm_mem HL hℓ (hwok yw hywk)
    have hpe : ∀ k < 2, permOfArr 4060 ruE0[k]! = Y⁻¹ * pcG X em[k]! * Y := by
      intro k hk
      have hck : conjB 12 L (List.range 4060) xw em[k]! yw pe[k]! = true := by
        interval_cases k
        · exact hc0
        · exact hc1
      have hpk : eqA 4060 (unpackP 4060 12 pe[k]!) ruE0[k]! = true := by
        interval_cases k
        · exact hpe0
        · exact hpe1
      refine permOfArr_eq_of_rep_ruR fun b => ?_
      have hbl : at' 12 pe[k]! b < 4060 := by
        have := List.all_eq_true.1 hpel b (List.mem_range.2 b.2)
        simp only [Bool.and_eq_true] at this
        interval_cases k
        · exact Nat.blt_eq.mp this.1
        · exact Nat.blt_eq.mp this.2
      have e1 := Nat.eq_of_beq_eq_true (List.all_eq_true.1 hck b (List.mem_range.2 b.2))
      rw [wPt_eq HL yw (hwok yw hywk) b b.2, pcwPt_eq HL xw hxw _ _ (Fin.isLt _),
        wPt_eq HL yw (hwok yw hywk) _ hbl, ← hXdef, ← hY] at e1
      have e2 : (ruE0[k]!)[(b : ℕ)]! = at' 12 pe[k]! b := by
        have := allLt_spec hpk b.2
        rw [beq_iff_eq, SP.unpackP_get, if_pos b.2] at this
        exact this.symm
      have e3 : (pcG X em[k]!) (Y b) = Y ⟨at' 12 pe[k]! b, hbl⟩ := Fin.ext e1
      have e4 : Y⁻¹ (Y ⟨at' 12 pe[k]! b, hbl⟩) = ⟨at' 12 pe[k]! b, hbl⟩ := by simp
      rw [e2, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, e3, e4]
    have hE0sub : ruE0Sub = (closure {pcG X em[0]!, pcG X em[1]!}).map
        (MulAut.conj Y⁻¹).toMonoidHom := by
      rw [ruE0Sub, permsA_ruE0_pair, hpe 0 (by norm_num), hpe 1 (by norm_num),
        MonoidHom.map_closure, Set.image_pair]
      simp [MulAut.conj_apply]
    refine ⟨(w4 : Equiv.Perm (Fin 4060)) * Y, ruP.mul_mem (hS4P w4.2) hYP, ?_⟩
    rw [← hE4def, ← hEWmap, hEW, hE0sub, map_conj_map_conj, map_map]
    have hsub : (E0W.map S4.subtype) = closure {pcG X em[0]!, pcG X em[1]!} := by
      rw [hE0W, MonoidHom.map_closure, Set.image_pair, hpcS, hpcS]
      rfl
    rw [← hsub, map_map]
    congr 1
    ext g
    simp [MulAut.conj_apply, mul_assoc]

end CFSG.ComponentClassification.RankTwoSporadic.Ru
