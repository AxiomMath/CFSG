module

public import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionDefs

public section

namespace CFSG.OddStandard

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native

variable {n : ℕ}

@[expose] noncomputable def classClosurePerms (n : ℕ) (gens gensInv : Array Table)
    (r : Equiv.Perm (Fin n)) (cap : ℕ) : List (Equiv.Perm (Fin n)) :=
  (conjClosure n gens gensInv (toTable r) cap).1.toList.map (tablePerm n)

theorem length_classClosurePerms (gens gensInv : Array Table) (r : Equiv.Perm (Fin n)) (cap : ℕ) :
    (classClosurePerms n gens gensInv r cap).length =
      (conjClosure n gens gensInv (toTable r) cap).1.size := by
  simp [classClosurePerms]

theorem classes_of_repsOK (hn : n < 2 ^ 32) (H : Subgroup (Equiv.Perm (Fin n)))
    {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ H)
    {XT : List Table} {XG : List (Equiv.Perm (Fin n))} (hX : List.Forall₂ (Rep n) XT XG)
    (hclosed : ∀ c ∈ H, ∀ x ∈ XG, c * x * c⁻¹ ∈ XG)
    (reps : List (Equiv.Perm (Fin n))) (hreps : ∀ r ∈ reps, r ∈ XG) (cap : ℕ)
    (hok : repsOK n gens gensInv XT (reps.map toTable) cap = true) :
    (∀ u ∈ XG, ∃ r ∈ reps, ∃ d ∈ H, u = d * r * d⁻¹) ∧
    (∀ r ∈ reps, (∀ y ∈ classClosurePerms n gens gensInv r cap, y ∈ conjClass H r) ∧
      (classClosurePerms n gens gensInv r cap).Nodup) ∧
    reps.Pairwise fun r s => List.Disjoint (classClosurePerms n gens gensInv r cap)
      (classClosurePerms n gens gensInv s cap) := by
  simp only [repsOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨htree, hdist⟩, hsum⟩ := hok
  set cl := (reps.map toTable).map fun r => (r, conjClosure n gens gensInv r cap) with hcl
  have hentries : ∀ r ∈ reps, ∀ T ∈ (conjClosure n gens gensInv (toTable r) cap).1.toList,
      ∃ d ∈ H, Rep n T (d * r * d⁻¹) := by
    intro r hr T hT
    have htr := htree (toTable r, conjClosure n gens gensInv (toTable r) cap) (by
      simp only [hcl, List.map_map, List.mem_map, Function.comp]
      exact ⟨r, hr, rfl⟩)
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
    rw [Array.length_toList] at hk
    obtain ⟨d, hd, hrepd⟩ := conjTreeOK_spec H hg (rep_toTable hn r) htr k hk
    refine ⟨d, hd, ?_⟩
    rw [Array.getElem_toList]
    rwa [getElem!_pos (conjClosure n gens gensInv (toTable r) cap).1 k hk] at hrepd
  set U := cl.flatMap fun c => c.2.1.toList with hU
  have hUeq : U.map (tablePerm n) = reps.flatMap (classClosurePerms n gens gensInv · cap) := by
    simp only [hU, hcl, classClosurePerms, List.map_map, List.flatMap_map, List.map_flatMap]
    rfl
  have hUrep : ∀ T ∈ U, ∃ r ∈ reps, ∃ d ∈ H, Rep n T (d * r * d⁻¹) := by
    intro T hT
    obtain ⟨c, hc, hT⟩ := List.mem_flatMap.1 hT
    simp only [hcl, List.map_map, List.mem_map, Function.comp] at hc
    obtain ⟨r, hr, rfl⟩ := hc
    obtain ⟨d, hd, hrep⟩ := hentries r hr T hT
    exact ⟨r, hr, d, hd, hrep⟩
  have hUforall : List.Forall₂ (Rep n) U (U.map (tablePerm n)) := by
    rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun T hT => ?_
    obtain ⟨r, -, d, -, hrep⟩ := hUrep T hT
    rw [tablePerm_eq hrep]
    exact hrep
  have hnodup : (U.map (tablePerm n)).Nodup := nodup_of_keysDistinct hUforall hdist
  have hsub : U.map (tablePerm n) ⊆ XG := by
    intro y hy
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hy
    obtain ⟨r, hr, d, hd, hrep⟩ := hUrep T hT
    rw [tablePerm_eq hrep]
    exact hclosed d hd r (hreps r hr)
  have hlen : XG.length ≤ (U.map (tablePerm n)).length := by
    rw [List.length_map, List.length_flatMap, ← hX.length_eq, ← hsum]
    simp [hcl]
  have hperm := (hnodup.subperm hsub).perm_of_length_le hlen
  rw [hUeq] at hperm hnodup
  have hflat := List.nodup_flatMap.1 hnodup
  refine ⟨fun u hu => ?_, fun r hr => ⟨fun y hy => ?_, hflat.1 r hr⟩, hflat.2⟩
  · have hmem : u ∈ reps.flatMap (classClosurePerms n gens gensInv · cap) := hperm.symm.subset hu
    obtain ⟨r, hr, hur⟩ := List.mem_flatMap.1 hmem
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hur
    obtain ⟨d, hd, hrep⟩ := hentries r hr T hT
    exact ⟨r, hr, d, hd, tablePerm_eq hrep⟩
  · obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hy
    obtain ⟨d, hd, hrep⟩ := hentries r hr T hT
    exact ⟨d, hd, tablePerm_eq hrep⟩


theorem conjClass_eq_of_classClosure {H : Subgroup (Equiv.Perm (Fin n))} {r : Equiv.Perm (Fin n)}
    {L : List (Equiv.Perm (Fin n))} (hsub : ∀ y ∈ L, y ∈ conjClass H r) (hnd : L.Nodup)
    (hcard : (conjClass H r).ncard = L.length) : conjClass H r = {y | y ∈ L} := by
  symm
  refine Set.eq_of_subset_of_ncard_le (fun y hy => hsub y hy) ?_ (conjClass_finite H r)
  have : {y | y ∈ L} = ((L.toFinset : Finset (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))) := by
    ext y
    simp
  rw [hcard, this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem length_le_ncard_conjClass {H : Subgroup (Equiv.Perm (Fin n))} {r : Equiv.Perm (Fin n)}
    {L : List (Equiv.Perm (Fin n))} (hsub : ∀ y ∈ L, y ∈ conjClass H r) (hnd : L.Nodup) :
    L.length ≤ (conjClass H r).ncard := by
  have : {y | y ∈ L} = ((L.toFinset : Finset (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))) := by
    ext y
    simp
  have h := Set.ncard_le_ncard (s := {y | y ∈ L}) (fun y hy => hsub y hy) (conjClass_finite H r)
  rwa [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd] at h

@[expose] def orderIn (n : ℕ) (ps : List ℕ) (T : Table) : Bool := ps.any fun p => ordTest n p T

@[expose] def orderInTables (Q : RawSchreierDatum n) (ps : List ℕ) : List Table :=
  filterProducts n (orderIn n ps) (levelTables Q) (idT n) []

theorem forall₂_orderInTables (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) {ps : List ℕ}
    (hps : ∀ p ∈ ps, 0 < p) :
    List.Forall₂ (Rep n) (orderInTables Q ps)
      ((enumeration Q).filter fun h => decide (∃ p ∈ ps, orderOf h = p)).reverse := by
  have h := filterProducts_spec (f := orderIn n ps)
    (P := fun h : Equiv.Perm (Fin n) => ∃ p ∈ ps, orderOf h = p)
    (fun T g hT => by
      simp only [orderIn, List.any_eq_true]
      exact exists_congr fun p => and_congr_right fun hp => ordTest_iff perm_faithful hT (hps p hp))
    (forall₂_levelTables hn Q) (Rep.idT hn) (acc := []) (accG := []) List.Forall₂.nil
  simp only [one_mul, List.map_id', List.append_nil] at h
  exact h

@[expose] def generatorTables (cg : List (Equiv.Perm (Fin n))) : Array Table :=
  (cg.map toTable).toArray

@[expose] def generatorTablesInv (cg : List (Equiv.Perm (Fin n))) : Array Table :=
  (cg.map fun g => toTable g⁻¹).toArray

theorem generatorTables_spec (hn : n < 2 ^ 32) {H : Subgroup (Equiv.Perm (Fin n))}
    {cg : List (Equiv.Perm (Fin n))} (hH : ∀ g ∈ cg, g ∈ H) :
    ∀ l < (generatorTables cg).size, Rep n (generatorTables cg)[l]! (cg.getD l 1) ∧
      Rep n (generatorTablesInv cg)[l]! (cg.getD l 1)⁻¹ ∧ cg.getD l 1 ∈ H := by
  intro l hl
  have hl' : l < cg.length := by simpa [generatorTables] using hl
  have hget : cg.getD l 1 = cg[l] := List.getD_eq_getElem _ _ hl'
  have h1 : (generatorTables cg)[l]! = toTable cg[l] := by
    rw [getElem!_pos _ l hl]
    simp [generatorTables]
  have h2 : (generatorTablesInv cg)[l]! = toTable (cg[l])⁻¹ := by
    rw [getElem!_pos _ l (by simpa [generatorTablesInv] using hl')]
    simp [generatorTablesInv]
  rw [hget, h1, h2]
  exact ⟨rep_toTable hn _, rep_toTable hn _, hH _ (List.getElem_mem hl')⟩

theorem commT_iff {X Y : Table} {xg yg : Equiv.Perm (Fin n)} (hX : Rep n X xg) (hY : Rep n Y yg) :
    commT n X Y = true ↔ xg * yg = yg * xg := by
  refine ⟨eq_of_commT hX hY, fun h => ?_⟩
  have h1 := Rep.compT hX hY
  have h2 := Rep.compT hY hX
  rw [h] at h1
  exact tblEq_iff.2 fun i hi => (h1 i hi).trans (h2 i hi).symm

@[expose] def commCountT (n : ℕ) (Ks : List Table) (x : Table) : ℕ :=
  Ks.countP fun y => commT n x y

theorem card_centralizerIn_eq_commCountT (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (x : Equiv.Perm (Fin n)) :
    Nat.card (centralizerIn Q.originalSubgroup x) = commCountT n (allTables Q) (toTable x) := by
  have hA := forall₂_allTables hn Q
  have h1 : commCountT n (allTables Q) (toTable x) =
      (enumeration Q).countP fun g => decide (x * g = g * x) := by
    rw [← List.countP_reverse]
    refine countP_eq_of_forall₂ hA fun a b hab _ => ?_
    rw [commT_iff (rep_toTable hn x) hab, decide_eq_true_iff]
  have h2 := card_subtype_eq_countP Q.originalSubgroup (enumeration Q) (enumeration_nodup Q hQ)
    (mem_enumeration_iff Q hQ) fun g => x * g = g * x
  rw [h1, ← h2]
  refine Nat.card_congr
    ⟨fun g => ⟨⟨g, (mem_centralizerIn.1 g.2).1⟩, (mem_centralizerIn.1 g.2).2.symm⟩,
      fun g => ⟨g.1, mem_centralizerIn.2 ⟨g.1.2, g.2.symm⟩⟩, fun g => rfl, fun g => rfl⟩


theorem oddCoreRowsValid_of_checks (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {cg : List (Equiv.Perm (Fin n))}
    (hcg : Q.originalSubgroup = Subgroup.closure {g | g ∈ cg}) {ps : List ℕ}
    (hps : ∀ p ∈ ps, p.Prime ∧ p ≠ 2)
    (hps' : ∀ q, q.Prime → q ≠ 2 → q ∣ Nat.card Q.originalSubgroup → q ∈ ps)
    (rows : List (OddCoreRow n)) (cap : ℕ) (hrp : ∀ r ∈ rows, r.prime.Prime ∧ r.prime ≠ 2)
    (hmem : ∀ r ∈ rows, r.representative ∈ Q.originalSubgroup)
    (hord : ∀ r ∈ rows, ordTest n r.prime (toTable r.representative) = true)
    (hok : repsOK n (generatorTables cg) (generatorTablesInv cg) (orderInTables Q ps)
      ((rows.map (·.representative)).map toTable) cap = true)
    (hsz : repSizes n (generatorTables cg) (generatorTablesInv cg)
      ((rows.map (·.representative)).map toTable) cap = rows.map (·.classSize))
    (hcent : (rows.all fun r => r.classSize *
      commCountT n (allTables Q) (toTable r.representative) == Q.orderCertificate) = true)
    (hwit : ∀ r ∈ rows, ∃ (h : Equiv.Perm (Fin n)) (m : ℕ), r.witness = .conjugator h m ∧
      h ∈ Q.originalSubgroup ∧ 0 < m ∧
      ordTest n m (toTable (r.representative * (h * r.representative * h⁻¹))) = true ∧ Even m) :
    OddCoreRowsValid Q.originalSubgroup rows := by
  set K := Q.originalSubgroup with hK
  have hKcard : Nat.card K = Q.orderCertificate := (Q.orderCertificate_eq_card hQ).symm
  have hcgK : ∀ g ∈ cg, g ∈ K := fun g hg => hcg ▸ Subgroup.subset_closure hg
  have hg := generatorTables_spec hn hcgK
  have hX := forall₂_orderInTables hn Q fun p hp => (hps p hp).1.pos
  set XG := ((enumeration Q).filter fun h => decide (∃ p ∈ ps, orderOf h = p)).reverse with hXG
  have hXGmem : ∀ u, u ∈ XG ↔ u ∈ K ∧ ∃ p ∈ ps, orderOf u = p := by
    intro u
    simp only [XG, List.mem_reverse, List.mem_filter, mem_enumeration_iff Q hQ, decide_eq_true_eq]
    exact Iff.rfl
  have hclosed : ∀ c ∈ K, ∀ x ∈ XG, c * x * c⁻¹ ∈ XG := by
    intro c hc x hx
    rw [hXGmem] at hx ⊢
    obtain ⟨hxK, p, hp, hxp⟩ := hx
    refine ⟨K.mul_mem (K.mul_mem hc hxK) (K.inv_mem hc), p, hp, ?_⟩
    rw [← hxp]
    exact (MulEquiv.orderOf_eq (MulAut.conj c) x)
  have hordeq : ∀ r ∈ rows, orderOf r.representative = r.prime := fun r hr =>
    (ordTest_iff perm_faithful (rep_toTable hn _) (hrp r hr).1.pos).1 (hord r hr)
  have hreps : ∀ x ∈ rows.map (·.representative), x ∈ XG := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    rw [hXGmem]
    refine ⟨hmem r hr, r.prime, hps' _ (hrp r hr).1 (hrp r hr).2 ?_, hordeq r hr⟩
    rw [← hordeq r hr]
    have := orderOf_dvd_natCard (⟨r.representative, hmem r hr⟩ : K)
    rwa [← Subgroup.orderOf_coe] at this
  obtain ⟨hcov, hcls, hdisj⟩ := classes_of_repsOK hn K hg hX hclosed _ hreps cap hok
  have hsizes : ∀ r ∈ rows, (conjClosure n (generatorTables cg) (generatorTablesInv cg)
      (toTable r.representative) cap).1.size = r.classSize := by
    intro r hr
    simp only [repSizes, List.map_map] at hsz
    exact (List.map_inj_left.1 hsz) r hr
  have hncard : ∀ r ∈ rows, (conjClass K r.representative).ncard = r.classSize := by
    intro r hr
    have horb := ncard_conjClass_mul_card K r.representative
    have hpos : 0 < Nat.card (centralizerIn K r.representative) := Nat.card_pos
    rw [card_centralizerIn_eq_commCountT hn Q hQ] at horb hpos
    have hc := List.all_eq_true.1 hcent r hr
    rw [beq_iff_eq] at hc
    rw [hKcard, ← hc] at horb
    exact Nat.eq_of_mul_eq_mul_right hpos horb
  have hclassEq : ∀ r ∈ rows, conjClass K r.representative = {y | y ∈ classClosurePerms n
      (generatorTables cg) (generatorTablesInv cg) r.representative cap} := by
    intro r hr
    obtain ⟨hsub, hnd⟩ := hcls r.representative (List.mem_map_of_mem hr)
    refine conjClass_eq_of_classClosure hsub hnd ?_
    rw [length_classClosurePerms, hsizes r hr, hncard r hr]
  refine ⟨fun r hr => ⟨(hrp r hr).1, (hrp r hr).2, hmem r hr, hordeq r hr, hncard r hr, ?_⟩,
    ?_, ?_⟩
  · obtain ⟨h, m, hw, hhK, hm0, hordm, hev⟩ := hwit r hr
    rw [hw]
    exact ⟨hhK, (ordTest_iff perm_faithful (rep_toTable hn _) hm0).1 hordm, hev⟩
  · rw [List.pairwise_map] at hdisj
    refine hdisj.imp_of_mem fun {r s} hr hs hrs => ?_
    rw [hclassEq r hr, hclassEq s hs, Set.disjoint_left]
    exact fun y hy hy' => hrs hy hy'
  · intro x hx hodd
    obtain ⟨p, hp, hp2, hxp⟩ := hodd
    have hxXG : x ∈ XG := by
      rw [hXGmem]
      refine ⟨hx, p, hps' p hp hp2 ?_, hxp⟩
      rw [← hxp]
      have := orderOf_dvd_natCard (⟨x, hx⟩ : K)
      rwa [← Subgroup.orderOf_coe] at this
    obtain ⟨y, hy, d, hd, hxy⟩ := hcov x hxXG
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
    exact ⟨r, hr, d, hd, hxy⟩


structure WordRowSpec where
  prime : ℕ
  repWord : List ℤ
  classSize : ℕ
  conjWord : List ℤ
  productOrder : ℕ

@[expose] def WordRowSpec.row (cg : List (Equiv.Perm (Fin n))) (sp : WordRowSpec) : OddCoreRow n :=
  ⟨sp.prime, evalCodes cg sp.repWord, sp.classSize,
    .conjugator (evalCodes cg sp.conjWord) sp.productOrder⟩

@[expose] def oddRowsCheck (n : ℕ) (Q : RawSchreierDatum n) (cg : List (Equiv.Perm (Fin n)))
    (ps : List ℕ) (specs : List WordRowSpec) (cap : ℕ) : Bool :=
  let reps := specs.map fun sp => evalCodes cg sp.repWord
  let gT := generatorTables cg
  let gI := generatorTablesInv cg
  repsOK n gT gI (orderInTables Q ps) (reps.map toTable) cap &&
    (repSizes n gT gI (reps.map toTable) cap == specs.map (·.classSize)) &&
    specs.all (fun sp => sp.classSize *
      commCountT n (allTables Q) (toTable (evalCodes cg sp.repWord)) == Q.orderCertificate) &&
    specs.all (fun sp => ordTest n sp.prime (toTable (evalCodes cg sp.repWord))) &&
    specs.all fun sp => ordTest n sp.productOrder (toTable (evalCodes cg sp.repWord *
      (evalCodes cg sp.conjWord * evalCodes cg sp.repWord * (evalCodes cg sp.conjWord)⁻¹)))

theorem oddCoreRowsValid_of_check (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {cg : List (Equiv.Perm (Fin n))}
    (hcg : Q.originalSubgroup = Subgroup.closure {g | g ∈ cg}) {ps : List ℕ}
    (hps : ∀ p ∈ ps, p.Prime ∧ p ≠ 2)
    (hps' : ∀ q, q.Prime → q ≠ 2 → q ∣ Nat.card Q.originalSubgroup → q ∈ ps)
    (specs : List WordRowSpec) (cap : ℕ)
    (hspecs : ∀ sp ∈ specs, sp.prime.Prime ∧ sp.prime ≠ 2 ∧ 0 < sp.productOrder ∧
      Even sp.productOrder)
    (h : oddRowsCheck n Q cg ps specs cap = true) :
    OddCoreRowsValid Q.originalSubgroup (specs.map (·.row cg)) := by
  have hcgK : ∀ g ∈ cg, g ∈ Q.originalSubgroup := fun g hg => hcg ▸ Subgroup.subset_closure hg
  simp only [oddRowsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hok, hsz⟩, hcent⟩, hord⟩, hprod⟩ := h
  have hrows : (specs.map (·.row cg)).map (·.representative) =
      specs.map fun sp => evalCodes cg sp.repWord := by
    simp [List.map_map, Function.comp_def, WordRowSpec.row]
  refine oddCoreRowsValid_of_checks hn Q hQ hcg hps hps' (specs.map (·.row cg)) cap ?_ ?_ ?_ ?_
    ?_ ?_ ?_
  · intro r hr
    obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 hr
    exact ⟨(hspecs sp hsp).1, (hspecs sp hsp).2.1⟩
  · intro r hr
    obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 hr
    exact evalCodes_mem _ hcgK _
  · intro r hr
    obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 hr
    exact hord sp hsp
  · rw [hrows]
    exact hok
  · rw [hrows]
    simpa [List.map_map, Function.comp_def, WordRowSpec.row] using hsz
  · rw [List.all_eq_true]
    intro r hr
    obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 hr
    exact beq_iff_eq.2 (hcent sp hsp)
  · intro r hr
    obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 hr
    exact ⟨_, _, rfl, evalCodes_mem _ hcgK _, (hspecs sp hsp).2.2.1, hprod sp hsp,
      (hspecs sp hsp).2.2.2⟩

theorem oddCoreRowsValid_of_check_card (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {cg : List (Equiv.Perm (Fin n))}
    (hcg : Q.originalSubgroup = Subgroup.closure {g | g ∈ cg}) {ps : List ℕ} (h2 : 2 ∉ ps)
    {N : ℕ} (hN : Nat.card Q.originalSubgroup = N) (hpf : N.primeFactors = insert 2 ps.toFinset)
    (specs : List WordRowSpec) (cap : ℕ)
    (hspecs : ∀ sp ∈ specs, sp.prime.Prime ∧ sp.prime ≠ 2 ∧ 0 < sp.productOrder ∧
      Even sp.productOrder)
    (h : oddRowsCheck n Q cg ps specs cap = true) :
    OddCoreRowsValid Q.originalSubgroup (specs.map (·.row cg)) := by
  refine oddCoreRowsValid_of_check hn Q hQ hcg (fun p hp => ⟨?_, fun hp2 => h2 (hp2 ▸ hp)⟩) ?_
    specs cap hspecs h
  · have : p ∈ N.primeFactors := by
      rw [hpf]
      exact Finset.mem_insert_of_mem (List.mem_toFinset.2 hp)
    exact Nat.prime_of_mem_primeFactors this
  · intro q hq hq2 hd
    have hq' : q ∈ N.primeFactors := by
      refine Nat.mem_primeFactors.2 ⟨hq, hN ▸ hd, ?_⟩
      rintro rfl
      rw [Nat.primeFactors_zero] at hpf
      exact Finset.insert_ne_empty _ _ hpf.symm
    rw [hpf] at hq'
    simpa [hq2] using hq'

theorem innerRecordsValid_of_checks (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {a b : Equiv.Perm (Fin n)} (ha : a ∈ Q.originalSubgroup)
    (hb : b ∈ Q.originalSubgroup) (recs : List (InnerClassRecord n)) (cap : ℕ)
    (hok : repsOK n (pairTables a b) (pairTables a⁻¹ b⁻¹) (cosetOrderTables Q 1 2)
      ((recs.map (·.representative)).map toTable) cap = true)
    (hsz : repSizes n (pairTables a b) (pairTables a⁻¹ b⁻¹)
      ((recs.map (·.representative)).map toTable) cap = recs.map (·.classSize))
    (hrecs : ∀ r ∈ recs, r.representative ∈ Q.originalSubgroup ∧ orderOf r.representative = 2 ∧
      ∃ Qc : RawSchreierDatum n, ValidSchreier Qc ∧
        Qc.originalSubgroup = Subgroup.closure {g | g ∈ r.centralizerGenerators} ∧
        Qc.originalSubgroup ≤ centralizerIn Q.originalSubgroup r.representative ∧
        Qc.orderCertificate = r.centralizerOrder ∧
        r.classSize * r.centralizerOrder = Nat.card Q.originalSubgroup ∧
        OddCoreRowsValid Qc.originalSubgroup r.oddCore) :
    InnerClassRecordsValid Q.originalSubgroup recs := by
  set G := Q.originalSubgroup with hG
  have hg := pairTables_spec hn ha hb
  have hX := forall₂_cosetOrderTables hn Q 1 (m := 2) (by norm_num)
  simp only [one_mul, List.map_id'] at hX
  set XG := ((enumeration Q).filter fun h => decide (orderOf h = 2)).reverse with hXG
  have hXGmem : ∀ u, u ∈ XG ↔ u ∈ G ∧ orderOf u = 2 := by
    intro u
    simp only [XG, List.mem_reverse, List.mem_filter, mem_enumeration_iff Q hQ, decide_eq_true_eq]
    exact Iff.rfl
  have hclosed : ∀ c ∈ G, ∀ x ∈ XG, c * x * c⁻¹ ∈ XG := by
    intro c hc x hx
    rw [hXGmem] at hx ⊢
    exact ⟨G.mul_mem (G.mul_mem hc hx.1) (G.inv_mem hc),
      (MulEquiv.orderOf_eq (MulAut.conj c) x).trans hx.2⟩
  have hreps : ∀ x ∈ recs.map (·.representative), x ∈ XG := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact (hXGmem _).2 ⟨(hrecs r hr).1, (hrecs r hr).2.1⟩
  obtain ⟨hcov, hcls, hdisj⟩ := classes_of_repsOK hn G hg hX hclosed _ hreps cap hok
  have hsizes : ∀ r ∈ recs,
      (conjClosure n (pairTables a b) (pairTables a⁻¹ b⁻¹) (toTable r.representative) cap).1.size =
        r.classSize := by
    intro r hr
    simp only [repSizes, List.map_map] at hsz
    exact (List.map_inj_left.1 hsz) r hr
  have hdata : ∀ r ∈ recs,
      centralizerIn G r.representative = Subgroup.closure {g | g ∈ r.centralizerGenerators} ∧
      Nat.card (centralizerIn G r.representative) = r.centralizerOrder ∧
      (conjClass G r.representative).ncard = r.classSize ∧
      OddCoreRowsValid (centralizerIn G r.representative) r.oddCore := by
    intro r hr
    obtain ⟨hrG, hr2, Qc, hQc, hQcg, hQcle, hQco, hprod, hrows⟩ := hrecs r hr
    obtain ⟨hsub, hnd⟩ := hcls r.representative (List.mem_map_of_mem hr)
    have hcard : Nat.card Qc.originalSubgroup = r.centralizerOrder := by
      rw [← hQco, Qc.orderCertificate_eq_card hQc]
    have hle : r.classSize ≤ (conjClass G r.representative).ncard := by
      have := length_le_ncard_conjClass hsub hnd
      rwa [length_classClosurePerms, hsizes r hr] at this
    have hcenteq : centralizerIn G r.representative = Qc.originalSubgroup :=
      centralizerIn_eq_of_le G r.representative hQcle hle (by rw [hcard, hprod])
    refine ⟨hcenteq.trans hQcg, hcenteq ▸ hcard, ?_, hcenteq ▸ hrows⟩
    have horb := ncard_conjClass_mul_card G r.representative
    rw [hcenteq, hcard, ← hprod] at horb
    have hpos : 0 < r.centralizerOrder := hcard ▸ Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos horb
  have hclassEq : ∀ r ∈ recs, conjClass G r.representative = {y | y ∈ classClosurePerms n
      (pairTables a b) (pairTables a⁻¹ b⁻¹) r.representative cap} := by
    intro r hr
    obtain ⟨hsub, hnd⟩ := hcls r.representative (List.mem_map_of_mem hr)
    refine conjClass_eq_of_classClosure hsub hnd ?_
    rw [length_classClosurePerms, hsizes r hr, (hdata r hr).2.2.1]
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · obtain ⟨hcenteq, hcard, hncard, hrows⟩ := hdata r hr
    obtain ⟨hrG, hr2, -⟩ := hrecs r hr
    refine ⟨hrG, hr2, hncard, hcard, fun g hg => ?_, hcenteq.symm, hrows⟩
    rw [hcenteq]
    exact Subgroup.subset_closure hg
  · rw [List.pairwise_map] at hdisj
    refine hdisj.imp_of_mem fun {r s} hr hs hrs => ?_
    rw [hclassEq r hr, hclassEq s hs, Set.disjoint_left]
    exact fun y hy hy' => hrs hy hy'
  · intro u hu hu2
    have hmem : u ∈ XG := (hXGmem u).2 ⟨hu, hu2⟩
    obtain ⟨y, hy, d, hd, hxy⟩ := hcov u hmem
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
    exact ⟨r, hr, d, hd, hxy⟩

end CFSG.OddStandard
