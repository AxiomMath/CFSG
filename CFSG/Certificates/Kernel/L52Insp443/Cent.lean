module

public import CFSG.Certificates.Kernel.L52Insp443.Span
public import Certificates.Data.CFSGNative.Insp443.L52Tests

public section

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.Literature.GL52 CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

theorem kG_one : mcode ((1 : G) : Mat) = idK := by
  rw [Units.val_one, mcode_one]

theorem kG_mul (g h : G) : mcode ((g * h : G) : Mat) = mmulK (mcode (g : Mat)) (mcode (h : Mat)) := by
  rw [Units.val_mul, mmulK_mcode]

theorem kG_inj : Function.Injective fun g : G => mcode (g : Mat) := fun g h e =>
  Units.ext (mcode_inj e)

theorem hn31 : 31 < 2 ^ 32 := by norm_num

theorem mem_of_cent {bs cs : List ℕ} {Ts : List Table} (hcs : tabsK cs Ts = true)
    (hbs : ∀ b ∈ bs, unitK b = true) (hnd : (spanK cs).Nodup)
    (hc : ∀ s ∈ spanK cs, ∀ b ∈ bs, mmulK s b = mmulK b s)
    (hcard : solCntK (diagK bs) = (spanK cs).length) {h : G}
    (hh : ∀ b ∈ bs, h * gD b = gD b * h) : mcode (h : Mat) ∈ spanK cs := by
  obtain ⟨hT, hu⟩ := forall₂_of_tabsK hcs
  refine mem_of_comm_card (fun g : G => mcode (g : Mat)) kG_mul kG_inj gD
    (fun b hb => mcode_gD (hbs b hb)) (fun s hs => ?_) hnd hc ?_ hh
  · obtain ⟨x, hx, -⟩ := exists_of_mem_spanK (fun g : G => mcode (g : Mat)) kG_one kG_mul gD hn31
      glPerm (fun c hc => mcode_gD (hu c hc)) hT s hs
    exact ⟨x, hx⟩
  · rw [card_cent_gD hbs, hcard]

theorem centTestS_false {bs cs : List ℕ} {Us Ts : List Table} (hbs : tabsK bs Us = true)
    (hcs : tabsK cs Ts = true) (hnd : (spanK cs).Nodup)
    (hc : ∀ s ∈ spanK cs, ∀ b ∈ bs, mmulK s b = mmulK b s)
    (hcard : solCntK (diagK bs) = (spanK cs).length) (h : G) {T : Table}
    (hT : Rep 31 T (glPerm h)) : centTestS 31 Us (spanTabs 31 Ts) T = false := by
  obtain ⟨hU, hbu⟩ := forall₂_of_tabsK hbs
  obtain ⟨hTs, hcu⟩ := forall₂_of_tabsK hcs
  rw [← Bool.not_eq_true]
  intro hcent
  unfold centTestS at hcent
  rw [Bool.and_eq_true, Bool.not_eq_true'] at hcent
  have hcomm := comm_of_commAllT hT hU hcent.1
  have hh : ∀ b ∈ bs, h * gD b = gD b * h := fun b hb => by
    apply glPerm_injective
    rw [map_mul, map_mul]
    exact hcomm _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
  have hmem := mem_of_cent hcs hbu hnd hc hcard hh
  have hin := inSp_of_mem_spanK (fun g : G => mcode (g : Mat)) kG_one kG_mul kG_inj gD hn31
    glPerm (fun c hc => mcode_gD (hcu c hc)) hTs hmem hT
  rw [hin] at hcent
  exact absurd hcent.2 (by decide)

theorem tabsK_append {b : List ℕ} {B : List Table} (hb : tabsK b B = true) :
    ∀ {a : List ℕ} {A : List Table}, tabsK a A = true → tabsK (a ++ b) (A ++ B) = true
  | [], [], _ => hb
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | c :: a, T :: A, h => by
    rw [tabsK_cons, andB_true] at h
    rw [List.cons_append, List.cons_append, tabsK_cons, andB_true]
    exact ⟨h.1, tabsK_append hb h.2⟩

theorem length_of_tabsK : ∀ {a : List ℕ} {A : List Table}, tabsK a A = true → a.length = A.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | c :: a, T :: A, h => by
    rw [tabsK_cons, andB_true] at h
    rw [List.length_cons, List.length_cons, length_of_tabsK h.2]

theorem centTestS_false_of {bs cs S : List ℕ} {Us Ts : List Table} (hbs : tabsK bs Us = true)
    (hcs : tabsK cs Ts = true) (hS : listBeq (spanK cs) S = true) (hnd : nodupK S = true)
    (hc : allK (fun s => allK (commK s) bs) S = true) (hcard : solCntK (diagK bs) = 2 ^ cs.length)
    (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    centTestS 31 Us (spanTabs 31 Ts) T = false := by
  rw [listBeq_iff] at hS
  subst hS
  refine centTestS_false hbs hcs ((nodupK_iff _).mp hnd) (fun s hs b hb => ?_)
    (by rw [hcard, length_spanK]) h hT
  exact (commK_iff s b).mp ((allK_iff _ _).mp ((allK_iff _ _).mp hc s hs) b hb)

theorem c2TestS_false {bs : List ℕ} {Us : List Table} (hbs : tabsK bs Us = true) {e : ℕ}
    (hcard : solCntK (diagK bs) = e) (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    c2TestS 31 Us e T = false := by
  obtain ⟨hU, hbu⟩ := forall₂_of_tabsK hbs
  rw [← Bool.not_eq_true]
  intro hc2
  unfold c2TestS at hc2
  rw [Bool.and_eq_true, Bool.not_eq_true'] at hc2
  have hcomm := comm_of_commAllT hT hU hc2.1
  let C : Subgroup G := Subgroup.centralizer (gD '' {b | b ∈ bs})
  have hmemC : ∀ g : G, g ∈ C ↔ ∀ b ∈ bs, g * gD b = gD b * g := fun g => by
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hg b hb
      exact (hg _ ⟨b, hb, rfl⟩).symm
    · rintro hg _ ⟨b, hb, rfl⟩
      exact (hg b hb).symm
  have hcardC : Nat.card C = e := by
    rw [← hcard, ← card_cent_gD hbu]
    exact Nat.card_congr (Equiv.subtypeEquivRight hmemC)
  have hhC : h ∈ C := (hmemC h).mpr fun b hb => by
    apply glPerm_injective
    rw [map_mul, map_mul]
    exact hcomm _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
  have hpow : h ^ e = 1 := by
    have := pow_card_eq_one' (G := C) (x := ⟨h, hhC⟩)
    rw [hcardC] at this
    exact congrArg Subtype.val this
  have hp := (CFSG.Sporadic.Schreier.powFixW_iff CFSG.Sporadic.Schreier.perm_faithful
    (List.Forall₂.cons hT List.Forall₂.nil) e).mpr (by rw [List.prod_singleton, ← map_pow, hpow,
      map_one])
  rw [hp] at hc2
  exact absurd hc2.2 (by decide)

theorem conjCommK_cons (c p q : ℕ) (ps qs : List ℕ) :
    conjCommK c (p :: ps) (q :: qs) = CFSG.KC.Ord.andB (commK c (mmulK (mmulK p c) q)) (conjCommK c ps qs) :=
  rfl

theorem conjCommK_true : ∀ {c : ℕ} {ps qs : List ℕ}, ps.length = qs.length →
    (∀ j < ps.length, commK c (mmulK (mmulK (ps.getD j 0) c) (qs.getD j 0)) = true) →
    conjCommK c ps qs = true
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, h, _ => absurd h (by simp)
  | _, _ :: _, [], h, _ => absurd h (by simp)
  | c, p :: ps, q :: qs, hl, h => by
    rw [conjCommK_cons, andB_true]
    refine ⟨h 0 (by simp), conjCommK_true (by simpa using hl) fun j hj => ?_⟩
    have := h (j + 1) (by simp; omega)
    simpa using this

theorem sTestS_false {bs zc wc L ps qs : List ℕ} {Us Zs Ws : List Table}
    {cs : List (Table × Table)} (hbs : tabsK bs Us = true) (hz : tabsK zc Zs = true)
    (hw : tabsK wc Ws = true) (hnd : L.Nodup) (hcard : solCntK (diagK bs) = L.length)
    (hL : ∀ c ∈ L, unitK c = true ∧ (∀ b ∈ bs, mmulK c b = mmulK b c) ∧
      (conjCommK c ps qs = false ∨ c ∈ spanK zc ∨ c ∈ spanK wc))
    (x : G) (hl : ps.length = qs.length)
    (hpq : ∀ j < ps.length, ps.getD j 0 = mcode ((x ^ j : G) : Mat) ∧
      qs.getD j 0 = mcode ((x⁻¹ ^ j : G) : Mat) ∧
      ∃ ab ∈ cs, Rep 31 ab.1 (glPerm (x ^ j)) ∧ Rep 31 ab.2 (glPerm (x⁻¹ ^ j)))
    (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    sTestS 31 Us (spanTabs 31 Zs) (spanTabs 31 Ws) cs T = false := by
  obtain ⟨hU, hbu⟩ := forall₂_of_tabsK hbs
  obtain ⟨hZ, hzu⟩ := forall₂_of_tabsK hz
  obtain ⟨hW, hwu⟩ := forall₂_of_tabsK hw
  rw [← Bool.not_eq_true]
  intro hs
  unfold sTestS at hs
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
  obtain ⟨⟨⟨hcomm, hzT⟩, hwT⟩, hall⟩ := hs
  have hcomm' := comm_of_commAllT hT hU hcomm
  have hh : ∀ b ∈ bs, h * gD b = gD b * h := fun b hb => by
    apply glPerm_injective
    rw [map_mul, map_mul]
    exact hcomm' _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
  have hmem : mcode (h : Mat) ∈ L := by
    refine mem_of_comm_card (fun g : G => mcode (g : Mat)) kG_mul kG_inj gD
      (fun b hb => mcode_gD (hbu b hb)) (fun s hs => ⟨gD s, mcode_gD (hL s hs).1⟩) hnd
      (fun s hs => (hL s hs).2.1) ?_ hh
    rw [card_cent_gD hbu, hcard]
  rcases (hL _ hmem).2.2 with hc | hc | hc
  · rw [← Bool.not_eq_true] at hc
    apply hc
    refine conjCommK_true hl fun j hj => ?_
    obtain ⟨hp, hq, ab, hab, h1, h2⟩ := hpq j hj
    have hc2 := (CFSG.SectionRank.QTK.Insp443.PermKit.commT2_iff hT
      (Rep.compT (Rep.compT h1 hT) h2)).mp ((List.all_eq_true.mp hall) ab hab)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul] at hc2
    have e := congrArg (fun g : G => mcode (g : Mat)) (glPerm_injective hc2)
    simp only [kG_mul] at e
    rw [commK_iff, hp, hq]
    exact e
  · rw [inSp_of_mem_spanK (fun g : G => mcode (g : Mat)) kG_one kG_mul kG_inj gD hn31 glPerm
      (fun c hc => mcode_gD (hzu c hc)) hZ hc hT] at hzT
    exact absurd hzT (by decide)
  · rw [inSp_of_mem_spanK (fun g : G => mcode (g : Mat)) kG_one kG_mul kG_inj gD hn31 glPerm
      (fun c hc => mcode_gD (hwu c hc)) hW hc hT] at hwT
    exact absurd hwT (by decide)

theorem pow_codes {ps qs : List ℕ} {m : ℕ} {x : G} (h0 : ps.getD 0 0 = idK)
    (hstep : ∀ j < m, mmulK (ps.getD j 0) (ps.getD 1 0) = ps.getD (j + 1) 0)
    (hx : mcode (x : Mat) = ps.getD 1 0) (hinv : ∀ j ≤ m, mmulK (ps.getD j 0) (qs.getD j 0) = idK)
    (hqu : ∀ j ≤ m, unitK (qs.getD j 0) = true) :
    ∀ j ≤ m, ps.getD j 0 = mcode ((x ^ j : G) : Mat) ∧ qs.getD j 0 = mcode ((x⁻¹ ^ j : G) : Mat) := by
  have hp : ∀ j ≤ m, ps.getD j 0 = mcode ((x ^ j : G) : Mat) := by
    intro j hj
    induction j with
    | zero => rw [pow_zero, kG_one, h0]
    | succ j ih =>
      rw [← hstep j (by omega), ih (by omega), ← hx, ← kG_mul, ← pow_succ]
  intro j hj
  refine ⟨hp j hj, ?_⟩
  have e : x ^ j * gD (qs.getD j 0) = 1 := by
    apply kG_inj
    change mcode (((x ^ j * gD (qs.getD j 0)) : G) : Mat) = mcode (((1 : G)) : Mat)
    rw [kG_mul, kG_one, mcode_gD (hqu j hj), ← hp j hj, hinv j hj]
  rw [← mcode_gD (hqu j hj), eq_inv_of_mul_eq_one_right e, inv_pow]

theorem and2 {a b : Bool} (h : CFSG.KC.Ord.andB a b = true) : a = true ∧ b = true := andB_true.mp h

end CFSG.KC.L52I

end
