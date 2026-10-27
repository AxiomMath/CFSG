module

public import Certificates.Data.Kernel.Child3
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Data.CFSGNative.SporadicSchreier.Classes
public import CFSG.Certificates.Kernel.J2Enum.Group
import all CFSG.Certificates.Kernel.J2Enum.Count
import CFSG.Certificates.Kernel.J2CoverSnd.Chain
import CFSG.Certificates.Kernel.SporSch.ChainKZTot

public section

namespace CFSG.KC.J2Enum.CntPf

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover CFSG.KC.J2Enum
open CFSG.Sporadic.Th (Rep idx_of_lt Rep.compT Rep.idT)
open CFSG.Sporadic.SmallOddCore (conjClass self_mem_conjClass)

private def allProd (n : ℕ) : List (List Table) → Table → List Table
  | [], g => [g]
  | T :: Ts, g => T.flatMap fun t => allProd n Ts (compT n g t)

private theorem filterProducts_eq (n : ℕ) (f : Table → Bool) :
    ∀ (Ts : List (List Table)) (g : Table) (acc : List Table),
      filterProducts n f Ts g acc = ((allProd n Ts g).filter f).reverse ++ acc
  | [], g, acc => by
    rw [filterProducts, allProd]
    by_cases hf : f g = true <;> simp [hf]
  | T :: Ts, g, acc => by
    rw [filterProducts, allProd]
    induction T generalizing acc with
    | nil => simp
    | cons t T ih =>
      rw [List.foldl_cons, ih, filterProducts_eq n f Ts, List.flatMap_cons, List.filter_append,
        List.reverse_append, List.append_assoc]

private def trip {M : Type*} (r0 r1 r2 : ℕ) (F : ℕ → ℕ → ℕ → M) : List M :=
  (List.range r0).flatMap fun a => (List.range r1).flatMap fun b =>
    (List.range r2).flatMap fun c => [F a b c]

private theorem mem_trip {M : Type*} {r0 r1 r2 : ℕ} {F : ℕ → ℕ → ℕ → M} {x : M} :
    x ∈ trip r0 r1 r2 F ↔ ∃ a < r0, ∃ b < r1, ∃ c < r2, x = F a b c := by
  simp only [trip, List.mem_flatMap, List.mem_range, List.mem_singleton]

private theorem forall₂_flatMap {α β γ : Type*} {R : β → γ → Prop} {f : α → List β}
    {g : α → List γ} :
    ∀ {l : List α}, (∀ a ∈ l, List.Forall₂ R (f a) (g a)) →
      List.Forall₂ R (l.flatMap f) (l.flatMap g)
  | [], _ => by rw [List.flatMap_nil, List.flatMap_nil]; exact List.Forall₂.nil
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append (h a List.mem_cons_self)
      (forall₂_flatMap fun b hb => h b (List.mem_cons_of_mem a hb))

private theorem forall₂_trip {α β : Type*} {R : α → β → Prop} {r0 r1 r2 : ℕ}
    {F : ℕ → ℕ → ℕ → α} {F' : ℕ → ℕ → ℕ → β}
    (h : ∀ a < r0, ∀ b < r1, ∀ c < r2, R (F a b c) (F' a b c)) :
    List.Forall₂ R (trip r0 r1 r2 F) (trip r0 r1 r2 F') :=
  forall₂_flatMap fun a ha => forall₂_flatMap fun b hb => forall₂_flatMap fun c hc =>
    List.Forall₂.cons (h a (List.mem_range.1 ha) b (List.mem_range.1 hb) c (List.mem_range.1 hc))
      List.Forall₂.nil

private theorem nodup_flatMap_range {M : Type*} {r : ℕ} {f : ℕ → List M}
    (h1 : ∀ a < r, (f a).Nodup) (h2 : ∀ a < r, ∀ a' < r, ∀ x ∈ f a, x ∈ f a' → a = a') :
    ((List.range r).flatMap f).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun a ha => h1 a (List.mem_range.1 ha), List.pairwise_lt_range.imp_of_mem
    fun {a b} ha hb hab => ?_⟩
  rw [Function.onFun, List.disjoint_left]
  intro x hx hx'
  have := h2 a (List.mem_range.1 ha) b (List.mem_range.1 hb) x hx hx'
  omega

private theorem trip_nodup {M : Type*} {r0 r1 r2 : ℕ} {F : ℕ → ℕ → ℕ → M}
    (hF : ∀ a < r0, ∀ a' < r0, ∀ b < r1, ∀ b' < r1, ∀ c < r2, ∀ c' < r2,
      F a b c = F a' b' c' → a = a' ∧ b = b' ∧ c = c') :
    (trip r0 r1 r2 F).Nodup := by
  have m2 : ∀ a b x, x ∈ (List.range r2).flatMap (fun c => [F a b c]) ↔ ∃ c < r2, x = F a b c :=
    fun a b x => by simp [List.mem_flatMap]
  have m1 : ∀ a x, x ∈ (List.range r1).flatMap (fun b => (List.range r2).flatMap
      fun c => [F a b c]) ↔ ∃ b < r1, ∃ c < r2, x = F a b c :=
    fun a x => by simp only [List.mem_flatMap, List.mem_range, m2]
  unfold trip
  refine nodup_flatMap_range (fun a ha => nodup_flatMap_range (fun b hb => nodup_flatMap_range
    (fun c _ => List.nodup_singleton _) ?_) ?_) ?_
  · intro c hc c' hc' x hx hx'
    rw [List.mem_singleton] at hx hx'
    exact (hF a ha a ha b hb b hb c hc c' hc' (hx.symm.trans hx')).2.2
  · intro b hb b' hb' x hx hx'
    obtain ⟨c, hc, rfl⟩ := (m2 a b x).1 hx
    obtain ⟨c', hc', e⟩ := (m2 a b' _).1 hx'
    exact (hF a ha a ha b hb b' hb' c hc c' hc' e).2.1
  · intro a ha a' ha' x hx hx'
    obtain ⟨b, hb, c, hc, rfl⟩ := (m1 a x).1 hx
    obtain ⟨b', hb', c', hc', e⟩ := (m1 a' _).1 hx'
    exact (hF a ha a' ha' b hb b' hb' c hc c' hc' e).1

private theorem allProd3 {n w : ℕ} {LR TR : ℕ → ℕ} (g : Table) :
    allProd n ((List.range 3).map (CFSG.KC.J2Cover.Snd.lvTab n w LR TR)) g =
      trip (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
        compT n (compT n (compT n g (tabP n w (TR (roff n (n * w) (LR 0) + a))))
          (tabP n w (TR (roff n (n * w) (LR 1) + b)))) (tabP n w (TR (roff n (n * w) (LR 2) + c))) := by
  show allProd n [_, _, _] g = _
  simp only [allProd, CFSG.KC.J2Cover.Snd.lvTab, List.flatMap_map, trip]

private theorem acts_of_rep {n : ℕ} {T : Table} {γ : Equiv.Perm (Fin n)} (h : Rep n T γ) :
    Acts n (ap T) γ := fun p hp => by
  rw [h p hp, idx_of_lt _ hp]
  rfl

private theorem rep_of_prep {n w X : ℕ} {γ : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (h : Raw.Orb.PRep n w X γ) : Rep n (tabP n w X) γ := fun i hi => by
  rw [acts_ap hn h i hi, idx_of_lt _ hi]
  rfl

private def ordS {n : ℕ} (γ : Equiv.Perm (Fin n)) (m : ℕ) : Bool :=
  decide (γ ^ m = 1) && (divParts m).all fun e => !decide (γ ^ e = 1)

private theorem ordW_eq {n : ℕ} {W : List Table} {γ : Equiv.Perm (Fin n)} (hW : Acts n (apW W) γ)
    (m : ℕ) : ordW n W m = ordS γ m := by
  unfold ordW ordS
  simp only [powFixW_eq hW]

private theorem ordTest_eq {n : ℕ} {T : Table} {γ : Equiv.Perm (Fin n)} (h : Rep n T γ) (m : ℕ) :
    ordTest n m T = ordS γ m :=
  ordW_eq (acts_single (acts_of_rep h)) m

private theorem pow_conj_eq_one {n : ℕ} (c γ : Equiv.Perm (Fin n)) (e : ℕ) :
    (c * γ * c⁻¹) ^ e = 1 ↔ γ ^ e = 1 := by
  rw [conj_pow]
  constructor
  · intro h
    have := congrArg (fun z => c⁻¹ * z * c) h
    try simp only at this
    rwa [show c⁻¹ * (c * γ ^ e * c⁻¹) * c = γ ^ e by group, show c⁻¹ * 1 * c = 1 by group] at this
  · intro h
    rw [h]
    group

private theorem ordS_conj {n : ℕ} (c γ : Equiv.Perm (Fin n)) (m : ℕ) :
    ordS (c * γ * c⁻¹) m = ordS γ m := by
  have e : ∀ e, decide ((c * γ * c⁻¹) ^ e = 1) = decide (γ ^ e = 1) := fun e =>
    Bool.eq_iff_iff.2 (by rw [decide_eq_true_iff, decide_eq_true_iff]; exact pow_conj_eq_one c γ e)
  unfold ordS
  simp only [e]

private def PT {n : ℕ} (r s mx my : ℕ) (x y : Equiv.Perm (Fin n)) : Bool :=
  ordS (x * y) r && ordS (x * y * x ^ (mx - 1) * y ^ (my - 1)) s

private theorem apW_append (l₁ l₂ : List Table) (i : ℕ) :
    apW (l₁ ++ l₂) i = apW l₁ (apW l₂ i) := by
  unfold apW
  rw [List.foldr_append]

private theorem pairTest_eq {n r s mx my : ℕ} {T U : Table} {x y : Equiv.Perm (Fin n)}
    (hT : Rep n T x) (hU : Rep n U y) : pairTest n r s mx my T U = PT r s mx my x y := by
  have aT := acts_of_rep hT
  have aU := acts_of_rep hU
  have h1 : Acts n (apW [T, U]) (x * y) := acts_cons aT (acts_single aU)
  have h3 : Acts n (apW (List.replicate (mx - 1) T ++ List.replicate (my - 1) U))
      (x ^ (mx - 1) * y ^ (my - 1)) := fun p hp => by
    rw [apW_append]
    exact acts_comp (acts_replicate aT _) (acts_replicate aU _) p hp
  have h2 : Acts n (apW (commWord T U mx my)) (x * y * x ^ (mx - 1) * y ^ (my - 1)) := by
    have := acts_cons aT (acts_cons aU h3)
    rwa [show x * (y * (x ^ (mx - 1) * y ^ (my - 1))) = x * y * x ^ (mx - 1) * y ^ (my - 1) by
      simp only [mul_assoc]] at this
  unfold pairTest PT
  rw [ordW_eq h1, ordW_eq h2]

private theorem PT_conj {n : ℕ} (r s mx my : ℕ) (c x y : Equiv.Perm (Fin n)) :
    PT r s mx my (c * x * c⁻¹) (c * y * c⁻¹) = PT r s mx my x y := by
  unfold PT
  rw [conj_pow, conj_pow,
    show c * x * c⁻¹ * (c * y * c⁻¹) * (c * x ^ (mx - 1) * c⁻¹) * (c * y ^ (my - 1) * c⁻¹) =
      c * (x * y * x ^ (mx - 1) * y ^ (my - 1)) * c⁻¹ by simp only [mul_assoc, inv_mul_cancel_left],
    show c * x * c⁻¹ * (c * y * c⁻¹) = c * (x * y) * c⁻¹ by
      simp only [mul_assoc, inv_mul_cancel_left],
    ordS_conj, ordS_conj]

private theorem sum_blocks (CS : List ℕ) : ∀ f : ℕ → ℕ, ((List.range CS.sum).map f).sum =
    ((List.range CS.length).map fun i =>
      ((List.range (lget CS i)).map fun k => f ((CS.take i).sum + k)).sum).sum := by
  induction CS with
  | nil => intro f; simp
  | cons c CS ih =>
    intro f
    rw [List.sum_cons, List.range_add, List.map_append, List.sum_append, List.map_map,
      ih (f ∘ fun x => c + x), List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map]
    congr 1
    · show _ = ((List.range c).map fun k => f (0 + k)).sum
      simp only [Nat.zero_add]
    · congr 1
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, lget_eq, List.getD_cons_succ, List.take_succ_cons,
        List.sum_cons, Nat.add_assoc]

theorem classes_sound' {n w kS kO BP NS CH g N cap mx r s my : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {D : List (List ℤ)} {S : Array (Array ℕ)} {base : Array ℕ}
    {GP GIP CI E P L K Ss SI : ℕ → ℕ} {CS OFF : List ℕ} {gens gensInv : Array Table}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true) (hgk : g ≤ kO)
    (hg : gens.size = g ∧ gensInv.size = g ∧ ∀ l < g, gens[l]! = arrTable n (unpack n w (GP l)) ∧
      gensInv[l]! = arrTable n (unpack n w (GIP l)))
    (hgp : ∀ l < g, GP l = PS l ∧ GIP l = PSI l) (hkO : kO ≤ g)
    (hoff : offOK CS OFF N = true)
    (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K Ss SI N cap j = true)
    (hrep : ∀ i < CS.length, canonK n w (mask w) (n * w) (E (lget OFF i)) = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 (E (lget OFF i)) = true ∧
      ordTest n mx (arrTable n (unpack n w (E (lget OFF i)))) = true)
    (hN : (filterProducts n (ordTest n mx) (chainTables n S base) (idT n) []).length = N) :
    classOK n gens gensInv (filterProducts n (ordTest n mx) (chainTables n S base) (idT n) []) cap =
        true ∧
      classTotal n gens gensInv (filterProducts n (ordTest n mx) (chainTables n S base) (idT n) [])
          (filterProducts n (ordTest n my) (chainTables n S base) (idT n) []) cap r s mx my =
        ((List.range CS.length).map fun i => lget CS i *
          (filterProducts n (ordTest n my) (chainTables n S base) (idT n) []).countP
            (pairTest n r s mx my (arrTable n (unpack n w (E (lget OFF i)))))).sum := by
  classical
  have hgO : g = kO := le_antisymm hgk hkO
  subst hgO
  obtain ⟨-, -, hsift, -⟩ := GrpPf.group3 hb hh hl hNS hs
  obtain ⟨hT, hsurj, hinj⟩ := GrpPf.enum3 hb hh hl hNS hs
  have hn : n < 16777216 := by have := hb.2.2.1; omega
  have hn32 : n < 2 ^ 32 := by omega
  have hkS : g ≤ kS := hb.2.2.2.1 ▸ (Raw.Orb.rawHeadOK_of hb hh).1
  obtain ⟨G, hG⟩ : ∃ G, G = Raw.Orb.Gen n S g := ⟨_, rfl⟩
  rw [← hG] at hT hsurj hsift
  obtain ⟨gg, hggd⟩ : ∃ gg : ℕ → Equiv.Perm (Fin n),
      gg = fun l => CFSG.Monster.B.Co2.permOfArr n S[l]! := ⟨_, rfl⟩
  have hgg : ∀ l < g, Raw.Orb.PRep n w (GP l) (gg l) ∧ Raw.Orb.PRep n w (GIP l) (gg l)⁻¹ ∧
      gg l ∈ G := by
    intro l hl
    obtain ⟨e1, e2⟩ := hgp l hl
    obtain ⟨p1, p2⟩ := Raw.Orb.prep_PS hb hp (j := l) (by omega)
    rw [e1, e2, hggd, hG]
    exact ⟨p1, p2, Subgroup.subset_closure ⟨⟨l, hl⟩, rfl⟩⟩
  have hK : CFSG.KS.SporSch.ClsSpec.genK gens gg = G := by
    rw [CFSG.KS.SporSch.ClsSpec.genK, hG, Raw.Orb.Gen]
    congr 1
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, by omega⟩, by rw [hggd]⟩
    · rintro ⟨⟨l, hl⟩, rfl⟩
      exact ⟨l, by omega, by rw [hggd]⟩
  have hgR : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ G := by
    intro l hl
    rw [hg.1] at hl
    obtain ⟨p1, p2, p3⟩ := hgg l hl
    rw [(hg.2.2 l hl).1, (hg.2.2 l hl).2]
    exact ⟨rep_of_prep hn32 p1, rep_of_prep hn32 p2, p3⟩
  set τ : ℕ → ℕ → Equiv.Perm (Fin n) := fun j k => CFSG.Certificates.ChainArrays.levT n S base j k
    with hτ
  obtain ⟨P3, hP3⟩ : ∃ P3 : List (Equiv.Perm (Fin n)),
      P3 = trip (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c => τ 0 a * τ 1 b * τ 2 c :=
    ⟨_, rfl⟩
  have hP3nd : P3.Nodup := by
    rw [hP3]
    exact trip_nodup hinj
  have hP3mem : ∀ x, x ∈ P3 ↔ x ∈ G := by
    intro x
    rw [hP3, mem_trip]
    constructor
    · rintro ⟨a, ha, b, hb', c, hc, rfl⟩
      exact mul_mem (mul_mem (hT 0 (by norm_num) a ha).1 (hT 1 (by norm_num) b hb').1)
        (hT 2 (by norm_num) c hc).1
    · exact hsurj x
  obtain ⟨hct, -⟩ := CFSG.KC.J2Cover.Snd.chainTables_eq_lvTab hb hp hl
  have hA : List.Forall₂ (Rep n) (allProd n (chainTables n S base) (idT n)) P3 := by
    rw [hct, allProd3, hP3]
    refine forall₂_trip fun a ha b hb' c hc => ?_
    have := ((Rep.idT hn32).compT (rep_of_prep hn32 (hT 0 (by norm_num) a ha).2)).compT
      (rep_of_prep hn32 (hT 1 (by norm_num) b hb').2) |>.compT
      (rep_of_prep hn32 (hT 2 (by norm_num) c hc).2)
    rwa [one_mul] at this
  have hX : ∀ m, List.Forall₂ (Rep n) (filterProducts n (ordTest n m) (chainTables n S base)
      (idT n) []) (P3.filter fun x => ordS x m).reverse := by
    intro m
    rw [filterProducts_eq, List.append_nil, List.forall₂_reverse_iff]
    exact List.rel_filter (fun T x hTx => show ordTest n m T = true ↔ ordS x m = true by rw [ordTest_eq hTx]) hA
  have hXnd : ∀ m, ((P3.filter fun x => ordS x m).reverse).Nodup := fun m =>
    List.nodup_reverse.2 (hP3nd.filter _)
  have hXmem : ∀ m x, x ∈ (P3.filter fun x => ordS x m).reverse ↔ x ∈ G ∧ ordS x m = true := by
    intro m x
    rw [List.mem_reverse, List.mem_filter, hP3mem]
  have hXcl : ∀ m, ∀ c ∈ G, ∀ x ∈ (P3.filter fun x => ordS x m).reverse,
      c * x * c⁻¹ ∈ (P3.filter fun x => ordS x m).reverse := by
    intro m c hc x hx
    rw [hXmem] at hx ⊢
    exact ⟨mul_mem (mul_mem hc hx.1) (inv_mem hc), by rw [ordS_conj]; exact hx.2⟩
  set xs := (P3.filter fun x => ordS x mx).reverse with hxs
  set ys := (P3.filter fun x => ordS x my).reverse with hys
  obtain ⟨hoffv, hsum⟩ := offOK_facts hoff
  have F := fun j (hj : j < N) => repK_facts (h j hj)
  obtain ⟨ε, hεd⟩ : ∃ ε : ℕ → Equiv.Perm (Fin n),
      ε = fun j => Classical.epsilon (Raw.Orb.PRep n w (E j)) := ⟨_, rfl⟩
  have hε : ∀ j γ, Raw.Orb.PRep n w (E j) γ → ε j = γ := fun j γ hγ => by
    rw [hεd]
    exact prep_unique (Classical.epsilon_spec (p := Raw.Orb.PRep n w (E j)) ⟨γ, hγ⟩) hγ
  have hρ : ∀ i < CS.length, Raw.Orb.PRep n w (E (lget OFF i)) (ε (lget OFF i)) ∧
      ε (lget OFF i) ∈ G ∧ ordS (ε (lget OFF i)) mx = true := by
    intro i hi
    obtain ⟨hc, hsf, ho⟩ := hrep i hi
    obtain ⟨γ, hγG, hγ⟩ := (hsift _ hc).1 hsf
    rw [hε _ _ hγ]
    exact ⟨hγ, hγG, by rw [← ordTest_eq (rep_of_prep hn32 hγ)]; exact ho⟩
  have hcls : ∀ i < CS.length, ∀ k < lget CS i, Raw.Orb.PRep n w (E (lget OFF i + k))
      (ε (lget OFF i + k)) ∧ ε (lget OFF i + k) ∈
        conjClass G (ε (lget OFF i)) := by
    intro i hi k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [Nat.add_zero]
        exact ⟨(hρ i hi).1, self_mem_conjClass _ _⟩
      · obtain ⟨hjN, hci⟩ := ci_eq hoff h hi hk
        have hkj : lget OFF i + k - lget OFF (CI (lget OFF i + k)) = k := by rw [hci]; omega
        obtain ⟨hP, hL, hcj⟩ := (F _ hjN).tree (by rw [hkj]; omega)
        rw [hkj] at hP
        rw [hci] at hcj
        obtain ⟨r1, r2⟩ := ih _ hP (by omega)
        obtain ⟨g1, g2, g3⟩ := hgg _ hL
        have hr : Raw.Orb.PRep n w (E (lget OFF i + k))
            (gg (L (lget OFF i + k)) * ε (lget OFF i + P (lget OFF i + k)) *
              (gg (L (lget OFF i + k)))⁻¹) := by
          rw [← hcj]
          exact Raw.Orb.prep_pcomp hn32 (Raw.Orb.prep_pcomp hn32 g1 r1) g2
        rw [hε _ _ hr]
        exact ⟨hr, CFSG.KS.SporSch.ClsSpec.conj_mem_conjClass g3 r2⟩
  have hεN : ∀ j < N, CI j < CS.length ∧ lget OFF (CI j) + (j - lget OFF (CI j)) = j ∧
      j - lget OFF (CI j) < lget CS (CI j) := fun j hj =>
    ⟨(F j hj).ci_lt, by have := (F j hj).off_le; omega, (F j hj).loc_lt⟩
  have hεG : ∀ j < N, Raw.Orb.PRep n w (E j) (ε j) ∧
      ε j ∈ conjClass G (ε (lget OFF (CI j))) := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := hεN j hj
    have := hcls _ h1 _ h3
    rwa [h2] at this
  have hεinj : ∀ a < N, ∀ b < N, ε a = ε b → a = b := by
    intro a ha b hb e
    apply E_inj h ha hb
    obtain ⟨-, -, hA0, -⟩ := PF.canon_facts (F a ha).canon
    obtain ⟨-, hw, hB0, -⟩ := PF.canon_facts (F b hb).canon
    refine PF.eq_of_fields (PF.w_pos hw) hA0 hB0 fun i hi => ?_
    rw [(hεG a ha).1 ⟨i, hi⟩, (hεG b hb).1 ⟨i, hi⟩, e]
  have hεxs : ∀ j < N, ε j ∈ xs := by
    intro j hj
    obtain ⟨c, hc, e⟩ := (hεG j hj).2
    obtain ⟨-, h2, h3⟩ := hρ _ (hεN j hj).1
    rw [hxs, hXmem, e, ordS_conj]
    exact ⟨mul_mem (mul_mem hc h2) (inv_mem hc), h3⟩
  set εs := (List.range N).map ε with hεs
  have hεsnd : εs.Nodup := List.Nodup.map_on (fun a ha b hb e =>
    hεinj a (List.mem_range.1 ha) b (List.mem_range.1 hb) e) List.nodup_range
  have hxslen : xs.length = N := by rw [← (hX mx).length_eq, hN]
  have hperm : εs.Perm xs := by
    refine (hεsnd.subperm fun y hy => ?_).perm_of_length_le (by rw [hxslen, hεs]; simp)
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    exact hεxs j (List.mem_range.1 hj)
  have hclose : ∀ i < CS.length, ∀ c ∈ G, ∀ z ∈ (↑((Finset.range (lget CS i)).image
      fun k => ε (lget OFF i + k)) : Set (Equiv.Perm (Fin n))),
      c * z * c⁻¹ ∈ (↑((Finset.range (lget CS i)).image
        fun k => ε (lget OFF i + k)) : Set (Equiv.Perm (Fin n))) := by
    intro i hi c hc
    rw [← hK] at hc
    refine CFSG.KS.SporSch.ClsSpec.conj_closed ?_ c hc
    rintro _ ⟨l, hl, rfl⟩ z hz
    rw [hg.1] at hl
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hz ⊢
    obtain ⟨k, hk, rfl⟩ := hz
    obtain ⟨hjN, hci⟩ := ci_eq hoff h hi hk
    obtain ⟨hK1, hK2, -⟩ := (F _ hjN).close l hl
    rw [hci] at hK1 hK2
    refine ⟨_, hK1, ?_⟩
    obtain ⟨g1, g2, -⟩ := hgg l hl
    have hr := Raw.Orb.prep_pcomp hn32 (Raw.Orb.prep_pcomp hn32 g1 (hcls i hi k hk).1) g2
    rw [← cj, ← hK2] at hr
    exact hε _ _ hr
  have hcap : ∀ y ∈ xs, (conjClass (CFSG.KS.SporSch.ClsSpec.genK gens gg) y).ncard ≤
      cap := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (hperm.symm.subset hy)
    have hj' := List.mem_range.1 hj
    obtain ⟨h1, h2, h3⟩ := hεN j hj'
    rw [hK]
    calc (conjClass G (ε j)).ncard
        ≤ (↑((Finset.range (lget CS (CI j))).image
            fun k => ε (lget OFF (CI j) + k)) : Set (Equiv.Perm (Fin n))).ncard := by
          refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
          rintro _ ⟨c, hc, rfl⟩
          refine hclose _ h1 c hc _ ?_
          simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
          exact ⟨_, h3, by rw [h2]⟩
      _ ≤ lget CS (CI j) := by
          rw [Set.ncard_coe_finset]
          exact Finset.card_image_le.trans (Finset.card_range _).le
      _ ≤ cap := (F j hj').size_le
  have hgR' : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ :=
    fun l hl => ⟨(hgR l hl).1, (hgR l hl).2.1⟩
  have hok := CFSG.KS.SporSch.ClsSpec.classOK_of_closed hgR' (hX mx) hcap (hXnd mx)
    (fun y hy z hz => by
      rw [hK] at hz
      obtain ⟨c, hc, rfl⟩ := hz
      exact hXcl mx c hc y hy)
  refine ⟨hok, ?_⟩
  obtain ⟨pp, hpp⟩ : ∃ pp : Equiv.Perm (Fin n) → ℕ, pp = fun x => ys.countP (PT r s mx my x) :=
    ⟨_, rfl⟩
  have hpRep : ∀ T x, Rep n T x → (filterProducts n (ordTest n my) (chainTables n S base) (idT n)
      []).countP (pairTest n r s mx my T) = pp x := by
    intro T x hTx
    rw [hpp]
    exact CFSG.Sporadic.Schreier.countP_eq_of_forall₂ (hX my) fun U y hU _ => by
      rw [pairTest_eq hTx hU]
  have hpc : ∀ c ∈ G, ∀ x, pp (c * x * c⁻¹) = pp x := by
    intro c hc x
    rw [hpp]
    have e1 : ∀ y, PT r s mx my (c * x * c⁻¹) y = PT r s mx my x (c⁻¹ * y * c) := fun y => by
      rw [← PT_conj r s mx my c x (c⁻¹ * y * c),
        show c * (c⁻¹ * y * c) * c⁻¹ = y by group]
    have hpm : (ys.map fun y => c⁻¹ * y * c).Perm ys := by
      refine (List.perm_ext_iff_of_nodup ((hXnd my).map fun a b e => ?_) (hXnd my)).2 fun z => ?_
      · have := congrArg (fun t => c * t * c⁻¹) e
        try simp only at this
        rwa [show c * (c⁻¹ * a * c) * c⁻¹ = a by group,
          show c * (c⁻¹ * b * c) * c⁻¹ = b by group] at this
      · constructor
        · intro hz
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
          have := hXcl my c⁻¹ (inv_mem hc) y hy
          rwa [inv_inv] at this
        · intro hz
          exact List.mem_map.2 ⟨c * z * c⁻¹, hXcl my c hc z hz, by group⟩
    simp only
    rw [List.countP_congr (p := fun y => PT r s mx my (c * x * c⁻¹) y)
      (q := fun y => PT r s mx my x (c⁻¹ * y * c)) fun y _ => by rw [e1]]
    show ys.countP (PT r s mx my x ∘ fun y => c⁻¹ * y * c) = _
    rw [← List.countP_map, hpm.countP_eq]
  have hcl := hok
  unfold classOK at hcl
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hcl
  obtain ⟨⟨⟨hidx, htree⟩, hdist⟩, hcsum⟩ := hcl
  have key := CFSG.Sporadic.Schreier.sum_eq_classSum G pp hpc xs (fun c hc x hx => hXcl mx c hc x hx)
    hgR _ (fun T x hTx _ => hpRep T x hTx)
    (classes n gens gensInv (filterProducts n (ordTest n mx) (chainTables n S base) (idT n) []) cap)
    (fun c hc => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
      have hi' := hidx i hi
      have hlen : i < xs.length := by rw [← (hX mx).length_eq]; exact hi'
      refine ⟨xs[i], List.getElem_mem hlen, ?_⟩
      have harr : (filterProducts n (ordTest n mx) (chainTables n S base) (idT n) []).toArray[i]! =
          (filterProducts n (ordTest n mx) (chainTables n S base) (idT n) [])[i] := by
        rw [getElem!_pos _ i (by simpa using hi')]
        simp
      rw [harr]
      exact (hX mx).get hi' hlen)
    htree hdist (by rw [hcsum, (hX mx).length_eq])
  unfold classTotal
  rw [← key, ← (hperm.map pp).sum_eq, hεs, List.map_map, ← hsum, sum_blocks]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.1 hi
  rw [← hoffv i hi', hpRep _ _ (rep_of_prep hn32 (hρ i hi').1)]
  have hconst : ∀ k ∈ List.range (lget CS i), (pp ∘ ε) (lget OFF i + k) = pp (ε (lget OFF i)) := by
    intro k hk
    obtain ⟨c, hc, e⟩ := (hcls i hi' k (List.mem_range.1 hk)).2
    rw [Function.comp_apply, e, hpc c hc]
  rw [List.map_congr_left hconst, List.map_const', List.sum_replicate, smul_eq_mul,
    List.length_range]

end CFSG.KC.J2Enum.CntPf

end
