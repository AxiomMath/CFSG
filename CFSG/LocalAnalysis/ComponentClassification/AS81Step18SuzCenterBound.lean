module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18SuzCenterTests
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs
import CFSG.Perm.OrbitTree
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.ComponentClassification.AS81.SuzCenter

open Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Monster.B.Co2.Native

local notation "Perm1782" => Equiv.Perm (Fin 1782)

@[expose] def genSub (m : ℕ) (a : ℕ → Perm1782) : Subgroup Perm1782 :=
  closure {g | ∃ k < m, a k = g}

@[expose] def fixSub (B : List ℕ) : Subgroup Perm1782 where
  carrier := {g | ∀ x : Fin 1782, (x : ℕ) ∈ B → g x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {g h} hg hh x hx => by
    rw [Equiv.Perm.mul_apply, hh x hx, hg x hx]
  inv_mem' := fun {g} hg x hx => by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hg x hx).symm

theorem fixSub_nil : fixSub [] = ⊤ := by
  ext g
  simp [fixSub]

variable {gs : Array Tab} {a : ℕ → Perm1782}

theorem tabRep_wordC (ha : ∀ k < gs.size, TabRep gs[k]! (a k)) :
    ∀ w : List ℕ, (∀ j ∈ w, j < gs.size) → TabRep (wordC gs w) ((w.map a).prod)
  | [], _ => by simpa [wordC] using (TabRep.idTab (n := 1782))
  | j :: w, hw => by
    have h1 : wordC gs (j :: w) = comp 1782 gs[j]! (wordC gs w) := by
      simp only [wordC, List.foldr_cons]
    rw [h1, List.map_cons, List.prod_cons]
    exact (ha j (hw j List.mem_cons_self)).comp
      (tabRep_wordC ha w fun i hi => hw i (List.mem_cons_of_mem _ hi))

theorem prod_mem_genSub (w : List ℕ) (hw : ∀ j ∈ w, j < gs.size) :
    (w.map a).prod ∈ genSub gs.size a :=
  (genSub gs.size a).list_prod_mem fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact subset_closure ⟨j, hw j hj, rfl⟩

theorem mem_fixSub_of_fixesAll {t : Tab} {g : Perm1782} (ht : TabRep t g) {B : List ℕ}
    (h : fixesAll t B = true) : g ∈ fixSub B := by
  intro x hx
  have e := List.all_eq_true.1 h _ hx
  rw [beq_iff_eq, ht.apply x] at e
  exact Fin.ext e

theorem levelGens_rep (ha : ∀ k < gs.size, TabRep gs[k]! (a k)) {L : CentreLevel}
    (hw : L.ws.all (·.all (· < gs.size)) = true) :
    ∀ k < (levelGens gs L).size, ∃ g ∈ genSub gs.size a, TabRep (levelGens gs L)[k]! g := by
  intro k hk
  have hk' : k < L.ws.length := by simpa [levelGens] using hk
  have e : (levelGens gs L)[k]! = wordC gs L.ws[k] := by
    rw [getElem!_pos _ k hk]
    simp [levelGens]
  have hwk : ∀ j ∈ L.ws[k], j < gs.size := fun j hj => by
    have := List.all_eq_true.1 hw _ (List.getElem_mem hk')
    simpa using List.all_eq_true.1 this j hj
  exact ⟨_, prod_mem_genSub _ hwk, e ▸ tabRep_wordC ha _ hwk⟩

theorem tree_reach {hs : Array Tab} {L : CentreLevel} {K : Subgroup Perm1782}
    (hgen : ∀ k < hs.size, ∃ g ∈ K, TabRep hs[k]! g) (ht : treeOK hs L = true) :
    ∃ hb : L.b < 1782, ∀ j < L.pts.length, ∃ g ∈ K, (g ⟨L.b, hb⟩ : ℕ) = L.pts[j]! := by
  simp only [treeOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, List.mem_range] at ht
  obtain ⟨⟨⟨⟨⟨hpar, hgenl⟩, hhead⟩, -⟩, hlt⟩, htree⟩ := ht
  have hne : L.pts ≠ [] := by
    intro e
    rw [e] at hhead
    simp at hhead
  have h0 : L.pts[0]! = L.b := by
    obtain ⟨x, xs, e⟩ := List.exists_cons_of_ne_nil hne
    rw [e] at hhead ⊢
    simp at hhead
    simp [hhead]
  have hb : L.b < 1782 := by
    have := hlt (L.pts[0]!) (by
      rw [getElem!_pos _ 0 (List.length_pos_of_ne_nil hne)]
      exact List.getElem_mem _)
    rwa [h0] at this
  refine ⟨hb, fun j => ?_⟩
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact ⟨1, K.one_mem, by rw [h0]; rfl⟩
    · rcases htree j hj with h | ⟨⟨hp, hk⟩, he⟩
      · omega
      obtain ⟨g', hg', e'⟩ := ih _ hp (by omega)
      obtain ⟨g, hg, hrep⟩ := hgen _ hk
      refine ⟨g * g', K.mul_mem hg hg', ?_⟩
      rw [Equiv.Perm.mul_apply, ← hrep.apply, e', he]

theorem ncard_pts {l : List ℕ} (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < 1782) :
    {x : Fin 1782 | (x : ℕ) ∈ l}.ncard = l.length := by
  have e : (Fin.val '' {x : Fin 1782 | (x : ℕ) ∈ l}) = {x | x ∈ l} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hlt y hy⟩, hy, rfl⟩
  rw [← Set.ncard_image_of_injective _ Fin.val_injective, e]
  rw [show {x | x ∈ l} = (l.toFinset : Set ℕ) by ext; simp, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

theorem card_mul_le_level {G : Subgroup Perm1782} {B : List ℕ} {hs : Array Tab} {L : CentreLevel}
    (hgen : ∀ k < hs.size, ∃ g ∈ G ⊓ fixSub B, TabRep hs[k]! g) (ht : treeOK hs L = true) :
    L.pts.length * Nat.card ↥(G ⊓ fixSub (B ++ [L.b])) ≤ Nat.card ↥(G ⊓ fixSub B) := by
  obtain ⟨hb, hreach⟩ := tree_reach hgen ht
  have ht' := ht
  simp only [treeOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at ht'
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hnd⟩, hlt⟩, -⟩ := ht'
  set H := G ⊓ fixSub B
  set b : Fin 1782 := ⟨L.b, hb⟩
  have horb : {x : Fin 1782 | (x : ℕ) ∈ L.pts} ⊆ MulAction.orbit H b := by
    intro x hx
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hx
    obtain ⟨g, hg, eg⟩ := hreach j hj
    refine ⟨⟨g, hg⟩, Fin.ext ?_⟩
    change (g ⟨L.b, hb⟩ : ℕ) = (x : ℕ)
    rw [eg, getElem!_pos _ j hj, e]
  have hcard : L.pts.length ≤ (MulAction.orbit H b).ncard := by
    rw [← ncard_pts hnd fun x hx => by simpa using hlt x hx]
    exact Set.ncard_le_ncard horb (Set.toFinite _)
  have hstab : Nat.card (MulAction.stabilizer H b) = Nat.card ↥(G ⊓ fixSub (B ++ [L.b])) := by
    refine Nat.card_congr
      { toFun := fun h => ⟨h.1.1, h.1.2.1, fun x hx => ?_⟩
        invFun := fun g => ⟨⟨g.1, g.2.1, fun x hx => g.2.2 x (List.mem_append_left _ hx)⟩, ?_⟩
        left_inv := fun h => rfl
        right_inv := fun g => rfl }
    · rcases List.mem_append.1 hx with hx | hx
      · exact h.1.2.2 x hx
      · have e : x = b := Fin.ext (by simpa using hx)
        rw [e]
        have := h.2
        rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def] at this
        exact this
    · rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def]
      exact g.2.2 b (List.mem_append_right _ (by simp [b]))
  have hmul := (MulAction.stabilizer H b).card_mul_index
  rw [MulAction.index_stabilizer, hstab] at hmul
  rw [← hmul, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ hcard

theorem card_mul_le_of_levelsOK (ha : ∀ k < gs.size, TabRep gs[k]! (a k)) :
    ∀ (Ls : List CentreLevel) (B : List ℕ), levelsOK gs B Ls = true →
      (Ls.map (·.pts.length)).prod * Nat.card ↥(genSub gs.size a ⊓ fixSub (B ++ Ls.map (·.b))) ≤
        Nat.card ↥(genSub gs.size a ⊓ fixSub B)
  | [], B, _ => by simp
  | L :: Ls, B, h => by
    simp only [levelsOK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hw, hfix⟩, ht⟩, hrest⟩ := h
    have hgen : ∀ k < (levelGens gs L).size,
        ∃ g ∈ genSub gs.size a ⊓ fixSub B, TabRep (levelGens gs L)[k]! g := by
      intro k hk
      obtain ⟨g, hg, hrep⟩ := levelGens_rep ha hw k hk
      refine ⟨g, ⟨hg, mem_fixSub_of_fixesAll hrep ?_⟩, hrep⟩
      rw [getElem!_pos _ k hk]
      exact Array.all_eq_true_iff_forall_mem.1 hfix _ (Array.getElem_mem hk)
    have h1 := card_mul_le_level hgen ht
    have h2 := card_mul_le_of_levelsOK ha Ls (B ++ [L.b]) hrest
    rw [List.append_assoc, List.singleton_append] at h2
    simp only [List.map_cons, List.prod_cons]
    calc L.pts.length * (Ls.map (·.pts.length)).prod *
          Nat.card ↥(genSub gs.size a ⊓ fixSub (B ++ L.b :: Ls.map (·.b)))
        = L.pts.length * ((Ls.map (·.pts.length)).prod *
          Nat.card ↥(genSub gs.size a ⊓ fixSub (B ++ L.b :: Ls.map (·.b)))) := by ring
      _ ≤ L.pts.length * Nat.card ↥(genSub gs.size a ⊓ fixSub (B ++ [L.b])) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ _ := h1

theorem centreOK_spec (ha : ∀ k < gs.size, TabRep gs[k]! (a k)) {zw : List ℕ}
    {Ls : List CentreLevel} {N : ℕ} (hN : Nat.card ↥(genSub gs.size a) ≤ N)
    (h : centreOK gs zw Ls N = true) :
    Nat.card ↥(genSub gs.size a) = N ∧ Nat.card ↥(centerIn (genSub gs.size a)) = 2 := by
  set X := genSub gs.size a
  rcases Ls with _ | ⟨L0, _ | ⟨L1, Ls'⟩⟩
  · simp [centreOK] at h
  · simp [centreOK] at h
  simp only [centreOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlev, hprod⟩, hclosed⟩, hbase⟩, hfix2⟩, hzw⟩, hzc⟩, hzmove⟩ := h
  have hle := card_mul_le_of_levelsOK ha (L0 :: L1 :: Ls') [] hlev
  rw [hprod, List.nil_append, fixSub_nil, inf_top_eq] at hle
  set K := X ⊓ fixSub ((L0 :: L1 :: Ls').map (·.b))
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hcard : Nat.card X = N := by
    apply le_antisymm hN
    calc N = N * 1 := (Nat.mul_one N).symm
      _ ≤ N * Nat.card K := Nat.mul_le_mul_left _ hKpos
      _ ≤ Nat.card X := hle
  have hK1 : Nat.card K = 1 := by
    have hNpos : 0 < N := by
      rw [← hcard]
      exact Nat.card_pos
    have : N * Nat.card K ≤ N * 1 := by
      rw [Nat.mul_one, ← hcard]
      rw [hcard] at hle
      rwa [hcard]
    exact le_antisymm (Nat.le_of_mul_le_mul_left this hNpos) hKpos
  have hKbot : K = ⊥ := (Subgroup.card_le_one_iff_eq_bot K).1 hK1.le
  refine ⟨hcard, ?_⟩
  have hlev' := hlev
  simp only [levelsOK, Bool.and_eq_true] at hlev'
  obtain ⟨⟨⟨hw0, -⟩, ht0⟩, ⟨⟨⟨hw1, hfix1⟩, -⟩, -⟩⟩ := hlev'
  obtain ⟨hb, hreach⟩ := tree_reach (K := X) (levelGens_rep ha hw0) ht0
  set b : Fin 1782 := ⟨L0.b, hb⟩
  set O : Set (Fin 1782) := {x | (x : ℕ) ∈ L0.pts}
  have hbO : b ∈ O := by simpa [O, b] using hbase L0 List.mem_cons_self
  have hgenO : ∀ s ∈ {g | ∃ k < gs.size, a k = g}, ∀ x ∈ O, s • x ∈ O := by
    rintro _ ⟨k, hk, rfl⟩ x hx
    have e := hclosed _ hx
    rw [allBelow_eq_true] at e
    have e2 := e k hk
    rw [List.contains_iff_mem, (ha k hk).apply x] at e2
    exact e2
  have hXO : ∀ g ∈ X, g b ∈ O := fun g hg =>
    CFSG.Perm.smul_mem_of_finite_of_mem_closure (Set.toFinite O) hgenO hg hbO
  have hOX : ∀ x ∈ O, ∃ s ∈ X, s b = x := by
    intro x hx
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem (show (x : ℕ) ∈ L0.pts from hx)
    obtain ⟨s, hs, es⟩ := hreach j hj
    refine ⟨s, hs, Fin.ext ?_⟩
    rw [es, getElem!_pos _ j hj, e]
  have hfixb : ∀ d ∈ centerIn X, d b = b → d = 1 := by
    intro d hd hdb
    have hdO : ∀ x ∈ O, d x = x := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := hOX x hx
      have hc : s * d = d * s := (mem_centralizer_iff.1 hd.2 s hs)
      rw [← Equiv.Perm.mul_apply, ← hc, Equiv.Perm.mul_apply, hdb]
    have hdK : d ∈ K := ⟨hd.1, fun x hx => by
      obtain ⟨L, hL, hLx⟩ := List.mem_map.1 hx
      have hm : (x : ℕ) ∈ L0.pts := by
        rw [← hLx]
        simpa using hbase L hL
      exact hdO x hm⟩
    rw [hKbot] at hdK
    exact (Subgroup.mem_bot.1 hdK)
  have hgen1 := levelGens_rep ha hw1
  have hfix1' : ∀ k < (levelGens gs L1).size, ∀ g, TabRep (levelGens gs L1)[k]! g → g b = b := by
    intro k hk g hg
    have e := Array.all_eq_true_iff_forall_mem.1 hfix1 _ (Array.getElem_mem hk)
    rw [← getElem!_pos _ k hk] at e
    exact mem_fixSub_of_fixesAll hg e b (by simp [b])
  set P : Set (Fin 1782) := {x | (x : ℕ) ∈ L0.pts.filter fun x =>
    (levelGens gs L1).all fun h => h[x]! == x}
  have hP : P.ncard = 2 := by
    have ht0' := ht0
    simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht0'
    obtain ⟨⟨⟨-, hnd⟩, hlt⟩, -⟩ := ht0'
    rw [← hfix2]
    exact ncard_pts (hnd.filter _) fun x hx => by
      simpa using hlt x (List.mem_of_mem_filter hx)
  have hmaps : ∀ c ∈ centerIn X, c b ∈ P := by
    intro c hc
    refine List.mem_filter.2 ⟨hXO c hc.1, Array.all_eq_true_iff_forall_mem.2 fun t ht => ?_⟩
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 ht
    obtain ⟨g, hg, hrep⟩ := hgen1 k hk
    rw [← getElem!_pos _ k hk, beq_iff_eq, hrep.apply (c b)]
    have hcg : g * c = c * g := mem_centralizer_iff.1 hc.2 g hg
    rw [← Equiv.Perm.mul_apply, hcg, Equiv.Perm.mul_apply, hfix1' k hk g hrep]
  have hle2 : Nat.card ↥(centerIn X) ≤ 2 := by
    rw [← hP, ← Nat.card_coe_set_eq]
    refine Nat.card_le_card_of_injective (fun c => (⟨c.1 b, hmaps c.1 c.2⟩ : P)) ?_
    intro c c' e
    have e' : c.1 b = c'.1 b := congrArg Subtype.val e
    have hd : c.1⁻¹ * c'.1 ∈ centerIn X := (centerIn X).mul_mem ((centerIn X).inv_mem c.2) c'.2
    have := hfixb _ hd (by rw [Equiv.Perm.mul_apply, ← e']; simp)
    exact Subtype.ext (by rw [inv_mul_eq_one] at this; exact this)
  have hzw' : ∀ j ∈ zw, j < gs.size := fun j hj => by simpa using hzw j hj
  have hzrep := tabRep_wordC ha zw hzw'
  set z := (zw.map a).prod
  have hzX : z ∈ X := prod_mem_genSub zw hzw'
  have hzc' : ∀ k < gs.size, z * a k = a k * z := by
    intro k hk
    have e := allBelow_eq_true.1 hzc k hk
    exact ((hzrep.comp (ha k hk)).beq_iff ((ha k hk).comp hzrep)).1 e
  have hzZ : z ∈ centerIn X := by
    refine ⟨hzX, mem_centralizer_iff.2 fun x hx => ?_⟩
    have hle : X ≤ centralizer ({z} : Set Perm1782) := by
      rw [show X = closure {g | ∃ k < gs.size, a k = g} from rfl, closure_le]
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact (hzc' k hk).symm
    exact (mem_centralizer_singleton_iff.1 (hle hx))
  have hz1 : z ≠ 1 := by
    intro e
    have hfa : fixesAll (wordC gs zw) L0.pts = true := by
      rw [fixesAll, List.all_eq_true]
      intro p hp
      have hp' : p < 1782 := by
        have ht0' := ht0
        simp only [treeOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht0'
        simpa using ht0'.1.2 p hp
      rw [beq_iff_eq, hzrep.apply ⟨p, hp'⟩, e]
      rfl
    rw [hfa] at hzmove
    exact Bool.noConfusion hzmove
  have hge2 : 2 ≤ Nat.card ↥(centerIn X) := by
    have : (1 : ↥(centerIn X)) ≠ ⟨z, hzZ⟩ := fun e => hz1 (congrArg Subtype.val e).symm
    exact Finite.one_lt_card_iff_nontrivial.2 ⟨⟨1, ⟨z, hzZ⟩, this⟩⟩
  exact le_antisymm hle2 hge2

end CFSG.ComponentClassification.AS81.SuzCenter
