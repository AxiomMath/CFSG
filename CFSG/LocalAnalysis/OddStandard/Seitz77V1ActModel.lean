module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check
public import Certificates.Data.Seitz77L34FCent
public import Certificates.Data.Seitz77L34V1Act
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificateBase

public section

namespace CFSG.OddStandard.Seitz77.V1Act

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem tabRep_invTab {n : ℕ} {t : Tab} {g : Equiv.Perm (Fin n)} (ht : TabRep t g) :
    TabRep (invTab n t) g⁻¹ := by
  have hloop : invTab n t =
      (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
    unfold invTab
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
      Std.Legacy.Range.size]
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
    rfl
  have key : ∀ k, k ≤ n →
      ((List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)).size = n ∧
      ∀ i < k,
        ((List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨Array.size_replicate .., fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨hs, hv⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) = r
        at hs hv ⊢
      have hk' : k < n := hk
      have htk : t[k]! = (g ⟨k, hk'⟩ : ℕ) := ht.apply ⟨k, hk'⟩
      refine ⟨by rw [Array.size_set!, hs], fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | hik
      · have hlt' : i < n := by omega
        have hti : t[i]! = (g ⟨i, hlt'⟩ : ℕ) := ht.apply ⟨i, hlt'⟩
        have hne : t[k]! ≠ t[i]! := by
          rw [htk, hti]
          intro h
          have h3 := congrArg Fin.val (g.injective (Fin.ext h))
          simp only at h3
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ hne]
        exact hv i hlt
      · subst hik
        rw [htk]
        exact Array.getElem!_set!_self r _ _ (by rw [hs]; exact (g ⟨i, hk'⟩).2)
  obtain ⟨hs, hv⟩ := key n le_rfl
  rw [hloop]
  refine ⟨hs, fun j => ?_⟩
  have h1 := hv (g⁻¹ j).val (g⁻¹ j).2
  have h2 : t[(g⁻¹ j).val]! = j.val := by
    have hj : g (g⁻¹ j) = j := Equiv.apply_symm_apply g j
    rw [ht.apply, hj]
  rw [h2] at h1
  exact h1

theorem tabRep_of_comp_idTab {n : ℕ} {t : Tab} {g : Equiv.Perm (Fin n)} (hs : t.size = n)
    (h : TabRep (comp n t (idTab n)) g) : TabRep t g := by
  refine ⟨hs, fun i => ?_⟩
  have := h.2 i
  rwa [TabRep.comp_getElem!, TabRep.idTab_getElem!] at this

theorem enumOK_posOf {n : ℕ} {gens : Array Tab} {E : Enum} (h : enumOK n gens E = true) :
    ∀ i < E.tabs.size, posOf (indexOf E.tabs) E.tabs E.tabs[i]! = i := by
  unfold enumOK treeOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allBelow_eq_true] at h
  intro i hi
  exact (h.2 i hi).1.1

theorem l34SylCheck_spec {ES : Array Tab} (hES : Enumerates S ES.toList)
    (h : l34SylCheck ES = true) :
    ∃ P F : Subgroup (Equiv.Perm (Fin 42)), Enumerates F (enumBFS 42 fGens 16).tabs.toList ∧
      P ≤ S ∧ Nat.card P = 64 ∧ F ≤ P ∧ Nat.card F = 16 ∧
      (∀ f ∈ F, ∀ g ∈ F, f * g = g * f) ∧ (∀ f ∈ F, f * f = 1) ∧
      (∀ x ∈ P, r₃ * x * r₃⁻¹ ∈ P) := by
  unfold l34SylCheck at h
  extract_lets EP EPi idxP Et EF idxF nI at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16⟩ := h
  clear_value EP EPi idxP idxF nI
  have hr3r3 : r₃ * r₃ = 1 := Equiv.ext g6Fun_g6Fun
  have hr3i : r₃⁻¹ = r₃ := inv_eq_of_mul_eq_one_right hr3r3
  have hgensS : ∀ j < pGens.size, ∃ a ∈ S, TabRep pGens[j]! a := by
    intro j hj
    obtain ⟨k, hk, hkj⟩ := memTab_iff.1 ((allBelow_eq_true.1 c1) j hj)
    obtain ⟨a, haS, har⟩ := hES.exists_elt hk
    exact ⟨a, haS, by rw [← hkj]; exact har⟩
  set A : Set (Equiv.Perm (Fin 42)) := {a | ∃ j < pGens.size, TabRep pGens[j]! a}
  have hAS : A ⊆ S := by
    rintro a ⟨j, hj, har⟩
    obtain ⟨b, hbS, hbr⟩ := hgensS j hj
    rwa [har.perm_eq hbr]
  set P : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure A
  have hP : Enumerates P EP.tabs.toList :=
    enumerates_closure (fun a ha => ha) (fun j hj => by
      obtain ⟨a, -, har⟩ := hgensS j hj
      exact ⟨a, ⟨j, hj, har⟩, har⟩) c2
  have hPS : P ≤ S := (Subgroup.closure_le S).2 hAS
  have hcardP : Nat.card P = 64 := by
    rw [hP.card, Array.length_toList]
    exact beq_iff_eq.1 c3
  have hr3P : ∀ x ∈ P, r₃ * x * r₃⁻¹ ∈ P := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := hP.exists_pos hx
    obtain ⟨g, hgP, hg⟩ := hP.sound _ (mem_of_found ((allBelow_eq_true.1 c6) k hk))
    have hr : TabRep r₃T r₃⁻¹ := by rw [hr3i]; exact tabRep_r₃
    rw [(tabRep_r₃.conjTab hxk hr).perm_eq hg]
    exact hgP
  have hEFtab : ∀ k < EF.tabs.size, ∃ g ∈ P, TabRep EF.tabs[k]! g := by
    intro k hk
    have h11 := (allBelow_eq_true.1 c11) k hk
    simp only [Bool.and_eq_true] at h11
    exact hP.sound _ (mem_of_found h11.1.1)
  have hfsz : ∀ j < fGens.size, (fGens[j]!).size = 42 := by decide
  have hFgens : ∀ j < fGens.size, ∃ a : Equiv.Perm (Fin 42), TabRep fGens[j]! a := by
    intro j hj
    have c9' := c9
    unfold enumOK at c9'
    obtain ⟨hpos, h0, -, hclosed, -⟩ := treeOK_spec c9'
    have hmem := hclosed 0 hpos j hj
    rw [h0] at hmem
    obtain ⟨k, hk, hkeq⟩ := exists_getElem!_of_mem hmem
    obtain ⟨g, -, hg⟩ := hEFtab k hk
    rw [hkeq] at hg
    exact ⟨g, tabRep_of_comp_idTab (hfsz j hj) hg⟩
  set A' : Set (Equiv.Perm (Fin 42)) := {a | ∃ j < fGens.size, TabRep fGens[j]! a}
  set F : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure A'
  have hF : Enumerates F EF.tabs.toList :=
    enumerates_closure (fun a ha => ha) (fun j hj => by
      obtain ⟨a, har⟩ := hFgens j hj
      exact ⟨a, ⟨j, hj, har⟩, har⟩) c9
  have hcardF : Nat.card F = 16 := by
    rw [hF.card, Array.length_toList]
    exact beq_iff_eq.1 c10
  have hFP : F ≤ P := by
    intro f hf
    obtain ⟨k, hk, hfk⟩ := hF.exists_pos hf
    obtain ⟨g, hgP, hg⟩ := hEFtab k hk
    rw [hfk.perm_eq hg]
    exact hgP
  have hFdata : ∀ f ∈ F, f * f = 1 ∧ ∀ g ∈ F, f * g = g * f := by
    intro f hf
    obtain ⟨k, hk, hfk⟩ := hF.exists_pos hf
    have h11 := (allBelow_eq_true.1 c11) k hk
    simp only [Bool.and_eq_true] at h11
    obtain ⟨⟨-, h2⟩, h3⟩ := h11
    refine ⟨((hfk.comp hfk).beq_iff TabRep.idTab).1 h2, fun g hg => ?_⟩
    obtain ⟨l, hl, hgl⟩ := hF.exists_pos hg
    exact ((hfk.comp hgl).beq_iff (hgl.comp hfk)).1 ((allBelow_eq_true.1 h3) l hl)
  exact ⟨P, F, hF, hPS, hcardP, hFP, hcardF, fun f hf g hg => (hFdata f hf).2 g hg,
    fun f hf => (hFdata f hf).1, hr3P⟩

theorem l34FCentCheck_spec {F : Subgroup (Equiv.Perm (Fin 42))}
    (hF : Enumerates F (enumBFS 42 fGens 16).tabs.toList) {ER : Array Tab}
    (hER : Enumerates R ER.toList) (h : Certificates.Seitz77L34.l34FCentCheck ER = true) :
    (∀ x ∈ R, (∀ f ∈ F, x * f = f * x) → x ∈ F) ∧ ∃ f ∈ F, r₃ * f * r₃⁻¹ ∉ F := by
  unfold Certificates.Seitz77L34.l34FCentCheck at h
  extract_lets EF idxF at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := h
  have hr3r3 : r₃ * r₃ = 1 := Equiv.ext g6Fun_g6Fun
  have hr3i : r₃⁻¹ = r₃ := inv_eq_of_mul_eq_one_right hr3r3
  have hEF : EF = enumBFS 42 fGens 16 := rfl
  refine ⟨fun x hx hxc => ?_, ?_⟩
  · have hcomm : ∀ i < EF.tabs.size, ∃ a, TabRep EF.tabs[i]! a ∧ a * x = x * a := by
      intro i hi
      obtain ⟨g, hgF, hg⟩ := hF.exists_elt hi
      exact ⟨g, hg, (hxc g hgF).symm⟩
    obtain ⟨t, ht, hrep⟩ := centScanOK_spec hER c3 hx hcomm
    obtain ⟨g, hgF, hg⟩ := hF.sound t ht
    rw [hrep.perm_eq hg]
    exact hgF
  · obtain ⟨a, ha, hnf⟩ := anyBelow_eq_true.1 c4
    obtain ⟨g, hgF, hg⟩ := hF.exists_elt ha
    refine ⟨g, hgF, fun hmem => ?_⟩
    have hr : TabRep r₃T r₃⁻¹ := by rw [hr3i]; exact tabRep_r₃
    have htab := tabRep_r₃.conjTab hg hr
    obtain ⟨k, hk, hkt⟩ := hF.exists_pos hmem
    have hfound : found idxF EF.tabs (conjTab 42 r₃T r₃T EF.tabs[a]!) = true := by
      have hkk : conjTab 42 r₃T r₃T EF.tabs[a]! = EF.tabs[k]! := hkt.tab_eq htab |>.symm
      rw [hkk]
      have hk' : k < EF.tabs.size := hk
      have hp : posOf idxF EF.tabs EF.tabs[k]! = k := enumOK_posOf c1 k hk'
      unfold found
      rw [hp]
      simp [hk']
    rw [hfound] at hnf
    exact Bool.noConfusion hnf

section ActRep

variable {F : Subgroup (Equiv.Perm (Fin 42))} {EFt : Array Tab}

@[expose] def imgTab (EF : Array Tab) (r : Tab) : Tab :=
  EF.map fun f => posOf (indexOf EF) EF (conjTab 42 r (invTab 42 r) f)

@[expose] def passes (EF : Array Tab) (r : Tab) : Bool :=
  allBelow EF.size (fun i => (imgTab EF r)[i]! < EF.size &&
    EF[(imgTab EF r)[i]!]! == conjTab 42 r (invTab 42 r) EF[i]!)

def ActRep (EFt : Array Tab) (T : Tab) (r : Equiv.Perm (Fin 42)) : Prop :=
  T.size = EFt.size ∧ ∀ i < EFt.size, ∀ g : Equiv.Perm (Fin 42), TabRep EFt[i]! g →
    T[i]! < EFt.size ∧ TabRep EFt[T[i]!]! (r * g * r⁻¹)

theorem getElem!_imgTab {EF : Array Tab} {r : Tab} {i : ℕ} (hi : i < EF.size) :
    (imgTab EF r)[i]! = posOf (indexOf EF) EF (conjTab 42 r (invTab 42 r) EF[i]!) := by
  have hi' : i < (imgTab EF r).size := by simpa [imgTab] using hi
  rw [getElem!_pos _ i hi', getElem!_pos EF i hi]
  simp [imgTab]

theorem actRep_imgTab (hF : Enumerates F EFt.toList)
    (hpos : ∀ i < EFt.size, posOf (indexOf EFt) EFt EFt[i]! = i) {rT : Tab}
    {r : Equiv.Perm (Fin 42)} (hr : TabRep rT r) (hn : ∀ f ∈ F, r * f * r⁻¹ ∈ F) :
    ActRep EFt (imgTab EFt rT) r ∧ passes EFt rT = true := by
  have hinv : TabRep (invTab 42 rT) r⁻¹ := tabRep_invTab hr
  have key : ∀ i < EFt.size, ∀ g, TabRep EFt[i]! g →
      ∃ p < EFt.size, TabRep EFt[p]! (r * g * r⁻¹) ∧ (imgTab EFt rT)[i]! = p := by
    intro i hi g hg
    have hgF : g ∈ F := by
      obtain ⟨g', hg', h'⟩ := hF.exists_elt hi
      rwa [hg.perm_eq h']
    obtain ⟨p, hp, hpt⟩ := hF.exists_pos (hn g hgF)
    have htab : conjTab 42 rT (invTab 42 rT) EFt[i]! = EFt[p]! := (hr.conjTab hg hinv).tab_eq hpt
    refine ⟨p, hp, hpt, ?_⟩
    rw [getElem!_imgTab hi, htab]
    exact hpos p hp
  refine ⟨⟨by simp [imgTab], fun i hi g hg => ?_⟩, ?_⟩
  · obtain ⟨p, hp, hpt, hip⟩ := key i hi g hg
    rw [hip]
    exact ⟨hp, hpt⟩
  · rw [passes, allBelow_eq_true]
    intro i hi
    obtain ⟨g, -, hg⟩ := hF.exists_elt hi
    obtain ⟨p, hp, hpt, hip⟩ := key i hi g hg
    have htab : conjTab 42 rT (invTab 42 rT) EFt[i]! = EFt[p]! := (hr.conjTab hg hinv).tab_eq hpt
    rw [hip, htab]
    simp [hp]

theorem actRep_one (hsz : EFt.size = 16) : ActRep EFt (idTab 16) 1 := by
  refine ⟨by simp [idTab, hsz], fun i hi g hg => ?_⟩
  have e : (idTab 16)[i]! = i := TabRep.idTab_getElem! (n := 16) ⟨i, by omega⟩
  refine ⟨by rw [e]; exact hi, ?_⟩
  rw [e]
  simpa using hg

theorem actRep_comp (hsz : EFt.size = 16) {T T' : Tab} {r r' : Equiv.Perm (Fin 42)}
    (h : ActRep EFt T r) (h' : ActRep EFt T' r') : ActRep EFt (comp 16 T T') (r * r') := by
  refine ⟨by simp [comp, hsz], fun i hi g hg => ?_⟩
  obtain ⟨hj, hjt⟩ := h'.2 i hi g hg
  obtain ⟨hk, hkt⟩ := h.2 _ hj _ hjt
  have e : (comp 16 T T')[i]! = T[T'[i]!]! := TabRep.comp_getElem! (n := 16) T T' ⟨i, by omega⟩
  rw [e]
  refine ⟨hk, ?_⟩
  have : r * (r' * g * r'⁻¹) * r⁻¹ = r * r' * g * (r * r')⁻¹ := by group
  rwa [this] at hkt

theorem actRep_eq_iff (hF : Enumerates F EFt.toList) {T T' : Tab} {r r' : Equiv.Perm (Fin 42)}
    (h : ActRep EFt T r) (h' : ActRep EFt T' r') :
    T = T' ↔ ∀ f ∈ F, r * f * r⁻¹ = r' * f * r'⁻¹ := by
  constructor
  · rintro rfl f hf
    obtain ⟨i, hi, hfi⟩ := hF.exists_pos hf
    obtain ⟨-, h1⟩ := h.2 i hi f hfi
    obtain ⟨-, h2⟩ := h'.2 i hi f hfi
    exact h1.perm_eq h2
  · intro hall
    apply Array.ext (h.1.trans h'.1.symm)
    intro i hi hi'
    have hi0 : i < EFt.size := h.1 ▸ hi
    obtain ⟨g, hgF, hg⟩ := hF.exists_elt hi0
    obtain ⟨hk, h1⟩ := h.2 i hi0 g hg
    obtain ⟨hk', h2⟩ := h'.2 i hi0 g hg
    rw [hall g hgF] at h1
    have := hF.pos_unique hk hk' h1 h2
    rwa [getElem!_pos T i hi, getElem!_pos T' i hi'] at this

theorem actRep_card_fix (hF : Enumerates F EFt.toList) (hsz : EFt.size = 16) {T : Tab}
    {r : Equiv.Perm (Fin 42)} (h : ActRep EFt T r) :
    Nat.card ↥(F ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42)))) ≤
      countBelow 16 (fun i => T[i]! == i) := by
  classical
  rw [countBelow_eq]
  set s : Finset ℕ := (Finset.range 16).filter fun k => (T[k]! == k) = true with hs
  have hex : ∀ f : ↥(F ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42)))),
      ∃ k < EFt.size, TabRep EFt[k]! (f : Equiv.Perm (Fin 42)) := fun f => hF.exists_pos f.2.1
  choose k hk hkt using hex
  have hmem : ∀ f, k f ∈ s := by
    intro f
    have hcomm : (f : Equiv.Perm (Fin 42)) * r = r * f :=
      Subgroup.mem_centralizer_singleton_iff.1 f.2.2
    have hconj : r * (f : Equiv.Perm (Fin 42)) * r⁻¹ = f := by
      rw [← hcomm]; group
    obtain ⟨hlt, ht⟩ := h.2 (k f) (hk f) _ (hkt f)
    rw [hconj] at ht
    have := hF.pos_unique hlt (hk f) ht (hkt f)
    rw [hs, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simp [this]⟩
  have hinj : Function.Injective (fun f => (⟨k f, hmem f⟩ : s)) := by
    intro f f' he
    have hkk : k f = k f' := congrArg Subtype.val he
    apply Subtype.ext
    have h1 := hkt f
    rw [hkk] at h1
    exact h1.perm_eq (hkt f')
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

end ActRep


section V1Acts

def actStep (EF : Array Tab) (r : Tab) (s : Std.HashMap Tab Unit × Array Tab) :
    Std.HashMap Tab Unit × Array Tab :=
  if passes EF r = true then
    (if (!s.1.contains (imgTab EF r)) = true then
      (s.1.insert (imgTab EF r) (), s.2.push (imgTab EF r)) else s)
  else s

theorem v1Acts_eq (EF ER : Array Tab) :
    Certificates.Seitz77L34.v1Acts EF ER = (ER.foldl (fun s r => actStep EF r s) (∅, #[])).2 := by
  have h : ∀ (r : Tab) (s : Std.HashMap Tab Unit × Array Tab),
      (if passes EF r = true then
        (if (!s.1.contains (imgTab EF r)) = true then
          pure (ForInStep.yield (s.1.insert (imgTab EF r) (), s.2.push (imgTab EF r)))
         else pure (ForInStep.yield (s.1, s.2)))
       else pure (ForInStep.yield (s.1, s.2)) : Id (ForInStep (Std.HashMap Tab Unit × Array Tab)))
      = pure (ForInStep.yield (actStep EF r s)) := by
    intro r s
    unfold actStep
    split_ifs <;> rfl
  unfold Certificates.Seitz77L34.v1Acts
  simp only [Id.run, bind_pure_comp]
  show (Prod.snd <$> forIn ER ((∅ : Std.HashMap Tab Unit), (#[] : Array Tab))
      fun r (__s : Std.HashMap Tab Unit × Array Tab) =>
        (if passes EF r = true then
          (if (!__s.1.contains (imgTab EF r)) = true then
            pure (ForInStep.yield (__s.1.insert (imgTab EF r) (), __s.2.push (imgTab EF r)))
           else pure (ForInStep.yield (__s.1, __s.2)))
         else pure (ForInStep.yield (__s.1, __s.2)) :
           Id (ForInStep (Std.HashMap Tab Unit × Array Tab)))) = _
  simp only [h]
  rw [Array.forIn_pure_yield_eq_foldl]
  rfl

theorem foldl_actStep_spec (EF : Array Tab) (L : List Tab) :
    ∀ (s : Std.HashMap Tab Unit × Array Tab), (∀ t, s.1.contains t = true → t ∈ s.2.toList) →
    (∀ t ∈ s.2.toList, t ∈ (L.foldl (fun s r => actStep EF r s) s).2.toList) ∧
    (∀ r ∈ L, passes EF r = true →
      imgTab EF r ∈ (L.foldl (fun s r => actStep EF r s) s).2.toList) ∧
    (∀ t, (L.foldl (fun s r => actStep EF r s) s).1.contains t = true →
      t ∈ (L.foldl (fun s r => actStep EF r s) s).2.toList) := by
  induction L with
  | nil => intro s hs; exact ⟨fun t ht => ht, by simp, hs⟩
  | cons a L ih =>
    intro s hs
    have hs' : ∀ t, (actStep EF a s).1.contains t = true → t ∈ (actStep EF a s).2.toList := by
      intro t ht
      by_cases hp : passes EF a = true
      · by_cases hc : (!s.1.contains (imgTab EF a)) = true
        · simp only [actStep, hp, hc, ↓reduceIte, Std.HashMap.contains_insert, Bool.or_eq_true,
            beq_iff_eq, Array.toList_push, List.mem_append, List.mem_singleton] at ht ⊢
          rcases ht with h | h
          · exact Or.inr h.symm
          · exact Or.inl (hs t h)
        · simp only [actStep, hp, hc, ↓reduceIte] at ht ⊢
          exact hs t ht
      · simp only [actStep, hp] at ht ⊢
        exact hs t ht
    obtain ⟨h1, h2, h3⟩ := ih _ hs'
    simp only [List.foldl_cons]
    refine ⟨fun t ht => h1 t ?_, fun r hr hpr => ?_, h3⟩
    · by_cases hp : passes EF a = true
      · by_cases hc : (!s.1.contains (imgTab EF a)) = true
        · simp [actStep, hp, hc, ht]
        · simp [actStep, hp, hc, ht]
      · simp [actStep, hp, ht]
    · rcases List.mem_cons.1 hr with rfl | hr
      · apply h1
        by_cases hc : (!s.1.contains (imgTab EF r)) = true
        · simp [actStep, hpr, hc]
        · have : s.1.contains (imgTab EF r) = true := by simpa using hc
          simp only [actStep, hpr, hc, ↓reduceIte]
          exact hs _ this
      · exact h2 r hr hpr

theorem mem_v1Acts {EF ER : Array Tab} {r : Tab} (hr : r ∈ ER.toList)
    (hp : passes EF r = true) : imgTab EF r ∈ (Certificates.Seitz77L34.v1Acts EF ER).toList := by
  rw [v1Acts_eq, ← Array.foldl_toList]
  exact (foldl_actStep_spec EF ER.toList (∅, #[]) (by simp)).2.1 r hr hp

end V1Acts

@[expose] def Norm (F : Subgroup (Equiv.Perm (Fin 42))) (r : Equiv.Perm (Fin 42)) : Prop :=
  ∀ f ∈ F, r * f * r⁻¹ ∈ F

@[expose] def ActEq (F : Subgroup (Equiv.Perm (Fin 42))) (r s : Equiv.Perm (Fin 42)) : Prop :=
  ∀ f ∈ F, r * f * r⁻¹ = s * f * s⁻¹

@[expose] def ActCard (F : Subgroup (Equiv.Perm (Fin 42))) : Prop :=
  ∀ r ∈ R, Norm F r → (∃ f ∈ F, r * f * r⁻¹ ≠ f) →
    Nat.card ↥(F ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42)))) ≤ 4

@[expose] def ActTriple (F : Subgroup (Equiv.Perm (Fin 42))) : Prop :=
  ∀ x y z : Equiv.Perm (Fin 42), x ∈ R → y ∈ R → z ∈ R → Norm F x → Norm F y → Norm F z →
    ActEq F (x * x) 1 → ActEq F (y * y) 1 → ActEq F (z * z) 1 →
    ActEq F (x * y) (y * x) → ActEq F (x * z) (z * x) → ActEq F (y * z) (z * y) →
    ¬ ActEq F x 1 → ¬ ActEq F y 1 → ¬ ActEq F y x → ¬ ActEq F z 1 → ¬ ActEq F z x →
    ¬ ActEq F z y → ¬ ActEq F z (x * y) → False

theorem l34V1ActCheck_spec {F : Subgroup (Equiv.Perm (Fin 42))}
    (hF : Enumerates F (enumBFS 42 fGens 16).tabs.toList) {ER : Array Tab}
    (hER : Enumerates R ER.toList) (h : Certificates.Seitz77L34.l34V1ActCheck ER = true) :
    ActCard F ∧ ActTriple F := by
  unfold ActCard ActTriple
  unfold Certificates.Seitz77L34.l34V1ActCheck at h
  extract_lets EF acts idF invs at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := h
  have hsz : EF.tabs.size = 16 := beq_iff_eq.1 c2
  have hpos : ∀ i < EF.tabs.size, posOf (indexOf EF.tabs) EF.tabs EF.tabs[i]! = i :=
    enumOK_posOf c1
  have hF' : Enumerates F EF.tabs.toList := hF
  have hid : idF = idTab 16 := rfl
  have hact : ∀ r ∈ R, Norm F r → ∃ T, ActRep EF.tabs T r ∧ ∃ k < acts.size, acts[k]! = T := by
    intro r hr hn
    obtain ⟨rT, hrT, hrep⟩ := hER.complete r hr
    obtain ⟨hact, hpass⟩ := actRep_imgTab hF' hpos hrep hn
    obtain ⟨k, hk, hkt⟩ := exists_getElem!_of_mem (mem_v1Acts hrT hpass)
    exact ⟨_, hact, k, hk, hkt⟩
  refine ⟨fun r hr hn hne => ?_, fun x y z hx hy hz nx ny nz hxx hyy hzz hxy hxz hyz hx1 hy1 hyx
    hz1 hzx hzy hzxy => ?_⟩
  · obtain ⟨T, hT, k, hk, hkt⟩ := hact r hr hn
    have hTid : T ≠ idTab 16 := by
      intro hTe
      obtain ⟨f, hf, hfne⟩ := hne
      have := (actRep_eq_iff hF' hT (actRep_one hsz)).1 hTe f hf
      simp only [one_mul, inv_one, mul_one] at this
      exact hfne this
    have h3 := (allBelow_eq_true.1 c3) k hk
    rw [hkt] at h3
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h3
    rcases h3 with h3 | h3
    · exact absurd h3 hTid
    · exact (actRep_card_fix hF' hsz hT).trans h3
  · obtain ⟨X, aX, kx, hkx, hkxt⟩ := hact x hx nx
    obtain ⟨Y, aY, ky, hky, hkyt⟩ := hact y hy ny
    obtain ⟨Z, aZ, kz, hkz, hkzt⟩ := hact z hz nz
    have hsq : ∀ {T : Tab} {r : Equiv.Perm (Fin 42)}, ActRep EF.tabs T r → ActEq F (r * r) 1 →
        comp 16 T T = idTab 16 := fun hT hrr =>
      (actRep_eq_iff hF' (actRep_comp hsz hT hT) (actRep_one hsz)).2 hrr
    have hinvs : ∀ {T : Tab}, (∃ k < acts.size, acts[k]! = T) → comp 16 T T = idTab 16 →
        ∃ k < invs.size, invs[k]! = T := by
      rintro T ⟨k, hk, hkt⟩ hTT
      have hmem : T ∈ invs.toList := by
        simp only [invs, Array.toList_filter, List.mem_filter, beq_iff_eq]
        exact ⟨hkt ▸ getElem!_mem hk, by simpa [hid] using hTT⟩
      exact exists_getElem!_of_mem hmem
    obtain ⟨a, ha, hax⟩ := hinvs ⟨kx, hkx, hkxt⟩ (hsq aX hxx)
    obtain ⟨b, hb, hby⟩ := hinvs ⟨ky, hky, hkyt⟩ (hsq aY hyy)
    obtain ⟨c, hc, hcz⟩ := hinvs ⟨kz, hkz, hkzt⟩ (hsq aZ hzz)
    have h4 := (allBelow_eq_true.1 ((allBelow_eq_true.1 ((allBelow_eq_true.1 c4) a ha)) b hb)) c hc
    rw [hax, hby, hcz] at h4
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, hid] at h4
    have e1 : X = idTab 16 ↔ ActEq F x 1 := actRep_eq_iff hF' aX (actRep_one hsz)
    have e2 : Y = idTab 16 ↔ ActEq F y 1 := actRep_eq_iff hF' aY (actRep_one hsz)
    have e3 : Y = X ↔ ActEq F y x := actRep_eq_iff hF' aY aX
    have e4 : Z = idTab 16 ↔ ActEq F z 1 := actRep_eq_iff hF' aZ (actRep_one hsz)
    have e5 : Z = X ↔ ActEq F z x := actRep_eq_iff hF' aZ aX
    have e6 : Z = Y ↔ ActEq F z y := actRep_eq_iff hF' aZ aY
    have e7 : Z = comp 16 X Y ↔ ActEq F z (x * y) := actRep_eq_iff hF' aZ (actRep_comp hsz aX aY)
    have f1 : comp 16 X Y = comp 16 Y X ↔ ActEq F (x * y) (y * x) :=
      actRep_eq_iff hF' (actRep_comp hsz aX aY) (actRep_comp hsz aY aX)
    have f2 : comp 16 X Z = comp 16 Z X ↔ ActEq F (x * z) (z * x) :=
      actRep_eq_iff hF' (actRep_comp hsz aX aZ) (actRep_comp hsz aZ aX)
    have f3 : comp 16 Y Z = comp 16 Z Y ↔ ActEq F (y * z) (z * y) :=
      actRep_eq_iff hF' (actRep_comp hsz aY aZ) (actRep_comp hsz aZ aY)
    rcases h4 with (((((((h | h) | h) | h) | h) | h) | h) | h)
    · exact hx1 (e1.1 h)
    · exact hy1 (e2.1 h)
    · exact hyx (e3.1 h)
    · have h' : (comp 16 X Y == comp 16 Y X && comp 16 X Z == comp 16 Z X &&
          comp 16 Y Z == comp 16 Z Y) = true := by
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨⟨f1.2 hxy, f2.2 hxz⟩, f3.2 hyz⟩
      rw [h'] at h
      exact Bool.noConfusion h
    · exact hz1 (e4.1 h)
    · exact hzx (e5.1 h)
    · exact hzy (e6.1 h)
    · exact hzxy (e7.1 h)


theorem exists_triple_of_card_gt_four {Q : Type*} [Group Q] [Finite Q]
    (hcard : 4 < Nat.card Q) :
    ∃ a b c : Q, a ≠ 1 ∧ b ≠ 1 ∧ b ≠ a ∧ c ≠ 1 ∧ c ≠ a ∧ c ≠ b ∧ c ≠ a * b := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have hcard' : 4 < Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have key : ∀ s : Finset Q, s.card < Fintype.card Q → ∃ x : Q, x ∉ s := by
    intro s hs
    by_contra h
    have hsu : s = Finset.univ := Finset.eq_univ_iff_forall.mpr fun x => by
      by_contra hx
      exact h ⟨x, hx⟩
    rw [hsu, Finset.card_univ] at hs
    exact lt_irrefl _ hs
  obtain ⟨a, ha⟩ := key {1} (by rw [Finset.card_singleton]; omega)
  obtain ⟨b, hb⟩ := key {1, a} (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨c, hc⟩ := key {1, a, b, a * b} (lt_of_le_of_lt Finset.card_le_four hcard')
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at ha hb hc
  exact ⟨a, b, c, ha, hb.1, hb.2, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩

section Index

variable {F : Subgroup (Equiv.Perm (Fin 42))}

theorem actEq_iff_mem (hF1 : ∀ x ∈ R, (∀ f ∈ F, x * f = f * x) → x ∈ F)
    (hFab : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f) {x y : Equiv.Perm (Fin 42)} (hx : x ∈ R)
    (hy : y ∈ R) : ActEq F x y ↔ y⁻¹ * x ∈ F := by
  constructor
  · intro h
    refine hF1 _ (R.mul_mem (R.inv_mem hy) hx) fun f hf => ?_
    have := h f hf
    calc y⁻¹ * x * f = y⁻¹ * (x * f * x⁻¹) * x := by group
      _ = y⁻¹ * (y * f * y⁻¹) * x := by rw [this]
      _ = f * (y⁻¹ * x) := by group
  · intro h f hf
    have hc := hFab _ h f hf
    calc x * f * x⁻¹ = y * (y⁻¹ * x * f) * x⁻¹ := by group
      _ = y * (f * (y⁻¹ * x)) * x⁻¹ := by rw [hc]
      _ = y * f * y⁻¹ := by group

theorem relIndex_le_four_of_triple (hF1 : ∀ x ∈ R, (∀ f ∈ F, x * f = f * x) → x ∈ F)
    (hFab : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f) (hT : ActTriple F)
    {E : Subgroup (Equiv.Perm (Fin 42))} (hER : E ≤ R) (hn : ∀ x ∈ E, Norm F x)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ F) (hsq : ∀ x ∈ E, x * x ∈ F) :
    F.relIndex E ≤ 4 := by
  by_contra hlt
  push Not at hlt
  let H : Subgroup ↥E := F.subgroupOf E
  have hHn : H.Normal := ⟨fun n hn' g => by
    have : (g : Equiv.Perm (Fin 42)) * n * (g : Equiv.Perm (Fin 42))⁻¹ ∈ F := hn _ g.2 _ hn'
    exact this⟩
  have hcard : 4 < Nat.card (↥E ⧸ H) := by
    rw [← Subgroup.index_eq_card]
    exact hlt
  have hsqQ : ∀ q : ↥E ⧸ H, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact hsq x x.2
  obtain ⟨a, b, c, ha1, hb1, hba, hc1, hca, hcb, hcab⟩ := exists_triple_of_card_gt_four hcard
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective c
  have hmem : ∀ w : ↥E, (w : Equiv.Perm (Fin 42)) ∈ R := fun w => hER w.2
  have hF1' : ∀ w : ↥E, ((w : Equiv.Perm (Fin 42)) ∈ F ↔ w ∈ H) := fun w =>
    (Subgroup.mem_subgroupOf).symm
  have hone : ∀ w : ↥E, ActEq F (w : Equiv.Perm (Fin 42)) 1 ↔ (w : Equiv.Perm (Fin 42)) ∈ F := by
    intro w
    rw [actEq_iff_mem hF1 hFab (hmem w) R.one_mem]
    simp
  have hsqA : ∀ w : ↥E, ActEq F ((w : Equiv.Perm (Fin 42)) * w) 1 := by
    intro w
    rw [actEq_iff_mem hF1 hFab (R.mul_mem (hmem w) (hmem w)) R.one_mem]
    simpa using hsq w w.2
  have hcommA : ∀ u w : ↥E,
      ActEq F ((u : Equiv.Perm (Fin 42)) * w) ((w : Equiv.Perm (Fin 42)) * u) := by
    intro u w
    rw [actEq_iff_mem hF1 hFab (R.mul_mem (hmem u) (hmem w)) (R.mul_mem (hmem w) (hmem u))]
    have := hcomm _ (E.inv_mem u.2) _ (E.inv_mem w.2)
    simpa [mul_assoc] using this
  have hne : ∀ u w : ↥E, (↑u : ↥E ⧸ H) ≠ ↑w →
      ¬ ActEq F (w : Equiv.Perm (Fin 42)) (u : Equiv.Perm (Fin 42)) := by
    intro u w huw hact
    apply huw
    rw [QuotientGroup.eq]
    exact (hF1' _).1 ((actEq_iff_mem hF1 hFab (hmem w) (hmem u)).1 hact)
  have hne1 : ∀ u : ↥E, (↑u : ↥E ⧸ H) ≠ 1 → ¬ ActEq F (u : Equiv.Perm (Fin 42)) 1 := by
    intro u hu hact
    exact hu ((QuotientGroup.eq_one_iff u).2 ((hF1' u).1 ((hone u).1 hact)))
  refine hT x y z (hmem x) (hmem y) (hmem z) (hn x x.2) (hn y y.2) (hn z z.2) (hsqA x) (hsqA y)
    (hsqA z) (hcommA x y) (hcommA x z) (hcommA y z) (hne1 x ha1) (hne1 y hb1) (hne x y hba.symm)
    (hne1 z hc1) (hne x z hca.symm) (hne y z hcb.symm) ?_
  intro hact
  have hxy : (↑(x * y) : ↥E ⧸ H) ≠ ↑z := by
    rw [QuotientGroup.mk_mul]
    exact hcab.symm
  apply hxy
  rw [QuotientGroup.eq]
  have := (actEq_iff_mem hF1 hFab (hmem z) (R.mul_mem (hmem x) (hmem y))).1 hact
  exact (hF1' _).1 this

end Index

end CFSG.OddStandard.Seitz77.V1Act
