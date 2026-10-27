module

public import CFSG.Certificates.Kernel.J4NPVerdict.Group
public import CFSG.Milestones.ASVolI.C31.J4NP.TreeDefs

public section

namespace CFSG.KC.J4NPV

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.Native CFSG.KC.J4Q CFSG.ASVolI

theorem vj_mem_normalizer_closure {G : Type*} [Group G] [Finite G] {S : Set G} {s : G}
    (h : ∀ x ∈ S, s * x * s⁻¹ ∈ Subgroup.closure S) :
    s ∈ Subgroup.normalizer ((Subgroup.closure S : Subgroup G) : Set G) := by
  set K := Subgroup.closure S
  have hle : K.map (MulAut.conj s).toMonoidHom ≤ K := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hinj : Function.Injective ((MulAut.conj s).toMonoidHom : G →* G) :=
    (MulAut.conj s).injective
  have heq : K.map (MulAut.conj s).toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective hinj])
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hle ⟨y, hy, rfl⟩
  · intro hy
    rw [← heq] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hzy' : s * z * s⁻¹ = s * y * s⁻¹ := by simpa [MulAut.conj_apply] using hzy
    have : z = y := by simpa using hzy'
    rwa [← this]

@[expose] noncomputable def vjSub (L : List (Nat × Nat)) : Subgroup J :=
  Subgroup.closure {g | g ∈ L.map burnsideJ4NP_treeElt}

theorem vjElt_eq (p : Nat × Nat) : vjElt uJ kJ p = burnsideJ4NP_treeElt p := rfl

theorem vj_getD_mem {L : List (Nat × Nat)} {i : Nat} (hi : i < L.length) :
    burnsideJ4NP_treeElt (L.getD i (0, 0)) ∈ vjSub L := by
  apply Subgroup.subset_closure
  rw [List.getD_eq_getElem _ _ hi]
  exact List.mem_map.2 ⟨_, List.getElem_mem hi, rfl⟩

theorem vj_eta_mem (L : List (Nat × Nat)) (m : Nat) :
    eta (fun l => burnsideJ4NP_treeElt (L.getD l (0, 0))) L.length m ∈ vjSub L := by
  unfold eta
  suffices h : ∀ (S : List Nat), (∀ l ∈ S, l < L.length) → ∀ a ∈ vjSub L,
      S.foldl (fun acc l => if m.testBit l then acc * burnsideJ4NP_treeElt (L.getD l (0, 0))
        else acc) a ∈ vjSub L from
    h _ (fun l hl => List.mem_range.1 hl) 1 (Subgroup.one_mem _)
  intro S
  induction S with
  | nil => intro _ a ha; exact ha
  | cons l S ih =>
    intro hS a ha
    rw [List.foldl_cons]
    apply ih (fun l' hl' => hS l' (List.mem_cons_of_mem _ hl'))
    split_ifs
    · exact Subgroup.mul_mem _ ha (vj_getD_mem (hS l List.mem_cons_self))
    · exact ha

theorem vj_conj_mem {L : List (Nat × Nat)} {s x y : J} (h : s * x = y * s) (hy : y ∈ vjSub L) :
    s * x * s⁻¹ ∈ vjSub L := by
  rw [h, mul_inv_cancel_right]
  exact hy

theorem uJ_comm_eta (hE : ∀ i < 11, ∀ j < 11, uJ i * uJ j = uJ j * uJ i) {s : Nat} (hs : s < 11)
    (c : Nat) : uJ s * eta uJ 11 c = eta uJ 11 c * uJ s := by
  unfold eta
  suffices h : ∀ (S : List Nat), (∀ l ∈ S, l < 11) → ∀ a : J, uJ s * a = a * uJ s →
      uJ s * S.foldl (fun acc j => if c.testBit j then acc * uJ j else acc) a =
        S.foldl (fun acc j => if c.testBit j then acc * uJ j else acc) a * uJ s from
    h _ (fun l hl => List.mem_range.1 hl) 1 (by rw [mul_one, one_mul])
  intro S
  induction S with
  | nil => intro _ a ha; exact ha
  | cons l S ih =>
    intro hS a ha
    rw [List.foldl_cons]
    apply ih (fun l' hl' => hS l' (List.mem_cons_of_mem _ hl'))
    split_ifs
    · rw [← mul_assoc, ha, mul_assoc, hE s hs l (hS l List.mem_cons_self), mul_assoc]
    · exact ha

theorem comm_of_commK {T : Tabs} {g5 gE u k f : Nat → J} (hT : TabsOK T g5 gE u k f)
    (h : commK T.c T.rm T.us = true) : ∀ i < 11, ∀ j < 11, u i * u j = u j * u i := by
  obtain ⟨_, _, _, _, _, _, _, _, hK⟩ := hT.consts
  intro i hi j hj
  have hmem : ∀ l < 11, T.us.getD l 0 ∈ T.us := fun l hl => by
    rw [List.getD_eq_getElem _ _ (by rw [hT.us_len]; exact hl)]
    exact List.getElem_mem _
  exact vjRep_eq_of_eq (vjRep_mul hK (hT.us i hi) (hT.us j hj))
    (vjRep_mul hK (hT.us j hj) (hT.us i hi)) (commK_spec h _ (hmem i hi) _ (hmem j hj))

theorem Wv_eq_vjSub (k : Nat) : burnsideJ4NP_Wv k = vjSub (CFSG.J4Tree.Native.treeWv k) := rfl

theorem fB_le {T : Tabs} {g5 gE f : Nat → J} (hT : TabsOK T g5 gE uJ kJ f)
    {d : CFSG.J4Tree.VerdictJ.FData} (h : fB T d = true) :
    ∃ x : J, (Subgroup.closure {y | ∃ j < 10, y = f j}).map (MulAut.conj x).toMonoidHom ≤
      burnsideJ4NP_Wv d.node := by
  obtain ⟨_, hf⟩ := fB_group hT h
  simp only [vjElt_eq] at hf
  refine ⟨facProd g5 gE d.d, ?_⟩
  rw [MonoidHom.map_closure, Subgroup.closure_le, Wv_eq_vjSub]
  rintro _ ⟨y, ⟨j, hj, rfl⟩, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact vj_conj_mem (hf j hj) (vj_eta_mem _ _)

theorem conjB_eq {T : Tabs} {g5 gE f : Nat → J} (hT : TabsOK T g5 gE uJ kJ f)
    {src : List (Nat × Nat)} {d : CFSG.J4Tree.M4.ConjD} (h : conjB T src d = true) :
    ∃ m : J, vjSub d.tgt = (vjSub src).map (MulAut.conj m).toMonoidHom := by
  obtain ⟨_, _, hfw, hbw⟩ := conjB_group hT h
  simp only [vjElt_eq] at hfw hbw
  refine ⟨wordProd gE d.word, le_antisymm ?_ ?_⟩
  · rw [vjSub, Subgroup.closure_le]
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
    rw [← List.getD_eq_getElem d.tgt (0, 0) hj]
    refine ⟨eta (fun l => burnsideJ4NP_treeElt (src.getD l (0, 0))) src.length (d.bwd.getD j 0),
      vj_eta_mem _ _, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hbw j hj, mul_inv_cancel_right]
  · rw [vjSub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
    rw [← List.getD_eq_getElem src (0, 0) hi, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact vj_conj_mem (hfw i hi) (vj_eta_mem _ _)

theorem npB_normalizer {T : Tabs} {g5 gE f : Nat → J} (hT : TabsOK T g5 gE uJ kJ f)
    (hE : ∀ i < 11, ∀ j < 11, uJ i * uJ j = uJ j * uJ i) {d : CFSG.J4Tree.VerdictJ.NPData}
    (h : npB T d = true) :
    ∃ g : J, P0.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (burnsideJ4NP_Wv d.node : Set J) := by
  obtain ⟨_, _, hlen, hc, hu, hk⟩ := npB_group hT h
  simp only [vjElt_eq] at hc hu hk
  set g := facProd g5 gE d.g
  set WL := CFSG.J4Tree.Native.treeWv d.node
  have hcj : ∀ i < WL.length, burnsideJ4NP_treeElt (WL.getD i (0, 0)) =
      g * burnsideJ4NP_treeElt (d.V.getD i (0, 0)) * g⁻¹ := by
    intro i hi
    rw [← hc i (hlen ▸ hi), mul_inv_cancel_right]
  have hW : burnsideJ4NP_Wv d.node = (vjSub d.V).map (MulAut.conj g).toMonoidHom := by
    rw [burnsideJ4NP_Wv, vjSub, MonoidHom.map_closure]
    refine congrArg Subgroup.closure ?_
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
      refine ⟨burnsideJ4NP_treeElt (d.V.getD i (0, 0)),
        ⟨d.V.getD i (0, 0), ?_, rfl⟩, ?_⟩
      · rw [List.getD_eq_getElem _ _ (hlen ▸ hi)]
        exact List.getElem_mem _
      · rw [← List.getD_eq_getElem WL (0, 0) hi, hcj i hi]
        rfl
    · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
      have hi' : i < WL.length := by rw [hlen]; exact hi
      refine ⟨WL.getD i (0, 0), ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hi']
        exact List.getElem_mem _
      · rw [hcj i hi', ← List.getD_eq_getElem d.V (0, 0) hi]
        rfl
  have hgen : ∀ t ∈ S0, ∀ x ∈ {g | g ∈ d.V.map burnsideJ4NP_treeElt},
      t * x * t⁻¹ ∈ vjSub d.V := by
    rintro t ht x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
    rw [← List.getD_eq_getElem d.V (0, 0) hi]
    rcases ht with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rcases hu j hj i hi with hE0 | he
      · have h0 : (d.V.getD i (0, 0)).2 = 0 := by
          apply hE0
          rw [List.getD_eq_getElem _ _ hi]
          exact List.getElem_mem _
        have hx : burnsideJ4NP_treeElt (d.V.getD i (0, 0)) = eta uJ 11 (d.V.getD i (0, 0)).1 := by
          have hK0 : Kel 0 = 1 := by
            unfold Kel
            rfl
          rw [burnsideJ4NP_treeElt, h0, hK0, mul_one]
        rw [hx, uJ_comm_eta hE hj, mul_inv_cancel_right, ← hx]
        exact vj_getD_mem hi
      · exact vj_conj_mem he (vj_eta_mem _ _)
    · exact vj_conj_mem (hk j hj i hi) (vj_eta_mem _ _)
  have hP : P0 ≤ Subgroup.normalizer (vjSub d.V : Set J) := by
    rw [P0, Subgroup.closure_le]
    intro t ht
    exact vj_mem_normalizer_closure (hgen t ht)
  refine ⟨g, ?_⟩
  rw [hW, ← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hP

end CFSG.KC.J4NPV

end
