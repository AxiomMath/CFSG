
module

public import CFSG.RankThree.PartOne.HNB.UnitaryBridgeBase
public import Certificates.Data.Kernel.HN14969.Bridge
public import CFSG.Monster.B.Mathieu.Order

public section

namespace CFSG.KC.HN14969

open HNUnitaryBridge CFSG.RankThree.PartOne.HNB CFSG.Monster.B.Co2 CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem injective_of_card_le {G K : Type*} [Group G] [Group K] [Finite G] (f : G →* K)
    (h : Nat.card G ≤ Nat.card f.range) : Function.Injective f := by
  have hb := f.rangeRestrict_surjective.bijective_of_nat_card_le h
  intro a b hab
  exact hb.1 (Subtype.ext hab)

theorem fst_closure_pair {A B : Type*} [Group A] [Group B] (a1 a2 : A) (b1 b2 : B) :
    ((MonoidHom.fst A B).comp
        (Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B))).subtype).range =
      Subgroup.closure ({a1, a2} : Set A) := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem snd_closure_pair {A B : Type*} [Group A] [Group B] (a1 a2 : A) (b1 b2 : B) :
    ((MonoidHom.snd A B).comp
        (Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B))).subtype).range =
      Subgroup.closure ({b1, b2} : Set B) := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem snd_eq_one_of_card_le {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (a1 a2 : A) (b1 b2 : B)
    (h : Nat.card (Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B))) ≤
      Nat.card (Subgroup.closure ({a1, a2} : Set A))) :
    ∀ w ∈ Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B)), w.1 = 1 → w.2 = 1 := by
  intro w hw h1
  have hinj := injective_of_card_le ((MonoidHom.fst A B).comp
    (Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B))).subtype)
    (by rw [fst_closure_pair]; exact h)
  have he : (⟨w, hw⟩ : Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B))) = 1 :=
    hinj (by simpa using h1)
  have := congrArg (fun z : Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B)) =>
    (z : A × B).2) he
  simpa using this

theorem fst_eq_one_of_card_le {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (a1 a2 : A) (b1 b2 : B)
    (h : Nat.card (Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B))) ≤
      Nat.card (Subgroup.closure ({b1, b2} : Set B))) :
    ∀ w ∈ Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B)), w.2 = 1 → w.1 = 1 := by
  intro w hw h1
  have hinj := injective_of_card_le ((MonoidHom.snd A B).comp
    (Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B))).subtype)
    (by rw [snd_closure_pair]; exact h)
  have he : (⟨w, hw⟩ : Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B))) = 1 :=
    hinj (by simpa using h1)
  have := congrArg (fun z : Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B)) =>
    (z : A × B).1) he
  simpa using this

@[expose] noncomputable def emb :
    Equiv.Perm (Fin 50) × Equiv.Perm (Fin 126) →* Equiv.Perm (Fin (50 + 126)) :=
  ((finSumFinEquiv (m := 50) (n := 126)).permCongrHom.toMonoidHom).comp
    (Equiv.Perm.sumCongrHom (Fin 50) (Fin 126))

theorem emb_injective : Function.Injective emb :=
  (finSumFinEquiv (m := 50) (n := 126)).permCongrHom.injective.comp
    Equiv.Perm.sumCongrHom_injective

theorem emb_castAdd (p : Equiv.Perm (Fin 50)) (r : Equiv.Perm (Fin 126)) (x : Fin 50) :
    emb (p, r) (Fin.castAdd 126 x) = Fin.castAdd 126 (p x) := by
  change finSumFinEquiv (Sum.map p r (finSumFinEquiv.symm (Fin.castAdd 126 x))) = _
  rw [finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, finSumFinEquiv_apply_left]

theorem emb_natAdd (p : Equiv.Perm (Fin 50)) (r : Equiv.Perm (Fin 126)) (i : Fin 126) :
    emb (p, r) (Fin.natAdd 50 i) = Fin.natAdd 50 (r i) := by
  change finSumFinEquiv (Sum.map p r (finSumFinEquiv.symm (Fin.natAdd 50 i))) = _
  rw [finSumFinEquiv_symm_apply_natAdd, Sum.map_inr, finSumFinEquiv_apply_right]

theorem eq_emb {h : Equiv.Perm (Fin (50 + 126))} {p : Equiv.Perm (Fin 50)} {r : Equiv.Perm (Fin 126)}
    (h1 : ∀ x : Fin 50, (h (Fin.castAdd 126 x) : ℕ) = p x)
    (h2 : ∀ i : Fin 126, (h (Fin.natAdd 50 i) : ℕ) = 50 + r i) : h = emb (p, r) := by
  ext y
  refine Fin.addCases (m := 50) (n := 126) (motive := fun y => (h y : ℕ) = (emb (p, r) y : ℕ))
    (fun x => ?_) (fun i => ?_) y
  · rw [emb_castAdd, h1, Fin.coe_castAdd]
  · rw [emb_natAdd, h2, Fin.coe_natAdd]

@[expose] def decV (v : List ℕ) : Fin 3 → F25 := fun j => dec (lget v j)

theorem mvL_length (M v : List ℕ) : (mvL M v).length = 3 := by simp [mvL]

theorem decV_mvL (M v : List ℕ) : decV (mvL M v) = decMat (lget M) *ᵥ decV v := by
  funext j
  fin_cases j <;>
    simp [decV, mvL, lget, decMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, dec_fadd,
      dec_fmul]

theorem decV_map_fmul (c : ℕ) {u : List ℕ} (hu : u.length = 3) :
    decV (u.map (fmul c)) = dec c • decV u := by
  match u, hu with
  | [a, b, d], _ =>
    funext j
    fin_cases j <;> simp [decV, lget, dec_fmul]

theorem act_of_actOK {M : List ℕ} {X : List (List ℕ)} {g : ℕ → ℕ} (h : actOK M X g = true)
    {i : ℕ} (hi : i < 126) :
    ∃ c : F25, decV (X.getD (g i) []) = c • (decMat (lget M) *ᵥ decV (X.getD i [])) := by
  unfold actOK at h
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  refine ⟨dec (finv (firstNZL (mvL M (X.getD i [])))), ?_⟩
  rw [← this.2, normL, decV_map_fmul _ (mvL_length _ _), decV_mvL]

@[expose] def NormV (v : Fin 3 → F25) : Prop :=
  v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)

theorem eq_of_eq_smul {y z : Fin 3 → F25} (hy : NormV y) (hz : NormV z) {e : F25}
    (h : y = e • z) : y = z := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1 h2
  have he : e = 1 := by
    clear h
    unfold NormV at hy hz
    rcases hz with hz | ⟨hz0, hz1⟩ | ⟨hz0, hz1, hz2⟩ <;>
      rcases hy with hy | ⟨hy0, hy1⟩ | ⟨hy0, hy1, hy2⟩
    · rw [hy, hz, mul_one] at h0
      exact h0.symm
    · rw [hy0, hz, mul_one] at h0
      rw [hy1, ← h0, zero_mul] at h1
      exact absurd h1 one_ne_zero
    · rw [hy0, hz, mul_one] at h0
      rw [hy2, ← h0, zero_mul] at h2
      exact absurd h2 one_ne_zero
    · rw [hy, hz0, mul_zero] at h0
      exact absurd h0 one_ne_zero
    · rw [hy1, hz1, mul_one] at h1
      exact h1.symm
    · rw [hy1, hz1, mul_one] at h1
      rw [hy2, ← h1, zero_mul] at h2
      exact absurd h2 one_ne_zero
    · rw [hy, hz0, mul_zero] at h0
      exact absurd h0 one_ne_zero
    · rw [hy1, hz1, mul_zero] at h1
      exact absurd h1 one_ne_zero
    · rw [hy2, hz2, mul_one] at h2
      exact h2.symm
  rw [h, he, one_smul]

theorem normV_of_isoPtOK {v : List ℕ} (h : isoPtOK v = true) :
    NormV (decV v) ∧ v.length = 3 ∧ ∀ x ∈ v, x < 25 := by
  unfold isoPtOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hl, ha⟩, hf⟩, -⟩ := h
  refine ⟨?_, hl, ha⟩
  match v, hl with
  | [a, b, d], _ =>
    simp only [firstNZL, lget, List.getD_cons_zero, List.getD_cons_succ] at hf
    unfold NormV
    by_cases ha0 : a = 0
    · subst ha0
      rw [if_neg (by simp)] at hf
      by_cases hb0 : b = 0
      · subst hb0
        rw [if_neg (by simp)] at hf
        subst hf
        exact Or.inr (Or.inr ⟨dec_zero, dec_zero, dec_one⟩)
      · rw [if_pos hb0] at hf
        subst hf
        exact Or.inr (Or.inl ⟨dec_zero, dec_one⟩)
    · rw [if_pos ha0] at hf
      subst hf
      exact Or.inl dec_one

theorem decV_inj {v w : List ℕ} (hv : v.length = 3) (hw : w.length = 3) (hv' : ∀ x ∈ v, x < 25)
    (hw' : ∀ x ∈ w, x < 25) (h : decV v = decV w) : v = w := by
  match v, w, hv, hw with
  | [a, b, d], [a', b', d'], _, _ =>
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [decV, lget] at h0 h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hv' hw'
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, List.getD_cons_zero,
      List.getD_cons_succ] at h0 h1 h2
    rw [dec_injOn a hv'.1 a' hw'.1 h0, dec_injOn b hv'.2.1 b' hw'.2.1 h1,
      dec_injOn d hv'.2.2 d' hw'.2.2 h2]

theorem nodup_of_distinctL : ∀ {L : List (List ℕ)}, distinctL L = true → L.Nodup
  | [], _ => List.nodup_nil
  | v :: vs, h => by
    simp [distinctL] at h
    exact List.nodup_cons.2 ⟨h.1, nodup_of_distinctL h.2⟩

variable (X : List (List ℕ))

@[expose] def pt (i : Fin 126) : Fin 3 → F25 := decV (X.getD i [])

variable {X}

theorem pt_facts (hX : ptsOK X = true) :
    (∀ i, NormV (pt X i)) ∧ Function.Injective (pt X) := by
  unfold ptsOK at hX
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hX
  obtain ⟨⟨hl, hall⟩, hd⟩ := hX
  have hget : ∀ i : Fin 126, X.getD i [] = X[(i : ℕ)]'(by rw [hl]; exact i.2) := fun i => by
    rw [List.getD_eq_getElem]
  have hok : ∀ i : Fin 126, isoPtOK (X.getD i []) = true := fun i => by
    rw [hget i]
    exact hall _ (List.getElem_mem _)
  refine ⟨fun i => (normV_of_isoPtOK (hok i)).1, fun i j hij => ?_⟩
  have hi := normV_of_isoPtOK (hok i)
  have hj := normV_of_isoPtOK (hok j)
  have he := decV_inj hi.2.1 hj.2.1 hi.2.2 hj.2.2 hij
  rw [hget i, hget j] at he
  exact Fin.ext ((nodup_of_distinctL hd).getElem_inj_iff.1 he)

variable (X) in
@[expose] def Moves (r : Equiv.Perm (Fin 126)) (M : Matrix (Fin 3) (Fin 3) F25) : Prop :=
  ∀ i, ∃ c : F25, pt X (r i) = c • (M *ᵥ pt X i)

theorem moves_one : Moves X 1 1 := fun i => ⟨1, by simp⟩

theorem moves_mul {r s : Equiv.Perm (Fin 126)} {M N : Matrix (Fin 3) (Fin 3) F25}
    (h1 : Moves X r M) (h2 : Moves X s N) : Moves X (r * s) (M * N) := by
  intro i
  obtain ⟨d, hd⟩ := h2 i
  obtain ⟨c, hc⟩ := h1 (s i)
  refine ⟨c * d, ?_⟩
  rw [Equiv.Perm.mul_apply, hc, hd, Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec]

theorem moves_of_actOK {M : List ℕ} {g : ℕ → ℕ} (h : actOK M X g = true)
    {r : Equiv.Perm (Fin 126)} (hr : ∀ i : Fin 126, (r i : ℕ) = g i) :
    Moves X r (decMat (lget M)) := by
  intro i
  obtain ⟨c, hc⟩ := act_of_actOK h i.2
  exact ⟨c, by rw [pt, hr i]; exact hc⟩

theorem decMat_lget_uCode : decMat (lget uCode.toList) = Umat := by
  ext r s
  fin_cases r <;> fin_cases s <;> decide +kernel

theorem decMat_lget_vCode : decMat (lget vCode.toList) = Vmat := by
  ext r s
  fin_cases r <;> fin_cases s <;> decide +kernel

theorem moves_of_mem {rA rB : Equiv.Perm (Fin 126)} (hA : Moves X rA Umat) (hB : Moves X rB Vmat)
    {w : Equiv.Perm (Fin 126) × SU3}
    (hw : w ∈ Subgroup.closure ({(rA, UU), (rB, VV)} : Set (Equiv.Perm (Fin 126) × SU3))) :
    Moves X w.1 (((w.2 : SU3) : Matrix.GeneralLinearGroup (Fin 3) F25) :
      Matrix (Fin 3) (Fin 3) F25) := by
  have hm := mem_submonoidClosure_of_mem_closure hw
  refine Submonoid.closure_induction_left
    (motive := fun w _ => Moves X w.1 (((w.2 : SU3) : Matrix.GeneralLinearGroup (Fin 3) F25) :
      Matrix (Fin 3) (Fin 3) F25)) ?_ ?_ hm
  · exact moves_one
  · intro x hx y _ ih
    rcases hx with rfl | hx
    · exact moves_mul hA ih
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact moves_mul hB ih

theorem perm_eq_one_of_scalar (hX : ptsOK X = true) {r : Equiv.Perm (Fin 126)}
    {M : Matrix (Fin 3) (Fin 3) F25} (h : Moves X r M) {u : F25}
    (hs : M = u • (1 : Matrix (Fin 3) (Fin 3) F25)) : r = 1 := by
  obtain ⟨hn, hinj⟩ := pt_facts hX
  ext i
  obtain ⟨c, hc⟩ := h i
  rw [hs, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul] at hc
  exact congrArg Fin.val (hinj (eq_of_eq_smul (hn _) (hn _) hc))

theorem nonempty_mulEquiv_psu3_of_checks
    {pA pB : Equiv.Perm (Fin 50)} {rA rB : Equiv.Perm (Fin 126)} {hA hB : Equiv.Perm (Fin (50 + 126))}
    (eA : hA = emb (pA, rA)) (eB : hB = emb (pB, rB))
    (cH : Nat.card (Subgroup.closure ({hA, hB} : Set (Equiv.Perm (Fin (50 + 126))))) = 126000)
    (cP : Nat.card (Subgroup.closure ({pA, pB} : Set (Equiv.Perm (Fin 50)))) = 126000)
    (cR : Nat.card (Subgroup.closure ({rA, rB} : Set (Equiv.Perm (Fin 126)))) = 126000)
    (hX : ptsOK X = true) (mA : Moves X rA Umat) (mB : Moves X rB Vmat) :
    Nonempty (Subgroup.closure ({pA, pB} : Set (Equiv.Perm (Fin 50))) ≃* PSU3) := by
  have hD : (Subgroup.closure ({(pA, rA), (pB, rB)} :
      Set (Equiv.Perm (Fin 50) × Equiv.Perm (Fin 126)))).map emb =
      Subgroup.closure ({hA, hB} : Set (Equiv.Perm (Fin (50 + 126)))) := by
    rw [MonoidHom.map_closure, Set.image_pair, eA, eB]
  have cD : Nat.card (Subgroup.closure ({(pA, rA), (pB, rB)} :
      Set (Equiv.Perm (Fin 50) × Equiv.Perm (Fin 126)))) = 126000 := by
    rw [← Subgroup.card_map_of_injective emb_injective, hD, cH]
  obtain ⟨ePR⟩ := nonempty_mulEquiv_closure_of_kernels pA pB rA rB
    (snd_eq_one_of_card_le _ _ _ _ (by rw [cD, cP])) (fst_eq_one_of_card_le _ _ _ _ (by rw [cD, cR]))
  have hΓ : Subgroup.closure ({(rA, projPSU UU), (rB, projPSU VV)} :
      Set (Equiv.Perm (Fin 126) × PSU3)) =
      (Subgroup.closure ({(rA, UU), (rB, VV)} : Set (Equiv.Perm (Fin 126) × SU3))).map
        (MonoidHom.prodMap (MonoidHom.id _) projPSU) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have k2 : ∀ w ∈ Subgroup.closure ({(rA, projPSU UU), (rB, projPSU VV)} :
      Set (Equiv.Perm (Fin 126) × PSU3)), w.2 = 1 → w.1 = 1 := by
    rw [hΓ]
    rintro _ ⟨w, hw, rfl⟩ h2
    have h2' : w.2 ∈ (StatedScalars (Fin 3) F25).subgroupOf SU3 :=
      (QuotientGroup.eq_one_iff _).mp h2
    obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.mp h2'
    exact perm_eq_one_of_scalar hX (moves_of_mem mA mB hw) (u := (u : F25))
      (by rw [← hu, scalar_coe])
  have hinj : Function.Injective ((MonoidHom.snd _ _).comp
      (Subgroup.closure ({(rA, projPSU UU), (rB, projPSU VV)} :
        Set (Equiv.Perm (Fin 126) × PSU3))).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨w, hw⟩ h
    have h2 : w.2 = 1 := h
    exact Subtype.ext (Prod.ext (k2 w hw h2) h2)
  have cΓ : Nat.card (Subgroup.closure ({(rA, projPSU UU), (rB, projPSU VV)} :
      Set (Equiv.Perm (Fin 126) × PSU3))) ≤ Nat.card (Subgroup.closure ({rA, rB} :
        Set (Equiv.Perm (Fin 126)))) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, snd_closure_pair, cR, ← card_PSU3]
    exact Subgroup.card_le_card_group _
  obtain ⟨eRQ⟩ := nonempty_mulEquiv_closure_of_kernels rA rB (projPSU UU) (projPSU VV)
    (snd_eq_one_of_card_le _ _ _ _ cΓ) k2
  have hQ : Subgroup.closure ({projPSU UU, projPSU VV} : Set PSU3) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [card_PSU3, ← Nat.card_congr eRQ.toEquiv, cR]
  exact ⟨ePR.trans (eRQ.trans ((MulEquiv.subgroupCongr hQ).trans Subgroup.topEquiv))⟩

@[expose] def LRep (l : List ℕ) (g : Equiv.Perm (Fin 50)) : Prop :=
  l.length = 50 ∧ ∀ x : Fin 50, lget l x = g x

theorem lget_map (f : ℕ → ℕ) {q : List ℕ} {x : ℕ} (hx : x < q.length) :
    lget (q.map f) x = f (lget q x) := by
  simp [lget, List.getElem?_eq_getElem hx]

theorem LRep.unique {l : List ℕ} {g h : Equiv.Perm (Fin 50)} (hg : LRep l g) (hh : LRep l h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg.2 x).symm.trans (hh.2 x))

theorem lrep_range : LRep (List.range 50) 1 :=
  ⟨by simp, fun x => by simp [lget, List.getElem?_range x.2]⟩

theorem lrep_compL {p q : List ℕ} {g h : Equiv.Perm (Fin 50)} (hp : LRep p g) (hq : LRep q h) :
    LRep (compL p q) (g * h) := by
  refine ⟨by simp [compL, hq.1], fun x => ?_⟩
  rw [compL, lget_map _ (by rw [hq.1]; exact x.2), hq.2 x, hp.2 (h x), Equiv.Perm.mul_apply]

theorem lrep_foldr {α : Type*} (f : α → List ℕ) (gs : α → Equiv.Perm (Fin 50)) :
    ∀ L : List α, (∀ a ∈ L, LRep (f a) (gs a)) →
      LRep (L.foldr (fun a acc => compL (f a) acc) (List.range 50)) (L.map gs).prod
  | [], _ => by simpa using lrep_range
  | a :: L, h => by
    rw [List.foldr_cons, List.map_cons, List.prod_cons]
    exact lrep_compL (h a List.mem_cons_self)
      (lrep_foldr f gs L fun b hb => h b (List.mem_cons_of_mem a hb))

theorem lrep_of_isListL {g : ℕ → ℕ} {l : List ℕ} (h : isListL g l = true) (hl : l.length = 50)
    {p : Equiv.Perm (Fin 50)} (hp : ∀ x : Fin 50, g x = p x) : LRep l p := by
  refine ⟨hl, fun x => ?_⟩
  unfold isListL at h
  rw [beq_iff_eq] at h
  have hx : (x : ℕ) < (List.range l.length).length := by
    rw [List.length_range, hl]
    exact x.2
  have hx' : (x : ℕ) < l.length := by
    rw [hl]
    exact x.2
  rw [← h, lget_map _ hx, ← hp x]
  congr 1
  simp [lget, List.getElem?_range hx']

theorem smallPerms_get {k : ℕ} (hk : k < 6) (x : ℕ) :
    (smallPerms[k]!)[x]! = lget (smallL k) x := by
  have hs : smallPermLists.size = 6 := rfl
  have hk' : k < smallPermLists.size := by rw [hs]; exact hk
  have e1 : smallPerms[k]! = (smallPermLists[k]'hk').toArray := by
    rw [smallPerms, getElem!_pos _ k (by simpa using hk'), Array.getElem_map]
  have e2 : smallL k = smallPermLists[k]'hk' := by
    rw [smallL, List.getD_eq_getElem _ _ (by simpa using hk'), Array.getElem_toList]
  rw [e1, e2, lget]
  simp only [getElem!_def, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  cases (smallPermLists[k]'hk')[x]? <;> rfl

theorem wordB_lt : ∀ k ∈ wordB, k < 6 := by decide

theorem closure_smallPerms_eq (hw : wordsOKL = true) {pA pB : Equiv.Perm (Fin 50)}
    (hA : LRep sigmaAL pA) (hB : LRep sigmaBL pB) :
    Subgroup.closure (Set.range fun k : Fin 6 => permOfArr 50 smallPerms[(k : ℕ)]!) =
      Subgroup.closure ({pA, pB} : Set (Equiv.Perm (Fin 50))) := by
  have hAB : ∀ b : Bool, LRep (if b then sigmaBL else sigmaAL) (if b then pB else pA) := by
    intro b
    cases b
    · exact hA
    · exact hB
  have hword : ∀ k < 6, LRep (smallL k)
      ((wordsAB.getD k []).map fun b => if b then pB else pA).prod := by
    intro k hk
    have h := List.all_eq_true.1 hw k (List.mem_range.2 hk)
    rw [beq_iff_eq] at h
    rw [← h]
    exact lrep_foldr _ _ _ fun b _ => hAB b
  have hs : ∀ k < 6, permOfArr 50 smallPerms[k]! =
      ((wordsAB.getD k []).map fun b => if b then pB else pA).prod := by
    intro k hk
    refine CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep fun x => ?_
    rw [smallPerms_get hk]
    exact (hword k hk).2 x
  have hsL : ∀ k < 6, LRep (smallL k) (permOfArr 50 smallPerms[k]!) := fun k hk => by
    rw [hs k hk]
    exact hword k hk
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe]
    rw [hs k k.2]
    apply Subgroup.list_prod_mem
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨b, -, rfl⟩ := hy
    cases b
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    have hmem : ∀ k < 6, permOfArr 50 smallPerms[k]! ∈ Subgroup.closure
        (Set.range fun k : Fin 6 => permOfArr 50 smallPerms[(k : ℕ)]!) :=
      fun k hk => Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩
    intro y hy
    rcases hy with rfl | hy
    · rw [LRep.unique hA (hsL 0 (by norm_num))]
      exact hmem 0 (by norm_num)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      have hb := lrep_foldr smallL (fun k => permOfArr 50 smallPerms[k]!) wordB
        fun k hk => hsL k (wordB_lt k hk)
      rw [LRep.unique hB hb]
      apply Subgroup.list_prod_mem
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      exact hmem k (wordB_lt k hk)

end CFSG.KC.HN14969

end
