module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Brg
public import CFSG.ClassicalInvolution.Q3.AE.Models
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Pair

public section

namespace CFSG.KC.E64CCModel

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117
  CFSG.ClassicalInvolution.Q3.TL4.Mdl117

@[expose] def smulW (a : Wr 7) (p : ZMod 2 × Fin 7) : ZMod 2 × Fin 7 :=
  (p.1 + a.vec (a.perm p.2), a.perm p.2)

@[expose, instance_reducible] def actW : MulAction (Wr 7) (ZMod 2 × Fin 7) where
  smul := smulW
  one_smul p := by
    change (p.1 + (1 : Wr 7).vec ((1 : Wr 7).perm p.2), (1 : Wr 7).perm p.2) = p
    rw [one_vec, one_perm, Equiv.Perm.one_apply, Pi.zero_apply, add_zero]
  mul_smul a b p := by
    change ((p.1 + (a * b).vec ((a * b).perm p.2), (a * b).perm p.2) : ZMod 2 × Fin 7) =
      (p.1 + b.vec (b.perm p.2) + a.vec (a.perm (b.perm p.2)), a.perm (b.perm p.2))
    rw [mul_vec, mul_perm, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
    refine Prod.ext ?_ rfl
    change p.1 + (a.vec (a.perm (b.perm p.2)) + b.vec (b.perm p.2)) =
      p.1 + b.vec (b.perm p.2) + a.vec (a.perm (b.perm p.2))
    ring

@[expose] def eP : ZMod 2 × Fin 7 ≃ Fin 14 := finProdFinEquiv

@[expose] def phi : Wr 7 →* Equiv.Perm (Fin 14) :=
  eP.permCongrHom.toMonoidHom.comp (@MulAction.toPermHom (Wr 7) (ZMod 2 × Fin 7) _ actW)

theorem phi_apply (a : Wr 7) (x : Fin 14) : phi a x = eP (smulW a (eP.symm x)) := rfl

theorem phi_injective : Function.Injective phi := by
  intro a b h
  have hs : ∀ p, smulW a p = smulW b p := fun p => by
    have := congrArg (fun f => f (eP p)) h
    simpa only [phi_apply, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq] using this
  have hp : a.perm = b.perm := Equiv.ext fun j => congrArg Prod.snd (hs (0, j))
  refine Wr.ext (funext fun i => ?_) hp
  obtain ⟨j, rfl⟩ := a.perm.surjective i
  have := congrArg Prod.fst (hs (0, j))
  simp only [smulW, zero_add] at this
  rw [this, hp]

@[expose] def cpl : Fin 7 → Fin 4 → Fin 7 :=
  ![![2, 4, 5, 6], ![0, 3, 5, 6], ![0, 1, 4, 6], ![0, 1, 2, 5], ![1, 2, 3, 6], ![0, 2, 3, 4],
    ![1, 3, 4, 5]]

@[expose] def lineOf (g : ℕ) : Fin 7 := ⟨g / 4 % 7, Nat.mod_lt _ (by norm_num)⟩

@[expose] def eW (g : ℕ) : Wr 7 :=
  (memLC (cpl (lineOf g) 0) (cpl (lineOf g) 1) (cpl (lineOf g) 2) (cpl (lineOf g) 3)
    (g / 2 % 2 == 0)).getD (2 + 2 * (g % 2)) 1

theorem sort_cpl (l : Fin 7) :
    (fanoLines.get ⟨l, by simp [fanoLines]⟩)ᶜ.sort (· ≤ ·) = List.ofFn (cpl l) := by
  have hn : (List.ofFn (cpl l)).Nodup := by revert l; decide
  have hp : (List.ofFn (cpl l)).Pairwise (· ≤ ·) := by revert l; decide
  have hs : (fanoLines.get ⟨l, by simp [fanoLines]⟩)ᶜ = (List.ofFn (cpl l)).toFinset := by
    revert l; decide
  rw [hs]
  exact (List.toFinset_sort (· ≤ ·) hn).2 hp

theorem emb_cpl (l : Fin 7) (h : (fanoLines.get ⟨l, by simp [fanoLines]⟩)ᶜ.card = 4) (i : Fin 4) :
    emb _ h i = cpl l i := by
  have e := (sort_eq _ h).symm.trans (sort_cpl l)
  fin_cases i
  · exact congrArg (fun L => L.getD 0 0) e
  · exact congrArg (fun L => L.getD 1 0) e
  · exact congrArg (fun L => L.getD 2 0) e
  · exact congrArg (fun L => L.getD 3 0) e

@[expose] def kE (b : Bool) (j : ℕ) : Wr 4 := (if b then kList else kStarList).getD (2 + 2 * j) 1

@[expose] def words3 : List (List Bool) :=
  [[], [false], [true], [false, false], [false, true], [true, false], [true, true],
    [false, false, false], [false, false, true], [false, true, false], [false, true, true],
    [true, false, false], [true, false, true], [true, true, false], [true, true, true]]

@[expose] def evB {G : Type*} [Monoid G] (x y : G) (w : List Bool) : G :=
  (w.map fun c => bif c then y else x).prod

theorem evB_mem {G : Type*} [Group G] {x y : G} (w : List Bool) :
    evB x y w ∈ Subgroup.closure ({x, y} : Set G) := by
  unfold evB
  refine list_prod_mem fun t ht => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 ht
  cases c
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem kList_words (b : Bool) :
    ∀ a ∈ (if b then kList else kStarList), ∃ w ∈ words3, a = evB (kE b 0) (kE b 1) w := by
  cases b <;> decide +kernel

theorem kQ_eq_closure (b : Bool) :
    (bif b then kQ else kQStar) = Subgroup.closure ({kE b 0, kE b 1} : Set (Wr 4)) := by
  refine le_antisymm (fun a ha => ?_) ((Subgroup.closure_le _).2 ?_)
  · have ha' : a ∈ (if b then kList else kStarList) := by cases b <;> exact ha
    obtain ⟨w, -, rfl⟩ := kList_words b a ha'
    exact evB_mem w
  · have h2 : kE b 0 ∈ (if b then kList else kStarList) := by cases b <;> decide +kernel
    have h4 : kE b 1 ∈ (if b then kList else kStarList) := by cases b <;> decide +kernel
    rintro x (rfl | rfl)
    · cases b
      · exact h2
      · exact h2
    · cases b
      · exact h4
      · exact h4

theorem memAt_eq_map (α : Finset (Fin 7)) (h : α.card = 4) (b : Bool) :
    memAt α h b = (bif b then kQ else kQStar).map (embed (emb α h)) := by
  cases b <;> rfl

theorem embed_kE (l : Fin 7) (h : (fanoLines.get ⟨l, by simp [fanoLines]⟩)ᶜ.card = 4)
    (b : Bool) (j : ℕ) :
    embed (emb _ h) (kE b j) =
      (memLC (cpl l 0) (cpl l 1) (cpl l 2) (cpl l 3) b).getD (2 + 2 * j) 1 := by
  have e := memLC_eq (emb _ h) b
  rw [emb_cpl l h 0, emb_cpl l h 1, emb_cpl l h 2, emb_cpl l h 3] at e
  rw [e, ← map_one (embed (emb _ h)), List.getD_map, kE]

theorem memAt_eq_closure (l : Fin 7) (h : (fanoLines.get ⟨l, by simp [fanoLines]⟩)ᶜ.card = 4)
    (b : Bool) :
    memAt _ h b = Subgroup.closure ({eW (4 * l.val + 2 * (bif b then 0 else 1)),
      eW (4 * l.val + 2 * (bif b then 0 else 1) + 1)} : Set (Wr 7)) := by
  rw [memAt_eq_map, kQ_eq_closure, MonoidHom.map_closure, Set.image_pair, embed_kE, embed_kE]
  have hl7 := l.isLt
  have e0 : eW (4 * l.val + 2 * (bif b then 0 else 1)) =
      (memLC (cpl l 0) (cpl l 1) (cpl l 2) (cpl l 3) b).getD (2 + 2 * 0) 1 := by
    have hl : lineOf (4 * l.val + 2 * (bif b then 0 else 1)) = l :=
      Fin.ext (by cases b <;> simp [lineOf] <;> omega)
    have hb : ((4 * l.val + 2 * (bif b then 0 else 1)) / 2 % 2 == 0) = b := by
      cases b <;> simp <;> omega
    have h0 : (4 * l.val + 2 * (bif b then 0 else 1)) % 2 = 0 := by cases b <;> simp <;> omega
    rw [eW, hl, hb, h0]
  have e1 : eW (4 * l.val + 2 * (bif b then 0 else 1) + 1) =
      (memLC (cpl l 0) (cpl l 1) (cpl l 2) (cpl l 3) b).getD (2 + 2 * 1) 1 := by
    have hl : lineOf (4 * l.val + 2 * (bif b then 0 else 1) + 1) = l :=
      Fin.ext (by cases b <;> simp [lineOf] <;> omega)
    have hb : ((4 * l.val + 2 * (bif b then 0 else 1) + 1) / 2 % 2 == 0) = b := by
      cases b <;> simp <;> omega
    have h1 : (4 * l.val + 2 * (bif b then 0 else 1) + 1) % 2 = 1 := by
      cases b <;> simp <;> omega
    rw [eW, hl, hb, h1]
  rw [e0, e1]

end CFSG.KC.E64CCModel

end
