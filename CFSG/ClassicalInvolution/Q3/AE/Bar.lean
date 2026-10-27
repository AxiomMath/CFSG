module

public import CFSG.ClassicalInvolution.Q3.AE.Group

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem supportedOn_one (s : Set (Fin n)) : SupportedOn (1 : Wr n) s :=
  fun _ _ => ⟨rfl, rfl⟩

theorem SupportedOn.mul {a b : Wr n} {s : Set (Fin n)} (ha : SupportedOn a s)
    (hb : SupportedOn b s) : SupportedOn (a * b) s := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [mul_vec, (ha x hx).1, ha.perm_symm hx, (hb x hx).1, add_zero]
  · show a.perm (b.perm x) = x
    rw [(hb x hx).2, (ha x hx).2]

theorem SupportedOn.inv {a : Wr n} {s : Set (Fin n)} (ha : SupportedOn a s) :
    SupportedOn a⁻¹ s := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [inv_vec, (ha x hx).2, (ha x hx).1]
  · show a.perm⁻¹ x = x
    rw [Equiv.Perm.inv_def]
    exact ha.perm_symm hx

theorem ne_allOnes_of_supportedOn (hn : 5 ≤ n) {ι : Fin 4 ↪ Fin n} {a : Wr n}
    (ha : SupportedOn a (Set.range ι)) : a ≠ allOnes n := by
  classical
  intro h
  have hlt : (Finset.univ.map ι).card < (Finset.univ : Finset (Fin n)).card := by
    rw [card_map_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hx' : x ∉ Set.range ι := by
    rw [range_eq_finset]
    exact_mod_cast hx
  have h1 := (ha x hx').1
  rw [h] at h1
  exact absurd (show (1 : ZMod 2) = 0 from h1) (by decide)

theorem mkQ_inj_of_supportedOn (hn : 5 ≤ n) {ι : Fin 4 ↪ Fin n} {a b : Wr n}
    (ha : SupportedOn a (Set.range ι)) (hb : SupportedOn b (Set.range ι))
    (h : mkQ n a = mkQ n b) : a = b := by
  rcases mkQ_eq_iff.mp h with h1 | h1
  · exact inv_mul_eq_one.mp h1
  · exact absurd h1 (ne_allOnes_of_supportedOn hn (ha.inv.mul hb))

theorem comm_of_mkQ_comm_of_supportedOn (hn : 5 ≤ n) {ι : Fin 4 ↪ Fin n} {a b : Wr n}
    (ha : SupportedOn a (Set.range ι)) (hb : SupportedOn b (Set.range ι))
    (h : mkQ n a * mkQ n b = mkQ n b * mkQ n a) : a * b = b * a := by
  rw [← map_mul, ← map_mul] at h
  exact mkQ_inj_of_supportedOn hn (ha.mul hb) (hb.mul ha) h

@[expose] noncomputable def memAt (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    Subgroup (Wr n) :=
  bif b then memK (emb α h) else memKStar (emb α h)

@[expose] noncomputable def memBar (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    Subgroup (AEQ n) :=
  (memAt α h b).map (mkQ n)

@[expose] noncomputable def zBar (α : Finset (Fin n)) (h : α.card = 4) : AEQ n :=
  mkQ n (zOf (emb α h))

theorem supportedOn_of_mem_memAt {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} {a : Wr n}
    (ha : a ∈ memAt α h b) : SupportedOn a (Set.range (emb α h)) := by
  cases b
  · exact supportedOn_of_mem_memKStar _ ha
  · exact supportedOn_of_mem_memK _ ha

theorem zOf_mem_memAt (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    zOf (emb α h) ∈ memAt α h b := by
  cases b
  · exact zOf_mem_memKStar _
  · exact zOf_mem_memK _

theorem zOf_supportedOn (ι : Fin 4 ↪ Fin n) : SupportedOn (zOf ι) (Set.range ι) :=
  embed_supportedOn ι zQ

theorem zOf_ne_one (ι : Fin 4 ↪ Fin n) : zOf ι ≠ 1 := by
  intro h
  have h1 := congrFun (congrArg Wr.vec h) (ι 0)
  rw [zOf_vec_apply] at h1
  simp only [Set.mem_range_self, ite_true] at h1
  exact absurd (show (1 : ZMod 2) = 0 from h1) (by decide)

theorem zBar_ne_one (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4) : zBar α h ≠ 1 := by
  intro h1
  rw [zBar, ← (mkQ n).map_one] at h1
  exact zOf_ne_one _ (mkQ_inj_of_supportedOn hn (zOf_supportedOn _) (supportedOn_one _) h1)

theorem natCard_memAt (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    Nat.card (memAt α h b) = 8 := by
  cases b
  · exact natCard_memKStar _
  · exact natCard_memK _

theorem natCard_memBar (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    Nat.card (memBar α h b) = 8 := by
  have hinj : Set.InjOn (mkQ n) (memAt α h b : Set (Wr n)) := fun a ha a' ha' heq =>
    mkQ_inj_of_supportedOn hn (supportedOn_of_mem_memAt ha) (supportedOn_of_mem_memAt ha') heq
  have h1 : Nat.card ↥(memBar α h b) = Nat.card ↑((mkQ n) '' (memAt α h b : Set (Wr n))) := by
    rw [memBar, ← Subgroup.coe_map]
    rfl
  rw [h1, Nat.card_image_of_injOn hinj]
  exact natCard_memAt α h b

theorem zBar_mem_memBar (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    zBar α h ∈ memBar α h b :=
  ⟨_, zOf_mem_memAt α h b, rfl⟩

theorem eq_of_mem_memAt_mul_self {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} {a : Wr n}
    (ha : a ∈ memAt α h b) (h2 : a * a = 1) : a = 1 ∨ a = zOf (emb α h) := by
  cases b
  · exact eq_of_mem_memKStar_mul_self _ a ha h2
  · exact eq_of_mem_memK_mul_self _ a ha h2

theorem eq_of_mem_memBar_mul_self (hn : 5 ≤ n) {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    {x : AEQ n} (hx : x ∈ memBar α h b) (h2 : x * x = 1) : x = 1 ∨ x = zBar α h := by
  obtain ⟨a, ha, rfl⟩ := hx
  have hs := supportedOn_of_mem_memAt ha
  have h3 : a * a = 1 := by
    rw [← map_mul, ← (mkQ n).map_one] at h2
    exact mkQ_inj_of_supportedOn hn (hs.mul hs) (supportedOn_one _) h2
  rcases eq_of_mem_memAt_mul_self ha h3 with h4 | h4
  · left
    rw [h4, map_one]
  · right
    rw [h4]
    rfl

theorem comm_memBar_of_disjoint {α β : Finset (Fin n)} {h : α.card = 4} {h' : β.card = 4}
    (hd : Disjoint α β) (b c : Bool) :
    ∀ x ∈ memBar α h b, ∀ y ∈ memBar β h' c, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  refine comm_of_disjoint (supportedOn_of_mem_memAt ha) (supportedOn_of_mem_memAt ha') ?_
  rw [range_emb, range_emb]
  exact_mod_cast hd

@[expose] noncomputable def yBar (α : Finset (Fin n)) (h : α.card = 4) : AEQ n :=
  mkQ n (yOf (emb α h))

theorem yBar_mem (α : Finset (Fin n)) (h : α.card = 4) : yBar α h ∈ (aeSub n).map (mkQ n) :=
  ⟨_, yOf_mem_aeSub _, rfl⟩

theorem yBar_pow_three (α : Finset (Fin n)) (h : α.card = 4) : yBar α h ^ 3 = 1 := by
  rw [yBar, ← map_pow, pow_three, ← mul_assoc, yOf_pow_three, map_one]

theorem yBar_comm_zBar (α : Finset (Fin n)) (h : α.card = 4) :
    yBar α h * zBar α h = zBar α h * yBar α h := by
  rw [yBar, zBar, ← map_mul, ← map_mul, yOf_comm_zOf]

theorem yBar_conj_mem_memBar (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∀ x ∈ memBar α h b, yBar α h * x * (yBar α h)⁻¹ ∈ memBar α h b := by
  rintro _ ⟨a, ha, rfl⟩
  have : yOf (emb α h) * a * (yOf (emb α h))⁻¹ ∈ memAt α h b := by
    cases b
    · exact yOf_conj_mem_memKStar _ a ha
    · exact yOf_conj_mem_memK _ a ha
  refine ⟨_, this, ?_⟩
  rw [yBar, map_mul, map_mul, map_inv]

theorem yBar_not_comm_memBar (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∃ x ∈ memBar α h b, yBar α h * x ≠ x * yBar α h := by
  obtain ⟨a, ha, hne⟩ : ∃ a ∈ memAt α h b, yOf (emb α h) * a ≠ a * yOf (emb α h) := by
    cases b
    · exact yOf_not_comm_memKStar _
    · exact yOf_not_comm_memK _
  refine ⟨mkQ n a, ⟨a, ha, rfl⟩, fun h1 => hne ?_⟩
  exact comm_of_mkQ_comm_of_supportedOn hn (yOf_supportedOn _) (supportedOn_of_mem_memAt ha) h1

theorem yBar_comm_memBar_of_disjoint {α β : Finset (Fin n)} {h : α.card = 4} {h' : β.card = 4}
    (hd : Disjoint α β) (c : Bool) : ∀ y ∈ memBar β h' c, yBar α h * y = y * yBar α h := by
  rintro _ ⟨a', ha', rfl⟩
  rw [yBar, ← map_mul, ← map_mul]
  congr 1
  refine comm_of_disjoint (yOf_supportedOn _) (supportedOn_of_mem_memAt ha') ?_
  rw [range_emb, range_emb]
  exact_mod_cast hd

theorem eq_of_zBar_eq (hn8 : n ≠ 8) {α β : Finset (Fin n)} {h : α.card = 4} {h' : β.card = 4}
    (he : zBar α h = zBar β h') : α = β := by
  have := range_eq_of_mkQ_zOf_eq hn8 he
  rw [range_emb, range_emb] at this
  exact_mod_cast this

theorem disjoint_of_zBar_comm {α β : Finset (Fin n)} {h : α.card = 4} {h' : β.card = 4}
    (hne : α ≠ β) {c : Bool} (hc : ∀ y ∈ memBar β h' c, zBar α h * y = y * zBar α h) :
    Disjoint α β := by
  classical
  by_contra hd
  rw [Finset.not_disjoint_iff] at hd
  obtain ⟨x, hxα, hxβ⟩ := hd
  have hne' : (Set.range (emb α h) ∩ Set.range (emb β h')).Nonempty :=
    ⟨x, by rw [range_emb]; exact_mod_cast hxα, by rw [range_emb]; exact_mod_cast hxβ⟩
  have hneq : Set.range (emb α h) ≠ Set.range (emb β h') := by
    rw [range_emb, range_emb]
    exact_mod_cast hne
  cases c
  · obtain ⟨b, hb, hb'⟩ := not_comm_mkQ_zOf_memKStar hne' hneq
    exact hb' (hc _ ⟨b, hb, rfl⟩)
  · obtain ⟨b, hb, hb'⟩ := not_comm_mkQ_zOf_memK hne' hneq
    exact hb' (hc _ ⟨b, hb, rfl⟩)

theorem memBar_true_ne_false (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4) :
    memBar α h true ≠ memBar α h false := by
  intro heq
  have hmem : mkQ n (embed (emb α h) (⟨vec4 [0, 2], d₁⟩ : Wr 4)) ∈ memBar α h false := by
    rw [← heq]
    exact ⟨_, ⟨_, (by decide +kernel : (⟨vec4 [0, 2], d₁⟩ : Wr 4) ∈ kList), rfl⟩, rfl⟩
  obtain ⟨a, ha, h1⟩ := hmem
  have h2 := mkQ_inj_of_supportedOn hn (supportedOn_of_mem_memAt ha) (embed_supportedOn _ _) h1
  obtain ⟨a', ha', rfl⟩ := ha
  have h3 := embed_injective _ h2
  rw [h3] at ha'
  exact absurd ha' (by decide +kernel : (⟨vec4 [0, 2], d₁⟩ : Wr 4) ∉ kStarList)

@[expose] def vecSub (n : ℕ) : Subgroup (Wr n) where
  carrier := {a | a.perm = 1}
  mul_mem' {a b} ha hb := by
    show a.perm * b.perm = 1
    rw [show a.perm = 1 from ha, show b.perm = 1 from hb, one_mul]
  one_mem' := rfl
  inv_mem' {a} ha := by
    show a.perm⁻¹ = 1
    rw [show a.perm = 1 from ha, inv_one]

instance vecSub_normal : (vecSub n).Normal where
  conj_mem a ha g := by
    show (g * a * g⁻¹).perm = 1
    rw [mul_perm, mul_perm, show a.perm = 1 from ha, mul_one, inv_perm, mul_inv_cancel]

theorem vecSub_mul_self {a : Wr n} (ha : a ∈ vecSub n) : a * a = 1 := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [mul_vec, show a.perm = 1 from ha]
    exact zmod_two_add_self _
  · rw [mul_perm, show a.perm = 1 from ha, mul_one]
    rfl

theorem memAt_mul_vec (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∀ a ∈ memAt α h b, ∃ a' ∈ memAt α h (!b), a⁻¹ * a' ∈ vecSub n := by
  cases b
  · exact (memK_mul_vec _).2
  · exact (memK_mul_vec _).1

end CFSG.ClassicalInvolution.Q3.AE
