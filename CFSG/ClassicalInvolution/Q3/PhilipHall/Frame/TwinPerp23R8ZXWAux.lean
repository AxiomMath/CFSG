module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoWr
public import CFSG.ClassicalInvolution.Sp62Rec.I1.WrModel
public import CFSG.ClassicalInvolution.Solomon73
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZXW

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Solomon73

section Local

@[expose] def bList : List (Wr 4) :=
  [⟨vec4 [], 1⟩, ⟨vec4 [], Equiv.swap 0 1⟩, ⟨vec4 [], Equiv.swap 2 3⟩,
    ⟨vec4 [], Equiv.swap 0 1 * Equiv.swap 2 3⟩,
    ⟨vec4 [0, 1], 1⟩, ⟨vec4 [0, 1], Equiv.swap 0 1⟩, ⟨vec4 [0, 1], Equiv.swap 2 3⟩,
    ⟨vec4 [0, 1], Equiv.swap 0 1 * Equiv.swap 2 3⟩,
    ⟨vec4 [2, 3], 1⟩, ⟨vec4 [2, 3], Equiv.swap 0 1⟩, ⟨vec4 [2, 3], Equiv.swap 2 3⟩,
    ⟨vec4 [2, 3], Equiv.swap 0 1 * Equiv.swap 2 3⟩,
    ⟨vec4 [0, 1, 2, 3], 1⟩, ⟨vec4 [0, 1, 2, 3], Equiv.swap 0 1⟩,
    ⟨vec4 [0, 1, 2, 3], Equiv.swap 2 3⟩, ⟨vec4 [0, 1, 2, 3], Equiv.swap 0 1 * Equiv.swap 2 3⟩]

theorem bList_mul : ∀ a ∈ bList, ∀ b ∈ bList, a * b ∈ bList := by decide +kernel

theorem bList_inv : ∀ a ∈ bList, a⁻¹ ∈ bList := by decide +kernel

theorem one_mem_bList : (1 : Wr 4) ∈ bList := by decide +kernel

@[expose] def bQ : Subgroup (Wr 4) where
  carrier := {a | a ∈ bList}
  mul_mem' {a b} ha hb := bList_mul a ha b hb
  one_mem' := one_mem_bList
  inv_mem' {a} ha := bList_inv a ha

theorem mem_bQ {a : Wr 4} : a ∈ bQ ↔ a ∈ bList := Iff.rfl

theorem bList_comm : ∀ a ∈ bList, ∀ b ∈ bList, a * b = b * a := by decide +kernel

theorem bList_sq : ∀ a ∈ bList, a * a = 1 := by decide +kernel

theorem bList_conj_kList : ∀ k ∈ kList, ∀ a ∈ bList, k * a * k⁻¹ ∈ bList := by decide +kernel

theorem bList_conj_kStarList : ∀ k ∈ kStarList, ∀ a ∈ bList, k * a * k⁻¹ ∈ bList := by
  decide +kernel

theorem zQ_mem_bList : zQ ∈ bList := by decide +kernel

theorem bList_sum : ∀ a ∈ bList, (∑ i, a.vec i) = 0 := by decide +kernel

theorem bList_nodup : bList.Nodup := by decide +kernel

theorem natCard_bQ : Nat.card bQ = 16 := by
  classical
  have h1 : Nat.card bQ = (bQ : Set (Wr 4)).ncard := Nat.card_coe_set_eq _
  have h2 : (bQ : Set (Wr 4)) = ↑bList.toFinset := by
    ext a
    simp [mem_bQ]
  rw [h1, h2, Set.ncard_coe_finset, List.toFinset_card_of_nodup bList_nodup]
  rfl

end Local

section CHat

variable {β : Finset (Fin 6)}

@[expose] def cHat (β : Finset (Fin 6)) (hβ : β.card = 4) : Subgroup (Wr 6) where
  carrier := {c | SupportedOn c (Set.range (emb β hβ))ᶜ ∧ wsum c = 0}
  mul_mem' {a b} ha hb := ⟨ha.1.mul hb.1, by rw [wsum_mul, ha.2, hb.2, add_zero]⟩
  one_mem' := ⟨supportedOn_one _, wsum_one⟩
  inv_mem' {a} ha := ⟨ha.1.inv, by rw [wsum_inv]; exact ha.2⟩

theorem mem_cHat {hβ : β.card = 4} {c : Wr 6} :
    c ∈ cHat β hβ ↔ SupportedOn c (Set.range (emb β hβ))ᶜ ∧ wsum c = 0 := Iff.rfl

theorem cHat_spec {hβ : β.card = 4} {a a' : Fin 6} (haa' : a ≠ a') (ha : a ∉ β) (ha' : a' ∉ β)
    (hout : ∀ i, i ∉ β → i = a ∨ i = a') {c : Wr 6} (hc : c ∈ cHat β hβ) :
    (∀ x ∈ β, c.vec x = 0 ∧ c.perm x = x) ∧ (c.perm = 1 ∨ c.perm = Equiv.swap a a') ∧
      c.vec a = c.vec a' := by
  have h1 : ∀ x ∈ β, c.vec x = 0 ∧ c.perm x = x := by
    intro x hx
    apply hc.1 x
    rw [Set.mem_compl_iff, not_not, range_emb]
    exact hx
  refine ⟨h1, ZTwo.perm_dichotomy haa' ha ha' hout c.perm (fun x hx => (h1 x hx).2), ?_⟩
  have hsum : wsum c = c.vec a + c.vec a' := by
    unfold wsum
    rw [← Finset.sum_pair haa']
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    have hxβ : x ∈ β := by
      by_contra h
      rcases hout x h with rfl | rfl <;> simp at hx
    exact (h1 x hxβ).1
  have h2 := hc.2
  rw [hsum] at h2
  have key : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  exact key _ _ h2

theorem cHat_vec_perm {hβ : β.card = 4} {c d : Wr 6} (hc : c ∈ cHat β hβ)
    (hd : d ∈ cHat β hβ) (x : Fin 6) : d.vec (c.perm.symm x) = d.vec x := by
  obtain ⟨a, a', haa', ha, ha', hout⟩ := ZTwo.exists_compl_pair hβ
  obtain ⟨-, hcp, -⟩ := cHat_spec haa' ha ha' hout hc
  obtain ⟨-, -, hd3⟩ := cHat_spec haa' ha ha' hout hd
  rcases hcp with h | h
  · rw [h]
    rfl
  · rw [h, Equiv.symm_swap]
    by_cases hxa : x = a
    · subst hxa
      rw [Equiv.swap_apply_left, hd3]
    · by_cases hxa' : x = a'
      · subst hxa'
        rw [Equiv.swap_apply_right, hd3]
      · rw [Equiv.swap_apply_of_ne_of_ne hxa hxa']

theorem cHat_comm {hβ : β.card = 4} {c d : Wr 6} (hc : c ∈ cHat β hβ) (hd : d ∈ cHat β hβ) :
    c * d = d * c := by
  obtain ⟨a, a', haa', ha, ha', hout⟩ := ZTwo.exists_compl_pair hβ
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [mul_vec, mul_vec, cHat_vec_perm hc hd, cHat_vec_perm hd hc, add_comm]
  · rw [mul_perm, mul_perm]
    rcases (cHat_spec haa' ha ha' hout hc).2.1 with h | h <;>
      rcases (cHat_spec haa' ha ha' hout hd).2.1 with h' | h' <;> rw [h, h'] <;> simp

theorem cHat_sq {hβ : β.card = 4} {c : Wr 6} (hc : c ∈ cHat β hβ) : c * c = 1 := by
  obtain ⟨a, a', haa', ha, ha', hout⟩ := ZTwo.exists_compl_pair hβ
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [mul_vec, cHat_vec_perm hc hc]
    exact zmod_two_add_self _
  · rw [mul_perm, one_perm]
    rcases (cHat_spec haa' ha ha' hout hc).2.1 with h | h <;> rw [h]
    · exact mul_one 1
    · exact Equiv.swap_mul_self a a'

theorem natCard_cHat (hβ : β.card = 4) : Nat.card (cHat β hβ) = 4 := by
  classical
  obtain ⟨a, a', haa', ha, ha', hout⟩ := ZTwo.exists_compl_pair hβ
  set u : Fin 6 → ZMod 2 := fun x => if x = a ∨ x = a' then 1 else 0 with hu
  set s : Equiv.Perm (Fin 6) := Equiv.swap a a' with hs
  have hβr : ∀ x, x ∉ (Set.range (emb β hβ))ᶜ → x ∈ β := by
    intro x hx
    rw [Set.mem_compl_iff, not_not, range_emb] at hx
    exact hx
  have hxa : ∀ x ∈ β, x ≠ a := fun x hx h => ha (h ▸ hx)
  have hxa' : ∀ x ∈ β, x ≠ a' := fun x hx h => ha' (h ▸ hx)
  have hu0 : ∀ x ∈ β, u x = 0 := by
    intro x hx
    simp only [hu, hxa x hx, hxa' x hx, or_self, ite_false]
  have hs0 : ∀ x ∈ β, s x = x := fun x hx =>
    Equiv.swap_apply_of_ne_of_ne (hxa x hx) (hxa' x hx)
  have hua : u a = 1 := by simp [hu]
  have hua' : u a' = 1 := by simp [hu]
  have hsum : ∑ x, u x = 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ {a, a'}), Finset.sum_pair haa', hua, hua']
    · decide
    · intro x _ hx
      have hxβ : x ∈ β := by
        by_contra h
        rcases hout x h with rfl | rfl <;> simp at hx
      exact hu0 x hxβ
  have hmem1 : (⟨u, 1⟩ : Wr 6) ∈ cHat β hβ :=
    ⟨fun x hx => ⟨hu0 x (hβr x hx), rfl⟩, hsum⟩
  have hmem2 : (⟨0, s⟩ : Wr 6) ∈ cHat β hβ :=
    ⟨fun x hx => ⟨rfl, hs0 x (hβr x hx)⟩, by simp [wsum]⟩
  have hprod : (⟨u, 1⟩ : Wr 6) * ⟨0, s⟩ = ⟨u, s⟩ :=
    Wr.ext (funext fun x => by simp [mul_vec]) (by simp [mul_perm])
  have hmem3 : (⟨u, s⟩ : Wr 6) ∈ cHat β hβ := hprod ▸ (cHat β hβ).mul_mem hmem1 hmem2
  have hset : (cHat β hβ : Set (Wr 6)) = {1, ⟨u, 1⟩, ⟨0, s⟩, ⟨u, s⟩} := by
    ext c
    constructor
    · intro hc
      obtain ⟨h1, h2, h3⟩ := cHat_spec haa' ha ha' hout hc
      have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      have hvec : c.vec = 0 ∨ c.vec = u := by
        rcases hz (c.vec a) with h | h
        · left
          funext x
          by_cases hx : x ∈ β
          · exact (h1 x hx).1
          · rcases hout x hx with rfl | rfl
            · exact h
            · rw [← h3, h]
              rfl
        · right
          funext x
          by_cases hx : x ∈ β
          · rw [(h1 x hx).1, hu0 x hx]
          · rcases hout x hx with rfl | rfl
            · rw [h, hua]
            · rw [← h3, h, hua']
      rcases hvec with hv | hv <;> rcases h2 with hp | hp
      · left
        exact Wr.ext hv hp
      · right; right; left
        exact Wr.ext hv hp
      · right; left
        exact Wr.ext hv hp
      · right; right; right
        exact Wr.ext hv hp
    · rintro (rfl | rfl | rfl | rfl)
      · exact (cHat β hβ).one_mem
      · exact hmem1
      · exact hmem2
      · exact hmem3
  have hv : ∀ w w' : Wr 6, w = w' → w.vec a = w'.vec a := fun w w' h => h ▸ rfl
  have hp : ∀ w w' : Wr 6, w = w' → w.perm a = w'.perm a := fun w w' h => h ▸ rfl
  have hne1 : (1 : Wr 6) ∉ ({⟨u, 1⟩, ⟨0, s⟩, ⟨u, s⟩} : Set (Wr 6)) := by
    rintro (h | h | h)
    · have h0 : (0 : ZMod 2) = u a := hv _ _ h
      rw [hua] at h0
      exact absurd h0 (by decide)
    · have h0 : a = s a := hp _ _ h
      rw [hs, Equiv.swap_apply_left] at h0
      exact haa' h0
    · have h0 : (0 : ZMod 2) = u a := hv _ _ h
      rw [hua] at h0
      exact absurd h0 (by decide)
  have hne2 : (⟨u, 1⟩ : Wr 6) ∉ ({⟨0, s⟩, ⟨u, s⟩} : Set (Wr 6)) := by
    rintro (h | h)
    · have h0 : u a = (0 : ZMod 2) := hv _ _ h
      rw [hua] at h0
      exact absurd h0 (by decide)
    · have h0 : a = s a := hp _ _ h
      rw [hs, Equiv.swap_apply_left] at h0
      exact haa' h0
  have hne3 : (⟨0, s⟩ : Wr 6) ∉ ({⟨u, s⟩} : Set (Wr 6)) := by
    intro h
    have h0 : (0 : ZMod 2) = u a := hv _ _ (Set.mem_singleton_iff.mp h)
    rw [hua] at h0
    exact absurd h0 (by decide)
  have hcard : Nat.card (cHat β hβ) = (cHat β hβ : Set (Wr 6)).ncard := Nat.card_coe_set_eq _
  rw [hcard, hset, Set.ncard_insert_of_notMem hne1, Set.ncard_insert_of_notMem hne2,
    Set.ncard_insert_of_notMem hne3, Set.ncard_singleton]

end CHat

section AHat

variable (β : Finset (Fin 6)) (hβ : β.card = 4)

theorem comm_embed_cHat {β : Finset (Fin 6)} {hβ : β.card = 4} (l : Wr 4) {c : Wr 6}
    (hc : c ∈ cHat β hβ) : embed (emb β hβ) l * c = c * embed (emb β hβ) l :=
  comm_of_disjoint (embed_supportedOn _ l) hc.1 disjoint_compl_right

@[expose] noncomputable def aHom : ↥bQ × ↥(cHat β hβ) →* Wr 6 :=
  MonoidHom.noncommCoprod ((embed (emb β hβ)).comp bQ.subtype) (cHat β hβ).subtype
    fun l c => comm_embed_cHat (l : Wr 4) c.2

@[expose] noncomputable def aHat : Subgroup (Wr 6) := (aHom β hβ).range

theorem mem_aHat {w : Wr 6} :
    w ∈ aHat β hβ ↔ ∃ l ∈ bQ, ∃ c ∈ cHat β hβ, embed (emb β hβ) l * c = w := by
  constructor
  · rintro ⟨⟨l, c⟩, rfl⟩
    exact ⟨l, l.2, c, c.2, rfl⟩
  · rintro ⟨l, hl, c, hc, rfl⟩
    exact ⟨(⟨l, hl⟩, ⟨c, hc⟩), rfl⟩

theorem eq_one_of_supportedOn_compl {a : Wr 6} {s : Set (Fin 6)} (h1 : SupportedOn a s)
    (h2 : SupportedOn a sᶜ) : a = 1 := by
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · by_cases hx : x ∈ s
    · exact (h2 x (by simpa using hx)).1
    · exact (h1 x hx).1
  · by_cases hx : x ∈ s
    · exact (h2 x (by simpa using hx)).2
    · exact (h1 x hx).2

theorem aHom_injective : Function.Injective (aHom β hβ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨l, c⟩ h
  have h1 : embed (emb β hβ) (l : Wr 4) * (c : Wr 6) = 1 := h
  have h2 : embed (emb β hβ) (l : Wr 4) = (c : Wr 6)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : embed (emb β hβ) (l : Wr 4) = 1 :=
    eq_one_of_supportedOn_compl (embed_supportedOn _ _) (h2 ▸ c.2.1.inv)
  have hl : (l : Wr 4) = 1 := embed_injective _ (h3.trans (map_one _).symm)
  have hc : (c : Wr 6) = 1 := by
    rw [h3, one_mul] at h1
    exact h1
  rw [Subgroup.mem_bot]
  exact Prod.ext (Subtype.ext hl) (Subtype.ext hc)

theorem natCard_aHat : Nat.card (aHat β hβ) = 64 := by
  rw [aHat, ← Nat.card_congr (MonoidHom.ofInjective (aHom_injective β hβ)).toEquiv,
    Nat.card_prod, natCard_bQ, natCard_cHat]

theorem isE64_aHat : IsE64 (aHat β hβ) := by
  refine ⟨?_, ?_, natCard_aHat β hβ⟩
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (Subtype.ext (bList_comm _ p.1.2 _ q.1.2)) (Subtype.ext (cHat_comm p.2.2 q.2.2))
  · rintro _ ⟨p, rfl⟩
    rw [← map_mul]
    have : p * p = 1 := Prod.ext (Subtype.ext (bList_sq _ p.1.2)) (Subtype.ext (cHat_sq p.2.2))
    rw [this, map_one]

theorem wsum_embed (l : Wr 4) : wsum (embed (emb β hβ) l) = ∑ i, l.vec i := by
  unfold wsum
  rw [embed_vec, sum_embedVec]

theorem aHat_le_Wsub : aHat β hβ ≤ Sp62Rec.I1.Wsub := by
  rintro _ ⟨⟨l, c⟩, rfl⟩
  rw [Sp62Rec.I1.mem_Wsub]
  show wsum (embed (emb β hβ) (l : Wr 4) * (c : Wr 6)) = 0
  rw [wsum_mul, wsum_embed, bList_sum _ l.2, c.2.2, add_zero]

theorem conj_mem_aHat {b : Bool} {k : Wr 6} (hk : k ∈ memAt β hβ b) {w : Wr 6}
    (hw : w ∈ aHat β hβ) : k * w * k⁻¹ ∈ aHat β hβ := by
  obtain ⟨l, hl, c, hc, rfl⟩ := (mem_aHat β hβ).mp hw
  have hk' : ∃ k₀, (k₀ ∈ kList ∨ k₀ ∈ kStarList) ∧ embed (emb β hβ) k₀ = k := by
    cases b
    · change k ∈ memKStar (emb β hβ) at hk
      obtain ⟨k₀, hk₀, rfl⟩ := hk
      exact ⟨k₀, Or.inr hk₀, rfl⟩
    · change k ∈ memK (emb β hβ) at hk
      obtain ⟨k₀, hk₀, rfl⟩ := hk
      exact ⟨k₀, Or.inl hk₀, rfl⟩
  obtain ⟨k₀, hk₀, rfl⟩ := hk'
  have hl' : k₀ * l * k₀⁻¹ ∈ bQ := by
    rcases hk₀ with h | h
    · exact bList_conj_kList k₀ h l hl
    · exact bList_conj_kStarList k₀ h l hl
  refine (mem_aHat β hβ).mpr ⟨k₀ * l * k₀⁻¹, hl', c, hc, ?_⟩
  have hck : embed (emb β hβ) k₀⁻¹ * c = c * embed (emb β hβ) k₀⁻¹ := comm_embed_cHat _ hc
  rw [map_mul, map_mul, map_inv] at *
  calc embed (emb β hβ) k₀ * embed (emb β hβ) l * (embed (emb β hβ) k₀)⁻¹ * c
      = embed (emb β hβ) k₀ * embed (emb β hβ) l * ((embed (emb β hβ) k₀)⁻¹ * c) := by group
    _ = embed (emb β hβ) k₀ * embed (emb β hβ) l * (c * (embed (emb β hβ) k₀)⁻¹) := by rw [hck]
    _ = embed (emb β hβ) k₀ * (embed (emb β hβ) l * c) * (embed (emb β hβ) k₀)⁻¹ := by group

theorem mem_aHat_of_comm {w : Wr 6} (hw : w ∈ Sp62Rec.I1.Wsub)
    (hc : ∀ (b : Bool), ∀ k ∈ memAt β hβ b, w * k = k * w) : w ∈ aHat β hβ := by
  have hB : ∀ c : Bool, ∀ x ∈ memBar β hβ c, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x := by
    rintro c _ ⟨k, hk, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, hc c k hk, mul_inv_cancel_right]
  obtain ⟨c₀, e', hwe, he', hc₀⟩ :=
    TwinThinPf10.exists_split (by norm_num) (by norm_num) β hβ w hB
  obtain ⟨l, hl, rfl⟩ : ∃ l ∈ bQ, embed (emb β hβ) l = e' := by
    rcases he' with rfl | rfl
    · exact ⟨1, bQ.one_mem, map_one _⟩
    · exact ⟨zQ, zQ_mem_bList, rfl⟩
  have hwsum : wsum c₀ = 0 := by
    have h1 := Sp62Rec.I1.mem_Wsub.mp hw
    rw [hwe, wsum_mul, wsum_embed, bList_sum _ hl, add_zero] at h1
    exact h1
  refine (mem_aHat β hβ).mpr ⟨l, hl, c₀, ⟨hc₀, hwsum⟩, ?_⟩
  rw [hwe, comm_embed_cHat l ⟨hc₀, hwsum⟩]

end AHat

section Groups

variable {Y : Type} [Group Y]

theorem mem_normalizer_of_conjSub_eq {K : Subgroup Y} {x : Y} (h : conjSub x K = K) :
    x ∈ Subgroup.normalizer (K : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have := conj_mem_conjSub (n := x) hy
    rwa [h] at this
  · intro hy
    rw [← h, mem_conjSub_iff] at hy
    simpa [mul_assoc] using hy

theorem isE64_conjSub {A : Subgroup Y} (hA : IsE64 A) (g : Y) : IsE64 (conjSub g A) := by
  obtain ⟨hab, hsq, hcard⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hab a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]
  · rw [← hcard]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem mem_zpowers_sq_of_odd {x : Y} (h : Odd (orderOf x)) : x ∈ Subgroup.zpowers (x ^ 2) := by
  obtain ⟨j, hj⟩ := h
  refine ⟨((j + 1 : ℕ) : ℤ), ?_⟩
  show (x ^ 2) ^ (((j + 1 : ℕ) : ℤ)) = x
  rw [zpow_natCast, ← pow_mul, show 2 * (j + 1) = orderOf x + 1 by omega, pow_succ,
    pow_orderOf_eq_one, one_mul]

theorem comm_of_sq_comm {x y : Y} (hodd : Odd (orderOf x)) (h : x ^ 2 * y = y * x ^ 2) :
    x * y = y * x := by
  have h1 : x ^ 2 ∈ Subgroup.centralizer ({y} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h
  have h2 := (Subgroup.zpowers_le.mpr h1) (mem_zpowers_sq_of_odd hodd)
  exact Subgroup.mem_centralizer_singleton_iff.mp h2

theorem fix_of_odd {K L : Subgroup Y} {x : Y} (hodd : Odd (orderOf x)) (hne : K ≠ L)
    (h : (conjSub x K = K ∧ conjSub x L = L) ∨ (conjSub x K = L ∧ conjSub x L = K)) :
    conjSub x K = K ∧ conjSub x L = L := by
  rcases h with h | ⟨h1, h2⟩
  · exact h
  · exfalso
    have hsq : x ^ 2 ∈ Subgroup.normalizer (K : Set Y) :=
      mem_normalizer_of_conjSub_eq (by rw [pow_two, conjSub_mul, h1, h2])
    have hx := (Subgroup.zpowers_le.mpr hsq) (mem_zpowers_sq_of_odd hodd)
    rw [conjSub_eq_of_mem_normalizer hx] at h1
    exact hne h1

variable [Finite Y]

theorem comm_of_odd_of_conj_eq {K U : Subgroup Y} {x : Y} (hK : Nat.card K = 8) (hUK : U ≤ K)
    (hU : IsCyclic U) (hU4 : Nat.card U = 4) (hodd : Odd (orderOf x)) (hxK : conjSub x K = K)
    (hxU : conjSub x U = U) : ∀ k ∈ K, x * k = k * x := by
  classical
  have hconjU : ∀ y ∈ U, x * y * x⁻¹ ∈ U := fun y hy => by
    have := conj_mem_conjSub (n := x) hy
    rwa [hxU] at this
  have hconjK : ∀ y ∈ K, x * y * x⁻¹ ∈ K := fun y hy => by
    have := conj_mem_conjSub (n := x) hy
    rwa [hxK] at this
  have hconjU' : ∀ y, x * y * x⁻¹ ∈ U → y ∈ U := fun y hy => by
    rw [← hxU, mem_conjSub_iff] at hy
    simpa [mul_assoc] using hy
  obtain ⟨g, hg⟩ := hU.exists_zpow_surjective
  have hgz : ∀ y : ↥U, y ∈ Subgroup.zpowers g := fun y => by
    obtain ⟨k, hk⟩ := hg y
    exact ⟨k, hk⟩
  have hgo : orderOf g = 4 := by
    rw [← hU4]
    exact orderOf_eq_card_of_forall_mem_zpowers hgz
  have hg'o : orderOf (g : Y) = 4 := by rw [Subgroup.orderOf_coe, hgo]
  have hUg : ∀ y ∈ U, ∃ k : ℤ, (g : Y) ^ k = y := fun y hy => by
    obtain ⟨k, hk⟩ := hg ⟨y, hy⟩
    exact ⟨k, (SubgroupClass.coe_zpow g k).symm.trans (congrArg Subtype.val hk)⟩
  have hord : orderOf (x * (g : Y) * x⁻¹) = 4 := by
    rw [← hg'o]
    exact orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective (g : Y)
  have hxg : x * (g : Y) = (g : Y) * x := by
    have hmem : (⟨x * (g : Y) * x⁻¹, hconjU _ g.2⟩ : ↥U) ∈ Subgroup.zpowers g := hgz _
    rw [mem_zpowers_iff_mem_range_orderOf, hgo, Finset.mem_image] at hmem
    obtain ⟨n, hn, hgn⟩ := hmem
    have hgn' : (g : Y) ^ n = x * (g : Y) * x⁻¹ := by
      have := congrArg Subtype.val hgn
      rwa [SubgroupClass.coe_pow] at this
    rw [Finset.mem_range] at hn
    interval_cases n
    · rw [← hgn', pow_zero, orderOf_one] at hord
      exact absurd hord (by norm_num)
    · rw [pow_one] at hgn'
      calc x * (g : Y) = x * (g : Y) * x⁻¹ * x := by group
        _ = (g : Y) * x := by rw [← hgn']
    · rw [← hgn', orderOf_pow' _ (by norm_num), hg'o] at hord
      exact absurd hord (by norm_num)
    · apply comm_of_sq_comm hodd
      have h9 : (g : Y) ^ 9 = (g : Y) := by
        rw [show 9 = 4 * 2 + 1 by rfl, pow_add, pow_mul, ← hg'o, pow_orderOf_eq_one, one_pow,
          one_mul, pow_one]
      have h1 : x ^ 2 * (g : Y) * (x ^ 2)⁻¹ = (g : Y) := by
        calc x ^ 2 * (g : Y) * (x ^ 2)⁻¹ = x * (x * (g : Y) * x⁻¹) * x⁻¹ := by
              rw [pow_two]; group
          _ = x * (g : Y) ^ 3 * x⁻¹ := by rw [← hgn']
          _ = (x * (g : Y) * x⁻¹) ^ 3 := conj_pow.symm
          _ = (g : Y) ^ 9 := by rw [← hgn', ← pow_mul]
          _ = (g : Y) := h9
      calc x ^ 2 * (g : Y) = x ^ 2 * (g : Y) * (x ^ 2)⁻¹ * x ^ 2 :=
            (inv_mul_cancel_right _ _).symm
        _ = (g : Y) * x ^ 2 := by rw [h1]
  have hxU' : ∀ y ∈ U, x * y = y * x := by
    intro y hy
    obtain ⟨k, rfl⟩ := hUg y hy
    exact (Commute.zpow_right hxg k).eq
  have hidx : (U.subgroupOf K).index = 2 := by
    have h1 := Subgroup.card_mul_index (U.subgroupOf K)
    have h2 : Nat.card (U.subgroupOf K) = 4 := by
      rw [← hU4]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv
    rw [h2, hK] at h1
    omega
  intro k hk
  by_cases hkU : k ∈ U
  · exact hxU' k hkU
  · have hyK : x * k * x⁻¹ ∈ K := hconjK k hk
    have hyU : x * k * x⁻¹ ∉ U := fun h => hkU (hconjU' k h)
    have hu : k⁻¹ * (x * k * x⁻¹) ∈ U := by
      have ha : (⟨k⁻¹, K.inv_mem hk⟩ : ↥K) ∉ U.subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        exact fun h => hkU (by simpa using U.inv_mem h)
      have hb : (⟨x * k * x⁻¹, hyK⟩ : ↥K) ∉ U.subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        exact hyU
      have := (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false ha hb)
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    set u := k⁻¹ * (x * k * x⁻¹) with hudef
    have hxk : x * k = k * u * x := by
      rw [hudef]
      group
    have hpow : ∀ j : ℕ, x ^ j * k = k * u ^ j * x ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hc : x * u ^ j = u ^ j * x := (Commute.pow_right (hxU' u hu) j).eq
        calc x ^ (j + 1) * k = x * (x ^ j * k) := by rw [pow_succ', mul_assoc]
          _ = x * (k * u ^ j * x ^ j) := by rw [ih]
          _ = (x * k) * u ^ j * x ^ j := by group
          _ = k * u * (x * u ^ j) * x ^ j := by rw [hxk]; group
          _ = k * u * (u ^ j * x) * x ^ j := by rw [hc]
          _ = k * u ^ (j + 1) * x ^ (j + 1) := by rw [pow_succ', pow_succ']; group
    have hm := hpow (orderOf x)
    rw [pow_orderOf_eq_one, mul_one, one_mul] at hm
    have hum : u ^ orderOf x = 1 := by
      have h1 : k⁻¹ * k = k⁻¹ * (k * u ^ orderOf x) := by rw [← hm]
      simpa using h1.symm
    have hu4 : u ^ 4 = 1 := by
      have h1 := orderOf_dvd_natCard (⟨u, hu⟩ : ↥U)
      rw [hU4] at h1
      have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
      have h3 := congrArg Subtype.val h2
      rwa [SubgroupClass.coe_pow] at h3
    have hcop : Nat.Coprime (orderOf x) 4 :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd)
    have hu1 : u = 1 := by
      have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hum) (orderOf_dvd_of_pow_eq_one hu4)
      rw [hcop] at h1
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
    calc x * k = k * u * x := hxk
      _ = k * x := by rw [hu1, mul_one]

theorem not_two_dvd_index {V P : Subgroup Y} (h : IsSylow2In V P) :
    ¬ 2 ∣ (V.subgroupOf P).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Ps : Sylow 2 ↥P :=
    { toSubgroup := V.subgroupOf P
      isPGroup' := h.2.1.comap_subtype
      is_maximal' := by
        intro Q hQ hle
        have hVQ : V ≤ Q.map P.subtype := by
          rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
          exact Subgroup.map_mono hle
        have := h.2.2 (Q.map P.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
        rw [← Subgroup.comap_map_eq_self_of_injective P.subtype_injective Q, this]
        rfl }
  exact Ps.not_dvd_index

theorem exists_odd_not_mem {N H Q : Subgroup Y} (hQ : IsSylow2In Q N) (hQH : Q ≤ H) {x₀ : Y}
    (hx₀ : x₀ ∈ N) (hx₀H : x₀ ∉ H) : ∃ x ∈ N, x ∉ H ∧ Odd (orderOf x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H' : Subgroup ↥N := H.subgroupOf N
  have hle : Q.subgroupOf N ≤ H' := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hQH (Subgroup.mem_subgroupOf.mp hy))
  have h2 : ¬ 2 ∣ H'.index := fun h =>
    not_two_dvd_index hQ (h.trans (Subgroup.index_dvd_of_le hle))
  have hne : H'.index ≠ 1 := by
    rw [Ne, Subgroup.index_eq_one]
    intro htop
    apply hx₀H
    have h1 : (⟨x₀, hx₀⟩ : ↥N) ∈ H' := htop ▸ Subgroup.mem_top _
    exact h1
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hp2 : p ≠ 2 := fun h => h2 (h ▸ hpdvd)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p ↥N) := inferInstance
  have hPH : ¬ (P : Subgroup ↥N) ≤ H' := fun h =>
    P.not_dvd_index (hpdvd.trans (Subgroup.index_dvd_of_le h))
  obtain ⟨y, hyP, hyH⟩ := SetLike.not_le_iff_exists.mp hPH
  refine ⟨y, y.2, hyH, ?_⟩
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hyP⟩
  have hk' : y ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : orderOf (y : Y) ∣ p ^ k := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hk'
  exact Odd.of_dvd_nat ((hp.odd_of_ne_two hp2).pow) hdvd

theorem frattini_step {B C G T A A₁ P₀ : Subgroup Y} {e : Y}
    (hCG : C ≤ G) (hnorm : ∀ g ∈ G, conjSub g C = C) (hCB : C ≤ B)
    (hCe : ∀ c ∈ C, ∀ g ∈ G, c * (g * e * g⁻¹) = g * e * g⁻¹ * c)
    (hT : IsSylow2In T B) (huniq : ∀ A' ≤ T, IsE64 A' → A' = A)
    (hA₁ : IsE64 A₁) (hA₁C : A₁ ≤ C)
    (hP₀ : IsSylow2In P₀ G) (hP₀e : P₀ ≤ Subgroup.centralizer ({e} : Set Y))
    {c' : Y} (hc'G : c' ∈ G) (hc' : c' * e * c'⁻¹ ≠ e) :
    ∃ x ∈ G, x * e ≠ e * x ∧ Odd (orderOf x) ∧ conjSub x A₁ = A₁ ∧
      ∃ b ∈ B, conjSub b A₁ = A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA₁2 : IsPGroup 2 A₁ := IsPGroup.of_card (n := 6) (by rw [hA₁.2.2]; norm_num)
  obtain ⟨S, hS, hA₁S⟩ := IsSylow2In.exists_ge hA₁2 hA₁C
  obtain ⟨T', hT', hST'⟩ := IsSylow2In.exists_ge hS.2.1 (hS.1.trans hCB)
  obtain ⟨b, hbB, hb⟩ := Thompson.exists_conj_of_isSylow2In hT' hT
  have huniq' : ∀ A' ≤ T', IsE64 A' → conjSub b A' = A := fun A' hA'T hA' =>
    huniq _ (hb ▸ conjSub_mono hA'T) (isE64_conjSub hA' b)
  have hbA : conjSub b A₁ = A := huniq' A₁ (hA₁S.trans hST') hA₁
  have hNA : ∀ n ∈ Subgroup.normalizer (S : Set Y), conjSub n A₁ = A₁ := by
    intro n hn
    have h1 : conjSub n A₁ ≤ T' := by
      have := conjSub_mono (n := n) hA₁S
      rw [conjSub_eq_of_mem_normalizer hn] at this
      exact this.trans hST'
    apply conjSub_injective b
    rw [huniq' _ h1 (isE64_conjSub hA₁ n), hbA]
  set N : Subgroup Y := G ⊓ Subgroup.normalizer (S : Set Y)
  have hfr : ∀ g ∈ G, ∃ h ∈ C, h * g ∈ N := by
    intro g hg
    have h1 : IsSylow2In (conjSub g S) C := by
      have := hS.conj g
      rwa [hnorm g hg] at this
    obtain ⟨h, hhC, hh⟩ := Thompson.exists_conj_of_isSylow2In h1 hS
    refine ⟨h, hhC, G.mul_mem (hCG hhC) hg, mem_normalizer_of_conjSub_eq ?_⟩
    rw [conjSub_mul, hh]
  have hconj : ∀ h ∈ C, ∀ n ∈ G, (h * n) * e * (h * n)⁻¹ = n * e * n⁻¹ := by
    intro h hh n hn
    calc (h * n) * e * (h * n)⁻¹ = h * (n * e * n⁻¹) * h⁻¹ := by group
      _ = n * e * n⁻¹ * h * h⁻¹ := by rw [hCe h hh n hn]
      _ = n * e * n⁻¹ := by group
  obtain ⟨h₀, hh₀, hn₀⟩ := hfr c' hc'G
  have hn₀e : h₀ * c' ∉ Subgroup.centralizer ({e} : Set Y) := by
    intro hmem
    apply hc'
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hmem
    calc c' * e * c'⁻¹ = (h₀ * c') * e * (h₀ * c')⁻¹ := (hconj h₀ hh₀ c' hc'G).symm
      _ = e * (h₀ * c') * (h₀ * c')⁻¹ := by rw [← h1]
      _ = e := by group
  obtain ⟨Q, hQ, -⟩ :=
    IsSylow2In.exists_ge (IsPGroup.of_bot (p := 2)) (bot_le : (⊥ : Subgroup Y) ≤ N)
  obtain ⟨Q', hQ', hQQ'⟩ := IsSylow2In.exists_ge hQ.2.1 (hQ.1.trans inf_le_left)
  obtain ⟨g, hgG, hg⟩ := Thompson.exists_conj_of_isSylow2In hP₀ hQ'
  obtain ⟨h, hhC, hn⟩ := hfr g hgG
  have hgn : g * e * g⁻¹ = (h * g) * e * (h * g)⁻¹ := (hconj h hhC g hgG).symm
  have hQe : conjSub (h * g)⁻¹ Q ≤ Subgroup.centralizer ({e} : Set Y) := by
    intro q hq
    rw [mem_conjSub_iff, inv_inv] at hq
    have h1 : (h * g) * q * (h * g)⁻¹ ∈ conjSub g P₀ := hg ▸ hQQ' hq
    rw [mem_conjSub_iff] at h1
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hP₀e h1)
    have h3 : (g * e * g⁻¹) * ((h * g) * q * (h * g)⁻¹) =
        ((h * g) * q * (h * g)⁻¹) * (g * e * g⁻¹) := by
      calc (g * e * g⁻¹) * ((h * g) * q * (h * g)⁻¹)
          = g * (e * (g⁻¹ * ((h * g) * q * (h * g)⁻¹) * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * ((h * g) * q * (h * g)⁻¹) * g) * e) * g⁻¹ := by rw [h2]
        _ = ((h * g) * q * (h * g)⁻¹) * (g * e * g⁻¹) := by group
    rw [hgn] at h3
    have h4 : (h * g) * (e * q) * (h * g)⁻¹ = (h * g) * (q * e) * (h * g)⁻¹ := by
      calc (h * g) * (e * q) * (h * g)⁻¹
          = ((h * g) * e * (h * g)⁻¹) * ((h * g) * q * (h * g)⁻¹) := by group
        _ = ((h * g) * q * (h * g)⁻¹) * ((h * g) * e * (h * g)⁻¹) := h3
        _ = (h * g) * (q * e) * (h * g)⁻¹ := by group
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_left_cancel (mul_right_cancel h4)).symm
  have hQN : IsSylow2In (conjSub (h * g)⁻¹ Q) N := by
    have := hQ.conj (h * g)⁻¹
    rwa [conjSub_eq_self_of_mem (N.inv_mem hn)] at this
  obtain ⟨x, hxN, hxe, hxodd⟩ := exists_odd_not_mem hQN hQe hn₀ hn₀e
  refine ⟨x, hxN.1, fun h' => hxe (Subgroup.mem_centralizer_singleton_iff.mpr h'), hxodd,
    hNA x hxN.2, b, hbB, hbA⟩

end Groups

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZXW
