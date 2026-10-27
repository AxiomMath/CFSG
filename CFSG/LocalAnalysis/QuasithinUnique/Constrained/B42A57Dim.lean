module

public import CFSG.Quasithin.Background.ConjTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Emb
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Orb

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin Equiv Equiv.Perm

variable {S : Type} [CommGroup S] [Finite S] {G L A : Subgroup (MulAut S)} {m : ℕ}

theorem index_fixV_le (hA : IsFFStarOffender G A) :
    (fixV A).index ≤ Nat.card A := by
  have h1 := hA.card_le (bot_le : (⊥ : Subgroup (MulAut S)) ≤ A)
  rw [B1.card_bot_mul_card_fixV] at h1
  have h2 := Subgroup.index_mul_card (fixV A)
  have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : Nat.card A * Nat.card (fixV A) < (fixV A).index * Nat.card (fixV A) :=
    Nat.mul_lt_mul_of_pos_right hlt hpos
  omega

omit [Finite S] in
theorem index_fixV_conj (A : Subgroup (MulAut S)) (g : MulAut S) :
    (fixV (A.map (MulAut.conj g).toMonoidHom)).index = (fixV A).index :=
  CFSG.Quasithin.ConjTransport.index_fixV_map_conj A g

omit [Finite S] in
theorem fixV_eq_bot_of_irr (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    (hnc : ∃ a b : ↥L, a * b ≠ b * a) : fixV L = ⊥ := by
  have hinv : XMod.IsInv ↥L (fixV L) := by
    intro a v hv
    have h : (a : MulAut S) v = v := hv a a.2
    have h2 : a • v = v := by simpa [Subgroup.smul_def, MulAut.smul_def] using h
    rw [h2]
    exact hv
  rcases hirr.2 (fixV L) hinv bot_le le_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have h1 : ∀ l : ↥L, (l : MulAut S) = 1 := by
      intro l
      apply MulEquiv.ext
      intro v
      have hv : v ∈ fixV L := by rw [h]; trivial
      exact hv l l.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, h1 a, h1 b]

omit [Finite S] in
theorem offender_image (hA : IsFFStarOffender G A) (e : ↥G →* Perm (Fin m))
    (hinj : Function.Injective e) :
    (A.subgroupOf G).map e ≠ ⊥ ∧
      (∀ x ∈ (A.subgroupOf G).map e, ∀ y ∈ (A.subgroupOf G).map e, x * y = y * x) ∧
      (∀ x ∈ (A.subgroupOf G).map e, x * x = 1) ∧
      Nat.card ((A.subgroupOf G).map e) = Nat.card A := by
  have hAG : A ≤ G := hA.1
  set A' : Subgroup ↥G := A.subgroupOf G with hA'
  set Ā : Subgroup (Perm (Fin m)) := A'.map e with hĀ
  have hmemA' : ∀ a : MulAut S, ∀ ha : a ∈ G, (⟨a, ha⟩ : ↥G) ∈ A' ↔ a ∈ A := fun a ha =>
    Subgroup.mem_subgroupOf
  have hĀ1 : Ā ≠ ⊥ := by
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.2.1
    have ha' : (⟨(a : MulAut S), hAG a.2⟩ : ↥G) ∈ A' := (hmemA' _ _).2 a.2
    have hne : e ⟨(a : MulAut S), hAG a.2⟩ ≠ 1 := by
      intro h
      apply ha1
      have h3 : (⟨(a : MulAut S), hAG a.2⟩ : ↥G) = 1 := hinj (by rw [h, map_one])
      have h4 : (a : MulAut S) = 1 := congrArg Subtype.val h3
      exact Subtype.ext h4
    intro h
    have hmem : e ⟨(a : MulAut S), hAG a.2⟩ ∈ Ā := Subgroup.mem_map.2 ⟨_, ha', rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hne hmem
  have hĀc : ∀ x ∈ Ā, ∀ y ∈ Ā, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hA.2.2.1.1 _ (Subgroup.mem_subgroupOf.1 ha') _ (Subgroup.mem_subgroupOf.1 hb')
  have hĀ2 : ∀ x ∈ Ā, x * x = 1 := by
    intro x hx
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_mul]
    have : a' * a' = 1 := by
      apply Subtype.ext
      have := hA.2.2.1.2 _ (Subgroup.mem_subgroupOf.1 ha')
      simpa [pow_two] using this
    rw [this, map_one]
  have hcardĀ : Nat.card Ā = Nat.card A := by
    rw [hĀ, Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv
  exact ⟨hĀ1, hĀc, hĀ2, hcardĀ⟩

theorem card_le_of_cert (C : Bridge.Alt57.Ctx G L m) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    (hA : IsFFStarOffender G A) (ι : ↥L ≃* alternatingGroup (Fin m)) (e : ↥G →* Perm (Fin m))
    (hinj : Function.Injective e)
    (hL : ∀ l : ↥L, e ⟨(l : MulAut S), C.le_G l.2⟩ = (ι l : Perm (Fin m))) {N r : ℕ}
    (f : Fin r → Perm (Fin m)) (hf : ∀ i, f i ∈ alternatingGroup (Fin m))
    (hbound : Nat.card A ^ r ≤ N)
    (hcl : alternatingGroup (Fin m) ≤
      Subgroup.closure {x | ∃ i, ∃ b ∈ (A.subgroupOf G).map e, x = f i * b * (f i)⁻¹}) :
    Nat.card S ≤ N := by
  set A' : Subgroup ↥G := A.subgroupOf G with hA'
  let g : Fin r → ↥G := fun i =>
    ⟨((ι.symm ⟨f i, hf i⟩ : ↥L) : MulAut S), C.le_G (ι.symm ⟨f i, hf i⟩).2⟩
  have hge : ∀ i, e (g i) = f i := fun i => by
    have := hL (ι.symm ⟨f i, hf i⟩)
    rw [ι.apply_symm_apply] at this
    exact this
  let K : Fin r → Subgroup S := fun i =>
    fixV (A.map (MulAut.conj ((g i : ↥G) : MulAut S)).toMonoidHom)
  have hK : ⨅ i, K i = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hvK : ∀ i, v ∈ K i := fun i => (Subgroup.mem_iInf.1 hv) i
    let Stab : Subgroup ↥G :=
      { carrier := {x | ((x : ↥G) : MulAut S) v = v}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          have hx' : ((x : ↥G) : MulAut S) v = v := hx
          have hy' : ((y : ↥G) : MulAut S) v = v := hy
          show ((x * y : ↥G) : MulAut S) v = v
          rw [Subgroup.coe_mul, MulAut.mul_apply, hy', hx']
        inv_mem' := fun {x} hx => by
          have hx' : ((x : ↥G) : MulAut S) v = v := hx
          show (((x⁻¹ : ↥G) : MulAut S)) v = v
          rw [Subgroup.coe_inv]
          have := congrArg (fun w => ((x : ↥G) : MulAut S)⁻¹ w) hx'
          simpa using this.symm }
    let Hg : Subgroup ↥G := Subgroup.closure {x : ↥G | ∃ i, ∃ a ∈ A', x = g i * a * (g i)⁻¹}
    have hHS : Hg ≤ Stab := by
      refine (Subgroup.closure_le Stab).2 ?_
      rintro _ ⟨i, a, ha, rfl⟩
      have hmem : ((g i : ↥G) : MulAut S) * ((a : ↥G) : MulAut S) * ((g i : ↥G) : MulAut S)⁻¹ ∈
          A.map (MulAut.conj ((g i : ↥G) : MulAut S)).toMonoidHom :=
        Subgroup.mem_map.2 ⟨((a : ↥G) : MulAut S), Subgroup.mem_subgroupOf.1 ha, by simp⟩
      have := hvK i _ hmem
      show (((g i * a * (g i)⁻¹ : ↥G) : MulAut S)) v = v
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
    have hAle : alternatingGroup (Fin m) ≤ Hg.map e := by
      refine hcl.trans ?_
      rw [Subgroup.closure_le]
      rintro _ ⟨i, b, hb, rfl⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
      rw [← hge i, ← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map.2 ⟨_, Subgroup.subset_closure ⟨i, a, ha, rfl⟩, rfl⟩
    have hvL : v ∈ fixV L := by
      intro l hl
      have hlA : (ι ⟨l, hl⟩ : Perm (Fin m)) ∈ alternatingGroup (Fin m) := (ι ⟨l, hl⟩).2
      obtain ⟨h, hh, hel⟩ := Subgroup.mem_map.1 (hAle hlA)
      have : h = ⟨l, C.le_G hl⟩ := hinj (by rw [hel, hL ⟨l, hl⟩])
      have hS' := hHS hh
      rw [this] at hS'
      exact hS'
    rw [fixV_eq_bot_of_irr hirr C.nonab] at hvL
    exact hvL
  have h1 := Subgroup.index_iInf_le K
  rw [hK, Subgroup.index_bot] at h1
  have h2 : ∀ i, (K i).index = (fixV A).index := fun i => index_fixV_conj A _
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  calc Nat.card S ≤ (fixV A).index ^ r := h1
    _ ≤ Nat.card A ^ r := Nat.pow_le_pow_left (index_fixV_le hA) r
    _ ≤ N := hbound


theorem card_le_of_gen (C : Bridge.Alt57.Ctx G L m) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    (hA : IsFFStarOffender G A) {N : ℕ}
    (hgen : ∀ B : Subgroup (Perm (Fin m)), B ≠ ⊥ → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) →
      (∀ a ∈ B, a * a = 1) → ∃ (r : ℕ) (f : Fin r → Perm (Fin m)),
        (∀ i, f i ∈ alternatingGroup (Fin m)) ∧ Nat.card B ^ r ≤ N ∧
        alternatingGroup (Fin m) ≤
          Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = f i * b * (f i)⁻¹}) :
    Nat.card S ≤ N := by
  obtain ⟨ι, e, hinj, hL, -⟩ := exists_embedding C
  obtain ⟨h1, hc, h2, hcard⟩ := offender_image hA e hinj
  obtain ⟨r, f, hf, hbound, hcl⟩ := hgen _ h1 hc h2
  exact card_le_of_cert C hirr hA ι e hinj hL f hf (hcard ▸ hbound) hcl

theorem card_le_of_offender (C : Bridge.Alt57.Ctx G L m)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤) (hA : IsFFStarOffender G A) :
    (m = 5 → Nat.card S ≤ 2 ^ 4) ∧ (m = 7 → Nat.card S ≤ 2 ^ 6) := by
  constructor
  · rintro rfl
    exact card_le_of_gen C hirr hA fun B h1 hc h2 => gen5 h1 hc h2
  · rintro rfl
    exact card_le_of_gen C hirr hA fun B h1 hc h2 => gen7 h1 hc h2

theorem card_ge_of_faithful (C : Bridge.Alt57.Ctx G L m) (hS : ∀ s : S, s * s = 1) :
    2 ^ 4 ≤ Nat.card S := by
  have h5 : 5 ∣ Nat.card ↥L := by
    rcases C.card_cases with h | h <;> rw [h] <;> norm_num
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 5 h5
  have hx5 : ((x : ↥L) : MulAut S) ^ 5 = 1 := by
    have : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have := congrArg Subtype.val this
    simpa using this
  have hx1 : ((x : ↥L) : MulAut S) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    omega
  have := card_ge_sixteen_of_order_five hS ((x : ↥L) : MulAut S) hx5 hx1
  simpa using this

end CFSG.QuasithinUnique.B42A57
