module

public import CFSG.ClassicalInvolution.Q3.TL3T44
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.TC.Thin.Amalg
open CFSG.ComponentClassification.PresentationLocal

namespace AE8End

@[expose] def altOn (T : Finset (Fin 8)) : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | σ ∈ alternatingGroup (Fin 8) ∧ ∀ x, x ∉ T → σ x = x}
  mul_mem' := by
    rintro σ τ ⟨hσ, hσ'⟩ ⟨hτ, hτ'⟩
    refine ⟨mul_mem hσ hτ, fun x hx => ?_⟩
    rw [Equiv.Perm.mul_apply, hτ' x hx, hσ' x hx]
  one_mem' := ⟨one_mem _, fun _ _ => rfl⟩
  inv_mem' := by
    rintro σ ⟨hσ, hσ'⟩
    refine ⟨inv_mem hσ, fun x hx => ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hσ' x hx).symm

theorem altOn_mono {T T' : Finset (Fin 8)} (h : T ⊆ T') : altOn T ≤ altOn T' :=
  fun _ hσ => ⟨hσ.1, fun x hx => hσ.2 x fun hxT => hx (h hxT)⟩

theorem altOn_comm {T₁ T₂ : Finset (Fin 8)} (hT : Disjoint T₁ T₂) {s t : Equiv.Perm (Fin 8)}
    (hs : s ∈ altOn T₁) (ht : t ∈ altOn T₂) : s * t = t * s :=
  mul_comm_of_supp (T₁ := (T₁ : Set (Fin 8))) (T₂ := (T₂ : Set (Fin 8)))
    (Finset.disjoint_coe.2 hT) (fun p hp => hs.2 p (by simpa using hp))
    (fun p hp => ht.2 p (by simpa using hp))

theorem ae8k_inv_apply (σ : Equiv.Perm (Fin 8)) (x : Fin 8) : σ⁻¹ (σ x) = x :=
  σ.symm_apply_apply x

theorem ae8k_apply_inv (σ : Equiv.Perm (Fin 8)) (x : Fin 8) : σ (σ⁻¹ x) = x :=
  σ.apply_symm_apply x

theorem mem_altOn_image_iff (σ : Equiv.Perm (Fin 8)) (T : Finset (Fin 8))
    (s : Equiv.Perm (Fin 8)) : s ∈ altOn (T.image σ) ↔ σ⁻¹ * s * σ ∈ altOn T := by
  have hsign : s ∈ alternatingGroup (Fin 8) ↔ σ⁻¹ * s * σ ∈ alternatingGroup (Fin 8) := by
    have h : Equiv.Perm.sign (σ⁻¹ * s * σ) = Equiv.Perm.sign s := by
      rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
    simp only [Equiv.Perm.mem_alternatingGroup, h]
  refine and_congr hsign ⟨fun h x hx => ?_, fun h y hy => ?_⟩
  · have hσx : σ x ∉ T.image σ := fun hm => hx (by
      obtain ⟨z, hz, hzx⟩ := Finset.mem_image.1 hm
      rwa [← σ.injective hzx])
    simp only [Equiv.Perm.mul_apply, ae8k_inv_apply]
    rw [h (σ x) hσx, ae8k_inv_apply]
  · have hx : σ⁻¹ y ∉ T := fun hm => hy (Finset.mem_image.2 ⟨σ⁻¹ y, hm, ae8k_apply_inv σ y⟩)
    have := h (σ⁻¹ y) hx
    simp only [Equiv.Perm.mul_apply, ae8k_inv_apply] at this
    have h2 := congrArg σ this
    rwa [ae8k_apply_inv, ae8k_apply_inv] at h2

theorem exists_perm_image_eq {Γ Γ' : Finset (Fin 8)} (h : Γ.card = Γ'.card) :
    ∃ σ : Equiv.Perm (Fin 8), Γ.image σ = Γ' := by
  classical
  let e : {x // x ∈ Γ} ≃ {x // x ∈ Γ'} := Finset.equivOfCardEq h
  refine ⟨Equiv.extendSubtype e, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    rw [Equiv.extendSubtype_apply_of_mem e x hx]
    exact (e ⟨x, hx⟩).2
  · rw [Finset.card_image_of_injective _ (Equiv.injective _)]
    exact h.ge

theorem extPerm_mem_altOn {N : ℕ} (ε : Fin N ↪ Fin 8) (σ : alternatingGroup (Fin N)) :
    extPerm ε (σ : Equiv.Perm (Fin N)) ∈ altOn (Finset.univ.image ε) := by
  refine ⟨?_, fun x hx => extPerm_apply_not_mem ε _ fun ⟨i, hi⟩ =>
    hx (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)⟩
  rw [Equiv.Perm.mem_alternatingGroup, sign_extPerm]
  exact Equiv.Perm.mem_alternatingGroup.1 σ.2

theorem exists_extPerm_of_mem_altOn {N : ℕ} (ε : Fin N ↪ Fin 8) {s : Equiv.Perm (Fin 8)}
    (hs : s ∈ altOn (Finset.univ.image ε)) :
    ∃ σ : alternatingGroup (Fin N), extPerm ε (σ : Equiv.Perm (Fin N)) = s := by
  obtain ⟨σ, hσ⟩ := exists_altExt_eq ε ⟨s, hs.1⟩ (fun x hx => hs.2 x fun hm => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hm
    exact hx ⟨i, hi⟩)
  exact ⟨σ, congrArg Subtype.val hσ⟩

theorem altOn_symm_apply_of_not_mem {T : Finset (Fin 8)} {σ : Equiv.Perm (Fin 8)}
    (hσ : σ ∈ altOn T) {i : Fin 8} (hi : i ∉ T) : σ.symm i = i := by
  rw [Equiv.symm_apply_eq]
  exact (hσ.2 i hi).symm

theorem altOn_symm_mem {T : Finset (Fin 8)} {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ altOn T)
    {i : Fin 8} (hi : i ∈ T) : σ.symm i ∈ T := by
  by_contra h
  have h1 : σ (σ.symm i) = σ.symm i := hσ.2 _ h
  rw [Equiv.apply_symm_apply] at h1
  exact h (h1 ▸ hi)

theorem altOn_le_closure_extPerm (ε : Fin 4 ↪ Fin 8) :
    altOn (Finset.univ.image ε) ≤
      Subgroup.closure (Set.range fun k : CarmichaelIndex 4 => extPerm ε (carmichaelPerm k)) := by
  intro s hs
  obtain ⟨σ, rfl⟩ := exists_extPerm_of_mem_altOn ε hs
  have hσ : σ ∈ Subgroup.closure (Set.range (carmichaelCycle (n := 4))) := by
    rw [closure_range_carmichaelCycle (by norm_num)]
    trivial
  clear hs
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨k, rfl⟩
  | one => simpa using one_mem _
  | mul x y hx hy ihx ihy => simpa [map_mul] using mul_mem ihx ihy
  | inv x hx ihx => simpa [map_inv] using inv_mem ihx

namespace Ev8

abbrev F2Vec8 : Type := Fin 8 → ZMod 2

@[expose] def vecAct (σ : Equiv.Perm (Fin 8)) (f : F2Vec8) : F2Vec8 := fun i => f (σ.symm i)

@[expose] def vecOnes : F2Vec8 := fun _ => 1

@[expose] def InW (f : F2Vec8) : Prop := f = 0 ∨ f = vecOnes

instance : DecidablePred InW := fun f => inferInstanceAs (Decidable (f = 0 ∨ f = vecOnes))

theorem vecAct_apply (σ : Equiv.Perm (Fin 8)) (f : F2Vec8) (i : Fin 8) :
    vecAct σ f i = f (σ.symm i) := rfl

theorem vecAct_mul (s t : Equiv.Perm (Fin 8)) (f : F2Vec8) :
    vecAct (s * t) f = vecAct s (vecAct t f) := rfl

theorem vecAct_one (f : F2Vec8) : vecAct 1 f = f := rfl

theorem vecAct_add (s : Equiv.Perm (Fin 8)) (f g : F2Vec8) :
    vecAct s (f + g) = vecAct s f + vecAct s g := rfl

theorem vecAct_zero (s : Equiv.Perm (Fin 8)) : vecAct s 0 = 0 := rfl

theorem vecAct_ones (s : Equiv.Perm (Fin 8)) : vecAct s vecOnes = vecOnes := rfl

theorem vecAct_inv_vecAct (s : Equiv.Perm (Fin 8)) (f : F2Vec8) :
    vecAct s⁻¹ (vecAct s f) = f := by
  funext i
  simp only [vecAct_apply, Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem sum_vecAct (s : Equiv.Perm (Fin 8)) (f : F2Vec8) : ∑ i, vecAct s f i = ∑ i, f i :=
  Equiv.sum_comp s.symm f

theorem InW.zero : InW 0 := Or.inl rfl

theorem InW.add {f g : F2Vec8} (hf : InW f) (hg : InW g) : InW (f + g) := by
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
  · exact Or.inl (add_zero 0)
  · exact Or.inr (zero_add _)
  · exact Or.inr (add_zero _)
  · refine Or.inl (funext fun i => ?_)
    simp only [Pi.add_apply, vecOnes, Pi.zero_apply]
    decide

theorem InW.vecAct {f : F2Vec8} (hf : InW f) (s : Equiv.Perm (Fin 8)) : InW (vecAct s f) := by
  rcases hf with rfl | rfl
  · exact Or.inl (vecAct_zero s)
  · exact Or.inr (vecAct_ones s)

theorem InW.of_eq_add {g a b : F2Vec8} (ha : InW a) (hb : InW b) (h : g = a + b) : InW g :=
  h ▸ ha.add hb

theorem vec_add_self (f : F2Vec8) : f + f = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  grind

theorem vec_aux {T₁ T₂ : Finset (Fin 8)} (hT : Disjoint T₁ T₂) (hT₂ : T₂.Nonempty)
    {σ τ : Equiv.Perm (Fin 8)} (hσ : σ ∈ altOn T₁) (hτ : τ ∈ altOn T₂) (f : F2Vec8)
    (h : InW (vecAct σ (f + vecAct τ f + vecAct τ (vecAct τ f)) +
      (f + vecAct τ f + vecAct τ (vecAct τ f)))) : vecAct σ f = f := by
  obtain ⟨g, hg⟩ : ∃ g : F2Vec8, g = vecAct σ f + f := ⟨_, rfl⟩
  have hg1 : ∀ i, i ∉ T₁ → g i = 0 := by
    intro i hi
    have e : σ.symm i = i := altOn_symm_apply_of_not_mem hσ hi
    simp only [hg, Pi.add_apply, vecAct_apply, e]
    grind
  have hg2 : vecAct τ g = g := by
    funext i
    by_cases hi : i ∈ T₂
    · have h1 : τ.symm i ∈ T₂ := altOn_symm_mem hτ hi
      have h2 := hg1 i (fun h => Finset.disjoint_left.1 hT h hi)
      have h3 := hg1 _ (fun h => Finset.disjoint_left.1 hT h h1)
      rw [vecAct_apply, h3, h2]
    · rw [vecAct_apply, altOn_symm_apply_of_not_mem hτ hi]
  have hcomm : ∀ f' : F2Vec8, vecAct σ (vecAct τ f') = vecAct τ (vecAct σ f') := by
    intro f'
    rw [← vecAct_mul, ← vecAct_mul, altOn_comm hT hσ hτ]
  have key : vecAct σ (f + vecAct τ f + vecAct τ (vecAct τ f)) +
      (f + vecAct τ f + vecAct τ (vecAct τ f)) = g + vecAct τ g + vecAct τ (vecAct τ g) := by
    simp only [vecAct_add, hcomm, hg]
    funext i
    simp only [Pi.add_apply]
    grind
  rw [key, hg2, hg2] at h
  have e : g + g + g = g := by
    funext i
    simp only [Pi.add_apply]
    grind
  rw [e] at h
  rcases h with h0 | h1
  · funext i
    have := congrFun h0 i
    simp only [hg, Pi.add_apply, Pi.zero_apply] at this
    grind
  · exfalso
    obtain ⟨p, hp⟩ := hT₂
    have := congrFun h1 p
    rw [hg1 p (fun h => Finset.disjoint_left.1 hT h hp)] at this
    simp [vecOnes] at this

@[expose] def c₂ : Equiv.Perm (Fin 8) := carmichaelPerm (n := 8) ⟨⟨2, by norm_num⟩, by norm_num⟩

@[expose] def c₃ : Equiv.Perm (Fin 8) := carmichaelPerm (n := 8) ⟨⟨3, by norm_num⟩, by norm_num⟩

theorem core : ∀ x : F2Vec8, ∑ i, x i = 0 →
    InW (x + vecAct c₂ x + vecAct (c₂ * c₂) x) →
    ∀ y : F2Vec8, ∑ i, y i = 0 →
    InW (y + vecAct c₃ y + vecAct (c₃ * c₃) y) →
    InW ((x + vecAct c₂ y) + vecAct (c₂ * c₃) (x + vecAct c₂ y)) →
    ∃ v : F2Vec8, ∑ i, v i = 0 ∧ InW (x + vecAct c₂ v + v) ∧
      InW (y + vecAct c₃ v + v) := by
  decide +kernel

@[expose] def ε₄ : Fin 4 ↪ Fin 8 := Fin.castLEEmb (by norm_num)

@[expose] def Γ₀ : Finset (Fin 8) := Finset.univ.image ε₄

theorem Γ₀_card : Γ₀.card = 4 := by decide +kernel

theorem c₂_mem : c₂ ∈ altOn Γ₀ :=
  ⟨carmichaelPerm_mem _, by decide +kernel⟩

theorem c₃_mem : c₃ ∈ altOn Γ₀ :=
  ⟨carmichaelPerm_mem _, by decide +kernel⟩

theorem altOn_Γ₀_le_closure :
    altOn Γ₀ ≤ Subgroup.closure ({c₂, c₃} : Set (Equiv.Perm (Fin 8))) := by
  refine (altOn_le_closure_extPerm ε₄).trans (Subgroup.closure_mono ?_)
  rintro _ ⟨k, rfl⟩
  have h := congrArg Subtype.val
    (altExt_carmichaelCycle (m := 8) (N := 4) (by norm_num) (by norm_num) ε₄ rfl rfl k)
  have h' : extPerm ε₄ (carmichaelPerm k) =
      carmichaelPerm (n := 8) ⟨ε₄ k.1, two_le_of_fix (by norm_num) (by norm_num) ε₄
        rfl rfl k⟩ := h
  change extPerm ε₄ (carmichaelPerm k) ∈ ({c₂, c₃} : Set (Equiv.Perm (Fin 8)))
  rw [h']
  obtain ⟨⟨kv, hk⟩, h2⟩ := k
  interval_cases kv
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem H1_std (γ : Equiv.Perm (Fin 8) → F2Vec8)
    (hev : ∀ s ∈ altOn Γ₀, ∑ i, γ s i = 0)
    (hcoc : ∀ s ∈ altOn Γ₀, ∀ t ∈ altOn Γ₀,
      InW (γ (s * t) + γ s + vecAct s (γ t))) :
    ∃ v : F2Vec8, ∑ i, v i = 0 ∧ ∀ s ∈ altOn Γ₀, InW (γ s + vecAct s v + v) := by
  have hγ1 : InW (γ 1) := by
    have h := hcoc 1 (one_mem _) 1 (one_mem _)
    have e : γ 1 + γ 1 + γ 1 = γ 1 := by
      funext i
      simp only [Pi.add_apply]
      grind
    rw [mul_one, vecAct_one, e] at h
    exact h
  have hR1 : ∀ c ∈ altOn Γ₀, c * c * c = 1 →
      InW (γ c + vecAct c (γ c) + vecAct (c * c) (γ c)) := by
    intro c hc hc3
    have hA := hcoc c hc c hc
    have hB := hcoc (c * c) (mul_mem hc hc) c hc
    rw [hc3] at hB
    refine InW.of_eq_add (InW.add hA hB) hγ1 ?_
    funext i
    simp only [Pi.add_apply]
    grind
  have hR3 : ∀ c ∈ altOn Γ₀, ∀ d ∈ altOn Γ₀, c * d * (c * d) = 1 →
      InW ((γ c + vecAct c (γ d)) + vecAct (c * d) (γ c + vecAct c (γ d))) := by
    intro c hc d hd hcd
    have hA := hcoc c hc d hd
    have hB := hcoc (c * d) (mul_mem hc hd) (c * d) (mul_mem hc hd)
    rw [hcd] at hB
    refine InW.of_eq_add (InW.add (InW.add hA (hA.vecAct (c * d))) hB) hγ1 ?_
    funext i
    simp only [vecAct_add, Pi.add_apply]
    grind
  obtain ⟨v, hv, hv2, hv3⟩ := core (γ c₂) (hev _ c₂_mem)
    (hR1 _ c₂_mem (by decide +kernel)) (γ c₃) (hev _ c₃_mem)
    (hR1 _ c₃_mem (by decide +kernel))
    (hR3 _ c₂_mem _ c₃_mem (by decide +kernel))
  refine ⟨v, hv, fun s hs => ?_⟩
  have hcl : Subgroup.closure ({c₂, c₃} : Set (Equiv.Perm (Fin 8))) ≤
      altOn Γ₀ := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [c₂_mem, c₃_mem]
  have hsc := altOn_Γ₀_le_closure hs
  clear hs
  induction hsc using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    exacts [hv2, hv3]
  | one =>
    refine InW.of_eq_add hγ1 InW.zero ?_
    funext i
    simp only [Pi.add_apply, vecAct_one, Pi.zero_apply]
    grind
  | mul x y hx hy ihx ihy =>
    refine InW.of_eq_add (InW.add (hcoc x (hcl hx) y (hcl hy)) ihx) (ihy.vecAct x) ?_
    funext i
    simp only [vecAct_add, vecAct_mul, Pi.add_apply]
    grind
  | inv x hx ihx =>
    have hc := hcoc x⁻¹ (inv_mem (hcl hx)) x (hcl hx)
    rw [inv_mul_cancel] at hc
    refine InW.of_eq_add (InW.add hc hγ1) (ihx.vecAct x⁻¹) ?_
    funext i
    simp only [vecAct_add, vecAct_inv_vecAct, Pi.add_apply]
    grind

theorem vecAct_vecAct_inv (s : Equiv.Perm (Fin 8)) (f : F2Vec8) :
    vecAct s (vecAct s⁻¹ f) = f := by
  simpa using vecAct_inv_vecAct s⁻¹ f

theorem H1 {Γ : Finset (Fin 8)} (hΓ : Γ.card = 4) (γ : Equiv.Perm (Fin 8) → F2Vec8)
    (hev : ∀ s ∈ altOn Γ, ∑ i, γ s i = 0)
    (hcoc : ∀ s ∈ altOn Γ, ∀ t ∈ altOn Γ, InW (γ (s * t) + γ s + vecAct s (γ t))) :
    ∃ v : F2Vec8, ∑ i, v i = 0 ∧ ∀ s ∈ altOn Γ, InW (γ s + vecAct s v + v) := by
  obtain ⟨σ, rfl⟩ := exists_perm_image_eq (Γ := Γ₀) (Γ' := Γ) (by rw [hΓ, Γ₀_card])
  have hconj : ∀ s₀ ∈ altOn Γ₀, σ * s₀ * σ⁻¹ ∈ altOn (Γ₀.image σ) := by
    intro s₀ hs₀
    rw [mem_altOn_image_iff]
    have e : σ⁻¹ * (σ * s₀ * σ⁻¹) * σ = s₀ := by group
    rwa [e]
  have hev₀ : ∀ s ∈ altOn Γ₀, ∑ i, (fun s => vecAct σ⁻¹ (γ (σ * s * σ⁻¹))) s i = 0 := by
    intro s hs
    show ∑ i, vecAct σ⁻¹ (γ (σ * s * σ⁻¹)) i = 0
    rw [sum_vecAct]
    exact hev _ (hconj s hs)
  have hcoc₀ : ∀ s ∈ altOn Γ₀, ∀ t ∈ altOn Γ₀,
      InW ((fun s => vecAct σ⁻¹ (γ (σ * s * σ⁻¹))) (s * t) +
        (fun s => vecAct σ⁻¹ (γ (σ * s * σ⁻¹))) s +
        vecAct s ((fun s => vecAct σ⁻¹ (γ (σ * s * σ⁻¹))) t)) := by
    intro s hs t ht
    have h := (hcoc _ (hconj s hs) _ (hconj t ht)).vecAct σ⁻¹
    have e1 : σ * s * σ⁻¹ * (σ * t * σ⁻¹) = σ * (s * t) * σ⁻¹ := by group
    have e2 : σ⁻¹ * (σ * s * σ⁻¹) = s * σ⁻¹ := by group
    rw [vecAct_add, vecAct_add, e1, ← vecAct_mul σ⁻¹ (σ * s * σ⁻¹), e2, vecAct_mul s σ⁻¹] at h
    exact h
  obtain ⟨v₀, hv₀, hv₀'⟩ := H1_std (fun s => vecAct σ⁻¹ (γ (σ * s * σ⁻¹))) hev₀ hcoc₀
  refine ⟨vecAct σ v₀, by rwa [sum_vecAct], fun s hs => ?_⟩
  have hs₀ : σ⁻¹ * s * σ ∈ altOn Γ₀ := (mem_altOn_image_iff σ _ s).1 hs
  have h := (hv₀' _ hs₀).vecAct σ
  beta_reduce at h
  have e1 : σ * (σ⁻¹ * s * σ) * σ⁻¹ = s := by group
  have e2 : σ * (σ⁻¹ * s * σ) = s * σ := by group
  rw [vecAct_add, vecAct_add, e1, ← vecAct_mul σ (σ⁻¹ * s * σ), e2, vecAct_mul s σ,
    vecAct_vecAct_inv] at h
  exact h

end Ev8

open Ev8

structure EvenModule {X : Type} [Group X] (π : X →* Equiv.Perm (Fin 8))
    (β : Multiplicative (Fin 8 → ZMod 2) →* X) : Prop where
  mem_ker : ∀ g : X, g ∈ π.ker ↔
    ∃ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 ∧ β f = g
  beta_eq_one : ∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
    (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1)
  conj : ∀ (g : X) (f : Multiplicative (Fin 8 → ZMod 2)), ∑ i, f.toAdd i = 0 →
    g * β f * g⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((π g).symm i))

section Module

variable {X : Type} [Group X] {π : X →* Equiv.Perm (Fin 8)}
  {β : Multiplicative (Fin 8 → ZMod 2) →* X}

@[expose] def Ev8.bv (β : Multiplicative (Fin 8 → ZMod 2) →* X) (f : F2Vec8) : X :=
  β (Multiplicative.ofAdd f)

theorem Ev8.bv_add (f g : F2Vec8) : bv β (f + g) = bv β f * bv β g := by
  simp [bv, ofAdd_add]

theorem Ev8.bv_zero : bv β 0 = 1 := by simp [bv]

theorem Ev8.bv_self (f : F2Vec8) : bv β f * bv β f = 1 := by
  rw [← bv_add, vec_add_self, bv_zero]

theorem Ev8.bv_comm (f g : F2Vec8) : bv β f * bv β g = bv β g * bv β f := by
  rw [← bv_add, ← bv_add, add_comm]

theorem Ev8.bv_inv (f : F2Vec8) : (bv β f)⁻¹ = bv β f := inv_eq_of_mul_eq_one_right (bv_self f)

theorem EvenModule.bv_mem_ker (hM : EvenModule π β) {f : F2Vec8} (hf : ∑ i, f i = 0) :
    bv β f ∈ π.ker := (hM.mem_ker _).2 ⟨Multiplicative.ofAdd f, hf, rfl⟩

theorem EvenModule.bv_conj (hM : EvenModule π β) (g : X) {f : F2Vec8} (hf : ∑ i, f i = 0) :
    g * bv β f * g⁻¹ = bv β (vecAct (π g) f) := hM.conj g (Multiplicative.ofAdd f) hf

theorem EvenModule.bv_eq_one_iff (hM : EvenModule π β) {f : F2Vec8} (hf : ∑ i, f i = 0) :
    bv β f = 1 ↔ InW f := hM.beta_eq_one (Multiplicative.ofAdd f) hf

theorem EvenModule.bv_eq_iff (hM : EvenModule π β) {f g : F2Vec8} (hf : ∑ i, f i = 0)
    (hg : ∑ i, g i = 0) : bv β f = bv β g ↔ InW (f + g) := by
  have hfg : ∑ i, (f + g) i = 0 := by simp [Finset.sum_add_distrib, hf, hg]
  rw [← hM.bv_eq_one_iff hfg, bv_add]
  constructor
  · intro h
    rw [h, bv_self]
  · intro h
    have := congrArg (· * bv β g) h
    simpa [mul_assoc, bv_self] using this

theorem exists_vec_of_mem_ker (hM : EvenModule π β) {g : X} (hg : g ∈ π.ker) :
    ∃ f : F2Vec8, ∑ i, f i = 0 ∧ bv β f = g := by
  obtain ⟨f, hf, rfl⟩ := (hM.mem_ker g).1 hg
  exact ⟨f.toAdd, hf, rfl⟩

end Module

section Sections

variable {X : Type} [Group X]

theorem ae8k_eq_of_map_eq (ρ : X →* Equiv.Perm (Fin 8)) {B : Subgroup X} (hB : B ⊓ ρ.ker = ⊥)
    {a b : X} (ha : a ∈ B) (hb : b ∈ B) (h : ρ a = ρ b) : a = b := by
  have h1 : a⁻¹ * b ∈ B ⊓ ρ.ker := ⟨B.mul_mem (B.inv_mem ha) hb, MonoidHom.mem_ker.2 (by
    rw [map_mul, map_inv, h, inv_mul_cancel])⟩
  rw [hB, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.1 h1

open Classical in
noncomputable def ae8k_secOf (ρ : X →* Equiv.Perm (Fin 8)) (B : Subgroup X)
    (s : Equiv.Perm (Fin 8)) : X :=
  if h : ∃ b ∈ B, ρ b = s then h.choose else 1

theorem ae8k_secOf_spec {ρ : X →* Equiv.Perm (Fin 8)} {B : Subgroup X} {s : Equiv.Perm (Fin 8)}
    (h : ∃ b ∈ B, ρ b = s) : ae8k_secOf ρ B s ∈ B ∧ ρ (ae8k_secOf ρ B s) = s := by
  rw [ae8k_secOf, dif_pos h]
  exact h.choose_spec

theorem ae8k_secOf_eq {ρ : X →* Equiv.Perm (Fin 8)} {B : Subgroup X} (hB : B ⊓ ρ.ker = ⊥) {b : X}
    (hb : b ∈ B) : ae8k_secOf ρ B (ρ b) = b :=
  ae8k_eq_of_map_eq ρ hB (ae8k_secOf_spec ⟨b, hb, rfl⟩).1 hb (ae8k_secOf_spec ⟨b, hb, rfl⟩).2

theorem ae8k_secOf_mul {ρ : X →* Equiv.Perm (Fin 8)} {B : Subgroup X} (hB : B ⊓ ρ.ker = ⊥)
    {s t : Equiv.Perm (Fin 8)} (hs : ∃ b ∈ B, ρ b = s) (ht : ∃ b ∈ B, ρ b = t) :
    ae8k_secOf ρ B (s * t) = ae8k_secOf ρ B s * ae8k_secOf ρ B t := by
  have h1 := ae8k_secOf_spec hs
  have h2 := ae8k_secOf_spec ht
  have h : s * t = ρ (ae8k_secOf ρ B s * ae8k_secOf ρ B t) := by rw [map_mul, h1.2, h2.2]
  rw [h]
  exact ae8k_secOf_eq hB (B.mul_mem h1.1 h2.1)

variable {π : X →* Equiv.Perm (Fin 8)} {β : Multiplicative (Fin 8 → ZMod 2) →* X}

theorem exists_conj_of_complements (hM : EvenModule π β) {Γ : Finset (Fin 8)}
    (hΓ : Γ.card = 4) (B B' : Subgroup X) (hB : B ⊓ π.ker = ⊥) (hB' : B' ⊓ π.ker = ⊥)
    (hBπ : B.map π = altOn Γ) (hB'π : B'.map π = altOn Γ) :
    ∃ v ∈ π.ker, B' = B.map (MulAut.conj v).toMonoidHom := by
  classical
  have hex : ∀ s ∈ altOn Γ, ∃ b ∈ B, π b = s := fun s hs => by
    rw [← hBπ] at hs
    obtain ⟨b, hb, h⟩ := Subgroup.mem_map.1 hs
    exact ⟨b, hb, h⟩
  have hex' : ∀ s ∈ altOn Γ, ∃ b ∈ B', π b = s := fun s hs => by
    rw [← hB'π] at hs
    obtain ⟨b, hb, h⟩ := Subgroup.mem_map.1 hs
    exact ⟨b, hb, h⟩
  have hker : ∀ s ∈ altOn Γ, ae8k_secOf π B' s * (ae8k_secOf π B s)⁻¹ ∈ π.ker := by
    intro s hs
    rw [MonoidHom.mem_ker, map_mul, map_inv, (ae8k_secOf_spec (hex' s hs)).2,
      (ae8k_secOf_spec (hex s hs)).2, mul_inv_cancel]
  let γ : Equiv.Perm (Fin 8) → F2Vec8 := fun s =>
    if h : s ∈ altOn Γ then (exists_vec_of_mem_ker hM (hker s h)).choose else 0
  have hγ : ∀ s ∈ altOn Γ, ∑ i, γ s i = 0 ∧
      bv β (γ s) = ae8k_secOf π B' s * (ae8k_secOf π B s)⁻¹ := by
    intro s hs
    simp only [γ, dif_pos hs]
    exact (exists_vec_of_mem_ker hM (hker s hs)).choose_spec
  have hcoc : ∀ s ∈ altOn Γ, ∀ t ∈ altOn Γ, InW (γ (s * t) + γ s + vecAct s (γ t)) := by
    intro s hs t ht
    obtain ⟨hs1, hs2⟩ := hγ s hs
    obtain ⟨ht1, ht2⟩ := hγ t ht
    obtain ⟨hst1, hst2⟩ := hγ (s * t) (mul_mem hs ht)
    have hconj := hM.bv_conj (ae8k_secOf π B s) ht1
    rw [(ae8k_secOf_spec (hex s hs)).2] at hconj
    have e : bv β (γ (s * t)) = bv β (γ s + vecAct s (γ t)) := by
      rw [bv_add, hst2, ae8k_secOf_mul hB' (hex' s hs) (hex' t ht),
        ae8k_secOf_mul hB (hex s hs) (hex t ht), hs2, ← hconj, ht2]
      group
    have hsum : ∑ i, (γ s + vecAct s (γ t)) i = 0 := by
      simp [Finset.sum_add_distrib, sum_vecAct, hs1, ht1]
    have := (hM.bv_eq_iff hst1 hsum).1 e
    rwa [← add_assoc] at this
  obtain ⟨v, hv, hv'⟩ := Ev8.H1 hΓ γ (fun s hs => (hγ s hs).1) hcoc
  have hw : bv β v ∈ π.ker := hM.bv_mem_ker hv
  have key : ∀ b ∈ B, ae8k_secOf π B' (π b) = bv β v * b * (bv β v)⁻¹ := by
    intro b hb
    have hs : π b ∈ altOn Γ := hBπ ▸ Subgroup.mem_map_of_mem π hb
    obtain ⟨hs1, hs2⟩ := hγ (π b) hs
    have hb' : ae8k_secOf π B (π b) = b := ae8k_secOf_eq hB hb
    rw [hb'] at hs2
    have hsum : ∑ i, (vecAct (π b) v + v) i = 0 := by
      simp [Finset.sum_add_distrib, sum_vecAct, hv]
    have e : bv β (γ (π b)) = bv β (vecAct (π b) v + v) :=
      (hM.bv_eq_iff hs1 hsum).2 (by rw [← add_assoc]; exact hv' _ hs)
    have hc := hM.bv_conj b hv
    rw [bv_add, ← hc, hs2] at e
    have e2 : ae8k_secOf π B' (π b) = b * bv β v * b⁻¹ * bv β v * b := by
      rw [← e]
      group
    rw [e2]
    have hcomm : bv β (vecAct (π b) v) * bv β v = bv β v * bv β (vecAct (π b) v) := bv_comm _ _
    rw [← hc] at hcomm
    calc b * bv β v * b⁻¹ * bv β v * b = (b * bv β v * b⁻¹ * bv β v) * b := by group
      _ = (bv β v * (b * bv β v * b⁻¹)) * b := by rw [hcomm]
      _ = bv β v * b * (bv β v)⁻¹ := by rw [bv_inv v]; group
  refine ⟨bv β v, hw, le_antisymm ?_ ?_⟩
  · intro x hx
    have hs : π x ∈ altOn Γ := hB'π ▸ Subgroup.mem_map_of_mem π hx
    obtain ⟨b, hb, hbs⟩ := hex _ hs
    have hxb : ae8k_secOf π B' (π b) = x := by
      rw [hbs]
      exact ae8k_secOf_eq hB' hx
    refine Subgroup.mem_map.2 ⟨b, hb, ?_⟩
    rw [← hxb, key b hb]
    simp [MulAut.conj_apply]
  · rintro _ hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
    have := (ae8k_secOf_spec (hex' _ (hBπ ▸ Subgroup.mem_map_of_mem π hb))).1
    rw [key b hb] at this
    simpa [MulAut.conj_apply] using this

theorem exists_emb_of_card_four {T : Finset (Fin 8)} (hT : T.card = 4) :
    ∃ ε : Fin 4 ↪ Fin 8, Finset.univ.image ε = T := by
  refine ⟨(T.orderEmbOfFin hT).toEmbedding, ?_⟩
  ext x
  have := Finset.range_orderEmbOfFin T hT
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact Finset.orderEmbOfFin_mem T hT i
  · intro hx
    have hx' : x ∈ Set.range (T.orderEmbOfFin hT) := by rw [this]; exact hx
    exact hx'

theorem le_of_cube_eq_one {ρ : X →* Equiv.Perm (Fin 8)} {T : Finset (Fin 8)} (hT : T.card = 4)
    {B : Subgroup X} (hB : B ⊓ ρ.ker = ⊥) (hBρ : B.map ρ = altOn T) (Z : Subgroup X)
    (hZ : ∀ b ∈ B, b ^ 3 = 1 → b ∈ Z) : B ≤ Z := by
  obtain ⟨ε, hε⟩ := exists_emb_of_card_four hT
  subst hε
  have hle : altOn (Finset.univ.image ε) ≤ (Z ⊓ B).map ρ := by
    refine (altOn_le_closure_extPerm ε).trans ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨k, rfl⟩
    have hg : extPerm ε (carmichaelPerm k) ∈ B.map ρ := by
      rw [hBρ]
      exact extPerm_mem_altOn ε (carmichaelCycle k)
    obtain ⟨b, hb, hbg⟩ := Subgroup.mem_map.1 hg
    have hc3 : carmichaelPerm k ^ 3 = 1 := by
      have := congrArg Subtype.val (carmichaelCycle_pow_three k)
      simpa [carmichaelCycle] using this
    have hb3 : b ^ 3 = 1 := by
      have h3 : ρ (b ^ 3) = 1 := by rw [map_pow, hbg, ← map_pow, hc3, map_one]
      have hmem : b ^ 3 ∈ B ⊓ ρ.ker := ⟨B.pow_mem hb 3, MonoidHom.mem_ker.2 h3⟩
      rw [hB, Subgroup.mem_bot] at hmem
      exact hmem
    exact Subgroup.mem_map.2 ⟨b, ⟨hZ b hb hb3, hb⟩, hbg⟩
  intro b hb
  have hρb : ρ b ∈ altOn (Finset.univ.image ε) := hBρ ▸ Subgroup.mem_map_of_mem ρ hb
  obtain ⟨z, ⟨hzZ, hzB⟩, hz⟩ := Subgroup.mem_map.1 (hle hρb)
  rw [← ae8k_eq_of_map_eq ρ hB hzB hb hz]
  exact hzZ

theorem commute_cube {π : X →* Equiv.Perm (Fin 8)} {β : Multiplicative (Fin 8 → ZMod 2) →* X}
    (hM : EvenModule π β) {T₁ T₂ : Finset (Fin 8)} (h₁ : T₁.card = 4) (h₂ : T₂.card = 4)
    (hT : Disjoint T₁ T₂) {B₁ B₂ : Subgroup X} (hB₁ : B₁ ⊓ π.ker = ⊥)
    (hB₂ : B₂ ⊓ π.ker = ⊥) (hB₁π : B₁.map π = altOn T₁) (hB₂π : B₂.map π = altOn T₂)
    {y : X} (hy : y ∈ B₂) (hy3 : y ^ 3 = 1) : ∀ x ∈ B₁, x * y = y * x := by
  have hπy : π y ∈ altOn T₂ := hB₂π ▸ Subgroup.mem_map_of_mem π hy
  have hπb : ∀ b ∈ B₁, π b ∈ altOn T₁ := fun b hb => hB₁π ▸ Subgroup.mem_map_of_mem π hb
  have hπcomm : ∀ b ∈ B₁, π (y * b * y⁻¹) = π b := by
    intro b hb
    rw [map_mul, map_mul, map_inv, ← altOn_comm hT (hπb b hb) hπy, mul_inv_cancel_right]
  let C : Subgroup X := B₁.map (MulAut.conj y).toMonoidHom
  have hCker : C ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzC, hzk⟩
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hzC
    have hb1 : π b = 1 := by
      rw [← hπcomm b hb]
      exact MonoidHom.mem_ker.1 hzk
    have hbk : b ∈ B₁ ⊓ π.ker := ⟨hb, MonoidHom.mem_ker.2 hb1⟩
    rw [hB₁, Subgroup.mem_bot] at hbk
    subst hbk
    simp
  have hCπ : C.map π = altOn T₁ := by
    ext s
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hc
      have : π ((MulAut.conj y).toMonoidHom b) = π b := hπcomm b hb
      rw [this]
      exact hπb b hb
    · intro hs
      rw [← hB₁π] at hs
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hs
      exact ⟨(MulAut.conj y).toMonoidHom b, Subgroup.mem_map_of_mem _ hb, hπcomm b hb⟩
  obtain ⟨w, hw, hCw⟩ := exists_conj_of_complements hM h₁ B₁ C hB₁ hCker hB₁π hCπ
  have hπw : π w = 1 := MonoidHom.mem_ker.1 hw
  have hn : ∀ x ∈ B₁, w⁻¹ * y * x * (w⁻¹ * y)⁻¹ = x := by
    intro x hx
    have hxC : y * x * y⁻¹ ∈ C := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    rw [hCw] at hxC
    obtain ⟨x₁, hx₁, hxx₁⟩ := Subgroup.mem_map.1 hxC
    have hxx₁' : w * x₁ * w⁻¹ = y * x * y⁻¹ := hxx₁
    have hπx₁ : π x₁ = π x := by
      have := congrArg π hxx₁'
      rw [map_mul, map_mul, map_inv, hπw, one_mul, inv_one, mul_one, hπcomm x hx] at this
      exact this.symm ▸ rfl
    have hx₁x : x₁ = x := ae8k_eq_of_map_eq π hB₁ hx₁ hx hπx₁
    have : w⁻¹ * y * x * (w⁻¹ * y)⁻¹ = w⁻¹ * (y * x * y⁻¹) * w := by group
    rw [this, ← hxx₁', hx₁x]
    group
  obtain ⟨f, hf, hwf⟩ := exists_vec_of_mem_ker hM hw
  have hπn : π (w⁻¹ * y) = π y := by rw [map_mul, map_inv, hπw, inv_one, one_mul]
  obtain ⟨n, hn_def⟩ : ∃ n : X, n = w⁻¹ * y := ⟨_, rfl⟩
  rw [← hn_def] at hn hπn
  have hy_eq : y = w * n := by rw [hn_def, mul_inv_cancel_left]
  have hxn : ∀ x ∈ B₁, x * n = n * x := fun x hx => by
    have := hn x hx
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hf1 : ∑ i, vecAct (π y) f i = 0 := by rw [sum_vecAct]; exact hf
  have hf2 : ∑ i, vecAct (π y) (vecAct (π y) f) i = 0 := by rw [sum_vecAct]; exact hf1
  have e1 : n * w * n⁻¹ = bv β (vecAct (π y) f) := by rw [← hwf, hM.bv_conj n hf, hπn]
  have e2 : n * (n * w * n⁻¹) * n⁻¹ = bv β (vecAct (π y) (vecAct (π y) f)) := by
    rw [e1, hM.bv_conj n hf1, hπn]
  have hF : ∑ i, (f + vecAct (π y) f + vecAct (π y) (vecAct (π y) f)) i = 0 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, hf, hf1, hf2, add_zero]
  have hu : w * (n * w * n⁻¹) * (n * (n * w * n⁻¹) * n⁻¹) =
      bv β (f + vecAct (π y) f + vecAct (π y) (vecAct (π y) f)) := by
    rw [e2, e1, ← hwf, ← bv_add, ← bv_add]
  have e3 : (w * n) ^ 3 = w * (n * w * n⁻¹) * (n * (n * w * n⁻¹) * n⁻¹) * n ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  have hu3 : bv β (f + vecAct (π y) f + vecAct (π y) (vecAct (π y) f)) * n ^ 3 = 1 := by
    rw [← hu, ← e3, ← hy_eq]
    exact hy3
  have hu' := eq_inv_of_mul_eq_one_left hu3
  have hT₂ : T₂.Nonempty := Finset.card_pos.1 (by omega)
  have hcentW : ∀ x ∈ B₁, x * w = w * x := by
    intro x hx
    have hc : Commute x ((n ^ 3)⁻¹) := ((Commute.pow_right (hxn x hx) 3)).inv_right
    have h1 : x * bv β (f + vecAct (π y) f + vecAct (π y) (vecAct (π y) f)) * x⁻¹ =
        bv β (f + vecAct (π y) f + vecAct (π y) (vecAct (π y) f)) := by
      rw [hu', hc.eq, mul_inv_cancel_right]
    have h2 : bv β (vecAct (π x) (f + vecAct (π y) f + vecAct (π y) (vecAct (π y) f))) =
        bv β (f + vecAct (π y) f + vecAct (π y) (vecAct (π y) f)) := by
      rw [← hM.bv_conj x hF]
      exact h1
    have hFx : ∑ i, (vecAct (π x) (f + vecAct (π y) f +
        vecAct (π y) (vecAct (π y) f))) i = 0 := by rw [sum_vecAct]; exact hF
    have h3 := (hM.bv_eq_iff hFx hF).1 h2
    have h4 : vecAct (π x) f = f := vec_aux hT hT₂ (hπb x hx) hπy f h3
    have h5 : x * w * x⁻¹ = w := by
      rw [← hwf, hM.bv_conj x hf, h4]
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5
  intro x hx
  calc x * y = x * (w * n) := by rw [← hy_eq]
    _ = (x * w) * n := by rw [mul_assoc]
    _ = (w * x) * n := by rw [hcentW x hx]
    _ = w * (x * n) := by rw [mul_assoc]
    _ = w * (n * x) := by rw [hxn x hx]
    _ = y * x := by rw [hy_eq, mul_assoc]

theorem commute_of_complements {π : X →* Equiv.Perm (Fin 8)}
    {β : Multiplicative (Fin 8 → ZMod 2) →* X} (hM : EvenModule π β) {T₁ T₂ : Finset (Fin 8)}
    (h₁ : T₁.card = 4) (h₂ : T₂.card = 4) (hT : Disjoint T₁ T₂) {B₁ B₂ : Subgroup X}
    (hB₁ : B₁ ⊓ π.ker = ⊥) (hB₂ : B₂ ⊓ π.ker = ⊥) (hB₁π : B₁.map π = altOn T₁)
    (hB₂π : B₂.map π = altOn T₂) : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x := by
  have hle : B₂ ≤ Subgroup.centralizer (B₁ : Set X) := by
    refine le_of_cube_eq_one h₂ hB₂ hB₂π _ (fun y hy hy3 => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact commute_cube hM h₁ h₂ hT hB₁ hB₂ hB₁π hB₂π hy hy3 x hx
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hy)) x hx

end Sections

namespace Glue8

variable {X : Type} [Group X]

@[expose] def SectionsConj (ρ : X →* Equiv.Perm (Fin 8)) : Prop :=
  ∀ Γ : Finset (Fin 8), Γ.card = 4 → ∀ B B' : Subgroup X, B ⊓ ρ.ker = ⊥ → B' ⊓ ρ.ker = ⊥ →
    B.map ρ = altOn Γ → B'.map ρ = altOn Γ →
    ∃ v ∈ ρ.ker, B' = B.map (MulAut.conj v).toMonoidHom

@[expose] def SectionsComm (ρ : X →* Equiv.Perm (Fin 8)) : Prop :=
  ∀ T₁ T₂ : Finset (Fin 8), T₁.card = 4 → T₂.card = 4 → Disjoint T₁ T₂ →
    ∀ B₁ B₂ : Subgroup X, B₁ ⊓ ρ.ker = ⊥ → B₂ ⊓ ρ.ker = ⊥ → B₁.map ρ = altOn T₁ →
      B₂.map ρ = altOn T₂ → ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x

theorem section_inf {ρ : X →* Equiv.Perm (Fin 8)} {H : Subgroup X} {S T : Finset (Fin 8)}
    (hH : H ⊓ ρ.ker = ⊥) (hHρ : H.map ρ = altOn S) (hTS : T ⊆ S) :
    (H ⊓ (altOn T).comap ρ) ⊓ ρ.ker = ⊥ ∧ (H ⊓ (altOn T).comap ρ).map ρ = altOn T := by
  constructor
  · rw [eq_bot_iff]
    intro x hx
    have : x ∈ H ⊓ ρ.ker := ⟨hx.1.1, hx.2⟩
    rwa [hH] at this
  · ext s
    constructor
    · rintro ⟨h, ⟨_, hh⟩, rfl⟩
      exact hh
    · intro hs
      have : s ∈ H.map ρ := hHρ ▸ altOn_mono hTS hs
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 this
      exact ⟨h, ⟨hh, hs⟩, rfl⟩

theorem section_conj {ρ : X →* Equiv.Perm (Fin 8)} {H : Subgroup X} {S : Finset (Fin 8)}
    (hH : H ⊓ ρ.ker = ⊥) (hHρ : H.map ρ = altOn S) (g : X) :
    H.map (MulAut.conj g).toMonoidHom ⊓ ρ.ker = ⊥ ∧
      (H.map (MulAut.conj g).toMonoidHom).map ρ = altOn (S.image (ρ g)) := by
  constructor
  · rw [eq_bot_iff]
    rintro z ⟨hzC, hzk⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hzC
    have h1 : ρ g * ρ h * (ρ g)⁻¹ = 1 := by
      have := MonoidHom.mem_ker.1 hzk
      simpa [MulAut.conj_apply] using this
    have hρh : ρ h = 1 := by
      have : ρ h = (ρ g)⁻¹ * (ρ g * ρ h * (ρ g)⁻¹) * ρ g := by group
      rw [this, h1]
      group
    have hmem : h ∈ H ⊓ ρ.ker := ⟨hh, MonoidHom.mem_ker.2 hρh⟩
    rw [hH, Subgroup.mem_bot] at hmem
    subst hmem
    simp
  · ext s
    rw [mem_altOn_image_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hc
      have : (ρ g)⁻¹ * ρ ((MulAut.conj g).toMonoidHom h) * ρ g = ρ h := by
        simp [MulAut.conj_apply]
        group
      rw [this, ← hHρ]
      exact Subgroup.mem_map_of_mem ρ hh
    · intro hs
      rw [← hHρ] at hs
      obtain ⟨h, hh, hρh⟩ := Subgroup.mem_map.1 hs
      refine ⟨(MulAut.conj g).toMonoidHom h, Subgroup.mem_map_of_mem _ hh, ?_⟩
      have : ρ h = (ρ g)⁻¹ * s * ρ g := hρh
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, this]
      group

theorem exists_hom_section (ρ : X →* Equiv.Perm (Fin 8)) (ε : Fin 6 ↪ Fin 8) {H : Subgroup X}
    (hH : H ⊓ ρ.ker = ⊥) (hHρ : H.map ρ = altOn (Finset.univ.image ε)) :
    ∃ f : alternatingGroup (Fin 6) →* X, (∀ a, f a ∈ H) ∧
      ∀ a, ρ (f a) = extPerm ε (a : Equiv.Perm (Fin 6)) := by
  classical
  have hex : ∀ a : alternatingGroup (Fin 6),
      ∃ h ∈ H, ρ h = extPerm ε (a : Equiv.Perm (Fin 6)) := by
    intro a
    have : extPerm ε (a : Equiv.Perm (Fin 6)) ∈ H.map ρ := hHρ ▸ extPerm_mem_altOn ε a
    obtain ⟨h, hh, e⟩ := Subgroup.mem_map.1 this
    exact ⟨h, hh, e⟩
  choose g hgH hgρ using hex
  refine ⟨MonoidHom.mk' g (fun a b => ?_), hgH, hgρ⟩
  apply ae8k_eq_of_map_eq ρ hH (hgH _) (H.mul_mem (hgH a) (hgH b))
  rw [map_mul, hgρ, hgρ, hgρ]
  simp [map_mul]

@[expose] def chart₁ : Fin 6 ↪ Fin 8 := Fin.castLEEmb (by norm_num)

@[expose] def relabel : Equiv.Perm (Fin 8) := Equiv.swap 4 6 * Equiv.swap 5 7

@[expose] def chart₂ : Fin 6 ↪ Fin 8 := chart₁.trans relabel.toEmbedding

@[expose] def Tc₁ : Finset (Fin 8) := {0, 2, 4, 5}

@[expose] def Tc₂ : Finset (Fin 8) := {1, 3, 6, 7}

theorem relabel_mem : relabel ∈ altOn ({4, 5, 6, 7} : Finset (Fin 8)) :=
  ⟨by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel, by decide +kernel⟩

theorem exists_altExt_carmichael {ε : Fin 6 ↪ Fin 8} (h0 : ε ⟨0, by omega⟩ = ⟨0, by omega⟩)
    (h1 : ε ⟨1, by omega⟩ = ⟨1, by omega⟩) (k : CarmichaelIndex 8)
    (hk : k.1 ∈ Set.range ε) : ∃ σ : alternatingGroup (Fin 6), altExt ε σ = carmichaelCycle k := by
  obtain ⟨j, hj⟩ := hk
  have hj2 : 2 ≤ (j : ℕ) := two_le_of_image ε (by norm_num) (by norm_num) h0 h1 hj
  refine ⟨carmichaelCycle ⟨j, hj2⟩, ?_⟩
  rw [altExt_carmichaelCycle (by norm_num) (by norm_num) ε h0 h1]
  exact congrArg carmichaelCycle (Subtype.ext hj)

theorem exists_section_std (ρ : X →* Equiv.Perm (Fin 8))
    (hρ : ρ.range = alternatingGroup (Fin 8)) (hC : SectionsConj ρ) (hX : SectionsComm ρ)
    {H₀ : Subgroup X} (hH₀ : H₀ ⊓ ρ.ker = ⊥)
    (hH₀ρ : H₀.map ρ = altOn (Finset.univ.image chart₁)) :
    ∃ f : alternatingGroup (Fin 8) →* X,
      (∀ a, ρ (f a) = (a : Equiv.Perm (Fin 8))) ∧ H₀ ≤ f.range := by
  classical
  obtain ⟨f₁, hf₁H, hf₁ρ⟩ := exists_hom_section ρ chart₁ hH₀ hH₀ρ
  have hr : relabel ∈ ρ.range := by
    rw [hρ, Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  obtain ⟨g₀, hg₀⟩ := hr
  have hΓ₀S : Ev8.Γ₀ ⊆ Finset.univ.image chart₁ := by decide +kernel
  obtain ⟨hB₀, hB₀ρ⟩ := section_inf hH₀ hH₀ρ hΓ₀S
  obtain ⟨hB₀', hB₀'ρ⟩ := section_conj hB₀ hB₀ρ g₀
  rw [hg₀] at hB₀'ρ
  have himg : Ev8.Γ₀.image relabel = Ev8.Γ₀ := by decide +kernel
  rw [himg] at hB₀'ρ
  obtain ⟨v, hv, hvB⟩ := hC Ev8.Γ₀ Ev8.Γ₀_card _ _ hB₀' hB₀ hB₀'ρ hB₀ρ
  have hρg : ρ (v * g₀) = relabel := by rw [map_mul, MonoidHom.mem_ker.1 hv, one_mul, hg₀]
  have hgB : ∀ b ∈ H₀ ⊓ (altOn Ev8.Γ₀).comap ρ, v * g₀ * b * (v * g₀)⁻¹ ∈
      H₀ ⊓ (altOn Ev8.Γ₀).comap ρ := by
    intro b hb
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj g₀).toMonoidHom hb
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj v).toMonoidHom h1
    rw [← hvB] at h2
    have e : (MulAut.conj v).toMonoidHom ((MulAut.conj g₀).toMonoidHom b) =
        v * g₀ * b * (v * g₀)⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [e] at h2
  obtain ⟨hH₁, hH₁ρ⟩ := section_conj hH₀ hH₀ρ (v * g₀)
  rw [hρg] at hH₁ρ
  have himg2 : (Finset.univ.image chart₁).image relabel = Finset.univ.image chart₂ := by
    decide +kernel
  rw [himg2] at hH₁ρ
  obtain ⟨f₂, hf₂H, hf₂ρ⟩ := exists_hom_section ρ chart₂ hH₁ hH₁ρ
  have hr₁ : ∀ x, x ∈ Set.range chart₁ ↔ x ≠ 6 ∧ x ≠ 7 := by
    intro x
    simp only [Set.mem_range]
    revert x
    decide +kernel
  have hr₂ : ∀ x, x ∈ Set.range chart₂ ↔ x ≠ 4 ∧ x ≠ 5 := by
    intro x
    simp only [Set.mem_range]
    revert x
    decide +kernel
  have hcommon : ∀ x : Fin 8, x ∉ Ev8.Γ₀ → x ∈ Set.range chart₁ → x ∉ Set.range chart₂ := by
    intro x
    simp only [Set.mem_range]
    revert x
    decide +kernel
  have hdisj : Disjoint Ev8.Γ₀ ({4, 5, 6, 7} : Finset (Fin 8)) := by decide +kernel
  have hagree : ∀ σ σ' : alternatingGroup (Fin 6), altExt chart₁ σ = altExt chart₂ σ' →
      f₁ σ = f₂ σ' := by
    intro σ σ' hσσ'
    have hπ : extPerm chart₁ (σ : Equiv.Perm (Fin 6)) =
        extPerm chart₂ (σ' : Equiv.Perm (Fin 6)) := congrArg Subtype.val hσσ'
    have hπΓ : extPerm chart₁ (σ : Equiv.Perm (Fin 6)) ∈ altOn Ev8.Γ₀ := by
      refine ⟨(altExt chart₁ σ).2, fun x hx => ?_⟩
      by_cases hx₁ : x ∈ Set.range chart₁
      · rw [hπ]
        exact extPerm_apply_not_mem _ _ (hcommon x hx hx₁)
      · exact extPerm_apply_not_mem _ _ hx₁
    obtain ⟨h, hh, hfh⟩ := Subgroup.mem_map.1 (hf₂H σ')
    have hρh : ρ h = extPerm chart₁ (σ : Equiv.Perm (Fin 6)) := by
      have e1 : ρ (f₂ σ') = relabel * ρ h * relabel⁻¹ := by
        rw [← hfh]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [map_mul, map_mul, map_inv, hρg]
      have e2 : ρ (f₂ σ') = extPerm chart₁ (σ : Equiv.Perm (Fin 6)) := by rw [hf₂ρ, ← hπ]
      have hcomm := altOn_comm hdisj hπΓ relabel_mem
      have e3 : ρ h = relabel⁻¹ * (relabel * ρ h * relabel⁻¹) * relabel := by group
      rw [e3, ← e1, e2, mul_assoc, hcomm, inv_mul_cancel_left]
    have hhB : h ∈ H₀ ⊓ (altOn Ev8.Γ₀).comap ρ :=
      ⟨hh, Subgroup.mem_comap.2 (by rw [hρh]; exact hπΓ)⟩
    have hf₂B := hgB h hhB
    have e4 : v * g₀ * h * (v * g₀)⁻¹ = f₂ σ' := by
      rw [← hfh]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [e4] at hf₂B
    exact ae8k_eq_of_map_eq ρ hH₀ (hf₁H σ) hf₂B.1 (by rw [hf₁ρ, hf₂ρ, hπ])
  have hcross : ∀ σ σ' : alternatingGroup (Fin 6),
      (∀ x ∉ (Tc₁ : Set (Fin 8)), extPerm chart₁ (σ : Equiv.Perm (Fin 6)) x = x) →
      (∀ x ∉ (Tc₂ : Set (Fin 8)), extPerm chart₂ (σ' : Equiv.Perm (Fin 6)) x = x) →
      f₁ σ * f₂ σ' = f₂ σ' * f₁ σ := by
    intro σ σ' h₁ h₂
    have hT₁S : Tc₁ ⊆ Finset.univ.image chart₁ := by decide +kernel
    have hT₂S : Tc₂ ⊆ Finset.univ.image chart₂ := by decide +kernel
    obtain ⟨hB₁, hB₁ρ⟩ := section_inf hH₀ hH₀ρ hT₁S
    obtain ⟨hB₂, hB₂ρ⟩ := section_inf hH₁ hH₁ρ hT₂S
    have hm₁ : f₁ σ ∈ H₀ ⊓ (altOn Tc₁).comap ρ := ⟨hf₁H σ, Subgroup.mem_comap.2 (by
      rw [hf₁ρ]
      exact ⟨(altExt chart₁ σ).2, fun x hx => h₁ x (by simpa using hx)⟩)⟩
    have hm₂ : f₂ σ' ∈ H₀.map (MulAut.conj (v * g₀)).toMonoidHom ⊓ (altOn Tc₂).comap ρ :=
      ⟨hf₂H σ', Subgroup.mem_comap.2 (by
        rw [hf₂ρ]
        exact ⟨(altExt chart₂ σ').2, fun x hx => h₂ x (by simpa using hx)⟩)⟩
    exact hX Tc₁ Tc₂ (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
      hB₁ hB₂ hB₁ρ hB₂ρ _ hm₁ _ hm₂
  obtain ⟨f, hf1, hf2⟩ := exists_hom_of_two_charts (m := 8) (N := 6) (by norm_num)
    (by norm_num) chart₁ chart₂ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (q₁ := 4) (q₂ := 5) (a' := 2) (c := 3) (p₁ := 6) (p₂ := 7) hr₁ hr₂
    (T₁ := (Tc₁ : Set (Fin 8))) (T₂ := (Tc₂ : Set (Fin 8)))
    (Finset.disjoint_coe.2 (by decide +kernel))
    (Finset.mem_coe.2 (by decide +kernel)) (Finset.mem_coe.2 (by decide +kernel))
    (Finset.mem_coe.2 (by decide +kernel)) (Finset.mem_coe.2 (by decide +kernel))
    (Finset.mem_coe.2 (by decide +kernel)) (Finset.mem_coe.2 (by decide +kernel))
    (Finset.mem_coe.2 (by decide +kernel)) (Finset.mem_coe.2 (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) f₁ f₂ hagree hcross
  have hρf : ∀ a : alternatingGroup (Fin 8), ρ (f a) = a := by
    have hext := hom_ext_carmichaelCycle (n := 8) (by norm_num) (φ := ρ.comp f)
      (ψ := (alternatingGroup (Fin 8)).subtype) (by
        intro k
        by_cases hk : k.1 ∈ Set.range chart₁
        · obtain ⟨σ, hσ⟩ := exists_altExt_carmichael (by decide +kernel) (by decide +kernel) k hk
          have : f (carmichaelCycle k) = f₁ σ := by
            rw [← hσ]
            exact DFunLike.congr_fun hf1 σ
          show ρ (f (carmichaelCycle k)) = (carmichaelCycle k : Equiv.Perm (Fin 8))
          rw [this, hf₁ρ, ← hσ]
          rfl
        · have h67 : k.1 = 6 ∨ k.1 = 7 := by
            by_contra hcon
            push Not at hcon
            exact hk ((hr₁ k.1).2 hcon)
          have hk2 : k.1 ∈ Set.range chart₂ := (hr₂ _).2 (by
            rcases h67 with h | h <;> rw [h] <;> decide +kernel)
          obtain ⟨σ, hσ⟩ := exists_altExt_carmichael (by decide +kernel) (by decide +kernel) k hk2
          have : f (carmichaelCycle k) = f₂ σ := by
            rw [← hσ]
            exact DFunLike.congr_fun hf2 σ
          show ρ (f (carmichaelCycle k)) = (carmichaelCycle k : Equiv.Perm (Fin 8))
          rw [this, hf₂ρ, ← hσ]
          rfl)
    intro a
    exact DFunLike.congr_fun hext a
  refine ⟨f, hρf, fun h hh => ?_⟩
  have hρh : ρ h ∈ altOn (Finset.univ.image chart₁) := hH₀ρ ▸ Subgroup.mem_map_of_mem ρ hh
  obtain ⟨σ, hσ⟩ := exists_extPerm_of_mem_altOn chart₁ hρh
  have hfh : f₁ σ = h := ae8k_eq_of_map_eq ρ hH₀ (hf₁H σ) hh (by rw [hf₁ρ, hσ])
  exact ⟨altExt chart₁ σ, by rw [← hfh]; exact DFunLike.congr_fun hf1 σ⟩

theorem mem_alt_conj_iff (σ a : Equiv.Perm (Fin 8)) :
    σ⁻¹ * a * σ ∈ alternatingGroup (Fin 8) ↔ a ∈ alternatingGroup (Fin 8) := by
  have h : Equiv.Perm.sign (σ⁻¹ * a * σ) = Equiv.Perm.sign a := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  simp only [Equiv.Perm.mem_alternatingGroup, h]

theorem image_image_inv (s : Equiv.Perm (Fin 8)) (Γ : Finset (Fin 8)) :
    (Γ.image (s⁻¹ : Equiv.Perm (Fin 8))).image s = Γ := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    rwa [ae8k_apply_inv]
  · intro hx
    exact ⟨s⁻¹ x, ⟨x, hx, rfl⟩, ae8k_apply_inv s x⟩

theorem map_conj_altOn (s : Equiv.Perm (Fin 8)) (T : Finset (Fin 8)) :
    (altOn T).map (MulAut.conj s).toMonoidHom = altOn (T.image s) := by
  ext x
  rw [mem_altOn_image_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : s⁻¹ * (s * y * s⁻¹) * s = y := by group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [e]
  · intro hx
    refine ⟨s⁻¹ * x * s, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem exists_section (ρ : X →* Equiv.Perm (Fin 8))
    (hρ : ρ.range = alternatingGroup (Fin 8)) (hC : SectionsConj ρ) (hX : SectionsComm ρ)
    (ι : Fin 6 ↪ Fin 8) (H₀ : Subgroup X) (hH₀ : H₀ ⊓ ρ.ker = ⊥)
    (hH₀ρ : H₀.map ρ = altOn (Finset.univ.image ι)) :
    ∃ f : alternatingGroup (Fin 8) →* X,
      (∀ a, ρ (f a) = (a : Equiv.Perm (Fin 8))) ∧ H₀ ≤ f.range := by
  classical
  obtain ⟨s, hs⟩ := exists_perm_image_eq (Γ := Finset.univ.image ι)
    (Γ' := Finset.univ.image chart₁)
    (by rw [Finset.card_image_of_injective _ ι.injective,
      Finset.card_image_of_injective _ chart₁.injective])
  let ρ' : X →* Equiv.Perm (Fin 8) := (MulAut.conj s).toMonoidHom.comp ρ
  have hρ'apply : ∀ x, ρ' x = s * ρ x * s⁻¹ := fun x => by
    simp [ρ', MulAut.conj_apply]
  have hρapply : ∀ x, ρ x = s⁻¹ * ρ' x * s := fun x => by
    rw [hρ'apply]
    group
  have hker : ρ'.ker = ρ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, hρ'apply]
    constructor
    · intro h
      have : ρ x = s⁻¹ * (s * ρ x * s⁻¹) * s := by group
      rw [this, h]
      group
    · intro h
      rw [h]
      group
  have hρ'range : ρ'.range = alternatingGroup (Fin 8) := by
    ext x
    rw [← mem_alt_conj_iff s x, ← hρ]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, ?_⟩
      rw [hρapply]
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [hρ'apply, hy]
      group
  have hmap : ∀ B : Subgroup X, B.map ρ' = (B.map ρ).map (MulAut.conj s).toMonoidHom :=
    fun B => (Subgroup.map_map _ _ _).symm
  have hcorr : ∀ (B : Subgroup X) (Γ : Finset (Fin 8)), B.map ρ' = altOn Γ →
      B.map ρ = altOn (Γ.image (s⁻¹ : Equiv.Perm (Fin 8))) := by
    intro B Γ h
    apply Subgroup.map_injective (show Function.Injective (MulAut.conj s).toMonoidHom from
      (MulAut.conj s).injective)
    rw [← hmap, h, map_conj_altOn, image_image_inv]
  have hC' : SectionsConj ρ' := by
    intro Γ hΓ B B' hB hB' hBρ' hB'ρ'
    rw [hker] at hB hB'
    obtain ⟨v, hv, hvB⟩ := hC (Γ.image (s⁻¹ : Equiv.Perm (Fin 8)))
      (by rw [Finset.card_image_of_injective _ (s⁻¹ : Equiv.Perm (Fin 8)).injective, hΓ]) B B'
      hB hB' (hcorr B Γ hBρ') (hcorr B' Γ hB'ρ')
    exact ⟨v, hker ▸ hv, hvB⟩
  have hX' : SectionsComm ρ' := by
    intro T₁ T₂ h₁ h₂ hT B₁ B₂ hB₁ hB₂ hB₁ρ' hB₂ρ'
    rw [hker] at hB₁ hB₂
    refine hX (T₁.image (s⁻¹ : Equiv.Perm (Fin 8))) (T₂.image (s⁻¹ : Equiv.Perm (Fin 8)))
      (by rw [Finset.card_image_of_injective _ (s⁻¹ : Equiv.Perm (Fin 8)).injective, h₁])
      (by rw [Finset.card_image_of_injective _ (s⁻¹ : Equiv.Perm (Fin 8)).injective, h₂]) ?_
      B₁ B₂ hB₁ hB₂
      (hcorr B₁ T₁ hB₁ρ') (hcorr B₂ T₂ hB₂ρ')
    rw [Finset.disjoint_left] at hT ⊢
    intro a ha ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b', hb', hbb'⟩ := Finset.mem_image.1 ha'
    exact hT hb (by rwa [← (s⁻¹ : Equiv.Perm (Fin 8)).injective hbb'])
  have hH₀' : H₀ ⊓ ρ'.ker = ⊥ := by rwa [hker]
  have hH₀ρ' : H₀.map ρ' = altOn (Finset.univ.image chart₁) := by
    rw [hmap, hH₀ρ, map_conj_altOn, hs]
  obtain ⟨f', hf'ρ, hf'H⟩ := exists_section_std ρ' hρ'range hC' hX' hH₀' hH₀ρ'
  have hcj : ∀ a : alternatingGroup (Fin 8), s * (a : Equiv.Perm (Fin 8)) * s⁻¹ ∈
      alternatingGroup (Fin 8) := by
    intro a
    have := (mem_alt_conj_iff s⁻¹ (a : Equiv.Perm (Fin 8))).2 a.2
    simpa using this
  let cj : alternatingGroup (Fin 8) →* alternatingGroup (Fin 8) :=
    (((MulAut.conj s).toMonoidHom.comp (alternatingGroup (Fin 8)).subtype)).codRestrict
      (alternatingGroup (Fin 8)) (fun a => by simpa [MulAut.conj_apply] using hcj a)
  have hcj_apply : ∀ a : alternatingGroup (Fin 8), (cj a : Equiv.Perm (Fin 8)) =
      s * (a : Equiv.Perm (Fin 8)) * s⁻¹ := fun a => by
    simp [cj, MulAut.conj_apply]
  refine ⟨f'.comp cj, fun a => ?_, fun h hh => ?_⟩
  · rw [MonoidHom.comp_apply, hρapply, hf'ρ, hcj_apply]
    group
  · obtain ⟨a', ha'⟩ := hf'H hh
    have hmem : s⁻¹ * (a' : Equiv.Perm (Fin 8)) * s ∈ alternatingGroup (Fin 8) :=
      (mem_alt_conj_iff s _).2 a'.2
    refine ⟨⟨s⁻¹ * (a' : Equiv.Perm (Fin 8)) * s, hmem⟩, ?_⟩
    rw [MonoidHom.comp_apply, ← ha']
    congr 1
    apply Subtype.ext
    rw [hcj_apply]
    group

theorem eq_one_of_pow_three {K : Subgroup X} (h2 : IsPGroup 2 K) {k : X} (hk : k ∈ K)
    (h3 : k ^ 3 = 1) : k = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 h2) ⟨k, hk⟩
  have hdvd : orderOf (⟨k, hk⟩ : K) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h3))
  rw [hm] at hdvd
  rcases m with _ | m
  · have h1 : orderOf (⟨k, hk⟩ : K) = 1 := by simpa using hm
    exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
  · have h2d : 2 ∣ 3 := (dvd_pow_self 2 (Nat.succ_ne_zero m)).trans hdvd
    omega

theorem sectionsConj_of_central (ρ : X →* Equiv.Perm (Fin 8))
    (hcent : ρ.ker ≤ Subgroup.center X) (h2 : IsPGroup 2 ρ.ker) : SectionsConj ρ := by
  have key : ∀ {Γ : Finset (Fin 8)}, Γ.card = 4 → ∀ B B' : Subgroup X, B ⊓ ρ.ker = ⊥ →
      B' ⊓ ρ.ker = ⊥ → B.map ρ = altOn Γ → B'.map ρ = altOn Γ → B ≤ B' := by
    intro Γ hΓ B B' hB hB' hBρ hB'ρ
    refine le_of_cube_eq_one hΓ hB hBρ B' (fun b hb hb3 => ?_)
    have hρb : ρ b ∈ B'.map ρ := hB'ρ ▸ hBρ ▸ Subgroup.mem_map_of_mem ρ hb
    obtain ⟨b', hb', hbb'⟩ := Subgroup.mem_map.1 hρb
    obtain ⟨k, hk_def⟩ : ∃ k : X, k = b⁻¹ * b' := ⟨_, rfl⟩
    have hk : k ∈ ρ.ker := MonoidHom.mem_ker.2 (by
      rw [hk_def, map_mul, map_inv, hbb', inv_mul_cancel])
    have hkc := Subgroup.mem_center_iff.1 (hcent hk)
    have hb'3 : b' ^ 3 = 1 := by
      have hmem : b' ^ 3 ∈ B' ⊓ ρ.ker := ⟨B'.pow_mem hb' 3, MonoidHom.mem_ker.2 (by
        rw [map_pow, hbb', ← map_pow, hb3, map_one])⟩
      rw [hB', Subgroup.mem_bot] at hmem
      exact hmem
    have hb'_eq : b' = b * k := by rw [hk_def, mul_inv_cancel_left]
    have hc : Commute b k := hkc b
    have hk3 : k ^ 3 = 1 := by
      have h1 : b' ^ 3 = b ^ 3 * k ^ 3 := by rw [hb'_eq]; exact hc.mul_pow 3
      rw [hb3, one_mul] at h1
      rw [← h1]
      exact hb'3
    have hk1 : k = 1 := eq_one_of_pow_three h2 hk hk3
    have : b' = b := by rw [hb'_eq, hk1, mul_one]
    rw [← this]
    exact hb'
  intro Γ hΓ B B' hB hB' hBρ hB'ρ
  have hconj1 : B.map (MulAut.conj (1 : X)).toMonoidHom = B := by
    ext x
    simp [Subgroup.mem_map, MulAut.conj_apply]
  refine ⟨1, one_mem _, ?_⟩
  rw [hconj1]
  exact le_antisymm (key hΓ B' B hB' hB hB'ρ hBρ) (key hΓ B B' hB hB' hBρ hB'ρ)

theorem sectionsComm_of_central (ρ : X →* Equiv.Perm (Fin 8))
    (hcent : ρ.ker ≤ Subgroup.center X) (h2 : IsPGroup 2 ρ.ker) : SectionsComm ρ := by
  intro T₁ T₂ h₁ h₂' hT B₁ B₂ hB₁ hB₂ hB₁ρ hB₂ρ
  have hle : B₁ ≤ Subgroup.centralizer (B₂ : Set X) := by
    refine le_of_cube_eq_one h₁ hB₁ hB₁ρ _ (fun x hx hx3 => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hρx : ρ x ∈ altOn T₁ := hB₁ρ ▸ Subgroup.mem_map_of_mem ρ hx
    have hρy : ρ y ∈ altOn T₂ := hB₂ρ ▸ Subgroup.mem_map_of_mem ρ hy
    have hcomm := altOn_comm hT hρx hρy
    obtain ⟨k, hk_def⟩ : ∃ k : X, k = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
    have hk : k ∈ ρ.ker := MonoidHom.mem_ker.2 (by
      have : ρ x * ρ y * (ρ x)⁻¹ * (ρ y)⁻¹ = 1 := by
        rw [hcomm]
        group
      rw [hk_def]
      simpa only [map_mul, map_inv] using this)
    have hkc := Subgroup.mem_center_iff.1 (hcent hk)
    have e1 : x * y * x⁻¹ = k * y := by rw [hk_def]; group
    have hxk : x * k * x⁻¹ = k := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hkc x
    have e2 : x * (k * y) * x⁻¹ = k * (k * y) := by
      calc x * (k * y) * x⁻¹ = (x * k * x⁻¹) * (x * y * x⁻¹) := by group
        _ = k * (k * y) := by rw [hxk, e1]
    have e3 : x * (k * (k * y)) * x⁻¹ = k * (k * (k * y)) := by
      calc x * (k * (k * y)) * x⁻¹ = (x * k * x⁻¹) * (x * (k * y) * x⁻¹) := by group
        _ = k * (k * (k * y)) := by rw [hxk, e2]
    have e4 : x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ = y := by
      have : x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * y * (x ^ 3)⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      rw [this, hx3]
      simp
    rw [e1, e2, e3] at e4
    have hk3 : k ^ 3 = 1 := by
      have : k ^ 3 * y = y := by
        calc k ^ 3 * y = k * (k * (k * y)) := by
              simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = y := e4
      exact mul_eq_right.1 this
    have hk1 : k = 1 := eq_one_of_pow_three h2 hk hk3
    rw [hk1, one_mul] at e1
    exact (mul_inv_eq_iff_eq_mul.1 e1).symm
  intro x hx y hy
  exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) y hy).symm

end Glue8

theorem Glue8.exists_section_of_central {X : Type} [Group X] [Finite X]
    (ρ : X →* Equiv.Perm (Fin 8)) (hρ : ρ.range = alternatingGroup (Fin 8))
    (hcent : ρ.ker ≤ Subgroup.center X) (h2 : IsPGroup 2 ρ.ker)
    (ι : Fin 6 ↪ Fin 8) (H₀ : Subgroup X) (hH₀ : H₀ ⊓ ρ.ker = ⊥)
    (hH₀ρ : H₀.map ρ = altOn (Finset.univ.image ι)) :
    ∃ f : alternatingGroup (Fin 8) →* X, ∀ a, ρ (f a) = (a : Equiv.Perm (Fin 8)) :=
  let ⟨f, hf, _⟩ := Glue8.exists_section ρ hρ (Glue8.sectionsConj_of_central ρ hcent h2)
    (Glue8.sectionsComm_of_central ρ hcent h2) ι H₀ hH₀ hH₀ρ
  ⟨f, hf⟩

theorem splits_of_alt_eight_rel {X : Type} [Group X] [Finite X] (V : Subgroup X) [V.Normal]
    (π : X →* Equiv.Perm (Fin 8)) (hker : π.ker = V)
    (hrange : π.range = alternatingGroup (Fin 8))
    (β : Multiplicative (Fin 8 → ZMod 2) →* X)
    (hV : ∀ g : X, g ∈ V ↔ ∃ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 ∧ β f = g)
    (hβ : ∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
      (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1))
    (hconj : ∀ (g : X) (f : Multiplicative (Fin 8 → ZMod 2)), ∑ i, f.toAdd i = 0 →
      g * β f * g⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((π g).symm i)))
    (ι : Fin 6 ↪ Fin 8) (H₀ : Subgroup X) (hH₀V : H₀ ⊓ V = ⊥)
    (hH₀π : H₀.map π = altOn (Finset.univ.image ι)) :
    ∃ H : Subgroup X, V.IsComplement' H ∧ H₀ ≤ H := by
  subst hker
  have hM : EvenModule π β := ⟨hV, hβ, hconj⟩
  obtain ⟨f, hf, hH₀f⟩ := Glue8.exists_section π hrange
    (fun Γ hΓ B B' hB hB' hBπ hB'π => exists_conj_of_complements hM hΓ B B' hB hB' hBπ hB'π)
    (fun T₁ T₂ h₁ h₂ hT B₁ B₂ hB₁ hB₂ hB₁π hB₂π =>
      commute_of_complements hM h₁ h₂ hT hB₁ hB₂ hB₁π hB₂π) ι H₀ hH₀V hH₀π
  refine ⟨f.range, ?_, hH₀f⟩
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [Subgroup.disjoint_def]
    intro x hxV hxH
    obtain ⟨a, rfl⟩ := hxH
    have h1 : (a : Equiv.Perm (Fin 8)) = 1 := by
      rw [← hf a]
      exact MonoidHom.mem_ker.1 hxV
    have : a = 1 := Subtype.ext h1
    rw [this, map_one]
  · apply Set.eq_univ_of_forall
    intro g
    have hg : π g ∈ alternatingGroup (Fin 8) := hrange ▸ ⟨g, rfl⟩
    refine ⟨g * (f ⟨π g, hg⟩)⁻¹, ?_, f ⟨π g, hg⟩, ⟨_, rfl⟩, inv_mul_cancel_right _ _⟩
    show g * (f ⟨π g, hg⟩)⁻¹ ∈ π.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hf]
    simp

end AE8End

end CFSG.ClassicalInvolution.Q3.Sec13
