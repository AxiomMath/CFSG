module

public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv10
public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private def bruA : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

private def bruB : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

private theorem bru_even_inv_fix4 : ∀ w : Equiv.Perm (Fin 5), w * w = 1 → w 4 = 4 →
    Equiv.Perm.sign w = 1 → w = 1 ∨ w = bruA ∨ w = bruB ∨ w = bruA * bruB := by
  decide +kernel

private theorem bru_fix_unique : ∀ w : Equiv.Perm (Fin 5),
    (w = bruA ∨ w = bruB ∨ w = bruA * bruB) → ∀ q : Fin 5, w q = q → q = 4 := by
  decide +kernel

private theorem bru_V_props : ∀ w : Equiv.Perm (Fin 5),
    (w = 1 ∨ w = bruA ∨ w = bruB ∨ w = bruA * bruB) →
      w * w = 1 ∧ w 4 = 4 ∧ Equiv.Perm.sign w = 1 := by
  decide +kernel

private theorem bru_exists_third : ∀ q a c : Fin 5, a ≠ q → c ≠ q → a ≠ c →
    ∃ x : Fin 5, x ≠ q ∧ x ≠ a ∧ x ≠ c := by
  decide +kernel

private theorem bru_s3_inv : ∀ w : Equiv.Perm (Fin 3), w * w = 1 → w 2 = 2 →
    w = 1 ∨ w = Equiv.swap 0 1 := by
  decide +kernel

private theorem bru_s3_swap_fix : ∀ q : Fin 3, Equiv.swap (0 : Fin 3) 1 q = q → q = 2 := by
  decide +kernel

private theorem bru_s3_trans : ∀ q a c : Fin 3, a ≠ q → c ≠ q →
    ∃ h : Equiv.Perm (Fin 3), h q = q ∧ h a = c := by
  decide +kernel

private def bruV : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {w | w = 1 ∨ w = bruA ∨ w = bruB ∨ w = bruA * bruB}
  mul_mem' := by
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide +kernel
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro x (rfl | rfl | rfl | rfl) <;> decide +kernel

private theorem bru_card_of_mem {G : Type} [Group G] [DecidableEq G] (V : Subgroup G)
    (F : Finset G) (hF : ∀ w, w ∈ V ↔ w ∈ F) : Nat.card V = F.card := by
  have e : Nat.card V = Nat.card (F : Set G) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hF x).trans Finset.mem_coe.symm)
  rw [e, Nat.card_coe_set_eq, Set.ncard_coe_finset]

private theorem bru_card_V : Nat.card bruV = 4 :=
  (bru_card_of_mem bruV {1, bruA, bruB, bruA * bruB} fun w => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Iff.rfl).trans (by decide +kernel)

private theorem bru_V_le : bruV ≤ alternatingGroup (Fin 5) := fun w hw =>
  Equiv.Perm.mem_alternatingGroup.mpr (bru_V_props w hw).2.2

private theorem bru_card_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem bru_sign_a : Equiv.Perm.sign bruA = 1 := by decide +kernel

private def bruAA : alternatingGroup (Fin 5) :=
  ⟨bruA, Equiv.Perm.mem_alternatingGroup.mpr bru_sign_a⟩

private abbrev bruVA : Subgroup (alternatingGroup (Fin 5)) :=
  bruV.subgroupOf (alternatingGroup (Fin 5))

private theorem bru_card_VA : Nat.card bruVA = 4 := by
  rw [bruVA, Nat.card_congr (Subgroup.subgroupOfEquivOfLe bru_V_le).toEquiv, bru_card_V]

private theorem bru_mem_VA (w : alternatingGroup (Fin 5)) :
    w ∈ bruVA ↔ w * w = 1 ∧ (w : Equiv.Perm (Fin 5)) 4 = 4 := by
  rw [bruVA, Subgroup.mem_subgroupOf]
  constructor
  · intro hw
    obtain ⟨h1, h2, -⟩ := bru_V_props _ hw
    exact ⟨Subtype.ext (by simpa using h1), h2⟩
  · rintro ⟨h1, h2⟩
    have h1' : (w : Equiv.Perm (Fin 5)) * w = 1 := by
      simpa using congrArg Subtype.val h1
    exact bru_even_inv_fix4 _ h1' h2 (Equiv.Perm.mem_alternatingGroup.mp w.2)

private def bruS : Subgroup (Equiv.Perm (Fin 3)) where
  carrier := {w | w = 1 ∨ w = Equiv.swap 0 1}
  mul_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> decide +kernel
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro x (rfl | rfl) <;> decide +kernel

private theorem bru_card_S : Nat.card bruS = 2 :=
  (bru_card_of_mem bruS {1, Equiv.swap 0 1} fun w => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Iff.rfl).trans (by decide +kernel)

private theorem bru_mem_S (w : Equiv.Perm (Fin 3)) : w ∈ bruS ↔ w * w = 1 ∧ w 2 = 2 := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨by simp, by simp⟩
    · exact ⟨by decide +kernel, by decide +kernel⟩
  · rintro ⟨h1, h2⟩
    rcases bru_s3_inv w h1 h2 with h | h
    · exact Or.inl h
    · exact Or.inr h

private theorem bru_inv_apply {Ω : Type} (f : Equiv.Perm Ω) (x : Ω) : f⁻¹ (f x) = x := by
  rw [Equiv.Perm.inv_def]
  exact Equiv.symm_apply_apply f x

private theorem bru_apply_inv {Ω : Type} (f : Equiv.Perm Ω) (x : Ω) : f (f⁻¹ x) = x := by
  rw [Equiv.Perm.inv_def]
  exact Equiv.apply_symm_apply f x

private theorem bru_normalizer_point {M : Type} [Group M] {Ω : Type} (ι : M →* Equiv.Perm Ω)
    (V : Subgroup M) (p0 : Ω) (hV : ∀ w : M, w ∈ V ↔ w * w = 1 ∧ ι w p0 = p0)
    (a : M) (ha : a ∈ V) (ha1 : a ≠ 1)
    (hu : ∀ w ∈ V, w ≠ 1 → ∀ q : Ω, ι w q = q → q = p0) (z : M) :
    z ∈ Subgroup.normalizer (V : Set M) ↔ ι z p0 = p0 := by
  have hfix : ∀ w ∈ V, ι w p0 = p0 := fun w hw => ((hV w).1 hw).2
  have hinv : ∀ y : M, ι y p0 = p0 → ι y⁻¹ p0 = p0 := by
    intro y hy
    have h := bru_inv_apply (ι y) p0
    rw [hy] at h
    rw [map_inv]
    exact h
  have fwd : ∀ y : M, ι y p0 = p0 → ∀ h ∈ V, y * h * y⁻¹ ∈ V := by
    intro y hy h hh
    rw [hV]
    refine ⟨?_, ?_⟩
    · have hh2 := ((hV h).1 hh).1
      calc (y * h * y⁻¹) * (y * h * y⁻¹) = y * (h * h) * y⁻¹ := by group
        _ = 1 := by rw [hh2]; group
    · rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv y hy, hfix h hh, hy]
  constructor
  · intro hz
    rw [Subgroup.mem_normalizer_iff] at hz
    have hc : z * a * z⁻¹ ∈ V := (hz a).1 ha
    have hne : z * a * z⁻¹ ≠ 1 := by
      intro h1
      apply ha1
      have e : a = z⁻¹ * (z * a * z⁻¹) * z := by group
      rw [e, h1]
      group
    refine hu _ hc hne (ι z p0) ?_
    rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      bru_inv_apply, hfix a ha]
  · intro hz
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fwd z hz h
    · intro hh
      have e : z⁻¹ * (z * h * z⁻¹) * z⁻¹⁻¹ = h := by group
      have := fwd z⁻¹ (hinv z hz) (z * h * z⁻¹) hh
      rwa [e] at this

private theorem bru_mem_normalizer_comap {X M : Type} [Group X] [Group M] (ψ : X ≃* M)
    (V : Subgroup M) (y : X) :
    y ∈ Subgroup.normalizer ((V.comap ψ.toMonoidHom : Subgroup X) : Set X) ↔
      ψ y ∈ Subgroup.normalizer (V : Set M) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h m
    obtain ⟨t, rfl⟩ := ψ.surjective m
    have ht := h t
    simpa [Subgroup.mem_comap] using ht
  · intro h t
    have ht := h (ψ t)
    simpa [Subgroup.mem_comap] using ht

private theorem bru_card_comap {X M : Type} [Group X] [Group M] (ψ : X ≃* M) (V : Subgroup M) :
    Nat.card (V.comap ψ.toMonoidHom) = Nat.card V := by
  refine Nat.card_congr ?_
  exact ((MulEquiv.subgroupMap ψ (V.comap ψ.toMonoidHom)).toEquiv).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective ψ.surjective V)).toEquiv

private theorem bru_sylow_top {X : Type} [Group X] (V : Subgroup X) (k m : ℕ)
    (hV : Nat.card V = 2 ^ k) (hX : Nat.card X = 2 ^ k * m) (hm : Odd m) :
    IsSylowTwoOf V ⊤ := by
  have hp : IsPGroup 2 V := IsPGroup.of_card hV
  refine ⟨le_top, hp, ?_⟩
  have h1 := V.card_mul_index
  rw [hV, hX] at h1
  have hi : V.index = m := Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hodd' : ¬ 2 ∣ m := by
    rcases hm with ⟨j, rfl⟩
    omega
  have e : (V.subgroupOf ⊤).index = V.index := Subgroup.relIndex_top_right _
  rw [e, hi]
  exact hodd'

private theorem bru_sylow_top_of {X : Type} [Group X] (V : Subgroup X) (hp : IsPGroup 2 V)
    (hodd : ¬ 2 ∣ V.index) : IsSylowTwoOf V ⊤ := by
  refine ⟨le_top, hp, ?_⟩
  have e : (V.subgroupOf ⊤).index = V.index := Subgroup.relIndex_top_right _
  rw [e]
  exact hodd

private theorem bru_np {X : Type} [Group X] [Finite X] {Ω : Type} (σ : X →* Equiv.Perm Ω)
    (V0 T : Subgroup X) (hV : IsSylowTwoOf V0 ⊤) (hT : IsSylowTwoOf T ⊤) (q0 : Ω)
    (hV0 : ∀ y : X, y ∈ Subgroup.normalizer (V0 : Set X) ↔ σ y q0 = q0) :
    ∃ q : Ω, ∀ y : X, y ∈ Subgroup.normalizer (T : Set X) ↔ σ y q = q := by
  obtain ⟨x, -, hx⟩ := F7.isSylowTwoOf_exists_conj_le hT (le_top : V0 ≤ ⊤) hV.2.1
  have hVeq : V0 = CFSG.Quasithin.conjSub x T :=
    F1.eq_of_isSylowTwoOf_le hV le_top (F7.isPGroup_conjSub hT.2.1) hx
  refine ⟨σ x⁻¹ q0, fun y => ?_⟩
  have hkey : y ∈ Subgroup.normalizer (T : Set X) ↔
      x * y * x⁻¹ ∈ Subgroup.normalizer (V0 : Set X) := by
    rw [hVeq, CFSG.Quasithin.conjSub_normalizer, CFSG.Quasithin.mem_conjSub]
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rw [e]
  rw [hkey, hV0, map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  constructor
  · intro h
    have h' := congrArg (fun z => (σ x)⁻¹ z) h
    simp only [bru_inv_apply] at h'
    exact h'
  · intro h
    rw [h]
    exact bru_apply_inv _ _

private theorem bru_dc_point {X : Type} [Group X] {Ω : Type} (σ : X →* Equiv.Perm Ω) (q : Ω)
    (H : Subgroup X) (hH : ∀ y : X, y ∈ H ↔ σ y q = q)
    (hK : ∀ a c : Ω, a ≠ q → c ≠ q → ∃ h : X, σ h q = q ∧ σ h a = c)
    (x : X) (hx : x ∉ H) (g : X) :
    g ∈ H ∨ ∃ h1 ∈ H, ∃ h2 ∈ H, g = h1 * x * h2 := by
  by_cases hg : g ∈ H
  · exact Or.inl hg
  refine Or.inr ?_
  rw [hH] at hx hg
  obtain ⟨h1, hh1, hh1x⟩ := hK (σ x q) (σ g q) hx hg
  have e : (σ h1)⁻¹ (σ g q) = σ x q := by
    rw [← hh1x, bru_inv_apply]
  refine ⟨h1, (hH h1).2 hh1, x⁻¹ * h1⁻¹ * g, (hH _).2 ?_, ?_⟩
  · simp only [map_mul, map_inv, Equiv.Perm.mul_apply, e, bru_inv_apply]
  · group

private theorem bru_k1_A5 (q a c : Fin 5) (ha : a ≠ q) (hc : c ≠ q) :
    ∃ h : alternatingGroup (Fin 5), (h : Equiv.Perm (Fin 5)) q = q ∧
      (h : Equiv.Perm (Fin 5)) a = c := by
  by_cases hac : a = c
  · exact ⟨1, by simp, by simp [hac]⟩
  obtain ⟨x, hxq, hxa, hxc⟩ := bru_exists_third q a c ha hc hac
  have hs : Equiv.Perm.sign (Equiv.swap a c * Equiv.swap c x) = 1 := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hac, Equiv.Perm.sign_swap (Ne.symm hxc),
      Int.units_mul_self]
  refine ⟨⟨Equiv.swap a c * Equiv.swap c x, Equiv.Perm.mem_alternatingGroup.mpr hs⟩, ?_, ?_⟩
  · show (Equiv.swap a c * Equiv.swap c x) q = q
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hc) (Ne.symm hxq),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hc)]
  · show (Equiv.swap a c * Equiv.swap c x) a = c
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hac (Ne.symm hxa),
      Equiv.swap_apply_left]

private theorem bru_dc_A5 {X : Type} [Group X] [Finite X] (ψ : X ≃* alternatingGroup (Fin 5))
    (T : Subgroup X) (hT : IsSylowTwoOf T ⊤) (x : X) (hx : x ∉ Subgroup.normalizer (T : Set X))
    (g : X) : g ∈ Subgroup.normalizer (T : Set X) ∨
      ∃ h1 ∈ Subgroup.normalizer (T : Set X), ∃ h2 ∈ Subgroup.normalizer (T : Set X),
        g = h1 * x * h2 := by
  have hX : Nat.card X = 2 ^ 2 * 15 :=
    (by rw [Nat.card_congr ψ.toEquiv, bru_card_A5] : Nat.card X = 60).trans (by norm_num)
  have hcV : Nat.card (bruVA.comap ψ.toMonoidHom) = 2 ^ 2 :=
    (bru_card_comap ψ bruVA).trans (bru_card_VA.trans (by norm_num))
  have hV := bru_sylow_top (bruVA.comap ψ.toMonoidHom) 2 15 hcV hX (by decide)
  have hmemAA : bruAA ∈ bruVA :=
    (bru_mem_VA _).2 ⟨Subtype.ext (show bruA * bruA = 1 by decide +kernel),
      show bruA 4 = 4 by decide +kernel⟩
  have hne : bruAA ≠ 1 := fun h =>
    absurd (congrArg (fun w : alternatingGroup (Fin 5) => (w : Equiv.Perm (Fin 5)) 0) h)
      (by decide +kernel)
  have hu : ∀ w ∈ bruVA, w ≠ 1 → ∀ q : Fin 5,
      (alternatingGroup (Fin 5)).subtype w q = q → q = 4 := by
    intro w hw hw1 q hq
    have hw' : (w : Equiv.Perm (Fin 5)) = bruA ∨ (w : Equiv.Perm (Fin 5)) = bruB ∨
        (w : Equiv.Perm (Fin 5)) = bruA * bruB := by
      rcases (Subgroup.mem_subgroupOf.mp hw : (w : Equiv.Perm (Fin 5)) ∈ bruV) with h | h | h | h
      · exact absurd (Subtype.ext h) hw1
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact bru_fix_unique _ hw' q hq
  have hVn0 : ∀ y : alternatingGroup (Fin 5),
      y ∈ Subgroup.normalizer ((bruVA : Subgroup (alternatingGroup (Fin 5))) :
        Set (alternatingGroup (Fin 5))) ↔ (alternatingGroup (Fin 5)).subtype y 4 = 4 :=
    fun y => bru_normalizer_point (alternatingGroup (Fin 5)).subtype bruVA 4 bru_mem_VA
      _ hmemAA hne hu y
  have hVn : ∀ y : X, y ∈ Subgroup.normalizer
      ((bruVA.comap ψ.toMonoidHom : Subgroup X) : Set X) ↔
        ((alternatingGroup (Fin 5)).subtype.comp ψ.toMonoidHom) y 4 = 4 := by
    intro y
    rw [bru_mem_normalizer_comap]
    exact hVn0 (ψ y)
  obtain ⟨q, hq⟩ := bru_np ((alternatingGroup (Fin 5)).subtype.comp ψ.toMonoidHom) _ T hV hT 4 hVn
  have hK : ∀ a c : Fin 5, a ≠ q → c ≠ q → ∃ h : X,
      ((alternatingGroup (Fin 5)).subtype.comp ψ.toMonoidHom) h q = q ∧
        ((alternatingGroup (Fin 5)).subtype.comp ψ.toMonoidHom) h a = c := by
    intro a c ha hc
    obtain ⟨h', hh'q, hh'a⟩ := bru_k1_A5 q a c ha hc
    refine ⟨ψ.symm h', ?_, ?_⟩
    · simpa using hh'q
    · simpa using hh'a
  exact bru_dc_point _ q _ hq hK x hx g

private theorem bru_dc_S3 {X : Type} [Group X] [Finite X] (ψ : X ≃* Equiv.Perm (Fin 3))
    (T : Subgroup X) (hT : IsSylowTwoOf T ⊤) (x : X) (hx : x ∉ Subgroup.normalizer (T : Set X))
    (g : X) : g ∈ Subgroup.normalizer (T : Set X) ∨
      ∃ h1 ∈ Subgroup.normalizer (T : Set X), ∃ h2 ∈ Subgroup.normalizer (T : Set X),
        g = h1 * x * h2 := by
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have hX : Nat.card X = 2 ^ 1 * 3 :=
    (by rw [Nat.card_congr ψ.toEquiv, h6] : Nat.card X = 6).trans (by norm_num)
  have hcV : Nat.card (bruS.comap ψ.toMonoidHom) = 2 ^ 1 :=
    (bru_card_comap ψ bruS).trans (bru_card_S.trans (by norm_num))
  have hV := bru_sylow_top (bruS.comap ψ.toMonoidHom) 1 3 hcV hX (by decide)
  have hu : ∀ w ∈ bruS, w ≠ 1 → ∀ q : Fin 3,
      (MonoidHom.id (Equiv.Perm (Fin 3))) w q = q → q = 2 := by
    intro w hw hw1 q hq
    rcases (hw : w = 1 ∨ w = Equiv.swap 0 1) with h | h
    · exact absurd h hw1
    · subst h
      exact bru_s3_swap_fix q hq
  have hVn0 : ∀ y : Equiv.Perm (Fin 3),
      y ∈ Subgroup.normalizer ((bruS : Subgroup (Equiv.Perm (Fin 3))) : Set (Equiv.Perm (Fin 3))) ↔
        (MonoidHom.id (Equiv.Perm (Fin 3))) y 2 = 2 :=
    fun y => bru_normalizer_point (MonoidHom.id (Equiv.Perm (Fin 3))) bruS 2 bru_mem_S
      (Equiv.swap 0 1) ((bru_mem_S _).2 ⟨by decide +kernel, by decide +kernel⟩)
      (by decide +kernel) hu y
  have hVn : ∀ y : X, y ∈ Subgroup.normalizer
      ((bruS.comap ψ.toMonoidHom : Subgroup X) : Set X) ↔ ψ y 2 = 2 := by
    intro y
    rw [bru_mem_normalizer_comap]
    exact hVn0 (ψ y)
  obtain ⟨q, hq⟩ := bru_np ψ.toMonoidHom _ T hV hT 2 hVn
  have hK : ∀ a c : Fin 3, a ≠ q → c ≠ q → ∃ h : X,
      ψ.toMonoidHom h q = q ∧ ψ.toMonoidHom h a = c := by
    intro a c ha hc
    obtain ⟨h', hh'q, hh'a⟩ := bru_s3_trans q a c ha hc
    refine ⟨ψ.symm h', ?_, ?_⟩
    · simpa using hh'q
    · simpa using hh'a
  exact bru_dc_point _ q _ hq hK x hx g

private abbrev bruTbar {G : Type} [Group G] (L1 S : Subgroup G) : Subgroup (oTwoQuot ↥L1) :=
  ((S ⊓ L1).subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1))

private theorem bru_dc_oTwoQuot {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (h : Hyp111R L1 L2 S)
    (hv : IsL2Quot 2 (oTwoQuot ↥L1) ∨ Nonempty (oTwoQuot ↥L1 ≃* Equiv.Perm (Fin 3)))
    (x : oTwoQuot ↥L1)
    (hx : x ∉ Subgroup.normalizer ((bruTbar L1 S : Subgroup _) : Set (oTwoQuot ↥L1)))
    (g : oTwoQuot ↥L1) :
    g ∈ Subgroup.normalizer ((bruTbar L1 S : Subgroup _) : Set (oTwoQuot ↥L1)) ∨
      ∃ h1 ∈ Subgroup.normalizer ((bruTbar L1 S : Subgroup _) : Set (oTwoQuot ↥L1)),
        ∃ h2 ∈ Subgroup.normalizer ((bruTbar L1 S : Subgroup _) : Set (oTwoQuot ↥L1)),
          g = h1 * x * h2 := by
  have hsyl := F1.map_borelOf_eq_normalizer h.hyp.h1.sylow
  have hT : IsSylowTwoOf (bruTbar L1 S) ⊤ := bru_sylow_top_of _ hsyl.1 hsyl.2.1
  rcases hv with hq | hne
  · obtain ⟨ψ⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
    exact bru_dc_A5 ψ _ hT x hx g
  · obtain ⟨ψ⟩ := hne
    exact bru_dc_S3 ψ _ hT x hx g

private theorem bru_kl {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (h : Hyp111R L1 L2 S)
    (hv : IsL2Quot 2 (oTwoQuot ↥L1) ∨ Nonempty (oTwoQuot ↥L1 ≃* Equiv.Perm (Fin 3)))
    (l x : G) (hl : l ∈ L1) (hlB : l ∉ borelOf L1 S) (hx : x ∈ L1) :
    x ∈ borelOf L1 S ∨ ∃ b₁ ∈ borelOf L1 S, ∃ b₂ ∈ borelOf L1 S, x = b₁ * l * b₂ := by
  have hQB : ∀ q : ↥L1, q ∈ pCore 2 ↥L1 → (q : G) ∈ borelOf L1 S := fun q hq =>
    F1.sylow_le_borelOf L1 S
      (F7.isSylowTwoOf_pCoreOf_le h.hyp.h1.sylow ((F1.mem_pCore_iff_coe q).mp hq))
  have hN : ((borelOf L1 S).subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1)) =
      Subgroup.normalizer ((bruTbar L1 S : Subgroup _) : Set (oTwoQuot ↥L1)) :=
    (F1.map_borelOf_eq_normalizer h.hyp.h1.sylow).2.2
  have hDC := bru_dc_oTwoQuot h hv
  have hl_notin : QuotientGroup.mk' (pCore 2 ↥L1) (⟨l, hl⟩ : ↥L1) ∉
      Subgroup.normalizer ((bruTbar L1 S : Subgroup _) : Set (oTwoQuot ↥L1)) := by
    rw [← hN]
    intro hmem
    obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.mp hmem
    apply hlB
    have hq : k⁻¹ * (⟨l, hl⟩ : ↥L1) ∈ pCore 2 ↥L1 := QuotientGroup.eq.mp hkl
    have e : (k : G) * ((k⁻¹ * (⟨l, hl⟩ : ↥L1) : ↥L1) : G) = l := by simp
    rw [← e]
    exact (borelOf L1 S).mul_mem (Subgroup.mem_subgroupOf.mp hk) (hQB _ hq)
  have hx' := hDC (QuotientGroup.mk' (pCore 2 ↥L1) ⟨l, hl⟩) hl_notin
    (QuotientGroup.mk' (pCore 2 ↥L1) ⟨x, hx⟩)
  rcases hx' with hxB | ⟨k1', hk1', k2', hk2', he⟩
  · rw [← hN] at hxB
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.mp hxB
    have hq : k⁻¹ * (⟨x, hx⟩ : ↥L1) ∈ pCore 2 ↥L1 := QuotientGroup.eq.mp hke
    left
    have e : (k : G) * ((k⁻¹ * (⟨x, hx⟩ : ↥L1) : ↥L1) : G) = x := by simp
    rw [← e]
    exact (borelOf L1 S).mul_mem (Subgroup.mem_subgroupOf.mp hk) (hQB _ hq)
  · rw [← hN] at hk1' hk2'
    obtain ⟨k1, hk1, hk1e⟩ := Subgroup.mem_map.mp hk1'
    obtain ⟨k2, hk2, hk2e⟩ := Subgroup.mem_map.mp hk2'
    rw [← hk1e, ← hk2e] at he
    have hab : QuotientGroup.mk' (pCore 2 ↥L1) (k1 * ⟨l, hl⟩ * k2) =
        QuotientGroup.mk' (pCore 2 ↥L1) ⟨x, hx⟩ := by
      rw [map_mul, map_mul]
      exact he.symm
    have hq : (k1 * ⟨l, hl⟩ * k2)⁻¹ * (⟨x, hx⟩ : ↥L1) ∈ pCore 2 ↥L1 := QuotientGroup.eq.mp hab
    set q : ↥L1 := (k1 * ⟨l, hl⟩ * k2)⁻¹ * ⟨x, hx⟩ with hqdef
    right
    refine ⟨(k1 : G), Subgroup.mem_subgroupOf.mp hk1, (k2 : G) * (q : G),
      (borelOf L1 S).mul_mem (Subgroup.mem_subgroupOf.mp hk2) (hQB _ hq), ?_⟩
    have hxq : (k1 * ⟨l, hl⟩ * k2 : ↥L1) * q = ⟨x, hx⟩ := mul_inv_cancel_left _ _
    have hxG : (k1 : G) * l * (k2 : G) * (q : G) = x := by
      have := congrArg Subtype.val hxq
      simpa using this
    rw [← hxG]
    group

theorem leafBruhat : LeafBruhat := by
  intro G _ _ L1 L2 S h hv
  have hnorm : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (F1.bigB_le_normalizer_left h).1
  have hBB : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  intro s hs hsB g hg
  obtain ⟨ls, hls, bs, hbs, hseq⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp hs
  obtain ⟨lg, hlg, bg, hbg, hgeq⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp hg
  have hlsB : ls ∉ borelOf L1 S := fun hl => hsB (by
    rw [hseq]
    exact (bigB L1 L2 S).mul_mem (hBB hl) hbs)
  rcases bru_kl h hv ls lg hls hlsB hlg with hlgB | ⟨b1, hb1, b2, hb2, hlgeq⟩
  · left
    rw [hgeq]
    exact (bigB L1 L2 S).mul_mem (hBB hlgB) hbg
  · right
    refine ⟨b1, hBB hb1, bs⁻¹ * b2 * bg,
      (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).mul_mem ((bigB L1 L2 S).inv_mem hbs) (hBB hb2)) hbg,
      ?_⟩
    rw [hgeq, hlgeq, hseq]
    group

end CFSG.GH74.QTGen4.DSGen4
