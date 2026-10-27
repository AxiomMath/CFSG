module

public import CFSG.HardMathSupport.GuralnickMalle.BasicGeneral
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open scoped IsMulCommutative

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

@[expose] def IsBestFGen (ρ : Representation K G V) (B : Subgroup G) : Prop :=
  ∀ D : Subgroup G, D ≤ B → weight1Gen ρ D ≤ weight1Gen ρ B

theorem weight1Gen_mul_le_sup_mul_inf [Finite G] [Finite V]
    (ρ : Representation K G V) (A B : Subgroup G) :
    weight1Gen ρ A * weight1Gen ρ B ≤
      weight1Gen ρ (A ⊔ B) * weight1Gen ρ (A ⊓ B) := by
  rw [weight1Gen, weight1Gen, weight1Gen, weight1Gen]
  calc Nat.card A * Nat.card (fixSubGen ρ A) *
        (Nat.card B * Nat.card (fixSubGen ρ B))
      = (Nat.card A * Nat.card B) *
        (Nat.card (fixSubGen ρ A) * Nat.card (fixSubGen ρ B)) := by ring
    _ ≤ (Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)) *
        (Nat.card (fixSubGen ρ (A ⊔ B)) * Nat.card (fixSubGen ρ (A ⊓ B))) :=
      Nat.mul_le_mul (card_mul_card_le_sup_inf A B) (card_mul_card_fixSubGen_le ρ A B)
    _ = Nat.card ↥(A ⊔ B) * Nat.card (fixSubGen ρ (A ⊔ B)) *
        (Nat.card ↥(A ⊓ B) * Nat.card (fixSubGen ρ (A ⊓ B))) := by ring

theorem weight1Gen_le_weight1Gen_sup_of_le_inf [Finite G] [Finite V]
    (ρ : Representation K G V) {A B : Subgroup G}
    (h : weight1Gen ρ (A ⊓ B) ≤ weight1Gen ρ B) :
    weight1Gen ρ A ≤ weight1Gen ρ (A ⊔ B) := by
  have hkey : weight1Gen ρ A * weight1Gen ρ B ≤ weight1Gen ρ (A ⊔ B) * weight1Gen ρ B :=
    calc weight1Gen ρ A * weight1Gen ρ B
        ≤ weight1Gen ρ (A ⊔ B) * weight1Gen ρ (A ⊓ B) :=
          weight1Gen_mul_le_sup_mul_inf ρ A B
      _ ≤ weight1Gen ρ (A ⊔ B) * weight1Gen ρ B := Nat.mul_le_mul_left _ h
  exact Nat.le_of_mul_le_mul_right hkey (weight1Gen_pos ρ B)

theorem weight1Gen_le_weight1Gen_sup [Finite G] [Finite V]
    {ρ : Representation K G V} {Λ B : Subgroup G} (hB : IsBestFGen ρ B) :
    weight1Gen ρ Λ ≤ weight1Gen ρ (Λ ⊔ B) :=
  weight1Gen_le_weight1Gen_sup_of_le_inf ρ (hB (Λ ⊓ B) inf_le_right)

theorem IsBestFGen.map_conj {ρ : Representation K G V} {A : Subgroup G}
    (h : IsBestFGen ρ A) (g : G) :
    IsBestFGen ρ (A.map (MulAut.conj g).toMonoidHom) := by
  intro D hD
  have hD' : D.map (MulAut.conj g⁻¹).toMonoidHom ≤ A := by
    intro x hx
    obtain ⟨d, hd, hx'⟩ := Subgroup.mem_map.1 hx
    rw [← hx']
    obtain ⟨a, ha, hd'⟩ := Subgroup.mem_map.1 (hD hd)
    rw [← hd']
    have he : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom a) = a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [he]
    exact ha
  calc weight1Gen ρ D
      = weight1Gen ρ (D.map (MulAut.conj g⁻¹).toMonoidHom) :=
        (weight1Gen_map_conj ρ D g⁻¹).symm
    _ ≤ weight1Gen ρ A := h _ hD'
    _ = weight1Gen ρ (A.map (MulAut.conj g).toMonoidHom) :=
        (weight1Gen_map_conj ρ A g).symm

theorem weight1Gen_le_weight1Gen_sup_closure_conjList [Finite G] [Finite V]
    {ρ : Representation K G V} {A : Subgroup G} (hA : IsBestFGen ρ A) (ks : List G) :
    weight1Gen ρ A ≤
      weight1Gen ρ (A ⊔ Subgroup.closure {y : G | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹}) := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    have hset : {y : G | ∃ k' ∈ k :: ks, ∃ a ∈ A, y = k' * a * k'⁻¹} =
        {y : G | ∃ k' ∈ ks, ∃ a ∈ A, y = k' * a * k'⁻¹} ∪
          (A.map (MulAut.conj k).toMonoidHom : Set G) := by
      ext y
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union, Set.mem_setOf_eq,
        SetLike.mem_coe, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨k', hk' | hk', a, ha, rfl⟩
        · subst hk'
          exact Or.inr ⟨a, ha, rfl⟩
        · exact Or.inl ⟨k', hk', a, ha, rfl⟩
      · rintro (⟨k', hk', a, ha, rfl⟩ | ⟨a, ha, h⟩)
        · exact ⟨k', Or.inr hk', a, ha, rfl⟩
        · exact ⟨k, Or.inl rfl, a, ha, h.symm⟩
    have hcl : Subgroup.closure {y : G | ∃ k' ∈ k :: ks, ∃ a ∈ A, y = k' * a * k'⁻¹} =
        Subgroup.closure {y : G | ∃ k' ∈ ks, ∃ a ∈ A, y = k' * a * k'⁻¹} ⊔
          A.map (MulAut.conj k).toMonoidHom := by
      rw [hset, Subgroup.closure_union, Subgroup.closure_eq]
    rw [hcl]
    refine ih.trans ?_
    have hstep := weight1Gen_le_weight1Gen_sup (ρ := ρ)
      (Λ := A ⊔ Subgroup.closure {y : G | ∃ k' ∈ ks, ∃ a ∈ A, y = k' * a * k'⁻¹})
      (B := A.map (MulAut.conj k).toMonoidHom) (hA.map_conj k)
    simpa only [sup_assoc] using hstep

theorem weight1Gen_le_weight1Gen_normalClosure [Finite G] [Finite V]
    {ρ : Representation K G V} {A : Subgroup G} (hA : IsBestFGen ρ A) :
    weight1Gen ρ A ≤ weight1Gen ρ (Subgroup.normalClosure (A : Set G)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let ks : List G := (Finset.univ : Finset G).toList
  have hset : {y : G | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹} =
      (Group.conjugatesOfSet (A : Set G) : Set G) := by
    ext y
    constructor
    · rintro ⟨k, _, a, ha, rfl⟩
      exact Group.mem_conjugatesOfSet_iff.mpr ⟨a, ha, isConj_iff.mpr ⟨k, rfl⟩⟩
    · intro hy
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
      obtain ⟨k, rfl⟩ := isConj_iff.mp hconj
      exact ⟨k, Finset.mem_toList.mpr (Finset.mem_univ k), a, ha, rfl⟩
  have hN : Subgroup.normalClosure (A : Set G) =
      Subgroup.closure {y : G | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹} := by
    rw [Subgroup.normalClosure, hset]
  have hAle : A ≤ Subgroup.closure {y : G | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹} := by
    rw [← hN]
    exact Subgroup.le_normalClosure
  calc weight1Gen ρ A
      ≤ weight1Gen ρ (A ⊔ Subgroup.closure {y : G | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹}) :=
        weight1Gen_le_weight1Gen_sup_closure_conjList hA ks
    _ = weight1Gen ρ (Subgroup.normalClosure (A : Set G)) := by
        rw [sup_eq_right.mpr hAle, hN]

section Parabolic

variable {P : Type*} [Group P] [Finite P] {U L : Subgroup P} {p : ℕ}

@[expose] def CUGen (U A : Subgroup P) : Subgroup P :=
  U ⊓ Subgroup.centralizer (A : Set P)

@[simp] theorem mem_CUGen {U A : Subgroup P} {x : P} :
    x ∈ CUGen U A ↔ x ∈ U ∧ x ∈ Subgroup.centralizer (A : Set P) := by
  rw [CUGen]
  rfl

end Parabolic

section ConjAction

variable {P : Type*} [Group P] [Finite P] {U L : Subgroup P} [U.Normal]
  [IsMulCommutative ↥U] {K : Type*} [Field K] [Module K (Additive U)]

def fixSubGenEquivCUGen (ρ : Representation K L (Additive U))
    (hρ : ∀ (l : L) (u : U),
      (((ρ l) (Additive.ofMul u)).toMul : P) = (l : P) * (u : P) * (l : P)⁻¹)
    (A : Subgroup L) : fixSubGen ρ A ≃ CUGen U (A.map L.subtype) where
  toFun x :=
    ⟨(x.1.toMul : U), by
      refine (mem_CUGen).mpr ⟨(x.1.toMul).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨l, hl, rfl⟩
      have hx : (ρ l) x.1 = x.1 := x.2 l hl
      have hconj : (l : P) * ((x.1.toMul : U) : P) * (l : P)⁻¹ = ((x.1.toMul : U) : P) := by
        rw [← hρ l x.1.toMul]
        have hx' : (ρ l) (Additive.ofMul x.1.toMul) = Additive.ofMul x.1.toMul := by
          simpa using hx
        rw [hx']
        rfl
      calc (l : P) * ((x.1.toMul : U) : P)
          = (l : P) * ((x.1.toMul : U) : P) * (l : P)⁻¹ * (l : P) := by group
        _ = ((x.1.toMul : U) : P) * (l : P) := by rw [hconj]
    ⟩
  invFun y :=
    ⟨Additive.ofMul (⟨y.1, (mem_CUGen.mp y.2).1⟩ : U), by
      rw [mem_fixSubGen]
      intro l hl
      have hcent := (mem_CUGen.mp y.2).2
      have hcomm : (l : P) * y.1 = y.1 * (l : P) :=
        (Subgroup.mem_centralizer_iff.mp hcent) (l : P) (Subgroup.mem_map_of_mem L.subtype hl)
      have hU : ((ρ l) (Additive.ofMul (⟨y.1, (mem_CUGen.mp y.2).1⟩ : U))).toMul =
          (⟨y.1, (mem_CUGen.mp y.2).1⟩ : U) := by
        apply Subtype.ext
        have hρu := hρ l (⟨y.1, (mem_CUGen.mp y.2).1⟩ : U)
        rw [hρu]
        change (l : P) * y.1 * (l : P)⁻¹ = y.1
        rw [hcomm]
        group
      change ((ρ l) (Additive.ofMul (⟨y.1, (mem_CUGen.mp y.2).1⟩ : U))).toMul =
        (⟨y.1, (mem_CUGen.mp y.2).1⟩ : U)
      exact hU
    ⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl

end ConjAction

section Irreducible

theorem fixSubGen_eq_bot_of_normal_ne_bot {ρ : Representation K G V} {N : Subgroup G}
    [hN : N.Normal] [Representation.IsIrreducible ρ] (hNne : N ≠ ⊥)
    (hfaith : ∀ g : G, (∀ v : V, ρ g v = v) → g = 1) :
    fixSubGen ρ N = ⊥ := by
  let σ : Subrepresentation ρ :=
    { toSubmodule := fixSubGen ρ N
      apply_mem_toSubmodule := by
        intro g v hv
        rw [mem_fixSubGen] at hv ⊢
        intro n hn
        have hconj : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
        calc ρ n (ρ g v) = ρ (n * g) v := by rw [← Module.End.mul_apply, ← map_mul]
          _ = ρ (g * (g⁻¹ * n * g)) v := by
                rw [show n * g = g * (g⁻¹ * n * g) by group]
          _ = ρ g (ρ (g⁻¹ * n * g) v) := by rw [map_mul, Module.End.mul_apply]
          _ = ρ g v := by rw [hv _ hconj] }
  rcases IsSimpleOrder.eq_bot_or_eq_top σ with hbot | htop
  · have hσ : fixSubGen ρ N = ⊥ := by
      have h1 : σ.toSubmodule = (⊥ : Subrepresentation ρ).toSubmodule := by rw [hbot]
      exact (show σ.toSubmodule = fixSubGen ρ N from rfl).symm.trans
        (h1.trans (show (⊥ : Subrepresentation ρ).toSubmodule = ⊥ from rfl))
    exact hσ
  · exfalso
    have htop' : fixSubGen ρ N = ⊤ := by
      have h1 : σ.toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule := by rw [htop]
      exact (show σ.toSubmodule = fixSubGen ρ N from rfl).symm.trans
        (h1.trans (show (⊤ : Subrepresentation ρ).toSubmodule = ⊤ from rfl))
    apply hNne
    rw [eq_bot_iff]
    intro n hn
    have hn1 : ρ n = 1 := by
      ext v
      have hv : v ∈ fixSubGen ρ N := by rw [htop']; exact Submodule.mem_top
      simpa using mem_fixSubGen.mp hv n hn
    exact hfaith n fun v => by
      simpa using congrArg (fun f : Module.End K V => f v) hn1

theorem weight1Gen_le_card_of_irreducible [Finite G] [Finite V]
    {ρ : Representation K G V} [Representation.IsIrreducible ρ] {A : Subgroup G}
    (hA : IsBestFGen ρ A)
    (hfixN : fixSubGen ρ (Subgroup.normalClosure (A : Set G)) = ⊥) :
    weight1Gen ρ A ≤ Nat.card G := by
  let N := Subgroup.normalClosure (A : Set G)
  have hcard_bot : Nat.card (⊥ : Submodule K V) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨0, fun y => Subtype.ext ((Submodule.mem_bot (R := K)).mp y.2)⟩
  have h1 : weight1Gen ρ A ≤ weight1Gen ρ N := weight1Gen_le_weight1Gen_normalClosure hA
  have h2 : weight1Gen ρ N = Nat.card N := by
    rw [weight1Gen, hfixN, hcard_bot, mul_one]
  have h3 : Nat.card N ≤ Nat.card G :=
    Nat.card_le_card_of_injective (f := fun x : ↥N => (x : G)) Subtype.coe_injective
  calc weight1Gen ρ A ≤ weight1Gen ρ N := h1
    _ = Nat.card N := h2
    _ ≤ Nat.card G := h3

theorem weight1Gen_le_card_of_irreducible_of_faithful [Finite G] [Finite V]
    {ρ : Representation K G V} [Representation.IsIrreducible ρ] {A : Subgroup G}
    (hA : IsBestFGen ρ A) (hAne : A ≠ ⊥)
    (hfaith : ∀ g : G, (∀ v : V, ρ g v = v) → g = 1) :
    weight1Gen ρ A ≤ Nat.card G := by
  have hNne : Subgroup.normalClosure (A : Set G) ≠ ⊥ := by
    intro h
    apply hAne
    rw [eq_bot_iff]
    intro a ha
    have hmem : a ∈ Subgroup.normalClosure (A : Set G) := Subgroup.subset_normalClosure ha
    rwa [h] at hmem
  exact weight1Gen_le_card_of_irreducible hA
    (fixSubGen_eq_bot_of_normal_ne_bot (N := Subgroup.normalClosure (A : Set G)) hNne hfaith)

end Irreducible

end CFSG.HardMathSupport.GuralnickMalle
