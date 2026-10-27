module

public import CFSG.Goldschmidt.Steps.Components
public import CFSG.Goldschmidt.StrongClosure

public section

namespace CFSG.CGT.T75D

open CFSG.Open CFSG.Goldschmidt
open scoped Pointwise

section Types

theorem goldschmidtSimpleType_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : goldschmidtSimpleType A) : goldschmidtSimpleType B := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨p, f, hp, hpo, hf, h5, h8, ⟨e'⟩⟩ |
    ⟨m, hm, hcard⟩ | hJ
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hpo, hf, h5, h8, ⟨e.symm.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, hm, (Nat.card_congr e.symm.toEquiv).trans hcard⟩))))
  · obtain ⟨e'⟩ := hJ
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans e'⟩))))

end Types

section Split

variable {M : Type} [Group M] [Finite M]

theorem comp_comm_of_ne {X Y : Subgroup M} (hX : IsComponentOf X ⊤) (hY : IsComponentOf Y ⊤)
    (hne : X ≠ Y) : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  have h := N8b M X Y hX hY hne
  intro x hx y hy
  have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).1 h
  exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) y hy).symm

theorem pCore_comm_comp {X : Subgroup M} (hX : IsComponentOf X ⊤) :
    ∀ q ∈ CFSG.Open.pCore 2 M, ∀ x ∈ X, q * x = x * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (CFSG.pCore 2 M).Normal := inferInstance
  have hnil : Group.IsNilpotent ↥(CFSG.pCore 2 M) :=
    (CFSG.pCore_isPGroup (p := 2) (G := M)).isNilpotent
  have hs : Group.IsSolvable ↥(CFSG.pCore 2 M) := inferInstance
  have h := N8c M X (CFSG.pCore 2 M) hX hn hs
  intro q hq x hx
  have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).1 h
  exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) q hq)

theorem exists_component_not_le (hO : goldschmidtOddCore M = ⊥)
    (hM : CFSG.Open.pCore 2 M ⊔ goldschmidtLayer M = ⊤) {M₁ : Subgroup M}
    (hQ : CFSG.Open.pCore 2 M ≤ M₁) {m : M} (hm : m ∉ M₁) :
    ∃ X : Subgroup M, IsComponentOf X ⊤ ∧ ¬ X ≤ M₁ ∧ ∃ x ∈ X, m * x ≠ x * m := by
  by_contra hcon
  push Not at hcon
  set Q : Subgroup M := CFSG.Open.pCore 2 M with hQdef
  set E : Subgroup M := goldschmidtLayer M with hEdef
  set S₁ : Set (Subgroup M) := {K | IsComponentOf K ⊤ ∧ K ≤ M₁} with hS₁
  set S₂ : Set (Subgroup M) := {K | IsComponentOf K ⊤ ∧ ¬ K ≤ M₁} with hS₂
  set E₁ : Subgroup M := sSup S₁ with hE₁def
  set E₂ : Subgroup M := sSup S₂ with hE₂def
  have hset : {K : Subgroup M | IsComponentOf K ⊤} = S₁ ∪ S₂ := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_union, hS₁, hS₂]
    constructor
    · intro hK
      by_cases hKM : K ≤ M₁
      · exact Or.inl ⟨hK, hKM⟩
      · exact Or.inr ⟨hK, hKM⟩
    · rintro (h | h) <;> exact h.1
  have hE : E = E₁ ⊔ E₂ := by
    rw [hEdef, goldschmidtLayer, hset, sSup_union]
  have hE₁M : E₁ ≤ M₁ := sSup_le fun K hK => hK.2
  have hcomm12 : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := by
    have h1 : ∀ K₂ ∈ S₂, E₁ ≤ Subgroup.centralizer (K₂ : Set M) := by
      intro K₂ hK₂
      refine sSup_le fun K₁ hK₁ x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      have hne : K₁ ≠ K₂ := fun h => hK₂.2 (h ▸ hK₁.2)
      exact (comp_comm_of_ne hK₁.1 hK₂.1 hne x hx y hy).symm
    intro x hx
    have h2 : E₂ ≤ Subgroup.centralizer ({x} : Set M) := by
      refine sSup_le fun K₂ hK₂ y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 (h1 K₂ hK₂ hx) y hy)
    intro y hy
    exact ((Subgroup.mem_centralizer_singleton_iff).1 (h2 hy)).symm
  have hQE : ∀ q ∈ Q, ∀ e ∈ E, q * e = e * q := by
    intro q hq
    have : E ≤ Subgroup.centralizer ({q} : Set M) := by
      refine sSup_le fun K hK y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (pCore_comm_comp hK q hq y hy).symm
    intro e he
    exact ((Subgroup.mem_centralizer_singleton_iff).1 (this he)).symm
  have hmE₂ : ∀ y ∈ E₂, m * y = y * m := by
    have : E₂ ≤ Subgroup.centralizer ({m} : Set M) := by
      refine sSup_le fun K hK y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcon K hK.1 hK.2 y hy).symm
    intro y hy
    exact ((Subgroup.mem_centralizer_singleton_iff).1 (this hy)).symm
  have hnormE₂ : E₁ ≤ Subgroup.normalizer (E₂ : Set M) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : x * y * x⁻¹ = y := by rw [hcomm12 x hx y hy]; group
      rw [this]; exact hy
    · intro hy
      have hc : x⁻¹ * (x * y * x⁻¹) = (x * y * x⁻¹) * x⁻¹ :=
        hcomm12 x⁻¹ (E₁.inv_mem hx) _ hy
      have : y = x * y * x⁻¹ := by
        calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = (x * y * x⁻¹) * x⁻¹ * x := by rw [hc]
          _ = x * y * x⁻¹ := by group
      rw [this]; exact hy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : Q.Normal := by
    rw [hQdef]
    infer_instance
  have hEQ : E ⊔ Q = ⊤ := by rw [sup_comm]; exact hM
  have hmEQ : m ∈ (E : Set M) * (Q : Set M) := by
    rw [← Subgroup.mul_normal E Q, hEQ]
    trivial
  obtain ⟨e, he, q, hq, hmeq⟩ := hmEQ
  have heE : e ∈ ((E₁ ⊔ E₂ : Subgroup M) : Set M) := by rw [← hE]; exact he
  rw [Subgroup.coe_mul_of_left_le_normalizer_right E₁ E₂ hnormE₂] at heE
  obtain ⟨e₁, he₁, e₂, he₂, hee⟩ := heE
  have hE₂E : E₂ ≤ E := by rw [hE]; exact le_sup_right
  have hE₁E : E₁ ≤ E := by rw [hE]; exact le_sup_left
  have hmdec : m = e₁ * e₂ * q := by rw [← hmeq, ← hee]
  have he₂c : ∀ y ∈ E₂, y * e₂ = e₂ * y := by
    intro y hy
    have h1 : e₁⁻¹ * y = y * e₁⁻¹ := hcomm12 e₁⁻¹ (E₁.inv_mem he₁) y hy
    have h2 : m * y = y * m := hmE₂ y hy
    have h3 : q⁻¹ * y = y * q⁻¹ := hQE q⁻¹ (Q.inv_mem hq) y (hE₂E hy)
    have he₂eq : e₂ = e₁⁻¹ * m * q⁻¹ := by rw [hmdec]; group
    rw [he₂eq]
    calc y * (e₁⁻¹ * m * q⁻¹) = (y * e₁⁻¹) * m * q⁻¹ := by group
      _ = (e₁⁻¹ * y) * m * q⁻¹ := by rw [h1]
      _ = e₁⁻¹ * (y * m) * q⁻¹ := by group
      _ = e₁⁻¹ * (m * y) * q⁻¹ := by rw [h2]
      _ = e₁⁻¹ * m * (y * q⁻¹) := by group
      _ = e₁⁻¹ * m * (q⁻¹ * y) := by rw [h3]
      _ = e₁⁻¹ * m * q⁻¹ * y := by group
  have he₂E : e₂ ∈ E := hE₂E he₂
  have hcenter : (⟨e₂, he₂E⟩ : ↥E) ∈ Subgroup.center ↥E := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : M) * e₂ = e₂ * (g : M)
    have hg : (g : M) ∈ ((E₁ ⊔ E₂ : Subgroup M) : Set M) := by rw [← hE]; exact g.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E₁ E₂ hnormE₂] at hg
    obtain ⟨f₁, hf₁, f₂, hf₂, hff⟩ := hg
    rw [← hff]
    calc f₁ * f₂ * e₂ = f₁ * (f₂ * e₂) := by group
      _ = f₁ * (e₂ * f₂) := by rw [he₂c f₂ hf₂]
      _ = (f₁ * e₂) * f₂ := by group
      _ = (e₂ * f₁) * f₂ := by rw [hcomm12 f₁ hf₁ e₂ he₂]
      _ = e₂ * (f₁ * f₂) := by group
  have hN8d := (N8d M hO).2.1
  have he₂Q : e₂ ∈ Q := hN8d ⟨⟨e₂, he₂E⟩, hcenter, rfl⟩
  have hm1 : m ∈ M₁ := by
    rw [hmdec]
    exact M₁.mul_mem (M₁.mul_mem (hE₁M he₁) (hQ he₂Q)) (hQ hq)
  exact hm hm1

end Split

section Comp

variable {M : Type} [Group M] [Finite M] {X K : Subgroup M}

theorem pCore_le_centralizer (hX : IsComponentOf X ⊤) :
    CFSG.Open.pCore 2 M ≤ Subgroup.centralizer (X : Set M) := fun q hq =>
  Subgroup.mem_centralizer_iff.2 fun y hy => (pCore_comm_comp hX q hq y hy).symm

theorem comp_le_centralizer_of_ne (hK : IsComponentOf K ⊤) (hX : IsComponentOf X ⊤)
    (hne : K ≠ X) : K ≤ Subgroup.centralizer (X : Set M) := fun k hk =>
  Subgroup.mem_centralizer_iff.2 fun y hy => (comp_comm_of_ne hK hX hne k hk y hy).symm

theorem comp_normal (hM : CFSG.Open.pCore 2 M ⊔ goldschmidtLayer M = ⊤)
    (hX : IsComponentOf X ⊤) : X.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hM]
  refine sup_le ((pCore_le_centralizer hX).trans (Subgroup.centralizer_le_normalizer (X : Set M)))
    (sSup_le fun L hL => ?_)
  by_cases h : L = X
  · rw [h]; exact Subgroup.le_normalizer
  · exact (comp_le_centralizer_of_ne hL hX h).trans (Subgroup.centralizer_le_normalizer (X : Set M))

theorem comp_sup_centralizer (hM : CFSG.Open.pCore 2 M ⊔ goldschmidtLayer M = ⊤)
    (hX : IsComponentOf X ⊤) : X ⊔ Subgroup.centralizer (X : Set M) = ⊤ := by
  rw [eq_top_iff, ← hM]
  refine sup_le (le_sup_of_le_right (pCore_le_centralizer hX)) (sSup_le fun L hL => ?_)
  by_cases h : L = X
  · rw [h]; exact le_sup_left
  · exact le_sup_of_le_right (comp_le_centralizer_of_ne hL hX h)

omit [Finite M] in
theorem mem_centralizer_iff_mem_center (x : ↥X) :
    (x : M) ∈ Subgroup.centralizer (X : Set M) ↔ x ∈ Subgroup.center ↥X := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    exact Subtype.ext (h g g.2)
  · intro h g hg
    exact congrArg Subtype.val (h ⟨g, hg⟩)

omit [Finite M] in
theorem exists_mulEquiv_quotient_centralizer [X.Normal]
    (hsup : X ⊔ Subgroup.centralizer (X : Set M) = ⊤) :
    Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* (M ⧸ Subgroup.centralizer (X : Set M))) := by
  set C : Subgroup M := Subgroup.centralizer (X : Set M) with hC
  let φ : ↥X →* M ⧸ C := (QuotientGroup.mk' C).comp X.subtype
  have hφ : Function.Surjective φ := by
    intro m
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective m
    have hm : m ∈ ((X ⊔ C : Subgroup M) : Set M) := by rw [hsup]; trivial
    rw [Subgroup.mul_normal] at hm
    obtain ⟨x, hx, c, hc, rfl⟩ := hm
    refine ⟨⟨x, hx⟩, ?_⟩
    show (QuotientGroup.mk x : M ⧸ C) = QuotientGroup.mk (x * c)
    rw [QuotientGroup.eq]
    simpa using C.inv_mem hc
  have hker : φ.ker = Subgroup.center ↥X := by
    ext x
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (x : M) : M ⧸ C) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact mem_centralizer_iff_mem_center x
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

end Comp

end CFSG.CGT.T75D
