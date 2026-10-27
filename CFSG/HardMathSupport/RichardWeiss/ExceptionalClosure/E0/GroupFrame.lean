module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.ConjAction
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.OuterLayers
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.PiFrame

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm
open scoped commutatorElement

attribute [local instance] IsMulCommutative.instCommGroup

variable {G : Type} [Group G] {V L S : Subgroup G} {N : ℕ}

@[expose] def Uadd (V L : Subgroup G) : AddSubgroup (Additive V) :=
  Subgroup.toAddSubgroup (⁅V, L⁆.subgroupOf V)

theorem mem_Uadd {V L : Subgroup G} {u : Additive V} :
    u ∈ Uadd V L ↔ ((Additive.toMul u : V) : G) ∈ ⁅V, L⁆ := Iff.rfl

@[expose] def piAdd (π : ↥⁅V, L⁆ →* Multiplicative (altHeart N)) : ↥(Uadd V L) →+ altHeart N where
  toFun u := Multiplicative.toAdd (π ⟨((Additive.toMul (u : Additive V) : V) : G), u.2⟩)
  map_zero' := by
    have : (⟨((Additive.toMul ((0 : ↥(Uadd V L)) : Additive V) : V) : G), (0 : ↥(Uadd V L)).2⟩ :
        ↥⁅V, L⁆) = 1 := by
      apply Subtype.ext; rfl
    rw [this, map_one]; rfl
  map_add' a b := by
    have : (⟨((Additive.toMul ((a + b : ↥(Uadd V L)) : Additive V) : V) : G), (a + b).2⟩ :
        ↥⁅V, L⁆) = ⟨((Additive.toMul (a : Additive V) : V) : G), a.2⟩ *
          ⟨((Additive.toMul (b : Additive V) : V) : G), b.2⟩ := by
      apply Subtype.ext; rfl
    rw [this, map_mul]; rfl

theorem commutator_le_of_normalizes {V L S : Subgroup G}
    (hMV : ∀ m ∈ L ⊔ S, ∀ v ∈ V, m * v * m⁻¹ ∈ V) : ⁅V, L⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have h1 := hMV l (Subgroup.mem_sup_left hl) v⁻¹ (V.inv_mem hv)
  have : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [this]
  exact V.mul_mem hv h1

theorem conj_sub_coe (hMV : ∀ m ∈ L ⊔ S, ∀ v ∈ V, m * v * m⁻¹ ∈ V) (m : ↥(L ⊔ S))
    (w : Additive V) :
    ((Additive.toMul ((conjEnd hMV m) w - w) : V) : G) =
      (m : G) * ((Additive.toMul w : V) : G) * (m : G)⁻¹ * ((Additive.toMul w : V) : G)⁻¹ := by
  rw [toMul_sub]
  simp only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rfl

variable [IsMulCommutative V]

theorem piFrame_of_group
    (hMV : ∀ m ∈ L ⊔ S, ∀ v ∈ V, m * v * m⁻¹ ∈ V)
    (hML : ∀ m ∈ L ⊔ S, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hV2 : ∀ v ∈ V, v * v = 1)
    (π : ↥⁅V, L⁆ →* Multiplicative (altHeart N)) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (hπ : Function.Surjective π) (hequiv : SectionEquiv ⁅V, L⁆ (L ⊔ S) π θ)
    (hAθ : ∀ σ ∈ alternatingGroup (Fin N), ∃ l : ↥L, θ ⟨(l : G), Subgroup.mem_sup_left l.2⟩ = σ)
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (V : Set G))
    (hπker : π.ker = (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅V, L⁆)
    (hSlay : S ≤ layerTriv V ⁅V, L⁆ (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G))) :
    PiFrame (W := Additive V) θ (conjEnd hMV) (Uadd V L) (piAdd π) (L.subgroupOf (L ⊔ S))
      (S.subgroupOf (L ⊔ S)) := by
  have hUV : ⁅V, L⁆ ≤ V := commutator_le_of_normalizes hMV
  have hstable : ∀ (m : ↥(L ⊔ S)), ∀ u ∈ Uadd V L, (conjEnd hMV) m u ∈ Uadd V L := by
    intro m u hu
    rw [mem_Uadd] at hu ⊢
    exact conj_mem_commutator (V := V) (L := L) (hMV m m.2) (hML m m.2) _ hu
  refine ⟨?_, ?_, hstable, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hV2 _ (Additive.toMul w).2
  · intro m hm
    apply AddMonoidHom.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp (hker m hm) _ (Additive.toMul v).2
    show (m : G) * ((Additive.toMul v : V) : G) * (m : G)⁻¹ = ((Additive.toMul v : V) : G)
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  · intro m u
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (piAdd π u)
    have h1 := hequiv m ⟨((Additive.toMul (u : Additive V) : V) : G), u.2⟩
      ⟨(((conjEnd hMV m) (u : Additive V)).toMul : V), hstable m u u.2⟩ rfl x hx.symm
    show Multiplicative.toAdd (π ⟨_, _⟩) = _
    rw [h1, ← hx, altAct_mk]
  · intro v
    obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd v)
    refine ⟨⟨Additive.ofMul ⟨(u : G), hUV u.2⟩, u.2⟩, ?_⟩
    show Multiplicative.toAdd (π ⟨(u : G), _⟩) = v
    have : (⟨(u : G), u.2⟩ : ↥⁅V, L⁆) = u := Subtype.ext rfl
    rw [this, hu]
    rfl
  · intro σ hσ
    obtain ⟨l, hl⟩ := hAθ σ hσ
    exact ⟨⟨(l : G), Subgroup.mem_sup_left l.2⟩, Subgroup.mem_subgroupOf.2 l.2, hl⟩
  · intro l hl w
    have hw : ((Additive.toMul w : V) : G) ∈ V := (Additive.toMul w).2
    have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
    have h := Subgroup.commutator_mem_commutator hl' hw
    rw [Subgroup.commutator_comm L V] at h
    show ((Additive.toMul ((conjEnd hMV l) w - w) : V) : G) ∈ ⁅V, L⁆
    convert h using 1
    rw [conj_sub_coe]
    rfl
  · intro s hs w
    have hs' : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    have h := (hSlay hs').2.2.2 _ (Additive.toMul w).2
    show ((Additive.toMul ((conjEnd hMV s) w - w) : V) : G) ∈ ⁅V, L⁆
    convert h using 1
    rw [conj_sub_coe]
  · intro s hs u hu
    have hs' : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    have hπ1 : π ⟨((Additive.toMul (u : Additive V) : V) : G), u.2⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      exact hu
    have hmem : (⟨((Additive.toMul (u : Additive V) : V) : G), u.2⟩ : ↥⁅V, L⁆) ∈ π.ker :=
      MonoidHom.mem_ker.2 hπ1
    rw [hπker, Subgroup.mem_subgroupOf] at hmem
    have hc := (hSlay hs').2.2.1 _ hmem
    apply Additive.toMul.injective
    apply Subtype.ext
    show (s : G) * ((Additive.toMul (u : Additive V) : V) : G) * (s : G)⁻¹ =
      ((Additive.toMul (u : Additive V) : V) : G)
    rw [mul_inv_eq_iff_eq_mul]
    exact hc

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
