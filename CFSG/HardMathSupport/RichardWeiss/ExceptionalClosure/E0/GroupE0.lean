module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.GroupFrame
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Frame
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.PairPerm

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm
open scoped commutatorElement

attribute [local instance] IsMulCommutative.instCommGroup

variable {G : Type} [Group G]

@[expose] def Phi (S : Subgroup G) : Subgroup G :=
  ⁅S, S⁆ ⊔ Subgroup.closure {x | ∃ s ∈ S, x = s ^ 2}

theorem conj_mem_Phi {S : Subgroup G} {m : G} (hm : ∀ s ∈ S, m * s * m⁻¹ ∈ S) :
    ∀ y ∈ Phi S, m * y * m⁻¹ ∈ Phi S := by
  have hle : Phi S ≤ (Phi S).comap (MulAut.conj m).toMonoidHom := by
    unfold Phi
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_comap]
      have e : (MulAut.conj m).toMonoidHom ⁅x, y⁆ = ⁅m * x * m⁻¹, m * y * m⁻¹⁆ := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator (hm x hx) (hm y hy))
    · rw [Subgroup.closure_le]
      rintro x ⟨s, hs, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : (MulAut.conj m).toMonoidHom (s ^ 2) = (m * s * m⁻¹) ^ 2 := by
        simp [pow_two, mul_assoc]
      rw [e]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨m * s * m⁻¹, hm s hs, rfl⟩)
  intro y hy
  exact hle hy

@[expose] def Yadd (V S : Subgroup G) : AddSubgroup (Additive V) :=
  Subgroup.toAddSubgroup ((V ⊓ Phi S).subgroupOf V)

theorem mem_Yadd {V S : Subgroup G} {y : Additive V} :
    y ∈ Yadd V S ↔ ((Additive.toMul y : V) : G) ∈ Phi S := by
  show ((Additive.toMul y : V) : G) ∈ V ⊓ Phi S ↔ _
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨(Additive.toMul y : V).2, h⟩

variable {V L S : Subgroup G} {N : ℕ} [IsMulCommutative V]

theorem e0Frame_of_group
    (hMV : ∀ m ∈ L ⊔ S, ∀ v ∈ V, m * v * m⁻¹ ∈ V)
    (hML : ∀ m ∈ L ⊔ S, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hV2 : ∀ v ∈ V, v * v = 1) (hVS : V ≤ S)
    (π : ↥⁅V, L⁆ →* Multiplicative (altHeart N)) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (hπ : Function.Surjective π) (hequiv : SectionEquiv ⁅V, L⁆ (L ⊔ S) π θ)
    (hAθ : ∀ σ ∈ alternatingGroup (Fin N), ∃ l : ↥L, θ ⟨(l : G), Subgroup.mem_sup_left l.2⟩ = σ)
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (V : Set G))
    (hπker : π.ker = (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅V, L⁆)
    (hSlay : S ≤ layerTriv V ⁅V, L⁆ (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)))
    {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)} {Δ₀ : Finset (Fin N)}
    (hshape : E0Shape P ω Δ₀) (hN : 10 ≤ N)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)}) :
    E0Frame (W := Additive V) θ (conjEnd hMV) (Uadd V L) (piAdd π) (L.subgroupOf (L ⊔ S))
      (S.subgroupOf (L ⊔ S)) P ω Δ₀ (Yadd V S) := by
  refine ⟨piFrame_of_group hMV hML hV2 π θ hπ hequiv hAθ hker hπker hSlay, hshape, hN,
    hshape.even_card, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ
    have : σ ∈ (S.subgroupOf (L ⊔ S)).map θ ↔ σ ∈ E0grp P ω Δ₀ := by rw [hθ]; rfl
    rw [← this, Subgroup.mem_map]
  · intro m hm
    exact Subgroup.mem_subgroupOf.2 (hθS m hm)
  · intro l hl u hu
    have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
    have hπ1 : π ⟨((Additive.toMul (u : Additive V) : V) : G), u.2⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      exact hu
    have hmem : (⟨((Additive.toMul (u : Additive V) : V) : G), u.2⟩ : ↥⁅V, L⁆) ∈ π.ker :=
      MonoidHom.mem_ker.2 hπ1
    rw [hπker, Subgroup.mem_subgroupOf] at hmem
    have hc := Subgroup.mem_centralizer_iff.mp hmem.2 (l : G) hl'
    apply Additive.toMul.injective
    apply Subtype.ext
    show (l : G) * ((Additive.toMul (u : Additive V) : V) : G) * (l : G)⁻¹ =
      ((Additive.toMul (u : Additive V) : V) : G)
    rw [mul_inv_eq_iff_eq_mul]
    exact hc
  · intro s hs w'
    have hs' : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    have hw : ∀ w : Additive V, conjEnd hMV s w - w ∈ Yadd V S := by
      intro w
      rw [mem_Yadd, conj_sub_coe]
      exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hs' (hVS (Additive.toMul w).2))
    exact hw w'
  · intro m hm y hy
    rw [mem_Yadd] at hy ⊢
    have hm' : ∀ s ∈ S, (m : G) * s * (m : G)⁻¹ ∈ S := fun s hs => by
      have := hm ⟨s, Subgroup.mem_sup_right hs⟩ (Subgroup.mem_subgroupOf.2 hs)
      exact Subgroup.mem_subgroupOf.1 this
    exact conj_mem_Phi hm' _ hy

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
