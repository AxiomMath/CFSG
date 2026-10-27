module

public import CFSG.ClassicalInvolution.Q3.TL4D1Facts
import CFSG.ClassicalInvolution.Q3.TL4D1MAN
import CFSG.ClassicalInvolution.Q3.TL4D1MAGLF
public import CFSG.ClassicalInvolution.Q3.AE.E64

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

namespace RecogS

section Wreath

open AE

variable {n : ℕ}

private def wrVec (n : ℕ) : Multiplicative (Fin n → ZMod 2) →* Wr n where
  toFun f := Wr.ofVec f.toAdd
  map_one' := rfl
  map_mul' f g := (TL4.ofVec_mul_ofVec f.toAdd g.toAdd).symm

private def wrPerm (n : ℕ) : Equiv.Perm (Fin n) →* Wr n where
  toFun s := Wr.ofPerm s
  map_one' := rfl
  map_mul' s t := (ofPerm_mul s t).symm

private theorem mkQ_ofVec_eq_one_iff (v : Fin n → ZMod 2) :
    mkQ n (Wr.ofVec v) = 1 ↔ v = 0 ∨ v = fun _ => 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_piSub]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Wr.vec h)
    · exact Or.inr (congrArg Wr.vec h)
  · rintro (h | h)
    · exact Or.inl (Wr.ext h rfl)
    · exact Or.inr (Wr.ext h rfl)

private theorem mkQ_ofPerm_conj (s : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) :
    mkQ n (Wr.ofPerm s) * mkQ n (Wr.ofVec v) * (mkQ n (Wr.ofPerm s))⁻¹ =
      mkQ n (Wr.ofVec fun i => v (s.symm i)) := by
  rw [← map_inv, ← map_mul, ← map_mul, TL4.conj_ofVec]
  rfl

private theorem eq_one_of_mkQ_mul_eq_one {v : Fin n → ZMod 2} {s : Equiv.Perm (Fin n)}
    (h : mkQ n (Wr.ofVec v) * mkQ n (Wr.ofPerm s) = 1) : s = 1 := by
  have h1 := congrArg (TL4.permBar n) h
  rw [map_mul, TL4.permBar_mkQ, TL4.permBar_mkQ, map_one] at h1
  exact (one_mul s).symm.trans h1

private theorem mkQ_mul_mem_aeBarOver {A : Subgroup (Equiv.Perm (Fin n))} {v : Fin n → ZMod 2}
    (hv : ∑ i, v i = 0) {s : Equiv.Perm (Fin n)} (hs : s ∈ A) (hsg : Equiv.Perm.sign s = 1) :
    mkQ n (Wr.ofVec v) * mkQ n (Wr.ofPerm s) ∈ aeBarOver A := by
  rw [← map_mul]
  exact Subgroup.mem_map_of_mem _
    (mul_mem (TL4.ofVec_mem_aeSubOver hv) (ofPerm_mem_aeSubOver hs hsg))

private theorem exists_of_mem_aeBarOver {A : Subgroup (Equiv.Perm (Fin n))} {x : AEQ n}
    (hx : x ∈ aeBarOver A) : ∃ v : Fin n → ZMod 2, ∑ i, v i = 0 ∧
      ∃ s ∈ A, mkQ n (Wr.ofVec v) * mkQ n (Wr.ofPerm s) = x := by
  obtain ⟨a, ⟨⟨hw, -⟩, hA⟩, rfl⟩ := hx
  exact ⟨a.vec, hw, a.perm, hA, by rw [← map_mul, ← TL4.eq_ofVec_mul_ofPerm]⟩

private theorem sum_ofAdd_comp_symm (s : Equiv.Perm (Fin n))
    (f : Multiplicative (Fin n → ZMod 2)) :
    ∑ i, (Multiplicative.ofAdd fun i => f.toAdd (s.symm i)).toAdd i = ∑ i, f.toAdd i :=
  sum_perm_apply s f.toAdd

private def evenSub (n : ℕ) : Subgroup (Multiplicative (Fin n → ZMod 2)) where
  carrier := {f | ∑ i, f.toAdd i = 0}
  mul_mem' {f g} hf hg := by
    change ∑ i, f.toAdd i = 0 at hf
    change ∑ i, g.toAdd i = 0 at hg
    change ∑ i, (f.toAdd i + g.toAdd i) = 0
    rw [Finset.sum_add_distrib, hf, hg, add_zero]
  one_mem' := Finset.sum_const_zero
  inv_mem' {f} hf := by
    change ∑ i, f.toAdd i = 0 at hf
    change ∑ i, -f.toAdd i = 0
    rw [Finset.sum_neg_distrib, hf, neg_zero]

end Wreath

theorem exists_hom_of_isComplement' {X M : Type*} [Group X] [Group M] {Q H : Subgroup X}
    [Q.Normal] (hQH : Q.IsComplement' H) (ψ : Q →* M) (τ : H →* M)
    (hc : ∀ (x : H) (q : Q) (hq : (x : X) * q * (x : X)⁻¹ ∈ Q),
      τ x * ψ q * (τ x)⁻¹ = ψ ⟨(x : X) * q * (x : X)⁻¹, hq⟩) :
    ∃ φ : X →* M, (∀ q : Q, φ q = ψ q) ∧ ∀ x : H, φ x = τ x := by
  let e := SemidirectProduct.mulEquivSubgroup hQH
  refine ⟨(SemidirectProduct.lift ψ τ ?_).comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro x
    ext q
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hc x q (Subgroup.Normal.conj_mem inferInstance (q : X) q.2 (x : X))]
    congr 1
  · intro q
    have h1 : e.symm (q : X) = SemidirectProduct.inl q := by
      rw [MulEquiv.symm_apply_eq]
      simp [e, SemidirectProduct.mulEquivSubgroup_apply]
    simp [h1]
  · intro x
    have h1 : e.symm (x : X) = SemidirectProduct.inr x := by
      rw [MulEquiv.symm_apply_eq]
      simp [e, SemidirectProduct.mulEquivSubgroup_apply]
    simp [h1]

end RecogS

variable {G : Type*} [Group G] {n : ℕ}

structure AESplitHyp (V H : Subgroup G) (σ : H →* Equiv.Perm (Fin n))
    (β : Multiplicative (Fin n → ZMod 2) →* G) : Prop where
  compl : V.IsComplement' H
  inj : Function.Injective σ
  mem_iff : ∀ g : G, g ∈ V ↔
    ∃ f : Multiplicative (Fin n → ZMod 2), ∑ i, f.toAdd i = 0 ∧ β f = g
  eq_one_iff : ∀ f : Multiplicative (Fin n → ZMod 2), ∑ i, f.toAdd i = 0 →
    (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1)
  conj : ∀ (h : H) (f : Multiplicative (Fin n → ZMod 2)), ∑ i, f.toAdd i = 0 →
    (h : G) * β f * (h : G)⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((σ h).symm i))

namespace AESplitHyp

theorem of_odd (hn : Odd n) {V H : Subgroup G} {σ : H →* Equiv.Perm (Fin n)}
    {β : Multiplicative (Fin n → ZMod 2) →* G} (hVH : V.IsComplement' H)
    (hσ : Function.Injective σ) (hV : β.range = V)
    (hker : ∀ f : Multiplicative (Fin n → ZMod 2), β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1)
    (hconj : ∀ (h : H) (f : Multiplicative (Fin n → ZMod 2)),
      (h : G) * β f * (h : G)⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((σ h).symm i))) :
    AESplitHyp V H σ β := by
  have hπ : β (Multiplicative.ofAdd fun _ => 1) = 1 := (hker _).mpr (Or.inr rfl)
  refine ⟨hVH, hσ, fun g => ?_, fun f _ => hker f, fun h f _ => hconj h f⟩
  rw [← hV]
  constructor
  · rintro ⟨f, rfl⟩
    by_cases h0 : ∑ i, f.toAdd i = 0
    · exact ⟨f, h0, rfl⟩
    · refine ⟨f * Multiplicative.ofAdd fun _ => 1, ?_, by rw [map_mul, hπ, mul_one]⟩
      have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
      have hn1 : ∑ _i : Fin n, (1 : ZMod 2) = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        exact hn.natCast_zmod_two
      change ∑ i, (f.toAdd i + 1) = 0
      rw [Finset.sum_add_distrib, (h01 _).resolve_left h0, hn1]
      decide
  · rintro ⟨f, -, rfl⟩
    exact ⟨f, rfl⟩

section General

variable {V H : Subgroup G} {σ : H →* Equiv.Perm (Fin n)}
  {β : Multiplicative (Fin n → ZMod 2) →* G} (hS : AESplitHyp V H σ β)
include hS

theorem conj_mem (x : H) {v : G} (hv : v ∈ V) : (x : G) * v * (x : G)⁻¹ ∈ V := by
  obtain ⟨f, hf, rfl⟩ := (hS.mem_iff v).mp hv
  rw [hS.conj x f hf]
  exact (hS.mem_iff _).mpr ⟨_, (RecogS.sum_ofAdd_comp_symm (σ x) f).trans hf, rfl⟩

theorem exists_eq_mul (g : G) : ∃ f : Multiplicative (Fin n → ZMod 2), ∑ i, f.toAdd i = 0 ∧
    ∃ x : H, β f * x = g := by
  obtain ⟨⟨⟨v, hv⟩, ⟨x, hx⟩⟩, h⟩ := hS.compl.2 g
  obtain ⟨f, hf, rfl⟩ := (hS.mem_iff v).mp hv
  exact ⟨f, hf, ⟨x, hx⟩, h⟩

theorem normal : V.Normal where
  conj_mem v hv g := by
    obtain ⟨f, hf0, x, rfl⟩ := hS.exists_eq_mul g
    have hf : β f ∈ V := (hS.mem_iff _).mpr ⟨f, hf0, rfl⟩
    have h1 := hS.conj_mem x hv
    have h2 : β f * x * v * (β f * x)⁻¹ = β f * (x * v * (x : G)⁻¹) * (β f)⁻¹ := by group
    rw [h2]
    exact V.mul_mem (V.mul_mem hf h1) (V.inv_mem hf)

theorem exists_vecHom : ∃ ψ : V →* AE.AEQ n, ∀ (v : V) (f : Multiplicative (Fin n → ZMod 2)),
    ∑ i, f.toAdd i = 0 → β f = v → ψ v = AE.mkQ n (AE.Wr.ofVec f.toAdd) := by
  let E := RecogS.evenSub n
  have hmem : ∀ f : E, β f ∈ V := fun f => (hS.mem_iff _).mpr ⟨f, f.2, rfl⟩
  let β' : E →* V := (β.comp E.subtype).codRestrict V hmem
  have hsurj : Function.Surjective β' := by
    rintro ⟨v, hv⟩
    obtain ⟨f, hf, rfl⟩ := (hS.mem_iff v).mp hv
    exact ⟨⟨f, hf⟩, rfl⟩
  let ψ₀ : E →* AE.AEQ n := (AE.mkQ n).comp ((RecogS.wrVec n).comp E.subtype)
  have hk : β'.ker ≤ ψ₀.ker := by
    intro f hf
    rw [MonoidHom.mem_ker] at hf ⊢
    exact (RecogS.mkQ_ofVec_eq_one_iff _).mpr
      ((hS.eq_one_iff f f.2).mp (congrArg Subtype.val hf))
  refine ⟨β'.liftOfSurjective hsurj ⟨ψ₀, hk⟩, fun v f hf hfv => ?_⟩
  have h2 : v = β' ⟨f, hf⟩ := Subtype.ext hfv.symm
  rw [h2]
  exact MonoidHom.liftOfRightInverse_comp_apply β' _ (Function.rightInverse_surjInv hsurj)
    ⟨ψ₀, hk⟩ ⟨f, hf⟩

theorem compat {ψ : V →* AE.AEQ n}
    (hψ : ∀ (v : V) (f : Multiplicative (Fin n → ZMod 2)), ∑ i, f.toAdd i = 0 → β f = v →
      ψ v = AE.mkQ n (AE.Wr.ofVec f.toAdd))
    (x : H) (q : V) (hq : (x : G) * q * (x : G)⁻¹ ∈ V) :
    AE.mkQ n (AE.Wr.ofPerm (σ x)) * ψ q * (AE.mkQ n (AE.Wr.ofPerm (σ x)))⁻¹ =
      ψ ⟨(x : G) * q * (x : G)⁻¹, hq⟩ := by
  obtain ⟨f, hf, hfq⟩ := (hS.mem_iff q).mp q.2
  rw [hψ q f hf hfq, RecogS.mkQ_ofPerm_conj]
  refine (hψ _ (Multiplicative.ofAdd fun i => f.toAdd ((σ x).symm i))
    ((RecogS.sum_ofAdd_comp_symm (σ x) f).trans hf) ?_).symm
  rw [← hS.conj x f hf, hfq]

theorem exists_hom_apply : ∃ φ : G →* AE.AEQ n,
    (∀ f : Multiplicative (Fin n → ZMod 2), ∑ i, f.toAdd i = 0 →
      φ (β f) = AE.mkQ n (AE.Wr.ofVec f.toAdd)) ∧
    ∀ h : H, φ h = AE.mkQ n (AE.Wr.ofPerm (σ h)) := by
  haveI := hS.normal
  obtain ⟨ψ, hψ⟩ := hS.exists_vecHom
  let τ : H →* AE.AEQ n := (AE.mkQ n).comp ((RecogS.wrPerm n).comp σ)
  obtain ⟨φ, hφV, hφH⟩ := RecogS.exists_hom_of_isComplement' hS.compl ψ τ (hS.compat hψ)
  refine ⟨φ, fun f hf => ?_, hφH⟩
  have hm : β f ∈ V := (hS.mem_iff _).mpr ⟨f, hf, rfl⟩
  exact (hφV ⟨β f, hm⟩).trans (hψ _ f hf rfl)

theorem injective_of {φ : G →* AE.AEQ n}
    (hβ : ∀ f : Multiplicative (Fin n → ZMod 2), ∑ i, f.toAdd i = 0 →
      φ (β f) = AE.mkQ n (AE.Wr.ofVec f.toAdd))
    (hH : ∀ h : H, φ h = AE.mkQ n (AE.Wr.ofPerm (σ h))) : Function.Injective φ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨f, hf, x, rfl⟩ := hS.exists_eq_mul g
  rw [map_mul, hβ f hf, hH x] at hg
  have hx : x = 1 := hS.inj (by rw [RecogS.eq_one_of_mkQ_mul_eq_one hg, map_one])
  subst hx
  rw [map_one, AE.ofPerm_one, map_one, mul_one] at hg
  rw [OneMemClass.coe_one, mul_one]
  exact (hS.eq_one_iff f hf).mpr ((RecogS.mkQ_ofVec_eq_one_iff _).mp hg)

theorem range_eq_of {A : Subgroup (Equiv.Perm (Fin n))} (hσA : σ.range = A)
    (hA : ∀ s ∈ A, Equiv.Perm.sign s = 1) {φ : G →* AE.AEQ n}
    (hβ : ∀ f : Multiplicative (Fin n → ZMod 2), ∑ i, f.toAdd i = 0 →
      φ (β f) = AE.mkQ n (AE.Wr.ofVec f.toAdd))
    (hH : ∀ h : H, φ h = AE.mkQ n (AE.Wr.ofPerm (σ h))) : φ.range = AE.aeBarOver A := by
  have hmem : ∀ x : H, σ x ∈ A := fun x => hσA ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    obtain ⟨f, hf, x, rfl⟩ := hS.exists_eq_mul g
    rw [map_mul, hβ f hf, hH x]
    exact RecogS.mkQ_mul_mem_aeBarOver hf (hmem x) (hA _ (hmem x))
  · intro y hy
    obtain ⟨v, hv, s, hs, rfl⟩ := RecogS.exists_of_mem_aeBarOver hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (hσA ▸ hs : s ∈ σ.range)
    refine ⟨β (Multiplicative.ofAdd v) * x, ?_⟩
    rw [map_mul, hβ (Multiplicative.ofAdd v) hv, hH x, toAdd_ofAdd]

theorem exists_hom {A : Subgroup (Equiv.Perm (Fin n))} (hσA : σ.range = A)
    (hA : ∀ s ∈ A, Equiv.Perm.sign s = 1) :
    ∃ φ : G →* AE.AEQ n, Function.Injective φ ∧ φ.range = AE.aeBarOver A ∧
      (∀ f : Multiplicative (Fin n → ZMod 2), ∑ i, f.toAdd i = 0 →
        φ (β f) = AE.mkQ n (AE.Wr.ofVec f.toAdd)) ∧
      ∀ h : H, φ h = AE.mkQ n (AE.Wr.ofPerm (σ h)) := by
  obtain ⟨φ, hβ, hH⟩ := hS.exists_hom_apply
  exact ⟨φ, hS.injective_of hβ hH, hS.range_eq_of hσA hA hβ hH, hβ, hH⟩

theorem exists_hom_aeModel (hσA : σ.range = alternatingGroup (Fin n)) :
    ∃ φ : G →* AE.AEQ n, Function.Injective φ ∧ φ.range = TL4.aeModel n ∧
      (∀ f : Multiplicative (Fin n → ZMod 2), ∑ i, f.toAdd i = 0 →
        φ (β f) = AE.mkQ n (AE.Wr.ofVec f.toAdd)) ∧
      ∀ h : H, φ h = AE.mkQ n (AE.Wr.ofPerm (σ h)) := by
  rw [TL4.aeModel_eq]
  exact hS.exists_hom hσA TL4.alt_sign

end General

variable {V H : Subgroup G}

theorem exists_hom_e29Sub {σ : H →* Equiv.Perm (Fin 8)} {β : Multiplicative (Fin 8 → ZMod 2) →* G}
    (hS : AESplitHyp V H σ β) (hσA : σ.range = AE.agl32) :
    ∃ φ : G →* AE.AEQ 8, Function.Injective φ ∧ φ.range = AE.e29Sub ∧
      (∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
        φ (β f) = AE.mkQ 8 (AE.Wr.ofVec f.toAdd)) ∧
      ∀ h : H, φ h = AE.mkQ 8 (AE.Wr.ofPerm (σ h)) :=
  hS.exists_hom hσA TL4.agl32_sign

end AESplitHyp

end CFSG.ClassicalInvolution.Q3.Sec13
