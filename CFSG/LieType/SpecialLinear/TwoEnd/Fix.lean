module

public import CFSG.LieType.SpecialLinear.TwoEnd.Generation
public import CFSG.LieType.SpecialLinear.EndNode.Smith

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis

noncomputable section

section Generic

variable {k G G' V : Type*} [Field k] [Group G] [Group G'] [AddCommGroup V] [Module k V]

theorem fixSub_sup_eq (ρ : Representation k G V) (S T : Subgroup G) :
    fixSub ρ (S ⊔ T) = fixSub ρ S ⊓ fixSub ρ T := by
  refine le_antisymm (le_inf (fixSub_anti ρ le_sup_left) (fixSub_anti ρ le_sup_right)) ?_
  intro v hv
  exact mem_fixSub_sup ρ hv.1 hv.2

theorem fixSub_map (ρ : Representation k G V) (f : G' →* G) (N : Subgroup G') :
    fixSub ρ (N.map f) = fixSub (ρ.comp f) N := by
  ext v
  rw [mem_fixSub, mem_fixSub]
  constructor
  · intro h n hn
    exact h (f n) (Subgroup.mem_map_of_mem f hn)
  · rintro h _ ⟨n, hn, rfl⟩
    exact h n hn

theorem map_subtype_fixSub_restrictRep (ρ : Representation k G V) (W : Submodule k V)
    (hW : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W) (N : Subgroup G) :
    (fixSub (restrictRep ρ W hW) N).map W.subtype = W ⊓ fixSub ρ N := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.2, ?_⟩
    change ∀ g ∈ N, ρ g (W.subtype u) = W.subtype u
    intro g hg
    exact congrArg Subtype.val (hu g hg)
  · rintro ⟨hvW, hvN⟩
    refine ⟨⟨v, hvW⟩, ?_, rfl⟩
    change ∀ g ∈ N, (restrictRep ρ W hW) g ⟨v, hvW⟩ = ⟨v, hvW⟩
    intro g hg
    apply Subtype.ext
    exact hvN g hg

@[expose] def submoduleEquivOfEq {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {p q : Submodule k V} (h : p = q) : p ≃ₗ[k] q where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun y := ⟨y.1, h.symm ▸ y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' x y := by ext; rfl
  map_smul' c x := by ext; rfl

@[simp] theorem submoduleEquivOfEq_apply {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {p q : Submodule k V} (h : p = q) (x : p) :
    ((submoduleEquivOfEq h x : q) : V) = x.1 := by rfl

end Generic

variable (m : ℕ) (F : Type) [Field F]

@[expose] def twoEndFix {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (m+3)) F) V) : Submodule k V :=
  fixSub ρ (twoEndRadical m F)

theorem embedMid_conj_mem_twoEndRadical {h : SpecialLinearGroup (Fin (m+1)) F}
    {s : SpecialLinearGroup (Fin (m+3)) F} (hs : s ∈ twoEndRadical m F) :
    embedMid m F h * s * (embedMid m F h)⁻¹ ∈ twoEndRadical m F := by
  have hmid : embedMid m F h = embedSucc (m+1) F (embedCastSucc m F h) := rfl
  have hH : (firstRowRadical (m+1) F).map (MulAut.conj (embedMid m F h)).toMonoidHom ≤
      firstRowRadical (m+1) F := by
    rintro x ⟨y, hy, rfl⟩
    exact embedSucc_range_normalizes_firstRow (m := m+1) (F := F) (embedMid m F h)
      ⟨embedCastSucc m F h, hmid.symm⟩ y hy
  have hL : ((lastColRadical m F).map (embedSucc (m+1) F)).map
      (MulAut.conj (embedMid m F h)).toMonoidHom ≤
      (lastColRadical m F).map (embedSucc (m+1) F) := by
    rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    change embedMid m F h * embedSucc (m+1) F z * (embedMid m F h)⁻¹ ∈
      (lastColRadical m F).map (embedSucc (m+1) F)
    have heq : embedMid m F h * embedSucc (m+1) F z * (embedMid m F h)⁻¹ =
        embedSucc (m+1) F (embedCastSucc m F h * z * (embedCastSucc m F h)⁻¹) := by
      rw [hmid]
      simp only [map_mul, map_inv]
    rw [heq]
    exact Subgroup.mem_map_of_mem (embedSucc (m+1) F)
      (embedCastSucc_conj_mem_lastCol m F h hz)
  have hconj : (twoEndRadical m F).map (MulAut.conj (embedMid m F h)).toMonoidHom ≤
      twoEndRadical m F := by
    conv_lhs => rw [twoEndRadical_eq_first_sup]
    rw [Subgroup.map_sup]
    exact sup_le (hH.trans (firstRowRadical_le_twoEndRadical m F))
      (hL.trans (lastColRadical_map_embedSucc_le_twoEndRadical m F))
  exact hconj (Subgroup.mem_map_of_mem (MulAut.conj (embedMid m F h)).toMonoidHom hs)

theorem twoEndFix_stable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (m+3)) F) V) :
    ∀ g' ∈ (embedMid m F).range, ∀ w ∈ twoEndFix m F ρ, ρ g' w ∈ twoEndFix m F ρ := by
  rintro g' ⟨h, rfl⟩ w hw
  rw [twoEndFix, mem_fixSub] at hw ⊢
  intro s hs
  have hnorm : (embedMid m F h)⁻¹ * s * embedMid m F h ∈ twoEndRadical m F := by
    have h := embedMid_conj_mem_twoEndRadical (m := m) (F := F) (h := h⁻¹) hs
    simpa using h
  calc ρ s (ρ (embedMid m F h) w)
      = ρ (s * embedMid m F h) w := by rw [map_mul, Module.End.mul_apply]
    _ = ρ (embedMid m F h * ((embedMid m F h)⁻¹ * s * embedMid m F h)) w := by group
    _ = ρ (embedMid m F h) (ρ ((embedMid m F h)⁻¹ * s * embedMid m F h) w) := by
        rw [map_mul, Module.End.mul_apply]
    _ = ρ (embedMid m F h) w := by rw [hw _ hnorm]

@[expose] noncomputable def twoEndRestrict {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (SpecialLinearGroup (Fin (m+3)) F) V) :
    Representation k (SpecialLinearGroup (Fin (m+1)) F) (twoEndFix m F ρ) :=
  restrictRep (ρ.comp (embedMid m F)) (twoEndFix m F ρ)
    (fun g w hw => twoEndFix_stable m F ρ (embedMid m F g) ⟨g, rfl⟩ w hw)

theorem twoEndFix_eq_firstLast {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (m+3)) F) V) :
    twoEndFix m F ρ =
      (lastColFix m F (firstNodeRestrict (m+1) F ρ)).map
        (firstRowFix (m+1) F ρ).subtype := by
  rw [twoEndFix, twoEndRadical_eq_first_sup, fixSub_sup_eq]
  rw [fixSub_map ρ (embedSucc (m+1) F) (lastColRadical m F)]
  rw [show lastColFix m F (firstNodeRestrict (m+1) F ρ) =
      fixSub (restrictRep (ρ.comp (embedSucc (m+1) F)) (firstRowFix (m+1) F ρ)
        (firstRowFix_stable_embedSucc (m+1) F ρ)) (lastColRadical m F) from rfl]
  rw [map_subtype_fixSub_restrictRep (ρ.comp (embedSucc (m+1) F)) (firstRowFix (m+1) F ρ)
    (firstRowFix_stable_embedSucc (m+1) F ρ) (lastColRadical m F)]
  rfl

@[expose] noncomputable def twoEndEquivFirstLast {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (SpecialLinearGroup (Fin (m+3)) F) V) :
    (lastColFix m F (firstNodeRestrict (m+1) F ρ)) ≃ₗ[k] twoEndFix m F ρ :=
  (Submodule.equivMapOfInjective (firstRowFix (m+1) F ρ).subtype
      (fun _ _ h => Subtype.ext h) (lastColFix m F (firstNodeRestrict (m+1) F ρ))).trans
    (submoduleEquivOfEq (twoEndFix_eq_firstLast m F ρ).symm)

theorem twoEndEquivFirstLast_intertwine {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (SpecialLinearGroup (Fin (m+3)) F) V)
    (g : SpecialLinearGroup (Fin (m+1)) F)
    (x : lastColFix m F (firstNodeRestrict (m+1) F ρ)) :
    twoEndEquivFirstLast m F ρ
        (lastNodeRestrict m F (firstNodeRestrict (m+1) F ρ) g x) =
      twoEndRestrict m F ρ g (twoEndEquivFirstLast m F ρ x) := by
  apply Subtype.ext
  change ρ (embedMid m F g) x.1.1 = ρ (embedMid m F g) x.1.1
  rfl

end

end CFSG.LieType.SpecialLinear
