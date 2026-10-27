module

public import CFSG.CGT.T75P.IdentGen
public import CFSG.CGT.T75P.PermCent
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.CGT.T75P

open Equiv Equiv.Perm

section AutCenter

variable {Y : Type*} [Group Y]

theorem map_center_eq_aux (α : MulAut Y) :
    (Subgroup.center Y).map α.toMonoidHom = Subgroup.center Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.1 hx (α.symm g)
    apply α.symm.injective
    simpa using h1
  · intro hy
    refine ⟨α.symm y, Subgroup.mem_center_iff.2 fun g => ?_, by simp⟩
    apply α.injective
    simpa using (Subgroup.mem_center_iff.1 hy (α g))

theorem mulAut_eq_one_of_forall_mem_center (hY : commutator Y = ⊤) (α : MulAut Y)
    (h : ∀ x : Y, x⁻¹ * α x ∈ Subgroup.center Y) : α = 1 := by
  let c : Y →* Subgroup.center Y :=
    { toFun := fun x => ⟨x⁻¹ * α x, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        have hz := Subgroup.mem_center_iff.1 (h x) y⁻¹
        calc (x * y)⁻¹ * α (x * y) = y⁻¹ * (x⁻¹ * α x) * α y := by
              rw [map_mul, mul_inv_rev]; group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [hz]
          _ = (x⁻¹ * α x) * (y⁻¹ * α y) := by group }
  have hker : commutator Y ≤ c.ker := Abelianization.commutator_subset_ker c
  rw [hY] at hker
  ext x
  have hx : c x = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top x))
  have h1 : x⁻¹ * α x = 1 := congrArg Subtype.val hx
  have h2 : α x = x := by
    calc α x = x * (x⁻¹ * α x) := by group
      _ = x := by rw [h1, mul_one]
  simpa using h2

end AutCenter

section Nine

variable {Y : Type*} [Group Y]

theorem mulAut_eq_one_of_fixes_nine (hY : commutator Y = ⊤)
    (θ : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 9)) (α : MulAut Y) (T' H' : Subgroup Y)
    (hTH : T' ≤ H') (hcard : Nat.card T' = 8) (hab : ∀ a ∈ T', ∀ b ∈ T', a * b = b * a)
    (hTZ : T' ⊓ Subgroup.center Y = ⊥)
    (htrans : ∀ a ∈ T', a ≠ 1 → ∀ b ∈ T', b ≠ 1 → ∃ h ∈ H', h * a * h⁻¹ = b)
    (hfix : ∀ h ∈ H', α h = h) : α = 1 := by
  classical
  let q : Y →* alternatingGroup (Fin 9) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  let r : Y →* Perm (Fin 9) := (alternatingGroup (Fin 9)).subtype.comp q
  have hqker : ∀ y : Y, q y = 1 → y ∈ Subgroup.center Y := by
    intro y hy
    have h1 : θ (QuotientGroup.mk y) = 1 := hy
    have h2 : (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = 1 :=
      θ.injective (h1.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff y).1 h2
  have hrker : ∀ y : Y, r y = 1 → y ∈ Subgroup.center Y := fun y hy => hqker y (Subtype.ext hy)
  let ψ : Y ⧸ Subgroup.center Y ≃* Y ⧸ Subgroup.center Y :=
    QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) α (map_center_eq_aux α)
  let σ : MulAut (alternatingGroup (Fin 9)) := (θ.symm.trans ψ).trans θ
  have hσ : ∀ y : Y, σ (q y) = θ (QuotientGroup.mk (α y)) := by
    intro y
    show θ (ψ (θ.symm (θ (QuotientGroup.mk y)))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨π, hπσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
    (by norm_num) (by norm_num)).2 σ
  have hπfix : ∀ y : Y, α y = y → π * r y = r y * π := by
    intro y hy
    have h1 : σ (q y) = q y := by rw [hσ, hy]; rfl
    have h2 : (MulAut.conjNormal π : MulAut (alternatingGroup (Fin 9))) (q y) = q y := by
      rw [hπσ]; exact h1
    have h3 := congrArg Subtype.val h2
    rw [MulAut.conjNormal_apply] at h3
    exact mul_inv_eq_iff_eq_mul.1 h3
  have hTr : T'.map r ≤ H'.map r := Subgroup.map_mono hTH
  have hπ1 : π = 1 := by
    refine perm_centralizer_trivial (H'.map r) (T'.map r) hTr ?_ ?_ ?_ ?_
    · rw [card_map_of_inf_ker_eq_bot r T' (by
        rw [eq_bot_iff]
        intro y hy
        have h1 : y ∈ T' ⊓ Subgroup.center Y := ⟨hy.1, hrker y hy.2⟩
        rw [hTZ] at h1
        exact h1)]
      exact hcard
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hab a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩ ha1 _ ⟨b, hb, rfl⟩ hb1
      have ha1' : a ≠ 1 := fun h => ha1 (by rw [h, map_one])
      have hb1' : b ≠ 1 := fun h => hb1 (by rw [h, map_one])
      obtain ⟨h, hh, hhab⟩ := htrans a ha ha1' b hb hb1'
      exact ⟨r h, ⟨h, hh, rfl⟩, by rw [← map_mul, ← map_inv, ← map_mul, hhab]⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hπfix y (hfix y hy)
  have hσ1 : ∀ a : alternatingGroup (Fin 9), σ a = a := by
    intro a
    have : (MulAut.conjNormal π : MulAut (alternatingGroup (Fin 9))) a = a := by
      rw [hπ1, map_one]
      rfl
    rw [← hπσ]
    exact this
  apply mulAut_eq_one_of_forall_mem_center hY
  intro x
  have h1 : θ (QuotientGroup.mk (α x)) = θ (QuotientGroup.mk x) := by
    rw [← hσ]
    exact hσ1 (q x)
  have h2 := θ.injective h1
  exact QuotientGroup.eq.1 h2.symm

end Nine

end CFSG.CGT.T75P
