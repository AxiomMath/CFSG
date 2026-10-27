module

public import CFSG.LargeExtraspecial.AS35KFisD
public import CFSG.LargeExtraspecial.AS35KFixC
public import CFSG.LargeExtraspecial.AS35LAut
public import CFSG.LargeExtraspecial.AS35KFisC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification

namespace Setting

variable {H : Type} [Group H] [Finite H] (T : Setting H)

theorem false_of_case5_big (hs : IsSimpleGroup T.zGen) (hC : centralizer (T.zGen : Set H) = ⊥)
    {m : ℕ} (hm : 6 ≤ m) {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hsymm : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmodel : fischerCentralQuotientModel {g : T.zGen | IsConj T.zL g}
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) : False := by
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, hψ⟩ := (fischerCentralQuotientModel_iff _).1 hmodel
  have hLn := T.zGen_normal
  obtain ⟨v, hv, hvd⟩ := mem_D3_iff.1 ((hψ T.zL).1 (IsConj.refl _))
  have hd : reflBar f v ∈ D3 f := mem_D3_iff.2 ⟨v, hv, rfl⟩
  have hP := pair_R3 hf (by omega : 4 ≤ m)
  have hZ := center_R3_eq_bot hf (by omega : 4 ≤ m)
  have hna := T.exists_mul_ne_mul_zGen hC
  have hsX : IsSimpleGroup (R3 f) := ψ.symm.isSimpleGroup
  have hnaX : ∃ a b : R3 f, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨ψ a, ψ b, fun h => hab (ψ.injective (by rw [map_mul, map_mul, h]))⟩
  have hcommX := AS35K.commutator_eq_top_of_simple hnaX
  have hS : IsSimpleGroup (_root_.commutator (R3 f)) :=
    ((MulEquiv.subgroupCongr hcommX).trans topEquiv).isSimpleGroup
  have hna' : ∃ a b : _root_.commutator (R3 f), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnaX
    refine ⟨⟨a, hcommX ▸ mem_top _⟩, ⟨b, hcommX ▸ mem_top _⟩, fun h => hab ?_⟩
    have h' := congrArg Subtype.val h
    simpa only [Subgroup.coe_mul] using h'
  have hT := tripleProperty_D3 hf (by omega : 5 ≤ m)
  have hL : ¬ HasNormalPSubgroup 2 (LocalQuotient (D3 f) (reflBar f v)) := by
    rintro ⟨N, hNn, hN1, hN2⟩
    obtain ⟨f', hf', -, Φ, -⟩ := exists_localQuotient_equiv hf (by omega) hv
    refine AS35R3.not_tripleProperty_of_hasNormalPSubgroup (pair_R3 hf' (by omega))
      (center_R3_eq_bot hf' (by omega))
      ⟨N.map Φ.toMonoidHom, hNn.map _ Φ.surjective, fun h => hN1 ?_, hN2.map _⟩
      (tripleProperty_D3 hf' (by omega))
    rwa [Subgroup.map_eq_bot_iff_of_injective _ Φ.injective] at h
  have hA : ∀ ℓ : T.zGen, (ℓ : H) ∈ T.QG → ℓ = 1 ∨ ℓ = T.zL := by
    intro ℓ hℓ
    set P : Subgroup (R3 f) := (T.QG.comap T.zGen.subtype).map ψ.toMonoidHom with hPdef
    have hPC : P ≤ centralizer {reflBar f v} := by
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_singleton_iff, hvd, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (T.z_comm_QG hy)
    have hPn : ∀ c ∈ centralizer {reflBar f v}, ∀ x ∈ P, c * x * c⁻¹ ∈ P := by
      intro c hc x hx
      obtain ⟨c', rfl⟩ := ψ.surjective c
      obtain ⟨y, hy, rfl⟩ := hx
      rw [mem_centralizer_singleton_iff, hvd, ← map_mul, ← map_mul] at hc
      have hc' : ((c' : T.zGen) : H) ∈ T.M := by
        rw [T.mem_M_iff]
        exact congrArg Subtype.val (ψ.injective hc)
      refine ⟨c' * y * c'⁻¹, ?_, by simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]⟩
      change ((c' * y * c'⁻¹ : T.zGen) : H) ∈ T.QG
      rw [coe_mul, coe_mul, coe_inv]
      exact T.conj_mem_QG hc' hy
    have hP2 : IsPGroup 2 P := by
      have hQ2 : IsPGroup 2 T.QG := fun g => ⟨2, Subtype.ext (by simpa using T.pow_four_eq_one g.2)⟩
      exact (hQ2.comap_of_injective T.zGen.subtype T.zGen.subtype_injective).map _
    rcases AS35R3.eq_one_or_eq_of_mem hP hZ hS hna' hT hd hL hPC hPn hP2 (y := ψ ℓ)
        ⟨ℓ, hℓ, rfl⟩ with h | h
    · exact Or.inl (ψ.injective (h.trans (map_one ψ).symm))
    · exact Or.inr (ψ.injective (h.trans hvd))
  have hB : ∀ q ∈ T.QG, q = 1 ∨ q = T.z := by
    intro q hq
    set β : MulAut (R3 f) := ψ.symm.trans ((MulAut.conjNormal q).trans ψ) with hβdef
    have hβ : ∀ ℓ, β (ψ ℓ) = ψ (MulAut.conjNormal q ℓ) := fun ℓ => by
      rw [hβdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
    have hfixz : MulAut.conjNormal q T.zL = T.zL := Subtype.ext (by
      rw [MulAut.conjNormal_apply, coe_zL, T.z_comm_QG hq, mul_inv_cancel_right])
    have hβd : β (reflBar f v) = reflBar f v := by rw [hvd, hβ, hfixz]
    have hβE : ∀ e ∈ D3 f, β e ∈ D3 f := by
      intro e he
      obtain ⟨ℓ, rfl⟩ := ψ.surjective e
      rw [hβ]
      obtain ⟨c, rfl⟩ := isConj_iff.mp ((hψ ℓ).2 he)
      refine (hψ _).1 (isConj_iff.mpr ⟨MulAut.conjNormal q c, ?_⟩)
      rw [map_mul, map_mul, map_inv, hfixz]
    have hβD : ∀ g ∈ LocalClass (D3 f) (reflBar f v), β g = g := by
      intro g hg
      obtain ⟨ℓ, rfl⟩ := ψ.surjective g
      have hℓz : ℓ * T.zL = T.zL * ℓ := by
        have h1 := hg.2.2
        rw [hvd, ← map_mul, ← map_mul] at h1
        exact ψ.injective h1
      have hℓM : ((ℓ : T.zGen) : H) ∈ T.M := by
        rw [T.mem_M_iff]
        exact congrArg Subtype.val hℓz
      have hmemQ : ((ℓ⁻¹ * MulAut.conjNormal q ℓ : T.zGen) : H) ∈ T.QG := by
        rw [coe_mul, MulAut.conjNormal_apply, coe_inv,
          show ((ℓ : H))⁻¹ * (q * ℓ * q⁻¹) = ((ℓ : H)⁻¹ * q * ((ℓ : H))⁻¹⁻¹) * q⁻¹ by group]
        exact mul_mem (T.conj_mem_QG (inv_mem hℓM) hq) (inv_mem hq)
      rcases hA _ hmemQ with h1 | h1
      · rw [hβ, ← inv_mul_eq_one.mp h1]
      · exfalso
        have hq' : MulAut.conjNormal q ℓ = ℓ * T.zL := by
          rw [← h1, mul_inv_cancel_left]
        have hβg : β (ψ ℓ) = ψ ℓ * reflBar f v := by rw [hβ, hq', map_mul, hvd]
        have hg' : ψ ℓ * reflBar f v ∈ LocalClass (D3 f) (reflBar f v) := by
          rw [← hβg]
          refine ⟨hβE _ hg.1, fun h => hg.2.1 ?_, ?_⟩
          · apply β.injective
            rw [h, hβd]
          · have h2 := congrArg β hg.2.2
            rwa [map_mul, map_mul, hβd] at h2
        have hcen : (⟨ψ ℓ, mem_localGroup hg⟩ : LocalGroup (D3 f) (reflBar f v))⁻¹ *
            ⟨ψ ℓ * reflBar f v, mem_localGroup hg'⟩ ∈ center (LocalGroup (D3 f) (reflBar f v)) := by
          rw [mem_center_iff]
          intro l
          apply Subtype.ext
          simp only [coe_mul, coe_inv, inv_mul_cancel_left]
          exact commute_of_mem_localGroup' l.2
        have heq : starImage (D3 f) (reflBar f v) ⟨ψ ℓ, hg⟩ =
            starImage (D3 f) (reflBar f v) ⟨ψ ℓ * reflBar f v, hg'⟩ := by
          rw [starImage, starImage, QuotientGroup.eq]
          exact hcen
        have h2 := congrArg Subtype.val (Pair.starImage_injective_of_simple hP hZ hS hd heq)
        have h3 : reflBar f v = 1 := by
          have h4 : ψ ℓ * reflBar f v = ψ ℓ * 1 := by rw [mul_one]; exact h2.symm
          exact mul_left_cancel h4
        exact Pair.ne_one hP hd h3
    refine T.eq_one_or_z_of_conjNormal hC (AS35K.eq_or_eq_conj_of_transport ψ _ ?_)
    rw [← hvd]
    exact AS35L.mulAut_eq_one_or_conj_of_fix hP hZ hS hna' hT hd β hβE hβd hβD
  obtain ⟨x, hx, y, hy, hxy⟩ := T.exists_mem_QG_mul_ne
  rcases hB x hx with rfl | rfl <;> rcases hB y hy with rfl | rfl <;> simp at hxy

end Setting

namespace S14

theorem aschTwoReflSixStmt : AschTwoReflSixStmt := by
  intro H _ _ T _ hs hC _ m hm f hsymm hnd hmodel
  exact T.false_of_case5_big hs hC hm hsymm hnd hmodel

theorem aschTwoAutStmt :
    AschTwoAutStmt :=
  aschTwoAutStmt_of_unitaryModel
    (aschTwoUnitaryModelStmt_of_spRefl (aschTwoSpReflStmt_of_reflSix aschTwoReflSixStmt))

end S14

end CFSG.LargeExtraspecial
