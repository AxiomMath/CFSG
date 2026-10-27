module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ABGDGroups.LinearStructure
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldInv
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Base.ElemAut

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.GorensteinWalter

theorem card_le_two_mul_ker {H K : Type*} [Group H] [Group K] [Finite H] (φ : H →* K)
    (hφ : Nat.card φ.range ≤ 2) : Nat.card H ≤ 2 * Nat.card φ.ker := by
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [← h1]
  calc Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * 2 := Nat.mul_le_mul_left _ hφ
    _ = 2 * Nat.card φ.ker := mul_comm _ _

theorem card_le_two_mul_inf_pslRange {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    {E : Subgroup (PGammaL2 F)} (hE2 : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 * Nat.card ↥(E ⊓ pGammaL2PSLRange F) := by
  classical
  have hodd := AutL2Facts.isOddPrimePower_of hp hp2 hf hF
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hE2 _ (mul_mem ha hb))).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
        rw [inv_eq_of_mul_eq_one_right (hE2 b hb), inv_eq_of_mul_eq_one_right (hE2 a ha)]
  have hinl : ∀ a : PGammaL2 F, a.right = 1 → a = SemidirectProduct.inl a.left := fun a ha => by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right a]
    rw [ha, map_one, mul_one]
  by_cases hright : ∃ b ∈ E, b.right ≠ 1
  · obtain ⟨b, hb, hbr⟩ := hright
    set π : PGammaL2 F →* (F ≃+* F) := SemidirectProduct.rightHom with hπ
    set φ : ↥E →* (F ≃+* F) := π.comp E.subtype with hφ
    have hrange : Nat.card φ.range ≤ 2 := by
      have : IsCyclic (F ≃+* F) := AutL2Facts.isCyclic_ringAut F
      have hexp : Monoid.exponent φ.range ∣ 2 := by
        refine Monoid.exponent_dvd_of_forall_pow_eq_one fun σ => ?_
        obtain ⟨x, hxσ⟩ := σ.2
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, ← hxσ, ← map_pow, sq,
          show x * x = 1 from Subtype.ext (hE2 _ x.2), map_one, OneMemClass.coe_one]
      rw [← IsCyclic.exponent_eq_card]
      exact Nat.le_of_dvd two_pos hexp
    refine (card_le_two_mul_ker φ hrange).trans (Nat.mul_le_mul_left 2 ?_)
    refine Nat.card_le_card_of_injective
      (fun x : φ.ker => (⟨((x : E) : PGammaL2 F), mem_inf.mpr ⟨(x : E).2, ?_⟩⟩ :
        ↥(E ⊓ pGammaL2PSLRange F))) ?_
    · have hxr : ((x : E) : PGammaL2 F).right = 1 := by
        have h3 : π ((x : E) : PGammaL2 F) = 1 := MonoidHom.mem_ker.mp x.2
        rwa [hπ, SemidirectProduct.rightHom_eq_right] at h3
      have hxe := hinl _ hxr
      have hmem := AutL2Facts.mem_pslRange_of_commute_fieldInv hp hp2 hF b (hE2 b hb) hbr
        ((x : E) : PGammaL2 F).left (by rw [← hxe]; exact hcomm b hb _ (x : E).2)
      rw [← hxe] at hmem
      exact hmem
    · intro x y hxy
      have h1 := congrArg (fun u : ↥(E ⊓ pGammaL2PSLRange F) => (u : PGammaL2 F)) hxy
      exact Subtype.ext (Subtype.ext h1)
  · push Not at hright
    set d := ABGDGroups.pGammaL2DetClass F hodd with hd
    set φ : ↥E →* _ := d.comp E.subtype with hφ
    have hrange : Nat.card φ.range ≤ 2 := by
      obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ↥E, ∀ y : ↥E, φ y = 1 ∨ φ y = φ a₀ := by
        by_cases hall : ∀ y : ↥E, φ y = 1
        · exact ⟨1, fun y => Or.inl (hall y)⟩
        · push Not at hall
          obtain ⟨a₀, ha₀⟩ := hall
          exact ⟨a₀, fun y => by
            by_cases hy : φ y = 1
            · exact Or.inl hy
            · exact Or.inr (ABGDGroups.squareClass_eq_of_ne_one hodd hy ha₀)⟩
      have hsub : ∀ c ∈ φ.range, c ∈ ({1, φ a₀} : Finset _) := by
        rintro c ⟨y, rfl⟩
        rcases ha₀ y with h1 | h1 <;> rw [h1]
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact (SmallLocal.card_le_of_forall_mem_finset _ hsub).trans Finset.card_le_two
    refine (card_le_two_mul_ker φ hrange).trans (Nat.mul_le_mul_left 2 ?_)
    refine Nat.card_le_card_of_injective
      (fun x : φ.ker => (⟨((x : E) : PGammaL2 F), mem_inf.mpr ⟨(x : E).2, ?_⟩⟩ :
        ↥(E ⊓ pGammaL2PSLRange F))) ?_
    · rw [ABGDGroups.pGammaL2PSLRange_eq_inf_ker hodd, mem_inf, MonoidHom.mem_ker]
      refine ⟨?_, (MonoidHom.mem_ker.mp x.2 : d ((x : E) : PGammaL2 F) = 1)⟩
      rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
        SemidirectProduct.rightHom_eq_right, hright _ (x : E).2]
    · intro x y hxy
      have h1 := congrArg (fun u : ↥(E ⊓ pGammaL2PSLRange F) => (u : PGammaL2 F)) hxy
      exact Subtype.ext (Subtype.ext h1)

theorem card_le_two_mul_inf_innAut_alt7 {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
    (e : 𝕊 ≃* alternatingGroup (Fin 7)) (E : Subgroup (MulAut 𝕊)) :
    Nat.card E ≤ 2 * Nat.card ↥(E ⊓ innAut5 𝕊) := by
  classical
  set c : Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 7)) with hc
  have hcb : Function.Bijective c :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)
  set θ : Equiv.Perm (Fin 7) →* MulAut 𝕊 := (MulAut.congr e.symm).toMonoidHom.comp c with hθ
  have hθb : Function.Bijective θ := (MulAut.congr e.symm).bijective.comp hcb
  set θe := MulEquiv.ofBijective θ hθb with hθe
  have heven : ∀ σ : Equiv.Perm (Fin 7), Equiv.Perm.sign σ = 1 → θ σ ∈ innAut5 𝕊 := by
    intro σ hσ
    have hσA : σ ∈ alternatingGroup (Fin 7) := Equiv.Perm.mem_alternatingGroup.mpr hσ
    have hθσ : θ σ = MulAut.conj (e.symm ⟨σ, hσA⟩) := by
      ext y
      rw [hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
        MulAut.conj_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_symm]
      apply e.injective
      rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [hc, MulAut.conjNormal_apply]
      simp
    rw [hθσ]
    exact ⟨_, rfl⟩
  set φ : ↥E →* ℤˣ := Equiv.Perm.sign.comp (θe.symm.toMonoidHom.comp E.subtype) with hφ
  have hrange : Nat.card φ.range ≤ 2 := by
    have h1 : Nat.card φ.range ≤ Nat.card ℤˣ := card_le_of_le le_top |>.trans
      (by rw [card_top])
    have h2 : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
    omega
  refine (card_le_two_mul_ker φ hrange).trans (Nat.mul_le_mul_left 2 ?_)
  refine Nat.card_le_card_of_injective
    (fun x : φ.ker => (⟨((x : E) : MulAut 𝕊), mem_inf.mpr ⟨(x : E).2, ?_⟩⟩ :
      ↥(E ⊓ innAut5 𝕊))) ?_
  · have h1 : Equiv.Perm.sign (θe.symm ((x : E) : MulAut 𝕊)) = 1 := MonoidHom.mem_ker.mp x.2
    have h2 := heven _ h1
    rwa [show θ (θe.symm ((x : E) : MulAut 𝕊)) = ((x : E) : MulAut 𝕊) from
      θe.apply_symm_apply _] at h2
  · intro x y hxy
    have h1 := congrArg (fun u : ↥(E ⊓ innAut5 𝕊) => (u : MulAut 𝕊)) hxy
    exact Subtype.ext (Subtype.ext h1)

theorem card_le_two_mul_inf_innAut {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (h𝕊 : FooteSimpleType 𝕊)
    {E : Subgroup (MulAut 𝕊)} (hE2 : ∀ α ∈ E, α * α = 1) :
    Nat.card E ≤ 2 * Nat.card ↥(E ⊓ innAut5 𝕊) := by
  rcases h𝕊 with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  · exact card_le_two_mul_inf_innAut_alt7 e E
  · obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hL
    set ψ := AutL2Facts.autEquiv e with hψ
    have h1 := card_le_two_mul_inf_pslRange hp hp2 hf hF (E := E.map ψ.toMonoidHom) (by
      rintro _ ⟨α, hα, rfl⟩
      rw [← map_mul, hE2 α hα, map_one])
    rw [card_map_of_injective (f := ψ.toMonoidHom) ψ.injective,
      ← AutL2Facts.map_autEquiv_innAut e, ← hψ, ← map_inf_eq _ _ ψ.toMonoidHom ψ.injective,
      card_map_of_injective (f := ψ.toMonoidHom) ψ.injective] at h1
    exact h1

end CFSG.ComponentClassification.Foote5
