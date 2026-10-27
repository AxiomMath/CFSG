module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXInv
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QFAt
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofAdjointRoots
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeafProof

theorem famF_of_toralReps
    {t : StatedLieTag} {τ : Tag}
    (ht : t ∈ chevalleyExceptionalTags) (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (hmodel : ∀ (J : Type) [Group J] (p f : ℕ), ChevalleyExceptionalModel J t p f →
      UntwistedChevalleyModel J τ (p ^ f))
    {reps : List (List Bool)} {entries : List (List Bool × ℕ × List ℕ)}
    (hcert : OrbitCheck τ reps entries)
    (hreps : ∀ (K : Type) [Field K], ringChar K ≠ 2 → ∀ ρ < reps.length,
      listMask (τ := τ) (reps.getD ρ []) ≠ (fun _ => false) →
      ∃ (bb : Fin τ.rank → Bool) (i : Fin τ.rank), (∀ j, j ≠ i → bb j = false) ∧
        Nonempty (toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ []))) ≃*
          toralCentralizer τ K (bitsTuple bb))) :
    FamF t := by
  refine famF_of_fAt fun X _ _ _ n p f hp hp2 hX hq z hz => ?_
  obtain ⟨K, _, _, hK, ⟨E⟩⟩ := nonempty_mulEquiv_adjointGroup τ
    (hmodel X p f (GH74.chevalleyExceptionalModel_of_lieModel ht hX))
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hf : f ≠ 0 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := K)
    rw [hK, pow_zero] at h1
    exact lt_irrefl _ h1
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have : CharP K p := finite_field_prime_power_characteristic hp (Nat.one_le_iff_ne_zero.2 hf) hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hK5 : 5 ≤ Nat.card K := by
    have h3 : 3 ≤ Nat.card K := by
      rw [hK]
      exact hp3.trans (Nat.le_self_pow hf p)
    have h3' : Nat.card K ≠ 3 := by
      rw [hK]
      exact hq
    obtain ⟨k, hk⟩ := hKodd
    omega
  set z' : adjointGroup τ K := E z with hz'def
  have hz' : orderOf z' = 2 := (orderOf_injective E.toMonoidHom E.injective z).trans hz
  set α : MulAut (adjointGroup τ K) := MulAut.conj z' with hαdef
  have hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (z' : ModGL τ K) * rootDiagUnit τ (1 : Fin τ.rank → Kˣ) * (h : ModGL τ K) *
        (rootDiagUnit τ (1 : Fin τ.rank → Kˣ))⁻¹ * (z' : ModGL τ K)⁻¹ := by
    intro h
    rw [rootDiagUnit_one, mul_one, inv_one, mul_one]
    rfl
  have hα : α ^ 2 = 1 := by
    rw [hαdef, ← map_pow, ← hz', pow_orderOf_eq_one, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have hzc : z' ∈ center (adjointGroup τ K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := congrArg (fun φ : MulAut (adjointGroup τ K) => φ y) h1
      simp only [hαdef, MulAut.one_apply, MulAut.conj_apply] at h2
      calc y * z' = z' * y * z'⁻¹ * z' := by rw [h2]
        _ = z' * y := by group
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hzc
    rw [hzc, orderOf_one] at hz'
    exact absurd hz' (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ₁⟩⟩ := exists_toralCentralizer_equiv_of_innerDiag hτ hKodd hαg hα
  obtain ⟨ρ, hρ, w, hw, hmap⟩ := exists_conj_toralCentralizer_of_orbitCheck hK2 hcert hb
  have hne : listMask (τ := τ) (reps.getD ρ []) ≠ fun _ => false := by
    intro h0
    refine hb1 hα1 (eq_one_of_rootChar_smul_eq_one (w := w) fun v => ?_)
    rw [hw v]
    congr 1
    funext i
    change (if listMask (τ := τ) (reps.getD ρ []) i then (-1 : Kˣ) else 1) = 1
    rw [h0]
    rfl
  obtain ⟨bb, i, hbb, ⟨Θ₃⟩⟩ := hreps K hK2 ρ hρ hne
  have hfix : (centralizer ({z} : Set X)).map E.toMonoidHom =
      FixedCommutingProduct.fixedSubgroup α := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hx
      change z' * E x * z'⁻¹ = E x
      rw [hz'def, ← map_inv, ← map_mul, ← map_mul, ← hx', mul_inv_cancel_right]
    · intro hy
      have hy' : z' * y * z'⁻¹ = y := hy
      refine ⟨E.symm y, Subgroup.mem_centralizer_singleton_iff.2 (E.injective ?_),
        E.apply_symm_apply y⟩
      rw [map_mul, map_mul, E.apply_symm_apply, ← hz'def]
      calc y * z' = z' * y * z'⁻¹ * z' := by rw [hy']
        _ = z' * y := by group
  let Θ₀ : centralizer ({z} : Set X) ≃* FixedCommutingProduct.fixedSubgroup α :=
    ((centralizer ({z} : Set X)).equivMapOfInjective E.toMonoidHom E.injective).trans
      (MulEquiv.subgroupCongr hfix)
  let Θ₂ : toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ []))) ≃*
      toralCentralizer τ K b :=
    ((toralCentralizer τ K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
      (MulEquiv.subgroupCongr hmap)
  let Θ : centralizer ({z} : Set X) ≃* toralCentralizer τ K (bitsTuple bb) :=
    Θ₀.trans (Θ₁.trans (Θ₂.symm.trans Θ₃))
  have : Finite (ModGL τ K) := finite_modGL
  have hc : ∀ j, bitsTuple (K := K) bb j = 1 ∨ bitsTuple (K := K) bb j = -1 := bitsTuple_mem bb
  have hci : ∀ j, j ≠ i → bitsTuple (K := K) bb j = 1 := fun j hj => by
    simp [bitsTuple, hbb j hj]
  have hW := weyl_eq_one_of_fix_posKernel hτ hK2 hc
  obtain ⟨hcomm, hinv⟩ := evenCent_of_mulEquiv hz Θ
    (fun ψ : KernelComponent (maskChar (signTupleBits (bitsTuple (K := K) bb))) =>
      (componentRootSpan K (maskChar (signTupleBits (bitsTuple (K := K) bb))) ψ).subgroupOf
        (toralCentralizer τ K (bitsTuple bb)))
    (fun ψ => isComponent_componentRootSpan_toral hK2 hK5 hc ψ)
    (fun ψ => Burgoyne.even_card_of_isQuasisimple
      (isComponent_componentRootSpan_toral hK2 hK5 hc ψ).1)
    (toral_rootFactors_centComm hK2 hK5 hc hW) (toral_rootFactors_centInv hK2 hK5 hc hW hci)
  exact fAt_of_evenCent hcomm hinv

theorem famF_G2 :
    FamF .G2 :=
  famF_of_toralReps (τ := .G2) (by decide) (Or.inl rfl) (fun _ _ _ _ h => h.2) g2SignOrbit_check
    fun K _ _ ρ hρ hne => by
      have hlen : g2SignReps.length = 2 := rfl
      rw [hlen] at hρ
      interval_cases ρ
      · exact absurd (by funext i; revert i; decide) hne
      · exact ⟨listMask (g2SignReps.getD 1 []), ⟨0, by decide⟩, by decide, ⟨MulEquiv.refl _⟩⟩

theorem famF_F4 :
    FamF .F4 :=
  famF_of_toralReps (τ := .F4) (by decide) (Or.inr (Or.inl rfl)) (fun _ _ _ _ h => h.2)
    f4SignOrbit_check fun K _ _ ρ hρ hne => by
      have hlen : f4SignReps.length = 3 := rfl
      rw [hlen] at hρ
      interval_cases ρ
      · exact absurd (by funext i; revert i; decide) hne
      · exact ⟨listMask (f4SignReps.getD 1 []), ⟨0, by decide⟩, by decide, ⟨MulEquiv.refl _⟩⟩
      · exact ⟨listMask (f4SignReps.getD 2 []), ⟨2, by decide⟩, by decide, ⟨MulEquiv.refl _⟩⟩

theorem famF_E6 :
    FamF .E6 :=
  famF_of_toralReps (τ := .E6) (by decide) (Or.inr (Or.inr (Or.inl rfl))) (fun _ _ _ _ h => h.2)
    e6SignOrbit_check fun K _ _ ρ hρ hne => by
      have hlen : e6SignReps.length = 3 := rfl
      rw [hlen] at hρ
      interval_cases ρ
      · exact absurd (by funext i; revert i; decide) hne
      · exact ⟨listMask (e6SignReps.getD 1 []), ⟨0, by decide⟩, by decide, ⟨MulEquiv.refl _⟩⟩
      · exact ⟨listMask (e6SignReps.getD 2 []), ⟨1, by decide⟩, by decide, ⟨MulEquiv.refl _⟩⟩

@[expose] def p51qE8Word : List (Fin (Tag.rank .E8)) :=
  ([0, 2, 3, 4, 5, 6, 7] : List (Fin 8)).map fun j => ⟨j.1, j.2⟩

@[expose] def p51qE8Bits : Fin (Tag.rank .E8) → Bool :=
  listMask [false, false, false, false, false, false, false, true]

theorem maskAct_p51qE8Word :
    maskAct p51qE8Word p51qE8Bits = listMask (τ := .E8) (e8SignReps.getD 2 []) := by
  funext j
  revert j
  decide

theorem famF_E8 :
    FamF .E8 :=
  famF_of_toralReps (τ := .E8) (by decide) (Or.inr (Or.inr (Or.inr rfl))) (fun _ _ _ _ h => h.2)
    e8SignOrbit_check fun K _ hK2 ρ hρ hne => by
      have hlen : e8SignReps.length = 3 := rfl
      rw [hlen] at hρ
      interval_cases ρ
      · exact absurd (by funext i; revert i; decide) hne
      · exact ⟨listMask (e8SignReps.getD 1 []), ⟨0, by decide⟩, by decide, ⟨MulEquiv.refl _⟩⟩
      · have hmap := map_conj_toralCentralizer_of_maskAct (K := K) hK2 p51qE8Word p51qE8Bits
        rw [maskAct_p51qE8Word] at hmap
        exact ⟨p51qE8Bits, ⟨7, by decide⟩, by decide,
          ⟨(((toralCentralizer .E8 K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
            (MulEquiv.subgroupCongr hmap)).symm⟩⟩

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
