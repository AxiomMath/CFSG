module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSU4Twin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSp4Lift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBInputsU
public import CFSG.LieType.Steinberg.CentralExt.UnitaryHigher
public import CFSG.LieType.Universal.Unitary.Comparison
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (signMat slRingEquiv conj_injective_of_mulEquiv)
open scoped MatrixGroups

theorem statedSU_central_two_splitting {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 2 ≤ n) (E : Type) [Group E] [Finite E] (π : E →* StatedSU n (p ^ f) F)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E) (h2 : IsPGroup 2 π.ker) :
    ∃ s : StatedSU n (p ^ f) F →* E, ∀ x, π (s x) = x := by
  set ψ := CFSG.LieType.Universal.Unitary.equivStatedSU hF n
  have hker : (ψ.symm.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ψ.symm.injective]
  obtain ⟨s, hs, -⟩ := CFSG.LieType.Steinberg.su_central_two_extension_splitting hF hp2 hn
    (π := ψ.symm.toMonoidHom.comp π) (ψ.symm.surjective.comp hπ) (hker ▸ hcen) (hker ▸ h2)
  exact ⟨s.comp ψ.symm.toMonoidHom, fun g => ψ.symm.injective (hs (ψ.symm g))⟩

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]

theorem burgoynePropB_PSU4 (hcov : BurgoynePropBSU4CoverInput) (hexc : BurgoynePropBSU4ExcInput)
    {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K} (hH : PropBHyp J K t Y c) {p' f' : ℕ}
    (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) .PSU 4 p' f') :
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥ := by
  obtain ⟨hq, hM4, ht, hY1, hY2, s, hs2, -, -, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2, -⟩ := id hH
  have hII : PropBHypII (K ⧸ pPrimeCore 2 K) c := ⟨s, hs2, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2⟩
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  rcases hL with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨⟨hp, hf, -, -⟩, K₀, _, _, hKc, ⟨θ⟩⟩ := hcl
  have h : UnitaryFieldData p' f' K₀ := ⟨hp, hf, by rw [hKc, ← pow_mul, mul_comm]⟩
  have : Fact p'.Prime := ⟨hp⟩
  have := h.charP
  have h2 := utwo_ne_zero h hp2'
  set X := (rhoZ K).range with hX
  set ψ := socleAction θ with hψdef
  have hψ := socleAction_injective hsimple hnab θ
  have hInn : (MulAut.conj : StatedProj (StatedSU 4 (p' ^ f') K₀) →*
      MulAut (StatedProj (StatedSU 4 (p' ^ f') K₀))).range ≤ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact conj_mem_range_socleAction θ x
  have hinj := conj_injective_of_mulEquiv hsimple hnab θ
  have ht' := orderOf_rangeRestrict_of_phiO K hq ht
  rcases su4_twin_X h hp2' rfl hinj hψ hInn ht' hY1 hY2 with
    ⟨A, hα, H, J₀, l, hl0, hodd, hHA⟩ | ⟨h5, ψ', hψ', hInn', hpre, a, b, c', d, hab, hcd, hpair,
      hprop₁, hprop₂⟩
  · exact (hexc J K t Y c hH p' f' K₀ h hp2' θ A hα H J₀ l hl0 hodd hHA).elim
  have hsocle : ∀ x : X, x ∈ GeneralizedFitting.subgroup X ↔
      ψ' x ∈ (MulAut.conj : StatedProj (StatedSU 4 (p' ^ f') K₀) →*
        MulAut (StatedProj (StatedSU 4 (p' ^ f') K₀))).range :=
    fun x => by rw [hpre, mem_socle_iff hsimple hnab θ]
  have := h.finite
  set F := CFSG.LieType.Steinberg.fixedSubfield K₀ p' f' with hFdef
  have hFc : Nat.card F = p' ^ f' := CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  have hF2 : ringChar F ≠ 2 := ringChar_fixedSubfield_ne_two h2
  have : Fintype F := Fintype.ofFinite F
  have : CharP F p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  let : Algebra (ZMod p') F := ZMod.algebra F p'
  set eK := slRingEquiv (m := Fin 2) (GaloisField.algEquivGaloisField p' f' hFc).toRingEquiv
    with heK
  obtain ⟨e₁⟩ := nonempty_uBlock_pair_equiv h hab
  obtain ⟨e₂⟩ := nonempty_uBlock_pair_equiv h hcd
  obtain ⟨k₁, hk₁⟩ := PSL.exists_not_mem_pair (by norm_num : 3 ≤ 4) a b
  obtain ⟨k₂, hk₂⟩ := PSL.exists_not_mem_pair (by norm_num : 3 ≤ 4) c' d
  have hLZ₁ : ∀ g ∈ uBlock p' f' K₀ {a, b}, g ∈ (StatedScalars (Fin 4) K₀).subgroupOf
      (StatedSU 4 (p' ^ f') K₀) → g = 1 := fun g hg hz => eq_one_of_mem_uBlock_scalars hk₁ hg hz
  have hLZ₂ : ∀ g ∈ uBlock p' f' K₀ {c', d}, g ∈ (StatedScalars (Fin 4) K₀).subgroupOf
      (StatedSU 4 (p' ^ f') K₀) → g = 1 := fun g hg hz => eq_one_of_mem_uBlock_scalars hk₂ hg hz
  have huu := conjProjH_uPairSign_eq h hab hcd hpair
  have hu : orderOf (conjProjH (StatedSU 4 (p' ^ f') K₀) (uPairSign h hab)) = 2 :=
    orderOf_sliceInv hinj hLZ₁ hF2 (uPairSign_mem h hab) e₁ (uPairSign_eq_neg_one h h2 hab e₁)
  obtain ⟨ū, -, hū, ⟨f₁⟩, ⟨f₂⟩, hcomm, hū₁, hū₂, hint, hs₁, hs₁s, hs₂, hs₂s, hprop₁', hprop₂'⟩ :=
    twin_comap hψ' (slice_le_range.trans hInn') (slice_le_range.trans hInn')
      (u := conjProjH (StatedSU 4 (p' ^ f') K₀) (uPairSign h hab)) (hInn' ⟨_, rfl⟩) hu
      ((sliceEquivSL hinj hLZ₁ e₁).trans eK) ((sliceEquivSL hinj hLZ₂ e₂).trans eK)
      (fun x hx y hy => uslice_commute (disjoint_of_pair hpair) hx hy)
      ⟨uPairSign h hab, uPairSign_mem h hab, rfl⟩
      (by rw [← huu]; exact ⟨uPairSign h hcd, uPairSign_mem h hcd, rfl⟩)
      (fun x hx₁ hx₂ => uslice_inter h hinj h2 hab hpair e₁ hx₁ hx₂)
      (slice_le_centralizer (fun g hg => commute_uPairSign h h2 hab hg))
      (uslice_isPComponent h hp2' h5 (by norm_num) hinj hInn' hab)
      (by rw [← huu]; exact slice_le_centralizer (fun g hg => commute_uPairSign h h2 hcd hg))
      (by rw [← huu]; exact uslice_isPComponent h hp2' h5 (by norm_num) hinj hInn' hcd)
      hprop₁ hprop₂
  have hrange := liftHom_range_eq K hq hsimple hnab
  have hSr : ∀ {I : Finset (Fin 4)}, (slice (uBlock p' f' K₀ I)).comap ψ' ≤
      (liftHom K).range := by
    intro I g hg
    rw [hrange, hsocle]
    exact slice_le_range (hg : ψ' g ∈ slice (uBlock p' f' K₀ I))
  set β : StatedSU 4 (p' ^ f') K₀ →* X := factorHom hψ' (conjProjH (StatedSU 4 (p' ^ f') K₀))
    (fun g => hInn' ⟨_, rfl⟩) with hβ
  have hβr : β.range = (liftHom K).range := by
    rw [hrange]
    ext x
    rw [hsocle]
    constructor
    · rintro ⟨g, rfl⟩
      rw [factorHom_spec]
      exact ⟨_, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨g, rfl⟩ := projH_surjective y
      refine ⟨g, hψ' ?_⟩
      rw [factorHom_spec]
      exact hy
  obtain ⟨α, hαβ, hαs, -⟩ := exists_cover K
    (statedSU_central_two_splitting h.card_eq_sq hp2' (by norm_num)) hq hβr
  set g₀ : StatedSU 4 (p' ^ f') K₀ := uPairSign h hab * uPairSign h hcd with hg₀
  have hg₀m : ((g₀ : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀) = -1 := by
    rw [hg₀, Subgroup.coe_mul, Units.val_mul, coe_uPairSign, coe_uPairSign,
      signMat_mul_signMat_eq_neg_one hpair]
  have hcg : c = α g₀ := hcov p' f' K₀ h hp2' _ α hαs c hII g₀ hg₀m
  have hR : ∀ {x y : Fin 4} (hxy : x ≠ y),
      ⁅uBlock p' f' K₀ {x, y}, uBlock p' f' K₀ {x, y}⁆ = uBlock p' f' K₀ {x, y} := by
    intro x y hxy
    have hq' := isQuasisimple_uBlock h hp2' (J := {x, y}) (by rw [Finset.card_pair hxy])
      (Or.inr h5)
    have : Group.IsPerfect (uBlock p' f' K₀ {x, y}) := hq'.1
    exact Subgroup.isPerfect_iff.mp this
  have hcT := map_mem_sup_of_cover (liftHom K) α hαβ (hR hab) (hR hcd)
    (S₁ := (slice (uBlock p' f' K₀ {a, b})).comap ψ')
    (S₂ := (slice (uBlock p' f' K₀ {c', d})).comap ψ')
    (fun g hg => mem_comap_of_factorHom hψ' _ _ ⟨g, hg, rfl⟩)
    (fun g hg => mem_comap_of_factorHom hψ' _ _ ⟨g, hg, rfl⟩)
    (mul_mem (mem_sup_left (uPairSign_mem h hab)) (mem_sup_right (uPairSign_mem h hcd)) :
      g₀ ∈ uBlock p' f' K₀ {a, b} ⊔ uBlock p' f' K₀ {c', d})
  rw [← hcg] at hcT
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  exact propB_of_twin K hq hSr hSr hp2' h5 f₁ f₂ hcomm hū hū₁ hū₂ hint hs₁ hs₁s hs₂ hs₂s
    hprop₁' hprop₂' hcZ hc1 hcT

end CFSG.ComponentClassification.Burgoyne.B
