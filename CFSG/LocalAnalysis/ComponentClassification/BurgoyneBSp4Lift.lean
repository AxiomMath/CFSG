module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSp4Main
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.ComponentClassification.Burgoyne.PSL (conj_injective_of_mulEquiv slRingEquiv)
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K]

theorem eq_one_or_eq_lrInv_mul_of_scalar {g : StatedSp 2 K}
    (hg : g ∈ (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) :
    g = 1 ∨ g = lrInv K (0 : Fin 2) * lrInv K 1 := by
  rw [mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  have hgm : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (c : K) • 1 := by
    rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
    rfl
  have hJ := mem_statedSp_iff.1 g.2
  rw [hgm] at hJ
  have h1 := congrFun (congrFun hJ (Sum.inl 0)) (Sum.inr 0)
  simp only [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_apply, fromBlocks_apply₁₂, one_apply_eq, smul_eq_mul, mul_one] at h1
  rcases mul_self_eq_one_iff.mp h1 with h | h
  · left
    apply statedSp_ext
    rw [hgm, h, one_smul]
    rfl
  · right
    apply statedSp_ext
    rw [hgm, h, neg_one_smul, lrInv_zero_mul_lrInv_one]

theorem longRoot_perfect [Finite K] (h4 : 4 ≤ Nat.card K) (i : Fin 2) :
    ⁅longRoot K i, longRoot K i⁆ = longRoot K i := by
  have hSL : Group.IsPerfect SL(2, K) := CatalogueBGeneralLinear.specialLinear_perfect 2 K le_rfl
    (Or.inr (by omega)) (Or.inr (by omega))
  have : Group.IsPerfect (longRoot K i) :=
    Group.IsPerfect.ofSurjective (f := (longRootEquiv K i).symm.toMonoidHom)
      (longRootEquiv K i).symm.surjective
  exact Subgroup.isPerfect_iff.mp this

omit [Field K] in
theorem mem_socle_iff {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {T : Type} [Group T]
    (θ : GeneralizedFitting.subgroup X ≃* T) (x : X) :
    x ∈ GeneralizedFitting.subgroup X ↔
      socleAction θ x ∈ (MulAut.conj : T →* MulAut T).range := by
  have hψ := socleAction_injective hsimple hnab θ
  constructor
  · intro hx
    refine ⟨θ ⟨x, hx⟩, ?_⟩
    rw [← socleAction_symm θ, MulEquiv.symm_apply_apply]
  · rintro ⟨y, hy⟩
    rw [← socleAction_symm θ] at hy
    rw [← hψ hy]
    exact (θ.symm y).2

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]

omit [Finite J] in
theorem rhoZ_eq_one_of_phiO_eq_one {g : J} (h : phiO K g = 1) : rhoZ K g = 1 := by
  rw [conjQuotAction_eq_one_iff] at h ⊢
  intro l hl
  obtain ⟨z, hz, hzl⟩ := h l hl
  exact ⟨z, le_centralPreimage _ hz, hzl⟩

omit [Finite J] in
theorem orderOf_rangeRestrict_of_phiO (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K)) {t : J}
    (ht : orderOf (phiO K t) = 2) : orderOf ((rhoZ K).rangeRestrict t) = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    change rhoZ K t ^ 2 = 1
    rw [← map_pow]
    apply rhoZ_eq_one_of_phiO_eq_one
    have h2 := pow_orderOf_eq_one (phiO K t)
    rw [ht] at h2
    rw [map_pow]
    exact h2
  · intro h1
    have h2 : rhoZ K t = 1 := congrArg Subtype.val h1
    have h3 := phiO_eq_one_of_rhoZ_eq_one K hq h2
    rw [h3, orderOf_one] at ht
    exact absurd ht (by norm_num)

theorem burgoynePropB_PSp4 (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
    (hM4 : IsM4 (rhoZ K).range) {p' f' : ℕ} (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) .PSp 2 p' f') {t : J}
    (ht : orderOf (phiO K t) = 2) {Y : Subgroup J}
    (hY1 : Y.map (rhoZ K).rangeRestrict ≠ ⊥)
    (hY2 : Y.map (rhoZ K).rangeRestrict ≤ oddCentralizerCore ((rhoZ K).rangeRestrict t))
    {c : K ⧸ pPrimeCore 2 K} (hcZ : c ∈ center (K ⧸ pPrimeCore 2 K)) (hc2 : orderOf c = 2) :
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥ := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  rcases hL with ⟨-, hc'⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨⟨hp, hf, -, -⟩, K₀, _, _, hKc, ⟨θ⟩⟩ := hc'
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : Fact p'.Prime := ⟨hp⟩
  have : CharP K₀ p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K₀ ≠ 2 := by rw [ringChar.eq K₀ p']; exact hp2'
  set X := (rhoZ K).range with hX
  set ψ := socleAction θ with hψdef
  have hψ := socleAction_injective hsimple hnab θ
  have hInn : (MulAut.conj : StatedProj (StatedSp 2 K₀) →*
      MulAut (StatedProj (StatedSp 2 K₀))).range ≤ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact conj_mem_range_socleAction θ x
  have hinj := conj_injective_of_mulEquiv hsimple hnab θ
  have ht' := orderOf_rangeRestrict_of_phiO K hq ht
  obtain ⟨h5K, ψ', hψ', hInn', hpre, hprop⟩ := sp4_twin_X hp hp2' hf hKc hinj hψ hInn ht' hY1 hY2
  have h5 : 5 ≤ p' ^ f' := by rw [← hKc]; exact h5K
  have hsocle : ∀ x : X, x ∈ GeneralizedFitting.subgroup X ↔
      ψ' x ∈ (MulAut.conj : StatedProj (StatedSp 2 K₀) →*
        MulAut (StatedProj (StatedSp 2 K₀))).range := fun x => by
    rw [hpre, mem_socle_iff hsimple hnab θ]
  let : Algebra (ZMod p') K₀ := ZMod.algebra K₀ p'
  set eK := slRingEquiv (m := Fin 2) (GaloisField.algEquivGaloisField p' f' hKc).toRingEquiv
    with heK
  have hLZ := fun i : Fin 2 => longRoot_inf (K := K₀) le_rfl i
  have hle : ∀ i : Fin 2, slice (longRoot K₀ i) ≤ ψ'.range := fun i =>
    slice_le_range.trans hInn'
  obtain ⟨ū, -, hū, ⟨e₁⟩, ⟨e₂⟩, hcomm, hū₁, hū₂, hint, hs₁, hs₁s, hs₂, hs₂s, hprop₁, hprop₂⟩ :=
    twin_comap hψ' (hle 0) (hle 1) (hInn' ⟨_, rfl⟩) (orderOf_sp4u hK hinj)
      ((sliceEquivSL hinj (hLZ 0) (longRootEquiv K₀ 0)).trans eK)
      ((sliceEquivSL hinj (hLZ 1) (longRootEquiv K₀ 1)).trans eK) (fun a ha b hb =>
        slice_commute ha hb) (sp4u_mem_slice 0) (sp4u_mem_slice 1)
      (fun x hx₀ hx₁ => slice_inter hinj (by
        have h := pow_orderOf_eq_one (sp4u K₀)
        rw [orderOf_sp4u hK hinj, pow_two] at h
        exact h) hx₀ hx₁)
      (slice_le_centralizer_sp4u 0) (slice_isPComponent_sp4u hK h5K hinj hInn' 0)
      (slice_le_centralizer_sp4u 1) (slice_isPComponent_sp4u hK h5K hinj hInn' 1) (hprop 0)
      (hprop 1)
  have hrange := liftHom_range_eq K hq hsimple hnab
  have hSr : ∀ i : Fin 2, (slice (longRoot K₀ i)).comap ψ' ≤ (liftHom K).range := by
    intro i x hx
    rw [hrange, hsocle]
    exact slice_le_range (hx : ψ' x ∈ slice (longRoot K₀ i))
  set β : StatedSp 2 K₀ →* X := factorHom hψ' (conjProjH (StatedSp 2 K₀))
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
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSp 2 K₀),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : StatedSp 2 K₀ →* E, ∀ x, π (s x) = x := by
    intro E _ _ π hπ hker h2
    obtain ⟨s, hs, -⟩ :=
      CFSG.LieType.Steinberg.odd_symplectic_central_two_extension_splitting hK 2 hπ hker h2
    exact ⟨s, hs⟩
  obtain ⟨α, hαβ, -, hcen⟩ := exists_cover K hsplit hq hβr
  have hcT : c ∈ ⁅((slice (longRoot K₀ 0)).comap ψ').comap (liftHom K),
      ((slice (longRoot K₀ 0)).comap ψ').comap (liftHom K)⁆ ⊔
      ⁅((slice (longRoot K₀ 1)).comap ψ').comap (liftHom K),
        ((slice (longRoot K₀ 1)).comap ψ').comap (liftHom K)⁆ := by
    rw [hcen] at hcZ
    obtain ⟨g, hg, rfl⟩ := hcZ
    have hg1 : conjProjH (StatedSp 2 K₀) g = 1 := (factorHom_eq_one_iff hψ' _ _ g).mp hg
    have hg2 : projH (StatedSp 2 K₀) g = 1 := hinj (by rw [map_one]; exact hg1)
    have hgL : g ∈ longRoot K₀ 0 ⊔ longRoot K₀ 1 := by
      rcases eq_one_or_eq_lrInv_mul_of_scalar ((QuotientGroup.eq_one_iff g).mp hg2) with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact mul_mem (mem_sup_left (lrInv_mem 0)) (mem_sup_right (lrInv_mem 1))
    refine map_mem_sup_of_cover (liftHom K) α hαβ (longRoot_perfect (by omega) 0)
      (longRoot_perfect (by omega) 1) (fun g hg => ?_) (fun g hg => ?_) hgL
    · exact mem_comap_of_factorHom hψ' _ _ ⟨g, hg, rfl⟩
    · exact mem_comap_of_factorHom hψ' _ _ ⟨g, hg, rfl⟩
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  exact propB_of_twin K hq (hSr 0) (hSr 1) hp2' h5 e₁ e₂ hcomm hū hū₁ hū₂ hint hs₁ hs₁s hs₂
    hs₂s hprop₁ hprop₂ hcZ hc1 hcT

end CFSG.ComponentClassification.Burgoyne.B
