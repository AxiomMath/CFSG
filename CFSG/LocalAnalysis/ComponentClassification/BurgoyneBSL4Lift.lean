module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSL4Twin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSp4Lift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBInputs
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.Burgoyne.PSL
open scoped MatrixGroups

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]

theorem burgoynePropB_PSL4 (hcov : BurgoynePropBSL4CoverInput) (hexc : BurgoynePropBSL4ExcInput)
    {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K} (hH : PropBHyp J K t Y c) {p' f' : ℕ}
    (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) .PSL 4 p' f') :
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
  obtain ⟨hp, hf, -⟩ : p'.Prime ∧ 1 ≤ f' ∧ 2 ≤ 4 := by
    rcases hL with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact ⟨h.1, h.2.1, h.2.2.1⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  obtain ⟨K₀, _, _, hKc, ⟨θ⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : Fact p'.Prime := ⟨hp⟩
  have : CharP K₀ p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K₀ ≠ 2 := by rw [ringChar.eq K₀ p']; exact hp2'
  set X := (rhoZ K).range with hX
  set ψ := socleAction θ with hψdef
  have hψ := socleAction_injective hsimple hnab θ
  have hInn : (MulAut.conj : projectiveSL 4 K₀ →* MulAut (projectiveSL 4 K₀)).range ≤
      ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact conj_mem_range_socleAction θ x
  have hinj := conj_injective_of_mulEquiv hsimple hnab θ
  have ht' := orderOf_rangeRestrict_of_phiO K hq ht
  rcases sl4_twin_X hp hp2' hf hKc hinj hψ hInn ht' hY1 hY2 with
    ⟨A, hα, H, J₀, μ, hodd, hHA⟩ | ⟨h5K, ψ', hψ', hInn', hpre, a, b, c', d, hab, hcd, hpair,
      hprop₁, hprop₂⟩
  · exact (hexc J K t Y c hH K₀ hK θ A hα H J₀ μ hodd hHA).elim
  have h5 : 5 ≤ p' ^ f' := by rw [← hKc]; exact h5K
  have hsocle : ∀ x : X, x ∈ GeneralizedFitting.subgroup X ↔
      ψ' x ∈ (MulAut.conj : projectiveSL 4 K₀ →* MulAut (projectiveSL 4 K₀)).range :=
    fun x => by rw [hpre, mem_socle_iff hsimple hnab θ]
  let : Algebra (ZMod p') K₀ := ZMod.algebra K₀ p'
  set eK := slRingEquiv (m := Fin 2) (GaloisField.algEquivGaloisField p' f' hKc).toRingEquiv
    with heK
  have hle : ∀ {x y : Fin 4}, pairSlice K₀ x y ≤ ψ'.range := fun {x y} =>
    pairSlice_le_range.trans hInn'
  have huu := pairInvolution_eq (K := K₀) hab hcd hpair
  have hu : orderOf (pairInvolution K₀ hab) = 2 := orderOf_pairInvolution hK (by omega) hinj hab
  obtain ⟨ū, -, hū, ⟨e₁⟩, ⟨e₂⟩, hcomm, hū₁, hū₂, hint, hs₁, hs₁s, hs₂, hs₂s, hprop₁', hprop₂'⟩ :=
    twin_comap hψ' hle hle (u := pairInvolution K₀ hab) (hInn' ⟨_, rfl⟩) hu
      ((pairSliceEquivSL (by omega) hinj hab).trans eK)
      ((pairSliceEquivSL (by omega) hinj hcd).trans eK) (fun x hx y hy =>
        pairSlice_commute hpair hx hy) (pairInvolution_mem hab)
      (by rw [← huu]; exact pairInvolution_mem hcd)
      (fun x hx₁ hx₂ => pairSlice_inter hinj hab hpair (by
        have h := pow_orderOf_eq_one (pairInvolution K₀ hab)
        rw [hu, pow_two] at h
        exact h) hx₁ hx₂)
      (pairSlice_le_centralizer hab)
      (pairSlice_isPComponent hK (by omega) hinj (by omega) hInn' hab)
      (by rw [← huu]; exact pairSlice_le_centralizer hcd)
      (by rw [← huu]; exact pairSlice_isPComponent hK (by omega) hinj (by omega) hInn' hcd)
      hprop₁ hprop₂
  have hrange := liftHom_range_eq K hq hsimple hnab
  have hSr : ∀ {x y : Fin 4}, (pairSlice K₀ x y).comap ψ' ≤ (liftHom K).range := by
    intro x y g hg
    rw [hrange, hsocle]
    exact pairSlice_le_range (hg : ψ' g ∈ pairSlice K₀ x y)
  set β : SL(4, K₀) →* X := factorHom hψ' (conjProj 4 K₀) (fun g => hInn' ⟨_, rfl⟩) with hβ
  have hβr : β.range = (liftHom K).range := by
    rw [hrange]
    ext x
    rw [hsocle]
    constructor
    · rintro ⟨g, rfl⟩
      rw [factorHom_spec]
      exact ⟨_, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨g, rfl⟩ := proj_surjective 4 K₀ y
      refine ⟨g, hψ' ?_⟩
      rw [factorHom_spec]
      exact hy
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SL(4, K₀)),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : SL(4, K₀) →* E, ∀ x, π (s x) = x := by
    intro E _ _ π hπ hker h2
    obtain ⟨s, hs, -⟩ :=
      CFSG.LieType.Steinberg.sl_central_two_extension_splitting 3 hK hπ hker h2
    exact ⟨s, hs⟩
  obtain ⟨α, hαβ, hαs, -⟩ := exists_cover K hsplit hq hβr
  set g₀ : SL(4, K₀) := signSL K₀ {a, b} (even_card_pair hab) * signSL K₀ {c', d}
    (even_card_pair hcd) with hg₀
  have hg₀m : (g₀ : Matrix (Fin 4) (Fin 4) K₀) = -1 := by
    rw [hg₀, Matrix.SpecialLinearGroup.coe_mul, coe_signSL, coe_signSL,
      signMat_mul_signMat_eq_neg_one hpair]
  have hcg : c = α g₀ := hcov K₀ hK _ α hαs c hII g₀ hg₀m
  have hR : ∀ {x y : Fin 4} (hxy : x ≠ y),
      ⁅coordBlock K₀ {x, y}, coordBlock K₀ {x, y}⁆ = coordBlock K₀ {x, y} := by
    intro x y hxy
    have hq' := isQuasisimple_coordBlock (K := K₀) (J := {x, y})
      (by rw [Finset.card_pair hxy]) (Or.inr (by omega))
    have : Group.IsPerfect (coordBlock K₀ {x, y}) := hq'.1
    exact Subgroup.isPerfect_iff.mp this
  have hcT := map_mem_sup_of_cover (liftHom K) α hαβ (hR hab) (hR hcd)
    (S₁ := (pairSlice K₀ a b).comap ψ') (S₂ := (pairSlice K₀ c' d).comap ψ')
    (fun g hg => mem_comap_of_factorHom hψ' _ _ ⟨g, hg, rfl⟩)
    (fun g hg => mem_comap_of_factorHom hψ' _ _ ⟨g, hg, rfl⟩)
    (mul_mem (mem_sup_left (signSL_mem_coordBlock _ _))
      (mem_sup_right (signSL_mem_coordBlock _ _)) :
        g₀ ∈ coordBlock K₀ {a, b} ⊔ coordBlock K₀ {c', d})
  rw [← hcg] at hcT
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  exact propB_of_twin K hq hSr hSr hp2' h5 e₁ e₂ hcomm hū hū₁ hū₂ hint hs₁ hs₁s hs₂ hs₂s
    hprop₁' hprop₂' hcZ hc1 hcT

end CFSG.ComponentClassification.Burgoyne.B
