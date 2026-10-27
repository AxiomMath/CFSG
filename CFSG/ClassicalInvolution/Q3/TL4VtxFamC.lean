module

public import CFSG.ClassicalInvolution.Q3.TL4VtxFamB
public import CFSG.ClassicalInvolution.Q3.TL4VtxAut
public import CFSG.ClassicalInvolution.Q3.TL4VtxDich
public import CFSG.ClassicalInvolution.Q3.TL4VtxFam

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace Vtx

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {n : ℕ}

theorem ker_psiL_inf_conj (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q}
    (hK : K ∈ Φ) {z : Q} (hz : IsUniqueInvolution K z) {L : Subgroup Q} (hL : IsComponent L)
    (hm : ∃ y ∈ L, z * y ≠ y * z) (x : ↥(orbGrp Φ K)) :
    (psiL L (orbGrp Φ K) (orbGrp_le_normalizer h4 h hO hn hK hz hL hm)).ker ⊓
      conjSub x (K.subgroupOf (orbGrp Φ K)) = ⊥ := by
  have hXN := orbGrp_le_normalizer h4 h hO hn hK hz hL hm
  obtain ⟨y₀, hy₀, hne₀⟩ := hm
  have hLX : L ≤ orbGrp Φ K :=
    le_orbGrp_of_moves h.hyp.conjInvariant hK hL ⟨z, hz.mem, y₀, hy₀, hne₀⟩
  have hKX : K ≤ orbGrp Φ K := le_orbGrp K
  have hz₀ : IsUniqueInvolution (K.subgroupOf (orbGrp Φ K)) ⟨z, hKX hz.mem⟩ :=
    isUniqueInvolution_subgroupOf hz hKX
  have hk2 : IsPGroup 2 ↥(psiL L (orbGrp Φ K) hXN).ker := by
    rw [ker_psiL hXN hLX]
    exact isPGroup_centralizer_subgroupOf h4 h hO hn hK hz hL ⟨y₀, hy₀, hne₀⟩
  by_contra hne
  have hmem := T3.mem_of_isPGroup (hz₀.conj x) inf_le_right (hk2.to_le inf_le_left)
    ((Subgroup.one_lt_card_iff_ne_bot _).mpr hne)
  have hzk : (⟨z, hKX hz.mem⟩ : ↥(orbGrp Φ K)) ∈ (psiL L (orbGrp Φ K) hXN).ker := by
    have h1 := (psiL L (orbGrp Φ K) hXN).normal_ker.conj_mem _ hmem.1 x⁻¹
    simpa [mul_assoc] using h1
  exact hne₀ ((mem_ker_psiL_iff hXN _).mp hzk y₀ hy₀)

theorem typeRFam_imgFam (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q}
    (hK : K ∈ Φ) {z : Q} (hz : IsUniqueInvolution K z) {L : Subgroup Q} (hL : IsComponent L)
    (hm : ∃ y ∈ L, z * y ≠ y * z) (htf : TwinFreeAt Φ K z L) :
    TypeRFam 3 (imgFam Φ K L (orbGrp_le_normalizer h4 h hO hn hK hz hL hm)) := by
  have hcl := h.hyp.conjInvariant
  have hXN := orbGrp_le_normalizer h4 h hO hn hK hz hL hm
  obtain ⟨y₀, hy₀, hne₀⟩ := hm
  have hLX : L ≤ orbGrp Φ K := le_orbGrp_of_moves hcl hK hL ⟨z, hz.mem, y₀, hy₀, hne₀⟩
  have hKX : K ≤ orbGrp Φ K := le_orbGrp K
  obtain ⟨S', hd', hc'⟩ := tightCls_orbGrp h4 h hO hn hK hz
  have hcore : tightCore (K.subgroupOf (orbGrp Φ K)) = K.subgroupOf (orbGrp Φ K) := by
    rw [tightCore_subgroupOf ((tightCore_le K).trans hKX)]
    congr 1
    exact h.closure_twoElts hK
  have hΛ : TypeRFam 3 (CoreAssembly.conjClass (K.subgroupOf (orbGrp Φ K))) := by
    have h1 := typeRFam_of_tightDatum (r := 3) hd' hc'.1
    rwa [hcore] at h1
  have hconjX : ∀ x : ↥(orbGrp Φ K), conjSub (x : Q) K ≤ orbGrp Φ K :=
    fun x => conjSub_le_orbGrp K ⟨x, orbGrp_le hcl hK x.2⟩
  have himgM : ∀ x : ↥(orbGrp Φ K), (conjSub x (K.subgroupOf (orbGrp Φ K))).map
      (psiL L (orbGrp Φ K) hXN) = inducedImage L (conjSub (x : Q) K) := fun x => by
    rw [conjSub_subgroupOf, map_psiL hXN (hconjX x)]
  have hz₀ : IsUniqueInvolution (K.subgroupOf (orbGrp Φ K)) ⟨z, hKX hz.mem⟩ :=
    isUniqueInvolution_subgroupOf hz hKX
  have hmove : ∀ m : ↥(Subgroup.normalizer (L : Set Q)), ∀ x : ↥(orbGrp Φ K),
      ∃ x' ∈ orbGrp Φ K, conjSub x' K = conjSub ((m : Q) * x) K := by
    intro m x
    have hmx : (m : Q) * x ∈ Subgroup.normalizer (L : Set Q) :=
      Subgroup.mul_mem _ m.2 (hXN x.2)
    exact exists_conj_of_moves h4 h hO hn hL hK (hcl _ K hK) ⟨z, hz.mem, y₀, hy₀, hne₀⟩
      ⟨_, conj_mem_conjSub hz.mem, _, (Subgroup.mem_normalizer_iff.mp hmx y₀).mp hy₀,
        conj_ne_conj hne₀⟩
  refine TypeRFam.map hΛ (psiL L (orbGrp Φ K) hXN) ?_ ?_ ?_ ?_ ?_
  · rw [ker_psiL hXN hLX]
    exact centralizer_subgroupOf_le_center h4 h hO hn hK hz hL ⟨y₀, hy₀, hne₀⟩
  · rintro _ ⟨x, rfl⟩
    exact ker_psiL_inf_conj h4 h hO hn hK hz hL ⟨y₀, hy₀, hne₀⟩ x
  · intro g M hM
    obtain ⟨x, rfl⟩ := hM
    obtain ⟨m, rfl⟩ : ∃ m, toInducedAutOn L m = g := MonoidHom.rangeRestrict_surjective _ g
    obtain ⟨x', hx', e⟩ := hmove m x
    refine ⟨conjSub (⟨x', hx'⟩ : ↥(orbGrp Φ K)) (K.subgroupOf (orbGrp Φ K)),
      ⟨⟨x', hx'⟩, rfl⟩, ?_⟩
    dsimp only
    rw [himgM, himgM, conjSub_inducedImage, ← conjSub_mul]
    exact congrArg (inducedImage L) e.symm
  · rintro _ ⟨x, rfl⟩ z' hz' g hg
    dsimp only at hz' ⊢
    obtain ⟨m, rfl⟩ : ∃ m, toInducedAutOn L m = g := MonoidHom.rangeRestrict_surjective _ g
    obtain rfl := hz'.eq (hz₀.conj x)
    rw [himgM, mem_normalizer_iff_conjSub_eq, conjSub_inducedImage]
    set zN : ↥(Subgroup.normalizer (L : Set Q)) :=
      Subgroup.inclusion hXN (x * ⟨z, hKX hz.mem⟩ * x⁻¹) with hzN
    have hzNc : (zN : Q) = (x : Q) * z * (x : Q)⁻¹ := by
      rw [hzN]
      simp
    have h1 : toInducedAutOn L (m * zN * m⁻¹ * zN⁻¹) = 1 := by
      have hg' : toInducedAutOn L m * toInducedAutOn L zN =
          toInducedAutOn L zN * toInducedAutOn L m := hg
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg']
      group
    have hw := Lemma52Proof.commute_of_toInducedAutOn_eq_one L (m * zN * m⁻¹ * zN⁻¹).2 h1
    obtain ⟨x', hx', e⟩ := hmove m x
    have hx'z : (x' : Q) * z * x'⁻¹ = (m : Q) * ((x : Q) * z * (x : Q)⁻¹) * (m : Q)⁻¹ := by
      have h2 := hz.conj x'
      rw [e] at h2
      have h3 := h2.eq (hz.conj ((m : Q) * x))
      rw [h3]
      group
    have hfix := htf ((x : Q)⁻¹ * x') (Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) hx')
      fun l hl => by
        have hc := commute_conj_of_mem_normalizer (Subgroup.inv_mem _ (hXN x.2)) hw l hl
        have e2 : (x : Q)⁻¹ * x' * z * ((x : Q)⁻¹ * x')⁻¹ * z⁻¹ =
            (x : Q)⁻¹ * ((m * zN * m⁻¹ * zN⁻¹ : ↥(Subgroup.normalizer (L : Set Q))) : Q) *
              (x : Q)⁻¹⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzNc]
          calc (x : Q)⁻¹ * x' * z * ((x : Q)⁻¹ * x')⁻¹ * z⁻¹ =
              (x : Q)⁻¹ * ((x' : Q) * z * x'⁻¹) * x * z⁻¹ := by group
            _ = (x : Q)⁻¹ * ((m : Q) * ((x : Q) * z * (x : Q)⁻¹) * (m : Q)⁻¹) * x * z⁻¹ := by
                rw [hx'z]
            _ = _ := by group
        rw [e2]
        exact hc
    have hmz : (m : Q) ∈ Subgroup.centralizer ({(x : Q) * z * (x : Q)⁻¹} : Set Q) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h4 : (x' : Q) * z * x'⁻¹ = (x : Q) * z * (x : Q)⁻¹ := by
        calc (x' : Q) * z * x'⁻¹ =
            (x : Q) * (((x : Q)⁻¹ * x') * z * ((x : Q)⁻¹ * x')⁻¹) * (x : Q)⁻¹ := by group
          _ = (x : Q) * z * (x : Q)⁻¹ := by rw [hfix]
      rw [hx'z] at h4
      calc (m : Q) * ((x : Q) * z * (x : Q)⁻¹) =
          ((m : Q) * ((x : Q) * z * (x : Q)⁻¹) * (m : Q)⁻¹) * m := by group
        _ = ((x : Q) * z * (x : Q)⁻¹) * m := by rw [h4]
    have hN := h.tight (conjSub (x : Q) K) (hcl _ K hK) _ (hz.conj x) hmz
    rw [mem_normalizer_iff_conjSub_eq.mp hN]
  · rintro _ ⟨x₁, rfl⟩ _ ⟨x₂, rfl⟩ z₁' z₂' hz₁ hz₂ he
    dsimp only at hz₁ hz₂ ⊢
    obtain rfl := hz₁.eq (hz₀.conj x₁)
    obtain rfl := hz₂.eq (hz₀.conj x₂)
    have hk : (x₁ * ⟨z, hKX hz.mem⟩ * x₁⁻¹) * (x₂ * ⟨z, hKX hz.mem⟩ * x₂⁻¹)⁻¹ ∈
        (psiL L (orbGrp Φ K) hXN).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    have hw := (mem_ker_psiL_iff hXN _).mp hk
    have hfix := htf ((x₂ : Q)⁻¹ * x₁) (Subgroup.mul_mem _ (Subgroup.inv_mem _ x₂.2) x₁.2)
      fun l hl => by
        have hc := commute_conj_of_mem_normalizer (Subgroup.inv_mem _ (hXN x₂.2)) hw l hl
        have e2 : (x₂ : Q)⁻¹ * x₁ * z * ((x₂ : Q)⁻¹ * x₁)⁻¹ * z⁻¹ =
            (x₂ : Q)⁻¹ * ((((x₁ * ⟨z, hKX hz.mem⟩ * x₁⁻¹) *
              (x₂ * ⟨z, hKX hz.mem⟩ * x₂⁻¹)⁻¹ : ↥(orbGrp Φ K))) : Q) * (x₂ : Q)⁻¹⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e2]
        exact hc
    have hzeq : x₁ * (⟨z, hKX hz.mem⟩ : ↥(orbGrp Φ K)) * x₁⁻¹ =
        x₂ * ⟨z, hKX hz.mem⟩ * x₂⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (x₁ : Q) * z * (x₁ : Q)⁻¹ =
          x₂ * (((x₂ : Q)⁻¹ * x₁) * z * ((x₂ : Q)⁻¹ * x₁)⁻¹) * (x₂ : Q)⁻¹ := by group
        _ = x₂ * z * (x₂ : Q)⁻¹ := by rw [hfix]
    have hJ : IsUniqueInvolution (conjSub x₂ (K.subgroupOf (orbGrp Φ K)))
        (x₁ * ⟨z, hKX hz.mem⟩ * x₁⁻¹) := by
      rw [hzeq]
      exact hz₀.conj x₂
    exact (hΛ.noTwins _ ⟨x₁, rfl⟩ _ ⟨⟨x₂, rfl⟩, _, hz₀.conj x₁, hJ⟩).symm

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
