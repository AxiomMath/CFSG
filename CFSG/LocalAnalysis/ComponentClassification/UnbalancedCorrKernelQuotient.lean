module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open scoped Pointwise

theorem isStandardSubgroup_map_of_surjective {F A : Type*} [Group F] [Group A] (η : F →* A)
    (hηs : Function.Surjective η) {W L : Subgroup F} [hWn : W.Normal]
    (hKodd : Odd (Nat.card η.ker)) (hWK : W ⊓ η.ker = ⊥) (hKW : η.ker ≤ centralizer (W : Set F))
    (hLW : L ≤ W) (hL : IsStandardSubgroup L) : IsStandardSubgroup (L.map η) := by
  obtain ⟨hq, heven, hodd, hnorm, hcomm⟩ := hL
  set CL := centralizer (L : Set F) with hCL
  have hKCL : η.ker ≤ CL := hKW.trans (centralizer_le hLW)
  have hpre : (centralizer (L.map η : Set A)).comap η = CL :=
    OutcomeLocal.comap_centralizer_map hWK hLW
  have hC0 : centralizer (L.map η : Set A) = CL.map η := by
    rw [← hpre, map_comap_eq_self_of_surjective hηs]
  have hNC : (normalizer (CL.map η : Set A)).comap η = normalizer (CL : Set F) :=
    OutcomeLocal.comap_normalizer_map_of_ker_le hηs hKCL
  have hNL : (normalizer (L.map η : Set A)).comap η = normalizer (L : Set F) :=
    OutcomeLocal.comap_normalizer_map hWK hLW
  obtain ⟨e, -⟩ := OutcomeLocal.exists_mulEquiv_map_of_inf_ker_eq_bot (η := η) (L := L)
    (eq_bot_iff.mpr ((inf_le_inf_right _ hLW).trans hWK.le))
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ?_, ?_, ?_⟩
  · rw [hC0]
    have hcard : Nat.card (η.ker.subgroupOf CL) * Nat.card (CL.map η) = Nat.card CL := by
      have h1 := (η.comp CL.subtype).ker.card_mul_index
      have h2 : (η.comp CL.subtype).ker = η.ker.subgroupOf CL := by
        rw [← MonoidHom.comap_ker]
        rfl
      rw [Subgroup.index_ker, MonoidHom.range_comp, range_subtype, h2] at h1
      exact h1
    rw [← hcard, Nat.card_congr (subgroupOfEquivOfLe hKCL).toEquiv] at heven
    rcases Nat.even_mul.mp heven with h | h
    · exact absurd hKodd (Nat.not_odd_iff_even.mpr h)
    · exact h
  · intro g₀ hg₀
    obtain ⟨g, rfl⟩ := hηs g₀
    rw [hC0] at hg₀ ⊢
    have hg : g ∉ normalizer (CL : Set F) := fun hg => hg₀ (by
      rw [← hNC] at hg
      exact hg)
    have hKg : η.ker ≤ conjugate CL g := by
      intro k hk
      refine ⟨g * k * g⁻¹, hKCL ((inferInstance : η.ker.Normal).conj_mem k hk g), ?_⟩
      simp [mul_assoc]
    rw [← OutcomeLocal.map_conjugate, ← OutcomeLocal.map_inf_of_ker_le hηs hKCL hKg]
    exact Odd.of_dvd_nat (hodd g hg) (card_map_dvd _ _)
  · rw [hC0]
    apply comap_injective hηs
    rw [hNC, hNL, hnorm]
  · intro g₀ hbot
    obtain ⟨g, rfl⟩ := hηs g₀
    rw [← OutcomeLocal.map_conjugate, ← map_commutator, Subgroup.map_eq_bot_iff] at hbot
    have hcW : ⁅L, conjugate L g⁆ ≤ W :=
      (commutator_mono hLW (OutcomeLocal.conjugate_le_of_le_normal hLW g)).trans
        (commutator_le_left W W)
    exact hcomm g (eq_bot_iff.mpr ((le_inf hcW hbot).trans hWK.le))

theorem faithful_quotient_facts {F A : Type*} [Group F] [Finite F] [Group A] [Finite A]
    {ι : Type*} [Finite ι] (S : ι → Subgroup F) (hS : ∀ i, IsSimpleGroup (S i))
    (hSab : ∀ i, ∃ a b : S i, a * b ≠ b * a)
    (hcomm : Pairwise fun i j => ∀ x y : F, x ∈ S i → y ∈ S j → Commute x y)
    (hind : iSupIndep S) {W : Subgroup F} (hSW : ⨆ i, S i = W) [hWn : W.Normal] (hW1 : W ≠ ⊥)
    (hodd : Odd (Nat.card (centralizer (W : Set F))))
    (η : F →* A) (hη : Function.Surjective η) (hker : η.ker = pPrimeCore 2 F)
    {L : Subgroup F} (hLW : L ≤ W) (hLstd : IsStandardSubgroup L) {t : F}
    (htL : L ≤ centralizer ({t} : Set F)) (ht2 : orderOf t = 2)
    (hLt : IsComponent (L.subgroupOf (centralizer ({t} : Set F))))
    (hLcl : (⨆ e ∈ layer F, conjugate L e) = W) (hWt : ⁅W, zpowers t⁆ = W) :
    pPrimeCore 2 F = centralizer (W : Set F) ∧ W ⊓ pPrimeCore 2 F = ⊥ ∧ layer F = W ∧
    (⨆ f : F, conjugate L f) = W ∧ pCore 2 F = ⊥ ∧
    (∃ e : W ≃* W.map η, ∀ w : W, (e w : A) = η w) ∧
    (∃ e : L ≃* L.map η, ∀ x : L, (e x : A) = η x) ∧
    centralizer (W.map η : Set A) = ⊥ ∧ layer A = W.map η ∧ generalizedFitting A = W.map η ∧
    fittingSubgroup A = ⊥ ∧ pPrimeCore 2 A = ⊥ ∧ pCore 2 A = ⊥ ∧
    (⨆ g : A, conjugate (L.map η) g) = W.map η ∧ ⁅W.map η, zpowers (η t)⁆ = W.map η ∧
    orderOf (η t) = 2 ∧ IsStandardSubgroup (L.map η) ∧
    centralizer ({η t} : Set A) = (centralizer ({t} : Set F)).map η ∧
    L.map η ≤ centralizer ({η t} : Set A) ∧
    IsComponent ((L.map η).subgroupOf (centralizer ({η t} : Set A))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKeq, hWK, hlayer, hO2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgen⟩ :=
    OutcomeLocal.odd_centralizer_semisimple_layer_faithful_standard_quotient S hS hSab hcomm hind
      hSW hW1 hodd
  set K := pPrimeCore 2 F with hKdef
  have hKodd : Odd (Nat.card K) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hWK' : W ⊓ η.ker = ⊥ := by rw [hker]; exact hWK
  obtain ⟨eW, heW⟩ := OutcomeLocal.exists_mulEquiv_map_of_inf_ker_eq_bot hWK'
  obtain ⟨eL, heL⟩ := OutcomeLocal.exists_mulEquiv_map_of_inf_ker_eq_bot (η := η) (L := L)
    (eq_bot_iff.mpr ((inf_le_inf_right _ hLW).trans hWK'.le))
  have hcent := OutcomeLocal.comap_centralizer_map hWK' (le_rfl : W ≤ W)
  have hCA : centralizer (W.map η : Set A) = ⊥ := by
    rw [← map_comap_eq_self_of_surjective hη (centralizer (W.map η : Set A)), hcent, ← hKeq,
      ← hker]
    exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
  have hSW' : ∀ i, S i ≤ W := fun i => hSW ▸ le_iSup S i
  have hWn' : (⨆ j, S j).Normal := by rw [hSW]; exact hWn
  have hcomp : ∀ i, IsComponent (S i) := OutcomeLocal.isComponent_factor hS hSab hcomm
  have hcompA : ∀ i, IsComponent ((S i).map η) := by
    intro i
    obtain ⟨e, -⟩ := OutcomeLocal.exists_mulEquiv_map_of_inf_ker_eq_bot (η := η) (L := S i)
      (eq_bot_iff.mpr ((inf_le_inf_right _ (hSW' i)).trans hWK'.le))
    exact ⟨LocalCores.isQuasisimple_of_mulEquiv e (hcomp i).1, (hcomp i).2.map hη⟩
  have hW0 : W.map η = ⨆ i, (S i).map η := by rw [← hSW, Subgroup.map_iSup]
  have hsolvA : ∀ R : Subgroup A, R.Normal → Group.IsSolvable R → R = ⊥ :=
    fun R hRn hRs => by
      rw [eq_bot_iff, ← hCA, hW0]
      exact OutcomeLocal.le_centralizer_iSup fun i =>
        (LocalCores.component_solvable_centralizer hRs hRn.isSubnormal).1 _ (hcompA i)
  have hlayerA : layer A = W.map η := by
    refine le_antisymm (sSup_le fun Q hQ => ?_)
      (hW0 ▸ iSup_le fun i => LocalCores.component_le_layer (hcompA i))
    by_contra hQW
    have hc : ∀ i, ⁅(S i).map η, Q⁆ = ⊥ := fun i =>
      ((LocalCores.distinct_components_commute (hcompA i) hQ).resolve_left fun h =>
        hQW (h ▸ map_mono (hSW' i)))
    have hQbot : Q ≤ ⊥ := hCA ▸ hW0 ▸ OutcomeLocal.le_centralizer_iSup hc
    have : Nontrivial Q := LocalCores.isQuasisimple_nontrivial hQ.1
    exact (Subgroup.nontrivial_iff_ne_bot Q).mp this (le_bot_iff.mp hQbot)
  have hfitA : CFSG.fittingSubgroup A = ⊥ :=
    hsolvA _ CFSG.fittingSubgroup_normal inferInstance
  have hgFit : generalizedFitting A = W.map η := by
    rw [CFSG.generalizedFitting, hfitA, hlayerA, bot_sup_eq]
  have hOA : pPrimeCore 2 A = ⊥ := by
    have hodd' : Odd (Nat.card (pPrimeCore 2 A)) :=
      Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact hsolvA _ pPrimeCore_normal (Milestones.odd_order_solvable hodd')
  have hO2A : pCore 2 A = ⊥ := by
    have hp : IsPGroup 2 (pCore 2 A) := pCore_isPGroup
    have : Group.IsNilpotent (pCore 2 A) := hp.isNilpotent
    exact hsolvA _ pCore_normal inferInstance
  have hF := (hgen L hLW hLcl).1
  have hA0 : (⨆ g : A, conjugate (L.map η) g) = W.map η := by
    calc (⨆ g : A, conjugate (L.map η) g) = ⨆ f : F, conjugate (L.map η) (η f) :=
          (hη.iSup_comp _).symm
      _ = ⨆ f : F, (conjugate L f).map η :=
          iSup_congr fun f => (OutcomeLocal.map_conjugate η L f).symm
      _ = (⨆ f : F, conjugate L f).map η := (Subgroup.map_iSup η _).symm
      _ = W.map η := by rw [hF]
  have hWtA : ⁅W.map η, zpowers (η t)⁆ = W.map η := by
    rw [← MonoidHom.map_zpowers, ← map_commutator, hWt]
  have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have htK : t ∉ K := fun htK => by
    have := Subgroup.orderOf_dvd_natCard K htK
    rw [ht2] at this
    exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr this)
  have hηt : orderOf (η t) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ht2', map_one]
    · intro h
      apply htK
      rw [← hker]
      exact h
  have hstd : IsStandardSubgroup (L.map η) :=
    isStandardSubgroup_map_of_surjective η hη (by rw [hker]; exact hKodd) hWK'
      (by rw [hker, hKeq]) hLW hLstd
  have hCt : centralizer ({η t} : Set A) = (centralizer ({t} : Set F)).map η := by
    refine le_antisymm (fun y hy => ?_) (map_le_iff_le_comap.mpr fun x hx => ?_)
    · obtain ⟨f, rfl⟩ := hη y
      rw [mem_centralizer_singleton_iff] at hy
      have hf : f * t * f⁻¹ * t⁻¹ ∈ K := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hy]
        group
      obtain ⟨k, hk, hkf⟩ := OutcomeLocal.exists_mul_mem_centralizer_of_odd hKodd ht2' hf
      refine ⟨k * f, hkf, ?_⟩
      have hk' : k ∈ η.ker := by rw [hker]; exact hk
      rw [map_mul, MonoidHom.mem_ker.mp hk', one_mul]
    · rw [mem_comap, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        (mem_centralizer_singleton_iff.mp hx)]
  have hLtA : L.map η ≤ centralizer ({η t} : Set A) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (htL hl)]
  have hcompL : IsComponent ((L.map η).subgroupOf (centralizer ({η t} : Set A))) := by
    set Ct := centralizer ({t} : Set F) with hCt'
    set φ : Ct →* centralizer ({η t} : Set A) :=
      (MulEquiv.subgroupCongr hCt.symm).toMonoidHom.comp (η.subgroupMap Ct) with hφ
    have hφs : Function.Surjective φ :=
      (MulEquiv.subgroupCongr hCt.symm).surjective.comp (η.subgroupMap_surjective Ct)
    have hLφ : ¬ L.subgroupOf Ct ≤ φ.ker := fun h => by
      have : Nontrivial (L.subgroupOf Ct) := LocalCores.isQuasisimple_nontrivial hLt.1
      refine (Subgroup.nontrivial_iff_ne_bot _).mp this (eq_bot_iff.mpr fun x hx => ?_)
      have hx1 : η x = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp (h hx))
        exact this
      have : (x : F) ∈ W ⊓ η.ker := ⟨hLW (mem_subgroupOf.mp hx), hx1⟩
      rw [hWK', mem_bot] at this
      exact mem_bot.mpr (Subtype.ext this)
    have hmap : (L.subgroupOf Ct).map φ = (L.map η).subgroupOf (centralizer ({η t} : Set A)) := by
      ext y
      rw [mem_map, mem_subgroupOf, mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, mem_subgroupOf.mp hx, rfl⟩
      · rintro ⟨l, hl, hly⟩
        exact ⟨⟨l, htL hl⟩, mem_subgroupOf.mpr hl, Subtype.ext hly⟩
    rw [← hmap]
    exact ⟨LocalCores.isQuasisimple_map hLt.1 φ hLφ, hLt.2.map hφs⟩
  exact ⟨hKeq, hWK, hlayer, hF, hO2, ⟨eW, heW⟩, ⟨eL, heL⟩, hCA, hlayerA, hgFit, hfitA, hOA,
    hO2A, hA0, hWtA, hηt, hstd, hCt, hLtA, hcompL⟩

end CFSG.ComponentClassification.UnbalancedCorr
