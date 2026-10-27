module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Quasithin.Background.A1cRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Equiv MulAction Subgroup

open scoped Pointwise

private def altTenV₁ : alternatingGroup (Fin 10) :=
  ⟨Equiv.swap (0 : Fin 10) 1 * Equiv.swap 2 3,
    CFSG.Alternating.Multipliers.swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩

private def altTenV₂ : alternatingGroup (Fin 10) :=
  ⟨Equiv.swap (0 : Fin 10) 2 * Equiv.swap 1 3,
    CFSG.Alternating.Multipliers.swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩

private def altTenE₁ : alternatingGroup (Fin 10) :=
  ⟨Equiv.swap (0 : Fin 10) 2 * Equiv.swap 0 1,
    CFSG.Alternating.Multipliers.swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩

private def altTenE₂ : alternatingGroup (Fin 10) :=
  ⟨Equiv.swap (4 : Fin 10) 6 * Equiv.swap 4 5,
    CFSG.Alternating.Multipliers.swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩

private def altTenE₃ : alternatingGroup (Fin 10) :=
  ⟨Equiv.swap (7 : Fin 10) 9 * Equiv.swap 7 8,
    CFSG.Alternating.Multipliers.swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩

private def altTenV : Subgroup (alternatingGroup (Fin 10)) :=
  Subgroup.zpowers altTenV₁ ⊔ Subgroup.zpowers altTenV₂

private def altTenE : Subgroup (alternatingGroup (Fin 10)) :=
  (Subgroup.zpowers altTenE₁ ⊔ Subgroup.zpowers altTenE₂) ⊔ Subgroup.zpowers altTenE₃

private theorem orderOf_altTenV₁ : orderOf altTenV₁ = 2 :=
  orderOf_eq_prime (by decide) (by decide)

private theorem orderOf_altTenV₂ : orderOf altTenV₂ = 2 :=
  orderOf_eq_prime (by decide) (by decide)

private theorem orderOf_altTenE₁ : orderOf altTenE₁ = 3 :=
  orderOf_eq_prime (by decide) (by decide)

private theorem orderOf_altTenE₂ : orderOf altTenE₂ = 3 :=
  orderOf_eq_prime (by decide) (by decide)

private theorem orderOf_altTenE₃ : orderOf altTenE₃ = 3 :=
  orderOf_eq_prime (by decide) (by decide)

private theorem notMemZpowersOfOrderTwo {X : Type*} [Group X] [Finite X] [DecidableEq X]
    {x y : X}
    (hx : orderOf x = 2) (hy1 : y ≠ 1) (hyx : y ≠ x) : y ∉ Subgroup.zpowers x := by
  rw [mem_zpowers_iff_mem_range_orderOf, hx]
  intro hmem
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_range] at hk
  interval_cases k
  · exact hy1 (pow_zero x)
  · exact hyx (pow_one x)

private theorem altTen_mem_fixingSubgroup_singleton {x : alternatingGroup (Fin 10)}
    {p : Fin 10} (h : (x : Equiv.Perm (Fin 10)) p = p) :
    x ∈ fixingSubgroup (alternatingGroup (Fin 10)) ({p} : Set (Fin 10)) := by
  rw [mem_fixingSubgroup_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  simpa [Subgroup.smul_def, Perm.smul_def] using h

private theorem altTen_not_mem_fixingSubgroup_singleton {x : alternatingGroup (Fin 10)}
    {p : Fin 10} (h : (x : Equiv.Perm (Fin 10)) p ≠ p) :
    x ∉ fixingSubgroup (alternatingGroup (Fin 10)) ({p} : Set (Fin 10)) := by
  rw [mem_fixingSubgroup_iff]
  intro hx
  have hxp : (x : Equiv.Perm (Fin 10)) p = p := by
    simpa [Subgroup.smul_def, Perm.smul_def] using hx p (by simp)
  exact h hxp

private theorem altTen_not_mem_zpowers_of_moving {x y : alternatingGroup (Fin 10)}
    {p : Fin 10} (hx : (x : Equiv.Perm (Fin 10)) p = p)
    (hy : (y : Equiv.Perm (Fin 10)) p ≠ p) : y ∉ Subgroup.zpowers x := by
  intro hmem
  exact altTen_not_mem_fixingSubgroup_singleton hy
    (Subgroup.zpowers_le.mpr (altTen_mem_fixingSubgroup_singleton hx) hmem)

private theorem isElemAbelian_altTenV_and_card :
    CFSG.Open.IsElemAbelian 2 altTenV ∧ Nat.card ↥altTenV = 4 := by
  have hcomm : ∀ e ∈ Subgroup.zpowers altTenV₁, Commute e altTenV₂ := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ((commute_iff_eq _ _).2 (by decide)).zpow_left k
  have hnot : altTenV₂ ∉ Subgroup.zpowers altTenV₁ :=
    notMemZpowersOfOrderTwo orderOf_altTenV₁ (by decide) (by decide)
  have h := CFSG.Quasithin.exists_elemAbelian_sup_zpowers
    (p := 2) (E := Subgroup.zpowers altTenV₁) (y := altTenV₂)
    (CFSG.Open.isElemAbelian_zpowers (by decide : altTenV₁ ^ 2 = 1))
    orderOf_altTenV₂ hcomm hnot
  refine ⟨by simpa [altTenV] using h.1, ?_⟩
  rw [altTenV, h.2, Nat.card_zpowers, orderOf_altTenV₁]

private theorem isElemAbelian_altTenE_and_card :
    CFSG.Open.IsElemAbelian 3 altTenE ∧ Nat.card ↥altTenE = 27 := by
  have h12 : Commute altTenE₁ altTenE₂ :=
    (commute_iff_eq _ _).2 (by decide)
  have h13 : Commute altTenE₁ altTenE₃ :=
    (commute_iff_eq _ _).2 (by decide)
  have h23 : Commute altTenE₂ altTenE₃ :=
    (commute_iff_eq _ _).2 (by decide)
  have hA2cent : (Subgroup.zpowers altTenE₁ ⊔ Subgroup.zpowers altTenE₂) ≤
      Subgroup.centralizer (Subgroup.zpowers altTenE₃ : Set (alternatingGroup (Fin 10))) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (h13.zpow_right k).eq.symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (h23.zpow_right k).eq.symm
  have hcomm : ∀ e ∈ Subgroup.zpowers altTenE₁ ⊔ Subgroup.zpowers altTenE₂,
      Commute e altTenE₃ := by
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (hA2cent he) altTenE₃
      (Subgroup.mem_zpowers altTenE₃)).symm
  have hnot : altTenE₃ ∉ Subgroup.zpowers altTenE₁ ⊔ Subgroup.zpowers altTenE₂ := by
    intro hmem
    have hfix : Subgroup.zpowers altTenE₁ ⊔ Subgroup.zpowers altTenE₂ ≤
        fixingSubgroup (alternatingGroup (Fin 10)) ({7} : Set (Fin 10)) :=
      sup_le (Subgroup.zpowers_le.mpr
        (altTen_mem_fixingSubgroup_singleton (by decide)))
        (Subgroup.zpowers_le.mpr
          (altTen_mem_fixingSubgroup_singleton (by decide)))
    exact altTen_not_mem_fixingSubgroup_singleton (by decide) (hfix hmem)
  have hnot12 : altTenE₂ ∉ Subgroup.zpowers altTenE₁ :=
    altTen_not_mem_zpowers_of_moving (p := 4) (by decide) (by decide)
  have hcomm12 : ∀ e ∈ Subgroup.zpowers altTenE₁, Commute e altTenE₂ := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact h12.zpow_left k
  have hA2ea : CFSG.Open.IsElemAbelian 3
      (Subgroup.zpowers altTenE₁ ⊔ Subgroup.zpowers altTenE₂) := by
    have hA1 := CFSG.Open.isElemAbelian_zpowers (by decide : altTenE₁ ^ 3 = 1)
    have hA2 := CFSG.Quasithin.exists_elemAbelian_sup_zpowers
      (p := 3) (E := Subgroup.zpowers altTenE₁) (y := altTenE₂)
      hA1 orderOf_altTenE₂ hcomm12 hnot12
    simpa using hA2.1
  have hcard2 : Nat.card ↥(Subgroup.zpowers altTenE₁ ⊔ Subgroup.zpowers altTenE₂) = 9 := by
    have hA1 := CFSG.Open.isElemAbelian_zpowers (by decide : altTenE₁ ^ 3 = 1)
    have h := CFSG.Quasithin.exists_elemAbelian_sup_zpowers
      (p := 3) (E := Subgroup.zpowers altTenE₁) (y := altTenE₂)
      hA1 orderOf_altTenE₂ hcomm12 hnot12
    rw [h.2, Nat.card_zpowers, orderOf_altTenE₁]
  have hA2 := CFSG.Quasithin.exists_elemAbelian_sup_zpowers
    (p := 3) (E := Subgroup.zpowers altTenE₁ ⊔ Subgroup.zpowers altTenE₂) (y := altTenE₃)
    hA2ea orderOf_altTenE₃ hcomm hnot
  refine ⟨by simpa [altTenE] using hA2.1, ?_⟩
  rw [altTenE, hA2.2, hcard2]

private theorem altTenE₁_mem_normalizer_altTenV :
    altTenE₁ ∈ Subgroup.normalizer (altTenV : Set (alternatingGroup (Fin 10))) := by
  have hV : altTenV = Subgroup.zpowers altTenV₁ ⊔ Subgroup.zpowers altTenV₂ := rfl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [hV, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · change (MulAut.conj altTenE₁) altTenV₁ ∈
        Subgroup.zpowers altTenV₁ ⊔ Subgroup.zpowers altTenV₂
      rw [MulAut.conj_apply,
        show altTenE₁ * altTenV₁ * altTenE₁⁻¹ = altTenV₁ * altTenV₂ from by decide]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers altTenV₁)
        (Subgroup.mem_zpowers altTenV₂)
    · change (MulAut.conj altTenE₁) altTenV₂ ∈
        Subgroup.zpowers altTenV₁ ⊔ Subgroup.zpowers altTenV₂
      rw [MulAut.conj_apply,
        show altTenE₁ * altTenV₂ * altTenE₁⁻¹ = altTenV₁ from by decide]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers altTenV₁)
  · rw [Subgroup.card_map_of_injective (K := altTenV) (MulAut.conj altTenE₁).injective]

private theorem altTenE₂_mem_normalizer_altTenV :
    altTenE₂ ∈ Subgroup.normalizer (altTenV : Set (alternatingGroup (Fin 10))) := by
  have hV : altTenV = Subgroup.zpowers altTenV₁ ⊔ Subgroup.zpowers altTenV₂ := rfl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [hV, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · change (MulAut.conj altTenE₂) altTenV₁ ∈
        Subgroup.zpowers altTenV₁ ⊔ Subgroup.zpowers altTenV₂
      rw [MulAut.conj_apply,
        show altTenE₂ * altTenV₁ * altTenE₂⁻¹ = altTenV₁ from by decide]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers altTenV₁)
    · change (MulAut.conj altTenE₂) altTenV₂ ∈
        Subgroup.zpowers altTenV₁ ⊔ Subgroup.zpowers altTenV₂
      rw [MulAut.conj_apply,
        show altTenE₂ * altTenV₂ * altTenE₂⁻¹ = altTenV₂ from by decide]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers altTenV₂)
  · rw [Subgroup.card_map_of_injective (K := altTenV) (MulAut.conj altTenE₂).injective]

private theorem altTenE₃_mem_normalizer_altTenV :
    altTenE₃ ∈ Subgroup.normalizer (altTenV : Set (alternatingGroup (Fin 10))) := by
  have hV : altTenV = Subgroup.zpowers altTenV₁ ⊔ Subgroup.zpowers altTenV₂ := rfl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [hV, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · change (MulAut.conj altTenE₃) altTenV₁ ∈
        Subgroup.zpowers altTenV₁ ⊔ Subgroup.zpowers altTenV₂
      rw [MulAut.conj_apply,
        show altTenE₃ * altTenV₁ * altTenE₃⁻¹ = altTenV₁ from by decide]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers altTenV₁)
    · change (MulAut.conj altTenE₃) altTenV₂ ∈
        Subgroup.zpowers altTenV₁ ⊔ Subgroup.zpowers altTenV₂
      rw [MulAut.conj_apply,
        show altTenE₃ * altTenV₂ * altTenE₃⁻¹ = altTenV₂ from by decide]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers altTenV₂)
  · rw [Subgroup.card_map_of_injective (K := altTenV) (MulAut.conj altTenE₃).injective]

private theorem altTenE_le_normalizer_altTenV :
    altTenE ≤ Subgroup.normalizer (altTenV : Set (alternatingGroup (Fin 10))) := by
  rw [altTenE]
  exact sup_le (sup_le (Subgroup.zpowers_le.mpr altTenE₁_mem_normalizer_altTenV)
    (Subgroup.zpowers_le.mpr altTenE₂_mem_normalizer_altTenV))
    (Subgroup.zpowers_le.mpr altTenE₃_mem_normalizer_altTenV)

private theorem isQuasisimple_alternatingTen :
    CFSG.IsQuasisimple (alternatingGroup (Fin 10)) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    ⟨altTenE₁, altTenV₁, by decide⟩).1

private theorem altTen_four_le_of_injective {G : Type} [Group G] [Finite G]
    (ψ : alternatingGroup (Fin 10) →* G) (hψ : Function.Injective ψ) {z : G}
    (hz : orderOf z = 3) (hznot : z ∉ altTenE.map ψ)
    (hzcomm : ∀ e ∈ altTenE.map ψ, Commute e z)
    (hznorm : z ∈ Subgroup.normalizer (altTenV.map ψ : Set G)) :
    4 ≤ CFSG.Open.rankThreeLocalRank 3 G := by
  let V : Subgroup G := altTenV.map ψ
  let E : Subgroup G := altTenE.map ψ
  have hVcard : Nat.card V = 4 := by
    change Nat.card ↥(altTenV.map ψ) = 4
    rw [Subgroup.card_map_of_injective (K := altTenV) hψ,
      isElemAbelian_altTenV_and_card.2]
  have hVea : CFSG.Open.IsElemAbelian 2 V :=
    isElemAbelian_altTenV_and_card.1.map ψ
  have hVne : V ≠ ⊥ := by
    intro h
    have h1 : Nat.card V = 1 := by rw [h, Subgroup.card_bot]
    rw [h1] at hVcard
    norm_num at hVcard
  have hVp : IsPGroup 2 V := hVea.isPGroup
  have hNlocal : CFSG.Open.IsTwoLocal (Subgroup.normalizer (V : Set G)) :=
    ⟨V, hVne, hVp, rfl⟩
  have hEea : CFSG.Open.IsElemAbelian 3 E := isElemAbelian_altTenE_and_card.1.map ψ
  have hEcard : Nat.card E = 27 := by
    change Nat.card ↥(altTenE.map ψ) = 27
    rw [Subgroup.card_map_of_injective (K := altTenE) hψ,
      isElemAbelian_altTenE_and_card.2]
  have hEnorm : E ≤ Subgroup.normalizer (V : Set G) := by
    have hmap := Subgroup.map_mono (f := ψ) altTenE_le_normalizer_altTenV
    exact hmap.trans (Subgroup.le_normalizer_map ψ)
  have hE81 := CFSG.Quasithin.exists_elemAbelian_sup_zpowers
    (p := 3) (E := E) (y := z) hEea hz hzcomm hznot
  have hE81card : Nat.card ↥(E ⊔ Subgroup.zpowers z) = 3 ^ 4 := by
    rw [hE81.2, hEcard]
    norm_num
  have hE81norm : E ⊔ Subgroup.zpowers z ≤ Subgroup.normalizer (V : Set G) :=
    sup_le hEnorm (Subgroup.zpowers_le.mpr hznorm)
  have h4 : 4 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (V : Set G)) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE81norm hE81.1 hE81card
  exact h4.trans (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_localRank
    3 (by norm_num) (Subgroup.normalizer (V : Set G)) hNlocal)

private theorem altTen_z_not_mem_of_mulEquiv {G : Type} [Group G] {J : Subgroup G}
    (eJ : ↥J ≃* alternatingGroup (Fin 10)) {z : G}
    (hz : orderOf z = 3) (hzJ : ∀ j ∈ J, z * j = j * z) : z ∉ J := by
  intro hzmem
  have hcenterA : Subgroup.center (alternatingGroup (Fin 10)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  have hcent : eJ ⟨z, hzmem⟩ ∈ Subgroup.center (alternatingGroup (Fin 10)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨j, rfl⟩ := eJ.surjective a
    have h1 : (⟨j, j.2⟩ : ↥J) * ⟨z, hzmem⟩ = ⟨z, hzmem⟩ * ⟨j, j.2⟩ := by
      ext
      exact (hzJ j j.2).symm
    simpa using congrArg eJ h1
  have hbot : eJ ⟨z, hzmem⟩ ∈ (⊥ : Subgroup (alternatingGroup (Fin 10))) :=
    hcenterA ▸ hcent
  have hz1J : (⟨z, hzmem⟩ : ↥J) = 1 := eJ.injective (by simpa using hbot)
  have hz1 : z = 1 := congrArg Subtype.val hz1J
  rw [hz1, orderOf_one] at hz
  norm_num at hz

theorem four_le_localRank_of_altTen (hKSM : CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt)
    {G : Type} [Group G] [Finite G] {J : Subgroup G} (hJ : Group.IsPerfect ↥J)
    (φ : ↥J →* alternatingGroup (Fin 10)) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center ↥J) (hodd : Odd (Nat.card φ.ker)) {z : G}
    (hz : orderOf z = 3) (hzJ : ∀ j ∈ J, z * j = j * z) :
    4 ≤ CFSG.Open.rankThreeLocalRank 3 G := by
  let A := alternatingGroup (Fin 10)
  haveI : Finite ↥J := Subtype.finite
  have hAq : CFSG.IsQuasisimple A := isQuasisimple_alternatingTen
  have hJq : CFSG.IsQuasisimple ↥J :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hJ φ hφ hker).mpr hAq
  have hQJ : CFSG.Open.IsQuasisimple ↥J := ⟨hJq.1.commutator_eq_top, hJq.2.1⟩
  have hcenterA : Subgroup.center A = ⊥ := alternatingGroup.center_eq_bot (by norm_num)
  have hcen : Subgroup.center ↥J = φ.ker := by
    have h := CFSG.LocalCores.comap_center_eq_of_perfect hJ φ hφ hker
    rw [hcenterA, MonoidHom.comap_bot] at h
    exact h.symm
  have hodd' : Odd (Nat.card (Subgroup.center ↥J)) := by rwa [hcen]
  have hcenterCard : Nat.card (Subgroup.center ↥J) = 1 :=
    (hKSM ↥J hQJ 10 ⟨(QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩ hodd').2 (by norm_num)
  have hkerBot : φ.ker = ⊥ := by
    rw [← hcen]
    exact Subgroup.card_eq_one.mp hcenterCard
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerBot
  let eJ : ↥J ≃* A := MulEquiv.ofBijective φ ⟨hφinj, hφ⟩
  let ψ : A →* G := J.subtype.comp eJ.symm.toMonoidHom
  have hψinj : Function.Injective ψ := J.subtype_injective.comp eJ.symm.injective
  have hznotJ : z ∉ J := altTen_z_not_mem_of_mulEquiv eJ hz hzJ
  have hEJ : altTenE.map ψ ≤ J := by
    rintro x ⟨a, ha, rfl⟩
    exact (eJ.symm a).2
  have hVJ : altTenV.map ψ ≤ J := by
    rintro x ⟨a, ha, rfl⟩
    exact (eJ.symm a).2
  have hznotE : z ∉ altTenE.map ψ := fun h => hznotJ (hEJ h)
  have hzcomm : ∀ e ∈ altTenE.map ψ, Commute e z := by
    intro e he
    exact (hzJ e (hEJ he)).symm
  have hzcent : z ∈ Subgroup.centralizer (altTenV.map ψ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hzJ v (hVJ hv)).symm
  have hznorm : z ∈ Subgroup.normalizer (altTenV.map ψ : Set G) :=
    Subgroup.centralizer_le_normalizer _ hzcent
  exact altTen_four_le_of_injective ψ hψinj hz hznotE hzcomm hznorm
