module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThreeCtx
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11TwoSetThree
import CFSG.Permutation.OrderThreeCentralizer
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableNormalCyclic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThree

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

variable {G : Type} [Group G] [Finite G] {M H E Q : Subgroup G}

namespace Ctx

variable (c : Ctx G M H E Q)

theorem card_support_ne_nine {a : G} (haK : a ∈ kSub 3 M H) (ha : orderOf a = 3)
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(kSub 3 M H ⊓ Subgroup.centralizer ({a} : Set G))) :
    ((c.φ ⟨a, haK⟩ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card ≠ 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hs
  apply hns
  let K : Subgroup G := kSub 3 M H
  let D : Subgroup G := Subgroup.centralizer ({a} : Set G)
  let φD : ↥(D.subgroupOf K) →* alternatingGroup (Fin 11) := c.φ.comp (D.subgroupOf K).subtype
  have hmap : (D.subgroupOf K).map c.φ =
      Subgroup.centralizer ({c.φ ⟨a, haK⟩} : Set (alternatingGroup (Fin 11))) :=
    c.map_φ_centralizer_singleton haK ha
  have hsolv : IsSolvable ↥(Subgroup.centralizer
      ({c.φ ⟨a, haK⟩} : Set (alternatingGroup (Fin 11)))) :=
    CFSG.Permutation.isSolvable_centralizer_alternatingGroup_of_card_support_eq_nine
      (c.orderOf_φ ha) hs
  have hrange : φD.range =
      Subgroup.centralizer ({c.φ ⟨a, haK⟩} : Set (alternatingGroup (Fin 11))) := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
    exact hmap
  have hker_le : φD.ker.map (D.subgroupOf K).subtype ≤ CFSG.pPrimeCore 3 ↥K := by
    rintro z ⟨y, hy, rfl⟩
    rw [← c.ker_φ]
    exact hy
  have hcop : Nat.Coprime 3 (Nat.card ↥φD.ker) := by
    rw [Nat.prime_three.coprime_iff_not_dvd]
    intro h3
    apply c.not_three_dvd_card_pPrimeCore
    rw [← Subgroup.card_map_of_injective (D.subgroupOf K).subtype_injective] at h3
    exact h3.trans (Subgroup.card_dvd_of_le hker_le)
  haveI : Group.IsSolvable ↥φD.range := by rw [hrange]; exact hsolv
  have hQ : Group.IsSolvable (↥(D.subgroupOf K) ⧸ φD.ker) :=
    Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientKerEquivRange φD).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivRange φD).symm.surjective
  have hpsD : CFSG.HallHigman.IsPSolvable 3 ↥(D.subgroupOf K) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.isPSolvable_of_normal_coprime_quotient_solvable
      φD.ker hcop hQ
  have hsub : D.subgroupOf K = (K ⊓ D).subgroupOf K := by
    ext z
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨z.2, h⟩, fun h => h.2⟩
  exact QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ D ≤ K)) (hsub ▸ hpsD)

theorem centralizer_not_le {a : G} (ha : a ∈ kSub 3 M H ⊓ M) (ha3 : orderOf a = 3)
    (hs : ((c.φ ⟨a, ha.1⟩ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card ≤ 6) :
    ¬ Subgroup.centralizer ({a} : Set G) ≤ M := by
  intro hCM
  have hφS : c.φ ⟨a, ha.1⟩ ∈ a11TwoSetStab 9 10 := (c.mem_M_iff ⟨a, ha.1⟩).1 ha.2
  obtain ⟨g, hgC, hgS⟩ :=
    exists_mem_centralizer_not_mem_a11TwoSetStab hφS (c.orderOf_φ ha3) hs
  have hg : g ∈ ((Subgroup.centralizer ({a} : Set G)).subgroupOf (kSub 3 M H)).map c.φ := by
    rw [c.map_φ_centralizer_singleton ha.1 ha3]
    exact hgC
  obtain ⟨t, ht, htg⟩ := Subgroup.mem_map.mp hg
  have htM : (t : G) ∈ M := hCM (Subgroup.mem_subgroupOf.mp ht)
  have hmem : c.φ t ∈ a11TwoSetStab 9 10 := (c.mem_M_iff t).1 htM
  rw [htg] at hmem
  exact hgS hmem

private lemma exists_elem_E (c : Ctx G M H E Q) :
    ∃ e : G, e ∈ E ∧ e ≠ 1 ∧ orderOf e = 3 ∧ e ∈ kSub 3 M H ⊓ M := by
  have hcard : 1 < Nat.card E := by rw [c.choice.card]; norm_num
  haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨e, he1⟩ := exists_ne (1 : ↥E)
  have heG1 : (e : G) ≠ 1 := fun h => he1 (Subtype.ext (by simpa using h))
  refine ⟨(e : G), e.2, heG1, ?_, c.E_le e.2⟩
  exact orderOf_eq_prime (c.choice.elem.2 e e.2) heG1

private lemma centralizer_φ_le_stab (c : Ctx G M H E Q) {d : G} (hdK : d ∈ kSub 3 M H)
    (hd : orderOf d = 3) (hC : Subgroup.centralizer ({d} : Set G) ≤ M) :
    Subgroup.centralizer ({c.φ ⟨d, hdK⟩} : Set (alternatingGroup (Fin 11))) ≤
      a11TwoSetStab 9 10 := by
  rw [← c.map_φ_centralizer_singleton hdK hd]
  rintro _ ⟨t, ht, rfl⟩
  exact (c.mem_M_iff t).1 (hC (Subgroup.mem_subgroupOf.mp ht))

private lemma card_support_eq_nine_of_centralizer_le_Ctx (c : Ctx G M H E Q) {d : G}
    (hdK : d ∈ kSub 3 M H) (hd : orderOf d = 3)
    (hC : Subgroup.centralizer ({d} : Set G) ≤ M) :
    ((c.φ ⟨d, hdK⟩ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 9 :=
  CFSG.LocalAnalysis.AGL81TheoremCD.Section14.card_support_eq_nine_of_centralizer_le
    ((c.mem_M_iff ⟨d, hdK⟩).1 (hC (Subgroup.mem_centralizer_singleton_iff.mpr rfl)))
    (c.orderOf_φ hd) (centralizer_φ_le_stab c hdK hd hC)

private lemma isSylowOf_zpowers_sup_pPrimeCore (c : Ctx G M H E Q) {z : ↥(kSub 3 M H)}
    (hz : orderOf z = 3) :
    CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers z)
      (CFSG.pPrimeCore 3 ↥(kSub 3 M H) ⊔ Subgroup.zpowers z) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥(kSub 3 M H) := CFSG.pPrimeCore 3 ↥(kSub 3 M H)
  have hO : ¬ 3 ∣ Nat.card ↥O := c.not_three_dvd_card_pPrimeCore
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_sup_right, ?_, ?_⟩
  · rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hz, pow_one]⟩
  have hrel : (Subgroup.zpowers z).relIndex (O ⊔ Subgroup.zpowers z) =
      (Subgroup.zpowers z).relIndex O :=
    CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal O (Subgroup.zpowers z)
  have hbot : Subgroup.zpowers z ⊓ O = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have hdvd : Nat.card ↥(Subgroup.zpowers z ⊓ O) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_left : Subgroup.zpowers z ⊓ O ≤ Subgroup.zpowers z)
      rwa [Nat.card_zpowers, hz] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact h1
    · exfalso
      have hdvdO : Nat.card ↥(Subgroup.zpowers z ⊓ O) ∣ Nat.card ↥O :=
        Subgroup.card_dvd_of_le inf_le_right
      rw [h3] at hdvdO
      exact hO hdvdO
  have hrelO : (Subgroup.zpowers z).relIndex O = Nat.card ↥O := by
    rw [← Subgroup.inf_relIndex_right (H := Subgroup.zpowers z) (K := O), hbot,
      Subgroup.relIndex_bot_left]
  rw [hrel, hrelO]
  exact hO

private lemma exists_conj_mem_zpowers_of_mem_pPrimeCore (c : Ctx G M H E Q) {e y : G}
    (heK : e ∈ kSub 3 M H) (heM : e ∈ M) (hyK : y ∈ kSub 3 M H)
    (he3 : orderOf e = 3) (hy3 : orderOf y = 3)
    (hyO : (⟨y, hyK⟩ : ↥(kSub 3 M H)) * (⟨e, heK⟩ : ↥(kSub 3 M H))⁻¹ ∈
      CFSG.pPrimeCore 3 ↥(kSub 3 M H)) :
    ∃ w : G, w ∈ M ∧ w⁻¹ * y * w ∈ Subgroup.zpowers e := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let eK : ↥K := ⟨e, heK⟩
  let yK : ↥K := ⟨y, hyK⟩
  have heK3 : orderOf eK = 3 := by
    rw [← Subgroup.orderOf_coe]
    simpa [eK] using he3
  have hyK3 : orderOf yK = 3 := by
    rw [← Subgroup.orderOf_coe]
    simpa [yK] using hy3
  have hyO' : yK * eK⁻¹ ∈ O := hyO
  have heW : eK ∈ O ⊔ Subgroup.zpowers eK := Subgroup.mem_sup_right (Subgroup.mem_zpowers eK)
  have hyW : yK ∈ O ⊔ Subgroup.zpowers eK := by
    have h : yK = (yK * eK⁻¹) * eK := by group
    rw [h]
    exact (O ⊔ Subgroup.zpowers eK).mul_mem (Subgroup.mem_sup_left hyO') heW
  have hWy : O ⊔ Subgroup.zpowers eK = O ⊔ Subgroup.zpowers yK := by
    apply le_antisymm
    · apply sup_le le_sup_left
      apply Subgroup.zpowers_le.mpr
      have h : eK = (yK * eK⁻¹)⁻¹ * yK := by group
      rw [h]
      exact (O ⊔ Subgroup.zpowers yK).mul_mem (Subgroup.mem_sup_left (O.inv_mem hyO'))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers yK))
    · apply sup_le le_sup_left
      apply Subgroup.zpowers_le.mpr
      exact hyW
  have hSylE : CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers eK)
      (O ⊔ Subgroup.zpowers eK) := isSylowOf_zpowers_sup_pPrimeCore c heK3
  have hSylY : CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers yK)
      (O ⊔ Subgroup.zpowers eK) := by
    rw [hWy]
    exact isSylowOf_zpowers_sup_pPrimeCore c hyK3
  obtain ⟨w, hwW, hconj⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj hSylE hSylY
  have hWM : (O ⊔ Subgroup.zpowers eK).map K.subtype ≤ M := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · simpa [K, O] using c.pPrimeCore_map_le
    · rw [MonoidHom.map_zpowers]
      exact Subgroup.zpowers_le.mpr heM
  have hwM : (w : G) ∈ M := hWM (Subgroup.mem_map.mpr ⟨w, hwW, rfl⟩)
  refine ⟨(w : G), hwM, ?_⟩
  have hy_in : w⁻¹ * yK * w ∈ Subgroup.zpowers eK :=
    (hconj yK).mp (Subgroup.mem_zpowers yK)
  have hmem : ((w⁻¹ * yK * w : ↥K) : G) ∈ Subgroup.zpowers e := by
    have h := Subgroup.mem_map_of_mem K.subtype hy_in
    rw [MonoidHom.map_zpowers] at h
    simpa [eK] using h
  simpa [eK, yK] using hmem

private lemma exists_conj_eq_or_inv_of_mem_pPrimeCore (c : Ctx G M H E Q) {e y : G}
    (heK : e ∈ kSub 3 M H) (heM : e ∈ M) (hyK : y ∈ kSub 3 M H)
    (he3 : orderOf e = 3) (hy3 : orderOf y = 3)
    (hyO : (⟨y, hyK⟩ : ↥(kSub 3 M H)) * (⟨e, heK⟩ : ↥(kSub 3 M H))⁻¹ ∈
      CFSG.pPrimeCore 3 ↥(kSub 3 M H)) :
    ∃ w : G, w ∈ M ∧ (w⁻¹ * y * w = e ∨ w⁻¹ * y * w = e⁻¹) := by
  obtain ⟨w, hwM, hmem⟩ := exists_conj_mem_zpowers_of_mem_pPrimeCore c heK heM hyK he3 hy3 hyO
  refine ⟨w, hwM, ?_⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hje : e ^ j = w⁻¹ * y * w := by simpa using hj
  have he3n : e ^ (3 : ℕ) = 1 := by
    have h := pow_orderOf_eq_one e
    rwa [he3] at h
  have hred : e ^ j = e ^ (j % (3 : ℤ)) := by
    simpa using zpow_eq_zpow_emod' j he3n
  have hj3 : e ^ j ≠ 1 := by
    rw [hje]
    intro h1
    have hord : orderOf (w⁻¹ * y * w) = 3 := by
      have h := MulEquiv.orderOf_eq (MulAut.conj w⁻¹) y
      simpa [MulAut.conj_apply, hy3] using h
    rw [h1, orderOf_one] at hord
    norm_num at hord
  have he2 : e ^ 2 = e⁻¹ := by
    have h3 : e ^ 2 * e = 1 := by
      have h := pow_orderOf_eq_one e
      rw [he3] at h
      simpa [pow_succ] using h
    calc e ^ 2 = (e ^ 2 * e) * e⁻¹ := by group
      _ = 1 * e⁻¹ := by rw [h3]
      _ = e⁻¹ := one_mul _
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h0 | h1 | h2
  · exact absurd (by rw [hred, h0]; norm_num) hj3
  · left
    rw [← hje, hred, h1]
    norm_num
  · right
    rw [← hje, hred, h2]
    simpa using he2

private lemma exists_conj_eq_or_inv_card_support_eq_nine (c : Ctx G M H E Q) {x : G}
    (hx : x ∈ kSub 3 M H ⊓ M) (hx3 : orderOf x = 3)
    (hs : ((c.φ ⟨x, hx.1⟩ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 9) :
    ∃ e m : G, e ∈ E ∧ m ∈ M ∧ Subgroup.centralizer ({e} : Set G) ≤ M ∧
      (m * x * m⁻¹ = e ∨ m * x * m⁻¹ = e⁻¹) := by
  classical
  obtain ⟨e, heE, he1, he3, heKM⟩ := exists_elem_E c
  have heK : e ∈ kSub 3 M H := heKM.1
  have heM : e ∈ M := heKM.2
  have hCe : Subgroup.centralizer ({e} : Set G) ≤ M :=
    c.choice.hypCGen.centralizer_le_of_mem heE he1
  have hφeS : c.φ ⟨e, heK⟩ ∈ a11TwoSetStab 9 10 := (c.mem_M_iff ⟨e, heK⟩).1 heM
  have hφe9 : ((c.φ ⟨e, heK⟩ : alternatingGroup (Fin 11)) :
      Equiv.Perm (Fin 11)).support.card = 9 :=
    card_support_eq_nine_of_centralizer_le_Ctx c heK he3 hCe
  have hφxS : c.φ ⟨x, hx.1⟩ ∈ a11TwoSetStab 9 10 := (c.mem_M_iff ⟨x, hx.1⟩).1 hx.2
  obtain ⟨g, hgS, hg⟩ := exists_conj_eq_of_card_support_eq hφxS hφeS (c.orderOf_φ hx3)
    (c.orderOf_φ he3) (by rw [hs, hφe9])
  obtain ⟨k, hk_inf, hkg⟩ : ∃ k : ↥(kSub 3 M H),
      k ∈ (kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H) ∧ c.φ k = g := by
    have hg' : g ∈ ((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map c.φ := by
      rw [c.map_φ_inf]; exact hgS
    exact Subgroup.mem_map.mp hg'
  have hkM : (k : G) ∈ M := (Subgroup.mem_subgroupOf.mp hk_inf).2
  let y : G := (k : G) * x * (k : G)⁻¹
  have hyK : y ∈ kSub 3 M H :=
    (kSub 3 M H).mul_mem ((kSub 3 M H).mul_mem k.2 hx.1) ((kSub 3 M H).inv_mem k.2)
  have hy3 : orderOf y = 3 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj (k : G)) x
    simpa [y, MulAut.conj_apply] using h.trans hx3
  have hφy : c.φ ⟨y, hyK⟩ = c.φ ⟨e, heK⟩ := by
    have h1 : (⟨y, hyK⟩ : ↥(kSub 3 M H)) = k * ⟨x, hx.1⟩ * k⁻¹ := by
      ext
      simp [y]
    rw [h1, map_mul, map_mul, map_inv, hkg]
    exact hg
  have hyO : (⟨y, hyK⟩ : ↥(kSub 3 M H)) * (⟨e, heK⟩ : ↥(kSub 3 M H))⁻¹ ∈
      CFSG.pPrimeCore 3 ↥(kSub 3 M H) := by
    rw [← c.ker_φ, MonoidHom.mem_ker, map_mul, map_inv, hφy]
    exact mul_inv_cancel _
  obtain ⟨w, hwM, hw⟩ := exists_conj_eq_or_inv_of_mem_pPrimeCore c heK heM hyK he3 hy3 hyO
  refine ⟨e, w⁻¹ * (k : G), heE, M.mul_mem (M.inv_mem hwM) hkM, hCe, ?_⟩
  have hm : (w⁻¹ * (k : G)) * x * (w⁻¹ * (k : G))⁻¹ = w⁻¹ * y * w := by
    simp only [y]
    group
  rcases hw with hw | hw
  · left
    rw [hm, hw]
  · right
    rw [hm, hw]

theorem centralizer_le_of_card_support_eq_nine {x : G} (hx : x ∈ kSub 3 M H ⊓ M)
    (hx3 : orderOf x = 3)
    (hs : ((c.φ ⟨x, hx.1⟩ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 9) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  obtain ⟨e, m, -, hmM, hCe, hm⟩ := exists_conj_eq_or_inv_card_support_eq_nine c hx hx3 hs
  intro z hz
  have hzx : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hz
  have hzc : m * z * m⁻¹ ∈ Subgroup.centralizer ({e} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : (m * z * m⁻¹) * (m * x * m⁻¹) = (m * x * m⁻¹) * (m * z * m⁻¹) := by
      rw [show m * z * m⁻¹ * (m * x * m⁻¹) = m * (z * x) * m⁻¹ by group,
        show m * x * m⁻¹ * (m * z * m⁻¹) = m * (x * z) * m⁻¹ by group, hzx]
    rcases hm with hm | hm
    · rw [hm] at hcomm
      exact hcomm
    · rw [hm] at hcomm
      have h3 : e * (m * z * m⁻¹) = (m * z * m⁻¹) * e := by
        simpa [mul_assoc] using congrArg (fun t => e * t * e) hcomm
      exact h3.symm
  have h1 : m * z * m⁻¹ ∈ M := hCe hzc
  have h2 : z = m⁻¹ * (m * z * m⁻¹) * m := by group
  rw [h2]
  exact M.mul_mem (M.mul_mem (M.inv_mem hmM) h1) hmM

end Ctx

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThree
