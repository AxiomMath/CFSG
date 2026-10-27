module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Simple
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102U1
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102U2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L102

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open scoped commutatorElement

section Sub

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreOf_le_of_subnormalIn {L M : Subgroup G} (hLM : L ≤ M)
    (h : (L.subgroupOf M).IsSubnormal) : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 M := by
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal h
  rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf hLM]
  exact Subgroup.map_mono h1

omit [Finite G] in
theorem subnormal_dres_inf {H₁ H I : Subgroup G} {z t : G} (hHH₁ : H ≤ H₁)
    (hH₁n : H₁ ≤ normalizer (H : Set G))
    (hIU : I ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G))
    (hCI : ∀ c ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G),
      c ∈ normalizer (I : Set G)) :
    ((dres (H ⊓ I)).subgroupOf (H₁ ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G))).IsSubnormal := by
  have hAY : H ⊓ I ≤ H₁ ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) :=
    fun x hx => ⟨⟨hHH₁ hx.1, (hIU hx.2).1⟩, (hIU hx.2).2⟩
  have hYA : H₁ ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer ((H ⊓ I : Subgroup G) : Set G) := fun c hc =>
    normalizer_inf_of (hH₁n hc.1.1) (hCI c ⟨hc.1.2, hc.2⟩)
  have hJA : dres (H ⊓ I) ≤ H ⊓ I := dres_le _
  have hAJ : H ⊓ I ≤ normalizer ((dres (H ⊓ I) : Subgroup G) : Set G) := fun a ha =>
    normalizer_le_normalizer_dres _ (le_normalizer ha)
  have hS₁ : ((H ⊓ I).subgroupOf (H₁ ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAY).mpr hYA
  have hle : (dres (H ⊓ I)).subgroupOf (H₁ ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) ≤
      (H ⊓ I).subgroupOf (H₁ ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) :=
    fun x hx => hJA hx
  refine Subgroup.IsSubnormal.step _ ((H ⊓ I).subgroupOf (H₁ ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)))
    hle hS₁.isSubnormal ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hx' := Subgroup.mem_normalizer_iff.mp (hAJ hx) (h : G)
  exact hx'

end Sub


section ThreeSub

variable {G : Type*} [Group G]

theorem commutator_mem_of_double {J N : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hN : J ≤ normalizer (N : Set G)) {a : G} (haJ : a ∈ J)
    (H : ∀ y ∈ J, ∀ y' ∈ J, ⁅⁅a, y⁆, y'⁆ ∈ N) : ∀ y ∈ J, ⁅a, y⁆ ∈ N := by
  have hnorm : (N.subgroupOf J).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ
  have hperf' : Group.IsPerfect (↥J ⧸ N.subgroupOf J) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (N.subgroupOf J))
      (QuotientGroup.mk'_surjective _)
  let π : ↥J →* ↥J ⧸ N.subgroupOf J := QuotientGroup.mk' (N.subgroupOf J)
  let aJ : ↥J := ⟨a, haJ⟩
  have hcoe : ∀ u v : ↥J, ((⁅u, v⁆ : ↥J) : G) = ⁅(u : G), (v : G)⁆ := fun u v => rfl
  have hcent : ∀ y : ↥J, ⁅π aJ, π y⁆ ∈ Subgroup.center (↥J ⧸ N.subgroupOf J) := by
    intro y
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 : ⁅⁅aJ, y⁆, g⁆ ∈ N.subgroupOf J := by
      rw [Subgroup.mem_subgroupOf, hcoe, hcoe]
      exact H y y.2 g g.2
    have h2 : π ⁅⁅aJ, y⁆, g⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_commutatorElement, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  let φ : (↥J ⧸ N.subgroupOf J) →* Subgroup.center (↥J ⧸ N.subgroupOf J) :=
    MonoidHom.mk' (fun y => ⟨⁅π aJ, y⁆, by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      exact hcent y⟩) (by
      intro y y'
      apply Subtype.ext
      have hc' : ⁅π aJ, y'⁆ ∈ Subgroup.center (↥J ⧸ N.subgroupOf J) := by
        obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y'
        exact hcent y'
      have hy := Subgroup.mem_center_iff.mp hc' y
      show ⁅π aJ, y * y'⁆ = ⁅π aJ, y⁆ * ⁅π aJ, y'⁆
      have : ⁅π aJ, y * y'⁆ = ⁅π aJ, y⁆ * (y * ⁅π aJ, y'⁆ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this, hy]
      group)
  have hker : commutator (↥J ⧸ N.subgroupOf J) ≤ φ.ker := by
    refine Subgroup.commutator_le.mpr fun u _ v _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have hc : φ u * φ v = φ v * φ u :=
      Subtype.ext (Subgroup.mem_center_iff.mp (φ u).2 (φ v : ↥J ⧸ N.subgroupOf J)).symm
    exact commutatorElement_eq_one_iff_mul_comm.mpr hc
  rw [Group.IsPerfect.commutator_eq_top] at hker
  intro y hy
  have h1 : φ (π ⟨y, hy⟩) = 1 := by
    have := hker (Subgroup.mem_top (π ⟨y, hy⟩))
    exact this
  have h2 : ⁅π aJ, π ⟨y, hy⟩⁆ = 1 := congrArg Subtype.val h1
  rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  have h3 := Subgroup.mem_subgroupOf.mp h2
  exact h3

end ThreeSub

section Jq

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreOf_inf_and_quasisimple {I J : Subgroup G}
    (hs : IsSimpleGroup (↥I ⧸ pPrimeCore 2 ↥I))
    (hnc : ∃ a b : ↥I ⧸ pPrimeCore 2 ↥I, a * b ≠ b * a) (hJI : J ≤ I)
    (hcov : I ≤ J ⊔ pPrimeCoreOf 2 I) :
    pPrimeCoreOf 2 J = J ⊓ pPrimeCoreOf 2 I ∧ IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) := by
  set K : Subgroup G := pPrimeCoreOf 2 I with hK
  have hKI : K ≤ I := TwoThin.pPrimeCoreOf_le I
  have hIK : I ≤ normalizer (K : Set G) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact TwoThin.pPrimeCoreOf_normalized I hg
    · intro hh
      have := TwoThin.pPrimeCoreOf_normalized I (inv_mem hg) hh
      simpa [mul_assoc] using this
  have hmemK : ∀ x : ↥I, (x : G) ∈ K ↔ x ∈ pPrimeCore 2 ↥I := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  let φ : ↥J →* ↥I ⧸ pPrimeCore 2 ↥I :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥I)).comp (Subgroup.inclusion hJI)
  have hφsurj : Function.Surjective φ := by
    intro c
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    have hx : (x : G) ∈ K ⊔ J := by
      rw [sup_comm]
      exact hcov x.2
    obtain ⟨j, hj, hjk⟩ := exists_mem_inv_mul_mem (fun g hg => hIK (hJI hg)) hx
    refine ⟨⟨j, hj⟩, ?_⟩
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    exact (hmemK _).mp (by simpa using hjk)
  have hJKle : J ⊓ K ≤ pPrimeCoreOf 2 J := by
    refine le_pPrimeCoreOf_of_normal_odd inf_le_left (fun x hx n hn => ⟨?_, ?_⟩) ?_
    · exact J.mul_mem (J.mul_mem hx hn.1) (J.inv_mem hx)
    · exact (Subgroup.mem_normalizer_iff.mp (hIK (hJI hx)) n).mp hn.2
    · exact (TwoThin.card_pPrimeCoreOf_odd I).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hcore : pPrimeCore 2 (↥I ⧸ pPrimeCore 2 ↥I) = ⊥ := pPrimeCore_eq_bot_of_simple hs hnc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 ↥J ≤ φ.ker := by
    intro x hx
    have h1 : φ x ∈ (pPrimeCore 2 ↥J).map φ := ⟨x, hx, rfl⟩
    have h2 := CFSG.map_pPrimeCore_le φ hφsurj h1
    rw [hcore, Subgroup.mem_bot] at h2
    exact h2
  have hker : φ.ker = pPrimeCore 2 ↥J := by
    refine le_antisymm ?_ hO
    intro x hx
    have hxK : (x : G) ∈ K := by
      have : QuotientGroup.mk' (pPrimeCore 2 ↥I) (Subgroup.inclusion hJI x) = 1 := hx
      exact (hmemK _).mpr ((QuotientGroup.eq_one_iff _).mp this)
    have : (x : G) ∈ pPrimeCoreOf 2 J := hJKle ⟨x.2, hxK⟩
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  constructor
  · apply le_antisymm
    · rintro g ⟨y, hy, rfl⟩
      have h1 : y ∈ φ.ker := hO hy
      refine ⟨y.2, ?_⟩
      have : QuotientGroup.mk' (pPrimeCore 2 ↥I) (Subgroup.inclusion hJI y) = 1 := h1
      exact (hmemK _).mpr ((QuotientGroup.eq_one_iff _).mp this)
    · exact hJKle
  · let e : ↥J ⧸ pPrimeCore 2 ↥J ≃* ↥I ⧸ pPrimeCore 2 ↥I :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
    have : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) := e.isSimpleGroup
    obtain ⟨a, b, hab⟩ := hnc
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩).1

end Jq



section Hkey

variable {G : Type} [Group G] [Finite G]

theorem hkey_of_quasi (hB2 : B_B2_g4) (hG : IsKProperSimple G) (hgen4 : Gen4 G)
    {z t : G} (hz : orderOf z = 2) (ht : orderOf t = 2) (hzt : z * t = t * z)
    {H₁ H I : Subgroup G} (hH₁ : H₁ ≠ ⊤) (hzH₁ : z ∈ H₁) (htH₁ : t ∈ H₁) (hHH₁ : H ≤ H₁)
    (hH₁n : H₁ ≤ normalizer (H : Set G))
    (hIU : I ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G))
    (hCI : ∀ c ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G), c ∈ normalizer (I : Set G))
    (hs : IsSimpleGroup (↥I ⧸ pPrimeCore 2 ↥I))
    (hnc : ∃ a b : ↥I ⧸ pPrimeCore 2 ↥I, a * b ≠ b * a)
    (hN : pPrimeCoreOf 2 H₁ ≤ pPrimeCoreOf 2 H) :
    ∀ P₁ P₂ : Subgroup G, P₁ ≤ H ⊓ I → P₂ ≤ H ⊓ I → ⁅P₁, P₁⁆ = P₁ → ⁅P₂, P₂⁆ = P₂ →
      I ≤ P₁ ⊔ pPrimeCoreOf 2 I → I ≤ P₂ ⊔ pPrimeCoreOf 2 I → P₁ ≤ P₂ ⊔ pPrimeCoreOf 2 H := by
  intro P₁ P₂ hP₁ hP₂ hperf₁ hperf₂ hc₁ hc₂
  have hJP₁ : P₁ ≤ dres (H ⊓ I) := le_dres_of_perfect hperf₁ hP₁
  have hJP₂ : P₂ ≤ dres (H ⊓ I) := le_dres_of_perfect hperf₂ hP₂
  have hJHI : dres (H ⊓ I) ≤ H ⊓ I := dres_le _
  have hJperf : ⁅dres (H ⊓ I), dres (H ⊓ I)⁆ = dres (H ⊓ I) := dres_perfect _
  have hJI : dres (H ⊓ I) ≤ I := hJHI.trans inf_le_right
  have hcovJ : I ≤ dres (H ⊓ I) ⊔ pPrimeCoreOf 2 I :=
    hc₂.trans (sup_le_sup_right hJP₂ _)
  obtain ⟨hOJ, hJq⟩ := pPrimeCoreOf_inf_and_quasisimple hs hnc hJI hcovJ
  have hsub := subnormal_dres_inf (z := z) (t := t) hHH₁ hH₁n hIU hCI
  generalize dres (H ⊓ I) = J at *
  have hJH : J ≤ H := hJHI.trans inf_le_left
  have hIK : I ≤ normalizer ((pPrimeCoreOf 2 I : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_pPrimeCoreOf (le_normalizer hg)
  have hJY : J ≤ H₁ ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) := fun x hx =>
    ⟨⟨hHH₁ (hJH hx), (hIU (hJI hx)).1⟩, (hIU (hJI hx)).2⟩
  have hB₀z : H₁ ⊓ centralizer ({z} : Set G) ≠ ⊤ := fun h => hH₁ (top_le_iff.mp (h ▸ inf_le_left))
  have hKz := isKGroupNative_of_kProper hG.2.2 hB₀z
  have hgz : Gen4 ↥(H₁ ⊓ centralizer ({z} : Set G)) := Gen4.subgroup _ hgen4
  have hK₁ := isKGroupNative_of_kProper hG.2.2 hH₁
  have hg₁ : Gen4 ↥H₁ := Gen4.subgroup _ hgen4
  have htz : t ∈ H₁ ⊓ centralizer ({z} : Set G) :=
    ⟨htH₁, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  have hB : ∀ a ∈ J ⊓ pPrimeCoreOf 2 I, ∀ y ∈ J, ⁅a, y⁆ ∈ pPrimeCoreOf 2 H := by
    intro a ha
    have haJ : a ∈ J := ha.1
    have haO : a ∈ pPrimeCoreOf 2 J := hOJ ▸ ha
    have haY : a ∈ pPrimeCoreOf 2 (H₁ ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) :=
      pPrimeCoreOf_le_of_subnormalIn hJY hsub haO
    have hN' : J ≤ normalizer ((pPrimeCoreOf 2 H₁ : Subgroup G) : Set G) := fun g hg =>
      mem_normalizer_pPrimeCoreOf (le_normalizer (hHH₁ (hJH hg)))
    intro y hy
    refine hN (commutator_mem_of_double hJperf hN' haJ (fun y hy y' hy' => ?_) y hy)
    have h1 : ⁅a, y⁆ ∈ pPrimeCoreOf 2 (H₁ ⊓ centralizer ({z} : Set G)) :=
      commutator_oddCore_centralizer_le' hB2 hKz hgz htz ht hJY hJperf hsub hJq haY hy
    exact commutator_oddCore_le_oddCore' hB2 hK₁ hg₁ hzH₁ htH₁ hz ht hzt hJY hJperf hsub hJq h1 hy'
  have hJPZ : J ≤ P₂ ⊔ (J ⊓ pPrimeCoreOf 2 I) := by
    intro x hx
    have hx' : x ∈ pPrimeCoreOf 2 I ⊔ P₂ := by
      rw [sup_comm]
      exact hc₂ (hJI hx)
    obtain ⟨p, hp, hpk⟩ := exists_mem_inv_mul_mem
      (fun g hg => hIK ((hP₂ hg).2)) hx'
    have hpJ : p⁻¹ * x ∈ J := J.mul_mem (J.inv_mem (hJP₂ hp)) hx
    have hxe : x = p * (p⁻¹ * x) := by group
    rw [hxe]
    exact Subgroup.mul_mem_sup hp ⟨hpJ, hpk⟩
  have hNJ : J ≤ normalizer ((pPrimeCoreOf 2 H : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_pPrimeCoreOf (le_normalizer (hJH hg))
  have := le_sup_of_perfect_central hJperf hJP₂ inf_le_left hJPZ hNJ hB
  exact hJP₁.trans this

end Hkey

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L102
