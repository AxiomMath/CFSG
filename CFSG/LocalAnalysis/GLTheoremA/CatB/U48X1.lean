module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Row50

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X1

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 μ3 fieldSU4)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K)
open scoped commutatorElement


theorem derived_centralizer_le_Jblk {t : μ3} (ht : (t : Kˣ) ≠ 1) : ⁅Cstd t, Cstd t⁆ ≤ Jblk := by
  rw [← map_ker_rho ht]
  have hT : ⁅(⊤ : Subgroup ↥(Cstd t)), ⊤⁆ ≤ (rho ht).ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have h2 := Subgroup.map_mono (f := (Cstd t).subtype) hT
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h2


variable {G : Type} [Group G] [Finite G]

theorem layer_criterion {X M : Subgroup G} {y : G}
    (hM : GLAPComponent 3 X M) (hcat : catalogIs (PSimple 3 M) S9.isU4eight)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hyc : IsCentralIn 3 y M)
    {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hQM : Q ≤ ⁅M ⊓ Subgroup.centralizer ({y} : Set G), M ⊓ Subgroup.centralizer ({y} : Set G)⁆) :
    Q ≤ GLAPLayer 3 (M ⊓ Subgroup.centralizer ({y} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ := center_pquot_eq_bot_of_u48 hM hcat
  set e := pqModelP hZ hcat with he
  have hyM : y ∈ M := hyc.1
  obtain ⟨g, t, ht, hgy⟩ := exists_conj_of_central (piOf M e) (piOf_surjective M e)
    (not_three_dvd_card_ker_piOf e) hy3 hy1 hyc
  set φ : ↥M →* SU4 := (MulAut.conj g).toMonoidHom.comp (piOf M e) with hφ
  have hφapp : ∀ x : ↥M, φ x = g * piOf M e x * g⁻¹ := fun x => rfl
  have hφs : Function.Surjective φ := by
    intro s
    obtain ⟨x, hx⟩ := piOf_surjective M e (g⁻¹ * s * g)
    exact ⟨x, by rw [hφapp, hx]; group⟩
  have hker : φ.ker = (piOf M e).ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hφapp]
    constructor
    · intro h
      have h2 : g * piOf M e x * g⁻¹ = g * 1 * g⁻¹ := by rw [h, mul_one, mul_inv_cancel]
      exact mul_left_cancel (mul_right_cancel h2)
    · intro h; rw [h]; group
  have hφk : ¬ 3 ∣ Nat.card φ.ker := by
    rw [hker]; exact not_three_dvd_card_ker_piOf e
  have hφy : φ ⟨y, hyM⟩ = yStd t := by
    rw [hφapp]; exact hgy
  obtain ⟨J, hJ, hJl, himg, -⟩ := layerY φ hφs hφk ht hyM hy3 hφy
  set H : Subgroup G := M ⊓ Subgroup.centralizer ({y} : Set G) with hH
  have hJl' : GLAPLayer 3 H = J := hJl
  have hJH : J ≤ H := hJ.1
  have hJnorm : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J := by
    intro h hh j hj
    have hN : h ∈ Subgroup.normalizer (GLAPLayer 3 H : Set G) :=
      mem_normalizer_glaPLayer (p := 3) (Subgroup.le_normalizer hh)
    have hj' : j ∈ GLAPLayer 3 H := hJl' ▸ hj
    rw [← hJl']
    exact (Subgroup.mem_normalizer_iff.1 hN j).1 hj'
  have hcommH : ⁅H, H⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  set HM : Subgroup ↥M := H.subgroupOf M with hHM
  set A : Subgroup ↥M := Subgroup.comap φ Jblk ⊓ HM with hA
  set JM : Subgroup ↥M := J.subgroupOf M with hJM
  have hJMA : JM ≤ A := by
    intro x hx
    have hxJ : (x : G) ∈ J := Subgroup.mem_subgroupOf.1 hx
    rw [hA, Subgroup.mem_inf, Subgroup.mem_comap, hHM, Subgroup.mem_subgroupOf]
    refine ⟨?_, hJH hxJ⟩
    rw [← himg]
    exact Subgroup.mem_map_of_mem φ hx
  have hφH : ∀ h ∈ HM, φ h ∈ Cstd t := by
    intro h hh
    rw [Cstd, Subgroup.mem_centralizer_singleton_iff]
    have hhC : (h : G) ∈ H := Subgroup.mem_subgroupOf.1 hh
    have hcomm : (h : G) * y = y * (h : G) := Subgroup.mem_centralizer_singleton_iff.1 hhC.2
    have hxy : h * ⟨y, hyM⟩ = ⟨y, hyM⟩ * h := Subtype.ext hcomm
    have h2 := congrArg φ hxy
    rw [map_mul, map_mul, hφy] at h2
    exact h2
  have hφcomm : ∀ x ∈ ⁅HM, HM⁆, φ x ∈ Jblk := by
    intro x hx
    have hmap : φ x ∈ (⁅HM, HM⁆ : Subgroup ↥M).map φ := Subgroup.mem_map_of_mem φ hx
    rw [Subgroup.map_commutator] at hmap
    have hle : ⁅HM.map φ, HM.map φ⁆ ≤ ⁅Cstd t, Cstd t⁆ := by
      apply Subgroup.commutator_mono
      · rintro _ ⟨h, hh, rfl⟩
        exact hφH h hh
      · rintro _ ⟨h, hh, rfl⟩
        exact hφH h hh
    exact derived_centralizer_le_Jblk ht (hle hmap)
  have hQA : Q.subgroupOf M ≤ A := by
    intro x hx
    have hxQ : (x : G) ∈ Q := Subgroup.mem_subgroupOf.1 hx
    have hxc : (x : G) ∈ ⁅H, H⁆ := hQM hxQ
    have hxH : (x : G) ∈ H := hcommH hxc
    have hmapM : (⁅HM, HM⁆ : Subgroup ↥M).map M.subtype = ⁅H, H⁆ := by
      rw [Subgroup.map_commutator, hHM, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 inf_le_left]
    have hxmem : x ∈ ⁅HM, HM⁆ := by
      have h1 : (x : G) ∈ (⁅HM, HM⁆ : Subgroup ↥M).map M.subtype := by
        rw [hmapM]; exact hxc
      obtain ⟨y', hy', hy'eq⟩ := Subgroup.mem_map.1 h1
      have : y' = x := Subtype.ext hy'eq
      rw [← this]
      exact hy'
    rw [hA, Subgroup.mem_inf, Subgroup.mem_comap, hHM, Subgroup.mem_subgroupOf]
    exact ⟨hφcomm x hxmem, hxH⟩
  set KA : Subgroup ↥A := φ.ker.subgroupOf A with hKA
  set JA : Subgroup ↥A := JM.subgroupOf A with hJA
  have hJAn : JA.Normal := by
    constructor
    intro n hn a
    have hn' : (n : ↥M) ∈ JM := Subgroup.mem_subgroupOf.1 hn
    have hJn : ((n : ↥M) : G) ∈ J := Subgroup.mem_subgroupOf.1 hn'
    have ha : ((a : ↥M) : G) ∈ H := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 a.2).2
    rw [hJA, Subgroup.mem_subgroupOf, hJM, Subgroup.mem_subgroupOf]
    have := hJnorm _ ha _ hJn
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hsurj : Function.Surjective ((QuotientGroup.mk' JA).comp KA.subtype) := by
    intro c
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective JA c
    have haφ : φ (a : ↥M) ∈ Jblk := (Subgroup.mem_inf.1 a.2).1
    rw [← himg] at haφ
    obtain ⟨j, hj, hjφ⟩ := Subgroup.mem_map.1 haφ
    set jA : ↥A := ⟨j, hJMA hj⟩ with hjA
    have hkA : a * jA⁻¹ ∈ KA := by
      rw [hKA, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      show φ ((a : ↥M) * (j : ↥M)⁻¹) = 1
      rw [map_mul, map_inv, hjφ, mul_inv_cancel]
    refine ⟨⟨a * jA⁻¹, hkA⟩, ?_⟩
    show QuotientGroup.mk' JA (a * jA⁻¹) = QuotientGroup.mk' JA a
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 : (a * jA⁻¹)⁻¹ * a = jA := by group
    rw [h1]
    exact Subgroup.mem_subgroupOf.2 hj
  have hcardQ : ¬ 3 ∣ Nat.card (↥A ⧸ JA) := by
    intro h3
    apply hφk
    refine h3.trans ((Subgroup.card_dvd_of_surjective hsurj).trans ?_)
    rw [← Subgroup.card_map_of_injective (K := KA) A.subtype_injective]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨k, hk, rfl⟩
    have hk' : (k : ↥M) ∈ φ.ker := hk
    exact hk'
  intro x hx
  have hxH : x ∈ H := hcommH (hQM hx)
  have hxM : (x : G) ∈ M := (Subgroup.mem_inf.1 hxH).1
  set xM : ↥M := ⟨x, hxM⟩ with hxM'
  set xA : ↥A := ⟨xM, hQA (Subgroup.mem_subgroupOf.2 hx)⟩ with hxA'
  obtain ⟨n, hn⟩ := hQ ⟨x, hx⟩
  have hxn : xA ^ 3 ^ n = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have h2 := congrArg Subtype.val hn
    simpa [xA, xM, Subgroup.coe_pow] using h2
  have hmk : QuotientGroup.mk' JA xA ^ 3 ^ n = 1 := by
    rw [← map_pow, hxn, map_one]
  have hord1 : orderOf (QuotientGroup.mk' JA xA) ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hmk
  have hord2 : orderOf (QuotientGroup.mk' JA xA) ∣ Nat.card (↥A ⧸ JA) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ n) (Nat.card (↥A ⧸ JA)) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hcardQ)
  have hone : orderOf (QuotientGroup.mk' JA xA) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord1 hcop) hord2
  haveI := hJAn
  have hxJA : xA ∈ JA := (QuotientGroup.eq_one_iff xA).1 (orderOf_eq_one_iff.1 hone)
  have hxJ : x ∈ J := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hxJA)
  rw [hJl']
  exact hxJ

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X1
