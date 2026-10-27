module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneInputs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutStrongF
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutStrongSup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutTransport
import CFSG.GroupTheory.ConjKerCenter

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

open Subgroup

private theorem exists_pElement_lift_center {F : Type*} [Group F] [Finite F]
    {p : ℕ} [Fact p.Prime]
    (hcenter : Subgroup.center (F ⧸ Subgroup.center F) = ⊥)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center F))
    {c : MulAut (F ⧸ Subgroup.center F)}
    (hc : c ∈ (MulAut.conj :
      (F ⧸ Subgroup.center F) →* MulAut (F ⧸ Subgroup.center F)).range)
    (hcp : IsPGroup p (Subgroup.zpowers c)) :
    ∃ x : F, MulAut.conj (QuotientGroup.mk' (Subgroup.center F) x) = c ∧
      ∃ m : ℕ, orderOf x = p ^ m := by
  classical
  let π : F →* MulAut (F ⧸ Subgroup.center F) :=
    MulAut.conj.comp (QuotientGroup.mk' (Subgroup.center F))
  have hker : π.ker = Subgroup.center F := by
    change (MulAut.conj.comp (QuotientGroup.mk' (Subgroup.center F))).ker = _
    rw [← MonoidHom.comap_ker, CFSG.GroupTheory.ker_conj_eq_center, hcenter,
      MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have hC : ¬ p ∣ Nat.card π.ker := by
    rw [hker]
    exact hZ
  obtain ⟨k, hk⟩ := hc
  obtain ⟨k', hk'⟩ := QuotientGroup.mk'_surjective (Subgroup.center F) k
  have hπk' : π k' = c := by
    change MulAut.conj (QuotientGroup.mk' (Subgroup.center F) k') = c
    rw [hk', hk]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf (p := p)).1 hcp
    ⟨c, Subgroup.mem_zpowers c⟩
  have hn' : orderOf (π k') = p ^ n := by
    rw [hπk', Subgroup.orderOf_coe (⟨c, Subgroup.mem_zpowers c⟩ :
      ↥(Subgroup.zpowers c))]
    exact hn
  obtain ⟨x, hπx, m, hxord⟩ :=
    CFSG.LieType.CentralExt.exists_pElement_lift (p := p) (π := π) hC k' hn'
  exact ⟨x, hπx.trans hπk', m, hxord⟩

private theorem commutator_eq_one_of_centralizer {X : Type*} [Group X] {F : Subgroup X}
    {p m : ℕ} [Fact p.Prime] (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥F))
    {r x : X} (hxF : x ∈ F) (hxord : orderOf x = p ^ m)
    (hwF : r * x * r⁻¹ * x⁻¹ ∈ F)
    (hwC : r * x * r⁻¹ * x⁻¹ ∈ Subgroup.centralizer (F : Set X)) :
    r * x * r⁻¹ * x⁻¹ = 1 := by
  let w : X := r * x * r⁻¹ * x⁻¹
  have hwF' : w ∈ F := hwF
  have hwC' : w ∈ Subgroup.centralizer (F : Set X) := hwC
  have hxpow : x ^ p ^ m = 1 := by
    rw [← hxord, pow_orderOf_eq_one]
  have hconjpow : (r * x * r⁻¹) ^ p ^ m = 1 := by
    have hconj : r * x * r⁻¹ = MulAut.conj r x := by simp [MulAut.conj_apply]
    rw [hconj, ← map_pow, hxpow, map_one]
  have hwxe : w * x = r * x * r⁻¹ := by
    simp only [w]
    group
  have hxw : x * w = w * x := Subgroup.mem_centralizer_iff.mp hwC' x hxF
  have hwpow : w ^ p ^ m = 1 := by
    have h1 : (w * x) ^ p ^ m = 1 := by rw [hwxe]; exact hconjpow
    have h := (show Commute w x from hxw.symm).mul_pow (p ^ m)
    rw [h1, hxpow, mul_one] at h
    exact h.symm
  have hwcenter : (⟨w, hwF'⟩ : ↥F) ∈ Subgroup.center ↥F := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hwC' (z : X) z.2
  have hwdvd : orderOf w ∣ Nat.card (Subgroup.center ↥F) := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥F) hwcenter
    rwa [Subgroup.orderOf_mk] at h
  have hord_dvd_p : orderOf w ∣ p ^ m := orderOf_dvd_of_pow_eq_one hwpow
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hord_dvd_p
  have hpdvd : p ^ j ∣ Nat.card (Subgroup.center ↥F) := by
    rw [← hj]
    exact hwdvd
  have hj0 : j = 0 := by
    by_contra hjne
    exact hZ (Nat.dvd_of_pow_dvd (by omega : 1 ≤ j) hpdvd)
  have hord1 : orderOf w = 1 := by rw [hj, hj0, pow_zero]
  exact orderOf_eq_one_iff.mp hord1

private theorem isStronglyPEmbedded_range_autMap
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {X : Type} [Group X] [Finite X] {F Y R : Subgroup X}
    (hF : CFSG.IsQuasisimple ↥F) (hYF : Y ≤ F) (hYne : Y ≠ F)
    (hP : ∃ P : Subgroup X, CFSG.ABGLocalTools.IsSylowOf p P F ∧
      ∀ U : Subgroup X, U ≤ P → U ≠ ⊥ →
        F ⊓ Subgroup.normalizer (U : Set X) ≤ Y)
    (hRF : R ≤ Subgroup.normalizer (F : Set X))
    (hRY : R ≤ Subgroup.normalizer (Y : Set X))
    (hRexp : ∀ x ∈ R, x ^ 3 = 1)
    (hpF : p ∣ Nat.card (↥F ⧸ Subgroup.center ↥F)) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p
        ((((Y ⊔ R).subgroupOf (F ⊔ R)).map (autMap F R hRF)).subgroupOf
          (autMap F R hRF).range) ∧
      Nonempty (↥(CFSG.generalizedFitting ↥(autMap F R hRF).range) ≃*
        (↥F ⧸ Subgroup.center ↥F)) := by
  classical
  have hp3 : p ≠ 3 := by omega
  obtain ⟨P, hPsyl, hΓ⟩ := hP
  have hpF' : p ∣ Nat.card F := hpF.trans (Subgroup.card_quotient_dvd_card _)
  have hpY : p ∣ Nat.card Y := dvd_card_of_isSylowOf_gamma hPsyl hΓ hpF'
  have hZ : ¬ p ∣ Nat.card (Subgroup.center ↥F) :=
    not_dvd_card_center_of_gamma hPsyl hΓ hYF hYne
  have hk := not_dvd_card_inf_conj_of_gamma hPsyl hΓ hYF hYne hpF'
  have hFY : F ⊓ Subgroup.normalizer (Y : Set X) ≤ Y :=
    inf_normalizer_le_of_gamma hPsyl hΓ hYF hYne hpF'
  have hR3 : IsPGroup 3 R := fun x => ⟨1, Subtype.ext (by simpa using hRexp x x.2)⟩
  let f := autMap F R hRF
  have hYstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded p
      ((Y ⊔ R).subgroupOf (F ⊔ R)) :=
    isStronglyPEmbedded_sup_subgroupOf hp3 hYF hYne hRF hRY hR3 hpY hk hFY
  have hker : f.ker ≤ (Y ⊔ R).subgroupOf (F ⊔ R) :=
    ker_autMap_le hRF hF.1 hYF hRY hFY
  have hpk : ¬ p ∣ Nat.card f.ker :=
    not_dvd_card_ker_autMap hp3 hRF hR3 hF.1 hZ
  have hNstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded p
      ((((Y ⊔ R).subgroupOf (F ⊔ R)).map f).subgroupOf f.range) :=
    isStronglyPEmbedded_autMap_range hRF hYstr hker hpk
  have hconjrange : (MulAut.conj :
      (↥F ⧸ Subgroup.center ↥F) →* MulAut (↥F ⧸ Subgroup.center ↥F)).range ≤ f.range :=
    range_conj_le_range_autMap hRF
  haveI : IsSimpleGroup (↥F ⧸ Subgroup.center ↥F) := hF.2.1
  haveI : Finite (MulAut (↥F ⧸ Subgroup.center ↥F)) :=
    Finite.of_injective (fun φ : MulAut _ => (φ : _ → _)) DFunLike.coe_injective
  have he : Nonempty (↥(CFSG.generalizedFitting ↥f.range) ≃*
      (↥F ⧸ Subgroup.center ↥F)) :=
    nonempty_generalizedFitting_equiv_of_range_conj_le hF.2.2 hconjrange
  exact ⟨hNstr, he⟩

private theorem autMap_range_subgroupOf_facts
    {X : Type} [Group X] [Finite X] {F Y R : Subgroup X}
    (hRF : R ≤ Subgroup.normalizer (F : Set X))
    (hF : Group.IsPerfect ↥F)
    (hRC : R ⊓ Subgroup.centralizer (F : Set X) = ⊥)
    (hRexp : ∀ x ∈ R, x ^ 3 = 1) (hR9 : 9 ≤ Nat.card R) :
    (((R.subgroupOf (F ⊔ R)).map (autMap F R hRF)).subgroupOf
        (autMap F R hRF).range) ≤
      ((((Y ⊔ R).subgroupOf (F ⊔ R)).map (autMap F R hRF)).subgroupOf
        (autMap F R hRF).range) ∧
    (∀ x ∈ ((R.subgroupOf (F ⊔ R)).map (autMap F R hRF)).subgroupOf
        (autMap F R hRF).range, x ^ 3 = 1) ∧
    Nat.card (((R.subgroupOf (F ⊔ R)).map (autMap F R hRF)).subgroupOf
        (autMap F R hRF).range) = Nat.card R ∧
    9 ≤ Nat.card (((R.subgroupOf (F ⊔ R)).map (autMap F R hRF)).subgroupOf
        (autMap F R hRF).range) := by
  classical
  let f := autMap F R hRF
  let N : Subgroup ↥f.range :=
    (((Y ⊔ R).subgroupOf (F ⊔ R)).map f).subgroupOf f.range
  let R' : Subgroup ↥f.range := ((R.subgroupOf (F ⊔ R)).map f).subgroupOf f.range
  have hR'le : R' ≤ N := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.map_mono (Subgroup.subgroupOf_mono (F ⊔ R) le_sup_right)
        (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx)))
  have hR'exp : ∀ x ∈ R', x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hy, hyf⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
    have hy3 : y ^ 3 = 1 :=
      Subtype.ext (hRexp (y : X) (Subgroup.mem_subgroupOf.mp hy))
    apply Subtype.ext
    change (x : MulAut (↥F ⧸ Subgroup.center ↥F)) ^ 3 = 1
    rw [← hyf, ← map_pow, hy3, map_one]
  have hcardmap : Nat.card ((R.subgroupOf (F ⊔ R)).map f) = Nat.card R :=
    card_map_autMap_eq hRF hF hRC
  have hcardR' : Nat.card R' = Nat.card ((R.subgroupOf (F ⊔ R)).map f) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_le_range f _)).toEquiv
  have hcard : Nat.card R' = Nat.card R := hcardR'.trans hcardmap
  have hge : 9 ≤ Nat.card R' := by
    rw [hcard]
    exact hR9
  exact ⟨hR'le, hR'exp, hcard, hge⟩

private theorem commutator_eq_one_of_autMap_image
    {p m : ℕ} [Fact p.Prime]
    {X : Type} [Group X] [Finite X] {F R : Subgroup X}
    (hRF : R ≤ Subgroup.normalizer (F : Set X))
    (hF : Group.IsPerfect ↥F) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥F))
    {r x : X} (hrR : r ∈ R) (hxF : x ∈ F) (hxord : orderOf x = p ^ m)
    {c r' : MulAut (↥F ⧸ Subgroup.center ↥F)}
    (hrf : autMap F R hRF (⟨r, Subgroup.mem_sup_right hrR⟩ : ↥(F ⊔ R)) = r')
    (hxf : autMap F R hRF (⟨x, Subgroup.mem_sup_left hxF⟩ : ↥(F ⊔ R)) = c)
    (hcomm : c * r' = r' * c) :
    r * x = x * r := by
  let f := autMap F R hRF
  let g : ↥(F ⊔ R) := ⟨r, Subgroup.mem_sup_right hrR⟩ *
    ⟨x, Subgroup.mem_sup_left hxF⟩ * ⟨r, Subgroup.mem_sup_right hrR⟩⁻¹ *
    ⟨x, Subgroup.mem_sup_left hxF⟩⁻¹
  let w : X := r * x * r⁻¹ * x⁻¹
  have hgw : (g : X) = w := rfl
  have hgker : g ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    calc (f g : MulAut (↥F ⧸ Subgroup.center ↥F))
        = f (⟨r, Subgroup.mem_sup_right hrR⟩ : ↥(F ⊔ R)) *
            f (⟨x, Subgroup.mem_sup_left hxF⟩ : ↥(F ⊔ R)) *
            (f (⟨r, Subgroup.mem_sup_right hrR⟩ : ↥(F ⊔ R)))⁻¹ *
            (f (⟨x, Subgroup.mem_sup_left hxF⟩ : ↥(F ⊔ R)))⁻¹ := by
          simp only [g, map_mul, map_inv]
      _ = r' * c * r'⁻¹ * c⁻¹ := by rw [hrf, hxf]
      _ = 1 := by rw [← hcomm]; group
  have hwC : w ∈ Subgroup.centralizer (F : Set X) := by
    have h := mem_centralizer_of_mem_ker_autMap hRF hF hgker
    rwa [hgw] at h
  have hrxr : r * x * r⁻¹ ∈ F :=
    (Subgroup.mem_normalizer_iff.mp (hRF hrR) x).mp hxF
  have hwF : w ∈ F := by
    change r * x * r⁻¹ * x⁻¹ ∈ F
    exact F.mul_mem hrxr (F.inv_mem hxF)
  have hw1 : w = 1 := commutator_eq_one_of_centralizer hZ hxF hxord hwF hwC
  have h1 : r * x * r⁻¹ = x := by
    have h2 : r * x * r⁻¹ * x⁻¹ = 1 := hw1
    exact mul_inv_eq_one.mp h2
  calc r * x = (r * x * r⁻¹) * r := by group
    _ = x * r := by rw [h1]

private theorem exists_centralizing_pElement_of_fitting
    {p : ℕ} [Fact p.Prime]
    {X : Type} [Group X] [Finite X] {F Y R : Subgroup X}
    (hF : CFSG.IsQuasisimple ↥F)
    (hRF : R ≤ Subgroup.normalizer (F : Set X))
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥F))
    {r : X} (hrR : r ∈ R)
    {c r' : ↥(autMap F R hRF).range}
    (hcF : c ∈ CFSG.generalizedFitting ↥(autMap F R hRF).range)
    (hcomm : c * r' = r' * c)
    (hcp : IsPGroup p (Subgroup.zpowers c))
    (hcN : c ∉ (((Y ⊔ R).subgroupOf (F ⊔ R)).map (autMap F R hRF)).subgroupOf
      (autMap F R hRF).range)
    (hrf : autMap F R hRF (⟨r, Subgroup.mem_sup_right hrR⟩ : ↥(F ⊔ R)) =
      (r' : MulAut (↥F ⧸ Subgroup.center ↥F))) :
    ∃ x : ↥F, (∃ m : ℕ, orderOf x = p ^ m) ∧
      r * (x : X) = (x : X) * r ∧ (x : X) ∉ Y := by
  classical
  have hcenterS : Subgroup.center (↥F ⧸ Subgroup.center ↥F) = ⊥ :=
    CFSG.QuasithinUnique.Ch1.center_quotient_eq_bot hF
  let f := autMap F R hRF
  haveI : IsSimpleGroup (↥F ⧸ Subgroup.center ↥F) := hF.2.1
  have hcInn : c ∈ (MulAut.conj :
      (↥F ⧸ Subgroup.center ↥F) →* MulAut (↥F ⧸ Subgroup.center ↥F)).range.subgroupOf
        f.range := by
    rw [generalizedFitting_eq_range_conj hF.2.2 (range_conj_le_range_autMap hRF)] at hcF
    exact hcF
  have hcrange : (c : MulAut (↥F ⧸ Subgroup.center ↥F)) ∈ (MulAut.conj :
      (↥F ⧸ Subgroup.center ↥F) →* MulAut (↥F ⧸ Subgroup.center ↥F)).range :=
    Subgroup.mem_subgroupOf.mp hcInn
  have hcp' : IsPGroup p (Subgroup.zpowers ((Subgroup.subtype f.range) c)) := by
    rw [← MonoidHom.map_zpowers (Subgroup.subtype f.range) c]
    exact hcp.map (Subgroup.subtype f.range)
  obtain ⟨x, hxπ, m, hxord⟩ :=
    exists_pElement_lift_center hcenterS hZ hcrange hcp'
  let xX : X := (x : X)
  have hxf : f (⟨xX, Subgroup.mem_sup_left x.2⟩ : ↥(F ⊔ R)) =
      (c : MulAut (↥F ⧸ Subgroup.center ↥F)) := by
    change autMap F R hRF (⟨xX, Subgroup.mem_sup_left x.2⟩ : ↥(F ⊔ R)) = _
    rw [autMap_of_mem hRF x.2]
    simpa [QuotientGroup.mk'_apply] using hxπ
  have hcomm' : (c : MulAut (↥F ⧸ Subgroup.center ↥F)) *
      (r' : MulAut (↥F ⧸ Subgroup.center ↥F)) =
      (r' : MulAut (↥F ⧸ Subgroup.center ↥F)) *
        (c : MulAut (↥F ⧸ Subgroup.center ↥F)) := congrArg Subtype.val hcomm
  have hrx : r * xX = xX * r :=
    commutator_eq_one_of_autMap_image hRF hF.1 hZ hrR x.2
      ((Subgroup.orderOf_coe x).trans hxord) hrf hxf hcomm'
  have hxY : xX ∉ Y := by
    intro hxYmem
    apply hcN
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hmem : f (⟨xX, Subgroup.mem_sup_left x.2⟩ : ↥(F ⊔ R)) ∈
        ((Y ⊔ R).subgroupOf (F ⊔ R)).map f :=
      Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_left hxYmem))
    rwa [hxf] at hmem
  exact ⟨x, ⟨m, hxord⟩, hrx, hxY⟩

theorem kFactNineFourAutM_of_autMFor {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {X : Type} [Group X] [Finite X] {F Y R : Subgroup X}
    (hF : CFSG.IsQuasisimple ↥F) (hYF : Y ≤ F) (hYne : Y ≠ F)
    (hP : ∃ P : Subgroup X, CFSG.ABGLocalTools.IsSylowOf p P F ∧
      ∀ U : Subgroup X, U ≤ P → U ≠ ⊥ →
        F ⊓ Subgroup.normalizer (U : Set X) ≤ Y)
    (hRF : R ≤ Subgroup.normalizer (F : Set X))
    (hRY : R ≤ Subgroup.normalizer (Y : Set X))
    (hRC : R ⊓ Subgroup.centralizer (F : Set X) = ⊥)
    (hRexp : ∀ x ∈ R, x ^ 3 = 1) (hR9 : 9 ≤ Nat.card R)
    (hpF : p ∣ Nat.card (↥F ⧸ Subgroup.center ↥F))
    (hstar : AutMFor p (↥F ⧸ Subgroup.center ↥F)) :
    Nat.card R = 9 ∧ ∃ r ∈ R, r ≠ 1 ∧ ¬ F ⊓ Subgroup.centralizer ({r} : Set X) ≤ Y := by
  classical
  have hp3 : p ≠ 3 := by omega
  obtain ⟨hNstr, he⟩ :=
    isStronglyPEmbedded_range_autMap hp5 hF hYF hYne hP hRF hRY hRexp hpF
  obtain ⟨P, hPsyl, hΓ⟩ := hP
  have hZ : ¬ p ∣ Nat.card (Subgroup.center ↥F) :=
    not_dvd_card_center_of_gamma hPsyl hΓ hYF hYne
  let f := autMap F R hRF
  let N : Subgroup ↥f.range := (((Y ⊔ R).subgroupOf (F ⊔ R)).map f).subgroupOf f.range
  let R' : Subgroup ↥f.range := ((R.subgroupOf (F ⊔ R)).map f).subgroupOf f.range
  obtain ⟨hR'le, hR'exp, hcardR'eq, hR'9⟩ :=
    autMap_range_subgroupOf_facts hRF hF.1 hRC hRexp hR9
  obtain ⟨hcardR9, r', hr'R', hr'ne, c, hcF, hcomm, hcp, hcN⟩ :=
    hstar ↥f.range he N hNstr R' hR'le hR'exp hR'9
  obtain ⟨y, hy, hyf⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hr'R')
  let r : X := (y : X)
  have hrR : r ∈ R := Subgroup.mem_subgroupOf.mp hy
  have hrne : r ≠ 1 := by
    intro hr1
    apply hr'ne
    apply Subtype.ext
    rw [← hyf, show y = 1 from Subtype.ext hr1]
    exact map_one f
  have hrf : f (⟨r, Subgroup.mem_sup_right hrR⟩ : ↥(F ⊔ R)) =
      (r' : MulAut (↥F ⧸ Subgroup.center ↥F)) := by
    have hy_eq : (⟨r, Subgroup.mem_sup_right hrR⟩ : ↥(F ⊔ R)) = y := Subtype.ext rfl
    rw [hy_eq]
    exact hyf
  obtain ⟨x, ⟨m, hxord⟩, hrx, hxY⟩ :=
    exists_centralizing_pElement_of_fitting hF hRF hZ hrR hcF hcomm hcp hcN hrf
  have hxC : (x : X) ∈ Subgroup.centralizer ({r} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hrx.symm
  refine ⟨?_, r, hrR, hrne, ?_⟩
  · rw [← hcardR'eq]
    exact hcardR9
  · intro hle
    exact hxY (hle (Subgroup.mem_inf.mpr ⟨x.2, hxC⟩))

theorem kFactNineFourAutM_of_families
    (h : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (S : Type) [Group S] [Finite S],
      CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup p S →
      (∃ a b : S, a * b ≠ b * a) → p ∣ Nat.card S ∧ AutMFor p S) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactNineFourAutM := by
  intro p hp h5 X _ _ F Y R hF hlist hYF hYne hP hRF hRY hRC hRexp hR9
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpS, hS⟩ := h p h5 (↥F ⧸ Subgroup.center ↥F) hlist hF.2.2
  exact kFactNineFourAutM_of_autMFor h5 hF hYF hYne hP hRF hRY hRC hRexp hR9 hpS hS

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut
