module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SZ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SSup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec8s_sup_isPGroup {G : Type} [Group G] {t : G} {E : Subgroup G}
    (ht2 : t * t = 1) (htord : orderOf t = 2) (htn : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (hE2 : IsPGroup 2 E) : IsPGroup 2 (zpowers t ⊔ E : Subgroup G) := by
  have htP : IsPGroup 2 (zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, htord, pow_one]
  have ht_norm : t ∈ normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact htn x hx
    · intro hx
      have h2 := htn (t * x * t⁻¹) hx
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      have heq : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [hti]
        calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [ht2, one_mul, mul_one]
      rwa [heq] at h2
  have hzt : zpowers t ≤ normalizer (E : Set G) := zpowers_le.mpr ht_norm
  have h2 : IsPGroup 2 (E ⊔ zpowers t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hE2 htP hzt
  rwa [sup_comm] at h2

private theorem sec8s_comm_of_conj {G : Type} [Group G] {t : G} {E : Subgroup G}
    (hEel : CFSG.Open.IsElemAbelian 2 E) (ht2 : t * t = 1) (htord : orderOf t = 2) {e : G}
    (heE : e ∈ E) (hconj : IsConj t (t * e)) : e * t = t * e := by
  have hy2 : orderOf (t * e) = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff_inv_mul.mp hconj
    rw [← hc, orderOf_conjugate_eq, htord]
  have hsq : (t * e) * (t * e) = 1 := by
    rw [← pow_two, ← hy2, pow_orderOf_eq_one]
  have hee : e * e = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hEel heE
  have h1 : e * t * e = t := by
    have h := congrArg (fun z => t * z) hsq
    have heq : t * ((t * e) * (t * e)) = e * t * e := by
      calc t * ((t * e) * (t * e)) = (t * t) * (e * (t * e)) := by group
        _ = e * t * e := by rw [ht2, one_mul]; group
    rw [heq] at h
    simpa using h
  calc e * t = (e * t) * 1 := by group
    _ = (e * t) * (e * e) := by rw [hee]
    _ = (e * t * e) * e := by group
    _ = t * e := by rw [h1]

private theorem sec8s_class {G : Type} [Group G] {t z : G} {B E : Subgroup G}
    (hEel : CFSG.Open.IsElemAbelian 2 E)
    (hcent : E ⊓ centralizer ({t} : Set G) = B) (ht2 : t * t = 1)
    (htord : orderOf t = 2) (htn : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (h88bE : ∀ y ∈ E, IsConj t y → y ≠ 1 → IsConj z y) (hnotconj : ¬ IsConj z t)
    {y : G} (hy : y ∈ zpowers t ⊔ E) (hyconj : IsConj t y) : ∃ b ∈ B, y = t * b := by
  rcases sec8s_mem_sup_zpowers ht2 htn hy with hyE | ⟨e, heE, hyeq⟩
  · exfalso
    have hy1 : y ≠ 1 := by
      intro h
      have hy2 : orderOf y = 2 := by
        obtain ⟨c, hc⟩ := isConj_iff_inv_mul.mp hyconj
        rw [← hc, orderOf_conjugate_eq, htord]
      rw [h, orderOf_one] at hy2
      omega
    exact hnotconj (IsConj.trans (h88bE y hyE hyconj hy1) (IsConj.symm hyconj))
  · refine ⟨e, ?_, hyeq⟩
    have hec : e * t = t * e :=
      sec8s_comm_of_conj hEel ht2 htord heE (hyeq ▸ hyconj)
    have hecent : e ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hec
    have : e ∈ E ⊓ centralizer ({t} : Set G) := ⟨heE, hecent⟩
    rwa [hcent] at this

private theorem sec8s_eq_one_of_odd_of_two_pow {G : Type} [Group G] {o a w : G}
    (hwa : w = a * o) (hcomm : a * w = w * a) (hodd : Odd (orderOf o))
    (ha : ∃ i, a ^ 2 ^ i = 1) (hw : ∃ j, w ^ 2 ^ j = 1) : o = 1 := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hw
  have hcomm_inv : Commute a⁻¹ w := (show Commute a w from hcomm).inv_left
  have ho_pow : o ^ 2 ^ (i + j) = 1 := by
    have ho : o = a⁻¹ * w := by rw [hwa]; group
    rw [ho, hcomm_inv.mul_pow]
    have h1 : (a⁻¹) ^ 2 ^ (i + j) = 1 := by
      rw [inv_pow, show (2 : ℕ) ^ (i + j) = 2 ^ i * 2 ^ j by rw [pow_add], pow_mul, hi]
      simp
    have h2 : w ^ 2 ^ (i + j) = 1 := by
      rw [show (2 : ℕ) ^ (i + j) = 2 ^ j * 2 ^ i by rw [pow_add, mul_comm], pow_mul, hj,
        one_pow]
    rw [h1, h2, mul_one]
  have hdiv : orderOf o ∣ 2 ^ (i + j) := orderOf_dvd_of_pow_eq_one ho_pow
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hm0 : m = 0 := by
    by_contra hmne
    have h2dvd : 2 ∣ orderOf o := by rw [hm]; exact dvd_pow_self 2 hmne
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  exact orderOf_eq_one_iff.mp (by rw [hm, hm0]; simp)

theorem asc82FinkSylow_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (hM : Asc82Tab6M)
    (h8A : Asc82Lemma8A) (h88b : Asc82Lemma88b) : Asc82FinkSylow := by
  intro G _ _ t L S z g B E hE
  classical
  have hctx : Sec8Ctx G t L S z g B := hE.ctx
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have htord : orderOf t = 2 := hS.involution
  have ht2 : t * t = 1 := by rw [← pow_two, ← htord, pow_orderOf_eq_one]
  have hEel : CFSG.Open.IsElemAbelian 2 E := hE.elem.1
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 8) hE.elem.2
  have hBE : B ≤ E := by rw [← hE.cent_t]; exact inf_le_left
  have hBS : B ≤ S := fun b hb => (hctx.B_le hb).2
  have hb_comm : ∀ b ∈ B, b * t = t * b := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 (hBS hb))
  have hbb : ∀ b ∈ B, b * b = 1 := fun b hb =>
    CFSG.Open.IsElemAbelian.mul_self_eq_one hctx.B_e16.1 hb
  have hKC : zpowers t ⊔ E ≤ centralizer (B : Set G) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 (hBS hb))
    · intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hEel.comm he (hBE hb)).symm
  have hK2 : IsPGroup 2 (zpowers t ⊔ E : Subgroup G) :=
    sec8s_sup_isPGroup ht2 htord hE.t_norm hE2
  have hnotconj : ¬ IsConj z t := sec8s_not_isConj_z_t h36 h37 hM hctx
  have h88bE : ∀ y ∈ E, IsConj t y → y ≠ 1 → IsConj z y := by
    intro y hyE hyconj hy1
    exact h88b G t L S z g B E hE y hyconj y
      ⟨hyE, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ hy1
  obtain ⟨P, hPsyl, hKP⟩ := sec68_exists_sylow_ge (H := centralizer (B : Set G)) hK2 hKC
  have hPleK : P ≤ zpowers t ⊔ E := by
    by_contra hnot
    let H : Subgroup ↥P := (zpowers t ⊔ E).subgroupOf P
    have hHne : H ≠ ⊤ := by
      intro htop
      apply hnot
      intro p hp
      have hpH : (⟨p, hp⟩ : ↥P) ∈ H := by rw [htop]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hpH
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent ↥P := hPsyl.2.1.isNilpotent
    have hnc : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent
    have hlt : H < Subgroup.normalizer H := hnc H (lt_of_le_of_ne le_top hHne)
    have hssub : (H : Set ↥P) ⊂ (Subgroup.normalizer (H : Set ↥P) : Set ↥P) := by
      rw [Set.ssubset_iff_subset_ne]
      exact ⟨Subgroup.le_normalizer, SetLike.coe_injective.ne hlt.ne⟩
    obtain ⟨x, hxnorm, hxH⟩ := Set.exists_of_ssubset hssub
    have hxK : (x : G) ∉ zpowers t ⊔ E := by
      intro hx
      exact hxH (Subgroup.mem_subgroupOf.mpr hx)
    have hxn : ∀ k ∈ zpowers t ⊔ E,
        (x : G) * k * (x : G)⁻¹ ∈ zpowers t ⊔ E := by
      intro k hk
      have hkH : (⟨k, hKP hk⟩ : ↥P) ∈ H := Subgroup.mem_subgroupOf.mpr hk
      have hconjH : x * ⟨k, hKP hk⟩ * x⁻¹ ∈ H :=
        (Subgroup.mem_normalizer_iff.mp hxnorm ⟨k, hKP hk⟩).mp hkH
      simpa using Subgroup.mem_subgroupOf.mp hconjH
    have hyK : (x : G) * t * (x : G)⁻¹ ∈ zpowers t ⊔ E :=
      hxn t (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
    have hyconj : IsConj t ((x : G) * t * (x : G)⁻¹) := isConj_iff.mpr ⟨(x : G), rfl⟩
    obtain ⟨b, hbB, hyb⟩ :=
      sec8s_class hEel hE.cent_t ht2 htord hE.t_norm h88bE hnotconj hyK hyconj
    obtain ⟨e, heE, heq⟩ := hE.comm_onto b hbB
    have hee : e * e = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hEel heE
    have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
    have hete : e * t * e = b * t := by
      have h := congrArg (fun z => z * t) heq
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      rw [hei, hti] at h
      simpa [mul_assoc, ht2] using h
    have hebe : e * b * e = b := by
      have hcomm : e * b = b * e := hEel.comm heE (hBE hbB)
      calc e * b * e = b * (e * e) := by rw [hcomm]; group
        _ = b := by rw [hee, mul_one]
    let w : G := e⁻¹ * (x : G)
    have hwconj : w * t * w⁻¹ = t := by
      have h1 : w * t * w⁻¹ = e⁻¹ * ((x : G) * t * (x : G)⁻¹) * e := by
        dsimp only [w]; group
      rw [h1, hyb, hei]
      calc e * (t * b) * e = (e * t * e) * (e * b * e) := by
            have h2 : (e * t * e) * (e * b * e) = e * t * (e * e) * b * e := by group
            rw [h2, hee]; group
        _ = (b * t) * b := by rw [hete, hebe]
        _ = t := by rw [hb_comm b hbB, mul_assoc, hbb b hbB, mul_one]
    have hwt : w * t = t * w := by
      have h := congrArg (fun z => z * w) hwconj
      simpa [mul_assoc] using h
    have heC : e⁻¹ ∈ centralizer (B : Set G) := by
      rw [hei]
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      exact (hEel.comm heE (hBE hb')).symm
    have hxGC : (x : G) ∈ centralizer (B : Set G) := hPsyl.1 x.2
    have hwC : w ∈ centralizer (B : Set G) := by
      show e⁻¹ * (x : G) ∈ centralizer (B : Set G)
      exact (centralizer (B : Set G)).mul_mem heC hxGC
    have hAcent : Asub8 t B ≤ Subgroup.centralizer ({w} : Set G) := by
      change zpowers t ⊔ B ≤ Subgroup.centralizer ({w} : Set G)
      refine sup_le ?_ ?_
      · rw [zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hwt.symm
      · intro b' hb'
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hwC b' hb')
    have hwA : w ∈ centralizer (Asub8 t B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hAcent ha)
    have heP : e ∈ P := hKP (Subgroup.mem_sup_right heE)
    have hwP : w ∈ P := by
      show e⁻¹ * (x : G) ∈ P
      exact P.mul_mem (P.inv_mem heP) x.2
    obtain ⟨jw, hjw⟩ := hPsyl.2.1 ⟨w, hwP⟩
    have hw2 : ∃ j, w ^ 2 ^ j = 1 := ⟨jw, by simpa using hjw⟩
    have h8A' := h8A G t L S z g B hctx
    have hCeq : Asub8 t B ⊔ oddCoreIn (Nsub8 t B) = centralizer (Asub8 t B : Set G) :=
      h8A'.1.trans h8A'.2
    have hwAO : w ∈ Asub8 t B ⊔ oddCoreIn (Nsub8 t B) := by
      rw [hCeq]; exact hwA
    have hOleA : oddCoreIn (Nsub8 t B) ≤ centralizer (Asub8 t B : Set G) := by
      rw [← hCeq]; exact le_sup_right
    have hcommAO : ∀ a ∈ Asub8 t B, ∀ o ∈ oddCoreIn (Nsub8 t B), a * o = o * a :=
      fun a ha o ho => Subgroup.mem_centralizer_iff.mp (hOleA ho) a ha
    obtain ⟨a, haA, o, hoO, hwo⟩ := exists_mul_of_mem_sup_of_commute hcommAO hwAO
    have hAK : Asub8 t B ≤ zpowers t ⊔ E := by
      change zpowers t ⊔ B ≤ zpowers t ⊔ E
      exact sup_le le_sup_left (hBE.trans le_sup_right)
    obtain ⟨ia, hia⟩ := hK2 ⟨a, hAK haA⟩
    have ha2 : ∃ i, a ^ 2 ^ i = 1 := ⟨ia, by simpa using hia⟩
    have hcomm_aw : a * w = w * a := by
      rw [hwo]
      exact ((Commute.refl a).mul_right (hcommAO a haA o hoO)).eq
    have hodd_o : Odd (orderOf o) := odd_orderOf_of_mem_oddCoreIn hoO
    have ho1 : o = 1 := sec8s_eq_one_of_odd_of_two_pow hwo hcomm_aw hodd_o ha2 hw2
    have hwa : w = a := by rw [hwo, ho1, mul_one]
    have hwK : w ∈ zpowers t ⊔ E := by rw [hwa]; exact hAK haA
    have heK : e ∈ zpowers t ⊔ E := Subgroup.mem_sup_right heE
    have hew : e * w = (x : G) := by dsimp only [w]; group
    have hxGK : (x : G) ∈ zpowers t ⊔ E := by
      have hmem : e * w ∈ zpowers t ⊔ E := (zpowers t ⊔ E).mul_mem heK hwK
      rwa [hew] at hmem
    exact hxK hxGK
  have hPK : P = (zpowers t ⊔ E : Subgroup G) := le_antisymm hPleK hKP
  rw [← hPK]
  exact hPsyl

end CFSG.OddStandard.SmallF3.Omega
