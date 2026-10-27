module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec710Kap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec710_quot_E16 [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) (hF : Asc82AutFacts)
    (hP7 : Asc82Tab7P) (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710b : Asc82Lemma710b)
    (h710c : Asc82Lemma710c) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    QuotEquivTo (MSub S B ⊓ centralizer (B : Set G)) (centralizer (ASub S B : Set G)) E16 := by
  obtain ⟨κ, hκ⟩ := sec710_exists_kap hP h78 h710c hc
  have hsurj := sec710_kap_surj h36 hP hF hP7 h77b h78 h710b h710c hc hκ
  have hker := sec710_kap_eq_one_iff h78 hc hκ
  have hL : IsOm6P L := hc.ctx.isOm6P
  obtain ⟨φ, hφ⟩ :=
    (hP.aut_B G L hL (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B hc.normalE16).2.2
  obtain ⟨e⟩ := sec710_equiv_E16 hφ
  refine ⟨e.toMonoidHom.comp κ, e.surjective.comp hsurj, ?_⟩
  ext k
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff e]
  exact hker k

theorem sec710_trans_tB [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) (hF : Asc82AutFacts)
    (hP7 : Asc82Tab7P) (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710b : Asc82Lemma710b)
    (h710c : Asc82Lemma710c) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    ∀ x ∈ cosetSet t B, ∀ y ∈ cosetSet t B,
      ∃ n ∈ MSub S B ⊓ centralizer (B : Set G), n * x * n⁻¹ = y := by
  obtain ⟨κ, hκ⟩ := sec710_exists_kap hP h78 h710c hc
  have hsurj := sec710_kap_surj h36 hP hF hP7 h77b h78 h710b h710c hc hκ
  intro x hx y hy
  obtain ⟨b1, hb1, rfl⟩ := hx
  obtain ⟨b2, hb2, rfl⟩ := hy
  have hb : b2 * b1⁻¹ ∈ B := B.mul_mem hb2 (B.inv_mem hb1)
  obtain ⟨k, hk⟩ := hsurj ⟨b2 * b1⁻¹, hb⟩
  refine ⟨(k : G), k.2, ?_⟩
  have hkval : (κ k : G) = b2 * b1⁻¹ := congrArg Subtype.val hk
  have hκk := hκ k
  rw [hkval] at hκk
  have hkt : (k : G) * t * (k : G)⁻¹ = (b2 * b1⁻¹) * t := by
    rw [hκk]
    group
  have hkb : (k : G) * b1 * (k : G)⁻¹ = b1 := by
    have hc1 : b1 * (k : G) = (k : G) * b1 :=
      Subgroup.mem_centralizer_iff.mp k.2.2 b1 hb1
    rw [hc1.symm]
    group
  have htb : t * (b2 * b1⁻¹) = (b2 * b1⁻¹) * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (hc.ctx.sylow.1 (hc.normalE16.1 hb).1)).symm
  calc (k : G) * (t * b1) * (k : G)⁻¹
      = ((k : G) * t * (k : G)⁻¹) * ((k : G) * b1 * (k : G)⁻¹) := by group
    _ = ((b2 * b1⁻¹) * t) * b1 := by rw [hkt, hkb]
    _ = t * b2 := by
        rw [← htb]
        group

theorem sec710_stab_tB [Finite G] (h78 : Asc82Lemma78) (hP : Asc82Tab6P)
    (h710c : Asc82Lemma710c) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    ∀ n ∈ MSub S B ⊓ centralizer (B : Set G), ∀ x ∈ cosetSet t B,
      n * x * n⁻¹ = x → n ∈ centralizer (ASub S B : Set G) := by
  obtain ⟨κ, hκ⟩ := sec710_exists_kap hP h78 h710c hc
  have hker := sec710_kap_eq_one_iff h78 hc hκ
  intro n hn x hx hfix
  obtain ⟨b, hb, rfl⟩ := hx
  have hnb : n * b * n⁻¹ = b := by
    have hc1 : b * n = n * b := Subgroup.mem_centralizer_iff.mp hn.2 b hb
    rw [hc1.symm]
    group
  have h2 : n * (t * b) * n⁻¹ = (n * t * n⁻¹) * (n * b * n⁻¹) := by group
  rw [hnb] at h2
  have hnt : n * t * n⁻¹ = t :=
    mul_right_cancel (h2.symm.trans hfix)
  have hκn : κ ⟨n, hn⟩ = 1 := by
    apply Subtype.ext
    rw [hκ ⟨n, hn⟩, hnt]
    simp
  exact (hker ⟨n, hn⟩).mp hκn

theorem asc82Lemma710d_of (h36 : Asc82Lemma36) (hP : Asc82Tab6P) (hF : Asc82AutFacts)
    (hP7 : Asc82Tab7P) (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710b : Asc82Lemma710b)
    (h710c : Asc82Lemma710c) : Asc82Lemma710d := by
  intro G _ _ t L S z g B hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sec710_M_eq_K_sup_N h36 hP hF hP7 h78 h710b h710c hc
  · intro N₀ hN₀M hN₀ hC hk
    exact sec710_normal_two h36 hP hF hP7 h78 h710b h710c hc hN₀M hN₀ hC hk
  · exact sec710_quot_E16 h36 hP hF hP7 h77b h78 h710b h710c hc
  · intro x hx
    rw [Set.mem_inter_iff, Set.mem_setOf_eq]
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · obtain ⟨n, _, heq⟩ :=
        sec710_trans_tB h36 hP hF hP7 h77b h78 h710b h710c hc t
          ⟨1, B.one_mem, (mul_one t).symm⟩ (t * b) ⟨b, hb, rfl⟩
      exact isConj_iff.mpr ⟨n, heq⟩
    · exact (ASub S B).mul_mem (sec79_t_mem_A hc) (sec79_B_le_A hc hb)
  · exact sec710_trans_tB h36 hP hF hP7 h77b h78 h710b h710c hc
  · exact sec710_stab_tB h78 hP h710c hc

end CFSG.OddStandard.SmallF3.Omega
