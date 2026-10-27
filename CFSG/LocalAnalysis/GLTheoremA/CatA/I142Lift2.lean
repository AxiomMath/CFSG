module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Abs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_self_eq_of_commutator_eq_top {Q : Type*} [Group Q] {M : Subgroup Q}
    (h : commutator M = ⊤) : ⁅M, M⁆ = M := by
  have h1 : (⁅(⊤ : Subgroup M), ⊤⁆ : Subgroup M) = ⊤ := h
  have h2 := Subgroup.map_commutator (⊤ : Subgroup M) (⊤ : Subgroup M) M.subtype
  rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h2.symm

theorem commutator_eq_top_of_comm_self {Q : Type*} [Group Q] {M : Subgroup Q}
    (h : ⁅M, M⁆ = M) : commutator M = ⊤ := by
  apply Subgroup.map_injective (f := M.subtype) M.subtype_injective
  show Subgroup.map M.subtype ⁅(⊤ : Subgroup M), ⊤⁆ = Subgroup.map M.subtype ⊤
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact h

theorem commutator_mul_central {Q : Type*} [Group Q] {x y a b : Q}
    (ha : a ∈ Subgroup.center Q) (hb : b ∈ Subgroup.center Q) : ⁅x * a, y * b⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_center_left ha, commutatorElement_mul_center_right hb]

theorem barAut_commutator_fixed {p : ℕ} {K E : Subgroup G} {x y : PQuot p K}
    (hx : ∀ γ ∈ E.subgroupOf (Subgroup.normalizer (K : Set G)),
      QuotientGroup.mk' (Subgroup.center (PQuot p K)) (barAut p K γ x) =
        QuotientGroup.mk' (Subgroup.center (PQuot p K)) x)
    (hy : ∀ γ ∈ E.subgroupOf (Subgroup.normalizer (K : Set G)),
      QuotientGroup.mk' (Subgroup.center (PQuot p K)) (barAut p K γ y) =
        QuotientGroup.mk' (Subgroup.center (PQuot p K)) y)
    (γ : ↥(Subgroup.normalizer (K : Set G)))
    (hγ : γ ∈ E.subgroupOf (Subgroup.normalizer (K : Set G))) :
    barAut p K γ ⁅x, y⁆ = ⁅x, y⁆ := by
  have hx' := QuotientGroup.eq.1 (hx γ hγ)
  have hy' := QuotientGroup.eq.1 (hy γ hγ)
  obtain ⟨c, hc, hcx⟩ : ∃ c ∈ Subgroup.center (PQuot p K),
      barAut p K γ x = x * c :=
    ⟨((barAut p K γ x)⁻¹ * x)⁻¹, Subgroup.inv_mem _ hx', by group⟩
  obtain ⟨d, hd, hdy⟩ : ∃ d ∈ Subgroup.center (PQuot p K),
      barAut p K γ y = y * d :=
    ⟨((barAut p K γ y)⁻¹ * y)⁻¹, Subgroup.inv_mem _ hy', by group⟩
  rw [map_commutatorElement, hcx, hdy, commutator_mul_central hc hd]

theorem cbar_le_centFix {p : ℕ} {K E : Subgroup G} (x : PQuot p K) (hx : x ∈ Cbar p K E) :
    QuotientGroup.mk' (Subgroup.center (PQuot p K)) x ∈ centFix (Ebar p K E) := by
  rw [mem_centFix_mk_iff]
  intro γ hγ
  rw [barAut_fixed_of_mem_Cbar hx γ (Subgroup.mem_subgroupOf.1 hγ)]

theorem glaPLayer_ne_bot_of_component [Finite G] {p : ℕ} [hp : Fact p.Prime] {K E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (K : Set G)) (hE : IsElemAbelian p E)
    {M : Subgroup (PSimple p K)} (hM : CFSG.Open.IsComponentOf M (centFix (Ebar p K E)))
    (hpM : p ∣ Nat.card ↥M) :
    GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ := by
  classical
  let π : PQuot p K →* PSimple p K := QuotientGroup.mk' (Subgroup.center (PQuot p K))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let H : Subgroup (PSimple p K) := centFix (Ebar p K E)
  let Mq : Subgroup (PQuot p K) := M.comap π
  let Dq : Subgroup (PQuot p K) := ⁅Mq, Mq⁆
  have hMq_fix : ∀ x ∈ Mq, ∀ γ ∈ E.subgroupOf (Subgroup.normalizer (K : Set G)),
      QuotientGroup.mk' (Subgroup.center (PQuot p K)) (barAut p K γ x) =
        QuotientGroup.mk' (Subgroup.center (PQuot p K)) x := by
    intro x hx γ hγ
    have hxH : π x ∈ H := hM.1 (Subgroup.mem_comap.1 hx)
    exact (mem_centFix_mk_iff p K E x).1 hxH γ hγ
  have hDq_le : Dq ≤ Cbar p K E := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    refine mem_Cbar_of_fixed hEN hE fun γ hγ => ?_
    exact barAut_commutator_fixed (hMq_fix x hx) (hMq_fix y hy) γ hγ
  have hMq_sub : CFSG.Open.IsSubnormal Mq (H.comap π) := isSubnormal_comap' π hM.2.1
  have hDq_Mq : CFSG.Open.IsSubnormal Dq Mq := by
    refine CFSG.Open.IsSubnormal.step ?_ ?_ (CFSG.Open.IsSubnormal.refl Mq)
    · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact Mq.mul_mem (Mq.mul_mem (Mq.mul_mem ha hb) (Mq.inv_mem ha)) (Mq.inv_mem hb)
    · show (⁅Mq, Mq⁆ : Subgroup (PQuot p K)).subgroupOf Mq |>.Normal
      rw [subgroupOf_commutator le_rfl le_rfl, Subgroup.subgroupOf_self]
      exact Subgroup.commutator_normal ⊤ ⊤
  have hDq_M : CFSG.Open.IsSubnormal Dq (H.comap π) :=
    CFSG.LocalAnalysis.GLTheoremB.isSubnormal_trans' hDq_Mq hMq_sub
  have hCb_le : Cbar p K E ≤ H.comap π := fun x hx => Subgroup.mem_comap.2 (cbar_le_centFix x hx)
  have hDq_Cb : CFSG.Open.IsSubnormal Dq (Cbar p K E) :=
    isSubnormal_of_le_of_le hDq_M hDq_le hCb_le
  have hMq_map : Mq.map π = M := Subgroup.map_comap_eq_self_of_surjective hπ M
  have hMperf : ⁅M, M⁆ = M := comm_self_eq_of_commutator_eq_top hM.2.2.1
  have hDq_map : Dq.map π = M := by
    show (⁅Mq, Mq⁆ : Subgroup (PQuot p K)).map π = M
    rw [Subgroup.map_commutator, hMq_map, hMperf]
  have hDq_sub_M : ∀ x ∈ Dq, π x ∈ M := fun x hx => by
    have := Subgroup.mem_map_of_mem π hx
    rwa [hDq_map] at this
  have hM_sub_Dq : ∀ m ∈ M, ∃ x ∈ Dq, π x = m := fun m hm => by
    have hm' : m ∈ Dq.map π := by rw [hDq_map]; exact hm
    obtain ⟨x, hx, hxm⟩ := Subgroup.mem_map.1 hm'
    exact ⟨x, hx, hxm⟩
  have hMq_decomp : ∀ x ∈ Mq, ∃ d ∈ Dq, ∃ z ∈ Subgroup.center (PQuot p K), x = d * z := by
    intro x hx
    obtain ⟨d, hd, hdx⟩ := hM_sub_Dq (π x) (Subgroup.mem_comap.1 hx)
    have hz : d⁻¹ * x ∈ Subgroup.center (PQuot p K) := QuotientGroup.eq.1 hdx
    exact ⟨d, hd, d⁻¹ * x, hz, by group⟩
  have hDq_comm : ⁅Dq, Dq⁆ = Dq := by
    apply le_antisymm
    · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact Dq.mul_mem (Dq.mul_mem (Dq.mul_mem ha hb) (Dq.inv_mem ha)) (Dq.inv_mem hb)
    · show (⁅Mq, Mq⁆ : Subgroup (PQuot p K)) ≤ ⁅Dq, Dq⁆
      refine Subgroup.commutator_le.2 fun x hx y hy => ?_
      obtain ⟨dx, hdx, zx, hzx, rfl⟩ := hMq_decomp x hx
      obtain ⟨dy, hdy, zy, hzy, rfl⟩ := hMq_decomp y hy
      rw [commutator_mul_central hzx hzy]
      exact Subgroup.commutator_mem_commutator hdx hdy
  have hDq_top : commutator ↥Dq = ⊤ := commutator_eq_top_of_comm_self hDq_comm
  let f : ↥Dq →* ↥M := (π.comp Dq.subtype).codRestrict M (fun x => hDq_sub_M x x.2)
  have hf : Function.Surjective f := by
    intro m
    obtain ⟨x, hx, hxm⟩ := hM_sub_Dq m.1 m.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxm⟩
  have hfker : f.ker ≤ Subgroup.center ↥Dq := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : π x.1 = 1 := congrArg Subtype.val hx
    have hxc : x.1 ∈ Subgroup.center (PQuot p K) := (QuotientGroup.eq_one_iff _).1 hx'
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 hxc g.1)
  have hq : CFSG.Open.IsQuasisimple ↥Dq := isQuasisimple_of_surj_central f hf hfker hDq_top hM.2.2
  have hpD : p ∣ Nat.card ↥Dq := dvd_trans hpM (Subgroup.card_dvd_of_surjective hf)
  have hOt : GLAPPrimeCore p ↥Dq ≠ ⊤ := by
    intro h
    have h1 : Nat.Coprime p (Nat.card ↥(GLAPPrimeCore p ↥Dq)) := CFSG.pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at h1
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 h1 hpD
  have hOc : GLAPPrimeCore p ↥Dq ≤ Subgroup.center ↥Dq :=
    le_center_of_normal_of_isQuasisimple hq inferInstance hOt
  have hquot : CFSG.Open.IsQuasisimple (↥Dq ⧸ GLAPPrimeCore p ↥Dq) :=
    isQuasisimple_quot_of_le_center hq (GLAPPrimeCore p ↥Dq) hOc hOt
  obtain ⟨hΛc, -, hΛbar⟩ := glaPLayer_of_isQuasisimple hquot
  have hΛne : GLAPLayer p Dq ≠ ⊥ := by
    intro h
    have hb := hΛbar
    rw [h, barX, Subgroup.bot_subgroupOf, Subgroup.map_bot] at hb
    haveI := isQuasisimple_nontrivial hquot
    exact (bot_ne_top : (⊥ : Subgroup (↥Dq ⧸ GLAPPrimeCore p ↥Dq)) ≠ ⊤) hb
  have hΛcomp : GLAPComponent p (Cbar p K E) (GLAPLayer p Dq) :=
    glaPComponent_of_isSubnormal' hp.out hDq_Cb hΛc
  obtain ⟨K₀, hK₀, hK₀map⟩ := exists_glaPComponent_map_eq hp.out (pQuotHom p K)
    (A := (K ⊓ Subgroup.centralizer (E : Set G)).subgroupOf K)
    (coprime_card_inf_ker_pQuotHom hp.out K _) hΛcomp
  have hK₀ne : K₀ ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.map_bot] at hK₀map
    exact hΛne hK₀map.symm
  have hker : p.Coprime (Nat.card ↥(((K ⊓ Subgroup.centralizer (E : Set G)).subgroupOf K) ⊓
      K.subtype.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff K.subtype).2 K.subtype_injective, inf_bot_eq,
      Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hG := glaPComponent_map hp.out K.subtype hker hK₀
  have hA : Subgroup.map K.subtype ((K ⊓ Subgroup.centralizer (E : Set G)).subgroupOf K) =
      K ⊓ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 inf_le_left
  rw [hA] at hG
  have hJne : Subgroup.map K.subtype K₀ ≠ ⊥ := by
    intro h
    exact hK₀ne (Subgroup.map_injective K.subtype_injective (h.trans (Subgroup.map_bot K.subtype).symm))
  intro hbot
  have hJle : Subgroup.map K.subtype K₀ ≤ GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set G)) :=
    le_sSup hG
  rw [hbot] at hJle
  exact hJne (le_bot_iff.1 hJle)

end CFSG.LocalAnalysis.GLTheoremA.I142
