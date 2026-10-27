module

public import CFSG.LargeExtraspecial.AS62F431
public import CFSG.LargeExtraspecial.AS62Defs
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Holds
public import CFSG.LargeExtraspecial.AS62Iso2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Quasithin CFSG.Open AS62.Sem

namespace AS62

theorem code_cases : ∀ c < 16, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 15 ∨
    ∃ p : Equiv.Perm (Fin 5), Equiv.Perm.sign p = 1 ∧ actN (permCode p) c = 6 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

namespace ConfHyp

variable {S : Setting G} {H : Subgroup G}

theorem pCoreOf_H (hc : ConfHyp S H) : pCoreOf 2 H = closure (S.zConj H) := by
  obtain ⟨p, hp, hpz⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
  obtain ⟨L, -⟩ := hc.exists_label hp hpz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pCoreOf]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hP' : IsPGroup 2 ((CFSG.pCore 2 H).map L.σ) := CFSG.pCore_isPGroup.map _
    have hP'A : (CFSG.pCore 2 H).map L.σ ≤ alternatingGroup (Fin 5) :=
      L.range_σ hc.isAFive ▸ map_le_range _ _
    set N := ((CFSG.pCore 2 H).map L.σ).subgroupOf (alternatingGroup (Fin 5)) with hNdef
    have hN : N.Normal := ⟨fun n hn a => by
      rw [hNdef, mem_subgroupOf] at hn ⊢
      obtain ⟨q, hq, hqn⟩ := hn
      obtain ⟨h₀, hh₀⟩ : (a : Equiv.Perm (Fin 5)) ∈ L.σ.range :=
        (L.range_σ hc.isAFive).symm ▸ a.2
      refine ⟨h₀ * q * h₀⁻¹, CFSG.pCore_normal.conj_mem q hq h₀, ?_⟩
      rw [map_mul, map_mul, map_inv, hh₀, hqn]
      rfl⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
    · have hmem : (⟨L.σ x, hP'A ⟨x, hx, rfl⟩⟩ : alternatingGroup (Fin 5)) ∈ N :=
        mem_subgroupOf.mpr ⟨x, hx, rfl⟩
      rw [hb, mem_bot] at hmem
      exact (L.σ_eq_one_iff hc x).mp (congrArg Subtype.val hmem)
    · exfalso
      have hN2 : IsPGroup 2 N := hP'.comap_of_injective _ Subtype.val_injective
      obtain ⟨k, hk⟩ := hN2.exists_card_eq
      rw [ht, card_top, card_alternatingGroup_five] at hk
      have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  · intro v hv
    refine ⟨⟨v, hc.V_le hv⟩, ?_, rfl⟩
    have hN : ((closure (S.zConj H)).subgroupOf H).Normal := by
      rw [← L.ker_σ hc]
      infer_instance
    have hcard : Nat.card ((closure (S.zConj H)).subgroupOf H) = 2 ^ 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hc.V_le).toEquiv, hc.card_V]
      norm_num
    have hP : IsPGroup 2 ((closure (S.zConj H)).subgroupOf H) := IsPGroup.of_card hcard
    exact (le_sSup (show _ ∈ {K : Subgroup H | K.Normal ∧ IsPGroup 2 K} from ⟨hN, hP⟩) :
      _ ≤ CFSG.pCore 2 H) (mem_subgroupOf.mpr hv)

theorem centerOf_V (hc : ConfHyp S H) : centerOf (closure (S.zConj H)) = closure (S.zConj H) :=
  inf_eq_left.mpr fun _ hv => mem_centralizer_iff.mpr fun _ hw => hc.commute_V hw hv

end ConfHyp

namespace Gens

variable {S : Setting G} {H : Subgroup G} (g : Gens S H)

omit [Finite G] in
theorem zz_ne_z {i : Fin 5} (hi : i ≠ 0) : g.F.zz i ≠ S.z := by
  obtain ⟨L, hL⟩ := g.isFrameOf.label
  rw [hL]
  exact L.zz_ne_z hi

omit [Finite G] in
theorem vOf_six : g.F.vOf 6 = g.F.zz 1 * g.F.zz 2 :=
  g.F.eq_of_rep (g.F.rep_vOf (by decide))
    (g.F.rep_congr (g.F.rep_mul (g.F.rep_zz 1) (g.F.rep_zz 2)) (by decide))

theorem mem_zConj_of_mem_V (hc : ConfHyp S H) {v : G} (hv : v ∈ g.F.V) (hconj : IsConj S.z v) :
    v ∈ S.zConj H := by
  have hzz : ∀ i : Fin 5, g.F.vOf (colN i) ∈ S.zConj H := fun i =>
    (g.F.zz_eq_vOf i) ▸ g.isFrameOf.zz_mem i
  obtain ⟨c, hc16, rfl⟩ := g.F.exists_vOf hv
  rcases code_cases c hc16 with rfl | rfl | rfl | rfl | rfl | rfl | ⟨p, hp, hpc⟩
  · rw [g.F.vOf_zero] at hconj
    exact absurd (isConj_one_left.mp hconj) S.z_ne_one
  · exact hzz 0
  · exact hzz 1
  · exact hzz 2
  · exact hzz 3
  · exact hzz 4
  · exfalso
    obtain ⟨a, ha⟩ := g.F.exists_σ_eq (Equiv.Perm.mem_alternatingGroup.mpr hp)
    obtain ⟨k, hk⟩ := isConj_iff.mp hconj
    have h6 : ((a : G) * k) * S.z * ((a : G) * k)⁻¹ = g.F.zz 1 * g.F.zz 2 := by
      rw [← g.vOf_six, ← hpc, ← ha, ← g.F.conj_vOf, ← hk]
      group
    have hQ : g.F.zz 1 * g.F.zz 2 ∈ S.QG := hc.mul_mem_QG (g.isFrameOf.zz_mem 1)
      (g.zz_ne_z (by decide)) (g.isFrameOf.zz_mem 2) (g.zz_ne_z (by decide))
    have h7 := hc.hW ((a : G) * k) (by rw [h6]; exact hQ)
    rw [h6, ← g.vOf_six, ← g.isFrameOf.zz_zero, g.F.zz_eq_vOf 0] at h7
    exact absurd (g.F.vOf_injective (by decide) (by decide) h7) (by decide)

theorem normalizer_V (hc : ConfHyp S H) (h18 : Nat.card S.Mbar = 18) {y : G} (hy : g.IsY y) :
    normalizer (closure (S.zConj H) : Set G) = H := by
  rw [← g.isFrameOf.V_eq]
  set N := normalizer (g.F.V : Set G) with hNdef
  have hHF := g.isFrameOf.H_eq
  have hz : S.z ∈ g.F.V := g.isFrameOf.zz_zero ▸ g.F.zz_mem 0
  have hHN : H ≤ N := by
    intro h hh
    rw [hNdef, mem_normalizer_iff]
    intro v
    have hhF : h ∈ g.F.H := by rw [hHF]; exact hh
    refine ⟨fun hv => g.F.conj_mem_V hhF hv, fun hv => ?_⟩
    have h1 := g.F.conj_mem_V (g.F.H.inv_mem hhF) hv
    rwa [inv_inv, show h⁻¹ * (h * v * h⁻¹) * h = v by group] at h1
  have hyN : y ∉ N := by
    intro hyN
    have h1 := (mem_normalizer_iff.mp hyN _).mp g.b₁_mem_V
    rw [hy.conj_b₁] at h1
    apply g.e_not_mem_V
    have h2 := g.F.V.mul_mem (g.F.V.inv_mem hz) h1
    rwa [inv_mul_cancel_left] at h2
  have hNM : N ⊓ S.M ≤ S.M ⊓ H := by
    intro n hn
    by_contra hnB
    have hle := le_of_relIndex_prime_of_mem (B := S.M ⊓ H) (R := N ⊓ S.M) (P := S.M)
      (le_inf (inf_le_right.trans hHN) inf_le_left) inf_le_right
      (by rw [hc.relIndex_inf_M h18]; exact Nat.prime_three) hn hnB
    exact hyN (hle hy.mem_M).1
  have horb : {x | ∃ n ∈ N, n * S.z * n⁻¹ = x}.ncard ≤ 5 := by
    rw [← hc.ncard_zConj]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨n, hn, rfl⟩
    exact g.mem_zConj_of_mem_V hc ((mem_normalizer_iff.mp hn S.z).mp hz) (isConj_iff.mpr ⟨n, rfl⟩)
  have h1 := Setting.card_eq_relIndex_mul N S.M
  rw [Setting.relIndex_centralizer_eq_ncard] at h1
  have h2 : Nat.card ↥(N ⊓ S.M) ≤ 192 := (Subgroup.card_le_of_le hNM).trans hc.card_M_inf.le
  have hN960 : Nat.card N ≤ Nat.card H := by
    rw [h1, hc.card_H]
    calc _ ≤ 5 * 192 := Nat.mul_le_mul horb h2
      _ = 960 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hHN hN960).symm

theorem normalizer_centerOf_pCoreOf_H (hc : ConfHyp S H) (h18 : Nat.card S.Mbar = 18) {y : G}
    (hy : g.IsY y) : normalizer (centerOf (pCoreOf 2 H) : Set G) = H := by
  rw [hc.pCoreOf_H, hc.centerOf_V]
  exact g.normalizer_V hc h18 hy

end Gens

section F431


theorem Gens.lieModel_of_isY {S : Setting G} {H : Subgroup G} (g : Gens S H) (hc : ConfHyp S H)
    (htop : S.zGen ⊔ S.QG = ⊤) (hsimp : IsSimpleGroup S.zGen) (h18 : Nat.card S.Mbar = 18)
    {y : G} (hy : g.IsY y) :
    Blueprint.LieModel G .PSU 4 2 1 ∨ Blueprint.LieModel G .PSL 4 3 1 :=
  Quasithin.H13.F431.U42.stmtF431U42_holds G (hc.isSimpleGroup htop hsimp)
    hc.exists_not_commute S.M H S.z (Or.inl (g.isAmalgamOfGroup hc h18 hy))
    hc.pCoreOf_sup_eq_bot (by rw [pow_two]; exact S.z_mul_z) S.z_ne_one hc.z_mem_centerOf_inf
    le_rfl (normalizer_centerOf_pCoreOf_M S) (g.normalizer_centerOf_pCoreOf_H hc h18 hy)

theorem ConfHyp.lieModel {S : Setting G} {H : Subgroup G} (hc : ConfHyp S H)
    (htop : S.zGen ⊔ S.QG = ⊤) (hsimp : IsSimpleGroup S.zGen) (h18 : Nat.card S.Mbar = 18) :
    Blueprint.LieModel G .PSU 4 2 1 ∨ Blueprint.LieModel G .PSL 4 3 1 := by
  obtain ⟨g⟩ := hc.exists_gens
  obtain ⟨y, hy⟩ := g.exists_isY hc h18
  exact g.lieModel_of_isY hc htop hsimp h18 hy

theorem lieModel (S : Setting G) (h22 : S14.AschbacherTwoTwoStmt) (h : W2Hyp S)
    (htop : S.zGen ⊔ S.QG = ⊤) {H : Subgroup G} (hH : S.IsHStar H)
    (h18 : Nat.card S.Mbar = 18) :
    Blueprint.LieModel G .PSU 4 2 1 ∨ Blueprint.LieModel G .PSL 4 3 1 :=
  (ConfHyp.mk h22 h.hw h.hW hH).lieModel htop h.hsimp h18

end F431

end AS62

end CFSG.LargeExtraspecial
