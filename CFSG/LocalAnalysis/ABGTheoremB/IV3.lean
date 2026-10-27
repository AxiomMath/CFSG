module

public import CFSG.LocalAnalysis.ABGTheoremB.IV1
public import CFSG.LocalAnalysis.ABGTheoremB.Statements
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

universe u

section General

variable {G : Type u} [Group G]

private theorem normalizer_le_normalizer_centralizer_aux (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc r hr
    have hrn : n⁻¹ * r * n ∈ R := by
      have h := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (R : Set G)).inv_mem hn)
        r).mp hr
      simpa using h
    have h := hc _ hrn
    calc r * (n * c * n⁻¹) = n * ((n⁻¹ * r * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * r * n)) * n⁻¹ := by rw [h]
      _ = n * c * n⁻¹ * r := by group
  · intro hc r hr
    have hrn : n * r * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn r).mp hr
    have h := hc _ hrn
    calc r * c = n⁻¹ * ((n * r * n⁻¹) * (n * c * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * c * n⁻¹) * (n * r * n⁻¹)) * n := by rw [h]
      _ = c * r := by group

private theorem le_sup_inf_normalizer_of_isSylowOf [Finite G] {r : ℕ} [Fact r.Prime]
    {H K P : Subgroup G} (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hP : IsSylowOf r P K) :
    H ≤ K ⊔ (H ⊓ Subgroup.normalizer (P : Set G)) := by
  intro h hh
  set P' : Subgroup G := P.map (MulAut.conj h).toMonoidHom with hP'
  have hmem : ∀ y : G, y ∈ P' ↔ h⁻¹ * y * h ∈ P := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have e : h⁻¹ * ((MulAut.conj h).toMonoidHom z) * h = z := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hz
    · intro hy
      refine ⟨h⁻¹ * y * h, hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hP'K : P' ≤ K := by
    rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHK hh) z).mp (hP.le hz)
  have hP'syl : IsSylowOf r P' K := by
    refine isSylowOf_of_card hP'K ?_
    rw [hP', Subgroup.card_map_of_injective (MulAut.conj h).injective]
    exact hP.card_eq
  obtain ⟨k, hk, hconj⟩ := hP.exists_mem_conj hP'syl
  have hn : k⁻¹ * h ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e1 : (k⁻¹ * h) * y * (k⁻¹ * h)⁻¹ = k⁻¹ * (h * y * h⁻¹) * k := by group
    have e2 : h⁻¹ * (h * y * h⁻¹) * h = y := by group
    rw [e1, ← hconj, hmem, e2]
  have hkh : k⁻¹ * h ∈ H := H.mul_mem (H.inv_mem (hKH hk)) hh
  have e : h = k * (k⁻¹ * h) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right ⟨hkh, hn⟩)

private theorem exists_isSylowOf_ge_aux {p : ℕ} {Q K : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ P : Subgroup G, IsSylowOf p P K ∧ Q ≤ P := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K) : IsPGroup p (Q.subgroupOf K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, ?_⟩
  intro q hq
  exact ⟨⟨q, hQK hq⟩, hS (show (⟨q, hQK hq⟩ : K) ∈ Q.subgroupOf K from hq), rfl⟩

private theorem inf_centerOf_ne_bot_aux [Finite G] {p : ℕ} [Fact p.Prime] {P X : Subgroup G}
    (hP : IsPGroup p P) (hXP : X ≤ P) (hnorm : P ≤ Subgroup.normalizer (X : Set G))
    (hX : X ≠ ⊥) : X ⊓ centerOf P ≠ ⊥ := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have : (X.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXP).mpr hnorm
  have hY : X.subgroupOf P ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot, disjoint_of_le_iff_left_eq_bot hXP]
    exact hX
  intro hbot
  apply Group.IsNilpotent.inf_center_ne_bot_of_normal hY
  rw [eq_bot_iff]
  rintro a ⟨haX, haZ⟩
  have hmem : (a : G) ∈ X ⊓ centerOf P := by
    refine ⟨haX, a.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp haZ ⟨g, hg⟩)
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact Subtype.ext hmem

private theorem eq_one_of_mem_of_mem_of_odd_aux [Finite G] {A B : Subgroup G}
    (hA : IsPGroup 2 A) (hB : Odd (Nat.card B)) {g : G} (hgA : g ∈ A) (hgB : g ∈ B) :
    g = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA ⟨g, hgA⟩
  have h1 : orderOf g = 2 ^ k := by rw [← Subgroup.orderOf_mk g hgA]; exact hk
  have h2 : orderOf g ∣ Nat.card B := Subgroup.orderOf_dvd_natCard B hgB
  rw [h1] at h2
  have hk0 : k = 0 := by
    by_contra hk0
    exact hB.not_two_dvd_nat ((dvd_pow_self 2 hk0).trans h2)
  rw [hk0, pow_zero] at h1
  exact orderOf_eq_one_iff.mp h1

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

private theorem normalizer_mem_familyL_aux (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    (hdiv : r ∣ Nat.card σ.ON) {R : Subgroup G} (hR : IsSylowOf r R σ.ON)
    (hDR : σ.D ≤ Subgroup.normalizer (R : Set G)) :
    Subgroup.normalizer (R : Set G) ∈ σ.familyL r := by
  have : Fact r.Prime := ⟨hr⟩
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hcard := hR.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hpos := hr.factorization_pos_of_dvd Nat.card_pos.ne' hdiv
    have := Nat.one_lt_pow hpos.ne' hr.one_lt
    omega
  have hfr : σ.N ≤ σ.ON ⊔ (σ.N ⊓ Subgroup.normalizer (R : Set G)) :=
    le_sup_inf_normalizer_of_isSylowOf σ.ON_le_N σ.N_le_normalizer_ON hR
  refine ⟨⟨R, hRne, hR.isPGroup, rfl⟩, ?_, hDR, R, hR, Subgroup.le_normalizer⟩
  intro l hl
  have h1 := hfr (hσ.L₀_le_N hl)
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (inf_le_left.trans σ.N_le_normalizer_ON)] at h1
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  exact ⟨a, ha.2, b, hb, rfl⟩

private theorem exists_sylow_two_normalizing_aux (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON) {H : Subgroup G} (hH : H ∈ σ.familyL r)
    {Rs : Subgroup G} (hRs : IsSylowOf r Rs (oddCoreIn H))
    (hDRs : σ.D ≤ Subgroup.normalizer (Rs : Set G)) :
    ∃ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) ∧ IsSylowOf 2 (S₁ : Subgroup G) H ∧
      (S₁ : Subgroup G) ≤ Subgroup.normalizer (Rs : Set G) ∧
      IsSylowOf 2 ((S₁ : Subgroup G) ⊓ (H ⊓ Subgroup.centralizer (Rs : Set G)))
        (H ⊓ Subgroup.centralizer (Rs : Set G)) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, ⟨P, hPH⟩, -, -⟩ := σ.familyL_properties hσ hII hr hdiv hH
  have hDH : σ.D ≤ H := hH.2.2.1
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  obtain ⟨S₀, hS₀, hDS₀⟩ := exists_isSylowOf_ge_aux (le_inf hDH hDRs) hD2
  have hfr : H ≤ oddCoreIn H ⊔ (H ⊓ Subgroup.normalizer (Rs : Set G)) :=
    le_sup_inf_normalizer_of_isSylowOf (oddCoreIn_le H) (le_normalizer_oddCoreIn H) hRs
  have hK₁idx : ¬ 2 ∣ (H ⊓ Subgroup.normalizer (Rs : Set G)).relIndex H := by
    have h1 := relIndex_sup_eq_relIndex_of_le_normalizer
      (inf_le_left.trans (le_normalizer_oddCoreIn H) :
        H ⊓ Subgroup.normalizer (Rs : Set G) ≤ Subgroup.normalizer (oddCoreIn H : Set G))
    rw [le_antisymm (sup_le (oddCoreIn_le H) inf_le_left) hfr] at h1
    rw [h1]
    exact fun h2 =>
      (odd_card_oddCoreIn H).not_two_dvd_nat (h2.trans (Subgroup.relIndex_dvd_card _ _))
  have hS₀H : IsSylowOf 2 S₀ H := by
    rw [isSylowOf_iff] at hS₀ ⊢
    refine ⟨hS₀.1.trans inf_le_left, hS₀.2.1, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex S₀ _ H hS₀.1 inf_le_left]
    exact Nat.prime_two.not_dvd_mul hS₀.2.2 hK₁idx
  have hidx : ¬ 2 ∣ S₀.index := by
    rw [← Subgroup.relIndex_mul_index hS₀H.le]
    have hHidx : ¬ 2 ∣ H.index := fun h =>
      P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le (hPH.trans inf_le_left)))
    exact Nat.prime_two.not_dvd_mul (isSylowOf_iff.mp hS₀H).2.2 hHidx
  refine ⟨hS₀.isPGroup.toSylow hidx, ?_, ?_, ?_, ?_⟩ <;> rw [IsPGroup.toSylow_coe]
  · exact hDS₀
  · exact hS₀H
  · exact hS₀.le.trans inf_le_right
  · refine hS₀.inf_of_le_normalizer (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)) ?_
    exact (le_inf (inf_le_left.trans Subgroup.le_normalizer)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer_aux Rs))).trans
        Subgroup.inf_normalizer_le_normalizer_inf

theorem lemmaIV33 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) : σ.LemmaIV33 := by
  intro r hr hdiv H hH R Rs hR _ _ hRs hDRs hlt
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr hdiv
  have hcov : (σ.L₀ : Set G) ⊆ (H : Set G) * (σ.ON : Set G) := hH.2.1
  have hO : oddCoreIn H ≠ ⊥ := oddCoreIn_ne_bot_of_isPLocal hr hr2 hH.1
  have hRsN : ¬ Rs ≤ σ.N := by
    intro hle
    have hRsON : Rs ≤ σ.ON :=
      (le_inf hRs.le hle).trans (σ.oddCoreIn_inf_N_le_ON_of_cover hσ hII hcov)
    exact hlt.ne (hR.eq_of_le hlt.le hRsON hRs.isPGroup).symm
  obtain ⟨S₁, hDS₁, hS₁H, hS₁Rs, hsyl⟩ :=
    σ.exists_sylow_two_normalizing_aux hσ hII hr hdiv hH hRs hDRs
  set X : Subgroup G := (S₁ : Subgroup G) ⊓ (H ⊓ Subgroup.centralizer (Rs : Set G))
  have hX : X = ⊥ := by
    by_contra hne
    have hXS : X ≤ S₁ := inf_le_left
    have hnorm : (S₁ : Subgroup G) ≤ Subgroup.normalizer (X : Set G) :=
      (le_inf Subgroup.le_normalizer ((le_inf (hS₁H.le.trans Subgroup.le_normalizer)
        (hS₁Rs.trans (normalizer_le_normalizer_centralizer_aux Rs))).trans
          Subgroup.inf_normalizer_le_normalizer_inf)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hW := inf_centerOf_ne_bot_aux S₁.isPGroup' hXS hnorm hne
    have hW2 : IsPGroup 2 (X ⊓ centerOf (S₁ : Subgroup G) : Subgroup G) :=
      S₁.isPGroup'.to_le (inf_le_left.trans hXS)
    have hdvd : 2 ∣ Nat.card (X ⊓ centerOf (S₁ : Subgroup G) : Subgroup G) :=
      hW2.card_eq_or_dvd.resolve_left fun h => hW (Subgroup.card_eq_one.mp h)
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hzx : (z : G) = σ.x := (hII.center_involution_of_sylow S₁ hDS₁).2 z
      (Subgroup.mem_inf.mp z.2).2 (by rw [Subgroup.orderOf_coe]; exact hz)
    have hxC : σ.x ∈ Subgroup.centralizer (Rs : Set G) := by
      rw [← hzx]
      exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp z.2).1).2).2
    apply hRsN
    intro y hy
    rw [σ.mem_N_iff]
    exact (Subgroup.mem_centralizer_iff.mp hxC) y hy
  rw [hX] at hsyl
  have hodd : Odd (Nat.card (H ⊓ Subgroup.centralizer (Rs : Set G) : Subgroup G)) := by
    have h := (isSylowOf_iff.mp hsyl).2.2
    rw [Subgroup.relIndex_bot_left] at h
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  exact ((hII.qgroup_constraint_criterion H hH.2.2.1 hO hcov S₁ hS₁H r hr hr2 Rs hRs
    hS₁Rs).2).mpr hodd

theorem lemmaIV32 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (h_IV21 : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ∀ R : Subgroup G, IsSylowOf r R σ.ON →
      (σ.Constrained r ↔ σ.N ⊓ Subgroup.centralizer (R : Set G) ≤ solvRadIn σ.N))
    (h_P21 : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON →
      (σ.Ordinary r ↔ σ.Stationary r ∧ ¬ σ.Constrained r)) :
    σ.LemmaIV32 := by
  intro r hr hdiv hexc R hR hDR
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr hdiv
  have hHL := σ.normalizer_mem_familyL_aux hσ hr hdiv hR hDR
  refine ⟨hHL, ?_⟩
  set H : Subgroup G := Subgroup.normalizer (R : Set G)
  have hcov : (σ.L₀ : Set G) ⊆ (H : Set G) * (σ.ON : Set G) := hHL.2.1
  have hO : oddCoreIn H ≠ ⊥ := oddCoreIn_ne_bot_of_isPLocal hr hr2 hHL.1
  have hRodd : Odd (Nat.card R) := σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le hR.le)
  have hRH : R ≤ oddCoreIn H := le_oddCoreIn Subgroup.le_normalizer le_rfl hRodd
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  obtain ⟨Rs, hRs, hRRs, hDRs⟩ := exists_isSylowOf_normalized_ge_of_odd hr hD2
    (hHL.2.2.1.trans (le_normalizer_oddCoreIn H)) (odd_card_oddCoreIn H) hRH hR.isPGroup hDR
  by_cases hcon : σ.Constrained r
  ·
    have hCN : σ.N ⊓ Subgroup.centralizer (R : Set G) ≤ σ.ON ⊔ centerOf σ.D := by
      have h := (h_IV21 r hr hdiv R hR).mp hcon
      rwa [hII.N_solvRad, hII.center_S_eq_center_D] at h
    have hCD : σ.D ⊓ Subgroup.centralizer (R : Set G) ≤ centerOf σ.D := by
      intro d hd
      have h1 := hCN ⟨σ.D_le_N hσ hd.1, hd.2⟩
      have hZN : centerOf σ.D ≤ Subgroup.normalizer (σ.ON : Set G) :=
        (inf_le_left.trans (σ.D_le_N hσ)).trans σ.N_le_normalizer_ON
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZN] at h1
      obtain ⟨o, ho, z, hz, hoz⟩ := h1
      replace hoz : o * z = d := hoz
      have hoD : o ∈ σ.D := by
        have e : o = d * z⁻¹ := by rw [← hoz]; group
        rw [e]
        exact σ.D.mul_mem hd.1 (σ.D.inv_mem hz.1)
      have ho1 : o = 1 := eq_one_of_mem_of_mem_of_odd_aux hD2 σ.odd_card_ON hoD ho
      rw [← hoz, ho1, one_mul]
      exact hz
    obtain ⟨S₁, hDS₁, hS₁H, hS₁Rs, hsyl⟩ :=
      σ.exists_sylow_two_normalizing_aux hσ hII hr hdiv hHL hRs hDRs
    have hXZ : (S₁ : Subgroup G) ⊓ Subgroup.centralizer (Rs : Set G) ≤
        centerOf (S₁ : Subgroup G) := by
      refine hII.normal_le_center_of_inf_D S₁ hDS₁ _ inf_le_left ?_ ?_
      · exact (le_inf Subgroup.le_normalizer
          (hS₁Rs.trans (normalizer_le_normalizer_centralizer_aux Rs))).trans
            Subgroup.inf_normalizer_le_normalizer_inf
      · rintro y ⟨⟨-, hyC⟩, hyD⟩
        exact hCD ⟨hyD, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRRs) hyC⟩
    have heq : centerOf (S₁ : Subgroup G) ⊓ Subgroup.centralizer (Rs : Set G) =
        (S₁ : Subgroup G) ⊓ (H ⊓ Subgroup.centralizer (Rs : Set G)) := by
      apply le_antisymm
      · rintro y ⟨hyZ, hyC⟩
        exact ⟨hyZ.1, hS₁H.le hyZ.1, hyC⟩
      · rintro y ⟨hyS, -, hyC⟩
        exact ⟨hXZ ⟨hyS, hyC⟩, hyC⟩
    rw [← heq] at hsyl
    exact ((hII.qgroup_constraint_criterion H hHL.2.2.1 hO hcov S₁ hS₁H r hr hr2 Rs hRs
      hS₁Rs).1).mpr hsyl
  ·
    have hns : ¬ σ.Stationary r := fun hst => hexc ((h_P21 r hr hdiv).mpr ⟨hst, hcon⟩)
    have hne : R ≠ Rs := by
      rintro rfl
      exact hns ⟨R, hR, hRs⟩
    have h33 := σ.lemmaIV33 hσ hII r hr hdiv H hHL R Rs hR hDR hRH hRs hDRs
      (lt_of_le_of_ne hRRs hne)
    have hOS : CFSG.oddCore H ≤ CFSG.solvableRadical H := by
      have hle : oddCoreIn H ≤ solvRadIn H := by
        rw [hII.qgroup_solvRad H hHL.2.2.1 hO hcov]
        exact le_sup_left
      exact (Subgroup.map_le_map_iff_of_injective H.subtype_injective).mp hle
    exact ⟨h33.1.trans hOS, h33.2⟩

theorem exists_constrained_mem_familyL (hσ : σ.IsValid) (h32 : σ.LemmaIV32) {r : ℕ}
    (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON)
    (hexc : σ.Exceptional r) :
    ∃ H ∈ σ.familyL r, PConstrainedWithin r H (CFSG.solvableRadical H) := by
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  obtain ⟨R, hR, hDR⟩ := exists_isSylowOf_normalized_of_odd hr hD2
    ((σ.D_le_N hσ).trans σ.N_le_normalizer_ON) σ.odd_card_ON
  exact ⟨_, h32 r hr hdiv hexc R hR hDR⟩

end Setting

end CFSG.ABGTheoremB
