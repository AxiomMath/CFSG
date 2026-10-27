module

public import CFSG.LocalAnalysis.ABGTheoremB.V4Inputs
import CFSG.GroupTheory.QuasiDihedralFusion.QGroup
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
import CFSG.LocalAnalysis.ABGTheoremB.IV2
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public section

namespace CFSG.ABGTheoremB.Setting

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

section General

variable {H : Type*} [Group H] [Finite H]

private theorem qgs_isSylowOf_map {p : ℕ} [Fact p.Prime] {N : Subgroup H} [N.Normal]
    {A B : Subgroup H} (h : IsSylowOf p A B) :
    IsSylowOf p (A.map (QuotientGroup.mk' N)) (B.map (QuotientGroup.mk' N)) := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hAB, hA, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hAB, hA.map _, fun hdvd' => hdvd ?_⟩
  rw [← Subgroup.relIndex_comap, QuotientGroup.comap_map_mk'] at hdvd'
  exact hdvd'.trans (Subgroup.relIndex_dvd_of_le_left _ le_sup_right)

end General

variable {G : Type} [Group G] [Finite G] (σ : Setting G)

omit [Finite G] in
private theorem qgs_map_centralizer {H : Subgroup G} (hTH : σ.T ≤ H) :
    (Subgroup.centralizer ((σ.T.subgroupOf H : Subgroup H) : Set H)).map H.subtype =
      σ.C ⊓ H := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨?_, k.2⟩
    change (k : G) ∈ Subgroup.centralizer (σ.T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hk ⟨t, hTH ht⟩ ht)
  · rintro ⟨hgC, hgH⟩
    have hgC' : g ∈ Subgroup.centralizer (σ.T : Set G) := hgC
    refine ⟨⟨g, hgH⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
    intro t ht
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC' t ht)

theorem qGroupSignalizerInput_of (hσ : σ.IsValid) (hN : σ.NStructure)
    (hNF : ∀ X : Subgroup G, X ≤ σ.N → IsPGroup σ.p X →
      σ.D ≤ Subgroup.normalizer (X : Set G) → ∀ y ∈ X, σ.x₂ * y * σ.x₂⁻¹ * y⁻¹ ∈ σ.ON) :
    V4.QGroupSignalizerInput σ := by
  classical
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro H hHQ hDH _ U hU
  obtain ⟨hUH, hUp, hDU, -⟩ := hU
  set π := QuotientGroup.mk' (CFSG.oddCore H) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hxD : σ.x ∈ σ.D := σ.T_le_D hσ σ.x_mem_T
  have hxH : σ.x ∈ H := hDH hxD
  set xH : H := ⟨σ.x, hxH⟩ with hxHdef
  have hDp : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  obtain ⟨SH, hSH⟩ := (hDp.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨S₁, hS₁⟩ := (SH.isPGroup'.map H.subtype).exists_le_sylow
  have hDS₁ : σ.D ≤ (S₁ : Subgroup G) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hDH]
    exact (Subgroup.map_mono hSH).trans hS₁
  have hxc := (hN.center_involution_of_sylow S₁ hDS₁).1
  have hxZ : xH ∈ centerOf (SH : Subgroup H) := by
    refine ⟨hSH (show (xH : G) ∈ σ.D from hxD), Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxc.2) (s : G) (hS₁ ⟨s, hs, rfl⟩))
  set M := Subgroup.centralizer ({xH} : Set H) with hMdef
  have hfac : CFSG.oddCore H ⊔ M = ⊤ := by
    have h := (hHQ.oddCore_sup_centralizer_center SH).1
    rw [eq_top_iff, ← h]
    exact sup_le_sup_left (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxZ)) _
  have hMtop : ∀ q : H ⧸ CFSG.oddCore H, ∃ m ∈ M, π m = q := by
    intro q
    obtain ⟨h, rfl⟩ := hπ q
    have hh : h ∈ CFSG.oddCore H ⊔ M := by
      rw [hfac]
      exact Subgroup.mem_top h
    obtain ⟨o, ho, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh
    refine ⟨m, hm, ?_⟩
    rw [map_mul, show π o = 1 from (QuotientGroup.eq_one_iff o).mpr ho, one_mul]
  have hMN : ∀ m ∈ M, (m : G) ∈ σ.N := by
    intro m hm
    rw [σ.mem_N_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hm)
  have hUHp : IsPGroup σ.p (U.subgroupOf H) := hUp.comap_subtype
  have hDHp : IsPGroup 2 (σ.D.subgroupOf H) := hDp.comap_subtype
  have hDHU : σ.D.subgroupOf H ≤ Subgroup.normalizer ((U.subgroupOf H : Subgroup H) : Set H) :=
    (Subgroup.comap_mono hDU).trans (Subgroup.le_normalizer_comap _)
  have hDHM : σ.D.subgroupOf H ≤ M := by
    intro d hd
    rw [hMdef, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hσ.x_mem_center.2) (d : G) hd.1)
  have hYodd : Odd (Nat.card ((CFSG.oddCore H ⊔ U.subgroupOf H) ⊓ M : Subgroup H)) := by
    have h1 := odd_card_sup_oddCore hσ.p_ne_two hUHp
    rw [sup_comm] at h1
    exact Odd.of_dvd_nat h1 (Subgroup.card_dvd_of_le inf_le_left)
  have hDY : σ.D.subgroupOf H ≤
      Subgroup.normalizer (((CFSG.oddCore H ⊔ U.subgroupOf H) ⊓ M : Subgroup H) : Set H) := by
    intro d hd
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, Subgroup.le_normalizer (hDHM hd)⟩
    refine Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨?_, hDHU hd⟩
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top d
  obtain ⟨U₁, hU₁, -, hDU₁⟩ := exists_invariant_isSylowOf_ge_of_coprime Nat.prime_two
    hσ.p_prime hDHp hDY hYodd.not_two_dvd_nat bot_le IsPGroup.of_bot
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hYmap : ((CFSG.oddCore H ⊔ U.subgroupOf H) ⊓ M).map π = (U.subgroupOf H).map π := by
    apply le_antisymm
    · calc ((CFSG.oddCore H ⊔ U.subgroupOf H) ⊓ M).map π
          ≤ (CFSG.oddCore H ⊔ U.subgroupOf H).map π := Subgroup.map_mono inf_le_left
        _ = (U.subgroupOf H).map π := by
          rw [Subgroup.map_sup, hπdef, QuotientGroup.map_mk'_self, bot_sup_eq]
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨m, hm, hmu⟩ := hMtop (π u)
      have hum : u⁻¹ * m ∈ CFSG.oddCore H := by
        rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hmu
        exact QuotientGroup.eq.mp hmu.symm
      have hmY : m ∈ CFSG.oddCore H ⊔ U.subgroupOf H := by
        rw [show m = u * (u⁻¹ * m) by group]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left hum)
      exact ⟨m, ⟨hmY, hm⟩, hmu⟩
  have hsyl : IsSylowOf σ.p (U₁.map π) ((U.subgroupOf H).map π) := by
    rw [← hYmap, hπdef]
    exact qgs_isSylowOf_map hU₁
  have hUeq : (U.subgroupOf H).map π = U₁.map π := hsyl.eq_of_le hsyl.le le_rfl (hUHp.map π)
  have hUU₁ : U.subgroupOf H ≤ CFSG.oddCore H ⊔ U₁ := by
    rw [← QuotientGroup.comap_map_mk' (CFSG.oddCore H) U₁, ← hπdef, ← hUeq]
    exact Subgroup.le_comap_map π _
  have hU₁M : U₁ ≤ M := hU₁.le.trans inf_le_right
  have hNF₁ := hNF (U₁.map H.subtype)
    (by rintro _ ⟨u, hu, rfl⟩; exact hMN u (hU₁M hu)) (hU₁.isPGroup.map _)
    (by
      intro d hd
      exact Subgroup.le_normalizer_map H.subtype
        ⟨⟨d, hDH hd⟩, hDU₁ (show ((⟨d, hDH hd⟩ : H) : G) ∈ σ.D from hd), rfl⟩)
  have hONH : σ.ON.subgroupOf H ≤ CFSG.oddCore H := by
    have hnormal : ((σ.ON.subgroupOf H).map π).Normal := by
      refine ⟨fun k hk g => ?_⟩
      obtain ⟨m, hm, rfl⟩ := hMtop g
      obtain ⟨k', hk', rfl⟩ := hk
      refine ⟨m * k' * m⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      change (m : G) * k' * (m : G)⁻¹ ∈ σ.ON
      exact (Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_ON (hMN m hm)) k').mp hk'
    have hodd : Odd (Nat.card ((σ.ON.subgroupOf H).map π)) := by
      refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _)
      refine Odd.of_dvd_nat σ.odd_card_ON ?_
      rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hle := le_oddCore_of_normal hnormal hodd
    rw [CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot, le_bot_iff,
      Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk'] at hle
    exact hle
  have hcomm : ∀ u ∈ U₁, ∀ t ∈ σ.T.subgroupOf H, t * u * t⁻¹ * u⁻¹ ∈ CFSG.oddCore H := by
    intro u hu t ht
    apply hONH
    change (t : G) * u * (t : G)⁻¹ * (u : G)⁻¹ ∈ σ.ON
    have hux : σ.x * (u : G) = u * σ.x :=
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hU₁M hu))).symm
    have hx₂ : σ.x₂ * (u : G) * σ.x₂⁻¹ * (u : G)⁻¹ ∈ σ.ON := hNF₁ u ⟨u, hu, rfl⟩
    rcases σ.mem_T_cases hσ (show (t : G) ∈ σ.T from ht) with h | h | h | h <;> rw [h]
    · rw [one_mul, inv_one, mul_one, mul_inv_cancel]
      exact σ.ON.one_mem
    · rw [hux, mul_inv_cancel_right, mul_inv_cancel]
      exact σ.ON.one_mem
    · exact hx₂
    · have hxN : σ.x ∈ σ.N := σ.x_mem_N
      have h1 := (Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_ON hxN) _).mp hx₂
      rwa [show σ.x * (σ.x₂ * (u : G) * σ.x₂⁻¹ * (u : G)⁻¹) * σ.x⁻¹ =
          σ.x * σ.x₂ * u * (σ.x * σ.x₂)⁻¹ * (u : G)⁻¹ by
        calc σ.x * (σ.x₂ * (u : G) * σ.x₂⁻¹ * (u : G)⁻¹) * σ.x⁻¹
            = σ.x * σ.x₂ * u * σ.x₂⁻¹ * ((u : G)⁻¹ * σ.x⁻¹) := by group
          _ = σ.x * σ.x₂ * u * σ.x₂⁻¹ * (σ.x⁻¹ * (u : G)⁻¹) := by
            rw [show (u : G)⁻¹ * σ.x⁻¹ = (σ.x * u)⁻¹ by group, hux,
              show ((u : G) * σ.x)⁻¹ = σ.x⁻¹ * (u : G)⁻¹ by group]
          _ = σ.x * σ.x₂ * u * (σ.x * σ.x₂)⁻¹ * (u : G)⁻¹ := by group] at h1
  have hT2 : IsPGroup 2 (σ.T.subgroupOf H) :=
    (σ.S.isPGroup'.to_le (σ.T_le_S hσ)).comap_subtype
  have hCmap := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 2 (CFSG.oddCore H)
    (odd_card_oddCore H).not_two_dvd_nat (σ.T.subgroupOf H) hT2
  have hU₁C : U₁.map π ≤
      (Subgroup.centralizer ((σ.T.subgroupOf H : Subgroup H) : Set H)).map π := by
    rw [hπdef, hCmap]
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h := (inferInstance : (CFSG.oddCore H).Normal).conj_mem _
      (hcomm u hu t⁻¹ (Subgroup.inv_mem _ ht)) u⁻¹
    rwa [show u⁻¹ * (t⁻¹ * u * t⁻¹⁻¹ * u⁻¹) * u⁻¹⁻¹ = (t * u)⁻¹ * (u * t) by group] at h
  have hU₁le : U₁ ≤ CFSG.oddCore H ⊔
      Subgroup.centralizer ((σ.T.subgroupOf H : Subgroup H) : Set H) := by
    rw [← QuotientGroup.comap_map_mk', ← hπdef]
    exact (Subgroup.le_comap_map π U₁).trans (Subgroup.comap_mono hU₁C)
  have hle : U.subgroupOf H ≤ CFSG.oddCore H ⊔
      Subgroup.centralizer ((σ.T.subgroupOf H : Subgroup H) : Set H) :=
    hUU₁.trans (sup_le le_sup_left hU₁le)
  have hmap := Subgroup.map_mono (f := H.subtype) hle
  rw [Subgroup.map_subgroupOf_eq_of_le hUH, Subgroup.map_sup,
    σ.qgs_map_centralizer ((σ.T_le_D hσ).trans hDH), inf_comm] at hmap
  exact hmap

end CFSG.ABGTheoremB.Setting
