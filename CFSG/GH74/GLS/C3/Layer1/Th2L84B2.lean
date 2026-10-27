module

public import CFSG.GH74.GLS.C3.Layer1.Th2IV26
public import CFSG.GH74.GLS.C3.Layer1.Th2L84Syl

public section

namespace CFSG.GH74.GLS.Th2.IV26

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.Th2.P85
open scoped commutatorElement

section Central

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem imgM_pPrimeCoreOf_central {K : Subgroup G} (hKM : K ≤ M) (hKq : IsQuasisimple ↥(imgM M K)) :
    ∀ n ∈ imgM M (pPrimeCoreOf 2 K), ∀ k ∈ imgM M K, n * k = k * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kb : Subgroup (Mb M) := imgM M K with hKb
  set Nb : Subgroup (Mb M) := imgM M (pPrimeCoreOf 2 K) with hNb
  have hNK : Nb ≤ Kb := imgM_mono (TwoThin.pPrimeCoreOf_le K)
  have hnorm : (Nb.subgroupOf Kb).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨o, ho, hon⟩ := mem_imgM_iff.1 hn
    obtain ⟨k₀, hk₀, hk₀k⟩ := mem_imgM_iff.1 k.2
    have hk₀' : (k₀ : G) * o * (k₀ : G)⁻¹ ∈ pPrimeCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.1
        (TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hk₀)) o).1 ho
    refine mem_imgM_iff.2 ⟨k₀ * ⟨o, hKM (TwoThin.pPrimeCoreOf_le K ho)⟩ * k₀⁻¹, ?_, ?_⟩
    · simpa using hk₀'
    · simp only [map_mul, map_inv, hon, hk₀k]
      rfl
  have hodd : Odd (Nat.card (Nb.subgroupOf Kb)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv]
    have h1 : Nat.card Nb ∣ Nat.card ((pPrimeCoreOf 2 K).subgroupOf M) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card ((pPrimeCoreOf 2 K).subgroupOf M) = Nat.card (pPrimeCoreOf 2 K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((TwoThin.pPrimeCoreOf_le K).trans hKM)).toEquiv
    rw [h2] at h1
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) h1
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hnorm with htop | hcen
  · exfalso
    have hcard : Nat.card (Nb.subgroupOf Kb) = Nat.card ↥Kb := by
      rw [htop, Subgroup.card_top]
    rw [hcard] at hodd
    have hsolv : Group.IsSolvable ↥Kb := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have : Nontrivial ↥Kb := CFSG.LocalCores.isQuasisimple_nontrivial hKq
    have : Group.IsPerfect ↥Kb := hKq.1
    exact Group.IsPerfect.not_isSolvable ↥Kb hsolv
  · intro n hn k hk
    have := Subgroup.mem_center_iff.1
      (hcen (Subgroup.mem_subgroupOf.mpr hn : (⟨n, hNK hn⟩ : ↥Kb) ∈ Nb.subgroupOf Kb)) ⟨k, hk⟩
    exact (congrArg Subtype.val this).symm

end Central

end CFSG.GH74.GLS.Th2.IV26

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85
  CFSG.GH74.GLS.Th2.IV26 CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

theorem le_cmbar_of_imgM_quasisimple {G : Type} [Group G] [Finite G]
    {x : G} {K T M : Subgroup G} (hTM : T ≤ M) (hKM : K ≤ M)
    (hKq : IsQuasisimple ↥(imgM M K)) : T ⊓ CxK x K ≤ CMbar M K := by
  refine Th2.L84Syl.le_cmbar_of_comm (inf_le_left.trans hTM) hKM ?_
  intro q hq k hk
  have hqM : q ∈ M := hTM hq.1
  have hcent := imgM_pPrimeCoreOf_central hKM hKq
  have hle : ⁅imgM M K, imgM M (T ⊓ CxK x K)⁆ ≤ imgM M (pPrimeCoreOf 2 K) := by
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨a₀, ha₀, rfl⟩ := mem_imgM_iff.1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := mem_imgM_iff.1 hb
    have hb₀' : (b₀ : G) ∈ T ⊓ CxK x K := hb₀
    refine mem_imgM_iff.2 ⟨⁅a₀, b₀⁆, ?_, map_commutatorElement _ _ _⟩
    have : ((⁅a₀, b₀⁆ : ↥M) : G) = ⁅(a₀ : G), (b₀ : G)⁆ := by simp [commutatorElement_def]
    rw [this]
    exact hb₀'.2.2.2.2 (a₀ : G) ha₀
  have hdc : ⁅⁅imgM M K, imgM M (T ⊓ CxK x K)⁆, imgM M K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hcent c (hle hc) d hd).symm
  have hperf : Group.IsPerfect ↥(imgM M K) := hKq.1
  have h0 : ⁅imgM M K, imgM M (T ⊓ CxK x K)⁆ = ⊥ :=
    CFSG.LocalCores.perfect_double_commutator hperf hdc
  have hmem : ⁅barMk ↥M ⟨k, hKM hk⟩, barMk ↥M ⟨q, hqM⟩⁆ ∈
      ⁅imgM M K, imgM M (T ⊓ CxK x K)⁆ :=
    Subgroup.commutator_mem_commutator (mem_imgM_iff.2 ⟨⟨k, hKM hk⟩, hk, rfl⟩)
      (mem_imgM_iff.2 ⟨⟨q, hqM⟩, hq, rfl⟩)
  rw [h0, Subgroup.mem_bot, ← map_commutatorElement] at hmem
  have := (barMk_eq_one_iff_mem_pPrimeCoreOf (M := M) ⁅(⟨k, hKM hk⟩ : ↥M), ⟨q, hqM⟩⁆).1 hmem
  simpa [commutatorElement_def] using this

theorem b_thm2_l84_le_of_B2 (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) (hB2 : B_B2) :
    B_thm2_l84_le := by
  intro G _ _ hG x y K T S M ρ B h hKM _ q hq k hk
  have hstd := h.std
  have hMtop : M ≠ ⊤ := h.maximal.1
  have hTM : T ≤ M := t_le_M_of_M2 hL34 h82 hG h
  have hxM : x ∈ M := hTM hstd.x_mem_T
  have hMb : IsKGroupNative (Mb M) := isKGroupNative_Mb hG.kproper hMtop
  have hcore : pPrimeCore 2 (Mb M) = ⊥ := pPrimeCore_Mb_eq_bot M
  have hx2 : orderOf x = 2 := hstd.orderOf_x
  have hBx := isComponent_of_B2 hB2 (gen4_Mb hG.gen4 M) hMb hcore
    (show orderOf (eb M hxM) = 2 from orderOf_barMk ((Subgroup.orderOf_mk x hxM).trans hx2))
  have hxcomp := isCompIn_imgM_at_x hxM hx2 hKM hstd.comp hBx
  have hKq : IsQuasisimple ↥(imgM M K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hxcomp.1) hxcomp.2.1
  exact (le_cmbar_of_imgM_quasisimple hTM hKM hKq hq).2.2.2 k (Subgroup.mem_sup_left hk)

end CFSG.GH74.GLS
