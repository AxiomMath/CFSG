module

public import CFSG.GH74.GLS.C3.Layer1.Th2P85Bar
public import CFSG.GH74.GLS.LU.Local.Transport
public import CFSG.GH74.GLS.C3.Layer1.Th2HYComp

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.HY
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.Th2.P85
open scoped commutatorElement

namespace CFSG.GH74.GLS.Th2.P88b

variable {Z : Type} [Group Z] [Finite Z]

theorem comp_centralizes_in {Φ L O : Subgroup Z} (hL : IsCompIn Φ L)
    (hgen : L ≤ Subgroup.closure {t : Z | t ∈ L ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1})
    (hO : Odd (Nat.card ↥O)) (hOΦ : O ≤ Φ) {y : Z} (hy : y ∈ Φ) (hc : ∀ σ ∈ L, ⁅σ, y⁆ ∈ O) :
    ∀ σ ∈ L, y * σ * y⁻¹ = σ := by
  classical
  have hgen' : L.subgroupOf Φ ≤ Subgroup.closure
      {t : ↥Φ | t ∈ L.subgroupOf Φ ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1} := by
    intro t ht
    have h1 : (t : Z) ∈ L := ht
    have h2 := hgen h1
    have h3 : (Subgroup.closure {t : Z | t ∈ L ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1}) ≤
        (Subgroup.closure {t : ↥Φ | t ∈ L.subgroupOf Φ ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1}).map Φ.subtype := by
      rw [Subgroup.closure_le]
      rintro s ⟨hsL, k, hk⟩
      refine ⟨⟨s, hL.1 hsL⟩, Subgroup.subset_closure ⟨hsL, k, ?_⟩, rfl⟩
      exact Subtype.ext hk
    obtain ⟨u, hu, hut⟩ := h3 h2
    have : u = t := Subtype.ext hut
    rw [← this]
    exact hu
  have hO' : Odd (Nat.card ↥(O.subgroupOf Φ)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOΦ).toEquiv]
    exact hO
  have h := comp_centralizes_of_commutators_odd (Q := ↥Φ) (L := L.subgroupOf Φ) (O := O.subgroupOf Φ)
    hL.2 hgen' hO' (y := ⟨y, hy⟩) (fun σ hσ => by
      have h1 : ⁅(σ : Z), y⁆ ∈ O := hc _ hσ
      exact h1)
  intro σ hσ
  have := h ⟨σ, hL.1 hσ⟩ hσ
  exact congrArg Subtype.val this

section YComm

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barMk_mem_normalizer_imgM {M V : Subgroup G} {g : G} (hgM : g ∈ M)
    (hg : g ∈ normalizer (V : Set G)) :
    barMk ↥M (⟨g, hgM⟩ : ↥M) ∈ normalizer ((imgM M V : Subgroup (Mb M)) : Set (Mb M)) := by
  have key : ∀ g' : G, ∀ hg'M : g' ∈ M, g' ∈ normalizer (V : Set G) → ∀ w ∈ imgM M V,
      barMk ↥M (⟨g', hg'M⟩ : ↥M) * w * (barMk ↥M (⟨g', hg'M⟩ : ↥M))⁻¹ ∈ imgM M V := by
    intro g' hg'M hg' w hw
    obtain ⟨m, hmV, rfl⟩ := mem_imgM_iff.1 hw
    refine mem_imgM_iff.2 ⟨⟨g', hg'M⟩ * m * ⟨g', hg'M⟩⁻¹, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 hg' (m : G)).1 hmV
      simpa using this
    · rw [map_mul, map_mul, map_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => key g hgM hg w hw, fun hw => ?_⟩
  have hgM' : g⁻¹ ∈ M := M.inv_mem hgM
  have hg' : g⁻¹ ∈ normalizer (V : Set G) := (normalizer (V : Set G)).inv_mem hg
  have h := key g⁻¹ hgM' hg' _ hw
  have e : barMk ↥M (⟨g⁻¹, hgM'⟩ : ↥M) = (barMk ↥M (⟨g, hgM⟩ : ↥M))⁻¹ := by
    rw [← map_inv]; rfl
  rw [e] at h
  simpa [mul_assoc] using h

theorem isCompIn_normalizer_imgM {M K V : Subgroup G} (hKM : K ≤ M)
    (hterm : IsTerminalSub (imgM M K)) (hV2 : IsPGroup 2 ↥V) (hVne : V ≠ ⊥)
    (hVC : V ≤ CMbar M K) :
    IsCompIn (normalizer ((imgM M V : Subgroup (Mb M)) : Set (Mb M))) (imgM M K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v₀, hv₀V, hv₀2⟩ := Th2.exists_involution_mem hV2 hVne
  have hv₀M : v₀ ∈ M := (inf_le_left : CMbar M K ≤ M) (hVC hv₀V)
  have hVK : imgM M V ≤ centralizer ((imgM M K : Subgroup (Mb M)) : Set (Mb M)) := by
    rw [← imgM_cmbar_eq hKM]
    exact imgM_mono hVC
  have hev₀ : barMk ↥M (⟨v₀, hv₀M⟩ : ↥M) ∈ imgM M V :=
    mem_imgM_iff.2 ⟨⟨v₀, hv₀M⟩, hv₀V, rfl⟩
  have hord : orderOf (barMk ↥M (⟨v₀, hv₀M⟩ : ↥M)) = 2 :=
    orderOf_barMk ((Subgroup.orderOf_mk v₀ hv₀M).trans hv₀2)
  have hcen : ∀ k ∈ imgM M K,
      barMk ↥M (⟨v₀, hv₀M⟩ : ↥M) * k = k * barMk ↥M (⟨v₀, hv₀M⟩ : ↥M) := by
    intro k hk
    exact ((Subgroup.mem_centralizer_iff.1 (hVK hev₀)) k hk).symm
  have h0 := hterm _ hord hcen
  have hKC₁ : imgM M K ≤ centralizer ((imgM M V : Subgroup (Mb M)) : Set (Mb M)) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.1 (hVK hv)) k hk).symm
  have hC₁C₀ : centralizer ((imgM M V : Subgroup (Mb M)) : Set (Mb M)) ≤
      centralizer ({barMk ↥M (⟨v₀, hv₀M⟩ : ↥M)} : Set (Mb M)) :=
    Subgroup.centralizer_le (by simpa using hev₀)
  have h1 := LU.Local.isCompIn_mono' h0 hKC₁ hC₁C₀
  refine LU.Local.isCompIn_of_normal h1 (Subgroup.centralizer_le_normalizer _) ?_
  intro c hc a ha
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hc' : c⁻¹ ∈ normalizer ((imgM M V : Subgroup (Mb M)) : Set (Mb M)) :=
    (normalizer ((imgM M V : Subgroup (Mb M)) : Set (Mb M))).inv_mem hc
  have hv' : c⁻¹ * v * c ∈ imgM M V := by
    have := (Subgroup.mem_normalizer_iff.1 hc' v).1 hv
    simpa using this
  have h2 := (Subgroup.mem_centralizer_iff.1 ha) _ hv'
  calc v * (c * a * c⁻¹) = c * ((c⁻¹ * v * c) * a) * c⁻¹ := by group
    _ = c * (a * (c⁻¹ * v * c)) * c⁻¹ := by rw [h2]
    _ = (c * a * c⁻¹) * v := by group

theorem Y_comm_K_term {x y : G} {K T S V : Subgroup G} (hS : HYSetup x y K T S V) {M : Subgroup G}
    (hKM : K ≤ M) (hO : OV V ≤ M) (hterm : IsTerminalSub (imgM M K)) (hVC : V ≤ CMbar M K)
    {y' : G} (hy : y' ∈ YV K V) (hyM : y' ∈ M) :
    ∀ k ∈ K, ⁅k, y'⁆ ∈ pPrimeCoreOf 2 M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥M →* barQ ↥M := barMk ↥M
  have hΦ := isCompIn_normalizer_imgM hKM hterm hS.V_pGroup hS.hVne hVC
  let A : Subgroup (barQ ↥M) := imgM M (lamV K V)
  let W : Subgroup (barQ ↥M) := imgM M (pPrimeCoreOf 2 K)
  let Ō : Subgroup (barQ ↥M) := imgM M (OV V)
  have hLK' : lamV K V ≤ K := (twoGen_le _).trans inf_le_left
  have hAK : A ≤ imgM M K := imgM_mono hLK'
  have hWK : W ≤ imgM M K := imgM_mono (TwoThin.pPrimeCoreOf_le K)
  have hKq : CFSG.IsQuasisimple ↥(imgM M K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hΦ.1) hΦ.2.1
  have hWn : ∀ l ∈ imgM M K, ∀ w ∈ W, l * w * l⁻¹ ∈ W := by
    intro l hl w hw
    obtain ⟨k, hk, rfl⟩ := mem_imgM_iff.1 hl
    obtain ⟨o, ho, rfl⟩ := mem_imgM_iff.1 hw
    refine mem_imgM_iff.2 ⟨k * o * k⁻¹, ?_, by simp⟩
    simpa using TwoThin.pPrimeCoreOf_normalized K hk ho
  have hcardW : ∀ {B : Subgroup G}, B ≤ M → Odd (Nat.card ↥B) → Odd (Nat.card ↥(imgM M B)) := by
    intro B hBM hBodd
    have h1 : Nat.card ↥(imgM M B) ∣ Nat.card ↥(B.subgroupOf M) := Subgroup.card_map_dvd _ π
    have h2 : Nat.card ↥(B.subgroupOf M) = Nat.card ↥B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
    rw [h2] at h1
    exact hBodd.of_dvd_nat h1
  have hWodd : Odd (Nat.card ↥W) :=
    hcardW ((TwoThin.pPrimeCoreOf_le K).trans hKM) (TwoThin.card_pPrimeCoreOf_odd K)
  have hŌodd : Odd (Nat.card ↥Ō) := hcardW hO (TwoThin.card_pPrimeCoreOf_odd _)
  have hKeven : ¬ Odd (Nat.card ↥(imgM M K)) := by
    intro hodd
    have hsolv : Group.IsSolvable ↥(imgM M K) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have : Nontrivial ↥(imgM M K) := CFSG.LocalCores.isQuasisimple_nontrivial hKq
    have : Group.IsPerfect ↥(imgM M K) := hKq.1
    exact Group.IsPerfect.not_isSolvable ↥(imgM M K) inferInstance
  have hcov : ∀ l ∈ imgM M K, ∃ s ∈ A, ∃ w ∈ W, l = s * w := by
    intro l hl
    obtain ⟨k, hk, rfl⟩ := mem_imgM_iff.1 hl
    obtain ⟨lam, hlam, oK, hoK, hkk⟩ := hS.lam_cover k hk
    have hlamM : lam ∈ M := hKM (hLK' hlam)
    have hoKM : oK ∈ M := hKM (TwoThin.pPrimeCoreOf_le K hoK)
    refine ⟨π ⟨lam, hlamM⟩, mem_imgM_iff.2 ⟨⟨lam, hlamM⟩, hlam, rfl⟩,
      π ⟨oK, hoKM⟩, mem_imgM_iff.2 ⟨⟨oK, hoKM⟩, hoK, rfl⟩, ?_⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hkk
  have hAeq : A = imgM M K := eq_of_cover_odd hKq hAK hWK hWn hWodd hKeven hcov
  have hgen : A ≤ Subgroup.closure {t : barQ ↥M | t ∈ A ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1} := by
    have h1 : lamV K V ≤ ((Subgroup.closure {t : barQ ↥M | t ∈ A ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1}).comap
        π).map M.subtype := by
      refine twoGen_le_of_forall (fun g hg k hgk => ?_)
      have hgM : g ∈ M := hKM hg.1
      refine ⟨⟨g, hgM⟩, ?_, rfl⟩
      show π ⟨g, hgM⟩ ∈ Subgroup.closure {t : barQ ↥M | t ∈ A ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1}
      refine Subgroup.subset_closure ⟨mem_imgM_iff.2 ⟨⟨g, hgM⟩, subset_twoGen hg hgk, rfl⟩, k, ?_⟩
      rw [← map_pow]
      have : (⟨g, hgM⟩ : ↥M) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hgk)
      rw [this, map_one]
    intro a ha
    obtain ⟨l, hl, rfl⟩ := mem_imgM_iff.1 ha
    obtain ⟨m, hm, hml⟩ := h1 hl
    have : m = l := Subtype.ext hml
    subst this
    exact hm
  have hc : ∀ σ ∈ A, ⁅σ, π ⟨y', hyM⟩⁆ ∈ Ō := by
    intro σ hσ
    obtain ⟨l, hl, rfl⟩ := mem_imgM_iff.1 hσ
    have hlH : (l : G) ∈ HV K V := Subgroup.mem_sup_left hl
    have h1 : ⁅(l : G), y'⁆ ∈ OV V := hy.2.2.2 _ hlH
    refine mem_imgM_iff.2 ⟨⟨⁅(l : G), y'⁆, hO h1⟩, h1, ?_⟩
    have e : (⟨⁅(l : G), y'⁆, hO h1⟩ : ↥M) = ⁅l, ⟨y', hyM⟩⁆ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [e, map_commutatorElement]
  have hyΦ : π ⟨y', hyM⟩ ∈ normalizer ((imgM M V : Subgroup (Mb M)) : Set (Mb M)) :=
    barMk_mem_normalizer_imgM hyM hy.1
  have hŌΦ : Ō ≤ normalizer ((imgM M V : Subgroup (Mb M)) : Set (Mb M)) := by
    intro o ho
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 ho
    exact barMk_mem_normalizer_imgM m.2 (TwoThin.pPrimeCoreOf_le _ hm)
  have hcen := comp_centralizes_in hΦ (hAeq ▸ hgen) hŌodd hŌΦ hyΦ (fun σ hσ => hc σ (hAeq ▸ hσ))
  intro k hk
  have hkM : k ∈ M := hKM hk
  have h2 := hcen (π ⟨k, hkM⟩) (mem_imgM_iff.2 ⟨⟨k, hkM⟩, hk, rfl⟩)
  have hm : ⁅k, y'⁆ ∈ M := by
    simp only [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hkM hyM) (M.inv_mem hkM)) (M.inv_mem hyM)
  have h3 : π ⟨⁅k, y'⁆, hm⟩ = 1 := by
    have h4 : π ⟨⁅k, y'⁆, hm⟩ = ⁅π ⟨k, hkM⟩, π ⟨y', hyM⟩⁆ := by
      have e : (⟨⁅k, y'⁆, hm⟩ : ↥M) = ⁅(⟨k, hkM⟩ : ↥M), ⟨y', hyM⟩⁆ :=
        Subtype.ext (by simp [commutatorElement_def])
      rw [e, map_commutatorElement]
    rw [h4]
    have : π ⟨k, hkM⟩ * π ⟨y', hyM⟩ = π ⟨y', hyM⟩ * π ⟨k, hkM⟩ := by
      have h5 := congrArg (fun z => z * π ⟨y', hyM⟩) h2
      simp only [mul_assoc, inv_mul_cancel, mul_one] at h5
      exact h5.symm
    exact commutatorElement_eq_one_iff_mul_comm.2 this
  exact (barMk_eq_one_iff_mem_pPrimeCoreOf _).1 h3

theorem Q₁_sylow_YV_term (hG : C3Hyp G) {x y : G} {K T S V : Subgroup G}
    (hS : HYSetup x y K T S V) {M U : Subgroup G} (hKM : K ≤ M) (hO : OV V ≤ M)
    (hterm : IsTerminalSub (imgM M K)) (hVC : V ≤ CMbar M K) (hU : IsFourSub (T ⊓ K) U)
    (hFM : normalizer ((U ⊔ V : Subgroup G) : Set G) ≤ M)
    (hQ1 : IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K))
      (normalizer (V : Set G) ⊓ CMbar M K)) :
    IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)) (YV K V) := by
  have hYM : YV K V ≤ M := hS.YV_le_M hO hU hFM
  have hYC : YV K V ≤ normalizer (V : Set G) ⊓ CMbar M K := fun y' hy =>
    ⟨hy.1, mem_CMbar_of_comm hKM (hYM hy) (Y_comm_K_term hS hKM hO hterm hVC hy (hYM hy))⟩
  exact isSylowOf_of_le_of_le hQ1 (hS.Q₁_le_YV hG) hYC

end YComm

end CFSG.GH74.GLS.Th2.P88b
