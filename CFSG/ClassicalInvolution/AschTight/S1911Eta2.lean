module

public import CFSG.ClassicalInvolution.AschTight.S1911Eta
public import CFSG.ClassicalInvolution.AschTight.S1911Basic
public import CFSG.ClassicalInvolution.AschTight.S1911Quat
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem le_member (hd : Sec19DataT p f K z S W L t V) : V ≤ L := by
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  obtain ⟨J, hJ, hVJ⟩ := hΩ.exists_member_of_mem_USet hd.tight.branch.odd hd.memV
  obtain ⟨u, hu⟩ := exists_isUniqueInvolution_member htb hJ
  have htu : t = u := eq_of_mem_member hu hVJ hd.memT hd.invL.sq hd.invL.ne_one
  rw [eq_of_isUniqueInvolution_member htb hd.memL hJ hd.invL (htu ▸ hu)]
  exact hVJ

omit [IsSimpleGroup G] in
theorem mem_W (hd : Sec19DataT p f K z S W L t V) : t ∈ W := hd.leW hd.memT

omit [IsSimpleGroup G] in
theorem not_mem_centralizer_inf (hd : Sec19Data p f K z S W) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K) (hJK : J ≠ K) {u : G} (hu : IsUniqueInvolution J u) :
    u ∉ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  intro hC
  refine not_le_centralizer_of_mem_rSet hd.tight (CoreAssembly.mem_conjClass_self K) hJ
    (Ne.symm hJK) hu (inf_mem_rSet hd) inf_le_right ?_
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hC r hr

theorem card_inf_eq (hd : Sec19Data p f K z S W) :
    Nat.card ↥((S : Subgroup G) ⊓ K) = 2 * Nat.card ↥(K ⊓ W) := by
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hp := hd.tight.branch.odd
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := exists_eta hd
  have hU : K ⊓ W ∈ USet (CoreAssembly.conjClass K) := (hη.1 (inf_mem_eta hd hη hinv hWη hηS)).1
  obtain ⟨R', -, J, hJ, hR'J, hUR', -, hcard, -⟩ := hΩ.exists_data_of_mem_USet hp hU
  have hJK : J = K := hΩ.eq_of_mem_USet hp hU hJ (CoreAssembly.mem_conjClass_self K)
    (hUR'.trans hR'J.1) inf_le_left
  subst hJK
  rw [(isSylow2In_inf hd).natCard_eq hR'J, hcard]

theorem mul_mem_centralizer_inf (hd : Sec19Data p f K z S W) {J₁ J₂ : Subgroup G}
    (h₁ : J₁ ∈ CoreAssembly.conjClass K) (h₂ : J₂ ∈ CoreAssembly.conjClass K) (h₁K : J₁ ≠ K)
    (h₂K : J₂ ≠ K) {u₁ u₂ : G} (hu₁ : IsUniqueInvolution J₁ u₁) (hu₂ : IsUniqueInvolution J₂ u₂)
    (hu₁W : u₁ ∈ W) (hu₂W : u₂ ∈ W) :
    u₁ * u₂ ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hcomm := comm_of_mem hd
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  have hUz : ∀ x ∈ K ⊓ W, x * x = 1 → x = 1 ∨ x = z := fun x hx hx2 => hI.unique x hx.1 hx2
  have hN : ∀ x ∈ W, x ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    fun x hx => le_normalizer_inf hd (hd.hWS hx)
  have hC : ∀ x ∈ W, ∀ y ∈ K ⊓ W, x * y = y * x := fun x hx y hy => hcomm x hx y hy.2
  have hsq : ∀ u : G, u * u = 1 →
      u * u ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    intro u hu
    rw [hu]
    exact Subgroup.one_mem _
  exact mul_mem_centralizer_of_not_mem hUR (card_inf_eq hd) hUz (hN u₁ hu₁W) (hN u₂ hu₂W)
    (hC u₁ hu₁W) (hC u₂ hu₂W) (hsq u₁ hu₁.sq) (hsq u₂ hu₂.sq)
    (not_mem_centralizer_inf hd h₁ h₁K hu₁) (not_mem_centralizer_inf hd h₂ h₂K hu₂)

omit [Finite G] [IsSimpleGroup G] in
theorem conj_mul_inv_eq_or {J : Subgroup G} {w : G} (hw : IsUniqueInvolution J w) {x u : G}
    (hxJ : x ∈ J) (huJ : u ∈ Subgroup.normalizer (J : Set G)) (hu2 : u * u = 1)
    (hcomm : x * u * x⁻¹ * u = u * (x * u * x⁻¹)) :
    x * u * x⁻¹ * u⁻¹ = 1 ∨ x * u * x⁻¹ * u⁻¹ = w := by
  have hmem : x * u * x⁻¹ * u⁻¹ ∈ J := by
    have h1 : u * x⁻¹ * u⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp huJ _).mp (J.inv_mem hxJ)
    have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
    rw [e]
    exact J.mul_mem hxJ h1
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hsq : x * u * x⁻¹ * u⁻¹ * (x * u * x⁻¹ * u⁻¹) = 1 := by
    rw [hui]
    calc x * u * x⁻¹ * u * (x * u * x⁻¹ * u) = x * u * x⁻¹ * (u * (x * u * x⁻¹)) * u := by group
      _ = x * u * x⁻¹ * (x * u * x⁻¹ * u) * u := by rw [hcomm]
      _ = x * (u * u) * x⁻¹ * (u * u) := by group
      _ = 1 := by rw [hu2]; group
  exact hw.unique _ hmem hsq

omit [IsSimpleGroup G] in
theorem member_ne (hd : Sec19DataT p f K z S W L t V) : L ≠ K := by
  intro h
  apply hd.ne
  exact (h ▸ hd.invL).eq (isUniqueInvolution_of_tight hd.tight.toTightBranch)

theorem le_centralizer_of_mem (hd : Sec19Data p f K z S W) {u : G} (hu : u ∈ W) :
    W ≤ Subgroup.centralizer ({u} : Set G) := fun w hw =>
  Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem hd w hw u hu)

theorem invol_eq_or (hd : Sec19DataT p f K z S W L t V) {η : Set (Subgroup G)} {S' : Sylow 2 G}
    (hη : η ∈ etaSet (CoreAssembly.conjClass K) S')
    (hinv : ∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) (hWη : W = ⨆ U ∈ η, U)
    {A : Subgroup G} (hA : A ∈ η) {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K)
    (hAJ : A ≤ J) {u : G} (hu : IsUniqueInvolution J u) : u = z ∨ u = t ∨ u = t * z := by
  have hd0 := hd.toSec19Data
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hp := hd.tight.branch.odd
  have hI := isUniqueInvolution_of_tight htb
  have hcomm := comm_of_mem hd0
  have hAU : A ∈ USet (CoreAssembly.conjClass K) := (hη.1 hA).1
  have hAW : A ≤ W := hWη ▸ le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ η) => B) A hA
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hAU
  have huW : u ∈ W := hAW (mem_of_le_member hu hAJ (hΩ.isPGroup_of_mem_USet hp hAU) (by omega))
  by_contra hcon
  push Not at hcon
  obtain ⟨huz, hut, hutz⟩ := hcon
  have hJK : J ≠ K := fun h => huz ((h ▸ hu).eq hI)
  have hJL : J ≠ L := fun h => hut ((h ▸ hu).eq hd.invL)
  have htW := mem_W hd
  have hWL : W ≤ Subgroup.normalizer (L : Set G) :=
    (le_centralizer_of_mem hd0 htW).trans (centralizer_le_normalizer_member htb hd.memL hd.invL)
  have hW2 : IsPGroup 2 W := S.isPGroup'.to_le hd.hWS
  obtain ⟨R₁, hR₁, hR₁W⟩ := exists_sylow_normalized hW2 hWL
  have hR₁mem : R₁ ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hd.memL hR₁
  have hWR₁ : W ≤ Subgroup.normalizer (R₁ : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hR₁W w hw)
  obtain ⟨S₁, hS₁⟩ := (IsPGroup.to_sup_of_normal_right' hW2 hR₁.2.1 hWR₁).exists_le_sylow
  have hηS₁ : ∀ B ∈ η, B ≤ (S₁ : Subgroup G) := fun B hB =>
    ((hWη ▸ le_iSup₂ (f := fun (C : Subgroup G) (_ : C ∈ η) => C) B hB : B ≤ W).trans
      le_sup_left).trans hS₁
  have hxW : ∀ x ∈ R₁, conjSub x W = W := fun x hx => by
    rw [hWη]
    exact conjSub_iSup_eq (conjSub_mem_eta hd0 hη hinv hηS₁ hR₁mem (le_sup_right.trans hS₁) hx)
  have hdich : ∀ x ∈ R₁, x * u * x⁻¹ * u⁻¹ = 1 ∨ x * u * x⁻¹ * u⁻¹ = t := by
    intro x hx
    have hxu : x * u * x⁻¹ ∈ W := (hxW x hx) ▸ conj_mem_conjSub huW
    exact conj_mul_inv_eq_or hd.invL (hR₁.1 hx) (hWL huW) hu.sq (hcomm _ hxu u huW)
  by_cases hall : ∀ x ∈ R₁, x * u * x⁻¹ * u⁻¹ = 1
  · refine not_le_centralizer_of_mem_rSet hd.tight hd.memL hJ (Ne.symm hJL) hu hR₁mem hR₁.1 ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hall x hx
    calc x * u = x * u * x⁻¹ * u⁻¹ * (u * x) := by group
      _ = u * x := by rw [h1, one_mul]
  push Not at hall
  obtain ⟨x, hx, hx1⟩ := hall
  have hxt : x * u * x⁻¹ = t * u := by
    have h1 := (hdich x hx).resolve_left hx1
    calc x * u * x⁻¹ = x * u * x⁻¹ * u⁻¹ * u := by group
      _ = t * u := by rw [h1]
  have hJ' : conjSub x J ∈ CoreAssembly.conjClass K := hΩ.conjInvariant x J hJ
  have hu' : IsUniqueInvolution (conjSub x J) (t * u) := hxt ▸ hu.conj x
  have hJ'K : conjSub x J ≠ K := by
    intro h
    apply hutz
    have h1 : t * u = z := (h ▸ hu').eq hI
    have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right hd.invL.sq
    calc u = t⁻¹ * (t * u) := by group
      _ = t * z := by rw [h1, htt]
  exact not_mem_centralizer_inf hd0 hJ' hJ'K hu'
    (mul_mem_centralizer_inf hd0 hd.memL hJ (member_ne hd) hJK hd.invL hu htW huW)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
