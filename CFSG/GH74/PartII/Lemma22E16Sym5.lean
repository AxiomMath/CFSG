module

public import CFSG.GH74.PartII.UT3InvolutionAut
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ConjClassCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGHVI218N
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.PartII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.OddStandard.SmallF3.HarrisU33.Outside

private abbrev kleinFourS5F : Finset (Equiv.Perm (Fin 5)) :=
  {1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2}

set_option maxRecDepth 10000 in
private lemma mul_mem_kleinFourS5F :
    ∀ a ∈ kleinFourS5F, ∀ b ∈ kleinFourS5F, a * b ∈ kleinFourS5F := by
  decide

private lemma one_mem_kleinFourS5F : (1 : Equiv.Perm (Fin 5)) ∈ kleinFourS5F := by
  decide

set_option maxRecDepth 10000 in
private lemma inv_mem_kleinFourS5F :
    ∀ a ∈ kleinFourS5F, a⁻¹ ∈ kleinFourS5F := by
  decide

@[expose] def kleinFourS5 : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {g | g ∈ ({1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 5)))}
  mul_mem' := by
    intro a b ha hb
    exact mul_mem_kleinFourS5F a ha b hb
  one_mem' := by
    exact one_mem_kleinFourS5F
  inv_mem' := by
    intro a ha
    exact inv_mem_kleinFourS5F a ha

@[expose] def cycle012S5 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem card_kleinFourS5 : Nat.card kleinFourS5 = 4 := by
  change Nat.card {g : Equiv.Perm (Fin 5) // g ∈ kleinFourS5F} = 4
  rw [Nat.subtype_card kleinFourS5F (fun g => Iff.rfl)]
  decide

theorem cycle012S5_pow_three : cycle012S5 ^ 3 = 1 := by
  decide

theorem cycle012S5_ne_one : cycle012S5 ≠ 1 := by
  decide

set_option maxRecDepth 10000 in
private lemma conj_mem_kleinFourS5F (g : Equiv.Perm (Fin 5))
    (hg : g = cycle012S5 ∨ g = Equiv.swap 0 1) :
    ∀ v : Equiv.Perm (Fin 5), v ∈ kleinFourS5F ↔ g * v * g⁻¹ ∈ kleinFourS5F := by
  rcases hg with rfl | rfl <;> decide

theorem conj_mem_kleinFourS5 {g : Equiv.Perm (Fin 5)} (hg : g = cycle012S5 ∨ g = Equiv.swap 0 1)
    {v : Equiv.Perm (Fin 5)} : v ∈ kleinFourS5 ↔ g * v * g⁻¹ ∈ kleinFourS5 := by
  change v ∈ kleinFourS5F ↔ g * v * g⁻¹ ∈ kleinFourS5F
  exact conj_mem_kleinFourS5F g hg v

set_option maxRecDepth 10000 in
private lemma eq_one_of_mem_kleinFourS5_of_commute_aux :
    ∀ v : Equiv.Perm (Fin 5), v ∈ kleinFourS5F →
      cycle012S5 * v = v * cycle012S5 → v = 1 := by
  decide

theorem eq_one_of_mem_kleinFourS5_of_commute {v : Equiv.Perm (Fin 5)} (hv : v ∈ kleinFourS5)
    (hc : cycle012S5 * v = v * cycle012S5) : v = 1 := by
  change v ∈ kleinFourS5F at hv
  exact eq_one_of_mem_kleinFourS5_of_commute_aux v hv hc

theorem swap01_not_mem_kleinFourS5 : Equiv.swap (0 : Fin 5) 1 ∉ kleinFourS5 := by
  change Equiv.swap (0 : Fin 5) 1 ∉ kleinFourS5F
  decide

theorem swap01_conj_cycle012S5 :
    Equiv.swap (0 : Fin 5) 1 * cycle012S5 * (Equiv.swap 0 1)⁻¹ = cycle012S5⁻¹ := by
  decide

variable {B : Type} [Group B] [Finite B] {π : B →* Equiv.Perm (Fin 5)}

omit [Finite B] in
theorem card_eq_1920_of_e16_sym5 (hπ : Function.Surjective π) (hK16 : Nat.card π.ker = 16) :
    Nat.card B = 1920 := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have hq : Nat.card (B ⧸ π.ker) = 120 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv,
      Nat.card_perm, Nat.card_fin]
    norm_num
  rw [hcard, hq, hK16]

theorem card_centralizer_eq_128_of_e16_sym5 (hπ : Function.Surjective π)
    (hK16 : Nat.card π.ker = 16)
    (htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : B, g * a * g⁻¹ = b)
    {k : B} (hk : k ∈ π.ker) (hk1 : k ≠ 1) :
    Nat.card (centralizer ({k} : Set B)) = 128 := by
  have hclass : conjugatesOf k = (π.ker : Set B) \ {1} := by
    ext x
    constructor
    · intro hx
      change IsConj k x at hx
      refine ⟨Group.conjugates_subset_normal hk hx, ?_⟩
      intro hx1
      have hx' : IsConj 1 k := by
        rw [hx1] at hx
        exact hx.symm
      exact hk1 (isConj_one_right.mp hx')
    · intro hx
      rw [Set.mem_diff, Set.mem_singleton_iff] at hx
      obtain ⟨hxK, hx1⟩ := hx
      obtain ⟨g, hg⟩ := htr k hk x hxK hk1 hx1
      change IsConj k x
      exact isConj_iff.mpr ⟨g, hg⟩
  have hcl : (conjugatesOf k).ncard = 15 := by
    rw [hclass]
    rw [Set.ncard_diff (s := ({1} : Set B)) (t := (π.ker : Set B))
      (Set.singleton_subset_iff.mpr (π.ker.one_mem))]
    rw [Set.ncard_singleton, ← Nat.card_coe_set_eq]
    change Nat.card ↥(π.ker) - 1 = 15
    rw [hK16]
  have hcls := CFSG.GroupTheory.ncard_conjugatesOf_mul_card_centralizer k
  rw [hcl, card_eq_1920_of_e16_sym5 hπ hK16] at hcls
  omega

set_option maxRecDepth 10000 in
private lemma eq_one_of_commute_cycle012_cycle234 :
    ∀ σ : Equiv.Perm (Fin 5),
      σ * cycle012S5 = cycle012S5 * σ →
      σ * (Equiv.swap 2 3 * Equiv.swap 3 4) =
        (Equiv.swap 2 3 * Equiv.swap 3 4) * σ →
      σ = 1 := by
  decide

theorem centralizer_ker_eq_ker_of_e16_sym5 (hπ : Function.Surjective π)
    (hK : CFSG.Open.IsElemAbelian 2 π.ker) (hK16 : Nat.card π.ker = 16)
    (htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : B, g * a * g⁻¹ = b) :
    centralizer (π.ker : Set B) = π.ker := by
  let C : Subgroup B := centralizer (π.ker : Set B)
  have hKleC : π.ker ≤ C := by
    rw [Subgroup.le_centralizer_iff_isMulCommutative]
    exact hK.1
  have hCnormal : C.Normal := Subgroup.normal_centralizer (H := π.ker)
  let N : Subgroup (Equiv.Perm (Fin 5)) := C.map π
  have hNnormal : N.Normal := hCnormal.map π hπ
  have hAnormal : (N.subgroupOf (alternatingGroup (Fin 5))).Normal :=
    hNnormal.subgroupOf (alternatingGroup (Fin 5))
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (alternatingGroup (Fin 5)) _
      hsimple (N.subgroupOf (alternatingGroup (Fin 5))) hAnormal with hbot | htop
  · have hdisj : Disjoint N (alternatingGroup (Fin 5)) :=
      Subgroup.subgroupOf_eq_bot.mp hbot
    have hNbot : N = ⊥ := by
      rw [eq_bot_iff]
      intro n hn
      rw [Subgroup.mem_bot]
      have hcomm : ∀ a ∈ alternatingGroup (Fin 5), n * a = a * n := fun a ha =>
        Subgroup.commute_of_normal_of_disjoint N (alternatingGroup (Fin 5)) hNnormal
          alternatingGroup.normal hdisj n a hn ha
      refine eq_one_of_commute_cycle012_cycle234 n (hcomm _ ?_) (hcomm _ ?_) <;>
        · rw [Equiv.Perm.mem_alternatingGroup]
          decide
    have hCleK : C ≤ π.ker := by
      intro c hc
      have hπc : π c = 1 := by
        have hmem : π c ∈ N := Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
        rwa [hNbot, Subgroup.mem_bot] at hmem
      exact MonoidHom.mem_ker.mpr hπc
    exact le_antisymm hCleK hKleC
  · exfalso
    have hAleN : alternatingGroup (Fin 5) ≤ N := Subgroup.subgroupOf_eq_top.mp htop
    have hNcomap : N.comap π = C := by
      change (C.map π).comap π = C
      exact Subgroup.comap_map_eq_self hKleC
    have hAleC : (alternatingGroup (Fin 5)).comap π ≤ C := by
      calc (alternatingGroup (Fin 5)).comap π ≤ N.comap π := Subgroup.comap_mono hAleN
        _ = C := hNcomap
    have hAcard : Nat.card ↥((alternatingGroup (Fin 5)).comap π) = 960 := by
      have hidx : ((alternatingGroup (Fin 5)).comap π).index = 2 := by
        rw [Subgroup.index_comap_of_surjective (alternatingGroup (Fin 5)) hπ,
          alternatingGroup.index_eq_two]
      have h := Subgroup.card_mul_index ((alternatingGroup (Fin 5)).comap π)
      rw [hidx, card_eq_1920_of_e16_sym5 hπ hK16] at h
      omega
    have hlt : 1 < (π.ker : Set B).ncard := by
      rw [← Nat.card_coe_set_eq]
      change 1 < Nat.card ↥(π.ker)
      rw [hK16]
      norm_num
    obtain ⟨k, hkK, hk1⟩ := Set.exists_ne_of_one_lt_ncard hlt (1 : B)
    have hCleCk : C ≤ centralizer ({k} : Set B) := by
      intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hc k hkK).symm
    have hCcard : Nat.card ↥C ≤ 128 := by
      calc Nat.card ↥C ≤ Nat.card ↥(centralizer ({k} : Set B)) :=
            Subgroup.card_le_of_le hCleCk
        _ = 128 := card_centralizer_eq_128_of_e16_sym5 hπ hK16 htr hkK hk1
    have hcardle : Nat.card ↥((alternatingGroup (Fin 5)).comap π) ≤ Nat.card ↥C :=
      Subgroup.card_le_of_le hAleC
    omega

omit [Finite B] in
theorem exists_pow_three_eq_one_of_e16_sym5 (hπ : Function.Surjective π)
    (hK : CFSG.Open.IsElemAbelian 2 π.ker) :
    ∃ h : B, π h = cycle012S5 ∧ h ^ 3 = 1 := by
  obtain ⟨h0, hh0⟩ := hπ cycle012S5
  have h3ker : h0 ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hh0, cycle012S5_pow_three]
  have h6 : h0 ^ 6 = 1 := by
    have h := hK.2 (h0 ^ 3) h3ker
    rw [← pow_mul] at h
    simpa using h
  refine ⟨h0 ^ 4, ?_, ?_⟩
  · rw [map_pow, hh0, show (4 : ℕ) = 3 + 1 by norm_num, pow_succ,
      cycle012S5_pow_three, one_mul]
  · rw [← pow_mul, show (4 * 3 : ℕ) = 6 * 2 by norm_num, pow_mul, h6, one_pow]

theorem eq_one_of_conj_eq_of_e16_sym5 (hπ : Function.Surjective π)
    (hK16 : Nat.card π.ker = 16)
    (htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : B, g * a * g⁻¹ = b)
    {h : B} (hh : π h = cycle012S5) (hh3 : h ^ 3 = 1) {x : B} (hx : x ∈ kleinFourS5.comap π)
    (hc : h * x * h⁻¹ = x) : x = 1 := by
  have hxV : π x ∈ kleinFourS5 := Subgroup.mem_comap.mp hx
  have hcomm : cycle012S5 * π x = π x * cycle012S5 := by
    have hmap := congrArg π hc
    rw [map_mul, map_mul, map_inv, hh] at hmap
    have h2 := congrArg (fun z => z * cycle012S5) hmap
    simpa [mul_assoc] using h2
  have hπx : π x = 1 := eq_one_of_mem_kleinFourS5_of_commute hxV hcomm
  have hxK : x ∈ π.ker := MonoidHom.mem_ker.mpr hπx
  by_contra hx1
  have hmemC : h ∈ centralizer ({x} : Set B) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hh' := congrArg (fun z => z * h) hc
    simpa [mul_assoc] using hh'
  have h3dvd : orderOf h ∣ 128 := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer ({x} : Set B)) hmemC
    rwa [card_centralizer_eq_128_of_e16_sym5 hπ hK16 htr hxK hx1] at h
  have hne : h ≠ 1 := by
    intro hone
    apply cycle012S5_ne_one
    rw [← hh, hone, map_one]
  have hord : orderOf h = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp
      (orderOf_dvd_of_pow_eq_one hh3) with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h3
  rw [hord] at h3dvd
  norm_num at h3dvd

theorem exists_involution_inverting_of_e16_sym5 (hπ : Function.Surjective π)
    (hK : CFSG.Open.IsElemAbelian 2 π.ker) (hK16 : Nat.card π.ker = 16)
    (htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : B, g * a * g⁻¹ = b)
    {h : B} (hh : π h = cycle012S5) (hh3 : h ^ 3 = 1) :
    ∃ u : B, π u = Equiv.swap 0 1 ∧ u * u = 1 ∧ u * h * u⁻¹ = h⁻¹ := by
  obtain ⟨g, hg⟩ := hπ (Equiv.swap 0 1)
  have hyK : h * (g * h * g⁻¹) ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    rw [map_mul, map_mul, map_mul, map_inv, hh, hg, swap01_conj_cycle012S5]
    simp
  let cH : MulAut ↥(π.ker) := MulAut.conjNormal (H := π.ker) h
  let F : ↥(π.ker) →* ↥(π.ker) :=
    { toFun := fun k => cH k * k⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        change cH (a * b) * (a * b)⁻¹ = (cH a * a⁻¹) * (cH b * b⁻¹)
        rw [map_mul]
        have hcomm : (cH b * b⁻¹) * a⁻¹ = a⁻¹ * (cH b * b⁻¹) :=
          hK.1.is_comm.comm (cH b * b⁻¹) a⁻¹
        calc (cH a * cH b) * (a * b)⁻¹
            = cH a * ((cH b * b⁻¹) * a⁻¹) := by group
          _ = cH a * (a⁻¹ * (cH b * b⁻¹)) := by rw [hcomm]
          _ = (cH a * a⁻¹) * (cH b * b⁻¹) := by group }
  have hF_apply : ∀ k : ↥(π.ker), (F k : B) = h * (k : B) * h⁻¹ * (k : B)⁻¹ := by
    intro k
    change ((cH k * k⁻¹ : ↥(π.ker)) : B) = h * (k : B) * h⁻¹ * (k : B)⁻¹
    rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
  have hF_one : ∀ k : ↥(π.ker), F k = 1 → k = 1 := by
    intro k hk
    apply Subtype.ext
    have hk' : (F k : B) = 1 := congrArg Subtype.val hk
    rw [hF_apply] at hk'
    have hconj : h * (k : B) * h⁻¹ = (k : B) := by
      calc h * (k : B) * h⁻¹ =
            (h * (k : B) * h⁻¹ * (k : B)⁻¹) * (k : B) := by group
        _ = 1 * (k : B) := by rw [hk']
        _ = (k : B) := one_mul _
    have hkT : (k : B) ∈ kleinFourS5.comap π := by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp k.2]
      exact kleinFourS5.one_mem
    exact eq_one_of_conj_eq_of_e16_sym5 hπ hK16 htr hh hh3 hkT hconj
  have hF_inj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    exact hF_one
  have hF_surj : Function.Surjective F := Finite.injective_iff_surjective.mp hF_inj
  obtain ⟨k, hk⟩ := hF_surj ⟨h * (g * h * g⁻¹), hyK⟩
  have hkval : h * (k : B) * h⁻¹ * (k : B)⁻¹ = h * (g * h * g⁻¹) := by
    have h := congrArg Subtype.val hk
    rwa [hF_apply] at h
  have hkk : (k : B) * h⁻¹ * (k : B)⁻¹ = g * h * g⁻¹ := by
    have h := congrArg (fun z => h⁻¹ * z) hkval
    simpa [mul_assoc] using h
  have hku : ((k : B)⁻¹ * g) * h * ((k : B)⁻¹ * g)⁻¹ = h⁻¹ := by
    calc ((k : B)⁻¹ * g) * h * ((k : B)⁻¹ * g)⁻¹
        = (k : B)⁻¹ * (g * h * g⁻¹) * (k : B) := by group
      _ = (k : B)⁻¹ * ((k : B) * h⁻¹ * (k : B)⁻¹) * (k : B) := by rw [hkk]
      _ = h⁻¹ := by group
  have hku2 : ((k : B)⁻¹ * g) * ((k : B)⁻¹ * g) * h *
      (((k : B)⁻¹ * g) * ((k : B)⁻¹ * g))⁻¹ = h := by
    calc ((k : B)⁻¹ * g) * ((k : B)⁻¹ * g) * h *
          (((k : B)⁻¹ * g) * ((k : B)⁻¹ * g))⁻¹
        = ((k : B)⁻¹ * g) * (((k : B)⁻¹ * g) * h * ((k : B)⁻¹ * g)⁻¹) *
          ((k : B)⁻¹ * g)⁻¹ := by group
      _ = ((k : B)⁻¹ * g) * h⁻¹ * ((k : B)⁻¹ * g)⁻¹ := by rw [hku]
      _ = (((k : B)⁻¹ * g) * h * ((k : B)⁻¹ * g)⁻¹)⁻¹ := by group
      _ = (h⁻¹)⁻¹ := by rw [hku]
      _ = h := inv_inv h
  have hcomm2 : h * (((k : B)⁻¹ * g) * ((k : B)⁻¹ * g)) =
      (((k : B)⁻¹ * g) * ((k : B)⁻¹ * g)) * h := by
    have hthis := congrArg
      (fun z => z * (((k : B)⁻¹ * g) * ((k : B)⁻¹ * g))) hku2
    simpa [mul_assoc] using hthis.symm
  have hc2 : h * (((k : B)⁻¹ * g) * ((k : B)⁻¹ * g)) * h⁻¹ =
      ((k : B)⁻¹ * g) * ((k : B)⁻¹ * g) := by
    rw [hcomm2]
    group
  have hkuπ : π ((k : B)⁻¹ * g) = Equiv.swap 0 1 := by
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp k.2, inv_one, one_mul, hg]
  have hku2V : ((k : B)⁻¹ * g) * ((k : B)⁻¹ * g) ∈ kleinFourS5.comap π := by
    rw [Subgroup.mem_comap, map_mul]
    have hswap : π ((k : B)⁻¹ * g) * π ((k : B)⁻¹ * g) = 1 := by
      rw [hkuπ]
      exact Equiv.swap_mul_self 0 1
    rw [hswap]
    exact kleinFourS5.one_mem
  have hkuu : ((k : B)⁻¹ * g) * ((k : B)⁻¹ * g) = 1 :=
    eq_one_of_conj_eq_of_e16_sym5 hπ hK16 htr hh hh3 hku2V hc2
  exact ⟨(k : B)⁻¹ * g, hkuπ, hkuu, hku⟩

omit [Finite B] in
private lemma ker_le_comap_kleinFourS5 : π.ker ≤ kleinFourS5.comap π := by
  intro x hx
  rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
  exact kleinFourS5.one_mem

omit [Finite B] in
private lemma mem_normalizer_comap_kleinFourS5 {g : B}
    (hg : π g = cycle012S5 ∨ π g = Equiv.swap 0 1) :
    g ∈ normalizer (kleinFourS5.comap π : Set B) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  change π x ∈ kleinFourS5 ↔ π (g * x * g⁻¹) ∈ kleinFourS5
  rw [map_mul, map_mul, map_inv]
  exact conj_mem_kleinFourS5 hg

omit [Finite B] in
private lemma mul_self_of_mem_ker_subgroupOf (hK : CFSG.Open.IsElemAbelian 2 π.ker)
    (T : Subgroup B) : ∀ y ∈ π.ker.subgroupOf T, y * y = 1 := by
  intro y hy
  have h := hK.2 (y : B) (Subgroup.mem_subgroupOf.mp hy)
  exact Subtype.ext (by simpa [pow_two] using h)

omit [Finite B] in
private lemma card_ker_subgroupOf (hK16 : Nat.card π.ker = 16) {T : Subgroup B}
    (hKT : π.ker ≤ T) : Nat.card (π.ker.subgroupOf T) = 16 := by
  have h := Subgroup.card_subtype T (π.ker.subgroupOf T)
  rw [Subgroup.map_subgroupOf_eq_of_le hKT, hK16] at h
  exact h.symm

theorem nonempty_mulEquiv_sylSL3_4_of_e16_sym5 (hπ : Function.Surjective π)
    (hK : CFSG.Open.IsElemAbelian 2 π.ker) (hK16 : Nat.card π.ker = 16)
    (htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : B, g * a * g⁻¹ = b) :
    Nonempty (↥(kleinFourS5.comap π) ≃* SylSL3_4) := by
  let P₀ : Subgroup B := kleinFourS5.comap π
  have hKleP0 : π.ker ≤ P₀ := ker_le_comap_kleinFourS5
  have hidx : P₀.index = 30 := by
    change (kleinFourS5.comap π).index = 30
    rw [Subgroup.index_comap_of_surjective kleinFourS5 hπ]
    have h := Subgroup.card_mul_index kleinFourS5
    rw [card_kleinFourS5, Nat.card_perm, Nat.card_fin] at h
    norm_num at h
    omega
  have hcard : Nat.card ↥P₀ = 64 := by
    have h := Subgroup.card_mul_index P₀
    rw [hidx, card_eq_1920_of_e16_sym5 hπ hK16] at h
    omega
  obtain ⟨h, hπh, hpow3⟩ := exists_pow_three_eq_one_of_e16_sym5 hπ hK
  have hN : h ∈ normalizer (P₀ : Set B) := mem_normalizer_comap_kleinFourS5 (Or.inl hπh)
  let hn : ↥(normalizer (P₀ : Set B)) := ⟨h, hN⟩
  let ρ : MulAut ↥P₀ := Subgroup.normalizerMonoidHom P₀ hn
  have hρ_apply : ∀ x : ↥P₀, (ρ x : B) = h * (x : B) * h⁻¹ :=
    fun x => Subgroup.normalizerMonoidHom_apply_apply_coe P₀ hn x
  have hhn : hn ^ 3 = 1 := by
    apply Subtype.ext
    show h ^ 3 = 1
    exact hpow3
  have hρ3 : ρ ^ 3 = 1 := by
    show (Subgroup.normalizerMonoidHom P₀ hn) ^ 3 = 1
    rw [← map_pow, hhn, map_one]
  have hfpf : ∀ g : ↥P₀, ρ g = g → g = 1 := by
    intro g hg
    have hg' : h * (g : B) * h⁻¹ = (g : B) := by
      rw [← hρ_apply g]
      exact congrArg Subtype.val hg
    exact Subtype.ext (eq_one_of_conj_eq_of_e16_sym5 hπ hK16 htr hπh hpow3 g.2 hg')
  let Y : Subgroup ↥P₀ := π.ker.subgroupOf P₀
  have hY2 : ∀ y ∈ Y, y * y = 1 := mul_self_of_mem_ker_subgroupOf hK P₀
  have hY16 : Nat.card Y = 16 := card_ker_subgroupOf hK16 hKleP0
  have hC : centralizer (Y : Set ↥P₀) = Y := by
    apply le_antisymm
    · intro c hc
      have hcB : (c : B) ∈ centralizer (π.ker : Set B) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hkP : k ∈ P₀ := hKleP0 hk
        have hkY : (⟨k, hkP⟩ : ↥P₀) ∈ Y := Subgroup.mem_subgroupOf.mpr hk
        have h := Subgroup.mem_centralizer_iff.mp hc ⟨k, hkP⟩ hkY
        exact congrArg Subtype.val h
      rw [centralizer_ker_eq_ker_of_e16_sym5 hπ hK hK16 htr] at hcB
      exact Subgroup.mem_subgroupOf.mpr hcB
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hyK : (y : B) ∈ π.ker := Subgroup.mem_subgroupOf.mp hy
      have hzK : (z : B) ∈ π.ker := Subgroup.mem_subgroupOf.mp hz
      have hKleC : π.ker ≤ centralizer (π.ker : Set B) := by
        rw [Subgroup.le_centralizer_iff_isMulCommutative]
        exact hK.1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKleC hyK) (z : B) hzK)
  obtain ⟨⟨e⟩, -, -⟩ := CFSG.OddStandard.SmallF3.HarrisU33.Outside.GHVI218_E16
    (S := ↥P₀) hcard hρ3 hfpf Y hY2 hY16 hC
  exact ⟨e⟩

private lemma mem_of_subset_of_card {E : Subgroup U4} (hE : Nat.card E = 16) {p : U4 → Prop}
    (hp : Nat.card {x // p x} = 16) (hsub : ∀ x ∈ E, p x) {x : U4} (hx : p x) : x ∈ E := by
  have heq : (E : Set U4) = {x | p x} := by
    refine Set.eq_of_subset_of_ncard_le (fun y hy => hsub y hy) ?_
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    change Nat.card {x // p x} ≤ Nat.card ↥E
    rw [hp, hE]
  change x ∈ (E : Set U4)
  rw [heq]
  exact hx

theorem nonempty_mulEquiv_sylAhat8_of_e16_sym5 (hπ : Function.Surjective π)
    (hK : CFSG.Open.IsElemAbelian 2 π.ker) (hK16 : Nat.card π.ker = 16)
    (htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : B, g * a * g⁻¹ = b)
    (P : Sylow 2 B) : Nonempty (↥P ≃* SylAhat8) := by
  let T : Subgroup B := kleinFourS5.comap π
  have hKleT : π.ker ≤ T := ker_le_comap_kleinFourS5
  obtain ⟨e₀'⟩ := nonempty_mulEquiv_sylSL3_4_of_e16_sym5 hπ hK hK16 htr
  let e₀ : ↥T ≃* SylSL3_4 := e₀'
  let e : ↥T ≃* U4 := e₀.trans CFSG.GH74.GLS.Bg.TwoGroups.L23.sylLCongr
  obtain ⟨h, hh, hh3⟩ := exists_pow_three_eq_one_of_e16_sym5 hπ hK
  obtain ⟨u, huπ, huu, huh⟩ :=
    exists_involution_inverting_of_e16_sym5 hπ hK hK16 htr hh hh3
  have hNT : h ∈ normalizer (T : Set B) := mem_normalizer_comap_kleinFourS5 (Or.inl hh)
  have huNT : u ∈ normalizer (T : Set B) := mem_normalizer_comap_kleinFourS5 (Or.inr huπ)
  let hn : ↥(normalizer (T : Set B)) := ⟨h, hNT⟩
  let un : ↥(normalizer (T : Set B)) := ⟨u, huNT⟩
  let ch : MulAut ↥T := Subgroup.normalizerMonoidHom T hn
  let cu : MulAut ↥T := Subgroup.normalizerMonoidHom T un
  have hch_apply : ∀ x : ↥T, (ch x : B) = h * (x : B) * h⁻¹ :=
    fun x => Subgroup.normalizerMonoidHom_apply_apply_coe T hn x
  have hcu_apply : ∀ x : ↥T, (cu x : B) = u * (x : B) * u⁻¹ :=
    fun x => Subgroup.normalizerMonoidHom_apply_apply_coe T un x
  have hhn3 : hn ^ 3 = 1 := by
    apply Subtype.ext
    show h ^ 3 = 1
    exact hh3
  have hch3 : ch ^ 3 = 1 := by
    show (Subgroup.normalizerMonoidHom T hn) ^ 3 = 1
    rw [← map_pow, hhn3, map_one]
  have hun2 : un * un = 1 := by
    apply Subtype.ext
    show u * u = 1
    exact huu
  have hcu2 : cu * cu = 1 := by
    show Subgroup.normalizerMonoidHom T un * Subgroup.normalizerMonoidHom T un = 1
    rw [← map_mul, hun2, map_one]
  let α : MulAut U4 := (MulAut.congr e) cu
  let δ : MulAut U4 := (MulAut.congr e) ch
  have hα : α * α = 1 := by
    change (MulAut.congr e) cu * (MulAut.congr e) cu = 1
    rw [← map_mul, hcu2, map_one]
  have hδ3 : δ ^ 3 = 1 := by
    change ((MulAut.congr e) ch) ^ 3 = 1
    rw [← map_pow, hch3, map_one]
  have hch_fpf : ∀ y : ↥T, ch y = y → y = 1 := by
    intro y hy
    have hy' : h * (y : B) * h⁻¹ = (y : B) := by
      rw [← hch_apply y]
      exact congrArg Subtype.val hy
    exact Subtype.ext (eq_one_of_conj_eq_of_e16_sym5 hπ hK16 htr hh hh3 y.2 hy')
  have hδfpf : ∀ x : U4, δ x = x → x = 1 := by
    intro x hx
    have hx'' : e (ch (e.symm x)) = x := by
      simpa [δ, MulAut.congr_apply, MulEquiv.trans_apply] using hx
    have hx' : ch (e.symm x) = e.symm x := by
      simpa using congrArg e.symm hx''
    have h1 : e.symm x = 1 := hch_fpf (e.symm x) hx'
    calc x = e (e.symm x) := (MulEquiv.apply_symm_apply e x).symm
      _ = e 1 := by rw [h1]
      _ = 1 := map_one e
  have hcu_ch : cu * ch * cu⁻¹ = ch⁻¹ := by
    have hun : un * hn * un⁻¹ = hn⁻¹ := Subtype.ext huh
    show Subgroup.normalizerMonoidHom T un * Subgroup.normalizerMonoidHom T hn *
      (Subgroup.normalizerMonoidHom T un)⁻¹ = (Subgroup.normalizerMonoidHom T hn)⁻¹
    rw [← map_mul, ← map_inv, ← map_mul, hun, map_inv]
  have hαδ : α * δ * α⁻¹ = δ⁻¹ := by
    have hthis := congrArg (MulAut.congr e) hcu_ch
    simpa [α, δ, map_mul, map_inv] using hthis
  have hZ : ∃ z ∈ center U4, α z ≠ z :=
    exists_center_ne_of_inverts α δ hδ3 hδfpf hαδ
  let Y : Subgroup ↥T := π.ker.subgroupOf T
  have hY2 : ∀ y ∈ Y, y * y = 1 := mul_self_of_mem_ker_subgroupOf hK T
  have hY16 : Nat.card Y = 16 := card_ker_subgroupOf hK16 hKleT
  let E : Subgroup U4 := Y.map e.toMonoidHom
  have hE2 : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_mul, hY2 y hy, map_one]
  have hEcard : Nat.card ↥E = 16 := by
    change Nat.card ↥(Y.map e.toMonoidHom) = 16
    rw [Subgroup.card_map_of_injective e.injective, hY16]
  have hα_apply : ∀ z : ↥T, α (e z) = e (cu z) := by
    intro z
    simp [α, MulAut.congr_apply, MulEquiv.trans_apply]
  have hcu_mem_Y : ∀ y ∈ Y, cu y ∈ Y := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    rw [hcu_apply]
    exact (MonoidHom.normal_ker π).conj_mem (y : B) hy u
  have hαE : ∀ x ∈ E, α x ∈ E := by
    intro x hx
    rw [Subgroup.mem_map] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨cu y, hcu_mem_Y y hy, (hα_apply y).symm⟩
  have hbcard : Nat.card {x : U4 // x.b = 0} = 16 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hacard : Nat.card {x : U4 // x.a = 0} = 16 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hA : ∀ x : U4, x.b = 0 → (α x).b = 0 := by
    rcases elemAbelian_U4 E hE2 with hEb | hEa
    · exact fun x hx => hEb _ (hαE x (mem_of_subset_of_card hEcard hbcard hEb hx))
    · exact b_eq_zero_of_a_preserving α fun x hx =>
        hEa _ (hαE x (mem_of_subset_of_card hEcard hacard hEa hx))
  let f₁ : U4 →* B := T.subtype.comp e.symm.toMonoidHom
  let f₂ : Multiplicative (ZMod 2) →* B :=
    { toFun := fun ε => u ^ (Multiplicative.toAdd ε).val
      map_one' := by simp
      map_mul' := fun a b => by
        have h2 : u ^ 2 = 1 := by rw [pow_two, huu]
        rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ h2, pow_add] }
  have hcompat : ∀ ε : Multiplicative (ZMod 2),
      f₁.comp ((invAct α hα) ε).toMonoidHom =
        (MulAut.conj (f₂ ε)).toMonoidHom.comp f₁ := by
    intro ε
    apply MonoidHom.ext
    intro x
    have hval : (Multiplicative.toAdd ε).val = 0 ∨
        (Multiplicative.toAdd ε).val = 1 := by
      have h := ZMod.val_lt (Multiplicative.toAdd ε)
      omega
    rcases hval with h0 | h1
    · have hact : (invAct α hα) ε = 1 := by
        show α ^ (Multiplicative.toAdd ε).val = 1
        rw [h0, pow_zero]
      have hf2 : f₂ ε = 1 := by
        show u ^ (Multiplicative.toAdd ε).val = 1
        rw [h0, pow_zero]
      rw [hact, hf2]
      simp
    · have hact : (invAct α hα) ε = α := by
        show α ^ (Multiplicative.toAdd ε).val = α
        rw [h1, pow_one]
      have hf2 : f₂ ε = u := by
        show u ^ (Multiplicative.toAdd ε).val = u
        rw [h1, pow_one]
      have hαx : α x = e (cu (e.symm x)) := by
        simp [α, MulAut.congr_apply, MulEquiv.trans_apply]
      have hf1 : f₁ (α x) = u * f₁ x * u⁻¹ := by
        have hαx' : e.symm (α x) = cu (e.symm x) := by
          rw [hαx, MulEquiv.symm_apply_apply]
        calc f₁ (α x) = ((e.symm (α x) : ↥T) : B) := rfl
          _ = ((cu (e.symm x) : ↥T) : B) := by rw [hαx']
          _ = u * ((e.symm x : ↥T) : B) * u⁻¹ := hcu_apply (e.symm x)
          _ = u * f₁ x * u⁻¹ := rfl
      rw [hact, hf2]
      change f₁ (α x) = (MulAut.conj u).toMonoidHom (f₁ x)
      rw [hf1]
      simp [MulAut.conj_apply]
  let Φ : U4 ⋊[invAct α hα] Multiplicative (ZMod 2) →* B :=
    SemidirectProduct.lift f₁ f₂ hcompat
  have hΦ_inj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hdec := SemidirectProduct.inl_left_mul_inr_right p
    have hp' : f₁ p.left * f₂ p.right = 1 := by
      have hthis := congrArg Φ hdec
      rw [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr, hp] at hthis
      exact hthis
    have hval : (Multiplicative.toAdd p.right).val = 0 ∨
        (Multiplicative.toAdd p.right).val = 1 := by
      have h := ZMod.val_lt (Multiplicative.toAdd p.right)
      omega
    rcases hval with h0 | h1
    · have hf2 : f₂ p.right = 1 := by
        show u ^ (Multiplicative.toAdd p.right).val = 1
        rw [h0, pow_zero]
      rw [hf2, mul_one] at hp'
      have hT1 : e.symm p.left = 1 := by
        apply Subtype.ext
        exact hp'
      have hleft : p.left = 1 := by
        calc p.left = e (e.symm p.left) := (MulEquiv.apply_symm_apply e p.left).symm
          _ = e 1 := by rw [hT1]
          _ = 1 := map_one e
      have hright : p.right = 1 := by
        apply toAdd_eq_zero.mp
        exact (ZMod.val_eq_zero (Multiplicative.toAdd p.right)).mp h0
      rw [hdec.symm, hleft, hright]
      simp
    · have hf2 : f₂ p.right = u := by
        show u ^ (Multiplicative.toAdd p.right).val = u
        rw [h1, pow_one]
      rw [hf2] at hp'
      have huinv : u = (f₁ p.left)⁻¹ := mul_eq_one_iff_eq_inv'.mp hp'
      have havinv : f₁ p.left = ((e.symm p.left : ↥T) : B) := rfl
      have huT : u ∈ T := by
        rw [huinv, havinv]
        exact T.inv_mem (e.symm p.left).2
      have huV : π u ∈ kleinFourS5 := Subgroup.mem_comap.mp huT
      rw [huπ] at huV
      exact absurd huV swap01_not_mem_kleinFourS5
  let S : Subgroup B := Φ.range
  have hScard : Nat.card ↥S = 128 := by
    have h1 : Nat.card ↥S =
        Nat.card (U4 ⋊[invAct α hα] Multiplicative (ZMod 2)) :=
      (Nat.card_congr (MonoidHom.ofInjective hΦ_inj).toEquiv).symm
    rw [h1, SemidirectProduct.card, CFSG.GH74.GLS.Bg.TwoGroups.L23.card_UT3c,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hS : IsPGroup 2 ↥S := IsPGroup.of_card (n := 7) (by rw [hScard]; norm_num)
  have hidxS : S.index = 15 := by
    have h := Subgroup.card_mul_index S
    rw [hScard, card_eq_1920_of_e16_sym5 hπ hK16] at h
    omega
  have hSidx : ¬ 2 ∣ S.index := by rw [hidxS]; decide
  let Q : Sylow 2 B := hS.toSylow hSidx
  obtain ⟨eS⟩ := nonempty_mulEquiv_sylAhat8_of_aut α hα hA hZ
  exact ⟨(Sylow.equiv P Q).trans
    ((MulEquiv.subgroupCongr (IsPGroup.toSylow_coe hS hSidx)).trans
      ((MonoidHom.ofInjective hΦ_inj).symm.trans eS))⟩

end CFSG.GH74.PartII
