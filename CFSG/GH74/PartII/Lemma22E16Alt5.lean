module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGHVI218N
public import CFSG.GroupTheory.ConjClassCover
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.PartII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

private abbrev kleinFourA5F : Finset (Equiv.Perm (Fin 5)) :=
  {1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2}

private lemma mul_mem_kleinFourA5F :
    ∀ a : alternatingGroup (Fin 5), (a : Equiv.Perm (Fin 5)) ∈ kleinFourA5F →
      ∀ b : alternatingGroup (Fin 5), (b : Equiv.Perm (Fin 5)) ∈ kleinFourA5F →
        ((a * b : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ∈ kleinFourA5F := by
  decide

private lemma one_mem_kleinFourA5F :
    ((1 : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ∈ kleinFourA5F := by
  decide

private lemma inv_mem_kleinFourA5F :
    ∀ a : alternatingGroup (Fin 5), (a : Equiv.Perm (Fin 5)) ∈ kleinFourA5F →
      ((a⁻¹ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ∈ kleinFourA5F := by
  decide

@[expose] def kleinFourA5 : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {g | (g : Equiv.Perm (Fin 5)) ∈
    ({1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
      Equiv.swap 0 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 5)))}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact mul_mem_kleinFourA5F a ha b hb
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    exact one_mem_kleinFourA5F
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    exact inv_mem_kleinFourA5F a ha

@[expose] def cycle012A5 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

theorem card_kleinFourA5 : Nat.card kleinFourA5 = 4 := by
  let s : Finset (alternatingGroup (Fin 5)) :=
    {1, ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
          rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
        ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by
          rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
        ⟨Equiv.swap 0 3 * Equiv.swap 1 2, by
          rw [Equiv.Perm.mem_alternatingGroup]; decide⟩}
  have hs : ∀ g : alternatingGroup (Fin 5),
      g ∈ s ↔ (g : Equiv.Perm (Fin 5)) ∈ kleinFourA5F := by
    intro g
    simp only [s, kleinFourA5F, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff,
      Subgroup.coe_one]
  change Nat.card {g : alternatingGroup (Fin 5) //
    (g : Equiv.Perm (Fin 5)) ∈ kleinFourA5F} = 4
  rw [Nat.subtype_card s hs]
  decide

theorem cycle012A5_ne_one : cycle012A5 ≠ 1 := by
  decide

theorem cycle012A5_pow_three : cycle012A5 ^ 3 = 1 := by
  decide

private lemma cycle012A5_mem_normalizer_aux :
    ∀ v : alternatingGroup (Fin 5), (v : Equiv.Perm (Fin 5)) ∈ kleinFourA5F ↔
      ((cycle012A5 * v * cycle012A5⁻¹ : alternatingGroup (Fin 5)) :
        Equiv.Perm (Fin 5)) ∈ kleinFourA5F := by
  decide

theorem cycle012A5_mem_normalizer : cycle012A5 ∈ normalizer (kleinFourA5 : Set _) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro v
  change v ∈ kleinFourA5.carrier ↔
    cycle012A5 * v * cycle012A5⁻¹ ∈ kleinFourA5.carrier
  simp only [kleinFourA5, Set.mem_setOf_eq]
  exact cycle012A5_mem_normalizer_aux v

private lemma eq_one_of_mem_kleinFourA5_of_commute_aux :
    ∀ v : alternatingGroup (Fin 5), (v : Equiv.Perm (Fin 5)) ∈ kleinFourA5F →
      cycle012A5 * v = v * cycle012A5 → v = 1 := by
  decide

theorem eq_one_of_mem_kleinFourA5_of_commute {v : alternatingGroup (Fin 5)}
    (hv : v ∈ kleinFourA5) (hc : cycle012A5 * v = v * cycle012A5) : v = 1 := by
  simp only [kleinFourA5] at hv
  exact eq_one_of_mem_kleinFourA5_of_commute_aux v hv hc

variable {B : Type} [Group B] [Finite B] {π : B →* alternatingGroup (Fin 5)}

omit [Finite B] in
theorem card_eq_960_of_e16_alt5 (hπ : Function.Surjective π) (hK16 : Nat.card π.ker = 16) :
    Nat.card B = 960 := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have hq : Nat.card (B ⧸ π.ker) = 60 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv,
      nat_card_alternatingGroup]
    norm_num
  rw [hcard, hq, hK16]

theorem card_centralizer_eq_64_of_e16_alt5 (hπ : Function.Surjective π)
    (hK16 : Nat.card π.ker = 16)
    (htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : B, g * a * g⁻¹ = b)
    {k : B} (hk : k ∈ π.ker) (hk1 : k ≠ 1) :
    Nat.card (centralizer ({k} : Set B)) = 64 := by
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
  rw [hcl, card_eq_960_of_e16_alt5 hπ hK16] at hcls
  omega

theorem centralizer_ker_eq_ker_of_e16_alt5 (hπ : Function.Surjective π)
    (hK : CFSG.Open.IsElemAbelian 2 π.ker) (hK16 : Nat.card π.ker = 16)
    (htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : B, g * a * g⁻¹ = b) :
    centralizer (π.ker : Set B) = π.ker := by
  have hKleC : π.ker ≤ centralizer (π.ker : Set B) := by
    rw [Subgroup.le_centralizer_iff_isMulCommutative]
    exact hK.1
  have hmapnormal : ((centralizer (π.ker : Set B)).map π).Normal :=
    (Subgroup.normal_centralizer (H := π.ker)).map π hπ
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (alternatingGroup (Fin 5)) _
      alternatingGroup.isSimpleGroup_five ((centralizer (π.ker : Set B)).map π)
      hmapnormal with hbot | htop
  · have hle : centralizer (π.ker : Set B) ≤ π.ker := by
      intro c hc
      have hc' : π c ∈ (centralizer (π.ker : Set B)).map π := ⟨c, hc, rfl⟩
      rw [hbot] at hc'
      simpa using hc'
    exact le_antisymm hle hKleC
  · exfalso
    have htopC : centralizer (π.ker : Set B) = ⊤ := by
      rw [eq_top_iff]
      intro b _
      have hb' : π b ∈ (centralizer (π.ker : Set B)).map π := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb'
      have hk : c⁻¹ * b ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcb, inv_mul_cancel]
      have hb_eq : b = c * (c⁻¹ * b) := by group
      rw [hb_eq]
      exact mul_mem hc (hKleC hk)
    have hlt : 1 < (π.ker : Set B).ncard := by
      rw [← Nat.card_coe_set_eq]
      change 1 < Nat.card ↥(π.ker)
      rw [hK16]
      norm_num
    obtain ⟨x, hxK, hx1⟩ := Set.exists_ne_of_one_lt_ncard hlt (1 : B)
    have hKsub : (π.ker : Set B) ⊆ ({1, x} : Set B) := by
      intro b hb
      by_cases hb1 : b = 1
      · simp [hb1]
      · obtain ⟨g, hg⟩ := htr x hxK b hb hx1 hb1
        have hcomm : g * (x : B) = (x : B) * g := by
          have hg' : g ∈ centralizer (π.ker : Set B) := by
            rw [htopC]
            exact Subgroup.mem_top g
          exact (Subgroup.mem_centralizer_iff.mp hg' x hxK).symm
        have hbx : b = (x : B) := by
          rw [← hg]
          calc g * (x : B) * g⁻¹ = (x : B) * g * g⁻¹ := by rw [hcomm]
            _ = (x : B) := by group
        simp [hbx]
    have hle2 : Nat.card ↥(π.ker) ≤ 2 := by
      have h1 : (π.ker : Set B).ncard ≤ 2 := by
        calc (π.ker : Set B).ncard ≤ ({1, x} : Set B).ncard :=
              Set.ncard_le_ncard hKsub
          _ = 2 := Set.ncard_pair (fun h => hx1 h.symm)
      rwa [← Nat.card_coe_set_eq] at h1
    omega

omit [Finite B] in
theorem exists_pow_three_eq_one_of_e16_alt5 (hπ : Function.Surjective π)
    (hK : CFSG.Open.IsElemAbelian 2 π.ker) :
    ∃ h : B, π h = cycle012A5 ∧ h ^ 3 = 1 := by
  obtain ⟨h0, hh0⟩ := hπ cycle012A5
  have h3ker : h0 ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hh0, cycle012A5_pow_three]
  have h6 : h0 ^ 6 = 1 := by
    have h := hK.2 (h0 ^ 3) h3ker
    rw [← pow_mul] at h
    simpa using h
  refine ⟨h0 ^ 4, ?_, ?_⟩
  · rw [map_pow, hh0, show (4 : ℕ) = 3 + 1 by norm_num, pow_succ,
      cycle012A5_pow_three, one_mul]
  · rw [← pow_mul, show (4 * 3 : ℕ) = 6 * 2 by norm_num, pow_mul, h6, one_pow]

theorem nonempty_mulEquiv_sylSL3_4_of_e16_alt5 (hπ : Function.Surjective π)
    (hK : CFSG.Open.IsElemAbelian 2 π.ker) (hK16 : Nat.card π.ker = 16)
    (htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : B, g * a * g⁻¹ = b)
    (P : Sylow 2 B) : Nonempty (↥P ≃* SylSL3_4) := by
  let P₀ : Subgroup B := kleinFourA5.comap π
  have hKleP0 : π.ker ≤ P₀ := by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker] at hx
    simp [hx]
  have hidx : P₀.index = 15 := by
    change (kleinFourA5.comap π).index = 15
    rw [Subgroup.index_comap_of_surjective kleinFourA5 hπ]
    have h := Subgroup.card_mul_index kleinFourA5
    rw [card_kleinFourA5, nat_card_alternatingGroup] at h
    simp only [Nat.card_fin] at h
    norm_num at h
    omega
  have hcard : Nat.card ↥P₀ = 64 := by
    have h := Subgroup.card_mul_index P₀
    rw [hidx, card_eq_960_of_e16_alt5 hπ hK16] at h
    omega
  have hP0 : IsPGroup 2 ↥P₀ := IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)
  have hnotdvd : ¬ 2 ∣ P₀.index := by rw [hidx]; decide
  let Q0 : Sylow 2 B := hP0.toSylow hnotdvd
  obtain ⟨h, hπh, hpow3⟩ := exists_pow_three_eq_one_of_e16_alt5 hπ hK
  have hN : h ∈ normalizer (P₀ : Set B) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      change x ∈ kleinFourA5.comap π at hx
      change h * x * h⁻¹ ∈ kleinFourA5.comap π
      rw [Subgroup.mem_comap] at hx ⊢
      rw [map_mul, map_mul, map_inv, hπh]
      exact (Subgroup.mem_set_normalizer_iff.mp cycle012A5_mem_normalizer (π x)).mp hx
    · intro hx
      change h * x * h⁻¹ ∈ kleinFourA5.comap π at hx
      change x ∈ kleinFourA5.comap π
      rw [Subgroup.mem_comap] at hx ⊢
      rw [map_mul, map_mul, map_inv, hπh] at hx
      exact (Subgroup.mem_set_normalizer_iff.mp cycle012A5_mem_normalizer (π x)).mpr hx
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
    have hcomm : cycle012A5 * π g = π g * cycle012A5 := by
      have hmap := congrArg π hg'
      rw [map_mul, map_mul, map_inv, hπh] at hmap
      have h2 := congrArg (fun z => z * cycle012A5) hmap
      simpa [mul_assoc] using h2
    have hπg : π g = 1 := eq_one_of_mem_kleinFourA5_of_commute g.2 hcomm
    have hgK : (g : B) ∈ π.ker := MonoidHom.mem_ker.mpr hπg
    by_contra hg1
    have hg1' : (g : B) ≠ 1 := fun hh => hg1 (Subtype.ext hh)
    have hmemC : h ∈ centralizer ({(g : B)} : Set B) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hh := congrArg (fun z => z * h) hg'
      simpa [mul_assoc] using hh
    have h3dvd : orderOf h ∣ 64 := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer ({(g : B)} : Set B)) hmemC
      rwa [card_centralizer_eq_64_of_e16_alt5 hπ hK16 htr hgK hg1'] at h
    have hne : h ≠ 1 := by
      intro hh
      apply cycle012A5_ne_one
      rw [← hπh, hh, map_one]
    have hord : orderOf h = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp
        (orderOf_dvd_of_pow_eq_one hpow3) with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hne
      · exact h3
    rw [hord] at h3dvd
    norm_num at h3dvd
  let Y : Subgroup ↥P₀ := π.ker.subgroupOf P₀
  have hY2 : ∀ y ∈ Y, y * y = 1 := by
    intro y hy
    have hyK : (y : B) ∈ π.ker := Subgroup.mem_subgroupOf.mp hy
    have h := hK.2 (y : B) hyK
    have h2 : (y : B) * (y : B) = 1 := by simpa [pow_two] using h
    exact Subtype.ext h2
  have hY16 : Nat.card Y = 16 := by
    have hmap : Y.map P₀.subtype = π.ker := Subgroup.map_subgroupOf_eq_of_le hKleP0
    have h := Subgroup.card_subtype P₀ Y
    rw [hmap, hK16] at h
    exact h.symm
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
      rw [centralizer_ker_eq_ker_of_e16_alt5 hπ hK hK16 htr] at hcB
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
  exact ⟨(Sylow.equiv P Q0).trans
    ((MulEquiv.subgroupCongr (IsPGroup.toSylow_coe hP0 hnotdvd)).trans e)⟩

end CFSG.GH74.PartII
