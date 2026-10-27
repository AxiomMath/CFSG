module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7Defs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem twoA7_eq_of_natCard_two {A : Type*} [Group A] (h : Nat.card A = 2) {a b : A}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : A)).1 h
  exact (hy a ha).trans (hy b hb).symm

theorem twoA7_pow_eq_self_of_sq_eq_one {M : Type*} [Monoid M] {g : M} (hg : g ^ 2 = 1) {n : ℕ}
    (hn : Odd n) : g ^ n = g := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, hg, one_pow, one_mul]

theorem twoA7_pow_natCard_ker_eq_one {G : Type*} [Group G] {I' : Subgroup G} {K₀ : Type*}
    [Group K₀] (φ : ↥I' →* K₀) {x : ↥I'} (hx : x ∈ φ.ker) : (x : G) ^ Nat.card φ.ker = 1 := by
  have h := congrArg (fun y : φ.ker => ((y : ↥I') : G))
    (pow_card_eq_one' (x := (⟨x, hx⟩ : φ.ker)))
  simpa using h

theorem twoA7_phi_eq_one_of_central {G : Type*} [Group G] {K₀ : Type*} [Group K₀]
    (I' : Subgroup G) (s' : G) (hs2 : orderOf s' = 2) (hs'I : s' ∈ I')
    (hcomm : ∀ x ∈ I', x * s' = s' * x) (hns : s' ∉ Subgroup.center G)
    (hZ : Nat.card (Subgroup.center K₀) = 2) (φ : ↥I' →* K₀) (hφs : Function.Surjective φ)
    (hφo : Odd (Nat.card φ.ker)) {u : G} (hu : u ∈ I') (huZ : u ∈ Subgroup.center G) :
    φ ⟨u, hu⟩ = 1 := by
  have hs2' : s' ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s'
  have hcen : ∀ x : ↥I', (∀ y : ↥I', y * x = x * y) → φ x ∈ Subgroup.center K₀ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := hφs z
    rw [← map_mul, ← map_mul, hx y]
  have hsc : ∀ y : ↥I', y * ⟨s', hs'I⟩ = ⟨s', hs'I⟩ * y := fun y => Subtype.ext (hcomm y y.2)
  have huc : ∀ y : ↥I', y * ⟨u, hu⟩ = ⟨u, hu⟩ * y :=
    fun y => Subtype.ext (Subgroup.mem_center_iff.1 huZ y)
  have hs1 : φ ⟨s', hs'I⟩ ≠ 1 := by
    intro h
    have hpow := twoA7_pow_natCard_ker_eq_one φ (x := ⟨s', hs'I⟩) h
    rw [twoA7_pow_eq_self_of_sq_eq_one hs2' hφo] at hpow
    rw [hpow, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  by_contra hu1
  have hφeq : φ ⟨s', hs'I⟩ = φ ⟨u, hu⟩ :=
    congrArg Subtype.val (twoA7_eq_of_natCard_two hZ (a := ⟨φ ⟨s', hs'I⟩, hcen _ hsc⟩)
      (b := ⟨φ ⟨u, hu⟩, hcen _ huc⟩) (fun h => hs1 (congrArg Subtype.val h))
      (fun h => hu1 (congrArg Subtype.val h)))
  have hw : (⟨u, hu⟩ : ↥I')⁻¹ * ⟨s', hs'I⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφeq, inv_mul_cancel]
  have hpow := twoA7_pow_natCard_ker_eq_one φ hw
  have hcomm' : Commute u⁻¹ s' := (Subgroup.mem_center_iff.1 (inv_mem huZ) s').symm
  have hpow' : (u⁻¹) ^ Nat.card φ.ker * s' = 1 := by
    have := hpow
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rwa [hcomm'.mul_pow, twoA7_pow_eq_self_of_sq_eq_one hs2' hφo] at this
  apply hns
  rw [eq_inv_of_mul_eq_one_right hpow']
  exact inv_mem (pow_mem (inv_mem huZ) _)

theorem twoA7_exists_descent {G : Type*} [Group G] {K₀ : Type*} [Group K₀] (I' : Subgroup G)
    (s' : G) (hs2 : orderOf s' = 2) (hs'I : s' ∈ I') (hcomm : ∀ x ∈ I', x * s' = s' * x)
    (hns : s' ∉ Subgroup.center G) (hZ : Nat.card (Subgroup.center K₀) = 2) (φ : ↥I' →* K₀)
    (hφs : Function.Surjective φ) (hφo : Odd (Nat.card φ.ker)) :
    ∃ ψ : ↥(I'.map (QuotientGroup.mk' (Subgroup.center G))) →* K₀,
      Function.Surjective ψ ∧ Odd (Nat.card ψ.ker) := by
  set qI := (QuotientGroup.mk' (Subgroup.center G)).subgroupMap I'
  have hqIs : Function.Surjective qI := MonoidHom.subgroupMap_surjective _ _
  have hker : qI.ker ≤ φ.ker := by
    intro x hx
    have hxZ : (x : G) ∈ Subgroup.center G := by
      have h := congrArg Subtype.val ((MonoidHom.mem_ker).1 hx)
      exact (QuotientGroup.eq_one_iff _).1 h
    exact twoA7_phi_eq_one_of_central I' s' hs2 hs'I hcomm hns hZ φ hφs hφo x.2 hxZ
  set ψ := MonoidHom.liftOfSurjective qI hqIs ⟨φ, hker⟩
  have hcomp : ∀ x, ψ (qI x) = φ x := fun x => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := hφs y
    exact ⟨qI x, by rw [hcomp, hx]⟩
  refine ⟨ψ, hψs, ?_⟩
  have hkerψ : ψ.ker = φ.ker.map qI := by
    ext y
    obtain ⟨x, rfl⟩ := hqIs y
    simp only [MonoidHom.mem_ker, hcomp, Subgroup.mem_map]
    refine ⟨fun h => ⟨x, h, rfl⟩, ?_⟩
    rintro ⟨x', hx', hxx⟩
    rw [← hcomp x, ← hxx, hcomp, hx']
  rw [hkerψ]
  exact Odd.of_dvd_nat hφo (Subgroup.card_map_dvd _ _)

theorem twoA7_oddCore_eq_ker {H : Type*} [Group H] {K₀ : Type*} [Group K₀]
    (hq : CFSG.IsQuasisimple K₀) (hc : Nat.card (Subgroup.center K₀) = 2) (ψ : H →* K₀)
    (hψ : Function.Surjective ψ) (hodd : Odd (Nat.card ψ.ker)) :
    CFSG.Open.classicalInvolutionOddCore H = ψ.ker := by
  refine le_antisymm (sSup_le ?_) (le_sSup ⟨MonoidHom.normal_ker ψ, hodd⟩)
  rintro N ⟨hN, hNo⟩
  have hmap : (N.map ψ).Normal := hN.map ψ hψ
  have hmo : Odd (Nat.card (N.map ψ)) := Odd.of_dvd_nat hNo (Subgroup.card_map_dvd N ψ)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hmap with htop | hle
  · exfalso
    have h2 : 2 ∣ Nat.card K₀ := hc ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center K₀)
    have h3 : Nat.card (N.map ψ) = Nat.card K₀ := by rw [htop]; exact Subgroup.card_top
    rw [h3] at hmo
    exact (Nat.not_even_iff_odd.2 hmo) (even_iff_two_dvd.2 h2)
  · have hdvd : Nat.card (N.map ψ) ∣ 2 := hc ▸ Subgroup.card_dvd_of_le hle
    have h1 : Nat.card (N.map ψ) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hmo
        exact absurd hmo (by decide)
    exact (Subgroup.map_eq_bot_iff N).1 (Subgroup.card_eq_one.1 h1)

theorem twoA7_data_of_mulEquiv {Q K₀ : Type*} [Group Q] [Group K₀] (e : Q ≃* K₀)
    (hq : CFSG.IsQuasisimple K₀) (hc : Nat.card (Subgroup.center K₀) = 2)
    (ha : Nonempty (K₀ ⧸ Subgroup.center K₀ ≃* alternatingGroup (Fin 7))) :
    CFSG.Open.IsQuasisimple Q ∧ Nat.card (Subgroup.center Q) = 2 ∧
      Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 7)) := by
  have hcm : (Subgroup.center Q).map (e : Q →* K₀) = Subgroup.center K₀ :=
    Subgroup.map_center_eq e
  refine ⟨?_, ?_, ?_⟩
  · have h := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
    exact ⟨Group.isPerfect_def.1 h.1, h.2.1⟩
  · rw [← hc, ← hcm]
    exact (Subgroup.card_map_of_injective e.injective).symm
  · obtain ⟨f⟩ := ha
    exact ⟨(QuotientGroup.congr (Subgroup.center Q) (Subgroup.center K₀) e hcm).trans f⟩

theorem twoA7_not_isSolvable_of_surjective {H : Type*} [Group H] {K₀ : Type*} [Group K₀]
    (hq : CFSG.IsQuasisimple K₀) (ψ : H →* K₀) (hψ : Function.Surjective ψ) :
    ¬ Group.IsSolvable H := by
  intro hH
  have hsol : Group.IsSolvable K₀ := Group.isSolvable_of_surjective hψ
  have hnt : Nontrivial K₀ := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hperf : Group.IsPerfect K₀ := hq.1
  exact Group.IsPerfect.not_isSolvable K₀ hsol

theorem twoA7Witness_image {G : Type} [Group G] {K₀ : Type} [Group K₀]
    (I' : Subgroup G) (s' : G) (hs2 : orderOf s' = 2) (hs'I : s' ∈ I')
    (hcomm : ∀ x ∈ I', x * s' = s' * x) (hns : s' ∉ Subgroup.center G)
    (hK₀ : IsDoubleCoverOfAlt K₀ 7) (φ : ↥I' →* K₀) (hφs : Function.Surjective φ)
    (hφo : Odd (Nat.card φ.ker)) :
    TwoA7Witness (I'.map (QuotientGroup.mk' (Subgroup.center G))) ∧
      ¬ Group.IsSolvable (I'.map (QuotientGroup.mk' (Subgroup.center G))) := by
  obtain ⟨hq, hc, ha⟩ := hK₀
  obtain ⟨ψ, hψs, hψo⟩ := twoA7_exists_descent I' s' hs2 hs'I hcomm hns hc φ hφs hφo
  refine ⟨?_, twoA7_not_isSolvable_of_surjective hq ψ hψs⟩
  have hcore := twoA7_oddCore_eq_ker hq hc ψ hψs hψo
  exact twoA7_data_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)) hq hc ha

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
