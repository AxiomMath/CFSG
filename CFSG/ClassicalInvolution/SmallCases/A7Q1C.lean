module

public import CFSG.ClassicalInvolution.SmallCases.A7Q1B
public import CFSG.ClassicalInvolution.SmallCases.A7Q1

public section

namespace CFSG.ClassicalInvolution.A7Q.Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem conjSub_mem_omegaOfSet (hΩ : HypOmegaGen Ω) {K J : Subgroup G} {g : G}
    (hgK : conjSub g⁻¹ K = K) (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) :
    conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) := by
  refine ⟨hΩ.conjInvariant g J hJ.1, fun L hL => ?_⟩
  have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := hgK ▸ twinSet_conj hΩ.conjInvariant hL g⁻¹
  have := omegaNbr_conj hΩ.conjInvariant (hJ.2 _ hL') g
  rwa [conjSub_conjSub_inv] at this

theorem exists_twinFrameData_of_sylows (hΩ : HypOmegaGen Ω) {K K' J R₁ R₂ : Subgroup G}
    {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) (ht : IsUniqueInvolution J t)
    (hR₁ : IsSylow2In R₁ K) (hR₂ : IsSylow2In R₂ K') (hc : Commutes R₁ R₂) :
    ∃ g ∈ K ⊔ K', conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) ∧
      IsUniqueInvolution (conjSub g J) (g * t * g⁻¹) ∧
      (∃ T : Subgroup G, IsSylow2In T (conjSub g J) ∧ Commutes R₁ T ∧ Commutes R₂ T) ∧
      ∀ x ∈ R₁, ∀ y ∈ R₂, orderOf x = 4 → orderOf y = 4 →
        TwinFrameData Ω K K' z (x * y) (conjSub g J) (g * t * g⁻¹) := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  obtain ⟨-, R₀, R₀', T₀, hR₀, hR₀', hT₀, -, -, -, hc₀, hRT₀, hR'T₀⟩ :=
    exists_twinSylow hΩ hK hz hK' hne hJ
  obtain ⟨g, hgQ, hgR, hgR'⟩ :=
    exists_conj_sylow_pair hΩ hK hK'Ω hne hz hzK' hR₁ hR₂ hc hR₀ hR₀' hc₀
  have hgiK : conjSub g⁻¹ K = K :=
    (conjSub_eq_of_mem_sup hΩ hK hK'Ω hne hz hzK' (Subgroup.inv_mem _ hgQ)).1
  have hJ' : conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) := conjSub_mem_omegaOfSet hΩ hgiK hJ
  have ht' : IsUniqueInvolution (conjSub g J) (g * t * g⁻¹) := ht.conj g
  have hTsyl : IsSylow2In (conjSub g T₀) (conjSub g J) := hT₀.conj g
  have hT8 : 8 ≤ Nat.card ↥(conjSub g T₀) :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ'.1 hTsyl)
  have htT : g * t * g⁻¹ ∈ conjSub g T₀ :=
    mem_of_isUniqueInvolution_of_isPGroup ht' hTsyl.1 hTsyl.2.1 (by omega)
  have hcRT : Commutes R₁ (conjSub g T₀) := hgR ▸ hRT₀.conjSub g
  have hcR'T : Commutes R₂ (conjSub g T₀) := hgR' ▸ hR'T₀.conjSub g
  refine ⟨g, hgQ, hJ', ht', ⟨conjSub g T₀, hTsyl, hcRT, hcR'T⟩, fun x hx y hy hx4 hy4 => ?_⟩
  have hxK : x ∈ K := hR₁.1 hx
  have hyK' : y ∈ K' := hR₂.1 hy
  have hsqx : x * x = z := T7A.sq_eq_of_orderOf_four hz hxK hx4
  have hsqy : y * y = z := T7A.sq_eq_of_orderOf_four hzK' hyK' hy4
  have hcxy : x * y = y * x := hc x hx y hy
  have hxK' : x ∉ K' := not_mem_of_orderOf_four hΩ hK hK'Ω hne hx4 hxK
  have hu2 : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hcxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hsqx, hsqy, hz.sq]
  have hu1 : x * y ≠ 1 := by
    intro h
    apply hxK'
    rw [eq_inv_of_mul_eq_one_left h]
    exact K'.inv_mem hyK'
  have huz : x * y ≠ z := by
    intro h
    apply hxK'
    have : x = z * y⁻¹ := by rw [← h]; group
    rw [this]
    exact K'.mul_mem hzK'.mem (K'.inv_mem hyK')
  have htu : (g * t * g⁻¹) * (x * y) = (x * y) * (g * t * g⁻¹) := by
    have h1 : x * (g * t * g⁻¹) = (g * t * g⁻¹) * x := hcRT x hx _ htT
    have h2 : y * (g * t * g⁻¹) = (g * t * g⁻¹) * y := hcR'T y hy _ htT
    calc (g * t * g⁻¹) * (x * y) = ((g * t * g⁻¹) * x) * y := by group
      _ = (x * (g * t * g⁻¹)) * y := by rw [h1]
      _ = x * ((g * t * g⁻¹) * y) := by group
      _ = x * (y * (g * t * g⁻¹)) := by rw [h2]
      _ = (x * y) * (g * t * g⁻¹) := by group
  exact ⟨hK, hz, hK', hne, Subgroup.mul_mem _ (Subgroup.mem_sup_left hxK)
    (Subgroup.mem_sup_right hyK'), hu2, hu1, huz, hJ', ht', htu⟩

theorem sq_eq_of_mul (hΩ : HypOmegaGen Ω) {K K' R₁ R₂ : Subgroup G} {z x y : G} (hK : K ∈ Ω)
    (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hR₁ : IsSylow2In R₁ K) (hR₂ : IsSylow2In R₂ K') (hc : Commutes R₁ R₂) (hx : x ∈ R₁)
    (hy : y ∈ R₂) (hu2 : (x * y) * (x * y) = 1) (hu1 : x * y ≠ 1) (huz : x * y ≠ z) :
    x * x = z ∧ y * y = z := by
  have hcxy : x * y = y * x := hc x hx y hy
  have hsq : (x * x) * (y * y) = 1 := by
    calc (x * x) * (y * y) = x * (x * y) * y := by group
      _ = x * (y * x) * y := by rw [hcxy]
      _ = (x * y) * (x * y) := by group
      _ = 1 := hu2
  have hxK : x ∈ K := hR₁.1 hx
  have hyK' : y ∈ K' := hR₂.1 hy
  have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
    Sec6Gen.card_le_two_of_le_inf hΩ hK hK' hne.symm (hR₁.2.1.to_le inf_le_left)
      (inf_le_left.trans hR₁.1) (inf_le_right.trans hR₂.1)
  have hxxA : x * x ∈ R₁ ⊓ R₂ := by
    refine ⟨R₁.mul_mem hx hx, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hsq]
    exact R₂.inv_mem (R₂.mul_mem hy hy)
  have hxx : (x * x) * (x * x) = 1 := by
    have h2 : orderOf (x * x) ∣ 2 := by
      have hd : orderOf (x * x) ∣ Nat.card ↥(R₁ ⊓ R₂) := Subgroup.orderOf_dvd_natCard _ hxxA
      interval_cases hc2 : Nat.card ↥(R₁ ⊓ R₂)
      · exact absurd hc2 Nat.card_pos.ne'
      · exact hd.trans (one_dvd 2)
      · exact hd
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  have hx2 : x * x = z := by
    rcases hz.unique (x * x) (K.mul_mem hxK hxK) hxx with h1 | h1
    · exfalso
      have hy2 : y * y = 1 := by rwa [h1, one_mul] at hsq
      rcases hz.unique x hxK h1 with h2 | h2 <;> rcases hz'.unique y hyK' hy2 with h3 | h3
      · exact hu1 (by rw [h2, h3, one_mul])
      · exact huz (by rw [h2, h3, one_mul])
      · exact huz (by rw [h2, h3, mul_one])
      · exact hu1 (by rw [h2, h3]; exact hz.sq)
    · exact h1
  have h1 : z * (y * y) = 1 := by rwa [hx2] at hsq
  refine ⟨hx2, ?_⟩
  rw [eq_inv_of_mul_eq_one_right h1]
  exact inv_eq_of_mul_eq_one_right hz.sq

theorem exists_twinFrameData_at (hΩ : HypOmegaGen Ω) {K K' J' : Subgroup G} {z u t' : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hJ' : J' ∈ omegaOfSet Ω (twinSet Ω K)) (ht' : IsUniqueInvolution J' t') :
    ∃ g ∈ K ⊔ K', TwinFrameData Ω K K' z u (conjSub g J') (g * t' * g⁻¹) := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  obtain ⟨R₁, R₂, hR₁, hR₂, hc, huR⟩ :=
    exists_sylow_pair_of_mem hΩ hK hK'.1 hne hz hzK' hu hu2 hu1
  obtain ⟨g, hgQ, -, -, -, hfr⟩ :=
    exists_twinFrameData_of_sylows hΩ hK hz hK' hne hJ' ht' hR₁ hR₂ hc
  obtain ⟨x, hx, y, hy, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc huR
  obtain ⟨hx2, hy2⟩ := sq_eq_of_mul hΩ hK hK'.1 hne hz hzK' hR₁ hR₂ hc hx hy hu2 hu1 huz
  exact ⟨g, hgQ, hfr x hx y hy (T7A.orderOf_eq_four_of_sq hz hx2)
    (T7A.orderOf_eq_four_of_sq hz hy2)⟩

theorem exists_mem_omegaOfSet_twinSet (hΩ : HypOmegaGen Ω) {K : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hne : KPerp Ω K ≠ twinSet Ω K) :
    ∃ J ∈ omegaOfSet Ω (twinSet Ω K), J ∉ twinSet Ω K := by
  have hsub : twinSet Ω K ⊆ KPerp Ω K := fun L hL =>
    mem_kPerp_of_twin hΩ hL.1 hK (isUniqueInvolution_of_mem_twinSet hz hL) hz
  by_contra hcon
  push Not at hcon
  refine hne (Set.Subset.antisymm (fun J hJ => ?_) hsub)
  by_contra hJnot
  exact hJnot (hcon J (mem_omegaOfSet_of_mem_kPerp hΩ hK hJ hJnot))

theorem exists_twinFrameData (hΩ : HypOmegaGen Ω) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hperp : KPerp Ω K ≠ twinSet Ω K) :
    ∃ (u : G) (J : Subgroup G) (t : G), TwinFrameData Ω K K' z u J t := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  obtain ⟨J, hJ, -⟩ := exists_mem_omegaOfSet_twinSet hΩ hK hz hperp
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  obtain ⟨R₁, R₂, hR₁, hR₂, hc⟩ := exists_commuting_sylow_twin hΩ hK hK'.1 hne hz hzK'
  obtain ⟨g, -, -, -, -, hfr⟩ :=
    exists_twinFrameData_of_sylows hΩ hK hz hK' hne hJ ht hR₁ hR₂ hc
  obtain ⟨x, hx, hx4⟩ :=
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR₁)).exists_orderOf_four
  obtain ⟨y, hy, hy4⟩ :=
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK'.1 hR₂)).exists_orderOf_four
  exact ⟨x * y, conjSub g J, g * t * g⁻¹, hfr x hx y hy hx4 hy4⟩

end CFSG.ClassicalInvolution.A7Q.Gen
