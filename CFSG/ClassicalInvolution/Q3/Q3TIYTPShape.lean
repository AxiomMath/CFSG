module

public import CFSG.ClassicalInvolution.Q3.Q3TLKLink
public import CFSG.ClassicalInvolution.Q3.Q3TIYTPCore
public import CFSG.ClassicalInvolution.Q3.Q3TY1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Q3.Q3TLK
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u)
open CFSG.ClassicalInvolution.Q3.Q3OF (IsProductElt3)

section Component

variable {X : Type} [Group X]

theorem fund_eq_top_of_central_image {c : CompData} (hv : c.Valid) (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) {R : Subgroup c.G} (hR : R ∈ c.fund) {r : c.G}
    (hrR : r ∈ R) (hr1 : ψ r ≠ 1) (hcen : ∀ y : c.G, ψ y * ψ r = ψ r * ψ y) :
    ∀ R' ∈ c.fund, R' = ⊤ := by
  have hcomm : ∀ y : c.G, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center c.G := by
    intro y
    apply hker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    calc ψ r * ψ y * (ψ r)⁻¹ * (ψ y)⁻¹ = (ψ y * ψ r) * (ψ r)⁻¹ * (ψ y)⁻¹ := by
          rw [hcen y]
      _ = 1 := by group
  rcases hv with ⟨t', n', hft, hadm, hc⟩ | hc | hc
  · subst hc
    by_cases hA1 : t' = .PSL ∧ n' = 2
    · obtain ⟨rfl, rfl⟩ := hA1
      intro R' hR'
      exact ModelFacts.fundamentalSubgroups_eq_top_PSL_two 3 1 Nat.prime_three hadm R' hR'
    · exfalso
      have := ModelFacts.fundNoncentral_generic 3 t' n' 1 hft hadm hA1 R hR r hrR hcomm
      exact hr1 (by rw [this, map_one])
  · subst hc
    intro R' hR'
    exact Set.mem_singleton_iff.mp hR'
  · exfalso
    subst hc
    have hcen' : Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 = ⊥ :=
      center_m11_eq_bot m11Facts
    have hr : r ∈ Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := hcomm y
      rw [hcen', Subgroup.mem_bot] at h1
      calc y * r = (r * y * r⁻¹ * y⁻¹) * (y * r) := by rw [h1]; group
        _ = r * y := by group
    rw [hcen', Subgroup.mem_bot] at hr
    exact hr1 (by rw [hr, map_one])

end Component

section Shape

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}

theorem isolated_of_involution_eq (h3 : OddThreeFreeInput) (hR : RouteD3Setup K z)
    {N : Subgroup G} (hN : N ∈ centralizingMembers (conjClass3 K) {z})
    (hcls : IsClassicalMember3 N z) :
    ∀ M ∈ centralizingMembers (conjClass3 K) {z}, M ≠ N → Commutes N M := by
  classical
  have hΩ := hR.inClass
  have hex := hR.setup.1
  have hP1 : LocalOddCentral (conjClass3 K) {z} := hR.setup.2
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z := h3 G K z hR
  have hnab := routeD3_nonabelian hR
  have hznc : ¬ ({z} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hnab hR.cls.ne_one
  obtain ⟨ι, hι, ⟨D⟩⟩ := hR.ih {z} hznc
  have hNf : locImg (conjClass3 K) z N ∈ locFamily (conjClass3 K) z :=
    mem_locFamily_iff.mpr ⟨N, hN, rfl⟩
  obtain ⟨i, R, hRf, hNR⟩ := D.fundamental _ hNf
  have hzY : z ∈ locLayer (conjClass3 K) z := le_centralizingLayer hN hcls.mem
  have hzb1 : locMk (conjClass3 K) z ⟨z, hzY⟩ ≠ 1 := locMk_involution_ne_one3 hN hcls
  have hzbc : ∀ q : locQuot (conjClass3 K) z,
      q * locMk (conjClass3 K) z ⟨z, hzY⟩ = locMk (conjClass3 K) z ⟨z, hzY⟩ * q := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    show locMk (conjClass3 K) z y * locMk (conjClass3 K) z ⟨z, hzY⟩ =
      locMk (conjClass3 K) z ⟨z, hzY⟩ * locMk (conjClass3 K) z y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer (conjClass3 K) {z} y.2)
  have hzbN : locMk (conjClass3 K) z ⟨z, hzY⟩ ∈ locImg (conjClass3 K) z N :=
    Subgroup.mem_map.mpr ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hcls.mem, rfl⟩
  rw [hNR] at hzbN
  obtain ⟨r, hrR, hr⟩ := Subgroup.mem_map.mp hzbN
  have htop := fund_eq_top_of_central_image (D.valid i) (D.hom i) (D.ker_le_center i) hRf hrR
    (by rw [hr]; exact hzb1) (fun y => by rw [hr]; exact hzbc _)
  intro M hM hMN
  have hMf : locImg (conjClass3 K) z M ∈ locFamily (conjClass3 K) z :=
    mem_locFamily_iff.mpr ⟨M, hM, rfl⟩
  obtain ⟨j, R', hR'j, hMR'⟩ := D.fundamental _ hMf
  by_cases hji : j = i
  · subst hji
    exfalso
    apply hMN
    refine locImg_injOn3 hΩ hex hP1 hO3 hM hN ?_
    rw [hMR', hNR, htop R' hR'j, htop R hRf]
  · refine commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hN hM ?_
    rw [hNR, hMR']
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact D.commute i j (fun h => hji h.symm) a b

theorem exists_member_involution_ne (hR : RouteD3Setup K z) :
    ∃ J ∈ centralizingMembers (conjClass3 K) {z}, ∃ t : G, IsClassicalMember3 J t ∧ t ≠ z := by
  by_contra hno
  push Not at hno
  have hnab := routeD3_nonabelian hR
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨⟨1, conjSub_one K⟩, isSubnormal_le hR.cls.subnormal⟩
  have hz : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, z ∈ N := by
    intro N hN
    obtain ⟨w, hw⟩ := hR.inClass.classical N hN.1
    rw [← hno N hN w hw]
    exact hw.mem
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  have hsub : conjClass3 K ⊆ centralizingMembers (conjClass3 K) {z} :=
    subset_of_adj_closed hconn (fun N hN => hN.1) ⟨K, hKz⟩ (by
      intro N hN L hL hLN hcomm
      exact ⟨hL, fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr
        (hcomm z (hz N hN) l hl).symm⟩)
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [← hR.inClass.generated]
    exact iSup₂_le fun L hL => (hsub hL).2
  have hzc : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top g))
  exact Balance.not_subset_center_of_ne_one hnab hR.cls.ne_one (Set.singleton_subset_iff.mpr hzc)

theorem mem_sup_iff_of_commutes {K T : Subgroup G} (hKT : Commutes K T) {x : G} (hx : x ∈ K ⊔ T) :
    ∃ k ∈ K, ∃ t ∈ T, x = k * t := by
  let S : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ t ∈ T, x = k * t}
      one_mem' := ⟨1, K.one_mem, 1, T.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, t₁, ht₁, rfl⟩ ⟨k₂, hk₂, t₂, ht₂, rfl⟩
        refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, t₁ * t₂, T.mul_mem ht₁ ht₂, ?_⟩
        have : t₁ * k₂ = k₂ * t₁ := (hKT k₂ hk₂ t₁ ht₁).symm
        calc k₁ * t₁ * (k₂ * t₂) = k₁ * (t₁ * k₂) * t₂ := by group
          _ = k₁ * (k₂ * t₁) * t₂ := by rw [this]
          _ = k₁ * k₂ * (t₁ * t₂) := by group
      inv_mem' := by
        rintro _ ⟨k, hk, t, ht, rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, t⁻¹, T.inv_mem ht, ?_⟩
        have : k * t = t * k := hKT k hk t ht
        calc (k * t)⁻¹ = (t * k)⁻¹ := by rw [this]
          _ = k⁻¹ * t⁻¹ := by group }
  have hle : K ⊔ T ≤ S :=
    sup_le (fun k hk => ⟨k, hk, 1, T.one_mem, by simp⟩)
      (fun t ht => ⟨1, K.one_mem, t, ht, by simp⟩)
  exact hle hx

theorem exists_twinElt_of_productElt (hz : IsClassicalMember3 K z) (hzT : IsClassicalMember3 T z)
    (hexK : classicalInvolutionOddCore K = ⊥) (hKT : Commutes K T) {u : G} (hu : u ∈ K ⊔ T)
    (hu2 : orderOf u = 2) (huK : u ∉ K) (huT : u ∉ T) : ∃ e : TwinElt K T z, e.u = u := by
  obtain ⟨k, hk, t', ht', rfl⟩ := mem_sup_iff_of_commutes hKT hu
  have hz2 : z * z = 1 := hz.isCentralInvolution.sq
  have huu : (k * t') * (k * t') = 1 := Q3NT.mul_self_eq_one_of_orderOf_eq_two hu2
  have hkt : k * t' = t' * k := hKT k hk t' ht'
  have hsq : (k * k) * (t' * t') = 1 := by
    calc (k * k) * (t' * t') = k * (k * t') * t' := by group
      _ = k * (t' * k) * t' := by rw [hkt]
      _ = (k * t') * (k * t') := by group
      _ = 1 := huu
  have hkkK : k * k ∈ K := K.mul_mem hk hk
  have hkkcen : ∀ y ∈ K, y * (k * k) = (k * k) * y := by
    intro y hy
    have hmemT : k * k = (t' * t')⁻¹ := eq_inv_of_mul_eq_one_left hsq
    have hT' : t' * t' ∈ T := T.mul_mem ht' ht'
    have : (t' * t')⁻¹ ∈ T := T.inv_mem hT'
    rw [hmemT]
    have h1 : y * (t' * t') = (t' * t') * y := hKT y hy _ hT'
    calc y * (t' * t')⁻¹ = (t' * t')⁻¹ * ((t' * t') * y) * (t' * t')⁻¹ := by group
      _ = (t' * t')⁻¹ * (y * (t' * t')) * (t' * t')⁻¹ := by rw [h1]
      _ = (t' * t')⁻¹ * y := by group
  rcases Q3TY.eq_one_or_eq_of_central3 hz hexK hkkK hkkcen with h1 | h1
  ·
    exfalso
    apply huK
    have ht'sq : t' * t' = 1 := by rw [h1, one_mul] at hsq; exact hsq
    have hk' : k = 1 ∨ k = z := by
      by_cases hk1 : k = 1
      · exact Or.inl hk1
      · exact Or.inr (Q3TY.eq_of_mem_of_sq hz hk h1 hk1)
    have ht'' : t' = 1 ∨ t' = z := by
      by_cases ht1 : t' = 1
      · exact Or.inl ht1
      · exact Or.inr (Q3TY.eq_of_mem_of_sq hzT ht' ht'sq ht1)
    rcases hk' with rfl | rfl <;> rcases ht'' with rfl | rfl
    · simp
    · simpa using hz.mem
    · simpa using hz.mem
    · rw [hz2]
      exact K.one_mem
  · have ht'z : t' * t' = z := by
      have : t' * t' = (k * k)⁻¹ := eq_inv_of_mul_eq_one_right hsq
      rw [this, h1]
      exact inv_eq_of_mul_eq_one_right hz2
    exact ⟨⟨k, t', hk, ht', h1, ht'z⟩, rfl⟩

end Shape

@[expose] def TwinP1R3Central3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    RouteD3Setup K z → ∀ T ∈ conjClass3 K, T ≠ K → IsClassicalMember3 T z → Commutes K T →
      ∀ u : G, IsProductElt3 K T u →
        LocalOddCentral (conjClass3 K) {u} ∧ LocalOddThreeFree3 (conjClass3 K) u

end CFSG.ClassicalInvolution.Q3.Q3TIY
