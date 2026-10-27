module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RE
public import CFSG.GH74.GLS.C3.Layer1.Thm1Layer
public import CFSG.GH74.GLS.C3.Layer1.Th2L625b

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P39R

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.GH74.GLS.C3.Layer1

theorem odd_index_arith {q₀ m cK cH : ℕ} (hq₀ : Odd q₀) (h3 : 3 ≤ q₀)
    (hK : cK = q₀ ^ 2 * ((q₀ ^ 2) ^ 2 - 1) / 2) (hH : cH = q₀ * (q₀ ^ 2 - 1))
    (hm : cK = cH * m) : Odd m := by
  obtain ⟨k, rfl⟩ := hq₀
  have hk1 : 1 ≤ k := by omega
  set t := k * (k + 1) with ht
  have ht1 : 1 ≤ t := Nat.mul_pos (by omega) (by omega)
  have hsq : (2 * k + 1) ^ 2 = 4 * t + 1 := by rw [ht]; ring
  have hsq1 : (2 * k + 1) ^ 2 - 1 = 4 * t := by omega
  have hsq2 : ((2 * k + 1) ^ 2) ^ 2 - 1 = 8 * t * (2 * t + 1) := by
    rw [hsq]
    have : (4 * t + 1) ^ 2 = 8 * t * (2 * t + 1) + 1 := by ring
    omega
  have hcK : cK = (4 * t + 1) * (4 * t * (2 * t + 1)) := by
    rw [hK, hsq2, hsq]
    have : (4 * t + 1) * (8 * t * (2 * t + 1)) = 2 * ((4 * t + 1) * (4 * t * (2 * t + 1))) := by ring
    rw [this]
    omega
  have hcH : cH = (2 * k + 1) * (4 * t) := by rw [hH, hsq1]
  rw [hcK, hcH] at hm
  have hm' : (4 * t) * ((4 * t + 1) * (2 * t + 1)) = (4 * t) * ((2 * k + 1) * m) := by
    calc (4 * t) * ((4 * t + 1) * (2 * t + 1)) = (4 * t + 1) * (4 * t * (2 * t + 1)) := by ring
      _ = (2 * k + 1) * (4 * t) * m := hm
      _ = (4 * t) * ((2 * k + 1) * m) := by ring
  have hm'' := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4 * t) hm'
  rw [← hsq] at hm''
  have hm3 : (2 * k + 1) * ((2 * k + 1) * (2 * t + 1)) = (2 * k + 1) * m := by
    calc (2 * k + 1) * ((2 * k + 1) * (2 * t + 1)) = (2 * k + 1) ^ 2 * (2 * t + 1) := by ring
      _ = (2 * k + 1) * m := hm''
  have hm4 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * k + 1) hm3
  rw [← hm4]
  exact Odd.mul ⟨k, rfl⟩ ⟨t, rfl⟩

section Fixed

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem odd_index_fixedSubgroup (hF : L2Field F) (e : K ≃* L2 F)
    {σ : MulAut K} (hσ : σ ∈ fieldAutSub e) (hσ2 : orderOf σ = 2) :
    Odd (CFSG.GH74.GLS.fixedSubgroup K σ).index := by
  obtain ⟨τ, rfl⟩ := hσ
  have hinj : Function.Injective (fieldAutHom e) := fun a b hab => by
    have := congrArg (fieldProj e) hab
    rwa [fieldProj_fieldAutHom, fieldProj_fieldAutHom] at this
  have hτ2 : orderOf τ = 2 := by
    rw [← orderOf_injective (fieldAutHom e) hinj τ]
    exact hσ2
  obtain ⟨F₀, hF₀, hFin₀, hcard, ⟨eqv⟩⟩ :=
    (ivk_1_4a F hF K e τ).2.2 (by rw [hτ2]; exact even_two)
  rw [hτ2] at hcard
  have hodd₀ : Odd (Nat.card F₀) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have : Even (Nat.card F) := by
      rw [← hcard]
      exact Nat.even_pow.2 ⟨hne, by norm_num⟩
    exact (Nat.not_even_iff_odd.2 hF.1) this
  have h3₀ : 3 ≤ Nat.card F₀ := by
    have hq3 : 3 < Nat.card F := hF.2
    have h2 : 2 ≤ Nat.card F₀ := by
      by_contra hlt
      push Not at hlt
      have hle : Nat.card F₀ ≤ 1 := by omega
      have : Nat.card F ≤ 1 := by
        rw [← hcard]
        calc Nat.card F₀ ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left hle 2
          _ = 1 := by norm_num
      omega
    obtain ⟨m, hm⟩ := hodd₀
    omega
  have hKcard : Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := card_eq_of_L2Field e hF
  have hHcard : Nat.card ↥(fixedSubgroup K (fieldAutHom e τ)) = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := by
    rw [Nat.card_congr eqv.toEquiv]
    exact pgl2_card_formula F₀
  have hmul := Subgroup.card_mul_index (fixedSubgroup K (fieldAutHom e τ))
  refine odd_index_arith (cK := Nat.card K) (cH := Nat.card ↥(fixedSubgroup K (fieldAutHom e τ)))
    hodd₀ h3₀ ?_ hHcard hmul.symm
  rw [hKcard, ← hcard]


end Fixed

section Sylow

variable {G : Type} [Group G]

theorem mem_zpowers_of_isSylowOf_of_central [Finite G] {H : Subgroup G} {f x : G}
    (hS : IsSylowOf 2 (zpowers f) H) (hfc : ∀ h ∈ H, h * f = f * h) (hxH : x ∈ H)
    (hx2 : orderOf x = 2) : x ∈ zpowers f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, sq] at this
  have hzp : IsPGroup 2 ↥(zpowers x) := Thm1.isPGroup_zpowers_of_pow_eq_one ⟨1, by simpa [sq] using hxx⟩
  obtain ⟨T', hxT', hT'H, hT'p, hT'idx⟩ := P34.exists_sylow_ge (N := H) (zpowers_le.2 hxH) hzp
  have hT' : IsSylowOf 2 T' H := isSylowOf_iff.2 ⟨hT'H, hT'p, hT'idx⟩
  obtain ⟨k, hkH, hk⟩ := hS.exists_mem_conj hT'
  have h1 : k⁻¹ * x * k ∈ zpowers f := (hk x).1 (hxT' (mem_zpowers x))
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 h1
  have hkf : Commute k f := hfc k hkH
  have hx : x = f ^ n := by
    have : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [this, ← hn]
    calc k * f ^ n * k⁻¹ = f ^ n * k * k⁻¹ := by rw [(hkf.zpow_right n).eq]
      _ = f ^ n := by group
  rw [hx]
  exact zpow_mem_zpowers f n


omit [Group G] in
theorem factorization_two_mul_odd {a b : ℕ} (ha : a ≠ 0) (hb : Odd b) :
    (a * b).factorization 2 = a.factorization 2 := by
  have hb0 : b ≠ 0 := hb.pos.ne'
  have h2 : b.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.odd_iff, Nat.dvd_iff_mod_eq_zero] using hb)
  rw [Nat.factorization_mul ha hb0, Finsupp.add_apply, h2, add_zero]

theorem exists_isSylowOf_centralized [Finite G] {J : Subgroup G} {f₁ x : G}
    (hJn : ∀ c ∈ centralizer ({f₁} : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    (hxC : x ∈ centralizer ({f₁} : Set G)) (hx2 : orderOf x = 2)
    {F : Type} [Field F] [Finite F] (hF : L2Field F) (e' : kBar J ≃* L2 F)
    (hσ : Back.actHom hJn ⟨x, hxC⟩ ∈ fieldAutSub e')
    (hσ2 : orderOf (Back.actHom hJn ⟨x, hxC⟩) = 2) :
    ∃ S : Subgroup G, IsSylowOf 2 S J ∧ ∀ s ∈ S, x * s = s * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup G := J ⊓ centralizer ({x} : Set G) with hD
  set xh := Back.actHom hJn ⟨x, hxC⟩ with hxh
  have hψ := Thm1.centMap_surjective hJn hxC hx2
  have hker := Thm1.centMap_ker_odd hJn hxC
  obtain ⟨S, hS⟩ := exists_isSylowOf (G := G) 2 D
  refine ⟨S, ?_, fun s hs => (mem_centralizer_singleton_iff.1 (hS.le hs).2).symm⟩
  have hSJ : S ≤ J := hS.le.trans inf_le_left
  refine isSylowOf_of_card hSJ ?_
  have hD1 : Nat.card ↥D = Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup (kBar J) xh) *
      Nat.card (Thm1.centMap hJn hxC).ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Thm1.centMap hJn hxC).ker
    have h2 : Nat.card (↥D ⧸ (Thm1.centMap hJn hxC).ker) =
        Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup (kBar J) xh) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hψ).toEquiv
    rw [h2] at h1
    exact h1
  have hfix0 : Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup (kBar J) xh) ≠ 0 := Nat.card_pos.ne'
  have hv1 : (Nat.card ↥D).factorization 2 =
      (Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup (kBar J) xh)).factorization 2 := by
    rw [hD1]
    exact factorization_two_mul_odd hfix0 hker
  have hmul := Subgroup.card_mul_index (CFSG.GH74.GLS.fixedSubgroup (kBar J) xh)
  have hv2 : (Nat.card (kBar J)).factorization 2 =
      (Nat.card ↥(CFSG.GH74.GLS.fixedSubgroup (kBar J) xh)).factorization 2 := by
    rw [← hmul]
    exact factorization_two_mul_odd hfix0 (odd_index_fixedSubgroup hF e' hσ hσ2)
  have hv3 : twoPartCard J = 2 ^ (Nat.card (kBar J)).factorization 2 :=
    Th2.L625.twoPartCard_eq_of_card_kBar J rfl
  rw [hS.card_eq, hv1, ← hv2, ← hv3]
  rfl


theorem exists_fieldAut_actHom [Finite G] {J I : Subgroup G} {f₁ x : G} (hIJ : I ≤ J)
    (hJn : ∀ c ∈ centralizer ({f₁} : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    (hxC : x ∈ centralizer ({f₁} : Set G)) (hx2 : orderOf x = 2) (hf2 : orderOf f₁ = 2)
    (hxf : x ≠ f₁) (hS : IsSylowOf 2 (zpowers f₁) (CxK f₁ J))
    (hIx : ∀ c ∈ I, x * c = c * x) (hIns : ¬ Group.IsSolvable (kBar I))
    {F : Type} [Field F] [Finite F] (hF : L2Field F) (e : kBar J ≃* L2 F) :
    ∃ e' : kBar J ≃* L2 F, Back.actHom hJn ⟨x, hxC⟩ ∈ fieldAutSub e' ∧
      orderOf (Back.actHom hJn ⟨x, hxC⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set xh := Back.actHom hJn ⟨x, hxC⟩ with hxh
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, sq] at this
  have hff : f₁ * f₁ = 1 := by
    have := pow_orderOf_eq_one f₁
    rwa [hf2, sq] at this
  have hxh2 : xh ^ 2 = 1 := by
    have h1 : (⟨x, hxC⟩ : ↥(centralizer ({f₁} : Set G))) ^ 2 = 1 :=
      Subtype.ext (by simpa [sq] using hxx)
    rw [hxh, ← map_pow, h1, map_one]
  have hxh1 : xh ≠ 1 := by
    intro h1
    have hker : (⟨x, hxC⟩ : ↥(centralizer ({f₁} : Set G))) ∈ (Back.actHom hJn).ker := h1
    rw [Back.actHom_ker hJn] at hker
    have hxCx : x ∈ CxK f₁ J := hker
    have hxin : x ∈ zpowers f₁ :=
      mem_zpowers_of_isSylowOf_of_central hS
        (fun h hh => mem_centralizer_singleton_iff.1 hh.1) hxCx hx2
    rcases Thm1P310.eq_one_or_eq_of_mem_zpowers hff hxin with h | h
    · rw [h, orderOf_one] at hx2
      omega
    · exact hxf h
  have hker0 : (TwoThin.hatMap hIJ).ker ≤ pPrimeCore 2 ↥I :=
    le_sSup ⟨MonoidHom.normal_ker _, Nat.coprime_two_left.mpr (TwoThin.odd_card_ker_hatMap hIJ)⟩
  have hle : (TwoThin.hatMap hIJ).range ≤ CFSG.GH74.GLS.fixedSubgroup (kBar J) xh := by
    rintro _ ⟨c, rfl⟩
    show xh (QuotientGroup.mk (⟨(c : G), hIJ c.2⟩ : ↥J)) = QuotientGroup.mk (⟨(c : G), hIJ c.2⟩ : ↥J)
    rw [hxh, Back.actHom_mk hJn ⟨x, hxC⟩ ⟨c, hIJ c.2⟩]
    congr 1
    apply Subtype.ext
    show x * (c : G) * x⁻¹ = c
    rw [hIx c c.2]
    group
  have hns : ¬ Group.IsSolvable ↥(CFSG.GH74.GLS.fixedSubgroup (kBar J) xh) := by
    intro hsolv
    have hrange : Group.IsSolvable ↥(TwoThin.hatMap hIJ).range :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    have hquot : Group.IsSolvable (↥I ⧸ (TwoThin.hatMap hIJ).ker) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (QuotientGroup.quotientKerEquivRange (TwoThin.hatMap hIJ)).toMonoidHom)
        (QuotientGroup.quotientKerEquivRange (TwoThin.hatMap hIJ)).injective
    have hmap : (TwoThin.hatMap hIJ).ker ≤ (pPrimeCore 2 ↥I).comap (MonoidHom.id ↥I) := by
      simpa using hker0
    have hsurj : Function.Surjective
        (QuotientGroup.map (TwoThin.hatMap hIJ).ker (pPrimeCore 2 ↥I) (MonoidHom.id ↥I) hmap) := by
      intro y
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨QuotientGroup.mk a, rfl⟩
    exact hIns (Group.isSolvable_of_surjective hsurj)
  obtain ⟨e', he'⟩ := exists_fieldAut_of_not_solvable_fixed hF e hxh2 hxh1 hns
  exact ⟨e', he', orderOf_eq_prime hxh2 hxh1⟩

end Sylow

end CFSG.GH74.GLS.C3.Layer1.Thm1P39R
