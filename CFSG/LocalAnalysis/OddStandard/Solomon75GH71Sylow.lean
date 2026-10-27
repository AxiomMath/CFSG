module

public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Pairing
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

theorem eq_one_of_mul_self_eq_one_of_mem_odd {X : Type*} [Group X] {N : Subgroup X}
    (hN : Odd (Nat.card N)) {x : X}
    (hxN : x ∈ N) (hx : x * x = 1) : x = 1 := by
  have h1 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxN
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exfalso
    rw [h] at h1
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 h1)

theorem exists_sylow_eq_map_core {G : Type} [Group G] [Finite G] {t : G} (C : Subgroup G)
    (hCmem : ∀ g, g ∈ C ↔ g * t = t * g) (ht : orderOf t = 2) {n : ℕ} (hn : 8 ≤ n)
    (hcov : IsDoubleCoverOfAlt (↥C ⧸ pPrimeCore 2 ↥C) n) (T : Sylow 2 ↥C) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = (T : Subgroup ↥C).map C.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥C)) := by
    have hc : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥C)) := pPrimeCore_coprime_card
    exact Nat.coprime_two_left.mp hc
  have hπs : Function.Surjective (QuotientGroup.mk' (pPrimeCore 2 ↥C)) :=
    QuotientGroup.mk'_surjective _
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq ht)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hT₀p : IsPGroup 2 ((T : Subgroup ↥C).map C.subtype) := T.isPGroup'.map C.subtype
  obtain ⟨P, hTP⟩ := hT₀p.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hTP⟩
  by_contra hPT
  have hT1 : ((T : Subgroup ↥C).map C.subtype).subgroupOf (P : Subgroup G) ≠ ⊤ := by
    rw [Ne, Subgroup.subgroupOf_eq_top]
    exact hPT
  have : Finite ↥(P : Subgroup G) := inferInstance
  have : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup G))
  obtain ⟨x, hxn, hxT⟩ := IsConcreteLE.exists_of_lt (hnc _ (lt_top_iff_ne_top.2 hT1))
  have hx'P : (x : G) ∈ (P : Subgroup G) := x.2
  have hx'T : (x : G) ∉ (T : Subgroup ↥C).map C.subtype := fun h => hxT (by
    rw [Subgroup.mem_subgroupOf]
    exact h)
  have hxnorm : ∀ s : G, s ∈ (T : Subgroup ↥C).map C.subtype →
      (x : G) * s * (x : G)⁻¹ ∈ (T : Subgroup ↥C).map C.subtype ∧
      (x : G)⁻¹ * s * (x : G) ∈ (T : Subgroup ↥C).map C.subtype := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff] at hxn
    have hsP : s ∈ (P : Subgroup G) := hTP hs
    have h1 := (hxn ⟨s, hsP⟩).1 (by rw [Subgroup.mem_subgroupOf]; exact hs)
    rw [Subgroup.mem_subgroupOf] at h1
    refine ⟨h1, ?_⟩
    have hP2 : (x : G)⁻¹ * s * (x : G) ∈ (P : Subgroup G) :=
      P.mul_mem (P.mul_mem (P.inv_mem hx'P) hsP) hx'P
    have h2 := (hxn ⟨(x : G)⁻¹ * s * (x : G), hP2⟩).2 (by
      rw [Subgroup.mem_subgroupOf]
      convert hs using 1
      simp [mul_assoc])
    rw [Subgroup.mem_subgroupOf] at h2
    exact h2
  have ht₀ : t ∈ C := (hCmem t).2 rfl
  set t₀ : ↥C := ⟨t, ht₀⟩ with ht₀def
  have ht₀c : t₀ ∈ center ↥C := by
    rw [mem_center_iff]
    intro u
    apply Subtype.ext
    exact (hCmem (u : G)).1 u.2
  have ht₀ord : orderOf t₀ = 2 := by rw [ht₀def, Subgroup.orderOf_mk, ht]
  have ht₀p : IsPGroup 2 (zpowers t₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht₀ord, pow_one])
  have : (zpowers t₀).Normal := normal_of_le_center (zpowers_le.2 ht₀c)
  have ht₀T : t₀ ∈ (T : Subgroup ↥C) := ht₀p.le_sylow_of_normal T (mem_zpowers t₀)
  have htT₀ : t ∈ (T : Subgroup ↥C).map C.subtype := ⟨t₀, ht₀T, rfl⟩
  have hcomm_t : ∀ s ∈ (T : Subgroup ↥C).map C.subtype, s * t = t * s := by
    rintro s ⟨u, -, rfl⟩
    exact (hCmem (u : G)).1 u.2
  have ht'T₀ : (x : G) * t * (x : G)⁻¹ ∈ (T : Subgroup ↥C).map C.subtype :=
    (hxnorm t htT₀).1
  have ht'c : ∀ s ∈ (T : Subgroup ↥C).map C.subtype,
      s * ((x : G) * t * (x : G)⁻¹) = ((x : G) * t * (x : G)⁻¹) * s := by
    intro s hs
    have h2 := hcomm_t _ (hxnorm s hs).2
    calc s * ((x : G) * t * (x : G)⁻¹)
        = (x : G) * (((x : G)⁻¹ * s * (x : G)) * t) * (x : G)⁻¹ := by group
      _ = (x : G) * (t * ((x : G)⁻¹ * s * (x : G))) * (x : G)⁻¹ := by rw [h2]
      _ = ((x : G) * t * (x : G)⁻¹) * s := by group
  have ht'2 : ((x : G) * t * (x : G)⁻¹) * ((x : G) * t * (x : G)⁻¹) = 1 := by
    calc ((x : G) * t * (x : G)⁻¹) * ((x : G) * t * (x : G)⁻¹)
        = (x : G) * (t * t) * (x : G)⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨τ, hτT, hτ⟩ := ht'T₀
  have hτ' : (τ : G) = (x : G) * t * (x : G)⁻¹ := hτ
  set π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set S : Sylow 2 (↥C ⧸ pPrimeCore 2 ↥C) := T.mapSurjective hπs with hS
  have hSmem : ∀ s ∈ (S : Subgroup (↥C ⧸ pPrimeCore 2 ↥C)), ∃ σ ∈ (T : Subgroup ↥C), π σ = s :=
    fun s hs => hs
  have hττ : τ * τ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hτ', Subgroup.coe_one]
    exact ht'2
  have ht₀t₀ : t₀ * t₀ = 1 := Subtype.ext ht2
  have hwc : π τ ∈ center (↥C ⧸ pPrimeCore 2 ↥C) := by
    refine mem_center_of_mem_center_sylow hn hcov S (fun s hs => ?_)
      (by rw [← map_mul, hττ, map_one])
    obtain ⟨σ, hσ, rfl⟩ := hSmem s hs
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hτ']
    exact ht'c σ ⟨σ, hσ, rfl⟩
  have hw₀c : π t₀ ∈ center (↥C ⧸ pPrimeCore 2 ↥C) := by
    refine mem_center_of_mem_center_sylow hn hcov S (fun s hs => ?_)
      (by rw [← map_mul, ht₀t₀, map_one])
    obtain ⟨σ, hσ, rfl⟩ := hSmem s hs
    rw [← map_mul, ← map_mul, mem_center_iff.1 ht₀c σ]
  have hτ1 : π τ ≠ 1 := by
    intro h
    have := eq_one_of_mul_self_eq_one_of_mem_odd hNodd ((QuotientGroup.eq_one_iff τ).1 h) hττ
    apply ht1
    have h2 : (τ : G) = 1 := by rw [this]; rfl
    rw [hτ'] at h2
    have h3 := congrArg (fun y => (x : G)⁻¹ * y * (x : G)) h2
    simpa [mul_assoc] using h3
  have hw₀1 : π t₀ ≠ 1 := by
    intro h
    have := eq_one_of_mul_self_eq_one_of_mem_odd hNodd ((QuotientGroup.eq_one_iff t₀).1 h) ht₀t₀
    apply ht1
    have h2 : (t₀ : G) = 1 := by rw [this]; rfl
    exact h2
  have hceq : π τ = π t₀ := by
    have hcard := hcov.2.1
    rw [Nat.card_eq_two_iff' (1 : ↥(center (↥C ⧸ pPrimeCore 2 ↥C)))] at hcard
    obtain ⟨y, -, hy⟩ := hcard
    have e1 := hy ⟨π τ, hwc⟩ (fun h => hτ1 (congrArg Subtype.val h))
    have e2 := hy ⟨π t₀, hw₀c⟩ (fun h => hw₀1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hτt : τ = t₀ := by
    have hmem : τ⁻¹ * t₀ ∈ pPrimeCore 2 ↥C := (QuotientGroup.eq).1 hceq
    have hsq : (τ⁻¹ * t₀) * (τ⁻¹ * t₀) = 1 := by
      have hc := mem_center_iff.1 ht₀c τ⁻¹
      calc (τ⁻¹ * t₀) * (τ⁻¹ * t₀) = τ⁻¹ * (t₀ * τ⁻¹) * t₀ := by group
        _ = τ⁻¹ * (τ⁻¹ * t₀) * t₀ := by rw [← hc]
        _ = (τ * τ)⁻¹ * (t₀ * t₀) := by group
        _ = 1 := by rw [hττ, ht₀t₀]; group
    have := eq_one_of_mul_self_eq_one_of_mem_odd hNodd hmem hsq
    exact inv_mul_eq_one.1 this
  have hxt : (x : G) * t = t * (x : G) := by
    have h1 : (τ : G) = t := by rw [hτt]
    rw [hτ'] at h1
    calc (x : G) * t = ((x : G) * t * (x : G)⁻¹) * (x : G) := by group
      _ = t * (x : G) := by rw [h1]
  have hxC : (x : G) ∈ C := (hCmem _).2 hxt
  set x'' : ↥C := ⟨(x : G), hxC⟩ with hx''
  set Q : Subgroup ↥C := (T : Subgroup ↥C) ⊔ zpowers x'' with hQ
  have hQmap : Q.map C.subtype = (T : Subgroup ↥C).map C.subtype ⊔ zpowers (x : G) := by
    rw [hQ, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  have hQle : Q.map C.subtype ≤ (P : Subgroup G) := by
    rw [hQmap]
    exact sup_le hTP (zpowers_le.2 hx'P)
  have hQp : IsPGroup 2 Q := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 (P.isPGroup'.to_le hQle))
    exact IsPGroup.of_card (n := k) (by
      rw [← hk]
      exact (Subgroup.card_map_of_injective C.subtype_injective).symm)
  have hmax : Q = (T : Subgroup ↥C) := T.is_maximal' hQp le_sup_left
  have hx''T : x'' ∈ (T : Subgroup ↥C) := hmax ▸ mem_sup_right (mem_zpowers x'')
  exact hx'T ⟨x'', hx''T, rfl⟩

theorem exists_sylow_eq_map_of_centralizer_cover {G : Type} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) {n : ℕ} (hn : 8 ≤ n)
    (hcov : IsDoubleCoverOfAlt
      (↥(centralizer ({t} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({t} : Set G))) n)
    (T : Sylow 2 ↥(centralizer ({t} : Set G))) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = (T : Subgroup ↥(centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype :=
  exists_sylow_eq_map_core (centralizer ({t} : Set G)) (fun _ => mem_centralizer_singleton_iff)
    ht hn hcov T

theorem hasSylowTwoTypeAhat_of_centralizer_cover {G : Type} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) {n : ℕ} (hn : 8 ≤ n)
    (hcov : IsDoubleCoverOfAlt
      (↥(centralizer ({t} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({t} : Set G))) n) :
    HasSylowTwoTypeAhat G n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(centralizer ({t} : Set G))) := Sylow.nonempty
  obtain ⟨P, hP⟩ := exists_sylow_eq_map_of_centralizer_cover ht hn hcov T
  have hπs := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(centralizer ({t} : Set G)))
  refine ⟨_, inferInstance, hcov, P, T.mapSurjective hπs, ⟨?_⟩⟩
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer ({t} : Set G)))) := by
    have hc : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(centralizer ({t} : Set G)))) :=
      pPrimeCore_coprime_card
    exact Nat.coprime_two_left.mp hc
  let f : ↥(T : Subgroup ↥(centralizer ({t} : Set G))) →*
      ↥(centralizer ({t} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({t} : Set G)) :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({t} : Set G)))).comp
      (T : Subgroup ↥(centralizer ({t} : Set G))).subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : (a : ↥(centralizer ({t} : Set G))) ∈ pPrimeCore 2 ↥(centralizer ({t} : Set G)) :=
      (QuotientGroup.eq_one_iff _).1 ha
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 T.isPGroup') a
    have h1 : orderOf a ∣ Nat.card (pPrimeCore 2 ↥(centralizer ({t} : Set G))) := by
      rw [← Subgroup.orderOf_coe a]
      exact Subgroup.orderOf_dvd_natCard _ hmem
    rw [hk] at h1
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
      exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 (h2.trans h1))
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  have hrange : f.range = (T : Subgroup ↥(centralizer ({t} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({t} : Set G)))) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact (MulEquiv.subgroupCongr hP).trans
    ((Subgroup.equivMapOfInjective _ (centralizer ({t} : Set G)).subtype
      (centralizer ({t} : Set G)).subtype_injective).symm.trans
      ((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)))

end CFSG.OddStandard.Solomon75
