module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightTransport

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ProperTwoGeneratedCore.TheoremC

theorem injective_of_map_ne_one {T Y : Type*} [Group T] [Group Y] (hT : IsPGroup 2 T) {u : T}
    (hu : ∀ c : T, orderOf c = 2 → c = u) (χ : T →* Y) (hχ : χ u ≠ 1) :
    Function.Injective χ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  rw [MonoidHom.mem_ker] at hc
  rw [Subgroup.mem_bot]
  by_contra hc1
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hT c
  obtain _ | n := n
  · rw [pow_zero, orderOf_eq_one_iff] at hn
    exact hc1 hn
  have h2 : orderOf (c ^ 2 ^ n) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hn]; exact pow_dvd_pow 2 (by omega)), hn,
      pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
  apply hχ
  rw [← hu _ h2, map_pow, hc, one_pow]

theorem commute_of_unique_involution {T : Type*} [Group T] {u : T}
    (hu : ∀ c : T, orderOf c = 2 → c = u) (hu2 : orderOf u = 2) (a : T) : a * u = u * a := by
  have h := hu (a * u * a⁻¹) (by
    simpa only [MulAut.conj_apply] using ((MulAut.conj a).orderOf_eq u).trans hu2)
  calc a * u = a * u * a⁻¹ * a := by group
    _ = u * a := by rw [h]

theorem commute_of_injective_of_sq_eq {T R : Type*} [Group T] [Group R] {u : T}
    (hu : ∀ c : T, orderOf c = 2 → c = u) (hu2 : orderOf u = 2)
    (hR4 : ∀ x : R, x ^ 4 = 1) (hR : ∀ x y : R, x ^ 2 = y ^ 2 → x ^ 2 ≠ 1 → x * y = y * x)
    (χ : T →* R) (hχ : Function.Injective χ) (hχu : χ u ≠ 1) (a b : T) : a * b = b * a := by
  have hsq : ∀ c : T, c ^ 2 = 1 ∨ c ^ 2 = u := by
    intro c
    have h4 : c ^ 4 = 1 := hχ (by rw [map_pow, hR4, map_one])
    by_cases h1 : c ^ 2 = 1
    · exact Or.inl h1
    · exact Or.inr (hu _ (orderOf_eq_prime (by rw [← pow_mul]; exact h4) h1))
  have hcent : ∀ c : T, c ^ 2 = 1 → ∀ d : T, c * d = d * c := by
    intro c hc d
    by_cases hc1 : c = 1
    · rw [hc1, one_mul, mul_one]
    · rw [hu c (orderOf_eq_prime hc hc1)]
      exact (commute_of_unique_involution hu hu2 d).symm
  rcases hsq a with ha | ha
  · exact hcent a ha b
  rcases hsq b with hb | hb
  · exact (hcent b hb a).symm
  have hχa : χ a ^ 2 = χ u := by rw [← map_pow, ha]
  have hχb : χ b ^ 2 = χ u := by rw [← map_pow, hb]
  apply hχ
  rw [map_mul, map_mul]
  exact hR _ _ (hχa.trans hχb.symm) (hχa ▸ hχu)

theorem index_le_two_of_card_le {X : Type*} [Group X] [Finite X] {A B : Subgroup X}
    (hA : A.index ≤ 2) (hAB : Nat.card A ≤ Nat.card B) : B.index ≤ 2 := by
  have h1 := A.index_mul_card
  have h2 := B.index_mul_card
  have hB : 0 < Nat.card B := Nat.card_pos
  have h3 : B.index * Nat.card B ≤ 2 * Nat.card B := by
    rw [h2, ← h1]
    exact Nat.mul_le_mul hA hAB
  exact Nat.le_of_mul_le_mul_right h3 hB

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)} [J.Normal]

namespace SzEightSetting

variable (hs : SzEightSetting S H z J)
include hs

theorem false_of_szModel_of_normal
    (e : (J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) : False := by
  have hz := hs.central
  obtain ⟨φ, hφ⟩ := hs.exists_isInnerPart e
  have hR := hs.sylowFacts e
  obtain ⟨t, htJ, htc, htZ, -, htz⟩ := hs.exists_conj_mem_inCenterOf e hφ
  obtain ⟨g, hgt, hgS⟩ := centralInvolution_exists_transport hz htz
  set zS : (S : Subgroup G) := ⟨z, hz.1⟩ with hzS
  have hzc : ∀ a : (S : Subgroup G), a * zS = zS * a := fun a => Subtype.ext (hz.2.2 a a.2)
  have hzz : z * z = 1 := by
    rw [← pow_two]
    have h2 := pow_orderOf_eq_one z
    rwa [hz.2.1] at h2
  have hz1 : z ≠ 1 := fun h => by
    have h2 := hz.2.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  let τ : Subgroup.centralizer ({t} : Set (S : Subgroup G)) →* (S : Subgroup G) :=
    { toFun := fun x => ⟨g⁻¹ * ((x : (S : Subgroup G)) : G) * g, hgS _ (x : (S : Subgroup G)).2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  have hτ : ∀ x, ((τ x : (S : Subgroup G)) : G) = g⁻¹ * ((x : (S : Subgroup G)) : G) * g :=
    fun x => rfl
  have hτinj : Function.Injective τ := fun x y h => Subtype.ext (Subtype.ext (by
    have h1 := congrArg Subtype.val h
    rw [hτ, hτ] at h1
    simpa using h1))
  have hzt : zS ∈ Subgroup.centralizer ({t} : Set (S : Subgroup G)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc t).symm
  set s := τ ⟨zS, hzt⟩ with hsdef
  have hss : s * s = 1 := by
    rw [← map_mul, show (⟨zS, hzt⟩ * ⟨zS, hzt⟩ : Subgroup.centralizer ({t} : Set _)) = 1 from
      Subtype.ext (Subtype.ext hzz), map_one]
  have hs1 : s ≠ 1 := fun h => hz1 (by
    have h1 : g⁻¹ * z * g = 1 := congrArg Subtype.val h
    rw [show z = g * (g⁻¹ * z * g) * g⁻¹ by group, h1]
    group)
  have hsz : s ≠ zS := fun h => htZ (by
    have h1 : g⁻¹ * z * g = z := congrArg Subtype.val h
    have ht : (t : G) = z := by
      calc (t : G) = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = g * z * g⁻¹ := by rw [hgt]
        _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h1]
        _ = z := by group
    rw [hs.mem_center_iff]
    right
    change sylowBar hz t = escapingBar z
    rw [← sylowBar_self hz]
    congr 1
    exact Subtype.ext ht)
  obtain ⟨hsJ, -⟩ := hs.inCenterOf_of_mul_self e hφ hss
  have hφs : φ s ≠ 1 := by
    rw [hφ.eq_mk s hsJ, Ne, QuotientGroup.eq_one_iff, hs.mem_center_iff]
    rintro (h | h)
    · exact hs1 (sylowBar_injective hz (by rw [map_one]; exact h))
    · exact hsz (sylowBar_injective hz (by rw [sylowBar_self]; exact h))
  set T : Subgroup (S : Subgroup G) :=
    (Subgroup.centralizer (J : Set (EscapingQuotient z))).comap (sylowBar hz) with hTdef
  have hbarC : escapingBar z ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
    Subgroup.mem_centralizer_iff.mpr fun g _ => (hs.quotientData.commute_bar g).eq
  have hTt : T ≤ Subgroup.centralizer ({t} : Set (S : Subgroup G)) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply sylowBar_injective hz
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp hc _ htJ).symm
  have huT : zS ∈ T := by
    show sylowBar hz zS ∈ Subgroup.centralizer (J : Set (EscapingQuotient z))
    rw [sylowBar_self]
    exact hbarC
  set u : T := ⟨zS, huT⟩ with hudef
  have hu2 : orderOf u = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hz.2.1
  have hu : ∀ c : T, orderOf c = 2 → c = u := by
    intro c hc
    have h2 : orderOf (sylowBar hz c) = 2 := by
      rw [orderOf_injective _ (sylowBar_injective hz), Subgroup.orderOf_coe, hc]
    apply Subtype.ext
    apply sylowBar_injective hz
    rw [hudef, sylowBar_self]
    exact hs.eq_bar_of_mem_centralizer c.2 h2
  have hT2 : IsPGroup 2 T := S.isPGroup'.to_subgroup T
  let χ : T →* (sylowStar hz J : Subgroup (J ⧸ Subgroup.center J)) :=
    (φ.comp (τ.comp (Subgroup.inclusion hTt))).codRestrict _ fun c => hφ.mem_sylow _
  have hχu : χ u ≠ 1 := fun h => hφs (congrArg Subtype.val h)
  have hχ := injective_of_map_ne_one hT2 hu χ hχu
  have hTab := commute_of_injective_of_sq_eq hu hu2 hR.pow_four hR.comm_of_sq_eq χ hχ hχu
  obtain ⟨k', hkS, hkC, hk2⟩ := hs.exists_root
  rw [← sylowBar_range hz] at hkS
  obtain ⟨k, rfl⟩ := hkS
  have hkT : k ∈ T := hkC
  have hkk : k * k = zS := by
    apply sylowBar_injective hz
    rw [map_mul, sylowBar_self, ← pow_two, hk2]
  have hkc : ∀ a : (S : Subgroup G), a * k = k * a := by
    intro a
    obtain ⟨q, hqJ, -, hqa⟩ := hφ.exists_mul a
    have hqk : q * k = k * q := by
      apply sylowBar_injective hz
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hkC _ hqJ
    have h1 := congrArg Subtype.val (hTab ⟨q⁻¹ * a, hqa⟩ ⟨k, hkT⟩)
    change q⁻¹ * a * k = k * (q⁻¹ * a) at h1
    calc a * k = q * (q⁻¹ * a * k) := by group
      _ = q * k * (q⁻¹ * a) := by rw [h1]; group
      _ = k * a := by rw [hqk]; group
  have hkt : k ∈ Subgroup.centralizer ({t} : Set (S : Subgroup G)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hkc t).symm
  set y := τ ⟨k, hkt⟩ with hydef
  have hyy : y * y = s := by
    rw [← map_mul]
    exact congrArg τ (Subtype.ext hkk)
  have hidx : (Subgroup.centralizer ({y} : Set (S : Subgroup G))).index ≤ 2 := by
    refine index_le_two_of_card_le (hs.index_centralizer_le_two hφ htJ htc) ?_
    refine Nat.card_le_card_of_injective
      (fun x => (⟨τ x, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩ :
        Subgroup.centralizer ({y} : Set (S : Subgroup G)))) fun x x' h => hτinj (by
          simpa using congrArg Subtype.val h)
    rw [hydef, ← map_mul, ← map_mul]
    exact congrArg τ (Subtype.ext (hkc (x : (S : Subgroup G))))
  have hφy : φ y ^ 2 ≠ 1 := by
    rw [← map_pow, pow_two, hyy]
    exact hφs
  obtain ⟨r₁, r₂, h₁, h₂, h₃⟩ := hR.exists_noncomm ⟨φ y, hφ.mem_sylow y⟩
    (fun h => hφy (congrArg Subtype.val h))
  obtain ⟨q₁, -, hq₁, -⟩ := hφ.exists_eq r₁.2
  obtain ⟨q₂, -, hq₂, -⟩ := hφ.exists_eq r₂.2
  have hcomm : ∀ (q : (S : Subgroup G)) (r : (sylowStar hz J : Subgroup (J ⧸ _))), φ q = r →
      q ∈ Subgroup.centralizer ({y} : Set (S : Subgroup G)) →
      (⟨φ y, hφ.mem_sylow y⟩ : (sylowStar hz J : Subgroup (J ⧸ _))) * r =
        r * ⟨φ y, hφ.mem_sylow y⟩ := by
    intro q r hqr hq
    apply Subtype.ext
    have h := congrArg φ (Subgroup.mem_centralizer_singleton_iff.mp hq)
    rw [map_mul, map_mul, hqr] at h
    exact h.symm
  rcases mem_or_mem_or_mul_mem_of_index_le_two hidx Subgroup.index_ne_zero_of_finite q₁ q₂ with
    h | h | h
  · exact h₁ (hcomm q₁ r₁ hq₁ h)
  · exact h₂ (hcomm q₂ r₂ hq₂ h)
  · exact h₃ (hcomm (q₁ * q₂) (r₁ * r₂) (by rw [map_mul, hq₁, hq₂]; rfl) h)

end SzEightSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
