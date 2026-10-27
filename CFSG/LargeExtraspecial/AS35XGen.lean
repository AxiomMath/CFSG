module

public import CFSG.LargeExtraspecial.S12Fischer
public import CFSG.Timmesfeld.Outcome
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.LargeExtraspecial.AS35X

open Subgroup

section Center

variable {L : Type*} [Group L]

theorem mk'_eq_one_iff {x : L} : QuotientGroup.mk' (center L) x = 1 ↔ x ∈ center L := by
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']

theorem eq_one_of_mem_center_of_conj (hZ : ∀ c ∈ center L, c * c = 1 → c = 1) {c x : L}
    (hc : c ∈ center L) (h : x * c * x⁻¹ = c⁻¹) : c = 1 := by
  have hxc : x * c = c * x := mem_center_iff.mp hc x
  have h1 : c = c⁻¹ := by
    calc c = x * c * x⁻¹ := by rw [hxc, mul_inv_cancel_right]
      _ = c⁻¹ := h
  refine hZ c hc ?_
  calc c * c = c * c⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel c

theorem eq_of_mul_mem_center (hZ : ∀ c ∈ center L, c * c = 1 → c = 1) {u y : L}
    (hu : u * u = 1) (hy : y * y = 1) (hc : u * y ∈ center L) : u = y := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : u * y = 1 := by
    refine eq_one_of_mem_center_of_conj hZ hc (x := y) ?_
    calc y * (u * y) * y⁻¹ = y * u := by group
      _ = (u * y)⁻¹ := by rw [mul_inv_rev, hui, hyi]
  calc u = u * y * y⁻¹ := by group
    _ = y := by rw [h1, one_mul, hyi]

theorem eq_one_of_mem_center_of_pow (hZ : ∀ c ∈ center L, c * c = 1 → c = 1) {c : L}
    (hc : c ∈ center L) : ∀ k : ℕ, c ^ 2 ^ k = 1 → c = 1
  | 0, hk => by simpa using hk
  | k + 1, hk => eq_one_of_mem_center_of_pow hZ hc k (hZ _ (pow_mem hc _)
      (by rw [← pow_two, ← pow_mul, ← pow_succ]; exact hk))

theorem eq_of_mk_eq (hZ : ∀ c ∈ center L, c * c = 1 → c = 1) {d e : L} (hd : d * d = 1)
    (he : e * e = 1) (h : QuotientGroup.mk' (center L) d = QuotientGroup.mk' (center L) e) :
    d = e := by
  refine eq_of_mul_mem_center hZ hd he (mk'_eq_one_iff.mp ?_)
  rw [map_mul, h, ← map_mul, he, map_one]

theorem commute_of_mk (hZ : ∀ c ∈ center L, c * c = 1 → c = 1) {x y : L} (hy : y * y = 1)
    (h : QuotientGroup.mk' (center L) x * QuotientGroup.mk' (center L) y =
      QuotientGroup.mk' (center L) y * QuotientGroup.mk' (center L) x) : x * y = y * x := by
  have hu : x * y * x⁻¹ * (x * y * x⁻¹) = 1 := by
    calc x * y * x⁻¹ * (x * y * x⁻¹) = x * (y * y) * x⁻¹ := by group
      _ = 1 := by rw [hy, mul_one, mul_inv_cancel]
  have h1 : QuotientGroup.mk' (center L) (x * y * x⁻¹ * y) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, h, mul_inv_cancel_right, ← map_mul, hy, map_one]
  have h2 := eq_of_mul_mem_center hZ hu hy (mk'_eq_one_iff.mp h1)
  calc x * y = x * y * x⁻¹ * x := by group
    _ = y * x := by rw [h2]

theorem orderOf_mk_mul (hZ : ∀ c ∈ center L, c * c = 1 → c = 1) {d e : L} (hd : d * d = 1)
    (he : e * e = 1) :
    orderOf (QuotientGroup.mk' (center L) d * QuotientGroup.mk' (center L) e) =
      orderOf (d * e) := by
  rw [← map_mul]
  refine Nat.dvd_antisymm (orderOf_map_dvd _ _) (orderOf_dvd_of_pow_eq_one ?_)
  have hk : (d * e) ^ orderOf (QuotientGroup.mk' (center L) (d * e)) ∈ center L := by
    rw [← mk'_eq_one_iff, map_pow, pow_orderOf_eq_one]
  refine eq_one_of_mem_center_of_conj hZ hk (x := d) ?_
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have h1 : d * (d * e) * d⁻¹ = (d * e)⁻¹ := by
    rw [mul_inv_rev, hdi, hei]
    calc d * (d * e) * d = (d * d) * (e * d) := by group
      _ = e * d := by rw [hd, one_mul]
  rw [← conj_pow, h1, inv_pow]

theorem eq_bot_of_nilpotent (hF : CFSG.fittingSubgroup L ≤ center L)
    (N : Subgroup (L ⧸ center L)) (hN : N.Normal) (hnil : Group.IsNilpotent N) : N = ⊥ := by
  have hRn : (N.comap (QuotientGroup.mk' (center L))).Normal := hN.comap _
  have hRnil : Group.IsNilpotent (N.comap (QuotientGroup.mk' (center L))) := by
    refine Subgroup.isNilpotent_of_ker_le_center
      ((QuotientGroup.mk' (center L)).subgroupComap N) ?_
    intro x hx
    have hx1 : QuotientGroup.mk' (center L) (x : L) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxc := mk'_eq_one_iff.mp hx1
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp hxc y)
  have hRZ : N.comap (QuotientGroup.mk' (center L)) ≤ center L :=
    (le_sSup ⟨hRn, hRnil⟩ : N.comap (QuotientGroup.mk' (center L)) ≤
      CFSG.fittingSubgroup L).trans hF
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) y
  rw [mem_bot]
  exact mk'_eq_one_iff.mpr (hRZ hy)

theorem center_trivial_top (hF : CFSG.fittingSubgroup L ≤ center L) :
    ∀ y ∈ (⊤ : Subgroup (L ⧸ center L)),
      (∀ x ∈ (⊤ : Subgroup (L ⧸ center L)), x * y = y * x) → y = 1 := by
  intro y _ h
  have hy : y ∈ center (L ⧸ center L) := mem_center_iff.mpr fun g => h g (mem_top g)
  rw [eq_bot_of_nilpotent hF (center (L ⧸ center L)) inferInstance inferInstance, mem_bot] at hy
  exact hy

variable [Finite L] in
theorem pGroup_eq_bot_top (hF : CFSG.fittingSubgroup L ≤ center L) {p : ℕ} [Fact p.Prime] :
    ∀ P : Subgroup (L ⧸ center L), P ≤ ⊤ → IsPGroup p P →
      (⊤ : Subgroup (L ⧸ center L)) ≤ normalizer (P : Set (L ⧸ center L)) → P = ⊥ := by
  intro P _ hP hN
  exact eq_bot_of_nilpotent hF P (normalizer_eq_top_iff.mp (top_le_iff.mp hN)) hP.isNilpotent

variable [Finite L] in
theorem noNormalTwo_top (hF : CFSG.fittingSubgroup L ≤ center L) :
    S12NoNormalTwo (⊤ : Subgroup (L ⧸ center L)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  pGroup_eq_bot_top hF

theorem transpositionData (hZ : ∀ c ∈ center L, c * c = 1 → c = 1) {D : Set L} {d : L}
    (hgen : closure D = ⊤) (hd : d ∈ D) (hcls : ∀ e ∈ D, ∃ x : L, x * d * x⁻¹ = e)
    (hconj : ∀ x : L, ∀ e ∈ D, x * e * x⁻¹ ∈ D) (hinv : ∀ e ∈ D, e * e = 1)
    (hne : ∀ e ∈ D, e ≠ 1) (hord : ∀ a ∈ D, ∀ b ∈ D, orderOf (a * b) ≤ 4)
    (hsq : ∀ a ∈ D, ∀ b ∈ D, orderOf (a * b) = 4 → (a * b) ^ 2 ∈ D) :
    S12TranspositionData (⊤ : Subgroup (L ⧸ center L)) (QuotientGroup.mk' (center L) '' D)
      (QuotientGroup.mk' (center L) d) where
  subset := fun _ _ => mem_top _
  gen := by
    refine (eq_top_iff.mpr fun y _ => ?_).symm
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) y
    have hx : x ∈ closure D := hgen ▸ mem_top x
    have := mem_map_of_mem (QuotientGroup.mk' (center L)) hx
    rwa [MonoidHom.map_closure] at this
  mem := ⟨d, hd, rfl⟩
  cls := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨x, hxe⟩ := hcls e he
    exact ⟨QuotientGroup.mk' (center L) x, mem_top _, by rw [← hxe, map_mul, map_mul, map_inv]⟩
  conj := by
    rintro y - _ ⟨e, he, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) y
    exact ⟨x * e * x⁻¹, hconj x e he, by rw [map_mul, map_mul, map_inv]⟩
  invol := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, hinv e he, map_one]
  ne_one := by
    rintro _ ⟨e, he, rfl⟩ h
    exact hne e he (hZ e (mk'_eq_one_iff.mp h) (hinv e he))
  ord := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [orderOf_mk_mul hZ (hinv a ha) (hinv b hb)]
    exact hord a ha b hb
  sq := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h4
    rw [orderOf_mk_mul hZ (hinv a ha) (hinv b hb)] at h4
    exact ⟨(a * b) ^ 2, hsq a ha b hb h4, by rw [map_pow, map_mul]⟩

end Center

theorem exists_prime_five_le_of_not_isSolvable {H : Type*} [Group H] [Finite H]
    (h : ¬ Group.IsSolvable H) : ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ Nat.card H := by
  classical
  by_contra hc
  push Not at hc
  apply h
  let := Fintype.ofFinite H
  have hsupp : (Nat.card H).factorization.support ⊆ {2, 3} := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have h2 := hpp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hpp
    by_contra hne
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
    exact hc p hpp (by omega) hdvd
  have hcard : Nat.card H =
      2 ^ (Nat.card H).factorization 2 * 3 ^ (Nat.card H).factorization 3 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self Nat.card_pos.ne']
    rw [Finsupp.prod_of_support_subset _ hsupp _ fun _ _ => pow_zero _]
    simp
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hcard)

theorem mem_normalizer_of_conj_mem {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y} {g : Y}
    (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : g ∈ normalizer (K : Set Y) := by
  let f : K → K := fun k => ⟨g * k * g⁻¹, h k k.2⟩
  have hf : Function.Injective f := fun p q hpq => by
    have h1 : g * (p : Y) * g⁻¹ = g * q * g⁻¹ := congrArg Subtype.val hpq
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hs := Finite.injective_iff_surjective.mp hf
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => h k hk, fun hk => ?_⟩
  obtain ⟨q, hq⟩ := hs ⟨_, hk⟩
  have : g * q * g⁻¹ = g * k * g⁻¹ := congrArg Subtype.val hq
  have hqk : (q : Y) = k := by simpa using this
  rw [← hqk]
  exact q.2

theorem outcome_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : CFSG.Timmesfeld.Outcome G) : CFSG.Timmesfeld.Outcome G' := by
  open CFSG.LieType.CurtisTits in
  rcases h with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ | ⟨f, hf, h⟩ |
      ⟨f, hf, t, ht, h⟩ | h | h | h
  · exact Or.inl ⟨n, f, hn, hf, lieModel_of_mulEquiv e h⟩
  · exact Or.inr (Or.inl ⟨n, f, hn, hf, lieModel_of_mulEquiv e h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, f, hn, hf, Or.inl (lieModel_of_mulEquiv e h)⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨n, f, hn, hf, Or.inr (lieModel_of_mulEquiv e h)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, t, ht, lieModel_of_mulEquiv e h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (lieModel_of_mulEquiv e h))))))
  · obtain ⟨e'⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans e'⟩))))))
  · obtain ⟨e'⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (show Nonempty _ from ⟨e.symm.trans e'⟩)))))))

section Fischer

variable {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {D : Set G} {D' : Set G'}
  (hD : ∀ g, g ∈ D ↔ e g ∈ D')
include hD

theorem mem_iff_symm (g : G') : g ∈ D' ↔ e.symm g ∈ D := by
  rw [hD, MulEquiv.apply_symm_apply]

open CFSG.Open in
theorem fischerLinearModel_of_mulEquiv {ι F : Type*} [Fintype ι] [DecidableEq ι] [CommRing F]
    {H : Subgroup (GL ι F)} {T : Set (GL ι F)} (h : fischerLinearModel D H T) :
    fischerLinearModel D' H T := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨e.symm.trans φ, fun g => by rw [mem_iff_symm e hD, hφ]; rfl⟩

open CFSG.Open in
theorem fischerCentralQuotientModel_of_mulEquiv {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing F] {H : Subgroup (GL ι F)} {T : Set (GL ι F)}
    (h : fischerCentralQuotientModel D H T) : fischerCentralQuotientModel D' H T := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨e.symm.trans φ, fun g => by rw [mem_iff_symm e hD, hφ]; rfl⟩

theorem natCard_set_eq : Nat.card D' = Nat.card D :=
  (Nat.card_congr (e.toEquiv.subtypeEquiv hD)).symm

theorem s12FischerConclusion_of_mulEquiv (h : S12FischerConclusion G D) :
    S12FischerConclusion G' D' := by
  have hc : Nat.card G' = Nat.card G := (Nat.card_congr e.toEquiv).symm
  have hs := natCard_set_eq e hD
  rcases h with ⟨m, hm, φ, hφ⟩ | ⟨m, hm, b, hb1, hb2, h⟩ | ⟨m, hm, Q, hQ1, hQ2, h⟩ |
      ⟨m, hm, h⟩ | ⟨m, hm, f, hf1, hf2, h⟩ | h | h | h
  · exact Or.inl ⟨m, hm, e.symm.trans φ, fun g => by rw [mem_iff_symm e hD, hφ]; rfl⟩
  · exact Or.inr (Or.inl ⟨m, hm, b, hb1, hb2, fischerLinearModel_of_mulEquiv e hD h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m, hm, Q, hQ1, hQ2, fischerLinearModel_of_mulEquiv e hD h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, hm, fischerCentralQuotientModel_of_mulEquiv e hD h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, hm, f, hf1, hf2, fischerCentralQuotientModel_of_mulEquiv e hD h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hc, hs]; exact h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hc, hs]; exact h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [hc, hs]; exact h)))))))

end Fischer

end CFSG.LargeExtraspecial.AS35X
