module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3TA
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3TD
import CFSG.ClassicalInvolution.Q3.TL4Q8HomEng

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic QuaternionGroup
open scoped commutatorElement

theorem q8_hom_eq_one_of_aut3 {A : Type*} [CommGroup A] (f : QuaternionGroup 2 →* A)
    {φ : MulAut (QuaternionGroup 2)} (h3 : φ ^ 3 = 1) (h1 : φ ≠ 1)
    (hf : ∀ y, f (φ y) = f y) (y : QuaternionGroup 2) : f y = 1 :=
  CFSG.ClassicalInvolution.Q3.TL4.E3.q8_hom_eq_one_of_aut3_gen f h3 h1 hf y

theorem q8_sq_eq_one : ∀ y : QuaternionGroup 2, y ^ 2 = 1 → y = 1 ∨ y = a 2 := by decide

theorem q8_conj_eq_inv : ∀ q q' : QuaternionGroup 2, q ^ 2 ≠ 1 → q' ≠ q → q' ≠ q⁻¹ →
    q' ^ 2 ≠ 1 → q' * q * q'⁻¹ = q⁻¹ := by decide

theorem q8_index_zpowers {y : QuaternionGroup 2} (hy : y ^ 2 ≠ 1) :
    (Subgroup.zpowers y).index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy4 : y ^ 2 ^ (1 + 1) = 1 := by
    have h : ∀ x : QuaternionGroup 2, x ^ 4 = 1 := by decide
    exact h y
  have hord : orderOf y = 2 ^ (1 + 1) := orderOf_eq_prime_pow (by simpa using hy) hy4
  have h1 := (Subgroup.zpowers y).card_mul_index
  rw [Nat.card_zpowers, hord, Nat.card_eq_fintype_card, QuaternionGroup.card] at h1
  omega

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem tightCore_sup_commutator (hgen : TightSelfGen R) : tightCore R ⊔ commutator Y = ⊤ := by
  have hn : (tightCore R ⊔ commutator Y).Normal :=
    Subgroup.Normal.of_commutator_le _ le_sup_right
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun g x hx => ?_
  rw [mem_conjSub_iff] at hx
  have h1 := hn.conj_mem _ (Subgroup.mem_sup_left hx) g
  simpa [mul_assoc] using h1

theorem abel_pow_eq_one (hgen : TightSelfGen R) (y : Y) :
    Abelianization.of y ^ 2 ^ Nat.card Y = 1 := by
  set T : Subgroup Y :=
    (powMonoidHom (2 ^ Nat.card Y) : Abelianization Y →* Abelianization Y).ker.comap
      Abelianization.of with hT
  have hK : tightCore R ≤ T := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨-, hx2⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := hx2.exists_card_eq
    rw [Nat.card_zpowers] at hm
    have hmle : m ≤ Nat.card Y := by
      have h1 : orderOf x ≤ Nat.card Y := Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard x)
      have h2 : m < 2 ^ m := Nat.lt_two_pow_self
      omega
    have hx : x ^ 2 ^ Nat.card Y = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hm]
      exact pow_dvd_pow 2 hmle
    show (powMonoidHom (2 ^ Nat.card Y)) (Abelianization.of x) = 1
    rw [powMonoidHom_apply, ← map_pow, hx, map_one]
  have hC : commutator Y ≤ T := by
    intro c hc
    show (powMonoidHom (2 ^ Nat.card Y)) (Abelianization.of c) = 1
    have h1 : Abelianization.of c = 1 := by
      rw [← MonoidHom.mem_ker, Abelianization.ker_of]
      exact hc
    rw [h1, map_one]
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← tightCore_sup_commutator hgen]
    exact sup_le hK hC
  have hy : y ∈ T := hT ▸ Subgroup.mem_top y
  exact hy

theorem abel_eq_one_of_mem_oddCoreImg (hgen : TightSelfGen R) {o : Y}
    (ho : o ∈ oddCoreImg R) : Abelianization.of o = 1 := by
  have hodd : Odd (orderOf o) := by
    have h1 : orderOf (⟨o, ho⟩ : oddCoreImg R) ∣ Nat.card (oddCoreImg R) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact (odd_natCard_oddCoreImg R).of_dvd_nat h1
  have h1 : orderOf (Abelianization.of o) ∣ 2 ^ Nat.card Y :=
    orderOf_dvd_of_pow_eq_one (abel_pow_eq_one hgen o)
  have h2 : orderOf (Abelianization.of o) ∣ orderOf o := orderOf_map_dvd _ o
  have h3 : Nat.Coprime (orderOf o) (2 ^ Nat.card Y) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have h4 : orderOf (Abelianization.of o) ∣ 1 := by
    rw [← h3.gcd_eq_one]
    exact Nat.dvd_gcd h2 h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)

omit [Finite Y] in
theorem abel_exists_mem (hgen : TightSelfGen R) (b : Abelianization Y) :
    ∃ x ∈ R, Abelianization.of x = b := by
  have hsurj : Function.Surjective (Abelianization.of : Y →* Abelianization Y) :=
    QuotientGroup.mk_surjective
  obtain ⟨y, rfl⟩ := hsurj b
  have hy : y ∈ ((tightCore R ⊔ commutator Y : Subgroup Y) : Set Y) := by
    rw [tightCore_sup_commutator hgen]
    trivial
  rw [Subgroup.mul_normal] at hy
  obtain ⟨k, hk, c, hc, rfl⟩ := hy
  refine ⟨k, tightCore_le R hk, ?_⟩
  have h1 : Abelianization.of c = 1 := by
    rw [← MonoidHom.mem_ker, Abelianization.ker_of]
    exact hc
  rw [map_mul, h1, mul_one]

theorem exists_quotEquiv (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) :
    Nonempty ((R ⧸ oddCore R) ≃* QuaternionGroup 2) := by
  obtain ⟨eS⟩ := hq
  have hO : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S hd.quat hd.mem hd.order hd.cent hd.normal hd.twoGroup
  let eS' : ↥((S : Subgroup R).map R.subtype) ≃* QuaternionGroup 2 :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans eS
  exact ⟨(MulEquiv.ofBijective _ hO.bijective_restrict).symm.trans eS'⟩

theorem exists_quatHom (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) :
    ∃ φ : R →* QuaternionGroup 2, ∀ x : R, φ x = 1 ↔ (x : Y) ∈ oddCoreImg R := by
  obtain ⟨eM⟩ := exists_quotEquiv hd hq
  refine ⟨eM.toMonoidHom.comp (QuotientGroup.mk' (oddCore R)), fun x => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_oddCore_iff_coe_mem_oddCoreImg]

theorem index_commutator_le_two (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) (hgen : TightSelfGen R)
    (hsw : TwSwap R t) : (commutator Y).index ≤ 2 := by
  obtain ⟨g, hg, r, hr, hgr⟩ := hsw
  obtain ⟨φ, hφ⟩ := exists_quatHom hd hq
  set ψ : Y →* Abelianization Y := Abelianization.of with hψ
  have hψφ : ∀ a b : R, φ a = φ b → ψ a = ψ b := by
    intro a b hab
    have h1 : φ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 := abel_eq_one_of_mem_oddCoreImg hgen ((hφ _).mp h1)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hgN : g ∈ Subgroup.normalizer (R : Set Y) := hd.le_normalizer hg
  have hcR : ⁅g, r⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN r).mp hr) (R.inv_mem hr)
  set c : R := ⟨⁅g, r⁆, hcR⟩ with hc
  have hψc : ψ (c : Y) = 1 := by
    show ψ ⁅g, r⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hy2 : φ c ^ 2 ≠ 1 := by
    intro h
    apply hgr
    rw [← map_pow, hφ] at h
    simpa [hc] using h
  have hzp : ∀ k : ℤ, ψ ((c ^ k : R) : Y) = 1 := by
    intro k
    rw [Subgroup.coe_zpow, map_zpow, hψc, one_zpow]
  have hmem : ∀ a : R, φ a ∈ Subgroup.zpowers (φ c) → ψ a = 1 := by
    intro a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [hψφ a (c ^ k) (by rw [map_zpow, hk]), hzp]
  have hR : ∀ a b : R, ψ a = 1 ∨ ψ b = 1 ∨ ψ a = ψ b := by
    intro a b
    by_cases ha : φ a ∈ Subgroup.zpowers (φ c)
    · exact Or.inl (hmem a ha)
    by_cases hb : φ b ∈ Subgroup.zpowers (φ c)
    · exact Or.inr (Or.inl (hmem b hb))
    right; right
    have hab : φ (a⁻¹ * b) ∈ Subgroup.zpowers (φ c) := by
      rw [map_mul, map_inv, Subgroup.mul_mem_iff_of_index_two (q8_index_zpowers hy2),
        Subgroup.inv_mem_iff]
      exact iff_of_false ha hb
    have h1 := hmem _ hab
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  rw [Subgroup.index]
  show Nat.card (Abelianization Y) ≤ 2
  refine card_le_two_of_forall fun x y => ?_
  obtain ⟨a, haR, rfl⟩ := abel_exists_mem hgen x
  obtain ⟨b, hbR, rfl⟩ := abel_exists_mem hgen y
  exact hR ⟨a, haR⟩ ⟨b, hbR⟩

theorem commutator_eq_top_of_acts3 (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) (hgen : TightSelfGen R)
    (h3 : TightActs3 R t) : commutator Y = ⊤ := by
  obtain ⟨x, k, hxC, hx3, r₀, hr₀, hxr⟩ := h3
  obtain ⟨eM⟩ := exists_quotEquiv hd hq
  have hxN : x ∈ Subgroup.normalizer (R : Set Y) := hd.le_normalizer hxC
  set θ := tl3Act R ⟨x, hxN⟩ with hθdef
  have hθk : θ ^ 3 ^ k = 1 := by
    have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (R : Set Y)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [hθdef, ← map_pow, h1, map_one]
  have hθ1 : θ ≠ 1 := fun h => hxr ((tl3Act_eq_one_iff R _).mp h r₀ hr₀)
  have hθ3 : θ ^ 3 = 1 := tl3_aut_pow_three_of_pow_three_pow eM hθk
  set ψ : Y →* Abelianization Y := Abelianization.of with hψ
  let ρ : R ⧸ oddCore R →* Abelianization Y :=
    QuotientGroup.lift (oddCore R) (ψ.comp R.subtype) (fun o ho => MonoidHom.mem_ker.mpr
      (abel_eq_one_of_mem_oddCoreImg hgen ((mem_oddCore_iff_coe_mem_oddCoreImg R o).mp ho)))
  have hρθ : ∀ m, ρ (θ m) = ρ m := by
    intro m
    induction m using QuotientGroup.induction_on with
    | H r =>
      rw [hθdef, tl3Act_mk]
      show ψ ((R.normalizerMonoidHom ⟨x, hxN⟩ r : R) : Y) = ψ (r : Y)
      rw [tl3_normalizerMonoidHom_coe, map_mul, map_mul, map_inv, mul_comm (ψ x), mul_assoc,
        mul_inv_cancel, mul_one]
  set θ' : MulAut (QuaternionGroup 2) := MulAut.congr eM θ with hθ'
  have hθ'3 : θ' ^ 3 = 1 := by rw [hθ', ← map_pow, hθ3, map_one]
  have hθ'1 : θ' ≠ 1 := fun h =>
    hθ1 ((MulAut.congr eM).injective (by rw [← hθ', h, map_one]))
  let f : QuaternionGroup 2 →* Abelianization Y := ρ.comp eM.symm.toMonoidHom
  have hf : ∀ y, f (θ' y) = f y := by
    intro y
    simp only [f, hθ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact hρθ _
  have hall := q8_hom_eq_one_of_aut3 f hθ'3 hθ'1 hf
  have hR : ∀ r ∈ R, ψ r = 1 := by
    intro r hr
    have h1 := hall (eM ((⟨r, hr⟩ : R) : R ⧸ oddCore R))
    simp only [f, ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      QuotientGroup.lift_mk, Subgroup.coe_subtype] at h1
    exact h1
  rw [eq_top_iff, ← tightCore_sup_commutator hgen]
  refine sup_le (fun y hy => ?_) le_rfl
  rw [← Abelianization.ker_of]
  exact hR y (tightCore_le R hy)

theorem twSwap_of_sq (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) {c σ g j : Y} (hc2 : c * c = t)
    (hσR : σ ∈ R) (hσc : σ * c * σ⁻¹ = c⁻¹) (hg : g ∈ Subgroup.centralizer ({t} : Set Y))
    (hj : j * σ = σ * j) (hgg : g * g = c * j) :
    TwSwap R t := by
  refine ⟨g, hg, σ, hσR, fun hmem => ?_⟩
  obtain ⟨φ, hφ⟩ := exists_quatHom hd hq
  have hgN : g ∈ Subgroup.normalizer (R : Set Y) := hd.le_normalizer hg
  have hdR : ⁅g, σ⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN σ).mp hσR) (R.inv_mem hσR)
  have htR : t ∈ R := hd.mem_right
  have htO : t ∉ oddCoreImg R := fun ht => by
    have hdvd : orderOf t ∣ Nat.card (oddCoreImg R) := Subgroup.orderOf_dvd_natCard _ ht
    rw [hd.order] at hdvd
    exact (Nat.not_even_iff_odd.mpr (odd_natCard_oddCoreImg R)) (even_iff_two_dvd.mpr hdvd)
  have htt : t * t = 1 := by rw [← pow_two, ← hd.order, pow_orderOf_eq_one]
  have hφt : φ ⟨t, htR⟩ = a 2 := by
    rcases q8_sq_eq_one (φ ⟨t, htR⟩) (by rw [← map_pow, pow_two]; exact (by
      rw [show (⟨t, htR⟩ : R) * ⟨t, htR⟩ = 1 from Subtype.ext htt, map_one])) with h | h
    · exact absurd ((hφ _).mp h) htO
    · exact h
  have hφd : φ ⟨_, hdR⟩ ^ 2 = 1 := by
    rw [← map_pow, hφ]
    simpa using hmem
  obtain ⟨e, he, hde⟩ : ∃ e ∈ oddCoreImg R, ⁅g, σ⁆ = e ∨ ⁅g, σ⁆ = t * e := by
    rcases q8_sq_eq_one _ hφd with h | h
    · exact ⟨_, (hφ _).mp h, Or.inl rfl⟩
    · refine ⟨t⁻¹ * ⁅g, σ⁆, ?_, Or.inr (by group)⟩
      have h1 : φ (⟨t, htR⟩⁻¹ * ⟨_, hdR⟩) = 1 := by
        rw [map_mul, map_inv, hφt, h, inv_mul_cancel]
      simpa using (hφ _).mp h1
  have hgt : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hgt' : g * t * g⁻¹ = t := by rw [hgt, mul_inv_cancel_right]
  have hgeg : g * e * g⁻¹ ∈ oddCoreImg R := conj_mem_oddCoreImg hgN he
  have hte : g * e * g⁻¹ * t = t * (g * e * g⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hd.cent (oddCoreImg_le R hgeg))
  have hsq : ⁅g * g, σ⁆ = g * ⁅g, σ⁆ * g⁻¹ * ⁅g, σ⁆ := by
    simp only [commutatorElement_def]
    group
  have h1 : ⁅g * g, σ⁆ ∈ oddCoreImg R := by
    rw [hsq]
    rcases hde with h | h
    · rw [h]
      exact (oddCoreImg R).mul_mem hgeg he
    · have h2 : g * (t * e) * g⁻¹ * (t * e) = g * e * g⁻¹ * e := by
        calc g * (t * e) * g⁻¹ * (t * e) = (g * t * g⁻¹) * (g * e * g⁻¹) * t * e := by group
          _ = t * (g * e * g⁻¹) * t * e := by rw [hgt']
          _ = g * e * g⁻¹ * (t * t) * e := by rw [← hte]; group
          _ = g * e * g⁻¹ * e := by rw [htt, mul_one]
      rw [h, h2]
      exact (oddCoreImg R).mul_mem hgeg he
  have hσc' : σ * c⁻¹ * σ⁻¹ = c := by
    have h3 := congrArg (·⁻¹) hσc
    simpa [mul_assoc] using h3
  have h2 : ⁅g * g, σ⁆ = t := by
    rw [hgg]
    calc ⁅c * j, σ⁆ = c * (j * σ) * j⁻¹ * c⁻¹ * σ⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = c * (σ * j) * j⁻¹ * c⁻¹ * σ⁻¹ := by rw [hj]
      _ = c * (σ * c⁻¹ * σ⁻¹) := by group
      _ = c * c := by rw [hσc']
      _ = t := hc2
  exact htO (h2 ▸ h1)

omit [Finite Y] in
theorem two_dvd_index_of_not_mem [Finite Y] {N : Subgroup Y} [N.Normal] {x : Y}
    (hx4 : x ^ 4 = 1) (hxN : x ∉ N) : 2 ∣ N.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set xb := QuotientGroup.mk' N x with hxb
  have hxb1 : xb ≠ 1 := fun h => hxN ((QuotientGroup.eq_one_iff x).mp h)
  have hxb4 : xb ^ 2 ^ 2 = 1 := by
    rw [hxb, ← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, hx4, map_one]
  obtain ⟨m, hm, hmo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxb4)
  have h2 : 2 ∣ orderOf xb := by
    rcases m with _ | m
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hmo)) hxb1
    · rw [hmo, pow_succ]
      exact dvd_mul_left 2 _
  rw [Subgroup.index]
  exact h2.trans (orderOf_dvd_natCard xb)

omit [Finite Y] in
theorem exists_q8_mem_of_index_dvd_six [Finite Y] {N : Subgroup Y} [N.Normal]
    (h6 : N.index ∣ 6) (ι : QuaternionGroup 2 →* Y) :
    ∃ q : QuaternionGroup 2, q ^ 2 ≠ 1 ∧ ι q ∈ N := by
  set κ : QuaternionGroup 2 →* Y ⧸ N := (QuotientGroup.mk' N).comp ι with hκ
  have h8 : Nat.card κ.range ∣ 8 := by
    have hQ : Nat.card (QuaternionGroup 2) = 8 := by
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    have := Subgroup.card_range_dvd κ
    rwa [hQ] at this
  have hY : Nat.card κ.range ∣ 6 := by
    have h1 := Subgroup.card_subgroup_dvd_card κ.range
    rw [← Subgroup.index] at h1
    exact h1.trans h6
  have h2 : Nat.card κ.range ≤ 2 := by
    have h1 : Nat.card κ.range ∣ Nat.gcd 8 6 := Nat.dvd_gcd h8 hY
    exact Nat.le_of_dvd (by norm_num) (by simpa using h1)
  have hker : ∀ q, κ q = 1 → ι q ∈ N := fun q h => (QuotientGroup.eq_one_iff _).mp h
  rcases eq_one_or_eq_of_card_le_two h2 ⟨κ (a 1), a 1, rfl⟩ ⟨κ (xa 0), xa 0, rfl⟩ with
    h | h | h
  · exact ⟨a 1, by decide, hker _ (congrArg Subtype.val h)⟩
  · exact ⟨xa 0, by decide, hker _ (congrArg Subtype.val h)⟩
  · refine ⟨(a 1)⁻¹ * xa 0, by decide, hker _ ?_⟩
    have h1 : κ (a 1) = κ (xa 0) := congrArg Subtype.val h
    rw [map_mul, map_inv, h1, inv_mul_cancel]

end CFSG.ClassicalInvolution.Q3.TL4.E3S3T
