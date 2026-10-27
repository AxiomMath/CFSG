module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSQuasi
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHPigeon
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHGL

public section

namespace CFSG.EvenSporadicStandard.M24Std.DResH

open Subgroup CFSG.EvenSporadicStandard.M24Std.DRes Fixed

namespace LevelC

variable {V Y : Type*} [CommGroup V] [Group Y] (ρ : Y →* MulAut V)

@[expose] def kerOn (S : Subgroup Y) (D : Subgroup V) : Subgroup Y where
  carrier := {s | s ∈ S ∧ ∀ v ∈ D, ρ s v = v}
  one_mem' := ⟨S.one_mem, fun v _ => Fixed.rho_one_apply ρ v⟩
  mul_mem' {a b} ha hb := ⟨S.mul_mem ha.1 hb.1, fun v hv => by
    rw [Fixed.rho_mul_apply, hb.2 v hv, ha.2 v hv]⟩
  inv_mem' {a} ha := ⟨S.inv_mem ha.1, fun v hv => by
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha.2 v hv]
      _ = v := Fixed.rho_inv_rho_apply ρ a v⟩

theorem kerOn_le (S : Subgroup Y) (D : Subgroup V) : kerOn ρ S D ≤ S := fun _ h => h.1

theorem kerOn_normalized {S : Subgroup Y} {D : Subgroup V} (hD : ∀ s ∈ S, ∀ v ∈ D, ρ s v ∈ D) :
    ∀ g ∈ S, ∀ n ∈ kerOn ρ S D, g * n * g⁻¹ ∈ kerOn ρ S D := by
  intro g hg n hn
  refine ⟨S.mul_mem (S.mul_mem hg hn.1) (S.inv_mem hg), fun v hv => ?_⟩
  have hv' : ρ g⁻¹ v ∈ D := hD g⁻¹ (S.inv_mem hg) v hv
  rw [Fixed.rho_mul_apply, Fixed.rho_mul_apply, hn.2 _ hv', Fixed.rho_rho_inv_apply]

@[expose] def actAut (S : Subgroup Y) (D : Subgroup V) (hD : ∀ s ∈ S, ∀ v ∈ D, ρ s v ∈ D) :
    S →* MulAut D where
  toFun s :=
    { toFun := fun x => ⟨ρ s x, hD s s.2 x x.2⟩
      invFun := fun x => ⟨ρ s⁻¹ x, hD s⁻¹ (S.inv_mem s.2) x x.2⟩
      left_inv := fun x => Subtype.ext (Fixed.rho_inv_rho_apply ρ s x)
      right_inv := fun x => Subtype.ext (Fixed.rho_rho_inv_apply ρ s x)
      map_mul' := fun x y => Subtype.ext (map_mul (ρ s) (x : V) (y : V)) }
  map_one' := by
    ext x
    exact Fixed.rho_one_apply ρ x
  map_mul' g h := by
    ext x
    exact Fixed.rho_mul_apply ρ g h x

theorem actAut_apply {S : Subgroup Y} {D : Subgroup V} (hD : ∀ s ∈ S, ∀ v ∈ D, ρ s v ∈ D)
    (s : S) (x : D) : ((actAut ρ S D hD s x : D) : V) = ρ s x := rfl

theorem actAut_injective {S : Subgroup Y} {D : Subgroup V} (hD : ∀ s ∈ S, ∀ v ∈ D, ρ s v ∈ D)
    (hfaith : ∀ s ∈ S, (∀ v ∈ D, ρ s v = v) → s = 1) : Function.Injective (actAut ρ S D hD) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  apply Subtype.ext
  refine hfaith s s.2 fun v hv => ?_
  have h2 := congrArg (fun f : MulAut D => (f ⟨v, hv⟩ : V)) hs
  simp only [MulAut.one_apply] at h2
  exact (actAut_apply ρ hD s ⟨v, hv⟩).symm.trans h2

section Quasi

variable {Y' : Type} [Group Y']

theorem cube_eq_one_of_card_three {Z : Subgroup Y'} (hZ : Nat.card Z = 3) {x : Y'} (hx : x ∈ Z) :
    x * x * x = 1 := by
  have hfin : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have h := Subgroup.orderOf_dvd_natCard Z hx
  rw [hZ] at h
  rw [← pow_three']
  exact orderOf_dvd_iff_pow_eq_one.1 h

theorem zpowers_eq_of_card_three {Z : Subgroup Y'} (hZ : Nat.card Z = 3) {z : Y'} (hz : z ∈ Z)
    (hz1 : z ≠ 1) : zpowers z = Z := by
  have hfin : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hd : orderOf z ∣ 3 := hZ ▸ Subgroup.orderOf_dvd_natCard Z hz
  have hxo : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  refine eq_of_le_of_card_ge (zpowers_le.2 hz) ?_
  rw [Nat.card_zpowers, hxo, hZ]

theorem eq_one_or_eq_or_eq_inv_of_card_three {Z : Subgroup Y'} (hZ : Nat.card Z = 3) {z : Y'}
    (hz : z ∈ Z) (hz1 : z ≠ 1) {y : Y'} (hy : y ∈ Z) : y = 1 ∨ y = z ∨ y = z⁻¹ := by
  have hd : orderOf z ∣ 3 := by
    have hfin : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
    exact hZ ▸ Subgroup.orderOf_dvd_natCard Z hz
  have hxo : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  rw [← zpowers_eq_of_card_three hZ hz hz1] at hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  rw [← zpow_mod_orderOf, hxo]
  have : (k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) := by omega
  rcases this with h | h | h
  · left; simp [h]
  · right; left; simp [h]
  · right; right
    simp only [Nat.cast_ofNat, h]
    have h3 : z ^ (3 : ℕ) = 1 := hxo ▸ pow_orderOf_eq_one z
    calc z ^ (2 : ℤ) = z ^ (2 : ℕ) := by norm_cast
      _ = z⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact h3

theorem card_quasi {K0 Z : Subgroup Y'} {π : K0 →* alternatingGroup (Fin 6)}
    (h : QuasiData K0 Z π) : Nat.card K0 = 1080 := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective h.surj
  have h2 : Nat.card π.ker = 3 := by
    rw [← h.subgroupOf_eq_ker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Z_le).toEquiv,
      h.card_Z]
  rw [← h1, h2, card_alt6]

theorem mem_of_central {K0 Z : Subgroup Y'} {π : K0 →* alternatingGroup (Fin 6)}
    (h : QuasiData K0 Z π) {x : Y'} (hx : x ∈ K0) (hc : ∀ g ∈ K0, x * g = g * x) : x ∈ Z := by
  have h1 : π ⟨x, hx⟩ = 1 := by
    apply alt6_central
    intro c
    obtain ⟨g, rfl⟩ := h.surj c
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hc g g.2))
  exact (h.ker _).1 h1

end Quasi

open Fixed Heisenberg in
theorem card_decomp_omega [Finite V] (hV2 : ∀ v : V, v * v = 1) (ω β : MulAut V)
    (hω3 : ω * ω * ω = 1) (hωfpf : ∀ v : V, ω v = v → v = 1) (hβ3 : β * β * β = 1)
    (hωβ : β * ω = ω * β) (U : Subgroup V) (hUω : ∀ u ∈ U, ω u ∈ U)
    (hUβ : ∀ u ∈ U, β u ∈ U) :
    Nat.card U = Nat.card (U ⊓ fixedSubgroupAut β : Subgroup V) *
      (Nat.card (U ⊓ fixedSubgroupAut (ω * β) : Subgroup V) *
        Nat.card (U ⊓ fixedSubgroupAut (ω * ω * β) : Subgroup V)) := by
  have hc : Commute ω β := hωβ.symm
  have hcω : Commute ω ω := Commute.refl ω
  have hc1 : Commute ω (ω * β) := hcω.mul_right hc
  have hcω2 : Commute ω (ω * ω) := hcω.mul_right hcω
  have hc2 : Commute ω (ω * ω * β) := hcω2.mul_right hc
  have hd0 : Commute (ω * ω) β := hc.mul_left hc
  have hd1 : Commute (ω * ω) (ω * β) := hc1.mul_left hc1
  have hd2 : Commute (ω * ω) (ω * ω * β) := hc2.mul_left hc2
  have hx1 : (ω * β) * (ω * β) * (ω * β) = 1 := by
    rw [mul_cube_of_comm hc.eq, hω3, hβ3, mul_one]
  have hx2 : (ω * ω * β) * (ω * ω * β) * (ω * ω * β) = 1 := by
    rw [mul_cube_of_comm hd0.eq, hβ3, mul_one]
    calc ω * ω * (ω * ω) * (ω * ω) = (ω * ω * ω) * (ω * ω * ω) := by group
      _ = 1 := by rw [hω3, one_mul]
  have hζ1 := cube_omega ω hω3 hωfpf
  have hζ2 := cube_omega_sq ω hω3 hωfpf
  have hx01 : β = ω * ω * (ω * β) := by
    calc β = (ω * ω * ω) * β := by rw [hω3, one_mul]
      _ = ω * ω * (ω * β) := by group
  have hx02 : β = ω * (ω * ω * β) := by
    calc β = (ω * ω * ω) * β := by rw [hω3, one_mul]
      _ = ω * (ω * ω * β) := by group
  have hx12 : ω * β = ω * ω * (ω * ω * β) := by
    calc ω * β = ((ω * ω * ω) * ω) * β := by rw [hω3, one_mul]
      _ = ω * ω * (ω * ω * β) := by group
  exact card_decomp hV2 β (ω * β) (ω * ω * β) U hβ3 hx1 hx2 hUβ
    (fun u hu => hUω _ (hUβ u hu)) (fun u hu => hUω _ (hUω _ (hUβ u hu)))
    (fun c hc' => cube_eq_one_of_conj (ω * ω) (ω * β) β hx01 hd1.eq hζ2 hc')
    (fun c hc' => cube_eq_one_of_conj ω (ω * ω * β) β hx02 hc2.eq hζ1 hc')
    (fun c hc' => cube_eq_one_of_conj ω β (ω * β) rfl hc.eq hζ1 hc')
    (fun c hc' => cube_eq_one_of_conj (ω * ω) (ω * ω * β) (ω * β) hx12 hd2.eq hζ2 hc')
    (fun c hc' => cube_eq_one_of_conj (ω * ω) β (ω * ω * β) rfl hd0.eq hζ2 hc')
    (fun c hc' => cube_eq_one_of_conj ω (ω * β) (ω * ω * β) (mul_assoc ω ω β) hc1.eq hζ1 hc')
    (cube_sum hV2 ω β hω3 hωfpf hωβ)

theorem false_of_two_order_five {D : Type*} [CommGroup D] [Finite D] (hD2 : ∀ v : D, v * v = 1)
    (hD : Nat.card D = 2 ^ 6) (σ τ : MulAut D) (hσ : orderOf σ = 5) (hτ : orderOf τ = 5)
    (hcomm : σ * τ = τ * σ) (hne : τ ∉ zpowers σ) : False := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hσc : Nat.card (zpowers σ) = 5 := by rw [Nat.card_zpowers, hσ]
  have hτc : Nat.card (zpowers τ) = 5 := by rw [Nat.card_zpowers, hτ]
  have hfσ : Finite (zpowers σ) := Nat.finite_of_card_ne_zero (by rw [hσc]; norm_num)
  have hfτ : Finite (zpowers τ) := Nat.finite_of_card_ne_zero (by rw [hτc]; norm_num)
  have hcom : ∀ (m : zpowers σ) (n : zpowers τ), Commute ((zpowers σ).subtype m)
      ((zpowers τ).subtype n) := by
    rintro ⟨m, hm⟩ ⟨n, hn⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hm
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hn
    exact Commute.zpow_zpow (show Commute σ τ from hcomm) i j
  have hinter : zpowers σ ⊓ zpowers τ = ⊥ := by
    have hdvd : Nat.card (zpowers σ ⊓ zpowers τ : Subgroup (MulAut D)) ∣ 5 := by
      rw [← hτc]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime h5.out).1 hdvd with h | h
    · exact (Subgroup.eq_bot_iff_card _).2 h
    · exfalso
      have heq : zpowers σ ⊓ zpowers τ = zpowers τ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      have hτmem : τ ∈ zpowers σ ⊓ zpowers τ := by rw [heq]; exact mem_zpowers τ
      exact hne hτmem.1
  let f : (zpowers σ) × (zpowers τ) →* MulAut D :=
    (zpowers σ).subtype.noncommCoprod (zpowers τ).subtype hcom
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : (a : MulAut D) * (b : MulAut D) = 1 := hab
    have ha : (a : MulAut D) ∈ zpowers σ ⊓ zpowers τ := by
      refine ⟨a.2, ?_⟩
      have : (a : MulAut D) = (b : MulAut D)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact (zpowers τ).inv_mem b.2
    rw [hinter, mem_bot] at ha
    have hb : (b : MulAut D) = 1 := by rw [ha, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hcard : Nat.card ((zpowers σ) × (zpowers τ)) = 25 := by
    rw [Nat.card_prod, hσc, hτc]
  exact not_dvd_25_of_six hD2 hD f hf (by rw [hcard])

section Actions

variable {Y : Type} [Group Y]

theorem not_mem_of_orderOf_five {Z : Subgroup Y} (hZ : Nat.card Z = 3) {x : Y}
    (hx : orderOf x = 5) : x ∉ Z := by
  intro hmem
  have hfin : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have h := Subgroup.orderOf_dvd_natCard Z hmem
  rw [hx, hZ] at h
  omega

theorem faithful_of_fpf [Finite V] (hV2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 2 ^ 12)
    (ρ : Y →* MulAut V) {S Z : Subgroup Y} {π : S →* alternatingGroup (Fin 6)}
    (q : QuasiData S Z π) {D : Subgroup V} (hD : ∀ s ∈ S, ∀ v ∈ D, ρ s v ∈ D) (hDne : D ≠ ⊥)
    {z : Y} (hz : z ∈ Z) (hfpf : ∀ v ∈ D, ρ z v = v → v = 1) :
    (∀ s ∈ S, (∀ v ∈ D, ρ s v = v) → s = 1) ∧ 2 ^ 6 ≤ Nat.card D := by
  have hN := q.dichotomy (kerOn_le ρ S D) (kerOn_normalized ρ hD)
  have hzS : z ∈ S := q.Z_le hz
  have hzN : z ∉ kerOn ρ S D := by
    intro h
    apply hDne
    rw [eq_bot_iff]
    intro v hv
    rw [mem_bot]
    exact hfpf v hv (h.2 v hv)
  have hle : kerOn ρ S D ≤ Z := by
    rcases hN with h | h
    · exact h
    · exfalso
      apply hzN
      rw [h]
      exact hzS
  have hfaith : ∀ s ∈ S, (∀ v ∈ D, ρ s v = v) → s = 1 := by
    intro s hs hsD
    by_contra hs1
    have hsN : s ∈ kerOn ρ S D := ⟨hs, hsD⟩
    have hzp : zpowers s = Z := zpowers_eq_of_card_three q.card_Z (hle hsN) hs1
    have hzz : z ∈ zpowers s := by rw [hzp]; exact hz
    exact hzN ((zpowers_le.2 hsN) hzz)
  refine ⟨hfaith, ?_⟩
  have hfinS : Finite S := Nat.finite_of_card_ne_zero (by rw [card_quasi q]; norm_num)
  have hdvd : Nat.card D ∣ 2 ^ 12 := by
    rw [← hV]
    exact Subgroup.card_subgroup_dvd_card D
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  by_contra hlt
  push Not at hlt
  have hk5 : k ≤ 5 := by
    by_contra h
    push Not at h
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hD2 : ∀ v : D, v * v = 1 := fun v => Subtype.ext (hV2 v)
  exact not_dvd_27_of_small hD2 hk5 hk' (actAut ρ S D hD) (actAut_injective ρ hD hfaith)
    (by rw [card_quasi q]; norm_num)

theorem trivial_of_faithful [Finite V] (hV2 : ∀ v : V, v * v = 1) (ρ : Y →* MulAut V)
    {S S' Z Z' : Subgroup Y} {π : S →* alternatingGroup (Fin 6)}
    {π' : S' →* alternatingGroup (Fin 6)} (q : QuasiData S Z π) (q' : QuasiData S' Z' π')
    (hcomm : ∀ a ∈ S, ∀ b ∈ S', a * b = b * a) {D : Subgroup V} (hDord : Nat.card D = 2 ^ 6)
    (hD : ∀ s ∈ S, ∀ v ∈ D, ρ s v ∈ D) (hD' : ∀ s ∈ S', ∀ v ∈ D, ρ s v ∈ D)
    (hfaith : ∀ s ∈ S', (∀ v ∈ D, ρ s v = v) → s = 1) : ∀ s ∈ S, ∀ v ∈ D, ρ s v = v := by
  have hN := q.dichotomy (kerOn_le ρ S D) (kerOn_normalized ρ hD)
  rcases hN with hle | hSN
  · exfalso
    have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hfinS : Finite S := Nat.finite_of_card_ne_zero (by rw [card_quasi q]; norm_num)
    have hfinS' : Finite S' := Nat.finite_of_card_ne_zero (by rw [card_quasi q']; norm_num)
    obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := S) 5 (by rw [card_quasi q]; norm_num)
    obtain ⟨r', hr'⟩ := exists_prime_orderOf_dvd_card' (G := S') 5
      (by rw [card_quasi q']; norm_num)
    have hrY : orderOf (r : Y) = 5 := by rw [Subgroup.orderOf_coe]; exact hr
    have hr'Y : orderOf (r' : Y) = 5 := by rw [Subgroup.orderOf_coe]; exact hr'
    let σ := actAut ρ S D hD r
    let σ' := actAut ρ S' D hD' r'
    have hσ5 : σ ^ 5 = 1 := by
      rw [← map_pow, ← hr, pow_orderOf_eq_one, map_one]
    have hσ'5 : σ' ^ 5 = 1 := by
      rw [← map_pow, ← hr', pow_orderOf_eq_one, map_one]
    have hσne : σ ≠ 1 := by
      intro h
      have : (r : Y) ∈ kerOn ρ S D := by
        refine ⟨r.2, fun v hv => ?_⟩
        have := congrArg (fun f : MulAut D => (f ⟨v, hv⟩ : V)) h
        simp only [MulAut.one_apply] at this
        exact (actAut_apply ρ hD r ⟨v, hv⟩).symm.trans this
      exact not_mem_of_orderOf_five q.card_Z hrY (hle this)
    have hσ'ne : σ' ≠ 1 := by
      intro h
      have h1 : (r' : Y) = 1 := by
        refine hfaith r' r'.2 fun v hv => ?_
        have := congrArg (fun f : MulAut D => (f ⟨v, hv⟩ : V)) h
        simp only [MulAut.one_apply] at this
        exact (actAut_apply ρ hD' r' ⟨v, hv⟩).symm.trans this
      rw [h1, orderOf_one] at hr'Y
      omega
    have hσo : orderOf σ = 5 := orderOf_eq_prime hσ5 hσne
    have hσ'o : orderOf σ' = 5 := orderOf_eq_prime hσ'5 hσ'ne
    have hcommSS : ∀ (a : S) (b : S'), actAut ρ S D hD a * actAut ρ S' D hD' b =
        actAut ρ S' D hD' b * actAut ρ S D hD a := by
      intro a b
      refine MulEquiv.ext fun x => Subtype.ext ?_
      show ρ a (ρ b x) = ρ b (ρ a x)
      rw [← Fixed.rho_mul_apply, ← Fixed.rho_mul_apply, hcomm a a.2 b b.2]
    have hne : σ' ∉ zpowers σ := by
      intro hmem
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hmem
      have hcen : ∀ g ∈ S', (r' : Y) * g = g * r' := by
        intro g hg
        have hc : Commute (actAut ρ S' D hD' ⟨g, hg⟩) σ' := by
          rw [← hj]
          exact ((show Commute (actAut ρ S' D hD' ⟨g, hg⟩) σ from
            (hcommSS r ⟨g, hg⟩).symm).zpow_right j)
        have h1 : actAut ρ S' D hD' (⟨g, hg⟩ * r') = actAut ρ S' D hD' (r' * ⟨g, hg⟩) := by
          rw [map_mul, map_mul]
          exact hc.eq
        have h2 := actAut_injective ρ hD' hfaith h1
        exact (congrArg Subtype.val h2).symm
      exact not_mem_of_orderOf_five q'.card_Z hr'Y (mem_of_central q' r'.2 hcen)
    exact false_of_two_order_five (fun v => Subtype.ext (hV2 v)) hDord σ σ' hσo hσ'o
      (hcommSS r r') hne
  · intro s hs v hv
    have : s ∈ kerOn ρ S D := by rw [hSN]; exact hs
    exact this.2 v hv

end Actions

section Misc

theorem fixedSubgroupAut_mul_self (x : MulAut V) (hx : x * x * x = 1) :
    fixedSubgroupAut (x * x) = fixedSubgroupAut x := by
  ext v
  simp only [mem_fixedSubgroupAut]
  constructor
  · intro h
    have h1 : x (x (x v)) = v := by
      have := congrArg (fun f : MulAut V => f v) hx
      simpa using this
    have h2 : x (x (x v)) = x v := by
      have : (x * x) v = v := h
      simp only [MulAut.mul_apply] at this
      rw [this]
    rw [← h2, h1]
  · intro h
    simp only [MulAut.mul_apply, h]

variable [Finite V] in
theorem exists_comm_eq (x y : MulAut V) (hxy : x * y = y * x)
    (hfpf : ∀ v : V, x v = v → y v = v → v = 1) {D : Subgroup V}
    (hD : D = fixedSubgroupAut y) : ∀ v ∈ D, ∃ w ∈ D, x w * w⁻¹ = v := by
  subst hD
  have hDx : ∀ w ∈ fixedSubgroupAut y, x w ∈ fixedSubgroupAut y := fun w hw =>
    Heisenberg.fixedSubgroupAut_invariant hxy.symm w hw
  let φ : fixedSubgroupAut y →* fixedSubgroupAut y :=
    MonoidHom.mk' (fun w => ⟨x w * w⁻¹, Subgroup.mul_mem _ (hDx w w.2) (Subgroup.inv_mem _ w.2)⟩)
    (fun a b => Subtype.ext (by
      simp only [Subgroup.coe_mul, map_mul, mul_inv]
      ac_rfl))
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : x w * (w : V)⁻¹ = 1 := congrArg Subtype.val hw
    have h2 : x w = w := mul_inv_eq_one.1 h1
    have h3 : y w = w := mem_fixedSubgroupAut.1 w.2
    exact Subtype.ext (hfpf w h2 h3)
  intro v hv
  obtain ⟨w, hw⟩ := Finite.injective_iff_surjective.1 hinj ⟨v, hv⟩
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

end Misc

end LevelC

end CFSG.EvenSporadicStandard.M24Std.DResH
