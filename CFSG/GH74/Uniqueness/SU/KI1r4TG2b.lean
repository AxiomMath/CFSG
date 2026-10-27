module

public import CFSG.GH74.Uniqueness.SU.KI1r4TG1
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma23
public import CFSG.GH74.GLS.C3.Layer3.A8Cover

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.K.R3
open CFSG.GH74.Uniqueness.SU.K.R4.L82 CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

theorem card_sup_zpowers_le_four {V : Type*} [Group V] (hcomm : ∀ a b : V, a * b = b * a)
    (hsq : ∀ a : V, a * a = 1) (u v : V) : Nat.card ↥(zpowers u ⊔ zpowers v) ≤ 4 := by
  classical
  let _ : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  refine (SU5.card_le_card_of_subset_finset (s := {1, u, v, u * v}) ?_).trans Finset.card_le_four
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hz
  rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers (hsq u) ha with rfl | rfl <;>
    rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers (hsq v) hb with rfl | rfl <;> simp


theorem card_invariant_mod_three {V : Type*} [Group V] [Finite V] (φ : MulAut V) (hφ : φ ^ 3 = 1)
    (hfix : ∀ v, φ v = v → v = 1) (U : Subgroup V) (hU : ∀ u ∈ U, φ u ∈ U) :
    Nat.card U ≡ 1 [MOD 3] := by
  classical
  have hφ3 : ∀ v, φ (φ (φ v)) = v := fun v => by
    have h3 : (φ ^ 3) v = v := by rw [hφ]; rfl
    exact h3
  have hU' : ∀ u ∈ U, φ (φ u) ∈ U := fun u hu => hU _ (hU u hu)
  let π : Function.End U := fun u => ⟨φ u, hU u u.2⟩
  have hπ : π ^ 3 ^ 1 = 1 := by
    funext u
    apply Subtype.ext
    show φ (φ (φ (u : V))) = u
    exact hφ3 u
  let _ : Fintype U := Fintype.ofFinite U
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hπ
  have h2 : Fintype.card (Function.fixedPoints π) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, Subtype.ext (by
      show φ (1 : V) = 1
      exact map_one φ)⟩, ?_⟩
    rintro ⟨u, hu⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hfix u (congrArg Subtype.val hu)
  rw [h2] at h1
  rwa [Nat.card_eq_fintype_card]


section Aprime

open CFSG.GH74.Uniqueness.SU.K.R3.Pow

variable {M : Type} [Group M] [Finite M]

theorem exists_Aprime (hM : IsPGroup 2 M) {σ τ : MulAut M} (h : DihAct σ τ 1)
    (h64 : Nat.card M = 64) (hZ4 : Nat.card (center M) = 4)
    (hfr : frattini M = center M) (c : M) (hcτ : τ c = c) (hcZ : c ∉ center M) :
    ∃ A' : Subgroup M, center M ≤ A' ∧ Nat.card A' = 16 ∧ (∀ a ∈ A', σ a ∈ A') ∧
      (∀ a ∈ A', τ a ∈ A') ∧
      ∀ C : Subgroup M, A' ≤ C → (∀ m ∈ C, σ m ∈ C) → C = A' ∨ C = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, hsq⟩ := quot_comm_sq hM
  set Φ : Subgroup M := frattini M with hΦ
  have hΦcard : Nat.card Φ = 4 := by rw [hfr]; exact hZ4
  have hVcard : Nat.card (M ⧸ Φ) = 16 := by
    have h1 := Φ.card_mul_index
    have h2 : Nat.card (M ⧸ Φ) = Φ.index := rfl
    rw [hΦcard, h64] at h1
    rw [h2]
    omega
  set u : M ⧸ Φ := (c : M ⧸ Φ) with hu
  set v : M ⧸ Φ := ((σ c : M) : M ⧸ Φ) with hv
  have hu1 : u ≠ 1 := by
    intro h1
    apply hcZ
    rw [← hfr]
    exact (QuotientGroup.eq_one_iff c).mp h1
  have hσu : bar σ u = v := bar_mk σ c
  have hvu : v ≠ u := by
    intro h1
    rw [← hσu] at h1
    exact hu1 (bar_fix hM h u h1)
  set ℓ : Subgroup (M ⧸ Φ) := zpowers u ⊔ zpowers v with hℓ
  have hℓ_le : Nat.card ℓ ≤ 4 := card_sup_zpowers_le_four hcomm hsq u v
  have hℓ_ge : 4 ≤ Nat.card ℓ := by
    have hdvd : Nat.card ℓ ∣ 16 := hVcard ▸ Subgroup.card_subgroup_dvd_card ℓ
    have h4 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h4] at hdvd
    obtain ⟨i, hi, hℓi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have huℓ : u ∈ ℓ := Subgroup.mem_sup_left (mem_zpowers u)
    have hvℓ : v ∈ ℓ := Subgroup.mem_sup_right (mem_zpowers v)
    by_contra hlt
    push Not at hlt
    have hi2 : i ≤ 1 := by
      by_contra hi2
      push Not at hi2
      have : 2 ^ 2 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi2
      omega
    interval_cases i
    · have hsub : Subsingleton ℓ := (Nat.card_eq_one_iff_unique.mp (by simpa using hℓi)).1
      exact hu1 (congrArg Subtype.val (Subsingleton.elim (⟨u, huℓ⟩ : ℓ) 1))
    · have hℓ2 : Nat.card ℓ = 2 := by simpa using hℓi
      rw [Nat.card_eq_two_iff' (1 : ℓ)] at hℓ2
      obtain ⟨y, -, hy⟩ := hℓ2
      have e1 := hy ⟨u, huℓ⟩ (fun h' => hu1 (congrArg Subtype.val h'))
      have e2 := hy ⟨v, hvℓ⟩ (fun h' => by
        have h0 : v = 1 := congrArg Subtype.val h'
        apply hu1
        have : bar σ u = bar σ 1 := by rw [hσu, h0, map_one]
        exact (bar σ).injective this)
      exact hvu (congrArg Subtype.val (e2.trans e1.symm))
  have hℓ4 : Nat.card ℓ = 4 := le_antisymm hℓ_le hℓ_ge
  have huℓ : u ∈ ℓ := Subgroup.mem_sup_left (mem_zpowers u)
  have hvℓ : v ∈ ℓ := Subgroup.mem_sup_right (mem_zpowers v)
  set π := QuotientGroup.mk' Φ with hπ
  set A' : Subgroup M := ℓ.comap π with hA'
  have hA'idx : A'.index = 4 := by
    rw [hA', Subgroup.index_comap_of_surjective ℓ (QuotientGroup.mk'_surjective Φ)]
    have h1 := ℓ.card_mul_index
    rw [hℓ4, hVcard] at h1
    omega
  have hA'card : Nat.card A' = 16 := by
    have h1 := A'.card_mul_index
    rw [hA'idx, h64] at h1
    omega
  have hΦA' : Φ ≤ A' := fun m hm => by
    show π m ∈ ℓ
    rw [show π m = 1 from (QuotientGroup.eq_one_iff m).mpr hm]
    exact one_mem _
  have hσ3 : σ ^ 3 = 1 := by simpa using h.pow
  have hσσ : ∀ m : M, σ⁻¹ m = σ (σ m) := fun m => by
    have h1 : σ⁻¹ = σ * σ := by
      have : σ⁻¹ = σ ^ 2 := by
        calc σ⁻¹ = σ⁻¹ * σ ^ 3 := by rw [hσ3, mul_one]
          _ = σ ^ 2 := by group
      rw [this, pow_two]
    rw [h1]; rfl
  have hτσ : ∀ m : M, τ m = m → τ (σ m) = σ (σ m) := fun m hm => by
    have e1 : τ * σ = σ⁻¹ * τ := by
      have := h.inv
      calc τ * σ = τ * σ * τ⁻¹ * τ := by group
        _ = σ⁻¹ * τ := by rw [this]
    have : (τ * σ) m = (σ⁻¹ * τ) m := by rw [e1]
    simp only [MulAut.mul_apply] at this
    rw [this, hm, hσσ]
  have hστv : bar σ v ∈ ℓ := by
    have h1 : c * σ c * σ (σ c) = 1 := prod_sigma h c
    have h2 : σ (σ c) = (c * σ c)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : bar σ v = (u * v)⁻¹ := by
      show bar σ ((σ c : M) : M ⧸ Φ) = _
      rw [bar_mk, h2, QuotientGroup.mk_inv, QuotientGroup.mk_mul]
    rw [h3]
    exact inv_mem (mul_mem huℓ hvℓ)
  have hσℓ : ∀ w ∈ ℓ, bar σ w ∈ ℓ := by
    intro w hw
    have : ℓ.map (bar σ).toMonoidHom ≤ ℓ := by
      rw [hℓ, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr hστv)
      show bar σ u ∈ ℓ
      rw [hσu]; exact hvℓ
    exact this ⟨w, hw, rfl⟩
  have hτℓ : ∀ w ∈ ℓ, bar τ w ∈ ℓ := by
    intro w hw
    have hτu : bar τ u = u := by
      show bar τ (c : M ⧸ Φ) = c
      rw [bar_mk, hcτ]
    have hτv : bar τ v = bar σ v := by
      show bar τ ((σ c : M) : M ⧸ Φ) = _
      rw [bar_mk, hτσ c hcτ]
      show _ = bar σ ((σ c : M) : M ⧸ Φ)
      rw [bar_mk]
    have : ℓ.map (bar τ).toMonoidHom ≤ ℓ := by
      rw [hℓ, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · show bar τ u ∈ ℓ
        rw [hτu]; exact huℓ
      · show bar τ v ∈ ℓ
        rw [hτv]; exact hστv
    exact this ⟨w, hw, rfl⟩
  refine ⟨A', hfr ▸ hΦA', hA'card, fun a ha => ?_, fun a ha => ?_, ?_⟩
  · show π (σ a) ∈ ℓ
    have : π (σ a) = bar σ (π a) := (bar_mk σ a).symm
    rw [this]
    exact hσℓ _ ha
  · show π (τ a) ∈ ℓ
    have : π (τ a) = bar τ (π a) := (bar_mk τ a).symm
    rw [this]
    exact hτℓ _ ha
  · intro C hAC hσC
    have hΦC : Φ ≤ C := hΦA'.trans hAC
    set Cb : Subgroup (M ⧸ Φ) := C.map π with hCb
    have hCbσ : ∀ w ∈ Cb, bar σ w ∈ Cb := by
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨σ m, hσC m hm, bar_mk σ m⟩
    have hmod := card_invariant_mod_three (bar σ) (by
      rw [← map_pow, hσ3, map_one]) (bar_fix hM h) Cb hCbσ
    have hℓCb : ℓ ≤ Cb := by
      intro w hw
      obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective Φ w
      exact ⟨m, hAC (by show π m ∈ ℓ; rw [hm]; exact hw), hm⟩
    have hdvd : Nat.card Cb ∣ 16 := hVcard ▸ Subgroup.card_subgroup_dvd_card Cb
    have hge : 4 ≤ Nat.card Cb := hℓ4 ▸ Subgroup.card_le_of_le hℓCb
    have h4 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h4] at hdvd
    obtain ⟨i, hi, hCbi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hcomapC : Cb.comap π = C := by
      rw [hCb, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr hΦC
    have hcase : Nat.card Cb = 4 ∨ Nat.card Cb = 16 := by
      have hmod' : Nat.card Cb % 3 = 1 := hmod
      rw [hCbi] at hmod' hge ⊢
      interval_cases i <;> omega
    rcases hcase with h4' | h16
    · left
      have : Cb = ℓ := (Subgroup.eq_of_le_of_card_ge hℓCb (by omega)).symm
      rw [← hcomapC, this]
    · right
      have : Cb = ⊤ := Subgroup.eq_top_of_card_eq Cb (by rw [h16, hVcard])
      rw [← hcomapC, this, Subgroup.comap_top]



theorem nonempty_mulEquiv_Z4Z4 {G : Type*} [Group G] [Finite G] (B : Subgroup G) (a b : G)
    (hab : a * b = b * a) (ha : orderOf a = 4) (hb : orderOf b = 4)
    (hB : zpowers a ⊔ zpowers b = B) (hcard : Nat.card B = 16) :
    Nonempty (↥B ≃* Multiplicative (ZMod 4 × ZMod 4)) := by
  have haB : a ∈ B := hB ▸ Subgroup.mem_sup_left (mem_zpowers a)
  have hbB : b ∈ B := hB ▸ Subgroup.mem_sup_right (mem_zpowers b)
  have hc : Commute a b := hab
  have hpow : ∀ (g : G) (n : ℕ), orderOf g = 4 → g ^ (n % 4) = g ^ n := fun g n hg => by
    rw [← hg]; exact pow_mod_orderOf g n
  let f : Multiplicative (ZMod 4 × ZMod 4) →* G :=
    MonoidHom.mk' (fun g => a ^ (Multiplicative.toAdd g).1.val * b ^ (Multiplicative.toAdd g).2.val)
      (by
        intro g h
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
        rw [hpow a _ ha, hpow b _ hb, pow_add, pow_add]
        have h1 : b ^ (Multiplicative.toAdd g).2.val * a ^ (Multiplicative.toAdd h).1.val =
            a ^ (Multiplicative.toAdd h).1.val * b ^ (Multiplicative.toAdd g).2.val :=
          (hc.symm.pow_pow _ _).eq
        calc a ^ (Multiplicative.toAdd g).1.val * a ^ (Multiplicative.toAdd h).1.val *
              (b ^ (Multiplicative.toAdd g).2.val * b ^ (Multiplicative.toAdd h).2.val)
            = a ^ (Multiplicative.toAdd g).1.val * (a ^ (Multiplicative.toAdd h).1.val *
              b ^ (Multiplicative.toAdd g).2.val) * b ^ (Multiplicative.toAdd h).2.val := by group
          _ = a ^ (Multiplicative.toAdd g).1.val * (b ^ (Multiplicative.toAdd g).2.val *
              a ^ (Multiplicative.toAdd h).1.val) * b ^ (Multiplicative.toAdd h).2.val := by
            rw [h1]
          _ = _ := by group)
  have hfB : ∀ g, f g ∈ B := fun g =>
    B.mul_mem (B.pow_mem haB _) (B.pow_mem hbB _)
  let f' : Multiplicative (ZMod 4 × ZMod 4) →* B := f.codRestrict B hfB
  have hsurj : Function.Surjective f' := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ closure ({a, b} : Set G) := by
      rw [← hB] at hz
      rwa [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
        ← Set.insert_eq] at hz
    obtain ⟨m, n, rfl⟩ := CFSG.GH74.GLS.Layer3.mem_closure_pair_of_commute hc hz'
    refine ⟨Multiplicative.ofAdd ((m : ZMod 4), (n : ZMod 4)), Subtype.ext ?_⟩
    show a ^ ((m : ZMod 4)).val * b ^ ((n : ZMod 4)).val = a ^ m * b ^ n
    have h1 : a ^ ((m : ZMod 4)).val = a ^ m := by
      rw [← zpow_natCast, ← zpow_mod_orderOf a m, ha]
      congr 1
      have := ZMod.val_intCast (n := 4) m
      simpa using this
    have h2 : b ^ ((n : ZMod 4)).val = b ^ n := by
      rw [← zpow_natCast, ← zpow_mod_orderOf b n, hb]
      congr 1
      have := ZMod.val_intCast (n := 4) n
      simpa using this
    rw [h1, h2]
  have hcard' : Nat.card (Multiplicative (ZMod 4 × ZMod 4)) ≤ Nat.card B := by
    rw [hcard, Nat.card_eq_fintype_card]
    decide
  have hbij : Function.Bijective f' := hsurj.bijective_of_nat_card_le hcard'
  exact ⟨(MulEquiv.ofBijective f' hbij).symm⟩


end Aprime

variable {H : Type} [Group H] [Finite H]

theorem RData.exists_dihAct {T : Sylow 2 H} {x : H} {A R : Subgroup H} {y : H}
    (hR : RData T x A R y) {R' : Subgroup H} (hR'R : R' ≤ R) (hx : ∀ r ∈ R', x * r * x⁻¹ ∈ R')
    (hy : ∀ r ∈ R', y * r * y⁻¹ ∈ R') :
    ∃ σ τ : MulAut ↥R', Pow.DihAct σ τ 1 ∧ (∀ r : R', ((σ r : R') : H) = y * r * y⁻¹) ∧
      (∀ r : R', ((τ r : R') : H) = x * r * x⁻¹) := by
  have hyN := Pow.mem_normalizer_of_forall_mem R' hy
  have hxN := Pow.mem_normalizer_of_forall_mem R' hx
  let σ : MulAut R' := R'.normalizerMonoidHom ⟨y, hyN⟩
  let τ : MulAut R' := R'.normalizerMonoidHom ⟨x, hxN⟩
  have hσapp : ∀ r : R', ((σ r : R') : H) = y * r * y⁻¹ := fun r => rfl
  have hτapp : ∀ r : R', ((τ r : R') : H) = x * r * x⁻¹ := fun r => rfl
  refine ⟨σ, τ, ⟨?_, ?_, ?_, ?_⟩, hσapp, hτapp⟩
  · have h1 : σ ^ 3 = 1 := by
      refine MulEquiv.ext fun r => ?_
      have h0 : ((σ ^ 3) r : R') = σ (σ (σ r)) := by
        simp [pow_succ, MulAut.mul_apply]
      rw [h0]
      show σ (σ (σ r)) = r
      apply Subtype.ext
      rw [hσapp, hσapp, hσapp]
      have h3 := hR.y_cube r (hR'R r.2)
      have hy3 : y ^ 3 = y * y * y := by rw [pow_succ, pow_two]
      rw [hy3] at h3
      calc y * (y * (y * (r : H) * y⁻¹) * y⁻¹) * y⁻¹
          = y * y * y * r * (y * y * y)⁻¹ := by group
        _ = r := h3
    simpa using h1
  · have : (⟨x, hxN⟩ : normalizer (R' : Set H)) ^ 2 = 1 :=
      Subtype.ext (by simpa [pow_two] using hR.x_sq)
    change R'.normalizerMonoidHom ⟨x, hxN⟩ ^ 2 = 1
    rw [← map_pow, this, map_one]
  · have : (⟨x, hxN⟩ : normalizer (R' : Set H)) * ⟨y, hyN⟩ *
        (⟨x, hxN⟩ : normalizer (R' : Set H))⁻¹ = (⟨y, hyN⟩ : normalizer (R' : Set H))⁻¹ :=
      Subtype.ext (by simpa using hR.xy)
    have h2 := congrArg R'.normalizerMonoidHom this
    simpa only [map_mul, map_inv] using h2
  · intro r hr
    exact Subtype.ext (hR.y_free r (hR'R r.2) (by rw [← hσapp r, hr]))

theorem RData.isL34Type_of_special {T : Sylow 2 H} {x : H} {A R : Subgroup H} {y : H}
    (hR : RData T x A R y) (h64 : Nat.card R = 64) (hZ4 : Nat.card (center ↥R) = 4)
    (hfr : frattini ↥R = center ↥R) (hcom : ∀ u v : ↥R, ⁅u, v⁆ ∈ center ↥R)
    (hcsq : ∀ a ∈ center ↥R, a * a = 1)
    (hinv : ∃ e : ↥R, e * e = 1 ∧ e ∉ center ↥R) :
    SU5.IsL34Type ↥R := by
  classical
  have hM : IsPGroup 2 ↥R := hR.R_two
  obtain ⟨σ, τ, hDih, hσapp, hτapp⟩ := hR.exists_dihAct le_rfl hR.x_norm hR.y_norm
  have hcardC : Nat.card (fixSub τ) ^ 2 = Nat.card ↥R := card_fixSub_sq _ ↥R rfl hM σ τ 1 hDih
  have hC8 : Nat.card (fixSub τ) = 8 := by
    have h1 : Nat.card (fixSub τ) ^ 2 = 8 ^ 2 := by rw [hcardC, h64]; norm_num
    exact Nat.pow_left_injective (by norm_num) h1
  obtain ⟨c, hcτ, hcZ⟩ : ∃ c : ↥R, τ c = c ∧ c ∉ center ↥R := by
    by_contra hcon
    push Not at hcon
    have hle : fixSub τ ≤ center ↥R := fun c hc => by
      by_contra hnc
      exact hnc (hcon c hc)
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨A', hZA', hA'card, hA'σ, hA'τ, hmax⟩ :=
    exists_Aprime hM hDih h64 hZ4 hfr c hcτ hcZ
  set B : Subgroup H := A'.map R.subtype with hB
  have hBR : B ≤ R := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hBx : ∀ r ∈ B, x * r * x⁻¹ ∈ B := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨τ a, hA'τ a ha, (hτapp a).symm ▸ rfl⟩
  have hBy : ∀ r ∈ B, y * r * y⁻¹ ∈ B := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨σ a, hA'σ a ha, (hσapp a).symm ▸ rfl⟩
  have hBcard : Nat.card B = 16 := by
    rw [hB, Subgroup.card_map_of_injective R.subtype_injective]
    exact hA'card
  rcases hR.lemma82 hBR hBx hBy with ⟨hab, c₀, hc₀B, hxc₀, hgen, hcard⟩ |
      ⟨h64B, -⟩
  swap
  · rw [hBcard] at h64B
    omega
  have hc₀4 : orderOf c₀ = 4 := by
    rw [hBcard] at hcard
    have h1 : orderOf c₀ ^ 2 = 4 ^ 2 := by rw [← hcard]; norm_num
    exact Nat.pow_left_injective (by norm_num) h1
  have hb₀B : y * c₀ * y⁻¹ ∈ B := hBy c₀ hc₀B
  have hb₀4 : orderOf (y * c₀ * y⁻¹) = 4 := by
    rw [← hc₀4]
    exact orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective c₀
  have hcomm₀ : c₀ * (y * c₀ * y⁻¹) = (y * c₀ * y⁻¹) * c₀ := hab c₀ hc₀B _ hb₀B
  obtain ⟨eB⟩ := nonempty_mulEquiv_Z4Z4 B c₀ (y * c₀ * y⁻¹) hcomm₀ hc₀4 hb₀4 hgen hBcard
  let e4 : ↥A' ≃* Multiplicative (ZMod 4 × ZMod 4) :=
    (A'.equivMapOfInjective R.subtype R.subtype_injective).trans eB
  have hA'ab : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    intro a ha b hb
    have := hab (a : H) ⟨a, ha, rfl⟩ (b : H) ⟨b, hb, rfl⟩
    exact Subtype.ext this
  have hcent : centralizer (A' : Set ↥R) = A' := by
    set C : Subgroup ↥R := centralizer (A' : Set ↥R) with hC
    have hA'C : A' ≤ C := fun a ha => by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hA'ab b hb a ha)
    have hσinv : ∀ a ∈ A', σ⁻¹ a ∈ A' := fun a ha => by
      have h1 : σ⁻¹ a = σ (σ a) := by
        have h3 : σ ^ 3 = 1 := by simpa using hDih.pow
        have h2 : σ⁻¹ = σ * σ := by
          have : σ⁻¹ = σ ^ 2 := by
            calc σ⁻¹ = σ⁻¹ * σ ^ 3 := by rw [h3, mul_one]
              _ = σ ^ 2 := by group
          rw [this, pow_two]
        rw [h2]; rfl
      rw [h1]
      exact hA'σ _ (hA'σ _ ha)
    have hσC : ∀ m ∈ C, σ m ∈ C := fun m hm => by
      rw [hC, Subgroup.mem_centralizer_iff] at hm ⊢
      intro a ha
      have h1 := hm (σ⁻¹ a) (hσinv a ha)
      have h2 : σ (σ⁻¹ a * m) = σ (m * σ⁻¹ a) := by rw [h1]
      simp only [map_mul, MulAut.apply_inv_self] at h2
      exact h2
    rcases hmax C hA'C hσC with h | h
    · exact h
    · exfalso
      have hle : A' ≤ center ↥R := fun a ha => by
        rw [Subgroup.mem_center_iff]
        intro m
        have : m ∈ C := by rw [h]; trivial
        rw [hC, Subgroup.mem_centralizer_iff] at this
        exact (this a ha).symm
      have := Subgroup.card_le_of_le hle
      omega
  have hA'n : A'.Normal := by
    refine ⟨fun a ha m => ?_⟩
    have h1 : m * a * m⁻¹ = ⁅m, a⁆ * a := by rw [commutatorElement_def]; group
    rw [h1]
    exact A'.mul_mem (hZA' (hcom m a)) ha
  have hinvA : ∀ h ∈ A', h * h = 1 → h ∈ center ↥R := by
    have hcard4 : Nat.card {g : Multiplicative (ZMod 4 × ZMod 4) // g * g = 1} = 4 := by
      rw [Nat.card_eq_fintype_card]; decide
    have hcardS : Nat.card {h : ↥A' // h * h = 1} = 4 := by
      rw [← hcard4]
      exact Nat.card_congr (e4.toEquiv.subtypeEquiv (fun h => by
        constructor
        · intro h1
          show e4 h * e4 h = 1
          rw [← map_mul, h1, map_one]
        · intro h1
          apply e4.injective
          rw [map_mul, map_one]
          exact h1))
    let ι : center ↥R → {h : ↥A' // h * h = 1} := fun z =>
      ⟨⟨z, hZA' z.2⟩, Subtype.ext (hcsq z z.2)⟩
    have hι : Function.Injective ι := fun z₁ z₂ h12 =>
      Subtype.ext (congrArg (fun s => ((s.1 : ↥A') : ↥R)) h12)
    have hbij : Function.Bijective ι := hι.bijective_of_nat_card_le (by rw [hcardS, hZ4])
    intro h hh hh2
    obtain ⟨z, hz⟩ := hbij.2 ⟨⟨h, hh⟩, Subtype.ext hh2⟩
    have := congrArg (fun s => ((s.1 : ↥A') : ↥R)) hz
    simp only [ι] at this
    rw [← this]
    exact z.2
  have hσ3 : σ ^ 3 = 1 := by simpa using hDih.pow
  have hσne : σ ≠ 1 := by
    intro h1
    have h0 : ∀ m : ↥R, m = 1 := fun m => hDih.fix m (by rw [h1]; rfl)
    have : Subsingleton ↥R := ⟨fun a b => (h0 a).trans (h0 b).symm⟩
    have h2 : Nat.card ↥R = 1 := Nat.card_of_subsingleton 1
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσne
  obtain ⟨-, hL⟩ := CFSG.GH74.GLS.Bg.TwoGroups.iv2_2_3 ↥R h64 σ hσord hDih.fix A' hA'n
    hA'σ ⟨e4⟩ hcent
  refine hL ?_
  obtain ⟨e, he2, heZ⟩ := hinv
  intro heq
  have heT : e ∈ CFSG.GH74.GLS.Bg.TwoGroups.Om1 (⊤ : Subgroup ↥R) :=
    Subgroup.subset_closure ⟨mem_top e, by rw [pow_two]; exact he2⟩
  rw [← heq] at heT
  have hle : CFSG.GH74.GLS.Bg.TwoGroups.Om1 A' ≤ center ↥R := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro h ⟨hA, h2⟩
    exact hinvA h hA (by rw [← pow_two]; exact h2)
  exact heZ (hle heT)

end CFSG.GH74.Uniqueness.SU.K.R4
