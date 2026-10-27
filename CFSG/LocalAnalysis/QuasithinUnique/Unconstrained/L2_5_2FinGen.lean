module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinTools

public section

namespace CFSG.QuasithinUnique.Unc25G2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Descent

variable {X A : Type*} [Group X] [Group A]

theorem exists_descent {ρ : X →* A} (hρ : Function.Surjective ρ) (α : MulAut X)
    (hker : ∀ x, ρ x = 1 ↔ ρ (α x) = 1) : ∃ α' : MulAut A, ∀ x, ρ (α x) = α' (ρ x) := by
  classical
  let s : A → X := Function.surjInv hρ
  have hs : ∀ a, ρ (s a) = a := Function.surjInv_eq hρ
  have key : ∀ x y, ρ x = ρ y → ρ (α x) = ρ (α y) := by
    intro x y h
    have h1 : ρ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := (hker _).mp h1
    rw [map_mul, map_inv, map_mul, map_inv] at h2
    exact (inv_mul_eq_one.mp h2)
  let f : A → A := fun a => ρ (α (s a))
  have hf : ∀ x, ρ (α x) = f (ρ x) := fun x => key _ _ (hs (ρ x)).symm
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    have h : ρ (α (s a * s b)) = f (ρ (s a * s b)) := hf _
    have e : ρ (s a * s b) = a * b := by rw [map_mul, hs, hs]
    rw [e] at h
    rw [← h, map_mul α, map_mul ρ]
  have hone : f 1 = 1 := by
    have h : ρ (s 1) = 1 := hs 1
    exact (hker _).mp h
  let φ : A →* A := ⟨⟨f, hone⟩, hmul⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : ρ (α (s a)) = 1 := ha
    have h2 : ρ (s a) = 1 := (hker _).mpr h1
    rw [hs] at h2
    exact h2
  have hsurj : Function.Surjective φ := by
    intro b
    refine ⟨ρ (α.symm (s b)), ?_⟩
    have h := hf (α.symm (s b))
    rw [MulEquiv.apply_symm_apply, hs] at h
    exact h.symm
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, hf⟩

end Descent

theorem mem_center_iff_apply {X : Type*} [Group X] (α : MulAut X) (x : X) :
    x ∈ Subgroup.center X ↔ α x ∈ Subgroup.center X := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := h (α.symm g)
    have h2 := congrArg α this
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h2
  · intro h g
    apply α.injective
    rw [map_mul, map_mul]
    exact h (α g)

theorem exists_descent_of_center {X A : Type*} [Group X] [Group A] {ρ : X →* A}
    (hρ : Function.Surjective ρ) (hker : ∀ x, ρ x = 1 ↔ x ∈ Subgroup.center X) (α : MulAut X) :
    ∃ α' : MulAut A, ∀ x, ρ (α x) = α' (ρ x) :=
  exists_descent hρ α (fun x => by rw [hker, hker]; exact mem_center_iff_apply α x)

theorem commutator_mul_central {X : Type*} [Group X] {c d : X} (hc : c ∈ Subgroup.center X)
    (hd : d ∈ Subgroup.center X) (u v : X) : ⁅u * c, v * d⁆ = ⁅u, v⁆ := by
  have h1 : ∀ w : X, ⁅c, w⁆ = 1 := fun w =>
    commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp hc w).symm
  have h2 : ∀ w : X, ⁅w, d⁆ = 1 := fun w =>
    commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp hd w)
  rw [commutatorElement_mul_left_eq_conj_mul, h1, mul_one, mul_inv_cancel, one_mul,
    commutatorElement_mul_right_eq_mul_conj, h2, mul_one, mul_inv_cancel_right]

theorem eq_conj_of_descend {X A : Type*} [Group X] [Group A] (ρ : X →* A)
    (hZ : ρ.ker ≤ Subgroup.center X) (hperf : ρ.ker = ⊥ ∨ commutator X = ⊤)
    (α : MulAut X) (l : X) (h : ∀ x, ρ (α x) = ρ (l * x * l⁻¹)) :
    ∀ x, α x = l * x * l⁻¹ := by
  have hf : ∀ x, α x * (l * x * l⁻¹)⁻¹ ∈ ρ.ker := fun x => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h x, mul_inv_cancel]
  rcases hperf with hbot | hcomm
  · intro x
    have := hf x
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  · have hex : ∀ x, α x = (l * x * l⁻¹) * (α x * (l * x * l⁻¹)⁻¹) := fun x => by
      have hc := Subgroup.mem_center_iff.mp (hZ (hf x)) (l * x * l⁻¹)
      rw [hc]; group
    have hle : commutator X ≤ MonoidHom.eqLocus α.toMonoidHom (MulAut.conj l).toMonoidHom := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      show α ⁅x, y⁆ = l * ⁅x, y⁆ * l⁻¹
      rw [map_commutatorElement, hex x, hex y, commutator_mul_central (hZ (hf x)) (hZ (hf y)),
        conjugate_commutatorElement]
    intro x
    have : x ∈ commutator X := by rw [hcomm]; trivial
    exact hle this

theorem eq_top_of_map_eq_top {X A : Type*} [Group X] [Group A] (ρ : X →* A)
    (hZ : ρ.ker ≤ Subgroup.center X) (hperf : ρ.ker = ⊥ ∨ commutator X = ⊤)
    {H : Subgroup X} (hH : H.map ρ = ⊤) : H = ⊤ := by
  have hsurj : ∀ x : X, ∃ h ∈ H, ρ h = ρ x := fun x => by
    have : ρ x ∈ H.map ρ := by rw [hH]; trivial
    obtain ⟨h, hh, e⟩ := this
    exact ⟨h, hh, e⟩
  have hmemz : ∀ x h : X, ρ h = ρ x → h⁻¹ * x ∈ Subgroup.center X := fun x h e =>
    hZ (by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel])
  rcases hperf with hbot | hcomm
  · rw [eq_top_iff]
    intro x _
    obtain ⟨h, hh, e⟩ := hsurj x
    have : h⁻¹ * x ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at this
    rw [← this]; exact hh
  · rw [eq_top_iff, ← hcomm, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨hx, hhx, ex⟩ := hsurj x
    obtain ⟨hy, hhy, ey⟩ := hsurj y
    have hxe : x = hx * (hx⁻¹ * x) := by group
    have hye : y = hy * (hy⁻¹ * y) := by group
    have : ⁅x, y⁆ = ⁅hx, hy⁆ := by
      conv_lhs => rw [hxe, hye]
      exact commutator_mul_central (hmemz x hx ex) (hmemz y hy ey) hx hy
    rw [this, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hhx hhy) (H.inv_mem hhx)) (H.inv_mem hhy)

section Transfer

open scoped IsMulCommutative

theorem exists_hom_ne_one_of_central_three {Y : Type*} [Group Y] [Finite Y] (hY : Nat.card Y = 72)
    {z : Y} (hz : z ∈ Subgroup.center Y) (hz3 : orderOf z = 3) :
    ∃ f : Y →* Y, f z ≠ 1 ∧ ∀ y : Y, (∃ k : ℕ, y ^ 2 ^ k = 1) → f y = 1 := by
  have h3p : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzp : IsPGroup 3 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz3]
    norm_num
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hQidx : (Q : Subgroup Y).index = 8 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have h := (Q : Subgroup Y).card_mul_index
    rw [hY, hn] at h
    have hnd : ¬ 3 ∣ (Q : Subgroup Y).index := Q.not_dvd_index
    have hn2 : n ≤ 2 := by
      by_contra hn3
      have h27 : 27 ∣ 3 ^ n := by
        have : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
        simpa using this
      have : 27 ∣ 72 := by rw [← h]; exact h27.mul_right _
      omega
    interval_cases n
    · exfalso; apply hnd; omega
    · exfalso; apply hnd; omega
    · omega
  have hQcard : Nat.card Q = 3 ^ 2 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have h := (Q : Subgroup Y).card_mul_index
    rw [hY, hn, hQidx] at h
    have h9 : 3 ^ n = 3 ^ 2 := by omega
    rw [hn, h9]
  have : IsMulCommutative (Q : Subgroup Y) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hQcard
  have : (Q : Subgroup Y).FiniteIndex := ⟨by rw [hQidx]; norm_num⟩
  have hzQ : z ∈ (Q : Subgroup Y) := hQ (Subgroup.mem_zpowers z)
  let τ : Y →* (Q : Subgroup Y) := MonoidHom.transfer (MonoidHom.id (Q : Subgroup Y))
  have key : ∀ (k : ℕ) (g₀ : Y), g₀⁻¹ * z ^ k * g₀ ∈ (Q : Subgroup Y) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k ∈ Subgroup.center Y := Subgroup.pow_mem _ hz k
    rw [Subgroup.mem_center_iff] at hc
    rw [mul_assoc, ← hc g₀, inv_mul_cancel_left]
  have hτz : τ z = ⟨z ^ (Q : Subgroup Y).index, MonoidHom.transfer_eq_pow_aux z key⟩ :=
    MonoidHom.transfer_eq_pow (MonoidHom.id (Q : Subgroup Y)) z key
  refine ⟨(Q : Subgroup Y).subtype.comp τ, ?_, ?_⟩
  · intro h
    have h1 : τ z = 1 := by
      apply Subtype.ext
      simpa using h
    rw [hτz] at h1
    have h2' : z ^ (Q : Subgroup Y).index = 1 := congrArg Subtype.val h1
    have h2 : z ^ 8 = 1 := by rwa [hQidx] at h2'
    have h3 : orderOf z ∣ 8 := orderOf_dvd_of_pow_eq_one h2
    rw [hz3] at h3
    omega
  · rintro y ⟨k, hk⟩
    have h1 : (τ y) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    have h2 : orderOf (τ y) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') (τ y)
    rw [hj] at h2
    have h3 : j = 0 := by
      by_contra hj0
      have : 3 ∣ 2 ^ k := (dvd_pow_self 3 hj0).trans h2
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
      omega
    rw [h3, pow_zero, orderOf_eq_one_iff] at hj
    simp [hj]

end Transfer

section Lift

variable {X A : Type*} [Group X] [Finite X] [Group A] [Finite A]

omit [Finite X] in
theorem card_comap_eq {ρ : X →* A} (hρ : Function.Surjective ρ) (Kb : Subgroup A) :
    Nat.card (Kb.comap ρ) = Nat.card ρ.ker * Nat.card Kb := by
  have h1 := (Kb.comap ρ).card_mul_index
  have h2 := Kb.card_mul_index
  have h3 := Subgroup.card_ker_mul_card_of_surjective hρ
  rw [Kb.index_comap_of_surjective hρ] at h1
  have hpos : 0 < Kb.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, ← h3, ← h2, mul_assoc]

theorem map_eq_of_forall_mem {H : Subgroup A} (α : MulAut A) (h : ∀ x ∈ H, α x ∈ H) :
    H.map α.toMonoidHom = H := by
  have hle : H.map α.toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective α.injective).ge

theorem lift_charTwo (ρ : X →* A) (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ Subgroup.center X) (hZc : Nat.card ρ.ker = 1 ∨ Nat.card ρ.ker = 3)
    {P : Subgroup X} (hP : IsPGroup 2 P) {Kb Vb : Subgroup A} (hK24 : Nat.card Kb = 24)
    (hPK : P.map ρ ≤ Kb) (hVP : Vb ≤ P.map ρ) (hV2 : IsPGroup 2 Vb)
    (hVn : ∀ k ∈ Kb, ∀ v ∈ Vb, k * v * k⁻¹ ∈ Vb)
    (hVc : ∀ k ∈ Kb, (∀ v ∈ Vb, k * v = v * k) → k ∈ Vb)
    (hgen : ∀ H : Subgroup A, (∀ k ∈ Kb, ∀ p ∈ P.map ρ, k * p * k⁻¹ ∈ H) → Kb ≤ H)
    (Φ : MulAut X → Prop) (hΦ : ∀ α, Φ α → P.map α.toMonoidHom = P)
    (hinv : ∀ α, Φ α → (Kb.comap ρ).map α.toMonoidHom = Kb.comap ρ) :
    ∃ K V : Subgroup X, V ≤ K ∧ K ≤ Subgroup.normalizer (V : Set X) ∧ IsPGroup 2 V ∧
      (∀ x ∈ K, (∀ v ∈ V, x * v = v * x) → x ∈ V) ∧ K.map ρ = Kb ∧
      ∀ α, Φ α → K.map α.toMonoidHom = K := by
  classical
  set Y : Subgroup X := Kb.comap ρ with hY
  have hPY : P ≤ Y := fun p hp => hPK ⟨p, hp, rfl⟩
  let gens : Set X := {g | ∃ x ∈ Y, ∃ p ∈ P, g = x * p * x⁻¹}
  set K : Subgroup X := Subgroup.closure gens with hKdef
  have hgY : ∀ x ∈ Y, ∀ p ∈ P, x * p * x⁻¹ ∈ Y := fun x hx p hp =>
    Y.mul_mem (Y.mul_mem hx (hPY hp)) (Y.inv_mem hx)
  have hKY : K ≤ Y := by
    rw [hKdef, Subgroup.closure_le]
    rintro g ⟨x, hx, p, hp, rfl⟩
    exact hgY x hx p hp
  have hPK' : P ≤ K := fun p hp => Subgroup.subset_closure ⟨1, Y.one_mem, p, hp, by simp⟩
  have hKmap : K.map ρ = Kb := by
    apply le_antisymm
    · exact Subgroup.map_le_iff_le_comap.mpr hKY
    · apply hgen
      intro k hk p hp
      obtain ⟨x, rfl⟩ := hρ k
      obtain ⟨p₀, hp₀, rfl⟩ := hp
      refine ⟨x * p₀ * x⁻¹, Subgroup.subset_closure ⟨x, hk, p₀, hp₀, rfl⟩, ?_⟩
      simp
  have hKker : ∀ x ∈ K, ρ x = 1 → x = 1 := by
    intro x hxK hx1
    rcases hZc with hc | hc
    · have hbot : ρ.ker = ⊥ := Subgroup.card_eq_one.mp hc
      have h : x ∈ ρ.ker := hx1
      rw [hbot] at h
      exact h
    · by_contra hxne
      have hxker : x ∈ ρ.ker := hx1
      have hxcen : x ∈ Subgroup.center X := hZ hxker
      have hord : orderOf x = 3 := by
        have h1 : orderOf (⟨x, hxker⟩ : ρ.ker) ∣ Nat.card ρ.ker := orderOf_dvd_natCard _
        rw [hc, Subgroup.orderOf_mk] at h1
        rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hxne
        · exact h
      have hxY : x ∈ Y := hKY hxK
      have hcardY : Nat.card Y = 72 := by rw [hY, card_comap_eq hρ, hc, hK24]
      have hz'c : (⟨x, hxY⟩ : Y) ∈ Subgroup.center Y := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        have := Subgroup.mem_center_iff.mp hxcen y
        simpa using this
      have hz'o : orderOf (⟨x, hxY⟩ : Y) = 3 := by rw [Subgroup.orderOf_mk, hord]
      obtain ⟨f, hf1, hf2⟩ := exists_hom_ne_one_of_central_three hcardY hz'c hz'o
      have hKle : K ≤ f.ker.map Y.subtype := by
        rw [hKdef, Subgroup.closure_le]
        rintro g ⟨x₁, hx₁, p, hp, rfl⟩
        refine ⟨⟨x₁ * p * x₁⁻¹, hgY x₁ hx₁ p hp⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
        apply hf2
        obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
        refine ⟨k, ?_⟩
        apply Subtype.ext
        have hk' : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
        show (x₁ * p * x₁⁻¹) ^ 2 ^ k = 1
        rw [conj_pow, hk']
        simp
      obtain ⟨y, hy, hyx⟩ := hKle hxK
      have hyz : y = ⟨x, hxY⟩ := Subtype.ext hyx
      rw [hyz] at hy
      exact hf1 hy
  set V : Subgroup X := K ⊓ Vb.comap ρ with hVdef
  have hρK : ∀ k ∈ K, ρ k ∈ Kb := fun k hk => hKY hk
  have hfwd : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V := by
    intro k hk v hv
    refine ⟨K.mul_mem (K.mul_mem hk hv.1) (K.inv_mem hk), ?_⟩
    show ρ (k * v * k⁻¹) ∈ Vb
    rw [map_mul, map_mul, map_inv]
    exact hVn _ (hρK k hk) _ hv.2
  refine ⟨K, V, inf_le_left, ?_, ?_, ?_, hKmap, ?_⟩
  · intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hfwd k hk h hh
    · intro hh
      have := hfwd k⁻¹ (K.inv_mem hk) _ hh
      simpa [mul_assoc] using this
  · intro v
    obtain ⟨k, hk⟩ := hV2 ⟨ρ v, v.2.2⟩
    refine ⟨k, ?_⟩
    have h1 : ρ ((v : X) ^ 2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa [map_pow] using this
    have h2 : (v : X) ^ 2 ^ k ∈ K := K.pow_mem v.2.1 _
    apply Subtype.ext
    simpa using hKker _ h2 h1
  · intro x hxK hxc
    have hρx : ρ x ∈ Kb := hρK x hxK
    have hcomm : ∀ v ∈ Vb, ρ x * v = v * ρ x := by
      intro v hv
      obtain ⟨p, hp, hpv⟩ := hVP hv
      have hpV : p ∈ V := ⟨hPK' hp, by show ρ p ∈ Vb; rw [hpv]; exact hv⟩
      have := hxc p hpV
      rw [← hpv, ← map_mul, ← map_mul, this]
    exact ⟨hxK, hVc _ hρx hcomm⟩
  · intro α hα
    have hαY : Y.map α.toMonoidHom = Y := hinv α hα
    have hαP : P.map α.toMonoidHom = P := hΦ α hα
    have hKle : K.map α.toMonoidHom ≤ K := by
      rw [hKdef, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g, ⟨x, hx, p, hp, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨α x, ?_, α p, ?_, by simp⟩
      · have : α x ∈ Y.map α.toMonoidHom := ⟨x, hx, rfl⟩
        rwa [hαY] at this
      · have : α p ∈ P.map α.toMonoidHom := ⟨p, hp, rfl⟩
        rwa [hαP] at this
    exact Subgroup.eq_of_le_of_card_ge hKle (Subgroup.card_map_of_injective α.injective).ge

theorem lift_charTwo' (ρ : X →* A) (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ Subgroup.center X) (hZc : Nat.card ρ.ker = 1 ∨ Nat.card ρ.ker = 3)
    {P : Subgroup X} (hP : IsPGroup 2 P) {Pb Kb Vb : Subgroup A} (hPb : P.map ρ = Pb)
    (hPb8 : Nat.card Pb = 8) (hK24 : Nat.card Kb = 24) (hPK : Pb ≤ Kb) (hVP : Vb ≤ Pb)
    (hV2 : IsPGroup 2 Vb) (hVn : ∀ k ∈ Kb, ∀ v ∈ Vb, k * v * k⁻¹ ∈ Vb)
    (hVc : ∀ k ∈ Kb, (∀ v ∈ Vb, k * v = v * k) → k ∈ Vb)
    (hnot : ∃ k ∈ Kb, ∃ p ∈ Pb, k * p * k⁻¹ ∉ Pb)
    (Φ : MulAut X → Prop) (hΦ : ∀ α, Φ α → P.map α.toMonoidHom = P)
    (hinv : ∀ α, Φ α → ∃ α' : MulAut A, (∀ x, ρ (α x) = α' (ρ x)) ∧ Kb.map α'.toMonoidHom = Kb) :
    ∃ K V : Subgroup X, V ≤ K ∧ K ≤ Subgroup.normalizer (V : Set X) ∧ IsPGroup 2 V ∧
      (∀ x ∈ K, (∀ v ∈ V, x * v = v * x) → x ∈ V) ∧ K.map ρ = Kb ∧
      ∀ α, Φ α → K.map α.toMonoidHom = K := by
  subst hPb
  refine lift_charTwo ρ hρ hZ hZc hP hK24 hPK hVP hV2 hVn hVc ?_ Φ hΦ ?_
  · intro H hH
    obtain ⟨k, hk, p, hp, hnot'⟩ := hnot
    have hPH' : P.map ρ ≤ H ⊓ Kb := fun p hp =>
      ⟨by simpa using hH 1 Kb.one_mem p hp, hPK hp⟩
    have hmem : k * p * k⁻¹ ∈ H ⊓ Kb :=
      ⟨hH k hk p hp, Kb.mul_mem (Kb.mul_mem hk (hPK hp)) (Kb.inv_mem hk)⟩
    have hne : Nat.card (H ⊓ Kb : Subgroup A) ≠ 8 := by
      intro h8
      have := Subgroup.eq_of_le_of_card_ge hPH' (by rw [hPb8, h8])
      rw [← this] at hmem
      exact hnot' hmem
    have hd1 : 8 ∣ Nat.card (H ⊓ Kb : Subgroup A) := by
      have := Subgroup.card_dvd_of_le hPH'
      rwa [hPb8] at this
    have hd2 : Nat.card (H ⊓ Kb : Subgroup A) ∣ 24 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : H ⊓ Kb ≤ Kb)
      rwa [hK24] at this
    have hle := Nat.le_of_dvd (by norm_num) hd2
    have h24 : Nat.card (H ⊓ Kb : Subgroup A) = 24 := by
      obtain ⟨m, hm⟩ := hd1
      rw [hm] at hd2 hne hle ⊢
      have hm3 : m ≤ 3 := by omega
      interval_cases m <;> omega
    have heq : H ⊓ Kb = Kb := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hK24, h24])
    intro x hx
    rw [← heq] at hx
    exact hx.1
  · intro α hα
    obtain ⟨α', hα', hK⟩ := hinv α hα
    have hle : (Kb.comap ρ).map α.toMonoidHom ≤ Kb.comap ρ := by
      rintro _ ⟨x, hx, rfl⟩
      show ρ (α x) ∈ Kb
      rw [hα' x]
      have : α' (ρ x) ∈ Kb.map α'.toMonoidHom := ⟨ρ x, hx, rfl⟩
      rwa [hK] at this
    exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective α.injective).ge

end Lift

section Wrapper

variable {G : Type*} [Group G]

theorem isPGroup_inf_subgroupOf {S₀ : Subgroup G} (L : Subgroup G) (hS₀ : IsPGroup 2 S₀) :
    IsPGroup 2 ((S₀ ⊓ L).subgroupOf L) := by
  intro g
  obtain ⟨k, hk⟩ := hS₀ ⟨((g.1 : ↥L) : G),
    (inf_le_left : S₀ ⊓ L ≤ S₀) (Subgroup.mem_subgroupOf.mp g.2)⟩
  have hk' : ((g.1 : ↥L) : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact ⟨k, Subtype.ext (Subtype.ext hk')⟩

theorem map_conjAut_subgroupOf_eq {L S₀ : Subgroup G}
    (hS : S₀ ≤ Subgroup.normalizer (L : Set G)) {s : G} (hs : s ∈ S₀) :
    ((S₀ ⊓ L).subgroupOf L).map (conjAut L s (hS hs)).toMonoidHom = (S₀ ⊓ L).subgroupOf L := by
  refine Subgroup.ext (fun y => ?_)
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨S₀.mul_mem (S₀.mul_mem hs hx.1) (S₀.inv_mem hs), (conjAut L s (hS hs) x).2⟩
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    have hs' : s⁻¹ ∈ S₀ := S₀.inv_mem hs
    refine ⟨conjAut L s⁻¹ (hS hs') y, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, coe_conjAut]
      exact ⟨S₀.mul_mem (S₀.mul_mem hs' hy.1) (S₀.inv_mem hs'), (conjAut L s⁻¹ (hS hs') y).2⟩
    · apply Subtype.ext
      show ((conjAut L s (hS hs) (conjAut L s⁻¹ (hS hs') y) : L) : G) = y
      rw [coe_conjAut, coe_conjAut]
      group

theorem exists_charTwo_map_of_canonical {L S₀ : Subgroup G}
    (hS : S₀ ≤ Subgroup.normalizer (L : Set G)) {K V : Subgroup L} (hVK : V ≤ K)
    (hn : K ≤ Subgroup.normalizer (V : Set L)) (hV : IsPGroup 2 V)
    (hC : ∀ x ∈ K, (∀ v ∈ V, x * v = v * x) → x ∈ V)
    (hinv : ∀ s (hs : s ∈ S₀), K.map (conjAut L s (hS hs)).toMonoidHom = K) :
    CharTwo (K.map L.subtype) ∧
      S₀ ≤ Subgroup.normalizer ((K.map L.subtype : Subgroup G) : Set G) := by
  refine ⟨charTwo_map_subtype_of_normal_pGroup hVK hn hV hC, ?_⟩
  refine le_normalizer_map_subtype hS K (fun s hs x hx => ?_)
  rw [← hinv s hs]
  exact ⟨x, hx, rfl⟩

end Wrapper

section SylowStd

variable {X A : Type*} [Group X] [Finite X] [Group A] [Finite A]

theorem exists_conj_comp_map_eq (ρ : X →* A) (hρ : Function.Surjective ρ) {P : Subgroup X}
    (hP2 : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index) {Q : Subgroup A} (hQ2 : IsPGroup 2 Q)
    (hQi : ¬ 2 ∣ Q.index) :
    ∃ a : A, P.map ((MulAut.conj a).toMonoidHom.comp ρ) = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 X := hP2.toSylow hPi
  have hmapi : ¬ 2 ∣ (P.map ρ).index := by
    have h := Sylow.not_dvd_index (S.mapSurjective hρ)
    rwa [Sylow.coe_mapSurjective, show (S : Subgroup X) = P from rfl] at h
  obtain ⟨a, ha⟩ := exists_conj_map_eq (hP2.map ρ) hmapi hQ2 hQi
  exact ⟨a, by rw [← ha, Subgroup.map_map]⟩

end SylowStd

end CFSG.QuasithinUnique.Unc25G2
