module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaModel

public section

namespace CFSG.ComponentClassification.AS81.HeCompl

open Subgroup

variable {G P : Type*} [Group G] [Group P] {X L : Subgroup G} {T M : Subgroup P}

theorem psi_eq_one_iff {ψ : ↥L →* ↥M} (hψk : ψ.ker = X.subgroupOf L) (ℓ : ↥L) :
    ψ ℓ = 1 ↔ (ℓ : G) ∈ X := by
  rw [← MonoidHom.mem_ker, hψk, mem_subgroupOf]

theorem conj_mem {ψ : ↥L →* ↥M} (hψk : ψ.ker = X.subgroupOf L) (ℓ : ↥L) {x : G} (hx : x ∈ X)
    (hxL : x ∈ L) : (ℓ : G) * x * (ℓ : G)⁻¹ ∈ X := by
  have h : ψ (ℓ * ⟨x, hxL⟩ * ℓ⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, (psi_eq_one_iff hψk ⟨x, hxL⟩).mpr hx, mul_one, mul_inv_cancel]
  exact (psi_eq_one_iff hψk _).mp h

theorem mem_normalizer_zpowers_of_conj {g w : G} (h : g * w * g⁻¹ = w ∨ g * w * g⁻¹ = w⁻¹) :
    g ∈ normalizer (zpowers w : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change zpowers (g * w * g⁻¹) = zpowers w
  rcases h with h | h
  · rw [h]
  · rw [h, zpowers_inv]

theorem exists_conj_eq_mul [Finite G] {ψ : ↥L →* ↥M} (hXL : X ≤ L)
    (hψk : ψ.ker = X.subgroupOf L) {v : G} (hvL : v ∈ L)
    (hv : ∀ x : ↥X, v * x = x * v → x = 1) {x : G} (hx : x ∈ X) :
    ∃ e ∈ X, e * v * e⁻¹ = x * v := by
  have hmem : ∀ e : ↥X, (e : G) * (v * (e : G)⁻¹ * v⁻¹) ∈ X := fun e =>
    mul_mem e.2 (conj_mem hψk ⟨v, hvL⟩ (inv_mem e.2) (hXL (inv_mem e.2)))
  let c : ↥X → ↥X := fun e => ⟨_, hmem e⟩
  have hinj : Function.Injective c := by
    intro e₁ e₂ h
    have h1 : (e₁ : G) * (v * (e₁ : G)⁻¹ * v⁻¹) = e₂ * (v * (e₂ : G)⁻¹ * v⁻¹) :=
      congrArg Subtype.val h
    have h2 : v * ((e₂⁻¹ * e₁ : ↥X) : G) = ((e₂⁻¹ * e₁ : ↥X) : G) * v := by
      simp only [coe_mul, coe_inv]
      calc v * ((e₂ : G)⁻¹ * e₁) = (e₂ : G)⁻¹ * (e₂ * (v * (e₂ : G)⁻¹ * v⁻¹)) * v * e₁ := by
            group
        _ = (e₂ : G)⁻¹ * (e₁ * (v * (e₁ : G)⁻¹ * v⁻¹)) * v * e₁ := by rw [h1]
        _ = (e₂ : G)⁻¹ * e₁ * v := by group
    have h3 := hv _ h2
    rw [inv_mul_eq_one] at h3
    exact h3.symm
  obtain ⟨e, he⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨x, hx⟩
  refine ⟨e, e.2, ?_⟩
  have h1 : (e : G) * (v * (e : G)⁻¹ * v⁻¹) = x := congrArg Subtype.val he
  calc (e : G) * v * (e : G)⁻¹ = (e * (v * (e : G)⁻¹ * v⁻¹)) * v := by group
    _ = x * v := by rw [h1]

theorem eq_one_of_commute (ι : ↥X ≃* ↥T) (ψ : ↥L →* ↥M)
    (hequiv : ∀ (ℓ : ↥L) (x y : ↥X), (y : G) = ℓ * x * (ℓ : G)⁻¹ →
      (ι y : P) = ψ ℓ * ι x * (ψ ℓ : P)⁻¹)
    {ζ : P} (hfix : ∀ t ∈ T, ζ * t * ζ⁻¹ = t → t = 1) {ω : ↥L} (hωζ : (ψ ω : P) = ζ)
    {x : ↥X} (hx : (ω : G) * x = x * ω) : x = 1 := by
  have h := hequiv ω x x (by rw [hx, mul_inv_cancel_right])
  rw [hωζ] at h
  have h1 : ((ι x : ↥T) : P) = 1 := hfix _ (ι x).2 h.symm
  exact ι.injective ((Subtype.ext h1).trans (map_one ι).symm)

theorem exists_omega (ψ : ↥L →* ↥M) (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = X.subgroupOf L) (hX2 : ∀ x ∈ X, x * x = 1) {ζ : P} (hζM : ζ ∈ M)
    (hζ3 : ζ ^ 3 = 1) : ∃ ω : ↥L, ω ^ 3 = 1 ∧ (ψ ω : P) = ζ := by
  obtain ⟨ℓ, hℓ⟩ := hψs ⟨ζ, hζM⟩
  have h3 : ((ℓ ^ 3 : ↥L) : G) ∈ X := by
    rw [← psi_eq_one_iff hψk, map_pow, hℓ]
    exact Subtype.ext (by simpa using hζ3)
  have h6 : ℓ ^ 6 = 1 := by
    have h := hX2 _ h3
    apply Subtype.ext
    rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add]
    simpa using h
  refine ⟨ℓ ^ 4, ?_, ?_⟩
  · rw [← pow_mul, show 4 * 3 = 6 * 2 by norm_num, pow_mul, h6, one_pow]
  · rw [map_pow, hℓ]
    change ζ ^ 4 = ζ
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hζ3, one_mul, pow_one]

theorem inf_normalizer_eq_bot (ι : ↥X ≃* ↥T) (ψ : ↥L →* ↥M) (hXL : X ≤ L)
    (hψk : ψ.ker = X.subgroupOf L)
    (hequiv : ∀ (ℓ : ↥L) (x y : ↥X), (y : G) = ℓ * x * (ℓ : G)⁻¹ →
      (ι y : P) = ψ ℓ * ι x * (ψ ℓ : P)⁻¹)
    {ζ : P} (hζ1 : ζ ≠ 1) (hfix : ∀ t ∈ T, ζ * t * ζ⁻¹ = t → t = 1) {ω : ↥L}
    (hω3 : ω ^ 3 = 1) (hωζ : (ψ ω : P) = ζ) :
    X ⊓ (L ⊓ normalizer (zpowers (ω : G) : Set G)) = ⊥ := by
  rw [eq_bot_iff]
  rintro e ⟨heX, -, heN⟩
  rw [mem_bot]
  have hmem : (e : G) * ω * e⁻¹ ∈ zpowers (ω : G) :=
    (mem_normalizer_iff.mp heN _).mp (mem_zpowers _)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have hψe : ψ ⟨e, hXL heX⟩ = 1 := (psi_eq_one_iff hψk _).mpr heX
  have hk' : ω ^ k = ⟨e, hXL heX⟩ * ω * (⟨e, hXL heX⟩ : ↥L)⁻¹ := Subtype.ext (by simpa using hk)
  have hζ3 : ζ ^ 3 = 1 := by
    rw [← hωζ]
    have := congrArg (fun l => ((ψ l : ↥M) : P)) hω3
    simpa using this
  have hζk : ζ ^ k = ζ := by
    have := congrArg (fun l => ((ψ l : ↥M) : P)) hk'
    simp only [map_zpow, map_mul, map_inv, hψe, one_mul, inv_one, mul_one] at this
    rw [← hωζ]
    simpa using this
  have hord : orderOf ζ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hζ3 hζ1
  have hdvd : (3 : ℤ) ∣ k - 1 := by
    have h1 : ζ ^ (k - 1) = 1 := by rw [zpow_sub_one, hζk, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [hord] at this
  have hω' : (ω : G) ^ (k - 1) = 1 := by
    obtain ⟨j, hj⟩ := hdvd
    have hω3' : (ω : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hω3
    rw [hj, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hω3', one_zpow]
  have hcomm : (ω : G) * e = e * ω := by
    have h1 : (e : G) * ω * e⁻¹ = ω := by
      rw [← hk, show k = (k - 1) + 1 by ring, zpow_add_one, hω', one_mul]
    calc (ω : G) * e = (e * ω * e⁻¹) * e := by rw [h1]
      _ = e * ω := by group
  have := eq_one_of_commute ι ψ hequiv hfix hωζ (x := ⟨e, heX⟩) hcomm
  exact congrArg Subtype.val this

theorem exists_mem_inv_mul_mem [Finite G] (ι : ↥X ≃* ↥T) (ψ : ↥L →* ↥M) (hXL : X ≤ L)
    (hψk : ψ.ker = X.subgroupOf L)
    (hequiv : ∀ (ℓ : ↥L) (x y : ↥X), (y : G) = ℓ * x * (ℓ : G)⁻¹ →
      (ι y : P) = ψ ℓ * ι x * (ψ ℓ : P)⁻¹)
    {ζ : P} (hfix : ∀ t ∈ T, ζ * t * ζ⁻¹ = t → t = 1)
    (hζn : ∀ m ∈ M, m * ζ * m⁻¹ = ζ ∨ m * ζ * m⁻¹ = ζ⁻¹) {ω : ↥L} (hωζ : (ψ ω : P) = ζ)
    (ℓ : ↥L) : ∃ e ∈ X, e⁻¹ * (ℓ : G) ∈ L ⊓ normalizer (zpowers (ω : G) : Set G) := by
  have hfixω : ∀ x : ↥X, (ω : G) * x = x * ω → x = 1 := fun x hx =>
    eq_one_of_commute ι ψ hequiv hfix hωζ hx
  have hfixω' : ∀ x : ↥X, (ω : G)⁻¹ * x = x * (ω : G)⁻¹ → x = 1 := fun x hx =>
    hfixω x (by
      calc (ω : G) * x = (ω : G) * (x * (ω : G)⁻¹) * ω := by group
        _ = (ω : G) * ((ω : G)⁻¹ * x) * ω := by rw [hx]
        _ = x * ω := by group)
  have hωL : (ω : G) ∈ L := ω.2
  have hψconj : ((ψ (ℓ * ω * ℓ⁻¹) : ↥M) : P) = (ψ ℓ : P) * ζ * (ψ ℓ : P)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    simp only [coe_mul, coe_inv, hωζ]
  have hkey : ∀ v : G, v ∈ L → (∀ x : ↥X, v * x = x * v → x = 1) →
      (ℓ : G) * ω * (ℓ : G)⁻¹ * v⁻¹ ∈ X →
      ∃ e ∈ X, (e⁻¹ * ℓ : G) * ω * (e⁻¹ * ℓ : G)⁻¹ = v := by
    intro v hvL hv hxv
    obtain ⟨e, heX, he⟩ := exists_conj_eq_mul hXL hψk hvL hv hxv
    refine ⟨e, heX, ?_⟩
    calc (e⁻¹ * ℓ : G) * ω * (e⁻¹ * ℓ : G)⁻¹
        = e⁻¹ * ((ℓ : G) * ω * (ℓ : G)⁻¹ * v⁻¹ * v) * e := by group
      _ = e⁻¹ * (e * v * e⁻¹) * e := by rw [he]
      _ = v := by group
  have hmemL : ∀ e ∈ X, e⁻¹ * (ℓ : G) ∈ L := fun e he => mul_mem (inv_mem (hXL he)) ℓ.2
  rcases hζn _ (ψ ℓ).2 with h | h
  · have hx : (ℓ : G) * ω * (ℓ : G)⁻¹ * (ω : G)⁻¹ ∈ X := by
      have h1 : ψ (ℓ * ω * ℓ⁻¹ * ω⁻¹) = 1 := by
        apply Subtype.ext
        rw [map_mul, map_inv, coe_mul, hψconj, coe_inv, hωζ, h, mul_inv_cancel]
        rfl
      simpa using (psi_eq_one_iff hψk _).mp h1
    obtain ⟨e, heX, he⟩ := hkey ω hωL hfixω hx
    exact ⟨e, heX, hmemL e heX, mem_normalizer_zpowers_of_conj (Or.inl he)⟩
  · have hx : (ℓ : G) * ω * (ℓ : G)⁻¹ * ((ω : G)⁻¹)⁻¹ ∈ X := by
      have h1 : ψ (ℓ * ω * ℓ⁻¹ * ω) = 1 := by
        apply Subtype.ext
        rw [map_mul, coe_mul, hψconj, hωζ, h, inv_mul_cancel]
        rfl
      simpa using (psi_eq_one_iff hψk _).mp h1
    obtain ⟨e, heX, he⟩ := hkey (ω : G)⁻¹ (inv_mem hωL) hfixω' hx
    exact ⟨e, heX, hmemL e heX, mem_normalizer_zpowers_of_conj (Or.inr he)⟩

theorem sup_normalizer_eq [Finite G] (ι : ↥X ≃* ↥T) (ψ : ↥L →* ↥M) (hXL : X ≤ L)
    (hψk : ψ.ker = X.subgroupOf L)
    (hequiv : ∀ (ℓ : ↥L) (x y : ↥X), (y : G) = ℓ * x * (ℓ : G)⁻¹ →
      (ι y : P) = ψ ℓ * ι x * (ψ ℓ : P)⁻¹)
    {ζ : P} (hfix : ∀ t ∈ T, ζ * t * ζ⁻¹ = t → t = 1)
    (hζn : ∀ m ∈ M, m * ζ * m⁻¹ = ζ ∨ m * ζ * m⁻¹ = ζ⁻¹) {ω : ↥L} (hωζ : (ψ ω : P) = ζ) :
    X ⊔ (L ⊓ normalizer (zpowers (ω : G) : Set G)) = L := by
  refine le_antisymm (sup_le hXL inf_le_left) fun ℓ hℓ => ?_
  obtain ⟨e, heX, he⟩ := exists_mem_inv_mul_mem ι ψ hXL hψk hequiv hfix hζn hωζ ⟨ℓ, hℓ⟩
  have : ℓ = e * (e⁻¹ * ℓ) := by group
  rw [this]
  exact mul_mem_sup heX he

theorem exists_mulEquiv_sup [Finite G] (ι : ↥X ≃* ↥T) (ψ : ↥L →* ↥M) (hXL : X ≤ L)
    (hψs : Function.Surjective ψ) (hψk : ψ.ker = X.subgroupOf L)
    (hequiv : ∀ (ℓ : ↥L) (x y : ↥X), (y : G) = ℓ * x * (ℓ : G)⁻¹ →
      (ι y : P) = ψ ℓ * ι x * (ψ ℓ : P)⁻¹)
    {ζ : P} (hζ1 : ζ ≠ 1) (hfix : ∀ t ∈ T, ζ * t * ζ⁻¹ = t → t = 1)
    (hζn : ∀ m ∈ M, m * ζ * m⁻¹ = ζ ∨ m * ζ * m⁻¹ = ζ⁻¹) (hTM : T ⊓ M = ⊥)
    (hMT : M ≤ normalizer (T : Set P)) {ω : ↥L} (hω3 : ω ^ 3 = 1) (hωζ : (ψ ω : P) = ζ) :
    ∃ f : ↥(T ⊔ M) ≃* ↥L,
      (∀ (t : P) (ht : t ∈ T), ((f ⟨t, mem_sup_left ht⟩ : ↥L) : G) = ι.symm ⟨t, ht⟩) ∧
      ∀ (m : P) (hm : m ∈ M), (ψ (f ⟨m, mem_sup_right hm⟩) : P) = m ∧
        ((f ⟨m, mem_sup_right hm⟩ : ↥L) : G) ∈ normalizer (zpowers (ω : G) : Set G) := by
  set K := L ⊓ normalizer (zpowers (ω : G) : Set G) with hK
  have hinf := inf_normalizer_eq_bot ι ψ hXL hψk hequiv hζ1 hfix hω3 hωζ
  let ψK : ↥(K.subgroupOf L) →* ↥M := ψ.comp (K.subgroupOf L).subtype
  have hψKi : Function.Injective ψK := by
    refine (injective_iff_map_eq_one ψK).mpr fun k hk => ?_
    have hkX : ((k : ↥L) : G) ∈ X := (psi_eq_one_iff hψk _).mp hk
    have hkK : ((k : ↥L) : G) ∈ K := mem_subgroupOf.mp k.2
    have h1 : ((k : ↥L) : G) ∈ X ⊓ K := ⟨hkX, hkK⟩
    rw [hinf, mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hψKs : Function.Surjective ψK := by
    intro m
    obtain ⟨ℓ, rfl⟩ := hψs m
    obtain ⟨e, heX, he⟩ := exists_mem_inv_mul_mem ι ψ hXL hψk hequiv hfix hζn hωζ ℓ
    refine ⟨⟨⟨e⁻¹ * ℓ, he.1⟩, mem_subgroupOf.mpr he⟩, ?_⟩
    have h1 : (⟨e⁻¹ * ℓ, he.1⟩ : ↥L) = (⟨e, hXL heX⟩ : ↥L)⁻¹ * ℓ := rfl
    change ψ ⟨e⁻¹ * ℓ, he.1⟩ = ψ ℓ
    rw [h1, map_mul, map_inv, (psi_eq_one_iff hψk _).mpr heX, inv_one, one_mul]
  let eK : ↥(K.subgroupOf L) ≃* ↥M := MulEquiv.ofBijective ψK ⟨hψKi, hψKs⟩
  let κ : ↥M →* ↥L := (K.subgroupOf L).subtype.comp eK.symm.toMonoidHom
  have hκψ : ∀ m : ↥M, ψ (κ m) = m := fun m => eK.apply_symm_apply m
  have hκK : ∀ m : ↥M, ((κ m : ↥L) : G) ∈ K := fun m => mem_subgroupOf.mp (eK.symm m).2
  have hxmem : ∀ ℓ : ↥L, ((ℓ * (κ (ψ ℓ))⁻¹ : ↥L) : G) ∈ X := fun ℓ => by
    rw [← psi_eq_one_iff hψk, map_mul, map_inv, hκψ, mul_inv_cancel]
  let xof : ↥L → ↥X := fun ℓ => ⟨_, hxmem ℓ⟩
  have hxof : ∀ ℓ : ↥L, ((xof ℓ : ↥X) : G) = ℓ * ((κ (ψ ℓ) : ↥L) : G)⁻¹ := fun ℓ => by
    simp [xof]
  have hmul : ∀ ℓ₁ ℓ₂ : ↥L, ((ι (xof (ℓ₁ * ℓ₂)) : ↥T) : P) * ((ψ (ℓ₁ * ℓ₂) : ↥M) : P) =
      ((ι (xof ℓ₁) : ↥T) : P) * ((ψ ℓ₁ : ↥M) : P) *
        (((ι (xof ℓ₂) : ↥T) : P) * ((ψ ℓ₂ : ↥M) : P)) := by
    intro ℓ₁ ℓ₂
    have hymem : (((κ (ψ ℓ₁) : ↥L) : G) * ((xof ℓ₂ : ↥X) : G) * ((κ (ψ ℓ₁) : ↥L) : G)⁻¹) ∈ X :=
      conj_mem hψk (κ (ψ ℓ₁)) (xof ℓ₂).2 (hXL (xof ℓ₂).2)
    have hιy := hequiv (κ (ψ ℓ₁)) (xof ℓ₂) ⟨_, hymem⟩ rfl
    rw [hκψ] at hιy
    have hx12 : xof (ℓ₁ * ℓ₂) = xof ℓ₁ * ⟨_, hymem⟩ := by
      apply Subtype.ext
      rw [hxof (ℓ₁ * ℓ₂)]
      change _ = ((xof ℓ₁ : ↥X) : G) *
        (((κ (ψ ℓ₁) : ↥L) : G) * ((xof ℓ₂ : ↥X) : G) * ((κ (ψ ℓ₁) : ↥L) : G)⁻¹)
      rw [hxof ℓ₁, hxof ℓ₂, map_mul ψ, map_mul κ]
      simp only [coe_mul]
      group
    rw [hx12, map_mul, coe_mul, hιy, map_mul, coe_mul]
    group
  let g : ↥L →* P := MonoidHom.mk'
    (fun ℓ => ((ι (xof ℓ) : ↥T) : P) * ((ψ ℓ : ↥M) : P)) hmul
  have hg : ∀ ℓ : ↥L, g ℓ = ((ι (xof ℓ) : ↥T) : P) * ((ψ ℓ : ↥M) : P) := fun _ => rfl
  have hgmem : ∀ ℓ : ↥L, g ℓ ∈ T ⊔ M := fun ℓ => by
    rw [hg]
    exact mul_mem (mem_sup_left (ι (xof ℓ)).2) (mem_sup_right (ψ ℓ).2)
  have hgX : ∀ x : ↥X, g (inclusion hXL x) = ((ι x : ↥T) : P) := by
    intro x
    have hψx : ψ (inclusion hXL x) = 1 := (psi_eq_one_iff hψk _).mpr x.2
    have hx : xof (inclusion hXL x) = x := by
      apply Subtype.ext
      rw [hxof, hψx, map_one]
      simp
    rw [hg, hx, hψx]
    simp
  have hgκ : ∀ m : ↥M, g (κ m) = (m : P) := by
    intro m
    have hx : xof (κ m) = 1 := by
      apply Subtype.ext
      rw [hxof, hκψ]
      simp
    rw [hg, hx, hκψ, map_one]
    simp
  have hgi : Function.Injective g := by
    refine (injective_iff_map_eq_one g).mpr fun ℓ hℓ => ?_
    rw [hg] at hℓ
    have h1 : ((ι (xof ℓ) : ↥T) : P) = ((ψ ℓ : ↥M) : P)⁻¹ := eq_inv_of_mul_eq_one_left hℓ
    have h2 : ((ι (xof ℓ) : ↥T) : P) ∈ T ⊓ M := by
      refine ⟨(ι (xof ℓ)).2, ?_⟩
      rw [h1]
      exact M.inv_mem (ψ ℓ).2
    rw [hTM, mem_bot] at h2
    have hψℓ : ψ ℓ = 1 := by
      apply Subtype.ext
      rw [h2] at h1
      have := congrArg (·⁻¹) h1
      simpa using this.symm
    have hx1 : xof ℓ = 1 := ι.injective ((Subtype.ext h2).trans (map_one ι).symm)
    have h3 := congrArg Subtype.val hx1
    rw [hxof, hψℓ, map_one] at h3
    exact Subtype.ext (by simpa using h3)
  have hgs : ∀ n : ↥(T ⊔ M), ∃ ℓ : ↥L, g ℓ = n := by
    rintro ⟨n, hn⟩
    have hn' : n ∈ ((T ⊔ M : Subgroup P) : Set P) := hn
    rw [coe_mul_of_right_le_normalizer_left T M hMT] at hn'
    obtain ⟨t, ht, m, hm, rfl⟩ := hn'
    refine ⟨inclusion hXL (ι.symm ⟨t, ht⟩) * κ ⟨m, hm⟩, ?_⟩
    rw [map_mul, hgX, hgκ, MulEquiv.apply_symm_apply]
  let g' : ↥L →* ↥(T ⊔ M) := g.codRestrict (T ⊔ M) hgmem
  have hg'b : Function.Bijective g' :=
    ⟨fun a b h => hgi (congrArg Subtype.val h), fun n => by
      obtain ⟨ℓ, hℓ⟩ := hgs n
      exact ⟨ℓ, Subtype.ext hℓ⟩⟩
  refine ⟨(MulEquiv.ofBijective g' hg'b).symm, fun t ht => ?_, fun m hm => ?_⟩
  · have h1 : (MulEquiv.ofBijective g' hg'b).symm ⟨t, mem_sup_left ht⟩ =
        inclusion hXL (ι.symm ⟨t, ht⟩) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      change t = g (inclusion hXL (ι.symm ⟨t, ht⟩))
      rw [hgX, MulEquiv.apply_symm_apply]
    rw [h1]
    rfl
  · have h1 : (MulEquiv.ofBijective g' hg'b).symm ⟨m, mem_sup_right hm⟩ = κ ⟨m, hm⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      change m = g (κ ⟨m, hm⟩)
      rw [hgκ]
    rw [h1, hκψ]
    exact ⟨rfl, (hκK ⟨m, hm⟩).2⟩

end CFSG.ComponentClassification.AS81.HeCompl

namespace CFSG.ComponentClassification.AS81

open Subgroup Hexa

theorem map_centralizer_singleton_eq {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    (centralizer ({a} : Set A)).map e.toMonoidHom = centralizer ({e a} : Set B) := by
  ext b
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg e h
    simpa using this
  · intro h
    apply e.injective
    simpa using h

theorem exists_mulEquiv_hexa {G : Type*} [Group G] [Finite G] (hF : HexaFacts)
    {X L : Subgroup G} (hXL : X ≤ L) (hX2 : ∀ x ∈ X, x * x = 1) (ι : ↥X ≃* ↥hexaT)
    (ψ : ↥L →* ↥hexaM) (hψs : Function.Surjective ψ) (hψk : ψ.ker = X.subgroupOf L)
    (hequiv : ∀ (ℓ : ↥L) (x y : ↥X), (y : G) = ℓ * x * (ℓ : G)⁻¹ →
      (ι y : Equiv.Perm (Fin 64)) = ψ ℓ * ι x * (ψ ℓ : Equiv.Perm (Fin 64))⁻¹)
    {ζ : Equiv.Perm (Fin 64)} (hζM : ζ ∈ hexaM) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    (hfix : ∀ t ∈ hexaT, ζ * t * ζ⁻¹ = t → t = 1)
    (hζn : ∀ m ∈ hexaM, m * ζ * m⁻¹ = ζ ∨ m * ζ * m⁻¹ = ζ⁻¹) (hTM : hexaT ⊓ hexaM = ⊥) :
    ∃ (ω : ↥L) (f : ↥(hexaT ⊔ hexaM) ≃* ↥L), ω ^ 3 = 1 ∧ (ψ ω : Equiv.Perm (Fin 64)) = ζ ∧
      X ⊓ (L ⊓ normalizer (zpowers (ω : G) : Set G)) = ⊥ ∧
      X ⊔ (L ⊓ normalizer (zpowers (ω : G) : Set G)) = L ∧
      (∀ (t : Equiv.Perm (Fin 64)) (ht : t ∈ hexaT),
        ((f ⟨t, mem_sup_left ht⟩ : ↥L) : G) = ι.symm ⟨t, ht⟩) ∧
      ∀ (m : Equiv.Perm (Fin 64)) (hm : m ∈ hexaM),
        (ψ (f ⟨m, mem_sup_right hm⟩) : Equiv.Perm (Fin 64)) = m ∧
        ((f ⟨m, mem_sup_right hm⟩ : ↥L) : G) ∈ normalizer (zpowers (ω : G) : Set G) := by
  obtain ⟨ω, hω3, hωζ⟩ := HeCompl.exists_omega ψ hψs hψk hX2 hζM hζ3
  obtain ⟨f, hfT, hfM⟩ := HeCompl.exists_mulEquiv_sup ι ψ hXL hψs hψk hequiv hζ1 hfix hζn hTM
    hF.normT hω3 hωζ
  exact ⟨ω, f, hω3, hωζ, HeCompl.inf_normalizer_eq_bot ι ψ hXL hψk hequiv hζ1 hfix hω3 hωζ,
    HeCompl.sup_normalizer_eq ι ψ hXL hψk hequiv hfix hζn hωζ, hfT, hfM⟩

end CFSG.ComponentClassification.AS81
