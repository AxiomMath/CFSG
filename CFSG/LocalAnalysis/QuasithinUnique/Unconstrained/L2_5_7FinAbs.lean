module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7Model

public section

namespace CFSG.QuasithinUnique.Fin257

open scoped commutatorElement Pointwise
open CFSG.Open CFSG.LieType.BorelTits

theorem fix_of_odd_aux {H : Type*} [Group H] (α : MulAut H) {m : ℕ} (hm : Odd m)
    (hαm : α ^ m = 1) (S : Subgroup H) (hS2 : IsPGroup 2 S) (hSfix : ∀ s ∈ S, α s = s)
    (x : H) (hx : x⁻¹ * α x ∈ S) : α x = x := by
  set c : H := x⁻¹ * α x with hc
  have hαx : α x = x * c := by rw [hc]; group
  have hαc : α c = c := hSfix c hx
  have hcpow : ∀ k : ℕ, (α ^ k) x = x * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, hαx, map_pow, hαc, pow_succ']
      group
  have h1 : c ^ m = 1 := by
    have := hcpow m
    rw [hαm] at this
    simpa using this
  obtain ⟨j, hj⟩ := hS2 ⟨c, hx⟩
  have h2 : c ^ (2 ^ j) = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hcop : Nat.Coprime m (2 ^ j) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr hm) : Nat.Coprime m 2)
  have hord : orderOf c ∣ 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rwa [Nat.Coprime.gcd_eq_one hcop] at this
  have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
  rw [hαx, hc1, mul_one]

theorem fix_of_stab {H : Type*} [Group H] (α : MulAut H) {m : ℕ} (hm : Odd m)
    (hαm : α ^ m = 1) (R : Subgroup H) (hR2 : IsPGroup 2 R) (hRfix : ∀ r ∈ R, α r = r)
    (hC : ∀ g : H, (∀ r ∈ R, g * r = r * g) → g ∈ R) (x : H)
    (hx : ∀ r ∈ R, x * r * x⁻¹ ∈ R) : α x = x := by
  apply fix_of_odd_aux α hm hαm R hR2 hRfix x
  apply hC
  intro r hr
  have h1 : α (x * r * x⁻¹) = x * r * x⁻¹ := hRfix _ (hx r hr)
  rw [map_mul, map_mul, map_inv, hRfix r hr] at h1
  have h2 : α x * r = x * r * x⁻¹ * α x := by
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  calc x⁻¹ * α x * r = x⁻¹ * (α x * r) := by rw [mul_assoc]
    _ = x⁻¹ * (x * r * x⁻¹ * α x) := by rw [h2]
    _ = r * (x⁻¹ * α x) := by group

theorem eq_one_of_fix_sup {H : Type*} [Group H] (α : MulAut H) (A B : Subgroup H)
    (hA : ∀ x ∈ A, α x = x) (hB : ∀ x ∈ B, α x = x) (hsup : A ⊔ B = ⊤) : α = 1 := by
  let S : Subgroup H := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id H)
  have hAS : A ≤ S := fun x hx => hA x hx
  have hBS : B ≤ S := fun x hx => hB x hx
  have : (⊤ : Subgroup H) ≤ S := hsup ▸ sup_le hAS hBS
  ext x
  exact this (Subgroup.mem_top x)


theorem comm_aux {G : Type*} [Group G] {g₁ g₂ c₁ c₂ : G} (h1 : c₁ * g₂ = g₂ * c₁)
    (h2 : c₂ * g₁ = g₁ * c₂) (h3 : c₁ * c₂ = c₂ * c₁) :
    ⁅g₁ * c₁, g₂ * c₂⁆ = ⁅g₁, g₂⁆ := by
  have h2' : c₂ * g₁⁻¹ = g₁⁻¹ * c₂ := (Commute.inv_right (show Commute c₂ g₁ from h2)).eq
  calc ⁅g₁ * c₁, g₂ * c₂⁆ = g₁ * (c₁ * g₂) * c₂ * c₁⁻¹ * g₁⁻¹ * c₂⁻¹ * g₂⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = g₁ * (g₂ * c₁) * c₂ * c₁⁻¹ * g₁⁻¹ * c₂⁻¹ * g₂⁻¹ := by rw [h1]
    _ = g₁ * g₂ * (c₁ * c₂ * c₁⁻¹) * g₁⁻¹ * c₂⁻¹ * g₂⁻¹ := by group
    _ = g₁ * g₂ * c₂ * g₁⁻¹ * c₂⁻¹ * g₂⁻¹ := by rw [h3]; group
    _ = g₁ * g₂ * (c₂ * g₁⁻¹) * c₂⁻¹ * g₂⁻¹ := by group
    _ = g₁ * g₂ * (g₁⁻¹ * c₂) * c₂⁻¹ * g₂⁻¹ := by rw [h2']
    _ = ⁅g₁, g₂⁆ := by simp only [commutatorElement_def]; group

theorem ao_model {M : Type*} [Group M] (R₁ R₂ U : Subgroup M)
    (hR₁2 : IsPGroup 2 R₁) (hR₂2 : IsPGroup 2 R₂)
    (hab₁ : ∀ x ∈ R₁, ∀ y ∈ R₁, x * y = y * x) (hab₂ : ∀ x ∈ R₂, ∀ y ∈ R₂, x * y = y * x)
    (hW : R₁ ⊓ R₂ ≤ ⁅R₁, R₂⁆)
    (hc₁ : ∀ g : M, (∀ r ∈ R₁, g * r = r * g) → g ∈ R₁)
    (hc₂ : ∀ g : M, (∀ r ∈ R₂, g * r = r * g) → g ∈ R₂)
    (hsup : Subgroup.normalizer (R₁ : Set M) ⊔ Subgroup.normalizer (R₂ : Set M) = ⊤)
    (hU₁ : R₁ ≤ U) (hU₂ : R₂ ≤ U)
    (α : MulAut M) {m : ℕ} (hm : Odd m) (hαm : α ^ m = 1)
    (hU : ∀ u ∈ U, u⁻¹ * α u ∈ R₁ ⊓ R₂) : α = 1 := by
  have hWfix : ∀ w ∈ R₁ ⊓ R₂, α w = w := by
    let S : Subgroup M := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id M)
    have hcomm : ⁅R₁, R₂⁆ ≤ S := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      obtain ⟨c₁, hc₁def, hc1₁, hc1₂⟩ : ∃ c₁, α g₁ = g₁ * c₁ ∧ c₁ ∈ R₁ ∧ c₁ ∈ R₂ :=
        ⟨g₁⁻¹ * α g₁, by group, Subgroup.mem_inf.mp (hU g₁ (hU₁ hg₁))⟩
      obtain ⟨c₂, hc₂def, hc2₁, hc2₂⟩ : ∃ c₂, α g₂ = g₂ * c₂ ∧ c₂ ∈ R₁ ∧ c₂ ∈ R₂ :=
        ⟨g₂⁻¹ * α g₂, by group, Subgroup.mem_inf.mp (hU g₂ (hU₂ hg₂))⟩
      show α ⁅g₁, g₂⁆ = ⁅g₁, g₂⁆
      rw [map_commutatorElement, hc₁def, hc₂def]
      exact comm_aux (hab₂ c₁ hc1₂ g₂ hg₂) (hab₁ c₂ hc2₁ g₁ hg₁) (hab₁ c₁ hc1₁ c₂ hc2₁)
    exact fun w hw => hcomm (hW hw)
  have hUfix : ∀ u ∈ U, α u = u := fun u hu =>
    fix_of_odd_aux α hm hαm (R₁ ⊓ R₂) (hR₁2.to_le inf_le_left) hWfix u (hU u hu)
  refine eq_one_of_fix_sup α _ _ (fun x hx => ?_) (fun x hx => ?_) hsup
  · refine fix_of_stab α hm hαm R₁ hR₁2 (fun r hr => hUfix r (hU₁ hr)) hc₁ x fun r hr => ?_
    exact (Subgroup.mem_normalizer_iff.mp hx r).mp hr
  · refine fix_of_stab α hm hαm R₂ hR₂2 (fun r hr => hUfix r (hU₂ hr)) hc₂ x fun r hr => ?_
    exact (Subgroup.mem_normalizer_iff.mp hx r).mp hr

theorem centralizes_of_perfect {G : Type*} [Group G] (K Zc : Subgroup G)
    (hperf : commutator ↥K = ⊤)
    (hZcen : ∀ z ∈ Zc, ∀ x ∈ K, z * x = x * z)
    (hZab : ∀ z ∈ Zc, ∀ z' ∈ Zc, z * z' = z' * z)
    (g : G) (hgZ : ∀ x ∈ K, x⁻¹ * g⁻¹ * x * g ∈ Zc) :
    ∀ x ∈ K, g * x = x * g := by
  let c : ↥K → G := fun x => (x : G)⁻¹ * g⁻¹ * x * g
  have hc : ∀ x, c x ∈ Zc := fun x => hgZ x x.2
  have hmul : ∀ x y : ↥K, c (x * y) = c x * c y := by
    intro x y
    have hcen : c x * (y : G)⁻¹ = (y : G)⁻¹ * c x :=
      (Commute.inv_right (show Commute (c x) (y : G) from hZcen _ (hc x) y y.2)).eq
    calc c (x * y) = ((y : G)⁻¹ * ((x : G)⁻¹ * g⁻¹ * x * g)) * (g⁻¹ * y * g) := by
          simp only [c, Subgroup.coe_mul]; group
      _ = (c x * (y : G)⁻¹) * (g⁻¹ * y * g) := by
          rw [hcen]
      _ = c x * c y := by simp only [c]; group
  have hone : c 1 = 1 := by simp [c]
  have hinv : ∀ x : ↥K, c x⁻¹ = (c x)⁻¹ := by
    intro x
    have h := hmul x x⁻¹
    rw [mul_inv_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  let S : Subgroup ↥K :=
    { carrier := {x | c x = 1}
      one_mem' := hone
      mul_mem' := fun {a b} ha hb => by
        show c (a * b) = 1
        rw [hmul]
        have ha' : c a = 1 := ha
        have hb' : c b = 1 := hb
        rw [ha', hb', one_mul]
      inv_mem' := fun {a} ha => by
        show c a⁻¹ = 1
        rw [hinv]
        have ha' : c a = 1 := ha
        rw [ha', inv_one] }
  have hS : commutator ↥K ≤ S := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    show c ⁅x, y⁆ = 1
    rw [commutatorElement_def, hmul, hmul, hmul, hinv, hinv]
    have := hZab _ (hc x) _ (hc y)
    calc c x * c y * (c x)⁻¹ * (c y)⁻¹ = (c y * c x) * (c x)⁻¹ * (c y)⁻¹ := by rw [this]
      _ = 1 := by group
  intro x hx
  have h1 : c ⟨x, hx⟩ = 1 := hS (hperf ▸ Subgroup.mem_top _)
  have h2 : x⁻¹ * g⁻¹ * x * g = 1 := h1
  calc g * x = g * x * (x⁻¹ * g⁻¹ * x * g) := by rw [h2, mul_one]
    _ = x * g := by group

section Pre

variable {G : Type} [Group G] {K : Subgroup G} {M : Type} [Group M] (π : ↥K →* M)

@[expose] def pre (Y : Subgroup M) : Subgroup G := (Y.comap π).map K.subtype

variable {π}

theorem mem_pre {Y : Subgroup M} {x : G} : x ∈ pre π Y ↔ ∃ h : x ∈ K, π ⟨x, h⟩ ∈ Y := by
  unfold pre
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨⟨x, h⟩, hy, rfl⟩

theorem pre_le_K (Y : Subgroup M) : pre π Y ≤ K := fun _ hx => (mem_pre.mp hx).1

theorem mem_pre_of_mem {Y : Subgroup M} (k : ↥K) (hk : π k ∈ Y) : (k : G) ∈ pre π Y :=
  mem_pre.mpr ⟨k.2, hk⟩

theorem pre_mono {Y Z : Subgroup M} (h : Y ≤ Z) : pre π Y ≤ pre π Z := by
  intro x hx
  obtain ⟨hxK, hxY⟩ := mem_pre.mp hx
  exact mem_pre.mpr ⟨hxK, h hxY⟩

theorem pre_inf (Y Z : Subgroup M) : pre π (Y ⊓ Z) = pre π Y ⊓ pre π Z := by
  ext x
  simp only [Subgroup.mem_inf, mem_pre]
  constructor
  · rintro ⟨h, hY, hZ⟩
    exact ⟨⟨h, hY⟩, ⟨h, hZ⟩⟩
  · rintro ⟨⟨h, hY⟩, ⟨_, hZ⟩⟩
    exact ⟨h, hY, hZ⟩

theorem pre_top : pre π (⊤ : Subgroup M) = K := by
  ext x
  rw [mem_pre]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, Subgroup.mem_top _⟩⟩

theorem pre_le_iff (hπ : Function.Surjective π) {Y Z : Subgroup M} :
    pre π Y ≤ pre π Z ↔ Y ≤ Z := by
  refine ⟨fun h m hm => ?_, pre_mono⟩
  obtain ⟨k, rfl⟩ := hπ m
  have h1 : (k : G) ∈ pre π Y := mem_pre_of_mem k hm
  obtain ⟨h2, h3⟩ := mem_pre.mp (h h1)
  exact h3

theorem pre_injective (hπ : Function.Surjective π) {Y Z : Subgroup M}
    (h : pre π Y = pre π Z) : Y = Z :=
  le_antisymm ((pre_le_iff hπ).mp h.le) ((pre_le_iff hπ).mp h.ge)

theorem pre_lt_iff (hπ : Function.Surjective π) {Y Z : Subgroup M} :
    pre π Y < pre π Z ↔ Y < Z := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, pre_le_iff hπ, pre_le_iff hπ]

theorem pre_sup (hπ : Function.Surjective π) (Y Z : Subgroup M) :
    pre π (Y ⊔ Z) = pre π Y ⊔ pre π Z := by
  have hr : ∀ W : Subgroup M, W ≤ π.range := fun W m _ => by
    obtain ⟨k, rfl⟩ := hπ m
    exact ⟨k, rfl⟩
  unfold pre
  rw [← Subgroup.map_sup, Subgroup.comap_sup_eq_of_le_range π (hr Y) (hr Z)]

theorem pre_normalizer (hπ : Function.Surjective π) (Y : Subgroup M) :
    pre π (Subgroup.normalizer (Y : Set M)) = K ⊓ Subgroup.normalizer (pre π Y : Set G) := by
  ext x
  rw [Subgroup.mem_inf, mem_pre]
  constructor
  · rintro ⟨hxK, hx⟩
    refine ⟨hxK, ?_⟩
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro g
    constructor
    · intro hg
      obtain ⟨hgK, hgY⟩ := mem_pre.mp hg
      have hK : x * g * x⁻¹ ∈ K := K.mul_mem (K.mul_mem hxK hgK) (K.inv_mem hxK)
      refine mem_pre.mpr ⟨hK, ?_⟩
      have := (hx (π ⟨g, hgK⟩)).mp hgY
      have e : (⟨x * g * x⁻¹, hK⟩ : ↥K) = ⟨x, hxK⟩ * ⟨g, hgK⟩ * ⟨x, hxK⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact this
    · intro hg
      obtain ⟨hgK, hgY⟩ := mem_pre.mp hg
      have hgK' : g ∈ K := by
        have := K.mul_mem (K.mul_mem (K.inv_mem hxK) hgK) hxK
        simpa [mul_assoc] using this
      refine mem_pre.mpr ⟨hgK', ?_⟩
      have h2 : π ⟨x * g * x⁻¹, hgK⟩ ∈ Y := hgY
      have h3 : π ⟨x, hxK⟩ * π ⟨g, hgK'⟩ * (π ⟨x, hxK⟩)⁻¹ ∈ Y := by
        have : (⟨x * g * x⁻¹, hgK⟩ : ↥K) = ⟨x, hxK⟩ * ⟨g, hgK'⟩ * ⟨x, hxK⟩⁻¹ := rfl
        rw [this, map_mul, map_mul, map_inv] at h2
        exact h2
      exact (hx _).mpr h3
  · rintro ⟨hxK, hx⟩
    refine ⟨hxK, ?_⟩
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    obtain ⟨k, rfl⟩ := hπ y
    have := hx (k : G)
    rw [mem_pre, mem_pre] at this
    constructor
    · intro hk
      have h1 : ∃ h : (k : G) ∈ K, π ⟨k, h⟩ ∈ Y := ⟨k.2, hk⟩
      obtain ⟨h2, h3⟩ := this.mp h1
      have : (⟨(x : G) * k * x⁻¹, h2⟩ : ↥K) = ⟨x, hxK⟩ * k * ⟨x, hxK⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv] at h3
      exact h3
    · intro hk
      obtain ⟨h2, h3⟩ := this.mpr ⟨K.mul_mem (K.mul_mem hxK k.2) (K.inv_mem hxK), by
        have : (⟨(x : G) * k * x⁻¹, K.mul_mem (K.mul_mem hxK k.2) (K.inv_mem hxK)⟩ : ↥K) =
            ⟨x, hxK⟩ * k * ⟨x, hxK⟩⁻¹ := rfl
        rw [this, map_mul, map_mul, map_inv]
        exact hk⟩
      exact h3

theorem isPGroup_pre (hker : IsPGroup 2 π.ker) {Y : Subgroup M} (hY : IsPGroup 2 Y) :
    IsPGroup 2 (pre π Y) := by
  rintro ⟨x, hx⟩
  obtain ⟨hxK, hxY⟩ := mem_pre.mp hx
  obtain ⟨a, ha⟩ := hY ⟨π ⟨x, hxK⟩, hxY⟩
  have ha' : (π ⟨x, hxK⟩) ^ (2 ^ a) = 1 := by simpa using congrArg Subtype.val ha
  have hmem : (⟨x, hxK⟩ : ↥K) ^ (2 ^ a) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact ha'
  obtain ⟨b, hb⟩ := hker ⟨_, hmem⟩
  refine ⟨a + b, ?_⟩
  apply Subtype.ext
  have hb' : ((⟨x, hxK⟩ : ↥K) ^ (2 ^ a)) ^ (2 ^ b) = 1 := by
    simpa using congrArg Subtype.val hb
  have := congrArg Subtype.val hb'
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
  simpa [pow_add, pow_mul] using this

theorem pCoreOf_pre [Finite G] [Finite M] (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (Q : Subgroup M) : pCoreOf 2 (pre π Q) = pre π (pCoreOf 2 Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  ·
    set V := pCoreOf 2 (pre π Q) with hV
    have hVle : V ≤ pre π Q := pCoreOf_le 2 _
    have hVnorm : pre π Q ≤ Subgroup.normalizer (V : Set G) := le_normalizer_pCoreOf 2 _
    have hV2 : IsPGroup 2 V := pCoreOf_isPGroup 2 _
    let Vb : Subgroup M := (V.subgroupOf K).map π
    have hVbQ : Vb ≤ Q := by
      rintro _ ⟨v, hv, rfl⟩
      exact (mem_pre.mp (hVle hv)).2
    have hVb2 : IsPGroup 2 Vb := by
      rintro ⟨_, v, hv, rfl⟩
      obtain ⟨k, hk⟩ := hV2 ⟨v, hv⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      have h1 : (v : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h2 : v ^ 2 ^ k = 1 := Subtype.ext h1
      simp [← map_pow, h2]
    have hQnorm : Q ≤ Subgroup.normalizer (Vb : Set M) := by
      intro q hq
      obtain ⟨k, rfl⟩ := hπ q
      have hkQ : (k : G) ∈ pre π Q := mem_pre_of_mem k hq
      have hk := (Subgroup.mem_normalizer_iff.mp (hVnorm hkQ))
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨k * v * k⁻¹, ?_, by simp⟩
        simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hv ⊢
        exact (hk v).mp hv
      · rintro ⟨v, hv, hvy⟩
        refine ⟨k⁻¹ * v * k, ?_, ?_⟩
        · simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hv ⊢
          have := (hk ((k : G)⁻¹ * v * k)).mpr
          apply this
          have e : (k : G) * ((k : G)⁻¹ * v * k) * (k : G)⁻¹ = v := by group
          rw [e]
          exact hv
        · have : π k * y * (π k)⁻¹ = π v := hvy.symm
          simp only [map_mul, map_inv]
          rw [← this]
          group
    have hVb := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVbQ hQnorm hVb2
    intro x hx
    have hxK : x ∈ K := pre_le_K _ (hVle hx)
    refine mem_pre.mpr ⟨hxK, hVb ⟨⟨x, hxK⟩, ?_, rfl⟩⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact hx
  ·
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (pre_mono (pCoreOf_le 2 Q)) ?_
      (isPGroup_pre hker (pCoreOf_isPGroup 2 Q))
    intro x hx
    obtain ⟨hxK, hxQ⟩ := mem_pre.mp hx
    have : x ∈ pre π (Subgroup.normalizer (pCoreOf 2 Q : Set M)) :=
      mem_pre.mpr ⟨hxK, le_normalizer_pCoreOf 2 Q hxQ⟩
    rw [pre_normalizer hπ] at this
    exact (Subgroup.mem_inf.mp this).2

end Pre

structure ModelData (M : Type) [Group M] (U R₁ R₂ : Subgroup M) : Prop where
  center_trivial : ∀ m : M, (∀ y : M, m * y = y * m) → m = 1
  sylow : IsSylowTwoOf U ⊤
  elem₁ : IsElemAbelian 2 R₁
  elem₂ : IsElemAbelian 2 R₂
  le₁ : R₁ ≤ U
  le₂ : R₂ ≤ U
  sup : R₁ ⊔ R₂ = U
  ne : R₁ ≠ R₂
  noncomm : ¬ R₂ ≤ Subgroup.centralizer (R₁ : Set M)
  inter_le_comm : R₁ ⊓ R₂ ≤ ⁅R₁, R₂⁆
  cent₁ : ∀ g : M, (∀ r ∈ R₁, g * r = r * g) → g ∈ R₁
  cent₂ : ∀ g : M, (∀ r ∈ R₂, g * r = r * g) → g ∈ R₂
  lt₁ : Subgroup.normalizer (U : Set M) < Subgroup.normalizer (R₁ : Set M)
  lt₂ : Subgroup.normalizer (U : Set M) < Subgroup.normalizer (R₂ : Set M)
  lt_top₁ : Subgroup.normalizer (R₁ : Set M) < ⊤
  lt_top₂ : Subgroup.normalizer (R₂ : Set M) < ⊤
  core₁ : pCoreOf 2 (Subgroup.normalizer (R₁ : Set M)) = R₁
  core₂ : pCoreOf 2 (Subgroup.normalizer (R₂ : Set M)) = R₂
  torus : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∃ P₀ : Subgroup M, IsElemAbelian p P₀ ∧ Nat.card P₀ = p ^ 2) ∧
    ∃ h ∈ Subgroup.normalizer (U : Set M), (∃ k : ℕ, orderOf h = p ^ k) ∧
      ¬ ⁅R₁, R₂⁆ ≤ Subgroup.centralizer ({h} : Set M)

theorem ModelData.symm {M : Type} [Group M] {U R₁ R₂ : Subgroup M} (h : ModelData M U R₁ R₂) :
    ModelData M U R₂ R₁ where
  center_trivial := h.center_trivial
  sylow := h.sylow
  elem₁ := h.elem₂
  elem₂ := h.elem₁
  le₁ := h.le₂
  le₂ := h.le₁
  sup := by rw [sup_comm]; exact h.sup
  ne := h.ne.symm
  noncomm := fun hc => h.noncomm fun r₂ hr₂ => Subgroup.mem_centralizer_iff.mpr fun r₁ hr₁ =>
    (Subgroup.mem_centralizer_iff.mp (hc hr₁) r₂ hr₂).symm
  inter_le_comm := by rw [inf_comm, Subgroup.commutator_comm]; exact h.inter_le_comm
  cent₁ := h.cent₂
  cent₂ := h.cent₁
  lt₁ := h.lt₂
  lt₂ := h.lt₁
  lt_top₁ := h.lt_top₂
  lt_top₂ := h.lt_top₁
  core₁ := h.core₂
  core₂ := h.core₁
  torus := by
    obtain ⟨p, hp, hp2, hP, hh, hhn, hhk, hhc⟩ := h.torus
    exact ⟨p, hp, hp2, hP, hh, hhn, hhk, by rw [Subgroup.commutator_comm]; exact hhc⟩

theorem exists_conj_sylow {M : Type} [Group M] [Finite M] {S U : Subgroup M} (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) :
    ∃ m : M, ∀ x : M, x ∈ U ↔ m⁻¹ * x * m ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 M := hS.toSylow hSi
  let U' : Sylow 2 M := hU.toSylow hUi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M S' U'
  refine ⟨g, fun x => ?_⟩
  have hU' : (U : Subgroup M) = MulAut.conj g • (S : Subgroup M) := by
    have h1 : ((g • S' : Sylow 2 M) : Subgroup M) = MulAut.conj g • (S' : Subgroup M) :=
      Sylow.coe_subgroup_smul
    rw [hg] at h1
    exact h1
  rw [hU', Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem center_le_ker {M : Type} [Group M] (hM : ∀ m : M, (∀ y, m * y = y * m) → m = 1)
    {X : Type} [Group X] (π : X →* M) (hπ : Function.Surjective π) (x : X)
    (hx : ∀ y : X, x * y = y * x) : π x = 1 := by
  apply hM
  intro y
  obtain ⟨y', rfl⟩ := hπ y
  rw [← map_mul, ← map_mul, hx]

theorem ker_central_of_quasisimple {X : Type} [Group X] (hq : CFSG.IsQuasisimple X) {M : Type}
    [Group M] [Nontrivial M] (π : X →* M) (hπ : Function.Surjective π)
    (hcen : ∀ x : X, (∀ y : X, x * y = y * x) → π x = 1) :
    ∀ x : X, π x = 1 → ∀ y : X, x * y = y * x := by
  let q : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hq' : Function.Surjective q := QuotientGroup.mk'_surjective _
  have : (π.ker.map q).Normal := Subgroup.Normal.map inferInstance q hq'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (self := hq.2.1) (π.ker.map q) with h | h
  · intro x hx y
    have : q x ∈ π.ker.map q := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    have hxc : x ∈ Subgroup.center X := (QuotientGroup.eq_one_iff x).mp this
    exact (Subgroup.mem_center_iff.mp hxc y).symm
  · exfalso
    have hall : ∀ x : X, π x = 1 := by
      intro x
      have : q x ∈ π.ker.map q := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := this
      have h1 : n⁻¹ * x ∈ Subgroup.center X := QuotientGroup.eq.mp hnx
      have h2 : π (n⁻¹ * x) = 1 := hcen _ fun y => (Subgroup.mem_center_iff.mp h1 y).symm
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn, inv_one, one_mul] at h2
      exact h2
    obtain ⟨a, b, hab⟩ := exists_pair_ne M
    obtain ⟨a', rfl⟩ := hπ a
    obtain ⟨b', rfl⟩ := hπ b
    exact hab (by rw [hall a', hall b'])

theorem conj_mem_sup {M : Type} [Group M] {A B : Subgroup M} {q : M}
    (hA : ∀ x ∈ A, q * x * q⁻¹ ∈ A) (hB : ∀ x ∈ B, q * x * q⁻¹ ∈ B) :
    ∀ x ∈ A ⊔ B, q * x * q⁻¹ ∈ A ⊔ B := by
  have h1 : A.map (MulAut.conj q).toMonoidHom ≤ A := by
    rintro _ ⟨y, hy, rfl⟩
    exact hA y hy
  have h2 : B.map (MulAut.conj q).toMonoidHom ≤ B := by
    rintro _ ⟨y, hy, rfl⟩
    exact hB y hy
  have h3 : (A ⊔ B).map (MulAut.conj q).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    exact sup_le_sup h1 h2
  intro x hx
  exact h3 ⟨x, hx, rfl⟩

theorem ModelData.ne_norm {M : Type} [Group M] {U R₁ R₂ : Subgroup M}
    (h : ModelData M U R₁ R₂) :
    Subgroup.normalizer (R₁ : Set M) ≠ Subgroup.normalizer (R₂ : Set M) := by
  intro heq
  have hle : Subgroup.normalizer (R₁ : Set M) ≤ Subgroup.normalizer (U : Set M) := by
    intro q hq
    have hq2 : q ∈ Subgroup.normalizer (R₂ : Set M) := heq ▸ hq
    have hqi : q⁻¹ ∈ Subgroup.normalizer (R₁ : Set M) := inv_mem hq
    have hq2i : q⁻¹ ∈ Subgroup.normalizer (R₂ : Set M) := inv_mem hq2
    have hfw : ∀ q : M, q ∈ Subgroup.normalizer (R₁ : Set M) → q ∈ Subgroup.normalizer (R₂ : Set M) →
        ∀ x ∈ U, q * x * q⁻¹ ∈ U := by
      intro q hq hq2 x hx
      rw [← h.sup] at hx ⊢
      exact conj_mem_sup (fun y hy => (Subgroup.mem_normalizer_iff.mp hq y).mp hy)
        (fun y hy => (Subgroup.mem_normalizer_iff.mp hq2 y).mp hy) x hx
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hfw q hq hq2 x, fun hx => ?_⟩
    have := hfw q⁻¹ hqi hq2i _ hx
    simpa [mul_assoc] using this
  exact absurd h.lt₁ (not_lt_of_ge hle)

@[expose] noncomputable def quotMap {G : Type} [Group G] (K : Subgroup G) {M : Type} [Group M]
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* M) : ↥K →* M :=
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))

theorem quotMap_surjective {G : Type} [Group G] (K : Subgroup G) {M : Type} [Group M]
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* M) : Function.Surjective (quotMap K e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem quotMap_eq_one_iff {G : Type} [Group G] (K : Subgroup G) {M : Type} [Group M]
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* M) (x : ↥K) :
    quotMap K e x = 1 ↔ x ∈ CFSG.pCore 2 ↥K := by
  simp only [quotMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
  rw [e.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem conj_eq_one_iff {M : Type} [Group M] (m a : M) : m * a * m⁻¹ = 1 ↔ a = 1 := by
  constructor
  · intro h
    have := congrArg (fun t => m⁻¹ * t * m) h
    simpa [mul_assoc] using this
  · intro h
    rw [h]
    simp

structure Red257 {G : Type} [Group G] (K P K₁ K₂ V V' : Subgroup G) {M : Type} [Group M]
    (π : ↥K →* M) (U R₁ R₂ : Subgroup M) : Prop where
  surj : Function.Surjective π
  ker_central : ∀ x : ↥K, π x = 1 → ∀ y : ↥K, x * y = y * x
  ker_two : IsPGroup 2 π.ker
  center_le : ∀ x : ↥K, (∀ y : ↥K, x * y = y * x) → π x = 1
  hP : P = pre π U
  hK₁ : K₁ = pre π (Subgroup.normalizer (R₁ : Set M))
  hK₂ : K₂ = pre π (Subgroup.normalizer (R₂ : Set M))
  hV : V = pre π R₁
  hV' : V' = pre π R₂

theorem reduce257 {G : Type} [Group G] [Finite G] {K P K₁ K₂ V V' : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) {M : Type} [Group M] [Finite M] {U R₁ R₂ : Subgroup M}
    (hM : ModelData M U R₁ R₂) (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* M)
    (hpair : IsParabolicPair257 K P K₁ K₂) (hV : V = pCoreOf 2 K₁) (hV' : V' = pCoreOf 2 K₂) :
    ∃ (π : ↥K →* M) (R₁' R₂' : Subgroup M),
      ((R₁' = R₁ ∧ R₂' = R₂) ∨ (R₁' = R₂ ∧ R₂' = R₁)) ∧ Red257 K P K₁ K₂ V V' π U R₁' R₂' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial M := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hM.ne (Subgroup.ext fun x => by simp [Subsingleton.elim x 1])
  set π₀ := quotMap K e with hπ₀def
  have hπ₀ : Function.Surjective π₀ := quotMap_surjective K e
  have hker0 : ∀ x, π₀ x = 1 ↔ x ∈ CFSG.pCore 2 ↥K := quotMap_eq_one_iff K e
  have hcen : ∀ x : ↥K, (∀ y, x * y = y * x) → π₀ x = 1 := fun x hx =>
    center_le_ker hM.center_trivial π₀ hπ₀ x hx
  have hkc : ∀ x : ↥K, π₀ x = 1 → ∀ y, x * y = y * x :=
    ker_central_of_quasisimple hq π₀ hπ₀ hcen
  have hk2 : IsPGroup 2 π₀.ker := by
    have : π₀.ker = CFSG.pCore 2 ↥K := by
      ext x
      exact hker0 x
    rw [this]
    exact CFSG.pCore_isPGroup
  set P' := P.subgroupOf K with hP'def
  have hkerP : ∀ x : ↥K, π₀ x = 1 → x ∈ P' := by
    intro x hx
    have hx' : x ∈ CFSG.pCore 2 ↥K := (hker0 x).mp hx
    have h1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx', rfl⟩
    exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf hpair.sylow h1
  have hP2 : IsPGroup 2 P' := hpair.sylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hpair.sylow.1).symm
  set S := P'.map π₀ with hSdef
  have hPS : P' = S.comap π₀ := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨p, hp, hpx⟩
      have h1 : π₀ (p⁻¹ * x) = 1 := by rw [map_mul, map_inv, hpx, inv_mul_cancel]
      have h2 : p⁻¹ * x ∈ P' := hkerP _ h1
      have h3 : p * (p⁻¹ * x) ∈ P' := P'.mul_mem hp h2
      simpa using h3
  have hSp : IsPGroup 2 S := hP2.map π₀
  have hSi : ¬ 2 ∣ S.index := by
    rw [← Subgroup.index_comap_of_surjective S hπ₀, ← hPS]
    exact hpair.sylow.2.2
  have hUi : ¬ 2 ∣ U.index := by
    have := hM.sylow.2.2
    change ¬ 2 ∣ U.relIndex ⊤ at this
    rwa [Subgroup.relIndex_top_right] at this
  obtain ⟨m, hm⟩ := exists_conj_sylow hSp hSi hM.sylow.2.1 hUi
  set π : ↥K →* M := (MulAut.conj m).toMonoidHom.comp π₀ with hπdef
  have hπx : ∀ x : ↥K, π x = m * π₀ x * m⁻¹ := fun x => rfl
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨x, hx⟩ := hπ₀ (m⁻¹ * y * m)
    exact ⟨x, by rw [hπx, hx]; group⟩
  have hπ1 : ∀ x : ↥K, π x = 1 ↔ π₀ x = 1 := fun x => by
    rw [hπx]
    exact conj_eq_one_iff m _
  have hkerπ : π.ker = π₀.ker := by
    ext x
    simp only [MonoidHom.mem_ker]
    exact hπ1 x
  have hπU : ∀ x : ↥K, π x ∈ U ↔ (x : G) ∈ P := by
    intro x
    rw [hm, hπx]
    have e : m⁻¹ * (m * π₀ x * m⁻¹) * m = π₀ x := by group
    rw [e]
    have h1 : π₀ x ∈ S ↔ x ∈ P' := by
      rw [hPS]
      rfl
    rw [h1, hP'def, Subgroup.mem_subgroupOf]
  have hP : P = pre π U := by
    ext x
    rw [mem_pre]
    constructor
    · intro hx
      exact ⟨hpair.sylow.1 hx, (hπU ⟨x, hpair.sylow.1 hx⟩).mpr hx⟩
    · rintro ⟨h, hU⟩
      exact (hπU ⟨x, h⟩).mp hU
  have hker2 : IsPGroup 2 π.ker := hkerπ ▸ hk2
  have hB : K ⊓ Subgroup.normalizer (P : Set G) = pre π (Subgroup.normalizer (U : Set M)) := by
    rw [pre_normalizer hπ, ← hP]
  have hX₁ : (K ⊓ Subgroup.normalizer (P : Set G)) < pre π (Subgroup.normalizer (R₁ : Set M)) := by
    rw [hB]
    exact (pre_lt_iff hπ).mpr hM.lt₁
  have hX₂ : (K ⊓ Subgroup.normalizer (P : Set G)) < pre π (Subgroup.normalizer (R₂ : Set M)) := by
    rw [hB]
    exact (pre_lt_iff hπ).mpr hM.lt₂
  have hX₁K : pre π (Subgroup.normalizer (R₁ : Set M)) < K := by
    have := (pre_lt_iff hπ).mpr hM.lt_top₁
    rwa [pre_top] at this
  have hX₂K : pre π (Subgroup.normalizer (R₂ : Set M)) < K := by
    have := (pre_lt_iff hπ).mpr hM.lt_top₂
    rwa [pre_top] at this
  have hne : pre π (Subgroup.normalizer (R₁ : Set M)) ≠ pre π (Subgroup.normalizer (R₂ : Set M)) :=
    fun h => hM.ne_norm (pre_injective hπ h)
  have hcoreV : ∀ R : Subgroup M, pCoreOf 2 (Subgroup.normalizer (R : Set M)) = R →
      pCoreOf 2 (pre π (Subgroup.normalizer (R : Set M))) = pre π R := fun R hR => by
    rw [pCoreOf_pre hπ hker2 _, hR]
  have hker_c : ∀ x : ↥K, π x = 1 → ∀ y : ↥K, x * y = y * x := fun x hx => hkc x ((hπ1 x).mp hx)
  have hcen' : ∀ x : ↥K, (∀ y : ↥K, x * y = y * x) → π x = 1 := fun x hx => (hπ1 x).mpr (hcen x hx)
  rcases hpair.only _ hX₁ hX₁K with h1 | h1 <;> rcases hpair.only _ hX₂ hX₂K with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · refine ⟨π, R₁, R₂, Or.inl ⟨rfl, rfl⟩, ?_⟩
    exact { surj := hπ, ker_central := hker_c, ker_two := hker2, center_le := hcen', hP := hP,
            hK₁ := h1.symm, hK₂ := h2.symm,
            hV := by rw [hV, ← h1, hcoreV R₁ hM.core₁],
            hV' := by rw [hV', ← h2, hcoreV R₂ hM.core₂] }
  · refine ⟨π, R₂, R₁, Or.inr ⟨rfl, rfl⟩, ?_⟩
    exact { surj := hπ, ker_central := hker_c, ker_two := hker2, center_le := hcen', hP := hP,
            hK₁ := h2.symm, hK₂ := h1.symm,
            hV := by rw [hV, ← h2, hcoreV R₂ hM.core₂],
            hV' := by rw [hV', ← h1, hcoreV R₁ hM.core₁] }
  · exact absurd (h1.trans h2.symm) hne

noncomputable def inducedAut {X M : Type*} [Group X] [Group M] (π : X →* M)
    (hπ : Function.Surjective π) (β : X ≃* X) (hβ : π.ker.map β.toMonoidHom = π.ker) : M ≃* M :=
  (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    ((QuotientGroup.congr π.ker π.ker β hβ).trans (QuotientGroup.quotientKerEquivOfSurjective π hπ))

theorem inducedAut_apply {X M : Type*} [Group X] [Group M] (π : X →* M)
    (hπ : Function.Surjective π) (β : X ≃* X) (hβ : π.ker.map β.toMonoidHom = π.ker) (x : X) :
    inducedAut π hπ β hβ (π x) = π (β x) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π x) = (x : X ⧸ π.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [inducedAut, MulEquiv.trans_apply, h1]
  rfl


theorem pow_mod_eq {G : Type*} [Group G] {a : G} {p : ℕ} (ha : a ^ p = 1) (i : ℕ) :
    a ^ i = a ^ (i % p) := by
  conv_lhs => rw [← Nat.mod_add_div i p, pow_add, pow_mul, ha, one_pow, mul_one]

theorem exists_elemAbelian_pair {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {a b : G}
    (hab : a * b = b * a) (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hind : ∀ i j : ℕ, a ^ i * b ^ j = 1 → p ∣ i ∧ p ∣ j) :
    ∃ P₀ : Subgroup G, IsElemAbelian p P₀ ∧ Nat.card P₀ = p ^ 2 ∧ a ∈ P₀ ∧ b ∈ P₀ := by
  have hp0 : 0 < p := hp.pos
  have h1p : 1 ≤ p := hp0
  have hcomm : ∀ i j : ℕ, a ^ i * b ^ j = b ^ j * a ^ i := fun i j =>
    ((Commute.pow_pow (show Commute a b from hab) i j)).eq
  have hmulc : ∀ i j k l : ℕ, (a ^ i * b ^ j) * (a ^ k * b ^ l) = a ^ (i + k) * b ^ (j + l) := by
    intro i j k l
    calc (a ^ i * b ^ j) * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by group
      _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [← hcomm k j]
      _ = a ^ (i + k) * b ^ (j + l) := by rw [pow_add, pow_add]; group
  have hinvab : ∀ i j : ℕ, (a ^ i * b ^ j) * (a ^ ((p - 1) * i) * b ^ ((p - 1) * j)) = 1 := by
    intro i j
    rw [hmulc]
    have e1 : i + (p - 1) * i = p * i := by zify [h1p]; ring
    have e2 : j + (p - 1) * j = p * j := by zify [h1p]; ring
    rw [e1, e2, pow_mul, pow_mul, ha, hb]
    simp
  let P : Subgroup G :=
    { carrier := {g | ∃ i j : ℕ, g = a ^ i * b ^ j}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        exact ⟨i + k, j + l, hmulc i j k l⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        exact ⟨(p - 1) * i, (p - 1) * j, inv_eq_of_mul_eq_one_right (hinvab i j)⟩ }
  refine ⟨P, ⟨?_, ?_⟩, ?_, ⟨1, 0, by simp⟩, ⟨0, 1, by simp⟩⟩
  · refine isMulCommutative_iff_of_setLike.mpr ?_
    rintro _ ⟨i, j, rfl⟩ _ ⟨k, l, rfl⟩
    rw [hmulc, hmulc, add_comm i k, add_comm j l]
  · rintro _ ⟨i, j, rfl⟩
    show (a ^ i * b ^ j) ^ p = 1
    have hai : (a ^ i) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]
    have hbj : (b ^ j) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hb, one_pow]
    rw [Commute.mul_pow (show Commute (a ^ i) (b ^ j) from hcomm i j), hai, hbj, one_mul]
  · let f : Fin p × Fin p → P := fun x => ⟨a ^ (x.1 : ℕ) * b ^ (x.2 : ℕ), x.1, x.2, rfl⟩
    have hmodeq : ∀ x y : ℕ, x < p → y < p → p ∣ x + (p - 1) * y → x = y := by
      intro x y hx hy h
      have h0 : ((x + (p - 1) * y : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact h
      have : NeZero p := ⟨hp0.ne'⟩
      have : (x : ZMod p) = y := by
        push_cast [Nat.cast_sub h1p, ZMod.natCast_self] at h0
        linear_combination h0
      have := (ZMod.natCast_eq_natCast_iff' x y p).mp this
      rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
    have hinj : Function.Injective f := by
      intro x y hxy
      have h : a ^ (x.1 : ℕ) * b ^ (x.2 : ℕ) = a ^ (y.1 : ℕ) * b ^ (y.2 : ℕ) :=
        congrArg Subtype.val hxy
      have h2 := congrArg (fun g => g * (a ^ ((p - 1) * (y.1 : ℕ)) * b ^ ((p - 1) * (y.2 : ℕ)))) h
      rw [hmulc, hinvab] at h2
      obtain ⟨hd1, hd2⟩ := hind _ _ h2
      exact Prod.ext (Fin.ext (hmodeq _ _ x.1.2 y.1.2 hd1)) (Fin.ext (hmodeq _ _ x.2.2 y.2.2 hd2))
    have hsurj : Function.Surjective f := by
      rintro ⟨_, i, j, rfl⟩
      refine ⟨(⟨i % p, Nat.mod_lt _ hp0⟩, ⟨j % p, Nat.mod_lt _ hp0⟩), ?_⟩
      apply Subtype.ext
      show a ^ (i % p) * b ^ (j % p) = a ^ i * b ^ j
      rw [← pow_mod_eq ha, ← pow_mod_eq hb]
    have := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
    rw [← this, Nat.card_prod, Nat.card_fin, sq]


theorem isSylowTwoOf_of_le {M : Type} [Group M] {U N : Subgroup M} (hU : IsSylowTwoOf U ⊤)
    (hUN : U ≤ N) : IsSylowTwoOf U N := by
  refine ⟨hUN, hU.2.1, ?_⟩
  have h1 := hU.2.2
  change ¬ 2 ∣ U.relIndex ⊤ at h1
  rw [Subgroup.relIndex_top_right] at h1
  have h2 := Subgroup.relIndex_mul_index hUN
  exact fun h => h1 (h.trans (Dvd.intro _ h2))

theorem exists_odd_pow_mem {M : Type} [Group M] [Finite M] {U : Subgroup M}
    (hU : IsSylowTwoOf U ⊤) (g : M) (hg : g ∈ Subgroup.normalizer (U : Set M)) :
    ∃ r : ℕ, Odd r ∧ g ^ r ∈ U := by
  set N := Subgroup.normalizer (U : Set M) with hN
  have hUN : U ≤ N := Subgroup.le_normalizer
  have hS := isSylowTwoOf_of_le hU hUN
  have : (U.subgroupOf N).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp g.2 n).mp hn⟩
  set r := Nat.card (N ⧸ U.subgroupOf N) with hr
  refine ⟨r, ?_, ?_⟩
  · have h := hS.2.2
    change ¬ 2 ∣ (U.subgroupOf N).index at h
    have : r = (U.subgroupOf N).index := rfl
    rw [this]
    exact Nat.not_even_iff_odd.mp (fun he => h (even_iff_two_dvd.mp he))
  · have h1 : ((⟨g, hg⟩ : N) : N ⧸ U.subgroupOf N) ^ r = 1 := pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact h1

@[expose] def ConjTo {M : Type} [Group M] (g : M) (A B : Subgroup M) : Prop :=
  ∀ x, x ∈ A ↔ g * x * g⁻¹ ∈ B

theorem ConjTo.trans {M : Type} [Group M] {g h : M} {A B C : Subgroup M} (h1 : ConjTo g A B)
    (h2 : ConjTo h B C) : ConjTo (h * g) A C := fun x => by
  rw [h1 x, h2]
  have : h * g * x * (h * g)⁻¹ = h * (g * x * g⁻¹) * h⁻¹ := by group
  rw [this]

theorem ConjTo.of_mem_normalizer {M : Type} [Group M] {g : M} {A : Subgroup M}
    (hg : g ∈ Subgroup.normalizer (A : Set M)) : ConjTo g A A := fun x =>
  Subgroup.mem_normalizer_iff.mp hg x

theorem ConjTo.unique_right {M : Type} [Group M] {g : M} {A B B' : Subgroup M} (h : ConjTo g A B)
    (h' : ConjTo g A B') : B = B' := by
  have key : ∀ {C D : Subgroup M}, ConjTo g A C → ConjTo g A D → ∀ y, y ∈ C → y ∈ D := by
    intro C D hC hD y hy
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    have hA : g⁻¹ * y * g ∈ A := by
      rw [hC, e]
      exact hy
    have := (hD _).mp hA
    rwa [e] at this
  ext y
  exact ⟨key h h' y, key h' h y⟩

theorem ConjTo.unique_left {M : Type} [Group M] {g : M} {A A' B : Subgroup M} (h : ConjTo g A B)
    (h' : ConjTo g A' B) : A = A' := by
  ext x
  rw [h x, h' x]

theorem fixes_of_odd {M : Type} [Group M] [Finite M] {U A₁ A₂ : Subgroup M}
    (hU : IsSylowTwoOf U ⊤) (hn₁ : U ≤ Subgroup.normalizer (A₁ : Set M)) (hne : A₁ ≠ A₂)
    (h₁ : ∀ g ∈ Subgroup.normalizer (U : Set M), ConjTo g A₁ A₁ ∨ ConjTo g A₁ A₂)
    (h₂ : ∀ g ∈ Subgroup.normalizer (U : Set M), ConjTo g A₂ A₁ ∨ ConjTo g A₂ A₂) :
    ∀ g ∈ Subgroup.normalizer (U : Set M), ConjTo g A₁ A₁ ∧ ConjTo g A₂ A₂ := by
  intro g hg
  have hswap : ¬ ConjTo g A₁ A₂ := by
    intro h
    have h21 : ConjTo g A₂ A₁ := by
      rcases h₂ g hg with h' | h'
      · exact h'
      · exact absurd (h.unique_left h') hne
    have key : ∀ k : ℕ, (Even k ∧ ConjTo (g ^ k) A₁ A₁) ∨ (Odd k ∧ ConjTo (g ^ k) A₁ A₂) := by
      intro k
      induction k with
      | zero => exact Or.inl ⟨⟨0, rfl⟩, fun x => by simp⟩
      | succ k ih =>
        rcases ih with ⟨hk, hc⟩ | ⟨hk, hc⟩
        · exact Or.inr ⟨hk.add_one, by rw [pow_succ']; exact hc.trans h⟩
        · exact Or.inl ⟨hk.add_one, by rw [pow_succ']; exact hc.trans h21⟩
    obtain ⟨r, hr, hgr⟩ := exists_odd_pow_mem hU g hg
    rcases key r with ⟨he, -⟩ | ⟨-, hc⟩
    · exact (Nat.not_even_iff_odd.mpr hr) he
    · exact hne (ConjTo.unique_right (ConjTo.of_mem_normalizer (hn₁ hgr)) hc)
  have hfix : ConjTo g A₁ A₁ := (h₁ g hg).resolve_right hswap
  refine ⟨hfix, ?_⟩
  rcases h₂ g hg with h | h
  · exact absurd (h.unique_left hfix) hne.symm
  · exact h


theorem mem_normalizer_of_conj {G : Type*} [Group G] (H : Subgroup G) {g : G}
    (h : ∀ v ∈ H, g * v * g⁻¹ ∈ H) (h' : ∀ v ∈ H, g⁻¹ * v * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨h v, fun hv => ?_⟩
  have := h' _ hv
  simpa [mul_assoc] using this

end CFSG.QuasithinUnique.Fin257
