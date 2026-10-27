module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannS3
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.Section2.CoprimeTools

public section

namespace GL83

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin
  CFSG.Quasithin.F53Push CFSG.LieType.BorelTits
open scoped commutatorElement

namespace I28_3S3

variable {G : Type} [Group G]

theorem perm3_sq_exists_pow (δ τ : Equiv.Perm (Fin 3)) (hδ3 : δ ^ 3 = 1) (hδ1 : δ ≠ 1) :
    ∃ j : Fin 3, τ * τ = δ ^ (j : ℕ) := by
  revert δ τ; decide

theorem sl2_zmod2_fixed_zero : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), A ^ 3 = 1 →
    A ≠ 1 → ∀ v : Fin 2 → ZMod 2, (A : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec v = v → v = 0 := by
  decide +kernel

theorem conj_mem_centralizer_of_mem_normalizer {S : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (hc : c ∈ Subgroup.centralizer (S : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
  have key := hc _ hs'
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * s := by group

section Quotient

variable {X : Subgroup G}

theorem exists_order_three_mem (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {C : Subgroup G}
    (hCX : C ≤ X) (hCn : ∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ ∈ C) {g : G} (hgC : g ∈ C)
    (hg : toS3 e ⟨g, hCX hgC⟩ ≠ 1) :
    ∃ d ∈ C, ∃ hd : d ∈ X, toS3 e ⟨d, hd⟩ ^ 3 = 1 ∧ toS3 e ⟨d, hd⟩ ≠ 1 := by
  by_cases h3 : toS3 e ⟨g, hCX hgC⟩ ^ 3 = 1
  · exact ⟨g, hgC, hCX hgC, h3, hg⟩
  · have ht : toS3 e ⟨g, hCX hgC⟩ * toS3 e ⟨g, hCX hgC⟩ = 1 :=
      perm3_involution_of_pow_three_ne _ h3
    obtain ⟨c, hc⟩ := toS3_surjective e cyc3
    have hg' : (c : G) * g * (c : G)⁻¹ ∈ C := hCn _ c.2 g hgC
    have hg'X : (c : G) * g * (c : G)⁻¹ ∈ X := hCX hg'
    have hθ : toS3 e ⟨(c : G) * g * (c : G)⁻¹, hg'X⟩ =
        cyc3 * toS3 e ⟨g, hCX hgC⟩ * cyc3⁻¹ := by
      rw [← hc, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hne : toS3 e ⟨(c : G) * g * (c : G)⁻¹, hg'X⟩ ≠ toS3 e ⟨g, hCX hgC⟩ := by
      rw [hθ]
      exact perm3_conj_ne _ _ ht hg cyc3_pow_three cyc3_ne_one
    have ht1' : toS3 e ⟨(c : G) * g * (c : G)⁻¹, hg'X⟩ ≠ 1 := by
      intro h1
      apply hg
      rw [hθ] at h1
      have := congrArg (fun a => cyc3⁻¹ * a * cyc3) h1
      simpa [mul_assoc] using this
    have ht' : toS3 e ⟨(c : G) * g * (c : G)⁻¹, hg'X⟩ * toS3 e ⟨(c : G) * g * (c : G)⁻¹, hg'X⟩
        = 1 := by
      rw [hθ]
      have : cyc3 * toS3 e ⟨g, hCX hgC⟩ * cyc3⁻¹ * (cyc3 * toS3 e ⟨g, hCX hgC⟩ * cyc3⁻¹) =
          cyc3 * (toS3 e ⟨g, hCX hgC⟩ * toS3 e ⟨g, hCX hgC⟩) * cyc3⁻¹ := by group
      rw [this, ht]
      group
    obtain ⟨h3', hne3⟩ := perm3_prod_order_three ht ht' hg ht1' hne.symm
    refine ⟨g * ((c : G) * g * (c : G)⁻¹), C.mul_mem hgC hg', X.mul_mem (hCX hgC) hg'X, ?_, ?_⟩
    · have : (⟨g * ((c : G) * g * (c : G)⁻¹), X.mul_mem (hCX hgC) hg'X⟩ : ↥X) =
          ⟨g, hCX hgC⟩ * ⟨(c : G) * g * (c : G)⁻¹, hg'X⟩ := rfl
      rw [this, map_mul]
      exact h3'
    · have : (⟨g * ((c : G) * g * (c : G)⁻¹), X.mul_mem (hCX hgC) hg'X⟩ : ↥X) =
          ⟨g, hCX hgC⟩ * ⟨(c : G) * g * (c : G)⁻¹, hg'X⟩ := rfl
      rw [this, map_mul]
      exact hne3

theorem sq_mem_of_order_three (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {C : Subgroup G}
    (hRC : pCoreOf 2 X ≤ C) {d : G} (hdC : d ∈ C) (hdX : d ∈ X)
    (hd3 : toS3 e ⟨d, hdX⟩ ^ 3 = 1) (hd1 : toS3 e ⟨d, hdX⟩ ≠ 1) {x : G} (hx : x ∈ X) :
    x ^ 2 ∈ C := by
  obtain ⟨j, hj⟩ := perm3_sq_exists_pow (toS3 e ⟨d, hdX⟩) (toS3 e ⟨x, hx⟩) hd3 hd1
  have hyX : x ^ 2 * (d ^ (j : ℕ))⁻¹ ∈ X :=
    X.mul_mem (X.pow_mem hx 2) (X.inv_mem (X.pow_mem hdX _))
  have hy : x ^ 2 * (d ^ (j : ℕ))⁻¹ ∈ pCoreOf 2 X := by
    rw [← toS3_eq_one_iff e hyX]
    have : (⟨x ^ 2 * (d ^ (j : ℕ))⁻¹, hyX⟩ : ↥X) = ⟨x, hx⟩ ^ 2 * (⟨d, hdX⟩ ^ (j : ℕ))⁻¹ := rfl
    rw [this, map_mul, map_inv, map_pow, map_pow, pow_two, hj]
    simp
  have := C.mul_mem (hRC hy) (C.pow_mem hdC (j : ℕ))
  simpa using this

variable [Finite G]

theorem sylow_ne_bot {T : Subgroup G} (hT : IsSylowTwoOf T X)
    (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) : T ≠ ⊥ := by
  intro hT0
  have hRT : pCoreOf 2 X ≤ T := pCoreOf_le_of_isSylowTwoOf hT
  have hR0 : pCoreOf 2 X = ⊥ := le_bot_iff.mp (hT0 ▸ hRT)
  have h6 := relIndex_core_eq_six e
  rw [hR0] at h6
  apply hT.2.2
  rw [hT0]
  show 2 ∣ (⊥ : Subgroup G).relIndex X
  rw [h6]
  norm_num

theorem centralizer_conjClosure_le {T : Subgroup G} (hT : IsSylowTwoOf T X) (hF : CharTwo X)
    (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) (hnc : NoCharNormal T X) :
    X ⊓ Subgroup.centralizer (conjClosure (omegaOneCenterOf T) X : Set G) ≤ pCoreOf 2 X := by
  obtain ⟨hVle, hVel, hVred⟩ :=
    conjClosure_isTwoReducedIn_of_charTwo hT hF (Z := omegaOneCenterOf T) le_rfl
  set V := conjClosure (omegaOneCenterOf T) X with hV
  intro g hg
  by_contra hgR
  have hgX : g ∈ X := hg.1
  have hg1 : toS3 e ⟨g, hgX⟩ ≠ 1 := fun h => hgR ((toS3_eq_one_iff e hgX).mp h)
  have hCn : ∀ x ∈ X, ∀ c ∈ X ⊓ Subgroup.centralizer (V : Set G),
      x * c * x⁻¹ ∈ X ⊓ Subgroup.centralizer (V : Set G) := fun x hx c hc =>
    ⟨X.mul_mem (X.mul_mem hx hc.1) (X.inv_mem hx),
      conj_mem_centralizer_of_mem_normalizer (hVred.2.1 hx) hc.2⟩
  obtain ⟨d, hdC, hdX, hd3, hd1⟩ := exists_order_three_mem e (C := X ⊓ Subgroup.centralizer
    (V : Set G)) inf_le_left hCn hg hg1
  have hRC : pCoreOf 2 X ≤ X ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (pCoreOf_le 2 X) (Subgroup.le_centralizer_iff.mp (hVle.trans inf_le_right))
  have hD : X ≤ Subgroup.centralizer (V : Set G) := by
    refine hVred.2.2.2 X le_rfl Subgroup.le_normalizer (fun x hx => ⟨1, ?_⟩)
    have := (sq_mem_of_order_three e hRC hdC hdX hd3 hd1 hx).2
    simpa using this
  have hZ1V : omegaOneCenterOf T ≤ V := le_conjClosure _ _
  have hXnorm : X ≤ Subgroup.normalizer ((omegaOneCenterOf T : Subgroup G) : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hZ1V (hD hx))
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  exact hnc (omegaOneCenterOf T) (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le T)
    (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hT2 (sylow_ne_bot hT e))
    (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T) hXnorm

theorem pushHyp_conjClosure {T : Subgroup G} (hT : IsSylowTwoOf T X) (hF : CharTwo X)
    (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) (hnc : NoCharNormal T X) :
    PushHyp X T (conjClosure (omegaOneCenterOf T) X) := by
  obtain ⟨hVle, hVel, hVred⟩ :=
    conjClosure_isTwoReducedIn_of_charTwo hT hF (Z := omegaOneCenterOf T) le_rfl
  refine ⟨hT, hVred.2.1, hVel, hVle.trans inf_le_left, le_antisymm ?_ ?_⟩
  · exact centralizer_conjClosure_le hT hF e hnc
  · exact le_inf (pCoreOf_le 2 X) (Subgroup.le_centralizer_iff.mp (hVle.trans inf_le_right))

theorem mem_pResidualOf_of_pow_three {x : G} (hx : x ∈ X) (hx3 : x ^ 3 = 1) :
    x ∈ pResidualOf 2 X := by
  obtain ⟨k, hk⟩ := exists_pow_mem_pResidualOf X hx
  have h4 : ∀ m : ℕ, x ^ (4 ^ m) = x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_mul, ih, show (4 : ℕ) = 1 + 3 from rfl, pow_add, hx3, pow_one, mul_one]
  have : x = (x ^ 2 ^ k) ^ 2 ^ k := by
    rw [← pow_mul, ← mul_pow, show (2 : ℕ) * 2 = 4 from rfl]
    exact (h4 k).symm
  rw [this]
  exact (pResidualOf 2 X).pow_mem hk _

omit [Finite G] in
theorem card_commutator_mul_card_centralizer {V : Subgroup G} {u : G}
    (hVel : IsElemAbelian 2 V) (huV : u ∈ Subgroup.normalizer (V : Set G)) (hu3 : u ^ 3 = 1) :
    Nat.card (⁅V, Subgroup.zpowers u⁆ : Subgroup G) *
      Nat.card (V ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = Nat.card V := by
  classical
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hVel.1
    exact setLike_mul_comm (s := V) ha hb
  have hsq : ∀ a ∈ V, a * a = 1 := fun a ha => by rw [← pow_two]; exact hVel.2 a ha
  have hconj : ∀ a ∈ V, u * a * u⁻¹ ∈ V := fun a ha => (Subgroup.mem_normalizer_iff.mp huV a).mp ha
  let f : ↥V →* ↥V :=
    { toFun := fun x => ⟨x * (u * x * u⁻¹), V.mul_mem x.2 (hconj x x.2)⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have h1 := hcomm y y.2 (u * x * u⁻¹) (hconj x x.2)
        simp only [Subgroup.coe_mul]
        calc (x * y : G) * (u * (x * y) * u⁻¹)
            = x * y * ((u * x * u⁻¹) * (u * y * u⁻¹)) := by group
          _ = x * (y * (u * x * u⁻¹)) * (u * y * u⁻¹) := by group
          _ = x * ((u * x * u⁻¹) * y) * (u * y * u⁻¹) := by rw [h1]
          _ = (x * (u * x * u⁻¹)) * (y * (u * y * u⁻¹)) := by group }
  have hf : ∀ x : ↥V, ((f x : ↥V) : G) = (x : G) * (u * x * u⁻¹) := fun x => rfl
  have hxinv : ∀ a ∈ V, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hsq a ha)
  have hconj_inv : ∀ a ∈ V, (u * a * u⁻¹)⁻¹ = u * a * u⁻¹ := fun a ha =>
    hxinv _ (hconj a ha)
  have hcomm_u : ∀ a ∈ V, ⁅a, u⁆ = a * (u * a * u⁻¹) := fun a ha => by
    have h1 : (u * a * u⁻¹)⁻¹ = u * a⁻¹ * u⁻¹ := by group
    rw [commutatorElement_def]
    calc a * u * a⁻¹ * u⁻¹ = a * (u * a⁻¹ * u⁻¹) := by group
      _ = a * (u * a * u⁻¹) := by rw [← h1, hconj_inv a ha]
  have hker : f.ker.map V.subtype = V ⊓ Subgroup.centralizer ({u} : Set G) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : (x : G) * (u * x * u⁻¹) = 1 := congrArg Subtype.val hx
      have hux : u * x * u⁻¹ = x := by
        have : u * x * u⁻¹ = (x : G)⁻¹ := (eq_inv_of_mul_eq_one_right hx1)
        rw [this]
        exact hxinv x x.2
      refine Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (x : G) * u = (u * x * u⁻¹) * u := by rw [hux]
        _ = u * x := by group
    · intro hz
      obtain ⟨hzV, hzc⟩ := Subgroup.mem_inf.mp hz
      have hzc := Subgroup.mem_centralizer_singleton_iff.mp hzc
      refine ⟨⟨z, hzV⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      ext
      rw [hf]
      have : u * z * u⁻¹ = z := by
        calc u * z * u⁻¹ = (z * u) * u⁻¹ := by rw [← hzc]
          _ = z := by group
      show z * (u * z * u⁻¹) = 1
      rw [this]
      exact hsq z hzV
  have hrange : f.range.map V.subtype = ⁅V, Subgroup.zpowers u⁆ := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      show ((f x : ↥V) : G) ∈ _
      rw [hf, ← hcomm_u x x.2]
      exact Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_zpowers u)
    · rw [Subgroup.commutator_le]
      intro x hx w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      obtain ⟨q, m, hm0, hm3, hkq⟩ : ∃ q m : ℤ, 0 ≤ m ∧ m < 3 ∧ k = 3 * q + m :=
        ⟨k / 3, k % 3, by omega, by omega, by omega⟩
      have hk : u ^ k = u ^ m := by
        rw [hkq, zpow_add, zpow_mul]
        have : u ^ (3 : ℤ) = 1 := by exact_mod_cast hu3
        rw [this, one_zpow, one_mul]
      have hmem : ∀ y : ↥V, ((f y : ↥V) : G) ∈ f.range.map V.subtype := fun y =>
        ⟨f y, ⟨y, rfl⟩, rfl⟩
      rw [hk]
      obtain h | h | h : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      · rw [h]; simp only [zpow_zero]
        rw [commutatorElement_def]
        simp
      · rw [h, zpow_one, hcomm_u x hx]
        exact hmem ⟨x, hx⟩
      · rw [h]
        have hx1 : u * x * u⁻¹ ∈ V := hconj x hx
        have hx2 : u * (u * x * u⁻¹) * u⁻¹ ∈ V := hconj _ hx1
        have e1 : ⁅x, u ^ (2 : ℤ)⁆ =
            (x * (u * x * u⁻¹)) * ((u * x * u⁻¹) * (u * (u * x * u⁻¹) * u⁻¹)) := by
          have hsq1 := hsq _ hx1
          have hb : u ^ (2 : ℤ) * x⁻¹ * (u ^ (2 : ℤ))⁻¹ = u * (u * x * u⁻¹) * u⁻¹ := by
            rw [← hxinv _ hx2]; group
          calc ⁅x, u ^ (2 : ℤ)⁆ = x * (u ^ (2 : ℤ) * x⁻¹ * (u ^ (2 : ℤ))⁻¹) := by
                rw [commutatorElement_def]; group
            _ = x * (u * (u * x * u⁻¹) * u⁻¹) := by rw [hb]
            _ = (x * (u * x * u⁻¹)) * ((u * x * u⁻¹) * (u * (u * x * u⁻¹) * u⁻¹)) := by
                calc x * (u * (u * x * u⁻¹) * u⁻¹)
                    = x * ((u * x * u⁻¹) * (u * x * u⁻¹)) * (u * (u * x * u⁻¹) * u⁻¹) := by
                      rw [hsq1, mul_one]
                  _ = _ := by group
        rw [e1]
        exact (f.range.map V.subtype).mul_mem (hmem ⟨x, hx⟩) (hmem ⟨_, hx1⟩)
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card ↥V := by
    rw [← Subgroup.index_ker f]
    exact Subgroup.card_mul_index f.ker
  rw [← hrange, ← hker, CFSG.QuasithinUnique.Setup.card_map_subtype,
    CFSG.QuasithinUnique.Setup.card_map_subtype, mul_comm]
  exact hcard

theorem mem_zZero_of_centralizes {T V : Subgroup G} (h : PushHyp X T V)
    (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) (hnc : NoCharNormal T X)
    {u : G} (huX : u ∈ X) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) {z : G} (hzV : z ∈ V)
    (hzu : u * z * u⁻¹ = z) : z ∈ zZero X V := by
  obtain ⟨c, α, hα, -, hαk⟩ := exists_alpha_s3 h e hnc
  have hs := isSec_zZero h
  set g : ↥X := ⟨u, huX⟩ with hg
  have hconj : hs.conjHom g (hs.proj ⟨z, hzV⟩) = hs.proj ⟨z, hzV⟩ := by
    show hs.conjQ g (hs.proj ⟨z, hzV⟩) = _
    rw [hs.conjQ_mk]
    congr 1
    exact Subtype.ext hzu
  set v := Multiplicative.toAdd (c (hs.proj ⟨z, hzV⟩)) with hv
  have hfix : slPerm (ZMod 2) (α g) v = v := by
    have h2 : slPerm (ZMod 2) (α g) v =
        Multiplicative.toAdd (c (hs.conjHom g (c.symm (Multiplicative.ofAdd v)))) := by
      rw [← hα g]
      exact coordActHom_apply c _ v
    rw [h2]
    simp only [hv, ofAdd_toAdd, MulEquiv.symm_apply_apply, hconj]
  have hA3 : α g ^ 3 = 1 := by
    rw [← map_pow]
    have : g ^ 3 = 1 := Subtype.ext (by simpa [hg] using hu3)
    rw [this, map_one]
  have hA1 : α g ≠ 1 := by
    intro h1
    have hmem := (hαk g).mp h1
    have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact hu1 (eq_one_of_odd_orderOf_of_mem_pCoreOf hmem
      (by rw [orderOf_eq_prime hu3 hu1]; decide))
  have hv0 : v = 0 := by
    refine sl2_zmod2_fixed_zero (α g) hA3 hA1 v ?_
    have h2 := hfix
    rw [slPerm_apply, Matrix.SpecialLinearGroup.smul_def] at h2
    exact h2
  have hw : hs.proj ⟨z, hzV⟩ = 1 := by
    have h1 : c (hs.proj ⟨z, hzV⟩) = 1 := by
      have := congrArg Multiplicative.ofAdd hv0
      simpa [hv] using this
    exact c.injective (by simpa using h1)
  exact (hs.proj_eq_one_iff ⟨z, hzV⟩).mp hw

end Quotient

end I28_3S3

open I28_3S3

variable {G : Type} [Group G] [Finite G]

theorem baumann_niles_s3 {X T : Subgroup G} {u : G} (hT : IsSylowTwoOf T X) (hF : CharTwo X)
    (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3))) (hnc : NoCharNormal T X)
    (huX : u ∈ X) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) :
    Nat.card (⁅pCoreOf 2 X, Subgroup.zpowers u⁆ : Subgroup G) = 4 ∧
      ⁅pCoreOf 2 X, Subgroup.zpowers u⁆ ≤ omegaOneCenterOf (pCoreOf 2 X) ∧
        ⁅omegaOneCenterOf (pCoreOf 2 X), Subgroup.zpowers u⁆ =
          ⁅pCoreOf 2 X, Subgroup.zpowers u⁆ := by
  obtain ⟨e⟩ := hq
  have hpush := pushHyp_conjClosure hT hF e hnc
  obtain ⟨hVle, hVel, hVred⟩ :=
    conjClosure_isTwoReducedIn_of_charTwo hT hF (Z := omegaOneCenterOf T) le_rfl
  set V := conjClosure (omegaOneCenterOf T) X with hV
  set R := pCoreOf 2 X with hR
  have hBC : ⁅pCoreOf 2 X, pResidualOf 2 X⁆ ≤ V := baumannS3_holds G X T V hpush ⟨e⟩ hnc
  have huRes : u ∈ pResidualOf 2 X := mem_pResidualOf_of_pow_three huX hu3
  have hUres : Subgroup.zpowers u ≤ pResidualOf 2 X := Subgroup.zpowers_le.mpr huRes
  have hRU_V : ⁅R, Subgroup.zpowers u⁆ ≤ V := (Subgroup.commutator_mono le_rfl hUres).trans hBC
  have hVR : V ≤ R := hVle.trans inf_le_left
  have hUnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr (le_normalizer_pCoreOf 2 X huX)
  have hR2 : IsPGroup 2 ↥R := pCoreOf_isPGroup 2 X
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers u)) (Nat.card R) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : Nat.card (Subgroup.zpowers u) = 3 := by
      rw [Nat.card_zpowers]; exact orderOf_eq_prime hu3 hu1
    obtain ⟨n, hn⟩ := hR2.exists_card_eq
    rw [h3, hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hdouble : ⁅⁅R, Subgroup.zpowers u⁆, Subgroup.zpowers u⁆ = ⁅R, Subgroup.zpowers u⁆ :=
    commutator_double_eq_self _ _ hUnorm hcop
      (by have := hR2.isNilpotent; infer_instance)
  have hRV : ⁅R, Subgroup.zpowers u⁆ = ⁅V, Subgroup.zpowers u⁆ := by
    apply le_antisymm
    · calc ⁅R, Subgroup.zpowers u⁆ = ⁅⁅R, Subgroup.zpowers u⁆, Subgroup.zpowers u⁆ := hdouble.symm
        _ ≤ ⁅V, Subgroup.zpowers u⁆ := Subgroup.commutator_mono hRU_V le_rfl
    · exact Subgroup.commutator_mono hVR le_rfl
  have hA := card_commutator_mul_card_centralizer hVel (hVred.2.1 huX) hu3
  have hV0 : V ⊓ Subgroup.centralizer ({u} : Set G) = zZero X V := by
    apply le_antisymm
    · intro z hz
      obtain ⟨hzV, hzc⟩ := Subgroup.mem_inf.mp hz
      have hzu := Subgroup.mem_centralizer_singleton_iff.mp hzc
      refine mem_zZero_of_centralizes hpush e hnc huX hu3 hu1 hzV ?_
      calc u * z * u⁻¹ = (u * z) * u⁻¹ := rfl
        _ = (z * u) * u⁻¹ := by rw [← hzu]
        _ = z := by group
    · intro z hz
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz).1, ?_⟩
      have hzc := (Subgroup.mem_inf.mp hz).2
      rw [Subgroup.mem_centralizer_iff] at hzc ⊢
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact hzc u huRes
  have hW : Nat.card (isSec_zZero hpush).W = 2 ^ 2 := card_secW_s3 hpush e hnc
  have hzV : zZero X V ≤ V := inf_le_left
  have hrel : (zZero X V).relIndex V = 4 := by
    have : Nat.card (isSec_zZero hpush).W = (zZero X V).relIndex V := by
      show Nat.card (↥V ⧸ (zZero X V).subgroupOf V) = ((zZero X V).subgroupOf V).index
      exact (Subgroup.index_eq_card _).symm
    rw [← this, hW]; norm_num
  have hmul := Subgroup.relIndex_mul_card (H := zZero X V) (K := V)
  rw [inf_of_le_left hzV] at hmul
  have hpos : 0 < Nat.card (zZero X V : Subgroup G) := Nat.card_pos
  have hcard4 : Nat.card (⁅V, Subgroup.zpowers u⁆ : Subgroup G) = 4 := by
    rw [hV0] at hA
    rw [hrel] at hmul
    have : Nat.card (⁅V, Subgroup.zpowers u⁆ : Subgroup G) * Nat.card (zZero X V : Subgroup G) =
        4 * Nat.card (zZero X V : Subgroup G) := by rw [hA, ← hmul]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hVΩ : V ≤ omegaOneCenterOf R := fun z hz =>
    Subgroup.subset_closure ⟨⟨hVR hz, (hVle hz).2⟩, hVel.2 z hz⟩
  refine ⟨by rw [hRV]; exact hcard4, hRU_V.trans hVΩ, ?_⟩
  apply le_antisymm
  · exact Subgroup.commutator_mono (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le R) le_rfl
  · calc ⁅R, Subgroup.zpowers u⁆ = ⁅⁅R, Subgroup.zpowers u⁆, Subgroup.zpowers u⁆ := hdouble.symm
      _ ≤ ⁅omegaOneCenterOf R, Subgroup.zpowers u⁆ :=
        Subgroup.commutator_mono (hRU_V.trans hVΩ) le_rfl

@[expose] def I_28_3_S3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T : Subgroup G), IsSylowTwoOf T X → CharTwo X →
    Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3)) →
      (∃ C : Subgroup G, C ≤ T ∧ C ≠ ⊥ ∧ (C.subgroupOf T).Characteristic ∧
          X ≤ Subgroup.normalizer (C : Set G)) ∨
        ∀ u : G, u ∈ X → u ^ 3 = 1 → u ≠ 1 →
          Nat.card (⁅pCoreOf 2 X, Subgroup.zpowers u⁆ : Subgroup G) = 4 ∧
            ⁅pCoreOf 2 X, Subgroup.zpowers u⁆ ≤ omegaOneCenterOf (pCoreOf 2 X) ∧
              ⁅omegaOneCenterOf (pCoreOf 2 X), Subgroup.zpowers u⁆ =
                ⁅pCoreOf 2 X, Subgroup.zpowers u⁆

theorem I_28_3_S3_proved : I_28_3_S3 := by
  intro G _ _ X T hT hF hq
  by_cases hnc : NoCharNormal T X
  · exact Or.inr fun u huX hu3 hu1 => baumann_niles_s3 hT hF hq hnc huX hu3 hu1
  · left
    by_contra hcon
    exact hnc fun C hCT hC1 hCchar hXC => hcon ⟨C, hCT, hC1, hCchar, hXC⟩

end GL83
