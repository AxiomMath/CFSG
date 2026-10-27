module

public import CFSG.GH74.GLS.C3.Layer1.Thm1L3L34
public import CFSG.GH74.GLS.C3.Layer1.Thm1GlueLift
public import CFSG.Walter.W67.Section5.MaxClass
public import CFSG.GH74.GLS.C3.Layer1.BkP34N
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3Aux
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1

section JGlue

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_normalizes {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, (a₂⁻¹ * b₁ * a₂⁻¹⁻¹) * b₂, B.mul_mem ?_ hb₂, ?_⟩
        · exact h a₂⁻¹ (A.inv_mem ha₂) b₁ hb₁
        · group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, h a ha b⁻¹ (B.inv_mem hb), ?_⟩
        group }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩) (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem kBar_pumpJ_equiv {K : Subgroup G} {f : G}
    (hsup : pumpJ K f = layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f)) :
    Nonempty (kBar (layerI K f) ≃* kBar (pumpJ K f)) := by
  have hIJ : layerI K f ≤ pumpJ K f := layerI_le_pumpJ K f
  have hcov : ∀ k ∈ pumpJ K f, ∃ c ∈ layerI K f, ∃ o ∈ pPrimeCoreOf 2 (pumpJ K f), k = c * o := by
    intro k hk
    have hk' : k ∈ layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) := by rw [← hsup]; exact hk
    exact exists_mul_of_mem_sup_of_normalizes
      (fun a ha b hb => by
        have := (Subgroup.mem_normalizer_iff.1 (Back.Setup91.mem_normalizer_pPrimeCoreOf_self
          (M := pumpJ K f) (hIJ ha)) b).1 hb
        exact this) hk'
  have hsurj := TwoThin.hatMap_surjective hIJ hcov
  have hker := TwoThin.ker_hatMap_eq_pPrimeCore hIJ hcov
  let e₃ := QuotientGroup.quotientKerEquivOfSurjective (TwoThin.hatMap hIJ) hsurj
  let e₄ : kBar (layerI K f) ≃* (↥(layerI K f) ⧸ (TwoThin.hatMap hIJ).ker) :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  exact ⟨e₄.trans e₃⟩


theorem z_not_mem_secD {K : Subgroup G} {f z : G} {V : Subgroup G}
    (hsup : pumpJ K f = layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f))
    (hJn : ∀ c ∈ centralizer ({f} : Set G), ∀ j ∈ pumpJ K f, c * j * c⁻¹ ∈ pumpJ K f)
    (hcenJ : Function.Injective (MulAut.conj : kBar (pumpJ K f) →* MulAut (kBar (pumpJ K f))))
    (hzI : z ∈ layerI K f) (hz2 : orderOf z = 2) : z ∉ secD K f V := by
  intro hz
  have hzJ : z ∈ pumpJ K f := layerI_le_pumpJ K f hzI
  have hzC : z ∈ centralizer ({f} : Set G) := layerI_le_centralizer K f hzI
  have hz' : z ∈ centralizerSection (pumpJ K f) (pPrimeCoreOf 2 (pumpJ K f)) := by
    have := hz.2
    unfold secD at hz
    rw [← hsup] at this
    exact this
  have h1 : Back.actHom hJn ⟨z, hzC⟩ = 1 :=
    (Back.actHom_eq_one_iff_commutator_mem hJn ⟨z, hzC⟩).2 hz'.2.2
  rw [Back.actHom_of_mem hJn hzJ hzC] at h1
  have h2 : (QuotientGroup.mk (⟨z, hzJ⟩ : ↥(pumpJ K f)) : kBar (pumpJ K f)) = 1 :=
    hcenJ (by rw [h1, map_one])
  have h3 : (⟨z, hzJ⟩ : ↥(pumpJ K f)) ∈ pPrimeCore 2 ↥(pumpJ K f) :=
    (QuotientGroup.eq_one_iff _).1 h2
  have h4 : z ∈ pPrimeCoreOf 2 (pumpJ K f) := Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hzJ, h3⟩
  have hdvd : Nat.card ↥(zpowers z) ∣ Nat.card ↥(pPrimeCoreOf 2 (pumpJ K f)) :=
    Subgroup.card_dvd_of_le ((zpowers_le).2 h4)
  rw [Nat.card_zpowers, hz2] at hdvd
  exact (Nat.not_even_iff_odd.2 (TwoThin.card_pPrimeCoreOf_odd (pumpJ K f)))
    (even_iff_two_dvd.2 hdvd)


theorem exists_central_of_normal' {U B : Subgroup G}
    (hUbot : U ≠ ⊥) (hUB : U ≤ B) (hBN : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U)
    (hB2 : IsPGroup 2 B) : ∃ w ∈ U, w ≠ 1 ∧ ∀ y ∈ B, y * w = w * y := by
  classical
  have hnil : Group.IsNilpotent B := hB2.isNilpotent
  let H : Subgroup B := U.subgroupOf B
  have hHn : H.Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ U := hn
    exact hBN g g.2 n hn'⟩
  have hH0 : H ≠ ⊥ := by
    intro h
    apply hUbot
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hUB hu⟩ : B) ∈ H := hu
    rw [h] at this
    have h1 : (⟨u, hUB hu⟩ : B) = 1 := this
    have h2 : u = 1 := congrArg Subtype.val h1
    rw [h2]; exact one_mem _
  have hne : H ⊓ Subgroup.center B ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hH0
  obtain ⟨⟨w, hwH, hwc⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨(w : G), hwH, ?_, ?_⟩
  · intro h
    apply hw1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · intro y hy
    have := Subgroup.mem_center_iff.mp hwc ⟨y, hy⟩
    exact congrArg Subtype.val this

theorem inf_eq_bot_of_normal {V P D : Subgroup G} {z : G} (hV2 : IsPGroup 2 ↥V) (hPV : P ≤ V)
    (hPn : ∀ v ∈ V, ∀ p ∈ P, v * p * v⁻¹ ∈ P)
    (hDn : ∀ v ∈ V, ∀ d ∈ D, v * d * v⁻¹ ∈ D) (hzD : z ∉ D)
    (hzu : ∀ w ∈ P, (∀ p ∈ P, w * p = p * w) → w = 1 ∨ w = z) : P ⊓ D = ⊥ := by
  by_contra hne
  obtain ⟨w, ⟨hwP, hwD⟩, hw1, hwc⟩ := exists_central_of_normal' hne (inf_le_left.trans hPV)
    (fun v hv u hu => ⟨hPn v hv u hu.1, hDn v hv u hu.2⟩) hV2
  rcases hzu w hwP (fun p hp => (hwc p (hPV hp)).symm) with h | h
  · exact hw1 h
  · exact hzD (h ▸ hwD)

omit [Finite G] in
theorem commute_of_inf_eq_bot {V P D : Subgroup G} (hPV : P ≤ V) (hDV : D ≤ V)
    (hPn : ∀ v ∈ V, ∀ p ∈ P, v * p * v⁻¹ ∈ P) (hDn : ∀ v ∈ V, ∀ d ∈ D, v * d * v⁻¹ ∈ D)
    (hPD : P ⊓ D = ⊥) : ∀ p ∈ P, ∀ d ∈ D, p * d = d * p := by
  intro p hp d hd
  have h1 : p * d * p⁻¹ * d⁻¹ ∈ P ⊓ D := by
    refine ⟨?_, ?_⟩
    · have : p * d * p⁻¹ * d⁻¹ = p * (d * p⁻¹ * d⁻¹) := by group
      rw [this]
      exact P.mul_mem hp (hPn d (hDV hd) p⁻¹ (P.inv_mem hp))
    · exact D.mul_mem (hDn p (hPV hp) d hd) (D.inv_mem hd)
  rw [hPD, Subgroup.mem_bot] at h1
  calc p * d = (p * d * p⁻¹ * d⁻¹) * (d * p) := by group
    _ = d * p := by rw [h1, one_mul]

omit [Finite G] in
theorem two_elt_mul {a b : G} (hab : Commute a b) (ha : ∃ k : ℕ, a ^ (2 ^ k) = 1)
    (hb : ∃ k : ℕ, b ^ (2 ^ k) = 1) : ∃ k : ℕ, (a * b) ^ (2 ^ k) = 1 := by
  obtain ⟨k₁, h₁⟩ := ha
  obtain ⟨k₂, h₂⟩ := hb
  refine ⟨k₁ + k₂, ?_⟩
  rw [hab.mul_pow, pow_add, pow_mul, h₁, one_pow, one_mul, pow_mul', h₂, one_pow]

omit [Finite G] in
theorem two_elt_zpow {a : G} (ha : ∃ k : ℕ, a ^ (2 ^ k) = 1) (n : ℤ) :
    ∃ k : ℕ, (a ^ n) ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := ha
  refine ⟨k, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

theorem mem_zpowers_of_two_element {x : G} {Q : Subgroup G} (hS : IsSylowOf 2 (zpowers x) Q)
    (hQ : ∀ k ∈ Q, k * x = x * k) {w : G} (hwQ : w ∈ Q) (hw2 : ∃ k : ℕ, w ^ (2 ^ k) = 1) :
    w ∈ zpowers x := by
  obtain ⟨k, hkQ, hk⟩ := exists_conj_le_of_isSylowOf hS ((zpowers_le).2 hwQ)
    (isPGroup_zpowers_of_pow_eq_one hw2)
  have hu : k⁻¹ * w * k ∈ zpowers x := hk w (mem_zpowers w)
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hu
  have hkc : k * x ^ m = x ^ m * k :=
    (Commute.zpow_right (show Commute k x from hQ k hkQ) m).eq
  have : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
  rw [this, ← hm, hkc]
  have : x ^ m * k * k⁻¹ = x ^ m := by group
  rw [this]
  exact mem_zpowers_iff.2 ⟨m, rfl⟩


theorem cent_le_of_secD {x f : G} {K V P D : Subgroup G}
    (hKC : K ≤ centralizer ({x} : Set G))
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hPK : IsSylowOf 2 P K)
    (hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)))
    (hAutC : AutLevelC (kBar K)) (hPdih : ∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥P n)
    (hfC : f ∈ centralizer ({x} : Set G)) (hf2 : orderOf f = 2) (hfP : ∀ p ∈ P, f * p = p * f)
    (hfout : Back.actHom hKN ⟨f, hfC⟩ ∉ innAut (kBar K))
    (hxS : IsSylowOf 2 (zpowers x) (CxK x K))
    (hV2 : IsPGroup 2 ↥V) (hVf : ∀ v ∈ V, v * f = f * v) (hDV : D ≤ V) (hxD : x ∈ D)
    (hfD : f ∈ D) (hPD : P ⊓ D = ⊥) (hcomm : ∀ p ∈ P, ∀ d ∈ D, p * d = d * p) :
    ∀ d ∈ D, d * x = x * d → d ∈ zpowers x ⊔ zpowers f := by
  intro d hd hdx
  have hdC : d ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hdx
  have hd2 : ∃ k : ℕ, d ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hV2 ⟨d, hDV hd⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨z₀, hz₀P, a, b, hmem⟩ := exists_mul_mem_cmk_of_centralizes hKC hKN hPK hcen hAutC
    hPdih hfC hf2 hfP hfout hdC hd2 (fun p hp => (hcomm p hp d hd).symm) (hVf d (hDV hd))
  have hz₀2 : ∃ k : ℕ, z₀ ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hPK.isPGroup ⟨z₀, hz₀P⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hff2 : ∃ k : ℕ, f ^ (2 ^ k) = 1 :=
    ⟨1, by rw [pow_one]; have := pow_orderOf_eq_one f; rwa [hf2] at this⟩
  have hdz : Commute d z₀ := (hcomm z₀ hz₀P d hd).symm
  have hdf : Commute d f := hVf d (hDV hd)
  have hzf : Commute z₀ f := (hfP z₀ hz₀P).symm
  have hdz2 : ∃ k : ℕ, (d * z₀ ^ a) ^ (2 ^ k) = 1 :=
    two_elt_mul (hdz.zpow_right a) hd2 (two_elt_zpow hz₀2 a)
  have hc₂ : ∃ k : ℕ, (d * z₀ ^ a * f ^ b) ^ (2 ^ k) = 1 :=
    two_elt_mul (Commute.mul_left (hdf.zpow_right b) ((hzf.zpow_left a).zpow_right b)) hdz2
      (two_elt_zpow hff2 b)
  have hc₀ : d * z₀ ^ a * f ^ b ∈ zpowers x :=
    mem_zpowers_of_two_element hxS (fun k hk => mem_centralizer_singleton_iff.1 hk.1) hmem hc₂
  have hzaD : z₀ ^ a ∈ D := by
    have h1 : z₀ ^ a = d⁻¹ * (d * z₀ ^ a * f ^ b) * (f ^ b)⁻¹ := by group
    rw [h1]
    exact D.mul_mem (D.mul_mem (D.inv_mem hd) ((zpowers_le).2 hxD hc₀))
      (D.inv_mem (D.zpow_mem hfD b))
  have hzaP : z₀ ^ a ∈ P := P.zpow_mem hz₀P a
  have hza1 : z₀ ^ a = 1 := by
    have : z₀ ^ a ∈ P ⊓ D := ⟨hzaP, hzaD⟩
    rwa [hPD, Subgroup.mem_bot] at this
  have hd' : d = (d * z₀ ^ a * f ^ b) * (f ^ b)⁻¹ := by
    rw [hza1]; group
  rw [hd']
  exact (zpowers x ⊔ zpowers f).mul_mem (Subgroup.mem_sup_left hc₀)
    ((zpowers x ⊔ zpowers f).inv_mem (Subgroup.mem_sup_right (zpowers f |>.zpow_mem (mem_zpowers f) b)))


theorem isMaximalClassTwoGroup_of_card_centralizer {D : Type} [Group D] [Finite D]
    (hD : IsPGroup 2 D) {b : D} (hb : orderOf b = 2)
    (hc : Nat.card (centralizer ({b} : Set D)) = 4) : P34.IsMaximalClassTwoGroup D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm2, hm, hγ⟩ := CFSG.Walter.W67.isMaximalClass_of_card_centralizer (p := 2) hD b hb
    (by rw [hc]; norm_num)
  have hnil : Group.IsNilpotent D := hD.isNilpotent
  refine ⟨hD, hnil, ?_⟩
  have hcl1 : m - 1 ≤ Group.nilpotencyClass D := by
    by_contra hcon
    apply hγ
    rw [Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
    omega
  have hcl2 : Group.nilpotencyClass D ≤ m - 1 :=
    CFSG.GH74.Uniqueness.SU.SU1.nilpotencyClass_le_of_card Nat.prime_two m D hm hm2
  have hcl : Group.nilpotencyClass D = m - 1 := le_antisymm hcl2 hcl1
  rw [hcl, hm]
  congr 1
  omega


omit [Finite G] in
theorem coe_mem_zpowers {D : Subgroup G} {a b : ↥D} (h : b ∈ zpowers a) :
    (b : G) ∈ zpowers (a : G) := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 h
  exact mem_zpowers_iff.2 ⟨k, by simp⟩

omit [Finite G] in
theorem mem_zpowers_of_coe {D : Subgroup G} {a b : ↥D} (h : (b : G) ∈ zpowers (a : G)) :
    b ∈ zpowers a := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
  exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩

theorem secD_shape {x f : G} {V D : Subgroup G}
    (hD2 : IsPGroup 2 ↥D) (hDn : ∀ v ∈ V, ∀ d ∈ D, v * d * v⁻¹ ∈ D)
    (hxD : x ∈ D) (hx2 : orderOf x = 2) (hfD : f ∈ D) (hf2 : orderOf f = 2) (hxf : x * f = f * x)
    (hne : x ≠ f) (hCx : ∀ d ∈ D, d * x = x * d → d ∈ zpowers x ⊔ zpowers f)
    (hfZ : ∀ d ∈ D, d * f = f * d) :
    P34.IsMaximalClassTwoGroup ↥D ∧
      ((Nat.card ↥D = 4 ∧ D = zpowers x ⊔ zpowers f) ∨
        ∃ a ∈ D, (∀ v ∈ V, v * a * v⁻¹ ∈ zpowers a) ∧ 4 ∣ orderOf a ∧ x ∉ zpowers a ∧
          (∀ d ∈ D, d ∈ zpowers a ∨ x⁻¹ * d ∈ zpowers a) ∧ f ∈ zpowers a) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx2; omega
  have hf1 : f ≠ 1 := fun h => by rw [h, orderOf_one] at hf2; omega
  have hxsq : x ^ 2 = 1 := by have := pow_orderOf_eq_one x; rwa [hx2] at this
  have hfsq : f ^ 2 = 1 := by have := pow_orderOf_eq_one f; rwa [hf2] at this
  have hKlein : Nat.card ↥(zpowers x ⊔ zpowers f) = 4 := P89.card_klein hxsq hfsq hxf hx1 hf1 hne
  set b : ↥D := ⟨x, hxD⟩ with hbdef
  have hb2 : orderOf b = 2 := by rw [hbdef, Subgroup.orderOf_mk]; exact hx2
  have hDcx : D ⊓ centralizer ({x} : Set G) = zpowers x ⊔ zpowers f := by
    apply le_antisymm
    · rintro d ⟨hd, hdc⟩
      exact hCx d hd (mem_centralizer_singleton_iff.1 hdc)
    · refine sup_le ((zpowers_le).2 ⟨hxD, mem_centralizer_singleton_iff.2 rfl⟩)
        ((zpowers_le).2 ⟨hfD, mem_centralizer_singleton_iff.2 hxf.symm⟩)
  have hcent : (centralizer ({b} : Set ↥D)).map D.subtype = D ⊓ centralizer ({x} : Set G) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq, Subgroup.subtype_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, congrArg Subtype.val hw⟩
    · rintro ⟨hy, hyc⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyc, rfl⟩
  have hcard4 : Nat.card ↥(centralizer ({b} : Set ↥D)) = 4 := by
    have h1 := Subgroup.card_map_of_injective (f := D.subtype)
      (K := centralizer ({b} : Set ↥D)) D.subtype_injective
    rw [hcent, hDcx, hKlein] at h1
    exact h1.symm
  have hmax : P34.IsMaximalClassTwoGroup ↥D := isMaximalClassTwoGroup_of_card_centralizer hD2 hb2 hcard4
  refine ⟨hmax, ?_⟩
  have hf2' : orderOf (⟨f, hfD⟩ : ↥D) = 2 := by rw [Subgroup.orderOf_mk]; exact hf2
  have hfc : ∀ y : ↥D, (⟨f, hfD⟩ : ↥D) * y = y * ⟨f, hfD⟩ := fun y =>
    Subtype.ext (hfZ y y.2).symm
  have hsub : zpowers x ⊔ zpowers f ≤ D := sup_le ((zpowers_le).2 hxD) ((zpowers_le).2 hfD)
  rcases P34.QShape.classify hf2' hfc (Or.inr hmax) with hcyc | ⟨h4, -⟩ | ⟨a, S⟩
  · exfalso
    have := hcyc
    have h := P34.QShape.cyclic_involution_unique (H := ↥D) (u := ⟨x, hxD⟩) (v := ⟨f, hfD⟩)
      (Subtype.ext (by show x * x = 1; rw [← sq]; exact hxsq))
      (Subtype.ext (by show f * f = 1; rw [← sq]; exact hfsq))
      (fun h => hx1 (congrArg Subtype.val h)) (fun h => hf1 (congrArg Subtype.val h))
    exact hne (congrArg Subtype.val h)
  · left
    exact ⟨h4, (Subgroup.eq_of_le_of_card_ge hsub (by rw [hKlein, h4])).symm⟩
  · right
    have hidx := S.index_two
    have hord := S.order_ge
    have hDcard : orderOf a * 2 = Nat.card ↥D := by
      have h1 := Subgroup.card_mul_index (zpowers a)
      rwa [Nat.card_zpowers, hidx] at h1
    have h8 : 8 ≤ Nat.card ↥D := by omega
    have hnc : ∃ y : ↥D, (⟨x, hxD⟩ : ↥D) * y ≠ y * ⟨x, hxD⟩ := by
      by_contra hcon
      push Not at hcon
      have hle : D ≤ centralizer ({x} : Set G) := fun d hd =>
        mem_centralizer_singleton_iff.2 (congrArg Subtype.val (hcon ⟨d, hd⟩)).symm
      have h0 : D ⊓ centralizer ({x} : Set G) = D := inf_eq_left.2 hle
      rw [hDcx] at h0
      have h4 : Nat.card ↥D = 4 := by rw [← h0]; exact hKlein
      omega
    have hu2 : (⟨x, hxD⟩ : ↥D) * ⟨x, hxD⟩ = 1 :=
      Subtype.ext (by show x * x = 1; rw [← sq]; exact hxsq)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hD2) a
    have hk2 : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    refine ⟨(a : G), a.2, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      let φ : ↥D →* ↥D :=
        { toFun := fun d => ⟨v * d * v⁻¹, hDn v hv d d.2⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
      have hφ : Function.Injective φ := by
        intro d₁ d₂ h
        apply Subtype.ext
        have := congrArg Subtype.val h
        simpa [φ] using this
      exact coe_mem_zpowers (S.phi_mem hu2 hnc φ hφ)
    · rw [Subgroup.orderOf_coe, hk]
      exact (pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)
    · intro hxa
      exact S.not_mem_of_noncentral hu2 hnc (mem_zpowers_of_coe hxa)
    · intro d hd
      by_cases hda : (⟨d, hd⟩ : ↥D) ∈ zpowers a
      · exact Or.inl (coe_mem_zpowers hda)
      · right
        have hxa : (⟨x, hxD⟩ : ↥D)⁻¹ ∉ zpowers a := fun h =>
          S.not_mem_of_noncentral hu2 hnc (by simpa using (zpowers a).inv_mem h)
        have h1 : (⟨x, hxD⟩ : ↥D)⁻¹ * ⟨d, hd⟩ ∈ zpowers a := by
          rw [Subgroup.mul_mem_iff_of_index_two hidx]
          exact iff_of_false hxa hda
        exact coe_mem_zpowers h1
    · have hn2 : 2 ∣ orderOf a := by
        rw [hk]
        exact dvd_pow_self 2 (by omega)
      obtain ⟨m, hm⟩ := hn2
      have hu₀sq : a ^ m * a ^ m = 1 := by
        rw [← pow_add, ← two_mul, ← hm]; exact pow_orderOf_eq_one a
      have hu₀1 : a ^ m ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
      have hu₀mem : a ^ m ∈ zpowers a := ⟨(m : ℤ), by simp⟩
      rcases S.center_eq (a ^ m) (fun y => S.invol_central hu₀mem hu₀sq hu₀1 y) with h | h
      · exact absurd h hu₀1
      · have : (⟨f, hfD⟩ : ↥D) ∈ zpowers a := h ▸ hu₀mem
        exact coe_mem_zpowers this


theorem isSylowOf_of_le {G : Type} [Group G] [Finite G] {P X K : Subgroup G}
    (hPK : IsSylowOf 2 P K) (hPX : P ≤ X) (hXK : X ≤ K) : IsSylowOf 2 P X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hPK ⊢
  obtain ⟨-, hP2, hdvd⟩ := hPK
  refine ⟨hPX, hP2, fun h => hdvd ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P X K hPX hXK]
  exact h.mul_right _

theorem z_mem_layerI {G : Type} [Group G] [Finite G] {K P : Subgroup G} {f z : G} {r : ℕ}
    (hPK : IsSylowOf 2 P K) (hfP : ∀ p ∈ P, f * p = p * f)
    (hI : HasL2Model (kBar (layerI K f)) (fun q => q = r)) (hr : Odd r)
    (hzu : ∀ w ∈ P, (∀ p ∈ P, w * p = p * w) → w = 1 ∨ w = z) : z ∈ layerI K f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := K ⊓ centralizer ({f} : Set G) with hX
  set I := layerI K f with hIdef
  have hPX : P ≤ X := le_inf hPK.le (fun p hp => mem_centralizer_singleton_iff.2 (hfP p hp).symm)
  have hIX : I ≤ X := TwoThin.pLayerOf_le 2 X
  have hIconj : ∀ g ∈ X, ∀ i ∈ I, g * i * g⁻¹ ∈ I := by
    intro g hg i hi
    have h : (MulAut.conj g) i ∈ pLayerOf 2 X :=
      Stage1.Thm2.Recip.pLayerOf_map_conj_le hg ⟨i, hi, rfl⟩
    rw [MulAut.conj_apply] at h
    exact h
  have hPXsyl : IsSylowOf 2 P X := isSylowOf_of_le hPK hPX inf_le_left
  have hIeven : 2 ∣ Nat.card ↥I := by
    have h1 := Thm1L34.card_kBar_of_hasL2Model hI
    obtain ⟨k, rfl⟩ := hr
    rw [PumpClass.ordA_one_odd] at h1
    have h2 : 2 ∣ Nat.card (kBar I) := by
      rw [h1]
      exact ⟨k * (k + 1) * (2 * k + 1), by ring⟩
    exact h2.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hIeven
  have htI : (t : G) ∈ I := t.2
  have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htX : (t : G) ∈ X := hIX htI
  have hzpow : IsPGroup 2 ↥(zpowers (t : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  obtain ⟨k, hkX, hk⟩ := exists_conj_le_of_isSylowOf hPXsyl ((zpowers_le).2 htX) hzpow
  have huP : k⁻¹ * (t : G) * k ∈ P := hk _ (mem_zpowers _)
  have huI : k⁻¹ * (t : G) * k ∈ I := by
    have := hIconj k⁻¹ (X.inv_mem hkX) _ htI
    simpa using this
  have hu1 : k⁻¹ * (t : G) * k ≠ 1 := by
    intro h
    have : (t : G) = 1 := by
      calc (t : G) = k * (k⁻¹ * (t : G) * k) * k⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at ht2
    omega
  have hUbot : P ⊓ I ≠ ⊥ := by
    intro h
    have : k⁻¹ * (t : G) * k ∈ P ⊓ I := ⟨huP, huI⟩
    rw [h, Subgroup.mem_bot] at this
    exact hu1 this
  obtain ⟨w, ⟨hwP, hwI⟩, hw1, hwc⟩ := exists_central_of_normal' hUbot inf_le_left
    (fun p hp u hu => ⟨P.mul_mem (P.mul_mem hp hu.1) (P.inv_mem hp), hIconj p (hPX hp) u hu.2⟩)
    hPK.isPGroup
  rcases hzu w hwP (fun p hp => (hwc p hp).symm) with h | h
  · exact absurd h hw1
  · rw [← h]; exact hwI


omit [Finite G] in
theorem exists_mul_involutions_of_dihedral {P : Subgroup G} {n : ℕ}
    (hP : IsDihedralTwoGroup ↥P n) :
    ∀ p ∈ P, ∃ u ∈ P, ∃ w ∈ P, u * u = 1 ∧ w * w = 1 ∧ p = u * w := by
  obtain ⟨-, k, -, -, ⟨φ⟩⟩ := hP
  intro p hp
  have hmul : ∀ a : DihedralGroup k, ∃ u w : DihedralGroup k, u * u = 1 ∧ w * w = 1 ∧ a = u * w := by
    intro a
    cases a with
    | r i =>
      refine ⟨DihedralGroup.sr 0, DihedralGroup.sr i, DihedralGroup.sr_mul_self _,
        DihedralGroup.sr_mul_self _, ?_⟩
      rw [DihedralGroup.sr_mul_sr]; simp
    | sr i =>
      exact ⟨DihedralGroup.sr i, 1, DihedralGroup.sr_mul_self _, by simp, by simp⟩
  obtain ⟨u, w, hu, hw, huw⟩ := hmul (φ ⟨p, hp⟩)
  refine ⟨((φ.symm u : ↥P) : G), (φ.symm u).2, ((φ.symm w : ↥P) : G), (φ.symm w).2, ?_, ?_, ?_⟩
  · have := congrArg (fun y => ((φ.symm y : ↥P) : G)) hu
    simpa using this
  · have := congrArg (fun y => ((φ.symm y : ↥P) : G)) hw
    simpa using this
  · have := congrArg (fun y => ((φ.symm y : ↥P) : G)) huw
    simpa using this

section Abstract

variable {V' M : Type} [Group V'] [Group M] [Finite V'] [Finite M]

omit [Finite V'] in
theorem image_inf_eq_image (hV : IsPGroup 2 V') (ρ : V' →* M) (E : Subgroup M)
    (P' : Subgroup V') (hker : ∀ p ∈ P', ρ p = 1 → p = 1) (hPE : ∀ p ∈ P', ρ p ∈ E)
    (hcard : ∀ j : ℕ, 2 ^ j ∣ Nat.card E → 2 ^ j ≤ Nat.card P') :
    ∀ v : V', ρ v ∈ E → ∃ p ∈ P', ρ p = ρ v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup M := ρ.range ⊓ E with hB
  have hB2 : IsPGroup 2 ↥B :=
    (hV.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective).to_inf_left
  have hinj : Function.Injective (ρ.comp P'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hker a a.2 ha)
  have hrange : (ρ.comp P'.subtype).range = P'.map ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hPcard : Nat.card ↥(P'.map ρ) = Nat.card P' := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hρP : P'.map ρ ≤ B := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨⟨p, rfl⟩, hPE p hp⟩
  have hBle : Nat.card ↥B ≤ Nat.card P' := by
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hB2
    have hdvd : Nat.card ↥B ∣ Nat.card E := Subgroup.card_dvd_of_le inf_le_right
    rw [hj] at hdvd ⊢
    exact hcard j hdvd
  have heq : P'.map ρ = B := Subgroup.eq_of_le_of_card_ge hρP (by rw [hPcard]; exact hBle)
  intro v hv
  have hvB : ρ v ∈ B := ⟨⟨v, rfl⟩, hv⟩
  rw [← heq] at hvB
  obtain ⟨p, hp, hpv⟩ := hvB
  exact ⟨p, hp, hpv⟩

omit [Finite V'] [Finite M] in
theorem exists_gen_of_cyclic {C : Type} [Group C] [IsCyclic C] (ψ : V' →* C) :
    ∃ b : V', ∀ v : V', ∃ k : ℤ, ψ ((b ^ k)⁻¹ * v) = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥ψ.range)
  obtain ⟨b, hb⟩ := g.2
  refine ⟨b, fun v => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨ψ v, ⟨v, rfl⟩⟩)
  refine ⟨k, ?_⟩
  have h1 : ψ b ^ k = ψ v := by
    have := congrArg Subtype.val hk
    simpa [hb] using this
  rw [map_mul, map_inv, map_zpow, h1]
  simp

end Abstract

theorem two_pow_le_card_of_dvd {K P : Subgroup G} {r : ℕ} (hPK : IsSylowOf 2 P K) (hr : Odd r)
    (hdvd : r ^ 2 - 1 ∣ Nat.card (kBar K)) {j : ℕ} (hj : 2 ^ j ∣ r * (r ^ 2 - 1)) :
    2 ^ j ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime (2 ^ j) r :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hr)
  have h1 : 2 ^ j ∣ r ^ 2 - 1 := by
    rw [mul_comm] at hj
    exact hcop.dvd_of_dvd_mul_right hj
  have h2 : 2 ^ j ∣ Nat.card ↥K := h1.trans (hdvd.trans (Subgroup.card_quotient_dvd_card _))
  have hK0 : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
  have h3 : j ≤ (Nat.card ↥K).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hK0).1 h2
  rw [hPK.card_eq]
  exact Nat.pow_le_pow_right (by norm_num) h3



theorem involution_act_mem_innDiag
    {f : G} {J V : Subgroup G} {F₀ : Type} [Field F₀] [Finite F₀] (hodd : Odd (Nat.card F₀))
    (e₀ : kBar J ≃* L2 F₀) (hyp : Bk.Prop34HypN G f J)
    (hJn : ∀ c ∈ centralizer ({f} : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    (hVC : V ≤ centralizer ({f} : Set G)) :
    ∀ v (hv : v ∈ V), v * v = 1 → Back.actHom hJn ⟨v, hVC hv⟩ ∈ innDiagSub e₀ := by
  intro v hv hvv
  by_contra hnot
  set α := Back.actHom hJn ⟨v, hVC hv⟩ with hα
  have hvsq : (⟨v, hVC hv⟩ : ↥(centralizer ({f} : Set G))) * ⟨v, hVC hv⟩ = 1 := Subtype.ext hvv
  have hαα : α * α = 1 := by rw [hα, ← map_mul, hvsq, map_one]
  have hα1 : α ≠ 1 := fun h => hnot (h ▸ (innDiagSub e₀).one_mem)
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hαα) hα1
  obtain ⟨a, haE, hconj⟩ := exists_conj_fieldAut e₀ α hα2 hnot
  have hfa : α ∈ fieldAutSub (((a⁻¹ : MulAut (kBar J)) : kBar J ≃* kBar J).trans e₀) := by
    refine ⟨fieldProj e₀ α, ?_⟩
    rw [fieldAutHom_twist, inv_inv, ← hconj]
    group
  have hFaut : P34.IsFAutL2A7 (kBar J) α :=
    ⟨hα1, Or.inl ⟨F₀, inferInstance, inferInstance, ((a⁻¹ : MulAut (kBar J)) : kBar J ≃* kBar J).trans e₀,
      hodd, hfa⟩⟩
  have hv1 : v ≠ 1 := fun h => hα1 (by
    have : (⟨v, hVC hv⟩ : ↥(centralizer ({f} : Set G))) = 1 := Subtype.ext h
    rw [hα, this, map_one])
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hvv) hv1
  have hdef : Back.actHom hJn ⟨v, hVC hv⟩ =
      inducedQuotAut J (pPrimeCore 2 ↥J) ⟨v, U1a.mem_normalizer_of_norm hJn (hVC hv)⟩ := rfl
  exact Bk.prop34N_false hyp (hVC hv) hv2 ⟨U1a.mem_normalizer_of_norm hJn (hVC hv), by
    rw [← hdef]; exact hFaut⟩

end JGlue

end CFSG.GH74.GLS.C3.Layer1.Thm1
