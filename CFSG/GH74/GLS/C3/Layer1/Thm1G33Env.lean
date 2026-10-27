module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P310
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Aux
public import CFSG.GH74.GLS.C3.Layer1.Thm1GlueJ
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3A7

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1

structure Env33 {G : Type} [Group G] [Finite G] (x y : G) (K T V W : Subgroup G) (f z : G) :
    Prop where
  cfg : Cfg3 x y K T V W f z
  hsup : pumpJ K f = layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f)
  hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K
  hKuniq : ∀ K' : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G)) K' → K' = K
  hPK : IsSylowOf 2 (T ⊓ K) K
  hdih : ∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥(T ⊓ K) n
  hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z
  hfC : f ∈ centralizer ({x} : Set G)
  hfFaut : P34.IsFAutL2A7 (kBar K) (Back.actHom hKN ⟨f, hfC⟩)
  hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K))
  hAut : AutLevelF (kBar K)
  hQ2 : ∀ A : Subgroup G, A ≤ CMK (centralizer ({x} : Set G)) K → IsElementaryAbelian 2 ↥A →
    Nat.card ↥A ≤ 2
  hAutC : AutLevelC (kBar K)
  hxS : IsSylowOf 2 (zpowers x) (CxK x K)
  hJc : IsPCompIn 2 (centralizer ({f} : Set G)) (pumpJ K f)
  hJn : ∀ c ∈ centralizer ({f} : Set G), ∀ j ∈ pumpJ K f, c * j * c⁻¹ ∈ pumpJ K f
  hr : ∃ r : ℕ, Odd r ∧ 5 ≤ r ∧ HasL2Model (kBar (layerI K f)) (fun q => q = r) ∧
    (HasL2Model (kBar K) (fun q => q = r ^ 2) ∨
      (r = 5 ∧ Nonempty (kBar K ≃* alternatingGroup (Fin 7))))
  hshape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))

section Facts

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

theorem Env33.hV2 (E : Env33 x y K T V W f z) : IsPGroup 2 ↥V := E.cfg.sylowV.isPGroup

theorem Env33.hVC (E : Env33 x y K T V W f z) : V ≤ centralizer ({f} : Set G) :=
  E.cfg.sylowV.le

theorem Env33.hVf (E : Env33 x y K T V W f z) : ∀ v ∈ V, v * f = f * v := fun _ hv =>
  mem_centralizer_singleton_iff.1 (E.hVC hv)

theorem Env33.hfP (E : Env33 x y K T V W f z) : ∀ p ∈ T ⊓ K, f * p = p * f :=
  E.cfg.mem.2.2.1

theorem Env33.hPV (E : Env33 x y K T V W f z) : T ⊓ K ≤ V := fun p hp =>
  E.cfg.CTf_le p hp.1 (E.hfP p hp)

theorem Env33.hz2 (E : Env33 x y K T V W f z) : orderOf z = 2 := E.cfg.z_mem.2.1

theorem Env33.hzP (E : Env33 x y K T V W f z) : z ∈ T ⊓ K := E.cfg.z_mem.1

theorem Env33.hxD (E : Env33 x y K T V W f z) : x ∈ secD K f V := E.cfg.x_mem_secD E.hsup E.hJn

theorem Env33.hfD (E : Env33 x y K T V W f z) : f ∈ secD K f V := E.cfg.f_mem_secD E.hsup E.hJn

theorem Env33.hDV (_E : Env33 x y K T V W f z) : secD K f V ≤ V := inf_le_left

theorem Env33.hDeq (E : Env33 x y K T V W f z) :
    secD K f V = V ⊓ CMK (centralizer ({f} : Set G)) (pumpJ K f) :=
  secD_eq_inf_cmk E.hsup E.hVC

theorem Env33.hDn (E : Env33 x y K T V W f z) :
    ∀ v ∈ V, ∀ d ∈ secD K f V, v * d * v⁻¹ ∈ secD K f V := by
  intro v hv d hd
  rw [E.hDeq] at hd ⊢
  exact ⟨V.mul_mem (V.mul_mem hv hd.1) (V.inv_mem hv), P34Real.CMK_conj E.hJn (E.hVC hv) hd.2⟩

theorem Env33.hJdata (E : Env33 x y K T V W f z) :
    ∃ r : ℕ, Odd r ∧ 5 ≤ r ∧ HasL2Model (kBar (pumpJ K f)) (fun q => q = r) ∧
      ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = r ∧ L2Field F₀ ∧
        Nonempty (kBar (pumpJ K f) ≃* L2 F₀) := by
  obtain ⟨r, hrodd, hr5, hI, -⟩ := E.hr
  obtain ⟨eIJ⟩ := kBar_pumpJ_equiv E.hsup
  have hJmodel : HasL2Model (kBar (pumpJ K f)) (fun q => q = r) :=
    TwoThin.hasL2Model_of_mulEquiv eIJ hI
  exact ⟨r, hrodd, hr5, hJmodel, exists_l2_model_card hrodd hr5 hJmodel⟩

theorem Env33.hcenJ (E : Env33 x y K T V W f z) :
    Function.Injective
      (MulAut.conj : kBar (pumpJ K f) →* MulAut (kBar (pumpJ K f))) := by
  obtain ⟨r, -, -, -, F₀, _, _, -, -, ⟨e₀⟩⟩ := E.hJdata
  exact IVK.conj_injective_of_L2 e₀

theorem Env33.hzI (E : Env33 x y K T V W f z) : z ∈ layerI K f := by
  obtain ⟨r, hrodd, -, hI, -⟩ := E.hr
  exact z_mem_layerI E.hPK E.hfP hI hrodd E.hzu

theorem Env33.hzD (E : Env33 x y K T V W f z) : z ∉ secD K f V :=
  z_not_mem_secD E.hsup E.hJn E.hcenJ E.hzI E.hz2

theorem Env33.hPD (E : Env33 x y K T V W f z) : (T ⊓ K) ⊓ secD K f V = ⊥ := by
  by_contra hne
  obtain ⟨w, ⟨hwP, hwD⟩, hw1, hwc⟩ := exists_central_of_normal' (U := (T ⊓ K) ⊓ secD K f V)
    (B := T ⊓ K) hne inf_le_left
    (fun b hb u hu => ⟨(T ⊓ K).mul_mem ((T ⊓ K).mul_mem hb hu.1) ((T ⊓ K).inv_mem hb),
      E.hDn b (E.hPV hb) u hu.2⟩) (E.hV2.to_le E.hPV)
  rcases E.hzu w hwP (fun p hp => (hwc p hp).symm) with h | h
  · exact hw1 h
  · exact E.hzD (h ▸ hwD)

theorem Env33.hPeq (E : Env33 x y K T V W f z) : V ⊓ K = T ⊓ K :=
  E.hPK.eq_of_le (le_inf E.hPV E.hPK.le) inf_le_right E.hV2.to_inf_left

theorem Env33.hSnorm (E : Env33 x y K T V W f z) :
    ∀ s ∈ V, s * x = x * s → ∀ p ∈ T ⊓ K, s * p * s⁻¹ ∈ T ⊓ K := by
  intro s hs hsx p hp
  rw [← E.hPeq] at hp ⊢
  have hsC : s ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hsx
  exact ⟨V.mul_mem (V.mul_mem hs hp.1) (V.inv_mem hs), E.hKN s hsC p hp.2⟩

theorem Env33.hCDx (E : Env33 x y K T V W f z) :
    ∀ d ∈ secD K f V, d * x = x * d → ∀ p ∈ T ⊓ K, d * p = p * d := by
  intro d hd hdx p hp
  have h1 : d * p * d⁻¹ * p⁻¹ ∈ (T ⊓ K) ⊓ secD K f V := by
    refine ⟨?_, ?_⟩
    · have : d * p * d⁻¹ * p⁻¹ = (d * p * d⁻¹) * p⁻¹ := rfl
      rw [this]
      exact (T ⊓ K).mul_mem (E.hSnorm d (E.hDV hd) hdx p hp) ((T ⊓ K).inv_mem hp)
    · have : d * p * d⁻¹ * p⁻¹ = d * (p * d⁻¹ * p⁻¹) := by group
      rw [this]
      exact (secD K f V).mul_mem hd (E.hDn p (E.hPV hp) d⁻¹ ((secD K f V).inv_mem hd))
  rw [E.hPD, Subgroup.mem_bot] at h1
  calc d * p = (d * p * d⁻¹ * p⁻¹) * (p * d) := by group
    _ = p * d := by rw [h1, one_mul]

theorem Env33.hfout (E : Env33 x y K T V W f z) :
    Back.actHom E.hKN ⟨f, E.hfC⟩ ∉ innAut (kBar K) :=
  not_mem_innAut_of_isFAutL2A7 E.hfFaut

end Facts

theorem cent_le_of_secD' {G : Type} [Group G] [Finite G] {x f : G} {K V P D : Subgroup G}
    (hKC : K ≤ centralizer ({x} : Set G))
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hPK : IsSylowOf 2 P K)
    (hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)))
    (hAutC : AutLevelC (kBar K)) (hPdih : ∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥P n)
    (hfC : f ∈ centralizer ({x} : Set G)) (hf2 : orderOf f = 2) (hfP : ∀ p ∈ P, f * p = p * f)
    (hfout : Back.actHom hKN ⟨f, hfC⟩ ∉ innAut (kBar K))
    (hxS : IsSylowOf 2 (zpowers x) (CxK x K))
    (hV2 : IsPGroup 2 ↥V) (hVf : ∀ v ∈ V, v * f = f * v) (hDV : D ≤ V) (hxD : x ∈ D)
    (hfD : f ∈ D) (hPD : P ⊓ D = ⊥)
    (hcomm : ∀ d ∈ D, d * x = x * d → ∀ p ∈ P, p * d = d * p) :
    ∀ d ∈ D, d * x = x * d → d ∈ zpowers x ⊔ zpowers f := by
  intro d hd hdx
  have hdC : d ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hdx
  have hd2 : ∃ k : ℕ, d ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hV2 ⟨d, hDV hd⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨z₀, hz₀P, a, b, hmem⟩ := exists_mul_mem_cmk_of_centralizes hKC hKN hPK hcen hAutC
    hPdih hfC hf2 hfP hfout hdC hd2 (fun p hp => (hcomm d hd hdx p hp).symm) (hVf d (hDV hd))
  have hz₀2 : ∃ k : ℕ, z₀ ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hPK.isPGroup ⟨z₀, hz₀P⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hff2 : ∃ k : ℕ, f ^ (2 ^ k) = 1 :=
    ⟨1, by rw [pow_one]; have := pow_orderOf_eq_one f; rwa [hf2] at this⟩
  have hdz : Commute d z₀ := (hcomm d hd hdx z₀ hz₀P).symm
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

section Facts2

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

theorem Env33.hCx (E : Env33 x y K T V W f z) :
    ∀ d ∈ secD K f V, d * x = x * d → d ∈ zpowers x ⊔ zpowers f :=
  cent_le_of_secD' E.cfg.hKx E.hKN E.hPK E.hcen E.hAutC (E.hdih) E.hfC E.cfg.hf2 E.hfP E.hfout
    E.hxS E.hV2 E.hVf E.hDV E.hxD E.hfD E.hPD
    (fun d hd hdx p hp => (E.hCDx d hd hdx p hp).symm)

end Facts2

theorem factorization_kBar {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    (Nat.card ↥H).factorization 2 = (Nat.card (kBar H)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card ↥H = Nat.card (pPrimeCore 2 ↥H) * Nat.card (kBar H) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥H), mul_comm]
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rw [hK, Thm1L3A7.factorization_two_mul_odd hodd Nat.card_pos.ne']

theorem layerI_conj {G : Type} [Group G] [Finite G] {K : Subgroup G} {f : G} :
    ∀ g ∈ K ⊓ centralizer ({f} : Set G), ∀ i ∈ layerI K f, g * i * g⁻¹ ∈ layerI K f := by
  intro g hg i hi
  have h : (MulAut.conj g) i ∈ pLayerOf 2 (K ⊓ centralizer ({f} : Set G)) :=
    Stage1.Thm2.Recip.pLayerOf_map_conj_le hg ⟨i, hi, rfl⟩
  rw [MulAut.conj_apply] at h
  exact h

section Facts3

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

theorem Env33.hPI (E : Env33 x y K T V W f z) :
    IsSylowOf 2 ((T ⊓ K) ⊓ layerI K f) (layerI K f) := by
  have hPX : T ⊓ K ≤ K ⊓ centralizer ({f} : Set G) :=
    le_inf E.hPK.le (fun p hp => mem_centralizer_singleton_iff.2 (E.hfP p hp).symm)
  have hPXsyl : IsSylowOf 2 (T ⊓ K) (K ⊓ centralizer ({f} : Set G)) :=
    isSylowOf_of_le E.hPK hPX inf_le_left
  exact hPXsyl.inf_of_le_normalizer (TwoThin.pLayerOf_le 2 _)
    (fun g hg => Thm1L3.mem_normalizer_of_conj_le (layerI_conj g hg))

theorem Env33.hVJ (E : Env33 x y K T V W f z) :
    IsSylowOf 2 (V ⊓ pumpJ K f) (pumpJ K f) :=
  E.cfg.sylowV.inf_of_le_normalizer E.hJc.1
    (fun g hg => Thm1L3.mem_normalizer_of_conj_le (E.hJn g hg))

theorem Env33.hVJeq (E : Env33 x y K T V W f z) :
    V ⊓ pumpJ K f = (T ⊓ K) ⊓ layerI K f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eIJ⟩ := kBar_pumpJ_equiv E.hsup
  have hle : (T ⊓ K) ⊓ layerI K f ≤ V ⊓ pumpJ K f :=
    inf_le_inf E.hPV (layerI_le_pumpJ K f)
  have hcard : Nat.card ↥(V ⊓ pumpJ K f) ≤ Nat.card ↥((T ⊓ K) ⊓ layerI K f) := by
    rw [E.hVJ.card_eq, E.hPI.card_eq, factorization_kBar (pumpJ K f), factorization_kBar (layerI K f),
      Nat.card_congr eIJ.toEquiv]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem Env33.hP1n (E : Env33 x y K T V W f z) :
    ∀ v ∈ V, ∀ u ∈ (T ⊓ K) ⊓ layerI K f, v * u * v⁻¹ ∈ (T ⊓ K) ⊓ layerI K f := by
  intro v hv u hu
  rw [← E.hVJeq] at hu ⊢
  exact ⟨V.mul_mem (V.mul_mem hv hu.1) (V.inv_mem hv), E.hJn v (E.hVC hv) u hu.2⟩

theorem Env33.hzZ (E : Env33 x y K T V W f z) : z ∈ zCenter V := by
  have hz1 : z ≠ 1 := fun h => by have := E.hz2; rw [h, orderOf_one] at this; omega
  have hne : (T ⊓ K) ⊓ layerI K f ≠ ⊥ := by
    intro h
    have : z ∈ (T ⊓ K) ⊓ layerI K f := ⟨E.hzP, E.hzI⟩
    rw [h, Subgroup.mem_bot] at this
    exact hz1 this
  obtain ⟨w, ⟨hwP, hwI⟩, hw1, hwc⟩ := exists_central_of_normal' (U := (T ⊓ K) ⊓ layerI K f)
    (B := V) hne (inf_le_left.trans E.hPV) E.hP1n E.hV2
  have hwz : w = z := by
    rcases E.hzu w hwP (fun p hp => (hwc p (E.hPV hp)).symm) with h | h
    · exact absurd h hw1
    · exact h
  subst hwz
  exact ⟨E.hPV hwP, fun h hh => hwc h hh⟩

theorem Env33.hZVle (E : Env33 x y K T V W f z) :
    ∀ w ∈ zCenter V, w ∈ zpowers z ⊔ zpowers f ⊔ zpowers x := by
  intro w hw
  have hwV : w ∈ V := hw.1
  have hwx : w * x = x * w := (hw.2 x E.cfg.x_mem_V).symm
  have hwC : w ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hwx
  have hw2 : ∃ k : ℕ, w ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.hV2 ⟨w, hwV⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨z₀, hz₀P, a, b, hmem⟩ := exists_mul_mem_cmk_of_centralizes E.cfg.hKx E.hKN E.hPK E.hcen
    E.hAutC E.hdih E.hfC E.cfg.hf2 E.hfP E.hfout hwC hw2
    (fun p hp => (hw.2 p (E.hPV hp)).symm) (E.hVf w hwV)
  have hz₀2 : ∃ k : ℕ, z₀ ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.hPK.isPGroup ⟨z₀, hz₀P⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hff2 : ∃ k : ℕ, f ^ (2 ^ k) = 1 :=
    ⟨1, by rw [pow_one]; have := pow_orderOf_eq_one f; rwa [E.cfg.hf2] at this⟩
  have hwz : Commute w z₀ := (hw.2 z₀ (E.hPV hz₀P)).symm
  have hwf : Commute w f := E.hVf w hwV
  have hzf : Commute z₀ f := (E.hfP z₀ hz₀P).symm
  have hwz2 : ∃ k : ℕ, (w * z₀ ^ a) ^ (2 ^ k) = 1 :=
    two_elt_mul (hwz.zpow_right a) hw2 (two_elt_zpow hz₀2 a)
  have hc₂ : ∃ k : ℕ, (w * z₀ ^ a * f ^ b) ^ (2 ^ k) = 1 :=
    two_elt_mul (Commute.mul_left (hwf.zpow_right b) ((hzf.zpow_left a).zpow_right b)) hwz2
      (two_elt_zpow hff2 b)
  have hc₀ : w * z₀ ^ a * f ^ b ∈ zpowers x :=
    mem_zpowers_of_two_element E.hxS (fun k hk => mem_centralizer_singleton_iff.1 hk.1) hmem hc₂
  have hxP : ∀ q ∈ T ⊓ K, ∀ c ∈ zpowers x, c * q = q * c := by
    intro q hq c hc
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hc
    have hqx : q * x = x * q := mem_centralizer_singleton_iff.1 (E.cfg.hKx hq.2)
    exact (Commute.zpow_left (show Commute x q from hqx.symm) m).eq
  have hu : z₀ ^ a = w⁻¹ * (w * z₀ ^ a * f ^ b) * (f ^ b)⁻¹ := by group
  have hucomm : ∀ q ∈ T ⊓ K, z₀ ^ a * q = q * z₀ ^ a := by
    intro q hq
    have h1 : Commute w q := (hw.2 q (E.hPV hq)).symm
    have h2 : Commute (w * z₀ ^ a * f ^ b) q := hxP q hq _ hc₀
    have h3 : Commute f q := E.hfP q hq
    rw [hu]
    exact ((h1.inv_left.mul_left h2).mul_left (h3.zpow_left b).inv_left).eq
  have huP : z₀ ^ a ∈ T ⊓ K := (T ⊓ K).zpow_mem hz₀P a
  have hmem' : w = (w * z₀ ^ a * f ^ b) * (f ^ b)⁻¹ * (z₀ ^ a)⁻¹ := by group
  have hA : w * z₀ ^ a * f ^ b ∈ zpowers z ⊔ zpowers f ⊔ zpowers x := Subgroup.mem_sup_right hc₀
  have hB : (f ^ b)⁻¹ ∈ zpowers z ⊔ zpowers f ⊔ zpowers x :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right
      ((zpowers f).inv_mem ((zpowers f).zpow_mem (mem_zpowers f) b)))
  have hC : (z₀ ^ a)⁻¹ ∈ zpowers z ⊔ zpowers f ⊔ zpowers x := by
    rcases E.hzu (z₀ ^ a) huP (fun q hq => hucomm q hq) with h | h
    · rw [h, inv_one]; exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left ((zpowers z).inv_mem (mem_zpowers z)))
  have hfin := Subgroup.mul_mem _ (Subgroup.mul_mem _ hA hB) hC
  rwa [← hmem'] at hfin

theorem Env33.hx2 (E : Env33 x y K T V W f z) : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [E.cfg.hx2, sq] at this

theorem Env33.hf2' (E : Env33 x y K T V W f z) : f * f = 1 := by
  have := pow_orderOf_eq_one f
  rwa [E.cfg.hf2, sq] at this

theorem Env33.hz2' (E : Env33 x y K T V W f z) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [E.hz2, sq] at this

theorem Env33.hx1 (E : Env33 x y K T V W f z) : x ≠ 1 := fun h => by
  have := E.cfg.hx2; rw [h, orderOf_one] at this; omega

theorem Env33.hf1 (E : Env33 x y K T V W f z) : f ≠ 1 := fun h => by
  have := E.cfg.hf2; rw [h, orderOf_one] at this; omega

theorem Env33.hz1 (E : Env33 x y K T V W f z) : z ≠ 1 := fun h => by
  have := E.hz2; rw [h, orderOf_one] at this; omega

theorem Env33.hxf_ne (E : Env33 x y K T V W f z) : x ≠ f := Ne.symm E.cfg.mem.2.2.2.1

theorem Env33.hxcommK (E : Env33 x y K T V W f z) : ∀ q ∈ K, q * x = x * q := fun _ hq =>
  mem_centralizer_singleton_iff.1 (E.cfg.hKx hq)

theorem Env33.hDshape (E : Env33 x y K T V W f z) :
    P34.IsMaximalClassTwoGroup ↥(secD K f V) ∧
      ((Nat.card ↥(secD K f V) = 4 ∧ secD K f V = zpowers x ⊔ zpowers f) ∨
        ∃ a ∈ secD K f V, (∀ v ∈ V, v * a * v⁻¹ ∈ zpowers a) ∧ 4 ∣ orderOf a ∧
          x ∉ zpowers a ∧ (∀ d ∈ secD K f V, d ∈ zpowers a ∨ x⁻¹ * d ∈ zpowers a) ∧
          f ∈ zpowers a) :=
  secD_shape (E.hV2.to_le E.hDV) E.hDn E.hxD E.cfg.hx2 E.hfD E.cfg.hf2 E.cfg.hxf E.hxf_ne E.hCx
    (fun d hd => E.hVf d (E.hDV hd))

theorem Env33.hkleinCard (E : Env33 x y K T V W f z) : Nat.card ↥(zpowers x ⊔ zpowers f) = 4 :=
  P89.card_klein (by rw [sq]; exact E.hx2) (by rw [sq]; exact E.hf2') E.cfg.hxf E.hx1 E.hf1 E.hxf_ne

theorem Env33.hx_not_cent (E : Env33 x y K T V W f z) (h8 : 8 ≤ Nat.card ↥(secD K f V)) :
    ∃ d ∈ secD K f V, d * x ≠ x * d := by
  by_contra hcon
  push Not at hcon
  have hle : secD K f V ≤ zpowers x ⊔ zpowers f := fun d hd => E.hCx d hd (hcon d hd)
  have := Subgroup.card_le_of_le hle
  rw [E.hkleinCard] at this
  omega

theorem Env33.hZD (E : Env33 x y K T V W f z) (h8 : 8 ≤ Nat.card ↥(secD K f V)) :
    zCenter (secD K f V) = zpowers f := by
  apply le_antisymm
  · intro w hw
    have hfZ : f ∈ zCenter (secD K f V) := ⟨E.hfD, fun h hh => E.hVf h (E.hDV hh)⟩
    have hwD : w ∈ secD K f V := hw.1
    have hwx : w * x = x * w := (hw.2 x E.hxD).symm
    have hxZ : w = x ∨ w = x * f → False := by
      intro hh
      obtain ⟨d, hd, hdx⟩ := E.hx_not_cent h8
      apply hdx
      have hxZ' : x ∈ zCenter (secD K f V) := by
        rcases hh with h | h
        · rw [h] at hw; exact hw
        · rw [h] at hw
          have : x = x * f * f⁻¹ := by group
          rw [this]
          exact (zCenter (secD K f V)).mul_mem hw ((zCenter (secD K f V)).inv_mem hfZ)
      exact hxZ'.2 d hd
    rcases klein_cases E.hx2 E.hf2' E.cfg.hxf (E.hCx w hwD hwx) with h | h | h | h
    · rw [h]; exact (zpowers f).one_mem
    · exact (hxZ (Or.inl h)).elim
    · rw [h]; exact mem_zpowers f
    · exact (hxZ (Or.inr h)).elim
  · exact (zpowers_le).2 ⟨E.hfD, fun h hh => E.hVf h (E.hDV hh)⟩

theorem Env33.hZV (E : Env33 x y K T V W f z) (h8 : 8 ≤ Nat.card ↥(secD K f V)) :
    zCenter V = zpowers z ⊔ zpowers f := by
  have hfZ : f ∈ zCenter V := ⟨E.cfg.f_mem_V, fun v hv => E.hVf v hv⟩
  apply le_antisymm
  · intro w hw
    have hM : zpowers z ⊔ zpowers f ≤ centralizer ({x} : Set G) := by
      refine sup_le ((zpowers_le).2 ?_) ((zpowers_le).2 ?_)
      · exact mem_centralizer_singleton_iff.2 (E.hxcommK z E.hzP.2)
      · exact mem_centralizer_singleton_iff.2 E.cfg.hxf.symm
    obtain ⟨m, hm, c, hc, hwmc⟩ := Thm1P310.exists_mul_of_mem_sup
      (P := zpowers z ⊔ zpowers f) (D := zpowers x)
      (fun p hp d hd => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hd
        have hpx : p * x = x * p := mem_centralizer_singleton_iff.1 (hM hp)
        exact (Commute.zpow_right (show Commute p x from hpx) k).eq)
      (E.hZVle w hw)
    rcases Thm1P310.eq_one_or_eq_of_mem_zpowers E.hx2 hc with h | h
    · rw [hwmc, h, mul_one]; exact hm
    · exfalso
      have hmZ : m ∈ zCenter V := by
        have : zpowers z ⊔ zpowers f ≤ zCenter V :=
          sup_le ((zpowers_le).2 E.hzZ) ((zpowers_le).2 hfZ)
        exact this hm
      have hxZ : x ∈ zCenter V := by
        have : x = m⁻¹ * w := by rw [hwmc, h]; group
        rw [this]
        exact (zCenter V).mul_mem ((zCenter V).inv_mem hmZ) hw
      obtain ⟨d, hd, hdx⟩ := E.hx_not_cent h8
      exact hdx ((hxZ.2 d (E.hDV hd)))
  · exact sup_le ((zpowers_le).2 E.hzZ) ((zpowers_le).2 hfZ)

end Facts3

end CFSG.GH74.GLS.C3.Layer1.Thm1G33
