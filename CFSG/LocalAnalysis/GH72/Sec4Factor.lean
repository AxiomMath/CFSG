module

public import CFSG.LocalAnalysis.GH72.Sec4Fusion
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.GH72

open Subgroup

namespace G4c

open CFSG.CGT.Foote81L6.TStruct (isElemAbelian_two_iff comm_of_mul_self)

section Basic

variable {G : Type*} [Group G]

theorem map_cj_centralizer (g : G) (K : Subgroup G) :
    (centralizer (K : Set G)).map (cj g) = centralizer ((K.map (cj g) : Subgroup G) : Set G) := by
  ext x
  rw [mem_map_cj, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro h _ ⟨k, hk, rfl⟩
    have e := h k hk
    rw [cj_apply]
    calc g * k * g⁻¹ * x = g * (k * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * k) * g⁻¹ := by rw [e]
      _ = x * (g * k * g⁻¹) := by group
  · intro h k hk
    have e := h (g * k * g⁻¹) (mem_map_of_mem (cj g) hk)
    calc k * (g⁻¹ * x * g) = g⁻¹ * ((g * k * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * k * g⁻¹)) * g := by rw [e]
      _ = g⁻¹ * x * g * k := by group

theorem le_normalizer_commutator' {K L N : Subgroup G} (hK : N ≤ normalizer (K : Set G))
    (hL : N ≤ normalizer (L : Set G)) : N ≤ normalizer ((⁅K, L⁆ : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_of_map_cj_eq ?_
  rw [map_cj_commutator, map_cj_eq_of_mem_normalizer (hK hg), map_cj_eq_of_mem_normalizer (hL hg)]

theorem le_xySup {X Y : Subgroup G} {f : G → G → Subgroup G} {x y : G} (hx : x ∈ X) (hx1 : x ≠ 1)
    (hy : y ∈ Y) (hy1 : y ≠ 1) : f x y ≤ xySup X Y f :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hx1
    (le_iSup_of_le y (le_iSup_of_le hy (le_iSup_of_le hy1 le_rfl)))))

theorem sq_eq_one_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V) {v : G} (hv : v ∈ V) :
    v ^ 2 = 1 := by
  have h := Monoid.pow_exponent_eq_one (⟨v, hv⟩ : V)
  rw [hV.exponent_two] at h
  simpa using congrArg Subtype.val h

theorem exists_mem_centralizer_of_commutator [Finite G] {T O : Subgroup G} (hT : IsPGroup 2 T)
    (hO : Odd (Nat.card O)) (hTO : T ≤ normalizer (O : Set G)) {k : G}
    (hk : k ∈ normalizer (O : Set G)) (hc : ∀ t ∈ T, t * k * t⁻¹ * k⁻¹ ∈ O) :
    ∃ c ∈ centralizer (T : Set G), c⁻¹ * k ∈ O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let α : T →* MulAut G := MulAut.conj.comp T.subtype
  let S : Set G := {x | k⁻¹ * x ∈ O}
  have hk' : k⁻¹ ∈ normalizer (O : Set G) := inv_mem hk
  have hS : ∀ t : T, ∀ x ∈ S, α t x ∈ S := by
    intro t x hx
    have hx' : k⁻¹ * x ∈ O := hx
    show k⁻¹ * ((t : G) * x * (t : G)⁻¹) ∈ O
    have h1 : k⁻¹ * ((t : G) * k * (t : G)⁻¹ * k⁻¹) * k⁻¹⁻¹ ∈ O :=
      (mem_normalizer_iff.mp hk' _).mp (hc t t.2)
    have h2 : (t : G) * (k⁻¹ * x) * (t : G)⁻¹ ∈ O := (mem_normalizer_iff.mp (hTO t.2) _).mp hx'
    have h3 : k⁻¹ * ((t : G) * x * (t : G)⁻¹) =
        (k⁻¹ * ((t : G) * k * (t : G)⁻¹ * k⁻¹) * k⁻¹⁻¹) * ((t : G) * (k⁻¹ * x) * (t : G)⁻¹) := by
      group
    rw [h3]
    exact mul_mem h1 h2
  have hcard : ¬ 2 ∣ Nat.card S := by
    have he : Nat.card S = Nat.card O := Nat.card_congr
      { toFun := fun x => ⟨k⁻¹ * x.1, x.2⟩
        invFun := fun o => ⟨k * o.1, by simp [S]⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun o => Subtype.ext (by simp) }
    rw [he]
    exact hO.not_two_dvd_nat
  obtain ⟨c, hcS, hfix⟩ :=
    CFSG.Semidihedral.Principal.CoprimeFixedPoint.exists_fixed_of_invariant 2 hT α S hS hcard
  refine ⟨c, mem_centralizer_iff.mpr fun t ht => ?_, ?_⟩
  · have h := hfix ⟨t, ht⟩
    change t * c * t⁻¹ = c at h
    calc t * c = t * c * t⁻¹ * t := by group
      _ = c * t := by rw [h]
  · have : c⁻¹ * k = (k⁻¹ * c)⁻¹ := by group
    rw [this]
    exact inv_mem hcS

variable [Finite G]

theorem le_commutator_sup_inf {V K : Subgroup G} (hV : IsPGroup 2 V)
    (hVK : V ≤ normalizer (K : Set G)) (hK : Odd (Nat.card K)) :
    K ≤ ⁅K, V⁆ ⊔ (K ⊓ centralizer (V : Set G)) :=
  (CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2 Nat.prime_two V K
    hV hVK (Nat.coprime_two_left.mpr hK)).ge

theorem le_iSup_inf_C {K V : Subgroup G} (hK : Odd (Nat.card K)) (hV : IsKleinFour V)
    (hVK : V ≤ normalizer (K : Set G)) : K ≤ ⨆ (v : G) (_ : v ∈ V) (_ : v ≠ 1), K ⊓ C v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hV
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_of_isKleinFour hV
  have ha2 : a * a = 1 := by rw [← pow_two]; exact sq_eq_one_of_isKleinFour hV ha
  obtain ⟨b, hb, hb1, hba⟩ : ∃ b ∈ V, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hle : V ≤ zpowers a := fun v hv => by
      by_cases hv1 : v = 1
      · rw [hv1]
        exact one_mem _
      · rw [h v hv hv1]
        exact mem_zpowers a
    have h4 : Nat.card V = 4 := IsKleinFour.card_four
    have hao : orderOf a = 2 := orderOf_eq_prime (sq_eq_one_of_isKleinFour hV ha) ha1
    have hc := card_le_of_le hle
    rw [h4, Nat.card_zpowers, hao] at hc
    omega
  have hab1 : a * b ≠ 1 := fun h => hba (by
    calc b = a * a * b := by rw [ha2, one_mul]
      _ = a * (a * b) := mul_assoc _ _ _
      _ = a := by rw [h, mul_one])
  have haab : a ≠ a * b := fun h => hb1 (by
    have := congrArg (a⁻¹ * ·) h
    simpa using this.symm)
  have hbab : b ≠ a * b := fun h => ha1 (by
    have := congrArg (· * b⁻¹) h
    simpa using this.symm)
  have hset := CFSG.ABGLocalTools.four_group_odd_eq_mul_centralizers (T := V) hK hVK ha hb
    (mul_mem ha hb) ha1 hb1 hab1 (Ne.symm hba) haab hbab
  set T := ⨆ (v : G) (_ : v ∈ V) (_ : v ≠ 1), K ⊓ C v with hT
  have hle : ∀ v ∈ V, v ≠ 1 → K ⊓ C v ≤ T := fun v hv hv1 =>
    le_iSup_of_le v (le_iSup_of_le hv (le_iSup_of_le hv1 le_rfl))
  intro w hw
  have hw' : w ∈ (K : Set G) := hw
  rw [hset] at hw'
  obtain ⟨_, ⟨x, hx, y, hy, rfl⟩, z, hz, rfl⟩ := hw'
  exact mul_mem (mul_mem (hle a ha ha1 hx) (hle b hb hb1 hy)) (hle _ (mul_mem ha hb) hab1 hz)

theorem le_sup_O_of_hasNormalTwoComplement {K : Subgroup G} (hK : HasNormalTwoComplement K)
    (P : Sylow 2 G) (hPK : (P : Subgroup G) ≤ K) : K ≤ (P : Subgroup G) ⊔ O K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNK, hNn, hNodd, n, hidx⟩ := hK
  have hNO : N ≤ O K := le_O_of_hasNormalTwoComplement ⟨N, hNK, hNn, hNodd, n, hidx⟩ hNK hNodd
  set J := (P : Subgroup G) ⊔ N with hJ
  have h1 : J.relIndex K ∣ 2 ^ n := by
    rw [← hidx]
    exact relIndex_dvd_of_le_left K le_sup_right
  have h2 : J.relIndex K ∣ (P : Subgroup G).index :=
    (relIndex_dvd_of_le_left K le_sup_left).trans (relIndex_dvd_index_of_le hPK)
  obtain ⟨m, hm⟩ := exists_eq_two_pow_of_dvd h1
  have hm0 : m = 0 := by
    by_contra hm0
    apply P.not_dvd_index
    rw [hm] at h2
    exact (dvd_pow_self 2 hm0).trans h2
  rw [hm0, pow_zero, relIndex_eq_one] at hm
  exact hm.trans (sup_le_sup_left hNO _)

theorem le_sup_centralizer_sup_O {H R V : Subgroup G} {F : Subgroup (Bar H)} (hRH : R ≤ H)
    (hVR : V ≤ R) (hV : IsPGroup 2 V) (hRF' : bar H R ⊔ F = ⊤)
    (hFR : F ≤ centralizer (bar H R : Set (Bar H))) :
    H ≤ R ⊔ (H ⊓ centralizer (V : Set G)) ⊔ O H := by
  have := bar_normal_of_sup hRF' hFR
  intro c hc
  have hc' : (QuotientGroup.mk' (CFSG.oddCore H) ⟨c, hc⟩ : Bar H) ∈ bar H R ⊔ F := by
    rw [hRF']
    exact mem_top _
  obtain ⟨_, ⟨s, hs, rfl⟩, f, hf, hrf⟩ := mem_sup_of_normal_left.mp hc'
  set k : H := s⁻¹ * ⟨c, hc⟩ with hk
  have hkf : QuotientGroup.mk' (CFSG.oddCore H) k = f := by
    rw [hk, map_mul, map_inv, ← hrf]
    group
  have hcomm : ∀ v ∈ V, v * (k : G) * v⁻¹ * (k : G)⁻¹ ∈ O H := by
    intro v hv
    set v' : H := ⟨v, hRH (hVR hv)⟩ with hv'
    have hv'R : QuotientGroup.mk' (CFSG.oddCore H) v' ∈ bar H R :=
      mem_map_of_mem _ (show (v' : G) ∈ R from hVR hv)
    have h1 : QuotientGroup.mk' (CFSG.oddCore H) v' * f = f * QuotientGroup.mk' _ v' :=
      mem_centralizer_iff.mp (hFR hf) _ hv'R
    have h2 : v' * k * v'⁻¹ * k⁻¹ ∈ CFSG.oddCore H := by
      rw [← QuotientGroup.ker_mk' (CFSG.oddCore H), MonoidHom.mem_ker, map_mul, map_mul, map_mul,
        map_inv, map_inv, hkf, h1]
      group
    exact ⟨_, h2, rfl⟩
  obtain ⟨c', hc'V, hc'O⟩ := exists_mem_centralizer_of_commutator hV (odd_card_O H)
    ((hVR.trans hRH).trans (le_normalizer_O H)) (le_normalizer_O H k.2) hcomm
  have hc'H : c' ∈ H := by
    have e : c' = (k : G) * (c'⁻¹ * k)⁻¹ := by group
    rw [e]
    exact mul_mem k.2 (inv_mem (O_le H hc'O))
  have hck : c = (s : G) * c' * (c'⁻¹ * k) := by
    rw [hk]
    push_cast
    group
  rw [hck]
  exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hs))
    (mem_sup_left (mem_sup_right ⟨hc'H, hc'V⟩))) (mem_sup_right hc'O)

end Basic

section Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem S_le_C_z₁z₂ : (𝔖.S : Subgroup G) ≤ C (𝔖.z₁ * 𝔖.z₂) := fun s hs =>
  mem_centralizer_singleton_iff.mpr (by
    have h1 := mem_centralizer_singleton_iff.mp (S_le_C_z₁ 𝔖 hs)
    have h2 := mem_centralizer_singleton_iff.mp (S_le_C_z₂ 𝔖 hs)
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc])

theorem le_normalizer_M₀ (A : Subgroup G) : 𝔖.M A ≤ normalizer ((𝔖.M₀ A : Subgroup G) : Set G) :=
  (le_inf (le_normalizer_commutator' (le_normalizer_O2 _) (le_normalizer_O2 _))
    (le_normalizer_O _)).trans (inf_normalizer_le_normalizer_sup _ _)

theorem le_normalizer_N₀ (A : Subgroup G) : 𝔖.N A ≤ normalizer ((𝔖.N₀ A : Subgroup G) : Set G) :=
  (le_inf (le_normalizer_commutator' (le_normalizer_O2 _) (le_normalizer_O2 _))
    (le_normalizer_O _)).trans (inf_normalizer_le_normalizer_sup _ _)

variable {𝔖} {A : Subgroup G}

omit [Finite G] in
theorem A_le_C (hA : IsE16 A) {a : G} (ha : a ∈ A) : A ≤ C a := fun _ hb =>
  mem_centralizer_singleton_iff.mpr (comm_of_mul_self (isElemAbelian_two_iff.1 hA.1) hb ha)

omit [Finite G] in
theorem isE16_map_cj (hA : IsE16 A) (g : G) : IsE16 (A.map (cj g)) := by
  refine ⟨isElemAbelian_two_iff.2 ?_, by rw [card_map_cj]; exact hA.2⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, isElemAbelian_two_iff.1 hA.1 x hx, map_one]

variable (hAS : A ≤ 𝔖.S) (hA : IsE16 A)

include hAS hA in
theorem map_cj_le_S {g : G} (hXg : (𝔖.X A).map (cj g) ≤ 𝔖.S₁) (hYg : (𝔖.Y A).map (cj g) ≤ 𝔖.S₂) :
    A.map (cj g) ≤ 𝔖.S := by
  rw [← (dd_e16_split _ _ _ 𝔖.decomp A hAS hA).1, map_cj_sup, S_eq]
  exact sup_le_sup hXg hYg

include hAS hA in
theorem X_map_cj {g : G} (hXg : (𝔖.X A).map (cj g) ≤ 𝔖.S₁) (hA'S : A.map (cj g) ≤ 𝔖.S) :
    𝔖.X (A.map (cj g)) = (𝔖.X A).map (cj g) := by
  have hle : (𝔖.X A).map (cj g) ≤ 𝔖.X (A.map (cj g)) := le_inf (map_mono X_le_A) hXg
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_cj, (isKleinFour_X hAS hA).card_four,
    (isKleinFour_X hA'S (isE16_map_cj hA g)).card_four]

include hAS hA in
theorem Y_map_cj {g : G} (hYg : (𝔖.Y A).map (cj g) ≤ 𝔖.S₂) (hA'S : A.map (cj g) ≤ 𝔖.S) :
    𝔖.Y (A.map (cj g)) = (𝔖.Y A).map (cj g) := by
  have hle : (𝔖.Y A).map (cj g) ≤ 𝔖.Y (A.map (cj g)) := le_inf (map_mono Y_le_A) hYg
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_cj, (isKleinFour_Y hAS hA).card_four,
    (isKleinFour_Y hA'S (isE16_map_cj hA g)).card_four]

omit hAS hA

theorem cover_C_of_conj {a z g : G} (hg : g * a * g⁻¹ = z)
    (hX : 𝔖.X (A.map (cj g)) = (𝔖.X A).map (cj g)) (hY : 𝔖.Y (A.map (cj g)) = (𝔖.Y A).map (cj g))
    (h : C z ≤ (C z ⊓ 𝔖.M₀ (A.map (cj g))) ⊔ (C z ⊓ 𝔖.N₀ (A.map (cj g))) ⊔
      (C z ⊓ normalizer ((A.map (cj g) : Subgroup G) : Set G)) ⊔ O (C z)) :
    C a ≤ (C a ⊓ 𝔖.M₀ A) ⊔ (C a ⊓ 𝔖.N₀ A) ⊔ (C a ⊓ normalizer (A : Set G)) ⊔ O (C a) := by
  have hCa : (C a).map (cj g) = C z := by rw [map_cj_C, hg]
  have hM : 𝔖.M (A.map (cj g)) = (𝔖.M A).map (cj g) := by
    show centralizer ((𝔖.X (A.map (cj g)) : Subgroup G) : Set G) =
      (centralizer ((𝔖.X A : Subgroup G) : Set G)).map (cj g)
    rw [hX, map_cj_centralizer]
  have hN : 𝔖.N (A.map (cj g)) = (𝔖.N A).map (cj g) := by
    show centralizer ((𝔖.Y (A.map (cj g)) : Subgroup G) : Set G) =
      (centralizer ((𝔖.Y A : Subgroup G) : Set G)).map (cj g)
    rw [hY, map_cj_centralizer]
  have hM₀ : 𝔖.M₀ (A.map (cj g)) = (𝔖.M₀ A).map (cj g) := by
    show ⁅O2 (𝔖.M (A.map (cj g))), O2 (𝔖.M (A.map (cj g)))⁆ ⊔ O (𝔖.M (A.map (cj g))) =
      (⁅O2 (𝔖.M A), O2 (𝔖.M A)⁆ ⊔ O (𝔖.M A)).map (cj g)
    rw [hM, map_cj_sup, map_cj_commutator, map_cj_O2, map_cj_O]
  have hN₀ : 𝔖.N₀ (A.map (cj g)) = (𝔖.N₀ A).map (cj g) := by
    show ⁅O2 (𝔖.N (A.map (cj g))), O2 (𝔖.N (A.map (cj g)))⁆ ⊔ O (𝔖.N (A.map (cj g))) =
      (⁅O2 (𝔖.N A), O2 (𝔖.N A)⁆ ⊔ O (𝔖.N A)).map (cj g)
    rw [hN, map_cj_sup, map_cj_commutator, map_cj_O2, map_cj_O]
  rw [hM₀, hN₀, ← map_cj_normalizer, ← hCa, ← map_cj_O] at h
  simp only [← map_cj_inf, ← map_cj_sup] at h
  exact (map_le_map_iff_of_injective (cj_injective g)).mp h

theorem cover_C_z₁ (hz : 𝔖.z₁ ∈ 𝔖.X A) {H₁ : Subgroup (Bar (C 𝔖.z₁))}
    (hRF' : bar (C 𝔖.z₁) 𝔖.S₁ ⊔ H₁ = ⊤)
    (hFR : H₁ ≤ centralizer (bar (C 𝔖.z₁) 𝔖.S₁ : Set (Bar (C 𝔖.z₁))))
    (hS₁ : 𝔖.S₁ ≤ 𝔖.N₀ A) (hM : 𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G))) :
    C 𝔖.z₁ ≤ (C 𝔖.z₁ ⊓ 𝔖.M₀ A) ⊔ (C 𝔖.z₁ ⊓ 𝔖.N₀ A) ⊔ (C 𝔖.z₁ ⊓ normalizer (A : Set G)) ⊔
      O (C 𝔖.z₁) := by
  refine (le_sup_centralizer_sup_O 𝔖.hz₁.2.2 (X_le_S₁ (A := A))
    ((isPGroup_S₁ 𝔖).to_le X_le_S₁) hRF' hFR).trans (sup_le (sup_le ?_ ?_) le_sup_right)
  · exact (le_inf 𝔖.hz₁.2.2 hS₁).trans (le_sup_right.trans (le_sup_left.trans le_sup_left))
  · have hMC : 𝔖.M A ≤ C 𝔖.z₁ := M_le_C hz
    refine inf_le_right.trans ?_
    show 𝔖.M A ≤ _
    rw [hM]
    exact sup_le ((le_inf (M₀_le_M.trans hMC) le_rfl).trans
      (le_sup_left.trans (le_sup_left.trans le_sup_left)))
      ((le_inf (inf_le_left.trans hMC) inf_le_right).trans (le_sup_right.trans le_sup_left))

theorem cover_C_z₂ (hz : 𝔖.z₂ ∈ 𝔖.Y A) {K₁ : Subgroup (Bar (C 𝔖.z₂))}
    (hRF' : bar (C 𝔖.z₂) 𝔖.S₂ ⊔ K₁ = ⊤)
    (hFR : K₁ ≤ centralizer (bar (C 𝔖.z₂) 𝔖.S₂ : Set (Bar (C 𝔖.z₂))))
    (hS₂ : 𝔖.S₂ ≤ 𝔖.M₀ A) (hN : 𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G))) :
    C 𝔖.z₂ ≤ (C 𝔖.z₂ ⊓ 𝔖.M₀ A) ⊔ (C 𝔖.z₂ ⊓ 𝔖.N₀ A) ⊔ (C 𝔖.z₂ ⊓ normalizer (A : Set G)) ⊔
      O (C 𝔖.z₂) := by
  refine (le_sup_centralizer_sup_O 𝔖.hz₂.2.2 (Y_le_S₂ (A := A))
    ((isPGroup_S₂ 𝔖).to_le Y_le_S₂) hRF' hFR).trans (sup_le (sup_le ?_ ?_) le_sup_right)
  · exact (le_inf 𝔖.hz₂.2.2 hS₂).trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  · have hNC : 𝔖.N A ≤ C 𝔖.z₂ := N_le_C hz
    refine inf_le_right.trans ?_
    show 𝔖.N A ≤ _
    rw [hN]
    exact sup_le ((le_inf (N₀_le_N.trans hNC) le_rfl).trans
      (le_sup_right.trans (le_sup_left.trans le_sup_left)))
      ((le_inf (inf_le_left.trans hNC) inf_le_right).trans (le_sup_right.trans le_sup_left))

theorem cover_C_z₁z₂ (h317 : HasNormalTwoComplement (C (𝔖.z₁ * 𝔖.z₂))) (hS₁ : 𝔖.S₁ ≤ 𝔖.N₀ A)
    (hS₂ : 𝔖.S₂ ≤ 𝔖.M₀ A) :
    C (𝔖.z₁ * 𝔖.z₂) ≤ (C (𝔖.z₁ * 𝔖.z₂) ⊓ 𝔖.M₀ A) ⊔ (C (𝔖.z₁ * 𝔖.z₂) ⊓ 𝔖.N₀ A) ⊔
      (C (𝔖.z₁ * 𝔖.z₂) ⊓ normalizer (A : Set G)) ⊔ O (C (𝔖.z₁ * 𝔖.z₂)) := by
  have hS := S_le_C_z₁z₂ 𝔖
  refine (le_sup_O_of_hasNormalTwoComplement h317 𝔖.S hS).trans (sup_le ?_ le_sup_right)
  rw [S_eq 𝔖]
  refine sup_le ?_ ?_
  · exact (le_inf (𝔖.decomp.le_left.trans hS) hS₁).trans
      (le_sup_right.trans (le_sup_left.trans le_sup_left))
  · exact (le_inf (𝔖.decomp.le_right.trans hS) hS₂).trans
      (le_sup_left.trans (le_sup_left.trans le_sup_left))

end Setting

end G4c

namespace Sec4Setting

open G4c
open CFSG.CGT.Foote81L6.TStruct (isElemAbelian_two_iff comm_of_mul_self)

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A)

include hAS hA in
theorem lemma_4_15_of
    (h315 : (∃ H₁ : Subgroup (Bar (C 𝔖.z₁)), bar (C 𝔖.z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧
        bar (C 𝔖.z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧ H₁ ≤ centralizer (bar (C 𝔖.z₁) 𝔖.S₁ : Set (Bar (C 𝔖.z₁))) ∧
        bar (C 𝔖.z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C 𝔖.z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C 𝔖.z₂)), bar (C 𝔖.z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧
        bar (C 𝔖.z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧ K₁ ≤ centralizer (bar (C 𝔖.z₂) 𝔖.S₂ : Set (Bar (C 𝔖.z₂))) ∧
        bar (C 𝔖.z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C 𝔖.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C 𝔖.z₂) 𝔖.S₁)))
    (h317 : HasNormalTwoComplement (C (𝔖.z₁ * 𝔖.z₂)))
    (hP2b5 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
        V ≤ normalizer (K : Set X) → IsCyclic K)
    (h47 : ∀ {A' : Subgroup G}, A' ≤ 𝔖.S → IsE16 A' →
      QuotIs (𝔖.M₀ A') (O (𝔖.M A')) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A') ∧
      𝔖.M A' = 𝔖.M₀ A' ⊔ (𝔖.M A' ⊓ normalizer (A' : Set G)) ∧
      𝔖.M A' = 𝔖.M₀ A' ⊔ (𝔖.M A' ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A', x ≠ 1 → O2 (C x) = (O2 (𝔖.M A') ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A', x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A' ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : ∀ {A' : Subgroup G}, A' ≤ 𝔖.S → IsE16 A' →
      QuotIs (𝔖.N₀ A') (O (𝔖.N A')) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A') ∧
      𝔖.N A' = 𝔖.N₀ A' ⊔ (𝔖.N A' ⊓ normalizer (A' : Set G)) ∧
      𝔖.N A' = 𝔖.N₀ A' ⊔ (𝔖.N A' ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A', y ≠ 1 → O2 (C y) = (O2 (𝔖.N A') ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A', y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A' ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (a : G) (ha : a ∈ A) (ha1 : a ≠ 1) :
    C a ≤ xySup (𝔖.X A) (𝔖.Y A) (fun x y => O (C a) ⊓ O (C x) ⊓ O (C y)) ⊔
      (C a ⊓ 𝔖.M₀ A) ⊔ (C a ⊓ 𝔖.N₀ A) ⊔ (C a ⊓ normalizer (A : Set G)) := by
  set D := xySup (𝔖.X A) (𝔖.Y A) (fun x y => O (C a) ⊓ O (C x) ⊓ O (C y)) with hD
  have hP1 : C a ≤ (C a ⊓ 𝔖.M₀ A) ⊔ (C a ⊓ 𝔖.N₀ A) ⊔ (C a ⊓ normalizer (A : Set G)) ⊔
      O (C a) := by
    obtain ⟨⟨H₁, -, hRF₁', hFR₁, -, -⟩, ⟨K₁, -, hRF₂', hFR₂, -, -⟩⟩ := h315
    by_cases haX : a ∈ 𝔖.X A
    · obtain ⟨g, hg, hXg, hYg⟩ := exists_conj_align hA ha
        (𝔖.fusion.conj₁ a ((mem_X 𝔖).mp haX).2 _ 𝔖.hz₁.1 (orderOf_eq_two hA ha ha1) 𝔖.hz₁.2.1)
        (S_le_C_z₁ 𝔖)
      have hA'S := map_cj_le_S hAS hA hXg hYg
      have hA' := isE16_map_cj hA g
      have hX' := X_map_cj hAS hA hXg hA'S
      have hz : 𝔖.z₁ ∈ 𝔖.X (A.map (cj g)) := by
        rw [hX', ← hg]
        exact mem_map_of_mem (cj g) haX
      exact cover_C_of_conj hg hX' (Y_map_cj hAS hA hYg hA'S)
        (cover_C_z₁ hz hRF₁' hFR₁ (h48 hA'S hA').2.1.le (h47 hA'S hA').2.2.1)
    by_cases haY : a ∈ 𝔖.Y A
    · obtain ⟨g, hg, hXg, hYg⟩ := exists_conj_align hA ha
        (𝔖.fusion.conj₂ a ((mem_Y 𝔖).mp haY).2 _ 𝔖.hz₂.1 (orderOf_eq_two hA ha ha1) 𝔖.hz₂.2.1)
        (S_le_C_z₂ 𝔖)
      have hA'S := map_cj_le_S hAS hA hXg hYg
      have hA' := isE16_map_cj hA g
      have hY' := Y_map_cj hAS hA hYg hA'S
      have hz : 𝔖.z₂ ∈ 𝔖.Y (A.map (cj g)) := by
        rw [hY', ← hg]
        exact mem_map_of_mem (cj g) haY
      exact cover_C_of_conj hg (X_map_cj hAS hA hXg hA'S) hY'
        (cover_C_z₂ hz hRF₂' hFR₂ (h47 hA'S hA').2.1.le (h48 hA'S hA').2.2.1)
    · obtain ⟨g, hg, hXg, hYg⟩ := exists_conj_align hA ha (isConj_z₁z₂ hAS hA ha haX haY)
        (S_le_C_z₁z₂ 𝔖)
      have hA'S := map_cj_le_S hAS hA hXg hYg
      have hA' := isE16_map_cj hA g
      exact cover_C_of_conj hg (X_map_cj hAS hA hXg hA'S) (Y_map_cj hAS hA hYg hA'S)
        (cover_C_z₁z₂ h317 (h48 hA'S hA').2.1.le (h47 hA'S hA').2.1.le)
  set T := D ⊔ (C a ⊓ 𝔖.M₀ A) ⊔ (C a ⊓ 𝔖.N₀ A) ⊔ (C a ⊓ normalizer (A : Set G)) with hT
  have hTD : D ≤ T := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hTM : C a ⊓ 𝔖.M₀ A ≤ T := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hTN : C a ⊓ 𝔖.N₀ A ≤ T := le_sup_right.trans le_sup_left
  have hTA : C a ⊓ normalizer (A : Set G) ≤ T := le_sup_right
  have hA_eq : 𝔖.X A ⊔ 𝔖.Y A = A := (dd_e16_split _ _ _ 𝔖.decomp A hAS hA).1
  have hNXY : normalizer (𝔖.X A : Set G) ⊓ normalizer (𝔖.Y A : Set G) ≤
      normalizer (A : Set G) := by
    have h := inf_normalizer_le_normalizer_sup (𝔖.X A) (𝔖.Y A)
    rwa [hA_eq] at h
  have hCXY : ∀ K : Subgroup G, K ≤ C a → K ≤ centralizer (𝔖.X A : Set G) →
      K ≤ centralizer (𝔖.Y A : Set G) → K ≤ T := fun K hKa hKX hKY =>
    (le_inf hKa ((le_inf (hKX.trans (centralizer_le_normalizer _))
      (hKY.trans (centralizer_le_normalizer _))).trans hNXY)).trans hTA
  have hAC : A ≤ C a := A_le_C hA ha
  have hOodd : Odd (Nat.card (O (C a))) := odd_card_O (C a)
  have hAN : A ≤ normalizer (O (C a) : Set G) := hAC.trans (le_normalizer_O _)
  have hXf := isKleinFour_X hAS hA
  have hYf := isKleinFour_Y hAS hA
  have hX2 : IsPGroup 2 (𝔖.X A) := (isPGroup_S₁ 𝔖).to_le X_le_S₁
  have hY2 : IsPGroup 2 (𝔖.Y A) := (isPGroup_S₂ 𝔖).to_le Y_le_S₂
  have hYX : 𝔖.Y A ≤ centralizer (𝔖.X A : Set G) := fun y hy => mem_centralizer_iff.mpr
    fun x hx => comm_of_mul_self (isElemAbelian_two_iff.1 hA.1) (X_le_A hx) (Y_le_A hy)
  have hXY : 𝔖.X A ≤ centralizer (𝔖.Y A : Set G) := fun x hx => mem_centralizer_iff.mpr
    fun y hy => comm_of_mul_self (isElemAbelian_two_iff.1 hA.1) (Y_le_A hy) (X_le_A hx)
  have h411 := lemma_4_11_of 𝔖 hAS hA h315 hP2b5
  have hS₂M₀ : 𝔖.S₂ ≤ 𝔖.M₀ A := (h47 hAS hA).2.1.le
  have hS₁N₀ : 𝔖.S₁ ≤ 𝔖.N₀ A := (h48 hAS hA).2.1.le
  have hP2 : O (C a) ≤ T := by
    refine (le_iSup_inf_C hOodd hXf (X_le_A.trans hAN)).trans
      (iSup_le fun x => iSup_le fun hx => iSup_le fun hx1 => ?_)
    refine (le_iSup_inf_C (odd_card_of_le inf_le_left hOodd) hYf
      ((le_inf (Y_le_A.trans hAN) (Y_le_A.trans ((A_le_C hA (X_le_A hx)).trans
        le_normalizer))).trans inf_normalizer_le_normalizer_inf)).trans
      (iSup_le fun y => iSup_le fun hy => iSup_le fun hy1 => ?_)
    set E := O (C a) ⊓ C x ⊓ C y with hE
    have hEO : E ≤ O (C a) := inf_le_left.trans inf_le_left
    have hEodd : Odd (Nat.card E) := odd_card_of_le hEO hOodd
    have hEx : E ≤ C x := inf_le_left.trans inf_le_right
    have hEy : E ≤ C y := inf_le_right
    have hEa : E ≤ C a := hEO.trans (O_le _)
    have hAE : A ≤ normalizer (E : Set G) :=
      (le_inf (le_inf hAN ((A_le_C hA (X_le_A hx)).trans le_normalizer))
        ((A_le_C hA (Y_le_A hy)).trans le_normalizer)).trans
        ((inf_le_inf_right _ inf_normalizer_le_normalizer_inf).trans
          inf_normalizer_le_normalizer_inf)
    have hXE : 𝔖.X A ≤ normalizer (E : Set G) := X_le_A.trans hAE
    have hYE : 𝔖.Y A ≤ normalizer (E : Set G) := Y_le_A.trans hAE
    have f1 := le_commutator_sup_inf hX2 hXE hEodd
    have hYEX : 𝔖.Y A ≤ normalizer
        ((E ⊓ centralizer (𝔖.X A : Set G) : Subgroup G) : Set G) :=
      (le_inf hYE (hYX.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
    have f2 := le_commutator_sup_inf hY2 hYEX (odd_card_of_le inf_le_left hEodd)
    have hYEX' : 𝔖.Y A ≤ normalizer ((⁅E, 𝔖.X A⁆ : Subgroup G) : Set G) :=
      le_normalizer_commutator' hYE (hYX.trans (centralizer_le_normalizer _))
    have hEXE : ⁅E, 𝔖.X A⁆ ≤ E := commutator_le_left_of_le_normalizer hXE
    have f3 := le_commutator_sup_inf hY2 hYEX' (odd_card_of_le hEXE hEodd)
    have hXEY : 𝔖.X A ≤ normalizer
        ((E ⊓ centralizer (𝔖.Y A : Set G) : Subgroup G) : Set G) :=
      (le_inf hXE (hXY.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
    have f4 := le_commutator_sup_inf hX2 hXEY (odd_card_of_le inf_le_left hEodd)
    have p1 : E ⊓ centralizer (𝔖.X A : Set G) ⊓ centralizer (𝔖.Y A : Set G) ≤ T :=
      hCXY _ (inf_le_left.trans (inf_le_left.trans hEa)) (inf_le_left.trans inf_le_right)
        inf_le_right
    have p1' : E ⊓ centralizer (𝔖.Y A : Set G) ⊓ centralizer (𝔖.X A : Set G) ≤ T :=
      hCXY _ (inf_le_left.trans (inf_le_left.trans hEa)) inf_le_right
        (inf_le_left.trans inf_le_right)
    have p2 : ⁅E ⊓ centralizer (𝔖.X A : Set G), 𝔖.Y A⁆ ≤ T := by
      refine (le_inf ?_ ?_).trans hTM
      · exact (commutator_le_left_of_le_normalizer hYEX).trans (inf_le_left.trans hEa)
      · exact (commutator_mono (inf_le_right : _ ≤ 𝔖.M A) (Y_le_S₂.trans hS₂M₀)).trans
          (commutator_le_right_of_le_normalizer (le_normalizer_M₀ 𝔖 A))
    have p3 : ⁅E ⊓ centralizer (𝔖.Y A : Set G), 𝔖.X A⁆ ≤ T := by
      refine (le_inf ?_ ?_).trans hTN
      · exact (commutator_le_left_of_le_normalizer hXEY).trans (inf_le_left.trans hEa)
      · exact (commutator_mono (inf_le_right : _ ≤ 𝔖.N A) (X_le_S₁.trans hS₁N₀)).trans
          (commutator_le_right_of_le_normalizer (le_normalizer_N₀ 𝔖 A))
    have p4 : ⁅⁅E, 𝔖.X A⁆, 𝔖.Y A⁆ ≤ T := by
      have hEXY : ⁅⁅E, 𝔖.X A⁆, 𝔖.Y A⁆ ≤ ⁅E, 𝔖.X A⁆ :=
        commutator_le_left_of_le_normalizer hYEX'
      refine (le_inf (le_inf (hEXY.trans (hEXE.trans hEO)) (hEXY.trans
        (le_sup_left.trans (h411.1 x hx hx1 E hEx hEodd hAE)))) ?_).trans
        ((le_xySup (f := fun x y => O (C a) ⊓ O (C x) ⊓ O (C y)) hx hx1 hy hy1).trans hTD)
      exact (commutator_mono hEXE le_rfl).trans
        (le_sup_left.trans (h411.2 y hy hy1 E hEy hEodd hAE))
    refine f1.trans (sup_le (f3.trans (sup_le p4 ?_)) (f2.trans (sup_le p2 p1)))
    exact (inf_le_inf_right _ hEXE).trans (f4.trans (sup_le p3 p1'))
  refine hP1.trans (sup_le ?_ hP2)
  exact sup_le (sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left))
    (le_sup_right.trans le_sup_left)) le_sup_right

end Sec4Setting

end CFSG.GH72
