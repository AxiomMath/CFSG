module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeCompl
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModels
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step46
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open Subgroup CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.Hexa
open CFSG.Monster.B.Co2 CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section Transport

variable {P G : Type*} [Group P] [Group G] {H : Subgroup P} {K : Subgroup G}

theorem mem_map_comap_iff (f : ↥H ≃* ↥K) (Y : Subgroup G) (p : P) :
    p ∈ ((Y.subgroupOf K).comap f.toMonoidHom).map H.subtype ↔
      ∃ hp : p ∈ H, ((f ⟨p, hp⟩ : ↥K) : G) ∈ Y := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.2, mem_subgroupOf.mp hq⟩
  · rintro ⟨hp, h⟩
    exact ⟨⟨p, hp⟩, mem_subgroupOf.mpr h, rfl⟩

theorem card_map_comap (f : ↥H ≃* ↥K) {Y : Subgroup G} (hYK : Y ≤ K) :
    Nat.card (((Y.subgroupOf K).comap f.toMonoidHom).map H.subtype) = Nat.card Y := by
  rw [card_map_of_injective H.subtype_injective, comap_equiv_eq_map_symm',
    card_map_of_injective f.symm.injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hYK).toEquiv

theorem card_centralizer_subtype (h : ↥H) :
    Nat.card (centralizer ({h} : Set ↥H)) = Nat.card (H ⊓ centralizer ({(h : P)} : Set P) :
      Subgroup P) := by
  have heq : (centralizer ({h} : Set ↥H)).map H.subtype =
      H ⊓ centralizer ({(h : P)} : Set P) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)
      simpa using this
    · rintro ⟨hxH, hx⟩
      refine ⟨⟨x, hxH⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
      simpa using mem_centralizer_singleton_iff.mp hx
  rw [← heq, card_map_of_injective H.subtype_injective]

theorem mem_normalizer_of_forall [Finite P] {H₀ : Subgroup P} {c : P}
    (h : ∀ x ∈ H₀, c * x * c⁻¹ ∈ H₀) : c ∈ normalizer (H₀ : Set P) := by
  rw [mem_normalizer_iff_map_conj_eq]
  refine eq_of_le_of_card_ge ?_ (le_of_eq (card_map_of_injective (MulAut.conj c).injective).symm)
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

end Transport

section Inner

variable {G : Type*} [Group G] {L : Subgroup G}

theorem mem_iff_of_conj {H₀ : Subgroup (Equiv.Perm (Fin 64))} {c : ↥heN0}
    (hc : (c : Equiv.Perm (Fin 64)) ∈ normalizer (H₀ : Set (Equiv.Perm (Fin 64)))) (n : ↥heN0) :
    ((MulAut.conj c n : ↥heN0) : Equiv.Perm (Fin 64)) ∈ H₀ ↔ (n : Equiv.Perm (Fin 64)) ∈ H₀ := by
  rw [MulAut.conj_apply]
  simp only [coe_mul, coe_inv]
  exact ((mem_normalizer_iff.mp hc) n).symm

end Inner

theorem commute_iff_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a b : A) :
    a * b = b * a ↔ e a * e b = e b * e a := by
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

section Norm

variable {G : Type} [Group G] [Finite G]

theorem exists_normX_P12 (hF : HexaFacts) (hM : HeModelFacts) {X : Subgroup G} {z : G}
    (ι : ↥X ≃* ↥hexaT) (ψ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))) →* ↥hexaM)
    (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = X.subgroupOf (AS76b.oUpperTwoPrime (normalizer (X : Set G))))
    (hequiv : ∀ (ℓ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G)))) (x y : ↥X),
      (y : G) = ℓ * x * (ℓ : G)⁻¹ →
        (ι y : Equiv.Perm (Fin 64)) = ψ ℓ * ι x * (ψ ℓ : Equiv.Perm (Fin 64))⁻¹)
    (hX2 : ∀ x ∈ X, x * x = 1) (hX64 : Nat.card X = 64) (hzX : z ∈ X) (hz1 : z ≠ 1)
    (hCz : Nat.card (centralizer ({z} : Set G)) = 21504) :
    ∃ f : ↥heN0 ≃* ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))),
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) = hexaT0P ↔ (f n : G) = z) ∧
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ hexaT ↔ (f n : G) ∈ X) ∧
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP12 ↔ (f n : G) ∈ iX z X) ∧
      ∃ d : ↥heN0, ∀ (t : Equiv.Perm (Fin 64)) (ht : t ∈ hexaT),
        ((f (d * ⟨t, mem_sup_left ht⟩ * d⁻¹) : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G)))) :
          G) = ι.symm ⟨t, ht⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXL : X ≤ AS76b.oUpperTwoPrime (normalizer (X : Set G)) :=
    le_oUpper_of_card le_normalizer (n := 6) (by rw [hX64]; norm_num)
  obtain ⟨-, f, -, -, -, -, hfT, -⟩ := exists_mulEquiv_hexa hF hXL hX2 ι ψ hψs hψk hequiv
    hM.zeta_mem hM.zeta_pow hM.zeta_ne hM.zeta_fix hM.zeta_normal hM.T_inf_M
  have hfX : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ hexaT ↔ (f n : G) ∈ X := by
    intro n
    constructor
    · intro hn
      have h1 := hfT n hn
      rw [show (⟨(n : Equiv.Perm (Fin 64)), mem_sup_left hn⟩ : ↥heN0) = n from rfl] at h1
      rw [h1]
      exact (ι.symm ⟨n, hn⟩).2
    · intro hn
      have h1 := hfT (ι ⟨f n, hn⟩) (ι ⟨f n, hn⟩).2
      have h2 : f ⟨(ι ⟨f n, hn⟩ : Equiv.Perm (Fin 64)), mem_sup_left (ι ⟨f n, hn⟩).2⟩ = f n := by
        apply Subtype.ext
        rw [h1, show (⟨(ι ⟨f n, hn⟩ : Equiv.Perm (Fin 64)), (ι ⟨f n, hn⟩).2⟩ : ↥hexaT) =
          ι ⟨f n, hn⟩ from rfl, MulEquiv.symm_apply_apply]
      rw [← f.injective h2]
      exact (ι ⟨f n, hn⟩).2
  set t : Equiv.Perm (Fin 64) := (ι ⟨z, hzX⟩ : Equiv.Perm (Fin 64)) with htdef
  have ht : t ∈ hexaT := (ι ⟨z, hzX⟩).2
  have ht1 : t ≠ 1 := by
    intro h
    have h1 : ι ⟨z, hzX⟩ = 1 := Subtype.ext h
    rw [← map_one ι] at h1
    exact hz1 (congrArg Subtype.val (ι.injective h1))
  have hft : (f ⟨t, mem_sup_left ht⟩ : G) = z := by
    rw [hfT t ht, show (⟨t, ht⟩ : ↥hexaT) = ι ⟨z, hzX⟩ from rfl, MulEquiv.symm_apply_apply]
  rcases hM.orbit t ht ht1 with ⟨m, hm, hmt⟩ | ⟨m₅, hm₅, hm₅t, hm₅o⟩
  swap
  · exfalso
    have h1 : 5 ∣ Nat.card (heN0 ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 64))) :
        Subgroup (Equiv.Perm (Fin 64))) := by
      rw [← hm₅o]
      exact Subgroup.orderOf_dvd_natCard _
        ⟨mem_sup_right hm₅, mem_centralizer_singleton_iff.mpr hm₅t⟩
    have h2 : Nat.card (heN0 ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 64))) :
        Subgroup (Equiv.Perm (Fin 64))) =
        Nat.card (AS76b.oUpperTwoPrime (normalizer (X : Set G)) ⊓
          centralizer ({z} : Set G) : Subgroup G) := by
      have e1 := card_centralizer_subtype (⟨t, mem_sup_left ht⟩ : ↥heN0)
      have e2 := card_centralizer_subtype (f ⟨t, mem_sup_left ht⟩)
      have e3 := map_centralizer_singleton_eq f (⟨t, mem_sup_left ht⟩ : ↥heN0)
      have e4 : Nat.card ((centralizer ({⟨t, mem_sup_left ht⟩} : Set ↥heN0)).map f.toMonoidHom) =
          Nat.card (centralizer ({⟨t, mem_sup_left ht⟩} : Set ↥heN0)) :=
        card_map_of_injective f.injective
      rw [hft] at e2
      rw [← e1, ← e4, e3, e2]
    have h3 : Nat.card (AS76b.oUpperTwoPrime (normalizer (X : Set G)) ⊓
        centralizer ({z} : Set G) : Subgroup G) ∣ 21504 := by
      rw [← hCz]
      exact card_dvd_of_le inf_le_right
    rw [h2] at h1
    exact absurd (h1.trans h3) (by decide)
  have hmT : m ∈ normalizer (hexaT : Set (Equiv.Perm (Fin 64))) := hF.normT hm
  have ht0 : hexaT0P ∈ hexaT := by
    rw [← hmt]
    exact (mem_normalizer_iff.mp hmT t).mp ht
  set c : ↥heN0 := ⟨m, mem_sup_right hm⟩ with hc
  have hf1 : ∀ n : ↥heN0, ((MulAut.conj c⁻¹).trans f) n = f (c⁻¹ * n * c) := fun n => by
    simp [MulEquiv.trans_apply]
  have hz : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) = hexaT0P ↔
      ((((MulAut.conj c⁻¹).trans f) n : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G)))) :
        G) = z := by
    intro n
    rw [hf1]
    constructor
    · intro hn
      have h1 : c⁻¹ * n * c = ⟨t, mem_sup_left ht⟩ := by
        apply Subtype.ext
        simp only [coe_mul, coe_inv, hc, hn, ← hmt]
        group
      rw [h1, hft]
    · intro hn
      have h1 : f (c⁻¹ * n * c) = f ⟨t, mem_sup_left ht⟩ := Subtype.ext (by rw [hn, hft])
      have h2 := congrArg Subtype.val (f.injective h1)
      simp only [coe_mul, coe_inv, hc] at h2
      rw [← hmt, ← h2]
      group
  have hd0 : NXDatum X (AS76b.oUpperTwoPrime (normalizer (X : Set G)))
      (hexaT.subtype.comp ι.toMonoidHom) (hexaM.subtype.comp ψ) :=
    { inj := hexaT.subtype_injective.comp ι.injective
      rangeι := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.surjective,
          ← MonoidHom.range_eq_map, range_subtype]
      rangeψ := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψs, ← MonoidHom.range_eq_map,
          range_subtype]
      ker := by
        rw [← hψk]
        ext ℓ
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, coe_subtype,
          OneMemClass.coe_eq_one]
      equiv := fun ℓ x y hy => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_subtype]
        exact hequiv ℓ x y hy }
  have hd1 := hd0.conj hF hm
  have hz0 : ((MulAut.conj m).toMonoidHom.comp (hexaT.subtype.comp ι.toMonoidHom)) ⟨z, hzX⟩ =
      hexaT0P := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_subtype]
    exact hmt
  have hXC : X ≤ centralizer ({z} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (comm_of_sq hX2 hx hzX)
  obtain ⟨-, hIeq⟩ := hd1.iX_eq hF rfl hzX hz0 hXC (by rw [hX64]; norm_num)
  refine ⟨(MulAut.conj c⁻¹).trans f, hz, fun n => ?_, fun n => ?_, c, fun t ht => ?_⟩
  ·
    rw [hf1, ← hfX]
    have hcT : ((c⁻¹ : ↥heN0) : Equiv.Perm (Fin 64)) ∈
        normalizer (hexaT : Set (Equiv.Perm (Fin 64))) := by
      simpa [hc] using inv_mem hmT
    have := mem_iff_of_conj hcT n
    rw [MulAut.conj_apply, inv_inv] at this
    exact this.symm
  ·
    set n₀ : ↥heN0 := ⟨hexaT0P, mem_sup_left ht0⟩ with hn₀
    have hfn₀ : ((((MulAut.conj c⁻¹).trans f) n₀ :
        ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G)))) : G) = z := (hz n₀).mp rfl
    rw [hIeq]
    constructor
    · intro hn
      refine ⟨(((MulAut.conj c⁻¹).trans f) n).2, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : n * n₀ = n₀ * n := Subtype.ext (mem_centralizer_singleton_iff.mp hn.2)
      have h2 := (commute_iff_of_mulEquiv ((MulAut.conj c⁻¹).trans f) n n₀).mp h1
      have h3 := congrArg Subtype.val h2
      simp only [coe_mul] at h3
      rwa [hfn₀] at h3
    · intro hn
      refine ⟨n.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := mem_centralizer_singleton_iff.mp hn.2
      rw [← hfn₀] at h1
      have h2 : ((MulAut.conj c⁻¹).trans f) n * ((MulAut.conj c⁻¹).trans f) n₀ =
          ((MulAut.conj c⁻¹).trans f) n₀ * ((MulAut.conj c⁻¹).trans f) n := Subtype.ext h1
      have h3 := (commute_iff_of_mulEquiv ((MulAut.conj c⁻¹).trans f) n n₀).mpr h2
      exact congrArg Subtype.val h3
  ·
    rw [hf1, show c⁻¹ * (c * ⟨t, mem_sup_left ht⟩ * c⁻¹) * c = ⟨t, mem_sup_left ht⟩ by group]
    exact hfT t ht

theorem exists_normX (hF : HexaFacts) (hM : HeModelFacts) {X Y S₁ : Subgroup G} {z : G}
    (ι : ↥X ≃* ↥hexaT) (ψ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))) →* ↥hexaM)
    (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = X.subgroupOf (AS76b.oUpperTwoPrime (normalizer (X : Set G))))
    (hequiv : ∀ (ℓ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G)))) (x y : ↥X),
      (y : G) = ℓ * x * (ℓ : G)⁻¹ →
        (ι y : Equiv.Perm (Fin 64)) = ψ ℓ * ι x * (ψ ℓ : Equiv.Perm (Fin 64))⁻¹)
    (hX2 : ∀ x ∈ X, x * x = 1) (hX64 : Nat.card X = 64) (hzX : z ∈ X) (hz1 : z ≠ 1)
    (hCz : Nat.card (centralizer ({z} : Set G)) = 21504) (hS₁I : S₁ ≤ iX z X)
    (hS₁ : Nat.card S₁ = 1024) (hYS : Y ≤ S₁) (hSY : S₁ ≤ normalizer (Y : Set G))
    (hY2 : ∀ y ∈ Y, y * y = 1) (hY64 : Nat.card Y = 64) (hYX : Y ≠ X) :
    ∃ f : ↥heN0 ≃* ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))),
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) = hexaT0P ↔ (f n : G) = z) ∧
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ hexaT ↔ (f n : G) ∈ X) ∧
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP12 ↔ (f n : G) ∈ iX z X) ∧
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heB0 ↔ (f n : G) ∈ S₁) ∧
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heF0 ↔ (f n : G) ∈ Y) ∧
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP23 ↔
        (f n : G) ∈ AS76b.oUpperTwoPrime (normalizer (Y : Set G))) ∧
      ∃ d : ↥heN0, ∀ (t : Equiv.Perm (Fin 64)) (ht : t ∈ hexaT),
        ((f (d * ⟨t, mem_sup_left ht⟩ * d⁻¹) : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G)))) :
          G) = ι.symm ⟨t, ht⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f₁, hz, hT, hP, d₁, hd₁⟩ :=
    exists_normX_P12 hF hM ι ψ hψs hψk hequiv hX2 hX64 hzX hz1 hCz
  have hIL : iX z X ≤ AS76b.oUpperTwoPrime (normalizer (X : Set G)) := oUpper_mono' inf_le_right
  have hS₁L := hS₁I.trans hIL
  have hTN : heN0 ≤ normalizer (hexaT : Set (Equiv.Perm (Fin 64))) := sup_le le_normalizer hF.normT
  have hP12N : heP12 ≤ heN0 := inf_le_left
  set P₁ : Subgroup (Equiv.Perm (Fin 64)) :=
    ((S₁.subgroupOf (AS76b.oUpperTwoPrime (normalizer (X : Set G)))).comap
      f₁.toMonoidHom).map heN0.subtype with hP₁
  have hP₁P : P₁ ≤ heP12 := by
    intro p hp
    obtain ⟨hpN, hpS⟩ := (mem_map_comap_iff f₁ S₁ p).mp hp
    exact (hP ⟨p, hpN⟩).mpr (hS₁I hpS)
  have hP₁c : Nat.card P₁ = 1024 := by rw [card_map_comap f₁ hS₁L, hS₁]
  have hsyl : ∀ {B : Subgroup (Equiv.Perm (Fin 64))}, B ≤ heP12 → Nat.card B = 1024 →
      IsSylowOf 2 B heP12 := by
    intro B hB hBc
    refine isSylowOf_iff.mpr ⟨hB, IsPGroup.of_card (n := 10) (by rw [hBc]; norm_num), ?_⟩
    have h := relIndex_mul_card B heP12
    rw [inf_eq_left.mpr hB, hBc, hM.card_P12] at h
    have h3 : B.relIndex heP12 = 3 := by omega
    rw [h3]
    decide
  obtain ⟨c, hcP12, hcP⟩ :=
    CFSG.ComponentClassification.AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf
    (hsyl hM.B0_le hM.card_B0) (hsyl hP₁P hP₁c)
  set c' : ↥heN0 := ⟨c, hP12N hcP12⟩ with hc'
  set f₂ := (MulAut.conj c').trans f₁ with hf₂
  have hf₂a : ∀ n : ↥heN0, f₂ n = f₁ (c' * n * c'⁻¹) := fun n => rfl
  have hcT : (c' : Equiv.Perm (Fin 64)) ∈ normalizer (hexaT : Set (Equiv.Perm (Fin 64))) :=
    hTN c'.2
  have hcP12' : (c' : Equiv.Perm (Fin 64)) ∈ normalizer (heP12 : Set (Equiv.Perm (Fin 64))) :=
    le_normalizer hcP12
  have hct₀ : c * hexaT0P * c⁻¹ = hexaT0P := by
    have := mem_centralizer_singleton_iff.mp hcP12.2
    rw [this, mul_inv_cancel_right]
  have hcoe : ∀ n : ↥heN0, ((c' * n * c'⁻¹ : ↥heN0) : Equiv.Perm (Fin 64)) = c * n * c⁻¹ :=
    fun n => rfl
  have hz₂ : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) = hexaT0P ↔ (f₂ n : G) = z := by
    intro n
    rw [hf₂a, ← hz, hcoe]
    constructor
    · intro h
      rw [h, hct₀]
    · intro h
      calc (n : Equiv.Perm (Fin 64)) = c⁻¹ * (c * n * c⁻¹) * c := by group
        _ = c⁻¹ * hexaT0P * c := by rw [h]
        _ = c⁻¹ * (c * hexaT0P * c⁻¹) * c := by rw [hct₀]
        _ = hexaT0P := by group
  have hT₂ : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ hexaT ↔ (f₂ n : G) ∈ X := fun n => by
    rw [hf₂a, ← hT, ← MulAut.conj_apply, mem_iff_of_conj hcT]
  have hP₂ : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP12 ↔ (f₂ n : G) ∈ iX z X := fun n => by
    rw [hf₂a, ← hP, ← MulAut.conj_apply, mem_iff_of_conj hcP12']
  have hB₂ : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heB0 ↔ (f₂ n : G) ∈ S₁ := by
    intro n
    rw [← hcP, mem_rightConjugate_iff, mem_map_comap_iff, hf₂a]
    constructor
    · rintro ⟨h, hS⟩
      have : (⟨c * n * c⁻¹, h⟩ : ↥heN0) = c' * n * c'⁻¹ := rfl
      rwa [this] at hS
    · intro hS
      exact ⟨(c' * n * c'⁻¹).2, hS⟩
  have hYL : Y ≤ AS76b.oUpperTwoPrime (normalizer (X : Set G)) := hYS.trans hS₁L
  set Y' : Subgroup (Equiv.Perm (Fin 64)) :=
    ((Y.subgroupOf (AS76b.oUpperTwoPrime (normalizer (X : Set G)))).comap
      f₂.toMonoidHom).map heN0.subtype with hY'
  have hB0N : heB0 ≤ heN0 := hM.B0_le.trans hP12N
  have hY'B : Y' ≤ heB0 := by
    intro p hp
    obtain ⟨hpN, hpY⟩ := (mem_map_comap_iff f₂ Y p).mp hp
    exact (hB₂ ⟨p, hpN⟩).mpr (hYS hpY)
  have hY'n : ∀ b ∈ heB0, ∀ x ∈ Y', b * x * b⁻¹ ∈ Y' := by
    intro b hb x hx
    obtain ⟨hxN, hxY⟩ := (mem_map_comap_iff f₂ Y x).mp hx
    have hbS := (hB₂ ⟨b, hB0N hb⟩).mp hb
    refine (mem_map_comap_iff f₂ Y _).mpr ⟨mul_mem (mul_mem (hB0N hb) hxN) (inv_mem (hB0N hb)), ?_⟩
    have : (⟨b * x * b⁻¹, mul_mem (mul_mem (hB0N hb) hxN) (inv_mem (hB0N hb))⟩ : ↥heN0) =
        ⟨b, hB0N hb⟩ * ⟨x, hxN⟩ * (⟨b, hB0N hb⟩ : ↥heN0)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (hSY hbS) _).mp hxY
  have hY'2 : ∀ x ∈ Y', x * x = 1 := by
    intro x hx
    obtain ⟨hxN, hxY⟩ := (mem_map_comap_iff f₂ Y x).mp hx
    have h1 : f₂ (⟨x, hxN⟩ * ⟨x, hxN⟩) = 1 := by
      rw [map_mul]
      exact Subtype.ext (hY2 _ hxY)
    have h2 : (⟨x, hxN⟩ : ↥heN0) * ⟨x, hxN⟩ = 1 := by
      rw [← map_one f₂] at h1
      exact f₂.injective h1
    exact congrArg Subtype.val h2
  have hY'c : Nat.card Y' = 64 := by rw [card_map_comap f₂ hYL, hY64]
  have hY'eq : Y' = heF0 := by
    rcases hM.normal_B0 Y' hY'B hY'n hY'2 hY'c with h | h
    · exfalso
      apply hYX
      refine (eq_of_le_of_card_ge (fun y hy => ?_) (by rw [hX64, hY64])).symm.symm
      · have hn := f₂.apply_symm_apply ⟨y, hYL hy⟩
        have h1 : ((f₂.symm ⟨y, hYL hy⟩ : ↥heN0) : Equiv.Perm (Fin 64)) ∈ Y' :=
          (mem_map_comap_iff f₂ Y _).mpr ⟨(f₂.symm ⟨y, hYL hy⟩).2, by rw [hn]; exact hy⟩
        rw [h] at h1
        have h2 := (hT₂ _).mp h1
        rwa [hn] at h2
    · exact h
  have hF₂ : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heF0 ↔ (f₂ n : G) ∈ Y := by
    intro n
    rw [← hY'eq, mem_map_comap_iff]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨n.2, h⟩⟩
  have hF0N : heF0 ≤ heN0 := hM.F0_le_B0.trans hB0N
  have hconjY : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ normalizer
      (heF0 : Set (Equiv.Perm (Fin 64))) → (f₂ n : G) ∈ normalizer (Y : Set G) := by
    intro n hn
    refine mem_normalizer_of_forall fun y hy => ?_
    have hn' := f₂.apply_symm_apply ⟨y, hYL hy⟩
    set m := f₂.symm ⟨y, hYL hy⟩ with hm
    have hmF : (m : Equiv.Perm (Fin 64)) ∈ heF0 := (hF₂ m).mpr (by rw [hn']; exact hy)
    have h1 : ((n * m * n⁻¹ : ↥heN0) : Equiv.Perm (Fin 64)) ∈ heF0 := by
      simp only [coe_mul, coe_inv]
      exact (mem_normalizer_iff.mp hn _).mp hmF
    have h2 := (hF₂ _).mp h1
    rw [map_mul, map_mul, map_inv, hn'] at h2
    simpa using h2
  have hP23N : heP23 ≤ heN0 := hM.P23_eq ▸ inf_le_left
  have hP23le : heP23 ≤ (((AS76b.oUpperTwoPrime (normalizer (Y : Set G))).subgroupOf
      (AS76b.oUpperTwoPrime (normalizer (X : Set G)))).comap f₂.toMonoidHom).map
        heN0.subtype := by
    refine grpN_le fun a ha => ?_
    have hgP : permOfArr 64 a ∈ heP23 := gen_mem_grpN ha
    have hgN := hP23N hgP
    have hgF : permOfArr 64 a ∈ normalizer (heF0 : Set (Equiv.Perm (Fin 64))) := by
      have := hgP
      rw [hM.P23_eq] at this
      exact this.2
    obtain ⟨k, hk⟩ := hM.P23_gens a ha
    refine (mem_map_comap_iff f₂ _ _).mpr ⟨hgN, mem_oUpper' (hconjY ⟨_, hgN⟩ hgF) (n := k) ?_⟩
    have h1 : (⟨permOfArr 64 a, hgN⟩ : ↥heN0) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    have h2 : f₂ ((⟨permOfArr 64 a, hgN⟩ : ↥heN0) ^ 2 ^ k) = 1 := by rw [h1, map_one]
    rw [map_pow] at h2
    have h3 := congrArg Subtype.val h2
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h3
    exact h3
  refine ⟨f₂, hz₂, hT₂, hP₂, hB₂, hF₂, fun n => ⟨fun hn => ?_, fun hn => ?_⟩, c'⁻¹ * d₁,
    fun t ht => ?_⟩
  · obtain ⟨h, hY⟩ := (mem_map_comap_iff f₂ _ _).mp (hP23le hn)
    exact hY
  · have hnY : (f₂ n : G) ∈ normalizer (Y : Set G) := oUpper_le' _ hn
    have hnF : (n : Equiv.Perm (Fin 64)) ∈ normalizer (heF0 : Set (Equiv.Perm (Fin 64))) := by
      refine mem_normalizer_of_forall fun x hx => ?_
      have hxN := hF0N hx
      have h1 := (hF₂ ⟨x, hxN⟩).mp hx
      have h2 : (f₂ (n * ⟨x, hxN⟩ * n⁻¹) : G) ∈ Y := by
        rw [map_mul, map_mul, map_inv]
        simp only [coe_mul, coe_inv]
        exact (mem_normalizer_iff.mp hnY _).mp h1
      have h3 := (hF₂ _).mpr h2
      simpa using h3
    rw [hM.P23_eq]
    exact ⟨n.2, hnF⟩
  · rw [hf₂a, show c' * (c'⁻¹ * d₁ * ⟨t, mem_sup_left ht⟩ * (c'⁻¹ * d₁)⁻¹) * c'⁻¹ =
      d₁ * ⟨t, mem_sup_left ht⟩ * d₁⁻¹ by group]
    exact hd₁ t ht

end Norm

end CFSG.ComponentClassification.AS81.HeTri
