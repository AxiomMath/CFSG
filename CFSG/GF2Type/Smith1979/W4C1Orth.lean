module

public import CFSG.GF2Type.Smith1979.W4C1Par
public import CFSG.GF2Type.Smith1979.W4C1Siegel
public import CFSG.GF2Type.Smith1979.W4C1Syl
public import CFSG.LargeExtraspecial.S12FourteenMain
public import CFSG.LargeExtraspecial.S14C13Model

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C1

open Module QuadraticMap CFSG.LargeExtraspecial
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6)

section Orbit

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem ncard_singular_le (hQ : Q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8) :
    {v : V | Q v = 0}.ncard ≤ 136 := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  have hc : Nat.card V = 4 ^ 4 := CFSG.LargeExtraspecial.S12DW.natCard_eq_four_pow (by rw [hV])
  have h3 := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic Q
    (CFSG.LargeExtraspecial.S12DW.polar_eq_zero_imp hQ) hc
  have h4 := CFSG.LargeExtraspecial.S12DW.ncard_eq_zero_eq Q
  rw [hc] at h4
  norm_num at h3 h4
  omega

variable {M : Type} [Group M] (ρ : M →* (V ≃ₗ[ZMod 2] V))

@[expose] def stabSub (x : V) : Subgroup M where
  carrier := {m | ρ m x = x}
  mul_mem' {a b} ha hb := by
    change ρ (a * b) x = x
    rw [map_mul, LinearEquiv.mul_apply]
    change ρ a (ρ b x) = x
    rw [show ρ b x = x from hb]
    exact ha
  one_mem' := by
    change ρ 1 x = x
    rw [map_one]
    rfl
  inv_mem' {a} ha := by
    change ρ a⁻¹ x = x
    have h : ρ a x = x := ha
    calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [h]
      _ = x := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem mem_stabSub {x : V} {m : M} : m ∈ stabSub ρ x ↔ ρ m x = x := Iff.rfl

theorem card_le_mul_stabSub [Finite M] (hQ : Q.polarBilin.Nondegenerate)
    (hV : finrank (ZMod 2) V = 8) (hO : ∀ m, ρ m ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x : V}
    (hx0 : x ≠ 0) (hxq : Q x = 0) : Nat.card M ≤ 135 * Nat.card (stabSub ρ x) := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  letI : MulAction M V := MulAction.compHom V ρ
  have hst : MulAction.stabilizer M x = stabSub ρ x := rfl
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer M x)
  rw [MulAction.index_stabilizer, hst] at h1
  have h2 : (MulAction.orbit M x).ncard ≤ 135 := by
    have hsub : MulAction.orbit M x ⊆ {v : V | Q v = 0} \ {0} := by
      rintro _ ⟨m, rfl⟩
      refine ⟨?_, ?_⟩
      · change Q (ρ m x) = 0
        rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hO m)]
        exact hxq
      · intro h
        apply hx0
        have h' : ρ m x = 0 := h
        exact (ρ m).injective (by rw [h', map_zero])
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h4 : ({v : V | Q v = 0} \ ({0} : Set V)).ncard + 1 = {v : V | Q v = 0}.ncard := by
      have h0 : (0 : V) ∈ {v : V | Q v = 0} := by
        change Q 0 = 0
        exact QuadraticMap.map_zero Q
      exact Set.ncard_diff_singleton_add_one h0 (Set.toFinite _)
    have h5 := ncard_singular_le hQ hV
    omega
  calc Nat.card M = Nat.card (stabSub ρ x) * (MulAction.orbit M x).ncard := h1.symm
    _ ≤ Nat.card (stabSub ρ x) * 135 := Nat.mul_le_mul_left _ h2
    _ = 135 * Nat.card (stabSub ρ x) := mul_comm _ _

end Orbit

theorem normal_two_le {Γ : Type*} [Group Γ] [Finite Γ] {T N : Subgroup Γ}
    (hT : Nat.card T = 2 ^ 9) (hΓ : ¬ 2 ^ 10 ∣ Nat.card Γ) [N.Normal] (hN : IsPGroup 2 N) :
    N ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 T := IsPGroup.of_card hT
  have hsup : IsPGroup 2 (N ⊔ T : Subgroup Γ) := hN.to_sup_of_normal_left hTp
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hsup
  have hdvd : Nat.card (N ⊔ T : Subgroup Γ) ∣ Nat.card Γ := Subgroup.card_subgroup_dvd_card _
  have hn9 : n ≤ 9 := by
    by_contra h
    exact hΓ ((pow_dvd_pow 2 (by omega)).trans (hn ▸ hdvd))
  have hcard : Nat.card (N ⊔ T : Subgroup Γ) ≤ Nat.card T := by
    rw [hn, hT]
    exact Nat.pow_le_pow_right (by norm_num) hn9
  have heq : T = N ⊔ T := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
  exact heq ▸ le_sup_left

instance finite_linearEquiv_zmod2 {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] :
    Finite (W ≃ₗ[ZMod 2] W) :=
  Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W))
    (fun _ _ h => LinearEquiv.ext (congrFun h))

section Cases

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {M : Type} [Group M] [Finite M] (ρ : M →* (V ≃ₗ[ZMod 2] V))
  (hQ : Q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8) (hρ : Function.Injective ρ)
  (hO : ∀ m, ρ m ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hMord : Nat.card M = 1451520)
  {x : V} (hx0 : x ≠ 0) (hxq : Q x = 0)

include hQ hV hO hMord hx0 hxq in
theorem stabSub_card_bounds :
    10752 ≤ Nat.card (stabSub ρ x) ∧ ¬ 2 ^ 10 ∣ Nat.card (stabSub ρ x) := by
  have h1 := card_le_mul_stabSub ρ hQ hV hO hx0 hxq
  rw [hMord] at h1
  refine ⟨by omega, fun h => ?_⟩
  have h2 : Nat.card (stabSub ρ x) ∣ Nat.card M := Subgroup.card_subgroup_dvd_card _
  rw [hMord] at h2
  have := h.trans h2
  revert this
  decide

include hQ hV hρ hO hMord hx0 hxq in
theorem false_of_dim_one (horb : ∃ m : M, polar Q x (ρ m x) ≠ 0) (L : Subgroup M)
    (hL : Nat.card L = 2 ^ 6) (hLx : ∀ ℓ ∈ L, ρ ℓ x = x)
    (hLD : ∀ ℓ ∈ L, ∀ v, polar Q x v = 0 → ρ ℓ v - v ∈ (ZMod 2) ∙ x) : False := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  have hLR : L.map ρ ≤ pointRadical Q x := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    refine ⟨hO ℓ, hLx ℓ hℓ, hLD ℓ hℓ, fun v => ?_⟩
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hO ℓ) x v
    rw [hLx ℓ hℓ] at h1
    rw [polar_sub_right, h1, sub_self]
  have hcardL : Nat.card (L.map ρ) = 2 ^ 6 := (Subgroup.card_map_of_injective hρ).trans hL
  have hcardR : Nat.card (pointRadical Q x) = 2 ^ 6 := by
    rw [card_pointRadical hQ hx0 hxq, hV]
  have hR : L.map ρ = pointRadical Q x :=
    Subgroup.eq_of_le_of_card_ge hLR (by rw [hcardR, hcardL])
  have hA : pointRadical Q x ≤ ρ.range := by
    rw [← hR]
    exact fun t ht => by
      obtain ⟨ℓ, -, rfl⟩ := ht
      exact ⟨ℓ, rfl⟩
  obtain ⟨m, hm⟩ := horb
  have h10 := two_pow_ten_dvd_card hQ hV (M := ρ.range) (fun t ⟨m, hm⟩ => hm ▸ hO m) hx0 hxq hA
    ⟨ρ m, ⟨m, rfl⟩, hm⟩
  have hcard : Nat.card ρ.range = Nat.card M :=
    Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv.symm
  rw [hcard, hMord] at h10
  revert h10
  decide

include hQ hV hρ hO hMord hx0 hxq in
theorem false_of_dim_two_three {D : Submodule (ZMod 2) V} (hxD : x ∈ D)
    (hDq : ∀ v ∈ D, Q v = 0) (hDinv : ∀ m : M, ρ m x = x → ∀ v ∈ D, ρ m v ∈ D)
    (hk : finrank (ZMod 2) D = 2 ∨ finrank (ZMod 2) D = 3) : False := by
  obtain ⟨hPge, hP2⟩ := stabSub_card_bounds ρ hQ hV hO hMord hx0 hxq
  have hρ' : Function.Injective (ρ.comp (stabSub ρ x).subtype) :=
    hρ.comp (stabSub ρ x).subtype_injective
  have hO' : ∀ g : stabSub ρ x, (ρ.comp (stabSub ρ x).subtype) g ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := fun g => hO g
  have hD' : ∀ g : stabSub ρ x, ∀ d ∈ D, (ρ.comp (stabSub ρ x).subtype) g d ∈ D :=
    fun g d hd => hDinv g.1 g.2 d hd
  have hxfix' : ∀ g : stabSub ρ x, (ρ.comp (stabSub ρ x).subtype) g x = x := fun g => g.2
  rcases hk with hk | hk
  · obtain ⟨j, m, hm, hm15, hdvd⟩ := Par.odd_bound_two (ρ.comp (stabSub ρ x).subtype) hρ' hO' hD'
      hQ hDq hV hxD hx0 hxfix' hk
    have := Par.card_le_of_dvd hm hm15 hdvd hP2
    omega
  · obtain ⟨j, m, hm, hm9, hdvd⟩ := Par.odd_bound_three (ρ.comp (stabSub ρ x).subtype) hρ' hO' hD'
      hQ hDq hV hxD hx0 hxfix' hk
    have := Par.card_le_of_dvd hm hm9 hdvd hP2
    omega

include hQ hV hρ hO hMord hx0 hxq in
theorem false_of_dim_four (εM : M ≃* H6) (L : Subgroup M)
    (hLc : ∀ a ∈ L, ∀ a' ∈ L, a * a' = a' * a) (hLs : ∀ a ∈ L, a * a = 1)
    (hL8 : 8 ≤ Nat.card L) (hLx : ∀ ℓ ∈ L, ρ ℓ x = x)
    (hLn : ∀ m : M, ρ m x = x → ∀ ℓ ∈ L, m * ℓ * m⁻¹ ∈ L) {D : Submodule (ZMod 2) V}
    (hxD : x ∈ D) (hDq : ∀ v ∈ D, Q v = 0)
    (hDinv : ∀ m : M, ρ m x = x → ∀ v ∈ D, ρ m v ∈ D) (hk : finrank (ZMod 2) D = 4)
    (hfaith : ∀ ℓ ∈ L, (∀ v ∈ D, ρ ℓ v = v) → ℓ = 1) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPge, hP2⟩ := stabSub_card_bounds ρ hQ hV hO hMord hx0 hxq
  set P := stabSub ρ x with hP
  set ρ' : P →* (V ≃ₗ[ZMod 2] V) := ρ.comp P.subtype with hρ'def
  have hρ' : Function.Injective ρ' := hρ.comp P.subtype_injective
  have hO' : ∀ g : P, ρ' g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun g => hO g
  have hD' : ∀ g : P, ∀ d ∈ D, ρ' g d ∈ D := fun g d hd => hDinv g.1 g.2 d hd
  have hxfix' : ∀ g : P, ρ' g x = x := fun g => g.2
  obtain ⟨j, m, hm, hm21, hdvd⟩ := Par.odd_bound_four ρ' hρ' hO' hD' hQ hDq hV hxD hx0 hxfix' hk
  have hPle := Par.card_le_of_dvd hm hm21 hdvd hP2
  have hP10752 : Nat.card P = 10752 := by omega
  set K : Subgroup P := (Par.resD ρ' hD').ker with hK
  haveI hKn : K.Normal := MonoidHom.normal_ker _
  have hKcard : 8 ≤ Nat.card K := by
    have h1 : Nat.card P ≤ Nat.card K * 1344 := Par.card_le_ker_mul_four ρ' hD' hxD hx0 hxfix' hk
    omega
  have hDeq : Par.perp Q D = D := by
    refine (Submodule.eq_of_le_of_finrank_le (Par.le_perp hDq) ?_).symm
    have h1 : finrank (ZMod 2) (Par.perp Q D) = finrank (ZMod 2) V - finrank (ZMod 2) D :=
      LinearMap.BilinForm.finrank_orthogonal hQ D
    omega
  have hKc : ∀ a ∈ K, ∀ a' ∈ K, a * a' = a' * a := fun a ha a' ha' =>
    Par.ker_resD_comm ρ' hρ' hO' hD' hDeq ha ha'
  have hKs : ∀ a ∈ K, a * a = 1 := fun a ha => Par.ker_resD_sq ρ' hρ' hO' hD' hDeq ha
  obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) 2 (n := 9)
    (by rw [hP10752]; norm_num)
  have hPnd : ¬ 2 ^ 10 ∣ Nat.card P := by
    rw [hP10752]
    decide
  have hKT : K ≤ T := by
    refine normal_two_le hT hPnd ?_
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    exact ⟨1, Subtype.ext (by simpa [pow_two] using hKs g g.2)⟩
  have hLP : L ≤ P := fun ℓ hℓ => hLx ℓ hℓ
  set LP : Subgroup P := L.subgroupOf P with hLPdef
  haveI hLPn : LP.Normal :=
    ⟨fun n hn g => by
      rw [hLPdef, Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hLn g.1 g.2 n hn⟩
  have hLPT : LP ≤ T := by
    refine normal_two_le hT hPnd ?_
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := hLs g.1.1 (Subgroup.mem_subgroupOf.mp g.2)
    simpa [pow_two] using h1
  set TM : Subgroup M := T.map P.subtype with hTM
  have hTMcard : Nat.card TM = 2 ^ 9 :=
    (Subgroup.card_map_of_injective P.subtype_injective).trans hT
  have hTMP : ∀ t ∈ TM, ρ t x = x := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  obtain ⟨w, hwT, hw1, hF⟩ := sylow_normal_elemAb_mem εM.toMonoidHom εM.injective TM
    (by rw [hTMcard]; norm_num)
  have hwL : w ∈ L := by
    refine hF L ?_ ?_ hLc hLs hL8
    · intro ℓ hℓ
      exact ⟨⟨ℓ, hLP hℓ⟩, hLPT (Subgroup.mem_subgroupOf.mpr hℓ), rfl⟩
    · intro t ht f hf
      exact hLn t (hTMP t ht) f hf
  have hwK : w ∈ K.map P.subtype := by
    refine hF (K.map P.subtype) (Subgroup.map_mono hKT) ?_ ?_ ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨k, hk', rfl⟩
      exact ⟨g * k * g⁻¹, hKn.conj_mem k hk' g, by simp⟩
    · rintro _ ⟨k₁, hk₁, rfl⟩ _ ⟨k₂, hk₂, rfl⟩
      rw [← map_mul, ← map_mul, hKc k₁ hk₁ k₂ hk₂]
    · rintro _ ⟨k, hk', rfl⟩
      rw [← map_mul, hKs k hk', map_one]
    · rw [Subgroup.card_map_of_injective P.subtype_injective]
      exact hKcard
  obtain ⟨k, hkK, rfl⟩ := hwK
  have hkD : ∀ d ∈ D, ρ (k : M) d = d := fun d hd =>
    (Par.resD_eq_one_iff ρ' hD' k).mp hkK d hd
  exact hw1 (hfaith _ hwL hkD)

end Cases

section Config

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {M : Type} [Group M] (ρ : M →* (V ≃ₗ[ZMod 2] V))

theorem false_of_spSix_action
    (hQ : Q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8) (hρ : Function.Injective ρ)
    (hO : ∀ m, ρ m ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (b : LinearMap.BilinForm (ZMod 2) (Fin 6 → ZMod 2)) (hb₁ : ∀ y, b y y = 0)
    (hb₂ : ∀ y, (∀ z, b y z = 0) → y = 0) (e : M ≃* s12SpIsometries b)
    {x : V} (hx0 : x ≠ 0) (hxq : Q x = 0) (horb : ∃ m : M, polar Q x (ρ m x) ≠ 0)
    (L : Subgroup M) (hLc : ∀ a ∈ L, ∀ a' ∈ L, a * a' = a' * a) (hLs : ∀ a ∈ L, a * a = 1)
    (hL8 : 8 ≤ Nat.card L) (hLx : ∀ ℓ ∈ L, ρ ℓ x = x)
    (hLn : ∀ m : M, ρ m x = x → ∀ ℓ ∈ L, m * ℓ * m⁻¹ ∈ L)
    (D : Submodule (ZMod 2) V) (hxD : x ∈ D) (hDq : ∀ v ∈ D, Q v = 0)
    (hDinv : ∀ m : M, ρ m x = x → ∀ v ∈ D, ρ m v ∈ D)
    (hLD : ∀ ℓ ∈ L, ∀ v, polar Q x v = 0 → ρ ℓ v - v ∈ D)
    (hcard : Nat.card L * 2 ^ (finrank (ZMod 2) D + 1) = 2 ^ 8)
    (hfaith : finrank (ZMod 2) D = 4 → ∀ ℓ ∈ L, (∀ v ∈ D, ρ ℓ v = v) → ℓ = 1) : False := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  have he : s12SpIsometries b = TauCeti.BilinForm.isometryGroup b := by
    ext g
    exact TauCeti.BilinForm.mem_isometryGroup_iff.symm
  have hnd : b.Nondegenerate :=
    (LinearMap.IsAlt.isRefl hb₁).nondegenerate_iff_separatingLeft.mpr hb₂
  obtain ⟨φ⟩ := CFSG.LargeExtraspecial.S14.nonempty_isometryGroup_equiv_statedSp
    (V := Fin 6 → ZMod 2) hb₁ hnd (by simp)
  let εM : M ≃* H6 := e.trans ((MulEquiv.subgroupCongr he).trans φ)
  haveI : Finite M := Finite.of_equiv H6 εM.symm.toEquiv
  have hMord : Nat.card M = 1451520 :=
    (Nat.card_congr εM.toEquiv).trans CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.card_H6
  have hk1 : 1 ≤ finrank (ZMod 2) D := by
    refine Nat.one_le_iff_ne_zero.mpr fun h0 => hx0 ?_
    have : D = ⊥ := Submodule.finrank_eq_zero.mp h0
    rw [this] at hxD
    exact (Submodule.mem_bot _).mp hxD
  have hk4 : finrank (ZMod 2) D ≤ 4 := by
    have h1 : finrank (ZMod 2) D ≤ finrank (ZMod 2) (Par.perp Q D) :=
      Submodule.finrank_mono (Par.le_perp hDq)
    have h2 : finrank (ZMod 2) (Par.perp Q D) = finrank (ZMod 2) V - finrank (ZMod 2) D :=
      LinearMap.BilinForm.finrank_orthogonal hQ D
    omega
  rcases (by omega : finrank (ZMod 2) D = 1 ∨ finrank (ZMod 2) D = 2 ∨ finrank (ZMod 2) D = 3 ∨
      finrank (ZMod 2) D = 4) with hk | hk | hk | hk
  ·
    have hDx : D = (ZMod 2) ∙ x := by
      refine (Submodule.eq_of_le_of_finrank_le
        ((Submodule.span_singleton_le_iff_mem x D).mpr hxD) ?_).symm
      rw [hk, finrank_span_singleton hx0]
    have hL : Nat.card L = 2 ^ 6 := by
      rw [hk] at hcard
      have h1 : Nat.card L * 2 ^ 2 = 2 ^ 6 * 2 ^ 2 := by rw [hcard]; norm_num
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
    exact false_of_dim_one ρ hQ hV hρ hO hMord hx0 hxq horb L hL hLx
      (fun ℓ hℓ v hv => hDx ▸ hLD ℓ hℓ v hv)
  · exact false_of_dim_two_three ρ hQ hV hρ hO hMord hx0 hxq hxD hDq hDinv (Or.inl hk)
  · exact false_of_dim_two_three ρ hQ hV hρ hO hMord hx0 hxq hxD hDq hDinv (Or.inr hk)
  · exact false_of_dim_four ρ hQ hV hρ hO hMord hx0 hxq εM L hLc hLs hL8 hLx hLn hxD hDq hDinv
      hk (hfaith hk)

end Config

end CFSG.GF2Type.Smith1979.W4C1
