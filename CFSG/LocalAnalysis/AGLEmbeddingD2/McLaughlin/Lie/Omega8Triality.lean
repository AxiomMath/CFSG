module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8TypeMap
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8ParabolicBasic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Omega8OutProof
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.D4Unipotent

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.Lie

open CFSG.EvenSmallLie.OmegaEight CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise

theorem rho4_pow_three : rho4 ^ 3 = 1 := by decide

theorem rho4_ne_one : rho4 ≠ 1 := by decide

theorem orderOf_rho4 : orderOf rho4 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime rho4_pow_three rho4_ne_one

theorem cycle_of_values : ∀ a b c : Fin 4,
    (∀ x : Fin 4, (![a, 1, b, c] : Fin 4 → Fin 4) ((![a, 1, b, c] : Fin 4 → Fin 4)
      ((![a, 1, b, c] : Fin 4 → Fin 4) x)) = x) →
    ¬ (a = 0 ∧ b = 2 ∧ c = 3) → (a = 2 ∧ b = 3 ∧ c = 0) ∨ (a = 3 ∧ c = 2 ∧ b = 0) := by
  decide

theorem cycle_of_pow_three {σ : Equiv.Perm (Fin 4)} (h1 : σ 1 = 1) (h3 : σ ^ 3 = 1)
    (hne : σ ≠ 1) : (σ 0 = 2 ∧ σ 2 = 3 ∧ σ 3 = 0) ∨ (σ 0 = 3 ∧ σ 3 = 2 ∧ σ 2 = 0) := by
  have hf : (σ : Fin 4 → Fin 4) = ![σ 0, 1, σ 2, σ 3] := by
    funext x
    fin_cases x <;> simp [h1]
  apply cycle_of_values (σ 0) (σ 2) (σ 3)
  · intro x
    rw [← hf]
    have := congrArg (fun τ : Equiv.Perm (Fin 4) => τ x) h3
    simpa [pow_succ, Equiv.Perm.mul_apply] using this
  · rintro ⟨h0, h2, h3'⟩
    apply hne
    ext x
    fin_cases x <;> simp [h0, h1, h2, h3']

theorem pow_three_eq_one_of_pow {σ : Equiv.Perm (Fin 4)} {k : ℕ} (h : σ ^ 3 ^ k = 1) :
    σ ^ 3 = 1 := by
  have hd : orderOf σ ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨d, hdk, hd'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  have h24 : orderOf σ ∣ 24 := by
    have := orderOf_dvd_card (G := Equiv.Perm (Fin 4)) (x := σ)
    rwa [Fintype.card_perm, Fintype.card_fin, show Nat.factorial 4 = 24 from rfl] at this
  have hd1 : d ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h9 : 9 ∣ orderOf σ := by
      rw [hd']
      exact (pow_dvd_pow 3 hlt : 3 ^ 2 ∣ 3 ^ d)
    have := h9.trans h24
    omega
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hd']
  exact pow_dvd_pow 3 hd1

theorem image_eq_of_leaves {J : Set (Fin 4)} (h02 : (0 : Fin 4) ∈ J ↔ (2 : Fin 4) ∈ J)
    (h03 : (0 : Fin 4) ∈ J ↔ (3 : Fin 4) ∈ J) {σ : Equiv.Perm (Fin 4)} (h1 : σ 1 = 1) :
    ⇑σ '' J = J := by
  have hleaf : ∀ x y : Fin 4, x ≠ 1 → y ≠ 1 → (x ∈ J ↔ y ∈ J) := by
    intro x y hx hy
    fin_cases x <;> fin_cases y <;> simp_all
  have hiff : ∀ x, σ x ∈ J ↔ x ∈ J := by
    intro x
    by_cases hx : x = 1
    · rw [hx, h1]
    · have hσx : σ x ≠ 1 := fun e => hx (σ.injective (e.trans h1.symm))
      exact hleaf _ _ hσx hx
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hiff x).2 hx
  · intro hy
    exact ⟨σ.symm y, (hiff _).1 (by simpa using hy), by simp⟩

variable (hU : PosUnipotentSimple)
include hU

@[expose] noncomputable def typePerm (β : MulAut (spinGroup (quadPlus 4 F2))) :
    Equiv.Perm (Fin 4) :=
  (exists_isTypeMap hU β).choose

theorem typePerm_spec (β : MulAut (spinGroup (quadPlus 4 F2))) :
    typePerm hU β 1 = 1 ∧ IsTypeMap β (typePerm hU β) :=
  (exists_isTypeMap hU β).choose_spec

theorem typePerm_eq {β : MulAut (spinGroup (quadPlus 4 F2))} {σ : Equiv.Perm (Fin 4)}
    (h : IsTypeMap β σ) : typePerm hU β = σ :=
  (typePerm_spec hU β).2.unique card_F2 h

@[expose] noncomputable def typeHom : MulAut (spinGroup (quadPlus 4 F2)) →* Equiv.Perm (Fin 4) where
  toFun := typePerm hU
  map_one' := typePerm_eq hU isTypeMap_one
  map_mul' β β' := typePerm_eq hU ((typePerm_spec hU β).2.mul (typePerm_spec hU β').2)

theorem typeHom_apply (β : MulAut (spinGroup (quadPlus 4 F2))) :
    typeHom hU β = typePerm hU β := rfl

theorem inner_le_ker_typeHom : inner (spinGroup (quadPlus 4 F2)) ≤ (typeHom hU).ker := by
  rintro _ ⟨k, rfl⟩
  exact typePerm_eq hU (isTypeMap_conj k)

omit hU in
theorem card_outer_spin : Nat.card (Outer (spinGroup (quadPlus 4 F2))) = 6 := by
  rw [Nat.card_congr
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence spinOmegaEquiv).toEquiv,
    card_outer_omegaT]

theorem mem_inner_of_typeHom_eq_one {β : MulAut (spinGroup (quadPlus 4 F2))}
    (hβ : typeHom hU β = 1) {k : ℕ} (hk : β ^ 3 ^ k = 1) : β ∈ inner (spinGroup (quadPlus 4 F2)) := by
  have hfin : Finite (MulAut (spinGroup (quadPlus 4 F2))) :=
    Finite.of_equiv _ (MulAut.congr spinOmegaEquiv.symm).toEquiv
  set φ : Outer (spinGroup (quadPlus 4 F2)) →* Equiv.Perm (Fin 4) :=
    QuotientGroup.lift (inner (spinGroup (quadPlus 4 F2))) (typeHom hU) (inner_le_ker_typeHom hU)
    with hφ
  have hρ : rho4 ∈ φ.range := by
    refine ⟨QuotientGroup.mk (autSpin ⟨gen 8, gen_mem_autT (by norm_num)⟩), ?_⟩
    rw [hφ, QuotientGroup.lift_mk, typeHom_apply, typePerm_eq hU (isTypeMap_rho hU)]
  have h3 : 3 ∣ Nat.card φ.range := by
    have := Subgroup.orderOf_dvd_natCard φ.range hρ
    rwa [orderOf_rho4] at this
  have hcard : Nat.card φ.ker * Nat.card φ.range = 6 := by
    rw [← card_outer_spin, ← φ.ker.card_mul_index, Subgroup.index,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hker : Nat.card φ.ker ∣ 2 := by
    obtain ⟨r, hr⟩ := h3
    rw [hr] at hcard
    exact ⟨r, by linarith⟩
  set q : Outer (spinGroup (quadPlus 4 F2)) := QuotientGroup.mk β with hq
  have hqker : q ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hq, hφ, QuotientGroup.lift_mk, hβ]
  have hq3 : (⟨q, hqker⟩ : φ.ker) ^ 3 ^ k = 1 := by
    apply Subtype.ext
    have : q ^ 3 ^ k = 1 := by rw [hq, ← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
    simpa using this
  have ho : orderOf (⟨q, hqker⟩ : φ.ker) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3))
      ((orderOf_dvd_natCard _).trans hker) (orderOf_dvd_of_pow_eq_one hq3)
  have hq1 : q = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp ho)
  rwa [hq, QuotientGroup.eq_one_iff] at hq1

omit hU in
theorem map_conj_eq_of_mem_normalizer {X : Type} [Group X] {P : Subgroup X} {u : X}
    (hu : u ∈ Subgroup.normalizer (P : Set X)) : P.map (MulAut.conj u).toMonoidHom = P := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hu g).mp hg
  · intro g hg
    refine ⟨u⁻¹ * g * u, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (P : Set X)).inv_mem hu) g).mp hg
      simpa using this
    · simp [mul_assoc]

omit hU in
theorem map_map_conj_hom {K X : Type} [Group K] [Group X] (φ : K →* X) (C : Subgroup K) (k : K) :
    (C.map (MulAut.conj k).toMonoidHom).map φ = (C.map φ).map (MulAut.conj (φ k)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem kFactOmega8Triality_of : KFactOmega8Triality := by
  intro X _ _ Lb P hΩ hLn hP _ _ hu m
  obtain ⟨u, huN, hu3, huout⟩ := hu
  have := hLn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := finite_spinFour (F := F2)
  obtain ⟨eL⟩ := nonempty_mulEquiv_omegaT_of_isOmegaEightPlus hΩ
  set ψ : spinGroup (quadPlus 4 F2) ≃* ↥Lb := spinOmegaEquiv.trans eL.symm with hψ
  obtain ⟨hPL, T₀, hT₀, hN⟩ := hP
  obtain ⟨T, hT⟩ := exists_sylow_of_isSylowTwoOf hT₀
  have hidx : ¬ 2 ∣ ((borel4 F2).map ψ.toMonoidHom).index := by
    rw [show ((borel4 F2).map ψ.toMonoidHom).index = (borel4 F2).index from
      Subgroup.index_map_equiv (H := borel4 F2) ψ]
    exact not_dvd_index_borel4 card_F2
  let SB : Sylow 2 ↥Lb := ((borel4_isPGroup card_F2).map ψ.toMonoidHom).toSylow hidx
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥Lb SB T
  set e : spinGroup (quadPlus 4 F2) ≃* ↥Lb := ψ.trans (MulAut.conj h) with he
  have heB : (borel4 F2).map e.toMonoidHom = (T : Subgroup ↥Lb) := by
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    change _ = Subgroup.map (MulAut.conj h).toMonoidHom ((borel4 F2).map ψ.toMonoidHom)
    rw [Subgroup.map_map]
    rfl
  set φ : spinGroup (quadPlus 4 F2) →* X := Lb.subtype.comp e.toMonoidHom with hφ
  have hφinj : Function.Injective φ := Lb.subtype_injective.comp e.injective
  have hφLb : ∀ k, φ k ∈ Lb := fun k => (e k).2
  have hPr : P ≤ φ.range := fun x hx =>
    ⟨e.symm ⟨x, hPL hx⟩, by simp [hφ]⟩
  have hBP : (borel4 F2).map φ ≤ P := by
    have h1 : (borel4 F2).map φ = T₀ := by
      rw [hφ, ← Subgroup.map_map, heB, hT, Subgroup.map_subgroupOf_eq_of_le hT₀.1]
    rw [h1]
    exact fun x hx => hN ⟨hT₀.1 hx, Subgroup.le_normalizer hx⟩
  set A := P.comap φ with hA
  have hBA : borel4 F2 ≤ A := Subgroup.map_le_iff_le_comap.mp hBP
  have hAP : A.map φ = P := Subgroup.map_comap_eq_self hPr
  set J := negType F2 A with hJ
  have hAJ : par F2 J = A := par_negType hBA
  let β : X →* MulAut (spinGroup (quadPlus 4 F2)) :=
    (MulAut.congr e.symm).toMonoidHom.comp (MulAut.conjNormal (H := Lb))
  have hβφ : ∀ x k, φ (β x k) = x * φ k * x⁻¹ := by
    intro x k
    change ((e (e.symm (MulAut.conjNormal x (e k))) : ↥Lb) : X) = _
    rw [MulEquiv.apply_symm_apply, MulAut.conjNormal_apply]
    rfl
  have hmap : ∀ x (C : Subgroup (spinGroup (quadPlus 4 F2))),
      (C.map (β x).toMonoidHom).map φ = (C.map φ).map (MulAut.conj x).toMonoidHom := by
    intro x C
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext k
    simp [hβφ]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, u ^ 3 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hu3 ⟨u, Subgroup.mem_zpowers u⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  have hβn : β u ^ 3 ^ n = 1 := by rw [← map_pow, hn, map_one]
  have hout : typeHom hU (β u) ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := mem_inner_of_typeHom_eq_one hU h1 hβn
    apply huout
    have hc : (φ k)⁻¹ * u ∈ Subgroup.centralizer (Lb : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro ℓ hℓ
      obtain ⟨k', rfl⟩ : ∃ k', φ k' = ℓ := ⟨e.symm ⟨ℓ, hℓ⟩, by simp [hφ]⟩
      have h2 : u * φ k' * u⁻¹ = φ k * φ k' * (φ k)⁻¹ := by
        rw [← hβφ, ← hk, MulAut.conj_apply, map_mul, map_mul, map_inv]
      calc φ k' * ((φ k)⁻¹ * u) = (φ k)⁻¹ * (φ k * φ k' * (φ k)⁻¹) * u := by group
        _ = (φ k)⁻¹ * (u * φ k' * u⁻¹) * u := by rw [h2]
        _ = (φ k)⁻¹ * u * φ k' := by group
    have : u = φ k * ((φ k)⁻¹ * u) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hφLb k)) (Subgroup.mem_sup_right hc)
  set σ := typeHom hU (β u) with hσ
  have hσ1 : σ 1 = 1 := (typePerm_spec hU (β u)).1
  have hσ3 : σ ^ 3 = 1 := pow_three_eq_one_of_pow (k := n) (by rw [hσ, ← map_pow, hβn, map_one])
  have hσJ : ⇑σ '' J = J := by
    obtain ⟨k, hk⟩ := (typePerm_spec hU (β u)).2 J
    have hAu : A.map (β u).toMonoidHom = A := by
      apply Subgroup.map_injective hφinj
      rw [hmap, hAP, map_conj_eq_of_mem_normalizer huN]
    rw [hAJ, hAu] at hk
    exact eq_of_map_conj_par card_F2 k (hk.symm.trans hAJ.symm)
  have hcyc := cycle_of_pow_three hσ1 hσ3 hout
  have hmem : ∀ x ∈ J, σ x ∈ J := fun x hx => hσJ ▸ ⟨x, hx, rfl⟩
  have hleaves : ((0 : Fin 4) ∈ J ↔ (2 : Fin 4) ∈ J) ∧ ((0 : Fin 4) ∈ J ↔ (3 : Fin 4) ∈ J) := by
    rcases hcyc with ⟨h0, h2, h3⟩ | ⟨h0, h3, h2⟩
    · refine ⟨⟨fun h => h0 ▸ hmem _ h, fun h => ?_⟩, ⟨fun h => h2 ▸ hmem _ (h0 ▸ hmem _ h),
        fun h => h3 ▸ hmem _ h⟩⟩
      exact h3 ▸ hmem _ (h2 ▸ hmem _ h)
    · refine ⟨⟨fun h => h3 ▸ hmem _ (h0 ▸ hmem _ h), fun h => h2 ▸ hmem _ h⟩,
        ⟨fun h => h0 ▸ hmem _ h, fun h => h2 ▸ hmem _ (h3 ▸ hmem _ h)⟩⟩
  obtain ⟨k, hk⟩ := (typePerm_spec hU (β m)).2 J
  rw [image_eq_of_leaves hleaves.1 hleaves.2 (typePerm_spec hU (β m)).1, hAJ] at hk
  refine ⟨φ k, hφLb k, ?_⟩
  rw [← hAP, ← hmap, hk, map_map_conj_hom]

omit hU in
theorem kFactOmega8Triality_proved : KFactOmega8Triality :=
  kFactOmega8Triality_of (posUnipotent_plusDatum_four (F := F2))

end CFSG.AGLEmbeddingD2.McLaughlin.Lie
