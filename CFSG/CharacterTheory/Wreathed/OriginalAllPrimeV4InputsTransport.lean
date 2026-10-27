module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeV4InputsModel
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeR1NModel
public import CFSG.LocalAnalysis.ABGTheoremB.V4Inputs
public import CFSG.LocalAnalysis.ABGTheoremB.V4Basic
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsModel

public section

namespace CFSG.Wreathed.OriginalAllPrime.V4InputsW

open CFSG.ABGTheoremB CFSG.ABGLocalTools
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.OddFieldTorus CFSG.Wreathed.OriginalAllPrime.IVFacts

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {F : Type} [Field F] [Fintype F]
  {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m} {Sigma : Subgroup (F ≃+* F)}
  {hSigma : ∀ τ ∈ Sigma, τ (b : F) = b}
  {φ : σ.N →* SemilinearExtension F b m hm heven Sigma hSigma}

omit [Finite G] in
theorem map_le_modelC_of_odd (hW : IsWModel σ φ) (h4 : 4 ∣ m)
    (hc : ∃ c ∈ σ.D, c * c = σ.x₂) {Y : Subgroup G} (hYN : Y ≤ σ.N) (hY : Odd (Nat.card Y))
    (hDY : σ.D ≤ Subgroup.normalizer (Y : Set G)) :
    (Y.subgroupOf σ.N).map φ ≤ ModelSignalizers.modelC b m hm heven Sigma hSigma := by
  obtain ⟨c, hcD, hcc⟩ := hc
  obtain ⟨d, hdD, hdN, -, -, X, hdX, hX⟩ := hW.exists_swap_iota
  have hcN : c ∈ σ.N := hW.D_le_N hcD
  have hx₂N : σ.x₂ ∈ σ.N := hW.model.x₂_mem
  obtain ⟨k, hk⟩ := σ.S.isPGroup' ⟨c, σ.D_le_S hcD⟩
  have hck : (⟨c, hcN⟩ : σ.N) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  obtain ⟨v, hv⟩ := mem_modelBase_of_two_pow hW.sigma_odd (g := φ ⟨c, hcN⟩) (k := k)
    (by rw [← map_pow, hck, map_one])
  have hvv : v * v = yV b m hm heven := by
    apply (SemidirectProduct.inl_injective :
      Function.Injective (SemidirectProduct.inl : CentralExtension F b m hm heven →*
        SemilinearExtension F b m hm heven Sigma hSigma))
    rw [map_mul, hv, ← map_mul, ← modelY_eq_inl_yV, ← hW.model.map_x₂]
    congr 1
    exact Subtype.ext hcc
  have hYodd : Odd (Nat.card ((Y.subgroupOf σ.N).map φ)) := by
    apply hY.of_dvd_nat
    refine (Subgroup.card_map_dvd _ φ).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv]
  have hnorm := hW.model.le_normalizer_map hYN hDY
  have hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨σ.p, σ.f, hW.p_prime, hW.p_odd, hW.one_le_f, hW.card⟩
  refine le_modelC_of_odd hF hW.two_ne_zero hW.nonsquare hW.two_part h4 hYodd ?_ hX ?_ hvv ?_
  · rw [← hW.model.map_x₂]
    exact hnorm ⟨⟨σ.x₂, hx₂N⟩, hW.x₂_mem_D, rfl⟩
  · rw [← hdX]
    exact hnorm ⟨⟨d, hdN⟩, hdD, rfl⟩
  · rw [hv]
    exact hnorm ⟨⟨c, hcN⟩, hcD, rfl⟩

theorem le_C_sup_ON_of_odd
    (hW : IsWModel σ φ) (h4 : 4 ∣ m) (hc : ∃ c ∈ σ.D, c * c = σ.x₂)
    {Y : Subgroup G} (hYN : Y ≤ σ.N) (hY : Odd (Nat.card Y))
    (hDY : σ.D ≤ Subgroup.normalizer (Y : Set G)) : Y ≤ σ.C ⊔ σ.ON := by
  intro y hy
  have hmem := map_le_modelC_of_odd hW h4 hc hYN hY hDY ⟨⟨y, hYN hy⟩, hy, rfl⟩
  rw [ModelSignalizers.modelC, ← hW.model.map_C] at hmem
  exact hW.model.mem_of_map_mem le_sup_right
    (Subgroup.map_mono (Subgroup.comap_mono le_sup_left) hmem)

theorem x₂_commutator_mem_ON
    (hW : IsWModel σ φ) (h4 : 4 ∣ m) (hc : ∃ c ∈ σ.D, c * c = σ.x₂)
    {X : Subgroup G} (hXN : X ≤ σ.N) (hX : IsPGroup σ.p X)
    (hDX : σ.D ≤ Subgroup.normalizer (X : Set G)) {y : G} (hy : y ∈ X) :
    σ.x₂ * y * σ.x₂⁻¹ * y⁻¹ ∈ σ.ON := by
  have : Fact σ.p.Prime := ⟨hW.p_prime⟩
  have hodd : Odd (Nat.card X) := by
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    rw [hk]
    exact hW.p_odd.pow
  have hmem := map_le_modelC_of_odd hW h4 hc hXN hodd hDX ⟨⟨y, hXN hy⟩, hy, rfl⟩
  rw [ModelSignalizers.modelC, Subgroup.mem_centralizer_singleton_iff, ← hW.model.map_x₂]
    at hmem
  have hx₂N : σ.x₂ ∈ σ.N := hW.model.x₂_mem
  have h := (hW.mem_ON_iff (⟨σ.x₂, hx₂N⟩ * ⟨y, hXN hy⟩ * (⟨σ.x₂, hx₂N⟩ : σ.N)⁻¹ *
    (⟨y, hXN hy⟩ : σ.N)⁻¹)).mpr (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hmem]
      group)
  simpa using h

theorem exists_mem_W_map_eq (hW : IsWModel σ φ) (hσ : σ.IsValid) {J : Subgroup G}
    (hJ : σ.IsV21Layer J) (hCodd : ∀ c ∈ σ.C, Odd (orderOf c) → c ∈ oddCoreIn σ.C)
    {W : Subgroup G} (hWW : W ∈ σ.familyW J)
    {WF : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hWF : ∀ g, g ∈ WF ↔ g ∈ torus F ∧ Odd (orderOf g))
    {w : Matrix.SpecialLinearGroup (Fin 2) F} (hw : w ∈ WF) :
    ∃ u ∈ W, ∃ huN : u ∈ σ.N, φ ⟨u, huN⟩ = iota b m hm heven Sigma hSigma w := by
  obtain ⟨hwT, hwodd⟩ := (hWF w).mp hw
  have h1 : iota b m hm heven Sigma hSigma w ∈ (σ.C.subgroupOf σ.N).map φ := by
    rw [hW.model.map_C]
    exact (ModelSignalizers.inl_specialInclusion_mem_modelC_iff w).mpr hwT
  obtain ⟨g, hgC, hg⟩ := h1
  have hgL₀ : (g : G) ∈ σ.L₀ := hW.model.mem_of_map_mem hW.model.ON_le (by
    rw [hg, hW.model.map_L₀, modelLayer_eq_range]
    exact ⟨w, rfl⟩)
  obtain ⟨j, hj, o, ho, hjo⟩ := V4.exists_mul_eq_of_mem_C_inf_L₀ hσ hJ hgC hgL₀
  have hjN : j ∈ σ.N := σ.C_le_N hj.1
  have hoN : o ∈ σ.N := σ.ON_le_N ho
  set jN : σ.N := ⟨j, hjN⟩ with hjNdef
  have hφj : φ jN = iota b m hm heven Sigma hSigma w := by
    have h2 : g = jN * ⟨o, hoN⟩ := Subtype.ext hjo.symm
    have h3 : φ ⟨o, hoN⟩ = 1 := (hW.mem_ON_iff _).mp ho
    rw [← hg, h2, map_mul, h3, mul_one]
  obtain ⟨u, hu, i, hi⟩ := CFSG.ABGDGroups.exists_zpow_odd_and_two_pow jN
    (isOfFinOrder_of_finite jN)
  have hφodd : Odd (orderOf (φ jN)) := by
    rw [hφj, orderOf_injective _ (iota_injective b m hm heven Sigma hSigma)]
    exact hwodd
  have hφu : φ (jN ^ u) = φ jN := by
    set e := φ (jN * (jN ^ u)⁻¹) with hedef
    have he : e ∈ Subgroup.zpowers (φ jN) := by
      rw [hedef, map_mul, map_inv, map_zpow]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _)
        (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) u))
    have he2 : e ^ 2 ^ i = 1 := by rw [hedef, ← map_pow, hi, map_one]
    have hcop : Nat.Coprime (2 ^ i) (orderOf (φ jN)) :=
      (Nat.coprime_two_left.mpr hφodd).pow_left i
    have he1 : e = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one he2) (orderOf_dvd_of_mem_zpowers he))
    rw [hedef, map_mul, map_inv, mul_inv_eq_one] at he1
    exact he1.symm
  set j' : G := ((jN ^ u : σ.N) : G) with hj'def
  have hj'C : j' ∈ σ.C ⊓ J := by
    rw [hj'def, Subgroup.coe_zpow]
    exact Subgroup.zpow_mem _ hj u
  have hj'odd : Odd (orderOf j') := by
    rw [hj'def, Subgroup.orderOf_coe]
    exact hu
  have hj'O : j' ∈ oddCoreIn σ.C ⊓ J := ⟨hCodd j' hj'C.1 hj'odd, hj'C.2⟩
  have hj'W : j' ∈ W ⊔ pCoreIn σ.p σ.N := by
    rw [hWW.2.2.2]
    exact Subgroup.mem_sup_left hj'O
  have hWp : W ≤ Subgroup.normalizer (pCoreIn σ.p σ.N : Set G) :=
    (V4.W_le_N hσ hJ hWW).trans V4.N_le_normalizer_pCore
  obtain ⟨u', hu'W, k, hk, hu'k⟩ := (V4.mem_sup_iff_of_le_normalizer hWp).mp hj'W
  have hu'N : u' ∈ σ.N := V4.W_le_N hσ hJ hWW hu'W
  have hkN : k ∈ σ.N := σ.ON_le_N (V4.pCore_N_le_ON hσ hk)
  refine ⟨u', hu'W, hu'N, ?_⟩
  have h2 : jN ^ u = ⟨u', hu'N⟩ * ⟨k, hkN⟩ := Subtype.ext hu'k.symm
  have h3 : φ ⟨k, hkN⟩ = 1 := (hW.mem_ON_iff _).mp (V4.pCore_N_le_ON hσ hk)
  rw [← hφj, ← hφu, h2, map_mul, h3, mul_one]

theorem lemmaII42Input_of_isWModel (hW : IsWModel σ φ) (hσ : σ.IsValid)
    (hCodd : ∀ c ∈ σ.C, Odd (orderOf c) → c ∈ oddCoreIn σ.C) {J : Subgroup G}
    (hJ : σ.IsV21Layer J) : V4.LemmaII42Input σ J := by
  intro W hWW X hXC hWX y hyX hy
  obtain ⟨WF, hWF⟩ := exists_oddTorus F
  have hyC : y ∈ σ.C := oddCoreIn_le σ.C (hXC hyX)
  have hyN : y ∈ σ.N := σ.C_le_N hyC
  set yN : σ.N := ⟨y, hyN⟩ with hyNdef
  by_contra hyL
  have hyodd : Odd (orderOf yN) := (odd_card_oddCoreIn σ.C).of_dvd_nat (by
    rw [hyNdef, Subgroup.orderOf_mk, ← Subgroup.orderOf_mk y (hXC hyX)]
    exact orderOf_dvd_natCard _)
  have hφodd : ∀ k : ℕ, Odd (orderOf (φ (yN ^ k))) := fun k =>
    hyodd.of_dvd_nat ((orderOf_map_dvd φ _).trans (orderOf_pow_dvd k))
  have hφC : ∀ k : ℕ, φ (yN ^ k) ∈ ModelSignalizers.modelC b m hm heven Sigma hSigma :=
    fun k => hW.map_mem_modelC _ (σ.C.pow_mem hyC k)
  obtain ⟨w₁, -, τ, hτ⟩ := exists_eq_of_odd hW.p_prime hW.p_odd hW.one_le_f hW.card hm heven
    hW.two_part hW.sigma_odd hSigma hW.nonsquare hWF (by simpa using hφC 1)
    (by simpa using hφodd 1)
  have hright : ∀ k : ℕ, SemidirectProduct.rightHom (φ (yN ^ k)) = τ ^ k := by
    intro k
    rw [map_pow, map_pow, hτ, map_mul, iota_apply, SemidirectProduct.rightHom_inl,
      SemidirectProduct.rightHom_inr, one_mul]
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    apply hyL
    rw [hW.mem_L_iff yN, hτ, map_one, mul_one, iota_apply]
    exact ⟨_, rfl⟩
  set t := orderOf (τ : F ≃+* F) with htdef
  have ht0 : t ≠ 0 := (orderOf_pos (τ : F ≃+* F)).ne'
  have ht1 : t ≠ 1 := fun h => hτ1 (Subtype.ext (orderOf_eq_one_iff.mp h))
  obtain ⟨r, hr, hrt⟩ := Nat.exists_prime_and_dvd ht1
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h1 : t ∣ Nat.card Sigma := by
      rw [htdef, Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard τ
    exact (Nat.not_even_iff_odd.mpr hW.sigma_odd) (even_iff_two_dvd.mpr (hrt.trans h1))
  set k' := t / r with hk'def
  obtain ⟨w', hw', τ', hτ'⟩ := exists_eq_of_odd hW.p_prime hW.p_odd hW.one_le_f hW.card hm heven
    hW.two_part hW.sigma_odd hSigma hW.nonsquare hWF (hφC k') (hφodd k')
  have hτ'eq : τ' = τ ^ k' := by
    rw [← hright k', hτ', map_mul, iota_apply, SemidirectProduct.rightHom_inl,
      SemidirectProduct.rightHom_inr, one_mul]
  have hτ'r : orderOf (τ' : F ≃+* F) = r := by
    rw [hτ'eq, Subgroup.coe_pow, hk'def]
    exact orderOf_pow_orderOf_div ht0 hrt
  obtain ⟨s, hs, -, -, w₀, hw₀, hw₀s, hnorm, hfpf⟩ := exists_fixedPointFree hW.p_prime hW.p_odd
    hW.one_le_f hW.card hW.two_part hW.sigma_odd hWF (τ' : F ≃+* F) τ'.2 hr hr2 hτ'r
  have hw₀T : w₀ ∈ torus F := ((hWF w₀).mp hw₀).1
  have hw'T : w' ∈ torus F := ((hWF w').mp hw').1
  obtain ⟨u, huW, huN, hu⟩ := exists_mem_W_map_eq hW hσ hJ hCodd hWW hWF hw₀
  set uN : σ.N := ⟨u, huN⟩ with huNdef
  set zN : σ.N := uN * yN ^ k' * uN⁻¹ * (yN ^ k')⁻¹ with hzNdef
  have hzX : (zN : G) ∈ ⁅X, X⁆ := by
    have h := Subgroup.commutator_mem_commutator (hWX huW) (X.pow_mem hyX k')
    rw [commutatorElement_def] at h
    simpa [hzNdef, huNdef, hyNdef] using h
  set A := iota b m hm heven Sigma hSigma w' * SemidirectProduct.inr τ' with hAdef
  set k₀ := w₀ * (fieldSL F τ' w₀)⁻¹ with hk₀def
  have hk₀ : k₀ ∈ Subgroup.zpowers w₀ :=
    Subgroup.mul_mem _ (Subgroup.mem_zpowers w₀)
      (Subgroup.inv_mem _ (hnorm w₀ (Subgroup.mem_zpowers w₀)))
  have hk₀T : k₀ ∈ torus F := ((hWF k₀).mp (Subgroup.zpowers_le.mpr hw₀ hk₀)).1
  have hφz : φ zN = iota b m hm heven Sigma hSigma k₀ := by
    have hconj := conj_iota_of_mem_torus b m hm heven Sigma hSigma τ' hw'T
      ((torus F).inv_mem hw₀T)
    rw [hzNdef, map_mul, map_mul, map_mul, map_inv, map_inv, hu, hτ']
    calc iota b m hm heven Sigma hSigma w₀ * A * (iota b m hm heven Sigma hSigma w₀)⁻¹ * A⁻¹
        = iota b m hm heven Sigma hSigma w₀ *
            (A * iota b m hm heven Sigma hSigma w₀⁻¹ * A⁻¹) := by rw [map_inv]; group
      _ = iota b m hm heven Sigma hSigma w₀ *
            iota b m hm heven Sigma hSigma (fieldSL F τ' w₀⁻¹) := by rw [hAdef, hconj]
      _ = iota b m hm heven Sigma hSigma k₀ := by rw [← map_mul, map_inv]
  have hcomm : φ yN * φ zN = φ zN * φ yN := by
    have h1 := (hW.mem_ON_iff (yN * zN * yN⁻¹ * zN⁻¹)).mp (by simpa using hy _ hzX)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc φ yN * φ zN = φ yN * φ zN * (φ yN)⁻¹ * (φ zN)⁻¹ * (φ zN * φ yN) := by group
      _ = φ zN * φ yN := by rw [h1, one_mul]
  have hcommA : A * iota b m hm heven Sigma hSigma k₀ =
      iota b m hm heven Sigma hSigma k₀ * A := by
    have h1 := (Commute.pow_left hcomm k').eq
    rw [← map_pow, hτ', hφz] at h1
    exact h1
  have hfix : fieldSL F τ' k₀ = k₀ := by
    have h1 : A * iota b m hm heven Sigma hSigma k₀ * A⁻¹ =
        iota b m hm heven Sigma hSigma (fieldSL F τ' k₀) :=
      conj_iota_of_mem_torus b m hm heven Sigma hSigma τ' hw'T hk₀T
    rw [hcommA, mul_inv_cancel_right] at h1
    exact (iota_injective b m hm heven Sigma hSigma h1).symm
  have hk₀1 := hfpf k₀ hk₀ hfix
  have hw₀fix : fieldSL F τ' w₀ = w₀ := (mul_inv_eq_one.mp hk₀1).symm
  have hw₀1 := hfpf w₀ (Subgroup.mem_zpowers w₀) hw₀fix
  rw [hw₀1, orderOf_one] at hw₀s
  exact hs.one_lt.ne hw₀s

theorem lemmaII46Input_of_isWModel
    (hW : IsWModel σ φ) (hσ : σ.IsValid) {J : Subgroup G}
    (hJ : σ.IsV21Layer J) : V4.LemmaII46Input σ J := by
  intro W hWW r hr hrW W₀ hW₀ hW₀N Y hYN hYr hYT hYON
  by_contra hev
  rw [Nat.not_even_iff_odd] at hev
  obtain ⟨WF, hWF⟩ := exists_oddTorus F
  have : Fact σ.p.Prime := ⟨hW.p_prime⟩
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr (V4.odd_card_W hσ hJ hWW)) (even_iff_two_dvd.mpr hrW)
  have hrp : r ≠ σ.p := by
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := W) r hrW
    have huN : (u : G) ∈ σ.N := V4.W_le_N hσ hJ hWW u.2
    have huCL : (u : G) ∈ σ.C ⊓ σ.L₀ := ⟨V4.W_le_C hσ hJ hWW u.2, hJ.le (hWW.1 u.2)⟩
    obtain ⟨Z, hZT, hZ⟩ := hW.exists_torus_of_mem ⟨u, huN⟩ huCL
    have hφu : orderOf (φ ⟨u, huN⟩) = r := by
      have h1 : orderOf (φ ⟨u, huN⟩) ∣ r := by
        refine (orderOf_map_dvd φ _).trans ?_
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hu]
      rcases (Nat.dvd_prime hr).mp h1 with h | h
      · exfalso
        have hu1 : (u : G) ∈ W ⊓ σ.ON :=
          ⟨u.2, (hW.mem_ON_iff ⟨u, huN⟩).mpr (orderOf_eq_one_iff.mp h)⟩
        rw [V4.W_inf_ON hJ hWW, Subgroup.mem_bot] at hu1
        have hu1' : u = 1 := Subtype.ext hu1
        rw [hu1', orderOf_one] at hu
        exact hr.one_lt.ne hu
      · exact h
    have hZr : orderOf Z = r := by
      rw [← hφu, hZ, orderOf_injective _ (iota_injective b m hm heven Sigma hSigma)]
    have hZW : Z ∈ WF := (hWF Z).mpr ⟨hZT, by rw [hZr]; exact hr.odd_of_ne_two hr2⟩
    have hrWF : r ∣ Nat.card WF := by
      rw [← hZr, ← Subgroup.orderOf_mk Z hZW]
      exact orderOf_dvd_natCard _
    obtain ⟨-, -, -, hA, -⟩ := torus_arith hW.p_prime hW.p_odd hW.one_le_f hW.card hW.two_part
      hW.sigma_odd hWF 1 Sigma.one_mem
    intro hrp
    rw [hrp] at hrWF
    have h1 : (σ.p : ℤ) ∣ ((σ.p ^ σ.f : ℕ) : ℤ) -
        (if σ.p ^ σ.f % 4 = 1 then (1 : ℤ) else -1) := by
      rw [← hA]
      exact (Int.natCast_dvd_natCast.mpr hrWF).mul_right _
    have h2 : (σ.p : ℤ) ∣ ((σ.p ^ σ.f : ℕ) : ℤ) := by
      push_cast
      exact dvd_pow_self _ (by have := hW.one_le_f; omega)
    have h3 := dvd_sub h2 h1
    rw [sub_sub_cancel] at h3
    have h4 : (σ.p : ℤ) ∣ 1 := by
      split_ifs at h3
      · exact h3
      · exact (dvd_neg.mp h3)
    have h5 : σ.p ∣ 1 := by exact_mod_cast h4
    exact hW.p_prime.one_lt.ne' (Nat.dvd_one.mp h5)
  have hTL : σ.T ≤ σ.L := (σ.T_le_D hσ).trans (σ.D_le_S.trans le_sup_right)
  have hYL : Y ≤ σ.L := by
    rw [← hYT, Subgroup.commutator_le]
    intro y hy t ht
    rw [commutatorElement_def]
    exact σ.L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hW.L_normal (hYN hy)) t).mp (hTL ht))
      (σ.L.inv_mem (hTL ht))
  have hTY : σ.T ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hYT.le
  set K₁ := W₀ ⊔ Y with hK₁def
  have hW₀C : W₀ ≤ σ.C := hW₀.trans (inf_le_left.trans (oddCoreIn_le σ.C))
  have hK₁N : K₁ ≤ σ.N := sup_le (hW₀C.trans σ.C_le_N) hYN
  have hK₁L : K₁ ≤ σ.L := sup_le (hW₀.trans inf_le_right) hYL
  have hK₁odd : Odd (Nat.card K₁) := hev.of_dvd_nat (Subgroup.card_dvd_of_le le_sup_left)
  have hx₂W₀ : σ.x₂ ∈ Subgroup.normalizer (W₀ : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hW₀C hw) σ.x₂ σ.x₂_mem_T).symm
  have hx₂K₁ : σ.x₂ ∈ Subgroup.normalizer (K₁ : Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hx₂W₀, hTY σ.x₂_mem_T⟩
  have hx₂N : σ.x₂ ∈ σ.N := hW.model.x₂_mem
  set Kb := (K₁.subgroupOf σ.N).map φ with hKbdef
  set Yb := (Y.subgroupOf σ.N).map φ with hYbdef
  have hKb : Odd (Nat.card Kb) := by
    apply hK₁odd.of_dvd_nat
    refine (Subgroup.card_map_dvd _ φ).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₁N).toEquiv]
  have hKbM : Kb ≤ ModelSignalizers.modelLayer b m hm heven Sigma hSigma := by
    rintro _ ⟨g, hg, rfl⟩
    have hgB := (hW.mem_L_iff g).mp (hK₁L hg)
    have hgK : φ g ∈ Kb := ⟨g, hg, rfl⟩
    have hpow : φ g ^ Nat.card Kb = 1 := by
      have h := pow_card_eq_one' (G := Kb) (x := ⟨φ g, hgK⟩)
      exact congrArg Subtype.val h
    exact R1NFacts.mem_modelLayer_of_pow_eq_one hW.two_part hKb hgB hpow
  have hyKb : ModelSignalizers.modelY b m hm heven Sigma hSigma ∈
      Subgroup.normalizer (Kb : Set _) := by
    rw [← hW.model.map_x₂]
    exact hW.model.le_normalizer_map hK₁N (Subgroup.zpowers_le.mpr hx₂K₁)
      ⟨⟨σ.x₂, hx₂N⟩, Subgroup.mem_zpowers σ.x₂, rfl⟩
  have hyYb : ModelSignalizers.modelY b m hm heven Sigma hSigma ∈
      Subgroup.normalizer (Yb : Set _) := by
    rw [← hW.model.map_x₂]
    exact hW.model.le_normalizer_map hYN (Subgroup.zpowers_le.mpr (hTY σ.x₂_mem_T))
      ⟨⟨σ.x₂, hx₂N⟩, Subgroup.mem_zpowers σ.x₂, rfl⟩
  obtain ⟨g, hgW₀, hgON⟩ := IsConcreteLE.not_le_iff_exists.mp hW₀N
  have hgC : g ∈ σ.C := hW₀C hgW₀
  have hgN : g ∈ σ.N := σ.C_le_N hgC
  obtain ⟨v, hv⟩ := (hW.mem_L_iff ⟨g, hgN⟩).mp ((hW₀.trans inf_le_right) hgW₀)
  have hvC : v ∈ Subgroup.centralizer {yV b m hm heven} := by
    have h := hW.map_mem_modelC ⟨g, hgN⟩ hgC
    rw [← hv, ModelSignalizers.inl_mem_modelC_iff] at h
    exact h
  have hgodd : Odd (orderOf g) := (odd_card_oddCoreIn σ.C).of_dvd_nat (by
    rw [← Subgroup.orderOf_mk g ((hW₀.trans inf_le_left) hgW₀)]
    exact orderOf_dvd_natCard _)
  have hvodd : Odd (orderOf v) := by
    have h1 : orderOf (φ ⟨g, hgN⟩) ∣ orderOf g := by
      rw [← Subgroup.orderOf_mk g hgN]
      exact orderOf_map_dvd φ _
    rw [← hv, orderOf_injective _ SemidirectProduct.inl_injective] at h1
    exact hgodd.of_dvd_nat h1
  obtain ⟨w, hwW, hwv⟩ := exists_eq_iF_of_odd hW.p_prime hW.p_odd hW.one_le_f hW.card hm heven
    hW.two_part hW.sigma_odd hSigma hW.nonsquare hWF hvC hvodd
  have hφg : φ ⟨g, hgN⟩ = iota b m hm heven Sigma hSigma w := by
    rw [← hv, iota_apply, hwv]
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hgON
    rw [hW.mem_ON_iff ⟨g, hgN⟩, hφg, map_one]
  have hYb : Yb ≤ ModelSignalizers.modelC b m hm heven Sigma hSigma :=
    le_modelC_of_isPGroup hσ.p_ne_two hW.one_le_f hW.card hKb hKbM hyKb
      ((hWF w).mp hwW).1 hw1 ((hWF w).mp hwW).2 ⟨⟨g, hgN⟩, le_sup_left (a := W₀) hgW₀, hφg⟩
      (Subgroup.map_mono (Subgroup.comap_mono le_sup_right)) hr hrp
      ((hYr.comap_of_injective _ σ.N.subtype_injective).map φ) hyYb
  apply hYON
  rw [← hYT, Subgroup.commutator_le]
  intro y hy t ht
  have hyN := hYN hy
  have htN : t ∈ σ.N := σ.T_le_N hσ ht
  have hyC : φ ⟨y, hyN⟩ ∈ (σ.C.subgroupOf σ.N).map φ := by
    rw [hW.model.map_C]
    exact hYb ⟨⟨y, hyN⟩, hy, rfl⟩
  obtain ⟨c, hcC, hc⟩ := hyC
  have hct : (c : G) * t = t * c := (Subgroup.mem_centralizer_iff.mp hcC t ht).symm
  have hct' : c * ⟨t, htN⟩ = ⟨t, htN⟩ * c := Subtype.ext hct
  have h1 := (hW.mem_ON_iff (⟨y, hyN⟩ * ⟨t, htN⟩ * (⟨y, hyN⟩ : σ.N)⁻¹ * (⟨t, htN⟩ : σ.N)⁻¹)).mpr
    (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc, ← map_mul, hct', map_mul]; group)
  rw [commutatorElement_def]
  simpa using h1

end CFSG.Wreathed.OriginalAllPrime.V4InputsW
