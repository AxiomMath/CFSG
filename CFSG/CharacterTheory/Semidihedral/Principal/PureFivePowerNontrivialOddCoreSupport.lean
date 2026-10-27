module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusExclusionSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.PureFivePowerTorusAlternatingFourSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour

namespace PureFiveNontrivialCore

theorem projection_apply_of_mul {G : Type*} [Group G] (K W : Subgroup G) {a : ℕ}
    (hWcard : Nat.card W = 5 ^ a) (π : K →* W) (hπW : ∀ k : K, (k : G) ∈ W → (π k : G) = k)
    (k : K) {w j : G} (hw : w ∈ W) (hwK : w ∈ K) (hjK : j ∈ K) (hk : (k : G) = w * j)
    (hj : Nat.Coprime 5 (orderOf j)) : (π k : G) = w := by
  have hk' : k = ⟨w, hwK⟩ * ⟨j, hjK⟩ := Subtype.ext hk
  have hπj : π ⟨j, hjK⟩ = 1 := by
    have h1 : orderOf (π ⟨j, hjK⟩) ∣ orderOf j := by
      rw [← Subgroup.orderOf_mk j hjK]
      exact orderOf_map_dvd π _
    have h2 : orderOf (π ⟨j, hjK⟩) ∣ 5 ^ a := by
      rw [← hWcard]
      exact orderOf_dvd_natCard _
    have h3 := Nat.dvd_gcd h2 h1
    rw [Nat.Coprime.gcd_eq_one (hj.pow_left a)] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  rw [hk', map_mul, Subgroup.coe_mul, hπW ⟨w, hwK⟩ hw, hπj, OneMemClass.coe_one, mul_one]

theorem mem_of_coprime_of_sup {X : Type*} [Group X] {W J : Subgroup X}
    (hsup : W ⊔ J = Subgroup.centralizer (W : Set X)) (hdisj : W ⊓ J = ⊥) {a : ℕ}
    (hWcard : Nat.card W = 5 ^ a) (k : Subgroup.centralizer (W : Set X))
    (hk : Nat.Coprime 5 (orderOf (k : X))) : (k : X) ∈ J := by
  obtain ⟨w, j, hkwj⟩ := FivePowerColumn.exists_eq_mul hsup hdisj k
  have hw₀ : (w : X) = 1 := by
    have hvpow : ((w : X) * j) ^ orderOf (k : X) = 1 := by
      rw [← hkwj]
      exact pow_orderOf_eq_one _
    rw [(FivePowerColumn.commute_of_mem hsup w.2 j.2).mul_pow] at hvpow
    have hmemJ : (w : X) ^ orderOf (k : X) ∈ J := by
      rw [eq_inv_of_mul_eq_one_left hvpow]
      exact J.inv_mem (J.pow_mem j.2 _)
    have hone : (w : X) ^ orderOf (k : X) = 1 := by
      have hmem : (w : X) ^ orderOf (k : X) ∈ W ⊓ J := ⟨W.pow_mem w.2 _, hmemJ⟩
      rwa [hdisj, Subgroup.mem_bot] at hmem
    have hd1 : orderOf (w : X) ∣ orderOf (k : X) := orderOf_dvd_of_pow_eq_one hone
    have hd2 : orderOf (w : X) ∣ 5 ^ a := by
      rw [Subgroup.orderOf_coe, ← hWcard]
      exact orderOf_dvd_natCard w
    have hd := Nat.dvd_gcd hd2 hd1
    rw [Nat.Coprime.gcd_eq_one (hk.pow_left a), Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  rw [hkwj, hw₀, one_mul]
  exact j.2

theorem local_A4_column_pairing {G : Type} [Group G] [Fintype G]
    (W K H : Subgroup G) [IsCyclic W] (a : ℕ) (hWcard : Nat.card W = 5 ^ a)
    (hK : K = Subgroup.centralizer (W : Set G)) (hKH' : K ≤ H) (hWH : W ≤ H)
    [(W.subgroupOf H).Normal] (hKH : K.relIndex H = 2)
    (hR : (CFSG.pPrimeCore 2 K).map K.subtype = W)
    (hA4 : Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)))
    (hdih : ∃ P : Sylow 2 H, Nonempty ((P : Subgroup H) ≃* DihedralGroup 4))
    (t : G) (htK : t ∈ K) (ht2 : orderOf t = 2)
    (π : K →* W) (hπW : ∀ k : K, (k : G) ∈ W → (π k : G) = k)
    (lam : W →* ℂˣ) (hlam : orderOf lam = 5) (localBasis : FiniteIrreducibleCharacterBasis H) :
    (Nat.card H : ℂ) * characterPairing (fun k : K => 1 - (lam (π k) : ℂ))
        (fun k => ∑ α : localBasis.index,
          ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
            (localBasis.representation α).character u) ^ 2 *
            (localBasis.representation α).character ⟨k, hKH' k.2⟩ /
            (localBasis.representation α).character 1) = 3 * (5 : ℂ) ^ a := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set W' : Subgroup H := W.subgroupOf H with hW'def
  have : IsCyclic W' := isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hWH).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hWH).symm.surjective
  have hW'card : Nat.card W' = 5 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv, hWcard]
  have hcent : Subgroup.centralizer (W' : Set H) = K.subgroupOf H := by
    ext h
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, hK, Subgroup.mem_centralizer_iff]
    constructor
    · intro hh w hw
      exact congrArg Subtype.val (hh ⟨w, hWH hw⟩ hw)
    · intro hh w hw
      exact Subtype.ext (hh w hw)
  have hindex' : (Subgroup.centralizer (W' : Set H)).index = 2 := by
    rw [hcent]
    exact hKH
  let φ : Subgroup.centralizer (W' : Set H) ≃* K :=
    (MulEquiv.subgroupCongr hcent).trans (Subgroup.subgroupOfEquivOfLe hKH')
  have hφval : ∀ x : Subgroup.centralizer (W' : Set H), ((φ x : K) : G) = ((x : H) : G) :=
    fun x => rfl
  have hmapN : (W'.subgroupOf (Subgroup.centralizer (W' : Set H))).map φ.toMonoidHom =
      CFSG.pPrimeCore 2 K := by
    ext k
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxW : ((x : H) : G) ∈ W := hx
      rw [← hR] at hxW
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxW
      have : y = φ.toMonoidHom x := Subtype.ext (by
        change (y : G) = ((φ x : K) : G)
        rw [hφval]
        exact hyx)
      rw [← this]
      exact hy
    · intro hk
      refine ⟨φ.symm k, ?_, by simp⟩
      change (((φ.symm k : Subgroup.centralizer (W' : Set H)) : H) : G) ∈ W
      have h1 : (((φ.symm k : Subgroup.centralizer (W' : Set H)) : H) : G) = (k : G) := by
        rw [← hφval, MulEquiv.apply_symm_apply]
      rw [h1, ← hR]
      exact ⟨k, hk, rfl⟩
  obtain ⟨ψA⟩ := hA4
  have hquot : Nonempty (Subgroup.centralizer (W' : Set H) ⧸
      W'.subgroupOf (Subgroup.centralizer (W' : Set H)) ≃* alternatingGroup (Fin 4)) :=
    ⟨(QuotientGroup.congr _ _ φ hmapN).trans ψA⟩
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation H)
    (principalFiniteComplexRepresentation_isIrreducible H)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨J', π', E', σ', -, -, hJ'cop, hsup', hdisj', -, -, -, hπ'W, -, -, -, -, -, -, -, -, -,
      -, -, -, -, hcol⟩ :=
    cyclic_prime_power_A4_centralizer_inversion_normalizer_sign_S4_column_sum 5 le_rfl a W'
      hW'card hindex' hquot hdih localBasis localPrincipal hlocalPrincipal
  set lam' : W' →* ℂˣ := lam.comp (Subgroup.subgroupOfEquivOfLe hWH).toMonoidHom with hlam'def
  have hlam' : orderOf lam' = 5 := by
    have hlam5 : lam ^ 5 = 1 := hlam ▸ pow_orderOf_eq_one lam
    apply orderOf_eq_prime
    · rw [hlam'def]
      ext w
      simp only [MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.one_apply]
      rw [← MonoidHom.pow_apply, hlam5, MonoidHom.one_apply]
    · intro h1
      have hne : lam ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hlam
        norm_num at hlam
      apply hne
      ext w
      have h := congrArg (fun χ : W' →* ℂˣ => (χ ((Subgroup.subgroupOfEquivOfLe hWH).symm w) : ℂ))
        h1
      simpa [hlam'def] using h
  obtain ⟨θε, θμ, -, -, -, -, -, hfinal⟩ := hcol lam' hlam'
  set t' : H := ⟨t, hKH' htK⟩ with ht'def
  have ht'C : t' ∈ Subgroup.centralizer (W' : Set H) := by
    rw [hcent, Subgroup.mem_subgroupOf]
    exact htK
  have ht'2 : orderOf t' = 2 := by rw [ht'def, Subgroup.orderOf_mk]; exact ht2
  have ht'J : t' ∈ J' := mem_of_coprime_of_sup hsup' hdisj' hW'card ⟨t', ht'C⟩
    (by change Nat.Coprime 5 (orderOf t'); rw [ht'2]; norm_num)
  set x' : E' := σ'.symm (Equiv.swap 0 1) with hx'def
  have hx' : (σ' x').IsSwap := ⟨0, 1, by decide, by rw [hx'def, MulEquiv.apply_symm_apply]⟩
  obtain ⟨-, -, hsum⟩ := hfinal t' ht'J ht'2 x' hx'
  set ι : Subgroup.centralizer (W' : Set H) → K := fun k' => φ k' with hιdef
  have hιbij : Function.Bijective ι := φ.bijective
  have hπ : ∀ k' : Subgroup.centralizer (W' : Set H),
      (((π' k' : W') : H) : G) = (π (ι k') : G) := by
    intro k'
    obtain ⟨w', j', hk'⟩ := FivePowerColumn.exists_eq_mul hsup' hdisj' k'
    have hj'cop : Nat.Coprime 5 (orderOf (j' : H)) := by
      rw [Subgroup.orderOf_coe]
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard j') hJ'cop
    have hloc := projection_apply_of_mul (Subgroup.centralizer (W' : Set H)) W' hW'card π' hπ'W
      k' w'.2 ((FivePowerColumn.left_le_centralizer hsup') w'.2)
      ((FivePowerColumn.right_le_centralizer hsup') j'.2) hk' hj'cop
    have hjK : ((j' : H) : G) ∈ K := by
      have h := (FivePowerColumn.right_le_centralizer hsup') j'.2
      rw [hcent, Subgroup.mem_subgroupOf] at h
      exact h
    have hglob := projection_apply_of_mul K W hWcard π hπW (ι k') (w := ((w' : H) : G))
      (j := ((j' : H) : G)) w'.2 (hK ▸ CyclicInversion.le_centralizer_of_isCyclic W w'.2) hjK
      (by
        change ((k' : H) : G) = _
        rw [hk']
        rfl)
      (by rw [Subgroup.orderOf_coe]; exact hj'cop)
    rw [hglob, hloc]
  rw [show ((5 : ℕ) : ℂ) = 5 by norm_num] at hsum
  set FH : H → ℂ := fun h => ∑ α : localBasis.index,
    ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
      (localBasis.representation α).character u) ^ 2 *
        (localBasis.representation α).character h / (localBasis.representation α).character 1
    with hFHdef
  have hFHclass : ∀ h c : H, FH (c * h * c⁻¹) = FH h := by
    intro h c
    rw [hFHdef]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [show (localBasis.representation α).character (c * h * c⁻¹) =
      (localBasis.representation α).character h from Representation.char_conj _ h c]
  have hexp : ∑ α : localBasis.index, characterPairing
      (inducedFunction (Subgroup.centralizer (W' : Set H)) (fun k => 1 - (lam' (π' k) : ℂ)))
      (localBasis.representation α).character * ((Nat.card H : ℂ)⁻¹ *
        ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
          (localBasis.representation α).character u) ^ 2 /
        (localBasis.representation α).character 1 =
      characterPairing
        (inducedFunction (Subgroup.centralizer (W' : Set H)) (fun k => 1 - (lam' (π' k) : ℂ)))
        FH := by
    have hFH : FH = fun h => ∑ α ∈ Finset.univ, (((Nat.card H : ℂ)⁻¹ *
        ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
          (localBasis.representation α).character u) ^ 2 /
            (localBasis.representation α).character 1) *
        (localBasis.representation α).character h := by
      rw [hFHdef]
      funext h
      refine Finset.sum_congr rfl fun α _ => ?_
      ring
    rw [hFH, characterPairing_finset_expansion_right]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  have hfrob := characterPairing_inducedFunction_left (Subgroup.centralizer (W' : Set H))
    (fun k => 1 - (lam' (π' k) : ℂ)) FH hFHclass
  have hterm : ∀ k' : Subgroup.centralizer (W' : Set H),
      (1 - (lam' (π' k') : ℂ)) * FH ((k'⁻¹ : Subgroup.centralizer (W' : Set H)) : H) =
      (1 - (lam (π (ι k')) : ℂ)) * FH ⟨(((ι k')⁻¹ : K) : G), hKH' (ι k')⁻¹.2⟩ := by
    intro k'
    have hw : (Subgroup.subgroupOfEquivOfLe hWH) (π' k') = π (ι k') := Subtype.ext (hπ k')
    change (1 - (lam ((Subgroup.subgroupOfEquivOfLe hWH) (π' k')) : ℂ)) * _ = _
    rw [hw]
    rfl
  have htrans : characterPairing (fun k : Subgroup.centralizer (W' : Set H) =>
      1 - (lam' (π' k) : ℂ)) (fun k => FH k) =
      characterPairing (fun k : K => 1 - (lam (π k) : ℂ)) (fun k => FH ⟨k, hKH' k.2⟩) := by
    unfold characterPairing
    rw [Nat.card_congr (Equiv.ofBijective ι hιbij)]
    congr 1
    exact Fintype.sum_bijective ι hιbij _ _ hterm
  have hfinalEq : (Nat.card H : ℂ) * characterPairing (fun k : K => 1 - (lam (π k) : ℂ))
      (fun k => FH ⟨k, hKH' k.2⟩) = 3 * (5 : ℂ) ^ a := by
    rw [← htrans, ← hfrob, ← hexp]
    exact hsum
  exact hfinalEq

theorem two_generator_column_identity {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (ideal₂ ideal₅ : Ideal ComplexAlgebraicIntegers) [ideal₂.IsMaximal] [ideal₅.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2] [CharP (ComplexAlgebraicIntegers ⧸ ideal₅) 5]
    (P : Sylow 5 G) [IsCyclic (P : Subgroup G)] (a : ℕ) (ha : 1 ≤ a)
    (hWcard : Nat.card P = 5 ^ a)
    (hKH : (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 2)
    (hR : (CFSG.pPrimeCore 2 (Subgroup.centralizer (P : Set G))).map
      (Subgroup.centralizer (P : Set G)).subtype = P)
    (hA4 : Nonempty ((Subgroup.centralizer (P : Set G) ⧸
      CFSG.pPrimeCore 2 (Subgroup.centralizer (P : Set G))) ≃* alternatingGroup (Fin 4)))
    (hdih : ∃ Q : Sylow 2 (Subgroup.normalizer (P : Set G)),
      Nonempty ((Q : Subgroup (Subgroup.normalizer (P : Set G))) ≃* DihedralGroup 4))
    (t : G) (htK : t ∈ Subgroup.centralizer (P : Set G))
    (hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t) (χ₁ χ₂ χ₃ : basis.index)
    (hodd : ∀ θ : basis.index,
      (θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal ∧
        Odd (Module.finrank ℂ (basis.representation θ).vector)) ↔
      θ = principal ∨ θ = χ₁ ∨ θ = χ₂ ∨ θ = χ₃)
    (hd₁₂ : Module.finrank ℂ (basis.representation χ₁).vector ≠
      Module.finrank ℂ (basis.representation χ₂).vector)
    (hd₁₃ : Module.finrank ℂ (basis.representation χ₁).vector ≠
      Module.finrank ℂ (basis.representation χ₃).vector)
    (hd₂₃ : Module.finrank ℂ (basis.representation χ₂).vector ≠
      Module.finrank ℂ (basis.representation χ₃).vector)
    (v₁ v₂ v₃ : ℂ)
    (hv : ∀ w : (P : Subgroup G), Subgroup.zpowers (w : G) = P →
      (basis.representation χ₁).character (t * w) = v₁ ∧
      (basis.representation χ₂).character (t * w) = v₂ ∧
      (basis.representation χ₃).character (t * w) = v₃) :
    ∃ (ρ : basis.index) (δ : ℤ), (δ = 1 ∨ δ = -1) ∧
      ((ρ = χ₁ ∧ (δ : ℂ) = v₁) ∨ (ρ = χ₂ ∧ (δ : ℂ) = v₂) ∨ (ρ = χ₃ ∧ (δ : ℂ) = v₃)) ∧
      0 < (Module.finrank ℂ (basis.representation ρ).vector : ℤ) *
        ((Module.finrank ℂ (basis.representation ρ).vector : ℤ) + δ) ∧
      (Nat.card G : ℂ) * ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) -
          (basis.representation ρ).character t) ^ 2 =
        3 * (5 : ℂ) ^ a * (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 *
          ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) *
            ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) + δ)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have ht2 : orderOf t = 2 := (hinvol t).mpr (IsConj.refl t)
  have ht5 : ¬ 5 ∣ orderOf t := by rw [ht2]; norm_num
  obtain ⟨localBasisK⟩ :=
    finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer (P : Set G))
  obtain ⟨localPrincipalK, hlocalPrincipalK⟩ :=
    finiteIrreducibleCharacterBasis_contains_irreducible localBasisK
      (principalFiniteComplexRepresentation _)
      (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipalK
  obtain ⟨J, π, -, -, hJcop, hsup, hdisj, hcomm, -, hπW, -, -, -, -, -, -,
      ⟨lam₁, lam₂, h1, h2, h3, h4⟩, hcols⟩ :=
    cyclic_odd_sylow_inversion_normalizer_two_generator_supported_principal_columns 5 le_rfl a ha
      basis ideal₅ principal hprincipal P hWcard hKH localBasisK localPrincipalK hlocalPrincipalK
  obtain ⟨hlist, -, ρ, τ₁, τ₂, δ, hδ, hρB, -, -, hρ1, hτ₁1, hτ₂1, hρτ₁, -, hτ₁₂, hρreal, hτ₁real,
      hτ₂real, hT₁, -, hdτ₁, hdτ₂, hpos, hreg⟩ := hcols lam₁ lam₂ h1 h2 h3 h4
  obtain ⟨-, -, -, -, hcoeff⟩ := hlist lam₁ (by simp)
  have heqdeg : Module.finrank ℂ (basis.representation τ₁).vector =
      Module.finrank ℂ (basis.representation τ₂).vector := by
    have h : (Module.finrank ℂ (basis.representation τ₁).vector : ℤ) =
        Module.finrank ℂ (basis.representation τ₂).vector := by rw [hdτ₁, hdτ₂]
    exact_mod_cast h
  have hτeven : ¬ Odd (Module.finrank ℂ (basis.representation τ₁).vector) := by
    intro hodd₁
    have hodd₂ : Odd (Module.finrank ℂ (basis.representation τ₂).vector) := heqdeg ▸ hodd₁
    have hm₁ := (hodd τ₁).mp ⟨real_valued_odd_degree_irreducible_mem_principal_two_block basis
      ideal₂ principal hprincipal τ₁ hτ₁real hodd₁, hodd₁⟩
    have hm₂ := (hodd τ₂).mp ⟨real_valued_odd_degree_irreducible_mem_principal_two_block basis
      ideal₂ principal hprincipal τ₂ hτ₂real hodd₂, hodd₂⟩
    rcases hm₁ with h | h | h | h
    · exact hτ₁1 h
    all_goals rcases hm₂ with h' | h' | h' | h'
    all_goals first
      | exact hτ₂1 h'
      | exact hτ₁₂ (h.trans h'.symm)
      | (rw [h, h'] at heqdeg
         first
          | exact hd₁₂ heqdeg | exact hd₁₂ heqdeg.symm | exact hd₁₃ heqdeg
          | exact hd₁₃ heqdeg.symm | exact hd₂₃ heqdeg | exact hd₂₃ heqdeg.symm)
  have hρodd : Odd (Module.finrank ℂ (basis.representation ρ).vector) := by
    have hev := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hτeven)
    rw [Nat.odd_iff]
    rcases hδ with rfl | rfl <;> omega
  have hρmem : ρ = χ₁ ∨ ρ = χ₂ ∨ ρ = χ₃ := by
    rcases (hodd ρ).mp ⟨real_valued_odd_degree_irreducible_mem_principal_two_block basis ideal₂
      principal hprincipal ρ hρreal hρodd, hρodd⟩ with h | h
    · exact absurd h hρ1
    · exact h
  have hT : CyclicInversion.inversionColumn P π lam₁ = fun g =>
      1 * (basis.representation principal).character g + (δ : ℂ) *
        (basis.representation ρ).character g +
          (-(δ : ℂ)) * (basis.representation τ₁).character g := by
    funext g
    rw [hT₁ g, hprincipal]
    simp only [Pi.one_apply]
    ring
  have hcoefρ : characterPairing (CyclicInversion.inversionColumn P π lam₁)
      (basis.representation ρ).character = δ := by
    rw [hT, PureFiveAlternatingFour.characterPairing_three_left, characterPairing_basis,
      characterPairing_basis, characterPairing_basis, ite_eq_right (Ne.symm hρ1), ite_eq_left rfl,
      ite_eq_right (Ne.symm hρτ₁)]
    ring
  have hδval : ∀ c₀ : ℂ, (∀ w : (P : Subgroup G), Subgroup.zpowers (w : G) = P →
      (basis.representation ρ).character (t * w) = c₀) → (δ : ℂ) = c₀ := by
    intro c₀ hc₀
    have hgen := generator_column_coefficient (P : Subgroup G) a hWcard lam₁ h1
      (fun w => (basis.representation ρ).character ((w : G) * t)) c₀ (fun w hw => by
        have hwt : (w : G) * t = t * w := Subgroup.mem_centralizer_iff.mp htK (w : G) w.2
        show (basis.representation ρ).character ((w : G) * t) = c₀
        rw [hwt]
        exact hc₀ w hw)
    have hc := hcoeff ρ hρB t htK ht5
    rw [hcoefρ] at hc
    rw [hc]
    have hsum : ∑ w : (P : Subgroup G), (basis.representation ρ).character ((w : G) * t) *
        (1 - starRingEnd ℂ (lam₁ w : ℂ)) = -∑ w : (P : Subgroup G),
          (basis.representation ρ).character ((w : G) * t) *
            (starRingEnd ℂ (lam₁ w : ℂ) - 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring
    rw [hsum, show ((5 : ℕ) : ℂ) = 5 by norm_num, mul_neg, hgen, neg_neg]
  have hδρ : (ρ = χ₁ ∧ (δ : ℂ) = v₁) ∨ (ρ = χ₂ ∧ (δ : ℂ) = v₂) ∨ (ρ = χ₃ ∧ (δ : ℂ) = v₃) := by
    rcases hρmem with h | h | h
    · exact Or.inl ⟨h, hδval v₁ fun w hw => h ▸ (hv w hw).1⟩
    · exact Or.inr (Or.inl ⟨h, hδval v₂ fun w hw => h ▸ (hv w hw).2.1⟩)
    · exact Or.inr (Or.inr ⟨h, hδval v₃ fun w hw => h ▸ (hv w hw).2.2⟩)
  refine ⟨ρ, δ, hδ, hδρ, ?_, ?_⟩
  · have h1F : 1 ≤ (Module.finrank ℂ (basis.representation ρ).vector : ℤ) := by
      exact_mod_cast (basis_character_one basis ρ).2
    rcases hδ with rfl | rfl
    · nlinarith
    · have : (0 : ℤ) < Module.finrank ℂ (basis.representation ρ).vector + -1 := hpos
      nlinarith
  have hlam5 : lam₁ ^ 5 = 1 := by
    have h := pow_orderOf_eq_one lam₁
    rwa [h1] at h
  have : ((P : Subgroup G).subgroupOf (Subgroup.normalizer (P : Set G))).Normal :=
    Subgroup.normal_in_normalizer
  obtain ⟨localBasis⟩ :=
    finiteIrreducibleCharacterBasis_exists (G := Subgroup.normalizer (P : Set G))
  have hKH' : Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hlocal := local_A4_column_pairing (P : Subgroup G) (Subgroup.centralizer (P : Set G))
    (Subgroup.normalizer (P : Set G)) a hWcard rfl hKH' Subgroup.le_normalizer hKH hR hA4 hdih t
    htK ht2 π hπW lam₁ h1 localBasis
  have hFGclass : ∀ x c : G, (fun g => ∑ χ, (basis.representation χ).character t *
      (basis.representation χ).character t * (basis.representation χ).character g /
        (basis.representation χ).character 1) (c * x * c⁻¹) =
      (fun g => ∑ χ, (basis.representation χ).character t *
        (basis.representation χ).character t * (basis.representation χ).character g /
          (basis.representation χ).character 1) x := by
    intro x c
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [show (basis.representation χ).character (c * x * c⁻¹) =
      (basis.representation χ).character x from Representation.char_conj _ x c]
  have hglob := PureFiveAlternatingFour.characterPairing_three_left
    (basis.representation principal).character (basis.representation ρ).character
    (basis.representation τ₁).character
    (fun g => ∑ χ, (basis.representation χ).character t * (basis.representation χ).character t *
      (basis.representation χ).character g / (basis.representation χ).character 1)
    1 δ (-(δ : ℂ))
  rw [PureFiveAlternatingFour.characterPairing_involution_square_sum,
    PureFiveAlternatingFour.characterPairing_involution_square_sum,
    PureFiveAlternatingFour.characterPairing_involution_square_sum, ← hT,
    CyclicInversion.inversionColumn, characterPairing_inducedFunction_left _ _ _ hFGclass]
    at hglob
  have hloc : ∀ k : Subgroup.centralizer (P : Set G), (1 - (lam₁ (π k) : ℂ)) ≠ 0 →
      (Nat.card G : ℂ) * (fun g => ∑ χ, (basis.representation χ).character t *
        (basis.representation χ).character t * (basis.representation χ).character g /
          (basis.representation χ).character 1) ((k⁻¹ : Subgroup.centralizer (P : Set G)) : G) =
      ((Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 *
        (Nat.card (Subgroup.normalizer (P : Set G)) : ℂ)) *
        (fun h : Subgroup.normalizer (P : Set G) => ∑ α : localBasis.index,
          ((Nat.card (Subgroup.normalizer (P : Set G)) : ℂ)⁻¹ *
            ∑ u ∈ Finset.univ.filter (fun u : Subgroup.normalizer (P : Set G) => orderOf u = 2),
              (localBasis.representation α).character u) ^ 2 *
            (localBasis.representation α).character h /
              (localBasis.representation α).character 1)
          ⟨((k⁻¹ : Subgroup.centralizer (P : Set G)) : G), hKH' k⁻¹.2⟩ := by
    intro k hk
    have hlw1 : lam₁ (π k) ≠ 1 := fun h => hk (by rw [h, Units.val_one, sub_self])
    obtain ⟨w, j, hkwj⟩ := FivePowerColumn.exists_eq_mul hsup hdisj k
    have hjcop : Nat.Coprime 5 (orderOf (j : G)) := by
      rw [Subgroup.orderOf_coe]
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard j) hJcop
    have hπk := projection_apply_of_mul _ _ hWcard π hπW k w.2
      (CyclicInversion.le_centralizer_of_isCyclic _ w.2)
      (FivePowerColumn.right_le_centralizer hsup j.2) hkwj hjcop
    have hw : Subgroup.zpowers (w : G) = P := by
      rw [← hπk]
      exact FivePowerColumn.zpowers_eq_of_ne_one (P : Subgroup G) a hWcard lam₁ hlam5 (π k) hlw1
    have hcw : Commute (w : G) (j : G) := hcomm _ w.2 _ j.2
    have hE : extendedCentralizer ((k⁻¹ : Subgroup.centralizer (P : Set G)) : G) ≤
        Subgroup.normalizer (P : Set G) := by
      have hkinv : ((k⁻¹ : Subgroup.centralizer (P : Set G)) : G) = (w : G)⁻¹ * (j : G)⁻¹ := by
        rw [Subgroup.coe_inv, hkwj, mul_inv_rev]
        exact (hcw.inv_inv).eq.symm
      rw [hkinv]
      apply PureFiveAlternatingFour.extendedCentralizer_le_normalizer_of_generator
        (P : Subgroup G) hWcard (by rw [Subgroup.zpowers_inv, hw]) hcw.inv_inv
      rw [orderOf_inv]
      exact hjcop
    exact PureFiveAlternatingFour.localized_involution_square_sum basis
      (Subgroup.normalizer (P : Set G)) localBasis t hinvol
      ⟨((k⁻¹ : Subgroup.centralizer (P : Set G)) : G), hKH' k⁻¹.2⟩ hE
  have htrans := PureFiveAlternatingFour.pairing_transfer (Subgroup.centralizer (P : Set G))
    (Subgroup.normalizer (P : Set G)) hKH' (fun k => 1 - (lam₁ (π k) : ℂ))
    (fun g => ∑ χ, (basis.representation χ).character t * (basis.representation χ).character t *
      (basis.representation χ).character g / (basis.representation χ).character 1)
    (fun h : Subgroup.normalizer (P : Set G) => ∑ α : localBasis.index,
      ((Nat.card (Subgroup.normalizer (P : Set G)) : ℂ)⁻¹ *
        ∑ u ∈ Finset.univ.filter (fun u : Subgroup.normalizer (P : Set G) => orderOf u = 2),
          (localBasis.representation α).character u) ^ 2 *
        (localBasis.representation α).character h / (localBasis.representation α).character 1)
    ((Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 *
      (Nat.card (Subgroup.normalizer (P : Set G)) : ℂ)) hloc
  have hkey : (Nat.card G : ℂ) * (1 * ((basis.representation principal).character t *
      (basis.representation principal).character t /
        (basis.representation principal).character 1) +
      (δ : ℂ) * ((basis.representation ρ).character t * (basis.representation ρ).character t /
        (basis.representation ρ).character 1) +
      -(δ : ℂ) * ((basis.representation τ₁).character t * (basis.representation τ₁).character t /
        (basis.representation τ₁).character 1)) =
      (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 * (3 * (5 : ℂ) ^ a) := by
    rw [← hglob, htrans, mul_assoc, hlocal]
  have hτt : (basis.representation τ₁).character t = (basis.representation ρ).character t + δ :=
    (hreg t ht5).1
  have hτ1 : (basis.representation τ₁).character 1 =
      (Module.finrank ℂ (basis.representation ρ).vector : ℂ) + δ := by
    rw [(basis_character_one basis τ₁).1]
    exact_mod_cast hdτ₁
  rw [hprincipal, hτt, hτ1, (basis_character_one basis ρ).1] at hkey
  simp only [Pi.one_apply] at hkey
  set F : ℂ := (Module.finrank ℂ (basis.representation ρ).vector : ℂ) with hFdef
  set x : ℂ := (basis.representation ρ).character t with hxdef
  have hF0 : F ≠ 0 := by
    rw [hFdef]
    exact_mod_cast (basis_character_one basis ρ).2.ne'
  have hFδ : F + δ ≠ 0 := by
    rw [hFdef]
    have h : (0 : ℤ) < Module.finrank ℂ (basis.representation ρ).vector + δ := hpos
    exact_mod_cast h.ne'
  have hbr : 1 * (1 * 1 / 1) + (δ : ℂ) * (x * x / F) + -(δ : ℂ) * ((x + δ) * (x + δ) / (F + δ)) =
      (F - x) ^ 2 / (F * (F + δ)) := by
    rcases hδ with h | h
    · rw [h] at hFδ ⊢
      push_cast at hFδ ⊢
      field_simp
      ring
    · rw [h] at hFδ ⊢
      push_cast at hFδ ⊢
      field_simp
      ring
  rw [hbr, mul_div_assoc', div_eq_iff (mul_ne_zero hF0 hFδ)] at hkey
  linear_combination hkey

theorem case_two_false {G c d q e f δ m : ℤ} (hc : c = 2 * q * (q ^ 2 - 1))
    (hdd : d = 2 * (q + e)) (hm : 2 * m = q + e) (h5 : 5 ∣ m) (hq : 3 < q)
    (he : e = 1 ∨ e = -1) (hf : 1 < f) (hδ : δ = 1 ∨ δ = -1)
    (hcol : G * (f + δ * e * q) ^ 2 = 3 * m * c ^ 2 * (f * (f + δ)))
    (hOF : G * d ^ 2 * ((f + e * δ * q) ^ 2 * q) = c ^ 3 * (f * (f + δ) * (q - e))) : False := by
  have hc0 : c ≠ 0 := by
    rw [hc]
    have : 0 < q ^ 2 - 1 := by nlinarith
    have : 0 < 2 * q * (q ^ 2 - 1) := by positivity
    exact this.ne'
  have hX0 : f * (f + δ) ≠ 0 := by
    have : 0 < f * (f + δ) := by rcases hδ with rfl | rfl <;> nlinarith
    exact this.ne'
  have h1 : (c ^ 2 * (f * (f + δ))) * (c * (q - e)) =
      (c ^ 2 * (f * (f + δ))) * (3 * m * d ^ 2 * q) := by
    linear_combination (-1 : ℤ) * hOF + d ^ 2 * q * hcol
  have h2 := mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hc0) hX0) h1
  rw [hc, hdd] at h2
  have hq0 : 2 * q * (q + e) ≠ 0 := by
    have : 0 < 2 * q * (q + e) := by
      rcases he with rfl | rfl
      · have : 0 < q + 1 := by omega
        positivity
      · have : 0 < q + -1 := by omega
        positivity
    exact this.ne'
  have h3 : (2 * q * (q + e)) * (q - e) ^ 2 = (2 * q * (q + e)) * (3 * (q + e) ^ 2) := by
    rcases he with rfl | rfl
    · linear_combination h2 + 6 * q * (q + 1) ^ 2 * hm
    · linear_combination h2 + 6 * q * (q + -1) ^ 2 * hm
  have h4 := mul_left_cancel₀ hq0 h3
  have h5qe : (5 : ℤ) ∣ q + e := by
    rw [← hm]
    exact Dvd.dvd.mul_left h5 2
  have h5sq : (5 : ℤ) ∣ (q - e) ^ 2 := by
    rw [h4]
    exact Dvd.dvd.mul_left (dvd_pow h5qe two_ne_zero) 3
  have h5p : Prime (5 : ℤ) := Nat.prime_iff_prime_int.mp (by norm_num)
  have h5qe' := h5p.dvd_of_dvd_pow h5sq
  rcases he with rfl | rfl <;> omega

theorem case_one_false {G c d q e f δ m : ℤ} (hc : c = 2 * q * (q ^ 2 - 1))
    (hdd : d = 2 * (q + e)) (hm : 2 * m = q + e) (hm5 : 5 ≤ m) (hq : 3 < q)
    (he : e = 1 ∨ e = -1) (hf : 1 < f) (hδ : δ = 1 ∨ δ = -1)
    (hcol : G * (f - δ * e * q) ^ 2 = 3 * m * c ^ 2 * (f * (f - δ)))
    (hOF : G * d ^ 2 * ((f - e * δ * q) ^ 2 * q) = c ^ 3 * (f * (f + δ) * (q + e))) : False := by
  have hc0 : c ≠ 0 := by
    rw [hc]
    have : 0 < q ^ 2 - 1 := by nlinarith
    have : 0 < 2 * q * (q ^ 2 - 1) := by positivity
    exact this.ne'
  have hf0 : f ≠ 0 := by omega
  have h1 : (c ^ 2 * f) * (c * (f + δ) * (q + e)) =
      (c ^ 2 * f) * (3 * m * (f - δ) * d ^ 2 * q) := by
    linear_combination (-1 : ℤ) * hOF + d ^ 2 * q * hcol
  have h2 := mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hc0) hf0) h1
  rw [hc, hdd] at h2
  have hq0 : 2 * q * (q + e) ^ 2 ≠ 0 := by
    have : 0 < 2 * q * (q + e) ^ 2 := by
      rcases he with rfl | rfl
      · have : 0 < q + 1 := by omega
        positivity
      · have : 0 < q + -1 := by omega
        positivity
    exact this.ne'
  have h3 : (2 * q * (q + e) ^ 2) * ((q - e) * (f + δ)) =
      (2 * q * (q + e) ^ 2) * (3 * (q + e) * (f - δ)) := by
    rcases he with rfl | rfl
    · linear_combination h2 + 6 * q * (q + 1) ^ 2 * (f - δ) * hm
    · linear_combination h2 + 6 * q * (q + -1) ^ 2 * (f - δ) * hm
  have h4 := mul_left_cancel₀ hq0 h3
  have h6 : (q + 2 * e) * f = (2 * q + e) * δ := by linarith
  have hq9 : 9 ≤ q := by rcases he with rfl | rfl <;> omega
  rcases he with rfl | rfl <;> rcases hδ with rfl | rfl
  · have hd : q + 2 * 1 ∣ 3 := ⟨2 - f, by linarith⟩
    have := Int.le_of_dvd (by norm_num) hd
    omega
  · nlinarith
  · have hd : q + 2 * -1 ∣ 3 := ⟨f - 2, by linarith⟩
    have := Int.le_of_dvd (by norm_num) hd
    omega
  · nlinarith

section Tuple

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem pure_five_principal_tuple
    {G : Type} [Group G] [Fintype G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (a : ℕ) (ha : 1 ≤ a) (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (ideal₂ : Ideal ComplexAlgebraicIntegers) [ideal₂.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2] :
    let q : ℕ := p ^ f
    let e : ℤ := if q % 4 = 1 then 1 else -1
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    ((q : ℤ) + e) / 2 = 5 ^ a →
    ∃ (χ₁ χ₂ χ₃ : basis.index) (δ₁ δ₂ δ₃ : ℤ),
      (∀ θ : basis.index,
        (θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal ∧
          Odd (Module.finrank ℂ (basis.representation θ).vector)) ↔
        θ = principal ∨ θ = χ₁ ∨ θ = χ₂ ∨ θ = χ₃) ∧
      1 < Module.finrank ℂ (basis.representation χ₁).vector ∧
      1 < Module.finrank ℂ (basis.representation χ₂).vector ∧
      1 < Module.finrank ℂ (basis.representation χ₃).vector ∧
      Odd (Module.finrank ℂ (basis.representation χ₃).vector) ∧
      Module.finrank ℂ (basis.representation χ₁).vector ≠
        Module.finrank ℂ (basis.representation χ₂).vector ∧
      Module.finrank ℂ (basis.representation χ₁).vector ≠
        Module.finrank ℂ (basis.representation χ₃).vector ∧
      Module.finrank ℂ (basis.representation χ₂).vector ≠
        Module.finrank ℂ (basis.representation χ₃).vector ∧
      (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧ (δ₃ = 1 ∨ δ₃ = -1) ∧
      (basis.representation χ₁).character t = δ₁ * e * q ∧
      (basis.representation χ₂).character t = -(δ₂ * e * q) ∧
      (basis.representation χ₃).character t = -δ₃ ∧
      (∀ w ∈ W, Subgroup.zpowers w = W →
        (basis.representation χ₁).character (t * w) = -δ₁ ∧
        (basis.representation χ₂).character (t * w) = δ₂ ∧
        (basis.representation χ₃).character (t * w) = -δ₃) ∧
      (2 : ℤ) ^ (n - 1) ∣ (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) + δ₃ ∧
      ((Module.finrank ℂ (basis.representation χ₁).vector : ℚ) - e * δ₁ * q ≠ 0) ∧
      ((Module.finrank ℂ (basis.representation χ₂).vector : ℚ) + e * δ₂ * q ≠ 0) ∧
      (Nat.card G : ℚ) = (Nat.card (C t) : ℚ) ^ 3 / (Nat.card D : ℚ) ^ 2 *
        ((Module.finrank ℂ (basis.representation χ₁).vector : ℚ) *
            (Module.finrank ℂ (basis.representation χ₁).vector + δ₁) /
          (Module.finrank ℂ (basis.representation χ₁).vector - e * δ₁ * q) ^ 2) *
        ((q + e) / q) ∧
      (Nat.card G : ℚ) = (Nat.card (C t) : ℚ) ^ 3 / (Nat.card D : ℚ) ^ 2 *
        ((Module.finrank ℂ (basis.representation χ₂).vector : ℚ) *
            (Module.finrank ℂ (basis.representation χ₂).vector + δ₂) /
          (Module.finrank ℂ (basis.representation χ₂).vector + e * δ₂ * q) ^ 2) *
        ((q - e) / q) := by
  intro q e s₀ V D W hqa
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨-, -, hWcyc, -, hWm, ⟨hsup, -, -⟩, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have hsup : V ⊔ W = D := hsup
  have hWm : (Nat.card W : ℤ) = ((q : ℤ) + e) / 2 := hWm
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hWD : W ≤ D := hsup ▸ le_sup_right
  have he : e = 1 ∨ e = -1 := by
    change (if q % 4 = 1 then (1 : ℤ) else -1) = 1 ∨ (if q % 4 = 1 then (1 : ℤ) else -1) = -1
    split_ifs <;> simp
  have hqodd : Odd q := hpodd.pow
  have hqe : (q : ℤ) + e = 2 * 5 ^ a := by
    have heven : (2 : ℤ) ∣ (q : ℤ) + e := by
      obtain ⟨k, hk⟩ := hqodd
      have hk' : (q : ℤ) = 2 * k + 1 := by exact_mod_cast hk
      rcases he with h | h
      · exact ⟨k + 1, by rw [h, hk']; ring⟩
      · exact ⟨k, by rw [h, hk']; ring⟩
    have h := Int.ediv_mul_cancel heven
    rw [hqa] at h
    linarith
  have hWcard : Nat.card W = 5 ^ a := by
    have h : (Nat.card W : ℤ) = 5 ^ a := by rw [hWm, hqa]
    exact_mod_cast h
  have hWC : W ≤ C t := hWD.trans (fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx t htV).symm)
  have hgenord : ∀ w ∈ W, Subgroup.zpowers w = W → orderOf w = 5 ^ a := by
    intro w _ hw
    rw [← Nat.card_zpowers, hw, hWcard]
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨F, hfield, hfinite, ρ, hFcard, -, -, -, hrest⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal₂ basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  obtain ⟨hφ1, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ₂, ν₂, hfam, hdeg, -, hOFall⟩ := hrest
  have hOF := hOFall S fS hcent
  have heF : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = e := by rw [hFcard]
  have hq3 : 3 ≤ Nat.card F := by rw [hFcard]; omega
  have hqoddF : Odd (Nat.card F) := by rw [hFcard]; exact hqodd
  have he1 : Nat.card F % 4 = 1 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = 1 :=
    fun h => by simp [h]
  have he3 : Nat.card F % 4 = 3 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 :=
    fun h => by simp [show ¬ Nat.card F % 4 = 1 by omega]
  obtain ⟨F', hF', hF'fin, A', ρ', hdata⟩ := actual_simple_layer_matrix_data n hn S fS hG t ht2
    hnonab hcentral hnc p f hp hpodd hf hmodel
  have hqM : 2 ^ padicValNat 2 (Nat.card F ^ 2 - 1) = modulus n := by
    have h := hdata.two_part
    rw [hdata.field_card, Nat.factorization_def _ Nat.prime_two] at h
    rw [hFcard, h]
    rfl
  obtain ⟨hf₁, hf₂, hf₃, -, -, ho₃, hsigns, hsum2, hprod, -, -⟩ :=
    perfect_family_degree_data hn fS hcent ht2 hnonab basis ideal₂ principal hprincipal
      localBasis localPrincipal (Nat.card F) hq3 hqoddF hqM _ he1 he3 _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄
      ψ₂ ν₂ hfam hdeg
  obtain ⟨hrot, -, -, -⟩ := actual_principal_rotation_values_and_congruences hG hn ht2 hnonab
    basis ideal₂ principal hprincipal localBasis localPrincipal (Nat.card F) hq3 hqoddF _ he1 he3
    _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ₂ ν₂ hfam hdeg fS hcent
  obtain ⟨hlφ, hδ₁, hδ₂, hδ₃, -, -, -, -, -, -, -, hB, -, hodd2, hsec, -⟩ := hfam
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index),
      c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hodd₂ : ∀ θ : basis.index,
      (θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal ∧
        Odd (Module.finrank ℂ (basis.representation θ).vector)) ↔
      θ = principal ∨ θ = χ₁ ∨ θ = χ₂ ∨ θ = χ₃ := by
    intro θ
    constructor
    · rintro ⟨hθB, hθo⟩
      exact (hodd2 θ hθB).mp hθo
    · intro h
      have hθB : θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal := by
        rcases h with rfl | rfl | rfl | rfl <;> exact hmem _ (by simp)
      exact ⟨hθB, (hodd2 θ hθB).mpr h⟩
  have hrot₃ : ∀ v : ℤ, ¬ v ≡ 0 [ZMOD ((2 ^ (n - 1) : ℕ) : ℤ)] →
      ¬ v ≡ (((2 ^ (n - 1)) / 2 : ℕ) : ℤ) [ZMOD ((2 ^ (n - 1) : ℕ) : ℤ)] →
      (basis.representation χ₃).character ((fS (r n) : G) ^ v) = -δ₃ * (-1 : ℂ) ^ v :=
    fun v hv0 hv1 => (hrot v hv0 hv1).2.2
  have hM4 : 4 ∣ 2 ^ (n - 1) := by
    rw [show n - 1 = 2 + (n - 3) by omega, pow_add]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hr : (fS (r n) : G) ^ (2 ^ (n - 1)) = 1 := by
    have h := pow_orderOf_eq_one (fS (r n) : G)
    rwa [suppliedRotation_orderOf (by omega) fS] at h
  have hM2 : 2 ^ (n - 1) / 2 = 2 ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ, Nat.mul_div_cancel _ two_pos]
  obtain ⟨h₁t, h₂t, h₃t, -⟩ := hsec 1 (by rw [orderOf_one]; decide)
  simp only [OneMemClass.coe_one, mul_one, hφ1, hFcard] at h₁t h₂t h₃t
  have hM := PrimeTorusExclusion.dvd_add_of_rotation_values (basis.representation χ₃)
    (r := (fS (r n) : G)) (M := 2 ^ (n - 1)) (by positivity) hM4 hr δ₃
    (by rw [hM2, ← ht, h₃t]) hrot₃
  push_cast at hM
  have hdist := signed_degree_product_two_part_congruence_distinct (Nat.card F) _ _ _ δ₁ δ₂ δ₃
    (by omega) hqoddF hf₁ hf₂ hf₃ hsigns hsum2 hprod (by
      rw [hqM]
      change ((2 ^ (n - 1) : ℕ) : ℤ) ∣ _
      push_cast
      exact hM)
  obtain ⟨hd₁₂, hd₁₃, hd₂₃⟩ := hdist
  obtain ⟨lφ, hlφB, -, hφchar, hφdeg, hφker⟩ := hlφ
  rw [hFcard] at hφdeg
  have hφgen : ∀ (w : G) (hwW : w ∈ W), Subgroup.zpowers w = W →
      (localBasis.representation lφ).character ⟨w, hWC hwW⟩ = -e := by
    intro w hwW hw
    have hy : orderOf (⟨w, hWC hwW⟩ : C t) = 5 ^ a := by
      rw [Subgroup.orderOf_mk]
      exact hgenord w hwW hw
    have hyY : (⟨w, hWC hwW⟩ : C t) ∈
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t) :=
      mem_of_index_eq_two_of_odd_orderOf hY (by rw [hy]; exact Odd.pow (by decide))
    exact local_degree_q_value_of_five_power n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd
      hf hmodel hN ha he hqe ideal₂ localBasis localPrincipal hlocalPrincipal lφ hlφB hφdeg hφker
      ⟨w, hWC hwW⟩ hy hyY
  rw [← hφchar] at hsec
  have he2 : (e : ℂ) * e = 1 := by rcases he with h | h <;> rw [h] <;> norm_num
  have hvalw : ∀ w ∈ W, Subgroup.zpowers w = W →
      (basis.representation χ₁).character (t * w) = -δ₁ ∧
      (basis.representation χ₂).character (t * w) = δ₂ ∧
      (basis.representation χ₃).character (t * w) = -δ₃ := by
    intro w hwW hw
    have hodd : Odd (orderOf (⟨w, hWC hwW⟩ : C t)) := by
      rw [Subgroup.orderOf_mk, hgenord w hwW hw]
      exact Odd.pow (by decide)
    obtain ⟨h₁w, h₂w, h₃w, -⟩ := hsec ⟨w, hWC hwW⟩ hodd
    rw [hφgen w hwW hw, heF] at h₁w h₂w
    refine ⟨?_, ?_, h₃w⟩
    · change (basis.representation χ₁).character (t * w) = _ at h₁w
      rw [h₁w]
      linear_combination (-(δ₁ : ℂ)) * he2
    · change (basis.representation χ₂).character (t * w) = _ at h₂w
      rw [h₂w]
      linear_combination (δ₂ : ℂ) * he2
  obtain ⟨hne₁, hne₂, hG₁, hG₂⟩ := hOF
  rw [heF, hFcard] at hne₁ hne₂ hG₁ hG₂
  have hdD : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = Nat.card D := by
    change _ = Nat.card (Subgroup.centralizer
      ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) : Set G))
    rw [centralizer_zpowers_sup_zpowers]
  rw [hdD] at hG₁ hG₂
  have hf₁' : 1 < Module.finrank ℂ (basis.representation χ₁).vector := by exact_mod_cast hf₁
  have hf₂' : 1 < Module.finrank ℂ (basis.representation χ₂).vector := by exact_mod_cast hf₂
  have hf₃' : 1 < Module.finrank ℂ (basis.representation χ₃).vector := by exact_mod_cast hf₃
  have ho₃' : Odd (Module.finrank ℂ (basis.representation χ₃).vector) := by
    obtain ⟨k, hk⟩ := ho₃
    exact ⟨k.toNat, by omega⟩
  refine ⟨χ₁, χ₂, χ₃, δ₁, δ₂, δ₃, hodd₂, hf₁', hf₂', hf₃', ho₃',
    fun h => hd₁₂ (by exact_mod_cast h), fun h => hd₁₃ (by exact_mod_cast h),
    fun h => hd₂₃ (by exact_mod_cast h), hδ₁, hδ₂, hδ₃,
    by rw [h₁t], by rw [h₂t], by rw [h₃t], hvalw, hM, hne₁, hne₂, hG₁, hG₂⟩

end Tuple

end PureFiveNontrivialCore

end CFSG.Semidihedral.Principal
