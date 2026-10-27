module

public import CFSG.CharacterTheory.BrauerLinearThree.LayerSetting

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include φ hZ hZodd h2 hJ in
theorem exists_sylow_eq_of_sylow_centralizer [Finite G] (P : Subgroup G)
    (SC : Sylow 2 (Subgroup.centralizer ({J} : Set G)))
    (hSC : (SC : Subgroup (Subgroup.centralizer ({J} : Set G))).map
      (Subgroup.centralizer ({J} : Set G)).subtype = P) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  have hle : P ≤ Subgroup.centralizer {J} := by
    rw [← hSC]
    exact Subgroup.map_subtype_le _
  have hPp : IsPGroup 2 P := by
    rw [← hSC]
    exact SC.isPGroup'.map _
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  have hJP : J ∈ P := by
    obtain ⟨hJS, -⟩ := sylow_center_involution φ hZ hZodd h2 hJ SC
    rw [← hSC]
    exact ⟨_, hJS, rfl⟩
  have hbound : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {J} →
      Nat.card Q ≤ Nat.card P := by
    intro Q hQ hQC
    have hQ' : IsPGroup 2 (Q.subgroupOf (Subgroup.centralizer ({J} : Set G))) :=
      hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
    obtain ⟨T, hT⟩ := hQ'.exists_le_sylow
    have h1 : Nat.card Q = Nat.card (Q.subgroupOf (Subgroup.centralizer ({J} : Set G))) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv).symm
    have h3 : Nat.card P = Nat.card SC := by
      rw [← hSC, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    rw [h1, h3, Sylow.card_eq_multiplicity SC, ← Sylow.card_eq_multiplicity T]
    exact Subgroup.card_le_of_le hT
  refine ⟨S, ?_⟩
  by_contra hne'
  have hne : P ≠ (S : Subgroup G) := fun h => hne' h.symm
  have hlt : P < (S : Subgroup G) := lt_of_le_of_ne hPS hne
  have hSnil : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  have hK : P.subgroupOf (S : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm hPS
    intro x hx
    have : (⟨x, hx⟩ : (S : Subgroup G)) ∈ P.subgroupOf (S : Subgroup G) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact this
  have hN := Group.normalizerCondition_of_isNilpotent (G := (S : Subgroup G))
    (P.subgroupOf (S : Subgroup G)) hK
  obtain ⟨y, hyN, hyK⟩ := IsConcreteLE.exists_of_lt hN
  set x : G := (y : G) with hx_def
  have hxP : ∀ k ∈ P, x * k * x⁻¹ ∈ P := by
    intro k hk
    have hk' : (⟨k, hPS hk⟩ : (S : Subgroup G)) ∈ P.subgroupOf (S : Subgroup G) := hk
    exact (Subgroup.mem_normalizer_iff.mp hyN _).mp hk'
  have hxP' : ∀ k ∈ P, x⁻¹ * k * x ∈ P := by
    intro k hk
    have hk' : (⟨k, hPS hk⟩ : (S : Subgroup G)) ∈ P.subgroupOf (S : Subgroup G) := hk
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) _).mp hk'
    rw [Subgroup.mem_subgroupOf] at this
    simpa [hx_def] using this
  have hxnotP : x ∉ P := hyK
  have hxJ : x * J * x⁻¹ = J := by
    have hmem : x * J * x⁻¹ ∈ P := hxP J hJP
    have hmemC : x * J * x⁻¹ ∈ Subgroup.centralizer ({J} : Set G) := hle hmem
    have hmemSC : (⟨x * J * x⁻¹, hmemC⟩ : Subgroup.centralizer ({J} : Set G)) ∈ SC := by
      have : x * J * x⁻¹ ∈ (SC : Subgroup (Subgroup.centralizer ({J} : Set G))).map
          (Subgroup.centralizer ({J} : Set G)).subtype := by rw [hSC]; exact hmem
      obtain ⟨w, hw, hwx⟩ := this
      have : w = ⟨x * J * x⁻¹, hmemC⟩ := Subtype.ext hwx
      rw [← this]
      exact hw
    obtain ⟨-, huniq⟩ := sylow_center_involution φ hZ hZodd h2 hJ SC
    have hcen : (⟨⟨x * J * x⁻¹, hmemC⟩, hmemSC⟩ : SC) ∈ Subgroup.center SC := by
      refine Subgroup.mem_center_iff.mpr ?_
      intro z
      apply Subtype.ext
      apply Subtype.ext
      have hz : (((z : Subgroup.centralizer ({J} : Set G)) : G)) ∈ P := by
        rw [← hSC]
        exact ⟨z, z.2, rfl⟩
      have hz' := hxP' _ hz
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hle hz')
      change ((z : Subgroup.centralizer ({J} : Set G)) : G) * (x * J * x⁻¹) =
        (x * J * x⁻¹) * ((z : Subgroup.centralizer ({J} : Set G)) : G)
      calc ((z : Subgroup.centralizer ({J} : Set G)) : G) * (x * J * x⁻¹) =
            x * ((x⁻¹ * (z : Subgroup.centralizer ({J} : Set G)) * x) * J) * x⁻¹ := by group
        _ = x * (J * (x⁻¹ * (z : Subgroup.centralizer ({J} : Set G)) * x)) * x⁻¹ := by
            rw [hc]
        _ = (x * J * x⁻¹) * ((z : Subgroup.centralizer ({J} : Set G)) : G) := by group
    have hsq : (⟨⟨x * J * x⁻¹, hmemC⟩, hmemSC⟩ : SC) * ⟨⟨x * J * x⁻¹, hmemC⟩, hmemSC⟩ = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      change x * J * x⁻¹ * (x * J * x⁻¹) = 1
      calc x * J * x⁻¹ * (x * J * x⁻¹) = x * (J * J) * x⁻¹ := by group
        _ = 1 := by rw [J_mul_self hJ]; group
    rcases huniq _ hcen hsq with h1 | h1
    · exfalso
      have : x * J * x⁻¹ = 1 :=
        congrArg (fun w : SC => ((w : Subgroup.centralizer ({J} : Set G)) : G)) h1
      have hJ1 : J = 1 := by
        calc J = x⁻¹ * (x * J * x⁻¹) * x := by group
          _ = 1 := by rw [this]; group
      rw [hJ1, orderOf_one] at hJ
      exact absurd hJ (by norm_num)
    · exact h1
  have hxC : x ∈ Subgroup.centralizer ({J} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * J = x * J * x⁻¹ * x := by group
      _ = J * x := by rw [hxJ]
  have hQS : P ⊔ Subgroup.zpowers x ≤ (S : Subgroup G) :=
    sup_le hPS (Subgroup.zpowers_le.mpr y.2)
  have hQp : IsPGroup 2 (P ⊔ Subgroup.zpowers x : Subgroup G) := S.isPGroup'.to_le hQS
  have hQC : P ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer {J} :=
    sup_le hle (Subgroup.zpowers_le.mpr hxC)
  have hPQ : P < P ⊔ Subgroup.zpowers x := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hxnotP
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have := hbound _ hQp hQC
  have hlt' := Subgroup.card_lt_of_lt hPQ
  omega

include φ hZ hZodd h2 hJ in
theorem exists_semidihedral_sylow_of_G [Finite G] (hq : Nat.card F % 4 = 3) :
    4 ≤ (Nat.card F + 1).factorization 2 + 2 ∧
      ∃ (S : Sylow 2 G) (e' : CFSG.Open.SemidihedralGroup
          ((Nat.card F + 1).factorization 2 + 2) ≃* (S : Subgroup G)),
        (e' (CFSG.Semidihedral.r _) : G) ^
            (CFSG.Semidihedral.modulus ((Nat.card F + 1).factorization 2 + 2) / 2) = J ∧
          (e' (CFSG.Semidihedral.s _) : G) = invJ₁ φ := by
  set m := (Nat.card F + 1).factorization 2 with hm
  obtain ⟨hm2, h, -, -, hhpow, -, -, -, ⟨SC, hSC⟩, e, he_r, he_s, -, -⟩ :=
    exists_semidihedral_sylow φ hZ hZodd h2 hJ hq hm.symm
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_sylow_centralizer φ hZ hZodd h2 hJ _ SC hSC
  refine ⟨by omega, S, e.trans (MulEquiv.subgroupCongr hS.symm), ?_, ?_⟩
  · have hmod : CFSG.Semidihedral.modulus (m + 2) / 2 = 2 ^ m := by
      rw [CFSG.Semidihedral.modulus, show m + 2 - 1 = m + 1 by omega, pow_succ,
        Nat.mul_div_cancel _ (by norm_num)]
    rw [hmod]
    change ((e (CFSG.Semidihedral.r (m + 2)) : G)) ^ 2 ^ m = J
    rw [he_r, hhpow]
  · change ((e (CFSG.Semidihedral.s (m + 2)) : G)) = invJ₁ φ
    exact he_s

omit [Finite F] in
include hZ hZodd h2 in
theorem centralizer_inf_invJ₁_eq_torus :
    (Subgroup.centralizer ({J} : Set G) ⊓ Subgroup.centralizer ({invJ₁ φ} : Set G) :
        Subgroup G) = (torusC φ).map (Subgroup.centralizer ({J} : Set G)).subtype := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨hxJ, hxJ₁⟩
    obtain ⟨a, b, rfl⟩ := (isTorus_iff φ hZ hZodd h2 x).mp ⟨hxJ.symm, hxJ₁.symm⟩
    refine ⟨centralizerHom φ (diagGL a b), ⟨(a, b), rfl⟩, ?_⟩
    rw [coe_centralizerHom]
  · rintro ⟨y, ⟨⟨a, b⟩, rfl⟩, rfl⟩
    have ht := isTorus_diag φ a b
    change ((centralizerHom φ (diagHom (a, b)) : Subgroup.centralizer ({J} : Set G)) : G) * J =
        J * _ ∧ _ * invJ₁ φ = invJ₁ φ * _
    rw [coe_centralizerHom, diagHom_apply]
    exact ⟨ht.1.symm, ht.2.symm⟩

omit [Finite F] in
include hZ hZodd h2 in
theorem card_centralizer_inf_invJ₁ :
    Nat.card (Subgroup.centralizer ({J} : Set G) ⊓ Subgroup.centralizer ({invJ₁ φ} : Set G) :
        Subgroup G) * Nat.card Z = (Nat.card F - 1) ^ 2 := by
  rw [centralizer_inf_invJ₁_eq_torus φ hZ hZodd h2,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact card_torusC φ hZ

theorem card_formula_arith {g c d l q : ℕ} (hq5 : 5 ≤ q) (hl : 0 < l)
    (hc : c * l = q * (q - 1) ^ 2 * (q + 1)) (hdl : d * l = (q - 1) ^ 2)
    (hg : (g : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 * (((q : ℚ) ^ 2 + q + 1) / ((q : ℚ) + 1) ^ 2)) :
    g * l = q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) := by
  have hq1 : 1 ≤ q := by omega
  have hcQ : (c : ℚ) * l = q * (q - 1) ^ 2 * (q + 1) := by
    have := congrArg (fun n : ℕ => (n : ℚ)) hc
    push_cast [Nat.cast_sub hq1] at this
    exact this
  have hdQ : (d : ℚ) * l = (q - 1) ^ 2 := by
    have := congrArg (fun n : ℕ => (n : ℚ)) hdl
    push_cast [Nat.cast_sub hq1] at this
    exact this
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  have hq1' : (q : ℚ) - 1 ≠ 0 := by
    have : (5 : ℚ) ≤ q := by exact_mod_cast hq5
    linarith
  have hd0 : (d : ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdQ
    exact pow_ne_zero 2 hq1' hdQ.symm
  have hqp : (q : ℚ) + 1 ≠ 0 := by positivity
  have hg' : (g : ℚ) * d ^ 2 * (q + 1) ^ 2 = c ^ 3 * (q ^ 2 + q + 1) := by
    rw [hg]
    field_simp
  have hkey : (g : ℚ) * l * ((q - 1) ^ 4 * (q + 1) ^ 2) =
      q ^ 3 * (q - 1) ^ 2 * (q + 1) * (q ^ 2 + q + 1) * ((q - 1) ^ 4 * (q + 1) ^ 2) := by
    have h1 : (g : ℚ) * (d * l) ^ 2 * (q + 1) ^ 2 * l = (c * l) ^ 3 * (q ^ 2 + q + 1) := by
      linear_combination (l : ℚ) ^ 3 * hg'
    rw [hcQ, hdQ] at h1
    linear_combination h1
  have hne : ((q : ℚ) - 1) ^ 4 * (q + 1) ^ 2 ≠ 0 := by positivity
  have hfinal := mul_right_cancel₀ hne hkey
  have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have : ((g * l : ℕ) : ℚ) = ((q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub hq3, Nat.cast_sub hq2]
    rw [hfinal]
    ring
  exact_mod_cast this

include φ hZ hZodd h2 in
theorem padicValNat_centralizers (p f : ℕ) (hp : p.Prime) (hF : Nat.card F = p ^ f) :
    padicValNat p (Nat.card (Subgroup.centralizer ({J} : Set G))) = f ∧
      padicValNat p (Nat.card (Subgroup.centralizer ({J} : Set G) ⊓
        Subgroup.centralizer ({invJ₁ φ} : Set G) : Subgroup G)) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  have hc := card_centralizer_J φ
  have hd := card_centralizer_inf_invJ₁ φ hZ hZodd h2
  have hpc : ringChar F = p := by
    have hrc : (ringChar F).Prime := CharP.char_is_prime F _
    obtain ⟨f', hf', hq'⟩ := exists_card_eq_ringChar_pow F
    have hdvd : ringChar F ∣ p ^ f := by
      rw [← hF, hq']
      exact dvd_pow_self _ hf'.ne'
    exact (Nat.prime_dvd_prime_iff_eq hrc hp).mp (hrc.dvd_of_dvd_pow hdvd)
  have hcop := coprime_facts hZ
  rw [hpc] at hcop
  have hl0 : padicValNat p (Nat.card Z) = 0 :=
    padicValNat.eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop.1)
  have hq5 : 3 ≤ Nat.card F := by
    have := odd_card_F h2
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨k, hk⟩ := this
    omega
  have hq1 : 1 ≤ Nat.card F - 1 := by omega
  refine ⟨?_, ?_⟩
  · have hR : padicValNat p ((Nat.card F - 1) ^ 2 * (Nat.card F + 1)) = 0 :=
      padicValNat.eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop.2.1)
    have hqv : padicValNat p (Nat.card F) = f := by rw [hF, padicValNat.prime_pow]
    have e1 : padicValNat p (Nat.card (Subgroup.centralizer ({J} : Set G)) * Nat.card Z) =
        padicValNat p (Nat.card (Subgroup.centralizer ({J} : Set G))) := by
      rw [padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hl0, add_zero]
    have e2 : padicValNat p (Nat.card F * (Nat.card F - 1) ^ 2 * (Nat.card F + 1)) = f := by
      rw [mul_assoc, padicValNat.mul (by positivity) (by positivity), hqv, hR, add_zero]
    rw [← e1, hc, e2]
  · apply padicValNat.eq_zero_of_not_dvd
    intro hdvd
    have h1 : p ∣ (Nat.card F - 1) ^ 2 := by
      rw [← hd]
      exact hdvd.mul_right _
    have h3 := hp.dvd_of_dvd_pow h1
    have h4 := coprime_ringChar_card_sub_one F
    rw [hpc] at h4
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp h4 h3

include φ hZ hZodd h2 hJ in
theorem order_formula_of_cube_dvd
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq5 : 5 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hcube : Nat.card F ^ 3 ∣ Nat.card G) :
    (Nat.card G : ℚ) = (Nat.card (Subgroup.centralizer ({J} : Set G)) : ℚ) ^ 3 /
      (Nat.card (Subgroup.centralizer ({J} : Set G) ⊓
        Subgroup.centralizer ({invJ₁ φ} : Set G) : Subgroup G) : ℚ) ^ 2 *
      (((Nat.card F : ℚ) ^ 2 + Nat.card F + 1) / ((Nat.card F : ℚ) + 1) ^ 2) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · exfalso
      have hqodd := odd_card_F h2
      rw [hF, h] at hqodd
      exact (Nat.not_even_iff_odd.mpr hqodd) ((Nat.even_pow' (by omega)).mpr even_two)
    · exact h
  obtain ⟨hs, hnab, hcen, hnc, hmodel⟩ := layer_hypotheses φ hZ hZodd h2 hJ hq p f hp hf hF hq5
  have := hs
  obtain ⟨hn4, S, e', he'r, he's⟩ := exists_semidihedral_sylow_of_G φ hZ hZodd h2 hJ hq
  obtain ⟨basis⟩ := CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ :=
    CFSG.Semidihedral.Principal.finiteIrreducibleCharacterBasis_exists_principal_label basis
  obtain ⟨localBasis⟩ := CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer ({J} : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
    CFSG.Semidihedral.Principal.finiteIrreducibleCharacterBasis_exists_principal_label localBasis
  obtain ⟨⟨ideal, hmax, h2mem⟩, hchar⟩ :=
    CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (CFSG.TwoRankLowerBound.Helpers.ComplexAlgebraicIntegers ⧸ ideal) 2 :=
    hchar ideal hmax h2mem
  obtain ⟨hvc, hvd⟩ := padicValNat_centralizers φ hZ hZodd h2 p f hp hF
  have hvG : 3 * f ≤ padicValNat p (Nat.card G) := by
    rw [hF, ← pow_mul] at hcube
    exact (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (by rw [mul_comm]; exact hcube)
  have hval : 3 * (padicValNat p (Nat.card (Subgroup.centralizer ({J} : Set G))) : ℤ) -
      2 * (padicValNat p (Nat.card (Subgroup.centralizer ({J} : Set G) ⊓
        Subgroup.centralizer ({(e' (CFSG.Semidihedral.s _) : G)} : Set G) : Subgroup G)) : ℤ) ≤
      padicValNat p (Nat.card G) := by
    rw [he's, hvc, hvd]
    omega
  obtain ⟨F', _, _, ρ, hF', -, -, -, hrest⟩ :=
    CFSG.Semidihedral.Principal.actual_simple_layer_characteristic_valuation_degree_formulas
      hnonab _ hn4 S e' J hJ hnab hcen hnc p f hp hpodd hf hmodel ideal basis principal
      hprincipal localBasis localPrincipal hlocalPrincipal e' he'r hval
  obtain ⟨-, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, -, -, hvals⟩ := hrest
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGq, -⟩ := hvals
  rw [he's] at hGq
  have he : (if Nat.card F' % 4 = 1 then (1 : ℤ) else -1) = -1 := by
    rw [hF', ← hF]
    exact ite_eq_right_iff.mpr (fun h => by omega)
  rw [he, hF', ← hF] at hGq
  rw [hGq]
  push_cast
  ring

include φ hZ hZodd h2 hJ in
theorem card_mul_eq_of_cube_dvd
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hq : Nat.card F % 4 = 3) (hq5 : 5 ≤ Nat.card F) (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hcube : Nat.card F ^ 3 ∣ Nat.card G) :
    Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) :=
  card_formula_arith hq5 Nat.card_pos (card_centralizer_J φ)
    (card_centralizer_inf_invJ₁ φ hZ hZodd h2)
    (order_formula_of_cube_dvd φ hZ hZodd h2 hJ hnonab hq hq5 p f hp hf hF hcube)

end CFSG.BrauerLinearThree
