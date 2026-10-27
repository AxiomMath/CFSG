module

public import CFSG.CharacterTheory.BrauerLinearThree.FourGLocal
public import CFSG.CharacterTheory.BrauerLinearThree.FourGIndex
public import CFSG.CharacterTheory.BrauerLinearThree.FourGBounds
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerRotationCongruences

public section

open scoped Classical

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include hZ hZodd h2 hJ in
theorem exists_order_parameter
    [Finite G] (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F) (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) :
    ∃ μ : ℚ, (Nat.card G : ℚ) = (Nat.card (Subgroup.centralizer ({J} : Set G)) : ℚ) ^ 3 /
        (Nat.card (Subgroup.centralizer ({J} : Set G) ⊓
          Subgroup.centralizer ({invJ₁ φ} : Set G) : Subgroup G) : ℚ) ^ 2 * μ ∧
      5 * (5 * (Nat.card F : ℚ) + 1) * (Nat.card F - 1) / (36 * (Nat.card F : ℚ) ^ 2) < μ ∧
      μ < 5 * (5 * (Nat.card F : ℚ) + 1) * (Nat.card F + 1) / (16 * (Nat.card F : ℚ) ^ 2) := by
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
  obtain ⟨hs, hnab, hcen, hnc, hmodel⟩ :=
    layer_hypotheses φ hZ hZodd h2 hJ hq p f hp hf hF (by omega)
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
  obtain ⟨F', _, _, ρ, hF', -, -, -, hrest⟩ :=
    CFSG.Semidihedral.Principal.actual_nonsimple_layer_odd_character_rotation_congruences _ hn4 S
      e' hG J hJ hnab hcen hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal
  obtain ⟨hφ1, hφnc, ⟨δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg⟩, hall⟩ := hrest
  obtain ⟨-, -, -, -, hc3⟩ := hall _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν ⟨hfam, hdeg⟩
  obtain ⟨hd1, hd2, hG1, hG2⟩ :=
    CFSG.Semidihedral.Principal.actual_principal_order_formulas_of_family _ hn4 S e' hG J hJ
      hnab hcen hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal (Nat.card F') hF' _ rfl _ hφ1 hφnc δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄
      ψ ν hfam hdeg e' he'r
  obtain ⟨h1, h2', h3, -, hδ, -, -, hprod, hrel⟩ := hdeg
  have hq' : Nat.card F' = Nat.card F := hF'.trans hF.symm
  have he : (if Nat.card F' % 4 = 1 then (1 : ℤ) else -1) = -1 := by
    rw [hq']
    exact ite_eq_right_iff.mpr (fun h => by omega)
  rw [he, he's, hq'] at hG1 hG2
  rw [he, hq'] at hd1 hd2
  rw [hq'] at hprod hrel
  set c : ℚ := (Nat.card (Subgroup.centralizer ({J} : Set G)) : ℚ)
  set d : ℚ := (Nat.card (Subgroup.centralizer ({J} : Set G) ⊓
    Subgroup.centralizer ({invJ₁ φ} : Set G) : Subgroup G) : ℚ)
  set f₁ := Module.finrank ℂ (basis.representation χ₁).vector
  set f₂ := Module.finrank ℂ (basis.representation χ₂).vector
  set f₃ := Module.finrank ℂ (basis.representation χ₃).vector
  set q : ℚ := (Nat.card F : ℚ) with hqdef
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hd0 : d ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hK : c ^ 3 / d ^ 2 ≠ 0 := by positivity
  set μ : ℚ := (q - 1) / q * (f₁ * (f₁ + δ₁) / (f₁ + δ₁ * q) ^ 2) with hμ
  have hμ₁ : (Nat.card G : ℚ) = c ^ 3 / d ^ 2 * μ := by
    rw [hG1, hμ]
    push_cast
    ring_nf
  have hμ₂ : μ = (q + 1) / q * (f₂ * (f₂ + δ₂) / (f₂ - δ₂ * q) ^ 2) := by
    apply mul_left_cancel₀ hK
    rw [← hμ₁, hG2]
    push_cast
    ring_nf
  refine ⟨μ, hμ₁, ?_⟩
  exact order_parameter_bounds hp hF hq7 hq h1 h2' h3 hδ hprod hrel hc3 hμ hμ₂

omit [Finite F] in
@[expose] def centralizerEquivOfLe {G₀ : Subgroup G}
    (hC : Subgroup.centralizer ({J} : Set G) ≤ G₀) :
    Subgroup.centralizer ({(⟨J, hC (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩ : G₀)} :
      Set G₀) ≃* Subgroup.centralizer ({J} : Set G) where
  toFun x := ⟨((x : G₀) : G), by
    have h := Subgroup.mem_centralizer_singleton_iff.mp x.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h)⟩
  invFun y := ⟨⟨y, hC y.2⟩, by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

include hZ hZodd h2 hJ in
theorem false_of_conj_in_centralizer
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) {z : G}
    (hzC : z ∈ centerSub φ) (hz1 : z ≠ 1)
    (hcase : ∃ g ∈ Subgroup.centralizer ({z} : Set G), g * J * g⁻¹ = invJ₁ φ) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  set G₀ := Subgroup.centralizer ({z} : Set G) with hG₀
  have hCG₀ := centralizer_J_le_centralizer_of_mem_centerSub φ hzC
  set J₀ : G₀ := ⟨J, hCG₀ (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩
  set φ₀ := (centralizerEquivOfLe hCG₀).trans φ
  have hJ₀ : orderOf J₀ = 2 := by rw [Subgroup.orderOf_mk]; exact hJ
  have hlin : ∀ A : GL (Fin 2) F,
      ((linearCentralizerHom φ₀ A : G₀) : G) = linearCentralizerHom φ A := fun A => rfl
  have hconj₀ : ∃ g : G₀, g * J₀ * g⁻¹ = invJ₁ φ₀ := by
    obtain ⟨g, hg, hgJ⟩ := hcase
    exact ⟨⟨g, hg⟩, Subtype.ext hgJ⟩
  have hidx₀ := index_ne_two_of_conj φ₀ hZ hZodd h2 hJ₀ hq hconj₀
  have hidx := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hnonab
  obtain ⟨μ, hGμ, hμL, hμU⟩ := exists_order_parameter φ hZ hZodd h2 hJ hidx hq hq7 p f hp hf hF
  obtain ⟨μ₀, hG₀μ, hμ₀L, hμ₀U⟩ :=
    exists_order_parameter φ₀ hZ hZodd h2 hJ₀ hidx₀ hq hq7 p f hp hf hF
  have hc : Nat.card (Subgroup.centralizer ({J₀} : Set G₀)) =
      Nat.card (Subgroup.centralizer ({J} : Set G)) :=
    Nat.card_congr (centralizerEquivOfLe hCG₀).toEquiv
  have hd : Nat.card (Subgroup.centralizer ({J₀} : Set G₀) ⊓
      Subgroup.centralizer ({invJ₁ φ₀} : Set G₀) : Subgroup G₀) =
      Nat.card (Subgroup.centralizer ({J} : Set G) ⊓
        Subgroup.centralizer ({invJ₁ φ} : Set G) : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective G₀.subtype_injective]
    congr 2
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, ⟨hyJ, hy₁⟩, rfl⟩
      exact ⟨congrArg Subtype.val hyJ, congrArg Subtype.val hy₁⟩
    · rintro ⟨hxJ, hx₁⟩
      have hxG₀ : x ∈ G₀ := hCG₀ (Subgroup.mem_centralizer_singleton_iff.mpr hxJ)
      exact ⟨⟨x, hxG₀⟩, ⟨Subtype.ext hxJ, Subtype.ext hx₁⟩, rfl⟩
  rw [hc, hd] at hG₀μ
  have hq7' : (7 : ℚ) ≤ (Nat.card F : ℚ) := by exact_mod_cast hq7
  set q : ℚ := (Nat.card F : ℚ)
  set K : ℚ := (Nat.card (Subgroup.centralizer ({J} : Set G)) : ℚ) ^ 3 /
    (Nat.card (Subgroup.centralizer ({J} : Set G) ⊓
      Subgroup.centralizer ({invJ₁ φ} : Set G) : Subgroup G) : ℚ) ^ 2
  have hK : 0 < K := by
    have h1 : (0 : ℚ) < (Nat.card (Subgroup.centralizer ({J} : Set G)) : ℚ) :=
      Nat.cast_pos.mpr Nat.card_pos
    have h2' : (0 : ℚ) < (Nat.card (Subgroup.centralizer ({J} : Set G) ⊓
        Subgroup.centralizer ({invJ₁ φ} : Set G) : Subgroup G) : ℚ) :=
      Nat.cast_pos.mpr Nat.card_pos
    positivity
  have hUL : 5 * (5 * q + 1) * (q + 1) / (16 * q ^ 2) ≤
      3 * (5 * (5 * q + 1) * (q - 1) / (36 * q ^ 2)) := by
    have hq0 : 0 < q := by linarith
    have e : 3 * (5 * (5 * q + 1) * (q - 1) / (36 * q ^ 2)) =
        3 * (5 * (5 * q + 1) * (q - 1)) / (36 * q ^ 2) := by ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h := mul_nonneg (mul_nonneg (by positivity : (0 : ℚ) ≤ 5 * q + 1) (sq_nonneg q))
      (by linarith : (0 : ℚ) ≤ q - 7)
    nlinarith [h]
  have hlt : (Nat.card G : ℚ) < 3 * Nat.card G₀ := by
    rw [hGμ, hG₀μ]
    have : μ < 3 * μ₀ := by linarith
    nlinarith
  have hindex : Nat.card G = G₀.index * Nat.card G₀ := (G₀.index_mul_card).symm
  have hlt' : G₀.index < 3 := by
    have hlt'' : Nat.card G < 3 * Nat.card G₀ := by exact_mod_cast hlt
    rw [hindex] at hlt''
    have hpos : 0 < Nat.card G₀ := Nat.card_pos
    by_contra hcon
    push Not at hcon
    nlinarith
  obtain ⟨SC⟩ : Nonempty (Sylow 2 (Subgroup.centralizer ({J} : Set G))) := inferInstance
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_sylow_centralizer φ hZ hZodd h2 hJ _ SC rfl
  have hSG₀ : (S : Subgroup G) ≤ G₀ := by
    rw [hS]
    exact (Subgroup.map_subtype_le _).trans hCG₀
  have hodd : ¬ 2 ∣ G₀.index := fun h => S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hSG₀))
  have hpos : 0 < G₀.index := Nat.pos_of_ne_zero G₀.index_ne_zero_of_finite
  have h1 : G₀.index = 1 := by omega
  have htop : G₀ = ⊤ := Subgroup.index_eq_one.mp h1
  have hzcen : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ G₀ := by rw [htop]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at hzcen
    exact hz1 hzcen
  · obtain ⟨a, b, hab⟩ := hnonab
    have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

include hZ hZodd h2 hJ in
theorem centralizer_le_of_mem_centerSub
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) {z : G}
    (hzC : z ∈ centerSub φ) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer {J} := by
  by_cases hcase : ∃ g ∈ Subgroup.centralizer ({z} : Set G), g * J * g⁻¹ = invJ₁ φ
  · exact (false_of_conj_in_centralizer φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hzC hz1
      hcase).elim
  · exact centralizer_le_of_not_conj φ hZ hZodd h2 hJ hnonab hq hzC
      (fun g hg h => hcase ⟨g, hg, h⟩)

end CFSG.BrauerLinearThree
