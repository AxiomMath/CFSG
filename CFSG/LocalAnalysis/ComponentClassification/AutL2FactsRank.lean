module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

universe u

theorem commute_of_forall_sq {G : Type*} [Group G] (H : Subgroup G) (hH : ∀ h ∈ H, h * h = 1)
    {a b : G} (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a := by
  have hinv : ∀ h ∈ H, h⁻¹ = h := fun h hh => inv_eq_of_mul_eq_one_right (hH h hh)
  calc a * b = (a * b)⁻¹ := (hinv _ (H.mul_mem ha hb)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv b hb, hinv a ha]

theorem isPGroup_two_of_forall_sq {G : Type*} [Group G] (H : Subgroup G)
    (hH : ∀ h ∈ H, h * h = 1) : IsPGroup 2 H := fun x =>
  ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (hH x x.2)⟩

theorem pgl2_card_le_four_of_sq {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (E : Subgroup (PGL2 K)) (hE : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ 4 := by
  by_contra hlt
  push Not at hlt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (isPGroup_two_of_forall_sq E hE)
  have h4 : 2 ^ 2 ∣ Nat.card E := by
    rw [hk]
    apply Nat.pow_dvd_pow
    by_contra hk2
    push Not at hk2
    interval_cases k <;> simp_all
  obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
  set V' : Subgroup (PGL2 K) := V.map E.subtype with hV'
  have hV'card : Nat.card V' = 4 := by
    rw [hV', Subgroup.card_map_of_injective E.subtype_injective, hV]
    norm_num
  have hV'E : V' ≤ E := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hV'K : IsKleinFour V' := by
    have : Nontrivial V' := by
      rw [← Finite.one_lt_card_iff_nontrivial, hV'card]
      norm_num
    refine ⟨hV'card, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
    apply orderOf_eq_prime
    · rw [pow_two]
      exact Subtype.ext (hE g (hV'E g.2))
    · exact hg
  have hEC : E ≤ centralizer (V' : Set (PGL2 K)) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro v hv
    exact commute_of_forall_sq E hE (hV'E hv) hx
  rw [pgl2_kleinFour_centralizer_eq_self K hK V' hV'K] at hEC
  have := Subgroup.card_le_of_le hEC
  omega

abbrev fieldProj (F : Type u) [Field F] : PGammaL2 F →* (F ≃+* F) :=
  SemidirectProduct.rightHom

abbrev linearPart {F : Type u} [Field F] (E : Subgroup (PGammaL2 F)) : Subgroup (PGL2 F) :=
  E.comap SemidirectProduct.inl

theorem card_eq_linearPart_mul {F : Type u} [Field F] [Finite F] (E : Subgroup (PGammaL2 F)) :
    Nat.card E = Nat.card (linearPart E) * Nat.card (E.map (fieldProj F)) := by
  let π : E →* (F ≃+* F) := (fieldProj F).comp E.subtype
  have hrange : π.range = E.map (fieldProj F) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card π.ker = Nat.card (linearPart E) := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1.left, ?_⟩, fun g => ⟨⟨SemidirectProduct.inl g.1,
      g.2⟩, ?_⟩, ?_, ?_⟩
    · have hx : (x.1 : PGammaL2 F).right = 1 := x.2
      have : SemidirectProduct.inl (x.1 : PGammaL2 F).left = (x.1 : PGammaL2 F) :=
        SemidirectProduct.ext rfl hx.symm
      change SemidirectProduct.inl (x.1 : PGammaL2 F).left ∈ E
      rw [this]
      exact x.1.2
    · exact SemidirectProduct.right_inl (φ := pgl2FieldAut F) g.1
    · intro x
      have hx : (x.1 : PGammaL2 F).right = 1 := x.2
      exact Subtype.ext (Subtype.ext (SemidirectProduct.ext rfl hx.symm))
    · intro g
      rfl
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker, hker, mul_comm,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv, hrange]

theorem pGammaL2_card_le_eight_of_sq {F : Type u} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (E : Subgroup (PGammaL2 F)) (hE : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ 8 := by
  have h1 : Nat.card (linearPart E) ≤ 4 :=
    pgl2_card_le_four_of_sq hF _ fun g hg => SemidirectProduct.inl_injective (by
      rw [map_mul, map_one]; exact hE _ hg)
  have h2 : Nat.card (E.map (fieldProj F)) ≤ 2 := by
    apply card_le_two_of_sq_ringAut
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE x hx, map_one]
  rw [card_eq_linearPart_mul]
  calc Nat.card (linearPart E) * Nat.card (E.map (fieldProj F)) ≤ 4 * 2 :=
        Nat.mul_le_mul h1 h2
    _ = 8 := by norm_num

theorem pGammaL2_card_le_four_of_sq_of_prime {F : Type u} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p) (E : Subgroup (PGammaL2 F))
    (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 4 := by
  have hF' : Nat.card F = p ^ 1 := by rw [pow_one, hF]
  have h1 : Nat.card (linearPart E) ≤ 4 :=
    pgl2_card_le_four_of_sq (isOddPrimePower_of hp hp2 le_rfl hF') _ fun g hg =>
      SemidirectProduct.inl_injective (by rw [map_mul, map_one]; exact hE _ hg)
  have h2 : Nat.card (E.map (fieldProj F)) ≤ 1 := by
    calc Nat.card (E.map (fieldProj F)) ≤ Nat.card (F ≃+* F) := Subgroup.card_le_card_group _
      _ = 1 := card_ringAut F hp hF'
  rw [card_eq_linearPart_mul]
  calc Nat.card (linearPart E) * Nat.card (E.map (fieldProj F)) ≤ 4 * 1 :=
        Nat.mul_le_mul h1 h2
    _ = 4 := by norm_num

end CFSG.ComponentClassification.AutL2Facts
