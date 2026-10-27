module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Glue
public import CFSG.HardMathSupport.Lang.AnisoE6.F4InTwistedE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldConc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem card_le_of_conj_into_range {X G : Type*} [Group X] [Group G] {p n : ℕ}
    {ι : X →* G} (hι : Function.Injective ι)
    (hX : ∀ F : Subgroup X, IsElemAbelian p F → Nat.card F ≤ p ^ n) {F : Subgroup G}
    (hF : IsElemAbelian p F) (hconj : ∃ g : G, ∀ x ∈ F, g * x * g⁻¹ ∈ ι.range) :
    Nat.card F ≤ p ^ n := by
  obtain ⟨g, hg⟩ := hconj
  set c : G →* G := (MulAut.conj g).toMonoidHom with hc
  have hci : Function.Injective c := (MulAut.conj g).injective
  have hF₁ι : F.map c ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hcard : Nat.card ((F.map c).comap ι) = Nat.card F := by
    rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hF₁ι,
      Subgroup.card_map_of_injective hci]
  have hEA₁ : IsElemAbelian p (F.map c) := CFSG.StandardType.TableB.isElemAbelian_map hF c
  have hEA : IsElemAbelian p ((F.map c).comap ι) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hι ?_)⟩⟩, fun x hx => hι ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val (hEA₁.1.is_comm.comm ⟨ι a, a.2⟩ ⟨ι b, b.2⟩)
    · rw [map_pow, hEA₁.2 _ hx, map_one]
  rw [← hcard]
  exact hX _ hEA

private theorem three_dvd_sq_sub_one_of_mod {q : ℕ} (hq : q % 3 = 1 ∨ q % 3 = 2) :
    3 ∣ q ^ 2 - 1 := by
  have h : q ^ 2 % 3 = 1 := by
    rcases hq with h | h <;> rw [Nat.pow_mod, h]
  have h1 : 1 ≤ q ^ 2 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · rcases hq with h | h <;> simp at h
    · exact Nat.one_le_pow _ _ hq0
  omega

theorem card_le_pow_four_E6_three_of_mod_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) {F : Subgroup ↥(adjointGroup .E6 K)} (hF : IsElemAbelian 3 F) :
    Nat.card F ≤ 3 ^ 4 :=
  card_le_of_conj_into_range (CFSG.LieType.SeitzGeneration.ExcHighThree.e6F4Embed_injective K)
    (fun F' hF' => card_le_pow_rank_F4_of_dvd_sq Nat.prime_three (by norm_num)
      (three_dvd_sq_sub_one_of_mod (Or.inr hK)) hF') hF
    (CFSG.LieType.SeitzGeneration.ExcHighThree.exists_conj_into_e6F4_two K hK hF.2)

theorem card_le_pow_four_twistedE6_three_of_mod_one {F₀ K : Type} [Field F₀] [Finite F₀]
    [Field K] [Finite K] {q : ℕ} (hF₀ : Nat.card F₀ = q) (hK : Nat.card K = q ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ q) (hq3 : q % 3 = 1)
    {F : Subgroup ↥(twistedE6RootGroup K σ)} (hF : IsElemAbelian 3 F) :
    Nat.card F ≤ 3 ^ 4 := by
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H, ⟨e⟩, hH⟩ :=
    CFSG.HardMathSupport.Lang.AnisoE6.exists_f4_in_twistedE6 hF₀ hK σ hσ hq3
  have hHi : ¬ 3 ∣ H.index := by rwa [← Subgroup.relIndex_top_right]
  have hP : IsPGroup 3 F := fun x => ⟨1, by
    rw [pow_one]
    apply Subtype.ext
    simpa using hF.2 x x.2⟩
  obtain ⟨g, hg⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_conj_le_of_not_dvd_index H hHi hP
  have hrange : (H.subtype.comp e.toMonoidHom).range = H := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  refine card_le_of_conj_into_range (ι := H.subtype.comp e.toMonoidHom)
    (H.subtype_injective.comp e.injective)
    (fun F' hF' => card_le_pow_rank_F4_of_dvd_sq Nat.prime_three (by norm_num)
      (three_dvd_sq_sub_one_of_mod (Or.inl (by rwa [hF₀]))) hF') hF ⟨g⁻¹, fun x hx => ?_⟩
  rw [hrange, inv_inv]
  exact hg x hx

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
