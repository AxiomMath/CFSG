module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveA
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFivePureCo2
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Blueprint CFSG.Monster.GMS Subgroup CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.RankThree.Native

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {G : Type*} [Group G]

private theorem orderOf_conj_eq (g y : G) : orderOf (g * y * g⁻¹) = orderOf y := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

private theorem orderOf_eq_five_of_conj_pow (k : G) {σ x : G} {a : ℕ} (hx : orderOf x = 5)
    (ha : ¬ 5 ∣ a) (e : k * σ * k⁻¹ = x ^ a) : orderOf σ = 5 := by
  have hco : (orderOf x).Coprime a := by
    rw [hx]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 ha
  rw [← orderOf_conj_eq k σ, e, hco.orderOf_pow, hx]

private theorem map_conj_le_of_conj {t t₀ c : G} (hct : c * t * c⁻¹ = t₀) {F : Subgroup G}
    (hFt : F ≤ centralizer ({t} : Set G)) :
    F.map (MulAut.conj c).toMonoidHom ≤ centralizer ({t₀} : Set G) := by
  rintro _ ⟨f, hf, rfl⟩
  have hft : f * t = t * f := mem_centralizer_singleton_iff.1 (hFt hf)
  rw [mem_centralizer_singleton_iff, ← hct]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc c * f * c⁻¹ * (c * t * c⁻¹) = c * (f * t) * c⁻¹ := by group
    _ = c * (t * f) * c⁻¹ := by rw [hft]
    _ = c * t * c⁻¹ * (c * f * c⁻¹) := by group

private theorem card_map_conj (c : G) (F : Subgroup G) :
    Nat.card (F.map (MulAut.conj c).toMonoidHom) = Nat.card F :=
  card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective

private theorem exists_mem_of_mem_map_conj {c x : G} {F : Subgroup G}
    (hx : x ∈ F.map (MulAut.conj c).toMonoidHom) : ∃ y ∈ F, c * y * c⁻¹ = x := by
  obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
  exact ⟨y, hy, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

private theorem exists_image_card {H : Type*} [Group H] {C K : Subgroup G} (hKC : K ≤ C)
    (φ : ↥C →* H) (hK : Nat.card K = 5 ^ 2) (hker : ¬ 5 ∣ Nat.card φ.ker) :
    ∃ M : Subgroup H, Nat.card M = 5 ^ 2 ∧
      ∀ σ ∈ M, ∃ y ∈ K, ∃ hy : y ∈ C, φ ⟨y, hy⟩ = σ ∧ orderOf y = orderOf σ := by
  have hinj : Function.Injective (φ.comp (Subgroup.inclusion hKC)) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have h1 : Nat.card (φ.comp (Subgroup.inclusion hKC)).ker ∣ 5 ^ 2 := by
      rw [← hK]
      exact Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (φ.comp (Subgroup.inclusion hKC)).ker ∣ Nat.card φ.ker := by
      have hle : (φ.comp (Subgroup.inclusion hKC)).ker.map (Subgroup.inclusion hKC) ≤ φ.ker := by
        rintro _ ⟨x, hx, rfl⟩
        exact hx
      have h := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKC)] at h
    obtain ⟨m, -, e⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 h1
    rw [e] at h2
    have hm0 : m = 0 := by
      by_contra h0
      exact hker ((dvd_pow_self 5 h0).trans h2)
    rw [hm0, pow_zero] at e
    exact Subgroup.eq_bot_of_card_eq _ e
  refine ⟨(φ.comp (Subgroup.inclusion hKC)).range, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top, hK]
  · rintro _ ⟨y, rfl⟩
    exact ⟨(y : G), y.2, hKC y.2, rfl,
      (Subgroup.orderOf_coe y).trans (orderOf_injective _ hinj y).symm⟩

end Generic


theorem exists_fiveA_mem_of_babyInv_one_B {t : NativeSporadic.B} (ht : BabyInv 1 t)
    {F : Subgroup NativeSporadic.B} (hFt : F ≤ centralizer ({t} : Set NativeSporadic.B))
    (hF : Nat.card F = 5 ^ 2) :
    ∃ y ∈ F, orderOf y = 5 ∧ Matrix.rank (CFSG.Monster.B.bMat y - 1) = 3480 := by
  obtain ⟨c, hct⟩ :=
    isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 1 t xB ht babyInv_one_xB)
  have hF'le := map_conj_le_of_conj hct hFt
  have hF'c := (card_map_conj c F).trans hF
  obtain ⟨ds, hds⟩ :=
    exists_conj_mem_centralizer_xB babyInv_one_aFiveA aFiveA_mem_centralizer_sFiveA
  have hos := (orderOf_conj_eq ds sFiveA).trans orderOf_sFiveA
  obtain ⟨rs, as, ks, has, es⟩ := exists_conj_pow_co2LineElt (orderOf_fiveHom hos hds)
  have hN : ¬ 5 ∣ Nat.card fiveHom.ker := by
    rw [card_ker_fiveHom]
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd
    omega
  obtain ⟨M, hMc, hMK⟩ := exists_image_card (H := NativeSporadic.Co2) hF'le fiveHom hF'c hN
  obtain ⟨σ, hσ, a, k, ha, e⟩ := exists_lineType_mem_of_card_co2 hMc rs
  obtain ⟨y₁, hy₁, hy₁C, rfl, ho⟩ := hMK σ hσ
  have ho₁ := ho.trans (orderOf_eq_five_of_conj_pow k (orderOf_co2LineElt _) ha e)
  obtain ⟨n, hn, g, hg⟩ := exists_conj_pow_of_same_line ho₁ hos hy₁C hds ha has e es
  have hr₁ : Matrix.rank (CFSG.Monster.B.bMat y₁ - 1) = 3480 := by
    rw [← hg, rank_bMat_conj, rank_bMat_pow hos hn, rank_bMat_conj]
    exact bFiveAM_parts.2.2.1
  obtain ⟨y, hyF, hyx⟩ := exists_mem_of_mem_map_conj hy₁
  have hoy := orderOf_conj_eq c y
  have hry := rank_bMat_conj c y
  rw [hyx] at hoy hry
  exact ⟨y, hyF, hoy.symm.trans ho₁, hry.symm.trans hr₁⟩

end CFSG.LocalAnalysis.GLTheoremA.H1017
