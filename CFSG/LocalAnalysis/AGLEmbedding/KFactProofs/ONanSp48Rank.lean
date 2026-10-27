module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Local
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.Open

theorem factorization_three : (3 ^ 4 * 13045760).factorization 3 = 4 := by
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have h1 : (3 : ℕ).factorization 3 = 1 := Nat.Prime.factorization_self Nat.prime_three
  have h2 : (13045760 : ℕ).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [h1, h2]

section Rank

variable {T A E T0 : Subgroup Hh} {t1 t2 w s f : Hh} (L : Sp48Local T A E T0 t1 t2 w s f)

include L in
theorem T0_le_range : T0 ≤ (SemidirectProduct.inl : Sp8 →* Hh).range := by
  intro x hx
  rw [L.T0_eq] at hx
  have hxr : x.right = 1 := by
    have := (Subgroup.mem_inf.1 hx).2
    simpa [MonoidHom.mem_ker, SemidirectProduct.rightHom_eq_right] using this
  refine ⟨x.left, ?_⟩
  have := SemidirectProduct.inl_left_mul_inr_right x
  rw [hxr, map_one, mul_one] at this
  exact this

include L in
theorem card_T0S : Nat.card (T0.comap (SemidirectProduct.inl : Sp8 →* Hh)) = 3 ^ 4 := by
  have h := Subgroup.map_comap_eq_self (T0_le_range L)
  rw [← L.card_T0, ← h, Subgroup.card_map_of_injective SemidirectProduct.inl_injective]
  rw [h]

include L in
theorem elem_le_nine (hcard : Nat.card Sp8 = 3 ^ 4 * 13045760) (F : Subgroup Sp8)
    (hF : IsElemAbelian 3 F) : Nat.card F ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T0S : Subgroup Sp8 := T0.comap (SemidirectProduct.inl : Sp8 →* Hh) with hT0S
  have hc : Nat.card T0S = 3 ^ (Nat.card Sp8).factorization 3 := by
    rw [hT0S, card_T0S L, hcard, factorization_three]
  let S0 : Sylow 3 Sp8 := Sylow.ofCard T0S hc
  have hpg : IsPGroup 3 F := fun g => ⟨1, Subtype.ext (by simpa using hF.2 g g.2)⟩
  obtain ⟨P, hFP⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Sp8 S0 P
  have hP : (P : Subgroup Sp8) = T0S.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  set F' := F.map (MulAut.conj g⁻¹).toMonoidHom with hF'
  have hF'le : F' ≤ T0S := by
    rintro _ ⟨x, hx, rfl⟩
    have := hFP hx
    rw [hP] at this
    obtain ⟨y, hy, hyx⟩ := this
    have : (MulAut.conj g⁻¹).toMonoidHom x = y := by
      rw [← hyx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [this]
    exact hy
  have hF'e : IsElemAbelian 3 F' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hF _
  have hF'' : IsElemAbelian 3 (F'.map (SemidirectProduct.inl : Sp8 →* Hh)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hF'e _
  have hle : F'.map (SemidirectProduct.inl : Sp8 →* Hh) ≤ T0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hF'le hx
  have h9 := L.rank _ hle hF''
  rwa [Subgroup.card_map_of_injective SemidirectProduct.inl_injective, hF',
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at h9

end Rank

theorem exists_conj_eq_map {Y : Type} [Group Y] [Finite Y] (T : Sylow 3 Y) {T1 : Subgroup Y}
    (hT1 : IsPGroup 3 T1) (hc1 : Nat.card T1 = 3 ^ 5) (hT : Nat.card T ≤ 3 ^ 5) :
    ∃ y₀ : Y, (T : Subgroup Y) = T1.map (MulAut.conj y₀).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hle⟩ := hT1.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y T P
  have hP : (P : Subgroup Y) = (T : Subgroup Y).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hcardP : Nat.card (P : Subgroup Y) = Nat.card T := by
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq : T1 = (P : Subgroup Y) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP, hc1]; exact hT)
  refine ⟨g⁻¹, ?_⟩
  rw [heq, hP, Subgroup.map_map]
  have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id Y := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      MonoidHom.id_apply]
    group
  rw [this, Subgroup.map_id]

end CFSG.AGLEmbedding.KFactProofs.Sp48
