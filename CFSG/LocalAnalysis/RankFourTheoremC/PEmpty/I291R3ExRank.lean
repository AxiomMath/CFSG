module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporRank
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup

section Centralizer

variable {S : Type*} [Group S] [Finite S] {p : ℕ}

theorem three_le_pRank_centralizer_of_central_rank_two [Fact p.Prime] (P : Sylow p S)
    {E : Subgroup S} (hEP : E ≤ (P : Subgroup S)) (hE : IsElemAbelian p E)
    (hEc : ∀ e ∈ E, ∀ y ∈ (P : Subgroup S), e * y = y * e) (hE2 : p ^ 2 ≤ Nat.card E)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) {x : S} (hxP : x ∈ (P : Subgroup S))
    (hx : x ^ p = 1) : 3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  by_cases hxc : ∀ y ∈ (P : Subgroup S), x * y = y * x
  · refine three_le_pRank_centralizer_of_sylow P (fun y hy => ?_) h3
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hxc y hy).symm
  · have hxE : x ∉ E := fun h => hxc fun y hy => hEc x h y hy
    set F : Subgroup S := Subgroup.closure ((E : Set S) ∪ {x}) with hF
    have hEF : E ≤ F := fun a ha => Subgroup.subset_closure (Or.inl ha)
    have hxF : x ∈ F := Subgroup.subset_closure (Or.inr rfl)
    have hFC : F ≤ centralizer ({x} : Set S) := by
      refine (Subgroup.closure_le _).2 fun a ha => ?_
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rcases ha with ha | ha
      · exact hEc a ha x hxP
      · rw [Set.mem_singleton_iff.1 ha]
    haveI := hE.1
    have hFcomm : IsMulCommutative F := by
      refine Subgroup.isMulCommutative_closure ?_
      intro a ha b hb _
      show a * b = b * a
      rcases ha with ha | ha
      · rcases hb with hb | hb
        · exact setLike_mul_comm ha hb
        · rw [Set.mem_singleton_iff.1 hb]
          exact hEc a ha x hxP
      · rw [Set.mem_singleton_iff.1 ha]
        rcases hb with hb | hb
        · exact (hEc b hb x hxP).symm
        · rw [Set.mem_singleton_iff.1 hb]
    have hFexp : ∀ y ∈ F, y ^ p = 1 := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem a ha =>
        rcases ha with ha | ha
        · exact hE.2 a ha
        · rw [Set.mem_singleton_iff.1 ha]
          exact hx
      | one => exact one_pow p
      | mul a b ha hb iha ihb =>
        have hab : Commute a b := setLike_mul_comm ha hb
        rw [hab.mul_pow, iha, ihb, one_mul]
      | inv a ha iha => rw [inv_pow, iha, inv_one]
    obtain ⟨m, hm⟩ := exists_card_eq_pow_of_forall_pow_eq_one hFexp
    obtain ⟨k, hk⟩ := exists_card_eq_pow_of_forall_pow_eq_one hE.2
    have hk2 : 2 ≤ k := by
      by_contra h
      have h1 : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      have h2 : p ^ 2 ≤ p ^ 1 := by
        rw [hk] at hE2
        exact hE2.trans h1
      have h4 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp1 (by norm_num)
      omega
    have hlt : E < F := lt_of_le_of_ne hEF fun h => hxE (h ▸ hxF)
    have hcardlt : Nat.card E < Nat.card F := by
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hEF) fun h => ?_
      exact hlt.ne (Subgroup.eq_of_le_of_card_ge hEF h.ge)
    have hkm : k < m := by
      rw [hk, hm] at hcardlt
      exact (Nat.pow_lt_pow_iff_right hp1).1 hcardlt
    exact (by omega : 3 ≤ m).trans (CFSG.SectionRank.le_pRank hp1 hFC ⟨hFcomm, hFexp⟩ hm)

theorem pRank_centralizer_conj_le' (hp : 1 < p) (g y : S) :
    CFSG.Open.pRank p (centralizer ({g * y * g⁻¹} : Set S)) ≤
      CFSG.Open.pRank p (centralizer ({y} : Set S)) := by
  obtain ⟨E, hEC, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp
    (centralizer ({g * y * g⁻¹} : Set S))
  refine CFSG.SectionRank.le_pRank hp (E := E.map (MulAut.conj g⁻¹).toMonoidHom) ?_
    (CFSG.SectionRank.isElemAbelian_map hE _) ?_
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : c * (g * y * g⁻¹) = (g * y * g⁻¹) * c :=
      Subgroup.mem_centralizer_singleton_iff.1 (hEC hc)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change g⁻¹ * c * g⁻¹⁻¹ * y = y * (g⁻¹ * c * g⁻¹⁻¹)
    simp only [inv_inv]
    calc g⁻¹ * c * g * y = g⁻¹ * (c * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * c) * g := by rw [hc']
      _ = y * (g⁻¹ * c * g) := by group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]

theorem three_le_pRank_centralizer_of_exists_central_rank_two [Fact p.Prime] (P₀ : Sylow p S)
    {E₀ : Subgroup S} (hEP : E₀ ≤ (P₀ : Subgroup S)) (hE : IsElemAbelian p E₀)
    (hEc : ∀ e ∈ E₀, ∀ y ∈ (P₀ : Subgroup S), e * y = y * e) (hE2 : p ^ 2 ≤ Nat.card E₀)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) {x : S} (hx : x ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hzp : IsPGroup p (Subgroup.zpowers x) := by
    intro z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 z.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, OneMemClass.coe_one, SubgroupClass.coe_pow]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hxP : x ∈ (P : Subgroup S) := hP (Subgroup.mem_zpowers x)
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq S P₀ P
  have hyP : g⁻¹ * x * g ∈ (P₀ : Subgroup S) := by
    have := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := MulAut.conj g)
      (S := (P₀ : Subgroup S)) (x := x)).1 hxP
    simpa [MulAut.smul_def, MulAut.conj_apply, MulAut.inv_apply] using this
  have hyp : (g⁻¹ * x * g) ^ p = 1 := by
    have h := conj_pow (a := g⁻¹) (b := x) (i := p)
    rw [inv_inv] at h
    rw [h, hx]
    group
  have h1 := three_le_pRank_centralizer_of_central_rank_two P₀ hEP hE hEc hE2 h3 hyP hyp
  have h2 := pRank_centralizer_conj_le' hp1 g⁻¹ x
  simp only [inv_inv] at h2
  omega

end Centralizer

section Transfer

variable {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] {p : ℕ}

theorem card_map_eq_of_injOn_subgroup (π : G →* S) {U : Subgroup G}
    (hinj : ∀ u ∈ U, π u = 1 → u = 1) : Nat.card (U.map π) = Nat.card U := by
  have hψ : Function.Injective (π.comp U.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hu
    have : u = 1 := Subtype.ext (hinj u u.2 hu)
    simp [this]
  have hrange : (π.comp U.subtype).range = U.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm

theorem three_le_pRank_centralizer_of_heis [Fact p.Prime] (π : G →* S)
    (hπ : Function.Surjective π) {U Z : Subgroup G} (hU : IsPGroup p U) (hidx : ¬ p ∣ U.index)
    (hZU : Z ≤ U) (hZc : ∀ z ∈ Z, ∀ u ∈ U, z * u = u * z) (hZexp : ∀ z ∈ Z, z ^ p = 1)
    (hZcard : p ^ 2 ≤ Nat.card Z) (hinj : ∀ u ∈ U, π u = 1 → u = 1)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) {x : S} (hx : x ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) := by
  set P₀ : Sylow p S := (hU.toSylow hidx).mapSurjective hπ with hP₀
  have hP₀coe : (P₀ : Subgroup S) = U.map π := by
    rw [hP₀, Sylow.coe_mapSurjective, IsPGroup.toSylow_coe]
  have hZcomm : IsMulCommutative Z :=
    ⟨⟨fun a b => Subtype.ext (hZc a a.2 b (hZU b.2))⟩⟩
  have hZe : IsElemAbelian p Z := ⟨hZcomm, hZexp⟩
  refine three_le_pRank_centralizer_of_exists_central_rank_two P₀ (E₀ := Z.map π) ?_
    (CFSG.SectionRank.isElemAbelian_map hZe π) ?_ ?_ h3 hx
  · rw [hP₀coe]
    exact Subgroup.map_mono hZU
  · rintro _ ⟨z, hz, rfl⟩ _ hy
    rw [hP₀coe] at hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_mul, ← map_mul, hZc z hz u hu]
  · rw [card_map_eq_of_injOn_subgroup π (fun u hu => hinj u (hZU hu))]
    exact hZcard

theorem pRank_top_le_of_heis [Fact p.Prime] (π : G →* S) (hπ : Function.Surjective π)
    {U : Subgroup G} (hU : IsPGroup p U) (hidx : ¬ p ∣ U.index)
    (hinj : ∀ u ∈ U, π u = 1 → u = 1) {k : ℕ} (hk : Nat.card U = p ^ k) :
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ k := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set P₀ : Sylow p S := (hU.toSylow hidx).mapSurjective hπ with hP₀
  have hP₀coe : (P₀ : Subgroup S) = U.map π := by
    rw [hP₀, Sylow.coe_mapSurjective, IsPGroup.toSylow_coe]
  rw [← (CFSG.SectionRank.pRank_sylow P₀).1]
  refine CFSG.SectionRank.pRank_le hp1 fun E hE _ => ?_
  calc Nat.card E ≤ Nat.card (P₀ : Subgroup S) := Subgroup.card_le_of_le hE
    _ = p ^ k := by rw [hP₀coe, card_map_eq_of_injOn_subgroup π hinj, hk]

end Transfer

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
