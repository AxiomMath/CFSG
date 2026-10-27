module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmComp
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeConstrained

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup

variable {Z : Type} [Group Z] [Finite Z] {p : ℕ}

theorem top_le_of_normal (hp : p.Prime) (Q : Sylow p Z) {N Y : Subgroup Z} [N.Normal]
    (hNY : N ≤ Y) (h2 : 2 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ N))
    (hΓ2 : ∀ S : Subgroup Z, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y) :
    ⊤ ≤ Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQsyl : ¬ p ∣ ((Q : Subgroup Z).subgroupOf ⊤).index := by
    have : ((Q : Subgroup Z).subgroupOf ⊤).index = (Q : Subgroup Z).index := by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    rw [this]
    exact Q.not_dvd_index
  have h := P64Free.le_sup_of_normal_of_gammaTwo hp (X := ⊤) (Y := Y) (Q := (Q : Subgroup Z))
    (N := N) le_top (Subgroup.normalizer_eq_top (H := N)).ge le_top Q.isPGroup' hQsyl h2
    (fun S hS hS2 => inf_le_left.trans (hΓ2 S hS hS2))
  exact h.trans (sup_le hNY le_rfl)

theorem exists_isComponentOf_Z (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : primeComplementCore (G := Z) p = ⊥) (Q : Sylow p Z) {Y : Subgroup Z}
    (hQnc : ¬ IsCyclic (Q : Subgroup Z)) (hQY : (Q : Subgroup Z) ≤ Y)
    (hΓ2 : ∀ S : Subgroup Z, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (hY : ¬ ⊤ ≤ Y) : ∃ L : Subgroup Z, IsComponentOf L ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hno
  have hcore : CFSG.pPrimeCore p Z = ⊥ := hZ
  have hlayer : CFSG.layer Z = ⊥ := by
    rw [CFSG.layer.eq_sSup]
    refine le_bot_iff.mp (sSup_le fun K hK => ?_)
    exact absurd ⟨K, (CFSG.isComponent_iff_open K).mp hK⟩ hno
  have hchar : centralizer (CFSG.pCore p Z : Set Z) ≤ CFSG.pCore p Z :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot Z p hcore hlayer
  set U := CFSG.pCore p Z with hU
  have hUn : U.Normal := CFSG.pCore_normal (p := p) (G := Z)
  have hUQ : U ≤ (Q : Subgroup Z) := P64Free.pCore_le_sylow Q
  apply hY
  by_cases hUc : IsCyclic U
  · have hQn : (Q : Subgroup Z).Normal := by
      refine ⟨fun q hq g => ?_⟩
      have hc : g * q * g⁻¹ * q⁻¹ ∈ U :=
        hchar (P64Free.commutator_mem_centralizer_of_isCyclic (U := U) g q)
      have e : g * q * g⁻¹ = (g * q * g⁻¹ * q⁻¹) * q := by group
      rw [e]
      exact mul_mem (hUQ hc) hq
    have hQ2 : 2 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ (Q : Subgroup Z)) := by
      rw [inf_idem]
      exact CFSG.AGLEmbedding.two_le_pRank_of_isPGroup_not_isCyclic hp hp2 Q.isPGroup' hQnc
    exact top_le_of_normal hp Q hQY hQ2 hΓ2
  · have hU2 : 2 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ U) := by
      rw [inf_eq_right.mpr hUQ]
      exact CFSG.AGLEmbedding.two_le_pRank_of_isPGroup_not_isCyclic hp hp2
        (Q.isPGroup'.to_le hUQ) hUc
    exact top_le_of_normal hp Q (hUQ.trans hQY) hU2 hΓ2

theorem map_conj_eq_self_iff (g : Z) (M : Subgroup Z) :
    M.map (MulAut.conj g).toMonoidHom = M ↔ g ∈ normalizer (M : Set Z) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, by simp⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by simpa using hyx
      exact this ▸ hy
  · intro h
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (h y).mp hy
    · intro hz
      have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
      refine ⟨g⁻¹ * z * g, (h _).mpr ?_, ?_⟩
      · rw [e]
        exact hz
      · exact e

theorem sq_not_mem_normalizer (hp : p.Prime) (hp2 : p ≠ 2) {g : Z} {n : ℕ}
    (hg : g ^ (p ^ n) = 1) {M : Subgroup Z} (hgM : g ∉ normalizer (M : Set Z)) :
    g ^ 2 ∉ normalizer (M : Set Z) := by
  intro h2
  apply hgM
  have hodd : Odd (p ^ n) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨m, hm⟩ := hodd
  have e : g = (g ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    have : 2 * (m + 1) = p ^ n + 1 := by omega
    rw [this, pow_succ, hg, one_mul]
  rw [e]
  exact Subgroup.pow_mem _ h2 _

theorem map_conj_map_conj (a b : Z) (M : Subgroup Z) :
    (M.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      M.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem exists_pow_orderOf_eq_prime (hp : p.Prime) {g : Z} {n : ℕ} (hg : orderOf g = p ^ n)
    (hg1 : g ≠ 1) : ∃ k : ℕ, orderOf (g ^ k) = p := by
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hg
    exact hg1 hg
  have hdvd : p ^ (n - 1) ∣ orderOf g := by
    rw [hg]
    exact pow_dvd_pow p (Nat.sub_le n 1)
  refine ⟨p ^ (n - 1), ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, hg]
  have : p ^ n = p ^ (n - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [this, Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]

theorem exists_cube_of_not_normalizes (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : primeComplementCore (G := Z) p = ⊥) (Q : Sylow p Z) {M : Subgroup Z}
    (hM : IsComponentOf M ⊤) (hQM : ¬ (Q : Subgroup Z) ≤ normalizer (M : Set Z)) :
    ∃ y ∈ M, ∃ E : Subgroup Z, E ≤ (Q : Subgroup Z) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 3 ∧ y ∈ E ∧ y ≠ 1 ∧ y ^ p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hyQM, hyo, hyc⟩ := exists_mem_inf_sylow_component hp hp2 hZ Q hM
  have hyp : y ^ p = 1 := by
    rw [← hyo]
    exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    obtain ⟨l, -, hl⟩ := hyc
    exact hl (by simp)
  obtain ⟨g, hgQ, hgM⟩ : ∃ g ∈ (Q : Subgroup Z), g ∉ normalizer (M : Set Z) := by
    by_contra hcon
    push Not at hcon
    exact hQM fun g hg => hcon g hg
  obtain ⟨n, hn⟩ := Q.isPGroup' ⟨g, hgQ⟩
  have hgn : g ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hg2 : g ^ 2 ∉ normalizer (M : Set Z) := sq_not_mem_normalizer hp hp2 hgn hgM
  have hM₂ := isComponentOf_map_conj hM g
  have hM₃ := isComponentOf_map_conj hM (g ^ 2)
  have h12 : M ≠ M.map (MulAut.conj g).toMonoidHom := fun h =>
    hgM ((map_conj_eq_self_iff g M).1 h.symm)
  have h13 : M ≠ M.map (MulAut.conj (g ^ 2)).toMonoidHom := fun h =>
    hg2 ((map_conj_eq_self_iff (g ^ 2) M).1 h.symm)
  have h23 : M.map (MulAut.conj g).toMonoidHom ≠ M.map (MulAut.conj (g ^ 2)).toMonoidHom := by
    intro h
    apply h12
    have h' := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) h
    rw [map_conj_map_conj, map_conj_map_conj] at h'
    have e1 : g⁻¹ * g = 1 := inv_mul_cancel g
    have e2 : g⁻¹ * g ^ 2 = g := by group
    rw [e1, e2] at h'
    have e3 : M.map (MulAut.conj (1 : Z)).toMonoidHom = M := by
      ext x
      simp
    rw [e3] at h'
    exact h'
  obtain ⟨y₂, hy₂QM, hy₂o, hy₂c⟩ := exists_mem_inf_sylow_component hp hp2 hZ Q hM₂
  obtain ⟨y₃, hy₃QM, hy₃o, hy₃c⟩ := exists_mem_inf_sylow_component hp hp2 hZ Q hM₃
  have hy₂p : y₂ ^ p = 1 := by
    rw [← hy₂o]
    exact pow_orderOf_eq_one y₂
  have hy₃p : y₃ ^ p = 1 := by
    rw [← hy₃o]
    exact pow_orderOf_eq_one y₃
  obtain ⟨hel, hcard⟩ := isElemAbelian_card_three_of_components hp hM hM₂ hM₃ h12 h13 h23
    hyQM.2 hy₂QM.2 hy₃QM.2 hyp hy₂p hy₃p hyc hy₂c hy₃c
  refine ⟨y, hyQM.2, zpowers y ⊔ zpowers y₂ ⊔ zpowers y₃, ?_, hel, hcard, ?_, hy1, hyp⟩
  · exact sup_le (sup_le (zpowers_le.mpr hyQM.1) (zpowers_le.mpr hy₂QM.1))
      (zpowers_le.mpr hy₃QM.1)
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem_zpowers y))

theorem exists_central_of_inf (hp : p.Prime) (Q : Sylow p Z) {M : Subgroup Z}
    (hQM : (Q : Subgroup Z) ≤ normalizer (M : Set Z)) (hne : (Q : Subgroup Z) ⊓ M ≠ ⊥) :
    ∃ z ∈ (Q : Subgroup Z) ⊓ M, orderOf z = p ∧ ∀ q ∈ (Q : Subgroup Z), q * z = z * q := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnorm : ∀ g ∈ (Q : Subgroup Z), ∀ u ∈ (Q : Subgroup Z) ⊓ M,
      g * u * g⁻¹ ∈ (Q : Subgroup Z) ⊓ M := by
    intro g hg u hu
    refine ⟨(Q : Subgroup Z).mul_mem ((Q : Subgroup Z).mul_mem hg hu.1)
      ((Q : Subgroup Z).inv_mem hg), ?_⟩
    exact ((Subgroup.mem_normalizer_iff.mp (hQM hg)) u).mp hu.2
  obtain ⟨z, hzU, hz1, hzc⟩ :=
    SU1.exists_central_of_normal hp Q.isPGroup' inf_le_left hnorm hne
  have hzQ : z ∈ (Q : Subgroup Z) := hzU.1
  obtain ⟨n, hn⟩ : ∃ n, orderOf (⟨z, hzQ⟩ : (Q : Subgroup Z)) = p ^ n :=
    IsPGroup.iff_orderOf.mp Q.isPGroup' ⟨z, hzQ⟩
  rw [Subgroup.orderOf_mk] at hn
  obtain ⟨k, hk⟩ := exists_pow_orderOf_eq_prime hp hn hz1
  exact ⟨z ^ k, pow_mem hzU k, hk, fun q hq =>
    (Commute.pow_right (show Commute q z from hzc q hq) k).eq⟩

theorem exists_cube_of_component (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : primeComplementCore (G := Z) p = ⊥) (Q : Sylow p Z)
    (h3 : 3 ≤ Open.pRank p (Q : Subgroup Z)) {M : Subgroup Z} (hM : IsComponentOf M ⊤) :
    ∃ y ∈ M, ∃ E : Subgroup Z, E ≤ (Q : Subgroup Z) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 3 ∧ y ∈ E ∧ y ≠ 1 ∧ y ^ p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hQM : (Q : Subgroup Z) ≤ normalizer (M : Set Z)
  · obtain ⟨y, hyQM, hyo, hyc⟩ := exists_mem_inf_sylow_component hp hp2 hZ Q hM
    have hy1 : y ≠ 1 := by
      rintro rfl
      obtain ⟨l, -, hl⟩ := hyc
      exact hl (by simp)
    have hne : (Q : Subgroup Z) ⊓ M ≠ ⊥ := by
      intro h
      have : y ∈ (Q : Subgroup Z) ⊓ M := hyQM
      rw [h, Subgroup.mem_bot] at this
      exact hy1 this
    obtain ⟨z, hzU, hzo, hzc⟩ := exists_central_of_inf hp Q hQM hne
    have hzp : z ^ p = 1 := by
      rw [← hzo]
      exact pow_orderOf_eq_one z
    obtain ⟨E, hEQ, hE, hEc, hzE⟩ := exists_cube_containing_central hp h3 hzU.1 hzp hzc
    refine ⟨z, hzU.2, E, hEQ, hE, hEc, hzE, ?_, hzp⟩
    intro h1
    rw [h1, orderOf_one] at hzo
    exact hp.one_lt.ne hzo
  · exact exists_cube_of_not_normalizes hp hp2 hZ Q hM hQM

theorem component_le_of_ne (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : primeComplementCore (G := Z) p = ⊥) (Q : Sylow p Z) {Y : Subgroup Z}
    (h3 : 3 ≤ Open.pRank p (Q : Subgroup Z))
    (hΓ1 : ∀ E : Subgroup Z, E ≤ (Q : Subgroup Z) → IsElemAbelian p E → Nat.card E = p ^ 3 →
      ∀ S : Subgroup Z, S ≤ E → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    {M M' : Subgroup Z} (hM : IsComponentOf M ⊤) (hM' : IsComponentOf M' ⊤) (hne : M ≠ M') :
    M' ≤ Y := by
  obtain ⟨y, hyM, E, hEQ, hE, hEc, hyE, hy1, hyp⟩ := exists_cube_of_component hp hp2 hZ Q h3 hM
  have hN : normalizer ((zpowers y : Subgroup Z) : Set Z) ≤ Y :=
    hΓ1 E hEQ hE hEc _ (zpowers_le.mpr hyE) (P64Free.one_le_pRank_zpowers hp hyp hy1)
  intro m hm
  exact hN (P64Free.mem_normalizer_zpowers_of_commute (component_commute hM' hM hne.symm hm hyM))

theorem unique_component (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : primeComplementCore (G := Z) p = ⊥) (Q : Sylow p Z) {Y : Subgroup Z} (hY : ¬ ⊤ ≤ Y)
    (h3 : 3 ≤ Open.pRank p (Q : Subgroup Z))
    (hΓ2 : ∀ S : Subgroup Z, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (hΓ1 : ∀ E : Subgroup Z, E ≤ (Q : Subgroup Z) → IsElemAbelian p E → Nat.card E = p ^ 3 →
      ∀ S : Subgroup Z, S ≤ E → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    {L K : Subgroup Z} (hL : IsComponentOf L ⊤) (hK : IsComponentOf K ⊤) : L = K := by
  by_contra hLK
  have hall : ∀ M : Subgroup Z, IsComponentOf M ⊤ → M ≤ Y := by
    intro M hM
    rcases eq_or_ne M L with rfl | hML
    · exact component_le_of_ne hp hp2 hZ Q h3 hΓ1 hK hL (Ne.symm hLK)
    · exact component_le_of_ne hp hp2 hZ Q h3 hΓ1 hL hM (Ne.symm hML)
  set N : Subgroup Z := sSup {M : Subgroup Z | IsComponentOf M ⊤} with hN
  have hNY : N ≤ Y := sSup_le fun M hM => hall M hM
  haveI hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : N ≤ N.comap (MulAut.conj g).toMonoidHom := by
      refine sSup_le fun M hM => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup (isComponentOf_map_conj hM g)
    exact hle hn
  obtain ⟨y₁, hy₁QL, hy₁o, hy₁c⟩ := exists_mem_inf_sylow_component hp hp2 hZ Q hL
  obtain ⟨y₂, hy₂QK, hy₂o, hy₂c⟩ := exists_mem_inf_sylow_component hp hp2 hZ Q hK
  have hp₁ : y₁ ^ p = 1 := by
    rw [← hy₁o]
    exact pow_orderOf_eq_one y₁
  have hp₂ : y₂ ^ p = 1 := by
    rw [← hy₂o]
    exact pow_orderOf_eq_one y₂
  obtain ⟨hel, hcard⟩ := isElemAbelian_card_two_of_components hp hL hK hLK hy₁QL.2 hy₂QK.2 hp₁
    hp₂ hy₁c hy₂c
  have hLN : L ≤ N := le_sSup hL
  have hKN : K ≤ N := le_sSup hK
  have hle : zpowers y₁ ⊔ zpowers y₂ ≤ (Q : Subgroup Z) ⊓ N :=
    sup_le (zpowers_le.mpr ⟨hy₁QL.1, hLN hy₁QL.2⟩)
      (zpowers_le.mpr ⟨hy₂QK.1, hKN hy₂QK.2⟩)
  have h2 : 2 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ N) :=
    SU1.le_pRank hp.one_lt hle hel (k := 2) hcard
  exact hY (top_le_of_normal hp Q hNY h2 hΓ2)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm
