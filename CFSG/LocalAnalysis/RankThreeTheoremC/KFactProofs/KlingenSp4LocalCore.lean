module

public import CFSG.Open.GLBDefs
public import CFSG.Quasithin.Background.TwoReduced
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.Quasithin

structure SiegelRadicalData (p : ℕ) {Y : Type} [Group Y] (K T U : Subgroup Y) : Prop where
  T_le : T ≤ K
  U_le : U ≤ T
  elem : IsElemAbelian p U
  card_U : Nat.card U = p ^ 3
  card_T : Nat.card T = p ^ 4
  card_center : Nat.card (centerOf T) = p
  unique : ∀ B : Subgroup Y, B ≤ T → IsElemAbelian p B → Nat.card B = p ^ 3 → B = U
  coatom : ∀ M : Subgroup Y, Subgroup.normalizer (U : Set Y) ⊓ K ≤ M → M ≤ K →
    M = Subgroup.normalizer (U : Set Y) ⊓ K ∨ M = K

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] {K T U : Subgroup Y}

theorem eq_of_abelian_of_card_center [Finite Y] {T U B : Subgroup Y} (hT : Nat.card T = p ^ 4)
    (hZ : Nat.card (centerOf T) = p) (hUT : U ≤ T) (hBT : B ≤ T) (hUc : Nat.card U = p ^ 3)
    (hBc : Nat.card B = p ^ 3) (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) : B = U := by
  by_contra hne
  have hp : p.Prime := Fact.out
  have hsup : B ⊔ U = T := by
    have hle : B ⊔ U ≤ T := sup_le hBT hUT
    have hdvd : Nat.card (B ⊔ U : Subgroup Y) ∣ p ^ 4 :=
      hT ▸ Subgroup.card_dvd_of_le hle
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hdvd3 : p ^ 3 ∣ Nat.card (B ⊔ U : Subgroup Y) :=
      hUc ▸ Subgroup.card_dvd_of_le le_sup_right
    rw [hjc] at hdvd3
    have hj3 : 3 ≤ j := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd3
    have hj34 : j = 3 ∨ j = 4 := by omega
    rcases hj34 with rfl | rfl
    · have hUeq : U = B ⊔ U :=
        Subgroup.eq_of_le_of_card_ge (le_sup_right (a := B)) (by rw [hjc, hUc])
      exact absurd (Subgroup.eq_of_le_of_card_ge (hUeq ▸ (le_sup_left (b := U)))
        (by rw [hBc, hUc])) hne
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hjc, hT])
  have hD : B ⊓ U ≤ centerOf T := by
    intro d hd
    refine ⟨hBT hd.1, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have hcen : B ⊔ U ≤ Subgroup.centralizer ({d} : Set Y) := by
      refine sup_le (fun b hb => ?_) (fun u hu => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact hBab d hd.1 b hb
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact hUab d hd.2 u hu
    have := Subgroup.mem_centralizer_iff.mp (hcen (hsup ▸ ht)) d rfl
    exact this.symm
  have hDle : Nat.card (B ⊓ U : Subgroup Y) ≤ p :=
    hZ ▸ Subgroup.card_le_of_le hD
  have hrB : B.relIndex T = p := by
    have := Subgroup.relIndex_mul_card (H := B) (K := T)
    rw [inf_of_le_left hBT, hBc, hT] at this
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 3) (by rw [this]; ring)
  have hrU : U.relIndex T = p := by
    have := Subgroup.relIndex_mul_card (H := U) (K := T)
    rw [inf_of_le_left hUT, hUc, hT] at this
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 3) (by rw [this]; ring)
  have h3 : (B ⊓ U).relIndex T ≤ p * p := by
    have := Subgroup.relIndex_inf_le (H := B) (K := U) (L := T)
    rwa [hrB, hrU] at this
  have h4 := Subgroup.relIndex_mul_card (H := B ⊓ U) (K := T)
  rw [inf_of_le_left (inf_le_left.trans hBT), hT] at h4
  have hp2 : 2 ≤ p := hp.two_le
  by_contra _
  have hlt : Nat.card (B ⊓ U : Subgroup Y) < p ^ 2 := by
    by_contra hge
    push Not at hge
    have : p ^ 2 ≤ Nat.card (B ⊓ U : Subgroup Y) := hge
    nlinarith [Nat.card_pos (α := (B ⊓ U : Subgroup Y))]
  have hpos := Nat.card_pos (α := (B ⊓ U : Subgroup Y))
  nlinarith [h4, h3, hDle, hlt]

namespace SiegelRadicalData

theorem map_conj_eq (h : SiegelRadicalData p K T U) {g : Y}
    (hg : U.map (MulAut.conj g).toMonoidHom ≤ T) : U.map (MulAut.conj g).toMonoidHom = U :=
  h.unique _ hg (h.elem.map _)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card_U])

theorem T_le_normalizer (h : SiegelRadicalData p K T U) :
    T ≤ Subgroup.normalizer (U : Set Y) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine h.map_conj_eq fun _ hx => ?_
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  exact T.mul_mem (T.mul_mem hg (h.U_le hu)) (T.inv_mem hg)

theorem normalizer_T_le (h : SiegelRadicalData p K T U) :
    Subgroup.normalizer (T : Set Y) ≤ Subgroup.normalizer (U : Set Y) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine h.map_conj_eq fun _ hx => ?_
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  exact (Subgroup.mem_normalizer_iff.mp hg u).mp (h.U_le hu)

theorem normalizer_le_weakCore [Finite Y] (T : Sylow p Y)
    (h : SiegelRadicalData p K (T : Subgroup Y) U) :
    Subgroup.normalizer (U : Set Y) ≤ GLBWeakCore p (T : Subgroup Y) := by
  have hp : p.Prime := Fact.out
  have hrk : 3 ≤ Open.pRank p U := CFSG.SectionRank.le_pRank hp.one_lt le_rfl h.elem h.card_U
  exact CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p h.U_le (by omega)
    (hrk.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp le_sup_left))

theorem sup_normalizer_eq_top [Finite Y] [K.Normal] (T : Sylow p Y)
    (h : SiegelRadicalData p K (T : Subgroup Y) U) :
    Subgroup.normalizer (U : Set Y) ⊔ K = ⊤ := by
  have hfr := Sylow.normalizer_sup_eq_top' (N := K) T h.T_le
  rw [eq_top_iff, ← hfr]
  exact sup_le_sup_right h.normalizer_T_le _

theorem eq_normalizer [Finite Y] [K.Normal] (T : Sylow p Y)
    (h : SiegelRadicalData p K (T : Subgroup Y) U) {Y₀ : Subgroup Y}
    (hY₀ : GLBWeakCore p (T : Subgroup Y) ≤ Y₀) (hne : Y₀ ≠ ⊤) :
    Y₀ = Subgroup.normalizer (U : Set Y) := by
  have hNU : Subgroup.normalizer (U : Set Y) ≤ Y₀ := (h.normalizer_le_weakCore T).trans hY₀
  have hfr := h.sup_normalizer_eq_top T
  have hinf : Y₀ ⊓ K = Subgroup.normalizer (U : Set Y) ⊓ K := by
    rcases h.coatom (Y₀ ⊓ K) (inf_le_inf_right K hNU) inf_le_right with h1 | h1
    · exact h1
    · exfalso
      apply hne
      have hKY : K ≤ Y₀ := inf_eq_right.mp h1
      rw [eq_top_iff, ← hfr]
      exact sup_le hNU hKY
  refine le_antisymm ?_ hNU
  intro y hy
  set Q := Subgroup.normalizer (U : Set Y) ⊓ K with hQ
  have hyQ : ∀ {y : Y}, y ∈ Y₀ → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := by
    intro y hy q hq
    rw [← hinf] at hq ⊢
    exact ⟨Y₀.mul_mem (Y₀.mul_mem hy hq.1) (Y₀.inv_mem hy),
      (inferInstance : K.Normal).conj_mem q hq.2 y⟩
  have hUQ : U ≤ Q := fun u hu =>
    ⟨Subgroup.le_normalizer hu, h.T_le (h.U_le hu)⟩
  have hTQ : (T : Subgroup Y) ≤ Q := fun t ht => ⟨h.T_le_normalizer ht, h.T_le ht⟩
  set P' := U.map (MulAut.conj y).toMonoidHom with hP'
  have hP'Q : P' ≤ Q := by
    rintro _ hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    exact hyQ hy u (hUQ hu)
  have hQN : Q ≤ Subgroup.normalizer (P' : Set Y) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hy' : y⁻¹ ∈ Y₀ := Y₀.inv_mem hy
    have hq' : y⁻¹ * q * y ∈ Q := by simpa using hyQ hy' q hq
    have key : ∀ x : Y, x ∈ P' ↔ y⁻¹ * x * y ∈ U := by
      intro x
      constructor
      · rintro hx
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
        simpa [MulAut.conj_apply, mul_assoc] using hu
      · intro hx
        exact Subgroup.mem_map.mpr ⟨y⁻¹ * x * y, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [key, key]
    have := (Subgroup.mem_normalizer_iff.mp hq'.1 (y⁻¹ * x * y))
    simpa [mul_assoc] using this
  have hpP' : IsPGroup p P' := h.elem.isPGroup.map _
  have hpsup : IsPGroup p (P' ⊔ (T : Subgroup Y) : Subgroup Y) :=
    hpP'.to_sup_of_normal_left' T.isPGroup' (fun t ht => hQN (hTQ ht))
  have hP'T : P' ≤ (T : Subgroup Y) := by
    have := T.is_maximal' hpsup le_sup_right
    exact le_sup_left.trans this.le
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact h.map_conj_eq hP'T

theorem pRank_top_le [Finite Y] (T : Sylow p Y) (h : SiegelRadicalData p K (T : Subgroup Y) U) :
    Open.pRank p (⊤ : Subgroup Y) ≤ 3 := by
  have hp : p.Prime := Fact.out
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
  obtain ⟨P, hEP⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Y T P
  have hcardP : Nat.card (g • T : Sylow p Y) = p ^ 4 := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity T, h.card_T]
  by_contra hlt
  push Not at hlt
  have hdvd : Nat.card E ∣ p ^ 4 := hcardP ▸ Subgroup.card_dvd_of_le hEP
  obtain ⟨j, hj, hjE⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hj4 : j = 4 := by
    by_contra hj4
    have : j ≤ 3 := by omega
    exact absurd (hjE ▸ Nat.pow_le_pow_right hp.pos this) (not_le.mpr hlt)
  have hEeq : E = ((g • T : Sylow p Y) : Subgroup Y) :=
    Subgroup.eq_of_le_of_card_ge hEP (by rw [hcardP, hjE, hj4])
  have hcomm : ∀ a ∈ (T : Subgroup Y), ∀ b ∈ (T : Subgroup Y), a * b = b * a := by
    intro a ha b hb
    have hga : g * a * g⁻¹ ∈ E := by
      rw [hEeq, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
    have hgb : g * b * g⁻¹ ∈ E := by
      rw [hEeq, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨b, hb, by simp [MulAut.conj_apply]⟩
    have := hE.comm hga hgb
    have h2 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      simpa [mul_assoc] using this
    simpa using h2
  have hcen : centerOf (T : Subgroup Y) = (T : Subgroup Y) := by
    refine inf_eq_left.mpr fun t ht => ?_
    rw [Subgroup.mem_centralizer_iff]
    exact fun b hb => hcomm b hb t ht
  have := h.card_center
  rw [hcen, h.card_T] at this
  have h1 : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at h1
  omega

end SiegelRadicalData

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
