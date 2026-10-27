module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Setup
import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltAct
import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltRank
import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltSix
import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFA6
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Rest

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)
open CFSG.RankThree.PartTwo.Sec4.Census (IsThreeCenterCover)
open CFSG.LocalAnalysis.UniquenessCase

variable {X : Type} [Group X] [Finite X] {K E S : Subgroup X}

namespace K37Setting

theorem center_eq_bot_of_not_cover (h : K37Setting X K E S) {T : Type} [Group T]
    (φ : ↥K ⧸ Subgroup.center ↥K ≃* T) (hT : ¬ IsThreeCenterCover ↥K T) :
    Subgroup.center ↥K = ⊥ := by
  rcases h.isPGroup_center.card_eq_or_dvd with h1 | hz
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact (hT ⟨h.quasi, hz, ⟨φ⟩⟩).elim

theorem twoLocalPrimeRank_le (h : K37Setting X K E S) : twoLocalPrimeRank 3 X ≤ 3 := by
  refine csSup_le' ?_
  rintro a ⟨H, hH, rfl⟩
  obtain ⟨T, hT, hT2, rfl⟩ := hH
  rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact h.rank23 T hT hT2

theorem goal_of_alt (h : K37Setting X K E S) {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (φ : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n)) (hO : ¬ K37Open K E) :
    K37Goal K S := by
  intro hSC
  haveI := h.normal
  have hKc : commutator ↥K = ⊤ := Group.isPerfect_def.mp h.quasi.1
  have hn12 : n ≤ 12 := by
    by_contra hcon
    have h4 := UCK.Alt36.four_le_twoLocalPrimeRank_of_thirteen_le K φ (by omega)
    have h3 := h.twoLocalPrimeRank_le
    omega
  obtain ⟨θ, hθ⟩ : ∃ θ : X →* Equiv.Perm (Fin n), θ = UCK.Alt36.theta K hn hn6 φ := ⟨_, rfl⟩
  have hθK : ∀ y (hy : y ∈ K), θ y = (φ (QuotientGroup.mk ⟨y, hy⟩) : Equiv.Perm (Fin n)) :=
    fun y hy => by rw [hθ]; exact UCK.Alt36.theta_of_mem K hn hn6 φ hy
  have hθ1 : ∀ x : X, θ x = 1 → ∀ y ∈ K, x * y = y * x := fun x hx =>
    UCK.Odd.centralizes_of_forall_comm_mem K hKc
      ((UCK.Alt36.theta_eq_one_iff K hn hn6 φ x).mp (by rw [← hθ]; exact hx))
  have hθc : ∀ x y (hy : y ∈ K), θ x * θ y = θ y * θ x →
      x * y * x⁻¹ * y⁻¹ ∈ UCK.Odd.centerOf K := by
    intro x y hy hxy
    rw [hθK y hy, hθ] at hxy
    exact (UCK.Odd.psi_mk_eq_iff K φ x y hy).mp ((UCK.Alt36.psi_fix_iff K hn hn6 φ x _).mpr hxy)
  have hfaith : ∀ e ∈ E, θ e = 1 → e = 1 := by
    intro e he h1
    have hmem : e ∈ E ⊓ Subgroup.centralizer (K : Set X) := Subgroup.mem_inf.mpr
      ⟨he, Subgroup.mem_centralizer_iff.mpr fun y hy => (hθ1 e h1 y hy).symm⟩
    rw [h.inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hEθ : Nat.card (E.map θ) = 3 ^ 2 :=
    (UCK.Alt36.card_map_of_faithful θ hfaith).trans (h.card.trans (by norm_num))
  have hn5 : n ≠ 5 := by
    rintro rfl
    have hdvd := Subgroup.card_subgroup_dvd_card (E.map θ)
    rw [hEθ, Nat.card_perm, Nat.card_fin] at hdvd
    exact absurd hdvd (by decide)
  have hZ : Subgroup.center ↥K = ⊥ := by
    rcases (show n = 7 ∨ 8 ≤ n by omega) with rfl | h8
    · exact h.center_eq_bot_of_not_cover φ fun hc =>
        hO (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))))))
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      haveI : Group.IsPerfect ↥K := h.quasi.1
      set ψ : ↥K →* alternatingGroup (Fin (m + 2)) :=
        φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
      have hker : ψ.ker = Subgroup.center ↥K := by
        ext x
        simp [ψ, MonoidHom.mem_ker]
      obtain ⟨k, hk⟩ := h.isPGroup_center.exists_card_eq
      have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega : 6 ≤ m) ψ
        (φ.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le
        (by rw [hker, hk]; exact Odd.pow (by decide))
      rw [hker] at h1
      exact Subgroup.card_eq_one.mp h1
  by_cases h11 : n = 11
  · subst h11
    exact Or.inr
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ⟩
  have hZc : ∀ x y, y ∈ K → θ x * θ y = θ y * θ x → x * y = y * x := by
    intro x y hy hxy
    have h1 := hθc x y hy hxy
    rw [UCK.Hyp36.centerOf_eq K, hZ, Subgroup.map_bot, Subgroup.mem_bot] at h1
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have hθinj : ∀ y ∈ K, θ y = 1 → y = 1 := by
    intro y hy h1
    have h2 : (⟨y, hy⟩ : ↥K) ∈ Subgroup.center ↥K :=
      Subgroup.mem_center_iff.mpr fun z => Subtype.ext (hθ1 y h1 z z.2).symm
    rw [hZ, Subgroup.mem_bot] at h2
    exact congrArg Subtype.val h2
  have hlift : ∀ e ∈ E, e ≠ 1 → ∀ g ∈ alternatingGroup (Fin n), g * θ e = θ e * g →
      ∃ y ∈ K, y ∈ rankThreeGamma 1 3 E ∧ θ y = g := by
    intro e he he1 g hg hge
    obtain ⟨c, hc⟩ := φ.surjective ⟨g, hg⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective c
    have hθy : θ y = g := by rw [hθK y hy, hc]
    refine ⟨y, hy, h.centralizer_le he he1 (Subgroup.mem_centralizer_singleton_iff.mpr ?_), hθy⟩
    exact (hZc e y hy (by rw [hθy]; exact hge.symm)).symm
  obtain ⟨e₀, he₀, he₀1, s, hs, hse, hsK⟩ := h.exists_comm_not_mem hSC
  obtain ⟨R, hR⟩ : ∃ R : Subgroup (Equiv.Perm (Fin n)),
      R = S.map θ ⊓ Subgroup.centralizer ({θ e₀} : Set (Equiv.Perm (Fin n))) := ⟨_, rfl⟩
  have hR2 : IsPGroup 2 R := by
    rw [hR]
    exact (h.two.map θ).to_le inf_le_left
  have hRσ : ∀ r ∈ R, r * θ e₀ = θ e₀ * r := fun r hr => by
    rw [hR] at hr
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hr).2
  have hRn : ∀ k ∈ alternatingGroup (Fin n), k * θ e₀ = θ e₀ * k →
      ∀ r ∈ R, k * r * k⁻¹ ∈ R := by
    intro k hk hkσ r hr
    rw [hR] at hr ⊢
    obtain ⟨y, -, hyΓ, rfl⟩ := hlift e₀ he₀ he₀1 k hk hkσ
    obtain ⟨hr1, hr2⟩ := Subgroup.mem_inf.mp hr
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hr1
      rw [← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map_of_mem θ
        ((Subgroup.mem_normalizer_iff.mp (h.le_normalizer hyΓ) t).mp ht)
    · rw [Subgroup.mem_centralizer_singleton_iff] at hr2 ⊢
      have hk' : Commute (θ y) (θ e₀) := hkσ
      have hr' : Commute r (θ e₀) := hr2
      exact ((hk'.mul_left hr').mul_left hk'.inv_left).eq
  have hθs : θ s ∈ R := by
    rw [hR]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem θ hs, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hse]
  have hR1 : R ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hθs
    exact hsK (Subgroup.mem_centralizer_iff.mpr fun y hy => (hθ1 s hθs y hy).symm)
  have hσ3 : θ e₀ ^ 3 = 1 := by rw [← map_pow, h.elem.2 e₀ he₀, map_one]
  have hfix₀ := UCK.Alt36.card_compl_support_of_normalized Nat.prime_three (by norm_num) hσ3 hR2
    hRσ hRn hR1
  rcases UCK.Alt36.plane_dichotomy Nat.prime_three (by norm_num) (h.elem.map θ) hEθ
      (by rw [Fintype.card_fin]; exact hn12) (Subgroup.mem_map_of_mem θ he₀)
      (fun h1 => he₀1 (hfaith e₀ he₀ h1)) hfix₀ with hA | ⟨-, hn11, -⟩
  ·
    have hcl : UCK.Alt36.centClosure (E.map θ) ≤ (K ⊓ rankThreeGamma 1 3 E).map θ := by
      rw [UCK.Alt36.centClosure, Subgroup.closure_le]
      rintro g ⟨hg, _, ⟨e, he, rfl⟩, he1, hge⟩
      obtain ⟨y, hy, hyΓ, rfl⟩ := hlift e he (fun h1 => he1 (by rw [h1, map_one])) g hg hge
      exact Subgroup.mem_map_of_mem θ (Subgroup.mem_inf.mpr ⟨hy, hyΓ⟩)
    refine (h.not_le fun y hy => ?_).elim
    have hyA : θ y ∈ alternatingGroup (Fin n) := by
      rw [hθK y hy]
      exact (φ _).2
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.mp (hcl (hA hyA))
    obtain ⟨hy'K, hy'Γ⟩ := Subgroup.mem_inf.mp hy'
    have h1 : y'⁻¹ * y = 1 := hθinj _ (K.mul_mem (K.inv_mem hy'K) hy)
      (by rw [map_mul, map_inv, hyy', inv_mul_cancel])
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    exact hy'Γ
  · rw [Fintype.card_fin] at hn11
    exact absurd hn11 h11

theorem le_centralizer_of_alt_six (h : K37Setting X K E S)
    (φ : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 6)) (hO : ¬ K37Open K E) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  have hZ := h.center_eq_bot_of_not_cover φ fun hc =>
    hO (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))))))
  obtain ⟨Θ, hΘinj⟩ : ∃ Θ : MulAut ↥K →* MulAut (alternatingGroup (Fin 6)), Function.Injective Θ :=
    ⟨(MulAut.congr (((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.trans φ)).toMonoidHom, (MulAut.congr _).injective⟩
  have hinner : (autIm E K).map Θ ≤
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range :=
    fun α hα => UCK.Alt36.exists_conj_eq_six Nat.prime_three (by norm_num) α
      ((h.isElemAbelian_autIm.map Θ).2 α hα)
  obtain ⟨B, hB⟩ : ∃ B : Subgroup (alternatingGroup (Fin 6)),
      B = ((autIm E K).map Θ).comap MulAut.conj := ⟨_, rfl⟩
  have hB9 : Nat.card B = 3 ^ 2 := by
    rw [hB, ← Subgroup.card_map_of_injective (UCK.Alt36.conj_injective (n := 6) (by norm_num)),
      Subgroup.map_comap_eq_self hinner, Subgroup.card_map_of_injective hΘinj, h.card_autIm]
  have hN : ∀ b ∈ B, ∀ q ∈ (autIm S K).map Θ,
      MulAut.conj b * q * (MulAut.conj b)⁻¹ ∈ (autIm S K).map Θ := by
    intro b hb q hq
    rw [hB, Subgroup.mem_comap] at hb
    obtain ⟨_, ⟨⟨g, hgN⟩, hg, rfl⟩, hgb⟩ := Subgroup.mem_map.mp hb
    rw [← hgb]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer_map Θ (Subgroup.mem_map_of_mem Θ
      (mem_normalizer_autIm hgN (h.le_normalizer_S (Subgroup.mem_subgroupOf.mp hg))))) q).mp hq
  have hQ := CFSG.RankThree.PartTwo.Sec14.Ronan1422S.kfA6_no_two_normalized B
    (hB9.trans (by norm_num)) _ ((isPGroup_autIm (K := K) h.two).map Θ) hN
  exact le_centralizer_of_autIm_eq_bot h.S_le_normalizer_K
    ((Subgroup.map_eq_bot_iff_of_injective _ hΘinj).mp hQ)

theorem goal_of_alternating (h : K37Setting X K E S) {n : ℕ} (hn : 5 ≤ n)
    (hφ : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n))) (hO : ¬ K37Open K E) :
    K37Goal K S := by
  obtain ⟨φ⟩ := hφ
  by_cases hn6 : n = 6
  · subst hn6
    exact fun hSC => absurd (h.le_centralizer_of_alt_six φ hO) hSC
  · exact h.goal_of_alt hn hn6 φ hO

end K37Setting

end CFSG.LocalAnalysis.RankThreeUC.S15.K37
