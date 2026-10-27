module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CK372Ge5Setup
import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltAct
import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltRank
import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltSix
import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Action
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase

variable {X : Type} [Group X] [Finite X] {p : ℕ} {K E S : Subgroup X}

namespace K372Setting

theorem false_of_alt (h : K372Setting X p K E S) {n : ℕ} (hn : 5 ≤ n)
    (φ : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n))
    (hSC : ¬ S ≤ Subgroup.centralizer (K : Set X)) : False := by
  have := h.normal
  have : Fact p.Prime := ⟨h.prime⟩
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hKc : commutator ↥K = ⊤ := Group.isPerfect_def.mp h.quasi.1
  have hpsi : ∀ e ∈ E, UCK.Odd.psi K φ e = 1 → e = 1 := by
    intro e he h1
    have hc := UCK.Odd.centralizes_of_forall_comm_mem K hKc (g := e) fun y hy =>
      (UCK.Odd.psi_mk_eq_iff K φ e y hy).mp (by simp [h1])
    have hmem : e ∈ E ⊓ Subgroup.centralizer (K : Set X) := Subgroup.mem_inf.mpr
      ⟨he, Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm⟩
    rw [h.inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  by_cases hn6 : n = 6
  · subst hn6
    have hdvd := Subgroup.card_subgroup_dvd_card (E.map (UCK.Odd.psi K φ))
    rw [UCK.Alt36.card_map_of_faithful _ hpsi, h.card,
      CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6] at hdvd
    have h1 : p ∣ 2 ^ 5 * 3 ^ 2 * 5 := by
      norm_num
      exact (dvd_pow_self p two_ne_zero).trans hdvd
    rcases (Nat.Prime.dvd_mul h.prime).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul h.prime).mp h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp
          (h.prime.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp
          (h.prime.dvd_of_dvd_pow h3)
        omega
    · have h5 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_five).mp h2
      subst h5
      norm_num at hdvd
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
  have hEθ : Nat.card (E.map θ) = p ^ 2 := (UCK.Alt36.card_map_of_faithful θ hfaith).trans h.card
  have hn2p : 2 * p ≤ n := by
    by_contra hlt
    have hdvd := Subgroup.card_subgroup_dvd_card (E.map θ)
    rw [hEθ, Nat.card_perm, Nat.card_fin] at hdvd
    exact CFSG.HardMathSupport.RichardWeiss.Coordinator.not_sq_dvd_factorial_of_lt h.prime
      (by omega) hdvd
  have hZ : Subgroup.center ↥K = ⊥ := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have : Group.IsPerfect ↥K := h.quasi.1
    set ψ : ↥K →* alternatingGroup (Fin (m + 2)) :=
      φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
    have hker : ψ.ker = Subgroup.center ↥K := by
      ext x
      simp [ψ]
    obtain ⟨k, hk⟩ := h.isPGroup_center.exists_card_eq
    have hodd : Odd p := h.prime.odd_of_ne_two hp2
    have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega : 6 ≤ m) ψ
      (φ.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le
      (by rw [hker, hk]; exact hodd.pow)
    rw [hker] at h1
    exact Subgroup.card_eq_one.mp h1
  have hnp : n < p ^ 2 := by
    obtain ⟨V, E₀, -, -, hV1, hV2, hE₀, hE₀N, hcard⟩ :=
      GL83.PiGen.exists_klein_elem_in_component (p := p) (by omega) (by omega)
        (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ)
    rw [if_neg (show p ≠ 3 by omega), add_zero] at hcard
    obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow hE₀
    have hr := h.rank23 V hV1 hV2.isPGroup
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at hr
    have hk3 : k ≤ 3 := (CFSG.SectionRank.le_pRank h.prime.one_lt hE₀N hE₀ hk).trans hr
    have hle : (n - 4) / p ≤ 3 := (Nat.pow_le_pow_iff_right h.prime.one_lt).mp
      ((hcard.trans hk.le).trans (Nat.pow_le_pow_right h.prime.pos hk3))
    have h4 : n - 4 < 4 * p := (Nat.div_lt_iff_lt_mul h.prime.pos).mp (by omega)
    have h5p : 5 * p ≤ p ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul_right p hp5
    omega
  have hreg : ∀ x, Nat.card (UCK.Alt36.stb (E.map θ) x) ≠ 1 := by
    intro x hx
    have h1 := UCK.Alt36.card_orb_of_card_stb_one hEθ hx
    have h2 := Finset.card_le_univ (UCK.Alt36.orb (E.map θ) x)
    rw [h1, Fintype.card_fin] at h2
    omega
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
      ∃ y ∈ K, y ∈ rankThreeGamma 1 p E ∧ θ y = g := by
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
  have hσp : θ e₀ ^ p = 1 := by rw [← map_pow, h.elem.2 e₀ he₀, map_one]
  have hfix₀ := UCK.Alt36.card_compl_support_of_normalized h.prime hp2 hσp hR2 hRσ hRn hR1
  obtain ⟨c, -, hc⟩ := UCK.Alt36.exists_mem_fixE h.prime hp2 (h.elem.map θ) hEθ
    (Subgroup.mem_map_of_mem θ he₀) (fun h1 => he₀1 (hfaith e₀ he₀ h1)) hfix₀
  have hA := UCK.Alt36.alternatingGroup_le_of_no_regular h.prime hp2 (h.elem.map θ) hEθ hreg hc
  have hcl : UCK.Alt36.centClosure (E.map θ) ≤ (K ⊓ rankThreeGamma 1 p E).map θ := by
    rw [UCK.Alt36.centClosure, Subgroup.closure_le]
    rintro g ⟨hg, _, ⟨e, he, rfl⟩, he1, hge⟩
    obtain ⟨y, hy, hyΓ, rfl⟩ := hlift e he (fun h1 => he1 (by rw [h1, map_one])) g hg hge
    exact Subgroup.mem_map_of_mem θ (Subgroup.mem_inf.mpr ⟨hy, hyΓ⟩)
  refine h.not_le fun y hy => ?_
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

end K372Setting

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5
