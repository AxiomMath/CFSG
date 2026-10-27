module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.FactsVStar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.FactsDStar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {Q : Subgroup Y}

omit [Finite Y] in
theorem mem_conjStab_dstarComp_of_conjSub_mem (hc : ConjInvariant Φ) {K : Subgroup Y}
    (hK : K ∈ Φ) {g : Y} (hg : conjSub g K ∈ dstarComp Φ K) : g ∈ conjStab (dstarComp Φ K) := by
  have hKg : K ∈ dstarComp Φ (conjSub g K) := (mem_dstarComp_symm hK hg).2
  refine mem_conjStab_iff.mpr fun N => ⟨fun hN => ?_, fun hN => hg.trans (dstarComp_conj hc hN g)⟩
  have h1 := dstarComp_conj hc (hKg.trans hN) g⁻¹
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h1

theorem QFam.dstarComp_eq (h : QFam Φ Q) (hb : Thm3A.Thm3RBelowG (Nat.card Y)) {K : Subgroup Y}
    (hK : K ∈ Φ) (htw : TwinOrbits Φ K) : dstarComp Φ K = Φ := by
  have hΦ := h.hypGen
  have hc := hΦ.conjInvariant
  have hSΦ : ∀ M ∈ dstarComp Φ K, M ∈ Φ := fun M hM => (mem_dstarComp_symm hK hM).1
  refine Set.Subset.antisymm hSΦ ?_
  by_contra hne
  have hmemX : ∀ M ∈ dstarComp Φ K, M ≤ conjStab (dstarComp Φ K) := fun M hM x hx =>
    mem_conjStab_dstarComp hc hK hM (conjSub_eq_self_of_mem hx)
  have htwS : ∀ M ∈ dstarComp Φ K, ∀ N ∈ twinSet Φ M, N ∈ dstarComp Φ K := by
    intro M hM N hN
    by_cases hNM : N = M
    · rw [hNM]
      exact hM
    · obtain ⟨hNΦ, w, hwM, hwN⟩ := hN
      exact hM.tail ⟨hNΦ, Or.inl (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΦ M
        (Q3CL.T3.twin_mem_omegaNbr hΦ (hSΦ M hM) hNΦ hNM hwM hwN))⟩
  have hX : conjStab (dstarComp Φ K) ≠ ⊤ := by
    intro htop
    apply hne
    intro M hM
    obtain ⟨g, J, hJ, rfl⟩ := htw M hM
    have hg : g ∈ conjStab (dstarComp Φ K) := by
      rw [htop]
      exact Subgroup.mem_top g
    exact (mem_conjStab_iff.mp hg J).mpr (htwS K Relation.ReflTransGen.refl J hJ)
  have hc2 : ∀ L ∈ dstarComp Φ K, ∀ M ∈ dstarComp Φ K, M ∉ aStar Φ L → Commutes L M := by
    intro L hL M hM hML
    obtain ⟨J, zL, zJ, hv⟩ := not_aEmpty_iff.mp (h.notEmpty L (hSΦ L hL))
    have hJS : J ∈ dstarComp Φ K := hL.tail ⟨hv.mem, Or.inl hv.star⟩
    exact h.commutes_of_le_of_not_mem_aStar hb hX (hSΦ L hL) (hmemX L hL) (hmemX J hJS) hv
      (hSΦ M hM) (hmemX M hM) hML
  obtain ⟨J, z, j, hv⟩ := not_aEmpty_iff.mp (h.notEmpty K hK)
  have hJA : J ∈ aStar Φ K := mem_aStar_of_aViol hv
  have hJS : J ∈ dstarComp Φ K := (aStar_subset_dstarComp_gen hΦ hK hJA).2
  have hAJ : aStar Φ J = aStar Φ K := aStar_eq_of_mem_aStar hK hJA
  obtain ⟨u, v, R, T, cfg⟩ := Sec6Gen.exists_cfg64 hΦ hK hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr
  obtain ⟨r, hr, hru⟩ := cfg.exists_r
  obtain ⟨s, hs, hsv⟩ := cfg.symm.exists_r
  have hrK : r ∈ K := cfg.hR.1 hr
  have hsJ : s ∈ J := cfg.hT.1 hs
  have hd : ∀ g : Y, g * z * g⁻¹ ∈ conjStab (dstarComp Φ K) → g ∈ conjStab (dstarComp Φ K) := by
    intro g ht
    by_contra hg
    have htQ : g * z * g⁻¹ ∈ Q := h.normal.conj_mem z (h.inv_mem K hK z hv.hzK) g
    have hMΦ : conjSub g K ∈ Φ := hc g K hK
    have hMS : conjSub g K ∉ dstarComp Φ K := fun hMS =>
      hg (mem_conjStab_dstarComp_of_conjSub_mem hc hK hMS)
    have htM : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := hv.hzK.conj g
    have htA : g * z * g⁻¹ ∈ conjStab (aStar Φ K) := by
      by_contra htA
      set t := g * z * g⁻¹ with htdef
      have hKt : conjSub t K ∉ aStar Φ K := fun h' =>
        htA (mem_conjStab_aStar_of_conjSub_mem hc hK h')
      have hKtS : conjSub t K ∈ dstarComp Φ K :=
        (mem_conjStab_iff.mp ht K).mpr Relation.ReflTransGen.refl
      have hJtS : conjSub t J ∈ dstarComp Φ K := (mem_conjStab_iff.mp ht J).mpr hJS
      have hJt : conjSub t J ∉ aStar Φ K := by
        intro h'
        apply hKt
        have e1 := aStar_eq_of_mem_aStar (hc t K hK) (aStar_conj hc hJA t)
        rw [← aStar_eq_of_mem_aStar hK h', e1]
        exact Relation.ReflTransGen.refl
      have c1 : Commutes K (conjSub t K) := hc2 K Relation.ReflTransGen.refl _ hKtS hKt
      have c2 : Commutes K (conjSub t J) := hc2 K Relation.ReflTransGen.refl _ hJtS hJt
      have c3 : Commutes J (conjSub t K) := hc2 J hJS _ hKtS (by rw [hAJ]; exact hKt)
      have c4 : Commutes J (conjSub t J) := hc2 J hJS _ hJtS (by rw [hAJ]; exact hJt)
      have hr' : t * r * t⁻¹ ∈ conjSub t K := conj_mem_conjSub hrK
      have hs' : t * s * t⁻¹ ∈ conjSub t J := conj_mem_conjSub hsJ
      have e : t * (r * s) * t⁻¹ = (t * r * t⁻¹) * (t * s * t⁻¹) := by group
      have hcr : Commute r (t * (r * s) * t⁻¹) := by
        rw [e]
        exact Commute.mul_right (c1 r hrK _ hr') (c2 r hrK _ hs')
      have hcs : Commute s (t * (r * s) * t⁻¹) := by
        rw [e]
        exact Commute.mul_right (c3 s hsJ _ hr') (c4 s hsJ _ hs')
      have hcz : Commute z (t * (r * s) * t⁻¹) := by
        rw [e]
        exact Commute.mul_right (c1 z hv.hzK.mem _ hr') (c2 z hv.hzK.mem _ hs')
      have hcρ : Commute (t * (r * s) * t⁻¹) (r * s)⁻¹ := (hcr.mul_left hcs).symm.inv_right
      have hdQ : t * (r * s) * t⁻¹ * (r * s)⁻¹ ∈ Q := by
        have := Q.mul_mem htQ (h.normal.conj_mem t⁻¹ (Q.inv_mem htQ) (r * s))
        rwa [show t * (r * s * t⁻¹ * (r * s)⁻¹) = t * (r * s) * t⁻¹ * (r * s)⁻¹ by group]
          at this
      obtain ⟨n, hn⟩ := h.two ⟨_, hdQ⟩
      have hdn : (t * (r * s) * t⁻¹ * (r * s)⁻¹) ^ 2 ^ n = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      rw [hcρ.mul_pow, inv_pow, mul_inv_eq_one] at hdn
      have hz' : (r * s) ^ ((2 ^ n : ℕ) : ℤ) * z * ((r * s) ^ ((2 ^ n : ℕ) : ℤ))⁻¹ = z := by
        rw [zpow_natCast, ← hdn, ← (hcz.pow_right (2 ^ n)).eq, mul_inv_cancel_right]
      have h3 := (cfg.conj_rho_zpow_z_eq_iff hr hru hs hsv _).mp hz'
      have h3' : 3 ∣ 2 ^ n := by exact_mod_cast h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3') (by norm_num)
    have htz := h.conj_eq_of_mem_conjStab hK Relation.ReflTransGen.refl htQ htA hv.hzK
    have htj := h.conj_eq_of_mem_conjStab hK hJA htQ htA hv.hzJ
    have hcomm_of : ∀ w : Y, (g * z * g⁻¹) * w * (g * z * g⁻¹)⁻¹ = w →
        w * (g * z * g⁻¹) * w⁻¹ = g * z * g⁻¹ := by
      intro w hw
      have e : (g * z * g⁻¹) * w = w * (g * z * g⁻¹) := by
        calc (g * z * g⁻¹) * w = ((g * z * g⁻¹) * w * (g * z * g⁻¹)⁻¹) * (g * z * g⁻¹) := by
              group
          _ = w * (g * z * g⁻¹) := by rw [hw]
      rw [← e]
      group
    obtain ⟨Jm, zM, zJm, hvM⟩ := not_aEmpty_iff.mp (h.notEmpty _ hMΦ)
    obtain ⟨Ms, dM⟩ := FrameTwins.exists_of_aviol hΦ h.hyp.twoGroup
      (natCard_sylow_eq_eight h.hyp) hMΦ hvM
    have hVM : ∀ x : Y, x * (g * z * g⁻¹) * x⁻¹ = g * z * g⁻¹ →
        conjSub x (conjSub g K) = conjSub g K ∨ conjSub x (conjSub g K) = Ms := by
      intro x hx
      have hxM : conjSub x (conjSub g K) ∈ twinSet Φ (conjSub g K) := by
        refine ⟨hc x _ hMΦ, g * z * g⁻¹, htM, ?_⟩
        have := htM.conj x
        rwa [hx] at this
      rw [dM.twins] at hxM
      exact hxM
    obtain ⟨N, hNA, w, hw, hwM⟩ : ∃ N ∈ aStar Φ K, ∃ w : Y, IsUniqueInvolution N w ∧
        conjSub w (conjSub g K) = conjSub g K := by
      rcases hVM z (hcomm_of z htz) with hz1 | hz1
      · exact ⟨K, Relation.ReflTransGen.refl, z, hv.hzK, hz1⟩
      rcases hVM j (hcomm_of j htj) with hj1 | hj1
      · exact ⟨J, hJA, j, hv.hzJ, hj1⟩
      obtain ⟨s', hs'J, hs'⟩ := Thm3Quot.exists_conj_mul_involution hΦ hK hv
      have hNA : conjSub s' K ∈ aStar Φ K :=
        (mem_conjStab_iff.mp (le_conjStab_aStar hc hK hJA hs'J) K).mpr Relation.ReflTransGen.refl
      refine ⟨conjSub s' K, hNA, z * j, hs', ?_⟩
      rw [conjSub_mul, hj1, ← hz1, ← conjSub_mul, hv.hzK.sq, conjSub_one]
    have hNS : N ∈ dstarComp Φ K := (aStar_subset_dstarComp_gen hΦ hK hNA).2
    have hNΦ : N ∈ Φ := mem_of_mem_aStar hK hNA
    exact hMS (hNS.trans (h.mem_dstarComp_of_normalizes hMΦ hNΦ hw
      (mem_normalizer_of_conjSub_eq hwM)))
  apply hX
  rw [eq_top_iff]
  intro g _
  have hCz : Subgroup.centralizer ({z} : Set Y) ≤ conjStab (dstarComp Φ K) :=
    Thm3Quot.centralizer_le_conjStab_dstarComp_of_mem hΦ hK Relation.ReflTransGen.refl hv.hzK
  have h1 : (g * z * g⁻¹) * z * (g * z * g⁻¹)⁻¹ ∈ conjStab (dstarComp Φ K) :=
    hCz (Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_conj_conj hK hv.hzK g))
  exact hd g (hd _ h1)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
