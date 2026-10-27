module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A511Core
public import CFSG.Quasithin.H13.L32A511Gold
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A53c
import CFSG.Quasithin.H13.L32A511Pf

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

theorem lemma14_5_11_of_core_F4 (hcore : Lemma14_5_11Core_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ Y : Subgroup G), Ctx_F4 G T L V V₂ Y →
      quasithinO2QuotientIso (xL L V₂ ⊔ T) (Equiv.Perm (Fin 3)) →
      (xL L V₂ ⊔ T) ⊓ (Y ⊔ T) = T →
      pCoreOf 2 (hY T L V₂ Y) ≠ ⊥ → Group.IsSolvable ↥(hY T L V₂ Y) →
      thompsonJ T ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) →
      xL L V₂ = ⁅xL L V₂, thompsonJk 1 T⁆ →
      (CFSG.pPrimeCore 3 ↥(hY T L V₂ Y)).map (hY T L V₂ Y).subtype ≤
        Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
  intro G _ _ T L V V₂ Y C hXS3 hinf hQ hsolv hJ hX1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcoreC := hcore G T L V V₂ Y C hXS3 hinf hQ hsolv hJ hX1
  set H := hY T L V₂ Y with hHdef
  set W := vH T L V V₂ Y with hWdef
  set cW := cH T L V V₂ Y with hcWdef
  have hred : IsTwoReducedIn H W := C.isTwoReducedIn_vH_F4 hQ
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := hred.2.1
  have hXH : xL L V₂ ⊔ T ≤ H := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hYH : Y ⊔ T ≤ H := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hXH' : xL L V₂ ≤ H := le_sup_left.trans hXH
  have hcH : cW ≤ H := inf_le_left
  have hHc : H ≤ Subgroup.normalizer (cW : Set G) := by
    intro h hh
    have hhC : h ∈ Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) :=
      B2F.normalizer_le_normalizer_centralizer W (hHW hh)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨H.mul_mem (H.mul_mem hh hy1) (H.inv_mem hh),
        (Subgroup.mem_normalizer_iff.mp hhC y).mp hy2⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hhC y).mpr hy2⟩
      have := H.mul_mem (H.mul_mem (H.inv_mem hh) hy1) hh
      simpa [mul_assoc] using this
  have hTX := C.T_le_normalizer_xL_F4
  have hXTn : xL L V₂ ⊔ T ≤ Subgroup.normalizer (xL L V₂ : Set G) :=
    sup_le Subgroup.le_normalizer hTX
  have hmemN : ∀ g : G, (xL L V₂ ⊔ cW ≤ (xL L V₂ ⊔ cW).comap (MulAut.conj g).toMonoidHom) →
      g ∈ Subgroup.normalizer ((xL L V₂ ⊔ cW : Subgroup G) : Set G) := fun g hle =>
    Subgroup.mem_normalizer_fintype fun n hn => by
      have := hle hn
      simpa [MulAut.conj_apply] using this
  have hXTN : xL L V₂ ⊔ T ⊔ cW ≤ Subgroup.normalizer ((xL L V₂ ⊔ cW : Subgroup G) : Set G) := by
    refine sup_le (fun g hg => hmemN g (sup_le (fun x hx => ?_) (fun c hc => ?_)))
      (fun c hc => hmemN c (sup_le (fun x hx => ?_) (fun c' hc' => ?_)))
    · show g * x * g⁻¹ ∈ xL L V₂ ⊔ cW
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hXTn hg) x).mp hx)
    · show g * c * g⁻¹ ∈ xL L V₂ ⊔ cW
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hHc (hXH hg)) c).mp hc)
    · show c * x * c⁻¹ ∈ xL L V₂ ⊔ cW
      have h1 : x * c⁻¹ * x⁻¹ ∈ cW :=
        (Subgroup.mem_normalizer_iff.mp (hHc (hXH' hx)) c⁻¹).mp (cW.inv_mem hc)
      have e : c * x * c⁻¹ = (c * (x * c⁻¹ * x⁻¹)) * x := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_right (cW.mul_mem hc h1)) (Subgroup.mem_sup_left hx)
    · show c * c' * c⁻¹ ∈ xL L V₂ ⊔ cW
      exact Subgroup.mem_sup_right (cW.mul_mem (cW.mul_mem hc hc') (cW.inv_mem hc))
  set Nc : Subgroup ↥H := cW.subgroupOf H with hNc
  have hNcn : Nc.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hcH).mpr hHc
  set π := QuotientGroup.mk' Nc with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Nc
  have hπ1 : ∀ h : ↥H, π h = 1 ↔ (h : G) ∈ cW := fun h => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hNc, Subgroup.mem_subgroupOf]
  have hcW : ∀ g ∈ cW, g ∈ Subgroup.centralizer (W : Set G) := fun g hg => hg.2
  have hGI : F6.IsGoldschmidtTripleIn H (xL L V₂ ⊔ T) (Y ⊔ T) := by
    refine ⟨?_, nonempty_open_of_quasithinO2QuotientIso hXS3,
      nonempty_open_of_quasithinO2QuotientIso C.hS3, ?_⟩
    · apply le_antisymm
      · exact sup_le hXH hYH
      · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
          (le_sup_right.trans le_sup_right)
    · rw [hinf]
      exact C.isSylowTwoOf_T_F4 le_sup_right
  have hG := hGI.subgroupOf
  have hXc : (xL L V₂ ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 (xL L V₂ ⊔ T) := by
    refine le_pCoreOf_of_normal_of_S3 hXS3 inf_le_left ?_ ?_
    · intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, Ctx.le_normalizer_centralizer_vH hXH hx⟩
    · rw [C.oTwoUpper_xT_F4]
      intro h
      exact C.xL_not_le_centralizer_F4 (h.trans inf_le_right)
  have hYc := C.inf_yT_le_F4
  have h2grp : ∀ K : Subgroup G, K ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 K →
      IsPGroup 2 ↥(K.subgroupOf H ⊓ Nc) := by
    intro K hK
    have hle : K.subgroupOf H ⊓ Nc ≤ (pCoreOf 2 K).subgroupOf H := fun x hx =>
      hK ⟨hx.1, hx.2.2⟩
    exact ((pCoreOf_isPGroup 2 K).comap_of_injective H.subtype H.subtype_injective).to_le hle
  have hneYX : ¬ (Y ⊔ T).subgroupOf H ≤ (xL L V₂ ⊔ T).subgroupOf H ⊔ Nc := by
    intro hle
    apply C.not_le_normalizer_F4
    intro y hy
    have hyH : y ∈ H := hYH (Subgroup.mem_sup_left hy)
    have h1 : (⟨y, hyH⟩ : ↥H) ∈ (xL L V₂ ⊔ T).subgroupOf H ⊔ Nc :=
      hle (show y ∈ Y ⊔ T from Subgroup.mem_sup_left hy)
    have h2 : y ∈ ((xL L V₂ ⊔ T).subgroupOf H ⊔ Nc).map H.subtype := ⟨_, h1, rfl⟩
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXH,
      Subgroup.map_subgroupOf_eq_of_le hcH] at h2
    exact hXTN h2
  have hGD := goldschmidt_map_mk hG.symm (h2grp _ hYc) (h2grp _ hXc) hneYX
  have hO2 : Open.pCore 2 (↥H ⧸ Nc) = ⊥ := by
    set P₂ : Subgroup G := ((Open.pCore 2 (↥H ⧸ Nc)).comap π).map H.subtype with hP₂
    have hP₂H : P₂ ≤ H := Subgroup.map_subtype_le _
    have hP₂n : H ≤ Subgroup.normalizer (P₂ : Set G) := by
      intro h hh
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨n', hn', rfl⟩ := hn
      refine ⟨⟨h, hh⟩ * n' * (⟨h, hh⟩ : ↥H)⁻¹, ?_, rfl⟩
      show π (⟨h, hh⟩ * n' * (⟨h, hh⟩ : ↥H)⁻¹) ∈ Open.pCore 2 (↥H ⧸ Nc)
      rw [map_mul, map_mul, map_inv]
      exact (LieType.BorelTits.pCore_normal 2 (G := ↥H ⧸ Nc)).conj_mem _ hn' _
    have hP₂c : P₂ ≤ Subgroup.centralizer (W : Set G) := by
      refine hred.2.2.2 P₂ hP₂H hP₂n fun d hd => ?_
      obtain ⟨d', hd', rfl⟩ := hd
      obtain ⟨k, hk⟩ := (LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥H ⧸ Nc)) ⟨_, hd'⟩
      refine ⟨k, hcW _ ?_⟩
      have h1 : π (d' ^ 2 ^ k) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val hk
      have := (hπ1 _).mp h1
      simpa using this
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨h, rfl⟩ := hπs q
    rw [Subgroup.mem_bot, hπ1]
    exact ⟨h.2, hP₂c ⟨h, hq, rfl⟩⟩
  set Xs := ((xL L V₂).subgroupOf H).map π with hXs
  have hXcen : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ a ∈ Open.pCore p (↥H ⧸ Nc), ∀ x ∈ Xs,
      x * a = a * x := by
    intro p hp hp5 a ha x hx
    have : Fact p.Prime := ⟨hp⟩
    set P : Subgroup G := ((Open.pCore p (↥H ⧸ Nc)).comap π).map H.subtype with hP
    have hcP : cW ≤ P := fun c hc =>
      ⟨⟨c, hcH hc⟩, show π ⟨c, hcH hc⟩ ∈ Open.pCore p (↥H ⧸ Nc) by
        rw [(hπ1 _).mpr hc]; exact one_mem _, rfl⟩
    have hPH : P ≤ H := Subgroup.map_subtype_le _
    have hPn : H ≤ Subgroup.normalizer (P : Set G) := by
      intro h hh
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨n', hn', rfl⟩ := hn
      refine ⟨⟨h, hh⟩ * n' * (⟨h, hh⟩ : ↥H)⁻¹, ?_, rfl⟩
      show π (⟨h, hh⟩ * n' * (⟨h, hh⟩ : ↥H)⁻¹) ∈ Open.pCore p (↥H ⧸ Nc)
      rw [map_mul, map_mul, map_inv]
      exact (LieType.BorelTits.pCore_normal p (G := ↥H ⧸ Nc)).conj_mem _ hn' _
    have hPp : ∀ g ∈ P, ∃ k : ℕ, g ^ p ^ k ∈ cW := by
      rintro _ ⟨g', hg', rfl⟩
      obtain ⟨k, hk⟩ := (LieType.BorelTits.pCore_isPGroup (r := p) (G := ↥H ⧸ Nc)) ⟨_, hg'⟩
      refine ⟨k, ?_⟩
      have h1 : π (g' ^ p ^ k) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val hk
      have := (hπ1 _).mp h1
      simpa using this
    have hc := hcoreC p hp hp5 P hcP hPH hPn hPp
    obtain ⟨g', rfl⟩ := hπs a
    obtain ⟨x', hx', rfl⟩ := hx
    have hgP : (g' : G) ∈ P := ⟨g', ha, rfl⟩
    have h1 := hc _ hgP _ hx'
    have h2 : π ⁅g', x'⁆ = 1 := by
      rw [hπ1]
      refine ⟨H.mul_mem (H.mul_mem (H.mul_mem g'.2 x'.2) (H.inv_mem g'.2)) (H.inv_mem x'.2), ?_⟩
      exact h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  have hL : twoResidual (((xL L V₂ ⊔ T).subgroupOf H).map π) ≤
      Subgroup.centralizer (opResidual 3 (genFittingFitting (↥H ⧸ Nc)) : Set (↥H ⧸ Nc)) := by
    refine (twoResidual_le_of_pow_mem ?_ ?_ ?_).trans (le_centralizer_opResidual hO2 hXcen)
    · exact Subgroup.map_mono fun x hx => Subgroup.mem_sup_left hx
    · rintro _ ⟨g, hg, rfl⟩
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨x, hx, rfl⟩ := hn
      refine ⟨g * x * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp (hXTn hg) x).mp hx
    · rintro _ ⟨g, hg, rfl⟩
      have hgXT : (g : G) ∈ ((xL L V₂ : Set G) * (T : Set G)) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTX]
        exact hg
      obtain ⟨x, hx, t, ht, hxt⟩ := hgXT
      obtain ⟨a, ha⟩ := C.isSylowTwoOf_T_F4 (K := T) le_rfl |>.2.1 ⟨t, ht⟩
      have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
      obtain ⟨x', hx', he⟩ := pow_mul_eq_of_normalizes hx (hTX ht) (2 ^ a)
      rw [hta, mul_one] at he
      refine ⟨a, ⟨g ^ 2 ^ a, ?_, by rw [map_pow]⟩⟩
      show ((g ^ 2 ^ a : ↥H) : G) ∈ xL L V₂
      rw [SubgroupClass.coe_pow, ← hxt, he]
      exact hx'
  have hr : Open.pRank 3 (⊤ : Subgroup ↥H) ≤ 2 :=
    stronglyQuasithin_of_pCoreOf_ne_bot C.hyp.fsu.qtke hQ 3 Nat.prime_three (by norm_num)
  have hsolvD : Group.IsSolvable (↥H ⧸ Nc) := by
    have := hsolv
    infer_instance
  have h23 := fun q hq hqd =>
    F6.prime_eq_two_or_three_of_pRank_le_two hGD hsolvD π hπs hr (Or.inr hL) (q := q) hq hqd
  set K := CFSG.pPrimeCore 3 ↥H with hK
  have hKn : K.Normal := CFSG.pPrimeCore_normal
  have hKc : Nat.Coprime 3 (Nat.card K) := CFSG.pPrimeCore_coprime_card
  refine hred.2.2.2 _ (Subgroup.map_subtype_le _) ?_ ?_
  · intro h hh
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨n', hn', rfl⟩ := hn
    exact ⟨⟨h, hh⟩ * n' * (⟨h, hh⟩ : ↥H)⁻¹, hKn.conj_mem _ hn' _, rfl⟩
  · rintro _ ⟨d, hd, rfl⟩
    set m := orderOf (π d) with hm
    have hm0 : m ≠ 0 := (orderOf_pos _).ne'
    have hmd : m ∣ orderOf d := orderOf_map_dvd π d
    have hdK : orderOf d ∣ Nat.card K := by
      have := orderOf_dvd_natCard (⟨d, hd⟩ : ↥K)
      rwa [Subgroup.orderOf_mk] at this
    have hm2 : ∀ {q : ℕ}, q.Prime → q ∣ m → q = 2 := by
      intro q hq hqm
      rcases h23 q hq ((hqm.trans (orderOf_dvd_natCard (π d)))) with h | h
      · exact h
      · subst h
        exact absurd (Nat.Coprime.coprime_dvd_right (hqm.trans (hmd.trans hdK)) hKc)
          (by norm_num)
    have hm' : m = 2 ^ m.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd hm0 hm2
    refine ⟨m.primeFactorsList.length, hcW _ ?_⟩
    have h1 : π (d ^ 2 ^ m.primeFactorsList.length) = 1 := by
      rw [map_pow, ← hm', hm, pow_orderOf_eq_one]
    have := (hπ1 _).mp h1
    simpa using this

end CFSG.Quasithin.H13.L32A.T53

end
