module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop126b
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MCover
public import CFSG.RankThree.PartTwo.Sec18.Tools

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims126b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

section Derived

variable {G : Type} [Group G]

theorem dinf_le (H : Subgroup G) : derivedInf H ≤ H := by
  intro x hx
  have h0 := (Subgroup.mem_iInf.1 hx) 0
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 h0
  exact y.2

theorem conj_mem_dinf {H : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (H : Set G)) {x : G} (hx : x ∈ derivedInf H) :
    b * x * b⁻¹ ∈ derivedInf H := by
  let σ : ↥H →* ↥H := (H.normalizerMonoidHom ⟨b, hb⟩ : MulAut ↥H).toMonoidHom
  have hσ : ∀ y : ↥H, ((σ y : ↥H) : G) = b * (y : G) * b⁻¹ := fun y => rfl
  rw [derivedInf, Subgroup.mem_iInf] at hx ⊢
  intro n
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hx n)
  refine Subgroup.mem_map.2 ⟨σ y, map_derivedSeries_le_derivedSeries σ n
    (Subgroup.mem_map_of_mem σ hy), ?_⟩
  rw [← hyx]
  exact hσ y

theorem mem_normalizer_dinf {H : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (H : Set G)) :
    b ∈ Subgroup.normalizer ((derivedInf H : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_dinf hb hy
  · intro hy
    have hb' : b⁻¹ ∈ Subgroup.normalizer (H : Set G) := (Subgroup.normalizer (H : Set G)).inv_mem hb
    have := conj_mem_dinf hb' hy
    have e : b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y := by group
    rw [e] at this
    exact this

theorem dinf_normal (H : Subgroup G) : ((derivedInf H).subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (dinf_le H)).2 fun _ hh =>
    mem_normalizer_dinf (Subgroup.le_normalizer hh)

theorem exists_derivedSeries_eq (Γ : Type*) [Group Γ] [Finite Γ] :
    ∃ N : ℕ, ∀ n, N ≤ n → derivedSeries Γ n = derivedSeries Γ N := by
  have hanti : ∀ n, Nat.card (derivedSeries Γ (n + 1)) ≤ Nat.card (derivedSeries Γ n) :=
    fun n => Subgroup.card_le_of_le (derivedSeries_antitone Γ (Nat.le_succ n))
  obtain ⟨N, hN⟩ : ∃ N, Nat.card (derivedSeries Γ (N + 1)) = Nat.card (derivedSeries Γ N) := by
    by_contra h
    push Not at h
    have hlt : ∀ n, Nat.card (derivedSeries Γ n) + n ≤ Nat.card (derivedSeries Γ 0) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have := lt_of_le_of_ne (hanti n) (h n)
        omega
    have := hlt (Nat.card (derivedSeries Γ 0) + 1)
    omega
  have hEq : derivedSeries Γ (N + 1) = derivedSeries Γ N :=
    Subgroup.eq_of_le_of_card_ge (derivedSeries_antitone Γ (Nat.le_succ N)) hN.ge
  refine ⟨N, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [derivedSeries_succ, ih, ← derivedSeries_succ, hEq]

variable [Finite G]

theorem dinf_eq_map (H : Subgroup G) :
    ∃ N : ℕ, derivedInf H = (derivedSeries ↥H N).map H.subtype ∧
      derivedSeries ↥H (N + 1) = derivedSeries ↥H N := by
  obtain ⟨N, hN⟩ := exists_derivedSeries_eq ↥H
  refine ⟨N, le_antisymm (iInf_le _ N) (le_iInf fun n => ?_), hN (N + 1) (Nat.le_succ N)⟩
  rcases le_total n N with h | h
  · exact Subgroup.map_mono (derivedSeries_antitone ↥H h)
  · rw [hN n h]

theorem dinf_perfect (H : Subgroup G) : ⁅derivedInf H, derivedInf H⁆ = derivedInf H := by
  obtain ⟨N, hEq, hN⟩ := dinf_eq_map H
  rw [hEq, ← Subgroup.map_commutator, ← derivedSeries_succ, hN]

theorem exists_dinf_of_surjective {H : Subgroup G} {Q : Type*} [Group Q] (f : ↥H →* Q)
    (hf : Function.Surjective f) (hQ : commutator Q = ⊤) (q : Q) :
    ∃ c : ↥H, (c : G) ∈ derivedInf H ∧ f c = q := by
  have htop : ∀ n, derivedSeries Q n = ⊤ := by
    intro n
    induction n with
    | zero => exact derivedSeries_zero Q
    | succ n ih => rw [derivedSeries_succ, ih]; exact hQ
  obtain ⟨N, hEq, -⟩ := dinf_eq_map H
  have hq : q ∈ (derivedSeries ↥H N).map f := by
    rw [map_derivedSeries_eq hf, htop N]
    exact Subgroup.mem_top q
  obtain ⟨c, hc, rfl⟩ := hq
  refine ⟨c, ?_, rfl⟩
  rw [hEq]
  exact Subgroup.mem_map_of_mem _ hc

end Derived

section Small

variable {G : Type} [Group G]

theorem eq_bot_of_perfect_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {S : Subgroup G}
    (hS : IsPGroup p ↥S) (hperf : ⁅S, S⁆ = S) : S = ⊥ := by
  haveI := hS.isNilpotent
  have hcomm : commutator ↥S = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hperf)
  by_contra hne
  haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).2 hne
  have := IsSolvable.commutator_lt_top_of_nontrivial ↥S
  rw [hcomm] at this
  exact lt_irrefl _ this

theorem mem_normalizer_iSup {ι : Sort*} (K : ι → Subgroup G) {g : G}
    (hg : ∀ i, g ∈ Subgroup.normalizer ((K i : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (((⨆ i, K i : Subgroup G)) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  unfold GLBConj
  rw [Subgroup.map_iSup]
  refine iSup_congr fun i => ?_
  have := mem_normalizer_iff_gLBConj_eq.1 (hg i)
  exact this

theorem le_of_perfect_of_mul [Finite G] {P W T : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hT2 : IsPGroup 2 ↥T) (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hdec : ∀ x ∈ P, ∃ w ∈ W, w⁻¹ * x ∈ T) : P ≤ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := Subgroup.normalizer (W : Set G) with hNdef
  have hWN : W ≤ N := Subgroup.le_normalizer
  have hPN : P ≤ N := by
    intro x hx
    obtain ⟨w, hw, ht⟩ := hdec x hx
    have : x = w * (w⁻¹ * x) := by group
    rw [this]
    exact N.mul_mem (hWN hw) (hTW ht)
  haveI hWn : (W.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWN).2 le_rfl
  let q : ↥N →* ↥N ⧸ W.subgroupOf N := QuotientGroup.mk' (W.subgroupOf N)
  set Pq : Subgroup (↥N ⧸ W.subgroupOf N) := (P.subgroupOf N).map q with hPq
  have hPperf : ⁅Pq, Pq⁆ = Pq := by
    have h1 : ⁅P.subgroupOf N, P.subgroupOf N⁆ = P.subgroupOf N := by
      apply Subgroup.map_injective N.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPN]
      exact hP
    rw [hPq, ← Subgroup.map_commutator, h1]
  have hPT : Pq ≤ (T.subgroupOf N).map q := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, hw, ht⟩ := hdec (x : G) (Subgroup.mem_subgroupOf.1 hx)
    refine ⟨⟨w⁻¹ * (x : G), hTW ht⟩, Subgroup.mem_subgroupOf.2 ht, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hxN : ((x : G))⁻¹ ∈ Subgroup.normalizer (W : Set G) := N.inv_mem x.2
    have hc := (Subgroup.mem_normalizer_iff.1 hxN w).1 hw
    rw [show (w⁻¹ * (x : G))⁻¹ * (x : G) = (x : G)⁻¹ * w * (x : G)⁻¹⁻¹ by group]
    exact hc
  have hT2' : IsPGroup 2 ↥((T.subgroupOf N).map q) :=
    (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTW).symm).map q
  have hbot : Pq = ⊥ := eq_bot_of_perfect_of_isPGroup (hT2'.to_le hPT) hPperf
  intro x hx
  have hxq : q ⟨x, hPN hx⟩ ∈ Pq := ⟨⟨x, hPN hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hxq
  have := (QuotientGroup.eq_one_iff _).1 hxq
  exact Subgroup.mem_subgroupOf.1 this

theorem pCoreOf_two_le_primeCoreOf_three [Finite G] (Y : Subgroup G) :
    pCoreOf 2 Y ≤ GLAPPrimeCoreOf 3 Y := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, Prop126b.pCore_two_le_primeCore_three ↥Y hy, rfl⟩

end Small

section Comp

variable {G : Type} [Group G] [Finite G]

theorem isTwoPrimeComp_of {V K : Subgroup G} (hKV : K ≤ V) (hsn : IsSubnormal K V)
    (hperf : ⁅K, K⁆ = K) (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    IsTwoPrimeComp V K := by
  refine ⟨hKV, hsn, hperf, le_top, ?_, ?_⟩
  · have h1 := isSubnormal_map' (QuotientGroup.mk' (CFSG.pCore 2 ↥V))
      (isSubnormal_comap' V.subtype hsn)
    rw [show V.comap V.subtype = ⊤ from Subgroup.subgroupOf_self V,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
    exact h1
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivTwoImage hKV hsn) hq

theorem quasisimple_of_twoPrimeComp {X J : Subgroup G} (hJ : IsTwoPrimeComp X J) :
    CFSG.Open.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) :=
  CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    (quotEquivTwoImage hJ.1 hJ.2.1).symm hJ.2.2.2.2.2

theorem primeCoreOf_le_normalizer {p : ℕ} {V K : Subgroup G} (hK : GLAPComponent p V K) :
    GLAPPrimeCoreOf p V ≤ Subgroup.normalizer (K : Set G) := by
  have hP : GLAPPrimeCoreOf p V ≤ preimBarX p V K := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    show QuotientGroup.mk' (GLAPPrimeCore p ↥V) n ∈ barX p V K
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥V) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [h1]
    exact Subgroup.one_mem _
  exact hP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX p hK.1)).1
    (glaPComponent_normal_preimBarX hK))

theorem isSubnormal_iSup_glaPComponent {p : ℕ} {V : Subgroup G} {ι : Type*} (K : ι → Subgroup G)
    (hK : ∀ i, GLAPComponent p V (K i)) : IsSubnormal (⨆ i, K i) V := by
  set W : Subgroup G := ⨆ i, K i with hWdef
  set 𝒜 : Set (Subgroup (↥V ⧸ GLAPPrimeCore p ↥V)) := Set.range fun i => barX p V (K i) with h𝒜def
  have h𝒜 : ∀ A ∈ 𝒜, IsComponentOf A ⊤ := by
    rintro _ ⟨i, rfl⟩
    exact (hK i).2.2.1
  have hsn := isSubnormal_iSup_components 𝒜 h𝒜
  set Wb : Subgroup (↥V ⧸ GLAPPrimeCore p ↥V) := ⨆ A ∈ 𝒜, A with hWb
  set U : Subgroup G := (Wb.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥V))).map V.subtype with hU
  have hUV : IsSubnormal U V := isSubnormal_preimage_barX p hsn
  have hWU : W ≤ U := by
    refine iSup_le fun i k hk => ?_
    refine ⟨⟨k, (hK i).1 hk⟩, ?_, rfl⟩
    show QuotientGroup.mk' (GLAPPrimeCore p ↥V) ⟨k, (hK i).1 hk⟩ ∈ Wb
    exact (le_iSup₂_of_le (barX p V (K i)) ⟨i, rfl⟩ le_rfl : barX p V (K i) ≤ Wb)
      ⟨⟨k, (hK i).1 hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
  have hbar : Wb ≤ barX p V W := by
    refine iSup₂_le fun A hA => ?_
    obtain ⟨i, rfl⟩ := hA
    exact barX_mono (le_iSup K i)
  have hnorm : U ≤ Subgroup.normalizer (W : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨w, hw, hwu⟩ := hbar hu
    have hwW : (w : G) ∈ W := Subgroup.mem_subgroupOf.1 hw
    have hn : w⁻¹ * u ∈ GLAPPrimeCore p ↥V := (QuotientGroup.eq).1 hwu
    have hnG : ((w⁻¹ * u : ↥V) : G) ∈ GLAPPrimeCoreOf p V := ⟨_, hn, rfl⟩
    have hnN : ((w⁻¹ * u : ↥V) : G) ∈ Subgroup.normalizer (W : Set G) :=
      mem_normalizer_iSup K fun i => primeCoreOf_le_normalizer (hK i) hnG
    have e : (u : G) = (w : G) * ((w⁻¹ * u : ↥V) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    show (u : G) ∈ _
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hwW) hnN
  exact IsSubnormal.step hWU ((Subgroup.normal_subgroupOf_iff_le_normalizer hWU).2 hnorm) hUV

theorem mem_normalizer_of_comm {X K : Subgroup G} {z : G} (hK : GLAPComponent 3 X K)
    (hzX : z ∈ X) (hc : ∀ k ∈ K, z * k * z⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 X) :
    z ∈ Subgroup.normalizer (K : Set G) := by
  have hX : GLBConj z X = X := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hzX)
  have hK' : GLAPComponent 3 X (GLBConj z K) := by
    have := glaPComponent_gLBConj hK z
    rwa [hX] at this
  have hO : X ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 X : Set G) := le_normalizer_glaPPrimeCoreOf 3 X
  have hbar : barX 3 X (GLBConj z K) = barX 3 X K := by
    refine le_antisymm (barX_le_of_forall hK.1 fun k hk => ?_)
      (barX_le_of_forall hK'.1 fun k hk => ?_)
    · have hk0 : z * k * z⁻¹ ∈ K := mem_gLBConj.1 hk
      refine ⟨z * k * z⁻¹, hk0, ?_⟩
      have h1 := hc _ (K.inv_mem hk0)
      have h2 : z⁻¹ * (z * (z * k * z⁻¹)⁻¹ * z⁻¹ * (z * k * z⁻¹)⁻¹⁻¹) * z⁻¹⁻¹ ∈
          GLAPPrimeCoreOf 3 X := (Subgroup.mem_normalizer_iff.1 (hO (X.inv_mem hzX)) _).1 h1
      have e : (z * k * z⁻¹)⁻¹ * k = z⁻¹ * (z * (z * k * z⁻¹)⁻¹ * z⁻¹ * (z * k * z⁻¹)⁻¹⁻¹) * z⁻¹⁻¹ := by
        group
      rw [e]
      exact h2
    · refine ⟨z⁻¹ * k * z, mem_gLBConj.2 (by rw [show z * (z⁻¹ * k * z) * z⁻¹ = k by group]; exact hk), ?_⟩
      have h1 := hc _ (K.inv_mem hk)
      have h3 : z⁻¹ * (z * k⁻¹ * z⁻¹ * k⁻¹⁻¹) * z⁻¹⁻¹ ∈ GLAPPrimeCoreOf 3 X :=
        (Subgroup.mem_normalizer_iff.1 (hO (X.inv_mem hzX)) _).1 h1
      have e : (z⁻¹ * k * z)⁻¹ * k = (z⁻¹ * (z * k⁻¹ * z⁻¹ * k⁻¹⁻¹) * z⁻¹⁻¹)⁻¹ := by
        group
      rw [e]
      exact (GLAPPrimeCoreOf 3 X).inv_mem h3
  exact mem_normalizer_iff_gLBConj_eq.2 (glaPComponent_unique hK' hK hbar)

end Comp

section ZRed

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_pCoreOf_two (J : Subgroup G) : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 J) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J).exists_card_eq
  rw [hk]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (Nat.Coprime.pow_right k (by norm_num))

theorem exists_cent_cover {J : Subgroup G} {z : G} (hz : IsPGroup 3 ↥(Subgroup.zpowers z))
    (hzJ : z ∈ Subgroup.normalizer (J : Set G))
    (hc : ∀ j ∈ J, z * j * z⁻¹ * j⁻¹ ∈ pCoreOf 2 J) {j : G} (hj : j ∈ J) :
    ∃ c ∈ J ⊓ Cg z, c⁻¹ * j ∈ pCoreOf 2 J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzV : z ∈ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J hzJ
  have hjV : j ∈ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J hj
  obtain ⟨v, hv, hjv⟩ := exists_mul_mem_centralizer hz (not_three_dvd_pCoreOf_two J) hzV hjV (hc j hj)
  have hvJ : v ∈ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J hv
  refine ⟨j * v, ⟨J.mul_mem hj hvJ, hjv⟩, ?_⟩
  rw [show (j * v)⁻¹ * j = v⁻¹ by group]
  exact (pCoreOf 2 J).inv_mem hv

theorem commutator_quotient_eq_top {Γ : Type*} [Group Γ] (hΓ : commutator Γ = ⊤) (N : Subgroup Γ)
    [N.Normal] : commutator (Γ ⧸ N) = ⊤ := by
  have h1 : (commutator Γ).map (QuotientGroup.mk' N) = commutator (Γ ⧸ N) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  rw [← h1, hΓ, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

theorem exists_dinf_cover {J : Subgroup G} {z : G} (hJp : ⁅J, J⁆ = J)
    (hz : IsPGroup 3 ↥(Subgroup.zpowers z)) (hzJ : z ∈ Subgroup.normalizer (J : Set G))
    (hc : ∀ j ∈ J, z * j * z⁻¹ * j⁻¹ ∈ pCoreOf 2 J) {j : G} (hj : j ∈ J) :
    ∃ j₀ ∈ derivedInf (J ⊓ Cg z), j₀⁻¹ * j ∈ pCoreOf 2 J := by
  have hCJ : J ⊓ Cg z ≤ J := inf_le_left
  let f : ↥(J ⊓ Cg z) →* ↥J ⧸ CFSG.pCore 2 ↥J :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥J)).comp (Subgroup.inclusion hCJ)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨⟨j', hj'⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥J) q
    obtain ⟨c, hc', hcj⟩ := exists_cent_cover hz hzJ hc hj'
    refine ⟨⟨c, hc'⟩, ?_⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥J) (Subgroup.inclusion hCJ ⟨c, hc'⟩) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥J) ⟨j', hj'⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact (mem_pCore_two_iff _).2 hcj
  have hQ : commutator (↥J ⧸ CFSG.pCore 2 ↥J) = ⊤ :=
    commutator_quotient_eq_top (Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hJp)) _
  obtain ⟨c, hcD, hcf⟩ := exists_dinf_of_surjective f hf hQ
    (QuotientGroup.mk' (CFSG.pCore 2 ↥J) ⟨j, hj⟩)
  refine ⟨c, hcD, ?_⟩
  have hcf' : QuotientGroup.mk' (CFSG.pCore 2 ↥J) (Subgroup.inclusion hCJ c) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥J) ⟨j, hj⟩ := hcf
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcf'
  have := (mem_pCore_two_iff _).1 hcf'
  simpa using this

theorem dinf_quot_equiv {J : Subgroup G} {z : G} (hJp : ⁅J, J⁆ = J)
    (hz : IsPGroup 3 ↥(Subgroup.zpowers z)) (hzJ : z ∈ Subgroup.normalizer (J : Set G))
    (hc : ∀ j ∈ J, z * j * z⁻¹ * j⁻¹ ∈ pCoreOf 2 J) :
    Nonempty ((↥(derivedInf (J ⊓ Cg z)) ⧸ CFSG.pCore 2 ↥(derivedInf (J ⊓ Cg z))) ≃*
      (↥J ⧸ CFSG.pCore 2 ↥J)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J₀ : Subgroup G := derivedInf (J ⊓ Cg z) with hJ₀def
  have hJ₀J : J₀ ≤ J := (dinf_le _).trans inf_le_left
  let f : ↥J₀ →* ↥J ⧸ CFSG.pCore 2 ↥J :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥J)).comp (Subgroup.inclusion hJ₀J)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨⟨j, hj⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥J) q
    obtain ⟨j₀, hj₀, hj₀j⟩ := exists_dinf_cover hJp hz hzJ hc hj
    refine ⟨⟨j₀, hj₀⟩, ?_⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥J) (Subgroup.inclusion hJ₀J ⟨j₀, hj₀⟩) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥J) ⟨j, hj⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact (mem_pCore_two_iff _).2 hj₀j
  have hker : f.ker = CFSG.pCore 2 ↥J₀ := by
    apply le_antisymm
    · refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker f) ?_
      have hmem : ∀ x : ↥f.ker, Subgroup.inclusion hJ₀J (x : ↥J₀) ∈ CFSG.pCore 2 ↥J := by
        intro x
        have h1 : f x = 1 := x.2
        exact (QuotientGroup.eq_one_iff _).1 h1
      let φ : ↥f.ker →* ↥(CFSG.pCore 2 ↥J) :=
        ((Subgroup.inclusion hJ₀J).comp f.ker.subtype).codRestrict _ hmem
      have hφ : Function.Injective φ := by
        intro a b hab
        have h2 : (((a : ↥J₀) : G)) = ((b : ↥J₀) : G) :=
          congrArg (fun x : ↥(CFSG.pCore 2 ↥J) => ((x : ↥J) : G)) hab
        exact Subtype.ext (Subtype.ext h2)
      exact (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥J)).of_injective φ hφ
    · have h1 : (CFSG.pCore 2 ↥J₀).map f ≤ CFSG.pCore 2 (↥J ⧸ CFSG.pCore 2 ↥J) :=
        CFSG.LieType.BorelTits.map_pCore_le 2 f hf
      rw [CFSG.RankThree.PartTwo.Sec18.pCore_quotient_pCore_eq_bot] at h1
      intro x hx
      exact Subgroup.mem_bot.1 (h1 ⟨x, hx, rfl⟩)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem dinf_subnormal {X J : Subgroup G} (hJX : IsSubnormal J X) (z : G) :
    IsSubnormal (derivedInf (J ⊓ Cg z)) (X ⊓ Cg z) :=
  IsSubnormal.step (dinf_le _) (dinf_normal _) (isSubnormal_inf hJX (Cg z))

theorem dinf_isTwoPrimeComp {X J : Subgroup G} (hJ : IsTwoPrimeComp X J) {z : G}
    (hz : IsPGroup 3 ↥(Subgroup.zpowers z)) (hzJ : z ∈ Subgroup.normalizer (J : Set G))
    (hc : ∀ j ∈ J, z * j * z⁻¹ * j⁻¹ ∈ pCoreOf 2 J) :
    IsTwoPrimeComp (X ⊓ Cg z) (derivedInf (J ⊓ Cg z)) := by
  obtain ⟨e⟩ := dinf_quot_equiv hJ.2.2.1 hz hzJ hc
  refine isTwoPrimeComp_of ((dinf_le _).trans (inf_le_inf_right _ hJ.1)) (dinf_subnormal hJ.2.1 z)
    (dinf_perfect _) ?_
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm
    (quasisimple_of_twoPrimeComp hJ)

theorem norm_comm_of_comm {M X J : Subgroup G} (hXM : X ≤ M) (hJ : IsTwoPrimeComp X J)
    (h3 : 3 ∣ Nat.card ↥J) {z : G} (hzX : z ∈ X)
    (hcM : ∀ x ∈ J, z * x * z⁻¹ * x⁻¹ ∈ pCoreOf 2 M) :
    z ∈ Subgroup.normalizer (J : Set G) ∧ ∀ j ∈ J, z * j * z⁻¹ * j⁻¹ ∈ pCoreOf 2 J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ3 : GLAPComponent 3 X J :=
    Prop126b.glaPComponent_of_twoPrimeComp hJ (IsSubnormal.refl X) h3
  have hJX : J ≤ X := hJ.1
  have hMX : pCoreOf 2 M ⊓ X ≤ pCoreOf 2 X := by
    have := pCoreOf_inf_le (r := 2) M X
    rwa [inf_eq_right.2 hXM] at this
  have hzN : z ∈ Subgroup.normalizer (J : Set G) := by
    refine mem_normalizer_of_comm hJ3 hzX fun k hk => ?_
    have hkX : k ∈ X := hJX hk
    refine pCoreOf_two_le_primeCoreOf_three X (hMX ⟨hcM k hk, ?_⟩)
    exact X.mul_mem (X.mul_mem (X.mul_mem hzX hkX) (X.inv_mem hzX)) (X.inv_mem hkX)
  refine ⟨hzN, fun j hj => ?_⟩
  have hJ' : pCoreOf 2 M ⊓ J ≤ pCoreOf 2 J := by
    have := pCoreOf_inf_le (r := 2) M J
    rwa [inf_eq_right.2 (hJX.trans hXM)] at this
  refine hJ' ⟨hcM j hj, ?_⟩
  have hzj : z * j * z⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hzN j).1 hj
  exact J.mul_mem hzj (J.inv_mem hj)

end ZRed

section Lset

variable {G : Type} [Group G] [Finite G]

@[expose] def Lset (M : Subgroup G) : Set (Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  (fun J' : Subgroup G => (J'.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) ''
    {J' | JPred 3 M J'}

theorem pCoreOf_subgroupOf_eq (M : Subgroup G) : (pCoreOf 2 M).subgroupOf M = CFSG.pCore 2 ↥M := by
  show (Subgroup.map M.subtype (CFSG.Open.pCore 2 ↥M)).comap M.subtype = CFSG.pCore 2 ↥M
  rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

theorem mk_eq_one_iff (M : Subgroup G) (x : ↥M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) x = 1 ↔ (x : G) ∈ pCoreOf 2 M := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf_eq,
    Subgroup.mem_subgroupOf]

theorem ldata (M : Subgroup G) : LData (Lset M) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨J', hJ', rfl⟩
    obtain ⟨-, hJ'M, hsn, -, hhat⟩ := hJ'
    refine ⟨le_top, ?_, ?_⟩
    · have h1 := isSubnormal_comap' M.subtype hsn
      rw [show M.comap M.subtype = ⊤ from Subgroup.subgroupOf_self M] at h1
      have h2 := isSubnormal_map' (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) h1
      rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
    · have e1 := quotEquivTwoImage hJ'M hsn
      obtain ⟨f⟩ := hhat.2.2
      have hq : CFSG.Open.IsQuasisimple (↥J' ⧸ CFSG.pCore 2 ↥J') :=
        ⟨hhat.1, f.isSimpleGroup_congr.2 S7.isSimple_Alt7⟩
      exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e1 hq
  · rintro _ ⟨J', hJ', rfl⟩
    obtain ⟨-, hJ'M, hsn, -, hhat⟩ := hJ'
    exact nonempty_quot_center_alt7_of_equiv (quotEquivTwoImage hJ'M hsn) (Or.inr hhat)

theorem conj_mem_Lset (M : Subgroup G) {b : G} (hbM : b ∈ M) :
    ∀ L ∈ Lset M, L.map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩)).toMonoidHom ∈
      Lset M := by
  set π : ↥M →* ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  rintro _ ⟨J', hJ', rfl⟩
  refine ⟨GLBConj b⁻¹ J', JPred.gLBConj hJ' (M.inv_mem hbM), ?_⟩
  show ((GLBConj b⁻¹ J').subgroupOf M).map π = ((J'.subgroupOf M).map π).map _
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : b⁻¹ * (y : G) * b⁻¹⁻¹ ∈ J' := (mem_gLBConj).1 ((Subgroup.mem_subgroupOf).1 hy)
    refine ⟨π ⟨b⁻¹ * (y : G) * b⁻¹⁻¹, M.mul_mem (M.mul_mem (M.inv_mem hbM) y.2)
      (M.inv_mem (M.inv_mem hbM))⟩, ⟨_, (Subgroup.mem_subgroupOf).2 hy', rfl⟩, ?_⟩
    show π ⟨b, hbM⟩ * π ⟨b⁻¹ * (y : G) * b⁻¹⁻¹, _⟩ * (π ⟨b, hbM⟩)⁻¹ = π y
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show b * (b⁻¹ * (y : G) * b⁻¹⁻¹) * b⁻¹ = y
    group
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' : (w : G) ∈ J' := (Subgroup.mem_subgroupOf).1 hw
    refine ⟨⟨b * (w : G) * b⁻¹, M.mul_mem (M.mul_mem hbM w.2) (M.inv_mem hbM)⟩, ?_, ?_⟩
    · refine (Subgroup.mem_subgroupOf).2 ((mem_gLBConj).2 ?_)
      have : b⁻¹ * (b * (w : G) * b⁻¹) * b⁻¹⁻¹ = w := by group
      rw [this]
      exact hw'
    · show π ⟨b * (w : G) * b⁻¹, _⟩ = π ⟨b, hbM⟩ * π w * (π ⟨b, hbM⟩)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      try rfl

theorem le_alphaOf_of_JPred {M J' : Subgroup G} (hJ' : JPred 3 M J') : J' ≤ alphaOf 3 M := by
  unfold alphaOf
  exact le_sup_of_le_right (le_iSup₂_of_le J' hJ' le_rfl)

theorem alpha_le_sSup (M : Subgroup G) :
    ((alphaOf 3 M).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ≤ sSup (Lset M) := by
  have hα : alphaOf 3 M = pCoreOf 2 M ⊔ ⨆ x : {J' : Subgroup G // JPred 3 M J'}, x.1 := by
    unfold alphaOf
    rw [iSup_subtype']
    try rfl
  have hle1 : (⨆ x : {J' : Subgroup G // JPred 3 M J'}, x.1) ≤ M :=
    iSup_le fun x => x.2.2.1
  have hle2 : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  rw [hα, Subgroup.subgroupOf_sup hle2 hle1, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [pCoreOf_subgroupOf_eq]
    exact (QuotientGroup.map_mk'_self _).le.trans bot_le
  · refine le_trans (Subgroup.map_mono (subgroupOf_iSup_le _ fun x => x.2.2.1)) ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun x => le_sSup ⟨x.1, x.2, rfl⟩

theorem sSup_le_alpha (M : Subgroup G) :
    sSup (Lset M) ≤ ((alphaOf 3 M).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
  refine sSup_le ?_
  rintro _ ⟨J', hJ', rfl⟩
  refine Subgroup.map_mono ?_
  intro w hw
  exact (Subgroup.mem_subgroupOf).2 (le_alphaOf_of_JPred hJ' ((Subgroup.mem_subgroupOf).1 hw))

theorem sSup_inf_centralizer (M : Subgroup G) {b : G} (hbM : b ∈ M)
    (hbz : IsPGroup 3 ↥(Subgroup.zpowers b)) :
    sSup (Lset M) ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) =
      ((alphaOf 3 M ⊓ Cg b).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : ↥M →* ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  set bt := π ⟨b, hbM⟩ with hbt
  refine le_antisymm ?_ ?_
  · rintro z ⟨hzE, hzC⟩
    obtain ⟨y, hy, rfl⟩ := sSup_le_alpha M hzE
    have hyα : (y : G) ∈ alphaOf 3 M := (Subgroup.mem_subgroupOf).1 hy
    have hcomm : π y * bt = bt * π y := Subgroup.mem_centralizer_singleton_iff.1 hzC
    have hc0 : π (⟨b, hbM⟩ * y * ⟨b, hbM⟩⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hbt]
      have : bt * π y = π y * bt := hcomm.symm
      rw [this]
      group
    have hc0V : b * (y : G) * b⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 M := (mk_eq_one_iff M _).1 hc0
    have hVp : ¬ 3 ∣ Nat.card (pCoreOf 2 M) := not_three_dvd_pCoreOf_two M
    obtain ⟨v, hv, hxv⟩ := exists_mul_mem_centralizer (p := 3) (d := b) (x := (y : G))
      (V := pCoreOf 2 M) hbz hVp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hbM)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M y.2) hc0V
    have hvM : v ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hv
    have hVα : pCoreOf 2 M ≤ alphaOf 3 M := by
      unfold alphaOf
      exact le_sup_left
    have hyvX : (y : G) * v ∈ alphaOf 3 M ⊓ Cg b := ⟨(alphaOf 3 M).mul_mem hyα (hVα hv), hxv⟩
    refine ⟨⟨(y : G) * v, M.mul_mem y.2 hvM⟩, (Subgroup.mem_subgroupOf).2 hyvX, ?_⟩
    have : (⟨(y : G) * v, M.mul_mem y.2 hvM⟩ : ↥M) = y * ⟨v, hvM⟩ := Subtype.ext rfl
    have hπv : π ⟨v, hvM⟩ = 1 := (mk_eq_one_iff M _).2 hv
    rw [this, map_mul, hπv, mul_one]
  · rintro _ ⟨y, hy, rfl⟩
    have hyX : (y : G) ∈ alphaOf 3 M ⊓ Cg b := (Subgroup.mem_subgroupOf).1 hy
    refine ⟨alpha_le_sSup M ⟨y, (Subgroup.mem_subgroupOf).2 hyX.1, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [hbt, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 hyX.2

theorem typeWeak_gen {M : Subgroup G} {b : G} (hbM : b ∈ M) (hb3 : b ^ 3 = 1) {J : Subgroup G}
    (hJX : IsTwoPrimeComp (alphaOf 3 M ⊓ Cg b) J) :
    Nonempty (((↥J ⧸ CFSG.pCore 2 ↥J) ⧸ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) ≃* ↥S7.Alt7) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := alphaOf 3 M ⊓ Cg b with hX
  have hJle : J ≤ X := hJX.1
  have hJM : J ≤ M := hJle.trans (inf_le_left.trans (alphaOf_le 3 M))
  set N : Subgroup ↥M := CFSG.pCore 2 ↥M with hN
  set π : ↥M →* ↥M ⧸ N := QuotientGroup.mk' N with hπ
  set bt : ↥M ⧸ N := π ⟨b, hbM⟩ with hbt
  have hbt3 : bt ^ 3 = 1 := by
    rw [hbt, ← map_pow]
    have : (⟨b, hbM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  set ι : ↥J →* ↥M ⧸ N := π.comp (Subgroup.inclusion hJM) with hι
  have hιr : ι.range = (J.subgroupOf M).map π := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j, hJM j.2⟩, (Subgroup.mem_subgroupOf).2 j.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, (Subgroup.mem_subgroupOf).1 hy⟩, rfl⟩
  have hJα : J ≤ alphaOf 3 M := hJle.trans inf_le_left
  have hιE : ι.range ≤ sSup (Lset M) := by
    rw [hιr]
    refine le_trans (Subgroup.map_mono ?_) (alpha_le_sSup M)
    intro y hy
    exact (Subgroup.mem_subgroupOf).2 (hJα ((Subgroup.mem_subgroupOf).1 hy))
  have hιb : ι.range ≤ Subgroup.centralizer ({bt} : Set (↥M ⧸ N)) := by
    rw [hιr]
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hbt, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hyJ : (y : G) ∈ J := (Subgroup.mem_subgroupOf).1 hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hJle hyJ).2
  have hbz : IsPGroup 3 ↥(Subgroup.zpowers b) := l119_isPGroup_zpowers hb3
  have hperf : commutator ↥J = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hJX.2.2.1)
  have hO2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥J) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hker : ι.ker ≤ CFSG.pCore 2 ↥J := by
    intro j hj
    have hj1 : π ⟨(j : G), hJM j.2⟩ = 1 := hj
    have hjP : (j : G) ∈ pCoreOf 2 M := (mk_eq_one_iff M _).1 hj1
    rw [mem_pCore_two_iff]
    have := pCoreOf_inf_le (r := 2) M J ⟨hjP, j.2⟩
    rwa [inf_eq_right.2 hJM] at this
  have hq : CFSG.Open.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) := quasisimple_of_twoPrimeComp hJX
  have hsn : IsSubnormal ι.range (sSup (Lset M) ⊓ Subgroup.centralizer ({bt} : Set (↥M ⧸ N))) := by
    rw [hιr, sSup_inf_centralizer M hbM hbz]
    exact isSubnormal_map' π (isSubnormal_comap' M.subtype hJX.2.1)
  exact (ldata M).exists_equiv_alt7 hbt3 (conj_mem_Lset M hbM) ι hιE hιb hsn hperf
    (CFSG.pCore 2 ↥J) hO2 hker hq

end Lset

section Sylow3

variable {G : Type} [Group G] [Finite G]

theorem card_gLBConj' (g : G) (H : Subgroup G) : Nat.card ↥(GLBConj g H) = Nat.card ↥H := by
  unfold GLBConj
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem isSylowIn_inf_normal {X O R : Subgroup G} (hR : IsSylowIn 3 X R) (hOX : O ≤ X)
    (hXO : X ≤ Subgroup.normalizer (O : Set G)) : IsSylowIn 3 O (R ⊓ O) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨inf_le_right, hR.2.1.to_le inf_le_left, fun R' hR'O hR'p hle => ?_⟩
  obtain ⟨x, hxX, T, hTp, hTX, hRT, hR'T⟩ :=
    exists_conj_le_pGroup' hR.1 hR.2.1 (hR'O.trans hOX) hR'p
  have hTR : T = R := hR.2.2 T hTX hTp hRT
  rw [hTR] at hR'T
  have hO : GLBConj x O = O := gLBConj_eq_of_mem_normalizer (hXO hxX)
  have h1 : GLBConj x R' ≤ R ⊓ O := by
    refine le_inf hR'T ?_
    have := gLBConj_mono x hR'O
    rwa [hO] at this
  have h2 : Nat.card ↥R' ≤ Nat.card ↥(R ⊓ O) := by
    rw [← card_gLBConj' x R']
    exact Subgroup.card_le_of_le h1
  exact (Subgroup.eq_of_le_of_card_ge hle h2).symm

theorem isSylowIn_inf_of_isSubnormal {L K : Subgroup G} (hsn : IsSubnormal L K) {R : Subgroup G}
    (hR : IsSylowIn 3 K R) : IsSylowIn 3 L (R ⊓ L) := by
  revert hR
  induction hsn with
  | refl H =>
    intro hR
    rwa [inf_eq_left.2 hR.1]
  | step hHM hN _ ih =>
    intro hR
    have h1 := isSylowIn_inf_normal (ih hR) hHM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hN)
    rwa [inf_assoc, inf_eq_right.2 hHM] at h1

theorem exists_sylow_of_isSylowIn' {p : ℕ} [Fact p.Prime] {X R : Subgroup G}
    (hR : IsSylowIn p X R) : ∃ S : Sylow p ↥X, (S : Subgroup ↥X).map X.subtype = R := by
  obtain ⟨S, hS⟩ := (hR.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hR.1).symm :
    IsPGroup p ↥(R.subgroupOf X)).exists_le_sylow
  refine ⟨S, hR.2.2 _ (Subgroup.map_subtype_le _) (S.isPGroup'.map _) ?_⟩
  intro r hr
  exact ⟨⟨r, hR.1 hr⟩, hS (Subgroup.mem_subgroupOf.2 hr), rfl⟩

theorem comm_of_mem_centerOf {R : Subgroup G} {z : G} (hz : z ∈ centerOf R) {r : G} (hr : r ∈ R) :
    r * z = z * r := by
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.1 hz
  have hcr := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨r, hr⟩)
  have hc' : (c : G) = z := hcz
  have h3 : r * (c : G) = (c : G) * r := by simpa using hcr
  rw [← hc']
  exact h3

theorem mem_center_of_centralizes_sylow {K : Type*} [Group K] [Finite K] (hK : IsHatSeven K)
    (P : Sylow 3 K) {x : K} (hxP : x ∈ (P : Subgroup K))
    (hxc : ∀ y ∈ (P : Subgroup K), y * x = x * y) : x ∈ Subgroup.center K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hP27, ⟨r, hr, s, hs, hrs⟩, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.t112m_sylow_hatSeven hK P
  have hZ3 : Nat.card (Subgroup.center K) = 3 := hK.2.1
  have hZp : IsPGroup 3 ↥(Subgroup.center K) := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have hZP : Subgroup.center K ≤ (P : Subgroup K) := hZp.le_sylow_of_normal P
  by_contra hx
  set C : Subgroup K := Subgroup.center K ⊔ Subgroup.zpowers x with hC
  have hCP : C ≤ (P : Subgroup K) := sup_le hZP ((Subgroup.zpowers_le).2 hxP)
  have hxcent : x ∈ Subgroup.centralizer ((P : Subgroup K) : Set K) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => hxc y hy
  have hCc : C ≤ Subgroup.centralizer ((P : Subgroup K) : Set K) :=
    sup_le (Subgroup.center_le_centralizer _) ((Subgroup.zpowers_le).2 hxcent)
  have hCp : IsPGroup 3 ↥C := P.isPGroup'.to_le hCP
  obtain ⟨j, hj⟩ := hCp.exists_card_eq
  have h3C : 3 ∣ Nat.card ↥C := hZ3 ▸ Subgroup.card_dvd_of_le le_sup_left
  have hC3 : Nat.card ↥C ≠ 3 := by
    intro h
    apply hx
    have heq : Subgroup.center K = C :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hZ3])
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hj2 : 2 ≤ j := by
    rcases Nat.lt_or_ge j 2 with h | h
    · interval_cases j
      · rw [hj, pow_zero] at h3C
        exact absurd h3C (by norm_num)
      · rw [hj, pow_one] at hC3
        exact absurd rfl hC3
    · exact h
  have h9C : 9 ∣ Nat.card ↥C := by
    rw [hj]
    have h1 : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 hj2
    simpa using h1
  set Pz : Subgroup ↥(P : Subgroup K) := Subgroup.center ↥(P : Subgroup K) with hPz
  have hCZ : C.subgroupOf (P : Subgroup K) ≤ Pz := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.1 (hCc (Subgroup.mem_subgroupOf.1 hc)) (y : K) y.2
    simpa using this
  have hcardC : Nat.card ↥(C.subgroupOf (P : Subgroup K)) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv
  have h9Z : 9 ∣ Nat.card ↥Pz := by
    have := Subgroup.card_dvd_of_le hCZ
    rw [hcardC] at this
    exact h9C.trans this
  have hq : Nat.card (↥(P : Subgroup K) ⧸ Pz) ∣ 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Pz
    rw [hP27] at h1
    obtain ⟨t, ht⟩ := h9Z
    rw [ht] at h1
    refine ⟨t, ?_⟩
    have h27 : (27 : ℕ) = 9 * (Nat.card (↥(P : Subgroup K) ⧸ Pz) * t) := by rw [h1]; ring
    omega
  haveI : IsCyclic (↥(P : Subgroup K) ⧸ Pz) := isCyclic_of_card_dvd_prime hq
  have hab := (QuotientGroup.mk' Pz).isMulCommutative_of_isCyclic_of_ker_le_center
    (by rw [QuotientGroup.ker_mk'])
  apply hrs
  have := hab.is_comm.comm ⟨r, hr⟩ ⟨s, hs⟩
  exact congrArg Subtype.val this

end Sylow3

section Central

variable {G : Type} [Group G] [Finite G]

theorem zbar_comm_of_JPred {M R : Subgroup G} {z : G} (hR : IsSylowIn 3 M R) (hzR : z ∈ centerOf R)
    (hzα : z ∈ alphaOf 3 M) (hz3 : z ^ 3 = 1) {J' : Subgroup G} (hJ' : JPred 3 M J') (x : ↥M)
    (hx : (x : G) ∈ J') :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) x *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, alphaOf_le 3 M hzα⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, alphaOf_le 3 M hzα⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzM : z ∈ M := alphaOf_le 3 M hzα
  have hJ'0 := hJ'
  obtain ⟨-, hJ'M, hsn, -, hhat⟩ := hJ'
  set N : Subgroup ↥M := CFSG.pCore 2 ↥M with hN
  set π : ↥M →* ↥M ⧸ N := QuotientGroup.mk' N with hπ
  have hℒ : LData (Lset M) := ldata M
  set L : Subgroup (↥M ⧸ N) := (J'.subgroupOf M).map π with hLdef
  have hLℒ : L ∈ Lset M := ⟨J', hJ'0, rfl⟩
  set zb : ↥M ⧸ N := π ⟨z, hzM⟩ with hzb
  have hzbE : zb ∈ sSup (Lset M) :=
    alpha_le_sSup M ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.2 hzα, rfl⟩
  set D : Subgroup (↥M ⧸ N) := sSup (Lset M \ {L}) with hD
  have hDL : D ≤ Subgroup.centralizer (L : Set (↥M ⧸ N)) :=
    sSup_le fun L' hL' => hℒ.centralizes hL'.1 hLℒ fun h => hL'.2 (Set.mem_singleton_iff.2 h)
  have hLD : L ≤ Subgroup.centralizer (D : Set (↥M ⧸ N)) := Subgroup.le_centralizer_iff.1 hDL
  have hsSup : sSup (Lset M) ≤ L ⊔ D := by
    refine sSup_le fun L' hL' => ?_
    by_cases h : L' = L
    · rw [h]
      exact le_sup_left
    · exact le_sup_of_le_right (le_sSup ⟨hL', fun h' => h (Set.mem_singleton_iff.1 h')⟩)
  obtain ⟨ℓ, hℓ, d, hd, hzbe⟩ := exists_mul_of_mem_sup hLD (hsSup hzbE)
  have hdc : ∀ y ∈ L, y * d = d * y := fun y hy => Subgroup.mem_centralizer_iff.1 (hDL hd) y hy
  have hRJ : IsSylowIn 3 J' (R ⊓ J') := isSylowIn_inf_of_isSubnormal hsn hR
  obtain ⟨S₀, hS₀⟩ := exists_sylow_of_isSylowIn' hRJ
  have hιs : Function.Surjective (imageHom J' M hJ'M) := imageHom_surjective J' M hJ'M
  set P : Sylow 3 ↥L := S₀.mapSurjective hιs with hPdef
  have hHat : IsHatSeven ↥L := IsHatSeven.of_mulEquiv (quotEquivTwoImage hJ'M hsn) hhat
  have hzbP : ∀ q : ↥L, q ∈ (P : Subgroup ↥L) → (q : ↥M ⧸ N) * zb = zb * (q : ↥M ⧸ N) := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := hq
    have hyR : (y : G) ∈ R := by
      have : (y : G) ∈ R ⊓ J' := by
        rw [← hS₀]
        exact ⟨y, hy, rfl⟩
      exact this.1
    have hyz : (y : G) * z = z * y := comm_of_mem_centerOf hzR hyR
    show π (Subgroup.inclusion hJ'M y) * π ⟨z, hzM⟩ = π ⟨z, hzM⟩ * π (Subgroup.inclusion hJ'M y)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyz
  have hℓP : ∀ q : ↥L, q ∈ (P : Subgroup ↥L) → (q : ↥M ⧸ N) * ℓ = ℓ * (q : ↥M ⧸ N) := by
    intro q hq
    have h1 := hzbP q hq
    rw [hzbe] at h1
    have hdq : (q : ↥M ⧸ N) * d = d * q := hdc q q.2
    have h2 : ((q : ↥M ⧸ N) * ℓ) * d = (ℓ * q) * d := by
      calc ((q : ↥M ⧸ N) * ℓ) * d = (q : ↥M ⧸ N) * (ℓ * d) := by group
        _ = ℓ * d * q := h1
        _ = ℓ * (d * q) := by group
        _ = ℓ * (q * d) := by rw [hdq]
        _ = (ℓ * q) * d := by group
    exact mul_right_cancel h2
  have hzb3 : zb ^ 3 = 1 := by
    rw [hzb, ← map_pow]
    have : (⟨z, hzM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this, map_one]
  have hℓd : Commute ℓ d := hdc ℓ hℓ
  have hℓ3 : ℓ ^ 3 = (d ^ 3)⁻¹ := by
    have h1 : (ℓ * d) ^ 3 = ℓ ^ 3 * d ^ 3 := hℓd.mul_pow 3
    rw [← hzbe, hzb3] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have hℓ3L : ℓ ^ 3 ∈ L := L.pow_mem hℓ 3
  have hℓ3D : ℓ ^ 3 ∈ D := by
    rw [hℓ3]
    exact D.inv_mem (D.pow_mem hd 3)
  have hℓ3Z : (⟨ℓ ^ 3, hℓ3L⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 (hDL hℓ3D) y y.2
  set ℓ' : ↥L := ⟨ℓ, hℓ⟩ with hℓ'
  have hc3 : (⟨⟨ℓ ^ 3, hℓ3L⟩, hℓ3Z⟩ : ↥(Subgroup.center ↥L)) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(Subgroup.center ↥L)) (x := ⟨⟨ℓ ^ 3, hℓ3L⟩, hℓ3Z⟩)
    rwa [hHat.2.1] at this
  have hℓ9' : ℓ ^ 9 = 1 := by
    have h2 := congrArg (fun w : ↥(Subgroup.center ↥L) => (((w : ↥L)) : ↥M ⧸ N)) hc3
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul]
    exact h2
  have hℓ9 : ℓ' ^ (3 ^ 2) = 1 := by
    apply Subtype.ext
    simpa using hℓ9'
  have hℓp : IsPGroup 3 ↥(Subgroup.zpowers ℓ') := by
    have hdvd : orderOf ℓ' ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one hℓ9
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hℓc : ℓ' ∈ Subgroup.centralizer ((P : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subtype.ext (hℓP q hq)
  have hℓN : Subgroup.zpowers ℓ' ≤ Subgroup.normalizer ((P : Subgroup ↥L) : Set ↥L) :=
    (Subgroup.zpowers_le.2 hℓc).trans (Subgroup.centralizer_le_normalizer _)
  have hsupP := P.is_maximal' (IsPGroup.to_sup_of_normal_left' P.isPGroup' hℓp hℓN) le_sup_left
  have hℓPm : ℓ' ∈ (P : Subgroup ↥L) := by
    have : ℓ' ∈ (P : Subgroup ↥L) ⊔ Subgroup.zpowers ℓ' :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers ℓ')
    rwa [hsupP] at this
  have hℓZ : ℓ' ∈ Subgroup.center ↥L :=
    mem_center_of_centralizes_sylow hHat P hℓPm fun q hq => Subtype.ext (hℓP q hq)
  have hxL : π x ∈ L := ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  have hℓx : π x * ℓ = ℓ * π x := by
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hℓZ ⟨π x, hxL⟩)
    exact this
  rw [hzbe]
  calc π x * (ℓ * d) = (π x * ℓ) * d := by group
    _ = (ℓ * π x) * d := by rw [hℓx]
    _ = ℓ * (π x * d) := by group
    _ = ℓ * (d * π x) := by rw [hdc _ hxL]
    _ = ℓ * d * π x := by group

theorem comm_alpha {M R : Subgroup G} {z : G} (hR : IsSylowIn 3 M R) (hzR : z ∈ centerOf R)
    (hzα : z ∈ alphaOf 3 M) (hz3 : z ^ 3 = 1) {x : G} (hx : x ∈ alphaOf 3 M) :
    z * x * z⁻¹ * x⁻¹ ∈ pCoreOf 2 M := by
  have hzM : z ∈ M := alphaOf_le 3 M hzα
  have hxM : x ∈ M := alphaOf_le 3 M hx
  set π : ↥M →* ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  set zb := π ⟨z, hzM⟩ with hzb
  have hcent : sSup (Lset M) ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine sSup_le ?_
    rintro _ ⟨J', hJ', rfl⟩ _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact zbar_comm_of_JPred hR hzR hzα hz3 hJ' y (Subgroup.mem_subgroupOf.1 hy)
  have hxL : π ⟨x, hxM⟩ ∈ sSup (Lset M) :=
    alpha_le_sSup M ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  have h1 : π ⟨x, hxM⟩ * zb = zb * π ⟨x, hxM⟩ :=
    Subgroup.mem_centralizer_singleton_iff.1 (hcent hxL)
  have hmem : z * x * z⁻¹ * x⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hzM hxM) (M.inv_mem hzM)) (M.inv_mem hxM)
  have he : (⟨z * x * z⁻¹ * x⁻¹, hmem⟩ : ↥M) = ⟨z, hzM⟩ * ⟨x, hxM⟩ * ⟨z, hzM⟩⁻¹ * ⟨x, hxM⟩⁻¹ := rfl
  refine (mk_eq_one_iff M ⟨z * x * z⁻¹ * x⁻¹, hmem⟩).1 ?_
  rw [he, map_mul, map_mul, map_mul, map_inv, map_inv]
  show zb * π ⟨x, hxM⟩ * zb⁻¹ * (π ⟨x, hxM⟩)⁻¹ = 1
  rw [← h1]
  group

end Central

section Wsec

variable {G : Type} [Group G] [Finite G]

theorem isTwoPrimeComp_alpha_of_JPred {M J' : Subgroup G} (hJ' : JPred 3 M J') :
    IsTwoPrimeComp (alphaOf 3 M) J' := by
  have hJα := le_alphaOf_of_JPred hJ'
  obtain ⟨-, -, hsn, hperf, hhat⟩ := hJ'
  obtain ⟨f⟩ := hhat.2.2
  exact isTwoPrimeComp_of hJα (isSubnormal_of_le_of_le hsn hJα (alphaOf_le 3 M)) hperf
    ⟨hhat.1, f.isSimpleGroup_congr.2 S7.isSimple_Alt7⟩

theorem three_dvd_of_JPred {M J' : Subgroup G} (hJ' : JPred 3 M J') : 3 ∣ Nat.card ↥J' :=
  (Prop126b.three_dvd_of_isHatSeven hJ'.2.2.2.2).trans (Subgroup.card_quotient_dvd_card _)

theorem JPred_norm_comm {M R : Subgroup G} {z : G} (hR : IsSylowIn 3 M R) (hzR : z ∈ centerOf R)
    (hzα : z ∈ alphaOf 3 M) (hz3 : z ^ 3 = 1) {J' : Subgroup G} (hJ' : JPred 3 M J') :
    z ∈ Subgroup.normalizer (J' : Set G) ∧ ∀ j ∈ J', z * j * z⁻¹ * j⁻¹ ∈ pCoreOf 2 J' :=
  norm_comm_of_comm (alphaOf_le 3 M) (isTwoPrimeComp_alpha_of_JPred hJ') (three_dvd_of_JPred hJ')
    hzα fun x hx => comm_alpha hR hzR hzα hz3 (le_alphaOf_of_JPred hJ' hx)

@[expose] def Wz (M : Subgroup G) (z : G) : Subgroup G :=
  ⨆ x : {J' : Subgroup G // JPred 3 M J'}, derivedInf (x.1 ⊓ Cg z)

theorem Y_props {M R : Subgroup G} {z : G} (hR : IsSylowIn 3 M R) (hzR : z ∈ centerOf R)
    (hzα : z ∈ alphaOf 3 M) (hz3 : z ^ 3 = 1) {J' : Subgroup G} (hJ' : JPred 3 M J') :
    IsTwoPrimeComp (alphaOf 3 M ⊓ Cg z) (derivedInf (J' ⊓ Cg z)) ∧
      3 ∣ Nat.card ↥(derivedInf (J' ⊓ Cg z)) := by
  obtain ⟨hzN, hc⟩ := JPred_norm_comm hR hzR hzα hz3 hJ'
  have hzp : IsPGroup 3 ↥(Subgroup.zpowers z) := l119_isPGroup_zpowers hz3
  refine ⟨dinf_isTwoPrimeComp (isTwoPrimeComp_alpha_of_JPred hJ') hzp hzN hc, ?_⟩
  obtain ⟨e⟩ := dinf_quot_equiv hJ'.2.2.2.1 hzp hzN hc
  have h1 : 3 ∣ Nat.card (↥J' ⧸ CFSG.pCore 2 ↥J') := Prop126b.three_dvd_of_isHatSeven hJ'.2.2.2.2
  rw [← Nat.card_congr e.toEquiv] at h1
  exact h1.trans (Subgroup.card_quotient_dvd_card _)

theorem Wz_le (M : Subgroup G) (z : G) : Wz M z ≤ alphaOf 3 M ⊓ Cg z :=
  iSup_le fun x => (dinf_le _).trans (inf_le_inf_right _ (le_alphaOf_of_JPred x.2))

theorem Wz_subnormal {m : ℕ} {B M E A : Subgroup G} (h : Sec11 G m 3 B M E A) {R : Subgroup G}
    (hR : IsSylowIn 3 M R) {z : G} (hzR : z ∈ centerOf R) (hzα : z ∈ alphaOf 3 M) (hz3 : z ^ 3 = 1)
    (hzE : z ∈ E) (hz1 : z ≠ 1) : IsSubnormal (Wz M z) (Cg z) := by
  unfold Wz
  refine isSubnormal_iSup_glaPComponent (p := 3) _ fun x => ?_
  obtain ⟨hY, h3⟩ := Y_props hR hzR hzα hz3 x.2
  have hE : IsUniquenessTwoLocal 3 E M := h.pair.1.1.2
  have hYz : IsTwoPrimeComp (Cg z) (derivedInf (x.1 ⊓ Cg z)) := hE.clause_f rfl z hzE hz1 _ hY
  exact Prop126b.glaPComponent_of_twoPrimeComp hYz (IsSubnormal.refl _) h3

theorem le_Wz_of_perfect {M R : Subgroup G} {z : G} (hR : IsSylowIn 3 M R) (hzR : z ∈ centerOf R)
    (hzα : z ∈ alphaOf 3 M) (hz3 : z ^ 3 = 1) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPY : P ≤ alphaOf 3 M ⊓ Cg z) : P ≤ Wz M z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := alphaOf 3 M ⊓ Cg z with hYdef
  have hYM : Y ≤ M := inf_le_left.trans (alphaOf_le 3 M)
  set T : Subgroup G := pCoreOf 2 M ⊓ Y with hTdef
  have hT2 : IsPGroup 2 ↥T := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
  have hTY : T ≤ GLAPPrimeCoreOf 3 Y := by
    have := pCoreOf_inf_le (r := 2) M Y
    rw [inf_eq_right.2 hYM] at this
    exact this.trans (pCoreOf_two_le_primeCoreOf_three Y)
  have hTW : T ≤ Subgroup.normalizer (Wz M z : Set G) := by
    intro t ht
    refine mem_normalizer_iSup _ fun x => ?_
    obtain ⟨hY, h3⟩ := Y_props hR hzR hzα hz3 x.2
    exact primeCoreOf_le_normalizer
      (Prop126b.glaPComponent_of_twoPrimeComp hY (IsSubnormal.refl _) h3) (hTY ht)
  set π : ↥M →* ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  have hWM : Wz M z ≤ M := (Wz_le M z).trans (inf_le_left.trans (alphaOf_le 3 M))
  have hLW : sSup (Lset M) ≤ ((Wz M z).subgroupOf M).map π := by
    refine sSup_le ?_
    rintro _ ⟨J', hJ', rfl⟩ _ ⟨y, hy, rfl⟩
    have hyJ : (y : G) ∈ J' := Subgroup.mem_subgroupOf.1 hy
    obtain ⟨hzN, hc⟩ := JPred_norm_comm hR hzR hzα hz3 hJ'
    obtain ⟨y₀, hy₀, hy₀y⟩ :=
      exists_dinf_cover hJ'.2.2.2.1 (l119_isPGroup_zpowers hz3) hzN hc hyJ
    have hy₀W : y₀ ∈ Wz M z :=
      (le_iSup (fun x : {J' : Subgroup G // JPred 3 M J'} => derivedInf (x.1 ⊓ Cg z)) ⟨J', hJ'⟩) hy₀
    have hO : y₀⁻¹ * y ∈ pCoreOf 2 M := pCoreOf_le_of_isSubnormal 2 hJ'.2.2.1 hy₀y
    refine ⟨⟨y₀, hWM hy₀W⟩, Subgroup.mem_subgroupOf.2 hy₀W, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact (mem_pCore_two_iff _).2 hO
  refine le_of_perfect_of_mul hP hT2 hTW fun x hx => ?_
  have hxα : x ∈ alphaOf 3 M := (hPY hx).1
  have hxM : x ∈ M := alphaOf_le 3 M hxα
  obtain ⟨w, hw, hwx⟩ := hLW (alpha_le_sSup M ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hxα, rfl⟩)
  have hwW : (w : G) ∈ Wz M z := Subgroup.mem_subgroupOf.1 hw
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hwx
  refine ⟨w, hwW, (mem_pCore_two_iff _).1 hwx, ?_⟩
  exact Y.mul_mem (Y.inv_mem (Wz_le M z hwW)) (hPY hx)

theorem J0_subnormal {m : ℕ} {B M E A : Subgroup G} (h : Sec11 G m 3 B M E A) {R : Subgroup G}
    (hR : IsSylowIn 3 M R) {z : G} (hzR : z ∈ centerOf R) (hzα : z ∈ alphaOf 3 M) (hz3 : z ^ 3 = 1)
    (hzE : z ∈ E) (hz1 : z ≠ 1) {a : G} {J : Subgroup G} (hJ : IsTwoPrimeComp (alphaOf 3 M ⊓ Cg a) J)
    (hzN : z ∈ Subgroup.normalizer (J : Set G)) (hc : ∀ j ∈ J, z * j * z⁻¹ * j⁻¹ ∈ pCoreOf 2 J) :
    IsSubnormal (derivedInf (J ⊓ Cg z)) (Cg2 z a) := by
  have hzp : IsPGroup 3 ↥(Subgroup.zpowers z) := l119_isPGroup_zpowers hz3
  have hJ₀ := dinf_isTwoPrimeComp hJ hzp hzN hc
  have hJ₀J : derivedInf (J ⊓ Cg z) ≤ J ⊓ Cg z := dinf_le _
  have hJ₀Y : derivedInf (J ⊓ Cg z) ≤ alphaOf 3 M ⊓ Cg z :=
    hJ₀J.trans (inf_le_inf_right _ (hJ.1.trans inf_le_left))
  have hJ₀W : derivedInf (J ⊓ Cg z) ≤ Wz M z := le_Wz_of_perfect hR hzR hzα hz3 (dinf_perfect _) hJ₀Y
  have hJ₀a : derivedInf (J ⊓ Cg z) ≤ Cg a := hJ₀J.trans (inf_le_left.trans (hJ.1.trans inf_le_right))
  have hle : Wz M z ⊓ Cg a ≤ (alphaOf 3 M ⊓ Cg a) ⊓ Cg z := by
    intro w hw
    have h1 := Wz_le M z hw.1
    exact ⟨⟨h1.1, hw.2⟩, h1.2⟩
  have h1 : IsSubnormal (derivedInf (J ⊓ Cg z)) (Wz M z ⊓ Cg a) :=
    isSubnormal_of_le_of_le hJ₀.2.1 (le_inf hJ₀W hJ₀a) hle
  have h2 : IsSubnormal (Wz M z ⊓ Cg a) (Cg z ⊓ Cg a) :=
    isSubnormal_inf (Wz_subnormal h hR hzR hzα hz3 hzE hz1) (Cg a)
  have h3 := isSubnormal_trans' h1 h2
  have he : Cg z ⊓ Cg a = Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) :=
    inf_comm _ _
  rw [he] at h3
  unfold Cg2
  rw [l119_cg2_eq a z]
  exact h3

end Wsec

section Types

variable {G : Type} [Group G] [Finite G]

theorem not_two_dvd_card_center (J : Subgroup G) :
    ¬ 2 ∣ Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J))) 2 h2
  have hxo : orderOf (x : ↥J ⧸ CFSG.pCore 2 ↥J) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxc : ∀ g : ↥J ⧸ CFSG.pCore 2 ↥J, g * (x : ↥J ⧸ CFSG.pCore 2 ↥J) = x * g :=
    fun g => Subgroup.mem_center_iff.1 x.2 g
  have hN : (Subgroup.zpowers (x : ↥J ⧸ CFSG.pCore 2 ↥J)).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g ((x : ↥J ⧸ CFSG.pCore 2 ↥J) ^ k) := Commute.zpow_right (hxc g) k
    rw [hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k⟩
  have hx2 : (x : ↥J ⧸ CFSG.pCore 2 ↥J) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (x : ↥J ⧸ CFSG.pCore 2 ↥J)
    rwa [hxo] at this
  have hp : IsPGroup 2 ↥(Subgroup.zpowers (x : ↥J ⧸ CFSG.pCore 2 ↥J)) := l119_isPGroup_zpowers hx2
  have hle := CFSG.LieType.BorelTits.le_pCore 2 hN hp
  have hbot := CFSG.RankThree.PartTwo.Sec18.pCore_quotient_pCore_eq_bot (X := ↥J) 2
  have h1 : (x : ↥J ⧸ CFSG.pCore 2 ↥J) ∈ CFSG.pCore 2 (↥J ⧸ CFSG.pCore 2 ↥J) :=
    hle (Subgroup.mem_zpowers _)
  rw [hbot, Subgroup.mem_bot] at h1
  rw [h1, orderOf_one] at hxo
  exact absurd hxo (by norm_num)

theorem type_of_twoPrimeComp (hS : Prop95Iv.AltSixSevenCentre) {M : Subgroup G} {b : G} (hbM : b ∈ M)
    (hb3 : b ^ 3 = 1) {J : Subgroup G} (hJX : IsTwoPrimeComp (alphaOf 3 M ⊓ Cg b) J) :
    IsAltType 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨ IsHatSeven (↥J ⧸ CFSG.pCore 2 ↥J) := by
  obtain ⟨e⟩ := typeWeak_gen hbM hb3 hJX
  have hQperf : commutator (↥J ⧸ CFSG.pCore 2 ↥J) = ⊤ :=
    commutator_quotient_eq_top (Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hJX.2.2.1)) _
  have hdvd : Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) ∣ 6 :=
    hS 7 (Or.inr rfl) (↥J ⧸ CFSG.pCore 2 ↥J) hQperf ⟨e⟩
  have hodd := not_two_dvd_card_center J
  have h3 : Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) ∣ 3 := by
    have : Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) ∣ 2 * 3 := hdvd
    exact Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)) this
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
  · left
    have hbot : Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) = ⊥ := Subgroup.eq_bot_of_card_eq _ h
    exact ⟨QuotientGroup.quotientBot.symm.trans ((QuotientGroup.quotientMulEquivOfEq hbot.symm).trans e)⟩
  · exact Or.inr ⟨hQperf, h, ⟨e⟩⟩

theorem barOf_equiv_of_ty7 {J₀ : Subgroup G}
    (h : IsAltType 7 (↥J₀ ⧸ CFSG.pCore 2 ↥J₀) ∨ IsHatSeven (↥J₀ ⧸ CFSG.pCore 2 ↥J₀)) :
    Nonempty (barOf 3 J₀ ≃* (↥J₀ ⧸ CFSG.pCore 2 ↥J₀)) :=
  ⟨QuotientGroup.quotientMulEquivOfEq (le_antisymm (Prop126b.primeCore_le_pCore_two_of_ty7 h)
    (Prop126b.pCore_two_le_primeCore_three ↥J₀))⟩

end Types

section Assembly

theorem setup126_of_inputs (hS : Prop95Iv.AltSixSevenCentre) : Prop126b.Setup126 := by
  intro G _ _ m B M E A h a ha ha1 _ J hJ R hR hER z hzR hzα hz3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3' : z ^ 3 = 1 := by
    rw [← hz3]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz3
    omega
  have hzEA : z ∈ E ⊓ A := Sec12c.prop126_central_mem h hER hzR hz3
  obtain ⟨hDDp, -⟩ := h.pair
  obtain ⟨-, hDp, -⟩ := hDDp
  obtain ⟨hSCs, -⟩ := hDp
  obtain ⟨hSCp, -⟩ := hSCs
  obtain ⟨hAM, hAel, -⟩ := hSCp
  have haM : a ∈ M := hAM ha
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have hza : z * a = a * z :=
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨z, hzEA.2⟩ ⟨a, ha⟩)
  have hzX : z ∈ alphaOf 3 M ⊓ Cg a := ⟨hzα, Subgroup.mem_centralizer_singleton_iff.2 hza⟩
  have hty := type_of_twoPrimeComp hS haM ha3 hJ
  have h3J : 3 ∣ Nat.card ↥J :=
    (Prop126b.three_dvd_of_ty7 hty).trans (Subgroup.card_quotient_dvd_card _)
  have hXM : alphaOf 3 M ⊓ Cg a ≤ M := inf_le_left.trans (alphaOf_le 3 M)
  obtain ⟨hzN, hc⟩ := norm_comm_of_comm hXM hJ h3J hzX
    fun x hx => comm_alpha hR hzR hzα hz3' (hJ.1 hx).1
  have hzp : IsPGroup 3 ↥(Subgroup.zpowers z) := l119_isPGroup_zpowers hz3'
  set J₀ : Subgroup G := derivedInf (J ⊓ Cg z) with hJ₀def
  have hJ₀J : J₀ ≤ J := (dinf_le _).trans inf_le_left
  have hJ₀C : J₀ ≤ Cg2 z a := by
    intro x hx
    have hx1 := dinf_le _ hx
    unfold Cg2
    rw [l119_cg2_eq a z]
    exact ⟨(hJ.1 hx1.1).2, hx1.2⟩
  obtain ⟨e₀⟩ := dinf_quot_equiv hJ.2.2.1 hzp hzN hc
  have hty₀ : IsAltType 7 (↥J₀ ⧸ CFSG.pCore 2 ↥J₀) ∨ IsHatSeven (↥J₀ ⧸ CFSG.pCore 2 ↥J₀) :=
    Prop126b.ty7_congr e₀.symm hty
  have hsn : IsSubnormal J₀ (Cg2 z a) := J0_subnormal h hR hzR hzα hz3' hzEA.1 hz1 hJ hzN hc
  have hJ₀2 : IsTwoPrimeComp (Cg2 z a) J₀ :=
    isTwoPrimeComp_of hJ₀C hsn (dinf_perfect _)
      (CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₀.symm
        (quasisimple_of_twoPrimeComp hJ))
  have h3J₀ : 3 ∣ Nat.card ↥J₀ :=
    (Prop126b.three_dvd_of_ty7 hty₀).trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨eb⟩ := barOf_equiv_of_ty7 hty₀
  refine ⟨J₀, Prop126b.glaPComponent_of_twoPrimeComp hJ₀2 (IsSubnormal.refl _) h3J₀, hJ₀J,
    fun j hj => exists_dinf_cover hJ.2.2.1 hzp hzN hc hj, hty, Prop126b.ty7_congr eb.symm hty₀⟩

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims126b

end
