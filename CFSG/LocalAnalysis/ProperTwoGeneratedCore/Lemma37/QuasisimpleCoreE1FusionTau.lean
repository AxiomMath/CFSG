module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1FusionNormalizer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem e1EStar_pt : ∀ w : Fin 64, e1EStar w → (e1PtW w = 0 → w = 32 ∨ w = 8) ∧
    (e1PtW w = 1 → w = 2 ∨ w = 42) ∧ (e1PtW w = 2 → w = 10 ∨ w = 34) := by decide

theorem e1Act_cycle : ∀ v : Fin 64, e1EStar v →
    (e1PtW (e1Act 2 10 v)).val = ((e1PtW v).val + 1) % 3 ∧
    (e1PtW (e1Act 2 34 v)).val = ((e1PtW v).val + 1) % 3 ∧
    (e1PtW (e1Act 42 10 v)).val = ((e1PtW v).val + 1) % 3 ∧
    (e1PtW (e1Act 42 34 v)).val = ((e1PtW v).val + 1) % 3 := by decide

theorem e1_tau_words : c3Conj 16 32 = 32 ∧ c3Conj 16 2 = 34 ∧ c3Mul 32 2 = 34 ∧
    c3Mul 2 32 = 34 ∧ c3Mul 2 8 = 10 ∧ c3Mul 32 40 = 8 ∧ c3Mul 2 40 = 42 ∧ e1EStar 2 := by decide

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem exists_conj_e1EStar {g : J ⧸ Subgroup.center J}
    (hg : g ∈ Subgroup.normalizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)))
    {v : Fin 64} (hv : e1EStar v) : ∃ w : Fin 64, e1EStar w ∧
      g * caseC3Word (Subgroup.center J) u m y x v * g⁻¹ =
        caseC3Word (Subgroup.center J) u m y x w := by
  have hb := d.caseC3BCD
  have hgz := conj_self_of_mem_centralizer_singleton (d.normalizer_e1EBar_le hg)
  obtain ⟨hvE, hv0, hv40⟩ := hv
  obtain ⟨w, hw, hwg⟩ := hb.mem_e1EBar_iff.mp
    ((Subgroup.mem_normalizer_iff.mp hg _).mp (hb.caseC3Word_mem_e1EBar_iff.mpr hvE))
  refine ⟨w, ⟨hw, fun h0 => hv0 ?_, fun h40 => hv40 ?_⟩, hwg.symm⟩
  · rw [h0, CaseC3BCD.caseC3Word_zero] at hwg
    rw [← hb.caseC3Word_eq_one_iff, show caseC3Word (Subgroup.center J) u m y x v =
      g⁻¹ * (g * caseC3Word (Subgroup.center J) u m y x v * g⁻¹) * g by group, ← hwg]
    group
  · rw [h40, ← hgz] at hwg
    rw [← hb.caseC3Word_inj, show caseC3Word (Subgroup.center J) u m y x v =
      g⁻¹ * (g * caseC3Word (Subgroup.center J) u m y x v * g⁻¹) * g by group, ← hwg]
    group

theorem e1PtW_conj_pow {g : J ⧸ Subgroup.center J}
    (hg : g ∈ Subgroup.normalizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)))
    (hcyc : ∀ v w : Fin 64, e1EStar v → g * caseC3Word (Subgroup.center J) u m y x v * g⁻¹ =
      caseC3Word (Subgroup.center J) u m y x w → (e1PtW w).val = ((e1PtW v).val + 1) % 3)
    (k : ℕ) {v w : Fin 64} (hv : e1EStar v)
    (hw : g ^ k * caseC3Word (Subgroup.center J) u m y x v * (g ^ k)⁻¹ =
      caseC3Word (Subgroup.center J) u m y x w) : (e1PtW w).val = ((e1PtW v).val + k) % 3 := by
  have hb := d.caseC3BCD
  induction k generalizing w with
  | zero =>
    rw [pow_zero, one_mul, inv_one, mul_one, hb.caseC3Word_inj] at hw
    rw [hw]
    have := (e1PtW w).isLt
    omega
  | succ k ih =>
    obtain ⟨w', hw', hw'k⟩ := d.exists_conj_e1EStar (Subgroup.pow_mem _ hg k) hv
    have h2 := hcyc w' w hw' (by
      rw [← hw'k, ← hw, pow_succ']
      group)
    have h3 := ih hw'k
    omega

theorem exists_normalizer_cycle (htype : ∀ s ∈ (S : Subgroup J).map
      (QuotientGroup.mk' (Subgroup.center J)), s ∉ (partCSylow T).map
        (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
          CaseC3.Genuine (Subgroup.center J) s) :
    ∃ g ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)),
      ∃ b : Fin 64, (b = 10 ∨ b = 34) ∧
        g * (u : J ⧸ Subgroup.center J) * g⁻¹ = caseC3Word (Subgroup.center J) u m y x 2 ∧
        g * (y : J ⧸ Subgroup.center J) * g⁻¹ = caseC3Word (Subgroup.center J) u m y x b := by
  have hb := d.caseC3BCD
  obtain ⟨h16a, h16e, h32e, h2a, h2c, h32z, h2z, h2S⟩ := e1_tau_words
  have hu : (u : J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x 32 :=
    CaseC3BCD.caseC3Word_thirtytwo.symm
  have hy : (y : J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x 2 :=
    CaseC3BCD.caseC3Word_two.symm
  obtain ⟨n, hn, hnu⟩ := d.exists_normalizer_conj_two htype
  have hnz := conj_self_of_mem_centralizer_singleton (d.normalizer_e1EBar_le hn)
  obtain ⟨b₀, hb₀, hnb₀⟩ := d.exists_conj_e1EStar hn h2S
  rw [← hy] at hnb₀
  have hconj : ∀ a c : J ⧸ Subgroup.center J, n * (a * c) * n⁻¹ = n * a * n⁻¹ * (n * c * n⁻¹) :=
    fun a c => by group
  obtain ⟨h0, h1, h2⟩ := e1EStar_pt b₀ hb₀
  rcases (show e1PtW b₀ = 0 ∨ e1PtW b₀ = 1 ∨ e1PtW b₀ = 2 by omega) with hp | hp | hp
  ·
    refine ⟨n * caseC3Word (Subgroup.center J) u m y x 16, Subgroup.mul_mem _ hn
      (d.map_le_normalizer_e1EBar (hb.caseC3Word_mem 16)), c3Mul 2 b₀,
      by rcases h0 hp with rfl | rfl; exacts [Or.inr h2a, Or.inl h2c], ?_, ?_⟩
    · rw [show n * caseC3Word (Subgroup.center J) u m y x 16 * (u : J ⧸ Subgroup.center J) *
        (n * caseC3Word (Subgroup.center J) u m y x 16)⁻¹ = n * (caseC3Word (Subgroup.center J)
          u m y x 16 * (u : J ⧸ Subgroup.center J) *
            (caseC3Word (Subgroup.center J) u m y x 16)⁻¹) * n⁻¹ by group, hu,
        hb.caseC3Word_conj, h16a, ← hu, hnu, hy]
    · rw [show n * caseC3Word (Subgroup.center J) u m y x 16 * (y : J ⧸ Subgroup.center J) *
        (n * caseC3Word (Subgroup.center J) u m y x 16)⁻¹ = n * (caseC3Word (Subgroup.center J)
          u m y x 16 * (y : J ⧸ Subgroup.center J) *
            (caseC3Word (Subgroup.center J) u m y x 16)⁻¹) * n⁻¹ by group, hy,
        hb.caseC3Word_conj, h16e, ← h32e, ← hb.caseC3Word_mul, hconj, ← hu, ← hy, hnu, hnb₀, hy,
        hb.caseC3Word_mul]
  ·
    exfalso
    rcases h1 hp with rfl | rfl
    · have h' : (y : J ⧸ Subgroup.center J) = u :=
        mul_left_cancel (mul_right_cancel (hnb₀.trans (hy.symm.trans hnu.symm)))
      rw [hy, hu, hb.caseC3Word_inj] at h'
      exact absurd h' (by decide)
    · have e : caseC3Word (Subgroup.center J) u m y x 42 =
          n * ((u : J ⧸ Subgroup.center J) * caseC3Word (Subgroup.center J) u m y x 40) * n⁻¹ := by
        rw [← h2z, ← hb.caseC3Word_mul, ← hy, ← hnu]
        nth_rewrite 1 [← hnz]
        group
      have h' : (y : J ⧸ Subgroup.center J) = u * caseC3Word (Subgroup.center J) u m y x 40 :=
        mul_left_cancel (mul_right_cancel (hnb₀.trans e))
      rw [hy, hu, hb.caseC3Word_mul, hb.caseC3Word_inj, h32z] at h'
      exact absurd h' (by decide)
  ·
    exact ⟨n, hn, b₀, h2 hp, by rw [hnu, hy], hnb₀⟩

theorem exists_tau (htype : ∀ s ∈ (S : Subgroup J).map
      (QuotientGroup.mk' (Subgroup.center J)), s ∉ (partCSylow T).map
        (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
          CaseC3.Genuine (Subgroup.center J) s) :
    ∃ τ ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)),
      (∃ a : ℕ, τ ^ 3 ^ a = 1) ∧
      τ ^ 3 ∈ Subgroup.centralizer
        (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) ∧
      ∀ s ∈ e1EBar (Subgroup.center J) u m y x, s ≠ 1 →
        s ≠ caseC3Word (Subgroup.center J) u m y x 40 →
          τ * s * τ⁻¹ ≠ s ∧ τ * s * τ⁻¹ ≠ s * caseC3Word (Subgroup.center J) u m y x 40 := by
  have hb := d.caseC3BCD
  obtain ⟨g, hg, b, hb', hgu, hgy⟩ := d.exists_normalizer_cycle htype
  have hgz := conj_self_of_mem_centralizer_singleton (d.normalizer_e1EBar_le hg)
  have hcyc : ∀ v w : Fin 64, e1EStar v → g * caseC3Word (Subgroup.center J) u m y x v * g⁻¹ =
      caseC3Word (Subgroup.center J) u m y x w → (e1PtW w).val = ((e1PtW v).val + 1) % 3 := by
    intro v w hv hw
    have h := d.conj_caseC3Word_of_e1E hgu hgy hgz hv.1
    rw [hw, hb.caseC3Word_inj] at h
    rw [h]
    obtain ⟨c1, c2, c3, c4⟩ := e1Act_cycle v hv
    rcases hb' with rfl | rfl
    exacts [c1, c2]
  have hEStar : ∀ v : Fin 64, e1E v → caseC3Word (Subgroup.center J) u m y x v ≠ 1 →
      caseC3Word (Subgroup.center J) u m y x v ≠ caseC3Word (Subgroup.center J) u m y x 40 →
        e1EStar v := fun v hv h1 h40 =>
    ⟨hv, fun h => h1 (by rw [h, CaseC3BCD.caseC3Word_zero]), fun h => h40 (by rw [h])⟩
  obtain ⟨a, r, hr3, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  refine ⟨g ^ r, Subgroup.pow_mem _ hg r, ⟨a, by rw [← pow_mul, mul_comm, ← hor,
    pow_orderOf_eq_one]⟩, ?_, ?_⟩
  · rw [← pow_mul, Subgroup.mem_centralizer_iff]
    intro s hs
    have hz : g ^ (r * 3) * caseC3Word (Subgroup.center J) u m y x 40 * (g ^ (r * 3))⁻¹ =
        caseC3Word (Subgroup.center J) u m y x 40 := conj_self_of_mem_centralizer_singleton
      (d.normalizer_e1EBar_le (Subgroup.pow_mem _ hg _))
    by_cases hs1 : s = 1
    · rw [hs1, one_mul, mul_one]
    by_cases hsz : s = caseC3Word (Subgroup.center J) u m y x 40
    · rw [hsz]
      nth_rewrite 1 [← hz]
      group
    obtain ⟨v, hv, rfl⟩ := hb.mem_e1EBar_iff.mp hs
    have hvS := hEStar v hv hs1 hsz
    obtain ⟨w, hwS, hw⟩ := d.exists_conj_e1EStar (Subgroup.pow_mem _ hg (r * 3)) hvS
    have hpt := d.e1PtW_conj_pow hg hcyc (r * 3) hvS hw
    have hpt' : e1PtW v = e1PtW w := Fin.ext (by have := (e1PtW v).isLt; omega)
    rcases (e1PtW_eq_iff v w hvS hwS).mp hpt' with rfl | hwv
    · nth_rewrite 1 [← hw]
      group
    · exfalso
      have h40 := eq_one_of_conj_eq_mul (g := g ^ (r * 3)) (w := caseC3Word (Subgroup.center J)
        u m y x v) (k := 3 ^ a) (Odd.pow (by decide)) (by
          rw [← pow_mul, show r * 3 * 3 ^ a = orderOf g * 3 by rw [hor]; ring, pow_mul,
            pow_orderOf_eq_one, one_pow]) hz (by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hb.caseC3Word_mul,
            c3Mul_forty_forty, CaseC3BCD.caseC3Word_zero, one_mul])
        (by rw [hw, hwv, hb.caseC3Word_mul])
      rw [hb.caseC3Word_eq_one_iff] at h40
      exact absurd h40 (by decide)
  · intro s hs hs1 hsz
    obtain ⟨v, hv, rfl⟩ := hb.mem_e1EBar_iff.mp hs
    have hvS := hEStar v hv hs1 hsz
    obtain ⟨w, hwS, hw⟩ := d.exists_conj_e1EStar (Subgroup.pow_mem _ hg r) hvS
    have hpt := d.e1PtW_conj_pow hg hcyc r hvS hw
    have hne : e1PtW w ≠ e1PtW v := fun h => by
      have := congrArg Fin.val h
      have := (e1PtW v).isLt
      omega
    rw [hw]
    refine ⟨fun h => hne (by rw [hb.caseC3Word_inj.mp h]), fun h => hne ?_⟩
    rw [hb.caseC3Word_mul, hb.caseC3Word_inj] at h
    exact ((e1PtW_eq_iff v w hvS hwS).mpr (Or.inr h)).symm

theorem exists_oddCore_centralizer_e1EBar :
    ∃ O : Subgroup (J ⧸ Subgroup.center J),
      O ≤ Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) ∧
      Odd (Nat.card O) ∧
      (∀ c ∈ Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x :
        Set (J ⧸ Subgroup.center J)), ∃ e ∈ e1EBar (Subgroup.center J) u m y x, ∃ o ∈ O,
          e * o = c) ∧
      (∀ c ∈ Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x :
        Set (J ⧸ Subgroup.center J)), c ∈ O ↔ Odd (orderOf c)) ∧
      (∀ e ∈ e1EBar (Subgroup.center J) u m y x, e ∈ O → e = 1) ∧
      ∀ n ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)),
        ∀ o ∈ O, n * o * n⁻¹ ∈ O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb := d.caseC3BCD
  set E := e1EBar (Subgroup.center J) u m y x with hE
  set C := Subgroup.centralizer (E : Set (J ⧸ Subgroup.center J)) with hC
  have hEC : E ≤ C := fun s hs => Subgroup.mem_centralizer_iff.mpr fun t ht =>
    hb.commute_of_mem_e1EBar ht hs
  have hCN : C ≤ Subgroup.normalizer (E : Set (J ⧸ Subgroup.center J)) := fun c hc =>
    mem_normalizer_of_forall_conj_mem fun s hs => by
      rw [show c * s * c⁻¹ = s by rw [← Subgroup.mem_centralizer_iff.mp hc s hs]; group]
      exact hs
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hb.card_e1EBar]; norm_num)
  obtain ⟨P, hP⟩ := (hE2.of_equiv (Subgroup.subgroupOfEquivOfLe hEC).symm).exists_le_sylow
  set S'' := S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J))
  have hS'' : (S'' : Subgroup (J ⧸ Subgroup.center J)) =
      (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) := Sylow.coe_mapSurjective _ _
  have hPE : (P : Subgroup C) = E.subgroupOf C := by
    refine le_antisymm (fun p hp => ?_) hP
    obtain ⟨k, hkN, hk⟩ := exists_conj_mem_sylow_of_le S''
      (hS''.symm ▸ d.map_le_normalizer_e1EBar) ((Subgroup.map_subtype_le _).trans hCN)
      (P.isPGroup'.map C.subtype)
    have h1 := hk _ (Subgroup.mem_map_of_mem C.subtype hp)
    rw [hS''] at h1
    have h2 := conj_mem_centralizer_of_mem_normalizer hkN p.2
    have h3 := hb.mem_e1EBar_of_forall_commute h1 fun t ht =>
      (Subgroup.mem_centralizer_iff.mp h2 t ht).symm
    have h4 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkN) _).mp h3
    rw [show k⁻¹ * (k * C.subtype p * k⁻¹) * k⁻¹⁻¹ = (p : J ⧸ Subgroup.center J) by
      rw [Subgroup.coe_subtype]; group] at h4
    exact Subgroup.mem_subgroupOf.mpr h4
  have hNC : Subgroup.normalizer ((P : Subgroup C) : Set C) ≤
      Subgroup.centralizer ((P : Subgroup C) : Set C) := by
    intro c _
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    rw [SetLike.mem_coe, hPE, Subgroup.mem_subgroupOf] at hp
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp c.2 _ hp)
  set K := (MonoidHom.transferSylow P hNC).ker with hK
  have hKodd : Odd (Nat.card K) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (MonoidHom.not_dvd_card_ker_transferSylow P hNC))
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hiff : ∀ c ∈ C, c ∈ K.map C.subtype ↔ Odd (orderOf c) := by
    intro c hc
    constructor
    · rintro ⟨κ, hκ, rfl⟩
      have h1 := orderOf_dvd_natCard (⟨κ, hκ⟩ : K)
      rw [Subgroup.orderOf_mk] at h1
      rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
      exact hKodd.of_dvd_nat h1
    · intro hodd
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      change (⟨c, hc⟩ : C) ∈ (MonoidHom.transferSylow P hNC).ker
      rw [MonoidHom.mem_ker]
      obtain ⟨j, hj⟩ := P.isPGroup' (MonoidHom.transferSylow P hNC ⟨c, hc⟩)
      have h1 := orderOf_dvd_of_pow_eq_one hj
      have h2 := (orderOf_map_dvd (MonoidHom.transferSylow P hNC) ⟨c, hc⟩).trans
        (dvd_of_eq (Subgroup.orderOf_mk c hc))
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (hodd.coprime_two_right.pow_right j) h2 h1)
  refine ⟨K.map C.subtype, Subgroup.map_subtype_le _, ?_, fun c hc => ?_, hiff, fun e he heO => ?_,
    fun n hn o ho => ?_⟩
  · rwa [Subgroup.card_map_of_injective C.subtype_injective]
  · obtain ⟨⟨⟨κ, hκ⟩, ⟨p, hp⟩⟩, hκp⟩ :=
      (Subgroup.IsComplement.existsUnique hcompl ⟨c, hc⟩).exists
    have hpE : (p : J ⧸ Subgroup.center J) ∈ E := by
      have h : p ∈ (P : Subgroup C) := hp
      rw [hPE, Subgroup.mem_subgroupOf] at h
      exact h
    refine ⟨_, hpE, _, Subgroup.mem_map_of_mem C.subtype hκ, ?_⟩
    have h := congrArg Subtype.val hκp
    simp only [Subgroup.coe_mul] at h
    rw [← h, Subgroup.coe_subtype]
    exact Subgroup.mem_centralizer_iff.mp κ.2 _ hpE
  · have hodd := (hiff e (hEC he)).mp heO
    have h2 : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two]; exact hb.mul_self_of_mem_e1EBar he)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right
      dvd_rfl h2 |>.symm ▸ rfl)
  · have hoC : o ∈ C := Subgroup.map_subtype_le _ ho
    refine (hiff _ (conj_mem_centralizer_of_mem_normalizer hn hoC)).mpr ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact (hiff o hoC).mp ho

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
