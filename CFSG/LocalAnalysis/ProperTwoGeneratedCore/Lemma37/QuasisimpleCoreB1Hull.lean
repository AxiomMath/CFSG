module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1Unique
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1Fusion

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII

section General

variable {G : Type*} [Group G] [Finite G]

theorem exists_inv_mul_mul_mem_of_pow_eq_one (P : Sylow 2 G) {g : G} {n : ℕ}
    (hg : g ^ 2 ^ n = 1) : ∃ c : G, c⁻¹ * g * c ∈ (P : Subgroup G) := by
  have hp : IsPGroup 2 (Subgroup.zpowers g) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hg)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G R P
  have hmem : MulAut.conj c • g ∈ ((c • R : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hR (Subgroup.mem_zpowers g))
  rw [hc] at hmem
  refine ⟨c⁻¹, ?_⟩
  simpa only [MulAut.smul_def, MulAut.conj_apply, inv_inv] using hmem

theorem fusionStronglyEmbedded_subgroupOf_of_conj_mem {H K : Subgroup G} (hKH : ¬ K ≤ H)
    {k : G} (hkH : k ∈ H) (hkK : k ∈ K) (hk : orderOf k = 2)
    (hfus : ∀ w g : G, w ∈ H → w ∈ K → orderOf w = 2 → g ∈ K → g * w * g⁻¹ ∈ H → g ∈ H) :
    fusionStronglyEmbedded (H.subgroupOf K) := by
  refine ⟨fun htop => hKH (Subgroup.subgroupOf_eq_top.mp htop), ?_, fun g hg => ?_⟩
  · have hmem : (⟨k, hkK⟩ : K) ∈ H.subgroupOf K := hkH
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [Subgroup.orderOf_mk, hk] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  · by_contra hodd
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2
      (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.mp w.2
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv] at hw2
    refine hg (hfus _ _ hw1 (w : K).2 ?_ g.2 hw2)
    change orderOf ((w : K) : G) = 2
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]

end General

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

omit [Finite J] in
abbrev b1L (L : Subgroup (QuasiQuotient u)) : Subgroup (J ⧸ Subgroup.center J) :=
  ((L.comap (quasiMk u)).map (quasiNormalizer u).subtype).map
    (QuotientGroup.mk' (Subgroup.center J))

namespace CaseB1

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {M : ℕ}

theorem normal_comap (hb : CaseB1 Q B T L M) : (L.comap (quasiMk u)).Normal :=
  hb.normal.comap (quasiMk u)

theorem mem_quasiNormalizer_of_commute (hb : CaseB1 Q B T L M) {j : J}
    (hj : Commute (j : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J)) :
    j ∈ quasiNormalizer u :=
  (hb.setting.mem_normalizer_zpowers_iff_commute hb.partC.sq).mpr hj

theorem mem_X_of_isXType (hb : CaseB1 Q B T L M) {y : J ⧸ Subgroup.center J}
    (hy : IsXType T L y) (hyS : y ∈ b1S T) : y ∈ b1X T L := by
  obtain ⟨x, hx, -, hyx⟩ := hy
  obtain ⟨a, rfl⟩ := isConj_iff.mp hyx.symm
  exact hb.mul_mul_inv_mem_X hx hyS

theorem mem_b1L_of_isXType (hb : CaseB1 Q B T L M) {y : J ⧸ Subgroup.center J}
    (hy : IsXType T L y) (hyu : Commute y (u : J ⧸ Subgroup.center J)) : y ∈ b1L L := by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
  have hj := hb.mem_quasiNormalizer_of_commute hyu
  have hjj : j * j = centralElt J := hb.setting.mul_self_eq_centralElt_of_not_isMixedInv
    (hb.orderOf_of_isXType hy) (hb.not_isMixedInv_of_isXType hy)
  have h4 : (⟨j, hj⟩ : quasiNormalizer u) ^ 2 ^ 2 = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, show 2 ^ 2 = 2 + 2 by norm_num, pow_add, pow_two,
      hjj, hb.setting.centralElt_mul_self]
  obtain ⟨c, hc⟩ := exists_inv_mul_mul_mem_of_pow_eq_one T h4
  set k : quasiNormalizer u := c⁻¹ * ⟨j, hj⟩ * c with hk
  have hky : ((k : J) : J ⧸ Subgroup.center J) =
      ((c : J) : J ⧸ Subgroup.center J)⁻¹ * (j : J ⧸ Subgroup.center J) * (c : J) := by
    rw [hk, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hkX : ((k : J) : J ⧸ Subgroup.center J) ∈ b1X T L := by
    refine hb.mem_X_of_isXType (by rw [hky]; exact hy.inv_mul_mul _) ?_
    exact (hb.mk_mem_S_iff _).mpr ⟨k, hc, rfl⟩
  obtain ⟨k', hk', hk'k⟩ := (hb.mk_mem_X_iff _).mp hkX
  have hkL : k ∈ L.comap (quasiMk u) := by
    rw [← Subtype.ext hk'k]
    exact hk'.2
  have hjL : (⟨j, hj⟩ : quasiNormalizer u) ∈ L.comap (quasiMk u) := by
    have h := hb.normal_comap.conj_mem k hkL c
    rwa [hk, show c * (c⁻¹ * ⟨j, hj⟩ * c) * c⁻¹ = (⟨j, hj⟩ : quasiNormalizer u) by group] at h
  exact ⟨j, ⟨⟨j, hj⟩, hjL, rfl⟩, rfl⟩

theorem isXType_of_mem_b1L (hb : CaseB1 Q B T L M) {w : J ⧸ Subgroup.center J}
    (hw : w ∈ b1L L) (hw2 : orderOf w = 2) : IsXType T L w := by
  obtain ⟨_, ⟨k, hk, rfl⟩, rfl⟩ := hw
  simp only [QuotientGroup.mk'_apply, Subgroup.coe_subtype] at hw2 ⊢
  have hkk : (k : J) * k ∈ Subgroup.center J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hw2, pow_orderOf_eq_one]
  have h4 : k ^ 2 ^ 2 = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, show 2 ^ 2 = 2 + 2 by norm_num, pow_add, pow_two]
    rcases hb.setting.mem_center_iff.mp hkk with h1 | he
    · rw [h1, one_mul]
    · rw [he, hb.setting.centralElt_mul_self]
  obtain ⟨c, hc⟩ := exists_inv_mul_mul_mem_of_pow_eq_one T h4
  have hcL : c⁻¹ * k * c ∈ L.comap (quasiMk u) := by
    have h := hb.normal_comap.conj_mem k hk c⁻¹
    rwa [inv_inv] at h
  have hX : (((c⁻¹ * k * c : quasiNormalizer u) : J) : J ⧸ Subgroup.center J) ∈ b1X T L :=
    (hb.mk_mem_X_iff _).mpr ⟨_, ⟨hc, hcL⟩, rfl⟩
  have hck : (((c⁻¹ * k * c : quasiNormalizer u) : J) : J ⧸ Subgroup.center J) =
      ((c : J) : J ⧸ Subgroup.center J)⁻¹ * (k : J) * (c : J) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hconj : IsConj (((c⁻¹ * k * c : quasiNormalizer u) : J) : J ⧸ Subgroup.center J)
      ((k : J) : J ⧸ Subgroup.center J) :=
    isConj_iff.mpr ⟨(c : J), by rw [hck]; group⟩
  refine (isXType_of_mem_X hX fun h1 => ?_).of_isConj hconj
  rw [h1, isConj_one_right] at hconj
  rw [hconj, orderOf_one] at hw2
  exact absurd hw2 (by decide)

theorem isXType_of_mem_localInvolutionPointHull (hb : CaseB1 Q B T L M)
    {x v w : J ⧸ Subgroup.center J} (hx : IsXType T L x)
    (hv : ∃ d ∈ b1D T L, orderOf d = 2 ∧ IsConj v d) (hw : w ∈ localInvolutionPointHull x v)
    (hw2 : orderOf w = 2) : IsXType T L w := by
  obtain ⟨d, hd, hd2, hvd⟩ := hv
  obtain ⟨c, hc⟩ := isConj_iff.mp (hb.isConj_mk_of_isConj hd hd2 hvd)
  have hle : localInvolutionPointHull x v ≤ (b1L L).comap (MulAut.conj c).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨⟨g, rfl⟩, htv⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine hb.mem_b1L_of_isXType ((hx.inv_mul_mul g).conj c) ?_
    have htv' : Commute (g⁻¹ * x * g) v := Subgroup.mem_centralizer_singleton_iff.mp htv
    have h := htv'.map (MulAut.conj c)
    rw [MulAut.conj_apply, MulAut.conj_apply, hc] at h
    exact h
  have hcw := hle hw
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcw
  have h := hb.isXType_of_mem_b1L hcw (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact hw2)
  exact (isXType_conj_iff c w).mp h

theorem local_embedding
    (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hx1 : x ≠ 1) :
    ∀ v : J ⧸ Subgroup.center J, orderOf v = 2 → Commute v x →
      ¬ Subgroup.centralizer ({v} : Set (J ⧸ Subgroup.center J)) ≤ b1Bar B →
        fusionStronglyEmbedded ((b1Bar B).subgroupOf (localInvolutionPointHull x v)) := by
  intro v hv hvx hCv
  have hvB : v ∈ b1Bar B :=
    hb.centralizer_le_of_mem_X hx hx1 (Subgroup.mem_centralizer_singleton_iff.mpr hvx.eq)
  have hD : ∃ d ∈ b1D T L, orderOf d = 2 ∧ IsConj v d := by
    rcases hb.isMixedInv_or_isXType_or_exists_isConj hv hvB with hm | hX | hD
    · exact absurd (hb.setting.centralizer_le_of_isMixedInv hm hvB) hCv
    · exact absurd (hb.centralizer_le_of_isXType hX hvB) hCv
    · exact hD
  refine fusionStronglyEmbedded_subgroupOf_of_conj_mem (fun hle => hCv fun c hc => ?_)
    (hb.S_le (hb.X_le_S hx)) (distinguished_mem_localInvolutionPointHull hvx)
    (hb.orderOf_of_mem_X hx hx1) fun w l hwB hwL hw2 _ hlw =>
      hb.mem_of_conj_mem_of_isXType
        (hb.isXType_of_mem_localInvolutionPointHull (isXType_of_mem_X hx hx1) hD hwL hw2) hwB hlw
  have hcv : Commute c v := Subgroup.mem_centralizer_singleton_iff.mp hc
  refine hb.mem_of_conj_mem_of_mem_X hx hx1 (hle (mem_localInvolutionPointHull ⟨c⁻¹, ?_⟩
    ((hcv.mul_left hvx.symm).mul_left hcv.inv_left)))
  simp only [rightConjugateElem, inv_inv]

end CaseB1

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
