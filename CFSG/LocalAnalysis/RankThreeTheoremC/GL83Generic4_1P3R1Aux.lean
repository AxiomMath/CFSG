module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
import CFSG.LocalAnalysis.PreuniquenessRankFour.SamePrimeAction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

section Quot

variable {G : Type} [Group G] [Finite G]

theorem pRank_eq_of_isSylowOf3 {p : ℕ} (hp : p.Prime) {Y S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S Y) : Open.pRank p S = Open.pRank p Y := by
  obtain ⟨T, rfl⟩ := hS
  rw [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp Y.subtype
    Y.subtype_injective, CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p hp T,
    ← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp Y.subtype
      Y.subtype_injective (⊤ : Subgroup Y), ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem normalizer_map_mk_le3 {p : ℕ} {N M : Subgroup G} {D : Subgroup N} (hp : p.Prime)
    (hD : IsPGroup p D) (hnorm : normalizer ((D.map N.subtype : Subgroup G) : Set G) ≤ M) :
    normalizer ((D.map (QuotientGroup.mk' (primeComplementCore (G := N) p)) :
        Subgroup (N ⧸ primeComplementCore (G := N) p)) :
          Set (N ⧸ primeComplementCore (G := N) p)) ≤
      ((N ⊓ M).subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) := by
  set O := primeComplementCore (G := N) p with hO
  have hNH : normalizer (D : Set N) ≤ (N ⊓ M).subgroupOf N := fun n hn =>
    Subgroup.mem_subgroupOf.mpr
      ⟨n.property, hnorm (Subgroup.le_normalizer_map N.subtype ⟨n, hn, rfl⟩)⟩
  intro y hy
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective O y
  have h1 := comap_normalizer_map_le_sup hp O (primeComplementCore_coprime p) hD hy
  have h2 := Subgroup.mem_map_of_mem (QuotientGroup.mk' O) h1
  rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' O).ge,
    bot_sup_eq] at h2
  exact Subgroup.map_mono hNH h2

theorem isMulCommutative_of_isPGroup3 {P : Sylow 3 G} (hPab : IsMulCommutative (P : Subgroup G))
    {Q : Subgroup G} (hQ : IsPGroup 3 Q) : IsMulCommutative Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P', hP'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
  have h : ((g • P : Sylow 3 G) : Subgroup G) = (P' : Subgroup G) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h
  have hcomm : ∀ a b : G, a ∈ (P' : Subgroup G) → b ∈ (P' : Subgroup G) → a * b = b * a := by
    intro a b ha hb
    rw [← h, Subgroup.mem_smul_pointwise_iff_exists] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hab : a' * b' = b' * a' :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := (P : Subgroup G))).comm ⟨a', ha'⟩
        ⟨b', hb'⟩)
    show g * a' * g⁻¹ * (g * b' * g⁻¹) = g * b' * g⁻¹ * (g * a' * g⁻¹)
    calc g * a' * g⁻¹ * (g * b' * g⁻¹) = g * (a' * b') * g⁻¹ := by group
      _ = g * (b' * a') * g⁻¹ := by rw [hab]
      _ = g * b' * g⁻¹ * (g * a' * g⁻¹) := by group
  exact IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a b (hP' a.2) (hP' b.2))

theorem weakClosed_sylow3 {P : Sylow 3 G} {x : G}
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (Q : Sylow 3 G) (hxQ : x ∈ (Q : Subgroup G)) (g : G)
    (hg : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G)) :
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P Q
  have h : ((c • P : Sylow 3 G) : Subgroup G) = (Q : Subgroup G) := by rw [hc]
  rw [Sylow.coe_subgroup_smul] at h
  have hmem : ∀ y ∈ (Q : Subgroup G), c⁻¹ * y * c ∈ (P : Subgroup G) := by
    intro y hy
    rw [← h, Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have : c⁻¹ * (c * z * c⁻¹) * c = z := by group
    show c⁻¹ * (c * z * c⁻¹) * c ∈ (P : Subgroup G)
    rw [this]
    exact hz
  have h1 : (zpowers x).map (MulAut.conj (c⁻¹ * g)).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨z, hz, rfl⟩
    have hgz : g * z * g⁻¹ ∈ (Q : Subgroup G) := hg ⟨z, hz, rfl⟩
    have := hmem _ hgz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
    simpa [mul_assoc] using this
  have h2 : (zpowers x).map (MulAut.conj c⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ (Q : Subgroup G) := zpowers_le.mpr hxQ hz
    have := hmem _ hz'
    simpa [MulAut.conj_apply] using this
  have e1 := hwc _ h1
  have e2 := hwc _ h2
  have e3 : (zpowers x).map (MulAut.conj (c⁻¹ * g)).toMonoidHom =
      ((zpowers x).map (MulAut.conj g).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp
  apply Subgroup.map_injective (f := (MulAut.conj c⁻¹).toMonoidHom) (MulAut.conj c⁻¹).injective
  rw [← e3, e1, e2]

theorem zpowers_eq_of_mem_zpowers_of_orderOf_eq_three3 {Y : Type*} [Group Y] {a x : Y}
    (hx : orderOf x = 3) (hax : a ∈ zpowers x) (ha1 : a ≠ 1) : zpowers a = zpowers x := by
  have hdvd : orderOf a ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard (zpowers x) hax
    rwa [Nat.card_zpowers, hx] at this
  have hord : orderOf a = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have : Finite (zpowers x) := Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hx]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hax) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hx, hord]

end Quot

section Fin

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem eq_bot_of_normalized_coprime3 (hcore : primeComplementCore (G := Y) 3 = ⊥)
    {O : Subgroup Y} (hcop : Nat.Coprime 3 (Nat.card O)) (hn : ∀ g : Y, ∀ o ∈ O, g * o * g⁻¹ ∈ O) :
    O = ⊥ := by
  have hnormal : O.Normal := ⟨fun o ho g => hn g o ho⟩
  have := normal_coprime_le_primeComplementCore 3 O hnormal hcop
  rwa [hcore, le_bot_iff] at this

private theorem eq_bot_of_normal_in_normal3 (hcore : primeComplementCore (G := Y) 3 = ⊥)
    {C D : Subgroup Y} [C.Normal] (hDC : D ≤ C) (hcop : Nat.Coprime 3 (Nat.card D))
    (hn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D) : D = ⊥ := by
  set A : Subgroup C := primeComplementCore (G := C) 3 with hA
  have : A.Characteristic := primeComplementCore_characteristic 3
  have hD' : (D.subgroupOf C).Normal :=
    ⟨fun d hd c => Subgroup.mem_subgroupOf.mpr (hn c c.2 d (Subgroup.mem_subgroupOf.mp hd))⟩
  have hDA : D.subgroupOf C ≤ A := by
    refine normal_coprime_le_primeComplementCore 3 _ hD' ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv]
    exact hcop
  have hAn : (A.map C.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hAcop : Nat.Coprime 3 (Nat.card (A.map C.subtype)) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact primeComplementCore_coprime 3
  have hAbot : A.map C.subtype = ⊥ := by
    have := normal_coprime_le_primeComplementCore 3 _ hAn hAcop
    rwa [hcore, le_bot_iff] at this
  rw [eq_bot_iff]
  intro d hd
  have h1 : (⟨d, hDC hd⟩ : C) ∈ A := hDA (Subgroup.mem_subgroupOf.mpr hd)
  have h2 : d ∈ A.map C.subtype := ⟨⟨d, hDC hd⟩, h1, rfl⟩
  rw [hAbot] at h2
  exact h2

theorem centralizes_of_normal_centralizer3 (hcore : primeComplementCore (G := Y) 3 = ⊥)
    {Γ O K S R : Subgroup Y} {x : Y} (hxo : orderOf x = 3) (hcop : Nat.Coprime 3 (Nat.card O))
    (hOΓ : ∀ g ∈ Γ, ∀ o ∈ O, g * o * g⁻¹ ∈ O) (hxΓ : x ∈ Γ) (hKn : K.Normal)
    (hKC : K ≤ centralizer ({x} : Set Y)) (hKΓ : ¬ K ≤ Γ) (hSyl : IsSylowOf 3 S ⊤)
    (hΩ : ∀ s ∈ S, s ^ 3 = 1 → s ∈ R)
    (hothers : ∀ a ∈ R, a ≠ 1 → zpowers a ≠ zpowers x → centralizer ({a} : Set Y) ≤ Γ) :
    ∀ o ∈ O, o * x = x * o := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  intro o ho
  have hdO : o * x * o⁻¹ * x⁻¹ ∈ O := by
    have := O.mul_mem ho (hOΓ x hxΓ o⁻¹ (O.inv_mem ho))
    simpa [mul_assoc] using this
  have hfin : o * x * o⁻¹ * x⁻¹ = 1 → o * x = x * o := fun h => by
    have h1 : o * x * o⁻¹ = x := mul_inv_eq_one.mp h
    calc o * x = (o * x * o⁻¹) * o := by group
      _ = x * o := by rw [h1]
  by_cases hxK : x ∈ K
  ·
    have hc : o * x * o⁻¹ ∈ K := hKn.conj_mem x hxK o
    have hcx : (o * x * o⁻¹) * x = x * (o * x * o⁻¹) := mem_centralizer_singleton_iff.mp (hKC hc)
    apply hfin
    have hcomm : Commute (o * x * o⁻¹) x⁻¹ := by
      have : Commute (o * x * o⁻¹) x := hcx
      exact this.inv_right
    have hc3 : (o * x * o⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
    have hg3 : (o * x * o⁻¹ * x⁻¹) ^ 3 = 1 := by
      rw [hcomm.mul_pow, hc3, inv_pow, hx3, inv_one, one_mul]
    have hord : orderOf (o * x * o⁻¹ * x⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    have hord2 : orderOf (o * x * o⁻¹ * x⁻¹) ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨_, hdO⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord hord2)
  ·
    have h3K : 3 ∣ Nat.card K := by
      by_contra h3
      have hKcop : Nat.Coprime 3 (Nat.card K) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
      have := normal_coprime_le_primeComplementCore 3 K hKn hKcop
      rw [hcore] at this
      exact hKΓ (this.trans bot_le)
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3K
    have hko : orderOf (k : Y) = 3 := (Subgroup.orderOf_coe k).trans hk
    obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 3 Y, (Q : Subgroup Y) = S := by
      obtain ⟨-, hp, hdvd⟩ := isSylowOf_iff.1 hSyl
      rw [Subgroup.relIndex_top_right] at hdvd
      exact ⟨hp.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩
    have hkp : IsPGroup 3 (zpowers (k : Y)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hko, pow_one])
    obtain ⟨Q', hQ'⟩ := hkp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q Q'
    have hkQ' : (k : Y) ∈ ((g • Q : Sylow 3 Y) : Subgroup Y) := by
      rw [hg]
      exact hQ' (mem_zpowers _)
    rw [Sylow.coe_subgroup_smul, hQ, Subgroup.mem_smul_pointwise_iff_exists] at hkQ'
    obtain ⟨a, haS, hak⟩ := hkQ'
    have hak2 : g * a * g⁻¹ = (k : Y) := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using hak
    have hak' : a = g⁻¹ * (k : Y) * g := by
      rw [← hak2]
      group
    have haK : a ∈ K := by
      rw [hak']
      simpa using hKn.conj_mem (k : Y) k.2 g⁻¹
    have ha3 : a ^ 3 = 1 := by
      have h1 : (g⁻¹ * (k : Y) * g) ^ 3 = g⁻¹ * (k : Y) ^ 3 * g := by
        simpa using conj_pow (a := g⁻¹) (b := (k : Y)) (i := 3)
      have hk3 : (k : Y) ^ 3 = 1 := by rw [← hko]; exact pow_orderOf_eq_one _
      rw [hak', h1, hk3]
      group
    have haR : a ∈ R := hΩ a haS ha3
    have ha1 : a ≠ 1 := by
      intro h1
      rw [h1] at hak2
      have : (k : Y) = 1 := by simpa using hak2.symm
      rw [this, orderOf_one] at hko
      omega
    have hax : zpowers a ≠ zpowers x := by
      intro h
      apply hxK
      have : x ∈ zpowers a := h ▸ mem_zpowers x
      exact zpowers_le.mpr haK this
    have hCa := hothers a haR ha1 hax
    have hCK : centralizer (K : Set Y) ≤ Γ :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haK)).trans hCa
    have hCn : (centralizer (K : Set Y)).Normal := ⟨fun c hc y => by
      rw [mem_centralizer_iff]
      intro k hk
      have h1 : (y⁻¹ * k * y) * c = c * (y⁻¹ * k * y) := by
        have := mem_centralizer_iff.mp hc (y⁻¹ * k * y) (by simpa using hKn.conj_mem k hk y⁻¹)
        exact this
      calc k * (y * c * y⁻¹) = y * ((y⁻¹ * k * y) * c) * y⁻¹ := by group
        _ = y * (c * (y⁻¹ * k * y)) * y⁻¹ := by rw [h1]
        _ = y * c * y⁻¹ * k := by group⟩
    have hxC : x ∈ centralizer (K : Set Y) := by
      rw [mem_centralizer_iff]
      intro k hk
      exact mem_centralizer_singleton_iff.mp (hKC hk)
    have hdC : o * x * o⁻¹ * x⁻¹ ∈ centralizer (K : Set Y) :=
      Subgroup.mul_mem _ (hCn.conj_mem x hxC o) (Subgroup.inv_mem _ hxC)
    have hDbot : O ⊓ centralizer (K : Set Y) = ⊥ := by
      refine eq_bot_of_normal_in_normal3 hcore (C := centralizer (K : Set Y)) inf_le_right
        (hcop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)) ?_
      intro c hc δ hδ
      exact ⟨hOΓ c (hCK hc) δ hδ.1, hCn.conj_mem δ hδ.2 c⟩
    exact hfin (by simpa using (Subgroup.mem_bot.mp (hDbot ▸ (⟨hdO, hdC⟩ :
      o * x * o⁻¹ * x⁻¹ ∈ O ⊓ centralizer (K : Set Y)))))

end Fin

end CFSG.LocalAnalysis.RankThreeTheoremC
