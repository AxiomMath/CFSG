module

import CFSG.LocalAnalysis.RankThreeTheoremC.HasPrimeConstraintBridge
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_PCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem KFactSetting.exists_normal_coprime_signalizer {n : ℕ} (hS : KFactSetting n G)
    (hD1 : TheoremD1 G) (hK : KFactLemma212Ge n) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G) {d : G} (hdD : d ∈ D)
    (hd1 : d ≠ 1) :
    ∃ K : Subgroup G, K ≤ normalizer ((zpowers d : Subgroup G) : Set G) ∧
      normalizer ((zpowers d : Subgroup G) : Set G) ≤ normalizer (K : Set G) ∧
      p.Coprime (Nat.card K) ∧ ∀ Y : Subgroup G,
        Y ≤ normalizer ((zpowers d : Subgroup G) : Set G) → p.Coprime (Nat.card Y) →
          D ≤ normalizer (Y : Set G) → Y ≤ K := by
  classical
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, -⟩ :=
    hS.obstruction.transitivity_data hD1 hp hext hPD hR h13
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  set N₀ := normalizer ((zpowers z : Subgroup G) : Set G) with hN₀
  have hcon : HasPrimeConstraint (G := N₀) p :=
    hasPrimeConstraint_of_isPConstrained
      (hS.isPConstrained_normalizer_zpowers_of_transitivity hD1 hK hp hext hPD hDab hzD hz1 hzc hzp
        hN₀M)
  have hDN₀ : D ≤ N₀ := by
    intro x hx
    refine centralizer_singleton_le_normalizer_zpowers z ?_
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hDab.is_comm.comm ⟨x, hx⟩ ⟨z, hzD⟩)
  have hcontains : ∀ x : G, x ∈ N₀ → x ∈ centralizer (D : Set G) → orderOf x = p → x ∈ D :=
    fun x _ hxC hxo => hS.obstruction.mem_of_mem_centralizer_of_isMulCommutative hD1 hp hext hDab
      hCD hxC (by rw [← hxo]; exact pow_orderOf_eq_one x)
  obtain ⟨g, hgN, hgz⟩ := hS.obstruction.exists_mem_normalizer_zpowers_eq hD1 hp hext hPD hDab
    hCD hzD hz1 hzc hN₀M hdD hd1
  have hD : D.map (MulAut.conj g).toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hgN
  have hD' : D.map (MulAut.conj g⁻¹).toMonoidHom = D :=
    mem_normalizer_iff_map_conj_eq.mp (inv_mem hgN)
  set K₀ := (primeComplementCore (G := N₀) p).map N₀.subtype with hK₀
  have hK₀N : K₀ ≤ N₀ := Subgroup.map_subtype_le _
  have hK₀norm : N₀ ≤ normalizer (K₀ : Set G) := CFSG.ABGTheoremB.le_normalizer_map_subtype N₀ _
  have hNd : normalizer ((zpowers d : Subgroup G) : Set G) =
      N₀.map (MulAut.conj g).toMonoidHom := by
    rw [hgz, hN₀, Subgroup.map_equiv_normalizer_eq]
  refine ⟨K₀.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [hNd]
    exact Subgroup.map_mono hK₀N
  · rw [hNd, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hK₀norm
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hK₀,
      Subgroup.card_map_of_injective N₀.subtype_injective]
    exact primeComplementCore_coprime p
  · intro Y hYN hYc hDY
    set Y' := Y.map (MulAut.conj g⁻¹).toMonoidHom with hY'
    have hYY' : Y'.map (MulAut.conj g).toMonoidHom = Y := by
      rw [hY', Subgroup.map_map]
      have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply]
        group
      rw [this, Subgroup.map_id]
    have hY'N : Y' ≤ N₀ := by
      have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hYN
      rw [hNd, Subgroup.map_map] at h
      have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply]
        group
      rwa [this, Subgroup.map_id] at h
    have hDY' : D ≤ normalizer (Y' : Set G) := by
      rw [← hD', ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hDY
    have hY'c : p.Coprime (Nat.card Y') := by
      rw [hY', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
      exact hYc
    have hle := ambient_prime_constraint_signalizer_le_core p hprime hodd N₀ D Y' hcon
      (P.isPGroup'.to_le hDP) hDN₀ hY'c hY'N hDY' hcontains
    rw [← hYY']
    exact Subgroup.map_mono hle

theorem KFactSetting.pCore_quotient_eq_bot {n : ℕ} (hS : KFactSetting n G)
    (hD1 : TheoremD1 G) (hK : KFactLemma212Ge n) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M D R T H : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) (hH : IsRelPairCandidate p D R T H) :
    CFSG.Open.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥ := by
  classical
  by_contra hQ
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, -⟩ :=
    hS.obstruction.transitivity_data hD1 hp hext hPD hR h13
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hDp : IsPGroup p D := P.isPGroup'.to_le hDP
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hH.base_le
  set K' : Subgroup H := primeComplementCore (G := H) p with hK'
  set π : H →* H ⧸ K' := QuotientGroup.mk' K' with hπ
  have hDHp : IsPGroup p (D.subgroupOf H) :=
    hDp.of_equiv (Subgroup.subgroupOfEquivOfLe hDH).symm
  have hDbarp : IsPGroup p ((D.subgroupOf H).map π) := hDHp.map π
  have hQnormal : (CFSG.Open.pCore p (H ⧸ K')).Normal :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal p
  obtain ⟨u, huQ, huo, hucomm⟩ := exists_orderOf_eq_centralizing_of_normal
    (Q := CFSG.Open.pCore p (H ⧸ K')) (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup p) hQ
    hDbarp
  have hcontainsH : ∀ e : H, e ∈ centralizer ((D.subgroupOf H : Subgroup H) : Set H) →
      orderOf e = p → e ∈ D.subgroupOf H := by
    intro e hec heo
    have hxC : (e : G) ∈ centralizer (D : Set G) := by
      apply mem_centralizer_iff.mpr
      intro d hd
      exact congrArg Subtype.val (mem_centralizer_iff.mp hec ⟨d, hDH hd⟩ hd)
    have hxp : (e : G) ^ p = 1 := by
      have : orderOf (e : G) = p := (Subgroup.orderOf_coe e).trans heo
      rw [← this]
      exact pow_orderOf_eq_one _
    exact hS.obstruction.mem_of_mem_centralizer_of_isMulCommutative hD1 hp hext hDab hCD hxC hxp
  have hker : p.Coprime (Nat.card π.ker) := by
    rw [hπ, QuotientGroup.ker_mk']
    exact primeComplementCore_coprime p
  have hSC := coprime_quotient_preserves_order_prime_centralizer_condition p hprime
    (D.subgroupOf H) hDHp π (QuotientGroup.mk'_surjective K') hker hcontainsH
  have huC : u ∈ centralizer (((D.subgroupOf H).map π : Subgroup (H ⧸ K')) : Set (H ⧸ K')) :=
    mem_centralizer_iff.mpr fun d hd => hucomm d hd
  obtain ⟨δ, hδ, hδu⟩ := hSC u huC huo
  have hdD : (δ : G) ∈ D := hδ
  have hdH : (δ : G) ∈ H := δ.2
  have hd1 : (δ : G) ≠ 1 := by
    intro h
    have hδ1 : δ = 1 := Subtype.ext h
    rw [hδ1, map_one] at hδu
    rw [← hδu, orderOf_one] at huo
    exact hprime.one_lt.ne huo
  have hdp : (δ : G) ^ p = 1 := (hext.pow_eq_one_and_commutator_mem hprime hodd).1 _ hdD
  have huδ : π δ ∈ CFSG.Open.pCore p (H ⧸ K') := by rw [hδu]; exact huQ
  obtain ⟨Kd, -, -, hKdc, hKdall⟩ := hS.exists_normal_coprime_signalizer hD1 hK hp hext hPD hR
    h13 hdD hd1
  set Kg : Subgroup G := K'.map H.subtype with hKg
  have hKgH : Kg ≤ H := Subgroup.map_subtype_le _
  have hKgN : H ≤ normalizer (Kg : Set G) := CFSG.ABGTheoremB.le_normalizer_map_subtype H _
  have hKgc : p.Coprime (Nat.card Kg) := by
    rw [hKg, card_map_of_injective H.subtype_injective]
    exact primeComplementCore_coprime p
  have hDzp : D ≤ normalizer ((zpowers (δ : G) : Subgroup G) : Set G) := fun x hx =>
    centralizer_singleton_le_normalizer_zpowers (δ : G) (mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hDab.is_comm.comm ⟨x, hx⟩ ⟨(δ : G), hdD⟩)))
  have hDC : D ≤ normalizer ((centralizer ({(δ : G)} : Set G) : Subgroup G) : Set G) := by
    have h := hDzp.trans (RankThreeTheoremC.normalizer_le_normalizer_centralizer (zpowers (δ : G)))
    rwa [zpowers_eq_closure, Subgroup.centralizer_closure] at h
  have hall : ∀ A : Subgroup G, A ≤ H → IsPGroup 2 A → D ≤ normalizer (A : Set G) →
      A ≤ Kg ⊔ (Kd ⊓ H) := by
    intro A hAH hA2 hDA r hr
    have hdN : (δ : G) ∈ normalizer (A : Set G) := hDA hdD
    have hc : r * (δ : G) * r⁻¹ * (δ : G)⁻¹ ∈ A := by
      have h1 : (δ : G) * r⁻¹ * (δ : G)⁻¹ ∈ A := (mem_normalizer_iff.mp hdN r⁻¹).mp (A.inv_mem hr)
      have : r * (δ : G) * r⁻¹ * (δ : G)⁻¹ = r * ((δ : G) * r⁻¹ * (δ : G)⁻¹) := by group
      rw [this]
      exact A.mul_mem hr h1
    have hcomm : π ⟨r, hAH hr⟩ * π δ = π δ * π ⟨r, hAH hr⟩ := by
      set c : H := ⟨r, hAH hr⟩ * δ * ⟨r, hAH hr⟩⁻¹ * δ⁻¹ with hcdef
      have hcA : (c : G) ∈ A := by
        have : (c : G) = r * (δ : G) * r⁻¹ * (δ : G)⁻¹ := rfl
        rw [this]
        exact hc
      have hcQ : π c ∈ CFSG.Open.pCore p (H ⧸ K') := by
        have : π c = (π ⟨r, hAH hr⟩ * π δ * (π ⟨r, hAH hr⟩)⁻¹) * (π δ)⁻¹ := by
          simp only [hcdef, map_mul, map_inv]
        rw [this]
        exact Subgroup.mul_mem _ (hQnormal.conj_mem _ huδ _) (Subgroup.inv_mem _ huδ)
      obtain ⟨k, hk⟩ := hA2 ⟨(c : G), hcA⟩
      have hkG : (c : G) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      have hk' : c ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hkG)
      have hπc : π c = 1 := eq_one_of_mem_isPGroup_of_pow_two_pow_eq_one hprime hodd
        (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup p) hcQ (k := k)
        (by rw [← map_pow, hk', map_one])
      have : π ⟨r, hAH hr⟩ * π δ * (π ⟨r, hAH hr⟩)⁻¹ * (π δ)⁻¹ = 1 := by
        rw [← hπc]
        simp only [hcdef, map_mul, map_inv]
      exact (mul_inv_eq_one.mp (by rw [← this]; group))
    have hzR : δ ∈ normalizer ((A.subgroupOf H : Subgroup H) : Set H) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hAH]
      exact hdN
    obtain ⟨r₀, hr₀A, hr₀z, hr₀K⟩ := exists_centralizer_mul_mem_of_commute_map hodd K'
      (hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm) hzR
      (by exact Subtype.ext hdp) (r := ⟨r, hAH hr⟩) hr hcomm
    have hr₀C : (r₀ : G) ∈ centralizer ({(δ : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hr₀z)
    have hY2 : IsPGroup 2 ((A ⊓ centralizer ({(δ : G)} : Set G) : Subgroup G)) :=
      hA2.to_inf_left
    have hYc : p.Coprime (Nat.card (A ⊓ centralizer ({(δ : G)} : Set G) : Subgroup G)) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hY2
      rw [hn]
      exact ((Nat.coprime_primes hprime Nat.prime_two).mpr hodd).pow_right n
    have hr₀Kd : (r₀ : G) ∈ Kd :=
      hKdall _ (inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers (δ : G))) hYc
        (common_normalizer_le_normalizer_inf D A _ hDA hDC) ⟨hr₀A, hr₀C⟩
    have hmemKg : (r₀ : G)⁻¹ * r ∈ Kg := by
      have h : H.subtype (r₀⁻¹ * ⟨r, hAH hr⟩) ∈ K'.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype hr₀K
      exact h
    have hprod : r = (r₀ : G) * ((r₀ : G)⁻¹ * r) := by group
    rw [sup_comm, hprod]
    exact Subgroup.mul_mem_sup ⟨hr₀Kd, r₀.2⟩ hmemKg
  have hjoin : invariantTwoJoinIn D H ≤ Kg ⊔ (Kd ⊓ H) := invariantTwoJoinIn_le_of_forall hall
  have hWc : p.Coprime (Nat.card (Kd ⊓ H : Subgroup G)) :=
    hKdc.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have hcop : p.Coprime (Nat.card (Kg ⊔ (Kd ⊓ H) : Subgroup G)) :=
    coprime_card_sup_of_normalized_coprime hKgH inf_le_right hKgN hKgc hWc
  exact (hprime.coprime_iff_not_dvd.mp hcop)
    (hH.not_coprime.trans (Subgroup.card_dvd_of_le hjoin))

end CFSG.LocalAnalysis.RankFourTheoremC
