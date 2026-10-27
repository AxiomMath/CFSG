module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrStruct
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrPow
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.ParabAutIrr
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

@[expose] def PerfectJoinHub (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ (S₀ : Sylow 2 X) (J : Subgroup X), Subgroup.normalizer ((S₀ : Subgroup X) : Set X) ≤ J →
    ∀ A : Subgroup X, A ≤ J → IsPGroup p A → A ≤ perfectJoin J

theorem PerfectJoinHub.of_mulEquiv {p : ℕ} {X X' : Type*} [Group X] [Group X'] [Finite X']
    (e : X ≃* X') (h : PerfectJoinHub p X) : PerfectJoinHub p X' := by
  intro S₀ J hNJ A hAJ hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_equiv X' e.symm.toEquiv
  let S : Sylow 2 X := S₀.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hNS : Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ J.map e.symm.toMonoidHom := by
    intro x hx
    refine ⟨e x, hNJ (Subgroup.mem_normalizer_fintype fun s hs => ?_), by simp⟩
    have h1 : e.symm s ∈ (S : Subgroup X) := ⟨s, hs, rfl⟩
    obtain ⟨s', hs', hse⟩ := (Subgroup.mem_normalizer_iff.1 hx (e.symm s)).1 h1
    have : e x * s * (e x)⁻¹ = s' := by
      apply e.symm.injective
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
      exact hse.symm
    rw [this]
    exact hs'
  have hA' := h S (J.map e.symm.toMonoidHom) hNS (A.map e.symm.toMonoidHom)
    (Subgroup.map_mono hAJ) (hA.map _)
  have hJ : (J.map e.symm.toMonoidHom).map e.toMonoidHom = J := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id J
    ext x
    simp
  intro a ha
  have h2 : e.symm a ∈ perfectJoin (J.map e.symm.toMonoidHom) := hA' ⟨a, ha, rfl⟩
  have h3 := map_perfectJoin_le e.toMonoidHom hJ.le ⟨_, h2, rfl⟩
  simpa using h3

section Borel

variable {K : Type*} {Y : Type} [Group K] [Group Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem pSubgroup_le_perfectJoin_of_borelQuotient [Finite K] [Finite Y]
    (h : BorelQuotient D n H π M) {q : ℕ} (hq4 : 4 ≤ q) (hrank : ∀ i, RankOneNode D i q)
    (S₀ : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((S₀ : Subgroup Y) : Set Y) ≤ J)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpM : ¬ p ∣ M) {A : Subgroup Y} (hAJ : A ≤ J)
    (hA : IsPGroup p A) : A ≤ perfectJoin J := by
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq S₀
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel D H).map π' ≤ J := by
    rw [← hNπ]
    exact hNJ
  have hJeq := eq_map_borel_sup_of_le hQ.ct hQ.extras hπ' hBJ
  set T : Subgroup Y := (⨆ i, H i).map π' with hTdef
  set P : Subgroup Y := perfectJoin J with hPdef
  have hTJ : T ≤ J := (Subgroup.map_mono iSup_le_borel).trans hBJ
  have hSJ : (S₀ : Subgroup Y) ≤ J := by
    rw [hT]
    exact (Subgroup.map_mono posUnipotent_le_borel).trans hBJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 (S₀ : Subgroup Y) := S₀.isPGroup'
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.torus_mul_comm ha hb]
  have hTpow : ∀ t ∈ T, t ^ M = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hQ.pow_eq_one_of_mem_iSup ha, map_one]
  have hTodd : ∀ t ∈ T, ∃ m : ℕ, Odd m ∧ t ^ m = 1 := fun t ht => ⟨M, h.odd, hTpow t ht⟩
  have hTS : T ≤ Subgroup.normalizer ((S₀ : Subgroup Y) : Set Y) := by
    rw [hT]
    exact (Subgroup.map_mono ((iSup_le_borel).trans
      (borel_le_normalizer_posUnipotent hQ.ct))).trans (Subgroup.le_normalizer_map π')
  have hgen : J ≤ T ⊔ (S₀ : Subgroup Y) ⊔ P := by
    rw [hT]
    refine hJeq.le.trans (sup_le ?_ ?_)
    · calc (borel D H).map π'
          = (⨆ i, H i).map π' ⊔ (posUnipotent D).map π' := by
            simp only [CFSG.LieType.Steinberg.borel, Subgroup.map_sup]
        _ ≤ _ := le_sup_left
    · refine iSup₂_le fun i hi => ?_
      have hLi : (rankOne D.rootGroup i).map π' ≤ J := by
        refine le_trans ?_ hJeq.ge
        exact le_sup_of_le_right (le_iSup₂_of_le (f := fun i
          (_ : i ∈ negIndices D (J.comap π')) => (rankOne D.rootGroup i).map π') i hi le_rfl)
      refine le_sup_right.trans' (le_perfectJoin hLi ?_)
      rw [← Subgroup.map_commutator, (hrank i).perfect hq4]
  obtain ⟨hcore, -⟩ := borelLike_facts hS2 hSJ hTJ hTc hTodd hTS hgen
  have hNn : ((twoCore J).subgroupOf J).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simpa using conj_mem_twoCore (Subgroup.le_normalizer g.2) hx⟩
  have hTN : T ≤ Subgroup.normalizer ((P ⊔ (S₀ : Subgroup Y) : Subgroup Y) : Set Y) :=
    fun t ht => mem_normalizer_sup (le_normalizer_perfectJoin J (hTJ ht)) (hTS ht)
  have hAN : A ≤ P ⊔ (S₀ : Subgroup Y) := by
    intro a ha
    have haJ := hAJ ha
    have h1 : a ∈ T ⊔ (P ⊔ (S₀ : Subgroup Y)) := by
      have hEq : T ⊔ (S₀ : Subgroup Y) ⊔ P = T ⊔ (P ⊔ (S₀ : Subgroup Y)) := by
        rw [sup_assoc, sup_comm (S₀ : Subgroup Y) P]
      rw [← hEq]
      exact hgen haJ
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right T _ hTN,
      Set.mem_mul] at h1
    obtain ⟨t, ht, m, hm, rfl⟩ := h1
    have htJ : t ∈ J := hTJ ht
    set φ := QuotientGroup.mk' ((twoCore J).subgroupOf J) with hφ
    have he : φ ⟨t * m, haJ⟩ = φ ⟨t, htJ⟩ := by
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have : ((⟨t * m, haJ⟩ : ↥J)⁻¹ * ⟨t, htJ⟩ : ↥J).1 = m⁻¹ := by simp
      rw [this, hcore]
      exact Subgroup.inv_mem _ hm
    have hpowT : φ ⟨t, htJ⟩ ^ M = 1 := by
      rw [← map_pow]
      have : (⟨t, htJ⟩ : ↥J) ^ M = 1 := Subtype.ext (by simpa using hTpow t ht)
      rw [this, map_one]
    obtain ⟨k, hk⟩ := hA ⟨t * m, ha⟩
    have hpowA : φ ⟨t * m, haJ⟩ ^ p ^ k = 1 := by
      rw [← map_pow]
      have : (⟨t * m, haJ⟩ : ↥J) ^ p ^ k = 1 := Subtype.ext (by
        have := congrArg Subtype.val hk
        simpa using this)
      rw [this, map_one]
    have hcop : Nat.Coprime (p ^ k) M :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
    have hd1 : orderOf (φ ⟨t * m, haJ⟩) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hpowA
    have hd2 : orderOf (φ ⟨t * m, haJ⟩) ∣ M := by
      rw [he]
      exact orderOf_dvd_of_pow_eq_one hpowT
    have hord : orderOf (φ ⟨t * m, haJ⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    rw [orderOf_eq_one_iff, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hord
    rw [← hcore]
    exact hord
  exact pSubgroup_le_perfectJoin hp hp2 hS2 hSJ hAN hA

theorem perfectJoinHub_of_borelQuotient [Finite K] [Finite Y] (h : BorelQuotient D n H π M)
    {q : ℕ} (hq4 : 4 ≤ q) (hrank : ∀ i, RankOneNode D i q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : ¬ p ∣ M) : PerfectJoinHub p Y :=
  fun S₀ J hNJ _ hAJ hA =>
    pSubgroup_le_perfectJoin_of_borelQuotient h hq4 hrank S₀ J hNJ hp hp2 hpM hAJ hA

end Borel

namespace ToralCensus

section Central

variable {G X : Type*} [Group G] [Group X] (ψ : G →* X)

theorem normalizer_map_le_map [Finite G] (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center G) (hodd : Odd (Nat.card ψ.ker)) {T J : Subgroup G}
    (hT : IsPGroup 2 T) (hNJ : Subgroup.normalizer (T : Set G) ≤ J) :
    Subgroup.normalizer ((T.map ψ : Subgroup X) : Set X) ≤ J.map ψ := by
  intro y hy
  obtain ⟨x, rfl⟩ := hψ y
  refine ⟨x, hNJ ?_, rfl⟩
  apply Subgroup.mem_normalizer_fintype
  intro t ht
  have h1 : ψ (x * t * x⁻¹) ∈ T.map ψ := by
    have := (Subgroup.mem_normalizer_iff.1 hy (ψ t)).1 ⟨t, ht, rfl⟩
    simpa using this
  obtain ⟨s, hs, hse⟩ := h1
  have hz : s⁻¹ * (x * t * x⁻¹) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hse, inv_mul_cancel]
  have hzM : (s⁻¹ * (x * t * x⁻¹)) ^ Nat.card ψ.ker = 1 := by
    have := pow_card_eq_one' (G := ψ.ker) (x := ⟨_, hz⟩)
    simpa using congrArg Subtype.val this
  have hcen := Subgroup.mem_center_iff.1 (hker hz)
  have e : x * t * x⁻¹ = s * (s⁻¹ * (x * t * x⁻¹)) := by group
  have hcomm : Commute s (x * t * x⁻¹) := by
    have hc : Commute s (s⁻¹ * (x * t * x⁻¹)) := hcen s
    rw [e]
    exact (Commute.refl s).mul_right hc
  obtain ⟨r, hr⟩ := hT ⟨s, hs⟩
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have hr' : s ^ 2 ^ r = 1 := congrArg Subtype.val hr
  have hk' : (x * t * x⁻¹) ^ 2 ^ k = 1 := by
    have htk : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [conj_pow, htk, mul_one, mul_inv_cancel]
  have hz1 := eq_one_of_central_odd hodd hzM rfl hcomm hr' hk'
  have : x * t * x⁻¹ = s := by rw [e, hz1, mul_one]
  rw [this]
  exact hs

theorem map_perfectJoin_eq (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center G)
    {J : Subgroup G} (hkJ : ψ.ker ≤ J) : (perfectJoin J).map ψ = perfectJoin (J.map ψ) := by
  refine le_antisymm (map_perfectJoin_le ψ le_rfl) ?_
  obtain ⟨W, hW, hWc, hWe⟩ := exists_perfect_map_eq ψ hker (perfectJoin_perfect (J.map ψ))
    (by rw [MonoidHom.range_eq_top.2 hψ]; exact le_top)
  rw [← hWe]
  refine Subgroup.map_mono (le_perfectJoin ?_ hW)
  intro w hw
  obtain ⟨j, hj, hje⟩ := perfectJoin_le (J.map ψ) (hWc hw)
  have hk : j⁻¹ * w ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hje, inv_mul_cancel]
  simpa using J.mul_mem hj (hkJ hk)

theorem le_of_map_le_map_of_central [Finite G] (hker : ψ.ker ≤ Subgroup.center G) {p : ℕ}
    (hp : p.Prime) (hpk : ¬ p ∣ Nat.card ψ.ker) {A B : Subgroup G} (hA : IsPGroup p A)
    (h : A.map ψ ≤ B.map ψ) : A ≤ B := by
  intro a ha
  obtain ⟨b, hb, hbe⟩ := h ⟨a, ha, rfl⟩
  have hc : b⁻¹ * a ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbe, inv_mul_cancel]
  have hcN : (b⁻¹ * a) ^ Nat.card ψ.ker = 1 := by
    have := pow_card_eq_one' (G := ψ.ker) (x := ⟨_, hc⟩)
    simpa using congrArg Subtype.val this
  have hcomm : Commute b (b⁻¹ * a) := Subgroup.mem_center_iff.1 (hker hc) b
  have haN : a ^ Nat.card ψ.ker = b ^ Nat.card ψ.ker :=
    calc a ^ Nat.card ψ.ker = (b * (b⁻¹ * a)) ^ Nat.card ψ.ker := by rw [mul_inv_cancel_left]
      _ = b ^ Nat.card ψ.ker * (b⁻¹ * a) ^ Nat.card ψ.ker := hcomm.mul_pow _
      _ = b ^ Nat.card ψ.ker := by rw [hcN, mul_one]
  obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
  have hk' : a ^ p ^ k = 1 := congrArg Subtype.val hk
  have hcop : (Nat.card ψ.ker).Coprime (orderOf a) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk')
      (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk).symm)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, haN]
  exact B.pow_mem (B.pow_mem hb _) m

end Central

end ToralCensus

open ToralCensus in
theorem pSubgroup_le_perfectJoin_of_quotient {G X : Type*} [Group G] [Group X] [Finite G]
    {ψ : G →* X} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center G)
    (hodd : Odd (Nat.card ψ.ker)) {p : ℕ} (hp : p.Prime) (hpk : ¬ p ∣ Nat.card ψ.ker)
    (hH : PerfectJoinHub p X) (T : Sylow 2 G) {J : Subgroup G}
    (hNJ : Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ J) {A : Subgroup G} (hAJ : A ≤ J)
    (hA : IsPGroup p A) : A ≤ perfectJoin J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkJ : ψ.ker ≤ J :=
    hker.trans ((Subgroup.center_le_normalizer ((T : Subgroup G) : Set G)).trans hNJ)
  have hNS : Subgroup.normalizer (((T.mapSurjective hψ : Sylow 2 X) : Subgroup X) : Set X) ≤
      J.map ψ := by
    rw [Sylow.coe_mapSurjective]
    exact normalizer_map_le_map ψ hψ hker hodd T.isPGroup' hNJ
  have h1 := hH (T.mapSurjective hψ) (J.map ψ) hNS (A.map ψ) (Subgroup.map_mono hAJ) (hA.map ψ)
  rw [← map_perfectJoin_eq ψ hψ hker hkJ] at h1
  exact le_of_map_le_map_of_central ψ hker hp hpk hA h1

theorem pSubgroup_le_perfectJoin_of_parabolic {Y : Type*} [Group Y] [Finite Y]
    {L J : Subgroup Y} (hP : IsParabolicTwo L J) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    {p : ℕ} (hp : p.Prime) (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hH : PerfectJoinHub p (↥L ⧸ Subgroup.center ↥L)) {A : Subgroup Y} (hAJ : A ≤ J)
    (hA : IsPGroup p A) : A ≤ perfectJoin J := by
  obtain ⟨hJL, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : (QuotientGroup.mk' (Subgroup.center ↥L)).ker = Subgroup.center ↥L :=
    QuotientGroup.ker_mk' _
  let T' : Sylow 2 ↥L := (hT2.comap_subtype (K := L)).toSylow hTi
  have hNJ' : Subgroup.normalizer ((T' : Subgroup ↥L) : Set ↥L) ≤ J.subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hNJ ⟨x.2, Subgroup.mem_normalizer_fintype fun t ht => ?_⟩
    have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ (T' : Subgroup ↥L) := by
      simpa [T', Subgroup.mem_subgroupOf] using ht
    have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨t, hTL ht⟩).1 h1
    simpa [T', Subgroup.mem_subgroupOf] using h2
  have hAJ' : A.subgroupOf L ≤ J.subgroupOf L := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hAJ (Subgroup.mem_subgroupOf.1 hx))
  have hodd' : Odd (Nat.card (QuotientGroup.mk' (Subgroup.center ↥L)).ker) := by
    rw [hker]
    exact hodd
  have hpZ' : ¬ p ∣ Nat.card (QuotientGroup.mk' (Subgroup.center ↥L)).ker := by
    rw [hker]
    exact hpZ
  have h := pSubgroup_le_perfectJoin_of_quotient (QuotientGroup.mk'_surjective _) hker.le
    hodd' hp hpZ' hH T' hNJ' hAJ' (hA.comap_subtype (K := L))
  intro a ha
  have hmem : (⟨a, hJL (hAJ ha)⟩ : ↥L) ∈ perfectJoin (J.subgroupOf L) := h ha
  have hle : (J.subgroupOf L).map L.subtype ≤ J := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  exact map_perfectJoin_le L.subtype hle ⟨_, hmem, rfl⟩

@[expose] def IndexTorusFree (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .A _ q | .B _ q | .D _ q | .G2 q => q.card = 2 ∨ ¬ p ∣ q.card - 1
  | .twistedA _ q | .twistedD _ q => q.card = 2 ∨ ¬ p ∣ q.card ^ 2 - 1
  | _ => False

namespace ToralCensus

theorem exponent_eq_one_or_two_le {q : TauCeti.PrimePower} (hq : q.p = 2) {P : ℕ → Prop}
    (h : q.card = 2 ∨ P q.card) : q.exponent = 1 ∨ (2 ≤ q.exponent ∧ P (2 ^ q.exponent)) := by
  have hc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
  have := q.exponent_pos
  by_cases he : q.exponent = 1
  · exact Or.inl he
  · refine Or.inr ⟨by omega, ?_⟩
    rcases h with h2 | hP
    · exact absurd (Nat.pow_right_injective (le_refl 2) (hc.symm.trans h2 |>.trans
        (pow_one 2).symm)) he
    · rwa [hc] at hP

end ToralCensus

end CFSG.AGLEmbedding
