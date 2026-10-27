module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MonsterTargets
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.MonsterAmalgamCarrier
import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding Subgroup

@[expose] def GL83Type24Source (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  GL83Type24 p i ∨ ((p = 11 ∨ p = 13) ∧ i = .sporadic .M)

@[expose] def GL83NongenerationListSource : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CatalogSimpleSections X → ∀ (p : ℕ) (R : Sylow p X)
    (K : Subgroup X), p.Prime → p ≠ 2 → 3 ≤ Open.pRank p (R : Subgroup X) →
    IsComponentOf K ⊤ → K.Normal → (R : Subgroup X) ⊓ centralizer (K : Set X) ≠ ⊥ →
    ¬ K ≤ GLBCore p 2 (R : Subgroup X) →
    ∃ i : TauCeti.CFSGIndex, Nonempty (K ⧸ center K ≃* i.Group) ∧ GL83Type24Source p i ∧
      (GL83OuterType24 p i ∨
        ∀ g ∈ (R : Subgroup X), g ^ p = 1 → g ∈ K ⊔ centralizer (K : Set X))

theorem exists_mem_orderOf_eq_of_isPGroup_ne_bot {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {A : Subgroup G} (hA : IsPGroup p A) (hne : A ≠ ⊥) :
    ∃ a ∈ A, orderOf a = p := by
  rcases hA.card_eq_or_dvd with h | h
  · exact absurd (Subgroup.eq_bot_of_card_eq A h) hne
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem eq_one_of_pPow_eq_one_of_not_dvd_natCard {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {Z : Subgroup G} (hZ : ¬ p ∣ Nat.card Z) {c : G} (hc : c ∈ Z) {m : ℕ}
    (h : c ^ (p ^ m) = 1) : c = 1 := by
  have hp : p.Prime := Fact.out
  have h1 : orderOf c ∣ p ^ m := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf c ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hc
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h1
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa using hk
  · rw [hk] at h2
    exact absurd ((dvd_pow_self p hk0.ne').trans h2) hZ

theorem conj_mem_comap_inf_of_central_kernel {L M : Type*} [Group L] [Group M] {p : ℕ}
    [Fact p.Prime] (ρ : L →* M) (hc : ρ.ker ≤ center L) (hZ : ¬ p ∣ Nat.card ρ.ker)
    {T : Subgroup L} (hT : IsPGroup p T) {Q : Subgroup M} (hQ : Q ≤ T.map ρ) {n x : L}
    (hn : ρ n ∈ normalizer (Q : Set M)) (hx : x ∈ Q.comap ρ ⊓ T) :
    n * x * n⁻¹ ∈ Q.comap ρ ⊓ T := by
  rw [Subgroup.mem_inf, Subgroup.mem_comap] at hx
  obtain ⟨hxQ, hxT⟩ := hx
  have hy : ρ (n * x * n⁻¹) ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.1 hn (ρ x)).1 hxQ
    simpa [map_mul, map_inv] using this
  obtain ⟨q, hqT, hq⟩ := Subgroup.mem_map.1 (hQ hy)
  have hcker : q⁻¹ * (n * x * n⁻¹) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hq, inv_mul_cancel]
  have hcc : Commute q (q⁻¹ * (n * x * n⁻¹)) :=
    Subgroup.mem_center_iff.1 (hc hcker) q
  obtain ⟨i, hi⟩ := hT ⟨x, hxT⟩
  obtain ⟨j, hj⟩ := hT ⟨q, hqT⟩
  have hxi : x ^ (p ^ i) = 1 := by simpa using congrArg Subtype.val hi
  have hqj : q ^ (p ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hxN : x ^ (p ^ (i + j)) = 1 := by rw [pow_add, pow_mul, hxi, one_pow]
  have hqN : q ^ (p ^ (i + j)) = 1 := by rw [add_comm, pow_add, pow_mul, hqj, one_pow]
  have hyN : (n * x * n⁻¹) ^ (p ^ (i + j)) = 1 := by
    rw [conj_pow, hxN, mul_one, mul_inv_cancel]
  have hcN : (q⁻¹ * (n * x * n⁻¹)) ^ (p ^ (i + j)) = 1 := by
    have hyq : q * (q⁻¹ * (n * x * n⁻¹)) = n * x * n⁻¹ := mul_inv_cancel_left q _
    rw [← hyq, hcc.mul_pow, hqN, one_mul] at hyN
    exact hyN
  have hc1 : q⁻¹ * (n * x * n⁻¹) = 1 :=
    eq_one_of_pPow_eq_one_of_not_dvd_natCard hZ hcker hcN
  rw [← inv_mul_eq_one.1 hc1, Subgroup.mem_inf, Subgroup.mem_comap, hq]
  exact ⟨hy, hqT⟩

section Cover

variable {X M : Type} [Group X] [Finite X] [Group M] [Finite M] {p : ℕ} [Fact p.Prime]

theorem comap_normalizer_le_glbCore (R : Sylow p X) {K : Subgroup X} [K.Normal] (ρ : K →* M)
    (hc : ρ.ker ≤ center K) (hZ : ¬ p ∣ Nat.card ρ.ker) {z : X} (hzR : z ∈ (R : Subgroup X))
    (hzC : z ∈ centralizer (K : Set X)) (hzo : orderOf z = p) (hzK : z ∉ K) {Q : Subgroup M}
    (hQ : Q ≤ ((R : Subgroup X).subgroupOf K).map ρ) (hQrk : 1 ≤ Open.pRank p Q) :
    (normalizer (Q : Set M)).comap ρ ≤ (GLBCore p 2 (R : Subgroup X)).comap K.subtype := by
  have hp : p.Prime := Fact.out
  have hzp : z ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  set S : Sylow p K := QuasiDihedralFusion.sylowInfNormal R K
  have hS : (S : Subgroup K) = (R : Subgroup X).subgroupOf K :=
    QuasiDihedralFusion.sylowInfNormal_coe R K
  have hSR : ∀ x : K, x ∈ (S : Subgroup K) → (x : X) ∈ (R : Subgroup X) := fun x hx => by
    rw [hS] at hx
    exact hx
  have hQS : Q ≤ (S : Subgroup K).map ρ := by rw [hS]; exact hQ
  intro n hn
  have hQbot : Q ≠ ⊥ := by
    intro h
    obtain ⟨E, hEQ, -, hE⟩ := GH74.Uniqueness.SU.SU1.exists_pRank hp.one_lt Q
    rw [h, le_bot_iff] at hEQ
    rw [hEQ, Subgroup.card_bot] at hE
    have := Nat.one_lt_pow (by omega : Open.pRank p Q ≠ 0) hp.one_lt
    omega
  set Qp : Subgroup K := Q.comap ρ ⊓ (S : Subgroup K)
  have hQmap : Qp.map ρ = Q := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_inf.1 hx).1
    · intro y hy
      obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.1 (hQS hy)
      exact ⟨t, Subgroup.mem_inf.2 ⟨hy, htT⟩, rfl⟩
  have hQne : Qp ≠ ⊥ := by
    intro h
    apply hQbot
    rw [← hQmap, h, Subgroup.map_bot]
  obtain ⟨s, hsQ, hso⟩ :=
    exists_mem_orderOf_eq_of_isPGroup_ne_bot (S.isPGroup'.to_le inf_le_right) hQne
  have haord : orderOf (s : X) = p := by rw [Subgroup.orderOf_coe, hso]
  have hap : (s : X) ^ p = 1 := by rw [← haord]; exact pow_orderOf_eq_one _
  have hsK : (s : X) ∈ K := s.2
  have hcomm : (s : X) * z = z * (s : X) := Subgroup.mem_centralizer_iff.1 hzC _ hsK
  have ha1 : (s : X) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at haord
    exact hp.one_lt.ne haord
  have hzna : z ∉ Subgroup.zpowers (s : X) := fun h => hzK (Subgroup.zpowers_le.2 hsK h)
  obtain ⟨hel, hcard⟩ :=
    GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp hap hzp ha1 hzna hcomm
  set Q' : Subgroup X := Qp.map K.subtype ⊔ Subgroup.zpowers z
  have hQ'R : Q' ≤ (R : Subgroup X) := by
    refine sup_le ?_ (Subgroup.zpowers_le.2 hzR)
    rintro _ ⟨x, hx, rfl⟩
    exact hSR x (Subgroup.mem_inf.1 hx).2
  have hrank : 2 ≤ Open.pRank p Q' := by
    refine GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt
      (E := Subgroup.zpowers (s : X) ⊔ Subgroup.zpowers z) ?_ hel hcard
    have hsmem : (s : X) ∈ Qp.map K.subtype := Subgroup.mem_map.2 ⟨s, hsQ, rfl⟩
    exact sup_le_sup_right (Subgroup.zpowers_le.2 hsmem) _
  have hn' : ρ n ∈ normalizer (Q : Set M) := hn
  have hnormQ : n ∈ normalizer (Qp : Set K) := by
    have hconj : ∀ m : K, ρ m ∈ normalizer (Q : Set M) → ∀ x ∈ Qp, m * x * m⁻¹ ∈ Qp :=
      fun m hm x hx => conj_mem_comap_inf_of_central_kernel ρ hc hZ S.isPGroup' hQS hm hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj n hn' h hh, fun hh => ?_⟩
    have hninv : ρ n⁻¹ ∈ normalizer (Q : Set M) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hn'
    have := hconj n⁻¹ hninv _ hh
    simpa [mul_assoc] using this
  have hnormX : (n : X) ∈ normalizer (Q' : Set X) := by
    have h1 : (n : X) ∈ normalizer ((Qp.map K.subtype : Subgroup X) : Set X) :=
      Subgroup.le_normalizer_map (H := Qp) K.subtype (Subgroup.mem_map.2 ⟨n, hnormQ, rfl⟩)
    have hnz : (n : X) * z = z * (n : X) := Subgroup.mem_centralizer_iff.1 hzC n n.2
    have h2 : (n : X) ∈ normalizer ((Subgroup.zpowers z : Subgroup X) : Set X) := by
      have hcent : (n : X) ∈ centralizer ((Subgroup.zpowers z : Subgroup X) : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
        exact (Commute.zpow_left hnz.symm k).eq
      exact Subgroup.centralizer_le_normalizer _ hcent
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨h1, h2⟩
  have hB : normalizer (Q' : Set X) ≤ GLBCore p 2 (R : Subgroup X) :=
    le_sSup ⟨Q', hQ'R, hrank, rfl⟩
  exact hB hnormX

theorem le_glbCore_two_of_central_cover [Nontrivial M] (R : Sylow p X) {K : Subgroup X}
    [K.Normal] (ρ : K →* M) (hρ : Function.Surjective ρ) (hker : ρ.ker = center K)
    (hZ : ¬ p ∣ Nat.card (center K)) (hRK : (R : Subgroup X) ⊓ centralizer (K : Set X) ≠ ⊥)
    (hΓ : ∀ T : Sylow p M, GLBCore p 1 (T : Subgroup M) = ⊤) :
    K ≤ GLBCore p 2 (R : Subgroup X) := by
  set A : Subgroup X := (R : Subgroup X) ⊓ centralizer (K : Set X)
  have hAp : IsPGroup p A := R.isPGroup'.to_inf_left
  obtain ⟨z, hzA, hzo⟩ := exists_mem_orderOf_eq_of_isPGroup_ne_bot hAp hRK
  obtain ⟨hzR, hzC⟩ := Subgroup.mem_inf.1 hzA
  have hZ' : ¬ p ∣ Nat.card ρ.ker := by rw [hker]; exact hZ
  have hzK : z ∉ K := by
    intro hzK
    have hmem : (⟨z, hzK⟩ : K) ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzC g g.2)
    have := Subgroup.orderOf_dvd_natCard (center K) hmem
    rw [Subgroup.orderOf_mk, hzo] at this
    exact hZ this
  set S' : Sylow p M := (QuasiDihedralFusion.sylowInfNormal R K).mapSurjective hρ
  have key : ∀ Q : Subgroup M, Q ≤ (S' : Subgroup M) → 1 ≤ Open.pRank p Q →
      (normalizer (Q : Set M)).comap ρ ≤ (GLBCore p 2 (R : Subgroup X)).comap K.subtype :=
    fun Q hQ hQrk => comap_normalizer_le_glbCore R ρ hker.le hZ' hzR hzC hzo hzK
      (by rw [← QuasiDihedralFusion.sylowInfNormal_coe R K]; exact hQ) hQrk
  set B' : Subgroup K := (GLBCore p 2 (R : Subgroup X)).comap K.subtype
  have hne : ∃ Q : Subgroup M, Q ≤ (S' : Subgroup M) ∧ 1 ≤ Open.pRank p Q := by
    by_contra hcon
    push Not at hcon
    have h1 : GLBCore p 1 (S' : Subgroup M) = ⊥ := by
      refine le_bot_iff.1 (sSup_le ?_)
      rintro N ⟨Q, hQS, hQ1, rfl⟩
      exact absurd hQ1 (not_le.2 (hcon Q hQS))
    rw [hΓ S'] at h1
    obtain ⟨m, hm⟩ := exists_ne (1 : M)
    have : m ∈ (⊤ : Subgroup M) := Subgroup.mem_top m
    rw [h1] at this
    exact hm (Subgroup.mem_bot.1 this)
  obtain ⟨Q₀, hQ₀S, hQ₀⟩ := hne
  have hker' : ρ.ker ≤ B' := by
    intro c hc'
    have : c ∈ (normalizer (Q₀ : Set M)).comap ρ := by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hc']
      exact Subgroup.one_mem _
    exact key Q₀ hQ₀S hQ₀ this
  have hmap : B'.map ρ = ⊤ := by
    rw [eq_top_iff, ← hΓ S']
    refine sSup_le ?_
    rintro N ⟨Q, hQS, hQ1, rfl⟩
    calc normalizer (Q : Set M) = ((normalizer (Q : Set M)).comap ρ).map ρ :=
          (Subgroup.map_comap_eq_self_of_surjective hρ _).symm
      _ ≤ B'.map ρ := Subgroup.map_mono (key Q hQS hQ1)
  have hB'top : B' = ⊤ := by
    have h := Subgroup.comap_map_eq (f := ρ) B'
    rw [hmap, Subgroup.comap_top, sup_eq_left.2 hker'] at h
    exact h.symm
  intro k hk
  have : (⟨k, hk⟩ : K) ∈ B' := hB'top ▸ Subgroup.mem_top _
  exact this

open RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster in
theorem le_glbCore_two_of_gamma_one_of_kernelTrivial (R : Sylow p X) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) [K.Normal]
    (hRK : (R : Subgroup X) ⊓ centralizer (K : Set X) ≠ ⊥) (e : K ⧸ center K ≃* M)
    (hkt : KernelTrivialAt M p) (hΓ : ∀ T : Sylow p M, GLBCore p 1 (T : Subgroup M) = ⊤) :
    K ≤ GLBCore p 2 (R : Subgroup X) := by
  have hq : Open.IsQuasisimple K := hK.2.2
  have : Group.IsPerfect K := ⟨hq.1⟩
  have : IsSimpleGroup (K ⧸ center K) := hq.2
  haveI : Nontrivial M := e.injective.nontrivial
  let ρ : K →* M := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = center K := by
    ext x
    simp [ρ]
  haveI : Group.IsPerfect M := Group.IsPerfect.ofSurjective hρ
  have hZ : ¬ p ∣ Nat.card (center K) := by
    have h1 := card_ker_dvd_card_hopfMultiplier ρ hρ hker.le
    rw [hker] at h1
    exact fun h => not_dvd_card_hopfMultiplier_of_kernelTrivialAt hkt (h.trans h1)
  exact le_glbCore_two_of_central_cover R ρ hρ hker hZ hRK hΓ

end Cover

section Certified


open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

theorem le_glbCore_of_monster {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p = 11 ∨ p = 13) (R : Sylow p X) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hKn : K.Normal) (hRK : (R : Subgroup X) ⊓ centralizer (K : Set X) ≠ ⊥)
    (e : K ⧸ center K ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :
    K ≤ GLBCore p 2 (R : Subgroup X) := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Finite (TauCeti.CFSGIndex.sporadic .M).Group := Finite.of_equiv _ e.toEquiv
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
  have hkt : KernelTrivialAt (TauCeti.CFSGIndex.sporadic .M).Group p := by
    rcases hp with rfl | rfl
    · exact (kernelTrivialAt_iff_of_mulEquiv b 11).1 kernelTrivialAt_carrier_M_eleven_of_amalgam
    · exact (kernelTrivialAt_iff_of_mulEquiv b 13).1 kernelTrivialAt_carrier_M_thirteen_of_amalgam
  have hΓ : SporGammaOneAt .M p := by
    rcases hp with rfl | rfl
    · exact Norton.sporGammaOneAt_M_eleven_holds
    · exact Norton.sporGammaOneAt_M_thirteen_holds
  exact le_glbCore_two_of_gamma_one_of_kernelTrivial R hK hRK e hkt fun T =>
    hΓ _ ⟨MulEquiv.refl _⟩ T

theorem gl83NongenerationList_of_source (h : GL83NongenerationListSource) :
    GL83NongenerationList := by
  intro X _ _ hcat p R K hp hp2 hrk hK hKn hC hnot
  obtain ⟨i, hi, hty | ⟨hp11, hiM⟩, hout⟩ := h X hcat p R K hp hp2 hrk hK hKn hC hnot
  · exact ⟨i, hi, hty, hout⟩
  · subst hiM
    obtain ⟨e⟩ := hi
    exact absurd (le_glbCore_of_monster hp11 R hK hKn hC e) hnot

end Certified

end CFSG.LocalAnalysis.RankFourTheoremC
