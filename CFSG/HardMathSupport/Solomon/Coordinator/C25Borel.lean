module

public import CFSG.HardMathSupport.Solomon.Coordinator.C25ON
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance

section TwoLocal

variable {W : Type*} [Group W] [Finite W]

theorem c25_pRank_bddAbove (W : Type*) [Group W] [Finite W] :
    BddAbove {k | ∃ H : Subgroup W, IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k} := by
  refine ⟨Nat.card W, ?_⟩
  rintro k ⟨H, -, rfl⟩
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) H
  have h1 : CFSG.Open.pRank 3 H < 3 ^ CFSG.Open.pRank 3 H := Nat.lt_pow_self (by norm_num)
  have h2 : Nat.card E ≤ Nat.card W := Subgroup.card_le_card_group E
  omega

theorem c25_exists_twoLocal {n : ℕ} (hn : 0 < n) (h : n ≤ GLATwoLocalRank 3 W) :
    ∃ P : Subgroup W, P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧
      n ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (P : Set W)) := by
  unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank at h
  have hne : {k | ∃ H : Subgroup W, IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at h
    simp at h
    omega
  have hmem := Nat.sSup_mem hne (c25_pRank_bddAbove W)
  obtain ⟨H, ⟨P, hP, hP2, rfl⟩, hk⟩ := hmem
  exact ⟨P, hP, hP2, h.trans hk.ge⟩

theorem c25_le_twoLocal {n : ℕ} {P : Subgroup W} (hP : P ≠ ⊥) (hP2 : IsPGroup 2 ↥P)
    (h : n ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (P : Set W))) : n ≤ GLATwoLocalRank 3 W :=
  h.trans (le_csSup (c25_pRank_bddAbove W) ⟨_, ⟨P, hP, hP2, rfl⟩, rfl⟩)

end TwoLocal

section Lift

theorem c25_exists_elemAbelian_lift_hom {Z W : Type*} [Group Z] [Finite Z] [Group W]
    (f : Z →* W) (hf : Function.Surjective f) (hker : ¬ 3 ∣ Nat.card f.ker) {E : Subgroup W}
    (hE : IsElemAbelian 3 E) :
    ∃ S : Subgroup Z, IsElemAbelian 3 S ∧ S.map f = E ∧ Nat.card S = Nat.card E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let e : Z ⧸ f.ker ≃* W := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) := c25_isElemAbelian_map _ hE
  obtain ⟨S, hS, hSmap, hScard⟩ := exists_elemAbelian_lift (p := 3) f.ker hker hE'
  refine ⟨S, hS, ?_, ?_⟩
  · have h1 : f = (e.toMonoidHom).comp (QuotientGroup.mk' f.ker) := by
      ext x
      rfl
    rw [h1, ← Subgroup.map_map, hSmap, Subgroup.map_map]
    have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id W := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  · rw [hScard]
    exact Subgroup.card_map_of_injective e.symm.injective

end Lift

section InvSylow

variable {P : Type*} [Group P] [Finite P] {A : Type*} [Group A] [MulDistribMulAction A P]

theorem c25_exists_invariant_sylow (hA : IsPGroup 3 A) (hcop : ¬ 3 ∣ Nat.card P) :
    ∃ S : Sylow 2 P, ∀ (a : A) (x : P), x ∈ (S : Subgroup P) → a • x ∈ (S : Subgroup P) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let starting : Sylow 2 P := Classical.choice inferInstance
  have hnotdvd : ¬ 3 ∣ Nat.card (Sylow 2 P) := by
    intro hdiv
    exact hcop (hdiv.trans (starting.card_dvd_index.trans (starting : Subgroup P).index_dvd_card))
  obtain ⟨S, hfixed⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 P) hnotdvd
  refine ⟨S, ?_⟩
  intro a x hx
  have hsmul : a • S = S := MulAction.mem_fixedPoints.mp hfixed a
  have hmemsmul : a • x ∈ ((a • S : Sylow 2 P) : Subgroup P) := by
    rw [Sylow.pointwise_smul_def]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x, hx, rfl⟩
  rw [hsmul] at hmemsmul
  exact hmemsmul

end InvSylow

section Pre

variable {G : Type} [Group G] [Finite G]

@[expose] def c25Pre (K : Subgroup G) (U : Subgroup (barOf 3 K)) : Subgroup G :=
  (U.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K))).map K.subtype

omit [Finite G] in
theorem mem_c25Pre {K : Subgroup G} {U : Subgroup (barOf 3 K)} {g : G} :
    g ∈ c25Pre K U ↔ ∃ hg : g ∈ K, (QuotientGroup.mk (⟨g, hg⟩ : ↥K) : barOf 3 K) ∈ U := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

omit [Finite G] in
theorem c25Pre_le {K : Subgroup G} (U : Subgroup (barOf 3 K)) : c25Pre K U ≤ K := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

omit [Finite G] in
theorem c25_mem_normalizer_pre {K : Subgroup G} {U : Subgroup (barOf 3 K)} {s : G} (hs : s ∈ K)
    (hsU : (QuotientGroup.mk (⟨s, hs⟩ : ↥K) : barOf 3 K) ∈
      Subgroup.normalizer (U : Set (barOf 3 K))) : s ∈ Subgroup.normalizer (c25Pre K U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hconj : ∀ hh : h ∈ K, s * h * s⁻¹ ∈ K ∧
      (QuotientGroup.mk (⟨s * h * s⁻¹, K.mul_mem (K.mul_mem hs hh) (K.inv_mem hs)⟩ : ↥K) :
        barOf 3 K) = QuotientGroup.mk (⟨s, hs⟩ : ↥K) * QuotientGroup.mk (⟨h, hh⟩ : ↥K) *
          (QuotientGroup.mk (⟨s, hs⟩ : ↥K))⁻¹ :=
    fun hh => ⟨K.mul_mem (K.mul_mem hs hh) (K.inv_mem hs), rfl⟩
  constructor
  · rintro hP
    obtain ⟨hh, hU⟩ := mem_c25Pre.1 hP
    refine mem_c25Pre.2 ⟨(hconj hh).1, ?_⟩
    rw [(hconj hh).2]
    exact (Subgroup.mem_normalizer_iff.1 hsU _).1 hU
  · intro hP
    obtain ⟨hh', hU'⟩ := mem_c25Pre.1 hP
    have hh : h ∈ K := by
      have := K.mul_mem (K.mul_mem (K.inv_mem hs) hh') hs
      simpa [mul_assoc] using this
    refine mem_c25Pre.2 ⟨hh, ?_⟩
    rw [(hconj hh).2] at hU'
    exact (Subgroup.mem_normalizer_iff.1 hsU _).2 hU'

omit [Finite G] in
theorem c25_mem_normalizer_pre_of_mem_dQ {K : Subgroup G} (U : Subgroup (barOf 3 K)) {g : G}
    (hg : g ∈ dQ K) : g ∈ Subgroup.normalizer (c25Pre K U : Set G) := by
  have hgN : g ∈ Subgroup.normalizer (K : Set G) := (mem_dQ.1 hg).1
  have hb1 : barAut 3 K ⟨g, hgN⟩ = 1 :=
    (LocalBalance.Lemma54Ns.mem_centralizerQuot_iff_barAut' 3 (J := K) ⟨g, hgN⟩).1 hg
  have hconj : ∀ (h : G) (hh : h ∈ K) (hgh : g * h * g⁻¹ ∈ K),
      (QuotientGroup.mk (⟨g * h * g⁻¹, hgh⟩ : ↥K) : barOf 3 K) = QuotientGroup.mk (⟨h, hh⟩ : ↥K) := by
    intro h hh hgh
    have := congrArg (fun φ : MulAut (barOf 3 K) => φ (QuotientGroup.mk ⟨h, hh⟩)) hb1
    simp only [MulAut.one_apply] at this
    rw [barAut_mk] at this
    exact this
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hP
    obtain ⟨hh, hU⟩ := mem_c25Pre.1 hP
    have hgh : g * h * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hgN h).1 hh
    refine mem_c25Pre.2 ⟨hgh, ?_⟩
    rw [hconj h hh hgh]
    exact hU
  · intro hP
    obtain ⟨hgh, hU⟩ := mem_c25Pre.1 hP
    have hh : h ∈ K := (Subgroup.mem_normalizer_iff.1 hgN h).2 hgh
    refine mem_c25Pre.2 ⟨hh, ?_⟩
    rw [← hconj h hh hgh]
    exact hU

omit [Finite G] in
theorem c25_card_pre {K : Subgroup G} (U : Subgroup (barOf 3 K)) :
    Nat.card (c25Pre K U) = Nat.card (GLAPPrimeCore 3 ↥K) * Nat.card U := by
  rw [c25Pre, Subgroup.card_map_of_injective K.subtype_injective]
  exact QuotientGroup.card_preimage_mk (GLAPPrimeCore 3 ↥K) (U : Set (barOf 3 K))

theorem c25_not_dvd_card_pre {K : Subgroup G} {U : Subgroup (barOf 3 K)} (hU : IsPGroup 2 ↥U) :
    ¬ 3 ∣ Nat.card (c25Pre K U) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  rw [c25_card_pre, hk]
  have hc : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K) * 2 ^ k) :=
    Nat.Coprime.mul_right CFSG.pPrimeCore_coprime_card
      (Nat.Coprime.pow_right k (by norm_num))
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc

theorem c25_two_dvd_card_pre {K : Subgroup G} {U : Subgroup (barOf 3 K)} (hU : IsPGroup 2 ↥U)
    (hne : U ≠ ⊥) : 2 ∣ Nat.card (c25Pre K U) := by
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq U (by simpa using hk))
  rw [c25_card_pre, hk]
  exact Dvd.dvd.mul_left (dvd_pow_self 2 hk0) _

theorem c25_eq_one_of_mem_core {K : Subgroup G} {n : G} (hn : n ∈ GLAPPrimeCoreOf 3 K) {a : ℕ}
    (h : n ^ (3 ^ a) = 1) : n = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd1 : orderOf n ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one h
  have hd2 : orderOf n ∣ Nat.card (GLAPPrimeCoreOf 3 K) := by
    rw [← Subgroup.orderOf_mk n hn]
    exact orderOf_dvd_natCard _
  have hc : Nat.Coprime (3 ^ a) (Nat.card (GLAPPrimeCoreOf 3 K)) :=
    Nat.Coprime.pow_left a (coprime_card_glaPPrimeCoreOf K)
  have := Nat.dvd_gcd hd1 hd2
  rw [hc.gcd_eq_one] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

end Pre

section Main

variable {G : Type} [Group G] [Finite G]

theorem c25_five_le_twoLocalRank {X K : Subgroup G} {b : G} (hKX : K ≤ X) (hbX : b ∈ X)
    (hbd : b ∈ dQ K) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hcen : Subgroup.center (barOf 3 K) = ⊥) (h4 : 4 ≤ GLATwoLocalRank 3 (barOf 3 K)) :
    5 ≤ GLATwoLocalRank 3 ↥X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbN : b ∈ Subgroup.normalizer (K : Set G) := (mem_dQ.1 hbd).1
  have hbK : b ∉ K := by
    intro hbK
    have hz : (QuotientGroup.mk (⟨b, hbK⟩ : ↥K) : barOf 3 K) ∈ Subgroup.center (barOf 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
      have hbnN : b ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := (mem_dQ.1 hbd).2.1
      have h1 := (mem_dQ.1 hbd).2.2 ((k : G)⁻¹) (K.inv_mem k.2)
      have h2 : b⁻¹ * ((k : G)⁻¹ * b * ((k : G)⁻¹)⁻¹ * b⁻¹) * b⁻¹⁻¹ ∈ GLAPPrimeCoreOf 3 K :=
        (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hbnN) _).1 h1
      obtain ⟨hk1, h3⟩ := mem_glaPPrimeCoreOf_iff.1 h2
      show QuotientGroup.mk (k * ⟨b, hbK⟩) = QuotientGroup.mk (⟨b, hbK⟩ * k)
      rw [QuotientGroup.eq]
      have : (k * ⟨b, hbK⟩)⁻¹ * (⟨b, hbK⟩ * k) =
          ⟨b⁻¹ * ((k : G)⁻¹ * b * ((k : G)⁻¹)⁻¹ * b⁻¹) * b⁻¹⁻¹, hk1⟩ := by
        apply Subtype.ext
        show ((k : G) * b)⁻¹ * (b * (k : G)) =
          b⁻¹ * ((k : G)⁻¹ * b * ((k : G)⁻¹)⁻¹ * b⁻¹) * b⁻¹⁻¹
        group
      rw [this]
      exact h3
    rw [hcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hz
    have hbn : b ∈ GLAPPrimeCoreOf 3 K := ⟨_, hz, rfl⟩
    exact hb1 (c25_eq_one_of_mem_core hbn (a := 1) (by rw [pow_one]; exact hb3))
  obtain ⟨U₀, hU₀, hU₀2, hrk⟩ := c25_exists_twoLocal (by norm_num) h4
  obtain ⟨E₀, hE₀H, hE₀, hE₀card⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (Subgroup.normalizer (U₀ : Set (barOf 3 K)))
  set m := CFSG.Open.pRank 3 (Subgroup.normalizer (U₀ : Set (barOf 3 K))) with hm
  have hzd : Subgroup.zpowers b ≤ dQ K := by
    rw [Subgroup.zpowers_le]
    exact hbd
  have hzN : Subgroup.zpowers b ≤ Subgroup.normalizer (K : Set G) := fun g hg => (mem_dQ.1 (hzd hg)).1
  have hz3 : IsPGroup 3 ↥(Subgroup.zpowers b) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    show (g : G) ^ (3 ^ 1) = 1
    rw [← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3,
      one_zpow]
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({b} : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  let f : ↥C →* barOf 3 K := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hCK)
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨k, hk, hkC, hkm⟩ := c25_exists_centralized hzN hz3 (y := y) (fun e he => by
      have := (LocalBalance.Lemma54Ns.mem_centralizerQuot_iff_barAut' 3 (J := K)
        ⟨e, hzN he⟩).1 (hzd he)
      rw [this]
      rfl)
    have hkb : k ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hkC ⊢
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hkC _ (Subgroup.mem_zpowers _)
    exact ⟨⟨k, hk, hkb⟩, hkm⟩
  have hfker : ¬ 3 ∣ Nat.card f.ker := by
    have hinj : Function.Injective (Subgroup.inclusion hCK) := Subgroup.inclusion_injective hCK
    have hle : f.ker.map (Subgroup.inclusion hCK) ≤ GLAPPrimeCore 3 ↥K := by
      rintro _ ⟨c, hc, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hc)
    have hdvd : Nat.card f.ker ∣ Nat.card (GLAPPrimeCore 3 ↥K) := by
      rw [← Subgroup.card_map_of_injective hinj]
      exact Subgroup.card_dvd_of_le hle
    intro h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (Nat.Coprime.coprime_dvd_right hdvd CFSG.pPrimeCore_coprime_card) h3
  obtain ⟨SC, hSCel, hSCmap, hSCcard⟩ := c25_exists_elemAbelian_lift_hom f hfs hfker hE₀
  set Sh : Subgroup G := SC.map C.subtype with hSh
  have hShel : IsElemAbelian 3 Sh := c25_isElemAbelian_map _ hSCel
  have hShcard : Nat.card Sh = 3 ^ m := by
    rw [hSh, Subgroup.card_map_of_injective C.subtype_injective, hSCcard, hE₀card]
  have hShC : Sh ≤ C := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hShK : Sh ≤ K := hShC.trans hCK
  have hShψ : ∀ (s : G) (hs : s ∈ Sh), (QuotientGroup.mk (⟨s, hShK hs⟩ : ↥K) : barOf 3 K) ∈ E₀ := by
    rintro _ ⟨c, hc, rfl⟩
    rw [← hSCmap]
    exact ⟨c, hc, rfl⟩
  have hbcent : b ∈ Subgroup.centralizer (Sh : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := (hShC hh).2
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  set T : Subgroup G := Subgroup.zpowers b ⊔ Sh with hT
  have hTel : IsElemAbelian 3 T := c25_isElemAbelian_sup_zpowers hShel hb3 hbcent
  obtain ⟨j, hj⟩ := (c25_isPGroup_of_elemAbelian hTel).exists_card_eq
  have hShT : Sh ≤ T := le_sup_right
  have hmj : m ≤ j := by
    have h1 := Subgroup.card_dvd_of_le hShT
    rw [hShcard, hj] at h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  have hjm : j ≠ m := by
    intro hjm
    have hle : T ≤ Sh := by
      refine (Subgroup.eq_of_le_of_card_ge hShT ?_).symm.le
      rw [hShcard, hj, hjm]
    exact hbK (hShK (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))))
  have h5j : 5 ≤ j := by omega
  set P : Subgroup G := c25Pre K U₀ with hP
  have hTN : T ≤ Subgroup.normalizer (P : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact c25_mem_normalizer_pre_of_mem_dQ U₀ hbd
    · intro s hs
      exact c25_mem_normalizer_pre (hShK hs) (hE₀H (hShψ s hs))
  have hPcop : ¬ 3 ∣ Nat.card P := c25_not_dvd_card_pre hU₀2
  have hPK : P ≤ K := c25Pre_le U₀
  let φ : ↥T →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hTN)
  let _inst : MulDistribMulAction ↥T ↥P := MulDistribMulAction.compHom ↥P φ
  obtain ⟨S₂, hS₂⟩ := c25_exists_invariant_sylow (A := ↥T) (P := ↥P)
    (c25_isPGroup_of_elemAbelian hTel) hPcop
  set U : Subgroup G := (S₂ : Subgroup ↥P).map P.subtype with hU
  have hUP : U ≤ P := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hU2 : IsPGroup 2 ↥U :=
    (S₂.isPGroup').of_equiv ((S₂ : Subgroup ↥P).equivMapOfInjective P.subtype P.subtype_injective)
  have hU1 : U ≠ ⊥ := by
    intro hUb
    have h2 : 2 ∣ Nat.card P := c25_two_dvd_card_pre hU₀2 hU₀
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcard : Nat.card (S₂ : Subgroup ↥P) = 1 := by
      have h6 : Nat.card ↥U = Nat.card ↥(S₂ : Subgroup ↥P) :=
        Subgroup.card_map_of_injective P.subtype_injective
      rw [← h6, hUb, Subgroup.card_bot]
    have h3 := S₂.card_eq_multiplicity
    rw [hcard] at h3
    have h4 : 0 < (Nat.card P).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have : 2 ^ (Nat.card P).factorization 2 = 1 := h3.symm
    have h5 : 2 ≤ 2 ^ (Nat.card P).factorization 2 := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h4
    omega
  have hTU : T ≤ Subgroup.normalizer (U : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    have hφ : ∀ (t' : ↥T) (x : ↥P), (((φ t') x : ↥P) : G) = (t' : G) * (x : G) * (t' : G)⁻¹ :=
      fun _ _ => rfl
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hS₂ ⟨t, ht⟩ x hx
      exact ⟨φ ⟨t, ht⟩ • x, this, hφ ⟨t, ht⟩ x⟩
    · rintro ⟨y, hy, hyg⟩
      have hg : g ∈ P := by
        have h1 : t * g * t⁻¹ ∈ P := hyg ▸ y.2
        have h2 := (Subgroup.mem_normalizer_iff.1 (hTN ht) g).2 h1
        exact h2
      have := hS₂ ⟨t, ht⟩⁻¹ y hy
      refine ⟨_, this, ?_⟩
      show (((⟨t, ht⟩⁻¹ : ↥T) : G)) * (y : G) * (((⟨t, ht⟩⁻¹ : ↥T) : G))⁻¹ = g
      have hyg' : (y : G) = t * g * t⁻¹ := hyg
      rw [hyg']
      show t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g
      group
  have hTX : T ≤ X := sup_le (by rw [Subgroup.zpowers_le]; exact hbX) (hShK.trans hKX)
  have hUX : U ≤ X := hUP.trans ((c25Pre_le U₀).trans hKX)
  have hUX1 : U.subgroupOf X ≠ ⊥ := by
    intro h
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hUX hu⟩ : ↥X) ∈ U.subgroupOf X := Subgroup.mem_subgroupOf.2 hu
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hUX2 : IsPGroup 2 ↥(U.subgroupOf X) := hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUX).symm
  have hTXel : IsElemAbelian 3 (T.subgroupOf X) := c25_isElemAbelian_subgroupOf X hTel
  have hTXcard : Nat.card (T.subgroupOf X) = 3 ^ j :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv).trans hj
  have hTXN : T.subgroupOf X ≤ Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (hTU (Subgroup.mem_subgroupOf.1 ht)) (x : G)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact h1
  have hj' : j ≤ CFSG.Open.pRank 3 (Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X)) :=
    CFSG.SectionRank.le_pRank (by norm_num) hTXN hTXel hTXcard
  exact c25_le_twoLocal hUX1 hUX2 (h5j.trans hj')

end Main

end CFSG.HardMathSupport.Solomon.Coordinator
