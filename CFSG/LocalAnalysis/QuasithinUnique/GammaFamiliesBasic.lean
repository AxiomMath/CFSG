module

public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_isPGroup_card_eq_pow_of_le {p : ℕ} [Fact p.Prime] {U H : Subgroup G} (hUH : U ≤ H)
    (hU : IsPGroup p U) :
    ∃ S : Subgroup G, U ≤ S ∧ S ≤ H ∧ IsPGroup p S ∧
      Nat.card S = p ^ (Nat.card H).factorization p := by
  have hU' : IsPGroup p (U.subgroupOf H) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUH).symm
  obtain ⟨Q, hQ⟩ := hU'.exists_le_sylow
  refine ⟨(Q : Subgroup H).map H.subtype, ?_, Subgroup.map_subtype_le _,
    Q.isPGroup'.map H.subtype, ?_⟩
  · have := Subgroup.map_mono (f := H.subtype) hQ
    rwa [Subgroup.map_subgroupOf_eq_of_le hUH] at this
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact Q.card_eq_multiplicity

theorem card_dvd_pow_factorization_of_le {p : ℕ} [Fact p.Prime] {U H : Subgroup G}
    (hUH : U ≤ H) (hU : IsPGroup p U) : Nat.card U ∣ p ^ (Nat.card H).factorization p := by
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  rw [hk]
  have hdvd : p ^ k ∣ Nat.card H := hk ▸ Subgroup.card_dvd_of_le hUH
  exact pow_dvd_pow p
    ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp hdvd)

omit [Finite G] in
theorem twoPart_pos (X : Subgroup G) : 0 < twoPart X := by
  unfold twoPart
  positivity

theorem card_dvd_twoPart {U H : Subgroup G} (hUH : U ≤ H) (hU : IsPGroup 2 U) :
    Nat.card U ∣ twoPart H :=
  card_dvd_pow_factorization_of_le hUH hU

theorem card_le_twoPart {U H : Subgroup G} (hUH : U ≤ H) (hU : IsPGroup 2 U) :
    Nat.card U ≤ twoPart H :=
  Nat.le_of_dvd (twoPart_pos H) (card_dvd_twoPart hUH hU)

theorem twoPart_mono {K H : Subgroup G} (hKH : K ≤ H) : twoPart K ≤ twoPart H := by
  unfold twoPart
  refine Nat.pow_le_pow_right (by norm_num) ?_
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
    (Subgroup.card_dvd_of_le hKH) 2

theorem isSylowTwoOf_iff {S H : Subgroup G} :
    IsSylowTwoOf S H ↔ S ≤ H ∧ IsPGroup 2 S ∧ Nat.card S = twoPart H := by
  have hmul : S ≤ H → (S.subgroupOf H).index * Nat.card S = Nat.card H := fun hSH => by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv]
    exact Subgroup.index_mul_card _
  constructor
  · rintro ⟨hSH, hS, hidx⟩
    refine ⟨hSH, hS, ?_⟩
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    have hidx0 : (S.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hfac : (Nat.card H).factorization 2 = k := by
      rw [← hmul hSH, hk, Nat.factorization_mul hidx0 (pow_ne_zero _ two_ne_zero)]
      simp [Nat.factorization_eq_zero_of_not_dvd hidx, Nat.Prime.factorization_pow Nat.prime_two]
    rw [hk, twoPart, hfac]
  · rintro ⟨hSH, hS, hc⟩
    refine ⟨hSH, hS, fun hdvd => ?_⟩
    have hmulS := hmul hSH
    have h2 : 2 ^ ((Nat.card H).factorization 2 + 1) ∣ Nat.card H :=
      calc 2 ^ ((Nat.card H).factorization 2 + 1) = 2 * Nat.card S := by
            rw [pow_succ, hc, twoPart]; ring
        _ ∣ (S.subgroupOf H).index * Nat.card S := mul_dvd_mul_right hdvd _
        _ = Nat.card H := hmulS
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
    omega

omit [Finite G] in
theorem IsSylowTwoOf.le {S H : Subgroup G} (h : IsSylowTwoOf S H) : S ≤ H := h.1

omit [Finite G] in
theorem IsSylowTwoOf.isPGroup {S H : Subgroup G} (h : IsSylowTwoOf S H) : IsPGroup 2 S := h.2.1

theorem IsSylowTwoOf.card_eq {S H : Subgroup G} (h : IsSylowTwoOf S H) :
    Nat.card S = twoPart H :=
  (isSylowTwoOf_iff.mp h).2.2

theorem isSylowTwoOf_of_card_eq {S H : Subgroup G} (hSH : S ≤ H) (hS : IsPGroup 2 S)
    (hc : Nat.card S = twoPart H) : IsSylowTwoOf S H :=
  isSylowTwoOf_iff.mpr ⟨hSH, hS, hc⟩

theorem exists_isSylowTwoOf_of_le {U H : Subgroup G} (hUH : U ≤ H) (hU : IsPGroup 2 U) :
    ∃ S : Subgroup G, U ≤ S ∧ IsSylowTwoOf S H := by
  obtain ⟨S, hUS, hSH, hS, hc⟩ := exists_isPGroup_card_eq_pow_of_le (p := 2) hUH hU
  exact ⟨S, hUS, isSylowTwoOf_of_card_eq hSH hS hc⟩

theorem exists_isSylowTwoOf (H : Subgroup G) : ∃ S : Subgroup G, IsSylowTwoOf S H := by
  obtain ⟨S, -, hS⟩ := exists_isSylowTwoOf_of_le (bot_le : (⊥ : Subgroup G) ≤ H)
    (by simp [IsPGroup] : IsPGroup 2 (⊥ : Subgroup G))
  exact ⟨S, hS⟩

theorem IsSylowTwoOf.eq_of_le {S K X : Subgroup G} (hS : IsSylowTwoOf S K) (hSX : S ≤ X)
    (hXK : X ≤ K) (hX : IsPGroup 2 X) : X = S := by
  symm
  refine Subgroup.eq_of_le_of_card_ge hSX ?_
  rw [hS.card_eq]
  exact card_le_twoPart hXK hX

omit [Finite G] in
theorem IsSylowTwoOf.le_of_normalizes {S K N : Subgroup G} (hS : IsSylowTwoOf S K) (hNK : N ≤ K)
    (hN : K ≤ Subgroup.normalizer (N : Set G)) (hN2 : IsPGroup 2 N) : N ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 (S.subgroupOf K) :=
    hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS.le).symm
  let P : Sylow 2 K := hS2.toSylow hS.2.2
  have hnormal : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hN
  have hN' : IsPGroup 2 (N.subgroupOf K) := hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm
  have hle : N.subgroupOf K ≤ (P : Subgroup K) := hN'.le_sylow_of_normal P
  intro x hx
  have := hle (show (⟨x, hNK hx⟩ : K) ∈ N.subgroupOf K from hx)
  exact this

open scoped Pointwise in
theorem IsSylowTwoOf.exists_conj {S S' H : Subgroup G} (hS : IsSylowTwoOf S H)
    (hS' : IsSylowTwoOf S' H) : ∃ h ∈ H, S' = S.map (MulAut.conj h).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (S.subgroupOf H) :=
    hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS.le).symm
  have hQ : IsPGroup 2 (S'.subgroupOf H) :=
    hS'.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS'.le).symm
  let P : Sylow 2 H := hP.toSylow hS.2.2
  let Q : Sylow 2 H := hQ.toSylow hS'.2.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P Q
  have hgQ : (Q : Subgroup H) = MulAut.conj g • (S.subgroupOf H) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  refine ⟨g, g.2, ?_⟩
  ext x
  constructor
  · intro hx
    have hxQ : (⟨x, hS'.le hx⟩ : H) ∈ (Q : Subgroup H) := hx
    rw [hgQ, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨s, hs, hsx⟩ := hxQ
    refine ⟨s, hs, ?_⟩
    have := congrArg Subtype.val hsx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  · rintro ⟨y, hy, rfl⟩
    have hyH : y ∈ H := hS.le hy
    have hyP : (⟨y, hyH⟩ : H) ∈ S.subgroupOf H := hy
    have := Subgroup.smul_mem_pointwise_smul (⟨y, hyH⟩ : H) (MulAut.conj g) _ hyP
    rw [← hgQ] at this
    exact this

end Sylow

section Transport

variable {G : Type*} [Group G]

theorem map_equiv_symm_map_equiv (f : G ≃* G) (H : Subgroup G) :
    (H.map f.toMonoidHom).map f.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [this, Subgroup.map_id]

theorem map_equiv_map_equiv_symm (f : G ≃* G) (H : Subgroup G) :
    (H.map f.symm.toMonoidHom).map f.toMonoidHom = H := by
  simpa using map_equiv_symm_map_equiv f.symm H

theorem card_map_equiv (f : G ≃* G) (H : Subgroup G) :
    Nat.card (H.map f.toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective f.injective

theorem twoPart_map_equiv (f : G ≃* G) (H : Subgroup G) :
    twoPart (H.map f.toMonoidHom) = twoPart H := by
  unfold twoPart
  rw [card_map_equiv]

theorem isPGroup_map_equiv_iff (p : ℕ) (f : G ≃* G) (H : Subgroup G) :
    IsPGroup p (H.map f.toMonoidHom) ↔ IsPGroup p H :=
  ⟨fun h => h.of_equiv (H.equivMapOfInjective f.toMonoidHom f.injective).symm,
    fun h => h.of_equiv (H.equivMapOfInjective f.toMonoidHom f.injective)⟩

theorem map_equiv_le_map_equiv_iff (f : G ≃* G) {H K : Subgroup G} :
    H.map f.toMonoidHom ≤ K.map f.toMonoidHom ↔ H ≤ K :=
  Subgroup.map_le_map_iff_of_injective f.injective

theorem map_equiv_eq_bot_iff (f : G ≃* G) (H : Subgroup G) :
    H.map f.toMonoidHom = ⊥ ↔ H = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective H f.injective

theorem map_equiv_inf (f : G ≃* G) (H K : Subgroup G) :
    (H ⊓ K).map f.toMonoidHom = H.map f.toMonoidHom ⊓ K.map f.toMonoidHom :=
  Subgroup.map_inf H K f.toMonoidHom f.injective

theorem normalizer_map_equiv (f : G ≃* G) (H : Subgroup G) :
    Subgroup.normalizer ((H.map f.toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (H : Set G)).map f.toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq H f).symm

theorem centralizer_map_equiv (f : G ≃* G) (K : Subgroup G) :
    Subgroup.centralizer ((K.map f.toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.centralizer (K : Set G)).map f.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    apply f.injective
    simpa using h (f k) ⟨k, hk, rfl⟩
  · rintro h _ ⟨k, hk, rfl⟩
    have := congrArg f (h k hk)
    simpa using this

theorem map_pCoreOf_le_pCoreOf_map (p : ℕ) (f : G ≃* G) (H : Subgroup G) :
    (pCoreOf p H).map f.toMonoidHom ≤ pCoreOf p (H.map f.toMonoidHom) := by
  have hle : (pCoreOf p H).map f.toMonoidHom ≤ H.map f.toMonoidHom :=
    Subgroup.map_mono (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le p H)
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf p _ _ hle ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf p H)
  · exact (isPGroup_map_equiv_iff p f _).mpr
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup p H)

theorem pCoreOf_map_equiv (p : ℕ) (f : G ≃* G) (H : Subgroup G) :
    pCoreOf p (H.map f.toMonoidHom) = (pCoreOf p H).map f.toMonoidHom := by
  refine le_antisymm ?_ (map_pCoreOf_le_pCoreOf_map p f H)
  have h1 := map_pCoreOf_le_pCoreOf_map p f.symm (H.map f.toMonoidHom)
  rw [map_equiv_symm_map_equiv] at h1
  have h2 := Subgroup.map_mono (f := f.toMonoidHom) h1
  rwa [map_equiv_map_equiv_symm] at h2

theorem charTwo_map_equiv_iff (f : G ≃* G) (H : Subgroup G) :
    CharTwo (H.map f.toMonoidHom) ↔ CharTwo H := by
  unfold CharTwo
  rw [pCoreOf_map_equiv 2 f H, centralizer_map_equiv, ← map_equiv_inf, map_equiv_le_map_equiv_iff]

theorem IsTwoLocal.map_equiv {K : Subgroup G} (hK : IsTwoLocal K) (f : G ≃* G) :
    IsTwoLocal (K.map f.toMonoidHom) := by
  obtain ⟨P, hP, hP2, rfl⟩ := hK
  refine ⟨P.map f.toMonoidHom, ?_, (isPGroup_map_equiv_iff 2 f P).mpr hP2, ?_⟩
  · rwa [Ne, map_equiv_eq_bot_iff]
  · exact (Subgroup.map_equiv_normalizer_eq P f)

theorem quasithinIsMaxTwoLocal_map_equiv {K : Subgroup G}
    (hK : CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal K) (f : G ≃* G) :
    CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal (K.map f.toMonoidHom) := by
  refine ⟨IsTwoLocal.map_equiv hK.1 f, fun H hH hle => ?_⟩
  have h1 : IsTwoLocal (H.map f.symm.toMonoidHom) := IsTwoLocal.map_equiv hH f.symm
  have h2 : K ≤ H.map f.symm.toMonoidHom := by
    have := Subgroup.map_mono (f := f.symm.toMonoidHom) hle
    rwa [map_equiv_symm_map_equiv] at this
  have h3 := hK.2 _ h1 h2
  rw [← h3, map_equiv_map_equiv_symm]

theorem map_conj_eq_self_of_mem {M : Subgroup G} {m : G} (hm : m ∈ M) :
    M.map (MulAut.conj m).toMonoidHom = M := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro h
    have := M.mul_mem (M.mul_mem hm h) (M.inv_mem hm)
    simpa [mul_assoc] using this
  · intro hx
    exact M.mul_mem (M.mul_mem (M.inv_mem hm) hx) hm

end Transport

section NormalizerCondition

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_inf_normalizer_of_ne {p : ℕ} [Fact p.Prime] {U V : Subgroup G}
    (hV : IsPGroup p V) (hUV : U ≤ V) (hne : U ≠ V) :
    ∃ x ∈ V ⊓ Subgroup.normalizer (U : Set G), x ∉ U := by
  have : Group.IsNilpotent V := hV.isNilpotent
  have hlt : U.subgroupOf V < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne ?_
    refine le_antisymm hUV ?_
    intro v hv
    have : (⟨v, hv⟩ : V) ∈ U.subgroupOf V := htop ▸ Subgroup.mem_top _
    exact this
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := V) _ hlt
  obtain ⟨x, hx, hxn⟩ := Set.exists_of_ssubset hnorm
  refine ⟨x, ?_, hxn⟩
  rw [← map_subtype_normalizer hUV]
  exact ⟨x, hx, rfl⟩

theorem exists_quasithinIsMaxTwoLocal_ge {K : Subgroup G} (hK : IsTwoLocal K) :
    ∃ M' : Subgroup G, CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M' ∧ K ≤ M' := by
  obtain ⟨M', hM'⟩ := Set.Finite.exists_maximal
    (s := {L : Subgroup G | IsTwoLocal L ∧ K ≤ L}) (Set.toFinite _) ⟨K, hK, le_rfl⟩
  exact ⟨M', ⟨hM'.1.1, fun H hH hMH => le_antisymm (hM'.2 ⟨hH, hM'.1.2.trans hMH⟩ hMH) hMH⟩,
    hM'.1.2⟩

end NormalizerCondition

section Confinement

variable {G : Type*} [Group G] [Finite G]

theorem normalizer_overgroup_confinement {p : ℕ} [Fact p.Prime] {M U : Subgroup G} (hUM : U ≤ M)
    (hN : ∀ V : Subgroup G, IsPGroup p V → U ≤ V → V ≤ M →
      Subgroup.normalizer (V : Set G) ≤ M) :
    ∀ W : Subgroup G, IsPGroup p W → U ≤ W →
      W ≤ M ∧ ∀ V : Subgroup G, IsPGroup p V → W ≤ V → V ≤ M →
        Subgroup.normalizer (V : Set G) ≤ M := by
  intro W hW hUW
  have hWM : W ≤ M := by
    by_contra hnot
    have hne : W ⊓ M ≠ W := fun h => hnot (h ▸ inf_le_right)
    obtain ⟨x, hx, hxn⟩ := exists_mem_inf_normalizer_of_ne (p := p) hW
      (inf_le_left : W ⊓ M ≤ W) hne
    have hxM : x ∈ M := by
      have hmem := hN (W ⊓ M) (hW.to_le inf_le_left) (le_inf hUW hUM) inf_le_right hx.2
      exact hmem
    exact hxn ⟨hx.1, hxM⟩
  exact ⟨hWM, fun V hV hWV hVM => hN V hV (hUW.trans hWV) hVM⟩

theorem pow_factorization_card_eq_inf_of_confinement {p : ℕ} [Fact p.Prime] {M U : Subgroup G}
    (hUM : U ≤ M) (hU : IsPGroup p U)
    (hN : ∀ V : Subgroup G, IsPGroup p V → U ≤ V → V ≤ M →
      Subgroup.normalizer (V : Set G) ≤ M) :
    ∀ H : Subgroup G, U ≤ H →
      p ^ (Nat.card H).factorization p = p ^ (Nat.card (H ⊓ M : Subgroup G)).factorization p := by
  intro H hUH
  obtain ⟨S, hUS, hSH, hS, hSc⟩ := exists_isPGroup_card_eq_pow_of_le (p := p) hUH hU
  have hSM : S ≤ M := (normalizer_overgroup_confinement hUM hN S hS hUS).1
  have hdvd : p ^ (Nat.card H).factorization p ∣ Nat.card (H ⊓ M : Subgroup G) :=
    hSc ▸ Subgroup.card_dvd_of_le (le_inf hSH hSM)
  have h1 : (Nat.card H).factorization p ≤ (Nat.card (H ⊓ M : Subgroup G)).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp hdvd
  have h2 : (Nat.card (H ⊓ M : Subgroup G)).factorization p ≤ (Nat.card H).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_dvd_of_le inf_le_left) p
  rw [le_antisymm h1 h2]

end Confinement

section CentralizerTransfer

variable {E : Type*} [Group E] [Finite E]

theorem maxTwoLocal_centralizer_transfer {A : Set E} {Z M : Subgroup E} (hZ : Z ≠ ⊥)
    (hZ2 : IsPGroup 2 Z) (hAZ : A ⊆ (Subgroup.centralizer (Z : Set E) : Set E))
    (hM : {K : Subgroup E | CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal K ∧ A ⊆ (K : Set E)} =
      {M}) :
    Subgroup.centralizer (Z : Set E) ≤ Subgroup.normalizer (Z : Set E) ∧
      Subgroup.normalizer (Z : Set E) ≤ M ∧
      {K : Subgroup E | CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal K ∧
        Subgroup.centralizer (Z : Set E) ≤ K} = {M} ∧
      {K : Subgroup E | CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal K ∧
        Subgroup.normalizer (Z : Set E) ≤ K} = {M} := by
  have hCN : Subgroup.centralizer (Z : Set E) ≤ Subgroup.normalizer (Z : Set E) :=
    Subgroup.centralizer_le_normalizer _
  have hloc : IsTwoLocal (Subgroup.normalizer (Z : Set E)) := ⟨Z, hZ, hZ2, rfl⟩
  obtain ⟨H, hHmax, hNH⟩ := exists_quasithinIsMaxTwoLocal_ge hloc
  have hHM : H = M := by
    have : H ∈ ({M} : Set (Subgroup E)) := by
      rw [← hM]
      exact ⟨hHmax, fun a ha => hNH (hCN (hAZ ha))⟩
    exact this
  subst hHM
  have hAK : ∀ K : Subgroup E, Subgroup.centralizer (Z : Set E) ≤ K → A ⊆ (K : Set E) :=
    fun K hK a ha => hK (hAZ ha)
  refine ⟨hCN, hNH, ?_, ?_⟩
  · ext K
    constructor
    · rintro ⟨hKmax, hCK⟩
      have : K ∈ {K : Subgroup E | CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal K ∧
          A ⊆ (K : Set E)} := ⟨hKmax, hAK K hCK⟩
      rwa [hM] at this
    · intro hK
      rw [Set.mem_singleton_iff] at hK
      subst hK
      exact ⟨hHmax, hCN.trans hNH⟩
  · ext K
    constructor
    · rintro ⟨hKmax, hNK⟩
      have : K ∈ {K : Subgroup E | CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal K ∧
          A ⊆ (K : Set E)} := ⟨hKmax, hAK K (hCN.trans hNK)⟩
      rwa [hM] at this
    · intro hK
      rw [Set.mem_singleton_iff] at hK
      subst hK
      exact ⟨hHmax, hNH⟩

end CentralizerTransfer

end CFSG.QuasithinUnique
