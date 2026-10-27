module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveInvol
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoClassical

variable {G : Type} [Group G] [Finite G]

theorem sq_eq_one_of_commute_k1_k2 : ∀ σ : Perm (Fin 5), σ * (k1 : Perm (Fin 5)) = k1 * σ →
    σ * (k2 : Perm (Fin 5)) = k2 * σ → σ ^ 2 = 1 := by
  decide +kernel

@[expose] def c5 : A5 := ⟨swap 0 4 * swap 0 3 * swap 0 2 * swap 0 1, by decide⟩

theorem c5_pow_five : c5 ^ 5 = 1 := by decide

theorem c5_ne_one : c5 ≠ 1 := by decide

theorem sec3_of_le {A R : Subgroup G} (hA : Hyp31 A) (eA : ↥A ≃* A5)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) {x : G} (hx : rightConjugate R x ≤ A) :
    Sec3 A R (rightConjugate R x) x := by
  refine ⟨hA, hR, fun hxN => ?_, AschbacherTheorem3.isSylowOf_rightConjugate hR x, ?_⟩
  · have hK : rightConjugate (centralizer (A : Set G)) x = centralizer (A : Set G) := by
      rw [rightConjugate_eq_self_iff, normalizer_centralizer_eq hA.standard]
      exact hxN
    have hle : rightConjugate R x ≤ A ⊓ centralizer (A : Set G) := by
      refine le_inf hx ?_
      rw [← hK]
      exact map_mono hR.le
    rw [inf_centralizer_eq_bot eA, le_bot_iff] at hle
    have h4 := Lemma36.four_le_card hA hR
    have h := rightConjugate_card R x
    rw [hle, card_bot] at h
    omega
  · intro t ht
    rw [mem_centralizer_iff]
    intro r hr
    exact (mem_centralizer_iff.mp (hR.le hr) t (hx ht)).symm

theorem le_rightConjugate_of_le (h32 : Lemma32) (h332 : Lemma33Two) {A R T : Subgroup G} {g : G}
    (hc : Sec3 A R T g) (eA : ↥A ≃* A5) (hTA : T ≤ A) : R ≤ rightConjugate A g := by
  obtain ⟨hR4, hRT16, hVeq, -⟩ := card_sec3V h32 h332 hc.hyp eA hc.sylowR hc.not_mem hc.sylowT
    hc.le_centralizer
  obtain ⟨hVe, -, -⟩ := lemma35 h32 h332 hc.hyp hc.sylowR hc.sylowT hc.le_centralizer
  have hV16 : Nat.card (sec3V R T) = 16 := by rw [hVeq, hRT16]
  have hstar := star36 h332 hc.hyp eA hc.sylowR hVe hR4 hV16
  obtain ⟨xT, hTx, hAx⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
  have hcard : Nat.card R * Nat.card R ≤ Nat.card (sec3V R T) := by rw [hR4, hV16]
  have hcomm : ∀ x : G, rightConjugate R x ≤ sec3V R T →
      ⁅rightConjugate A x ⊓ normalizer (sec3V R T : Set G), sec3V R T⁆ =
        sec3V R T ⊓ rightConjugate A x := by
    intro x hx
    obtain ⟨y, hy, hodd, htr, -⟩ := hstar x hx
    exact (Lemma36.conjData h332 hc.hyp hc.sylowR hVe hcard hR4.ge hx hy hodd htr).commutator_eq
  have hTV : T ≤ sec3V R T := hVeq ▸ le_sup_right
  have hcA : ⁅A ⊓ normalizer (sec3V R T : Set G), sec3V R T⁆ = sec3V R T ⊓ A := by
    have h := hcomm 1 (by rw [rightConjugate_one]; exact hVeq ▸ le_sup_left)
    rwa [rightConjugate_one] at h
  have hcAg : ⁅rightConjugate A g ⊓ normalizer (sec3V R T : Set G), sec3V R T⁆ =
      sec3V R T ⊓ rightConjugate A g := by
    have h := hcomm xT (hTx ▸ hTV)
    rwa [hAx] at h
  rcases lemma36 h32 h332 G A R T g hc.hyp hc.sylowR hc.not_mem hc.sylowT hc.le_centralizer
      hstar with ⟨-, h2, -⟩ | ⟨-, h2, -⟩
  · rw [hcAg] at h2
    rw [← h2]
    exact inf_le_right
  · exfalso
    obtain ⟨⟨t, htT⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.T_ne_bot
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have h := (h2 t (hTV htT)).mpr ⟨xT, hTx ▸ hTV, hTx ▸ htT, ht1'⟩
    rw [hcA] at h
    exact h (mem_inf.mpr ⟨hTV htT, hTA htT⟩)

structure CaseIPair (A B R T : Subgroup G) : Prop where
  isoA : Nonempty (↥A ≃* A5)
  isoB : Nonempty (↥B ≃* A5)
  sylowR : IsSylowOf 2 R (centralizer (A : Set G))
  sylowT : IsSylowOf 2 T (centralizer (B : Set G))
  R_le : R ≤ B
  T_le : T ≤ A
  card_R : Nat.card R = 4
  card_T : Nat.card T = 4
  tightA : TightlyEmbedded (centralizer (A : Set G))
  tightB : TightlyEmbedded (centralizer (B : Set G))
  normA : normalizer (centralizer (A : Set G) : Set G) = normalizer (A : Set G)
  normB : normalizer (centralizer (B : Set G) : Set G) = normalizer (B : Set G)
  odd_card_inf : Odd (Nat.card (centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G))
  commutator_ne_bot : ⁅A, B⁆ ≠ ⊥

theorem caseIPair_of (h32 : Lemma32) (h332 : Lemma33Two) {A R T : Subgroup G} {g : G}
    (hc : Sec3 A R T g) (eA : ↥A ≃* A5) (hTA : T ≤ A) : CaseIPair A (rightConjugate A g) R T := by
  obtain ⟨hR4, -, -, -⟩ := card_sec3V h32 h332 hc.hyp eA hc.sylowR hc.not_mem hc.sylowT
    hc.le_centralizer
  have hstd := hc.hyp.standard
  have hKte := tightlyEmbedded_centralizer hstd
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rw [normalizer_centralizer_eq hstd]
    exact hc.not_mem
  refine ⟨⟨eA⟩, ⟨(conjEquiv A g).trans eA⟩, hc.sylowR, ?_,
    le_rightConjugate_of_le h32 h332 hc eA hTA, hTA, hR4, by rw [hc.card_eq, hR4], hKte, ?_,
    normalizer_centralizer_eq hstd, ?_, ?_, ?_⟩
  · rw [centralizer_rightConjugate]
    exact hc.sylowT
  · rw [centralizer_rightConjugate]
    exact tightlyEmbedded_rightConjugate hKte g
  · ext x
    rw [centralizer_rightConjugate, mem_normalizer_rightConjugate_iff,
      mem_normalizer_rightConjugate_iff, normalizer_centralizer_eq hstd]
  · rw [centralizer_rightConjugate]
    exact hKte.2 g hgK
  · exact hstd.2.2.2.2 g⁻¹

namespace CaseIPair

variable {A B R T : Subgroup G}

omit [Finite G] in
theorem symm (p : CaseIPair A B R T) : CaseIPair B A T R where
  isoA := p.isoB
  isoB := p.isoA
  sylowR := p.sylowT
  sylowT := p.sylowR
  R_le := p.T_le
  T_le := p.R_le
  card_R := p.card_T
  card_T := p.card_R
  tightA := p.tightB
  tightB := p.tightA
  normA := p.normB
  normB := p.normA
  odd_card_inf := by rw [inf_comm]; exact p.odd_card_inf
  commutator_ne_bot := by rw [commutator_comm]; exact p.commutator_ne_bot

omit [Finite G] in
theorem isPGroup_R (p : CaseIPair A B R T) : IsPGroup 2 R := p.sylowR.isPGroup

omit [Finite G] in
theorem R_ne_bot (p : CaseIPair A B R T) : R ≠ ⊥ := fun h => by
  have := p.card_R
  rw [h, card_bot] at this
  omega

theorem normalizer_R_le (p : CaseIPair A B R T) :
    normalizer (R : Set G) ≤ normalizer (A : Set G) := by
  rw [← p.normA]
  exact normalizer_two_subgroup_le _ _ p.tightA p.isPGroup_R p.sylowR.le p.R_ne_bot

theorem centralizer_le_normalizer (p : CaseIPair A B R T) :
    centralizer (A : Set G) ≤ normalizer (B : Set G) := by
  intro k hk
  refine p.symm.normalizer_R_le (Subgroup.centralizer_le_normalizer _ ?_)
  rw [mem_centralizer_iff]
  intro t ht
  exact mem_centralizer_iff.mp hk t (p.T_le ht)

theorem centralizer_B_le_normalizer (p : CaseIPair A B R T) :
    centralizer (B : Set G) ≤ normalizer (A : Set G) :=
  p.symm.centralizer_le_normalizer

theorem inf_normalizer_le (p : CaseIPair A B R T) :
    B ⊓ normalizer (R : Set G) ≤ centralizer (A : Set G) := by
  obtain ⟨eA⟩ := p.isoA
  obtain ⟨eB⟩ := p.isoB
  have hT4 : Nat.card (T.subgroupOf A) = 4 := by
    rw [← p.card_T]
    exact Nat.card_congr (subgroupOfEquivOfLe p.T_le).toEquiv
  obtain ⟨ψA, hψA⟩ := exists_equiv_map_P0 eA hT4
  have hR4 : Nat.card (R.subgroupOf B) = 4 := by
    rw [← p.card_R]
    exact Nat.card_congr (subgroupOfEquivOfLe p.R_le).toEquiv
  obtain ⟨ψB, hψB⟩ := exists_equiv_map_P0 eB hR4
  have hkT : ∀ k ∈ P0, ((ψA k : A) : G) ∈ T := fun k hk => by
    have h : ψA k ∈ T.subgroupOf A := hψA ▸ mem_map_of_mem _ hk
    exact mem_subgroupOf.mp h
  have hsq : ∀ y ∈ B ⊓ normalizer (R : Set G), y ^ 2 ∈ centralizer (A : Set G) := by
    rintro y ⟨hyB, hyN⟩
    have hyNA : y ∈ normalizer (A : Set G) := p.normalizer_R_le hyN
    set σ := autPerm ψA.symm ⟨y, hyNA⟩ with hσ
    have hcomm : ∀ k ∈ P0, σ * (k : Perm (Fin 5)) = k * σ := by
      intro k hk
      have hk' := autPerm_of_mem ψA.symm (ψA k).2
      simp only [Subtype.coe_eta, MulEquiv.symm_apply_apply] at hk'
      rw [← hk', hσ, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_iff.mp (p.sylowT.le (hkT k hk)) y hyB)
    have hσ2 : σ ^ 2 = 1 :=
      sq_eq_one_of_commute_k1_k2 σ (hcomm k1 (by decide)) (hcomm k2 (by decide))
    have h := (autPerm_eq_one_iff ψA.symm (⟨y, hyNA⟩ ^ 2)).mp (by rw [map_pow, ← hσ, hσ2])
    simpa using h
  obtain ⟨hy0N, hy0o, -, hNle⟩ := klein_of_map ψB
  rw [hψB] at hy0N hNle
  have hy0NR : ((ψB y0 : B) : G) ∈ normalizer (R : Set G) := by
    have h := (Subgroup.subgroupOf_normalizer_eq p.R_le).symm ▸ hy0N
    exact mem_subgroupOf.mp h
  have hy0C : ((ψB y0 : B) : G) ∈ centralizer (A : Set G) := by
    have h2 := hsq _ ⟨(ψB y0).2, hy0NR⟩
    have h3 : ((ψB y0 : B) : G) ^ 3 = 1 := by
      rw [← SubgroupClass.coe_pow, ← hy0o, pow_orderOf_eq_one, OneMemClass.coe_one]
    have h4 : ((ψB y0 : B) : G) = (((ψB y0 : B) : G) ^ 2) ^ 2 := by
      calc ((ψB y0 : B) : G) = ((ψB y0 : B) : G) * ((ψB y0 : B) : G) ^ 3 := by
            rw [h3, mul_one]
        _ = (((ψB y0 : B) : G) ^ 2) ^ 2 := by group
    rw [h4]
    exact pow_mem h2 2
  rintro y ⟨hyB, hyN⟩
  have hyNB : (⟨y, hyB⟩ : B) ∈ normalizer ((R.subgroupOf B : Subgroup B) : Set B) :=
    Subgroup.subgroupOf_normalizer_eq p.R_le ▸ mem_subgroupOf.mpr hyN
  have hle : R.subgroupOf B ⊔ zpowers (ψB y0) ≤ (centralizer (A : Set G)).subgroupOf B := by
    refine sup_le (fun r hr => ?_) ?_
    · exact mem_subgroupOf.mpr (p.sylowR.le (mem_subgroupOf.mp hr))
    · rw [zpowers_le]
      exact mem_subgroupOf.mpr hy0C
  exact mem_subgroupOf.mp (hle (hNle _ hyNB))

theorem exists_mul_mem (p : CaseIPair A B R T) {k : G} (hk : k ∈ centralizer (A : Set G)) :
    ∃ y ∈ B ⊓ normalizer (R : Set G), y⁻¹ * k ∈ centralizer (B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eA⟩ := p.isoA
  obtain ⟨eB⟩ := p.isoB
  have hT4 : Nat.card (T.subgroupOf A) = 4 := by
    rw [← p.card_T]
    exact Nat.card_congr (subgroupOfEquivOfLe p.T_le).toEquiv
  obtain ⟨ψA, hψA⟩ := exists_equiv_map_P0 eA hT4
  have hR4 : Nat.card (R.subgroupOf B) = 4 := by
    rw [← p.card_R]
    exact Nat.card_congr (subgroupOfEquivOfLe p.R_le).toEquiv
  obtain ⟨ψB, hψB⟩ := exists_equiv_map_P0 eB hR4
  set K := centralizer (A : Set G) with hKdef
  have hKN : K ≤ normalizer (B : Set G) := p.centralizer_le_normalizer
  set φ := autPerm ψB.symm with hφ
  set f : ↥K →* Perm (Fin 5) := φ.comp (inclusion hKN) with hf
  have hf_apply : ∀ x : ↥K, f x = φ ⟨x, hKN x.2⟩ := fun x => rfl
  have hker : ∀ x : ↥K, f x = 1 ↔ (x : G) ∈ centralizer (B : Set G) := fun x =>
    autPerm_eq_one_iff ψB.symm ⟨x, hKN x.2⟩
  have hkercard : Nat.card f.ker = Nat.card (K ⊓ centralizer (B : Set G) : Subgroup G) := by
    refine Nat.card_congr ⟨fun x => ⟨(x : ↥K), (x : ↥K).2, (hker _).mp x.2⟩,
      fun y => ⟨⟨y, y.2.1⟩, (hker ⟨y, y.2.1⟩).mpr y.2.2⟩, fun x => rfl, fun y => rfl⟩
  have hkerodd : Odd (Nat.card f.ker) := by rw [hkercard]; exact p.odd_card_inf
  have hKcard := Subgroup.card_ker_mul_card_range f
  have hfac : (Nat.card K).factorization 2 = 2 := by
    have h := p.sylowR.card_eq
    rw [p.card_R] at h
    have h2 : (2 : ℕ) ^ 2 = 2 ^ (Nat.card K).factorization 2 := by rw [← h]; norm_num
    exact (Nat.pow_right_injective le_rfl h2).symm
  have hKpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have h8 : ¬ 8 ∣ Nat.card f.range := by
    intro h
    have h1 : 2 ^ 3 ∣ Nat.card K := by
      rw [← hKcard]
      exact Dvd.dvd.mul_left h _
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hKpos, hfac] at h1
    omega
  have hRK : R ≤ K := p.sylowR.le
  set gR : ↥R →* Perm (Fin 5) := f.comp (inclusion hRK) with hgR
  have hgR_apply : ∀ r : ↥R, gR r = ((ψB.symm ⟨r, p.R_le r.2⟩ : A5) : Perm (Fin 5)) :=
    fun r => autPerm_of_mem ψB.symm (p.R_le r.2)
  have hgR_inj : Function.Injective gR := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : (r : G) ∈ centralizer (B : Set G) := (hker _).mp hr
    have h2 : (r : G) ∈ B ⊓ centralizer (B : Set G) := mem_inf.mpr ⟨p.R_le r.2, h1⟩
    rw [inf_centralizer_eq_bot eB, mem_bot] at h2
    exact Subtype.ext h2
  have hgRcard : Nat.card gR.range = 4 := by
    rw [← p.card_R]
    exact (Nat.card_congr (MonoidHom.ofInjective hgR_inj).toEquiv).symm
  have hgRle : gR.range ≤ f.range := by
    rintro _ ⟨r, rfl⟩
    exact ⟨_, rfl⟩
  have hgRsign : ∀ x ∈ gR.range, Perm.sign x = 1 := by
    rintro _ ⟨r, rfl⟩
    rw [hgR_apply]
    exact Equiv.Perm.mem_alternatingGroup.mp (ψB.symm ⟨r, p.R_le r.2⟩).2
  obtain ⟨hy0N, hy0o, -, -⟩ := klein_of_map ψB
  rw [hψB] at hy0N
  have hy0NR : ((ψB y0 : B) : G) ∈ normalizer (R : Set G) := by
    have h := (Subgroup.subgroupOf_normalizer_eq p.R_le).symm ▸ hy0N
    exact mem_subgroupOf.mp h
  have hy0Y : ((ψB y0 : B) : G) ∈ B ⊓ normalizer (R : Set G) := ⟨(ψB y0).2, hy0NR⟩
  set y3 : ↥K := ⟨_, p.inf_normalizer_le hy0Y⟩ with hy3
  have hfy3 : f y3 = ((y0 : A5) : Perm (Fin 5)) := by
    rw [hf_apply]
    have h := autPerm_of_mem ψB.symm (ψB y0).2
    simpa using h
  have hy3ord : orderOf (f y3) = 3 := by
    rw [hfy3, Subgroup.orderOf_coe, orderOf_y0]
  have h12 : ∀ X : Subgroup (Perm (Fin 5)), gR.range ≤ X → f y3 ∈ X → 12 ∣ Nat.card X := by
    intro X hX hy
    have h4 : 4 ∣ Nat.card X := hgRcard ▸ Subgroup.card_dvd_of_le hX
    have h3 : 3 ∣ Nat.card X := by
      have h := Subgroup.orderOf_dvd_natCard X hy
      rwa [hy3ord] at h
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h4
  have h12M := h12 f.range hgRle ⟨y3, rfl⟩
  have hMalt : f.range ≤ alternatingGroup (Fin 5) := by
    intro x hx
    by_contra hxs
    rw [Equiv.Perm.mem_alternatingGroup] at hxs
    set s : ↥f.range →* ℤˣ := Perm.sign.comp f.range.subtype with hs
    have hsx : s ⟨x, hx⟩ = -1 := by
      rcases Int.units_eq_one_or (Perm.sign x) with h | h
      · exact absurd h hxs
      · exact h
    have hrange : Nat.card s.range = 2 := by
      have h2 : s.range = ⊤ := by
        rw [eq_top_iff]
        intro u _
        rcases Int.units_eq_one_or u with rfl | rfl
        · exact one_mem _
        · exact ⟨_, hsx⟩
      rw [h2, card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
    have hgker : gR.range.subgroupOf f.range ≤ s.ker := by
      intro y hy
      rw [MonoidHom.mem_ker]
      exact hgRsign _ (mem_subgroupOf.mp hy)
    have h4 : 4 ∣ Nat.card s.ker := by
      have h := Subgroup.card_dvd_of_le hgker
      rwa [Nat.card_congr (subgroupOfEquivOfLe hgRle).toEquiv, hgRcard] at h
    have hcard := Subgroup.card_ker_mul_card_range s
    rw [hrange] at hcard
    apply h8
    rw [← hcard]
    exact Nat.mul_dvd_mul h4 (dvd_refl 2)
  have hA60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hM60 : Nat.card f.range ∣ 60 := hA60 ▸ Subgroup.card_dvd_of_le hMalt
  obtain ⟨j, hj⟩ := h12M
  have hj5 : j ∣ 5 := by
    have h := hM60
    rw [hj, show (60 : ℕ) = 12 * 5 by norm_num] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hj5 with rfl | rfl
  ·
    set Y : Subgroup ↥K := (B ⊓ normalizer (R : Set G)).subgroupOf K with hY
    have hYle : Y.map f ≤ f.range := map_le_range f Y
    have hgRY : gR.range ≤ Y.map f := by
      rintro _ ⟨r, rfl⟩
      exact ⟨inclusion hRK r, mem_subgroupOf.mpr ⟨p.R_le r.2, le_normalizer r.2⟩, rfl⟩
    have hy3Y : f y3 ∈ Y.map f := ⟨y3, mem_subgroupOf.mpr hy0Y, rfl⟩
    have h12Y := h12 _ hgRY hy3Y
    have hYeq : Y.map f = f.range := by
      refine eq_of_le_of_card_ge hYle ?_
      rw [hj, mul_one]
      exact Nat.le_of_dvd Nat.card_pos h12Y
    have hkY : f ⟨k, hk⟩ ∈ Y.map f := hYeq ▸ ⟨⟨k, hk⟩, rfl⟩
    obtain ⟨y', hy'Y, hy'f⟩ := hkY
    refine ⟨y', mem_subgroupOf.mp hy'Y, ?_⟩
    have h1 : f (y'⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hy'f, inv_mul_cancel]
    simpa using (hker _).mp h1
  ·
    exfalso
    have hMeq : f.range = alternatingGroup (Fin 5) :=
      eq_of_le_of_card_ge hMalt (by rw [hj, hA60])
    have hBN : B ≤ normalizer (A : Set G) := by
      intro b hb
      have h1 : ((ψB.symm ⟨b, hb⟩ : A5) : Perm (Fin 5)) ∈ f.range :=
        hMeq ▸ (ψB.symm ⟨b, hb⟩).2
      obtain ⟨k', hk'⟩ := h1
      have h2 : φ ((⟨(k' : G), hKN k'.2⟩ : normalizer (B : Set G))⁻¹ * ⟨b, le_normalizer hb⟩) =
          1 := by
        rw [map_mul, map_inv, ← hf_apply, hk', hφ, autPerm_of_mem ψB.symm hb, inv_mul_cancel]
      have h3 := (autPerm_eq_one_iff ψB.symm _).mp h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      have hb' : b = (k' : G) * ((k' : G)⁻¹ * b) := by group
      rw [hb']
      exact mul_mem (Subgroup.centralizer_le_normalizer _ k'.2) (p.centralizer_B_le_normalizer h3)
    have hkT : ∀ k ∈ P0, ((ψA k : A) : G) ∈ T := fun k hk => by
      have h : ψA k ∈ T.subgroupOf A := hψA ▸ mem_map_of_mem _ hk
      exact mem_subgroupOf.mp h
    set b5 : G := ((ψB c5 : B) : G) with hb5
    have hb5B : b5 ∈ B := (ψB c5).2
    set σ := autPerm ψA.symm ⟨b5, hBN hb5B⟩ with hσ
    have hσk : ∀ k ∈ P0, σ * (k : Perm (Fin 5)) = k * σ := by
      intro k hk
      have hk' := autPerm_of_mem ψA.symm (ψA k).2
      simp only [Subtype.coe_eta, MulEquiv.symm_apply_apply] at hk'
      rw [← hk', hσ, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_iff.mp (p.sylowT.le (hkT k hk)) b5 hb5B)
    have hσ2 := sq_eq_one_of_commute_k1_k2 σ (hσk k1 (by decide)) (hσk k2 (by decide))
    have hσ5 : σ ^ 5 = 1 := by
      rw [hσ, ← map_pow]
      have h5 : (⟨b5, hBN hb5B⟩ : normalizer (A : Set G)) ^ 5 = 1 := by
        apply Subtype.ext
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [hb5, ← SubgroupClass.coe_pow, ← map_pow, c5_pow_five, map_one, OneMemClass.coe_one]
      rw [h5, map_one]
    have hσ1 : σ = 1 := by
      calc σ = σ ^ 5 * ((σ ^ 2) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hσ5, hσ2, one_pow, inv_one, mul_one]
    have hb5C : b5 ∈ centralizer (A : Set G) := (autPerm_eq_one_iff ψA.symm _).mp hσ1
    have : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup ↥B := eB.isSimpleGroup
    have hnorm : ((centralizer (A : Set G)).subgroupOf B).Normal := by
      constructor
      intro n hn b
      rw [mem_subgroupOf] at hn ⊢
      have hbN : (b : G) ∈ normalizer (centralizer (A : Set G) : Set G) := by
        rw [p.normA]
        exact hBN b.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (mem_normalizer_iff.mp hbN _).mp hn
    rcases hnorm.eq_bot_or_eq_top with h | h
    · have hmem : (⟨b5, hb5B⟩ : B) ∈ (centralizer (A : Set G)).subgroupOf B :=
        mem_subgroupOf.mpr hb5C
      rw [h, mem_bot] at hmem
      apply c5_ne_one
      apply ψB.injective
      rw [map_one]
      exact hmem
    · apply p.commutator_ne_bot
      rw [commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
      intro b hb
      have hmem : (⟨b, hb⟩ : B) ∈ (centralizer (A : Set G)).subgroupOf B := h ▸ mem_top _
      exact mem_subgroupOf.mp hmem

end CaseIPair

end CFSG.ComponentClassification.RankTwoAltFive
