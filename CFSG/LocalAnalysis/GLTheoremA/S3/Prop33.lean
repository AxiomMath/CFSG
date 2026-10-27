module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma36
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace S3

private theorem zpowers_isPGroup_of_pow_eq_one {p : ℕ} {y : G} (h : y ^ p = 1) :
    IsPGroup p (Subgroup.zpowers y) := by
  intro g
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, h, one_zpow]
  rfl

private theorem centralizer_sup_zpowers (E : Subgroup G) (f : G) :
    Subgroup.centralizer ((E ⊔ Subgroup.zpowers f : Subgroup G) : Set G) =
      Subgroup.centralizer (E : Set G) ⊓ Subgroup.centralizer ({f} : Set G) := by
  apply le_antisymm
  · intro g hg
    refine ⟨Subgroup.centralizer_le (fun e he => ?_) hg, Subgroup.centralizer_le
      (fun y hy => ?_) hg⟩
    · exact (le_sup_left : E ≤ E ⊔ Subgroup.zpowers f) he
    · rw [Set.mem_singleton_iff.1 hy]
      exact (le_sup_right : Subgroup.zpowers f ≤ E ⊔ Subgroup.zpowers f) (Subgroup.mem_zpowers f)
  · rintro g ⟨hgE, hgf⟩
    have hle : E ⊔ Subgroup.zpowers f ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le (fun e he => ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 hgE e he
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 hgf f rfl
    exact Subgroup.mem_centralizer_iff.2 fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

private theorem le_normalizer_sup_of_conj_mem {A B C : Subgroup G}
    (hA : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A ⊔ B)
    (hB : ∀ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ A ⊔ B) :
    C ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro c hc
  set Q : Subgroup G := A ⊔ B with hQ
  have hle : Q.map (MulAut.conj c).toMonoidHom ≤ Q := by
    rw [Subgroup.map_le_iff_le_comap]
    exact sup_le (fun a ha => hA c hc a ha) (fun b hb => hB c hc b hb)
  have hcard : Nat.card Q ≤ Nat.card (Q.map (MulAut.conj c).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj c).injective).ge
  have heq : Q.map (MulAut.conj c).toMonoidHom = Q := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hle ⟨y, hy, rfl⟩
  · intro hy
    rw [← heq] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      have h : c * z * c⁻¹ = c * y * c⁻¹ := hzy
      exact mul_left_cancel (mul_right_cancel h)
    exact this ▸ hz

theorem notPConstr_sup_of_centMod {p : ℕ} (hp : p.Prime) {E J₀ : Subgroup G} {f : G}
    (hJ₀ : GLAPComponent p (Subgroup.centralizer (E : Set G)) J₀) (hf : CentMod p J₀ f)
    (hfp : f ^ p = 1) (hfE : ∀ e ∈ E, f * e = e * f) :
    NotPConstr p (E ⊔ Subgroup.zpowers f) := by
  have hI := (glaPLayer_inf_centralizer hp hJ₀ (zpowers_isPGroup_of_pow_eq_one hfp) hf).1
  have hsub : IsSubnormal (J₀ ⊓ Subgroup.centralizer ({f} : Set G))
      (Subgroup.centralizer (E : Set G) ⊓ Subgroup.centralizer ({f} : Set G)) :=
    hJ₀.2.1.inf _
  rw [← centralizer_sup_zpowers] at hsub
  exact (glaPLayer_ne_bot_iff hp).2 ⟨_, glaPComponent_of_isSubnormal' hp hsub hI⟩

private theorem isElemAbelian_range {p : ℕ} {A M : Type*} [Group A] [Group M] (f : A →* M)
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) :
    IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 x.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 y.2
    apply Subtype.ext
    change (x : M) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hz
    rw [← map_pow, hpow, map_one]

private theorem exists_lift_elemAbelian {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (N : Subgroup H) [N.Normal] (hN : ¬ p ∣ Nat.card N) (Pb : Subgroup (H ⧸ N))
    (hPb : IsElemAbelian p Pb) {n : ℕ} (hcard : Nat.card Pb = p ^ n) :
    ∃ P : Subgroup H, IsElemAbelian p P ∧ Nat.card P = p ^ n ∧
      ∀ x ∈ P, QuotientGroup.mk' N x ∈ Pb := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime (p ^ n) (Nat.card N) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 hN)
  set Pc : Subgroup H := Pb.comap (QuotientGroup.mk' N) with hPc
  have hPccard : Nat.card Pc = Nat.card N * p ^ n := by
    rw [← hcard]
    exact QuotientGroup.card_preimage_mk N (Pb : Set (H ⧸ N))
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p Pc))
  have hScard : Nat.card S = p ^ n := by
    rw [Sylow.card_eq_multiplicity, hPccard, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_pow hp,
      Finsupp.single_eq_same, zero_add]
  set ι : S →* H := Pc.subtype.comp (S : Subgroup Pc).subtype with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hmem : ∀ s : S, QuotientGroup.mk' N (ι s) ∈ Pb := fun s => s.1.2
  have hker : ∀ s : S, ι s ∈ N → s = 1 := by
    intro s hs
    have hdisj := Subgroup.disjoint_of_coprime_natCard (H := (S : Subgroup Pc).map Pc.subtype)
      (K := N) (by
        rw [Subgroup.card_map_of_injective Subtype.val_injective, hScard]
        exact hcop)
    have h1 : ι s ∈ (S : Subgroup Pc).map Pc.subtype ⊓ N := ⟨⟨s, s.2, rfl⟩, hs⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hφ : Function.Injective ((QuotientGroup.mk' N).comp ι) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    exact (Subgroup.mem_bot).2 (hker s hs)
  obtain ⟨hcomm, hpow⟩ := CFSG.SectionRank.comm_pow_of_injective (p := p) hφ
    (fun a b => isElemAbelian_commute hPb (hmem a) (hmem b)) (fun a => hPb.2 _ (hmem a))
  refine ⟨ι.range, isElemAbelian_range ι hcomm hpow, ?_, ?_⟩
  · rw [← hScard]
    exact (Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv).symm
  · rintro x ⟨s, rfl⟩
    exact hmem s

private theorem exists_lift_two_group {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (N : Subgroup H) [N.Normal] (hN : ¬ p ∣ Nat.card N) {P : Subgroup H}
    (hP : IsPGroup p P) {Sb : Subgroup (H ⧸ N)} (hSb : Sb ≠ ⊥) (hSb2 : IsPGroup 2 Sb)
    (hPS : ∀ x ∈ P, QuotientGroup.mk' N x ∈ Subgroup.normalizer (Sb : Set (H ⧸ N))) :
    ∃ S : Subgroup H, IsPGroup 2 S ∧ S ≠ ⊥ ∧ P ≤ Subgroup.normalizer (S : Set H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Sc : Subgroup H := Sb.comap (QuotientGroup.mk' N) with hSc
  have hSccard : Nat.card Sc = Nat.card N * Nat.card Sb :=
    QuotientGroup.card_preimage_mk N (Sb : Set (H ⧸ N))
  obtain ⟨m, hm⟩ := hSb2.exists_card_eq
  have hSbp : ¬ p ∣ Nat.card Sb := by
    rw [hm]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hScp : ¬ p ∣ Nat.card Sc := by
    rw [hSccard]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · exact hN h1
    · exact hSbp h1
  have hm1 : m ≠ 0 := by
    rintro rfl
    exact hSb (Subgroup.eq_bot_of_card_eq Sb (by simpa using hm))
  have h2Sc : 2 ∣ Nat.card Sc := by
    rw [hSccard]
    exact Dvd.dvd.mul_left (hm ▸ dvd_pow_self 2 hm1) _
  have hPSc : P ≤ Subgroup.normalizer (Sc : Set H) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := Subgroup.mem_normalizer_iff.1 (hPS x hx) (QuotientGroup.mk' N y)
    simpa [hSc, Subgroup.mem_comap, map_mul, map_inv] using this
  obtain ⟨S, -, hS2, hS, hPS', -⟩ := exists_invariant_sylow hp Nat.prime_two hP hPSc
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hScp) h2Sc
  exact ⟨S, hS2, hS, hPS'⟩

private theorem isElemAbelian_sup_of_commute {p : ℕ} {A P : Subgroup G} (hA : IsElemAbelian p A)
    (hP : IsElemAbelian p P) (hAP : ∀ a ∈ A, ∀ x ∈ P, a * x = x * a) :
    IsElemAbelian p (A ⊔ P) := by
  have hnorm : P ≤ Subgroup.normalizer (A : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer (A : Set G)
      (Subgroup.mem_centralizer_iff.2 fun a ha => hAP a ha x hx)
  have hdec : ∀ z ∈ A ⊔ P, ∃ a ∈ A, ∃ x ∈ P, z = a * x := by
    intro z hz
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A _ hnorm] at hz
    obtain ⟨a, ha, x, hx, rfl⟩ := Set.mem_mul.mp hz
    exact ⟨a, ha, x, hx, rfl⟩
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨a₁, ha₁, x₁, hx₁, h₁⟩ := hdec u u.2
    obtain ⟨a₂, ha₂, x₂, hx₂, h₂⟩ := hdec v v.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [h₁, h₂]
    have e1 : a₁ * a₂ = a₂ * a₁ := isElemAbelian_commute hA ha₁ ha₂
    have e2 : x₁ * x₂ = x₂ * x₁ := isElemAbelian_commute hP hx₁ hx₂
    have e3 : a₁ * x₂ = x₂ * a₁ := hAP a₁ ha₁ x₂ hx₂
    have e4 : a₂ * x₁ = x₁ * a₂ := hAP a₂ ha₂ x₁ hx₁
    calc a₁ * x₁ * (a₂ * x₂) = a₁ * (x₁ * a₂) * x₂ := by group
      _ = a₁ * (a₂ * x₁) * x₂ := by rw [e4]
      _ = (a₁ * a₂) * (x₁ * x₂) := by group
      _ = (a₂ * a₁) * (x₂ * x₁) := by rw [e1, e2]
      _ = a₂ * (a₁ * x₂) * x₁ := by group
      _ = a₂ * (x₂ * a₁) * x₁ := by rw [e3]
      _ = a₂ * x₂ * (a₁ * x₁) := by group
  · obtain ⟨a, ha, x, hx, rfl⟩ := hdec z hz
    have hc : Commute a x := hAP a ha x hx
    rw [hc.mul_pow, hA.2 a ha, hP.2 x hx, one_mul]

theorem rank_lower_bound {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X K A : Subgroup G}
    (hK : GLAPComponent p X K) (hZ : Subgroup.center (PQuot p K) = ⊥) (hA : IsElemAbelian p A)
    (hAK : A ≤ Subgroup.centralizer (K : Set G)) {a : ℕ} (hAcard : Nat.card A = p ^ a)
    (hA2 : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G)) :
    GLATwoLocalRank p (PQuot p K) + a ≤ GLATwoLocalRank p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (GLAPPrimeCore p ↥K).Normal := GLAPPrimeCore.normal p ↥K
  set n := GLATwoLocalRank p (PQuot p K) with hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, zero_add]
    obtain ⟨S, hS, hS2, hAS⟩ := hA2
    have h := card_le_pow_glaTwoLocalRank hp hA hS hS2 hAS
    rw [hAcard] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  · have hset : {k | ∃ H : Subgroup (PQuot p K), IsTwoLocal H ∧
        CFSG.Open.pRank p H = k}.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have : n = 0 := by
        rw [hn]
        unfold GLATwoLocalRank twoLocalPrimeRank
        rw [h]
        simp
      omega
    obtain ⟨Hb, ⟨Sb, hSb, hSb2, rfl⟩, hHbn⟩ :
        n ∈ {k | ∃ H : Subgroup (PQuot p K), IsTwoLocal H ∧ CFSG.Open.pRank p H = k} :=
      Nat.sSup_mem hset (bddAbove_twoLocalPRanks hp.one_lt)
    obtain ⟨Pb, hPbH, hPb, hPbcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
      (Subgroup.normalizer (Sb : Set (PQuot p K)))
    rw [hHbn] at hPbcard
    have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥K) :=
      (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
    obtain ⟨P, hPel, hPcard, hPmap⟩ := exists_lift_elemAbelian hp (GLAPPrimeCore p ↥K) hN Pb hPb
      hPbcard
    obtain ⟨S, hS2, hSne, hPS⟩ := exists_lift_two_group hp hp2 (GLAPPrimeCore p ↥K) hN
      (isPGroup_of_isElemAbelian hPel) hSb hSb2 (fun x hx => hPbH (hPmap x hx))
    have hPGK : P.map K.subtype ≤ K := Subgroup.map_subtype_le P
    have hSGK : S.map K.subtype ≤ K := Subgroup.map_subtype_le S
    have hPGel : IsElemAbelian p (P.map K.subtype) :=
      CFSG.SectionRank.isElemAbelian_map hPel K.subtype
    have hPGcard : Nat.card (P.map K.subtype) = p ^ n := by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hPcard]
    have hSG2 : IsPGroup 2 (S.map K.subtype) := hS2.map K.subtype
    have hSGne : S.map K.subtype ≠ ⊥ := fun h =>
      hSne ((Subgroup.map_eq_bot_iff_of_injective S K.subtype_injective).1 h)
    have hPSG : P.map K.subtype ≤ Subgroup.normalizer ((S.map K.subtype : Subgroup G) : Set G) :=
      (Subgroup.map_mono hPS).trans (Subgroup.le_normalizer_map K.subtype)
    have hAcomm : ∀ x ∈ K, ∀ b ∈ A, x * b = b * x := fun x hx b hb =>
      Subgroup.mem_centralizer_iff.1 (hAK hb) x hx
    have hAKO : A ⊓ K ≤ GLAPPrimeCoreOf p K := by
      rintro g ⟨hgA, hgK⟩
      have hcen : (⟨g, hgK⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (hAcomm y.1 y.2 g hgA)
      have hcen' : QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨g, hgK⟩ ∈
          Subgroup.center (PQuot p K) :=
        Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) ⟨_, hcen, rfl⟩
      rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen'
      exact ⟨⟨g, hgK⟩, hcen', rfl⟩
    have hdisjO : Disjoint A (GLAPPrimeCoreOf p K) := by
      apply Subgroup.disjoint_of_coprime_natCard
      rw [hAcard]
      exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2
        (not_dvd_card_glaPPrimeCoreOf hp K))
    have hdisj : A ⊓ P.map K.subtype = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have hgO : g ∈ A ⊓ GLAPPrimeCoreOf p K := ⟨hg.1, hAKO ⟨hg.1, hPGK hg.2⟩⟩
      rw [hdisjO.eq_bot] at hgO
      exact hgO
    have hAP : ∀ b ∈ A, ∀ x ∈ P.map K.subtype, b * x = x * b := fun b hb x hx =>
      (hAcomm x (hPGK hx) b hb).symm
    have hABel : IsElemAbelian p (A ⊔ P.map K.subtype) :=
      isElemAbelian_sup_of_commute hA hPGel hAP
    have hPGnorm : P.map K.subtype ≤ Subgroup.normalizer (A : Set G) := fun x hx =>
      Subgroup.centralizer_le_normalizer (A : Set G)
        (Subgroup.mem_centralizer_iff.2 fun b hb => hAP b hb x hx)
    have hABcard : Nat.card (A ⊔ P.map K.subtype : Subgroup G) = p ^ (n + a) := by
      have h := card_sup_mul_card_inf_of_le_normalizer hPGnorm
      rw [hdisj, Subgroup.card_bot, mul_one, hAcard, hPGcard] at h
      rw [h, pow_add, mul_comm]
    have hAS : A ≤ Subgroup.normalizer ((S.map K.subtype : Subgroup G) : Set G) := fun b hb =>
      Subgroup.centralizer_le_normalizer ((S.map K.subtype : Subgroup G) : Set G)
        (Subgroup.mem_centralizer_iff.2 fun y hy => hAcomm y (hSGK hy) b hb)
    have hfin := card_le_pow_glaTwoLocalRank hp hABel hSGne hSG2 (sup_le hAS hPSG)
    rw [hABcard] at hfin
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hfin

theorem final_contra {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X K T P : Subgroup G}
    (hK : GLAPComponent p X K) (hT2 : IsPGroup 2 T) (hTne : T ≠ ⊥)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hTc : ∀ t ∈ T, CentMod p K t)
    (hPK : P ≤ K) (hP : IsElemAbelian p P) : Nat.card P ≤ p ^ GLATwoLocalRank p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  set O := GLAPPrimeCoreOf p K with hO
  have hTO : T ≤ Subgroup.normalizer (O : Set G) :=
    hTK.trans (normalizer_le_normalizer_glaPPrimeCoreOf p K)
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p K
  obtain ⟨m, hm⟩ := hT2.exists_card_eq
  have hTp : ¬ p ∣ Nat.card T := by
    rw [hm]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hQp : ¬ p ∣ Nat.card (O ⊔ T : Subgroup G) :=
    not_dvd_card_sup_of_le_normalizer hp hTO (not_dvd_card_glaPPrimeCoreOf hp K) hTp
  have hPQ : P ≤ Subgroup.normalizer ((O ⊔ T : Subgroup G) : Set G) := by
    refine le_normalizer_sup_of_conj_mem (fun x hx a ha => ?_) (fun x hx t ht => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hKO (hPK hx)) a).1 ha)
    · have h1 : ⁅x, t⁆ ∈ O := (centMod_iff.1 (hTc t ht)).2 x (hPK hx)
      have : x * t * x⁻¹ = ⁅x, t⁆ * t := by simp only [commutatorElement_def]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right ht)
  have h2Q : 2 ∣ Nat.card (O ⊔ T : Subgroup G) := by
    have hm1 : m ≠ 0 := by
      rintro rfl
      exact hTne (Subgroup.eq_bot_of_card_eq T (by simpa using hm))
    exact (dvd_pow_self 2 hm1).trans (hm ▸ Subgroup.card_dvd_of_le le_sup_right)
  obtain ⟨S, -, hS2, hS, hPS, -⟩ := exists_invariant_sylow hp Nat.prime_two
    (isPGroup_of_isElemAbelian hP) hPQ ((hp.coprime_iff_not_dvd).2 hQp) h2Q
  exact card_le_pow_glaTwoLocalRank hp hP hS hS2 hPS

end S3

private theorem le_layerClosure_self (p : ℕ) (D' J : Subgroup G) : J ≤ layerClosure p D' J := by
  unfold layerClosure
  have h : GLBConj (1 : G) J ≤
      ⨆ g ∈ GLAPLayer p (Subgroup.centralizer (D' : Set G)), GLBConj g J :=
    le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) le_rfl
  rwa [gLBConj_one] at h

private theorem chain_le_of_step {p : ℕ} {B : Subgroup G} {k : ℕ} {Es Js : ℕ → Subgroup G}
    (hstep : ∀ i, i + 1 < k → Step36 p B (Es i) (Js i) (Es (i + 1)) (Js (i + 1))) :
    (∀ i j, i ≤ j → j < k → Js i ≤ Js j) ∧ (∀ i j, i ≤ j → j < k → Es j ≤ Es i) := by
  constructor
  · intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hj
      refine (ih (by omega)).trans ?_
      obtain ⟨-, -, -, -, -, -, hJ', -⟩ := hstep j hj
      rw [hJ']
      exact le_layerClosure_self p _ _
  · intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hj
      refine le_trans ?_ (ih (by omega))
      obtain ⟨hle, -⟩ := hstep j hj
      exact hle

theorem exists_chain {p : ℕ} (hc : S3Ctx G p) (hI18 : Input18_3_4) (h1135 : I1135At G p)
    (hCl : ChevClosureAt G p) (hUn : ChevUniqueAt G p) (hInn : ChevInnerAt G p)
    {B E J₀ : Subgroup G} (hS : Star3 G p B) (hEB : E ≤ B) {k : ℕ} (hEcard : Nat.card E = p ^ k)
    (hk : 2 ≤ k) (hJ₀ : GLAPComponent p (Subgroup.centralizer (E : Set G)) J₀) :
    ∃ Es Js : ℕ → Subgroup G, Es 0 = E ∧ Js 0 = J₀ ∧
      (∀ i, i < k → Es i ≤ B ∧ Nat.card (Es i) = p ^ (k - i) ∧
        GLAPComponent p (Subgroup.centralizer (Es i : Set G)) (Js i)) ∧
      ∀ i, i + 1 < k → Step36 p B (Es i) (Js i) (Es (i + 1)) (Js (i + 1)) := by
  have hp := hc.prime
  have key : ∀ n, n < k → ∃ Es Js : ℕ → Subgroup G, Es 0 = E ∧ Js 0 = J₀ ∧
      (∀ i, i ≤ n → Es i ≤ B ∧ Nat.card (Es i) = p ^ (k - i) ∧
        GLAPComponent p (Subgroup.centralizer (Es i : Set G)) (Js i)) ∧
      ∀ i, i + 1 ≤ n → Step36 p B (Es i) (Js i) (Es (i + 1)) (Js (i + 1)) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨fun _ => E, fun _ => J₀, rfl, rfl, ?_, ?_⟩
      · intro i hi
        obtain rfl : i = 0 := by omega
        exact ⟨hEB, by simpa using hEcard, hJ₀⟩
      · intro i hi
        exact absurd hi (by omega)
    | succ n ih =>
      intro hn
      obtain ⟨Es, Js, hE0, hJ0, hcomp, hstep⟩ := ih (by omega)
      obtain ⟨hEsB, hEscard, hEsJ⟩ := hcomp n le_rfl
      have hnc : ¬ IsCyclic (Es n) := by
        apply S3.not_isCyclic_of_card hp (isElemAbelian_mono hS.bmax.1 hEsB)
        rw [hEscard]
        exact Nat.pow_le_pow_right hp.pos (by omega)
      obtain ⟨D', J', hD'⟩ := lemma36 hc hI18 h1135 hCl hUn hInn hS hEsB hnc hEsJ
      obtain ⟨hD'le, hD'card, -, hD'comp, -⟩ := id hD'
      have hEs1 : ∀ i, i ≤ n → (fun i => if i ≤ n then Es i else D') i = Es i :=
        fun i hi => if_pos hi
      have hJs1 : ∀ i, i ≤ n → (fun i => if i ≤ n then Js i else J') i = Js i :=
        fun i hi => if_pos hi
      have hEs2 : (fun i => if i ≤ n then Es i else D') (n + 1) = D' := if_neg (by omega)
      have hJs2 : (fun i => if i ≤ n then Js i else J') (n + 1) = J' := if_neg (by omega)
      refine ⟨fun i => if i ≤ n then Es i else D', fun i => if i ≤ n then Js i else J',
        ?_, ?_, ?_, ?_⟩
      · rw [hEs1 0 (Nat.zero_le _)]
        exact hE0
      · rw [hJs1 0 (Nat.zero_le _)]
        exact hJ0
      · intro i hi
        by_cases hin : i ≤ n
        · rw [hEs1 i hin, hJs1 i hin]
          exact hcomp i hin
        · obtain rfl : i = n + 1 := by omega
          rw [hEs2, hJs2]
          refine ⟨hD'le.trans hEsB, ?_, hD'comp⟩
          have h1 : p ^ (k - n) = p ^ (k - (n + 1)) * p := by
            rw [← pow_succ]
            congr 1
            omega
          rw [hEscard, h1] at hD'card
          exact Nat.eq_of_mul_eq_mul_right hp.pos hD'card
      · intro i hi
        by_cases hin : i + 1 ≤ n
        · rw [hEs1 i (by omega), hEs1 (i + 1) hin, hJs1 i (by omega), hJs1 (i + 1) hin]
          exact hstep i hin
        · obtain rfl : i = n := by omega
          rw [hEs1 i le_rfl, hJs1 i le_rfl, hEs2, hJs2]
          exact hD'
  obtain ⟨Es, Js, hE0, hJ0, hcomp, hstep⟩ := key (k - 1) (by omega)
  exact ⟨Es, Js, hE0, hJ0, fun i hi => hcomp i (by omega), fun i hi => hstep i (by omega)⟩

theorem faithful_outer {p : ℕ} (hp : p.Prime) {B E : Subgroup G} {k : ℕ} {Es Js : ℕ → Subgroup G}
    (hEB : E ≤ B) (hE0 : Es 0 = E) (hk : 2 ≤ k)
    (hnorm : ∀ i, i < k → B ≤ Subgroup.normalizer (Js i : Set G))
    (hstep : ∀ i, i + 1 < k → Step36 p B (Es i) (Js i) (Es (i + 1)) (Js (i + 1)))
    {e : G} (he : e ∈ E) (hce : CentMod p (Js (k - 1)) e) : e ∈ Es (k - 1) := by
  obtain ⟨hmono, -⟩ := chain_le_of_step hstep
  have key : ∀ i, i < k → e ∈ Es i := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hE0]
      exact he
    | succ i ih =>
      intro hi
      have hei : e ∈ Es i := ih (by omega)
      by_contra hne
      obtain ⟨-, -, -, -, -, -, -, -, hout⟩ := hstep i hi
      refine hout e hei hne ?_
      have hJle : Js (i + 1) ≤ Js (k - 1) := hmono (i + 1) (k - 1) (by omega) (by omega)
      have hN : e ∈ Subgroup.normalizer (Js (i + 1) : Set G) := hnorm (i + 1) hi (hEB he)
      exact S3.inducesInnerMod_of_centMod (S3.centMod_of_le_cen hp hJle hN hce)
  exact key (k - 1) (by omega)

theorem max_E_eq_centMod {p : ℕ} (hp : p.Prime) {B E J₀ : Subgroup G} (hB : IsElemAbelian p B)
    (hEB : E ≤ B)
    (hmax : ∀ E' : Subgroup G, E' ≤ B → NotPConstr p E' → Nat.card E' ≤ Nat.card E)
    (hJ₀ : GLAPComponent p (Subgroup.centralizer (E : Set G)) J₀) {f : G} (hf : f ∈ B)
    (hcf : CentMod p J₀ f) : f ∈ E := by
  have hfp : f ^ p = 1 := hB.2 f hf
  have hfE : ∀ e ∈ E, f * e = e * f := fun e he => isElemAbelian_commute hB hf (hEB he)
  have hnp := S3.notPConstr_sup_of_centMod hp hJ₀ hcf hfp hfE
  have hle : E ⊔ Subgroup.zpowers f ≤ B := sup_le hEB (Subgroup.zpowers_le.2 hf)
  have heq : E = E ⊔ Subgroup.zpowers f :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (hmax _ hle hnp)
  have hmem : f ∈ E ⊔ Subgroup.zpowers f := Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  rwa [← heq] at hmem

theorem exists_T {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup G} (hB : IsElemAbelian p B)
    {x : G} (hx : IsEssential p B x) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ T ≠ ⊥ ∧ T ≤ Subgroup.centralizer ({x} : Set G) ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) = T := by
  obtain ⟨-, -, T', hT'x, hT'2, hBT', hne, -⟩ := hx
  obtain ⟨hle, hBN, heq⟩ := S3.comm_two_group hp hp2 hB hT'2 hBT'
  refine ⟨⁅B, T'⁆, IsPGroup.to_le hT'2 hle, ?_, hle.trans hT'x, hBN, ?_⟩
  · rw [Subgroup.commutator_comm B T']
    exact hne
  · rw [Subgroup.commutator_comm (⁅B, T'⁆ : Subgroup G) B]
    exact heq

private theorem prop33_end {p : ℕ} (hc : S3Ctx G p) (h1135 : I1135At G p)
    (hInn : ChevInnerAt G p) (h65 : I65At G p) (h76 : I76At G p) (hR3 : ChevRank3At G p)
    {B E F K J₀ : Subgroup G} (hS : Star3 G p B) (hEB : E ≤ B) {k : ℕ}
    (hEcard : Nat.card E = p ^ k) (hk : 2 ≤ k) (hmk : GLATwoLocalRank p G ≤ k + 2)
    (hmax : ∀ E' : Subgroup G, E' ≤ B → NotPConstr p E' → Nat.card E' ≤ Nat.card E)
    (hJ₀ : GLAPComponent p (Subgroup.centralizer (E : Set G)) J₀)
    (hJ₀B : B ≤ Subgroup.normalizer (J₀ : Set G)) (hFE : F ≤ E) (hFcard : Nat.card F = p)
    (hFess : ∀ d ∈ F, d ≠ 1 → IsEssential p B d)
    (hK : GLAPComponent p (Subgroup.centralizer (F : Set G)) K)
    (hKchev : IsChevSimple p (PSimple p K)) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hJ₀K : J₀ ≤ K) (hfaith : ∀ e ∈ E, CentMod p K e → e ∈ F) : False := by
  have hp := hc.prime
  have hp2 := hc.odd
  have hBel : IsElemAbelian p B := hS.bmax.1
  have hBcard : Nat.card B = p ^ GLATwoLocalRank p G := hS.bmax.2.1
  have hm4 : 4 ≤ GLATwoLocalRank p G := hc.rank_ge
  have hFne : F ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hFcard
    exact hp.ne_one hFcard.symm
  have hFB : F ≤ B := hFE.trans hEB
  have hEel : IsElemAbelian p E := isElemAbelian_mono hBel hEB
  have hKX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (F : Set G)) :=
    S3.isKGroup_cen hc.simple hc.nonabelian hc.kProper hFne
  have hEK : E ≤ Subgroup.normalizer (K : Set G) := hEB.trans hBK
  have hFK : F ≤ Subgroup.centralizer (K : Set G) := fun g hg =>
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      (Subgroup.mem_centralizer_iff.1 (hK.1 hy) g hg).symm
  have hEcm : E ⊓ centModSubgroup p K = F := by
    apply le_antisymm
    · rintro f ⟨hfE, hfc⟩
      exact hfaith f hfE (centMod_iff.2 hfc)
    · intro g hg
      exact ⟨hFE hg, centMod_iff.1 (centMod_of_mem_centralizer (hFK hg))⟩
  have hJ₀K' : GLAPComponent p (K ⊓ Subgroup.centralizer (E : Set G)) J₀ :=
    glaPComponent_of_le hp hJ₀ (le_inf hJ₀K hJ₀.1) inf_le_right
  have hinn : ∀ a ∈ E, CentMod p K a ∨ ¬ InducesInnerMod p K a :=
    hInn hp hp2 _ K E hKX hK hKchev hEel hEK ⟨J₀, hJ₀K'⟩
  obtain ⟨a, haE, haF⟩ : ∃ a ∈ E, a ∉ F := by
    by_contra h
    push_neg at h
    have hle := Subgroup.card_le_of_le (show E ≤ F from fun a ha => h a ha)
    rw [hEcard, hFcard] at hle
    have h1 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    have h2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h2
    exact lt_irrefl p (lt_of_lt_of_le h2 (h1.trans hle))
  have hnotcm : ¬ CentMod p K a := fun h => haF (hfaith a haE h)
  have hnotinn : ¬ InducesInnerMod p K a := (hinn a haE).resolve_left hnotcm
  have h76' := h76 hp hp2 _ K E hKX hK hKchev hEel hEK
    (fun b hb hbc => (hinn b hb).resolve_left hbc)
  rw [hEcm, hEcard, hFcard] at h76'
  obtain ⟨hle76, heq76⟩ := h76'
  have hk3 : k ≤ 3 := by
    have h : p ^ k ≤ p ^ 3 := by
      calc p ^ k ≤ p ^ 2 * p := hle76
        _ = p ^ 3 := by ring
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  have hZ : Subgroup.center (PQuot p K) = ⊥ :=
    h65 hp hp2 _ K hKX hK hKchev ⟨a, hEK haE, hEel.2 a haE, hnotcm, hnotinn⟩
  obtain ⟨U, hU, hU2, hBU⟩ := hS.bmax.2.2
  have hrank : GLATwoLocalRank p (PQuot p K) + 1 ≤ GLATwoLocalRank p G :=
    S3.rank_lower_bound hp hp2 hK hZ (isElemAbelian_mono hBel hFB) hFK
      (a := 1) (by rw [hFcard, pow_one]) ⟨U, hU, hU2, hFB.trans hBU⟩
  have hk23 : k = 2 ∨ k = 3 := by omega
  rcases hk23 with rfl | rfl
  · have hm : GLATwoLocalRank p G = 4 := by omega
    have hn3 : GLATwoLocalRank p (PQuot p K) ≤ 3 := by omega
    have hBcm : B ⊓ centModSubgroup p K = F := by
      apply le_antisymm
      · rintro f ⟨hfB, hfc⟩
        have hcf0 : CentMod p J₀ f :=
          S3.centMod_of_le_cen hp hJ₀K (hJ₀B hfB) (centMod_iff.2 hfc)
        exact hfaith f (max_E_eq_centMod hp hBel hEB hmax hJ₀ hfB hcf0) (centMod_iff.2 hfc)
      · intro g hg
        exact ⟨hFB hg, centMod_iff.1 (centMod_of_mem_centralizer (hFK hg))⟩
    have hBcard' : Nat.card B = p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p K) := by
      rw [hBcm, hFcard, hBcard, hm]
      ring
    obtain ⟨⟨P, hPK, hPel, hPcard⟩, hT⟩ := hR3 hp hp2 _ K B hKX hK hKchev hn3 hBel hBK hBcard'
      ⟨a, hEB haE, hnotcm, hnotinn⟩
    obtain ⟨x, hxF, hx1⟩ : ∃ x ∈ F, x ≠ 1 := by
      by_contra h
      push_neg at h
      exact hFne ((Subgroup.eq_bot_iff_forall F).2 h)
    have hxess := hFess x hxF hx1
    have hFx : Subgroup.zpowers x = F := by
      have hle : Subgroup.zpowers x ≤ F := Subgroup.zpowers_le.2 hxF
      have : Fact p.Prime := ⟨hp⟩
      have hord : orderOf x = p := orderOf_eq_prime (hBel.2 x (hFB hxF)) hx1
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hFcard, Nat.card_zpowers, hord]
    rw [← hFx, S3.centralizer_zpowers] at hK
    obtain ⟨T, hT2, hTne, hTx, hBT, hTB⟩ := exists_T hp hp2 hBel hxess
    have hTK : T ≤ Subgroup.normalizer (K : Set G) := by
      refine S3.normalizes_of_comm (A := B) (fun t ht => ?_) hTB.ge
      have h := glaPComponent_gLBConj hK t
      rw [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hTx ht))] at h
      exact hS.normalizes hc h1135 hxess h
    have hfc := S3.final_contra hp hp2 hK hT2 hTne hTK (hT T hT2 hTK hBT hTB) hPK hPel
    rw [hPcard, hm] at hfc
    have h46 : p ^ 4 < p ^ 6 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact absurd hfc (not_le.2 h46)
  · obtain ⟨-, h12⟩ := heq76 (by ring)
    omega

theorem prop33 {p : ℕ} (hKM : KMUsedAt) (hDih : DihedralUsed) (hc : S3Ctx G p)
    (hI18 : Input18_3_4) (h1135 : I1135At G p) (hCl : ChevClosureAt G p)
    (hUn : ChevUniqueAt G p) (hInn : ChevInnerAt G p) (h65 : I65At G p) (h76 : I76At G p)
    (hR3 : ChevRank3At G p) {B : Subgroup G} (hB : GLAIsBmax p B)
    (hchev : ∀ (x : G) (L : Subgroup G), IsEssential p B x →
      GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L → IsChevSimple p (PSimple p L)) :
    IsSC p B := by
  by_contra hnSC
  have hS : Star3 G p B := ⟨hB, hnSC, hchev⟩
  have hp := hc.prime
  have hBel : IsElemAbelian p B := hB.1
  have hBcard : Nat.card B = p ^ GLATwoLocalRank p G := hB.2.1
  obtain ⟨E₁, hE₁B, hE₁card, hE₁⟩ := lemma35 hKM hDih hc hS
  obtain ⟨E, ⟨hEB, hEnp⟩, hmax⟩ := Set.exists_max_image
    {E : Subgroup G | E ≤ B ∧ NotPConstr p E} (fun E : Subgroup G => Nat.card E)
    (Set.toFinite _) ⟨E₁, hE₁B, hE₁⟩
  have hmax' : ∀ E' : Subgroup G, E' ≤ B → NotPConstr p E' → Nat.card E' ≤ Nat.card E :=
    fun E' h1 h2 => hmax E' ⟨h1, h2⟩
  have hBE : Nat.card B ≤ Nat.card E * p ^ 2 :=
    hE₁card.trans (Nat.mul_le_mul_right _ (hmax' E₁ hE₁B hE₁))
  have hEel : IsElemAbelian p E := isElemAbelian_mono hBel hEB
  obtain ⟨k, hEcard⟩ := exists_card_eq_pow_of_isElemAbelian hp hEel
  have hmk : GLATwoLocalRank p G ≤ k + 2 := by
    have h : p ^ GLATwoLocalRank p G ≤ p ^ (k + 2) := by
      calc p ^ GLATwoLocalRank p G = Nat.card B := hBcard.symm
        _ ≤ Nat.card E * p ^ 2 := hBE
        _ = p ^ (k + 2) := by rw [hEcard, pow_add]
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  have hk : 2 ≤ k := by
    have := hc.rank_ge
    omega
  obtain ⟨J₀, hJ₀⟩ := (S3.glaPLayer_ne_bot_iff hp).1 hEnp
  obtain ⟨N, hN, hBN⟩ := GLAIsBmax.exists_maxTwoLocal hB
  have hEnc : ¬ IsCyclic E := S3.not_isCyclic_of_card hp hEel
    (by rw [hEcard]; exact Nat.pow_le_pow_right hp.pos hk)
  obtain ⟨E₀, hE₀E, hE₀card, hE₀ess, -⟩ := hc.lemma31 B E N hB hEB hEnc hN hBN
  have hE₀ne : ∃ x ∈ E₀, x ≠ 1 := by
    by_contra h
    push_neg at h
    have hbot : E₀ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    rw [hbot, Subgroup.card_bot, hEcard] at hE₀card
    have h1 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    have h2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h2
    omega
  obtain ⟨x, hxE₀, hx1⟩ := hE₀ne
  have hess : ∃ d ∈ E, IsEssential p B d := ⟨x, hE₀E hxE₀, hE₀ess x hxE₀ hx1⟩
  obtain ⟨-, hJ₀B⟩ := lemma34_iii hc hI18 h1135 hCl hUn hS hEB hess hJ₀
  obtain ⟨Es, Js, hE0, hJ0, hch, hstep⟩ :=
    exists_chain hc hI18 h1135 hCl hUn hInn hS hEB hEcard hk hJ₀
  obtain ⟨hmonoJ, hmonoE⟩ := chain_le_of_step hstep
  have hk1 : k - 1 < k := by omega
  obtain ⟨-, hFcard, hK⟩ := hch (k - 1) hk1
  have hFcard1 : Nat.card (Es (k - 1)) = p := by
    have h : k - (k - 1) = 1 := by omega
    rwa [h, pow_one] at hFcard
  have hstep' : ∀ i, 1 ≤ i → i < k →
      Step36 p B (Es (i - 1)) (Js (i - 1)) (Es i) (Js i) := by
    intro i h1 hi
    have h := hstep (i - 1) (by omega)
    rwa [Nat.sub_add_cancel h1] at h
  have hnormJ : ∀ i, i < k → B ≤ Subgroup.normalizer (Js i : Set G) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rw [hJ0]
      exact hJ₀B
    · obtain ⟨-, -, -, -, -, hBi, -⟩ := hstep' i hpos hi
      exact hBi
  obtain ⟨-, -, hFess, -, hKchev, -⟩ := hstep' (k - 1) (by omega) hk1
  refine prop33_end hc h1135 hInn h65 h76 hR3 hS hEB hEcard hk hmk hmax' hJ₀ hJ₀B
    (F := Es (k - 1)) (K := Js (k - 1)) ?_ hFcard1 hFess hK hKchev (hnormJ (k - 1) hk1) ?_ ?_
  · have h := hmonoE 0 (k - 1) (Nat.zero_le _) hk1
    rwa [hE0] at h
  · have h := hmonoJ 0 (k - 1) (Nat.zero_le _) hk1
    rwa [hJ0] at h
  · exact fun e he hce => faithful_outer hp hEB hE0 hk hnormJ hstep he hce

end CFSG.LocalAnalysis.GLTheoremA
