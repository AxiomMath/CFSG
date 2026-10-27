module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2GenDefs
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfigCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (PointConfig pointConfig_of_u3)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

open CFSG.ABGLocalTools in
private theorem torA_frattini_ker {Γ Q : Type*} [Group Γ] [Finite Γ] [Group Q] {p : ℕ} [Fact p.Prime]
    (ψ : Γ →* Q) (hcop : Nat.Coprime p (Nat.card ψ.ker)) {T : Subgroup Γ} (hT : IsPGroup p T)
    {j : Γ} (hj : ψ j ∈ Subgroup.normalizer ((T.map ψ : Subgroup Q) : Set Q)) :
    ∃ n ∈ Subgroup.normalizer (T : Set Γ), ψ n = ψ j := by
  classical
  set K := ψ.ker with hK
  set H : Subgroup Γ := K ⊔ T with hH
  have hTH : IsSylowOf p T H := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_right, hT, ?_⟩
    rw [hH, relIndex_sup_eq_relIndex_of_normal K T]
    intro hdvd
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop)
      (hdvd.trans (Subgroup.index_dvd_card (T.subgroupOf K)))
  set Tj : Subgroup Γ := T.map (MulAut.conj j).toMonoidHom with hTj
  have hmemTj : ∀ y, y ∈ Tj ↔ j⁻¹ * y * j ∈ T := by
    intro y
    rw [hTj, Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hTjH : Tj ≤ H := by
    intro y hy
    rw [hmemTj] at hy
    have h1 : ψ y ∈ T.map ψ := by
      have h2 := (Subgroup.mem_normalizer_iff.mp hj (ψ (j⁻¹ * y * j))).mp
        (Subgroup.mem_map_of_mem ψ hy)
      have e : ψ j * ψ (j⁻¹ * y * j) * (ψ j)⁻¹ = ψ y := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        group
      rwa [e] at h2
    obtain ⟨t', ht', hψ⟩ := h1
    have hk : y * t'⁻¹ ∈ K := by
      rw [hK, MonoidHom.mem_ker, map_mul, map_inv, ← hψ, mul_inv_cancel]
    have : y = (y * t'⁻¹) * t' := by group
    rw [this]
    exact Subgroup.mul_mem_sup hk ht'
  have hcardTj : Nat.card Tj = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj j).injective
  have hTjS : IsSylowOf p Tj H := isSylowOf_of_card hTjH (by rw [hcardTj]; exact hTH.card_eq)
  obtain ⟨x, hxH, hx⟩ := CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj hTH hTjS
  obtain ⟨k, hk, t, htT, hkt⟩ := Subgroup.mem_sup_of_normal_left.mp hxH
  subst hkt
  refine ⟨k⁻¹ * j, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : y ∈ T ↔ j * y * j⁻¹ ∈ Tj := by
      rw [hmemTj]
      have : j⁻¹ * (j * y * j⁻¹) * j = y := by group
      rw [this]
    have h2 : (j * y * j⁻¹ ∈ Tj) ↔ (k * t)⁻¹ * (j * y * j⁻¹) * (k * t) ∈ T := hx _
    have h3 : (k * t)⁻¹ * (j * y * j⁻¹) * (k * t) =
        t⁻¹ * ((k⁻¹ * j) * y * (k⁻¹ * j)⁻¹) * t := by group
    have h4 : t⁻¹ * ((k⁻¹ * j) * y * (k⁻¹ * j)⁻¹) * t ∈ T ↔
        (k⁻¹ * j) * y * (k⁻¹ * j)⁻¹ ∈ T := by
      constructor
      · intro h
        have := T.mul_mem (T.mul_mem htT h) (T.inv_mem htT)
        simpa [mul_assoc] using this
      · intro h
        exact T.mul_mem (T.mul_mem (T.inv_mem htT) h) htT
    rw [h1, h2, h3, h4]
  · rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]

omit [Finite G] in
private theorem torA_T_le_J (P : Sylow p G) (x : G) (J : Subgroup G) : u3T P x J ≤ J := inf_le_right

omit [Finite G] in
private theorem torA_T_le_P (P : Sylow p G) (x : G) (J : Subgroup G) : u3T P x J ≤ (P : Subgroup G) :=
  inf_le_left.trans inf_le_left

private theorem torA_isPGroup_T (P : Sylow p G) (x : G) (J : Subgroup G) :
    IsPGroup p ((u3T P x J).subgroupOf J) :=
  (P.isPGroup'.to_le (torA_T_le_P P x J)).comap_subtype

private theorem torA_ker_coprime (p : ℕ) (J : Subgroup G) {Q : Type} [Group Q] (ψ : ↥J →* Q)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) : Nat.Coprime p (Nat.card ψ.ker) := by
  have hle : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact CFSG.AGLEmbedding.glbPrimeCore_coprime p J

theorem u3_normalizer_onto_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J) :
    ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J ∧ Typ p Q ∧
      ∀ q ∈ Subgroup.normalizer (((u3T P x J).subgroupOf J).map ψ : Set Q),
        ∃ n ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ⊓ J, ∃ hn : n ∈ J, ψ ⟨n, hn⟩ = q := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨Q, iQ, ψ, hsurj, hker, hU3⟩ := hc.typ
  refine ⟨Q, iQ, ψ, hsurj, hker, hU3, ?_⟩
  intro q hq
  obtain ⟨j, rfl⟩ := hsurj q
  obtain ⟨n, hn, hψ⟩ := torA_frattini_ker ψ (torA_ker_coprime p J ψ hker) (torA_isPGroup_T P x J) hq
  refine ⟨(n : G), Subgroup.mem_inf.mpr ⟨?_, n.2⟩, n.2, ?_⟩
  · have := u3main_mem_normalizer_map hn
    rwa [Subgroup.map_subgroupOf_eq_of_le (torA_T_le_J P x J)] at this
  · simpa using hψ

private noncomputable def torA_ext {Q : Type} [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) (g : G) : Q :=
  open Classical in if h : g ∈ J then ψ ⟨g, h⟩ else 1

private theorem torA_ext_of_mem {Q : Type} [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) {g : G}
    (hg : g ∈ J) : torA_ext J ψ g = ψ ⟨g, hg⟩ := by
  unfold torA_ext
  rw [dif_pos hg]

private theorem torA_ext_mul {Q : Type} [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) {a b : G}
    (ha : a ∈ J) (hb : b ∈ J) : torA_ext J ψ (a * b) = torA_ext J ψ a * torA_ext J ψ b := by
  rw [torA_ext_of_mem J ψ ha, torA_ext_of_mem J ψ hb, torA_ext_of_mem J ψ (J.mul_mem ha hb)]
  exact map_mul ψ ⟨a, ha⟩ ⟨b, hb⟩

private theorem torA_ext_inv {Q : Type} [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) {a : G}
    (ha : a ∈ J) : torA_ext J ψ a⁻¹ = (torA_ext J ψ a)⁻¹ := by
  rw [torA_ext_of_mem J ψ ha, torA_ext_of_mem J ψ (J.inv_mem ha)]
  exact map_inv ψ ⟨a, ha⟩

private theorem torA_ext_one {Q : Type} [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) :
    torA_ext J ψ 1 = 1 := by
  rw [torA_ext_of_mem J ψ J.one_mem]
  exact map_one ψ

private theorem torA_ext_pow {Q : Type} [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) {a : G}
    (ha : a ∈ J) (k : ℕ) : torA_ext J ψ (a ^ k) = (torA_ext J ψ a) ^ k := by
  rw [torA_ext_of_mem J ψ ha, torA_ext_of_mem J ψ (J.pow_mem ha k)]
  exact map_pow ψ ⟨a, ha⟩ k

theorem u3_torusProps_NJ_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J) (hIrr : TypeTorusIrred Typ p) (hFpf : TypeTorusFpf Typ p) (hOn : TypeTorusOnCenter Typ p) :
    TorusProps p (u3T P x J) (Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ⊓ J) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨Q, iQ, ψ, hsurj, hker, hU3, hnorm⟩ := u3_normalizer_onto_gen hc
  haveI : Finite Q := Finite.of_surjective ψ hsurj
  have hTJ : u3T P x J ≤ J := torA_T_le_J P x J
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := torA_ker_coprime p J ψ hker
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p (u3T P x J) J :=
    hc.generic.2.2.1.inf_of_le_normalizer hc.le_cent hc.cent_le
  obtain ⟨S, hS⟩ := hsyl.exists_sylow_eq_subgroupOf
  set TS : Sylow p Q := S.mapSurjective hsurj with hTSdef
  set T : Subgroup G := u3T P x J with hT
  set F : Subgroup G := Subgroup.normalizer (T : Set G) ⊓ J with hF
  set Tb : Subgroup Q := (T.subgroupOf J).map ψ with hTb
  have hTS : (TS : Subgroup Q) = Tb := by
    show (S : Subgroup ↥J).map ψ = _
    rw [hS]
  obtain ⟨e, he_of_mem, he_mul, he_inv, he_one, he_pow⟩ : ∃ e : G → Q,
      (∀ g (hg : g ∈ J), e g = ψ ⟨g, hg⟩) ∧ (∀ {a b : G}, a ∈ J → b ∈ J → e (a * b) = e a * e b) ∧
      (∀ {a : G}, a ∈ J → e a⁻¹ = (e a)⁻¹) ∧ e 1 = 1 ∧
      (∀ {a : G}, a ∈ J → ∀ k : ℕ, e (a ^ k) = e a ^ k) :=
    ⟨torA_ext J ψ, fun g hg => torA_ext_of_mem J ψ hg, fun ha hb => torA_ext_mul J ψ ha hb,
      fun ha => torA_ext_inv J ψ ha, torA_ext_one J ψ, fun ha k => torA_ext_pow J ψ ha k⟩
  have he_mk : ∀ j : ↥J, e (j : G) = ψ j := fun j => he_of_mem _ j.2
  have hinj0 : ∀ t ∈ T.subgroupOf J, ψ t = 1 → t = 1 :=
    u3main_eq_one_of_ker ψ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop)
      (torA_isPGroup_T P x J)
  have hinj : ∀ a ∈ T, ∀ b ∈ T, e a = e b → a = b := by
    intro a ha b hb hab
    have haJ := hTJ ha
    have hbJ := hTJ hb
    have h1 : (⟨a, haJ⟩ * ⟨b, hbJ⟩⁻¹ : ↥J) ∈ T.subgroupOf J := by
      rw [Subgroup.mem_subgroupOf]
      exact T.mul_mem ha (T.inv_mem hb)
    have h2 : ψ (⟨a, haJ⟩ * ⟨b, hbJ⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, ← he_of_mem _ haJ, ← he_of_mem _ hbJ]
      rw [hab, mul_inv_cancel]
    have h3 := hinj0 _ h1 h2
    have : (⟨a, haJ⟩ : ↥J) = ⟨b, hbJ⟩ := mul_inv_eq_one.mp h3
    exact congrArg Subtype.val this
  have hmemTb : ∀ q, q ∈ Tb ↔ ∃ t ∈ T, e t = q := by
    intro q
    rw [hTb, Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a : G), ha, he_mk a⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, hTJ ht⟩, ht, (he_of_mem _ (hTJ ht)).symm⟩
  have hC : ∀ t ∈ T, (e t ∈ Subgroup.centralizer (Tb : Set Q) ↔
      t ∈ Subgroup.centralizer (T : Set G)) := by
    intro t ht
    have htJ := hTJ ht
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h t' ht'
      have h1 := h (e t') ((hmemTb _).mpr ⟨t', ht', rfl⟩)
      rw [← he_mul (hTJ ht') htJ, ← he_mul htJ (hTJ ht')] at h1
      exact hinj _ (T.mul_mem ht' ht) _ (T.mul_mem ht ht') h1
    · intro h q hq
      obtain ⟨t', ht', rfl⟩ := (hmemTb q).mp hq
      rw [← he_mul (hTJ ht') htJ, ← he_mul htJ (hTJ ht'), h t' ht']
  have hnorm' : ∀ q ∈ Subgroup.normalizer (Tb : Set Q), ∃ n ∈ F, e n = q := by
    intro q hq
    obtain ⟨n, hnF, hnJ, hψ⟩ := hnorm q hq
    exact ⟨n, hnF, by rw [he_of_mem _ hnJ, hψ]⟩
  have hconj : ∀ m ∈ F, ∀ t ∈ J, e (m * t * m⁻¹) = e m * e t * (e m)⁻¹ := by
    intro m hm t ht
    have hmJ := (Subgroup.mem_inf.mp hm).2
    rw [he_mul (J.mul_mem hmJ ht) (J.inv_mem hmJ), he_mul hmJ ht,
      he_inv hmJ]
  have hirr : ∀ {A : Subgroup Q}, A ≤ Tb → Tb ⊓ Subgroup.centralizer (Tb : Set Q) ≤ A →
      (∀ n ∈ Subgroup.normalizer (Tb : Set Q), ∀ a ∈ A, n * a * n⁻¹ ∈ A) →
      A = Tb ⊓ Subgroup.centralizer (Tb : Set Q) ∨ A = Tb := by
    intro A h1 h2 h3
    have := hIrr Q hU3 TS A (by rw [hTS]; exact h1)
      (by rw [hTS]; exact h2) (by rw [hTS]; exact h3)
    rwa [hTS] at this
  have hfpf : ∀ {t : Q}, t ∈ Tb → (∀ n ∈ Subgroup.normalizer (Tb : Set Q),
      n * t * n⁻¹ * t⁻¹ ∈ Tb ⊓ Subgroup.centralizer (Tb : Set Q)) →
      t ∈ Tb ⊓ Subgroup.centralizer (Tb : Set Q) := by
    intro t ht h
    have := hFpf Q hU3 TS t (by rw [hTS]; exact ht) (by rw [hTS]; exact h)
    rwa [hTS] at this
  have hon : ∀ {c : Q}, c ∈ Tb → c ∈ Subgroup.centralizer (Tb : Set Q) → c ≠ 1 →
      ∀ k : ℤ, ¬ (p : ℤ) ∣ k → ∃ n ∈ Subgroup.normalizer (Tb : Set Q), n * c * n⁻¹ = c ^ k := by
    intro c hcT hcZ hc1 k hk
    have := hOn Q hU3 TS c (by rw [hTS]; exact hcT)
      (by rw [hTS]; exact hcZ) hc1 k hk
    rwa [hTS] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf t ht
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hf).1 t).mp ht
  · intro A hAT hZA hinv
    have hAJ : A ≤ J := hAT.trans hTJ
    set Ab : Subgroup Q := (A.subgroupOf J).map ψ with hAb
    have hmemAb : ∀ q, q ∈ Ab ↔ ∃ a ∈ A, e a = q := by
      intro q
      rw [hAb, Subgroup.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨(a : G), ha, he_mk a⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, hAJ ht⟩, ht, (he_of_mem _ (hAJ ht)).symm⟩
    have h1 : Ab ≤ Tb := by
      intro q hq
      obtain ⟨a, ha, rfl⟩ := (hmemAb q).mp hq
      exact (hmemTb _).mpr ⟨a, hAT ha, rfl⟩
    have h2 : Tb ⊓ Subgroup.centralizer (Tb : Set Q) ≤ Ab := by
      intro q hq
      obtain ⟨hqT, hqC⟩ := Subgroup.mem_inf.mp hq
      obtain ⟨t, ht, rfl⟩ := (hmemTb q).mp hqT
      have : t ∈ zOf T := Subgroup.mem_inf.mpr ⟨ht, (hC t ht).mp hqC⟩
      exact (hmemAb _).mpr ⟨t, hZA this, rfl⟩
    have h3 : ∀ n ∈ Subgroup.normalizer (Tb : Set Q), ∀ a ∈ Ab, n * a * n⁻¹ ∈ Ab := by
      intro n hn a ha
      obtain ⟨m, hmF, rfl⟩ := hnorm' n hn
      obtain ⟨a₀, ha₀, rfl⟩ := (hmemAb a).mp ha
      refine (hmemAb _).mpr ⟨m * a₀ * m⁻¹, hinv m hmF a₀ ha₀, ?_⟩
      exact hconj m hmF a₀ (hAJ ha₀)
    rcases hirr h1 h2 h3 with h | h
    · left
      refine le_antisymm (fun a ha => ?_) hZA
      have haT := hAT ha
      have h4 : e a ∈ Ab := (hmemAb _).mpr ⟨a, ha, rfl⟩
      rw [h] at h4
      exact Subgroup.mem_inf.mpr ⟨haT, (hC a haT).mp (Subgroup.mem_inf.mp h4).2⟩
    · right
      refine le_antisymm hAT (fun t ht => ?_)
      have h4 : e t ∈ Tb := (hmemTb _).mpr ⟨t, ht, rfl⟩
      rw [← h] at h4
      obtain ⟨a, ha, hat⟩ := (hmemAb _).mp h4
      have h5 := hinj a (hAT ha) t ht hat
      exact h5 ▸ ha
  · intro t ht h
    have htb : e t ∈ Tb := (hmemTb _).mpr ⟨t, ht, rfl⟩
    have hz : ∀ z ∈ zOf T, e z ∈ Tb ⊓ Subgroup.centralizer (Tb : Set Q) := by
      intro z hz
      obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hz
      exact Subgroup.mem_inf.mpr ⟨(hmemTb _).mpr ⟨z, hzT, rfl⟩, (hC z hzT).mpr hzC⟩
    have h6 := hfpf htb (by
      intro n hn
      obtain ⟨m, hmF, rfl⟩ := hnorm' n hn
      have h1 := hz _ (h m hmF)
      have hmJ := (Subgroup.mem_inf.mp hmF).2
      have htJ := hTJ ht
      rw [he_mul (J.mul_mem (J.mul_mem hmJ htJ) (J.inv_mem hmJ)) (J.inv_mem htJ),
        hconj m hmF t htJ, he_inv htJ] at h1
      exact h1)
    exact Subgroup.mem_inf.mpr ⟨ht, (hC t ht).mp (Subgroup.mem_inf.mp h6).2⟩
  · intro z hz k hk
    obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hz
    by_cases hz1 : z = 1
    · subst hz1
      exact ⟨1, F.one_mem, by simp⟩
    · have hzJ := hTJ hzT
      have hez1 : e z ≠ 1 := by
        intro h1
        apply hz1
        exact hinj z hzT 1 T.one_mem (by rw [h1, he_one])
      have hezT : e z ∈ Tb := (hmemTb _).mpr ⟨z, hzT, rfl⟩
      have hezC : e z ∈ Subgroup.centralizer (Tb : Set Q) := (hC z hzT).mpr hzC
      obtain ⟨n, hn, hnz⟩ := hon hezT hezC hez1 (k : ℤ) (by exact_mod_cast hk)
      obtain ⟨m, hmF, rfl⟩ := hnorm' n hn
      refine ⟨m, hmF, ?_⟩
      have hmz : m * z * m⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hmF).1 z).mp hzT
      apply hinj _ hmz _ (T.pow_mem hzT k)
      rw [hconj m hmF z hzJ, hnz, he_pow hzJ, zpow_natCast]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
