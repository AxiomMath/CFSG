module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9DataAux
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Helpers

variable {Y : Type*} [Group Y] [Finite Y]

theorem card_sylow_three_of_le (Q : Sylow 3 Y) {K : Subgroup Y} (hQK : (Q : Subgroup Y) ≤ K)
    (e : K ≃* alternatingGroup (Fin 9)) : Nat.card (Q : Subgroup Y) = 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Nat.card (alternatingGroup (Fin 9)) = 3 ^ 4 * 2240 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  have h := (Q.subtype hQK).card_eq_multiplicity
  rw [Sylow.coe_subtype, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv,
    Nat.card_congr e.toEquiv, hA, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)] at h
  simpa using h

theorem exists_injective_map_le_sylow {θ₀ : alternatingGroup (Fin 9) →* Y}
    (hθ₀ : Function.Injective θ₀) (Q : Sylow 3 Y) :
    ∃ θ : alternatingGroup (Fin 9) →* Y, Function.Injective θ ∧
      (a9Base ⊔ Subgroup.zpowers a9σ).map θ ≤ Q := by
  obtain ⟨S, hS⟩ := (isPGroup_a9Base_sup.map θ₀).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S Q
  refine ⟨(MulAut.conj g).toMonoidHom.comp θ₀, (MulAut.conj g).injective.comp hθ₀, ?_⟩
  rw [← hg, sylow_conjugate_eq_map, ← Subgroup.map_map]
  exact Subgroup.map_mono hS

theorem eq_sup_zpowers_of_card {B T : Subgroup Y} {s : Y} (hBT : B ≤ T) (hsT : s ∈ T)
    (hsB : s ∉ B) (hB : Nat.card B = 3 ^ 3) (hT : Nat.card T = 3 ^ 4) :
    T = B ⊔ Subgroup.zpowers s := by
  have hST : B ⊔ Subgroup.zpowers s ≤ T := sup_le hBT (Subgroup.zpowers_le.mpr hsT)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_sup_left : B ≤ B ⊔ Subgroup.zpowers s)
  have hdvd := Subgroup.card_dvd_of_le hST
  rw [hm, hB, hT, show 3 ^ 4 = 3 ^ 3 * 3 by norm_num] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd)
    with rfl | rfl
  · refine absurd ?_ hsB
    rw [Subgroup.eq_of_le_of_card_ge (le_sup_left : B ≤ B ⊔ Subgroup.zpowers s)
      (by rw [hm, hB, mul_one])]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  · exact (Subgroup.eq_of_le_of_card_ge hST (by rw [hm, hB, hT]; norm_num)).symm

theorem mem_normalizer_closure_pair {a b g : Y}
    (ha : g * a * g⁻¹ ∈ Subgroup.closure {a, b}) (hb : g * b * g⁻¹ ∈ Subgroup.closure {a, b}) :
    g ∈ Subgroup.normalizer ((Subgroup.closure {a, b} : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  rw [MonoidHom.map_closure, Subgroup.closure_le, Set.image_pair]
  rintro _ (rfl | rfl)
  exacts [ha, hb]

end Helpers

theorem exists_a9DataCore_of (hL : KFactA9Local) {G : Type} [Group G] [Finite G]
    [Fact (Nat.Prime 3)] {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hglob : CFSG.AGLEmbeddingD2.AGLGlobal G) (hext : D1Extremal 3 P M H R)
    (hrbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
    (hred : ReducedNongeneration 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))))
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K)
    (hC : Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) = ⊥)
    (hZ : Subgroup.center K = ⊥)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 9))) :
    ∃ (X : Subgroup G) (σ z : G), D1A9DataCore P M H R X σ z := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨e'⟩ := e
  have e₀ : K ≃* alternatingGroup (Fin 9) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e'
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hRH : R ≤ H := hext.le_H
  have hRp : IsPGroup 3 (R.subgroupOf H) := hext.isPGroup.comap_subtype
  have hO : (3 : ℕ).Coprime (Nat.card (primeComplementCore (G := H) 3)) :=
    primeComplementCore_coprime 3
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  set X₀ := ((H ⊓ M).subgroupOf H).map π
  have hinj : ∀ a ∈ R.subgroupOf H, ∀ b ∈ R.subgroupOf H, π a = π b → a = b :=
    fun a ha b hb hab => eq_of_mk_eq_of_isPGroup hp _ hO hRp ha hb hab
  have hRK : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ≤ K := by
    have : Finite (MulAut K) := MulEquiv.finite_left
    have hOut : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) := by
      rw [← Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e₀.symm).toEquiv]
      exact not_dvd_card_outer_alternatingGroup 9 (by norm_num) 3 hp (by norm_num)
    intro x hx
    obtain ⟨k, hk⟩ := Rbar.isPGroup' ⟨x, hx⟩
    have hxk : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hmem := mem_sup_centralizer_of_pow hp hOut hxk
    rwa [hC, sup_bot_eq] at hmem
  have hQcard := card_sylow_three_of_le Rbar hRK e₀
  obtain ⟨θ, hθ, hθT⟩ := exists_injective_map_le_sylow
    (θ₀ := K.subtype.comp e₀.symm.toMonoidHom) (K.subtype_injective.comp e₀.symm.injective) Rbar
  have hBQ : a9Base.map θ ≤ Rbar := (Subgroup.map_mono le_sup_left).trans hθT
  have hσQ : θ a9σ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) :=
    hθT (Subgroup.mem_map_of_mem θ (Subgroup.mem_sup_right (Subgroup.mem_zpowers a9σ)))
  have hzB : θ a9z ∈ a9Base.map θ := Subgroup.mem_map_of_mem θ a9z_mem
  have hσB : θ a9σ ∉ a9Base.map θ := fun h => a9σ_not_mem ((Subgroup.mem_map_iff_mem hθ).mp h)
  have hBel : IsElemAbelian 3 (a9Base.map θ) := elementary_abelian_map 3 isElemAbelian_a9Base θ
  have hBcard : Nat.card (a9Base.map θ) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective hθ, card_a9Base]
  have hQX₀ : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ≤ X₀ :=
    (subgroup_le_weakCore_of_rank 3 hp _ hred.three_le_pRank).trans hred.weakCore_le
  have hIS : A9InSitu (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (a9Base.map θ) X₀ :=
    hL _ K hKn ⟨e₀⟩ hC Rbar _ _ hBQ hBel hBcard hred.weakCore_le hred.ne_top
  have hzc : ∀ q ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      q * θ a9z = θ a9z * q := by
    rw [eq_sup_zpowers_of_card hBQ hσQ hσB hBcard hQcard]
    intro q hq
    refine Subgroup.mem_centralizer_singleton_iff.mp ((sup_le ?_ ?_ : _ ≤
      Subgroup.centralizer {θ a9z}) hq)
    · rintro _ ⟨b, hb, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg θ (congrArg Subtype.val
        ((isMulCommutative_iff.mp isElemAbelian_a9Base.1) ⟨b, hb⟩ ⟨a9z, a9z_mem⟩))
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        commute_a9σ_a9z.eq]
  have hBQ' := hBQ
  rw [hrbar] at hBQ' hσQ
  obtain ⟨E₁, hE₁R, hE₁map, hE₁, hE₁card⟩ := exists_isElemAbelian_lift hp _ hO hRp hBel hBQ'
  obtain ⟨s, hsR, hsπ⟩ := hσQ
  obtain ⟨t, htR, htπ⟩ := hBQ' hzB
  have hmemE : ∀ a ∈ R.subgroupOf H, π a ∈ a9Base.map θ → a ∈ E₁ := by
    intro a ha h
    rw [← hE₁map] at h
    obtain ⟨b, hb, hba⟩ := h
    rwa [← hinj b (hE₁R hb) a ha hba]
  have htE : t ∈ E₁ := hmemE t htR (by rw [htπ]; exact hzB)
  set X : Subgroup G := E₁.map H.subtype with hX
  have hXR : X ≤ R := (Subgroup.map_mono hE₁R).trans (Subgroup.map_subgroupOf_eq_of_le hRH).le
  have hXmap : (X.subgroupOf H).map π = a9Base.map θ := by
    rw [hX, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective,
      hE₁map]
  have hXcard : Nat.card X = 3 ^ 3 := by
    rw [hX, Subgroup.card_map_of_injective H.subtype_injective, hE₁card, hBcard]
  have hfix : ∀ x ∈ X, (s : G) * x * (s : G)⁻¹ = x → x ∈ Subgroup.zpowers (t : G) := by
    rintro _ ⟨a, haE, rfl⟩ hx
    have haR := hE₁R haE
    have hsa : s * a * s⁻¹ = a := Subtype.ext (by simpa using hx)
    have ha : π a ∈ a9Base.map θ := by
      rw [← hE₁map]
      exact Subgroup.mem_map_of_mem π haE
    obtain ⟨b, hb, hba⟩ := ha
    have hb' : a9σ * b * a9σ⁻¹ = b := hθ (by
      rw [map_mul, map_mul, map_inv, hba, ← hsπ, ← map_inv, ← map_mul, ← map_mul, hsa])
    obtain ⟨n, rfl⟩ := exists_eq_a9z_pow_of_conj_eq hb hb'
    have han : a = t ^ n := hinj a haR _ (Subgroup.pow_mem _ htR n) (by
      rw [← hba, map_pow, map_pow, htπ])
    rw [han]
    exact ⟨n, by simp⟩
  have hgX : θ a9g ∉ X₀ := fun h => by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hIS.le_normalizer h) (θ a9z)).mp hzB
    rw [← map_inv, ← map_mul, ← map_mul, a9g_conj_a9z] at h1
    exact hσB h1
  have hgN : θ a9g ∈ Subgroup.normalizer
      ((Subgroup.closure {θ a9σ, θ a9z} : Subgroup (H ⧸ primeComplementCore (G := H) 3)) :
        Set (H ⧸ primeComplementCore (G := H) 3)) := by
    refine mem_normalizer_closure_pair ?_ ?_
    · rw [← map_inv, ← map_mul, ← map_mul, a9g_conj_a9σ, map_inv]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    · rw [← map_inv, ← map_mul, ← map_mul, a9g_conj_a9z]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
  refine ⟨X, s, t, ?_⟩
  refine
    { surv := ?_
      elem := elementary_abelian_map 3 hE₁ H.subtype
      card_X := hXcard
      card_R := ?_
      normalizer_le := ?_
      pRank_le := pRank_inf_le_of_pRank_top_le hp hIS.pRank_le
      perfect_le := fun Y hY hYY => le_glbPrimeCore_of_perfect hIS.solvable hY hYY
      pcore_le := fun Y hY hYN hYp => le_sup_glbPrimeCore_of_forall
        (fun W hW hWn hWp => by rw [hXmap]; exact hIS.pcore_le W hW hWn hWp) hY hYN hYp
      z_mem := ⟨t, htE, rfl⟩
      z_ne := ?_
      z_center := ?_
      center_le := ?_
      σ_mem := Subgroup.mem_subgroupOf.mp hsR
      σ_not_mem := ?_
      σ_pow := ?_
      fix := hfix
      escape := ?_ }
  ·
    have hX1 : X ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hXcard
      norm_num at hXcard
    refine hext.survivorData_of_map hglob hXR hX1 (fun W hW hWn hWc => ?_) ?_ ?_
    · exact hIS.primeCore W hW ((Subgroup.normal_subgroupOf_iff_le_normalizer hW).mp hWn) hWc
    · rw [hXmap]
      exact hIS.normal_dichotomy
    · rw [hXmap, ← hrbar]
      exact hIS.centralizer_le.trans hBQ
  ·
    rw [← hQcard, hrbar, card_map_mk_of_isPGroup hp _ hO hRp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv]
  ·
    refine le_normalizer_of_forall_mul_mul_inv_mem fun k hk x hx => ?_
    obtain ⟨⟨hkH, hkM⟩, hkN⟩ := hk
    obtain ⟨a, haE, rfl⟩ := hx
    have hkx : k * a * k⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hkN _).mp (hXR ⟨a, haE, rfl⟩)
    have hkX₀ : π ⟨k, hkH⟩ ∈ X₀ :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ⟨hkH, hkM⟩)
    have h1 : π (⟨k, hkH⟩ * a * (⟨k, hkH⟩ : H)⁻¹) ∈ a9Base.map θ := by
      rw [map_mul, map_mul, map_inv]
      refine (Subgroup.mem_normalizer_iff.mp (hIS.le_normalizer hkX₀) (π a)).mp ?_
      rw [← hE₁map]
      exact Subgroup.mem_map_of_mem π haE
    have h2 : (⟨k, hkH⟩ * a * (⟨k, hkH⟩ : H)⁻¹ : H) ∈ R.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr (by simpa using hkx)
    exact ⟨_, hmemE _ h2 h1, by simp⟩
  ·
    intro h1
    have ht1 : t = 1 := Subtype.ext h1
    exact a9z_ne_one (hθ (by rw [← htπ, ht1, map_one, map_one]))
  ·
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : (⟨r, hRH hr⟩ : H) ∈ R.subgroupOf H := Subgroup.mem_subgroupOf.mpr hr
    have h := hinj _ (Subgroup.mul_mem _ hr' htR) _ (Subgroup.mul_mem _ htR hr') (by
      rw [map_mul, map_mul, htπ]
      refine hzc _ ?_
      rw [hrbar]
      exact Subgroup.mem_map_of_mem π hr')
    simpa using congrArg Subtype.val h
  ·
    intro r hr
    obtain ⟨hrR, hrC⟩ := hr
    have hr' : (⟨r, hRH hrR⟩ : H) ∈ R.subgroupOf H := Subgroup.mem_subgroupOf.mpr hrR
    have hrQ : π ⟨r, hRH hrR⟩ ∈ X₀ := hQX₀ (by
      rw [hrbar]
      exact Subgroup.mem_map_of_mem π hr')
    have hrc : π ⟨r, hRH hrR⟩ ∈ Subgroup.centralizer
        ((a9Base.map θ : Subgroup (H ⧸ primeComplementCore (G := H) 3)) :
          Set (H ⧸ primeComplementCore (G := H) 3)) := by
      rw [Subgroup.mem_centralizer_iff, ← hE₁map]
      rintro _ ⟨a, haE, rfl⟩
      rw [← map_mul, ← map_mul]
      refine congrArg π (Subtype.ext ?_)
      simpa using Subgroup.mem_centralizer_iff.mp hrC _ (hXR ⟨a, haE, rfl⟩)
    have hrX : r ∈ X := ⟨_, hmemE _ hr' (hIS.centralizer_le ⟨hrQ, hrc⟩), rfl⟩
    refine hfix r hrX ?_
    have hsr := Subgroup.mem_centralizer_iff.mp hrC _ (Subgroup.mem_subgroupOf.mp hsR)
    rw [hsr, mul_inv_cancel_right]
  ·
    rintro ⟨a, haE, ha⟩
    have has : a = s := Subtype.ext ha
    subst has
    refine hσB ?_
    rw [← hsπ, ← hE₁map]
    exact Subgroup.mem_map_of_mem π haE
  ·
    have h := hinj _ (Subgroup.pow_mem _ hsR 3) _ (Subgroup.one_mem _) (by
      rw [map_pow, hsπ, ← map_pow, a9σ_pow_three, map_one, map_one])
    simpa using congrArg Subtype.val h
  ·
    intro hN
    have hOM : primeComplementCore (G := H) 3 ≤ (H ⊓ M).subgroupOf H := by
      rw [← glbPrimeCore_subgroupOf]
      exact glbPrimeCore_subgroupOf_le_inf hext.primeCore_le
    have hDp : IsPGroup 3 (Subgroup.closure {s, t} : Subgroup H) := hRp.to_le
      ((Subgroup.closure_le _).mpr (by rintro _ (rfl | rfl); exacts [hsR, htR]))
    have hNH : Subgroup.normalizer ((Subgroup.closure {s, t} : Subgroup H) : Set H) ≤
        (H ⊓ M).subgroupOf H := fun n hn => by
      refine Subgroup.mem_subgroupOf.mpr ⟨n.2, hN ?_⟩
      have h := Subgroup.le_normalizer_map H.subtype ⟨n, hn, rfl⟩
      rwa [MonoidHom.map_closure, Set.image_pair] at h
    have h1 := le_map_of_comap_le (QuotientGroup.mk'_surjective _)
      ((comap_normalizer_map_le_sup hp _ hO hDp).trans (sup_le hOM hNH))
    rw [MonoidHom.map_closure, Set.image_pair, hsπ, htπ] at h1
    exact hgX (h1 hgN)

theorem stmtA9Data_of (hL : KFactA9Local) : StmtA9Data := by
  intro G _ _ _ P M H R Rbar hcfg K hK huniq hcent hZ e
  obtain ⟨X, σ, z, hcore⟩ := exists_a9DataCore_of hL hcfg.glob hcfg.ext hcfg.rbar hcfg.red hK huniq
    (hcfg.centralizer_eq_bot hK huniq hcent hZ) hZ e
  exact ⟨X, σ, z, { hcore with four_le := betaFour_all_sylows_rank_ge_four hcfg.loc.beta P }⟩

end CFSG.AGLEmbedding
