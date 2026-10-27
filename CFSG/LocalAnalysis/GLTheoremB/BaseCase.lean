module

public import CFSG.LocalAnalysis.GLTheoremB.UniqStatements
public import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section General

variable {G : Type*} [Group G]

theorem le_normalizer_pCoreOf (r : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (pCoreOf r X : Set G) := by
  have : (CFSG.Open.pCore r ↥X).Characteristic := CFSG.LieType.BorelTits.pCore_characteristic r
  exact Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.Open.pCore r ↥X))

theorem pCoreOf_inf_le {r : ℕ} [Fact r.Prime] [Finite G] (A Z : Subgroup G) :
    pCoreOf r A ⊓ Z ≤ pCoreOf r (A ⊓ Z) := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer r ?_ ?_ ?_
  · exact inf_le_inf_right Z (CFSG.LieType.BorelTits.pCoreOf_le r A)
  · intro x hx
    have hxA := Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf r A hx.1)
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · rintro ⟨hnA, hnZ⟩
      exact ⟨(hxA n).1 hnA, Z.mul_mem (Z.mul_mem hx.2 hnZ) (Z.inv_mem hx.2)⟩
    · rintro ⟨hnA, hnZ⟩
      refine ⟨(hxA n).2 hnA, ?_⟩
      have := Z.mul_mem (Z.mul_mem (Z.inv_mem hx.2) hnZ) hx.2
      simpa [mul_assoc] using this
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup r A).to_le inf_le_left

theorem pCoreOf_two_le_glaPPrimeCoreOf [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (X : Subgroup G) : pCoreOf 2 X ≤ GLAPPrimeCoreOf p X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Subgroup.map_mono (le_sSup ⟨CFSG.LieType.BorelTits.pCore_normal 2, ?_⟩)
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) 2).exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

theorem le_normalizer_glaPPrimeCoreOf (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (GLAPPrimeCoreOf p X : Set G) := by
  have key : ∀ x ∈ X, ∀ y ∈ GLAPPrimeCoreOf p X, x * y * x⁻¹ ∈ GLAPPrimeCoreOf p X := by
    intro x hx y hy
    obtain ⟨y', hy', rfl⟩ := hy
    refine ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, (GLAPPrimeCore.normal p ↥X).conj_mem y' hy' ⟨x, hx⟩, ?_⟩
    simp
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨key x hx y, fun h => by simpa [mul_assoc] using key x⁻¹ (inv_mem hx) _ h⟩

theorem not_dvd_card_glaPPrimeCoreOf [Finite G] {p : ℕ} (hp : p.Prime) (X : Subgroup G) :
    ¬ p ∣ Nat.card (GLAPPrimeCoreOf p X) := by
  have : Fact p.Prime := ⟨hp⟩
  unfold GLAPPrimeCoreOf
  rw [Subgroup.card_map_of_injective X.subtype_injective]
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card

theorem exists_ne_bot_le_pCoreOf [Finite G] {M : Subgroup G} (hM : IsTwoLocal M) :
    ∃ P : Subgroup G, P ≠ ⊥ ∧ IsPGroup 2 P ∧ P ≤ pCoreOf 2 M := by
  obtain ⟨P, hP, hP2, rfl⟩ := hM
  exact ⟨P, hP, hP2,
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hP2⟩

theorem even_card_glaPPrimeCoreOf_of_isTwoLocal [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M : Subgroup G} (hM : IsTwoLocal M) : Even (Nat.card (GLAPPrimeCoreOf p M)) := by
  obtain ⟨P, hP, hPp, hPle⟩ := exists_ne_bot_le_pCoreOf hM
  have h2 : Nat.card P ∣ Nat.card (GLAPPrimeCoreOf p M) :=
    Subgroup.card_dvd_of_le (hPle.trans (pCoreOf_two_le_glaPPrimeCoreOf hp hp2 M))
  obtain ⟨k, hk⟩ := hPp.exists_card_eq
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hP (Subgroup.eq_bot_of_card_eq P (by simpa using hk))
  rw [even_iff_two_dvd]
  exact (dvd_pow_self 2 hk1).trans (hk ▸ h2)

theorem normalizer_pCoreOf_eq_of_isMaxTwoLocal [Finite G] {M : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) : Subgroup.normalizer (pCoreOf 2 M : Set G) = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, -, hPle⟩ := exists_ne_bot_le_pCoreOf hM.1
  have hne : pCoreOf 2 M ≠ ⊥ := fun h => hP (le_bot_iff.1 (h ▸ hPle))
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 M : Set G)) :=
    ⟨pCoreOf 2 M, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M, rfl⟩
  exact hM.2 _ hloc (le_normalizer_pCoreOf 2 M)

theorem normalizer_ne_top_of_isPGroup_two [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) {T : Subgroup G} (h0 : T ≠ ⊥) (hT : IsPGroup 2 T) :
    Subgroup.normalizer (T : Set G) ≠ ⊤ := by
  intro htop
  have hnorm : T.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  have hT1 : T = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal T).resolve_left h0
  subst hT1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : IsPGroup 2 G := hT.of_equiv Subgroup.topEquiv
  have := hG.isNilpotent
  obtain ⟨a, b, hab⟩ := hna
  exact hab (IsSimpleGroup.comm_iff_isSolvable.2 inferInstance a b)

theorem normalizer_le_normalizer_sigmaOf (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (sigmaOf D : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_gLBConj_eq] at hn ⊢
  rw [← sigmaOf_gLBConj, hn]

theorem card_eq_of_index_eq {p : ℕ} (hp : p.Prime) {B K : Subgroup G} (hKB : K ≤ B)
    (hidx : (K.subgroupOf B).index = p) {n : ℕ} (hB : Nat.card B = p ^ (n + 1)) :
    Nat.card K = p ^ n := by
  have h1 := Subgroup.card_mul_index (K.subgroupOf B)
  rw [hidx, hB, pow_succ] at h1
  have h2 : Nat.card (K.subgroupOf B) = p ^ n := Nat.eq_of_mul_eq_mul_right hp.pos h1
  rw [← h2]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKB).toEquiv).symm

theorem le_iSup_inf_centralizer_hyperplane {p : ℕ} [Fact p.Prime] [Finite G] {E Y : Subgroup G}
    (hE : IsElemAbelian p E) [Nontrivial E] (hEY : E ≤ Subgroup.normalizer (Y : Set G))
    (hY : ¬ p ∣ Nat.card Y) :
    Y ≤ ⨆ (K : Subgroup G) (_ : K ≤ E ∧ (K.subgroupOf E).index = p),
      Y ⊓ Subgroup.centralizer (K : Set G) := by
  have : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hE.2 x x.2) }
  let _ : MulDistribMulAction E Y := Subgroup.conjMulDistribMulActionOfLeNormalizer E Y hEY
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := E) (H := Y) hY
  intro y hy
  have h1 : (⟨y, hy⟩ : Y) ∈ ⨆ (B : Subgroup E) (_ : B.index = p), CFSG.fixedPointSubgroup B Y :=
    hgen ▸ Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem Y.subtype h1
  simp only [Subgroup.map_iSup] at h2
  have hle : (⨆ (B : Subgroup E) (_ : B.index = p),
      (CFSG.fixedPointSubgroup B Y).map Y.subtype) ≤
      ⨆ (K : Subgroup G) (_ : K ≤ E ∧ (K.subgroupOf E).index = p),
        Y ⊓ Subgroup.centralizer (K : Set G) := by
    refine iSup₂_le fun B hB => ?_
    refine le_iSup_of_le (B.map E.subtype) (le_iSup_of_le ⟨Subgroup.map_subtype_le B, ?_⟩ ?_)
    · have hsub : (B.map E.subtype).subgroupOf E = B :=
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective B
      rw [hsub]
      exact hB
    · rintro _ ⟨z, hz, rfl⟩
      refine Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      have h3 : ((b : E) : G) * (z : G) * ((b : E) : G)⁻¹ = z := congrArg Subtype.val (hz ⟨b, hb⟩)
      simp only [Subgroup.coe_subtype]
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3
  exact hle h2

end General

section Setting

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem GLStanding.prime (hS : GLStanding G m p) : p.Prime := hS.beta.1

theorem GLStanding.ne_two (hS : GLStanding G m p) : p ≠ 2 := hS.beta.2.1

theorem GLStanding.card_eq (hS : GLStanding G m p) {B : Subgroup G} (hB : IsBOneMax p B) :
    Nat.card B = p ^ m := by
  have h := hB.1.2.1
  rw [hS.rank_eq] at h
  exact h

theorem GLStanding.nontrivial (hS : GLStanding G m p) {B : Subgroup G} (hB : IsBOneMax p B) :
    Nontrivial B := by
  refine Finite.one_lt_card_iff_nontrivial.1 ?_
  rw [hS.card_eq hB]
  exact Nat.one_lt_pow (by have := hS.four_le; omega) hS.prime.one_lt

theorem le_of_isPreUniquenessTwoLocal (hS : GLStanding G m p) {B M : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M) : B ≤ M := by
  have h3 : 3 ≤ pRank p B := by
    have := CFSG.SectionRank.le_pRank hS.prime.one_lt le_rfl hB.1.1 (hS.card_eq hB)
    have := hS.four_le
    omega
  exact Subgroup.le_normalizer.trans
    ((le_sSup ⟨B, le_rfl, h3, rfl⟩ : Subgroup.normalizer (B : Set G) ≤ GLBCore p 3 B).trans
      hM.2.2)

theorem normalizer_le_of_hyperplane (hS : GLStanding G m p) {B M K : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M) (hKB : K ≤ B)
    (hidx : (K.subgroupOf B).index = p) : Subgroup.normalizer (K : Set G) ≤ M := by
  have hp := hS.prime
  have hm4 := hS.four_le
  have hB' : Nat.card B = p ^ ((m - 1) + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
    exact hS.card_eq hB
  have hKcard := card_eq_of_index_eq hp hKB hidx hB'
  have hKel : IsElemAbelian p K := isElemAbelian_mono hB.1.1 hKB
  have h3 : 3 ≤ pRank p K := by
    have := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hKel hKcard
    omega
  exact (le_sSup ⟨K, hKB, h3, rfl⟩ : Subgroup.normalizer (K : Set G) ≤ GLBCore p 3 B).trans hM.2.2

theorem lemma91_i (hS : GLStanding G m p) {B M : Subgroup G} (hB : IsBOneMax p B)
    (hM : IsPreUniquenessTwoLocal p B M) {b : G} (hb : b ∈ B) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) ≤ M := by
  have hp := hS.prime
  have : Fact p.Prime := ⟨hp⟩
  have := hS.nontrivial hB
  have hBC : B ≤ Subgroup.centralizer ({b} : Set G) := fun b' hb' =>
    Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hB.1.1 hb' hb)
  have hBY : B ≤ Subgroup.normalizer
      (GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) : Set G) :=
    hBC.trans (le_normalizer_glaPPrimeCoreOf p _)
  refine (le_iSup_inf_centralizer_hyperplane hB.1.1 hBY
    (not_dvd_card_glaPPrimeCoreOf hp _)).trans (iSup₂_le fun K hK => inf_le_right.trans ?_)
  exact (Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_of_hyperplane hS hB hM hK.1 hK.2)

theorem lemma91_iff : Lemma91 ↔ Lemma91ii := by
  constructor
  · intro h G _ _ m p hS B M hB hM b hb hb1
    exact (h G m p hS B M hB hM b hb hb1).2
  · intro h G _ _ m p hS B M hB hM b hb hb1
    exact ⟨lemma91_i hS hB hM hb, h G m p hS B M hB hM b hb hb1⟩

theorem pCoreOf_inf_centralizer_le (h91 : Lemma91ii) (hS : GLStanding G m p) {B M : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    pCoreOf 2 M ⊓ Subgroup.centralizer ({b} : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer ({b} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (pCoreOf_inf_le M _).trans (h91 G m p hS B M hB hM b hb hb1)

theorem lemma92_of_inputs (h91 : Lemma91ii) (i1 : Input19Delta) (i2 : Input19_1_6) : Lemma92 := by
  intro G _ _ m p hS B M hB hM H hH hle
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hS.nontrivial hB
  have hBM := le_of_isPreUniquenessTwoLocal hS hB hM
  have hYH : pCoreOf 2 M ≤ H := le_sup_left.trans hle
  have hBH : B ≤ H := le_sup_right.trans hle
  have hYnorm : B ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    hBM.trans (le_normalizer_pCoreOf 2 M)
  have hYp : ¬ p ∣ Nat.card (pCoreOf 2 M) := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).exists_card_eq
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have hm4 := hS.four_le
  refine (le_iSup_inf_centralizer_hyperplane hB.1.1 hYnorm hYp).trans
    (iSup₂_le fun K hK => ?_)
  have hB' : Nat.card B = p ^ ((m - 1) + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
    exact hS.card_eq hB
  have hKcard := card_eq_of_index_eq hp hK.1 hK.2 hB'
  have hKel : IsElemAbelian p K := isElemAbelian_mono hB.1.1 hK.1
  obtain ⟨E, hEK, hEel, hEcard⟩ := exists_le_isElemAbelian_card hKel (n := 3)
    (by rw [hKcard]; exact pow_dvd_pow p (by omega))
  have hEB : E ≤ B := hEK.trans hK.1
  have h1 := i1 G hS.kProper p hp hp2 B hB.1 H hH hBH E hEB hEel hEcard
  have hrank : 2 ≤ pRank p E := by
    have := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEel hEcard
    omega
  have h2 := i2 G hS.kProper p 2 hp Nat.prime_two hp2 H hH E (hEB.trans hBH) hEel hrank
  refine le_trans (inf_le_inf_left _ (Subgroup.centralizer_le (by exact hEK))) ?_
  intro y hy
  have hyY : y ∈ pCoreOf 2 M := hy.1
  have hyE : ∀ e ∈ E, e ≠ 1 → y ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({e} : Set G)) := by
    intro e he he1
    have hyC : y ∈ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 he) hy.2
    have h3 := pCoreOf_inf_centralizer_le h91 hS hB hM (hEB he) he1 ⟨hyY, hyC⟩
    have h4 := pCoreOf_inf_le (r := 2) (Subgroup.centralizer ({e} : Set G)) H ⟨h3, hYH hyY⟩
    rwa [inf_comm] at h4
  have hmem1 : y ∈ ⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
      pCoreOf 2 (H ⊓ Subgroup.centralizer ({e} : Set G)) := by
    simp only [Subgroup.mem_iInf]
    exact fun e he he1 => hyE e he he1
  have hmem2 : y ∈ ⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({e} : Set G)) := by
    simp only [Subgroup.mem_iInf]
    exact fun e he he1 => pCoreOf_two_le_glaPPrimeCoreOf hp hp2 _ (hyE e he he1)
  exact h2 (Subgroup.mem_inf.2 ⟨hmem1, h1 hmem2⟩)

theorem lemma94_of_lemma91ii_lemma92 (h91 : Lemma91ii) (h92 : Lemma92) : Lemma94 := by
  intro G _ _ m p hS B M hB hM D hDB hD
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hS.simple
  have hBM := le_of_isPreUniquenessTwoLocal hS hB hM
  have hel := hB.1.1
  let Good : Subgroup G → Prop := fun T =>
    IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧ pCoreOf 2 M ≤ T ∧ T ≤ M
  have hstep : ∀ T, Good T → Good (gammaOne T) := by
    rintro T ⟨hTp, hBT, hOT, hTM⟩
    refine ⟨hTp.to_le (gammaOne_le T), hBT.trans (normalizer_le_normalizer_gammaOne T), ?_,
      (gammaOne_le T).trans hTM⟩
    intro x hx
    rw [mem_gammaOne]
    refine ⟨hOT hx, fun T₀ h0 hc => ?_⟩
    have hN : T ≤ Subgroup.normalizer (T₀ : Set G) := Subgroup.le_normalizer.trans hc.normalizer_le
    have hBN : B ≤ Subgroup.normalizer (T₀ : Set G) := hBT.trans hc.normalizer_le
    have hne := normalizer_ne_top_of_isPGroup_two hS.nonabelian h0 (hTp.to_le hc.1)
    exact h92 G m p hS B M hB hM _ hne (sup_le (hOT.trans hN) hBN) hx
  have hiter : ∀ T, Good T → ∀ n, Good (gammaIter T n) := by
    intro T hT n
    induction n with
    | zero => exact hT
    | succ n ih => exact hstep _ ih
  have hinf : ∀ T, Good T → Good (gammaInf T) := by
    intro T hT
    have hit := hiter T hT
    exact ⟨hT.1.to_le (gammaInf_le T), hT.2.1.trans (normalizer_le_normalizer_gammaInf T),
      le_iInf fun n => (hit (n + 1)).2.2.1, (gammaInf_le T).trans hT.2.2.2⟩
  have hBcD : B ≤ Subgroup.centralizer (D : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun d hd => elemAbelian_comm hel (hDB hd) hb
  have hSS : sigmaStar D ≤ M := iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 =>
    (pCoreOf_two_le_glaPPrimeCoreOf hp hp2 _).trans (lemma91_i hS hB hM (hDB hd))
  have hOp : ¬ p ∣ Nat.card (pCoreOf 2 M) := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).exists_card_eq
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have : Nontrivial D := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hD.2]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  have hOS : pCoreOf 2 M ≤ sigmaStar D := by
    refine (le_iSup_inf_centralizer_hyperplane hD.1
      ((hDB.trans hBM).trans (le_normalizer_pCoreOf 2 M)) hOp).trans
      (iSup₂_le fun K hK => ?_)
    have hKcard : Nat.card K = p ^ 1 := card_eq_of_index_eq hp hK.1 hK.2 (n := 1) hD.2
    obtain ⟨k, hkK, hk1⟩ : ∃ k ∈ K, k ≠ 1 := by
      rcases Subgroup.bot_or_exists_ne_one K with h | h
      · rw [h, Subgroup.card_bot, pow_one] at hKcard
        have := hp.one_lt
        omega
      · exact h
    have hle : pCoreOf 2 (Subgroup.centralizer ({k} : Set G)) ≤ sigmaStar D :=
      le_iSup_of_le k (le_iSup_of_le (hK.1 hkK) (le_iSup_of_le hk1 le_rfl))
    intro y hy
    have hyC : y ∈ Subgroup.centralizer ({k} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 hkK) hy.2
    exact hle (pCoreOf_inf_centralizer_le h91 hS hB hM (hDB (hK.1 hkK)) hk1 ⟨hy.1, hyC⟩)
  have hOSig : pCoreOf 2 M ≤ sigmaOf D :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOS
      (hSS.trans (le_normalizer_pCoreOf 2 M)) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hSig : Good (sigmaOf D) :=
    ⟨CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _,
      (hBcD.trans (Subgroup.centralizer_le_normalizer _)).trans
        (normalizer_le_normalizer_sigmaOf D),
      hOSig, (sigmaOf_le_sigmaStar D).trans hSS⟩
  exact ⟨(hinf _ hSig).2.2.1, (hinf _ hSig).2.2.2⟩

@[expose] def TheoremTwoBase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M →
      ∀ D : Subgroup G, IsPPlane p D → D ≤ B →
        IsPGroup 2 (gammaStar p D) ∧
          (∀ g : G, gammaStar p (GLBConj g D) = GLBConj g (gammaStar p D)) ∧
          (D ≤ M → IsTwoConnectedIn p M D B →
            pCoreOf 2 M ≤ gammaStar p D ∧ gammaStar p D ≤ M ∧
              ∀ T : Subgroup G, pCoreOf 2 M ≤ T → T ≤ gammaStar p D →
                Subgroup.normalizer (T : Set G) ≤ M)

theorem isTwoConnectedIn_of_plane_le (hS : GLStanding G m p) {B M D : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M) (hD : IsPPlane p D) (hDB : D ≤ B) :
    D ≤ M ∧ IsTwoConnectedIn p M D B := by
  have hp := hS.prime
  have : Fact p.Prime := ⟨hp⟩
  have hBM := le_of_isPreUniquenessTwoLocal hS hB hM
  have hm4 := hS.four_le
  have hBc : p ^ 2 ≤ Nat.card B := by
    rw [hS.card_eq hB]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  exact ⟨hDB.trans hBM, isTwoConnectedIn_of_le
    ⟨hDB.trans hBM, hD.1, not_isCyclic_of_isElemAbelian hD.1 (hD.2 ▸ le_rfl)⟩
    ⟨hBM, hB.1.1, not_isCyclic_of_isElemAbelian hB.1.1 hBc⟩ hDB⟩

theorem theoremTwoBase_of_prop98 (h : Prop98) : TheoremTwoBase := by
  intro G _ _ m p hS B M hB hM D hD hDB
  obtain ⟨-, h98⟩ := h G m p hS B M hB hM
  have hDeq : gammaStar p D = pCoreOf 2 M := h98 D hDB hD
  refine ⟨isPGroup_gammaStar p D, fun g => gammaStar_gLBConj p g D, fun _ _ => ?_⟩
  refine ⟨hDeq.symm.le, hDeq.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 M), ?_⟩
  intro T hT1 hT2
  have hTeq : T = pCoreOf 2 M := le_antisymm (hDeq ▸ hT2) hT1
  rw [hTeq]
  exact (normalizer_pCoreOf_eq_of_isMaxTwoLocal hM.1).le

end Setting

end CFSG.LocalAnalysis.GLTheoremB
