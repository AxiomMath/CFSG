module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.LinearCover
import CFSG.HardMathSupport.Solomon.Coordinator.I10_20
import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
import CFSG.Adapters.TauCetiLieModels
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcRed
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open Matrix CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover
open CFSG.HardMathSupport.Solomon.Coordinator (i1020_map_witness i1020_quotient_witness
  i1020_le_glaTwoLocalRank)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (exists_hom_of_cover scalars_le_center
  dvd_card_scalars)
open CFSG.RankThree.PerfectCover (hopfMultiplier hopfMultiplierEquivGriess)

private theorem witness_of_commute {G A : Type*} [Group G] [CommGroup A] {r k : ℕ}
    (hpow : ∀ a : A, a ^ r = 1) (hA : Nat.card A = r ^ k) (f : A →* G)
    (hf : Function.Injective f) {g : G} (hg : g ^ 2 = 1) (hg1 : g ≠ 1)
    (hc : ∀ a, Commute (f a) g) :
    ∃ S E : Subgroup G, IsPGroup 2 S ∧ S ≠ ⊥ ∧ E ≤ Subgroup.normalizer (S : Set G) ∧
      IsElemAbelian r E ∧ Nat.card E = r ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Subgroup.zpowers g, f.range, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hg hg1, pow_one])
  · intro h
    apply hg1
    have := Subgroup.mem_zpowers g
    rwa [h, Subgroup.mem_bot] at this
  · rintro _ ⟨a, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨i, rfl⟩
    exact ((hc a).zpow_right i).symm.eq
  · refine ⟨⟨⟨fun x y => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 x.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 y.2
      apply Subtype.ext
      change (x : G) * y = y * x
      rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hy
      rw [← map_pow, hpow, map_one]
  · rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

section Torus

variable {F : Type} [Field F]

private theorem neg_one_ne_one_of_card_pow [Finite F] {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hF : Nat.card F = ℓ ^ e) : (-1 : F) ≠ 1 := by
  have : Fintype F := Fintype.ofFinite F
  rw [Ne, neg_one_eq_one_iff, FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hF]
  have := Nat.odd_iff.1 ((hℓ.odd_of_ne_two hℓ2).pow (n := e))
  omega

private def sgnVec (n : ℕ) (F : Type) [Field F] : Fin n → Fˣ :=
  fun i => if i.val < 2 then -1 else 1

private theorem prod_sgnVec (m : ℕ) : ∏ i, sgnVec (m + 2) F i = 1 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [sgnVec, Fin.val_succ]

private theorem sgnVec_sq {n : ℕ} (i : Fin n) : sgnVec n F i ^ 2 = 1 := by
  unfold sgnVec
  split_ifs <;> simp

private theorem diagHom_sgnVec_ne_scalar (h2 : (-1 : F) ≠ 1) {m : ℕ} (hm : 1 ≤ m) (c : Fˣ) :
    diagHom (m + 2) (sgnVec (m + 2) F) ≠ Matrix.GeneralLinearGroup.scalar (Fin (m + 2)) c := by
  intro h
  have h0 := congrArg (fun g : GL (Fin (m + 2)) F => (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F)
    0 0) h
  have h1 := congrArg (fun g : GL (Fin (m + 2)) F => (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F)
    ⟨2, by omega⟩ ⟨2, by omega⟩) h
  simp [coe_diagHom, sgnVec, GeneralLinearGroup.coe_scalar] at h0 h1
  exact h2 (h0.trans h1.symm)

private theorem diagHom_mem_linUni [Finite F] {n ℓ f r : ℕ} {H : Subgroup (GL (Fin n) F)}
    (hH : (Nat.card F = ℓ ^ f ∧ H = StatedSL n F ∧ r ∣ ℓ ^ f - 1) ∨
      (Nat.card F = (ℓ ^ f) ^ 2 ∧ H = StatedSU n (ℓ ^ f) F ∧ r ∣ ℓ ^ f + 1))
    (hq : ℓ ^ f ≠ 0) {d : Fin n → Fˣ} (hd : ∏ i, d i = 1)
    (hdu : ∀ i, d i ^ (ℓ ^ f + 1) = 1) : diagHom n d ∈ H := by
  have hdet : ((diagHom n d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [det_diagHom, ← Units.coe_prod, hd, Units.val_one]
  rcases hH with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
  · exact Subgroup.subset_closure hdet
  · refine Subgroup.subset_closure ⟨hdet, ?_⟩
    rw [coe_diagHom, Matrix.diagonal_map (by simp [zero_pow hq]), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, hdu i, Units.val_one]

private theorem diagHom_sgnVec_mem [Finite F] {m ℓ f r : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    {H : Subgroup (GL (Fin (m + 2)) F)}
    (hH : (Nat.card F = ℓ ^ f ∧ H = StatedSL (m + 2) F ∧ r ∣ ℓ ^ f - 1) ∨
      (Nat.card F = (ℓ ^ f) ^ 2 ∧ H = StatedSU (m + 2) (ℓ ^ f) F ∧ r ∣ ℓ ^ f + 1)) :
    diagHom (m + 2) (sgnVec (m + 2) F) ∈ H := by
  refine diagHom_mem_linUni hH (pow_ne_zero _ hℓ.ne_zero) (prod_sgnVec m) fun i => ?_
  obtain ⟨j, hj⟩ := ((hℓ.odd_of_ne_two hℓ2).pow (n := f)).add_one
  rw [hj, ← two_mul, pow_mul, sgnVec_sq, one_pow]

private theorem exists_zeta_torus [Finite F] {n ℓ f r : ℕ} (hℓ : ℓ.Prime) [Fact r.Prime]
    [NeZero r] {H : Subgroup (GL (Fin n) F)}
    (hH : (Nat.card F = ℓ ^ f ∧ H = StatedSL n F ∧ r ∣ ℓ ^ f - 1) ∨
      (Nat.card F = (ℓ ^ f) ^ 2 ∧ H = StatedSU n (ℓ ^ f) F ∧ r ∣ ℓ ^ f + 1)) :
    ∃ ζ : Fˣ, orderOf ζ = r ∧ ∀ (hζ : ζ ^ r = 1) {m : ℕ}
      (v : (Fin m → ZMod r) →+ (Fin n → ZMod r)), (∀ u, ∑ i, v u i = 0) →
        ∀ u, torusWit ζ hζ v u ∈ H := by
  rcases hH with ⟨hK, rfl, hrq⟩ | ⟨hK, rfl, hrq⟩
  · obtain ⟨ζ, hζ⟩ := exists_zeta (K := F) (r := r) (by rw [hK]; exact hrq)
    exact ⟨ζ, hζ, fun hζ' m v hv u => torusWit_mem_SL hζ' v hv u⟩
  · have hq : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
    obtain ⟨ζ, hζ⟩ := exists_zeta (K := F) (r := r)
      (by rw [hK, sq_sub_one_eq hq]; exact Dvd.dvd.mul_right hrq _)
    have hζu : ζ ^ (ℓ ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hrq)
    exact ⟨ζ, hζ, fun hζ' m v hv u => torusWit_mem_SU (by positivity) hζ' hζu v hv u⟩

private theorem witness_statedProj [Finite F] {m ℓ f r : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    [hr : Fact r.Prime] (hm : 1 ≤ m) {H : Subgroup (GL (Fin (m + 2)) F)}
    (hH : (Nat.card F = ℓ ^ f ∧ H = StatedSL (m + 2) F ∧ r ∣ ℓ ^ f - 1) ∨
      (Nat.card F = (ℓ ^ f) ^ 2 ∧ H = StatedSU (m + 2) (ℓ ^ f) F ∧ r ∣ ℓ ^ f + 1)) :
    ∃ S E : Subgroup (StatedProj H), IsPGroup 2 S ∧ S ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (S : Set (StatedProj H)) ∧ IsElemAbelian r E ∧
        Nat.card E = r ^ m := by
  have : NeZero r := ⟨hr.out.ne_zero⟩
  obtain ⟨ζ, hζr, hmemH⟩ := exists_zeta_torus hℓ hH
  have hζ : ζ ^ r = 1 := by rw [← hζr]; exact pow_orderOf_eq_one ζ
  have h2 : (-1 : F) ≠ 1 := by
    rcases hH with ⟨hK, -, -⟩ | ⟨hK, -, -⟩
    · exact neg_one_ne_one_of_card_pow hℓ hℓ2 hK
    · exact neg_one_ne_one_of_card_pow hℓ hℓ2 (e := f * 2) (by rw [hK, ← pow_mul])
  set D := (StatedScalars (Fin (m + 2)) F).subgroupOf H
  let ψ : Multiplicative (Fin m → ZMod r) →* H :=
    (torusWit ζ hζ (sumZeroHom m)).codRestrict H (hmemH hζ _ sum_sumZeroVec)
  let φ : Multiplicative (Fin m → ZMod r) →* StatedProj H := (QuotientGroup.mk' D).comp ψ
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hu
    obtain ⟨c, hc⟩ := hu
    refine Subgroup.mem_bot.2 (eq_one_of_torusWit_scalar hζ hζr (sumZeroHom m)
      (Fin.castSucc (Fin.last m)) (fun u => ?_) (fun u hu0 => ?_) u hc.symm)
    · simp [sumZeroHom, sumZeroVec]
    · funext i
      have := hu0 (Fin.castSucc (Fin.castSucc i))
      simpa [sumZeroHom, sumZeroVec] using this
  have hs := diagHom_sgnVec_mem hℓ hℓ2 hH
  let t : H := ⟨_, hs⟩
  refine witness_of_commute multiplicative_zmod_pow_eq_one (card_multiplicative_zmod m) φ hφ
    (g := QuotientGroup.mk' D t) ?_ ?_ fun u => ?_
  · rw [← map_pow]
    have : t ^ 2 = 1 := Subtype.ext (by
      change diagHom (m + 2) (sgnVec (m + 2) F) ^ 2 = 1
      rw [← map_pow, show sgnVec (m + 2) F ^ 2 = 1 from funext fun i => sgnVec_sq i, map_one])
    rw [this, map_one]
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨c, hc⟩ := h
    exact diagHom_sgnVec_ne_scalar h2 hm c hc.symm
  · have hcomm : Commute (ψ u) t := Subtype.ext (by
      change torusWit ζ hζ (sumZeroHom m) u * diagHom (m + 2) (sgnVec (m + 2) F) =
        diagHom (m + 2) (sgnVec (m + 2) F) * torusWit ζ hζ (sumZeroHom m) u
      rw [torusWit_apply, ← map_mul, ← map_mul, mul_comm])
    exact hcomm.map (QuotientGroup.mk' D)

private theorem witness_linUni [Finite F] {m ℓ f r : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    [hr : Fact r.Prime] (hm : 1 ≤ m) {H : Subgroup (GL (Fin (m + 2)) F)}
    (hH : (Nat.card F = ℓ ^ f ∧ H = StatedSL (m + 2) F ∧ r ∣ ℓ ^ f - 1) ∨
      (Nat.card F = (ℓ ^ f) ^ 2 ∧ H = StatedSU (m + 2) (ℓ ^ f) F ∧ r ∣ ℓ ^ f + 1)) :
    ∃ S E : Subgroup H, IsPGroup 2 S ∧ S ≠ ⊥ ∧ E ≤ Subgroup.normalizer (S : Set H) ∧
      IsElemAbelian r E ∧ Nat.card E = r ^ (m + 1) := by
  have : NeZero r := ⟨hr.out.ne_zero⟩
  obtain ⟨ζ, hζr, hmemH⟩ := exists_zeta_torus hℓ hH
  have hζ : ζ ^ r = 1 := by rw [← hζr]; exact pow_orderOf_eq_one ζ
  have h2 : (-1 : F) ≠ 1 := by
    rcases hH with ⟨hK, -, -⟩ | ⟨hK, -, -⟩
    · exact neg_one_ne_one_of_card_pow hℓ hℓ2 hK
    · exact neg_one_ne_one_of_card_pow hℓ hℓ2 (e := f * 2) (by rw [hK, ← pow_mul])
  let ψ : Multiplicative (Fin (m + 1) → ZMod r) →* H :=
    (torusWit ζ hζ (sumZeroHom' (m + 1))).codRestrict H (hmemH hζ _ sum_sumZeroVec')
  have hψ : Function.Injective ψ := fun a b hab =>
    torusWit_injective hζ hζr _ (fun u hu0 => by
      funext i
      have := hu0 (Fin.castSucc i)
      simpa [sumZeroHom', sumZeroVec'] using this) (congrArg Subtype.val hab)
  have hs := diagHom_sgnVec_mem hℓ hℓ2 hH
  let t : H := ⟨_, hs⟩
  refine witness_of_commute multiplicative_zmod_pow_eq_one (card_multiplicative_zmod (m + 1)) ψ
    hψ (g := t) ?_ ?_ fun u => ?_
  · exact Subtype.ext (by
      change diagHom (m + 2) (sgnVec (m + 2) F) ^ 2 = 1
      rw [← map_pow, show sgnVec (m + 2) F ^ 2 = 1 from funext fun i => sgnVec_sq i, map_one])
  · intro h
    have h' : diagHom (m + 2) (sgnVec (m + 2) F) =
        Matrix.GeneralLinearGroup.scalar (Fin (m + 2)) 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    exact diagHom_sgnVec_ne_scalar h2 hm 1 h'
  · exact Subtype.ext (by
      change torusWit ζ hζ (sumZeroHom' (m + 1)) u * diagHom (m + 2) (sgnVec (m + 2) F) =
        diagHom (m + 2) (sgnVec (m + 2) F) * torusWit ζ hζ (sumZeroHom' (m + 1)) u
      rw [torusWit_apply, ← map_mul, ← map_mul, mul_comm])

end Torus

private theorem lpEps_core {p n ℓ f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : n = p)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {F : Type} [Field F] [Finite F] {H : Subgroup (GL (Fin n) F)}
    (hH : (Nat.card F = ℓ ^ f ∧ H = StatedSL n F ∧ p ∣ ℓ ^ f - 1) ∨
      (Nat.card F = (ℓ ^ f) ^ 2 ∧ H = StatedSU n (ℓ ^ f) F ∧ p ∣ ℓ ^ f + 1))
    (hperf : Group.IsPerfect H) (hM : Nat.card (griessHopfMultiplier (StatedProj H)) = p)
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (θ : K ⧸ Subgroup.center K ≃* StatedProj H) :
    (p - 2) + CFSG.Open.pRank p (⊤ : Subgroup (Subgroup.center K)) ≤ GLATwoLocalRank p K := by
  subst hn
  have hn2 := hp.two_le
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (by omega : m + 2 = 2) hp2
    · exact h
  haveI : Fact (m + 2).Prime := ⟨hp⟩
  rw [show m + 2 - 2 = m by omega]
  by_cases hZ : m + 2 ∣ Nat.card (Subgroup.center K)
  ·
    have hZc : Nat.card (Subgroup.center K) = m + 2 := by
      have h := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier ⟨hK.1⟩ θ
      rw [hM] at h
      exact Nat.dvd_antisymm h hZ
    have h1 : CFSG.Open.pRank (m + 2) (⊤ : Subgroup (Subgroup.center K)) ≤ 1 := by
      refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ _ => ?_
      rw [pow_one, ← hZc]
      exact Subgroup.card_le_card_group E
    have hHK : (Nat.card F = ℓ ^ f ∧ H = StatedSL (m + 2) F) ∨
        (Nat.card F = (ℓ ^ f) ^ 2 ∧ H = StatedSU (m + 2) (ℓ ^ f) F) := by
      rcases hH with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    set D := (StatedScalars (Fin (m + 2)) F).subgroupOf H
    have hDc : Nat.card D = m + 2 := by
      refine Nat.dvd_antisymm (card_scalars_dvd (by omega) H fun x c hc => ?_) ?_
      · have hdet := det_eq_one_of_linUni hHK (x : H).2
        rw [hc] at hdet
        simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
        exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
      · refine dvd_card_scalars (q := ℓ ^ f) (by omega) (Nat.one_le_pow _ _ hℓ.pos) ?_
        rcases hH with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exact Or.inl ⟨h1, h2, dvd_rfl, h3⟩
        · exact Or.inr ⟨h1, h2, dvd_rfl, h3⟩
    have hMfin : Finite (griessHopfMultiplier (StatedProj H)) :=
      Nat.finite_of_card_ne_zero (by rw [hM]; omega)
    have : Finite (hopfMultiplier (StatedProj H)) :=
      Finite.of_equiv _ (hopfMultiplierEquivGriess (StatedProj H)).toEquiv
    have hMp : (Nat.card (hopfMultiplier (StatedProj H))).factorization (m + 2) ≤
        (Nat.card (QuotientGroup.mk' D).ker).factorization (m + 2) := by
      rw [← Nat.card_congr (hopfMultiplierEquivGriess (StatedProj H)).toEquiv, hM,
        QuotientGroup.ker_mk', hDc]
    obtain ⟨φ, hφs, -⟩ := exists_hom_of_cover hperf ⟨hK.1⟩ (QuotientGroup.mk' D)
      (QuotientGroup.mk'_surjective D) (by rw [QuotientGroup.ker_mk']; exact scalars_le_center H)
      (CFSG.GH74.Generic.centralQuotientMap θ)
      (CFSG.GH74.Generic.centralQuotientMap_surjective θ)
      (CFSG.GH74.Generic.centralQuotientMap_ker θ).le hp
      (by
        rw [CFSG.GH74.Generic.centralQuotientMap_ker θ]
        exact IsPGroup.of_card (n := 1) (by rw [hZc, pow_one]))
      hMp
    have hcard : Nat.card H = Nat.card K := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup D, hDc,
        Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), hZc,
        Nat.card_congr θ.toEquiv]
    have hφi : Function.Injective φ :=
      ((Nat.bijective_iff_surjective_and_card φ).2 ⟨hφs, hcard⟩).1
    obtain ⟨S, E, hS, hSne, hES, hE, hEc⟩ := witness_linUni hℓ hℓ2 hm hH
    obtain ⟨hS', hSne', hES', hE', hEc'⟩ := i1020_map_witness φ hφi hS hES hE hEc
    have := i1020_le_glaTwoLocalRank hp hS' (hSne' hSne) hES' hE' hEc'
    omega
  ·
    have h0 : CFSG.Open.pRank (m + 2) (⊤ : Subgroup (Subgroup.center K)) = 0 := by
      obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
        (⊤ : Subgroup (Subgroup.center K))
      by_contra hne
      exact hZ ((dvd_pow_self (m + 2) hne).trans (hE ▸ Subgroup.card_subgroup_dvd_card E))
    obtain ⟨S, E, hS, hSne, hES, hE, hEc⟩ := witness_statedProj hℓ hℓ2 hm hH
    obtain ⟨hS', hSne', hES', hE', hEc'⟩ :=
      i1020_map_witness θ.symm.toMonoidHom θ.symm.injective hS hES hE hEc
    obtain ⟨S₁, hS₁, hS₁ne, E₁, hE₁S, hE₁, hE₁c⟩ := i1020_quotient_witness hp
      (Subgroup.center K) hZ True ⟨_, hS', fun _ => hSne' hSne, _, hES', hE', hEc'⟩
    have := i1020_le_glaTwoLocalRank hp hS₁ (hS₁ne trivial) hE₁S hE₁ hE₁c
    omega

theorem genLpEpsLocal_holds :
    GenLpEpsLocal := by
  intro p hp hp2 K _ _ hK e he hchar hiso
  obtain ⟨ι⟩ := hiso
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : ¬ Even (p - 1 + 1) := by
    rw [show p - 1 + 1 = p by omega, Nat.not_even_iff_odd]
    exact hp.odd_of_ne_two hp2
  obtain ⟨idx, hv⟩ := e
  obtain ⟨Q, ⟨rfl, hQ⟩ | ⟨rfl, hQ⟩⟩ := he
  ·
    have hc : Q.p ≠ 2 := by simpa using hchar
    have hQ' : p ∣ Q.p ^ Q.exponent - 1 := by rwa [← TauCeti.PrimePower.card_def]
    obtain ⟨-, hcl | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_A (p - 1) Q hv ι
    swap
    · omega
    obtain ⟨-, F, _, _, hF, ⟨θ⟩⟩ := hcl
    have : Fintype F := Fintype.ofFinite F
    have hF' : Fintype.card F = Q.p ^ Q.exponent := by rw [Fintype.card_eq_nat_card, hF]
    have hq3 : 3 ≤ Q.p ^ Q.exponent := by
      have h1 : Q.p ≤ Q.p ^ Q.exponent := Nat.le_self_pow Q.exponent_pos.ne' _
      have := Q.prime_p.two_le
      omega
    have hq4 : Q.p ^ Q.exponent ≠ 4 := by
      have := Nat.odd_iff.1 ((Q.prime_p.odd_of_ne_two hc).pow (n := Q.exponent))
      omega
    refine lpEps_core hp hp2 (n := p - 1 + 1) (by omega) Q.prime_p hc (Or.inl ⟨hF, rfl, hQ'⟩)
      ?_ ?_ hK θ
    · have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F)
        (n := p - 1 + 1) (by omega)
      exact Group.IsPerfect.ofSurjective
        (f := (specialLinearGroupEquivStatedSL (p - 1 + 1) F).toMonoidHom)
        (specialLinearGroupEquivStatedSL _ F).surjective
    · obtain ⟨-, ⟨eM⟩⟩ :=
        CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_three_le (k := F)
          (n := p - 1 + 1) (by omega) (by omega) (by omega)
      rw [← Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr
        (projectiveSpecialLinearGroupEquivStatedProj (p - 1 + 1) F)).toEquiv,
        Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hF',
        show p - 1 + 1 = p by omega]
      exact Nat.gcd_eq_left hQ'
  ·
    have hc : Q.p ≠ 2 := by simpa using hchar
    have hQ' : p ∣ Q.p ^ Q.exponent + 1 := by rwa [← TauCeti.PrimePower.card_def]
    obtain ⟨-, F, _, _, hF, ⟨θ⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA (p - 1) Q hv ι
    haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have : Fintype F := Fintype.ofFinite F
    haveI : CharP F Q.p := charP_of_card_eq_prime_pow (f := 2 * Q.exponent) (by
      rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
    have hq : (p - 1 + 1, Q.p ^ Q.exponent) ≠ (3, 2) := by
      intro h
      have h2 : Q.p ^ Q.exponent = 2 := congrArg Prod.snd h
      have := Nat.odd_iff.1 ((Q.prime_p.odd_of_ne_two hc).pow (n := Q.exponent))
      omega
    refine lpEps_core hp hp2 (n := p - 1 + 1) (by omega) Q.prime_p hc (Or.inr ⟨hF, rfl, hQ'⟩)
      ?_ ?_ hK θ
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.isPerfect_statedSU_odd hF (by omega) hq
    · obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier hF
        Q.exponent_pos (by omega) hodd hq
      rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
        show p - 1 + 1 = p by omega]
      exact Nat.gcd_eq_left hQ'

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen

end
