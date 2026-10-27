module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndOverBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38Core
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndConfig
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12OverOdd

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M12

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.Endgame CFSG.ComponentClassification.M12Cover
open CFSG.ComponentClassification.AschbacherTheorem3 CFSG.ComponentClassification.Asc76
open CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem exc_of_tightM {W : Type*} [Group W] [Finite W]
    {X : Subgroup W} {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    {Exc : Subgroup W → Prop} (hc : YCensus X Exc) {Q : Subgroup (normalizer (A : Set G))}
    (hQ : TightlyEmbedded Q) {U : Subgroup G} (hUM : U ≤ normalizer (A : Set G))
    (hU : IsSylowOf 2 (U.subgroupOf (normalizer (A : Set G))) Q) (hUab : ∀ x ∈ U, x ^ 2 = 1)
    (hU4 : 4 ≤ Nat.card U) (hUK : U ⊓ centralizer (A : Set G) = ⊥) :
    Exc ((U.subgroupOf (normalizer (A : Set G))).map ψ) := by
  set Qg : Subgroup G := Q.map (normalizer (A : Set G)).subtype with hQg
  have hQgM : Qg ≤ normalizer (A : Set G) := map_subtype_le Q
  have hQgQ : Qg.subgroupOf (normalizer (A : Set G)) = Q :=
    comap_map_eq_self_of_injective (normalizer (A : Set G)).subtype_injective Q
  have hsyl : IsSylowOf 2 U (Qg ⊓ normalizer (A : Set G)) := by
    rw [inf_eq_left.mpr hQgM, ← Asc76.Sec5.isSylowOf_subgroupOf_iff hUM hQgM, hQgQ]
    exact hU
  have hQ' : ∀ u ∈ U, u ≠ 1 → ∀ c ∈ A, c * u = u * c → c ∈ normalizer (Qg : Set G) := by
    intro u hu hu1 c hcA hcu
    have huQ : (⟨u, hUM hu⟩ : normalizer (A : Set G)) ∈ Q := hU.le hu
    have h1 : (⟨c, le_normalizer hcA⟩ : normalizer (A : Set G)) ∈
        normalizer (Q : Set (normalizer (A : Set G))) :=
      mem_normalizer_of_commute_of_tightlyEmbedded hQ huQ
        (fun h => hu1 (congrArg Subtype.val h)) (Subtype.ext (by simpa using hUab u hu))
        (Subtype.ext hcu)
    exact (Asc76.Sec5.mem_normalizer_map_subtype_iff Q _).mp h1
  by_contra hExc
  refine not_yWitness_map hψ hsyl hUab hQ' (hc _ ?_ ?_ hExc)
  · refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
      apply Subtype.ext
      simp only [coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact commute_of_sq_eq_one hUab hx hy
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hUab _ hx)
      rw [this, map_one]
  · rw [card_map_eq_of_inf_centralizer hψ hUK, Nat.card_congr (subgroupOfEquivOfLe hUM).toEquiv]
    exact hU4

theorem m12_isSylowOf_overlap
    {S : Array (Array ℕ)} {Wd : Array (List ℤ)} {sG roots : Array ℕ}
    {nodes : Array CFSG.KC.Census.NodeP} {cS : CFSG.KC.Census.ArrCertP}
    {wcs : Array (Array CFSG.KC.Census.ArrCertP)} {excs : List CFSG.KC.Census.ExcRefP}
    (hc : m12CheckW S Wd m12E0 sG roots nodes cS wcs excs = true)
    (hE : m12EndCheck S m12E0 m12EndA0 m12EndLeaves m12EndL m12EndSigma m12EndC0 m12EndZ = true)
    (hO : m12OverFacts S)
    (h22 : Asc76Lemma22) (h75 : AS76b.Asc75Theorem4) (hA : standardComponentIsStandard A)
    (hm : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (e : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Carrier .M12)
    {R : Subgroup G} (hRd : ¬ IsDihedralTwoGroup R) {g : G} {T : Subgroup G}
    (hov : Asc76.Sec5.Overlap A R g T) :
    IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  set K := centralizer (A : Set G) with hKdef
  have hc' := hc
  simp only [m12CheckW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨hk, hch⟩, -⟩, -⟩, -⟩ := hc'
  have hF := m12EndFacts_of_check hk hch hE
  have hCE := (m12_centralizer_facts hk hch hE).1
  obtain ⟨hOodd, hOcent, hOh⟩ := hO
  have hE' := hE
  simp only [m12EndCheck, m12EndE0OK, Bool.and_eq_true, beq_iff_eq] at hE'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsz, hcE⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE'
  have hv : ∀ k < m12E0.size, validA 24 m12E0[k]! = true := fun k hk' =>
    enumOK_gens_valid hcE hk'
  have hv0 : validA 24 m12E0[0]! = true := hv 0 (by rw [hsz]; norm_num)
  have hv1 : validA 24 m12E0[1]! = true := hv 1 (by rw [hsz]; norm_num)
  set E₀ := closure (permsA 24 m12E0) with hE₀
  set t₀ := permOfArr 24 (m12T0 m12E0) with ht₀
  have hrt : Rep 24 (m12T0 m12E0) t₀ := by
    have h1 := rep_compA (rep_of_validA hv0) (rep_of_validA hv1)
    have h2 := permOfArr_eq_of_rep h1
    rw [← h2] at h1
    exact h1
  have hb₀E : permOfArr 24 m12E0[0]! ∈ E₀ := subset_closure ⟨0, by rw [hsz]; norm_num, rfl⟩
  have hnormD : autModel ≤ normalizer (blockGroup : Set (Equiv.Perm (Fin 24))) :=
    (normal_subgroupOf_iff_le_normalizer blockGroup_le_autModel).1 m12_normal
  have hconjD : ∀ {v y : Equiv.Perm (Fin 24)}, v ∈ autModel → y ∈ blockGroup →
      v * y * v⁻¹ ∈ blockGroup := fun hv' hy => (mem_normalizer_iff.mp (hnormD hv') _).mp hy
  have hTc := hov.isMulCommutative h22 hm hnot
  have hU4 := hov.four_le_card_omegaOne h22 hm hRd hnot
  have hT1 := hov.ne_bot
  have hTM : T ≤ normalizer (A : Set G) := hov.sylow.le.trans inf_le_right
  have hTKg : T ≤ rightConjugate K g := hov.sylow.le.trans inf_le_left
  have hKg : TightlyEmbedded (rightConjugate K g) :=
    AS76b.tightlyEmbedded_rightConjugate (AS76b.tightlyEmbedded_centralizer hA) g
  have hPeven : Even (Nat.card (rightConjugate K g ⊓ normalizer (A : Set G) : Subgroup G)) :=
    even_iff_two_dvd.mpr ((Asc76.Sec5.even_card_of_isPGroup hov.sylow.isPGroup hT1).two_dvd.trans
      (card_dvd_of_le hov.sylow.le))
  have hP' : TightlyEmbedded ((rightConjugate K g ⊓ normalizer (A : Set G)).subgroupOf
      (normalizer (A : Set G))) :=
    AS76b.tightlyEmbedded_inf_subgroupOf_of_tightlyEmbedded hKg hPeven
  have hT' : IsSylowOf 2 (T.subgroupOf (normalizer (A : Set G)))
      ((rightConjugate K g ⊓ normalizer (A : Set G)).subgroupOf (normalizer (A : Set G))) :=
    (Asc76.Sec5.isSylowOf_subgroupOf_iff hTM inf_le_right).mpr hov.sylow
  have hTc' := Asc76.Sec5.isMulCommutative_subgroupOf (normalizer (A : Set G)) hTc
  have hT1' : T.subgroupOf (normalizer (A : Set G)) ≠ ⊥ := by
    intro h
    apply hT1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hTM hx⟩ : normalizer (A : Set G)) ∈ T.subgroupOf (normalizer (A : Set G)) := hx
    rw [h, mem_bot] at this
    exact mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨Q', -, hUQ', hnil', hQTE'⟩ := Asc76.Sec5.exists_twoNilpotent_tightlyEmbedded h75 hP' hT'
    hTc' hT1' (Asc76.Sec5.not_normalIn_twoPrimeLayerIn hA hov.not_mem)
  rw [Asc76.Sec5.omegaOne_subgroupOf _ hTc] at hUQ'
  obtain ⟨ψ, hψ⟩ := exists_isActionHom m12AutModel hA.1.1 e
  have hcen := m12_yCensusExc hc
  have hUT : omegaOne T ≤ T := omegaOne_le T
  have hUM : omegaOne T ≤ normalizer (A : Set G) := hUT.trans hTM
  have hUab : ∀ x ∈ omegaOne T, x ^ 2 = 1 := fun x hx => ((mem_omegaOne_iff hTc).mp hx).2
  have hTK : T ⊓ K = ⊥ := inf_centralizer_eq_bot' hA hov.not_mem hov.sylow.isPGroup hTKg
  have hUK : omegaOne T ⊓ K = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right K hUT).trans hTK.le)
  obtain ⟨w, hwR, hw⟩ := exc_of_tightM hψ hcen hQTE' hUM hUQ' hUab hU4 hUK
  have hTab : ∀ s ∈ T, s ^ 2 = 1 := by
    intro s hs
    set sN : normalizer (A : Set G) := ⟨s, hTM hs⟩ with hsN
    have hmem : w⁻¹ * ((ψ sN : ↥autModel) : Equiv.Perm (Fin 24)) * w ∈
        autModel ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24))) := by
      refine mem_inf.mpr ⟨autModel.mul_mem (autModel.mul_mem (autModel.inv_mem hwR) (ψ sN).2)
        hwR, mem_centralizer_iff.mpr fun f hf => ?_⟩
      obtain ⟨u, huU, huψ⟩ := exists_of_excClass hw hf
      have hsu0 : s * (u : G) = u * s :=
        congrArg Subtype.val (hTc.is_comm.comm ⟨s, hs⟩ ⟨u, hUT huU⟩)
      have hsu : sN * u = u * sN := Subtype.ext hsu0
      have h1 := congrArg (fun m => ((ψ m : ↥autModel) : Equiv.Perm (Fin 24))) hsu
      simp only [map_mul, Subgroup.coe_mul] at h1
      rw [huψ] at h1
      calc f * (w⁻¹ * ((ψ sN : ↥autModel) : Equiv.Perm (Fin 24)) * w)
          = w⁻¹ * ((w * f * w⁻¹) * ((ψ sN : ↥autModel) : Equiv.Perm (Fin 24))) * w := by group
        _ = w⁻¹ * (((ψ sN : ↥autModel) : Equiv.Perm (Fin 24)) * (w * f * w⁻¹)) * w := by
            rw [h1]
        _ = w⁻¹ * ((ψ sN : ↥autModel) : Equiv.Perm (Fin 24)) * w * f := by group
    have hcp : ∀ (y : Equiv.Perm (Fin 24)) (n : ℕ), (w⁻¹ * y * w) ^ n = w⁻¹ * y ^ n * w :=
      fun y n => by simpa using (conj_pow : (w⁻¹ * y * w⁻¹⁻¹) ^ n = w⁻¹ * y ^ n * w⁻¹⁻¹)
    obtain ⟨j, hj⟩ := (hov.sylow.isPGroup) ⟨s, hs⟩
    have hj' : s ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hsj : sN ^ 2 ^ j = 1 := Subtype.ext (by simpa [hsN] using hj')
    have h2 := sq_eq_one_of_two_element
      (fun x hx hx4 => m12_cent_check_spec hk hch hv hCE hOcent hx hx4) hmem j (by
        rw [hcp, ← Subgroup.coe_pow, ← map_pow, hsj, map_one, OneMemClass.coe_one, mul_one,
          inv_mul_cancel])
    have h3 : ψ (sN ^ 2) = 1 := by
      apply Subtype.ext
      rw [map_pow, Subgroup.coe_pow, OneMemClass.coe_one]
      rw [hcp] at h2
      have := congrArg (fun x => w * x * w⁻¹) h2
      simpa [mul_assoc] using this
    have h4 : s ^ 2 ∈ T ⊓ K := ⟨pow_mem hs 2, by simpa [hsN] using (hψ.eq_one_iff _).mp h3⟩
    rw [hTK, mem_bot] at h4
    exact h4
  have hUTeq : omegaOne T = T := le_antisymm hUT (le_omegaOne hTab)
  rw [hUTeq] at hw hU4 hUQ'
  obtain ⟨t, htT, htψ⟩ := exists_of_excClass hw hF.mem
  have ht2 : (t : G) ^ 2 = 1 := hTab _ htT
  have ht₀1 : t₀ ≠ 1 := by
    intro h1
    obtain ⟨a₀, -, -, hnot₀, -⟩ := hF.exists_conj
    apply hnot₀
    rw [h1, mul_one, inv_mul_cancel]
    exact one_mem _
  have htD : ((ψ t : ↥autModel) : Equiv.Perm (Fin 24)) ∈ blockGroup := by
    rw [htψ]
    exact hconjD hwR hF.mem_P
  have hfpf : ∀ p, ((ψ t : ↥autModel) : Equiv.Perm (Fin 24)) p ≠ p := by
    rw [htψ]
    exact hF.Q_conj w hwR _ (hF.Q_of_mem _ hF.mem ht₀1)
  have ht1 : (t : G) ≠ 1 := by
    intro h1
    have h2 : t = 1 := Subtype.ext h1
    have := hfpf 0
    rw [h2, map_one] at this
    exact this rfl
  obtain ⟨a', ha', ha'e⟩ := hψ.exists_eq (ψ t) htD
  have htAK : (t : G) ∈ A ⊔ K := by
    have hk' : a'⁻¹ * (t : G) ∈ K := by
      have h1 : ψ ((⟨a', le_normalizer ha'⟩ : normalizer (A : Set G))⁻¹ * t) = 1 := by
        rw [map_mul, map_inv, ha'e, inv_mul_cancel]
      simpa using (hψ.eq_one_iff _).mp h1
    have e1 : (t : G) = a' * (a'⁻¹ * t) := by group
    rw [e1]
    exact mul_mem (mem_sup_left ha') (mem_sup_right hk')
  obtain ⟨a, ha, r, hr, htar⟩ := Asc76.Sec5.exists_mul_of_mem_sup_centralizer hov.sylowR htAK
    (hov.normalizesR htT) (m := 1) (by rw [pow_one]; exact ht2)
  have hrK : r ∈ K := hov.sylowR.le hr
  have har : a * r = r * a := mem_centralizer_iff.mp hrK a ha
  have hrT : r ∈ R ⊓ centralizer ({(t : G)} : Set G) := by
    refine mem_inf.mpr ⟨hr, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [htar]
    calc r * (a * r) = (r * a) * r := by group
      _ = (a * r) * r := by rw [har]
  rw [Asc76.Sec5.inf_centralizer_singleton_eq hov.tight hov.not_mem_K hov.sylowK hov.sylowR
    hov.normalizesR htT ht1] at hrT
  have hr2 : r ^ 2 = 1 := by
    obtain ⟨φ⟩ := hov.mulEquiv
    have h1 := hTab _ (φ ⟨r, hrT⟩).2
    have h2 : (φ ⟨r, hrT⟩) ^ 2 = 1 := Subtype.ext (by simpa using h1)
    rw [← map_pow, MulEquiv.map_eq_one_iff] at h2
    simpa using congrArg Subtype.val h2
  have hat : ψ ⟨a, le_normalizer ha⟩ = ψ t := by
    have h1 : ψ ((⟨a, le_normalizer ha⟩ : normalizer (A : Set G))⁻¹ * t) = 1 := by
      rw [hψ.eq_one_iff]
      change a⁻¹ * (t : G) ∈ K
      rw [htar, inv_mul_cancel_left]
      exact hrK
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have hc2 : (a⁻¹ * t) ^ 2 = 1 := by
    rw [htar, inv_mul_cancel_left]
    exact hr2
  have hZ := m12_odd_card_center hA e hψ ht2 hfpf ha hat hc2
  obtain ⟨N', hNQ, hNn, hNodd, kN, hkN⟩ := hnil'
  have htQ : (t : normalizer (A : Set G)) ∈ Q' := hUQ'.le (show (t : G) ∈ T from htT)
  have hnormQ : ∀ {h : G} (hhA : h ∈ A), h * t = t * h →
      (⟨h, le_normalizer hhA⟩ : normalizer (A : Set G)) ∈
        normalizer (Q' : Set (normalizer (A : Set G))) := by
    intro h hhA hht
    exact mem_normalizer_of_commute_of_tightlyEmbedded hQTE' htQ
      (fun h1 => ht1 (congrArg Subtype.val h1)) (Subtype.ext (by simpa using ht2))
      (Subtype.ext hht)
  have hN1 : ∀ n ∈ N', ψ n = 1 := by
    intro n hn
    by_contra hn1
    have hoddn : Odd (orderOf n) := hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N' hn)
    have hoddy : Odd (orderOf (ψ n)) := hoddn.of_dvd_nat (orderOf_map_dvd ψ n)
    have hyD : ((ψ n : ↥autModel) : Equiv.Perm (Fin 24)) ∈ blockGroup :=
      mem_blockGroup_of_odd (ψ n).2 (by rwa [Subgroup.orderOf_coe])
    set y' := w⁻¹ * ((ψ n : ↥autModel) : Equiv.Perm (Fin 24)) * w with hy'
    have hy'D : y' ∈ blockGroup := by
      have := hconjD (autModel.inv_mem hwR) hyD
      rwa [inv_inv] at this
    have hy'1 : y' ≠ 1 := by
      intro h1
      apply hn1
      apply Subtype.ext
      have := congrArg (fun x => w * x * w⁻¹) h1
      simpa [hy', mul_assoc] using this
    have hy'15 : y' ^ 1485 = 1 := by
      rw [hy', show w⁻¹ * ((ψ n : ↥autModel) : Equiv.Perm (Fin 24)) * w =
        w⁻¹ * ((ψ n : ↥autModel) : Equiv.Perm (Fin 24)) * w⁻¹⁻¹ by rw [inv_inv], conj_pow,
        ← Subgroup.coe_pow, pow_1485_eq_one hoddy]
      simp
    obtain ⟨c, hcD, hct, hc15⟩ := hOodd y' hy'D hy'1 hy'15
    change c * t₀ = t₀ * c at hct
    have hxD : w * c * w⁻¹ ∈ blockGroup := hconjD hwR hcD
    obtain ⟨h, hhA, hhψ, hht⟩ := exists_lift_commute hψ hZ ht2
      (x := ⟨w * c * w⁻¹, blockGroup_le_autModel hxD⟩) hxD (by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [htψ]
        calc w * c * w⁻¹ * (w * t₀ * w⁻¹) = w * (c * t₀) * w⁻¹ := by group
          _ = w * (t₀ * c) * w⁻¹ := by rw [hct]
          _ = w * t₀ * w⁻¹ * (w * c * w⁻¹) := by group)
    set hN : normalizer (A : Set G) := ⟨h, le_normalizer hhA⟩ with hhN
    have hhQ := hnormQ hhA hht
    have hconjN : hN * n * hN⁻¹ ∈ N' := by
      refine mem_of_odd_orderOf hNn hkN ?_ (by
        rw [show hN * n * hN⁻¹ = MulAut.conj hN n from rfl, MulEquiv.orderOf_eq]
        exact hoddn)
      exact (mem_normalizer_iff.mp hhQ n).mp (hNQ hn)
    have hprod : n * (hN * n * hN⁻¹) ∈ N' := N'.mul_mem hn hconjN
    have hoddp : Odd (orderOf (ψ (n * (hN * n * hN⁻¹)))) :=
      (hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N' hprod)).of_dvd_nat
        (orderOf_map_dvd ψ _)
    have h15 := pow_1485_eq_one hoddp
    apply hc15
    have h16 := congrArg (fun x : ↥autModel => w⁻¹ * (x : Equiv.Perm (Fin 24)) * w) h15
    simp only [map_mul, map_inv, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv,
      OneMemClass.coe_one] at h16
    rw [hhψ] at h16
    simp only at h16
    rw [show w⁻¹ * (((ψ n : ↥autModel) : Equiv.Perm (Fin 24)) * (w * c * w⁻¹ *
        ((ψ n : ↥autModel) : Equiv.Perm (Fin 24)) * (w * c * w⁻¹)⁻¹)) ^ 1485 * w =
        (w⁻¹ * (((ψ n : ↥autModel) : Equiv.Perm (Fin 24)) * (w * c * w⁻¹ *
        ((ψ n : ↥autModel) : Equiv.Perm (Fin 24)) * (w * c * w⁻¹)⁻¹)) * w⁻¹⁻¹) ^ 1485 by
      rw [conj_pow, inv_inv]] at h16
    have e2 : w⁻¹ * (((ψ n : ↥autModel) : Equiv.Perm (Fin 24)) * (w * c * w⁻¹ *
        ((ψ n : ↥autModel) : Equiv.Perm (Fin 24)) * (w * c * w⁻¹)⁻¹)) * w⁻¹⁻¹ =
        y' * (c * y' * c⁻¹) := by
      rw [hy']
      group
    rw [e2] at h16
    simpa using h16
  set T'' := T.subgroupOf (normalizer (A : Set G)) with hT''
  have hT''Q : T'' ≤ Q' := hUQ'.le
  have hQN : Q' ≤ normalizer (N' : Set (normalizer (A : Set G))) :=
    (normal_subgroupOf_iff_le_normalizer hNQ).1 hNn
  have hT''N : T'' ≤ normalizer (N' : Set (normalizer (A : Set G))) := hT''Q.trans hQN
  have hNT : N' ⊓ T'' = ⊥ :=
    two_subgroup_of_odd_eq_bot (N' ⊓ T'') N' hUQ'.isPGroup.to_inf_right hNodd inf_le_left
  have hcardsup : Nat.card (N' ⊔ T'' : Subgroup (normalizer (A : Set G))) =
      Nat.card N' * Nat.card T'' := AS76b.card_sup_eq_mul hT''N hNT
  have hrel := relIndex_mul_card N' Q'
  rw [inf_eq_left.mpr hNQ, hkN] at hrel
  have hnd : ¬ 2 ∣ Nat.card N' := by
    have := Nat.odd_iff.mp hNodd
    omega
  have hT''card : Nat.card T'' = 2 ^ kN := by
    rw [hUQ'.card_eq, ← hrel, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnd, add_zero,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      smul_eq_mul, mul_one]
  have hQeq : N' ⊔ T'' = Q' :=
    eq_of_le_of_card_ge (sup_le hNQ hT''Q) (by rw [hcardsup, hT''card, ← hrel, mul_comm])
  obtain ⟨hh0D, hh0t, hh0c⟩ := m12_h_check_spec hk hch hrt hv0 hOh
  obtain ⟨b, hbT, hbψ⟩ := exists_of_excClass hw hb₀E
  have hxD : w * permOfArr 24 m12OverH0 * w⁻¹ ∈ blockGroup := hconjD hwR hh0D
  obtain ⟨h, hhA, hhψ, hht⟩ := exists_lift_commute hψ hZ ht2
    (x := ⟨w * permOfArr 24 m12OverH0 * w⁻¹, blockGroup_le_autModel hxD⟩) hxD (by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [htψ]
      calc w * permOfArr 24 m12OverH0 * w⁻¹ * (w * t₀ * w⁻¹)
          = w * (permOfArr 24 m12OverH0 * t₀) * w⁻¹ := by group
        _ = w * (t₀ * permOfArr 24 m12OverH0) * w⁻¹ := by rw [hh0t]
        _ = w * t₀ * w⁻¹ * (w * permOfArr 24 m12OverH0 * w⁻¹) := by group)
  set hN : normalizer (A : Set G) := ⟨h, le_normalizer hhA⟩ with hhN
  have hhQ := hnormQ hhA hht
  have hbQ : b ∈ Q' := hT''Q (show b ∈ T'' from hbT)
  have hzQ : ⁅hN, b⁆ ∈ Q' := by
    rw [commutatorElement_def]
    exact Q'.mul_mem ((mem_normalizer_iff.mp hhQ b).mp hbQ |> fun h1 => by
      simpa [mul_assoc] using h1) (Q'.inv_mem hbQ)
  have hzA : ((⁅hN, b⁆ : normalizer (A : Set G)) : G) ∈ A := by
    have := J2End.commutatorElement_mem_of_mem_left hhA b.2
    simpa [commutatorElement_def] using this
  have hzψ : ψ ⁅hN, b⁆ = ψ t := by
    apply Subtype.ext
    rw [map_commutatorElement, hhψ, htψ]
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hbψ, ← hh0c, commutatorElement_def]
    group
  rw [← hQeq] at hzQ
  have hzmem : ⁅hN, b⁆ ∈ (N' : Set (normalizer (A : Set G))) *
      (T'' : Set (normalizer (A : Set G))) := by
    rw [← coe_mul_of_right_le_normalizer_left N' T'' hT''N]
    exact hzQ
  obtain ⟨n, hn, u, hu, hnu⟩ := hzmem
  have hψu : ψ u = ψ t := by rw [← hzψ, ← hnu, map_mul, hN1 n hn, one_mul]
  have hut : u = t := by
    have h1 : ψ (u * t⁻¹) = 1 := by rw [map_mul, map_inv, hψu, mul_inv_cancel]
    have h2 : ((u * t⁻¹ : normalizer (A : Set G)) : G) ∈ T ⊓ K :=
      ⟨T.mul_mem hu (T.inv_mem htT), (hψ.eq_one_iff _).mp h1⟩
    rw [hTK, mem_bot] at h2
    exact mul_inv_eq_one.mp (Subtype.ext h2)
  have hnK : (n : G) ∈ K := (hψ.eq_one_iff n).mp (hN1 n hn)
  have hnz : (n : G) * (⁅hN, b⁆ : normalizer (A : Set G)) =
      (⁅hN, b⁆ : normalizer (A : Set G)) * n := (mem_centralizer_iff.mp hnK _ hzA).symm
  have hoddn : Odd (orderOf (n : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N' hn)
  have htA : (t : G) ∈ A := by
    have e1 : (t : G) = (n : G)⁻¹ * (⁅hN, b⁆ : normalizer (A : Set G)) := by
      rw [← hut, ← hnu, Subgroup.coe_mul, inv_mul_cancel_left]
    have e2 : (t : G) = (t : G) ^ orderOf (n : G) := by
      obtain ⟨j, hj⟩ := hoddn
      rw [hj, pow_succ, pow_mul, ht2, one_pow, one_mul]
    have hcn : Commute (n : G)⁻¹ ((⁅hN, b⁆ : normalizer (A : Set G)) : G) :=
      (Commute.inv_left hnz)
    rw [e2, e1, hcn.mul_pow, inv_pow, pow_orderOf_eq_one, inv_one, one_mul]
    exact pow_mem hzA _
  have hRt : R ≤ centralizer ({(t : G)} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hov.sylowR.le hx) _ htA).symm
  exact hnot (Asc76.Sec5.isSylowOf_of_le_centralizer hov.tight hov.not_mem_K hov.sylowK
    hov.sylowR htT ht1 hRt)

theorem m12_isSylowOf_of_overlap'
    {S : Array (Array ℕ)} {Wd : Array (List ℤ)} {sG roots : Array ℕ}
    {nodes : Array CFSG.KC.Census.NodeP} {cS : CFSG.KC.Census.ArrCertP}
    {wcs : Array (Array CFSG.KC.Census.ArrCertP)} {excs : List CFSG.KC.Census.ExcRefP}
    (hc : m12CheckW S Wd m12E0 sG roots nodes cS wcs excs = true)
    (hE : m12EndCheck S m12E0 m12EndA0 m12EndLeaves m12EndL m12EndSigma m12EndC0 m12EndZ = true)
    (hO : m12OverFacts S)
    (h22 : Asc76Lemma22) (h75 : AS76b.Asc75Theorem4) (hA : standardComponentIsStandard A)
    (hm : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (e : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Carrier .M12)
    {R : Subgroup G} (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRd : ¬ IsDihedralTwoGroup R)
    {y : G} (hy : y ∉ normalizer (A : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) y ⊓ normalizer (A : Set G)))
    (hT1 : T ≠ ⊥) : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  have hTN : T ≤ normalizer (K : Set G) := by
    rw [AS76b.normalizer_centralizer_eq hA]
    exact hT.le.trans inf_le_right
  obtain ⟨S₀, hS₀, hTS₀⟩ := exists_isSylowOf_le hT.isPGroup (le_sup_right : T ≤ K ⊔ T)
  have hR' : IsSylowOf 2 (S₀ ⊓ K) K :=
    hS₀.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hTN)
  have hTR' : T ≤ normalizer ((S₀ ⊓ K : Subgroup G) : Set G) := fun t ht =>
    Asc76.Sec5.mem_normalizer_inf (le_normalizer (hTS₀ ht)) (hTN ht)
  obtain ⟨c, -, hcR⟩ := exists_rightConjugate_eq_of_isSylowOf hR' hR
  have hR'd : ¬ IsDihedralTwoGroup (S₀ ⊓ K) := fun hd =>
    hRd (Asc76.Sec5.isDihedralTwoGroup_of_mulEquiv
      (by rw [← hcR]; exact R.equivMapOfInjective _ (MulAut.conj c⁻¹).injective) hd)
  exact m12_isSylowOf_overlap hc hE hO h22 h75 hA hm e hR'd ⟨hA, hy, hT, hT1, hR', hTR'⟩

theorem m12_isElemAbelian_of_not_dihedral
    {S : Array (Array ℕ)} {Wd : Array (List ℤ)} {sG roots : Array ℕ}
    {nodes : Array CFSG.KC.Census.NodeP} {cS : CFSG.KC.Census.ArrCertP}
    {wcs : Array (Array CFSG.KC.Census.ArrCertP)} {excs : List CFSG.KC.Census.ExcRefP}
    (hc : m12CheckW S Wd m12E0 sG roots nodes cS wcs excs = true)
    (hE : m12EndCheck S m12E0 m12EndA0 m12EndLeaves m12EndL m12EndSigma m12EndC0 m12EndZ = true)
    (hO : m12OverFacts S)
    (h22 : Asc76Lemma22) (h75 : AS76b.Asc75Theorem4) (h4' : Asc76Theorem4)
    (hA : standardComponentIsStandard A) (hodd : standardComponentOddCore G = ⊥)
    (hm : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (e : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Carrier .M12)
    {R : Subgroup G} (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRd : ¬ IsDihedralTwoGroup R)
    {g : G} (hg : g ∉ normalizer (A : Set G)) : IsElemAbelian 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  set K₀ := AS76b.oUpperTwoPrime K with hK₀def
  have hNA : normalizer (K : Set G) = normalizer (A : Set G) := AS76b.normalizer_centralizer_eq hA
  have hRK₀ : R ≤ K₀ := Asc76.Sec5.le_oUpperTwoPrime_of_isPGroup hR.le hR.isPGroup
  have hK₀K : K₀ ≤ K := AS76b.oUpperTwoPrime_le K
  have hRK₀s : IsSylowOf 2 R K₀ := hR.of_le hRK₀ hK₀K
  have hNK : normalizer (K : Set G) ≤ normalizer (K₀ : Set G) :=
    AS76b.normalizer_le_normalizer_oUpperTwoPrime K
  have hReven : Even (Nat.card R) :=
    even_iff_two_dvd.mpr
      (AS76b.two_dvd_card_of_isSylowOf hR (AS76b.tightlyEmbedded_centralizer hA).1)
  have hK₀even : Even (Nat.card K₀) :=
    even_iff_two_dvd.mpr (hReven.two_dvd.trans (card_dvd_of_le hRK₀))
  have hNeq : normalizer (K₀ : Set G) = normalizer (K : Set G) :=
    le_antisymm (Asc76.Sec5.normalizer_le_normalizer_of_tightlyEmbedded
      (AS76b.tightlyEmbedded_centralizer hA) hK₀K hK₀even) hNK
  refine Asc76.Sec5.isElemAbelian_of_theorem4 h4' hA hodd hg hK₀K hNK
    (Asc76.Sec5.oUpperTwoPrime_oUpperTwoPrime K) (fun y heven => ?_) hRK₀s
    (Asc76.Sec5.one_lt_pRank_of_isSylowOf hR hm)
  by_cases hy : y ∈ normalizer (K : Set G)
  · have hKy : rightConjugate K₀ y = K₀ := (rightConjugate_eq_self_iff K₀ y).mpr (hNK hy)
    exact ⟨R, by rw [hKy]; exact hRK₀s, hRK₀.trans le_normalizer⟩
  have hyA : y ∉ normalizer (A : Set G) := by rwa [← hNA]
  have hle : rightConjugate K₀ y ⊓ normalizer (K₀ : Set G) ≤
      rightConjugate K y ⊓ normalizer (A : Set G) := by
    rw [hNeq, hNA]
    exact inf_le_inf_right _ (rightConjugate_le_rightConjugate hK₀K y)
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (rightConjugate K y ⊓ normalizer (A : Set G))
  have hT1 : T ≠ ⊥ := AS76b.isSylowOf_ne_bot_of_even hT
    (even_iff_two_dvd.mpr (heven.two_dvd.trans (card_dvd_of_le hle)))
  have hTs := m12_isSylowOf_of_overlap' hc hE hO h22 h75 hA hm e hR hRd hyA hT hT1
  have hTK₀ : T ≤ rightConjugate K₀ y := by
    rw [hK₀def, ← Asc76X.oUpperTwoPrime_rightConjugate]
    exact Asc76.Sec5.le_oUpperTwoPrime_of_isPGroup hTs.le hT.isPGroup
  refine ⟨T, hTs.of_le hTK₀ (rightConjugate_le_rightConjugate hK₀K y), ?_⟩
  rw [hNeq, hNA]
  exact hT.le.trans inf_le_right

theorem m12_false_of_not_dihedral
    {S : Array (Array ℕ)} {Wd : Array (List ℤ)} {sG roots : Array ℕ}
    {nodes : Array CFSG.KC.Census.NodeP} {cS : CFSG.KC.Census.ArrCertP}
    {wcs : Array (Array CFSG.KC.Census.ArrCertP)} {excs : List CFSG.KC.Census.ExcRefP}
    (hc : m12CheckW S Wd m12E0 sG roots nodes cS wcs excs = true)
    (hE : m12EndCheck S m12E0 m12EndA0 m12EndLeaves m12EndL m12EndSigma m12EndC0 m12EndZ = true)
    (hO : m12OverFacts S)
    (h22 : Asc76Lemma22) (h75 : AS76b.Asc75Theorem4) (h4' : Asc76Theorem4)
    (hA : standardComponentIsStandard A) (hodd : standardComponentOddCore G = ⊥)
    (hm : 1 < Open.pRank 2 (centralizer (A : Set G))) (hnn : ¬ A.Normal)
    (e : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Carrier .M12)
    {R : Subgroup G} (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hRd : ¬ IsDihedralTwoGroup R) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, heven⟩ := AS76b.exists_even_overlap hA hodd hm hnn
  obtain ⟨T, hT⟩ := exists_isSylowOf 2
    (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G))
  have hT1 : T ≠ ⊥ := AS76b.isSylowOf_ne_bot_of_even hT heven
  have hTs := m12_isSylowOf_of_overlap' hc hE hO h22 h75 hA hm e hR hRd hg hT hT1
  have hRe := m12_isElemAbelian_of_not_dihedral hc hE hO h22 h75 h4' hA hodd hm e hR hRd hg
  have hR4 : 4 ≤ Nat.card R := by
    obtain ⟨E, hER, -, hE4⟩ := Asc76X.exists_fourGroup_le
      (Asc76.Sec5.one_lt_pRank_of_isSylowOf hR hm)
    rw [← hE4]
    exact card_le_of_le hER
  exact false_of_config hc hE hA e hg hTs (hT.le.trans inf_le_right) hR hRe.2 hR4

end CFSG.ComponentClassification.RankTwoSporadic.M12
