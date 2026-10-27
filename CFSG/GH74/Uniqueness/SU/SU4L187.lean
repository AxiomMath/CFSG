module

public import CFSG.GH74.Uniqueness.SU.SU4L18H
public import CFSG.Adapters.Involutions
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup

variable {G : Type} [Group G]

@[expose] def omegaZ (D : Subgroup G) : Subgroup G where
  carrier := {e | e ∈ D ∧ (∀ d ∈ D, d * e = e * d) ∧ e * e = 1}
  one_mem' := ⟨D.one_mem, fun d _ => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨haD, hac, ha2⟩ ⟨hbD, hbc, hb2⟩
    refine ⟨D.mul_mem haD hbD, fun d hd => ?_, ?_⟩
    · calc d * (a * b) = (d * a) * b := by group
        _ = (a * d) * b := by rw [hac d hd]
        _ = a * (d * b) := by group
        _ = a * (b * d) := by rw [hbc d hd]
        _ = (a * b) * d := by group
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hac b hbD]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨haD, hac, ha2⟩
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    show a⁻¹ ∈ D ∧ (∀ d ∈ D, d * a⁻¹ = a⁻¹ * d) ∧ a⁻¹ * a⁻¹ = 1
    rw [hainv]
    exact ⟨haD, hac, ha2⟩

theorem omegaZ_le (D : Subgroup G) : omegaZ D ≤ D := fun _ he => he.1

theorem isElemAbelian_omegaZ (D : Subgroup G) : Open.IsElemAbelian 2 (omegaZ D) := by
  rw [SU1.isElemAbelian_iff]
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · exact hb.2.1 a ha.1
  · rw [pow_two]; exact ha.2.2

theorem conj_mem_omegaZ {D : Subgroup G} {g y : G} (hg : g ∈ normalizer (D : Set G))
    (hy : y ∈ omegaZ D) : g * y * g⁻¹ ∈ omegaZ D := by
  obtain ⟨hyD, hyc, hy2⟩ := hy
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hyD, fun d hd => ?_, ?_⟩
  · have hd' : g⁻¹ * d * g ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) d).mp hd
      simpa using this
    have := hyc _ hd'
    calc d * (g * y * g⁻¹) = g * ((g⁻¹ * d * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * d * g)) * g⁻¹ := by rw [this]
      _ = (g * y * g⁻¹) * d := by group
  · calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hy2]; group

theorem normalizer_le_normalizer_omegaZ (D : Subgroup G) :
    normalizer (D : Set G) ≤ normalizer ((omegaZ D : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => conj_mem_omegaZ hg hy
  · intro hy
    have := conj_mem_omegaZ (inv_mem hg) hy
    simpa [mul_assoc] using this

section Finite

variable [Finite G]

theorem conj_eq_of_rank_le_one {D : Subgroup G} {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzE : z ∈ omegaZ D) (hE1 : Open.pRank 2 (omegaZ D) ≤ 1) {n : G}
    (hn : n ∈ normalizer (D : Set G)) : n⁻¹ * z * n = z := by
  by_contra hne
  have hw := conj_mem_omegaZ (inv_mem hn) hzE
  have hw' : n⁻¹ * z * n ∈ omegaZ D := by simpa using hw
  have hw2 : (n⁻¹ * z * n) * (n⁻¹ * z * n) = 1 := hw'.2.2
  have hw1 : n⁻¹ * z * n ≠ 1 := by
    intro h
    apply hz1
    have : z = n * (n⁻¹ * z * n) * n⁻¹ := by group
    rw [this, h]; group
  have hwn : n⁻¹ * z * n ∉ zpowers z := by
    intro hm
    rcases eq_one_or_eq_of_mem_zpowers hz2 hm with h | h
    · exact hw1 h
    · exact hne h
  have hcomm : z * (n⁻¹ * z * n) = (n⁻¹ * z * n) * z := by
    have := hzE.2.1 _ hw'.1
    exact this.symm
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (by rw [pow_two]; exact hz2)
    (by rw [pow_two]; exact hw2) hz1 hwn hcomm
  have hle : zpowers z ⊔ zpowers (n⁻¹ * z * n) ≤ omegaZ D :=
    sup_le (Subgroup.zpowers_le.mpr hzE) (Subgroup.zpowers_le.mpr hw')
  have := SU1.le_pRank (by norm_num) hle hel hcard
  omega

end Finite

variable {G : Type} [Group G] [Finite G]

theorem eq_one_or_eq_of_mul_self_eq_one {K S : Subgroup G} {z : G} (hKS : K ≤ S)
    (hzc : ∀ s ∈ S, s * z = z * s) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzK : z ∈ K)
    (hKrk : Open.pRank 2 K = 1) : ∀ k ∈ K, k * k = 1 → k = 1 ∨ k = z := by
  intro k hkK hk2
  by_contra hcon
  push Not at hcon
  have hkn : k ∉ zpowers z := by
    intro hm
    rcases eq_one_or_eq_of_mem_zpowers hz2 hm with h | h
    · exact hcon.1 h
    · exact hcon.2 h
  have hcomm : z * k = k * z := (hzc k (hKS hkK)).symm
  obtain ⟨hel2, hcard2⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two
    (by rw [pow_two]; exact hz2) (by rw [pow_two]; exact hk2) hz1 hkn hcomm
  have hle : zpowers z ⊔ zpowers k ≤ K :=
    sup_le (Subgroup.zpowers_le.mpr hzK) (Subgroup.zpowers_le.mpr hkK)
  have := SU1.le_pRank (by norm_num) hle hel2 hcard2
  omega

theorem omegaZ_contradiction {S D : Subgroup G} {z : G} (hS : IsPGroup 2 S)
    (h3 : 3 ≤ Open.pRank 2 S) (hDS : D ≤ S) (hCD : centralizer (D : Set G) ⊓ S ≤ D)
    (hzS : z ∈ S) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ s ∈ S, s * z = z * s)
    (hzE : z ∈ omegaZ D) (hE2 : 2 ≤ Open.pRank 2 (omegaZ D))
    (hC2 : Open.pRank 2 (centralizer ((omegaZ D : Subgroup G) : Set G) ⊓ S) ≤ 2)
    {n : G} (hn : n ∈ normalizer (D : Set G)) (hnz : n⁻¹ * z * n ≠ z) : False := by
  set E := omegaZ D with hEdef
  have hEel : Open.IsElemAbelian 2 E := isElemAbelian_omegaZ D
  have hEel' := SU1.isElemAbelian_iff.mp hEel
  have hED : E ≤ D := omegaZ_le D
  have hES : E ≤ S := hED.trans hDS
  have hEC : E ≤ centralizer (E : Set G) ⊓ S :=
    le_inf (fun e he => Subgroup.mem_centralizer_iff.mpr (fun f hf => hEel'.1 f hf e he)) hES
  have hrkE : Open.pRank 2 E = 2 := by
    have := SU1.pRank_mono (p := 2) (by norm_num) hEC
    omega
  obtain ⟨k, hk⟩ := SU1.IsElemAbelian.exists_card Nat.prime_two hEel
  have hkle : k ≤ 2 := by
    have := SU1.le_pRank (p := 2) (by norm_num) (le_refl E) hEel hk
    omega
  have hk2 : 2 ≤ k := by
    obtain ⟨E₀, hE₀E, hE₀el, hE₀c⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two hE2
    have := Subgroup.card_le_of_le hE₀E
    rw [hE₀c, hk] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
  have hEcard : Nat.card E = 2 ^ 2 := by rw [hk]; congr 1; omega
  have hE4 : IsFour S E := ⟨hES, hEel, hEcard⟩
  have hiso : IsIsolatedVertex S E := by
    refine isIsolatedVertex_iff.mpr ⟨hE4, fun B hB hc => ?_⟩
    by_contra hBE
    have hsup := SU1.sup_isElemAbelian_card Nat.prime_two hEel hEcard hB.2.1 hB.2.2
      (fun h => hBE h.symm) hc
    have hsupC : E ⊔ B ≤ centralizer (E : Set G) ⊓ S :=
      sup_le hEC (le_inf (fun b hb => Subgroup.mem_centralizer_iff.mpr
        (fun e he => hc e he b hb)) hB.1)
    obtain ⟨m, hm⟩ := SU1.IsElemAbelian.exists_card Nat.prime_two hsup.1
    have hm3 : 3 ≤ m := by
      have h2 := hsup.2
      rw [hm] at h2
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
    have := SU1.le_pRank (p := 2) (by norm_num) hsupC hsup.1 hm
    omega
  have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  obtain ⟨h4S, hisoS⟩ := hiso
  obtain ⟨hnot, hall⟩ := SU1.ig10_21_iii Nat.prime_two hS h3 (exists_isNormalEp2 hS h3)
    ⟨E, h4S⟩ hisoS (E := zpowers z) (Subgroup.zpowers_le.mpr hzS)
    (le_normalizer_zpowers_of_central hzc) (SU1.isElemAbelian_zpowers hz2')
    (by rwa [Ne, Subgroup.zpowers_eq_bot])
  obtain ⟨a, haE, haz⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨hcentEq, K, hKS, hKC, hKinf, hKsup, hEzK, hKrk⟩ := (hall a haE haz).2
  have ha1 : a ≠ 1 := fun h => haz (h ▸ Subgroup.one_mem _)
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hEel'.2 a haE
  have hzK : z ∈ K := hEzK (Subgroup.mem_inf.mpr ⟨hzE, Subgroup.mem_zpowers z⟩)
  have hKinv : ∀ k ∈ K, k * k = 1 → k = 1 ∨ k = z :=
    eq_one_or_eq_of_mul_self_eq_one hKS hzc hz2 hz1 hzK hKrk
  have hEgen : zpowers z ⊔ zpowers a = E := by
    obtain ⟨-, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two hz2'
      (by rw [pow_two]; exact ha2) hz1 haz (hEel'.1 z hzE a haE)
    exact Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hzE)
      (Subgroup.zpowers_le.mpr haE)) (by rw [hcard, hEcard])
  have hwE : n⁻¹ * z * n ∈ E := by simpa using conj_mem_omegaZ (inv_mem hn) hzE
  have hw1 : n⁻¹ * z * n ≠ 1 := by
    intro h
    apply hz1
    have : z = n * (n⁻¹ * z * n) * n⁻¹ := by group
    rw [this, h]; group
  have hwK : n⁻¹ * z * n ∉ K := by
    intro hwK
    have hwE' : n⁻¹ * z * n ∈ zpowers z ⊔ zpowers a := hEgen ▸ hwE
    obtain ⟨b, hb, c, hc, hbc⟩ := SU1.mem_sup_of_commute
      (zpowers_commute_of (show z * a = a * z from hEel'.1 z hzE a haE)) hwE'
    have hbz := eq_one_or_eq_of_mem_zpowers hz2 hb
    have hca := eq_one_or_eq_of_mem_zpowers ha2 hc
    have haK : a ∉ K := by
      intro haK
      have : a ∈ zpowers a ⊓ K := ⟨Subgroup.mem_zpowers a, haK⟩
      rw [hKinf, Subgroup.mem_bot] at this
      exact ha1 this
    rcases hbz with h1 | h1 <;> rcases hca with h2 | h2
    · exact hw1 (by rw [← hbc, h1, h2]; simp)
    · have : n⁻¹ * z * n = a := by rw [← hbc, h1, h2]; simp
      rw [this] at hwK
      exact haK hwK
    · exact hnz (by rw [← hbc, h1, h2]; simp)
    · have hw : n⁻¹ * z * n = z * a := by rw [← hbc, h1, h2]
      rw [hw] at hwK
      apply haK
      have h4 := K.mul_mem hzK hwK
      have e : z * (z * a) = a := by rw [← mul_assoc, hz2, one_mul]
      rwa [e] at h4
  have hDle : D ≤ zpowers a ⊔ K := by
    rw [hKsup, ← hcentEq]
    refine le_inf (fun d hd => ?_) hDS
    exact Subgroup.mem_centralizer_iff.mpr (fun e he => (he.2.1 d hd).symm)
  have hcommaK : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm
  have hdecomp : ∀ d ∈ D, ∃ a' ∈ zpowers a, ∃ k ∈ K, a' * k = d := fun d hd =>
    SU1.mem_sup_of_commute (A := zpowers a) (B := K) (fun a' ha' k hk => by
      obtain ⟨j, rfl⟩ := ha'
      exact (Commute.zpow_left (show Commute a k from hcommaK k hk) j).eq) (hDle hd)
  have hsq : ∀ k ∈ D ⊓ K, k * k = 1 := by
    intro k hk
    by_contra hk2
    have hkn : k ∉ zpowers z := by
      intro hm
      rcases eq_one_or_eq_of_mem_zpowers hz2 hm with h | h
      · exact hk2 (by rw [h]; simp)
      · exact hk2 (by rw [h]; exact hz2)
    obtain ⟨y, hyDK, -, -, hyyV, hyy1⟩ := exists_orderOf_four (P := D ⊓ K) (V := zpowers z)
      (hS.to_le (inf_le_right.trans hKS))
      (fun v hv => by
        rcases eq_one_or_eq_of_mem_zpowers hz2 hv with h | h <;> rw [h] <;> simp [hz2])
      (fun t ht h => by
        rcases hKinv t ht.2 h with h' | h' <;> rw [h'] <;> simp)
      hk hkn
    have hyz : y * y = z := by
      rcases eq_one_or_eq_of_mem_zpowers hz2 hyyV with h | h
      · exact absurd h hyy1
      · exact h
    have hy'D : n⁻¹ * y * n ∈ D := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hn) y).mp hyDK.1
    obtain ⟨a'', ha'', k'', hk'', hak⟩ := hdecomp _ hy'D
    have hwsq : n⁻¹ * z * n = k'' * k'' := by
      have h1 : n⁻¹ * z * n = (n⁻¹ * y * n) * (n⁻¹ * y * n) := by rw [← hyz]; group
      rw [h1, ← hak]
      rcases eq_one_or_eq_of_mem_zpowers ha2 ha'' with h | h
      · rw [h]; simp
      · rw [h]
        calc a * k'' * (a * k'') = a * (k'' * a) * k'' := by group
          _ = a * (a * k'') * k'' := by rw [← hcommaK k'' hk'']
          _ = (a * a) * (k'' * k'') := by group
          _ = k'' * k'' := by rw [ha2, one_mul]
    exact hwK (hwsq ▸ K.mul_mem hk'' hk'')
  have hDE : D ≤ E := by
    intro d hd
    obtain ⟨a', ha', k, hk, hak⟩ := hdecomp d hd
    have haD : a ∈ D := hED haE
    have ha'D : a' ∈ D := Subgroup.zpowers_le.mpr haD ha'
    have hkD : k ∈ D := by
      have : k = a'⁻¹ * d := by rw [← hak]; group
      rw [this]
      exact D.mul_mem (D.inv_mem ha'D) hd
    have hk' : k = 1 ∨ k = z := hKinv k hk (hsq k ⟨hkD, hk⟩)
    have ha'E : a' ∈ E := Subgroup.zpowers_le.mpr haE ha'
    have hkE : k ∈ E := by
      rcases hk' with h | h
      · rw [h]; exact E.one_mem
      · rw [h]; exact hzE
    rw [← hak]
    exact E.mul_mem ha'E hkE
  have hDeq : D = E := le_antisymm hDE hED
  have hCle : centralizer (E : Set G) ⊓ S ≤ E := by
    have := hCD
    rw [hDeq] at this
    exact this
  have hcardC : Nat.card ↥(centralizer (E : Set G) ⊓ S) = 4 := by
    have h1 : centralizer (E : Set G) ⊓ S = E := le_antisymm hCle hEC
    rw [h1, hEcard]
    norm_num
  have h4 := four_lt_card_centralizer hS h3 ⟨h4S, hisoS⟩
  omega

variable {G : Type} [Group G] [Finite G]

theorem lemma187_core {S : Sylow 2 G} {U M V : Subgroup G} {x z : G} (h : Hyp184Core S U M)
    (hc : Conf18H S M V x z) {D : Subgroup G} (hDS : D ≤ (S : Subgroup G))
    (hCD : centralizer (D : Set G) ⊓ (S : Subgroup G) ≤ D)
    (hnot : ¬ IsFusionIsolated (normalizer (D : Set G)) (normalizer (D : Set G) ⊓ (S : Subgroup G))
      z) : normalizer (D : Set G) ≤ M := by
  have hSp : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hzS : z ∈ (S : Subgroup G) := hc.z_mem_S
  have hz2 : z * z = 1 := hc.z_mul_self
  have hz1 : z ≠ 1 := hc.z_ne_one
  have hzc := hc.z_center
  have hzD : z ∈ D := hCD (Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_iff.mpr (fun d hd => hzc d (hDS hd)), hzS⟩)
  have hzE : z ∈ omegaZ D := ⟨hzD, fun d hd => hzc d (hDS hd), hz2⟩
  have hES : omegaZ D ≤ (S : Subgroup G) := (omegaZ_le D).trans hDS
  have hex : ∃ n ∈ normalizer (D : Set G), n⁻¹ * z * n ∈
      normalizer (D : Set G) ⊓ (S : Subgroup G) ∧ n⁻¹ * z * n ≠ z := by
    by_contra hcon
    push Not at hcon
    exact hnot ⟨Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hzD, hzS⟩, fun u hu huP =>
      hcon u hu huP⟩
  obtain ⟨n, hnN, -, hnz⟩ := hex
  by_cases hE2 : 2 ≤ Open.pRank 2 (omegaZ D)
  · by_cases hC3 : 3 ≤ Open.pRank 2
        (centralizer ((omegaZ D : Subgroup G) : Set G) ⊓ (S : Subgroup G))
    · exact (normalizer_le_normalizer_omegaZ D).trans
        ((normalizer_le_gammaElem hES (isElemAbelian_omegaZ D) hE2 hC3).trans h.gamma_le)
    · exact absurd (omegaZ_contradiction hSp h.rank hDS hCD hzS hz2 hz1 hzc hzE hE2 (by omega) hnN
        hnz) id
  · exact absurd (conj_eq_of_rank_le_one hz2 hz1 hzE (by omega) hnN) hnz

theorem lemma188_core :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G),
      Hyp184Core S U M → Conf18H S M V x z → ¬ IsFusionIsolated M (S : Subgroup G) z := by
  intro G _ _ S U M V x z h hc hiso
  have hzS : z ∈ (S : Subgroup G) := hc.z_mem_S
  have hz1 : z ≠ 1 := hc.z_ne_one
  obtain ⟨g, hgS, hgz⟩ : ∃ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) ∧ g⁻¹ * z * g ≠ z := by
    by_contra hcon
    push Not at hcon
    have hzZ : (⟨z, hzS⟩ : ↥(S : Subgroup G)) ∈ Subgroup.center ↥(S : Subgroup G) :=
      Subgroup.mem_center_iff.mpr (fun s => Subtype.ext (hc.z_center s.1 s.2))
    have hzo : orderOf (⟨z, hzS⟩ : ↥(S : Subgroup G)) = 2 :=
      (Subgroup.orderOf_coe (⟨z, hzS⟩ : ↥(S : Subgroup G))).symm.trans hc.hz
    have hZ := CFSG.Adapters.glauberman_zStar S ⟨z, hzS⟩ hzZ hzo (fun g hg => hcon g hg)
    have hodd : CFSG.oddCore G = ⊥ := by
      rcases h.simple.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h0 | h0
      · exact h0
      · exfalso
        have : z ∈ CFSG.oddCore G := by rw [h0]; exact Subgroup.mem_top z
        exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hc.hz this
    have hcentral : ∀ g : G, g * z = z * g := by
      intro g
      obtain ⟨c, hc', k, hk, hg⟩ := hZ.1 g
      rw [hodd, Subgroup.mem_bot] at hk
      subst hk
      rw [mul_one] at hg
      subst hg
      exact (Subgroup.mem_centralizer_singleton_iff.mp hc')
    rcases h.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
    · have : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr hcentral
      rw [h0, Subgroup.mem_bot] at this
      exact hz1 this
    · obtain ⟨a, b, hab⟩ := h.nonab
      have : a ∈ Subgroup.center G := by rw [h0]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp this b).symm
  obtain ⟨Q, hQ, hzQ, n, hnQ, hnz⟩ :=
    CFSG.RankTwoShapes.exists_alperinSubgroup_moving S hzS hgS hgz
  have hQS : Q ≤ (S : Subgroup G) := hQ.1
  have hCQ : centralizer (Q : Set G) ⊓ (S : Subgroup G) ≤ Q := hQ.2.2.1
  have hznQ : n⁻¹ * z * n ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hnQ) z).mp hzQ
    simpa using this
  have hnotIso : ¬ IsFusionIsolated (normalizer (Q : Set G))
      (normalizer (Q : Set G) ⊓ (S : Subgroup G)) z := by
    rintro ⟨-, hall⟩
    exact hnz (hall n hnQ (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hznQ, hQS hznQ⟩))
  have hQM : normalizer (Q : Set G) ≤ M := lemma187_core h hc hQS hCQ hnotIso
  exact hnz (hiso.2 n (hQM hnQ) (hQS hznQ))

theorem lemma188 : Lemma188Stmt := by
  intro G _ _ S U M V x z h hc hiso
  exact lemma188_core G S U M V x z h.toHyp184Core hc hiso

end CFSG.GH74.Uniqueness.SU.SU4
