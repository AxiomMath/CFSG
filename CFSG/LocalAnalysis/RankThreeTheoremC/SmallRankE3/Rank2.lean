module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Rank3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Cyc
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Signal
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Step0
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.RankThree.PartOne.K1214.CycAlg

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem r10h7_le_centralizer_of_mem {E : Subgroup G} (hE : IsElemAbelian 3 E) {u : G}
    (hu : u ∈ E) : E ≤ centralizer ({u} : Set G) := fun e he =>
  mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨u, hu⟩))

private theorem r10h7_three_le_pRank_centralizer {U E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hUE : U ≤ E) {u : G} (hu : u ∈ U) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({u} : Set G)) :=
  le_pRank_of_isElemAbelian Nat.prime_three (r10h7_le_centralizer_of_mem hE (hUE hu)) hE
    (by rw [hE27]; norm_num)

private theorem r10h7_pRank_centralizer_conj (g y : G) :
    CFSG.Open.pRank 3 (centralizer ({g * y * g⁻¹} : Set G)) =
      CFSG.Open.pRank 3 (centralizer ({y} : Set G)) := by
  have hcz : ∀ w : G,
      centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := fun w => by
    rw [zpowers_eq_closure, centralizer_closure]
  have hz : zpowers (g * y * g⁻¹) = (zpowers y).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hC : centralizer ({g * y * g⁻¹} : Set G) =
      (centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [hcz (g * y * g⁻¹), hcz y, hz, centralizer_map_automorphism]
  rw [hC]
  exact pRank_map_automorphism 3 (by norm_num) _ _

private theorem r10h7_not_mem_zpowers {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) : x ∉ zpowers z := by
  intro hx
  have hB := SmallRankPlane.of_situation h.setting h.situation h.point h.central
  have hle : zpowers x ⊔ zpowers z ≤ zpowers z := sup_le (zpowers_le.2 hx) le_rfl
  have h1 := Subgroup.card_le_of_le hle
  rw [hB.card_eq, Nat.card_zpowers, orderOf_eq_prime h.central.pow_eq_one h.central.ne_one] at h1
  norm_num at h1

private theorem r10h7_conj_not_mem {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {U E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hUE : U ≤ E) (g : G) : g * x * g⁻¹ ∉ U := by
  intro hxU
  have h3 := r10h7_three_le_pRank_centralizer hE hE27 hUE hxU
  have h2 := pRank_centralizer_le_two_of_mem_plane h (mem_sup_left (mem_zpowers x))
    (r10h7_not_mem_zpowers h)
  rw [r10h7_pRank_centralizer_conj] at h3
  omega

private theorem r10h7_not_conj {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {U E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hUE : U ≤ E) (g : G) :
    (zpowers x ⊔ zpowers z).map (MulAut.conj g).toMonoidHom ≠ U := by
  intro hgU
  refine r10h7_conj_not_mem h hE hE27 hUE g ?_
  rw [← hgU]
  exact ⟨x, mem_sup_left (mem_zpowers x), rfl⟩

private theorem r10h7_sup_zpowers {E : Subgroup G} (hE : IsElemAbelian 3 E) {w : G}
    (hw : w ^ 3 = 1) (hwE : w ∉ E) (hc : ∀ e ∈ E, e * w = w * e) :
    IsElemAbelian 3 (E ⊔ zpowers w) ∧ Nat.card (E ⊔ zpowers w : Subgroup G) = Nat.card E * 3 := by
  refine ⟨?_, CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three E hw hwE hc⟩
  have : CFSG.IsElementaryAbelian 3 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hE
  have : CFSG.IsElementaryAbelian 3 (zpowers w) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hw
  exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
    (CFSG.IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.2 (mem_centralizer_iff.2 hc)))

private theorem r10h7_central_mem_zpowers {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {Q U E : Subgroup G} (hBQ : zpowers x ⊔ zpowers z ≤ Q)
    (hUQ : U ≤ Q) (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hUE : U ≤ E)
    (hU : IsElemAbelian 3 U) (hU9 : Nat.card U = 9) {w : G} (hw3 : orderOf w = 3)
    (hwc : ∀ q ∈ Q, q * w = w * q) : w ∈ zpowers z := by
  by_contra hwz
  have hpl := SmallRankPlane.of_situation h.setting h.situation h.point h.central
  have hw3' : w ^ 3 = 1 := by rw [← hw3]; exact pow_orderOf_eq_one w
  have hwB : w ∈ zpowers x ⊔ zpowers z := hpl.mem_of_mem_centralizer w
    (mem_centralizer_iff.2 fun b hb => hwc b (hBQ hb)) hw3'
  have h2 := pRank_centralizer_le_two_of_mem_plane h hwB hwz
  have h3 : 3 ≤ CFSG.Open.pRank 3 (centralizer ({w} : Set G)) := by
    by_cases hwU : w ∈ U
    · exact r10h7_three_le_pRank_centralizer hE hE27 hUE hwU
    · have hc : ∀ u ∈ U, u * w = w * u := fun u hu => hwc u (hUQ hu)
      obtain ⟨hel, hcard⟩ := r10h7_sup_zpowers hU hw3' hwU hc
      refine le_pRank_of_isElemAbelian Nat.prime_three ?_ hel (by rw [hcard, hU9]; norm_num)
      exact sup_le (fun u hu => mem_centralizer_singleton_iff.2 (hc u hu))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  omega

private theorem r10h7_weakly_closed {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {Q U E : Subgroup G} (hBQ : zpowers x ⊔ zpowers z ≤ Q)
    (hUQ : U ≤ Q) (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hUE : U ≤ E)
    (hU : IsElemAbelian 3 U) (hU9 : Nat.card U = 9) {w : G} (hw3 : orderOf w = 3)
    (hwc : ∀ q ∈ Q, q * w = w * q) {g : G}
    (hg : g * w * g⁻¹ ∈ zpowers x ⊔ zpowers z) : g * w * g⁻¹ ∈ zpowers w := by
  have hwz : w ∈ zpowers z := r10h7_central_mem_zpowers h hBQ hUQ hE hE27 hUE hU hU9 hw3 hwc
  have hz3 : orderOf z = 3 := orderOf_eq_prime h.central.pow_eq_one h.central.ne_one
  have heq : zpowers w = zpowers z := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hwz)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hz3, hw3])
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (show z ∈ zpowers w by rw [heq]; exact mem_zpowers z)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hwz
  have hgz : g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z := by
    have : g * z * g⁻¹ = (g * w * g⁻¹) ^ j := by rw [conj_zpow, hj]
    rw [this]
    exact zpow_mem hg j
  have hgz' := mem_zpowers_of_conj_mem_plane h hgz
  have : g * w * g⁻¹ = (g * z * g⁻¹) ^ k := by rw [conj_zpow, hk]
  rw [heq, this]
  exact zpow_mem hgz' k

private theorem r10h7_isCyclic_center {Q B U : Subgroup G} (hQ : IsPGroup 3 Q) (hBQ : B ≤ Q)
    (hUQ : U ≤ Q) (hB9 : Nat.card B = 9) (hU : IsElemAbelian 3 U) (hU9 : Nat.card U = 9)
    (hmem : ∀ y ∈ centralizer (B : Set G), y ^ 3 = 1 → y ∈ B) (hBU : B ≠ U) :
    IsCyclic (center Q) := by
  by_contra hnc
  set Y : Subgroup G := (center Q).map Q.subtype with hY
  have hYQ : Y ≤ Q := map_subtype_le _
  have hYc : ∀ y ∈ Y, ∀ q ∈ Q, q * y = y * q := by
    rintro _ ⟨c, hc, rfl⟩ q hq
    exact congrArg Subtype.val (mem_center_iff.1 hc ⟨q, hq⟩)
  have hYp : IsPGroup 3 ↥Y := hQ.to_le hYQ
  have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb => (hYc a ha b (hYQ hb)).symm
  have hYnc : ¬ IsCyclic ↥Y := fun hc =>
    hnc ((Subgroup.equivMapOfInjective (center Q) Q.subtype Q.subtype_injective).isCyclic.2 hc)
  have key : ∀ B' : Subgroup G, Nat.card B' ≤ 3 → ∃ y ∈ Y, y ^ 3 = 1 ∧ y ∉ B' := by
    intro B' hB'
    by_contra hcon
    push Not at hcon
    exact hYnc (CFSG.RankThree.PartOne.K1214.isCyclic_of_torsion_le Nat.prime_three hYp hYcomm
      hB' hcon)
  obtain ⟨y₁, hy₁Y, hy₁3, hy₁⟩ := key ⊥ (by simp)
  have hy₁1 : y₁ ≠ 1 := fun h1 => hy₁ (Subgroup.mem_bot.2 h1)
  have hy₁c : Nat.card (zpowers y₁) = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hy₁3 hy₁1]
  obtain ⟨y₂, hy₂Y, hy₂3, hy₂⟩ := key (zpowers y₁) hy₁c.le
  have hyB : ∀ y ∈ Y, y ^ 3 = 1 → y ∈ B := fun y hy hy3 =>
    hmem y (mem_centralizer_iff.2 fun b hb => hYc y hy b (hBQ hb)) hy3
  have hcomm : ∀ e ∈ zpowers y₁, e * y₂ = y₂ * e := fun e he =>
    mem_centralizer_singleton_iff.1
      ((zpowers_le.2 (mem_centralizer_singleton_iff.2 (hYcomm y₁ hy₁Y y₂ hy₂Y))) he)
  have hV9 : Nat.card (zpowers y₁ ⊔ zpowers y₂ : Subgroup G) = 9 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers y₁) hy₂3 hy₂ hcomm,
      hy₁c]
  have hVB : zpowers y₁ ⊔ zpowers y₂ ≤ B :=
    sup_le (zpowers_le.2 (hyB y₁ hy₁Y hy₁3)) (zpowers_le.2 (hyB y₂ hy₂Y hy₂3))
  have hVeq : zpowers y₁ ⊔ zpowers y₂ = B :=
    Subgroup.eq_of_le_of_card_ge hVB (by omega)
  have hUB : U ≤ B := by
    intro u hu
    refine hmem u (mem_centralizer_iff.2 fun b hb => ?_) (hU.2 u hu)
    rw [← hVeq] at hb
    have hle : zpowers y₁ ⊔ zpowers y₂ ≤ centralizer ({u} : Set G) :=
      sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 (hYc y₁ hy₁Y u (hUQ hu)).symm))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 (hYc y₂ hy₂Y u (hUQ hu)).symm))
    exact mem_centralizer_singleton_iff.1 (hle hb)
  exact hBU (Subgroup.eq_of_le_of_card_ge hUB (by omega)).symm

private theorem r10h7_normalizer_le_of_le_U {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {E U S : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hUE : U ≤ E) (hU : IsElemAbelian 3 U) (hU9 : Nat.card U = 9)
    (hSU : S ≤ U) (hS1 : 1 ≤ CFSG.Open.pRank 3 S) : normalizer (S : Set G) ≤ M := by
  obtain ⟨E₁, hE₁S, -, hE₁c⟩ := exists_isElemAbelian_of_le_pRank Nat.prime_three (k := 1) hS1
  have hS3 : 3 ≤ Nat.card S := by
    have := Subgroup.card_le_of_le hE₁S
    rw [hE₁c] at this
    simpa using this
  obtain ⟨i, hi, hSi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (show Nat.card S ∣ 3 ^ 2 by simpa [hU9] using Subgroup.card_dvd_of_le hSU)
  have hS : Nat.card S = 3 ∨ Nat.card S = 9 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [pow_zero] at hSi
      omega
    · exact Or.inl (by rw [hSi]; norm_num)
    · exact Or.inr (by rw [hSi]; norm_num)
  rcases hS with hS | hS
  · have hSne : S ≠ ⊥ := fun hb => by
      rw [hb, Subgroup.card_bot] at hS
      omega
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hSne
    have hu1' : (u : G) ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
    have huS : (u : G) ∈ S := u.2
    have hu3 : (u : G) ^ 3 = 1 := hU.2 u (hSU huS)
    have heq : zpowers (u : G) = S := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 huS)
      (by rw [Nat.card_zpowers, orderOf_eq_prime hu3 hu1', hS])
    rw [← heq]
    exact normalizer_zpowers_le_of_isElemAbelian_le_centralizer h (hEM (hUE (hSU huS))) hu1' hu3
      hEM hE hE27 (r10h7_le_centralizer_of_mem hE (hUE (hSU huS)))
  · have hSeq : S = U := Subgroup.eq_of_le_of_card_ge hSU (by omega)
    subst hSeq
    refine normalizer_le_of_le_of_two_le_pRank h.setting h.u0 h.situation.mem_sigmaA
      h.situation.isCoreMaxLocal (IsPGroup.of_card (n := 2) (by rw [hU9]; norm_num))
      (hUE.trans hEM) ?_
    exact le_pRank_of_isElemAbelian Nat.prime_three le_rfl hU (by rw [hU9]; norm_num)

private theorem r10h7_centralizer_le {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {E U : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hUE : U ≤ E) (hU : IsElemAbelian 3 U) {u : G} (hu : u ∈ U)
    (hu1 : u ≠ 1) : centralizer ({u} : Set G) ≤ M :=
  centralizer_le_of_isElemAbelian_le_centralizer h (hEM (hUE hu)) hu1 (hU.2 u hu) hEM hE hE27
    (r10h7_le_centralizer_of_mem hE (hUE hu))

private theorem r10h7_apply_kfact {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) (hK1 : KFactRankTwoUniqueness) {H E U : Subgroup G}
    (hHK : CFSG.IsKGroup H) (hrank : CFSG.Open.pRank 3 H = 2) (hHM : ¬ H ≤ M) (hEM : E ≤ M)
    (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hUE : U ≤ E) (hU : IsElemAbelian 3 U)
    (hU9 : Nat.card U = 9) (hBH : zpowers x ⊔ zpowers z ≤ H) (hUH : U ≤ H)
    (hQ₀ : IsPGroup 3 ↥(zpowers x ⊔ zpowers z ⊔ U)) {W : Subgroup G} (hWH : W ≤ H)
    (hWn : zpowers x ⊔ zpowers z ⊔ U ≤ normalizer (W : Set G))
    (hW6 : Nat.Coprime (Nat.card W) 6) : W ≤ rankThreePrimeCore 3 H := by
  have hpl := SmallRankPlane.of_situation h.setting h.situation h.point h.central
  obtain ⟨Q, hQ₀Q, hQH, hQ3, hQidx⟩ :=
    exists_sylow_le_of_isPGroup Nat.prime_three (sup_le hBH hUH) hQ₀
  have hBQ : zpowers x ⊔ zpowers z ≤ Q := le_sup_left.trans hQ₀Q
  have hUQ : U ≤ Q := le_sup_right.trans hQ₀Q
  have hQM : Q ≤ M := le_of_isPGroup_of_plane_le h hQ3 hBQ
  have hB9 : Nat.card (zpowers x ⊔ zpowers z : Subgroup G) = 9 := by
    rw [hpl.card_eq]
    norm_num
  have hBU : zpowers x ⊔ zpowers z ≠ U := by
    intro hBU
    have := r10h7_conj_not_mem h hE hE27 hUE 1
    rw [one_mul, inv_one, mul_one] at this
    exact this (hBU ▸ mem_sup_left (mem_zpowers x))
  have hcyc : IsCyclic (center Q) :=
    r10h7_isCyclic_center hQ3 hBQ hUQ hB9 hU hU9 hpl.mem_of_mem_centralizer hBU
  refine hK1 G H Q (zpowers x ⊔ zpowers z) U hHK hrank hQH hQ3 hQidx hcyc hBQ hpl.isElemAbelian
    hB9 hUQ hU hU9 (fun g _ => r10h7_not_conj h hE hE27 hUE g) ?_ ?_ W hWH hWn hW6
  · intro w _ hw3 hwc g _ hg
    exact r10h7_weakly_closed h hBQ hUQ hE hE27 hUE hU hU9 hw3 hwc hg
  · refine ⟨H ⊓ M, inf_le_left, fun heq => hHM (inf_eq_left.1 heq), ?_, ?_⟩
    · intro S hSU hS1 g hg
      exact ⟨hg.2, r10h7_normalizer_le_of_le_U h hEM hE hE27 hUE hU hU9 hSU hS1 hg.1⟩
    · intro S hSQ hS2 g hg
      exact ⟨hg.2, normalizer_le_of_le_of_two_le_pRank h.setting h.u0 h.situation.mem_sigmaA
        h.situation.isCoreMaxLocal (hQ3.to_le hSQ) (hSQ.trans hQM) hS2 hg.1⟩

omit [Finite G] in
private theorem r10h7_normalizer_ne_top [IsSimpleGroup G] {F Fs : Subgroup G} (hF1 : F ≠ ⊥)
    (hFFs : F < Fs) : normalizer (F : Set G) ≠ ⊤ := by
  intro htop
  have : F.Normal := normalizer_eq_top_iff.1 htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal F with hb | ht
  · exact hF1 hb
  · rw [ht] at hFFs
    exact not_top_lt hFFs

private theorem r10h7_coprime_six {f : ℕ} (hf : f.Prime) (hf5 : 5 ≤ f) : Nat.Coprime f 6 := by
  rw [Nat.Prime.coprime_iff_not_dvd hf]
  intro hd
  have := Nat.le_of_dvd (by norm_num) hd
  interval_cases f
  · norm_num at hd
  · exact absurd hf (by norm_num)

private theorem r10h7_exists_plane_in_centre {E C : Subgroup G} (hE : IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hCE : C ≤ E) (hC3 : C.relIndex E ≤ 3) :
    ∃ U : Subgroup G, U ≤ C ∧ IsElemAbelian 3 U ∧ Nat.card U = 9 := by
  have hcard : C.relIndex E * Nat.card C = 27 := by
    have h1 := Subgroup.relIndex_mul_card (H := C) (K := E)
    rw [inf_eq_left.2 hCE, hE27] at h1
    exact h1
  have h9 : 9 ≤ Nat.card C := by
    have h3 : C.relIndex E * Nat.card C ≤ 3 * Nat.card C := Nat.mul_le_mul_right _ hC3
    omega
  have hdvd : Nat.card C ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num]
    exact Dvd.intro_left _ hcard
  obtain ⟨i, -, hCi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hi2 : 2 ≤ i := by
    by_contra hlt
    have hlt' : 3 ^ i < 3 ^ 2 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [← hCi] at hlt'
    norm_num at hlt'
    omega
  have hCel : IsElemAbelian 3 C := CFSG.Open.IsElemAbelian.mono hE hCE
  have h2 : 2 ≤ CFSG.Open.pRank 3 C :=
    le_trans hi2 (le_pRank_of_isElemAbelian Nat.prime_three le_rfl hCel hCi)
  obtain ⟨U, hUC, hU, hU9⟩ := exists_isElemAbelian_of_le_pRank Nat.prime_three h2
  exact ⟨U, hUC, hU, by rw [hU9]; norm_num⟩

theorem rank_two_enlarge {P : Sylow 3 G} {M : Subgroup G} {x z : G} (h : Setup65A G P M x z)
    (hK1 : KFactRankTwoUniqueness) {f : ℕ} (hf : f.Prime) (hf5 : 5 ≤ f) {F Fs R : Subgroup G}
    (hF : IsPGroup f F) (hF1 : F ≠ ⊥) (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G))
    (hHM : ¬ normalizer (F : Set G) ≤ M) (hFs : IsPGroup f Fs)
    (hFsD : Fs ≤ rankThreePrimeCore 3 M)
    (hsyl : ¬ f ∣ (Fs.subgroupOf (rankThreePrimeCore 3 M)).index)
    (hBFs : zpowers x ⊔ zpowers z ≤ normalizer (Fs : Set G)) (hFFs : F < Fs)
    (hR3 : IsPGroup 3 R) (hRM : R ≤ M) (hBR : zpowers x ⊔ zpowers z ≤ R)
    (hRFs : R ≤ normalizer (Fs : Set G)) (hRrank : CFSG.Open.pRank 3 R = 3)
    (hrank : CFSG.Open.pRank 3 (normalizer (F : Set G)) = 2) :
    ∃ E : Subgroup G, F < E ∧ IsPGroup f E ∧ zpowers x ⊔ zpowers z ≤ normalizer (E : Set G) ∧
      E ≤ rankThreePrimeCore 3 (normalizer (F : Set G)) ∧
      rankThreePrimeCore 3 (normalizer (F : Set G)) ≤ M := by
  classical
  have : IsSimpleGroup G := h.setting.simple
  have : Fact f.Prime := ⟨hf⟩
  obtain ⟨E, hER, hE, hEc⟩ :=
    exists_isElemAbelian_of_le_pRank Nat.prime_three (k := 3) (le_of_eq hRrank.symm)
  have hE27 : Nat.card E = 27 := by rw [hEc]; norm_num
  have hFsM : Fs ≤ M := hFsD.trans (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 M).1
  have hrk : CFSG.Open.pRank f Fs ≤ 2 :=
    (pRank_mono f hf.one_lt hFsM).trans (pRank_le_two_of_situation h.setting h.situation hf hf5)
  have hYF : M ⊓ normalizer (Fs : Set G) ≤ normalizer (Fs : Set G) := inf_le_right
  have hY := no_normal_index_three_normalizer h hf hFsD hFs hsyl
  have hEY : E ≤ M ⊓ normalizer (Fs : Set G) := le_inf (hER.trans hRM) (hER.trans hRFs)
  have hC3 : (E ⊓ centralizer (Fs : Set G)).relIndex E ≤ 3 :=
    cyc_relIndex_le_three hf (by omega) (by omega) hFs hrk hYF hY hEY hE
  obtain ⟨U, hUC, hU, hU9⟩ :=
    r10h7_exists_plane_in_centre hE hE27 (inf_le_left : E ⊓ centralizer (Fs : Set G) ≤ E) hC3
  have hUE : U ≤ E := hUC.trans inf_le_left
  have hUCf : U ≤ centralizer (Fs : Set G) := hUC.trans inf_le_right
  obtain ⟨y, hyFs, hyN, hyF⟩ := exists_mem_normalizer_not_mem_of_lt hFs hFFs
  have hEF : F < Fs ⊓ normalizer (F : Set G) := by
    rw [IsConcreteLE.lt_iff_le_and_exists]
    exact ⟨le_inf hFFs.le le_normalizer, y, ⟨hyFs, hyN⟩, hyF⟩
  have hE'p : IsPGroup f ↥(Fs ⊓ normalizer (F : Set G)) := hFs.to_le inf_le_left
  have hBN : zpowers x ⊔ zpowers z ≤
      normalizer ((Fs ⊓ normalizer (F : Set G) : Subgroup G) : Set G) :=
    (le_inf hBFs (hBF.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hUN : U ≤ normalizer ((Fs ⊓ normalizer (F : Set G) : Subgroup G) : Set G) :=
    hUCf.trans ((centralizer_le (SetLike.coe_subset_coe.2 inf_le_left)).trans
      (centralizer_le_normalizer _))
  have hUH : U ≤ normalizer (F : Set G) :=
    hUCf.trans ((centralizer_le (SetLike.coe_subset_coe.2 hFFs.le)).trans
      (centralizer_le_normalizer _))
  have hHK : CFSG.IsKGroup (normalizer (F : Set G)) :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_isKGroup
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 h.setting.kProper) _
      (r10h7_normalizer_ne_top hF1 hFFs)
  have hcop : Nat.Coprime (Nat.card ↥(Fs ⊓ normalizer (F : Set G))) 6 := by
    obtain ⟨n, hn⟩ := hE'p.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n (r10h7_coprime_six hf hf5)
  have hW := r10h7_apply_kfact h hK1 hHK hrank hHM (hER.trans hRM) hE hE27 hUE hU hU9 hBF hUH
    (hR3.to_le (sup_le hBR (hUE.trans hER))) inf_le_right (sup_le hBN hUN) hcop
  refine ⟨Fs ⊓ normalizer (F : Set G), hEF, hE'p, hBN, hW, ?_⟩
  obtain ⟨-, hHO, hOc⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 (normalizer (F : Set G))
  exact le_of_plane_centralizers_le hU hU9 (hUH.trans hHO)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hOc)
    fun u hu hu1 => r10h7_centralizer_le h (hER.trans hRM) hE hE27 hUE hU hu hu1

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
