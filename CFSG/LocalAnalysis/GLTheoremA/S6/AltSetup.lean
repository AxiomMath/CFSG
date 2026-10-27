module

public import CFSG.LocalAnalysis.GLTheoremA.S6.AltAux
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltFix
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Assembly
import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ}

structure AltCommon (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (n : ℕ) : Prop where
  alt : IsAltPType p L n
  three_mul_le : 3 * p ≤ n
  seven_lt : 7 < n
  B_eq : IsDirectZpowersInf B x L
  rank_L : CFSG.Open.pRank p L = n / p
  rank_B : CFSG.Open.pRank p B ≤ n / p + 1

theorem AltSetup.toCommon {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (S : AltSetup p B x L n y J) : AltCommon p B x L n :=
  ⟨S.alt, S.three_mul_le, S.seven_lt, S.B_eq, S.rank_L, S.rank_B⟩

theorem altDxy_eq_closure (x y : G) : altDxy x y = Subgroup.closure {x, y} := by
  unfold altDxy
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
    Set.singleton_union]

theorem mem_centralizer_altDxy_iff {x y g : G} :
    g ∈ Subgroup.centralizer (altDxy x y : Set G) ↔ g * x = x * g ∧ g * y = y * g := by
  rw [altDxy_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨(h x (by simp)).symm, (h y (by simp)).symm⟩
  · rintro ⟨h1, h2⟩ z hz
    rcases hz with rfl | rfl
    · exact h1.symm
    · exact h2.symm

theorem inf_centralizer_altDxy_eq {x y : G} {L : Subgroup G}
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) :
    L ⊓ Subgroup.centralizer (altDxy x y : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_centralizer_altDxy_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hg, -, h2⟩
    exact ⟨hg, fun h hh => by rw [Set.mem_singleton_iff] at hh; subst hh; exact h2.symm⟩
  · rintro ⟨hg, h2⟩
    have h1 := (Subgroup.mem_centralizer_iff.1 (hxL hg)) x rfl
    exact ⟨hg, h1.symm, (h2 y rfl).symm⟩

theorem le_pRank_of_card_altSetup {Y : Type} [Group Y] [Finite Y] (hp : 1 < p) {H E : Subgroup Y}
    (hEH : E ≤ H) (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card ↥E = p ^ k) : k ≤ CFSG.Open.pRank p H := by
  refine le_csSup ⟨Nat.card Y, ?_⟩ ⟨E, hEH, hE, hk⟩
  rintro r ⟨B, -, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card ↥B := hB.symm
    _ ≤ Nat.card Y := Subgroup.card_le_card_group B

theorem pRank_eq_of_isElemAbelian_altSetup {Y : Type} [Group Y] [Finite Y] (hp : 1 < p)
    {B : Subgroup Y} (hB : IsElemAbelian p B) {k : ℕ} (hk : Nat.card ↥B = p ^ k) :
    CFSG.Open.pRank p B = k := by
  refine le_antisymm ?_ (le_pRank_of_card_altSetup hp le_rfl hB hk)
  refine csSup_le ⟨k, B, le_rfl, hB, hk⟩ ?_
  rintro j ⟨E, hEB, -, hj⟩
  have hdvd : p ^ j ∣ p ^ k := by
    rw [← hj, ← hk]
    exact Subgroup.card_dvd_of_le hEB
  exact (Nat.pow_dvd_pow_iff_le_right hp).1 hdvd

theorem exists_alt_of_catalogIs {S : Type} [Group S] (h : catalogIs S isAltIndex) :
    ∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* ↥(alternatingGroup (Fin n))) := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | alternating m hm => exact ⟨m, hm, ⟨f⟩⟩
  | cyclic _ _ => exact absurd hi (by simp [isAltIndex])
  | lie _ => exact absurd hi (by simp [isAltIndex])
  | sporadic _ => exact absurd hi (by simp [isAltIndex])

theorem exists_pCycle (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hpn : p ≤ n) :
    ∃ σ : ↥(alternatingGroup (Fin n)),
      ((σ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)).cycleType = {p} := by
  classical
  obtain ⟨g, hg⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin n)).mpr
    (show ({p} : Multiset ℕ).sum ≤ Fintype.card (Fin n) ∧ ∀ a ∈ ({p} : Multiset ℕ), 2 ≤ a from
      ⟨by simpa using hpn, fun a ha => by rw [Multiset.mem_singleton.1 ha]; exact hp.two_le⟩)
  refine ⟨⟨g, ?_⟩, hg⟩
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType, hg]
  have hodd : Even (p + 1) := (hp.odd_of_ne_two hp2).add_one
  simpa [Multiset.sum_singleton] using hodd.neg_one_pow

theorem center_pQuot_eq_bot_of_alt (hp : p.Prime) (hp2 : p ≠ 2) {X L : Subgroup G}
    (hL : GLAPComponent p X L) {n : ℕ} (hn : 8 ≤ n)
    (f : PSimple p L ≃* ↥(alternatingGroup (Fin n))) : Subgroup.center (PQuot p L) = ⊥ := by
  haveI : Group.IsPerfect (PQuot p L) :=
    CFSG.HardMathSupport.Timmesfeld.Balance.Alt.isPerfect_barOf hL
  exact CFSG.HardMathSupport.Timmesfeld.Balance.Alt.center_eq_bot_of_odd hn f
    (CFSG.HardMathSupport.Timmesfeld.Balance.Alt.odd_card_center_barOf hp hp2 L)

theorem card_autBar_mul (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) : Nat.card ↥(autBar p B L) * p = Nat.card ↥B := by
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := IsSStarMax.normalizes h
  have hCME : CentModEqZpowers p B L x := (IsSStarMax.inT hc h).2.2.2.2.2
  have hxB : x ∈ B := (IsSStarMax.essential h).1
  have hxo : orderOf x = p := by
    haveI : Fact p.Prime := ⟨hc.prime⟩
    exact orderOf_eq_prime ((IsSStarMax.bmax h).1.2 x hxB) (IsSStarMax.essential h).2.1
  let φ : ↥B →* MulAut (barOf p L) := (barAut p L).comp (Subgroup.inclusion hBN)
  have hrange : φ.range = autBar p B L := by
    unfold autBar
    rw [inf_eq_left.2 hBN, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : Nat.card ↥φ.ker = p := by
    have h1 : φ.ker.map B.subtype = Subgroup.zpowers x := by
      ext b
      constructor
      · rintro ⟨b', hb', rfl⟩
        have hb'' : barAut p L (Subgroup.inclusion hBN b') = 1 := hb'
        exact (hCME b' b'.2).1 ((chev_barAut_eq_one_iff_centMod (hBN b'.2)).1 hb'')
      · intro hb
        have hbB : b ∈ B := (Subgroup.zpowers_le.2 hxB) hb
        refine ⟨⟨b, hbB⟩, ?_, rfl⟩
        show barAut p L (Subgroup.inclusion hBN ⟨b, hbB⟩) = 1
        exact (chev_barAut_eq_one_iff_centMod (hBN hbB)).2 ((hCME b hbB).2 hb)
    rw [← Subgroup.card_map_of_injective B.subtype_injective, h1, Nat.card_zpowers, hxo]
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hker] at h2
  exact h2.symm

theorem three_mul_le_of_alt (hc : S6Ctx G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : IsSStarMax p B x L) {n : ℕ} (hn : 5 ≤ n)
    (f : PSimple p L ≃* ↥(alternatingGroup (Fin n))) : 3 * p ≤ n := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  haveI : Group.IsPerfect (PQuot p L) :=
    CFSG.HardMathSupport.Timmesfeld.Balance.Alt.isPerfect_barOf (IsSStarMax.component h)
  have hcard := card_autBar_mul hc h
  have hel : IsElemAbelian p (autBar p B L) :=
    CFSG.HardMathSupport.Timmesfeld.Balance.Alt.isElemAbelian_autBar (IsSStarMax.bmax h).1 L
  have h4 := pow_four_le_card_of_bmax hc (IsSStarMax.bmax h)
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hc.prime hel
  have hk3 : 3 ≤ k := by
    have h1 : p ^ 4 ≤ p ^ (k + 1) := by
      calc p ^ 4 ≤ Nat.card ↥B := h4
        _ = Nat.card ↥(autBar p B L) * p := hcard.symm
        _ = p ^ (k + 1) := by rw [hk, pow_succ]
    have := (Nat.pow_le_pow_iff_right hc.prime.one_lt).1 h1
    omega
  have hrk : k ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PQuot p L))) :=
    le_pRank_of_card_altSetup hc.prime.one_lt le_top hel hk
  have hup := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_aut_le (L := PQuot p L) hn f
    hc.prime hc.odd
  have h3 : 3 ≤ n / p := hk3.trans (hrk.trans hup)
  exact (Nat.le_div_iff_mul_le hc.prime.pos).1 h3

theorem pRank_eq_pRank_pQuot (hp : p.Prime) (L : Subgroup G) :
    CFSG.Open.pRank p L = CFSG.Open.pRank p (⊤ : Subgroup (PQuot p L)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 := CFSG.SectionRank.pRank_quotient_eq (G := ↥L) (p := p) (GLAPPrimeCore p ↥L)
    ((Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_card_gLAPPrimeCore_aux p ↥L))
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
  exact h1.symm

theorem pRank_eq_div_of_alt (hc : S6Ctx G p) {L : Subgroup G} {n : ℕ}
    (e : PQuot p L ≃* ↥(alternatingGroup (Fin n))) : CFSG.Open.pRank p L = n / p := by
  rw [pRank_eq_pRank_pQuot hc.prime L, CFSG.SectionRank.pRank_top_eq_of_mulEquiv hc.prime.one_lt e,
    (CFSG.Quasithin.H13.A7.section_rank_alternating_odd_prime_rank).1 n p hc.prime hc.odd]

theorem mem_glaPPrimeCoreOf_of_centMod {L : Subgroup G} (hZ : Subgroup.center (PQuot p L) = ⊥)
    {g : G} (hgL : g ∈ L) (hcm : CentMod p L g) : g ∈ GLAPPrimeCoreOf p L := by
  have ha : g ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hgL
  have h1 : barAut p L ⟨g, ha⟩ = 1 := (chev_barAut_eq_one_iff_centMod ha).2 hcm
  have hcen : (QuotientGroup.mk (⟨g, hgL⟩ : ↥L) : PQuot p L) ∈ Subgroup.center (PQuot p L) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨k, rfl⟩ := pQuotHom_surjective p L z
    have h2 := congrArg (fun φ : MulAut (PQuot p L) => φ (pQuotHom p L k)) h1
    simp only [MulAut.one_apply] at h2
    rw [barAut_pQuotHom] at h2
    have e1 : L.normalizerMonoidHom ⟨g, ha⟩ k = ⟨g, hgL⟩ * k * ⟨g, hgL⟩⁻¹ := Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [hZ, Subgroup.mem_bot] at hcen
  exact (chev_mem_glaPPrimeCoreOf_iff hgL).2 ((QuotientGroup.eq_one_iff _).1 hcen)

theorem barAut_eq_conj_of_mem {L : Subgroup G} {l : G} (hl : l ∈ L) :
    barAut p L ⟨l, Subgroup.le_normalizer hl⟩ =
      MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : PQuot p L) := by
  ext z
  obtain ⟨k, rfl⟩ := pQuotHom_surjective p L z
  rw [barAut_pQuotHom, MulAut.conj_apply]
  have e1 : L.normalizerMonoidHom ⟨l, Subgroup.le_normalizer hl⟩ k = ⟨l, hl⟩ * k * ⟨l, hl⟩⁻¹ :=
    Subtype.ext rfl
  rw [e1, map_mul, map_mul, map_inv]
  rfl

theorem exists_inner_decomp (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) {n : ℕ} (hn : 5 ≤ n)
    (e : PQuot p L ≃* ↥(alternatingGroup (Fin n))) :
    ∀ b ∈ B, ∃ l ∈ L, CentMod p L (b * l⁻¹) := by
  intro b hb
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := IsSStarMax.normalizes h hb
  have hbp : b ^ p = 1 := (IsSStarMax.bmax h).1.2 b hb
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (PQuot p L), α = barAut p L ⟨b, hbN⟩ := ⟨_, rfl⟩
  have hα : α ^ p = 1 := by
    have h1 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 := Subtype.ext hbp
    rw [hαdef, ← map_pow, h1, map_one]
  have hβ : (MulAut.congr e α) ^ p = 1 := by rw [← map_pow, hα, map_one]
  by_cases hβ1 : MulAut.congr e α = 1
  · have hα1 : α = 1 := (MulAut.congr e).injective (by rw [hβ1, map_one])
    refine ⟨1, L.one_mem, ?_⟩
    rw [inv_one, mul_one]
    exact (chev_barAut_eq_one_iff_centMod hbN).1 (by rw [← hαdef]; exact hα1)
  · obtain ⟨xb, -, -, hxb⟩ := AltDown.exists_conj_of_alt hn hc.prime hc.odd hβ hβ1
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e.symm xb)
    have hαconj : α = MulAut.conj (QuotientGroup.mk l : PQuot p L) := by
      ext z
      have h1 := DFunLike.congr_fun hxb (e z)
      rw [MulAut.conj_apply]
      have h2 : e (α z) = xb * e z * xb⁻¹ := by
        have : (MulAut.congr e α) (e z) = e (α z) := by simp [MulAut.congr_apply]
        rw [← this, h1, MulAut.conj_apply]
      rw [hl]
      apply e.injective
      rw [h2, map_mul, map_mul, map_inv]
      simp
    refine ⟨l, l.2, ?_⟩
    have hmem : b * (l : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ hbN (Subgroup.inv_mem _ (Subgroup.le_normalizer l.2))
    refine (chev_barAut_eq_one_iff_centMod hmem).1 ?_
    have e1 : (⟨b * (l : G)⁻¹, hmem⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨b, hbN⟩ * ⟨(l : G)⁻¹, Subgroup.le_normalizer (L.inv_mem l.2)⟩ := rfl
    rw [e1, map_mul, ← hαdef, barAut_eq_conj_of_mem (L.inv_mem l.2), hαconj]
    have e2 : (⟨(l : G)⁻¹, L.inv_mem l.2⟩ : ↥L) = l⁻¹ := rfl
    rw [e2]
    simp

theorem card_mul_inf_eq_of_sup_eq {A B L : Subgroup G} (hA : A ≤ Subgroup.normalizer (L : Set G))
    (hB : B ≤ Subgroup.normalizer (L : Set G)) (h : A ⊔ L = B ⊔ L) :
    Nat.card ↥A * Nat.card ↥(B ⊓ L : Subgroup G) = Nat.card ↥B * Nat.card ↥(A ⊓ L : Subgroup G) := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer hA
  have h2 := card_sup_mul_card_inf_of_le_normalizer hB
  rw [sup_comm L A, h, inf_comm L A] at h1
  rw [sup_comm L B, inf_comm L B] at h2
  have hU : 0 < Nat.card ↥(B ⊔ L : Subgroup G) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hU
  calc Nat.card ↥(B ⊔ L : Subgroup G) * (Nat.card ↥A * Nat.card ↥(B ⊓ L : Subgroup G))
      = Nat.card ↥A * (Nat.card ↥(B ⊔ L : Subgroup G) * Nat.card ↥(B ⊓ L : Subgroup G)) := by ring
    _ = Nat.card ↥A * (Nat.card ↥L * Nat.card ↥B) := by rw [h2]
    _ = Nat.card ↥B * (Nat.card ↥L * Nat.card ↥A) := by ring
    _ = Nat.card ↥B * (Nat.card ↥(B ⊔ L : Subgroup G) * Nat.card ↥(A ⊓ L : Subgroup G)) := by
      rw [← h1]
    _ = Nat.card ↥(B ⊔ L : Subgroup G) * (Nat.card ↥B * Nat.card ↥(A ⊓ L : Subgroup G)) := by ring

theorem exists_pSubgroup_centMod (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) (hZ : Subgroup.center (PQuot p L) = ⊥)
    (hdec : ∀ b ∈ B, ∃ l ∈ L, CentMod p L (b * l⁻¹)) :
    ∃ S : Subgroup G, IsPGroup p S ∧ (∀ g ∈ S, CentMod p L g) ∧ S ≤ B ⊔ L ∧ S ⊓ L = ⊥ ∧
      Nat.card ↥S * Nat.card ↥(B ⊓ L : Subgroup G) = Nat.card ↥B := by
  classical
  haveI : Fact p.Prime := ⟨hc.prime⟩
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := IsSStarMax.normalizes h
  have hBel : IsElemAbelian p B := (IsSStarMax.bmax h).1
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup G, Y = centModSubgroup p L ⊓ (B ⊔ L) := ⟨_, rfl⟩
  have hYC : ∀ g ∈ Y, CentMod p L g := fun g hg => centMod_iff.2 (hYdef ▸ hg).1
  have hYBL : Y ≤ B ⊔ L := hYdef ▸ inf_le_right
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := fun g hg => (hYC g hg).1
  have hYL : Y ⊔ L = B ⊔ L := by
    refine le_antisymm (sup_le hYBL le_sup_right) (sup_le ?_ le_sup_right)
    intro b hb
    obtain ⟨l, hl, hcm⟩ := hdec b hb
    have hmem : b * l⁻¹ ∈ Y := by
      rw [hYdef]
      exact ⟨centMod_iff.1 hcm,
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right (L.inv_mem hl))⟩
    have : b = (b * l⁻¹) * l := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hl)
  have hcard := card_mul_inf_eq_of_sup_eq hYN hBN hYL
  have hYLO : (Y ⊓ L : Subgroup G) ≤ GLAPPrimeCoreOf p L := fun g hg =>
    mem_glaPPrimeCoreOf_of_centMod hZ hg.2 (hYC g hg.1)
  have hYLnd : ¬ p ∣ Nat.card ↥(Y ⊓ L : Subgroup G) := fun hd =>
    not_dvd_card_glaPPrimeCoreOf hc.prime L (hd.trans (Subgroup.card_dvd_of_le hYLO))
  obtain ⟨a, ha⟩ := exists_card_eq_pow_of_isElemAbelian hc.prime hBel
  obtain ⟨c, hcc⟩ := exists_card_eq_pow_of_isElemAbelian hc.prime
    (isElemAbelian_mono hBel (inf_le_left : B ⊓ L ≤ B))
  have hfac : (Nat.card ↥Y).factorization p + c = a := by
    rw [ha, hcc] at hcard
    have h1 : (Nat.card ↥Y * p ^ c).factorization p =
        (p ^ a * Nat.card ↥(Y ⊓ L : Subgroup G)).factorization p := by rw [hcard]
    rw [Nat.factorization_mul Nat.card_pos.ne' (pow_ne_zero _ hc.prime.ne_zero),
      Nat.factorization_mul (pow_ne_zero _ hc.prime.ne_zero) Nat.card_pos.ne', Finsupp.add_apply,
      Finsupp.add_apply, Nat.Prime.factorization_pow hc.prime, Nat.Prime.factorization_pow hc.prime,
      Finsupp.single_eq_same, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hYLnd] at h1
    omega
  obtain ⟨S⟩ : Nonempty (Sylow p ↥Y) := inferInstance
  have hScard : Nat.card ↥S = p ^ (Nat.card ↥Y).factorization p := Sylow.card_eq_multiplicity S
  have hS'card : Nat.card ↥((S : Subgroup ↥Y).map Y.subtype) = p ^ (Nat.card ↥Y).factorization p := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact hScard
  have hS'p : IsPGroup p ↥((S : Subgroup ↥Y).map Y.subtype) := IsPGroup.of_card hS'card
  have hS'Y : (S : Subgroup ↥Y).map Y.subtype ≤ Y := Subgroup.map_subtype_le _
  refine ⟨(S : Subgroup ↥Y).map Y.subtype, hS'p, fun g hg => hYC g (hS'Y hg), hS'Y.trans hYBL, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hgO : g ∈ GLAPPrimeCoreOf p L := hYLO ⟨hS'Y hg.1, hg.2⟩
    have hd1 : orderOf g ∣ Nat.card ↥(GLAPPrimeCoreOf p L) := Subgroup.orderOf_dvd_natCard _ hgO
    have hd2 : orderOf g ∣ p ^ (Nat.card ↥Y).factorization p := by
      rw [← hS'card]
      exact Subgroup.orderOf_dvd_natCard _ hg.1
    have hcop : Nat.Coprime (p ^ (Nat.card ↥Y).factorization p) (Nat.card ↥(GLAPPrimeCoreOf p L)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hc.prime).2
        (not_dvd_card_glaPPrimeCoreOf hc.prime L))
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd2 hd1)
  · rw [hS'card, hcc, ha, ← pow_add, hfac]

theorem card_le_of_cyclic_complement (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) {S : Subgroup G} (hS : S ≤ B ⊔ L) (hSL : S ⊓ L = ⊥)
    (hcyc : IsCyclic S) : Nat.card ↥S ≤ p := by
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := IsSStarMax.normalizes h
  obtain ⟨s, hs⟩ := hcyc.exists_generator
  obtain ⟨b, hb, l, hl, hsbl⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN (hS s.2)
  have hpow : ∀ k : ℕ, ∃ l' ∈ L, ((b * l) ^ k : G) = b ^ k * l' := by
    intro k
    induction k with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨l', hl', hk⟩ := ih
      refine ⟨b⁻¹ * l' * b * l, L.mul_mem ?_ hl, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (hBN (B.inv_mem hb)) l').1 hl'
        simpa using this
      · rw [pow_succ, hk, pow_succ]; group
  obtain ⟨l', hl', hk⟩ := hpow p
  have hbp : b ^ p = 1 := (IsSStarMax.bmax h).1.2 b hb
  have hsp : (s : G) ^ p = l' := by
    rw [hsbl, hk, hbp, one_mul]
  have hspS : (s : G) ^ p ∈ S := S.pow_mem s.2 p
  have hsp1 : (s : G) ^ p = 1 := by
    have : (s : G) ^ p ∈ S ⊓ L := ⟨hspS, hsp ▸ hl'⟩
    rw [hSL] at this
    exact Subgroup.mem_bot.1 this
  have hsp1' : s ^ p = 1 := Subtype.ext hsp1
  rw [← orderOf_eq_card_of_forall_mem_zpowers hs]
  exact Nat.le_of_dvd hc.prime.pos (orderOf_dvd_of_pow_eq_one hsp1')

theorem card_le_mul_of_decomp (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) (hZ : Subgroup.center (PQuot p L) = ⊥)
    (hdec : ∀ b ∈ B, ∃ l ∈ L, CentMod p L (b * l⁻¹)) :
    Nat.card ↥B ≤ p * Nat.card ↥(B ⊓ L : Subgroup G) := by
  obtain ⟨S, hSp, hSC, hSBL, hSL, hcard⟩ := exists_pSubgroup_centMod hc h hZ hdec
  have hcyc : IsCyclic S := (IsSStarMax.cycMod h) S hSC hSp
  have hle := card_le_of_cyclic_complement hc h hSBL hSL hcyc
  calc Nat.card ↥B = Nat.card ↥S * Nat.card ↥(B ⊓ L : Subgroup G) := hcard.symm
    _ ≤ p * Nat.card ↥(B ⊓ L : Subgroup G) := Nat.mul_le_mul_right _ hle

theorem zpowers_inf_eq_bot (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) (hZ : Subgroup.center (PQuot p L) = ⊥) :
    Subgroup.zpowers x ⊓ L = ⊥ := by
  have hCME : CentModEqZpowers p B L x := (IsSStarMax.inT hc h).2.2.2.2.2
  have hxB : x ∈ B := (IsSStarMax.essential h).1
  have hBel : IsElemAbelian p B := (IsSStarMax.bmax h).1
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hgB : g ∈ B := (Subgroup.zpowers_le.2 hxB) hg.1
  have hgO : g ∈ GLAPPrimeCoreOf p L :=
    mem_glaPPrimeCoreOf_of_centMod hZ hg.2 ((hCME g hgB).2 hg.1)
  have hdvd : orderOf g ∣ Nat.card ↥(GLAPPrimeCoreOf p L) := Subgroup.orderOf_dvd_natCard _ hgO
  have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p L)) :=
    (Nat.Prime.coprime_iff_not_dvd hc.prime).2 (not_dvd_card_glaPPrimeCoreOf hc.prime L)
  have h3 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hBel.2 g hgB)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h3 hdvd)

theorem isDirectZpowersInf_of_decomp (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) (hZ : Subgroup.center (PQuot p L) = ⊥)
    (hdec : ∀ b ∈ B, ∃ l ∈ L, CentMod p L (b * l⁻¹)) : IsDirectZpowersInf B x L := by
  have hxB : x ∈ B := (IsSStarMax.essential h).1
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component h).1
  have hxo : orderOf x = p := by
    haveI : Fact p.Prime := ⟨hc.prime⟩
    exact orderOf_eq_prime ((IsSStarMax.bmax h).1.2 x hxB) (IsSStarMax.essential h).2.1
  have hinf : Subgroup.zpowers x ⊓ (B ⊓ L) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ Subgroup.zpowers x ⊓ L := ⟨hg.1, hg.2.2⟩
    rwa [zpowers_inf_eq_bot hc h hZ] at this
  refine ⟨?_, hinf⟩
  have hle : Subgroup.zpowers x ⊔ (B ⊓ L) ≤ B :=
    sup_le (Subgroup.zpowers_le.2 hxB) inf_le_left
  have hN : B ⊓ L ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro g hg
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hxL hg.2
  have h1 := card_sup_mul_card_inf_of_le_normalizer hN
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hxo, mul_one] at h1
  have h2 := card_le_mul_of_decomp hc h hZ hdec
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h1]; exact h2)).symm

theorem card_eq_mul_of_isDirectZpowersInf (hc : S6Ctx G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : IsSStarMax p B x L) (hdir : IsDirectZpowersInf B x L) :
    Nat.card ↥B = p * Nat.card ↥(B ⊓ L : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  have hBel : IsElemAbelian p B := (IsSStarMax.bmax h).1
  have hxB : x ∈ B := (IsSStarMax.essential h).1
  have hx1 : x ≠ 1 := (IsSStarMax.essential h).2.1
  have hxo : orderOf x = p := orderOf_eq_prime (hBel.2 x hxB) hx1
  have hzB : Subgroup.zpowers x ≤ B := (Subgroup.zpowers_le).2 hxB
  have hN : (B ⊓ L : Subgroup G) ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    fun g hg => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd =>
      isElemAbelian_commute hBel (hzB hd) hg.1)
  have h1 := card_sup_mul_card_inf_of_le_normalizer hN
  rw [← hdir.1, hdir.2, Subgroup.card_bot, Nat.card_zpowers, hxo] at h1
  simpa using h1

theorem pRank_le_of_isDirectZpowersInf (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) (hdir : IsDirectZpowersInf B x L) :
    CFSG.Open.pRank p B ≤ CFSG.Open.pRank p L + 1 := by
  have hBel : IsElemAbelian p B := (IsSStarMax.bmax h).1
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian hc.prime hBel
  have hrk : CFSG.Open.pRank p B = m := pRank_eq_of_isElemAbelian_altSetup hc.prime.one_lt hBel hm
  have hmul := card_eq_mul_of_isDirectZpowersInf hc h hdir
  have hBLel : IsElemAbelian p (B ⊓ L : Subgroup G) := isElemAbelian_mono hBel inf_le_left
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hc.prime hBLel
  have hkL : k ≤ CFSG.Open.pRank p L :=
    le_pRank_of_card_altSetup hc.prime.one_lt inf_le_right hBLel hk
  have hmk : m = k + 1 := by
    rw [hm, hk, ← pow_succ'] at hmul
    exact Nat.pow_right_injective hc.prime.two_le hmul
  omega

theorem exists_cycle_lift (hp : p.Prime) {L : Subgroup G} {n : ℕ}
    (e : PQuot p L ≃* ↥(alternatingGroup (Fin n))) (σ : ↥(alternatingGroup (Fin n)))
    (hσ : ((σ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)).cycleType = {p}) :
    ∃ y : G, y ∈ L ∧ orderOf y = p ∧
      permOfMod p L n e y = ((σ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (e.symm σ)
  have hσp : σ ^ p = 1 := Subtype.ext (by simpa using pow_eq_one_of_cycleType_eq hσ)
  have hσ1 : σ ≠ 1 := by
    intro h
    have := hσ
    rw [h] at this
    simp at this
  have hbar : (QuotientGroup.mk y₀ : PQuot p L) ^ p = 1 := by
    rw [hy₀, ← map_pow, hσp, map_one]
  have hy₀O : y₀ ^ p ∈ GLAPPrimeCore p ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hbar
  have hy₀pm : y₀ ^ (p * Nat.card ↥(GLAPPrimeCore p ↥L)) = 1 := by
    rw [pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hy₀O)
  have hcop : Nat.Coprime (Nat.card ↥(GLAPPrimeCore p ↥L)) p :=
    (coprime_card_gLAPPrimeCore_aux p ↥L).symm
  obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  set y₁ : ↥L := y₀ ^ (Nat.card ↥(GLAPPrimeCore p ↥L) * m') with hy₁
  have hy₁p : y₁ ^ p = 1 := by
    rw [hy₁, ← pow_mul]
    have : Nat.card ↥(GLAPPrimeCore p ↥L) * m' * p =
        p * Nat.card ↥(GLAPPrimeCore p ↥L) * m' := by ring
    rw [this, pow_mul, hy₀pm, one_pow]
  have hbar₁ : (QuotientGroup.mk y₁ : PQuot p L) = QuotientGroup.mk y₀ := by
    rw [hy₁, QuotientGroup.mk_pow, pow_eq_pow_mod _ hbar, hm', pow_one]
  have hy₁1 : y₁ ≠ 1 := by
    intro h
    rw [h, QuotientGroup.mk_one] at hbar₁
    have h2 : e.symm σ = 1 := hy₀.symm.trans hbar₁.symm
    exact hσ1 (e.symm.injective (by rw [h2, map_one]))
  refine ⟨(y₁ : G), y₁.2, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · exact congrArg Subtype.val hy₁p
    · intro h
      exact hy₁1 (Subtype.ext h)
  · rw [permOfMod_of_mem e y₁.2]
    have : (⟨(y₁ : G), y₁.2⟩ : ↥L) = y₁ := rfl
    rw [this, hbar₁, hy₀, e.apply_symm_apply]

theorem isElemAbelian_card_altDxy (hp : p.Prime) {B : Subgroup G} {x : G} {L : Subgroup G} {y : G}
    (hB : IsElemAbelian p B) (hx : x ∈ B) (hx1 : x ≠ 1)
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) (hdir : IsDirectZpowersInf B x L) (hyL : y ∈ L)
    (hy : orderOf y = p) : IsElemAbelian p (altDxy x y) ∧ Nat.card ↥(altDxy x y) = p ^ 2 := by
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 (hxL hyL)).symm
  have hy1 : y ^ p = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hyne : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact hp.one_lt.ne hy
  have hna : x ∉ Subgroup.zpowers y := by
    intro hxy'
    have h1 : x ∈ Subgroup.zpowers x ⊓ (B ⊓ L) :=
      ⟨Subgroup.mem_zpowers x, hx, (Subgroup.zpowers_le.2 hyL) hxy'⟩
    rw [hdir.2] at h1
    exact hx1 (Subgroup.mem_bot.1 h1)
  exact Prop53.isElemAbelian_card_sup_zpowers hp hxy (hB.2 x hx) hy1 hyne hna

theorem imageMod_centralizer_eq (hp : p.Prime) {L : Subgroup G} {y : G} (hyL : y ∈ L)
    (hyo : orderOf y = p) :
    imageMod p L (L ⊓ Subgroup.centralizer ({y} : Set G)) =
      Subgroup.centralizer ({(QuotientGroup.mk (⟨y, hyL⟩ : ↥L) : PQuot p L)} : Set (PQuot p L)) := by
  have ha : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL
  have hy1 : y ^ p = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hap : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hy1
  have h1 := map_fixSubgroup_pQuotHom hp ha hap
  rw [fixSubgroup_normalizerMonoidHom ha] at h1
  refine h1.trans ?_
  ext z
  obtain ⟨k, rfl⟩ := pQuotHom_surjective p L z
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, barAut_pQuotHom,
    Subgroup.mem_centralizer_singleton_iff]
  have e1 : L.normalizerMonoidHom ⟨y, ha⟩ k = ⟨y, hyL⟩ * k * ⟨y, hyL⟩⁻¹ := Subtype.ext rfl
  rw [e1, map_mul, map_mul, map_inv]
  constructor
  · intro h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  · intro h
    exact mul_inv_eq_iff_eq_mul.2 h.symm

theorem pComponent_lift (hp : p.Prime) {L : Subgroup G} {y : G} (hyL : y ∈ L) (hyo : orderOf y = p) :
    (∀ J, GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) J →
      GLAPComponent p (imageMod p L (L ⊓ Subgroup.centralizer ({y} : Set G))) (imageMod p L J)) ∧
    (∀ I, GLAPComponent p (imageMod p L (L ⊓ Subgroup.centralizer ({y} : Set G))) I →
      ∃ J, GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) J ∧ imageMod p L J = I) ∧
    (∀ J J', GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) J →
      GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) J' →
      imageMod p L J = imageMod p L J' → J = J') := by
  have ha : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL
  have hy1 : y ^ p = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hap : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hy1
  have hker := coprime_card_inf_ker_pQuotHom hp L
    ((L ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf L)
  have hmk : ∀ {J : Subgroup G}, GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) J →
      GLAPComponent p ((L ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf L) (J.subgroupOf L) :=
    fun hJ => glaPComponent_subgroupOf hp inf_le_left hJ
  refine ⟨?_, ?_, ?_⟩
  · intro J hJ
    have h1 := glaPComponent_map_pQuotHom hp ha hap hJ
    have h2 := map_fixSubgroup_pQuotHom hp ha hap
    rw [fixSubgroup_normalizerMonoidHom ha] at h2
    rw [← h2] at h1
    exact h1
  · intro I hI
    obtain ⟨K, hK, hKI⟩ := exists_glaPComponent_map_eq hp (pQuotHom p L) hker hI
    have hsub : Nat.Coprime p (Nat.card ↥(((L ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf L) ⊓
        L.subtype.ker)) := by
      rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    refine ⟨K.map L.subtype, ?_, ?_⟩
    · have h1 := glaPComponent_map hp L.subtype hsub hK
      rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h1
    · have h1 : (K.map L.subtype).subgroupOf L = K :=
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective K
      show ((K.map L.subtype).subgroupOf L).map (pQuotHom p L) = I
      rw [h1]
      exact hKI
  · intro J J' hJ hJ' h
    have h1 : J.subgroupOf L = J'.subgroupOf L :=
      glaPComponent_eq_of_map_eq hp (pQuotHom p L) hker (hmk hJ) (hmk hJ') h
    rw [← Subgroup.map_subgroupOf_eq_of_le (hJ.1.trans inf_le_left),
      ← Subgroup.map_subgroupOf_eq_of_le (hJ'.1.trans inf_le_left), h1]

theorem glaPComponent_map_mulEquiv {A B : Type} [Group A] [Finite A] [Group B] (hp : p.Prime)
    (e : A ≃* B) {X K : Subgroup A} (hK : GLAPComponent p X K) :
    GLAPComponent p (X.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  refine glaPComponent_map hp e.toMonoidHom ?_ hK
  have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
  rw [this, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right p

theorem exists_J_alt (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {n : ℕ} (h2p : 2 * p ≤ n)
    (h5 : p + 5 ≤ n) (e : PQuot p L ≃* ↥(alternatingGroup (Fin n))) {y : G}
    (hy : IsPCycleMod p L n e y) (hyo : orderOf y = p) :
    ∃ J : Subgroup G, GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) J ∧
      GLAPLayer p (L ⊓ Subgroup.centralizer ({y} : Set G)) = J ∧
      (imageMod p L J).map e.toMonoidHom =
        fixingSubgroup (alternatingGroup (Fin n))
          ((permOfMod p L n e y).support : Set (Fin n)) := by
  classical
  obtain ⟨hyL, hcyc⟩ := hy
  obtain ⟨σ, hσdef⟩ : ∃ σ : ↥(alternatingGroup (Fin n)),
      σ = e (QuotientGroup.mk (⟨y, hyL⟩ : ↥L) : PQuot p L) := ⟨_, rfl⟩
  have hσperm : permOfMod p L n e y = (σ : Equiv.Perm (Fin n)) := by
    rw [hσdef]; exact permOfMod_of_mem e hyL
  have hσ : (σ : Equiv.Perm (Fin n)).cycleType = {p} := by rw [← hσperm]; exact hcyc
  obtain ⟨F, hF⟩ : ∃ F : Subgroup ↥(alternatingGroup (Fin n)),
      F = altFix (σ : Equiv.Perm (Fin n)) := ⟨_, rfl⟩
  obtain ⟨hmap, hex, huniq⟩ := pComponent_lift hp hyL hyo
  have ha := imageMod_centralizer_eq hp hyL hyo
  have hmapmap : ∀ K : Subgroup (PQuot p L), (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
    intro K
    rw [Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by ext; simp
    rw [this, Subgroup.map_id]
  have hmapmap' : ∀ K : Subgroup ↥(alternatingGroup (Fin n)),
      (K.map e.symm.toMonoidHom).map e.toMonoidHom = K := by
    intro K
    rw [Subgroup.map_map]
    have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by ext; simp
    rw [this, Subgroup.map_id]
  have hC : (imageMod p L (L ⊓ Subgroup.centralizer ({y} : Set G))).map e.toMonoidHom =
      Subgroup.centralizer ({σ} : Set ↥(alternatingGroup (Fin n))) := by
    rw [ha, hσdef]
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' := Subgroup.mem_centralizer_singleton_iff.1 hw
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      change e w * e (QuotientGroup.mk (⟨y, hyL⟩ : ↥L) : PQuot p L) =
        e (QuotientGroup.mk (⟨y, hyL⟩ : ↥L) : PQuot p L) * e w
      rw [← map_mul, ← map_mul, hw']
    · intro hz
      refine ⟨e.symm z, Subgroup.mem_centralizer_singleton_iff.2 ?_, e.apply_symm_apply z⟩
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact Subgroup.mem_centralizer_singleton_iff.1 hz
  have hFcomp : GLAPComponent p (Subgroup.centralizer ({σ} : Set ↥(alternatingGroup (Fin n)))) F := by
    rw [hF]; exact altFix_isPComponent_cycle hp hp2 hσ h2p h5
  obtain ⟨I, hI⟩ : ∃ I : Subgroup (PQuot p L), I = F.map e.symm.toMonoidHom := ⟨_, rfl⟩
  have hIcomp : GLAPComponent p (imageMod p L (L ⊓ Subgroup.centralizer ({y} : Set G))) I := by
    have h1 := glaPComponent_map_mulEquiv hp e.symm hFcomp
    rw [← hC, hmapmap] at h1
    rwa [hI]
  obtain ⟨J, hJ, hJI⟩ := hex I hIcomp
  have hJF : (imageMod p L J).map e.toMonoidHom = F := by
    rw [hJI, hI, hmapmap']
  refine ⟨J, hJ, ?_, by rw [hσperm]; exact hJF.trans (hF.trans (altFix_eq_fixingSubgroup _))⟩
  refine le_antisymm (sSup_le fun J' hJ' => ?_) (le_sSup hJ)
  have h1 := glaPComponent_map_mulEquiv hp e (hmap J' hJ')
  rw [hC] at h1
  have h2 : (imageMod p L J').map e.toMonoidHom = F := by
    rw [hF]; exact altFix_unique_cycle hp hp2 hσ h5 h1
  have h3 : imageMod p L J' = I := by
    rw [hI, ← h2, hmapmap]
  exact (huniq J' J hJ' hJ (h3.trans hJI.symm)).le

theorem nonempty_pQuot_equiv_imageMod (hp : p.Prime) {L J : Subgroup G} (hJL : J ≤ L) :
    Nonempty (PQuot p J ≃* PQuot p (imageMod p L J)) := by
  obtain ⟨e₁⟩ := nonempty_pQuot_equiv_subgroupOf p hJL
  have hN : ¬ p ∣ Nat.card (pQuotHom p L).ker := by
    rw [ker_pQuotHom]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_card_gLAPPrimeCore_aux p ↥L)
  obtain ⟨e₂⟩ := nonempty_pQuot_equiv_map hp hN (J.subgroupOf L)
  exact ⟨e₁.symm.trans e₂⟩

theorem nonempty_pQuot_equiv_of_eq {Y : Type} [Group Y] {H₁ H₂ : Subgroup Y} (h : H₁ = H₂) :
    Nonempty (PQuot p H₁ ≃* PQuot p H₂) := by
  subst h
  exact ⟨MulEquiv.refl _⟩

theorem exists_J_alt_type (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {n : ℕ} (h2p : 2 * p ≤ n)
    (h5 : p + 5 ≤ n) (e : PQuot p L ≃* ↥(alternatingGroup (Fin n))) {y : G}
    (hy : IsPCycleMod p L n e y) (hyo : orderOf y = p) {J : Subgroup G}
    (hJ : GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (hfix : (imageMod p L J).map e.toMonoidHom =
      fixingSubgroup (alternatingGroup (Fin n)) ((permOfMod p L n e y).support : Set (Fin n))) :
    IsAltPType p J (n - p) := by
  classical
  obtain ⟨hyL, hcyc⟩ := hy
  have hcard : (permOfMod p L n e y).support.card = p := card_support_eq_of_cycleType hcyc
  have hF : (imageMod p L J).map e.toMonoidHom = altFix (permOfMod p L n e y) := by
    rw [hfix, altFix_eq_fixingSubgroup]
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  obtain ⟨e₁⟩ := nonempty_pQuot_equiv_imageMod hp hJL
  have hN : ¬ p ∣ Nat.card e.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective, Subgroup.card_bot]
    exact fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)
  obtain ⟨e₂⟩ := nonempty_pQuot_equiv_map hp hN (imageMod p L J)
  obtain ⟨e₃⟩ := nonempty_pQuot_equiv_of_eq (p := p) hF
  obtain ⟨e₄⟩ := nonempty_pQuot_equiv_altFix hp hp2 (permOfMod p L n e y) (m := n - p)
    (by rw [hcard]) (by omega) (by omega)
  exact ⟨e₁.trans (e₂.trans (e₃.trans e₄))⟩

theorem altCommon_of_alt (hc : S6Ctx G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : IsSStarMax p B x L) {n : ℕ} (hn : 5 ≤ n)
    (f : PSimple p L ≃* ↥(alternatingGroup (Fin n))) : AltCommon p B x L n := by
  have h3 : 3 * p ≤ n := three_mul_le_of_alt hc h hn f
  have hp3 : 3 ≤ p := by
    have := hc.prime.two_le
    have := hc.odd
    omega
  have h8 : 8 ≤ n := by omega
  have hZ : Subgroup.center (PQuot p L) = ⊥ :=
    center_pQuot_eq_bot_of_alt hc.prime hc.odd (IsSStarMax.component h) h8 f
  let e : PQuot p L ≃* ↥(alternatingGroup (Fin n)) :=
    ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans f)
  have hdir : IsDirectZpowersInf B x L :=
    isDirectZpowersInf_of_decomp hc h hZ (exists_inner_decomp hc h hn e)
  have hrL : CFSG.Open.pRank p L = n / p := pRank_eq_div_of_alt hc e
  refine ⟨⟨e⟩, h3, by omega, hdir, hrL, ?_⟩
  rw [← hrL]
  exact pRank_le_of_isDirectZpowersInf hc h hdir

theorem altSetup_of_common (hc : S6Ctx G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : IsSStarMax p B x L) {n : ℕ} (hcom : AltCommon p B x L n)
    (e : PQuot p L ≃* ↥(alternatingGroup (Fin n))) {y : G} (hy : IsPCycleMod p L n e y)
    (hyo : orderOf y = p) : ∃ J : Subgroup G, AltSetup p B x L n y J := by
  have hp3 : 3 ≤ p := by
    have := hc.prime.two_le
    have := hc.odd
    omega
  have h2p : 2 * p ≤ n := by have := hcom.three_mul_le; omega
  have h5 : p + 5 ≤ n := by have := hcom.three_mul_le; omega
  obtain ⟨J, hJc, hJl, hJfix⟩ := exists_J_alt hc.prime hc.odd h2p h5 e hy hyo
  have hJalt : IsAltPType p J (n - p) := exists_J_alt_type hc.prime hc.odd h2p h5 e hy hyo hJc hJfix
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component h).1
  have hCD := inf_centralizer_altDxy_eq (y := y) hxL
  obtain ⟨hDel, hDcard⟩ := isElemAbelian_card_altDxy hc.prime (IsSStarMax.bmax h).1
    (IsSStarMax.essential h).1 (IsSStarMax.essential h).2.1 hxL hcom.B_eq hy.1 hyo
  have hrJ : CFSG.Open.pRank p J = n / p - 1 := by
    obtain ⟨eJ⟩ := hJalt
    rw [pRank_eq_pRank_pQuot hc.prime J, CFSG.SectionRank.pRank_top_eq_of_mulEquiv hc.prime.one_lt eJ,
      (CFSG.Quasithin.H13.A7.section_rank_alternating_odd_prime_rank).1 (n - p) p hc.prime hc.odd]
    have hp0 : 0 < p := hc.prime.pos
    have h3 := hcom.three_mul_le
    have hnp : p ≤ n := by omega
    have h1 : n / p = (n - p) / p + 1 := by
      conv_lhs => rw [show n = (n - p) + p by omega]
      exact Nat.add_div_right _ hp0
    rw [h1, Nat.add_sub_cancel]
  refine ⟨J, ⟨hcom.alt, hcom.three_mul_le, hcom.seven_lt, hy.1, hyo, hDel, hDcard, ⟨e, hy, hJfix⟩,
    ?_, ?_, hJalt, hcom.B_eq, hcom.rank_L, hrJ, hcom.rank_B⟩⟩
  · rw [hCD]; exact hJc
  · rw [hCD]; exact hJl

theorem altSetup_holds (hc : S6Ctx G p) : AltSetupAt G p := by
  intro B x L h hAlt
  obtain ⟨n, hn, ⟨f⟩⟩ := exists_alt_of_catalogIs hAlt
  have hcom := altCommon_of_alt hc h hn f
  obtain ⟨e⟩ := hcom.alt
  obtain ⟨σ, hσ⟩ := exists_pCycle hc.prime hc.odd
    (le_trans (Nat.le_mul_of_pos_left p (by norm_num)) hcom.three_mul_le)
  obtain ⟨y, hyL, hyo, hyσ⟩ := exists_cycle_lift hc.prime e σ hσ
  have hy : IsPCycleMod p L n e y := ⟨hyL, by rw [hyσ]; exact hσ⟩
  obtain ⟨J, hJ⟩ := altSetup_of_common hc h hcom e hy hyo
  exact ⟨n, y, J, hJ⟩

theorem AltSetup.rechoose (hc : S6Ctx G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G} (h : IsSStarMax p B x L)
    (S : AltSetup p B x L n y J) (e : PQuot p L ≃* ↥(alternatingGroup (Fin n))) {y' : G}
    (hy' : IsPCycleMod p L n e y') (hyo' : orderOf y' = p) :
    ∃ J' : Subgroup G, AltSetup p B x L n y' J' :=
  altSetup_of_common hc h S.toCommon e hy' hyo'

end CFSG.LocalAnalysis.GLTheoremA
