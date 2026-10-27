module

public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
public import CFSG.LocalAnalysis.GLTheoremA.PartI.BmaxCent
public import CFSG.LocalAnalysis.GL83PartI.I_33
import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.LocalAnalysis.GLTheoremA.S3.Basic
import CFSG.Milestones.AT_alternating_automorphism_permutation
import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk coprime_card_gLAPPrimeCore_aux)
open scoped commutatorElement

structure Lemma72Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i183 : Input18_3_4
  i112 : I112StarAt G p
  altNotWeakExc : AltNotWeakExcAt
  i1415 : I1415At G p
  i2013 : I2013At

variable {G : Type} [Group G] [Finite G] {p : ℕ}

structure L72Single (p : ℕ) (D J K : Subgroup G) (a : G) : Prop where
  comp : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K
  norm : D ≤ Subgroup.normalizer (K : Set G)
  J_le : J ≤ K
  J_comp : GLAPComponent p (K ⊓ Subgroup.centralizer (D : Set G)) J

private theorem centralizer_eq_inf_of_eq_sup {D : Subgroup G} {a b : G}
    (hD : D = Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
  rw [hD, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
    Subgroup.centralizer_closure]
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_union,
    Set.mem_singleton_iff, or_imp, forall_and, forall_eq]

private theorem mem_gLBConj_iff' {M : Subgroup G} {g x : G} : x ∈ GLBConj g M ↔ g * x * g⁻¹ ∈ M := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

private theorem closureIn_eq_iSup_gLBConj' (I H : Subgroup G) :
    closureIn I H = ⨆ g ∈ H, GLBConj g I := by
  unfold closureIn
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    have : I.map (MulAut.conj a).toMonoidHom = GLBConj a⁻¹ I := by
      unfold GLBConj
      rw [inv_inv]
    rw [this]
    exact le_iSup₂_of_le a⁻¹ (H.inv_mem ha) le_rfl
  · refine iSup₂_le fun g hg => ?_
    unfold GLBConj
    exact le_iSup₂_of_le g⁻¹ (H.inv_mem hg) le_rfl


theorem l72_pComponent_centralizer {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hp : p.Prime) (hB : IsSStarMax p B x L) (S : AltSetup p B x L n y J) :
    GLAPComponent p (Subgroup.centralizer (altDxy x y : Set G)) J := by
  have hLx := IsSStarMax.component hB
  have hxD : x ∈ altDxy x y := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hCD : Subgroup.centralizer (altDxy x y : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (by simpa using hxD)
  have hsn : IsSubnormal (L ⊓ Subgroup.centralizer (altDxy x y : Set G))
      (Subgroup.centralizer (altDxy x y : Set G)) := by
    have := hLx.2.1.inf (Subgroup.centralizer (altDxy x y : Set G))
    rwa [inf_eq_right.2 hCD] at this
  exact glaPComponent_of_isSubnormal' hp hsn S.J_comp

theorem l72_exists_Bprime {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hc : S6Ctx G p) (hB : IsSStarMax p B x L) (S : AltSetup p B x L n y J) :
    ∃ B' : Subgroup G, altDxy x y ≤ B' ∧ IsElemAbelian p B' ∧
      B' ≤ Subgroup.centralizer (altDxy x y : Set G) ∧
      CFSG.Open.pRank p B ≤ CFSG.Open.pRank p B' := by
  have hp := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hpn : p ≤ n := by have := S.three_mul_le; omega
  obtain ⟨e, hycyc, -⟩ := S.cycle
  have hσc : ((e (QuotientGroup.mk (⟨y, S.y_mem⟩ : ↥L) : PQuot p L) : ↥(alternatingGroup (Fin n))) :
      Equiv.Perm (Fin n)).cycleType = {p} := by
    have := hycyc.2
    rwa [permOfMod_of_mem e S.y_mem] at this
  obtain ⟨Eb, hEbel, hEbc, hσEb, -⟩ := exists_elemAbelian_pCycle hp hc.odd hpn _ hσc
  obtain ⟨E, hEL, hEel, hyE, hEcard, -⟩ :=
    exists_lift_elemAbelian hp e hEbel S.y_mem S.y_order hσEb
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component hB).1
  have hxB : x ∈ B := (IsSStarMax.essential hB).1
  have hx1 : x ≠ 1 := (IsSStarMax.essential hB).2.1
  have hBel : IsElemAbelian p B := (IsSStarMax.bmax hB).1
  have hxel : IsElemAbelian p (Subgroup.zpowers x) := isElemAbelian_zpowers_of_mem hBel hxB
  have hEz : E ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hEL.trans hxL
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.1 (hEz hb)) a ha)
  have hB'el := isElemAbelian_sup_of_commute hxel hEel hcomm
  have hxo : orderOf x = p := orderOf_eq_prime (hBel.2 x hxB) hx1
  have hinf : Subgroup.zpowers x ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h1 : g ∈ Subgroup.zpowers x ⊓ (B ⊓ L) :=
      ⟨hg.1, (Subgroup.zpowers_le.2 hxB) hg.1, hEL hg.2⟩
    rw [S.B_eq.2] at h1
    exact h1
  have hcard : Nat.card ↥(Subgroup.zpowers x ⊔ E) = p ^ (n / p + 1) := by
    have hN : E ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
      hEz.trans (Subgroup.centralizer_le_normalizer _)
    have h1 := card_sup_mul_card_inf_of_le_normalizer hN
    rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hxo, mul_one] at h1
    rw [h1, hEcard, hEbc, pow_succ, mul_comm]
  have hrk : CFSG.Open.pRank p (Subgroup.zpowers x ⊔ E) = n / p + 1 :=
    pRank_eq_of_isElemAbelian_altSetup hp.one_lt hB'el hcard
  have hxB' : x ∈ Subgroup.zpowers x ⊔ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyB' : y ∈ Subgroup.zpowers x ⊔ E := Subgroup.mem_sup_right hyE
  refine ⟨Subgroup.zpowers x ⊔ E, ?_, hB'el, ?_, ?_⟩
  · exact sup_le ((Subgroup.zpowers_le).2 hxB') ((Subgroup.zpowers_le).2 hyB')
  · intro g hg
    rw [mem_centralizer_altDxy_iff]
    exact ⟨isElemAbelian_commute hB'el hg hxB', isElemAbelian_commute hB'el hg hyB'⟩
  · rw [hrk]
    exact S.rank_B

theorem l72_family_single {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hc : S6Ctx G p) (i112 : I112StarAt G p) (hne : AltNotWeakExcAt)
    (hB : IsSStarMax p B x L)
    (S : AltSetup p B x L n y J) (hn : 7 < n - p) {a b : G} (haD : a ∈ altDxy x y) (ha1 : a ≠ 1)
    (hbD : b ∈ altDxy x y) (hb : b ∉ Subgroup.zpowers a)
    (hJ : GLAPComponent p (Subgroup.centralizer ({a} : Set G) ⊓
      Subgroup.centralizer ({b} : Set G)) J)
    {𝒞 : Set (Subgroup G)}
    (h𝒞c : ∀ K ∈ 𝒞, GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K)
    (h𝒞sup : (⨆ K ∈ 𝒞, K) =
      ⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({a} : Set G)), GLBConj g J)
    (h𝒞tr : ∀ K ∈ 𝒞, ∀ K' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers b, GLBConj e K = K') :
    ∀ K ∈ 𝒞, ∀ K' ∈ 𝒞, K = K' := by
  classical
  intro K hK K' hK'
  by_contra hKK'
  have hp := hc.prime
  obtain ⟨B', hDB', hB'el, hB'C, hrank⟩ := l72_exists_Bprime hc hB S
  have hB'a : B' ≤ Subgroup.centralizer ({a} : Set G) :=
    hB'C.trans (Subgroup.centralizer_le (by simpa using haD))
  have hbB' : b ∈ B' := hDB' hbD
  have hbn : b ∉ Subgroup.normalizer (K : Set G) := by
    intro hbN
    obtain ⟨e, he, hKe⟩ := h𝒞tr K hK K' hK'
    have heN : e ∈ Subgroup.normalizer (K : Set G) := (Subgroup.zpowers_le.2 hbN) he
    exact hKK' ((mem_normalizer_iff_gLBConj_eq.1 heN).symm.trans hKe)
  obtain ⟨-, hcat⟩ := i112 hp hc.odd (Subgroup.centralizer ({a} : Set G)) B' K
    (kGroup_centralizer hc ha1) hB'a hB'el
    ((glaTwoLocalRank_le_pRank_of_isBmax hp (IsSStarMax.bmax hB) _).trans hrank) (h𝒞c K hK)
    (fun h => hbn (h hbB'))
  have hKcl : closureIn K B' ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [closureIn_eq_iSup_gLBConj']
    refine iSup₂_le fun g hg x hx => ?_
    have h1 := hB'a hg
    have h2 : g * x * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := (h𝒞c K hK).1 (mem_gLBConj_iff'.1 hx)
    have h3 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h2) h1
  have hJle : J ≤ closureIn K B' := by
    have hJ1 : J ≤ ⨆ K ∈ 𝒞, K := by
      rw [h𝒞sup]
      exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (fun x hx => by
        exact mem_gLBConj_iff'.2 (by simpa using hx))
    refine hJ1.trans (iSup₂_le fun K'' hK'' => ?_)
    obtain ⟨e, he, hKe⟩ := h𝒞tr K hK K'' hK''
    rw [← hKe, closureIn_eq_iSup_gLBConj']
    exact le_iSup₂_of_le e ((Subgroup.zpowers_le.2 hbB') he) le_rfl
  have hJb : J ≤ Subgroup.centralizer ({b} : Set G) := hJ.1.trans inf_le_right
  have hJcomp : GLAPComponent p (closureIn K B' ⊓ Subgroup.centralizer ({b} : Set G)) J :=
    glaPComponent_of_le hp hJ (le_inf hJle hJb) (inf_le_inf_right _ hKcl)
  obtain ⟨e⟩ := S.J_alt
  exact hne (n - p) (by omega) ((catalogIs_congr e).1 (hcat b hbB' hbn J hJcomp))

theorem l72_single_of_family {D J : Subgroup G} {a b : G} (hp : p.Prime)
    (hD : D = Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hJ : GLAPComponent p (Subgroup.centralizer ({a} : Set G) ⊓
      Subgroup.centralizer ({b} : Set G)) J)
    {𝒞 : Set (Subgroup G)}
    (h𝒞c : ∀ K ∈ 𝒞, GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K)
    (h𝒞sup : (⨆ K ∈ 𝒞, K) =
      ⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({a} : Set G)), GLBConj g J)
    (h𝒞inv : ∀ K ∈ 𝒞, ∀ e ∈ Subgroup.zpowers b, GLBConj e K ∈ 𝒞)
    (h𝒞one : ∀ K ∈ 𝒞, ∀ K' ∈ 𝒞, K = K') :
    L72Single p D J (closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G)))) a := by
  classical
  have hJ0 : J ≠ ⊥ := glaPComponent_ne_bot' hJ
  have hcl : closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G))) = ⨆ K ∈ 𝒞, K := by
    rw [h𝒞sup, closureIn_eq_iSup_gLBConj']
  have hJcl : J ≤ closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G))) := by
    rw [closureIn_eq_iSup_gLBConj']
    exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (fun x hx => by
      exact mem_gLBConj_iff'.2 (by simpa using hx))
  obtain ⟨K₁, hK₁⟩ : ∃ K₁, K₁ ∈ 𝒞 := by
    by_contra hne
    push Not at hne
    apply hJ0
    rw [eq_bot_iff]
    refine hJcl.trans ?_
    rw [hcl]
    exact iSup₂_le fun K hK => absurd hK (hne K)
  have hall : closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G))) = K₁ := by
    rw [hcl]
    exact le_antisymm (iSup₂_le fun K hK => (h𝒞one K hK K₁ hK₁).le)
      (le_iSup₂_of_le K₁ hK₁ le_rfl)
  rw [hall] at hJcl ⊢
  have hCD := centralizer_eq_inf_of_eq_sup hD
  have hKa : K₁ ≤ Subgroup.centralizer ({a} : Set G) := (h𝒞c K₁ hK₁).1
  refine ⟨h𝒞c K₁ hK₁, ?_, hJcl, ?_⟩
  · rw [hD]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.2 fun h hh => Subgroup.mem_centralizer_singleton_iff.1 (hKa hh))
    · exact mem_normalizer_iff_gLBConj_eq.2
        (h𝒞one _ (h𝒞inv K₁ hK₁ b (Subgroup.mem_zpowers b)) K₁ hK₁)
  · refine glaPComponent_of_le hp hJ (le_inf hJcl (by rw [hCD]; exact hJ.1)) ?_
    rw [hCD]
    exact inf_le_right

theorem exists_pair_of_card_sq (hp : p.Prime) {D : Subgroup G} (hD : Nat.card ↥D = p ^ 2) {a : G}
    (haD : a ∈ D) (ha1 : a ≠ 1) (hel : IsElemAbelian p D) :
    ∃ b ∈ D, b ∉ Subgroup.zpowers a ∧ D = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hao : orderOf a = p := orderOf_eq_prime (hel.2 a haD) ha1
  have hz : Nat.card ↥(Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hao]
  have hzD : Subgroup.zpowers a ≤ D := Subgroup.zpowers_le.2 haD
  obtain ⟨b, hbD, hb⟩ : ∃ b ∈ D, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ Subgroup.zpowers a := fun g hg => hcon g hg
    have := Subgroup.card_le_of_le hle
    rw [hD, hz] at this
    have h2 : p < p ^ 2 := by
      have := hp.one_lt
      nlinarith
    omega
  have hb1 : b ≠ 1 := fun h => hb (h ▸ Subgroup.one_mem _)
  have hab : a * b = b * a := isElemAbelian_commute hel haD hbD
  have hbo : orderOf b = p := orderOf_eq_prime (hel.2 b hbD) hb1
  have hna : a ∉ Subgroup.zpowers b := by
    intro hab'
    have hle : Subgroup.zpowers a ≤ Subgroup.zpowers b := Subgroup.zpowers_le.2 hab'
    have heq : Subgroup.zpowers a = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hao, hbo])
    exact hb (heq ▸ Subgroup.mem_zpowers b)
  obtain ⟨-, hcard⟩ := Prop53.isElemAbelian_card_sup_zpowers hp hab (hel.2 a haD) (hel.2 b hbD) hb1 hna
  refine ⟨b, hbD, hb, ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hzD (Subgroup.zpowers_le.2 hbD))
    (by rw [hcard, hD])).symm

theorem l72_single {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    (hc : S6Ctx G p) (i183 : Input18_3_4) (i112 : I112StarAt G p) (hne : AltNotWeakExcAt)
    (hB : IsSStarMax p B x L) (S : AltSetup p B x L n y J) (hn : 7 < n - p) {a : G}
    (haD : a ∈ altDxy x y) (ha1 : a ≠ 1) :
    L72Single p (altDxy x y) J
      (closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G)))) a := by
  obtain ⟨b, hbD, hb, hDab⟩ := exists_pair_of_card_sq hc.prime S.card_D haD ha1 S.isElemAbelian_D
  have hJD := l72_pComponent_centralizer hc.prime hB S
  have hJab : GLAPComponent p (Subgroup.centralizer ({a} : Set G) ⊓
      Subgroup.centralizer ({b} : Set G)) J := by
    have : Subgroup.centralizer (altDxy x y : Set G) =
        Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
      rw [hDab, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
        Subgroup.centralizer_closure]
      ext g
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_union,
        Set.mem_singleton_iff, or_imp, forall_and, forall_eq]
    rwa [this] at hJD
  have hKa : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    kGroup_centralizer hc ha1
  have hab : a * b = b * a := isElemAbelian_commute S.isElemAbelian_D haD hbD
  have hbN : Subgroup.zpowers b ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hab
  have hbel : IsElemAbelian p (Subgroup.zpowers b) :=
    isElemAbelian_zpowers_of_mem S.isElemAbelian_D hbD
  have hJz : GLAPComponent p (Subgroup.centralizer ({a} : Set G) ⊓
      Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G)) J := by
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨𝒞, h𝒞c, h𝒞sup, h𝒞inv, h𝒞tr⟩ := i183 G (Subgroup.centralizer ({a} : Set G)) hKa p
    hc.prime (Subgroup.zpowers b) hbN hbel J hJz
  exact l72_single_of_family hc.prime hDab hJab h𝒞c h𝒞sup h𝒞inv
    (l72_family_single hc i112 hne hB S hn haD ha1 hbD hb hJab h𝒞c h𝒞sup h𝒞tr)

theorem genByPElts_of_simple (hp : p.Prime) {Y : Type} [Group Y] [Finite Y] {F : Subgroup Y}
    [IsSimpleGroup ↥F] (hpF : p ∣ Nat.card ↥F) : GenByPElts p F := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpF
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    exact hp.one_lt.ne hg
  have hbot : Subgroup.normalClosure ({g} : Set ↥F) ≠ ⊥ := by
    intro h
    rw [Subgroup.normalClosure_eq_bot_iff] at h
    exact hg1 (h rfl)
  have htop : Subgroup.normalClosure ({g} : Set ↥F) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ ).resolve_left hbot
  have hsub : Subgroup.normalClosure ({g} : Set ↥F) ≤
      Subgroup.closure {x : ↥F | x ^ p = 1} := by
    rw [Subgroup.normalClosure]
    refine Subgroup.closure_mono ?_
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨c, rfl⟩ := isConj_iff.1 hax
    show (c * a * c⁻¹) ^ p = 1
    rw [conj_pow, ← hg, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  intro y hy
  have hy0 : (⟨y, hy⟩ : ↥F) ∈ Subgroup.normalClosure ({g} : Set ↥F) := by
    rw [htop]; exact Subgroup.mem_top _
  have hy' : (⟨y, hy⟩ : ↥F) ∈ Subgroup.closure {x : ↥F | x ^ p = 1} := hsub hy0
  have h2 : (Subgroup.closure {x : ↥F | x ^ p = 1}).map F.subtype ≤
      Subgroup.closure {g : Y | g ∈ F ∧ IsPGroup p (Subgroup.zpowers g)} := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, isPGroup_zpowers_of_pow_eq_one (by simpa using congrArg Subtype.val hx)⟩
  exact h2 ⟨⟨y, hy⟩, hy', rfl⟩

theorem genByPElts_map {A B : Type} [Group A] [Group B] (f : A →* B) {I : Subgroup A}
    (h : GenByPElts p I) : GenByPElts p (I.map f) := by
  have h1 : I.map f ≤ (Subgroup.closure {g : A | g ∈ I ∧ IsPGroup p (Subgroup.zpowers g)}).map f :=
    Subgroup.map_mono h
  rw [MonoidHom.map_closure] at h1
  refine h1.trans (Subgroup.closure_mono ?_)
  rintro _ ⟨x, ⟨hxI, hx⟩, rfl⟩
  refine ⟨Subgroup.mem_map_of_mem f hxI, ?_⟩
  rintro ⟨_, hy⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  obtain ⟨m, hm⟩ := hx ⟨x ^ k, Subgroup.zpow_mem_zpowers x k⟩
  refine ⟨m, Subtype.ext ?_⟩
  have h2 : (x ^ k) ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  show ((f x) ^ k) ^ p ^ m = 1
  rw [← map_zpow, ← map_pow, h2, map_one]

theorem isPGroup_subgroup_map {A B : Type} [Group A] [Group B] (f : A →* B) {H : Subgroup A}
    (hH : IsPGroup p H) : IsPGroup p (H.map f) := by
  rintro ⟨_, hy⟩
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨m, hm⟩ := hH ⟨x, hx⟩
  refine ⟨m, Subtype.ext ?_⟩
  have h2 : x ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  show (f x) ^ p ^ m = 1
  rw [← map_pow, h2, map_one]

theorem exists_barI_barT_alt (hp : p.Prime) (hp2 : p ≠ 2) {M m₀ : ℕ} (h5 : 5 ≤ m₀) (hpm : p ≤ m₀)
    (hM : m₀ + 4 ≤ M) :
    ∃ I' T' : Subgroup ↥(alternatingGroup (Fin M)),
      IsRootAlt (MulEquiv.refl ↥(alternatingGroup (Fin M))) I' m₀ ∧ GenByPElts p I' ∧
        ¬ IsPGroup 2 I' ∧ IsPGroup 2 T' ∧ T' ≠ ⊥ ∧ T' ≤ Subgroup.centralizer (I' : Set _) := by
  classical
  have hm₀M : m₀ ≤ M := by omega
  obtain ⟨T, hTdef⟩ : ∃ T : Finset (Fin M), T = (Finset.univ : Finset (Fin m₀)).map (Fin.castLEEmb hm₀M) :=
    ⟨_, rfl⟩
  have hTcard : T.card = m₀ := by rw [hTdef, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hTmem : ∀ i ∈ T, i.val < m₀ := by
    intro i hi
    rw [hTdef, Finset.mem_map] at hi
    obtain ⟨a, -, rfl⟩ := hi
    exact a.2
  let a : Fin M := ⟨m₀, by omega⟩
  let b : Fin M := ⟨m₀ + 1, by omega⟩
  let c : Fin M := ⟨m₀ + 2, by omega⟩
  let d : Fin M := ⟨m₀ + 3, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hcd : c ≠ d := by simp [c, d, Fin.ext_iff]
  have hdisj : Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c d) := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support, Equiv.Perm.support_swap hab,
      Equiv.Perm.support_swap hcd, Finset.disjoint_left]
    intro u hu hu'
    simp only [Finset.mem_insert, Finset.mem_singleton, a, b, c, d, Fin.ext_iff] at hu hu'
    omega
  set τ : Equiv.Perm (Fin M) := Equiv.swap a b * Equiv.swap c d with hτdef
  have hτsign : Equiv.Perm.sign τ = 1 := by
    rw [hτdef, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcd]
    decide
  have hτsq : τ ^ 2 = 1 := by
    rw [hτdef, hdisj.commute.mul_pow, pow_two, pow_two, Equiv.swap_mul_self, Equiv.swap_mul_self,
      mul_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
    have had : a ≠ d := by simp [a, d, Fin.ext_iff]
    have h1 : τ a = b := by
      rw [hτdef, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_left]
    have h2 : τ a = a := by rw [h]; rfl
    exact hab (h1.symm.trans h2).symm
  have hτsupp : τ.support ⊆ ({a, b, c, d} : Finset (Fin M)) := by
    refine (Equiv.Perm.support_mul_le _ _).trans (sup_le ?_ ?_)
    · rw [Equiv.Perm.support_swap hab]; intro u hu; simp at hu ⊢; tauto
    · rw [Equiv.Perm.support_swap hcd]; intro u hu; simp at hu ⊢; tauto
  let τ' : ↥(alternatingGroup (Fin M)) := ⟨τ, Equiv.Perm.mem_alternatingGroup.2 hτsign⟩
  have hτ'sq : τ' ^ 2 = 1 := Subtype.ext (by simpa using hτsq)
  have hτ'1 : τ' ≠ 1 := fun h => hτ1 (congrArg Subtype.val h)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ'o : orderOf τ' = 2 := orderOf_eq_prime hτ'sq hτ'1
  have hTcard3 : 3 ≤ T.card := by omega
  have hTcard5 : 5 ≤ Nat.card (Fin m₀) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact h5
  obtain ⟨e⟩ := nonempty_altOn_equiv T hTcard
  haveI : IsSimpleGroup (alternatingGroup (Fin m₀)) := alternatingGroup.isSimpleGroup hTcard5
  haveI : IsSimpleGroup ↥(altOn T) := e.isSimpleGroup
  have hdvd : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≤ m₀ → q ∣ Nat.card ↥(altOn T) := by
    intro q hq hq2 hqm
    rw [Nat.card_congr e.toEquiv]
    exact p_dvd_card_alternatingGroup hq hq2 (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hqm)
  refine ⟨altOn T, Subgroup.zpowers τ', ?_, genByPElts_of_simple hp (hdvd p hp hp2 hpm), ?_, ?_, ?_, ?_⟩
  · have := isRootAlt_altOn hTcard3
    rwa [hTcard] at this
  · intro h2
    have h3 : 3 ∣ Nat.card ↥(altOn T) := hdvd 3 Nat.prime_three (by norm_num) (by omega)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 h2
    rw [hk] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hτ'o, pow_one]
  · intro h
    apply hτ'1
    have : τ' ∈ Subgroup.zpowers τ' := Subgroup.mem_zpowers τ'
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  · rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgs : (g : Equiv.Perm (Fin M)).support ⊆ T := mem_altOn_iff.1 hg
    have hd : Equiv.Perm.Disjoint (g : Equiv.Perm (Fin M)) τ := by
      rw [Equiv.Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
      intro u hu hu'
      have h1 := hTmem u (hgs hu)
      have h2 := hτsupp hu'
      simp only [Finset.mem_insert, Finset.mem_singleton] at h2
      rcases h2 with rfl | rfl | rfl | rfl <;> simp [a, b, c, d] at h1 <;> omega
    exact Subtype.ext hd.commute.eq

theorem isPGroup_of_map_injective {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) {H : Subgroup A} (h : IsPGroup p (H.map f)) : IsPGroup p H := by
  rintro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := h ⟨f x, Subgroup.mem_map_of_mem f hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h2 : (f x) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  show x ^ p ^ k = 1
  apply hf
  rw [map_pow, h2, map_one]

theorem exists_barI_barT {Q : Type} [Group Q] {M : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin M)))
    (hp : p.Prime) (hp2 : p ≠ 2) {m₀ : ℕ} (h5 : 5 ≤ m₀) (hpm : p ≤ m₀) (hM : m₀ + 4 ≤ M) :
    ∃ I' T' : Subgroup Q, IsRootAlt e I' m₀ ∧ GenByPElts p I' ∧ ¬ IsPGroup 2 I' ∧
      IsPGroup 2 T' ∧ T' ≠ ⊥ ∧ T' ≤ Subgroup.centralizer (I' : Set Q) := by
  obtain ⟨I, T, hroot, hgen, hnot2, hT2, hT0, hTI⟩ := exists_barI_barT_alt hp hp2 h5 hpm hM
  obtain ⟨f, hf⟩ : ∃ f : ↥(alternatingGroup (Fin M)) →* Q, f = e.symm.toMonoidHom := ⟨_, rfl⟩
  have hfinj : Function.Injective f := by rw [hf]; exact e.symm.injective
  refine ⟨I.map f, T.map f, ⟨⟨(Subgroup.equivMapOfInjective I f hfinj).symm.trans hroot.1.some⟩, ?_⟩,
    genByPElts_map f hgen, fun h2 => hnot2 (isPGroup_of_map_injective f hfinj h2),
    isPGroup_subgroup_map f hT2,
    fun h => hT0 ((Subgroup.map_eq_bot_iff_of_injective T hfinj).1 h), ?_⟩
  · have h1 : movedLettersOf e (I.map f) = movedLettersOf (MulEquiv.refl _) I := by
      ext i
      constructor
      · rintro ⟨h, ⟨h', hh', rfl⟩, hi⟩
        exact ⟨h', hh', by simpa [hf] using hi⟩
      · rintro ⟨h', hh', hi⟩
        exact ⟨f h', ⟨h', hh', rfl⟩, by simpa [hf] using hi⟩
    unfold MovesExactly
    rw [h1]
    exact hroot.2
  · rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨i, hi, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 (hTI ht) i hi
    rw [← map_mul, ← map_mul, this]

@[expose] def preimageMod (p : ℕ) (J : Subgroup G) (Tbar : Subgroup (PQuot p J)) : Subgroup G :=
  (Tbar.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥J))).map J.subtype

private theorem mem_preimageMod_iff {J : Subgroup G} {Tbar : Subgroup (PQuot p J)} {x : G} :
    x ∈ preimageMod p J Tbar ↔ ∃ h : x ∈ J, (QuotientGroup.mk (⟨x, h⟩ : ↥J) : PQuot p J) ∈ Tbar := by
  unfold preimageMod
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.2, hj⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem exists_sylow_two_lift (J : Subgroup G) (Tbar : Subgroup (PQuot p J)) (hT2 : IsPGroup 2 Tbar) :
    ∃ T : Subgroup G, T ≤ J ∧ IsPGroup 2 T ∧ imageMod p J T = Tbar ∧
      ∀ U : Subgroup G, U ≤ preimageMod p J Tbar → IsPGroup 2 U →
        ∃ g ∈ preimageMod p J Tbar, U ≤ GLBConj g T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPJ : preimageMod p J Tbar ≤ J := Subgroup.map_subtype_le _
  set Ph := preimageMod p J Tbar with hPh
  let φ : ↥Ph →* PQuot p J := (QuotientGroup.mk' (GLAPPrimeCore p ↥J)).comp (Subgroup.inclusion hPJ)
  have hφ : ∀ x : ↥Ph, φ x ∈ Tbar := fun x => (mem_preimageMod_iff.1 x.2).2
  let f : ↥Ph →* ↥Tbar := φ.codRestrict Tbar hφ
  have hf : Function.Surjective f := by
    rintro ⟨tb, htb⟩
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective tb
    exact ⟨⟨(j : G), mem_preimageMod_iff.2 ⟨j.2, htb⟩⟩, Subtype.ext rfl⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 ↥Ph) := inferInstance
  have himg : (S₀ : Subgroup ↥Ph).map f = ⊤ := by
    have h1 : IsPGroup 2 (⊤ : Subgroup ↥Tbar) := fun g => by
      obtain ⟨k, hk⟩ := hT2 g.1
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    exact ((S₀.mapSurjective hf).is_maximal' h1 le_top).symm
  refine ⟨(S₀ : Subgroup ↥Ph).map Ph.subtype, (Subgroup.map_subtype_le _).trans hPJ,
    isPGroup_subgroup_map _ S₀.isPGroup', le_antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    obtain ⟨s, hs, hsj⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hj)
    have : Subgroup.inclusion hPJ s = j := Subtype.ext hsj
    rw [← this]
    exact hφ s
  · intro tb htb
    have h1 : (⟨tb, htb⟩ : ↥Tbar) ∈ (S₀ : Subgroup ↥Ph).map f := by rw [himg]; exact Subgroup.mem_top _
    obtain ⟨s, hs, hsf⟩ := Subgroup.mem_map.1 h1
    refine Subgroup.mem_map.2 ⟨Subgroup.inclusion hPJ s, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨s, hs, rfl⟩)
    · exact congrArg Subtype.val hsf
  · intro U hUP hU2
    have hU'2 : IsPGroup 2 (U.comap Ph.subtype) :=
      hU2.comap_of_injective Ph.subtype Ph.subtype_injective
    obtain ⟨Q, hUQ⟩ := hU'2.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥Ph S₀ Q
    refine ⟨((c⁻¹ : ↥Ph) : G), (c⁻¹ : ↥Ph).2, fun u hu => ?_⟩
    rw [mem_gLBConj_iff']
    have hQ : (⟨u, hUP hu⟩ : ↥Ph) ∈ (Q : Subgroup ↥Ph) := hUQ hu
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hQ
    obtain ⟨s, hs, hsu⟩ := hQ
    have h2 : ((c⁻¹ : ↥Ph) : G) * u * ((c⁻¹ : ↥Ph) : G)⁻¹ = (s : G) := by
      have h3 : (c : ↥Ph) * s * c⁻¹ = ⟨u, hUP hu⟩ := hsu
      have h4 : c⁻¹ * ⟨u, hUP hu⟩ * c = s := by rw [← h3]; group
      have h5 := congrArg Subtype.val h4
      simpa using h5
    rw [h2]
    exact Subgroup.mem_map.2 ⟨s, hs, rfl⟩

theorem exists_normalizer_lift (J : Subgroup G) (Ibar Tbar : Subgroup (PQuot p J))
    (hTI : Tbar ≤ Subgroup.centralizer (Ibar : Set (PQuot p J))) {T : Subgroup G} (hTJ : T ≤ J)
    (hT2 : IsPGroup 2 T) (hTimg : imageMod p J T = Tbar)
    (hsyl : ∀ U : Subgroup G, U ≤ preimageMod p J Tbar → IsPGroup 2 U →
      ∃ g ∈ preimageMod p J Tbar, U ≤ GLBConj g T) :
    ∃ N : Subgroup G, N ≤ J ∧ N ≤ Subgroup.normalizer (T : Set G) ∧ imageMod p J N = Ibar := by
  classical
  have hPJ : ∀ K : Subgroup (PQuot p J), preimageMod p J K ≤ J := fun K => Subgroup.map_subtype_le _
  have hTbar : ∀ t : G, ∀ ht : t ∈ T, (QuotientGroup.mk (⟨t, hTJ ht⟩ : ↥J) : PQuot p J) ∈ Tbar := by
    intro t ht
    rw [← hTimg]
    exact Subgroup.mem_map.2 ⟨⟨t, hTJ ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  refine ⟨preimageMod p J Ibar ⊓ Subgroup.normalizer (T : Set G),
    inf_le_left.trans (hPJ _), inf_le_right, le_antisymm ?_ ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    obtain ⟨hjI, -⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hj)
    obtain ⟨hjJ, hmem⟩ := mem_preimageMod_iff.1 hjI
    exact hmem
  · intro ib hib
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ib
    set U : Subgroup G := T.map (MulAut.conj (g : G)).toMonoidHom with hU
    have hUP : U ≤ preimageMod p J Tbar := by
      rintro _ ⟨t, ht, rfl⟩
      have hgt : (g : G) * t * (g : G)⁻¹ ∈ J := J.mul_mem (J.mul_mem g.2 (hTJ ht)) (J.inv_mem g.2)
      have hmem : (g : G) * t * (g : G)⁻¹ ∈ preimageMod p J Tbar := by
        refine mem_preimageMod_iff.2 ⟨hgt, ?_⟩
        have hc := Subgroup.mem_centralizer_iff.1 (hTI (hTbar t ht)) _ hib
        have h1 : (QuotientGroup.mk (⟨(g : G) * t * (g : G)⁻¹, hgt⟩ : ↥J) : PQuot p J) =
            (QuotientGroup.mk g) * (QuotientGroup.mk (⟨t, hTJ ht⟩ : ↥J)) * (QuotientGroup.mk g)⁻¹ := rfl
        rw [h1, hc, mul_assoc, mul_inv_cancel, mul_one]
        exact hTbar t ht
      exact hmem
    obtain ⟨q, hqP, hUq⟩ := hsyl U hUP (isPGroup_subgroup_map _ hT2)
    have hUeq : U = GLBConj q T :=
      Subgroup.eq_of_le_of_card_ge hUq (by
        unfold GLBConj
        rw [Subgroup.card_map_of_injective (MulAut.conj q⁻¹).injective, hU,
          Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective])
    have hqg : q * (g : G) ∈ Subgroup.normalizer (T : Set G) := by
      have hmapT : T.map (MulAut.conj (q * (g : G))).toMonoidHom ≤ T := by
        rintro _ ⟨t, ht, rfl⟩
        have h1 : (g : G) * t * (g : G)⁻¹ ∈ GLBConj q T := hUeq ▸ ⟨t, ht, rfl⟩
        have h2 := mem_gLBConj_iff'.1 h1
        have h3 : (MulAut.conj (q * (g : G))).toMonoidHom t = q * ((g : G) * t * (g : G)⁻¹) * q⁻¹ := by
          simp [MulAut.conj_apply, mul_assoc]
        rw [h3]
        exact h2
      have heq : T.map (MulAut.conj (q * (g : G))).toMonoidHom = T :=
        Subgroup.eq_of_le_of_card_ge hmapT
          (by rw [Subgroup.card_map_of_injective (MulAut.conj (q * (g : G))).injective])
      refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => hmapT ⟨x, hx, rfl⟩, fun hx => ?_⟩
      have hx' : (q * (g : G)) * x * (q * (g : G))⁻¹ ∈ T.map (MulAut.conj (q * (g : G))).toMonoidHom := by
        rw [heq]
        exact hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
      have hyx' : (MulAut.conj (q * (g : G))) y = (MulAut.conj (q * (g : G))) x := by
        rw [MulAut.conj_apply (q * (g : G)) x]
        exact hyx
      rw [← (MulAut.conj (q * (g : G))).injective hyx']
      exact hy
    obtain ⟨hqJ, hqbar⟩ := mem_preimageMod_iff.1 hqP
    have hinvT : (QuotientGroup.mk (⟨q, hqJ⟩ : ↥J) : PQuot p J)⁻¹ ∈ imageMod p J T := by
      rw [hTimg]
      exact Tbar.inv_mem hqbar
    obtain ⟨t₀, ht₀, hteq⟩ := Subgroup.mem_map.1 hinvT
    have ht₀T : (t₀ : G) ∈ T := Subgroup.mem_subgroupOf.1 ht₀
    have hnJ : (t₀ : G) * (q * (g : G)) ∈ J := J.mul_mem t₀.2 (J.mul_mem hqJ g.2)
    have hmk : (QuotientGroup.mk (⟨(t₀ : G) * (q * (g : G)), hnJ⟩ : ↥J) : PQuot p J) =
        QuotientGroup.mk g := by
      have h1 : (QuotientGroup.mk (⟨(t₀ : G) * (q * (g : G)), hnJ⟩ : ↥J) : PQuot p J) =
          (QuotientGroup.mk t₀) * ((QuotientGroup.mk (⟨q, hqJ⟩ : ↥J)) * QuotientGroup.mk g) := rfl
      have h2 : (QuotientGroup.mk t₀ : PQuot p J) = (QuotientGroup.mk (⟨q, hqJ⟩ : ↥J))⁻¹ := hteq
      rw [h1, h2, ← mul_assoc, inv_mul_cancel, one_mul]
    refine Subgroup.mem_map.2 ⟨⟨(t₀ : G) * (q * (g : G)), hnJ⟩, ?_, hmk⟩
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨mem_preimageMod_iff.2 ⟨hnJ, ?_⟩, ?_⟩)
    · rw [hmk]
      exact hib
    · exact Subgroup.mul_mem _ (Subgroup.le_normalizer ht₀T) hqg

theorem exists_pPart_lift (hp : p.Prime) (J : Subgroup G) {Ibar : Subgroup (PQuot p J)}
    (hI : GenByPElts p Ibar) {N : Subgroup G} (hNJ : N ≤ J) (hN : imageMod p J N = Ibar) :
    ∃ I : Subgroup G, I ≤ N ∧ GenByPElts p I ∧ imageMod p J I = Ibar := by
  classical
  subst hN
  set P : Set G := {g : G | g ∈ N ∧ IsPGroup p (Subgroup.zpowers g)} with hP
  have hIN : Subgroup.closure P ≤ N := (Subgroup.closure_le N).2 fun g hg => hg.1
  refine ⟨Subgroup.closure P, hIN, ?_, le_antisymm ?_ ?_⟩
  · exact Subgroup.closure_mono fun g hg => ⟨Subgroup.subset_closure hg, hg.2⟩
  · unfold imageMod
    exact Subgroup.map_mono (Subgroup.comap_mono hIN)
  · refine hI.trans ((Subgroup.closure_le _).2 ?_)
    rintro ib ⟨hib, hibp⟩
    obtain ⟨n, hnN, hn⟩ := Subgroup.mem_map.1 hib
    have hgN : (n : G) ∈ N := Subgroup.mem_subgroupOf.1 hnN
    have hg0 : orderOf (n : G) ≠ 0 := (orderOf_pos _).ne'
    have hmc : Nat.Coprime p (orderOf (n : G) / p ^ ((orderOf (n : G)).factorization p)) :=
      Nat.coprime_ordCompl hp hg0
    have hmo : orderOf (n : G) / p ^ ((orderOf (n : G)).factorization p) *
        p ^ ((orderOf (n : G)).factorization p) = orderOf (n : G) :=
      Nat.div_mul_cancel (Nat.ordProj_dvd _ p)
    set m := orderOf (n : G) / p ^ ((orderOf (n : G)).factorization p) with hm
    have hgm : IsPGroup p (Subgroup.zpowers ((n : G) ^ m)) := by
      refine isPGroup_zpowers_iff_exists_pow.2 ⟨(orderOf (n : G)).factorization p, ?_⟩
      rw [← pow_mul, hmo]
      exact pow_orderOf_eq_one _
    have hgmP : (n : G) ^ m ∈ P := ⟨N.pow_mem hgN m, hgm⟩
    obtain ⟨k, hk⟩ := isPGroup_zpowers_iff_exists_pow.1 hibp
    have hcop : Nat.Coprime m (orderOf ib) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk) (Nat.Coprime.pow_right k hmc.symm)
    obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hcop
    have hmem : ib ∈ imageMod p J (Subgroup.closure P) := by
      refine Subgroup.mem_map.2 ⟨(n ^ m) ^ r, ?_, ?_⟩
      · show (((n ^ m) ^ r : ↥J) : G) ∈ Subgroup.closure P
        rw [Subgroup.coe_pow, Subgroup.coe_pow]
        exact Subgroup.pow_mem _ (Subgroup.subset_closure hgmP) r
      · rw [map_pow, map_pow, hn, hr]
    exact hmem

theorem exists_lift_TI (hp : p.Prime) (J : Subgroup G) (Ibar Tbar : Subgroup (PQuot p J))
    (hI : GenByPElts p Ibar) (hI2 : ¬ IsPGroup 2 Ibar) (hT2 : IsPGroup 2 Tbar) (hT0 : Tbar ≠ ⊥)
    (hTI : Tbar ≤ Subgroup.centralizer (Ibar : Set (PQuot p J))) :
    ∃ T I : Subgroup G, T ≤ J ∧ I ≤ J ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧
      I ≤ Subgroup.normalizer (T : Set G) ∧ GenByPElts p I ∧ ¬ IsPGroup 2 I ∧
      imageMod p J I = Ibar := by
  obtain ⟨T, hTJ, hT2', hTimg, hsyl⟩ := exists_sylow_two_lift J Tbar hT2
  obtain ⟨N, hNJ, hNT, hNimg⟩ := exists_normalizer_lift J Ibar Tbar hTI hTJ hT2' hTimg hsyl
  obtain ⟨I, hIN, hIgen, hIimg⟩ := exists_pPart_lift hp J hI hNJ hNimg
  refine ⟨T, I, hTJ, hIN.trans hNJ, hT2', ?_, hIN.trans hNT, hIgen, ?_, hIimg⟩
  · intro h
    apply hT0
    rw [← hTimg, h]
    simp [imageMod]
  · intro h2
    apply hI2
    rw [← hIimg]
    unfold imageMod
    exact isPGroup_subgroup_map _ (h2.comap_of_injective J.subtype J.subtype_injective)

theorem l72_exists_TI (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (S : AltSetup p B x L n y J) (hn : 9 < n - p) :
    ∃ (T I : Subgroup G) (e : PQuot p J ≃* ↥(alternatingGroup (Fin (n - p)))) (m₀ : ℕ),
      T ≤ J ∧ I ≤ J ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧ I ≤ Subgroup.normalizer (T : Set G) ∧
      GenByPElts p I ∧ ¬ IsPGroup 2 I ∧ 5 ≤ m₀ ∧ m₀ ≤ n - p ∧ IsRootAlt e (imageMod p J I) m₀ := by
  obtain ⟨e⟩ := S.J_alt
  have hp3 : 3 ≤ p := by
    have := hc.prime.two_le
    have := hc.odd
    omega
  have h3 := S.three_mul_le
  have h5 : 5 ≤ max 5 p := le_max_left _ _
  have hpm : p ≤ max 5 p := le_max_right _ _
  have hM : max 5 p + 4 ≤ n - p := by
    rcases le_total p 5 with h | h
    · rw [max_eq_left h]; omega
    · rw [max_eq_right h]; omega
  obtain ⟨I', T', hroot, hgen, hI2, hT2, hT0, hTI⟩ := exists_barI_barT e hc.prime hc.odd h5 hpm hM
  obtain ⟨T, I, hTJ, hIJ, hT2', hT0', hIN, hgenI, hI2', himg⟩ :=
    exists_lift_TI hc.prime J I' T' hgen hI2 hT2 hT0 hTI
  exact ⟨T, I, e, max 5 p, hTJ, hIJ, hT2', hT0', hIN, hgenI, hI2', h5, by omega, himg ▸ hroot⟩

theorem l72_exists_a (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (S : AltSetup p B x L n y J) {T I : Subgroup G} (hT0 : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hTJ : T ≤ J) (hIJ : I ≤ J)
    (hIN : I ≤ Subgroup.normalizer (T : Set G)) (hI2 : ¬ IsPGroup 2 I) :
    ∃ a : G, a ∈ altDxy x y ∧ a ≠ 1 ∧
      (⁅I, pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓ Subgroup.centralizer ({a} : Set G)⁆ :
        Subgroup G) ≠ ⊥ := by
  have hJC : J ≤ Subgroup.centralizer (altDxy x y : Set G) := S.J_comp.1.trans inf_le_right
  have hDN : altDxy x y ≤ Subgroup.normalizer (T : Set G) := by
    intro d hd
    refine Subgroup.centralizer_le_normalizer (T : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.1 (hJC (hTJ ht)) d hd).symm
  have hD0 : altDxy x y ≠ ⊥ := by
    intro h
    have := S.card_D
    rw [h, Subgroup.card_bot] at this
    have h1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hc.prime.one_lt
    omega
  have hIND : I ≤ Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer (altDxy x y : Set G) :=
    le_inf hIN (le_trans hIJ hJC)
  obtain ⟨A, hAD, hAi, hne⟩ := GL83.I_33_3_proved G hc.charTwo p hc.prime hc.odd
    (Subgroup.normalizer (T : Set G)) (altDxy x y) I ⟨T, hT0, hT2, rfl⟩ hD0 S.isElemAbelian_D hDN
    hIND hI2
  obtain ⟨a, haA, ha1, rfl⟩ := exists_gen_of_index hc.prime S.card_D hAD hAi
  refine ⟨a, hAD haA, ha1, ?_⟩
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hne

structure L72Data (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (n : ℕ) (y : G)
    (J : Subgroup G) (a : G) (K : Subgroup G) : Prop where
  ctx : S6Ctx G p
  sstar : IsSStarMax p B x L
  setup : AltSetup p B x L n y J
  big : 9 < n - p
  a_mem : a ∈ altDxy x y
  a_ne : a ≠ 1
  single : L72Single p (altDxy x y) J K a

structure L72Shape (p n : ℕ) (J K : Subgroup G) : Prop where
  kernel : J ⊓ GLAPPrimeCoreOf p K = GLAPPrimeCoreOf p J
  root : ∃ (N' : ℕ) (e : PQuot p K ≃* ↥(alternatingGroup (Fin N'))),
    IsRootAlt e (imageMod p K J) (n - p)

theorem l72_noncentral_alt {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} {a : G} {K : Subgroup G} (i1415 : I1415At G p)
    (h : L72Data p B x L n y J a K) (hDK : ¬ altDxy x y ≤ centModSubgroup p K) :
    ∃ (b : G) (r : ℕ), b ∈ altDxy x y ∧ b ∈ Subgroup.normalizer (K : Set G) ∧ ¬ CentMod p K b ∧
      GLAPComponent p (K ⊓ Subgroup.centralizer ({b} : Set G)) J ∧ IsAltPType p K (n + r * p) := by
  classical
  have hp := h.ctx.prime
  obtain ⟨b, hbD, hb, hDab⟩ :=
    exists_pair_of_card_sq hp h.setup.card_D h.a_mem h.a_ne h.setup.isElemAbelian_D
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := h.single.comp.1
  have haK : CentMod p K a := centMod_of_mem_centralizer
    (Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKa hk))
  have hbn : ¬ CentMod p K b := by
    intro hb'
    apply hDK
    rw [hDab]
    exact sup_le (Subgroup.zpowers_le.2 (centMod_iff.1 haK))
      (Subgroup.zpowers_le.2 (centMod_iff.1 hb'))
  have hbN : b ∈ Subgroup.normalizer (K : Set G) := h.single.norm hbD
  have hbp : b ^ p = 1 := h.setup.isElemAbelian_D.2 b hbD
  have hJb : GLAPComponent p (K ⊓ Subgroup.centralizer ({b} : Set G)) J := by
    have h2 : K ⊓ Subgroup.centralizer (altDxy x y : Set G) =
        K ⊓ Subgroup.centralizer ({b} : Set G) := by
      rw [centralizer_eq_inf_of_eq_sup hDab]
      ext g
      simp only [Subgroup.mem_inf]
      exact ⟨fun ⟨hk, _, hb⟩ => ⟨hk, hb⟩, fun ⟨hk, hb⟩ => ⟨hk, hKa hk, hb⟩⟩
    have h1 := h.single.J_comp
    rwa [h2] at h1
  obtain ⟨k, hk0, hk⟩ := i1415 hp h.ctx.odd (Subgroup.centralizer ({a} : Set G)) K J b (n - p)
    (kGroup_centralizer h.ctx h.a_ne) h.single.comp hbN hbp hbn hJb h.big h.setup.J_alt
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine ⟨b, k', hbD, hbN, hbn, hJb, ?_⟩
  have h3 := h.setup.three_mul_le
  have h4 : n - p + (k' + 1) * p = n + k' * p := by
    have : (k' + 1) * p = k' * p + p := by ring
    omega
  rwa [h4] at hk

theorem map_fixSubgroup_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) (α : MulAut A) :
    (fixSubgroup α).map e.toMonoidHom = fixSubgroup (MulAut.congr e α) := by
  ext z
  rw [Subgroup.mem_map, mem_fixSubgroup]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 : α w = w := mem_fixSubgroup.1 hw
    show e (α (e.symm (e w))) = e w
    rw [e.symm_apply_apply, h1]
  · intro h
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    rw [mem_fixSubgroup]
    have h2 : e (α (e.symm z)) = z := h
    apply e.injective
    rw [h2, e.apply_symm_apply]

theorem l72_inner_of_alt (hp : p.Prime) (hp2 : p ≠ 2) {X K : Subgroup G} {b : G} {N' : ℕ}
    (hK : GLAPComponent p X K) (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbp : b ^ p = 1)
    (hbn : ¬ CentMod p K b) (e : PQuot p K ≃* ↥(alternatingGroup (Fin N'))) :
    ∃ x₀ : ↥(alternatingGroup (Fin N')), x₀ ^ p = 1 ∧
      ∀ J : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({b} : Set G)) J →
        (imageMod p K J).map e.toMonoidHom = altFix (x₀ : Equiv.Perm (Fin N')) ∧
        5 ≤ N' - (x₀ : Equiv.Perm (Fin N')).support.card ∧
        p ∣ Nat.card ↥(altFix (x₀ : Equiv.Perm (Fin N'))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hK
  haveI : Nontrivial (PQuot p K) := isQuasisimple_nontrivial hq
  haveI : Group.IsPerfect (PQuot p K) := ⟨hq.1⟩
  have hN5 : 5 ≤ N' := by
    by_contra hlt
    haveI : Group.IsSolvable (alternatingGroup (Fin N')) :=
      alternatingGroup.isSolvable (by simpa using (by omega : N' ≤ 4))
    haveI : Group.IsSolvable (PQuot p K) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.IsPerfect.not_isSolvable (PQuot p K) inferInstance
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (PQuot p K), α = barAut p K ⟨b, hb⟩ := ⟨_, rfl⟩
  have hα : α ^ p = 1 := by
    have h1 : (⟨b, hb⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ p = 1 := Subtype.ext hbp
    rw [hαdef, ← map_pow, h1, map_one]
  have hα1 : α ≠ 1 := fun h =>
    hbn ((chev_barAut_eq_one_iff_centMod hb).1 (by rw [← hαdef]; exact h))
  have hβ : (MulAut.congr e α) ^ p = 1 := by rw [← map_pow, hα, map_one]
  have hβ1 : MulAut.congr e α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e).injective (by rw [h, map_one]))
  obtain ⟨x₀, -, hx₀p, hx₀⟩ := AltDown.exists_conj_of_alt hN5 hp hp2 hβ hβ1
  refine ⟨x₀, hx₀p, fun J hJ => ?_⟩
  have hap : IsPGroup p (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hbp
  have hJc := glaPComponent_map_pQuotHom hp hb hap hJ
  have hJc' := glaPComponent_map_mulEquiv hp e hJc
  have hfix : (fixSubgroup (barAut p K ⟨b, hb⟩)).map e.toMonoidHom =
      Subgroup.centralizer ({x₀} : Set ↥(alternatingGroup (Fin N'))) := by
    rw [← hαdef, map_fixSubgroup_congr, hx₀, ← centralizer_singleton_eq_fixSubgroup_conj]
  rw [hfix] at hJc'
  have hI : GLAPComponent p (Subgroup.centralizer ({x₀} : Set ↥(alternatingGroup (Fin N'))))
      ((imageMod p K J).map e.toMonoidHom) := hJc'
  obtain ⟨hIeq, h5⟩ := altFix_unique_of_component hp hp2 hx₀p hI
  refine ⟨hIeq, h5, ?_⟩
  have hnc := AltDown.not_coprime_card_of_glaPComponent hp hI
  rw [hIeq] at hnc
  exact not_not.1 fun h => hnc ((Nat.Prime.coprime_iff_not_dvd hp).2 h)

theorem l72_root_of_fix (hp : p.Prime) (hp2 : p ≠ 2) {K J : Subgroup G} {N' m : ℕ} (hJK : J ≤ K)
    (e : PQuot p K ≃* ↥(alternatingGroup (Fin N'))) {x₀ : ↥(alternatingGroup (Fin N'))} (hm : 5 ≤ m)
    (hJa : IsAltPType p J m)
    (hF : (imageMod p K J).map e.toMonoidHom = altFix (x₀ : Equiv.Perm (Fin N')))
    (h5 : 5 ≤ N' - (x₀ : Equiv.Perm (Fin N')).support.card)
    (hpd : p ∣ Nat.card ↥(altFix (x₀ : Equiv.Perm (Fin N')))) :
    IsRootAlt e (imageMod p K J) m ∧ J ⊓ GLAPPrimeCoreOf p K = GLAPPrimeCoreOf p J := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ : ∃ k, N' - (x₀ : Equiv.Perm (Fin N')).support.card = k := ⟨_, rfl⟩
  have hk5 : 5 ≤ k := hk ▸ h5
  obtain ⟨eF⟩ := nonempty_altFix_equiv (x₀ : Equiv.Perm (Fin N')) hk
  have hkc : 5 ≤ Nat.card (Fin k) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hk5
  haveI : IsSimpleGroup (alternatingGroup (Fin k)) := alternatingGroup.isSimpleGroup hkc
  haveI : IsSimpleGroup ↥(altFix (x₀ : Equiv.Perm (Fin N'))) := eF.isSimpleGroup
  let eJ : ↥(imageMod p K J) ≃* ↥(altFix (x₀ : Equiv.Perm (Fin N'))) :=
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hF)
  haveI : IsSimpleGroup ↥(imageMod p K J) := eJ.isSimpleGroup
  have hpJ : p ∣ Nat.card ↥(imageMod p K J) := by rw [Nat.card_congr eJ.toEquiv]; exact hpd
  obtain ⟨e1⟩ := hJa
  obtain ⟨e2⟩ := nonempty_pQuot_equiv_imageMod hp hJK
  obtain ⟨e3⟩ := nonempty_pQuot_equiv_of_simple hp hpJ
  have eAm : ↥(alternatingGroup (Fin m)) ≃* ↥(alternatingGroup (Fin k)) :=
    e1.symm.trans (e2.trans (e3.trans (eJ.trans eF)))
  have hmk : m = k := by
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
    have h1 : 2 * Nat.card (alternatingGroup (Fin m)) = m.factorial := by
      rw [two_mul_nat_card_alternatingGroup (α := Fin m), Nat.card_perm,
        Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]
    have h2 : 2 * Nat.card (alternatingGroup (Fin k)) = k.factorial := by
      rw [two_mul_nat_card_alternatingGroup (α := Fin k), Nat.card_perm,
        Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
    have hc := Nat.card_congr eAm.toEquiv
    have : m.factorial = k.factorial := by rw [← h1, ← h2, hc]
    exact (Nat.factorial_inj (by omega)).1 this
  subst hmk
  have hcoreJ : GLAPPrimeCore p ↥(imageMod p K J) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥(imageMod p K J)) with h | h
    · exact h
    · exfalso
      have hcop := coprime_card_gLAPPrimeCore_aux p ↥(imageMod p K J)
      rw [h, Subgroup.card_top] at hcop
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpJ)
  refine ⟨⟨⟨eJ.trans eF⟩, ?_⟩, ?_⟩
  · have h1 : movedLettersOf e (imageMod p K J) =
        movedLettersOf (MulEquiv.refl _) (altFix (x₀ : Equiv.Perm (Fin N'))) := by
      rw [← hF]
      ext i
      constructor
      · rintro ⟨h, hh, hi⟩
        exact ⟨e h, ⟨h, hh, rfl⟩, hi⟩
      · rintro ⟨f, ⟨h, hh, rfl⟩, hi⟩
        exact ⟨h, hh, hi⟩
    unfold MovesExactly
    rw [h1]
    have hcard : ((x₀ : Equiv.Perm (Fin N')).supportᶜ).card = m := by
      rw [Finset.card_compl, Fintype.card_fin]; exact hk
    rw [altFix_eq_altOn, movedLettersOf_altOn (by omega), Set.ncard_coe_finset, hcard]
  ·
    have hker := coprime_card_inf_ker_pQuotHom hp K (J.subgroupOf K)
    have hcore := glaPPrimeCore_map_subgroupMap hp (pQuotHom p K) (J.subgroupOf K) hker
    apply le_antisymm
    · intro g hg
      have hgJ : g ∈ J := hg.1
      let N₀ : Subgroup ↥J := (J ⊓ GLAPPrimeCoreOf p K).subgroupOf J
      have hN₀n : N₀.Normal := ⟨fun n hn j => by
        refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩
        · exact J.mul_mem (J.mul_mem j.2 (Subgroup.mem_subgroupOf.1 hn).1) (J.inv_mem j.2)
        · have := chev_conj_mem_glaPPrimeCoreOf (hJK j.2) (Subgroup.mem_subgroupOf.1 hn).2
          simpa using this⟩
      have hN₀c : Nat.Coprime p (Nat.card N₀) := by
        refine Nat.Coprime.coprime_dvd_right ?_ ((Nat.Prime.coprime_iff_not_dvd hp).2
          (not_dvd_card_glaPPrimeCoreOf hp K))
        rw [← Subgroup.card_map_of_injective J.subtype_injective, Subgroup.subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le (by simp)
      have hN₀le : N₀ ≤ GLAPPrimeCore p ↥J := le_sSup ⟨hN₀n, hN₀c⟩
      exact ⟨⟨g, hgJ⟩, hN₀le (Subgroup.mem_subgroupOf.2 hg), rfl⟩
    · intro g hg
      have hgJ : g ∈ J := Subgroup.map_subtype_le _ hg
      refine ⟨hgJ, ?_⟩
      rw [← map_subtype_glaPPrimeCoreOf_subgroupOf p hJK] at hg
      obtain ⟨n, hn, rfl⟩ := hg
      obtain ⟨o, ho, rfl⟩ := hn
      have h1 : (pQuotHom p K).subgroupMap (J.subgroupOf K) o ∈
          GLAPPrimeCore p ↥((J.subgroupOf K).map (pQuotHom p K)) := by
        rw [← hcore]
        exact Subgroup.mem_map_of_mem _ ho
      have hcoreJ' : GLAPPrimeCore p ↥((J.subgroupOf K).map (pQuotHom p K)) = ⊥ := hcoreJ
      rw [hcoreJ', Subgroup.mem_bot] at h1
      have h2 : pQuotHom p K ((o : ↥(J.subgroupOf K)) : ↥K) = 1 := congrArg Subtype.val h1
      have h3 : ((o : ↥(J.subgroupOf K)) : ↥K) ∈ GLAPPrimeCore p ↥K := by
        rw [← ker_pQuotHom]; exact h2
      exact Subgroup.mem_map.2 ⟨_, h3, rfl⟩

theorem l72_root_of_alt (hp : p.Prime) (hp2 : p ≠ 2) {X K J : Subgroup G} {b : G} {m N' : ℕ}
    (hK : GLAPComponent p X K) (hb : b ∈ Subgroup.normalizer (K : Set G))
    (hbp : b ^ p = 1) (hbn : ¬ CentMod p K b)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({b} : Set G)) J) (hm : 5 ≤ m)
    (hJa : IsAltPType p J m) (e : PQuot p K ≃* ↥(alternatingGroup (Fin N'))) :
    IsRootAlt e (imageMod p K J) m ∧ J ⊓ GLAPPrimeCoreOf p K = GLAPPrimeCoreOf p J := by
  obtain ⟨x₀, -, hx₀⟩ := l72_inner_of_alt hp hp2 hK hb hbp hbn e
  obtain ⟨hF, h5, hpd⟩ := hx₀ J hJ
  exact l72_root_of_fix hp hp2 (hJ.1.trans inf_le_left) e hm hJa hF h5 hpd

theorem imageMod_eq_top_of_sup {J K : Subgroup G} (hJK : J ≤ K)
    (hcov : J ⊔ GLAPPrimeCoreOf p K = K) : imageMod p K J = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨⟨k, hkK⟩, rfl⟩ := QuotientGroup.mk_surjective z
  have hk : k ∈ (J ⊔ GLAPPrimeCoreOf p K : Subgroup G) := hcov.symm ▸ hkK
  obtain ⟨j, hj, o, ho, hjo⟩ := exists_mul_of_mem_sup_of_le_normalizer
    (hJK.trans (le_normalizer_glaPPrimeCoreOf p K)) hk
  refine ⟨⟨j, hJK hj⟩, Subgroup.mem_subgroupOf.2 hj, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
  have h1 : (⟨j, hJK hj⟩ : ↥K)⁻¹ * ⟨k, hkK⟩ =
      ⟨o, (Subgroup.map_subtype_le _ ho : o ∈ K)⟩ := by
    apply Subtype.ext
    show j⁻¹ * k = o
    rw [hjo]
    group
  rw [h1]
  exact (chev_mem_glaPPrimeCoreOf_iff (Subgroup.map_subtype_le _ ho)).1 ho

theorem l72_shape_central {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} {a : G} {K : Subgroup G} (h : L72Data p B x L n y J a K)
    (hDK : altDxy x y ≤ centModSubgroup p K) :
    J ⊔ GLAPPrimeCoreOf p K = K ∧ L72Shape p n J K := by
  classical
  have hp := h.ctx.prime
  have hJK : J ≤ K := h.single.J_le
  have hcov : J ⊔ GLAPPrimeCoreOf p K = K :=
    S3.cover_of_centMod hp h.single.comp (isPGroup_of_isElemAbelian h.setup.isElemAbelian_D) hDK
      h.single.J_comp
  obtain ⟨hker, ⟨e₂⟩⟩ := cover_facts hp hJK hcov
  obtain ⟨e₁⟩ := h.setup.J_alt
  have hn3 : 3 ≤ n - p := by
    have := h.big
    omega
  have htop : imageMod p K J = ⊤ := imageMod_eq_top_of_sup hJK hcov
  refine ⟨hcov, hker.symm, n - p, e₂.symm.trans e₁, ?_⟩
  rw [htop]
  exact isRootAlt_top hn3 _

theorem l72_shape {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K : Subgroup G} (i1415 : I1415At G p) (h : L72Data p B x L n y J a K) :
    L72Shape p n J K := by
  by_cases hDK : altDxy x y ≤ centModSubgroup p K
  · exact (l72_shape_central h hDK).2
  · obtain ⟨b, r, hbD, hbN, hbn, hJb, hKa⟩ := l72_noncentral_alt i1415 h hDK
    obtain ⟨eK⟩ := hKa
    have hb1 : b ^ p = 1 := h.setup.isElemAbelian_D.2 b hbD
    have hp3 : 5 ≤ n - p := by
      have := h.big
      omega
    obtain ⟨hroot, hker⟩ := l72_root_of_alt h.ctx.prime h.ctx.odd h.single.comp hbN hb1 hbn hJb
      hp3 h.setup.J_alt eK
    exact ⟨hker, _, eK, hroot⟩

theorem exists_alt_embedding_support {k N : ℕ} (hk : k = 5 ∨ 7 ≤ k)
    (P : ↥(alternatingGroup (Fin k)) →* ↥(alternatingGroup (Fin N))) (hP : Function.Injective P)
    (Ω : Finset (Fin N)) (hΩ : Ω.card = k)
    (hsupp : ∀ g, ((P g : ↥(alternatingGroup (Fin N))) : Equiv.Perm (Fin N)).support ⊆ Ω) :
    ∃ f : Fin k → Fin N, Function.Injective f ∧ Set.range f = (Ω : Set (Fin N)) ∧
      ∀ (g : ↥(alternatingGroup (Fin k))) (i : Fin k),
        ((P g : ↥(alternatingGroup (Fin N))) : Equiv.Perm (Fin N)) (f i) =
          f ((g : Equiv.Perm (Fin k)) i) := by
  classical
  obtain ⟨e₀⟩ : Nonempty (Fin k ≃ ↥Ω) := ⟨(Finset.equivFinOfCardEq hΩ).symm⟩
  have hrange : ∀ g, P g ∈ (alternatingGroup.ofSubtype Ω).range := fun g =>
    (alternatingGroup.mem_range_ofSubtype_iff Ω (P g)).2 (hsupp g)
  let ι : (alternatingGroup.ofSubtype Ω).range ≃* alternatingGroup ↥Ω :=
    (MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).symm
  let ψ₀ : ↥(alternatingGroup (Fin k)) →* alternatingGroup ↥Ω :=
    ι.toMonoidHom.comp (P.codRestrict _ hrange)
  have hψ₀ : ∀ g, alternatingGroup.ofSubtype Ω (ψ₀ g) = P g := fun g =>
    MonoidHom.apply_ofInjective_symm alternatingGroup.ofSubtype_injective ⟨P g, hrange g⟩
  have hψ₀inj : Function.Injective ψ₀ := fun g g' h => hP (by rw [← hψ₀ g, ← hψ₀ g', h])
  have hbij : Function.Bijective ψ₀ :=
    hψ₀inj.bijective_of_nat_card_le (by rw [Nat.card_congr e₀.altCongrHom.toEquiv])
  let ψ : MulAut ↥(alternatingGroup (Fin k)) :=
    (MulEquiv.ofBijective ψ₀ hbij).trans e₀.altCongrHom.symm
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation hk ψ
  have hψg : ∀ g, e₀.altCongrHom (ψ g) = ψ₀ g := fun g => e₀.altCongrHom.apply_symm_apply _
  have hfin : ∀ g j, ((P g : ↥(alternatingGroup (Fin N))) : Equiv.Perm (Fin N)) (e₀ j : Fin N) =
      (e₀ ((ψ g : Equiv.Perm (Fin k)) j) : Fin N) := by
    intro g j
    rw [← hψ₀ g, alternatingGroup.coe_ofSubtype, Equiv.Perm.ofSubtype_apply_coe, ← hψg g]
    simp [Equiv.altCongrHom_apply_coe]
  refine ⟨fun i => (e₀ (σ i) : Fin N), ?_, ?_, ?_⟩
  · intro i j hij
    exact σ.injective (e₀.injective (Subtype.ext hij))
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e₀ (σ i)).2
    · intro hx
      exact ⟨σ.symm (e₀.symm ⟨x, hx⟩), by simp⟩
  · intro g i
    rw [hfin g (σ i), hσ g]
    simp

theorem isRootAlt_transport {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] {k N m₀ : ℕ} (hk : 7 ≤ k)
    (hm : 3 ≤ m₀) (e₁ : Q₁ ≃* ↥(alternatingGroup (Fin k))) (e₂ : Q₂ ≃* ↥(alternatingGroup (Fin N)))
    {H : Subgroup Q₂} (hH : IsRootAlt e₂ H k) (θ : Q₁ ≃* ↥H) {T : Subgroup Q₁}
    (hT : IsRootAlt e₁ T m₀) :
    IsRootAlt e₂ (T.map (H.subtype.comp θ.toMonoidHom)) m₀ := by
  classical
  set φ : Q₁ →* Q₂ := H.subtype.comp θ.toMonoidHom with hφ
  have hφinj : Function.Injective φ := H.subtype_injective.comp θ.injective
  refine ⟨?_, ?_⟩
  · obtain ⟨u⟩ := hT.1
    exact ⟨(Subgroup.equivMapOfInjective T φ hφinj).symm.trans u⟩
  ·
    let P : ↥(alternatingGroup (Fin k)) →* ↥(alternatingGroup (Fin N)) :=
      (e₂.toMonoidHom.comp φ).comp e₁.symm.toMonoidHom
    have hPinj : Function.Injective P := (e₂.injective.comp hφinj).comp e₁.symm.injective
    have hPe : ∀ t : Q₁, P (e₁ t) = e₂ (φ t) := fun t => by
      show e₂ (φ (e₁.symm (e₁ t))) = _
      rw [e₁.symm_apply_apply]
    set Ω : Finset (Fin N) := (Set.toFinite (movedLettersOf e₂ H)).toFinset with hΩ
    have hΩcard : Ω.card = k := by
      rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
      exact hH.2
    have hΩmem : ∀ x, x ∈ Ω ↔ x ∈ movedLettersOf e₂ H := fun x => Set.Finite.mem_toFinset _
    have hsupp : ∀ g, ((P g : ↥(alternatingGroup (Fin N))) : Equiv.Perm (Fin N)).support ⊆ Ω := by
      intro g x hx
      rw [hΩmem]
      exact ⟨φ (e₁.symm g), (θ (e₁.symm g)).2, Equiv.Perm.mem_support.1 hx⟩
    obtain ⟨f, hfinj, hfrange, hf⟩ := exists_alt_embedding_support (Or.inr hk) P hPinj Ω hΩcard hsupp
    have himage : movedLettersOf e₂ (T.map φ) = f '' movedLettersOf e₁ T := by
      ext x
      constructor
      · rintro ⟨t', ⟨t, ht, rfl⟩, hx⟩
        have hxΩ : x ∈ Ω := by
          rw [← hPe t] at hx
          exact hsupp _ (Equiv.Perm.mem_support.2 hx)
        obtain ⟨i, rfl⟩ : x ∈ Set.range f := by rw [hfrange]; exact hxΩ
        refine ⟨i, ⟨t, ht, fun hti => hx ?_⟩, rfl⟩
        rw [← hPe t, hf, hti]
      · rintro ⟨i, ⟨t, ht, hti⟩, rfl⟩
        refine ⟨φ t, ⟨t, ht, rfl⟩, fun hx => hti (hfinj ?_)⟩
        rw [← hf, hPe t]
        exact hx
    unfold MovesExactly
    rw [himage, Set.ncard_image_of_injective _ hfinj]
    exact hT.2

theorem l72_equiv_of_kernel {J K : Subgroup G} (hJK : J ≤ K)
    (hker : J ⊓ GLAPPrimeCoreOf p K = GLAPPrimeCoreOf p J) :
    ∃ θ : PQuot p J ≃* ↥(imageMod p K J), ∀ j : ↥J,
      ((θ (QuotientGroup.mk j) : ↥(imageMod p K J)) : PQuot p K) =
        QuotientGroup.mk (⟨(j : G), hJK j.2⟩ : ↥K) := by
  classical
  let ρ : ↥J →* ↥(imageMod p K J) :=
    ((pQuotHom p K).subgroupMap (J.subgroupOf K)).comp (Subgroup.subgroupOfEquivOfLe hJK).symm.toMonoidHom
  have hρ : Function.Surjective ρ :=
    ((pQuotHom p K).subgroupMap_surjective (J.subgroupOf K)).comp
      (Subgroup.subgroupOfEquivOfLe hJK).symm.surjective
  have hρker : ρ.ker = GLAPPrimeCore p ↥J := by
    ext j
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : pQuotHom p K ⟨(j : G), hJK j.2⟩ = 1 := congrArg Subtype.val h
      have h2 : (⟨(j : G), hJK j.2⟩ : ↥K) ∈ GLAPPrimeCore p ↥K := by rw [← ker_pQuotHom]; exact h1
      have h3 : (j : G) ∈ GLAPPrimeCoreOf p K := Subgroup.mem_map.2 ⟨_, h2, rfl⟩
      have h4 : (j : G) ∈ GLAPPrimeCoreOf p J := hker ▸ ⟨j.2, h3⟩
      exact (chev_mem_glaPPrimeCoreOf_iff j.2).1 h4
    · intro h
      have h4 : (j : G) ∈ GLAPPrimeCoreOf p J := Subgroup.mem_map.2 ⟨j, h, rfl⟩
      have h3 : (j : G) ∈ GLAPPrimeCoreOf p K := (hker.symm ▸ h4 : (j : G) ∈ J ⊓ GLAPPrimeCoreOf p K).2
      have h2 := (chev_mem_glaPPrimeCoreOf_iff (hJK j.2)).1 h3
      have h1 : pQuotHom p K ⟨(j : G), hJK j.2⟩ = 1 := by
        rw [← MonoidHom.mem_ker, ker_pQuotHom]; exact h2
      exact Subtype.ext h1
  let θ : PQuot p J ≃* ↥(imageMod p K J) :=
    (QuotientGroup.quotientMulEquivOfEq hρker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
  exact ⟨θ, fun j => rfl⟩

theorem l72_transport {I J K : Subgroup G} {n m₀ : ℕ} (hI : I ≤ J) (hJ : J ≤ K) (hn : 6 < n - p)
    (hm : 3 ≤ m₀) (hSh : L72Shape p n J K) (eJ : PQuot p J ≃* ↥(alternatingGroup (Fin (n - p))))
    (hroot : IsRootAlt eJ (imageMod p J I) m₀) :
    ∃ (N' : ℕ) (e : PQuot p K ≃* ↥(alternatingGroup (Fin N'))),
      m₀ ≤ N' ∧ IsRootAlt e (imageMod p K I) m₀ := by
  obtain ⟨N', eK, hKroot⟩ := hSh.root
  obtain ⟨θ, hθ⟩ := l72_equiv_of_kernel hJ hSh.kernel
  have himg : (imageMod p J I).map ((imageMod p K J).subtype.comp θ.toMonoidHom) =
      imageMod p K I := by
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.1 hw
      exact ⟨⟨(i : G), hJ i.2⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hi),
        (hθ i).symm⟩
    · intro hz
      obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.1 hz
      have hiI : (i : G) ∈ I := Subgroup.mem_subgroupOf.1 hi
      exact ⟨QuotientGroup.mk (⟨(i : G), hI hiI⟩ : ↥J),
        Subgroup.mem_map.2 ⟨⟨(i : G), hI hiI⟩, Subgroup.mem_subgroupOf.2 hiI, rfl⟩, hθ _⟩
  have h1 := isRootAlt_transport (by omega) hm eJ eK hKroot θ hroot
  rw [himg] at h1
  refine ⟨N', eK, ?_, h1⟩
  have := h1.2
  unfold MovesExactly at this
  rw [← this]
  exact (Set.ncard_le_ncard (Set.subset_univ _)).trans (by simp)

theorem l72_imageMod_facts {K I S : Subgroup G} (hIK : I ≤ K) (hSK : S ≤ K) (hS2 : IsPGroup 2 S)
    (hIS : I ≤ Subgroup.normalizer (S : Set G)) :
    IsPGroup 2 (imageMod p K S) ∧
      imageMod p K I ≤ Subgroup.normalizer ((imageMod p K S : Subgroup (PQuot p K)) : Set (PQuot p K)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨z, hz⟩
    obtain ⟨s, hs, rfl⟩ := hz
    obtain ⟨k, hk⟩ := hS2 ⟨(s : G), Subgroup.mem_subgroupOf.1 hs⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : s ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    show (QuotientGroup.mk' (GLAPPrimeCore p ↥K) s) ^ 2 ^ k = 1
    rw [← map_pow, h1, map_one]
  · rintro _ ⟨i, hi, rfl⟩
    have hiN : (i : G) ∈ Subgroup.normalizer (S : Set G) := hIS (Subgroup.mem_subgroupOf.1 hi)
    have hiK : (i : G) ∈ K := i.2
    have key : ∀ (j : ↥K), (j : G) ∈ I → ∀ z : PQuot p K, z ∈ imageMod p K S →
        QuotientGroup.mk' (GLAPPrimeCore p ↥K) j * z * (QuotientGroup.mk' (GLAPPrimeCore p ↥K) j)⁻¹ ∈
          imageMod p K S := by
      intro j hj z hz
      obtain ⟨s, hs, rfl⟩ := hz
      refine ⟨j * s * j⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
      have := (Subgroup.mem_normalizer_iff.1 (hIS hj) (s : G)).1 (Subgroup.mem_subgroupOf.1 hs)
      simpa using this
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact key i (Subgroup.mem_subgroupOf.1 hi) z
    · intro hz
      have h2 := key i⁻¹ (by simpa using I.inv_mem (Subgroup.mem_subgroupOf.1 hi)) _ hz
      simpa [mul_assoc] using h2

theorem l72_comm_le_core {K I S : Subgroup G} (hIK : I ≤ K) (hSK : S ≤ K)
    (hcen : imageMod p K I ≤ Subgroup.centralizer ((imageMod p K S : Subgroup (PQuot p K)) :
      Set (PQuot p K))) : (⁅S, I⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p K := by
  rw [Subgroup.commutator_le]
  intro s hs i hi
  have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨i, hIK hi⟩) ∈ imageMod p K I :=
    ⟨⟨i, hIK hi⟩, Subgroup.mem_subgroupOf.2 hi, rfl⟩
  have h2 : (QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨s, hSK hs⟩) ∈ imageMod p K S :=
    ⟨⟨s, hSK hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.1 (hcen h1) _ h2
  have hcomm : (⁅(⟨s, hSK hs⟩ : ↥K), (⟨i, hIK hi⟩ : ↥K)⁆ : ↥K) ∈ GLAPPrimeCore p ↥K := by
    rw [← QuotientGroup.ker_mk' (GLAPPrimeCore p ↥K), MonoidHom.mem_ker, commutatorElement_def,
      map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc' : (QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨s, hSK hs⟩) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨i, hIK hi⟩) =
        (QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨i, hIK hi⟩) *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨s, hSK hs⟩) := hc
    rw [hc']
    group
  exact (chev_mem_glaPPrimeCoreOf_iff (K.mul_mem (K.mul_mem (K.mul_mem (hSK hs) (hIK hi))
    (K.inv_mem (hSK hs))) (K.inv_mem (hIK hi)))).2 hcomm

theorem l72_S_le_core {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K : Subgroup G} (i1415 : I1415At G p) (i2013 : I2013At)
    (h : L72Data p B x L n y J a K) {I S : Subgroup G} {e : PQuot p J ≃* ↥(alternatingGroup (Fin (n - p)))} {m₀ : ℕ}
    (hIJ : I ≤ J) (hSK : S ≤ K) (hS2 : IsPGroup 2 S) (hIS : I ≤ Subgroup.normalizer (S : Set G))
    (hSI : S ≤ ⁅S, I⁆) (h5 : 5 ≤ m₀) (hroot : IsRootAlt e (imageMod p J I) m₀) :
    S ≤ (⁅GLAPPrimeCoreOf p K, K⁆ : Subgroup G) := by
  have hIK : I ≤ K := hIJ.trans h.single.J_le
  obtain ⟨N', eK, hmN, hrootK⟩ := l72_transport hIJ h.single.J_le (by have := h.big; omega)
    (by omega) (l72_shape i1415 h) e hroot
  obtain ⟨hT2, hnorm⟩ := l72_imageMod_facts hIK hSK hS2 hIS
  have hcen := i2013 (PQuot p K) N' m₀ eK (imageMod p K I) h5 hmN hrootK (imageMod p K S) hT2
    hnorm
  have hcomm := l72_comm_le_core hIK hSK hcen
  calc S ≤ ⁅S, I⁆ := hSI
    _ ≤ ⁅GLAPPrimeCoreOf p K, K⁆ := Subgroup.commutator_mono (hSI.trans hcomm) hIK

def L72Bstar (p : ℕ) (B : Subgroup G) (a : G) (K : Subgroup G) : Prop :=
  ∃ B' F : Subgroup G, IsElemAbelian p B' ∧ a ∈ B' ∧ B' ≤ Subgroup.centralizer ({a} : Set G) ∧
    B' ≤ Subgroup.normalizer (K : Set G) ∧ CFSG.Open.pRank p B ≤ CFSG.Open.pRank p B' ∧
    F ≤ B' ∧ IsElemAbelian p F ∧ Nat.card ↥F = p ^ 3 ∧
    GLAPLayer p (K ⊓ Subgroup.centralizer (F : Set G)) ≠ ⊥

@[expose] def fixedBar (p : ℕ) (K F : Subgroup G) : Subgroup (PQuot p K) where
  carrier := {z | ∀ f : ↥(Subgroup.normalizer (K : Set G)), (f : G) ∈ F → barAut p K f z = z}
  one_mem' := fun f _ => map_one _
  mul_mem' := fun {a b} ha hb f hf => by rw [map_mul, ha f hf, hb f hf]
  inv_mem' := fun {a} ha f hf => by rw [map_inv, ha f hf]

theorem eq_one_of_centMod_pElt (hp : p.Prime) {K : Subgroup G}
    (hZ : Subgroup.center (PQuot p K) = ⊥) {d : G} (hdK : d ∈ K) (hdp : d ^ p = 1)
    (hcm : CentMod p K d) : d = 1 := by
  have hdO : d ∈ GLAPPrimeCoreOf p K := mem_glaPPrimeCoreOf_of_centMod hZ hdK hcm
  have hdvd : orderOf d ∣ Nat.card ↥(GLAPPrimeCoreOf p K) := Subgroup.orderOf_dvd_natCard _ hdO
  have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p K)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp K)
  exact orderOf_eq_one_iff.1
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hdp) hdvd)

theorem center_pQuot_eq_bot_of_equiv {K : Subgroup G} {N : ℕ} (hN : 4 ≤ N)
    (e : PQuot p K ≃* ↥(alternatingGroup (Fin N))) : Subgroup.center (PQuot p K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hZ := alternatingGroup.center_eq_bot (α := Fin N) (by simpa using hN)
  have : e z ∈ Subgroup.center (alternatingGroup (Fin N)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨w, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
  rw [hZ, Subgroup.mem_bot] at this
  exact e.injective (by rw [this, map_one])

theorem l72_central_D_inf_K {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} {a : G} {K : Subgroup G} (h : L72Data p B x L n y J a K)
    (hDK : altDxy x y ≤ centModSubgroup p K) : altDxy x y ⊓ K = ⊥ := by
  obtain ⟨-, hSh⟩ := l72_shape_central h hDK
  obtain ⟨N', e, hroot⟩ := hSh.root
  have hN' : n - p ≤ N' := by
    have := hroot.2
    unfold MovesExactly at this
    rw [← this]
    exact (Set.ncard_le_ncard (Set.subset_univ _)).trans (by simp)
  have hZ := center_pQuot_eq_bot_of_equiv (by have := h.big; omega) e
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  exact eq_one_of_centMod_pElt h.ctx.prime hZ hd.2 (h.setup.isElemAbelian_D.2 d hd.1)
    (centMod_iff.2 (hDK hd.1))

theorem l72_c1_E {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K : Subgroup G} (h : L72Data p B x L n y J a K)
    (e : PQuot p J ≃* ↥(alternatingGroup (Fin (n - p)))) :
    ∃ E : Subgroup G, E ≤ J ∧ IsElemAbelian p E ∧ Nat.card ↥E = p ^ CFSG.Open.pRank p J ∧
      ∃ z ∈ E, orderOf z = p ∧ IsPCycleMod p J (n - p) e z := by
  have hp := h.ctx.prime
  have h3 := h.setup.three_mul_le
  have hpn : p ≤ n - p := by omega
  obtain ⟨σ, hσ⟩ := exists_pCycle hp h.ctx.odd hpn
  obtain ⟨z, hzJ, hzo, hzσ⟩ := exists_cycle_lift hp e σ hσ
  obtain ⟨Eb, hEbel, hEbc, hσEb, -⟩ := exists_elemAbelian_pCycle hp h.ctx.odd hpn σ hσ
  have hzmem : e (QuotientGroup.mk (⟨z, hzJ⟩ : ↥J) : PQuot p J) ∈ Eb := by
    rw [permOfMod_of_mem e hzJ] at hzσ
    have : e (QuotientGroup.mk (⟨z, hzJ⟩ : ↥J) : PQuot p J) = σ := Subtype.ext hzσ
    rwa [this]
  obtain ⟨E, hEJ, hEel, hzE, hEcard, -⟩ := exists_lift_elemAbelian hp e hEbel hzJ hzo hzmem
  have hrJ := h.setup.rank_J
  have hp0 : 0 < p := hp.pos
  have h1 : n / p = (n - p) / p + 1 := by
    conv_lhs => rw [show n = (n - p) + p by omega]
    exact Nat.add_div_right _ hp0
  refine ⟨E, hEJ, hEel, ?_, z, hzE, hzo, hzJ, ?_⟩
  · rw [hEcard, hEbc, hrJ, h1, Nat.add_sub_cancel]
  · rw [hzσ]; exact hσ

theorem l72_c1_Bprime {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K : Subgroup G} (h : L72Data p B x L n y J a K)
    (hDK : altDxy x y ≤ centModSubgroup p K) {E : Subgroup G} (hEJ : E ≤ J)
    (hEel : IsElemAbelian p E) :
    IsElemAbelian p (E ⊔ altDxy x y) ∧ Nat.card ↥(E ⊔ altDxy x y) = Nat.card ↥E * p ^ 2 ∧
      E ⊔ altDxy x y ≤ Subgroup.centralizer ({a} : Set G) ∧
      E ⊔ altDxy x y ≤ Subgroup.normalizer (K : Set G) := by
  have hDel := h.setup.isElemAbelian_D
  have hEK : E ≤ K := hEJ.trans h.single.J_le
  have hEC : E ≤ Subgroup.centralizer (altDxy x y : Set G) :=
    hEJ.trans (h.single.J_comp.1.trans inf_le_right)
  have hcomm : ∀ e ∈ E, ∀ d ∈ altDxy x y, e * d = d * e := fun e he d hd =>
    (Subgroup.mem_centralizer_iff.1 (hEC he) d hd).symm
  have hDN : altDxy x y ≤ Subgroup.normalizer (E : Set G) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun e he =>
      hcomm e he d hd)
  have hinf : E ⊓ altDxy x y = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ altDxy x y ⊓ K := ⟨hg.2, hEK hg.1⟩
    rw [l72_central_D_inf_K h hDK] at this
    exact this
  have hcard := card_sup_mul_card_inf_of_le_normalizer hDN
  rw [hinf, Subgroup.card_bot, mul_one, h.setup.card_D] at hcard
  refine ⟨isElemAbelian_sup_of_commute hEel hDel hcomm, hcard, ?_, ?_⟩
  · refine sup_le (hEK.trans h.single.comp.1) ?_
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute hDel h.a_mem hd |>.symm
  · exact sup_le (hEK.trans Subgroup.le_normalizer) h.single.norm

theorem glaPLayer_inf_centralizer_ne_bot (hp : p.Prime) {K F : Subgroup G} (hFp : IsPGroup p F)
    (hFN : F ≤ Subgroup.normalizer (K : Set G))
    (hex : ∃ I : Subgroup (PQuot p K), GLAPComponent p (fixedBar p K F) I) :
    GLAPLayer p (K ⊓ Subgroup.centralizer (F : Set G)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨I, hI⟩ := hex
  have hKO : GLAPPrimeCoreOf p K ≤ K := Subgroup.map_subtype_le _
  have hfix : ∀ (k : G) (hk : k ∈ K),
      (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : PQuot p K) ∈ fixedBar p K F ↔
      ∀ f : ↥(Subgroup.normalizer (K : Set G)), (f : G) ∈ F →
        (QuotientGroup.mk (K.normalizerMonoidHom f ⟨k, hk⟩) : PQuot p K) =
          QuotientGroup.mk ⟨k, hk⟩ := by
    intro k hk
    constructor
    · intro h f hf
      have := h f hf
      rwa [barAut_mk] at this
    · intro h f hf
      rw [barAut_mk]
      exact h f hf
  set Yf := preimageMod p K (fixedBar p K F) with hYf
  have hYfK : Yf ≤ K := Subgroup.map_subtype_le _
  set Y' : Subgroup G := K ⊓ Subgroup.centralizer (F : Set G) with hY'
  have hY'Yf : Y' ≤ Yf := by
    intro y hy
    refine mem_preimageMod_iff.2 ⟨hy.1, (hfix y hy.1).2 fun f hf => ?_⟩
    have h1 : K.normalizerMonoidHom f ⟨y, hy.1⟩ = ⟨y, hy.1⟩ := by
      apply Subtype.ext
      show (f : G) * y * (f : G)⁻¹ = y
      rw [Subgroup.mem_centralizer_iff.1 hy.2 f hf]
      group
    rw [h1]
  have hOYf : GLAPPrimeCoreOf p K ≤ Yf := by
    intro o ho
    refine mem_preimageMod_iff.2 ⟨hKO ho, ?_⟩
    have h1 : (QuotientGroup.mk (⟨o, hKO ho⟩ : ↥K) : PQuot p K) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ((chev_mem_glaPPrimeCoreOf_iff (hKO ho)).1 ho)
    rw [h1]
    exact Subgroup.one_mem _
  have hcomm : ∀ y ∈ Yf, ∀ d ∈ F, ⁅y, d⁆ ∈ GLAPPrimeCoreOf p K := by
    intro y hy d hd
    obtain ⟨hyK', hyfix⟩ := mem_preimageMod_iff.1 (Subgroup.inv_mem Yf hy)
    have h1 := (hfix _ hyK').1 hyfix ⟨d, hFN hd⟩ hd
    have h2 := QuotientGroup.eq.1 h1.symm
    have hxK : y * (d * y⁻¹ * d⁻¹) ∈ K :=
      K.mul_mem (hYfK hy) ((Subgroup.mem_normalizer_iff.1 (hFN hd) y⁻¹).1 (K.inv_mem (hYfK hy)))
    have e : (⟨y * (d * y⁻¹ * d⁻¹), hxK⟩ : ↥K) =
        (⟨y⁻¹, hyK'⟩ : ↥K)⁻¹ * K.normalizerMonoidHom ⟨d, hFN hd⟩ ⟨y⁻¹, hyK'⟩ :=
      Subtype.ext (by
        show y * (d * y⁻¹ * d⁻¹) = (y⁻¹)⁻¹ * (d * y⁻¹ * d⁻¹)
        rw [inv_inv])
    have h3 : y * (d * y⁻¹ * d⁻¹) ∈ GLAPPrimeCoreOf p K :=
      (chev_mem_glaPPrimeCoreOf_iff hxK).2 (by rw [e]; exact h2)
    have h4 : ⁅y, d⁆ = y * (d * y⁻¹ * d⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h4]
    exact h3
  have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p K)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp K)
  have hDQ : F ≤ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) := fun d hd =>
    normalizer_le_normalizer_glaPPrimeCoreOf p K (hFN hd)
  have hsup := S3.eq_inf_centralizer_sup_of_pgroup hp hFp hOYf hDQ hcop hcomm
  have hYfC : Yf ⊓ Subgroup.centralizer (F : Set G) = Y' :=
    le_antisymm (fun g hg => ⟨hYfK hg.1, hg.2⟩) (fun g hg => ⟨hY'Yf hg, hg.2⟩)
  rw [hYfC] at hsup
  let π : ↥Y' →* PQuot p K := (pQuotHom p K).comp (Subgroup.inclusion (inf_le_left : Y' ≤ K))
  have hrange : π.range = fixedBar p K F := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      exact (mem_preimageMod_iff.1 (hY'Yf y.2)).2
    · intro z hz
      obtain ⟨k, rfl⟩ := pQuotHom_surjective p K z
      have hkYf : (k : G) ∈ Yf := mem_preimageMod_iff.2 ⟨k.2, hz⟩
      rw [← hsup] at hkYf
      obtain ⟨y, hy, o, ho, hyo⟩ := exists_mul_of_mem_sup_of_le_normalizer
        (inf_le_left.trans (le_normalizer_glaPPrimeCoreOf p K)) hkYf
      refine ⟨⟨y, hy⟩, ?_⟩
      have hk : Subgroup.inclusion (inf_le_left : Y' ≤ K) ⟨y, hy⟩ = k * ⟨o, hKO ho⟩⁻¹ :=
        Subtype.ext (by
          show y = (k : G) * o⁻¹
          rw [hyo]
          group)
      have ho1 : pQuotHom p K ⟨o, hKO ho⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).2 ((chev_mem_glaPPrimeCoreOf_iff (hKO ho)).1 ho)
      show pQuotHom p K (Subgroup.inclusion (inf_le_left : Y' ≤ K) ⟨y, hy⟩) = pQuotHom p K k
      rw [hk, map_mul, map_inv, ho1]
      simp
  have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup ↥Y') ⊓ π.ker)) := by
    rw [top_inf_eq]
    have hle : π.ker.map (Subgroup.inclusion (inf_le_left : Y' ≤ K)) ≤ GLAPPrimeCore p ↥K := by
      rintro _ ⟨y, hy, rfl⟩
      have : π y = 1 := hy
      exact (QuotientGroup.eq_one_iff _).1 this
    have hcard : Nat.card ↥(π.ker.map (Subgroup.inclusion (inf_le_left : Y' ≤ K))) =
        Nat.card ↥π.ker := Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)
    rw [← hcard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      CFSG.pPrimeCore_coprime_card
  have hI' : GLAPComponent p ((⊤ : Subgroup ↥Y').map π) I := by
    rw [← MonoidHom.range_eq_map, hrange]
    exact hI
  obtain ⟨I₀, hI₀, hmap⟩ := exists_glaPComponent_map_eq hp π hker hI'
  have hI₀0 : I₀ ≠ ⊥ := fun h => glaPComponent_ne_bot' hI (by rw [← hmap, h, Subgroup.map_bot])
  have hker0 : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup ↥Y') ⊓ Y'.subtype.ker)) := by
    rw [top_inf_eq, Subgroup.ker_subtype, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have htop : (⊤ : Subgroup ↥Y').map Y'.subtype = Y' :=
    le_antisymm (by rintro _ ⟨y, -, rfl⟩; exact y.2) fun y hy => ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  have hI₁ : GLAPComponent p Y' (I₀.map Y'.subtype) := by
    have := glaPComponent_map hp Y'.subtype hker0 hI₀
    rwa [htop] at this
  intro hbot
  have hle : I₀.map Y'.subtype ≤ GLAPLayer p Y' := le_sSup hI₁
  rw [hbot, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ Y'.subtype_injective] at hle
  exact hI₀0 hle

theorem fixedBar_sup_eq_centralizer {K C Z : Subgroup G} (hC : C ≤ centModSubgroup p K) (hZ : Z ≤ K) :
    fixedBar p K (C ⊔ Z) =
      Subgroup.centralizer ((imageMod p K Z : Subgroup (PQuot p K)) : Set (PQuot p K)) := by
  ext w
  constructor
  · intro hw m hm
    obtain ⟨⟨z, hzK⟩, hz, rfl⟩ := hm
    have hzZ : z ∈ Z := hz
    have hfix := hw ⟨z, Subgroup.le_normalizer hzK⟩ (Subgroup.mem_sup_right hzZ)
    rw [barAut_eq_conj_of_mem hzK, MulAut.conj_apply] at hfix
    exact mul_inv_eq_iff_eq_mul.1 hfix
  · intro hw
    have key : ∀ g ∈ C ⊔ Z, ∃ hgN : g ∈ Subgroup.normalizer (K : Set G),
        barAut p K ⟨g, hgN⟩ w = w := by
      intro g hg
      rw [Subgroup.sup_eq_closure] at hg
      refine Subgroup.closure_induction
        (p := fun g _ => ∃ hgN : g ∈ Subgroup.normalizer (K : Set G), barAut p K ⟨g, hgN⟩ w = w)
        ?_ ?_ ?_ ?_ hg
      · rintro g (hg | hg)
        · have hgc := hC hg
          have hgN := hgc.1
          refine ⟨hgN, ?_⟩
          have h1 : barAut p K ⟨g, hgN⟩ = 1 :=
            (chev_barAut_eq_one_iff_centMod hgN).2 (centMod_iff.2 hgc)
          rw [h1]
          rfl
        · have hgK := hZ hg
          refine ⟨Subgroup.le_normalizer hgK, ?_⟩
          rw [barAut_eq_conj_of_mem hgK, MulAut.conj_apply]
          have h1 := hw (QuotientGroup.mk (⟨g, hgK⟩ : ↥K)) ⟨⟨g, hgK⟩, hg, rfl⟩
          rw [h1, mul_inv_cancel_right]
      · exact ⟨Subgroup.one_mem _, by
          have h1 : (⟨1, Subgroup.one_mem _⟩ : ↥(Subgroup.normalizer (K : Set G))) = 1 := rfl
          rw [h1, map_one]
          rfl⟩
      · rintro g₁ g₂ - - ⟨h1N, h1⟩ ⟨h2N, h2⟩
        refine ⟨Subgroup.mul_mem _ h1N h2N, ?_⟩
        have h3 : (⟨g₁ * g₂, Subgroup.mul_mem _ h1N h2N⟩ :
            ↥(Subgroup.normalizer (K : Set G))) = ⟨g₁, h1N⟩ * ⟨g₂, h2N⟩ := rfl
        rw [h3, map_mul, MulAut.mul_apply, h2, h1]
      · rintro g - ⟨hgN, hg⟩
        refine ⟨Subgroup.inv_mem _ hgN, ?_⟩
        have h3 : (⟨g⁻¹, Subgroup.inv_mem _ hgN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
            ⟨g, hgN⟩⁻¹ := rfl
        rw [h3, map_inv]
        exact (MulEquiv.symm_apply_eq _).2 hg.symm
    intro f hf
    obtain ⟨hfN, hfw⟩ := key f hf
    exact hfw

theorem exists_glaPComponent_centralizer_of_alt (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G}
    {M : ℕ} (e : PQuot p K ≃* ↥(alternatingGroup (Fin M))) (P : Subgroup (PQuot p K))
    {τ : ↥(alternatingGroup (Fin M))} (hτP : e.symm τ ∈ P)
    (hsupp : ∀ g ∈ P, ((e g : ↥(alternatingGroup (Fin M))) : Equiv.Perm (Fin M)).support ⊆
      (τ : Equiv.Perm (Fin M)).support)
    (h5 : 5 ≤ M - (τ : Equiv.Perm (Fin M)).support.card)
    (hpn : p ≤ M - (τ : Equiv.Perm (Fin M)).support.card) :
    ∃ I : Subgroup (PQuot p K),
      GLAPComponent p (Subgroup.centralizer (P : Set (PQuot p K))) I := by
  classical
  have h1 := altFix_isPComponent hp hp2 (P := P.map e.toMonoidHom) (τ := τ)
    ⟨e.symm τ, hτP, by simp⟩
    (fun g hg => by
      obtain ⟨g', hg', rfl⟩ := hg
      exact hsupp g' hg') h5 hpn
  have h2 := glaPComponent_map_mulEquiv hp e.symm h1
  have hcent : (Subgroup.centralizer ((P.map e.toMonoidHom : Subgroup _) : Set _)).map
      e.symm.toMonoidHom = Subgroup.centralizer (P : Set (PQuot p K)) := by
    ext w
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩ h hh
      apply e.injective
      have := Subgroup.mem_centralizer_iff.1 hu (e h) ⟨h, hh, rfl⟩
      simpa using this
    · intro hw
      refine ⟨e w, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨h, hh, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 hw h hh
      simpa using congrArg e this
  rw [hcent] at h2
  exact ⟨_, h2⟩

theorem l72_c1_fixedBar {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K : Subgroup G} (h : L72Data p B x L n y J a K)
    (hDK : altDxy x y ≤ centModSubgroup p K)
    (e : PQuot p J ≃* ↥(alternatingGroup (Fin (n - p)))) {z : G} (hzJ : z ∈ J) (hzo : orderOf z = p)
    (hz : IsPCycleMod p J (n - p) e z) :
    ∃ I : Subgroup (PQuot p K),
      GLAPComponent p (fixedBar p K (altDxy x y ⊔ Subgroup.zpowers z)) I := by
  classical
  have hp := h.ctx.prime
  have hJK : J ≤ K := h.single.J_le
  have hzK : z ∈ K := hJK hzJ
  obtain ⟨hcov, hSh⟩ := l72_shape_central h hDK
  obtain ⟨θ, hθ⟩ := l72_equiv_of_kernel hJK hSh.kernel
  have htop : imageMod p K J = ⊤ := imageMod_eq_top_of_sup hJK hcov
  let θ' : PQuot p J ≃* PQuot p K := θ.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
  have hθ' : ∀ j : ↥J, θ' (QuotientGroup.mk j) = QuotientGroup.mk (⟨(j : G), hJK j.2⟩ : ↥K) :=
    fun j => hθ j
  let e' : PQuot p K ≃* ↥(alternatingGroup (Fin (n - p))) := θ'.symm.trans e
  set σ : ↥(alternatingGroup (Fin (n - p))) := e (QuotientGroup.mk (⟨z, hzJ⟩ : ↥J)) with hσ
  have he'z : e' (QuotientGroup.mk (⟨z, hzK⟩ : ↥K)) = σ := by
    show e (θ'.symm (QuotientGroup.mk (⟨z, hzK⟩ : ↥K))) = σ
    rw [(MulEquiv.symm_apply_eq θ').2 (hθ' ⟨z, hzJ⟩).symm]
  have hσc : ((σ : ↥(alternatingGroup (Fin (n - p)))) : Equiv.Perm (Fin (n - p))).cycleType = {p} := by
    have := hz.2
    rwa [permOfMod_of_mem e hzJ] at this
  have hZK : Subgroup.zpowers z ≤ K := Subgroup.zpowers_le.2 hzK
  rw [fixedBar_sup_eq_centralizer hDK hZK]
  have hcard := card_support_eq_of_cycleType hσc
  have h3 := h.setup.three_mul_le
  have hbig := h.big
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := h.ctx.odd
    omega
  refine exists_glaPComponent_centralizer_of_alt hp h.ctx.odd e' _ (τ := σ) ?_ ?_ ?_ ?_
  · rw [← he'z, e'.symm_apply_apply]
    exact ⟨⟨z, hzK⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers z), rfl⟩
  · rintro g ⟨⟨w, hwK⟩, hw, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hw)
    have h1 : (⟨w, hwK⟩ : ↥K) = (⟨z, hzK⟩ : ↥K) ^ k := Subtype.ext (by simpa using hk.symm)
    have h2 : e' ((QuotientGroup.mk' (GLAPPrimeCore p ↥K)) ⟨w, hwK⟩) = σ ^ k := by
      rw [h1, QuotientGroup.mk'_apply, QuotientGroup.mk_zpow, map_zpow, he'z]
    rw [h2]
    show ((σ ^ k : ↥(alternatingGroup (Fin (n - p)))) : Equiv.Perm (Fin (n - p))).support ⊆ _
    rw [SubgroupClass.coe_zpow]
    exact Equiv.Perm.support_zpow_le _ _
  · rw [hcard]
    omega
  · rw [hcard]
    omega

theorem l72_c1_F {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K : Subgroup G} (h : L72Data p B x L n y J a K)
    (hDK : altDxy x y ≤ centModSubgroup p K)
    (e : PQuot p J ≃* ↥(alternatingGroup (Fin (n - p)))) {E : Subgroup G} (hEJ : E ≤ J) {z : G}
    (hzE : z ∈ E) (hzo : orderOf z = p) (hz : IsPCycleMod p J (n - p) e z) :
    IsElemAbelian p (altDxy x y ⊔ Subgroup.zpowers z) ∧
      Nat.card ↥(altDxy x y ⊔ Subgroup.zpowers z) = p ^ 3 ∧
      GLAPLayer p (K ⊓ Subgroup.centralizer ((altDxy x y ⊔ Subgroup.zpowers z : Subgroup G) :
        Set G)) ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨h.ctx.prime⟩
  have hDel := h.setup.isElemAbelian_D
  have hzJ : z ∈ J := hEJ hzE
  have hzK : z ∈ K := h.single.J_le hzJ
  have hzC : z ∈ Subgroup.centralizer (altDxy x y : Set G) := h.single.J_comp.1 hzJ |>.2
  have hzp : z ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro hz1
    rw [hz1, orderOf_one] at hzo
    exact h.ctx.prime.one_lt.ne hzo
  have hzD : z ∉ altDxy x y := by
    intro hzD
    have : z ∈ altDxy x y ⊓ K := ⟨hzD, hzK⟩
    rw [l72_central_D_inf_K h hDK] at this
    exact hz1 (Subgroup.mem_bot.1 this)
  have hzel : IsElemAbelian p (Subgroup.zpowers z) :=
    isElemAbelian_zpowers hzp
  have hcomm : ∀ d ∈ altDxy x y, ∀ w ∈ Subgroup.zpowers z, d * w = w * d := by
    intro d hd w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact (Commute.zpow_right (show Commute d z from Subgroup.mem_centralizer_iff.1 hzC d hd) k).eq
  have hFel : IsElemAbelian p (altDxy x y ⊔ Subgroup.zpowers z) :=
    isElemAbelian_sup_of_commute hDel hzel hcomm
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (altDxy x y : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ hzC)
  have hinf : altDxy x y ⊓ Subgroup.zpowers z = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ altDxy x y ⊓ K := ⟨hg.1, (Subgroup.zpowers_le.2 hzK) hg.2⟩
    rw [l72_central_D_inf_K h hDK] at this
    exact this
  have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hinf, Subgroup.card_bot, mul_one, h.setup.card_D, Nat.card_zpowers, hzo] at hcard
  refine ⟨hFel, by rw [hcard]; ring, ?_⟩
  have hFN : altDxy x y ⊔ Subgroup.zpowers z ≤ Subgroup.normalizer (K : Set G) :=
    sup_le h.single.norm (Subgroup.zpowers_le.2 (Subgroup.le_normalizer hzK))
  obtain ⟨I, hI⟩ := l72_c1_fixedBar h hDK e hzJ hzo hz
  exact glaPLayer_inf_centralizer_ne_bot h.ctx.prime (isPGroup_of_isElemAbelian hFel) hFN ⟨I, hI⟩

theorem l72_central_Bstar {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K : Subgroup G} (h : L72Data p B x L n y J a K)
    (hDK : altDxy x y ≤ centModSubgroup p K) : L72Bstar p B a K := by
  have hp := h.ctx.prime
  obtain ⟨e⟩ := h.setup.J_alt
  obtain ⟨E, hEJ, hEel, hEc, z, hzE, hzo, hz⟩ := l72_c1_E h e
  obtain ⟨hB'el, hB'c, hB'a, hB'N⟩ := l72_c1_Bprime h hDK hEJ hEel
  obtain ⟨hFel, hFc, hFne⟩ := l72_c1_F h hDK e hEJ hzE hzo hz
  have hzD : Subgroup.zpowers z ≤ E := (Subgroup.zpowers_le).2 hzE
  have h3 : 3 ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).2 (by have := h.setup.three_mul_le; omega)
  have hrJ := h.setup.rank_J
  have hrB := h.setup.rank_B
  have hcardB' : Nat.card ↥(E ⊔ altDxy x y) = p ^ (CFSG.Open.pRank p J + 2) := by
    rw [hB'c, hEc, ← pow_add]
  have hrk : CFSG.Open.pRank p (E ⊔ altDxy x y) = CFSG.Open.pRank p J + 2 :=
    pRank_eq_of_isElemAbelian_altSetup hp.one_lt hB'el hcardB'
  refine ⟨E ⊔ altDxy x y, altDxy x y ⊔ Subgroup.zpowers z, hB'el, Subgroup.mem_sup_right h.a_mem,
    hB'a, hB'N, ?_, sup_le le_sup_right (le_sup_of_le_left hzD), hFel, hFc, hFne⟩
  rw [hrk]
  omega

theorem l72_c2_E {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K : Subgroup G} (h : L72Data p B x L n y J a K) {r : ℕ}
    (e : PQuot p K ≃* ↥(alternatingGroup (Fin (n + r * p)))) :
    ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card ↥E = p ^ (n / p + r) ∧
      ∃ z₁ ∈ E, ∃ z₂ ∈ E, orderOf z₁ = p ∧ orderOf z₂ = p ∧ IsPCycleMod p K (n + r * p) e z₁ ∧
        IsPCycleMod p K (n + r * p) e z₂ ∧
        Equiv.Perm.Disjoint (permOfMod p K (n + r * p) e z₁) (permOfMod p K (n + r * p) e z₂) := by
  have hp := h.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have h3 := h.setup.three_mul_le
  have hpM : p ≤ n + r * p := by omega
  have hMp : (n + r * p) / p = n / p + r := Nat.add_mul_div_right n r hp.pos
  have h23 : 3 ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).2 (by omega)
  obtain ⟨σ, hσ⟩ := exists_pCycle hp h.ctx.odd hpM
  obtain ⟨z₁, hz₁K, hz₁o, hz₁σ⟩ := exists_cycle_lift hp e σ hσ
  obtain ⟨Eb, hEbel, hEbc, hσEb, hτ⟩ := exists_elemAbelian_pCycle hp h.ctx.odd hpM σ hσ
  obtain ⟨τ, hτE, hτc, hτd⟩ := hτ (by omega)
  have hz₁mem : e (QuotientGroup.mk (⟨z₁, hz₁K⟩ : ↥K) : PQuot p K) ∈ Eb := by
    rw [permOfMod_of_mem e hz₁K] at hz₁σ
    have : e (QuotientGroup.mk (⟨z₁, hz₁K⟩ : ↥K) : PQuot p K) = σ := Subtype.ext hz₁σ
    rwa [this]
  obtain ⟨E, hEK, hEel, hz₁E, hEcard, hlift⟩ := exists_lift_elemAbelian hp e hEbel hz₁K hz₁o hz₁mem
  obtain ⟨z₂, hz₂E, hz₂τ⟩ := hlift τ hτE
  have hz₂K : z₂ ∈ K := hEK hz₂E
  have hz₂1 : z₂ ≠ 1 := by
    rintro rfl
    have h1 : permOfMod p K (n + r * p) e 1 = 1 := by
      rw [permOfMod_of_mem e (Subgroup.one_mem K)]
      have : (⟨1, Subgroup.one_mem K⟩ : ↥K) = 1 := rfl
      simp [this]
    rw [h1] at hz₂τ
    have := hτc
    rw [← hz₂τ] at this
    simp at this
  have hz₂o : orderOf z₂ = p := orderOf_eq_prime (hEel.2 z₂ hz₂E) hz₂1
  refine ⟨E, hEK, hEel, ?_, z₁, hz₁E, z₂, hz₂E, hz₁o, hz₂o, ⟨hz₁K, ?_⟩, ⟨hz₂K, ?_⟩, ?_⟩
  · rw [hEcard, hEbc, hMp]
  · rw [hz₁σ]; exact hσ
  · rw [hz₂τ]; exact hτc
  · rw [hz₁σ, hz₂τ]; exact hτd

theorem l72_c2_Bprime {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K : Subgroup G} (h : L72Data p B x L n y J a K) {r : ℕ}
    (e : PQuot p K ≃* ↥(alternatingGroup (Fin (n + r * p)))) {E : Subgroup G} (hEK : E ≤ K)
    (hEel : IsElemAbelian p E) :
    IsElemAbelian p (E ⊔ Subgroup.zpowers a) ∧ Nat.card ↥(E ⊔ Subgroup.zpowers a) = Nat.card ↥E * p ∧
      E ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({a} : Set G) ∧
      E ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (K : Set G) := by
  haveI : Fact p.Prime := ⟨h.ctx.prime⟩
  have hap : a ^ p = 1 := h.setup.isElemAbelian_D.2 a h.a_mem
  have hao : orderOf a = p := orderOf_eq_prime hap h.a_ne
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := h.single.comp.1
  have haK : a ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKa hk)
  have hZ := center_pQuot_eq_bot_of_equiv (by have := h.setup.three_mul_le; have := h.ctx.prime.two_le; nlinarith) e
  have hzel : IsElemAbelian p (Subgroup.zpowers a) := isElemAbelian_zpowers hap
  have hcomm : ∀ g ∈ E, ∀ w ∈ Subgroup.zpowers a, g * w = w * g := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact (Commute.zpow_right (show Commute g a from Subgroup.mem_centralizer_singleton_iff.1
      (hKa (hEK hg))) k).eq
  have hinfK : Subgroup.zpowers a ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    exact eq_one_of_centMod_pElt h.ctx.prime hZ hg.2 (hzel.2 g hg.1)
      (centMod_of_mem_centralizer ((Subgroup.zpowers_le.2 haK) hg.1))
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun g hg => (hcomm g hg a (Subgroup.mem_zpowers a))))
  have hinf : E ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ Subgroup.zpowers a ⊓ K := ⟨hg.2, hEK hg.1⟩
    rw [hinfK] at this
    exact this
  have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hao] at hcard
  refine ⟨isElemAbelian_sup_of_commute hEel hzel hcomm, hcard, ?_, ?_⟩
  · refine sup_le (hEK.trans hKa) ?_
    exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  · exact sup_le (hEK.trans Subgroup.le_normalizer)
      (Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ haK))

theorem l72_c2_fixedBar {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K : Subgroup G} (h : L72Data p B x L n y J a K) {r : ℕ}
    (e : PQuot p K ≃* ↥(alternatingGroup (Fin (n + r * p)))) {z₁ z₂ : G}
    (hz₁ : IsPCycleMod p K (n + r * p) e z₁) (hz₂ : IsPCycleMod p K (n + r * p) e z₂)
    (hz₁o : orderOf z₁ = p) (hz₂o : orderOf z₂ = p)
    (hdisj : Equiv.Perm.Disjoint (permOfMod p K (n + r * p) e z₁) (permOfMod p K (n + r * p) e z₂)) :
    ∃ I : Subgroup (PQuot p K), GLAPComponent p
      (fixedBar p K (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ⊔ Subgroup.zpowers a)) I := by
  classical
  have hp := h.ctx.prime
  have hK₁ : z₁ ∈ K := hz₁.1
  have hK₂ : z₂ ∈ K := hz₂.1
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := h.single.comp.1
  have haK : a ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKa hk)
  have hC : Subgroup.zpowers a ≤ centModSubgroup p K :=
    Subgroup.zpowers_le.2 (centMod_iff.1 (centMod_of_mem_centralizer haK))
  have hZK : Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ≤ K :=
    sup_le (Subgroup.zpowers_le.2 hK₁) (Subgroup.zpowers_le.2 hK₂)
  rw [sup_comm (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) (Subgroup.zpowers a),
    fixedBar_sup_eq_centralizer hC hZK]
  set σ₁ : ↥(alternatingGroup (Fin (n + r * p))) := e (QuotientGroup.mk (⟨z₁, hK₁⟩ : ↥K)) with hσ₁
  set σ₂ : ↥(alternatingGroup (Fin (n + r * p))) := e (QuotientGroup.mk (⟨z₂, hK₂⟩ : ↥K)) with hσ₂
  have hσ₁c : ((σ₁ : ↥(alternatingGroup (Fin (n + r * p)))) :
      Equiv.Perm (Fin (n + r * p))).cycleType = {p} := by
    have := hz₁.2
    rwa [permOfMod_of_mem e hK₁] at this
  have hσ₂c : ((σ₂ : ↥(alternatingGroup (Fin (n + r * p)))) :
      Equiv.Perm (Fin (n + r * p))).cycleType = {p} := by
    have := hz₂.2
    rwa [permOfMod_of_mem e hK₂] at this
  have hd : Equiv.Perm.Disjoint (σ₁ : Equiv.Perm (Fin (n + r * p))) (σ₂ : Equiv.Perm (Fin (n + r * p))) := by
    have := hdisj
    rwa [permOfMod_of_mem e hK₁, permOfMod_of_mem e hK₂] at this
  have hs₁ := card_support_eq_of_cycleType hσ₁c
  have hs₂ := card_support_eq_of_cycleType hσ₂c
  have hsupp_mul : ((σ₁ * σ₂ : ↥(alternatingGroup (Fin (n + r * p)))) : Equiv.Perm (Fin (n + r * p))).support =
      (σ₁ : Equiv.Perm (Fin (n + r * p))).support ∪ (σ₂ : Equiv.Perm (Fin (n + r * p))).support :=
    Equiv.Perm.Disjoint.support_mul hd
  have hcard : ((σ₁ * σ₂ : ↥(alternatingGroup (Fin (n + r * p)))) :
      Equiv.Perm (Fin (n + r * p))).support.card = 2 * p := by
    rw [hsupp_mul, Finset.card_union_of_disjoint (Equiv.Perm.disjoint_iff_disjoint_support.1 hd), hs₁, hs₂]
    ring
  have h3 := h.setup.three_mul_le
  have hbig := h.big
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := h.ctx.odd
    omega
  refine exists_glaPComponent_centralizer_of_alt hp h.ctx.odd e _ (τ := σ₁ * σ₂) ?_ ?_ ?_ ?_
  · have h1 : e.symm (σ₁ * σ₂) = QuotientGroup.mk (⟨z₁, hK₁⟩ : ↥K) * QuotientGroup.mk (⟨z₂, hK₂⟩ : ↥K) := by
      rw [hσ₁, hσ₂, ← map_mul, e.symm_apply_apply]
    rw [h1]
    exact Subgroup.mul_mem _
      ⟨⟨z₁, hK₁⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers z₁)), rfl⟩
      ⟨⟨z₂, hK₂⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers z₂)), rfl⟩
  · rintro g ⟨⟨w, hwK⟩, hw, rfl⟩
    have hw' : w ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ := Subgroup.mem_subgroupOf.1 hw
    set U : Finset (Fin (n + r * p)) :=
      (σ₁ : Equiv.Perm (Fin (n + r * p))).support ∪ (σ₂ : Equiv.Perm (Fin (n + r * p))).support with hU
    set W : Subgroup G := ((altOn U).comap (e.toMonoidHom.comp (pQuotHom p K))).map K.subtype with hW
    have hz₁W : z₁ ∈ W :=
      ⟨⟨z₁, hK₁⟩, mem_altOn_iff.2 (Finset.subset_union_left), rfl⟩
    have hz₂W : z₂ ∈ W :=
      ⟨⟨z₂, hK₂⟩, mem_altOn_iff.2 (Finset.subset_union_right), rfl⟩
    have hZW : Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ≤ W :=
      sup_le (Subgroup.zpowers_le.2 hz₁W) (Subgroup.zpowers_le.2 hz₂W)
    obtain ⟨k, hk, hkw⟩ := hZW hw'
    have hkeq : k = ⟨w, hwK⟩ := Subtype.ext hkw
    rw [hkeq] at hk
    have := mem_altOn_iff.1 hk
    rw [hsupp_mul]
    exact this
  · rw [hcard]
    omega
  · rw [hcard]
    omega

theorem l72_c2_F {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K : Subgroup G} (h : L72Data p B x L n y J a K) {r : ℕ}
    (e : PQuot p K ≃* ↥(alternatingGroup (Fin (n + r * p)))) {E : Subgroup G} (hEK : E ≤ K)
    (hEel : IsElemAbelian p E)
    {z₁ z₂ : G} (hz₁E : z₁ ∈ E) (hz₂E : z₂ ∈ E) (hz₁o : orderOf z₁ = p) (hz₂o : orderOf z₂ = p)
    (hz₁ : IsPCycleMod p K (n + r * p) e z₁) (hz₂ : IsPCycleMod p K (n + r * p) e z₂)
    (hdisj : Equiv.Perm.Disjoint (permOfMod p K (n + r * p) e z₁) (permOfMod p K (n + r * p) e z₂)) :
    IsElemAbelian p (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ⊔ Subgroup.zpowers a) ∧
      Nat.card ↥(Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ⊔ Subgroup.zpowers a) = p ^ 3 ∧
      GLAPLayer p (K ⊓ Subgroup.centralizer ((Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ⊔
        Subgroup.zpowers a : Subgroup G) : Set G)) ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨h.ctx.prime⟩
  have hap : a ^ p = 1 := h.setup.isElemAbelian_D.2 a h.a_mem
  have hao : orderOf a = p := orderOf_eq_prime hap h.a_ne
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := h.single.comp.1
  have haK : a ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKa hk)
  have hK₁ : z₁ ∈ K := hz₁.1
  have hK₂ : z₂ ∈ K := hz₂.1
  have hz₁p : z₁ ^ p = 1 := hEel.2 z₁ hz₁E
  have hz₂p : z₂ ^ p = 1 := hEel.2 z₂ hz₂E
  have hz₂1 : z₂ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz₂o
    exact h.ctx.prime.one_lt.ne hz₂o
  have hna : z₁ ∉ Subgroup.zpowers z₂ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : permOfMod p K (n + r * p) e z₁ = (permOfMod p K (n + r * p) e z₂) ^ k := by
      rw [permOfMod_of_mem e hK₁, permOfMod_of_mem e hK₂]
      have : (⟨z₁, hK₁⟩ : ↥K) = (⟨z₂, hK₂⟩ : ↥K) ^ k := Subtype.ext (by simpa using hk.symm)
      rw [this, QuotientGroup.mk_zpow, map_zpow]
      exact SubgroupClass.coe_zpow _ _
    have hsupp : (permOfMod p K (n + r * p) e z₁).support ⊆ (permOfMod p K (n + r * p) e z₂).support := by
      rw [h1]; exact Equiv.Perm.support_zpow_le _ _
    have hd := Equiv.Perm.disjoint_iff_disjoint_support.1 hdisj
    have hne : (permOfMod p K (n + r * p) e z₁).support = ∅ :=
      Finset.subset_empty.1 (by
        intro u hu
        exact absurd (hsupp hu) (Finset.disjoint_left.1 hd hu))
    have hone : permOfMod p K (n + r * p) e z₁ = 1 := Equiv.Perm.support_eq_empty_iff.1 hne
    have := hz₁.2
    rw [hone] at this
    simp at this
  obtain ⟨hA, hAcard⟩ := Prop53.isElemAbelian_card_sup_zpowers h.ctx.prime
    (isElemAbelian_commute hEel hz₁E hz₂E) hz₁p hz₂p hz₂1 hna
  have hzel : IsElemAbelian p (Subgroup.zpowers a) := isElemAbelian_zpowers hap
  have hAK : Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ≤ K :=
    sup_le (Subgroup.zpowers_le.2 hK₁) (Subgroup.zpowers_le.2 hK₂)
  have hZ := center_pQuot_eq_bot_of_equiv
    (by have := h.setup.three_mul_le; have := h.ctx.prime.two_le; nlinarith) e
  have hinfK : Subgroup.zpowers a ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    exact eq_one_of_centMod_pElt h.ctx.prime hZ hg.2 (hzel.2 g hg.1)
      (centMod_of_mem_centralizer ((Subgroup.zpowers_le.2 haK) hg.1))
  have hcomm : ∀ g ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂, ∀ w ∈ Subgroup.zpowers a,
      g * w = w * g := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact (Commute.zpow_right (show Commute g a from
      Subgroup.mem_centralizer_singleton_iff.1 (hKa (hAK hg))) k).eq
  have hFel : IsElemAbelian p (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ⊔ Subgroup.zpowers a) :=
    isElemAbelian_sup_of_commute hA hzel hcomm
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer
      ((Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun g hg => hcomm g hg a (Subgroup.mem_zpowers a)))
  have hinf : (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ Subgroup.zpowers a ⊓ K := ⟨hg.2, hAK hg.1⟩
    rw [hinfK] at this
    exact this
  have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hao, hAcard] at hcard
  refine ⟨hFel, by rw [hcard]; ring, ?_⟩
  have hFN : Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ⊔ Subgroup.zpowers a ≤
      Subgroup.normalizer (K : Set G) :=
    sup_le (hAK.trans Subgroup.le_normalizer)
      (Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ haK))
  obtain ⟨I, hI⟩ := l72_c2_fixedBar h e hz₁ hz₂ hz₁o hz₂o hdisj
  exact glaPLayer_inf_centralizer_ne_bot h.ctx.prime (isPGroup_of_isElemAbelian hFel) hFN ⟨I, hI⟩

theorem l72_noncentral_Bstar {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} {a : G} {K : Subgroup G} (i1415 : I1415At G p)
    (h : L72Data p B x L n y J a K) (hDK : ¬ altDxy x y ≤ centModSubgroup p K) :
    L72Bstar p B a K := by
  have hp := h.ctx.prime
  obtain ⟨b, r, hbD, hbN, hbn, hJb, ⟨e⟩⟩ := l72_noncentral_alt i1415 h hDK
  obtain ⟨E, hEK, hEel, hEc, z₁, hz₁E, z₂, hz₂E, hz₁o, hz₂o, hz₁, hz₂, hdisj⟩ := l72_c2_E h e
  obtain ⟨hB'el, hB'c, hB'a, hB'N⟩ := l72_c2_Bprime h e hEK hEel
  obtain ⟨hFel, hFc, hFne⟩ := l72_c2_F h e hEK hEel hz₁E hz₂E hz₁o hz₂o hz₁ hz₂ hdisj
  have hcardB' : Nat.card ↥(E ⊔ Subgroup.zpowers a) = p ^ (n / p + r + 1) := by
    rw [hB'c, hEc, ← pow_succ]
  have hrk : CFSG.Open.pRank p (E ⊔ Subgroup.zpowers a) = n / p + r + 1 :=
    pRank_eq_of_isElemAbelian_altSetup hp.one_lt hB'el hcardB'
  have hz₁F : z₁ ∈ E ⊔ Subgroup.zpowers a := Subgroup.mem_sup_left hz₁E
  have hz₂F : z₂ ∈ E ⊔ Subgroup.zpowers a := Subgroup.mem_sup_left hz₂E
  have haF : a ∈ E ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  refine ⟨E ⊔ Subgroup.zpowers a, Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ⊔ Subgroup.zpowers a,
    hB'el, haF, hB'a, hB'N, ?_, ?_, hFel, hFc, hFne⟩
  · rw [hrk]
    have := h.setup.rank_B
    omega
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact (Subgroup.zpowers_le).2 hz₁F
    · exact (Subgroup.zpowers_le).2 hz₂F
    · exact (Subgroup.zpowers_le).2 haF

theorem l72_exists_Bstar {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K : Subgroup G} (i1415 : I1415At G p) (h : L72Data p B x L n y J a K)
    (hev : ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      U ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G))) :
    ∃ B' : Subgroup G, GLAIsBmax p B' ∧ a ∈ B' ∧ B' ≤ Subgroup.normalizer (K : Set G) ∧
      IsGStar p B' K := by
  have hp := h.ctx.prime
  obtain ⟨B', F, hB'el, haB', hB'a, hB'N, hrank, hFB, hFel, hFc, hFne⟩ :
      L72Bstar p B a K := by
    by_cases hDK : altDxy x y ≤ centModSubgroup p K
    · exact l72_central_Bstar h hDK
    · exact l72_noncentral_Bstar i1415 h hDK
  obtain ⟨U, hU0, hU2, hUO⟩ := hev
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set O := GLAPPrimeCoreOf p Ca with hO
  have hev' : ¬ Odd (Nat.card ↥O) := by
    intro hodd
    have hdvd : Nat.card ↥U ∣ Nat.card ↥O := Subgroup.card_dvd_of_le hUO
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hU2
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hU0 (Subgroup.card_eq_one.1 (by simpa using hk))
    have h2 : 2 ∣ Nat.card ↥O := by
      refine dvd_trans ?_ hdvd
      rw [hk]
      exact dvd_pow_self 2 hk0
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBpg : IsPGroup p B' := isPGroup_of_isElemAbelian hB'el
  have hBO : B' ≤ Subgroup.normalizer (O : Set G) :=
    hB'a.trans (le_normalizer_glaPPrimeCoreOf p Ca)
  obtain ⟨U', hU'O, hU'0, hU'2, hB'U'⟩ := exists_invariant_twoGroup hp h.ctx.odd hBpg hBO
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp Ca) hev'
  have hbmax : GLAIsBmax p B' :=
    isBmax_of_pRank_le hp (IsSStarMax.bmax h.sstar) hB'el hrank ⟨U', hU'0, hU'2, hB'U'⟩
  refine ⟨B', hbmax, haB', hB'N, F, hFB, hFel, hFc, ?_⟩
  rwa [closureIn_eq_self hB'N]

theorem false_of_twoGroup_le_odd {U Q : Subgroup G} (hU2 : IsPGroup 2 U) (hU0 : U ≠ ⊥) (hUQ : U ≤ Q)
    (hodd : Odd (Nat.card ↥Q)) : False := by
  have hdvd : Nat.card ↥U ∣ Nat.card ↥Q := Subgroup.card_dvd_of_le hUQ
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hU2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hU0 (Subgroup.card_eq_one.1 (by simpa using hk))
  have h2 : 2 ∣ Nat.card ↥Q := by
    refine dvd_trans ?_ hdvd
    rw [hk]
    exact dvd_pow_self 2 hk0
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem lemma72_big (hc : S6Ctx G p) (hin : Lemma72Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G} (hB : IsSStarMax p B x L)
    (S : AltSetup p B x L n y J) (hn : 9 < n - p) : False := by
  obtain ⟨T, I, eJ, m₀, hTJ, hIJ, hT2, hT0, hIN, hgen, hI2, h5, hm₀, hroot⟩ :=
    l72_exists_TI hc S hn
  obtain ⟨a, haD, ha1, hSne⟩ := l72_exists_a hc S hT0 hT2 hTJ hIJ hIN hI2
  set K := closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G))) with hKdef
  have hK : L72Single p (altDxy x y) J K a :=
    l72_single hc hin.i183 hin.i112 hin.altNotWeakExc hB S (by omega) haD ha1
  have h : L72Data p B x L n y J a K := ⟨hc, hB, S, hn, haD, ha1, hK⟩
  set N := Subgroup.normalizer (T : Set G) with hNdef
  set C := pCoreOf 2 N ⊓ Subgroup.centralizer ({a} : Set G) with hCdef
  set S₀ := (⁅I, C⁆ : Subgroup G) with hS₀def
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC2 : IsPGroup 2 C :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le inf_le_left
  have hID : I ≤ Subgroup.centralizer (altDxy x y : Set G) := hIJ.trans (S.J_comp.1.trans inf_le_right)
  have hIa : I ≤ Subgroup.centralizer ({a} : Set G) :=
    hID.trans (Subgroup.centralizer_le (by simpa using h.a_mem))
  have hIC : I ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_gLBConj_eq, hCdef, gLBConj_inf,
      mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_pCoreOf 2 N (hIN hg)),
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hIa hg))]
  have hS₀C : S₀ ≤ C := by
    rw [hS₀def, Subgroup.commutator_comm]
    exact commutator_le_left_of_normalizes hIC
  have hS₀2 : IsPGroup 2 S₀ := hC2.to_le hS₀C
  have hS₀I : S₀ ≤ ⁅S₀, I⁆ := le_commutator_of_genByPElts hc.prime hc.odd hC2 hIC hgen
  have hIS : I ≤ Subgroup.normalizer (S₀ : Set G) :=
    le_normalizer_commutator Subgroup.le_normalizer hIC
  have hS₀a : S₀ ≤ Subgroup.centralizer ({a} : Set G) := hS₀C.trans inf_le_right
  have hIK : I ≤ K := hIJ.trans hK.J_le
  have hS₀K : S₀ ≤ K := le_of_commutator_subnormal hK.comp.2.1 hIK hS₀a hS₀I
  have hS₀O : S₀ ≤ (⁅GLAPPrimeCoreOf p K, K⁆ : Subgroup G) :=
    l72_S_le_core hin.i1415 hin.i2013 h hIJ hS₀K hS₀2 hIS hS₀I h5 hroot
  have hOK : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) :=
    glaPPrimeCoreOf_le_of_isSubnormal hc.prime hK.comp.2.1
  have hS₀le : S₀ ≤ GLAPPrimeCoreOf p K :=
    hS₀O.trans (commutator_le_left_of_normalizes (le_normalizer_glaPPrimeCoreOf p K))
  obtain ⟨B', hBmax, haB', hB'N, hG⟩ := l72_exists_Bstar hin.i1415 h
    ⟨S₀, hSne, hS₀2, hS₀le.trans hOK⟩
  have h413 := hc.stage4.2.1 B' a K hBmax haB' ha1 hK.comp hG
  rw [closureIn_eq_self hB'N] at h413
  have hle : S₀ ≤ (⁅K, GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G))⁆ : Subgroup G) := by
    rw [Subgroup.commutator_comm]
    exact hS₀O.trans (Subgroup.commutator_mono hOK le_rfl)
  exact false_of_twoGroup_le_odd hS₀2 hSne hle h413

theorem lemma72_holds (hc : S6Ctx G p) (hin : Lemma72Inputs G p) : Lemma72At G p := by
  intro B x L n y J hB S
  have hp3 : 3 ≤ p := by
    have := hc.prime.two_le
    have := hc.odd
    omega
  have h3 := S.three_mul_le
  by_cases hsmall : n - p ≤ 9
  · have hp4 : p ≤ 4 := by omega
    have hp : p = 3 := by
      interval_cases p
      · rfl
      · exact absurd hc.prime (by norm_num)
    exact ⟨hp, by omega, by omega⟩
  · exact (lemma72_big hc hin hB S (by omega)).elim

end CFSG.LocalAnalysis.GLTheoremA
