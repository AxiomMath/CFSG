module

public import CFSG.LocalAnalysis.GLTheoremA.S11.CounterC
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs710
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma102

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S11

variable {G : Type} [Group G] [Finite G] {m p q : ℕ} {B : Subgroup G} {x : G} {L M D E F J : Subgroup G}
  {a : G} {S K : Subgroup G}

theorem isS0_of_isGStar {p : ℕ} {B K : Subgroup G} {x : G} (hS : IsSTriple p B x K) (hG : IsGStar p B K) : IsS0 p B x K := by
  refine ⟨hS, ?_⟩
  have h5 : tripleLevel p B K = 5 := by
    unfold tripleLevel
    rw [if_pos hG]
  have h1 : tripleLevel p B K ≤ dLevel G p := tripleLevel_le_dLevel hS
  have h2 : dLevel G p ≤ 5 := by
    refine csSup_le' ?_
    rintro j ⟨B', x', L', -, rfl⟩
    exact tripleLevel_le_five' p B' L'
  omega

theorem isS0_of_conf (hH : Hyp111 G m p B x L) (hc : CConf G p q B x L M D E F J a S K) (hess : IsEssential p B a) :
    IsS0 p B a K :=
  isS0_of_isGStar ⟨hH.bmax, hess, hc.K_comp⟩ hc.K_gstar

private theorem counterd_step_I_comp (hc : S3Ctx G p) (h183 : Input18_3_4) {B B' L L' : Subgroup G} {x x' : G}
    (hrel : PumpRel p (B, x, L) (B', x', L')) :
    GLAPComponent p (closureIn L' (Subgroup.zpowers x) ⊓ cx x) (Ipart p L x') := by
  obtain ⟨hIJ, -⟩ := S10.lemma102_I_le hc.prime h183 hc.kProper hc.simple hc.nonabelian hrel
  have hP := (pumpRel_facts hc.prime h183 hc.kProper hc.simple hc.nonabelian hrel).2.1
  have hIC : Ipart p L x' ≤ cx x :=
    (S10.lemma102_glaPLayer_le _).trans (inf_le_left.trans (hrel.1.2.2).1)
  exact glaPComponent_of_le hc.prime hP (le_inf hIJ hIC)
    (inf_le_inf_right _ (S10.lemma102_closureIn_mono_right (Subgroup.zpowers_le.2 hrel.2.2.1)))

theorem chev2_of_pumpRel (hc : S3Ctx G p) (hin : Chev2DownAt G p) (h183 : Input18_3_4) (h1122 : I1122IsoAt G p)
    {t t' : Triple G} (h : PumpRel p t t')
    (h' : IsChevSimple 2 (PSimple p t'.2.2)) : IsChevSimple 2 (PSimple p t.2.2) := by
  classical
  obtain ⟨B, x, L⟩ := t
  obtain ⟨B', x', L'⟩ := t'
  have hrel : PumpRel p (B, x, L) (B', x', L') := h
  have h2 : IsChevSimple 2 (PSimple p L') := h'
  show IsChevSimple 2 (PSimple p L)
  have hp := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hS := hrel.1
  have hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hS.2.2
  have hS' := hrel.2.1
  have hL'c : GLAPComponent p (Subgroup.centralizer ({x'} : Set G)) L' := hS'.2.2
  have hxB' : x ∈ B' := hrel.2.2.1
  have hx'B' : x' ∈ B' := hrel.2.2.2.2.1
  have hx'L : CentMod p L x' := hrel.2.2.2.2.2.1
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hS'.1.1 hx'B'
  obtain ⟨-, -, -, -, -, ⟨eIL⟩⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  have hIdiag := (pumpRel_facts hp h183 hc.kProper hc.simple hc.nonabelian hrel).2.1
  obtain ⟨eS⟩ := nonempty_pSimple_congr eIL
  suffices hI : IsChevSimple 2 (PSimple p (Ipart p L x')) from
    chev_isChevSimple_of_mulEquiv eS.symm hI
  by_cases hxN : x ∈ Subgroup.normalizer (L' : Set G)
  ·
    have hJ : GLAPComponent p (L' ⊓ Subgroup.centralizer ({x} : Set G)) (Ipart p L x') := by
      have h := counterd_step_I_comp hc h183 hrel
      rwa [closureIn_eq_self (Subgroup.zpowers_le.2 hxN)] at h
    have hKx' : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x'} : Set G)) :=
      isKGroup_of_isKProper hc.kProper
        (centralizer_ne_top_of_ne_one hc.simple hc.nonabelian hS'.2.1.2.1)
    have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1.1
    exact hin hp hc.odd (Subgroup.centralizer ({x'} : Set G)) L' x hKx' hL'c hxp hxN h2
      (Ipart p L x') hJ
  ·
    obtain ⟨e1⟩ := h1122 B' x' L' x hS'.1 hS'.2.1 hL'c hxB' hxN (Ipart p L x') hIdiag
    obtain ⟨hsimp, hnab⟩ := chev_pSimple_simple_nonabelian hp hL'c
    haveI := hsimp
    have hZ : Subgroup.center (PSimple p L') = ⊥ := chev_center_eq_bot_of_simple_nonabelian hnab
    have hcard : Nat.card (Subgroup.center (PQuot p (Ipart p L x'))) = 1 := by
      rw [Nat.card_congr (Subgroup.centerCongr e1).toEquiv, hZ]
      simp
    have hZI : Subgroup.center (PQuot p (Ipart p L x')) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
    have e2 : PSimple p (Ipart p L x') ≃* PQuot p (Ipart p L x') :=
      (QuotientGroup.quotientMulEquivOfEq hZI).trans QuotientGroup.quotientBot
    exact chev_isChevSimple_of_mulEquiv (e2.trans e1) h2

theorem chev2_of_pumpLe (hc : S3Ctx G p) (hin : Chev2DownAt G p) (h183 : Input18_3_4) (h1122 : I1122IsoAt G p)
    {t t' : Triple G} (h : PumpLe p t t')
    (h' : IsChevSimple 2 (PSimple p t'.2.2)) : IsChevSimple 2 (PSimple p t.2.2) := by
  obtain ⟨-, -, hchain⟩ := h
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl => exact h'
  | head hstep _ ih => exact chev2_of_pumpRel hc hin h183 h1122 hstep ih

theorem pump_chev2 (hsf : StageFacts G m) (hH : Hyp111 G m p B x L) (hc : CConf G p q B x L M D E F J a S K)
    (hS0 : IsS0 p B a K) (hSc : ¬ S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G))) :
    ∃ (B' : Subgroup G) (x' : G) (L' : Subgroup G), IsSStarMax p B' x' L' ∧ PumpLe p (B, a, K) (B', x', L') ∧
      IsChevSimple 2 (PSimple p L') := by
  obtain ⟨-, h4o, -, h5, -, -, h8, -, -⟩ := hsf p hH.mu
  obtain ⟨B', x', L', hS0M, hle⟩ := h4o.2.2.1 B a K hS0
  have hn : ¬ nGen B (closureIn K B) ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) := by
    intro hle'
    refine hSc (le_trans ?_ hle')
    rw [closureIn_eq_self hc.K_normB]
    exact le_iSup₂_of_le S ⟨hc.S_le_K, hc.S_two, hc.S_normB⟩ le_rfl
  have hn' := h4o.2.2.2.2.2.1 (B, a, K) (B', x', L') hle hn
  have hBN : B' ≤ Subgroup.normalizer (L' : Set G) := hS0M.2.2
  have hn'' : ¬ nGen B' L' ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x'} : Set G)) := by
    simpa only [closureIn_eq_self hBN] using hn'
  have hT : ∃ T : Subgroup G, T ≤ L' ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ B' ≤ Subgroup.normalizer (T : Set G) := by
    by_contra hno
    refine hn'' (iSup₂_le fun T hT => ?_)
    have hTbot : T = ⊥ := by
      by_contra hne
      exact hno ⟨T, hT.1, hne, hT.2.1, hT.2.2⟩
    rw [hTbot]
    exact bot_le
  obtain ⟨T, hTL, hTne, hT2, hBT⟩ := hT
  have hcyc : CycModSylow p L' := h5.2.2 B' x' L' hS0M ⟨T, hTL.trans le_sup_left, hTne, hT2, hBT⟩
  have hSS : IsSStarMax p B' x' L' := ⟨hS0M, hcyc⟩
  exact ⟨B', x', L', hSS, hle, h8.1 B' x' L' hSS⟩

private theorem counterd_isPGroup_subgroupOf {q : ℕ} {H K : Subgroup G} (hH : IsPGroup q H) :
    IsPGroup q (H.subgroupOf K) := by
  intro g
  obtain ⟨k, hk⟩ := hH ⟨((g : K) : G), Subgroup.mem_subgroupOf.1 g.2⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (fun x : ↥H => (x : G)) hk
  simpa using h

theorem frattini_V {q : ℕ} (hq : q.Prime) {K V R : Subgroup G} (hVK : V ≤ K) (hVn : K ≤ Subgroup.normalizer (V : Set G))
    (hR : IsPGroup q R) (hRV : R ≤ V) (hRmax : ∀ Q : Subgroup G, IsPGroup q Q → Q ≤ V → R ≤ Q → Q = R) :
    K ≤ V ⊔ (Subgroup.normalizer (R : Set G) ⊓ K) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hNn : (V.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).2 hVn
  haveI := hNn
  let P : Sylow q ↥(V.subgroupOf K) :=
    { toSubgroup := (R.subgroupOf K).subgroupOf (V.subgroupOf K)
      isPGroup' := counterd_isPGroup_subgroupOf (counterd_isPGroup_subgroupOf hR)
      is_maximal' := by
        intro Q hQ hRQ
        have hQg : IsPGroup q (Q.map ((K.subtype).comp ((V.subgroupOf K).subtype))) := hQ.map _
        have hQV : Q.map ((K.subtype).comp ((V.subgroupOf K).subtype)) ≤ V := by
          rintro _ ⟨x, -, rfl⟩
          exact Subgroup.mem_subgroupOf.1 x.2
        have hRQg : R ≤ Q.map ((K.subtype).comp ((V.subgroupOf K).subtype)) := by
          intro r hr
          have hrK : r ∈ K := hVK (hRV hr)
          have hrN : (⟨r, hrK⟩ : K) ∈ V.subgroupOf K := Subgroup.mem_subgroupOf.2 (hRV hr)
          have hmem : (⟨⟨r, hrK⟩, hrN⟩ : ↥(V.subgroupOf K)) ∈ Q :=
            hRQ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 hr))
          exact ⟨_, hmem, rfl⟩
        have hQeq := hRmax _ hQg hQV hRQg
        apply le_antisymm
        · intro x hx
          have hxR : ((x : K) : G) ∈ R := by
            have hmem : ((x : K) : G) ∈ Q.map ((K.subtype).comp ((V.subgroupOf K).subtype)) :=
              ⟨x, hx, rfl⟩
            rw [hQeq] at hmem
            exact hmem
          exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 hxR)
        · exact hRQ }
  intro k hk
  have htop := Sylow.normalizer_sup_eq_top P
  have hk' : (⟨k, hk⟩ : ↥K) ∈ (⊤ : Subgroup ↥K) := Subgroup.mem_top _
  rw [← htop, sup_comm] at hk'
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hk'
  have hyV : (y : G) ∈ V := Subgroup.mem_subgroupOf.1 hy
  have hzK : (z : G) ∈ K := z.2
  have hconj : ∀ g : K, g ∈ Subgroup.normalizer ((P : Subgroup ↥(V.subgroupOf K)).map
      (V.subgroupOf K).subtype : Set K) → ∀ h : G, h ∈ R → (g : G) * h * (g : G)⁻¹ ∈ R := by
    intro g hg h hh
    have hhK : h ∈ K := hVK (hRV hh)
    have hmem : (⟨h, hhK⟩ : K) ∈ (P : Subgroup ↥(V.subgroupOf K)).map (V.subgroupOf K).subtype := by
      rw [show (P : Subgroup ↥(V.subgroupOf K)) = (R.subgroupOf K).subgroupOf (V.subgroupOf K) from rfl,
        Subgroup.subgroupOf_map_subtype, Subgroup.mem_inf]
      exact ⟨Subgroup.mem_subgroupOf.2 hh, Subgroup.mem_subgroupOf.2 (hRV hh)⟩
    have hconjmem := (Subgroup.mem_normalizer_iff.1 hg _).1 hmem
    rw [show (P : Subgroup ↥(V.subgroupOf K)) = (R.subgroupOf K).subgroupOf (V.subgroupOf K) from rfl,
      Subgroup.subgroupOf_map_subtype, Subgroup.mem_inf] at hconjmem
    exact Subgroup.mem_subgroupOf.1 hconjmem.1
  have hzN : (z : G) ∈ Subgroup.normalizer (R : Set G) := by
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hconj z hz h hh, fun hh => ?_⟩
    have := hconj z⁻¹ (Subgroup.inv_mem _ hz) _ hh
    simpa [mul_assoc] using this
  have hkG : (y : G) * (z : G) = k := by
    have := congrArg Subtype.val hyz
    simpa using this
  rw [← hkG]
  exact mul_mem (le_sup_left (a := V) hyV) (le_sup_right (a := V) ⟨hzN, hzK⟩)

theorem commutator_core_le (p : ℕ) (K : Subgroup G) : (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) ≤ K :=
  commutator_le_of_le' le_rfl (Subgroup.map_subtype_le _)

theorem commutator_core_le_core (p : ℕ) (K : Subgroup G) :
    (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p K := by
  rw [Subgroup.commutator_le]
  intro k hk o ho
  rw [commutatorElement_def]
  have h1 : k * o * k⁻¹ ∈ GLAPPrimeCoreOf p K :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p K hk) o).1 ho
  exact (GLAPPrimeCoreOf p K).mul_mem h1 ((GLAPPrimeCoreOf p K).inv_mem ho)

theorem core_le_oPPrimeP (p : ℕ) (K : Subgroup G) : GLAPPrimeCoreOf p K ≤ oPPrimeP p K := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥K) y = 1 := (QuotientGroup.eq_one_iff y).2 hy
  show QuotientGroup.mk' (GLAPPrimeCore p ↥K) y ∈ CFSG.pCore p (↥K ⧸ GLAPPrimeCore p ↥K)
  rw [h1]
  exact Subgroup.one_mem _

theorem le_normalizer_commutator_core {p : ℕ} {K F : Subgroup G} (hF : F ≤ Subgroup.normalizer (K : Set G)) :
    F ≤ Subgroup.normalizer ((⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) : Set G) := by
  intro g hg
  have h1 := mem_normalizer_iff_gLBConj_eq.1 (hF hg)
  have h2 : GLBConj g (GLAPPrimeCoreOf p K) = GLAPPrimeCoreOf p K := by
    rw [← glaPPrimeCoreOf_gLBConj, h1]
  rw [mem_normalizer_iff_gLBConj_eq]
  unfold GLBConj at h1 h2 ⊢
  rw [Subgroup.map_commutator, h1, h2]

theorem eq_bot_of_forall_qpower {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {X K : Subgroup G}
    (hK : GLAPComponent p X K) (Y : Subgroup (PSimple p K)) [Y.Normal]
    (hY : ∀ s ∈ Y, ∃ n : ℕ, s ^ (q ^ n) = 1) : Y = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsSimpleGroup (PSimple p K) := S9.isSimple_pSimple hp hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with hbot | htop
  · exact hbot
  · exfalso
    have hqgroup : IsPGroup q (PSimple p K) := by
      intro s
      have hs : s ∈ Y := by
        rw [htop]
        exact Subgroup.mem_top s
      exact hY s hs
    haveI : Nontrivial (Subgroup.center (PSimple p K)) := IsPGroup.center_nontrivial hqgroup
    have hcenter := IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PSimple p K))
    obtain ⟨a, b, hab⟩ := S9.pSimple_nonabelian hp hK
    rcases hcenter with hc | hc
    · obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center (PSimple p K))
      apply hz
      apply Subtype.ext
      have hzbot : (z : PSimple p K) ∈ (⊥ : Subgroup (PSimple p K)) := by
        rw [← hc]
        exact z.2
      simpa using Subgroup.mem_bot.1 hzbot
    · have ha : a ∈ Subgroup.center (PSimple p K) := by
        rw [hc]
        exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm

private theorem counterd_not_dvd_relIndex {q : ℕ} (hq : q.Prime) {V R : Subgroup G} (hR : IsPGroup q R)
    (hRV : R ≤ V) (hRmax : ∀ Q : Subgroup G, IsPGroup q Q → Q ≤ V → R ≤ Q → Q = R) :
    ¬ q ∣ R.relIndex V := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hP⟩ := (counterd_isPGroup_subgroupOf (K := V) hR).exists_le_sylow
  have hmap : (P : Subgroup ↥V).map V.subtype = R := by
    refine hRmax _ (P.isPGroup'.map _) (Subgroup.map_subtype_le _) ?_
    intro r hr
    exact ⟨⟨r, hRV hr⟩, hP (Subgroup.mem_subgroupOf.2 hr), rfl⟩
  rw [← hmap]
  have hidx : ((P : Subgroup ↥V).map V.subtype).relIndex V = (P : Subgroup ↥V).index := by
    unfold Subgroup.relIndex Subgroup.subgroupOf
    rw [Subgroup.comap_map_eq_self_of_injective V.subtype_injective]
  rw [hidx]
  exact P.not_dvd_index

private def counterd_conjAut {R : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    MulAut ↥R where
  toFun r := ⟨g * (r : G) * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg (r : G)).1 r.2⟩
  invFun r := ⟨g⁻¹ * (r : G) * g, by
    have h := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) (r : G)).1 r.2
    simpa [mul_assoc] using h⟩
  left_inv r := Subtype.ext (by simp [mul_assoc])
  right_inv r := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

private theorem counterd_conj_pow {R : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (R : Set G))
    (m : ℕ) (r : ↥R) : (((counterd_conjAut hg) ^ m) r : G) = g ^ m * (r : G) * (g ^ m)⁻¹ := by
  induction m generalizing r with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (counterd_conjAut hg) m, MulAut.mul_apply, ih]
    show g ^ m * (g * (r : G) * g⁻¹) * (g ^ m)⁻¹ = g ^ (m + 1) * (r : G) * (g ^ (m + 1))⁻¹
    group

private theorem counterd_pow_centralizer {q : ℕ} {R : Subgroup G} {D : Subgroup ↥R}
    (hDfix : IsPGroup q (fixingSubgroup (MulAut ↥R) (D : Set ↥R))) {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) (hgD : ∀ d ∈ D, g * (d : G) * g⁻¹ = d) :
    ∃ n : ℕ, g ^ (q ^ n) ∈ Subgroup.centralizer (R : Set G) := by
  have hσ : counterd_conjAut hg ∈ fixingSubgroup (MulAut ↥R) (D : Set ↥R) := by
    rw [mem_fixingSubgroup_iff]
    intro d hd
    exact Subtype.ext (hgD d hd)
  obtain ⟨n, hn⟩ := hDfix ⟨counterd_conjAut hg, hσ⟩
  have hn' : counterd_conjAut hg ^ (q ^ n) = 1 := by
    have h := congrArg Subtype.val hn
    simpa using h
  refine ⟨n, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
  have key : h = g ^ (q ^ n) * h * (g ^ (q ^ n))⁻¹ := by
    have h1 := counterd_conj_pow hg (q ^ n) ⟨h, hh⟩
    rw [hn'] at h1
    exact h1
  calc h * g ^ (q ^ n) = (g ^ (q ^ n) * h * (g ^ (q ^ n))⁻¹) * g ^ (q ^ n) := by rw [← key]
    _ = g ^ (q ^ n) * h := by group

private theorem counterd_factor {K V R : Subgroup G} (hVK : V ≤ K)
    (hVn : K ≤ Subgroup.normalizer (V : Set G)) (hfr : K ≤ V ⊔ (Subgroup.normalizer (R : Set G) ⊓ K))
    {k : G} (hk : k ∈ K) : ∃ v ∈ V, ∃ n ∈ Subgroup.normalizer (R : Set G) ⊓ K, v * n = k := by
  haveI : (V.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).2 hVn
  have hle : V ⊔ (Subgroup.normalizer (R : Set G) ⊓ K) ≤
      ((V.subgroupOf K) ⊔ ((Subgroup.normalizer (R : Set G) ⊓ K).subgroupOf K)).map K.subtype := by
    refine sup_le (fun v hv => ⟨⟨v, hVK hv⟩, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hv), rfl⟩) ?_
    intro n hn
    exact ⟨⟨n, (Subgroup.mem_inf.1 hn).2⟩, Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hn), rfl⟩
  obtain ⟨w, hw, hwk⟩ := Subgroup.mem_map.1 (hle (hfr hk))
  have hwe : w = ⟨k, hk⟩ := Subtype.ext hwk
  rw [hwe] at hw
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hw
  refine ⟨(y : G), Subgroup.mem_subgroupOf.1 hy, (z : G), Subgroup.mem_subgroupOf.1 hz, ?_⟩
  have h := congrArg Subtype.val hyz
  simpa using h

theorem exists_R2 (h1810 : Input18_10) (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    {X K V R : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hK : GLAPComponent p X K) (hVdef : V = ⁅K, GLAPPrimeCoreOf p K⁆) (hqV : q ∣ Nat.card V)
    (hR : IsPGroup q R) (hRV : R ≤ V) (hRmax : ∀ Q : Subgroup G, IsPGroup q Q → Q ≤ V → R ≤ Q → Q = R) :
    ∃ R₂ : Subgroup G, R₂ ≤ R ∧ R₂ ≠ ⊥ ∧ (∀ g ∈ Subgroup.normalizer (R : Set G), g ∈ Subgroup.normalizer (R₂ : Set G)) ∧
      (∀ g ∈ R₂, g ^ q = 1) ∧ ⁅R₂, R₂⁆ ≤ Subgroup.centralizer (R₂ : Set G) ∧
      K ⊓ Subgroup.normalizer (R : Set G) ⊓ Subgroup.centralizer (R₂ : Set G) ≤ oPPrimeP p K := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  subst hVdef
  have hKX : K ≤ X := hK.1
  have hKXg : CFSG.Open.IsKGroup ↥K :=
    hX.of_injective (Subgroup.inclusion hKX) (Subgroup.inclusion_injective hKX)
  have hKK : GLAPComponent p K K := glaPComponent_of_le hp hK le_rfl hKX
  have hVK : (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) ≤ K := commutator_core_le p K
  have hVcore : (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p K :=
    commutator_core_le_core p K
  have hVn : K ≤ Subgroup.normalizer ((⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left _ _
  have hfr : K ≤ (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) ⊔ (Subgroup.normalizer (R : Set G) ⊓ K) :=
    frattini_V hq hVK hVn hR hRV hRmax
  have hRsyl : ¬ q ∣ R.relIndex (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) :=
    counterd_not_dvd_relIndex hq hR hRV hRmax
  have hRne : R ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.relIndex_bot_left] at hRsyl
    exact hRsyl hqV
  haveI : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).2 hRne
  have hCR : K ⊓ Subgroup.centralizer (R : Set G) ≤ oPPrimeP p K :=
    h1810 G K hKXg p hp hKK q hq R hqV hRV hR hRsyl
  obtain ⟨D, hDchar, hDne, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hq2 hR
  have hR₂N : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ x ∈ D.map R.subtype,
      g * x * g⁻¹ ∈ D.map R.subtype := by
    intro g hg x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨counterd_conjAut hg d, ?_, rfl⟩
    have h1 : d ∈ D.comap (counterd_conjAut hg).toMonoidHom := by
      rw [hDchar.fixed (counterd_conjAut hg)]
      exact hd
    exact h1
  have hNR₂ : ∀ g ∈ Subgroup.normalizer (R : Set G),
      g ∈ Subgroup.normalizer ((D.map R.subtype : Subgroup G) : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hR₂N g hg h hh, fun hh => ?_⟩
    have h2 := hR₂N _ (inv_mem hg) _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at h2
  have hcomm : ⁅(D.map R.subtype : Subgroup G), (D.map R.subtype : Subgroup G)⁆ ≤
      Subgroup.centralizer ((D.map R.subtype : Subgroup G) : Set G) := by
    rw [← Subgroup.map_commutator]
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hz
    have hyD : y ∈ D ⊓ Subgroup.centralizer (D : Set ↥R) :=
      hDcomm (Subgroup.commutator_mono (le_refl D) le_top hy)
    have hdy : d * y = y * d := Subgroup.mem_centralizer_iff.1 hyD.2 d hd
    rw [← map_mul, ← map_mul, hdy]
  have hexp : ∀ g ∈ D.map R.subtype, g ^ q = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_pow, hDexp d hd, map_one]
  have hne : D.map R.subtype ≠ ⊥ := by
    intro h
    apply hDne
    rw [eq_bot_iff]
    intro d hd
    have hmem : R.subtype d ∈ D.map R.subtype := Subgroup.mem_map_of_mem _ hd
    rw [h, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by simpa using hmem)
  have hcentD : ∀ g : G, g ∈ Subgroup.centralizer ((D.map R.subtype : Subgroup G) : Set G) →
      ∀ d ∈ D, g * (d : G) * g⁻¹ = d := by
    intro g hg d hd
    have h1 := Subgroup.mem_centralizer_iff.1 hg (R.subtype d) (Subgroup.mem_map_of_mem _ hd)
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  have hfinal : K ⊓ Subgroup.normalizer (R : Set G) ⊓
      Subgroup.centralizer ((D.map R.subtype : Subgroup G) : Set G) ≤ oPPrimeP p K := by
    rintro g ⟨⟨hgK, hgN⟩, hgC⟩
    let pr : ↥K →* PQuot p K := QuotientGroup.mk' (GLAPPrimeCore p ↥K)
    let ps : PQuot p K →* PSimple p K := QuotientGroup.mk' (Subgroup.center (PQuot p K))
    have hprs : Function.Surjective pr := QuotientGroup.mk'_surjective _
    have hpss : Function.Surjective ps := QuotientGroup.mk'_surjective _
    let C0 : Subgroup ↥K :=
      (Subgroup.normalizer (R : Set G) ⊓
        Subgroup.centralizer ((D.map R.subtype : Subgroup G) : Set G)).subgroupOf K
    have hC0mem : ∀ c : ↥K, c ∈ C0 ↔ ((c : G) ∈ Subgroup.normalizer (R : Set G) ∧
        (c : G) ∈ Subgroup.centralizer ((D.map R.subtype : Subgroup G) : Set G)) :=
      fun c => Subgroup.mem_subgroupOf.trans Subgroup.mem_inf
    have hfac : ∀ k : ↥K, ∃ n : ↥K, (n : G) ∈ Subgroup.normalizer (R : Set G) ∧ pr k = pr n := by
      intro k
      obtain ⟨v, hv, n, hn, hvn⟩ := counterd_factor hVK hVn hfr k.2
      have hnK : n ∈ K := (Subgroup.mem_inf.1 hn).2
      have hvK : (⟨v, hVK hv⟩ : ↥K) ∈ GLAPPrimeCore p ↥K := by
        obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.1 (hVcore hv)
        rwa [show w = ⟨v, hVK hv⟩ from Subtype.ext hwv] at hw
      refine ⟨⟨n, hnK⟩, (Subgroup.mem_inf.1 hn).1, ?_⟩
      have hk : k = (⟨v, hVK hv⟩ : ↥K) * ⟨n, hnK⟩ := Subtype.ext hvn.symm
      have h1 : pr ⟨v, hVK hv⟩ = 1 := (QuotientGroup.eq_one_iff (⟨v, hVK hv⟩ : ↥K)).2 hvK
      rw [hk, map_mul, h1, one_mul]
    have hC0conj : ∀ n : ↥K, (n : G) ∈ Subgroup.normalizer (R : Set G) →
        ∀ c ∈ C0, n * c * n⁻¹ ∈ C0 := by
      intro n hn c hc
      obtain ⟨hcN, hcC⟩ := (hC0mem c).1 hc
      rw [hC0mem]
      refine ⟨?_, ?_⟩
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact mul_mem (mul_mem hn hcN) (inv_mem hn)
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hw := hR₂N _ (inv_mem hn) z hz
        rw [inv_inv] at hw
        have hwc := Subgroup.mem_centralizer_iff.1 hcC _ hw
        calc z * ((n : G) * (c : G) * (n : G)⁻¹)
            = (n : G) * (((n : G)⁻¹ * z * (n : G)) * (c : G)) * (n : G)⁻¹ := by group
          _ = (n : G) * ((c : G) * ((n : G)⁻¹ * z * (n : G))) * (n : G)⁻¹ := by rw [hwc]
          _ = (n : G) * (c : G) * (n : G)⁻¹ * z := by group
    let Y : Subgroup (PQuot p K) := C0.map pr
    have hYn : Y.Normal := by
      refine ⟨fun y hy ψ => ?_⟩
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨k, rfl⟩ := hprs ψ
      obtain ⟨n, hnN, hkn⟩ := hfac k
      rw [hkn]
      have e : pr n * pr c * (pr n)⁻¹ = pr (n * c * n⁻¹) := by simp only [map_mul, map_inv]
      rw [e]
      exact Subgroup.mem_map_of_mem pr (hC0conj n hnN c hc)
    let Ys : Subgroup (PSimple p K) := Y.map ps
    haveI hYsn : Ys.Normal := Subgroup.Normal.map hYn ps hpss
    have hcen : ∀ c : ↥K, c ∈ C0 →
        ∃ n : ℕ, QuotientGroup.mk (c ^ (q ^ n)) ∈ Subgroup.center (PQuot p K) := by
      intro c hc
      obtain ⟨hcN, hcC⟩ := (hC0mem c).1 hc
      obtain ⟨n, hn⟩ := counterd_pow_centralizer hDfix hcN (hcentD _ hcC)
      refine ⟨n, ((S9.pComponent_basic hp hK).1 (c ^ (q ^ n))).mp ?_⟩
      apply hCR
      refine ⟨(c ^ (q ^ n)).2, ?_⟩
      rw [Subgroup.coe_pow]
      exact hn
    have hYspow : ∀ s ∈ Ys, ∃ n : ℕ, s ^ (q ^ n) = 1 := by
      intro s hs
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hs
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨n, hn⟩ := hcen c hc
      refine ⟨n, ?_⟩
      rw [← map_pow, ← map_pow]
      exact (QuotientGroup.eq_one_iff (QuotientGroup.mk (c ^ (q ^ n)) : PQuot p K)).2 hn
    have hYsbot : Ys = ⊥ := eq_bot_of_forall_qpower hp hq hK Ys hYspow
    have hgC0 : (⟨g, hgK⟩ : ↥K) ∈ C0 := (hC0mem _).2 ⟨hgN, hgC⟩
    have hmem : ps (pr ⟨g, hgK⟩) ∈ Ys :=
      Subgroup.mem_map_of_mem ps (Subgroup.mem_map_of_mem pr hgC0)
    rw [hYsbot, Subgroup.mem_bot] at hmem
    exact ((S9.pComponent_basic hp hK).1 ⟨g, hgK⟩).2 ((QuotientGroup.eq_one_iff (pr ⟨g, hgK⟩)).1 hmem)
  exact ⟨D.map R.subtype, Subgroup.map_subtype_le _, hne, hNR₂, hexp, hcomm, hfinal⟩

private theorem counterd_solv_of_card {H : Type} [Group H] [Finite H] {d p q a b : ℕ} (hd : Nat.card H = d)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hdpq : d = p ^ a * q ^ b) : Group.IsSolvable H := by
  haveI : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card, hd, hdpq])

private theorem counterd_small_solv {H : Type} [Group H] [Finite H] {d : ℕ} (hd : Nat.card H = d)
    (hmem : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 10 ∨ d = 12 ∨ d = 14 ∨
      d = 21 ∨ d = 24 ∨ d = 28) : Group.IsSolvable H := by
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact counterd_solv_of_card hd (p := 2) (q := 3) (a := 0) (b := 0) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 2) (q := 3) (a := 1) (b := 0) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 2) (q := 3) (a := 0) (b := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 2) (q := 3) (a := 2) (b := 0) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 5) (q := 2) (a := 1) (b := 0) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 2) (q := 3) (a := 1) (b := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 7) (q := 2) (a := 1) (b := 0) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 2) (q := 3) (a := 3) (b := 0) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 2) (q := 5) (a := 1) (b := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 2) (q := 3) (a := 2) (b := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 2) (q := 7) (a := 1) (b := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 3) (q := 7) (a := 1) (b := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 2) (q := 3) (a := 3) (b := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact counterd_solv_of_card hd (p := 2) (q := 7) (a := 2) (b := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

private theorem counterd_core_inf_le {p : ℕ} (hp : p.Prime) {K J : Subgroup G} (hJK : J ≤ K) :
    GLAPPrimeCoreOf p K ⊓ J ≤ GLAPPrimeCoreOf p J := by
  have hnorm : ((GLAPPrimeCoreOf p K ⊓ J).subgroupOf J).Normal := by
    constructor
    intro u hu g
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    have hg : (g : G) ∈ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) :=
      le_normalizer_glaPPrimeCoreOf p K (hJK g.2)
    have h1 := (Subgroup.mem_normalizer_iff.1 hg (u : G)).1 hu.1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨h1, J.mul_mem (J.mul_mem g.2 hu.2) (J.inv_mem g.2)⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card ((GLAPPrimeCoreOf p K ⊓ J).subgroupOf J)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : GLAPPrimeCoreOf p K ⊓ J ≤ J)).toEquiv]
    have h2 : Nat.card (GLAPPrimeCoreOf p K) = Nat.card (GLAPPrimeCore p ↥K) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective K)
    have hd : Nat.card ↥(GLAPPrimeCoreOf p K ⊓ J) ∣ Nat.card (GLAPPrimeCore p ↥K) := by
      rw [← h2]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥K)).coprime_dvd_right hd
  have hsub : (GLAPPrimeCoreOf p K ⊓ J).subgroupOf J ≤ CFSG.pPrimeCore p ↥J := le_sSup ⟨hnorm, hcop⟩
  intro g hg
  exact ⟨⟨g, hg.2⟩, hsub (Subgroup.mem_subgroupOf.2 hg), rfl⟩

private theorem counterd_core_of_comm {p : ℕ} {K : Subgroup G} {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (h : (QuotientGroup.mk ⟨a, ha⟩ : PQuot p K) * QuotientGroup.mk ⟨b, hb⟩ =
      QuotientGroup.mk ⟨b, hb⟩ * QuotientGroup.mk ⟨a, ha⟩) :
    (a * b)⁻¹ * (b * a) ∈ GLAPPrimeCoreOf p K := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  exact ⟨_, h, rfl⟩

private theorem counterd_comm_of_core {p : ℕ} (hp : p.Prime) {K J : Subgroup G} (hJK : J ≤ K) {a b : G}
    (ha : a ∈ J) (hb : b ∈ J) (h : (a * b)⁻¹ * (b * a) ∈ GLAPPrimeCoreOf p K) :
    (QuotientGroup.mk ⟨a, ha⟩ : PQuot p J) * QuotientGroup.mk ⟨b, hb⟩ =
      QuotientGroup.mk ⟨b, hb⟩ * QuotientGroup.mk ⟨a, ha⟩ := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have hJm : (a * b)⁻¹ * (b * a) ∈ J := J.mul_mem (J.inv_mem (J.mul_mem ha hb)) (J.mul_mem hb ha)
  obtain ⟨z, hz, hzy⟩ := counterd_core_inf_le hp hJK ⟨h, hJm⟩
  have hzx : z = ((⟨a, ha⟩ : ↥J) * ⟨b, hb⟩)⁻¹ * (⟨b, hb⟩ * ⟨a, ha⟩) := Subtype.ext hzy
  exact hzx ▸ hz

theorem not_small_of_proper {p : ℕ} (hp : p.Prime) {X K J : Subgroup G} (hK : GLAPComponent p X K)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) J) (hJK : ¬ K ≤ J ⊔ GLAPPrimeCoreOf p K) :
    Nat.card (PSimple p K) ≠ 60 ∧ Nat.card (PSimple p K) ≠ 168 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hJK0 : J ≤ K := hJ.1.trans inf_le_left
  have hsK : IsSimpleGroup (PSimple p K) := S9.isSimple_pSimple hp hK
  have hsJ : IsSimpleGroup (PSimple p J) := S9.isSimple_pSimple hp hJ
  obtain ⟨c₁, c₂, hc⟩ := S9.pSimple_nonabelian hp hJ
  have hTnot : ¬ Group.IsSolvable (PSimple p J) := fun hs =>
    hc (IsSimpleGroup.comm_iff_isSolvable.2 hs c₁ c₂)
  have hQ : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  let ψ : ↥K →* PSimple p K :=
    (QuotientGroup.mk' (Subgroup.center (PQuot p K))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥K))
  let ψJ : ↥J →* PSimple p K := ψ.comp (Subgroup.inclusion hJK0)
  let πJ : ↥J →* PSimple p J :=
    (QuotientGroup.mk' (Subgroup.center (PQuot p J))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥J))
  have hπJs : Function.Surjective πJ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hψker : ∀ k : ↥K, ψ k = 1 ↔ (k : G) ∈ oPPrimeP p K := by
    intro k
    rw [(S9.pComponent_basic hp hK).1 k]
    exact QuotientGroup.eq_one_iff (QuotientGroup.mk k)
  have hHtop : ψJ.range ≠ ⊤ := by
    intro htop
    have hsurj : ∀ k : ↥K, ∃ j : ↥K, (j : G) ∈ J ∧ ∃ z ∈ Subgroup.center (PQuot p K),
        (QuotientGroup.mk k : PQuot p K) = QuotientGroup.mk j * z := by
      intro k
      have hk : ψ k ∈ ψJ.range := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨j₀, hj₀⟩ := hk
      have he : ((QuotientGroup.mk k : PQuot p K) : PSimple p K) =
          ((QuotientGroup.mk (Subgroup.inclusion hJK0 j₀) : PQuot p K) : PSimple p K) := hj₀.symm
      rw [QuotientGroup.eq] at he
      refine ⟨Subgroup.inclusion hJK0 j₀, j₀.2, ((QuotientGroup.mk k : PQuot p K)⁻¹ *
        QuotientGroup.mk (Subgroup.inclusion hJK0 j₀))⁻¹, Subgroup.inv_mem _ he, ?_⟩
      group
    have hcomm : ∀ q₁ q₂ : PQuot p K,
        ⁅q₁, q₂⁆ ∈ (J.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) := by
      intro q₁ q₂
      obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective q₁
      obtain ⟨k₂, rfl⟩ := QuotientGroup.mk_surjective q₂
      obtain ⟨j₁, hj₁, z₁, hz₁, e₁⟩ := hsurj k₁
      obtain ⟨j₂, hj₂, z₂, hz₂, e₂⟩ := hsurj k₂
      have hcJ : (⁅j₁, j₂⁆ : ↥K) ∈ J.subgroupOf K := by
        simp only [Subgroup.mem_subgroupOf, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        exact J.mul_mem (J.mul_mem (J.mul_mem hj₁ hj₂) (J.inv_mem hj₁)) (J.inv_mem hj₂)
      have e : ⁅(QuotientGroup.mk j₁ : PQuot p K), QuotientGroup.mk j₂⁆ =
          QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⁅j₁, j₂⁆ :=
        (map_commutatorElement (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) j₁ j₂).symm
      rw [e₁, e₂, commutatorElement_mul_center_left hz₁, commutatorElement_mul_center_right hz₂, e]
      exact Subgroup.mem_map_of_mem _ hcJ
    have htopQ : (⊤ : Subgroup (PQuot p K)) ≤
        (J.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) := by
      have h1 : (⁅(⊤ : Subgroup (PQuot p K)), ⊤⁆ : Subgroup (PQuot p K)) ≤
          (J.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) :=
        Subgroup.commutator_le.2 (fun q₁ _ q₂ _ => hcomm q₁ q₂)
      have h2 : (⁅(⊤ : Subgroup (PQuot p K)), ⊤⁆ : Subgroup (PQuot p K)) = ⊤ := hQ.1
      rwa [h2] at h1
    apply hJK
    intro k hk
    have hmem := htopQ (Subgroup.mem_top (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : PQuot p K))
    obtain ⟨j, hj, hjeq⟩ := Subgroup.mem_map.1 hmem
    have hjrel : j⁻¹ * (⟨k, hk⟩ : ↥K) ∈ GLAPPrimeCore p ↥K := QuotientGroup.eq.1 hjeq
    have hO : ((j⁻¹ * (⟨k, hk⟩ : ↥K) : ↥K) : G) ∈ GLAPPrimeCoreOf p K := ⟨_, hjrel, rfl⟩
    have hk' : k = (j : G) * ((j⁻¹ * (⟨k, hk⟩ : ↥K) : ↥K) : G) := by simp
    rw [hk']
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 hj) hO
  have hN : ψJ.ker ≤ πJ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxc : (QuotientGroup.mk (Subgroup.inclusion hJK0 x) : PQuot p K) ∈
        Subgroup.center (PQuot p K) :=
      (S9.pComponent_basic hp hK).1 _ |>.1 ((hψker _).1 hx)
    have hxJ : (QuotientGroup.mk x : PQuot p J) ∈ Subgroup.center (PQuot p J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective g
      have h1 := Subgroup.mem_center_iff.1 hxc (QuotientGroup.mk (Subgroup.inclusion hJK0 j))
      exact counterd_comm_of_core hp hJK0 j.2 x.2 (counterd_core_of_comm (hJK0 j.2) (hJK0 x.2) h1)
    exact (QuotientGroup.eq_one_iff (QuotientGroup.mk x)).2 hxJ
  have key : Nat.card (PSimple p K) = 60 ∨ Nat.card (PSimple p K) = 168 → False := by
    intro hn
    have hnorm : ψJ.range.normalCore = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψJ.range.normalCore with h | h
      · exact h
      · exact absurd (eq_top_iff.2 (h ▸ Subgroup.normalCore_le _)) hHtop
    have hdvd : Nat.card (PSimple p K) ∣ Nat.factorial ψJ.range.index := by
      have h := Subgroup.index_normalCore_dvd_factorial_index ψJ.range
      rwa [hnorm, Subgroup.index_bot] at h
    have hm5 : 5 ≤ ψJ.range.index := by
      by_contra hlt
      push_neg at hlt
      interval_cases hi : ψJ.range.index <;> rcases hn with hn | hn <;> rw [hn] at hdvd <;>
        norm_num [Nat.factorial] at hdvd
    have hsolvH : Group.IsSolvable ↥ψJ.range := by
      have hmul := Subgroup.card_mul_index (H := ψJ.range)
      obtain ⟨d, hd⟩ : ∃ d, Nat.card ↥ψJ.range = d := ⟨_, rfl⟩
      rw [hd] at hmul
      have hdiv : d * ψJ.range.index = 60 ∨ d * ψJ.range.index = 168 := hmul ▸ hn
      have hdle : d ≤ 33 := by rcases hdiv with h | h <;> nlinarith
      have hmem : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 10 ∨ d = 12 ∨
          d = 14 ∨ d = 21 ∨ d = 24 ∨ d = 28 := by
        interval_cases d <;> omega
      exact counterd_small_solv hd hmem
    have hquot : Group.IsSolvable (↥J ⧸ ψJ.ker) :=
      Group.isSolvable_of_isSolvable_injective (f := (QuotientGroup.quotientKerEquivRange ψJ).toMonoidHom)
        (QuotientGroup.quotientKerEquivRange ψJ).injective
    have hF : Function.Surjective (QuotientGroup.lift ψJ.ker πJ hN) := by
      intro t
      obtain ⟨x, rfl⟩ := hπJs t
      exact ⟨QuotientGroup.mk x, rfl⟩
    exact hTnot (Group.isSolvable_of_surjective hF)
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

theorem three_le_pRank_R2 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) {X K V R R₂ : Subgroup G}
    (hK : GLAPComponent p X K) (hVdef : V = ⁅K, GLAPPrimeCoreOf p K⁆)
    (hfr : K ≤ V ⊔ (Subgroup.normalizer (R : Set G) ⊓ K))
    (hN : ∀ g ∈ Subgroup.normalizer (R : Set G), g ∈ Subgroup.normalizer (R₂ : Set G))
    (hexp : ∀ g ∈ R₂, g ^ q = 1) (hcl : ⁅R₂, R₂⁆ ≤ Subgroup.centralizer (R₂ : Set G))
    (hcen : K ⊓ Subgroup.normalizer (R : Set G) ⊓ Subgroup.centralizer (R₂ : Set G) ≤ oPPrimeP p K)
    (hnot : ¬ S9.InvolvedSL2 q (PSimple p K)) : 3 ≤ CFSG.Open.pRank q R₂ := by
  by_contra hlt
  have hr : CFSG.Open.pRank q R₂ ≤ 2 := by omega
  have hcl' : ∀ a ∈ R₂, ∀ b ∈ R₂, ∀ c ∈ R₂, ⁅a, b⁆ * c = c * ⁅a, b⁆ := by
    intro a ha b hb c hc
    have h1 : ⁅a, b⁆ ∈ Subgroup.centralizer (R₂ : Set G) := hcl (Subgroup.commutator_mem_commutator ha hb)
    exact (Subgroup.mem_centralizer_iff.1 h1 c hc).symm
  have hidx := S9.index_commutator_le_of_pRank_le_two hq hq2 hexp hcl' hr
  set N : Subgroup G := Subgroup.normalizer (R : Set G) ⊓ K with hNdef
  have hNK : N ≤ K := inf_le_right
  have hNR₂ : N ≤ Subgroup.normalizer (R₂ : Set G) := fun g hg => hN g hg.1
  obtain ⟨φ, hφ⟩ := S9.exists_hom_action hq hq2 hexp hNR₂ hidx
  apply hnot
  obtain ⟨hmem, -, -, -⟩ := S9.pComponent_basic hp hK
  let π : ↥K →* PSimple p K :=
    (QuotientGroup.mk' (Subgroup.center (PQuot p K))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥K))
  have hπs : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ g : ↥K, π g = 1 ↔ (g : G) ∈ oPPrimeP p K := by
    intro g
    rw [hmem g]
    exact QuotientGroup.eq_one_iff _
  let πN : ↥N →* PSimple p K := π.comp (Subgroup.inclusion hNK)
  have hVoP : V ≤ oPPrimeP p K := hVdef ▸ (commutator_core_le_core p K).trans (core_le_oPPrimeP p K)
  have hVK : V ≤ K := hVdef ▸ commutator_core_le p K
  have hNV : N ≤ Subgroup.normalizer (V : Set G) :=
    hNK.trans (hVdef ▸ Subgroup.normalizer_commutator_ge_left _ _)
  have hπNs : Function.Surjective πN := by
    intro s
    obtain ⟨k, rfl⟩ := hπs s
    have hk : (k : G) ∈ ((V ⊔ N : Subgroup G) : Set G) := hfr k.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left V N hNV] at hk
    obtain ⟨v, hv, n, hn, hvn⟩ := hk
    refine ⟨⟨n, hn⟩, ?_⟩
    have hkvn : k = ⟨v, hVK hv⟩ * ⟨n, hNK hn⟩ := Subtype.ext hvn.symm
    have hπv : π ⟨v, hVK hv⟩ = 1 := (hker _).2 (hVoP hv)
    show π ⟨n, hNK hn⟩ = π k
    rw [hkvn, map_mul, hπv, one_mul]
  haveI : IsSimpleGroup (PSimple p K) := S9.isSimple_pSimple hp hK
  have hY : φ.ker.map πN = ⊥ := by
    haveI hYn : (φ.ker.map πN).Normal := Subgroup.Normal.map inferInstance πN hπNs
    refine eq_bot_of_forall_qpower hp hq hK _ ?_
    rintro s ⟨k, hk, rfl⟩
    have hact := (hφ k).1 (MonoidHom.mem_ker.1 hk)
    obtain ⟨n, hn⟩ := S9.pow_mem_centralizer_of_acts_trivially hq hexp (hNR₂ k.2) hact
    refine ⟨n, ?_⟩
    rw [← map_pow]
    have hmemK : ((k : G)) ^ (q ^ n) ∈ oPPrimeP p K :=
      hcen ⟨⟨Subgroup.pow_mem _ k.2.2 _, Subgroup.pow_mem _ k.2.1 _⟩, hn⟩
    exact (hker _).2 hmemK
  have hle1 : φ.ker ≤ πN.ker := by
    intro k hk
    have h1 : πN k ∈ φ.ker.map πN := Subgroup.mem_map_of_mem πN hk
    rw [hY, Subgroup.mem_bot] at h1
    exact h1
  have hrs : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hle2 : φ.rangeRestrict.ker ≤ πN.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hle1
  refine ⟨φ.range, MonoidHom.liftOfSurjective φ.rangeRestrict hrs ⟨πN, hle2⟩, ?_⟩
  intro s
  obtain ⟨g, hg⟩ := hπNs s
  refine ⟨φ.rangeRestrict g, ?_⟩
  exact (MonoidHom.liftOfRightInverse_comp_apply φ.rangeRestrict (Function.surjInv hrs)
    (Function.rightInverse_surjInv hrs) ⟨πN, hle2⟩ g).trans hg

theorem exists_sylow_normalized {q : ℕ} (hq : q.Prime) {F V : Subgroup G} (hF : IsPGroup q F)
    (hFV : F ≤ Subgroup.normalizer (V : Set G)) :
    ∃ R : Subgroup G, IsPGroup q R ∧ R ≤ V ∧ (∀ Q : Subgroup G, IsPGroup q Q → Q ≤ V → R ≤ Q → Q = R) ∧
      F ≤ Subgroup.normalizer (R : Set G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup G, H = F ⊔ V := ⟨_, rfl⟩
  have hVH : V ≤ H := by rw [hHdef]; exact le_sup_right
  have hFH : F ≤ H := by rw [hHdef]; exact le_sup_left
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := by
    rw [hHdef]; exact sup_le hFV Subgroup.le_normalizer
  obtain ⟨Sy, hSy⟩ := IsPGroup.exists_le_sylow (counterd_isPGroup_subgroupOf (K := H) hF)
  obtain ⟨Qs, hQsdef⟩ : ∃ Qs : Subgroup G, Qs = Sy.toSubgroup.map H.subtype := ⟨_, rfl⟩
  have hQsq : IsPGroup q Qs := by rw [hQsdef]; exact Sy.isPGroup'.map H.subtype
  have hQsH : Qs ≤ H := by rw [hQsdef]; exact Subgroup.map_subtype_le _
  have hFQs : F ≤ Qs := by
    intro f hf
    have hfH : (⟨f, hFH hf⟩ : ↥H) ∈ Sy.toSubgroup := hSy (Subgroup.mem_subgroupOf.2 hf)
    rw [hQsdef]
    exact ⟨_, hfH, rfl⟩
  have hQsN : Qs ≤ Subgroup.normalizer (V : Set G) := hQsH.trans hHN
  have hsup : V ⊔ Qs = H := by
    apply le_antisymm
    · exact sup_le hVH hQsH
    · rw [hHdef]
      exact sup_le (hFQs.trans le_sup_right) le_sup_left
  have hprod := card_sup_mul_card_inf_of_le_normalizer (A := V) (B := Qs) hQsN
  rw [hsup] at hprod
  have hm : ¬ q ∣ Sy.toSubgroup.index := Sy.not_dvd_index
  have hcardH : Nat.card ↥H = Nat.card ↥Qs * Sy.toSubgroup.index := by
    rw [hQsdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective H)]
    exact (Subgroup.card_mul_index (H := Sy.toSubgroup)).symm
  have hVeq : Nat.card ↥V = Sy.toSubgroup.index * Nat.card ↥(V ⊓ Qs) := by
    have hpos : 0 < Nat.card ↥Qs := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc Nat.card ↥Qs * Nat.card ↥V = Nat.card ↥V * Nat.card ↥Qs := mul_comm _ _
      _ = Nat.card ↥H * Nat.card ↥(V ⊓ Qs) := hprod.symm
      _ = Nat.card ↥Qs * (Sy.toSubgroup.index * Nat.card ↥(V ⊓ Qs)) := by rw [hcardH]; ring
  have hRq : IsPGroup q (V ⊓ Qs : Subgroup G) := hQsq.to_le inf_le_right
  refine ⟨V ⊓ Qs, hRq, inf_le_left, ?_, ?_⟩
  · intro Q hQ hQV hRQ
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hQ
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hRq
    have hdvd : Nat.card ↥Q ∣ Nat.card ↥V := Subgroup.card_dvd_of_le hQV
    rw [ha, hVeq, hb] at hdvd
    have hab : a ≤ b := by
      by_contra hlt
      push_neg at hlt
      have h1 : q ^ (b + 1) ∣ Sy.toSubgroup.index * q ^ b := (Nat.pow_dvd_pow q hlt).trans hdvd
      rw [pow_succ'] at h1
      exact hm (Nat.dvd_of_mul_dvd_mul_right (pow_pos hq.pos b) h1)
    refine (Subgroup.eq_of_le_of_card_ge hRQ ?_).symm
    rw [ha, hb]
    exact Nat.pow_le_pow_right hq.pos hab
  · intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have e1 := Subgroup.mem_normalizer_iff.1 (hFV hf) h
    have e2 := Subgroup.mem_normalizer_iff.1
      ((Subgroup.le_normalizer : Qs ≤ Subgroup.normalizer (Qs : Set G)) (hFQs hf)) h
    simp only [Subgroup.mem_inf]
    exact and_congr e1 e2

theorem isPGroup_sup_of_normalizes {q : ℕ} (hq : q.Prime) {F R : Subgroup G} (hF : IsPGroup q F) (hR : IsPGroup q R)
    (hFR : F ≤ Subgroup.normalizer (R : Set G)) : IsPGroup q ↥(F ⊔ R) := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hF
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hR
  have h1 := card_sup_mul_card_inf_of_le_normalizer (A := R) (B := F) hFR
  rw [sup_comm R F, inf_comm R F, mul_comm (Nat.card R)] at h1
  refine IsPGroup.of_card_dvd_pow (n := a + b) ⟨Nat.card ↥(F ⊓ R), ?_⟩
  rw [h1, ha, hb, pow_add]

theorem S_le_core_of_cover {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X K V M S : Subgroup G} (hK : GLAPComponent p X K)
    (hVdef : V = ⁅K, GLAPPrimeCoreOf p K⁆) (hcov : K ≤ V ⊔ (M ⊓ K)) (hS : S ≤ pCoreOf 2 M ⊓ K) (hS2 : IsPGroup 2 S) :
    S ≤ GLAPPrimeCoreOf p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ := isQuasisimple_pQuot_of_glaPComponent hp hK
  haveI : IsSimpleGroup (PSimple p K) := S9.isSimple_pSimple hp hK
  obtain ⟨-, -, hzp, -⟩ := S9.pComponent_basic hp hK
  set π : ↥K →* PQuot p K := QuotientGroup.mk' (GLAPPrimeCore p ↥K) with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ GLAPPrimeCoreOf p K := by
    intro k
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨k, h, rfl⟩
    · rintro ⟨y, hy, hyk⟩
      have : y = k := Subtype.ext hyk
      exact this ▸ hy
  have hVO : V ≤ GLAPPrimeCoreOf p K := by rw [hVdef]; exact commutator_core_le_core p K
  have hVK : V ≤ K := by rw [hVdef]; exact commutator_core_le p K
  have hVn : K ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVdef]; exact Subgroup.normalizer_commutator_ge_left _ _
  have hMK : M ⊓ K ≤ Subgroup.normalizer (V : Set G) := inf_le_right.trans hVn
  obtain ⟨σ, hσdef⟩ : ∃ σ : ↥(M ⊓ K) →* PQuot p K, σ = π.comp (Subgroup.inclusion inf_le_right) :=
    ⟨_, rfl⟩
  have hσ : Function.Surjective σ := by
    intro x
    obtain ⟨k, rfl⟩ := hπs x
    have hk : (k : G) ∈ ((V ⊔ (M ⊓ K) : Subgroup G) : Set G) := hcov k.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left V (M ⊓ K) hMK] at hk
    obtain ⟨v, hv, m, hm, hvm⟩ := Set.mem_mul.1 hk
    have hvK : v ∈ K := hVK hv
    have hπv : π ⟨v, hvK⟩ = 1 := (hker _).2 (hVO hv)
    have hkvm : k = ⟨v, hvK⟩ * ⟨m, hm.2⟩ := Subtype.ext (by simpa using hvm.symm)
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [hσdef]
    show π ⟨m, hm.2⟩ = π k
    rw [hkvm, map_mul, hπv, one_mul]
  have hpcM : pCoreOf 2 M ≤ M := by unfold pCoreOf; exact Subgroup.map_subtype_le _
  have hpc : IsPGroup 2 (pCoreOf 2 M) := by
    unfold pCoreOf
    exact CFSG.pCore_isPGroup.map _
  have hŨp : IsPGroup 2 ((pCoreOf 2 M ⊓ K).subgroupOf (M ⊓ K)) :=
    counterd_isPGroup_subgroupOf hpc.to_inf_left
  have hŨn : ((pCoreOf 2 M ⊓ K).subgroupOf (M ⊓ K)).Normal := by
    constructor
    intro u hu g
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    have hg : (g : G) ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      le_normalizer_pCoreOf 2 M g.2.1
    have h1 := (Subgroup.mem_normalizer_iff.1 hg (u : G)).1 hu.1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨h1, K.mul_mem (K.mul_mem g.2.2 hu.2) (K.inv_mem g.2.2)⟩
  obtain ⟨Ū, hŪdef⟩ : ∃ Ū : Subgroup (PQuot p K), Ū = ((pCoreOf 2 M ⊓ K).subgroupOf (M ⊓ K)).map σ :=
    ⟨_, rfl⟩
  have hŪn : Ū.Normal := by
    rw [hŪdef]
    exact Subgroup.Normal.map hŨn σ hσ
  have hŪ2 : ∀ x ∈ Ū, ∃ n : ℕ, x ^ (2 ^ n) = 1 := by
    intro x hx
    rw [hŪdef] at hx
    obtain ⟨n, hn⟩ := (hŨp.map σ) ⟨x, hx⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hŪtop : Ū ≠ ⊤ := by
    intro htop
    have hy : ∀ s ∈ (⊤ : Subgroup (PSimple p K)), ∃ n : ℕ, s ^ (2 ^ n) = 1 := by
      intro s _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
      have hx : x ∈ Ū := by rw [htop]; exact Subgroup.mem_top x
      obtain ⟨n, hn⟩ := hŪ2 x hx
      refine ⟨n, ?_⟩
      show (QuotientGroup.mk' (Subgroup.center (PQuot p K)) x) ^ (2 ^ n) = 1
      rw [← map_pow, hn, map_one]
    exact top_ne_bot (eq_bot_of_forall_qpower hp Nat.prime_two hK ⊤ hy)
  have hZ : Ū ≤ Subgroup.center (PQuot p K) := le_center_of_normal_of_isQuasisimple hQ hŪn hŪtop
  intro s hs
  have hsK : s ∈ K := (hS hs).2
  have hsM : s ∈ M := hpcM (hS hs).1
  set k : ↥K := ⟨s, hsK⟩ with hkdef
  have hu : (⟨s, hsM, hsK⟩ : ↥(M ⊓ K)) ∈ (pCoreOf 2 M ⊓ K).subgroupOf (M ⊓ K) :=
    Subgroup.mem_subgroupOf.2 (hS hs)
  have hπk : π k ∈ Ū := by
    rw [hŪdef]
    exact ⟨_, hu, by rw [hσdef]; rfl⟩
  have hz : π k ∈ Subgroup.center (PQuot p K) := hZ hπk
  obtain ⟨a, ha⟩ := hzp (π k) hz
  obtain ⟨n, hn⟩ := hS2 ⟨s, hs⟩
  have hsn : s ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hk2 : k ^ (2 ^ n) = 1 := Subtype.ext (by simpa using hsn)
  have h2 : (π k) ^ (2 ^ n) = 1 := by rw [← map_pow, hk2, map_one]
  have hcop : Nat.Coprime (2 ^ n) (p ^ a) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h1 : (π k) ^ (Nat.gcd (2 ^ n) (p ^ a)) = 1 := pow_gcd_eq_one.2 ⟨h2, ha⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  exact (hker k).1 h1

theorem core_le_core {p : ℕ} (hp : p.Prime) {X K : Subgroup G} (hK : GLAPComponent p X K) :
    GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p X := by
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hK.2.1]
  exact inf_le_right

theorem exists_zpowers_sup {p : ℕ} (hp : p.Prime) {D : Subgroup G} {a : G} (hD : Nat.card D = p ^ 2)
    (hexp : ∀ g ∈ D, g ^ p = 1) (haD : a ∈ D) (ha1 : a ≠ 1) :
    ∃ a' ∈ D, D ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers a' := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf a = p := orderOf_eq_prime (hexp a haD) ha1
  have hZD : Subgroup.zpowers a ≤ D := Subgroup.zpowers_le.2 haD
  have hZcard : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hord]
  have hlt : Subgroup.zpowers a < D := by
    refine lt_of_le_of_ne hZD fun h => ?_
    rw [h, hD] at hZcard
    have h1 := Nat.pow_lt_pow_right hp.one_lt (show 1 < 2 by norm_num)
    rw [pow_one] at h1
    omega
  obtain ⟨a', ha'D, ha'Z⟩ := SetLike.exists_of_lt hlt
  refine ⟨a', ha'D, ?_⟩
  have hWD : Subgroup.zpowers a ⊔ Subgroup.zpowers a' ≤ D := sup_le hZD (Subgroup.zpowers_le.2 ha'D)
  have ha'W : a' ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers a' := Subgroup.mem_sup_right (Subgroup.mem_zpowers a')
  have hdvd : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers a') ∣ p ^ 2 := hD ▸ Subgroup.card_dvd_of_le hWD
  obtain ⟨i, hi, hWi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hpd : p ∣ Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers a') :=
    hZcard ▸ Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers a')
  have hi1 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hWi
    rw [hWi] at hpd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpd)
  have hi2 : i ≠ 1 := by
    rintro rfl
    rw [pow_one] at hWi
    have := Subgroup.eq_of_le_of_card_ge
      (le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers a') (le_of_eq (by rw [hWi, hZcard]))
    exact ha'Z (this ▸ ha'W)
  have hi2' : i = 2 := by omega
  subst hi2'
  exact (Subgroup.eq_of_le_of_card_ge hWD (le_of_eq (by rw [hD, hWi]))).ge

theorem exists_maximal_pGroup {q : ℕ} {F W : Subgroup G} (hF : IsPGroup q F) (hFW : F ≤ W) :
    ∃ Fo : Subgroup G, IsPGroup q Fo ∧ Fo ≤ W ∧ F ≤ Fo ∧
      ∀ Q : Subgroup G, IsPGroup q Q → Q ≤ W → Fo ≤ Q → Q = Fo := by
  obtain ⟨Fo, ⟨hFFo, hFoW, hFop⟩, hmax⟩ := Set.exists_max_image
    {P : Subgroup G | F ≤ P ∧ P ≤ W ∧ IsPGroup q P} (fun P : Subgroup G => Nat.card P) (Set.toFinite _)
    ⟨F, le_rfl, hFW, hF⟩
  refine ⟨Fo, hFop, hFoW, hFFo, fun Q hQ hQW hFoQ => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hFoQ (hmax Q ⟨hFFo.trans hFoQ, hQW, hQ⟩)).symm

theorem V_coprime (hctx : ThmACtx G m) (hH : Hyp111 G m p B x L) (hc : CConf G p q B x L M D E F J a S K)
    (h1810 : Input18_10) (h3013 : I3013At G) (hKX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)))
    (hK2 : IsChevSimple 2 (PSimple p K)) (hJK : ¬ K ≤ J ⊔ GLAPPrimeCoreOf p K)
    (hSc : ¬ S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)))
    (hFK : F ≤ Subgroup.normalizer (K : Set G)) (hq : q.Prime) (hq2 : q ≠ 2) :
    Nat.Coprime q (Nat.card (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G)) := by
  have hp : p.Prime := hH.prime
  have hp2 : p ≠ 2 := hH.ne_two
  by_contra hcop
  have hqV : q ∣ Nat.card (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) :=
    by_contra fun h => hcop ((Nat.Prime.coprime_iff_not_dvd hq).2 h)
  set V : Subgroup G := ⁅K, GLAPPrimeCoreOf p K⁆ with hVdef
  have hVK : V ≤ K := commutator_core_le p K
  have hVn : K ≤ Subgroup.normalizer (V : Set G) := Subgroup.normalizer_commutator_ge_left _ _
  have hFq : IsPGroup q F := isPGroup_of_isElemAbelian hc.red.F_elem
  obtain ⟨R, hRq, hRV, hRmax, hFR⟩ := exists_sylow_normalized hq hFq (le_normalizer_commutator_core hFK)
  obtain ⟨R₂, hR₂R, hR₂ne, hNR, hexp, hcl, hcen⟩ :=
    exists_R2 h1810 hp hp2 hq hq2 hKX hc.K_comp hVdef hqV hRq hRV hRmax
  have hfr : K ≤ V ⊔ (Subgroup.normalizer (R : Set G) ⊓ K) := frattini_V hq hVK hVn hRq hRV hRmax
  have hnot : ¬ S9.InvolvedSL2 q (PSimple p K) := by
    intro hinv
    have h60 := h3013 p q (Subgroup.centralizer ({a} : Set G)) K hp hq hq2 hKX hc.K_comp hK2 hinv
    obtain ⟨hDcard, hDle⟩ := (⟨hc.red.card_D, hc.red.D_le.trans hc.red.E_le⟩ :
      Nat.card D = p ^ 2 ∧ D ≤ B)
    obtain ⟨a', ha'D, hDa'⟩ := exists_zpowers_sup hp hDcard (fun g hg => hH.elem.2 g (hDle hg)) hc.a_mem hc.a_ne
    have hJD : GLAPComponent p (Subgroup.centralizer (D : Set G)) J :=
      S9.glaPComponent_centralizer hp hH.comp hc.red.x_mem hc.red.J_comp
    have hCDa' : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({a'} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 ha'D)
    have hJle : J ≤ K ⊓ Subgroup.centralizer ({a'} : Set G) := le_inf hc.J_le (hJD.1.trans hCDa')
    have hle : K ⊓ Subgroup.centralizer ({a'} : Set G) ≤ Subgroup.centralizer (D : Set G) := by
      intro g hg
      have hga : g ∈ Subgroup.centralizer ({a} : Set G) := hc.K_comp.1 hg.1
      have hsup : Subgroup.zpowers a ⊔ Subgroup.zpowers a' ≤ Subgroup.centralizer ({g} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff] at hga ⊢
          exact hga.symm
        · have hga' : g ∈ Subgroup.centralizer ({a'} : Set G) := hg.2
          rw [Subgroup.mem_centralizer_singleton_iff] at hga' ⊢
          exact hga'.symm
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have := hsup (hDa' hd)
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    have hJ' : GLAPComponent p (K ⊓ Subgroup.centralizer ({a'} : Set G)) J :=
      glaPComponent_of_le hp hJD hJle hle
    have hns := not_small_of_proper (a := a') hp hc.K_comp hJ' hJK
    rcases h60 with h | h
    · exact hns.1 h
    · exact hns.2 h
  have h3 : 3 ≤ CFSG.Open.pRank q R₂ := three_le_pRank_R2 hp hq hq2 hc.K_comp hVdef hfr hNR hexp hcl hcen hnot
  have h3R : 3 ≤ CFSG.Open.pRank q R := h3.trans (S9.pRank_mono hq hR₂R)
  have hFRq : IsPGroup q ↥(F ⊔ R) := isPGroup_sup_of_normalizes hq hFq hRq hFR
  have hFM : F ≤ M := hc.red.F_le.trans (inf_le_left.trans hc.red.L_le)
  have hFRM : F ⊔ R ≤ M := S9.le_M_of_chain hq hc.red.closed hFM hc.red.F_rank le_sup_left hFRq
  have hNRM : Subgroup.normalizer (R : Set G) ≤ M := hc.red.closed R hRq (le_sup_right.trans hFRM) h3R
  have hcov : K ≤ V ⊔ (M ⊓ K) := hfr.trans (sup_le_sup_left (inf_le_inf_right K hNRM) V)
  have hS : S ≤ pCoreOf 2 M ⊓ K := le_inf (hc.S_le_T0.trans inf_le_left) hc.S_le_K
  exact hSc ((S_le_core_of_cover hp hp2 hc.K_comp hVdef hcov hS hc.S_two).trans (core_le_core hp hc.K_comp))

private theorem counterd_pRank_le_map {q : ℕ} (hq : q.Prime) {f : G →* G} (hf : Function.Injective f)
    (X : Subgroup G) : CFSG.Open.pRank q X ≤ CFSG.Open.pRank q (X.map f) := by
  obtain ⟨E, hEX, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt X
  have hc' : Nat.card (E.map f) = q ^ CFSG.Open.pRank q X := by
    rw [Subgroup.card_map_of_injective hf, hcard]
  exact CFSG.SectionRank.le_pRank hq.one_lt (Subgroup.map_mono hEX)
    (CFSG.SectionRank.isElemAbelian_map hE f) hc'

open scoped Pointwise in
private theorem counterd_exists_conj_le_sylow {q : ℕ} (hq : q.Prime) (R : Sylow q G) {M : Subgroup G}
    (hRM : (R : Subgroup G) ≤ M) {P : Subgroup G} (hP : IsPGroup q P) (hPM : P ≤ M) :
    ∃ g ∈ M, ∀ x ∈ P, g * x * g⁻¹ ∈ (R : Subgroup G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  let RM : Sylow q M :=
    { toSubgroup := (R : Subgroup G).subgroupOf M
      isPGroup' := counterd_isPGroup_subgroupOf R.isPGroup'
      is_maximal' := by
        intro Q hQ hRQ
        have hQ' : IsPGroup q (Q.map M.subtype) := hQ.map M.subtype
        have hR' : (R : Subgroup G) ≤ Q.map M.subtype := by
          intro x hx
          exact Subgroup.mem_map.2 ⟨⟨x, hRM hx⟩, hRQ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
        have hEq : Q.map M.subtype = R := R.is_maximal' hQ' hR'
        calc Q = (Q.map M.subtype).comap M.subtype :=
              (Subgroup.comap_map_eq_self_of_injective M.subtype_injective Q).symm
          _ = (R : Subgroup G).subgroupOf M := by rw [hEq]; rfl }
  obtain ⟨Q₀, hQ₀⟩ := IsPGroup.exists_le_sylow (counterd_isPGroup_subgroupOf (K := M) hP)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) Q₀ RM
  have hS : MulAut.conj g • (Q₀ : Subgroup ↥M) = (RM : Subgroup ↥M) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  refine ⟨(g : G), g.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hPM hx⟩ : ↥M) ∈ Q₀ := hQ₀ (Subgroup.mem_subgroupOf.2 hx)
  have hmem := Subgroup.smul_mem_pointwise_smul (⟨x, hPM hx⟩ : ↥M) (MulAut.conj g) _ hxQ
  rw [hS] at hmem
  have := Subgroup.mem_subgroupOf.1 hmem
  simpa [MulAut.conj_apply] using this

theorem counterd_weakCore_Fo_le_M_of_sylow {q : ℕ} (hq : q.Prime) {M Q Fo : Subgroup G} (hFoQ : Fo ≤ Q)
    (hΓ : GLAWeakCore q Q ≤ M) {X : Subgroup G} (hXFo : X ≤ Fo) (h2 : 2 ≤ CFSG.Open.pRank q X)
    (h3 : 3 ≤ CFSG.Open.pRank q (X ⊔ (Fo ⊓ Subgroup.centralizer (X : Set G)))) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  have hgen : Subgroup.normalizer (X : Set G) ≤ GLAWeakCore q Q := by
    unfold GLAWeakCore rankThreeAschCore
    refine le_sSup ⟨X, hXFo.trans hFoQ, h2, ?_, rfl⟩
    exact h3.trans (S9.pRank_mono hq (sup_le_sup_left (inf_le_inf_right _ hFoQ) X))
  exact hgen.trans hΓ

theorem weakCore_Fo_le_M (hq : q.Prime) (hH : Hyp111 G m p B x L) (hc : CConf G p q B x L M D E F J a S K)
    {W Fo : Subgroup G}
    (hW : W = F ⊔ K) (hFo : IsPGroup q Fo) (hFoW : Fo ≤ W) (hFoS : ∀ Q : Subgroup G, IsPGroup q Q → Q ≤ W → Fo ≤ Q → Q = Fo)
    (hFFo : F ≤ Fo) :
    ∀ X : Subgroup G, X ≤ Fo → 2 ≤ CFSG.Open.pRank q X →
      3 ≤ CFSG.Open.pRank q (X ⊔ (Fo ⊓ Subgroup.centralizer (X : Set G))) →
      Subgroup.normalizer (X : Set G) ⊓ W ≤ M := by
  intro X hXFo h2 h3
  obtain ⟨R, hRΓ⟩ := hc.red.sylow
  haveI : Fact q.Prime := ⟨hq⟩
  have hFM : F ≤ M := hc.red.F_le.trans (inf_le_left.trans hc.red.L_le)
  have h3R : 3 ≤ CFSG.Open.pRank q (R : Subgroup G) := by
    rw [(CFSG.SectionRank.pRank_sylow R).1]
    exact hc.red.F_rank.trans (S9.pRank_mono hq le_top)
  have hRM : (R : Subgroup G) ≤ M :=
    (Subgroup.le_normalizer (H := (R : Subgroup G))).trans
      ((S9.normalizer_le_weakCore hq (le_refl (R : Subgroup G)) h3R).trans hRΓ)
  have hFoM : Fo ≤ M := S9.le_M_of_chain hq hc.red.closed hFM hc.red.F_rank hFFo hFo
  obtain ⟨g, hgM, hg⟩ := counterd_exists_conj_le_sylow hq R hRM hFo hFoM
  set φ : G →* G := (MulAut.conj g).toMonoidHom with hφdef
  have hφ : ∀ y : G, φ y = g * y * g⁻¹ := fun y => by simp [hφdef, MulAut.conj_apply]
  have hinj : Function.Injective φ := (MulAut.conj g).injective
  have hFo'R : Fo.map φ ≤ (R : Subgroup G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hφ]
    exact hg y hy
  have h2' : 2 ≤ CFSG.Open.pRank q (X.map φ) := h2.trans (counterd_pRank_le_map hq hinj X)
  have h3' : 3 ≤ CFSG.Open.pRank q (X.map φ ⊔ (Fo.map φ ⊓ Subgroup.centralizer ((X.map φ : Subgroup G) : Set G))) := by
    have hle : (X ⊔ (Fo ⊓ Subgroup.centralizer (X : Set G))).map φ ≤
        X.map φ ⊔ (Fo.map φ ⊓ Subgroup.centralizer ((X.map φ : Subgroup G) : Set G)) := by
      rw [Subgroup.map_sup]
      refine sup_le_sup_left (le_inf (Subgroup.map_mono inf_le_left) ?_) _
      rintro _ ⟨c, hcX, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hcX).2 y hy]
    exact h3.trans ((counterd_pRank_le_map hq hinj _).trans (S9.pRank_mono hq hle))
  have hN' : Subgroup.normalizer ((X.map φ : Subgroup G) : Set G) ≤ M :=
    counterd_weakCore_Fo_le_M_of_sylow hq hFo'R hRΓ (Subgroup.map_mono hXFo) h2' h3'
  refine inf_le_left.trans fun n hn => ?_
  have hz : φ n ∈ Subgroup.normalizer ((X.map φ : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ hn)
  have hzM : g * n * g⁻¹ ∈ M := by
    have := hN' hz
    rwa [hφ] at this
  have hn' : n = g⁻¹ * (g * n * g⁻¹) * g := by group
  rw [hn']
  exact M.mul_mem (M.mul_mem (M.inv_mem hgM) hzM) hgM

theorem part2 (h2315 : I2315bAt G) (hH : Hyp111 G m p B x L) (hc : CConf G p q B x L M D E F J a S K)
    (hK2 : IsChevSimple 2 (PSimple p K)) (hFK : F ≤ Subgroup.normalizer (K : Set G))
    (hV : Nat.Coprime q (Nat.card (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G))) (hq : q.Prime) (hq2 : q ≠ 2) :
    S ≤ GLAPPrimeCoreOf p K := by
  have hp : p.Prime := hH.prime
  have hp2 : p ≠ 2 := hH.ne_two
  have hFq : IsPGroup q F := isPGroup_of_isElemAbelian hc.red.F_elem
  have hFCa : F ≤ Subgroup.centralizer ({a} : Set G) :=
    (hc.red.F_le.trans inf_le_right).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hc.a_mem))
  set W : Subgroup G := F ⊔ K with hW
  have hWCa : W ≤ Subgroup.centralizer ({a} : Set G) := sup_le hFCa hc.K_comp.1
  have hKW : GLAPComponent p W K := glaPComponent_of_le hp hc.K_comp le_sup_right hWCa
  have hWK : W ≤ Subgroup.normalizer (K : Set G) := sup_le hFK Subgroup.le_normalizer
  have hWV : W ≤ Subgroup.normalizer ((⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) : Set G) :=
    sup_le (le_normalizer_commutator_core hFK) (Subgroup.normalizer_commutator_ge_left _ _)
  obtain ⟨Fo, hFoq, hFoW, hFFo, hFomax⟩ := exists_maximal_pGroup hFq (le_sup_left : F ≤ W)
  have h3 : 3 ≤ CFSG.Open.pRank q Fo := hc.red.F_rank.trans (S9.pRank_mono hq hFFo)
  have hXM := weakCore_Fo_le_M hq hH hc hW hFoq hFoW hFomax hFFo
  have hcore := h2315 p q hp hp2 hq hq2 hc.red.q_ne W K (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) M Fo hKW hK2 hWK hV
    (commutator_core_le p K) hWV le_rfl hFoq hFoW hFomax h3 hXM
  exact (le_inf (hc.S_le_T0.trans inf_le_left) hc.S_le_K).trans hcore

theorem F_normalizes_K (hH : Hyp111 G m p B x L) (hc : CConf G p q B x L M D E F J a S K) : F ≤ Subgroup.normalizer (K : Set G) := by
  have hp : p.Prime := hH.prime
  have hFCa : F ≤ Subgroup.centralizer ({a} : Set G) :=
    (hc.red.F_le.trans inf_le_right).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hc.a_mem))
  intro f hf
  rw [mem_normalizer_iff_gLBConj_eq]
  have hfa : f * a = a * f := Subgroup.mem_centralizer_singleton_iff.1 (hFCa hf)
  have hfinv : f⁻¹ * a * f = a := by rw [mul_assoc, ← hfa, inv_mul_cancel_left]
  have hCa : GLBConj f (Subgroup.centralizer ({a} : Set G)) = Subgroup.centralizer ({a} : Set G) := by
    ext y
    rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have e1 : f⁻¹ * (f * y * f⁻¹ * a) * f = y * a := by
        rw [show f⁻¹ * (f * y * f⁻¹ * a) * f = y * (f⁻¹ * a * f) by group, hfinv]
      have e2 : f⁻¹ * (a * (f * y * f⁻¹)) * f = a * y := by
        rw [show f⁻¹ * (a * (f * y * f⁻¹)) * f = (f⁻¹ * a * f) * y by group, hfinv]
      calc y * a = f⁻¹ * (f * y * f⁻¹ * a) * f := e1.symm
        _ = f⁻¹ * (a * (f * y * f⁻¹)) * f := by rw [h]
        _ = a * y := e2
    · intro h
      have e3 : f * y * f⁻¹ * a = f * (y * a) * f⁻¹ := by
        calc f * y * f⁻¹ * a = f * y * (f⁻¹ * a * f) * f⁻¹ := by group
          _ = f * (y * a) * f⁻¹ := by rw [hfinv]; group
      rw [e3, h]
      calc f * (a * y) * f⁻¹ = (f * a) * y * f⁻¹ := by group
        _ = (a * f) * y * f⁻¹ := by rw [hfa]
        _ = a * (f * y * f⁻¹) := by group
  have hK' : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) (GLBConj f K) := by
    have h := glaPComponent_gLBConj hc.K_comp f
    rwa [hCa] at h
  have hJK' : J ≤ GLBConj f K := by
    intro j hj
    rw [mem_gLBConj]
    have hfj : f * j * f⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (hc.red.F_norm hf) j).1 hj
    exact hc.J_le hfj
  by_contra hne
  have hle := le_centModSubgroup_of_ne hp hK' hc.K_comp hne
  have hcomm : ∀ j₁ ∈ J, ∀ j₂ ∈ J, ⁅j₁, j₂⁆ ∈ GLAPPrimeCoreOf p K := by
    intro j₁ hj₁ j₂ hj₂
    exact (mem_centModSubgroup.1 (hle (hJK' hj₂))).2 j₁ (hc.J_le hj₁)
  have hJc : ∀ j₁ ∈ J, ∀ j₂ ∈ J, ⁅j₁, j₂⁆ ∈ J := by
    intro j₁ hj₁ j₂ hj₂
    rw [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem hj₁ hj₂) (J.inv_mem hj₁)) (J.inv_mem hj₂)
  have hJcomm : ∀ j₁ ∈ J, ∀ j₂ ∈ J, ⁅j₁, j₂⁆ ∈ GLAPPrimeCoreOf p J := fun j₁ hj₁ j₂ hj₂ =>
    counterd_core_inf_le hp hc.J_le ⟨hcomm j₁ hj₁ j₂ hj₂, hJc j₁ hj₁ j₂ hj₂⟩
  have hgrp : ∀ x y : ↥J, ⁅x, y⁆ ∈ GLAPPrimeCore p ↥J := by
    intro x y
    obtain ⟨z, hz, hzeq⟩ := hJcomm x x.2 y y.2
    have hzx : z = ⁅x, y⁆ := Subtype.ext hzeq
    exact hzx ▸ hz
  have hcommQ : ∀ s t : PQuot p J, s * t = t * s := by
    intro s t
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    rw [show (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ by rw [commutatorElement_def]; group]
    exact hgrp _ _
  obtain ⟨u, v, huv⟩ := S9.pSimple_nonabelian hp hc.red.J_comp
  apply huv
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcommQ u' v']

theorem redC (hctx : ThmACtx G m) (hsf : StageFacts G m) (h183 : Input18_3_4) (h2315 : I2315bAt G) (h3013 : I3013At G)
    (h1810 : Input18_10) (hc2 : Chev2DownAt G p) (h1122 : I1122IsoAt G p) (hH : Hyp111 G m p B x L)
    (hR : RedB G p q B x L M D E F J) (hq : q.Prime) (hq2 : q ≠ 2) : False := by
  obtain ⟨a, S, K, hc⟩ := exists_conf hctx hsf h183 hH hR
  have hp : p.Prime := hH.prime
  have haB : a ∈ B := hR.E_le (hR.D_le hc.a_mem)
  have hS0 : IsS0 p B a K := isS0_of_conf hH hc (a_essential hH hR hc)
  have hJKc : J ≤ closureIn K B := by
    rw [closureIn_eq_self hc.K_normB]
    exact hc.J_le
  have hSc : ¬ S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) :=
    S_not_le_core hsf hH hc.a_ne haB hc.K_comp hc.K_gstar hJKc hc.S_ne hc.S_two hc.S_comm
  obtain ⟨B', x', L', -, hle, hchev⟩ := pump_chev2 hsf hH hc hS0 hSc
  have hK2 : IsChevSimple 2 (PSimple p K) := chev2_of_pumpLe (S3Ctx.of_ctx hctx hH.mu) hc2 h183 h1122 hle hchev
  have hJK : ¬ K ≤ J ⊔ GLAPPrimeCoreOf p K := J_lt_K hH hR hc hSc
  have hFK : F ≤ Subgroup.normalizer (K : Set G) := F_normalizes_K hH hc
  obtain ⟨h3, h4o, h4, h5, -, -, -, -, -⟩ := hsf p hH.mu
  have hc6 : S6Ctx G p := S6Ctx.of_ctx hctx hH.mu h3 h4o h4 h5
  have hKX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) := kGroup_centralizer hc6 hc.a_ne
  have hV := V_coprime hctx hH hc h1810 h3013 hKX hK2 hJK hSc hFK hq hq2
  exact hSc ((part2 h2315 hH hc hK2 hFK hV hq hq2).trans (core_le_core hp hc.K_comp))

end S11

end CFSG.LocalAnalysis.GLTheoremA
