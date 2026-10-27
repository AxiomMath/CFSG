module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Lemma124
public import CFSG.LocalAnalysis.EvenBN.TwoF4.CoprimeProduct

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

abbrev Jc (B : Subgroup G) (x : G) (K : Subgroup G) : Subgroup G :=
  closureIn K (Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G))

theorem J_cent_comm (h : Cfg12 G m p B x L D K) (hin : Inputs124 G p) (hnn : NoNbr12 p B x L D K) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTB : B ≤ Subgroup.normalizer (T : Set G)) :
    Jc B x K ≤ Subgroup.centralizer ((⁅T, Subgroup.zpowers x⁆ : Subgroup G) : Set G) := by
  rw [Jc, closureIn_eq_iSup_gLBConj]
  refine iSup₂_le fun a ha => ?_
  obtain ⟨haB, hax⟩ := Subgroup.mem_inf.1 ha
  have haxz : a ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [S3.centralizer_zpowers x]
    exact hax
  have hainv : a⁻¹ ∈ Subgroup.normalizer (B : Set G) := inv_mem haB
  have hainvz : a⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := inv_mem haxz
  set T' := GLBConj a⁻¹ T with hT'
  have hT'2 : IsPGroup 2 T' := hT2.map _
  have hT'B : B ≤ Subgroup.normalizer (T' : Set G) := by
    intro b hb
    have hb'' : a⁻¹ * b * a⁻¹⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hainv b).1 hb
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [hT', mem_gLBConj, mem_gLBConj]
    have e : (a⁻¹ * b * a⁻¹⁻¹) * (a⁻¹ * z * a⁻¹⁻¹) * (a⁻¹ * b * a⁻¹⁻¹)⁻¹ = a⁻¹ * (b * z * b⁻¹) * a⁻¹⁻¹ := by
      group
    rw [← e]
    exact Subgroup.mem_normalizer_iff.1 (hTB hb'') _
  have h1 := lemma124 h hin hnn hT'2 (fun d hd => hT'B (h.DB hd))
  have hcomm : GLBConj a⁻¹ (⁅T, Subgroup.zpowers x⁆ : Subgroup G) = ⁅T', Subgroup.zpowers x⁆ := by
    have hz : GLBConj a⁻¹ (Subgroup.zpowers x) = Subgroup.zpowers x := gLBConj_eq_of_mem_normalizer hainvz
    calc GLBConj a⁻¹ (⁅T, Subgroup.zpowers x⁆ : Subgroup G)
        = ⁅GLBConj a⁻¹ T, GLBConj a⁻¹ (Subgroup.zpowers x)⁆ := by
          unfold GLBConj
          rw [Subgroup.map_commutator]
      _ = ⁅T', Subgroup.zpowers x⁆ := by rw [hz]
  intro g hg
  rw [mem_gLBConj] at hg
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : a * u * a⁻¹ ∈ (⁅T', Subgroup.zpowers x⁆ : Subgroup G) := by
    rw [← hcomm, mem_gLBConj]
    have e : a⁻¹ * (a * u * a⁻¹) * a⁻¹⁻¹ = u := by group
    rw [e]
    exact hu
  have h2 := Subgroup.mem_centralizer_iff.1 (h1 hu') (a * g * a⁻¹) hg
  have h3 : a * (g * u) * a⁻¹ = a * (u * g) * a⁻¹ := by
    calc a * (g * u) * a⁻¹ = (a * g * a⁻¹) * (a * u * a⁻¹) := by group
      _ = (a * u * a⁻¹) * (a * g * a⁻¹) := h2
      _ = a * (u * g) * a⁻¹ := by group
  have h4 : g * u = u * g := by simpa using h3
  exact h4.symm

theorem pCoreOf_two_facts (N : Subgroup G) :
    IsPGroup 2 (pCoreOf 2 N) ∧ N ≤ Subgroup.normalizer ((pCoreOf 2 N : Subgroup G) : Set G) := by
  refine ⟨?_, ?_⟩
  · rw [CFSG.Open.pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  · have key : ∀ k ∈ N, ∀ r ∈ pCoreOf 2 N, k * r * k⁻¹ ∈ pCoreOf 2 N := by
      intro k hk r hr
      rw [CFSG.Open.pCoreOf] at hr ⊢
      obtain ⟨o', ho', rfl⟩ := hr
      exact ⟨⟨k, hk⟩ * o' * ⟨k, hk⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨key k hk r, fun hr => ?_⟩
    have h1 := key k⁻¹ (N.inv_mem hk) _ hr
    have e : k⁻¹ * (k * r * k⁻¹) * k⁻¹⁻¹ = r := by group
    rwa [e] at h1

theorem x_nontrivial (h : Cfg12 G m p B x L D K) {U : Subgroup G} (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) :
    (⁅pCoreOf 2 (Subgroup.normalizer (U : Set G)), Subgroup.zpowers x⁆ : Subgroup G) ≠ ⊥ := by
  intro hbot
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hloc : IsTwoLocal (Subgroup.normalizer (U : Set G)) := ⟨U, hU1, hU2, rfl⟩
  have hct := h.ctx.toS6.charTwo _ hloc
  have hxc : x ∈ Subgroup.centralizer ((pCoreOf 2 (Subgroup.normalizer (U : Set G)) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 : r ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot hr
    exact (Subgroup.mem_centralizer_iff.1 h1 x (Subgroup.mem_zpowers x)).symm
  have hxP : x ∈ pCoreOf 2 (Subgroup.normalizer (U : Set G)) := hct ⟨hxU, hxc⟩
  have hord : orderOf x = p := orderOf_eq_prime (h.elem.2 x h.xD) h.tri.ne_one
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 (pCoreOf_two_facts (Subgroup.normalizer (U : Set G))).1 ⟨x, hxP⟩
  rw [Subgroup.orderOf_mk, hord] at hk
  have hpd : p ∣ 2 ^ k := by rw [← hk]
  exact h.odd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpd))

theorem exists_T_noncomm (h : Cfg12 G m p B x L D K) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, Subgroup.zpowers x⁆ : Subgroup G) ≠ ⊥ := by
  obtain ⟨-, -, R, -, hR2, hBR, hRB, -⟩ := IsSStarMax.essential h.tri.star
  have hR1 : R ≠ ⊥ := by
    rintro rfl
    exact hRB (Subgroup.commutator_bot_left _)
  obtain ⟨hT2, hNT⟩ := pCoreOf_two_facts (Subgroup.normalizer (R : Set G))
  exact ⟨pCoreOf 2 (Subgroup.normalizer (R : Set G)), hT2, fun b hb => hNT (hBR hb),
    x_nontrivial h hR1 hR2 (hBR h.tri.mem)⟩

theorem Jc_le_L (h : Cfg12 G m p B x L D K) : Jc B x K ≤ L :=
  closureIn_le_of_le_normalizer h.K_le_L (inf_le_right.trans (cx_le_normalizer_L h))

abbrev Sof (B : Subgroup G) (x : G) (K V : Subgroup G) : Subgroup G :=
  ⁅Jc B x K, pCoreOf 2 (Subgroup.normalizer (V : Set G)) ⊓ Subgroup.centralizer ({x} : Set G)⁆

theorem B_le_cx (h : Cfg12 G m p B x L D K) : B ≤ Subgroup.centralizer ({x} : Set G) := fun b hb =>
  Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute h.tri.bmax.1 hb h.tri.mem)

theorem Jc_le_cx (h : Cfg12 G m p B x L D K) : Jc B x K ≤ Subgroup.centralizer ({x} : Set G) :=
  (Jc_le_L h).trans h.tri.comp.1

theorem B_norm_Jc (h : Cfg12 G m p B x L D K) : B ≤ Subgroup.normalizer (Jc B x K : Set G) := fun b hb =>
  mem_normalizer_closureIn (B_norm_K h hb)
    (Subgroup.le_normalizer (Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer hb, B_le_cx h hb⟩))

theorem mem_normalizer_inf_cx {O : Subgroup G} {g : G} (hgO : g ∈ Subgroup.normalizer (O : Set G))
    (hgc : g ∈ Subgroup.centralizer ({x} : Set G)) :
    g ∈ Subgroup.normalizer ((O ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.1 hgO w) (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hgc) w)

theorem jc_residual (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) :
    ∀ N : Subgroup G, N ≤ Jc B x K → (N.subgroupOf (Jc B x K)).Normal →
      Nat.Coprime p (N.subgroupOf (Jc B x K)).index → N = Jc B x K := by
  intro N hNJ hNn hcop
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hJN : Jc B x K ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).1 hNn
  refine le_antisymm hNJ ?_
  rw [Jc, closureIn_eq_iSup_gLBConj]
  refine iSup₂_le fun a ha => ?_
  have hKaJ : GLBConj a K ≤ Jc B x K := by
    rw [Jc, closureIn_eq_iSup_gLBConj]
    exact le_iSup₂ (f := fun a (_ : a ∈ Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) => GLBConj a K) a ha
  have hPP := pPrimePerfect_of_glaPComponent (p := p) (glaPComponent_gLBConj (std_pcomp' h hin) a)
  have hnorm : ((N ⊓ GLBConj a K).subgroupOf (GLBConj a K)).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (hKaJ.trans hJN)
  have hidx : Nat.Coprime ((N ⊓ GLBConj a K).relIndex (GLBConj a K)) p := by
    rw [Subgroup.inf_relIndex_right]
    exact (Nat.Coprime.coprime_dvd_right (relIndex_dvd_of_le_of_normal hKaJ hNn)
      (show Nat.Coprime p (N.relIndex (Jc B x K)) from hcop)).symm
  exact (hPP (N ⊓ GLBConj a K) inf_le_right hnorm hidx ▸ inf_le_left : GLBConj a K ≤ N)

theorem S_ne_bot (h : Cfg12 G m p B x L D K) (hin : Inputs124 G p) (hnn : NoNbr12 p B x L D K) {V : Subgroup G}
    (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hBV : B ≤ Subgroup.normalizer (V : Set G))
    (hJV : Jc B x K ≤ Subgroup.normalizer (V : Set G)) : Sof B x K V ≠ ⊥ := by
  intro hS
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hO2, hNO⟩ := pCoreOf_two_facts (Subgroup.normalizer (V : Set G))
  have hloc : IsTwoLocal (Subgroup.normalizer (V : Set G)) := ⟨V, hV, hV2, rfl⟩
  have hct := h.ctx.toS6.charTwo _ hloc
  have hBO : B ≤ Subgroup.normalizer ((pCoreOf 2 (Subgroup.normalizer (V : Set G)) : Subgroup G) : Set G) :=
    hBV.trans hNO
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := hBV h.tri.mem
  have hzO : Subgroup.zpowers x ≤
      Subgroup.normalizer ((pCoreOf 2 (Subgroup.normalizer (V : Set G)) : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 (hNO hxN)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers x)) (Nat.card (pCoreOf 2 (Subgroup.normalizer (V : Set G)))) := by
    have hord : orderOf x = p := orderOf_eq_prime (h.elem.2 x h.xD) h.tri.ne_one
    rw [Nat.card_zpowers, hord]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hO2
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 h.odd)
  have hsolv : Group.IsSolvable (pCoreOf 2 (Subgroup.normalizer (V : Set G))) := by
    haveI := IsPGroup.isNilpotent hO2
    infer_instance
  have hdec := CFSG.LocalAnalysis.EvenBN.TwoF4.inf_centralizer_sup_commutator_eq hzO hsolv hcop
  have hJc := J_cent_comm h hin hnn hO2 hBO
  have hJ1 : (⁅pCoreOf 2 (Subgroup.normalizer (V : Set G)), Subgroup.zpowers x⁆ : Subgroup G) ≤
      Subgroup.centralizer (Jc B x K : Set G) := Subgroup.le_centralizer_iff.1 hJc
  have hS' : (⁅Jc B x K, pCoreOf 2 (Subgroup.normalizer (V : Set G)) ⊓ Subgroup.centralizer ({x} : Set G)⁆ : Subgroup G) = ⊥ := hS
  have hJ2 : pCoreOf 2 (Subgroup.normalizer (V : Set G)) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer (Jc B x K : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hS'
  have hOJ : pCoreOf 2 (Subgroup.normalizer (V : Set G)) ≤ Subgroup.centralizer (Jc B x K : Set G) := by
    rw [← hdec]
    refine sup_le ?_ hJ1
    rw [← S3.centralizer_zpowers x] at hJ2
    exact hJ2
  have hJO : Jc B x K ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G)) := fun j hj =>
    hct ⟨hJV hj, Subgroup.le_centralizer_iff.1 hOJ hj⟩
  have hK2 : IsPGroup 2 ↥K := hO2.to_le ((le_closureIn_self K _).trans hJO)
  exact not_isPGroup_of_isQuasisimple h.K_qs hK2

theorem S_basic (h : Cfg12 G m p B x L D K) {V : Subgroup G} (hBV : B ≤ Subgroup.normalizer (V : Set G))
    (hJV : Jc B x K ≤ Subgroup.normalizer (V : Set G)) :
    Sof B x K V ≤ L ∧ Sof B x K V ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G)) ∧ IsPGroup 2 (Sof B x K V) ∧
      Jc B x K ⊔ B ≤ Subgroup.normalizer ((Sof B x K V : Subgroup G) : Set G) := by
  obtain ⟨hO2, hNO⟩ := pCoreOf_two_facts (Subgroup.normalizer (V : Set G))
  have hJL : Jc B x K ≤ L := Jc_le_L h
  have hJO : Jc B x K ≤ Subgroup.normalizer ((pCoreOf 2 (Subgroup.normalizer (V : Set G)) : Subgroup G) : Set G) :=
    hJV.trans hNO
  have hBO : B ≤ Subgroup.normalizer ((pCoreOf 2 (Subgroup.normalizer (V : Set G)) : Subgroup G) : Set G) :=
    hBV.trans hNO
  have hSO : Sof B x K V ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G)) := by
    rw [Sof, Subgroup.commutator_le]
    intro j hj c hc
    have hcO : c ∈ pCoreOf 2 (Subgroup.normalizer (V : Set G)) := (Subgroup.mem_inf.1 hc).1
    have h1 : j * c * j⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (V : Set G)) :=
      (Subgroup.mem_normalizer_iff.1 (hJO hj) c).1 hcO
    have e : ⁅j, c⁆ = (j * c * j⁻¹) * c⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact mul_mem h1 (inv_mem hcO)
  refine ⟨?_, hSO, hO2.to_le hSO, ?_⟩
  · rw [Sof, Subgroup.commutator_le]
    intro j hj c hc
    have hcL : c ∈ Subgroup.normalizer (L : Set G) := cx_le_normalizer_L h (Subgroup.mem_inf.1 hc).2
    have h1 : c * j⁻¹ * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hcL j⁻¹).1 (inv_mem (hJL hj))
    have e : ⁅j, c⁆ = j * (c * j⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (hJL hj) h1
  · refine sup_le ?_ ?_
    · exact le_normalizer_commutator Subgroup.le_normalizer
        (fun g hg => mem_normalizer_inf_cx (hJO hg) (Jc_le_cx h hg))
    · exact le_normalizer_commutator (B_norm_Jc h)
        (fun g hg => mem_normalizer_inf_cx (hBO hg) (B_le_cx h hg))

theorem S_perfect (h : Cfg12 G m p B x L D K) (hin : Inputs124 G p) {V : Subgroup G}
    (hBV : B ≤ Subgroup.normalizer (V : Set G)) (hJV : Jc B x K ≤ Subgroup.normalizer (V : Set G)) :
    (⁅Sof B x K V, Jc B x K⁆ : Subgroup G) = Sof B x K V := by
  obtain ⟨hO2, hNO⟩ := pCoreOf_two_facts (Subgroup.normalizer (V : Set G))
  have hp := h.prime
  have hJO : Jc B x K ≤ Subgroup.normalizer ((pCoreOf 2 (Subgroup.normalizer (V : Set G)) : Subgroup G) : Set G) :=
    hJV.trans hNO
  have hcopA : Nat.Coprime p (Nat.card ↥(pCoreOf 2 (Subgroup.normalizer (V : Set G)) ⊓ Subgroup.centralizer ({x} : Set G))) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (hO2.to_le (inf_le_left : _ ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G))))
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 h.odd)
  have hI := i321UsedAt_holds (G := G) p hp
    (pCoreOf 2 (Subgroup.normalizer (V : Set G)) ⊓ Subgroup.centralizer ({x} : Set G)) (Jc B x K) hcopA
    (fun g hg => mem_normalizer_inf_cx (hJO hg) (Jc_le_cx h hg)) (jc_residual h hin.l122.l121.common)
  show (⁅(⁅Jc B x K, pCoreOf 2 (Subgroup.normalizer (V : Set G)) ⊓ Subgroup.centralizer ({x} : Set G)⁆ : Subgroup G),
    Jc B x K⁆ : Subgroup G) = ⁅Jc B x K, pCoreOf 2 (Subgroup.normalizer (V : Set G)) ⊓ Subgroup.centralizer ({x} : Set G)⁆
  rw [Subgroup.commutator_comm (Jc B x K)]
  exact hI

theorem exists_S_of_N (h : Cfg12 G m p B x L D K) (hin : Inputs124 G p) (hnn : NoNbr12 p B x L D K) {V : Subgroup G}
    (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hBV : B ≤ Subgroup.normalizer (V : Set G))
    (hJV : Jc B x K ≤ Subgroup.normalizer (V : Set G)) :
    ∃ S : Subgroup G, S ≤ L ∧ S ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G)) ∧ IsPGroup 2 S ∧ S ≠ ⊥ ∧
      Jc B x K ⊔ B ≤ Subgroup.normalizer (S : Set G) ∧ (⁅S, Jc B x K⁆ : Subgroup G) = S := by
  obtain ⟨h1, h2, h3, h4⟩ := S_basic h hBV hJV
  exact ⟨Sof B x K V, h1, h2, h3, S_ne_bot h hin hnn hV hV2 hBV hJV, h4, S_perfect h hin hBV hJV⟩

theorem L_centralizes_core (h : Cfg12 G m p B x L D K) :
    L ≤ Subgroup.centralizer ((GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) : Subgroup G) : Set G) := by
  have hp := h.prime
  have hY := comm_le_primeCore hp h.tri.comp
  have hOL : (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G) = ⊥ :=
    S9.commutator_eq_bot_of_isQuasisimple hp h.tri.comp (h.tri.qs h.ctx)
  have h1 : (⁅(⁅L, GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))⁆ : Subgroup G), L⁆ : Subgroup G) = ⊥ := by
    refine le_bot_iff.1 ((Subgroup.commutator_mono hY le_rfl).trans ?_)
    rw [Subgroup.commutator_comm]
    exact hOL.le
  have h2 := CFSG.LocalCores.perfect_double_commutator
    (Subgroup.isPerfect_iff.2 (glaPComponent_perfect h.tri.comp)) h1
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2

theorem S_le_center (h : Cfg12 G m p B x L D K) {N S : Subgroup G} (hLN : L ≤ N) (hSL : S ≤ L)
    (hSN : S ≤ pCoreOf 2 N) : S ≤ Subgroup.centralizer (L : Set G) := by
  have hq := h.tri.qs h.ctx
  obtain ⟨hO2, hON⟩ := pCoreOf_two_facts N
  have hLW : L ≤ Subgroup.normalizer ((L ⊓ pCoreOf 2 N : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hl) w)
      (Subgroup.mem_normalizer_iff.1 (hON (hLN hl)) w)
  have hWn : ((L ⊓ pCoreOf 2 N).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hLW
  have hW2 : IsPGroup 2 ↥((L ⊓ pCoreOf 2 N).subgroupOf L) :=
    (hO2.to_le (inf_le_right : L ⊓ pCoreOf 2 N ≤ pCoreOf 2 N)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ pCoreOf 2 N ≤ L)).symm
  have hle : (L ⊓ pCoreOf 2 N).subgroupOf L ≤ CFSG.pCore 2 ↥L := le_sSup ⟨hWn, hW2⟩
  have hcen := CFSG.HardMathSupport.Solomon.LocalBalance.pCore_le_center_of_isQuasisimple Nat.prime_two hq
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hs' : (⟨s, hSL hs⟩ : ↥L) ∈ (L ⊓ pCoreOf 2 N).subgroupOf L :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hSL hs, hSN hs⟩)
  have h1 := Subgroup.mem_center_iff.1 (hcen (hle hs')) ⟨l, hl⟩
  exact congrArg Subtype.val h1

theorem exists_invariant_sylow_core (h : Cfg12 G m p B x L D K)
    (hev : ¬ Odd (Nat.card ↥(GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))))) :
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) ∧
      B ≤ Subgroup.normalizer (U : Set G) := by
  have hp := h.prime
  have hBpg : IsPGroup p B := isPGroup_of_isElemAbelian h.tri.bmax.1
  have hBO : B ≤ Subgroup.normalizer (GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) : Set G) :=
    (B_le_cx h).trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_glaPPrimeCoreOf p _))
  obtain ⟨S, ⟨hSO, hS2, hSmax⟩, -, hBS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp Nat.prime_two
    hBpg (not_dvd_card_glaPPrimeCoreOf hp _) hBO (bot_le : (⊥ : Subgroup G) ≤ _) (IsPGroup.of_card (n := 0) (by simp))
    Subgroup.le_normalizer_of_normal
  refine ⟨S, ?_, hS2, hSO, hBS⟩
  rintro rfl
  have h2 : 2 ∣ Nat.card ↥(GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))) := by
    by_contra hnd
    exact hev (Nat.odd_iff.2 (by omega))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))) 2 h2
  have hgO : (g : G) ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := g.2
  have hord : orderOf (g : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
  have hP2 : IsPGroup 2 (Subgroup.zpowers (g : G)) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have := hSmax (Subgroup.zpowers (g : G)) (Subgroup.zpowers_le.2 hgO) hP2 bot_le
  have hg1 : (g : G) = 1 := by
    have h1 : (g : G) ∈ Subgroup.zpowers (g : G) := Subgroup.mem_zpowers _
    rw [this] at h1
    exact h1
  rw [hg1, orderOf_one] at hord
  omega

theorem normalizer_commutator {A C : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hC : g ∈ Subgroup.normalizer (C : Set G)) : g ∈ Subgroup.normalizer ((⁅A, C⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hA hC ⊢
  unfold GLBConj at hA hC ⊢
  rw [Subgroup.map_commutator, hA, hC]

theorem comm_le_left {A C : Subgroup G} (hC : C ≤ Subgroup.normalizer (A : Set G)) : (⁅A, C⁆ : Subgroup G) ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha c hc
  rw [commutatorElement_def]
  have h1 : c * a⁻¹ * c⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hC hc) a⁻¹).1 (Subgroup.inv_mem _ ha)
  simpa [mul_assoc] using Subgroup.mul_mem _ ha h1

theorem lemma125_i (h : Cfg12 G m p B x L D K) (hin : Inputs124 G p) (hnn : NoNbr12 p B x L D K) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 2 S ∧ Jc B x K ⊔ B ≤ Subgroup.normalizer (S : Set G) ∧
      (⁅Jc B x K, S⁆ : Subgroup G) ≠ ⊥ := by
  obtain ⟨T, hT2, hTB, hTx⟩ := exists_T_noncomm h
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.zpowers_le.2 (hTB h.tri.mem)
  have hV2 : IsPGroup 2 (⁅T, Subgroup.zpowers x⁆ : Subgroup G) := hT2.to_le (comm_le_left hxN)
  have hBx : ∀ b ∈ B, b ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := fun b hb => by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [S3.centralizer_zpowers x]
    exact Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute h.tri.bmax.1 hb h.tri.mem)
  have hBV : B ≤ Subgroup.normalizer ((⁅T, Subgroup.zpowers x⁆ : Subgroup G) : Set G) := fun b hb =>
    normalizer_commutator (hTB hb) (hBx b hb)
  have hJV : Jc B x K ≤ Subgroup.normalizer ((⁅T, Subgroup.zpowers x⁆ : Subgroup G) : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _ (J_cent_comm h hin hnn hT2 hTB hg)
  obtain ⟨S, hSL, -, hS2, hS1, hSN, hSJ⟩ := exists_S_of_N h hin hnn hTx hV2 hBV hJV
  refine ⟨S, hSL, hS2, hSN, fun hbot => hS1 ?_⟩
  rw [← hSJ, Subgroup.commutator_comm]
  exact hbot

theorem lemma125_ii (h : Cfg12 G m p B x L D K) (hin : Inputs124 G p) (hnn : NoNbr12 p B x L D K) :
    Odd (Nat.card ↥(GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))) := by
  by_contra hev
  obtain ⟨U, hU1, hU2, hUO, hBU⟩ := exists_invariant_sylow_core h hev
  have hLcs : L ≤ Subgroup.centralizer (U : Set G) :=
    (L_centralizes_core h).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hUO))
  have hLU : L ≤ Subgroup.normalizer (U : Set G) := fun l hl => Subgroup.centralizer_le_normalizer _ (hLcs hl)
  have hJU : Jc B x K ≤ Subgroup.normalizer (U : Set G) := (Jc_le_L h).trans hLU
  obtain ⟨S, hSL, hSN, hS2, hS1, hSN', hSJ⟩ := exists_S_of_N h hin hnn hU1 hU2 hBU hJU
  have hSc := S_le_center h hLU hSL hSN
  have hcomm : (⁅S, Jc B x K⁆ : Subgroup G) = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2
      (hSc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (Jc_le_L h))))
  exact hS1 (by rw [← hSJ]; exact hcomm)

end S12

end CFSG.LocalAnalysis.GLTheoremA
