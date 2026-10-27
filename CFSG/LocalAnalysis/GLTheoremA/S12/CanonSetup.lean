module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Count
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.GLTheoremA.S12.Common

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Vocabulary

variable {Γ : Type} [Group Γ]

@[expose] def InnerOn (J : Subgroup Γ) (b : Γ) : Prop :=
  ∃ a ∈ J, ∀ j ∈ J, b * j * b⁻¹ = a * j * a⁻¹

@[expose] def MarkedInnDiag (L : Subgroup Γ) (y : Γ) (lab : GLALabel) : Prop :=
  GLAMarking L (fun lab' _ _ I _ θ => lab' = lab ∧
    ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Γ) = y⁻¹ * l * y) φ)

end Vocabulary

section Rank

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_sup_zpowers_of_card {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) {z : G} (hzp : z ^ p = 1)
    (hzE : z ∉ E) (hz : ∀ e ∈ E, e * z = z * e) :
    IsElemAbelian p (E ⊔ Subgroup.zpowers z) ∧
      Nat.card (E ⊔ Subgroup.zpowers z : Subgroup G) = p ^ (k + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hz1 : z ≠ 1 := fun h => hzE (h ▸ E.one_mem)
  have hcardz : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1]
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (E : Set G) (Subgroup.mem_centralizer_iff.mpr hz)
  have hdisj : Disjoint E (Subgroup.zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro g hgE hgz
    have : Fact (Nat.card (Subgroup.zpowers z)).Prime := ⟨by rw [hcardz]; exact hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (E.subgroupOf (Subgroup.zpowers z)) with h | h
    · have hg : (⟨g, hgz⟩ : Subgroup.zpowers z) ∈ E.subgroupOf (Subgroup.zpowers z) := hgE
      rw [h] at hg
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hg)
    · exfalso
      have hf : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈
          E.subgroupOf (Subgroup.zpowers z) := by
        rw [h]
        trivial
      exact hzE hf
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hE (CFSG.Open.isElemAbelian_zpowers hzp) ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (hz a ha) n).eq
  · rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E _ hnorm hdisj, hk,
      hcardz, pow_succ]

theorem card_mul_le_of_normalizes {p : ℕ} (hp : p.Prime) {x : G} {L E U : Subgroup G} (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) (hEL : E ≤ L) (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hUL : U ≤ L) (hE : IsElemAbelian p E)
    (hEU : E ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card E * p ≤ p ^ GLATwoLocalRank p G * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hxL hl)
  have hpos : 0 < Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  by_cases hxE : x ∈ E
  · have h1 : Nat.card E ≤ p ^ GLATwoLocalRank p G := GL83.PiGen.card_le_pow_twoLocalRank hE hU2 hU hEU
    have h2 : p ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) := by
      have hle : Subgroup.zpowers x ≤ E ⊓ Subgroup.centralizer (L : Set G) :=
        Subgroup.zpowers_le.2 ⟨hxE, hxC⟩
      have := Subgroup.card_le_of_le hle
      rwa [Nat.card_zpowers, orderOf_eq_prime hxp hx1] at this
    exact Nat.mul_le_mul h1 h2
  · obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
    have hcomm : ∀ e ∈ E, e * x = x * e := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.1 (hxL (hEL he))
    obtain ⟨hab, hcard⟩ := isElemAbelian_sup_zpowers_of_card hp hE hk hxp hxE hcomm
    have hxU : x ∈ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact Subgroup.mem_centralizer_singleton_iff.mp (hxL (hUL hu))
    have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ hxU
    have h1 := GL83.PiGen.card_le_pow_twoLocalRank hab hU2 hU (sup_le hEU hxN)
    rw [hcard] at h1
    calc Nat.card E * p = p ^ (k + 1) := by rw [hk, pow_succ]
      _ ≤ p ^ GLATwoLocalRank p G := h1
      _ = p ^ GLATwoLocalRank p G * 1 := (mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hpos

end Rank

section Config

variable {G : Type} [Group G] [Finite G]

structure CanonCfg (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (L D K : Subgroup G) (y : G) (J : Subgroup G) : Prop where
  star : IsSStarMax p B x L
  split : SplitInnerDiagMarking p B L
  std : GLAStdSub p B x L D K
  shat : GLASHat p B y J
  nb : GLANeighbor p x y J D K
  KJ : K ≤ J
  BNJ : B ≤ Subgroup.normalizer (J : Set G)
  rank : 4 ≤ GLATwoLocalRank p G

namespace CanonCfg

variable {p : ℕ} {B : Subgroup G} {x y : G} {L D K J : Subgroup G}

theorem bmax (h : CanonCfg G p B x L D K y J) : GLAIsBmax p B := IsSStarMax.bmax h.star

theorem elem (h : CanonCfg G p B x L D K y J) : IsElemAbelian p B := h.bmax.1

theorem card_B (h : CanonCfg G p B x L D K y J) : Nat.card B = p ^ GLATwoLocalRank p G := h.bmax.2.1

theorem xB (h : CanonCfg G p B x L D K y J) : x ∈ B := (IsSStarMax.essential h.star).1

theorem x_ne_one (h : CanonCfg G p B x L D K y J) : x ≠ 1 := (IsSStarMax.essential h.star).2.1

theorem yB (h : CanonCfg G p B x L D K y J) : y ∈ B := h.shat.2.1

theorem y_ne_one (h : CanonCfg G p B x L D K y J) : y ≠ 1 := h.shat.2.2.1

theorem J_le_cy (h : CanonCfg G p B x L D K y J) : J ≤ Subgroup.centralizer ({y} : Set G) :=
  h.shat.2.2.2.1

theorem L_le_cx (h : CanonCfg G p B x L D K y J) : L ≤ Subgroup.centralizer ({x} : Set G) :=
  (IsSStarMax.component h.star).1

theorem BNL (h : CanonCfg G p B x L D K y J) : B ≤ Subgroup.normalizer (L : Set G) :=
  IsSStarMax.normalizes h.star

theorem pre (h : CanonCfg G p B x L D K y J) : GLAStdSubPre p B x L D K := h.std.1

theorem DB (h : CanonCfg G p B x L D K y J) : D ≤ B := h.pre.1

theorem card_D (h : CanonCfg G p B x L D K y J) : Nat.card D = p ^ 2 := h.pre.2.2.1

theorem K_eq (h : CanonCfg G p B x L D K y J) :
    K = GLALayer (L ⊓ Subgroup.centralizer (D : Set G)) := h.pre.2.2.2.2.1

theorem K_comp (h : CanonCfg G p B x L D K y J) :
    IsComponentOf K (L ⊓ Subgroup.centralizer (D : Set G)) := h.pre.2.2.2.2.2.1

theorem D_eq (h : CanonCfg G p B x L D K y J) : D = B ⊓ Subgroup.centralizer (K : Set G) :=
  h.pre.2.2.2.2.2.2

theorem D_closure (h : CanonCfg G p B x L D K y J) : D = Subgroup.closure {x, y} := h.nb.1

theorem K_le_L (h : CanonCfg G p B x L D K y J) : K ≤ L := h.K_comp.1.trans inf_le_left

theorem y_notMem_zpowers_x (hp : p.Prime) (h : CanonCfg G p B x L D K y J) :
    y ∉ Subgroup.zpowers x := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hy
  have hle : D ≤ Subgroup.zpowers x := by
    rw [h.D_closure, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact Subgroup.mem_zpowers _
    · exact hy
  have hcard := Subgroup.card_le_of_le hle
  rw [h.card_D, Nat.card_zpowers, orderOf_eq_prime (h.elem.2 x h.xB) h.x_ne_one] at hcard
  have := hp.two_le
  nlinarith

theorem x_notMem_zpowers_y (hp : p.Prime) (h : CanonCfg G p B x L D K y J) :
    x ∉ Subgroup.zpowers y := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hx
  have hle : D ≤ Subgroup.zpowers y := by
    rw [h.D_closure, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hx
    · exact Subgroup.mem_zpowers _
  have hcard := Subgroup.card_le_of_le hle
  rw [h.card_D, Nat.card_zpowers, orderOf_eq_prime (h.elem.2 y h.yB) h.y_ne_one] at hcard
  have := hp.two_le
  nlinarith

theorem card_zpowers_y (hp : p.Prime) (h : CanonCfg G p B x L D K y J) :
    Nat.card (Subgroup.zpowers y) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_zpowers, orderOf_eq_prime (h.elem.2 y h.yB) h.y_ne_one]

theorem card_zpowers_x (hp : p.Prime) (h : CanonCfg G p B x L D K y J) :
    Nat.card (Subgroup.zpowers x) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_zpowers, orderOf_eq_prime (h.elem.2 x h.xB) h.x_ne_one]

theorem x_pow (h : CanonCfg G p B x L D K y J) : x ^ p = 1 := h.elem.2 x h.xB

theorem y_pow (h : CanonCfg G p B x L D K y J) : y ^ p = 1 := h.elem.2 y h.yB

theorem inf_centralizer_J (h : CanonCfg G p B x L D K y J) :
    B ⊓ Subgroup.centralizer (J : Set G) = Subgroup.zpowers y := by
  ext b
  constructor
  · rintro ⟨hbB, hbc⟩
    refine (h.shat.2.2.2.2.2 b).1 ⟨hbB, h.BNJ hbB, ?_⟩
    have h1 : (⁅J, Subgroup.zpowers b⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      have h2 : j * b = b * j := Subgroup.mem_centralizer_iff.mp hbc j hj
      exact (Commute.zpow_left (show Commute b j from h2.symm) n).eq
    rw [h1]
    exact bot_le
  · intro hb
    have hbB : b ∈ B := (Subgroup.zpowers_le.2 h.yB) hb
    refine ⟨hbB, ?_⟩
    show b ∈ Subgroup.centralizer (J : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hjy : j * y = y * j := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cy hj)
    exact (Commute.zpow_left (show Commute y j from hjy.symm) n).eq.symm

theorem card_inf_centralizer_J (hp : p.Prime) (h : CanonCfg G p B x L D K y J) :
    Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set G)) = p := by
  rw [h.inf_centralizer_J, h.card_zpowers_y hp]

theorem x_notMem_centralizer_J (hp : p.Prime) (h : CanonCfg G p B x L D K y J) :
    x ∉ Subgroup.centralizer (J : Set G) := by
  intro hx
  have : x ∈ B ⊓ Subgroup.centralizer (J : Set G) := ⟨h.xB, hx⟩
  rw [h.inf_centralizer_J] at this
  exact h.x_notMem_zpowers_y hp this

theorem mem_centralizer_of_le_centralizer {a : G} {M : Subgroup G}
    (hM : M ≤ Subgroup.centralizer ({a} : Set G)) : a ∈ Subgroup.centralizer (M : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hM hm)

theorem card_le_of_isCyclic_exp {S : Subgroup G} (hp : 0 < p) (hc : IsCyclic S)
    (he : ∀ y ∈ S, y ^ p = 1) : Nat.card S ≤ p := by
  obtain ⟨e, he'⟩ := hc.exists_generator
  rw [← orderOf_eq_card_of_forall_mem_zpowers he']
  exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using he _ e.2)))

theorem inf_centralizer_L (hp : p.Prime) (h : CanonCfg G p B x L D K y J) :
    B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := mem_centralizer_of_le_centralizer h.L_le_cx
  have hle : Subgroup.zpowers x ≤ B ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.2 ⟨h.xB, hxC⟩
  have hE : IsElemAbelian p (B ⊓ Subgroup.centralizer (L : Set G)) :=
    CFSG.Open.IsElemAbelian.mono h.elem inf_le_left
  have hcyc : IsCyclic ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
    refine (IsSStarMax.cycMod h.star) _ ?_ (CFSG.Open.IsElemAbelian.isPGroup hE)
    intro g hg
    refine ⟨Subgroup.centralizer_le_normalizer (L : Set G) hg.2, ?_⟩
    have h1 : (⁅L, Subgroup.zpowers g⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      have h2 : l * g = g * l := (Subgroup.mem_centralizer_iff.mp hg.2 l hl)
      exact (Commute.zpow_left (show Commute g l from h2.symm) n).eq
    rw [h1]
    exact bot_le
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [h.card_zpowers_x hp]
  exact card_le_of_isCyclic_exp hp.pos hcyc hE.2

theorem card_inf_centralizer_L (hp : p.Prime) (h : CanonCfg G p B x L D K y J) :
    Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = p := by
  rw [h.inf_centralizer_L hp, h.card_zpowers_x hp]

theorem y_notMem_centralizer_L (hp : p.Prime) (h : CanonCfg G p B x L D K y J) :
    y ∉ Subgroup.centralizer (L : Set G) := by
  intro hy
  have : y ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨h.yB, hy⟩
  rw [h.inf_centralizer_L hp] at this
  exact h.y_notMem_zpowers_x hp this

theorem centralizer_D (h : CanonCfg G p B x L D K y J) :
    Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
  rw [h.D_closure, Subgroup.centralizer_closure]
  ext g
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]

theorem L_inf_centralizer_D (h : CanonCfg G p B x L D K y J) :
    L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
  rw [h.centralizer_D, ← inf_assoc, inf_eq_left.2 h.L_le_cx]

theorem isComponent_K_J (h : CanonCfg G p B x L D K y J) :
    IsComponentOf K (J ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hKc := h.K_comp
  rw [h.L_inf_centralizer_D] at hKc
  have hLsub : IsSubnormal L (Subgroup.centralizer ({x} : Set G)) :=
    (IsSStarMax.component h.star).2.1
  have h1 : IsSubnormal (L ⊓ Subgroup.centralizer ({y} : Set G))
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) :=
    hLsub.inf _
  have h2 : IsSubnormal K (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) :=
    hKc.2.1.trans h1
  have hK1 : K ≤ J ⊓ Subgroup.centralizer ({x} : Set G) :=
    le_inf h.KJ (h.K_le_L.trans h.L_le_cx)
  have hK2 : J ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) :=
    fun g hg => ⟨hg.2, h.J_le_cy hg.1⟩
  have h3 := h2.inf (J ⊓ Subgroup.centralizer ({x} : Set G))
  rw [inf_eq_left.2 hK1, inf_eq_right.2 hK2] at h3
  exact ⟨hK1, h3, hKc.2.2⟩

theorem B_le_normalizer_K (h : CanonCfg G p B x L D K y J) :
    B ≤ Subgroup.normalizer (K : Set G) := by
  have hbcs : ∀ b ∈ B, b ∈ Subgroup.centralizer (D : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (CFSG.Open.IsElemAbelian.comm h.elem (h.DB hd) hb)
  have hBX : B ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
    intro b hb
    refine S12.mem_normalizer_inf' (h.BNL hb) ?_
    have hbD : b ∈ Subgroup.normalizer (D : Set G) := Subgroup.centralizer_le_normalizer _ (hbcs b hb)
    rw [mem_normalizer_iff_gLBConj_eq] at hbD ⊢
    rw [gLBConj_centralizer, hbD]
  intro b hb
  rw [h.K_eq]
  exact S12.mem_normalizer_glaLayer' (hBX hb)

end CanonCfg

theorem inf_centralizer_eq_bot_of_center {E J : Subgroup G} (hEJ : E ≤ J) (hZ : Subgroup.center ↥J = ⊥) :
    E ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hgJ : g ∈ J := hEJ hg.1
  have hc : (⟨g, hgJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hg.2 j j.2)
  rw [hZ] at hc
  have := Subgroup.mem_bot.mp hc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

end Config

section Marking

variable {Γ : Type} [Group Γ]

theorem isQuasisimple_of_marking {L : Subgroup Γ} {P : GLAMarkProp ↥L} (h : GLAMarking L P) :
    CFSG.Open.IsQuasisimple ↥L := by
  obtain ⟨hperf, lab, -, R, _, I, F, θ, hs, -, -⟩ := CFSG.StandardType.Canonical.largeEvenMarking_exists h
  exact ⟨hperf, θ.isSimpleGroup⟩

theorem split_label {p : ℕ} {B L : Subgroup Γ} (h : SplitInnerDiagMarking p B L) :
    ∃ labL : GLALabel, GLAInLambda2 labL ∧ GLASplit p labL ∧ B ≤ Subgroup.normalizer (L : Set Γ) ∧
      ∀ b ∈ B, MarkedInnDiag L b labL := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, hs, hna, θ, hsp, hBN, hind⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  refine ⟨lab, hlab, hsp, hBN, fun b hb => ⟨hperf, lab, hlab, ?_⟩⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R' _ I' F' ⟨hs', hna', θ', hsp', hBN', hind'⟩
  exact ⟨hs', hna', θ', rfl, hind' b hb⟩

theorem labelOf_of_markedInnDiag {L : Subgroup Γ} {y : Γ} {lab : GLALabel}
    (h : MarkedInnDiag L y lab) : GLAMarking L (fun lab' _ _ _ _ _ => lab' = lab) :=
  CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) h

end Marking

end CFSG.LocalAnalysis.GLTheoremA
