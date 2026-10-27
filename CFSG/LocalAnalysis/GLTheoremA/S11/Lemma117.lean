module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma116
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs117
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.GLTheoremA.Prop51Core
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Concl117 (G : Type) [Group G] [Finite G] (p p' : ℕ) (B' : Subgroup G) (x' x : G) (J L' : Subgroup G) : Prop where
  comp' : GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) L'
  J_le : J ≤ L'
  uniq : ∀ Y : Subgroup G, GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) Y → J ≤ Y → Y = L'
  triple : IsSTriple p' B' x' L'
  x_norm : x ∈ Subgroup.normalizer (L' : Set G)
  J_layer : GLAPLayer p (L' ⊓ Subgroup.centralizer ({x} : Set G)) = J ∧
    GLAPComponent p (L' ⊓ Subgroup.centralizer ({x} : Set G)) J
  comp_p : GLAPComponent p (Subgroup.centralizer ({x'} : Set G)) L'

namespace S11

variable {G : Type} [Group G] [Finite G] {m p p' : ℕ} {B B' : Subgroup G} {x x' : G} {L J : Subgroup G}

private theorem lemma117_le_of_comm {H J N : Subgroup G} (hJH : J ≤ H)
    (hq : CFSG.Open.IsQuasisimple ↥J) (hN : ∀ j ∈ J, ∀ l ∈ H, ⁅l, j⁆ ∈ N) : J ≤ N := by
  have key : commutator ↥J ≤ N.subgroupOf J := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [Subgroup.mem_subgroupOf]
    have := hN (b : G) b.2 (a : G) (hJH a.2)
    simpa [commutatorElement_def] using this
  rw [hq.1] at key
  intro j hj
  exact Subgroup.mem_subgroupOf.1 (key (Subgroup.mem_top (⟨j, hj⟩ : ↥J)))

private theorem lemma117_eq_one_of_mem_center {H : Type} [Group H] [Finite H] {u : H}
    (hu : u ∈ Subgroup.center H) (hodd : Odd (Nat.card (Subgroup.center H))) (h2 : u ^ 2 = 1) :
    u = 1 := by
  have hle : Subgroup.zpowers u ≤ Subgroup.center H := Subgroup.zpowers_le.2 hu
  have h3 : orderOf u ∣ Nat.card (Subgroup.center H) := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have h4 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hodd' : Odd (orderOf u) := hodd.of_dvd_nat h3
  rcases (Nat.dvd_prime Nat.prime_two).1 h4 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ hodd') (by decide)

private def lemma117_conjHomS {G : Type} [Group G] (S : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    S →* S where
  toFun s := ⟨g * s * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg s).1 s.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp [mul_assoc])

private theorem lemma117_conjHomS_apply {G : Type} [Group G] (S : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (S : Set G)) (s : S) :
    ((lemma117_conjHomS S g hg s : S) : G) = g * s * g⁻¹ := rfl

private theorem lemma117_conjHomS_injective {G : Type} [Group G] (S : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    Function.Injective (lemma117_conjHomS S g hg) := by
  intro s t h
  apply Subtype.ext
  have := congrArg Subtype.val h
  rw [lemma117_conjHomS_apply, lemma117_conjHomS_apply] at this
  simpa using this

private theorem lemma117_conjHomS_mul {G : Type} [Group G] (S : Subgroup G) (g h : G) (hg : g ∈ Subgroup.normalizer (S : Set G))
    (hh : h ∈ Subgroup.normalizer (S : Set G)) (hgh : g * h ∈ Subgroup.normalizer (S : Set G)) (s : S) :
    lemma117_conjHomS S (g * h) hgh s = lemma117_conjHomS S g hg (lemma117_conjHomS S h hh s) := by
  apply Subtype.ext
  simp [lemma117_conjHomS_apply, mul_assoc]

private theorem lemma117_not_Q8_action {G : Type} [Group G] [Finite G] {m : ℕ} (hm : 4 ≤ m)
    {B S : Subgroup G} {z : G} (hBN : B ≤ Subgroup.normalizer (S : Set G))
    (hzB : ∀ b ∈ B, (∀ s ∈ S, b * s * b⁻¹ = s) → b ∈ Subgroup.zpowers z)
    (hzc : Nat.card (Subgroup.zpowers z) = 3) (hBc : Nat.card B = 3 ^ m)
    (e : S ≃* QuaternionGroup 2) : False := by
  classical
  haveI : Fintype B := Fintype.ofFinite B
  set i₀ : S := e.symm (QuaternionGroup.a 1) with hi₀def
  set j₀ : S := e.symm (QuaternionGroup.xa 0) with hj₀def
  have hi₀ : e i₀ = QuaternionGroup.a 1 := e.apply_symm_apply _
  have hj₀ : e j₀ = QuaternionGroup.xa 0 := e.apply_symm_apply _
  have hgen : ∀ s : S, ∃ k l : ℕ, s = i₀ ^ k * j₀ ^ l := by
    intro s
    obtain ⟨k, l, hkl⟩ : ∃ k l : Fin 4, e s = (QuaternionGroup.a 1) ^ (k : ℕ) * (QuaternionGroup.xa 0) ^ (l : ℕ) := by
      have hdec : ∀ x : QuaternionGroup 2, ∃ k : Fin 4, ∃ l : Fin 4,
          x = (QuaternionGroup.a 1) ^ (k : ℕ) * (QuaternionGroup.xa 0) ^ (l : ℕ) := by decide
      obtain ⟨k, l, h⟩ := hdec (e s)
      exact ⟨k, l, h⟩
    refine ⟨k, l, ?_⟩
    apply e.injective
    rw [map_mul, map_pow, map_pow, hi₀, hj₀, hkl]
  have hconj_fix : ∀ g (hg : g ∈ Subgroup.normalizer (S : Set G)), lemma117_conjHomS S g hg i₀ = i₀ →
      lemma117_conjHomS S g hg j₀ = j₀ → ∀ s ∈ S, g * s * g⁻¹ = s := by
    intro g hg h1 h2 s hs
    obtain ⟨k, l, hkl⟩ := hgen ⟨s, hs⟩
    have : lemma117_conjHomS S g hg ⟨s, hs⟩ = ⟨s, hs⟩ := by
      rw [hkl, map_mul, map_pow (lemma117_conjHomS S g hg) i₀ k,
        map_pow (lemma117_conjHomS S g hg) j₀ l, h1, h2]
    have h' := congrArg Subtype.val this
    rw [lemma117_conjHomS_apply] at h'
    simpa using h'
  let P : Finset (QuaternionGroup 2 × QuaternionGroup 2) := Finset.univ.filter (fun p =>
    p.1 ^ 2 ≠ 1 ∧ p.2 ^ 2 ≠ 1 ∧ p.1 * p.2 ≠ p.2 * p.1)
  have hP : P.card ≤ 24 := by
    have : P.card = (Finset.univ.filter (fun p : QuaternionGroup 2 × QuaternionGroup 2 =>
        p.1 ^ 2 ≠ 1 ∧ p.2 ^ 2 ≠ 1 ∧ p.1 * p.2 ≠ p.2 * p.1)).card := rfl
    rw [this]
    decide
  let F : B → QuaternionGroup 2 × QuaternionGroup 2 := fun b =>
    (e (lemma117_conjHomS S b (hBN b.2) i₀), e (lemma117_conjHomS S b (hBN b.2) j₀))
  have hF : ∀ b : B, F b ∈ P := by
    intro b
    set c := lemma117_conjHomS S (b : G) (hBN b.2) with hc
    have hsq : ∀ s : S, (e (c s)) ^ 2 = e (c (s ^ 2)) := by
      intro s; rw [map_pow, map_pow]
    have hsq' : ∀ s : S, s ^ 2 ≠ 1 → (e (c s)) ^ 2 ≠ 1 := by
      intro s hs h
      rw [hsq] at h
      have h2 : c (s ^ 2) = 1 := e.map_eq_one_iff.1 h
      apply hs
      apply (lemma117_conjHomS_injective S _ _)
      rw [h2, map_one]
    have hi2 : i₀ ^ 2 ≠ 1 := by
      intro h
      have := congrArg e h
      rw [map_pow, hi₀, map_one] at this
      exact (show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 by decide) this
    have hj2 : j₀ ^ 2 ≠ 1 := by
      intro h
      have := congrArg e h
      rw [map_pow, hj₀, map_one] at this
      exact (show (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 by decide) this
    have hcomm : e (c i₀) * e (c j₀) ≠ e (c j₀) * e (c i₀) := by
      intro h
      have h2 : c (i₀ * j₀) = c (j₀ * i₀) := by
        apply e.injective
        have e1 : e (c (i₀ * j₀)) = e (c i₀) * e (c j₀) := by rw [map_mul c, map_mul e]
        have e2 : e (c (j₀ * i₀)) = e (c j₀) * e (c i₀) := by rw [map_mul c, map_mul e]
        rw [e1, e2]
        exact h
      have h3 := lemma117_conjHomS_injective S _ _ h2
      have h4 := congrArg e h3
      rw [map_mul, map_mul, hi₀, hj₀] at h4
      exact (show (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠ QuaternionGroup.xa 0 * QuaternionGroup.a 1 by decide) h4
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, F]
    exact ⟨hsq' i₀ hi2, hsq' j₀ hj2, hcomm⟩
  have hT0 : ((Set.toFinite (Subgroup.zpowers z : Set G)).toFinset).card = 3 := by
    rw [← Nat.card_eq_card_finite_toFinset]
    exact hzc
  have hfib : ∀ y ∈ Finset.univ.image F, (Finset.univ.filter (fun b : B => F b = y)).card ≤ 3 := by
    intro y hy
    obtain ⟨b₀, -, hb₀⟩ := Finset.mem_image.1 hy
    have hmem : ∀ b : B, F b = F b₀ → (b₀ : G)⁻¹ * (b : G) ∈ Subgroup.zpowers z := by
      intro b hb
      have h1 : lemma117_conjHomS S (b : G) (hBN b.2) i₀ = lemma117_conjHomS S (b₀ : G) (hBN b₀.2) i₀ :=
        e.injective (congrArg Prod.fst hb)
      have h2 : lemma117_conjHomS S (b : G) (hBN b.2) j₀ = lemma117_conjHomS S (b₀ : G) (hBN b₀.2) j₀ :=
        e.injective (congrArg Prod.snd hb)
      have hgb : (b₀ : G)⁻¹ * (b : G) ∈ Subgroup.normalizer (S : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (hBN b₀.2)) (hBN b.2)
      have hc1 : (b : G) * (i₀ : G) * (b : G)⁻¹ = (b₀ : G) * (i₀ : G) * (b₀ : G)⁻¹ := by
        have := congrArg Subtype.val h1
        simpa [lemma117_conjHomS_apply] using this
      have hc2 : (b : G) * (j₀ : G) * (b : G)⁻¹ = (b₀ : G) * (j₀ : G) * (b₀ : G)⁻¹ := by
        have := congrArg Subtype.val h2
        simpa [lemma117_conjHomS_apply] using this
      have hi : lemma117_conjHomS S ((b₀ : G)⁻¹ * (b : G)) hgb i₀ = i₀ := by
        apply Subtype.ext
        rw [lemma117_conjHomS_apply]
        calc ((b₀ : G)⁻¹ * (b : G)) * (i₀ : G) * ((b₀ : G)⁻¹ * (b : G))⁻¹
            = (b₀ : G)⁻¹ * ((b : G) * (i₀ : G) * (b : G)⁻¹) * (b₀ : G) := by group
          _ = (b₀ : G)⁻¹ * ((b₀ : G) * (i₀ : G) * (b₀ : G)⁻¹) * (b₀ : G) := by rw [hc1]
          _ = (i₀ : G) := by group
      have hj : lemma117_conjHomS S ((b₀ : G)⁻¹ * (b : G)) hgb j₀ = j₀ := by
        apply Subtype.ext
        rw [lemma117_conjHomS_apply]
        calc ((b₀ : G)⁻¹ * (b : G)) * (j₀ : G) * ((b₀ : G)⁻¹ * (b : G))⁻¹
            = (b₀ : G)⁻¹ * ((b : G) * (j₀ : G) * (b : G)⁻¹) * (b₀ : G) := by group
          _ = (b₀ : G)⁻¹ * ((b₀ : G) * (j₀ : G) * (b₀ : G)⁻¹) * (b₀ : G) := by rw [hc2]
          _ = (j₀ : G) := by group
      have hfix := hconj_fix _ hgb hi hj
      exact hzB _ (B.mul_mem (B.inv_mem b₀.2) b.2) hfix
    have hle : (Finset.univ.filter (fun b : B => F b = y)).card ≤
        (Set.toFinite (Subgroup.zpowers z : Set G)).toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun b : B => (b₀ : G)⁻¹ * (b : G))
      · intro b hb
        have hb' : F b = y := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
        show (b₀ : G)⁻¹ * (b : G) ∈ (Set.toFinite (Subgroup.zpowers z : Set G)).toFinset
        rw [Set.Finite.mem_toFinset]
        exact hmem b (hb'.trans hb₀.symm)
      · intro b _ b' _ h
        exact Subtype.ext (mul_left_cancel h)
    rw [hT0] at hle
    exact hle
  have hcard := Finset.card_le_mul_card_image (Finset.univ : Finset B) 3 hfib
  have himg : (Finset.univ.image F).card ≤ 24 := by
    refine le_trans (Finset.card_le_card ?_) hP
    intro y hy
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hy
    exact hF b
  have hBcard' : (Finset.univ : Finset B).card = 3 ^ m := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hBc]
  have h81 : 3 ^ 4 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  norm_num at h81
  omega


theorem bstar_facts (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J) :
    GLAIsBmax p' B' ∧ IsEssential p' B' x' := by
  classical
  haveI : Fact p'.Prime := ⟨hc.cfg.prime⟩
  have hm4 : 4 ≤ m := hctx.1.four_le
  have hBc : Nat.card B' = p' ^ m := by rw [← hc.e_eq]; exact hc.cfg.rank_B
  have hord : orderOf x' = p' := orderOf_eq_prime (hc.cfg.elem.2 x' hc.cfg.mem) hc.cfg.ne_one
  obtain ⟨S, hSJ, hS2, hBN, hBS⟩ := hc.cfg.eight
  have hJC : J ≤ Subgroup.centralizer ({x'} : Set G) := fun j hj => (hc.cfg.comp.1.1 hj).2
  have hSC : S ≤ Subgroup.centralizer ({x'} : Set G) := hSJ.trans hJC
  have hBz : ¬ B' ≤ Subgroup.zpowers x' := by
    intro h
    have h1 := Subgroup.card_le_of_le h
    rw [Nat.card_zpowers, hord, hBc] at h1
    have h2 : p' ^ 2 ≤ p' ^ m := Nat.pow_le_pow_right hc.cfg.prime.pos (by omega)
    have h3 : p' < p' ^ 2 := by
      have := hc.cfg.prime.two_le
      nlinarith
    omega
  have hS_ne : S ≠ ⊥ := by
    intro hS
    apply hBz
    have hBC : B' ≤ Subgroup.centralizer (S : Set G) := by
      intro b _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe, hS, Subgroup.mem_bot] at hh
      simp [hh]
    rw [← hBS]
    exact le_inf le_rfl hBC
  have hcomm_ne : (⁅S, B'⁆ : Subgroup G) ≠ ⊥ := by
    intro hbot
    apply hBz
    have hbot' : (⁅B', S⁆ : Subgroup G) = ⊥ := by rw [Subgroup.commutator_comm]; exact hbot
    have hBC : B' ≤ Subgroup.centralizer (S : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot'
    rw [← hBS]
    exact le_inf le_rfl hBC
  have hBmax : GLAIsBmax p' B' := by
    show CFSG.Open.IsElemAbelian p' B' ∧ Nat.card B' = p' ^ GLATwoLocalRank p' G ∧
      ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B' ≤ Subgroup.normalizer (U : Set G)
    refine ⟨hc.cfg.elem, ?_, S, hS_ne, hS2, hBN⟩
    rw [hc.mu.2.1, ← hc.e_eq]
    exact hc.cfg.rank_B
  refine ⟨hBmax, ?_⟩
  unfold IsEssential
  refine ⟨hc.cfg.mem, hc.cfg.ne_one, S, hSC, hS2, hBN, hcomm_ne, ?_⟩
  intro h3
  refine ⟨fun e => ?_⟩
  refine lemma117_not_Q8_action (z := x') hm4 hBN ?_ ?_ ?_ e
  · intro b hb hcent
    have hcen : b ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have := hcent s hs
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have hmem : b ∈ B' ⊓ Subgroup.centralizer (S : Set G) := ⟨hb, hcen⟩
    rw [hBS] at hmem
    exact hmem
  · rw [Nat.card_zpowers, hord, h3]
  · rw [hBc, h3]

theorem twoLocalRank_quot_le {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (X : Subgroup G) :
    GLATwoLocalRank r (PQuot r X) ≤ GLATwoLocalRank r ↥X := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hN : ¬ r ∣ Nat.card (GLAPPrimeCore r ↥X) :=
    (Nat.Prime.coprime_iff_not_dvd hr).1 CFSG.pPrimeCore_coprime_card
  exact glaTwoLocalRank_quotient_le hr hr2 (GLAPPrimeCore r ↥X) hN

private theorem lemma117_isMulCommutative_map {H K : Type} [Group H] [Group K] {A : Subgroup H}
    (hA : IsMulCommutative A) (f : H →* K) : IsMulCommutative (A.map f) :=
  ⟨⟨by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    have h : a * b = b * a := congrArg Subtype.val (hA.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, h]⟩⟩

private theorem lemma117_comm_mem {r : ℕ} {C : Subgroup G} {j : G} (hj : j ∈ C) (c : ↥C)
    (h : Commute (QuotientGroup.mk' (GLAPPrimeCore r ↥C) (⟨j, hj⟩ : ↥C))
      (QuotientGroup.mk' (GLAPPrimeCore r ↥C) c)) :
    ⁅j, (c : G)⁆ ∈ GLAPPrimeCoreOf r C := by
  have hK : (⁅(⟨j, hj⟩ : ↥C), c⁆ : ↥C) ∈ GLAPPrimeCore r ↥C := by
    have hmap : (QuotientGroup.mk' (GLAPPrimeCore r ↥C) ⁅(⟨j, hj⟩ : ↥C), c⁆ : PQuot r C) = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h
    exact (QuotientGroup.eq_one_iff _).1 hmap
  exact Subgroup.mem_map.2 ⟨_, hK, rfl⟩

theorem exists_faithful_two_group (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J) {r : ℕ} (hr : r = p ∨ r = p')
    (hrp : r.Prime) (hr2 : r ≠ 2)
    (hnc : ¬ (⁅J, oPPrimeP r (Subgroup.centralizer ({x'} : Set G))⁆ : Subgroup G) ≤
      GLAPPrimeCoreOf r (Subgroup.centralizer ({x'} : Set G))) :
    ∃ U R : Subgroup (PQuot r (Subgroup.centralizer ({x'} : Set G))),
      IsElemAbelian 2 U ∧ Nat.card U = 2 ^ (m + 2) ∧ IsPGroup r R ∧
        U ≤ Subgroup.normalizer (R : Set (PQuot r (Subgroup.centralizer ({x'} : Set G)))) ∧
        ∀ u ∈ U, R ≤ Subgroup.centralizer ({u} : Set (PQuot r (Subgroup.centralizer ({x'} : Set G)))) → u = 1 := by
  haveI : Fact r.Prime := ⟨hrp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJC : J ≤ Subgroup.centralizer ({x'} : Set G) := fun j hj => (hc.cfg.comp.1.1 hj).2
  have hJq : CFSG.Open.IsQuasisimple ↥J := hc.cfg.comp.1.2.2
  let φ : ↥J →* PQuot r (Subgroup.centralizer ({x'} : Set G)) :=
    (QuotientGroup.mk' (GLAPPrimeCore r ↥(Subgroup.centralizer ({x'} : Set G)))).comp
      (Subgroup.inclusion hJC)
  have hJ2 : m + 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥J) := by
    have h := hc.cfg.m2
    rw [hc.e_eq] at h
    exact h
  obtain ⟨E, -, hE2, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) (⊤ : Subgroup ↥J)
  obtain ⟨U₀, -, hU₀2, hU₀card⟩ := exists_le_isElemAbelian_card hE2 (n := m + 2)
    (by rw [hEcard]; exact pow_dvd_pow 2 hJ2)
  let R : Subgroup (PQuot r (Subgroup.centralizer ({x'} : Set G))) := CFSG.pCore r _
  have hRp : IsPGroup r R := CFSG.pCore_isPGroup
  have hRn : R.Normal := CFSG.pCore_normal
  let M : Subgroup ↥J := (Subgroup.centralizer (R : Set (PQuot r (Subgroup.centralizer ({x'} : Set G))))).comap φ
  have hMn : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    change φ n ∈ Subgroup.centralizer (R : Set _) at hn
    change φ (g * n * g⁻¹) ∈ Subgroup.centralizer (R : Set _)
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro h hh
    have hk : (φ g)⁻¹ * h * φ g ∈ R := by
      have := hRn.conj_mem h hh (φ g)⁻¹
      simpa [mul_assoc] using this
    have hcomm := hn _ hk
    rw [map_mul, map_mul, map_inv]
    calc h * (φ g * φ n * (φ g)⁻¹) = φ g * ((φ g)⁻¹ * h * φ g * φ n) * (φ g)⁻¹ := by group
      _ = φ g * (φ n * ((φ g)⁻¹ * h * φ g)) * (φ g)⁻¹ := by rw [hcomm]
      _ = φ g * φ n * (φ g)⁻¹ * h := by group
  have hMtop : M ≠ ⊤ := by
    intro hMt
    apply hnc
    refine Subgroup.commutator_le.2 fun j hj o ho => ?_
    unfold oPPrimeP at ho
    obtain ⟨c, hc1, rfl⟩ := Subgroup.mem_map.1 ho
    have hcR : (QuotientGroup.mk' (GLAPPrimeCore r ↥(Subgroup.centralizer ({x'} : Set G))) c :
        PQuot r (Subgroup.centralizer ({x'} : Set G))) ∈ R := hc1
    have hjM : φ ⟨j, hj⟩ ∈ Subgroup.centralizer (R : Set (PQuot r (Subgroup.centralizer ({x'} : Set G)))) := by
      have : (⟨j, hj⟩ : ↥J) ∈ M := hMt ▸ Subgroup.mem_top _
      exact this
    have hcomm := (Subgroup.mem_centralizer_iff.1 hjM) _ hcR
    exact lemma117_comm_mem (hJC hj) c hcomm.symm
  haveI := hMn
  have hMc : M ≤ Subgroup.center ↥J := le_center_of_normal_of_isQuasisimple hJq hMn hMtop
  have hkey : ∀ u₀ ∈ U₀, φ u₀ ∈ Subgroup.centralizer (R : Set (PQuot r (Subgroup.centralizer ({x'} : Set G)))) →
      u₀ = 1 := fun u₀ hu₀ hcen =>
    lemma117_eq_one_of_mem_center (hMc hcen) hc.cfg.odd_center (hU₀2.2 u₀ hu₀)
  have hinj : Function.Injective (φ.comp U₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : φ (a : ↥J) = 1 := ha
    have : (a : ↥J) = 1 := hkey (a : ↥J) a.2 (by rw [ha']; exact Subgroup.one_mem _)
    exact Subtype.ext this
  refine ⟨U₀.map φ, R, ⟨lemma117_isMulCommutative_map hU₀2.1 φ, ?_⟩, ?_, hRp, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, hU₀2.2 u hu, map_one]
  · have hrange : (φ.comp U₀.subtype).range = U₀.map φ := by
      ext q
      simp [MonoidHom.mem_range, Subgroup.mem_map]
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hU₀card]
  · intro u _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => hRn.conj_mem h hh u, fun hh => by simpa [mul_assoc] using hRn.conj_mem _ hh u⁻¹⟩
  · rintro _ ⟨u₀, hu₀, rfl⟩ hcent
    have hcen : φ u₀ ∈ Subgroup.centralizer (R : Set (PQuot r (Subgroup.centralizer ({x'} : Set G)))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := hcent hh
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    rw [hkey u₀ hu₀ hcen, map_one]

theorem jbar_cent_R (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J) {r : ℕ} (hr : r = p ∨ r = p')
    (hrp : r.Prime) (hr2 : r ≠ 2) (hrank : GLATwoLocalRank r G = m) :
    (⁅J, oPPrimeP r (Subgroup.centralizer ({x'} : Set G))⁆ : Subgroup G) ≤
      GLAPPrimeCoreOf r (Subgroup.centralizer ({x'} : Set G)) := by
  by_contra hnc
  obtain ⟨U, R, hU2, hUcard, hRr, hUN, hfaith⟩ := exists_faithful_two_group hctx hc hr hrp hr2 hnc
  obtain ⟨u, hu, hu1, Q₁, -, hQel, hQcard, hQu, -⟩ :=
    P55.dihedralUsed (PQuot r (Subgroup.centralizer ({x'} : Set G))) r hrp hr2 R U (m + 1) hRr hU2 hUcard hUN hfaith
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf u = 2 := orderOf_eq_prime (hU2.2 u hu) hu1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
  have hM : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers u : Set (PQuot r (Subgroup.centralizer ({x'} : Set G))))) :=
    ⟨Subgroup.zpowers u, fun h => hu1 (by simpa using (Subgroup.zpowers_eq_bot.1 h)), hu2, rfl⟩
  have hQM : Q₁ ≤ Subgroup.normalizer (Subgroup.zpowers u : Set (PQuot r (Subgroup.centralizer ({x'} : Set G)))) := by
    intro q hq
    refine Subgroup.centralizer_le_normalizer _ ?_
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hQu hq)) k).symm
  have h1 := elemAbelian_le_of_twoLocal hrp hM hQM hQel
  rw [hQcard] at h1
  have h2 : m + 1 ≤ GLATwoLocalRank r (PQuot r (Subgroup.centralizer ({x'} : Set G))) :=
    (Nat.pow_le_pow_iff_right hrp.one_lt).1 h1
  have h3 := twoLocalRank_quot_le hrp hr2 (Subgroup.centralizer ({x'} : Set G))
  have h4 := twoLocalRank_le_top hrp (Subgroup.centralizer ({x'} : Set G))
  omega

@[instance_reducible] private def lemma117Act {G : Type} [Group G] (E : Subgroup G) : MulAction ↥E (Subgroup G) where
  smul e Y := GLBConj (e : G)⁻¹ Y
  one_smul Y := by
    show GLBConj (((1 : ↥E) : G))⁻¹ Y = Y
    simp [gLBConj_one]
  mul_smul e f Y := by
    show GLBConj ((e * f : ↥E) : G)⁻¹ Y = GLBConj ((e : G)⁻¹) (GLBConj ((f : G)⁻¹) Y)
    rw [gLBConj_gLBConj, Subgroup.coe_mul, mul_inv_rev]

private theorem lemma117_card_le {G : Type} [Group G] [Finite G] :
    ∀ (n : ℕ) (Ω : Finset (Subgroup G)), Ω.card = n → Ω.Nonempty →
      ∀ E : Subgroup G, IsElemAbelian 2 E → (∀ Y ∈ Ω, ∀ g ∈ E, GLBConj g Y ∈ Ω) →
      ∀ k : ℕ, Nat.card E = 2 ^ k →
      (∀ e ∈ E, (∀ Y ∈ Ω, GLBConj e Y = Y) → e = 1) → k + 1 ≤ n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Ω hΩn hΩne E hE hcl k hEk hfaith
  obtain ⟨Y₀, hY₀⟩ := hΩne
  letI := lemma117Act E
  have hcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := fun e he f hf =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨f, hf⟩)
  set T : Set (Subgroup G) := MulAction.orbit E Y₀ with hT
  set O : Finset (Subgroup G) := Ω.filter (fun Y => Y ∈ T) with hO
  set Ω' : Finset (Subgroup G) := Ω.filter (fun Y => Y ∉ T) with hΩ'
  have hTΩ : ∀ Y ∈ T, Y ∈ Ω := by
    intro Y hY
    obtain ⟨e, rfl⟩ := MulAction.mem_orbit_iff.1 hY
    exact hcl Y₀ hY₀ (e : G)⁻¹ (E.inv_mem e.2)
  have hOT : (T : Set (Subgroup G)) = ↑O := by
    ext Y
    simp only [hO, Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨fun hY => ⟨hTΩ Y hY, hY⟩, fun hY => hY.2⟩
  have hOcard : Nat.card T = O.card := by
    rw [Nat.card_coe_set_eq, hOT, Set.ncard_coe_finset]
  have hsplit : O.card + Ω'.card = n := by
    rw [← hΩn]
    exact Finset.card_filter_add_card_filter_not _
  have hY₀O : Y₀ ∈ O := Finset.mem_filter.2 ⟨hY₀, MulAction.mem_orbit_self Y₀⟩
  have hOpos : 1 ≤ O.card := Finset.card_pos.2 ⟨Y₀, hY₀O⟩
  set S : Subgroup ↥E := MulAction.stabilizer E Y₀ with hS
  clear_value S
  have hidx : S.index = O.card := by
    rw [hS, MulAction.index_stabilizer, ← hOcard, Nat.card_coe_set_eq]
  have hmul : O.card * Nat.card S = 2 ^ k := by
    rw [← hidx, Subgroup.index_mul_card, hEk]
  obtain ⟨a, ha, hOa⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hmul)
  have hS' : Nat.card S = 2 ^ (k - a) := by
    have h2 : (2 : ℕ) ^ k = 2 ^ a * 2 ^ (k - a) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hOa, h2] at hmul
    exact Nat.eq_of_mul_eq_mul_left (pow_pos Nat.two_pos a) hmul
  set S' : Subgroup G := S.map E.subtype with hS'def
  clear_value S'
  have hS'card : Nat.card S' = 2 ^ (k - a) := by
    rw [hS'def, Subgroup.card_map_of_injective E.subtype_injective, hS']
  have hS'E : S' ≤ E := by
    rw [hS'def]
    exact Subgroup.map_subtype_le S
  have hS'E2 : IsElemAbelian 2 S' := isElemAbelian_mono hE hS'E
  have hSfix : ∀ s ∈ S', GLBConj s Y₀ = Y₀ := by
    intro s hs
    rw [hS'def] at hs
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 hs
    rw [hS] at ht
    have ht1 : t • Y₀ = Y₀ := MulAction.mem_stabilizer_iff.1 ht
    have ht1' : GLBConj (t : G)⁻¹ Y₀ = Y₀ := ht1
    have hts' : (t : G) = s := hts
    rw [← hts']
    calc GLBConj (t : G) Y₀ = GLBConj (t : G) (GLBConj (t : G)⁻¹ Y₀) := by rw [ht1']
      _ = GLBConj ((t : G)⁻¹ * (t : G)) Y₀ := gLBConj_gLBConj _ _ _
      _ = Y₀ := by rw [inv_mul_cancel, gLBConj_one]
  have hfix : ∀ s ∈ S', (∀ Y ∈ Ω', GLBConj s Y = Y) → ∀ Y ∈ Ω, GLBConj s Y = Y := by
    intro s hs hΩ'' Y hY
    by_cases hYT : Y ∈ T
    · obtain ⟨e, rfl⟩ := MulAction.mem_orbit_iff.1 hYT
      show GLBConj s (GLBConj (e : G)⁻¹ Y₀) = GLBConj (e : G)⁻¹ Y₀
      rw [gLBConj_gLBConj, hcomm _ (E.inv_mem e.2) _ (hS'E hs), ← gLBConj_gLBConj, hSfix s hs]
    · exact hΩ'' Y (Finset.mem_filter.2 ⟨hY, hYT⟩)
  have hfaithS : ∀ s ∈ S', (∀ Y ∈ Ω', GLBConj s Y = Y) → s = 1 := fun s hs hΩ'' =>
    hfaith s (hS'E hs) (hfix s hs hΩ'')
  by_cases hne' : Ω'.Nonempty
  · have hcl' : ∀ Y ∈ Ω', ∀ g ∈ S', GLBConj g Y ∈ Ω' := by
      intro Y hY g hg
      obtain ⟨hYΩ, hYT⟩ := Finset.mem_filter.1 hY
      refine Finset.mem_filter.2 ⟨hcl Y hYΩ g (hS'E hg), fun hGT => hYT ?_⟩
      obtain ⟨f, hf⟩ := MulAction.mem_orbit_iff.1 hGT
      have hgE : g ∈ E := hS'E hg
      refine MulAction.mem_orbit_iff.2 ⟨⟨g, hgE⟩ * f, ?_⟩
      rw [mul_smul, hf]
      show GLBConj g⁻¹ (GLBConj g Y) = Y
      rw [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]
    have hk := ih Ω'.card (by omega) Ω' rfl hne' S' hS'E2 hcl' (k - a) hS'card hfaithS
    have hlt := Nat.lt_two_pow_self (n := a)
    omega
  · have hΩ'0 : Ω'.card = 0 := Finset.card_eq_zero.2 (Finset.not_nonempty_iff_eq_empty.1 hne')
    have hS1 : S' = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro s hs
      exact hfaithS s hs (fun Y hY => absurd hY (by simp [Finset.card_eq_zero.1 hΩ'0]))
    have hcard1 : Nat.card S' = 1 := by rw [hS1, Subgroup.card_bot]
    rw [hS'card] at hcard1
    have hka : k - a = 0 := by
      rcases Nat.pow_eq_one.1 hcard1 with h | h
      · exact absurd h (by norm_num)
      · exact h
    have hak : a = k := by omega
    rw [hak] at hOa
    have hlt := Nat.lt_two_pow_self (n := k)
    omega

private theorem lemma117_exists_two_rank {H : Type} [Group H] [Finite H] {n : ℕ}
    (hH : n ≤ CFSG.Open.pRank 2 (⊤ : Subgroup H)) : ∃ U : Subgroup H, IsElemAbelian 2 U ∧
      Nat.card U = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, -, hE2, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) (⊤ : Subgroup H)
  obtain ⟨U, -, hU2, hUcard⟩ := exists_le_isElemAbelian_card hE2 (n := n)
    (by rw [hEcard]; exact pow_dvd_pow 2 hH)
  exact ⟨U, hU2, hUcard⟩

theorem exists_many_components (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J) {r : ℕ} (hr : r = p ∨ r = p')
    (hrp : r.Prime) (hr2 : r ≠ 2)
    (hN : ¬ ∀ Y : Subgroup G, GLAPComponent r (Subgroup.centralizer ({x'} : Set G)) Y → J ≤ Subgroup.normalizer (Y : Set G)) :
    ∃ 𝒮 : Finset (Subgroup G), (∀ Y ∈ 𝒮, GLAPComponent r (Subgroup.centralizer ({x'} : Set G)) Y) ∧ m + 2 ≤ 𝒮.card := by
  classical
  haveI : Fact r.Prime := ⟨hrp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer ({x'} : Set G) with hCdef
  have hJC : J ≤ C := fun j hj => (hc.cfg.comp.1.1 hj).2
  have hJq : CFSG.Open.IsQuasisimple ↥J := hc.cfg.comp.1.2.2
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Finset (Subgroup G), ∀ Y, Y ∈ Ω ↔ GLAPComponent r C Y :=
    ⟨(Set.toFinite {Y : Subgroup G | GLAPComponent r C Y}).toFinset, fun Y => by simp⟩
  have hclC : ∀ Y ∈ Ω, ∀ g ∈ C, GLBConj g Y ∈ Ω := by
    intro Y hY g hg
    rw [hΩ] at hY ⊢
    have h1 := glaPComponent_gLBConj hY g
    rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg)] at h1
  obtain ⟨Y₀, hY₀, j₀, hj₀, hj₀N⟩ : ∃ Y : Subgroup G, GLAPComponent r C Y ∧
      ∃ j ∈ J, j ∉ Subgroup.normalizer (Y : Set G) := by
    by_contra hcon
    push_neg at hcon
    exact hN fun Y hY => fun j hj => by
      by_contra hjN
      exact absurd (hcon Y hY) (by push_neg; exact ⟨j, hj, hjN⟩)
  have hY₀Ω : Y₀ ∈ Ω := (hΩ Y₀).2 hY₀
  have hΩne : Ω.Nonempty := ⟨Y₀, hY₀Ω⟩
  let Jo : Subgroup ↥J :=
    { carrier := {j | ∀ Y ∈ Ω, GLBConj (j : G) Y = Y}
      mul_mem' := fun {a b} ha hb Y hY => by
        show GLBConj ((a * b : ↥J) : G) Y = Y
        rw [Subgroup.coe_mul, ← gLBConj_gLBConj, ha Y hY, hb Y hY]
      one_mem' := fun Y _ => by
        show GLBConj ((1 : ↥J) : G) Y = Y
        rw [Subgroup.coe_one, gLBConj_one]
      inv_mem' := fun {a} ha Y hY => by
        show GLBConj ((a⁻¹ : ↥J) : G) Y = Y
        rw [Subgroup.coe_inv]
        calc GLBConj (a : G)⁻¹ Y = GLBConj (a : G)⁻¹ (GLBConj (a : G) Y) := by rw [ha Y hY]
          _ = GLBConj ((a : G) * (a : G)⁻¹) Y := gLBConj_gLBConj _ _ _
          _ = Y := by rw [mul_inv_cancel, gLBConj_one] }
  have hJon : Jo.Normal := by
    refine ⟨fun n hn g Y hY => ?_⟩
    have hgY : GLBConj (g : G) Y ∈ Ω := hclC Y hY g (hJC g.2)
    have hn' : GLBConj (n : G) (GLBConj (g : G) Y) = GLBConj (g : G) Y := hn _ hgY
    show GLBConj ((g : G) * (n : G) * (g : G)⁻¹) Y = Y
    calc GLBConj ((g : G) * (n : G) * (g : G)⁻¹) Y
        = GLBConj (g : G)⁻¹ (GLBConj ((g : G) * (n : G)) Y) := (gLBConj_gLBConj _ _ _).symm
      _ = GLBConj (g : G)⁻¹ (GLBConj (n : G) (GLBConj (g : G) Y)) := by
          rw [gLBConj_gLBConj (n : G) (g : G) Y]
      _ = GLBConj (g : G)⁻¹ (GLBConj (g : G) Y) := by rw [hn']
      _ = Y := by rw [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]
  have hJoT : Jo ≠ ⊤ := by
    intro hT
    have hjJo : (⟨j₀, hj₀⟩ : ↥J) ∈ Jo := hT ▸ Subgroup.mem_top _
    apply hj₀N
    rw [mem_normalizer_iff_gLBConj_eq]
    exact hjJo Y₀ hY₀Ω
  haveI := hJon
  have hJoZ : Jo ≤ Subgroup.center ↥J := le_center_of_normal_of_isQuasisimple hJq hJon hJoT
  have hJ2 : m + 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥J) := by
    have h := hc.cfg.m2
    rw [hc.e_eq] at h
    exact h
  obtain ⟨U₀, hU₀2, hU₀card⟩ := lemma117_exists_two_rank hJ2
  set E : Subgroup G := U₀.map J.subtype with hEdef
  have hEC : E ≤ C := by
    rw [hEdef]
    exact (Subgroup.map_subtype_le U₀).trans hJC
  have hEel : IsElemAbelian 2 E := by
    refine ⟨lemma117_isMulCommutative_map hU₀2.1 J.subtype, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, hU₀2.2 u hu, map_one]
  have hEcard : Nat.card E = 2 ^ (m + 2) := by
    rw [hEdef, Subgroup.card_map_of_injective J.subtype_injective, hU₀card]
  have hfaithE : ∀ e ∈ E, (∀ Y ∈ Ω, GLBConj e Y = Y) → e = 1 := by
    intro e he hfix
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 he
    have huJo : u ∈ Jo := fun Y hY => hfix Y hY
    have hu1 : u = 1 := lemma117_eq_one_of_mem_center (hJoZ huJo) hc.cfg.odd_center (hU₀2.2 u hu)
    rw [hu1, map_one]
  have hclE : ∀ Y ∈ Ω, ∀ g ∈ E, GLBConj g Y ∈ Ω := fun Y hY g hg => hclC Y hY g (hEC hg)
  have hkey := lemma117_card_le Ω.card Ω rfl hΩne E hEel hclE (m + 2) hEcard hfaithE
  exact ⟨Ω, fun Y hY => (hΩ Y).1 hY, by omega⟩

private theorem y10x_core_top_eq_bot {H : Type} [Group H] [Finite H] {r : ℕ}
    (hO : GLAPPrimeCore r H = ⊥) : GLAPPrimeCoreOf r (⊤ : Subgroup H) = ⊥ := by
  have hcore : GLAPPrimeCore r ↥(⊤ : Subgroup H) = ⊥ := by
    have h := glaPPrimeCore_map_iso r (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H)
    rw [hO] at h
    exact Subgroup.map_injective (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H).injective
      (by simpa using h)
  unfold GLAPPrimeCoreOf
  rw [hcore, Subgroup.map_bot]

private theorem y10x_le_core_of_coprime {H : Type} [Group H] [Finite H] {r : ℕ} (N : Subgroup H)
    (hcop : Nat.Coprime r (Nat.card N)) : N ≤ GLAPPrimeCoreOf r N := by
  have htop : GLAPPrimeCore r ↥N = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, by rw [Subgroup.card_top]; exact hcop⟩)
  intro n hn
  unfold GLAPPrimeCoreOf
  exact Subgroup.mem_map.2 ⟨⟨n, hn⟩, by rw [htop]; exact Subgroup.mem_top _, rfl⟩

private theorem y10x_isSubnormal_coprime_eq_bot {H : Type} [Group H] [Finite H] {r : ℕ}
    (hr : r.Prime) (hO : GLAPPrimeCore r H = ⊥) {N : Subgroup H} (hN : IsSubnormal N ⊤)
    (hcop : Nat.Coprime r (Nat.card N)) : N = ⊥ := by
  have h1 := glaPPrimeCoreOf_le_of_isSubnormal hr hN
  rw [y10x_core_top_eq_bot hO] at h1
  exact le_bot_iff.1 ((y10x_le_core_of_coprime N hcop).trans h1)

private theorem y10x_isPGroup_center {H : Type} [Group H] [Finite H] {r : ℕ} (hr : r.Prime)
    (hO : GLAPPrimeCore r H = ⊥) {K : Subgroup H} (hK : IsSubnormal K ⊤) :
    IsPGroup r (Subgroup.center ↥K) := by
  haveI : Fact r.Prime := ⟨hr⟩
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos.ne') fun {d} hd hdvd => ?_⟩
  by_contra hne
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥K) d hdvd
  set w : H := ((z : ↥K) : H) with hw
  have hwc : ((z : ↥K)) ∈ Subgroup.center ↥K := z.2
  have hwK : w ∈ K := (z : ↥K).2
  have hcomm : ∀ g : ↥K, g * (z : ↥K) = (z : ↥K) * g := fun g =>
    (Subgroup.mem_center_iff.1 hwc) g
  have hcomm' : ∀ g ∈ K, g * w = w * g := fun g hg => by
    have := hcomm ⟨g, hg⟩
    simpa [hw] using congrArg Subtype.val this
  have hord : orderOf w = d := by
    rw [hw, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  set N : Subgroup H := Subgroup.zpowers w with hN
  have hNcard : Nat.card N = d := by rw [hN, Nat.card_zpowers, hord]
  have hNK : N ≤ K := by
    rw [hN, Subgroup.zpowers_le]; exact hwK
  have hNnorm : (N.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcj : (g : H) * (n : H) * (g : H)⁻¹ = (n : H) := by
      rw [← hj]
      have hc : Commute (g : H) w := hcomm' g g.2
      have : (g : H) * w ^ j = w ^ j * (g : H) := (hc.zpow_right j)
      rw [mul_inv_eq_iff_eq_mul, this]
    show (g : H) * (n : H) * (g : H)⁻¹ ∈ N
    rw [hcj]; exact hn
  have hsub : IsSubnormal N ⊤ :=
    isSubnormal_trans' (IsSubnormal.step hNK hNnorm (IsSubnormal.refl K)) hK
  have hcop : Nat.Coprime r (Nat.card N) := by
    rw [hNcard]; exact (Nat.coprime_primes hr hd).2 (Ne.symm hne)
  have hN1 := y10x_isSubnormal_coprime_eq_bot hr hO hsub hcop
  rw [hN1, Subgroup.card_bot] at hNcard
  exact hd.one_lt.ne hNcard

private theorem y10x_comm_central_left {Q : Type*} [Group Q] {z : Q} (hz : z ∈ Subgroup.center Q)
    (g h : Q) : ⁅z * g, h⁆ = ⁅g, h⁆ := by
  have key : ∀ a : Q, z * a = a * z := fun a => (Subgroup.mem_center_iff.1 hz a).symm
  rw [commutatorElement_def, commutatorElement_def]
  simp only [mul_inv_rev]
  calc z * g * h * (g⁻¹ * z⁻¹) * h⁻¹ = z * (g * h * g⁻¹) * z⁻¹ * h⁻¹ := by group
    _ = (g * h * g⁻¹) * z * z⁻¹ * h⁻¹ := by rw [key]
    _ = g * h * g⁻¹ * h⁻¹ := by group

private theorem y10x_comm_central_right {Q : Type*} [Group Q] {z : Q} (hz : z ∈ Subgroup.center Q)
    (g h : Q) : ⁅g, z * h⁆ = ⁅g, h⁆ := by
  have key : ∀ a : Q, z * a = a * z := fun a => (Subgroup.mem_center_iff.1 hz a).symm
  rw [commutatorElement_def, commutatorElement_def]
  simp only [mul_inv_rev]
  calc g * (z * h) * g⁻¹ * (h⁻¹ * z⁻¹) = (g * z) * h * g⁻¹ * h⁻¹ * z⁻¹ := by group
    _ = z * (g * h * g⁻¹ * h⁻¹) * z⁻¹ := by rw [← key g]; group
    _ = (g * h * g⁻¹ * h⁻¹) * z * z⁻¹ := by rw [key]
    _ = g * h * g⁻¹ * h⁻¹ := by group

private theorem y10x_dvd_card_quot_center {H : Type} [Group H] [Finite H] {r : ℕ} (hr : r.Prime)
    (hO : GLAPPrimeCore r H = ⊥) {K : Subgroup H} (hK : CFSG.Open.IsComponentOf K ⊤) :
    r ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hKs : IsSubnormal K ⊤ := hK.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  by_contra hndvd
  have hcopK : Nat.Coprime r (Nat.card (↥K ⧸ Subgroup.center ↥K)) :=
    (Nat.Prime.coprime_iff_not_dvd hr).2 hndvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (y10x_isPGroup_center hr hO hKs)
  have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥K))
      (Nat.card (↥K ⧸ Subgroup.center ↥K)) := by
    rw [hn]; exact Nat.Coprime.pow_left n hcopK
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime (N := Subgroup.center ↥K) hcop
  have hg : ∀ g : ↥K, ∃ z ∈ Subgroup.center ↥K, ∃ c ∈ C, z * c = g := fun g =>
    Subgroup.mem_sup_of_normal_left.1 (hC.isCompl.codisjoint.eq_top ▸ Subgroup.mem_top g)
  have hcomm : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro g1 _ g2 _
    obtain ⟨z1, hz1, c1, hc1, rfl⟩ := hg g1
    obtain ⟨z2, hz2, c2, hc2, rfl⟩ := hg g2
    rw [y10x_comm_central_left hz1, y10x_comm_central_right hz2]
    exact C.mul_mem (C.mul_mem (C.mul_mem hc1 hc2) (C.inv_mem hc1)) (C.inv_mem hc2)
  have hCtop : C = ⊤ := by
    rw [← top_le_iff]
    have h := hq.1
    rw [commutator_def] at h
    rw [← h]; exact hcomm
  have hZ : Subgroup.center ↥K = ⊥ := by
    have h := hC.disjoint
    rw [hCtop] at h
    exact disjoint_top.1 h
  have hcardK : Nat.card ↥K = Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
    have hc1 : Nat.card (Subgroup.center ↥K) = 1 := by rw [hZ, Subgroup.card_bot]
    rw [hc1, mul_one] at h
    exact h
  have hKbot : K = ⊥ :=
    y10x_isSubnormal_coprime_eq_bot hr hO hKs (by rw [hcardK]; exact hcopK)
  have hnt : Nontrivial ↥K := isQuasisimple_nontrivial hq
  exact ((Subgroup.nontrivial_iff_ne_bot K).1 hnt) hKbot

private theorem y10x_exists_rElement {H : Type} [Group H] [Finite H] {r : ℕ} (hr : r.Prime)
    (hO : GLAPPrimeCore r H = ⊥) {K : Subgroup H} (hK : CFSG.Open.IsComponentOf K ⊤) :
    ∃ y : H, y ∈ K ∧ (∃ k ∈ K, k * y ≠ y * k) ∧ ∃ n : ℕ, y ^ (r ^ n) = 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨gb, hgb⟩ := exists_prime_orderOf_dvd_card' (G := ↥K ⧸ Subgroup.center ↥K) r
    (y10x_dvd_card_quot_center hr hO hK)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  have hgZ : g ∉ Subgroup.center ↥K := by
    intro hgc
    have h1 : (QuotientGroup.mk g : ↥K ⧸ Subgroup.center ↥K) = 1 :=
      (QuotientGroup.eq_one_iff g).2 hgc
    rw [h1, orderOf_one] at hgb
    exact hr.one_lt.ne hgb
  have hgr : g ^ r ∈ Subgroup.center ↥K := by
    have h1 : (QuotientGroup.mk g : ↥K ⧸ Subgroup.center ↥K) ^ r = 1 := by
      rw [← hgb]; exact pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨k, hk⟩ := (y10x_isPGroup_center hr hO hK.2.1) ⟨g ^ r, hgr⟩
  have hk' : (g ^ r) ^ (r ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  refine ⟨(g : H), g.2, ?_, k + 1, ?_⟩
  · have hnc : ¬ ∀ h : ↥K, h * g = g * h := fun h => hgZ (Subgroup.mem_center_iff.2 h)
    obtain ⟨h, hh⟩ := not_forall.1 hnc
    exact ⟨(h : H), h.2, fun e => hh (Subtype.ext e)⟩
  · have : g ^ (r * r ^ k) = 1 := by rw [pow_mul]; exact hk'
    rw [pow_succ']
    exact_mod_cast (show ((g : H)) ^ (r * r ^ k) = 1 from by
      have := congrArg Subtype.val this
      simpa using this)

private theorem y10x_exists_involution {H : Type} [Group H] [Finite H] {K : Subgroup H}
    (hq : CFSG.Open.IsQuasisimple ↥K) : ∃ t ∈ K, t ≠ 1 ∧ t ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥K := ⟨hq.1⟩
  have hnt : Nontrivial ↥K := isQuasisimple_nontrivial hq
  have heven : 2 ∣ Nat.card ↥K := by
    by_contra hdiv
    have hodd : Odd (Nat.card ↥K) := Nat.not_even_iff_odd.1 (fun h => hdiv (even_iff_two_dvd.1 h))
    exact Group.IsPerfect.not_isSolvable ↥K (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 heven
  have ht : orderOf (g : H) = 2 := by rw [Subgroup.orderOf_coe, hg]
  refine ⟨(g : H), g.2, ?_, ?_⟩
  · intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · have := pow_orderOf_eq_one (g : H)
    rw [ht] at this
    exact this

private theorem y10x_barX_commute {X Y Y' : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hY : GLAPComponent r X Y) (hY' : GLAPComponent r X Y') (hne : Y ≠ Y') :
    ∀ a ∈ barX r X Y, ∀ b ∈ barX r X Y', a * b = b * a := by
  intro a ha b hb
  obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨x1, hx1, rfl⟩ := Subgroup.mem_map.1 hb
  have hx0Y : (x0 : G) ∈ Y := Subgroup.mem_subgroupOf.1 hx0
  have hx1Y' : (x1 : G) ∈ Y' := Subgroup.mem_subgroupOf.1 hx1
  have hY'Y : Y' ≤ centModSubgroup r Y := le_centModSubgroup_of_ne hr hY' hY (Ne.symm hne)
  have h2 : ⁅(x0 : G), (x1 : G)⁆ ∈ GLAPPrimeCoreOf r Y :=
    (mem_centModSubgroup.1 (hY'Y hx1Y')).2 (x0 : G) hx0Y
  have h3 : ⁅(x0 : G), (x1 : G)⁆ ∈ GLAPPrimeCoreOf r X :=
    glaPPrimeCoreOf_le_of_isSubnormal hr hY.2.1 h2
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.1 h3
  have hwx : w = ⁅x0, x1⁆ := Subtype.ext hwe
  have hcore : ⁅x0, x1⁆ ∈ GLAPPrimeCore r ↥X := hwx ▸ hw
  have hmap : (QuotientGroup.mk' (GLAPPrimeCore r ↥X) ⁅x0, x1⁆ : ↥X ⧸ GLAPPrimeCore r ↥X) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hcore
  rw [map_commutatorElement] at hmap
  exact commutatorElement_eq_one_iff_mul_comm.1 hmap

private theorem y10x_counting {H : Type} [Group H] [Finite H] {r : ℕ} (hr : r.Prime)
    {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Subgroup H) (y : ι → H)
    (hyK : ∀ i, y i ∈ K i)
    (hnc : ∀ i, ∃ k ∈ K i, k * y i ≠ y i * k)
    (hrel : ∀ i, ∃ n : ℕ, y i ^ (r ^ n) = 1)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, a * b = b * a)
    (a0 : H) (ha0 : ∀ i, y i * a0 = a0 * y i) :
    ∃ E : Subgroup H, IsElemAbelian r E ∧ r ^ Fintype.card ι ≤ Nat.card E ∧
      ∀ e ∈ E, e * a0 = a0 * e := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hSc : (Set.range y).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hij : i ≠ j := fun h => hne (congrArg y h)
    exact hcomm i j hij _ (hyK i) _ (hyK j)
  letI : CommGroup ↥(Subgroup.closure (Set.range y)) := Subgroup.closureCommGroupOfComm hSc
  let yD : ι → ↥(Subgroup.closure (Set.range y)) := fun i => ⟨y i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hgen : ∀ (h : H) (hh : h ∈ Subgroup.closure (Set.range y)),
      ∃ c : ι → ℤ, (⟨h, hh⟩ : ↥(Subgroup.closure (Set.range y))) = ∏ i, yD i ^ c i := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine ⟨Pi.single i 1, ?_⟩
      rw [Finset.prod_eq_single i]
      · simp [yD]
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji, yD]
      · intro h'
        exact absurd (Finset.mem_univ i) h'
    | one => exact ⟨0, by simp⟩
    | mul x z hx hz ihx ihz =>
      obtain ⟨c1, hc1⟩ := ihx
      obtain ⟨c2, hc2⟩ := ihz
      refine ⟨c1 + c2, ?_⟩
      rw [show (⟨x * z, Subgroup.mul_mem _ hx hz⟩ : ↥(Subgroup.closure (Set.range y))) =
        ⟨x, hx⟩ * ⟨z, hz⟩ from rfl, hc1, hc2, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, zpow_add]
    | inv x hx ihx =>
      obtain ⟨c1, hc1⟩ := ihx
      refine ⟨-c1, ?_⟩
      rw [show (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : ↥(Subgroup.closure (Set.range y))) =
        (⟨x, hx⟩ : ↥(Subgroup.closure (Set.range y)))⁻¹ from rfl, hc1, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [Pi.neg_apply, zpow_neg]
  have hKC : ∀ e : ι → ℤ, ∏ i, yD i ^ e i = 1 → ∀ i, (r : ℤ) ∣ e i := by
    intro e he i
    set P : ↥(Subgroup.closure (Set.range y)) := ∏ j ∈ Finset.univ.erase i, yD j ^ e j with hP
    have hsplit : yD i ^ e i * P = 1 :=
      (Finset.mul_prod_erase Finset.univ (fun j => yD j ^ e j) (Finset.mem_univ i)).trans he
    have hPc : ∀ a ∈ K i, Commute a (P : H) := by
      have hmem : ∀ j ∈ Finset.univ.erase i,
          (yD j ^ e j : ↥(Subgroup.closure (Set.range y))) ∈
            (Subgroup.centralizer (K i : Set H)).subgroupOf (Subgroup.closure (Set.range y)) := by
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        rw [Subgroup.mem_subgroupOf]
        refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
        have hc : Commute (y j) a := hcomm j i hji (y j) (hyK j) a ha
        have hc' : Commute (y j ^ e j) a := hc.zpow_left (e j)
        have hcoe : ((yD j ^ e j : ↥(Subgroup.closure (Set.range y))) : H) = y j ^ e j := by
          simp [yD]
        rw [hcoe]
        exact hc'.eq.symm
      have hPsub : P ∈ (Subgroup.centralizer (K i : Set H)).subgroupOf
          (Subgroup.closure (Set.range y)) :=
        Subgroup.prod_mem _ hmem
      intro a ha
      exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hPsub) a ha
    have hz_mul : y i ^ e i * (P : H) = 1 := by
      have := congrArg Subtype.val hsplit
      simpa [yD] using this
    have hz_eq : y i ^ e i = (P : H)⁻¹ := eq_inv_of_mul_eq_one_left hz_mul
    have hzc : ∀ a ∈ K i, Commute a (y i ^ e i) := by
      intro a ha
      rw [hz_eq]
      exact (hPc a ha).inv_right
    by_contra hndvd
    obtain ⟨n, hn⟩ := hrel i
    have hdvd : orderOf (y i) ∣ r ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hr).1 hdvd
    have hcop : IsCoprime (e i) ((orderOf (y i) : ℕ) : ℤ) := by
      rw [ha]
      push_cast
      have hprime : Prime (r : ℤ) := Nat.prime_iff_prime_int.1 hr
      have h1 : IsCoprime (r : ℤ) (e i) := (Prime.coprime_iff_not_dvd hprime).2 hndvd
      exact (IsCoprime.pow_left h1).symm
    obtain ⟨u, v, huv⟩ := hcop
    have hyu : y i = (y i ^ e i) ^ u := by
      have h2 : y i ^ (u * e i + v * (orderOf (y i) : ℤ)) = y i := by rw [huv, zpow_one]
      rw [zpow_add, mul_comm u (e i), zpow_mul, mul_comm v, zpow_mul, zpow_natCast,
        pow_orderOf_eq_one, one_zpow, mul_one] at h2
      exact h2.symm
    obtain ⟨k, hk, hne⟩ := hnc i
    apply hne
    have hc : Commute k (y i ^ e i) := hzc k hk
    rw [hyu]
    exact (hc.zpow_right u).eq
  let φ : ↥(Subgroup.closure (Set.range y)) →* ↥(Subgroup.closure (Set.range y)) := powMonoidHom r
  have hkerq : Nat.card (↥(Subgroup.closure (Set.range y)) ⧸ φ.range) = Nat.card φ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.range
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2)).symm
  have hpow : ∀ c : ι → ℤ, (∏ i, yD i ^ c i) ^ r = ∏ i, yD i ^ (c i * (r : ℤ)) := by
    intro c
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [← zpow_natCast, ← zpow_mul]
  let θ : (ι → Fin r) → (↥(Subgroup.closure (Set.range y)) ⧸ φ.range) :=
    fun f => QuotientGroup.mk (∏ i, yD i ^ ((f i : ℕ) : ℤ))
  have hθ : Function.Injective θ := by
    intro f g hfg
    obtain ⟨e, he⟩ := MonoidHom.mem_range.1 (QuotientGroup.eq.1 hfg)
    obtain ⟨c, hc⟩ := hgen e.1 e.2
    have heq : e = ∏ i, yD i ^ c i := by rw [← hc]
    have hA : (∏ i, yD i ^ (c i * (r : ℤ))) = (∏ i, yD i ^ ((f i : ℕ) : ℤ))⁻¹ * (∏ i, yD i ^ ((g i : ℕ) : ℤ)) := by
      rw [← hpow, ← heq]
      exact he
    have hkey : ∏ i, yD i ^ (c i * (r : ℤ) + ((f i : ℕ) : ℤ) - ((g i : ℕ) : ℤ)) = 1 := by
      have e1 : ∏ i, yD i ^ (c i * (r : ℤ) + ((f i : ℕ) : ℤ) - ((g i : ℕ) : ℤ)) =
          (∏ i, yD i ^ (c i * (r : ℤ))) * (∏ i, yD i ^ ((f i : ℕ) : ℤ)) *
            (∏ i, yD i ^ ((g i : ℕ) : ℤ))⁻¹ := by
        rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by rw [zpow_sub, zpow_add]
      rw [e1, hA, mul_right_comm (∏ i, yD i ^ ((f i : ℕ) : ℤ))⁻¹ (∏ i, yD i ^ ((g i : ℕ) : ℤ))
        (∏ i, yD i ^ ((f i : ℕ) : ℤ)), inv_mul_cancel, one_mul, mul_inv_cancel]
    have hdvd : ∀ i, (r : ℤ) ∣ ((f i : ℕ) : ℤ) - ((g i : ℕ) : ℤ) := by
      intro i
      have h1 := hKC _ hkey i
      have h2 : ((f i : ℕ) : ℤ) - ((g i : ℕ) : ℤ) = c i * (r : ℤ) + ((f i : ℕ) : ℤ) - ((g i : ℕ) : ℤ) -
          c i * (r : ℤ) := by ring
      rw [h2]
      exact dvd_sub h1 (dvd_mul_left _ _)
    funext i
    apply Fin.ext
    obtain ⟨t, ht⟩ := hdvd i
    have hf : ((f i : ℕ) : ℤ) < r := by exact_mod_cast (f i).isLt
    have hg : ((g i : ℕ) : ℤ) < r := by exact_mod_cast (g i).isLt
    have hf0 : (0 : ℤ) ≤ ((f i : ℕ) : ℤ) := by positivity
    have hg0 : (0 : ℤ) ≤ ((g i : ℕ) : ℤ) := by positivity
    have hr0 : (0 : ℤ) < r := by exact_mod_cast hr.pos
    have ht0 : t = 0 := by
      rcases lt_trichotomy t 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [ht0, mul_zero] at ht
    exact_mod_cast (sub_eq_zero.1 ht)
  have hcard : Nat.card (ι → Fin r) ≤
      Nat.card (↥(Subgroup.closure (Set.range y)) ⧸ φ.range) :=
    Nat.card_le_card_of_injective θ hθ
  have hcard' : r ^ Fintype.card ι ≤ Nat.card (↥(Subgroup.closure (Set.range y)) ⧸ φ.range) := by
    have h := hcard
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin,
      Nat.card_eq_fintype_card (α := ι)] at h
    exact h
  have hEcard : Nat.card (φ.ker.map (Subgroup.closure (Set.range y)).subtype) = Nat.card φ.ker :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hDc : ∀ h ∈ Subgroup.closure (Set.range y), h * a0 = a0 * h := by
    intro h hh
    have hle : Subgroup.closure (Set.range y) ≤ Subgroup.centralizer ({a0} : Set H) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff.1 hg]; exact (ha0 i).symm
    exact (Subgroup.mem_centralizer_iff.1 (hle hh) a0 rfl).symm
  refine ⟨φ.ker.map (Subgroup.closure (Set.range y)).subtype, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨d1, -, hd1⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨d2, -, hd2⟩ := Subgroup.mem_map.1 b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hd1, ← hd2]
      exact congrArg Subtype.val (mul_comm d1 d2)
    · obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hx
      have hd1 : d ^ r = 1 := by
        have := MonoidHom.mem_ker.1 hd
        simpa [φ, powMonoidHom_apply] using this
      have := congrArg Subtype.val hd1
      simpa using this
  · rw [hEcard, ← hkerq]
    exact hcard'
  · intro e he
    obtain ⟨d, -, rfl⟩ := Subgroup.mem_map.1 he
    exact hDc d.1 d.2


private theorem y10x_fitting_le_pCore {H : Type} [Group H] [Finite H] {r : ℕ} (hr : r.Prime)
    (hO : GLAPPrimeCore r H = ⊥) : CFSG.fittingSubgroup H ≤ CFSG.pCore r H := by
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun p => ?_
  by_cases h : (p : ℕ) = r
  · rw [h]
  · have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    haveI : Fact (p : ℕ).Prime := ⟨hp⟩
    have hle : CFSG.pCore (p : ℕ) H ≤ GLAPPrimeCore r H := by
      refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := (p : ℕ)) (G := H))
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes hr hp).2 (Ne.symm h))
    rw [hO] at hle
    have hbot : CFSG.pCore (p : ℕ) H = ⊥ := le_bot_iff.1 hle
    rw [hbot]
    exact bot_le

private theorem y10x_barX_conj_mem {C Y : Subgroup G} {r : ℕ} (hYC : Y ≤ C) {x : ↥C}
    (hx : (x : G) ∈ Subgroup.normalizer (Y : Set G)) :
    ∀ h ∈ barX r C Y, (QuotientGroup.mk' (GLAPPrimeCore r ↥C) x) * h *
      (QuotientGroup.mk' (GLAPPrimeCore r ↥C) x)⁻¹ ∈ barX r C Y := by
  intro h hh
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hh
  have hcY : (c : G) ∈ Y := Subgroup.mem_subgroupOf.1 hc
  refine Subgroup.mem_map.2 ⟨x * c * x⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.1 hx (c : G)).1 hcY
    simpa using this
  · rw [map_mul, map_mul, map_inv]

private theorem y10x_barX_normalizer {C Y : Subgroup G} {r : ℕ} (hYC : Y ≤ C) {x : ↥C}
    (hx : (x : G) ∈ Subgroup.normalizer (Y : Set G)) :
    QuotientGroup.mk' (GLAPPrimeCore r ↥C) x ∈
      Subgroup.normalizer ((barX r C Y : Subgroup _) : Set _) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact y10x_barX_conj_mem hYC hx h
  · intro hh
    have hx' : ((x⁻¹ : ↥C) : G) ∈ Subgroup.normalizer (Y : Set G) := by
      have : ((x⁻¹ : ↥C) : G) = (x : G)⁻¹ := rfl
      rw [this]
      exact Subgroup.inv_mem _ hx
    have key := y10x_barX_conj_mem (r := r) hYC hx' _ hh
    rw [map_inv] at key
    convert key using 1
    group

private theorem y10x_isCatalog_iso : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y →
    CFSG.Open.IsCatalogGroup Y → CFSG.Open.IsCatalogGroup X := by
  intro X Y _ _ e hY
  obtain ⟨i, ⟨f⟩⟩ := hY
  exact ⟨i, ⟨e.trans f⟩⟩

private theorem y10x_perfect_barX {C J : Subgroup G} {r : ℕ} (hJC : J ≤ C) [Group.IsPerfect ↥J] :
    Group.IsPerfect ↥(barX r C J) := by
  let ψJ : ↥J →* (↥C ⧸ GLAPPrimeCore r ↥C) :=
    (QuotientGroup.mk' (GLAPPrimeCore r ↥C)).comp (Subgroup.inclusion hJC)
  have hrange : ψJ.range = barX r C J := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact Subgroup.mem_map.2 ⟨⟨j, hJC j.2⟩, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
    · intro hz
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
      exact ⟨⟨c, Subgroup.mem_subgroupOf.1 hc⟩, rfl⟩
  have h := Group.IsPerfect.range ψJ
  rwa [hrange] at h

private theorem y10x_commute_pCore {C J : Subgroup G} {r : ℕ}
    (hJC : J ≤ C) (hR : ⁅J, oPPrimeP r C⁆ ≤ GLAPPrimeCoreOf r C) :
    ∀ x ∈ barX r C J, ∀ h ∈ CFSG.pCore r (↥C ⧸ GLAPPrimeCore r ↥C), h * x = x * h := by
  intro x hx h hh
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore r ↥C) h
  have hcO : (c : G) ∈ oPPrimeP r C :=
    Subgroup.mem_map.2 ⟨c, hh, rfl⟩
  have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
  have hcomm : ⁅(j : G), (c : G)⁆ ∈ GLAPPrimeCoreOf r C :=
    hR (Subgroup.commutator_mem_commutator hjJ hcO)
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.1 hcomm
  have hwj : w = ⁅j, c⁆ := Subtype.ext hwe
  have hcore : ⁅j, c⁆ ∈ GLAPPrimeCore r ↥C := hwj ▸ hw
  have hmap : (QuotientGroup.mk' (GLAPPrimeCore r ↥C) ⁅j, c⁆ : ↥C ⧸ GLAPPrimeCore r ↥C) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hcore
  rw [map_commutatorElement] at hmap
  exact (commutatorElement_eq_one_iff_mul_comm.1 hmap).symm

private theorem y10x_core_le_oPPrimeP {C : Subgroup G} {r : ℕ} :
    GLAPPrimeCoreOf r C ≤ oPPrimeP r C := by
  intro w hw
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hw
  refine Subgroup.mem_map.2 ⟨c, ?_, rfl⟩
  show QuotientGroup.mk' (GLAPPrimeCore r ↥C) c ∈ CFSG.pCore r (↥C ⧸ GLAPPrimeCore r ↥C)
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff c).2 hc]
  exact one_mem _

private theorem y10x_outer_solvable {m r : ℕ} {C Y : Subgroup G} (hctx : ThmACtx G m)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hrp : r.Prime)
    (hY : GLAPComponent r C Y) (hCtop : C ≠ ⊤) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥(barX r C Y) ⧸ Subgroup.center ↥(barX r C Y))) := by
  classical
  have hYC : Y ≤ C := hY.1
  have hK : CFSG.Open.IsComponentOf (barX r C Y) ⊤ := hY.2.2.1
  have hq : CFSG.Open.IsQuasisimple ↥(barX r C Y) := hK.2.2
  haveI : IsSimpleGroup (↥(barX r C Y) ⧸ Subgroup.center ↥(barX r C Y)) := hq.2
  have hYtop : Y ≠ ⊤ := fun h => hCtop (top_le_iff.1 (h ▸ hYC))
  let ψ0 : ↥Y →* (↥C ⧸ GLAPPrimeCore r ↥C) :=
    (QuotientGroup.mk' (GLAPPrimeCore r ↥C)).comp (Subgroup.inclusion hYC)
  have hψ0 : ∀ y : ↥Y, ψ0 y ∈ barX r C Y := fun y =>
    Subgroup.mem_map.2 ⟨⟨y, hYC y.2⟩, Subgroup.mem_subgroupOf.2 y.2, rfl⟩
  let ψ : ↥Y →* ↥(barX r C Y) := ψ0.codRestrict (barX r C Y) hψ0
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
    refine ⟨⟨(c : G), Subgroup.mem_subgroupOf.1 hc⟩, ?_⟩
    ext
    rfl
  let φ : ↥Y →* (↥(barX r C Y) ⧸ Subgroup.center ↥(barX r C Y)) :=
    (QuotientGroup.mk' (Subgroup.center ↥(barX r C Y))).comp ψ
  have hφsurj : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp hψsurj
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have hcat : CFSG.Open.IsCatalogGroup (↥(barX r C Y) ⧸ Subgroup.center ↥(barX r C Y)) :=
    CFSG.KCore.KProperNonab.catalogue_of_surjective y10x_isCatalog_iso hctx.1.kProper Y hYtop
      hnonab φ hφsurj
  exact hSch _ inferInstance hnonab hcat

theorem twoLocalRank_of_components {r : ℕ} (hrp : r.Prime) (hr2 : r ≠ 2) {X : Subgroup G} (𝒮 : Finset (Subgroup G))
    (h𝒮 : ∀ Y ∈ 𝒮, GLAPComponent r X Y) : 𝒮.card - 1 ≤ GLATwoLocalRank r G := by
  classical
  rcases 𝒮.eq_empty_or_nonempty with hempty | ⟨Y₀, hY₀⟩
  · simp [hempty]
  haveI : Fact r.Prime := ⟨hrp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : GLAPPrimeCore r (↥X ⧸ GLAPPrimeCore r ↥X) = ⊥ := glaPPrimeCore_quotient_eq_bot hrp
  set T : Finset (Subgroup G) := 𝒮.erase Y₀ with hT
  have hTmem : ∀ Y ∈ T, Y ∈ 𝒮 := fun Y hY => Finset.mem_of_mem_erase hY
  have hTne : ∀ Y ∈ T, Y ≠ Y₀ := fun Y hY => Finset.ne_of_mem_erase hY
  have hex : ∀ Y : ↥T, ∃ y : (↥X ⧸ GLAPPrimeCore r ↥X), y ∈ barX r X Y.1 ∧
      (∃ k ∈ barX r X Y.1, k * y ≠ y * k) ∧ ∃ n : ℕ, y ^ (r ^ n) = 1 :=
    fun Y => y10x_exists_rElement hrp hO (h𝒮 Y.1 (hTmem Y.1 Y.2)).2.2.1
  choose y hyK hnc hrel using hex
  obtain ⟨t, htK, ht1, ht2⟩ :=
    y10x_exists_involution (K := barX r X Y₀) (h𝒮 Y₀ hY₀).2.2.1.2.2
  have hcomm : ∀ i j : ↥T, i ≠ j → ∀ a ∈ barX r X i.1, ∀ b ∈ barX r X j.1, a * b = b * a :=
    fun i j hij => y10x_barX_commute hrp (h𝒮 i.1 (hTmem i.1 i.2)) (h𝒮 j.1 (hTmem j.1 j.2))
      (fun h => hij (Subtype.ext h))
  have ha0 : ∀ i : ↥T, y i * t = t * y i := fun i =>
    y10x_barX_commute hrp (h𝒮 i.1 (hTmem i.1 i.2)) (h𝒮 Y₀ hY₀) (hTne i.1 i.2) _ (hyK i) _ htK
  obtain ⟨E, hE, hEcard, hEcent⟩ :=
    y10x_counting hrp (fun i : ↥T => barX r X i.1) y hyK hnc hrel hcomm t ha0
  have htord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hSne : Subgroup.zpowers t ≠ ⊥ := fun h => ht1 (Subgroup.zpowers_eq_bot.1 h)
  have hS2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htord]; simp)
  have hES : E ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup _) : Set (↥X ⧸ GLAPPrimeCore r ↥X)) := by
    intro e he
    have hcommt : Commute e t := hEcent e he
    have hconj : ∀ k : ℤ, e * t ^ k * e⁻¹ = t ^ k := fun k => by
      rw [mul_inv_eq_iff_eq_mul, (hcommt.zpow_right k).eq]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [hconj k]
      exact Subgroup.zpow_mem_zpowers t k
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
      have hinv : Commute e⁻¹ (t ^ k) := (hcommt.zpow_right k).inv_left
      have h1 : h = e⁻¹ * (e * h * e⁻¹) * e := by group
      rw [← hk] at h1
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, by rw [h1, hinv.eq, inv_mul_cancel_right]⟩
  have hm := card_le_pow_glaTwoLocalRank hrp hE hSne hS2 hES
  have hpow : r ^ Fintype.card ↥T ≤ r ^ GLATwoLocalRank r (↥X ⧸ GLAPPrimeCore r ↥X) :=
    hEcard.trans hm
  have hle : Fintype.card ↥T ≤ GLATwoLocalRank r (↥X ⧸ GLAPPrimeCore r ↥X) :=
    (Nat.pow_le_pow_iff_right hrp.one_lt).1 hpow
  have hlift : GLATwoLocalRank r (↥X ⧸ GLAPPrimeCore r ↥X) ≤ GLATwoLocalRank r G :=
    (twoLocalRank_quot_le hrp hr2 X).trans (twoLocalRank_le_top hrp X)
  have hTcard : Fintype.card ↥T = 𝒮.card - 1 := by
    rw [Fintype.card_coe, hT, Finset.card_erase_of_mem hY₀]
  omega

theorem j_norm_comps (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J) {r : ℕ} (hr : r = p ∨ r = p')
    (hrp : r.Prime) (hr2 : r ≠ 2) (hrank : GLATwoLocalRank r G = m) :
    ∀ Y : Subgroup G, GLAPComponent r (Subgroup.centralizer ({x'} : Set G)) Y → J ≤ Subgroup.normalizer (Y : Set G) := by
  by_contra hN
  obtain ⟨𝒮, h𝒮, hcard⟩ := exists_many_components hctx hc hr hrp hr2 hN
  have := twoLocalRank_of_components hrp hr2 𝒮 h𝒮
  omega

theorem jbar_le_layer_mul (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hctx : ThmACtx G m)
    (hc : Cfg116 G m p L p' B' x' J) {r : ℕ} (hr : r = p ∨ r = p') (hrp : r.Prime)
    (hR : ⁅J, oPPrimeP r (Subgroup.centralizer ({x'} : Set G))⁆ ≤ GLAPPrimeCoreOf r (Subgroup.centralizer ({x'} : Set G)))
    (hN : ∀ Y : Subgroup G, GLAPComponent r (Subgroup.centralizer ({x'} : Set G)) Y → J ≤ Subgroup.normalizer (Y : Set G)) :
    J ≤ GLAPLayer r (Subgroup.centralizer ({x'} : Set G)) ⊔ oPPrimeP r (Subgroup.centralizer ({x'} : Set G)) := by
  classical
  haveI : Fact r.Prime := ⟨hrp⟩
  set C : Subgroup G := Subgroup.centralizer ({x'} : Set G) with hCdef
  have hJC : J ≤ C := fun j hj => (hc.cfg.comp.1.1 hj).2
  have hJq : CFSG.Open.IsQuasisimple ↥J := hc.cfg.comp.1.2.2
  haveI : Group.IsPerfect ↥J := ⟨hJq.1⟩
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have hz : x' ∈ Subgroup.center G := by
      refine Subgroup.mem_center_iff.2 fun g => ?_
      have hg : g ∈ C := by rw [hCt]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.1 hg) x' (Set.mem_singleton x') |>.symm
    haveI := hctx.1.simple
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
    · exact hc.cfg.ne_one (Subgroup.mem_bot.1 (h ▸ hz))
    · obtain ⟨a, b, hab⟩ := hctx.1.nonabelian
      have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm
  have hO : GLAPPrimeCore r (↥C ⧸ GLAPPrimeCore r ↥C) = ⊥ := glaPPrimeCore_quotient_eq_bot hrp
  have hJbP : Group.IsPerfect ↥(barX r C J) := y10x_perfect_barX hJC
  have hnorm : ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore r ↥C), CFSG.Open.IsComponentOf K ⊤ →
      barX r C J ≤ Subgroup.normalizer (K : Set (↥C ⧸ GLAPPrimeCore r ↥C)) := by
    intro K hK
    obtain ⟨Y, hY, rfl⟩ := exists_glaPComponent_barX_eq C hK
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hx
    exact y10x_barX_normalizer hY.1 (hN Y hY (Subgroup.mem_subgroupOf.1 hj))
  have hF : CFSG.fittingSubgroup (↥C ⧸ GLAPPrimeCore r ↥C) ≤
      CFSG.pCore r (↥C ⧸ GLAPPrimeCore r ↥C) :=
    y10x_fitting_le_pCore hrp hO
  have hcentr : ⁅barX r C J, CFSG.fittingSubgroup (↥C ⧸ GLAPPrimeCore r ↥C)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact y10x_commute_pCore hJC hR x hx f (hF hf)
  have houter : ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore r ↥C), CFSG.Open.IsComponentOf K ⊤ →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (↥K ⧸ Subgroup.center ↥K)) := by
    intro K hK
    obtain ⟨Y, hY, rfl⟩ := exists_glaPComponent_barX_eq C hK
    exact y10x_outer_solvable hctx hSch hrp hY hCtop
  have hlayer : barX r C J ≤
      CFSG.ComponentClassification.Layer.subgroup (↥C ⧸ GLAPPrimeCore r ↥C) :=
    CFSG.ComponentClassification.GeneralizedFitting.perfect_normalizer_enters_layer
      (barX r C J) hcentr hnorm houter
  have hL : CFSG.ComponentClassification.Layer.subgroup (↥C ⧸ GLAPPrimeCore r ↥C) ≤
      barX r C (GLAPLayer r C) := by
    rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
    refine sSup_le fun K hK => ?_
    obtain ⟨Y, hY, rfl⟩ := exists_glaPComponent_barX_eq C hK
    refine barX_mono r ?_
    exact le_sSup (s := {L' | GLAPComponent r C L'}) hY
  intro j hj
  have hjb : (QuotientGroup.mk' (GLAPPrimeCore r ↥C) (⟨j, hJC hj⟩ : ↥C)) ∈ barX r C J :=
    Subgroup.mem_map.2 ⟨⟨j, hJC hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
  obtain ⟨l, hl, hlj⟩ := Subgroup.mem_map.1 (hL (hlayer hjb))
  have hlL : (l : G) ∈ GLAPLayer r C := Subgroup.mem_subgroupOf.1 hl
  have hker : l⁻¹ * (⟨j, hJC hj⟩ : ↥C) ∈ GLAPPrimeCore r ↥C := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    have h1 : QuotientGroup.mk' (GLAPPrimeCore r ↥C) (l⁻¹ * (⟨j, hJC hj⟩ : ↥C)) = 1 := by
      rw [map_mul, map_inv, hlj, inv_mul_cancel]
    exact h1
  have hjmul : j = (l : G) * ((l⁻¹ * (⟨j, hJC hj⟩ : ↥C) : ↥C) : G) := by
    simp
  rw [hjmul]
  exact Subgroup.mul_mem_sup hlL
    (y10x_core_le_oPPrimeP (Subgroup.mem_map.2 ⟨_, hker, rfl⟩))

private theorem lemma117_perfect_hom_mem {H Q : Type} [Group H] [Group Q] [Finite H] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hH : commutator H = ⊤) {A R : Subgroup Q} (hA : A.Normal) (hR : IsPGroup p R)
    (f : H →* Q) (hf : ∀ h, f h ∈ A ⊔ R) (h : H) : f h ∈ A := by
  haveI : Fact p.Prime := ⟨hp⟩
  set g : H →* Q ⧸ A := (QuotientGroup.mk' A).comp f with hg
  have hTR : g.range ≤ R.map (QuotientGroup.mk' A) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, ha, r, hr, har⟩ := Subgroup.mem_sup_of_normal_left.1 (hf x)
    refine Subgroup.mem_map.2 ⟨r, hr, ?_⟩
    rw [hg, MonoidHom.comp_apply, ← har, map_mul]
    have ha1 : QuotientGroup.mk' A a = 1 := (QuotientGroup.eq_one_iff a).2 ha
    rw [ha1, one_mul]
  have hTp : IsPGroup p g.range := (hR.map (QuotientGroup.mk' A)).to_le hTR
  have hTperf : ⁅g.range, g.range⁆ = g.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hH]
  by_contra hfA
  have hne : g.range ≠ ⊥ := by
    intro h0
    apply hfA
    have hmem : g h ∈ g.range := ⟨h, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff _).1 hmem
  haveI : Group.IsPerfect ↥g.range := Subgroup.isPerfect_iff.2 hTperf
  haveI : Group.IsNilpotent ↥g.range := hTp.isNilpotent
  haveI : Nontrivial ↥g.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  exact Group.IsPerfect.not_isSolvable ↥g.range inferInstance

theorem le_layer_of_le_mul {r : ℕ} (hrp : r.Prime) {C J : Subgroup G} (hJC : J ≤ C) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJr : r ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (h : J ≤ GLAPLayer r C ⊔ oPPrimeP r C) : J ≤ GLAPLayer r C := by
  haveI : Fact r.Prime := ⟨hrp⟩
  have hΛC : GLAPLayer r C ≤ C := sSup_le fun L hL => hL.1
  have hOC : oPPrimeP r C ≤ C := Subgroup.map_subtype_le _
  have hΛn : ((GLAPLayer r C).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hΛC).2
      (fun g hg => mem_normalizer_glaPLayer (Subgroup.le_normalizer hg))
  set Λ' : Subgroup ↥C := (GLAPLayer r C).subgroupOf C with hΛ'
  set O' : Subgroup ↥C := (oPPrimeP r C).subgroupOf C with hO'
  set K : Subgroup ↥C := GLAPPrimeCore r ↥C with hK
  set π : ↥C →* PQuot r C := QuotientGroup.mk' K with hπ
  set R : Subgroup (PQuot r C) := CFSG.pCore r (PQuot r C) with hR
  have hRp : IsPGroup r R := CFSG.pCore_isPGroup
  set A : Subgroup (PQuot r C) := Λ'.map π with hA
  have hAn : A.Normal := Subgroup.Normal.map hΛn π (QuotientGroup.mk'_surjective K)
  have hOR : ∀ c : ↥C, c ∈ O' → π c ∈ R := by
    intro c hc
    have hc' : (c : G) ∈ oPPrimeP r C := Subgroup.mem_subgroupOf.1 hc
    unfold oPPrimeP at hc'
    obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.1 hc'
    have hdc' : d = c := Subtype.ext hdc
    rw [← hdc']
    exact hd
  have hsup : (GLAPLayer r C ⊔ oPPrimeP r C).subgroupOf C = Λ' ⊔ O' :=
    Subgroup.subgroupOf_sup hΛC hOC
  have hJ_sup : ∀ j : ↥J, π ⟨j, hJC j.2⟩ ∈ A ⊔ R := by
    intro j
    have hj : (⟨j, hJC j.2⟩ : ↥C) ∈ Λ' ⊔ O' := by
      rw [← hsup]
      exact Subgroup.mem_subgroupOf.2 (h j.2)
    obtain ⟨l, hl, o, ho, hlo⟩ := Subgroup.mem_sup_of_normal_left.1 hj
    rw [← hlo, map_mul]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_map.2 ⟨l, hl, rfl⟩))
      (Subgroup.mem_sup_right (hOR o ho))
  let f : ↥J →* PQuot r C := π.comp (Subgroup.inclusion hJC)
  have hfA : ∀ j : ↥J, f j ∈ A := fun j =>
    lemma117_perfect_hom_mem hrp hJq.1 hAn hRp f (fun j => hJ_sup j) j
  let g : ↥J →* ↥C ⧸ Λ' := (QuotientGroup.mk' Λ').comp (Subgroup.inclusion hJC)
  by_contra hJΛ
  have hM : g.ker ≠ ⊤ := by
    intro hMt
    apply hJΛ
    intro j hj
    have hjM : (⟨j, hj⟩ : ↥J) ∈ g.ker := hMt ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hjM
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hjM)
  have hMc : g.ker ≤ Subgroup.center ↥J :=
    le_center_of_normal_of_isQuasisimple hJq inferInstance hM
  let hK' : ↥K →* ↥C ⧸ Λ' := (QuotientGroup.mk' Λ').comp K.subtype
  have hsub : g.range ≤ hK'.range := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨l, hl, hlj⟩ := Subgroup.mem_map.1 (hfA j)
    have hlj' : π l = π (⟨j, hJC j.2⟩ : ↥C) := hlj
    have hk : l⁻¹ * (⟨j, hJC j.2⟩ : ↥C) ∈ K := by
      have : π (l⁻¹ * (⟨j, hJC j.2⟩ : ↥C)) = 1 := by
        rw [map_mul, map_inv, hlj', inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 this
    refine ⟨⟨_, hk⟩, ?_⟩
    show (QuotientGroup.mk' Λ') (l⁻¹ * (⟨j, hJC j.2⟩ : ↥C)) = (QuotientGroup.mk' Λ') (⟨j, hJC j.2⟩ : ↥C)
    have hl1 : QuotientGroup.mk' Λ' l⁻¹ = 1 := (QuotientGroup.eq_one_iff l⁻¹).2 (Λ'.inv_mem hl)
    rw [map_mul, hl1, one_mul]
  have hcard : Nat.card g.range ∣ Nat.card K :=
    (Subgroup.card_dvd_of_le hsub).trans (Subgroup.card_range_dvd hK')
  have hcop : ¬ r ∣ Nat.card K := (Nat.Prime.coprime_iff_not_dvd hrp).1 CFSG.pPrimeCore_coprime_card
  have hidx : Subgroup.index (Subgroup.center ↥J) ∣ Subgroup.index g.ker :=
    Subgroup.index_dvd_of_le hMc
  have hquot : Subgroup.index g.ker = Nat.card g.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have hr1 : r ∣ Nat.card g.range := hquot ▸ (hJr.trans hidx)
  exact hcop (hr1.trans hcard)

theorem j_le_layer (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hctx : ThmACtx G m)
    (hc : Cfg116 G m p L p' B' x' J) {r : ℕ} (hr : r = p ∨ r = p') (hrp : r.Prime)
    (hR : ⁅J, oPPrimeP r (Subgroup.centralizer ({x'} : Set G))⁆ ≤ GLAPPrimeCoreOf r (Subgroup.centralizer ({x'} : Set G)))
    (hN : ∀ Y : Subgroup G, GLAPComponent r (Subgroup.centralizer ({x'} : Set G)) Y → J ≤ Subgroup.normalizer (Y : Set G)) :
    J ≤ GLAPLayer r (Subgroup.centralizer ({x'} : Set G)) := by
  have hJx : J ≤ Subgroup.centralizer ({x'} : Set G) := fun j hj => (hc.cfg.comp.1.1 hj).2
  have hdvd : r ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    rcases hr with rfl | rfl
    · exact (Dvd.intro _ rfl).trans hc.cfg.dvd
    · exact (Dvd.intro_left _ rfl).trans hc.cfg.dvd
  exact le_layer_of_le_mul hrp hJx hc.cfg.comp.1.2.2 hdvd (jbar_le_layer_mul hSch hctx hc hr hrp hR hN)


section Lemma117Closure


open CFSG.Open
open scoped commutatorElement

variable {Q : Type} [Group Q]

private theorem lemma117_comm_mul_central {X : Type} [Group X] {z : X} (hz : ∀ x : X, x * z = z * x) (a b : X) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hzb : z * b = b * z := (hz b).symm
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hzb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem lemma117_comm_central_mul {X : Type} [Group X] {z : X} (hz : ∀ x : X, x * z = z * x) (a b : X) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hza : a * z = z * a := hz a
  have hza' : z * a⁻¹ = a⁻¹ * z := by
    calc z * a⁻¹ = a⁻¹ * (a * z) * a⁻¹ := by group
      _ = a⁻¹ * (z * a) * a⁻¹ := by rw [hza]
      _ = a⁻¹ * z := by group
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hza']
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem lemma117_qs_normal_dichotomy {S A : Subgroup Q} (hS : CFSG.Open.IsQuasisimple ↥S) (hAS : A ≤ S)
    (hnorm : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A) :
    (∀ a ∈ A, ∀ s ∈ S, s * a = a * s) ∨ S ≤ A := by
  classical
  let A' : Subgroup ↥S := A.subgroupOf S
  let π := QuotientGroup.mk' (Subgroup.center ↥S)
  have hA'n : A'.Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hnorm (g : Q) g.2 (n : Q) hn
    simpa [mul_assoc] using this
  haveI : (A'.map π).Normal := hA'n.map π (QuotientGroup.mk'_surjective _)
  rcases hS.2.eq_bot_or_eq_top_of_normal (A'.map π) with h | h
  · left
    intro a ha s hs
    have ha' : (⟨a, hAS ha⟩ : ↥S) ∈ A' := Subgroup.mem_subgroupOf.2 ha
    have h1 : π ⟨a, hAS ha⟩ ∈ A'.map π := Subgroup.mem_map.2 ⟨_, ha', rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have hz : (⟨a, hAS ha⟩ : ↥S) ∈ Subgroup.center ↥S := (QuotientGroup.eq_one_iff _).1 h1
    have hc := (Subgroup.mem_center_iff.1 hz) ⟨s, hs⟩
    have := congrArg Subtype.val hc
    simpa using this
  · right
    have hc : commutator ↥S ≤ A' := by
      rw [commutator_def]
      refine Subgroup.commutator_le.2 fun g1 _ g2 _ => ?_
      have m1 : π g1 ∈ A'.map π := by rw [h]; exact Subgroup.mem_top _
      have m2 : π g2 ∈ A'.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨a1, ha1, e1⟩ := Subgroup.mem_map.1 m1
      obtain ⟨a2, ha2, e2⟩ := Subgroup.mem_map.1 m2
      obtain ⟨z1, hz1, rfl⟩ : ∃ z ∈ Subgroup.center ↥S, g1 = a1 * z :=
        ⟨a1⁻¹ * g1, (QuotientGroup.eq).1 e1, by group⟩
      obtain ⟨z2, hz2, rfl⟩ : ∃ z ∈ Subgroup.center ↥S, g2 = a2 * z :=
        ⟨a2⁻¹ * g2, (QuotientGroup.eq).1 e2, by group⟩
      have key : ⁅a1 * z1, a2 * z2⁆ = ⁅a1, a2⁆ := by
        rw [lemma117_comm_mul_central (Subgroup.mem_center_iff.1 hz1),
          lemma117_comm_central_mul (Subgroup.mem_center_iff.1 hz2)]
      rw [key]
      exact A'.mul_mem (A'.mul_mem (A'.mul_mem ha1 ha2) (A'.inv_mem ha1)) (A'.inv_mem ha2)
    have htop : (⊤ : Subgroup ↥S) ≤ A' := by
      rw [← hS.1]
      exact hc
    intro s hs
    have := htop (Subgroup.mem_top (⟨s, hs⟩ : ↥S))
    exact Subgroup.mem_subgroupOf.1 this

private theorem lemma117_qs_comm_self {Y : Subgroup Q} (hY : CFSG.Open.IsQuasisimple ↥Y) : ⁅Y, Y⁆ = Y := by
  have h1 : (⁅(⊤ : Subgroup ↥Y), ⊤⁆ : Subgroup ↥Y) = ⊤ := by
    rw [← commutator_def]
    exact hY.1
  have h2 := congrArg (Subgroup.map Y.subtype) h1
  rw [Subgroup.map_commutator] at h2
  have h3 : Subgroup.map Y.subtype (⊤ : Subgroup ↥Y) = Y := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h3] at h2
  exact h2

private theorem lemma117_qs_perfect_centralizes {Y : Subgroup Q} (hY : CFSG.Open.IsQuasisimple ↥Y) {m : Q}
    (hm : ∀ y ∈ Y, ⁅m, y⁆ ∈ Y ⊓ Subgroup.centralizer (Y : Set Q)) :
    ∀ y ∈ Y, m * y = y * m := by
  have hmul : ∀ a ∈ Y, ∀ b ∈ Y, ⁅m, a * b⁆ = ⁅m, a⁆ * ⁅m, b⁆ := by
    intro a ha b hb
    have hcb := (Subgroup.mem_centralizer_iff.1 (hm b hb).2) a ha
    have hac : a * ⁅m, b⁆ * a⁻¹ = ⁅m, b⁆ := by rw [hcb]; group
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    calc m * (a * b) * m⁻¹ * (a * b)⁻¹ = (m * a * m⁻¹ * a⁻¹) * (a * (m * b * m⁻¹ * b⁻¹) * a⁻¹) := by
          group
      _ = (m * a * m⁻¹ * a⁻¹) * (m * b * m⁻¹ * b⁻¹) := by
          rw [commutatorElement_def] at hac
          rw [← commutatorElement_def, hac]
  have hinv : ∀ a ∈ Y, ⁅m, a⁻¹⁆ = ⁅m, a⁆⁻¹ := by
    intro a ha
    have h1 := hmul a ha a⁻¹ (Y.inv_mem ha)
    rw [mul_inv_cancel, commutatorElement_one_right] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hc : ⁅Y, Y⁆ ≤ Subgroup.centralizer ({m} : Set Q) := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have ha' : a * b * a⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)
    have h1 := hmul (a * b * a⁻¹) ha' b⁻¹ (Y.inv_mem hb)
    have h2 := hmul (a * b) (Y.mul_mem ha hb) a⁻¹ (Y.inv_mem ha)
    have h3 := hmul a ha b hb
    have hxz : ⁅h, a⁆ * ⁅h, b⁆ = ⁅h, b⁆ * ⁅h, a⁆ :=
      (Subgroup.mem_centralizer_iff.1 (hm b hb).2) _ (hm a ha).1
    have key : ⁅h, a * b * a⁻¹ * b⁻¹⁆ = 1 := by
      rw [h1, h2, h3, hinv a ha, hinv b hb]
      calc ⁅h, a⁆ * ⁅h, b⁆ * ⁅h, a⁆⁻¹ * ⁅h, b⁆⁻¹ = ⁅h, b⁆ * ⁅h, a⁆ * ⁅h, a⁆⁻¹ * ⁅h, b⁆⁻¹ := by
            rw [hxz]
        _ = 1 := by group
    rw [commutatorElement_def]
    exact commutatorElement_eq_one_iff_mul_comm.1 key
  intro y hy
  have hyY : y ∈ ⁅Y, Y⁆ := by rw [lemma117_qs_comm_self hY]; exact hy
  exact Subgroup.mem_centralizer_iff.1 (hc hyY) m (Set.mem_singleton m)

private def lemma117_zc (Y : Subgroup Q) : Subgroup Q := Y ⊓ Subgroup.centralizer (Y : Set Q)

private theorem lemma117_mem_zc {Y : Subgroup Q} {z : Q} : z ∈ lemma117_zc Y ↔ z ∈ Y ∧ ∀ y ∈ Y, y * z = z * y := by
  unfold lemma117_zc
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

private def lemma117_EN (H T : Subgroup Q) : Prop := ∀ h ∈ H, ∀ t ∈ T, h * t * h⁻¹ ∈ T

private theorem lemma117_en_iff_map (H T : Subgroup Q) :
    lemma117_EN H T ↔ ∀ h ∈ H, T.map (MulAut.conj h).toMonoidHom ≤ T := by
  constructor
  · intro hN h hh
    rintro _ ⟨t, ht, rfl⟩
    have := hN h hh t ht
    simpa [MulAut.conj_apply] using this
  · intro hN h hh t ht
    have := hN h hh (Subgroup.mem_map.2 ⟨t, ht, rfl⟩)
    simpa [MulAut.conj_apply] using this

private theorem lemma117_en_sup {H A B : Subgroup Q} (hA : lemma117_EN H A) (hB : lemma117_EN H B) : lemma117_EN H (A ⊔ B) := by
  rw [lemma117_en_iff_map] at hA hB ⊢
  intro h hh
  rw [Subgroup.map_sup]
  exact sup_le ((hA h hh).trans le_sup_left) ((hB h hh).trans le_sup_right)

private theorem lemma117_en_iSup {ι : Type} {H : Subgroup Q} {S : ι → Subgroup Q} (hS : ∀ j, lemma117_EN H (S j)) :
    lemma117_EN H (⨆ j, S j) := by
  rw [lemma117_en_iff_map]
  intro h hh
  rw [Subgroup.map_iSup]
  exact iSup_le fun j => ((lemma117_en_iff_map _ _).1 (hS j) h hh).trans (le_iSup S j)

private theorem lemma117_en_of_iSup {ι : Type} {S : ι → Subgroup Q} {T : Subgroup Q}
    (hS : ∀ j, lemma117_EN (S j) T) : lemma117_EN (⨆ j, S j) T := by
  intro h hh
  refine Subgroup.iSup_induction S (C := fun x => ∀ t ∈ T, x * t * x⁻¹ ∈ T) hh ?_ ?_ ?_
  · intro j x hx t ht
    exact hS j x hx t ht
  · intro t ht
    simpa using ht
  · intro x y hx hy t ht
    have e : x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
    rw [e]
    exact hx _ (hy t ht)

private theorem lemma117_qs_nontrivial {G : Type} [Group G] (h : CFSG.Open.IsQuasisimple G) : Nontrivial G := by
  haveI := h.2.toNontrivial
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  exact not_subsingleton (G ⧸ Subgroup.center G) inferInstance

private theorem lemma117_mem_sup_decomp {A B : Subgroup Q} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : Q}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  let P : Subgroup Q :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, a * b = g}
      mul_mem' := by
        rintro _ _ ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
        refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
        calc a1 * a2 * (b1 * b2) = a1 * (a2 * b1) * b2 := by group
          _ = a1 * (b1 * a2) * b2 := by rw [hc a2 ha2 b1 hb1]
          _ = a1 * b1 * (a2 * b2) := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [← hc a ha b hb] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact hle hg

private theorem lemma117_mem_of_pow_mem_coprime {S : Subgroup Q} {ℓ : ℕ} {y : Q} (hy : y ^ ℓ ∈ S)
    (hcop : Nat.Coprime ℓ (orderOf y)) : y ∈ S := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : y = (y ^ ℓ) ^ u := by
    have e : y ^ (u * (ℓ : ℤ) + v * (orderOf y : ℤ)) = y := by rw [huv, zpow_one]
    rw [zpow_add, mul_comm u (ℓ : ℤ), zpow_mul, zpow_natCast, mul_comm v (orderOf y : ℤ),
      zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one] at e
    exact e.symm
  rw [h1]
  exact S.zpow_mem hy u

private theorem lemma117_closure_core_abstract {ι κ : Type} {ℓ : ℕ} (hℓ : ℓ.Prime) (Y : ι → Subgroup Q)
    (hq : ∀ j, CFSG.Open.IsQuasisimple ↥(Y j))
    (hcomm : ∀ j j', Y j ≠ Y j' → ⁅Y j, Y j'⁆ = ⊥)
    (H : κ → Subgroup Q) (K M : Subgroup Q)
    (hH : ∀ c, H c ≤ ⨆ j, Y j)
    (hstar : ∀ c (T : Subgroup Q), (∀ h ∈ H c, ∀ t ∈ T, h * t * h⁻¹ ∈ T) → ¬ H c ≤ T →
      ∃ g ∈ H c, g ^ ℓ = 1 ∧ g ∉ T)
    (hK : ∀ T : Subgroup Q, (∀ c, H c ≤ T) → K ≤ T)
    (hKL : K ≤ ⨆ j, Y j)
    (hMK : M ≤ K) (hMn : ∀ g : Q, ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (hMo : ∀ m ∈ M, ¬ ℓ ∣ orderOf m) :
    ∀ k ∈ K, ∀ m ∈ M, k * m = m * k := by
  classical
  set L : Subgroup Q := ⨆ j, Y j with hLdef
  let R : ι → Subgroup Q := fun j => ⨆ j' : {j' : ι // Y j' ≠ Y j}, Y j'.1
  have hYY_comm : ∀ j j', Y j ≠ Y j' → ∀ y ∈ Y j, ∀ z ∈ Y j', y * z = z * y := by
    intro j j' hne y hy z hz
    have h := hcomm j' j (Ne.symm hne)
    have hz' : z ∈ Subgroup.centralizer (Y j : Set Q) := by
      have : Y j' ≤ Subgroup.centralizer (Y j : Set Q) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
      exact this hz
    exact (Subgroup.mem_centralizer_iff.1 hz') y hy
  have hR_comm : ∀ j, ∀ y ∈ Y j, ∀ r ∈ R j, y * r = r * y := by
    intro j y hy r hr
    have hle : R j ≤ Subgroup.centralizer (Y j : Set Q) := by
      refine iSup_le fun j' => ?_
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (hYY_comm j'.1 j j'.2 z hz w hw).symm
    exact (Subgroup.mem_centralizer_iff.1 (hle hr)) y hy
  have hEN_YY : ∀ j k, lemma117_EN (Y j) (Y k) := by
    intro j k h hh t ht
    by_cases hjk : Y j = Y k
    · have hh' : h ∈ Y k := hjk ▸ hh
      exact (Y k).mul_mem ((Y k).mul_mem hh' ht) ((Y k).inv_mem hh')
    · have e : h * t * h⁻¹ = t := by
        rw [hYY_comm j k hjk h hh t ht]
        group
      rw [e]
      exact ht
  have hEN_R : ∀ j k, lemma117_EN (Y j) (R k) := by
    intro j k
    exact lemma117_en_iSup (fun j' : {j' : ι // Y j' ≠ Y k} => hEN_YY j j'.1)
  have hEN_zc : ∀ j k, lemma117_EN (Y k) (lemma117_zc (Y j)) := by
    intro j k
    by_cases hjk : Y k = Y j
    · intro h hh t ht
      have hh' : h ∈ Y j := hjk ▸ hh
      rw [lemma117_mem_zc] at ht
      rw [lemma117_mem_zc]
      refine ⟨(Y j).mul_mem ((Y j).mul_mem hh' ht.1) ((Y j).inv_mem hh'), ?_⟩
      intro y hy
      have hc : h⁻¹ * y * h ∈ Y j := (Y j).mul_mem ((Y j).mul_mem ((Y j).inv_mem hh') hy) hh'
      have hct := ht.2 (h⁻¹ * y * h) hc
      calc y * (h * t * h⁻¹) = h * ((h⁻¹ * y * h) * t) * h⁻¹ := by group
        _ = h * (t * (h⁻¹ * y * h)) * h⁻¹ := by rw [hct]
        _ = h * t * h⁻¹ * y := by group
    · intro h hh t ht
      have htY : t ∈ Y j := (lemma117_mem_zc.1 ht).1
      have e : h * t * h⁻¹ = t := by
        rw [hYY_comm k j hjk h hh t htY]
        group
      rw [e]
      exact ht
  have hEN_L_R : ∀ j, lemma117_EN L (R j) := fun j => lemma117_en_of_iSup (fun k => hEN_R k j)
  have hEN_L_zc : ∀ j, lemma117_EN L (lemma117_zc (Y j)) := fun j => lemma117_en_of_iSup (fun k => hEN_zc j k)
  have hEN_L_T : ∀ j, lemma117_EN L (R j ⊔ lemma117_zc (Y j)) := fun j => lemma117_en_sup (hEN_L_R j) (hEN_L_zc j)
  have hEN_L_Y : ∀ j, lemma117_EN L (Y j) := fun j => lemma117_en_of_iSup (fun k => hEN_YY k j)
  have hL_le : ∀ j, L ≤ Y j ⊔ R j := by
    intro j
    refine iSup_le fun k => ?_
    by_cases hk : Y k = Y j
    · rw [hk]
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun j' : {j' : ι // Y j' ≠ Y j} => Y j'.1) ⟨k, hk⟩)
  have hA : ∀ j, Y j ⊓ M ≤ lemma117_zc (Y j) := by
    intro j
    have hnorm : ∀ s ∈ Y j, ∀ a ∈ Y j ⊓ M, s * a * s⁻¹ ∈ Y j ⊓ M := by
      intro s hs a ha
      exact ⟨(Y j).mul_mem ((Y j).mul_mem hs ha.1) ((Y j).inv_mem hs), hMn s a ha.2⟩
    rcases lemma117_qs_normal_dichotomy (hq j) inf_le_left hnorm with hc | hsub
    · intro a ha
      rw [lemma117_mem_zc]
      exact ⟨ha.1, fun y hy => hc a ha y hy⟩
    · exfalso
      have hYM : Y j ≤ M := fun y hy => (hsub hy).2
      have hsome : ∃ c, ¬ H c ≤ R j ⊔ lemma117_zc (Y j) := by
        by_contra hall
        push Not at hall
        have hKT : K ≤ R j ⊔ lemma117_zc (Y j) := hK _ hall
        have hYzc : Y j ≤ lemma117_zc (Y j) := by
          intro y hy
          have hyK : y ∈ K := hMK (hYM hy)
          have hyT : y ∈ lemma117_zc (Y j) ⊔ R j := by
            rw [sup_comm]
            exact hKT hyK
          obtain ⟨z, hz, r, hr, hzr⟩ := lemma117_mem_sup_decomp (A := lemma117_zc (Y j)) (B := R j)
            (fun a ha b hb => hR_comm j a (lemma117_mem_zc.1 ha).1 b hb) hyT
          have hrY : r ∈ Y j := by
            have e : r = z⁻¹ * y := by
              rw [← hzr]
              group
            rw [e]
            exact (Y j).mul_mem ((Y j).inv_mem (lemma117_mem_zc.1 hz).1) hy
          have hrz : r ∈ lemma117_zc (Y j) := by
            rw [lemma117_mem_zc]
            exact ⟨hrY, fun w hw => hR_comm j w hw r hr⟩
          rw [← hzr]
          exact (lemma117_zc (Y j)).mul_mem hz hrz
        have hcomm_bot : ⁅Y j, Y j⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          exact (lemma117_mem_zc.1 (hYzc hw)).2 y hy |>.symm
        have hbot : Y j = ⊥ := (lemma117_qs_comm_self (hq j)).symm.trans hcomm_bot
        haveI := lemma117_qs_nontrivial (hq j)
        obtain ⟨x, hx⟩ := exists_ne (1 : ↥(Y j))
        exact hx (Subtype.ext (Subgroup.mem_bot.1 (hbot.le x.2)))
      obtain ⟨c, hc⟩ := hsome
      obtain ⟨g, hgH, hgpow, hgT⟩ := hstar c (R j ⊔ lemma117_zc (Y j))
        (fun h hh t ht => hEN_L_T j h (hH c hh) t ht) hc
      have hgL : g ∈ Y j ⊔ R j := hL_le j (hH c hgH)
      obtain ⟨y, hy, r, hr, hyr⟩ := lemma117_mem_sup_decomp (A := Y j) (B := R j)
        (fun a ha b hb => hR_comm j a ha b hb) hgL
      have hcommyr : Commute y r := hR_comm j y hy r hr
      have hpow : y ^ ℓ * r ^ ℓ = 1 := by
        rw [← hcommyr.mul_pow, hyr, hgpow]
      have hyℓ : y ^ ℓ = (r ^ ℓ)⁻¹ := eq_inv_of_mul_eq_one_left hpow
      have hyℓR : y ^ ℓ ∈ R j := by
        rw [hyℓ]
        exact (R j).inv_mem ((R j).pow_mem hr ℓ)
      have hyℓlemma117_zc : y ^ ℓ ∈ lemma117_zc (Y j) := by
        rw [lemma117_mem_zc]
        exact ⟨(Y j).pow_mem hy ℓ, fun w hw => hR_comm j w hw (y ^ ℓ) hyℓR⟩
      have hyzc : y ∈ lemma117_zc (Y j) :=
        lemma117_mem_of_pow_mem_coprime hyℓlemma117_zc ((Nat.Prime.coprime_iff_not_dvd hℓ).2 (hMo y (hYM hy)))
      exact hgT (by
        rw [← hyr]
        exact (R j ⊔ lemma117_zc (Y j)).mul_mem ((le_sup_right : lemma117_zc (Y j) ≤ R j ⊔ lemma117_zc (Y j)) hyzc)
          ((le_sup_left : R j ≤ R j ⊔ lemma117_zc (Y j)) hr))
  have hB : ∀ j, ∀ m ∈ M, ∀ y ∈ Y j, m * y = y * m := by
    intro j m hm
    refine lemma117_qs_perfect_centralizes (hq j) ?_
    intro y hy
    have hmL : m ∈ L := hKL (hMK hm)
    have h1 : m * y * m⁻¹ ∈ Y j := hEN_L_Y j m hmL y hy
    have h2 : m * y * m⁻¹ * y⁻¹ ∈ Y j := (Y j).mul_mem h1 ((Y j).inv_mem hy)
    have h3 : m * y * m⁻¹ * y⁻¹ ∈ M := by
      have e : m * y * m⁻¹ * y⁻¹ = m * (y * m⁻¹ * y⁻¹) := by group
      rw [e]
      exact M.mul_mem hm (hMn y m⁻¹ (M.inv_mem hm))
    have hz : m * y * m⁻¹ * y⁻¹ ∈ lemma117_zc (Y j) := hA j ⟨h2, h3⟩
    rw [commutatorElement_def]
    exact hz
  have hLM : L ≤ Subgroup.centralizer (M : Set Q) := by
    refine iSup_le fun j => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact hB j m hm y hy
  intro k hk m hm
  have hk' : k ∈ Subgroup.centralizer (M : Set Q) := hLM (hKL hk)
  exact ((Subgroup.mem_centralizer_iff.1 hk') m hm).symm

private theorem lemma117_barX_iSup_le {p : ℕ} {Cg : Subgroup G} {ι : Type} (K : ι → Subgroup G)
    (hK : ∀ i, K i ≤ Cg) :
    barX p Cg (⨆ i, K i) ≤ ⨆ i, barX p Cg (K i) := by
  set T : Subgroup (↥Cg ⧸ GLAPPrimeCore p ↥Cg) := ⨆ i, barX p Cg (K i) with hT
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hz
  have haK : (a : G) ∈ ⨆ i, K i := Subgroup.mem_subgroupOf.1 ha
  have key : ∀ g : G, g ∈ ⨆ i, K i → ∃ hg : g ∈ Cg,
      (QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) ⟨g, hg⟩ : ↥Cg ⧸ GLAPPrimeCore p ↥Cg) ∈ T := by
    intro g hg
    refine Subgroup.iSup_induction K
      (C := fun g => ∃ hg : g ∈ Cg,
        (QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) ⟨g, hg⟩ : ↥Cg ⧸ GLAPPrimeCore p ↥Cg) ∈ T) hg ?_ ?_ ?_
    · intro i x hx
      have hxC : x ∈ Cg := hK i hx
      refine ⟨hxC, ?_⟩
      have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) ⟨x, hxC⟩ :
          ↥Cg ⧸ GLAPPrimeCore p ↥Cg) ∈ barX p Cg (K i) :=
        Subgroup.mem_map.2 ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      exact (le_iSup (fun i => barX p Cg (K i)) i) hmem
    · exact ⟨Cg.one_mem, T.one_mem⟩
    · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
      refine ⟨Cg.mul_mem hx hy, ?_⟩
      have e : (⟨x * y, Cg.mul_mem hx hy⟩ : ↥Cg) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, map_mul]
      exact T.mul_mem hx' hy'
  obtain ⟨hg, hmem⟩ := key a.1 haK
  exact hmem

private theorem lemma117_map_conj_eq_GLBConj_inv (a : G) (J : Subgroup G) :
    J.map (MulAut.conj a).toMonoidHom = GLBConj a⁻¹ J := by
  unfold GLBConj
  rw [inv_inv]

end Lemma117Closure

theorem closureCore_le_oPPrimeP (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J) (hp : p.Prime)
    (hJp : J ≤ GLAPLayer p (Subgroup.centralizer ({x'} : Set G))) :
    ⁅closureIn J (Subgroup.centralizer ({x'} : Set G)), GLAPPrimeCoreOf p' (closureIn J (Subgroup.centralizer ({x'} : Set G)))⁆ ≤
      GLAPPrimeCoreOf p (closureIn J (Subgroup.centralizer ({x'} : Set G))) := by
  classical
  set Cg : Subgroup G := Subgroup.centralizer ({x'} : Set G) with hCg
  have hp' : p'.Prime := hc.cfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact p'.Prime := ⟨hp'⟩
  have hJCg : J ≤ Cg := fun j hj => (hc.cfg.comp.1.1 hj).2
  have hJq : CFSG.Open.IsQuasisimple ↥J := hc.cfg.comp.1.2.2
  let ι := {Y : Subgroup G // GLAPComponent p Cg Y}
  let Yb : ι → Subgroup (↥Cg ⧸ GLAPPrimeCore p ↥Cg) := fun Y => barX p Cg Y.1
  have hYCg : ∀ Y : ι, Y.1 ≤ Cg := fun Y => Y.2.1
  have hlayer_le : GLAPLayer p Cg ≤ ⨆ Y : ι, Y.1 :=
    sSup_le fun L hL => le_iSup (fun Y : ι => Y.1) ⟨L, hL⟩
  have hq : ∀ Y : ι, CFSG.Open.IsQuasisimple ↥(Yb Y) := fun Y => Y.2.2.2.1.2.2
  have hcomm : ∀ Y Y' : ι, Yb Y ≠ Yb Y' → ⁅Yb Y, Yb Y'⁆ = ⊥ := fun Y Y' hne =>
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ Y.2.2.2.1 Y'.2.2.2.1 hne
  set Kg : Subgroup G := closureIn J Cg with hKg
  have hKgCg : Kg ≤ Cg := by
    refine iSup₂_le fun a ha => ?_
    rintro _ ⟨j, hj, rfl⟩
    exact Cg.mul_mem (Cg.mul_mem ha (hJCg hj)) (Cg.inv_mem ha)
  have hKgL : Kg ≤ GLAPLayer p Cg := by
    refine iSup₂_le fun a ha => ?_
    rintro _ ⟨j, hj, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (mem_normalizer_glaPLayer (Subgroup.le_normalizer ha)) j).1
      (hJp hj)
  have hKgnorm : Cg ≤ Subgroup.normalizer (Kg : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.L62.le_normalizer_closureIn J Cg
  have hKgsub : IsSubnormal Kg Cg :=
    IsSubnormal.step hKgCg ((Subgroup.normal_subgroupOf_iff_le_normalizer hKgCg).2 hKgnorm)
      (IsSubnormal.refl Cg)
  have hlayerCg : GLAPLayer p Cg ≤ Cg := sSup_le fun L hL => hL.1
  have hGLBle : ∀ c : ↥Cg, GLBConj (c : G) J ≤ GLAPLayer p Cg := by
    intro c y hy
    have hlay : (c : G) * y * (c : G)⁻¹ ∈ GLAPLayer p Cg := hJp (mem_gLBConj.1 hy)
    exact (Subgroup.mem_normalizer_iff.1 (mem_normalizer_glaPLayer (Subgroup.le_normalizer c.2)) y).2 hlay
  have hGLBCg : ∀ c : ↥Cg, GLBConj (c : G) J ≤ Cg := fun c => (hGLBle c).trans hlayerCg
  have hHle : ∀ c : ↥Cg, barX p Cg (GLBConj (c : G) J) ≤ ⨆ Y : ι, Yb Y :=
    fun c => (barX_mono p ((hGLBle c).trans hlayer_le)).trans (lemma117_barX_iSup_le (fun Y : ι => Y.1) hYCg)
  have hKL : barX p Cg Kg ≤ ⨆ Y : ι, Yb Y :=
    (barX_mono p (hKgL.trans hlayer_le)).trans (lemma117_barX_iSup_le (fun Y : ι => Y.1) hYCg)
  have hKle : Kg ≤ ⨆ c : ↥Cg, GLBConj (c : G) J := by
    rw [hKg]
    refine iSup₂_le fun a ha => ?_
    rw [lemma117_map_conj_eq_GLBConj_inv]
    exact le_iSup (fun c : ↥Cg => GLBConj (c : G) J) ⟨a⁻¹, Cg.inv_mem ha⟩
  have hK : ∀ T : Subgroup (↥Cg ⧸ GLAPPrimeCore p ↥Cg),
      (∀ c : ↥Cg, barX p Cg (GLBConj (c : G) J) ≤ T) → barX p Cg Kg ≤ T := by
    intro T hT
    refine (barX_mono p hKle).trans ((lemma117_barX_iSup_le (fun c : ↥Cg => GLBConj (c : G) J) hGLBCg).trans ?_)
    exact iSup_le fun c => hT c
  set N : Subgroup G := GLAPPrimeCoreOf p' Kg with hN
  have hNKg : N ≤ Kg := Subgroup.map_subtype_le _
  have hNCg : Cg ≤ Subgroup.normalizer (N : Set G) :=
    hKgnorm.trans (normalizer_le_normalizer_glaPPrimeCoreOf p' Kg)
  set Mb : Subgroup (↥Cg ⧸ GLAPPrimeCore p ↥Cg) := barX p Cg N with hMb
  have hMK : Mb ≤ barX p Cg Kg := barX_mono p hNKg
  have hMn : ∀ g : (↥Cg ⧸ GLAPPrimeCore p ↥Cg), ∀ m ∈ Mb, g * m * g⁻¹ ∈ Mb := by
    intro g m hm
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥Cg) g
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hm
    have e : (QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) c) *
        QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) n *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) c)⁻¹ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) (c * n * c⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    refine Subgroup.mem_map.2 ⟨c * n * c⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.1 hn
    have := (Subgroup.mem_normalizer_iff.1 (hNCg c.2) (n : G)).1 hnN
    simpa using this
  have hMo : ∀ m ∈ Mb, ¬ p' ∣ orderOf m := by
    intro m hm hdiv
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hm
    have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.1 hn
    have h1 : orderOf (QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) n) ∣ orderOf n :=
      orderOf_map_dvd _ n
    have h2 : orderOf (n : G) ∣ Nat.card ↥N := by
      have := orderOf_dvd_natCard (⟨(n : G), hnN⟩ : ↥N)
      rwa [Subgroup.orderOf_mk] at this
    have h3 : p' ∣ orderOf n := hdiv.trans h1
    rw [← Subgroup.orderOf_coe] at h3
    exact not_dvd_card_glaPPrimeCoreOf hp' Kg (h3.trans h2)
  have hstar : ∀ c : ↥Cg, ∀ T : Subgroup (↥Cg ⧸ GLAPPrimeCore p ↥Cg),
      (∀ h ∈ barX p Cg (GLBConj (c : G) J), ∀ t ∈ T, h * t * h⁻¹ ∈ T) →
      ¬ barX p Cg (GLBConj (c : G) J) ≤ T →
      ∃ g ∈ barX p Cg (GLBConj (c : G) J), g ^ p' = 1 ∧ g ∉ T := by
    intro c T hTn hnot
    set S : Subgroup ↥Cg := (GLBConj (c : G) J).subgroupOf Cg with hS
    have hcardJ : Nat.card ↥(GLBConj (c : G) J) = Nat.card ↥J :=
      Nat.card_congr (Subgroup.equivMapOfInjective J _ (MulAut.conj (c : G)⁻¹).injective).symm.toEquiv
    have hGq : CFSG.Open.IsQuasisimple ↥(GLBConj (c : G) J) :=
      CFSG.Open.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective J _ (MulAut.conj (c : G)⁻¹).injective).symm hJq
    have hSq : CFSG.Open.IsQuasisimple ↥S :=
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hGLBCg c)) hGq
    have hSdvd : p' ∣ Nat.card ↥S := by
      have h1 : p' ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := (dvd_mul_left p' p).trans hc.cfg.dvd
      have h2 : p' ∣ Nat.card ↥J := h1.trans (Subgroup.card_quotient_dvd_card _)
      have h3 : Nat.card ↥S = Nat.card ↥(GLBConj (c : G) J) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hGLBCg c)).toEquiv
      rw [h3, hcardJ]
      exact h2
    set Tc : Subgroup ↥Cg := T.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥Cg)) with hTc
    have hnormA : ∀ s ∈ S, ∀ a ∈ Tc ⊓ S, s * a * s⁻¹ ∈ Tc ⊓ S := by
      intro s hs a ha
      refine ⟨?_, S.mul_mem (S.mul_mem hs ha.2) (S.inv_mem hs)⟩
      have hπs : QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) s ∈ barX p Cg (GLBConj (c : G) J) :=
        Subgroup.mem_map.2 ⟨s, hs, rfl⟩
      have h1 := hTn _ hπs _ ha.1
      show QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) (s * a * s⁻¹) ∈ T
      rw [map_mul, map_mul, map_inv]
      exact h1
    rcases lemma117_qs_normal_dichotomy hSq inf_le_right hnormA with hcent | hsub
    · obtain ⟨g', hg'ord, hg'nc⟩ :=
        CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
          hSq hp' hc.cfg.odd hSdvd
      refine ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) (g' : ↥Cg),
        Subgroup.mem_map.2 ⟨(g' : ↥Cg), g'.2, rfl⟩, ?_, ?_⟩
      · rw [← map_pow]
        have hpow : ((g' : ↥S) : ↥Cg) ^ p' = 1 := by
          have h := pow_orderOf_eq_one g'
          rw [hg'ord] at h
          have := congrArg (fun z : ↥S => (z : ↥Cg)) h
          simpa using this
        rw [hpow, map_one]
      · intro hT
        apply hg'nc
        rw [Subgroup.mem_center_iff]
        intro s
        exact Subtype.ext (hcent _ ⟨hT, g'.2⟩ _ s.2)
    · exfalso
      apply hnot
      show S.map (QuotientGroup.mk' (GLAPPrimeCore p ↥Cg)) ≤ T
      rw [Subgroup.map_le_iff_le_comap]
      intro s hs
      exact (hsub hs).1
  have hmain := lemma117_closure_core_abstract hp' (fun Y : ι => Yb Y) hq hcomm
    (fun c : ↥Cg => barX p Cg (GLBConj (c : G) J)) (barX p Cg Kg) Mb hHle hstar hK hKL hMK hMn hMo
  refine Subgroup.commutator_le.2 fun k hk n hn => ?_
  have hkC : k ∈ Cg := hKgCg hk
  have hnC : n ∈ Cg := hKgCg (hNKg hn)
  have hkK : QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) (⟨k, hkC⟩ : ↥Cg) ∈ barX p Cg Kg :=
    Subgroup.mem_map.2 ⟨⟨k, hkC⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
  have hnM : QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) (⟨n, hnC⟩ : ↥Cg) ∈ Mb :=
    Subgroup.mem_map.2 ⟨⟨n, hnC⟩, Subgroup.mem_subgroupOf.2 hn, rfl⟩
  have hcomm_q := hmain _ hkK _ hnM
  have hw : (QuotientGroup.mk' (GLAPPrimeCore p ↥Cg) ⁅(⟨k, hkC⟩ : ↥Cg), ⟨n, hnC⟩⁆ :
      ↥Cg ⧸ GLAPPrimeCore p ↥Cg) = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hcomm_q
  have hwcore : ⁅(⟨k, hkC⟩ : ↥Cg), ⟨n, hnC⟩⁆ ∈ GLAPPrimeCore p ↥Cg := (QuotientGroup.eq_one_iff _).1 hw
  have hcoreC : ⁅k, n⁆ ∈ GLAPPrimeCoreOf p Cg :=
    Subgroup.mem_map.2 ⟨_, hwcore, rfl⟩
  have hkn_Kg : ⁅k, n⁆ ∈ Kg := by
    rw [commutatorElement_def]
    have e : k * n * k⁻¹ * n⁻¹ = k * (n * k⁻¹ * n⁻¹) := by group
    rw [e]
    exact Kg.mul_mem hk ((Subgroup.mem_normalizer_iff.1 (hKgnorm hnC) k⁻¹).1 (Kg.inv_mem hk))
  have hfin : ⁅k, n⁆ ∈ Kg ⊓ GLAPPrimeCoreOf p Cg := ⟨hkn_Kg, hcoreC⟩
  rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hKgsub] at hfin
  exact hfin

theorem j_isComponent_cent (hsf : StageFacts G m) (hR : RQuad G m p B x L) (hc : Cfg116 G m p L p' B' x' J) :
    IsComponentOf J (Subgroup.centralizer ({x'} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hH := rquad_hyp hsf hR
  obtain ⟨-, hJsub, hJq⟩ := hc.cfg.comp.1
  have h1 : IsSubnormal (L ⊓ Subgroup.centralizer ({x'} : Set G))
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({x'} : Set G)) := hH.comp.2.1.inf _
  have h2 := hJsub.trans h1
  rw [inf_comm] at h2
  exact ⟨h2.le, h2, hJq⟩

private theorem lemma117_diag_sup_decomp_norm {Q : Type} [Group Q] {A B : Subgroup Q} (hn : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B)
    {g : Q} (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  let P : Subgroup Q :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, a * b = g}
      mul_mem' := by
        rintro _ _ ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
        refine ⟨a1 * a2, A.mul_mem ha1 ha2, a2⁻¹ * b1 * a2 * b2, ?_, ?_⟩
        · refine B.mul_mem ?_ hb2
          have := hn a2⁻¹ (A.inv_mem ha2) b1 hb1
          simpa [mul_assoc] using this
        · group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, hn a ha b⁻¹ (B.inv_mem hb), ?_⟩
        group }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact hle hg


theorem y10xA_cn {Γ : Type} [Group Γ] [Finite Γ] {A K N : Subgroup Γ}
    (hK : IsComponentOf K A) (hNA : N ≤ A) (hAN : A ≤ Subgroup.normalizer (N : Set Γ)) :
    K ≤ N ∨ ⁅K, N⁆ = ⊥ := by
  have hNn : (N.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mpr hAN
  have hA : CFSG.Assembly.IsComponentOf K A := CFSG.Assembly.isComponentOf_iff_open.2 hK
  have hK' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hK.1).1 hA
  rcases CFSG.LocalCores.component_normal_subgroup hK' hNn with h | h
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hK.1 h)
  · right
    have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hK.1 h
    rwa [inf_of_le_left hNA] at h1

theorem y10xA_qs_comm_self {Q : Type} [Group Q] {Y : Subgroup Q}
    (hY : CFSG.Open.IsQuasisimple ↥Y) : ⁅Y, Y⁆ = Y := by
  have h1 : (⁅(⊤ : Subgroup ↥Y), ⊤⁆ : Subgroup ↥Y) = ⊤ := by
    rw [← commutator_def]
    exact hY.1
  have h2 := congrArg (Subgroup.map Y.subtype) h1
  rw [Subgroup.map_commutator] at h2
  have h3 : Subgroup.map Y.subtype (⊤ : Subgroup ↥Y) = Y := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h3] at h2
  exact h2

theorem y10xA_qs_ne_bot {Q : Type} [Group Q] {Y : Subgroup Q}
    (hY : CFSG.Open.IsQuasisimple ↥Y) : Y ≠ ⊥ := by
  intro h
  have hnt : Nontrivial (↥Y ⧸ Subgroup.center ↥Y) := hY.2.toNontrivial
  subst h
  obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (congrArg QuotientGroup.mk
    (Subtype.ext ((Subgroup.mem_bot.1 a'.2).trans (Subgroup.mem_bot.1 b'.2).symm)))

def y10xA_Commute {Q : Type} [Group Q] (A B : Subgroup Q) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, a * b = b * a

theorem y10xA_commute_of_bot {Q : Type} [Group Q] {A B : Subgroup Q} (h : ⁅A, B⁆ = ⊥) :
    y10xA_Commute A B := by
  intro a ha b hb
  have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h ha
  rw [Subgroup.mem_centralizer_iff] at h1
  exact (h1 b hb).symm

theorem y10xA_bot_of_commute {Q : Type} [Group Q] {A B : Subgroup Q}
    (h : y10xA_Commute A B) : ⁅A, B⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (h a ha b hb).symm

theorem y10xA_commute_iSup {Q : Type} [Group Q] {ι κ : Type} (A : ι → Subgroup Q)
    (B : κ → Subgroup Q) (h : ∀ i j, y10xA_Commute (A i) (B j)) :
    y10xA_Commute (⨆ i, A i) (⨆ j, B j) := by
  have key : ∀ a ∈ ⨆ i, A i, ∀ b ∈ ⨆ j, B j, a * b = b * a := by
    intro a ha
    refine Subgroup.iSup_induction A (C := fun a => ∀ b ∈ ⨆ j, B j, a * b = b * a) ha ?_ ?_ ?_
    · intro i a ha b hb
      refine Subgroup.iSup_induction B (C := fun b => a * b = b * a) hb ?_ ?_ ?_
      · intro j b hb
        exact h i j a ha b hb
      · simp
      · intro b₁ b₂ h₁ h₂
        rw [← mul_assoc, h₁, mul_assoc, h₂, mul_assoc]
    · intro b _
      simp
    · intro a₁ a₂ h₁ h₂ b hb
      rw [mul_assoc, h₂ b hb, ← mul_assoc, h₁ b hb, mul_assoc]
  exact key

theorem y10xA_mem_sup_of_commute {Q : Type} [Group Q] {A B : Subgroup Q}
    (h : y10xA_Commute A B) {x : Q} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let T : Subgroup Q :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, a * b = g}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
          _ = a₁ * (b₁ * a₂) * b₂ := by rw [h a₂ ha₂ b₁ hb₁]
          _ = a₁ * b₁ * (a₂ * b₂) := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hc : a * b = b * a := h a ha b hb
        have : (a * b)⁻¹ = (b * a)⁻¹ := by rw [hc]
        simpa [mul_inv_rev] using this.symm }
  have hle : A ⊔ B ≤ T := by
    refine sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩) ?_
    intro b hb
    exact ⟨1, A.one_mem, b, hb, one_mul b⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hle hx
  exact ⟨a, ha, b, hb, hab⟩

theorem y10xA_le_of_perfect {Q : Type} [Group Q] {W V T : Subgroup Q}
    (hWT : ∀ t ∈ T, ∀ w ∈ W, t * w * t⁻¹ ∈ W) (hVT : ∀ v ∈ V, ∀ t ∈ T, v * t = t * v)
    (hWV : y10xA_Commute W V) (hTWV : T ≤ W ⊔ V) (hT : ⁅T, T⁆ = T) : T ≤ W := by
  have hcomm : ⁅T, T⁆ ≤ W := by
    refine Subgroup.commutator_le.2 fun t ht t' ht' => ?_
    obtain ⟨w, hw, v, hv, rfl⟩ := y10xA_mem_sup_of_commute hWV (hTWV ht)
    have hvt : v * t' * v⁻¹ = t' := by
      rw [hVT v hv t' ht']
      group
    have e : w * v * t' * (w * v)⁻¹ * t'⁻¹ = w * (t' * w⁻¹ * t'⁻¹) := by
      calc w * v * t' * (w * v)⁻¹ * t'⁻¹ = w * (v * t' * v⁻¹) * w⁻¹ * t'⁻¹ := by group
        _ = w * t' * w⁻¹ * t'⁻¹ := by rw [hvt]
        _ = w * (t' * w⁻¹ * t'⁻¹) := by group
    rw [commutatorElement_def, e]
    exact W.mul_mem hw (hWT t' ht' w⁻¹ (W.inv_mem hw))
  rw [← hT]
  exact hcomm

theorem y10xA_commute_of_perfect {Q : Type} [Group Q] {A B Z : Subgroup Q} (hA : ⁅A, A⁆ = A)
    (hZ : ∀ z ∈ Z, ∀ g ∈ A ⊔ B, g * z = z * g) (hZZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z)
    (hc : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ Z) : y10xA_Commute A B := by
  intro a ha b hb
  have hmul : ∀ a ∈ A, ∀ a' ∈ A, ⁅a * a', b⁆ = ⁅a', b⁆ * ⁅a, b⁆ := by
    intro a ha a' ha'
    have hz : a * ⁅a', b⁆ = ⁅a', b⁆ * a := hZ _ (hc a' ha' b hb) a (Subgroup.mem_sup_left ha)
    have e : ⁅a * a', b⁆ = a * ⁅a', b⁆ * a⁻¹ * ⁅a, b⁆ := by
      rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
      group
    rw [e, hz]
    group
  have hinv : ∀ a ∈ A, ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
    intro a ha
    have h1 := hmul a⁻¹ (A.inv_mem ha) a ha
    rw [inv_mul_cancel, commutatorElement_one_left] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have key : ∀ a1 ∈ A, ∀ a2 ∈ A, ⁅⁅a1, a2⁆, b⁆ = 1 := by
    intro a1 ha1 a2 ha2
    have hcE : ⁅a1, a2⁆ = a1 * (a2 * a1⁻¹ * a2⁻¹) := by
      rw [commutatorElement_def]
      group
    have hA1 : a2 * a1⁻¹ * a2⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem ha2 (A.inv_mem ha1)) (A.inv_mem ha2)
    have hA2 : a2 * a1⁻¹ ∈ A := A.mul_mem ha2 (A.inv_mem ha1)
    have hA3 : a2⁻¹ ∈ A := A.inv_mem ha2
    have hx1 := hc a1 ha1 b hb
    have hx2 := hc a2 ha2 b hb
    have hcomm12 : Commute ⁅a1, b⁆ ⁅a2, b⁆ := hZZ _ hx1 _ hx2
    have h3 := (Commute.inv_left hcomm12).eq
    rw [hcE, hmul a1 ha1 _ hA1, hmul (a2 * a1⁻¹) hA2 a2⁻¹ hA3, hmul a2 ha2 a1⁻¹ (A.inv_mem ha1),
      hinv a2 ha2, hinv a1 ha1, h3]
    group
  have hsub : ⁅A, A⁆ ≤ A ⊓ Subgroup.centralizer ({b} : Set Q) := by
    refine Subgroup.commutator_le.2 fun a1 ha1 a2 ha2 => ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem ha1 ha2) (A.inv_mem ha1)) (A.inv_mem ha2)
    · refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (commutatorElement_eq_one_iff_mul_comm.1 (key a1 ha1 a2 ha2)).symm
  have hmem : a ∈ A ⊓ Subgroup.centralizer ({b} : Set Q) := hsub (by rw [hA]; exact ha)
  exact ((Subgroup.mem_centralizer_iff.1 hmem.2) b (Set.mem_singleton b)).symm

theorem y10xA_normalizes_sup {Γ : Type} [Group Γ] {κ : Type} (Z : κ → Subgroup Γ)
    (M : Subgroup Γ) (h : ∀ k, Z k ≤ M ∨ ∀ m ∈ M, ∀ z ∈ Z k, z * m = m * z) :
    ∀ g ∈ ⨆ k, Z k, ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
  intro g hg
  refine Subgroup.iSup_induction Z (C := fun g => ∀ m ∈ M, g * m * g⁻¹ ∈ M) hg ?_ ?_ ?_
  · intro k x hx m hm
    rcases h k with hle | hcm
    · exact M.mul_mem (M.mul_mem (hle hx) hm) (M.inv_mem (hle hx))
    · have e : x * m * x⁻¹ = m := by
        rw [hcm m hm x hx]
        group
      rw [e]
      exact hm
  · intro m hm
    simpa using hm
  · intro x y hx hy m hm
    have e : x * y * m * (x * y)⁻¹ = x * (y * m * y⁻¹) * x⁻¹ := by group
    rw [e]
    exact hx _ (hy m hm)

theorem y10xA_le_normalizer {Γ : Type} [Group Γ] {H N : Subgroup Γ}
    (h : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : H ≤ Subgroup.normalizer (N : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact h g hg n hn
  · intro hn
    have := h g⁻¹ (H.inv_mem hg) _ hn
    simpa [mul_assoc] using this

theorem y10xA_inv_eq_pow {Γ : Type} [Group Γ] {σ : Γ} {k : ℕ} (hk : 0 < k) (hσk : σ ^ k = 1) :
    σ⁻¹ = σ ^ (k - 1) := by
  have h1 : σ * σ ^ (k - 1) = 1 := by
    rw [← pow_succ']
    rw [Nat.sub_add_cancel hk]
    exact hσk
  exact eq_inv_of_mul_eq_one_right h1 ▸ rfl


theorem y10xA_map_conj_map {Γ : Type} [Group Γ] (H : Subgroup Γ) (a b : Γ) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem y10xA_iSup_centralizes {Γ : Type} [Group Γ] {κ : Type} (Z : κ → Subgroup Γ) (y : Γ)
    (h : ∀ k, ∀ z ∈ Z k, z * y = y * z) : ∀ m ∈ ⨆ k, Z k, m * y = y * m := by
  intro m hm
  refine Subgroup.iSup_induction Z (C := fun m => m * y = y * m) hm ?_ ?_ ?_
  · intro k x hx
    exact h k x hx
  · simp
  · intro x₁ x₂ h₁ h₂
    rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc]

theorem y10xA_comm_prod {Γ : Type} [Group Γ] {a b c d : Γ} (hbc : Commute b c)
    (had : Commute a d) (hXa : Commute (b * d * b⁻¹ * d⁻¹) a)
    (hXc : Commute (b * d * b⁻¹ * d⁻¹) c) :
    ⁅a * b, c * d⁆ = ⁅a, c⁆ * ⁅b, d⁆ := by
  have hda : a⁻¹ * d⁻¹ = d⁻¹ * a⁻¹ := had.inv_inv.eq
  have hX2 : Commute (b * d * b⁻¹ * d⁻¹) (a⁻¹ * c⁻¹) :=
    (hXa.inv_right).mul_right (hXc.inv_right)
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
  calc a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹
      = a * (b * c) * d * b⁻¹ * (a⁻¹ * d⁻¹) * c⁻¹ := by group
    _ = a * (c * b) * d * b⁻¹ * (d⁻¹ * a⁻¹) * c⁻¹ := by rw [hbc.eq, hda]
    _ = a * c * ((b * d * b⁻¹ * d⁻¹) * (a⁻¹ * c⁻¹)) := by group
    _ = a * c * ((a⁻¹ * c⁻¹) * (b * d * b⁻¹ * d⁻¹)) := by rw [hX2.eq]
    _ = a * c * a⁻¹ * c⁻¹ * (b * d * b⁻¹ * d⁻¹) := by group

theorem y10xA_comm_central {Γ : Type} [Group Γ] {a b z w : Γ} (hza : Commute z a)
    (hzb : Commute z b) (hwa : Commute w a) (hwb : Commute w b) (hzw : Commute z w) :
    ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hzwz : z * w * z⁻¹ = w := by
    rw [hzw.eq]
    group
  have hwa' : w * a⁻¹ = a⁻¹ * w := (hwa.inv_right).eq
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzb.eq]
    _ = a * b * (z * w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * w * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzwz]
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hwa']
    _ = a * b * a⁻¹ * b⁻¹ := by group


theorem y10xA_single_orbit {Γ : Type} [Group Γ] [Finite Γ] {ι : Type} (Y : ι → Subgroup Γ)
    (σ : Γ) (k : ℕ) (hk : 0 < k) (hσk : σ ^ k = 1) (Ĵ : Subgroup Γ)
    (hcomm : ∀ i j, Y i ≠ Y j → ⁅Y i, Y j⁆ = ⊥)
    (hσ : ∀ i, ∃ j, (Y i).map (MulAut.conj σ).toMonoidHom = Y j)
    (hĴ : IsComponentOf Ĵ ((⨆ i, Y i) ⊓ Subgroup.centralizer ({σ} : Set Γ))) :
    ∃ i₀ : ι, (∀ j, (∃ g ∈ Ĵ, ∃ y ∈ Y j, g * y ≠ y * g) → ∃ n : ℕ,
        Y j = (Y i₀).map (MulAut.conj (σ ^ n)).toMonoidHom) ∧
      Ĵ ≤ ⨆ n : ℕ, (Y i₀).map (MulAut.conj (σ ^ n)).toMonoidHom := by
  classical
  have hĴc := hĴ
  obtain ⟨hĴH, -, hqs⟩ := hĴ
  have hĴQ : Ĵ ≤ ⨆ i, Y i := hĴH.trans inf_le_left
  have hĴC : ∀ g ∈ Ĵ, σ * g = g * σ := fun g hg =>
    (Subgroup.mem_centralizer_iff.1 (hĴH hg).2) σ (Set.mem_singleton σ)
  have hperf : ⁅Ĵ, Ĵ⁆ = Ĵ := y10xA_qs_comm_self hqs
  have hne : Ĵ ≠ ⊥ := y10xA_qs_ne_bot hqs
  have hσinv : σ⁻¹ = σ ^ (k - 1) := y10xA_inv_eq_pow hk hσk
  let 𝒞 : ι → Prop := fun j => ∃ g ∈ Ĵ, ∃ y ∈ Y j, g * y ≠ y * g
  have h𝒞bot : ∀ j, ¬ 𝒞 j → ⁅Ĵ, Y j⁆ = ⊥ := by
    intro j hj
    apply y10xA_bot_of_commute
    intro g hg y hy
    by_contra hne'
    exact hj ⟨g, hg, y, hy, hne'⟩
  have h𝒞e : ∀ i j, Y i = Y j → (𝒞 i ↔ 𝒞 j) := by
    intro i j h
    simp only [𝒞, h]
  let W : Subgroup Γ := ⨆ (j : {j // 𝒞 j}), Y j.1
  let V : Subgroup Γ := ⨆ (j : {j // ¬ 𝒞 j}), Y j.1
  have hWV : y10xA_Commute W V := by
    refine y10xA_commute_iSup (fun j : {j // 𝒞 j} => Y j.1) (fun j : {j // ¬ 𝒞 j} => Y j.1)
      (fun i j => y10xA_commute_of_bot (hcomm _ _ ?_))
    intro he
    exact j.2 ((h𝒞e _ _ he).1 i.2)
  have hVT : ∀ v ∈ V, ∀ t ∈ Ĵ, v * t = t * v := by
    have hV : V ≤ Subgroup.centralizer (Ĵ : Set Γ) := by
      refine iSup_le fun j => ?_
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact y10xA_commute_of_bot (h𝒞bot j.1 j.2) t ht y hy
    intro v hv t ht
    exact ((Subgroup.mem_centralizer_iff.1 (hV hv)) t ht).symm
  have hYW : ∀ k, Y k ≤ W ∨ ∀ m ∈ W, ∀ z ∈ Y k, z * m = m * z := by
    intro k
    by_cases hk' : 𝒞 k
    · exact Or.inl (le_iSup (fun j : {j // 𝒞 j} => Y j.1) ⟨k, hk'⟩)
    · right
      intro m hm z hz
      have hzV : z ∈ V := le_iSup (fun j : {j // ¬ 𝒞 j} => Y j.1) ⟨k, hk'⟩ hz
      exact (hWV m hm z hzV).symm
  have hWnorm : ∀ g ∈ ⨆ i, Y i, ∀ m ∈ W, g * m * g⁻¹ ∈ W :=
    y10xA_normalizes_sup Y W hYW
  have hĴW : Ĵ ≤ W := by
    refine y10xA_le_of_perfect (fun t ht w hw => hWnorm t (hĴQ ht) w hw) hVT hWV ?_ hperf
    refine le_trans hĴQ (iSup_le fun i => ?_)
    by_cases hi : 𝒞 i
    · exact le_sup_of_le_left (le_iSup (fun j : {j // 𝒞 j} => Y j.1) ⟨i, hi⟩)
    · exact le_sup_of_le_right (le_iSup (fun j : {j // ¬ 𝒞 j} => Y j.1) ⟨i, hi⟩)
  obtain ⟨j₁, hj₁⟩ : ∃ j, 𝒞 j := by
    by_contra hno
    push_neg at hno
    apply hne
    rw [← le_bot_iff]
    refine le_trans hĴW (iSup_le fun j => ?_)
    exact (hno j.1 j.2).elim
  let P₁ : ι → Prop := fun j => ∃ n : ℕ, Y j = (Y j₁).map (MulAut.conj (σ ^ n)).toMonoidHom
  have hPe : ∀ i j, Y i = Y j → (P₁ i ↔ P₁ j) := by
    intro i j h
    simp only [P₁, h]
  let M₁ : Subgroup Γ := ⨆ (j : {j // 𝒞 j ∧ P₁ j}), Y j.1
  let M₂ : Subgroup Γ := ⨆ (j : {j // 𝒞 j ∧ ¬ P₁ j}), Y j.1
  have hM₁W : M₁ ≤ W := iSup_le fun j => le_iSup (fun j : {j // 𝒞 j} => Y j.1) ⟨j.1, j.2.1⟩
  have hM₂W : M₂ ≤ W := iSup_le fun j => le_iSup (fun j : {j // 𝒞 j} => Y j.1) ⟨j.1, j.2.1⟩
  have hW_le : W ≤ M₁ ⊔ M₂ := by
    refine iSup_le fun j => ?_
    by_cases hp : P₁ j.1
    · exact le_sup_of_le_left (le_iSup (fun j : {j // 𝒞 j ∧ P₁ j} => Y j.1) ⟨j.1, j.2, hp⟩)
    · exact le_sup_of_le_right (le_iSup (fun j : {j // 𝒞 j ∧ ¬ P₁ j} => Y j.1) ⟨j.1, j.2, hp⟩)
  have hM₁M₂ : y10xA_Commute M₁ M₂ := by
    refine y10xA_commute_iSup (fun j : {j // 𝒞 j ∧ P₁ j} => Y j.1)
      (fun j : {j // 𝒞 j ∧ ¬ P₁ j} => Y j.1) (fun i j => y10xA_commute_of_bot (hcomm _ _ ?_))
    intro he
    exact j.2.2 ((hPe _ _ he).1 i.2.2)
  let τ : ι → ι := fun j => (hσ j).choose
  have hτ : ∀ j, (Y j).map (MulAut.conj σ).toMonoidHom = Y (τ j) := fun j => (hσ j).choose_spec
  have hconjmem : ∀ j, ∀ x ∈ Y j, σ * x * σ⁻¹ ∈ Y (τ j) := by
    intro j x hx
    rw [← hτ j]
    exact Subgroup.mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hgσ : ∀ g ∈ Ĵ, σ⁻¹ * g * σ = g := by
    intro g hg
    calc σ⁻¹ * g * σ = σ⁻¹ * (g * σ) := by group
      _ = σ⁻¹ * (σ * g) := by rw [← hĴC g hg]
      _ = g := by group
  have h𝒞τ : ∀ j, 𝒞 j → 𝒞 (τ j) := by
    rintro j ⟨g, hg, y, hy, hgy⟩
    refine ⟨g, hg, σ * y * σ⁻¹, hconjmem j y hy, ?_⟩
    intro hcon
    apply hgy
    have e1 : σ⁻¹ * (g * (σ * y * σ⁻¹)) * σ = g * y := by
      calc σ⁻¹ * (g * (σ * y * σ⁻¹)) * σ = (σ⁻¹ * g * σ) * y := by group
        _ = g * y := by rw [hgσ g hg]
    have e2 : σ⁻¹ * (σ * y * σ⁻¹ * g) * σ = y * g := by
      calc σ⁻¹ * (σ * y * σ⁻¹ * g) * σ = y * (σ⁻¹ * g * σ) := by group
        _ = y * g := by rw [hgσ g hg]
    exact e1.symm.trans ((congrArg (fun z => σ⁻¹ * z * σ) hcon).trans e2)
  have hP₁τ : ∀ j, P₁ j → P₁ (τ j) := by
    rintro j ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [← hτ j, hn, y10xA_map_conj_map, pow_succ']
  have hP₁back : ∀ j, P₁ (τ j) → P₁ j := by
    rintro j ⟨n, hn⟩
    refine ⟨k - 1 + n, ?_⟩
    have hYj : Y j = ((Y j).map (MulAut.conj σ).toMonoidHom).map (MulAut.conj σ⁻¹).toMonoidHom := by
      rw [y10xA_map_conj_map]
      have hid : (MulAut.conj (σ⁻¹ * σ)).toMonoidHom = MonoidHom.id Γ := by
        ext x
        simp [MulAut.conj_apply]
      rw [hid, Subgroup.map_id]
    rw [hYj, hτ j, hn, y10xA_map_conj_map, hσinv, pow_add]
  have hσM₁ : ∀ m ∈ M₁, σ * m * σ⁻¹ ∈ M₁ := by
    intro m hm
    refine Subgroup.iSup_induction (fun j : {j // 𝒞 j ∧ P₁ j} => Y j.1)
      (C := fun m => σ * m * σ⁻¹ ∈ M₁) hm ?_ ?_ ?_
    · intro j x hx
      exact le_iSup (fun j : {j // 𝒞 j ∧ P₁ j} => Y j.1) ⟨τ j.1, h𝒞τ _ j.2.1, hP₁τ _ j.2.2⟩
        (hconjmem j.1 x hx)
    · simp
    · intro x y hx hy
      have e : σ * (x * y) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * y * σ⁻¹) := by group
      rw [e]
      exact M₁.mul_mem hx hy
  have hσM₂ : ∀ m ∈ M₂, σ * m * σ⁻¹ ∈ M₂ := by
    intro m hm
    refine Subgroup.iSup_induction (fun j : {j // 𝒞 j ∧ ¬ P₁ j} => Y j.1)
      (C := fun m => σ * m * σ⁻¹ ∈ M₂) hm ?_ ?_ ?_
    · intro j x hx
      have hnp : ¬ P₁ (τ j.1) := fun h => j.2.2 (hP₁back _ h)
      exact le_iSup (fun j : {j // 𝒞 j ∧ ¬ P₁ j} => Y j.1) ⟨τ j.1, h𝒞τ _ j.2.1, hnp⟩
        (hconjmem j.1 x hx)
    · simp
    · intro x y hx hy
      have e : σ * (x * y) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * y * σ⁻¹) := by group
      rw [e]
      exact M₂.mul_mem hx hy
  have hM₁norm : ∀ g ∈ ⨆ i, Y i, ∀ m ∈ M₁, g * m * g⁻¹ ∈ M₁ := by
    refine y10xA_normalizes_sup Y M₁ (fun k => ?_)
    by_cases hk1 : 𝒞 k ∧ P₁ k
    · exact Or.inl (le_iSup (fun j : {j // 𝒞 j ∧ P₁ j} => Y j.1) ⟨k, hk1⟩)
    · right
      intro m hm z hz
      by_cases hk2 : 𝒞 k
      · have hnp : ¬ P₁ k := fun h => hk1 ⟨hk2, h⟩
        have hzM₂ : z ∈ M₂ := le_iSup (fun j : {j // 𝒞 j ∧ ¬ P₁ j} => Y j.1) ⟨k, hk2, hnp⟩ hz
        exact (hM₁M₂ m hm z hzM₂).symm
      · have hzV : z ∈ V := le_iSup (fun j : {j // ¬ 𝒞 j} => Y j.1) ⟨k, hk2⟩ hz
        exact (hWV m (hM₁W hm) z hzV).symm
  have hM₂norm : ∀ g ∈ ⨆ i, Y i, ∀ m ∈ M₂, g * m * g⁻¹ ∈ M₂ := by
    refine y10xA_normalizes_sup Y M₂ (fun k => ?_)
    by_cases hk1 : 𝒞 k ∧ ¬ P₁ k
    · exact Or.inl (le_iSup (fun j : {j // 𝒞 j ∧ ¬ P₁ j} => Y j.1) ⟨k, hk1⟩)
    · right
      intro m hm z hz
      by_cases hk2 : 𝒞 k
      · have hp : P₁ k := by
          by_contra hp
          exact hk1 ⟨hk2, hp⟩
        have hzM₁ : z ∈ M₁ := le_iSup (fun j : {j // 𝒞 j ∧ P₁ j} => Y j.1) ⟨k, hk2, hp⟩ hz
        exact hM₁M₂ z hzM₁ m hm
      · have hzV : z ∈ V := le_iSup (fun j : {j // ¬ 𝒞 j} => Y j.1) ⟨k, hk2⟩ hz
        exact (hWV m (hM₂W hm) z hzV).symm
  have hM₁Q : M₁ ≤ ⨆ i, Y i := iSup_le fun j => le_iSup Y j.1
  have hM₂Q : M₂ ≤ ⨆ i, Y i := iSup_le fun j => le_iSup Y j.1
  let H : Subgroup Γ := (⨆ i, Y i) ⊓ Subgroup.centralizer ({σ} : Set Γ)
  let A₁ : Subgroup Γ := M₁ ⊓ H
  let A₂ : Subgroup Γ := M₂ ⊓ H
  have hfixcomm : ∀ x : Γ, σ * x * σ⁻¹ = x → σ * x = x * σ := by
    intro x hx
    calc σ * x = (σ * x * σ⁻¹) * σ := by group
      _ = x * σ := by rw [hx]
  have hfix_mem : ∀ x : Γ, x ∈ ⨆ i, Y i → σ * x * σ⁻¹ = x → x ∈ H := by
    intro x hx hfix
    exact ⟨hx, Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hfixcomm x hfix)⟩
  have hA₁H : H ≤ Subgroup.normalizer (A₁ : Set Γ) :=
    y10xA_le_normalizer (fun g hg n hn => ⟨hM₁norm g hg.1 n hn.1,
      H.mul_mem (H.mul_mem hg hn.2) (H.inv_mem hg)⟩)
  have hA₂H : H ≤ Subgroup.normalizer (A₂ : Set Γ) :=
    y10xA_le_normalizer (fun g hg n hn => ⟨hM₂norm g hg.1 n hn.1,
      H.mul_mem (H.mul_mem hg hn.2) (H.inv_mem hg)⟩)
  have cn₁ : Ĵ ≤ A₁ ∨ ⁅Ĵ, A₁⁆ = ⊥ := y10xA_cn hĴc inf_le_right hA₁H
  have cn₂ : Ĵ ≤ A₂ ∨ ⁅Ĵ, A₂⁆ = ⊥ := y10xA_cn hĴc inf_le_right hA₂H
  by_cases hall : ∀ j, 𝒞 j → P₁ j
  · refine ⟨j₁, fun j hj => hall j hj, le_trans hĴW (iSup_le fun j => ?_)⟩
    obtain ⟨n, hn⟩ := hall j.1 j.2
    rw [hn]
    exact le_iSup (fun n : ℕ => (Y j₁).map (MulAut.conj (σ ^ n)).toMonoidHom) n
  exfalso
  push_neg at hall
  obtain ⟨j₂, hj₂𝒞, hj₂P⟩ := hall
  have hM₁y₂ : ∀ m ∈ M₁, ∀ y ∈ Y j₂, m * y = y * m := fun m hm y hy =>
    y10xA_iSup_centralizes (fun j : {j // 𝒞 j ∧ P₁ j} => Y j.1) y
      (fun j z hz => y10xA_commute_of_bot
        (hcomm _ _ (fun he => hj₂P ((hPe _ _ he).1 j.2.2))) z hz y hy) m hm
  have hP₁j₁ : P₁ j₁ := by
    refine ⟨0, ?_⟩
    have hid : (MulAut.conj (σ ^ 0)).toMonoidHom = MonoidHom.id Γ := by
      ext x
      simp [MulAut.conj_apply]
    rw [hid, Subgroup.map_id]
  have hM₂y₁ : ∀ m ∈ M₂, ∀ y ∈ Y j₁, m * y = y * m := fun m hm y hy =>
    y10xA_iSup_centralizes (fun j : {j // 𝒞 j ∧ ¬ P₁ j} => Y j.1) y
      (fun j z hz => y10xA_commute_of_bot
        (hcomm _ _ (fun he => j.2.2 ((hPe _ _ he).2 hP₁j₁))) z hz y hy) m hm
  rcases cn₁ with h1 | h1
  · obtain ⟨g, hg, y, hy, hgy⟩ := hj₂𝒞
    exact hgy (hM₁y₂ g (h1 hg).1 y hy)
  rcases cn₂ with h2 | h2
  · obtain ⟨g, hg, y, hy, hgy⟩ := hj₁
    exact hgy (hM₂y₁ g (h2 hg).1 y hy)
  have hJA₁ : y10xA_Commute Ĵ A₁ := y10xA_commute_of_bot h1
  have hJA₂ : y10xA_Commute Ĵ A₂ := y10xA_commute_of_bot h2
  have hA₁M₁ : A₁ ≤ M₁ := inf_le_left
  have hA₂M₂ : A₂ ≤ M₂ := inf_le_left
  have hA₁A₂ : y10xA_Commute A₁ A₂ := fun a ha b hb => hM₁M₂ a (hA₁M₁ ha) b (hA₂M₂ hb)
  have hgcomm : ∀ g ∈ Ĵ, ∀ h ∈ Ĵ, ⁅g, h⁆ ∈ A₁ ⊔ A₂ := by
    intro g hg h hh
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := y10xA_mem_sup_of_commute hM₁M₂ (hW_le (hĴW hg))
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := y10xA_mem_sup_of_commute hM₁M₂ (hW_le (hĴW hh))
    have hfixg : σ * (g₁ * g₂) * σ⁻¹ = g₁ * g₂ := by
      rw [hĴC _ hg]
      group
    have hfixh : σ * (h₁ * h₂) * σ⁻¹ = h₁ * h₂ := by
      rw [hĴC _ hh]
      group
    obtain ⟨zg, hzg⟩ : ∃ z : Γ, z = g₁⁻¹ * (σ * g₁ * σ⁻¹) := ⟨_, rfl⟩
    obtain ⟨zh, hzh⟩ : ∃ z : Γ, z = h₁⁻¹ * (σ * h₁ * σ⁻¹) := ⟨_, rfl⟩
    have hsg : σ * g₁ * σ⁻¹ = g₁ * zg := by
      rw [hzg]
      group
    have hsh : σ * h₁ * σ⁻¹ = h₁ * zh := by
      rw [hzh]
      group
    have hzgM₁ : zg ∈ M₁ := by
      rw [hzg]
      exact M₁.mul_mem (M₁.inv_mem hg₁) (hσM₁ g₁ hg₁)
    have hzhM₁ : zh ∈ M₁ := by
      rw [hzh]
      exact M₁.mul_mem (M₁.inv_mem hh₁) (hσM₁ h₁ hh₁)
    have hsg2 : σ * g₂ * σ⁻¹ = zg⁻¹ * g₂ := by
      have e : σ * g₂ * σ⁻¹ = (σ * g₁ * σ⁻¹)⁻¹ * (σ * (g₁ * g₂) * σ⁻¹) := by group
      rw [e, hfixg, hsg]
      group
    have hsh2 : σ * h₂ * σ⁻¹ = zh⁻¹ * h₂ := by
      have e : σ * h₂ * σ⁻¹ = (σ * h₁ * σ⁻¹)⁻¹ * (σ * (h₁ * h₂) * σ⁻¹) := by group
      rw [e, hfixh, hsh]
      group
    have hzgM₂ : zg ∈ M₂ := by
      have e : zg = g₂ * (σ * g₂ * σ⁻¹)⁻¹ := by
        rw [hsg2]
        group
      rw [e]
      exact M₂.mul_mem hg₂ (M₂.inv_mem (hσM₂ g₂ hg₂))
    have hzhM₂ : zh ∈ M₂ := by
      have e : zh = h₂ * (σ * h₂ * σ⁻¹)⁻¹ := by
        rw [hsh2]
        group
      rw [e]
      exact M₂.mul_mem hh₂ (M₂.inv_mem (hσM₂ h₂ hh₂))
    have hzg_g₁ : Commute zg g₁ := (hM₁M₂ g₁ hg₁ zg hzgM₂).symm
    have hzg_h₁ : Commute zg h₁ := (hM₁M₂ h₁ hh₁ zg hzgM₂).symm
    have hzg_g₂ : Commute zg g₂ := hM₁M₂ zg hzgM₁ g₂ hg₂
    have hzg_h₂ : Commute zg h₂ := hM₁M₂ zg hzgM₁ h₂ hh₂
    have hzh_g₁ : Commute zh g₁ := (hM₁M₂ g₁ hg₁ zh hzhM₂).symm
    have hzh_h₁ : Commute zh h₁ := (hM₁M₂ h₁ hh₁ zh hzhM₂).symm
    have hzh_g₂ : Commute zh g₂ := hM₁M₂ zh hzhM₁ g₂ hg₂
    have hzh_h₂ : Commute zh h₂ := hM₁M₂ zh hzhM₁ h₂ hh₂
    have hzg_zh : Commute zg zh := hM₁M₂ zg hzgM₁ zh hzhM₂
    have hc1 : σ * ⁅g₁, h₁⁆ * σ⁻¹ = ⁅g₁, h₁⁆ := by
      calc σ * ⁅g₁, h₁⁆ * σ⁻¹ = ⁅σ * g₁ * σ⁻¹, σ * h₁ * σ⁻¹⁆ := by
            simp only [commutatorElement_def]
            group
        _ = ⁅g₁ * zg, h₁ * zh⁆ := by rw [hsg, hsh]
        _ = ⁅g₁, h₁⁆ := y10xA_comm_central hzg_g₁ hzg_h₁ hzh_g₁ hzh_h₁ hzg_zh
    have hc2 : σ * ⁅g₂, h₂⁆ * σ⁻¹ = ⁅g₂, h₂⁆ := by
      have e₂ : σ * g₂ * σ⁻¹ = g₂ * zg⁻¹ := by
        rw [hsg2, (hzg_g₂.inv_left).eq]
      have e₂' : σ * h₂ * σ⁻¹ = h₂ * zh⁻¹ := by
        rw [hsh2, (hzh_h₂.inv_left).eq]
      calc σ * ⁅g₂, h₂⁆ * σ⁻¹ = ⁅σ * g₂ * σ⁻¹, σ * h₂ * σ⁻¹⁆ := by
            simp only [commutatorElement_def]
            group
        _ = ⁅g₂ * zg⁻¹, h₂ * zh⁻¹⁆ := by rw [e₂, e₂']
        _ = ⁅g₂, h₂⁆ := y10xA_comm_central hzg_g₂.inv_left hzg_h₂.inv_left
            hzh_g₂.inv_left hzh_h₂.inv_left hzg_zh.inv_left.inv_right
    have hM₁c : ⁅g₁, h₁⁆ ∈ M₁ := by
      rw [commutatorElement_def]
      exact M₁.mul_mem (M₁.mul_mem (M₁.mul_mem hg₁ hh₁) (M₁.inv_mem hg₁)) (M₁.inv_mem hh₁)
    have hM₂c : ⁅g₂, h₂⁆ ∈ M₂ := by
      rw [commutatorElement_def]
      exact M₂.mul_mem (M₂.mul_mem (M₂.mul_mem hg₂ hh₂) (M₂.inv_mem hg₂)) (M₂.inv_mem hh₂)
    have hmem1 : ⁅g₁, h₁⁆ ∈ A₁ := ⟨hM₁c, hfix_mem _ (hM₁Q hM₁c) hc1⟩
    have hmem2 : ⁅g₂, h₂⁆ ∈ A₂ := ⟨hM₂c, hfix_mem _ (hM₂Q hM₂c) hc2⟩
    have hcomm_prod : ⁅g₁ * g₂, h₁ * h₂⁆ = ⁅g₁, h₁⁆ * ⁅g₂, h₂⁆ :=
      y10xA_comm_prod (hM₁M₂ h₁ hh₁ g₂ hg₂).symm (hM₁M₂ g₁ hg₁ h₂ hh₂)
        (hM₁M₂ g₁ hg₁ _ hM₂c).symm (hM₁M₂ h₁ hh₁ _ hM₂c).symm
    rw [hcomm_prod]
    exact (A₁ ⊔ A₂).mul_mem (Subgroup.mem_sup_left hmem1) (Subgroup.mem_sup_right hmem2)
  have hsub : Ĵ ≤ A₁ ⊔ A₂ := by
    calc Ĵ = ⁅Ĵ, Ĵ⁆ := hperf.symm
      _ ≤ A₁ ⊔ A₂ := Subgroup.commutator_le.2 hgcomm
  have habel : y10xA_Commute Ĵ Ĵ := by
    intro g hg h hh
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := y10xA_mem_sup_of_commute hA₁A₂ (hsub hg)
    calc a₁ * a₂ * h = a₁ * (a₂ * h) := by group
      _ = a₁ * (h * a₂) := by rw [← hJA₂ h hh a₂ ha₂]
      _ = (a₁ * h) * a₂ := by group
      _ = (h * a₁) * a₂ := by rw [← hJA₁ h hh a₁ ha₁]
      _ = h * (a₁ * a₂) := by group
  apply hne
  rw [← hperf]
  exact y10xA_bot_of_commute habel


section Conc

variable {G : Type} [Group G] [Finite G]

theorem y10xA_comm_mem {X : Subgroup G} {a b : G} (ha : a ∈ X) (hb : b ∈ X) : ⁅a, b⁆ ∈ X := by
  rw [commutatorElement_def]
  exact X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)

theorem y10xA_mem_core {s : ℕ} {X : Subgroup G} {y : G} (hy : y ∈ GLAPPrimeCoreOf s X)
    (hX : y ∈ X) : (⟨y, hX⟩ : ↥X) ∈ GLAPPrimeCore s ↥X := by
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
  have hzeq : z = ⟨y, hX⟩ := Subtype.ext hzy
  rw [← hzeq]
  exact hz

theorem y10xA_of_mem_core {s : ℕ} {X : Subgroup G} {y : G} (hX : y ∈ X)
    (h : (⟨y, hX⟩ : ↥X) ∈ GLAPPrimeCore s ↥X) : y ∈ GLAPPrimeCoreOf s X :=
  Subgroup.mem_map.2 ⟨⟨y, hX⟩, h, rfl⟩

theorem y10xA_quot_comm_of_mem {s : ℕ} {X : Subgroup G} {a b : G} (ha : a ∈ X) (hb : b ∈ X)
    (hab : ⁅a, b⁆ ∈ GLAPPrimeCoreOf s X) :
    QuotientGroup.mk' (GLAPPrimeCore s ↥X) (⟨a, ha⟩ : ↥X) *
        QuotientGroup.mk' (GLAPPrimeCore s ↥X) (⟨b, hb⟩ : ↥X) =
      QuotientGroup.mk' (GLAPPrimeCore s ↥X) (⟨b, hb⟩ : ↥X) *
        QuotientGroup.mk' (GLAPPrimeCore s ↥X) (⟨a, ha⟩ : ↥X) := by
  have e : (⁅(⟨a, ha⟩ : ↥X), ⟨b, hb⟩⁆ : ↥X) = ⟨⁅a, b⁆, y10xA_comm_mem ha hb⟩ := Subtype.ext rfl
  have h1 : ⁅QuotientGroup.mk' (GLAPPrimeCore s ↥X) (⟨a, ha⟩ : ↥X),
      QuotientGroup.mk' (GLAPPrimeCore s ↥X) (⟨b, hb⟩ : ↥X)⁆ = 1 := by
    rw [← map_commutatorElement, e]
    exact (QuotientGroup.eq_one_iff _).2 (y10xA_mem_core hab _)
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem y10xA_comm_mod {s : ℕ} (hs : s.Prime) {X Y Y' : Subgroup G}
    (hY : GLAPComponent s X Y) (hY' : GLAPComponent s X Y') (hne : Y' ≠ Y) {y y' : G}
    (hy : y ∈ Y) (hy' : y' ∈ Y') : ⁅y, y'⁆ ∈ GLAPPrimeCoreOf s X := by
  have hmem := le_centModSubgroup_of_ne hs hY' hY hne hy'
  exact glaPPrimeCoreOf_le_of_isSubnormal hs hY.2.1 ((mem_centModSubgroup.1 hmem).2 y hy)

theorem y10xA_barX_isComponent {s : ℕ} {C Y : Subgroup G} (hY : GLAPComponent s C Y) :
    IsComponentOf (barX s C Y) ⊤ := by
  obtain ⟨-, -, hc, -⟩ := hY
  exact hc

theorem y10xA_cn_mod {s : ℕ} {C K Y : Subgroup G} (hY : GLAPComponent s C Y)
    (hKn : (K.subgroupOf C).Normal) :
    barX s C Y ≤ barX s C K ∨ ⁅barX s C Y, barX s C K⁆ = ⊥ := by
  have hNn : (barX s C K).Normal := by
    unfold barX
    exact hKn.map (QuotientGroup.mk' (GLAPPrimeCore s ↥C)) (QuotientGroup.mk'_surjective _)
  exact y10xA_cn (y10xA_barX_isComponent hY) le_top
    (by rw [Subgroup.normalizer_eq_top_iff.2 hNn])

theorem y10xA_le_sup_of_barX_le {s : ℕ} {C K Y : Subgroup G} (hKC : K ≤ C) (hYC : Y ≤ C)
    (h : barX s C Y ≤ barX s C K) : Y ≤ K ⊔ GLAPPrimeCoreOf s C := by
  intro y hy
  have hyC : y ∈ C := hYC hy
  have hmem : QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨y, hyC⟩ : ↥C) ∈ barX s C K :=
    h (Subgroup.mem_map.2 ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩)
  obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.1 hmem
  have hrel := (QuotientGroup.eq).1 hkeq
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
  have hcore : ((k⁻¹ * ⟨y, hyC⟩ : ↥C) : G) ∈ GLAPPrimeCoreOf s C :=
    Subgroup.mem_map.2 ⟨k⁻¹ * ⟨y, hyC⟩, hrel, rfl⟩
  have hsplit : y = (k : G) * ((k⁻¹ * ⟨y, hyC⟩ : ↥C) : G) := by
    simp
  rw [hsplit]
  exact (K ⊔ GLAPPrimeCoreOf s C).mul_mem (Subgroup.mem_sup_left hkK)
    (Subgroup.mem_sup_right hcore)

end Conc


section Conc2

variable {G : Type} [Group G] [Finite G]

theorem y10xA_conj_closureIn {C J : Subgroup G} {c x : G} (hc : c ∈ C)
    (hx : x ∈ closureIn J C) : c * x * c⁻¹ ∈ closureIn J C := by
  have key : ∀ x ∈ closureIn J C, ∀ c ∈ C, c * x * c⁻¹ ∈ closureIn J C := by
    intro x hx
    unfold closureIn at hx ⊢
    refine Subgroup.iSup_induction (fun a : G => ⨆ (_ : a ∈ C), J.map (MulAut.conj a).toMonoidHom)
      (C := fun x => ∀ c ∈ C, c * x * c⁻¹ ∈ ⨆ (a : G) (_ : a ∈ C), J.map (MulAut.conj a).toMonoidHom)
      hx ?_ ?_ ?_
    · intro a y hy c hc'
      by_cases ha : a ∈ C
      · rw [iSup_pos ha] at hy
        obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hy
        have hca : c * a ∈ C := C.mul_mem hc' ha
        have e : c * (MulAut.conj a).toMonoidHom j * c⁻¹ =
            (MulAut.conj (c * a)).toMonoidHom j := by
          simp [MulAut.conj_apply, mul_assoc]
        rw [e]
        exact le_iSup₂ (f := fun (a : G) (_ : a ∈ C) => J.map (MulAut.conj a).toMonoidHom) (c * a) hca
          (Subgroup.mem_map.2 ⟨j, hj, rfl⟩)
      · rw [iSup_neg ha] at hy
        rw [Subgroup.mem_bot.1 hy]
        simp
    · intro c _
      simp
    · intro x₁ x₂ h₁ h₂ c hc'
      have e : c * (x₁ * x₂) * c⁻¹ = (c * x₁ * c⁻¹) * (c * x₂ * c⁻¹) := by group
      rw [e]
      exact (⨆ (a : G) (_ : a ∈ C), J.map (MulAut.conj a).toMonoidHom).mul_mem
        (h₁ c hc') (h₂ c hc')
  exact key x hx c hc

theorem y10xA_closureIn_normalizer {C J : Subgroup G} :
    C ≤ Subgroup.normalizer ((closureIn J C : Subgroup G) : Set G) :=
  y10xA_le_normalizer fun c hc n hn => y10xA_conj_closureIn hc hn

theorem y10xA_closureIn_le {C J : Subgroup G} (hJC : J ≤ C) : closureIn J C ≤ C := by
  unfold closureIn
  refine iSup₂_le fun a ha => ?_
  rintro _ ⟨j, hj, rfl⟩
  have := hJC hj
  exact C.mul_mem (C.mul_mem ha this) (C.inv_mem ha)

theorem y10xA_le_closureIn {C J : Subgroup G} (hC : (1 : G) ∈ C) : J ≤ closureIn J C := by
  intro j hj
  unfold closureIn
  refine le_iSup₂ (f := fun (a : G) (_ : a ∈ C) => J.map (MulAut.conj a).toMonoidHom) 1 hC ?_
  exact Subgroup.mem_map.2 ⟨j, hj, by simp⟩

theorem y10xA_comm_core_normalizer {s : ℕ} {C K : Subgroup G} (hKC : C ≤ Subgroup.normalizer (K : Set G)) :
    C ≤ Subgroup.normalizer ((⁅K, GLAPPrimeCoreOf s K⁆ : Subgroup G) : Set G) := by
  refine y10xA_le_normalizer fun c hc n hn => ?_
  have hmap : (⁅K, GLAPPrimeCoreOf s K⁆ : Subgroup G).map (MulAut.conj c).toMonoidHom ≤
      ⁅K, GLAPPrimeCoreOf s K⁆ := by
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_
    · intro k hk
      obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.1 hk
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 (hKC hc) k').1 hk'
    · intro o ho
      obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.1 ho
      have hcO := normalizer_le_normalizer_glaPPrimeCoreOf s K (hKC hc)
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 hcO o').1 ho'
  exact hmap (Subgroup.mem_map.2 ⟨n, hn, rfl⟩)

end Conc2


section Conc3

variable {G : Type} [Group G] [Finite G]

theorem y10xA_barX_comm {s : ℕ} {C Y Y' : Subgroup G} (hs : s.Prime)
    (hY : GLAPComponent s C Y) (hY' : GLAPComponent s C Y') (hne : Y' ≠ Y) :
    y10xA_Commute (barX s C Y) (barX s C Y') := by
  intro a ha b hb
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hb
  have hz' : (z : G) ∈ Y := Subgroup.mem_subgroupOf.1 hz
  have hw' : (w : G) ∈ Y' := Subgroup.mem_subgroupOf.1 hw
  exact y10xA_quot_comm_of_mem z.2 w.2 (y10xA_comm_mod hs hY hY' hne hz' hw')

theorem y10xA_barX_layer {s : ℕ} {C J : Subgroup G} (hJlay : J ≤ GLAPLayer s C) (hJC : J ≤ C) :
    barX s C J ≤ ⨆ (Y : {Y : Subgroup G // GLAPComponent s C Y}), barX s C Y.1 := by
  have hlay : GLAPLayer s C ≤ ⨆ (Y : {Y : Subgroup G // GLAPComponent s C Y}), Y.1 := by
    unfold GLAPLayer
    refine sSup_le fun L hL => ?_
    exact le_iSup (fun Y : {Y : Subgroup G // GLAPComponent s C Y} => Y.1) ⟨L, hL⟩
  intro t ht
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 ht
  have hmem : j.1 ∈ ⨆ (Y : {Y : Subgroup G // GLAPComponent s C Y}), Y.1 :=
    hlay (hJlay (Subgroup.mem_subgroupOf.1 hj))
  have key := Subgroup.iSup_induction (fun Y : {Y : Subgroup G // GLAPComponent s C Y} => Y.1)
    (C := fun g => ∃ hg : g ∈ C, QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨g, hg⟩ : ↥C) ∈
      ⨆ (Y : {Y : Subgroup G // GLAPComponent s C Y}), barX s C Y.1) hmem ?_ ?_ ?_
  · exact key.2
  · intro Y x hx
    obtain ⟨hYC, -, -, -⟩ := Y.2
    refine ⟨hYC hx, le_iSup (fun Y : {Y : Subgroup G // GLAPComponent s C Y} => barX s C Y.1) Y ?_⟩
    exact Subgroup.mem_map.2 ⟨⟨x, hYC hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  · refine ⟨C.one_mem, ?_⟩
    have e : (⟨1, C.one_mem⟩ : ↥C) = 1 := Subtype.ext rfl
    rw [e, map_one]
    exact (⨆ (Y : {Y : Subgroup G // GLAPComponent s C Y}), barX s C Y.1).one_mem
  · rintro x y ⟨hx1, h1⟩ ⟨hy1, h2⟩
    refine ⟨C.mul_mem hx1 hy1, ?_⟩
    have e : (⟨x * y, C.mul_mem hx1 hy1⟩ : ↥C) = ⟨x, hx1⟩ * ⟨y, hy1⟩ := Subtype.ext rfl
    rw [e, map_mul]
    exact (⨆ (Y : {Y : Subgroup G // GLAPComponent s C Y}), barX s C Y.1).mul_mem h1 h2

end Conc3


section Conc4

variable {G : Type} [Group G] [Finite G]

theorem y10xA_barJ_le_S {s : ℕ} (hs : s.Prime) {C J K : Subgroup G}
    (hJlay : J ≤ GLAPLayer s C) (hJC : J ≤ C) (hJK : J ≤ K) (hKC : K ≤ C)
    (hKn : (K.subgroupOf C).Normal) (hJq : CFSG.Open.IsQuasisimple ↥J) :
    barX s C J ≤ ⨆ (Y : {Y : Subgroup G // GLAPComponent s C Y ∧
      Y ≤ K ⊔ GLAPPrimeCoreOf s C}), barX s C Y.1 := by
  classical
  set O := GLAPPrimeCoreOf s C with hO
  let Sx := {Y : Subgroup G // GLAPComponent s C Y ∧ Y ≤ K ⊔ O}
  let Sc := {Y : Subgroup G // GLAPComponent s C Y ∧ ¬ Y ≤ K ⊔ O}
  let All := {Y : Subgroup G // GLAPComponent s C Y}
  let W : Subgroup (↥C ⧸ GLAPPrimeCore s ↥C) := ⨆ (Y : Sx), barX s C Y.1
  let V : Subgroup (↥C ⧸ GLAPPrimeCore s ↥C) := ⨆ (Y : Sc), barX s C Y.1
  have hbarK : barX s C J ≤ barX s C K := barX_mono s hJK
  have hne : ∀ (Y Y' : All), ¬ Y'.1 = Y.1 → y10xA_Commute (barX s C Y.1) (barX s C Y'.1) :=
    fun Y Y' h => y10xA_barX_comm hs Y.2 Y'.2 h
  have hWV : y10xA_Commute W V := by
    refine y10xA_commute_iSup (fun Y : Sx => barX s C Y.1) (fun Y : Sc => barX s C Y.1)
      (fun i j => y10xA_barX_comm hs i.2.1 j.2.1 ?_)
    intro h
    apply j.2.2
    rw [h]
    exact i.2.2
  have hScK : ∀ Y : Sc, ⁅barX s C Y.1, barX s C K⁆ = ⊥ := by
    intro Y
    rcases y10xA_cn_mod Y.2.1 hKn with h | h
    · exact absurd (y10xA_le_sup_of_barX_le hKC Y.2.1.1 h) Y.2.2
    · exact h
  have hV : V ≤ Subgroup.centralizer ((barX s C K : Subgroup _) : Set (↥C ⧸ GLAPPrimeCore s ↥C)) := by
    refine iSup_le fun Y => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (y10xA_commute_of_bot (hScK Y) y hy h hh).symm
  have hVT : ∀ v ∈ V, ∀ t ∈ barX s C J, v * t = t * v := by
    intro v hv t ht
    exact ((Subgroup.mem_centralizer_iff.1 (hV hv)) t (hbarK ht)).symm
  have hgen : ∀ Y : All, barX s C Y.1 ≤ W ∨ ∀ m ∈ W, ∀ z ∈ barX s C Y.1, z * m = m * z := by
    intro Y
    by_cases hY : Y.1 ≤ K ⊔ O
    · exact Or.inl (le_iSup (fun Y' : Sx => barX s C Y'.1) ⟨Y.1, Y.2, hY⟩)
    · right
      intro m hm z hz
      have hcomm : ∀ Y' : Sx, ∀ u ∈ barX s C Y'.1, u * z = z * u := by
        intro Y' u hu
        exact y10xA_barX_comm hs Y'.2.1 Y.2 (fun h => hY (h ▸ Y'.2.2)) _ hu _ hz
      exact ((y10xA_iSup_centralizes (fun Y' : Sx => barX s C Y'.1) z hcomm) m hm).symm
  have hWnorm : ∀ t ∈ barX s C J, ∀ w ∈ W, t * w * t⁻¹ ∈ W := by
    intro t ht w hw
    exact y10xA_normalizes_sup (fun Y : All => barX s C Y.1) W hgen t
      (y10xA_barX_layer hJlay hJC ht) w hw
  have hTWV : barX s C J ≤ W ⊔ V := by
    refine le_trans (y10xA_barX_layer hJlay hJC) (iSup_le fun Y => ?_)
    by_cases hY : Y.1 ≤ K ⊔ O
    · exact le_sup_of_le_left (le_iSup (fun Y' : Sx => barX s C Y'.1) ⟨Y.1, Y.2, hY⟩)
    · exact le_sup_of_le_right (le_iSup (fun Y' : Sc => barX s C Y'.1) ⟨Y.1, Y.2, hY⟩)
  have hperf : ⁅barX s C J, barX s C J⁆ = barX s C J := by
    rw [← barX_commutator s hJC hJC, y10xA_qs_comm_self hJq]
  exact y10xA_le_of_perfect hWnorm hVT hWV hTWV hperf

end Conc4


section Conc5

variable {G : Type} [Group G] [Finite G]

theorem y10xA_mem_sup_of_barX {s : ℕ} {C : Subgroup G} {ι : Type} (F : ι → Subgroup G)
    {z : ↥C ⧸ GLAPPrimeCore s ↥C} (hz : z ∈ ⨆ i, barX s C (F i)) :
    ∀ (a : G) (ha : a ∈ C), QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨a, ha⟩ : ↥C) = z →
      a ∈ (⨆ i, F i) ⊔ GLAPPrimeCoreOf s C := by
  refine Subgroup.iSup_induction (fun i => barX s C (F i))
    (C := fun z => ∀ (a : G) (ha : a ∈ C),
      QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨a, ha⟩ : ↥C) = z →
        a ∈ (⨆ i, F i) ⊔ GLAPPrimeCoreOf s C) hz ?_ ?_ ?_
  · intro i z' hz' a ha hzeq
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz'
    have hrel := (QuotientGroup.eq).1 hzeq
    have e : (w⁻¹ * ⟨a, ha⟩ : ↥C) = (⟨a, ha⟩⁻¹ * w)⁻¹ := by group
    have hcore : (w⁻¹ * ⟨a, ha⟩ : ↥C) ∈ GLAPPrimeCore s ↥C := by
      rw [e]
      exact (GLAPPrimeCore s ↥C).inv_mem hrel
    have hO : (((w⁻¹ * ⟨a, ha⟩ : ↥C)) : G) ∈ GLAPPrimeCoreOf s C :=
      y10xA_of_mem_core (w⁻¹ * ⟨a, ha⟩ : ↥C).2 hcore
    have hsplit : a = (w : G) * (((w⁻¹ * ⟨a, ha⟩ : ↥C)) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      group
    rw [hsplit]
    exact ((⨆ i, F i) ⊔ GLAPPrimeCoreOf s C).mul_mem
      (Subgroup.mem_sup_left ((le_iSup F i) (Subgroup.mem_subgroupOf.1 hw))) (Subgroup.mem_sup_right hO)
  · intro a ha h1
    have hO : a ∈ GLAPPrimeCoreOf s C := y10xA_of_mem_core ha ((QuotientGroup.eq_one_iff _).1 h1)
    exact Subgroup.mem_sup_right hO
  · intro z₁ z₂ h₁ h₂ a ha hzeq
    obtain ⟨x₁, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore s ↥C) z₁
    obtain ⟨x₂, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore s ↥C) z₂
    have hx₁ := h₁ (x₁ : G) x₁.2 rfl
    have hx₂ := h₂ (x₂ : G) x₂.2 rfl
    rw [← map_mul] at hzeq
    have hrel := (QuotientGroup.eq).1 hzeq
    have e : ((x₁ * x₂)⁻¹ * ⟨a, ha⟩ : ↥C) = ((⟨a, ha⟩⁻¹ * (x₁ * x₂)))⁻¹ := by group
    have hcore : ((x₁ * x₂)⁻¹ * ⟨a, ha⟩ : ↥C) ∈ GLAPPrimeCore s ↥C := by
      rw [e]
      exact (GLAPPrimeCore s ↥C).inv_mem hrel
    have hO : (((x₁ * x₂)⁻¹ * ⟨a, ha⟩ : ↥C) : G) ∈ GLAPPrimeCoreOf s C :=
      y10xA_of_mem_core ((x₁ * x₂)⁻¹ * ⟨a, ha⟩ : ↥C).2 hcore
    have hsplit : a = (((x₁ * x₂ : ↥C)) : G) * ((((x₁ * x₂)⁻¹ * ⟨a, ha⟩ : ↥C)) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      group
    rw [hsplit]
    exact ((⨆ i, F i) ⊔ GLAPPrimeCoreOf s C).mul_mem
      (((⨆ i, F i) ⊔ GLAPPrimeCoreOf s C).mul_mem hx₁ hx₂) (Subgroup.mem_sup_right hO)

theorem y10xA_closureIn_le_of {C J X : Subgroup G} (hJX : J ≤ X)
    (hX : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X) : closureIn J C ≤ X := by
  unfold closureIn
  refine iSup₂_le fun a ha => ?_
  rintro _ ⟨j, hj, rfl⟩
  exact hX a ha j (hJX hj)

theorem y10xA_sup_conj_mem {C A B : Subgroup G} (hAB : ∀ h ∈ A, ∀ t ∈ B, h * t * h⁻¹ ∈ B)
    (hA : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A) (hB : ∀ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    {c : G} (hc : c ∈ C) {x : G} (hx : x ∈ A ⊔ B) : c * x * c⁻¹ ∈ A ⊔ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := lemma117_diag_sup_decomp_norm hAB hx
  have e : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
  rw [e]
  exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left (hA c hc a ha))
    (Subgroup.mem_sup_right (hB c hc b hb))

theorem y10xA_conj_mem_S {s : ℕ} {C K Y : Subgroup G} {c : G} (hcC : c ∈ C)
    (hCn : C ≤ Subgroup.normalizer (C : Set G)) (hKC : K ≤ C)
    (hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hOn : ∀ c ∈ C, ∀ o ∈ GLAPPrimeCoreOf s C, c * o * c⁻¹ ∈ GLAPPrimeCoreOf s C)
    (hY : GLAPComponent s C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C) :
    GLAPComponent s C (GLBConj c⁻¹ Y) ∧ GLBConj c⁻¹ Y ≤ K ⊔ GLAPPrimeCoreOf s C := by
  have hcN : c⁻¹ ∈ Subgroup.normalizer (C : Set G) := hCn (C.inv_mem hcC)
  have hCeq : GLBConj c⁻¹ C = C := (mem_normalizer_iff_gLBConj_eq.1 hcN)
  have hAB : ∀ h ∈ K, ∀ t ∈ GLAPPrimeCoreOf s C, h * t * h⁻¹ ∈ GLAPPrimeCoreOf s C :=
    fun h hh t ht => hOn h (hKC hh) t ht
  refine ⟨?_, ?_⟩
  · have h := glaPComponent_gLBConj hY c⁻¹
    rwa [hCeq] at h
  · intro y hy
    rw [mem_gLBConj] at hy
    have h2 := y10xA_sup_conj_mem hAB hKn hOn hcC (hYK hy)
    rwa [show c * (c⁻¹ * y * c⁻¹⁻¹) * c⁻¹ = y by group] at h2

end Conc5


section Conc6

variable {G : Type} [Group G] [Finite G]

theorem y10xA_fnd_iff_open (Q : Type) [Group Q] :
    CFSG.IsQuasisimple Q ↔ CFSG.Open.IsQuasisimple Q :=
  (CFSG.Foundations.SteinbergCA.quasisimple_iff Q).2.2.1

def y10xA_img (C N : Subgroup G) [(N.subgroupOf C).Normal] (H : Subgroup G) :
    Subgroup (↥C ⧸ N.subgroupOf C) :=
  (H.subgroupOf C).map (QuotientGroup.mk' (N.subgroupOf C))

theorem y10xA_mem_img {C N H : Subgroup G} [(N.subgroupOf C).Normal] {c : G} (hcC : c ∈ C)
    (hc : c ∈ H) : QuotientGroup.mk' (N.subgroupOf C) (⟨c, hcC⟩ : ↥C) ∈ y10xA_img C N H :=
  Subgroup.mem_map.2 ⟨⟨c, hcC⟩, Subgroup.mem_subgroupOf.2 hc, rfl⟩

theorem y10xA_exists_of_mem_img {C N H : Subgroup G} [(N.subgroupOf C).Normal]
    {z : ↥C ⧸ N.subgroupOf C} (hz : z ∈ y10xA_img C N H) :
    ∃ c : ↥C, (c : G) ∈ H ∧ QuotientGroup.mk' (N.subgroupOf C) c = z := by
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.1 hz
  exact ⟨c, Subgroup.mem_subgroupOf.1 hc, hcz⟩

theorem y10xA_img_mono {C N H H' : Subgroup G} [(N.subgroupOf C).Normal] (h : H ≤ H') :
    y10xA_img C N H ≤ y10xA_img C N H' := by
  intro z hz
  obtain ⟨c, hc, rfl⟩ := y10xA_exists_of_mem_img hz
  exact Subgroup.mem_map.2 ⟨c, Subgroup.mem_subgroupOf.2 (h hc), rfl⟩

theorem y10xA_mem_of_mk_eq {C N K : Subgroup G} [(N.subgroupOf C).Normal] (hNK : N ≤ K)
    {k c : ↥C} (hk : (k : G) ∈ K)
    (h : QuotientGroup.mk' (N.subgroupOf C) k = QuotientGroup.mk' (N.subgroupOf C) c) :
    (c : G) ∈ K := by
  have hrel := (QuotientGroup.eq).1 h
  have hn : ((k⁻¹ * c : ↥C) : G) ∈ N := Subgroup.mem_subgroupOf.1 hrel
  have e : (c : G) = (k : G) * ((k⁻¹ * c : ↥C) : G) := by simp
  rw [e]
  exact K.mul_mem hk (hNK hn)

theorem y10xA_isPGroup_zpowers {Q : Type} [Group Q] {p : ℕ} (hp : p.Prime) {a : Q}
    (ha : a ^ p = 1) : IsPGroup p (Subgroup.zpowers a) := by
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  have h1 : (a ^ n) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
  rw [pow_one, Subgroup.coe_pow, ← hn]
  simpa using h1

theorem y10xA_centralizer_singleton_eq {Q : Type} [Group Q] (g : Q) :
    Subgroup.centralizer ({g} : Set Q) =
      Subgroup.centralizer ((Subgroup.zpowers g : Subgroup Q) : Set Q) := by
  ext h
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hh k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (SetLike.mem_coe.1 hk)
    exact (Commute.zpow_left (hh g (Set.mem_singleton g)) m).eq
  · intro hh k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    exact hh g (SetLike.mem_coe.2 (Subgroup.mem_zpowers g))

theorem y10xA_img_inf_centralizer {p : ℕ} (hp : p.Prime) {C K N : Subgroup G}
    [(N.subgroupOf C).Normal] {x : G} (hxC : x ∈ C) (hx : x ^ p = 1) (hKC : K ≤ C) (hNK : N ≤ K)
    (hNp : ¬ p ∣ Nat.card N) :
    y10xA_img C N K ⊓
        Subgroup.centralizer ({QuotientGroup.mk' (N.subgroupOf C) (⟨x, hxC⟩ : ↥C)} :
          Set (↥C ⧸ N.subgroupOf C)) =
      y10xA_img C N (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hNC : N ≤ C := hNK.trans hKC
  have hNp' : ¬ p ∣ Nat.card (N.subgroupOf C) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
  set a : ↥C := ⟨x, hxC⟩ with ha
  have hax : ((a : ↥C) : G) = x := rfl
  have hpow : a ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hax, hx]; rfl)
  have hcop := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime p (N.subgroupOf C) hNp'
    (Subgroup.zpowers a) (y10xA_isPGroup_zpowers hp hpow)
  rw [MonoidHom.map_zpowers, ← y10xA_centralizer_singleton_eq (QuotientGroup.mk' (N.subgroupOf C) a)]
    at hcop
  ext z
  constructor
  · rintro ⟨hzK, hzC⟩
    obtain ⟨k, hkK, rfl⟩ := y10xA_exists_of_mem_img hzK
    have hz' : QuotientGroup.mk' (N.subgroupOf C) k ∈
        (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup ↥C) : Set ↥C)).map
          (QuotientGroup.mk' (N.subgroupOf C)) := by
      rw [hcop]
      exact hzC
    obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.1 hz'
    have hcK : (c : G) ∈ K := y10xA_mem_of_mk_eq hNK hkK hcz.symm
    have hcx : (c : G) ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h2 := Subgroup.mem_centralizer_iff.1 hc a (Subgroup.mem_zpowers a)
      have h3 := congrArg Subtype.val h2
      simpa [hax] using h3
    exact Subgroup.mem_map.2 ⟨c, Subgroup.mem_subgroupOf.2 ⟨hcK, hcx⟩, hcz⟩
  · intro hz
    obtain ⟨c, hc, rfl⟩ := y10xA_exists_of_mem_img hz
    refine ⟨Subgroup.mem_map.2 ⟨c, Subgroup.mem_subgroupOf.2 hc.1, rfl⟩, ?_⟩
    rw [← hcop]
    have hcomm : a * c = c * a := by
      apply Subtype.ext
      have h4 := Subgroup.mem_centralizer_iff.1 hc.2 x (Set.mem_singleton x)
      simp only [Subgroup.coe_mul, hax]
      exact h4
    have hcen : c ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup ↥C) : Set ↥C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (SetLike.mem_coe.1 hh)
      exact (Commute.zpow_left (show Commute a c from hcomm) m).eq
    exact Subgroup.mem_map.2 ⟨c, hcen, rfl⟩

theorem lemma117_khat_transport {p : ℕ} (hp : p.Prime) {C K J N : Subgroup G}
    [(N.subgroupOf C).Normal] {x : G} (hxC : x ∈ C) (hx : x ^ p = 1) (hKC : K ≤ C)
    (hNK : N ≤ K) (hNp : ¬ p ∣ Nat.card N) (hJK : J ≤ K)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hJN : ¬ J ≤ N)
    (hJs : CFSG.Open.IsSubnormal J (K ⊓ Subgroup.centralizer ({x} : Set G))) :
    CFSG.Open.IsComponentOf (y10xA_img C N J)
      (y10xA_img C N K ⊓
        Subgroup.centralizer ({QuotientGroup.mk' (N.subgroupOf C) (⟨x, hxC⟩ : ↥C)} :
          Set (↥C ⧸ N.subgroupOf C))) := by
  rw [y10xA_img_inf_centralizer hp hxC hx hKC hNK hNp]
  have hJC : J ≤ C := hJK.trans hKC
  have hJx : J ≤ K ⊓ Subgroup.centralizer ({x} : Set G) := hJs.le
  refine ⟨y10xA_img_mono hJx, ?_, ?_⟩
  · exact CFSG.Open.IsSubnormal.map (QuotientGroup.mk' (N.subgroupOf C))
      (CFSG.Open.IsSubnormal.comap C.subtype hJs)
  · have hJt : CFSG.Open.IsQuasisimple ↥(J.subgroupOf C) :=
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC) hJq
    have hJπ : ¬ (J.subgroupOf C) ≤ (QuotientGroup.mk' (N.subgroupOf C)).ker := by
      intro h
      apply hJN
      intro j hj
      have hjC : j ∈ C := hJC hj
      have h1 := h (show (⟨j, hjC⟩ : ↥C) ∈ J.subgroupOf C from Subgroup.mem_subgroupOf.2 hj)
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact Subgroup.mem_subgroupOf.1 h1
    exact (y10xA_fnd_iff_open _).1
      (CFSG.LocalCores.isQuasisimple_map ((y10xA_fnd_iff_open _).2 hJt)
        (QuotientGroup.mk' (N.subgroupOf C)) hJπ)

end Conc6

section Conc7

variable {G : Type} [Group G] [Finite G]

theorem y10xA_comm_mem_gen {Q : Type} [Group Q] {X : Subgroup Q} {a b : Q} (ha : a ∈ X)
    (hb : b ∈ X) : ⁅a, b⁆ ∈ X := by
  rw [commutatorElement_def]
  exact X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)

theorem y10xA_coreOf_le {s : ℕ} (X : Subgroup G) : GLAPPrimeCoreOf s X ≤ X := by
  intro y hy
  obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.1 hy
  exact z.2

theorem y10xA_mk_eq_iff {s : ℕ} {C : Subgroup G} {a b : G} (ha : a ∈ C) (hb : b ∈ C) :
    QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨a, ha⟩ : ↥C) =
        QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨b, hb⟩ : ↥C) ↔
      a⁻¹ * b ∈ GLAPPrimeCoreOf s C := by
  have key : QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨a, ha⟩ : ↥C) =
      QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨b, hb⟩ : ↥C) ↔
        ((⟨a, ha⟩ : ↥C)⁻¹ * ⟨b, hb⟩) ∈ GLAPPrimeCore s ↥C := QuotientGroup.eq
  rw [key]
  constructor
  · intro h
    have h' : ((⟨a, ha⟩⁻¹ * ⟨b, hb⟩ : ↥C) : G) ∈ GLAPPrimeCoreOf s C :=
      Subgroup.mem_map.2 ⟨_, h, rfl⟩
    simpa using h'
  · intro h
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.1 h
    have e : (⟨a, ha⟩⁻¹ * ⟨b, hb⟩ : ↥C) = z :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]; exact hzeq.symm)
    rw [e]
    exact hz

theorem y10xA_inf_le_coreK {s : ℕ} (hs : s.Prime) {C K : Subgroup G} (hKC : K ≤ C)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G)) :
    K ⊓ GLAPPrimeCoreOf s C ≤ GLAPPrimeCoreOf s K := by
  have hcop : Nat.Coprime s (Nat.card (K ⊓ GLAPPrimeCoreOf s C : Subgroup G)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hs]
    intro h
    exact not_dvd_card_glaPPrimeCoreOf hs C (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hKN : K ≤ Subgroup.normalizer ((K ⊓ GLAPPrimeCoreOf s C : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact ⟨K.mul_mem (K.mul_mem hk hn.1) (K.inv_mem hk),
        (Subgroup.mem_normalizer_iff.1 (hO (hKC hk)) n).1 hn.2⟩
    · intro hn
      have hk' : k⁻¹ ∈ K := K.inv_mem hk
      have e : k⁻¹ * (k * n * k⁻¹) * k⁻¹⁻¹ = n := by group
      refine ⟨?_, ?_⟩
      · rw [← e]
        exact K.mul_mem (K.mul_mem hk' hn.1) (K.inv_mem hk')
      · have h2 := (Subgroup.mem_normalizer_iff.1 (hO (hKC hk')) (k * n * k⁻¹)).1 hn.2
        rwa [e] at h2
  exact le_glaPPrimeCoreOf_of_le_normalizer inf_le_left hKN hcop

theorem y10xA_img_central {C K T N : Subgroup G} [(N.subgroupOf C).Normal] (hKC : K ≤ C)
    (hTK : T ≤ K) (hcomm : ∀ k ∈ K, ∀ t ∈ T, ⁅k, t⁆ ∈ N) :
    ∀ z ∈ y10xA_img C N T, ∀ g ∈ y10xA_img C N K, g * z = z * g := by
  intro z hz g hg
  obtain ⟨o, ho, rfl⟩ := y10xA_exists_of_mem_img hz
  obtain ⟨k, hk, rfl⟩ := y10xA_exists_of_mem_img hg
  rw [← map_mul, ← map_mul]
  refine (QuotientGroup.eq).2 ?_
  rw [Subgroup.mem_subgroupOf]
  have hm : ⁅(k : G)⁻¹, (o : G)⁻¹⁆ ∈ N := hcomm _ (K.inv_mem hk) _ (T.inv_mem ho)
  have e : ((((k * o)⁻¹ * (o * k)) : ↥C) : G) = ⁅(k : G)⁻¹, (o : G)⁻¹⁆⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [e]
  exact N.inv_mem hm

theorem y10xA_mk_mem_barX_of_sup {s : ℕ} {C Y : Subgroup G} (hYC : Y ≤ C)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G)) {p : G}
    (hpC : p ∈ C) (hp : p ∈ Y ⊔ GLAPPrimeCoreOf s C) :
    ∃ y : G, ∃ hyC : y ∈ C, y ∈ Y ∧
      QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨p, hpC⟩ : ↥C) =
        QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨y, hyC⟩ : ↥C) := by
  obtain ⟨y, hy, o, ho, hyo⟩ := lemma117_diag_sup_decomp_norm
    (A := Y) (B := GLAPPrimeCoreOf s C)
    (fun h hh t ht => (Subgroup.mem_normalizer_iff.1 (hO (hYC hh)) t).1 ht) hp
  have hyC : y ∈ C := hYC hy
  refine ⟨y, hyC, hy, ?_⟩
  rw [y10xA_mk_eq_iff hpC hyC]
  have e : p⁻¹ * y = o⁻¹ := by rw [← hyo]; group
  rw [e]
  exact (GLAPPrimeCoreOf s C).inv_mem ho

theorem y10xA_barX_le_P {s : ℕ} {C K Y : Subgroup G} (hKC : K ≤ C) (hYC : Y ≤ C)
    (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G)) :
    barX s C Y ≤ barX s C (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)) := by
  intro z hz
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
  have hcY : (c : G) ∈ Y := Subgroup.mem_subgroupOf.1 hc
  obtain ⟨k, hkK, o, ho, hko⟩ := lemma117_diag_sup_decomp_norm
    (A := K) (B := GLAPPrimeCoreOf s C)
    (fun h hh t ht => (Subgroup.mem_normalizer_iff.1 (hO (hKC hh)) t).1 ht) (hYK hcY)
  have hkC : k ∈ C := hKC hkK
  have hkP : k ∈ K ⊓ (Y ⊔ GLAPPrimeCoreOf s C) := by
    refine ⟨hkK, ?_⟩
    have e : k = (c : G) * o⁻¹ := by rw [← hko]; group
    rw [e]
    exact (Y ⊔ GLAPPrimeCoreOf s C).mul_mem (Subgroup.mem_sup_left hcY)
      (Subgroup.mem_sup_right ((GLAPPrimeCoreOf s C).inv_mem ho))
  have hkc : (k : G)⁻¹ * (c : G) ∈ GLAPPrimeCoreOf s C := by
    rw [← hko, inv_mul_cancel_left]
    exact ho
  exact Subgroup.mem_map.2 ⟨⟨k, hkC⟩, Subgroup.mem_subgroupOf.2 hkP,
    (y10xA_mk_eq_iff hkC c.2).2 hkc⟩

theorem y10xA_perf_decomp {s : ℕ} (hs : s.Prime) {C K Y : Subgroup G} (hKC : K ≤ C)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    (hY : GLAPComponent s C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C) {p : ↥C}
    (hp : (p : G) ∈ K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)) :
    ∃ d ∈ ⁅(K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)).subgroupOf C,
        (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)).subgroupOf C⁆,
      ∃ o : ↥C, (o : G) ∈ GLAPPrimeCoreOf s K ∧ p = d * o := by
  classical
  have hYC : Y ≤ C := hY.1
  set P : Subgroup G := K ⊓ (Y ⊔ GLAPPrimeCoreOf s C) with hP
  set Ph : Subgroup ↥C := P.subgroupOf C with hPh
  have hperf : ⁅barX s C Y, barX s C Y⁆ = barX s C Y :=
    y10xA_qs_comm_self (y10xA_barX_isComponent hY).2.2
  have hbarP := y10xA_barX_le_P hKC hYC hYK hO
  have hsub : ⁅barX s C Y, barX s C Y⁆ ≤
      (⁅Ph, Ph⁆).map (QuotientGroup.mk' (GLAPPrimeCore s ↥C)) := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨k1, hk1, rfl⟩ := Subgroup.mem_map.1 (hbarP ha)
    obtain ⟨k2, hk2, rfl⟩ := Subgroup.mem_map.1 (hbarP hb)
    rw [← map_commutatorElement]
    exact Subgroup.mem_map.2 ⟨⁅k1, k2⁆, Subgroup.commutator_mem_commutator hk1 hk2, rfl⟩
  have hpmem : QuotientGroup.mk' (GLAPPrimeCore s ↥C) p ∈ barX s C Y := by
    obtain ⟨y, hyC, hy, hmk⟩ := y10xA_mk_mem_barX_of_sup hYC hO p.2 hp.2
    have hmk' : QuotientGroup.mk' (GLAPPrimeCore s ↥C) p =
        QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨y, hyC⟩ : ↥C) := hmk
    rw [hmk']
    exact Subgroup.mem_map.2 ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  have hmemC : QuotientGroup.mk' (GLAPPrimeCore s ↥C) p ∈ ⁅barX s C Y, barX s C Y⁆ := by
    rw [hperf]
    exact hpmem
  obtain ⟨d, hd, hdeq⟩ := Subgroup.mem_map.1 (hsub hmemC)
  have hdPh : d ∈ Ph := by
    have hle : ⁅Ph, Ph⁆ ≤ Ph := Subgroup.commutator_le.2 fun a ha b hb => y10xA_comm_mem_gen ha hb
    exact hle hd
  have hcore : (d : ↥C)⁻¹ * p ∈ GLAPPrimeCore s ↥C := by
    have h1 : QuotientGroup.mk' (GLAPPrimeCore s ↥C) ((d : ↥C)⁻¹ * p) = 1 := by
      rw [map_mul, map_inv, hdeq, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hoO : (((d : ↥C)⁻¹ * p : ↥C) : G) ∈ GLAPPrimeCoreOf s C :=
    y10xA_of_mem_core _ hcore
  have hopP : ((d : ↥C)⁻¹ * p : ↥C) ∈ Ph := Ph.mul_mem (Ph.inv_mem hdPh) (Subgroup.mem_subgroupOf.2 hp)
  have hoK : (((d : ↥C)⁻¹ * p : ↥C) : G) ∈ K ⊓ GLAPPrimeCoreOf s C := by
    have h1 : (((d : ↥C)⁻¹ * p : ↥C) : G) ∈ P := Subgroup.mem_subgroupOf.1 hopP
    exact ⟨h1.1, hoO⟩
  refine ⟨d, hd, (d : ↥C)⁻¹ * p, y10xA_inf_le_coreK hs hKC hO hoK, ?_⟩
  simp

theorem y10xA_perfect_image {H Γ : Type} [Group H] [Group Γ] (π : H →* Γ) {Ph : Subgroup H}
    {Zs S : Subgroup Γ} (hZc : ∀ z ∈ Zs, ∀ g ∈ S, g * z = z * g) (hAS : Ph.map π ≤ S)
    (hZS : Zs ≤ S)
    (hdec : ∀ p ∈ Ph, ∃ d ∈ ⁅Ph, Ph⁆, ∃ o : H, π o ∈ Zs ∧ p = d * o) :
    ⁅(⁅Ph, Ph⁆).map π, (⁅Ph, Ph⁆).map π⁆ = (⁅Ph, Ph⁆).map π := by
  have hle : ⁅Ph, Ph⁆ ≤ Ph := Subgroup.commutator_le.2 fun a ha b hb => y10xA_comm_mem_gen ha hb
  set A : Subgroup Γ := Ph.map π with hA
  set B : Subgroup Γ := (⁅Ph, Ph⁆).map π with hB
  have hBA : B = ⁅A, A⁆ := Subgroup.map_commutator Ph Ph π
  have hBle : B ≤ A := Subgroup.map_mono hle
  have hBS : B ≤ S := hBle.trans hAS
  have hcentral : ∀ z ∈ Zs, ∀ g ∈ B, Commute z g := fun z hz g hg =>
    (hZc z hz g (hBS hg)).symm
  have hAB : A ≤ B ⊔ Zs := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨d, hd, o, ho, rfl⟩ := hdec p hp
    rw [map_mul]
    exact (B ⊔ Zs).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_map.2 ⟨d, hd, rfl⟩))
      (Subgroup.mem_sup_right ho)
  have hcomm_BZ : y10xA_Commute B Zs := fun b hb z hz => ((hcentral z hz b hb).eq).symm
  have h1 : ⁅A, A⁆ ≤ ⁅B, B⁆ := by
    refine Subgroup.commutator_le.2 fun a ha a' ha' => ?_
    obtain ⟨b, hb, z, hz, hbz⟩ := y10xA_mem_sup_of_commute hcomm_BZ (hAB ha)
    obtain ⟨b', hb', z', hz', hbz'⟩ := y10xA_mem_sup_of_commute hcomm_BZ (hAB ha')
    rw [← hbz, ← hbz']
    rw [y10xA_comm_central (hcentral z hz b hb) (hcentral z hz b' hb')
      (hcentral z' hz' b hb) (hcentral z' hz' b' hb') (hZc z hz z' (hZS hz')).symm]
    exact Subgroup.commutator_mem_commutator hb hb'
  have h2 : ⁅B, B⁆ ≤ B := Subgroup.commutator_le.2 fun a ha b hb => y10xA_comm_mem_gen ha hb
  exact le_antisymm h2 ((le_of_eq hBA).trans h1)

theorem y10xA_perfect_commute {H Γ : Type} [Group H] [Group Γ] (π : H →* Γ) {Ph1 Ph2 : Subgroup H}
    {Zs S : Subgroup Γ} (hZc : ∀ z ∈ Zs, ∀ g ∈ S, g * z = z * g) (hA1S : Ph1.map π ≤ S)
    (hA2S : Ph2.map π ≤ S) (hZS : Zs ≤ S)
    (hdec : ∀ p ∈ Ph1, ∃ d ∈ ⁅Ph1, Ph1⁆, ∃ o : H, π o ∈ Zs ∧ p = d * o)
    (hc : ∀ d ∈ ⁅Ph1, Ph1⁆, ∀ p ∈ Ph2, π ⁅d, p⁆ ∈ Zs) :
    y10xA_Commute (Ph1.map π) (Ph2.map π) := by
  have hle1 : ⁅Ph1, Ph1⁆ ≤ Ph1 := Subgroup.commutator_le.2 fun a ha b hb => y10xA_comm_mem_gen ha hb
  have hperf := y10xA_perfect_image π hZc hA1S hZS hdec
  have hc' : ∀ a ∈ (⁅Ph1, Ph1⁆).map π, ∀ b ∈ Ph2.map π, ⁅a, b⁆ ∈ Zs := by
    intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hb
    rw [← map_commutatorElement]
    exact hc d hd p hp
  have hZZ : ∀ z ∈ Zs, ∀ z' ∈ Zs, z * z' = z' * z := fun z hz z' hz' =>
    (hZc z hz z' (hZS hz')).symm
  have hBS : (⁅Ph1, Ph1⁆).map π ≤ S := (Subgroup.map_mono hle1).trans hA1S
  have hcommB : y10xA_Commute ((⁅Ph1, Ph1⁆).map π) (Ph2.map π) :=
    y10xA_commute_of_perfect hperf (fun z hz g hg => hZc z hz g (sup_le hBS hA2S hg)) hZZ hc'
  intro a ha b hb
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨d, hd, o, ho, rfl⟩ := hdec p hp
  rw [map_mul]
  have hdb := hcommB (π d) (Subgroup.mem_map.2 ⟨d, hd, rfl⟩) b hb
  have hob := hZc (π o) ho b (hA2S hb)
  calc π d * π o * b = π d * (π o * b) := mul_assoc _ _ _
    _ = π d * (b * π o) := by rw [hob]
    _ = (π d * b) * π o := (mul_assoc _ _ _).symm
    _ = (b * π d) * π o := by rw [hdb]
    _ = b * (π d * π o) := mul_assoc _ _ _

theorem y10xA_img_P_commute {s : ℕ} (hs : s.Prime) {C K N : Subgroup G}
    [(N.subgroupOf C).Normal] {Y Y' : Subgroup G} (hKC : K ≤ C)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    (hcomm : ∀ k ∈ K, ∀ t ∈ GLAPPrimeCoreOf s K, ⁅k, t⁆ ∈ N)
    (hY : GLAPComponent s C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C)
    (hY' : GLAPComponent s C Y') (hYK' : Y' ≤ K ⊔ GLAPPrimeCoreOf s C) (hne : Y' ≠ Y) :
    y10xA_Commute (y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)))
      (y10xA_img C N (K ⊓ (Y' ⊔ GLAPPrimeCoreOf s C))) := by
  set P1 : Subgroup G := K ⊓ (Y ⊔ GLAPPrimeCoreOf s C) with hP1
  set P2 : Subgroup G := K ⊓ (Y' ⊔ GLAPPrimeCoreOf s C) with hP2
  have hOK : GLAPPrimeCoreOf s K ≤ K := y10xA_coreOf_le K
  have hZc := y10xA_img_central (N := N) hKC hOK hcomm
  have hP1K : P1 ≤ K := inf_le_left
  have hP2K : P2 ≤ K := inf_le_left
  have hcrossK : ∀ d ∈ P1, ∀ p ∈ P2, ⁅d, p⁆ ∈ GLAPPrimeCoreOf s K := by
    intro d hd p hp
    have hdC : d ∈ C := hKC (hP1K hd)
    have hpC : p ∈ C := hKC (hP2K hp)
    have hm1 : QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨d, hdC⟩ : ↥C) ∈ barX s C Y := by
      obtain ⟨y, hyC, hy, hmk⟩ := y10xA_mk_mem_barX_of_sup hY.1 hO hdC hd.2
      have hmk' : QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨d, hdC⟩ : ↥C) =
          QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨y, hyC⟩ : ↥C) := hmk
      rw [hmk']
      exact Subgroup.mem_map.2 ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
    have hm2 : QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨p, hpC⟩ : ↥C) ∈ barX s C Y' := by
      obtain ⟨y, hyC, hy, hmk⟩ := y10xA_mk_mem_barX_of_sup hY'.1 hO hpC hp.2
      have hmk' : QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨p, hpC⟩ : ↥C) =
          QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨y, hyC⟩ : ↥C) := hmk
      rw [hmk']
      exact Subgroup.mem_map.2 ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
    have hcm := y10xA_barX_comm hs hY hY' hne _ hm1 _ hm2
    have hbar : QuotientGroup.mk' (GLAPPrimeCore s ↥C) ⁅(⟨d, hdC⟩ : ↥C), ⟨p, hpC⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 hcm
    have hcmC : ⁅d, p⁆ ∈ C := y10xA_comm_mem_gen hdC hpC
    have hcoreO : ⁅d, p⁆ ∈ GLAPPrimeCoreOf s C := by
      have e : (⟨⁅d, p⁆, hcmC⟩ : ↥C) = ⁅(⟨d, hdC⟩ : ↥C), ⟨p, hpC⟩⁆ := Subtype.ext rfl
      exact y10xA_of_mem_core hcmC (by rw [e]; exact (QuotientGroup.eq_one_iff _).1 hbar)
    exact y10xA_inf_le_coreK hs hKC hO ⟨y10xA_comm_mem_gen (hP1K hd) (hP2K hp), hcoreO⟩
  have hle1 : ⁅P1.subgroupOf C, P1.subgroupOf C⁆ ≤ P1.subgroupOf C :=
    Subgroup.commutator_le.2 fun a ha b hb => y10xA_comm_mem_gen ha hb
  have hdec : ∀ p ∈ P1.subgroupOf C, ∃ d ∈ ⁅P1.subgroupOf C, P1.subgroupOf C⁆, ∃ o : ↥C,
      QuotientGroup.mk' (N.subgroupOf C) o ∈ y10xA_img C N (GLAPPrimeCoreOf s K) ∧ p = d * o := by
    intro p hp
    obtain ⟨d, hd, o, ho, hpd⟩ :=
      y10xA_perf_decomp hs hKC hO hY hYK (Subgroup.mem_subgroupOf.1 hp)
    exact ⟨d, hd, o, y10xA_mem_img o.2 ho, hpd⟩
  have hc : ∀ d ∈ ⁅P1.subgroupOf C, P1.subgroupOf C⁆, ∀ p ∈ P2.subgroupOf C,
      QuotientGroup.mk' (N.subgroupOf C) ⁅d, p⁆ ∈ y10xA_img C N (GLAPPrimeCoreOf s K) := by
    intro d hd p hp
    have hdP : (d : G) ∈ P1 := Subgroup.mem_subgroupOf.1 (hle1 hd)
    have hpP : (p : G) ∈ P2 := Subgroup.mem_subgroupOf.1 hp
    have hcmC : ((⁅d, p⁆ : ↥C) : G) ∈ GLAPPrimeCoreOf s K := by
      have e : ((⁅d, p⁆ : ↥C) : G) = ⁅(d : G), (p : G)⁆ := rfl
      rw [e]
      exact hcrossK _ hdP _ hpP
    exact y10xA_mem_img (⁅d, p⁆ : ↥C).2 hcmC
  exact y10xA_perfect_commute (Ph1 := P1.subgroupOf C) (Ph2 := P2.subgroupOf C)
    (QuotientGroup.mk' (N.subgroupOf C)) hZc (y10xA_img_mono hP1K) (y10xA_img_mono hP2K)
    (y10xA_img_mono hOK) hdec hc

end Conc7

section Conc8

variable {G : Type} [Group G] [Finite G]

abbrev y10xA_I (s : ℕ) (C K : Subgroup G) : Type :=
  {Y : Subgroup G // GLAPComponent s C Y ∧ Y ≤ K ⊔ GLAPPrimeCoreOf s C}

def y10xA_fam (s : ℕ) (C K N : Subgroup G) [(N.subgroupOf C).Normal] :
    Option (y10xA_I s C K) → Subgroup (↥C ⧸ N.subgroupOf C)
  | none => y10xA_img C N (GLAPPrimeCoreOf s K)
  | some Y => y10xA_img C N (K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C))

theorem y10xA_barX_iSup_mem {s : ℕ} {C : Subgroup G} {ι : Type} (F : ι → Subgroup G)
    (hF : ∀ i, F i ≤ C) {y : G} (hy : y ∈ ⨆ i, F i) :
    ∃ hyC : y ∈ C, QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨y, hyC⟩ : ↥C) ∈
      ⨆ i, barX s C (F i) := by
  refine Subgroup.iSup_induction (fun i => F i) (C := fun y => ∃ hyC : y ∈ C,
    QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨y, hyC⟩ : ↥C) ∈ ⨆ i, barX s C (F i)) hy ?_ ?_ ?_
  · intro i x hx
    have hxC : x ∈ C := hF i hx
    refine ⟨hxC, le_iSup (fun i => barX s C (F i)) i ?_⟩
    exact Subgroup.mem_map.2 ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  · refine ⟨C.one_mem, ?_⟩
    have e : (⟨1, C.one_mem⟩ : ↥C) = 1 := Subtype.ext rfl
    rw [e, map_one]
    exact (⨆ i, barX s C (F i)).one_mem
  · rintro x₁ x₂ ⟨hx1, h1⟩ ⟨hx2, h2⟩
    refine ⟨C.mul_mem hx1 hx2, ?_⟩
    have e : (⟨x₁ * x₂, C.mul_mem hx1 hx2⟩ : ↥C) = ⟨x₁, hx1⟩ * ⟨x₂, hx2⟩ := Subtype.ext rfl
    rw [e, map_mul]
    exact (⨆ i, barX s C (F i)).mul_mem h1 h2

theorem y10xA_img_iSup_mem {C N : Subgroup G} [(N.subgroupOf C).Normal] {ι : Type}
    (F : ι → Subgroup G) (hF : ∀ i, F i ≤ C) {y : G} (hy : y ∈ ⨆ i, F i) :
    ∃ hyC : y ∈ C, QuotientGroup.mk' (N.subgroupOf C) (⟨y, hyC⟩ : ↥C) ∈
      ⨆ i, y10xA_img C N (F i) := by
  refine Subgroup.iSup_induction (fun i => F i) (C := fun y => ∃ hyC : y ∈ C,
    QuotientGroup.mk' (N.subgroupOf C) (⟨y, hyC⟩ : ↥C) ∈ ⨆ i, y10xA_img C N (F i)) hy ?_ ?_ ?_
  · intro i x hx
    have hxC : x ∈ C := hF i hx
    exact ⟨hxC, le_iSup (fun i => y10xA_img C N (F i)) i (y10xA_mem_img hxC hx)⟩
  · refine ⟨C.one_mem, ?_⟩
    have e : (⟨1, C.one_mem⟩ : ↥C) = 1 := Subtype.ext rfl
    rw [e, map_one]
    exact (⨆ i, y10xA_img C N (F i)).one_mem
  · rintro x₁ x₂ ⟨hx1, h1⟩ ⟨hx2, h2⟩
    refine ⟨C.mul_mem hx1 hx2, ?_⟩
    have e : (⟨x₁ * x₂, C.mul_mem hx1 hx2⟩ : ↥C) = ⟨x₁, hx1⟩ * ⟨x₂, hx2⟩ := Subtype.ext rfl
    rw [e, map_mul]
    exact (⨆ i, y10xA_img C N (F i)).mul_mem h1 h2

theorem y10xA_iSup_conj_mem {ι : Type} {C : Subgroup G} (F : ι → Subgroup G)
    (hF : ∀ i, ∀ c ∈ C, ∀ y ∈ F i, ∃ j, c * y * c⁻¹ ∈ F j) :
    ∀ c ∈ C, ∀ a ∈ ⨆ i, F i, c * a * c⁻¹ ∈ ⨆ i, F i := by
  intro c hc a ha
  refine Subgroup.iSup_induction F (C := fun a => c * a * c⁻¹ ∈ ⨆ i, F i) ha ?_ ?_ ?_
  · intro i y hy
    obtain ⟨j, hj⟩ := hF i c hc y hy
    exact le_iSup F j hj
  · simp
  · intro x y hx hy
    have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    rw [e]
    exact (⨆ i, F i).mul_mem hx hy

theorem y10xA_sup_normalized {s : ℕ} {C K : Subgroup G} (hKC : K ≤ C)
    (hCn : C ≤ Subgroup.normalizer (C : Set G))
    (hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G)) :
    ∀ c ∈ C, ∀ x ∈ (⨆ Y : y10xA_I s C K, Y.1) ⊔ GLAPPrimeCoreOf s C,
      c * x * c⁻¹ ∈ (⨆ Y : y10xA_I s C K, Y.1) ⊔ GLAPPrimeCoreOf s C := by
  have hOn : ∀ c ∈ C, ∀ o ∈ GLAPPrimeCoreOf s C, c * o * c⁻¹ ∈ GLAPPrimeCoreOf s C :=
    fun c hc o ho => (Subgroup.mem_normalizer_iff.1 (hO hc) o).1 ho
  have hYC : ∀ Y : y10xA_I s C K, Y.1 ≤ C := fun Y => Y.2.1.1
  have hsupC : (⨆ Y : y10xA_I s C K, Y.1) ≤ C := iSup_le hYC
  have hA : ∀ c ∈ C, ∀ a ∈ ⨆ Y : y10xA_I s C K, Y.1, c * a * c⁻¹ ∈ ⨆ Y : y10xA_I s C K, Y.1 := by
    refine y10xA_iSup_conj_mem (fun Y : y10xA_I s C K => Y.1) ?_
    intro Y c hc y hy
    refine ⟨⟨GLBConj c⁻¹ Y.1, y10xA_conj_mem_S hc hCn hKC hKn hOn Y.2.1 Y.2.2⟩, ?_⟩
    show c * y * c⁻¹ ∈ GLBConj c⁻¹ Y.1
    rw [mem_gLBConj]
    have e : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
    rw [e]
    exact hy
  have hB : ∀ c ∈ C, ∀ b ∈ GLAPPrimeCoreOf s C, c * b * c⁻¹ ∈ GLAPPrimeCoreOf s C := hOn
  have hAB : ∀ h ∈ ⨆ Y : y10xA_I s C K, Y.1, ∀ t ∈ GLAPPrimeCoreOf s C,
      h * t * h⁻¹ ∈ GLAPPrimeCoreOf s C := fun h hh t ht => hOn h (hsupC hh) t ht
  exact fun c hc x hx => y10xA_sup_conj_mem hAB hA hB hc hx

theorem y10xA_J_le_sup {s : ℕ} (hs : s.Prime) {C K J : Subgroup G} (hKC : K ≤ C) (hJK : J ≤ K)
    (hJC : J ≤ C) (hJlay : J ≤ GLAPLayer s C) (hKn : (K.subgroupOf C).Normal)
    (hJq : CFSG.Open.IsQuasisimple ↥J) :
    J ≤ (⨆ Y : y10xA_I s C K, Y.1) ⊔ GLAPPrimeCoreOf s C := by
  intro j hj
  have hz := y10xA_barJ_le_S hs hJlay hJC hJK hKC hKn hJq
    (Subgroup.mem_map.2 ⟨⟨j, hJC hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩)
  exact y10xA_mem_sup_of_barX (fun Y : y10xA_I s C K => Y.1) hz j (hJC hj) rfl

theorem y10xA_K_le_sup_P {s : ℕ} (hs : s.Prime) {C K : Subgroup G} (hKC : K ≤ C)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    (hKX : K ≤ (⨆ Y : y10xA_I s C K, Y.1) ⊔ GLAPPrimeCoreOf s C) :
    K ≤ (⨆ Y : y10xA_I s C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) ⊔ GLAPPrimeCoreOf s K := by
  have hsupC : (⨆ Y : y10xA_I s C K, Y.1) ≤ C := iSup_le fun Y => Y.2.1.1
  have hNO : ∀ h ∈ (⨆ Y : y10xA_I s C K, Y.1), ∀ t ∈ GLAPPrimeCoreOf s C,
      h * t * h⁻¹ ∈ GLAPPrimeCoreOf s C := fun h hh t ht =>
    (Subgroup.mem_normalizer_iff.1 (hO (hsupC hh)) t).1 ht
  have hPle : (⨆ Y : y10xA_I s C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) ≤ K :=
    iSup_le fun Y => inf_le_left
  have hPO : ∀ h ∈ (⨆ Y : y10xA_I s C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)), ∀ t ∈ GLAPPrimeCoreOf s C,
      h * t * h⁻¹ ∈ GLAPPrimeCoreOf s C := fun h hh t ht =>
    (Subgroup.mem_normalizer_iff.1 (hO ((hPle hh) |> hKC)) t).1 ht
  intro k hk
  have hk' := hKX hk
  obtain ⟨y, hy, o, ho, hyo⟩ := lemma117_diag_sup_decomp_norm hNO hk'
  have hyC : y ∈ C := hsupC hy
  have hbar : QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨k, hKC hk⟩ : ↥C) ∈
      ⨆ Y : y10xA_I s C K, barX s C Y.1 := by
    obtain ⟨hyC', hmem⟩ := y10xA_barX_iSup_mem (fun Y : y10xA_I s C K => Y.1) (fun Y => Y.2.1.1) hy
    have hmk : QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨k, hKC hk⟩ : ↥C) =
        QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨y, hyC⟩ : ↥C) := by
      rw [y10xA_mk_eq_iff (hKC hk) hyC]
      have e : k⁻¹ * y = o⁻¹ := by rw [← hyo]; group
      rw [e]
      exact (GLAPPrimeCoreOf s C).inv_mem ho
    rw [hmk]
    exact hmem
  have hbarP : (⨆ Y : y10xA_I s C K, barX s C Y.1) ≤
      ⨆ Y : y10xA_I s C K, barX s C (K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) :=
    iSup_mono fun Y => y10xA_barX_le_P hKC Y.2.1.1 Y.2.2 hO
  have hz := hbarP hbar
  obtain ⟨p, hp, o', ho', hko⟩ := lemma117_diag_sup_decomp_norm hPO
    (y10xA_mem_sup_of_barX (fun Y : y10xA_I s C K => K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) hz k (hKC hk) rfl)
  have hoK : o' ∈ K := by
    have e : o' = p⁻¹ * k := by rw [← hko]; group
    rw [e]
    exact K.mul_mem (K.inv_mem (hPle hp)) hk
  have hoOK : o' ∈ GLAPPrimeCoreOf s K := y10xA_inf_le_coreK hs hKC hO ⟨hoK, ho'⟩
  rw [← hko]
  exact ((⨆ Y : y10xA_I s C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) ⊔ GLAPPrimeCoreOf s K).mul_mem
    (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hoOK)

end Conc8

section Conc9

variable {G : Type} [Group G] [Finite G]

theorem y10xA_gLBConj_le {C Y : Subgroup G} {c : G} (hc : c ∈ C) (hYC : Y ≤ C) :
    GLBConj c⁻¹ Y ≤ C := by
  intro w hw
  have h2 := hYC (mem_gLBConj.1 hw)
  have e : w = c * (c⁻¹ * w * c⁻¹⁻¹) * c⁻¹ := by group
  rw [e]
  exact C.mul_mem (C.mul_mem hc h2) (C.inv_mem hc)

theorem y10xA_conj_P {s : ℕ} {C K Y : Subgroup G} (hKC : K ≤ C) (hYC : Y ≤ C)
    (hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G)) {c : G}
    (hc : c ∈ C) :
    ∀ h ∈ K ⊓ (Y ⊔ GLAPPrimeCoreOf s C),
      c * h * c⁻¹ ∈ K ⊓ (GLBConj c⁻¹ Y ⊔ GLAPPrimeCoreOf s C) := by
  intro h hh
  refine ⟨hKn c hc h hh.1, ?_⟩
  obtain ⟨y, hy, o, ho, hyo⟩ := lemma117_diag_sup_decomp_norm (A := Y) (B := GLAPPrimeCoreOf s C)
    (fun g hg t ht => (Subgroup.mem_normalizer_iff.1 (hO (hYC hg)) t).1 ht) hh.2
  have e : c * h * c⁻¹ = (c * y * c⁻¹) * (c * o * c⁻¹) := by rw [← hyo]; group
  rw [e]
  refine (GLBConj c⁻¹ Y ⊔ GLAPPrimeCoreOf s C).mul_mem (Subgroup.mem_sup_left ?_)
    (Subgroup.mem_sup_right ?_)
  · rw [mem_gLBConj]
    have e2 : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
    rw [e2]
    exact hy
  · exact (Subgroup.mem_normalizer_iff.1 (hO hc) o).1 ho

theorem y10xA_map_conj_img_of {C H H' N : Subgroup G} [(N.subgroupOf C).Normal] {c : G}
    (hc : c ∈ C) (hHC : H ≤ C) (hH'C : H' ≤ C)
    (hH : ∀ h ∈ H, c * h * c⁻¹ ∈ H') (hH' : ∀ h ∈ H', c⁻¹ * h * c ∈ H) :
    (y10xA_img C N H).map
        (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨c, hc⟩ : ↥C))).toMonoidHom =
      y10xA_img C N H' := by
  apply le_antisymm
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
    obtain ⟨p, hp, rfl⟩ := y10xA_exists_of_mem_img hz
    have hcp : c * (p : G) * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc p.2) (C.inv_mem hc)
    have e : (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨c, hc⟩ : ↥C))).toMonoidHom
        (QuotientGroup.mk' (N.subgroupOf C) p) =
        QuotientGroup.mk' (N.subgroupOf C) (⟨c * (p : G) * c⁻¹, hcp⟩ : ↥C) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      try rfl
    rw [e]
    exact y10xA_mem_img hcp (hH _ hp)
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := y10xA_exists_of_mem_img hw
    have hq' : c⁻¹ * (q : G) * c ∈ H := hH' _ hq
    have hC' : c⁻¹ * (q : G) * c ∈ C := hHC hq'
    refine Subgroup.mem_map.2 ⟨QuotientGroup.mk' (N.subgroupOf C) (⟨c⁻¹ * (q : G) * c, hC'⟩ : ↥C),
      y10xA_mem_img hC' hq', ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]

theorem y10xA_fam_le_img {s : ℕ} {C K N : Subgroup G} [(N.subgroupOf C).Normal]
    (a : Option (y10xA_I s C K)) : y10xA_fam s C K N a ≤ y10xA_img C N K := by
  cases a with
  | none => exact y10xA_img_mono (y10xA_coreOf_le K)
  | some Y => exact y10xA_img_mono inf_le_left

theorem y10xA_img_K_eq {s : ℕ} {C K N : Subgroup G} [(N.subgroupOf C).Normal]
    (hKC : K ≤ C) (hKN : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    (hKP : K ≤ (⨆ Y : y10xA_I s C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) ⊔ GLAPPrimeCoreOf s K) :
    y10xA_img C N K = ⨆ a : Option (y10xA_I s C K), y10xA_fam s C K N a := by
  have hOK : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s K : Subgroup G) : Set G) :=
    fun c hc => normalizer_le_normalizer_glaPPrimeCoreOf s K (hKN hc)
  have hPle : (⨆ Y : y10xA_I s C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) ≤ K :=
    iSup_le fun Y => inf_le_left
  have hPC : (⨆ Y : y10xA_I s C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) ≤ C := hPle.trans hKC
  have hPOK : ∀ h ∈ (⨆ Y : y10xA_I s C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)),
      ∀ t ∈ GLAPPrimeCoreOf s K, h * t * h⁻¹ ∈ GLAPPrimeCoreOf s K := fun h hh t ht =>
    (Subgroup.mem_normalizer_iff.1 (hOK (hPC hh)) t).1 ht
  have hsub : (⨆ Y : y10xA_I s C K, y10xA_img C N (K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C))) ≤
      ⨆ a : Option (y10xA_I s C K), y10xA_fam s C K N a :=
    iSup_le fun Y => le_iSup (fun a => y10xA_fam s C K N a) (some Y)
  apply le_antisymm
  · intro z hz
    obtain ⟨c, hcK, rfl⟩ := y10xA_exists_of_mem_img hz
    obtain ⟨p, hp, o, ho, hko⟩ := lemma117_diag_sup_decomp_norm hPOK (hKP hcK)
    have hpC : p ∈ C := hPC hp
    have hoC : o ∈ C := hKC (y10xA_coreOf_le K ho)
    have hmemP : QuotientGroup.mk' (N.subgroupOf C) (⟨p, hpC⟩ : ↥C) ∈
        ⨆ Y : y10xA_I s C K, y10xA_img C N (K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) := by
      obtain ⟨_, hmem⟩ := y10xA_img_iSup_mem (C := C) (N := N)
        (fun Y : y10xA_I s C K => K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) (fun Y => inf_le_left.trans hKC) hp
      exact hmem
    have hmemO : QuotientGroup.mk' (N.subgroupOf C) (⟨o, hoC⟩ : ↥C) ∈
        ⨆ a : Option (y10xA_I s C K), y10xA_fam s C K N a :=
      le_iSup (fun a => y10xA_fam s C K N a) none (y10xA_mem_img hoC ho)
    have hc_eq : (c : ↥C) = ⟨p, hpC⟩ * ⟨o, hoC⟩ := Subtype.ext hko.symm
    rw [hc_eq, map_mul]
    exact (⨆ a : Option (y10xA_I s C K), y10xA_fam s C K N a).mul_mem (hsub hmemP) hmemO
  · exact iSup_le fun a => y10xA_fam_le_img a

end Conc9

section Conc10

variable {G : Type} [Group G] [Finite G]

theorem y10xA_lift_iSup {C N : Subgroup G} [(N.subgroupOf C).Normal] {ι : Type}
    (F : ι → Subgroup G) (hF : ∀ i, F i ≤ C) {z : ↥C ⧸ N.subgroupOf C}
    (hz : z ∈ ⨆ i, y10xA_img C N (F i)) :
    ∀ (a : G) (ha : a ∈ C), QuotientGroup.mk' (N.subgroupOf C) (⟨a, ha⟩ : ↥C) = z →
      a ∈ (⨆ i, F i) ⊔ N := by
  refine Subgroup.iSup_induction (fun i => y10xA_img C N (F i))
    (C := fun z => ∀ (a : G) (ha : a ∈ C),
      QuotientGroup.mk' (N.subgroupOf C) (⟨a, ha⟩ : ↥C) = z → a ∈ (⨆ i, F i) ⊔ N) hz ?_ ?_ ?_
  · intro i z' hz' a ha hzeq
    obtain ⟨w, hw, rfl⟩ := y10xA_exists_of_mem_img hz'
    have hrel : (⟨a, ha⟩ : ↥C)⁻¹ * w ∈ N.subgroupOf C := (QuotientGroup.eq).1 hzeq
    have hn : (((⟨a, ha⟩ : ↥C)⁻¹ * w : ↥C) : G) ∈ N := Subgroup.mem_subgroupOf.1 hrel
    have hn' : ((w : G))⁻¹ * a ∈ N := by
      have h2 := N.inv_mem (show (((⟨a, ha⟩ : ↥C)⁻¹ * w : ↥C) : G) ∈ N from hn)
      simpa [mul_inv_rev] using h2
    have hsplit : a = (w : G) * ((w : G)⁻¹ * a) := by group
    rw [hsplit]
    exact ((⨆ i, F i) ⊔ N).mul_mem (Subgroup.mem_sup_left (le_iSup F i hw))
      (Subgroup.mem_sup_right hn')
  · intro a ha h1
    have hn : a ∈ N := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
    exact Subgroup.mem_sup_right hn
  · intro z₁ z₂ h₁ h₂ a ha hzeq
    obtain ⟨x₁, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf C) z₁
    obtain ⟨x₂, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf C) z₂
    have hx₁ := h₁ (x₁ : G) x₁.2 rfl
    have hx₂ := h₂ (x₂ : G) x₂.2 rfl
    rw [← map_mul] at hzeq
    have hrel : (⟨a, ha⟩ : ↥C)⁻¹ * (x₁ * x₂) ∈ N.subgroupOf C := (QuotientGroup.eq).1 hzeq
    have hn : (((⟨a, ha⟩ : ↥C)⁻¹ * (x₁ * x₂) : ↥C) : G) ∈ N := Subgroup.mem_subgroupOf.1 hrel
    have hn' : a⁻¹ * ((x₁ : G) * (x₂ : G)) ∈ N := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk] using hn
    have hm : ((x₁ : G) * (x₂ : G))⁻¹ * a ∈ N := by
      have h3 := N.inv_mem hn'
      simpa [mul_inv_rev, mul_assoc] using h3
    have hsplit : a = ((x₁ : G) * (x₂ : G)) * (((x₁ : G) * (x₂ : G))⁻¹ * a) := by group
    rw [hsplit]
    exact ((⨆ i, F i) ⊔ N).mul_mem (((⨆ i, F i) ⊔ N).mul_mem hx₁ hx₂) (Subgroup.mem_sup_right hm)

theorem y10xA_le_of_le_sup_core {s : ℕ} {J M O : Subgroup G}
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hsJ : s ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hOs : ¬ s ∣ Nat.card ↥O) (hMO : ∀ o ∈ O, ∀ m ∈ M, o * m * o⁻¹ ∈ M)
    (hMn : ∀ h ∈ M, ∀ t ∈ O, h * t * h⁻¹ ∈ O) (hJ : J ≤ M ⊔ O) : J ≤ M := by
  have hQn : ∀ q ∈ M ⊔ O, ∀ m ∈ M, q * m * q⁻¹ ∈ M := by
    intro q hq m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := lemma117_diag_sup_decomp_norm hMn hq
    have h1 : b * m * b⁻¹ ∈ M := hMO b hb m hm
    have e : a * b * m * (a * b)⁻¹ = a * (b * m * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem ha h1) (M.inv_mem ha)
  have hQM : M ⊔ O ≤ Subgroup.normalizer (M : Set G) := y10xA_le_normalizer hQn
  haveI hMQ : (M.subgroupOf (M ⊔ O)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hQM
  let φO : ↥O →* (↥(M ⊔ O) ⧸ M.subgroupOf (M ⊔ O)) :=
    (QuotientGroup.mk' (M.subgroupOf (M ⊔ O))).comp (Subgroup.inclusion le_sup_right)
  have hφO : Function.Surjective φO := by
    intro z
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (M.subgroupOf (M ⊔ O)) z
    obtain ⟨a, ha, b, hb, hab⟩ := lemma117_diag_sup_decomp_norm hMn q.2
    refine ⟨⟨b, hb⟩, ?_⟩
    apply (QuotientGroup.eq).2
    rw [Subgroup.mem_subgroupOf]
    have e : ((((⟨b, Subgroup.mem_sup_right hb⟩ : ↥(M ⊔ O)))⁻¹ * q : ↥(M ⊔ O)) : G) =
        b⁻¹ * a * b⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      rw [← hab]
      group
    show ((((⟨b, Subgroup.mem_sup_right hb⟩ : ↥(M ⊔ O)))⁻¹ * q : ↥(M ⊔ O)) : G) ∈ M
    rw [e]
    exact hMO b⁻¹ (O.inv_mem hb) a ha
  have hcardQ : ¬ s ∣ Nat.card (↥(M ⊔ O) ⧸ M.subgroupOf (M ⊔ O)) := fun h =>
    hOs (h.trans (Subgroup.card_dvd_of_surjective hφO))
  let φJ : ↥J →* (↥(M ⊔ O) ⧸ M.subgroupOf (M ⊔ O)) :=
    (QuotientGroup.mk' (M.subgroupOf (M ⊔ O))).comp (Subgroup.inclusion hJ)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups ((y10xA_fnd_iff_open _).2 hJq)
      φJ.normal_ker with htop | hle
  · intro j hj
    have h1 : (⟨j, hj⟩ : ↥J) ∈ φJ.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at h1
    have h3 := (QuotientGroup.eq_one_iff _).1 h1
    exact Subgroup.mem_subgroupOf.1 h3
  · exfalso
    have hidx : (Subgroup.center ↥J).index ∣ φJ.ker.index := Subgroup.index_dvd_of_le hle
    have hr : φJ.ker.index ∣ Nat.card (↥(M ⊔ O) ⧸ M.subgroupOf (M ⊔ O)) := by
      have e1 : φJ.ker.index = Nat.card φJ.range := by
        rw [Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivRange φJ).toEquiv]
      rw [e1]
      exact Subgroup.card_subgroup_dvd_card _
    exact hcardQ ((hsJ.trans hidx).trans hr)

theorem y10xA_barX_conj_le {s : ℕ} {C Y : Subgroup G} (hYC : Y ≤ C)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G)) {o : G}
    (ho : o ∈ GLAPPrimeCoreOf s C) :
    barX s C (GLBConj o⁻¹ Y) ≤ barX s C Y := by
  intro z hz
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
  have hcY : o⁻¹ * (c : G) * o⁻¹⁻¹ ∈ Y := mem_gLBConj.1 (Subgroup.mem_subgroupOf.1 hc)
  have hyC : o⁻¹ * (c : G) * o⁻¹⁻¹ ∈ C := hYC hcY
  have hA : (c : G)⁻¹ * o⁻¹ * (c : G)⁻¹⁻¹ ∈ GLAPPrimeCoreOf s C :=
    (Subgroup.mem_normalizer_iff.1 (hO (C.inv_mem c.2)) o⁻¹).1 ((GLAPPrimeCoreOf s C).inv_mem ho)
  have hcy : (c : G)⁻¹ * (o⁻¹ * (c : G) * o⁻¹⁻¹) ∈ GLAPPrimeCoreOf s C := by
    have e : (c : G)⁻¹ * (o⁻¹ * (c : G) * o⁻¹⁻¹) = ((c : G)⁻¹ * o⁻¹ * (c : G)⁻¹⁻¹) * o := by
      group
    rw [e]
    exact (GLAPPrimeCoreOf s C).mul_mem hA ho
  have heq : QuotientGroup.mk' (GLAPPrimeCore s ↥C) c =
      QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨o⁻¹ * (c : G) * o⁻¹⁻¹, hyC⟩ : ↥C) :=
    (y10xA_mk_eq_iff c.2 hyC).2 hcy
  exact Subgroup.mem_map.2 ⟨⟨o⁻¹ * (c : G) * o⁻¹⁻¹, hyC⟩, Subgroup.mem_subgroupOf.2 hcY, heq.symm⟩

theorem y10xA_O_normalizes_comp {s : ℕ} {C Y : Subgroup G} (hY : GLAPComponent s C Y)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G)) {o : G}
    (ho : o ∈ GLAPPrimeCoreOf s C) : GLBConj o⁻¹ Y = Y := by
  have hoC : o⁻¹ ∈ C := C.inv_mem (y10xA_coreOf_le C ho)
  have hCeq : GLBConj o⁻¹ C = C := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hoC)
  have hY' : GLAPComponent s C (GLBConj o⁻¹ Y) := by
    have h := glaPComponent_gLBConj hY o⁻¹
    rwa [hCeq] at h
  have hle1 := y10xA_barX_conj_le hY.1 hO ho
  have h2 := y10xA_barX_conj_le (s := s) (C := C) (Y := GLBConj o⁻¹ Y) hY'.1 hO
    ((GLAPPrimeCoreOf s C).inv_mem ho)
  rw [inv_inv, gLBConj_gLBConj_inv] at h2
  have hbar : barX s C (GLBConj o⁻¹ Y) = barX s C Y := le_antisymm hle1 h2
  exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_uniqueAux hY' hY hbar

theorem y10xA_O_conj_mem_comp {s : ℕ} {C Y : Subgroup G} (hY : GLAPComponent s C Y)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G)) {o : G}
    (ho : o ∈ GLAPPrimeCoreOf s C) {y : G} (hy : y ∈ Y) : o * y * o⁻¹ ∈ Y := by
  have h := y10xA_O_normalizes_comp hY hO ho
  have hmem : o * y * o⁻¹ ∈ GLBConj o⁻¹ Y := mem_gLBConj.2 (by
    have e : o⁻¹ * (o * y * o⁻¹) * o⁻¹⁻¹ = y := by group
    rw [e]
    exact hy)
  rw [h] at hmem
  exact hmem

end Conc10

section Conc11

variable {G : Type} [Group G] [Finite G]

theorem y10xA_fam_conj {s : ℕ} {C K N : Subgroup G} [(N.subgroupOf C).Normal] (hKC : K ≤ C)
    (hKN : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G)) {c : G}
    (hc : c ∈ C) (a : Option (y10xA_I s C K)) :
    ∃ b, (y10xA_fam s C K N a).map
        (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨c, hc⟩ : ↥C))).toMonoidHom =
      y10xA_fam s C K N b := by
  have hOK : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s K : Subgroup G) : Set G) :=
    fun c' hc' => normalizer_le_normalizer_glaPPrimeCoreOf s K (hKN hc')
  have hCn : C ≤ Subgroup.normalizer (C : Set G) := fun c' hc' => Subgroup.le_normalizer hc'
  have hKn : ∀ c' ∈ C, ∀ k ∈ K, c' * k * c'⁻¹ ∈ K := fun c' hc' k hk =>
    (Subgroup.mem_normalizer_iff.1 (hKN hc') k).1 hk
  cases a with
  | none =>
    refine ⟨none, ?_⟩
    refine y10xA_map_conj_img_of hc ((y10xA_coreOf_le K).trans hKC) ((y10xA_coreOf_le K).trans hKC)
      (fun h hh => (Subgroup.mem_normalizer_iff.1 (hOK hc) h).1 hh) (fun h hh => ?_)
    have h2 := (Subgroup.mem_normalizer_iff.1 (hOK (C.inv_mem hc)) h).1 hh
    rwa [inv_inv] at h2
  | some Y =>
    have hmem : GLAPComponent s C (GLBConj c⁻¹ Y.1) ∧
        GLBConj c⁻¹ Y.1 ≤ K ⊔ GLAPPrimeCoreOf s C :=
      y10xA_conj_mem_S hc hCn hKC hKn (fun c' hc' o ho => (Subgroup.mem_normalizer_iff.1 (hO hc') o).1 ho)
        Y.2.1 Y.2.2
    refine ⟨some ⟨GLBConj c⁻¹ Y.1, hmem⟩, ?_⟩
    have hYC : Y.1 ≤ C := Y.2.1.1
    have hY'C : GLBConj c⁻¹ Y.1 ≤ C := y10xA_gLBConj_le hc hYC
    refine y10xA_map_conj_img_of hc (inf_le_left.trans hKC) (inf_le_left.trans hKC)
      (fun h hh => y10xA_conj_P hKC hYC hKn hO hc h hh) (fun h hh => ?_)
    have key := y10xA_conj_P hKC hY'C hKn hO (C.inv_mem hc) h hh
    rw [inv_inv, gLBConj_gLBConj_inv] at key
    exact key

theorem y10xA_pow_fix {Q : Type} [Group Q] {Y : Subgroup Q} {x : Q} (hx : GLBConj x Y = Y)
    (n : ℕ) : GLBConj (x ^ n) Y = Y := by
  have hxN : x ∈ Subgroup.normalizer (Y : Set Q) := mem_normalizer_iff_gLBConj_eq.2 hx
  exact mem_normalizer_iff_gLBConj_eq.1 (pow_mem hxN n)

theorem y10xA_orbit_ne {Q : Type} [Group Q] {Y : Subgroup Q} {x : Q} {p : ℕ} (hp : p.Prime)
    (hx : x ^ p = 1) (hxY : GLBConj x Y ≠ Y) {i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j) :
    GLBConj (x ^ i) Y ≠ GLBConj (x ^ j) Y := by
  have key : ∀ i j : ℕ, i < j → j < p → GLBConj (x ^ i) Y = GLBConj (x ^ j) Y → False := by
    intro i j hlt hjp heq
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    have hdpos : 0 < d := by omega
    have hdp : d < p := by omega
    have e : GLBConj (x ^ (i + d)) Y = GLBConj (x ^ i) (GLBConj (x ^ d) Y) := by
      rw [pow_add, gLBConj_gLBConj, ← pow_add, ← pow_add, add_comm]
    rw [e] at heq
    have hd : GLBConj (x ^ d) Y = Y := by
      have h3 := congrArg (GLBConj (x ^ i)⁻¹) heq
      rw [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at h3
      exact h3.symm
    have hcop : Nat.Coprime d p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hdpos hdp)).symm
    obtain ⟨m, -, hmod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hdm : d * m = p * (d * m / p) + 1 := by
      have := Nat.div_add_mod (d * m) p
      omega
    have hxd : x ^ d ∈ Subgroup.normalizer (Y : Set Q) := mem_normalizer_iff_gLBConj_eq.2 hd
    have hxm : x = (x ^ d) ^ m := by
      rw [← pow_mul, hdm, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]
    have hxN : x ∈ Subgroup.normalizer (Y : Set Q) := by
      rw [hxm]
      exact pow_mem hxd m
    exact hxY (mem_normalizer_iff_gLBConj_eq.1 hxN)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact fun heq => key i j h hj heq
  · exact fun heq => key j i h hi heq.symm

theorem y10xA_iSup_O_normal {s : ℕ} {C : Subgroup G} {Yf : ℕ → Subgroup G}
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    (hYc : ∀ n, GLAPComponent s C (Yf n)) :
    ∀ o ∈ GLAPPrimeCoreOf s C, ∀ m ∈ ⨆ n, Yf n, o * m * o⁻¹ ∈ ⨆ n, Yf n :=
  fun o ho m hm => y10xA_iSup_conj_mem (C := GLAPPrimeCoreOf s C) (fun n => Yf n)
    (fun n o' ho' y hy => ⟨n, y10xA_O_conj_mem_comp (hYc n) hO ho' hy⟩) o ho m hm

end Conc11

section Conc12

variable {G : Type} [Group G] [Finite G]

theorem y10xA_centralizer_inv {Q : Type} [Group Q] (g : Q) :
    Subgroup.centralizer ({g⁻¹} : Set Q) = Subgroup.centralizer ({g} : Set Q) := by
  ext k
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

theorem y10xA_fam_conj_some {s : ℕ} {C K N : Subgroup G} [(N.subgroupOf C).Normal]
    (hKC : K ≤ C) (hKN : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G)) {c : G}
    (hc : c ∈ C) (Y : y10xA_I s C K) :
    (y10xA_fam s C K N (some Y)).map
        (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨c, hc⟩ : ↥C))).toMonoidHom =
      y10xA_img C N (K ⊓ (GLBConj c⁻¹ Y.1 ⊔ GLAPPrimeCoreOf s C)) := by
  have hKn : ∀ c' ∈ C, ∀ k ∈ K, c' * k * c'⁻¹ ∈ K := fun c' hc' k hk =>
    (Subgroup.mem_normalizer_iff.1 (hKN hc') k).1 hk
  have hYC : Y.1 ≤ C := Y.2.1.1
  have hY'C : GLBConj c⁻¹ Y.1 ≤ C := y10xA_gLBConj_le hc hYC
  refine y10xA_map_conj_img_of hc (inf_le_left.trans hKC) (inf_le_left.trans hKC)
    (fun h hh => y10xA_conj_P hKC hYC hKn hO hc h hh) (fun h hh => ?_)
  have key := y10xA_conj_P hKC hY'C hKn hO (C.inv_mem hc) h hh
  rw [inv_inv, gLBConj_gLBConj_inv] at key
  exact key

theorem lemma117_khat_concrete {s p : ℕ} (hs : s.Prime) (hp : p.Prime) {C J : Subgroup G} {x : G}
    (hxC : x ∈ C) (hx : x ^ p = 1) (hJC : J ≤ C) (hJlay : J ≤ GLAPLayer s C)
    (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJc : CFSG.Open.IsComponentOf J (C ⊓ Subgroup.centralizer ({x} : Set G)))
    (hsJ : s ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hNp : ⁅closureIn J C, GLAPPrimeCoreOf s (closureIn J C)⁆ ≤
      GLAPPrimeCoreOf p (closureIn J C)) :
    (∃ Y : Subgroup G, GLAPComponent s C Y ∧ J ≤ Y) ∨
      (∃ Y : Subgroup G, GLAPComponent s C Y ∧
        (∀ i j : ℕ, i < p → j < p → i ≠ j → GLBConj (x ^ i) Y ≠ GLBConj (x ^ j) Y) ∧
        J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y) := by
  classical
  set K : Subgroup G := closureIn J C with hK
  have hKC : K ≤ C := y10xA_closureIn_le hJC
  have hCK : C ≤ Subgroup.normalizer (K : Set G) := y10xA_closureIn_normalizer
  have hJK : J ≤ K := y10xA_le_closureIn C.one_mem
  have hKmin : ∀ X : Subgroup G, (∀ c ∈ C, ∀ y ∈ X, c * y * c⁻¹ ∈ X) → J ≤ X → K ≤ X :=
    fun X hX hJX => y10xA_closureIn_le_of hJX hX
  have hCn : C ≤ Subgroup.normalizer (C : Set G) := fun c hc => Subgroup.le_normalizer hc
  have hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G) :=
    fun c hc => normalizer_le_normalizer_glaPPrimeCoreOf s C (hCn hc)
  have hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun c hc k hk =>
    (Subgroup.mem_normalizer_iff.1 (hCK hc) k).1 hk
  have hKn' : (K.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).2 hCK
  set OK : Subgroup G := GLAPPrimeCoreOf s K with hOKdef
  have hOK_le : OK ≤ K := y10xA_coreOf_le K
  have hOKC : OK ≤ C := hOK_le.trans hKC
  have hOKn : C ≤ Subgroup.normalizer (OK : Set G) := fun c hc =>
    normalizer_le_normalizer_glaPPrimeCoreOf s K (hCK hc)
  set N : Subgroup G := ⁅K, OK⁆ with hNdef
  have hNK : N ≤ K := by
    show ⁅K, OK⁆ ≤ K
    exact Subgroup.commutator_le.2 fun a ha b hb => y10xA_comm_mem_gen ha (hOK_le hb)
  have hNs : N ≤ OK := by
    show ⁅K, OK⁆ ≤ OK
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    have h1 : a * b * a⁻¹ ∈ OK := (Subgroup.mem_normalizer_iff.1 (hOKn (hKC ha)) b).1 hb
    exact OK.mul_mem h1 (OK.inv_mem hb)
  have hNC : N ≤ C := hNK.trans hKC
  have hNnorm : C ≤ Subgroup.normalizer (N : Set G) := y10xA_comm_core_normalizer hCK
  have hNn : (N.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNC).2 hNnorm
  haveI hNinst : (N.subgroupOf C).Normal := hNn
  have hcommN : ∀ k ∈ K, ∀ t ∈ OK, ⁅k, t⁆ ∈ N := fun k hk t ht =>
    Subgroup.commutator_mem_commutator hk ht
  have hNp' : ¬ p ∣ Nat.card N := fun h =>
    not_dvd_card_glaPPrimeCoreOf hp K (h.trans (Subgroup.card_dvd_of_le hNp))
  have hJN : ¬ J ≤ N := by
    intro hJN'
    have h1 : J ≤ OK := hJN'.trans hNs
    have h2 : s ∣ Nat.card ↥J := by
      rw [← Subgroup.card_mul_index (Subgroup.center ↥J)]
      exact Dvd.dvd.mul_left hsJ _
    exact not_dvd_card_glaPPrimeCoreOf hs K (h2.trans (Subgroup.card_dvd_of_le h1))
  have hJs : CFSG.Open.IsSubnormal J (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
    have hJx : J ≤ K ⊓ Subgroup.centralizer ({x} : Set G) :=
      le_inf hJK (fun j hj => (hJc.1 hj).2)
    have h1 := CFSG.Open.IsSubnormal.inf hJc.2.1 (K ⊓ Subgroup.centralizer ({x} : Set G))
    rw [inf_eq_left.2 hJx, inf_eq_right.2 (inf_le_inf_right _ hKC)] at h1
    exact h1
  have hsubtr := lemma117_khat_transport hp hxC hx hKC hNK hNp' hJK hJq hJN hJs
  set σ : ↥C ⧸ N.subgroupOf C := QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C)
    with hσdef
  have hcn : ∀ n : ℕ, (x⁻¹) ^ n ∈ C := fun n => C.pow_mem (C.inv_mem hxC) n
  have hσpow : ∀ n : ℕ, σ ^ n =
      QuotientGroup.mk' (N.subgroupOf C) (⟨(x⁻¹) ^ n, hcn n⟩ : ↥C) := by
    intro n
    rw [hσdef, ← map_pow]
    rfl
  have hσp : σ ^ p = 1 := by
    rw [hσpow p]
    have h1 : (⟨(x⁻¹) ^ p, hcn p⟩ : ↥C) = 1 := Subtype.ext (by simp [inv_pow, hx])
    rw [h1, map_one]
  have hcent : Subgroup.centralizer ({σ} : Set (↥C ⧸ N.subgroupOf C)) =
      Subgroup.centralizer ({QuotientGroup.mk' (N.subgroupOf C) (⟨x, hxC⟩ : ↥C)} :
        Set (↥C ⧸ N.subgroupOf C)) := by
    have hσinv : σ = (QuotientGroup.mk' (N.subgroupOf C) (⟨x, hxC⟩ : ↥C))⁻¹ := by
      rw [hσdef, ← map_inv]
      rfl
    rw [hσinv]
    exact y10xA_centralizer_inv _
  have hĴ : CFSG.Open.IsComponentOf (y10xA_img C N J)
      (y10xA_img C N K ⊓ Subgroup.centralizer ({σ} : Set (↥C ⧸ N.subgroupOf C))) := by
    rw [hcent]
    exact hsubtr
  have hKX : K ≤ (⨆ Y : y10xA_I s C K, Y.1) ⊔ GLAPPrimeCoreOf s C :=
    hKmin _ (y10xA_sup_normalized hKC hCn hKn hO)
      (y10xA_J_le_sup hs hKC hJK hJC hJlay hKn' hJq)
  have hKP : K ≤ (⨆ Y : y10xA_I s C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) ⊔ OK :=
    y10xA_K_le_sup_P hs hKC hO hKX
  have hFK : y10xA_img C N K = ⨆ a : Option (y10xA_I s C K), y10xA_fam s C K N a :=
    y10xA_img_K_eq hKC hCK hO hKP
  have hĴ' : CFSG.Open.IsComponentOf (y10xA_img C N J)
      ((⨆ a : Option (y10xA_I s C K), y10xA_fam s C K N a) ⊓
        Subgroup.centralizer ({σ} : Set (↥C ⧸ N.subgroupOf C))) := by
    rw [← hFK]
    exact hĴ
  have hZc := y10xA_img_central (N := N) hKC hOK_le hcommN
  have hcommfam : ∀ a b : Option (y10xA_I s C K), a ≠ b →
      y10xA_Commute (y10xA_fam s C K N a) (y10xA_fam s C K N b) := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact absurd rfl hab
      | some Y' => exact fun u hu w hw => (hZc u hu w (y10xA_fam_le_img (some Y') hw)).symm
    | some Y =>
      cases b with
      | none => exact fun u hu w hw => hZc w hw u (y10xA_fam_le_img (some Y) hu)
      | some Y' =>
        have hne : Y'.1 ≠ Y.1 := fun h => hab (congrArg some (Subtype.ext h.symm))
        exact y10xA_img_P_commute hs hKC hO hcommN Y.2.1 Y.2.2 Y'.2.1 Y'.2.2 hne
  have hcomm' : ∀ a b : Option (y10xA_I s C K), y10xA_fam s C K N a ≠ y10xA_fam s C K N b →
      ⁅y10xA_fam s C K N a, y10xA_fam s C K N b⁆ = ⊥ := fun a b hne =>
    y10xA_bot_of_commute (hcommfam a b (fun h => hne (by rw [h])))
  have hσfam : ∀ a : Option (y10xA_I s C K), ∃ b : Option (y10xA_I s C K),
      (y10xA_fam s C K N a).map (MulAut.conj σ).toMonoidHom = y10xA_fam s C K N b :=
    fun a => y10xA_fam_conj hKC hCK hO (C.inv_mem hxC) a
  obtain ⟨i₀, -, hJ0⟩ := y10xA_single_orbit (fun a => y10xA_fam s C K N a) σ p hp.pos hσp
    (y10xA_img C N J) hcomm' hσfam hĴ'
  have hJq' : CFSG.Open.IsQuasisimple ↥(y10xA_img C N J) := hsubtr.2.2
  cases i₀ with
  | none =>
    exfalso
    have hnone : ∀ n : ℕ, (y10xA_fam s C K N none).map (MulAut.conj (σ ^ n)).toMonoidHom =
        y10xA_fam s C K N none := by
      intro n
      rw [hσpow n]
      exact y10xA_map_conj_img_of (hcn n) hOKC hOKC
        (fun h hh => (Subgroup.mem_normalizer_iff.1 (hOKn (hcn n)) h).1 hh)
        (fun h hh => by
          have h2 := (Subgroup.mem_normalizer_iff.1 (hOKn (C.inv_mem (hcn n))) h).1 hh
          rwa [inv_inv] at h2)
    have hJsub : y10xA_img C N J ≤ y10xA_img C N OK := by
      refine hJ0.trans (iSup_le fun n => ?_)
      exact le_of_eq (hnone n)
    have hbotOK : ⁅y10xA_img C N OK, y10xA_img C N OK⁆ = ⊥ := by
      apply y10xA_bot_of_commute
      intro u hu w hw
      exact hZc w hw u (y10xA_img_mono hOK_le hu)
    have hcontra : ⁅y10xA_img C N J, y10xA_img C N J⁆ ≤
        ⁅y10xA_img C N OK, y10xA_img C N OK⁆ := Subgroup.commutator_mono hJsub hJsub
    rw [y10xA_qs_comm_self hJq', hbotOK] at hcontra
    exact y10xA_qs_ne_bot hJq' (le_bot_iff.1 hcontra)
  | some Y₀ =>
    set Yn : ℕ → Subgroup G := fun n => GLBConj (x ^ n) Y₀.1 with hYn
    have hYnC : ∀ n, Yn n ≤ C := fun n => by
      have h1 := y10xA_gLBConj_le (C.inv_mem (C.pow_mem hxC n)) Y₀.2.1.1
      rwa [inv_inv] at h1
    have hYnc : ∀ n, GLAPComponent s C (Yn n) := fun n => by
      have h1 := glaPComponent_gLBConj Y₀.2.1 (x ^ n)
      have hCeq : GLBConj (x ^ n) C = C :=
        mem_normalizer_iff_gLBConj_eq.1 (hCn (C.pow_mem hxC n))
      rwa [hCeq] at h1
    set F : ℕ → Subgroup G := fun n => K ⊓ (Yn n ⊔ GLAPPrimeCoreOf s C) with hF
    have hFC : ∀ n, F n ≤ C := fun n => inf_le_left.trans hKC
    have hconj : ∀ n : ℕ, (y10xA_fam s C K N (some Y₀)).map (MulAut.conj (σ ^ n)).toMonoidHom =
        y10xA_img C N (F n) := by
      intro n
      rw [hσpow n, y10xA_fam_conj_some hKC hCK hO (hcn n) Y₀]
      have hc' : ((x⁻¹) ^ n)⁻¹ = x ^ n := by rw [inv_pow, inv_inv]
      rw [hc']
    have hiSup : (⨆ n : ℕ, (y10xA_fam s C K N (some Y₀)).map (MulAut.conj (σ ^ n)).toMonoidHom) =
        ⨆ n : ℕ, y10xA_img C N (F n) := iSup_congr fun n => hconj n
    have hJ1 : y10xA_img C N J ≤ ⨆ n : ℕ, y10xA_img C N (F n) := hJ0.trans (le_of_eq hiSup)
    have hOKle : OK ≤ GLAPPrimeCoreOf s C :=
      le_glaPPrimeCoreOf_of_le_normalizer hOKC hOKn
        ((Nat.Prime.coprime_iff_not_dvd hs).2 (not_dvd_card_glaPPrimeCoreOf hs K))
    have hMM : J ≤ (⨆ n : ℕ, Yn n) ⊔ GLAPPrimeCoreOf s C := by
      intro j hj
      have hz : QuotientGroup.mk' (N.subgroupOf C) (⟨j, hJC hj⟩ : ↥C) ∈ y10xA_img C N J :=
        Subgroup.mem_map.2 ⟨⟨j, hJC hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
      have hlift := y10xA_lift_iSup F hFC (hJ1 hz) j (hJC hj) rfl
      have hFN : (⨆ n : ℕ, F n) ⊔ N ≤ (⨆ n : ℕ, Yn n) ⊔ GLAPPrimeCoreOf s C :=
        sup_le (iSup_le fun n => inf_le_right.trans (sup_le_sup_right (le_iSup Yn n) _))
          ((hNs.trans hOKle).trans le_sup_right)
      exact hFN hlift
    have hMsub : (⨆ n : ℕ, Yn n) ≤ C := iSup_le hYnC
    have hMO := y10xA_iSup_O_normal hO hYnc
    have hMn : ∀ h ∈ (⨆ n : ℕ, Yn n), ∀ t ∈ GLAPPrimeCoreOf s C,
        h * t * h⁻¹ ∈ GLAPPrimeCoreOf s C := fun h hh t ht =>
      (Subgroup.mem_normalizer_iff.1 (hO (hMsub hh)) t).1 ht
    have hJM : J ≤ ⨆ n : ℕ, Yn n :=
      y10xA_le_of_le_sup_core hJq hsJ (not_dvd_card_glaPPrimeCoreOf hs C) hMO hMn hMM
    by_cases hfix : GLBConj x Y₀.1 = Y₀.1
    · left
      refine ⟨Y₀.1, Y₀.2.1, ?_⟩
      have hMY : (⨆ n : ℕ, Yn n) ≤ Y₀.1 := iSup_le fun n => le_of_eq (y10xA_pow_fix hfix n)
      exact hJM.trans hMY
    · right
      refine ⟨Y₀.1, Y₀.2.1, fun i j hi hj hij => y10xA_orbit_ne hp hx hfix hi hj hij, ?_⟩
      have hMle : (⨆ n : ℕ, Yn n) ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y₀.1 := by
        refine iSup_le fun n => ?_
        have hxn : x ^ n = x ^ (n % p) := by
          conv_lhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hx, one_pow, one_mul]
        show GLBConj (x ^ n) Y₀.1 ≤ _
        rw [hxn]
        exact le_iSup (fun i : Fin p => GLBConj (x ^ (i : ℕ)) Y₀.1) ⟨n % p, Nat.mod_lt n hp.pos⟩
      exact hJM.trans hMle

end Conc12

theorem dichotomy (hI25 : Input2_5) (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J) {x : G} (hp : p.Prime)
    (hx : x ^ p = 1) (hxx : x ∈ Subgroup.centralizer ({x'} : Set G))
    (hJc : IsComponentOf J (Subgroup.centralizer ({x'} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)))
    (hJp : J ≤ GLAPLayer p' (Subgroup.centralizer ({x'} : Set G)))
    (hJp' : J ≤ GLAPLayer p (Subgroup.centralizer ({x'} : Set G))) :
    (∃ Y : Subgroup G, GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) Y ∧ J ≤ Y) ∨
      (∃ Y : Subgroup G, GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) Y ∧
        (∀ i j : ℕ, i < p → j < p → i ≠ j → GLBConj (x ^ i) Y ≠ GLBConj (x ^ j) Y) ∧
        J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y) := by
  have hpp : p'.Prime := hc.cfg.prime
  have hJC : J ≤ Subgroup.centralizer ({x'} : Set G) := fun j hj => (hc.cfg.comp.1.1 hj).2
  have hJq : CFSG.Open.IsQuasisimple ↥J := hc.cfg.comp.1.2.2
  have hsJ : p' ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := (dvd_mul_left p' p).trans hc.cfg.dvd
  exact lemma117_khat_concrete hpp hp hxx hx hJC hJp hJq hJc hsJ (closureCore_le_oPPrimeP hctx hc hp hJp')

theorem y10xD_comm_center {A : Type} [Group A] (hperf : commutator A = ⊤) {a : A}
    (h : ∀ g : A, a * g * a⁻¹ * g⁻¹ ∈ Subgroup.center A) : a ∈ Subgroup.center A := by
  classical
  let φ : A →* Subgroup.center A :=
    { toFun := fun g => ⟨a * g * a⁻¹ * g⁻¹, h g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        have hcv : ∀ g : A, g * (a * v * a⁻¹ * v⁻¹) = (a * v * a⁻¹ * v⁻¹) * g := fun g =>
          (Subgroup.mem_center_iff.1 (h v)) g
        have e1 : a * u = (a * u * a⁻¹ * u⁻¹) * u * a := by group
        show a * (u * v) * a⁻¹ * (u * v)⁻¹ =
          (a * u * a⁻¹ * u⁻¹) * (a * v * a⁻¹ * v⁻¹)
        calc a * (u * v) * a⁻¹ * (u * v)⁻¹
            = (a * u) * v * a⁻¹ * v⁻¹ * u⁻¹ := by group
          _ = ((a * u * a⁻¹ * u⁻¹) * u * a) * v * a⁻¹ * v⁻¹ * u⁻¹ := by rw [← e1]
          _ = (a * u * a⁻¹ * u⁻¹) * (u * (a * v * a⁻¹ * v⁻¹) * u⁻¹) := by group
          _ = (a * u * a⁻¹ * u⁻¹) * (a * v * a⁻¹ * v⁻¹) := by
              rw [hcv u]
              group }
  have hcenter_comm : ∀ z w : Subgroup.center A, z * w = w * z := by
    intro z w
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.1 z.2 (w : A)).symm
  have hker : ∀ u v : A, φ ⁅u, v⁆ = 1 := by
    intro u v
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcenter_comm _ _)
  have hle : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ ≤ φ.ker :=
    Subgroup.commutator_le.2 fun u _ v _ => (MonoidHom.mem_ker).2 (hker u v)
  have htop : (⊤ : Subgroup A) ≤ φ.ker := by
    rw [← hperf]
    exact hle
  have hg : ∀ g : A, a * g = g * a := by
    intro g
    have h1 : φ g = 1 := (MonoidHom.mem_ker).1 (htop (Subgroup.mem_top g))
    have h2 : a * g * a⁻¹ * g⁻¹ = 1 := congrArg Subtype.val h1
    calc a * g = a * g * a⁻¹ * g⁻¹ * (g * a) := by group
      _ = g * a := by rw [h2, one_mul]
  exact Subgroup.mem_center_iff.2 fun g => (hg g).symm

theorem y10xD_preimage_center {A B : Type} [Group A] [Group B] {f : A →* B}
    (hperf : commutator A = ⊤) (hker : ∀ a, f a = 1 → a ∈ Subgroup.center A) {a : A}
    (ha : f a ∈ Subgroup.center B) : a ∈ Subgroup.center A := by
  refine y10xD_comm_center hperf fun g => hker _ ?_
  have hc : f g * f a = f a * f g := (Subgroup.mem_center_iff.1 ha) (f g)
  simp only [map_mul, map_inv]
  rw [← hc]
  group

theorem y10xD_commutator_surj {A B : Type} [Group A] [Group B] {f : A →* B}
    (hf : Function.Surjective f) (hperf : commutator A = ⊤) : commutator B = ⊤ := by
  have hsurj : Subgroup.map f (⊤ : Subgroup A) = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact (MonoidHom.range_eq_top).2 hf
  calc commutator B = ⁅Subgroup.map f ⊤, Subgroup.map f ⊤⁆ := by rw [hsurj]; rfl
    _ = Subgroup.map f ⁅(⊤ : Subgroup A), ⊤⁆ := (Subgroup.map_commutator _ _ _).symm
    _ = Subgroup.map f ⊤ := by rw [show ⁅(⊤ : Subgroup A), ⊤⁆ = ⊤ from hperf]
    _ = ⊤ := hsurj

theorem y10xD_quot_equiv {A B : Type} [Group A] [Group B] {f : A →* B}
    (hf : Function.Surjective f) (hperf : commutator A = ⊤)
    (hker : ∀ a, f a = 1 → a ∈ Subgroup.center A) :
    Nonempty ((A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B)) := by
  have hcen : Subgroup.center A ≤ (Subgroup.center B).comap f := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := hf y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) g]
  let φ : A ⧸ Subgroup.center A →* B ⧸ Subgroup.center B :=
    QuotientGroup.map (Subgroup.center A) (Subgroup.center B) f hcen
  have hbij : Function.Bijective φ := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      have h1 : (f a)⁻¹ * f b ∈ Subgroup.center B := by
        have h2 : (QuotientGroup.mk (f a) : B ⧸ Subgroup.center B) =
            QuotientGroup.mk (f b) := hxy
        exact QuotientGroup.eq.1 h2
      rw [QuotientGroup.eq]
      apply y10xD_preimage_center hperf hker (f := f)
      rw [map_mul, map_inv]
      exact h1
    · intro y
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨a, rfl⟩ := hf b
      exact ⟨QuotientGroup.mk a, rfl⟩
  exact ⟨MulEquiv.ofBijective φ hbij⟩

theorem y10xD_isQuasisimple_iff {A B : Type} [Group A] [Group B] {f : A →* B}
    (hf : Function.Surjective f) (hperf : commutator A = ⊤)
    (hker : ∀ a, f a = 1 → a ∈ Subgroup.center A) :
    CFSG.Open.IsQuasisimple A ↔ CFSG.Open.IsQuasisimple B := by
  obtain ⟨e⟩ := y10xD_quot_equiv hf hperf hker
  constructor
  · intro h
    obtain ⟨-, h2⟩ := h
    exact ⟨y10xD_commutator_surj hf hperf, (MulEquiv.isSimpleGroup_congr e).1 h2⟩
  · intro h
    obtain ⟨-, h2⟩ := h
    exact ⟨hperf, (MulEquiv.isSimpleGroup_congr e).2 h2⟩

theorem y10xD_marking_transfer {A B : Type} [Group A] [Group B] (lab₀ : CFSG.Assembly.LargeEvenLabel)
    (hA : commutator A = ⊤) (e : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B)
    (hM : GLAMarking B (fun lab _ _ _ _ _ => lab = lab₀)) :
    GLAMarking A (fun lab _ _ _ _ _ => lab = lab₀) := by
  obtain ⟨-, lab, hlab, hraw⟩ := hM
  refine ⟨hA, lab, hlab, ?_⟩
  have hiff : ∀ (R : Type) [Group R] (I F : Set (MulAut R)),
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : B ⧸ Subgroup.center B ≃* R, lab = lab₀) ↔
        (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : A ⧸ Subgroup.center A ≃* R, lab = lab₀) := by
    intro R _ I F
    constructor
    · rintro ⟨h1, h2, θ, h3⟩
      exact ⟨h1, h2, ⟨e.trans θ, h3⟩⟩
    · rintro ⟨h1, h2, θ, h3⟩
      exact ⟨h1, h2, ⟨e.symm.trans θ, h3⟩⟩
  have hfun : (fun (R : Type) (_ : Group R) (I F : Set (MulAut R)) =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : B ⧸ Subgroup.center B ≃* R, lab = lab₀) =
      (fun (R : Type) (_ : Group R) (I F : Set (MulAut R)) =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : A ⧸ Subgroup.center A ≃* R, lab = lab₀) :=
    funext fun R => funext fun inst => funext fun I => funext fun F =>
      propext (hiff R I F)
  rw [hfun] at hraw
  exact hraw

theorem y10xD_card_pow {Δ : Type} [Group Δ] [Finite Δ] {r : ℕ} (hr : r.Prime) {E : Subgroup Δ}
    (hE : CFSG.Open.IsElemAbelian r E) : ∃ n : ℕ, Nat.card E = r ^ n := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hP : IsPGroup r ↥E := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hg : (g : Δ) ^ r = 1 := hE.2 g g.2
    have hd : orderOf g ∣ r := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hg
    rcases (Nat.dvd_prime hr).1 hd with h1 | h1
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h1, pow_one]⟩
  exact IsPGroup.iff_card.1 hP

theorem y10xD_pRank_le_card {Δ : Type} [Group Δ] [Finite Δ] {r : ℕ} (hr : r.Prime)
    (H : Subgroup Δ) : CFSG.Open.pRank r H ≤ Nat.card Δ := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hr.one_lt H
  have h1 : CFSG.Open.pRank r H < r ^ CFSG.Open.pRank r H := Nat.lt_pow_self hr.one_lt
  have h2 : Nat.card E ≤ Nat.card Δ := Subgroup.card_le_card_group E
  rw [hE] at h2
  omega

theorem y10xD_tlr_bdd {Δ : Type} [Group Δ] [Finite Δ] {r : ℕ} (hr : r.Prime) :
    BddAbove {k | ∃ H : Subgroup Δ, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank r H = k} := by
  refine ⟨Nat.card Δ, ?_⟩
  rintro k ⟨H, -, rfl⟩
  exact y10xD_pRank_le_card hr H

theorem y10xD_le_tlr {Δ : Type} [Group Δ] [Finite Δ] {r : ℕ} (hr : r.Prime) {H : Subgroup Δ}
    (hH : CFSG.Open.IsTwoLocal H) : CFSG.Open.pRank r H ≤ CFSG.Open.GLATwoLocalRank r Δ :=
  le_csSup (y10xD_tlr_bdd hr) ⟨H, hH, rfl⟩

theorem y10xD_tlr_attained {Δ : Type} [Group Δ] [Finite Δ] {r : ℕ} (hr : r.Prime)
    {H : Subgroup Δ} (hH : CFSG.Open.IsTwoLocal H) :
    ∃ K : Subgroup Δ, CFSG.Open.IsTwoLocal K ∧
      CFSG.Open.pRank r K = CFSG.Open.GLATwoLocalRank r Δ := by
  have hmem := Nat.sSup_mem
    (s := {k | ∃ K : Subgroup Δ, CFSG.Open.IsTwoLocal K ∧ CFSG.Open.pRank r K = k})
    ⟨_, H, hH, rfl⟩ (y10xD_tlr_bdd hr)
  obtain ⟨K, hK, hKeq⟩ := hmem
  exact ⟨K, hK, hKeq⟩

theorem y10xD_normalizer_map {Δ Γ : Type} [Group Δ] [Group Γ] (φ : Δ →* Γ)
    (hφ : Function.Injective φ) {P : Subgroup Δ} {g : Δ}
    (hg : g ∈ Subgroup.normalizer (P : Set Δ)) :
    φ g ∈ Subgroup.normalizer ((P.map φ : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  constructor
  · intro hh
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hh
    refine Subgroup.mem_map.2 ⟨g * x * g⁻¹, (hg x).1 hx, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · intro hh
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hh
    refine Subgroup.mem_map.2 ⟨g⁻¹ * y * g, ?_, ?_⟩
    · apply (hg (g⁻¹ * y * g)).2
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [e]
      exact hy
    · rw [map_mul, map_mul, map_inv, hyeq]
      group

theorem y10xD_le_normalizer_of_comm {Γ : Type} [Group Γ] {A B : Subgroup Γ}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ Subgroup.normalizer (A : Set Γ) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hc : h * e = e * h := hcomm h hh e he
    have : e * h * e⁻¹ = h := by
      rw [← hc]
      group
    rw [this]
    exact hh
  · intro hh
    have hqe : (e * h * e⁻¹) * e = e * (e * h * e⁻¹) := hcomm _ hh e he
    have h2 : e * h = e * (e * h * e⁻¹) := by
      rw [← hqe]
      group
    have h3 : h = e * h * e⁻¹ := mul_left_cancel h2
    rw [h3]
    exact hh

theorem y10xD_count {Γ : Type} [Group Γ] [Finite Γ] {r : ℕ} (hr : r.Prime)
    (H₀ H₁ : Subgroup Γ) (hcomm : ∀ a ∈ H₀, ∀ b ∈ H₁, a * b = b * a)
    (t : Γ) (htH : t ∈ H₀) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (E₁ : Subgroup Γ) (hE₁H : E₁ ≤ H₁) (hE₁ : CFSG.Open.IsElemAbelian r E₁)
    (hE₁card : Nat.card E₁ = r ^ CFSG.Open.pRank r (⊤ : Subgroup ↥H₀)) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥H₀) + CFSG.Open.GLATwoLocalRank r ↥H₀ ≤
      CFSG.Open.GLATwoLocalRank r Γ + CFSG.Open.pRank r (Subgroup.center ↥H₀) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  let g0 : ↥H₀ := ⟨t, htH⟩
  have hg0 : g0 ^ 2 = 1 := Subtype.ext (by simpa using ht2)
  have hg0ne : g0 ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hP0 : Subgroup.zpowers g0 ≠ ⊥ := by
    intro h
    apply hg0ne
    have hmem : g0 ∈ Subgroup.zpowers g0 := Subgroup.mem_zpowers g0
    rw [h] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hloc0 : CFSG.Open.IsTwoLocal (Subgroup.normalizer ((Subgroup.zpowers g0 : Subgroup ↥H₀) : Set ↥H₀)) :=
    ⟨Subgroup.zpowers g0, hP0, y10xA_isPGroup_zpowers Nat.prime_two hg0, rfl⟩
  obtain ⟨H, hHloc, hHa⟩ := y10xD_tlr_attained (Δ := ↥H₀) hr hloc0
  obtain ⟨P1, hP1ne, hP1p, hHeq⟩ := hHloc
  obtain ⟨Ā₀, hĀ₀H, hĀ₀el, hĀ₀card⟩ := CFSG.SectionRank.exists_pRank hr.one_lt H
  rw [hHa] at hĀ₀card
  let φ : ↥H₀ →* Γ := H₀.subtype
  have hφinj : Function.Injective φ := Subtype.val_injective
  have hĀH₀ : Ā₀.map φ ≤ H₀ := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact x.2
  have hĀel : CFSG.Open.IsElemAbelian r (Ā₀.map φ) := CFSG.SectionRank.isElemAbelian_map hĀ₀el φ
  have hĀcard : Nat.card ↥(Ā₀.map φ) = r ^ CFSG.Open.GLATwoLocalRank r ↥H₀ := by
    rw [Subgroup.card_map_of_injective hφinj, hĀ₀card]
  have hPH₀ : P1.map φ ≤ H₀ := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact x.2
  have hPne : P1.map φ ≠ ⊥ := by
    intro h
    apply hP1ne
    rw [Subgroup.map_eq_bot_iff] at h
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : φ x = 1 := (MonoidHom.mem_ker).1 (h hx)
    exact Subgroup.mem_bot.2 (hφinj (hx'.trans (map_one φ).symm))
  have hPp : IsPGroup 2 ↥(P1.map φ) := IsPGroup.map hP1p φ
  have hĀN : Ā₀.map φ ≤ Subgroup.normalizer ((P1.map φ : Subgroup Γ) : Set Γ) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have hxN : x ∈ Subgroup.normalizer (P1 : Set ↥H₀) := by
      rw [← hHeq]
      exact hĀ₀H hx
    exact y10xD_normalizer_map φ hφinj hxN
  have hcommĀE : ∀ a ∈ Ā₀.map φ, ∀ b ∈ E₁, a * b = b * a :=
    fun a ha b hb => hcomm a (hĀH₀ ha) b (hE₁H hb)
  have hcommPE : ∀ a ∈ P1.map φ, ∀ b ∈ E₁, a * b = b * a :=
    fun a ha b hb => hcomm a (hPH₀ ha) b (hE₁H hb)
  have hE₁N : E₁ ≤ Subgroup.normalizer ((P1.map φ : Subgroup Γ) : Set Γ) :=
    y10xD_le_normalizer_of_comm (A := P1.map φ) (B := E₁) hcommPE
  have hE₁NĀ : E₁ ≤ Subgroup.normalizer ((Ā₀.map φ : Subgroup Γ) : Set Γ) :=
    y10xD_le_normalizer_of_comm (A := Ā₀.map φ) (B := E₁) hcommĀE
  set Ā : Subgroup Γ := Ā₀.map φ with hĀdef
  set P : Subgroup Γ := P1.map φ with hPdef
  set M : Subgroup Γ := Ā ⊔ E₁ with hMdef
  have hMN : M ≤ Subgroup.normalizer (P : Set Γ) := by
    refine sup_le hĀN hE₁N
  set W : Subgroup ↥H₀ := (Ā ⊓ E₁).comap φ with hWdef
  have hWmap : W.map φ = Ā ⊓ E₁ := by
    ext y
    constructor
    · intro hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.mem_comap.1 hw
    · intro hy
      have hy0 : y ∈ H₀ := hĀH₀ (Subgroup.mem_inf.1 hy).1
      exact Subgroup.mem_map.2 ⟨⟨y, hy0⟩, Subgroup.mem_comap.2 hy, rfl⟩
  have hWcomm : ∀ x y : Γ, x ∈ Ā ⊓ E₁ → y ∈ Ā ⊓ E₁ → x * y = y * x := fun x y hx hy =>
    isElemAbelian_commute hĀel (Subgroup.mem_inf.1 hx).1 (Subgroup.mem_inf.1 hy).1
  have hWcen : W ≤ Subgroup.center ↥H₀ := by
    intro w hw
    have hw' : φ w ∈ Ā ⊓ E₁ := Subgroup.mem_comap.1 hw
    have hwE : φ w ∈ E₁ := (Subgroup.mem_inf.1 hw').2
    rw [Subgroup.mem_center_iff]
    intro x
    apply hφinj
    rw [map_mul, map_mul]
    exact hcomm (φ x) x.2 (φ w) (hE₁H hwE)
  have hWmem : ∀ x : ↥W, φ (x : ↥H₀) ∈ Ā ⊓ E₁ := fun x => by
    rw [← hWmap]
    exact Subgroup.mem_map_of_mem φ x.2
  have hWel : CFSG.Open.IsElemAbelian r W := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hφinj ?_)⟩⟩, ?_⟩
    · simp only [Subgroup.coe_mul]
      exact hWcomm _ _ (hWmem x) (hWmem y)
    · intro x hx
      apply hφinj
      rw [map_pow, map_one]
      exact hĀel.2 _ (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hx)).1
  have hWcard : Nat.card ↥W = Nat.card ↥(Ā ⊓ E₁) := by
    rw [← hWmap, Subgroup.card_map_of_injective hφinj]
  obtain ⟨j, hj⟩ := y10xD_card_pow hr hWel
  have hjz : j ≤ CFSG.Open.pRank r (Subgroup.center ↥H₀) :=
    CFSG.SectionRank.le_pRank hr.one_lt hWcen hWel hj
  have hIcard : Nat.card ↥(Ā ⊓ E₁) = r ^ j := by
    rw [← hWcard, hj]
  have hcommĀE' : ∀ a ∈ Ā, ∀ b ∈ E₁, a * b = b * a := hcommĀE
  have hCom : y10xA_Commute Ā E₁ := by
    refine y10xA_commute_of_bot (Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun a ha => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hcommĀE' a ha e he).symm
  have hMcomm : ∀ u v : Γ, u ∈ M → v ∈ M → u * v = v * u := by
    intro u v hu hv
    obtain ⟨a1, ha1, e1, he1, rfl⟩ := y10xA_mem_sup_of_commute (A := Ā) (B := E₁) hCom hu
    obtain ⟨a2, ha2, e2, he2, rfl⟩ := y10xA_mem_sup_of_commute (A := Ā) (B := E₁) hCom hv
    have c1 : Commute e1 a2 := show e1 * a2 = a2 * e1 from (hcommĀE' a2 ha2 e1 he1).symm
    have c2 : Commute e2 a1 := show e2 * a1 = a1 * e2 from (hcommĀE' a1 ha1 e2 he2).symm
    rw [c1.mul_mul_mul_comm a1 e2, c2.mul_mul_mul_comm a2 e1,
      isElemAbelian_commute hĀel ha1 ha2, isElemAbelian_commute hE₁ he1 he2]
  have hMel : CFSG.Open.IsElemAbelian r M := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hMcomm x y x.2 y.2)⟩⟩, fun x hx => ?_⟩
    obtain ⟨a, ha, e, he, rfl⟩ := y10xA_mem_sup_of_commute (A := Ā) (B := E₁) hCom hx
    rw [(show Commute a e from hcommĀE' a ha e he).mul_pow, hĀel.2 a ha, hE₁.2 e he, one_mul]
  obtain ⟨k, hk⟩ := y10xD_card_pow hr hMel
  have hMcard_mul : Nat.card ↥M * Nat.card ↥(Ā ⊓ E₁) = Nat.card ↥Ā * Nat.card ↥E₁ :=
    card_sup_mul_card_inf_of_le_normalizer hE₁NĀ
  have hkj : k + j = CFSG.Open.GLATwoLocalRank r ↥H₀ + CFSG.Open.pRank r (⊤ : Subgroup ↥H₀) := by
    have h1 : r ^ (k + j) = r ^ (CFSG.Open.GLATwoLocalRank r ↥H₀ +
        CFSG.Open.pRank r (⊤ : Subgroup ↥H₀)) := by
      rw [pow_add, pow_add, ← hk, ← hIcard, ← hĀcard, ← hE₁card]
      exact hMcard_mul
    exact Nat.pow_right_injective hr.two_le h1
  have hPp : IsPGroup 2 ↥P := IsPGroup.map hP1p φ
  have hNP : CFSG.Open.IsTwoLocal (Subgroup.normalizer (P : Set Γ)) := ⟨P, hPne, hPp, rfl⟩
  have hkB : CFSG.Open.pRank r M ≤ CFSG.Open.GLATwoLocalRank r Γ :=
    (CFSG.SectionRank.pRank_mono hr.one_lt hMN).trans (y10xD_le_tlr hr hNP)
  have hkle : k ≤ CFSG.Open.pRank r M :=
    CFSG.SectionRank.le_pRank hr.one_lt (le_refl M) hMel hk
  omega

theorem y10xD_commutator_le_of_le {Γ : Type} [Group Γ] {H L : Subgroup Γ} (h : H ≤ L) :
    ⁅H, H⁆ ≤ L :=
  Subgroup.commutator_le.2 fun u hu v hv => by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem (h hu) (h hv)) (L.inv_mem (h hu))) (L.inv_mem (h hv))

theorem y10xD_commutator_iSup_le {Γ : Type} [Group Γ] {ι : Type} (A : ι → Subgroup Γ)
    (hA : ∀ i j, A i ≠ A j → ⁅A i, A j⁆ = ⊥) :
    ⁅⨆ i, A i, ⨆ i, A i⁆ ≤ ⨆ i, ⁅A i, A i⁆ := by
  classical
  set T : Subgroup Γ := ⨆ i, ⁅A i, A i⁆ with hT
  have hpiece : ∀ i j, ∀ a ∈ A i, ∀ t ∈ ⁅A j, A j⁆, a * t * a⁻¹ ∈ ⁅A j, A j⁆ := by
    intro i j a ha t ht
    by_cases hij : A i = A j
    · rw [← hij] at ht ⊢
      have hmapA : (A i).map (MulAut.conj a).toMonoidHom ≤ A i := by
        rintro _ ⟨y, hy, rfl⟩
        exact (A i).mul_mem ((A i).mul_mem ha hy) ((A i).inv_mem ha)
      have hle : (⁅A i, A i⁆ : Subgroup Γ).map (MulAut.conj a).toMonoidHom ≤ ⁅A i, A i⁆ := by
        rw [Subgroup.map_commutator]
        exact Subgroup.commutator_mono hmapA hmapA
      exact hle ⟨t, ht, rfl⟩
    · have hc := hA i j hij
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
      have hac : a ∈ Subgroup.centralizer (A j : Set Γ) := hc ha
      have hAjL : A j ≤ Subgroup.centralizer ({a} : Set Γ) := by
        intro u hu
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 hac) u hu
      have h1 := (y10xD_commutator_le_of_le hAjL) ht
      rw [Subgroup.mem_centralizer_singleton_iff] at h1
      have e : a * t * a⁻¹ = t := by
        rw [← h1]
        group
      rw [e]
      exact ht
  have hgen : ∀ i j, ∀ a ∈ A i, ∀ b ∈ A j, ⁅a, b⁆ ∈ T := by
    intro i j a ha b hb
    by_cases hij : A i = A j
    · have hb' : b ∈ A i := by
        rw [hij]
        exact hb
      exact (le_iSup (fun k => ⁅A k, A k⁆) i) (Subgroup.commutator_mem_commutator ha hb')
    · have hc := hA i j hij
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
      have hcomm_ab : b * a = a * b := (Subgroup.mem_centralizer_iff.1 (hc ha)) b hb
      have h1 : ⁅a, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hcomm_ab.symm
      rw [h1]
      exact T.one_mem
  have hTnorm : ∀ x ∈ ⨆ i, A i, ∀ t ∈ T, x * t * x⁻¹ ∈ T := by
    intro x hx
    refine Subgroup.iSup_induction A (C := fun x => ∀ t ∈ T, x * t * x⁻¹ ∈ T) hx ?_ ?_ ?_
    · intro i a ha t ht
      refine Subgroup.iSup_induction (fun k => ⁅A k, A k⁆) (C := fun t => a * t * a⁻¹ ∈ T) ht ?_ ?_ ?_
      · intro j t' ht'
        exact (le_iSup (fun k => ⁅A k, A k⁆) j) (hpiece i j a ha t' ht')
      · simp only [mul_one, mul_inv_cancel]
        exact T.one_mem
      · intro t1 t2 h1 h2
        have e : a * (t1 * t2) * a⁻¹ = (a * t1 * a⁻¹) * (a * t2 * a⁻¹) := by group
        rw [e]
        exact T.mul_mem h1 h2
    · intro t ht
      simpa using ht
    · intro x y hx' hy' t ht
      have h1 := hy' t ht
      have h2 := hx' _ h1
      have e : x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
      rw [e]
      exact h2
  have hall : ∀ x ∈ ⨆ i, A i, ∀ y ∈ ⨆ i, A i, ⁅x, y⁆ ∈ T := by
    intro x hx
    refine Subgroup.iSup_induction' A (C := fun x _ => ∀ y ∈ ⨆ i, A i, ⁅x, y⁆ ∈ T) ?_ ?_ ?_ hx
    · intro i a ha y hy
      refine Subgroup.iSup_induction' A (C := fun y _ => ⁅a, y⁆ ∈ T) ?_ ?_ ?_ hy
      · intro j b hb
        exact hgen i j a ha b hb
      · simp only [commutatorElement_one_right]
        exact T.one_mem
      · intro y1 y2 hy1 hy2 h1 h2
        have e : ⁅a, y1 * y2⁆ = ⁅a, y1⁆ * (y1 * ⁅a, y2⁆ * y1⁻¹) := by
          rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
          group
        rw [e]
        exact T.mul_mem h1 (hTnorm y1 hy1 _ h2)
    · intro y _
      simp only [commutatorElement_one_left]
      exact T.one_mem
    · intro x1 x2 hx1 hx2 h1 h2 y hy
      have e : ⁅x1 * x2, y⁆ = (x1 * ⁅x2, y⁆ * x1⁻¹) * ⁅x1, y⁆ := by
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
        group
      rw [e]
      exact T.mul_mem (hTnorm x1 hx1 _ (h2 y hy)) (h1 y hy)
  exact Subgroup.commutator_le.2 fun x hx y hy => hall x hx y hy

theorem y10xD_comp_top {Γ : Type} [Group Γ] {X L : Subgroup Γ}
    (hL : CFSG.Open.IsComponentOf L X) : CFSG.Open.IsComponentOf (L.subgroupOf X) ⊤ := by
  obtain ⟨hLX, hsub, hq⟩ := hL
  exact ⟨le_top, CFSG.Open.IsSubnormal.top_iff.2 hsub.subgroupOf,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLX) hq⟩

theorem y10xD_B_comp {Γ : Type} [Group Γ] (B : ℕ → Subgroup Γ)
    (hqs : ∀ m, CFSG.Open.IsQuasisimple ↥(B m))
    (hcomm : ∀ m m', B m ≠ B m' → ⁅B m, B m'⁆ = ⊥) (m : ℕ) :
    CFSG.Open.IsComponentOf (B m) (⨆ m, B m) := by
  have hBX : ∀ m, B m ≤ ⨆ m, B m := fun m => le_iSup B m
  have hnormX : ∀ m, (⨆ m, B m) ≤ Subgroup.normalizer (B m : Set Γ) := by
    intro m
    refine iSup_le fun j => ?_
    by_cases hj : B j = B m
    · rw [hj]
      exact Subgroup.le_normalizer
    · have hc := hcomm m j (fun h => hj h.symm)
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
      exact y10xD_le_normalizer_of_comm (A := B m) (B := B j) fun a ha b hb =>
        ((Subgroup.mem_centralizer_iff.1 (hc ha)) b hb).symm
  have hBnorm : ((B m).subgroupOf (⨆ m, B m)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hBX m)).2 (hnormX m)
  exact ⟨hBX m, CFSG.Open.IsSubnormal.step (hBX m) hBnorm (CFSG.Open.IsSubnormal.refl _), hqs m⟩

theorem y10xD_comp_eq_B {Γ : Type} [Group Γ] [Finite Γ] (B : ℕ → Subgroup Γ)
    (hqs : ∀ m, CFSG.Open.IsQuasisimple ↥(B m))
    (hcomm : ∀ m m', B m ≠ B m' → ⁅B m, B m'⁆ = ⊥)
    {L : Subgroup Γ} (hL : CFSG.Open.IsComponentOf L (⨆ m, B m)) : ∃ m, L = B m := by
  classical
  by_contra hne
  push_neg at hne
  have hLX : L ≤ ⨆ m, B m := hL.1
  have hLB : ∀ m, ∀ a ∈ L, ∀ b ∈ B m, a * b = b * a := by
    intro m a ha b hb
    have hne' : L.subgroupOf (⨆ m, B m) ≠ (B m).subgroupOf (⨆ m, B m) := by
      intro e
      apply hne m
      have h2 := congrArg (Subgroup.map (⨆ m, B m).subtype) e
      rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.2 hLX, inf_eq_left.2 (le_iSup B m)] at h2
      exact h2
    have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
      (y10xD_comp_top hL) (y10xD_comp_top (y10xD_B_comp B hqs hcomm m)) hne'
    have ha' : (⟨a, hLX ha⟩ : ↥(⨆ m, B m)) ∈ L.subgroupOf (⨆ m, B m) :=
      Subgroup.mem_subgroupOf.2 ha
    have hb' : (⟨b, le_iSup B m hb⟩ : ↥(⨆ m, B m)) ∈ (B m).subgroupOf (⨆ m, B m) :=
      Subgroup.mem_subgroupOf.2 hb
    have hcm := Subgroup.commutator_mem_commutator ha' hb'
    rw [hc, Subgroup.mem_bot] at hcm
    exact congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.1 hcm)
  have hLX' : ∀ a ∈ L, ∀ b ∈ ⨆ m, B m, a * b = b * a := by
    intro a ha b hb
    refine Subgroup.iSup_induction B (C := fun b => a * b = b * a) hb ?_ ?_ ?_
    · intro m b hb'
      exact hLB m a ha b hb'
    · simp
    · intro b1 b2 h1 h2
      calc a * (b1 * b2) = (a * b1) * b2 := (mul_assoc _ _ _).symm
        _ = (b1 * a) * b2 := by rw [h1]
        _ = b1 * (a * b2) := mul_assoc _ _ _
        _ = b1 * (b2 * a) := by rw [h2]
        _ = (b1 * b2) * a := (mul_assoc _ _ _).symm
  have hLab : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := fun a ha b hb => hLX' a ha b (hLX hb)
  have hsimp := hL.2.2.2
  have hcenter : Subgroup.center ↥L = ⊤ := by
    refine eq_top_iff.2 fun a _ => Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
    exact hLab g.1 g.2 a.1 a.2
  have hss : Subsingleton (↥L ⧸ Subgroup.center ↥L) := by
    rw [hcenter]
    exact QuotientGroup.subsingleton_quotient_top
  exact (not_nontrivial_iff_subsingleton.2 hss) hsimp.toNontrivial

theorem y10xD_mem_GLBConj {Γ : Type} [Group Γ] (g : Γ) (H : Subgroup Γ) {h : Γ} (hh : h ∈ H) :
    g * h * g⁻¹ ∈ GLBConj g⁻¹ H :=
  Subgroup.mem_map.2 ⟨h, hh, by simp [MulAut.conj_apply]⟩

theorem y10xD_input25_B {Γ : Type} [Group Γ] [Finite Γ] (hI25 : Input2_5) {p : ℕ} (hp : p.Prime)
    (σ : Γ) (hσp : σ ^ p = 1) (B : ℕ → Subgroup Γ)
    (hqs : ∀ m, CFSG.Open.IsQuasisimple ↥(B m))
    (hcomm : ∀ m m', B m ≠ B m' → ⁅B m, B m'⁆ = ⊥)
    (hconj : ∀ m, GLBConj σ (B m) = B (m + 1))
    (hper : ∀ m, B (m + p) = B m)
    (hdist : ∀ m m', B m = B m' → m % p = m' % p)
    {X₁ : Subgroup Γ} (hX₁ : CFSG.Open.IsComponentOf X₁ (⨆ m, B m)) :
    ∃ (Z : Subgroup ↥X₁) (_ : Z.Normal), Z ≤ Subgroup.center ↥X₁ ∧
      Nonempty (↥(CFSG.Open.GLALayer ((⨆ m, B m) ⊓ Subgroup.centralizer
        ((Subgroup.zpowers σ : Subgroup Γ) : Set Γ))) ≃* (↥X₁ ⧸ Z)) := by
  classical
  have hp1 : 1 ≤ p := hp.one_le
  have hBper : ∀ a n, B (a + p * n) = B a := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show a + p * (n + 1) = (a + p * n) + p by ring, hper, ih]
  have hgen : ∀ m, GLBConj σ⁻¹ (B m) ≤ ⨆ m, B m := by
    intro m
    rcases m with _ | k
    · have hB0 : B 0 = B (p - 1 + 1) := by
        have : p - 1 + 1 = 0 + p := by omega
        rw [this, hper 0]
      have h0 : GLBConj σ⁻¹ (B 0) = B (p - 1) := by
        rw [hB0, ← hconj (p - 1), gLBConj_inv_gLBConj]
      rw [h0]
      exact le_iSup B _
    · rw [← hconj k, gLBConj_inv_gLBConj]
      exact le_iSup B k
  have hsX : ∀ h ∈ ⨆ m, B m, σ * h * σ⁻¹ ∈ ⨆ m, B m := by
    intro h hh
    refine Subgroup.iSup_induction B (C := fun h => σ * h * σ⁻¹ ∈ ⨆ m, B m) hh ?_ ?_ ?_
    · intro m h hh'
      exact hgen m (y10xD_mem_GLBConj σ (B m) hh')
    · simp
    · intro h1 h2 e1 e2
      have e : σ * (h1 * h2) * σ⁻¹ = (σ * h1 * σ⁻¹) * (σ * h2 * σ⁻¹) := by group
      rw [e]
      exact (⨆ m, B m).mul_mem e1 e2
  have hsX' : ∀ h ∈ ⨆ m, B m, σ⁻¹ * h * σ ∈ ⨆ m, B m := by
    intro h hh
    refine Subgroup.iSup_induction B (C := fun h => σ⁻¹ * h * σ ∈ ⨆ m, B m) hh ?_ ?_ ?_
    · intro m h hh'
      have hmem : σ⁻¹ * h * σ⁻¹⁻¹ ∈ GLBConj σ (B m) :=
        Subgroup.mem_map.2 ⟨h, hh', by simp [MulAut.conj_apply]⟩
      rw [hconj m] at hmem
      exact le_iSup B (m + 1) (by simpa using hmem)
    · simp
    · intro h1 h2 e1 e2
      have e : σ⁻¹ * (h1 * h2) * σ = (σ⁻¹ * h1 * σ) * (σ⁻¹ * h2 * σ) := by group
      rw [e]
      exact (⨆ m, B m).mul_mem e1 e2
  have hσN : σ ∈ Subgroup.normalizer ((⨆ m, B m : Subgroup Γ) : Set Γ) := by
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hsX h hh, fun hh => ?_⟩
    have e : σ⁻¹ * (σ * h * σ⁻¹) * σ = h := by group
    rw [← e]
    exact hsX' _ hh
  have hnorm : Subgroup.zpowers σ ≤ Subgroup.normalizer ((⨆ m, B m : Subgroup Γ) : Set Γ) :=
    Subgroup.zpowers_le.2 hσN
  have hel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers σ) := by
    refine ⟨Subgroup.zpowers_isMulCommutative σ, fun e he => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσp, one_zpow]
  have hlayer : CFSG.Open.GLALayer (⨆ m, B m) = ⨆ m, B m := by
    apply le_antisymm
    · exact sSup_le fun K hK => hK.1
    · exact iSup_le fun m => le_sSup (y10xD_B_comp B hqs hcomm m)
  have hpow : ∀ n m, GLBConj (σ ^ n) (B m) = B (m + n) := by
    intro n
    induction n with
    | zero => intro m; simp [gLBConj_one]
    | succ n ih =>
      intro m
      rw [pow_succ, ← gLBConj_gLBConj, ih, hconj]
      rw [show m + n + 1 = m + (n + 1) by ring]
  have htrans : ∀ L L' : Subgroup Γ, CFSG.Open.IsComponentOf L (⨆ m, B m) →
      CFSG.Open.IsComponentOf L' (⨆ m, B m) → ∃ e ∈ Subgroup.zpowers σ, GLBConj e L = L' := by
    intro L L' hL hL'
    obtain ⟨m, rfl⟩ := y10xD_comp_eq_B B hqs hcomm hL
    obtain ⟨m', rfl⟩ := y10xD_comp_eq_B B hqs hcomm hL'
    refine ⟨σ ^ (m' + (p - 1) * m), (Subgroup.zpowers σ).pow_mem (Subgroup.mem_zpowers σ) _, ?_⟩
    rw [hpow]
    have e : m + (m' + (p - 1) * m) = m' + p * m := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, hBper]
  have hfree : ∀ e ∈ Subgroup.zpowers σ, e ≠ 1 → ∀ L : Subgroup Γ,
      CFSG.Open.IsComponentOf L (⨆ m, B m) → GLBConj e L ≠ L := by
    intro e he hne' L hL heq
    obtain ⟨m, rfl⟩ := y10xD_comp_eq_B B hqs hcomm hL
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 he)
    rw [hpow] at heq
    have hmod := hdist _ _ heq
    have hdvd : p ∣ n := by
      have h1 : m + n ≡ m [MOD p] := hmod
      have h2 : n ≡ 0 [MOD p] :=
        Nat.ModEq.add_left_cancel' m (show m + n ≡ m + 0 [MOD p] by simpa using h1)
      exact Nat.modEq_zero_iff_dvd.1 h2
    apply hne'
    obtain ⟨c, rfl⟩ := hdvd
    rw [pow_mul, hσp, one_pow]
  obtain ⟨h1, -⟩ := hI25 Γ p hp (⨆ m, B m) (Subgroup.zpowers σ) hlayer hnorm hel htrans hfree
  exact h1 X₁ hX₁

theorem y10xD_not_comm {Δ : Type} [Group Δ] (h : CFSG.Open.IsQuasisimple Δ) :
    ¬ (∀ a b : Δ, a * b = b * a) := by
  intro hc
  obtain ⟨-, hsimp⟩ := h
  have hcen : Subgroup.center Δ = ⊤ :=
    eq_top_iff.2 fun a _ => Subgroup.mem_center_iff.2 fun g => hc g a
  have hss : Subsingleton (Δ ⧸ Subgroup.center Δ) := by
    rw [hcen]
    exact QuotientGroup.subsingleton_quotient_top
  exact (not_nontrivial_iff_subsingleton.2 hss) hsimp.toNontrivial

theorem y10xD_glbConj_le {G : Type} [Group G] {C H : Subgroup G} {g : G} (hg : g ∈ C)
    (hH : H ≤ C) : GLBConj g H ≤ C := by
  intro z hz
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hz
  exact C.mul_mem (C.mul_mem (C.inv_mem hg) (hH hh)) (by simpa using hg)

theorem y10xD_barX_qs {G : Type} [Group G] [Finite G] {s : ℕ} {C J : Subgroup G} (hs : s.Prime)
    (hJC : J ≤ C) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hsJ : s ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    CFSG.Open.IsQuasisimple ↥(barX s C J) := by
  classical
  let φ : ↥J →* (↥C ⧸ GLAPPrimeCore s ↥C) :=
    (QuotientGroup.mk' (GLAPPrimeCore s ↥C)).comp (Subgroup.inclusion hJC)
  have hφ : ∀ j : ↥J, φ j ∈ barX s C J := fun j =>
    Subgroup.mem_map.2 ⟨⟨j.1, hJC j.2⟩, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
  let f : ↥J →* ↥(barX s C J) := φ.codRestrict (barX s C J) hφ
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
    refine ⟨⟨c.1, Subgroup.mem_subgroupOf.1 hc⟩, ?_⟩
    apply Subtype.ext
    rfl
  let NJ : Subgroup ↥J := (GLAPPrimeCoreOf s C).comap J.subtype
  have hNJn : NJ.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : (g : G) * (n : G) * (g : G)⁻¹ ∈ GLAPPrimeCoreOf s C :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf s C (hJC g.2)) (n : G)).1 hn
    show ((g * n * g⁻¹ : ↥J) : G) ∈ GLAPPrimeCoreOf s C
    simpa using h1
  have hNJne : NJ ≠ ⊤ := by
    intro htop
    have hJO : J ≤ GLAPPrimeCoreOf s C := by
      intro j hj
      have hmem : (⟨j, hj⟩ : ↥J) ∈ NJ := htop ▸ Subgroup.mem_top _
      exact hmem
    have hsJ' : s ∣ Nat.card ↥J := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)]
      exact Dvd.dvd.mul_right hsJ _
    exact not_dvd_card_glaPPrimeCoreOf hs C (hsJ'.trans (Subgroup.card_dvd_of_le hJO))
  have hNJc : NJ ≤ Subgroup.center ↥J :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hJq NJ hNJne
  have hker : ∀ a : ↥J, f a = 1 → a ∈ Subgroup.center ↥J := by
    intro a ha
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore s ↥C) (Subgroup.inclusion hJC a) :
        ↥C ⧸ GLAPPrimeCore s ↥C) = 1 := congrArg Subtype.val ha
    have h2 : (a : G) ∈ GLAPPrimeCoreOf s C :=
      y10xA_of_mem_core (hJC a.2) ((QuotientGroup.eq_one_iff _).1 h1)
    exact hNJc (show a ∈ NJ from h2)
  exact (y10xD_isQuasisimple_iff hf hJq.1 hker).1 hJq

theorem y10xD_barX_shift {G : Type} [Group G] [Finite G] {s : ℕ} {C J Q : Subgroup G} {x : G}
    (hJC : J ≤ C) (hJx : J ≤ Subgroup.centralizer ({x} : Set G)) (hxC : x ∈ C)
    (h : ∃ a ∈ barX s C Q, ∃ b ∈ barX s C J, a * b ≠ b * a) :
    ∃ a ∈ barX s C (GLBConj x Q), ∃ b ∈ barX s C J, a * b ≠ b * a := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := h
  set c : ↥C ⧸ GLAPPrimeCore s ↥C := QuotientGroup.mk' (GLAPPrimeCore s ↥C) ⟨x, hxC⟩ with hc
  refine ⟨c⁻¹ * a * c, ?_, b, hb, ?_⟩
  · rw [barX_gLBConj_eq s hxC Q]
    exact Subgroup.mem_map.2 ⟨a, ha, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; rfl⟩
  · intro h2
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hb
    have hzJ : z.1 ∈ J := Subgroup.mem_subgroupOf.1 hz
    have hcb : c * QuotientGroup.mk' (GLAPPrimeCore s ↥C) z =
        QuotientGroup.mk' (GLAPPrimeCore s ↥C) z * c := by
      rw [hc, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show x * z.1 = z.1 * x
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hJx hzJ)).symm
    apply hab
    set b' := QuotientGroup.mk' (GLAPPrimeCore s ↥C) z with hb'
    have h3 : c * (c⁻¹ * a * c * b') = c * (b' * (c⁻¹ * a * c)) := by rw [h2]
    have h4 : a * c * b' = b' * a * c := by
      calc a * c * b' = c * (c⁻¹ * a * c * b') := by group
        _ = c * (b' * (c⁻¹ * a * c)) := h3
        _ = (c * b') * (c⁻¹ * a * c) := by group
        _ = (b' * c) * (c⁻¹ * a * c) := by rw [hcb]
        _ = b' * a * c := by group
    have h5 : a * b' * c = b' * a * c := by
      calc a * b' * c = a * (b' * c) := by group
        _ = a * (c * b') := by rw [hcb]
        _ = a * c * b' := by group
        _ = b' * a * c := h4
    exact mul_right_cancel h5

theorem y10xD_barX_exists {G : Type} [Group G] [Finite G] {s p : ℕ} {C J : Subgroup G} {x : G}
    {Y : Subgroup G} (hs : s.Prime) (hJC : J ≤ C) (hJx : J ≤ Subgroup.centralizer ({x} : Set G))
    (hxC : x ∈ C) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hsJ : s ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hJY : J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y) (hYC : Y ≤ C) :
    ∃ i : ℕ, i < p ∧ ∃ a ∈ barX s C (GLBConj (x ^ i) Y), ∃ b ∈ barX s C J, a * b ≠ b * a := by
  classical
  by_contra hno
  push_neg at hno
  have hqs := y10xD_barX_qs (s := s) hs hJC hJq hsJ
  have hF : ∀ i : Fin p, GLBConj (x ^ (i : ℕ)) Y ≤ C := fun i =>
    y10xD_glbConj_le (C.pow_mem hxC _) hYC
  have hsub : barX s C J ≤ ⨆ i : Fin p, barX s C (GLBConj (x ^ (i : ℕ)) Y) := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨hyC, hmem⟩ := y10xA_barX_iSup_mem (s := s) (fun i : Fin p => GLBConj (x ^ (i : ℕ)) Y)
      hF (hJY (Subgroup.mem_subgroupOf.1 hj))
    exact hmem
  have hcomm_all : ∀ z ∈ ⨆ i : Fin p, barX s C (GLBConj (x ^ (i : ℕ)) Y),
      ∀ w ∈ barX s C J, z * w = w * z := by
    intro z hz w hw
    refine Subgroup.iSup_induction (fun i : Fin p => barX s C (GLBConj (x ^ (i : ℕ)) Y))
      (C := fun z => z * w = w * z) hz ?_ ?_ ?_
    · intro i z hz'
      exact hno i i.2 z hz' w hw
    · simp
    · intro z1 z2 h1 h2
      calc z1 * z2 * w = z1 * (z2 * w) := by rw [mul_assoc]
        _ = z1 * (w * z2) := by rw [h2]
        _ = (z1 * w) * z2 := by rw [mul_assoc]
        _ = (w * z1) * z2 := by rw [h1]
        _ = w * (z1 * z2) := by rw [mul_assoc]
  apply y10xD_not_comm (y10xD_barX_qs (s := s) hs hJC hJq hsJ)
  intro a b
  apply Subtype.ext
  exact hcomm_all a.1 (hsub a.2) b.1 b.2

theorem y10xD_barX_noncomm {G : Type} [Group G] [Finite G] {s p : ℕ} {C J : Subgroup G} {x : G}
    {Y : Subgroup G} (hs : s.Prime) (hp : 0 < p) (hJC : J ≤ C)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set G)) (hxC : x ∈ C) (hxp : x ^ p = 1)
    (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hsJ : s ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hJY : J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y) (hYC : Y ≤ C) (m : ℕ) :
    ∃ a ∈ barX s C (GLBConj (x ^ m) Y), ∃ b ∈ barX s C J, a * b ≠ b * a := by
  obtain ⟨i, hi, hiP⟩ := y10xD_barX_exists hs hJC hJx hxC hJq hsJ hJY hYC
  have hshift : ∀ k : ℕ, ∃ a ∈ barX s C (GLBConj (x ^ (i + k)) Y), ∃ b ∈ barX s C J,
      a * b ≠ b * a := by
    intro k
    induction k with
    | zero => simpa using hiP
    | succ k ih =>
      have h1 := y10xD_barX_shift (s := s) hJC hJx hxC ih
      have e2 : GLBConj x (GLBConj (x ^ (i + k)) Y) = GLBConj (x ^ (i + (k + 1))) Y := by
        rw [gLBConj_gLBConj, show i + (k + 1) = (i + k) + 1 by ring, pow_succ]
      rw [e2] at h1
      exact h1
  obtain ⟨a, ha, b, hb, hab⟩ := hshift (m + p - i)
  have e : i + (m + p - i) = m + p := by omega
  rw [e, pow_add, hxp, mul_one] at ha
  exact ⟨a, ha, b, hb, hab⟩

section Gamma

variable {G : Type} [Group G] [Finite G] {s : ℕ}

def y10xD_proj {C N : Subgroup G} [hN : (N.subgroupOf C).Normal] (hNO : N ≤ GLAPPrimeCoreOf s C) :
    (↥C ⧸ N.subgroupOf C) →* (↥C ⧸ GLAPPrimeCore s ↥C) :=
  QuotientGroup.map (N.subgroupOf C) (GLAPPrimeCore s ↥C) (MonoidHom.id ↥C) (fun c hc => by
    rw [Subgroup.mem_comap, MonoidHom.id_apply]
    exact y10xA_mem_core (hNO (Subgroup.mem_subgroupOf.1 hc)) c.2)

theorem y10xD_proj_mk {C N : Subgroup G} [hN : (N.subgroupOf C).Normal]
    (hNO : N ≤ GLAPPrimeCoreOf s C) (c : ↥C) :
    y10xD_proj (s := s) hNO (QuotientGroup.mk' (N.subgroupOf C) c) =
      QuotientGroup.mk' (GLAPPrimeCore s ↥C) c := by
  simp [y10xD_proj]

theorem y10xD_map_proj {C N H : Subgroup G} [hN : (N.subgroupOf C).Normal]
    (hNO : N ≤ GLAPPrimeCoreOf s C) (hHC : H ≤ C) :
    (y10xA_img C N H).map (y10xD_proj (s := s) hNO) = barX s C H := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨c, hc, rfl⟩ := y10xA_exists_of_mem_img hw
    rw [y10xD_proj_mk]
    exact Subgroup.mem_map.2 ⟨c, Subgroup.mem_subgroupOf.2 hc, rfl⟩
  · intro hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
    refine Subgroup.mem_map.2 ⟨QuotientGroup.mk' (N.subgroupOf C) c,
      y10xA_mem_img c.2 (Subgroup.mem_subgroupOf.1 hc), ?_⟩
    rw [y10xD_proj_mk]

abbrev y10xD_Yhat (s : ℕ) {C N K Y : Subgroup G} [hN : (N.subgroupOf C).Normal] :
    Subgroup (↥C ⧸ N.subgroupOf C) :=
  y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C))

abbrev y10xD_Bhat (s : ℕ) {C N K Y : Subgroup G} [hN : (N.subgroupOf C).Normal] :
    Subgroup (↥C ⧸ N.subgroupOf C) :=
  ⁅y10xD_Yhat s (C := C) (N := N) (K := K) (Y := Y), y10xD_Yhat s (C := C) (N := N) (K := K) (Y := Y)⁆

theorem y10xD_commutator_top_of_self {Δ : Type} [Group Δ] {B : Subgroup Δ} (h : ⁅B, B⁆ = B) :
    commutator ↥B = ⊤ := by
  apply Subgroup.map_injective (f := B.subtype) Subtype.val_injective
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  calc Subgroup.map B.subtype (commutator ↥B) = ⁅Subgroup.map B.subtype ⊤, Subgroup.map B.subtype ⊤⁆ :=
        Subgroup.map_commutator _ _ _
    _ = B := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]; exact h

theorem y10xD_img_eq {C N H : Subgroup G} [hN : (N.subgroupOf C).Normal] :
    y10xA_img C N H = (H.subgroupOf C).map (QuotientGroup.mk' (N.subgroupOf C)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨c, hc, rfl⟩ := y10xA_exists_of_mem_img hz
    exact Subgroup.mem_map.2 ⟨c, Subgroup.mem_subgroupOf.2 hc, rfl⟩
  · intro hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
    exact y10xA_mem_img c.2 (Subgroup.mem_subgroupOf.1 hc)

theorem y10xD_Bhat_perfect {C K N Y : Subgroup G} [hN : (N.subgroupOf C).Normal] (hs : s.Prime)
    (hKC : K ≤ C) (hcommN : ∀ k ∈ K, ∀ t ∈ GLAPPrimeCoreOf s K, ⁅k, t⁆ ∈ N)
    (hY : GLAPComponent s C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C) :
    ⁅y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y),
      y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y)⁆ =
      y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y) := by
  classical
  have hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf s C
  have hTK : GLAPPrimeCoreOf s K ≤ K := y10xA_coreOf_le K
  have hZc := y10xA_img_central (N := N) hKC hTK hcommN
  have hZS : y10xA_img C N (GLAPPrimeCoreOf s K) ≤ y10xA_img C N K := y10xA_img_mono hTK
  have hAS : ((K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)).subgroupOf C).map
      (QuotientGroup.mk' (N.subgroupOf C)) ≤ y10xA_img C N K := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
    exact y10xA_mem_img c.2 ((inf_le_left : K ⊓ (Y ⊔ GLAPPrimeCoreOf s C) ≤ K)
      (Subgroup.mem_subgroupOf.1 hc))
  have hdec : ∀ p ∈ (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)).subgroupOf C, ∃ d ∈
      ⁅(K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)).subgroupOf C, (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)).subgroupOf C⁆,
        ∃ o : ↥C, QuotientGroup.mk' (N.subgroupOf C) o ∈ y10xA_img C N (GLAPPrimeCoreOf s K) ∧
          p = d * o := by
    intro p hp
    obtain ⟨d, hd, o, ho, hpeq⟩ := y10xA_perf_decomp hs hKC hO hY hYK
      (p := p) (Subgroup.mem_subgroupOf.1 hp)
    exact ⟨d, hd, o, y10xA_mem_img o.2 ho, hpeq⟩
  have hperf := y10xA_perfect_image (QuotientGroup.mk' (N.subgroupOf C)) hZc hAS hZS hdec
  show ⁅⁅y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)), y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C))⁆,
      ⁅y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)), y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C))⁆⁆ =
      ⁅y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)), y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C))⁆
  rw [y10xD_img_eq, ← Subgroup.map_commutator]
  exact hperf

theorem y10xD_Bhat_proj {C K N Y : Subgroup G} [hN : (N.subgroupOf C).Normal] (hs : s.Prime)
    (hKC : K ≤ C) (hNO : N ≤ GLAPPrimeCoreOf s C) (hY : GLAPComponent s C Y)
    (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C) :
    (y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y)).map (y10xD_proj (s := s) hNO) =
      barX s C Y := by
  have hYC : Y ≤ C := hY.1
  have hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf s C
  have hPC : K ⊓ (Y ⊔ GLAPPrimeCoreOf s C) ≤ C := inf_le_left.trans hKC
  have hPY : barX s C (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)) = barX s C Y := by
    apply le_antisymm
    · intro z hz
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
      have hpY : (c : G) ∈ Y ⊔ GLAPPrimeCoreOf s C :=
        (inf_le_right : K ⊓ (Y ⊔ GLAPPrimeCoreOf s C) ≤ Y ⊔ GLAPPrimeCoreOf s C)
          (Subgroup.mem_subgroupOf.1 hc)
      obtain ⟨y, hyC, hy, heq⟩ := y10xA_mk_mem_barX_of_sup hYC hO c.2 hpY
      have heq' : QuotientGroup.mk' (GLAPPrimeCore s ↥C) c =
          QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨y, hyC⟩ : ↥C) := heq
      rw [heq']
      exact Subgroup.mem_map.2 ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
    · exact y10xA_barX_le_P hKC hYC hYK hO
  have hcomm_self : ⁅barX s C Y, barX s C Y⁆ = barX s C Y :=
    y10xA_qs_comm_self (y10xA_barX_isComponent hY).2.2
  show (⁅y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)),
      y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C))⁆).map (y10xD_proj (s := s) hNO) =
      barX s C Y
  rw [Subgroup.map_commutator, y10xD_map_proj hNO hPC, hPY, hcomm_self]

theorem y10xD_Bhat_qs {C K N Y : Subgroup G} [hN : (N.subgroupOf C).Normal] (hs : s.Prime)
    (hKC : K ≤ C) (hcommN : ∀ k ∈ K, ∀ t ∈ GLAPPrimeCoreOf s K, ⁅k, t⁆ ∈ N)
    (hNO : N ≤ GLAPPrimeCoreOf s C) (hY : GLAPComponent s C Y)
    (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C) :
    CFSG.Open.IsQuasisimple ↥(y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y)) := by
  have hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf s C
  have hTK : GLAPPrimeCoreOf s K ≤ K := y10xA_coreOf_le K
  have hZc := y10xA_img_central (N := N) hKC hTK hcommN
  have hproj := y10xD_Bhat_proj (C := C) (N := N) (Y := Y) hs hKC hNO hY hYK
  have hperf : commutator ↥(y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y)) = ⊤ :=
    y10xD_commutator_top_of_self (y10xD_Bhat_perfect hs hKC hcommN hY hYK)
  have hBleS : y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y) ≤ y10xA_img C N K :=
    y10xD_commutator_le_of_le (y10xA_img_mono inf_le_left)
  let B := y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y)
  have hmem : ∀ b : ↥B, (y10xD_proj (s := s) hNO) (b : (↥C ⧸ N.subgroupOf C)) ∈
      barX s C Y := fun b => by
    rw [← hproj]
    exact Subgroup.mem_map.2 ⟨b.1, b.2, rfl⟩
  let f : ↥B →* ↥(barX s C Y) :=
    ((y10xD_proj (s := s) hNO).comp B.subtype).codRestrict (barX s C Y) hmem
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ B.map (y10xD_proj (s := s) hNO) := by
      rw [hproj]
      exact hz
    obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.1 hz'
    exact ⟨⟨b, hb⟩, Subtype.ext hbz⟩
  have hker : ∀ a : ↥B, f a = 1 → a ∈ Subgroup.center ↥B := by
    intro a ha
    have h1 : (y10xD_proj (s := s) hNO) a.1 = 1 := congrArg Subtype.val ha
    obtain ⟨c, hcK, hc⟩ := y10xA_exists_of_mem_img (hBleS a.2)
    have h2 : (c : G) ∈ GLAPPrimeCoreOf s C := by
      have h3 : (y10xD_proj (s := s) hNO) (QuotientGroup.mk' (N.subgroupOf C) c) = 1 := by
        rw [hc]
        exact h1
      rw [y10xD_proj_mk] at h3
      exact y10xA_of_mem_core c.2 ((QuotientGroup.eq_one_iff _).1 h3)
    have h4 : (c : G) ∈ GLAPPrimeCoreOf s K := y10xA_inf_le_coreK hs hKC hO ⟨hcK, h2⟩
    have hZ : a.1 ∈ y10xA_img C N (GLAPPrimeCoreOf s K) := by
      rw [← hc]
      exact y10xA_mem_img c.2 h4
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hZc a.1 hZ g.1 (hBleS g.2))
  exact (y10xD_isQuasisimple_iff hsurj hperf hker).2 (y10xA_barX_isComponent hY).2.2

end Gamma

section Family

variable {G : Type} [Group G] [Finite G]

theorem y10xD_img_K_eq {s : ℕ} {C K N : Subgroup G} [hN : (N.subgroupOf C).Normal] (hs : s.Prime)
    (hKC : K ≤ C) (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    (hKX : K ≤ (⨆ Y : y10xA_I s C K, Y.1) ⊔ GLAPPrimeCoreOf s C) :
    y10xA_img C N K = ⨆ i : Option (y10xA_I s C K), y10xA_fam s C K N i := by
  classical
  have hKP := y10xA_K_le_sup_P hs hKC hO hKX
  let F' : Option (y10xA_I s C K) → Subgroup G := fun i =>
    match i with
    | none => GLAPPrimeCoreOf s K
    | some Y => K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)
  have hF'C : ∀ i, F' i ≤ C := by
    intro i
    cases i with
    | none => exact (y10xA_coreOf_le K).trans hKC
    | some Y => exact inf_le_left.trans hKC
  have hsup : (⨆ Y : y10xA_I s C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) ⊔ GLAPPrimeCoreOf s K =
      ⨆ i, F' i := by
    rw [iSup_option, sup_comm]
  have hfam : (fun i : Option (y10xA_I s C K) => y10xA_img C N (F' i)) =
      fun i => y10xA_fam s C K N i := by
    funext i
    cases i <;> rfl
  apply le_antisymm
  · intro z hz
    obtain ⟨c, hc, rfl⟩ := y10xA_exists_of_mem_img hz
    have hcX : (c : G) ∈ ⨆ i, F' i := hsup ▸ hKP hc
    obtain ⟨hcC, hmem⟩ := y10xA_img_iSup_mem (C := C) (N := N) F' hF'C hcX
    have hm : QuotientGroup.mk' (N.subgroupOf C) c ∈ ⨆ i, y10xA_img C N (F' i) := hmem
    rw [hfam] at hm
    exact hm
  · refine iSup_le fun i => ?_
    cases i with
    | none => exact y10xA_img_mono ((y10xA_coreOf_le K))
    | some Y => exact y10xA_img_mono inf_le_left

theorem y10xD_fam_conj {s : ℕ} {C K N Y : Subgroup G} [hN : (N.subgroupOf C).Normal]
    (hKC : K ≤ C) (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    {x : G} (hxC : x ∈ C) (hYc : GLAPComponent s C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C) :
    ∃ Y' : y10xA_I s C K, Y'.1 = GLBConj x Y ∧
      (y10xA_fam s C K N (some ⟨Y, hYc, hYK⟩)).map
        (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C))).toMonoidHom =
        y10xA_fam s C K N (some Y') := by
  have hYC : Y ≤ C := hYc.1
  have hxN : x ∈ Subgroup.normalizer ((C : Subgroup G) : Set G) := Subgroup.le_normalizer hxC
  have hY'c : GLAPComponent s C (GLBConj x Y) := by
    have h := glaPComponent_gLBConj hYc x
    rwa [gLBConj_eq_of_mem_normalizer hxN] at h
  have hY'K : GLBConj x Y ≤ K ⊔ GLAPPrimeCoreOf s C := by
    have hKx : GLBConj x K = K := gLBConj_eq_of_mem_normalizer (hCK hxC)
    have hOx : GLBConj x (GLAPPrimeCoreOf s C) = GLAPPrimeCoreOf s C :=
      gLBConj_eq_of_mem_normalizer (hO hxC)
    calc GLBConj x Y ≤ GLBConj x (K ⊔ GLAPPrimeCoreOf s C) := gLBConj_mono (g := x) hYK
      _ = GLBConj x K ⊔ GLBConj x (GLAPPrimeCoreOf s C) := by
          unfold GLBConj
          exact Subgroup.map_sup _ _ _
      _ = K ⊔ GLAPPrimeCoreOf s C := by rw [hKx, hOx]
  refine ⟨⟨GLBConj x Y, hY'c, hY'K⟩, rfl, ?_⟩
  have hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun c hc k hk =>
    (Subgroup.mem_normalizer_iff.1 (hCK hc) k).1 hk
  have hH : ∀ h ∈ K ⊓ (Y ⊔ GLAPPrimeCoreOf s C),
      x⁻¹ * h * x⁻¹⁻¹ ∈ K ⊓ (GLBConj x Y ⊔ GLAPPrimeCoreOf s C) := by
    intro h hh
    have := y10xA_conj_P hKC hYC hKn hO (C.inv_mem hxC) h hh
    rw [inv_inv] at this ⊢
    exact this
  have hH' : ∀ h ∈ K ⊓ (GLBConj x Y ⊔ GLAPPrimeCoreOf s C),
      x⁻¹⁻¹ * h * x⁻¹ ∈ K ⊓ (Y ⊔ GLAPPrimeCoreOf s C) := by
    intro h hh
    have hY'C : GLBConj x Y ≤ C := y10xD_glbConj_le hxC hYC
    have := y10xA_conj_P hKC hY'C hKn hO hxC h hh
    rw [gLBConj_inv_gLBConj] at this
    rw [inv_inv]
    exact this
  exact y10xA_map_conj_img_of (C.inv_mem hxC) (inf_le_left.trans hKC) (inf_le_left.trans hKC)
    hH hH'

theorem y10xD_Fam_comm {s : ℕ} {C K N : Subgroup G} [hN : (N.subgroupOf C).Normal] (hs : s.Prime)
    (hKC : K ≤ C) (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    (hcommN : ∀ k ∈ K, ∀ t ∈ GLAPPrimeCoreOf s K, ⁅k, t⁆ ∈ N) (i j : Option (y10xA_I s C K))
    (hij : y10xA_fam s C K N i ≠ y10xA_fam s C K N j) :
    ⁅y10xA_fam s C K N i, y10xA_fam s C K N j⁆ = ⊥ := by
  have hTK : GLAPPrimeCoreOf s K ≤ K := y10xA_coreOf_le K
  have hZc := y10xA_img_central (N := N) hKC hTK hcommN
  have hsubK : ∀ Y : y10xA_I s C K, y10xA_img C N (K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) ≤
      y10xA_img C N K := fun Y => y10xA_img_mono inf_le_left
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  cases i with
  | none =>
    cases j with
    | none => exact absurd rfl hij
    | some Y' =>
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hZc u hu v (hsubK Y' hv)
  | some Y =>
    cases j with
    | none =>
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hZc v hv u (hsubK Y hu)).symm
    | some Y' =>
      have hne : Y'.1 ≠ Y.1 := fun h => hij (by
        show y10xA_img C N (K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf s C)) =
          y10xA_img C N (K ⊓ (Y'.1 ⊔ GLAPPrimeCoreOf s C))
        rw [h])
      have hc := y10xA_img_P_commute hs hKC hO hcommN Y.2.1 Y.2.2 Y'.2.1 Y'.2.2 hne
      have hbot := y10xA_bot_of_commute hc
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot hu) v hv

theorem y10xD_Fam_sigma {s : ℕ} {C K N : Subgroup G} [hN : (N.subgroupOf C).Normal]
    (hKC : K ≤ C) (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    {x : G} (hxC : x ∈ C) (i : Option (y10xA_I s C K)) :
    ∃ j, (y10xA_fam s C K N i).map
        (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C))).toMonoidHom =
        y10xA_fam s C K N j := by
  cases i with
  | none =>
    refine ⟨none, ?_⟩
    have hN' : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s K : Subgroup G) : Set G) :=
      fun c hc => normalizer_le_normalizer_glaPPrimeCoreOf s K (hCK hc)
    have hH : ∀ h ∈ GLAPPrimeCoreOf s K, x⁻¹ * h * x⁻¹⁻¹ ∈ GLAPPrimeCoreOf s K := fun h hh =>
      (Subgroup.mem_normalizer_iff.1 (hN' (C.inv_mem hxC)) h).1 hh
    have hH' : ∀ h ∈ GLAPPrimeCoreOf s K, x⁻¹⁻¹ * h * x⁻¹ ∈ GLAPPrimeCoreOf s K := by
      intro h hh
      rw [inv_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hN' hxC) h).1 hh
    exact y10xA_map_conj_img_of (C.inv_mem hxC) ((y10xA_coreOf_le K).trans hKC)
      ((y10xA_coreOf_le K).trans hKC) hH hH'
  | some Y =>
    obtain ⟨Y', -, hY'⟩ := y10xD_fam_conj (s := s) (N := N) hKC hCK hO hxC Y.2.1 Y.2.2
    exact ⟨some Y', hY'⟩

end Family

section Gamma2

variable {G : Type} [Group G] [Finite G] {s : ℕ}


theorem y10xD_barX_P_eq {s : ℕ} {C K Y : Subgroup G} (hKC : K ≤ C) (hY : GLAPComponent s C Y)
    (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C) :
    barX s C (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)) = barX s C Y := by
  have hYC : Y ≤ C := hY.1
  have hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf s C
  apply le_antisymm
  · intro z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
    have hpY : (c : G) ∈ Y ⊔ GLAPPrimeCoreOf s C :=
      (inf_le_right : K ⊓ (Y ⊔ GLAPPrimeCoreOf s C) ≤ Y ⊔ GLAPPrimeCoreOf s C)
        (Subgroup.mem_subgroupOf.1 hc)
    obtain ⟨y, hyC, hy, heq⟩ := y10xA_mk_mem_barX_of_sup hYC hO c.2 hpY
    have heq' : QuotientGroup.mk' (GLAPPrimeCore s ↥C) c =
        QuotientGroup.mk' (GLAPPrimeCore s ↥C) (⟨y, hyC⟩ : ↥C) := heq
    rw [heq']
    exact Subgroup.mem_map.2 ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  · exact y10xA_barX_le_P hKC hYC hYK hO

theorem y10xD_le_of_noncomm {s : ℕ} {C K J Y : Subgroup G} (hKC : K ≤ C) (hJK : J ≤ K)
    (hY : GLAPComponent s C Y) (hKn : (K.subgroupOf C).Normal)
    (hnc : ∃ a ∈ barX s C Y, ∃ b ∈ barX s C J, a * b ≠ b * a) :
    Y ≤ K ⊔ GLAPPrimeCoreOf s C := by
  have hYC : Y ≤ C := hY.1
  have hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf s C
  rcases y10xA_cn_mod hY hKn with h | h
  · exact y10xA_le_sup_of_barX_le hKC hYC h
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    apply hab
    have hbK : b ∈ barX s C K := by
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hb
      exact Subgroup.mem_map.2 ⟨j, Subgroup.mem_subgroupOf.2 (hJK (Subgroup.mem_subgroupOf.1 hj)),
        rfl⟩
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h ha
    exact ((Subgroup.mem_centralizer_iff.1 hc) b hbK).symm

theorem y10xD_Bhat_comm {s : ℕ} {C K N Y Y' : Subgroup G} [hN : (N.subgroupOf C).Normal]
    (hs : s.Prime) (hKC : K ≤ C) (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    (hcommN : ∀ k ∈ K, ∀ t ∈ GLAPPrimeCoreOf s K, ⁅k, t⁆ ∈ N)
    (hY : GLAPComponent s C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C)
    (hY' : GLAPComponent s C Y') (hYK' : Y' ≤ K ⊔ GLAPPrimeCoreOf s C) (hne : Y' ≠ Y) :
    ⁅y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y),
      y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y')⁆ = ⊥ := by
  have hc := y10xA_img_P_commute hs hKC hO hcommN hY hYK hY' hYK' hne
  have hbot := y10xA_bot_of_commute hc
  refine eq_bot_iff.2 ?_
  have hle : ⁅y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y),
      y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y')⁆ ≤
      ⁅y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)),
        y10xA_img C N (K ⊓ (Y' ⊔ GLAPPrimeCoreOf s C))⁆ :=
    Subgroup.commutator_mono (y10xD_commutator_le_of_le le_rfl)
      (y10xD_commutator_le_of_le le_rfl)
  exact hle.trans hbot.le

theorem y10xD_Bhat_inj {s : ℕ} {C K N Y Y' : Subgroup G} [hN : (N.subgroupOf C).Normal]
    (hs : s.Prime) (hKC : K ≤ C) (hNO : N ≤ GLAPPrimeCoreOf s C)
    (hY : GLAPComponent s C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C)
    (hY' : GLAPComponent s C Y') (hYK' : Y' ≤ K ⊔ GLAPPrimeCoreOf s C)
    (h : y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y) =
      y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y')) : Y = Y' := by
  have h1 := y10xD_Bhat_proj (C := C) (N := N) (Y := Y) hs hKC hNO hY hYK
  have h2 := y10xD_Bhat_proj (C := C) (N := N) (Y := Y') hs hKC hNO hY' hYK'
  rw [h] at h1
  exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_uniqueAux hY hY' (h1.symm.trans h2)

theorem y10xD_img_conj {s : ℕ} {C K N Y : Subgroup G} [hN : (N.subgroupOf C).Normal]
    (hKC : K ≤ C) (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    {x : G} (hxC : x ∈ C) (hYc : GLAPComponent s C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C) :
    (y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C))).map
        (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C))).toMonoidHom =
      y10xA_img C N (K ⊓ (GLBConj x Y ⊔ GLAPPrimeCoreOf s C)) := by
  obtain ⟨Y', hY'1, hY'⟩ := y10xD_fam_conj (s := s) (N := N) hKC hCK hO hxC hYc hYK
  have e : y10xA_fam s C K N (some ⟨Y, hYc, hYK⟩) =
      y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)) := rfl
  rw [← e, hY']
  show y10xA_img C N (K ⊓ (Y'.1 ⊔ GLAPPrimeCoreOf s C)) = _
  rw [hY'1]

theorem y10xD_img_conj_pow {s : ℕ} {C K N : Subgroup G} [hN : (N.subgroupOf C).Normal]
    (hKC : K ≤ C) (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    {x : G} (hxC : x ∈ C) (Yf : ℕ → Subgroup G) (hYf : ∀ m, GLAPComponent s C (Yf m))
    (hYfK : ∀ m, Yf m ≤ K ⊔ GLAPPrimeCoreOf s C) (hYfx : ∀ m, GLBConj x (Yf m) = Yf (m + 1)) :
    ∀ k m : ℕ, (y10xA_img C N (K ⊓ (Yf m ⊔ GLAPPrimeCoreOf s C))).map
        (MulAut.conj ((QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C)) ^ k)).toMonoidHom =
      y10xA_img C N (K ⊓ (Yf (m + k) ⊔ GLAPPrimeCoreOf s C)) := by
  intro k
  induction k with
  | zero =>
    intro m
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
      simpa using hw
    · intro hz
      exact Subgroup.mem_map.2 ⟨z, by simpa using hz, by simp⟩
  | succ k ih =>
    intro m
    have hcomp : (MulAut.conj ((QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C)) ^
        (k + 1))).toMonoidHom =
        (MulAut.conj ((QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C)) ^ k)).toMonoidHom.comp
          (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C))).toMonoidHom := by
      ext z
      simp only [MulAut.conj_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, pow_succ]
      group
    rw [hcomp, ← Subgroup.map_map]
    have hstep := y10xD_img_conj (s := s) (N := N) hKC hCK hO hxC (hYf m) (hYfK m)
    rw [hYfx m] at hstep
    rw [hstep]
    have := ih (m + 1)
    rw [show m + 1 + k = m + (k + 1) by ring] at this
    exact this

end Gamma2

section JHat

variable {G : Type} [Group G] [Finite G] {s : ℕ}

theorem y10xD_not_le_N {C K N J : Subgroup G} (hs : s.Prime) (hJK : J ≤ K)
    (hNO : N ≤ GLAPPrimeCoreOf s K) (hsJ : s ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    ¬ J ≤ N := by
  intro hJN
  have hsJ' : s ∣ Nat.card ↥J := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)]
    exact Dvd.dvd.mul_right hsJ _
  exact not_dvd_card_glaPPrimeCoreOf hs K
    ((hsJ'.trans (Subgroup.card_dvd_of_le (hJN.trans hNO))))

theorem y10xD_Jhat_qs {C N J : Subgroup G} [hN : (N.subgroupOf C).Normal] (hJC : J ≤ C)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hNJ : ¬ J ≤ N) :
    CFSG.Open.IsQuasisimple ↥(y10xA_img C N J) := by
  classical
  let φ : ↥J →* (↥C ⧸ N.subgroupOf C) :=
    (QuotientGroup.mk' (N.subgroupOf C)).comp (Subgroup.inclusion hJC)
  have hφ : ∀ j : ↥J, φ j ∈ y10xA_img C N J := fun j => y10xA_mem_img (hJC j.2) j.2
  let f : ↥J →* ↥(y10xA_img C N J) := φ.codRestrict (y10xA_img C N J) hφ
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨c, hc, rfl⟩ := y10xA_exists_of_mem_img hz
    refine ⟨⟨c.1, hc⟩, ?_⟩
    apply Subtype.ext
    rfl
  let NJ : Subgroup ↥J := N.comap J.subtype
  have hNJn : NJ.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ N := hn
    have hnC : (⟨(n : G), hJC n.2⟩ : ↥C) ∈ N.subgroupOf C := Subgroup.mem_subgroupOf.2 hn'
    have h1 : (g : G) * (n : G) * (g : G)⁻¹ ∈ N := by
      have := Subgroup.Normal.conj_mem hN _ hnC ⟨g.1, hJC g.2⟩
      exact Subgroup.mem_subgroupOf.1 this
    show ((g * n * g⁻¹ : ↥J) : G) ∈ N
    simpa using h1
  have hNJne : NJ ≠ ⊤ := by
    intro htop
    apply hNJ
    intro j hj
    have hmem : (⟨j, hj⟩ : ↥J) ∈ NJ := htop ▸ Subgroup.mem_top _
    exact hmem
  have hNJc : NJ ≤ Subgroup.center ↥J :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hJq NJ hNJne
  have hker : ∀ a : ↥J, f a = 1 → a ∈ Subgroup.center ↥J := by
    intro a ha
    have h1 : (QuotientGroup.mk' (N.subgroupOf C) (Subgroup.inclusion hJC a) :
        ↥C ⧸ N.subgroupOf C) = 1 := congrArg Subtype.val ha
    have h2 : (a : G) ∈ N := Subgroup.mem_subgroupOf.1
      ((QuotientGroup.eq_one_iff (Subgroup.inclusion hJC a)).1 h1)
    exact hNJc (show a ∈ NJ from h2)
  exact (y10xD_isQuasisimple_iff hf hJq.1 hker).1 hJq

theorem y10xD_Jhat_centralizer {C N J : Subgroup G} [hN : (N.subgroupOf C).Normal] {x : G}
    (hJC : J ≤ C) (hxC : x ∈ C)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set G)) :
    y10xA_img C N J ≤ Subgroup.centralizer ({QuotientGroup.mk' (N.subgroupOf C) (⟨x, hxC⟩ : ↥C)} :
      Set (↥C ⧸ N.subgroupOf C)) := by
  intro z hz
  obtain ⟨c, hc, rfl⟩ := y10xA_exists_of_mem_img hz
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show (c : G) * x = x * (c : G)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hJx hc)

end JHat

section Conj

variable {G : Type} [Group G] [Finite G]

theorem y10xD_S1 {s p : ℕ} {C J Y : Subgroup G} {x : G} (hs : s.Prime) (hp : 0 < p)
    (hxC : x ∈ C) (hxp : x ^ p = 1) (hJC : J ≤ C) (hJx : J ≤ Subgroup.centralizer ({x} : Set G))
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hsJ : s ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hJY : J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y) (hY : GLAPComponent s C Y) (m : ℕ) :
    GLAPComponent s C (GLBConj (x ^ m) Y) ∧
      GLBConj (x ^ m) Y ≤ closureIn J C ⊔ GLAPPrimeCoreOf s C := by
  have hYC : Y ≤ C := hY.1
  have hxm : x ^ m ∈ C := C.pow_mem hxC m
  have hYm : GLAPComponent s C (GLBConj (x ^ m) Y) := by
    have h := glaPComponent_gLBConj hY (x ^ m)
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hxm)] at h
  refine ⟨hYm, ?_⟩
  have hKC : closureIn J C ≤ C := y10xA_closureIn_le hJC
  have hJK : J ≤ closureIn J C := y10xA_le_closureIn C.one_mem
  have hKn : ((closureIn J C).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).2 y10xA_closureIn_normalizer
  refine y10xD_le_of_noncomm hKC hJK hYm hKn ?_
  exact y10xD_barX_noncomm hs hp hJC hJx hxC hxp hJq hsJ hJY hYC m

end Conj

section Orbit

variable {G : Type} [Group G] [Finite G]

theorem y10xD_orbit {s p : ℕ} {C J Y N : Subgroup G} [hN : (N.subgroupOf C).Normal] {x : G}
    (hs : s.Prime) (hp : p.Prime) (hxC : x ∈ C) (hx : x ^ p = 1) (hJC : J ≤ C)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set G))
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hsJ : s ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hJY : J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y) (hY : GLAPComponent s C Y)
    (hJp : J ≤ GLAPLayer s C)
    (hJs : CFSG.Open.IsSubnormal J (closureIn J C ⊓ Subgroup.centralizer ({x} : Set G)))
    (hNp : ¬ p ∣ Nat.card ↥(⁅closureIn J C, GLAPPrimeCoreOf s (closureIn J C)⁆ : Subgroup G))
    (hNdef : N = ⁅closureIn J C, GLAPPrimeCoreOf s (closureIn J C)⁆) :
    y10xA_img C N J ≤ ⨆ m : ℕ, y10xA_img C N (closureIn J C ⊓
      (GLBConj (x ^ m) Y ⊔ GLAPPrimeCoreOf s C)) := by
  classical
  have hKC : closureIn J C ≤ C := y10xA_closureIn_le hJC
  have hJK : J ≤ closureIn J C := y10xA_le_closureIn C.one_mem
  have hCK : C ≤ Subgroup.normalizer ((closureIn J C : Subgroup G) : Set G) :=
    y10xA_closureIn_normalizer
  have hKn : ((closureIn J C).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).2 hCK
  have hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf s C
  have hKnK : ∀ c ∈ C, ∀ k ∈ closureIn J C, c * k * c⁻¹ ∈ closureIn J C := fun c hc k hk =>
    (Subgroup.mem_normalizer_iff.1 (hCK hc) k).1 hk
  have hNOK : N ≤ GLAPPrimeCoreOf s (closureIn J C) := by
    rw [hNdef]
    refine Subgroup.commutator_le.2 fun k hk t ht => ?_
    rw [commutatorElement_def]
    have h1 : k * t * k⁻¹ ∈ GLAPPrimeCoreOf s (closureIn J C) :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf s (closureIn J C) hk) t).1 ht
    exact (GLAPPrimeCoreOf s (closureIn J C)).mul_mem h1
      ((GLAPPrimeCoreOf s (closureIn J C)).inv_mem ht)
  have hNK : N ≤ closureIn J C := hNOK.trans (y10xA_coreOf_le _)
  have hNC : N ≤ C := hNK.trans hKC
  have hNO : N ≤ GLAPPrimeCoreOf s C := hNOK.trans (glaPPrimeCoreOf_le_of_normal hs hKC hKn)
  have hcommN : ∀ k ∈ closureIn J C, ∀ t ∈ GLAPPrimeCoreOf s (closureIn J C),
      ⁅k, t⁆ ∈ N := by
    intro k hk t ht
    rw [hNdef]
    exact Subgroup.commutator_mem_commutator hk ht
  have hJN : ¬ J ≤ N := y10xD_not_le_N (C := C) hs hJK hNOK hsJ
  have hS1 := y10xD_S1 (C := C) (J := J) (Y := Y) hs hp.pos hxC hx hJC hJx hJq hsJ hJY hY
  have hYfx : ∀ m, GLBConj x (GLBConj (x ^ m) Y) = GLBConj (x ^ (m + 1)) Y := by
    intro m
    rw [gLBConj_gLBConj, pow_succ]
  have hKX : closureIn J C ≤ (⨆ Y' : y10xA_I s C (closureIn J C), Y'.1) ⊔
      GLAPPrimeCoreOf s C :=
    y10xA_closureIn_le_of (y10xA_J_le_sup hs hKC hJK hJC hJp hKn hJq)
      (y10xA_sup_normalized hKC (fun c hc => Subgroup.le_normalizer hc) hKnK hO)
  have hFK := y10xD_img_K_eq (N := N) (C := C) (K := closureIn J C) hs hKC hCK hO hKX
  have hNp' : ¬ p ∣ Nat.card ↥N := by
    rw [hNdef]
    exact hNp
  have hĴ0 := lemma117_khat_transport hp hxC hx hKC hNK hNp' hJK hJq hJN hJs
  set σ : ↥C ⧸ N.subgroupOf C := QuotientGroup.mk' (N.subgroupOf C) (⟨x, hxC⟩ : ↥C) with hσdef
  set σ' : ↥C ⧸ N.subgroupOf C := QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C)
    with hσ'def
  have hσσ : σ' = σ⁻¹ := by
    rw [hσ'def, hσdef, ← map_inv]
    rfl
  have hcent : Subgroup.centralizer ({σ'} : Set (↥C ⧸ N.subgroupOf C)) =
      Subgroup.centralizer ({σ} : Set (↥C ⧸ N.subgroupOf C)) := by
    rw [hσσ, y10xA_centralizer_inv]
  have hĴ1 : CFSG.Open.IsComponentOf (y10xA_img C N J)
      ((⨆ i : Option (y10xA_I s C (closureIn J C)),
        y10xA_fam s C (closureIn J C) N i) ⊓
        Subgroup.centralizer ({σ'} : Set (↥C ⧸ N.subgroupOf C))) := by
    rw [hcent, ← hFK]
    exact hĴ0
  have hxp' : (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C) ^ p = 1 := Subtype.ext (by simp [inv_pow, hx])
  have hσk : σ' ^ p = 1 := by
    rw [hσ'def, ← map_pow, hxp', map_one]
  obtain ⟨i₀, hnc, hle⟩ := y10xA_single_orbit
    (fun i : Option (y10xA_I s C (closureIn J C)) =>
      y10xA_fam s C (closureIn J C) N i) σ' p hp.pos hσk (y10xA_img C N J)
    (fun i j hij => y10xD_Fam_comm (N := N) hs hKC hO hcommN i j hij)
    (fun i => y10xD_Fam_sigma (N := N) hKC hCK hO hxC i) hĴ1
  have hY0c : GLAPComponent s C (GLBConj (x ^ 0) Y) := (hS1 0).1
  have hY0K : GLBConj (x ^ 0) Y ≤ closureIn J C ⊔ GLAPPrimeCoreOf s C := (hS1 0).2
  let Y0I : y10xA_I s C (closureIn J C) := ⟨GLBConj (x ^ 0) Y, hY0c, hY0K⟩
  have hg0 : ∃ g ∈ y10xA_img C N J, ∃ y ∈ y10xA_fam s C (closureIn J C) N
      (some Y0I), g * y ≠ y * g := by
    obtain ⟨a, ha, b, hb, hab⟩ := y10xD_barX_noncomm hs hp.pos hJC hJx hxC hx hJq hsJ hJY hY.1 0
    have hH : closureIn J C ⊓ (GLBConj (x ^ 0) Y ⊔ GLAPPrimeCoreOf s C) ≤ C :=
      inf_le_left.trans hKC
    have hmapH := y10xD_map_proj (N := N) hNO hH
    have hPY := y10xD_barX_P_eq (s := s) hKC hY0c hY0K
    have hmapJ := y10xD_map_proj (N := N) hNO hJC
    have ha' : a ∈ (y10xA_img C N (closureIn J C ⊓ (GLBConj (x ^ 0) Y ⊔ GLAPPrimeCoreOf s C))).map
        (y10xD_proj (s := s) hNO) := by
      rw [hmapH, hPY]
      exact ha
    have hb' : b ∈ (y10xA_img C N J).map (y10xD_proj (s := s) hNO) := by
      rw [hmapJ]
      exact hb
    obtain ⟨α, hα, hαa⟩ := Subgroup.mem_map.1 ha'
    obtain ⟨β, hβ, hβb⟩ := Subgroup.mem_map.1 hb'
    refine ⟨β, hβ, α, hα, fun h => hab ?_⟩
    rw [← hαa, ← hβb, ← map_mul, ← map_mul, h]
  obtain ⟨n, hn⟩ := hnc (some Y0I) hg0
  have hconjpow := y10xD_img_conj_pow (s := s) (N := N) hKC hCK hO hxC
    (fun m => GLBConj (x ^ m) Y) (fun m => (hS1 m).1) (fun m => (hS1 m).2) hYfx
  have hp1 : 1 ≤ p := hp.one_le
  have hcn : σ' ^ ((p - 1) * n) * σ' ^ n = 1 := by
    rw [← pow_add]
    have e : (p - 1) * n + n = p * n := by
      rw [← add_one_mul, Nat.sub_add_cancel hp1]
    rw [e, pow_mul, hσk, one_pow]
  have hinv : σ' ^ ((p - 1) * n) = (σ' ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hcn
  have hid : (MulAut.conj (σ' ^ ((p - 1) * n))).toMonoidHom.comp
      (MulAut.conj (σ' ^ n)).toMonoidHom = MonoidHom.id _ := by
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
    rw [hinv]
    group
  have hWc : y10xA_fam s C (closureIn J C) N i₀ =
      y10xA_img C N (closureIn J C ⊓ (GLBConj (x ^ ((p - 1) * n)) Y ⊔ GLAPPrimeCoreOf s C)) := by
    have h1 : ((y10xA_fam s C (closureIn J C) N i₀).map
        (MulAut.conj (σ' ^ n)).toMonoidHom).map (MulAut.conj (σ' ^ ((p - 1) * n))).toMonoidHom =
        y10xA_fam s C (closureIn J C) N i₀ := by
      rw [Subgroup.map_map, hid, Subgroup.map_id]
    have h2 : ((y10xA_fam s C (closureIn J C) N (some Y0I))).map
        (MulAut.conj (σ' ^ ((p - 1) * n))).toMonoidHom =
        (((y10xA_fam s C (closureIn J C) N i₀).map
          (MulAut.conj (σ' ^ n)).toMonoidHom)).map (MulAut.conj (σ' ^ ((p - 1) * n))).toMonoidHom := by
      rw [← hn]
    rw [h1] at h2
    rw [← h2]
    have h3 := hconjpow ((p - 1) * n) 0
    rw [zero_add] at h3
    exact h3
  calc y10xA_img C N J ≤ ⨆ k : ℕ, (y10xA_fam s C (closureIn J C) N i₀).map
        (MulAut.conj (σ' ^ k)).toMonoidHom := hle
    _ ≤ ⨆ m : ℕ, y10xA_img C N (closureIn J C ⊓ (GLBConj (x ^ m) Y ⊔ GLAPPrimeCoreOf s C)) := by
      refine iSup_le fun k => ?_
      rw [hWc, hconjpow k ((p - 1) * n)]
      exact le_iSup (fun m : ℕ => y10xA_img C N (closureIn J C ⊓
        (GLBConj (x ^ m) Y ⊔ GLAPPrimeCoreOf s C))) ((p - 1) * n + k)

end Orbit

section Final

variable {Γ : Type} [Group Γ]

theorem y10xD_self_of_commutator_top {B : Subgroup Γ} (h : commutator ↥B = ⊤) : ⁅B, B⁆ = B := by
  have hmap : Subgroup.map B.subtype (⊤ : Subgroup ↥B) = B := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  calc ⁅B, B⁆ = ⁅Subgroup.map B.subtype (⊤ : Subgroup ↥B), Subgroup.map B.subtype ⊤⁆ := by
        rw [hmap]
    _ = Subgroup.map B.subtype ⁅(⊤ : Subgroup ↥B), ⊤⁆ := (Subgroup.map_commutator _ _ _).symm
    _ = Subgroup.map B.subtype ⊤ := by rw [show ⁅(⊤ : Subgroup ↥B), ⊤⁆ = ⊤ from h]
    _ = B := hmap

theorem y10xD_eq_of_qs {L Λ : Subgroup Γ} (hΛ : CFSG.Open.IsQuasisimple ↥Λ)
    (hL : CFSG.Open.IsComponentOf L Λ) : L = Λ := by
  have h1 := y10xD_comp_top hL
  have h2 : CFSG.Open.IsComponentOf (⊤ : Subgroup ↥Λ) ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.refl _,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv (G := ↥Λ)) hΛ⟩
  have h3 := CFSG.ComponentClassification.LocalComponents.eq_of_le _ _ h1 h2 le_top
  have h4 : Λ ≤ L := by
    rw [← Subgroup.subgroupOf_eq_top]
    exact h3
  exact le_antisymm hL.1 h4

theorem y10xD_qs_of_quot {X Λ : Type} [Group X] [Group Λ] (hX : CFSG.Open.IsQuasisimple X)
    (Z : Subgroup X) [Z.Normal] (hZ : Z ≤ Subgroup.center X) (e : Λ ≃* X ⧸ Z) :
    CFSG.Open.IsQuasisimple Λ := by
  let f : X →* Λ := e.symm.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z (e y)
    refine ⟨x, ?_⟩
    show e.symm (QuotientGroup.mk' Z x) = y
    rw [hx, MulEquiv.symm_apply_apply]
  have hker : ∀ a : X, f a = 1 → a ∈ Subgroup.center X := by
    intro a ha
    have h1 : QuotientGroup.mk' Z a = 1 := by
      have : e.symm.toMonoidHom (QuotientGroup.mk' Z a) = 1 := ha
      rw [MulEquiv.coe_toMonoidHom] at this
      exact (map_eq_one_iff e.symm e.symm.injective).1 this
    exact hZ ((QuotientGroup.eq_one_iff a).1 h1)
  exact (y10xD_isQuasisimple_iff hf hX.1 hker).1 hX

end Final

section Kernels

variable {G : Type} [Group G] [Finite G]

theorem y10xD_ker_central_J {C N J : Subgroup G} [hN : (N.subgroupOf C).Normal] (hJC : J ≤ C)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hNJ : ¬ J ≤ N) :
    ∀ a : ↥J, (QuotientGroup.mk' (N.subgroupOf C) (Subgroup.inclusion hJC a) :
      ↥C ⧸ N.subgroupOf C) = 1 → a ∈ Subgroup.center ↥J := by
  let NJ : Subgroup ↥J := N.comap J.subtype
  have hNJn : NJ.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ N := hn
    have hnC : (⟨(n : G), hJC n.2⟩ : ↥C) ∈ N.subgroupOf C := Subgroup.mem_subgroupOf.2 hn'
    have h1 : (g : G) * (n : G) * (g : G)⁻¹ ∈ N := by
      have := Subgroup.Normal.conj_mem hN _ hnC ⟨g.1, hJC g.2⟩
      exact Subgroup.mem_subgroupOf.1 this
    show ((g * n * g⁻¹ : ↥J) : G) ∈ N
    simpa using h1
  have hNJne : NJ ≠ ⊤ := by
    intro htop
    apply hNJ
    intro j hj
    have hmem : (⟨j, hj⟩ : ↥J) ∈ NJ := htop ▸ Subgroup.mem_top _
    exact hmem
  have hNJc : NJ ≤ Subgroup.center ↥J :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hJq NJ hNJne
  intro a ha
  have h2 : (a : G) ∈ N := Subgroup.mem_subgroupOf.1
    ((QuotientGroup.eq_one_iff (Subgroup.inclusion hJC a)).1 ha)
  exact hNJc (show a ∈ NJ from h2)

theorem y10xD_Yhat_comm {s : ℕ} {C K N Y Y' : Subgroup G} [hN : (N.subgroupOf C).Normal]
    (hs : s.Prime) (hKC : K ≤ C) (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    (hcommN : ∀ k ∈ K, ∀ t ∈ GLAPPrimeCoreOf s K, ⁅k, t⁆ ∈ N)
    (hY : GLAPComponent s C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C)
    (hY' : GLAPComponent s C Y') (hYK' : Y' ≤ K ⊔ GLAPPrimeCoreOf s C) (hne : Y' ≠ Y) :
    ⁅y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)),
      y10xA_img C N (K ⊓ (Y' ⊔ GLAPPrimeCoreOf s C))⁆ = ⊥ := by
  have hc := y10xA_img_P_commute hs hKC hO hcommN hY hYK hY' hYK' hne
  exact y10xA_bot_of_commute hc

theorem y10xD_Bhat_conj {s : ℕ} {C K N Y : Subgroup G} [hN : (N.subgroupOf C).Normal]
    (hKC : K ≤ C) (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G))
    {x : G} (hxC : x ∈ C) (hYc : GLAPComponent s C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf s C) :
    (y10xD_Bhat s (C := C) (N := N) (K := K) (Y := Y)).map
        (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C))).toMonoidHom =
      y10xD_Bhat s (C := C) (N := N) (K := K) (Y := GLBConj x Y) := by
  show Subgroup.map _ ⁅y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C)),
      y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf s C))⁆ = _
  rw [Subgroup.map_commutator, y10xD_img_conj hKC hCK hO hxC hYc hYK]

end Kernels

section Involution

variable {G : Type} [Group G] [Finite G]

theorem y10xD_Jhat_involution {C N J : Subgroup G} [hN : (N.subgroupOf C).Normal] (hJC : J ≤ C)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hJN : ¬ J ≤ N)
    (hm2 : 6 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥J))
    (hodd : Odd (Nat.card (Subgroup.center ↥J))) :
    ∃ t ∈ y10xA_img C N J, t ≠ 1 ∧ t ^ 2 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₂, -, hE₂el, hE₂card⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) (⊤ : Subgroup ↥J)
  have h2dvd : 2 ∣ Nat.card ↥E₂ := by
    rw [hE₂card]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨e₂, he₂⟩ := exists_prime_orderOf_dvd_card' (G := ↥E₂) 2 h2dvd
  set tJ : ↥J := (e₂ : ↥J) with htJ
  have htJo : orderOf tJ = 2 := by
    rw [htJ, Subgroup.orderOf_coe, he₂]
  have htJ2 : tJ ^ 2 = 1 := by
    rw [← htJo]
    exact pow_orderOf_eq_one tJ
  have htJne : tJ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htJo
    norm_num at htJo
  have hnotN : (tJ : G) ∉ N := by
    intro hmem
    have hker := y10xD_ker_central_J hJC hJq hJN tJ
      ((QuotientGroup.eq_one_iff (Subgroup.inclusion hJC tJ)).2 (Subgroup.mem_subgroupOf.2 hmem))
    have hdvd := orderOf_dvd_natCard (⟨tJ, hker⟩ : ↥(Subgroup.center ↥J))
    have hord : orderOf (⟨tJ, hker⟩ : ↥(Subgroup.center ↥J)) = 2 := by
      rw [← htJo]
      exact (Subgroup.orderOf_coe (⟨tJ, hker⟩ : ↥(Subgroup.center ↥J))).symm
    rw [hord] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    obtain ⟨j, hj⟩ := hodd
    omega
  refine ⟨QuotientGroup.mk' (N.subgroupOf C) (Subgroup.inclusion hJC tJ), ?_, ?_, ?_⟩
  · exact y10xA_mem_img (hJC tJ.2) tJ.2
  · intro h
    apply hnotN
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (Subgroup.inclusion hJC tJ)).1 h)
  · rw [← map_pow]
    have : (Subgroup.inclusion hJC tJ) ^ 2 = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val htJ2
      simpa using this
    rw [this, map_one]

theorem y10xD_B_involution {Γ : Type} [Group Γ] [Finite Γ] {Λ X : Subgroup Γ} (Z : Subgroup ↥X)
    [Z.Normal] (e : ↥Λ ≃* ↥X ⧸ Z) (hτ : ∃ t ∈ Λ, t ≠ 1 ∧ t ^ 2 = 1) :
    ∃ b ∈ X, b ≠ 1 ∧ b ^ 2 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htΛ, ht1, ht2⟩ := hτ
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have h2Λ : 2 ∣ Nat.card ↥Λ := by
    have hdvd := orderOf_dvd_natCard (⟨t, htΛ⟩ : ↥Λ)
    have hord : orderOf (⟨t, htΛ⟩ : ↥Λ) = 2 := by
      rw [← hto]
      exact (Subgroup.orderOf_coe (⟨t, htΛ⟩ : ↥Λ)).symm
    rw [hord] at hdvd
    exact hdvd
  have h2X : 2 ∣ Nat.card ↥X := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z]
    have hcard : Nat.card ↥Λ = Nat.card (↥X ⧸ Z) := Nat.card_congr e.toEquiv
    rw [← hcard]
    exact Dvd.dvd.mul_right h2Λ _
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 h2X
  refine ⟨(b : Γ), b.2, ?_, ?_⟩
  · intro h
    have hb1 : b = 1 := Subtype.ext h
    rw [hb1, orderOf_one] at hb
    norm_num at hb
  · have hb2 : b ^ 2 = 1 := by
      rw [← hb]
      exact pow_orderOf_eq_one b
    have := congrArg Subtype.val hb2
    simpa using this

end Involution

section Core

variable {G : Type} [Group G] [Finite G]

theorem y10xD_core {s p : ℕ} {C J Y N : Subgroup G} [hN : (N.subgroupOf C).Normal] {x : G}
    (hs : s.Prime) (hs2 : s ≠ 2) (hp : p.Prime) (hxC : x ∈ C) (hx : x ^ p = 1) (hJC : J ≤ C)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set G)) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hsJ : s ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hJY : J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y) (hY : GLAPComponent s C Y)
    (hJp : J ≤ GLAPLayer s C)
    (hJs : CFSG.Open.IsSubnormal J (closureIn J C ⊓ Subgroup.centralizer ({x} : Set G)))
    (hNp : ¬ p ∣ Nat.card ↥(⁅closureIn J C, GLAPPrimeCoreOf s (closureIn J C)⁆ : Subgroup G))
    (hNdef : N = ⁅closureIn J C, GLAPPrimeCoreOf s (closureIn J C)⁆)
    (hdistY : ∀ i j : ℕ, i < p → j < p → i ≠ j → GLBConj (x ^ i) Y ≠ GLBConj (x ^ j) Y)
    (hI25 : Input2_5) (hG : CFSG.Open.GLATwoLocalRank s G ≤ 4)
    (hm2 : 6 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥J))
    (hodd : Odd (Nat.card (Subgroup.center ↥J)))
    (labJ : GLALabel) (hMJ : GLAMarking ↥J (fun lab _ _ _ _ _ => lab = labJ))
    (hcount : ∀ (K₀ : Type) [Group K₀] [Finite K₀],
      GLAMarking K₀ (fun lab _ _ _ _ _ => lab = labJ) →
        5 + CFSG.Open.pRank s (Subgroup.center K₀) ≤
          CFSG.Open.GLATwoLocalRank s K₀ + CFSG.Open.pRank s (⊤ : Subgroup K₀)) : False := by
  classical
  haveI : Fact s.Prime := ⟨hs⟩
  have hKC : closureIn J C ≤ C := y10xA_closureIn_le hJC
  have hJK : J ≤ closureIn J C := y10xA_le_closureIn C.one_mem
  have hCK : C ≤ Subgroup.normalizer ((closureIn J C : Subgroup G) : Set G) :=
    y10xA_closureIn_normalizer
  have hKn : ((closureIn J C).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).2 hCK
  have hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf s C : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf s C
  have hNOK : N ≤ GLAPPrimeCoreOf s (closureIn J C) := by
    rw [hNdef]
    refine Subgroup.commutator_le.2 fun k hk t ht => ?_
    rw [commutatorElement_def]
    have h1 : k * t * k⁻¹ ∈ GLAPPrimeCoreOf s (closureIn J C) :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf s (closureIn J C) hk) t).1 ht
    exact (GLAPPrimeCoreOf s (closureIn J C)).mul_mem h1
      ((GLAPPrimeCoreOf s (closureIn J C)).inv_mem ht)
  have hNK : N ≤ closureIn J C := hNOK.trans (y10xA_coreOf_le _)
  have hNC : N ≤ C := hNK.trans hKC
  have hNO : N ≤ GLAPPrimeCoreOf s C := hNOK.trans (glaPPrimeCoreOf_le_of_normal hs hKC hKn)
  have hcommN : ∀ k ∈ closureIn J C, ∀ t ∈ GLAPPrimeCoreOf s (closureIn J C), ⁅k, t⁆ ∈ N := by
    intro k hk t ht
    rw [hNdef]
    exact Subgroup.commutator_mem_commutator hk ht
  have hJN : ¬ J ≤ N := y10xD_not_le_N (C := C) hs hJK hNOK hsJ
  have hNp' : ¬ p ∣ Nat.card ↥N := by
    rw [hNdef]
    exact hNp
  have hNs : ¬ s ∣ Nat.card ↥(N.subgroupOf C) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
    intro h
    exact not_dvd_card_glaPPrimeCoreOf hs C (h.trans (Subgroup.card_dvd_of_le hNO))
  have hS1 := fun m => y10xD_S1 (C := C) (J := J) (Y := Y) hs hp.pos hxC hx hJC hJx hJq hsJ hJY hY m
  have hYfx : ∀ m, GLBConj x (GLBConj (x ^ m) Y) = GLBConj (x ^ (m + 1)) Y := by
    intro m
    rw [gLBConj_gLBConj, pow_succ]
  have hxpow : ∀ m : ℕ, x ^ m = x ^ (m % p) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m p]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
  let Ŷ : ℕ → Subgroup (↥C ⧸ N.subgroupOf C) := fun m =>
    y10xA_img C N (closureIn J C ⊓ (GLBConj (x ^ m) Y ⊔ GLAPPrimeCoreOf s C))
  let Bm : ℕ → Subgroup (↥C ⧸ N.subgroupOf C) := fun m =>
    y10xD_Bhat s (C := C) (N := N) (K := closureIn J C) (Y := GLBConj (x ^ m) Y)
  have hBqs : ∀ m, CFSG.Open.IsQuasisimple ↥(Bm m) := fun m =>
    y10xD_Bhat_qs hs hKC hcommN hNO (hS1 m).1 (hS1 m).2
  have hBcomm : ∀ m m', Bm m ≠ Bm m' → ⁅Bm m, Bm m'⁆ = ⊥ := by
    intro m m' hne
    have hYne : GLBConj (x ^ m') Y ≠ GLBConj (x ^ m) Y := fun h =>
      hne (congrArg (fun Z => y10xD_Bhat s (C := C) (N := N) (K := closureIn J C) (Y := Z)) h.symm)
    exact y10xD_Bhat_comm hs hKC hO hcommN (hS1 m).1 (hS1 m).2 (hS1 m').1 (hS1 m').2 hYne
  have hBconj' : ∀ m, (Bm m).map (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C)
      (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C))).toMonoidHom = Bm (m + 1) := by
    intro m
    rw [y10xD_Bhat_conj hKC hCK hO hxC (hS1 m).1 (hS1 m).2, hYfx m]
  have hσσ : QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C) =
      (QuotientGroup.mk' (N.subgroupOf C) (⟨x, hxC⟩ : ↥C))⁻¹ := by
    rw [← map_inv]
    rfl
  set σ : ↥C ⧸ N.subgroupOf C := QuotientGroup.mk' (N.subgroupOf C) (⟨x, hxC⟩ : ↥C) with hσdef
  have hBconj : ∀ m, GLBConj σ (Bm m) = Bm (m + 1) := by
    intro m
    show (Bm m).map (MulAut.conj σ⁻¹).toMonoidHom = Bm (m + 1)
    rw [← hσσ]
    exact hBconj' m
  have hσp : σ ^ p = 1 := by
    rw [hσdef, ← map_pow]
    rw [show (⟨x, hxC⟩ : ↥C) ^ p = 1 from Subtype.ext (by simp [hx])]
    exact map_one _
  have hBper : ∀ m, Bm (m + p) = Bm m := by
    intro m
    show y10xD_Bhat s (C := C) (N := N) (K := closureIn J C) (Y := GLBConj (x ^ (m + p)) Y) =
      y10xD_Bhat s (C := C) (N := N) (K := closureIn J C) (Y := GLBConj (x ^ m) Y)
    rw [pow_add, hx, mul_one]
  have hBdist : ∀ m m', Bm m = Bm m' → m % p = m' % p := by
    intro m m' h
    have hY' := y10xD_Bhat_inj hs hKC hNO (hS1 m).1 (hS1 m).2 (hS1 m').1 (hS1 m').2 h
    by_contra hne
    apply hdistY (m % p) (m' % p) (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) hne
    rw [← hxpow m, ← hxpow m']
    exact hY'
  have hX1 := y10xD_B_comp Bm hBqs hBcomm 0
  obtain ⟨Z, hZn, hZc, ⟨e⟩⟩ := y10xD_input25_B hI25 hp σ hσp Bm hBqs hBcomm hBconj hBper hBdist hX1
  have hĴqs : CFSG.Open.IsQuasisimple ↥(y10xA_img C N J) := y10xD_Jhat_qs hJC hJq hJN
  have hĴ0 := lemma117_khat_transport hp hxC hx hKC hNK hNp' hJK hJq hJN hJs
  have horb := y10xD_orbit (N := N) hs hp hxC hx hJC hJx hJq hsJ hJY hY hJp hJs hNp hNdef
  have hA : ∀ i j, Ŷ i ≠ Ŷ j → ⁅Ŷ i, Ŷ j⁆ = ⊥ := by
    intro i j hij
    have hYne : GLBConj (x ^ j) Y ≠ GLBConj (x ^ i) Y := fun h =>
      hij (congrArg (fun Z => y10xA_img C N (closureIn J C ⊓ (Z ⊔ GLAPPrimeCoreOf s C))) h.symm)
    exact y10xD_Yhat_comm hs hKC hO hcommN (hS1 i).1 (hS1 i).2 (hS1 j).1 (hS1 j).2 hYne
  have hĴB : y10xA_img C N J ≤ ⨆ m, Bm m := by
    calc y10xA_img C N J = ⁅y10xA_img C N J, y10xA_img C N J⁆ :=
          (y10xD_self_of_commutator_top hĴqs.1).symm
      _ ≤ ⁅⨆ m, Ŷ m, ⨆ m, Ŷ m⁆ := Subgroup.commutator_mono horb horb
      _ ≤ ⨆ m, ⁅Ŷ m, Ŷ m⁆ := y10xD_commutator_iSup_le Ŷ hA
      _ = ⨆ m, Bm m := rfl
  have hcent : Subgroup.centralizer ({σ} : Set (↥C ⧸ N.subgroupOf C)) =
      Subgroup.centralizer ((Subgroup.zpowers σ : Subgroup (↥C ⧸ N.subgroupOf C)) : Set _) :=
    y10xA_centralizer_singleton_eq σ
  set L : Subgroup (↥C ⧸ N.subgroupOf C) := (⨆ m, Bm m) ⊓
    Subgroup.centralizer ((Subgroup.zpowers σ : Subgroup (↥C ⧸ N.subgroupOf C)) : Set _) with hLdef
  have hĴL : y10xA_img C N J ≤ L := by
    refine le_inf hĴB ?_
    rw [← hcent]
    exact y10xD_Jhat_centralizer hJC hxC hJx
  have hLK : L ≤ y10xA_img C N (closureIn J C) ⊓ Subgroup.centralizer ({σ} : Set _) := by
    refine inf_le_inf ?_ (le_of_eq hcent.symm)
    exact iSup_le fun m => (y10xD_commutator_le_of_le (le_refl (Ŷ m))).trans
      (y10xA_img_mono inf_le_left)
  have hĴcomp : CFSG.Open.IsComponentOf (y10xA_img C N J) L := by
    refine ⟨hĴL, ?_, hĴqs⟩
    have h1 := CFSG.Open.IsSubnormal.inf_of_le hĴ0.2.1 hLK
    rwa [inf_eq_left.2 hĴL] at h1
  have hΛĴ_le : y10xA_img C N J ≤ CFSG.Open.GLALayer L := by
    show _ ≤ sSup {K | CFSG.Open.IsComponentOf K L}
    exact le_sSup hĴcomp
  have hΛL : CFSG.Open.GLALayer L ≤ L := sSup_le fun K hK => hK.1
  have hĴΛcomp : CFSG.Open.IsComponentOf (y10xA_img C N J) (CFSG.Open.GLALayer L) := by
    refine ⟨hΛĴ_le, ?_, hĴqs⟩
    have h1 := CFSG.Open.IsSubnormal.inf_of_le hĴcomp.2.1 hΛL
    rwa [inf_eq_left.2 hΛĴ_le] at h1
  have hΛqs : CFSG.Open.IsQuasisimple ↥(CFSG.Open.GLALayer L) :=
    y10xD_qs_of_quot (hBqs 0) Z hZc e
  have hΛĴeq : CFSG.Open.GLALayer L = y10xA_img C N J :=
    (y10xD_eq_of_qs hΛqs hĴΛcomp).symm
  have hJmem : ∀ j : ↥J, (QuotientGroup.mk' (N.subgroupOf C) (Subgroup.inclusion hJC j) :
      ↥C ⧸ N.subgroupOf C) ∈ CFSG.Open.GLALayer L := by
    intro j
    rw [hΛĴeq]
    exact y10xA_mem_img (hJC j.2) j.2
  let fJ : ↥J →* ↥(CFSG.Open.GLALayer L) :=
    ((QuotientGroup.mk' (N.subgroupOf C)).comp (Subgroup.inclusion hJC)).codRestrict
      (CFSG.Open.GLALayer L) hJmem
  have hfJsurj : Function.Surjective fJ := by
    rintro ⟨y, hy⟩
    rw [hΛĴeq] at hy
    obtain ⟨c, hc, hcy⟩ := y10xA_exists_of_mem_img hy
    refine ⟨⟨c.1, hc⟩, ?_⟩
    apply Subtype.ext
    exact hcy
  have hfJker : ∀ a : ↥J, fJ a = 1 → a ∈ Subgroup.center ↥J := fun a ha =>
    y10xD_ker_central_J hJC hJq hJN a (congrArg Subtype.val ha)
  obtain ⟨eJ⟩ := y10xD_quot_equiv hfJsurj hJq.1 hfJker
  let fB : ↥(Bm 0) →* ↥(CFSG.Open.GLALayer L) := e.symm.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hfBsurj : Function.Surjective fB := fun y => by
    obtain ⟨x0, hx0⟩ := QuotientGroup.mk'_surjective Z (e y)
    refine ⟨x0, ?_⟩
    show e.symm (QuotientGroup.mk' Z x0) = y
    rw [hx0, MulEquiv.symm_apply_apply]
  have hfBker : ∀ a : ↥(Bm 0), fB a = 1 → a ∈ Subgroup.center ↥(Bm 0) := by
    intro a ha
    have h1 : QuotientGroup.mk' Z a = 1 := by
      have h2 : e.symm.toMonoidHom (QuotientGroup.mk' Z a) = 1 := ha
      rw [MulEquiv.coe_toMonoidHom] at h2
      exact (map_eq_one_iff e.symm e.symm.injective).1 h2
    exact hZc ((QuotientGroup.eq_one_iff a).1 h1)
  obtain ⟨eB⟩ := y10xD_quot_equiv hfBsurj (hBqs 0).1 hfBker
  have eBJ := eB.trans eJ.symm
  have hMB : GLAMarking ↥(Bm 0) (fun lab _ _ _ _ _ => lab = labJ) :=
    y10xD_marking_transfer labJ (hBqs 0).1 eBJ hMJ
  have hcnt := hcount ↥(Bm 0) hMB
  have hτΛ : ∃ t ∈ CFSG.Open.GLALayer L, t ≠ 1 ∧ t ^ 2 = 1 := by
    obtain ⟨t, ht, ht1, ht2⟩ := y10xD_Jhat_involution hJC hJq hJN hm2 hodd
    exact ⟨t, by rw [hΛĴeq]; exact ht, ht1, ht2⟩
  obtain ⟨b0, hb0, hb01, hb02⟩ := y10xD_B_involution Z e hτΛ
  have hBne01 : Bm 0 ≠ Bm 1 := fun h => by
    have h1 := hBdist 0 1 h
    rw [Nat.zero_mod, Nat.mod_eq_of_lt hp.one_lt] at h1
    exact absurd h1 (by norm_num)
  have hcomm01 : ∀ a ∈ Bm 0, ∀ b ∈ Bm 1, a * b = b * a := by
    intro a ha b hb
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hBcomm 0 1 hBne01) ha
    exact ((Subgroup.mem_centralizer_iff.1 hc) b hb).symm
  obtain ⟨E₀, -, hE₀el, hE₀card⟩ :=
    CFSG.SectionRank.exists_pRank hs.one_lt (⊤ : Subgroup ↥(Bm 0))
  have hE₀' : E₀.map (Bm 0).subtype ≤ Bm 0 := by
    intro y hy
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact w.2
  have hE₀'el := CFSG.SectionRank.isElemAbelian_map hE₀el (Bm 0).subtype
  have hE₁le : (E₀.map (Bm 0).subtype).map (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C)
      (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C))).toMonoidHom ≤ Bm 1 := by
    calc _ ≤ (Bm 0).map (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C)
          (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C))).toMonoidHom := Subgroup.map_mono hE₀'
      _ = Bm 1 := hBconj' 0
  have hE₁el := CFSG.SectionRank.isElemAbelian_map hE₀'el (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C)
      (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C))).toMonoidHom
  have hE₁card : Nat.card ↥((E₀.map (Bm 0).subtype).map (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C)
      (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C))).toMonoidHom) = s ^ CFSG.Open.pRank s (⊤ : Subgroup ↥(Bm 0)) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective,
      Subgroup.card_map_of_injective Subtype.val_injective, hE₀card]
  have hcountres := y10xD_count hs (Bm 0) (Bm 1) hcomm01 b0 hb0 hb01 hb02 _ hE₁le hE₁el hE₁card
  have hGΓ : CFSG.Open.GLATwoLocalRank s (↥C ⧸ N.subgroupOf C) ≤ 4 :=
    (glaTwoLocalRank_quotient_le hs hs2 (N.subgroupOf C) hNs).trans ((twoLocalRank_le_top hs C).trans hG)
  omega

end Core

theorem no_diag_SU5 (hI25 : Input2_5) (hU5 : U5CaseAt G) (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J)
    {x : G} (hp : p.Prime) (hx : x ^ p = 1) (hxx : x ∈ Subgroup.centralizer ({x'} : Set G))
    (hJc : IsComponentOf J (Subgroup.centralizer ({x'} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)))
    (hJp : J ≤ GLAPLayer p' (Subgroup.centralizer ({x'} : Set G)))
    (hJp' : J ≤ GLAPLayer p (Subgroup.centralizer ({x'} : Set G)))
    (hsix : evenRank ↥L = 4 ∧ ∃ labJ : GLALabel, LabelOf J labJ ∧ labJ.tag = .twA ∧ labJ.rank = 4 ∧ Even labJ.n) :
    ¬ ∃ Y : Subgroup G, GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) Y ∧
        (∀ i j : ℕ, i < p → j < p → i ≠ j → GLBConj (x ^ i) Y ≠ GLBConj (x ^ j) Y) ∧
        J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y := by
  classical
  rintro ⟨Y, hY, hdistY, hJY⟩
  set C : Subgroup G := Subgroup.centralizer ({x'} : Set G) with hCdef
  have hs : p'.Prime := hc.cfg.prime
  have hs2 : p' ≠ 2 := hc.cfg.odd
  have hJC : J ≤ C := fun j hj => (hc.cfg.comp.1.1 hj).2
  have hJq : CFSG.Open.IsQuasisimple ↥J := hc.cfg.comp.1.2.2
  have hsJ : p' ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := (dvd_mul_left p' p).trans hc.cfg.dvd
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) := fun j hj => (hJc.1 hj).2
  have hKC : closureIn J C ≤ C := y10xA_closureIn_le hJC
  have hJK : J ≤ closureIn J C := y10xA_le_closureIn C.one_mem
  have hJs : CFSG.Open.IsSubnormal J (closureIn J C ⊓ Subgroup.centralizer ({x} : Set G)) := by
    have h := CFSG.Open.IsSubnormal.inf hJc.2.1 (closureIn J C)
    rw [inf_eq_left.2 hJK, inf_right_comm, inf_eq_right.2 hKC] at h
    exact h
  have hNp : ¬ p ∣ Nat.card ↥(⁅closureIn J C, GLAPPrimeCoreOf p' (closureIn J C)⁆ : Subgroup G) := by
    intro h
    have hle := closureCore_le_oPPrimeP hctx hc hp hJp'
    exact not_dvd_card_glaPPrimeCoreOf hp (closureIn J C) (h.trans (Subgroup.card_dvd_of_le hle))
  have hG : CFSG.Open.GLATwoLocalRank p' G ≤ 4 := by
    obtain ⟨-, h2, -⟩ := hc.mu
    have hm : m = 4 := hc.e_eq.symm.trans hsix.1
    rw [h2, hm]
  have hm2 : 6 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥J) := by
    have h := hc.cfg.m2
    rw [hsix.1] at h
    exact h
  have hodd : Odd (Nat.card (Subgroup.center ↥J)) := hc.cfg.odd_center
  obtain ⟨labJ, hlabJ, htag, hrank, hevn⟩ := hsix.2
  have hlab : labJ = ⟨.twA, 4, labJ.n⟩ := by
    rcases labJ with ⟨t, r, n⟩
    simp only at htag hrank
    subst htag
    subst hrank
    rfl
  have hlabJ' : LabelOf J ⟨.twA, 4, labJ.n⟩ := hlab ▸ hlabJ
  have hU5' := hU5 p p' L B' x' J hc.cfg hsix.1 labJ.n hevn hlabJ'
  have hNK : ⁅closureIn J C, GLAPPrimeCoreOf p' (closureIn J C)⁆ ≤ closureIn J C := by
    refine Subgroup.commutator_le.2 fun k hk t ht => ?_
    rw [commutatorElement_def]
    have ht' : t ∈ closureIn J C := y10xA_coreOf_le _ ht
    exact (closureIn J C).mul_mem ((closureIn J C).mul_mem ((closureIn J C).mul_mem hk ht')
      ((closureIn J C).inv_mem hk)) ((closureIn J C).inv_mem ht')
  have hNC : ⁅closureIn J C, GLAPPrimeCoreOf p' (closureIn J C)⁆ ≤ C := hNK.trans hKC
  have hCK : C ≤ Subgroup.normalizer ((closureIn J C : Subgroup G) : Set G) :=
    y10xA_closureIn_normalizer
  haveI hNn : ((⁅closureIn J C, GLAPPrimeCoreOf p' (closureIn J C)⁆ : Subgroup G).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNC).2 (y10xA_comm_core_normalizer hCK)
  have hMJ : GLAMarking ↥J (fun lab _ _ _ _ _ => lab = ⟨.twA, 4, labJ.n⟩) := hlabJ'
  exact y10xD_core (C := C) (N := ⁅closureIn J C, GLAPPrimeCoreOf p' (closureIn J C)⁆) (x := x)
    hs hs2 hp hxx hx hJC hJx hJq hsJ hJY hY hJp hJs hNp rfl hdistY hI25 hG hm2 hodd
    ⟨.twA, 4, labJ.n⟩ hMJ (fun K₀ _ _ hM => hU5'.2 K₀ hM)

section Ranks

variable {Q : Type} [Group Q] [Finite Q]

theorem y10xE_isMulComm_of_forall {E : Subgroup Q} (h : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    IsMulCommutative E :=
  ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩

theorem y10xE_comm_of_elemAb {p : ℕ} {A : Subgroup Q} (hA : CFSG.Open.IsElemAbelian p A)
    {a b : Q} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem y10xE_elemAb_mono {p : ℕ} {A T : Subgroup Q} (hA : CFSG.Open.IsElemAbelian p A)
    (hTA : T ≤ A) : CFSG.Open.IsElemAbelian p T :=
  ⟨y10xE_isMulComm_of_forall fun x hx y hy => y10xE_comm_of_elemAb hA (hTA hx) (hTA hy),
    fun x hx => hA.2 x (hTA hx)⟩

theorem y10xE_pRank_le_card {p : ℕ} (hp : p.Prime) (H : Subgroup Q) :
    CFSG.Open.pRank p H ≤ Nat.card Q := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp.one_lt
  have h2 : p ^ CFSG.Open.pRank p H ≤ Nat.card Q := hE ▸ Subgroup.card_le_card_group E
  omega

theorem y10xE_bdd_pRank {p : ℕ} (hp : p.Prime) (H : Subgroup Q) :
    BddAbove {k | ∃ E : Subgroup Q, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
  refine ⟨Nat.card Q, ?_⟩
  rintro k ⟨E, -, -, hE⟩
  have h1 : k < p ^ k := Nat.lt_pow_self hp.one_lt
  have h2 : p ^ k ≤ Nat.card Q := hE ▸ Subgroup.card_le_card_group E
  omega

theorem y10xE_bdd_twoLocal {p : ℕ} (hp : p.Prime) :
    BddAbove {k | ∃ H : Subgroup Q, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := by
  refine ⟨Nat.card Q, ?_⟩
  rintro k ⟨H, -, rfl⟩
  exact y10xE_pRank_le_card hp H

theorem y10xE_pRank_le_twoLocal {p : ℕ} (hp : p.Prime) (H : Subgroup Q)
    (hH : CFSG.Open.IsTwoLocal H) :
    CFSG.Open.pRank p H ≤ GLATwoLocalRank p Q :=
  le_csSup (y10xE_bdd_twoLocal hp) ⟨H, hH, rfl⟩

theorem y10xE_le_pRank {p : ℕ} (hp : p.Prime) {H F : Subgroup Q} (hFH : F ≤ H)
    (hF : CFSG.Open.IsElemAbelian p F) {k : ℕ} (hk : Nat.card F = p ^ k) :
    k ≤ CFSG.Open.pRank p H :=
  le_csSup (y10xE_bdd_pRank hp H) ⟨F, hFH, hF, hk⟩

theorem y10xE_le_twoLocal_of_elemAb {p : ℕ} (hp : p.Prime) {S : Subgroup Q} (hS : S ≠ ⊥)
    (hSp : IsPGroup 2 S) {F : Subgroup Q} (hF : F ≤ Subgroup.normalizer (S : Set Q))
    (hFe : CFSG.Open.IsElemAbelian p F) {k : ℕ} (hk : Nat.card F = p ^ k) :
    k ≤ GLATwoLocalRank p Q := by
  have hT : CFSG.Open.IsTwoLocal (Subgroup.normalizer (S : Set Q)) := ⟨S, hS, hSp, rfl⟩
  exact (y10xE_le_pRank hp hF hFe hk).trans (y10xE_pRank_le_twoLocal hp _ hT)

theorem y10xE_attain {H : Type} [Group H] [Finite H] (S0 : Subgroup H) (hS0 : S0 ≠ ⊥)
    (hS0p : IsPGroup 2 S0) :
    ∃ S : Subgroup H, S ≠ ⊥ ∧ IsPGroup 2 S ∧ ∃ A : Subgroup H,
      A ≤ Subgroup.normalizer (S : Set H) ∧ CFSG.Open.IsElemAbelian 3 A ∧
        Nat.card A = 3 ^ GLATwoLocalRank 3 H := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  by_cases hne : {k | ∃ H0 : Subgroup H, CFSG.Open.IsTwoLocal H0 ∧ CFSG.Open.pRank 3 H0 = k}.Nonempty
  · have hmem := Nat.sSup_mem hne (y10xE_bdd_twoLocal (Q := H) h3)
    obtain ⟨H0, hH0, hH0k⟩ := hmem
    obtain ⟨P, hP, hPp, rfl⟩ := hH0
    obtain ⟨A, hAle, hAel, hAcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
      (Subgroup.normalizer (P : Set H))
    refine ⟨P, hP, hPp, A, hAle, hAel, ?_⟩
    have : GLATwoLocalRank 3 H = CFSG.Open.pRank 3 (Subgroup.normalizer (P : Set H)) := hH0k.symm
    rw [hAcard, this]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨S0, hS0, hS0p, ⊥, bot_le, ⟨y10xE_isMulComm_of_forall ?_, ?_⟩, ?_⟩
    · intro x hx y hy
      rw [Subgroup.mem_bot] at hx hy
      rw [hx, one_mul, mul_one]
    · intro x hx
      rw [Subgroup.mem_bot] at hx
      rw [hx, one_pow]
    · have h0 : GLATwoLocalRank 3 H = 0 := by
        show sSup {k | ∃ H0 : Subgroup H, CFSG.Open.IsTwoLocal H0 ∧ CFSG.Open.pRank 3 H0 = k} = 0
        rw [hne, csSup_empty]
        rfl
      rw [h0]
      simp

theorem y10xE_elem_of_bot {A B : Subgroup Q} (h : ⁅A, B⁆ = ⊥) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h ha
  exact (Subgroup.mem_centralizer_iff.1 h1 b hb).symm

theorem y10xE_bot_of_elem {A B : Subgroup Q} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ⁅A, B⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (h a ha b hb).symm

theorem y10xE_elemAb_sup {p : ℕ} {A B : Subgroup Q} (hA : CFSG.Open.IsElemAbelian p A)
    (hB : CFSG.Open.IsElemAbelian p B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    CFSG.Open.IsElemAbelian p (A ⊔ B) := by
  have hpair : ∀ a ∈ A, ∀ b ∈ B, ∀ a' ∈ A, ∀ b' ∈ B, Commute (a * b) (a' * b') := by
    intro a ha b hb a' ha' b' hb'
    have h1 : Commute a a' := y10xE_comm_of_elemAb hA ha ha'
    have h2 : Commute b b' := y10xE_comm_of_elemAb hB hb hb'
    have h3 : Commute a b' := hAB a ha b' hb'
    have h4 : Commute b a' := (hAB a' ha' b hb).symm
    have h5 : Commute (a * b) a' := Commute.mul_left h1 h4
    have h6 : Commute (a * b) b' := Commute.mul_left h3 h2
    exact Commute.mul_right h5 h6
  have hcomm : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := y10xA_mem_sup_of_commute (y10xA_commute_of_bot (y10xE_bot_of_elem hAB)) hx
    obtain ⟨a', ha', b', hb', rfl⟩ := y10xA_mem_sup_of_commute (y10xA_commute_of_bot (y10xE_bot_of_elem hAB)) hy
    exact (hpair a ha b hb a' ha' b' hb').eq
  refine ⟨y10xE_isMulComm_of_forall hcomm, fun x hx => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := y10xA_mem_sup_of_commute (y10xA_commute_of_bot (y10xE_bot_of_elem hAB)) hx
  have hc : Commute a b := hAB a ha b hb
  rw [hc.mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

theorem y10xE_card_sup_mul {A B : Subgroup Q} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card (A ⊔ B : Subgroup Q) * Nat.card (A ⊓ B : Subgroup Q) =
      Nat.card A * Nat.card B := by
  have hmul : ∀ x y : ↥A × ↥B, ((x.1 : Q) * (y.1 : Q)) * ((x.2 : Q) * (y.2 : Q)) =
      ((x.1 : Q) * (x.2 : Q)) * ((y.1 : Q) * (y.2 : Q)) := by
    intro x y
    have h := hAB (y.1 : Q) y.1.2 (x.2 : Q) x.2.2
    calc ((x.1 : Q) * (y.1 : Q)) * ((x.2 : Q) * (y.2 : Q))
        = (x.1 : Q) * ((y.1 : Q) * (x.2 : Q)) * (y.2 : Q) := by group
      _ = (x.1 : Q) * ((x.2 : Q) * (y.1 : Q)) * (y.2 : Q) := by rw [h]
      _ = ((x.1 : Q) * (x.2 : Q)) * ((y.1 : Q) * (y.2 : Q)) := by group
  let φ : ↥A × ↥B →* Q := MonoidHom.mk' (fun x => (x.1 : Q) * (x.2 : Q)) (fun x y => hmul x y)
  have hφ : ∀ x : ↥A × ↥B, φ x = (x.1 : Q) * (x.2 : Q) := fun x => rfl
  have hrange : φ.range = A ⊔ B := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hφ]
      exact (A ⊔ B).mul_mem ((le_sup_left : A ≤ A ⊔ B) x.1.2) ((le_sup_right : B ≤ A ⊔ B) x.2.2)
    · refine sup_le ?_ ?_
      · intro a ha
        refine ⟨(⟨a, ha⟩, 1), ?_⟩
        rw [hφ]
        simp
      · intro b hb
        refine ⟨(1, ⟨b, hb⟩), ?_⟩
        rw [hφ]
        simp
  have hk : ∀ z : φ.ker, (z.1.2 : Q) = ((z.1.1 : Q))⁻¹ := by
    intro z
    have h1 : (z.1.1 : Q) * (z.1.2 : Q) = 1 := by
      have h2 := z.2
      rw [MonoidHom.mem_ker, hφ] at h2
      exact h2
    exact eq_inv_of_mul_eq_one_right h1
  have hker : Nat.card φ.ker = Nat.card (A ⊓ B : Subgroup Q) := by
    refine Nat.card_congr
      { toFun := fun z => ⟨(z.1.1 : Q), ?_⟩
        invFun := fun t => ⟨(⟨(t : Q), (Subgroup.mem_inf.1 t.2).1⟩,
          ⟨(t : Q)⁻¹, B.inv_mem (Subgroup.mem_inf.1 t.2).2⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · refine Subgroup.mem_inf.2 ⟨z.1.1.2, ?_⟩
      have h3 : (z.1.1 : Q)⁻¹ ∈ B := by
        rw [← hk z]
        exact z.1.2.2
      simpa using B.inv_mem h3
    · rw [MonoidHom.mem_ker, hφ]
      simp
    · intro z
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact (hk z).symm
    · intro t
      rfl
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hrange, hker, Nat.card_prod] at h
  rw [mul_comm]
  exact h

end Ranks


section Count

variable {Q : Type} [Group Q] [Finite Q]

theorem y10xE_normalizes_of_comm {S : Subgroup Q} {g : Q} (hg : ∀ h ∈ S, g * h = h * g) :
    g ∈ Subgroup.normalizer (S : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : g * h * g⁻¹ = h := by
      rw [hg h hh]
      group
    rw [e]
    exact hh
  · intro hs
    have hinv : ∀ s ∈ S, g⁻¹ * s = s * g⁻¹ := by
      intro s hs'
      have h1 := hg s hs'
      calc g⁻¹ * s = g⁻¹ * (s * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * s) * g⁻¹ := by rw [h1]
        _ = s * g⁻¹ := by group
    have e2 : h = g * h * g⁻¹ := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = (g * h * g⁻¹) * g⁻¹ * g := by rw [hinv _ hs]
        _ = g * h * g⁻¹ := by group
    rw [e2]
    exact hs

theorem y10xE_pow3_pair {X Y a e : ℕ} (h : X * Y = 3 ^ a * 3 ^ e) :
    ∃ k t : ℕ, X = 3 ^ k ∧ Y = 3 ^ t ∧ k + t = a + e := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hX : X ∣ 3 ^ (a + e) := by
    rw [pow_add, ← h]
    exact dvd_mul_right X Y
  have hY : Y ∣ 3 ^ (a + e) := by
    rw [pow_add, ← h]
    exact dvd_mul_left Y X
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hX
  obtain ⟨t, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hY
  refine ⟨k, t, rfl, rfl, ?_⟩
  rw [← pow_add, ← pow_add] at h
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h

theorem y10xE_count {Y0 Y1 S A E1 : Subgroup Q} {a e z : ℕ}
    (hcomm : ∀ x ∈ Y0, ∀ y ∈ Y1, x * y = y * x)
    (hS : S ≤ Y0) (hA : A ≤ Y0) (hAN : A ≤ Subgroup.normalizer (S : Set Q))
    (hAe : CFSG.Open.IsElemAbelian 3 A) (hAc : Nat.card A = 3 ^ a)
    (hE : E1 ≤ Y1) (hEe : CFSG.Open.IsElemAbelian 3 E1) (hEc : Nat.card E1 = 3 ^ e)
    (hZ : ∀ T : Subgroup Q, T ≤ Y0 → (∀ t ∈ T, ∀ y ∈ Y0, t * y = y * t) →
      CFSG.Open.IsElemAbelian 3 T → Nat.card T ≤ 3 ^ z) :
    ∃ F : Subgroup Q, F ≤ Subgroup.normalizer (S : Set Q) ∧ CFSG.Open.IsElemAbelian 3 F ∧
      ∃ k : ℕ, Nat.card F = 3 ^ k ∧ a + e ≤ k + z := by
  have hcAE : ∀ x ∈ A, ∀ y ∈ E1, x * y = y * x := fun x hx y hy =>
    hcomm x (hA hx) y (hE hy)
  have hE1N : E1 ≤ Subgroup.normalizer (S : Set Q) := by
    intro g hg
    apply y10xE_normalizes_of_comm
    intro h hh
    exact (hcomm h (hS hh) g (hE hg)).symm
  have hF : CFSG.Open.IsElemAbelian 3 (A ⊔ E1) := y10xE_elemAb_sup hAe hEe hcAE
  have hTz := hZ (A ⊓ E1 : Subgroup Q) (inf_le_left.trans hA) (fun t ht y hy =>
    (hcomm y hy t (hE (Subgroup.mem_inf.1 ht).2)).symm) (y10xE_elemAb_mono hAe inf_le_left)
  have hprod := y10xE_card_sup_mul hcAE
  rw [hAc, hEc] at hprod
  obtain ⟨k, t, hk, ht, hkt⟩ := y10xE_pow3_pair hprod
  have htz : t ≤ z := by
    rw [ht] at hTz
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hTz
  exact ⟨A ⊔ E1, sup_le hAN hE1N, hF, k, hk, by omega⟩

end Count


section QS

variable {H : Type} [Group H] [Finite H]

theorem y10xE_eq_top_of_sup_center (hH : commutator H = ⊤) {N : Subgroup H}
    (hN : N ⊔ Subgroup.center H = ⊤) : N = ⊤ := by
  have hnorm : ∀ n ∈ N, ∀ t ∈ Subgroup.center H, n * t * n⁻¹ ∈ Subgroup.center H := by
    intro n _ t ht
    have e : n * t * n⁻¹ = t := by
      rw [Subgroup.mem_center_iff.1 ht n]
      group
    rw [e]
    exact ht
  have key : commutator H ≤ N := by
    refine Subgroup.commutator_le.2 fun x _ y _ => ?_
    have hx : x ∈ N ⊔ Subgroup.center H := hN ▸ Subgroup.mem_top x
    have hy : y ∈ N ⊔ Subgroup.center H := hN ▸ Subgroup.mem_top y
    obtain ⟨n, hn, z, hz, rfl⟩ := lemma117_diag_sup_decomp_norm hnorm hx
    obtain ⟨n', hn', z', hz', rfl⟩ := lemma117_diag_sup_decomp_norm hnorm hy
    have hza : Commute z n := (Subgroup.mem_center_iff.1 hz n).symm
    have hzb : Commute z n' := (Subgroup.mem_center_iff.1 hz n').symm
    have hwa : Commute z' n := (Subgroup.mem_center_iff.1 hz' n).symm
    have hwb : Commute z' n' := (Subgroup.mem_center_iff.1 hz' n').symm
    have hzw : Commute z z' := (Subgroup.mem_center_iff.1 hz z').symm
    rw [y10xA_comm_central hza hzb hwa hwb hzw]
    exact y10xA_comm_mem_gen hn hn'
  rw [hH] at key
  exact top_le_iff.1 key

theorem y10xE_sup_center_of_map_top {M : Subgroup H}
    (h : M.map (QuotientGroup.mk' (Subgroup.center H)) = ⊤) : M ⊔ Subgroup.center H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : QuotientGroup.mk' (Subgroup.center H) g ∈ M.map (QuotientGroup.mk' (Subgroup.center H)) :=
    h ▸ Subgroup.mem_top _
  obtain ⟨n, hn, hnk⟩ := Subgroup.mem_map.1 hg
  have hz : n⁻¹ * g ∈ Subgroup.center H := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hnk
    exact QuotientGroup.eq.1 hnk
  have e : g = n * (n⁻¹ * g) := by group
  rw [e]
  exact (M ⊔ Subgroup.center H).mul_mem ((le_sup_left : M ≤ M ⊔ Subgroup.center H) hn)
    ((le_sup_right : Subgroup.center H ≤ M ⊔ Subgroup.center H) hz)

theorem y10xE_le_center_of_map_bot {M : Subgroup H}
    (h : M.map (QuotientGroup.mk' (Subgroup.center H)) = ⊥) : M ≤ Subgroup.center H := by
  intro n hn
  have hg : QuotientGroup.mk' (Subgroup.center H) n ∈ M.map (QuotientGroup.mk' (Subgroup.center H)) :=
    Subgroup.mem_map.2 ⟨n, hn, rfl⟩
  rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg
  exact hg

theorem y10xE_normal_dich (hH : CFSG.Open.IsQuasisimple H) {N : Subgroup H} (hN : N.Normal) :
    N ≤ Subgroup.center H ∨ N = ⊤ := by
  obtain ⟨hcomm, hsimp⟩ := hH
  haveI := hsimp
  have hmap : (N.map (QuotientGroup.mk' (Subgroup.center H))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  haveI := hmap
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center H))) with h0 | h1
  · exact Or.inl (y10xE_le_center_of_map_bot h0)
  · exact Or.inr (y10xE_eq_top_of_sup_center hcomm (y10xE_sup_center_of_map_top h1))

theorem y10xE_subnormal_simple {K₀ : Type} [Group K₀] [Finite K₀] [IsSimpleGroup K₀]
    {A B : Subgroup K₀} (h : CFSG.Open.IsSubnormal A B) : B = ⊤ → A = ⊥ ∨ A = ⊤ := by
  induction h with
  | refl H' => intro hH'; exact Or.inr hH'
  | @step A' B' C' hle hnorm _ ih =>
    intro hC
    rcases ih hC with hB | hB
    · left
      exact le_bot_iff.1 (hB ▸ hle)
    · subst hB
      have hN : A'.Normal := ⟨fun n hn g => by
        have h1 := hnorm.conj_mem ⟨n, Subgroup.mem_top n⟩ (Subgroup.mem_subgroupOf.2 hn)
          ⟨g, Subgroup.mem_top g⟩
        have h2 := Subgroup.mem_subgroupOf.1 h1
        simpa using h2⟩
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal A'

theorem y10xE_eq_of_subnormal_qs (hH : CFSG.Open.IsQuasisimple H) {M : Subgroup H}
    (hM : CFSG.Open.IsSubnormal M ⊤) (hMq : CFSG.Open.IsQuasisimple ↥M) : M = ⊤ := by
  obtain ⟨hcomm, hsimp⟩ := hH
  haveI := hsimp
  have hsub := CFSG.Open.IsSubnormal.map (QuotientGroup.mk' (Subgroup.center H)) hM
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hsub
  rcases y10xE_subnormal_simple hsub rfl with h0 | h1
  · exfalso
    have hle := y10xE_le_center_of_map_bot h0
    have hbot : ⁅M, M⁆ = ⊥ := y10xE_bot_of_elem fun a _ b hb =>
      Subgroup.mem_center_iff.1 (hle hb) a
    have h1 := y10xA_qs_comm_self hMq
    have h2 := y10xA_qs_ne_bot hMq
    rw [hbot] at h1
    exact h2 h1.symm
  · exact y10xE_eq_top_of_sup_center hcomm (y10xE_sup_center_of_map_top h1)

end QS




section CentreQuot

variable {H : Type} [Group H] [Finite H]

theorem y10xE_central_of_quot (hH : commutator H = ⊤) {Z : Subgroup H} (hZ : Z ≤ Subgroup.center H)
    {h : H} (hc : ∀ g : H, h⁻¹ * g⁻¹ * h * g ∈ Z) : h ∈ Subgroup.center H := by
  set q : H → H := fun g => h⁻¹ * g⁻¹ * h * g with hqdef
  have hqZ : ∀ g, q g ∈ Subgroup.center H := fun g => hZ (hc g)
  have hstar : ∀ g : H, h * g = g * h * q g := by
    intro g
    simp only [hqdef]
    group
  have hcen : ∀ g w : H, q g * w = w * q g := fun g w =>
    (Subgroup.mem_center_iff.1 (hqZ g) w).symm
  have hmul : ∀ g g' : H, q (g * g') = q g' * q g := by
    intro g g'
    have e1 : h * (g * g') = (g * g') * h * (q g' * q g) := by
      calc h * (g * g') = (h * g) * g' := by group
        _ = (g * h * q g) * g' := by rw [hstar g]
        _ = g * h * (q g * g') := by group
        _ = g * h * (g' * q g) := by rw [hcen g g']
        _ = g * (h * g') * q g := by group
        _ = g * (g' * h * q g') * q g := by rw [hstar g']
        _ = (g * g') * h * (q g' * q g) := by group
    have e2 : h * (g * g') = (g * g') * h * q (g * g') := hstar (g * g')
    exact (mul_left_cancel (e1.symm.trans e2)).symm
  have hq1 : q 1 = 1 := by simp [hqdef]
  have hqinv : ∀ g, q g⁻¹ = (q g)⁻¹ := by
    intro g
    have h1 := hmul g g⁻¹
    rw [mul_inv_cancel, hq1] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have hcomm : ∀ a b : H, h * ⁅a, b⁆ = ⁅a, b⁆ * h := by
    intro a b
    have hab : q ⁅a, b⁆ = 1 := by
      rw [commutatorElement_def, hmul, hmul, hmul, hqinv, hqinv]
      have hc' : q b * q a = q a * q b := (hcen b (q a)).symm.trans (hcen a (q b)).symm |>.symm.trans
        (by rfl) |> fun _ => (Subgroup.mem_center_iff.1 (hqZ b) (q a)).symm
      rw [hc']
      group
    rw [hstar ⁅a, b⁆, hab, mul_one]
  have hT : commutator H ≤ Subgroup.centralizer ({h} : Set H) := by
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact hcomm a b
  rw [hH] at hT
  refine Subgroup.mem_center_iff.2 fun g => ?_
  have hg := Subgroup.mem_centralizer_iff.1 (hT (Subgroup.mem_top g)) h (Set.mem_singleton h)
  exact hg.symm

theorem y10xE_center_quot (hH : commutator H = ⊤) (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) :
    Subgroup.center (H ⧸ Z) = (Subgroup.center H).map (QuotientGroup.mk' Z) := by
  ext z
  constructor
  · intro hz
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
    refine ⟨h, y10xE_central_of_quot hH hZ (fun g => ?_), rfl⟩
    have h1 := (Subgroup.mem_center_iff.1 hz) (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h1
    have h2 := QuotientGroup.eq.1 h1
    have e : h⁻¹ * g⁻¹ * h * g = (g * h)⁻¹ * (h * g) := by group
    rw [e]
    exact h2
  · rintro ⟨h, hh, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
    show (QuotientGroup.mk g : H ⧸ Z) * QuotientGroup.mk h = QuotientGroup.mk h * QuotientGroup.mk g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hh g]

def y10xE_quot_center_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B := by
  refine QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e ?_
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    show e g' * e a = e a * e g'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 ha g']
  · intro hb
    refine ⟨e.symm b, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.1 hb (e g)

theorem y10xE_qs_quot (hH : CFSG.Open.IsQuasisimple H) {Z : Subgroup H} [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) (hZne : Z ≠ ⊤) : CFSG.Open.IsQuasisimple (H ⧸ Z) := by
  have hK : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup H) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hH
  have hK' : CFSG.IsQuasisimple ↥(⊤ : Subgroup H) := (y10xA_fnd_iff_open _).2 hK
  have hnot : ¬ (⊤ : Subgroup H) ≤ (QuotientGroup.mk' Z).ker := by
    rw [QuotientGroup.ker_mk']
    intro h
    exact hZne (eq_top_iff.2 h)
  have hq := CFSG.LocalCores.isQuasisimple_map hK' (QuotientGroup.mk' Z) hnot
  have hmapTop : (⊤ : Subgroup H).map (QuotientGroup.mk' Z) = ⊤ :=
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hq' : CFSG.Open.IsQuasisimple ↥((⊤ : Subgroup H).map (QuotientGroup.mk' Z)) :=
    (y10xA_fnd_iff_open _).1 hq
  exact CFSG.Open.IsQuasisimple.of_mulEquiv
    (((MulEquiv.subgroupCongr hmapTop).trans Subgroup.topEquiv).symm) hq'

def y10xE_quot_quot_center_equiv (hH : commutator H = ⊤) (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) :
    (H ⧸ Z) ⧸ Subgroup.center (H ⧸ Z) ≃* H ⧸ Subgroup.center H := by
  have hc := y10xE_center_quot hH Z hZ
  refine (QuotientGroup.quotientMulEquivOfEq hc).trans ?_
  exact QuotientGroup.quotientQuotientEquivQuotient Z (Subgroup.center H) hZ

end CentreQuot

section CO

variable {G : Type} [Group G] [Finite G]

theorem y10xE_barX_perfect_nontriv {C J : Subgroup G} (hJC : J ≤ C)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (h3J : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    ⁅barX 3 C J, barX 3 C J⁆ = barX 3 C J ∧ barX 3 C J ≠ ⊥ := by
  have hJnot : ¬ J ≤ GLAPPrimeCoreOf 3 C := by
    intro hle
    have h1 : Nat.card J ∣ Nat.card (GLAPPrimeCoreOf 3 C) := Subgroup.card_dvd_of_le hle
    have h2 : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 C) :=
      not_dvd_card_glaPPrimeCoreOf Nat.prime_three C
    have h3 : 3 ∣ Nat.card J := h3J.trans (Subgroup.card_quotient_dvd_card _)
    exact h2 (h3.trans h1)
  constructor
  · rw [← barX_commutator 3 hJC hJC, y10xA_qs_comm_self hJq]
  · intro h
    obtain ⟨j, hj, hjO⟩ := SetLike.not_le_iff_exists.1 hJnot
    have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) (⟨j, hJC hj⟩ : ↥C) ∈ barX 3 C J :=
      Subgroup.mem_map.2 ⟨⟨j, hJC hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hjO (y10xA_of_mem_core (hJC hj) hmem)

end CO


section Criterion

theorem y10xE_qs_of_surj {G' Γ : Type} [Group G'] [Group Γ] [Finite G'] (f : G' →* Γ)
    {B : Subgroup G'} (hperf : ⁅B, B⁆ = B) (hT : CFSG.Open.IsQuasisimple ↥(B.map f))
    (hker : ∀ b ∈ B, f b = 1 → ∀ c ∈ B, c * b = b * c) : CFSG.Open.IsQuasisimple ↥B := by
  have hmapTop : (⊤ : Subgroup ↥B).map B.subtype = B := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcommB : commutator ↥B = ⊤ := by
    apply Subgroup.map_injective (f := B.subtype) B.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, hmapTop, hperf]
  let f' : ↥B →* ↥(B.map f) :=
    (f.comp B.subtype).codRestrict (B.map f) (fun b => Subgroup.mem_map.2 ⟨b, b.2, rfl⟩)
  have hsurj : Function.Surjective f' := by
    intro t
    obtain ⟨z, hz, hzt⟩ := Subgroup.mem_map.1 t.2
    exact ⟨⟨z, hz⟩, Subtype.ext hzt⟩
  have hkerc : f'.ker ≤ Subgroup.center ↥B := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hz1 : f z.1 = 1 := congrArg Subtype.val hz
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact hker z.1 z.2 hz1 c.1 c.2
  have e1 := y10xE_quot_quot_center_equiv hcommB f'.ker hkerc
  have e2 := QuotientGroup.quotientKerEquivOfSurjective f' hsurj
  have e3 := y10xE_quot_center_equiv e2
  haveI : IsSimpleGroup (↥(B.map f) ⧸ Subgroup.center ↥(B.map f)) := hT.2
  have hsimp : IsSimpleGroup (↥B ⧸ Subgroup.center ↥B) := MulEquiv.isSimpleGroup (e1.symm.trans e3)
  exact ⟨hcommB, hsimp⟩

end Criterion




section Orbit

variable {G : Type} [Group G] [Finite G]

theorem y10xE_barX_conj {C Y : Subgroup G} {g : G} (hg : g ∈ C) :
    barX 3 C (GLBConj g Y) =
      (barX 3 C Y).map (MulAut.conj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) (⟨g, hg⟩ : ↥C))⁻¹).toMonoidHom := by
  ext z
  constructor
  · intro hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
    have hcG : (c : G) ∈ GLBConj g Y := Subgroup.mem_subgroupOf.1 hc
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.1 hcG
    have hyc' : g⁻¹ * y * g⁻¹⁻¹ = (c : G) := hyc
    rw [inv_inv] at hyc'
    have hyC : y ∈ C := by
      have : y = g * (c : G) * g⁻¹ := by
        rw [← hyc']
        group
      rw [this]
      exact C.mul_mem (C.mul_mem hg c.2) (C.inv_mem hg)
    refine Subgroup.mem_map.2 ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) (⟨y, hyC⟩ : ↥C),
      Subgroup.mem_map.2 ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩, ?_⟩
    have hsub : ((⟨g, hg⟩ : ↥C)⁻¹ * ⟨y, hyC⟩ * ⟨g, hg⟩ : ↥C) = c := Subtype.ext (by simpa using hyc')
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← map_inv, ← map_mul, ← map_mul, hsub]
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.1 hw
    have hc'Y : (c' : G) ∈ Y := Subgroup.mem_subgroupOf.1 hc'
    have hmem : ((⟨g, hg⟩ : ↥C)⁻¹ * c' * ⟨g, hg⟩ : ↥C) ∈ (GLBConj g Y).subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_map.2 ⟨(c' : G), hc'Y, ?_⟩
      simp [MulAut.conj_apply]
    have e : (MulEquiv.toMonoidHom (MulAut.conj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)
        (⟨g, hg⟩ : ↥C))⁻¹)) (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) c') =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ((⟨g, hg⟩ : ↥C)⁻¹ * c' * ⟨g, hg⟩ : ↥C) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [← map_inv, ← map_mul, ← map_mul]
    rw [e]
    exact Subgroup.mem_map.2 ⟨_, hmem, rfl⟩

theorem y10xE_orbit_contra {p : ℕ} (hp : p.Prime) {C J Y₀ : Subgroup G} {x : G}
    (hxC : x ∈ C) (hx : x ^ p = 1) (hJC : J ≤ C) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (h3J : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) (hJx : ∀ j ∈ J, x * j = j * x)
    (hY₀ : GLAPComponent 3 C Y₀) (hJsup : J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y₀)
    (hcomm0 : ∀ a ∈ barX 3 C Y₀, ∀ t ∈ barX 3 C J, a * t = t * a) : False := by
  obtain ⟨hperf, hnt⟩ := y10xE_barX_perfect_nontriv hJC hJq h3J
  have hYC : Y₀ ≤ C := hY₀.1
  have hxpow : ∀ n : ℕ, x ^ n ∈ C := fun n => C.pow_mem hxC n
  have hFC : ∀ i : Fin p, GLBConj (x ^ (i : ℕ)) Y₀ ≤ C := by
    intro i
    have h1 := y10xA_gLBConj_le (C.inv_mem (hxpow (i : ℕ))) hYC
    rwa [inv_inv] at h1
  have hTsup : barX 3 C J ≤ ⨆ i : Fin p, barX 3 C (GLBConj (x ^ (i : ℕ)) Y₀) := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨hyC, hmem⟩ := y10xA_barX_iSup_mem (s := 3)
      (fun i : Fin p => GLBConj (x ^ (i : ℕ)) Y₀) (fun i => hFC i)
      (hJsup (Subgroup.mem_subgroupOf.1 hz))
    exact hmem
  have hxcomm : ∀ j ∈ J, ∀ n : ℕ, x ^ n * j = j * x ^ n := fun j hj n =>
    (Commute.pow_left (show Commute x j from hJx j hj) n)
  have hxT : ∀ n : ℕ, ∀ t ∈ barX 3 C J, (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) (⟨x ^ n, hxpow n⟩ : ↥C)) * t
      = t * QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) (⟨x ^ n, hxpow n⟩ : ↥C) := by
    intro n t ht
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 ht
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hxcomm _ (Subgroup.mem_subgroupOf.1 hc) n)
  have hcomm_i : ∀ i : Fin p, ∀ a ∈ barX 3 C (GLBConj (x ^ (i : ℕ)) Y₀), ∀ t ∈ barX 3 C J,
      a * t = t * a := by
    intro i a ha t ht
    rw [y10xE_barX_conj (hxpow (i : ℕ))] at ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
    set gg := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) (⟨x ^ (i : ℕ), hxpow (i : ℕ)⟩ : ↥C)) with hgg
    have hgt : gg * t = t * gg := hxT (i : ℕ) t ht
    have hgt' : gg⁻¹ * t = t * gg⁻¹ := by
      calc gg⁻¹ * t = gg⁻¹ * (t * gg) * gg⁻¹ := by group
        _ = gg⁻¹ * (gg * t) * gg⁻¹ := by rw [hgt]
        _ = t * gg⁻¹ := by group
    have hbt : b * t = t * b := hcomm0 b hb t ht
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc gg⁻¹ * b * gg * t = gg⁻¹ * b * (gg * t) := by group
      _ = gg⁻¹ * b * (t * gg) := by rw [hgt]
      _ = gg⁻¹ * (b * t) * gg := by group
      _ = gg⁻¹ * (t * b) * gg := by rw [hbt]
      _ = (gg⁻¹ * t) * b * gg := by group
      _ = (t * gg⁻¹) * b * gg := by rw [hgt']
      _ = t * (gg⁻¹ * b * gg) := by group
  have hTc : ∀ t ∈ barX 3 C J, ∀ m ∈ ⨆ i : Fin p, barX 3 C (GLBConj (x ^ (i : ℕ)) Y₀), m * t = t * m :=
    fun t ht => y10xA_iSup_centralizes (fun i : Fin p => barX 3 C (GLBConj (x ^ (i : ℕ)) Y₀)) t
      (fun i z hz => hcomm_i i z hz t ht)
  have hab : ∀ a ∈ barX 3 C J, ∀ b ∈ barX 3 C J, a * b = b * a := fun a ha b hb =>
    hTc b hb a (hTsup ha)
  have hbot : ⁅barX 3 C J, barX 3 C J⁆ = ⊥ := y10xE_bot_of_elem hab
  rw [hbot] at hperf
  exact hnt hperf.symm

end Orbit


section Family

variable {G : Type} [Group G] [Finite G]

theorem y10xE_fam_le_img {C K N : Subgroup G} [(N.subgroupOf C).Normal]
    (a : Option (y10xA_I 3 C K)) : y10xA_fam 3 C K N a ≤ y10xA_img C N K := by
  cases a with
  | none => exact y10xA_img_mono (y10xA_coreOf_le K)
  | some Y => exact y10xA_img_mono inf_le_left

theorem y10xE_img_le_iSup_fam {C K N : Subgroup G} [(N.subgroupOf C).Normal] (hKC : K ≤ C)
    (hKP : K ≤ (⨆ Y : y10xA_I 3 C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf 3 C)) ⊔ GLAPPrimeCoreOf 3 K) :
    y10xA_img C N K ≤ ⨆ a, y10xA_fam 3 C K N a := by
  have hK : K ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 K : Subgroup G) : Set G) :=
    fun k hk => normalizer_le_normalizer_glaPPrimeCoreOf 3 K (Subgroup.le_normalizer hk)
  have hOKK : ∀ c ∈ K, ∀ t ∈ GLAPPrimeCoreOf 3 K, c * t * c⁻¹ ∈ GLAPPrimeCoreOf 3 K := by
    intro c hc t ht
    exact (Subgroup.mem_normalizer_iff.1 (hK hc) t).1 ht
  have hsupK : (⨆ Y : y10xA_I 3 C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf 3 C)) ≤ K :=
    iSup_le fun Y => inf_le_left
  intro z hz
  obtain ⟨c, hcK, rfl⟩ := y10xA_exists_of_mem_img hz
  obtain ⟨a, ha, o, ho, hao⟩ := lemma117_diag_sup_decomp_norm
    (A := ⨆ Y : y10xA_I 3 C K, K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf 3 C)) (B := GLAPPrimeCoreOf 3 K)
    (fun h hh t ht => hOKK h (hsupK hh) t ht) (hKP hcK)
  have haK : a ∈ K := hsupK ha
  have hoK : o ∈ K := y10xA_coreOf_le K ho
  have haC : a ∈ C := hKC haK
  have hoC : o ∈ C := hKC hoK
  have hsplit : QuotientGroup.mk' (N.subgroupOf C) c =
      QuotientGroup.mk' (N.subgroupOf C) (⟨a, haC⟩ : ↥C) * QuotientGroup.mk' (N.subgroupOf C) (⟨o, hoC⟩ : ↥C) := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hao.symm
  rw [hsplit]
  refine Subgroup.mul_mem _ ?_ ?_
  · have hm' := y10xA_img_iSup_mem (C := C) (N := N)
      (fun Y : y10xA_I 3 C K => K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf 3 C))
      (fun Y => inf_le_left.trans hKC) ha
    obtain ⟨hyC, hm⟩ := hm'
    have hle : (⨆ Y : y10xA_I 3 C K, y10xA_img C N (K ⊓ (Y.1 ⊔ GLAPPrimeCoreOf 3 C))) ≤
        ⨆ a', y10xA_fam 3 C K N a' :=
      iSup_le fun Y => le_iSup (fun a' => y10xA_fam 3 C K N a') (some Y)
    exact hle hm
  · exact le_iSup (fun a' => y10xA_fam 3 C K N a') none (y10xA_mem_img hoC ho)

theorem y10xE_gLBConj_KO {C K : Subgroup G} (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G)) {c : G} (hc : c ∈ C) :
    GLBConj c (K ⊔ GLAPPrimeCoreOf 3 C) = K ⊔ GLAPPrimeCoreOf 3 C := by
  have h1 : GLBConj c K = K := mem_normalizer_iff_gLBConj_eq.1 (hCK hc)
  have h2 : GLBConj c (GLAPPrimeCoreOf 3 C) = GLAPPrimeCoreOf 3 C := mem_normalizer_iff_gLBConj_eq.1 (hO hc)
  have h3 : GLBConj c (K ⊔ GLAPPrimeCoreOf 3 C) = GLBConj c K ⊔ GLBConj c (GLAPPrimeCoreOf 3 C) :=
    Subgroup.map_sup _ _ _
  rw [h3, h1, h2]

theorem y10xE_fam_comm {C K N : Subgroup G} [(N.subgroupOf C).Normal] (hKC : K ≤ C)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hcomm : ∀ k ∈ K, ∀ t ∈ GLAPPrimeCoreOf 3 K, ⁅k, t⁆ ∈ N)
    {a b : Option (y10xA_I 3 C K)} (hab : a ≠ b) :
    ⁅y10xA_fam 3 C K N a, y10xA_fam 3 C K N b⁆ = ⊥ := by
  have hOK : GLAPPrimeCoreOf 3 K ≤ K := y10xA_coreOf_le K
  have hcentral := y10xA_img_central (N := N) hKC hOK hcomm
  cases a with
  | none =>
    cases b with
    | none => exact absurd rfl hab
    | some Y =>
      refine y10xE_bot_of_elem fun u hu w hw => ?_
      have hw' : w ∈ y10xA_img C N K := y10xE_fam_le_img (some Y) hw
      exact (hcentral u hu w hw').symm
  | some Y =>
    cases b with
    | none =>
      refine y10xE_bot_of_elem fun u hu w hw => ?_
      have hu' : u ∈ y10xA_img C N K := y10xE_fam_le_img (some Y) hu
      exact hcentral w hw u hu'
    | some Y' =>
      have hne : Y'.1 ≠ Y.1 := fun h => hab (congrArg some (Subtype.ext h.symm))
      exact y10xA_bot_of_commute (y10xA_img_P_commute (s := 3) Nat.prime_three hKC hO hcomm
        Y.2.1 Y.2.2 Y'.2.1 Y'.2.2 hne)

theorem y10xE_fam_conj_none {C K N : Subgroup G} [(N.subgroupOf C).Normal] (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G)) {c : G} (hc : c ∈ C) :
    (y10xA_fam 3 C K N none).map (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨c, hc⟩ : ↥C))).toMonoidHom =
      y10xA_fam 3 C K N none := by
  have hOKn : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 K : Subgroup G) : Set G) :=
    fun d hd => normalizer_le_normalizer_glaPPrimeCoreOf 3 K (hCK hd)
  have hOKC : GLAPPrimeCoreOf 3 K ≤ C := (y10xA_coreOf_le K).trans hKC
  refine y10xA_map_conj_img_of hc hOKC hOKC (fun h hh => (Subgroup.mem_normalizer_iff.1 (hOKn hc) h).1 hh) ?_
  intro h hh
  have h2 := (Subgroup.mem_normalizer_iff.1 (hOKn (C.inv_mem hc)) h).1 hh
  simpa using h2

theorem y10xE_gLBConj_mem {C K : Subgroup G} (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    {c : G} (hc : c ∈ C) (Y : y10xA_I 3 C K) :
    GLAPComponent 3 C (GLBConj c⁻¹ Y.1) ∧ GLBConj c⁻¹ Y.1 ≤ K ⊔ GLAPPrimeCoreOf 3 C := by
  have hCfix : GLBConj c⁻¹ C = C := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (C.inv_mem hc))
  constructor
  · have h1 := glaPComponent_gLBConj Y.2.1 c⁻¹
    rwa [hCfix] at h1
  · have h2 : GLBConj c⁻¹ (K ⊔ GLAPPrimeCoreOf 3 C) = K ⊔ GLAPPrimeCoreOf 3 C :=
      y10xE_gLBConj_KO hKC hCK hO (C.inv_mem hc)
    exact (Subgroup.map_mono Y.2.2 : GLBConj c⁻¹ Y.1 ≤ GLBConj c⁻¹ (K ⊔ GLAPPrimeCoreOf 3 C)).trans h2.le

theorem y10xE_fam_conj_some {C K N : Subgroup G} [(N.subgroupOf C).Normal] (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) {c : G} (hc : c ∈ C) (Y : y10xA_I 3 C K) :
    (y10xA_fam 3 C K N (some Y)).map (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨c, hc⟩ : ↥C))).toMonoidHom =
      y10xA_fam 3 C K N (some ⟨GLBConj c⁻¹ Y.1, (y10xE_gLBConj_mem hKC hCK hO hc Y).1,
        (y10xE_gLBConj_mem hKC hCK hO hc Y).2⟩) := by
  have hYC : GLBConj c⁻¹ Y.1 ≤ C := y10xA_gLBConj_le hc Y.2.1.1
  have hY'C : GLBConj c⁻¹ Y.1 ≤ C := hYC
  refine y10xA_map_conj_img_of hc (inf_le_left.trans hKC) (inf_le_left.trans hKC)
    (y10xA_conj_P hKC Y.2.1.1 hKn hO hc) ?_
  intro h hh
  have h1 := y10xA_conj_P hKC hYC hKn hO (C.inv_mem hc) h hh
  have e : GLBConj (c⁻¹)⁻¹ (GLBConj c⁻¹ Y.1) = Y.1 := by
    rw [inv_inv]
    exact gLBConj_gLBConj_inv c Y.1
  rw [e] at h1
  rw [inv_inv] at h1
  exact h1

end Family

section Bridge

variable {G : Type} [Group G] [Finite G]

@[expose] def y10xE_rho {C N : Subgroup G} [(N.subgroupOf C).Normal] (hNO : N ≤ GLAPPrimeCoreOf 3 C) :
    (↥C ⧸ N.subgroupOf C) →* (↥C ⧸ GLAPPrimeCore 3 ↥C) :=
  QuotientGroup.map (N.subgroupOf C) (GLAPPrimeCore 3 ↥C) (MonoidHom.id ↥C)
    (by
      intro n hn
      have hnG : (n : G) ∈ GLAPPrimeCoreOf 3 C := hNO (Subgroup.mem_subgroupOf.1 hn)
      exact y10xA_mem_core hnG n.2)

theorem y10xE_rho_mk' {C N : Subgroup G} [(N.subgroupOf C).Normal] (hNO : N ≤ GLAPPrimeCoreOf 3 C)
    (c : ↥C) :
    y10xE_rho hNO (QuotientGroup.mk' (N.subgroupOf C) c) = QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) c :=
  QuotientGroup.map_mk' _ _ _ _ _

theorem y10xE_rho_img {C N H : Subgroup G} [(N.subgroupOf C).Normal] (hNO : N ≤ GLAPPrimeCoreOf 3 C)
    (hHC : H ≤ C) :
    (y10xA_img C N H).map (y10xE_rho hNO) = barX 3 C H := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨c, hcH, rfl⟩ := y10xA_exists_of_mem_img hw
    rw [y10xE_rho_mk']
    exact Subgroup.mem_map.2 ⟨c, Subgroup.mem_subgroupOf.2 hcH, rfl⟩
  · intro hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
    have hcH : (c : G) ∈ H := Subgroup.mem_subgroupOf.1 hc
    have hmem := y10xA_mem_img (N := N) c.2 hcH
    refine Subgroup.mem_map.2 ⟨QuotientGroup.mk' (N.subgroupOf C) c, hmem, ?_⟩
    rw [y10xE_rho_mk']

end Bridge

section DiagY

variable {G : Type} [Group G] [Finite G]

theorem y10xE_barX_mono {C J K : Subgroup G} (hJK : J ≤ K) : barX 3 C J ≤ barX 3 C K := by
  intro t ht
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ht
  exact Subgroup.mem_map.2 ⟨z, Subgroup.mem_subgroupOf.2 (hJK (Subgroup.mem_subgroupOf.1 hz)), rfl⟩

theorem y10xE_comm_of_comp {C J : Subgroup G} {x : G}
    (hJc : CFSG.Open.IsComponentOf J (C ⊓ Subgroup.centralizer ({x} : Set G))) :
    ∀ j ∈ J, x * j = j * x := by
  intro j hj
  have h := (hJc.1 hj).2
  exact (Subgroup.mem_centralizer_singleton_iff.1 h).symm

theorem y10xE_Y_mem {p : ℕ} (hp : p.Prime) {C J : Subgroup G} {x : G} {K : Subgroup G}
    (hxC : x ∈ C) (hx : x ^ p = 1) (hJC : J ≤ C) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (h3J : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hJc : CFSG.Open.IsComponentOf J (C ⊓ Subgroup.centralizer ({x} : Set G)))
    (hKC : K ≤ C) (hJK : J ≤ K) (hKn : (K.subgroupOf C).Normal)
    {Y : Subgroup G} (hY : GLAPComponent 3 C Y)
    (hdiag : J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y) : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C := by
  rcases y10xA_cn_mod hY hKn with h | h
  · exact y10xA_le_sup_of_barX_le hKC hY.1 h
  · exfalso
    refine y10xE_orbit_contra hp hxC hx hJC hJq h3J (y10xE_comm_of_comp hJc) hY hdiag ?_
    intro a ha t ht
    exact (y10xE_elem_of_bot h) a ha t (y10xE_barX_mono hJK ht)

end DiagY

section OrbitAux

variable {G : Type} [Group G] [Finite G]

theorem y10xE_barX_P {C K Y : Subgroup G} (hKC : K ≤ C)
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hYC : Y ≤ C) :
    barX 3 C (K ⊓ (Y ⊔ GLAPPrimeCoreOf 3 C)) = barX 3 C Y := by
  have hOn : ∀ h ∈ C, ∀ t ∈ GLAPPrimeCoreOf 3 C, h * t * h⁻¹ ∈ GLAPPrimeCoreOf 3 C :=
    fun h hh t ht => (Subgroup.mem_normalizer_iff.1 (hO hh) t).1 ht
  have hmo : ∀ o : ↥C, (o : G) ∈ GLAPPrimeCoreOf 3 C →
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) o = 1 := by
    intro o ho
    exact (QuotientGroup.eq_one_iff _).2 (y10xA_mem_core ho o.2)
  apply le_antisymm
  · intro t ht
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ht
    have hzP : (z : G) ∈ K ⊓ (Y ⊔ GLAPPrimeCoreOf 3 C) := Subgroup.mem_subgroupOf.1 hz
    obtain ⟨y, hy, o, ho, hyo⟩ := lemma117_diag_sup_decomp_norm (A := Y) (B := GLAPPrimeCoreOf 3 C)
      (fun h hh t ht => hOn h (hYC hh) t ht) hzP.2
    have hyC : y ∈ C := hYC hy
    have hoC : o ∈ C := y10xA_coreOf_le C ho
    have hz_eq : z = (⟨y, hyC⟩ : ↥C) * (⟨o, hoC⟩ : ↥C) := Subtype.ext hyo.symm
    rw [hz_eq, map_mul, hmo ⟨o, hoC⟩ ho, mul_one]
    exact Subgroup.mem_map.2 ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  · intro t ht
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 ht
    have hcY : (c : G) ∈ Y := Subgroup.mem_subgroupOf.1 hc
    obtain ⟨k, hk, o, ho, hko⟩ := lemma117_diag_sup_decomp_norm (A := K) (B := GLAPPrimeCoreOf 3 C)
      (fun h hh t ht => hOn h (hKC hh) t ht) (hYK hcY)
    have hkP : k ∈ K ⊓ (Y ⊔ GLAPPrimeCoreOf 3 C) := by
      refine ⟨hk, ?_⟩
      have hk_eq : k = (c : G) * o⁻¹ := by
        rw [← hko]
        group
      rw [hk_eq]
      exact (Y ⊔ GLAPPrimeCoreOf 3 C).mul_mem ((le_sup_left : Y ≤ Y ⊔ GLAPPrimeCoreOf 3 C) hcY)
        ((le_sup_right : GLAPPrimeCoreOf 3 C ≤ Y ⊔ GLAPPrimeCoreOf 3 C)
          ((GLAPPrimeCoreOf 3 C).inv_mem ho))
    have hkC : k ∈ C := hKC hk
    have hoC : o ∈ C := y10xA_coreOf_le C ho
    have hc_eq : c = (⟨k, hkC⟩ : ↥C) * (⟨o, hoC⟩ : ↥C) := Subtype.ext hko.symm
    rw [hc_eq, map_mul, hmo ⟨o, hoC⟩ ho, mul_one]
    exact Subgroup.mem_map.2 ⟨⟨k, hkC⟩, Subgroup.mem_subgroupOf.2 hkP, rfl⟩

theorem y10xE_map_conj_pow {Q' : Type} [Group Q'] {H : Subgroup Q'} {σ : Q'}
    (hH : H.map (MulAut.conj σ).toMonoidHom = H) (m : ℕ) :
    H.map (MulAut.conj (σ ^ m)).toMonoidHom = H := by
  induction m with
  | zero =>
    have h1 : (MulAut.conj (σ ^ 0)).toMonoidHom = MonoidHom.id Q' := by
      ext y
      simp
    rw [h1, Subgroup.map_id]
  | succ m ih =>
    have hcomp : (MulAut.conj (σ ^ (m + 1))).toMonoidHom =
        (MulAut.conj (σ ^ m)).toMonoidHom.comp (MulAut.conj σ).toMonoidHom := by
      ext y
      simp [pow_succ, mul_assoc]
    rw [hcomp, ← Subgroup.map_map, hH, ih]

theorem y10xE_conj_img {C K N Y : Subgroup G} [(N.subgroupOf C).Normal] (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hYC : Y ≤ C) {c : G} (hc : c ∈ C) :
    (y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf 3 C))).map
        (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨c, hc⟩ : ↥C))).toMonoidHom =
      y10xA_img C N (K ⊓ (GLBConj c⁻¹ Y ⊔ GLAPPrimeCoreOf 3 C)) := by
  have hKn : ∀ d ∈ C, ∀ k ∈ K, d * k * d⁻¹ ∈ K := fun d hd k hk =>
    (Subgroup.mem_normalizer_iff.1 (hCK hd) k).1 hk
  have hYC' : GLBConj c⁻¹ Y ≤ C := y10xA_gLBConj_le hc hYC
  refine y10xA_map_conj_img_of hc (inf_le_left.trans hKC) (inf_le_left.trans hKC)
    (y10xA_conj_P hKC hYC hKn hO hc) ?_
  intro h hh
  have h1 := y10xA_conj_P hKC hYC' hKn hO (C.inv_mem hc) h hh
  have e : GLBConj (c⁻¹)⁻¹ (GLBConj c⁻¹ Y) = Y := by
    rw [inv_inv]
    exact gLBConj_gLBConj_inv c Y
  rw [e, inv_inv] at h1
  exact h1

end OrbitAux

section NonComm

variable {G : Type} [Group G] [Finite G]

theorem y10xE_noncomm {p : ℕ} (hp : p.Prime) {C J K N Y : Subgroup G} {x : G}
    (hxC : x ∈ C) (hx : x ^ p = 1) (hJC : J ≤ C) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (h3J : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hJc : CFSG.Open.IsComponentOf J (C ⊓ Subgroup.centralizer ({x} : Set G)))
    (hKC : K ≤ C) (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    [(N.subgroupOf C).Normal] (hNO : N ≤ GLAPPrimeCoreOf 3 C)
    (hY : GLAPComponent 3 C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C)
    (hdiag : J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y)
    (hJK : J ≤ K)
    (hall : ∀ g ∈ y10xA_img C N J, ∀ y ∈ y10xA_img C N (K ⊓ (Y ⊔ GLAPPrimeCoreOf 3 C)), g * y = y * g) :
    False := by
  have hOn : ∀ h ∈ C, ∀ t ∈ GLAPPrimeCoreOf 3 C, h * t * h⁻¹ ∈ GLAPPrimeCoreOf 3 C :=
    fun h hh t ht => (Subgroup.mem_normalizer_iff.1 (hO hh) t).1 ht
  have hYC : Y ≤ C := hY.1
  have hcomm0 : ∀ a ∈ barX 3 C Y, ∀ t ∈ barX 3 C J, a * t = t * a := by
    intro a ha t ht
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 ht
    have hcY : (c : G) ∈ Y := Subgroup.mem_subgroupOf.1 hc
    have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
    obtain ⟨k, hk, o, ho, hko⟩ := lemma117_diag_sup_decomp_norm (A := K) (B := GLAPPrimeCoreOf 3 C)
      (fun h hh t ht => hOn h (hKC hh) t ht) (hYK hcY)
    have hkP : k ∈ K ⊓ (Y ⊔ GLAPPrimeCoreOf 3 C) := by
      refine ⟨hk, ?_⟩
      have hk_eq : k = (c : G) * o⁻¹ := by
        rw [← hko]
        group
      rw [hk_eq]
      exact (Y ⊔ GLAPPrimeCoreOf 3 C).mul_mem ((le_sup_left : Y ≤ Y ⊔ GLAPPrimeCoreOf 3 C) hcY)
        ((le_sup_right : GLAPPrimeCoreOf 3 C ≤ Y ⊔ GLAPPrimeCoreOf 3 C)
          ((GLAPPrimeCoreOf 3 C).inv_mem ho))
    have hkC : k ∈ C := hKC hk
    have hoC : o ∈ C := y10xA_coreOf_le C ho
    have hc_eq : c = (⟨k, hkC⟩ : ↥C) * (⟨o, hoC⟩ : ↥C) := Subtype.ext hko.symm
    have hmo : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) (⟨o, hoC⟩ : ↥C) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (y10xA_mem_core ho hoC)
    have hkN := y10xA_mem_img (N := N) hkC hkP
    have hjN := y10xA_mem_img (N := N) j.2 hjJ
    have hcomm := hall _ hjN _ hkN
    have hrho_a : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) c =
        y10xE_rho hNO (QuotientGroup.mk' (N.subgroupOf C) (⟨k, hkC⟩ : ↥C)) := by
      rw [y10xE_rho_mk', hc_eq, map_mul, hmo, mul_one]
    have hrho_t : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) j =
        y10xE_rho hNO (QuotientGroup.mk' (N.subgroupOf C) (⟨(j : G), j.2⟩ : ↥C)) := by
      rw [y10xE_rho_mk']
    rw [hrho_a, hrho_t, ← map_mul (y10xE_rho hNO), ← map_mul (y10xE_rho hNO), hcomm.symm]
  exact y10xE_orbit_contra hp hxC hx hJC hJq h3J (y10xE_comm_of_comp hJc) hY hdiag hcomm0

end NonComm

section RData

variable {G : Type} [Group G] [Finite G]

theorem y10xE_Rdata {p : ℕ} (hp : p.Prime) {C J : Subgroup G} {x : G} (hxC : x ∈ C) (hx : x ^ p = 1)
    (hJC : J ≤ C) (hJlay : J ≤ GLAPLayer 3 C) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJc : CFSG.Open.IsComponentOf J (C ⊓ Subgroup.centralizer ({x} : Set G)))
    (h3J : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hNp : ⁅closureIn J C, GLAPPrimeCoreOf 3 (closureIn J C)⁆ ≤ GLAPPrimeCoreOf p (closureIn J C))
    [hNn : (⁅closureIn J C, GLAPPrimeCoreOf 3 (closureIn J C)⁆.subgroupOf C).Normal]
    {Y : Subgroup G} (hY : GLAPComponent 3 C Y)
    (hdiag : J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y) :
    y10xA_img C ⁅closureIn J C, GLAPPrimeCoreOf 3 (closureIn J C)⁆ J ≤
      ⨆ k : ℕ, y10xA_img C ⁅closureIn J C, GLAPPrimeCoreOf 3 (closureIn J C)⁆
        (closureIn J C ⊓ (GLBConj (x ^ k) Y ⊔ GLAPPrimeCoreOf 3 C)) := by
  classical
  set K : Subgroup G := closureIn J C with hKdef
  set O : Subgroup G := GLAPPrimeCoreOf 3 C with hOdef
  set OK : Subgroup G := GLAPPrimeCoreOf 3 K with hOKdef
  set N : Subgroup G := ⁅K, OK⁆ with hNdef
  have hKC : K ≤ C := y10xA_closureIn_le hJC
  have hCK : C ≤ Subgroup.normalizer (K : Set G) := y10xA_closureIn_normalizer
  have hJK : J ≤ K := y10xA_le_closureIn C.one_mem
  have hCn : C ≤ Subgroup.normalizer (C : Set G) := fun c hc => Subgroup.le_normalizer hc
  have hO : C ≤ Subgroup.normalizer (O : Set G) :=
    fun c hc => normalizer_le_normalizer_glaPPrimeCoreOf 3 C (hCn hc)
  have hKn : (K.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).2 hCK
  have hKn' : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun c hc k hk =>
    (Subgroup.mem_normalizer_iff.1 (hCK hc) k).1 hk
  have hOKK : K ≤ Subgroup.normalizer (OK : Set G) :=
    fun k hk => normalizer_le_normalizer_glaPPrimeCoreOf 3 K (Subgroup.le_normalizer hk)
  have hOKC : C ≤ Subgroup.normalizer (OK : Set G) :=
    fun c hc => normalizer_le_normalizer_glaPPrimeCoreOf 3 K (hCK hc)
  have hOK_le : OK ≤ K := y10xA_coreOf_le K
  have hNK : N ≤ K := Subgroup.commutator_le.2 fun a ha b hb => y10xA_comm_mem_gen ha (hOK_le hb)
  have hNOK : N ≤ OK := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    have h1 : a * b * a⁻¹ ∈ OK := (Subgroup.mem_normalizer_iff.1 (hOKK ha) b).1 hb
    exact OK.mul_mem h1 (OK.inv_mem hb)
  have hNC : N ≤ C := hNK.trans hKC
  have hN3 : ¬ 3 ∣ Nat.card N := fun h =>
    not_dvd_card_glaPPrimeCoreOf Nat.prime_three K (h.trans (Subgroup.card_dvd_of_le hNOK))
  have hNp' : ¬ p ∣ Nat.card N := fun h =>
    not_dvd_card_glaPPrimeCoreOf hp K (h.trans (Subgroup.card_dvd_of_le hNp))
  have hNO : N ≤ O :=
    le_glaPPrimeCoreOf_of_le_normalizer hNC (y10xA_comm_core_normalizer (s := 3) hCK)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3)
  have hcomm' : ∀ k ∈ K, ∀ t ∈ OK, ⁅k, t⁆ ∈ N := fun k hk t ht => Subgroup.commutator_mem_commutator hk ht
  have hJX := y10xA_J_le_sup (s := 3) Nat.prime_three hKC hJK hJC hJlay hKn hJq
  have hKX : K ≤ (⨆ Y' : y10xA_I 3 C K, Y'.1) ⊔ O :=
    y10xA_closureIn_le_of hJX (y10xA_sup_normalized (s := 3) hKC hCn hKn' hO)
  have hKP : K ≤ (⨆ Y' : y10xA_I 3 C K, K ⊓ (Y'.1 ⊔ O)) ⊔ OK :=
    y10xA_K_le_sup_P Nat.prime_three hKC hO hKX
  have hcov : y10xA_img C N K ≤ ⨆ a, y10xA_fam 3 C K N a := y10xE_img_le_iSup_fam hKC hKP
  have hKeq : y10xA_img C N K = ⨆ a, y10xA_fam 3 C K N a :=
    le_antisymm hcov (iSup_le fun a => y10xE_fam_le_img a)
  have hYK : Y ≤ K ⊔ O := y10xE_Y_mem hp hxC hx hJC hJq h3J hJc hKC hJK hKn hY hdiag
  set σ : ↥C ⧸ N.subgroupOf C := QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C)
    with hσdef
  have hσp : σ ^ p = 1 := by
    rw [hσdef, ← map_pow]
    have h1 : (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C) ^ p = 1 := Subtype.ext (by simp [inv_pow, hx])
    rw [h1, map_one]
  have hσfam : ∀ a, ∃ b, (y10xA_fam 3 C K N a).map (MulAut.conj σ).toMonoidHom = y10xA_fam 3 C K N b := by
    intro a
    cases a with
    | none => exact ⟨none, y10xE_fam_conj_none hKC hCK (C.inv_mem hxC)⟩
    | some Y' => exact ⟨_, y10xE_fam_conj_some hKC hCK hO hKn' (C.inv_mem hxC) Y'⟩
  have hcommF : ∀ i j : Option (y10xA_I 3 C K), (y10xA_fam 3 C K N) i ≠ (y10xA_fam 3 C K N) j →
      ⁅(y10xA_fam 3 C K N) i, (y10xA_fam 3 C K N) j⁆ = ⊥ := by
    intro i j hne
    exact y10xE_fam_comm hKC hO hcomm' (fun h => hne (by rw [h]))
  have hσcent : Subgroup.centralizer ({σ} : Set (↥C ⧸ N.subgroupOf C)) =
      Subgroup.centralizer ({QuotientGroup.mk' (N.subgroupOf C) (⟨x, hxC⟩ : ↥C)} :
        Set (↥C ⧸ N.subgroupOf C)) := by
    have h1 : σ = (QuotientGroup.mk' (N.subgroupOf C) (⟨x, hxC⟩ : ↥C))⁻¹ := by
      rw [hσdef, ← map_inv]
      rfl
    rw [h1]
    exact y10xA_centralizer_inv _
  have hJN : ¬ J ≤ N := fun hJN' =>
    not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
      ((h3J.trans (Subgroup.card_quotient_dvd_card _)).trans (Subgroup.card_dvd_of_le (hJN'.trans hNOK)))
  have hJs : CFSG.Open.IsSubnormal J (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
    have hJx : J ≤ K ⊓ Subgroup.centralizer ({x} : Set G) := le_inf hJK (fun j hj => (hJc.1 hj).2)
    have h1 := CFSG.Open.IsSubnormal.inf hJc.2.1 (K ⊓ Subgroup.centralizer ({x} : Set G))
    rw [inf_eq_left.2 hJx, inf_eq_right.2 (inf_le_inf_right _ hKC)] at h1
    exact h1
  have hkt := lemma117_khat_transport hp hxC hx hKC hNK hNp' hJK hJq hJN hJs
  have hJcomp : CFSG.Open.IsComponentOf (y10xA_img C N J)
      ((⨆ a, y10xA_fam 3 C K N a) ⊓ Subgroup.centralizer ({σ} : Set (↥C ⧸ N.subgroupOf C))) := by
    rw [← hKeq, hσcent]
    exact hkt
  obtain ⟨i₀, hnon, hJ0⟩ := y10xA_single_orbit (fun a => y10xA_fam 3 C K N a) σ p hp.pos hσp
    (y10xA_img C N J) (fun i j hne => hcommF i j hne) hσfam hJcomp
  set Yi : y10xA_I 3 C K := ⟨Y, hY, hYK⟩ with hYidef
  have hnc : ∃ g ∈ y10xA_img C N J, ∃ y ∈ y10xA_fam 3 C K N (some Yi), g * y ≠ y * g := by
    by_contra hcon
    push_neg at hcon
    exact y10xE_noncomm hp hxC hx hJC hJq h3J hJc hKC hO hNO hY hYK hdiag hJK
      (fun g hg y hy => hcon g hg y hy)
  obtain ⟨m, hm⟩ := hnon (some Yi) hnc
  have hstab : (y10xA_fam 3 C K N none).map (MulAut.conj σ).toMonoidHom = y10xA_fam 3 C K N none :=
    y10xE_fam_conj_none hKC hCK (C.inv_mem hxC)
  cases i₀ with
  | none =>
    exfalso
    obtain ⟨g, hg, y, hy, hne⟩ := hnc
    have h1 : y ∈ (y10xA_fam 3 C K N none).map (MulAut.conj (σ ^ m)).toMonoidHom := hm ▸ hy
    rw [y10xE_map_conj_pow hstab m] at h1
    exact hne (y10xA_img_central (N := N) hKC hOK_le hcomm' y h1 g (y10xA_img_mono hJK hg))
  | some Y₀ =>
    have hσm : ∀ n : ℕ, σ ^ n = QuotientGroup.mk' (N.subgroupOf C)
        (⟨(x⁻¹) ^ n, C.pow_mem (C.inv_mem hxC) n⟩ : ↥C) := by
      intro n
      rw [hσdef, ← map_pow]
      rfl
    have hconj_n : ∀ n : ℕ, (y10xA_fam 3 C K N (some Y₀)).map (MulAut.conj (σ ^ n)).toMonoidHom =
        y10xA_img C N (K ⊓ (GLBConj (x ^ n) Y₀.1 ⊔ O)) := by
      intro n
      rw [hσm n]
      have h1 := y10xE_conj_img (N := N) hKC hCK hO Y₀.2.1.1 (C.pow_mem (C.inv_mem hxC) n)
      rw [show ((x⁻¹) ^ n)⁻¹ = x ^ n by simp [inv_pow]] at h1
      exact h1
    have hm' : y10xA_img C N (K ⊓ (Y ⊔ O)) = y10xA_img C N (K ⊓ (GLBConj (x ^ m) Y₀.1 ⊔ O)) :=
      hm.trans (hconj_n m)
    have hZC : GLBConj (x ^ m) Y₀.1 ≤ C := by
      have h1 := y10xA_gLBConj_le (C.inv_mem (C.pow_mem hxC m)) Y₀.2.1.1
      rwa [inv_inv] at h1
    have hZcomp : GLAPComponent 3 C (GLBConj (x ^ m) Y₀.1) := by
      have h1 := glaPComponent_gLBConj Y₀.2.1 (x ^ m)
      have hCfix : GLBConj (x ^ m) C = C := mem_normalizer_iff_gLBConj_eq.1 (hCn (C.pow_mem hxC m))
      rwa [hCfix] at h1
    have hZKO : GLBConj (x ^ m) Y₀.1 ≤ K ⊔ O := by
      have h1 : GLBConj (x ^ m) (K ⊔ O) = K ⊔ O := y10xE_gLBConj_KO hKC hCK hO (C.pow_mem hxC m)
      exact (Subgroup.map_mono Y₀.2.2 : GLBConj (x ^ m) Y₀.1 ≤ GLBConj (x ^ m) (K ⊔ O)).trans h1.le
    have hHC1 : K ⊓ (Y ⊔ O) ≤ C := inf_le_left.trans hKC
    have hHC2 : K ⊓ (GLBConj (x ^ m) Y₀.1 ⊔ O) ≤ C := inf_le_left.trans hKC
    have hbar : barX 3 C Y = barX 3 C (GLBConj (x ^ m) Y₀.1) := by
      rw [← y10xE_barX_P hKC hO hYK hY.1, ← y10xE_barX_P hKC hO hZKO hZC]
      have h1 := congrArg (Subgroup.map (y10xE_rho hNO)) hm'
      rw [y10xE_rho_img hNO hHC1, y10xE_rho_img hNO hHC2] at h1
      exact h1
    have hYZ : Y = GLBConj (x ^ m) Y₀.1 := glaPComponent_unique hY hZcomp hbar
    have hpow : x ^ ((p - 1) * m) * x ^ m = 1 := by
      rw [← pow_add]
      have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
      have h2 : (p - 1) * m + m = p * m := by
        calc (p - 1) * m + m = (p - 1 + 1) * m := by ring
          _ = p * m := by rw [hp1]
      rw [h2, pow_mul, hx, one_pow]
    have hinvm : x ^ ((p - 1) * m) = (x ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    have hY₀eq : Y₀.1 = GLBConj (x ^ ((p - 1) * m)) Y := by
      rw [hinvm, hYZ, gLBConj_inv_gLBConj]
    have hshift : ∀ n : ℕ, GLBConj (x ^ n) Y₀.1 = GLBConj (x ^ ((p - 1) * m + n)) Y := by
      intro n
      rw [hY₀eq, gLBConj_gLBConj, pow_add]
    refine hJ0.trans (iSup_le fun n => ?_)
    have hterm : (y10xA_fam 3 C K N (some Y₀)).map (MulAut.conj (σ ^ n)).toMonoidHom =
        y10xA_img C N (K ⊓ (GLBConj (x ^ ((p - 1) * m + n)) Y ⊔ O)) := by
      rw [hconj_n n, hshift n]
    exact hterm.le.trans (le_iSup (fun k : ℕ => y10xA_img C N (K ⊓ (GLBConj (x ^ k) Y ⊔ O)))
      ((p - 1) * m + n))

end RData

section DiagAbs

variable {G : Type} [Group G] [Finite G]

theorem y10xF_subnormal_subgroupOf {H K : Subgroup G} (h : CFSG.Open.IsSubnormal H K) :
    CFSG.Open.IsSubnormal (H.subgroupOf K) ⊤ := by
  induction h with
  | refl H =>
    rw [Subgroup.subgroupOf_self]
    exact CFSG.Open.IsSubnormal.refl ⊤
  | @step H M K hHM hn hMK ih =>
    have hMN : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hn
    have hle : H.subgroupOf K ≤ M.subgroupOf K := fun y hy =>
      Subgroup.mem_subgroupOf.2 (hHM (Subgroup.mem_subgroupOf.1 hy))
    have hM'N : M.subgroupOf K ≤ Subgroup.normalizer ((H.subgroupOf K : Subgroup K) : Set K) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hyM : (y : G) ∈ M := Subgroup.mem_subgroupOf.1 hy
      have key := Subgroup.mem_normalizer_iff.1 (hMN hyM) (h : G)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact key
    exact CFSG.Open.IsSubnormal.step hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hM'N) ih

theorem y10xF_qs_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hc, hs⟩ := hA
  refine ⟨?_, ?_⟩
  · have h1 : (⁅(⊤ : Subgroup A), ⊤⁆ : Subgroup A) = ⊤ := by
      rw [← commutator_def]
      exact hc
    have h2 := congrArg (Subgroup.map e.toMonoidHom) h1
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective] at h2
    rw [commutator_def]
    exact h2
  · haveI := hs
    exact MulEquiv.isSimpleGroup (y10xE_quot_center_equiv e).symm

theorem y10xF_eq_of_subnormal {K M : Subgroup G} (hK : CFSG.Open.IsQuasisimple ↥K)
    (hMK : M ≤ K) (hsub : CFSG.Open.IsSubnormal M K) (hMq : CFSG.Open.IsQuasisimple ↥M) :
    M = K := by
  have h1 := y10xF_subnormal_subgroupOf hsub
  have hMq' : CFSG.Open.IsQuasisimple ↥(M.subgroupOf K) :=
    y10xF_qs_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMK).symm hMq
  have h2 := y10xE_eq_of_subnormal_qs hK h1 hMq'
  exact le_antisymm hMK (Subgroup.subgroupOf_eq_top.1 h2)

theorem y10xF_comm_central {Q : Type} [Group Q] {a b z w : Q}
    (hza : z * a = a * z) (hzb : z * b = b * z) (hwa : w * a = a * w) (hwb : w * b = b * w)
    (hzw : z * w = w * z) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hc : Commute a⁻¹ w := Commute.inv_left (show Commute a w from hwa.symm)
  have h2 : w * a⁻¹ * w⁻¹ = a⁻¹ := by
    have h : a⁻¹ * w = w * a⁻¹ := hc.eq
    rw [← h]
    group
  have h1 : a * z * (b * w) = a * b * w * z := by
    calc a * z * (b * w) = a * (z * b) * w := by group
      _ = a * (b * z) * w := by rw [hzb]
      _ = a * b * (z * w) := by group
      _ = a * b * (w * z) := by rw [hzw]
      _ = a * b * w * z := by group
  simp only [commutatorElement_def, mul_inv_rev]
  rw [show a * z * (b * w) * (z⁻¹ * a⁻¹) * (w⁻¹ * b⁻¹) =
      (a * z * (b * w)) * z⁻¹ * (a⁻¹ * (w⁻¹ * b⁻¹)) by group, h1]
  calc a * b * w * z * z⁻¹ * (a⁻¹ * (w⁻¹ * b⁻¹)) = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2]

theorem y10xF_commutator_le_self {Q : Type} [Group Q] (A : Subgroup Q) : ⁅A, A⁆ ≤ A := by
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)

theorem y10xF_derived_qs {Q Θ : Type} [Group Q] [Group Θ] [Finite Q] (f : Q →* Θ)
    {P : Subgroup Q} (hT : CFSG.Open.IsQuasisimple ↥(P.map f))
    (hker : ∀ b ∈ P, f b = 1 → ∀ c ∈ P, c * b = b * c) :
    (⁅P, P⁆ : Subgroup Q).map f = P.map f ∧ CFSG.Open.IsQuasisimple ↥(⁅P, P⁆ : Subgroup Q) := by
  have hmap : (⁅P, P⁆ : Subgroup Q).map f = P.map f := by
    rw [Subgroup.map_commutator, y10xA_qs_comm_self hT]
  have hDP : (⁅P, P⁆ : Subgroup Q) ≤ P := y10xF_commutator_le_self P
  have hperf : ⁅(⁅P, P⁆ : Subgroup Q), ⁅P, P⁆⁆ = ⁅P, P⁆ := by
    apply le_antisymm
    · exact Subgroup.commutator_mono hDP hDP
    · refine Subgroup.commutator_le.2 fun p hp q hq => ?_
      have hfp : f p ∈ (⁅P, P⁆ : Subgroup Q).map f := by
        rw [hmap]
        exact Subgroup.mem_map_of_mem f hp
      have hfq : f q ∈ (⁅P, P⁆ : Subgroup Q).map f := by
        rw [hmap]
        exact Subgroup.mem_map_of_mem f hq
      obtain ⟨d, hd, hdf⟩ := Subgroup.mem_map.1 hfp
      obtain ⟨d', hd', hdf'⟩ := Subgroup.mem_map.1 hfq
      have hdP : d ∈ P := hDP hd
      have hdP' : d' ∈ P := hDP hd'
      obtain ⟨z, hzdef⟩ : ∃ z, z = d⁻¹ * p := ⟨_, rfl⟩
      obtain ⟨w, hwdef⟩ : ∃ w, w = d'⁻¹ * q := ⟨_, rfl⟩
      have hzP : z ∈ P := by rw [hzdef]; exact P.mul_mem (P.inv_mem hdP) hp
      have hwP : w ∈ P := by rw [hwdef]; exact P.mul_mem (P.inv_mem hdP') hq
      have hfz : f z = 1 := by
        rw [hzdef, map_mul, map_inv, hdf, inv_mul_cancel]
      have hfw : f w = 1 := by
        rw [hwdef, map_mul, map_inv, hdf', inv_mul_cancel]
      have hp' : p = d * z := by rw [hzdef]; group
      have hq' : q = d' * w := by rw [hwdef]; group
      have hza : z * d = d * z := (hker z hzP hfz d hdP).symm
      have hzb : z * d' = d' * z := (hker z hzP hfz d' hdP').symm
      have hwa : w * d = d * w := (hker w hwP hfw d hdP).symm
      have hwb : w * d' = d' * w := (hker w hwP hfw d' hdP').symm
      have hzw : z * w = w * z := hker w hwP hfw z hzP
      rw [hp', hq', y10xF_comm_central hza hzb hwa hwb hzw]
      exact Subgroup.commutator_mem_commutator hd hd'
  refine ⟨hmap, ?_⟩
  have hT' : CFSG.Open.IsQuasisimple ↥((⁅P, P⁆ : Subgroup Q).map f) := by
    rw [hmap]
    exact hT
  exact y10xE_qs_of_surj f hperf hT' (fun b hb hfb c hc => hker b (hDP hb) hfb c (hDP hc))

end DiagAbs


section DiagInput

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem y10xF_le_normalizer_of_bot {A B : Subgroup Γ} (h : ⁅A, B⁆ = ⊥) :
    A ≤ Subgroup.normalizer (B : Set Γ) := fun a ha =>
  y10xE_normalizes_of_comm (fun b hb => (y10xE_elem_of_bot h) a ha b hb)

theorem y10xF_components_of_family {p : ℕ} (hp : p.Prime)
    {D : ℕ → Subgroup Γ} (hD_qs : ∀ k, CFSG.Open.IsQuasisimple ↥(D k))
    (hD_per : ∀ k, D (k + p) = D k)
    (hD_comm : ∀ k j, k % p ≠ j % p → ⁅D k, D j⁆ = ⊥) :
    (∀ k, CFSG.Open.IsComponentOf (D k) (⨆ j, D j)) ∧
      (∀ L : Subgroup Γ, CFSG.Open.IsComponentOf L (⨆ j, D j) → ∃ k, L = D k) := by
  have hD_mul : ∀ m j, D (j + p * m) = D j := by
    intro m
    induction m with
    | zero => intro j; simp
    | succ m ih =>
      intro j
      rw [show j + p * (m + 1) = (j + p * m) + p by ring, hD_per, ih]
  have hD_mod : ∀ k, D k = D (k % p) := fun k => by
    have h := hD_mul (k / p) (k % p)
    rw [Nat.mod_add_div] at h
    exact h
  have hDX : ∀ k, D k ≤ ⨆ j, D j := fun k => le_iSup D k
  have hXN : ∀ k, (⨆ j, D j) ≤ Subgroup.normalizer ((D k : Subgroup Γ) : Set Γ) := by
    intro k
    refine iSup_le fun j => ?_
    by_cases hkj : k % p = j % p
    · have hDjk : D j = D k := by rw [hD_mod j, hD_mod k, hkj]
      rw [hDjk]
      exact Subgroup.le_normalizer
    · exact y10xF_le_normalizer_of_bot (hD_comm j k (fun h => hkj h.symm))
  have hsub : ∀ k, CFSG.Open.IsSubnormal (D k) (⨆ j, D j) := fun k =>
    CFSG.Open.IsSubnormal.step (hDX k)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hDX k)).2 (hXN k))
      (CFSG.Open.IsSubnormal.refl _)
  have hcomp : ∀ k, CFSG.Open.IsComponentOf (D k) (⨆ j, D j) := fun k =>
    ⟨hDX k, hsub k, hD_qs k⟩
  refine ⟨hcomp, fun L hL => ?_⟩
  have hLc : CFSG.Open.IsComponentOf L (⨆ j, D j) := hL
  obtain ⟨hLX, hLsub, hLq⟩ := hLc
  have hcls : ∀ k, L ≤ D k ∨ ⁅L, D k⁆ = ⊥ := fun k =>
    y10xA_cn (show CFSG.Open.IsComponentOf L (⨆ j, D j) from ⟨hLX, hLsub, hLq⟩) (hDX k) (hXN k)
  have hex : ∃ k, L ≤ D k := by
    by_contra hcon
    have hcomm : ∀ k, ⁅L, D k⁆ = ⊥ := fun k => (hcls k).resolve_left (fun h => hcon ⟨k, h⟩)
    have hLcomm : ∀ x ∈ (⨆ j, D j), ∀ l ∈ L, x * l = l * x := by
      intro x hx
      refine Subgroup.iSup_induction D (C := fun x => ∀ l ∈ L, x * l = l * x) hx ?_ ?_ ?_
      · intro j y hy l hl
        exact ((y10xE_elem_of_bot (hcomm j)) l hl y hy).symm
      · intro l _
        simp
      · intro a b ha hb l hl
        rw [mul_assoc, hb l hl, ← mul_assoc, ha l hl, mul_assoc]
    have hLL : ⁅L, L⁆ = ⊥ := y10xE_bot_of_elem (fun a ha b hb => hLcomm a (hLX ha) b hb)
    have h1 : L = ⊥ := by
      rw [← y10xA_qs_comm_self hLq]
      exact hLL
    exact y10xA_qs_ne_bot hLq h1
  obtain ⟨k, hLk⟩ := hex
  have h1 := CFSG.Open.IsSubnormal.inf hLsub (D k)
  rw [inf_eq_left.2 hLk, inf_eq_right.2 (hDX k)] at h1
  exact ⟨k, y10xF_eq_of_subnormal (hD_qs k) hLk h1 hLq⟩

theorem y10xF_input25_app (hI25 : Input2_5) {p : ℕ} (hp : p.Prime) {σ : Γ} (hσ : σ ^ p = 1)
    {D : ℕ → Subgroup Γ} (hD_qs : ∀ k, CFSG.Open.IsQuasisimple ↥(D k))
    (hD_per : ∀ k, D (k + p) = D k)
    (hD_comm : ∀ k j, k % p ≠ j % p → ⁅D k, D j⁆ = ⊥)
    (hD_ne : ∀ k j, k % p ≠ j % p → D k ≠ D j)
    (hD_shift : ∀ k, (D k).map (MulAut.conj σ).toMonoidHom = D (k + 1)) :
    ∀ X₁ : Subgroup Γ, CFSG.Open.IsComponentOf X₁ (⨆ k, D k) →
      ∃ (Z : Subgroup ↥X₁) (_ : Z.Normal), Z ≤ Subgroup.center ↥X₁ ∧
        Nonempty (↥(GLALayer ((⨆ k, D k) ⊓ Subgroup.centralizer
          ((Subgroup.zpowers σ : Subgroup Γ) : Set Γ))) ≃* (↥X₁ ⧸ Z)) := by
  obtain ⟨hcomp, hcls⟩ := y10xF_components_of_family hp hD_qs hD_per hD_comm
  have hshift_pow : ∀ n j, (D j).map (MulAut.conj (σ ^ n)).toMonoidHom = D (j + n) := by
    intro n
    induction n with
    | zero =>
      intro j
      have h1 : (MulAut.conj (σ ^ 0)).toMonoidHom = MonoidHom.id Γ := by
        ext y
        simp
      rw [h1, Subgroup.map_id, add_zero]
    | succ n ih =>
      intro j
      have hcompos : (MulAut.conj (σ ^ (n + 1))).toMonoidHom =
          (MulAut.conj (σ ^ n)).toMonoidHom.comp (MulAut.conj σ).toMonoidHom := by
        ext y
        simp [pow_succ, mul_assoc]
      rw [hcompos, ← Subgroup.map_map, hD_shift j, ih (j + 1)]
      congr 1
      ring
  have hconjX : ∀ n, ∀ g ∈ (⨆ k, D k), (σ ^ n) * g * (σ ^ n)⁻¹ ∈ (⨆ k, D k) := by
    intro n g hg
    refine Subgroup.iSup_induction D
      (C := fun g => (σ ^ n) * g * (σ ^ n)⁻¹ ∈ (⨆ k, D k)) hg ?_ ?_ ?_
    · intro j y hy
      have h1 : (σ ^ n) * y * (σ ^ n)⁻¹ ∈ (D j).map (MulAut.conj (σ ^ n)).toMonoidHom :=
        Subgroup.mem_map.2 ⟨y, hy, rfl⟩
      rw [hshift_pow n j] at h1
      exact le_iSup D (j + n) h1
    · simp
    · intro a b ha hb
      have e : σ ^ n * (a * b) * (σ ^ n)⁻¹ =
          (σ ^ n * a * (σ ^ n)⁻¹) * (σ ^ n * b * (σ ^ n)⁻¹) := by group
      rw [e]
      exact (⨆ k, D k).mul_mem ha hb
  have hσN : σ ∈ Subgroup.normalizer ((⨆ k, D k : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      simpa using hconjX 1 h hh
    · intro hh
      have hpm : σ ^ (p - 1) = σ⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hσ]
      have h2 := hconjX (p - 1) _ hh
      rw [hpm] at h2
      have e : σ⁻¹ * (σ * h * σ⁻¹) * (σ⁻¹)⁻¹ = h := by group
      rw [e] at h2
      exact h2
  have hEN : Subgroup.zpowers σ ≤ Subgroup.normalizer ((⨆ k, D k : Subgroup Γ) : Set Γ) :=
    Subgroup.zpowers_le.2 hσN
  have hEA : CFSG.Open.IsElemAbelian p (Subgroup.zpowers σ) := by
    refine ⟨y10xE_isMulComm_of_forall ?_, ?_⟩
    · intro x hx y hy
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((Commute.refl σ).zpow_zpow a b).eq
    · intro x hx
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ, one_zpow]
  have hGL : ∀ n k, GLBConj ((σ ^ n)⁻¹) (D k) = D (k + n) := by
    intro n k
    unfold GLBConj
    rw [inv_inv, hshift_pow]
  have hD_mul : ∀ m j, D (j + p * m) = D j := by
    intro m
    induction m with
    | zero => intro j; simp
    | succ m ih =>
      intro j
      rw [show j + p * (m + 1) = (j + p * m) + p by ring, hD_per, ih]
  have htrans : ∀ L L' : Subgroup Γ, CFSG.Open.IsComponentOf L (⨆ k, D k) →
      CFSG.Open.IsComponentOf L' (⨆ k, D k) → ∃ e ∈ Subgroup.zpowers σ, GLBConj e L = L' := by
    intro L L' hL hL'
    obtain ⟨k, rfl⟩ := hcls L hL
    obtain ⟨j, rfl⟩ := hcls L' hL'
    refine ⟨(σ ^ ((p - 1) * k + j))⁻¹, inv_mem (pow_mem (Subgroup.mem_zpowers σ) _), ?_⟩
    have hn : k + ((p - 1) * k + j) = j + p * k := by
      have hpq : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
      calc k + ((p - 1) * k + j) = (p - 1 + 1) * k + j := by ring
        _ = p * k + j := by rw [hpq]
        _ = j + p * k := by ring
    rw [hGL, hn, hD_mul]
  have hsemi : ∀ e ∈ Subgroup.zpowers σ, e ≠ 1 → ∀ L : Subgroup Γ,
      CFSG.Open.IsComponentOf L (⨆ k, D k) → GLBConj e L ≠ L := by
    intro e he hne1 L hL
    obtain ⟨k, rfl⟩ := hcls L hL
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff e σ).1 (mem_powers_iff_mem_zpowers.2 he)
    have hprod : σ ^ ((p - 1) * m) * e = 1 := by
      rw [← hm, ← pow_add]
      have hsum : (p - 1) * m + m = p * m := by
        have hpq : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
        calc (p - 1) * m + m = (p - 1 + 1) * m := by ring
          _ = p * m := by rw [hpq]
      rw [hsum, pow_mul, hσ, one_pow]
    have he' : e = (σ ^ ((p - 1) * m))⁻¹ := eq_inv_of_mul_eq_one_right hprod
    have hnp : ¬ p ∣ (p - 1) * m := by
      intro hdvd
      obtain ⟨c, hc⟩ := hdvd
      apply hne1
      have h1 : σ ^ ((p - 1) * m) = 1 := by rw [hc, pow_mul, hσ, one_pow]
      rw [h1, one_mul] at hprod
      exact hprod
    rw [he', hGL]
    apply hD_ne (k + (p - 1) * m) k
    intro hmod
    apply hnp
    have h2 : k + (p - 1) * m ≡ k + 0 [MOD p] := by
      rw [add_zero]
      exact hmod
    exact Nat.modEq_zero_iff_dvd.1 (Nat.ModEq.add_left_cancel' k h2)
  have hlay : GLALayer (⨆ k, D k) = ⨆ k, D k := by
    apply le_antisymm
    · exact sSup_le fun K hK => hK.1
    · exact iSup_le fun k => le_sSup (show D k ∈
        {K : Subgroup Γ | CFSG.Open.IsComponentOf K (⨆ j, D j)} from hcomp k)
  intro X₁ hX₁
  exact (hI25 Γ p hp (⨆ k, D k) (Subgroup.zpowers σ) hlay hEN hEA htrans hsemi).1 X₁ hX₁

end DiagInput


section DiagFam

variable {G : Type} [Group G] [Finite G]

theorem y10xF_gconj_comp {C K Y : Subgroup G} {g : G} (hg : g ∈ C) (hYc : GLAPComponent 3 C Y)
    (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G)) :
    GLAPComponent 3 C (GLBConj g Y) ∧ GLBConj g Y ≤ K ⊔ GLAPPrimeCoreOf 3 C := by
  have hCfix : GLBConj g C = C := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg)
  refine ⟨?_, ?_⟩
  · have h1 := glaPComponent_gLBConj hYc g
    rwa [hCfix] at h1
  · have h2 : GLBConj g (K ⊔ GLAPPrimeCoreOf 3 C) = K ⊔ GLAPPrimeCoreOf 3 C :=
      y10xE_gLBConj_KO hKC hCK hO hg
    exact (Subgroup.map_mono hYK : GLBConj g Y ≤ GLBConj g (K ⊔ GLAPPrimeCoreOf 3 C)).trans h2.le

@[expose] def y10xF_mem {C K Y : Subgroup G} {g : G} (hg : g ∈ C) (hYc : GLAPComponent 3 C Y)
    (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G)) :
    y10xA_I 3 C K :=
  ⟨GLBConj g Y, y10xF_gconj_comp hg hYc hYK hKC hCK hO⟩

@[expose] def y10xF_P {C K Y : Subgroup G} (N : Subgroup G) [(N.subgroupOf C).Normal]
    {x : G} (hxC : x ∈ C)
    (hYc : GLAPComponent 3 C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G)) (k : ℕ) :
    Subgroup (↥C ⧸ N.subgroupOf C) :=
  y10xA_fam 3 C K N (some (y10xF_mem (C.pow_mem hxC k) hYc hYK hKC hCK hO))

theorem y10xF_P_map {C K N Y : Subgroup G} [(N.subgroupOf C).Normal] {x : G} (hxC : x ∈ C)
    (hYc : GLAPComponent 3 C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hNO : N ≤ GLAPPrimeCoreOf 3 C) (k : ℕ) :
    (y10xF_P N hxC hYc hYK hKC hCK hO k).map (y10xE_rho hNO) =
      barX 3 C (GLBConj (x ^ k) Y) := by
  have hg := C.pow_mem hxC k
  obtain ⟨hcomp, hle⟩ := y10xF_gconj_comp hg hYc hYK hKC hCK hO
  show (y10xA_img C N (K ⊓ (GLBConj (x ^ k) Y ⊔ GLAPPrimeCoreOf 3 C))).map (y10xE_rho hNO) = _
  rw [y10xE_rho_img hNO (inf_le_left.trans hKC)]
  exact y10xE_barX_P hKC hO hle hcomp.1

theorem y10xF_ker_img {C K N : Subgroup G} [(N.subgroupOf C).Normal] (hKC : K ≤ C)
    (hNO : N ≤ GLAPPrimeCoreOf 3 C) (hKO : K ⊓ GLAPPrimeCoreOf 3 C ≤ GLAPPrimeCoreOf 3 K)
    {H : Subgroup G} (hHK : H ≤ K) :
    ∀ b ∈ y10xA_img C N H, y10xE_rho hNO b = 1 → b ∈ y10xA_img C N (GLAPPrimeCoreOf 3 K) := by
  intro b hb hb1
  obtain ⟨c, hcH, rfl⟩ := y10xA_exists_of_mem_img hb
  rw [y10xE_rho_mk'] at hb1
  have hcO : (c : G) ∈ GLAPPrimeCoreOf 3 C :=
    y10xA_of_mem_core c.2 ((QuotientGroup.eq_one_iff _).1 hb1)
  exact y10xA_mem_img c.2 (hKO ⟨hHK hcH, hcO⟩)

theorem y10xF_P_central {C K N Y : Subgroup G} [(N.subgroupOf C).Normal] {x : G} (hxC : x ∈ C)
    (hYc : GLAPComponent 3 C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hNO : N ≤ GLAPPrimeCoreOf 3 C)
    (hKO : K ⊓ GLAPPrimeCoreOf 3 C ≤ GLAPPrimeCoreOf 3 K)
    (hOK_le : GLAPPrimeCoreOf 3 K ≤ K)
    (hcommN : ∀ k ∈ K, ∀ t ∈ GLAPPrimeCoreOf 3 K, ⁅k, t⁆ ∈ N) (k : ℕ) :
    ∀ b ∈ y10xF_P N hxC hYc hYK hKC hCK hO k, y10xE_rho hNO b = 1 →
      ∀ c ∈ y10xF_P N hxC hYc hYK hKC hCK hO k, c * b = b * c := by
  intro b hb hb1 c hc
  have hbOK : b ∈ y10xA_img C N (GLAPPrimeCoreOf 3 K) :=
    y10xF_ker_img hKC hNO hKO inf_le_left b hb hb1
  have hcK : c ∈ y10xA_img C N K := y10xE_fam_le_img _ hc
  exact y10xA_img_central hKC hOK_le hcommN b hbOK c hcK

theorem y10xF_D_qs {C K N Y : Subgroup G} [(N.subgroupOf C).Normal] {x : G} (hxC : x ∈ C)
    (hYc : GLAPComponent 3 C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hNO : N ≤ GLAPPrimeCoreOf 3 C)
    (hKO : K ⊓ GLAPPrimeCoreOf 3 C ≤ GLAPPrimeCoreOf 3 K)
    (hOK_le : GLAPPrimeCoreOf 3 K ≤ K)
    (hcommN : ∀ k ∈ K, ∀ t ∈ GLAPPrimeCoreOf 3 K, ⁅k, t⁆ ∈ N) (k : ℕ) :
    (⁅y10xF_P N hxC hYc hYK hKC hCK hO k, y10xF_P N hxC hYc hYK hKC hCK hO k⁆ :
        Subgroup (↥C ⧸ N.subgroupOf C)).map (y10xE_rho hNO) = barX 3 C (GLBConj (x ^ k) Y) ∧
      CFSG.Open.IsQuasisimple ↥(⁅y10xF_P N hxC hYc hYK hKC hCK hO k,
        y10xF_P N hxC hYc hYK hKC hCK hO k⁆ : Subgroup (↥C ⧸ N.subgroupOf C)) := by
  have hq : CFSG.Open.IsQuasisimple ↥(barX 3 C (GLBConj (x ^ k) Y)) :=
    (y10xA_barX_isComponent (y10xF_gconj_comp (C.pow_mem hxC k) hYc hYK hKC hCK hO).1).2.2
  have hT : CFSG.Open.IsQuasisimple
      ↥((y10xF_P N hxC hYc hYK hKC hCK hO k).map (y10xE_rho hNO)) := by
    rw [y10xF_P_map hxC hYc hYK hKC hCK hO hNO k]
    exact hq
  obtain ⟨h1, h2⟩ := y10xF_derived_qs (y10xE_rho hNO) hT
    (y10xF_P_central hxC hYc hYK hKC hCK hO hNO hKO hOK_le hcommN k)
  exact ⟨by rw [h1, y10xF_P_map hxC hYc hYK hKC hCK hO hNO k], h2⟩

theorem y10xF_P_le_D {C K N Y : Subgroup G} [(N.subgroupOf C).Normal] {x : G} (hxC : x ∈ C)
    (hYc : GLAPComponent 3 C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hNO : N ≤ GLAPPrimeCoreOf 3 C)
    (hKO : K ⊓ GLAPPrimeCoreOf 3 C ≤ GLAPPrimeCoreOf 3 K)
    (hOK_le : GLAPPrimeCoreOf 3 K ≤ K)
    (hcommN : ∀ k ∈ K, ∀ t ∈ GLAPPrimeCoreOf 3 K, ⁅k, t⁆ ∈ N) (k : ℕ) :
    y10xF_P N hxC hYc hYK hKC hCK hO k ≤
      ⁅y10xF_P N hxC hYc hYK hKC hCK hO k, y10xF_P N hxC hYc hYK hKC hCK hO k⁆ ⊔
        y10xA_img C N (GLAPPrimeCoreOf 3 K) := by
  intro p hp
  have hD := y10xF_D_qs hxC hYc hYK hKC hCK hO hNO hKO hOK_le hcommN k
  have hfp : y10xE_rho hNO p ∈
      (⁅y10xF_P N hxC hYc hYK hKC hCK hO k, y10xF_P N hxC hYc hYK hKC hCK hO k⁆ :
        Subgroup (↥C ⧸ N.subgroupOf C)).map (y10xE_rho hNO) := by
    rw [hD.1, ← y10xF_P_map hxC hYc hYK hKC hCK hO hNO k]
    exact Subgroup.mem_map_of_mem _ hp
  obtain ⟨d, hd, hdp⟩ := Subgroup.mem_map.1 hfp
  have hdP : d ∈ y10xF_P N hxC hYc hYK hKC hCK hO k := y10xF_commutator_le_self _ hd
  have hz : d⁻¹ * p ∈ y10xF_P N hxC hYc hYK hKC hCK hO k :=
    (y10xF_P N hxC hYc hYK hKC hCK hO k).mul_mem ((y10xF_P N hxC hYc hYK hKC hCK hO k).inv_mem hdP) hp
  have hzρ : y10xE_rho hNO (d⁻¹ * p) = 1 := by
    rw [map_mul, map_inv, hdp, inv_mul_cancel]
  have hzimg : d⁻¹ * p ∈ y10xA_img C N (GLAPPrimeCoreOf 3 K) :=
    y10xF_ker_img hKC hNO hKO inf_le_left (d⁻¹ * p) hz hzρ
  have e : p = d * (d⁻¹ * p) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right hzimg)

end DiagFam


section Count3

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem y10xF_normalizer_map {H Δ : Type} [Group H] [Group Δ] (f : H →* Δ)
    (hf : Function.Injective f) {S A : Subgroup H} (hAN : A ≤ Subgroup.normalizer (S : Set H)) :
    A.map f ≤ Subgroup.normalizer ((S.map f : Subgroup Δ) : Set Δ) := by
  rintro _ ⟨a, ha, rfl⟩
  have hN := Subgroup.mem_normalizer_iff.1 (hAN ha)
  have hNi : a⁻¹ ∈ Subgroup.normalizer (S : Set H) := inv_mem (hAN ha)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hh
    rw [show f a * f s * (f a)⁻¹ = f (a * s * a⁻¹) by rw [map_mul, map_mul, map_inv]]
    exact Subgroup.mem_map_of_mem f ((hN s).1 hs)
  · intro hh
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 hh
    have hs : a⁻¹ * u * a ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 hNi u).1 hu
      simpa using this
    refine Subgroup.mem_map.2 ⟨a⁻¹ * u * a, hs, ?_⟩
    rw [map_mul, map_mul, map_inv, hue]
    group

theorem y10xF_elemAb_map {H Δ : Type} [Group H] [Group Δ] [Finite H] [Finite Δ] (f : H →* Δ)
    (hf : Function.Injective f) {p : ℕ} {E : Subgroup H} (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  refine ⟨y10xE_isMulComm_of_forall ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, y10xE_comm_of_elemAb hE ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

theorem y10xF_count_bound {X₀ X₁ : Subgroup Γ} (hX₀ : CFSG.Open.IsQuasisimple ↥X₀)
    (hcomm : ⁅X₀, X₁⁆ = ⊥)
    (hS0 : ∃ S0 : Subgroup ↥X₀, S0 ≠ ⊥ ∧ IsPGroup 2 S0)
    (hE1 : ∃ E1 : Subgroup Γ, E1 ≤ X₁ ∧ CFSG.Open.IsElemAbelian 3 E1 ∧
      Nat.card E1 = 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup ↥X₀)) :
    ∃ k : ℕ, GLATwoLocalRank 3 ↥X₀ + CFSG.Open.pRank 3 (⊤ : Subgroup ↥X₀) ≤
        k + CFSG.Open.pRank 3 (Subgroup.center ↥X₀) ∧ k ≤ GLATwoLocalRank 3 Γ := by
  obtain ⟨S0, hS0ne, hS0p⟩ := hS0
  obtain ⟨S, hSne, hSp, A, hAN, hAe, hAc⟩ := y10xE_attain S0 hS0ne hS0p
  obtain ⟨E1, hE1X, hE1e, hE1c⟩ := hE1
  have hinj : Function.Injective (X₀.subtype : ↥X₀ →* Γ) := Subtype.val_injective
  have hS'ne : S.map (X₀.subtype) ≠ ⊥ := by
    obtain ⟨s, hs⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hSne
    intro hbot
    have hmem : ((s : ↥X₀) : Γ) ∈ S.map (X₀.subtype) := Subgroup.mem_map_of_mem _ s.2
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hs
    apply Subtype.ext
    apply Subtype.ext
    exact hmem
  have hS'p : IsPGroup 2 (S.map (X₀.subtype)) := IsPGroup.map hSp X₀.subtype
  have hS'X : S.map (X₀.subtype) ≤ X₀ := by
    rintro _ ⟨s, _, rfl⟩
    exact s.2
  have hA'X : A.map (X₀.subtype) ≤ X₀ := by
    rintro _ ⟨s, _, rfl⟩
    exact s.2
  have hA'N := y10xF_normalizer_map X₀.subtype hinj hAN
  have hA'e := y10xF_elemAb_map X₀.subtype hinj hAe
  have hA'c : Nat.card (A.map (X₀.subtype)) = 3 ^ GLATwoLocalRank 3 ↥X₀ := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hAc
  have hZ : ∀ T : Subgroup Γ, T ≤ X₀ → (∀ t ∈ T, ∀ y ∈ X₀, t * y = y * t) →
      CFSG.Open.IsElemAbelian 3 T →
        Nat.card T ≤ 3 ^ CFSG.Open.pRank 3 (Subgroup.center ↥X₀) := by
    intro T hTX hTc hTe
    have hT'c : T.subgroupOf X₀ ≤ Subgroup.center ↥X₀ := by
      intro t ht
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (hTc (t : Γ) (Subgroup.mem_subgroupOf.1 ht) (g : Γ) g.2).symm
    have hT'e : CFSG.Open.IsElemAbelian 3 (T.subgroupOf X₀) := by
      refine ⟨y10xE_isMulComm_of_forall ?_, ?_⟩
      · intro x hx y hy
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact y10xE_comm_of_elemAb hTe (Subgroup.mem_subgroupOf.1 hx)
          (Subgroup.mem_subgroupOf.1 hy)
      · intro x hx
        apply Subtype.ext
        simp only [Subgroup.coe_pow, OneMemClass.coe_one]
        exact hTe.2 _ (Subgroup.mem_subgroupOf.1 hx)
    have hcard : Nat.card (T.subgroupOf X₀) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (isPGroup_of_isElemAbelian hT'e)
    have hle := y10xE_le_pRank Nat.prime_three hT'c hT'e hn
    rw [← hcard, hn]
    exact Nat.pow_le_pow_right (by norm_num) hle
  obtain ⟨F, hFN, hFe, k, hFk, hak⟩ :=
    y10xE_count (Y0 := X₀) (Y1 := X₁) (S := S.map (X₀.subtype)) (A := A.map (X₀.subtype))
      (E1 := E1) (a := GLATwoLocalRank 3 ↥X₀) (e := CFSG.Open.pRank 3 (⊤ : Subgroup ↥X₀))
      (z := CFSG.Open.pRank 3 (Subgroup.center ↥X₀))
      (fun x hx y hy => y10xE_elem_of_bot hcomm x hx y hy) hS'X hA'X hA'N hA'e hA'c hE1X hE1e
      hE1c hZ
  exact ⟨k, hak, y10xE_le_twoLocal_of_elemAb Nat.prime_three hS'ne hS'p hFN hFe hFk⟩

end Count3

section Arith

theorem y10xF_dvd_of_eq {c z0 Jc k0 a0 J1 : ℕ} (ha0 : 0 < a0) (h1 : c * a0 = z0 * J1)
    (h2 : Jc * a0 = k0 * J1) (h3 : 3 ∣ Jc) (h4 : ¬ 3 ∣ k0) : 3 ∣ c := by
  have key : c * k0 = z0 * Jc := by
    apply Nat.eq_of_mul_eq_mul_left ha0
    calc a0 * (c * k0) = (c * a0) * k0 := by ring
      _ = z0 * J1 * k0 := by rw [h1]
      _ = z0 * (k0 * J1) := by ring
      _ = z0 * (Jc * a0) := by rw [h2]
      _ = a0 * (z0 * Jc) := by ring
  have h5 : 3 ∣ c * k0 := by
    rw [key]
    exact Dvd.dvd.mul_left h3 z0
  exact ((Nat.Prime.dvd_mul Nat.prime_three).1 h5).resolve_right h4

end Arith

section Perfect

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem y10xF_sub_of_sup {X Z0 T : Subgroup Γ} (hZX : ∀ v ∈ Z0, ∀ w ∈ X, v * w = w * v)
    (hZT : ∀ v ∈ Z0, ∀ t ∈ T, v * t = t * v) (hT : T ≤ X ⊔ Z0) (hperf : ⁅T, T⁆ = T) :
    T ≤ X := by
  have hWV : y10xA_Commute X Z0 := by
    apply y10xA_commute_of_bot
    apply y10xE_bot_of_elem
    intro a ha b hb
    exact (hZX b hb a ha).symm
  refine y10xA_le_of_perfect (W := X) (V := Z0) (T := T) ?_ hZT hWV hT hperf
  intro t ht w hw
  obtain ⟨a, ha, v, hv, rfl⟩ := y10xA_mem_sup_of_commute hWV (hT ht)
  have e : a * v * w * (a * v)⁻¹ = a * w * a⁻¹ := by
    have hvw := hZX v hv w hw
    calc a * v * w * (a * v)⁻¹ = a * (v * w) * v⁻¹ * a⁻¹ := by group
      _ = a * (w * v) * v⁻¹ * a⁻¹ := by rw [hvw]
      _ = a * w * a⁻¹ := by group
  rw [e]
  exact X.mul_mem (X.mul_mem ha hw) (X.inv_mem ha)

theorem y10xF_layer_eq {X E Jh : Subgroup Γ}
    (hJh : CFSG.Open.IsComponentOf Jh (X ⊓ E))
    (hLq : CFSG.Open.IsQuasisimple ↥(GLALayer (X ⊓ E))) : Jh = GLALayer (X ⊓ E) := by
  have hJL : Jh ≤ GLALayer (X ⊓ E) := le_sSup (s := {K : Subgroup Γ |
      CFSG.Open.IsComponentOf K (X ⊓ E)}) hJh
  have hLle : GLALayer (X ⊓ E) ≤ X ⊓ E := sSup_le fun K hK => hK.1
  have h1 := CFSG.Open.IsSubnormal.inf hJh.2.1 (GLALayer (X ⊓ E))
  rw [inf_eq_left.2 hJL, inf_eq_right.2 hLle] at h1
  exact y10xF_eq_of_subnormal hLq hJL h1 hJh.2.2

theorem y10xF_layer_qs {X₁ L' Jh : Subgroup Γ} (hX₁ : CFSG.Open.IsQuasisimple ↥X₁)
    {Z : Subgroup ↥X₁} [Z.Normal] (hZ : Z ≤ Subgroup.center ↥X₁)
    (e : ↥L' ≃* (↥X₁ ⧸ Z)) (hJL : Jh ≤ L') (hJq : CFSG.Open.IsQuasisimple ↥Jh) :
    CFSG.Open.IsQuasisimple ↥L' := by
  have hZne : Z ≠ ⊤ := by
    intro hZtop
    subst hZtop
    haveI : Subsingleton (↥X₁ ⧸ (⊤ : Subgroup ↥X₁)) := QuotientGroup.subsingleton_quotient_top
    haveI : Subsingleton ↥L' := Equiv.subsingleton e.toEquiv
    apply y10xA_qs_ne_bot hJq
    rw [eq_bot_iff]
    intro y hy
    have h1 : (⟨y, hJL hy⟩ : ↥L') = 1 := Subsingleton.elim _ _
    have h2 : y = 1 := congrArg Subtype.val h1
    exact (Subgroup.mem_bot).2 h2
  exact y10xF_qs_of_mulEquiv e.symm (y10xE_qs_quot hX₁ hZ hZne)

theorem y10xF_quot_center_equiv_of_surj {J A : Type} [Group J] [Group A] [Finite J] [Finite A]
    (φ : J →* A)
    (hφ : Function.Surjective φ) (hJ : commutator J = ⊤)
    (hker : ∀ j, φ j = 1 → j ∈ Subgroup.center J) :
    Nonempty (J ⧸ Subgroup.center J ≃* A ⧸ Subgroup.center A) := by
  let ψ : J →* A ⧸ Subgroup.center A := (QuotientGroup.mk' (Subgroup.center A)).comp φ
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨j, rfl⟩ := hφ a
    exact ⟨j, rfl⟩
  have hkerψ : ψ.ker = Subgroup.center J := by
    ext j
    constructor
    · intro hj
      have hj1 : φ j ∈ Subgroup.center A := by
        have := (MonoidHom.mem_ker).1 hj
        exact (QuotientGroup.eq_one_iff _).1 this
      refine y10xE_central_of_quot hJ (Z := φ.ker) (fun j' hj' => hker j' hj') ?_
      intro g
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hc : ∀ b : A, φ j * b = b * φ j := fun b => ((Subgroup.mem_center_iff.1 hj1) b).symm
      have hcg := hc (φ g)
      calc (φ j)⁻¹ * (φ g)⁻¹ * φ j * φ g = (φ j)⁻¹ * ((φ g)⁻¹ * (φ j * φ g)) := by group
        _ = (φ j)⁻¹ * ((φ g)⁻¹ * (φ g * φ j)) := by rw [hcg]
        _ = 1 := by group
    · intro hj
      rw [MonoidHom.mem_ker]
      apply (QuotientGroup.eq_one_iff _).2
      have hjc : ∀ g : J, g * j = j * g := fun g => (Subgroup.mem_center_iff.1 hj) g
      apply Subgroup.mem_center_iff.2
      intro b
      obtain ⟨g, rfl⟩ := hφ b
      have := congrArg φ (hjc g)
      simpa [map_mul] using this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem y10xF_two_local_exists {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    (h : 0 < CFSG.Open.twoLocalPrimeRank p Q) : ∃ H : Subgroup Q, CFSG.Open.IsTwoLocal H := by
  by_contra hno
  push_neg at hno
  have hset : {k | ∃ H : Subgroup Q, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank p H = k} = ∅ := by
    ext k
    constructor
    · rintro ⟨H, hH, -⟩
      exact absurd hH (hno H)
    · intro hk
      simp at hk
  unfold CFSG.Open.twoLocalPrimeRank at h
  rw [hset] at h
  simp at h

end Perfect


section DiagFam2

variable {G : Type} [Group G] [Finite G]

theorem y10xF_pow_mod {x : G} {p : ℕ} (hx : x ^ p = 1) (k : ℕ) : x ^ k = x ^ (k % p) := by
  conv_lhs => rw [← Nat.mod_add_div k p, pow_add, pow_mul, hx, one_pow, mul_one]

theorem y10xF_P_shift {C K N Y : Subgroup G} [(N.subgroupOf C).Normal] {x : G} (hxC : x ∈ C)
    (hYc : GLAPComponent 3 C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hNO : N ≤ GLAPPrimeCoreOf 3 C)
    (hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) (k : ℕ) :
    (y10xF_P N hxC hYc hYK hKC hCK hO k).map
        (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C))).toMonoidHom =
      y10xF_P N hxC hYc hYK hKC hCK hO (k + 1) := by
  have h := y10xE_fam_conj_some (N := N) hKC hCK hO hKn (C.inv_mem hxC)
    (y10xF_mem (C.pow_mem hxC k) hYc hYK hKC hCK hO)
  refine h.trans (congrArg (fun a : y10xA_I 3 C K => y10xA_fam 3 C K N (some a)) (Subtype.ext ?_))
  show GLBConj (x⁻¹)⁻¹ (GLBConj (x ^ k) Y) = GLBConj (x ^ (k + 1)) Y
  rw [inv_inv, gLBConj_gLBConj, pow_succ]

theorem y10xF_P_per {C K N Y : Subgroup G} [(N.subgroupOf C).Normal] {x : G} (hxC : x ∈ C)
    (hYc : GLAPComponent 3 C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hNO : N ≤ GLAPPrimeCoreOf 3 C) {p : ℕ} (hx : x ^ p = 1) (k : ℕ) :
    y10xF_P N hxC hYc hYK hKC hCK hO (k + p) = y10xF_P N hxC hYc hYK hKC hCK hO k := by
  exact congrArg (fun a : y10xA_I 3 C K => y10xA_fam 3 C K N (some a))
    (Subtype.ext (by
      show GLBConj (x ^ (k + p)) Y = GLBConj (x ^ k) Y
      rw [pow_add, hx, mul_one]))

theorem y10xF_D_comm {C K N Y : Subgroup G} [(N.subgroupOf C).Normal] {x : G} (hxC : x ∈ C)
    (hYc : GLAPComponent 3 C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hNO : N ≤ GLAPPrimeCoreOf 3 C)
    (hcommN : ∀ k ∈ K, ∀ t ∈ GLAPPrimeCoreOf 3 K, ⁅k, t⁆ ∈ N)
    {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    (hdist : ∀ i j : ℕ, i < p → j < p → i ≠ j → GLBConj (x ^ i) Y ≠ GLBConj (x ^ j) Y)
    (k j : ℕ) (hkj : k % p ≠ j % p) :
    ⁅⁅y10xF_P N hxC hYc hYK hKC hCK hO k, y10xF_P N hxC hYc hYK hKC hCK hO k⁆,
      ⁅y10xF_P N hxC hYc hYK hKC hCK hO j, y10xF_P N hxC hYc hYK hKC hCK hO j⁆⁆ = ⊥ := by
  have hne : GLBConj (x ^ k) Y ≠ GLBConj (x ^ j) Y := by
    rw [y10xF_pow_mod hx k, y10xF_pow_mod hx j]
    exact hdist (k % p) (j % p) (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) hkj
  have hfam : ⁅y10xF_P N hxC hYc hYK hKC hCK hO k, y10xF_P N hxC hYc hYK hKC hCK hO j⁆ = ⊥ := by
    refine y10xE_fam_comm (N := N) hKC hO hcommN ?_
    intro h
    apply hne
    exact congrArg Subtype.val (Option.some.inj h)
  have h1 := Subgroup.commutator_mono (y10xF_commutator_le_self (y10xF_P N hxC hYc hYK hKC hCK hO k))
    (y10xF_commutator_le_self (y10xF_P N hxC hYc hYK hKC hCK hO j))
  rw [hfam] at h1
  exact le_bot_iff.1 h1

end DiagFam2


section DiagFam3

variable {G : Type} [Group G] [Finite G]

@[expose] def y10xF_sigma {C N : Subgroup G} [(N.subgroupOf C).Normal] (x : G) (hxC : x ∈ C) :
    ↥C ⧸ N.subgroupOf C :=
  QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C)

theorem y10xF_D_ne {C K N Y : Subgroup G} [(N.subgroupOf C).Normal] {x : G} (hxC : x ∈ C)
    (hYc : GLAPComponent 3 C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hNO : N ≤ GLAPPrimeCoreOf 3 C)
    (hKO : K ⊓ GLAPPrimeCoreOf 3 C ≤ GLAPPrimeCoreOf 3 K)
    (hOK_le : GLAPPrimeCoreOf 3 K ≤ K)
    (hcommN : ∀ k ∈ K, ∀ t ∈ GLAPPrimeCoreOf 3 K, ⁅k, t⁆ ∈ N)
    {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    (hdist : ∀ i j : ℕ, i < p → j < p → i ≠ j → GLBConj (x ^ i) Y ≠ GLBConj (x ^ j) Y)
    (k j : ℕ) (hkj : k % p ≠ j % p) :
    ⁅y10xF_P N hxC hYc hYK hKC hCK hO k, y10xF_P N hxC hYc hYK hKC hCK hO k⁆ ≠
      ⁅y10xF_P N hxC hYc hYK hKC hCK hO j, y10xF_P N hxC hYc hYK hKC hCK hO j⁆ := by
  intro heq
  have hne : GLBConj (x ^ k) Y ≠ GLBConj (x ^ j) Y := by
    rw [y10xF_pow_mod hx k, y10xF_pow_mod hx j]
    exact hdist (k % p) (j % p) (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) hkj
  have hmap := congrArg (Subgroup.map (y10xE_rho hNO)) heq
  rw [(y10xF_D_qs hxC hYc hYK hKC hCK hO hNO hKO hOK_le hcommN k).1,
    (y10xF_D_qs hxC hYc hYK hKC hCK hO hNO hKO hOK_le hcommN j).1] at hmap
  exact hne (glaPComponent_unique (y10xF_gconj_comp (C.pow_mem hxC k) hYc hYK hKC hCK hO).1
    (y10xF_gconj_comp (C.pow_mem hxC j) hYc hYK hKC hCK hO).1 hmap)

theorem y10xF_D_shift {C K N Y : Subgroup G} [(N.subgroupOf C).Normal] {x : G} (hxC : x ∈ C)
    (hYc : GLAPComponent 3 C Y) (hYK : Y ≤ K ⊔ GLAPPrimeCoreOf 3 C) (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G))
    (hNO : N ≤ GLAPPrimeCoreOf 3 C)
    (hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) (k : ℕ) :
    (⁅y10xF_P N hxC hYc hYK hKC hCK hO k, y10xF_P N hxC hYc hYK hKC hCK hO k⁆ :
        Subgroup (↥C ⧸ N.subgroupOf C)).map
        (MulAut.conj (QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C))).toMonoidHom =
      ⁅y10xF_P N hxC hYc hYK hKC hCK hO (k + 1), y10xF_P N hxC hYc hYK hKC hCK hO (k + 1)⁆ := by
  rw [Subgroup.map_commutator, y10xF_P_shift hxC hYc hYK hKC hCK hO hNO hKn k]

theorem y10xF_KO_normalizer {C K O : Subgroup G} (hKC : K ≤ C)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hO : C ≤ Subgroup.normalizer (O : Set G)) :
    K ≤ Subgroup.normalizer ((K ⊓ O : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hkC : k ∈ C := hKC hk
  have hkinv : k⁻¹ ∈ C := C.inv_mem hkC
  constructor
  · intro hh
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hCK hkC) h).1 hh.1,
      (Subgroup.mem_normalizer_iff.1 (hO hkC) h).1 hh.2⟩
  · intro hh
    have e : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
    have h1 := (Subgroup.mem_normalizer_iff.1 (hCK hkinv) (k * h * k⁻¹)).1 hh.1
    have h2 := (Subgroup.mem_normalizer_iff.1 (hO hkinv) (k * h * k⁻¹)).1 hh.2
    rw [e] at h1 h2
    exact ⟨h1, h2⟩

theorem y10xF_Jcomp {p : ℕ} (hp : p.Prime) {C J N : Subgroup G} {x : G} (hxC : x ∈ C)
    (hx : x ^ p = 1) (hJC : J ≤ C) (hJlay : J ≤ GLAPLayer 3 C) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJc : CFSG.Open.IsComponentOf J (C ⊓ Subgroup.centralizer ({x} : Set G)))
    (h3J : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hN : N = ⁅closureIn J C, GLAPPrimeCoreOf 3 (closureIn J C)⁆)
    (hNp : ⁅closureIn J C, GLAPPrimeCoreOf 3 (closureIn J C)⁆ ≤ GLAPPrimeCoreOf p (closureIn J C))
    [hNn : (N.subgroupOf C).Normal]
    {Y : Subgroup G} (hY : GLAPComponent 3 C Y)
    (hdiag : J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y) :
    CFSG.Open.IsComponentOf (y10xA_img C N J)
      (y10xA_img C N (closureIn J C) ⊓
        Subgroup.centralizer ({y10xF_sigma (N := N) x hxC} : Set (↥C ⧸ N.subgroupOf C))) := by
  subst hN
  unfold y10xF_sigma
  classical
  set K : Subgroup G := closureIn J C with hKdef
  set O : Subgroup G := GLAPPrimeCoreOf 3 C with hOdef
  set OK : Subgroup G := GLAPPrimeCoreOf 3 K with hOKdef
  set N : Subgroup G := ⁅K, OK⁆ with hNdef
  have hKC : K ≤ C := y10xA_closureIn_le hJC
  have hCK : C ≤ Subgroup.normalizer (K : Set G) := y10xA_closureIn_normalizer
  have hJK : J ≤ K := y10xA_le_closureIn C.one_mem
  have hCn : C ≤ Subgroup.normalizer (C : Set G) := fun c hc => Subgroup.le_normalizer hc
  have hO : C ≤ Subgroup.normalizer (O : Set G) :=
    fun c hc => normalizer_le_normalizer_glaPPrimeCoreOf 3 C (hCn hc)
  have hKn : (K.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).2 hCK
  have hKn' : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun c hc k hk =>
    (Subgroup.mem_normalizer_iff.1 (hCK hc) k).1 hk
  have hOKK : K ≤ Subgroup.normalizer (OK : Set G) :=
    fun k hk => normalizer_le_normalizer_glaPPrimeCoreOf 3 K (Subgroup.le_normalizer hk)
  have hOKC : C ≤ Subgroup.normalizer (OK : Set G) :=
    fun c hc => normalizer_le_normalizer_glaPPrimeCoreOf 3 K (hCK hc)
  have hOK_le : OK ≤ K := y10xA_coreOf_le K
  have hNK : N ≤ K := Subgroup.commutator_le.2 fun a ha b hb => y10xA_comm_mem_gen ha (hOK_le hb)
  have hNOK : N ≤ OK := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    have h1 : a * b * a⁻¹ ∈ OK := (Subgroup.mem_normalizer_iff.1 (hOKK ha) b).1 hb
    exact OK.mul_mem h1 (OK.inv_mem hb)
  have hNC : N ≤ C := hNK.trans hKC
  have hN3 : ¬ 3 ∣ Nat.card N := fun h =>
    not_dvd_card_glaPPrimeCoreOf Nat.prime_three K (h.trans (Subgroup.card_dvd_of_le hNOK))
  have hNp' : ¬ p ∣ Nat.card N := fun h =>
    not_dvd_card_glaPPrimeCoreOf hp K (h.trans (Subgroup.card_dvd_of_le hNp))
  have hNO : N ≤ O :=
    le_glaPPrimeCoreOf_of_le_normalizer hNC (y10xA_comm_core_normalizer (s := 3) hCK)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3)
  have hcomm' : ∀ k ∈ K, ∀ t ∈ OK, ⁅k, t⁆ ∈ N := fun k hk t ht => Subgroup.commutator_mem_commutator hk ht
  have hJX := y10xA_J_le_sup (s := 3) Nat.prime_three hKC hJK hJC hJlay hKn hJq
  have hKX : K ≤ (⨆ Y' : y10xA_I 3 C K, Y'.1) ⊔ O :=
    y10xA_closureIn_le_of hJX (y10xA_sup_normalized (s := 3) hKC hCn hKn' hO)
  have hKP : K ≤ (⨆ Y' : y10xA_I 3 C K, K ⊓ (Y'.1 ⊔ O)) ⊔ OK :=
    y10xA_K_le_sup_P Nat.prime_three hKC hO hKX
  have hcov : y10xA_img C N K ≤ ⨆ a, y10xA_fam 3 C K N a := y10xE_img_le_iSup_fam hKC hKP
  have hKeq : y10xA_img C N K = ⨆ a, y10xA_fam 3 C K N a :=
    le_antisymm hcov (iSup_le fun a => y10xE_fam_le_img a)
  have hYK : Y ≤ K ⊔ O := y10xE_Y_mem hp hxC hx hJC hJq h3J hJc hKC hJK hKn hY hdiag
  set σ : ↥C ⧸ N.subgroupOf C := QuotientGroup.mk' (N.subgroupOf C) (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C)
    with hσdef
  have hσp : σ ^ p = 1 := by
    rw [hσdef, ← map_pow]
    have h1 : (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C) ^ p = 1 := Subtype.ext (by simp [inv_pow, hx])
    rw [h1, map_one]
  have hσfam : ∀ a, ∃ b, (y10xA_fam 3 C K N a).map (MulAut.conj σ).toMonoidHom = y10xA_fam 3 C K N b := by
    intro a
    cases a with
    | none => exact ⟨none, y10xE_fam_conj_none hKC hCK (C.inv_mem hxC)⟩
    | some Y' => exact ⟨_, y10xE_fam_conj_some hKC hCK hO hKn' (C.inv_mem hxC) Y'⟩
  have hcommF : ∀ i j : Option (y10xA_I 3 C K), (y10xA_fam 3 C K N) i ≠ (y10xA_fam 3 C K N) j →
      ⁅(y10xA_fam 3 C K N) i, (y10xA_fam 3 C K N) j⁆ = ⊥ := by
    intro i j hne
    exact y10xE_fam_comm hKC hO hcomm' (fun h => hne (by rw [h]))
  have hσcent : Subgroup.centralizer ({σ} : Set (↥C ⧸ N.subgroupOf C)) =
      Subgroup.centralizer ({QuotientGroup.mk' (N.subgroupOf C) (⟨x, hxC⟩ : ↥C)} :
        Set (↥C ⧸ N.subgroupOf C)) := by
    have h1 : σ = (QuotientGroup.mk' (N.subgroupOf C) (⟨x, hxC⟩ : ↥C))⁻¹ := by
      rw [hσdef, ← map_inv]
      rfl
    rw [h1]
    exact y10xA_centralizer_inv _
  have hJN : ¬ J ≤ N := fun hJN' =>
    not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
      ((h3J.trans (Subgroup.card_quotient_dvd_card _)).trans (Subgroup.card_dvd_of_le (hJN'.trans hNOK)))
  have hJs : CFSG.Open.IsSubnormal J (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
    have hJx : J ≤ K ⊓ Subgroup.centralizer ({x} : Set G) := le_inf hJK (fun j hj => (hJc.1 hj).2)
    have h1 := CFSG.Open.IsSubnormal.inf hJc.2.1 (K ⊓ Subgroup.centralizer ({x} : Set G))
    rw [inf_eq_left.2 hJx, inf_eq_right.2 (inf_le_inf_right _ hKC)] at h1
    exact h1
  have hkt := lemma117_khat_transport hp hxC hx hKC hNK hNp' hJK hJq hJN hJs
  have hJcomp' : CFSG.Open.IsComponentOf (y10xA_img C N J)
      (y10xA_img C N K ⊓ Subgroup.centralizer
        ({σ} : Set (↥C ⧸ N.subgroupOf C))) := by
    rw [hσcent]
    exact hkt
  exact hJcomp'

end DiagFam3


section MainAux

variable {G : Type} [Group G] [Finite G]

theorem y10xF_normal_inf {C J N : Subgroup G} (hJC : J ≤ C)
    (hNnorm : C ≤ Subgroup.normalizer (N : Set G)) :
    ((J ⊓ N).subgroupOf J).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hjC : j ∈ C := hJC hj
  constructor
  · intro hh
    exact ⟨J.mul_mem (J.mul_mem hj hh.1) (J.inv_mem hj),
      (Subgroup.mem_normalizer_iff.1 (hNnorm hjC) h).1 hh.2⟩
  · intro hh
    have e : j⁻¹ * (j * h * j⁻¹) * j⁻¹⁻¹ = h := by group
    have h1 := J.mul_mem (J.mul_mem (J.inv_mem hj) hh.1) (J.inv_mem (J.inv_mem hj))
    have h2 := (Subgroup.mem_normalizer_iff.1 (hNnorm (C.inv_mem hjC)) (j * h * j⁻¹)).1 hh.2
    rw [e] at h1 h2
    exact ⟨h1, h2⟩

end MainAux


theorem no_diag_SU6 (hI25 : Input2_5) (hU6 : U6CaseAt G) (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J)
    {x : G} (hp : p.Prime) (hx : x ^ p = 1) (hxx : x ∈ Subgroup.centralizer ({x'} : Set G))
    (hJc : IsComponentOf J (Subgroup.centralizer ({x'} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)))
    (hJp : J ≤ GLAPLayer p' (Subgroup.centralizer ({x'} : Set G)))
    (hJp' : J ≤ GLAPLayer p (Subgroup.centralizer ({x'} : Set G)))
    (hsix : J = L ∧ 3 ∣ Nat.card (Subgroup.center ↥L) ∧ ∃ lab : GLALabel, LabelOf L lab ∧ Odd lab.n ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) :
    ¬ ∃ Y : Subgroup G, GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) Y ∧
        (∀ i j : ℕ, i < p → j < p → i ≠ j → GLBConj (x ^ i) Y ≠ GLBConj (x ^ j) Y) ∧
        J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y := by
  classical
  rintro ⟨Y, hY, hdist, hdiag⟩
  obtain ⟨hJL, h3L, lab, hlab, hodd, hty⟩ := hsix
  subst L
  have hp3 : p' = 3 := (hc.cfg.su_case h3L ⟨lab, hlab, hty⟩).2.1
  subst p'
  have hJC : J ≤ Subgroup.centralizer ({x'} : Set G) := fun j hj => (hc.cfg.comp.1.1 hj).2
  have hJq : CFSG.Open.IsQuasisimple ↥J := hc.cfg.comp.1.2.2
  have h3J : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := (dvd_mul_left 3 p).trans hc.cfg.dvd
  have hNp := closureCore_le_oPPrimeP hctx hc hp hJp'
  have hmJ : GLATwoLocalRank 3 ↥J = m := by rw [hc.cfg.rank_K, hc.e_eq]
  set C : Subgroup G := Subgroup.centralizer ({x'} : Set G) with hCdef
  have hxC : x ∈ C := hxx
  have hJlay : J ≤ GLAPLayer 3 C := hJp
  set K : Subgroup G := closureIn J C with hKdef
  set O : Subgroup G := GLAPPrimeCoreOf 3 C with hOdef
  set OK : Subgroup G := GLAPPrimeCoreOf 3 K with hOKdef
  set N : Subgroup G := ⁅K, OK⁆ with hNdef
  have hKC : K ≤ C := y10xA_closureIn_le hJC
  have hCK : C ≤ Subgroup.normalizer (K : Set G) := y10xA_closureIn_normalizer
  have hJK : J ≤ K := y10xA_le_closureIn C.one_mem
  have hCn : C ≤ Subgroup.normalizer (C : Set G) := fun c hc' => Subgroup.le_normalizer hc'
  have hO : C ≤ Subgroup.normalizer (O : Set G) :=
    fun c hc' => normalizer_le_normalizer_glaPPrimeCoreOf 3 C (hCn hc')
  have hKn : (K.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).2 hCK
  have hKn' : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun c hc' k hk =>
    (Subgroup.mem_normalizer_iff.1 (hCK hc') k).1 hk
  have hOK_le : OK ≤ K := y10xA_coreOf_le K
  have hOKK : K ≤ Subgroup.normalizer (OK : Set G) :=
    fun k hk => normalizer_le_normalizer_glaPPrimeCoreOf 3 K (Subgroup.le_normalizer hk)
  have hNK : N ≤ K := Subgroup.commutator_le.2 fun a ha b hb => y10xA_comm_mem_gen ha (hOK_le hb)
  have hNOK : N ≤ OK := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    have h1 : a * b * a⁻¹ ∈ OK := (Subgroup.mem_normalizer_iff.1 (hOKK ha) b).1 hb
    exact OK.mul_mem h1 (OK.inv_mem hb)
  have hNC : N ≤ C := hNK.trans hKC
  have hN3 : ¬ 3 ∣ Nat.card N := fun h =>
    not_dvd_card_glaPPrimeCoreOf Nat.prime_three K (h.trans (Subgroup.card_dvd_of_le hNOK))
  have hNnorm : C ≤ Subgroup.normalizer (N : Set G) := y10xA_comm_core_normalizer hCK
  haveI hNn : (N.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNC).2 hNnorm
  have hNO : N ≤ O := le_glaPPrimeCoreOf_of_le_normalizer hNC hNnorm
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3)
  have hcommN : ∀ k ∈ K, ∀ t ∈ OK, ⁅k, t⁆ ∈ N := fun k hk t ht =>
    Subgroup.commutator_mem_commutator hk ht
  have hKO : K ⊓ O ≤ OK := le_glaPPrimeCoreOf_of_le_normalizer inf_le_left
    (y10xF_KO_normalizer hKC hCK hO)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (fun h =>
      not_dvd_card_glaPPrimeCoreOf Nat.prime_three C (h.trans (Subgroup.card_dvd_of_le inf_le_right))))
  have hYK : Y ≤ K ⊔ O := y10xE_Y_mem hp hxC hx hJC hJq h3J hJc hKC hJK hKn hY hdiag
  have hJcomp := y10xF_Jcomp hp hxC hx hJC hJlay hJq hJc h3J (N := N) rfl hNp hY hdiag
  have hJbound := y10xE_Rdata hp hxC hx hJC hJlay hJq hJc h3J hNp hY hdiag
  have hσp : (y10xF_sigma (N := N) x hxC) ^ p = 1 := by
    unfold y10xF_sigma
    rw [← map_pow]
    have h1 : (⟨x⁻¹, C.inv_mem hxC⟩ : ↥C) ^ p = 1 := Subtype.ext (by simp [inv_pow, hx])
    rw [h1, map_one]
  let D : ℕ → Subgroup (↥C ⧸ N.subgroupOf C) := fun k =>
    ⁅y10xF_P N hxC hY hYK hKC hCK hO k, y10xF_P N hxC hY hYK hKC hCK hO k⁆
  have hD_qs : ∀ k, CFSG.Open.IsQuasisimple ↥(D k) := fun k =>
    (y10xF_D_qs hxC hY hYK hKC hCK hO hNO hKO hOK_le hcommN k).2
  have hD_per : ∀ k, D (k + p) = D k := fun k => by
    show ⁅y10xF_P N hxC hY hYK hKC hCK hO (k + p), y10xF_P N hxC hY hYK hKC hCK hO (k + p)⁆ =
      ⁅y10xF_P N hxC hY hYK hKC hCK hO k, y10xF_P N hxC hY hYK hKC hCK hO k⁆
    rw [y10xF_P_per hxC hY hYK hKC hCK hO hNO hx k]
  have hD_comm : ∀ k j, k % p ≠ j % p → ⁅D k, D j⁆ = ⊥ := fun k j hkj =>
    y10xF_D_comm hxC hY hYK hKC hCK hO hNO hcommN hp hx hdist k j hkj
  have hD_ne : ∀ k j, k % p ≠ j % p → D k ≠ D j := fun k j hkj =>
    y10xF_D_ne hxC hY hYK hKC hCK hO hNO hKO hOK_le hcommN hp hx hdist k j hkj
  have hD_shift : ∀ k, (D k).map (MulAut.conj (y10xF_sigma (N := N) x hxC)).toMonoidHom =
      D (k + 1) := fun k => y10xF_D_shift hxC hY hYK hKC hCK hO hNO hKn' k
  have hlayer := y10xF_input25_app hI25 hp hσp hD_qs hD_per hD_comm hD_ne hD_shift
  obtain ⟨hcompD, -⟩ := y10xF_components_of_family hp hD_qs hD_per hD_comm
  set X : Subgroup (↥C ⧸ N.subgroupOf C) := ⨆ k, D k with hXdef
  set Z0 : Subgroup (↥C ⧸ N.subgroupOf C) := y10xA_img C N OK with hZ0def
  set Jh : Subgroup (↥C ⧸ N.subgroupOf C) := y10xA_img C N J with hJhdef
  have hPK : ∀ k, y10xF_P N hxC hY hYK hKC hCK hO k ≤ y10xA_img C N K := fun k =>
    y10xE_fam_le_img (N := N) (C := C) (K := K) _
  have hX_le : X ≤ y10xA_img C N K := iSup_le fun k =>
    (y10xF_commutator_le_self _).trans (hPK k)
  have hZ := y10xA_img_central (N := N) hKC hOK_le hcommN
  have hZX : ∀ v ∈ Z0, ∀ w ∈ X, v * w = w * v := fun v hv w hw =>
    (hZ v hv w (hX_le hw)).symm
  have hZT : ∀ v ∈ Z0, ∀ t ∈ Jh, v * t = t * v := fun v hv t ht =>
    (hZ v hv t (y10xA_img_mono hJK ht)).symm
  have hJX : Jh ≤ X ⊔ Z0 := hJbound.trans (iSup_le fun k =>
    (y10xF_P_le_D hxC hY hYK hKC hCK hO hNO hKO hOK_le hcommN k).trans
      (sup_le_sup (le_iSup D k) le_rfl))
  have hJq' : CFSG.Open.IsQuasisimple ↥Jh := hJcomp.2.2
  have hJX' : Jh ≤ X := y10xF_sub_of_sup hZX hZT hJX (y10xA_qs_comm_self hJq')
  set σ : ↥C ⧸ N.subgroupOf C := y10xF_sigma (N := N) x hxC with hσdef
  set E : Subgroup (↥C ⧸ N.subgroupOf C) := Subgroup.zpowers σ with hEdef
  have hEC : Subgroup.centralizer ({σ} : Set (↥C ⧸ N.subgroupOf C)) =
      Subgroup.centralizer (E : Set (↥C ⧸ N.subgroupOf C)) := y10xA_centralizer_singleton_eq σ
  have hJcent : Jh ≤ Subgroup.centralizer ({σ} : Set (↥C ⧸ N.subgroupOf C)) := fun t ht =>
    (hJcomp.1 ht).2
  have hBle : X ⊓ Subgroup.centralizer (E : Set (↥C ⧸ N.subgroupOf C)) ≤
      y10xA_img C N K ⊓ Subgroup.centralizer ({σ} : Set (↥C ⧸ N.subgroupOf C)) :=
    le_inf (inf_le_left.trans hX_le) (inf_le_right.trans (le_of_eq hEC.symm))
  have hJE : CFSG.Open.IsComponentOf Jh
      (X ⊓ Subgroup.centralizer (E : Set (↥C ⧸ N.subgroupOf C))) := by
    have hJC' : Jh ≤ Subgroup.centralizer (E : Set (↥C ⧸ N.subgroupOf C)) := fun t ht => by
      rw [← hEC]
      exact hJcent ht
    have hsub := CFSG.Open.IsSubnormal.inf hJcomp.2.1
      (X ⊓ Subgroup.centralizer (E : Set (↥C ⧸ N.subgroupOf C)))
    rw [inf_eq_left.2 (le_inf hJX' hJC'), inf_eq_right.2 hBle] at hsub
    exact ⟨le_inf hJX' hJC', hsub, hJq'⟩
  obtain ⟨Z, hZn, hZc, ⟨e⟩⟩ := hlayer (D 0) (hcompD 0)
  haveI := hZn
  have hJL : Jh ≤ GLALayer (X ⊓ Subgroup.centralizer (E : Set (↥C ⧸ N.subgroupOf C))) :=
    le_sSup (s := {K' : Subgroup (↥C ⧸ N.subgroupOf C) |
      CFSG.Open.IsComponentOf K' (X ⊓ Subgroup.centralizer (E : Set (↥C ⧸ N.subgroupOf C)))}) hJE
  have hL'q := y10xF_layer_qs (hD_qs 0) hZc e hJL hJq'
  have hJeq := y10xF_layer_eq hJE hL'q
  have e1 : (↥(D 0) ⧸ Z) ≃* ↥Jh := e.symm.trans (MulEquiv.subgroupCongr hJeq.symm)
  have hX0comm : commutator ↥(D 0) = ⊤ := (hD_qs 0).1
  have ψ1 := (y10xE_quot_quot_center_equiv hX0comm Z hZc).symm
  have ψ2 := y10xE_quot_center_equiv e1
  let φ0 : ↥J →* (↥C ⧸ N.subgroupOf C) :=
    (QuotientGroup.mk' (N.subgroupOf C)).comp (Subgroup.inclusion hJC)
  have hφ0 : ∀ j : ↥J, φ0 j ∈ Jh := fun j => y10xA_mem_img (hJC j.2) j.2
  let φ : ↥J →* ↥Jh := φ0.codRestrict Jh hφ0
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨c, hcJ, hcy⟩ := y10xA_exists_of_mem_img y.2
    exact ⟨⟨(c : G), hcJ⟩, Subtype.ext hcy⟩
  have hJNcentral : ∀ j : ↥J, (j : G) ∈ N → j ∈ Subgroup.center ↥J := by
    have hMn := y10xF_normal_inf hJC hNnorm
    have hnot : (J ⊓ N).subgroupOf J ≠ ⊤ := by
      intro htop
      have hJle : J ≤ J ⊓ N := Subgroup.subgroupOf_eq_top.1 htop
      apply hN3
      exact h3J.trans ((Subgroup.card_quotient_dvd_card _).trans
        (Subgroup.card_dvd_of_le (hJle.trans inf_le_right)))
    have hle := (y10xE_normal_dich hJq hMn).resolve_right hnot
    intro j hj
    exact hle (Subgroup.mem_subgroupOf.2 ⟨j.2, hj⟩)
  have hφker : ∀ j : ↥J, φ j = 1 → j ∈ Subgroup.center ↥J := by
    intro j hj
    have hj1 : φ0 j = 1 := congrArg Subtype.val hj
    exact hJNcentral j (Subgroup.mem_subgroupOf.1
      ((QuotientGroup.eq_one_iff (Subgroup.inclusion hJC j)).1 hj1))
  have ψ3 := (y10xF_quot_center_equiv_of_surj φ hφs hJq.1 hφker).some
  have ψ := ψ1.trans (ψ2.trans ψ3.symm)
  have hXmark : GLAMarking ↥(D 0) (fun lab' _ _ _ _ _ => lab' = lab) :=
    y10xD_marking_transfer lab hX0comm ψ hlab
  have hkidx : φ.ker.index = Nat.card ↥Jh :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv
  have hk_card : Nat.card ↥J = Nat.card φ.ker * Nat.card ↥Jh := by
    rw [← hkidx]
    exact (Subgroup.card_mul_index φ.ker).symm
  have hZidx : Z.index = Nat.card ↥Jh := Nat.card_congr e1.toEquiv
  have hz_q : Nat.card Z * Z.index = Nat.card ↥(D 0) := Subgroup.card_mul_index Z
  have hc_a : Nat.card (Subgroup.center ↥(D 0)) * (Subgroup.center ↥(D 0)).index =
      Nat.card ↥(D 0) := Subgroup.card_mul_index _
  have hidx : (Subgroup.center ↥(D 0)).index = (Subgroup.center ↥J).index :=
    Nat.card_congr ψ.toEquiv
  have hJc_a : Nat.card (Subgroup.center ↥J) * (Subgroup.center ↥J).index = Nat.card ↥J :=
    Subgroup.card_mul_index _
  have hkerle : φ.ker ≤ Subgroup.center ↥J := fun j hj => hφker j (MonoidHom.mem_ker.1 hj)
  have hkerN : φ.ker.map J.subtype ≤ N := by
    rintro _ ⟨j, hj, rfl⟩
    have hj1 : φ0 j = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hj)
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (Subgroup.inclusion hJC j)).1 hj1)
  have hkN : Nat.card φ.ker ∣ Nat.card N := by
    rw [← Subgroup.card_map_of_injective J.subtype_injective]
    exact Subgroup.card_dvd_of_le hkerN
  have hk0N : ¬ 3 ∣ Nat.card φ.ker := fun h => hN3 (h.trans hkN)
  have hk0odd : ¬ 2 ∣ Nat.card φ.ker := by
    have hd : Nat.card φ.ker ∣ Nat.card (Subgroup.center ↥J) := Subgroup.card_dvd_of_le hkerle
    exact (Odd.of_dvd_nat hc.cfg.odd_center hd).not_two_dvd_nat
  have ha0 : 0 < (Subgroup.center ↥(D 0)).index := Nat.card_pos
  have h3X0 : 3 ∣ Nat.card (Subgroup.center ↥(D 0)) := by
    have h1 : Nat.card (Subgroup.center ↥(D 0)) * (Subgroup.center ↥(D 0)).index =
        Nat.card Z * Nat.card ↥Jh := by
      rw [hc_a, ← hz_q, hZidx]
    have h2 : Nat.card (Subgroup.center ↥J) * (Subgroup.center ↥(D 0)).index =
        Nat.card φ.ker * Nat.card ↥Jh := by
      rw [hidx, hJc_a, hk_card]
    exact y10xF_dvd_of_eq ha0 h1 h2 h3L hk0N
  have hm4 : 4 ≤ m := hctx.1.four_le
  have hpos : 0 < CFSG.Open.twoLocalPrimeRank 3 ↥J := by
    have hdef : GLATwoLocalRank 3 ↥J = CFSG.Open.twoLocalPrimeRank 3 ↥J := rfl
    omega
  have h2J : 2 ∣ Nat.card ↥J := by
    obtain ⟨H, hH⟩ := y10xF_two_local_exists hpos
    obtain ⟨P, hPne, hPp, -⟩ := hH
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hPp
    have hn0 : n ≠ 0 := by
      intro h0
      apply hPne
      apply Subgroup.eq_bot_of_card_eq
      rw [hn, h0, pow_zero]
    have h2P : 2 ∣ Nat.card P := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact h2P.trans (Subgroup.card_subgroup_dvd_card P)
  have h2J1 : 2 ∣ Nat.card ↥Jh := by
    have h : 2 ∣ Nat.card φ.ker * Nat.card ↥Jh := by
      rw [← hk_card]
      exact h2J
    exact ((Nat.Prime.dvd_mul Nat.prime_two).1 h).resolve_left hk0odd
  have h2D0 : 2 ∣ Nat.card ↥(D 0) := by
    rw [← hz_q, hZidx]
    exact Dvd.dvd.mul_left h2J1 _
  haveI : Fintype ↥(D 0) := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard2 : 2 ∣ Fintype.card ↥(D 0) := by
    rw [Fintype.card_eq_nat_card]
    exact h2D0
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 hcard2
  have hS0 : ∃ S0 : Subgroup ↥(D 0), S0 ≠ ⊥ ∧ IsPGroup 2 S0 := by
    refine ⟨Subgroup.zpowers g, ?_, IsPGroup.of_card (n := 1) ?_⟩
    · intro h
      have hg1 : g ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hg
        norm_num at hg
      apply hg1
      have hmem : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · rw [Nat.card_zpowers, hg]
      norm_num
  have hE1 : ∃ E1 : Subgroup (↥C ⧸ N.subgroupOf C), E1 ≤ D 1 ∧ CFSG.Open.IsElemAbelian 3 E1 ∧
      Nat.card E1 = 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(D 0)) := by
    obtain ⟨E0, -, hE0e, hE0c⟩ :=
      CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup ↥(D 0))
    have hsh : (D 0).map (MulAut.conj σ).toMonoidHom = D 1 := hD_shift 0
    have hE0D : E0.map (D 0).subtype ≤ D 0 := by
      rintro _ ⟨e0, -, rfl⟩
      exact e0.2
    refine ⟨(E0.map (D 0).subtype).map (MulAut.conj σ).toMonoidHom, ?_, ?_, ?_⟩
    · exact (Subgroup.map_mono hE0D).trans (le_of_eq hsh)
    · exact y10xF_elemAb_map (MulAut.conj σ).toMonoidHom (MulAut.conj σ).injective
        (y10xF_elemAb_map (D 0).subtype (D 0).subtype_injective hE0e)
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj σ).toMonoidHom) (MulAut.conj σ).injective,
        Subgroup.card_map_of_injective (f := (D 0).subtype) (D 0).subtype_injective, hE0c]
  have hcomm01 : ⁅D 0, D 1⁆ = ⊥ := hD_comm 0 1 (by
    rw [Nat.zero_mod, Nat.mod_eq_of_lt hp.one_lt]
    norm_num)
  obtain ⟨k, hk1, hk2⟩ := y10xF_count_bound (hD_qs 0) hcomm01 hS0 hE1
  have hU := hU6 J lab hlab hodd hty h3L (↥(D 0)) hXmark h3X0
  have hΓ : GLATwoLocalRank 3 (↥C ⧸ N.subgroupOf C) ≤ m := by
    have hN3C : ¬ 3 ∣ Nat.card (N.subgroupOf C) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
      exact hN3
    have h1 := glaTwoLocalRank_quotient_le Nat.prime_three (by norm_num) (N.subgroupOf C) hN3C
    have h2 := twoLocalRank_le_top Nat.prime_three C
    have h3 : GLATwoLocalRank 3 G = m := hc.mu.2.1
    omega
  rw [hmJ] at hU
  omega

section Diag

variable {Q : Type} [Group Q]

private def lemma117_diagQ {p : ℕ} (Yq : Fin p → Subgroup Q) (k : Fin p) : Subgroup Q :=
  ⨆ j : {j : Fin p // j ≠ k}, Yq j.1

private theorem lemma117_diagQ_comm {p : ℕ} {Yq : Fin p → Subgroup Q}
    (hYc : ∀ i j, i ≠ j → ⁅Yq i, Yq j⁆ = ⊥) (k : Fin p) :
    ∀ y ∈ Yq k, ∀ z ∈ lemma117_diagQ Yq k, y * z = z * y := by
  intro y hy z hz
  have hle : lemma117_diagQ Yq k ≤ Subgroup.centralizer (Yq k : Set Q) := by
    refine iSup_le fun j => ?_
    have hc : Yq j.1 ≤ Subgroup.centralizer (Yq k : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hYc j.1 k j.2)
    exact hc
  exact (Subgroup.mem_centralizer_iff.1 (hle hz)) y hy

private theorem lemma117_diag_EN_YY {p : ℕ} {Yq : Fin p → Subgroup Q}
    (hYc : ∀ i j, i ≠ j → ⁅Yq i, Yq j⁆ = ⊥) (i j : Fin p) : lemma117_EN (Yq i) (Yq j) := by
  intro h hh t ht
  by_cases hij : i = j
  · subst hij
    exact (Yq i).mul_mem ((Yq i).mul_mem hh ht) ((Yq i).inv_mem hh)
  · have hc : Yq i ≤ Subgroup.centralizer (Yq j : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hYc i j hij)
    have hcomm : t * h = h * t := (Subgroup.mem_centralizer_iff.1 (hc hh)) t ht
    have e : h * t * h⁻¹ = t := by
      rw [← hcomm]
      group
    rw [e]
    exact ht

private theorem lemma117_diag_norm {p : ℕ} {Yq : Fin p → Subgroup Q}
    (hYc : ∀ i j, i ≠ j → ⁅Yq i, Yq j⁆ = ⊥) (k : Fin p) :
    lemma117_EN (⨆ j, Yq j) (lemma117_diagQ Yq k) := by
  refine lemma117_en_of_iSup fun j => ?_
  exact lemma117_en_iSup fun i : {i : Fin p // i ≠ k} => lemma117_diag_EN_YY hYc j i.1

private theorem lemma117_diag_conj_le {p : ℕ} {Yq : Fin p → Subgroup Q} {xb : Q} {f : Fin p → Fin p}
    (hf : Function.Injective f) (hxY : ∀ i, (Yq i).map (MulAut.conj xb).toMonoidHom ≤ Yq (f i))
    (k : Fin p) :
    (lemma117_diagQ Yq k).map (MulAut.conj xb).toMonoidHom ≤ lemma117_diagQ Yq (f k) := by
  rw [lemma117_diagQ, Subgroup.map_iSup]
  refine iSup_le fun j => ?_
  refine (hxY j.1).trans ?_
  exact le_iSup (fun i : {i : Fin p // i ≠ f k} => Yq i.1) ⟨f j.1, fun h => j.2 (hf h)⟩

end Diag

section Diag2

variable {Q : Type} [Group Q]

private theorem lemma117_diag_not_le {p : ℕ} {Yq : Fin p → Subgroup Q}
    (hYc : ∀ i j, i ≠ j → ⁅Yq i, Yq j⁆ = ⊥)
    {xb : Q} {f : Fin p → Fin p} (hf : Function.Injective f)
    (hxY : ∀ i, (Yq i).map (MulAut.conj xb).toMonoidHom ≤ Yq (f i))
    (hcyc : ∀ i j : Fin p, ∃ t : ℕ, f^[t] i = j)
    {J : Subgroup Q} (hJY : J ≤ ⨆ j, Yq j) (hJc : ∀ j ∈ J, xb * j * xb⁻¹ = j)
    (hJperf : commutator ↥J = ⊤) (hJnt : Nontrivial ↥J) (k : Fin p) :
    ¬ J ≤ lemma117_diagQ Yq k := by
  intro hk
  have hstep : ∀ k, J ≤ lemma117_diagQ Yq k → J ≤ lemma117_diagQ Yq (f k) := by
    intro k hk j hj
    have hmem : (MulAut.conj xb).toMonoidHom j ∈ (lemma117_diagQ Yq k).map (MulAut.conj xb).toMonoidHom :=
      Subgroup.mem_map.2 ⟨j, hk hj, rfl⟩
    have e : (MulAut.conj xb).toMonoidHom j = j := by
      simpa [MulAut.conj_apply] using hJc j hj
    rw [e] at hmem
    exact lemma117_diag_conj_le hf hxY k hmem
  have hiter : ∀ t : ℕ, ∀ k, J ≤ lemma117_diagQ Yq k → J ≤ lemma117_diagQ Yq (f^[t] k) := by
    intro t
    induction t with
    | zero => intro k hk; exact hk
    | succ n ih =>
      intro k hk
      rw [Function.iterate_succ_apply]
      exact ih (f k) (hstep k hk)
  have hall : ∀ j, J ≤ lemma117_diagQ Yq j := by
    intro j
    obtain ⟨t, ht⟩ := hcyc k j
    rw [← ht]
    exact hiter t k hk
  have hcent : ∀ w ∈ J, ∀ u ∈ (⨆ j, Yq j), u * w = w * u := by
    intro w hw u hu
    refine Subgroup.iSup_induction (fun j => Yq j) (C := fun u => u * w = w * u) hu ?_ ?_ ?_
    · intro j x hx
      exact lemma117_diagQ_comm hYc j x hx w (hall j hw)
    · simp
    · intro x y hx hy
      calc x * y * w = x * (y * w) := by group
        _ = x * (w * y) := by rw [hy]
        _ = (x * w) * y := by group
        _ = (w * x) * y := by rw [hx]
        _ = w * (x * y) := by group
  have hJcom : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := fun a ha b hb => hcent b hb a (hJY ha)
  have hcomm_bot : commutator ↥J = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    exact Subtype.ext (hJcom h.1 h.2 a.1 a.2)
  have htop : (⊤ : Subgroup ↥J) = ⊥ := by rw [← hJperf, hcomm_bot]
  haveI := hJnt
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥J)
  have hx' : x ∈ (⊤ : Subgroup ↥J) := Subgroup.mem_top x
  rw [htop, Subgroup.mem_bot] at hx'
  exact hx hx'

private theorem lemma117_diag_inf_eq_bot {p : ℕ} {Yq : Fin p → Subgroup Q}
    (hYc : ∀ i j, i ≠ j → ⁅Yq i, Yq j⁆ = ⊥)
    {xb : Q} {f : Fin p → Fin p} (hf : Function.Injective f)
    (hxY : ∀ i, (Yq i).map (MulAut.conj xb).toMonoidHom ≤ Yq (f i))
    (hcyc : ∀ i j : Fin p, ∃ t : ℕ, f^[t] i = j)
    {J : Subgroup Q} (hJY : J ≤ ⨆ j, Yq j) (hJc : ∀ j ∈ J, xb * j * xb⁻¹ = j)
    (hJperf : commutator ↥J = ⊤) (hJnt : Nontrivial ↥J) (hJs : IsSimpleGroup ↥J) (k : Fin p) :
    J ⊓ lemma117_diagQ Yq k = ⊥ := by
  have hnorm : ((J ⊓ lemma117_diagQ Yq k).subgroupOf J).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨(J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2)), ?_⟩
    exact lemma117_diag_norm hYc k _ (hJY g.2) _ hn.2
  rcases hJs.eq_bot_or_eq_top_of_normal ((J ⊓ lemma117_diagQ Yq k).subgroupOf J) with hb | ht
  · ext n
    constructor
    · intro hn
      have hmem : (⟨n, hn.1⟩ : ↥J) ∈ (J ⊓ lemma117_diagQ Yq k).subgroupOf J := Subgroup.mem_subgroupOf.2 hn
      rw [hb, Subgroup.mem_bot] at hmem
      have : n = 1 := congrArg Subtype.val hmem
      rw [this]
      exact Subgroup.one_mem _
    · intro hn
      rw [Subgroup.mem_bot] at hn
      rw [hn]
      exact Subgroup.one_mem _
  · exfalso
    apply lemma117_diag_not_le hYc hf hxY hcyc hJY hJc hJperf hJnt k
    intro j hj
    have hmem : (⟨j, hj⟩ : ↥J) ∈ (J ⊓ lemma117_diagQ Yq k).subgroupOf J := by
      rw [ht]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.1 hmem).2

end Diag2

section Diag3

variable {Q : Type} [Group Q]

private theorem lemma117_diag_iUnion_le {p : ℕ} (Yq : Fin p → Subgroup Q) (k : Fin p) :
    (⨆ j, Yq j) ≤ Yq k ⊔ lemma117_diagQ Yq k := by
  refine iSup_le fun j => ?_
  by_cases hjk : j = k
  · subst hjk
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup (fun i : {i : Fin p // i ≠ k} => Yq i.1) ⟨j, hjk⟩)

private theorem lemma117_diag_E_cover {p : ℕ} {Yq : Fin p → Subgroup Q}
    (hYc : ∀ i j, i ≠ j → ⁅Yq i, Yq j⁆ = ⊥) {J : Subgroup Q} (hJY : J ≤ ⨆ j, Yq j)
    (k : Fin p) {w : Q} (hw : w ∈ J ⊔ lemma117_diagQ Yq k) :
    ∃ y ∈ Yq k ⊓ (J ⊔ lemma117_diagQ Yq k), ∃ q ∈ lemma117_diagQ Yq k, y * q = w := by
  obtain ⟨j, hj, q, hq, rfl⟩ := lemma117_diag_sup_decomp_norm (A := J) (B := lemma117_diagQ Yq k)
    (fun a ha b hb => lemma117_diag_norm hYc k a (hJY ha) b hb) hw
  have hjYQ : j ∈ Yq k ⊔ lemma117_diagQ Yq k := lemma117_diag_iUnion_le Yq k (hJY hj)
  obtain ⟨y, hy, q', hq', hyq⟩ := lemma117_mem_sup_decomp
    (A := Yq k) (B := lemma117_diagQ Yq k) (fun a ha b hb => lemma117_diagQ_comm hYc k a ha b hb) hjYQ
  refine ⟨y, ⟨hy, ?_⟩, q' * q, (lemma117_diagQ Yq k).mul_mem hq' hq, ?_⟩
  · have : y = j * q'⁻¹ := by rw [← hyq]; group
    rw [this]
    exact (J ⊔ lemma117_diagQ Yq k).mul_mem ((le_sup_left : J ≤ J ⊔ lemma117_diagQ Yq k) hj)
      ((le_sup_right : lemma117_diagQ Yq k ≤ J ⊔ lemma117_diagQ Yq k) ((lemma117_diagQ Yq k).inv_mem hq'))
  · rw [← mul_assoc, hyq]

end Diag3

section Diag4

variable {Q : Type} [Group Q] [Finite Q]

private theorem lemma117_diag_perfect_of_comm_self {D : Subgroup Q} (h : ⁅D, D⁆ = D) : commutator ↥D = ⊤ := by
  have h1 : Subgroup.map D.subtype (⊤ : Subgroup ↥D) = D := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective (f := D.subtype) Subtype.coe_injective
  rw [commutator_def, Subgroup.map_commutator, h1, h]

private theorem lemma117_diag_comm_mul_central {E : Subgroup Q} {z a b : Q} (hz : ∀ x ∈ E, x * z = z * x)
    (ha : a ∈ E) (hb : b ∈ E) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hzb : z * b = b * z := (hz b hb).symm
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hzb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem lemma117_diag_comm_central_mul {E : Subgroup Q} {z a b : Q} (hz : ∀ x ∈ E, x * z = z * x)
    (ha : a ∈ E) (hb : b ∈ E) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hza : a * z = z * a := hz a ha
  have hza' : z * a⁻¹ = a⁻¹ * z := by
    calc z * a⁻¹ = a⁻¹ * (a * z) * a⁻¹ := by group
      _ = a⁻¹ * (z * a) * a⁻¹ := by rw [hza]
      _ = a⁻¹ * z := by group
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hza']
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem lemma117_diag_iso {p : ℕ} {Yq : Fin p → Subgroup Q}
    (hYc : ∀ i j, i ≠ j → ⁅Yq i, Yq j⁆ = ⊥)
    {J : Subgroup Q} (hJY : J ≤ ⨆ j, Yq j) (k : Fin p)
    (hJperf : commutator ↥J = ⊤) (hJinf : J ⊓ lemma117_diagQ Yq k = ⊥)
    (hJtm : ∀ (E : Type) [Group E] [Finite E], commutator E = ⊤ → ∀ π : E →* ↥J,
        Function.Surjective π → π.ker ≤ Subgroup.center E → π.ker = ⊥) :
    ∃ ι : ↥J →* Q, Function.Injective ι ∧ (∀ j, ι j ∈ Yq k) ∧
      (∀ j, ι j ∈ lemma117_diagQ Yq k → ι j = 1) := by
  classical
  have hJnorm : ∀ a ∈ J, ∀ b ∈ lemma117_diagQ Yq k, a * b * a⁻¹ ∈ lemma117_diagQ Yq k :=
    fun a ha b hb => lemma117_diag_norm hYc k a (hJY ha) b hb
  set W : Subgroup Q := J ⊔ lemma117_diagQ Yq k with hW
  have hJW : J ≤ W := le_sup_left
  have hEN_W : ∀ h ∈ W, ∀ t ∈ lemma117_diagQ Yq k, h * t * h⁻¹ ∈ lemma117_diagQ Yq k := by
    intro h hh t ht
    obtain ⟨j, hj, q, hq, rfl⟩ := lemma117_diag_sup_decomp_norm (A := J) (B := lemma117_diagQ Yq k) hJnorm hh
    have e : j * q * t * (j * q)⁻¹ = j * (q * t * q⁻¹) * j⁻¹ := by group
    rw [e]
    exact hJnorm j hj _ ((lemma117_diagQ Yq k).mul_mem ((lemma117_diagQ Yq k).mul_mem hq ht)
      ((lemma117_diagQ Yq k).inv_mem hq))
  set Qn : Subgroup ↥W := (lemma117_diagQ Yq k).subgroupOf W with hQn
  haveI hQn_normal : Qn.Normal := by
    constructor
    intro n hn g
    rw [hQn, Subgroup.mem_subgroupOf] at hn ⊢
    have := hEN_W (g : Q) g.2 (n : Q) hn
    simpa using this
  let pW : ↥W →* ↥W ⧸ Qn := QuotientGroup.mk' Qn
  have hQn_iff : ∀ a b : ↥W, pW a = pW b ↔ ((a : Q)⁻¹ * (b : Q)) ∈ lemma117_diagQ Yq k := by
    intro a b
    show QuotientGroup.mk' Qn a = QuotientGroup.mk' Qn b ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hQn,
      Subgroup.mem_subgroupOf]
    simp
  have hpW_surj : Function.Surjective pW := QuotientGroup.mk'_surjective Qn
  let ψ0 : ↥J →* ↥W ⧸ Qn := pW.comp (Subgroup.inclusion hJW)
  have hψ0_surj : Function.Surjective ψ0 := by
    intro c
    obtain ⟨x, rfl⟩ := hpW_surj c
    obtain ⟨j, hj, q, hq, hjq⟩ := lemma117_diag_sup_decomp_norm (A := J) (B := lemma117_diagQ Yq k) hJnorm x.2
    refine ⟨⟨j, hj⟩, ?_⟩
    show pW (Subgroup.inclusion hJW ⟨j, hj⟩) = pW x
    rw [hQn_iff]
    simp only [Subgroup.coe_inclusion]
    rw [← hjq, inv_mul_cancel_left] at *
    exact hq
  have hψ0_inj : Function.Injective ψ0 := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have h1 : pW (Subgroup.inclusion hJW j) = 1 := hj
    have hmem : (j : Q) ∈ lemma117_diagQ Yq k := by
      have := (QuotientGroup.eq_one_iff (Subgroup.inclusion hJW j)).1 h1
      exact Subgroup.mem_subgroupOf.1 this
    have h2 : (j : Q) ∈ J ⊓ lemma117_diagQ Yq k := ⟨j.2, hmem⟩
    rw [hJinf, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  let ψe : ↥J ≃* ↥W ⧸ Qn := MulEquiv.ofBijective ψ0 ⟨hψ0_inj, hψ0_surj⟩
  have hWq : commutator (↥W ⧸ Qn) = ⊤ := by
    have hmapc : (commutator ↥J).map ψ0 = commutator (↥W ⧸ Qn) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective ψ0 hψ0_surj]
    rw [← hmapc, hJperf, Subgroup.map_top_of_surjective ψ0 hψ0_surj]
  set E : Subgroup Q := Yq k ⊓ W with hE
  set E' : Subgroup ↥W := E.subgroupOf W with hE'
  have hE_surj : ∀ x : ↥W, ∃ e ∈ E', pW e = pW x := by
    intro x
    obtain ⟨y, hy, q, hq, hyq⟩ := lemma117_diag_E_cover hYc hJY k x.2
    refine ⟨⟨y, hy.2⟩, Subgroup.mem_subgroupOf.2 hy, ?_⟩
    rw [hQn_iff]
    simp only [Subgroup.coe_mk]
    rw [← hyq, inv_mul_cancel_left]
    exact hq
  have hE_map : Subgroup.map pW E' = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨x, rfl⟩ := hpW_surj c
    obtain ⟨e, he, hpe⟩ := hE_surj x
    exact Subgroup.mem_map.2 ⟨e, he, hpe⟩
  set D : Subgroup Q := ⁅E, E⁆ with hD
  have hDE : D ≤ E := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact E.mul_mem (E.mul_mem (E.mul_mem ha hb) (E.inv_mem ha)) (E.inv_mem hb)
  have hDW : D ≤ W := hDE.trans inf_le_right
  have hDY : D ≤ Yq k := hDE.trans inf_le_left
  have hmapD : Subgroup.map pW ⁅E', E'⁆ = ⊤ := by
    rw [Subgroup.map_commutator, hE_map, ← commutator_def, hWq]
  have hD_cover : ∀ x : ↥W, ∃ d : ↥W, d ∈ ⁅E', E'⁆ ∧ pW d = pW x := by
    intro x
    have hx : pW x ∈ Subgroup.map pW ⁅E', E'⁆ := by
      rw [hmapD]
      exact Subgroup.mem_top _
    obtain ⟨d, hd, hpd⟩ := Subgroup.mem_map.1 hx
    exact ⟨d, hd, hpd⟩
  have hD_of : ∀ d : ↥W, d ∈ ⁅E', E'⁆ → (d : Q) ∈ D := by
    intro d hd
    have hle : ⁅E', E'⁆ ≤ D.subgroupOf W := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [Subgroup.mem_subgroupOf]
      have hab : ((⁅a, b⁆ : ↥W) : Q) = ⁅(a : Q), (b : Q)⁆ := rfl
      rw [hab]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 ha)
        (Subgroup.mem_subgroupOf.1 hb)
    exact Subgroup.mem_subgroupOf.1 (hle hd)
  have hE_dec : ∀ e ∈ E, ∃ d ∈ D, ∃ z ∈ Yq k ⊓ lemma117_diagQ Yq k, d * z = e := by
    intro e he
    obtain ⟨d, hd, hpd⟩ := hD_cover ⟨e, he.2⟩
    have hdq : (d : Q)⁻¹ * e ∈ lemma117_diagQ Yq k := (hQn_iff d ⟨e, he.2⟩).1 hpd
    have hdE : (d : Q) ∈ E := hDE (hD_of d hd)
    have hzE : (d : Q)⁻¹ * e ∈ E := E.mul_mem (E.inv_mem hdE) he
    refine ⟨(d : Q), hD_of d hd, (d : Q)⁻¹ * e, ⟨hzE.1, hdq⟩, ?_⟩
    group
  have hDperf : ⁅D, D⁆ = D := by
    apply le_antisymm
    · exact Subgroup.commutator_mono hDE hDE
    · show ⁅E, E⁆ ≤ ⁅D, D⁆
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      obtain ⟨d1, hd1, z1, hz1, rfl⟩ := hE_dec a ha
      obtain ⟨d2, hd2, z2, hz2, rfl⟩ := hE_dec b hb
      have hcz1 : ∀ x ∈ E, x * z1 = z1 * x := fun x hx => lemma117_diagQ_comm hYc k x hx.1 z1 hz1.2
      have hcz2 : ∀ x ∈ E, x * z2 = z2 * x := fun x hx => lemma117_diagQ_comm hYc k x hx.1 z2 hz2.2
      rw [lemma117_diag_comm_central_mul hcz2 ha (hDE hd2), lemma117_diag_comm_mul_central hcz1 (hDE hd1) (hDE hd2)]
      exact Subgroup.commutator_mem_commutator hd1 hd2
  have hDperf' : commutator ↥D = ⊤ := lemma117_diag_perfect_of_comm_self hDperf
  let πD : ↥D →* ↥J := ψe.symm.toMonoidHom.comp (pW.comp (Subgroup.inclusion hDW))
  have hπD_surj : Function.Surjective πD := by
    intro j
    obtain ⟨d, hd, hpd⟩ := hD_cover (Subgroup.inclusion hJW j)
    refine ⟨⟨(d : Q), hD_of d hd⟩, ?_⟩
    show ψe.symm (pW (Subgroup.inclusion hDW ⟨(d : Q), hD_of d hd⟩)) = j
    have h1 : pW d = ψ0 j := hpd
    have h2 : ψe j = ψ0 j := rfl
    have h3 : Subgroup.inclusion hDW ⟨(d : Q), hD_of d hd⟩ = d := rfl
    rw [h3, h1, ← h2]
    exact ψe.symm_apply_apply j
  have hπD_ker : πD.ker ≤ Subgroup.center ↥D := by
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have h1 : pW (Subgroup.inclusion hDW d) = 1 := ψe.symm.injective (by rw [map_one]; exact hd)
    have h1' : ((Subgroup.inclusion hDW d : ↥W) : ↥W ⧸ Qn) = 1 := h1
    have hmemW : (Subgroup.inclusion hDW d : ↥W) ∈ Qn :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hDW d)).1 h1'
    have hdq : (d : Q) ∈ lemma117_diagQ Yq k := Subgroup.mem_subgroupOf.1 hmemW
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact lemma117_diagQ_comm hYc k (g : Q) (hDY g.2) (d : Q) hdq
  have hπD_bot : πD.ker = ⊥ := hJtm ↥D hDperf' πD hπD_surj hπD_ker
  have hπD_inj : Function.Injective πD := (MonoidHom.ker_eq_bot_iff πD).1 hπD_bot
  let φD : ↥D ≃* ↥J := MulEquiv.ofBijective πD ⟨hπD_inj, hπD_surj⟩
  refine ⟨D.subtype.comp φD.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : φD.symm a = φD.symm b := Subtype.ext hab
    exact φD.symm.injective h1
  · intro j
    exact hDY (φD.symm j).2
  · intro j hj
    have hdq : ((φD.symm j : ↥D) : Q) ∈ lemma117_diagQ Yq k := hj
    have h1 : pW (Subgroup.inclusion hDW (φD.symm j)) = 1 := by
      have hmem : (Subgroup.inclusion hDW (φD.symm j) : ↥W) ∈ Qn := Subgroup.mem_subgroupOf.2 hdq
      exact (QuotientGroup.eq_one_iff _).2 hmem
    have h2 : πD (φD.symm j) = 1 := by
      show ψe.symm (pW (Subgroup.inclusion hDW (φD.symm j))) = 1
      rw [h1, map_one]
    have h3 : πD (φD.symm j) = j := φD.apply_symm_apply j
    rw [h2] at h3
    rw [← h3, map_one]

end Diag4

section Diag5

variable {Q : Type} [Group Q] [Finite Q]

private theorem lemma117_le_normalizer_of_forall {A T : Subgroup Q} (h : ∀ a ∈ A, ∀ t ∈ T, a * t * a⁻¹ ∈ T) :
    A ≤ Subgroup.normalizer (T : Set Q) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    exact h a ha t ht
  · intro ht
    have := h a⁻¹ (A.inv_mem ha) _ ht
    simpa [mul_assoc] using this

private theorem lemma117_le_normalizer_of_comm {A B : Subgroup Q} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ Subgroup.normalizer (A : Set Q) := by
  have key : ∀ c ∈ B, ∀ a ∈ A, c * a * c⁻¹ = a := by
    intro c hc a ha
    have := h a ha c hc
    rw [← this]
    group
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [key b hb a ha]
    exact ha
  · intro ha
    have h1 := key b⁻¹ (B.inv_mem hb) _ ha
    have e : b⁻¹ * (b * a * b⁻¹) * (b⁻¹)⁻¹ = a := by group
    rw [e] at h1
    rw [h1]
    exact ha

end Diag5

section Diag6

variable {Q : Type} [Group Q] [Finite Q]

private theorem lemma117_diag_main {p q : ℕ} (hp : 0 < p) {Yq : Fin p → Subgroup Q}
    (hYc : ∀ i j, i ≠ j → ⁅Yq i, Yq j⁆ = ⊥)
    {xb : Q} {f : Fin p → Fin p} (hf : Function.Injective f)
    (hxY : ∀ i, (Yq i).map (MulAut.conj xb).toMonoidHom ≤ Yq (f i))
    (hcyc : ∀ i j : Fin p, ∃ t : ℕ, f^[t] i = j)
    {J : Subgroup Q} (hJY : J ≤ ⨆ j, Yq j) (hJc : ∀ j ∈ J, xb * j * xb⁻¹ = j)
    (hJperf : commutator ↥J = ⊤) (hJnt : Nontrivial ↥J) (hJs : IsSimpleGroup ↥J)
    (hJtm : ∀ (E : Type) [Group E] [Finite E], commutator E = ⊤ → ∀ π : E →* ↥J,
        Function.Surjective π → π.ker ≤ Subgroup.center E → π.ker = ⊥)
    (r0 : ℕ) (A0 : Subgroup Q) (hA0J : A0 ≤ J) (hA0 : CFSG.Open.IsElemAbelian q A0)
    (hA0c : Nat.card A0 = q ^ r0)
    (S0 : Subgroup Q) (hS0J : S0 ≤ J) (hS0 : IsPGroup 2 S0) (hS0ne : S0 ≠ ⊥)
    (hA0n : A0 ≤ Subgroup.normalizer (S0 : Set Q)) :
    ∃ E : Subgroup Q, CFSG.Open.IsElemAbelian q E ∧ Nat.card E = q ^ (p * r0) ∧
      ∃ T : Subgroup Q, T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set Q) := by
  classical
  have hJinf : ∀ k, J ⊓ lemma117_diagQ Yq k = ⊥ := fun k =>
    lemma117_diag_inf_eq_bot hYc hf hxY hcyc hJY hJc hJperf hJnt hJs k
  have hι : ∀ k : Fin p, ∃ ι : ↥J →* Q, Function.Injective ι ∧ (∀ j, ι j ∈ Yq k) ∧
      (∀ j, ι j ∈ lemma117_diagQ Yq k → ι j = 1) := fun k => lemma117_diag_iso hYc hJY k hJperf (hJinf k) hJtm
  choose ι hιinj hιmem hιone using hι
  have hA0comm : ∀ x ∈ A0, ∀ y ∈ A0, x * y = y * x := by
    intro x hx y hy
    have := congrArg Subtype.val (hA0.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    exact this
  set A0J : Subgroup ↥J := A0.subgroupOf J with hA0J'
  set A : Fin p → Subgroup Q := fun k => A0J.map (ι k) with hA
  have hAmem : ∀ k, ∀ a ∈ A k, a ∈ Yq k := by
    intro k a ha
    obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.1 ha
    exact hιmem k x
  have hAcomm : ∀ k, ∀ a ∈ A k, ∀ b ∈ A k, a * b = b * a := by
    intro k a ha b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA0comm x (Subgroup.mem_subgroupOf.1 hx) y (Subgroup.mem_subgroupOf.1 hy))
  have hAel : ∀ k, CFSG.Open.IsElemAbelian q (A k) := by
    intro k
    have hmc : IsMulCommutative ↥(A k) := ⟨⟨fun a b => Subtype.ext (hAcomm k a.1 a.2 b.1 b.2)⟩⟩
    refine ⟨hmc, ?_⟩
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    rw [← map_pow]
    have hx1 : x ^ q = 1 := Subtype.ext (hA0.2 _ (Subgroup.mem_subgroupOf.1 hx))
    rw [hx1, map_one]
  have hAcard : ∀ k, Nat.card (A k) = q ^ r0 := by
    intro k
    rw [hA, Subgroup.card_map_of_injective (hιinj k)]
    rw [hA0J', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0J).toEquiv]
    exact hA0c
  have hAinf : ∀ k, A k ⊓ lemma117_diagQ Yq k = ⊥ := by
    intro k
    rw [eq_bot_iff]
    rintro a ⟨ha, hd⟩
    obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.1 ha
    rw [hιone k x hd, Subgroup.mem_bot]
  have hAsub : ∀ k j, j ≠ k → A j ≤ lemma117_diagQ Yq k := by
    intro k j hjk a ha
    exact (le_iSup (fun i : {i : Fin p // i ≠ k} => Yq i.1) ⟨j, hjk⟩) (hAmem j a ha)
  have hind : ∀ F : Finset (Fin p), CFSG.Open.IsElemAbelian q (⨆ j ∈ F, A j) ∧
      Nat.card (⨆ j ∈ F, A j : Subgroup Q) = q ^ (F.card * r0) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      have hbot : (⨆ j ∈ (∅ : Finset (Fin p)), A j : Subgroup Q) = ⊥ := by simp
      have hmc0 : IsMulCommutative (↥(⊥ : Subgroup Q)) := ⟨⟨fun a b => by
        have h1 : (a : Q) = 1 := Subgroup.mem_bot.1 a.2
        have h2 : (b : Q) = 1 := Subgroup.mem_bot.1 b.2
        exact Subtype.ext (by simp only [Subgroup.coe_mul, h1, h2])⟩⟩
      rw [hbot]
      refine ⟨⟨hmc0, fun x hx => ?_⟩, by simp⟩
      rw [Subgroup.mem_bot.1 hx]
      simp
    | insert a F haF ih =>
      obtain ⟨hB, hBc⟩ := ih
      rw [Finset.iSup_insert, Finset.card_insert_of_notMem haF]
      have hBle : (⨆ j ∈ F, A j) ≤ lemma117_diagQ Yq a := by
        refine iSup₂_le fun j hj => ?_
        exact hAsub a j (fun h => haF (h ▸ hj))
      have hBn : (⨆ j ∈ F, A j) ≤ Subgroup.normalizer (A a : Set Q) :=
        lemma117_le_normalizer_of_comm (fun x hx y hy => lemma117_diagQ_comm hYc a x (hAmem a x hx) y (hBle hy))
      have hinf : A a ⊓ (⨆ j ∈ F, A j) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx2 : x ∈ A a ⊓ lemma117_diagQ Yq a := ⟨hx.1, hBle hx.2⟩
        rw [hAinf a] at hx2
        exact hx2
      have hcard := card_sup_mul_card_inf_of_le_normalizer hBn
      rw [hinf, Subgroup.card_bot, mul_one, hAcard a, hBc] at hcard
      refine ⟨?_, ?_⟩
      · exact CFSG.Open.IsElemAbelian.sup_of_commute (hAel a) hB
          (fun x hx y hy => lemma117_diagQ_comm hYc a x (hAmem a x hx) y (hBle hy))
      · rw [hcard, ← pow_add]
        congr 1
        ring
  obtain ⟨hEel, hEc⟩ := hind Finset.univ
  set k0 : Fin p := ⟨0, hp⟩ with hk0
  set S0J : Subgroup ↥J := S0.subgroupOf J with hS0J'
  set T : Subgroup Q := S0J.map (ι k0) with hT
  have hTne : T ≠ ⊥ := by
    intro hTb
    apply hS0ne
    rw [eq_bot_iff]
    intro s hs
    have h1 : ι k0 ⟨s, hS0J hs⟩ ∈ T :=
      Subgroup.mem_map.2 ⟨⟨s, hS0J hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    rw [hTb, Subgroup.mem_bot] at h1
    have h2 : (⟨s, hS0J hs⟩ : ↥J) = 1 := hιinj k0 (by rw [h1, map_one])
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h2
  have hTp : IsPGroup 2 T := by
    intro t
    obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.1 t.2
    obtain ⟨n, hn⟩ := hS0 (⟨(x : Q), Subgroup.mem_subgroupOf.1 hx⟩ : ↥S0)
    refine ⟨n, Subtype.ext ?_⟩
    have hn' : (x : Q) ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hx1 : x ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn')
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hxt, ← map_pow, hx1, map_one]
  have hEnorm : (⨆ j ∈ (Finset.univ : Finset (Fin p)), A j) ≤ Subgroup.normalizer (T : Set Q) := by
    refine iSup₂_le fun j _ => ?_
    refine lemma117_le_normalizer_of_forall fun a ha t ht => ?_
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    by_cases hjk : j = k0
    · rw [hjk] at ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
      rw [← map_inv, ← map_mul, ← map_mul]
      refine Subgroup.mem_map.2 ⟨x * s * x⁻¹, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      have hxA := Subgroup.mem_subgroupOf.1 hx
      have hsS := Subgroup.mem_subgroupOf.1 hs
      have := (Subgroup.mem_normalizer_iff.1 (hA0n hxA) (s : Q)).1 hsS
      simpa [mul_assoc] using this
    · have hc : ι k0 s * a = a * ι k0 s :=
        (Subgroup.mem_centralizer_iff.1
          (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hYc j k0 hjk) (hAmem j a ha)))
          (ι k0 s) (hιmem k0 s)
      have e : a * ι k0 s * a⁻¹ = ι k0 s := by
        rw [← hc]
        group
      rw [e]
      exact Subgroup.mem_map.2 ⟨s, hs, rfl⟩
  exact ⟨⨆ j ∈ (Finset.univ : Finset (Fin p)), A j, hEel,
    by rw [hEc, Finset.card_univ, Fintype.card_fin], T, hTne, hTp, hEnorm⟩

end Diag6

section NoDiag



private theorem lemma117_succ_mod_inj {p i j : ℕ} (hi : i < p) (hj : j < p) (h : (i + 1) % p = (j + 1) % p) :
    i = j := by
  rcases Nat.lt_or_ge (i + 1) p with h1 | h1 <;> rcases Nat.lt_or_ge (j + 1) p with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h
    omega
  · have : j + 1 = p := by omega
    rw [Nat.mod_eq_of_lt h1, this, Nat.mod_self] at h
    omega
  · have : i + 1 = p := by omega
    rw [Nat.mod_eq_of_lt h2, this, Nat.mod_self] at h
    omega
  · omega

private theorem lemma117_pow_mod {x : G} {p : ℕ} (hp0 : 0 < p) (hx : x ^ p = 1) (n : ℕ) :
    x ^ n = x ^ (n % p) := by
  conv_lhs => rw [← Nat.mod_add_div n p]
  rw [pow_add, pow_mul, hx, one_pow, mul_one]

end NoDiag

section NoDiag2



private theorem lemma117_no_diag {m p p' : ℕ} {L B' : Subgroup G} {x' : G} {J : Subgroup G}
    (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J) {x : G} (hx : x ^ p = 1)
    (hxx : x ∈ Subgroup.centralizer ({x'} : Set G)) (hJx : x ∈ Subgroup.centralizer (J : Set G))
    (hp3 : 3 ≤ p) (hsix : Subgroup.center ↥J = ⊥ ∧ TrivialMultiplier J) :
    ¬ ∃ Y : Subgroup G, GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) Y ∧
        (∀ i j : ℕ, i < p → j < p → i ≠ j → GLBConj (x ^ i) Y ≠ GLBConj (x ^ j) Y) ∧
        J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y := by
  rintro ⟨Y, hY, hdist, hJY⟩
  classical
  have hq : p'.Prime := hc.cfg.prime
  have hq2 : p' ≠ 2 := hc.cfg.odd
  have hq1 : 1 < p' := hq.one_lt
  haveI : Fact p'.Prime := ⟨hq⟩
  have hp0 : 0 < p := by omega
  have hxC : x ∈ Subgroup.centralizer ({x'} : Set G) := hxx
  set C : Subgroup G := Subgroup.centralizer ({x'} : Set G) with hCdef
  have hpowC : ∀ i : ℕ, x ^ i ∈ C := fun i => C.pow_mem hxC i
  have hYi : ∀ i : ℕ, GLAPComponent p' C (GLBConj (x ^ i) Y) := by
    intro i
    have h := glaPComponent_gLBConj hY (x ^ i)
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hpowC i))] at h
  have hJC : J ≤ C := fun j hj => (hc.cfg.comp.1.1 hj).2
  have hJq : CFSG.Open.IsQuasisimple ↥J := hc.cfg.comp.1.2.2
  obtain ⟨Yq, hYq⟩ : ∃ Yq : Fin p → Subgroup (↥C ⧸ GLAPPrimeCore p' ↥C),
      ∀ i : Fin p, Yq i = barX p' C (GLBConj (x ^ (i : ℕ)) Y) := ⟨_, fun i => rfl⟩
  have hYqc : ∀ i : Fin p, IsComponentOf (Yq i) ⊤ := fun i => by
    rw [hYq]
    exact (hYi i).2.2.1
  have hYc : ∀ i j : Fin p, i ≠ j → ⁅Yq i, Yq j⁆ = ⊥ := by
    intro i j hij
    have hne : Yq i ≠ Yq j := fun h => by
      rw [hYq, hYq] at h
      exact hdist i j i.2 j.2 (fun e => hij (Fin.ext e))
        (CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_uniqueAux (hYi i) (hYi j) h)
    exact CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hYqc i) (hYqc j) hne
  let f : Fin p → Fin p := fun i => ⟨(i.val + 1) % p, Nat.mod_lt _ hp0⟩
  have hf : Function.Injective f := by
    intro i j h
    have h' := congrArg Fin.val h
    exact Fin.ext (lemma117_succ_mod_inj i.2 j.2 h')
  have hcyc : ∀ i j : Fin p, ∃ t : ℕ, f^[t] i = j := by
    intro i j
    refine ⟨j.val + p - i.val, ?_⟩
    have hval : ∀ t : ℕ, (f^[t] i).val = (i.val + t) % p := by
      intro t
      induction t with
      | zero => simp [Nat.mod_eq_of_lt i.2]
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        show ((f^[n] i).val + 1) % p = (i.val + (n + 1)) % p
        rw [ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1
    apply Fin.ext
    rw [hval]
    have : i.val + (j.val + p - i.val) = j.val + p := by have := i.2; omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt j.2]
  let gC : ↥C := ⟨x⁻¹, C.inv_mem hxC⟩
  let xb : ↥C ⧸ GLAPPrimeCore p' ↥C := QuotientGroup.mk' (GLAPPrimeCore p' ↥C) gC
  have hconj : ∀ K : Subgroup G, K ≤ C → ∀ z ∈ barX p' C K,
      MulAut.conj xb z ∈ barX p' C (GLBConj x K) := by
    intro K hKC z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hz
    rw [MulAut.conj_apply]
    have e : xb * QuotientGroup.mk' (GLAPPrimeCore p' ↥C) k * xb⁻¹ =
        QuotientGroup.mk' (GLAPPrimeCore p' ↥C) (gC * k * gC⁻¹) := by
      simp only [xb, map_mul, map_inv]
    rw [e]
    refine Subgroup.mem_map.2 ⟨gC * k * gC⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, mem_gLBConj]
    have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
    have e2 : x * ((gC * k * gC⁻¹ : ↥C) : G) * x⁻¹ = (k : G) := by
      simp only [gC, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e2]
    exact hk'
  have hYq_shift : ∀ i : Fin p, (Yq i).map (MulAut.conj xb).toMonoidHom ≤ Yq (f i) := by
    intro i
    rintro _ ⟨z, hz, rfl⟩
    rw [hYq] at hz
    have hz' := hconj (GLBConj (x ^ (i : ℕ)) Y) (hYi i).1 z hz
    have hG : GLBConj x (GLBConj (x ^ (i : ℕ)) Y) = GLBConj (x ^ ((f i : Fin p) : ℕ)) Y := by
      rw [gLBConj_gLBConj, ← pow_succ, lemma117_pow_mod hp0 hx]
    rw [hYq, ← hG]
    exact hz'
  have hJs : IsSimpleGroup ↥J := by
    have h := hJq.2
    have e := QuotientGroup.congr (Subgroup.center ↥J) ⊥ (MulEquiv.refl ↥J) (by
      change (Subgroup.center ↥J).map (MonoidHom.id ↥J) = ⊥
      rw [Subgroup.map_id, hsix.1])
    exact (MulEquiv.isSimpleGroup_congr (e.trans (QuotientGroup.quotientBot (G := ↥J)))).mp h
  have hJperf : commutator ↥J = ⊤ := hJq.1
  have hJnt0 : Nontrivial ↥J := lemma117_qs_nontrivial hJq
  have hJO : J ⊓ GLAPPrimeCoreOf p' C = ⊥ := by
    have hnorm : ((J ⊓ GLAPPrimeCoreOf p' C).subgroupOf J).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2), ?_⟩
      have hgC : (g : G) ∈ Subgroup.normalizer (GLAPPrimeCoreOf p' C : Set G) :=
        normalizer_le_normalizer_glaPPrimeCoreOf p' C (Subgroup.le_normalizer (hJC g.2))
      exact (Subgroup.mem_normalizer_iff.1 hgC _).1 hn.2
    rcases hJs.eq_bot_or_eq_top_of_normal ((J ⊓ GLAPPrimeCoreOf p' C).subgroupOf J) with hb | ht
    · rw [eq_bot_iff]
      rintro j ⟨hjJ, hjO⟩
      have hmem : (⟨j, hjJ⟩ : ↥J) ∈ (J ⊓ GLAPPrimeCoreOf p' C).subgroupOf J :=
        Subgroup.mem_subgroupOf.2 ⟨hjJ, hjO⟩
      rw [hb, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hmem
    · exfalso
      have hJsub : J ≤ GLAPPrimeCoreOf p' C := by
        intro j hj
        have hmem : (⟨j, hj⟩ : ↥J) ∈ (J ⊓ GLAPPrimeCoreOf p' C).subgroupOf J := by
          rw [ht]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.1 hmem).2
      have hdvd : p' ∣ Nat.card ↥J := by
        have h1 : p' ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := (dvd_mul_left p' p).trans hc.cfg.dvd
        exact h1.trans (Subgroup.card_quotient_dvd_card _)
      exact not_dvd_card_glaPPrimeCoreOf hq C (hdvd.trans (Subgroup.card_dvd_of_le hJsub))
  let ψJ : ↥J →* (↥C ⧸ GLAPPrimeCore p' ↥C) :=
    (QuotientGroup.mk' (GLAPPrimeCore p' ↥C)).comp (Subgroup.inclusion hJC)
  have hψJ_mem : ∀ j : ↥J, ψJ j ∈ barX p' C J := fun j =>
    Subgroup.mem_map.2 ⟨Subgroup.inclusion hJC j, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
  have hψJ_inj : Function.Injective (ψJ.codRestrict (barX p' C J) hψJ_mem) := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have h1 : ψJ j = 1 := congrArg Subtype.val hj
    have h1' : ((Subgroup.inclusion hJC j : ↥C) : ↥C ⧸ GLAPPrimeCore p' ↥C) = 1 := h1
    have h3 : (Subgroup.inclusion hJC j : ↥C) ∈ GLAPPrimeCore p' ↥C :=
      (QuotientGroup.eq_one_iff _).1 h1'
    have h2 : (j : G) ∈ GLAPPrimeCoreOf p' C := Subgroup.mem_map.2 ⟨_, h3, rfl⟩
    have h4 : (j : G) ∈ J ⊓ GLAPPrimeCoreOf p' C := ⟨j.2, h2⟩
    rw [hJO, Subgroup.mem_bot] at h4
    exact Subtype.ext h4
  have hψJ_surj : Function.Surjective (ψJ.codRestrict (barX p' C J) hψJ_mem) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨(k : G), Subgroup.mem_subgroupOf.1 hk⟩, rfl⟩
  let ψJe : ↥J ≃* ↥(barX p' C J) :=
    MulEquiv.ofBijective (ψJ.codRestrict (barX p' C J) hψJ_mem) ⟨hψJ_inj, hψJ_surj⟩
  have hJs' : IsSimpleGroup ↥(barX p' C J) := (MulEquiv.isSimpleGroup_congr ψJe).mp hJs
  have hJperf' : commutator ↥(barX p' C J) = ⊤ := by
    have hsurjψ : Function.Surjective ψJe.toMonoidHom := ψJe.surjective
    have hmap : (commutator ↥J).map ψJe.toMonoidHom = commutator ↥(barX p' C J) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective ψJe.toMonoidHom hsurjψ]
    rw [← hmap, hJperf, Subgroup.map_top_of_surjective ψJe.toMonoidHom hsurjψ]
  have hJnt' : Nontrivial ↥(barX p' C J) := by
    haveI := hJnt0
    exact ψJe.symm.toEquiv.nontrivial
  have hJtm' : ∀ (E : Type) [Group E] [Finite E], commutator E = ⊤ →
      ∀ π' : E →* ↥(barX p' C J), Function.Surjective π' →
        π'.ker ≤ Subgroup.center E → π'.ker = ⊥ := by
    intro E _ _ hE π' hπ' hker
    have hsurj'' : Function.Surjective (ψJe.symm.toMonoidHom.comp π') :=
      ψJe.symm.surjective.comp hπ'
    have hker'' : (ψJe.symm.toMonoidHom.comp π').ker ≤ Subgroup.center E := by
      intro e he
      apply hker
      rw [MonoidHom.mem_ker] at he ⊢
      have he' : ψJe.symm (π' e) = 1 := he
      exact (MulEquiv.map_eq_one_iff ψJe.symm).1 he'
    have hbot := hsix.2 E hE _ hsurj'' hker''
    have hinj'' : Function.Injective (ψJe.symm.toMonoidHom.comp π') :=
      (MonoidHom.ker_eq_bot_iff _).1 hbot
    exact (MonoidHom.ker_eq_bot_iff π').2 fun a b hab => hinj'' (by
      show ψJe.symm (π' a) = ψJe.symm (π' b)
      rw [hab])
  have hJc : ∀ j ∈ barX p' C J, xb * j * xb⁻¹ = j := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hj
    have hkJ : (k : G) ∈ J := Subgroup.mem_subgroupOf.1 hk
    have hcomm : (k : G) * x = x * (k : G) := (Subgroup.mem_centralizer_iff.1 hJx) (k : G) hkJ
    have e : gC * k * gC⁻¹ = k := by
      apply Subtype.ext
      simp only [gC, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      calc x⁻¹ * (k : G) * x = x⁻¹ * ((k : G) * x) := by group
        _ = x⁻¹ * (x * (k : G)) := by rw [hcomm]
        _ = (k : G) := by group
    show xb * QuotientGroup.mk' (GLAPPrimeCore p' ↥C) k * xb⁻¹ = QuotientGroup.mk' (GLAPPrimeCore p' ↥C) k
    simp only [xb, ← map_inv, ← map_mul, e]
  have hJY' : barX p' C J ≤ ⨆ i : Fin p, Yq i := by
    have h1 := (barX_mono (X := C) p' hJY).trans
      (lemma117_barX_iSup_le (Cg := C) (fun i : Fin p => GLBConj (x ^ (i : ℕ)) Y) (fun i => (hYi i).1))
    exact h1.trans (iSup_mono fun i => le_of_eq (hYq i).symm)
  obtain ⟨E0, hE0, hE0el, hE0c⟩ := CFSG.SectionRank.exists_pRank hq1 (B' ⊓ J)
  have hE0J : E0 ≤ J := hE0.trans inf_le_right
  have hE0C : E0 ≤ C := hE0J.trans hJC
  have hO_inj : ∀ e : ↥C, e ∈ GLAPPrimeCore p' ↥C → (e : G) ∈ J → e = 1 := by
    intro e he heJ
    have h2 : (e : G) ∈ GLAPPrimeCoreOf p' C := Subgroup.mem_map.2 ⟨e, he, rfl⟩
    have h4 : (e : G) ∈ J ⊓ GLAPPrimeCoreOf p' C := ⟨heJ, h2⟩
    rw [hJO, Subgroup.mem_bot] at h4
    exact Subtype.ext h4
  have hE0comm : ∀ u ∈ E0, ∀ v ∈ E0, u * v = v * u := fun u hu v hv => by
    have := congrArg Subtype.val (hE0el.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    exact this
  set r0 := CFSG.Open.pRank p' (B' ⊓ J) with hr0
  have hA0J : barX p' C E0 ≤ barX p' C J := barX_mono (X := C) p' hE0J
  have hE0B' : E0 ≤ B' := hE0.trans inf_le_left
  have hA0el : CFSG.Open.IsElemAbelian p' (barX p' C E0) := by
    have hmc : IsMulCommutative ↥(barX p' C E0) := by
      refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨e1, he1, h1⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨e2, he2, h2⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← h1, ← h2, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hE0comm _ (Subgroup.mem_subgroupOf.1 he1) _ (Subgroup.mem_subgroupOf.1 he2))
    refine ⟨hmc, ?_⟩
    intro z hz
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hz
    rw [← map_pow]
    have he1 : (e : G) ^ p' = 1 := hE0el.2 _ (Subgroup.mem_subgroupOf.1 he)
    have he2 : e ^ p' = 1 := Subtype.ext he1
    rw [he2, map_one]
  have hA0c : Nat.card (barX p' C E0) = p' ^ r0 := by
    let g : ↥(E0.subgroupOf C) →* (↥C ⧸ GLAPPrimeCore p' ↥C) :=
      (QuotientGroup.mk' (GLAPPrimeCore p' ↥C)).comp (E0.subgroupOf C).subtype
    have hginj : Function.Injective g := by
      rw [injective_iff_map_eq_one]
      intro e he
      have he1 : ((e : ↥C) : ↥C ⧸ GLAPPrimeCore p' ↥C) = 1 := he
      have he2 : (e : ↥C) ∈ GLAPPrimeCore p' ↥C := (QuotientGroup.eq_one_iff _).1 he1
      have h5 : (e : ↥C) = 1 := hO_inj (e : ↥C) he2 (hE0J (Subgroup.mem_subgroupOf.1 e.2))
      exact Subtype.ext h5
    have hmapeq : barX p' C E0 = Subgroup.map g ⊤ := by
      ext z
      constructor
      · intro hz
        obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.1 hz
        exact Subgroup.mem_map.2 ⟨⟨c, hc'⟩, Subgroup.mem_top _, rfl⟩
      · intro hz
        obtain ⟨e, _, rfl⟩ := Subgroup.mem_map.1 hz
        exact Subgroup.mem_map.2 ⟨(e : ↥C), e.2, rfl⟩
    rw [hmapeq, Subgroup.card_map_of_injective hginj, Subgroup.card_top]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0C).toEquiv]
    exact hE0c
  obtain ⟨S, hSJ, hS2, hBN, hBC⟩ := hc.cfg.eight
  have hSC : S ≤ C := hSJ.trans hJC
  have hS0J : barX p' C S ≤ barX p' C J := barX_mono (X := C) p' hSJ
  have hS0_2 : IsPGroup 2 ↥(barX p' C S) := by
    rintro ⟨z, hz⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hz
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    obtain ⟨n, hn⟩ := hS2 (⟨(s : G), hsS⟩ : ↥S)
    refine ⟨n, Subtype.ext ?_⟩
    have hn' : (s : G) ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have hs1 : s ^ 2 ^ n = 1 := Subtype.ext hn'
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hs1, map_one]
  have hSne : S ≠ ⊥ := by
    intro hSb
    have hB'z : B' ≤ Subgroup.zpowers x' := by
      intro b hb
      have hbc : b ∈ Subgroup.centralizer (S : Set G) := by
        rw [hSb]
        intro h hh
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
        rw [hh, one_mul, mul_one]
      have hmem : b ∈ B' ⊓ Subgroup.centralizer (S : Set G) := ⟨hb, hbc⟩
      rw [hBC] at hmem
      exact hmem
    have hxord : orderOf x' = p' := by
      haveI : Fact p'.Prime := ⟨hq⟩
      exact orderOf_eq_prime (hc.cfg.elem.2 x' hc.cfg.mem) hc.cfg.ne_one
    have hcardB : Nat.card B' ≤ p' := by
      have h1 := Subgroup.card_le_of_le hB'z
      rw [Nat.card_zpowers, hxord] at h1
      exact h1
    have hrankB := hc.cfg.rank_B
    rw [hc.e_eq] at hrankB
    have hm4 : 4 ≤ m := hctx.1.four_le
    have h1 : p' ^ 2 ≤ p' ^ m := Nat.pow_le_pow_right hq.pos (by omega)
    have h2 : 2 ≤ p' := hq.two_le
    rw [hrankB] at hcardB
    have h3 : p' ^ 2 ≤ p' := le_trans h1 hcardB
    nlinarith
  have hS0ne : barX p' C S ≠ ⊥ := by
    intro hb
    apply hSne
    rw [eq_bot_iff]
    intro s hs
    have hsC : (s : G) ∈ C := hSC hs
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore p' ↥C) (⟨(s : G), hsC⟩ : ↥C) :
        ↥C ⧸ GLAPPrimeCore p' ↥C) ∈ barX p' C S :=
      Subgroup.mem_map.2 ⟨⟨(s : G), hsC⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    have h1 : (⟨(s : G), hsC⟩ : ↥C) ∈ GLAPPrimeCore p' ↥C := (QuotientGroup.eq_one_iff _).1 hmem
    have h5 : (⟨(s : G), hsC⟩ : ↥C) = 1 := hO_inj _ h1 (hSJ hs)
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h5
  have hA0n : barX p' C E0 ≤ Subgroup.normalizer (barX p' C S : Set (↥C ⧸ GLAPPrimeCore p' ↥C)) := by
    refine lemma117_le_normalizer_of_forall fun z hz t ht => ?_
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    have hsn : (e : G) * (s : G) * (e : G)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.1 (hBN (hE0B' (Subgroup.mem_subgroupOf.1 he)))  (s : G)).1
        (Subgroup.mem_subgroupOf.1 hs)
    have e2 : QuotientGroup.mk' (GLAPPrimeCore p' ↥C) e * QuotientGroup.mk' (GLAPPrimeCore p' ↥C) s *
        (QuotientGroup.mk' (GLAPPrimeCore p' ↥C) e)⁻¹ =
        QuotientGroup.mk' (GLAPPrimeCore p' ↥C) (e * s * e⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e2]
    exact Subgroup.mem_map.2 ⟨e * s * e⁻¹, Subgroup.mem_subgroupOf.2 hsn, rfl⟩
  obtain ⟨E, hEel, hEc, T, hTne, hTp, hEnorm⟩ := lemma117_diag_main hp0 hYc hf hYq_shift hcyc hJY' hJc
    hJperf' hJnt' hJs' hJtm' r0 (barX p' C E0) hA0J hA0el hA0c (barX p' C S) hS0J hS0_2 hS0ne hA0n
  have hnum := CFSG.HardMathSupport.Solomon.Coordinator.i1020_le_glaTwoLocalRank hq hTp hTne hEnorm hEel hEc
  have hle1 := twoLocalRank_quot_le hq hq2 C
  have hle2 := twoLocalRank_le_top hq C
  have hm' : GLATwoLocalRank p' G = m := hc.mu.2.1
  have hr : m ≤ r0 + 2 := by
    have h := hc.cfg.rank_inf
    rw [hc.e_eq] at h
    exact h
  have hm4 : 4 ≤ m := hctx.1.four_le
  have hfin : p * r0 ≤ m := by
    have h := hnum.trans (hle1.trans hle2)
    rw [hm'] at h
    exact h
  have h5 : 3 * r0 ≤ p * r0 := Nat.mul_le_mul_right r0 hp3
  have h6 : 3 * r0 ≤ m := le_trans h5 hfin
  omega

end NoDiag2


theorem no_diag_simple (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J) {x : G} (hx : x ^ p = 1)
    (hxx : x ∈ Subgroup.centralizer ({x'} : Set G)) (hJx : x ∈ Subgroup.centralizer (J : Set G))
    (hp3 : 3 ≤ p) (hsix : Subgroup.center ↥J = ⊥ ∧ TrivialMultiplier J) :
    ¬ ∃ Y : Subgroup G, GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) Y ∧
        (∀ i j : ℕ, i < p → j < p → i ≠ j → GLBConj (x ^ i) Y ≠ GLBConj (x ^ j) Y) ∧
        J ≤ ⨆ i : Fin p, GLBConj (x ^ (i : ℕ)) Y := by
  exact lemma117_no_diag hctx hc hx hxx hJx hp3 hsix

theorem j_unique (hc : Cfg116 G m p L p' B' x' J) {Y Y' : Subgroup G}
    (hY : GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) Y) (hY' : GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) Y')
    (hJY : J ≤ Y) (hJY' : J ≤ Y') : Y = Y' := by
  by_contra hne
  have hp : p'.Prime := hc.cfg.prime
  haveI : Fact p'.Prime := ⟨hp⟩
  have hYY' : Y ≤ centModSubgroup p' Y' := le_centModSubgroup_of_ne hp hY hY' hne
  have hJq : CFSG.Open.IsQuasisimple ↥J := hc.cfg.comp.1.2.2
  have hJN : J ≤ GLAPPrimeCoreOf p' Y' :=
    lemma117_le_of_comm hJY' hJq fun j hj l hl => (mem_centModSubgroup.1 (hYY' (hJY hj))).2 l hl
  have hdvd : Nat.card J ∣ Nat.card (GLAPPrimeCoreOf p' Y') := Subgroup.card_dvd_of_le hJN
  have hcop : ¬ p' ∣ Nat.card J := fun h => not_dvd_card_glaPPrimeCoreOf hp Y' (h.trans hdvd)
  have h1 : p' ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := (dvd_mul_left _ _).trans hc.cfg.dvd
  exact hcop ((h1.trans (Subgroup.card_quotient_dvd_card _)))

private theorem y10xB_qdich_abs {K : Type} [Group K] [Finite K] (R : Subgroup K) [R.Normal]
    (hQ : CFSG.Open.IsQuasisimple (K ⧸ R)) (S : Subgroup K) (hS : IsSubnormal S ⊤) :
    (∀ k : K, ∃ s ∈ S, s⁻¹ * k ∈ R) ∨ (∀ s ∈ S, ∀ k : K, ⁅s, k⁆ ∈ R) := by
  classical
  set π : K →* K ⧸ R := QuotientGroup.mk' R with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hSbar : IsSubnormal (S.map π) ⊤ := by
    have h1 := isSubnormal_map' π hS
    rwa [Subgroup.map_top_of_surjective π hπs] at h1
  by_cases htop : S.map π = ⊤
  · left
    intro k
    have hk : π k ∈ S.map π := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨s, hs, hsk⟩ := Subgroup.mem_map.1 hk
    refine ⟨s, hs, ?_⟩
    have h1 : π (s⁻¹ * k) = 1 := by
      rw [map_mul, map_inv, hsk, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 h1
  · right
    obtain ⟨M, hSM, -, hMne, hMn, -⟩ := isSubnormal_exists_normal hSbar htop
    have hMnorm : M.Normal := by
      have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : M ≤ ⊤)).1 hMn
      exact Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 h1)
    have hcent : S.map π ≤ Subgroup.center (K ⧸ R) :=
      hSM.trans (le_center_of_normal_of_isQuasisimple hQ hMnorm hMne)
    intro s hs k
    have hz : π s ∈ Subgroup.center (K ⧸ R) := hcent (Subgroup.mem_map.2 ⟨s, hs, rfl⟩)
    have hcomm : π s * π k = π k * π s := ((Subgroup.mem_center_iff.1 hz) (π k)).symm
    have hc : ⁅π s, π k⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hcomm
    rw [← map_commutatorElement] at hc
    exact (QuotientGroup.eq_one_iff _).1 hc

private theorem y10xB_qdich {G : Type} [Group G] [Finite G] {L R S : Subgroup G} (hRL : R ≤ L)
    [hRn : (R.subgroupOf L).Normal] (hQ : CFSG.Open.IsQuasisimple (↥L ⧸ R.subgroupOf L))
    (hSL : S ≤ L) (hS : IsSubnormal (S.subgroupOf L) ⊤) :
    (∀ k ∈ L, ∃ s ∈ S, s⁻¹ * k ∈ R) ∨ (∀ s ∈ S, ∀ k ∈ L, ⁅s, k⁆ ∈ R) := by
  rcases y10xB_qdich_abs (R.subgroupOf L) hQ (S.subgroupOf L) hS with h | h
  · left
    intro k hk
    obtain ⟨s, hs, hsk⟩ := h ⟨k, hk⟩
    refine ⟨(s : G), Subgroup.mem_subgroupOf.1 hs, ?_⟩
    have := Subgroup.mem_subgroupOf.1 hsk
    simpa using this
  · right
    intro s hs k hk
    have := h ⟨s, hSL hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨k, hk⟩
    exact Subgroup.mem_subgroupOf.1 this

private theorem y10xB_isSubnormal_of_normal_in {G : Type} [Group G] {T L : Subgroup G}
    (hTL : T ≤ L) (hn : (T.subgroupOf L).Normal) : IsSubnormal T L :=
  IsSubnormal.step hTL hn (IsSubnormal.refl L)

private theorem y10xB_subgroupOf_subnormal {G : Type} [Group G] {T L : Subgroup G}
    (h : IsSubnormal T L) : IsSubnormal (T.subgroupOf L) ⊤ := by
  have h1 := isSubnormal_comap' L.subtype h
  have h2 : (L.comap L.subtype) = ⊤ := by
    ext x
    simp
  rw [h2] at h1
  exact h1

private theorem y10xB_mem_preimBarX {G : Type} [Group G] [Finite G] {p : ℕ} {C K : Subgroup G}
    {y : G} (hyC : y ∈ C) :
    y ∈ preimBarX p C K ↔ QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨y, hyC⟩ ∈ barX p C K := by
  constructor
  · intro hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
    have hz' : z = ⟨y, hyC⟩ := Subtype.ext hzy
    rw [hz'] at hz
    exact hz
  · intro h
    exact Subgroup.mem_map.2 ⟨⟨y, hyC⟩, h, rfl⟩

private theorem y10xB_card_barX_dvd {G : Type} [Group G] [Finite G] (p : ℕ) {C S : Subgroup G}
    (hS : S ≤ C) : Nat.card (barX p C S) ∣ Nat.card S := by
  have h1 : Nat.card (barX p C S) ∣ Nat.card (S.subgroupOf C) := by
    unfold barX
    exact Subgroup.card_map_dvd (S.subgroupOf C) (QuotientGroup.mk' (GLAPPrimeCore p ↥C))
  have h2 : Nat.card (S.subgroupOf C) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  rw [h2] at h1
  exact h1

private theorem y10xB_barX_iSup_le {G : Type} [Group G] [Finite G] {ι : Type} (p : ℕ)
    {C : Subgroup G} (S : ι → Subgroup G) (hS : ∀ i, S i ≤ C) {K : Subgroup G}
    (hK : K ≤ ⨆ i, S i) : barX p C K ≤ ⨆ i, barX p C (S i) := by
  have key : ∀ x ∈ (⨆ i, S i), ∃ hx : x ∈ C,
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hx⟩ ∈ ⨆ i, barX p C (S i) := by
    intro x hx
    refine Subgroup.iSup_induction S
      (C := fun x => ∃ hx : x ∈ C, QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hx⟩ ∈
        ⨆ i, barX p C (S i)) hx ?_ ?_ ?_
    · intro i x hxi
      have hxC : x ∈ C := hS i hxi
      refine ⟨hxC, ?_⟩
      exact (le_iSup (fun i => barX p C (S i)) i) ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.2 hxi, rfl⟩
    · exact ⟨C.one_mem, by
        rw [show (⟨1, C.one_mem⟩ : ↥C) = 1 from rfl, map_one]
        exact Subgroup.one_mem _⟩
    · rintro x y ⟨hxC, hx⟩ ⟨hyC, hy⟩
      refine ⟨C.mul_mem hxC hyC, ?_⟩
      show QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨x, hxC⟩ * ⟨y, hyC⟩) ∈ _
      rw [map_mul]
      exact Subgroup.mul_mem _ hx hy
  rintro _ ⟨k, hk, rfl⟩
  have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
  obtain ⟨hkC, hmem⟩ := key (k : G) (hK hk')
  have e : (⟨(k : G), hkC⟩ : ↥C) = k := Subtype.ext rfl
  rw [e] at hmem
  exact hmem

private theorem y10xB_dvd_barX {G : Type} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime)
    {C J : Subgroup G} (hJC : J ≤ C) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hpJ : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) (hqJ : q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    q ∣ Nat.card (barX p C J) := by
  classical
  set f : ↥J →* (↥C ⧸ GLAPPrimeCore p ↥C) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (Subgroup.inclusion hJC) with hf
  have hrange : f.range = barX p C J := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hJC j, (Subgroup.mem_subgroupOf).2 j.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨(c : G), (Subgroup.mem_subgroupOf).1 hc⟩, rfl⟩
  have hne : f.ker ≠ ⊤ := by
    intro htop
    have hJO : J ≤ GLAPPrimeCoreOf p C := by
      intro j hj
      have hj1 : (⟨j, hJC hj⟩ : ↥C) ∈ GLAPPrimeCore p ↥C := by
        have hmem : (⟨j, hj⟩ : ↥J) ∈ f.ker := htop ▸ Subgroup.mem_top _
        rw [MonoidHom.mem_ker] at hmem
        exact (QuotientGroup.eq_one_iff _).1 hmem
      exact Subgroup.mem_map.2 ⟨_, hj1, rfl⟩
    have h1 : Nat.card J ∣ Nat.card (GLAPPrimeCoreOf p C) := Subgroup.card_dvd_of_le hJO
    have h2 : p ∣ Nat.card J := hpJ.trans (Subgroup.card_quotient_dvd_card _)
    exact not_dvd_card_glaPPrimeCoreOf hp C (h2.trans h1)
  have hker : f.ker ≤ Subgroup.center ↥J :=
    le_center_of_normal_of_isQuasisimple hJq (inferInstance) hne
  have hidx : (Subgroup.center ↥J).index ∣ f.ker.index := Subgroup.index_dvd_of_le hker
  have hcard : f.ker.index = Nat.card (barX p C J) := by
    rw [← hrange]
    unfold Subgroup.index
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [← hcard]
  exact (show q ∣ (Subgroup.center ↥J).index from hqJ).trans hidx

theorem l_comp_p (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J) (hp : p.Prime) {L' : Subgroup G}
    (hL' : GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) L') (hJL : J ≤ L')
    (hJp : J ≤ GLAPLayer p (Subgroup.centralizer ({x'} : Set G))) :
    GLAPComponent p (Subgroup.centralizer ({x'} : Set G)) L' := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({x'} : Set G) with hCdef
  have hp' : p'.Prime := hc.cfg.prime
  rcases eq_or_ne p p' with hpp | hpp
  · subst hpp
    exact hL'
  have hJq : CFSG.Open.IsQuasisimple ↥J := hc.cfg.comp.1.2.2
  have hJC : J ≤ C := fun j hj => (hc.cfg.comp.1.1 hj).2
  have hJd : p * p' ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := hc.cfg.dvd
  have hpJ : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := (dvd_mul_right p p').trans hJd
  have hp'J : p' ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := (dvd_mul_left p' p).trans hJd
  have hp'Jc : p' ∣ Nat.card J := hp'J.trans (Subgroup.card_quotient_dvd_card _)
  have hperfJ : ⁅J, J⁆ = J := y10xA_qs_comm_self hJq
  set Rq : Subgroup G := GLAPPrimeCoreOf p' L' with hRq
  have hRqL : Rq ≤ L' := Subgroup.map_subtype_le _
  have hRqC : Rq ≤ GLAPPrimeCoreOf p' C := glaPPrimeCoreOf_le_of_isSubnormal hp' hL'.2.1
  have hRq_cop : ¬ p' ∣ Nat.card Rq := fun h =>
    not_dvd_card_glaPPrimeCoreOf hp' C (h.trans (Subgroup.card_dvd_of_le hRqC))
  have hL'C : L' ≤ C := hL'.1
  have hsnL' : IsSubnormal L' C := hL'.2.1
  have hRq_sub : Rq.subgroupOf L' = GLAPPrimeCore p' ↥L' := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
    · intro hx
      exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  haveI hRqn : (Rq.subgroupOf L').Normal := by
    rw [hRq_sub]
    infer_instance
  have hQ : CFSG.Open.IsQuasisimple (↥L' ⧸ Rq.subgroupOf L') :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hRq_sub.symm) (isQuasisimple_pQuot_of_glaPComponent hp' hL')
  have hqmin : ∀ T : Subgroup G, T ≤ L' → IsSubnormal T C →
      (∀ k ∈ L', ∃ s ∈ T, s⁻¹ * k ∈ Rq) → T = L' := by
    intro T hTL hTC hcov
    by_contra hne
    have hlt : T < L' := lt_of_le_of_ne hTL hne
    have hEq : barX p' C T = barX p' C L' := by
      refine le_antisymm (barX_mono p' hTL) (barX_le_of_forall (hTL.trans hL'C) ?_)
      intro k hk
      obtain ⟨s, hs, hsk⟩ := hcov k hk
      exact ⟨s, hs, hRqC hsk⟩
    exact (hL'.2.2.2 T hlt hTC) hEq
  have hqdich : ∀ S : Subgroup G, S ≤ L' → IsSubnormal (S.subgroupOf L') ⊤ →
      (∀ k ∈ L', ∃ s ∈ S, s⁻¹ * k ∈ Rq) ∨ (∀ s ∈ S, ∀ k ∈ L', ⁅s, k⁆ ∈ Rq) :=
    fun S hSL hS => y10xB_qdich hRqL hQ hSL hS
  have hsubC_of_normal : ∀ T : Subgroup G, T ≤ L' → (T.subgroupOf L').Normal → IsSubnormal T C :=
    fun T hTL hTn => isSubnormal_trans' (y10xB_isSubnormal_of_normal_in hTL hTn) hsnL'
  have hT1 : L' ≤ GLAPLayer p C := by
    obtain ⟨T₁, hT₁⟩ : ∃ T₁ : Subgroup G, T₁ = L' ⊓ GLAPLayer p C := ⟨_, rfl⟩
    have hT₁L : T₁ ≤ L' := by rw [hT₁]; exact inf_le_left
    have hT₁lay : T₁ ≤ GLAPLayer p C := by rw [hT₁]; exact inf_le_right
    have hT₁n : (T₁.subgroupOf L').Normal := by
      rw [Subgroup.normal_subgroupOf_iff hT₁L]
      intro h k hh hk
      have hh1 : h ∈ L' ∧ h ∈ GLAPLayer p C := by
        rw [hT₁, Subgroup.mem_inf] at hh
        exact hh
      rw [hT₁, Subgroup.mem_inf]
      refine ⟨L'.mul_mem (L'.mul_mem hk hh1.1) (L'.inv_mem hk), ?_⟩
      exact (Subgroup.mem_normalizer_iff.1 (mem_normalizer_glaPLayer (Subgroup.le_normalizer (hL'C hk))) h).1 hh1.2
    have hT₁sn : IsSubnormal (T₁.subgroupOf L') ⊤ := isSubnormal_of_normal hT₁n
    rcases hqdich T₁ hT₁L hT₁sn with hcov | hcen
    · have hTeq := hqmin T₁ hT₁L (hsubC_of_normal T₁ hT₁L hT₁n) hcov
      intro k hk
      rw [← hTeq] at hk
      exact hT₁lay hk
    · exfalso
      have hJT : J ≤ T₁ := by
        intro j hj
        rw [hT₁, Subgroup.mem_inf]
        exact ⟨hJL hj, hJp hj⟩
      have hcomm : ⁅J, J⁆ ≤ Rq :=
        Subgroup.commutator_le.2 fun j hj j' hj' => hcen j (hJT hj) j' (hJL hj')
      rw [hperfJ] at hcomm
      exact hRq_cop (hp'Jc.trans (Subgroup.card_dvd_of_le hcomm))
  have hcomp : ∀ Y : Subgroup G, GLAPComponent p C Y → IsComponentOf (barX p C Y) ⊤ :=
    fun Y hY => hY.2.2.1
  have hsnQ : IsSubnormal (barX p C L') ⊤ := by
    have h := isSubnormal_barX (C := C) p hsnL'
    rwa [barX_self] at h
  have hF1 : ∀ Y : Subgroup G, GLAPComponent p C Y →
      barX p C Y ≤ barX p C L' ∨ ⁅barX p C Y, barX p C L'⁆ = ⊥ :=
    fun Y hY => CFSG.ComponentClassification.LocalComponents.subnormal_contains_or_commutes _ _
      (hcomp Y hY) hsnQ
  have hcomm2 : ∀ Y Y' : Subgroup G, GLAPComponent p C Y → GLAPComponent p C Y' →
      barX p C Y ≠ barX p C Y' → ⁅barX p C Y, barX p C Y'⁆ = ⊥ :=
    fun Y Y' hY hY' hne => CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
      (hcomp Y hY) (hcomp Y' hY') hne
  have hF2 : barX p C L' ≤ ⨆ Y : {Y : Subgroup G // GLAPComponent p C Y}, barX p C Y.1 := by
    have hlay : L' ≤ ⨆ Y : {Y : Subgroup G // GLAPComponent p C Y}, Y.1 := by
      have e : GLAPLayer p C = ⨆ Y : {Y : Subgroup G // GLAPComponent p C Y}, Y.1 :=
        sSup_eq_iSup' _
      rw [← e]
      exact hT1
    exact y10xB_barX_iSup_le p (fun Y : {Y : Subgroup G // GLAPComponent p C Y} => Y.1)
      (fun Y => Y.2.1) hlay
  obtain ⟨A', hA'⟩ : ∃ A' : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C),
      A' = ⨆ Y : {Y : Subgroup G // GLAPComponent p C Y ∧ barX p C Y ≤ barX p C L'},
        barX p C Y.1 := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C),
      B' = ⨆ Y : {Y : Subgroup G // GLAPComponent p C Y ∧ ¬ barX p C Y ≤ barX p C L'},
        barX p C Y.1 := ⟨_, rfl⟩
  have hA'L : A' ≤ barX p C L' := by
    rw [hA']
    exact iSup_le fun Y => Y.2.2
  have hB'cent : ∀ Y : {Y : Subgroup G // GLAPComponent p C Y ∧ ¬ barX p C Y ≤ barX p C L'},
      barX p C Y.1 ≤ Subgroup.centralizer (barX p C L' : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    fun Y => Subgroup.commutator_eq_bot_iff_le_centralizer.1
      ((hF1 Y.1 Y.2.1).resolve_left Y.2.2)
  have hA'B' : A' ≤ Subgroup.centralizer (B' : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    rw [hA']
    refine iSup_le fun Y => ?_
    have hBY : B' ≤ Subgroup.centralizer ((barX p C Y.1 : Subgroup _) : Set _) := by
      rw [hB']
      refine iSup_le fun Z => ?_
      have hne : barX p C Z.1 ≠ barX p C Y.1 := fun h => Z.2.2 (by rw [h]; exact Y.2.2)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm2 Z.1 Y.1 Z.2.1 Y.2.1 hne)
    exact Subgroup.le_centralizer_iff.2 (fun k hk => hBY hk)
  have hJL' : barX p C J ≤ barX p C L' := barX_mono p hJL
  have hJ'C : barX p C J ≤ Subgroup.centralizer (B' : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    have hBJ : B' ≤ Subgroup.centralizer ((barX p C J : Subgroup _) : Set _) := by
      rw [hB']
      refine iSup_le fun Z => ?_
      have h1 : ⁅barX p C Z.1, barX p C L'⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hB'cent Z)
      have h2 : ⁅barX p C Z.1, barX p C J⁆ ≤ ⁅barX p C Z.1, barX p C L'⁆ :=
        Subgroup.commutator_mono le_rfl hJL'
      rw [h1] at h2
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 h2)
    exact Subgroup.le_centralizer_iff.2 (fun k hk => hBJ hk)
  have hJ'sup : barX p C J ≤ A' ⊔ B' := by
    refine hJL'.trans (hF2.trans (iSup_le fun Y => ?_))
    by_cases hY : barX p C Y.1 ≤ barX p C L'
    · refine le_sup_of_le_left ?_
      rw [hA']
      exact le_iSup (fun Y : {Y : Subgroup G // GLAPComponent p C Y ∧ barX p C Y ≤ barX p C L'} =>
        barX p C Y.1) ⟨Y.1, Y.2, hY⟩
    · refine le_sup_of_le_right ?_
      rw [hB']
      exact le_iSup (fun Y : {Y : Subgroup G // GLAPComponent p C Y ∧ ¬ barX p C Y ≤ barX p C L'} =>
        barX p C Y.1) ⟨Y.1, Y.2, hY⟩
  have hJ'perf : ⁅barX p C J, barX p C J⁆ = barX p C J := barX_perfect p hJC hperfJ
  have hJ'A : barX p C J ≤ A' := le_of_perfect_le_sup_centralizer hA'B' hJ'C hJ'perf hJ'sup
  have hdivJ : p' ∣ Nat.card (barX p C J) := y10xB_dvd_barX hp hJC hJq hpJ hp'J
  have hex : ∃ Y : {Y : Subgroup G // GLAPComponent p C Y ∧ barX p C Y ≤ barX p C L'},
      ¬ barX p C Y.1 ≤ barX p C Rq := by
    by_contra hcon
    have hcon' : ∀ Y : {Y : Subgroup G // GLAPComponent p C Y ∧ barX p C Y ≤ barX p C L'},
        barX p C Y.1 ≤ barX p C Rq := fun Y => by
      by_contra h
      exact hcon ⟨Y, h⟩
    have hA'N : A' ≤ barX p C Rq := by
      rw [hA']
      exact iSup_le fun Y => hcon' Y
    have hJN : barX p C J ≤ barX p C Rq := hJ'A.trans hA'N
    exact hRq_cop ((hdivJ.trans (Subgroup.card_dvd_of_le hJN)).trans
      (y10xB_card_barX_dvd p (hRqL.trans hL'C)))
  obtain ⟨⟨Y0, hY0c, hY0L⟩, hY0N⟩ := hex
  have hnormY : ∀ Y : Subgroup G, GLAPComponent p C Y →
      barX p C Y ≤ Subgroup.normalizer (barX p C Y0 : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    intro Y hY
    by_cases h : barX p C Y = barX p C Y0
    · rw [h]
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm2 Y Y0 hY hY0c h)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hnorm : barX p C L' ≤ Subgroup.normalizer (barX p C Y0 : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    hF2.trans (iSup_le fun Y => hnormY Y.1 Y.2)
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, T = L' ⊓ preimBarX p C Y0 := ⟨_, rfl⟩
  have hTL : T ≤ L' := by
    rw [hT]
    exact inf_le_left
  have hTC : T ≤ C := hTL.trans hL'C
  have hT2mem : ∀ l (hl : l ∈ L'), l ∈ T ↔
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨l, hL'C hl⟩ : ↥C) ∈ barX p C Y0 := by
    intro l hl
    rw [hT, Subgroup.mem_inf]
    exact ⟨fun h => (y10xB_mem_preimBarX (hL'C hl)).1 h.2,
      fun h => ⟨hl, (y10xB_mem_preimBarX (hL'C hl)).2 h⟩⟩
  have hTn : (T.subgroupOf L').Normal := by
    rw [Subgroup.normal_subgroupOf_iff hTL]
    intro t l ht hl
    have ht' : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨t, hTC ht⟩ : ↥C) ∈ barX p C Y0 :=
      (hT2mem t (hTL ht)).1 ht
    have hlC : l ∈ C := hL'C hl
    have hltC : l * t * l⁻¹ ∈ C := C.mul_mem (C.mul_mem hlC (hTC ht)) (C.inv_mem hlC)
    have hgl : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨l, hlC⟩ : ↥C) ∈ barX p C L' :=
      Subgroup.mem_map.2 ⟨⟨l, hlC⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.1 (hnorm hgl) _).1 ht'
    have heq : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨l * t * l⁻¹, hltC⟩ : ↥C) =
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨l, hlC⟩ : ↥C) *
          QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨t, hTC ht⟩ : ↥C) *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨l, hlC⟩ : ↥C))⁻¹ := by
      have e1 : (⟨l * t * l⁻¹, hltC⟩ : ↥C) =
          (⟨l, hlC⟩ : ↥C) * (⟨t, hTC ht⟩ : ↥C) * (⟨l, hlC⟩ : ↥C)⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv]
    rw [← heq] at hconj
    exact (hT2mem _ (L'.mul_mem (L'.mul_mem hl (hTL ht)) (L'.inv_mem hl))).2 hconj
  have hbarT : barX p C T = barX p C Y0 := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      have hcT : (c : G) ∈ T := Subgroup.mem_subgroupOf.1 hc
      exact (hT2mem (c : G) (hTL hcT)).1 hcT
    · intro a ha
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 (hY0L ha)
      have hcL : (c : G) ∈ L' := Subgroup.mem_subgroupOf.1 hc
      have hcT : (c : G) ∈ T := (hT2mem (c : G) hcL).2 ha
      exact Subgroup.mem_map.2 ⟨⟨c, hTC hcT⟩, Subgroup.mem_subgroupOf.2 hcT, rfl⟩
  have hTsubC : IsSubnormal T C := hsubC_of_normal T hTL hTn
  have hEq : barX p C L' = barX p C Y0 := by
    rcases hqdich T hTL (isSubnormal_of_normal hTn) with hcov | hcen
    · rw [← hqmin T hTL hTsubC hcov]
      exact hbarT
    · exfalso
      have hcomm_sub : ⁅T, L'⁆ ≤ Rq := Subgroup.commutator_le.2 hcen
      have hbarcomm : ⁅barX p C T, barX p C L'⁆ ≤ barX p C Rq := by
        rw [← barX_commutator p hTC hL'C]
        exact barX_mono p hcomm_sub
      have hY0comm : ⁅barX p C Y0, barX p C Y0⁆ ≤ barX p C Rq := by
        rw [← hbarT]
        exact (Subgroup.commutator_mono le_rfl (by rw [hbarT]; exact hY0L)).trans hbarcomm
      have hself : barX p C Y0 ≤ barX p C Rq := by
        calc barX p C Y0 = ⁅barX p C Y0, barX p C Y0⁆ :=
              (barX_perfect_of_glaPComponent hY0c).symm
          _ ≤ barX p C Rq := hY0comm
      exact hY0N hself
  have hmin : ∀ T' : Subgroup G, T' < L' → IsSubnormal T' C → barX p C T' ≠ barX p C L' := by
    intro T' hlt hT'C heq
    have hT'L : T' ≤ L' := hlt.le
    have hT'sub : IsSubnormal (T'.subgroupOf L') ⊤ :=
      y10xB_subgroupOf_subnormal (isSubnormal_of_le_of_le hT'C hT'L hL'C)
    rcases hqdich T' hT'L hT'sub with hcov | hcen
    · exact hlt.ne (hqmin T' hT'L hT'C hcov)
    · have hcomm_sub : ⁅T', L'⁆ ≤ Rq := Subgroup.commutator_le.2 hcen
      have hbarcomm : ⁅barX p C T', barX p C L'⁆ ≤ barX p C Rq := by
        rw [← barX_commutator p (hT'L.trans hL'C) hL'C]
        exact barX_mono p hcomm_sub
      rw [heq] at hbarcomm
      have hJcomm : barX p C J ≤ ⁅barX p C L', barX p C L'⁆ := by
        calc barX p C J = ⁅barX p C J, barX p C J⁆ := (barX_perfect p hJC hperfJ).symm
          _ ≤ ⁅barX p C L', barX p C L'⁆ := Subgroup.commutator_mono hJL' hJL'
      have hJN : barX p C J ≤ barX p C Rq := hJcomm.trans hbarcomm
      exact hRq_cop ((hdivJ.trans (Subgroup.card_dvd_of_le hJN)).trans
        (y10xB_card_barX_dvd p (hRqL.trans hL'C)))
  refine ⟨hL'C, hsnL', ?_, hmin⟩
  show IsComponentOf (barX p C L') ⊤
  rw [hEq]
  exact hcomp Y0 hY0c

theorem x_mem_normalizer {r : ℕ} {x x' : G} {J L' : Subgroup G} (hxx : x ∈ Subgroup.centralizer ({x'} : Set G))
    (hJx : x ∈ Subgroup.normalizer (J : Set G)) (hL' : GLAPComponent r (Subgroup.centralizer ({x'} : Set G)) L')
    (hJL : J ≤ L')
    (huniq : ∀ Y : Subgroup G, GLAPComponent r (Subgroup.centralizer ({x'} : Set G)) Y → J ≤ Y → Y = L') :
    x ∈ Subgroup.normalizer (L' : Set G) := by
  have hc := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL' x
  rw [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hxx)] at hc
  have hJ : GLBConj x J = J := gLBConj_eq_of_mem_normalizer hJx
  have hle : J ≤ GLBConj x L' := by
    calc J = GLBConj x J := hJ.symm
      _ ≤ GLBConj x L' := Subgroup.map_mono hJL
  exact mem_normalizer_iff_gLBConj_eq.2 (huniq _ hc hle)

private theorem y10xC_outer_solvable (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hctx : ThmACtx G m)
    {K : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥K) (hKtop : K ≠ ⊤) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) := by
  classical
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have hcat : CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.KCore.KProperNonab.catalogue_of_surjective y10x_isCatalog_iso hctx.1.kProper K hKtop hnonab
      (QuotientGroup.mk' (Subgroup.center ↥K)) (QuotientGroup.mk'_surjective _)
  haveI hcenter := hSch _ inferInstance hnonab hcat
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥K

private theorem y10xC_inner_of_perfect {K Y : Subgroup G} (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    [Group.IsPerfect ↥Y]
    (hO : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K))
    {y : G} (hy : y ∈ Y) :
    ∃ ℓ ∈ K, ∀ k ∈ K, y * k * y⁻¹ = ℓ * k * ℓ⁻¹ := by
  let act : ↥Y →* MulAut ↥K :=
    (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hYK)
  obtain ⟨ℓ, hℓ⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner act ⟨y, hy⟩
  refine ⟨ℓ, ℓ.2, fun k hk => ?_⟩
  have := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : G)) hℓ
  simpa [act, MulAut.conj_apply] using this

private theorem y10xC_normalizer_le_centralizer {T : Subgroup G} {p : ℕ} [hp : Fact p.Prime]
    {x : G} (hxT : x ∈ T) (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxc : ∀ t ∈ T, t * x = x * t)
    (P : Sylow p ↥T) [IsCyclic ↥(P : Subgroup ↥T)] :
    Subgroup.normalizer ((P : Subgroup ↥T) : Set ↥T) ≤
      Subgroup.centralizer ((P : Subgroup ↥T) : Set ↥T) := by
  classical
  set S : Subgroup ↥T := (P : Subgroup ↥T) with hSdef
  set xT : ↥T := ⟨x, hxT⟩ with hxTdef
  have hxTp : xT ^ p = 1 := Subtype.ext (by simpa [hxTdef] using hxp)
  have hxT1 : xT ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hxcT : ∀ t : ↥T, t * xT = xT * t := fun t => Subtype.ext (hxc t t.2)
  have hord : orderOf xT = p := orderOf_eq_prime hxTp hxT1
  haveI hZn : (Subgroup.zpowers xT).Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hc : g * xT ^ k * g⁻¹ = xT ^ k := by
      have hgx : g * xT * g⁻¹ = xT := by rw [hxcT g, mul_assoc, mul_inv_cancel, mul_one]
      rw [← conj_zpow, hgx]
    rw [hc]
    exact Subgroup.zpow_mem_zpowers xT k
  have hZp : IsPGroup p (Subgroup.zpowers xT) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  have hxS : xT ∈ S := by
    have hle : Subgroup.zpowers xT ≤ P := IsPGroup.le_sylow_of_normal hZp P
    exact hle (Subgroup.mem_zpowers xT)
  obtain ⟨gS, hgS⟩ := IsCyclic.exists_generator (α := ↥S)
  set gT : ↥T := (gS : ↥T) with hgTdef
  have hgTS : gT ∈ S := gS.2
  have hzS : Subgroup.zpowers gT = S := by
    apply le_antisymm
    · exact Subgroup.zpowers_le.2 hgTS
    · intro s hs
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 (hgS ⟨s, hs⟩)
      have : gT ^ z = s := by
        have := congrArg Subtype.val hz
        simpa [hgTdef] using this
      exact Subgroup.mem_zpowers_iff.2 ⟨z, this⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P.isPGroup'
  have hordg : orderOf gT = p ^ k := by
    rw [← Nat.card_zpowers, hzS]
    exact hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hxT1
    have h1 : orderOf gT = 1 := by rw [hordg, pow_zero]
    have h2 : gT = 1 := orderOf_eq_one_iff.1 h1
    have h3 : S = ⊥ := by
      rw [← hzS, h2, Subgroup.zpowers_one_eq_bot]
    have : xT ∈ (⊥ : Subgroup ↥T) := h3 ▸ hxS
    exact Subgroup.mem_bot.1 this
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hsS : s ∈ S := hs
  have hSab : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    intro a ha b hb
    have ha' : a ∈ Subgroup.zpowers gT := by rw [hzS]; exact ha
    have hb' : b ∈ Subgroup.zpowers gT := by rw [hzS]; exact hb
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
    obtain ⟨w, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
    exact ((Commute.refl gT).zpow_left z).zpow_right w
  have hnS : ∀ a ∈ S, n * a * n⁻¹ ∈ S := fun a ha => (Subgroup.mem_normalizer_iff.1 hn a).1 ha
  have hc1 : n * gT * n⁻¹ ∈ Subgroup.zpowers gT := by rw [hzS]; exact hnS gT hgTS
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1 hc1
  have hconj : ∀ j : ℕ, n ^ j * gT * (n ^ j)⁻¹ = gT ^ (t ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show n ^ (j + 1) * gT * (n ^ (j + 1))⁻¹ = n * (n ^ j * gT * (n ^ j)⁻¹) * n⁻¹ by group,
        ih, ← conj_zpow, ← ht, ← zpow_mul]
      congr 1
      ring
  have hxS' : xT ∈ Subgroup.zpowers gT := by rw [hzS]; exact hxS
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hxS'
  have hxfix : n * xT * n⁻¹ = xT := by rw [hxcT n, mul_assoc, mul_inv_cancel, mul_one]
  have hxt : xT ^ t = xT := by
    have h1 : n * xT * n⁻¹ = (n * gT * n⁻¹) ^ a := by rw [← ha, ← conj_zpow]
    rw [hxfix, ← ht] at h1
    have h2 : (gT ^ t) ^ a = (gT ^ a) ^ t := by rw [← zpow_mul, ← zpow_mul, mul_comm]
    rw [h2, ha] at h1
    exact h1.symm
  have hpt : (p : ℤ) ∣ t - 1 := by
    have h3 : xT ^ (t - 1) = 1 := by rw [zpow_sub_one, hxt, mul_inv_cancel]
    have h4 := orderOf_dvd_iff_zpow_eq_one.2 h3
    rw [hord] at h4
    exact_mod_cast h4
  have hdvd : (orderOf gT : ℤ) ∣ t ^ (p ^ (k - 1)) - 1 := by
    have h5 := dvd_sub_pow_of_dvd_sub (R := ℤ) hpt (k - 1)
    rw [one_pow, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk0)] at h5
    rw [hordg]
    push_cast
    exact h5
  set e : ℕ := p ^ (k - 1) with he
  have hfix : n ^ e * gT * (n ^ e)⁻¹ = gT := by
    rw [hconj e]
    have h6 := orderOf_dvd_iff_zpow_eq_one.1 hdvd
    have h7 : gT ^ (t ^ e) = gT ^ (t ^ e - 1) * gT := by
      rw [← zpow_add_one]
      congr 1
      ring
    rw [h7, h6, one_mul]
  have hAg : Commute (n ^ e) gT := by
    have h := hfix
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  have hAS : ∀ a ∈ S, Commute (n ^ e) a := by
    intro a ha
    have ha' : a ∈ Subgroup.zpowers gT := by rw [hzS]; exact ha
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
    exact hAg.zpow_right z
  have hBS : n ^ (S.relIndex (Subgroup.normalizer ((S : Subgroup ↥T) : Set ↥T))) ∈ S := by
    have h := Subgroup.pow_index_mem (S.subgroupOf (Subgroup.normalizer ((S : Subgroup ↥T) : Set ↥T)))
      (⟨n, hn⟩ : ↥(Subgroup.normalizer ((S : Subgroup ↥T) : Set ↥T)))
    rw [Subgroup.mem_subgroupOf] at h
    show n ^ (S.subgroupOf (Subgroup.normalizer ((S : Subgroup ↥T) : Set ↥T))).index ∈ S
    simpa using h
  have hBS' : ∀ a ∈ S, Commute (n ^ (S.relIndex (Subgroup.normalizer ((S : Subgroup ↥T) : Set ↥T)))) a :=
    fun a ha => hSab _ hBS a ha
  have hcopr : Nat.Coprime p (S.relIndex (Subgroup.normalizer ((S : Subgroup ↥T) : Set ↥T))) := by
    have hSN : S ≤ Subgroup.normalizer ((S : Subgroup ↥T) : Set ↥T) := Subgroup.le_normalizer
    have hdv : S.relIndex (Subgroup.normalizer ((S : Subgroup ↥T) : Set ↥T)) ∣ S.index :=
      ⟨(Subgroup.normalizer ((S : Subgroup ↥T) : Set ↥T)).index, (Subgroup.relIndex_mul_index hSN).symm⟩
    have hnd : ¬ p ∣ S.relIndex (Subgroup.normalizer ((S : Subgroup ↥T) : Set ↥T)) :=
      fun h => P.not_dvd_index (h.trans hdv)
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hnd
  have hcop : Nat.Coprime (p ^ (k - 1))
      (S.relIndex (Subgroup.normalizer ((S : Subgroup ↥T) : Set ↥T))) :=
    Nat.Coprime.pow_left _ hcopr
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  set idx := S.relIndex (Subgroup.normalizer ((S : Subgroup ↥T) : Set ↥T)) with hidx
  have hdecomp : (n ^ e) ^ u * (n ^ idx) ^ v = n := by
    rw [← zpow_natCast n e, ← zpow_mul, ← zpow_natCast n idx, ← zpow_mul, ← zpow_add]
    have hEq : (e : ℤ) * u + (idx : ℤ) * v = 1 := by
      rw [he]
      have := huv
      push_cast at this ⊢
      linarith
    rw [hEq, zpow_one]
  have hcomm : Commute ((n ^ e) ^ u * (n ^ idx) ^ v) s :=
    ((hAS s hsS).zpow_left u).mul_left ((hBS' s hsS).zpow_left v)
  have key := hcomm.symm.eq
  rwa [hdecomp] at key

private theorem y10xC_normal_complement {T : Subgroup G} {p : ℕ} [hp : Fact p.Prime] {x : G}
    (hxT : x ∈ T) (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxc : ∀ t ∈ T, t * x = x * t)
    (hcyc : ∀ S : Subgroup G, S ≤ T → IsPGroup p S → IsCyclic S) :
    ∃ K : Subgroup G, K ≤ T ∧ (∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K) ∧ ¬ p ∣ Nat.card K ∧
      ∀ t ∈ T, ∃ b : ℕ, t ^ (p ^ b) ∈ K := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow p ↥T) := inferInstance
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P.isPGroup'
  have hPc : IsCyclic ↥(P : Subgroup ↥T) := by
    have hmapP : (P : Subgroup ↥T).map T.subtype ≤ T := Subgroup.map_subtype_le _
    have hPpm : IsPGroup p ((P : Subgroup ↥T).map T.subtype) := by
      refine IsPGroup.of_card (n := k) ?_
      rw [Subgroup.card_map_of_injective T.subtype_injective]
      exact hk
    have hcy := hcyc _ hmapP hPpm
    let e := (P : Subgroup ↥T).equivMapOfInjective T.subtype T.subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hnorm := y10xC_normalizer_le_centralizer hxT hx1 hxp hxc P
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hnorm
  have hnd := MonoidHom.not_dvd_card_ker_transferSylow P hnorm
  set K0 := (MonoidHom.transferSylow P hnorm).ker with hK0
  haveI hK0n : K0.Normal := MonoidHom.normal_ker _
  refine ⟨K0.map T.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro t ht k hk'
    obtain ⟨k0, hk0, rfl⟩ := Subgroup.mem_map.1 hk'
    refine Subgroup.mem_map.2 ⟨(⟨t, ht⟩ : ↥T) * k0 * (⟨t, ht⟩ : ↥T)⁻¹, hK0n.conj_mem k0 hk0 _, ?_⟩
    simp
  · rw [Subgroup.card_map_of_injective T.subtype_injective]
    exact hnd
  · intro t ht
    have hidx : Nat.card (↥T ⧸ K0) = p ^ k := by
      rw [← Subgroup.index_eq_card, hcomp.symm.index_eq_card, hk]
    have hquot : IsPGroup p (↥T ⧸ K0) := IsPGroup.of_card hidx
    obtain ⟨b, hb⟩ := hquot (QuotientGroup.mk (⟨t, ht⟩ : ↥T))
    refine ⟨b, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hb
    exact Subgroup.mem_map.2 ⟨_, hb, by simp⟩

def y10xC_prod (A B : Subgroup G) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Subgroup G where
  carrier := {g | ∃ a ∈ A, ∃ b ∈ B, a * b = g}
  mul_mem' := by
    rintro _ _ ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
    refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
    calc a1 * a2 * (b1 * b2) = a1 * (a2 * b1) * b2 := by group
      _ = a1 * (b1 * a2) * b2 := by rw [hAB a2 ha2 b1 hb1]
      _ = a1 * b1 * (a2 * b2) := by group
  one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
      _ = (a * b)⁻¹ := by rw [hAB a ha b hb]

private theorem y10xC_perfect_pgroup_trivial {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H]
    [Group.IsPerfect H] (hH : IsPGroup p H) : Subsingleton H := by
  by_contra hnt
  have hnt' : Nontrivial H := not_subsingleton_iff_nontrivial.1 hnt
  haveI : Group.IsNilpotent H := hH.isNilpotent
  exact Group.IsPerfect.not_isSolvable (G := H) inferInstance

private theorem y10xC_ppp_of_gen {p : ℕ} [hp : Fact p.Prime] {Y : Subgroup G}
    (hgen : Subgroup.closure {g : G | g ∈ Y ∧ ∃ k : ℕ, g ^ (p ^ k) = 1} = Y) : PPrimePerfect p Y := by
  intro M hMY hMn hcop
  have hcopQ : Nat.Coprime (Nat.card (↥Y ⧸ M.subgroupOf Y)) p := by
    rw [← Subgroup.index_eq_card]
    exact hcop
  have hpM : ∀ g ∈ Y, (∃ k : ℕ, g ^ (p ^ k) = 1) → g ∈ M := by
    rintro g hg ⟨k, hk⟩
    set q : ↥Y ⧸ M.subgroupOf Y := QuotientGroup.mk (⟨g, hg⟩ : ↥Y) with hqdef
    have hqpow : q ^ (p ^ k) = 1 := by
      rw [hqdef, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      have h1 : (⟨g, hg⟩ : ↥Y) ^ (p ^ k) = 1 := Subtype.ext (by simpa using hk)
      rw [h1]
      exact Subgroup.one_mem _
    have h1 : orderOf q ∣ p ^ k := orderOf_dvd_of_pow_eq_one hqpow
    have h2 : orderOf q ∣ Nat.card (↥Y ⧸ M.subgroupOf Y) := orderOf_dvd_natCard _
    have hc : Nat.Coprime (p ^ k) (Nat.card (↥Y ⧸ M.subgroupOf Y)) :=
      Nat.Coprime.pow_left k hcopQ.symm
    have h4 : orderOf q ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one hc]
      exact Nat.dvd_gcd h1 h2
    have hq1 : q = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
    rw [hqdef, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
    exact hq1
  have hYM : Y ≤ M := by
    rw [← hgen]
    exact Subgroup.closure_le _ |>.2 (fun g hg => hpM g hg.1 hg.2)
  exact le_antisymm hMY hYM

private theorem y10xC_le_prod_of_perfect {p : ℕ} [hp : Fact p.Prime] {L T K Y : Subgroup G}
    (hLT : ∀ a ∈ L, ∀ b ∈ T, a * b = b * a) (hKT : K ≤ T)
    (hKn : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K) (hKtp : ∀ t ∈ T, ∃ b : ℕ, t ^ (p ^ b) ∈ K)
    [Group.IsPerfect ↥Y] (hYR : Y ≤ y10xC_prod L T hLT) :
    Y ≤ y10xC_prod L K (fun a ha b hb => hLT a ha b (hKT hb)) := by
  classical
  set R := y10xC_prod L T hLT with hRdef
  set M := y10xC_prod L K (fun a ha b hb => hLT a ha b (hKT hb)) with hMdef
  have hRp : ∀ r ∈ R, ∃ b : ℕ, r ^ (p ^ b) ∈ M := by
    rintro _ ⟨a, ha, t, ht, rfl⟩
    obtain ⟨b, hb⟩ := hKtp t ht
    refine ⟨b, ?_⟩
    have hc : Commute a t := hLT a ha t ht
    rw [hc.mul_pow]
    exact ⟨a ^ (p ^ b), L.pow_mem ha _, t ^ (p ^ b), hb, rfl⟩
  have hMR : ∀ r ∈ R, ∀ m ∈ M, r * m * r⁻¹ ∈ M := by
    rintro _ ⟨a, ha, t, ht, rfl⟩ _ ⟨a', ha', k, hk, rfl⟩
    have h1 : t * a' = a' * t := (hLT a' ha' t ht).symm
    have h2 : a * (t * k * t⁻¹) = (t * k * t⁻¹) * a := hLT a ha _ (hKT (hKn t ht k hk))
    refine ⟨a * a' * a⁻¹, L.mul_mem (L.mul_mem ha ha') (L.inv_mem ha), t * k * t⁻¹, hKn t ht k hk, ?_⟩
    calc a * a' * a⁻¹ * (t * k * t⁻¹) = a * a' * a⁻¹ * (a * (t * k * t⁻¹) * a⁻¹) := by rw [h2]; group
      _ = a * a' * (t * k * t⁻¹) * a⁻¹ := by group
      _ = a * (a' * t) * k * t⁻¹ * a⁻¹ := by group
      _ = a * (t * a') * k * t⁻¹ * a⁻¹ := by rw [← h1]
      _ = a * t * (a' * k) * (a * t)⁻¹ := by group
  have hMnorm : (M.subgroupOf R).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hMR g g.2 n hn
    simpa using this
  let f : ↥Y →* (↥R ⧸ M.subgroupOf R) :=
    (QuotientGroup.mk' (M.subgroupOf R)).comp (Subgroup.inclusion hYR)
  have hfp : ∀ y : ↥Y, ∃ b : ℕ, (f y) ^ (p ^ b) = 1 := by
    intro y
    obtain ⟨b, hb⟩ := hRp (y : G) (hYR y.2)
    refine ⟨b, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hYR y) : ↥R ⧸ M.subgroupOf R) ^ (p ^ b) = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hb
  have hpg : IsPGroup p ↥f.range := by
    intro h
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 h.2
    obtain ⟨b, hb⟩ := hfp y
    refine ⟨b, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hy]
    exact hb
  haveI : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have hsub := y10xC_perfect_pgroup_trivial hpg
  intro y hy
  have hf1 : f ⟨y, hy⟩ = 1 := by
    have h := Subsingleton.elim (⟨f ⟨y, hy⟩, f.mem_range.2 ⟨_, rfl⟩⟩ : ↥f.range) 1
    exact congrArg Subtype.val h
  have h1 : (QuotientGroup.mk (Subgroup.inclusion hYR ⟨y, hy⟩) : ↥R ⧸ M.subgroupOf R) = 1 := hf1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa using h1

private theorem y10xC_le_of_prod {p : ℕ} [hp : Fact p.Prime] {L K Y : Subgroup G}
    (hLK : ∀ a ∈ L, ∀ b ∈ K, a * b = b * a) (hKp : ¬ p ∣ Nat.card K)
    (hMN : ∀ g ∈ y10xC_prod L K hLK, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hYM : Y ≤ y10xC_prod L K hLK) (hpp : PPrimePerfect p Y) : Y ≤ L := by
  classical
  set M := y10xC_prod L K hLK with hMdef
  have hpow : ∀ m ∈ M, m ^ Nat.card K ∈ L := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have hc : Commute a b := hLK a ha b hb
    rw [hc.mul_pow]
    have hb1 : b ^ Nat.card K = 1 := by
      have h := pow_card_eq_one' (G := ↥K) (x := ⟨b, hb⟩)
      exact congrArg Subtype.val h
    rw [hb1, mul_one]
    exact L.pow_mem ha _
  haveI hLM : (L.subgroupOf M).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hMN g g.2 n hn
    simpa using this
  let φ : ↥Y →* (↥M ⧸ L.subgroupOf M) :=
    (QuotientGroup.mk' (L.subgroupOf M)).comp (Subgroup.inclusion hYM)
  have hq : ∀ q ∈ φ.range, q ^ Nat.card K = 1 := by
    intro q hq
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hq
    show (QuotientGroup.mk (Subgroup.inclusion hYM y) : ↥M ⧸ L.subgroupOf M) ^ Nat.card K = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hpow (y : G) (hYM y.2)
  have hcopIm : Nat.Coprime p (Nat.card φ.range) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hd
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' p hd
    have h1 := hq (h : ↥M ⧸ L.subgroupOf M) h.2
    have h2 : orderOf (h : ↥M ⧸ L.subgroupOf M) ∣ Nat.card K := orderOf_dvd_of_pow_eq_one h1
    rw [Subgroup.orderOf_coe, hh] at h2
    exact hKp h2
  have hker : (φ.ker.map Y.subtype).subgroupOf Y = φ.ker := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 hz
      have hwz' : w = z := Subtype.ext hwz
      rw [← hwz']
      exact hw
    · intro hz
      exact Subgroup.mem_map.2 ⟨z, hz, rfl⟩
  have hM0n : ((φ.ker.map Y.subtype).subgroupOf Y).Normal := by
    rw [hker]
    exact inferInstance
  have hrel : (φ.ker.map Y.subtype).relIndex Y = Nat.card φ.range := by
    rw [Subgroup.relIndex, hker, Subgroup.index_ker]
  have hM0eq : φ.ker.map Y.subtype = Y :=
    hpp _ (Subgroup.map_subtype_le _) hM0n (by rw [hrel]; exact hcopIm.symm)
  intro y hy
  have hy' : y ∈ φ.ker.map Y.subtype := by rw [hM0eq]; exact hy
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy'
  have hz1 : φ z = 1 := MonoidHom.mem_ker.1 hz
  have h3 : (QuotientGroup.mk (Subgroup.inclusion hYM z) : ↥M ⧸ L.subgroupOf M) = 1 := hz1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  have hzy' : (z : G) = y := hzy
  rw [← hzy']
  simpa using h3

private theorem y10xC_le_L_of_ppp (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hctx : ThmACtx G m)
    (hsf : StageFacts G m) (hR : RQuad G m p B x L) {Y : Subgroup G}
    (hY : Y ≤ Subgroup.centralizer ({x} : Set G)) (hperf : commutator ↥Y = ⊤)
    (hpp : PPrimePerfect p Y) : Y ≤ L := by
  classical
  have hH := rquad_hyp hsf hR
  have hp : p.Prime := hH.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h3, h4o, h4, h5, -, -, -, -, -⟩ := hsf p hR.1
  have hc6 : S6Ctx G p := S6Ctx.of_ctx hctx hR.1 h3 h4o h4 h5
  have hlay : GLAPLayer p (Subgroup.centralizer ({x} : Set G)) = L := sstarMax_layer_eq hc6 hR.2.1
  have hLC : L ≤ Subgroup.centralizer ({x} : Set G) := hH.comp.1
  have hLN : ∀ g ∈ Subgroup.centralizer ({x} : Set G), g ∈ Subgroup.normalizer (L : Set G) := by
    intro g hg
    rw [← hlay]
    exact mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)
  have hxL : ∀ l ∈ L, l * x = x * l := fun l hl =>
    (Subgroup.mem_centralizer_iff.1 (hLC hl) x (Set.mem_singleton x)).symm
  have hx1 : x ≠ 1 := hH.ne_one
  have hxp : x ^ p = 1 := hH.elem.2 x hH.mem
  have hxC : ∀ t ∈ Subgroup.centralizer ({x} : Set G), t * x = x * t :=
    fun t ht => (Subgroup.mem_centralizer_iff.1 ht x (Set.mem_singleton x)).symm
  have hLtop : L ≠ ⊤ := by
    intro hLt
    have hCt : Subgroup.centralizer ({x} : Set G) = ⊤ := top_unique (hLt ▸ hLC)
    have hz : x ∈ Subgroup.center G := by
      refine Subgroup.mem_center_iff.2 fun g => ?_
      have hg : g ∈ Subgroup.centralizer ({x} : Set G) := by rw [hCt]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.1 hg x (Set.mem_singleton x)).symm
    haveI := hctx.1.simple
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
    · exact hx1 (Subgroup.mem_bot.1 (h ▸ hz))
    · obtain ⟨a, b, hab⟩ := hctx.1.nonabelian
      have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm
  have hOut := y10xC_outer_solvable hSch hctx hH.qs hLtop
  haveI : Group.IsPerfect ↥Y := ⟨hperf⟩
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := fun y hy => hLN y (hY hy)
  set T : Subgroup G := Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({x} : Set G) with hTdef
  have hYT : ∀ y ∈ Y, ∃ ℓ ∈ L, ℓ⁻¹ * y ∈ T := by
    intro y hy
    obtain ⟨ℓ, hℓ, hconj⟩ := y10xC_inner_of_perfect hYN hOut hy
    refine ⟨ℓ, hℓ, ?_⟩
    have hgL : ℓ⁻¹ * y ∈ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
      have e1 : y * k = ℓ * k * ℓ⁻¹ * y := by rw [← hconj k hk]; group
      calc k * (ℓ⁻¹ * y) = ℓ⁻¹ * (ℓ * k * ℓ⁻¹ * y) := by group
        _ = ℓ⁻¹ * (y * k) := by rw [e1]
        _ = ℓ⁻¹ * y * k := by group
    have hgx : ℓ⁻¹ * y ∈ Subgroup.centralizer ({x} : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      rw [Set.mem_singleton_iff.1 hh]
      have hℓx : Commute ℓ x := hxL ℓ hℓ
      have hyx : Commute y x := hxC y (hY hy)
      have hcomm : Commute (ℓ⁻¹ * y) x := (hℓx.inv_left).mul_left hyx
      exact hcomm.symm.eq
    exact ⟨hgL, hgx⟩
  have hLT : ∀ a ∈ L, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 hb.1 a ha
  have hYR : Y ≤ y10xC_prod L T hLT := fun y hy => by
    obtain ⟨ℓ, hℓ, ht⟩ := hYT y hy
    exact ⟨ℓ, hℓ, ℓ⁻¹ * y, ht, by group⟩
  have hxT : x ∈ T := by
    refine ⟨Subgroup.mem_centralizer_iff.2 fun l hl => (hxL l hl), ?_⟩
    exact Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]
  have hcycT : ∀ S : Subgroup G, S ≤ T → IsPGroup p S → IsCyclic S := by
    intro S hST hSp
    refine hR.2.1.2 S (fun g hg => ?_) hSp
    have hgC : g ∈ Subgroup.centralizer (L : Set G) := (hST hg).1
    refine ⟨Subgroup.centralizer_le_normalizer (L : Set G) hgC, ?_⟩
    have hbot : (⁅L, Subgroup.zpowers g⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro l hl
      refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      have hcgl : Commute g l := ((Subgroup.mem_centralizer_iff.1 hgC) l hl).symm
      exact (hcgl.zpow_left k).eq
    rw [hbot]
    exact bot_le
  obtain ⟨K, hKT, hKn, hKp, hKtp⟩ :=
    y10xC_normal_complement hxT hx1 hxp (fun t ht => hxC t ht.2) hcycT
  have hLK : ∀ a ∈ L, ∀ b ∈ K, a * b = b * a := fun a ha b hb => hLT a ha b (hKT hb)
  have hYM := y10xC_le_prod_of_perfect hLT hKT hKn hKtp hYR
  have hMN : ∀ g ∈ y10xC_prod L K hLK, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    rintro _ ⟨a, ha, b, hb, rfl⟩ l hl
    have hbl : b * l = l * b := (hLT l hl b (hKT hb)).symm
    have e : a * b * l * (a * b)⁻¹ = a * l * a⁻¹ := by
      calc a * b * l * (a * b)⁻¹ = a * (b * l * b⁻¹) * a⁻¹ := by group
        _ = a * (l * b * b⁻¹) * a⁻¹ := by rw [hbl]
        _ = a * l * a⁻¹ := by group
    rw [e]
    exact L.mul_mem (L.mul_mem ha hl) (L.inv_mem ha)
  exact y10xC_le_of_prod hLK hKp hMN hYM hpp

theorem pPerfect_le_L (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hctx : ThmACtx G m) (hsf : StageFacts G m)
    (hR : RQuad G m p B x L) {Y : Subgroup G} (hY : Y ≤ Subgroup.centralizer ({x} : Set G))
    (hperf : commutator ↥Y = ⊤)
    (hgen : Subgroup.closure {g : G | g ∈ Y ∧ ∃ k : ℕ, g ^ (p ^ k) = 1} = Y) : Y ≤ L := by
  haveI : Fact p.Prime := ⟨(rquad_hyp hsf hR).prime⟩
  exact y10xC_le_L_of_ppp hSch hctx hsf hR hY hperf (y10xC_ppp_of_gen hgen)

theorem j_layer_eq (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hCQ : CentQuasiAt G) (hctx : ThmACtx G m)
    (hsf : StageFacts G m) (hR : RQuad G m p B x L) (hc : Cfg116 G m p L p' B' x' J)
    {L' : Subgroup G} (hL' : GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) L') (hJL : J ≤ L') :
    GLAPLayer p (L' ⊓ Subgroup.centralizer ({x} : Set G)) = J ∧
      GLAPComponent p (L' ⊓ Subgroup.centralizer ({x} : Set G)) J := by
  classical
  have hH := rquad_hyp hsf hR
  have hp : p.Prime := hH.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hH.ne_two
  have hLC : L ≤ Subgroup.centralizer ({x} : Set G) := hH.comp.1
  have hJL0 : J ≤ L := (hc.cfg.comp.1.1).trans inf_le_left
  have hJC : J ≤ Subgroup.centralizer ({x} : Set G) := hJL0.trans hLC
  have hLL' : L' ≤ Subgroup.centralizer ({x'} : Set G) := hL'.1
  have hJD : J ≤ L' ⊓ Subgroup.centralizer ({x} : Set G) := le_inf hJL hJC
  have hJc : IsComponentOf J (Subgroup.centralizer ({x'} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    j_isComponent_cent hsf hR hc
  have hDsub : IsSubnormal (L' ⊓ Subgroup.centralizer ({x} : Set G))
      (Subgroup.centralizer ({x'} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isSubnormal_inf hL'.2.1 _
  have hJsubD : IsSubnormal J (L' ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isSubnormal_of_le_of_le hJc.2.1 hJD (inf_le_inf_right _ hLL')
  have hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := (dvd_mul_right p p').trans hc.cfg.dvd
  have hJq : CFSG.Open.IsQuasisimple ↥J := hc.cfg.comp.1.2.2
  have hJp : GLAPComponent p (L' ⊓ Subgroup.centralizer ({x} : Set G)) J :=
    glaPComponent_of_quasisimple hp hJsubD hJq hdvd
  refine ⟨?_, hJp⟩
  have key : ∀ Y : Subgroup G, GLAPComponent p (L' ⊓ Subgroup.centralizer ({x} : Set G)) Y → Y = J := by
    intro Y hY
    have hYD : Y ≤ L' ⊓ Subgroup.centralizer ({x} : Set G) := hY.1
    have hYC : Y ≤ Subgroup.centralizer ({x} : Set G) := hYD.trans inf_le_right
    have hYL' : Y ≤ Subgroup.centralizer ({x'} : Set G) := (hYD.trans inf_le_left).trans hLL'
    have hYperf : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hY)
    have hcomm : commutator ↥Y = ⊤ := hYperf.commutator_eq_top
    have hpp : PPrimePerfect p Y := pPrimePerfect_of_glaPComponent hY
    have hYLx : Y ≤ L := y10xC_le_L_of_ppp hSch hctx hsf hR hYC hcomm hpp
    have hYH : Y ≤ L ⊓ Subgroup.centralizer ({x'} : Set G) := le_inf hYLx hYL'
    have hHD₀ : L ⊓ Subgroup.centralizer ({x'} : Set G) ≤
        Subgroup.centralizer ({x'} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
      le_inf inf_le_right (inf_le_left.trans hLC)
    have hYD₀ : GLAPComponent p (Subgroup.centralizer ({x'} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) Y :=
      glaPComponent_of_isSubnormal' hp hDsub hY
    have hYH' : GLAPComponent p (L ⊓ Subgroup.centralizer ({x'} : Set G)) Y :=
      glaPComponent_of_le hp hYD₀ hYH hHD₀
    have hxL : x' ∈ L := hc.cfg.le hc.cfg.mem
    have hord : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ orderOf x' = q := by
      haveI : Fact p'.Prime := ⟨hc.cfg.prime⟩
      exact ⟨p', hc.cfg.prime, hc.cfg.odd, orderOf_eq_prime (hc.cfg.elem.2 x' hc.cfg.mem) hc.cfg.ne_one⟩
    have hYq : CFSG.Open.IsQuasisimple ↥Y :=
      hCQ L x' p hp hp2 hH.isChev2 hH.qs hxL hord Y hYH'
    have hYcomp : IsComponentOf Y (L ⊓ Subgroup.centralizer ({x'} : Set G)) := ⟨hYH, hYH'.2.1, hYq⟩
    have hYJ : Y ≤ J := by
      have h1 : Y ≤ GLALayer (L ⊓ Subgroup.centralizer ({x'} : Set G)) := le_sSup hYcomp
      rw [hc.cfg.comp.2] at h1
      exact h1
    have hYsubJ : IsSubnormal Y J := isSubnormal_of_le_of_le hY.2.1 hYJ hJD
    have hYsubtop : IsSubnormal (Y.subgroupOf J) ⊤ := by
      have := isSubnormal_comap' J.subtype hYsubJ
      simpa using this
    have hYcomp' : IsComponentOf (Y.subgroupOf J) ⊤ :=
      ⟨le_top, hYsubtop, CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hYJ).symm hYq⟩
    have htop := eq_top_of_isComponentOf_of_isQuasisimple hJq hYcomp'
    have hJY : J ≤ Y := (Subgroup.subgroupOf_eq_top).1 htop
    exact le_antisymm hYJ hJY
  apply le_antisymm
  · exact sSup_le fun Y hY => (key Y hY).le
  · exact le_sSup (s := {Y : Subgroup G | GLAPComponent p (L' ⊓ Subgroup.centralizer ({x} : Set G)) Y}) hJp

theorem lemma117 (hctx : ThmACtx G m) (hsf : StageFacts G m) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hI25 : Input2_5) (hU5 : U5CaseAt G) (hU6 : U6CaseAt G) (hCQ : CentQuasiAt G) (hR : RQuad G m p B x L)
    (hc : Cfg116 G m p L p' B' x' J) :
    ∃ L' : Subgroup G, Concl117 G p p' B' x' x J L' := by
  have hH := rquad_hyp hsf hR
  have hp : p.Prime := hH.prime
  have hp' : p'.Prime := hc.cfg.prime
  have hm : GLATwoLocalRank p G = m := hH.mu.2.1
  have hm' : GLATwoLocalRank p' G = m := hc.mu.2.1
  have hlayer : ∀ r : ℕ, (r = p ∨ r = p') → J ≤ GLAPLayer r (Subgroup.centralizer ({x'} : Set G)) := by
    intro r hr
    have hrank : GLATwoLocalRank r G = m := by rcases hr with rfl | rfl <;> assumption
    have hrp : r.Prime := by rcases hr with rfl | rfl <;> assumption
    have hr2 : r ≠ 2 := by
      rcases hr with rfl | rfl
      · exact hH.ne_two
      · exact hc.cfg.odd
    have h1 := jbar_cent_R hctx hc hr hrp hr2 hrank
    exact j_le_layer hSch hctx hc hr hrp h1 (j_norm_comps hctx hc hr hrp hr2 hrank)
  have hxx : x ∈ Subgroup.centralizer ({x'} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hH.comp.1 (hc.cfg.le hc.cfg.mem))).symm
  have hJx : x ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjL : j ∈ L := (hc.cfg.comp.1.1 hj).1
    exact Subgroup.mem_centralizer_singleton_iff.1 (hH.comp.1 hjL)
  obtain ⟨hbmax, hess⟩ := bstar_facts hctx hc
  have hxp : x ^ p = 1 := hH.elem.2 x hH.mem
  have hJc := j_isComponent_cent hsf hR hc
  have hJp' := hlayer p' (Or.inr rfl)
  have hJpp := hlayer p (Or.inl rfl)
  have hsingle : ∃ Y : Subgroup G, GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) Y ∧ J ≤ Y := by
    rcases dichotomy hI25 hctx hc hp hxp hxx hJc hJp' hJpp with h | h
    · exact h
    · exfalso
      rcases hc.cfg.six with h6 | h6 | h6
      · have hp3 : 3 ≤ p := by
          have := hp.two_le
          have := hH.ne_two
          omega
        exact no_diag_simple hctx hc hxp hxx hJx hp3 h6 h
      · exact no_diag_SU5 hI25 hU5 hctx hc hp hxp hxx hJc hJp' hJpp h6 h
      · exact no_diag_SU6 hI25 hU6 hctx hc hp hxp hxx hJc hJp' hJpp h6 h
  obtain ⟨L', hL', hJL⟩ := hsingle
  have huniq : ∀ Y : Subgroup G, GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) Y → J ≤ Y → Y = L' :=
    fun Y hY hJY => j_unique hc hY hL' hJY hJL
  have hxn : x ∈ Subgroup.normalizer (L' : Set G) :=
    x_mem_normalizer hxx (Subgroup.centralizer_le_normalizer (J : Set G) hJx) hL' hJL huniq
  obtain ⟨hJlay, hJcomp⟩ := j_layer_eq hSch hCQ hctx hsf hR hc hL' hJL
  exact ⟨L', hL', hJL, huniq, ⟨hbmax, hess, hL'⟩, hxn, ⟨hJlay, hJcomp⟩,
    l_comp_p hctx hc hp hL' hJL hJpp⟩

end S11

end CFSG.LocalAnalysis.GLTheoremA
