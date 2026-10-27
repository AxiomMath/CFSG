module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma96A
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9.L96

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_two_zpowers {u : G} (hu : u ^ 2 = 1) : IsPGroup 2 (Subgroup.zpowers u) := by
  intro g
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]

theorem exists_minimal_Q2 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {T Q : Subgroup G} {z : G}
    (hzT : z ∈ T ⊓ Subgroup.centralizer (T : Set G)) (hz2 : z ^ 2 = 1)
    (hexp : ∀ g ∈ Q, g ^ q = 1) (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hne : (⁅Q, Subgroup.zpowers z⁆ : Subgroup G) ≠ ⊥) :
    ∃ Q₂ : Subgroup G, Q₂ ≤ Q ∧ Q₂ ≠ ⊥ ∧ T ≤ Subgroup.normalizer (Q₂ : Set G) ∧
      (⁅Q₂, Subgroup.zpowers z⁆ : Subgroup G) = Q₂ ∧
      ∀ Q' : Subgroup G, Q' ≤ Q₂ → Q' ≠ ⊥ → T ≤ Subgroup.normalizer (Q' : Set G) →
        (⁅Q', Subgroup.zpowers z⁆ : Subgroup G) = Q' → Q' = Q₂ := by
  classical
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.zpowers_le.2 (hTQ hzT.1))
  have hTz : T ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro t ht
    have : t ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      rw [S3.centralizer_zpowers]
      exact Subgroup.mem_centralizer_iff.2 (fun h hh => by
        rw [Set.mem_singleton_iff] at hh; subst hh
        exact (Subgroup.mem_centralizer_iff.1 hzT.2 t ht).symm)
    exact Subgroup.centralizer_le_normalizer _ this
  haveI : Fact q.Prime := ⟨hq⟩
  have hP : IsPGroup q Q := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers z)) (Nat.card Q) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk, Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hz2)
      (Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2)))
  have hsolv : Group.IsSolvable ↥Q := by
    haveI := hP.isNilpotent
    infer_instance
  have hQ0 : (⁅⁅Q, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ : Subgroup G) =
      ⁅Q, Subgroup.zpowers z⁆ :=
    GL83.commutator_double_eq_self (Subgroup.zpowers z) Q hzN hcop hsolv
  set Q₀ : Subgroup G := ⁅Q, Subgroup.zpowers z⁆ with hQ₀
  have hQ₀le : Q₀ ≤ Q := CFSG.LocalAnalysis.GLTheoremA.commutator_le_left_of_normalizes hzN
  have hQ₀N : T ≤ Subgroup.normalizer (Q₀ : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.le_normalizer_commutator hTQ hTz
  let P : Subgroup G → Prop := fun Q' =>
    Q' ≤ Q ∧ Q' ≠ ⊥ ∧ T ≤ Subgroup.normalizer (Q' : Set G) ∧
      (⁅Q', Subgroup.zpowers z⁆ : Subgroup G) = Q'
  have hP0 : P Q₀ := ⟨hQ₀le, hne, hQ₀N, hQ0⟩
  obtain ⟨Q₂, hQ₂, hmin⟩ := Set.exists_min_image {Q' | P Q'} (fun Q' => Nat.card Q')
    (Set.toFinite _) ⟨Q₀, hP0⟩
  refine ⟨Q₂, hQ₂.1, hQ₂.2.1, hQ₂.2.2.1, hQ₂.2.2.2, fun Q' hle hne' hN' hcomm' => ?_⟩
  have hQ'P : P Q' := ⟨hle.trans hQ₂.1, hne', hN', hcomm'⟩
  exact Subgroup.eq_of_le_of_card_ge hle (hmin Q' hQ'P)

theorem pRank_le_twoLocalRank_of_involution {q : ℕ} (hq : q.Prime) {t : G} (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) {R : Subgroup G} (hR : R ≤ Subgroup.centralizer ({t} : Set G)) :
    CFSG.Open.pRank q R ≤ GLATwoLocalRank q G := by
  obtain ⟨E, hER, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt R
  have hne : Subgroup.zpowers t ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]; exact ht1
  have hES : E ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    rw [← S3.centralizer_zpowers] at hR
    exact (hER.trans hR).trans (Subgroup.centralizer_le_normalizer _)
  have h1 := card_le_pow_glaTwoLocalRank hq hE hne (isPGroup_two_zpowers ht2) hES
  rw [hcard] at h1
  exact (Nat.pow_le_pow_iff_right hq.one_lt).1 h1

theorem exists_central_involution {T : Subgroup G} {n : ℕ} (hT : IsExtraspecialTwo T n) :
    ∃ z ∈ T ⊓ Subgroup.centralizer (T : Set G), z ≠ 1 ∧ z ^ 2 = 1 := by
  have hc : Nat.card (Subgroup.center ↥T) = 2 := hT.1.2.2.2
  have hne : Subgroup.center ↥T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc
    omega
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  refine ⟨((a : ↥T) : G), ⟨(a : ↥T).2, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩, ?_, ?_⟩
  · have := Subgroup.mem_center_iff.1 a.2 ⟨h, hh⟩
    exact congrArg Subtype.val this
  · intro h1
    apply ha
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  · have h2 : a ^ Nat.card (Subgroup.center ↥T) = 1 := pow_card_eq_one'
    rw [hc] at h2
    have := congrArg (fun y : ↥(Subgroup.center ↥T) => ((y : ↥T) : G)) h2
    simpa using this

theorem twoLocalRank_eq_four {B : Subgroup G} (hB : GLAIsBmax 3 B) (hcard : Nat.card B = 3 ^ 4) :
    GLATwoLocalRank 3 G = 4 := by
  have h := hB.2.1
  rw [hcard] at h
  exact (Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num : 2 ≤ 3)) h).symm

theorem inf_core_eq_bot {p : ℕ} {L T : Subgroup G} (hodd : Odd (Nat.card (GLAPPrimeCoreOf p L)))
    (hT : IsPGroup 2 T) : T ⊓ GLAPPrimeCoreOf p L = ⊥ := by
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  have hdisj : Disjoint T (GLAPPrimeCoreOf p L) :=
    Subgroup.disjoint_of_coprime_natCard
      (by rw [hk]; exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd))
  exact hdisj.eq_bot

theorem inf_centralizer_eq_bot {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G}
    (hc : S9Ctx G p) (hC : Contra92 p B x L q Q₁)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p L))) {T : Subgroup G} (hTL : T ≤ L)
    (hT : IsPGroup 2 T) : T ⊓ Subgroup.centralizer (Q₁ : Set G) = ⊥ := by
  have h1 := two_part_le_core hc.ctx.prime hc.ctx.odd hC.setup.cent hTL hT
  have hbot := inf_core_eq_bot (L := L) hodd hT
  rw [eq_bot_iff]
  intro g hg
  have h2 : g ∈ T ⊓ GLAPPrimeCoreOf p L := ⟨hg.1, h1 hg⟩
  rw [hbot] at h2
  exact h2

theorem five_le_pRank (h314 : I314At) {q : ℕ} (hq : q.Prime) {Q R : Subgroup G}
    (hexp : ∀ g ∈ Q, g ^ q = 1)
    (hcl : ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, ⁅a, b⁆ * c = c * ⁅a, b⁆) (hRQ : R ≤ Q)
    (h8 : q ^ 8 * Nat.card ↥(R ⊓ (⁅Q, Q⁆ : Subgroup G)) ≤ Nat.card R) :
    5 ≤ CFSG.Open.pRank q R := by
  have h := h314 G q 8 R (R ⊓ (⁅Q, Q⁆ : Subgroup G)) hq (fun g hg => hexp g (hRQ hg))
    (fun a ha b hb c hc => hcl a (hRQ ha) b (hRQ hb) c (hRQ hc))
    (le_inf (CFSG.LocalAnalysis.GLTheoremA.commutator_self_le R)
      (Subgroup.commutator_mono hRQ hRQ)) inf_le_left h8
  by_contra hlt
  have hlt' := not_le.1 hlt
  have h5 : CFSG.Open.pRank q R + 1 ≤ 5 := by omega
  have := Nat.pow_le_pow_left h5 2
  omega

theorem list107_of_inputs {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G}
    (hc : S9Ctx G p) (hin : I107At G p) (hC : Contra92 p B x L q Q₁)
    (h95 : GLATwoLocalRank q G ≤ GLATwoLocalRank p G) :
    p = 3 ∧ catalogIs (PSimple p L) S9.isList107 := by
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  have hX : CFSG.Open.IsKGroup ↥(S9.cx x) := isKGroup_cx hc hC.h.ne_one
  have hm4 : 4 ≤ GLATwoLocalRank p G := hc.ctx.rank_ge
  refine hin hp hp2 (S9.cx x) L B (GLATwoLocalRank p G - 1) hX hC.h.comp hC.h.chev2 hC.h.bmax.1
    hC.h.norm (by omega) ?_ ?_
  · rw [hC.h.card_inf_centMod hp, hC.h.bmax.2.1, ← pow_succ]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  · have := rank_ineq_ltilde hc hC h95
    omega

theorem card_B_eq_of_aut {q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G} (hc : S9Ctx G 3)
    (hC : Contra92 3 B x L q Q₁) (haut : AutRank96At G)
    (hL : catalogIs (PSimple 3 L) (fun i => S9.isTD4two i ∨ S9.isU3eight i)) :
    Nat.card B = 3 ^ 4 := by
  have hX : CFSG.Open.IsKGroup ↥(S9.cx x) := isKGroup_cx hc hC.h.ne_one
  have h1 := haut (S9.cx x) L B hX hC.h.comp hL hC.h.bmax.1 hC.h.norm
  rw [hC.h.card_inf_centMod hc.ctx.prime] at h1
  have h3 := hC.h.pow_four_le hc
  norm_num at h1 h3 ⊢
  omega

theorem case_D4 {q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G} (hc : S9Ctx G 3)
    (hC : Contra92 3 B x L q Q₁) (h95 : GLATwoLocalRank q G ≤ GLATwoLocalRank 3 G)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 L))) (hrank : Rank2D4At G)
    (hB : Nat.card B = 3 ^ 4) (hL : catalogIs (PSimple 3 L) S9.isD4two) : False := by
  have hX : CFSG.Open.IsKGroup ↥(S9.cx x) := isKGroup_cx hc hC.h.ne_one
  have hm : GLATwoLocalRank 3 G = 4 := twoLocalRank_eq_four hC.h.bmax hB
  have h6 := hrank (S9.cx x) L hX hC.h.comp hodd hL
  have h5 := pRank_L_le_of_odd hc hC h95 hodd
  omega

theorem case_TD4 {q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G} (hc : S9Ctx G 3)
    (hC : Contra92 3 B x L q Q₁) (h95 : GLATwoLocalRank q G ≤ GLATwoLocalRank 3 G)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 L))) (haut : AutRank96At G)
    (hext : ExtraspecialU5D4At G) (hrep : ExtraspecialRepAt) (h314 : I314At)
    (hL : catalogIs (PSimple 3 L) S9.isTD4two) : False := by
  have hq := hC.setup.prime
  have hq2 := hC.setup.ne_two
  have hX : CFSG.Open.IsKGroup ↥(S9.cx x) := isKGroup_cx hc hC.h.ne_one
  have hB := card_B_eq_of_aut hc hC haut (catalogIs_mono (fun i hi => Or.inl hi) hL)
  have hm : GLATwoLocalRank 3 G = 4 := twoLocalRank_eq_four hC.h.bmax hB
  obtain ⟨T, hTL, hT, t, htT, ht2, htZ⟩ := (hext (S9.cx x) L hX hC.h.comp hodd).2 hL
  obtain ⟨z, hzZ, hz1, hz2⟩ := exists_central_involution hT
  have hT2 : IsPGroup 2 T := hT.1.1
  have hfaith := inf_centralizer_eq_bot hc hC hodd hTL hT2
  have hTN : T ≤ Subgroup.normalizer (Q₁ : Set G) :=
    hTL.trans (Subgroup.le_normalizer.trans hC.setup.char)
  have hne : (⁅Q₁, Subgroup.zpowers z⁆ : Subgroup G) ≠ ⊥ := by
    intro h
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have hzC : z ∈ T ⊓ Subgroup.centralizer (Q₁ : Set G) :=
      ⟨hzZ.1, Subgroup.mem_centralizer_iff.2 (fun g hg => by
        have := Subgroup.mem_centralizer_iff.1 (h1 hg) z (Subgroup.mem_zpowers z)
        exact this.symm)⟩
    rw [hfaith, Subgroup.mem_bot] at hzC
    exact hz1 hzC
  obtain ⟨Q₂, hQ₂le, hQ₂ne, hQ₂N, hQ₂eq, hmin⟩ :=
    exists_minimal_Q2 hq hq2 hzZ hz2 hC.setup.exp hTN hne
  have hexp₂ : ∀ g ∈ Q₂, g ^ q = 1 := fun g hg => hC.setup.exp g (hQ₂le hg)
  have hcl₂ : ∀ a ∈ Q₂, ∀ b ∈ Q₂, ∀ c ∈ Q₂, ⁅a, b⁆ * c = c * ⁅a, b⁆ := fun a ha b hb c hc =>
    hC.setup.class_two a (hQ₂le ha) b (hQ₂le hb) c (hQ₂le hc)
  obtain ⟨-, hCt⟩ := hrep G q 4 T Q₂ z hq hq2 hT hzZ hz1 hexp₂ hcl₂ hQ₂N hQ₂ne hQ₂eq hmin
  have h8 := hCt t htT ht2 htZ
  have hR := five_le_pRank h314 hq hexp₂ hcl₂ (R := Q₂ ⊓ Subgroup.centralizer ({t} : Set G))
    inf_le_left (by norm_num at h8; exact h8.symm.le)
  have ht1 : t ≠ 1 := fun h => htZ (h ▸ (T ⊓ Subgroup.centralizer (T : Set G)).one_mem)
  have h5 := pRank_le_twoLocalRank_of_involution hq ht1 ht2
    (R := Q₂ ⊓ Subgroup.centralizer ({t} : Set G)) inf_le_right
  omega

theorem case_U38 {q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G} (hc : S9Ctx G 3)
    (hC : Contra92 3 B x L q Q₁) (h95 : GLATwoLocalRank q G ≤ GLATwoLocalRank 3 G)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 L))) (haut : AutRank96At G)
    (hsyl : SylowU38At G) (hrep : ExtraspecialRepCenterAt) (h314 : I314At)
    (hL : catalogIs (PSimple 3 L) S9.isU3eight) : False := by
  have hq := hC.setup.prime
  have hq2 := hC.setup.ne_two
  have hX : CFSG.Open.IsKGroup ↥(S9.cx x) := isKGroup_cx hc hC.h.ne_one
  have hB := card_B_eq_of_aut hc hC haut (catalogIs_mono (fun i hi => Or.inr hi) hL)
  have hm : GLATwoLocalRank 3 G = 4 := twoLocalRank_eq_four hC.h.bmax hB
  obtain ⟨T, hTL, hT2, hTcard, hZcard, hZsq, hV⟩ := hsyl (S9.cx x) L hX hC.h.comp hodd hL
  have hfaith := inf_centralizer_eq_bot hc hC hodd hTL hT2
  have hTN : T ≤ Subgroup.normalizer (Q₁ : Set G) :=
    hTL.trans (Subgroup.le_normalizer.trans hC.setup.char)
  obtain ⟨h, hhZ, hh1, hbound⟩ := hrep G q T Q₁ hq hq2 hT2 hZcard hZsq hV hC.setup.exp
    hC.setup.class_two hTN hfaith
  have hh2 : h ^ 2 = 1 := hZsq h hhZ
  have h5 := five_le_pRank h314 hq hC.setup.exp hC.setup.class_two
    (R := Q₁ ⊓ Subgroup.centralizer ({h} : Set G)) inf_le_left hbound
  have h6 := pRank_le_twoLocalRank_of_involution hq hh1 hh2
    (R := Q₁ ⊓ Subgroup.centralizer ({h} : Set G)) inf_le_right
  omega

end CFSG.LocalAnalysis.GLTheoremA.S9.L96
