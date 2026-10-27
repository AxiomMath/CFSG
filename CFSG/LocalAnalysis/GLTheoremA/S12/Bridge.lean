module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop127
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def Exc16Label (p : ℕ) (lab : GLALabel) (c : Prop) : Prop :=
  (lab.tag = .triD4 ∧ p ∣ 2 ^ lab.n + 1) ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
    (lab.tag = .E6 ∧ lab.n = 2 ∧ c ∧ p = 5)

theorem not_three_dvd_two_pow_add_one_of_even {n : ℕ} (h : Even n) : ¬ 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := h
  intro hd
  have h1 : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
  rw [h1] at hd
  have h2 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

theorem halfSplit_of_16 {p : ℕ} {lab : GLALabel} {c : Prop} (h : GLAHalfSplit16 p lab c)
    (hne : ¬ Exc16Label p lab c) : GLAHalfSplit p lab c := by
  have h1 : ¬ (lab.tag = .triD4 ∧ p ∣ 2 ^ lab.n + 1) := fun h' => hne (Or.inl h')
  have h2 : lab.tag ≠ .twB2 := fun h' => hne (Or.inr (Or.inl h'))
  have h3 : lab.tag ≠ .twF4 := fun h' => hne (Or.inr (Or.inr (Or.inl h')))
  have h4 : ¬ (lab.tag = .E6 ∧ lab.n = 2 ∧ c ∧ p = 5) := fun h' => hne (Or.inr (Or.inr (Or.inr h')))
  rcases h with hs | hb | hc' | hd | he | hf
  · refine Or.inl ?_
    rcases hs with hs | ⟨hs, -, -, hd⟩ | ⟨hs, hd⟩ | hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl ⟨hs, fun ht => h1 ⟨ht, hd⟩, hd⟩)
    · refine Or.inr (Or.inr (Or.inl ⟨?_, hd⟩))
      rcases hs with hs | hs | hs | hs
      · exact Or.inl hs
      · exact Or.inr hs
      · exact absurd hs h2
      · exact absurd hs h3
    · exact Or.inr (Or.inr (Or.inr hs))
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr (Or.inl hc'))
  · rcases hd with ⟨hA | hE, hn, hc'', hp5⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hA.1, hA.2, hn, hc'', hp5⟩)))
    · exact absurd ⟨hE, hn, hc'', hp5⟩ h4
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hf))))

theorem split16_of_split {p : ℕ} {lab : GLALabel} (h : GLASplit p lab) (h2 : lab.tag ≠ .twB2)
    (h3 : lab.tag ≠ .twF4) : GLASplit16 p lab := by
  rcases h with h | ⟨h, -, hd⟩ | ⟨h, hd⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, h2, h3, hd⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨?_, hd⟩))
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

section Markings

variable {G : Type} [Group G] [Finite G]

theorem splitInnerDiag16_of_canon {p : ℕ} {B L : Subgroup G}
    (hrk : ∀ lab : GLALabel, LabelOf L lab → lab.tag ≠ .twB2 ∧ lab.tag ≠ .twF4)
    (h : SplitInnerDiagMarking p B L) : SplitInnerDiagMarking16 p B L := by
  obtain ⟨hL, lab, hlab, hraw⟩ := h
  have hLab : LabelOf L lab :=
    ⟨hL, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨h2, h3⟩ := hrk lab hLab
  refine ⟨hL, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hsp, hnorm, hind⟩
  exact ⟨hs, hna, θ, split16_of_split hsp h2 h3, hnorm, hind⟩

end Markings

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem card_inf_centMod_of_star (hc : S12Ctx G m p) (hS : IsSStarMax p B x L) :
    Nat.card ↥(B ⊓ centModSubgroup p L) = p := by
  have hp := hc.ctx.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hBm := IsSStarMax.bmax hS
  have hxB := (IsSStarMax.essential hS).1
  have hx1 := (IsSStarMax.essential hS).2.1
  have hcent : CentModEqZpowers p B L x := hc.ctx.stage5.2.1 B x L hS.1
  have : B ⊓ centModSubgroup p L = Subgroup.zpowers x := by
    ext g
    constructor
    · rintro ⟨hgB, hg⟩
      exact (hcent g hgB).1 (centMod_iff.2 hg)
    · intro hg
      have hgB : g ∈ B := (Subgroup.zpowers_le.2 hxB) hg
      exact ⟨hgB, centMod_iff.1 ((hcent g hgB).2 hg)⟩
  rw [this, Nat.card_zpowers]
  exact orderOf_eq_prime (hBm.1.2 x hxB) hx1

theorem rankLabel_of_canon (hc : S12Ctx G m p) (hS : IsSStarMax p B x L) (hsplit : SplitInnerDiagMarking p B L)
    (hrk : RankThreeLabelAt G) : ∀ lab : GLALabel, LabelOf L lab → lab.tag ≠ .twB2 ∧ lab.tag ≠ .twF4 := by
  intro lab hlab
  have hp := hc.ctx.ctx.prime
  have hIM : InnerDiagMarking B L :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨_, h2, h3⟩ => ⟨h2, h3⟩) hsplit
  have hBm := IsSStarMax.bmax hS
  have hm : 4 ≤ m := hc.rank ▸ hc.ctx.ctx.rank_ge
  have hpow : p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B := by
    rw [card_inf_centMod_of_star hc hS, hc.card_B hBm, ← pow_succ]
    exact Nat.pow_le_pow_right hp.pos hm
  obtain ⟨-, h2, h3⟩ := hrk p hp hc.ctx.ctx.odd B L lab hBm.1 hIM hpow hlab
  exact ⟨h2, h3⟩

theorem card_inf_centMod_of_nbr {y : G} {J : Subgroup G} (h : NbrCfg G m p B x L D K y J) :
    Nat.card ↥(B ⊓ centModSubgroup p J) = p := by
  have hp := h.cfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have : B ⊓ centModSubgroup p J = Subgroup.zpowers y := by
    ext g
    constructor
    · rintro ⟨hgB, hg⟩
      exact (h.J_cent g hgB).1 (centMod_iff.2 hg)
    · intro hg
      have hgB : g ∈ B := (Subgroup.zpowers_le.2 h.yB) hg
      exact ⟨hgB, centMod_iff.1 ((h.J_cent g hgB).2 hg)⟩
  rw [this, Nat.card_zpowers]
  exact orderOf_eq_prime (h.bmax.1.2 y h.yB) h.y_ne_one

structure CanonNbrAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  e6four : ∀ (B : Subgroup G) (x : G) (L D K : Subgroup G) (y : G) (J : Subgroup G), IsSStarMax p B x L →
    SplitInnerDiagMarking p B L → GLAStdSub p B x L D K → GLASHat p B y J → GLANeighbor p x y J D K →
    K ≤ J → B ≤ Subgroup.normalizer (J : Set G) → 4 ≤ GLATwoLocalRank p G → InnerDiagMarking B J →
      ∀ lab : GLALabel, LabelOf J lab → ¬ (lab.tag = .E6 ∧ lab.n = 2 ∧ Subgroup.center ↥J = ⊥ ∧ p = 5)
  tri : ∀ (B : Subgroup G) (x : G) (L D K : Subgroup G) (y : G) (J : Subgroup G), IsSStarMax p B x L →
    SplitInnerDiagMarking p B L → GLAStdSub p B x L D K → GLASHat p B y J → GLANeighbor p x y J D K →
    K ≤ J → B ≤ Subgroup.normalizer (J : Set G) → 4 ≤ GLATwoLocalRank p G →
    p = 3 → ∀ lab : GLALabel, LabelOf J lab → lab.tag = .triD4 → Odd lab.n → 3 ≤ lab.n → False

theorem prop122_marking_canon (hc : S12Ctx G m p) (hS : IsSStarMax p B x L) (hsplit : SplitInnerDiagMarking p B L)
    (hrk : RankThreeLabelAt G) (hcan : CanonNbrAt G p) (hin : Inputs122 G p) {y : G} {J : Subgroup G}
    (hnb : GLAIsNeighborOf p B x L y J) :
    B ≤ Subgroup.normalizer (J : Set G) ∧
      GLAMarking J (fun lab _ _ I F θ => GLAHalfSplit p lab (Subgroup.center ↥J = ⊥) ∨
        GLAPrimeField p lab I F (GLAInduces θ fun j j' => (j' : G) = x⁻¹ * j * x)) := by
  obtain ⟨D, K, hnb'⟩ := isNeighborOf_iff.1 hnb
  have hp := hc.ctx.ctx.prime
  have hsplit16 : SplitInnerDiagMarking16 p B L :=
    splitInnerDiag16_of_canon (rankLabel_of_canon hc hS hsplit hrk) hsplit
  have hcfg : Cfg12 G m p B x L D K := ⟨hc, ⟨hS, hsplit16⟩, hnb'.std⟩
  have hnbc : NbrCfg G m p B x L D K y J := ⟨hcfg, hnb'.shat, hnb'.nb⟩
  have hKJ : K ≤ J := by
    rw [← ky_eq_J hnbc hin]
    exact le_closureIn_self K _
  have h122 := prop122 hnbc hin
  refine ⟨h122.norm, ?_⟩
  have hhalf : ∀ lab : GLALabel, LabelOf J lab → GLAHalfSplit p lab (Subgroup.center ↥J = ⊥) →
      GLAMarking J (fun lab' _ _ I F θ => GLAHalfSplit p lab' (Subgroup.center ↥J = ⊥) ∨
        GLAPrimeField p lab' I F (GLAInduces θ fun j j' => (j' : G) = x⁻¹ * j * x)) := by
    intro lab hlab hhs
    refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ (show LabelOf J lab from hlab)
    rintro lab' R _ I F θ rfl
    exact Or.inl hhs
  rcases h122.half with ⟨⟨lab, hlab, hhs⟩, hIM⟩ | ⟨hp3, -, lab, hlab, htag, hhs⟩ | hf
  ·
    have hm : 4 ≤ m := hc.rank ▸ hc.ctx.ctx.rank_ge
    have hpow : p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p J) ≤ Nat.card B := by
      rw [card_inf_centMod_of_nbr hnbc, hc.card_B hnbc.bmax, ← pow_succ]
      exact Nat.pow_le_pow_right hp.pos hm
    obtain ⟨h1, h2, h3⟩ := hrk p hp hc.ctx.ctx.odd B J lab hnbc.bmax.1 hIM hpow hlab
    have hne : ¬ Exc16Label p lab (Subgroup.center ↥J = ⊥) := by
      rintro (⟨htag, -⟩ | htag | htag | he)
      · exact h1 htag
      · exact h2 htag
      · exact h3 htag
      · exact hcan.e6four B x L D K y J hS hsplit hnb'.std hnb'.shat hnb'.nb hKJ h122.norm
          hc.ctx.ctx.rank_ge hIM lab hlab he
    exact hhalf lab hlab (halfSplit_of_16 hhs hne)
  ·
    refine hhalf lab hlab ?_
    rcases htag with htag | htag
    · refine halfSplit_of_16 hhs ?_
      rintro (⟨h1, -⟩ | h1 | h1 | ⟨h1, -⟩) <;> (rw [htag] at h1; exact absurd h1 (by decide))
    · rcases Nat.even_or_odd lab.n with hev | hodd
      · refine halfSplit_of_16 hhs ?_
        rintro (⟨-, hdvd⟩ | h1 | h1 | ⟨h1, -⟩)
        · rw [hp3] at hdvd
          exact not_three_dvd_two_pow_add_one_of_even hev hdvd
        all_goals (rw [htag] at h1; exact absurd h1 (by decide))
      · by_cases hn1 : lab.n = 1
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hn1, hp3⟩)))
        · exact (hcan.tri B x L D K y J hS hsplit hnb'.std hnb'.shat hnb'.nb hKJ h122.norm
            hc.ctx.ctx.rank_ge hp3 lab hlab htag hodd
            (by obtain ⟨k, hk⟩ := hodd; omega)).elim
  · refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ (marking_of_fieldOn hnbc.J_comp h122.qs hf)
    intro lab' R _ I F θ h'
    exact Or.inr h'

theorem odd_canon (h : Cfg12 G m p B x L D K) (hin : Inputs124 G p) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    Odd (Nat.card ↥(⁅K, GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))⁆ : Subgroup G)) :=
  Odd.of_dvd_nat (prop127 h hin hd hd1) (Subgroup.card_dvd_of_le
    (Subgroup.commutator_mono (le_closureIn_self K _) le_rfl))

end S12

end CFSG.LocalAnalysis.GLTheoremA
