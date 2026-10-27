module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMTorDet
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMTorA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMTorB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement MatrixGroups

private lemma commutatorElement_mul_right_of_central {G : Type*} [Group G] {s g h : G}
    (hs : ∀ x : G, Commute s x) : ⁅g, s * h⁆ = ⁅g, h⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h1 : ⁅g, s⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (hs g).symm
  rw [h1, one_mul, (hs ⁅g, h⁆).eq, mul_assoc, mul_inv_cancel, mul_one]

private lemma commute_scalar_inv {d : ℕ} {F : Type} [Field F] (a : Fˣ)
    (x : GL (Fin d) F) : Commute ((Matrix.GeneralLinearGroup.scalar (Fin d) a)⁻¹) x := by
  rw [← map_inv]
  exact Matrix.GeneralLinearGroup.scalar_commute a⁻¹ x

private lemma commute_scalar {d : ℕ} {F : Type} [Field F] (a : Fˣ)
    (x : GL (Fin d) F) : Commute (Matrix.GeneralLinearGroup.scalar (Fin d) a) x :=
  Matrix.GeneralLinearGroup.scalar_commute a x

private theorem dich_rank_aux :
    ∀ d : ℕ, ∀ (p : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2],
      p.Prime → p ≠ 2 → p ∣ Nat.card F - 1 →
      (∀ {G : Subgroup (GL (Fin d) F)},
        LargeEvenScalars (Fin d) F ≤ G → MElemMod p d F G →
        MToral p d F G ∨
          (p ∣ d ∧ (LargeEvenScalars (Fin d) F).relIndex G ≤ p ^ (d / p + 1))) ∧
      (∀ {G : Subgroup (GL (Fin d) F)},
        LargeEvenScalars (Fin d) F ≤ G → MElemMod p d F G →
        (LargeEvenScalars (Fin d) F).relIndex G ≤ p ^ (d - 1)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro p F _ _ _ hp hp2 hpF
    have hdich : ∀ {G : Subgroup (GL (Fin d) F)},
        LargeEvenScalars (Fin d) F ≤ G → MElemMod p d F G →
        MToral p d F G ∨
          (p ∣ d ∧ (LargeEvenScalars (Fin d) F).relIndex G ≤ p ^ (d / p + 1)) := by
      intro G hZG hel
      by_cases hd0 : d = 0
      · subst hd0
        left
        constructor
        · intro g _ h _
          exact Subsingleton.elim _ _
        · intro g _
          exact ⟨1, Subsingleton.elim _ _⟩
      · by_cases htor : MToral p d F G
        · exact Or.inl htor
        · right
          by_cases hA : ∃ h ∈ G, h ^ p = 1 ∧ ∃ g ∈ G, ⁅g, h⁆ ≠ 1
          · obtain ⟨h, hhG, hhp, g, hgG, hζ⟩ := hA
            obtain ⟨hpd, G', hZG', hel', hle⟩ :=
              tor_lemmaA hp hp2 hpF hZG hel hhG hgG hhp hζ
            refine ⟨hpd, ?_⟩
            have hpos : 0 < d := Nat.pos_of_ne_zero hd0
            have hlt : d / p < d := Nat.div_lt_self hpos hp.one_lt
            have hR' : (LargeEvenScalars (Fin (d / p)) F).relIndex G' ≤
                p ^ (d / p - 1) :=
              (ih (d / p) hlt p F hp hp2 hpF).2 hZG' hel'
            have hp_le_d : p ≤ d := Nat.le_of_dvd hpos hpd
            have hdp : 1 ≤ d / p := Nat.div_pos hp_le_d hp.pos
            have harith : p ^ 2 * p ^ (d / p - 1) = p ^ (d / p + 1) := by
              rw [← Nat.pow_add]
              congr 1
              omega
            calc (LargeEvenScalars (Fin d) F).relIndex G
                ≤ p ^ 2 * (LargeEvenScalars (Fin (d / p)) F).relIndex G' := hle
              _ ≤ p ^ 2 * p ^ (d / p - 1) := Nat.mul_le_mul_left _ hR'
              _ = p ^ (d / p + 1) := harith
          · have hrad : ∀ h ∈ G,
                (∃ a : Fˣ, h ^ p = (Matrix.GeneralLinearGroup.scalar (Fin d) a) ^ p) →
                  ∀ g' ∈ G, ⁅g', h⁆ = 1 := by
              intro h hhG ⟨a, ha⟩ g' hg'G
              by_contra hne
              let s : GL (Fin d) F := (Matrix.GeneralLinearGroup.scalar (Fin d) a)⁻¹
              have hs_central : ∀ x : GL (Fin d) F, Commute s x := by
                intro x
                exact commute_scalar_inv a x
              have hs_mem : s ∈ G := hZG ⟨a⁻¹, by simp [s]⟩
              have hs_pow : s ^ p =
                  ((Matrix.GeneralLinearGroup.scalar (Fin d) a) ^ p)⁻¹ := by
                simp [s, inv_pow]
              have hpow : (s * h) ^ p = 1 := by
                rw [(hs_central h).mul_pow p, ha, hs_pow, inv_mul_cancel]
              have hcomm : ⁅g', s * h⁆ = ⁅g', h⁆ :=
                commutatorElement_mul_right_of_central hs_central
              exact hA ⟨s * h, G.mul_mem hs_mem hhG, hpow, g', hg'G, by
                rw [hcomm]
                exact hne⟩
            have hcne : ∃ g ∈ G,
                ∀ a : Fˣ, g ^ p ≠ (Matrix.GeneralLinearGroup.scalar (Fin d) a) ^ p := by
              by_contra hcon
              have hall : ∀ g ∈ G, ∃ a : Fˣ,
                  g ^ p = (Matrix.GeneralLinearGroup.scalar (Fin d) a) ^ p := by
                intro g hg
                by_contra hg'
                exact hcon ⟨g, hg, fun a ha => hg' ⟨a, ha⟩⟩
              apply htor
              constructor
              · intro g hg h hh
                exact commutatorElement_eq_one_iff_mul_comm.mp
                  (hrad h hh (hall h hh) g hg)
              · intro g hg
                obtain ⟨a, ha⟩ := hall g hg
                refine ⟨a⁻¹, ?_⟩
                have hc : Commute (Matrix.GeneralLinearGroup.scalar (Fin d) a⁻¹) g :=
                  commute_scalar a⁻¹ g
                have hsp : (Matrix.GeneralLinearGroup.scalar (Fin d) a⁻¹) ^ p =
                    ((Matrix.GeneralLinearGroup.scalar (Fin d) a) ^ p)⁻¹ := by
                  simp [← map_pow, inv_pow]
                rw [hc.mul_pow p, ha, hsp, inv_mul_cancel]
            obtain ⟨g, hgG, hgc⟩ := hcne
            obtain ⟨hpdB, hleB⟩ := tor_lemmaB hp hp2 hpF hZG hel hgG hgc hrad
            exact ⟨hpdB, hleB.trans (Nat.pow_le_pow_right hp.pos (Nat.le_succ (d / p)))⟩
    have hrank : ∀ {G : Subgroup (GL (Fin d) F)},
        LargeEvenScalars (Fin d) F ≤ G → MElemMod p d F G →
        (LargeEvenScalars (Fin d) F).relIndex G ≤ p ^ (d - 1) := by
      intro G hZG hel
      by_cases hd0 : d = 0
      · subst hd0
        have hGbot : G = ⊥ := by
          ext x
          simp only [Subgroup.mem_bot]
          constructor
          · intro _
            exact Subsingleton.elim x 1
          · intro hx
            rw [hx]
            exact G.one_mem
        rw [hGbot, Subgroup.relIndex_bot_right]
        simp
      · rcases hdich hZG hel with htor | ⟨hpd, hle⟩
        · exact (tor_toral_diag hp hp2 hpF hZG htor).2
        · have hpos : 0 < d := Nat.pos_of_ne_zero hd0
          have hp3 : 3 ≤ p := by
            have := hp.two_le
            omega
          have hp_le_d : p ≤ d := Nat.le_of_dvd hpos hpd
          obtain ⟨k, hk⟩ := hpd
          have hkpos : 0 < k := by
            rcases Nat.eq_zero_or_pos k with hk0 | hkpos
            · rw [hk0, mul_zero] at hk
              omega
            · exact hkpos
          have hkey : d / p + 1 ≤ d - 1 := by
            rw [hk, Nat.mul_div_cancel_left k hp.pos]
            have h1 : 3 * k ≤ p * k := Nat.mul_le_mul_right k hp3
            have h2 : k + 2 ≤ 3 * k := by omega
            have h3 : k + 2 ≤ p * k := le_trans h2 h1
            omega
          exact hle.trans (Nat.pow_le_pow_right hp.pos hkey)
    exact ⟨hdich, hrank⟩

theorem tor_dichotomy {p d : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) {G : Subgroup (GL (Fin d) F)}
    (hZG : LargeEvenScalars (Fin d) F ≤ G) (hel : MElemMod p d F G) :
    MToral p d F G ∨
      (p ∣ d ∧ (LargeEvenScalars (Fin d) F).relIndex G ≤ p ^ (d / p + 1)) :=
  (dich_rank_aux d p F hp hp2 hpF).1 hZG hel

theorem tor_rank_le {p d : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) {G : Subgroup (GL (Fin d) F)}
    (hZG : LargeEvenScalars (Fin d) F ≤ G) (hel : MElemMod p d F G) :
    (LargeEvenScalars (Fin d) F).relIndex G ≤ p ^ (d - 1) :=
  (dich_rank_aux d p F hp hp2 hpF).2 hZG hel

theorem tor_toral_of_rank {p d : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (hpd : p ∣ d) {G : Subgroup (GL (Fin d) F)}
    (hZG : LargeEvenScalars (Fin d) F ≤ G) (hel : MElemMod p d F G)
    (hrank : p ^ max 3 (d - 2) ≤ (LargeEvenScalars (Fin d) F).relIndex G) :
    MToral p d F G := by
  rcases tor_dichotomy hp hp2 hpF hZG hel with h | ⟨-, hle⟩
  · exact h
  · exfalso
    have h1 : p ^ max 3 (d - 2) ≤ p ^ (d / p + 1) := hrank.trans hle
    have h2 : max 3 (d - 2) ≤ d / p + 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    obtain ⟨k, hk⟩ := hpd
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hdk : d / p = k := by
      rw [hk]
      exact Nat.mul_div_cancel_left k hp.pos
    rw [hdk] at h2
    have h3 : 3 ≤ k + 1 := le_trans (le_max_left _ _) h2
    have h4 : d - 2 ≤ k + 1 := le_trans (le_max_right _ _) h2
    have h5 : 3 * k ≤ p * k := Nat.mul_le_mul_right k hp3
    omega

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
