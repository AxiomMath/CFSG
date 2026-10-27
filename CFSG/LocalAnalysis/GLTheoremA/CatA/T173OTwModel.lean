module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitTwistedE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U6Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Split
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.Quasithin.Background.F918D5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.LocalAnalysis.GLTheoremA.S172X CFSG.StandardType

private theorem not_dvd_rk2DiagIndex_of_twE6 {p r n : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ¬ p ∣ rk2DiagIndex (⟨.twE6, r, n⟩ : GLALabel) := by
  intro h
  have h3 : p ∣ Nat.gcd 3 (2 ^ n + 1) := by simpa [rk2DiagIndex] using h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
    (h3.trans (Nat.gcd_dvd_left 3 (2 ^ n + 1))))

private theorem five_le_and_two_le_of_dvd_two_pow_add_one {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ 2 ^ n + 1) :
    5 ≤ p ∧ 2 ≤ n := by
  have hn0 : n ≠ 0 := by
    intro hn
    rw [hn] at hpq
    norm_num at hpq
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpq)
  have hn1 : n ≠ 1 := by
    intro hn
    rw [hn] at hpq
    norm_num at hpq
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpq)
  have hn2 : 2 ≤ n := by omega
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    have hp4 : p ≤ 4 := by omega
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  exact ⟨hp5, hn2⟩

section


private theorem markedModel_twE6_of_marking
    {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (hpd : ¬ p ∣ rk2DiagIndex lab)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧ GLASplit16 p lab' ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    Rk2IsLabel S lab ∧ GLASplit16 p lab ∧
      MarkedModel lab (↥S ⧸ Subgroup.center ↥S) ∧
      ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω) := by
  have hmark' : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ) :=
    rk2_marking_mono (fun lab' R _ I F θ h => ⟨h.1, h.2.2⟩) hmark
  have hBin := mem_sup_centralizer_of_innerDiag_of_not_dvd_diagIndex hcfg.prime hcfg.odd
    hcfg.elem hlab hpd hmark'
  have hRk : Rk2IsLabel S lab := rk2_marking_mono (fun lab' R _ I F θ h => h.1) hmark
  obtain ⟨-, -, hM⟩ := rk2_model_of_isLabel hRk
  obtain ⟨-, lab', hlab', hraw⟩ := hmark
  obtain ⟨R, _, I, F₀, _hs, _hna, θ, ⟨hlabEq, hsplit, _hN, _hind⟩⟩ := rk2_rawDatum_exists hraw
  subst hlabEq
  exact ⟨hRk, hsplit, hM, hBin⟩

private theorem exists_twistedE6Model_of_markedModel
    {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {lab : GLALabel} (htag : lab.tag = .twE6)
    (hp3 : p ≠ 3) (hsplit : GLASplit16 p lab) (hRk : Rk2IsLabel S lab)
    (hM : MarkedModel lab (↥S ⧸ Subgroup.center ↥S))
    (hBin : ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F ≃+* F),
      Nat.card F = (2 ^ lab.n) ^ 2 ∧ (∀ c, σ c = c ^ 2 ^ lab.n) ∧
      p ∣ 2 ^ lab.n + 1 ∧ 5 ≤ p ∧ 2 ≤ lab.n ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥S) ∧
      Nonempty (S172X.S172Model S B ↥(twistedE6RootGroup F σ)) := by
  obtain ⟨t, r, n⟩ := lab
  subst htag
  have hM' : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .twistedE6 0 2 n :=
    u6_model_twE6 (lab := ⟨.twE6, r, n⟩) rfl hM
  have hpq : p ∣ 2 ^ n + 1 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.dvd_two_pow_add_one_of_split16_of_twA_or_twE6
      hsplit (Or.inr rfl)
  obtain ⟨hp5, hn2⟩ := five_le_and_two_le_of_dvd_two_pow_add_one hcfg.prime hcfg.odd hp3 hpq
  have hcenter : ¬ p ∣ Nat.card (Subgroup.center ↥S) := by
    intro hpZ
    have hdvd := rk2_card_center_dvd_twE6 hRk rfl hn2
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hcfg.prime Nat.prime_three).1
      (hpZ.trans (hdvd.trans (Nat.gcd_dvd_left 3 (2 ^ n + 1)))))
  obtain ⟨F, hF, hFin, σ, hcard, hσ, ⟨e⟩⟩ :=
    exists_twistedE6RootGroup_of_marked (lab := ⟨.twE6, r, n⟩) hM'
  letI : Field F := hF
  letI : Finite F := hFin
  obtain ⟨M⟩ := S172Model.nonempty_of_mem_sup hcfg.normal hBin e
  exact ⟨F, hF, hFin, σ, hcard, hσ, hpq, hp5, hn2, hcenter, ⟨M⟩⟩

theorem exists_model_twE6
    {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (hfam : famTwE6 lab p)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧ GLASplit16 p lab' ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F ≃+* F),
      Nat.card F = (2 ^ lab.n) ^ 2 ∧ (∀ c, σ c = c ^ 2 ^ lab.n) ∧
      p ∣ 2 ^ lab.n + 1 ∧ 5 ≤ p ∧ 2 ≤ lab.n ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥S) ∧
      Nonempty (S172X.S172Model S B ↥(twistedE6RootGroup F σ)) := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨htag, hp3⟩ := hfam
  subst htag
  have hpd := not_dvd_rk2DiagIndex_of_twE6 (r := r) (n := n) hcfg.prime hp3
  obtain ⟨hRk, hsplit, hM, hBin⟩ := markedModel_twE6_of_marking hcfg hlab hpd hmark
  exact exists_twistedE6Model_of_markedModel hcfg rfl hp3 hsplit hRk hM hBin

end

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
