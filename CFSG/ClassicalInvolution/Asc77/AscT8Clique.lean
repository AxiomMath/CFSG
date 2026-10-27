module

public import CFSG.ClassicalInvolution.Asc77.AscT8Thm4
public import CFSG.ClassicalInvolution.Asc77.AscIHSectD
public import CFSG.ClassicalInvolution.Asc77.AscIHSectE
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8Free
public import CFSG.ClassicalInvolution.RouteD.ExoticD4Model
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Dichotomy

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dConnected_or_transitive_noTwins {n : ℕ} (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h4 : Thm4NTBelow p f n) (hlt : Nat.card X < n) (hΦ : HypOmegaMod p f Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K) :
    DConnected Φ ∨ ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L := by
  by_cases htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L
  · exact Or.inr htrans
  left
  push Not at htrans
  obtain ⟨K₀, hK₀, M₀, hM₀, hnc⟩ := htrans
  have hc0 : Commutes K₀ M₀ :=
    h4 hp hq X hlt Φ hΦ hO hnt K₀ hK₀ M₀ hM₀ (fun ⟨g, hg⟩ => hnc g hg)
  have hne0 : K₀ ≠ M₀ := fun h => hnc 1 (by rw [conjSub_one, h])
  have hadj0 : dAdj Φ K₀ M₀ := dAdj_of_commutes hM₀ hne0 hc0
  have hjoin : ∀ M ∈ Φ,
      Relation.ReflTransGen (fun A B : Subgroup X => B ∈ Φ ∧ dAdj Φ A B) K₀ M ∧
        Relation.ReflTransGen (fun A B : Subgroup X => B ∈ Φ ∧ dAdj Φ A B) M K₀ := by
    intro M hM
    by_cases hMc : ∃ g : X, conjSub g K₀ = M
    · have hnotM : ¬ ∃ g : X, conjSub g M = M₀ := by
        rintro ⟨g, hg⟩
        obtain ⟨y, rfl⟩ := hMc
        exact hnc (g * y) (by rw [conjSub_mul]; exact hg)
      have hc : Commutes M M₀ := h4 hp hq X hlt Φ hΦ hO hnt M hM M₀ hM₀ hnotM
      have hne : M ≠ M₀ := fun h => hnotM ⟨1, by rw [conjSub_one, h]⟩
      have hadj : dAdj Φ M M₀ := dAdj_of_commutes hM₀ hne hc
      exact ⟨(Relation.ReflTransGen.single ⟨hM₀, hadj0⟩).tail ⟨hM, dAdj_symm hadj⟩,
        (Relation.ReflTransGen.single ⟨hM₀, hadj⟩).tail ⟨hK₀, dAdj_symm hadj0⟩⟩
    · push Not at hMc
      have hc : Commutes K₀ M :=
        h4 hp hq X hlt Φ hΦ hO hnt K₀ hK₀ M hM (fun ⟨g, hg⟩ => hMc g hg)
      have hne : K₀ ≠ M := fun h => hMc 1 (by rw [conjSub_one, h])
      have hadj : dAdj Φ K₀ M := dAdj_of_commutes hM hne hc
      exact ⟨Relation.ReflTransGen.single ⟨hM, hadj⟩,
        Relation.ReflTransGen.single ⟨hK₀, dAdj_symm hadj⟩⟩
  intro K hK L hL
  exact (hjoin K hK).2.trans (hjoin L hL).1

end Dichotomy

section G2D4

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dEdgeless_of_g2d4_datum (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {t : StatedLieTag} {k e : ℕ}
    (M : Ih8Model p f Φ t k e) (ht : t = .G2 ∨ t = .trialityD4) : DEdgeless Φ := by
  have he : 1 ≤ e := M.admissible.2.1
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 ht k he M.ψ M.ker_le_center
  have hsurj : Function.Surjective M.ψ := M.surj
  rcases ht with ht2 | ht2
  · subst ht2
    obtain ⟨hk, -⟩ := M.admissible.2.2
    subst hk
    have hqe : 5 ≤ p ^ e := by
      rcases M.exp_eq with h' | ⟨h', -⟩
      · rw [h']
        exact hq
      · exact absurd h' (by decide)
    exact G2D4Models.dEdgeless_of_model M.ψ hinj hsurj M.mem_iff htrans fun Q hQ =>
      G2D4Models.eq_of_isMaxPGroup_le_normalizer_g2 hp2 hqe M.admissible Q (M.cls_sub hQ)
  · subst ht2
    have hk : k = 0 := M.admissible.2.2
    subst hk
    have hf : f ≠ 0 := by
      rintro rfl
      simp at hq
    have h60 : ∀ Q ∈ M.cls, 60 ≤ Nat.card Q := by
      intro Q hQ
      obtain ⟨z, hz⟩ := hΦ.classical _ (M.map_mem hQ)
      obtain ⟨φ⟩ := hz.nonempty_equiv
      have h1 : Nat.card SL(2, GaloisField p f) ≤ Nat.card (Q.map M.ψ) :=
        calc Nat.card SL(2, GaloisField p f)
            = Nat.card ((Q.map M.ψ) ⧸ classicalInvolutionOddCore (Q.map M.ψ)) :=
              Nat.card_congr φ.toEquiv.symm
          _ ≤ Nat.card (Q.map M.ψ) :=
              Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
      rw [Subgroup.card_map_of_injective hinj, RouteD.G2D4.card_sl2_field,
        GaloisField.card p f hf] at h1
      have h25 : 25 ≤ (p ^ f) ^ 2 := by nlinarith
      have h24 : 24 ≤ (p ^ f) ^ 2 - 1 := by omega
      calc 60 ≤ 5 * 24 := by norm_num
        _ ≤ p ^ f * ((p ^ f) ^ 2 - 1) := Nat.mul_le_mul hq h24
        _ ≤ Nat.card Q := h1
    exact G2D4Models.dEdgeless_of_model M.ψ hinj hsurj M.mem_iff htrans fun Q hQ =>
      G2D4Models.eq_of_isMaxPGroup_le_normalizer_td4 hp2 M.admissible Q (M.cls_sub hQ) (h60 Q hQ)

end G2D4

section Clique

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dConnected_of_five_clique {n : ℕ} (hn : CITBelowU p f n) (hlt : Nat.card X < n)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K) (B : Fin 5 → Subgroup X)
    (hB : ∀ i, B i ∈ Φ) (hinj : Function.Injective B)
    (hadj : ∀ i j, i ≠ j → B j ∈ omegaNbr Φ (B i)) : DConnected Φ := by
  classical
  have hne : Φ.Nonempty := ⟨B 0, hB 0⟩
  rcases dConnected_or_transitive_noTwins hp2 hq (thm4NTBelow_of_citBelow hn) hlt hΦ hO hnt with
    hc | htrans
  · exact hc
  obtain ⟨D⟩ := exists_omegaLie hn hΦ hne hO hlt
  obtain ⟨t, k, e, M, -⟩ := exists_datum_of_omegaLie D hΦ hgen htrans hne
  by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
  · exact absurd (Or.inl (hadj 0 1 (by decide))) (dEdgeless_of_g2d4_datum hp2 hq hΦ htrans M hG2d4
      _ (hB 0) _ (hB 1))
  have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
  have hD4' : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
  have h10 : B 1 ≠ B 0 := fun h => absurd (hinj h) (by decide)
  have htop := top_notMem_of_transitive htrans (hB 0) (hB 1) h10
  have hnpsl := M.not_psl_two_sect hp2 hne htop
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4']; exact hq
  have hpre : ∀ i, ∃ R ∈ M.cls, B i = R.map M.ψ := fun i => (M.mem_iff _).mp (hB i)
  choose R hRcls hRB using hpre
  have hcomm : ∀ i j, i ≠ j → Commutes (R i) (R j) := fun i j hij =>
    M.commutes_of_omegaNbr_sect hΦ hp2 hq hG2 hD4' (hRcls i) (hRcls j)
      (by rw [← hRB i, ← hRB j]; exact hadj i j hij)
  have hRne : ∀ i j, i ≠ j → R i ≠ R j := fun i j hij h =>
    hij (hinj (by rw [hRB i, hRB j, h]))
  have hRf := fun i => M.cls_sub (hRcls i)
  rcases ih8_tag_cases hp2 hq' M.isFundTag M.admissible hG2 hD4' with hconn | hsmall
  · exact M.dConnected_of_connected hp2 hq hne hG2 hD4' hconn
  exfalso
  have h01 : (0 : Fin 5) ≠ 1 := by decide
  have h02 : (0 : Fin 5) ≠ 2 := by decide
  have h12 : (1 : Fin 5) ≠ 2 := by decide
  have hNT := smallNoThree (p := p)
  rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    have hk2 : 2 ≤ k := M.admissible.2.2.1
    have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl
    · exact hnpsl ⟨rfl, rfl⟩
    · have := four_le_of_commutes_psl hp2 (le_refl 3) (hRf 0) (hRf 1) (hRne 0 1 h01)
        (hcomm 0 1 h01)
      omega
    · exact hNT _ _ _ M.admissible hp2 hq' (Or.inr (Or.inl ⟨rfl, rfl⟩)) _ (hRf 0) _ (hRf 1) _
        (hRf 2) (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12) (hcomm 0 1 h01) (hcomm 0 2 h02)
        (hcomm 1 2 h12)
  ·
    have hk3 : 3 ≤ k := M.admissible.2.2.1
    have : k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl
    · have := four_le_of_commutes_psu hp2 M.admissible (hRf 0) (hRf 1) (hRne 0 1 h01)
        (hcomm 0 1 h01)
      omega
    · exact hNT _ _ _ M.admissible hp2 hq' (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) _ (hRf 0) _
        (hRf 1) _ (hRf 2) (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12) (hcomm 0 1 h01)
        (hcomm 0 2 h02) (hcomm 1 2 h12)
  · exact hNT _ _ _ M.admissible hp2 hq' (Or.inl ⟨rfl, rfl⟩) _ (hRf 0) _ (hRf 1) _ (hRf 2)
      (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12) (hcomm 0 1 h01) (hcomm 0 2 h02)
      (hcomm 1 2 h12)
  · exact hNT _ _ _ M.admissible hp2 hq' (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) _
      (hRf 0) _ (hRf 1) _ (hRf 2) (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12)
      (hcomm 0 1 h01) (hcomm 0 2 h02) (hcomm 1 2 h12)
  ·
    obtain ⟨F₄, -, -, -, -, -, -, hall⟩ := cliqueFour_fund_plus_four hp2 hq' M.admissible
      ⟨R 0, hRf 0⟩ ⟨R 1, hRf 1⟩ ⟨R 2, hRf 2⟩
      (fun h => hRne 0 1 h01 (congrArg Subtype.val h))
      (fun h => hRne 0 2 h02 (congrArg Subtype.val h))
      (fun h => hRne 1 2 h12 (congrArg Subtype.val h))
      (hcomm 0 1 h01) (hcomm 0 2 h02) (hcomm 1 2 h12)
    have h3 := hall ⟨R 3, hRf 3⟩ (hcomm 0 3 (by decide))
    have h4 := hall ⟨R 4, hRf 4⟩ (hcomm 0 4 (by decide))
    have h31 : R 3 ≠ R 1 := hRne 3 1 (by decide)
    have h32 : R 3 ≠ R 2 := hRne 3 2 (by decide)
    have h41 : R 4 ≠ R 1 := hRne 4 1 (by decide)
    have h42 : R 4 ≠ R 2 := hRne 4 2 (by decide)
    have e3 : R 3 = F₄.1 := by
      rcases h3 with h | h | h
      · exact absurd (congrArg Subtype.val h) h31
      · exact absurd (congrArg Subtype.val h) h32
      · exact congrArg Subtype.val h
    have e4 : R 4 = F₄.1 := by
      rcases h4 with h | h | h
      · exact absurd (congrArg Subtype.val h) h41
      · exact absurd (congrArg Subtype.val h) h42
      · exact congrArg Subtype.val h
    exact hRne 3 4 (by decide) (e3.trans e4.symm)
  · exact hNT _ _ _ M.admissible hp2 hq' (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) _
      (hRf 0) _ (hRf 1) _ (hRf 2) (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12)
      (hcomm 0 1 h01) (hcomm 0 2 h02) (hcomm 1 2 h12)

end Clique

end CFSG.ClassicalInvolution.Asc77
