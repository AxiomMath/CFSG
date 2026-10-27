module

public import CFSG.Quasithin.H13.A7NatMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Elimination
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7NatAssembly
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7NatMainS331

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

@[expose] def Stmt12_3_3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ∃ ψ : V ≃* Multiplicative (evenWeight 7),
      (∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ) ∧
      ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ

@[expose] def Stmt12_3_6_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ∀ ψ : V ≃* Multiplicative (evenWeight 7),
      (∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ) →
      (∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ) →
      ∀ e : V, (e : G) ∈ quasithinOmegaOneCenter T → hammingNorm (vec ψ e) = 6 →
        centralizer ({(e : G)} : Set G) ≤ normalizer (L : Set G)

@[expose] def Stmt12_3_8_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ∀ ψ : V ≃* Multiplicative (evenWeight 7),
      (∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ) →
      (∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ) →
      ∀ e : V, (e : G) ∈ quasithinOmegaOneCenter T → hammingNorm (vec ψ e) = 2 →
        centralizer ({(e : G)} : Set G) ≤ normalizer (L : Set G)

theorem stmtA7NaturalModuleConfigHyp_of_lemmas_F4 (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4)
    (h1233 : Stmt12_3_3_F4) (h1236 : Stmt12_3_6_F4) (h1238 : Stmt12_3_8_F4) :
    StmtA7NaturalModuleConfigHyp_F4 := by
  intro G _ _ T L V hyp hA7
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, hTI, -, -⟩ := hall V hyp.irrPlus

  obtain ⟨ψ₀, hLact, hLonto⟩ := h1233 G T L V hyp hA7
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hNM := normalizer_le_of_hyp1223_F4 h331 hyp hVT hTV
  have hpre : A7NatPre T L V ψ₀ :=
    ⟨hVT, hLV, hTV, hLact, hLonto, nact_of_lact hLV hLact hLonto hNM, hNM, hTI⟩
  obtain ⟨ψ, h, hcent⟩ := hpre.exists_aligned_central hyp.sylow

  have hZ : ∀ x : V, (x : G) ∈ centralizer (T : Set G) → (x : G) ∈ quasithinOmegaOneCenter T :=
    fun x hx => mem_omegaOneCenter_of_central hVT hx (by
      rw [pow_two]
      exact congrArg Subtype.val (sq_eq_one_of_vec ψ x))
  have wt26 : ∀ v : V, (hammingNorm (vec ψ v) = 2 ∨ hammingNorm (vec ψ v) = 6) →
      centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) := by
    intro v hv
    rcases hv with hv | hv
    · obtain ⟨x, hx, hxc⟩ := hcent 2 (Or.inl rfl)
      exact h.centralizer_le_of_weight hx
        (h1238 G T L V hyp hA7 ψ h.Lact h.Lonto x (hZ x hxc) hx) hv
    · obtain ⟨x, hx, hxc⟩ := hcent 6 (Or.inr (Or.inr rfl))
      exact h.centralizer_le_of_weight hx
        (h1236 G T L V hyp hA7 ψ h.Lact h.Lonto x (hZ x hxc) hx) hv
  exact ⟨ψ, h.toConfig wt26 (h.weight_four_of_mem_conjugate_F4 h331 hyp wt26)⟩

theorem stmtA7NaturalModuleConfig_of_lemmas_F4 (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4)
    (h1233 : Stmt12_3_3_F4) (h1236 : Stmt12_3_6_F4) (h1238 : Stmt12_3_8_F4) :
    StmtA7NaturalModuleConfig_F4 :=
  stmtA7NaturalModuleConfig_of_hyp_F4 h1222
    (stmtA7NaturalModuleConfigHyp_of_lemmas_F4 h1222 h331 h1233 h1236 h1238)

theorem stmt12_3_1_of_lemmas_F4
    (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4) (h1233 : Stmt12_3_3_F4)
    (h1236 : Stmt12_3_6_F4) (h1238 : Stmt12_3_8_F4) (h12213 : Stmt12_2_13_F4) (h1227 : Stmt12_2_7_F4)
    (h1228 : Stmt12_2_8_F4) (h1229 : Stmt12_2_9_F4) : Stmt12_3_1_F4 :=
  stmt12_3_1_of_inputs_F4 (stmtA7NaturalModuleConfigHyp_of_lemmas_F4 h1222 h331 h1233 h1236 h1238)
    h12213 h1227 h1228 h1229 h331

end CFSG.Quasithin.H13.A7
