module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Lem96

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

namespace L915

section Lem912

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

omit [Finite G] in
theorem le_normalizer_Dcore (p : ℕ) (N : Subgroup G) : N ≤ normalizer ((Dcore p N : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, Dcore, Subgroup.map_iSup]
  refine iSup_congr fun q => ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun hq => ?_
  exact mem_normalizer_iff_map_conj_eq.mp (le_normalizer_Op' q N hg)

theorem coprime_card_Dcore (hp : p.Prime) (N : Subgroup G) : Nat.Coprime p (Nat.card ↥(Dcore p N)) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : Nat.card ↥(Dcore p N) ∣ Nat.card ↥(pPrimeCoreOf p N) :=
    Subgroup.card_dvd_of_le (Dcore_le_pPrimeCoreOf hp N)
  have h2 : Nat.card ↥(pPrimeCoreOf p N) = Nat.card ↥(pPrimeCore p ↥N) :=
    Subgroup.card_map_of_injective N.subtype_injective
  exact Nat.Coprime.coprime_dvd_right h1 (h2 ▸ CFSG.pPrimeCore_coprime_card (p := p) (G := ↥N))

theorem lemma9_12 (h512 : IG_5_12) (h19 : B_signalizer_19_9) (h118 : IG_11_8) (h1123 : IG_11_23)
    (hC : Ctx9 G z k S M p) {X V N : Subgroup G} (hXP : X ≤ Op p M)
    (hzX : z ∈ normalizer (X : Set G)) (hXc : ⁅X, zpowers z⁆ = X) (hN : IsCoatom N)
    (hXN : normalizer (X : Set G) ≤ N) (hV : V ≤ Op p M ⊓ N ⊓ Cen z) (hVe : IsElementaryAbelian p ↥V)
    (hV2 : Nat.card ↥V = p ^ 2) (hv : ∀ v ∈ V, v ≠ 1 → NN z p (Op p M) (zpowers v))
    (hnot : Fs N ≠ Op p N) : Fm N = Op p N ∧ Em N ≠ ⊥ := by
  have hp := hC.prime
  have hXN' : X ≤ N := le_trans Subgroup.le_normalizer hXN
  have hD : Dcore p N = ⊥ := by
    have hXD : X ≤ centralizer (Dcore p N : Set G) :=
      lemma9_2b h19 h118 hC hXP hzX hN hXN (le_inf hXP hXN') hXc
    have hcent : ∀ v ∈ V, v ≠ 1 → Dcore p N ⊓ centralizer ({v} : Set G) = ⊥ := by
      intro v hvV hv1
      have hvP : v ∈ Op p M := (hV hvV).1.1
      have hvN : v ∈ N := (hV hvV).1.2
      have hY : NN z p ⊤ (zpowers v) :=
        ⟨le_top, (hv v hvV hv1).2.1, (hv v hvV hv1).2.2.1, (hv v hvV hv1).2.2.2⟩
      have hW : IsPGroup p ↥(X ⊔ zpowers v) :=
        hC.P_pgroup.to_le (sup_le hXP (Subgroup.zpowers_le.mpr hvP))
      obtain ⟨h1, -⟩ := lemma_9_3 h512 G z k S M p hC N X (zpowers v) hN hXN
        (Subgroup.zpowers_le.mpr hvN) hY hW
      rw [eq_bot_iff, ← h1]
      refine le_inf (inf_le_left.trans (Dcore_le_pPrimeCoreOf hp N)) ?_
      intro x hx
      have hxD : x ∈ Dcore p N := hx.1
      have hle : X ⊔ zpowers v ≤ centralizer ({x} : Set G) := by
        refine sup_le (fun h hh => ?_) (Subgroup.zpowers_le.mpr ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp (hXD hh) x hxD).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
    have hVN : V ≤ N := fun v hv => (hV hv).1.2
    have hgen := h1123 G p hp V (Dcore p N) hVe hV2 (coprime_card_Dcore hp N)
      (hVN.trans (le_normalizer_Dcore p N))
    exact le_bot_iff.mp (hgen.trans (iSup₂_le fun v hv => (hcent v hv.1 hv.2).le))
  have hFm : Fm N = Op p N := by
    refine le_antisymm ?_ (Op_le_Fm p hp N)
    calc Fm N ≤ Op p N ⊔ Dcore p N := Fm_le_Op_sup_Dcore N
      _ = Op p N := by rw [hD, sup_bot_eq]
  refine ⟨hFm, fun hEm => hnot ?_⟩
  rw [Fs_eq_sup, hFm, hEm, sup_bot_eq]

end Lem912

end L915

end CFSG.GH74.GLS.Stage2.Bender.Thm2
