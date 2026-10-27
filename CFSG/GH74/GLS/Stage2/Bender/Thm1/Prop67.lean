module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Cited
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der72a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Elem

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section P67

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pPrimeCoreOf_conj_of_mem {r : ℕ} {N : Subgroup G} {c x : G} (hc : c ∈ N)
    (hx : x ∈ pPrimeCoreOf r N) : c * x * c⁻¹ ∈ pPrimeCoreOf r N := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, (CFSG.pPrimeCore_normal).conj_mem y hy ⟨c, hc⟩, rfl⟩

theorem cen_le_normalizer_zpowers_aux (v : G) :
    centralizer ({v} : Set G) ≤ normalizer ((zpowers v : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_of_forall fun y hy => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hxv : Commute x v := Subgroup.mem_centralizer_singleton_iff.mp hx
  have h : x * v ^ n * x⁻¹ = v ^ n := by
    rw [(hxv.zpow_right n).eq]
    group
  rw [h]
  exact Subgroup.zpow_mem_zpowers v n

theorem prop6_7_Fm (hB12 : Bender12) {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
    (hC : Ctx6 G z k S M p) {r : ℕ} (hr : r.Prime) {V : Subgroup G} (hV : V ≤ Op r M ⊓ Cen z)
    (hVe : IsElementaryAbelian r ↥V) (hVc : Nat.card ↥V = r ^ 2)
    (hv : ∀ v ∈ V, v ≠ 1 → NF z M (zpowers v)) {X : Subgroup G} (hX : X ≤ Fm M)
    (hVX : V ≤ normalizer (X : Set G)) {N : Subgroup G} (hXN : normalizer (X : Set G) ≤ N) :
    Fm N ≤ M := by
  have hFπ : Fpi {q | q.Prime ∧ q ∣ Nat.card ↥(Fm M)} N ≤ M := by
    have h := hB12 G hC.ctx.std.kps M N hC.coatom X hX (inf_le_right.trans hXN)
    rcases h.2.1 with ⟨q, hq, hqP⟩ | h
    · rw [hC.Fs_eq hC.mem] at hqP
      exact absurd hqP (not_isPGroup_of_twoPrimes hC.twoPrimes hq)
    · exact h
  have hVF : V ≤ Fm M := (hV.trans inf_le_left).trans (Op_le_Fm r hr M)
  have hrπ : r ∣ Nat.card ↥(Fm M) := by
    have h1 : Nat.card ↥V ∣ Nat.card ↥(Fm M) := Subgroup.card_dvd_of_le hVF
    rw [hVc] at h1
    exact (dvd_pow_self r (by norm_num)).trans h1
  have hVN : V ≤ N := hVX.trans hXN
  set D : Subgroup G := pPrimeCoreOf r N with hD
  have hDM : D ≤ M := by
    have hVnorm : V ≤ normalizer (D : Set G) := fun v hv' =>
      mem_normalizer_of_forall fun d hd => pPrimeCoreOf_conj_of_mem (hVN hv') hd
    have hcop : Nat.Coprime r (Nat.card ↥D) := by
      have : Nat.card ↥D = Nat.card ↥(pPrimeCore r ↥N) :=
        Subgroup.card_map_of_injective N.subtype_injective
      rw [this]
      have : Fact r.Prime := ⟨hr⟩
      exact pPrimeCore_coprime_card (p := r) (G := ↥N)
    have h := ig_11_23_thm G r hr V D hVe hVc hcop hVnorm
    refine h.trans (iSup₂_le fun v hv' => ?_)
    exact inf_le_right.trans
      ((cen_le_normalizer_zpowers_aux v).trans (hv v hv'.1 hv'.2).2.2.2)
  refine Fm_le_of_forall fun q hq => ?_
  by_cases hqr : q = r
  · subst hqr
    rw [← Op_Fm_eq hq N]
    exact (le_iSup₂_of_le q ⟨hq, hrπ⟩ le_rfl).trans hFπ
  · have : Fact q.Prime := ⟨hq⟩
    have hOD : Op q N ≤ D := by
      rw [Op_def, hD, pPrimeCoreOf]
      refine Subgroup.map_mono (le_pPrimeCore_of_normal_coprime (CFSG.pCore_normal) ?_)
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (pCore_isPGroup (p := q) (G := ↥N))
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes hr hq).mpr (Ne.symm hqr))
    exact hOD.trans hDM

@[expose] def Prop6_7E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ (r : ℕ) (V : Subgroup G), r.Prime → V ≤ Op r M ⊓ Cen z → IsElementaryAbelian r ↥V →
      Nat.card ↥V = r ^ 2 → (∀ v ∈ V, v ≠ 1 → NF z M (zpowers v)) →
      ∀ X : Subgroup G, X ≤ Fm M → X ≠ ⊥ → V ⊔ zpowers z ≤ normalizer (X : Set G) →
        ∀ N : Subgroup G, IsCoatom N → normalizer (X : Set G) ≤ N → Em N ≤ M

theorem prop6_7_of (hB12 : Bender12) (hB13 : Bender13) (hE : Prop6_7E) : Prop6_7 := by
  intro G _ _ z k S M p hC r V hr hV hVe hVc hv X hX hX1 hVX
  have hVX' : V ≤ normalizer (X : Set G) := le_sup_left.trans hVX
  have hzX : z ∈ normalizer (X : Set G) := le_sup_right.trans hVX (Subgroup.mem_zpowers z)
  have hne : normalizer (X : Set G) ≠ ⊤ := normalizer_ne_top hC hX1 (hX.trans (Fm_le M))
  rcases eq_top_or_exists_le_coatom (normalizer (X : Set G)) with h | ⟨N, hN, hXN⟩
  · exact absurd h hne
  have hFm : Fm N ≤ M := prop6_7_Fm hB12 hC hr hV hVe hVc hv hX hVX' hXN
  have hEm : Em N ≤ M := hE G z k S M p hC r V hr hV hVe hVc hv X hX hX1 hVX N hN hXN
  have hFs : Fs N ≤ M := by
    rw [Fs_eq_sup]
    exact sup_le hFm hEm
  have hNM : Links N M := ⟨⊥, bot_le, inf_le_left.trans hFs⟩
  have hMN : Links M N := ⟨X, hX, inf_le_right.trans hXN⟩
  have hMN' : M = N := by
    rcases hB13 G hC.ctx.std.kps M N hC.coatom hN hMN hNM with h | ⟨q, hq, hqM, -⟩
    · exact h
    · exfalso
      rw [hC.Fs_eq hC.mem] at hqM
      exact not_isPGroup_of_twoPrimes hC.twoPrimes hq hqM
  refine ⟨hX, hX1, hzX, ?_⟩
  rw [hMN']
  exact hXN

end P67

end CFSG.GH74.GLS.Stage2.Bender.Thm1
