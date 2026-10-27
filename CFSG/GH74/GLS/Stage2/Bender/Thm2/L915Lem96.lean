module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Lem92
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs9

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

namespace L915

structure Hyp95 {G : Type} [Group G] (z : G) (M : Subgroup G) (p : ℕ) (N A B : Subgroup G) : Prop where
  coatom : IsCoatom N
  A_le : A ≤ Op p M
  B_le : B ≤ Op p M
  A_ne : A ≠ ⊥
  B_ne : B ≠ ⊥
  A_inv : z ∈ normalizer (A : Set G)
  B_inv : z ∈ normalizer (B : Set G)
  A_comm : ⁅A, zpowers z⁆ = A
  A_mem : NN z p (Op p M) A
  B_norm : normalizer (B : Set G) ≤ N
  A_N : A ≤ N

section Lem96

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem normalizer_eq_of_normalized9 (hC : Ctx9 G z k S M p) {N B : Subgroup G} (hN : IsCoatom N)
    (hB : B ≠ ⊥) (hBN : B ≤ N) (hn : N ≤ normalizer (B : Set G)) : normalizer (B : Set G) = N := by
  refine le_antisymm ?_ hn
  by_contra hnle
  have hne : N ≠ normalizer (B : Set G) := fun h => hnle (h ▸ le_rfl)
  have hlt : N < normalizer (B : Set G) := lt_of_le_of_ne hn hne
  have htop : normalizer (B : Set G) = ⊤ := hN.2 _ hlt
  have hBn : B.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases (haveI := hBn; hC.simple.eq_bot_or_eq_top_of_normal B) with h | h
  · exact hB h
  · have : (⊤ : Subgroup G) ≤ N := h ▸ hBN
    exact hN.1 (top_le_iff.mp this)

omit [Finite G] in
theorem Fs_eq_sup (N : Subgroup G) : Fs N = Fm N ⊔ Em N := Subgroup.map_sup _ _ _

theorem Op_le_pPrimeCoreOf {q : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) (N : Subgroup G) :
    Op q N ≤ pPrimeCoreOf p N := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card ↥(pCore q ↥N)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (G := ↥N) (p := q))
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp hq).mpr (Ne.symm hqp))
  have hle : pCore q ↥N ≤ CFSG.pPrimeCore p ↥N := le_sSup ⟨CFSG.pCore_normal, hcop⟩
  exact Subgroup.map_mono hle

theorem Fm_le_Op_sup_Dcore (N : Subgroup G) : Fm N ≤ Op p N ⊔ Dcore p N := by
  rw [Fm_def, CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore (G := ↥N), Subgroup.map_iSup]
  refine iSup_le fun q => ?_
  by_cases hqp : (q : ℕ) = p
  · rw [hqp]
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂_of_le (q : ℕ)
      ⟨Nat.prime_of_mem_primeFactors q.2, hqp⟩ le_rfl)

theorem commutator_Op_Op_eq_bot {q : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) (N : Subgroup G) :
    ⁅Op q N, Op p N⁆ = ⊥ := by
  refine commutator_eq_bot_of_coprime (le_normalizer_Op' q N) (le_normalizer_Op' p N) (Op_le' q N)
    (Op_le' p N) ?_
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (op_isPGroup (p := q) N)
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (op_isPGroup (p := p) N)
  rw [ha, hb]
  exact Nat.Coprime.pow a b ((Nat.coprime_primes hq hp).mpr hqp)

theorem Fm_comm_Em (N : Subgroup G) : ⁅Fm N, Em N⁆ = ⊥ := by
  have h := CFSG.LocalCores.fitting_layer_commute (G := ↥N)
  have h2 := Subgroup.map_commutator (fittingSubgroup ↥N) (layer ↥N) N.subtype
  rw [h, Subgroup.map_bot] at h2
  exact h2.symm

theorem inf_pPrimeCoreOf_eq_bot {A N : Subgroup G} (hp : p.Prime) (hA : IsPGroup p ↥A) :
    A ⊓ pPrimeCoreOf p N = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hA) ⟨a, ha.1⟩
  rw [Subgroup.orderOf_mk] at hj
  exact eq_one_of_coprime_pow hp hj (coprime_orderOf_of_mem_pPrimeCoreOf hp ha.2)

theorem Dcore_le_pPrimeCoreOf (hp : p.Prime) (N : Subgroup G) : Dcore p N ≤ pPrimeCoreOf p N :=
  iSup₂_le fun _ hq => Op_le_pPrimeCoreOf hq.1 hp hq.2 N

theorem Dcore_le_centralizer_Op (hp : p.Prime) (N : Subgroup G) :
    Dcore p N ≤ centralizer ((Op p N : Subgroup G) : Set G) :=
  iSup₂_le fun _ hq =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commutator_Op_Op_eq_bot hq.1 hp hq.2 N)

theorem lemma9_6a (h118 : IG_11_8) (hC : Ctx9 G z k S M p) {N A B : Subgroup G}
    (h : Hyp95 z M p N A B) : Op 2 N = ⊥ :=
  lemma9_2a h118 hC h.B_le h.B_inv h.B_norm

theorem A_le_centralizer_Dcore (h19 : B_signalizer_19_9) (h118 : IG_11_8) (hC : Ctx9 G z k S M p)
    {N A B : Subgroup G} (h : Hyp95 z M p N A B) : A ≤ centralizer (Dcore p N : Set G) :=
  lemma9_2b h19 h118 hC h.B_le h.B_inv h.coatom h.B_norm (le_inf h.A_le h.A_N) h.A_comm

theorem lemma9_6b (h512 : IG_5_12) (h19 : B_signalizer_19_9) (h118 : IG_11_8)
    (hC : Ctx9 G z k S M p) {N A B : Subgroup G} (h : Hyp95 z M p N A B) (hR : Op p N ≠ ⊥) :
    Dcore p N = ⊥ := by
  have hp := hC.prime
  have hNX' : normalizer ((Op p N : Subgroup G) : Set G) = N :=
    normalizer_eq_of_normalized9 hC h.coatom hR (Op_le' p N) (le_normalizer_Op' p N)
  have hAN : NN z p ⊤ A := ⟨le_top, h.A_ne, h.A_inv, h.A_mem.2.2.2⟩
  have hW : IsPGroup p ↥(Op p N ⊔ A) :=
    (op_isPGroup N).to_sup_of_normal_left' (hC.P_pgroup.to_le h.A_le)
      (h.A_N.trans (le_normalizer_Op' p N))
  obtain ⟨h1, -⟩ := lemma_9_3 h512 G z k S M p hC N (Op p N) A h.coatom hNX'.le h.A_N hAN hW
  have hD1 : Dcore p N ≤ centralizer ((Op p N ⊔ A : Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ (A_le_centralizer_Dcore h19 h118 hC h)
    rw [← Subgroup.le_centralizer_iff]
    exact Dcore_le_centralizer_Op hp N
  have h2 : Dcore p N ≤ pPrimeCoreOf p N ⊓ centralizer ((Op p N ⊔ A : Subgroup G) : Set G) :=
    le_inf (Dcore_le_pPrimeCoreOf hp N) hD1
  rw [h1] at h2
  exact le_bot_iff.mp h2

theorem lemma9_6c (h512 : IG_5_12) (h19 : B_signalizer_19_9) (h118 : IG_11_8)
    (hC : Ctx9 G z k S M p) {N A B : Subgroup G} (h : Hyp95 z M p N A B)
    (hnot : Fs N ≠ Op p N) : ¬ A ≤ centralizer (Em N : Set G) := by
  intro hAE
  apply hnot
  have hp := hC.prime
  have hFmle : Fm N ≤ Op p N ⊔ Dcore p N := Fm_le_Op_sup_Dcore N
  have hOpFs : Op p N ≤ Fs N := (Op_le_Fm p hp N).trans (Fm_le_Fs N)
  by_cases hR : Op p N = ⊥
  · exfalso
    have hD : Fm N ≤ Dcore p N := by simpa [hR] using hFmle
    have hAD : A ≤ centralizer (Dcore p N : Set G) := A_le_centralizer_Dcore h19 h118 hC h
    apply h.A_ne
    rw [eq_bot_iff]
    intro a ha
    have haN : a ∈ N := h.A_N ha
    have hDa : Dcore p N ≤ centralizer ({a} : Set G) :=
      (Subgroup.le_centralizer_iff.mp hAD).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
    have hEa : Em N ≤ centralizer ({a} : Set G) :=
      (Subgroup.le_centralizer_iff.mp hAE).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
    have haFm : a ∈ Fm N := by
      refine mem_Fm_of_centralizes_Fs haN ?_
      rw [Fs_eq_sup]
      exact sup_le (hD.trans hDa) hEa
    have hmem : a ∈ A ⊓ pPrimeCoreOf p N :=
      ⟨ha, Dcore_le_pPrimeCoreOf hp N (hD haFm)⟩
    rw [inf_pPrimeCoreOf_eq_bot hp (hC.P_pgroup.to_le h.A_le)] at hmem
    exact hmem
  · have hD0 : Dcore p N = ⊥ := lemma9_6b h512 h19 h118 hC h hR
    have hNX' : normalizer ((Op p N : Subgroup G) : Set G) = N :=
      normalizer_eq_of_normalized9 hC h.coatom hR (Op_le' p N) (le_normalizer_Op' p N)
    have hAN : NN z p ⊤ A := ⟨le_top, h.A_ne, h.A_inv, h.A_mem.2.2.2⟩
    have hW : IsPGroup p ↥(Op p N ⊔ A) :=
      (op_isPGroup N).to_sup_of_normal_left' (hC.P_pgroup.to_le h.A_le)
        (h.A_N.trans (le_normalizer_Op' p N))
    obtain ⟨-, h2⟩ := lemma_9_3 h512 G z k S M p hC N (Op p N) A h.coatom hNX'.le h.A_N hAN hW
    have hYN : Op p N ⊔ A ≤ N := sup_le (Op_le' p N) h.A_N
    have hYcen : Op p N ⊔ A ≤ centralizer (Em N : Set G) := by
      refine sup_le ?_ hAE
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      rw [eq_bot_iff, ← Fm_comm_Em N]
      exact Subgroup.commutator_mono (Op_le_Fm p hp N) le_rfl
    set Y' : Subgroup ↥N := (Op p N ⊔ A).subgroupOf N with hY'
    have hYmap : Y'.map N.subtype = Op p N ⊔ A := Subgroup.map_subgroupOf_eq_of_le hYN
    have hlayer : layer ↥N = ⊥ := by
      refine CFSG.LocalCores.layer_eq_bot_of_forall fun K hK => ?_
      refine no_component_of_Em_bot Y' (by rw [hYmap]; exact h2) K hK ?_
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyG : (y : G) ∈ Op p N ⊔ A := by
        rw [← hYmap]
        exact ⟨y, hy, rfl⟩
      have hkE : (k : G) ∈ Em N := ⟨k, CFSG.LocalCores.component_le_layer hK hk, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp (hYcen hyG) (k : G) hkE
      exact Subtype.ext this.symm
    have hEm0 : Em N = ⊥ := by
      rw [Em_def', hlayer, Subgroup.map_bot]
    refine le_antisymm ?_ hOpFs
    rw [Fs_eq_sup, hEm0, sup_bot_eq]
    calc Fm N ≤ Op p N ⊔ Dcore p N := hFmle
      _ = Op p N := by rw [hD0, sup_bot_eq]

end Lem96

end L915

end CFSG.GH74.GLS.Stage2.Bender.Thm2
