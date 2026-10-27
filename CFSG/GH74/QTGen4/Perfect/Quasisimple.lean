module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.GH74.QTGen4

open Subgroup

@[expose] def ActsTriviallyStmt : Prop :=
  ∀ {Q R : Type} [Group Q] [Finite Q] [Group R] [Finite R], commutator Q = ⊤ →
    Nat.card Q ∣ 20160 →
    (Nat.card R = 1 ∨ Nat.card R = 3 ∨ Nat.card R = 5 ∨ Nat.card R = 7 ∨ Nat.card R = 9) →
    ∀ φ : Q →* MulAut R, φ = 1

theorem pow_mem_of_dvd_20160 {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ n ∣ 20160) :
    p ^ n = 1 ∨ p ^ n = 3 ∨ p ^ n = 5 ∨ p ^ n = 7 ∨ p ^ n = 9 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hpd : p ∣ 20160 := (dvd_pow_self p hn.ne').trans h
  have h20 : (20160 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num
  rw [h20] at hpd
  have key : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 5 ∨ p ∣ 7 := by
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
        · exact Or.inl (hp.dvd_of_dvd_pow h3)
        · exact Or.inr (Or.inl (hp.dvd_of_dvd_pow h3))
      · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr h1))
  rw [h20] at h
  rcases key with h2 | h3 | h5 | h7
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2) hp2
  · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    subst hp3
    have hn2 : n ≤ 2 := by
      by_contra hc
      have h27 : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
      have := h27.trans h
      norm_num at this
    interval_cases n
    all_goals norm_num
  · have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5
    subst hp5
    have hn1 : n ≤ 1 := by
      by_contra hc
      have h25 : 5 ^ 2 ∣ 5 ^ n := pow_dvd_pow 5 (by omega)
      have := h25.trans h
      norm_num at this
    interval_cases n
    all_goals norm_num
  · have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1 h7
    subst hp7
    have hn1 : n ≤ 1 := by
      by_contra hc
      have h49 : 7 ^ 2 ∣ 7 ^ n := pow_dvd_pow 7 (by omega)
      have := h49.trans h
      norm_num at this
    interval_cases n
    all_goals norm_num

theorem le_center_of_card_mem {Q : Type} [Group Q] [Finite Q] (hA : ActsTriviallyStmt)
    (hperf : commutator Q = ⊤) (hcard : Nat.card Q ∣ 20160) (M : Subgroup Q) [M.Normal]
    (hM : Nat.card M = 1 ∨ Nat.card M = 3 ∨ Nat.card M = 5 ∨ Nat.card M = 7 ∨ Nat.card M = 9) :
    M ≤ Subgroup.center Q := by
  have hφ : (MulAut.conjNormal (H := M) : Q →* MulAut M) = 1 :=
    hA (Q := Q) (R := M) hperf hcard hM _
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg (fun f : Q →* MulAut M => ((f g) ⟨x, hx⟩ : Q)) hφ
  simp only [MonoidHom.one_apply, MulAut.one_apply, MulAut.conjNormal_apply] at h1
  calc g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [h1]

theorem le_center_of_normal_ne_top {Q : Type} [Group Q] [Finite Q] (hA : ActsTriviallyStmt)
    (hperf : commutator Q = ⊤) (hO2 : CFSG.pCore 2 Q = ⊥)
    (hsol : ∀ N : Subgroup Q, N.Normal → N ≠ ⊤ → Group.IsSolvable ↥N)
    (hcard : Nat.card Q ∣ 20160) (N : Subgroup Q) [hN : N.Normal] (hNt : N ≠ ⊤) :
    N ≤ Subgroup.center Q := by
  classical
  have hsolv : Group.IsSolvable ↥N := hsol N hN hNt
  have hcore : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥N →
      CFSG.pCore p ↥N ≤ (Subgroup.center Q).subgroupOf N := by
    intro p hp hpN
    have : Fact p.Prime := ⟨hp⟩
    have hMn : ((CFSG.pCore p ↥N).map N.subtype).Normal := inferInstance
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).1
      (CFSG.pCore_isPGroup (p := p) (G := ↥N))
    have hMcard : Nat.card ((CFSG.pCore p ↥N).map N.subtype) = p ^ n :=
      (Subgroup.card_map_of_injective N.subtype_injective).trans hn
    have hMdvd : p ^ n ∣ 20160 := by
      rw [← hMcard]
      exact (Subgroup.card_subgroup_dvd_card _).trans hcard
    have hMp : IsPGroup p ((CFSG.pCore p ↥N).map N.subtype) := IsPGroup.of_card hMcard
    by_cases hp2 : p = 2
    · subst hp2
      have hMle : (CFSG.pCore 2 ↥N).map N.subtype ≤ CFSG.pCore 2 Q :=
        le_sSup (⟨hMn, hMp⟩ : (CFSG.pCore 2 ↥N).map N.subtype ∈
          {K : Subgroup Q | K.Normal ∧ IsPGroup 2 K})
      rw [hO2] at hMle
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hy : (x : Q) ∈ (CFSG.pCore 2 ↥N).map N.subtype :=
        Subgroup.mem_map_of_mem _ hx
      have h1 := hMle hy
      rw [Subgroup.mem_bot] at h1
      rw [h1]
      exact Subgroup.one_mem _
    · have hmem := pow_mem_of_dvd_20160 hp hp2 hMdvd
      have hle := le_center_of_card_mem hA hperf hcard
        ((CFSG.pCore p ↥N).map N.subtype) (by rw [hMcard]; exact hmem)
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact hle (Subgroup.mem_map_of_mem _ hx)
  have hF : CFSG.fittingSubgroup ↥N ≤ (Subgroup.center Q).subgroupOf N := by
    rw [CFSG.fitting_eq_sup_pCore ↥N]
    refine iSup_le fun p => hcore p.1.1 (Nat.prime_of_mem_primeFactors p.1.2) ?_
    exact Nat.dvd_of_mem_primeFactors p.1.2
  intro x hx
  have hxC : (⟨x, hx⟩ : ↥N) ∈ Subgroup.centralizer (CFSG.fittingSubgroup ↥N : Set ↥N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfZ : (f : Q) ∈ Subgroup.center Q := Subgroup.mem_subgroupOf.mp (hF hf)
    rw [Subgroup.mem_center_iff] at hfZ
    apply Subtype.ext
    show (f : Q) * x = x * (f : Q)
    exact (hfZ x).symm
  have hxF := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hxC
  exact Subgroup.mem_subgroupOf.mp (hF hxF)

theorem isQuasisimple_of_perfect_of_card_dvd_20160 (hA : ActsTriviallyStmt) {Q : Type}
    [Group Q] [Finite Q] [Nontrivial Q] (hperf : commutator Q = ⊤) (hO2 : CFSG.pCore 2 Q = ⊥)
    (hsol : ∀ N : Subgroup Q, N.Normal → N ≠ ⊤ → Group.IsSolvable ↥N)
    (hcard : Nat.card Q ∣ 20160) : CFSG.GorensteinWalter.IsQuasisimple Q := by
  classical
  have hnorm : ∀ N : Subgroup Q, N.Normal → N ≠ ⊤ → N ≤ Subgroup.center Q :=
    fun N hN hNt => by
      have := hN
      exact le_center_of_normal_ne_top hA hperf hO2 hsol hcard N hNt
  have hZtop : Subgroup.center Q ≠ ⊤ := by
    intro hZ
    have h1 : commutator Q = ⊥ := (commutator_eq_bot_iff_center_eq_top Q).2 hZ
    rw [hperf, eq_bot_iff_forall] at h1
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    exact hx (h1 x (Subgroup.mem_top x))
  have hnt : Nontrivial (Q ⧸ Subgroup.center Q) := QuotientGroup.nontrivial_iff.2 hZtop
  refine ⟨inferInstance, hperf, ?_⟩
  refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun K hK => ?_ }
  have hsurj := QuotientGroup.mk'_surjective (Subgroup.center Q)
  have hKK : (K.comap (QuotientGroup.mk' (Subgroup.center Q))).map
      (QuotientGroup.mk' (Subgroup.center Q)) = K :=
    Subgroup.map_comap_eq_self_of_surjective hsurj K
  by_cases htop : K.comap (QuotientGroup.mk' (Subgroup.center Q)) = ⊤
  · right
    rw [← hKK, htop, Subgroup.map_top_of_surjective _ hsurj]
  · left
    have hle : K.comap (QuotientGroup.mk' (Subgroup.center Q)) ≤ Subgroup.center Q :=
      hnorm _ (Subgroup.Normal.comap hK _) htop
    have hcle : Subgroup.center Q ≤ K.comap (QuotientGroup.mk' (Subgroup.center Q)) := by
      intro x hx
      rw [Subgroup.mem_comap]
      have h1 : QuotientGroup.mk' (Subgroup.center Q) x = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff x).2 hx
      rw [h1]
      exact K.one_mem
    have heq := le_antisymm hle hcle
    rw [← hKK, heq, QuotientGroup.map_mk'_self]

end CFSG.GH74.QTGen4
