module

public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitStandard
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainTargetProduction
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.SolAltLit

open CFSG Subgroup
open scoped Pointwise commutatorElement

theorem alternating_nonabelian {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hZ : center (alternatingGroup (Fin n)) = ⊤ :=
    eq_top_iff.2 fun a _ => mem_center_iff.2 fun b => h b a
  rw [alternatingGroup.center_eq_bot (by simpa using hn)] at hZ
  have : Nontrivial (alternatingGroup (Fin n)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
  exact bot_ne_top hZ

theorem alternating_isPerfect {n : ℕ} (hn : 5 ≤ n) :
    Group.IsPerfect (alternatingGroup (Fin n)) := by
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  exact (LocalCores.isQuasisimple_of_isSimpleGroup (alternating_nonabelian (by omega))).1.1

section General

variable {X : Type*} [Group X] [Finite X]

theorem not_mem_of_le_centralizer {J : Subgroup X} {n : ℕ} (hn : 4 ≤ n)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) {y : X} (hy : orderOf y = 2)
    (hJy : J ≤ centralizer ({y} : Set X)) : y ∉ J := by
  intro hyJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set y' : J := ⟨y, hyJ⟩
  have hcen : y' ∈ center J := by
    rw [mem_center_iff]
    intro j
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hJy j.2))
  have hq : QuotientGroup.mk' (pPrimeCore 2 J) y' = 1 := by
    have h1 : e (QuotientGroup.mk' (pPrimeCore 2 J) y') ∈ center (alternatingGroup (Fin n)) := by
      rw [mem_center_iff]
      intro a
      obtain ⟨b, rfl⟩ := e.surjective a
      obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 J) b
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mem_center_iff.1 hcen j]
    rw [alternatingGroup.center_eq_bot (by simpa using hn), mem_bot] at h1
    exact e.injective (h1.trans e.map_one.symm)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
  have hdvd : orderOf y' ∣ Nat.card (pPrimeCore 2 J) := by
    have h := orderOf_dvd_natCard (⟨y', hq⟩ : pPrimeCore 2 J)
    rwa [Subgroup.orderOf_mk] at h
  rw [Subgroup.orderOf_mk, hy] at hdvd
  exact absurd (Nat.Coprime.eq_one_of_dvd (pPrimeCore_coprime_card (p := 2) (G := J)) hdvd)
    (by norm_num)

theorem le_centralizer_of_le_centralizer {t : X} {J : Subgroup X} {n : ℕ} (hn : 5 ≤ n)
    (hJC : J ≤ centralizer ({t} : Set X))
    (hJP : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set X))))
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n))
    {N : Subgroup X} (hJN : J ≤ normalizer (N : Set X))
    {E : Subgroup X} (hEJ : E ≤ J) (hE : ¬ E ≤ (pPrimeCore 2 J).map J.subtype)
    (hEN : E ≤ centralizer (N : Set X)) : J ≤ centralizer (N : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set X) with hCdef
  set A := centralizer (N : Set X) ⊓ J with hA
  have hconj : ∀ a ∈ A, ∀ j ∈ J, j * a * j⁻¹ ∈ A := by
    intro a ha j hj
    obtain ⟨haN, haJ⟩ := Subgroup.mem_inf.1 ha
    refine Subgroup.mem_inf.2 ⟨?_, J.mul_mem (J.mul_mem hj haJ) (J.inv_mem hj)⟩
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : j⁻¹ * x * j ∈ N := (mem_normalizer_iff''.1 (hJN hj) x).1 hx
    have hcomm := (mem_centralizer_iff.1 haN) _ hx'
    calc x * (j * a * j⁻¹) = j * ((j⁻¹ * x * j) * a) * j⁻¹ := by group
      _ = j * (a * (j⁻¹ * x * j)) * j⁻¹ := by rw [hcomm]
      _ = j * a * j⁻¹ * x := by group
  set π := QuotientGroup.mk' (pPrimeCore 2 J) with hπ
  have hAn : (A.subgroupOf J).Normal := by
    rw [normal_subgroupOf_iff inf_le_right]
    intro a j ha hj
    exact hconj a ha j hj
  have himg : (A.subgroupOf J).map π = ⊤ := by
    have hnorm : ((A.subgroupOf J).map π).Normal :=
      hAn.map π (QuotientGroup.mk'_surjective _)
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using hn)
    have : IsSimpleGroup (J ⧸ pPrimeCore 2 J) := e.isSimpleGroup
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exfalso
      apply hE
      intro x hx
      have hxA : (⟨x, hEJ hx⟩ : J) ∈ A.subgroupOf J := Subgroup.mem_inf.2 ⟨hEN hx, hEJ hx⟩
      have h1 : π ⟨x, hEJ hx⟩ = 1 := by
        have := Subgroup.mem_map_of_mem π hxA
        rwa [h, mem_bot] at this
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨⟨x, hEJ hx⟩, h1, rfl⟩
    · exact h
  set A' := A.subgroupOf C with hA'
  have hA'L : A' ≤ J.subgroupOf C := fun x hx => (Subgroup.mem_inf.1 hx).2
  have hsubL : (J.subgroupOf C).IsSubnormal := hJP.choose_spec.2.1
  have hA'sub : A'.IsSubnormal := by
    refine Subgroup.IsSubnormal.step A' (J.subgroupOf C) hA'L hsubL ?_
    rw [normal_subgroupOf_iff hA'L]
    intro a j ha hj
    exact hconj a ha j hj
  have hmap : A'.map (QuotientGroup.mk' (pPrimeCore 2 C)) =
      (J.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 C)) := by
    refine le_antisymm (map_mono hA'L) ?_
    rintro _ ⟨l, hl, rfl⟩
    have hlJ : (l : X) ∈ J := hl
    obtain ⟨a, ha, hla⟩ : ∃ a ∈ A.subgroupOf J, π a = π ⟨l, hlJ⟩ := by
      have hmem : π ⟨l, hlJ⟩ ∈ (A.subgroupOf J).map π := by rw [himg]; exact mem_top _
      obtain ⟨a, ha, h⟩ := hmem
      exact ⟨a, ha, h⟩
    have ho : a⁻¹ * ⟨l, hlJ⟩ ∈ pPrimeCore 2 J := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hla
      exact QuotientGroup.eq.1 hla
    have hoC : ((a : X)⁻¹ * l) ∈ (pPrimeCore 2 C).map C.subtype :=
      UGSChain.map_pPrimeCore_le_of_isPComponent hJC hJP ⟨_, ho, rfl⟩
    obtain ⟨o, ho', hoeq⟩ := hoC
    have haC : (a : X) ∈ C := hJC a.2
    refine ⟨⟨a, haC⟩, ha, ?_⟩
    have hl' : l = ⟨a, haC⟩ * o := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at hoeq ⊢
      rw [hoeq]
      group
    have h1 : QuotientGroup.mk' (pPrimeCore 2 C) o = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff o).2 ho'
    rw [hl', map_mul, h1, mul_one]
  have hEq := UnbalancedLayer.eq_of_le_of_map_eq hJP hA'L hA'sub hmap
  intro j hj
  have hjC : j ∈ C := hJC hj
  have hj' : (⟨j, hjC⟩ : C) ∈ A' := by rw [hEq]; exact hj
  exact (Subgroup.mem_inf.1 hj').1

omit [Finite X] in
theorem le_normalizer_map_subtype {K : Subgroup X} (H : Subgroup K) [H.Normal] :
    K ≤ normalizer ((H.map K.subtype : Subgroup X) : Set X) := by
  have h := Subgroup.le_normalizer_map (H := H) K.subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

omit [Finite X] in
theorem not_le_of_card_eq_four {E Q : Subgroup X} (hE : Nat.card E = 4)
    (hQ : Nat.Coprime 2 (Nat.card Q)) : ¬ E ≤ Q := by
  intro hEQ
  have h := Subgroup.card_dvd_of_le hEQ
  rw [hE] at h
  have h2 : 2 ∣ Nat.card Q := dvd_trans (by norm_num) h
  exact absurd (Nat.Coprime.eq_one_of_dvd hQ h2) (by norm_num)

theorem pPrimeCore_eq_bot_of_le_center (hS : SchurAlternatingMultiplierInput) {Q : Type*}
    [Group Q] [Finite Q] [Group.IsPerfect Q] {n : ℕ} (hn : 8 ≤ n)
    (e : Q ⧸ pPrimeCore 2 Q ≃* alternatingGroup (Fin n)) (hZ : pPrimeCore 2 Q ≤ center Q) :
    pPrimeCore 2 Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect (alternatingGroup (Fin n)) := alternating_isPerfect (by omega)
  set p : Q →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 Q)) with hpdef
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : p.ker = pPrimeCore 2 Q := by
    ext x
    rw [MonoidHom.mem_ker, hpdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨-, h, -, -, -, hmap, -⟩ :=
    RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier p hp
      (hker ▸ hZ)
  obtain ⟨-, hcard6⟩ := hS n (by omega)
  have hcard : Nat.card (RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin n))) = 2 := by
    rw [hcard6]
    split_ifs with h67
    · omega
    · rfl
  have : Finite (RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin n))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hle : Nat.card p.ker ≤ 2 := by
    rw [← hmap, ← hcard]
    exact Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective h _)
  have hodd : Nat.Coprime 2 (Nat.card p.ker) := hker ▸ pPrimeCore_coprime_card
  have hpos : 0 < Nat.card p.ker := Nat.card_pos
  have h1 : Nat.card p.ker = 1 := by
    rcases (show Nat.card p.ker = 1 ∨ Nat.card p.ker = 2 by omega) with h1 | h2
    · exact h1
    · rw [h2] at hodd
      norm_num at hodd
  rw [← hker]
  exact Subgroup.card_eq_one.1 h1

theorem conjugate_eq_of_centralizes_core {y : X} {J : Subgroup X}
    [IsSimpleGroup J] (hJ2 : 2 ∣ Nat.card J) (hJO : pPrimeCore 2 J = ⊥)
    (hnorm : centralizer ({y} : Set X) ≤ normalizer
      ((((pPrimeCore 2 (centralizer ({y} : Set X))).map (centralizer ({y} : Set X)).subtype ⊔
        J : Subgroup X)) : Set X))
    (hcent : J ≤ centralizer (((pPrimeCore 2 (centralizer ({y} : Set X))).map
      (centralizer ({y} : Set X)).subtype : Subgroup X) : Set X))
    {c : X} (hc : c ∈ centralizer ({y} : Set X)) : conjugate J c = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({y} : Set X) with hCdef
  set O : Subgroup X := (pPrimeCore 2 C).map C.subtype with hOdef
  set M : Subgroup X := O ⊔ J with hMdef
  have hOodd : Nat.Coprime 2 (Nat.card O) := by
    rw [hOdef, Subgroup.card_map_of_injective C.subtype_injective]
    exact pPrimeCore_coprime_card
  have hcomm : ∀ j ∈ J, ∀ o ∈ O, o * j = j * o := fun j hj o ho =>
    (mem_centralizer_iff.1 (hcent hj)) o ho
  have hJnO : J ≤ normalizer (O : Set X) := hcent.trans (centralizer_le_normalizer _)
  have hOJ : O ≤ centralizer (J : Set X) := le_centralizer_iff.1 hcent
  have hMJ : M ≤ normalizer (J : Set X) :=
    sup_le (hOJ.trans (centralizer_le_normalizer _)) le_normalizer
  have hOJbot : O ⊓ J = ⊥ := by
    have hN : ((O ⊓ J).subgroupOf J).Normal := by
      rw [normal_subgroupOf_iff inf_le_right]
      intro a j ha hj
      obtain ⟨haO, haJ⟩ := Subgroup.mem_inf.1 ha
      refine Subgroup.mem_inf.2 ⟨?_, J.mul_mem (J.mul_mem hj haJ) (J.inv_mem hj)⟩
      exact ((mem_normalizer_iff.1 (hJnO hj)) a).1 haO
    have hodd : Odd (Nat.card ((O ⊓ J).subgroupOf J)) := by
      have h1 : Nat.card ((O ⊓ J).subgroupOf J) = Nat.card ↥(O ⊓ J) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      rw [h1]
      have h2 : Nat.card ↥(O ⊓ J) ∣ Nat.card O := Subgroup.card_dvd_of_le inf_le_left
      exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h2 hOodd)
    have hle : (O ⊓ J).subgroupOf J ≤ pPrimeCore 2 J := by
      unfold pPrimeCore
      exact le_sSup ⟨hN, Nat.coprime_two_left.mpr hodd⟩
    rw [hJO] at hle
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, (Subgroup.mem_inf.1 hx).2⟩ : J) ∈ (O ⊓ J).subgroupOf J := hx
    exact congrArg Subtype.val (Subgroup.mem_bot.1 (hle hmem))
  have hinv : ∀ x ∈ M, x * x = 1 → x ∈ J := by
    intro x hx hx2
    have hxM : x ∈ ((O ⊔ J : Subgroup X) : Set X) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left O J hJnO] at hxM
    obtain ⟨o, ho, j, hj, rfl⟩ := hxM
    have hoj : o * j = j * o := hcomm j hj o ho
    have hsq : o * j * (o * j) = (o * o) * (j * j) := by
      calc o * j * (o * j) = o * (j * o) * j := by group
        _ = o * (o * j) * j := by rw [hoj]
        _ = (o * o) * (j * j) := by group
    rw [hsq] at hx2
    have h1 : o * o = (j * j)⁻¹ := eq_inv_of_mul_eq_one_left hx2
    have hoo : o * o ∈ O ⊓ J :=
      Subgroup.mem_inf.2 ⟨O.mul_mem ho ho, h1 ▸ J.inv_mem (J.mul_mem hj hj)⟩
    rw [hOJbot, mem_bot] at hoo
    have hdo : orderOf o ∣ Nat.card O := by
      have h := orderOf_dvd_natCard (⟨o, ho⟩ : O)
      rwa [Subgroup.orderOf_mk] at h
    have hd2 : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hoo)
    have ho1 : o = 1 := orderOf_eq_one_iff.1
      ((Nat.Coprime.coprime_dvd_left hd2 hOodd).eq_one_of_dvd hdo)
    show o * j ∈ J
    rw [ho1, one_mul]
    exact hj
  have hJcM : conjugate J c ≤ M := by
    rw [← conjugate_eq_of_mem_normalizer (hnorm hc)]
    exact Subgroup.map_mono le_sup_right
  obtain ⟨j₀, hj₀o⟩ := exists_prime_orderOf_dvd_card' 2 hJ2
  have hj₀2 : orderOf (j₀ : X) = 2 := by rw [Subgroup.orderOf_coe, hj₀o]
  set x := c⁻¹ * (j₀ : X) * c with hx
  have hxc : x ∈ conjugate J c := by
    rw [mem_conjugate_iff_conj, hx, show c * (c⁻¹ * (j₀ : X) * c) * c⁻¹ = j₀ by group]
    exact j₀.2
  have hj₀sq : (j₀ : X) * j₀ = 1 := by rw [← pow_two, ← hj₀2, pow_orderOf_eq_one]
  have hx2 : x * x = 1 := by
    rw [hx, show c⁻¹ * (j₀ : X) * c * (c⁻¹ * j₀ * c) = c⁻¹ * ((j₀ : X) * j₀) * c by group,
      hj₀sq]
    group
  have hxJ : x ∈ J := hinv x (hJcM hxc) hx2
  have hx1 : x ≠ 1 := by
    intro h1
    rw [hx, show c⁻¹ * (j₀ : X) * c = 1 ↔ (j₀ : X) = 1 by
      constructor
      · intro h
        have : (j₀ : X) = c * (c⁻¹ * j₀ * c) * c⁻¹ := by group
        rw [this, h]
        group
      · intro h
        rw [h]
        group] at h1
    rw [h1, orderOf_one] at hj₀2
    norm_num at hj₀2
  have : IsSimpleGroup (conjugate J c) :=
    (J.equivMapOfInjective _ (MulAut.conj c⁻¹).injective).symm.isSimpleGroup
  have hNorm : ((J ⊓ conjugate J c).subgroupOf (conjugate J c)).Normal := by
    rw [normal_subgroupOf_iff inf_le_right]
    intro a b ha hb
    obtain ⟨haJ, haJc⟩ := Subgroup.mem_inf.1 ha
    refine Subgroup.mem_inf.2 ⟨((mem_normalizer_iff.1 (hMJ (hJcM hb))) a).1 haJ, ?_⟩
    exact (conjugate J c).mul_mem ((conjugate J c).mul_mem hb haJc) ((conjugate J c).inv_mem hb)
  have hle : conjugate J c ≤ J := by
    rcases hNorm.eq_bot_or_eq_top with h | h
    · exfalso
      have hmem : (⟨x, hxc⟩ : conjugate J c) ∈
          (J ⊓ conjugate J c).subgroupOf (conjugate J c) := Subgroup.mem_inf.2 ⟨hxJ, hxc⟩
      rw [h, mem_bot] at hmem
      exact hx1 (congrArg Subtype.val hmem)
    · intro z hz
      have hmem : (⟨z, hz⟩ : conjugate J c) ∈
          (J ⊓ conjugate J c).subgroupOf (conjugate J c) := by
        rw [h]
        exact mem_top _
      exact (Subgroup.mem_inf.1 hmem).1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [conjugate, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]

end General

end CFSG.ComponentClassification.SolAltLit
