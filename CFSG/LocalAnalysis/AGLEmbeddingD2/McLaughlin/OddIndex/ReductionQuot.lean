module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.ReductionGroup

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open

variable {N : Type} [Group N] [Finite N]

instance redKer_normal (X I : Subgroup N) [I.Normal] : ((X ⊓ I).subgroupOf X).Normal := by
  have h : (X ⊓ I).subgroupOf X = I.subgroupOf X := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [h]
  exact Subgroup.Normal.subgroupOf inferInstance X

abbrev Red (X I : Subgroup N) [I.Normal] : Type := ↥X ⧸ (X ⊓ I).subgroupOf X

@[expose] def redMk (X I : Subgroup N) [I.Normal] : ↥X →* Red X I := QuotientGroup.mk' _

omit [Finite N] in
theorem redMk_surjective (X I : Subgroup N) [I.Normal] : Function.Surjective (redMk X I) :=
  QuotientGroup.mk'_surjective _

omit [Finite N] in
theorem redMk_eq_one_iff (X I : Subgroup N) [I.Normal] (x : ↥X) :
    redMk X I x = 1 ↔ (x : N) ∈ I := by
  unfold redMk
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simp

theorem card_ker_redMk_coprime (X : Subgroup N) :
    Nat.Coprime 3 (Nat.card (redMk X (CFSG.pPrimeCore 3 N)).ker) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : (redMk X (CFSG.pPrimeCore 3 N)).ker = (X ⊓ CFSG.pPrimeCore 3 N).subgroupOf X := by
    unfold redMk
    exact QuotientGroup.ker_mk' _
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  exact (CFSG.pPrimeCore_coprime_card (p := 3) (G := N)).coprime_dvd_right
    (Subgroup.card_dvd_of_le inf_le_right)

theorem red_isCyclic {X : Subgroup N}
    (hcyc : ∀ R : Subgroup N, IsPGroup 3 R → IsCyclic R) (R : Subgroup (Red X (CFSG.pPrimeCore 3 N)))
    (hR : IsPGroup 3 R) : IsCyclic ↥R := by
  obtain ⟨L, hL, ⟨e⟩⟩ := CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup 3
    Nat.prime_three (redMk X (CFSG.pPrimeCore 3 N)) (redMk_surjective _ _)
    (card_ker_redMk_coprime X) R hR
  have hLN : IsCyclic ↥(L.map X.subtype) := hcyc _ (hL.map _)
  have e2 : L ≃* L.map X.subtype := Subgroup.equivMapOfInjective L X.subtype X.subtype_injective
  have hLc : IsCyclic ↥L := isCyclic_of_surjective e2.symm.toMonoidHom e2.symm.surjective
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem exists_ne_one_of_card_three {A : Subgroup N} (hA : Nat.card A = 3) :
    ∃ a ∈ A, a ≠ 1 ∧ orderOf a = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (by rw [hA])
  refine ⟨a, a.2, ?_, (Subgroup.orderOf_coe a).trans ha⟩
  intro h1
  have : orderOf (a : N) = 1 := by rw [h1, orderOf_one]
  rw [(Subgroup.orderOf_coe a).trans ha] at this
  omega

theorem red_isSimple {X A : Subgroup N} [X.Normal]
    (hcyc : ∀ R : Subgroup N, IsPGroup 3 R → IsCyclic R) (hA : Nat.card A = 3) (hAX : A ≤ X)
    (hX : X ≤ Subgroup.normalClosure (A : Set N)) :
    IsSimpleGroup (Red X (CFSG.pPrimeCore 3 N)) := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I : Subgroup N := CFSG.pPrimeCore 3 N with hI
  have hcop : Nat.Coprime 3 (Nat.card I) := CFSG.pPrimeCore_coprime_card
  have hdisj : Disjoint A I := Subgroup.disjoint_of_coprime_natCard (by rw [hA]; exact hcop)
  obtain ⟨a, haA, ha1, -⟩ := exists_ne_one_of_card_three hA
  have hnt : Nontrivial (Red X I) := by
    refine ⟨⟨redMk X I ⟨a, hAX haA⟩, 1, fun h => ?_⟩⟩
    have haI : a ∈ I := (redMk_eq_one_iff X I ⟨a, hAX haA⟩).mp h
    exact ha1 (Subgroup.mem_bot.mp (hdisj.le_bot ⟨haA, haI⟩))
  refine @IsSimpleGroup.mk _ _ hnt (fun M hM => ?_)
  set Mt : Subgroup ↥X := M.comap (redMk X I) with hMt
  have hMtn : Mt.Normal := Subgroup.Normal.comap hM _
  set M' : Subgroup N := Mt.map X.subtype with hM'
  have hM'X : M' ≤ X := Subgroup.map_subtype_le _
  have hMdvd : Nat.card M ∣ Nat.card Mt := by
    have hs : Function.Surjective ((redMk X I).subgroupMap Mt) :=
      MonoidHom.subgroupMap_surjective _ Mt
    have h1 : Mt.map (redMk X I) = M := Subgroup.map_comap_eq_self_of_surjective (redMk_surjective X I) M
    have h2 := Subgroup.card_dvd_of_surjective hs
    rwa [h1] at h2
  by_cases hM3 : 3 ∣ Nat.card M
  · right
    have hMt3 : 3 ∣ Nat.card Mt := hM3.trans hMdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Mt) 3 hMt3
    set gN : N := (((g : ↥X)) : N) with hgN
    have hgord : orderOf gN = 3 := by
      rw [hgN, Subgroup.orderOf_coe (g : ↥X), Subgroup.orderOf_coe g, hg]
    set B : Subgroup N := Subgroup.zpowers gN with hB
    have hBc : Nat.card B = 3 := by rw [hB, Nat.card_zpowers, hgord]
    have hgM' : gN ∈ M' := Subgroup.mem_map.mpr ⟨(g : ↥X), g.2, rfl⟩
    have hBM' : B ≤ M' := Subgroup.zpowers_le.mpr hgM'
    have hBX : B ≤ X := hBM'.trans hM'X
    have hconj : ∀ x ∈ X, ∀ m ∈ M', x * m * x⁻¹ ∈ M' := by
      intro x hx m hm
      obtain ⟨m', hm', rfl⟩ := Subgroup.mem_map.mp hm
      refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * m' * ⟨x, hx⟩⁻¹, hMtn.conj_mem m' hm' _, ?_⟩
      rfl
    have hall : ∀ g : N, A.map (MulAut.conj g).toMonoidHom ≤ M' := by
      intro g
      have hCX : A.map (MulAut.conj g).toMonoidHom ≤ X := by
        rintro _ hy
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
        exact Subgroup.Normal.conj_mem inferInstance z (hAX hz) g
      have hCc : Nat.card (A.map (MulAut.conj g).toMonoidHom) = 3 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA]
      obtain ⟨x, hx, hxB⟩ := exists_conj_mem_of_card_eq (p := 3) hcyc hAX hBX hA hBc
      obtain ⟨y, hy, hyC⟩ := exists_conj_mem_of_card_eq (p := 3) hcyc hAX hCX hA hCc
      rintro _ hz
      rw [hyC] at hz
      obtain ⟨z, hzA, rfl⟩ := Subgroup.mem_map.mp hz
      have hxz : x * z * x⁻¹ ∈ B := by
        rw [hxB]; exact Subgroup.mem_map.mpr ⟨z, hzA, rfl⟩
      have := hconj (y * x⁻¹) (X.mul_mem hy (X.inv_mem hx)) _ (hBM' hxz)
      simpa [MulAut.conj_apply, mul_assoc] using this
    have hXM' : X ≤ M' := by
      refine hX.trans ?_
      unfold Subgroup.normalClosure
      rw [Subgroup.closure_le]
      intro z hz
      obtain ⟨a', ha', hconjz⟩ := Group.mem_conjugatesOfSet_iff.mp hz
      obtain ⟨c, hc⟩ := isConj_iff.mp hconjz
      exact hall c ⟨a', ha', by simpa [MulAut.conj_apply] using hc⟩
    rw [eq_top_iff]
    intro k _
    obtain ⟨x, rfl⟩ := redMk_surjective X I k
    have : (x : N) ∈ M' := hXM' x.2
    obtain ⟨m', hm', hmx⟩ := Subgroup.mem_map.mp this
    have : m' = x := Subtype.ext hmx
    subst this
    exact hm'
  · left
    have hMt3 : ¬ 3 ∣ Nat.card Mt := by
      intro hMt3
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Mt) 3 hMt3
      have hgM : redMk X I (g : ↥X) ∈ M := g.2
      have hord : orderOf (redMk X I (g : ↥X)) ∣ 3 := by
        have := orderOf_map_dvd (redMk X I) (g : ↥X)
        rwa [Subgroup.orderOf_coe g, hg] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h1
      · rw [orderOf_eq_one_iff] at h1
        have hgI : ((g : ↥X) : N) ∈ I := (redMk_eq_one_iff X I _).mp h1
        have h3I : 3 ∣ Nat.card I := by
          have := orderOf_dvd_natCard (⟨((g : ↥X) : N), hgI⟩ : I)
          rwa [show orderOf (⟨((g : ↥X) : N), hgI⟩ : I) = 3 by
            rw [Subgroup.orderOf_mk]
            rw [Subgroup.orderOf_coe (g : ↥X), Subgroup.orderOf_coe g, hg]] at this
        exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3I) (by norm_num)
      · apply hM3
        have := orderOf_dvd_natCard (⟨redMk X I (g : ↥X), hgM⟩ : M)
        rwa [show orderOf (⟨redMk X I (g : ↥X), hgM⟩ : M) = 3 by
          rw [Subgroup.orderOf_mk]; exact h1] at this
    have hMsub : (M'.subgroupOf X) = Mt := Subgroup.comap_map_eq_self_of_injective X.subtype_injective Mt
    have hM'c : Nat.Coprime 3 (Nat.card M') := by
      rw [hM', Subgroup.card_map_of_injective X.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hMt3
    have hM'I : M' ≤ I :=
      le_pPrimeCore_of_normal_normal (p := 3) inferInstance hM'X (by rw [hMsub]; exact hMtn) hM'c
    rw [eq_bot_iff]
    intro k hk
    obtain ⟨x, rfl⟩ := redMk_surjective X I k
    have hxMt : x ∈ Mt := hk
    have : (x : N) ∈ I := hM'I (Subgroup.mem_map.mpr ⟨x, hxMt, rfl⟩)
    exact (Subgroup.mem_bot).mpr ((redMk_eq_one_iff X I x).mpr this)

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
