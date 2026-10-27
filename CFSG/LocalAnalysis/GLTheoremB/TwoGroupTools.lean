module

public import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics

public section

namespace CFSG.LocalAnalysis.GLTheoremB

section PGroup

variable {Q : Type*} [Group Q]

theorem isPGroup_sup_of_commute {q : ℕ} {A B : Subgroup Q} (hA : IsPGroup q ↥A)
    (hB : IsPGroup q ↥B) (hAB : A ≤ Subgroup.centralizer (B : Set Q)) : IsPGroup q ↥(A ⊔ B) := by
  intro z
  obtain ⟨a, ha, b, hb, hz⟩ := exists_mul_of_mem_sup hAB z.2
  obtain ⟨m, hm⟩ := hA ⟨a, ha⟩
  obtain ⟨n, hn⟩ := hB ⟨b, hb⟩
  have hm' : a ^ (q ^ m) = 1 := congrArg Subtype.val hm
  have hn' : b ^ (q ^ n) = 1 := congrArg Subtype.val hn
  have hcomm : Commute a b := ((Subgroup.mem_centralizer_iff.1 (hAB ha)) b hb).symm
  refine ⟨m + n, Subtype.ext ?_⟩
  show (z : Q) ^ (q ^ (m + n)) = 1
  rw [hz, hcomm.mul_pow]
  have h1 : a ^ (q ^ (m + n)) = 1 := by
    rw [pow_add, pow_mul, hm', one_pow]
  have h2 : b ^ (q ^ (m + n)) = 1 := by
    rw [add_comm, pow_add, pow_mul, hn', one_pow]
  rw [h1, h2, one_mul]

omit [Group Q] in
theorem isPGroup_bot' {q : ℕ} [Group Q] : IsPGroup q ↥(⊥ : Subgroup Q) := fun g =>
  ⟨0, by
    have : g = 1 := Subsingleton.elim g 1
    simp [this]⟩

theorem isPGroup_iSup_of_pairwise {q : ℕ} {ι : Type*} [Finite ι] (S : ι → Subgroup Q)
    (h2 : ∀ i, IsPGroup q ↥(S i)) (hpair : ∀ i j, S i = S j ∨ ⁅S i, S j⁆ = ⊥) :
    IsPGroup q ↥(⨆ i, S i) := by
  classical
  have := Fintype.ofFinite ι
  rw [← Finset.sup_univ_eq_iSup]
  have key : ∀ s : Finset ι, IsPGroup q ↥(s.sup S) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sup_empty]
      exact isPGroup_bot'
    | insert j s hj ih =>
      rw [Finset.sup_insert]
      by_cases hex : ∃ i ∈ s, S i = S j
      · obtain ⟨i, his, hij⟩ := hex
        have : S j ≤ s.sup S := hij ▸ Finset.le_sup (f := S) his
        rw [sup_eq_right.2 this]
        exact ih
      · push Not at hex
        refine isPGroup_sup_of_commute (h2 j) ih ?_
        refine Subgroup.le_centralizer_iff.2 (Finset.sup_le fun i hi => ?_)
        rcases hpair i j with h | h
        · exact absurd h (hex i hi)
        · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  exact key Finset.univ

theorem le_of_perfect_of_le_sup_pGroup [Finite Q] {q : ℕ} [Fact q.Prime] {H T K : Subgroup Q}
    (hH : ⁅H, H⁆ = H) (hTH : T ≤ H) (hTn : (T.subgroupOf H).Normal) (hKH : K ≤ H)
    (hK : IsPGroup q ↥K) (hHTK : H ≤ T ⊔ K) : H ≤ T := by
  have hperf : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.2 hH
  set T' : Subgroup ↥H := T.subgroupOf H with hT'
  set K' : Subgroup ↥H := K.subgroupOf H with hK'
  have hsup : T' ⊔ K' = ⊤ := by
    rw [hT', hK', ← Subgroup.subgroupOf_sup hTH hKH]
    exact Subgroup.subgroupOf_eq_top.2 hHTK
  have hperfq : Group.IsPerfect (↥H ⧸ T') :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' T') (QuotientGroup.mk'_surjective T')
  have hq : IsPGroup q (↥H ⧸ T') := by
    intro z
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
    have hh : h ∈ T' ⊔ K' := hsup ▸ Subgroup.mem_top h
    obtain ⟨t, ht, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hh
    obtain ⟨n, hn⟩ := hK ⟨(k : Q), (Subgroup.mem_subgroupOf).1 hk⟩
    refine ⟨n, ?_⟩
    have h1 : (k : Q) ^ (q ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hkn : k ^ (q ^ n) = 1 := Subtype.ext (by simpa using h1)
    have e : (QuotientGroup.mk (t * k) : ↥H ⧸ T') = QuotientGroup.mk k := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff t).2 ht, one_mul]
    rw [e, ← QuotientGroup.mk_pow, hkn]
    rfl
  have hsub : Subsingleton (↥H ⧸ T') := by
    by_contra hns
    have : Nontrivial (↥H ⧸ T') := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isNilpotent (↥H ⧸ T') hq.isNilpotent
  intro h hh
  have : (QuotientGroup.mk (⟨h, hh⟩ : ↥H) : ↥H ⧸ T') = QuotientGroup.mk 1 := Subsingleton.elim _ _
  have h2 := (QuotientGroup.eq).1 this
  simpa using (Subgroup.mem_subgroupOf).1 h2

end PGroup

section QuotAction

variable {Q : Type*} [Group Q] {Γ : Type*} [Group Γ]

@[expose] noncomputable def quotAutHom (N : Subgroup Q) [N.Normal] (ρ : Γ →* MulAut Q)
    (hρ : ∀ γ, N.map (ρ γ).toMonoidHom = N) : Γ →* MulAut (Q ⧸ N) where
  toFun γ := QuotientGroup.congr N N (ρ γ) (hρ γ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | H z => ?_
    show QuotientGroup.congr N N (ρ 1) (hρ 1) (QuotientGroup.mk z) = QuotientGroup.mk z
    rw [QuotientGroup.congr_mk N N (ρ 1) (hρ 1) z, map_one]
    rfl
  map_mul' γ δ := by
    ext x
    induction x using QuotientGroup.induction_on with | H z => ?_
    show QuotientGroup.congr N N (ρ (γ * δ)) (hρ _) (QuotientGroup.mk z) =
      QuotientGroup.congr N N (ρ γ) (hρ γ)
        (QuotientGroup.congr N N (ρ δ) (hρ δ) (QuotientGroup.mk z))
    rw [QuotientGroup.congr_mk N N (ρ (γ * δ)) (hρ _) z, QuotientGroup.congr_mk N N (ρ δ) (hρ δ) z,
      QuotientGroup.congr_mk N N (ρ γ) (hρ γ) _, map_mul]
    rfl

theorem quotAutHom_mk (N : Subgroup Q) [N.Normal] (ρ : Γ →* MulAut Q)
    (hρ : ∀ γ, N.map (ρ γ).toMonoidHom = N) (γ : Γ) (x : Q) :
    quotAutHom N ρ hρ γ (QuotientGroup.mk x) = QuotientGroup.mk (ρ γ x) :=
  QuotientGroup.congr_mk N N (ρ γ) (hρ γ) x

end QuotAction

end CFSG.LocalAnalysis.GLTheoremB
