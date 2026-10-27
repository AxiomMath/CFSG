module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem index_dvd_card_of_forall_mul {M : Type} [Group M] (Z' N' : Subgroup M)
    (h : ∀ m : M, ∃ z ∈ Z', ∃ n ∈ N', m = z * n) : N'.index ∣ Nat.card Z' := by
  have : MulAction.IsPretransitive Z' (M ⧸ N') := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with | _ a => ?_
    induction b using QuotientGroup.induction_on with | _ b => ?_
    obtain ⟨z0, hz0, n0, hn0, rfl⟩ := h b
    obtain ⟨z1, hz1, n1, hn1, rfl⟩ := h a
    refine ⟨⟨z0 * z1⁻¹, Z'.mul_mem hz0 (Z'.inv_mem hz1)⟩, ?_⟩
    show ((z0 * z1⁻¹ * (z1 * n1) : M) : M ⧸ N') = ((z0 * n0 : M) : M ⧸ N')
    rw [QuotientGroup.eq]
    have : (z0 * z1⁻¹ * (z1 * n1))⁻¹ * (z0 * n0) = n1⁻¹ * n0 := by group
    rw [this]
    exact N'.mul_mem (N'.inv_mem hn1) hn0
  have h1 := MulAction.index_stabilizer_of_transitive Z' (((1 : M) : M ⧸ N'))
  have h2 := Subgroup.index_dvd_card (MulAction.stabilizer Z' (((1 : M) : M ⧸ N')))
  rw [h1] at h2
  exact h2

theorem sylow_lift {p : ℕ} [Fact p.Prime] {M Z N₀ : Subgroup G} (hN₀M : N₀ ≤ M) (hZM : Z ≤ M)
    (hZn : M ≤ Subgroup.normalizer (Z : Set G)) (hZp : ¬ p ∣ Nat.card Z)
    (hM : M ≤ Z ⊔ N₀) {x : G} (hx : x ∈ M) {n : ℕ} (hxn : x ^ (p ^ n) = 1) :
    ∃ z ∈ Z, ∃ r ∈ N₀, (∃ k : ℕ, r ^ (p ^ k) = 1) ∧ x = z * r * z⁻¹ := by
  classical
  have hdecomp : ∀ g ∈ M, ∃ n' ∈ N₀, ∃ z' ∈ Z, g = n' * z' := by
    intro g hg
    have hle : N₀ ≤ Subgroup.normalizer (Z : Set G) := hN₀M.trans hZn
    have hmem : g ∈ N₀ ⊔ Z := by rw [sup_comm]; exact hM hg
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right N₀ Z hle] at hmem
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem
    exact ⟨a, ha, b, hb, rfl⟩
  set N' : Subgroup M := N₀.subgroupOf M with hN'
  set Z' : Subgroup M := Z.subgroupOf M with hZ'
  have hcardZ : Nat.card Z' = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv
  have hcardN : Nat.card N' = Nat.card N₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀M).toEquiv
  have hidx : N'.index ∣ Nat.card Z' := by
    apply index_dvd_card_of_forall_mul
    intro m
    obtain ⟨n', hn', z', hz', hmz⟩ := hdecomp m.1 m.2
    have hzn : n' * z' * n'⁻¹ ∈ Z := by
      have := hZn (hN₀M hn')
      rw [Subgroup.mem_normalizer_iff] at this
      exact (this z').1 hz' |> fun h => by simpa using h
    refine ⟨⟨n' * z' * n'⁻¹, ?_⟩, ?_, ⟨n', hN₀M hn'⟩, hn', ?_⟩
    · exact M.mul_mem (M.mul_mem (hN₀M hn') (hZM hz')) (M.inv_mem (hN₀M hn'))
    · exact hzn
    · apply Subtype.ext; simp [← hmz]
  have hndvd : ¬ p ∣ N'.index := fun h => hZp (hcardZ ▸ h.trans hidx)
  let T : Sylow p N' := default
  set P : Subgroup M := (T : Subgroup N').map N'.subtype with hP
  have hPp : IsPGroup p P := T.isPGroup'.map _
  have hPcard : Nat.card P = Nat.card T :=
    Subgroup.card_map_of_injective N'.subtype_injective
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  have hMN : Nat.card M = Nat.card N' * N'.index := (Subgroup.card_mul_index N').symm
  have hSP : (S : Subgroup M) = P := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hPS
    rw [hPcard, Sylow.card_eq_multiplicity S, Sylow.card_eq_multiplicity T, hMN,
      Nat.factorization_mul Nat.card_pos.ne' (Subgroup.index_ne_zero_of_finite),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]
  have hxM : (⟨x, hx⟩ : M) ^ (p ^ n) = 1 := Subtype.ext (by simpa using hxn)
  have hZp' : IsPGroup p (Subgroup.zpowers (⟨x, hx⟩ : M)) := by
    have := orderOf_dvd_of_pow_eq_one hxM
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).1 this
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hZp'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M S Q
  have hxQ : (⟨x, hx⟩ : M) ∈ (Q : Subgroup M) := hQ (Subgroup.mem_zpowers _)
  rw [← hg, Sylow.coe_subgroup_smul, hSP, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  rw [hP, Subgroup.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨t, ht⟩
  obtain ⟨n', hn', z', hz', hgz⟩ := hdecomp (g⁻¹ : M).1 (g⁻¹ : M).2
  have hx_eq : x = g.1 * t.1.1 * g.1⁻¹ := by
    have := congrArg Subtype.val hsx
    simpa [MulAut.conj_apply] using this.symm
  have hgz' : g.1 = z'⁻¹ * n'⁻¹ := by
    have : g.1 = ((g⁻¹ : M).1)⁻¹ := by simp
    rw [this, hgz]; group
  refine ⟨z'⁻¹, Z.inv_mem hz', n'⁻¹ * t.1.1 * n', ?_, ⟨k, ?_⟩, ?_⟩
  · have ht0 : t.1.1 ∈ N₀ := t.2
    exact N₀.mul_mem (N₀.mul_mem (N₀.inv_mem hn') ht0) hn'
  · have ht0 : t.1.1 ∈ N₀ := t.2
    have h1 : (n'⁻¹ * t.1.1 * n') ^ (p ^ k) = n'⁻¹ * t.1.1 ^ (p ^ k) * n' := by
      simpa using conj_pow (a := n'⁻¹) (b := t.1.1) (i := p ^ k)
    have h2 : t.1.1 ^ (p ^ k) = 1 := by
      have := congrArg (fun y : T => y.1.1.1) hk
      simpa using this
    rw [h1, h2]; group
  · rw [hx_eq, hgz']; group

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
