module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

open Subgroup

section Perm

variable {p : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem eq_bot_of_pCycle_mem_normalizer (hp : p.Prime) (hcard : Fintype.card Ω = p)
    {c : Equiv.Perm Ω} (hc1 : c ≠ 1) (hcp : c ^ p = 1) {N : Subgroup (Equiv.Perm Ω)}
    (hN : p.Coprime (Nat.card N)) (hcN : c ∈ normalizer (N : Set (Equiv.Perm Ω))) : N = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf c = Fintype.card Ω := by
    rw [hcard]
    exact orderOf_eq_prime hcp hc1
  have hcyc : c.IsCycle := Equiv.Perm.isCycle_of_prime_order'' (hcard ▸ hp) hord
  have hmoved : ∀ x : Ω, c x ≠ x := by
    intro x
    have hsupp : c.support = Finset.univ := by
      refine Finset.eq_univ_of_card _ ?_
      rw [← hcyc.orderOf, hord]
    have : x ∈ c.support := by rw [hsupp]; exact Finset.mem_univ x
    simpa [Equiv.Perm.mem_support] using this
  set G : Subgroup (Equiv.Perm Ω) := N ⊔ zpowers c with hG
  have hNG : N ≤ G := le_sup_left
  have hcG : c ∈ G := (le_sup_right : zpowers c ≤ N ⊔ zpowers c) (mem_zpowers c)
  have hGN : G ≤ normalizer (N : Set (Equiv.Perm Ω)) :=
    sup_le le_normalizer ((zpowers_le).2 hcN)
  have hNnormal : (N.subgroupOf G).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNG).2 hGN
  haveI : MulAction.IsPretransitive G Ω := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨i, hi⟩ := hcyc.exists_zpow_eq (hmoved a) (hmoved b)
    exact ⟨⟨c ^ i, zpow_mem hcG i⟩, hi⟩
  haveI : MulAction.IsPreprimitive G Ω :=
    MulAction.IsPreprimitive.of_prime_card (by rw [Nat.card_eq_fintype_card, hcard]; exact hp)
  by_cases hfix : MulAction.fixedPoints (N.subgroupOf G) Ω = Set.univ
  ·
    rw [eq_bot_iff]
    intro n hn
    rw [mem_bot]
    ext x
    have hx : x ∈ MulAction.fixedPoints (N.subgroupOf G) Ω := by rw [hfix]; trivial
    have := hx ⟨⟨n, hNG hn⟩, hn⟩
    exact this
  ·
    exfalso
    haveI : MulAction.IsPretransitive (N.subgroupOf G) Ω :=
      MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfix
    obtain ⟨a⟩ : Nonempty Ω := Fintype.card_pos_iff.1 (by rw [hcard]; exact hp.pos)
    have horb : MulAction.orbit (N.subgroupOf G) a = Set.univ :=
      MulAction.orbit_eq_univ (N.subgroupOf G) a
    have h1 : Nat.card (MulAction.orbit (N.subgroupOf G) a) *
        Nat.card (MulAction.stabilizer (N.subgroupOf G) a) = Nat.card (N.subgroupOf G) := by
      rw [← Nat.card_prod,
        Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (N.subgroupOf G) a)]
    have h2 : p ∣ Nat.card (N.subgroupOf G) := by
      rw [← h1]
      refine Dvd.dvd.mul_right ?_ _
      have h3 : Nat.card (MulAction.orbit (N.subgroupOf G) a) = Nat.card Ω := by
        rw [horb]
        exact Nat.card_congr (Equiv.Set.univ Ω)
      rw [h3, Nat.card_eq_fintype_card, hcard]
    rw [Nat.card_congr (subgroupOfEquivOfLe hNG).toEquiv] at h2
    exact (hp.coprime_iff_not_dvd.1 hN) h2

end Perm

section Sections

variable {G H S : Type*} [Group G] [Group H] [Group S]

theorem simple_quotient_cases [IsSimpleGroup S] (φ : G →* H) (U : Subgroup G) (f : U →* S)
    (hf : Function.Surjective f) :
    (∃ (V : Subgroup G) (g : V →* S), V ≤ U ∧ V ≤ φ.ker ∧ Function.Surjective g) ∨
      ∃ (V : Subgroup H) (g : V →* S), Function.Surjective g := by
  classical
  let ψ : U →* H := φ.comp U.subtype
  have hfn : (ψ.ker.map f).Normal := ψ.normal_ker.map f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ψ.ker.map f) with hbot | htop
  · right
    have hker : ψ.rangeRestrict.ker ≤ f.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      intro u hu
      have : f u ∈ ψ.ker.map f := Subgroup.mem_map_of_mem f hu
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    let g : ψ.range →* S :=
      MonoidHom.liftOfSurjective ψ.rangeRestrict ψ.rangeRestrict_surjective ⟨f, hker⟩
    have hg : ∀ u, g (ψ.rangeRestrict u) = f u := fun u => by simp [g]
    refine ⟨ψ.range, g, fun s => ?_⟩
    obtain ⟨u, rfl⟩ := hf s
    exact ⟨ψ.rangeRestrict u, hg u⟩
  · left
    refine ⟨U ⊓ φ.ker, f.comp (Subgroup.inclusion inf_le_left), inf_le_left, inf_le_right,
      fun s => ?_⟩
    have hs : s ∈ ψ.ker.map f := by rw [htop]; exact Subgroup.mem_top s
    obtain ⟨u, hu, rfl⟩ := hs
    exact ⟨⟨u, u.2, hu⟩, rfl⟩

theorem false_of_central_pElements {p : ℕ} (hp : p.Prime) {M : Type*} [Group M] [Finite M]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (hdvd : p ∣ Nat.card S)
    (hcent : ∀ x : M, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ center M) (f : M →* S)
    (hf : Function.Surjective f) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p M) := inferInstance
  have hPc : ∀ x ∈ (P : Subgroup M), x ∈ center M := fun x hx => by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    exact hcent x ⟨k, congrArg Subtype.val hk⟩
  have hP : normalizer (P : Set M) ≤ centralizer (P : Set M) := fun n _ x hx =>
    (mem_center_iff.1 (hPc x hx) n).symm
  let τ := MonoidHom.transferSylow P hP
  have hndvd := MonoidHom.not_dvd_card_ker_transferSylow P hP
  have hfn : (τ.ker.map f).Normal := τ.normal_ker.map f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (τ.ker.map f) with hbot | htop
  ·
    have hpg : IsPGroup p S := fun s => by
      obtain ⟨m, rfl⟩ := hf s
      obtain ⟨k, hk⟩ := P.isPGroup' (τ m)
      refine ⟨k, ?_⟩
      have hm : m ^ (p ^ k) ∈ τ.ker := by
        rw [MonoidHom.mem_ker, map_pow]
        exact hk
      have : f (m ^ (p ^ k)) ∈ τ.ker.map f := Subgroup.mem_map_of_mem f hm
      rw [hbot, Subgroup.mem_bot] at this
      simpa using this
    haveI : Finite S := Finite.of_surjective f hf
    haveI : Group.IsNilpotent S := hpg.isNilpotent
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := S)).2 inferInstance a b)
  · apply hndvd
    have h1 : Nat.card (τ.ker.map f) ∣ Nat.card τ.ker := Subgroup.card_map_dvd τ.ker f
    rw [htop, Subgroup.card_top] at h1
    exact hdvd.trans h1

end Sections

section Solvable

theorem isSolvable_pi_of_finite {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, Group.IsSolvable (G i)] : Group.IsSolvable (∀ i, G i) := by
  cases nonempty_fintype ι
  have hle : ∀ k : ℕ, derivedSeries (∀ i, G i) k ≤
      Subgroup.pi Set.univ (fun i => derivedSeries (G i) k) := by
    intro k
    induction k with
    | zero =>
      simp only [derivedSeries_zero]
      rw [Subgroup.pi_top]
    | succ k ih =>
      rw [derivedSeries_succ]
      calc ⁅derivedSeries (∀ i, G i) k, derivedSeries (∀ i, G i) k⁆
          ≤ ⁅Subgroup.pi Set.univ (fun i => derivedSeries (G i) k),
              Subgroup.pi Set.univ (fun i => derivedSeries (G i) k)⁆ :=
            Subgroup.commutator_mono ih ih
        _ ≤ Subgroup.pi Set.univ (fun i => ⁅derivedSeries (G i) k, derivedSeries (G i) k⁆) :=
            Subgroup.commutator_pi_pi_le _ _
        _ = Subgroup.pi Set.univ (fun i => derivedSeries (G i) (k + 1)) := by
            simp_rw [derivedSeries_succ]
  choose n hn using fun i => (inferInstance : Group.IsSolvable (G i)).solvable
  refine ⟨⟨Finset.univ.sup n, ?_⟩⟩
  rw [eq_bot_iff]
  refine (hle _).trans ?_
  rw [le_bot_iff, Subgroup.pi_eq_bot_iff]
  intro i
  rw [eq_bot_iff, ← hn i]
  exact derivedSeries_antitone (G i) (Finset.le_sup (f := n) (Finset.mem_univ i))

end Solvable

end CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
