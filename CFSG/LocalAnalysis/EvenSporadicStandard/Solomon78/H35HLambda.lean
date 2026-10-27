module

public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterTransfer

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_cyclic_sylow_two {X : Type*} [Group X] [Finite X]
    (hcyc : ∀ P : Sylow 2 X, IsCyclic P) : Group.IsSolvable X := by
  classical
  by_cases hodd : Odd (Nat.card X)
  · exact CFSG.Milestones.odd_order_solvable hodd
  · have h2 : 2 ∣ Nat.card X := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    have hmin : (Nat.card X).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
    have hP : IsCyclic P := hcyc P
    have hc := hP.normalizer_le_centralizer hmin
    let f := MonoidHom.transferSylow P hc
    have hNodd : Odd (Nat.card f.ker) :=
      Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (MonoidHom.not_dvd_card_ker_transferSylow P hc))
    have hNsolv : Group.IsSolvable f.ker := CFSG.Milestones.odd_order_solvable hNodd
    have : Group.IsSolvable ↥(P : Subgroup X) := inferInstance
    have : Group.IsSolvable f.range := inferInstance
    exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])

private theorem isCyclic_of_isPGroup_of_injective {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (hcyc : ∀ Q : Sylow 2 Y, IsCyclic Q) {f : X →* Y} (hf : Function.Injective f)
    (hX : IsPGroup 2 X) : IsCyclic X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hX.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have := hcyc Q
  exact isCyclic_of_injective ((Subgroup.inclusion hQ).comp (MonoidHom.ofInjective hf).toMonoidHom)
    ((Subgroup.inclusion_injective hQ).comp (MonoidHom.ofInjective hf).injective)

private theorem isSolvable_of_card_le_four {A : Type*} [Group A] [Finite A] (h : Nat.card A ≤ 4) :
    Group.IsSolvable A := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  have key : ∃ p n : ℕ, p.Prime ∧ Nat.card A = p ^ n := by
    obtain h1 | h2 | h3 | h4 : Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 3 ∨ Nat.card A = 4 :=
      by omega
    · exact ⟨2, 0, Nat.prime_two, by simpa using h1⟩
    · exact ⟨2, 1, Nat.prime_two, by simpa using h2⟩
    · exact ⟨3, 1, Nat.prime_three, by simpa using h3⟩
    · exact ⟨2, 2, Nat.prime_two, by simpa using h4⟩
  obtain ⟨p, n, hp, hn⟩ := key
  have : Fact p.Prime := ⟨hp⟩
  have := (IsPGroup.of_card hn).isNilpotent
  infer_instance

theorem card_autCentralizer_le {L K : Subgroup G} (hout : OutTwo ↥L)
    (hC : Nat.card (centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) ≤ 2) :
    Nat.card (autCentralizer L K) ≤ 4 := by
  set A := autCentralizer L K with hA
  set I : Subgroup (MulAut ↥L) := A ⊓ (MulAut.conj : ↥L →* MulAut ↥L).range with hI
  have hfix : ∀ l : ↥L, MulAut.conj l ∈ A ↔
      l ∈ centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro l
    constructor
    · intro hl
      rw [mem_centralizer_iff]
      intro k hk
      have h1 : (MulAut.conj l) k = k := hl k (mem_subgroupOf.1 hk)
      rw [MulAut.conj_apply] at h1
      calc k * l = (l * k * l⁻¹) * l := by rw [h1]
        _ = l * k := by group
    · intro hl k hk
      have h1 : k * l = l * k := mem_centralizer_iff.1 hl k (mem_subgroupOf.2 hk)
      rw [MulAut.conj_apply]
      calc l * k * l⁻¹ = (k * l) * l⁻¹ := by rw [h1]
        _ = k := by group
  have hIcard : Nat.card I ≤ 2 := by
    have hsurj : Function.Surjective
        (fun l : centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) =>
          (⟨MulAut.conj (l : ↥L), (hfix l).2 l.2, l, rfl⟩ : I)) := by
      rintro ⟨α, hαA, l, rfl⟩
      exact ⟨⟨l, (hfix l).1 hαA⟩, rfl⟩
    exact (Nat.card_le_card_of_surjective _ hsurj).trans hC
  have hIA : I ≤ A := inf_le_left
  have hidx : Nat.card (A ⧸ I.subgroupOf A) ≤ 2 := by
    by_cases hall : ∀ α ∈ A, α ∈ I
    · have : Subsingleton (A ⧸ I.subgroupOf A) := by
        refine ⟨fun x y => ?_⟩
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
        rw [QuotientGroup.eq]
        exact mem_subgroupOf.2 (hall _ (mul_mem (inv_mem a.2) b.2))
      rw [Nat.card_unique]
      norm_num
    · push Not at hall
      obtain ⟨α₀, hα₀A, hα₀I⟩ := hall
      have hsurj : Function.Surjective (fun b : Bool =>
          if b then (QuotientGroup.mk (⟨α₀, hα₀A⟩ : A) : A ⧸ I.subgroupOf A)
          else QuotientGroup.mk 1) := by
        intro x
        obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective x
        have hα₀inn : ¬ ∃ l : ↥L, α₀ = MulAut.conj l := fun ⟨l, hl⟩ =>
          hα₀I ⟨hα₀A, l, hl.symm⟩
        rcases hout α₀ β with h | ⟨l, hl⟩ | ⟨l, hl⟩
        · exact absurd h hα₀inn
        · refine ⟨false, ?_⟩
          show QuotientGroup.mk 1 = QuotientGroup.mk β
          rw [QuotientGroup.eq]
          refine mem_subgroupOf.2 ⟨?_, l, hl.symm⟩
          simp
        · refine ⟨true, ?_⟩
          show QuotientGroup.mk ⟨α₀, hα₀A⟩ = QuotientGroup.mk β
          rw [QuotientGroup.eq]
          refine mem_subgroupOf.2 ⟨?_, l, hl.symm⟩
          simpa using mul_mem (inv_mem hα₀A) β.2
      exact (Nat.card_le_card_of_surjective _ hsurj).trans (by simp)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (I.subgroupOf A)
  have h2 : Nat.card (I.subgroupOf A) = Nat.card I :=
    Nat.card_congr (subgroupOfEquivOfLe hIA).toEquiv
  rw [h1, h2]
  calc Nat.card (A ⧸ I.subgroupOf A) * Nat.card I ≤ 2 * 2 := Nat.mul_le_mul hidx hIcard
    _ = 4 := by norm_num

theorem isSolvable_autCentralizer_of_card_le {L K : Subgroup G}
    (h : Nat.card (autCentralizer L K) ≤ 4) : Group.IsSolvable (autCentralizer L K) :=
  isSolvable_of_card_le_four h

@[expose] def lam (L K : Subgroup G) : Subgroup G :=
  normalizer (L : Set G) ⊓ centralizer (K : Set G)

private def lamAct (L K : Subgroup G) : lam L K →* autCentralizer L K :=
  ((normalizerMonoidHom L).comp
    (Subgroup.inclusion (inf_le_left : lam L K ≤ normalizer (L : Set G)))).codRestrict
      (autCentralizer L K) (by
    intro g k hk
    have h1 : (k : G) * g = g * k := mem_centralizer_iff.1 g.2.2 k hk
    apply Subtype.ext
    show (g : G) * k * (g : G)⁻¹ = k
    rw [← h1]
    group)

omit [Finite G] in
private lemma lamAct_coe (L K : Subgroup G) (g : lam L K) (l : L) :
    (((lamAct L K g : autCentralizer L K) : MulAut ↥L) l : G) = g * l * (g : G)⁻¹ := rfl

omit [Finite G] in
private lemma mem_centralizer_of_mem_ker {L K : Subgroup G} {g : lam L K}
    (hg : g ∈ (lamAct L K).ker) : (g : G) ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff]
  intro l hl
  have h := congrArg (fun α : autCentralizer L K => ((α : MulAut ↥L) ⟨l, hl⟩ : G))
    (MonoidHom.mem_ker.1 hg)
  simp only [lamAct_coe] at h
  have h' : (g : G) * l * (g : G)⁻¹ = l := h
  have h'' : (g : G) * l = l * g := by
    calc (g : G) * l = ((g : G) * l * (g : G)⁻¹) * g := by group
      _ = l * g := by rw [h']
  exact h''.symm

private def kerToCentralizer (L K : Subgroup G) :
    (lamAct L K).ker →* centralizer (L : Set G) where
  toFun g := ⟨(g : lam L K), mem_centralizer_of_mem_ker g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
private lemma kerToCentralizer_injective (L K : Subgroup G) :
    Function.Injective (kerToCentralizer L K) := by
  intro a b h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : centralizer (L : Set G) => (z : G)) h))

theorem lam_isSolvable {L K : Subgroup G}
    (hcyc : ∀ P : Sylow 2 (centralizer (L : Set G)), IsCyclic P)
    (hA : Group.IsSolvable (autCentralizer L K)) : Group.IsSolvable (lam L K) := by
  have hker : Group.IsSolvable (lamAct L K).ker := by
    refine isSolvable_of_cyclic_sylow_two fun P => ?_
    exact isCyclic_of_isPGroup_of_injective hcyc
      (f := (kerToCentralizer L K).comp (P : Subgroup (lamAct L K).ker).subtype)
      ((kerToCentralizer_injective L K).comp (P : Subgroup (lamAct L K).ker).subtype_injective)
      P.isPGroup'
  exact Group.isSolvable_of_ker_le_range (lamAct L K).ker.subtype (lamAct L K)
    (by rw [Subgroup.range_subtype])

theorem lam_elemAbelian_card_le_pow {L K : Subgroup G} {m : ℕ}
    (hcyc : ∀ P : Sylow 2 (centralizer (L : Set G)), IsCyclic P)
    (hA : twoAdic (autCentralizer L K) ≤ m) {E : Subgroup G} (hE : E ≤ lam L K)
    (h2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 * 2 ^ m := by
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using h2 x x.2)⟩
  let ψ : E →* autCentralizer L K := (lamAct L K).comp (Subgroup.inclusion hE)
  have hker : Nat.card ψ.ker ≤ 2 := by
    let ι : ψ.ker →* centralizer (L : Set G) :=
      { toFun := fun x => ⟨((x : E) : G), mem_centralizer_of_mem_ker
          (g := Subgroup.inclusion hE x) x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro a b h
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : centralizer (L : Set G) => (z : G)) h))
    have hcycker : IsCyclic ψ.ker :=
      isCyclic_of_isPGroup_of_injective hcyc hι (hEp.to_subgroup _)
    obtain ⟨g, hg⟩ := hcycker.exists_generator
    have hg2 : g ^ 2 = 1 := by
      have := h2 ((g : E) : G) (g : E).2
      apply Subtype.ext
      apply Subtype.ext
      simpa [pow_two] using this
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)
  have hrange : Nat.card ψ.range ≤ 2 ^ m := by
    have hpg : IsPGroup 2 ψ.range :=
      hEp.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    obtain ⟨n, hn⟩ := hpg.exists_card_eq
    have hdvd : Nat.card ψ.range ∣ Nat.card (autCentralizer L K) :=
      Subgroup.card_subgroup_dvd_card _
    have hle : n ≤ (Nat.card (autCentralizer L K)).factorization 2 := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne']
      rwa [hn] at hdvd
    have hn2 : n ≤ m := hle.trans hA
    rw [hn]
    exact Nat.pow_le_pow_right (by norm_num) hn2
  calc Nat.card E = Nat.card ψ.ker * Nat.card ψ.range :=
        (Subgroup.card_ker_mul_card_range ψ).symm
    _ ≤ 2 * 2 ^ m := Nat.mul_le_mul hker hrange

end CFSG.EvenSporadicStandard.Solomon78
