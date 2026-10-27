module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

namespace CFSG.OddSolvableUnitary

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement

variable {H : Type*} [Group H]

theorem isMulCommutative_map_subtype_iff {N : Subgroup H} (K : Subgroup N) :
    IsMulCommutative (K.map N.subtype) ↔ IsMulCommutative K := by
  let e := K.equivMapOfInjective N.subtype N.subtype_injective
  exact ⟨fun h => e.symm.surjective.isMulCommutative h, fun h => e.surjective.isMulCommutative h⟩

theorem le_of_le_centralizer {A B : Subgroup H}
    (hA : Maximal (fun B : Subgroup H => B.Normal ∧ IsMulCommutative B) A) (hBn : B.Normal)
    (hBc : IsMulCommutative B) (hBC : B ≤ centralizer (A : Set H)) : B ≤ A := by
  have hAn : A.Normal := hA.prop.1
  have hAA : A ≤ centralizer (A : Set H) := le_centralizer_iff_isMulCommutative.2 hA.prop.2
  have hBB : B ≤ centralizer (B : Set H) := le_centralizer_iff_isMulCommutative.2 hBc
  have hcomm : IsMulCommutative (A ⊔ B : Subgroup H) := by
    rw [sup_eq_closure]
    refine isMulCommutative_closure fun x hx y hy _ => ?_
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact mem_centralizer_iff.1 (hAA hy) x hx
    · exact (mem_centralizer_iff.1 (hBC hy) x hx)
    · exact (mem_centralizer_iff.1 (hBC hx) y hy).symm
    · exact mem_centralizer_iff.1 (hBB hy) x hx
  exact le_sup_right.trans (hA.2 ⟨Subgroup.sup_normal A B, hcomm⟩ le_sup_left)

theorem isMulCommutative_fittingSubgroup {G : Type*} [Group G] [Finite G]
    (h : ∀ r : ℕ, r.Prime → IsMulCommutative (pCore r G)) :
    IsMulCommutative (fittingSubgroup G) := by
  rw [fitting_eq_sup_pCore, iSup_eq_closure]
  refine isMulCommutative_closure fun x hx y hy _ => ?_
  obtain ⟨p, hxp⟩ := Set.mem_iUnion.1 hx
  obtain ⟨p', hyp⟩ := Set.mem_iUnion.1 hy
  by_cases hpp : p.1.1 = p'.1.1
  · rw [SetLike.mem_coe, hpp] at hxp
    have hle := le_centralizer_iff_isMulCommutative.2 (h p'.1.1 (Fact.out : p'.1.1.Prime))
    exact (mem_centralizer_iff.1 (hle hxp) y hyp).symm
  · exact commute_of_normal_of_disjoint _ _ pCore_normal pCore_normal
      (IsPGroup.disjoint_of_ne _ _ hpp _ _ pCore_isPGroup pCore_isPGroup) x y hxp hyp

theorem odd_solvable_cyclic_maximal_abelian_normal_extraspecial_obstruction [Finite H]
    (hsolv : Group.IsSolvable H) (hodd : Odd (Nat.card H)) {A : Subgroup H}
    (hA : Maximal (fun B : Subgroup H => B.Normal ∧ IsMulCommutative B) A) (hAcyc : IsCyclic A)
    (hlt : A < centralizer (A : Set H)) :
    ∃ (r a : ℕ) (D : Subgroup H), r.Prime ∧ Odd r ∧ 1 ≤ a ∧ D.Normal ∧
      D ≤ centralizer (A : Set H) ∧ Nat.card D = r ^ (1 + 2 * a) ∧ (∀ x ∈ D, x ^ r = 1) ∧
      center D = commutator D ∧ Nat.card (center D) = r := by
  have hAn : A.Normal := hA.prop.1
  set C := centralizer (A : Set H) with hCdef
  have hCn : C.Normal := normal_centralizer
  have key : ∀ B : Subgroup H, B.Normal → IsMulCommutative B → B ≤ C → B ≤ A :=
    fun B hBn hBc hBC => le_of_le_centralizer hA hBn hBc hBC
  obtain ⟨r, hr, hQc⟩ : ∃ r : ℕ, r.Prime ∧ ¬IsMulCommutative (pCore r C) := by
    by_contra! hall
    have hF := isMulCommutative_fittingSubgroup hall
    set F' := (fittingSubgroup C).map C.subtype
    have hF'A : F' ≤ A := key F' inferInstance
      ((isMulCommutative_map_subtype_iff _).2 hF) (map_subtype_le _)
    have htop : centralizer (fittingSubgroup C : Set C) = ⊤ := by
      refine eq_top_iff.2 fun c _ => mem_centralizer_iff.2 fun f hf => ?_
      have hfA : (f : H) ∈ A := hF'A ⟨f, hf, rfl⟩
      exact Subtype.ext (mem_centralizer_iff.1 c.2 _ hfA)
    have hFtop := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
      (inferInstance : Group.IsSolvable C)
    rw [htop] at hFtop
    exact not_le_of_gt hlt fun c hc => hF'A ⟨⟨c, hc⟩, hFtop (mem_top _), rfl⟩
  have : Fact r.Prime := ⟨hr⟩
  set Q := (pCore r C).map C.subtype with hQdef
  have hQn : Q.Normal := inferInstance
  have hQC : Q ≤ C := map_subtype_le _
  have hQp : IsPGroup r Q := (pCore_isPGroup (p := r) (G := C)).map C.subtype
  have hQnc : ¬IsMulCommutative Q := fun h => hQc ((isMulCommutative_map_subtype_iff _).1 h)
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hnt : Nontrivial Q := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      exact hQnc ⟨⟨fun x y => Subsingleton.elim _ _⟩⟩
    obtain ⟨n, hn, hcard⟩ := hQp.nontrivial_iff_card.1 hnt
    have h2 : 2 ∣ Nat.card H :=
      (dvd_pow_self 2 hn.ne').trans (hcard ▸ card_subgroup_dvd_card Q)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  obtain ⟨P, hPchar, hPΦ, -, hPcen⟩ := (thompson_critical_subgroup hQp).1
  have : P.Characteristic := hPchar
  set ι : P →* H := Q.subtype.comp P.subtype with hιdef
  have hι : Function.Injective ι := fun a b h => P.subtype_injective (Q.subtype_injective h)
  have hιC : ∀ x : P, ι x ∈ C := fun x => hQC (x : Q).2
  have hlift : ∀ K : Subgroup P, K.Characteristic → (K.map ι).Normal := by
    intro K hK
    rw [hιdef, ← map_map]
    infer_instance
  have hliftA : ∀ K : Subgroup P, K.Characteristic → IsMulCommutative K → ∀ x ∈ K, ι x ∈ A := by
    intro K hK hKc x hx
    refine key (K.map ι) (hlift K hK) ?_ ?_ ⟨x, hx, rfl⟩
    · rw [hιdef, ← map_map, isMulCommutative_map_subtype_iff, isMulCommutative_map_subtype_iff]
      exact hKc
    · rintro _ ⟨y, -, rfl⟩
      exact hιC y
  have hPnc : ¬IsMulCommutative P := by
    intro hPc
    have hPA : ∀ x : P, ι x ∈ A := fun x => hliftA ⊤ inferInstance
      ((Subgroup.topEquiv (G := P)).symm.surjective.isMulCommutative hPc) x (mem_top x)
    have htop : centralizer (P : Set Q) = ⊤ := by
      refine eq_top_iff.2 fun q _ => mem_centralizer_iff.2 fun y hy => ?_
      exact Subtype.ext (mem_centralizer_iff.1 (hQC q.2) _ (hPA ⟨y, hy⟩))
    rw [htop, inf_top_eq] at hPcen
    refine hQnc ⟨⟨fun q₁ q₂ => ?_⟩⟩
    have h₁ : q₁ ∈ P := hPcen ▸ mem_top q₁
    have h₂ : q₂ ∈ P := hPcen ▸ mem_top q₂
    have := hPc.is_comm.comm ⟨q₁, h₁⟩ ⟨q₂, h₂⟩
    exact congrArg Subtype.val this
  have hZPcyc : IsCyclic (center P) := by
    have hZA : ∀ x : center P, ι x ∈ A := fun x =>
      hliftA (center P) inferInstance inferInstance x x.2
    refine isCyclic_of_injective ((ι.comp (center P).subtype).codRestrict A hZA) ?_
    intro x y hxy
    exact Subtype.ext (hι (congrArg Subtype.val hxy :))
  have hΦ : frattini P ≤ center P := by
    intro x hx
    have hxc := (hPΦ ⟨x, hx, rfl⟩).2
    refine mem_center_iff.2 fun y => Subtype.ext ?_
    exact mem_centralizer_iff.1 hxc _ y.2
  obtain ⟨hPcomm, -, ⟨θ, hθ, hθker⟩, hset, hchar, hnt⟩ :=
    central_frattini_odd_power_map hr2 (hQp.to_subgroup P) hΦ
  set D₀ := omega₁ (G := P) (p := r) with hD₀
  have hmemD₀ : ∀ x : P, x ∈ D₀ ↔ x ^ r = 1 := fun x => by
    rw [← SetLike.mem_coe, hset, Set.mem_ofPred_eq]
  set D := D₀.map ι with hDdef
  have hDn : D.Normal := hlift D₀ hchar
  have hDC : D ≤ C := by
    rintro _ ⟨y, -, rfl⟩
    exact hιC y
  have hDexp : ∀ x ∈ D, x ^ r = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, (hmemD₀ y).1 hy, map_one]
  have hDnc : ¬IsMulCommutative D := by
    intro hDc
    have hDA : D ≤ A := key D hDn hDc hDC
    have hD₀Z : D₀ ≤ center P := by
      intro x hx
      refine mem_center_iff.2 fun y => hι ?_
      rw [map_mul, map_mul]
      exact (mem_centralizer_iff.1 (hιC y) _ (hDA ⟨x, hx, rfl⟩)).symm
    have : IsCyclic θ.range := inferInstance
    refine hPnc (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center θ.rangeRestrict ?_)
    rw [MonoidHom.ker_rangeRestrict, hθker]
    exact hD₀Z
  have hDp : IsPGroup r D := IsPGroup.to_le hQp (by rintro _ ⟨y, -, rfl⟩; exact (y : Q).2)
  have hDnt : Nontrivial D := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hDnc ⟨⟨fun x y => Subsingleton.elim _ _⟩⟩
  have hDcomm : commutator D ≤ center D := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    rintro ⟨_, x, hx, rfl⟩ - ⟨_, y, hy, rfl⟩ -
    refine mem_center_iff.2 fun ⟨_, z, hz, rfl⟩ => Subtype.ext ?_
    have hc : ⁅x, y⁆ ∈ center P := by
      apply hPcomm
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top x) (mem_top y)
    have hcz := mem_center_iff.1 hc z
    change ι z * ⁅ι x, ι y⁆ = ⁅ι x, ι y⁆ * ι z
    rw [← map_commutatorElement, ← map_mul, ← map_mul, hcz]
  have hZDcyc : IsCyclic (center D) := by
    have hZA : ∀ x : center D, ((x : D) : H) ∈ A := fun x =>
      key ((center D).map D.subtype) inferInstance
        ((isMulCommutative_map_subtype_iff _).2 inferInstance) ((map_subtype_le _).trans hDC)
        ⟨x, x.2, rfl⟩
    refine isCyclic_of_injective ((D.subtype.comp (center D).subtype).codRestrict A hZA) ?_
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg Subtype.val hxy :))
  have hZDcard : Nat.card (center D) = r := by
    have hdvd : Nat.card (center D) ∣ r := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (Subtype.ext (hDexp _ (x : D).2))
    have hnt : Nontrivial (center D) := hDp.center_nontrivial
    rcases (Nat.dvd_prime hr).1 hdvd with h | h
    · exact absurd h Finite.one_lt_card.ne'
    · exact h
  have hZDeq : center D = commutator D := by
    have hne : commutator D ≠ ⊥ := fun h => hDnc ((commutator_eq_bot_iff D).1 h)
    refine (Subgroup.eq_of_le_of_card_ge hDcomm ?_).symm
    rw [hZDcard]
    have h1 : Nat.card (commutator D) ∣ r := hZDcard ▸ Subgroup.card_dvd_of_le hDcomm
    rcases (Nat.dvd_prime hr).1 h1 with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hne
    · exact h.ge
  obtain ⟨a, hDcard, ha⟩ := card_eq_pow_one_add_two_mul (D := D)
    (fun x => Subtype.ext (hDexp _ x.2)) hZDeq hZDcard
  exact ⟨r, a, D, hr, hr.odd_of_ne_two hr2, ha hDnc, hDn, hDC, hDcard, hDexp, hZDeq, hZDcard⟩

end CFSG.OddSolvableUnitary
