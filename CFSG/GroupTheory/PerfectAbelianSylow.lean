module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Walter.AStar.Basic
import CFSG.Quasithin.EmptyFaithful.S153QPC1

public section

namespace CFSG

open CFSG.Walter

private theorem two_dvd_card_of_perfect (X : Type*) [Group X] [Finite X] [Group.IsPerfect X]
    [Nontrivial X] : 2 ∣ Nat.card X := by
  by_contra h
  have hodd : Odd (Nat.card X) :=
    Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  exact Group.IsPerfect.not_isSolvable X (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

private theorem four_dvd_card_of_perfect (X : Type*) [Group X] [Finite X] [Group.IsPerfect X]
    [Nontrivial X]
    (hab : ∀ P : Sylow 2 X, ∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), x * y = y * x)
    (h16 : ¬ 16 ∣ Nat.card X)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ Nat.card X) :
    4 ∣ Nat.card X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card X := two_dvd_card_of_perfect X
  by_contra h4
  obtain ⟨T⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  have hidx : ¬ 2 ∣ (T : Subgroup X).index := T.not_dvd_index
  have hmul : Nat.card (T : Subgroup X) * (T : Subgroup X).index = Nat.card X :=
    Subgroup.card_mul_index _
  have hTcard : Nat.card (T : Subgroup X) = 2 := by
    rcases n with _ | n
    · exfalso
      rw [pow_zero] at hn
      rw [hn, one_mul] at hmul
      rw [← hmul] at h2
      exact hidx h2
    rcases n with _ | n
    · simpa using hn
    · exfalso
      apply h4
      have h4T : 4 ∣ Nat.card (T : Subgroup X) := by
        rw [hn]
        exact dvd_trans (by norm_num : 4 ∣ 2 ^ 2) (pow_dvd_pow 2 (by omega))
      exact h4T.trans (Subgroup.card_subgroup_dvd_card (T : Subgroup X))
  have hcyc : IsCyclic (T : Subgroup X) := isCyclic_of_prime_card hTcard
  have hmin : (Nat.card X).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
  have hnorm : Subgroup.normalizer (T : Set X) ≤ Subgroup.centralizer (T : Set X) :=
    hcyc.normalizer_le_centralizer hmin
  let τ : X →* (T : Subgroup X) := MonoidHom.transferSylow T hnorm
  have hcomp : τ.ker.IsComplement' (T : Subgroup X) :=
    MonoidHom.ker_transferSylow_isComplement' T hnorm
  have hker : τ.ker = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup X) = commutator X := Group.IsPerfect.commutator_eq_top.symm
      _ ≤ τ.ker := Abelianization.commutator_subset_ker τ
  have hdisj : Disjoint τ.ker (T : Subgroup X) := hcomp.disjoint
  rw [hker, Subgroup.disjoint_def] at hdisj
  have hTbot : (T : Subgroup X) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact hdisj (Subgroup.mem_top x) hx
  rw [hTbot, Subgroup.card_bot] at hTcard
  exact absurd hTcard (by norm_num)

private theorem exists_nontrivial_perfect_subgroup {X : Type*} [Group X] [Finite X]
    (hX : ¬ Group.IsSolvable X) :
    ∃ D : Subgroup X, D ≠ ⊥ ∧ Group.IsPerfect ↥D := by
  classical
  haveI : WellFoundedLT (Subgroup X) := Finite.to_wellFoundedLT
  by_contra h
  apply hX
  rw [Group.isSolvable_iff_commutator_lt]
  intro H hH
  by_contra hlt
  have hcomm_le : ⁅H, H⁆ ≤ H := Subgroup.commutator_le_of_le (le_refl H) (le_refl H)
  exact h ⟨H, hH, Subgroup.isPerfect_iff.mpr (eq_of_le_of_not_lt hcomm_le hlt)⟩

private theorem exists_abelian_characteristic_subgroup (X : Type*) [Group X] [Finite X]
    [Nontrivial X] (hX : Group.IsSolvable X) :
    ∃ A : Subgroup X, A ≠ ⊥ ∧ A.Characteristic ∧ IsMulCommutative ↥A := by
  classical
  have hex : ∃ m, derivedSeries X m = ⊥ := Group.IsSolvable.solvable (G := X)
  have hn : derivedSeries X (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h
    have htopbot : (⊤ : Subgroup X) = ⊥ := by
      rw [← derivedSeries_zero (G := X), ← h]
      exact hn
    have hcard : Nat.card X = 1 := by
      rw [← Subgroup.card_top (G := X), htopbot, Subgroup.card_bot]
    have hgt : 1 < Nat.card X := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 :=
    ⟨Nat.find hex - 1, by omega⟩
  have hAj : derivedSeries X (j + 1) = ⊥ := by
    rw [← hj]
    exact hn
  have hAne : derivedSeries X j ≠ ⊥ := by
    intro hbot
    exact Nat.find_min hex (by omega) hbot
  let A : Subgroup X := derivedSeries X j
  have hAne' : A ≠ ⊥ := hAne
  have hAchar : A.Characteristic := derivedSeries_characteristic (G := X) j
  have hAcomm : IsMulCommutative ↥A := by
    refine Subgroup.commutator_self_eq_bot_iff.mp ?_
    have h := derivedSeries_succ (G := X) j
    rw [hAj] at h
    simpa [A] using h.symm
  exact ⟨A, hAne', hAchar, hAcomm⟩

private theorem exists_normal_torsion_subgroup {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] {A : Subgroup ↥N}
    (hAchar : A.Characteristic) (hAcomm : IsMulCommutative ↥A) (hAne : A ≠ ⊥) :
    ∃ (r : ℕ) (_ : r.Prime) (Ar : Subgroup G),
      Ar.Normal ∧ Ar ≠ ⊥ ∧ Ar ≤ N ∧ (∀ x ∈ Ar, x ^ r = 1) := by
  classical
  haveI : A.Characteristic := hAchar
  haveI : IsMulCommutative ↥A := hAcomm
  let AG : Subgroup G := A.map N.subtype
  have hAGnormal : AG.Normal :=
    ConjAct.normal_of_characteristic_of_normal (G := G) (H := N) (K := A)
  haveI : IsMulCommutative AG := Subgroup.map_isMulCommutative A N.subtype
  have hAGle : AG ≤ N := Subgroup.map_subtype_le A
  have hAcard : Nat.card ↥A ≠ 1 := fun h => hAne (Subgroup.card_eq_one.mp h)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hAcard
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨a, haord⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) r hrdvd
  let aG : G := ((a : ↥N) : G)
  have haG_mem : aG ∈ AG := ⟨a, a.2, rfl⟩
  have haG_pow : aG ^ r = 1 := by
    have h : (a : ↥A) ^ r = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
    simpa [aG] using congrArg (fun x : ↥A => ((x : ↥N) : G)) h
  let Ar : Subgroup G :=
    { carrier := {x | x ∈ AG ∧ x ^ r = 1}
      one_mem' := ⟨AG.one_mem, by simp⟩
      mul_mem' := by
        intro x y hx hy
        refine ⟨AG.mul_mem hx.1 hy.1, ?_⟩
        have hxy : x * y = y * x :=
          Subgroup.mul_comm_of_mem_isMulCommutative AG hx.1 hy.1
        rw [Commute.mul_pow hxy, hx.2, hy.2, mul_one]
      inv_mem' := by
        intro x hx
        refine ⟨AG.inv_mem hx.1, ?_⟩
        rw [inv_pow, hx.2]
        simp }
  have hArnormal : Ar.Normal := by
    refine ⟨fun x hx g => ?_⟩
    exact ⟨hAGnormal.conj_mem x hx.1 g, by rw [conj_pow, hx.2]; simp⟩
  have hArleAG : Ar ≤ AG := fun x hx => hx.1
  have hArleN : Ar ≤ N := hArleAG.trans hAGle
  have haG_memAr : aG ∈ Ar := ⟨haG_mem, haG_pow⟩
  have haG_ne : aG ≠ 1 := by
    intro h
    have ho : orderOf aG = r := by simpa [aG] using haord
    have h1 : orderOf aG = 1 := by rw [h, orderOf_one]
    rw [ho] at h1
    exact hr.ne_one h1
  have hArne : Ar ≠ ⊥ := by
    intro h
    have h1 : aG = 1 := by
      have : aG ∈ (⊥ : Subgroup G) := h ▸ haG_memAr
      simpa using this
    exact haG_ne h1
  have hArpow : ∀ x ∈ Ar, x ^ r = 1 := fun x hx => hx.2
  exact ⟨r, hr, Ar, hArnormal, hArne, hArleN, hArpow⟩

private theorem isPGroup_of_forall_pow_eq_one {G : Type*} [Group G] {r : ℕ} [Fact r.Prime]
    {H : Subgroup G} (h : ∀ x ∈ H, x ^ r = 1) : IsPGroup r H := by
  have hr : r.Prime := Fact.out
  rw [IsPGroup.iff_orderOf]
  intro x
  have hxr : x ^ r = 1 := by
    apply Subtype.ext
    simpa using h x x.2
  have hdvd : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one hxr
  rcases (Nat.dvd_prime hr).mp hdvd with h' | h'
  · exact ⟨0, by rw [h', pow_zero]⟩
  · exact ⟨1, by rw [h', pow_one]⟩

private theorem card_eq_prime_of_isPGroup {G : Type*} [Group G] [Finite G]
    (h16 : ¬ 16 ∣ Nat.card G)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ Nat.card G)
    {N : Subgroup G} (h4N : ¬ 4 ∣ Nat.card N)
    {r : ℕ} [Fact r.Prime] {Ar : Subgroup G} (hArne : Ar ≠ ⊥) (hArleN : Ar ≤ N)
    (hArP : IsPGroup r Ar) : Nat.card Ar = r := by
  have hr : r.Prime := Fact.out
  obtain ⟨k, hk⟩ := hArP.exists_card_eq
  have hkpos : 0 < k := by
    rcases k with _ | k
    · exfalso
      rw [pow_zero] at hk
      exact hArne (Subgroup.card_eq_one.mp hk)
    · exact Nat.succ_pos k
  rcases eq_or_ne r 2 with hr2 | hr2
  · rw [hr2] at hk ⊢
    have hkdvd : Nat.card Ar ∣ Nat.card N := Subgroup.card_dvd_of_le hArleN
    have hk1 : k ≤ 1 := by
      by_contra h
      have h2k : 2 ≤ k := by omega
      have h4Ar : 4 ∣ Nat.card Ar := by
        rw [hk]
        exact dvd_trans (by norm_num : 4 ∣ 2 ^ 2) (pow_dvd_pow 2 h2k)
      exact h4N (h4Ar.trans hkdvd)
    have hk_eq : k = 1 := by omega
    rw [hk, hk_eq, pow_one]
  · have hnot : ¬ r ^ 2 ∣ Nat.card G := hsq r hr hr2
    have hkdvdG : Nat.card Ar ∣ Nat.card G := Subgroup.card_subgroup_dvd_card (Ar : Subgroup G)
    have hk1 : k ≤ 1 := by
      by_contra h
      have h2k : 2 ≤ k := by omega
      have hdvd : r ^ 2 ∣ Nat.card Ar := by
        rw [hk]
        exact pow_dvd_pow r h2k
      exact hnot (hdvd.trans hkdvdG)
    have hk_eq : k = 1 := by omega
    rw [hk, hk_eq, pow_one]

private theorem exists_normal_subgroup_card_prime {G : Type*} [Group G] [Finite G]
    (h16 : ¬ 16 ∣ Nat.card G)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ Nat.card G)
    {N : Subgroup G} [N.Normal] (hNbot : N ≠ ⊥) (h4N : ¬ 4 ∣ Nat.card N)
    (hNsolv : Group.IsSolvable ↥N) :
    ∃ (r : ℕ) (_ : r.Prime) (Ar : Subgroup G),
      Ar.Normal ∧ Ar ≠ ⊥ ∧ Ar ≤ N ∧ Nat.card Ar = r := by
  classical
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNbot
  obtain ⟨A, hAne, hAchar, hAcomm⟩ := exists_abelian_characteristic_subgroup ↥N hNsolv
  obtain ⟨r, hr, Ar, hArn, hArne, hArleN, hArpow⟩ :=
    exists_normal_torsion_subgroup hAchar hAcomm hAne
  haveI : Fact r.Prime := ⟨hr⟩
  exact ⟨r, hr, Ar, hArn, hArne, hArleN,
    card_eq_prime_of_isPGroup h16 hsq h4N hArne hArleN
      (isPGroup_of_forall_pow_eq_one hArpow)⟩

private theorem le_center_of_normal_subgroup_card_prime {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] {r : ℕ} [Fact r.Prime] {Ar : Subgroup G} (hArn : Ar.Normal)
    (hArcard : Nat.card Ar = r) : Ar ≤ Subgroup.center G := by
  classical
  haveI : Ar.Normal := hArn
  haveI : IsCyclic Ar := isCyclic_of_prime_card hArcard
  have hAutComm : IsMulCommutative (MulAut Ar) := by
    refine IsMulCommutative.of_comm ?_
    intro f g
    apply (IsCyclic.mulAutMulEquiv Ar).injective
    simp only [map_mul]
    exact mul_comm _ _
  let ψ : G →* MulAut Ar := MulAut.conjNormal (H := Ar)
  have hker : ψ.ker = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup G) = commutator G := Group.IsPerfect.commutator_eq_top.symm
      _ ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  intro a ha
  rw [Subgroup.mem_center_iff]
  intro g
  have hψg : ψ g = 1 := by
    have : g ∈ ψ.ker := by rw [hker]; exact Subgroup.mem_top g
    exact MonoidHom.mem_ker.mp this
  have hfix : g * a * g⁻¹ = a := by
    have h := congrArg (fun f : MulAut Ar => ((f ⟨a, ha⟩ : Ar) : G)) (hψg)
    simpa [ψ, MulAut.conjNormal_apply] using h
  calc g * a = (g * a * g⁻¹) * g := by group
    _ = a * g := by rw [hfix]

private theorem false_of_solvable_normal {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (hab : ∀ P : Sylow 2 G, ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x)
    (h16 : ¬ 16 ∣ Nat.card G)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ Nat.card G)
    {N : Subgroup G} [N.Normal] (hNbot : N ≠ ⊥) (h4N : ¬ 4 ∣ Nat.card N)
    (hNsolv : Group.IsSolvable ↥N) : False := by
  classical
  obtain ⟨r, hr, Ar, hArn, hArne, hArleN, hArcard⟩ :=
    exists_normal_subgroup_card_prime h16 hsq hNbot h4N hNsolv
  haveI : Fact r.Prime := ⟨hr⟩
  have hArcenter : Ar ≤ Subgroup.center G :=
    le_center_of_normal_subgroup_card_prime hArn hArcard
  have hdvd : r ∣ Nat.card Ar := by rw [hArcard]
  obtain ⟨a, haord⟩ := exists_prime_orderOf_dvd_card' (G := Ar) r hdvd
  have haG : ((a : Ar) : G) ∈ Ar := a.2
  have hacentral : ((a : Ar) : G) ∈ Subgroup.center G := hArcenter haG
  have haorder : orderOf ((a : Ar) : G) = r := by simpa using haord
  have hP : IsPGroup r (Subgroup.zpowers ((a : Ar) : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, haorder, pow_one]
  obtain ⟨R, hR⟩ := hP.exists_le_sylow
  have haR : ((a : Ar) : G) ∈ (R : Subgroup G) := hR (Subgroup.mem_zpowers _)
  have hRcomm : ∀ x ∈ (R : Subgroup G), ∀ y ∈ (R : Subgroup G), x * y = y * x := by
    by_cases hr2 : r = 2
    · cases hr2
      exact fun x hx y hy => hab R x hx y hy
    · have hRcard : Nat.card (R : Subgroup G) = r := by
        obtain ⟨m, hm⟩ := R.isPGroup'.exists_card_eq
        have hmpos : 0 < m := by
          by_contra h
          have hm0 : m = 0 := by omega
          have hdvd : r ∣ Nat.card (R : Subgroup G) :=
            haorder ▸ Subgroup.orderOf_dvd_natCard (R : Subgroup G) haR
          rw [hm, hm0, pow_zero] at hdvd
          exact hr.not_dvd_one hdvd
        have hm1 : m ≤ 1 := by
          by_contra h
          have h2m : 2 ≤ m := by omega
          have hdvd : r ^ 2 ∣ Nat.card (R : Subgroup G) := by
            rw [hm]
            exact pow_dvd_pow r h2m
          exact hsq r hr hr2 (hdvd.trans (Subgroup.card_subgroup_dvd_card (R : Subgroup G)))
        have hm_eq : m = 1 := by omega
        rw [hm, hm_eq, pow_one]
      haveI : IsCyclic (R : Subgroup G) := isCyclic_of_prime_card hRcard
      haveI : IsMulCommutative (R : Subgroup G) := IsCyclic.isMulCommutative
      exact fun x hx y hy => Subgroup.mul_comm_of_mem_isMulCommutative (R : Subgroup G) hx hy
  have ha1 : ((a : Ar) : G) = 1 :=
    CFSG.Quasithin.QP.eq_one_of_mem_center_of_isPerfect R hRcomm hacentral
      (haorder ▸ pow_orderOf_eq_one _)
  have h1 : orderOf ((a : Ar) : G) = 1 := by rw [ha1, orderOf_one]
  rw [haorder] at h1
  exact hr.ne_one h1

theorem isSimpleGroup_of_isPerfect_of_card {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    [Nontrivial G]
    (hab : ∀ P : Sylow 2 G, ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x)
    (h16 : ¬ 16 ∣ Nat.card G) (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ Nat.card G) :
    IsSimpleGroup G := by
  classical
  have hGHab : HasAbelianSylowTwo G := fun P =>
    IsMulCommutative.of_comm (fun x y => Subtype.ext (hab P x x.2 y y.2))
  refine IsSimpleGroup.mk ?_
  intro N hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  by_cases htop : N = ⊤
  · exact Or.inr htop
  exfalso
  have h4N : ¬ 4 ∣ Nat.card N := by
    intro h4Ndiv
    haveI : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr htop
    have hcard : Nat.card G = Nat.card N * Nat.card (G ⧸ N) := by
      rw [← Subgroup.card_mul_index N, Subgroup.index_eq_card]
    have hQhab : HasAbelianSylowTwo (G ⧸ N) := hGHab.quotient N
    have h16Q : ¬ 16 ∣ Nat.card (G ⧸ N) := fun h =>
      h16 (hcard ▸ dvd_mul_of_dvd_right h _)
    have hsqQ : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ Nat.card (G ⧸ N) :=
      fun p hp hp2 h => hsq p hp hp2 (hcard ▸ dvd_mul_of_dvd_right h _)
    have h4Q : 4 ∣ Nat.card (G ⧸ N) :=
      four_dvd_card_of_perfect (G ⧸ N)
        (fun P x hx y hy =>
          congrArg Subtype.val ((hQhab P).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) h16Q hsqQ
    exact h16 (hcard ▸ mul_dvd_mul h4Ndiv h4Q)
  have hNsolv : Group.IsSolvable ↥N := by
    by_contra hns
    obtain ⟨D, hDne, hDperf⟩ := exists_nontrivial_perfect_subgroup hns
    haveI : Group.IsPerfect ↥D := hDperf
    haveI : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).mpr hDne
    have hDhab : HasAbelianSylowTwo ↥D := (hGHab.subgroup N).subgroup D
    have hDdvdN : Nat.card ↥D ∣ Nat.card ↥N := by
      have := Subgroup.card_dvd_of_le (H := D) (K := ⊤) le_top
      simpa using this
    have hNdvdG : Nat.card ↥N ∣ Nat.card G := Subgroup.card_subgroup_dvd_card N
    have hD16 : ¬ 16 ∣ Nat.card ↥D := fun h => h16 (h.trans (hDdvdN.trans hNdvdG))
    have hDsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ Nat.card ↥D :=
      fun p hp hp2 h => hsq p hp hp2 (h.trans (hDdvdN.trans hNdvdG))
    have h4D : 4 ∣ Nat.card ↥D :=
      four_dvd_card_of_perfect ↥D
        (fun P x hx y hy =>
          congrArg Subtype.val ((hDhab P).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hD16 hDsq
    exact h4N (h4D.trans hDdvdN)
  exact false_of_solvable_normal hab h16 hsq hNbot h4N hNsolv

end CFSG
