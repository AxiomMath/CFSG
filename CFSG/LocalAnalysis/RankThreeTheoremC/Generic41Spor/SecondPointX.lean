module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PlaneInT

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC
  card_inf_centralizer_of_nonabelian_card_p_cube exists_isElemAbelian_card_sq_of_nonabelian)

theorem spx_exists_elemAbelian_sq_le_centralizer {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    {T : Subgroup G} (hcard : Nat.card T = p ^ 3) (hexp : ∀ t ∈ T, t ^ p = 1)
    (hnc : ¬ IsMulCommutative T) {t : G} (ht : t ∈ T) :
    ∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      E ≤ Subgroup.centralizer ({t} : Set G) := by
  have hp : p.Prime := Fact.out
  by_cases hZt : t ∈ T ⊓ Subgroup.centralizer (T : Set G)
  · obtain ⟨E, hET, hE, hEc, -⟩ := exists_isElemAbelian_card_sq_of_nonabelian hcard hexp hnc
    refine ⟨E, hET, hE, hEc, fun e he => ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hZt).2 e (hET he)).symm
  · obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup G, Z = T ⊓ Subgroup.centralizer (T : Set G) := ⟨_, rfl⟩
    have hZcard : Nat.card Z = p := by
      rw [hZdef]
      exact card_inf_centralizer_of_nonabelian_card_p_cube hcard hnc
    obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G, E = T ⊓ Subgroup.centralizer ({t} : Set G) := ⟨_, rfl⟩
    have hET : E ≤ T := by
      rw [hEdef]
      exact inf_le_left
    have hEC : E ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [hEdef]
      exact inf_le_right
    have hZE : Z ≤ E := by
      intro z hz
      rw [hZdef] at hz
      obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hz
      rw [hEdef]
      refine Subgroup.mem_inf.mpr ⟨hzT, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact Subgroup.mem_centralizer_iff.mp hzC h ht
    have htE : t ∈ E := by
      rw [hEdef]
      refine Subgroup.mem_inf.mpr ⟨ht, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
    have hTfin : Finite T :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
    have hEfin : Finite E :=
      Finite.of_injective (Subgroup.inclusion hET) (Subgroup.inclusion_injective hET)
    have hdvdT : Nat.card E ∣ p ^ 3 := by
      have h := Subgroup.card_dvd_of_le hET
      rwa [hcard] at h
    have hZdvd : p ∣ Nat.card E := by
      have h := Subgroup.card_dvd_of_le hZE
      rwa [hZcard] at h
    obtain ⟨i, hi, hEi⟩ := (Nat.dvd_prime_pow hp).mp hdvdT
    have hcardE : Nat.card E = p ^ 2 := by
      interval_cases i
      · exfalso
        rw [pow_zero] at hEi
        rw [hEi] at hZdvd
        have h1 : p = 1 := Nat.dvd_one.mp hZdvd
        have h2 := hp.one_lt
        omega
      · exfalso
        rw [pow_one] at hEi
        have hZE' : Z = E := Subgroup.eq_of_le_of_card_ge hZE (le_of_eq (by rw [hEi, hZcard]))
        apply hZt
        rw [← hZdef, hZE']
        exact htE
      · exact hEi
      · exfalso
        have hET' : E = T := Subgroup.eq_of_le_of_card_ge hET (le_of_eq (by rw [hEi, hcard]))
        apply hZt
        refine Subgroup.mem_inf.mpr ⟨ht, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have hhE : h ∈ E := by rw [hET']; exact hh
        have := Subgroup.mem_centralizer_iff.mp (hEC hhE) t rfl
        exact this.symm
    refine ⟨E, hET, ⟨?_, fun e he => hexp e (hET he)⟩, hcardE, hEC⟩
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcardE

theorem spx_exists_mul_of_sup_eq {G : Type*} [Group G] {T Z S : Subgroup G}
    (hcomm : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hsup : T ⊔ Z = S) :
    ∀ s ∈ S, ∃ t ∈ T, ∃ z ∈ Z, s = t * z := by
  have hrange := MonoidHom.noncommCoprod_range T.subtype Z.subtype
    (fun a b => (hcomm b b.2 a a.2).symm)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  intro s hs
  rw [← hsup, ← hrange] at hs
  obtain ⟨⟨a, b⟩, rfl⟩ := hs
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem spx_commutator_le_left {G : Type*} [Group G] {T Z P : Subgroup G} [IsMulCommutative Z]
    (hcomm : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hsup : T ⊔ Z = P) : ⁅P, P⁆ ≤ T := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨t, ht, z, hz, rfl⟩ := spx_exists_mul_of_sup_eq hcomm hsup a ha
  obtain ⟨t', ht', z', hz', rfl⟩ := spx_exists_mul_of_sup_eq hcomm hsup b hb
  have h1 : Commute z t' := hcomm z hz t' ht'
  have h2 : Commute z' t := hcomm z' hz' t ht
  have h3 : z * z' = z' * z := congrArg Subtype.val (mul_comm' (⟨z, hz⟩ : Z) ⟨z', hz'⟩)
  have e1 : t * z * (t' * z') = t * t' * (z * z') := h1.mul_mul_mul_comm t z'
  have e2 : t' * z' * (t * z) = t' * t * (z * z') := by
    rw [h3]
    exact h2.mul_mul_mul_comm t' z
  have key : ⁅t * z, t' * z'⁆ = ⁅t, t'⁆ := by
    have e0 : ⁅t * z, t' * z'⁆ = (t * z * (t' * z')) * (t' * z' * (t * z))⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e0, e1, e2]
    simp only [commutatorElement_def]
    group
  rw [key, commutatorElement_def]
  exact T.mul_mem (T.mul_mem (T.mul_mem ht ht') (T.inv_mem ht)) (T.inv_mem ht')

theorem spx_x_not_mem_commutator_of_decomp {G : Type*} [Group G] {T Z P : Subgroup G} {x : G}
    [IsMulCommutative Z] (hxZ : x ∈ Z) (hx1 : x ≠ 1)
    (hcomm : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hTZ : T ⊓ Z = ⊥) (hsup : T ⊔ Z = P) :
    x ∉ ⁅P, P⁆ := by
  intro hx
  have hxT : x ∈ T := spx_commutator_le_left hcomm hsup hx
  have : x ∈ T ⊓ Z := Subgroup.mem_inf.mpr ⟨hxT, hxZ⟩
  rw [hTZ, Subgroup.mem_bot] at this
  exact hx1 this

theorem spx_three_le_pRank_of_decomp {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T Z P : Subgroup G} {x y : G}
    (hcard : Nat.card T = p ^ 3) (hexp : ∀ t ∈ T, t ^ p = 1) (hnc : ¬ IsMulCommutative T)
    (hxZ : x ∈ Z) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hcomm : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hTZ : T ⊓ Z = ⊥) (hsup : T ⊔ Z = P)
    (hxP : ∀ a ∈ P, x * a = a * x) (hy : y ∈ P) :
    3 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({y} : Set G)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨t, ht, z, hz, rfl⟩ := spx_exists_mul_of_sup_eq hcomm hsup y hy
  obtain ⟨E, hET, hEel, hEcard, hEt⟩ := spx_exists_elemAbelian_sq_le_centralizer hcard hexp hnc ht
  have hXel : IsElemAbelian p (Subgroup.zpowers x) := by
    refine ⟨inferInstance, fun w hw => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hXcard : Nat.card (Subgroup.zpowers x) = p ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1, pow_one]
  have hXZ : Subgroup.zpowers x ≤ Z := Subgroup.zpowers_le.mpr hxZ
  have hcommEX : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, Commute a b :=
    fun a ha b hb => (hcomm b (hXZ hb) a (hET ha)).symm
  have hdisj : E ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwE, hwX⟩ := Subgroup.mem_inf.mp hw
    have : w ∈ T ⊓ Z := Subgroup.mem_inf.mpr ⟨hET hwE, hXZ hwX⟩
    rwa [hTZ] at this
  have hEH : E ≤ Subgroup.centralizer ({t * z} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 : t * e = e * t := Subgroup.mem_centralizer_iff.mp (hEt he) t rfl
    have h2 : z * e = e * z := hcomm z hz e (hET he)
    calc t * z * e = t * (z * e) := mul_assoc _ _ _
      _ = t * (e * z) := by rw [h2]
      _ = t * e * z := (mul_assoc _ _ _).symm
      _ = e * t * z := by rw [h1]
      _ = e * (t * z) := mul_assoc _ _ _
  have hXH : Subgroup.zpowers x ≤ Subgroup.centralizer ({t * z} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hxP _ hy).symm
  exact plane_add_le_pRank hp hEel hXel hEcard hXcard hcommEX hdisj hEH hXH


variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G} {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
  {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}

theorem typeII_three_le_pRank_centralizer (hX : ExtraFacts Typ p Shape)
    (hc : PointConfig Typ G p P M x J) (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    {y : G} (hy : y ∈ (P : Subgroup G)) (hyp : y ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({y} : Set G)) := by
  clear hyp
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hTcard, hTexp, hTnab, -⟩ := typeII_T_structure hX hc
  obtain ⟨Z, -, hxZ, -, hcomm, hTZ, hsup⟩ := typeII_S_decomp hX hc
  have hS : u3S P x = (P : Subgroup G) := inf_eq_left.mpr hP
  rw [hS] at hsup
  exact spx_three_le_pRank_of_decomp hTcard hTexp hTnab hxZ hc.generic.2.1.2.1
    hc.generic.2.1.2.2.1 hcomm hTZ hsup
    (fun a ha => Subgroup.mem_centralizer_iff.mp (hP ha) x rfl) hy

theorem typeII_x_not_mem_commutator (hX : ExtraFacts Typ p Shape)
    (hc : PointConfig Typ G p P M x J) (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) :
    x ∉ ⁅(P : Subgroup G), (P : Subgroup G)⁆ := by
  obtain ⟨Z, hZcyc, hxZ, -, hcomm, hTZ, hsup⟩ := typeII_S_decomp hX hc
  have hS : u3S P x = (P : Subgroup G) := inf_eq_left.mpr hP
  rw [hS] at hsup
  exact spx_x_not_mem_commutator_of_decomp hxZ hc.generic.2.1.2.1 hcomm hTZ hsup

theorem plane_three_le_pRank_centralizer
    (hsyl : ∀ (K : Type) [Group K] [Finite K], Typ p K → SylowIsPlane p K)
    (hno : ∀ (K : Type) [Group K] [Finite K], Typ p K → NoOuterP p K)
    (hc : PointConfig Typ G p P M x J) (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    {y : G} (hy : y ∈ (P : Subgroup G)) :
    3 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({y} : Set G)) := by
  have hp : p.Prime := hc.prime
  obtain ⟨-, hTel, -⟩ := plane_T_structure hsyl hc
  obtain ⟨Z, hZcyc, -, -, hcomm, -, hsup⟩ := plane_S_decomp hsyl hno hc
  have hS : u3S P x = (P : Subgroup G) := inf_eq_left.mpr hP
  rw [hS] at hsup
  haveI : IsMulCommutative (u3T P x J) := hTel.1
  have hPab : IsMulCommutative (P : Subgroup G) := by
    have := plane_sup_comm (A := u3T P x J) (B := Z) (fun a ha b hb => (hcomm b hb a ha).symm)
    rwa [hsup] at this
  have hrk : CFSG.Open.pRank p (P : Subgroup G) = 3 := by
    have := hc.generic.2.2.2
    rwa [inf_eq_left.mpr hP] at this
  have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({y} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact congrArg Subtype.val (mul_comm' (⟨h, hy⟩ : (P : Subgroup G)) ⟨a, ha⟩)
  calc 3 = CFSG.Open.pRank p (P : Subgroup G) := hrk.symm
    _ ≤ CFSG.Open.pRank p (Subgroup.centralizer ({y} : Set G)) :=
        CFSG.SectionRank.pRank_mono hp.one_lt hle

theorem plane_x_not_mem_commutator
    (hsyl : ∀ (K : Type) [Group K] [Finite K], Typ p K → SylowIsPlane p K)
    (hno : ∀ (K : Type) [Group K] [Finite K], Typ p K → NoOuterP p K)
    (hc : PointConfig Typ G p P M x J) (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) :
    x ∉ ⁅(P : Subgroup G), (P : Subgroup G)⁆ := by
  obtain ⟨Z, hZcyc, hxZ, -, hcomm, hTZ, hsup⟩ := plane_S_decomp hsyl hno hc
  have hS : u3S P x = (P : Subgroup G) := inf_eq_left.mpr hP
  rw [hS] at hsup
  exact spx_x_not_mem_commutator_of_decomp hxZ hc.generic.2.1.2.1 hcomm hTZ hsup

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
