module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.I414Aut
public import CFSG.GH74.GLS.Stage2.Final.Thm6.I414Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.RankThree.PerfectCover.CentralQuotientPrimeSupport

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.I414

open CFSG CFSG.LocalCores CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBHeldSmallCore (primeCore_subnormal_intersection)
open CFSG.RankThree.PerfectCover (sylow_eq_bot_of_not_dvd_card_quotient_center)

@[expose] def restrictAct {X : Type*} [Group X] {A : Type*} [Group A] (α : A →* MulAut X)
    (L : Subgroup X) (hL : ∀ a, ∀ x ∈ L, α a x ∈ L) : A →* MulAut L where
  toFun a :=
    { toFun := fun x => ⟨α a (x : X), hL a (x : X) x.2⟩
      invFun := fun x => ⟨α a⁻¹ (x : X), hL a⁻¹ (x : X) x.2⟩
      left_inv := fun x => Subtype.ext <| by
        change α a⁻¹ (α a (x : X)) = x
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      right_inv := fun x => Subtype.ext <| by
        change α a (α a⁻¹ (x : X)) = x
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      map_mul' := fun x y => Subtype.ext (map_mul (α a) (x : X) y) }
  map_one' := by
    ext x
    change α 1 (x : X) = x
    rw [map_one, MulAut.one_apply]
  map_mul' a b := by
    ext x
    change α (a * b) (x : X) = α a (α b x)
    rw [map_mul, MulAut.mul_apply]

theorem restrictAct_apply {X : Type*} [Group X] {A : Type*} [Group A] (α : A →* MulAut X)
    (L : Subgroup X) (hL : ∀ a, ∀ x ∈ L, α a x ∈ L) (a : A) (x : L) :
    ((restrictAct α L hL a x : L) : X) = α a (x : X) :=
  rfl

theorem isSylowOf_top {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime] (P : Sylow r G) :
    IsSylowOf r (P : Subgroup G) ⊤ := by
  rw [isSylowOf_iff]
  exact ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩

theorem isSylowOf_inf_of_isSubnormal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsSylowOf p P ⊤) {H : Subgroup G} (hH : H.IsSubnormal) :
    IsSylowOf p (P ⊓ H) H := by
  induction hH with
  | top => simpa using hP
  | step H K hHK _ hN ih =>
    have h1 := ih.inf_of_le_normalizer hHK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN)
    rwa [inf_assoc, inf_eq_right.mpr hHK] at h1

theorem map_component_eq {X : Type*} [Group X] [Finite X] {r : ℕ} [Fact r.Prime]
    (P : Sylow r X) {L : Subgroup X} (hL : IsComponent L) (hrL : r ∣ Nat.card L)
    (φ : MulAut X) (hfix : ∀ x ∈ (P : Subgroup X), φ x = x) :
    L.map φ.toMonoidHom = L := by
  have hL' : IsComponent (L.map φ.toMonoidHom) := isComponent_map_mulEquiv φ hL
  rcases distinct_components_commute hL hL' with h | h
  · exact h.symm
  · exfalso
    have hT := isSylowOf_inf_of_isSubnormal (isSylowOf_top P) hL.2
    obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
    have hcomm : ∀ l ∈ L, ∀ m ∈ L.map φ.toMonoidHom, m * l = l * m := by
      have : L ≤ Subgroup.centralizer ((L.map φ.toMonoidHom : Subgroup X) : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      intro l hl m hm
      exact Subgroup.mem_centralizer_iff.mp (this hl) m hm
    have hQc : (Q : Subgroup ↥L) ≤ Subgroup.center ↥L := by
      intro x hx
      rw [hQ] at hx
      have hx' : (x : X) ∈ (P : Subgroup X) ⊓ L := hx
      have hxm : (x : X) ∈ L.map φ.toMonoidHom := ⟨x, x.2, hfix _ hx'.1⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y y.2 x hxm).symm
    have hnd : ¬ r ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := fun hd =>
      Q.not_dvd_index (hd.trans (Subgroup.index_dvd_of_le hQc))
    have : Group.IsPerfect ↥L := hL.1.1
    exact Q.ne_bot_of_dvd_card hrL (sylow_eq_bot_of_not_dvd_card_quotient_center Q hnd)

theorem dvd_card_of_isComponent {X : Type*} [Group X] [Finite X] {r : ℕ} [Fact r.Prime]
    (hO : pPrimeCore r X = ⊥) {L : Subgroup X} (hL : IsComponent L) : r ∣ Nat.card L := by
  by_contra hn
  have hcop : r.Coprime (Nat.card L) := (Fact.out : r.Prime).coprime_iff_not_dvd.mpr hn
  have htop : (⊤ : Subgroup ↥L) ≤ pPrimeCore r ↥L :=
    le_sSup ⟨inferInstance, by simpa only [Subgroup.card_top] using hcop⟩
  have hbot : pPrimeCore r ↥L = ⊥ := by
    rw [primeCore_subnormal_intersection r L hL.2, hO]
    exact Subgroup.bot_subgroupOf L
  rw [hbot] at htop
  have : Nontrivial ↥L := isQuasisimple_nontrivial hL.1
  exact (not_le_of_gt (bot_lt_top : (⊥ : Subgroup ↥L) < ⊤) htop).elim

theorem fitting_le_sylow {X : Type*} [Group X] [Finite X] {r : ℕ} [Fact r.Prime]
    (hO : pPrimeCore r X = ⊥) (P : Sylow r X) : fittingSubgroup X ≤ (P : Subgroup X) := by
  rw [Fitting_eq_pcore X r hO]
  have := pCore_normal (p := r) (G := X)
  exact (pCore_isPGroup (p := r) (G := X)).le_sylow_of_normal P

theorem act_eq_one {X : Type} [Group X] [Finite X] {A : Type*} [Group A] [Group.IsPerfect A]
    (α : A →* MulAut X) {p r : ℕ} [Fact r.Prime]
    (hXp : p.Coprime (Nat.card X)) (hS : HasPropS X) (hO : pPrimeCore r X = ⊥)
    (P : Sylow r X) (hfix : ∀ a : A, ∀ x ∈ (P : Subgroup X), α a x = x)
    {a : A} {n : ℕ} (ha : a ^ (p ^ n) = 1) : α a = 1 := by
  have hinv : ∀ L : Subgroup X, IsComponent L → ∀ b : A, L.map (α b).toMonoidHom = L :=
    fun L hL b => map_component_eq P hL (dvd_card_of_isComponent hO hL) (α b) (hfix b)
  have hcomp : ∀ L : Subgroup X, IsComponent L → ∀ x ∈ L, α a x = x := by
    intro L hL x hx
    have hLinv : ∀ b : A, ∀ y ∈ L, α b y ∈ L := fun b y hy => by
      rw [← hinv L hL b]
      exact ⟨y, hy, rfl⟩
    have hOut : Group.IsSolvable (Outer (↥L ⧸ Subgroup.center ↥L)) :=
      hS _ hL.1.2.1 hL.1.2.2 ⟨L, QuotientGroup.mk' _, QuotientGroup.mk'_surjective _⟩
    have hLp : p.Coprime (Nat.card L) := hXp.coprime_dvd_right (Subgroup.card_subgroup_dvd_card L)
    have h1 := act_trivial_on_quasisimple hL.1 (restrictAct α L hLinv) hOut hLp ha
    have h2 := congrArg (fun m : MulAut L => ((m ⟨x, hx⟩ : L) : X)) h1
    simpa [restrictAct_apply] using h2
  have hlayer : layer X ≤ fixedSubgroup (α a) := sSup_le fun L hL x hx => hcomp L hL x hx
  have hfitt : fittingSubgroup X ≤ fixedSubgroup (α a) := fun x hx =>
    hfix a x (fitting_le_sylow hO P hx)
  have hgf : ∀ x ∈ generalizedFitting X, α a x = x := fun x hx =>
    (sup_le hfitt hlayer : generalizedFitting X ≤ fixedSubgroup (α a)) hx
  exact eq_one_of_fixes_generalizedFitting hXp (α a) (n := n)
    (by rw [← map_pow, ha, map_one]) hgf

end CFSG.GH74.GLS.Stage2.Final.Thm6.I414
