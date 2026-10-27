module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L33F
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Comm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Dihedral
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.Open (standardComponentIsStandard)

variable {G : Type} [Group G]

theorem componentAtCentralInvolutions_of_pocketed [Finite G] (h36 : Asc82Lemma36) {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) {X : Subgroup G} (hX : InCStar X)
    (hXF : InFStar X) (hpk : InF X ∨ IsL3Eps3 X) : ComponentAtCentralInvolutions X := by
  intro x hx hxX
  obtain ⟨x₀, hx₀, hXx₀⟩ := hX.1
  have hx₀X : x₀ ∈ centralizer (X : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (hXx₀.le ha)
  have ha : x₀ * x₀ = 1 := by
    rw [← pow_two]
    exact hx₀ ▸ pow_orderOf_eq_one x₀
  have hb : x * x = 1 := by
    rw [← pow_two]
    exact hx ▸ pow_orderOf_eq_one x
  have hprod : x₀ * x ∈ centralizer (X : Set G) := mul_mem hx₀X hxX
  rcases Nat.even_or_odd (orderOf (x₀ * x)) with hev | hodd
  · obtain ⟨n, hz, hza, hzb⟩ := exists_pow_involution_of_even_orderOf_mul ha hb hev
    have hzX : (x₀ * x) ^ n ∈ centralizer (X : Set G) := Subgroup.pow_mem _ hprod n
    have h1 : IsComponentIn X (centralizer ({(x₀ * x) ^ n} : Set G)) :=
      isComponentIn_centralizer_of_commute h36 hS hX hXF hpk hx₀ hz hza hXx₀ hzX
    exact isComponentIn_centralizer_of_commute h36 hS hX hXF hpk hz hx hzb.symm h1 hxX
  · obtain ⟨n, hn⟩ := exists_pow_inv_conj_of_odd_orderOf_mul ha hb hodd
    have hk : ((x₀ * x) ^ n)⁻¹ ∈ centralizer (X : Set G) :=
      inv_mem (Subgroup.pow_mem _ hprod n)
    have h := IsComponentIn.of_conj_centralizer hXx₀ hk
    rwa [hn] at h

@[expose] def Asc82Walter12F : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ X : Subgroup G, InCStar X → InFStar X → ComponentAtCentralInvolutions X

@[expose] def Asc82Walter12L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ X : Subgroup G, InCStar X → InFStar X → ¬ InF X → ¬ IsL3Eps3 X →
      ComponentAtCentralInvolutions X

theorem asc82Walter12F_of_L2 (h36 : Asc82Lemma36) (hL2 : Asc82Walter12L2) :
    Asc82Walter12F := by
  intro G _ _ t L hS X hX hXF
  by_cases hpk : InF X ∨ IsL3Eps3 X
  · exact componentAtCentralInvolutions_of_pocketed h36 hS hX hXF hpk
  · rw [not_or] at hpk
    exact hL2 G t L hS X hX hXF hpk.1 hpk.2

theorem nonCommute_of_componentAt (hP : Asc82PocketExists) (h34c : Asc82Lemma34c) [Finite G]
    {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L) {X : Subgroup G}
    (hX : InCStar X) (hXF : InFStar X) (hpk : InF X ∨ IsL3Eps3 X)
    (h2 : ComponentAtCentralInvolutions X) (g : G) :
    ⁅X, X.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  intro hcomm
  obtain ⟨x, hx, hXx⟩ := hX.1
  obtain ⟨y, K, hy, hKX, hpocket⟩ := hP G x X hx hXx hpk
  have hyX : y ∈ X := hKX hpocket.1
  have hPD : Sec3PocketData x X y K := ⟨hx, hXx, hXF, hy, hyX, hKX, hpocket⟩
  have hXle : X ≤ Subgroup.centralizer
      ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hyCg : y ∈ Subgroup.centralizer
      ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := hXle hyX
  have hy''C : g⁻¹ * y * g ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : MulAut.conj g a ∈ X.map (MulAut.conj g).toMonoidHom := ⟨a, ha, rfl⟩
    have hcomm' := (Subgroup.mem_centralizer_iff.mp hyCg) (MulAut.conj g a) ha'
    rw [MulAut.conj_apply] at hcomm'
    have hconj := congrArg (fun z => g⁻¹ * z * g) hcomm'
    rw [show g⁻¹ * ((g * a * g⁻¹) * y) * g = a * (g⁻¹ * y * g) by group,
      show g⁻¹ * (y * (g * a * g⁻¹)) * g = (g⁻¹ * y * g) * a by group] at hconj
    exact hconj
  have hy''2 : orderOf (g⁻¹ * y * g) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) y
    rwa [MulAut.conj_apply, inv_inv, hy] at h
  have hcompX : IsComponentIn X (Subgroup.centralizer ({g⁻¹ * y * g} : Set G)) :=
    h2 (g⁻¹ * y * g) hy''2 hy''C
  have hmapped := IsComponentIn.map_mulEquiv hcompX (MulAut.conj g)
  rw [CFSG.centralizer_singleton_map (MulAut.conj g) (g⁻¹ * y * g)] at hmapped
  have hconjy : MulAut.conj g (g⁻¹ * y * g) = y := by
    rw [MulAut.conj_apply]
    group
  rw [hconjy] at hmapped
  have hFS : InFStar (X.map (MulAut.conj g).toMonoidHom) := by
    rw [← conjugate_inv_eq_map_conj X g]
    exact hXF.conjugate g⁻¹
  exact h34c G t L hS x X y K hPD (X.map (MulAut.conj g).toMonoidHom) hmapped hFS

theorem asc82Lemma33_of_walter12F (hF : Asc82Walter12F) (hnc : Asc82NonCommuteNonPocketed)
    (hP : Asc82PocketExists) (h34c : Asc82Lemma34c) (hstd : Asc82StandardInput) :
    Asc82Lemma33 := by
  intro G _ _ t L hS X hXC hXF S
  by_contra hcyc
  have h2 : ComponentAtCentralInvolutions X := hF G t L hS X hXC hXF
  have h4 : ∀ g : G, ⁅X, X.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro g
    by_cases hpk : InF X ∨ IsL3Eps3 X
    · exact nonCommute_of_componentAt hP h34c hS hXC hXF hpk h2 g
    · rw [not_or] at hpk
      exact hnc G t L hS X hXC hXF hpk.1 hpk.2 g
  have hstd0 : standardComponentIsStandard X :=
    standard_of_componentAtCentralInvolutions hXC.1 h2 h4
  exact hS.notChev3 (hstd G hS.simple hS.kProper hS.notCat hS.a1 hS.a2
    ⟨L, hS.inF, t, hS.involution, hS.component⟩ X hstd0 hXF ⟨S, hcyc⟩)

@[expose] def Asc82StandardInputF : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ¬ CFSG.Blueprint.Catalog G →
    AschA1 G → AschA2 G →
    (∃ L : Subgroup G, InF L ∧ InC L) →
      ∀ X : Subgroup G, standardComponentIsStandard X → InF X →
        (∃ S : Sylow 2 (centralizer (X : Set G)),
          ¬ IsCyclic (S : Subgroup (centralizer (X : Set G)))) → Chev3 G

theorem asc82StandardInputF_of_standardInput (h : Asc82StandardInput) : Asc82StandardInputF :=
  fun G _ _ hs hK hn h1 h2 hL X hX hXF hS => h G hs hK hn h1 h2 hL X hX (Or.inl hXF) hS

theorem asc82Lemma33F_of_inputs (h36 : Asc82Lemma36) (hP : Asc82PocketExists)
    (h34c : Asc82Lemma34c) (hstd : Asc82StandardInputF) : Asc82Lemma33F := by
  intro G _ _ t L hS X hXC hXF S
  by_contra hcyc
  have h2 : ComponentAtCentralInvolutions X :=
    componentAtCentralInvolutions_of_pocketed h36 hS hXC (Or.inl hXF) (Or.inl hXF)
  have h4 : ∀ g : G, ⁅X, X.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := fun g =>
    nonCommute_of_componentAt hP h34c hS hXC (Or.inl hXF) (Or.inl hXF) h2 g
  have hstd0 : standardComponentIsStandard X :=
    standard_of_componentAtCentralInvolutions hXC.1 h2 h4
  exact hS.notChev3 (hstd G hS.simple hS.kProper hS.notCat hS.a1 hS.a2
    ⟨L, hS.inF, t, hS.involution, hS.component⟩ X hstd0 hXF ⟨S, hcyc⟩)

end CFSG.OddStandard.SmallF3.Omega
