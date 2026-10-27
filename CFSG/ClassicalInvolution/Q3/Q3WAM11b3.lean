module

public import CFSG.ClassicalInvolution.Q3.Q3WAM11b2
public import CFSG.ClassicalInvolution.Q3.Q3WAM11
public import CFSG.ClassicalInvolution.Q3.Q3WASTImg
public import CFSG.ClassicalInvolution.Q3.Q3WASNorm
public import CFSG.ClassicalInvolution.Q3.Q3WAM11b1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD


@[expose] def M11AutInner : Prop :=
  ∀ φ : MulAut ↥CFSG.Blueprint.NativeSporadic.M11, ∃ g, φ = MulAut.conj g

@[expose] def InvAdj {Y : Type*} [Group Y] (a b : Y) : Prop :=
  orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a

section Generic

variable {c : CompData}

theorem m11_fund_classical (hc : c = CompData.m11) {R : Subgroup c.G} (hR : R ∈ c.fund) :
    ∃ u, IsClassicalMember3 R u := by
  subst hc
  exact hR

theorem m11_mem_fund_of_classical (hc : c = CompData.m11) {R : Subgroup c.G} {u : c.G}
    (h : IsClassicalMember3 R u) : R ∈ c.fund := by
  subst hc
  exact ⟨u, h⟩

theorem m11_involution_unique_gen (hc : c = CompData.m11) {R : Subgroup c.G} {u u' : c.G}
    (h : IsClassicalMember3 R u) (h' : IsClassicalMember3 R u') : u = u' := by
  subst hc
  exact involution_unique3 h h'

theorem m11_classical_eq_gen (hc : c = CompData.m11) {R R' : Subgroup c.G} {u : c.G}
    (h : IsClassicalMember3 R u) (h' : IsClassicalMember3 R' u) : R = R' := by
  subst hc
  exact Uniform.m11_classical_eq h h'

theorem m11_exists_classical_gen (hc : c = CompData.m11) {R₀ : Subgroup c.G} {w₀ : c.G}
    (h₀ : IsClassicalMember3 R₀ w₀) {u : c.G} (hu : orderOf u = 2) :
    ∃ R : Subgroup c.G, IsClassicalMember3 R u := by
  subst hc
  exact m11_classical_of_involution h₀ hu

theorem m11_hom_injective_gen (hc : c = CompData.m11) {X : Type} [Group X] (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) : Function.Injective ψ := by
  subst hc
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [m11_center_eq_bot] at hker
  exact le_bot_iff.mp hker

theorem m11_singleClass_gen (hc : c = CompData.m11) :
    ∀ R ∈ c.fund, ∀ R' ∈ c.fund, ∃ g : c.G, R' = conjSub g R := by
  subst hc
  exact Uniform.m11_singleClass

theorem m11_center_eq_bot_gen (hc : c = CompData.m11) : Subgroup.center c.G = ⊥ := by
  subst hc
  exact m11_center_eq_bot

theorem m11_exists_commuting_gen (hc : c = CompData.m11) {w : c.G} (hw : orderOf w = 2) :
    ∃ u : c.G, orderOf u = 2 ∧ u ≠ w ∧ u * w = w * u := by
  subst hc
  exact m11_exists_commuting_involution hw

theorem m11_card_gen (hc : c = CompData.m11) : Nat.card c.G = 7920 := by
  subst hc
  exact card_m11_kernel

theorem m11_comm_connected_gen (hc : c = CompData.m11) {u v : c.G} (hu : orderOf u = 2)
    (hv : orderOf v = 2) : Relation.ReflTransGen InvAdj u v := by
  subst hc
  exact m11_comm_connected hu hv

theorem m11_aut_dichotomy_gen (hOut : M11AutInner) (hc : c = CompData.m11) {X : Type} [Group X]
    (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) (σ : X ≃* X) (hσσ : ∀ a, σ (σ a) = a)
    (hstab : ∀ x, σ (ψ x) ∈ ψ.range) {R₀ : Subgroup c.G} (hR₀ : R₀ ∈ c.fund)
    (hfix : ∀ r ∈ R₀, σ (ψ r) = ψ r) :
    ∃ k : c.G, (k = 1 ∨ ∃ r₀, IsClassicalMember3 R₀ r₀ ∧ k = r₀) ∧
      ∀ x, σ (ψ x) = ψ (k * x * k⁻¹) := by
  subst hc
  obtain ⟨r₀, hr₀⟩ := hR₀
  obtain ⟨k, hk, h⟩ := m11_aut_dichotomy hOut ψ hker σ hσσ hstab hr₀ hfix
  exact ⟨k, hk.imp id fun h' => ⟨r₀, hr₀, h'⟩, h⟩

theorem m11_fund_iSup_eq_top_gen (hc : c = CompData.m11) {R₀ : Subgroup c.G} (hR₀ : R₀ ∈ c.fund) :
    (⨆ R ∈ c.fund, R) = ⊤ := by
  subst hc
  obtain ⟨w₀, hw₀⟩ := hR₀
  exact m11_fund_iSup_eq_top hw₀

end Generic

section Pic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

structure LocOK (Ω : Set (Subgroup G)) (x : G) : Prop where
  hΩ : InClass3 Ω
  hex : ExactMembers3 Ω
  hP1 : LocalOddCentral Ω {x}
  hO3 : LocalOddThreeFree3 Ω x

theorem LocOK.conj (h : LocOK Ω x) (g : G) : LocOK Ω (g * x * g⁻¹) :=
  ⟨h.hΩ, h.hex, Gaps.localOddCentral_conj h.hΩ.conjInvariant g x h.hP1,
    localOddThreeFree3_conj h.hΩ.conjInvariant g x h.hO3⟩

structure M11Pic (Ω : Set (Subgroup G)) (x : G) where
  ι : Type
  D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)
  i₀ : ι
  i₁ : ι
  ne : i₀ ≠ i₁
  k₀ : D.kind i₀ = CompData.sl23
  k₁ : D.kind i₁ = CompData.m11
  all : ∀ i, i = i₀ ∨ i = i₁

theorem nonempty_pic (h : LocalShapeC3 1 CompData.m11 Ω x) : Nonempty (M11Pic Ω x) := by
  obtain ⟨ι, hι, D, hcard, i₁, hk, hrest⟩ := h
  have := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card] at hcard
  have h1 : 1 < Fintype.card ι := by omega
  obtain ⟨i₀, hne⟩ := Fintype.exists_ne_of_one_lt_card h1 i₁
  refine ⟨⟨ι, D, i₀, i₁, hne, hrest i₀ hne, hk, fun i => ?_⟩⟩
  by_contra hcon
  push Not at hcon
  have h3 : 2 < Fintype.card ι :=
    Fintype.two_lt_card_iff.mpr ⟨i, i₀, i₁, hcon.1, hcon.2, hne⟩
  omega

variable (P : M11Pic Ω x)

theorem M11Pic.not_a1 : ¬ IsA1Comp3 P.D P.i₁ := fun h =>
  compData_m11_ne_sl23 (P.k₁.symm.trans h)

theorem M11Pic.a1 : IsA1Comp3 P.D P.i₀ := P.k₀

theorem M11Pic.mem_cases (c : LocOK Ω x) {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {x}) :
    N ∈ compMembers3 Ω x P.D P.i₀ ∨ N ∈ compMembers3 Ω x P.D P.i₁ := by
  obtain ⟨j, hj, -⟩ := exists_unique_comp3 c.hΩ c.hex c.hP1 c.hO3 P.D hN
  rcases P.all j with h | h
  · rw [h] at hj
    exact Or.inl hj
  · rw [h] at hj
    exact Or.inr hj

theorem M11Pic.a1_eq (c : LocOK Ω x) {N N' : Subgroup G} (hN : N ∈ compMembers3 Ω x P.D P.i₀)
    (hN' : N' ∈ compMembers3 Ω x P.D P.i₀) : N = N' :=
  eq_of_mem_compMembers_a13 c.hΩ c.hex c.hP1 c.hO3 P.a1 hN hN'

theorem M11Pic.not_commutes (c : LocOK Ω x) {N N' : Subgroup G}
    (hN : N ∈ compMembers3 Ω x P.D P.i₁) (hN' : N' ∈ compMembers3 Ω x P.D P.i₁) :
    ¬ Commutes N N' :=
  not_commutes_of_m11_comp3 c.hΩ c.hex c.hP1 c.hO3 P.k₁ hN hN'

theorem M11Pic.exists_ne (c : LocOK Ω x) : ∃ N N' : Subgroup G, N ∈ compMembers3 Ω x P.D P.i₁ ∧
    N' ∈ compMembers3 Ω x P.D P.i₁ ∧ N ≠ N' :=
  exists_ne_of_not_isA1Comp3 c.hΩ c.hex c.hP1 c.hO3 P.not_a1

theorem M11Pic.commutes_cross (c : LocOK Ω x) {N N' : Subgroup G}
    (hN : N ∈ compMembers3 Ω x P.D P.i₀) (hN' : N' ∈ compMembers3 Ω x P.D P.i₁) :
    Commutes N N' :=
  commutes_of_ne_comp3 c.hΩ c.hex c.hP1 c.hO3 P.D P.ne hN hN'

theorem M11Pic.vertex_mem {V : Subgroup G} (hV : V ∈ centralizingMembers Ω {x})
    (hVx : IsClassicalMember3 V x) : V ∈ compMembers3 Ω x P.D P.i₀ := by
  obtain ⟨i, hi, himg⟩ := locImg_eq_range_of_involution3 (RouteD.Gaps.fundNoncentral 3)
    (D := P.D) hV hVx
  rcases P.all i with h | h
  · subst h
    exact ⟨hV, himg.le⟩
  · subst h
    exact absurd hi P.not_a1

theorem M11Pic.mem_i₁ (c : LocOK Ω x) {V N : Subgroup G} (hV : V ∈ compMembers3 Ω x P.D P.i₀)
    (hN : N ∈ centralizingMembers Ω {x}) (hNV : N ≠ V) : N ∈ compMembers3 Ω x P.D P.i₁ := by
  rcases P.mem_cases c hN with h | h
  · exact absurd (P.a1_eq c h hV) hNV
  · exact h

theorem M11Pic.vertex_universal (c : LocOK Ω x) {V : Subgroup G}
    (hV : V ∈ compMembers3 Ω x P.D P.i₀) : Universal3 Ω x V :=
  universal3_of_a1comp c.hΩ c.hex c.hP1 c.hO3 P.D P.a1 hV

theorem M11Pic.not_universal (c : LocOK Ω x) {N : Subgroup G}
    (hN : N ∈ compMembers3 Ω x P.D P.i₁) : ¬ Universal3 Ω x N := by
  intro hu
  obtain ⟨A, B, hA, hB, hAB⟩ := P.exists_ne c
  by_cases hAN : A = N
  · subst hAN
    exact P.not_commutes c hA hB (hu B hB.1 fun h => hAB h.symm)
  · exact P.not_commutes c hN hA (hu A hA.1 hAN)

theorem M11Pic.conjSub_vertex (c : LocOK Ω x) {V : Subgroup G}
    (hV : V ∈ compMembers3 Ω x P.D P.i₀) {g : G} (hg : g * x * g⁻¹ = x) : conjSub g V = V := by
  have hV' : conjSub g V ∈ centralizingMembers Ω {x} :=
    conjSub_mem_centralizingMembers3 c.hΩ.conjInvariant hg hV.1
  by_contra hne
  have hmem := P.mem_i₁ c hV hV' hne
  have hu : Universal3 Ω x (conjSub g V) := by
    have := universal3_conj c.hΩ.conjInvariant g x (P.vertex_universal c hV)
    rwa [hg] at this
  exact P.not_universal c hmem hu

theorem comm_of_central_commutator {H : Type*} [Group H] (O : Subgroup H)
    (hOc : O ≤ Subgroup.center H) (hodd : Odd (Nat.card O)) {a b : H} (ha : a * a = 1)
    (hb : b * b = 1) (hq : a * b * a⁻¹ * b⁻¹ ∈ O) : a * b = b * a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [hai, hbi] at hq
  have hcen : a * b * a * b ∈ Subgroup.center H := hOc hq
  have h1 : a * (a * b * a * b) * a = a * b * a * b := by
    have := Subgroup.mem_center_iff.mp hcen a
    calc a * (a * b * a * b) * a = (a * b * a * b) * a * a := by rw [this]
      _ = (a * b * a * b) * (a * a) := by group
      _ = a * b * a * b := by rw [ha, mul_one]
  have h2 : a * (a * b * a * b) * a = b * a * b * a := by
    calc a * (a * b * a * b) * a = (a * a) * b * a * b * a := by group
      _ = b * a * b * a := by rw [ha, one_mul]
  have h3 : a * b * a * b = b * a * b * a := h1.symm.trans h2
  have hqq : (a * b * a * b) * (a * b * a * b) = 1 := by
    calc (a * b * a * b) * (a * b * a * b) = (a * b * a * b) * (b * a * b * a) := by rw [← h3]
      _ = a * b * a * (b * b) * a * b * a := by group
      _ = a * b * a * 1 * a * b * a := by rw [hb]
      _ = a * b * (a * a) * b * a := by group
      _ = a * (b * b) * a := by rw [ha]; group
      _ = 1 := by rw [hb, mul_one, ha]
  have h2' : (⟨a * b * a * b, hq⟩ : O) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hqq
  have hd : orderOf (⟨a * b * a * b, hq⟩ : O) ∣ 2 := orderOf_dvd_of_pow_eq_one h2'
  have hodd' : Odd (orderOf (⟨a * b * a * b, hq⟩ : O)) :=
    Odd.of_dvd_nat hodd (orderOf_dvd_natCard _)
  have hord : orderOf (⟨a * b * a * b, hq⟩ : O) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  have hq1 : a * b * a * b = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp hord)
  have hab : (a * b) * (a * b) = 1 := by
    simpa [mul_assoc] using hq1
  have := eq_inv_of_mul_eq_one_left hab
  rw [this, mul_inv_rev, hai, hbi]

theorem commute_of_locMk_commute (hP1 : LocalOddCentral Ω {x}) {u u' : G}
    (hu : u ∈ locLayer Ω x) (hu' : u' ∈ locLayer Ω x) (hu2 : u * u = 1) (hu'2 : u' * u' = 1)
    (h : Gaps.locMk Ω x ⟨u, hu⟩ * Gaps.locMk Ω x ⟨u', hu'⟩ =
      Gaps.locMk Ω x ⟨u', hu'⟩ * Gaps.locMk Ω x ⟨u, hu⟩) : u * u' = u' * u := by
  have ha2 : (⟨u, hu⟩ : ↥(locLayer Ω x)) * ⟨u, hu⟩ = 1 := Subtype.ext hu2
  have hb2 : (⟨u', hu'⟩ : ↥(locLayer Ω x)) * ⟨u', hu'⟩ = 1 := Subtype.ext hu'2
  have hq : (⟨u, hu⟩ : ↥(locLayer Ω x)) * ⟨u', hu'⟩ * (⟨u, hu⟩ : ↥(locLayer Ω x))⁻¹ *
      (⟨u', hu'⟩ : ↥(locLayer Ω x))⁻¹ ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := by
    rw [← QuotientGroup.eq_one_iff]
    have : Gaps.locMk Ω x ((⟨u, hu⟩ : ↥(locLayer Ω x)) * ⟨u', hu'⟩ *
        (⟨u, hu⟩ : ↥(locLayer Ω x))⁻¹ * (⟨u', hu'⟩ : ↥(locLayer Ω x))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
      group
    exact this
  have := comm_of_central_commutator _ hP1 (CFSG.ComponentClassification.OddCore.odd_card _)
    ha2 hb2 hq
  exact congrArg Subtype.val this

@[expose, reducible] def M11Pic.HasInv (N : Subgroup G) (u : (P.D.kind P.i₁).G) : Prop :=
  ∃ R, Corr3 Ω x P.D P.i₁ N R ∧ IsClassicalMember3 R u

theorem M11Pic.hasInv_exists (c : LocOK Ω x) {N : Subgroup G}
    (hN : N ∈ compMembers3 Ω x P.D P.i₁) : ∃ u, P.HasInv N u := by
  obtain ⟨R, hR⟩ := exists_corr_left3 c.hΩ c.hex c.hP1 c.hO3 P.D hN
  obtain ⟨u, hu⟩ := m11_fund_classical P.k₁ hR.2.1
  exact ⟨u, R, hR, hu⟩

theorem M11Pic.mem_of_hasInv {N : Subgroup G} {u : (P.D.kind P.i₁).G} (h : P.HasInv N u) :
    N ∈ compMembers3 Ω x P.D P.i₁ := by
  obtain ⟨R, hR, -⟩ := h
  refine ⟨hR.1, ?_⟩
  rw [hR.2.2]
  exact Subgroup.map_le_range _ _

theorem M11Pic.hasInv_unique {N : Subgroup G} {u u' : (P.D.kind P.i₁).G} (h : P.HasInv N u)
    (h' : P.HasInv N u') : u = u' := by
  obtain ⟨R, hR, hu⟩ := h
  obtain ⟨R', hR', hu'⟩ := h'
  have hpow : PowCop3 (P.D.kind P.i₁) := by
    rw [P.k₁]
    exact powCop3_m11
  have := corr_unique_left3 hpow hR hR'
  subst this
  exact m11_involution_unique_gen P.k₁ hu hu'

theorem M11Pic.hasInv_eq (c : LocOK Ω x) {N N' : Subgroup G} {u : (P.D.kind P.i₁).G}
    (h : P.HasInv N u) (h' : P.HasInv N' u) : N = N' := by
  obtain ⟨R, hR, hu⟩ := h
  obtain ⟨R', hR', hu'⟩ := h'
  have := m11_classical_eq_gen P.k₁ hu hu'
  subst this
  exact corr_unique_right3 c.hΩ c.hex c.hP1 c.hO3 hR hR'

theorem M11Pic.exists_hasInv_of_involution (c : LocOK Ω x) {u : (P.D.kind P.i₁).G}
    (hu : orderOf u = 2) : ∃ N, P.HasInv N u := by
  obtain ⟨A, B, hA, hB, hAB⟩ := P.exists_ne c
  obtain ⟨w₀, R₀, -, hcl₀⟩ := P.hasInv_exists c hA
  obtain ⟨R, hR⟩ := m11_exists_classical_gen P.k₁ hcl₀ hu
  obtain ⟨N, hN⟩ := exists_corr_right3 c.hΩ P.D (m11_singleClass_gen P.k₁)
    (m11_mem_fund_of_classical P.k₁ hR)
  exact ⟨N, R, hN, hR⟩

theorem M11Pic.locMk_eq (c : LocOK Ω x) {N : Subgroup G} {u : (P.D.kind P.i₁).G} {z : G}
    (hN : N ∈ centralizingMembers Ω {x}) (hz : IsClassicalMember3 N z) (hu : P.HasInv N u) :
    Gaps.locMk Ω x ⟨z, le_centralizingLayer hN hz.mem⟩ = P.D.hom P.i₁ u := by
  obtain ⟨R, hR, hRu⟩ := hu
  have hU := ConnectedA2.isUniqueInvolution_locImg c.hex hN
    (isUniqueInvolution_of_exact3 (c.hex N hN.1) hz)
  rw [hR.2.2] at hU
  have hinj := m11_hom_injective_gen P.k₁ (P.D.hom P.i₁) (P.D.ker_le_center P.i₁)
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hRu.orderOf_eq_two, pow_two] at this
  have hu1 : P.D.hom P.i₁ u ≠ 1 := fun h => hRu.ne_one (hinj (h.trans (map_one _).symm))
  rcases hU.unique (P.D.hom P.i₁ u) ⟨u, hRu.mem, rfl⟩
    (by rw [← map_mul, hu2, map_one]) with h | h
  · exact absurd h hu1
  · exact h.symm

@[expose] def MemAdj (A B : Subgroup G) : Prop :=
  A ≠ B ∧ ∃ zA zB : G, IsClassicalMember3 A zA ∧ IsClassicalMember3 B zB ∧ zA * zB = zB * zA

@[expose, reducible] def M11Pic.Step (N N' : Subgroup G) : Prop :=
  N ∈ compMembers3 Ω x P.D P.i₁ ∧ N' ∈ compMembers3 Ω x P.D P.i₁ ∧ MemAdj N N'

private theorem M11Pic.chain_aux (c : LocOK Ω x) {u v : (P.D.kind P.i₁).G}
    (h : Relation.ReflTransGen InvAdj u v) :
    ∀ {A B : Subgroup G}, P.HasInv A u → P.HasInv B v → Relation.ReflTransGen P.Step A B := by
  induction h with
  | refl =>
    intro A B hA hB
    have hAB := P.hasInv_eq c hA hB
    subst hAB
    exact Relation.ReflTransGen.refl
  | tail hchain hstep ih =>
    rename_i v' v
    intro A B hA hB
    obtain ⟨B', hB'⟩ := P.exists_hasInv_of_involution c hstep.1
    refine (ih hA hB').tail ⟨P.mem_of_hasInv hB', P.mem_of_hasInv hB, ?_, ?_⟩
    · intro hBB
      subst hBB
      exact hstep.2.2.1 (P.hasInv_unique hB' hB)
    · have hB'm := P.mem_of_hasInv hB'
      have hBm := P.mem_of_hasInv hB
      obtain ⟨zA, hzA⟩ := c.hΩ.classical B' hB'm.1.1
      obtain ⟨zB, hzB⟩ := c.hΩ.classical B hBm.1.1
      refine ⟨zA, zB, hzA, hzB, ?_⟩
      have h1 := P.locMk_eq c hB'm.1 hzA hB'
      have h2 := P.locMk_eq c hBm.1 hzB hB
      refine commute_of_locMk_commute c.hP1 (le_centralizingLayer hB'm.1 hzA.mem)
        (le_centralizingLayer hBm.1 hzB.mem) ?_ ?_ ?_
      · have := hzA.orderOf_eq_two
        have h3 := pow_orderOf_eq_one zA
        rwa [this, pow_two] at h3
      · have := hzB.orderOf_eq_two
        have h3 := pow_orderOf_eq_one zB
        rwa [this, pow_two] at h3
      · rw [h1, h2, ← map_mul, ← map_mul, hstep.2.2.2]

theorem M11Pic.members_connected (c : LocOK Ω x) {N N' : Subgroup G}
    (hN : N ∈ compMembers3 Ω x P.D P.i₁) (hN' : N' ∈ compMembers3 Ω x P.D P.i₁) :
    Relation.ReflTransGen P.Step N N' := by
  obtain ⟨u, hu⟩ := P.hasInv_exists c hN
  obtain ⟨u', hu'⟩ := P.hasInv_exists c hN'
  have hu2 : orderOf u = 2 := by
    obtain ⟨R, -, hR⟩ := hu
    exact hR.orderOf_eq_two
  have hu'2 : orderOf u' = 2 := by
    obtain ⟨R, -, hR⟩ := hu'
    exact hR.orderOf_eq_two
  exact P.chain_aux c (m11_comm_connected_gen P.k₁ hu2 hu'2) hu hu'

end Pic

end CFSG.ClassicalInvolution.Q3.Q3W
