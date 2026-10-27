module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fL2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section WIn

open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

theorem wIn_data {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (h8 : ∀ J ∈ Ω, Nat.card J = 8) {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hPne : P.Nonempty)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) {W : Subgroup G}
    (hW : WIn P (pSpan P) = {W}) :
    W ≤ pSpan P ∧ IsPGroup 2 ↥W ∧ (∀ x ∈ pSpan P, ∀ q ∈ W, x * q * x⁻¹ ∈ W) ∧
      (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) ∧ ∃ J ∈ P, ∃ b ∈ J, b ∈ W ∧ b * b ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := pSpan P with hX
  have hLX : ∀ L ∈ P, L ≤ X := fun L hL => le_pSpan hL
  have hc' : ConjInvariant (restrictFamily P X) :=
    conjInvariant_restrictFamily fun L hL x hx => hinv L hL x hx
  have hΩ' : HypOmegaGen (restrictFamily P X) := by
    refine TL4.hypOmegaGen_restrict_of X hLX (fun n hn L hL => hinv L hL n hn)
      (fun K hK => hΩ.omega1 K (hPΩ hK)) (fun K hK => ?_)
      (fun K hK J hJ => hΩ.omega3 K (hPΩ hK) J (hPΩ hJ))
      (fun K hK J hJ hne => hΩ.omega4 K (hPΩ hK) J (hPΩ hJ) hne)
      (fun K hK J hJ hne => hΩ.omega5 K (hPΩ hK) J (hPΩ hJ) hne)
    refine le_antisymm (Subgroup.closure_le _ |>.mpr fun x hx => hx.1) fun x hx => ?_
    exact Subgroup.subset_closure ⟨hx, (h2 K (hPΩ hK)).to_le (Subgroup.zpowers_le.mpr hx)⟩
  have hWmem : W ∈ WIn P X := by rw [hW]; rfl
  obtain ⟨W', hW'mem, rfl⟩ := hWmem
  have hW'uniq : ∀ W'' ∈ WSet (restrictFamily P X), W'' = W' := by
    intro W'' h
    have h1 : W''.map X.subtype ∈ WIn P X := ⟨W'', h, rfl⟩
    rw [hW] at h1
    exact Subgroup.map_injective X.subtype_injective h1
  have hnorm' : ∀ g : X, conjSub g W' = W' := fun g => hW'uniq _ (WSet.conj hc' hW'mem g)
  have hab' := Q3CL.Thompson.commutes_of_mem_WSet hΩ' hW'mem
  obtain ⟨η, ⟨S, hη, -⟩, hW'eq⟩ := hW'mem
  have hWS : W' ≤ (S : Subgroup X) := by
    rw [hW'eq]
    exact iSup₂_le fun U hU => (hη.1 hU).2
  have hW2 : IsPGroup 2 ↥(W'.map X.subtype) := (S.isPGroup'.to_le hWS).map _
  have hWX : W'.map X.subtype ≤ X := Subgroup.map_subtype_le _
  have hnorm : ∀ x ∈ X, ∀ q ∈ W'.map X.subtype, x * q * x⁻¹ ∈ W'.map X.subtype := by
    rintro x hx _ ⟨q, hq, rfl⟩
    have h1 : (⟨x, hx⟩ : X) * q * (⟨x, hx⟩ : X)⁻¹ ∈ conjSub (⟨x, hx⟩ : X) W' :=
      conj_mem_conjSub hq
    rw [hnorm'] at h1
    exact ⟨_, h1, rfl⟩
  have habel : ∀ a ∈ W'.map X.subtype, ∀ b ∈ W'.map X.subtype, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hab' a ha b hb)
  refine ⟨hWX, hW2, hnorm, habel, ?_⟩
  obtain ⟨L, hL⟩ := hPne
  have hL'2 : IsPGroup 2 ↥(L.subgroupOf X) := (h2 L (hPΩ hL)).comap_subtype
  obtain ⟨S'', hS''⟩ := hL'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S'' S
  have hgS : conjSub g (L.subgroupOf X) ≤ (S : Subgroup X) := by
    rw [← hg, Sec7.coe_smul_sylow]
    exact conjSub_mono hS''
  rw [conjSub_subgroupOf] at hgS
  set L₁ := conjSub (g : G) L with hL₁
  have hL₁P : L₁ ∈ P := hinv L hL g g.2
  have hL₁X : L₁ ≤ X := le_pSpan hL₁P
  obtain ⟨⟨z₁, hz₁⟩, Q₁, hQ₁, hQ₁nc⟩ := hΩ.omega1 L₁ (hPΩ hL₁P)
  have hN'8 : Nat.card ↥(L₁.subgroupOf X) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁X).toEquiv]
    exact h8 L₁ (hPΩ hL₁P)
  have hz₁' := isUniqueInvolution_subgroupOf hz₁ hL₁X
  obtain ⟨x', hx'N, hx'2⟩ := exists_sq_ne_one hz₁' hN'8
  have hnc' : ∃ Q : Subgroup X, IsSylow2In Q (L₁.subgroupOf X) ∧ ¬ IsMulCommutative ↥Q := by
    refine ⟨Q₁.subgroupOf X, hQ₁.subgroupOf hL₁X, fun hc => hQ₁nc ?_⟩
    let e : Q₁.subgroupOf X ≃* Q₁ := Subgroup.subgroupOfEquivOfLe (hQ₁.1.trans hL₁X)
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 : e.symm a * e.symm b = e.symm b * e.symm a := hc.is_comm.comm _ _
    have h2' := congrArg e h1
    simpa using h2'
  obtain ⟨hU1, -⟩ := zpowers_mem_USet (P := restrictFamily P X) ⟨L₁, hL₁P, hL₁X, rfl⟩
    (h2 L₁ (hPΩ hL₁P)).comap_subtype hN'8 hnc' hx'N hx'2
  have hU1S : Subgroup.zpowers x' ≤ (S : Subgroup X) :=
    (Subgroup.zpowers_le.mpr hx'N).trans hgS
  have hηpos : η.ncard ≠ 0 := by
    have h1 := hη.2.2 {Subgroup.zpowers x'} (by
      intro U hU
      rw [Set.mem_singleton_iff.mp hU]
      exact ⟨hU1, hU1S⟩) (by
      intro U hU U' hU' hne
      exact absurd ((Set.mem_singleton_iff.mp hU).trans (Set.mem_singleton_iff.mp hU').symm) hne)
    rw [Set.ncard_singleton] at h1
    omega
  obtain ⟨U₀, hU₀⟩ := Set.nonempty_of_ncard_ne_zero hηpos
  obtain ⟨hU₀U, -⟩ := hη.1 hU₀
  obtain ⟨R₀, hR₀, hU₀R₀, -, hidx⟩ := hU₀U
  obtain ⟨J₀', hJ₀', hR₀J₀, -, hmax⟩ := mem_RSet_iff.mp hR₀
  obtain ⟨J₀, hJ₀, hJ₀X, rfl⟩ := hJ₀'
  have hJ₀'2 : IsPGroup 2 ↥(J₀.subgroupOf X) := (h2 J₀ (hPΩ hJ₀)).comap_subtype
  have hR₀eq : J₀.subgroupOf X = R₀ := hmax _ le_rfl hJ₀'2 hR₀J₀
  have hU₀card : Nat.card U₀ = 4 := by
    have h1 := Subgroup.relIndex_mul_card U₀ R₀
    rw [inf_eq_left.mpr hU₀R₀, hidx, ← hR₀eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ₀X).toEquiv, h8 J₀ (hPΩ hJ₀)] at h1
    omega
  obtain ⟨⟨z₀, hz₀⟩, -⟩ := hΩ.omega1 J₀ (hPΩ hJ₀)
  have hU₀W : U₀ ≤ W' := by
    rw [hW'eq]
    exact le_biSup (fun U => U) hU₀
  refine ⟨J₀, hJ₀, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsub : ((U₀.map X.subtype : Subgroup G) : Set G) ⊆ ({1, z₀} : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : G) ∈ J₀ := Subgroup.mem_subgroupOf.mp (hR₀J₀ (hU₀R₀ hu))
    have hsq := hcon (u : G) hu' ⟨u, hU₀W hu, rfl⟩
    rcases hz₀.unique (u : G) hu' hsq with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hle : Nat.card ↥(U₀.map X.subtype) ≤ ({1, z₀} : Set G).ncard := by
    rw [← SetLike.coe_sort_coe, ← Nat.card_coe_set_eq]
    exact Nat.card_mono (Set.toFinite _) hsub
  rw [Subgroup.card_map_of_injective X.subtype_injective, hU₀card] at hle
  have h3 : ({1, z₀} : Set G).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : G) ({z₀} : Set G)
    rw [Set.ncard_singleton] at this
    exact this
  omega

end WIn

theorem comp_in_cyc {Y : Type} [Group Y] {J : Subgroup Y} {t : Y} (hq8 : WF.Q8Facts J t)
    {a k b r r' : Y} (ha : a ∈ J) (haa : a * a = t) (hk : k ∈ J) (hk1 : k ≠ 1) (hkt : k ≠ t)
    (hb : b ∈ J) (hbb : b * b = t) (hr : ∀ j ∈ J, j * r = r * j) (hr' : ∀ j ∈ J, j * r' = r' * j)
    (hbz : b * (a * r) = (a * r) * b) (hbw : b * (k * r') = (k * r') * b) : k = a ∨ k = a * t := by
  have comm_of : ∀ {c c' : Y}, c ∈ J → (∀ j ∈ J, j * c' = c' * j) → b * (c * c') = (c * c') * b →
      b * c = c * b := by
    intro c c' _ hc' h
    have h1 : (b * c) * c' = (c * b) * c' := by
      calc (b * c) * c' = b * (c * c') := by rw [mul_assoc]
        _ = (c * c') * b := h
        _ = c * (c' * b) := by rw [mul_assoc]
        _ = c * (b * c') := by rw [← hc' b hb]
        _ = (c * b) * c' := by rw [mul_assoc]
    exact mul_right_cancel h1
  have hba : b * a = a * b := comm_of ha hr hbz
  have hbk : b * k = k * b := comm_of hk hr' hbw
  have htt : t * t = 1 := hq8.z_sq
  have ht1 : t ≠ 1 := hq8.z_ne
  have hacases := hq8.cent_cyc b hb hbb a ha hba.symm
  have hkcases := hq8.cent_cyc b hb hbb k hk hbk.symm
  have ha1 : a ≠ 1 := fun e => ht1 (by rw [← haa, e, mul_one])
  have hat : a ≠ t := fun e => ht1 (by rw [e, htt] at haa; exact haa.symm)
  have hbt : b * t * t = b := by rw [mul_assoc, htt, mul_one]
  rcases hacases with e | e | e | e
  · exact absurd e ha1
  · rcases hkcases with e' | e' | e' | e'
    · exact absurd e' hk1
    · left; rw [e', e]
    · exact absurd e' hkt
    · right; rw [e', e]
  · exact absurd e hat
  · rcases hkcases with e' | e' | e' | e'
    · exact absurd e' hk1
    · right; rw [e', e, hbt]
    · exact absurd e' hkt
    · left; rw [e', e]

theorem not_cent_of_comp {Y : Type} [Group Y] {J : Subgroup Y} {t a r z : Y} (hq8 : WF.Q8Facts J t)
    (ha : a ∈ J) (haa : a * a = t) (hr : ∀ j ∈ J, j * r = r * j) (hz : z = a * r) :
    ¬ ∀ j ∈ J, j * z = z * j := by
  intro hc
  have hac : ∀ g ∈ J, a * g = g * a := fun g hg => by
    have h1 := hc g hg
    rw [hz] at h1
    have : g * a * r = a * g * r := by
      calc g * a * r = g * (a * r) := by rw [mul_assoc]
        _ = (a * r) * g := h1
        _ = a * (r * g) := by rw [mul_assoc]
        _ = a * (g * r) := by rw [← hr g hg]
        _ = a * g * r := by rw [mul_assoc]
    exact (mul_right_cancel this).symm
  rcases hq8.center a ha hac with e | e
  · rw [e, mul_one] at haa
    exact hq8.z_ne haa.symm
  · rw [e, hq8.z_sq] at haa
    exact hq8.z_ne haa.symm

theorem cent_of_central_comp {Y : Type} [Group Y] {J : Subgroup Y} {t k r z : Y}
    (hq8 : WF.Q8Facts J t) (hk : k = 1 ∨ k = t) (hr : ∀ j ∈ J, j * r = r * j) (hz : z = k * r) :
    ∀ j ∈ J, j * z = z * j := by
  intro j hj
  rw [hz]
  rcases hk with hk | hk
  · rw [hk, one_mul]
    exact hr j hj
  · rw [hk]
    calc j * (t * r) = (j * t) * r := by rw [mul_assoc]
      _ = (t * j) * r := by rw [← hq8.z_central j hj]
      _ = t * (j * r) := by rw [mul_assoc]
      _ = t * (r * j) := by rw [hr j hj]
      _ = t * r * j := by rw [mul_assoc]

section Datum

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}
  (C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y)

include C in
theorem prod4_comp {k₁ k₂ k₃ k₄ : Y} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K') (hk₃ : k₃ ∈ K₃)
    (hk₄ : k₄ ∈ K₄) :
    (∃ r ∈ ae6P Ω[R] t, (∀ j ∈ K, j * r = r * j) ∧ k₁ * k₂ * k₃ * k₄ = k₁ * r) ∧
    (∃ r ∈ ae6P Ω[R] t, (∀ j ∈ K', j * r = r * j) ∧ k₁ * k₂ * k₃ * k₄ = k₂ * r) ∧
    (∃ r ∈ ae6P Ω[R] t, (∀ j ∈ K₃, j * r = r * j) ∧ k₁ * k₂ * k₃ * k₄ = k₃ * r) ∧
    (∃ r ∈ ae6P Ω[R] t, (∀ j ∈ K₄, j * r = r * j) ∧ k₁ * k₂ * k₃ * k₄ = k₄ * r) := by
  obtain ⟨hne12, hne13, hne14, hne23, hne24, hne34⟩ := C.twins_ne
  have hKP : K ≤ ae6P Ω[R] t := A6Hx.le_ae6P C.H.ex.1.datum.mem C.H.ex.1.datum.hz
  have hK'P : K' ≤ ae6P Ω[R] t := A6Hx.le_ae6P C.H.ex.1.datum.hK'.1 (C.uniq C.hK't)
  have hK₃P : K₃ ≤ ae6P Ω[R] t := A6Hx.le_ae6P C.H.ex.1.datum.hK₃.1 (C.uniq C.hK₃t)
  have hK₄P : K₄ ≤ ae6P Ω[R] t := A6Hx.le_ae6P C.H.ex.2.1.1.1 (C.uniq C.hK₄t)
  have c12 : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hKt C.hK't hne12 a ha b hb
  have c13 : ∀ a ∈ K, ∀ b ∈ K₃, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hKt C.hK₃t hne13 a ha b hb
  have c14 : ∀ a ∈ K, ∀ b ∈ K₄, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hKt C.hK₄t hne14 a ha b hb
  have c23 : ∀ a ∈ K', ∀ b ∈ K₃, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hK't C.hK₃t hne23 a ha b hb
  have c24 : ∀ a ∈ K', ∀ b ∈ K₄, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hK't C.hK₄t hne24 a ha b hb
  have c34 : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hK₃t C.hK₄t hne34 a ha b hb
  have cp3 : ∀ {j a b c : Y}, j * a = a * j → j * b = b * j → j * c = c * j →
      j * (a * b * c) = (a * b * c) * j := fun {j a b c} ha hb hc =>
    (((show Commute j a from ha).mul_right (show Commute j b from hb)).mul_right
      (show Commute j c from hc)).eq
  have mul3 : ∀ {a b c : Y}, a ∈ ae6P Ω[R] t → b ∈ ae6P Ω[R] t → c ∈ ae6P Ω[R] t →
      a * b * c ∈ ae6P Ω[R] t := fun ha hb hc =>
    (ae6P Ω[R] t).mul_mem ((ae6P Ω[R] t).mul_mem ha hb) hc
  refine ⟨⟨k₂ * k₃ * k₄, mul3 (hK'P hk₂) (hK₃P hk₃) (hK₄P hk₄),
      fun j hj => cp3 (c12 j hj k₂ hk₂) (c13 j hj k₃ hk₃) (c14 j hj k₄ hk₄), ?_⟩,
    ⟨k₁ * k₃ * k₄, mul3 (hKP hk₁) (hK₃P hk₃) (hK₄P hk₄),
      fun j hj => cp3 (c12 k₁ hk₁ j hj).symm (c23 j hj k₃ hk₃) (c24 j hj k₄ hk₄), ?_⟩,
    ⟨k₁ * k₂ * k₄, mul3 (hKP hk₁) (hK'P hk₂) (hK₄P hk₄),
      fun j hj => cp3 (c13 k₁ hk₁ j hj).symm (c23 k₂ hk₂ j hj).symm (c34 j hj k₄ hk₄), ?_⟩,
    ⟨k₁ * k₂ * k₃, mul3 (hKP hk₁) (hK'P hk₂) (hK₃P hk₃),
      fun j hj => cp3 (c14 k₁ hk₁ j hj).symm (c24 k₂ hk₂ j hj).symm (c34 k₃ hk₃ j hj).symm, ?_⟩⟩
  · simp only [mul_assoc]
  · rw [c12 k₁ hk₁ k₂ hk₂]
    simp only [mul_assoc]
  · simp only [mul_assoc]
    rw [swap_mul (c13 k₁ hk₁ k₃ hk₃).symm (k₂ * k₄), swap_mul (c23 k₂ hk₂ k₃ hk₃).symm k₄]
  · simp only [mul_assoc]
    rw [swap_mul (c14 k₁ hk₁ k₄ hk₄).symm (k₂ * k₃), swap_mul (c24 k₂ hk₂ k₄ hk₄).symm k₃,
      (c34 k₃ hk₃ k₄ hk₄).symm]

end Datum

section LDatum

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}
  (Z : LCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h)

include Z in
theorem tau_not_cent {J : Subgroup Y} (hJ : J ∈ ae6Vc Ω[R] t) :
    ¬ ∀ j ∈ J, j * tauE t y = tauE t y * j := by
  have fr := Z.C.fr
  obtain ⟨c1, c2, c3, c4⟩ := prod4_comp Z.C fr.h₁.1 fr.h₂.1 fr.h₃.1 fr.h₄.1
  have hτ : tauE t y = a₁ * a₂ * a₃ * a₄ := fr.hy
  rcases (mem_ae6Vc_iff Z.C).mp hJ with rfl | rfl | rfl | rfl
  · obtain ⟨r, -, hr, he⟩ := c1
    exact not_cent_of_comp (Z.C.twin_q8 Z.C.hKt) fr.h₁.1
      (Asc77.sq_eq_of_orderOf_four (Z.C.uniq Z.C.hKt) fr.h₁.1 fr.o₁) hr (hτ.trans he)
  · obtain ⟨r, -, hr, he⟩ := c2
    exact not_cent_of_comp (Z.C.twin_q8 Z.C.hK't) fr.h₂.1
      (Asc77.sq_eq_of_orderOf_four (Z.C.uniq Z.C.hK't) fr.h₂.1 fr.o₂) hr (hτ.trans he)
  · obtain ⟨r, -, hr, he⟩ := c3
    exact not_cent_of_comp (Z.C.twin_q8 Z.C.hK₃t) fr.h₃.1
      (Asc77.sq_eq_of_orderOf_four (Z.C.uniq Z.C.hK₃t) fr.h₃.1 fr.o₃) hr (hτ.trans he)
  · obtain ⟨r, -, hr, he⟩ := c4
    exact not_cent_of_comp (Z.C.twin_q8 Z.C.hK₄t) fr.h₄.1
      (Asc77.sq_eq_of_orderOf_four (Z.C.uniq Z.C.hK₄t) fr.h₄.1 fr.o₄) hr (hτ.trans he)

include Z in
theorem x_not_cent {J : Subgroup Y} (hJ : J ∈ ae6Vc Ω[R] t) :
    ¬ ∀ j ∈ J, j * xE t y h = xE t y h * j := by
  intro hc
  have hhC := Z.hx.1
  have hht : h⁻¹ * t * h⁻¹⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.centralizer ({t} : Set Y)).inv_mem hhC)
    rw [this, mul_inv_cancel_right]
  have hJ' : conjSub h⁻¹ J ∈ ae6Vc Ω[R] t := by
    refine ⟨conjInvariant_conjClass (tightCore R) h⁻¹ J hJ.1, ?_⟩
    have := hJ.2.conj h⁻¹
    rwa [hht] at this
  refine tau_not_cent Z hJ' ?_
  intro j' hj'
  have hj : h * j' * h⁻¹ ∈ J := by
    have := mem_conjSub_iff.mp hj'
    simpa [mul_assoc] using this
  have h1 := hc _ hj
  have e : j' * tauE t y = h⁻¹ * ((h * j' * h⁻¹) * xE t y h) * h := by
    simp only [xE, tauE]
    group
  have e' : tauE t y * j' = h⁻¹ * (xE t y h * (h * j' * h⁻¹)) * h := by
    simp only [xE, tauE]
    group
  rw [e, e', h1]

include Z in
theorem false_of_wIn_eq {W₀ : Subgroup Y}
    (hW : WIn (ae6ConjIn (ae6L Ω[R] t (tauE t y) (xE t y h)) K)
      (pSpan (ae6ConjIn (ae6L Ω[R] t (tauE t y) (xE t y h)) K)) = {W₀}) : False := by
  have hd := Z.C.H.ex.1.datum
  have fr := Z.C.fr
  have hΩ := A6d.hypOf Z.C.H
  have h2 := A6d.h2Of Z.C.H
  have h8 := A6d.h8Of Z.C.H
  have htt : t * t = 1 := hd.hz.sq
  set L := ae6L Ω[R] t (tauE t y) (xE t y h) with hLdef
  set P := ae6ConjIn L K with hPdef
  have hspan : pSpan P = L := pSpan_KL Z
  have hPΩ : P ⊆ Ω[R] := A6d.ae6ConjIn_subset hΩ.conjInvariant hd.mem
  have hinv : ∀ L' ∈ P, ∀ x ∈ pSpan P, conjSub x L' ∈ P := fun L' hL' x hx =>
    A6d.conjSub_mem_of_mem_ae6ConjIn (by rw [hspan] at hx; exact hx) hL'
  have hPne : P.Nonempty := ⟨K, A6d.mem_ae6ConjIn_self⟩
  obtain ⟨-, -, hW₀norm', hW₀ab, J, hJP, b, hbJ, hbW, hbb⟩ :=
    wIn_data hΩ h2 h8 hPΩ hPne hinv hW
  have hW₀norm : ∀ g ∈ L, ∀ q ∈ W₀, g * q * g⁻¹ ∈ W₀ := fun g hg q hq =>
    hW₀norm' g (by rw [hspan]; exact hg) q hq
  obtain ⟨g, hg, rfl⟩ := hJP
  have hb₀K : g⁻¹ * b * g ∈ K := mem_conjSub_iff.mp hbJ
  have hb₀W : g⁻¹ * b * g ∈ W₀ := by simpa using hW₀norm g⁻¹ (L.inv_mem hg) b hbW
  have hb₀1 : (g⁻¹ * b * g) * (g⁻¹ * b * g) ≠ 1 := by
    intro e
    apply hbb
    have : b * b = g * ((g⁻¹ * b * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    rw [this, e]
    group
  have hb₀t : (g⁻¹ * b * g) * (g⁻¹ * b * g) = t :=
    ((Z.C.twin_q8 Z.C.hKt).sq_cases _ hb₀K).resolve_left hb₀1
  have htW : t ∈ W₀ := hb₀t ▸ W₀.mul_mem hb₀W hb₀W
  have hEW : ∀ e ∈ e3 t y h, e ∈ W₀ := by
    intro e he
    by_cases h1 : e = 1
    · rw [h1]; exact W₀.one_mem
    · obtain ⟨ℓ, hℓ, hℓe⟩ := exists_conj_t_of_mem_E3 Z he h1
      rw [← hℓe]
      exact hW₀norm ℓ hℓ t htW
  have hbtw : ∀ J' ∈ ae6Vc Ω[R] t, ∃ bJ ∈ J', bJ ∈ W₀ ∧ bJ * bJ = t := by
    intro J' hJ'
    obtain ⟨ℓ, hℓ, hℓJ⟩ := mem_KL_of_inv_mem_E3 Z hJ'.1 hJ'.2 (t_mem_e3 t y h)
    have hmem : ℓ * (g⁻¹ * b * g) * ℓ⁻¹ ∈ J' := by
      rw [← hℓJ]
      exact conj_mem_conjSub hb₀K
    refine ⟨ℓ * (g⁻¹ * b * g) * ℓ⁻¹, hmem, hW₀norm ℓ hℓ _ hb₀W, ?_⟩
    rcases (Z.C.twin_q8 (ae6Vc_subset_twinSet Z.C hJ')).sq_cases _ hmem with e | e
    · exfalso
      apply hb₀1
      have : (g⁻¹ * b * g) * (g⁻¹ * b * g) =
          ℓ⁻¹ * ((ℓ * (g⁻¹ * b * g) * ℓ⁻¹) * (ℓ * (g⁻¹ * b * g) * ℓ⁻¹)) * ℓ := by group
      rw [this, e]
      group
    · exact e
  have hτW : tauE t y ∈ W₀ := hEW _ (tau_mem_e3 t y h)
  have hxW : xE t y h ∈ W₀ := hEW _ (x_mem_e3 t y h)
  have hxP : xE t y h ∈ ae6P Ω[R] t := Z.hEt (x_mem_e3 t y h)
  obtain ⟨k₁, hk₁, k₂, hk₂, k₃, hk₃, k₄, hk₄, hxk⟩ := exists_prod4 Z.C hxP
  obtain ⟨c1, c2, c3, c4⟩ := prod4_comp Z.C hk₁ hk₂ hk₃ hk₄
  obtain ⟨d1, d2, d3, d4⟩ := prod4_comp Z.C fr.h₁.1 fr.h₂.1 fr.h₃.1 fr.h₄.1
  have hτ : tauE t y = a₁ * a₂ * a₃ * a₄ := fr.hy
  have hKv : K ∈ ae6Vc Ω[R] t := (mem_ae6Vc_iff Z.C).mpr (Or.inl rfl)
  have hK'v : K' ∈ ae6Vc Ω[R] t := (mem_ae6Vc_iff Z.C).mpr (Or.inr (Or.inl rfl))
  have hK₃v : K₃ ∈ ae6Vc Ω[R] t := (mem_ae6Vc_iff Z.C).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hK₄v : K₄ ∈ ae6Vc Ω[R] t := (mem_ae6Vc_iff Z.C).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have per : ∀ (J : Subgroup Y) (a k r r' : Y), J ∈ ae6Vc Ω[R] t → a ∈ J → a * a = t → k ∈ J →
      (∀ j ∈ J, j * r = r * j) → (∀ j ∈ J, j * r' = r' * j) → a * r = tauE t y →
      k * r' = xE t y h → (k = a ∨ k = a * t) := by
    intro J a k r r' hJv ha haa hk hr hr' har hkr'
    have hq8 := Z.C.twin_q8 (ae6Vc_subset_twinSet Z.C hJv)
    obtain ⟨bJ, hbJJ, hbJW, hbJ2⟩ := hbtw J hJv
    have hkn : k ≠ 1 ∧ k ≠ t :=
      ⟨fun e => x_not_cent Z hJv (cent_of_central_comp hq8 (Or.inl e) hr' hkr'.symm),
        fun e => x_not_cent Z hJv (cent_of_central_comp hq8 (Or.inr e) hr' hkr'.symm)⟩
    refine comp_in_cyc hq8 ha haa hk hkn.1 hkn.2 hbJJ hbJ2 hr hr' ?_ ?_
    · rw [har]
      exact hW₀ab _ hbJW _ hτW
    · rw [hkr']
      exact hW₀ab _ hbJW _ hxW
  obtain ⟨r₁, -, hr₁, hr₁e⟩ := d1
  obtain ⟨r₂, -, hr₂, hr₂e⟩ := d2
  obtain ⟨r₃, -, hr₃, hr₃e⟩ := d3
  obtain ⟨r₄, -, hr₄, hr₄e⟩ := d4
  obtain ⟨s₁, -, hs₁, hs₁e⟩ := c1
  obtain ⟨s₂, -, hs₂, hs₂e⟩ := c2
  obtain ⟨s₃, -, hs₃, hs₃e⟩ := c3
  obtain ⟨s₄, -, hs₄, hs₄e⟩ := c4
  have e1 := per K a₁ k₁ r₁ s₁ hKv fr.h₁.1
    (Asc77.sq_eq_of_orderOf_four (Z.C.uniq Z.C.hKt) fr.h₁.1 fr.o₁) hk₁ hr₁ hs₁
    (hr₁e.symm.trans hτ.symm) (hs₁e.symm.trans hxk.symm)
  have e2 := per K' a₂ k₂ r₂ s₂ hK'v fr.h₂.1
    (Asc77.sq_eq_of_orderOf_four (Z.C.uniq Z.C.hK't) fr.h₂.1 fr.o₂) hk₂ hr₂ hs₂
    (hr₂e.symm.trans hτ.symm) (hs₂e.symm.trans hxk.symm)
  have e3 := per K₃ a₃ k₃ r₃ s₃ hK₃v fr.h₃.1
    (Asc77.sq_eq_of_orderOf_four (Z.C.uniq Z.C.hK₃t) fr.h₃.1 fr.o₃) hk₃ hr₃ hs₃
    (hr₃e.symm.trans hτ.symm) (hs₃e.symm.trans hxk.symm)
  have e4 := per K₄ a₄ k₄ r₄ s₄ hK₄v fr.h₄.1
    (Asc77.sq_eq_of_orderOf_four (Z.C.uniq Z.C.hK₄t) fr.h₄.1 fr.o₄) hk₄ hr₄ hs₄
    (hr₄e.symm.trans hτ.symm) (hs₄e.symm.trans hxk.symm)
  have hδ : ∀ {a k : Y}, (k = a ∨ k = a * t) → ∃ δ, (δ = 1 ∨ δ = t) ∧ k = a * δ := by
    rintro a k (e | e)
    · exact ⟨1, Or.inl rfl, by rw [e, mul_one]⟩
    · exact ⟨t, Or.inr rfl, e⟩
  obtain ⟨δ₁, hδ₁, hk₁e⟩ := hδ e1
  obtain ⟨δ₂, hδ₂, hk₂e⟩ := hδ e2
  obtain ⟨δ₃, hδ₃, hk₃e⟩ := hδ e3
  obtain ⟨δ₄, hδ₄, hk₄e⟩ := hδ e4
  have hδc : ∀ {δ p : Y}, (δ = 1 ∨ δ = t) → p ∈ ae6P Ω[R] t → p * δ = δ * p := by
    intro δ p hδ hp
    rcases hδ with hδ | hδ
    · rw [hδ, mul_one, one_mul]
    · rw [hδ]
      exact ae6P_comm_t Z.C hp
  have haP : ∀ {a : Y} {J : Subgroup Y}, J ∈ ae6Vc Ω[R] t → a ∈ J → a ∈ ae6P Ω[R] t :=
    fun hJ ha => A6Hx.le_ae6P hJ.1 hJ.2 ha
  have mulZ : ∀ a b : Y, (a = 1 ∨ a = t) → (b = 1 ∨ b = t) → (a * b = 1 ∨ a * b = t) := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · left; simp
    · right; simp
    · right; simp
    · left; exact htt
  have hx' : xE t y h = tauE t y * (δ₁ * δ₂ * δ₃ * δ₄) := by
    rw [hxk, hk₁e, hk₂e, hk₃e, hk₄e, hτ]
    exact (mul4_swap (hδc hδ₁ (haP hK'v fr.h₂.1)) (hδc hδ₁ (haP hK₃v fr.h₃.1))
      (hδc hδ₁ (haP hK₄v fr.h₄.1)) (hδc hδ₂ (haP hK₃v fr.h₃.1)) (hδc hδ₂ (haP hK₄v fr.h₄.1))
      (hδc hδ₃ (haP hK₄v fr.h₄.1))).symm
  have hδ' := mulZ _ _ (mulZ _ _ (mulZ _ _ hδ₁ hδ₂) hδ₃) hδ₄
  have htD : t ∈ ae6D Ω[R] W (u₁ * u₂) := Z.C.t_mem_D
  have hτD : tauE t y ∈ ae6D Ω[R] W (u₁ * u₂) := Z.C.tau_mem_D
  have hxD : xE t y h ∈ ae6D Ω[R] W (u₁ * u₂) := by
    rw [hx']
    rcases hδ' with e | e
    · rw [e, mul_one]; exact hτD
    · rw [e]; exact (ae6D Ω[R] W (u₁ * u₂)).mul_mem hτD htD
  exact Z.hx.2.1 hxD

end LDatum

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f
