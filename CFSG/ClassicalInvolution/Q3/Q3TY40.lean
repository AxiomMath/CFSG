module

public import CFSG.ClassicalInvolution.Q3.Q3TY39
public import CFSG.ClassicalInvolution.Q3.Q3TY17
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.RouteD.TwinSmallTwin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.RouteD.TwinSmall (eigen_contradiction commutes_of_span_orth)
open scoped MatrixGroups commutatorElement

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

noncomputable abbrev QM3 (m : ℕ) : QuadraticForm (GaloisField 3 1) (Vm m (GaloisField 3 1)) :=
  quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2

noncomputable abbrev SpinM3 (m : ℕ) : Type := spinGroup (QM3 m)

theorem commute_of_pow3_of_map_commute3 {S X : Type} [Group S] [Group X] (ψ : S →* X)
    (hker : ψ.ker ≤ Subgroup.center S) (hcop : ∀ n ∈ ψ.ker, ¬ 3 ∣ orderOf n) {R : Subgroup S}
    (hR : Pow3 R) {a : S} (h : ∀ r ∈ R, Commute (ψ a) (ψ r)) : ∀ r ∈ R, Commute a r := by
  intro r hr
  exact (commutes_of_map_commute_exponent3 ψ hker hcop (A := Subgroup.zpowers a) (L := R) hR
    (fun a' ha' l hl => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
      rw [map_zpow]
      exact ((h l hl).zpow_left k).eq) a (Subgroup.mem_zpowers a) r hr)


section Local

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem centralizes_iff_locElt3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x) {u : G} (hu : u ∈ locLayer Ω x)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) {S : Subgroup (locQuot Ω x)}
    (hLS : locImg Ω x L = S) :
    L ≤ Subgroup.centralizer ({u} : Set G) ↔ ∀ s ∈ S, Commute (locElt Ω x u hu) s := by
  constructor
  · intro h s hs
    rw [← hLS] at hs
    obtain ⟨b, hb, rfl⟩ := hs
    have hbL : (b : G) ∈ L := Subgroup.mem_subgroupOf.mp hb
    have hc : u * (b : G) = (b : G) * u :=
      (Subgroup.mem_centralizer_singleton_iff.mp (h hbL)).symm
    show locMk Ω x ⟨u, hu⟩ * locMk Ω x b = locMk Ω x b * locMk Ω x ⟨u, hu⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  · intro h
    obtain ⟨z₀, hz₀⟩ := hΩ.classical L hL.1
    obtain ⟨eL⟩ := hz₀.nonempty_equiv_sl2 (hex L hL.1)
    set Y := locLayer Ω x
    set O := classicalInvolutionOddCore ↥Y
    have hle : L ≤ Y := le_centralizingLayer hL
    have hpow : Pow3 (L.subgroupOf Y) := by
      intro l hl
      exact pow_three_mem_commutator_of_equiv (K := ZMod 3) (by simp)
        ((Subgroup.subgroupOfEquivOfLe hle).trans eL) l hl
    have hcop : ∀ y ∈ O, ¬ 3 ∣ orderOf y := by
      intro y hy h3
      have h1 : orderOf (⟨y, hy⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact hO3 (h3.trans h1)
    have hker : (locMk Ω x).ker ≤ Subgroup.center ↥Y := by
      rw [QuotientGroup.ker_mk']
      exact hP1
    have key := commute_of_pow3_of_map_commute3 (locMk Ω x) hker
      (fun y hy => hcop y (by rwa [QuotientGroup.ker_mk'] at hy)) (a := ⟨u, hu⟩) hpow
      (fun r hr => h _ (by rw [← hLS]; exact ⟨r, hr, rfl⟩))
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := key ⟨n, le_centralizingLayer hL hn⟩ (Subgroup.mem_subgroupOf.mpr hn)
    exact (congrArg Subtype.val this.eq).symm

theorem commute_w_of_model3 {tY : StatedLieTag} {nY : ℕ} {N : Subgroup G} {x : G}
    (cx : Q3TC.TCtx3 tY nY Ω N x) {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ) {w w' : G}
    (hw : IsClassicalMember3 L w) (hw' : IsClassicalMember3 L' w')
    (hc : ∀ r r', InvOf R r → InvOf R' r' → r * r' = r' * r) : Commute w w' := by
  obtain ⟨r, hr, hψr⟩ := exists_involution_of_fund3 cx hL hR hLR hw
  obtain ⟨r', hr', hψr'⟩ := exists_involution_of_fund3 cx hL' hR' hLR' hw'
  have hwx : w ∈ locLayer Ω x := le_centralizingLayer hL hw.mem
  have hwx' : w' ∈ locLayer Ω x := le_centralizingLayer hL' hw'.mem
  have hcomm : locElt Ω x w hwx * locElt Ω x w' hwx' = locElt Ω x w' hwx' * locElt Ω x w hwx := by
    rw [← hψr, ← hψr', ← map_mul, ← map_mul, hc r r' hr hr']
  have hw2 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw.orderOf_eq_two, pow_two] at this
  have hw2' : w' * w' = 1 := by
    have := pow_orderOf_eq_one w'
    rwa [hw'.orderOf_eq_two, pow_two] at this
  have := commute_of_involutions_of_mk (Y := ↥(locLayer Ω x)) cx.hP1
    (a := ⟨w, hwx⟩) (b := ⟨w', hwx'⟩) (Subtype.ext hw2) (Subtype.ext hw2') hcomm
  exact congrArg Subtype.val this.eq

end Local

section Spin

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {KY : Type} [Group KY] {𝓕 : Set (Subgroup KY)}
  {Z' : Subgroup (V ≃ₗ[F] V)} {π : KY →* (V ≃ₗ[F] V)}

theorem map_invOf_eq3 (hodd : Odd (Nat.card F)) (cq : CentralQuot3 π 𝓕 (fundSet Q) Z')
    {R : Subgroup KY} (hR : R ∈ 𝓕) {i : V ≃ₗ[F] V} (hi : IsFundamental Q (R.map π) i) {r : KY}
    (hr : InvOf R r) : π r = i := by
  obtain ⟨hrR, hr2⟩ := hr
  refine hi.eq_of_orderOf_eq_two hodd ⟨r, hrR, rfl⟩ ?_
  have h1 : orderOf (π r) ∣ 2 := by
    rw [← hr2]
    exact orderOf_map_dvd π r
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exfalso
    have h3 : π r = 1 := orderOf_eq_one_iff.mp h
    have := cq.inj R hR r hrR h3
    rw [this, orderOf_one] at hr2
    exact absurd hr2 (by simp)
  · exact h

theorem invs_commute_of_normalizes3 (hodd : Odd (Nat.card F))
    (cq : CentralQuot3 π 𝓕 (fundSet Q) Z') {R R' : Subgroup KY} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕)
    {i i' : V ≃ₗ[F] V} (hi : IsFundamental Q (R.map π) i) (hi' : IsFundamental Q (R'.map π) i')
    (hN : i' ∈ Subgroup.normalizer ((R.map π : Subgroup (V ≃ₗ[F] V)) : Set (V ≃ₗ[F] V))) :
    ∀ r r', InvOf R r → InvOf R' r' → r * r' = r' * r := by
  intro r r' hr hr'
  have hπr : π r = i := map_invOf_eq3 hodd cq hR hi hr
  have hπr' : π r' = i' := map_invOf_eq3 hodd cq hR' hi' hr'
  obtain ⟨hrR, hr2⟩ := hr
  have hrr : r * r = 1 := by
    have := pow_orderOf_eq_one r
    rwa [hr2, pow_two] at this
  have hnorm : ∀ y ∈ R, r' * y * r'⁻¹ ∈ R := by
    have hst := mem_of_stable3 π cq.ker_le cq.cop (MulAut.conj r') (MulAut.conj i')
      (fun y => by simp [hπr']) (cq.pow3 R hR) (fun y hy => by
        have h1 : (MulAut.conj i') (π y) ∈ R.map π := by
          have := (Subgroup.mem_normalizer_iff.mp hN (π y)).mp ⟨y, hy, rfl⟩
          simpa [MulAut.conj_apply] using this
        exact h1)
    intro y hy
    exact hst y hy
  have h1 : r' * r * r'⁻¹ ∈ R := hnorm r hrR
  have hsq : (r' * r * r'⁻¹) * (r' * r * r'⁻¹) = 1 := by
    calc (r' * r * r'⁻¹) * (r' * r * r'⁻¹) = r' * (r * r) * r'⁻¹ := by group
      _ = 1 := by rw [hrr]; group
  have hne : r' * r * r'⁻¹ ≠ 1 := by
    intro h
    have : r = 1 := by
      have h' : r = r'⁻¹ * (r' * r * r'⁻¹) * r' := by group
      rw [h', h]
      group
    rw [this, orderOf_one] at hr2
    exact absurd hr2 (by simp)
  have hord : orderOf (r' * r * r'⁻¹) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
  have h2 : π (r' * r * r'⁻¹) = π r := by
    rw [hπr]
    exact hi.eq_of_orderOf_eq_two hodd ⟨_, h1, rfl⟩ (by
      have h4 : orderOf (π (r' * r * r'⁻¹)) ∣ 2 := by
        rw [← hord]
        exact orderOf_map_dvd π _
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h | h
      · exfalso
        have h3 : π (r' * r * r'⁻¹) = 1 := orderOf_eq_one_iff.mp h
        have := cq.inj R hR _ h1 h3
        exact hne this
      · exact h)
  have h3 : r' * r * r'⁻¹ = r := by
    have := cq.inj R hR ((r' * r * r'⁻¹) * r⁻¹) (R.mul_mem h1 (R.inv_mem hrR)) (by
      rw [map_mul, map_inv, h2, mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  calc r * r' = (r' * r * r'⁻¹) * r' := by rw [h3]
    _ = r' * r := by group

end Spin

section Layer

variable {m : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {N : Subgroup G} {x : G}

theorem ctx_centralQuot3 (hm : 4 ≤ m) :
    CentralQuot3 (spinAction (QM3 m)) (fundamentalSubgroups .POmegaMinus (minusDatum m
      (minusCoeffs_irr 3 1))) (fundSet (QM3 m))
      (scalars (GaloisField 3 1) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField 3 1)) :=
  centralQuot3_minus ⟨Nat.prime_three, le_rfl, hm⟩

theorem locElt_mul_psi3 (cx : Q3TC.TCtx3 .POmegaMinus m Ω N x) {A B : Subgroup G}
    (hA : A ∈ centralizingMembers Ω {x}) (hB : B ∈ centralizingMembers Ω {x})
    {RA RB : Subgroup (SpinM3 m)}
    (hRA : RA ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)))
    (hRB : RB ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)))
    (hAR : locImg Ω x A = RA.map cx.d.ψ) (hBR : locImg Ω x B = RB.map cx.d.ψ) {wA wB : G}
    (hwA : IsClassicalMember3 A wA) (hwB : IsClassicalMember3 B wB) :
    ∃ rA rB : SpinM3 m, InvOf RA rA ∧ InvOf RB rB ∧
      locElt Ω x (wA * wB) ((locLayer Ω x).mul_mem (le_centralizingLayer hA hwA.mem)
        (le_centralizingLayer hB hwB.mem)) = cx.d.ψ (rA * rB) := by
  obtain ⟨rA, hrA, hψA⟩ : ∃ r : SpinM3 m, InvOf RA r ∧
      cx.d.ψ r = locElt Ω x wA (le_centralizingLayer hA hwA.mem) :=
    exists_involution_of_fund3 cx hA hRA hAR hwA
  obtain ⟨rB, hrB, hψB⟩ : ∃ r : SpinM3 m, InvOf RB r ∧
      cx.d.ψ r = locElt Ω x wB (le_centralizingLayer hB hwB.mem) :=
    exists_involution_of_fund3 cx hB hRB hBR hwB
  refine ⟨rA, rB, hrA, hrB, ?_⟩
  calc locElt Ω x (wA * wB) _ = locElt Ω x wA (le_centralizingLayer hA hwA.mem) *
        locElt Ω x wB (le_centralizingLayer hB hwB.mem) := (locElt_mul _ _).symm
    _ = cx.d.ψ rA * cx.d.ψ rB := by rw [hψA, hψB]
    _ = cx.d.ψ (rA * rB) := (map_mul cx.d.ψ rA rB).symm

theorem centralizes_prod_of_same3 (cx : Q3TC.TCtx3 .POmegaMinus m Ω N x) (hm : 4 ≤ m)
    {A B : Subgroup G} (hA : A ∈ centralizingMembers Ω {x}) (hB : B ∈ centralizingMembers Ω {x})
    {RA RB : Subgroup (SpinM3 m)}
    (hRA : RA ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)))
    (hRB : RB ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)))
    (hAR : locImg Ω x A = RA.map cx.d.ψ) (hBR : locImg Ω x B = RB.map cx.d.ψ) {wA wB : G}
    (hwA : IsClassicalMember3 A wA) (hwB : IsClassicalMember3 B wB)
    {iA : (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField 3 1)}
    (hiA : IsFundamental (QM3 m) (RA.map (spinAction (QM3 m))) iA)
    (hiB : IsFundamental (QM3 m) (RB.map (spinAction (QM3 m))) iA)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) {R : Subgroup (SpinM3 m)}
    (hLR : locImg Ω x L = R.map cx.d.ψ) :
    L ≤ Subgroup.centralizer ({wA * wB} : Set G) := by
  have cq := ctx_centralQuot3 hm
  obtain ⟨rA, rB, hrA, hrB, hloc⟩ := locElt_mul_psi3 cx hA hB hRA hRB hAR hBR hwA hwB
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hπA := map_invOf_eq3 hodd cq hRA hiA hrA
  have hπB := map_invOf_eq3 hodd cq hRB hiB hrB
  have hπ : spinAction (QM3 m) (rA * rB) = 1 := by
    rw [map_mul, hπA, hπB]
    exact hiA.mul_self
  have hcen := cq.ker_le (MonoidHom.mem_ker.mpr hπ)
  rw [centralizes_iff_locElt3 cx.hΩ cx.hex cx.hP1 cx.hO3 ((locLayer Ω x).mul_mem
    (le_centralizingLayer hA hwA.mem) (le_centralizingLayer hB hwB.mem)) hL hLR]
  intro s hs
  obtain ⟨r, -, rfl⟩ : ∃ r : SpinM3 m, r ∈ R ∧ cx.d.ψ r = s := hs
  rw [hloc]
  have := Subgroup.mem_center_iff.mp hcen r
  calc cx.d.ψ (rA * rB) * cx.d.ψ r = cx.d.ψ ((rA * rB) * r) := (map_mul cx.d.ψ _ _).symm
    _ = cx.d.ψ (r * (rA * rB)) := congrArg cx.d.ψ this.symm
    _ = cx.d.ψ r * cx.d.ψ (rA * rB) := map_mul cx.d.ψ _ _

theorem not_centralizes_prod_mixed3 (cx : Q3TC.TCtx3 .POmegaMinus m Ω N x) (hm : 4 ≤ m)
    {A B L : Subgroup G} (hA : A ∈ centralizingMembers Ω {x}) (hB : B ∈ centralizingMembers Ω {x})
    (hL : L ∈ centralizingMembers Ω {x}) {RA RB R : Subgroup (SpinM3 m)}
    (hRA : RA ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)))
    (hRB : RB ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)))
    (hR : R ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)))
    (hAR : locImg Ω x A = RA.map cx.d.ψ) (hBR : locImg Ω x B = RB.map cx.d.ψ)
    (hLR : locImg Ω x L = R.map cx.d.ψ) {wA wB : G} (hwA : IsClassicalMember3 A wA)
    (hwB : IsClassicalMember3 B wB) (F₁ F₂ F : OPFrame (QM3 m))
    (hF₁ : RA.map (spinAction (QM3 m)) = F₁.La.range)
    (hF₂ : RB.map (spinAction (QM3 m)) = F₂.La.range)
    (hF : R.map (spinAction (QM3 m)) = F.La.range)
    (horth : ∀ x ∈ F₁.span, ∀ y ∈ F₂.span, polar (QM3 m) x y = 0)
    {e a : Vm m (GaloisField 3 1)} (he : e ∈ F.span) (he0 : e ≠ 0) (heA : e ∈ F₁.span)
    (heB : ∀ y ∈ F₂.span, polar (QM3 m) e y = 0) (ha : a ∈ F.span) (ha0 : a ≠ 0)
    (haA : ∀ y ∈ F₁.span, polar (QM3 m) a y = 0)
    (haB : ∀ y ∈ F₂.span, polar (QM3 m) a y = 0) :
    ¬ L ≤ Subgroup.centralizer ({wA * wB} : Set G) := by
  intro hcent
  have cq := ctx_centralQuot3 hm
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have h2 : (2 : GaloisField 3 1) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨rA, rB, hrA, hrB, hloc⟩ := locElt_mul_psi3 cx hA hB hRA hRB hAR hBR hwA hwB
  have hiA : IsFundamental (QM3 m) (RA.map (spinAction (QM3 m))) (F₁.La (-1)) := by
    rw [hF₁]
    exact IsFundamental.of_frame F₁
  have hiB : IsFundamental (QM3 m) (RB.map (spinAction (QM3 m))) (F₂.La (-1)) := by
    rw [hF₂]
    exact IsFundamental.of_frame F₂
  have hiL : IsFundamental (QM3 m) (R.map (spinAction (QM3 m))) (F.La (-1)) := by
    rw [hF]
    exact IsFundamental.of_frame F
  have hπA := map_invOf_eq3 hodd cq hRA hiA hrA
  have hπB := map_invOf_eq3 hodd cq hRB hiB hrB
  have h1 := (centralizes_iff_locElt3 cx.hΩ cx.hex cx.hP1 cx.hO3 ((locLayer Ω x).mul_mem
    (le_centralizingLayer hA hwA.mem) (le_centralizingLayer hB hwB.mem)) hL hLR).mp hcent
  have h2' : ∀ r : SpinM3 m, r ∈ R → Commute (cx.d.ψ (rA * rB)) (cx.d.ψ r) := fun r hr => by
    have := h1 (cx.d.ψ r) ⟨r, hr, rfl⟩
    rwa [hloc] at this
  have h3 := commute_of_pow3_of_map_commute3 cx.d.ψ cx.d.ker_le cx.ker_cop (cq.pow3 R hR) h2'
  set g : Vm m (GaloisField 3 1) ≃ₗ[GaloisField 3 1] Vm m (GaloisField 3 1) :=
    F₁.La (-1) * F₂.La (-1) with hg
  have hπ : spinAction (QM3 m) (rA * rB) = g := by
    rw [map_mul, hπA, hπB]
  have hcommg : ∀ l ∈ F.La.range, g * l = l * g := by
    intro l hl
    rw [← hF] at hl
    obtain ⟨r, hr, rfl⟩ := hl
    have h3' : (rA * rB) * r = r * (rA * rB) := (h3 r hr).eq
    rw [← hπ, ← map_mul, ← map_mul, h3']
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (QM3 m) :=
    Subgroup.mul_mem _ (F₁.La_mem_orthogonalGroup (-1)) (F₂.La_mem_orthogonalGroup (-1))
  have hc12 : F₁.La (-1) * F₂.La (-1) = F₂.La (-1) * F₁.La (-1) :=
    commutes_of_span_orth F₁ F₂ horth (-1) (-1)
  have hg2 : g * g = 1 := by
    calc g * g = F₁.La (-1) * (F₂.La (-1) * F₁.La (-1)) * F₂.La (-1) := by rw [hg]; group
      _ = F₁.La (-1) * (F₁.La (-1) * F₂.La (-1)) * F₂.La (-1) := by rw [← hc12]
      _ = (F₁.La (-1) * F₁.La (-1)) * (F₂.La (-1) * F₂.La (-1)) := by group
      _ = 1 := by rw [F₁.La_neg_one_mul_self, F₂.La_neg_one_mul_self, one_mul]
  have hperpB : ∀ v, (∀ y ∈ F₂.span, polar (QM3 m) v y = 0) → F₂.La (-1) v = v := fun v hv =>
    (Frame.mem_perp_iff_fix F₂ h2).mp ((Frame.mem_perp_iff_forall_incl F₂).mpr fun Y =>
      hv _ ⟨Y, rfl⟩)
  have hperpA : ∀ v, (∀ y ∈ F₁.span, polar (QM3 m) v y = 0) → F₁.La (-1) v = v := fun v hv =>
    (Frame.mem_perp_iff_fix F₁ h2).mp ((Frame.mem_perp_iff_forall_incl F₁).mpr fun Y =>
      hv _ ⟨Y, rfl⟩)
  have hge : g e = -e := by
    rw [hg, LinearEquiv.mul_apply, hperpB e heB]
    exact (Frame.mem_span_iff_inv F₁ h2).mp heA
  have hga : g a = a := by
    rw [hg, LinearEquiv.mul_apply, hperpB a haB, hperpA a haA]
  have hnegF : negSpace (F.La (-1)) = F.span := negSpace_La_neg_one h2 F
  exact eigen_contradiction h2 hiL hgO hg2 (fun l hl => hcommg l (by rw [← hF]; exact hl))
    (hnegF ▸ he) (hnegF ▸ ha) he0 ha0 hge hga

theorem false_of_twins_other_layer3 {K M : Subgroup G} {z xM : G}
    (c : Q3TC.TCtx3 .POmegaMinus m Ω K z) (cM : Q3TC.TCtx3 .POmegaMinus m Ω M xM) (hm : 7 ≤ m)
    (hKxM : K ∈ centralizingMembers Ω {xM}) {A B : Subgroup G}
    (hAz : A ∈ centralizingMembers Ω {z}) (hBz : B ∈ centralizingMembers Ω {z})
    (hAM : A ∈ centralizingMembers Ω {xM}) (hBM : B ∈ centralizingMembers Ω {xM})
    {wA wB : G} (hwA : IsClassicalMember3 A wA) (hwB : IsClassicalMember3 B wB)
    {RAz RBz : Subgroup (SpinM3 m)}
    (hRAz : RAz ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)))
    (hRBz : RBz ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)))
    (hAimgz : locImg Ω z A = RAz.map c.d.ψ) (hBimgz : locImg Ω z B = RBz.map c.d.ψ)
    (hsame : ∀ i j, IsFundamental (QM3 m) (RAz.map (spinAction (QM3 m))) i →
      IsFundamental (QM3 m) (RBz.map (spinAction (QM3 m))) j → i = j)
    {RKM RAM RBM : Subgroup (SpinM3 m)}
    (hRAM : RAM ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)))
    (hRBM : RBM ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)))
    (hKimgM : locImg Ω xM K = RKM.map cM.d.ψ) (hAimgM : locImg Ω xM A = RAM.map cM.d.ψ)
    (hBimgM : locImg Ω xM B = RBM.map cM.d.ψ) (F₀ F₁ F₂ : OPFrame (QM3 m))
    (hF₀ : RKM.map (spinAction (QM3 m)) = F₀.La.range)
    (hF₁ : RAM.map (spinAction (QM3 m)) = F₁.La.range)
    (hF₂ : RBM.map (spinAction (QM3 m)) = F₂.La.range)
    (h01 : ∀ x ∈ F₀.span, ∀ y ∈ F₁.span, polar (QM3 m) x y = 0)
    (h02 : ∀ x ∈ F₀.span, ∀ y ∈ F₂.span, polar (QM3 m) x y = 0)
    (h12 : ∀ x ∈ F₁.span, ∀ y ∈ F₂.span, polar (QM3 m) x y = 0) : False := by
  have hm4 : 4 ≤ m := by omega
  have cq := ctx_centralQuot3 hm4
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have h2 : (2 : GaloisField 3 1) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hQ : (polarBilin (QM3 m)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite _ (GaloisField 3 1) (minusCoeffs_irr 3 1)
  have hdim : 13 ≤ Module.finrank (GaloisField 3 1) (Vm m (GaloisField 3 1)) := by
    rw [finrank_minus 3 1 m (by omega)]
    omega
  obtain ⟨iA, hiA⟩ := cq.map_mem _ hRAz
  obtain ⟨iB, hiB⟩ := cq.map_mem _ hRBz
  have hAB : iA = iB := hsame iA iB hiA hiB
  subst hAB
  obtain ⟨F, hFK, ⟨e, heF, he0, heA, heB⟩, ⟨a, haF, ha0, haA, haB⟩, ⟨e', he'F, f', hf'A, hpol⟩⟩ :=
    exists_mixed_frame h2 hQ F₀ F₁ F₂ h01 h02 h12 hdim
  have hL : F.La.range ∈ fundSet (QM3 m) := ⟨F.La (-1), IsFundamental.of_frame F⟩
  obtain ⟨R', hR', hR'F⟩ := cq.surj _ hL
  obtain ⟨Nn, hNnM, hNnne, -, hNnimg⟩ := cM.exists_member_of_fund hR'
  have hRK : Commutes R' RKM := by
    refine (cq.commutes_iff hR').mp ?_
    rw [hR'F, hF₀]
    rintro _ ⟨A', rfl⟩ _ ⟨B', rfl⟩
    exact commutes_of_span_orth F F₀ hFK A' B'
  have hNnK : Commutes Nn K :=
    (cM.commutes_iff_fund hNnM hKxM hR' hNnimg hKimgM).mpr hRK
  have hNnz : Nn ∈ centralizingMembers Ω {z} := by
    refine ⟨hNnM.1, fun n hn => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hNnK n hn z c.hz.mem
  have hspan : ¬ F₁.span = F.span := by
    intro h
    have : a ∈ F₁.span := h ▸ haF
    exact ha0 (F₁.polarNondegOn_span a this haA)
  have hFiso : IsFundamental (QM3 m) F.La.range (F.La (-1)) := IsFundamental.of_frame F
  have hF₁iso : IsFundamental (QM3 m) F₁.La.range (F₁.La (-1)) := IsFundamental.of_frame F₁
  have hnegF : negSpace (F.La (-1)) = F.span := negSpace_La_neg_one h2 F
  have hnegF₁ : negSpace (F₁.La (-1)) = F₁.span := negSpace_La_neg_one h2 F₁
  have hnc : ¬ Commutes Nn A := by
    intro hc
    have h1 : Commutes R' RAM := (cM.commutes_iff_fund hNnM hAM hR' hNnimg hAimgM).mp hc
    have h2' : Commutes F.La.range F₁.La.range := by
      rw [← hR'F, ← hF₁]
      exact (cq.commutes_iff hR').mpr h1
    rcases orth_or_twin hodd hFiso hF₁iso h2' with h | h
    · have := h e' (hnegF ▸ he'F) f' (hnegF₁ ▸ hf'A)
      rw [hpol] at this
      exact one_ne_zero this
    · apply hspan
      rw [← hnegF₁, ← hnegF, h]
  have hne : Nn ≠ A := by
    rintro rfl
    have h1 : R'.map cM.d.ψ = RAM.map cM.d.ψ := hNnimg.symm.trans hAimgM
    have h2' : R' = RAM := eq_of_map_eq_of_pow3 cM.d.ψ cM.d.ker_le cM.ker_cop (cq.pow3 R' hR')
      (cq.pow3 RAM hRAM) h1
    have h3 : F.La.range = F₁.La.range := by rw [← hR'F, ← hF₁, h2']
    have h4 : F.La (-1) = F₁.La (-1) :=
      IsFundamental.involution_unique hodd hFiso (h3 ▸ hF₁iso)
    exact hspan (by rw [← hnegF₁, ← hnegF, h4])
  have hlayer : IsLayerMember3 c Nn := IsLayerMember3.of_not_commutes c hNnz hAz hne hnc
  obtain ⟨Rz, hRz, hNnimgz⟩ := hlayer.exists_fund
  have hcent := centralizes_prod_of_same3 c hm4 hAz hBz hRAz hRBz hAimgz hBimgz hwA hwB hiA hiB
    hNnz hNnimgz
  exact not_centralizes_prod_mixed3 cM hm4 hAM hBM hNnM hRAM hRBM hR' hAimgM hBimgM hNnimg hwA hwB
    F₁ F₂ F hF₁ hF₂ hR'F h12 heF he0 heA heB haF ha0 haA haB hcent

end Layer

end CFSG.ClassicalInvolution.Q3.Q3TY
