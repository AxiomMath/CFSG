module

public import CFSG.ClassicalInvolution.Q3.Q3E8BCent
public import CFSG.ClassicalInvolution.Q3.Q3EPQuot
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


structure XCtx3 (t : StatedLieTag) (n : ℕ) {G : Type} [Group G] (Ω : Set (Subgroup G))
    (x : G) where
  hΩ : InClass3 Ω
  hex : ExactMembers3 Ω
  hP1 : LocalOddCentral Ω {x}
  hO3 : LocalOddThreeFree3 Ω x
  hpc : PowCop3 (CompData.model t n)
  ψ : (modelUniv t n 3 1 Nat.prime_three).K →* locQuot Ω x
  ker_le : ψ.ker ≤ Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K
  mem_fam : ∀ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D,
    R.map ψ ∈ locFamily Ω x
  fam_range : ∀ N ∈ centralizingMembers Ω {x}, locImg Ω x N ≤ ψ.range →
    ∃ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D,
      locImg Ω x N = R.map ψ

namespace XCtx3

variable {t : StatedLieTag} {n : ℕ} {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}
  (X : XCtx3 t n Ω x)

include X

theorem ker_cop : ∀ w ∈ X.ψ.ker, ¬ 3 ∣ orderOf w := fun w hw => X.hpc.cop w (X.ker_le hw)

theorem exists_member_of_fund {R : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D) :
    ∃ N ∈ centralizingMembers Ω {x}, locImg Ω x N = R.map X.ψ :=
  mem_locFamily_iff.mp (X.mem_fam R hR)

theorem eq_of_locImg_eq [Finite G] {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x}) (h : locImg Ω x L = locImg Ω x L') : L = L' :=
  locImg_injOn3 X.hΩ X.hex X.hP1 X.hO3 hL hL' h

theorem eq_of_map_eq {R R' : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (h : R.map X.ψ = R'.map X.ψ) : R = R' :=
  eq_of_map_eq_of_pow3 X.ψ X.ker_le X.ker_cop (X.hpc.pow3 R hR) (X.hpc.pow3 R' hR') h

theorem commutes_of_commutes_map {R R' : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (h : Commutes (R.map X.ψ) (R'.map X.ψ)) : Commutes R R' := by
  intro a ha b hb
  exact (commutes_of_map_commute_exponent3 X.ψ (hker := X.ker_le) X.ker_cop
    (A := R') (L := R) (X.hpc.pow3 R hR)
    (fun a' ha' l hl => (h _ ⟨l, hl, rfl⟩ _ ⟨a', ha', rfl⟩).symm) b hb a ha).symm

theorem commutes_iff_fund [Finite G] {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map X.ψ) (hLR' : locImg Ω x L' = R'.map X.ψ) :
    Commutes L L' ↔ Commutes R R' := by
  constructor
  · intro h
    have h1 := commutes_locImg_of_commutes (x := x) (Ω := Ω) h
    rw [hLR, hLR'] at h1
    exact X.commutes_of_commutes_map hR h1
  · intro h
    refine commutes_of_commutes_locImg3 X.hΩ X.hex X.hP1 X.hO3 hL hL' ?_
    rw [hLR, hLR']
    exact commutes_map_of_commutes _ h

theorem stdPair_of_fund [Finite G] {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' W : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hW : LinearBlockStandardPair (GaloisField 3 1) W R R')
    (hLR : locImg Ω x L = R.map X.ψ) (hLR' : locImg Ω x L' = R'.map X.ψ) :
    ∃ W' : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W' L L' := by
  have := linearBlockStandardPair_map_central hW X.ψ X.ker_le
  rw [← hLR, ← hLR'] at this
  exact linearBlockStandardPair_of_locImg3' X.hΩ X.hex X.hP1 X.hO3 hL hL' this

theorem stdPair_model [Finite G] [Finite (modelUniv t n 3 1 Nat.prime_three).K]
    {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map X.ψ) (hLR' : locImg Ω x L' = R'.map X.ψ)
    (h : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W L L') :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R' := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members X.hP1 hL hL' hW
  rw [hLR, hLR'] at hW'
  exact exists_lin_of_map3 (not_three_dvd_card_center X.hpc.cop) X.ψ X.ker_le
    (X.hpc.pow3 R hR) (X.hpc.pow3 R' hR') ⟨W', hW'⟩

theorem centralizes_iff [Finite G] {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {x})
    {R : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hNR : locImg Ω x N = R.map X.ψ) {y : G} (hy : y ∈ locLayer Ω x)
    {r : (modelUniv t n 3 1 Nat.prime_three).K} (hr : X.ψ r = locElt Ω x y hy) :
    N ≤ Subgroup.centralizer ({y} : Set G) ↔ R ≤ Subgroup.centralizer ({r} : Set _) := by
  rw [le_centralizer_iff_locImg3 X.hΩ X.hex X.hP1 X.hO3 hN ⟨y, hy⟩,
    le_centralizer_iff_map3 X.ψ X.ker_le X.ker_cop (X.hpc.pow3 R hR) r, hNR, hr]
  exact Iff.rfl

theorem normalizes_of_conjSub {L : Subgroup G}
    {R : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map X.ψ) {w : G} (hwx : w ∈ locLayer Ω x)
    {r : (modelUniv t n 3 1 Nat.prime_three).K} (hr : X.ψ r = locElt Ω x w hwx)
    (hN : conjSub w L = L) : ∀ y ∈ R, r * y * r⁻¹ ∈ R := by
  have hle : (conjSub r R).map X.ψ ≤ R.map X.ψ := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have h1 : X.ψ y ∈ locImg Ω x L := by
      rw [hLR]
      exact ⟨y, hy, rfl⟩
    have h2 : X.ψ (r * y * r⁻¹) ∈ locImg Ω x (conjSub w L) := by
      have := Gaps.locImg_conjSub_layer (Ω := Ω) (x := x) L ⟨w, hwx⟩
      rw [this]
      refine ⟨X.ψ y, h1, ?_⟩
      simp only [map_mul, map_inv, hr]
      rfl
    rwa [hN, hLR] at h2
  have hsub := le_of_map_le_of_pow3 X.ψ X.ker_le X.ker_cop (X.hpc.pow3 R hR |>.conjSub r) hle
  exact fun y hy => hsub (conj_mem_conjSub hy)

section Involutions

variable (hcf : ∀ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D, ∀ r ∈ R,
  r ∈ Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K → r = 1)

include hcf

theorem exists_involution_of_fund [Finite G] {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x})
    {R : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map X.ψ) {w : G} (hw : IsClassicalMember3 L w) :
    ∃ r, Gaps.InvOf R r ∧ X.ψ r = locElt Ω x w (le_centralizingLayer hL hw.mem) := by
  have hwx : w ∈ locLayer Ω x := le_centralizingLayer hL hw.mem
  have hmem : locElt Ω x w hwx ∈ R.map X.ψ :=
    hLR ▸ locElt_mem_locImg (le_centralizingLayer hL) hw.mem
  obtain ⟨r, hrR, hr⟩ := hmem
  have h2 : orderOf (X.ψ r) = 2 := by
    rw [hr]
    exact orderOf_locElt hwx hw.orderOf_eq_two
  have hsq : r * r = 1 := by
    have h1 : X.ψ (r * r) = 1 := by
      rw [map_mul]
      have := pow_orderOf_eq_one (X.ψ r)
      rwa [h2, pow_two] at this
    exact hcf R hR (r * r) (R.mul_mem hrR hrR) (X.ker_le h1)
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, map_one] at h2
    simp at h2
  exact ⟨r, ⟨hrR, orderOf_eq_prime (by rw [pow_two]; exact hsq) hr1⟩, hr⟩

theorem modelInvComm_of_commute [Finite G] {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map X.ψ) (hLR' : locImg Ω x L' = R'.map X.ψ) {w w' : G}
    (hw : IsClassicalMember3 L w) (hw' : IsClassicalMember3 L' w') (hc : Commute w w') :
    ∃ r r', Gaps.InvOf R r ∧ Gaps.InvOf R' r' ∧
      ⁅r, r'⁆ ∈ Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K ∧
      X.ψ r = locElt Ω x w (le_centralizingLayer hL hw.mem) ∧
      X.ψ r' = locElt Ω x w' (le_centralizingLayer hL' hw'.mem) := by
  obtain ⟨r, hr, hψr⟩ := X.exists_involution_of_fund hcf hL hR hLR hw
  obtain ⟨r', hr', hψr'⟩ := X.exists_involution_of_fund hcf hL' hR' hLR' hw'
  refine ⟨r, r', hr, hr', X.ker_le ?_, hψr, hψr'⟩
  have hcomm : X.ψ r * X.ψ r' = X.ψ r' * X.ψ r := by
    rw [hψr, hψr', locElt_mul, locElt_mul]
    congr 1
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

theorem modelAdj_of_adj [Finite G] {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map X.ψ) (hLR' : locImg Ω x L' = R'.map X.ψ) {w w' : G}
    (hw : IsClassicalMember3 L w) (hw' : IsClassicalMember3 L' w') (hne : L ≠ L')
    (hnc : ¬ Commutes L L') (hc : Commute w w') (hN : conjSub w' L = L) :
    Gaps.ModelAdj (Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K) R R' := by
  obtain ⟨r, r', hr, hr', hcen, hψr, hψr'⟩ :=
    X.modelInvComm_of_commute hcf hL hL' hR hR' hLR hLR' hw hw' hc
  refine ⟨fun h => hne (X.eq_of_locImg_eq hL hL' (by rw [hLR, hLR', h])), ?_, r, r', hr, hr',
    hcen, ?_⟩
  · intro h
    exact hnc ((X.commutes_iff_fund hL hL' hR hLR hLR').mpr h)
  · exact X.normalizes_of_conjSub hR hLR (le_centralizingLayer hL' hw'.mem) hψr' hN

end Involutions

end XCtx3

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_xctx3_of_comp [Finite G] {ι : Type} (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι} {t : StatedLieTag} {n : ℕ}
    (hk : D.kind i = CompData.model t n) (hft : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) :
    ∃ X : XCtx3 t n Ω x, X.ψ.range = (D.hom i).range := by
  obtain ⟨ψ, hker, hrange, hfund⟩ := exists_hom_of_comp3 D i hk
  have hsc := ModelFacts.fundamentalSingleClass t n 3 1 Nat.prime_three
    (modelFacts_isFundTag hft) hadm hG2 hD4
  obtain ⟨N₀, hN₀⟩ := exists_mem_compMembers3 (D := D) (Ω := Ω) (x := x) i
  have hΦ : ConjInvariant (locFamily Ω x) :=
    conjInvariant_oddQuotientFamily (inClass3_local hΩ {x} ⟨N₀, hN₀.1⟩).conjInvariant
  refine ⟨{
    hΩ := hΩ
    hex := hex
    hP1 := hP1
    hO3 := hO3
    hpc := powCop3_model hft hadm hG2 hD4
    ψ := ψ
    ker_le := hker
    mem_fam := ?_
    fam_range := ?_ }, hrange⟩
  · intro R hR
    obtain ⟨R', hR', hRR'⟩ := (hfund (R.map ψ)).mpr ⟨R, hR, rfl⟩
    rw [hRR']
    exact map_mem_of_comp3 D hΦ i hk hsc R' hR'
  · intro N hN hle
    obtain ⟨R, -, hRf, hNR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D (i := i)
      ⟨hN, by rw [← hrange]; exact hle⟩
    exact (hfund _).mp ⟨R, hRf, hNR⟩

end CFSG.ClassicalInvolution.Q3.Q3W
