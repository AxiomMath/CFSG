module

public import CFSG.ClassicalInvolution.Q3.Q3WAEDict


public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open CFSG.LieType.Universal
open scoped commutatorElement MatrixGroups

section Lift


variable {KY X : Type} [Group KY] [Group X]

theorem exists_lin_of_map3' [Finite KY] (hC : ¬ 3 ∣ Nat.card (Subgroup.center KY)) (ψ : KY →* X)
    (hker : ψ.ker ≤ Subgroup.center KY) {R₁ R₂ : Subgroup KY} (hR₁ : Pow3 R₁) (hR₂ : Pow3 R₂)
    (h : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₁.map ψ) (R₂.map ψ)) :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂ := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨θ, hrange, hθ, hU, hV⟩ := WeakCT.pair_normalize hW
  have hWsup := linear_eq_sup hW
  have hle : θ.range ≤ ψ.range := by
    rw [hrange, hWsup]
    exact sup_le (Subgroup.map_le_range ψ R₁) (Subgroup.map_le_range ψ R₂)
  let θ' : SL(3, GaloisField 3 1) →* ψ.range := θ.codRestrict ψ.range fun s => hle ⟨s, rfl⟩
  have hπ : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hπker : ψ.rangeRestrict.ker ≤ Subgroup.center KY := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hπC : ¬ 3 ∣ Nat.card ψ.rangeRestrict.ker := fun hd =>
    hC (hd.trans (Subgroup.card_dvd_of_le hπker))
  obtain ⟨α, hα, -⟩ := ModelFacts.LinearAut.sl_existsUnique_lift (n := 3) (K := GaloisField 3 1)
    (p := 3) (by norm_num) hπ hπker hπC θ'
  have hαψ : ∀ s, ψ (α s) = θ s := fun s => congrArg Subtype.val (DFunLike.congr_fun hα s)
  have hψα : ψ.comp α = θ := MonoidHom.ext hαψ
  have hcop : ∀ z ∈ ψ.ker, ¬ 3 ∣ orderOf z := fun z hz h3 =>
    hC (h3.trans (Subgroup.orderOf_dvd_natCard _ (hker hz)))
  have hp₁ : Pow3 ((B12 (GaloisField 3 1)).map α) := (pow3_range_sl2 card_gf3 _).map α
  have hp₂ : Pow3 ((B23 (GaloisField 3 1)).map α) := (pow3_range_sl2 card_gf3 _).map α
  have hR₁' : (B12 (GaloisField 3 1)).map α = R₁ :=
    eq_of_map_eq_of_pow3 ψ hker hcop hp₁ hR₁ (by rw [Subgroup.map_map, hψα, hU])
  have hR₂' : (B23 (GaloisField 3 1)).map α = R₂ :=
    eq_of_map_eq_of_pow3 ψ hker hcop hp₂ hR₂ (by rw [Subgroup.map_map, hψα, hV])
  have hid : (MulAut.conj (1 : SL(3, GaloisField 3 1))⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext
    simp
  refine ⟨α.range, α, 1, rfl, fun s hs => hθ ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.mem_ker, ← hαψ, hs, map_one]
  · rw [hid, Subgroup.map_id, hR₁']
  · rw [hid, Subgroup.map_id, hR₂']

theorem not_three_dvd_card_center' {G : Type} [Group G] [Finite G]
    (h : ∀ w ∈ Subgroup.center G, ¬ 3 ∣ orderOf w) : ¬ 3 ∣ Nat.card (Subgroup.center G) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) 3 h3
  apply h (x : G) x.2
  rw [Subgroup.orderOf_coe, hx]

end Lift


variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

structure Layer03 (Ω : Set (Subgroup G)) (x : G) (tY : StatedLieTag) (nY : ℕ) where
  φ : (modelUniv tY nY 3 1 Nat.prime_three).K →* locQuot Ω x
  ker_le : φ.ker ≤ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K
  mem : ∀ L ∈ centralizingMembers Ω {x}, ∃ R ∈ fundamentalSubgroups tY
    (modelUniv tY nY 3 1 Nat.prime_three).D, locImg Ω x L = R.map φ
  comp : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
    ∃ L ∈ centralizingMembers Ω {x}, locImg Ω x L = R.map φ

theorem Layer03.of_shape [Finite G] {tY : StatedLieTag} {nY : ℕ} (hΩ : InClass3 Ω)
    (hsc : FundamentalSingleClass tY (modelUniv tY nY 3 1 Nat.prime_three).D) {K : Subgroup G}
    (hK : K ∈ centralizingMembers Ω {x}) (h : LocalShapeC3 0 (CompData.model tY nY) Ω x) :
    Nonempty (Layer03 Ω x tY nY) := by
  obtain ⟨ι, hι, D, hcard, i₁, hk₁, -⟩ := h
  obtain ⟨ψ, hker, -, hfund⟩ := exists_hom_of_comp3 D i₁ hk₁
  have hΦ : ConjInvariant (locFamily Ω x) :=
    conjInvariant_oddQuotientFamily (inClass3_local hΩ {x} ⟨K, hK⟩).conjInvariant
  have hone : Nat.card ι = 1 := by simpa using hcard
  have hi : ∀ i : ι, i = i₁ := fun i =>
    (Nat.card_eq_one_iff_unique.mp hone).1.elim i i₁
  refine ⟨{ φ := ψ, ker_le := hker, mem := ?_, comp := ?_ }⟩
  · intro L hL
    have hmem : locImg Ω x L ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
    obtain ⟨i, R, hR, hRL⟩ := D.fundamental _ hmem
    obtain rfl := hi i
    obtain ⟨R', hR', hR'eq⟩ := (hfund _).mp ⟨R, hR, hRL⟩
    exact ⟨R', hR', hR'eq⟩
  · intro R hR
    obtain ⟨R'', hR'', hRR''⟩ := (hfund (R.map ψ)).mpr ⟨R, hR, rfl⟩
    have := map_mem_of_comp3 D hΦ i₁ hk₁ hsc R'' hR''
    rw [← hRR''] at this
    obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp this
    exact ⟨L, hL, hLR⟩

section Transfer

variable [Finite G] {tY : StatedLieTag} {nY : ℕ}

theorem Layer03.ker_cop (e : Layer03 Ω x tY nY) (hY : YData3 tY nY) :
    ∀ n ∈ e.φ.ker, ¬ 3 ∣ orderOf n := fun n hn => hY.cop n (e.ker_le hn)

theorem Layer03.commutes_of_commutes_map (e : Layer03 Ω x tY nY) (hY : YData3 tY nY)
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (h : Commutes (R.map e.φ) (R'.map e.φ)) : Commutes R R' := by
  intro a ha b hb
  exact (commutes_of_map_commute_exponent3 e.φ (hker := e.ker_le) (e.ker_cop hY)
    (A := R') (L := R) (hY.pow3 R hR)
    (fun a' ha' l hl => (h _ ⟨l, hl, rfl⟩ _ ⟨a', ha', rfl⟩).symm) b hb a ha).symm

theorem Layer03.commutes_iff (e : Layer03 Ω x tY nY) (hY : YData3 tY nY) (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map e.φ) (hLR' : locImg Ω x L' = R'.map e.φ) :
    Commutes L L' ↔ Commutes R R' := by
  constructor
  · intro h
    have h1 := commutes_locImg_of_commutes (x := x) (Ω := Ω) h
    rw [hLR, hLR'] at h1
    exact e.commutes_of_commutes_map hY hR h1
  · intro h
    refine commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hL hL' ?_
    rw [hLR, hLR']
    exact commutes_map_of_commutes _ h

theorem Layer03.exists_involution (e : Layer03 Ω x tY nY) (hY : YData3 tY nY) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x})
    {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map e.φ) {w : G} (hw : IsClassicalMember3 L w) :
    ∃ r, InvOf R r ∧ e.φ r = locElt Ω x w (le_centralizingLayer hL hw.mem) := by
  have hwx : w ∈ locLayer Ω x := le_centralizingLayer hL hw.mem
  have hmem : locElt Ω x w hwx ∈ R.map e.φ :=
    hLR ▸ locElt_mem_locImg (le_centralizingLayer hL) hw.mem
  obtain ⟨r, hrR, hr⟩ := hmem
  have h2 : orderOf (e.φ r) = 2 := by
    rw [hr]
    exact orderOf_locElt hwx hw.orderOf_eq_two
  have hsq : r * r = 1 := by
    have h1 : e.φ (r * r) = 1 := by
      rw [map_mul]
      have := pow_orderOf_eq_one (e.φ r)
      rwa [h2, pow_two] at this
    exact hY.central R hR (r * r) (R.mul_mem hrR hrR) (e.ker_le h1)
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, map_one] at h2
    simp at h2
  exact ⟨r, ⟨hrR, orderOf_eq_prime (by rw [pow_two]; exact hsq) hr1⟩, hr⟩

theorem Layer03.modelInvComm (e : Layer03 Ω x tY nY) (hY : YData3 tY nY) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map e.φ) (hLR' : locImg Ω x L' = R'.map e.φ) {w w' : G}
    (hw : IsClassicalMember3 L w) (hw' : IsClassicalMember3 L' w') (hc : Commute w w') :
    ∃ r r', InvOf R r ∧ InvOf R' r' ∧
      ⁅r, r'⁆ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K ∧
      e.φ r = locElt Ω x w (le_centralizingLayer hL hw.mem) ∧
      e.φ r' = locElt Ω x w' (le_centralizingLayer hL' hw'.mem) := by
  obtain ⟨r, hr, hψr⟩ := e.exists_involution hY hL hR hLR hw
  obtain ⟨r', hr', hψr'⟩ := e.exists_involution hY hL' hR' hLR' hw'
  refine ⟨r, r', hr, hr', e.ker_le ?_, hψr, hψr'⟩
  have hcomm : e.φ r * e.φ r' = e.φ r' * e.φ r := by
    rw [hψr, hψr', locElt_mul, locElt_mul]
    congr 1
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

theorem Layer03.conjSub_eq (e : Layer03 Ω x tY nY) (hY : YData3 tY nY) {L : Subgroup G}
    {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map e.φ) {w : G} (hwx : w ∈ locLayer Ω x)
    {r : (modelUniv tY nY 3 1 Nat.prime_three).K} (hr : e.φ r = locElt Ω x w hwx)
    (hN : conjSub w L = L) : conjSub r R = R := by
  refine eq_of_map_eq_of_pow3 e.φ e.ker_le (e.ker_cop hY) ((hY.pow3 R hR).conjSub r)
    (hY.pow3 R hR) ?_
  have h1 := locImg_conjSub_layer (Ω := Ω) (x := x) L ⟨w, hwx⟩
  rw [hN, hLR] at h1
  have h2 : (conjSub r R).map e.φ =
      (R.map e.φ).map (MulAut.conj (locMk Ω x ⟨w, hwx⟩)).toMonoidHom := by
    show (R.map (MulAut.conj r).toMonoidHom).map e.φ = _
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
    rw [show locMk Ω x ⟨w, hwx⟩ = locElt Ω x w hwx from rfl, ← hr]
  rw [h2, ← h1]

theorem Layer03.pair_to_model (e : Layer03 Ω x tY nY) (hY : YData3 tY nY)
    [Finite (modelUniv tY nY 3 1 Nat.prime_three).K] (hP1 : LocalOddCentral Ω {x})
    {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map e.φ) (hLR' : locImg Ω x L' = R'.map e.φ) {W : Subgroup G}
    (hW : LinearBlockStandardPair (GaloisField 3 1) W L L') :
    ∃ W' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K,
      LinearBlockStandardPair (GaloisField 3 1) W' R R' := by
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members hP1 hL hL' hW
  rw [hLR, hLR'] at hW'
  exact exists_lin_of_map3' (not_three_dvd_card_center' hY.cop) e.φ e.ker_le (hY.pow3 R hR)
    (hY.pow3 R' hR') ⟨W', hW'⟩

theorem Layer03.pair_of_model (e : Layer03 Ω x tY nY) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' W : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hLR : locImg Ω x L = R.map e.φ) (hLR' : locImg Ω x L' = R'.map e.φ)
    (hW : LinearBlockStandardPair (GaloisField 3 1) W R R') :
    ∃ W' : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W' L L' := by
  have h1 := linearBlockStandardPair_map_central hW e.φ e.ker_le
  rw [← hLR, ← hLR'] at h1
  exact linearBlockStandardPair_of_locImg3' hΩ hex hP1 hO3 hL hL' h1

end Transfer

end CFSG.ClassicalInvolution.Q3.Q3TY
