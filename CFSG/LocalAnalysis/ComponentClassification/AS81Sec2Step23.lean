module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Families

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace Sec2

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem sign_eq_one_of_mul_self_eq_one (h5 : Fintype.card α = 5) {σ : Equiv.Perm α}
    (hσ2 : σ * σ = 1) {e : α} (hfix : ∀ v, σ v = v ↔ v = e) : Equiv.Perm.sign σ = 1 := by
  classical
  have h1 : Fintype.card (Function.fixedPoints σ) = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨e, (hfix e).mpr rfl⟩, fun ⟨v, hv⟩ => Subtype.ext ((hfix v).mp hv)⟩
  rw [Equiv.Perm.sign_of_pow_two_eq_one (by rw [sq]; exact hσ2), h5, h1]
  decide

theorem pow_three_eq_one_of_card_five (h5 : Fintype.card α = 5) {a b : Equiv.Perm α} {e f : α}
    (hef : e ≠ f) (ha2 : a * a = 1) (hafix : ∀ v, a v = v ↔ v = e) (hb2 : b * b = 1)
    (hbfix : ∀ v, b v = v ↔ v = f) (hab : a f = b e) : (a * b) ^ 3 = 1 ∧ a * b ≠ 1 := by
  have ha : ∀ v, a (a v) = v := fun v => by
    rw [← Equiv.Perm.mul_apply, ha2, Equiv.Perm.one_apply]
  have hb : ∀ v, b (b v) = v := fun v => by
    rw [← Equiv.Perm.mul_apply, hb2, Equiv.Perm.one_apply]
  set w := a f with hw
  have hae : a e = e := (hafix e).mpr rfl
  have hbf : b f = f := (hbfix f).mpr rfl
  have hwe : w ≠ e := fun h => hef (by
    have := congrArg a h
    rw [hw, ha, hae] at this
    exact this.symm)
  have hwf : w ≠ f := fun h => hef (by
    have h1 : b e = f := hab ▸ h
    have := congrArg b h1
    rw [hb, hbf] at this
    exact this)
  have hbw : b w = e := by rw [hab, hb]
  have haw : a w = f := by rw [hw, ha]
  have hagree : ∀ v, v ≠ e → v ≠ f → v ≠ w → a v = b v := by
    intro v hve hvf hvw
    have hav : a v ∉ ({e, f, w, v} : Finset α) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => hve ?_, fun h => hvw ?_, fun h => hvf ?_, fun h => hve ((hafix v).mp h)⟩
      · have := congrArg a h; rwa [ha, hae] at this
      · have := congrArg a h; rwa [ha] at this
      · have := congrArg a h; rwa [ha, haw] at this
    have hbv : b v ∉ ({e, f, w, v} : Finset α) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => hvw ?_, fun h => hvf ?_, fun h => hve ?_, fun h => hvf ((hbfix v).mp h)⟩
      · have := congrArg b h; rwa [hb, ← hab] at this
      · have := congrArg b h; rwa [hb, hbf] at this
      · have := congrArg b h; rwa [hb, hbw] at this
    have hcard : ({e, f, w, v} : Finset α).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hvw.symm]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hwf.symm, hvf.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hef, hwe.symm, hve.symm⟩
    have hc : (Finset.univ \ ({e, f, w, v} : Finset α)).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, h5, hcard]
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hc
    have h1 : a v ∈ Finset.univ \ ({e, f, w, v} : Finset α) :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hav⟩
    have h2 : b v ∈ Finset.univ \ ({e, f, w, v} : Finset α) :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hbv⟩
    rw [hu, Finset.mem_singleton] at h1 h2
    rw [h1, h2]
  have hbe : b e = w := hab.symm
  refine ⟨Equiv.ext fun v => ?_, fun h => ?_⟩
  · simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    by_cases hve : v = e
    · rw [hve, hbe, haw, hbf, ← hw, hbw, hae]
    by_cases hvf : v = f
    · rw [hvf, hbf, ← hw, hbw, hae, hbe, haw]
    by_cases hvw : v = w
    · rw [hvw, hbw, hae, hbe, haw, hbf, ← hw]
    have h1 : a (b v) = v := by rw [← hagree v hve hvf hvw, ha]
    rw [h1, h1, h1]
  · have := congrArg (fun σ : Equiv.Perm α => σ e) h
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at this
    rw [hbe, haw] at this
    exact hef this.symm

end Perm

variable {G : Type} [Group G]

@[expose] noncomputable def conjPermHom {Ps : Set (Subgroup G)} {X : Subgroup G}
    (hX : X ≤ conjSetStab Ps) : ↥X →* Equiv.Perm ↥Ps where
  toFun n :=
    { toFun := fun V => ⟨rightConjugate V (n : G)⁻¹, (hX (inv_mem n.2) V).mp V.2⟩
      invFun := fun V => ⟨rightConjugate V n, (hX n.2 V).mp V.2⟩
      left_inv := fun V => Subtype.ext (by
        simp only
        rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one])
      right_inv := fun V => Subtype.ext (by
        simp only
        rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]) }
  map_one' := Equiv.ext fun V => Subtype.ext (by
    simp only [OneMemClass.coe_one, inv_one, Equiv.coe_fn_mk, Equiv.Perm.coe_one, id_eq]
    exact rightConjugate_one _)
  map_mul' n m := Equiv.ext fun V => Subtype.ext (by
    simp only [Subgroup.coe_mul, mul_inv_rev, Equiv.coe_fn_mk, Equiv.Perm.coe_mul,
      Function.comp_apply]
    rw [rightConjugate_mul])

theorem conjPermHom_apply {Ps : Set (Subgroup G)} {X : Subgroup G} (hX : X ≤ conjSetStab Ps)
    (n : ↥X) (V : ↥Ps) : ((conjPermHom hX n V : ↥Ps) : Subgroup G) = rightConjugate V (n : G)⁻¹ :=
  rfl

theorem inf_normalizer_eq_of_mem_conjSet {V W X C : Subgroup G} (hV : V ∈ conjSet W X)
    (hC : X ⊓ normalizer (W : Set G) = C) (hXC : X ≤ normalizer (C : Set G)) :
    X ⊓ normalizer (V : Set G) = C := by
  obtain ⟨q, hq, rfl⟩ := hV
  ext n
  rw [mem_inf, ← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff,
    (mem_normalizer_iff.mp (hXC hq) n), ← hC, mem_inf]
  constructor
  · rintro ⟨hn, hqn⟩
    exact ⟨X.mul_mem (X.mul_mem hq hn) (X.inv_mem hq), hqn⟩
  · rintro ⟨hqnX, hqn⟩
    refine ⟨?_, hqn⟩
    have := X.mul_mem (X.mul_mem (X.inv_mem hq) hqnX) hq
    simpa [mul_assoc] using this

end Sec2

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem sec2P_inf_normalizer_F_eq :
    sec2P E ⊓ normalizer (F : Set G) =
      centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  have hPN := sec2P_sup_sec2S_inf_normalizer h11 hE16 hF hL hodd
  have hSP := sec2S_inf_sec2P h11 hE16 hF hL hodd
  have hSF := sec2S_le_normalizer h11 hE16 hF hL hodd
  refine le_antisymm (fun p hp => ?_)
    (le_inf (fun c hc => (mem_centralizerMod.mp hc).1) (le_sup_right.trans hSF))
  have h1 : p ∈ (sec2P E ⊔ sec2S A R E F) ⊓ normalizer (F : Set G) := ⟨mem_sup_left hp.1, hp.2⟩
  rw [hPN] at h1
  rw [← hSP]
  exact ⟨h1, hp.1⟩

theorem sec2P_le_normalizer_centralizerMod :
    sec2P E ≤ normalizer (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) : Set G) :=
  fun q hq => Sec2.mem_normalizer_of_forall_conj_mem fun c hc => by
    obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
    have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
    have h1 := (hD.sq_mem_and_commutator_mem hT hCE hq (mem_centralizerMod.mp hc).1).2
    have h2 : q * c * q⁻¹ = (q * c * q⁻¹ * c⁻¹) * c := by group
    rw [h2]
    exact mul_mem (le_centralizerMod hF h1) hc

theorem inducesA5_sec2H {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G}
    (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) :
    InducesA5 (sec2H E F) (conjSet E (sec2H E F)) := by
  classical
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have hhS' : h ∉ sec2S A R F E := hSc ▸ hhS
  set H := sec2H E F with hHdef
  set Ps := conjSet E H with hPsdef
  set C := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) with hCdef
  set C' := centralizerMod (sec2P F) (R ⊔ sec2Z A F E) (sec2Z A F E) with hC'def
  set F₀' := sec2F0 A F h with hF₀'
  have hEH := conjSet_E_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hEHi := conjSet_E_sec2H_eq_insert h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hU := planes_sec2S_eq_conjSet_union h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hPs5 : Ps.ncard = 5 := by
    rw [hPsdef, hEH]
    exact ncard_sec2Fam h11 hE16 hF.symm hL hodd hh hhS'
  have hHPs : H ≤ Sec2.conjSetStab Ps := Sec2.le_conjSetStab fun n hn V ⟨θ, hθ, hV⟩ =>
    ⟨θ * n, mul_mem hθ hn, by rw [hV, rightConjugate_mul]⟩
  have hPsfin : Ps.Finite := Set.finite_of_ncard_ne_zero (by rw [hPs5]; norm_num)
  have : Finite ↥Ps := hPsfin.to_subtype
  have : Fintype ↥Ps := Fintype.ofFinite _
  have hcard5 : Fintype.card ↥Ps = 5 := by
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, hPs5]
  refine ⟨by rw [Nat.card_coe_set_eq, hPs5], fun n hn V hV => (hHPs hn V).mp hV, ?_⟩
  set ψ := Sec2.conjPermHom hHPs with hψ
  have hPi : {σ : Equiv.Perm ↥Ps | ∃ n ∈ H, ∀ V : ↥Ps,
      ((σ V : ↥Ps) : Subgroup G) = rightConjugate (V : Subgroup G) n} =
      (ψ.range : Set (Equiv.Perm ↥Ps)) := by
    ext σ
    constructor
    · rintro ⟨n, hn, hσ⟩
      refine ⟨⟨n⁻¹, inv_mem hn⟩, Equiv.ext fun V => Subtype.ext ?_⟩
      rw [hσ, Sec2.conjPermHom_apply]
      simp
    · rintro ⟨n, rfl⟩
      exact ⟨(n : G)⁻¹, inv_mem n.2, fun V => Sec2.conjPermHom_apply hHPs n V⟩
  rw [hPi]
  change Nat.card ψ.range = 60
  have hVS : ∀ V ∈ Ps, sec2S A R E F ≤ normalizer (V : Set G) := fun V hV => by
    have hV' : V ∈ {V | V ∈ planes E F ∧ V ≤ sec2S A R E F} := hU ▸ Or.inr hV
    exact sec2S_le_normalizer_of_sec2Z_le h11 hE16 hF hL hodd
      (sec2Z_le_of_mem_planes h11 hE16 hF hL hodd hV'.1 hV'.2) hV'.2
  have hS1 : ∀ n : ↥H, (n : G) ∈ sec2S A R E F → ψ n = 1 := fun n hn =>
    Equiv.ext fun V => Subtype.ext (by
      rw [Sec2.conjPermHom_apply, Equiv.Perm.one_apply]
      exact (rightConjugate_eq_self_iff _ _).mpr (hVS V V.2 (inv_mem hn)))
  have hE_mem : E ∈ Ps := ⟨1, one_mem _, (rightConjugate_one E).symm⟩
  have hF₀'_mem : F₀' ∈ Ps := by rw [hPsdef, hEH]; exact Set.mem_insert _ _
  have hF₀'E : F₀' ≠ E := fun h' => by
    have h1 := sec2F0_inf_F_eq h11 hE16 hF.symm hL hodd hh hhS'
    rw [← hF₀', h', inf_idem, sec2Z_comm] at h1
    have h2 := hF.cardE
    rw [h1, hF.card_sec2Z hodd] at h2
    omega
  have hF₀'x : F₀' ∈ conjSet (rightConjugate E x) (sec2P E) := by
    have h1 := hF₀'_mem
    rw [hPsdef, hEHi] at h1
    exact h1.resolve_left hF₀'E
  have hPsE : ∀ V ∈ Ps, V ≠ E → V ∈ conjSet F₀' (sec2P E) := fun V hV hVE => by
    rw [hPsdef, hEHi] at hV
    rw [Sec2.conjSet_eq_of_mem_conjSet hF₀'x]
    exact hV.resolve_left hVE
  have hPsF : ∀ V ∈ Ps, V ≠ F₀' → V ∈ conjSet E (sec2P F) := fun V hV hVF => by
    rw [hPsdef, hEH] at hV
    exact hV.resolve_left hVF
  have hNV : ∀ V ∈ Ps, V ≠ E → sec2P E ⊓ normalizer (V : Set G) = C := fun V hV hVE =>
    Sec2.inf_normalizer_eq_of_mem_conjSet (hPsE V hV hVE)
      (sec2P_inf_normalizer_sec2F0_symm_eq h11 hE16 hF hL hodd hh hhS h4')
      (sec2P_le_normalizer_centralizerMod h11 hE16 hF hL hodd)
  have hNV' : ∀ V ∈ Ps, V ≠ F₀' → sec2P F ⊓ normalizer (V : Set G) = C' := fun V hV hVF =>
    Sec2.inf_normalizer_eq_of_mem_conjSet (hPsF V hV hVF)
      (sec2P_inf_normalizer_F_eq h11 hE16 hF.symm hL hodd)
      (sec2P_le_normalizer_centralizerMod h11 hE16 hF.symm hL hodd)
  set E' : ↥Ps := ⟨E, hE_mem⟩ with hE'
  set F₀'' : ↥Ps := ⟨F₀', hF₀'_mem⟩ with hF₀''
  have hE'F : E' ≠ F₀'' := fun h' => hF₀'E (congrArg Subtype.val h').symm
  have hPH : sec2P E ≤ H := le_sup_left
  have hPFH : sec2P F ≤ H := le_sup_right
  obtain ⟨-, -, hES⟩ := isElemQuot_sec2P h11 hE16 hF hL hodd
  obtain ⟨-, -, hFS⟩ := isElemQuot_sec2P h11 hE16 hF.symm hL hodd
  obtain ⟨hEle, hFle⟩ := le_sec2S_and_le_sec2S (A := A) (R := R) hF
  have hfixV : ∀ (n : ↥H) (V : ↥Ps), ψ n V = V →
      (n : G)⁻¹ ∈ normalizer ((V : Subgroup G) : Set G) :=
    fun n V hV => (rightConjugate_eq_self_iff _ _).mp (congrArg Subtype.val hV)
  have hP2 : ∀ p (hp : p ∈ sec2P E), ψ ⟨p, hPH hp⟩ * ψ ⟨p, hPH hp⟩ = 1 := fun p hp => by
    rw [← map_mul]
    exact hS1 _ (hEle (hES p hp p hp).1)
  have hPfix : ∀ p (hp : p ∈ sec2P E), p ∉ C → ∀ V, ψ ⟨p, hPH hp⟩ V = V ↔ V = E' :=
    fun p hp hpC V => by
      refine ⟨fun hV => ?_, fun hV => ?_⟩
      · by_contra hVE
        have hVE' : (V : Subgroup G) ≠ E := fun h' => hVE (Subtype.ext h')
        have h1 : p⁻¹ ∈ sec2P E ⊓ normalizer ((V : Subgroup G) : Set G) :=
          ⟨(sec2P E).inv_mem hp, hfixV _ V hV⟩
        rw [hNV V V.2 hVE'] at h1
        exact hpC (by simpa using inv_mem h1)
      · rw [hV]
        exact Subtype.ext ((rightConjugate_eq_self_iff _ _).mpr (Sec2.sec2P_le E (inv_mem hp)))
  have hPC : ∀ p (hp : p ∈ sec2P E), p ∈ C → ψ ⟨p, hPH hp⟩ = 1 := fun p hp hpC =>
    hS1 _ (mem_sup_right hpC)
  have hF₀'N := sec2P_le_normalizer_sec2F0 h11 hE16 hF.symm hL hodd hh hhS'
  have hPF2 : ∀ y (hy : y ∈ sec2P F), ψ ⟨y, hPFH hy⟩ * ψ ⟨y, hPFH hy⟩ = 1 := fun y hy => by
    rw [← map_mul]
    exact hS1 _ (hFle (hFS y hy y hy).1)
  have hPFfix : ∀ y (hy : y ∈ sec2P F), y ∉ C' → ∀ V, ψ ⟨y, hPFH hy⟩ V = V ↔ V = F₀'' :=
    fun y hy hyC V => by
      refine ⟨fun hV => ?_, fun hV => ?_⟩
      · by_contra hVF
        have hVF' : (V : Subgroup G) ≠ F₀' := fun h' => hVF (Subtype.ext h')
        have h1 : y⁻¹ ∈ sec2P F ⊓ normalizer ((V : Subgroup G) : Set G) :=
          ⟨(sec2P F).inv_mem hy, hfixV _ V hV⟩
        rw [hNV' V V.2 hVF'] at h1
        exact hyC (by simpa using inv_mem h1)
      · rw [hV]
        exact Subtype.ext ((rightConjugate_eq_self_iff _ _).mpr (hF₀'N (inv_mem hy)))
  have hPFC : ∀ y (hy : y ∈ sec2P F), y ∈ C' → ψ ⟨y, hPFH hy⟩ = 1 := fun y hy hyC =>
    hS1 _ (hSc ▸ (mem_sup_right hyC : y ∈ sec2S A R F E))
  have hsignP : ∀ p (hp : p ∈ sec2P E), Equiv.Perm.sign (ψ ⟨p, hPH hp⟩) = 1 := fun p hp => by
    by_cases hpC : p ∈ C
    · rw [hPC p hp hpC, map_one]
    · exact Sec2.sign_eq_one_of_mul_self_eq_one hcard5 (hP2 p hp) (hPfix p hp hpC)
  have hsignPF : ∀ y (hy : y ∈ sec2P F), Equiv.Perm.sign (ψ ⟨y, hPFH hy⟩) = 1 := fun y hy => by
    by_cases hyC : y ∈ C'
    · rw [hPFC y hy hyC, map_one]
    · exact Sec2.sign_eq_one_of_mul_self_eq_one hcard5 (hPF2 y hy) (hPFfix y hy hyC)
  have hrange : ψ.range = ((sec2P E).subgroupOf H).map ψ ⊔ ((sec2P F).subgroupOf H).map ψ := by
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hPH hPFH, MonoidHom.range_eq_map]
    congr 1
    exact (Subgroup.subgroupOf_self H).symm
  have hAlt : ψ.range ≤ alternatingGroup ↥Ps := by
    rw [hrange]
    refine sup_le ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      exact Equiv.Perm.mem_alternatingGroup.mpr (hsignP _ (mem_subgroupOf.mp hn))
    · rintro _ ⟨n, hn, rfl⟩
      exact Equiv.Perm.mem_alternatingGroup.mpr (hsignPF _ (mem_subgroupOf.mp hn))
  have : Nontrivial ↥Ps := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hcard5]; norm_num)
  have h60 : Nat.card (alternatingGroup ↥Ps) = 60 := by
    have h1 := two_mul_nat_card_alternatingGroup (α := ↥Ps)
    rw [Nat.card_perm, Nat.card_coe_set_eq, hPs5] at h1
    have h2 : (5 : ℕ).factorial = 120 := by decide
    omega
  have hdvd60 : Nat.card ψ.range ∣ 60 := h60 ▸ Subgroup.card_dvd_of_le hAlt
  have hψE : ∀ (n : ↥H) (V : ↥Ps), ((ψ n V : ↥Ps) : Subgroup G) = rightConjugate V (n : G)⁻¹ :=
    fun n V => Sec2.conjPermHom_apply hHPs n V
  have h5dvd : 5 ∣ Nat.card ψ.range := by
    have horb : MulAction.orbit ψ.range E' = Set.univ := by
      ext V
      simp only [Set.mem_univ, iff_true]
      obtain ⟨θ, hθ, hV⟩ := V.2
      refine ⟨⟨ψ ⟨θ⁻¹, inv_mem hθ⟩, ⟨_, rfl⟩⟩, Subtype.ext ?_⟩
      change ((ψ ⟨θ⁻¹, inv_mem hθ⟩ E' : ↥Ps) : Subgroup G) = V
      rw [hψE, hV]
      simp [hE']
    have h1 := MulAction.index_stabilizer ψ.range E'
    rw [horb, Set.ncard_univ, Nat.card_eq_fintype_card, hcard5] at h1
    exact h1 ▸ Subgroup.index_dvd_card _
  set K₁ := ((sec2P E).subgroupOf H).map ψ with hK₁
  have hK₁le : K₁ ≤ ψ.range := by rw [hrange]; exact le_sup_left
  have horbK : MulAction.orbit K₁ F₀'' = {E'}ᶜ := by
    ext V
    constructor
    · rintro ⟨⟨σ, ⟨n, hn, rfl⟩⟩, rfl⟩
      change ψ n F₀'' ≠ E'
      intro h'
      have hE'fix : ψ n E' = E' := Subtype.ext ((rightConjugate_eq_self_iff _ _).mpr
        (Sec2.sec2P_le E (inv_mem (mem_subgroupOf.mp hn))))
      exact hE'F ((ψ n).injective (h'.trans hE'fix.symm)).symm
    · intro hVE
      have hVE' : (V : Subgroup G) ≠ E := fun h' => hVE (Subtype.ext h')
      obtain ⟨q, hq, hVq⟩ := hPsE V V.2 hVE'
      refine ⟨⟨ψ ⟨q⁻¹, hPH (inv_mem hq)⟩, ⟨⟨q⁻¹, hPH (inv_mem hq)⟩,
        mem_subgroupOf.mpr (inv_mem hq), rfl⟩⟩, Subtype.ext ?_⟩
      change ((ψ ⟨q⁻¹, hPH (inv_mem hq)⟩ F₀'' : ↥Ps) : Subgroup G) = V
      rw [hψE, hVq]
      simp [hF₀'']
  have h4dvd : 4 ∣ Nat.card ψ.range := by
    have h1 := MulAction.index_stabilizer K₁ F₀''
    rw [horbK, Set.ncard_compl, Set.ncard_singleton, Nat.card_eq_fintype_card, hcard5] at h1
    exact (h1 ▸ Subgroup.index_dvd_card _).trans (Subgroup.card_dvd_of_le hK₁le)
  obtain ⟨y₀, hy₀, hy₀C⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF.symm hL hodd
  set b := ψ ⟨y₀, hPFH hy₀⟩ with hb
  have hbfix := hPFfix y₀ hy₀ hy₀C
  have hWE : b E' ≠ E' := fun h' => hE'F ((hbfix E').mp h')
  have hWorb : b E' ∈ MulAction.orbit K₁ F₀'' := by rw [horbK]; exact hWE
  obtain ⟨⟨σ, ⟨n, hn, rfl⟩⟩, hσ⟩ := hWorb
  have hσ' : ψ n F₀'' = b E' := hσ
  have hn' : (n : G) ∈ sec2P E := mem_subgroupOf.mp hn
  have hnψ : ψ n = ψ ⟨(n : G), hPH hn'⟩ := rfl
  have hnC : (n : G) ∉ C := fun hnC => by
    have h1 : ψ n F₀'' = F₀'' := by rw [hnψ, hPC _ hn' hnC, Equiv.Perm.one_apply]
    have h2 : b F₀'' = F₀'' := (hbfix F₀'').mpr rfl
    exact hE'F (b.injective (by rw [← hσ', h1, h2]))
  obtain ⟨h3, hne⟩ := Sec2.pow_three_eq_one_of_card_five hcard5 hE'F
    (by rw [hnψ]; exact hP2 _ hn') (by rw [hnψ]; exact hPfix _ hn' hnC)
    (hPF2 y₀ hy₀) hbfix hσ'
  have hord : orderOf (ψ n * b) = 3 := orderOf_eq_prime h3 hne
  have h3dvd : 3 ∣ Nat.card ψ.range :=
    hord ▸ Subgroup.orderOf_dvd_natCard _ (ψ.range.mul_mem ⟨n, rfl⟩ ⟨_, rfl⟩)
  have h12 : 12 ∣ Nat.card ψ.range :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3dvd h4dvd
  have h60' : 60 ∣ Nat.card ψ.range :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h12 h5dvd
  exact Nat.dvd_antisymm hdvd60 h60'

end Frame

theorem step23_of (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (h22iv : Step22iv) : Step23 := by
  intro G _ _ A R g E F hS x hx hxS
  have hF := hS.frame
  have hL := hS.type
  have hodd := hS.odd
  have h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)) :=
    h22iv G A R g F E ⟨hF.symm, hL, hodd, hS.below⟩
  have h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E)) := h22iv G A R g E F hS
  obtain ⟨h, hh, hhC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF hL hodd
  have hhS : h ∉ sec2S A R E F := fun hS' => hhC (by
    rw [← sec2S_inf_sec2P h11 hE16 hF hL hodd]
    exact ⟨hS', hh⟩)
  obtain ⟨h1, h2⟩ := rightConjugate_inf_eq_and_sec2S_eq h11 hE16 hF hL hodd hx hxS
  exact ⟨h1, h2, sec2P_inf_sec2S_eq h11 hE16 hF hL hodd hx hxS,
    isElemAbelian_sec2F0 (x := x) h11 hE16 hF hL hodd,
    card_sec2F0 h11 hE16 hF hL hodd hx hxS,
    fun U hU hUe => le_or_le_of_isElemAbelian h11 hE16 hF hL hodd hx hxS hU hUe,
    conjSet_F_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4',
    conjSet_E_sec2H_eq_insert h11 hE16 hF hL hodd hx hxS hh hhS h4 h4',
    planes_sec2S_eq_conjSet_union h11 hE16 hF hL hodd hx hxS hh hhS h4 h4',
    fun n hn => image_conjSet_sec2H_eq_or h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hn,
    inducesA5_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'⟩

end CFSG.ComponentClassification.AS81
