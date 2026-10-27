module

public import CFSG.CGT.PushingUpLit.CGT6.EmbDictMod

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

theorem shortU_le_ker_of_irred {L B : Type} [Group L] [Finite L] [Group B] (hL : IsShortGroup L)
    (π : L →* B) (hπ : Function.Surjective π) (hKT : π.ker ≤ shortU L)
    (hnot : ¬ π.ker ≤ shortC L) : shortU L ≤ π.ker := by
  have hCn : (shortC L).Normal := by
    unfold shortC
    infer_instance
  have hN₁n : (π.ker ⊔ shortC L).Normal := Subgroup.sup_normal _ _
  rcases hL.irreducible _ hN₁n (sup_le hKT shortC_le_shortU) le_sup_right with h | h
  · exact absurd (le_sup_left.trans h.le) hnot
  · have hTle : shortU L ≤ (Subgroup.center B).comap π := by
      rw [← h]
      refine sup_le (fun x hx => ?_) (fun c hc => ?_)
      · rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
        exact Subgroup.one_mem _
      · rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := hπ y
        rw [← map_mul, ← map_mul,
          Subgroup.mem_center_iff.mp ((inf_le_right : shortC L ≤ Subgroup.center L) hc) x]
    have hTop : SubTwo.NoTwoQuotient (⊤ : Subgroup L) :=
      SubTwo.noTwoQuotient_of_oResidualTwo
        (oResidualTwo_eq_top_of_mulEquiv Subgroup.topEquiv.symm hL.residual_eq)
    have hTT : ⁅shortU L, ⊤⁆ = shortU L :=
      SixThree.commutator_commutator_eq (G := L) hTop (pCore_isPGroup (p := 2) (G := L)) (by
        rw [Subgroup.normalizer_eq_top])
    conv_lhs => rw [← hTT]
    rw [Subgroup.commutator_le]
    intro t ht y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hTle ht) _).symm

section Minus

variable {G : Type} [Group G] [Finite G] {V A : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V)
  (D0 : Dict0 V A)

include D0 hV in
theorem not_ker_le_shortC (hΦ : IsShortGroup ↥(yuHolOf hV (autOn A V))) :
    ¬ (projPhi hV A).ker ≤ shortC ↥(yuHolOf hV (autOn A V)) := by
  intro hKC
  have hV2 : IsPGroup 2 ↥V := fun v => ⟨1, Subtype.ext (by simpa using hV.2 v v.2)⟩
  have hW : ⁅⁅V, A⁆, A⁆ = ⁅V, A⁆ :=
    SixThree.commutator_commutator_eq D0.hR hV2 (A_le_normalizer (V := V) (A := A))
  have hcent : ∀ (w : ↥(commOn hV A)) (a : ↥A),
      (a : G) * ((w : ↥V) : G) * (a : G)⁻¹ = ((w : ↥V) : G) := by
    intro w a
    have hw : incPhi hV A w ∈ (projPhi hV A).ker := by
      rw [ker_projPhi hV A]
      exact ⟨w, rfl⟩
    have hz : incPhi hV A w ∈ Subgroup.center ↥(yuHolOf hV (autOn A V)) :=
      (inf_le_right : shortC _ ≤ Subgroup.center _) (hKC hw)
    obtain ⟨u', hu'1, hu'2⟩ := conj_incPhi_exists hV (sigPhi hV A a) w
    have h2 : incPhi hV A u' = incPhi hV A w := by
      rw [← hu'2, Subgroup.mem_center_iff.mp hz (sigPhi hV A a)]
      group
    have h3 : u' = w := @yuInc_injective ↥V (commGroupOfElemAbelian hV) (autOn A V) _ _ h2
    have h5 := right_apply_coe hV (sigPhi hV A a) a rfl (w : ↥V)
    rw [← h5, ← hu'1, h3]
  have hbot : ⁅V, A⁆ = ⊥ := by
    rw [← hW, eq_bot_iff]
    refine Subgroup.commutator_le.mpr (fun m hm a ha => ?_)
    have h4 := hcent (mkV hV m hm) ⟨a, ha⟩
    rw [Subgroup.mem_bot, commutatorElement_def]
    have h6 : a * m = m * a := by
      calc a * m = (a * m * a⁻¹) * a := by group
        _ = m * a := by rw [show a * m * a⁻¹ = m from h4]
    calc m * a * m⁻¹ * a⁻¹ = (m * a) * (a * m)⁻¹ := by group
      _ = 1 := by rw [← h6, mul_inv_cancel]
  have hAC : ∀ a : ↥A, a ∈ (rhoA V A).ker := by
    intro a
    rw [mem_ker_rhoA, Subgroup.mem_centralizer_iff]
    intro v hv
    have h7 : ⁅v, (a : G)⁆ ∈ ⁅V, A⁆ := Subgroup.commutator_mem_commutator hv a.2
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at h7
    have key : ∀ g : G, v * g = (v * g * v⁻¹ * g⁻¹) * (g * v) := fun g => by group
    rw [key (a : G), h7, one_mul]
  have hA1 : A = ⊥ := by
    refine (D0.hR ⊥ bot_le (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      (fun y hy => ?_)).symm
    obtain ⟨k, hk⟩ := D0.hK ⟨y, hy⟩ (hAC ⟨y, hy⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hsub : ∀ x : ↥(yuHolOf hV (autOn A V)), x = 1 := by
    intro x
    have hx := @yu_eq_inc_mul_sec ↥V (commGroupOfElemAbelian hV) (autOn A V) x
    obtain ⟨a, ha⟩ := rhoA_surjective V A ⟨(x : HolOf hV).right, x.2.2⟩
    have hsec : @yuSec ↥V (commGroupOfElemAbelian hV) (autOn A V)
        ⟨(x : HolOf hV).right, x.2.2⟩ = sigPhi hV A a := by
      rw [← ha]
      rfl
    have ha1 : a = 1 := Subtype.ext (by
      have : (a : G) ∈ (⊥ : Subgroup G) := hA1 ▸ a.2
      simpa using this)
    have hleft : (⟨(x : HolOf hV).left, x.2.1⟩ : ↥(commOn hV A)) = 1 := by
      have hm := mem_comm_of_mem_commOn hV (⟨(x : HolOf hV).left, x.2.1⟩ : ↥(commOn hV A)).2
      rw [hbot, Subgroup.mem_bot] at hm
      exact Subtype.ext (Subtype.ext hm)
    rw [hx, hsec, ha1, map_one]
    change incPhi hV A ⟨(x : HolOf hV).left, x.2.1⟩ * 1 = 1
    rw [hleft, map_one, mul_one]
  exact absurd (fun t _ => by rw [hsub t]; exact (shortC _).one_mem :
    shortU ↥(yuHolOf hV (autOn A V)) ≤ shortC ↥(yuHolOf hV (autOn A V))) (not_le_of_gt hΦ.nonzero)

include D0 hV in
theorem shortU_phi_le_ker_of_short (hΦ : IsShortGroup ↥(yuHolOf hV (autOn A V))) :
    shortU ↥(yuHolOf hV (autOn A V)) ≤ (projPhi hV A).ker :=
  shortU_le_ker_of_irred hΦ (projPhi hV A) (projPhi_surjective hV A)
    (fun x hx => by
      rw [ker_projPhi hV A] at hx
      obtain ⟨w, rfl⟩ := hx
      exact incPhi_mem_shortU hV D0 w)
    (not_ker_le_shortC hV D0 hΦ)

include D0 hV in
theorem comm_oTwoIn_le (hΦ : IsShortGroup ↥(yuHolOf hV (autOn A V))) :
    ⁅oTwoIn A, A⁆ ≤ A ⊓ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.commutator_le]
  rintro q ⟨q', hq', rfl⟩ a ha
  have hσ := sigPhi_mem_pCore hV D0 hq'
  have hmem : ⁅sigPhi hV A q', sigPhi hV A ⟨a, ha⟩⁆ ∈ shortU ↥(yuHolOf hV (autOn A V)) :=
    Subgroup.commutator_mem_commutator hσ (Subgroup.mem_top _)
  have hker := shortU_phi_le_ker_of_short hV D0 hΦ hmem
  rw [MonoidHom.mem_ker, map_commutatorElement] at hker
  have h2 : rhoA V A ⁅q', (⟨a, ha⟩ : ↥A)⁆ = 1 := by
    rw [map_commutatorElement]
    exact hker
  exact ⟨(⁅q', (⟨a, ha⟩ : ↥A)⁆ : ↥A).2, (mem_ker_rhoA V A).mp h2⟩

include D0 hV in
theorem hP_of_short (hVA : V ≤ Subgroup.normalizer (A : Set G))
    (hKA : ⁅A ⊓ Subgroup.centralizer (V : Set G), A⁆ ≤ ⁅V, A⁆)
    (hΦ : IsShortGroup ↥(yuHolOf hV (autOn A V))) : ⁅V, A⁆ = ⁅oTwoIn A, A⁆ := by
  have hV2 : IsPGroup 2 ↥V := fun v => ⟨1, Subtype.ext (by simpa using hV.2 v v.2)⟩
  have hW : ⁅⁅V, A⁆, A⁆ = ⁅V, A⁆ :=
    SixThree.commutator_commutator_eq D0.hR hV2 (A_le_normalizer (V := V) (A := A))
  have hQ2 : ⁅⁅oTwoIn A, A⁆, A⁆ = ⁅oTwoIn A, A⁆ :=
    SixThree.commutator_commutator_eq D0.hR (SixThree.isPGroup_oTwoIn A)
      (SixThree.le_normalizer_oTwoIn A)
  refine le_antisymm ?_ ?_
  · have hle : ⁅V, A⁆ ≤ oTwoIn A := by
      intro g hg
      have hgA : g ∈ A := (Subgroup.le_normalizer_iff_commutator_le_right.mp hVA) hg
      have hgC : g ∈ Subgroup.centralizer (V : Set G) :=
        Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1 (Subgroup.commutator_le_left V A hg)
      exact ⟨⟨g, hgA⟩, ker_rhoA_le_pCore D0.hK ((mem_ker_rhoA V A).mpr hgC), rfl⟩
    calc ⁅V, A⁆ = ⁅⁅V, A⁆, A⁆ := hW.symm
      _ ≤ ⁅oTwoIn A, A⁆ := Subgroup.commutator_mono hle le_rfl
  · calc ⁅oTwoIn A, A⁆ = ⁅⁅oTwoIn A, A⁆, A⁆ := hQ2.symm
      _ ≤ ⁅A ⊓ Subgroup.centralizer (V : Set G), A⁆ :=
          Subgroup.commutator_mono (comm_oTwoIn_le hV D0 hΦ) le_rfl
      _ ≤ ⁅V, A⁆ := hKA

include D0 hV in
theorem hZ_of_short (hP : ⁅V, A⁆ = ⁅oTwoIn A, A⁆)
    (hΦ : IsShortGroup ↥(yuHolOf hV (autOn A V))) :
    ∀ u ∈ ⁅oTwoIn A, A⁆, ∀ q ∈ oTwoIn A, u * q = q * u := by
  intro u hu q hq
  obtain ⟨q', hq', rfl⟩ := hq
  have huV : u ∈ ⁅V, A⁆ := hP ▸ hu
  have hmem : incPhi hV A (mkV hV u huV) ∈ shortU ↥(yuHolOf hV (autOn A V)) :=
    incPhi_mem_shortU hV D0 _
  have hcomm := (shortU_le_center_iff.1 hΦ.U_le_center _ hmem).2 _ (sigPhi_mem_pCore hV D0 hq')
  obtain ⟨u', hu'1, hu'2⟩ := conj_incPhi_exists hV (sigPhi hV A q') (mkV hV u huV)
  have h2 : incPhi hV A u' = incPhi hV A (mkV hV u huV) := by
    rw [← hu'2, ← hcomm]
    group
  have h3 : u' = mkV hV u huV :=
    @yuInc_injective ↥V (commGroupOfElemAbelian hV) (autOn A V) _ _ h2
  have h5 := right_apply_coe hV (sigPhi hV A q') q' rfl ((mkV hV u huV).1)
  have h6 : (q' : G) * u * (q' : G)⁻¹ = u := by
    have h7 : ((((sigPhi hV A q' : ↥(yuHolOf hV (autOn A V))) : HolOf hV).right : MulAut ↥V)
        ((mkV hV u huV).1 : ↥V) : ↥V) = ((mkV hV u huV).1 : ↥V) := by
      rw [← hu'1, h3]
    exact h5.symm.trans (congrArg Subtype.val h7)
  calc u * (q' : G) = ((q' : G) * u * (q' : G)⁻¹) * q' := by rw [h6]
    _ = (q' : G) * u := by group

end Minus

theorem embDictMinus_holds : EmbDictMinus := by
  intro G _ _ V A _ hV hVA hK2 hres hF hKA hΦ
  have D0 : Dict0 V A := ⟨kTwo_of_isPGroup hK2, SubTwo.noTwoQuotient_of_oResidualTwo hres⟩
  have hP : ⁅V, A⁆ = ⁅oTwoIn A, A⁆ := hP_of_short hV D0 hVA hKA hΦ.1
  have hZ := hZ_of_short hV D0 hP hΦ.1
  have D : DictHyp V A := { toDict0 := D0, hP := hP, hZ := hZ }
  let S := shortIsoPhi hV D
  refine ⟨⟨⟨hF, hres, S.symm.quotient_type hΦ.1.quotient_type, ?_, S.symm.nonzero hΦ.1.nonzero,
    S.symm.irreducible hΦ.1.irreducible⟩, ?_⟩, hP.symm⟩
  · rw [shortU_le_center_iff]
    intro u hu
    have huU : (u : G) ∈ ⁅oTwoIn A, A⁆ := coe_mem_U ⟨u, hu⟩
    obtain ⟨q, hq, hqu⟩ := SixThree.U_le_oTwoIn A huU
    have hqu' : q = u := Subtype.ext hqu
    refine ⟨hqu' ▸ hq, fun r hr => ?_⟩
    exact Subtype.ext (hZ _ huU (r : G) ⟨r, hr, rfl⟩)
  · rcases hΦ.2 with ⟨n, hn, hnat⟩ | ⟨n, hn, hnat⟩
    · obtain ⟨φ, hφ⟩ := isNaturalAltModule_iff.mp hnat
      exact Or.inl ⟨n, hn, isNaturalAltModule_iff.mpr ⟨_, S.altModule hφ⟩⟩
    · exact Or.inr ⟨n, hn, S.slModule hnat⟩

end CFSG.CGT.PushingUpLit.CGT6
