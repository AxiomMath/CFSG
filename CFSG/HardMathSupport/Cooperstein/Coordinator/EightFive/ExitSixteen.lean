module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepTransitive
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolLarge

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.RankThree.PartTwo Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

theorem card_fixV_zpowers_conj_eq {V : Type*} [CommGroup V] (g x : MulAut V) :
    Nat.card (fixV (Subgroup.zpowers (g * x * g⁻¹))) = Nat.card (fixV (Subgroup.zpowers x)) :=
  CFSG.Quasithin.card_fixV_zpowers_conj g x

theorem cycleRange_six_pow_seven : (Fin.cycleRange (6 : Fin 8)) ^ 7 = 1 := by
  have h1 := lcm_cycleType (Fin.cycleRange (6 : Fin 8))
  rw [Fin.cycleType_cycleRange (by decide)] at h1
  have h2 : orderOf (Fin.cycleRange (6 : Fin 8)) = 7 := by
    rw [← h1]
    rfl
  have h3 := pow_orderOf_eq_one (Fin.cycleRange (6 : Fin 8))
  rwa [h2] at h3

theorem cycleRange_six_apply_zero : Fin.cycleRange (6 : Fin 8) 0 ≠ 0 := by
  rw [Fin.cycleRange_of_lt (by decide)]
  decide

theorem cycleRange_six_mem : Fin.cycleRange (6 : Fin 8) ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup, Fin.sign_cycleRange]
  decide

theorem exitSixteenTransitive : ExitSixteenTransitive := by
  intro V _ _ hV H ψ hψ hAlt A hA htr a haA ha1 B hBA haB hAB ι hBΓ hBtr ht hMW hC hout
  classical
  have : Finite (MulAut V) := Finite.of_injective _ DFunLike.coe_injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := hA.2.2.1.1
  have hsq := hA.2.2.1.2
  have ha2 : (a : MulAut V) ^ 2 = 1 := hsq _ haA
  have hainv : (a : MulAut V)⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ha2)
  have hψa2 : ∀ x, ψ a (ψ a x) = x := fun x => by
    have h1 : a * a = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, ha2]; rfl)
    have h2 := congrArg (fun g : Perm (Fin 16) => g x) (congrArg ψ h1)
    simpa only [map_mul, map_one, Perm.mul_apply, Perm.one_apply] using h2
  have hκsurj := fun σ =>
    restrictHom_transM_surjective (ψ := ψ) (ι := ι) (t := ψ a) hAlt ht hψa2 σ
  have hκinj := restrictHom_transM_injective (ψ := ψ) (ι := ι) (t := ψ a) hψ ht hψa2
  have hker : ∀ k : ↥(transM ψ ι (ψ a)), restrictHom ψ ι _ (transM_le ψ ι (ψ a)) k = 1 →
      ∀ w ∈ fixV (Subgroup.zpowers (a : MulAut V)), (k : MulAut V) w = w := fun k hk w _ => by
    rw [show k = 1 from hκinj (hk.trans (map_one _).symm)]
    rfl
  have hψWinj := autSubLift_injective (hKW := hMW) (hC := hC) hker
  have hψWrange : (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC).range = ⊤ := by
    rw [range_autSubLift, eq_top_iff]
    intro σ _
    obtain ⟨k, hk, -⟩ := hκsurj σ
    exact ⟨k, hk⟩
  have hBM : B ≤ transM ψ ι (ψ a) := fun b hb => by
    have hbH := (hBA.trans hA.1) hb
    refine (coe_mem_preSub (x := ⟨b, hbH⟩)).2
      ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hBΓ ⟨b, hbH⟩ hb⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hcomm _ (hBA hb) _ haA))
  have hnormal : ∀ {K : Subgroup (MulAut V)}, (∀ k ∈ K, k * (a : MulAut V) = a * k) →
      K ≤ Subgroup.normalizer (Subgroup.zpowers (a : MulAut V) : Set (MulAut V)) :=
    fun hK d hd => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute (a : MulAut V) d from (hK d hd).symm) j).eq)
  have hAW := le_stabSub_fixV (hnormal fun g hg => hcomm g hg _ haA)
  have hAMW : autSub A (fixV (Subgroup.zpowers (a : MulAut V))) ≤
      autSub (transM ψ ι (ψ a)) (fixV (Subgroup.zpowers (a : MulAut V))) := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
    rcases hAB _ hg with hgB | hagB
    · exact mem_autSub.2 ⟨g, hBM hgB, rfl⟩
    · refine mem_autSub.2 ⟨⟨a * g, hAW (A.mul_mem haA hg)⟩, hBM hagB, ?_⟩
      refine MulEquiv.ext fun w => Subtype.ext ?_
      change (a : MulAut V) ((g : MulAut V) w) = (g : MulAut V) w
      exact mem_fixV_zpowers_iff.1 ((g.2 w).2 w.2)
  have hWA : commSub (fixV (Subgroup.zpowers (a : MulAut V))) A ≠ ⊥ := by
    intro hbot
    obtain ⟨b, hb, hbij⟩ := hBtr 0 1
    have hκb : restrictHom ψ ι _ (transM_le ψ ι (ψ a)) ⟨b, hBM hb⟩ ≠ 1 := fun h => by
      have h1 := restrictHom_apply_apply (hK := transM_le ψ ι (ψ a)) ⟨(b : MulAut V), hBM hb⟩ 0
      rw [h, Perm.one_apply] at h1
      have h2 := ι.injective (h1.trans hbij)
      exact absurd h2 (by decide)
    exact hκb (hC ⟨b, hBM hb⟩ fun w hw => (commSub_eq_bot_iff.1 hbot) hw _ (hBA hb))
  have hoffW := isFFStarOffender_autSub hA (fun g hg w hw => ((hAW hg) w).2 hw) hWA hAMW
  have hcardA : Nat.card A = 16 := by
    have : IsPretransitive ((A.subgroupOf H).map ψ) (Fin 16) := htr
    have hE : IsExp2 ((A.subgroupOf H).map ψ) := isExp2_map_subgroupOf hA.2.2.1
    have h1 := card_eq_of_isExp2_of_pretransitive hE (Ω := Fin 16)
    rw [Nat.card_fin, Subgroup.card_map_of_injective hψ] at h1
    rw [← h1]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv).symm
  have hcent : A ⊓ centSub (fixV (Subgroup.zpowers (a : MulAut V))) =
      Subgroup.zpowers (a : MulAut V) := by
    apply le_antisymm
    · rintro g ⟨hgA, hgW⟩
      rcases hAB g hgA with hgB | hagB
      · have h1 := hC ⟨g, hBM hgB⟩ fun w hw => hgW w hw
        have h2 : (⟨g, hBM hgB⟩ : ↥(transM ψ ι (ψ a))) = 1 := hκinj (h1.trans (map_one _).symm)
        rw [show g = 1 from congrArg Subtype.val h2]
        exact Subgroup.one_mem _
      · have hagW : ∀ w ∈ fixV (Subgroup.zpowers (a : MulAut V)),
            ((a : MulAut V) * g) w = w := fun w hw => by
          rw [MulAut.mul_apply, hgW w hw]
          exact mem_fixV_zpowers_iff.1 hw
        have h1 := hC ⟨_, hBM hagB⟩ hagW
        have h2 : (⟨_, hBM hagB⟩ : ↥(transM ψ ι (ψ a))) = 1 := hκinj (h1.trans (map_one _).symm)
        have h3 : (a : MulAut V) * g = 1 := congrArg Subtype.val h2
        rw [eq_inv_of_mul_eq_one_right h3, hainv]
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact ⟨haA, fun w hw => mem_fixV_zpowers_iff.1 hw⟩
  have hAW8 : Nat.card (autSub A (fixV (Subgroup.zpowers (a : MulAut V)))) = 8 := by
    have h := card_autSub_mul hAW
    rw [hcent, Nat.card_zpowers, orderOf_eq_prime ha2 ha1, hcardA] at h
    omega
  have hfixA : Nat.card (fixV (autSub A (fixV (Subgroup.zpowers (a : MulAut V))))) =
      Nat.card (fixV A) := by
    have h1 := map_subtype_fixV_autSub hAW
    have h2 : fixV (Subgroup.zpowers (a : MulAut V)) ⊓ fixV A = fixV A :=
      inf_eq_right.2 fun v hv => mem_fixV_zpowers_iff.2 (hv _ haA)
    rw [h2] at h1
    rw [← h1, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hkey : Nat.card (autSub A (fixV (Subgroup.zpowers (a : MulAut V)))) *
      Nat.card (fixV (autSub A (fixV (Subgroup.zpowers (a : MulAut V))))) ≤
        Nat.card (fixV (Subgroup.zpowers (a : MulAut V))) := by
    rcases hout with hnat | hex
    · obtain ⟨π, hπ, hkerπ, heq⟩ := hnat
      have hAB' : ∀ b ∈ ((autSub A (fixV (Subgroup.zpowers (a : MulAut V)))).subgroupOf
          (autSub (transM ψ ι (ψ a)) (fixV (Subgroup.zpowers (a : MulAut V))))).map
            (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC),
          ∃ a' ∈ autSub A (fixV (Subgroup.zpowers (a : MulAut V))),
            ∀ u v : ↥(commV (autSub (transM ψ ι (ψ a)) (fixV (Subgroup.zpowers (a : MulAut V))))),
              (v : ↥(fixV (Subgroup.zpowers (a : MulAut V)))) = a' u →
                Multiplicative.toAdd (π v) = altAct b (Multiplicative.toAdd (π u)) := by
        rintro _ ⟨φ, hφ, rfl⟩
        exact ⟨φ, hφ, fun u v huv => heq φ u v huv⟩
      have n1 := card_mul_card_inf_fixV_le (Y := ⊤) inf_le_left le_top π hπ hkerπ hAB'
      rw [top_inf_eq, Subgroup.card_top] at n1
      have hcardB : Nat.card (((autSub A (fixV (Subgroup.zpowers (a : MulAut V)))).subgroupOf
          (autSub (transM ψ ι (ψ a)) (fixV (Subgroup.zpowers (a : MulAut V))))).map
            (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC)) = 8 := by
        rw [Subgroup.card_map_of_injective hψWinj]
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAMW).toEquiv).trans hAW8
      have hBexp : IsExp2 (((autSub A (fixV (Subgroup.zpowers (a : MulAut V)))).subgroupOf
          (autSub (transM ψ ι (ψ a)) (fixV (Subgroup.zpowers (a : MulAut V))))).map
            (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC)) := by
        rintro _ ⟨φ, hφ, rfl⟩
        rw [← map_mul]
        have : φ * φ = 1 := by
          obtain ⟨g, hg, hgφ⟩ := mem_autSub.1 (Subgroup.mem_subgroupOf.1 hφ)
          refine Subtype.ext ?_
          change (φ : MulAut ↥(fixV (Subgroup.zpowers (a : MulAut V)))) * φ = 1
          rw [← hgφ, ← map_mul]
          have hgg : g * g = 1 := Subtype.ext (by
            rw [Subgroup.coe_mul, ← pow_two]
            exact hsq _ hg)
          rw [hgg, map_one]
        rw [this, map_one]
      have hΔ : ¬ IsMatchingGroup (((autSub A (fixV (Subgroup.zpowers (a : MulAut V)))).subgroupOf
          (autSub (transM ψ ι (ψ a)) (fixV (Subgroup.zpowers (a : MulAut V))))).map
            (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC)) := fun hΔ => by
        have := two_pow_le_card_of_isMatchingGroup hΔ
        rw [hcardB] at this
        norm_num at this
      have hFF := natFF_le (by norm_num) hBexp hΔ
      rw [hcardB] at hFF
      have hCN : 0 < Nat.card (altFix 8 (((autSub A (fixV (Subgroup.zpowers
          (a : MulAut V)))).subgroupOf (autSub (transM ψ ι (ψ a))
            (fixV (Subgroup.zpowers (a : MulAut V))))).map
              (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC))) := Nat.card_pos
      rw [hAW8]
      refine Nat.le_of_mul_le_mul_right ?_ hCN
      calc 8 * Nat.card (fixV (autSub A (fixV (Subgroup.zpowers (a : MulAut V))))) *
            Nat.card (altFix 8 (((autSub A (fixV (Subgroup.zpowers
              (a : MulAut V)))).subgroupOf (autSub (transM ψ ι (ψ a))
                (fixV (Subgroup.zpowers (a : MulAut V))))).map
                  (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC)))
          = 8 * Nat.card (altFix 8 (((autSub A (fixV (Subgroup.zpowers
              (a : MulAut V)))).subgroupOf (autSub (transM ψ ι (ψ a))
                (fixV (Subgroup.zpowers (a : MulAut V))))).map
                  (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC))) *
            Nat.card (fixV (autSub A (fixV (Subgroup.zpowers (a : MulAut V))))) := by ring
        _ ≤ Nat.card (altHeart 8) *
            Nat.card (fixV (autSub A (fixV (Subgroup.zpowers (a : MulAut V))))) :=
          Nat.mul_le_mul_right _ hFF
        _ ≤ _ := n1
    · exact (hex.2.2 hψWrange _ hoffW).symm.le
  have hVW : Nat.card V ≤ 2 * Nat.card (fixV (Subgroup.zpowers (a : MulAut V))) := by
    have o1 : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
      have := hA.2.2.2 ⊥ bot_le
      rwa [B1.card_bot_mul_card_fixV] at this
    rw [hcardA, ← hfixA] at o1
    rw [hAW8] at hkey
    omega
  have hσ7 : (⟨_, cycleRange_six_mem⟩ : alternatingGroup (Fin 8)) ^ 7 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact cycleRange_six_pow_seven)
  obtain ⟨z, hz⟩ := hAlt (altLift ι ⟨_, cycleRange_six_mem⟩).2
  have hu_out : ∀ x ∉ Set.range ι, ψ z x = x := fun x hx => by
    rw [hz]
    exact altLift_apply_of_notMem ι _ hx
  have hu_stab : ψ z ∈ permSetStab (Set.range ι) := hz ▸ altLift_mem_permSetStab ι _
  have hu7 : ψ z ^ 7 = 1 := by
    rw [hz, ← SubgroupClass.coe_pow, ← map_pow, hσ7, map_one]
    rfl
  have htt : ψ a * ψ a = 1 := Equiv.ext fun x => hψa2 x
  have htinv : (ψ a)⁻¹ = ψ a := inv_eq_of_mul_eq_one_right htt
  have hw_in : ∀ x ∈ Set.range ι, (ψ a * (ψ z)⁻¹ * ψ a) x = x := fun x hx => by
    have h1 : ψ a x ∉ Set.range ι := fun h => (ht x).1 h hx
    have h2 : (ψ z)⁻¹ (ψ a x) = ψ a x := by
      rw [Perm.inv_eq_iff_eq]
      exact (hu_out _ h1).symm
    simp only [Perm.mul_apply]
    rw [h2, hψa2]
  have hw_stab : ψ a * (ψ z)⁻¹ * ψ a ∈ permSetStab (Set.range ι) := fun x => by
    by_cases hx : x ∈ Set.range ι
    · rw [hw_in x hx]
    · have h1 : ψ a x ∈ Set.range ι := (ht x).2 hx
      have h2 : (ψ z)⁻¹ (ψ a x) ∈ Set.range ι :=
        ((permSetStab (Set.range ι)).inv_mem hu_stab (ψ a x)).2 h1
      have h3 : ψ a ((ψ z)⁻¹ (ψ a x)) ∉ Set.range ι := fun h => (ht _).1 h h2
      simp only [Perm.mul_apply]
      exact ⟨fun h => absurd h h3, fun h => absurd h hx⟩
  have hcw : (ψ a * (ψ z)⁻¹ * ψ a) * ψ z = ψ z * (ψ a * (ψ z)⁻¹ * ψ a) :=
    perm_mul_comm_of_fix hw_in hu_out hw_stab hu_stab
  have hw7 : (ψ a * (ψ z)⁻¹ * ψ a) ^ 7 = 1 := by
    conv_lhs => rw [show ψ a * (ψ z)⁻¹ * ψ a = ψ a * (ψ z)⁻¹ * (ψ a)⁻¹ by rw [htinv]]
    rw [conj_pow, inv_pow, hu7, inv_one, mul_one, mul_inv_cancel]
  have hψy : ψ (z * a * z⁻¹ * a) = ψ z * (ψ a * (ψ z)⁻¹ * ψ a) := by
    rw [map_mul, map_mul, map_mul, map_inv]
    simp only [mul_assoc]
  have hy7 : ((z * a * z⁻¹ * a : ↥H) : MulAut V) ^ 7 = 1 := by
    have hcomm' : Commute (ψ z) (ψ a * (ψ z)⁻¹ * ψ a) := hcw.symm
    have h1 : (z * a * z⁻¹ * a) ^ 7 = 1 := hψ (by
      rw [map_pow, hψy, hcomm'.mul_pow, hu7, hw7, one_mul, map_one])
    have h2 := congrArg (fun g : ↥H => (g : MulAut V)) h1
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h2
  have hy1 : ((z * a * z⁻¹ * a : ↥H) : MulAut V) ≠ 1 := fun h => by
    have h1 : z * a * z⁻¹ * a = 1 := Subtype.ext h
    have h3 : ψ (z * a * z⁻¹ * a) = 1 := by rw [h1, map_one]
    have h2 := congrArg (fun g : Perm (Fin 16) => g (ι 0)) (hψy.symm.trans h3)
    have hw0 := hw_in (ι 0) ⟨0, rfl⟩
    simp only [Perm.mul_apply, Perm.one_apply] at h2 hw0
    rw [hw0, hz, altLift_apply_apply] at h2
    exact cycleRange_six_apply_zero (ι.injective h2)
  have hconj : (a : MulAut V) * ((z * a * z⁻¹ * a : ↥H) : MulAut V) =
      ((a : MulAut V) * z) * a * ((a : MulAut V) * z)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, hainv, mul_assoc]
  have hcardY : Nat.card (fixV (Subgroup.zpowers ((a : MulAut V) *
      ((z * a * z⁻¹ * a : ↥H) : MulAut V)))) = Nat.card (fixV (Subgroup.zpowers (a : MulAut V))) := by
    rw [hconj]
    exact card_fixV_zpowers_conj_eq _ _
  have hinf : fixV (Subgroup.zpowers (a : MulAut V)) ⊓ fixV (Subgroup.zpowers ((a : MulAut V) *
      ((z * a * z⁻¹ * a : ↥H) : MulAut V))) ≤
        fixV (Subgroup.zpowers ((z * a * z⁻¹ * a : ↥H) : MulAut V)) := by
    intro v hv
    obtain ⟨hvX, hvY⟩ := Subgroup.mem_inf.1 hv
    rw [mem_fixV_zpowers_iff] at hvX hvY ⊢
    rw [MulAut.mul_apply] at hvY
    exact (a : MulAut V).injective (hvY.trans hvX.symm)
  have hsup := card_sup_mul_card_inf (fixV (Subgroup.zpowers (a : MulAut V)))
    (fixV (Subgroup.zpowers ((a : MulAut V) * ((z * a * z⁻¹ * a : ↥H) : MulAut V))))
  have hle1 := Subgroup.card_le_card_group (fixV (Subgroup.zpowers (a : MulAut V)) ⊔
    fixV (Subgroup.zpowers ((a : MulAut V) * ((z * a * z⁻¹ * a : ↥H) : MulAut V))))
  have hle2 := Subgroup.card_le_of_le hinf
  have hV4 : Nat.card V ≤ 4 * Nat.card (fixV (Subgroup.zpowers
      ((z * a * z⁻¹ * a : ↥H) : MulAut V))) := by
    have hVpos : 0 < Nat.card V := Nat.card_pos
    rw [hcardY] at hsup
    have h1 : Nat.card V * Nat.card V ≤ Nat.card V * (4 * Nat.card ↥(fixV (Subgroup.zpowers
        (a : MulAut V)) ⊓ fixV (Subgroup.zpowers ((a : MulAut V) *
          ((z * a * z⁻¹ * a : ↥H) : MulAut V))))) := by
      nlinarith
    have h2 := Nat.le_of_mul_le_mul_left h1 hVpos
    omega
  exact hy1 (eq_one_of_pow_seven hV hy7 hV4)

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
