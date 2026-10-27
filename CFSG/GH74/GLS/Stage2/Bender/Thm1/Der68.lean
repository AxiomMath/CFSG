module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Nilp
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der62
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der65

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Prop68

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem z_mem_normalizer_zpowers {z v : G} (hv : v ∈ Cen z) : z ∈ normalizer ((zpowers v : Subgroup G) : Set G) := by
  have hc : z * v = v * z := (Subgroup.mem_centralizer_singleton_iff.mp hv).symm
  have : Commute z v := hc
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ((this.symm.zpow_left n)).eq

theorem prime_dvd_card_Ep {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ} (hC : Ctx6 G z k S M p) {s : ℕ}
    (hs : s.Prime) (hsd : s ∣ Nat.card ↥(Ep p M)) : s ≠ 2 ∧ s ≠ p := by
  have hp := hC.prime
  have hodd : Odd (Nat.card ↥(Fm M)) := odd_card_Fm hC.hyp hC.mem
  have hdvdF : s ∣ Nat.card ↥(Fm M) := hsd.trans (Subgroup.card_dvd_of_le (Ep_le_Fm p M))
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvdF)
  · rintro rfl
    have h1 : Nat.card ↥(Ep s M) = Nat.card ↥(pPrimeCore s ↥(Fm M)) :=
      Subgroup.card_map_of_injective (Fm M).subtype_injective
    have : Fact s.Prime := ⟨hs⟩
    have h2 := pPrimeCore_coprime_card (p := s) (G := ↥(Fm M))
    rw [← h1] at h2
    exact hs.one_lt.ne' (Nat.eq_one_of_dvd_one (h2 ▸ Nat.dvd_gcd (dvd_refl s) hsd))

omit [Finite G] in
theorem sylow_image_isPGroup {s : ℕ} (E : Subgroup G) (Q : Sylow s ↥E) :
    IsPGroup s ↥((Q : Subgroup ↥E).map E.subtype) :=
  Q.isPGroup'.of_equiv ((Q : Subgroup ↥E).equivMapOfInjective E.subtype E.subtype_injective)

theorem prop6_8_of (h65 : Prop6_5) (h66 : Prop6_6) (h67 : Prop6_7) (hplane : OddNoncyclicPlane) : Prop6_8 := by
  intro G _ _ z k S M p hC
  by_cases hb : IsCyclic ↥(Ep p M) ∧ Ep p M ≤ Cen z
  · exact Or.inr hb
  left
  intro X hXF hX0 hXz
  have hp := hC.prime
  have hFM : Fm M ≤ M := Fm_le M
  have hXnil : Group.IsNilpotent ↥X := isNilpotent_of_le_Fm hXF
  have hcard1 : Nat.card ↥X ≠ 1 := fun h => hX0 (Subgroup.eq_bot_of_card_eq _ h)
  obtain ⟨r, hr, hrX⟩ := Nat.exists_prime_and_dvd hcard1
  have : Fact r.Prime := ⟨hr⟩
  let Q : Sylow r ↥X := default
  have hQn : (Q : Subgroup ↥X).Normal := Group.IsNilpotent.sylow_normal hXnil r Q
  have hQc : (Q : Subgroup ↥X).Characteristic := Sylow.characteristic_of_normal Q hQn
  set Xr : Subgroup G := (Q : Subgroup ↥X).map X.subtype with hXr
  have hXrX : Xr ≤ X := Subgroup.map_subtype_le _
  have hXr0 : Xr ≠ ⊥ := by
    intro h
    have : (Q : Subgroup ↥X) = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h
    exact Sylow.ne_bot_of_dvd_card Q hrX this
  have hXrn : normalizer (X : Set G) ≤ normalizer (Xr : Set G) :=
    le_normalizer_of_characteristic (L := X) (H := normalizer (X : Set G)) le_rfl (Q : Subgroup ↥X)
  have hXrz : z ∈ normalizer (Xr : Set G) := hXrn hXz
  have hXrp : IsPGroup r ↥Xr := sylow_image_isPGroup X Q
  have hXrF : Xr ≤ Fm M := hXrX.trans hXF
  have hXrO : Xr ≤ Op r M := le_Op_of_isPGroup_of_le_Fm hr hXrp hXrF
  suffices hXr : NF z M Xr from ⟨hXF, hX0, hXz, hXrn.trans hXr.2.2.2⟩
  by_cases hrp : r = p
  · subst hrp
    have hEnil : Group.IsNilpotent ↥(Ep r M) := isNilpotent_of_le_Fm (Ep_le_Fm r M)
    by_cases hEz : Ep r M ≤ Cen z
    ·
      have hnc : ¬ IsCyclic ↥(Ep r M) := fun hc => hb ⟨hc, hEz⟩
      obtain ⟨s, hs, Q', hQ'⟩ : ∃ s : ℕ, s.Prime ∧ ∃ Q' : Sylow s ↥(Ep r M), ¬ IsCyclic ↥Q' := by
        by_contra hcon
        push Not at hcon
        have : IsZGroup ↥(Ep r M) := ⟨fun s hs Q' => hcon s hs Q'⟩
        exact hnc inferInstance
      have : Fact s.Prime := ⟨hs⟩
      set Vs : Subgroup G := (Q' : Subgroup ↥(Ep r M)).map (Ep r M).subtype with hVs
      let eV : ↥(Q' : Subgroup ↥(Ep r M)) ≃* ↥Vs :=
        (Q' : Subgroup ↥(Ep r M)).equivMapOfInjective (Ep r M).subtype (Ep r M).subtype_injective
      have hVsE : Vs ≤ Ep r M := Subgroup.map_subtype_le _
      have hVsp : IsPGroup s ↥Vs := sylow_image_isPGroup (Ep r M) Q'
      have hVsnc : ¬ IsCyclic ↥Vs := fun hc =>
        hQ' (isCyclic_of_surjective eV.symm.toMonoidHom eV.symm.surjective)
      have hsd : s ∣ Nat.card ↥(Ep r M) := by
        by_contra hnd
        have hcop : Nat.Coprime s (Nat.card ↥(Ep r M)) := (Nat.Prime.coprime_iff_not_dvd hs).mpr hnd
        have hVs1 : Vs = ⊥ :=
          eq_bot_of_pGroup_coprime hs hVsp (hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hVsE))
        rw [hVs1] at hVsnc
        exact hVsnc inferInstance
      obtain ⟨hs2, hsp⟩ := prime_dvd_card_Ep hC hs hsd
      obtain ⟨V, hVVs, hVea, hVcard⟩ := hplane G s hs hs2 Vs hVsp hVsnc
      have hVE : V ≤ Ep r M := hVVs.trans hVsE
      have hVO : V ≤ Op s M := le_Op_of_isPGroup_of_le_Fm hs (hVsp.to_le hVVs) (hVE.trans (Ep_le_Fm r M))
      have hVC : V ≤ Cen z := hVE.trans hEz
      have hVnf : ∀ v ∈ V, v ≠ 1 → NF z M (zpowers v) := fun v hv hv1 =>
        h66 G z k S M r hC (zpowers v) (Subgroup.zpowers_le.mpr (hVE hv))
          (fun h => hv1 (Subgroup.zpowers_eq_bot.mp h)) (z_mem_normalizer_zpowers (hVC hv))
      have hEcO : Ep r M ≤ centralizer ((Op r M : Subgroup G) : Set G) := by
        have h := commute_Op_Ep r hr M
        rw [Subgroup.commutator_comm] at h
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hVcen : V ≤ centralizer (Xr : Set G) :=
        hVE.trans (hEcO.trans (Subgroup.centralizer_le (fun x hx => hXrO hx)))
      have hVn : V ⊔ zpowers z ≤ normalizer (Xr : Set G) :=
        sup_le (hVcen.trans (Subgroup.centralizer_le_normalizer _)) (Subgroup.zpowers_le.mpr hXrz)
      exact h67 G z k S M r hC s V hs (le_inf hVO hVC) hVea hVcard hVnf Xr hXrF hXr0 hVn
    ·
      obtain ⟨s, hsd, hsn⟩ : ∃ s ∈ (Nat.card ↥(Ep r M)).primeFactors,
          ¬ ((default : Sylow s ↥(Ep r M)) : Subgroup ↥(Ep r M)).map (Ep r M).subtype ≤ Cen z := by
        by_contra hcon
        push Not at hcon
        exact hEz (le_of_forall_sylow_le hcon)
      have hs : s.Prime := Nat.prime_of_mem_primeFactors hsd
      obtain ⟨hs2, hsp⟩ := prime_dvd_card_Ep hC hs (Nat.dvd_of_mem_primeFactors hsd)
      have : Fact s.Prime := ⟨hs⟩
      have hsylO : ((default : Sylow s ↥(Ep r M)) : Subgroup ↥(Ep r M)).map (Ep r M).subtype ≤ Op s M :=
        le_Op_of_isPGroup_of_le_Fm hs (sylow_image_isPGroup (Ep r M) default)
          ((Subgroup.map_subtype_le _).trans (Ep_le_Fm r M))
      have hOs : ¬ Op s M ≤ Cen z := fun h => hsn (hsylO.trans h)
      have hzO : z ∈ normalizer ((Op s M : Subgroup G) : Set G) := le_normalizer_Op s M hC.z_mem
      have hAP : ⁅Op s M, zpowers z⁆ ≤ Op s M :=
        commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzO)
      have hA0 : ⁅Op s M, zpowers z⁆ ≠ ⊥ := by
        intro h
        apply hOs
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
          (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers z)))
      have hAz : z ∈ normalizer ((⁅Op s M, zpowers z⁆ : Subgroup G) : Set G) :=
        le_normalizer_commutator_zpowers (le_normalizer_Op s M hC.z_mem) (mem_Cen_self z)
      have hAc : ⁅⁅Op s M, zpowers z⁆, zpowers z⁆ = ⁅Op s M, zpowers z⁆ :=
        commutator_zpowers_idem (A := Op s M) hC.orderOf_z hs hs2 (isPGroup_Op s hs M) hzO
      have hAE : ⁅Op s M, zpowers z⁆ ≤ Ep r M := hAP.trans (Op_le_Ep hs hr hsp M)
      have hAN : NF z M ⁅Op s M, zpowers z⁆ := h66 G z k S M r hC _ hAE hA0 hAz
      exact h65 G z k S M r hC _ s hs hAc hAP hAN Xr (hXrO.trans (Op_le_Ep hr hs (Ne.symm hsp) M))
        hXr0 hXrz
  ·
    exact h66 G z k S M p hC Xr (hXrO.trans (Op_le_Ep hr hp hrp M)) hXr0 hXrz

end Prop68

end CFSG.GH74.GLS.Stage2.Bender.Thm1
