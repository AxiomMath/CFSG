module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOne
public import CFSG.Sporadic.SmallOddCore.J2
public import Certificates.Certificate13509

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Monster.B.Co2 CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.Open CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.RankThree.PartOne.StrongP
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.Certificates.Native

section Outer


theorem j2_outer_not_dvd {σ : MulAut ↥j2P} (hσ2 : σ ^ 2 = 1) (hσ : σ ∉ innerAut ↥j2P)
    {H : Subgroup ↥j2P} (hH : ∀ x ∈ H, σ x = x) : ¬ 3 ^ 3 ∣ Nat.card H := by
  obtain ⟨e, he, hmap, -⟩ := ctuc_j2_full_automorphism_permutation_model
  obtain ⟨-, -, -, hrows, hcover, -, hlist, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨t, rfl⟩ := e.surjective σ
  have htP : (t : Equiv.Perm (Fin 315)) ∉ j2P := by
    intro h
    apply hσ
    have : e t ∈ (j2P.subgroupOf j2R).map e.toMonoidHom :=
      ⟨t, Subgroup.mem_subgroupOf.2 h, rfl⟩
    rw [hmap] at this
    exact this
  have ht2 : t ^ 2 = 1 := e.injective (by rw [map_pow, hσ2, map_one])
  have ht2' : (t : Equiv.Perm (Fin 315)) ^ 2 = 1 := congrArg Subtype.val ht2
  have ht1 : (t : Equiv.Perm (Fin 315)) ≠ 1 := fun h => htP (h ▸ j2P.one_mem)
  have hto : orderOf (t : Equiv.Perm (Fin 315)) = 2 := orderOf_eq_prime ht2' ht1
  obtain ⟨r, hr, g, hg, hteq⟩ := hcover _ t.2 hto
  obtain ⟨-, -, hout, -, hcard, -⟩ := hrows r hr
  have hrep : tp 315 r.rep ∉ j2P := by
    intro h
    apply htP
    rw [hteq]
    exact j2P.mul_mem (j2P.mul_mem hg h) (j2P.inv_mem hg)
  have hro : r.outer = true := hout.2 hrep
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      [(true, 1800, 336), (false, 2520, 240), (false, 315, 1920)] := by
    rw [← hlist]
    exact List.mem_map_of_mem hr
  have hc336 : r.centOrder = 336 := by
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h
    · exact h.2.2
    · rw [hro] at h
      exact absurd h.1 (by simp)
    · rw [hro] at h
      exact absurd h.1 (by simp)
  have hcardt : Nat.card ↥(j2P ⊓ Subgroup.centralizer ({(t : Equiv.Perm (Fin 315))} :
      Set (Equiv.Perm (Fin 315)))) = 336 := by
    rw [hteq, inf_centralizer_conj j2P hg,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard, hc336]
  have hle : H.map j2P.subtype ≤ j2P ⊓ Subgroup.centralizer ({(t : Equiv.Perm (Fin 315))} :
      Set (Equiv.Perm (Fin 315))) := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := congrArg Subtype.val (hH x hx)
    rw [he t x] at h1
    have h2 : (t : Equiv.Perm (Fin 315)) * x * (t : Equiv.Perm (Fin 315))⁻¹ = x := h1
    have hcomm : (t : Equiv.Perm (Fin 315)) * x = x * t := by
      have := congrArg (· * (t : Equiv.Perm (Fin 315))) h2
      simpa [mul_assoc] using this
    exact hcomm.symm
  intro hdvd
  have h3 : Nat.card H ∣ 336 := by
    rw [← hcardt]
    calc Nat.card H = Nat.card (H.map j2P.subtype) :=
          (Subgroup.card_map_of_injective j2P.subtype_injective).symm
      _ ∣ _ := Subgroup.card_dvd_of_le hle
  have := hdvd.trans h3
  norm_num at this

end Outer

theorem balance_J2_three :
    IsLocallyBalancedAbs 3 2 NativeSporadic.J2 := by
  refine IsLocallyBalancedAbs.of_mulEquiv j2PermEquiv ?_
  have h := Certificates.certificate13509
  simp only [j2ThreeCheck, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, hvA⟩, hvB⟩, hsz⟩, hcent⟩, hord⟩, hne⟩, hclass⟩ := h
  have hA := rep_of_validA hvA
  have hB := rep_of_validA hvB
  have hQ : Subgroup.closure {permOfArr 315 j2ThreeA, permOfArr 315 j2ThreeB} = j2P := rfl
  have hn : 1 ≤ 315 := by norm_num
  have hk : 2 ≤ j2ThreeArrs.size := by simp [j2ThreeArrs]
  have hb : j2ThreeBase.Nodup := by decide
  obtain ⟨z, hz, hzo, h27, hO⟩ := gfr3_kit hn (S := j2ThreeArrs) hk (bs := j2ThreeBase) hb hA hB
    j2P hQ h1 (rels := j2ThreeRels) (gs := j2ThreeGens) (ps := j2ThreeKeys)
    (c := j2ThreeCert ()) (N := 1080) (e := 3) (f := 1) (by decide) (by decide)
    hcent hord hne (by norm_num) hclass
  have hcard : Nat.card ↥j2P = 604800 := by
    have := card_closure_two_of_chainOK hn hk hb hA hB h1
    have hsz' : rawOrbitSizes 315 j2ThreeArrs (List.map Fin.val j2ThreeBase).toArray =
        [315, 10, 16, 4, 3, 1, 1] := hsz
    rw [hQ, hsz'] at this
    rw [this]
    norm_num
  have hnc : HasNoncommPair 3 ↥j2P :=
    HasNoncommPair.map j2PermEquiv.toMonoidHom j2PermEquiv.injective pair_J2_three
  have hsimple : IsSimpleGroup ↥j2P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 j2PermEquiv.symm
  have hcen : Subgroup.center ↥j2P = ⊥ := by
    obtain ⟨x, y, -, -, hxy, -⟩ := hnc
    exact center_eq_bot_of_isSimpleGroup ⟨x, y, hxy⟩
  have hzo' : orderOf (⟨z, hz⟩ : ↥j2P) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hzo
  have hgood : GFR3Good ↥j2P ⟨z, hz⟩ := by
    refine ⟨hO, fun σ hσ2 hσ => ?_⟩
    by_contra hno
    push Not at hno
    exact j2_outer_not_dvd hσ2 hσ (H := Subgroup.centralizer ({(⟨z, hz⟩ : ↥j2P)} : Set ↥j2P))
      (fun x hx => hno x (Subgroup.mem_centralizer_singleton_iff.1 hx).symm) h27
  exact gfr3_locallyBalanced_of_good hcen j2_outer_card_le
    (gfr3_exists_good_of_sylow hnc (by rw [hcard]; norm_num) hzo' h27 hgood)

end CFSG.HardMathSupport.Solomon.Coordinator
