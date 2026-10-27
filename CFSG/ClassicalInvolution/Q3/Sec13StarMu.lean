module

public import CFSG.ClassicalInvolution.Q3.Sec13StarHyp
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.TL3T22

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {Ω : Set (Subgroup G)} (h : StarHyp Ω)
include h

theorem partIHyp : Q3T8.Asc77.PartIHyp Ω :=
  ⟨h.thmD.hyp, classicalClause_of_two h.thmD.hyp h.thmD.two, h.thmD.aEmpty⟩

private theorem isSylow2In_self {K : Subgroup G} (hK : K ∈ Ω) : IsSylow2In K K :=
  ⟨le_rfl, h.thmD.two K hK, fun _ hVK _ hKV => le_antisymm hVK hKV⟩

theorem mem_dSet_iff {W R : Subgroup G} :
    R ∈ DSet Ω W ↔ R ∈ Ω ∧ R ≤ Subgroup.normalizer (W : Set G) := by
  refine ⟨fun ⟨hR, hRN⟩ => ⟨?_, hRN⟩,
    fun ⟨hR, hRN⟩ => ⟨TC.mem_RSet_of_isPGroup hR (h.thmD.two R hR), hRN⟩⟩
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  rwa [← hRJ.2.2 J le_rfl (h.thmD.two J hJ) hRJ.1]

theorem mem_dstarComp_of_mem_dSet {W : Subgroup G} (hW : W ∈ WSet Ω) {K R : Subgroup G}
    (hK : K ∈ DSet Ω W) (hR : R ∈ DSet Ω W) : R ∈ dstarComp Ω K := by
  by_cases hKR : K = R
  · subst hKR
    exact Relation.ReflTransGen.refl
  have hKΩ := (h.mem_dSet_iff.mp hK).1
  have hRΩ := (h.mem_dSet_iff.mp hR).1
  exact Relation.ReflTransGen.single ⟨hRΩ, Or.inl (Q3CL.Thompson.mem_omegaStarNbr_of_inf_W
    h.thmD.hyp hW hKΩ hRΩ hKR hK hR (h.isSylow2In_self hKΩ) (h.isSylow2In_self hRΩ)).1⟩

theorem dbarConnected_of_move {W : Subgroup G} (hW : W ∈ WSet Ω) {t : G}
    (htW : t ∈ Subgroup.normalizer (W : Set G)) (ht2 : t * t = 1)
    (hmove : ∀ R ∈ DSet Ω W, conjSub t R ≠ R) : DbarConnected Ω W := by
  by_contra hnc
  obtain ⟨R, hR, hfix⟩ := Q3T8.Asc77.l7_12_proved G Ω h.partIHyp W hW hnc t htW ht2
  exact hmove R hR hfix

open CFSG.ClassicalInvolution.Asc77.Thompson in
theorem muIsoE4_of_dSet {S : Sylow 2 G} {η : Set (Subgroup G)} (hη : η ∈ etaG Ω)
    (hηS : ∀ V ∈ η, V ≤ (S : Subgroup G)) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω)
    (hKS : K ≤ (S : Subgroup G)) (hK'S : K' ≤ (S : Subgroup G)) (hne : K ≠ K')
    (hD : DSet Ω (⨆ V ∈ η, V) = {K, K'}) : MuIsoE4 Ω (⨆ V ∈ η, V) := by
  set W := ⨆ V ∈ η, V
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hW : W ∈ WSet Ω := ⟨η, hη, rfl⟩
  have hW2 : IsPGroup 2 W := S.isPGroup'.to_le (iSup₂_le hηS)
  have hKD : K ∈ DSet Ω W := by
    rw [hD]
    exact Set.mem_insert K {K'}
  have hK'D : K' ∈ DSet Ω W := by
    rw [hD]
    exact Set.mem_insert_of_mem K rfl
  have hcomm := Q3CP.l67Gen G Ω hΩ S K (TC.mem_RSet_of_isPGroup hK (h.thmD.two K hK)) K'
    (TC.mem_RSet_of_isPGroup hK' (h.thmD.two K' hK')) hKS hK'S hne
  have hMG : MGrp Ω W = K ⊔ K' := by
    show (⨆ R ∈ DSet Ω W, R) = K ⊔ K'
    rw [hD, iSup_insert, iSup_singleton]
  have hKK' : K ≤ Subgroup.normalizer (K' : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm)
  have hMN : K ⊔ K' ≤ Subgroup.normalizer (OCW W : Set G) :=
    (sup_le hKD.2 hK'D.2).trans (normalizer_le_normalizer_OCW W)
  have hdec : ∀ m ∈ MGrp Ω W ⊔ OCW W, ∃ x ∈ K, ∃ y ∈ K', ∃ c ∈ OCW W, x * y * c = m := by
    intro m hm
    rw [hMG, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hMN] at hm
    obtain ⟨xy, hxy, c, hc, rfl⟩ := Set.mem_mul.mp hm
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKK'] at hxy
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hxy
    exact ⟨x, hx, y, hy, c, hc, rfl⟩
  obtain ⟨k, hk, hkW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hKD
  obtain ⟨k', hk', hk'W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hK'D
  have hkN := hKD.2 hk
  have hk'N := hK'D.2 hk'
  have himg : ∀ {R : Subgroup G}, R ∈ DSet Ω W → ∀ {r x : G}, r ∈ R → r ∉ W → x ∈ R →
      piG W x = 1 ∨ piG W x = piG W r := by
    intro R hR r x hr hrW hx
    by_cases hxW : x ∈ W
    · exact Or.inl (piG_of_mem_sup (Subgroup.mem_sup_left hxW))
    · exact Or.inr (Q3CL.Thompson.D_piG_eq hΩ hW hR hx hr hxW hrW)
  have hsq : ∀ {R : Subgroup G}, R ∈ DSet Ω W → ∀ {r : G}, r ∈ R → piG W r * piG W r = 1 := by
    intro R hR r hr
    rw [← piG_mul (hR.2 hr) (hR.2 hr)]
    exact piG_of_mem_sup (Subgroup.mem_sup_left (Q3CL.Thompson.D_sq_mem hΩ hW hR hr))
  have hne1 : ∀ {R : Subgroup G}, R ∈ DSet Ω W → ∀ {r : G}, r ∈ R → r ∉ W → piG W r ≠ 1 :=
    fun hR _ hr hrW h1 => D_not_mem_sup hW hR hr hrW ((piG_eq_one_iff (hR.2 hr)).mp h1)
  have hk2 := hsq hKD hk
  have hk'2 := hsq hK'D hk'
  have hk1 := hne1 hKD hk hkW
  have hk'1 := hne1 hK'D hk' hk'W
  have hkk' : piG W k * piG W k' = piG W k' * piG W k := by
    refine (piG_comm_iff hkN hk'N).mpr ?_
    have h1 : k * k' * k⁻¹ * k'⁻¹ = 1 := by
      rw [hcomm k hk k' hk']
      group
    rw [h1]
    exact Subgroup.one_mem _
  have hne' : piG W k ≠ piG W k' := by
    intro heq
    have hw : k⁻¹ * k' ∈ W := mem_of_isPGroup_of_mem_sup_OCW hW2
      (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr ((S : Subgroup G).mul_mem
        ((S : Subgroup G).inv_mem (hKS hk)) (hK'S hk')))) ((piG_eq_iff hkN hk'N).mp heq)
    obtain ⟨-, -, hcyc, h4, -⟩ :=
      Q3CL.Thompson.inf_W_of_mem_D hΩ hW hKD hK (h.isSylow2In_self hK)
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(K ⊓ W))
    have hgo : orderOf (g : G) = Nat.card ↥(K ⊓ W) := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
    have hgK : (g : G) ∈ K := g.2.1
    have hgW : (g : G) ∈ W := g.2.2
    have hwg := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW _ (W.inv_mem hw) _ hgW
    have hkg : k * g = g * k := by
      calc k * g = k' * ((k⁻¹ * k')⁻¹ * g) := by group
        _ = k' * (g * (k⁻¹ * k')⁻¹) := by rw [hwg]
        _ = (k' * g) * (k⁻¹ * k')⁻¹ := by group
        _ = (g * k') * (k⁻¹ * k')⁻¹ := by rw [hcomm _ hgK _ hk']
        _ = g * k := by group
    have hKc := Q3CL.Thompson.le_centralizer_of_mem hΩ hW hKD hk hkW hgW hkg
    have hgg := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hKD.1).sq_eq_one_of_central hgK
      fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hKc hy)).symm
    have h2 : orderOf (g : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hkmem : piG W k ∈ muGroup Ω W :=
    piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hKD hk))
  have hk'mem : piG W k' ∈ muGroup Ω W :=
    piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hK'D hk'))
  have hcoe : ((muGroup Ω W : Subgroup (NQuot (W ⊔ OCW W))) : Set (NQuot (W ⊔ OCW W))) =
      {1, piG W k, piG W k', piG W k * piG W k'} := by
    ext q
    rw [SetLike.mem_coe]
    constructor
    · intro hq
      obtain ⟨m, hm, rfl⟩ := mem_muGroup_iff.mp hq
      obtain ⟨x, hx, y, hy, c, hc, rfl⟩ := hdec m hm
      have hxN := hKD.2 hx
      have hyN := hK'D.2 hy
      rw [piG_mul (Subgroup.mul_mem _ hxN hyN) (OCW_le_normalizer W hc), piG_mul hxN hyN,
        piG_of_mem_sup (Subgroup.mem_sup_right hc), mul_one]
      rcases himg hKD hk hkW hx with hx' | hx' <;> rcases himg hK'D hk' hk'W hy with hy' | hy' <;>
        simp [hx', hy']
    · rintro (rfl | rfl | rfl | rfl)
      · exact Subgroup.one_mem _
      · exact hkmem
      · exact hk'mem
      · exact Subgroup.mul_mem _ hkmem hk'mem
  have hcard : Nat.card ↥(muGroup Ω W) = 4 := by
    rw [← SetLike.coe_sort_coe, hcoe, Nat.card_coe_set_eq]
    exact Set.ncard_eq_four.mpr ⟨_, _, _, _, hk1.symm, hk'1.symm,
      fun h1 => hne' (mul_left_cancel (hk2.trans h1)), hne',
      fun h1 => hk'1 (mul_left_cancel ((mul_one _).trans h1)).symm,
      fun h1 => hk1 (mul_right_cancel ((one_mul _).trans h1)).symm, rfl⟩
  have hexp : ∀ q : ↥(muGroup Ω W), q * q = 1 := by
    intro q
    have hq : (q : NQuot (W ⊔ OCW W)) ∈
        ((muGroup Ω W : Subgroup (NQuot (W ⊔ OCW W))) : Set (NQuot (W ⊔ OCW W))) := q.2
    rw [hcoe] at hq
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    rcases hq with hq | hq | hq | hq <;> rw [hq]
    · exact mul_one 1
    · exact hk2
    · exact hk'2
    · calc piG W k * piG W k' * (piG W k * piG W k')
          = piG W k * (piG W k' * piG W k) * piG W k' := by group
        _ = (piG W k * piG W k) * (piG W k' * piG W k') := by rw [← hkk']; group
        _ = 1 := by rw [hk2, hk'2, one_mul]
  have : Nontrivial ↥(muGroup Ω W) :=
    ⟨⟨⟨_, hkmem⟩, 1, fun h1 => hk1 (congrArg Subtype.val h1)⟩⟩
  have : IsKleinFour ↥(muGroup Ω W) :=
    ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun q hq =>
      orderOf_eq_prime (by rw [pow_two]; exact hexp q) hq⟩
  exact IsKleinFour.nonempty_mulEquiv

end StarHyp

end CFSG.ClassicalInvolution.Q3.Sec13
