module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Main
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Phi2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311f2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311l

section Abstract

variable {G : Type*} [Group G]

theorem reeF4l_uniClosure_eq_top_of_cenGen [IsSimpleGroup G] {E : Subgroup G} {r : ℕ} (hE : E ≠ ⊥)
    (hZ : Subgroup.center G = ⊥) (h0 : Subgroup.closure (CFSG.RankThree.PartOne.SEITZ3.cenGen E) = ⊤)
    (hC : ∀ x ∈ E, x ≠ 1 → Subgroup.centralizer {x} ≤
      Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} ⊔
        Subgroup.centralizer (E : Set G)) :
    Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤ := by
  set S : Set G := {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1}
  set M : Subgroup G := Subgroup.closure S
  have hconj : ∀ g ∈ Subgroup.centralizer (E : Set G), ∀ k ∈ M, g * k * g⁻¹ ∈ M := by
    intro g hg k hk
    have hle : M ≤ M.comap (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.closure_le _).2 fun s hs => ?_
      obtain ⟨x, hx, hx1, hsx, n, hn⟩ := hs
      show g * s * g⁻¹ ∈ M
      have hgx : x * g = g * x := Subgroup.mem_centralizer_iff.1 hg x hx
      have hx' : g * x * g⁻¹ = x := by rw [← hgx, mul_inv_cancel_right]
      refine Subgroup.subset_closure ⟨x, hx, hx1, ?_, n, ?_⟩
      · show g * s * g⁻¹ * x = x * (g * s * g⁻¹)
        calc g * s * g⁻¹ * x = g * s * g⁻¹ * (g * x * g⁻¹) := by rw [hx']
          _ = g * (s * x) * g⁻¹ := by group
          _ = g * (x * s) * g⁻¹ := by rw [hsx.eq]
          _ = (g * x * g⁻¹) * (g * s * g⁻¹) := by group
          _ = x * (g * s * g⁻¹) := by rw [hx']
      · rw [conj_pow, hn, mul_one, mul_inv_cancel]
    exact hle hk
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (M : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨hconj g hg k, fun hk => ?_⟩
    have h1 := hconj g⁻¹ (Subgroup.inv_mem _ hg) _ hk
    rwa [show g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k by group] at h1
  have hsupN : M ⊔ Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (M : Set G) :=
    sup_le Subgroup.le_normalizer hCN
  have hN : Subgroup.normalizer (M : Set G) = ⊤ := by
    rw [eq_top_iff, ← h0, Subgroup.closure_le]
    rintro k ⟨x, hx, hx1, hkx⟩
    exact hsupN (hC x hx hx1 (Subgroup.mem_centralizer_singleton_iff.2 hkx))
  haveI : M.Normal := Subgroup.normalizer_eq_top_iff.1 hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hbot | htop
  ·
    exfalso
    have hCE : (⊤ : Subgroup G) ≤ Subgroup.centralizer (E : Set G) := by
      rw [← h0, Subgroup.closure_le]
      rintro k ⟨x, hx, hx1, hkx⟩
      have h1 := hC x hx hx1 (Subgroup.mem_centralizer_singleton_iff.2 hkx)
      rwa [hbot, bot_sup_eq] at h1
    apply hE
    rw [eq_bot_iff]
    intro y hy
    have hyZ : y ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (Subgroup.mem_centralizer_iff.1 (hCE (Subgroup.mem_top g)) y hy).symm
    rwa [hZ] at hyZ
  · exact htop

end Abstract

section Native

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.SEITZ3
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Malle.LocalAction
  CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a p : ℕ}

omit [CharP K ReeTag.F4.prime] in
theorem reeF4l_two_dvd_card_layer (hK : Nat.card K = 2 ^ (2 * a + 1)) {G : Type} [Group G]
    (h : Nonempty (G ≃* suzukiGroup a K) ∨ Nonempty (G ≃* SL2 K)) : 2 ∣ Nat.card G := by
  have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, suzuki_order hK]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow h2 two_ne_zero) _) _
  · rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    exact Dvd.dvd.mul_right h2 _

theorem reeF4l_centralizer_le_uniClosure_sup (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime)
    (hp3 : 3 < p) (P : ReePlane K a p) {x : ReeTag.F4.reeGamma K a} (hx : x ∈ P.Ψ.range) (hx1 : x ≠ 1) :
    Subgroup.centralizer {x} ≤
      Subgroup.closure {k | ∃ x ∈ P.Ψ.range, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (2 ^ n) = 1} ⊔
        Subgroup.centralizer (P.Ψ.range : Set (ReeTag.F4.reeGamma K a)) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, rfl⟩ := hx
  have hz : z ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have htorus : ∀ γ : ReeTag.F4.reeGamma K a,
      (∃ c : Fin ReeTag.F4.tag.rank → (AlgebraicClosure K)ˣ,
        reeConj P.g₀ γ = rootDiagUnit ReeTag.F4.tag c) →
      γ ∈ Subgroup.centralizer (P.Ψ.range : Set (ReeTag.F4.reeGamma K a)) := by
    rintro γ ⟨c, hc⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z', rfl⟩
    apply reeConj_injective P.g₀
    rw [map_mul, map_mul, hc, P.hΨ z', ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  set b : Fin ReeTag.F4.tag.rank → (AlgebraicClosure K)ˣ :=
    expTuple (z.1 : (AlgebraicClosure K)ˣ) (z.2 : (AlgebraicClosure K)ˣ) P.U with hb
  have hxb : reeConj P.g₀ (P.Ψ z) = rootDiagUnit ReeTag.F4.tag b := P.hΨ z
  by_cases hne : rootCharKernel b = ∅
  ·
    intro γ hγ
    refine Subgroup.mem_sup_right (htorus γ ?_)
    have hz5 : (z.1 : (AlgebraicClosure K)ˣ) ^ p = 1 ∧ (z.2 : (AlgebraicClosure K)ˣ) ^ p = 1 :=
      ⟨(mem_rootsOfUnity p _).1 z.1.2, (mem_rootsOfUnity p _).1 z.2.2⟩
    have hbp : ∀ i, b i ^ p = 1 := by
      intro i
      show ((z.1 : (AlgebraicClosure K)ˣ) ^ P.U 0 i * (z.2 : (AlgebraicClosure K)ˣ) ^ P.U 1 i) ^ p = 1
      rw [mul_pow]
      have hzp : ∀ (y : (AlgebraicClosure K)ˣ), y ^ p = 1 → ∀ n : ℤ, (y ^ n) ^ p = 1 := by
        intro y hy n
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
      rw [hzp _ hz5.1, hzp _ hz5.2, mul_one]
    have hb1 : b ≠ 1 := by
      intro h
      apply hz
      apply P.Ψinj
      apply reeConj_injective P.g₀
      rw [hxb, h, rootDiagUnit_one, map_one, map_one]
    have hγ' : γ * P.Ψ z = P.Ψ z * γ := Subgroup.mem_centralizer_singleton_iff.1 hγ
    have hcomm : reeConj P.g₀ γ * rootDiagUnit ReeTag.F4.tag b =
        rootDiagUnit ReeTag.F4.tag b * reeConj P.g₀ γ := by
      rw [← hxb, ← map_mul, ← map_mul, hγ']
    have hadj : reeConj P.g₀ γ ∈ adjointGroup ReeTag.F4.tag (AlgebraicClosure K) :=
      (reeConj_mem_twistedFixed P.D P.hg₀ P.hFg₀ γ).1
    have hordW : ¬ p ∣ Nat.card (WeylGroup ReeTag.F4.tag) := not_dvd_card_weylGroup_F4 hp hp3
    obtain ⟨t, ht, q, hq, htq⟩ := mem_torus_mul_rootSpan_of_commute hp hordW hbp hb1 (S := ∅)
      (by simp) (by simp) hne.subset hadj hcomm
    have htq' : t * q = reeConj P.g₀ γ := htq
    have h1 : rootSpan ReeTag.F4.tag (AlgebraicClosure K) (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    have h2 : q ∈ rootSpan ReeTag.F4.tag (AlgebraicClosure K) (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := hq
    rw [h1, Subgroup.mem_bot] at h2
    have ht' : t ∈ torusGroup ReeTag.F4.tag (AlgebraicClosure K) := ht
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht'
    exact ⟨l, by rw [← htq', h2, mul_one, hl]⟩
  ·
    obtain ⟨A, Sg, hAm, -, -, hsup, -, hty⟩ := plane_layer hK hp hp3 P hz hne
    obtain ⟨hq, -, -⟩ := layerType_props ha hK hty
    have h2 : 2 ∣ Nat.card Sg := reeF4l_two_dvd_card_layer hK hty
    rw [← hsup]
    refine sup_le (fun γ hγ => Subgroup.mem_sup_right (htorus γ ?_)) ?_
    · obtain ⟨c, -, hc⟩ := mem_ZGrp.1 ((hAm γ).1 hγ)
      exact ⟨c, hc.symm⟩
    · refine (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.le_closure_pow_of_quasisimple (r := 2) hq
        h2).trans
        ((Subgroup.closure_mono ?_).trans le_sup_left)
      rintro s ⟨hs, n, hn⟩
      have hsC : s ∈ Subgroup.centralizer ({P.Ψ z} : Set (ReeTag.F4.reeGamma K a)) := by
        rw [← hsup]
        exact Subgroup.mem_sup_right hs
      exact ⟨P.Ψ z, ⟨z, rfl⟩, hx1, Subgroup.mem_centralizer_singleton_iff.1 hsC, n, hn⟩

theorem reeF4l_uniClosure_native [IsSimpleGroup ↥(ReeTag.F4.reeGamma K a)] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ (2 * a + 1) + 1 ∨ p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1)
    (hC0 : ∀ F : Subgroup (ReeTag.F4.reeGamma K a), (∀ x ∈ F, x ^ p = 1) → Nat.card F = p ^ 2 →
      Subgroup.closure (cenGen F) = ⊤)
    (E₀ : Subgroup (ReeTag.F4.reeGamma K a)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (2 ^ n) = 1} = ⊤ := by
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨P, hsh⟩ : Nonempty (ReePlane K a p) ∧
      ∃ e, SylowShape p 2 e (ReeTag.F4.reeGamma K a) := by
    rcases hpq with h | h
    · have hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) + 1 := by
        have := Int.natCast_dvd_natCast.2 h
        exact_mod_cast this
      exact ⟨exists_plane_phi2 hK hp hp3 hmM, _, sylowShape_ree_phi2 hK hp hp5 h⟩
    · have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine ⟨?_, _, sylowShape_ree_phi4 hK hp hp5 h⟩
      rcases dvd_phi4_cases hp hp3 h with ⟨h1, -⟩ | ⟨h1, -⟩
      · have hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 := by
          have := Int.natCast_dvd_natCast.2 h1
          exact_mod_cast this
        exact exists_plane_phi4p hK hp hp3 hmM
      · have hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
          have := int_dvd_sub_add_one' hle h1
          exact_mod_cast this
        exact exists_plane_phi4m hK hp hp3 hmM
  obtain ⟨P⟩ := P
  obtain ⟨γ, hγ⟩ := exists_conj_plane hp hp2 hsh P E₀ hE₀p hE₀c
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_conj γ⁻¹ ?_
  have hE : E₀.map (MulAut.conj γ⁻¹).toMonoidHom = P.Ψ.range := by
    rw [hγ]
    exact cj_cj
  rw [hE]
  have hne : P.Ψ.range ≠ ⊥ := by
    intro h
    have hc := card_range_plane hp hp2 P
    rw [h, Subgroup.card_bot] at hc
    have : 2 ≤ p := hp.two_le
    nlinarith
  exact reeF4l_uniClosure_eq_top_of_cenGen hne (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
    (hC0 _ (pow_range_plane hp P) (card_range_plane hp hp2 P))
    (fun x hx hx1 => reeF4l_centralizer_le_uniClosure_sup ha hK hp hp3 P hx hx1)

end Native

section Catalogue

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  TauCeti CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c (UniPlaneGen UniSeitzPlanes)



theorem uniSeitzPlanes_reeF4_inner_phi24 :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ ¬ NormalizesRSubgroup d E ∧
      ∃ m : ℕ, d.1 = .reeF4 m ∧ (p ∣ 2 ^ (2 * m + 1) + 1 ∨ p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, hn, m, hm, hpq⟩
  obtain rfl : d = .reeF4 m := hm
  obtain ⟨X, _, _, _, hm1, hX, hsimple, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  haveI := hsimple
  haveI : IsSimpleGroup ↥(F4.reeGamma X m) := MulEquiv.isSimpleGroup e.symm
  haveI : Finite (ModGL F4.tag X) := finite_modGL
  haveI : Finite (F4.reeGamma X m) := Subtype.finite
  have hinj := conj_injective_of_mulEquiv e
    (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot (large_Ree_fixed_group_center_trivial m X hX))
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie ↥(F4.reeGamma X m) (.reeF4 m) := ⟨hv, ⟨e.symm⟩⟩
  have hC0 : ∀ F : Subgroup (F4.reeGamma X m), (∀ x ∈ F, x ^ p = 1) → Nat.card F = p ^ 2 →
      Subgroup.closure (CFSG.RankThree.PartOne.SEITZ3.cenGen F) = ⊤ := by
    intro F hFp hFc
    rcases hpq with h | h
    · exact reeF4_closure_cenGen_eq_top_of_phi2
        (fun _ K _ _ _ hm hK => reeF4_phi2Ambient_of_card hm K hK) hiso hp hp5 h F hFp hFc
    · exact reeF4_closure_cenGen_eq_top_of_phi4
        (fun _ K _ _ _ hm hK => CFSG.RankThree.PartOne.SEITZ12.phi4_ambient_holds hm hK) hiso hp hp5 h F hFp
        hFc
  show UniPlaneGen (LieTypeIndex.reeF4 m).characteristic E
  rw [LieTypeIndex.characteristic_reeF4]
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniPlaneGen_of_native_uniClosure
    (p := p) (r := 2) e hinj (fun E₀ h1 h2 _ => reeF4l_uniClosure_native hm1 hX hp hp5 hpq hC0 E₀ h1 h2)
    hE hc hin ?_
  rintro ⟨R, hR1, hRp, hRn⟩
  exact hn ⟨R, hR1, by rw [LieTypeIndex.characteristic_reeF4]; exact hRp, hRn⟩

theorem uniSeitzPlanes_reeF4_rest4 :
    UniSeitzPlanes fun d p E => d.1.characteristic = 2 ∧ 5 ≤ p ∧ CentralPrimeFree p d.1 ∧
      InnerPlane d p E ∧ ¬ NormalizesRSubgroup d E ∧
      (IsReeF4Index d.1 ∧ ¬ (p = 5 ∧ d.1 = LieTypeIndex.reeF4 2) ∧ ∃ m : ℕ, d.1 = .reeF4 m ∧
        (p ∣ 2 ^ (2 * m + 1) + 1 ∨ p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1)) :=
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.UniSeitzPlanes.mono
    (fun _ _ _ ⟨_, hp5, _, hin, hn, _, _, hm⟩ => ⟨hin, hp5, hn, hm⟩) uniSeitzPlanes_reeF4_inner_phi24

end Catalogue

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311l
