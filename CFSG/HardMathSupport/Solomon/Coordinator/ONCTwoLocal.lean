module

public import CFSG.HardMathSupport.Solomon.Coordinator.ONCTwoLocalB

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple Subgroup
open scoped commutatorElement

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


theorem mem_normalizer_map_conj {G : Type*} [Group G] {S : Subgroup G} {w : G}
    (hw : w ∈ normalizer (S : Set G)) (m : G) :
    m * w * m⁻¹ ∈ normalizer ((S.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hw ⊢
  intro t
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  have h := hw (m⁻¹ * t * m)
  have e : m⁻¹ * (m * w * m⁻¹ * t * (m * w * m⁻¹)⁻¹) * m = w * (m⁻¹ * t * m) * w⁻¹ := by group
  rw [e]
  exact h

theorem exists_two_group_normalized_of_card_81 {E : Subgroup GM} (hz : zG ∈ E)
    (hcard : Nat.card E = 81) :
    ∃ T : Subgroup GM, T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ normalizer (T : Set GM) := by
  have hp3 : IsPGroup 3 E := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  obtain ⟨P', hEP'⟩ := hp3.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq GM P' P0Syl
  have hconj : ∀ e ∈ E, h * e * h⁻¹ ∈ P0G := by
    intro e he
    have h1 : (MulAut.conj h).toMonoidHom e ∈ P0G := by
      rw [← P0Syl_coe, ← hh, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact mem_map_of_mem _ (hEP' he)
    simpa [MulAut.conj_apply] using h1
  set E0 : Subgroup GM := E.map (MulAut.conj h).toMonoidHom with hE0
  have hE0P : E0 ≤ P0G := by
    rintro _ ⟨e, he, rfl⟩
    exact hconj e he
  have hz0 : zG ∈ E0 := ⟨zG, hz, by
    show h * zG * h⁻¹ = zG
    rw [← pow_one zG, conj_zG_pow]⟩
  have hcard0 : Nat.card E0 = 81 := by
    rw [hE0, Subgroup.card_map_of_injective (MulAut.conj h).injective, hcard]
  obtain ⟨a, ha, haz, hcomm⟩ := exists_centralizer_of_card_81 hE0P hz0 hcard0
  obtain ⟨g, hgn, hgc⟩ := exists_g_centralizer ha haz
  obtain ⟨S, hS0, hS2, hSN⟩ := exists_two_group_normalized_by_centralizer_x1
  refine ⟨S.map (MulAut.conj (h⁻¹ * g)).toMonoidHom, ?_, hS2.map _, fun e he => ?_⟩
  · intro hbot
    exact hS0 ((Subgroup.map_eq_bot_iff_of_injective S (MulAut.conj (h⁻¹ * g)).injective).1 hbot)
  · have hw0 : h * e * h⁻¹ ∈ E0 := ⟨e, he, rfl⟩
    have hw0P := hE0P hw0
    have hw1P := hgn _ hw0P
    have hw1 := hgc (h * e * h⁻¹) (hcomm _ hw0)
    have hN := hSN _ hw1P hw1
    have key := mem_normalizer_map_conj hN (h⁻¹ * g)
    have e1 : (h⁻¹ * g) * (g⁻¹ * (h * e * h⁻¹) * g) * (h⁻¹ * g)⁻¹ = e := by group
    rwa [e1] at key

theorem exists_two_group_of_surj {K : Type} [Group K] (π : GM →* K) (hπ : Function.Surjective π)
    (hker : π.ker = zpowers zG) {E : Subgroup K} (hE : Nat.card E = 27) :
    ∃ T : Subgroup K, T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ normalizer (T : Set K) := by
  have : Finite K := Finite.of_surjective π hπ
  have hzcard : Nat.card (zpowers zG) = 3 := by
    rw [Nat.card_zpowers]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime relG.xcube relG.x1
  have hGK : Nat.card GM = 3 * Nat.card K := by
    have := Subgroup.card_ker_mul_card_of_surjective hπ
    rw [hker, hzcard] at this
    exact this.symm
  set Ê : Subgroup GM := E.comap π with hÊ
  have hcard : Nat.card Ê = 81 := by
    have h1 := Subgroup.card_mul_index Ê
    have h2 := Subgroup.card_mul_index E
    have h3 : Ê.index = E.index := Subgroup.index_comap_of_surjective E hπ
    rw [h3, hGK] at h1
    have hi : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
    have h2' : 27 * E.index = Nat.card K := by rw [← hE]; exact h2
    rw [h1]
    omega
  have hzÊ : zG ∈ Ê := by
    show π zG ∈ E
    have : zG ∈ π.ker := hker ▸ mem_zpowers zG
    rw [MonoidHom.mem_ker] at this
    rw [this]
    exact E.one_mem
  obtain ⟨T, hT0, hT2, hTN⟩ := exists_two_group_normalized_of_card_81 hzÊ hcard
  refine ⟨T.map π, ?_, hT2.map π, fun e he => ?_⟩
  · intro hbot
    apply hT0
    have hle : T ≤ zpowers zG := hker ▸ (Subgroup.map_eq_bot_iff T).1 hbot
    rw [eq_bot_iff]
    intro t ht
    rw [mem_bot]
    obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
    have h2 : t ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have hd2 := orderOf_dvd_of_pow_eq_one h2
    have hd3 : orderOf t ∣ 3 := hzcard ▸ Subgroup.orderOf_dvd_natCard (zpowers zG) (hle ht)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left n
      (by norm_num : Nat.Coprime 2 3)) hd2 hd3)
  · obtain ⟨ê, rfl⟩ := hπ e
    have hê : ê ∈ Ê := he
    have hn := hTN hê
    have one : ∀ x ∈ normalizer (T : Set GM), ∀ t ∈ T.map π, π x * t * (π x)⁻¹ ∈ T.map π := by
      intro x hx t ht
      obtain ⟨s, hs, rfl⟩ := ht
      exact ⟨x * s * x⁻¹, (mem_normalizer_iff.1 hx s).1 hs, by simp [map_mul, map_inv]⟩
    rw [mem_normalizer_iff]
    intro t
    constructor
    · exact fun ht => one ê hn t ht
    · intro ht
      have := one ê⁻¹ (inv_mem hn) _ ht
      simpa [map_inv, mul_assoc] using this

theorem input20_29_holds : LocalBalance.Lemma59Ns.Input20_29 := by
  intro K _ _ ⟨eK⟩ E _ hE
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b : CFSG.Blueprint.NativeSporadic.ON ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b0
  let e : CFSG.ONSchreier.Pv ≃* K := (CFSG.ONSchreier.onEquivPv.symm.trans b).trans eK.symm
  let π : GM →* K := e.toMonoidHom.comp phiM
  have hπ : Function.Surjective π := e.surjective.comp phiM_surjective
  have hker : π.ker = zpowers zG := by
    rw [← ker_phiM]
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show e (phiM g) = 1 ↔ phiM g = 1
    exact MulEquiv.map_eq_one_iff e
  exact exists_two_group_of_surj π hπ hker (by rw [hE]; norm_num)

end CFSG.HardMathSupport.Solomon.Coordinator
