module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Lay
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VAut
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VLU

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 (SmallL2 SmallL3Ne3 SmallU3Ne3)
open CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest
open scoped commutatorElement

theorem exists_quat_full_z {r : ℕ} (hr : 3 ≤ r) {A : Type} [Group A] [Finite A] {R : Subgroup A}
    {S : Sylow 2 R} {z : A} (hd : TightDatum R S z) (hc : TightClsR r A R S z) :
    ∃ x b : A, x ∈ sylowSet S ∧ b ∈ sylowSet S ∧ orderOf x = 2 ^ (r - 1) ∧ b * x * b⁻¹ = x⁻¹ ∧
      b * b = x ^ 2 ^ (r - 2) ∧ x ^ 2 ^ (r - 2) = z := by
  obtain ⟨x, b, hx, hb, hxo, hbx, hbb⟩ := exists_quat_full_of_datum hr hc
  refine ⟨x, b, hx, hb, hxo, hbx, hbb, ?_⟩
  have h2 : orderOf (x ^ 2 ^ (r - 2)) = 2 := by
    have h4 : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
      rw [← pow_succ']; congr 1; omega
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
      (by rw [hxo]; exact pow_dvd_pow 2 (by omega)), hxo, h4]
    exact Nat.mul_div_cancel 2 (by positivity)
  exact hd.eq_of_orderOf_eq_two (R.pow_mem (mem_sylowSet_le S hx) _) h2

section Main

theorem false_of_layer_action2 {r n : ℕ} (hr : 4 ≤ r) (hA : CIT3Below n) (hB : TightBelowR r n)
    (hList : SmallListR) (hO : NoDatumOtherR r) (h6 : ∀ m, TightLargeEdgeSR r m)
    (hL3 : SocF4L3 r) (hU3 : SocF4U3 r) {Q : Type} [Group Q] [Finite Q] (hQn : Nat.card Q < n)
    {R : Subgroup Q} {S : Sylow 2 R} {z : Q} (hd : TightDatum R S z) (hc : TightClsR r Q R S z)
    (hnO : ¬ TightInO2 z) (hE : TightEdgeless R) {Γ : Type} [Group Γ] (α : Γ →* MulAut Q)
    {𝒦 𝒩 Ĥ : Subgroup Γ} {e : Γ} (heK : e ∈ 𝒦)
    (hSe : ∀ s ∈ (S : Subgroup R).map R.subtype, α e s = s)
    (he : α e ^ 2 ^ (r - 2) = MulAut.conj z)
    (hN : ∀ a ∈ 𝒦, ∀ b ∈ 𝒦, ⁅a, b⁆ ∈ 𝒩) (hNodd : Odd (Nat.card ↥𝒩)) (hN𝒦 : 𝒩 ≤ 𝒦)
    (hKdec : ∀ k ∈ 𝒦, ∃ n ∈ 𝒩, ∃ j : ℤ, k = n * e ^ j) (hKz : ∀ k ∈ 𝒦, α k z = z)
    (hHK : ∀ h ∈ Ĥ, ∀ k ∈ 𝒦, h * k * h⁻¹ ∈ 𝒦)
    (hcov : ∀ q : Q, q * z = z * q → ∃ h ∈ Ĥ, α h = MulAut.conj q) : False := by
  classical
  obtain ⟨L, hLq, hLn, hLC⟩ := exists_normal_component hd hc hnO
  have hN2 : IsPGroup 2 ↥(Subgroup.center Q) := isPGroup_center_R hc
  have htN : z ∉ (Subgroup.center Q) := fun h => hnO ⟨(Subgroup.center Q), inferInstance, hN2, h⟩
  have hNc : (Subgroup.center Q) ≤ Subgroup.center Q := le_rfl
  have hnt : ∀ y : Q, ∀ n ∈ (Subgroup.center Q), y * z * y⁻¹ = z * n → n = 1 := by
    intro y n hn hy
    by_contra h1
    exact hd.not_edgeless_of_twin hn h1 hy hE
  have hd' := TwistQ.datum hd hN2 htN hnt
  have hc' := twistQ_clsR hd hNc hN2 htN hc
  have hnO' : ¬ TightInO2 (QuotientGroup.mk' (Subgroup.center Q) z) := fun h =>
    hnO (TwistQ.inO2_of hN2 h)
  haveI := hLn
  have hTs : IsSimpleGroup ↥(socleOf L) := isSimpleGroup_socle hLq hLC
  have hTab := exists_ne_comm_socle hLq hLC
  have hTC := centralizer_socle_eq_bot hLq hLC
  have hAn : Nat.card (Q ⧸ (Subgroup.center Q)) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _
      (QuotientGroup.mk'_surjective (Subgroup.center Q))) hQn
  have hZA : Subgroup.center (Q ⧸ (Subgroup.center Q)) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [← hTC, Subgroup.mem_centralizer_iff]
    intro g _
    exact (Subgroup.mem_center_iff.mp hx g)
  have hE' : TightEdgeless (R.map (QuotientGroup.mk' (Subgroup.center Q))) := by
    rcases (hB (Q ⧸ (Subgroup.center Q)) hAn _ _ _ hd' hc').resolve_right
      (not_goodThreeElement_of_four_le hr hd' hc'.1) with h2 | ⟨he, -⟩ | ⟨he, -⟩ | h4
    · exact absurd h2 hnO'
    · exact he
    · exact he
    · exact absurd h4 (not_tightE4_R hd' hc' hnO' hZA)
  have hT : socleOf L ≤ (MonoidHom.id (Q ⧸ (Subgroup.center Q))).range := fun x _ => ⟨x, rfl⟩
  have h4gen := twoSubgroupsFourGenerated_socle hr hA hB h6 (socleOf L) hTs hTab hTC hAn
    (MonoidHom.id (Q ⧸ (Subgroup.center Q))) Function.injective_id hT hd' hc' hnO'
  have hfam := edgelessFamily_of_embedded hr hList hO (socleOf L) hTs hTab hTC h4gen
    (MonoidHom.id (Q ⧸ (Subgroup.center Q))) Function.injective_id hT hd' hc'
  let Λ : Γ →* MulAut ↥(socleOf L) :=
    (restrictHom hTs hTab hTC).comp ((qcHom (Q := Q)).comp α)
  have hΛ : ∀ g : Γ, Λ g = restrictHom hTs hTab hTC (qcHom (α g)) := fun g => rfl
  have hz2 : z * z = 1 := by rw [← pow_two, ← hd.order, pow_orderOf_eq_one]
  have hmz : (QuotientGroup.mk z : Q ⧸ Subgroup.center Q) ≠ 1 := fun h =>
    htN ((QuotientGroup.eq_one_iff z).mp h)
  have hgC : Λ e ∈ autCentOf (socleOf L) (sylowSet (TwistQ.sylowMap (Subgroup.center Q) S)) := by
    rw [mem_autCentOf_iff]
    intro s hs
    unfold sylowSet at hs
    rw [TwistQ.sylowMap_map_subtype] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    have h1 := restrictHom_conj hTs hTab hTC (qcHom (α e)) (QuotientGroup.mk' (Subgroup.center Q) s₀)
    have h2 : qcHom (α e) (QuotientGroup.mk' (Subgroup.center Q) s₀) =
        QuotientGroup.mk' (Subgroup.center Q) s₀ := by
      rw [QuotientGroup.mk'_apply, qcHom_apply_mk, hSe s₀ hs₀]
    rw [h2, ← hΛ] at h1
    calc Λ e * MulAut.conjNormal (QuotientGroup.mk' (Subgroup.center Q) s₀)
        = Λ e * MulAut.conjNormal (QuotientGroup.mk' (Subgroup.center Q) s₀) * (Λ e)⁻¹ * Λ e := by
          group
      _ = MulAut.conjNormal (QuotientGroup.mk' (Subgroup.center Q) s₀) * Λ e := by rw [h1]
  have hNodd' : Odd (Nat.card ↥(𝒩.map Λ)) := hNodd.of_dvd_nat (Subgroup.card_map_dvd 𝒩 Λ)
  have hUN : ∀ a ∈ 𝒦.map Λ, ∀ b ∈ 𝒦.map Λ, ⁅a, b⁆ ∈ 𝒩.map Λ := by
    rintro _ ⟨k₁, hk₁, rfl⟩ _ ⟨k₂, hk₂, rfl⟩
    rw [← map_commutatorElement]
    exact Subgroup.mem_map_of_mem Λ (hN k₁ hk₁ k₂ hk₂)
  have hgn : Λ e ^ 2 ^ (r - 2) = MulAut.conjNormal (QuotientGroup.mk z : Q ⧸ Subgroup.center Q) := by
    rw [← map_pow, hΛ, map_pow α e _, he, qcHom_conj, restrictHom_conj_self]
  have hHU : ∀ h ∈ Ĥ.map Λ, ∀ u ∈ 𝒦.map Λ, h * u * h⁻¹ ∈ 𝒦.map Λ := by
    rintro _ ⟨h, hh, rfl⟩ _ ⟨k, hk, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem Λ (hHK h hh k hk)
  have hHcov : ∀ a ∈ socleOf L ⊓ Subgroup.centralizer
      ({(QuotientGroup.mk z : Q ⧸ Subgroup.center Q)} : Set (Q ⧸ Subgroup.center Q)),
      MulAut.conjNormal a ∈ Ĥ.map Λ := by
    intro a ha
    obtain ⟨-, haz⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective a
    have hcomm : (QuotientGroup.mk q : Q ⧸ Subgroup.center Q) * QuotientGroup.mk z =
        QuotientGroup.mk z * QuotientGroup.mk q :=
      Subgroup.mem_centralizer_singleton_iff.mp haz
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
    have hn_center : (q * z)⁻¹ * (z * q) ∈ Subgroup.center Q := hcomm
    have h2 : q⁻¹ * z * q⁻¹⁻¹ = z * ((q * z)⁻¹ * (z * q)) := by group
    have h3 : (q * z)⁻¹ * (z * q) = 1 := hnt q⁻¹ _ hn_center h2
    have hq : q * z = z * q := inv_mul_eq_one.mp h3
    obtain ⟨ĥ, hĥ, hαĥ⟩ := hcov q hq
    refine ⟨ĥ, hĥ, ?_⟩
    rw [hΛ, hαĥ, qcHom_conj, restrictHom_conj_self]
  have hSL : socSL (socleOf L) (QuotientGroup.mk' (Subgroup.center Q) z) ≤ Ĥ.map Λ := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := ha
    exact hHcov _ (by simpa using perfectCore_le _ ha')
  rcases (id hfam) with hL2 | hLU
  ·
    obtain ⟨x, b, hx, hb, hxo, hbx, hbb, hxz⟩ := exists_quat_full_z (show 3 ≤ r by omega) hd' hc'
    have hub : Λ e * MulAut.conjNormal b = MulAut.conjNormal b * Λ e :=
      (mem_autCentOf_iff.mp hgC) b hb
    refine l2_contra hr (socleOf L) hL2 hTC hxo hbx hbb hxz hub hgn hNodd' (Subgroup.map_mono hN𝒦)
      (Subgroup.mem_map_of_mem Λ heK) ?_ ?_ hHU hHcov
    · rintro _ ⟨k, hk, rfl⟩
      obtain ⟨n₀, hn₀, j, hkj⟩ := hKdec k hk
      exact ⟨Λ n₀, Subgroup.mem_map_of_mem Λ hn₀, j, by rw [hkj, map_mul, map_zpow]⟩
    · rintro _ ⟨k, hk, rfl⟩
      have h1 := restrictHom_conj hTs hTab hTC (qcHom (α k)) (QuotientGroup.mk z)
      rw [qcHom_apply_mk, hKz k hk, ← hΛ] at h1
      calc Λ k * MulAut.conjNormal (QuotientGroup.mk z : Q ⧸ Subgroup.center Q)
          = Λ k * MulAut.conjNormal (QuotientGroup.mk z : Q ⧸ Subgroup.center Q) * (Λ k)⁻¹ * Λ k := by
            group
        _ = MulAut.conjNormal (QuotientGroup.mk z : Q ⧸ Subgroup.center Q) * Λ k := by rw [h1]
  ·
    set g : MulAut ↥(socleOf L) := Λ e ^ 2 ^ (r - 4) with hgdef
    have hg4 : g ^ 4 = MulAut.conjNormal (QuotientGroup.mk z : Q ⧸ Subgroup.center Q) := by
      rw [hgdef, ← pow_mul, show 2 ^ (r - 4) * 4 = 2 ^ (r - 2) by
        rw [show r - 2 = (r - 4) + 2 by omega, pow_add]; norm_num]
      exact hgn
    have hg8 : orderOf g = 8 := by
      have h1 : ¬ g ^ 2 ^ 2 = 1 := by
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hg4]
        exact fun h => hmz (conjNormal_eq_one hTC h)
      have h2 : g ^ 2 ^ (2 + 1) = 1 := by
        rw [show (2 : ℕ) ^ (2 + 1) = 4 * 2 by norm_num, pow_mul, hg4, ← map_pow,
          ← QuotientGroup.mk_pow, pow_two, hz2, QuotientGroup.mk_one, map_one]
      have := orderOf_eq_prime_pow (p := 2) (n := 2) h1 h2
      simpa using this
    exact false_of_aut_core_lu hL3 hU3 hr (socleOf L) hTs hTab hTC hfam hd' hc' hnO' hE' hLU hNodd'
      hUN (Submonoid.pow_mem _ (Subgroup.mem_map_of_mem Λ heK) _) (Subgroup.pow_mem _ hgC _) hg8
      hHU hSL

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
