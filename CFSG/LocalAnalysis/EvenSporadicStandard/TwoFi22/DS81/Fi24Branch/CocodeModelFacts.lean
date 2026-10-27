module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeX
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelFacts

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H153
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelSz
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelStab
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5

theorem O2In_Sz' :
    O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) = img11 KSp :=
  O2In_Sz

theorem O23In_Sz_eq' :
    O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) =
      img11 KSp ⊔ Subgroup.zpowers r0Aut :=
  O23In_Sz_eq

theorem card_O23In_Sz' :
    Nat.card ↥(O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0))) = 192 :=
  card_O23In_Sz

theorem commV_img11_KSp' : Quasithin.commV (img11 KSp) = W0 :=
  commV_img11_KSp

theorem card_Ctz :
    Nat.card ↥(img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) ⊓
      centSub (Subgroup.zpowers t0)) = 2 ^ 8 * 3 * 5 :=
  card_stab_t0_Sz_eq.trans (by norm_num)

theorem card_NV :
    Nat.card ↥(img11 AutPerm ⊓ stabSub (Subgroup.closure {t0, z0})) = 2 ^ 9 * 3 * 5 :=
  card_stab_V0.trans (by norm_num)

theorem swap :
    ∃ g ∈ img11 AutPerm ⊓ stabSub (Subgroup.closure {t0, z0}), g t0 = t0 * z0 := by
  obtain ⟨g, hg, hgt⟩ := CocodeModelPair.exists_swap
  have hgS := img11_Lz_le_stab hg
  have hgz : g z0 = z0 := mem_centSub_zpowers.1 hgS.2
  exact ⟨g, ⟨hgS.1, mem_stabSub_V0_of (by rw [hgt]; exact t0_mul_z0_mem_V0)
    (by rw [hgz]; exact z0_mem_V0)⟩, hgt⟩

theorem card_P :
    Nat.card ↥(O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0))) = 2 ^ 6 := by
  rw [O2In_Sz']
  exact card_img11_KSp

theorem O2_NV :
    O2In (img11 AutPerm ⊓ stabSub (Subgroup.closure {t0, z0})) =
      O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) := by
  rw [O2In_Sz']
  exact O2In_stab_V0

theorem img11_KSp_comm {a b : MulAut W11} (ha : a ∈ img11 KSp) (hb : b ∈ img11 KSp) :
    a * b = b * a := by
  obtain ⟨c, rfl⟩ := mem_img11_KSp.1 ha
  obtain ⟨d, rfl⟩ := mem_img11_KSp.1 hb
  rw [rho_ksP_mul, rho_ksP_mul]
  exact congrArg _ (Subtype.ext (congrArg ksP (Fin.ext (Nat.xor_comm _ _))))

theorem img11_KSp_sq {a : MulAut W11} (ha : a ∈ img11 KSp) : a ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := mem_img11_KSp.1 ha
  rw [pow_two, ← map_mul,
    show (⟨ksP c, ksP_mem_autPerm c⟩ * ⟨ksP c, ksP_mem_autPerm c⟩ : ↥AutPerm) = 1 from
      Subtype.ext (ksP_mul_self c), map_one]

theorem P_comm :
    ∀ a ∈ O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)),
      ∀ b ∈ O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)), a * b = b * a := by
  intro a ha b hb
  rw [O2In_Sz'] at ha hb
  exact img11_KSp_comm ha hb

theorem P_sq :
    ∀ a ∈ O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)), a ^ 2 = 1 := by
  intro a ha
  rw [O2In_Sz'] at ha
  exact img11_KSp_sq ha

theorem lattice :
    ∀ U : Subgroup W11,
      (∀ g ∈ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0), ∀ u ∈ U, g u ∈ U) →
      U = ⊥ ∨ U = Subgroup.zpowers z0 ∨ Nat.card ↥U = 2 ^ 7 ∨ U = ⊤ := by
  intro U hU
  rcases eq_of_forall_apply_mem (fun g hg v hv => hU g (img11_Lz_le_stab hg) v hv) with
    h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (by rw [h]; exact card_W0)))
  · exact Or.inr (Or.inr (Or.inr h))

theorem P_irred :
    ∀ S : Subgroup (MulAut W11), S ≤ O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) →
      (∀ g ∈ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0), ∀ s ∈ S, g * s * g⁻¹ ∈ S) →
      S = ⊥ ∨ S = O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) := by
  intro S hS hSinv
  rw [O2In_Sz'] at hS ⊢
  by_cases h1 : S = ⊥
  · exact Or.inl h1
  · refine Or.inr (eq_of_le_img11_KSp hS h1 fun g hg => ?_)
    have hg' : g ∈ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) := img11_Lz_le_stab hg
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hSinv g hg' h hh, fun hh => ?_⟩
    have h2 := hSinv g⁻¹ (Subgroup.inv_mem _ hg') _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at h2

theorem comm_ne :
    Quasithin.commV (O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0))) ≠
      Subgroup.zpowers z0 := by
  rw [O2In_Sz', commV_img11_KSp']
  intro h
  have h1 := card_W0
  rw [h, lat_card_zpowers_z0] at h1
  norm_num at h1

theorem card_O23 :
    Nat.card ↥(O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0))) = 3 * 2 ^ 6 :=
  card_O23In_Sz'.trans (by norm_num)

theorem sup_zpowers_eq_O23
    {r : MulAut W11}
    (hr : r ∈ O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0))) (hr3 : orderOf r = 3) :
    img11 KSp ⊔ Subgroup.zpowers r =
      O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) := by
  have hKO : img11 KSp ≤ O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) := by
    rw [O23In_Sz_eq']
    exact le_sup_left
  have hle : img11 KSp ⊔ Subgroup.zpowers r ≤
      O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) :=
    sup_le hKO (Subgroup.zpowers_le.2 hr)
  have hrc : Nat.card (Subgroup.zpowers r) = 3 := by rw [Nat.card_zpowers, hr3]
  have h64 : 64 ∣ Nat.card ↥(img11 KSp ⊔ Subgroup.zpowers r) := by
    have h := Subgroup.card_dvd_of_le (le_sup_left : img11 KSp ≤ img11 KSp ⊔ Subgroup.zpowers r)
    rwa [show Nat.card ↥(img11 KSp) = 64 from card_img11_KSp] at h
  have h3 : 3 ∣ Nat.card ↥(img11 KSp ⊔ Subgroup.zpowers r) := by
    have h := Subgroup.card_dvd_of_le
      (le_sup_right : Subgroup.zpowers r ≤ img11 KSp ⊔ Subgroup.zpowers r)
    rwa [hrc] at h
  have h192 : 192 ∣ Nat.card ↥(img11 KSp ⊔ Subgroup.zpowers r) := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 64 3) h64 h3
    simpa using this
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_O23In_Sz']
  exact Nat.le_of_dvd Nat.card_pos h192

theorem r_fpf :
    ∀ r ∈ O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)), orderOf r = 3 →
      ∀ p ∈ O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)),
        r * p * r⁻¹ * p⁻¹ = 1 → p = 1 := by
  intro r hr hr3 p hp hcomm
  rw [O2In_Sz'] at hp
  have hsup := sup_zpowers_eq_O23 hr hr3
  have hρ : r0Aut ∈ img11 KSp ⊔ Subgroup.zpowers r := by
    rw [hsup, O23In_Sz_eq']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hrp : r * p = p * r := mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hcomm)
  have hC : img11 KSp ⊔ Subgroup.zpowers r ≤ Subgroup.centralizer ({p} : Set (MulAut W11)) := by
    refine sup_le (fun k hk q hq => ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      exact img11_KSp_comm hp hk
    · intro q hq
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact hrp.symm
  by_contra hp1
  have h1 : r0Aut * p = p * r0Aut := (Subgroup.mem_centralizer_iff.1 (hC hρ) p rfl).symm
  exact r0Aut_fpf hp hp1 (mul_inv_eq_iff_eq_mul.2 h1)

theorem r_E :
    ∀ r ∈ O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)), orderOf r = 3 →
      ∀ U : Subgroup W11,
        (∀ g ∈ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0), ∀ u ∈ U, g u ∈ U) →
        Nat.card ↥U = 2 ^ 7 → ∀ v : W11, r v * v⁻¹ ∈ U := by
  intro r hr _ U hU hUc v
  rw [eq_W0_of_Sz_invariant hU hUc]
  have hle : O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) ≤ moveSub W0 := by
    rw [O23In_Sz_eq']
    exact sup_le img11_KSp_le_moveSub (Subgroup.zpowers_le.2 r0Aut_mem_moveSub)
  exact hle hr v

theorem exists_A :
    ∃ A : Subgroup (MulAut W11), A ≤ img11 AutPerm ⊓ stabSub (Subgroup.closure {t0, z0}) ∧
      (∀ a ∈ A, ∀ r ∈ O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)), orderOf r = 3 →
        a * r * a⁻¹ * r⁻¹ ∈ O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0))) ∧
      ∀ U : Subgroup W11,
        (∀ g ∈ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0), ∀ u ∈ U, g u ∈ U) →
        Nat.card ↥U = 2 ^ 7 →
        HomVanishX A (O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0))) U := by
  refine ⟨Abar, Abar_le_stab, fun a ha r hr _ => ?_, fun U hU hUc => ?_⟩
  · rw [O2In_Sz']
    exact commutator_mem_img11_KSp_of_mem_O23In (Abar_le_img11_Lz ha) hr
  · rw [eq_W0_of_Sz_invariant hU hUc, O2In_Sz']
    exact homVanishX_model

theorem exists_sextet :
    ∀ U : Subgroup W11,
      (∀ g ∈ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0), ∀ u ∈ U, g u ∈ U) →
      Nat.card ↥U = 2 ^ 7 → ∃ z' ∈ U, z' ≠ z0 ∧ z' ∈ MulAction.orbit ↥(img11 AutPerm) z0 := by
  intro U hU hUc
  rw [eq_W0_of_Sz_invariant hU hUc]
  obtain ⟨φ, hφ, hφz, hφW⟩ := exists_fus
  exact ⟨φ z0, hφW, hφz, ⟨⟨φ, hφ⟩, rfl⟩⟩

theorem exists_perfect :
    ∃ Y : Subgroup (MulAut W11), Y ≤ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) ∧
      ⁅Y, Y⁆ = Y ∧ Quasithin.commV Y = ⊤ ∧ Nat.card ↥Y = 2 ^ 9 * 3 ^ 3 * 5 :=
  ⟨img11 Lz, img11_Lz_le_stab, commutator_img11_Lz, commV_img11_Lz,
    card_img11_Lz.trans (by norm_num)⟩

theorem normal_card :
    ∀ M : Subgroup (MulAut W11), M ≤ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) →
      O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) ≤ M →
      (∀ g ∈ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0), ∀ m ∈ M, g * m * g⁻¹ ∈ M) →
      Nat.card ↥M = 2 ^ 6 ∨ Nat.card ↥M = 3 * 2 ^ 6 ∨ Nat.card ↥M = 1080 * 2 ^ 6 ∨
        Nat.card ↥M = 2160 * 2 ^ 6 := by
  intro M hMS hPM hn
  rw [O2In_Sz'] at hPM
  have h := normal_card_model hMS hPM hn
  have e : (2 : ℕ) ^ 6 = 64 := by norm_num
  rw [e]
  exact h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelFacts

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

theorem cocodeX_std :
    CocodeX W11 (img11 AutPerm) CocodeModelPair.t0 CFSG.Quasithin.H.Coc24.z0 where
  card_Ctz := CocodeModelFacts.card_Ctz
  card_NV := CocodeModelFacts.card_NV
  swap := CocodeModelFacts.swap
  card_P := CocodeModelFacts.card_P
  O2_NV := CocodeModelFacts.O2_NV
  P_comm := CocodeModelFacts.P_comm
  P_sq := CocodeModelFacts.P_sq
  lattice := CocodeModelFacts.lattice
  P_irred := CocodeModelFacts.P_irred
  comm_ne := CocodeModelFacts.comm_ne
  card_O23 := CocodeModelFacts.card_O23
  r_fpf := CocodeModelFacts.r_fpf
  r_E := CocodeModelFacts.r_E
  exists_A := CocodeModelFacts.exists_A
  exists_sextet := CocodeModelFacts.exists_sextet
  exists_perfect := CocodeModelFacts.exists_perfect
  normal_card := CocodeModelFacts.normal_card

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
