module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf90AE5MuModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Lab
public import CFSG.ClassicalInvolution.Q3.Q3MTAbel
public import CFSG.ClassicalInvolution.Q3.TL3T35

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.AE5Mu

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem le_normalizer_of_commutes {K J : Subgroup X} (hc : ∀ x ∈ K, ∀ y ∈ J, x * y = y * x) :
    J ≤ Subgroup.normalizer (K : Set X) := fun y hy =>
  Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun h hh => hc h hh y hy)

theorem map_comm_of_comm (I : AEIdent Φ 5) {K J : Subgroup X}
    (hc : ∀ x ∈ K, ∀ y ∈ J, x * y = y * x) :
    ∀ x ∈ (K.subgroupOf (pSpan Φ)).map I.φ, ∀ y ∈ (J.subgroupOf (pSpan Φ)).map I.φ,
      x * y = y * x := by
  rintro _ ⟨k, hk, rfl⟩ _ ⟨j, hj, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc k (Subgroup.mem_subgroupOf.mp hk) j (Subgroup.mem_subgroupOf.mp hj))

theorem eq_of_comm_labels (I : AEIdent Φ 5) {K J : Subgroup X} {α β : Finset (Fin 5)}
    {hα : α.card = 4} {hβ : β.card = 4} {b c : Bool}
    (hK : (K.subgroupOf (pSpan Φ)).map I.φ = memBar α hα b)
    (hJ : (J.subgroupOf (pSpan Φ)).map I.φ = memBar β hβ c)
    (hc : ∀ x ∈ K, ∀ y ∈ J, x * y = y * x) : α = β := by
  have hc' : ∀ x ∈ memBar α hα b, ∀ y ∈ memBar β hβ c, x * y = y * x := by
    rw [← hK, ← hJ]
    exact map_comm_of_comm I hc
  rcases eq_or_disjoint_of_comm hc' with h | hd
  · exact h
  · exfalso
    have h8 : (α ∪ β).card = 8 := by rw [Finset.card_union_of_disjoint hd, hα, hβ]
    have h5 : (α ∪ β).card ≤ 5 := by simpa using Finset.card_le_univ (α ∪ β)
    omega

section Q8

variable (hS : TwinDisc.Q8Section X Φ) (I : AEIdent Φ 5)
include hS I

theorem twin_comm {K J : Subgroup X} (hK : K ∈ Φ) (hJ : J ∈ Φ) {α : Finset (Fin 5)}
    {hα : α.card = 4} {b : Bool}
    (hlabK : (K.subgroupOf (pSpan Φ)).map I.φ = memBar α hα b)
    (hlabJ : (J.subgroupOf (pSpan Φ)).map I.φ = memBar α hα (!b)) :
    K ≠ J ∧ ∀ x ∈ K, ∀ y ∈ J, x * y = y * x := by
  have hne : K ≠ J := by
    rintro rfl
    rw [hlabK] at hlabJ
    cases b
    · exact memBar_true_ne_false (le_refl 5) α hα hlabJ.symm
    · exact memBar_true_ne_false (le_refl 5) α hα hlabJ
  refine ⟨hne, aeIdent_comm_of_map_comm hS.hyp (TwinDisc.AE5.members_twoN (le_refl 5) hS I)
    (subset_refl Φ) I (TwinDisc.AE5.ker_pGroupN hS I) hK hJ hne ?_⟩
  rw [hlabK, hlabJ]
  exact memBar_twin_comm α hα b

theorem omegaStar_subset : ∀ K ∈ Φ, omegaStarNbr Φ K ⊆ omegaNbr Φ K := by
  intro K hK J ⟨hJ, hJK, U, hU, hUJ, hUN⟩
  have h2 := TwinDisc.AE5.members_twoN (le_refl 5) hS I
  have h8 := TwinDisc.AE5.members_card8 (le_refl 5) hS I
  have hk := TwinDisc.AE5.ker_pGroupN hS I
  obtain ⟨R, -, J₀, hJ₀, hRJ₀, hUR, hcyc, hRU, h4⟩ :=
    Sec6Gen.exists_data_of_mem_USet hS.hyp hU
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card U := orderOf_eq_card_of_forall_mem_zpowers hg
  have hu : (g : X) ∈ U := g.2
  have hu2 : (g : X) * g ≠ 1 := by
    intro h
    have hd : orderOf (g : X) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    have hle := Nat.le_of_dvd (by norm_num) hd
    rw [show orderOf (g : X) = orderOf g from Subgroup.orderOf_coe g, hord] at hle
    omega
  obtain ⟨α, hα, b, hlabK⟩ := I.label K hK
  obtain ⟨β, hβ, c, hlabJ⟩ := I.label J hJ
  obtain ⟨⟨z, hz⟩, -⟩ := hS.hyp.omega1 K hK
  have hzK : I.φ ⟨z, le_pSpan hK hz.mem⟩ = zBar α hα :=
    I.map_eq_zBar (le_refl 5) hK (h8 K hK) hlabK hz
  have huJ : (g : X) ∈ J := hUJ hu
  have hxmem : I.φ ⟨(g : X), le_pSpan hJ huJ⟩ ∈ memBar β hβ c := by
    rw [← hlabJ]
    exact I.mem_map hJ huJ
  have hconj : (g : X) * z * (g : X)⁻¹ = z :=
    hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hUN hu))
  have hc : I.φ ⟨(g : X), le_pSpan hJ huJ⟩ * zBar α hα * (I.φ ⟨(g : X), le_pSpan hJ huJ⟩)⁻¹ =
      zBar α hα := by
    rw [← hzK, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hconj
  have hx2 : I.φ ⟨(g : X), le_pSpan hJ huJ⟩ * I.φ ⟨(g : X), le_pSpan hJ huJ⟩ ≠ 1 := by
    intro h
    refine hu2 (I.injOn (le_refl 5) hJ (h8 J hJ) hlabJ (J.mul_mem huJ huJ) J.one_mem ?_)
    show I.φ (⟨(g : X), le_pSpan hJ huJ⟩ * ⟨(g : X), le_pSpan hJ huJ⟩) = I.φ 1
    rw [map_mul, h, map_one]
  obtain ⟨p, rfl⟩ := exists_miss hα
  obtain ⟨q, rfl⟩ := exists_miss hβ
  have hpq : p = q := eq_of_conj_zBar_eq hxmem hx2 hc
  subst hpq
  have hcb : c = !b := by
    by_contra hcb
    have hcb' : c = b := by cases b <;> cases c <;> simp_all
    subst hcb'
    exact hJK (aeIdent_eq_of_map_eq hS.hyp h2 (subset_refl Φ) (le_refl 5) I hk hJ hK
      (hlabJ.trans hlabK.symm))
  subst hcb
  obtain ⟨hne, hcomm⟩ := twin_comm hS I hK hJ hlabK hlabJ
  exact (TC.mem_omegaNbr_iff hS.hyp h2).mpr ⟨hJ, hJK, le_normalizer_of_commutes hcomm⟩

theorem no_triangle : ∀ K ∈ Φ, ∀ J ∈ omegaNbr Φ K, ∀ L ∈ omegaNbr Φ K, L ∈ omegaNbr Φ J → False := by
  intro K hK J hJ L hL hLJ
  have h2 := TwinDisc.AE5.members_twoN (le_refl 5) hS I
  have hk := TwinDisc.AE5.ker_pGroupN hS I
  rw [TC.mem_omegaNbr_iff hS.hyp h2] at hJ hL hLJ
  obtain ⟨hJΦ, hJK, hJN⟩ := hJ
  obtain ⟨hLΦ, hLK, hLN⟩ := hL
  obtain ⟨-, hLJ', -⟩ := hLJ
  have hcJ : ∀ x ∈ K, ∀ y ∈ J, x * y = y * x := fun x hx y hy =>
    (TL4.commutes_of_le_two hS.hyp h2 hJΦ hK hJK
      ((h2 J hJΦ).to_sup_of_normal_right' (h2 K hK) hJN) le_sup_left le_sup_right y hy x hx).symm
  have hcL : ∀ x ∈ K, ∀ y ∈ L, x * y = y * x := fun x hx y hy =>
    (TL4.commutes_of_le_two hS.hyp h2 hLΦ hK hLK
      ((h2 L hLΦ).to_sup_of_normal_right' (h2 K hK) hLN) le_sup_left le_sup_right y hy x hx).symm
  obtain ⟨α, hα, b, hlabK⟩ := I.label K hK
  obtain ⟨β, hβ, c, hlabJ⟩ := I.label J hJΦ
  obtain ⟨γ, hγ, d, hlabL⟩ := I.label L hLΦ
  have hαβ : α = β := eq_of_comm_labels I hlabK hlabJ hcJ
  have hαγ : α = γ := eq_of_comm_labels I hlabK hlabL hcL
  subst hαβ hαγ
  have hcb : c ≠ b := by
    rintro rfl
    exact hJK (aeIdent_eq_of_map_eq hS.hyp h2 (subset_refl Φ) (le_refl 5) I hk hJΦ hK
      (hlabJ.trans hlabK.symm))
  have hdb : d ≠ b := by
    rintro rfl
    exact hLK (aeIdent_eq_of_map_eq hS.hyp h2 (subset_refl Φ) (le_refl 5) I hk hLΦ hK
      (hlabL.trans hlabK.symm))
  have hcd : c = d := by cases b <;> cases c <;> cases d <;> simp_all
  subst hcd
  exact hLJ' (aeIdent_eq_of_map_eq hS.hyp h2 (subset_refl Φ) (le_refl 5) I hk hLΦ hJΦ
    (hlabL.trans hlabJ.symm))

theorem exists_edge : ∃ K ∈ Φ, (omegaNbr Φ K).Nonempty := by
  have h2 := TwinDisc.AE5.members_twoN (le_refl 5) hS I
  obtain ⟨K, hK, hlabK⟩ := I.label_surj (miss 0) (card_miss 0) true
  obtain ⟨J, hJ, hlabJ⟩ := I.label_surj (miss 0) (card_miss 0) false
  obtain ⟨hne, hc⟩ := twin_comm hS I hK hJ hlabK hlabJ
  exact ⟨K, hK, J, (TC.mem_omegaNbr_iff hS.hyp h2).mpr
    ⟨hJ, hne.symm, le_normalizer_of_commutes hc⟩⟩

theorem partIHypG : Q3CL.PartIHypG Φ :=
  ⟨hS.hyp, classicalClause_of_two hS.hyp (TwinDisc.AE5.members_twoN (le_refl 5) hS I),
    hS.aEmpty⟩

theorem muIsoE4_of_mem_WSet {W : Subgroup X} (hW : W ∈ WSet Φ) : MuIsoE4 Φ W :=
  Q3MT.muIsoE4_of_shape (partIHypG hS I) hW (omegaStar_subset hS I) (no_triangle hS I)
    (exists_edge hS I)

theorem exists_W_muIsoE4 : ∃ W ∈ WSet Φ, MuIsoE4 Φ W := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨η, hη, hηinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hS.hyp S
  have hW : (⨆ U ∈ η, U) ∈ WSet Φ := ⟨η, ⟨S, hη, hηinv⟩, rfl⟩
  exact ⟨_, hW, muIsoE4_of_mem_WSet hS I hW⟩

end Q8

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.AE5Mu
