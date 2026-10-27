module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81E6f
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81E6Tr

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace E6

theorem commutator_self_of_isPerfect {G : Type*} [Group G] {L : Subgroup G}
    (hL : Group.IsPerfect L) : ⁅L, L⁆ = L := by
  have h := congrArg (Subgroup.map L.subtype) hL.commutator_eq_top
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

variable {G : Type} [Group G] [Finite G]

theorem rank_le_of_closure {P : Subgroup G} {s : Finset G} (hs : closure (s : Set G) = P) :
    Group.rank ↥P ≤ s.card := by
  rw [← Subgroup.rank_congr hs]
  exact Subgroup.rank_closure_finset_le_card s

theorem exists_finset_of_rank_le (P : Subgroup G) {n : ℕ} (h : Group.rank ↥P ≤ n) :
    ∃ s : Finset G, s.card ≤ n ∧ closure (s : Set G) = P := by
  obtain ⟨S, hS, hStop⟩ := Group.rank_spec ↥P
  refine ⟨S.map ⟨P.subtype, P.subtype_injective⟩, by rw [Finset.card_map, hS]; exact h, ?_⟩
  rw [Finset.coe_map, Function.Embedding.coeFn_mk, ← MonoidHom.map_closure, hStop,
    ← MonoidHom.range_eq_map, range_subtype]

end E6

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem e6_commutator_K : ⁅h.K, h.K⁆ = h.K :=
  E6.commutator_self_of_isPerfect
    (B5a.isPerfect_of_isPComponent_subgroupOf h.isPComponent_K.1 h.isPComponent_K.2)

theorem e6_commutator_J : ⁅h.J, h.J⁆ = h.J :=
  E6.commutator_self_of_isPerfect (B5a.isPerfect_of_isPComponent_subgroupOf h.J_le h.isPComponent_J)

theorem J_le_fstar : h.J ≤ generalizedFitting H := by
  rw [h.generalizedFitting_simple.1]
  exact B5a.le_conjClosure _ _

include h in
theorem fstar_le_of_cyclic (N : Subgroup H) [N.Normal] (hN : IsCyclic (H ⧸ N)) :
    generalizedFitting H ≤ N := by
  rw [h.generalizedFitting_simple.1]
  refine B5a.conjClosure_le (E6.le_of_perfect h.e6_commutator_J ‹_› hN) fun g _ => ?_
  rw [normalizer_eq_top N]
  exact mem_top g

variable {h}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

theorem normalizer_B_eq : normalizer (h.B : Set H) = centralizer ({d.b} : Set H) := by
  apply le_antisymm
  · intro w hw
    rw [mem_centralizer_iff]
    rintro _ rfl
    exact (d.comm_b_of_mem_W hw).symm
  · rw [d.B_eq]
    refine Seven.le_normalizer_of_commute fun x hx y hy => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have hyb : Commute d.b y := mem_centralizer_iff.mp hy d.b rfl
    exact (hyb.zpow_left k).eq

theorem a_mem_fstar (I : In81) (F : d.Facts) : h.a ∈ generalizedFitting H := by
  obtain ⟨c, hc⟩ := d.exists_conj_a_z I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F
  have hz : d.z ∈ generalizedFitting H := h.J_le_fstar (mem_inf.mp d.z_D).2
  have ha : h.a = c * d.z * c⁻¹ := by rw [← hc]; group
  rw [ha]
  exact CFSG.LocalCores.generalized_fitting_characteristic.2.conj_mem _ hz c

theorem M3_le_of_cyclic (I : In81) (F : d.Facts) (N : Subgroup H) [N.Normal]
    (hN : IsCyclic (H ⧸ N)) : h.M3 ≤ N := by
  obtain ⟨c, hc⟩ := d.exists_conj_a_z I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F
  have hzN : d.z ∈ N := E6.le_of_perfect h.e6_commutator_J ‹_› hN (mem_inf.mp d.z_D).2
  have ha : h.a = c * d.z * c⁻¹ := by rw [← hc]; group
  refine sup_le (E6.le_of_perfect h.e6_commutator_K ‹_› hN) (zpowers_le.mpr ?_)
  rw [ha]
  exact ‹N.Normal›.conj_mem _ hzN c

include d in
theorem rank_card_le_of_le_Q0 (I : In81) (hJo : CFSec8JOrder) (hL0 : CF81L0)
    (hSect : CF81E6Sect) (T : Sylow 2 H)
    (R : Sylow 2 ↥h.M3) (hR : (R : Subgroup ↥h.M3) = (T : Subgroup H).subgroupOf h.M3)
    {P : Subgroup H} (hP : P ≤ (T : Subgroup H) ⊓ h.M3) :
    Group.rank ↥P ≤ 4 ∧ Nat.card P ≤ 2 * Nat.card h.D ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := H₁.kloc.not_two_dvd_card_ker_modelHom I.cf1 I.cf2
  have hPM : P ≤ h.M3 := hP.trans inf_le_right
  set P' := P.subgroupOf h.M3 with hP'
  have hP'R : P' ≤ R := fun x hx => by
    rw [hR]
    exact (mem_inf.mp (hP hx)).1
  have hP'2 : IsPGroup 2 P' := R.isPGroup'.to_le hP'R
  have hinj : Function.Injective (H₁.kloc.rho.subgroupMap P') := fun x y hxy =>
    Subtype.ext (Eight.injOn_of_isPGroup hker hP'2 x.2 y.2 (congrArg Subtype.val hxy))
  let e : ↥P ≃* ↥(P'.map H₁.kloc.rho) := (subgroupOfEquivOfLe hPM).symm.trans
    (MulEquiv.ofBijective _ ⟨hinj, H₁.kloc.rho.subgroupMap_surjective P'⟩)
  obtain ⟨p, f, c, hp, hp2, hf, hK, hca, -, -, hcD⟩ := d.exists_e6Conf I.cf1 I.cf2 hJo hL0
  have hPN : P'.map H₁.kloc.rho ≤ Cat8.innA (h.K ⧸ pPrimeCore 2 h.K) c.a := by
    have h1 : P'.map H₁.kloc.rho ≤ H₁.kloc.rho.range := map_le_range _ _
    rw [H₁.kloc.rho_range_eq] at h1
    rw [hca]
    exact h1
  obtain ⟨⟨s, hs4, hscl⟩, hcard⟩ := hSect _ p f hp hp2 hf hK c _ hPN (hP'2.map _)
  refine ⟨?_, ?_⟩
  · rw [Group.rank_congr e]
    exact (E6.rank_le_of_closure hscl).trans hs4
  · rw [Nat.card_congr e.toEquiv, ← hcD]
    exact hcard

variable {d}

section Exit

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts) (hJo : CFSec8JOrder) (hL0 : CF81L0)
  (hCls : CF81E6Cls) (hOut : CF81E6Out) (hFld : CF81E6Fld)
include hv I F hJo hL0 hCls hOut hFld

theorem exists_T_fstar (hT₀ : ∃ T : Sylow 2 H, (T : Subgroup H) ≤ centralizer (h.B : Set H)) :
    ∃ T : Sylow 2 H, (T : Subgroup H) ≤ h.W ∧ h.B ≤ T ∧
      ∃ R : Sylow 2 ↥h.M3, (R : Subgroup ↥h.M3) = (T : Subgroup H).subgroupOf h.M3 ∧
        (T : Subgroup H) ⊓ generalizedFitting H ≤ (T : Subgroup H) ⊓ h.M3 := by
  obtain ⟨T, hTW, hBT, haT, R, hR⟩ := exists_T hT₀
  refine ⟨T, hTW, hBT, R, hR, fun t ht => ?_⟩
  obtain ⟨htT, htF⟩ := mem_inf.mp ht
  have hbT : d.b ∈ (T : Subgroup H) := hBT (d.B_eq ▸ mem_zpowers d.b)
  have hbM : d.b ∉ h.M3 := fun hb => d.e6_not_conj_b_M3 hv I hJo hL0 hCls F 1 (by
    rw [show (1 : H)⁻¹ * d.b * 1 = d.b by group]
    exact hb)
  exact E6.mem_of_transfer T.isPGroup' T.not_dvd_index
    (fun t ht q hq => Q0_normal hv I F hJo hL0 hCls hOut T hTW hBT haT R hR ht hq)
    (T_mod_Q0_cyclic hv I F hJo hL0 hCls hOut hFld T hTW hBT haT R hR)
    (fun N _ hN => inf_le_right.trans (d.M3_le_of_cyclic I F N hN)) hbT
    (fun hb => hbM (mem_inf.mp hb).2) d.b_mul_self
    (fun g hg => d.e6_not_conj_b_M3 hv I hJo hL0 hCls F g (mem_inf.mp hg).2) htT
    (fun N _ hN => h.fstar_le_of_cyclic N hN htF)

theorem exists_conj_le_Q0 (hT₀ : ∃ T : Sylow 2 H, (T : Subgroup H) ≤ centralizer (h.B : Set H)) :
    ∃ T : Sylow 2 H, (T : Subgroup H) ≤ h.W ∧ ∃ R : Sylow 2 ↥h.M3,
      (R : Subgroup ↥h.M3) = (T : Subgroup H).subgroupOf h.M3 ∧
      ∀ P : Subgroup H, P ≤ generalizedFitting H → IsPGroup 2 P → ∃ g : H,
        P.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup H) ⊓ h.M3 := by
  obtain ⟨T, hTW, -, R, hR, hTF⟩ := exists_T_fstar hv I F hJo hL0 hCls hOut hFld hT₀
  refine ⟨T, hTW, R, hR, fun P hPF hP2 => ?_⟩
  obtain ⟨P₂, hP₂⟩ := hP2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P₂ T
  refine ⟨g, fun y hy => hTF (mem_inf.mpr ⟨?_, ?_⟩)⟩
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def]
    exact smul_mem_pointwise_smul _ _ _ (hP₂ hx)
  · obtain ⟨x, hx, rfl⟩ := hy
    exact CFSG.LocalCores.generalized_fitting_characteristic.2.conj_mem _ (hPF hx) g

theorem card_le_fstar (hSect : CF81E6Sect)
    (hT₀ : ∃ T : Sylow 2 H, (T : Subgroup H) ≤ centralizer (h.B : Set H)) :
    ∀ P : Subgroup H, P ≤ generalizedFitting H → IsPGroup 2 P →
      Nat.card P ≤ 2 * Nat.card h.D ^ 2 := by
  obtain ⟨T, -, R, hR, hconj⟩ := exists_conj_le_Q0 hv I F hJo hL0 hCls hOut hFld hT₀
  intro P hPF hP2
  obtain ⟨g, hg⟩ := hconj P hPF hP2
  have h1 := (d.rank_card_le_of_le_Q0 I hJo hL0 hSect T R hR hg).2
  rwa [card_map_of_injective (MulAut.conj g).injective] at h1

theorem sect_fstar (hSect : CF81E6Sect)
    (hT₀ : ∃ T : Sylow 2 H, (T : Subgroup H) ≤ centralizer (h.B : Set H)) :
    ∀ P : Subgroup ↥(generalizedFitting H), IsPGroup 2 P →
      ∃ s : Finset ↥(generalizedFitting H), s.card ≤ 4 ∧ Subgroup.closure (s : Set _) = P := by
  obtain ⟨T, -, R, hR, hconj⟩ := exists_conj_le_Q0 hv I F hJo hL0 hCls hOut hFld hT₀
  intro P hP2
  set P₁ := P.map (generalizedFitting H).subtype with hP₁
  obtain ⟨g, hg⟩ := hconj P₁ (map_subtype_le _) (hP2.map _)
  have h1 := (d.rank_card_le_of_le_Q0 I hJo hL0 hSect T R hR hg).1
  apply E6.exists_finset_of_rank_le
  rw [Group.rank_congr (P.equivMapOfInjective _ (generalizedFitting H).subtype_injective),
    Group.rank_congr (P₁.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)]
  exact h1

omit hv hJo hL0 hCls hOut hFld in
theorem three_le_twoRank_fstar : 3 ≤ Open.twoRank ↥(generalizedFitting H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haF := d.a_mem_fstar I F
  have hzF : d.z ∈ generalizedFitting H := h.J_le_fstar (mem_inf.mp d.z_D).2
  have hτF : d.tau ∈ generalizedFitting H := mul_mem haF
    (by
      have h1 := CFSG.LocalCores.generalized_fitting_characteristic.2.conj_mem _ haF d.g⁻¹
      rwa [inv_inv] at h1)
  have ha2 : h.a * h.a = 1 := Six.a_mul_a_self h.toHyp52
  have hz2 : d.z * d.z = 1 := by rw [← pow_two, ← d.z_ord, pow_orderOf_eq_one]
  have hτ2 : d.tau * d.tau = 1 := d.tau_sq
  have hzM : d.z ∈ h.M3 := H₁.kloc.D_le_M3 d.z_D
  have hτz : d.tau * d.z = d.z * d.tau := F.tau_comm d.z ⟨h.toHyp52.sec8_D_le_Q d.z_D, hzM⟩
  have hA2 : ∀ x ∈ zpowers h.a, x * x = 1 := fun x hx => by
    rcases E6.mem_zpowers_of_mul_self ha2 hx with rfl | rfl
    · rw [mul_one]
    · exact ha2
  have hAz : ∀ x ∈ zpowers h.a, x * d.z = d.z * x := fun x hx => by
    rcases E6.mem_zpowers_of_mul_self ha2 hx with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (d.z_comm_a).symm
  have hAτ : ∀ x ∈ zpowers h.a, x * d.tau = d.tau * x := fun x hx => by
    rcases E6.mem_zpowers_of_mul_self ha2 hx with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (d.tau_comm_a).symm
  have hzA : d.z ∉ zpowers h.a := fun hz => by
    rcases E6.mem_zpowers_of_mul_self ha2 hz with h1 | h1
    · have := d.z_ord
      rw [h1, orderOf_one] at this
      exact absurd this (by norm_num)
    · exact d.z_ne_a h1
  have hA4 : Nat.card ↥(zpowers h.a ⊔ zpowers d.z) = 4 := by
    rw [E6.card_sup_zpowers hz2 hzA hAz, Nat.card_zpowers, h.orderOf_a]
  have hAzDP : zpowers h.a ⊔ zpowers d.z ≤ h.D ⊔ h.P :=
    sup_le (zpowers_le.mpr (mem_sup_right h.toHyp52.a_mem_P))
      (zpowers_le.mpr (mem_sup_left d.z_D))
  have hτA : d.tau ∉ zpowers h.a ⊔ zpowers d.z := fun hτ =>
    d.tau_not_mem_DP I.cf1 I.cf2 F (hAzDP hτ)
  have hτc := E6.comm_of_mem_sup_zpowers hAτ hτz.symm
  set E₈ := (zpowers h.a ⊔ zpowers d.z) ⊔ zpowers d.tau with hE₈
  have hE₈card : Nat.card E₈ = 8 := by
    rw [hE₈, E6.card_sup_zpowers hτ2 hτA hτc, hA4]
  have hE₈2 : ∀ x ∈ E₈, x * x = 1 :=
    E6.mul_self_of_mem_sup_zpowers (E6.mul_self_of_mem_sup_zpowers hA2 hz2 hAz) hτ2 hτc
  have hE₈F : E₈ ≤ generalizedFitting H :=
    sup_le (sup_le (zpowers_le.mpr haF) (zpowers_le.mpr hzF)) (zpowers_le.mpr hτF)
  set E' := E₈.subgroupOf (generalizedFitting H) with hE'
  have hE'card : Nat.card E' = 2 ^ 3 := by
    rw [hE', Six.card_subgroupOf_eq, inf_eq_left.mpr hE₈F, hE₈card]
    norm_num
  have hel : Open.IsElemAbelian 2 E' := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact E6.comm_of_mul_self hE₈2 _ x.2 _ y.2
    · apply Subtype.ext
      rw [SubgroupClass.coe_pow, sq, OneMemClass.coe_one]
      exact hE₈2 _ hx
  refine le_csSup ⟨Nat.card ↥(generalizedFitting H), ?_⟩ ⟨E', le_top, hel, hE'card⟩
  rintro k ⟨E, -, -, hE⟩
  calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
    _ = Nat.card E := hE.symm
    _ ≤ Nat.card ↥(generalizedFitting H) := Subgroup.card_le_card_group E

end Exit

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
