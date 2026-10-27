module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelSz
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6Abs
public import CFSG.Quasithin.Background.H153Grp
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.GlueO23
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44ReifartTransport

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H153
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelSz
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6Abs

@[expose] def KM : Subgroup ↥(MY M24g S0) := KSp.subgroupOf (MY M24g S0)

@[expose] def LM : Subgroup ↥(MY M24g S0) := Lz.subgroupOf (MY M24g S0)

theorem card_KM : Nat.card KM = 64 := by
  rw [KM, Nat.card_congr (Subgroup.subgroupOfEquivOfLe KSp_le_MY0).toEquiv, card_KSp]

theorem normal_KM :
    KM.Normal :=
  ⟨fun k hk g => by
    have := MY0_conj_KSp g.2 (Subgroup.mem_subgroupOf.1 hk)
    exact Subgroup.mem_subgroupOf.2 this⟩

theorem KM_le_ker : KM ≤ piM.ker := fun k hk => by
  obtain ⟨c, hc⟩ := mem_KSp_iff.1 (Subgroup.mem_subgroupOf.1 hk)
  have : k = ⟨ksP c, KSp_le_MY0 (ksP_mem_KSp c)⟩ := Subtype.ext hc.symm
  rw [this]
  exact piM_ksP c

theorem LM_perfect : LM ≤ ⁅LM, LM⁆ := by
  have h : ⁅Lz.subgroupOf (MY M24g S0), Lz.subgroupOf (MY M24g S0)⁆ =
      Lz.subgroupOf (MY M24g S0) := by
    apply Subgroup.map_injective (MY M24g S0).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le Lz_le_MY0, commutator_Lz]
  exact h.ge

theorem ker_le_LM :
    piM.ker ≤ LM := fun σ hσ => by
  show (σ : S24) ∈ Lz
  by_contra h
  have h1 := sign_piM_neg σ.2 h
  have h2 : piM σ = 1 := hσ
  rw [show (⟨(σ : S24), σ.2⟩ : ↥(MY M24g S0)) = σ from rfl, h2, map_one] at h1
  exact absurd h1 (by decide)

theorem map_LM_le : LM.map piM ≤ alternatingGroup (Fin 6) := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact Equiv.Perm.mem_alternatingGroup.2 (sign_piM_one σ.2 hσ)

theorem normal_cases_M
    {M : Subgroup ↥(MY M24g S0)} [M.Normal] (hKM : KM ≤ M) :
    (M ≤ piM.ker ∨ piM.ker ≤ M) ∧
      (Nat.card M = 64 ∨ Nat.card M = 3 * 64 ∨ Nat.card M = 1080 * 64 ∨
        Nat.card M = 2160 * 64) := by
  haveI := normal_KM
  have hc : Nat.card piM.ker = 3 * Nat.card KM := by rw [card_ker_piM, card_KM]
  have h := card_normal_cases piM piM_surjective LM_perfect ker_le_LM map_LM_le KM_le_ker hc hKM
  rw [card_KM] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, by omega⟩

@[expose] noncomputable def rhoM : ↥(MY M24g S0) →* MulAut W11 :=
  (rho11 AutPerm le_rfl).comp (Subgroup.inclusion MY0_le_autPerm)

theorem rhoM_injective : Function.Injective rhoM :=
  (rho11_injective AutPerm le_rfl).comp (Subgroup.inclusion_injective _)

theorem map_rhoM_subgroupOf {Γ : Subgroup S24} (hΓ : Γ ≤ MY M24g S0) :
    (Γ.subgroupOf (MY M24g S0)).map rhoM = img11 Γ := by
  ext x
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, MY0_le_autPerm σ.2⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hσ),
      rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    have hσΓ : (σ : S24) ∈ Γ := Subgroup.mem_subgroupOf.1 hσ
    exact ⟨⟨σ, hΓ hσΓ⟩, Subgroup.mem_subgroupOf.2 hσΓ, rfl⟩

theorem map_rhoM_KM : KM.map rhoM = img11 KSp := map_rhoM_subgroupOf KSp_le_MY0

theorem range_rhoM : rhoM.range = img11 (MY M24g S0) := by
  rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self (H := MY M24g S0),
    map_rhoM_subgroupOf le_rfl]

theorem img11_MY0_eq_Sz :
    img11 (MY M24g S0) = img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) :=
  Subgroup.eq_of_le_of_card_ge img11_MY0_le
    (le_of_eq (by rw [card_img11' MY0_le_autPerm, card_MY0, card_Sz]))

@[expose] noncomputable def eSz :
    ↥(MY M24g S0) ≃* ↥(img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) :=
  (MonoidHom.ofInjective rhoM_injective).trans
    (MulEquiv.subgroupCongr (range_rhoM.trans img11_MY0_eq_Sz))

theorem mem_Sz_iff
    {g : MulAut W11} :
    g ∈ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) ↔ ∃ σ : ↥(MY M24g S0), rhoM σ = g := by
  rw [← img11_MY0_eq_Sz, ← range_rhoM]
  exact MonoidHom.mem_range

theorem subtype_comp_eSz :
    (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)).subtype.comp eSz.toMonoidHom = rhoM :=
  MonoidHom.ext fun _ => rfl

theorem img11_KSp_le_Sz :
    img11 KSp ≤ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) := by
  rw [← img11_MY0_eq_Sz, ← range_rhoM, ← map_rhoM_KM]
  exact Subgroup.map_le_range _ _

theorem conj_mem_img11_KSp
    {g k : MulAut W11}
    (hg : g ∈ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) (hk : k ∈ img11 KSp) :
    g * k * g⁻¹ ∈ img11 KSp := by
  obtain ⟨σ, rfl⟩ := mem_Sz_iff.1 hg
  rw [← map_rhoM_KM] at hk ⊢
  obtain ⟨κ, hκ, rfl⟩ := hk
  haveI := normal_KM
  exact ⟨σ * κ * σ⁻¹, ‹KM.Normal›.conj_mem κ hκ σ, by rw [map_mul, map_mul, map_inv]⟩

theorem normal_card_model
    {M : Subgroup (MulAut W11)}
    (hMS : M ≤ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) (hKM : img11 KSp ≤ M)
    (hn : ∀ n ∈ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0), ∀ u ∈ M, n * u * n⁻¹ ∈ M) :
    Nat.card M = 64 ∨ Nat.card M = 3 * 64 ∨ Nat.card M = 1080 * 64 ∨
      Nat.card M = 2160 * 64 := by
  have h1 : (M.comap rhoM).map rhoM = M := by
    refine Subgroup.map_comap_eq_self ?_
    rw [range_rhoM, img11_MY0_eq_Sz]
    exact hMS
  have hcard : Nat.card (M.comap rhoM) = Nat.card M := by
    conv_rhs => rw [← h1]
    exact (Subgroup.card_map_of_injective rhoM_injective).symm
  haveI : (M.comap rhoM).Normal := ⟨fun x hx g => by
    show rhoM (g * x * g⁻¹) ∈ M
    rw [map_mul, map_mul, map_inv]
    exact hn _ (mem_Sz_iff.2 ⟨g, rfl⟩) _ hx⟩
  have hKM' : KM ≤ M.comap rhoM := fun κ hκ =>
    hKM (by rw [← map_rhoM_KM]; exact ⟨κ, hκ, rfl⟩)
  have h2 := (normal_cases_M hKM').2
  rw [hcard] at h2
  exact h2

theorem pCore_MY0 :
    CFSG.pCore 2 ↥(MY M24g S0) = KM := by
  have h : (pCoreOf 2 (MY M24g S0)).subgroupOf (MY M24g S0) = CFSG.pCore 2 ↥(MY M24g S0) :=
    Subgroup.comap_map_eq_self_of_injective (MY M24g S0).subtype_injective _
  rw [← h, pCoreOf_MY0]
  rfl

theorem O2In_MY0 :
    O2In (MY M24g S0) = KSp := pCoreOf_MY0

theorem O23In_MY0 :
    O23In (MY M24g S0) = N0 := by
  obtain ⟨hle, hnorm, -, hpow, hmax⟩ := isO23_MY0
  refine le_antisymm (hmax _ Glue.O23In_le (fun g hg n hn => Glue.O23In_conj_mem hn hg) ?_ ?_) ?_
  · rw [pCoreOf_MY0]
    exact Glue.le_O23In KSp_le_MY0 O2In_MY0
  · intro n hn
    have h := Glue.exists_pow_mem_of_mem_O23In O2In_MY0 hn
    rwa [pCoreOf_MY0]
  · refine Glue.le_O23In_of_pow_mem O2In_MY0 hle (fun v n hv hn => hnorm n hn v hv) ?_
    intro v hv
    have h := hpow v hv
    rwa [pCoreOf_MY0] at h

theorem O23Abs_MY0 :
    Reifart.O23Abs ↥(MY M24g S0) = piM.ker := by
  have h1 := Reifart.subgroupOf_map_subtype_eq (H := MY M24g S0)
    (Reifart.O23Abs ↥(MY M24g S0))
  rw [← Reifart.O23In_eq, O23In_MY0, N0_subgroupOf] at h1
  exact h1.symm

theorem O2In_Sz :
    O2In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) = img11 KSp := by
  rw [Reifart.O2In_eq, ← CFSG.pCore_map_iso 2 eSz, pCore_MY0, Subgroup.map_map,
    subtype_comp_eSz, map_rhoM_KM]

theorem O23In_Sz_eq_map :
    O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) = piM.ker.map rhoM := by
  rw [Reifart.O23In_eq, ← Reifart.map_O23Abs eSz, O23Abs_MY0, Subgroup.map_map,
    subtype_comp_eSz]

theorem card_O23In_Sz :
    Nat.card ↥(O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0))) = 192 := by
  rw [O23In_Sz_eq_map, Subgroup.card_map_of_injective rhoM_injective, card_ker_piM]

theorem ker_piM_eq_sup :
    piM.ker = KM ⊔ Subgroup.zpowers (⟨r0, Lz_le_MY0 r0_mem_Lz⟩ : ↥(MY M24g S0)) := by
  have hr : (⟨r0, Lz_le_MY0 r0_mem_Lz⟩ : ↥(MY M24g S0)) ∈ piM.ker :=
    (piM_lz r0_mem_Lz).trans colLz_r0
  have hle : KM ⊔ Subgroup.zpowers (⟨r0, Lz_le_MY0 r0_mem_Lz⟩ : ↥(MY M24g S0)) ≤ piM.ker :=
    sup_le KM_le_ker (Subgroup.zpowers_le.2 hr)
  have hQc : Nat.card (Subgroup.zpowers (⟨r0, Lz_le_MY0 r0_mem_Lz⟩ : ↥(MY M24g S0))) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_r0]
  have h64 : 64 ∣ Nat.card ↥(KM ⊔
      Subgroup.zpowers (⟨r0, Lz_le_MY0 r0_mem_Lz⟩ : ↥(MY M24g S0))) :=
    card_KM ▸ Subgroup.card_dvd_of_le le_sup_left
  have h3 : 3 ∣ Nat.card ↥(KM ⊔
      Subgroup.zpowers (⟨r0, Lz_le_MY0 r0_mem_Lz⟩ : ↥(MY M24g S0))) :=
    hQc ▸ Subgroup.card_dvd_of_le le_sup_right
  have h192 : 192 ∣ Nat.card ↥(KM ⊔
      Subgroup.zpowers (⟨r0, Lz_le_MY0 r0_mem_Lz⟩ : ↥(MY M24g S0))) := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 64 3) h64 h3
    simpa using this
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_ker_piM]
  exact Nat.le_of_dvd Nat.card_pos h192

theorem O23In_Sz_eq :
    O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) =
      img11 KSp ⊔ Subgroup.zpowers r0Aut := by
  rw [O23In_Sz_eq_map, ker_piM_eq_sup, Subgroup.map_sup, map_rhoM_KM, MonoidHom.map_zpowers]
  rfl

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6
