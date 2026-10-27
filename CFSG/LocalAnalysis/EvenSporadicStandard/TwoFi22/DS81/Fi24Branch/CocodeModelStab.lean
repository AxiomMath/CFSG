module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelStab

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H153
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelSz
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6Abs
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6

theorem mem_stabSub_of_maps_fin {U : Subgroup W11} {g : MulAut W11}
    (hg : ∀ u ∈ U, g u ∈ U) : g ∈ stabSub U := by
  have h1 : U.map g.toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact hg u hu
  have h2 : U.map g.toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge h1 (by rw [Subgroup.card_map_of_injective g.injective])
  intro u
  refine ⟨fun h => ?_, hg u⟩
  have hu' : g u ∈ U.map g.toMonoidHom := h2.symm ▸ h
  obtain ⟨v, hv, hvu⟩ := hu'
  have e : v = u := g.injective hvu
  rwa [← e]

@[expose] def V0 : Subgroup W11 := Subgroup.closure {t0, z0}

theorem t0_mul_self : t0 * t0 = 1 := by rw [← toW_xor, Nat.xor_self, toW_zero]

theorem t0_mem_V0 : t0 ∈ V0 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem z0_mem_V0 : z0 ∈ V0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem t0_mul_z0_mem_V0 : t0 * z0 ∈ V0 := V0.mul_mem t0_mem_V0 z0_mem_V0

theorem mem_V0_iff {x : W11} : x ∈ V0 ↔ x = 1 ∨ x = t0 ∨ x = z0 ∨ x = t0 * z0 := by
  have hT : t0 * t0 = 1 := t0_mul_self
  have hZ : z0 * z0 = 1 := lat_z0_mul_self
  have hTi : t0⁻¹ = t0 := inv_eq_of_mul_eq_one_right hT
  have hZi : z0⁻¹ = z0 := inv_eq_of_mul_eq_one_right hZ
  have h1 : t0 * (t0 * z0) = z0 := by rw [← mul_assoc, hT, one_mul]
  have h2 : t0 * z0 * t0 = z0 := by rw [mul_comm t0 z0, mul_assoc, hT, mul_one]
  have h3 : z0 * (t0 * z0) = t0 := by rw [mul_comm t0 z0, ← mul_assoc, hZ, one_mul]
  have h4 : t0 * z0 * z0 = t0 := by rw [mul_assoc, hZ, mul_one]
  have h5 : z0 * t0 = t0 * z0 := mul_comm _ _
  have h6 : t0 * z0 * (t0 * z0) = 1 := by rw [mul_mul_mul_comm, hT, hZ, one_mul]
  constructor
  · intro h
    induction h using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl hy))
    | one => exact Or.inl rfl
    | mul a b _ _ ha hb =>
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
        simp [hT, hZ, h1, h2, h3, h4, h5, h6]
    | inv a _ ha =>
      rcases ha with rfl | rfl | rfl | rfl
      · exact Or.inl inv_one
      · exact Or.inr (Or.inl hTi)
      · exact Or.inr (Or.inr (Or.inl hZi))
      · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right h6)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact V0.one_mem
    · exact t0_mem_V0
    · exact z0_mem_V0
    · exact t0_mul_z0_mem_V0

theorem maps_V0 {g : MulAut W11} (h1 : g t0 ∈ V0) (h2 : g z0 ∈ V0) {u : W11} (hu : u ∈ V0) :
    g u ∈ V0 := by
  induction hu using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact h1
    · rw [Set.mem_singleton_iff.1 hy]
      exact h2
  | one => rw [map_one]; exact V0.one_mem
  | mul a b _ _ iha ihb => rw [map_mul]; exact V0.mul_mem iha ihb
  | inv a _ iha => rw [map_inv]; exact V0.inv_mem iha

theorem mem_stabSub_V0_of {g : MulAut W11} (h1 : g t0 ∈ V0) (h2 : g z0 ∈ V0) :
    g ∈ stabSub V0 :=
  mem_stabSub_of_maps_fin fun _ hu => maps_V0 h1 h2 hu

theorem apply_z0_ne_of_duad {g : MulAut W11}
    (hg : g ∈ img11 AutPerm) {v : W11} (hv : v ∈ Duad) : g z0 ≠ v := by
  intro h
  have h2 : g⁻¹ (g z0) ∈ Duad :=
    apply_mem_Duad ((img11 AutPerm).inv_mem hg) (by rw [h]; exact hv)
  rw [MulAut.inv_apply_self] at h2
  exact z0_not_mem_Duad h2

theorem t0_mem_Duad : t0 ∈ Duad :=
  (mem_D0_iff.1 t0_mem_D0).1

theorem t0_mul_z0_mem_Duad : t0 * z0 ∈ Duad :=
  (mem_D0_iff.1 t0_mem_D0).2

theorem apply_z0_of_mem_stab {g : MulAut W11}
    (hg : g ∈ img11 AutPerm ⊓ stabSub V0) : g z0 = z0 := by
  have hz : g z0 ∈ V0 := (hg.2 z0).2 z0_mem_V0
  rcases mem_V0_iff.1 hz with h | h | h | h
  · exact absurd (g.injective (h.trans (map_one g).symm)) pair_z0_ne_one
  · exact absurd h (apply_z0_ne_of_duad hg.1 t0_mem_Duad)
  · exact h
  · exact absurd h (apply_z0_ne_of_duad hg.1 t0_mul_z0_mem_Duad)

theorem stab_V0_le_Sz :
    img11 AutPerm ⊓ stabSub V0 ≤ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) :=
  fun _ hg => ⟨hg.1, mem_centSub_zpowers.2 (apply_z0_of_mem_stab hg)⟩

theorem ksC_t0 : ∀ c < 64, act11 (ksC c) 32 = 32 ∨ act11 (ksC c) 32 = 63 := by decide +kernel

theorem img11_KSp_le_stab_V0 :
    img11 KSp ≤ stabSub V0 := by
  intro g hg
  obtain ⟨σ, hσ, rfl⟩ := hg
  have hσK : (σ : S24) ∈ KSp := Subgroup.mem_subgroupOf.1 hσ
  obtain ⟨c, hc⟩ := mem_KSp_iff.1 hσK
  have hz : rho11 AutPerm le_rfl σ z0 = z0 :=
    mem_centSub_zpowers.1 (img11_KSp_le_Sz ⟨σ, hσ, rfl⟩).2
  have ha : HasArr (σ : S24) (ksC c) := hc ▸ hasArr_ksP c
  have ht : rho11 AutPerm le_rfl σ t0 = toW 11 (act11 (ksC c) 32) :=
    rho11_toW AutPerm le_rfl σ ha 32
  refine mem_stabSub_V0_of ?_ (by rw [hz]; exact z0_mem_V0)
  rw [ht]
  rcases ksC_t0 c c.2 with h | h
  · rw [h]
    exact t0_mem_V0
  · rw [h, ← t0_mul_z0]
    exact t0_mul_z0_mem_V0

theorem act11_r0Arr_t0 : act11 r0Arr 32 = 96 := by decide +kernel

theorem r0Aut_not_mem_stab_V0 : r0Aut ∉ stabSub V0 := by
  intro h
  have h1 : r0Aut t0 ∈ V0 := (h t0).2 t0_mem_V0
  have e : r0Aut t0 = toW 11 96 := by
    rw [r0Aut, rho11_toW AutPerm le_rfl ⟨r0, r0_mem_AutPerm⟩ hasArr_r0 32, act11_r0Arr_t0]
  rw [e, mem_V0_iff, t0_mul_z0] at h1
  rcases h1 with h | h | h | h
  · have := toW_inj (by norm_num) (by norm_num) (h.trans (toW_zero 11).symm)
    omega
  · have := toW_inj (by norm_num) (by norm_num) h
    omega
  · have := toW_inj (by norm_num) (by norm_num) h
    omega
  · have := toW_inj (by norm_num) (by norm_num) h
    omega

theorem apply_t0_cases {g : MulAut W11}
    (hg : g ∈ img11 AutPerm ⊓ stabSub V0) : g t0 = t0 ∨ g t0 = t0 * z0 := by
  have h1 : g t0 ∈ V0 := (hg.2 t0).2 t0_mem_V0
  have h2 : g t0 ∈ Duad := apply_mem_Duad hg.1 t0_mem_Duad
  rcases mem_V0_iff.1 h1 with h | h | h | h
  · exact absurd (h ▸ h2) one_not_mem_Duad
  · exact Or.inl h
  · exact absurd (h ▸ h2) z0_not_mem_Duad
  · exact Or.inr h

theorem orbit_t0_stab :
    MulAction.orbit ↥(img11 AutPerm ⊓ stabSub V0) t0 = {t0, t0 * z0} := by
  ext v
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    rcases apply_t0_cases hg with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hv
    rcases hv with rfl | hv
    · exact ⟨1, one_smul _ _⟩
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      obtain ⟨g, hg, hgt⟩ := CocodeModelPair.exists_swap
      have hgS := img11_Lz_le_stab hg
      have hgz : g z0 = z0 := mem_centSub_zpowers.1 hgS.2
      have hmem : g ∈ img11 AutPerm ⊓ stabSub V0 :=
        ⟨hgS.1, mem_stabSub_V0_of (by rw [hgt]; exact t0_mul_z0_mem_V0)
          (by rw [hgz]; exact z0_mem_V0)⟩
      exact ⟨⟨g, hmem⟩, hgt⟩

theorem ncard_orbit_t0_stab : ({t0, t0 * z0} : Set W11).ncard = 2 := by
  refine Set.ncard_pair fun h => pair_z0_ne_one (mul_left_cancel (a := t0) ?_)
  rw [mul_one]
  exact h.symm

theorem card_stab_V0 :
    Nat.card ↥(img11 AutPerm ⊓ stabSub V0) = 7680 := by
  set H := img11 AutPerm ⊓ stabSub V0 with hH
  have e : ↥(H ⊓ centSub (Subgroup.zpowers t0)) ≃ ↥(MulAction.stabilizer ↥H t0) :=
    { toFun := fun y => ⟨⟨y, y.2.1⟩, mem_centSub_zpowers.1 y.2.2⟩
      invFun := fun y => ⟨y.1, y.1.2, mem_centSub_zpowers.2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥H t0)
  rw [MulAction.index_stabilizer, orbit_t0_stab, ncard_orbit_t0_stab,
    ← Nat.card_congr e] at h1
  have h2 : H ⊓ centSub (Subgroup.zpowers t0) =
      (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) ⊓ centSub (Subgroup.zpowers t0) := by
    refine le_antisymm (fun g hg => ⟨stab_V0_le_Sz hg.1, hg.2⟩) (fun g hg => ⟨⟨hg.1.1, ?_⟩, hg.2⟩)
    have ht : g t0 = t0 := mem_centSub_zpowers.1 hg.2
    have hz : g z0 = z0 := mem_centSub_zpowers.1 hg.1.2
    exact mem_stabSub_V0_of (by rw [ht]; exact t0_mem_V0) (by rw [hz]; exact z0_mem_V0)
  rw [h2, card_stab_t0_Sz_eq] at h1
  omega

@[expose] noncomputable def MV : Subgroup ↥(MY M24g S0) := (stabSub V0).comap rhoM

theorem rhoM_mem_img11 (σ : ↥(MY M24g S0)) : rhoM σ ∈ img11 AutPerm :=
  ⟨⟨σ, MY0_le_autPerm σ.2⟩, Subgroup.mem_subgroupOf.2 (MY0_le_autPerm σ.2), rfl⟩

theorem map_rhoM_MV :
    MV.map rhoM = img11 AutPerm ⊓ stabSub V0 := by
  ext g
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨rhoM_mem_img11 σ, hσ⟩
  · intro hg
    obtain ⟨σ, rfl⟩ := mem_Sz_iff.1 (stab_V0_le_Sz hg)
    exact ⟨σ, hg.2, rfl⟩

theorem card_MV :
    Nat.card MV = 7680 := by
  have h := Subgroup.card_map_of_injective (K := MV) rhoM_injective
  rw [map_rhoM_MV, card_stab_V0] at h
  exact h.symm

theorem KM_le_MV :
    KM ≤ MV := fun κ hκ =>
  img11_KSp_le_stab_V0 (by rw [← map_rhoM_KM]; exact ⟨κ, hκ, rfl⟩)

theorem r0_not_mem_MV :
    (⟨r0, Lz_le_MY0 r0_mem_Lz⟩ : ↥(MY M24g S0)) ∉ MV :=
  r0Aut_not_mem_stab_V0

theorem kappa_pairVec_one_three : cocodeCoords.κ (pairVec (1 : Fin 24) 3) = t0 := by
  rw [kappa11_pairVec_mask 1 3 (by decide)]
  exact congrArg (toW 11) (by decide +kernel : pairImg11 ((1 : Fin 24) : ℕ) ((3 : Fin 24) : ℕ) = 32)

theorem kappa_pairVec_zero_two : cocodeCoords.κ (pairVec (0 : Fin 24) 2) = t0 * z0 := by
  rw [kappa11_pairVec_mask 0 2 (by decide), t0_mul_z0]
  exact congrArg (toW 11) (by decide +kernel : pairImg11 ((0 : Fin 24) : ℕ) ((2 : Fin 24) : ℕ) = 63)

theorem colOf_apply (σ : ↥(MY M24g S0)) (i : Fin 24) :
    colOf ((σ : S24) i) = piM σ (colOf i) :=
  colHom_spec ⟨σ, MY0_le_BP σ.2⟩ i

theorem piM_fix_of_mem_MV
    {σ : ↥(MY M24g S0)}
    (hσ : σ ∈ MV) : piM σ 0 = 0 := by
  have hH : rhoM σ ∈ img11 AutPerm ⊓ stabSub V0 := ⟨rhoM_mem_img11 σ, hσ⟩
  have he : rhoM σ t0 = cocodeCoords.κ (pairVec ((σ : S24) 1) ((σ : S24) 3)) := by
    rw [← kappa_pairVec_one_three]
    exact rho11_pairVec AutPerm le_rfl ⟨(σ : S24), MY0_le_autPerm σ.2⟩ 1 3
  have h13 : (σ : S24) 1 ≠ (σ : S24) 3 := fun h => absurd ((σ : S24).injective h) (by decide)
  have hcol : (σ : S24) 1 = 0 ∨ (σ : S24) 1 = 1 ∨ (σ : S24) 1 = 2 ∨ (σ : S24) 1 = 3 := by
    rcases apply_t0_cases hH with h | h
    · have h' : cocodeCoords.κ (pairVec ((σ : S24) 1) ((σ : S24) 3)) =
          cocodeCoords.κ (pairVec (1 : Fin 24) 3) := by rw [← he, h, kappa_pairVec_one_three]
      rcases kappa11_pairVec_inj h13 (by decide) h' with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inr h1))
    · have h' : cocodeCoords.κ (pairVec ((σ : S24) 1) ((σ : S24) 3)) =
          cocodeCoords.κ (pairVec (0 : Fin 24) 2) := by rw [← he, h, kappa_pairVec_zero_two]
      rcases kappa11_pairVec_inj h13 (by decide) h' with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inl h1))
  have hc : colOf ((σ : S24) 1) = 0 := by
    rcases hcol with h | h | h | h <;> rw [h] <;> rfl
  rw [colOf_apply] at hc
  exact hc

theorem inf_ker_MV_eq :
    MV ⊓ piM.ker = KM := by
  have hc : Nat.card piM.ker = 3 * Nat.card KM := by rw [card_ker_piM, card_KM]
  have hle : KM ≤ MV ⊓ piM.ker := le_inf KM_le_MV KM_le_ker
  rcases card_eq_of_le_ker hle inf_le_right hc with h | h
  · exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq h)).symm
  · exfalso
    have h2 : MV ⊓ piM.ker = piM.ker :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq h.symm)
    have hr : (⟨r0, Lz_le_MY0 r0_mem_Lz⟩ : ↥(MY M24g S0)) ∈ piM.ker :=
      (piM_lz r0_mem_Lz).trans colLz_r0
    have hr' : (⟨r0, Lz_le_MY0 r0_mem_Lz⟩ : ↥(MY M24g S0)) ∈ MV ⊓ piM.ker := by
      rw [h2]
      exact hr
    exact r0_not_mem_MV hr'.1

theorem card_map_piM_MV :
    Nat.card (MV.map piM) = 120 := by
  have hidx : (piM.ker.subgroupOf MV).index = Nat.card (MV.map piM) := by
    change piM.ker.relIndex MV = Nat.card (MV.map piM)
    rw [Subgroup.relIndex_ker]
  have h1 := Subgroup.card_mul_index (piM.ker.subgroupOf MV)
  have hsub : piM.ker.subgroupOf MV = KM.subgroupOf MV := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hx : (x : ↥(MY M24g S0)) ∈ MV ⊓ piM.ker := ⟨x.2, h⟩
      rwa [inf_ker_MV_eq] at hx
    · intro h
      exact KM_le_ker h
  rw [hidx, hsub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe KM_le_MV).toEquiv, card_KM,
    card_MV] at h1
  omega

theorem map_piM_MV :
    MV.map piM = MulAction.stabilizer (Equiv.Perm (Fin 6)) (0 : Fin 6) := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨σ, hσ, rfl⟩
    exact piM_fix_of_mem_MV hσ
  · rw [card_stabilizer, card_map_piM_MV]

theorem le_KM_of_normal_isPGroup
    {Q : Subgroup ↥(MY M24g S0)} (hQMV : Q ≤ MV)
    (hQ2 : IsPGroup 2 Q) (hQn : ∀ τ ∈ MV, ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q) : Q ≤ KM := by
  have hY : Q.map piM = ⊥ := by
    refine eq_bot_of_normal_isPGroup (c := 0) (hQ2.map piM) ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact piM_fix_of_mem_MV (hQMV hq)
    · intro s hs y hy
      obtain ⟨q, hq, rfl⟩ := hy
      have hs' : s ∈ MV.map piM := by
        rw [map_piM_MV]
        exact hs
      obtain ⟨τ, hτ, rfl⟩ := hs'
      exact ⟨τ * q * τ⁻¹, hQn τ hτ q hq, by rw [map_mul, map_mul, map_inv]⟩
  have hker : Q ≤ piM.ker := fun q hq => by
    have hm : piM q ∈ Q.map piM := ⟨q, hq, rfl⟩
    rw [hY, Subgroup.mem_bot] at hm
    exact hm
  intro q hq
  have hq' : q ∈ MV ⊓ piM.ker := ⟨hQMV hq, hker hq⟩
  rwa [inf_ker_MV_eq] at hq'

theorem O2In_le_self {G : Type} [Group G] (H : Subgroup G) : O2In H ≤ H :=
  Subgroup.map_subtype_le _

theorem O2In_conj_mem {G : Type} [Group G] {H : Subgroup G} {u h : G} (hu : u ∈ O2In H)
    (hh : h ∈ H) : h * u * h⁻¹ ∈ O2In H := by
  obtain ⟨x, hx, rfl⟩ := hu
  exact ⟨⟨h, hh⟩ * x * ⟨h, hh⟩⁻¹,
    (CFSG.LieType.BorelTits.pCore_normal 2).conj_mem x hx ⟨h, hh⟩, rfl⟩

theorem isPGroup_O2In {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    IsPGroup 2 (O2In H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.LieType.BorelTits.pCore_isPGroup 2).map H.subtype

theorem O2In_stab_V0 :
    O2In (img11 AutPerm ⊓ stabSub V0) = img11 KSp := by
  set H := img11 AutPerm ⊓ stabSub V0 with hH
  have hKH : img11 KSp ≤ H := fun g hg => ⟨(img11_KSp_le_Sz hg).1, img11_KSp_le_stab_V0 hg⟩
  have hHS : H ≤ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) := stab_V0_le_Sz
  refine le_antisymm ?_ ?_
  · have hrange : O2In H ≤ rhoM.range := by
      rw [range_rhoM, img11_MY0_eq_Sz]
      exact (O2In_le_self H).trans hHS
    have hQ : (O2In H).comap rhoM ≤ KM := by
      refine le_KM_of_normal_isPGroup ?_ ?_ ?_
      · intro q hq
        exact (O2In_le_self H hq).2
      · exact (isPGroup_O2In H).comap_of_injective rhoM rhoM_injective
      · intro τ hτ q hq
        show rhoM (τ * q * τ⁻¹) ∈ O2In H
        rw [map_mul, map_mul, map_inv]
        exact O2In_conj_mem hq ⟨rhoM_mem_img11 τ, hτ⟩
    calc O2In H = ((O2In H).comap rhoM).map rhoM := (Subgroup.map_comap_eq_self hrange).symm
      _ ≤ KM.map rhoM := Subgroup.map_mono hQ
      _ = img11 KSp := map_rhoM_KM
  · have hKA : KSp ≤ AutPerm := KSp_le_MY0.trans MY0_le_autPerm
    have hp : IsPGroup 2 (img11 KSp) :=
      IsPGroup.of_card (n := 6) (by rw [card_img11' hKA, card_KSp]; norm_num)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKH
      (fun h hh => Subgroup.mem_normalizer_fintype fun n hn =>
        conj_mem_img11_KSp (hHS hh) hn) hp

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelStab
