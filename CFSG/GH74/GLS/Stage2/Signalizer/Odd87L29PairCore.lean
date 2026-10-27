module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29NonTriv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank

structure PairCore {G : Type} [Group G] (z : G) (q₁ q₂ : ℕ)
    (L₁ L₂ : Subgroup (CentralizerBar z)) : Prop where
  prod : IsCentralProd L₁ L₂ (LBar z)
  zc₁ : Nat.card ↥(center ↥L₁) = 2
  zc₂ : Nat.card ↥(center ↥L₂) = 2
  inv₁ : ∀ x ∈ L₁, ∀ y ∈ L₁, orderOf x = 2 → orderOf y = 2 → x = y
  inv₂ : ∀ x ∈ L₂, ∀ y ∈ L₂, orderOf x = 2 → orderOf y = 2 → x = y
  card₁ : Nat.card ↥L₁ = q₁ * (q₁ ^ 2 - 1)
  card₂ : Nat.card ↥L₂ = q₂ * (q₂ ^ 2 - 1)
  fit : generalizedFitting (CentralizerBar z) ≤ LBar z

section PairCore

variable {G : Type} [Group G] {z : G} {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem PairCore.symm (hp : PairCore z q₁ q₂ L₁ L₂) : PairCore z q₂ q₁ L₂ L₁ where
  prod := ⟨by rw [sup_comm]; exact hp.prod.1, fun a ha b hb => (hp.prod.2.1 b hb a ha).symm,
    by rw [inf_comm]; exact hp.prod.2.2⟩
  zc₁ := hp.zc₂
  zc₂ := hp.zc₁
  inv₁ := hp.inv₂
  inv₂ := hp.inv₁
  card₁ := hp.card₂
  card₂ := hp.card₁
  fit := hp.fit

variable [Finite G]

theorem PairCore.mem_LBar_of_centralizes (hp : PairCore z q₁ q₂ L₁ L₂) {c : CentralizerBar z}
    (hc : ∀ x ∈ LBar z, c * x = x * c) : c ∈ LBar z := by
  have h := CFSG.centralizer_generalizedFitting_le (CentralizerBar z)
  refine hp.fit (h ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (hc x (hp.fit hx)).symm

theorem PairCore.centralizer_le_inf (hp : PairCore z q₁ q₂ L₁ L₂) (c : CentralizerBar z)
    (hc₁ : ∀ a ∈ L₁, c * a = a * c) (hc₂ : ∀ b ∈ L₂, c * b = b * c) : c ∈ L₁ ⊓ L₂ := by
  obtain ⟨hsup, hcomm, hcard⟩ := hp.prod
  have hcLB : c ∈ LBar z := by
    refine hp.mem_LBar_of_centralizes fun x hx => ?_
    rw [← hsup] at hx
    have hcc : (centralizer ({c} : Set (CentralizerBar z))) ≥ L₁ ⊔ L₂ :=
      sup_le (fun a ha => by
        rw [Subgroup.mem_centralizer_singleton_iff]; exact (hc₁ a ha).symm)
        (fun b hb => by
          rw [Subgroup.mem_centralizer_singleton_iff]; exact (hc₂ b hb).symm)
    have := hcc hx
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm
  rw [← hsup] at hcLB
  obtain ⟨l₁, hl₁, l₂, hl₂, hc⟩ := exists_mul_of_mem_sup_of_commute_aux hcomm hcLB
  have hl₁c : ∀ a ∈ L₁, l₁ * a = a * l₁ := by
    intro a ha
    have h1 := hc₁ a ha
    rw [hc] at h1
    have h2 := hcomm a ha l₂ hl₂
    have h3 : l₁ * a * l₂ = a * l₁ * l₂ := by
      calc l₁ * a * l₂ = l₁ * (a * l₂) := by group
        _ = l₁ * (l₂ * a) := by rw [h2]
        _ = l₁ * l₂ * a := by group
        _ = a * (l₁ * l₂) := h1
        _ = a * l₁ * l₂ := by group
    exact mul_right_cancel h3
  have hl₂c : ∀ b ∈ L₂, l₂ * b = b * l₂ := by
    intro b hb
    have h1 := hc₂ b hb
    rw [hc] at h1
    have h2 := hcomm l₁ hl₁ b hb
    have h3 : l₁ * (l₂ * b) = l₁ * (b * l₂) := by
      calc l₁ * (l₂ * b) = l₁ * l₂ * b := by group
        _ = b * (l₁ * l₂) := h1
        _ = (b * l₁) * l₂ := by group
        _ = (l₁ * b) * l₂ := by rw [← h2]
        _ = l₁ * (b * l₂) := by group
    exact mul_left_cancel h3
  have hI₁ : l₁ ∈ L₁ ⊓ L₂ := mem_inf_of_central hcomm hp.zc₁ hcard hl₁ hl₁c
  have hI₂ : l₂ ∈ L₂ ⊓ L₁ :=
    mem_inf_of_central (fun b hb a ha => (hcomm a ha b hb).symm) hp.zc₂ (by rwa [inf_comm]) hl₂
      hl₂c
  rw [inf_comm] at hI₂
  rw [hc]
  exact (L₁ ⊓ L₂).mul_mem hI₁ hI₂

theorem PairCore.zbar_mem_inf (hp : PairCore z q₁ q₂ L₁ L₂) :
    toBar z ⟨z, z_mem_cen z⟩ ∈ L₁ ⊓ L₂ :=
  hp.centralizer_le_inf _ (fun a _ => zbar_central z a) (fun b _ => zbar_central z b)

theorem PairCore.inf_eq_zpowers_zbar (hp : PairCore z q₁ q₂ L₁ L₂) (hz2 : orderOf z = 2) :
    L₁ ⊓ L₂ = zpowers (toBar z ⟨z, z_mem_cen z⟩) := by
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hne : toBar z ⟨z, z_mem_cen z⟩ ≠ 1 := by
    intro h
    have := eq_one_of_toBar_eq_one_of_sq (z_mem_cen z) hzz h
    rw [this, orderOf_one] at hz2
    omega
  have hsq : toBar z ⟨z, z_mem_cen z⟩ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    have : (⟨z, z_mem_cen z⟩ * ⟨z, z_mem_cen z⟩ : ↥(Cen z)) = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hord : orderOf (toBar z ⟨z, z_mem_cen z⟩) = 2 := orderOf_eq_prime hsq hne
  have hle : zpowers (toBar z ⟨z, z_mem_cen z⟩) ≤ L₁ ⊓ L₂ := (zpowers_le).mpr hp.zbar_mem_inf
  have hI : Nat.card ↥(L₁ ⊓ L₂) = 2 := hp.prod.2.2
  have hfin : Finite ↥(L₁ ⊓ L₂) := Nat.finite_of_card_ne_zero (by rw [hI]; norm_num)
  have hc : Nat.card ↥(zpowers (toBar z ⟨z, z_mem_cen z⟩)) = 2 := by rw [Nat.card_zpowers, hord]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hI])).symm

theorem PairCore.actOnK_ne_one_of_mem_LBar (hp : PairCore z q₁ q₂ L₁ L₂) (hz2 : orderOf z = 2)
    {u : G} (hu : u ∈ Cen z) (hu2 : u * u = 1) (hu1 : u ∉ zpowers z)
    (hLB : toBar z ⟨u, hu⟩ ∈ LBar z)
    (hn₁ : toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hn₂ : toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) :
    Stage1.Main.actOnK L₁ (toBar z ⟨u, hu⟩) hn₁ ≠ 1 ∧
      Stage1.Main.actOnK L₂ (toBar z ⟨u, hu⟩) hn₂ ≠ 1 := by
  obtain ⟨hsup, hcomm, hI⟩ := hp.prod
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hsq : (⟨u, hu⟩ : ↥(Cen z)) * ⟨u, hu⟩ = 1 := Subtype.ext hu2
  have hū2 : toBar z ⟨u, hu⟩ * toBar z ⟨u, hu⟩ = 1 := by rw [← map_mul, hsq, map_one]
  have hnI : toBar z ⟨u, hu⟩ ∉ L₁ ⊓ L₂ := by
    intro h
    rw [hp.inf_eq_zpowers_zbar hz2] at h
    exact hu1 (mem_zpowers_of_toBar_mem hzz hu hu2 h)
  have hLB₁ : toBar z ⟨u, hu⟩ ∈ L₁ ⊔ L₂ := hsup ▸ hLB
  have hLB₂ : toBar z ⟨u, hu⟩ ∈ L₂ ⊔ L₁ := by rw [sup_comm]; exact hLB₁
  refine ⟨fun h => hnI ?_, fun h => hnI ?_⟩
  · exact mem_inf_of_sq_one_of_centralizes hcomm hp.zc₁ hI hp.inv₂ hLB₁ hū2
      (actOnK_eq_one_imp hn₁ h)
  · have := mem_inf_of_sq_one_of_centralizes (A := L₂) (B := L₁)
      (fun b hb a ha => (hcomm a ha b hb).symm) hp.zc₂ (by rwa [inf_comm]) hp.inv₁ hLB₂ hū2
      (actOnK_eq_one_imp hn₂ h)
    rwa [inf_comm] at this

theorem PairCore.false_of_centralizes_of_index_two (hp : PairCore z q₁ q₂ L₁ L₂) {R M : Subgroup G}
    (hRL : R ≤ LC z) (hMC : M ≤ Cen z) (hidx : R.relIndex M ≤ 2) {u : G}
    (huM : u ∈ M) (huR : u ∉ R) (hpgl : InducedPGL2 L₁ (barOf z M) q₁)
    (hcen : ∀ a ∈ L₁, toBar z ⟨u, hMC huM⟩ * a = a * toBar z ⟨u, hMC huM⟩) : False := by
  obtain ⟨hsup, hcomm, -⟩ := hp.prod
  have hidx2 : (R.subgroupOf M).index = 2 := by
    have h1 : (R.subgroupOf M).index ≠ 1 := by
      intro h
      apply huR
      have := (Subgroup.index_eq_one.mp h)
      have hmem : (⟨u, huM⟩ : ↥M) ∈ R.subgroupOf M := by rw [this]; exact Subgroup.mem_top _
      exact hmem
    have h0 : (R.subgroupOf M).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have h3 : (R.subgroupOf M).index ≤ 2 := hidx
    omega
  apply false_of_pgl_inner hp.zc₁ hp.card₁ hpgl
  rintro t ⟨c, hc, rfl⟩
  have hcM : (c : G) ∈ M := hc
  by_cases hcR : (c : G) ∈ R
  · have hLB := toBar_mem_LBar (z := z) (hRL hcR)
    rw [← hsup] at hLB
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute_aux hcomm hLB
    refine ⟨a, ha, ?_⟩
    rw [hab, inv_mul_cancel_left]
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx b hb
  · have hu' : (⟨u, huM⟩ : ↥M)⁻¹ ∉ R.subgroupOf M := fun h => huR ((Subgroup.inv_mem_iff _).1 h)
    have hcR' : (⟨c, hcM⟩ : ↥M) ∉ R.subgroupOf M := hcR
    have hprod : (⟨c, hcM⟩ : ↥M) * (⟨u, huM⟩ : ↥M)⁻¹ ∈ R.subgroupOf M := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx2]
      exact ⟨fun h => absurd h hcR', fun h => absurd h hu'⟩
    have hprodR : (c : G) * u⁻¹ ∈ R := hprod
    have hLB := toBar_mem_LBar (z := z) (hRL hprodR)
    rw [← hsup] at hLB
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute_aux hcomm hLB
    refine ⟨a, ha, ?_⟩
    have e : toBar z c =
        toBar z ⟨(c : G) * u⁻¹, LC_le_cen z (hRL hprodR)⟩ * toBar z ⟨u, hMC huM⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      show (c : G) = (c : G) * u⁻¹ * u
      group
    rw [e, hab]
    have h2 : a⁻¹ * (a * b * toBar z ⟨u, hMC huM⟩) = b * toBar z ⟨u, hMC huM⟩ := by group
    rw [h2]
    refine Subgroup.mul_mem _ (Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx b hb) ?_
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hcen x hx).symm

theorem PairCore.actOnK_ne_one_of_index_two (hp : PairCore z q₁ q₂ L₁ L₂) {R M : Subgroup G}
    (hRL : R ≤ LC z) (hMC : M ≤ Cen z) (hidx : R.relIndex M ≤ 2) {u : G} (huM : u ∈ M)
    (huR : u ∉ R) (hpgl₁ : InducedPGL2 L₁ (barOf z M) q₁)
    (hpgl₂ : InducedPGL2 L₂ (barOf z M) q₂)
    (hn₁ : toBar z ⟨u, hMC huM⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hn₂ : toBar z ⟨u, hMC huM⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) :
    Stage1.Main.actOnK L₁ (toBar z ⟨u, hMC huM⟩) hn₁ ≠ 1 ∧
      Stage1.Main.actOnK L₂ (toBar z ⟨u, hMC huM⟩) hn₂ ≠ 1 :=
  ⟨fun h => hp.false_of_centralizes_of_index_two hRL hMC hidx huM huR hpgl₁
      (actOnK_eq_one_imp hn₁ h),
   fun h => hp.symm.false_of_centralizes_of_index_two hRL hMC hidx huM huR hpgl₂
      (actOnK_eq_one_imp hn₂ h)⟩

end PairCore

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
