module

public import CFSG.GH74.GLS.IVK.Lifted.Lem13a52
public import CFSG.GH74.GLS.IVK.Lifted.Lem31c
public import CFSG.GH74.GLS.IVK.Lifted.GroupAux

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem mem_sup_of_cSec_comp (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) (hpc : IsPCompIn 2 (Cz z) K) (hOK : HatOK (Hat K)) {x : G} (hx : x ∈ K)
    (hxc : x ∈ cSec K) : x ∈ Oz z ⊔ zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzK : z ∈ K := hM.z_mem_comp hK
  have hzc : z ∈ cSec K := (z_mem_Qof hM hK).2
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hM.z_sq) hM.z_ne
  have hxcen : hatMk K ⟨x, hx⟩ ∈ Subgroup.center (Hat K) := (mem_cSec_iff_hatMk_central hx).1 hxc
  have hzcen : hatMk K ⟨z, hzK⟩ ∈ Subgroup.center (Hat K) :=
    (mem_cSec_iff_hatMk_central hzK).1 hzc
  have hz1 : hatMk K ⟨z, hzK⟩ ≠ 1 := by
    intro h
    have hzO : z ∈ pPrimeCoreOf 2 K := (hatMk_eq_one_iff K ⟨z, hzK⟩).1 h
    have h1 := Subgroup.orderOf_dvd_natCard (pPrimeCoreOf 2 K) hzO
    rw [hz2] at h1
    exact (Nat.not_even_iff_odd.2 (TwoThin.card_pPrimeCoreOf_odd K)) (even_iff_two_dvd.2 h1)
  obtain ⟨c, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center (Hat K))).1 hOK.sl2.2
  have hzc' : (⟨hatMk K ⟨z, hzK⟩, hzcen⟩ : Subgroup.center (Hat K)) = c :=
    huniq _ (fun h => hz1 (congrArg Subtype.val h))
  by_cases hx1 : hatMk K ⟨x, hx⟩ = 1
  · have hxO : x ∈ pPrimeCoreOf 2 K := (hatMk_eq_one_iff K ⟨x, hx⟩).1 hx1
    exact mem_sup_left (pPrimeCoreOf_le_Oz hpc hxO)
  · have hxc' : (⟨hatMk K ⟨x, hx⟩, hxcen⟩ : Subgroup.center (Hat K)) = c :=
      huniq _ (fun h => hx1 (congrArg Subtype.val h))
    have hxz : hatMk K ⟨x, hx⟩ = hatMk K ⟨z, hzK⟩ :=
      congrArg Subtype.val (hxc'.trans hzc'.symm)
    have hxzO : x * z⁻¹ ∈ pPrimeCoreOf 2 K := by
      have hmem : x * z⁻¹ ∈ K := K.mul_mem hx (K.inv_mem hzK)
      refine (hatMk_eq_one_iff K ⟨x * z⁻¹, hmem⟩).1 ?_
      have : (⟨x * z⁻¹, hmem⟩ : ↥K) = ⟨x, hx⟩ * ⟨z, hzK⟩⁻¹ := rfl
      rw [this, map_mul, map_inv, hxz, mul_inv_cancel]
    have hx' : x = (x * z⁻¹) * z := by group
    rw [hx']
    exact mul_mem (mem_sup_left (pPrimeCoreOf_le_Oz hpc hxzO)) (mem_sup_right (mem_zpowers z))

theorem not_both_central (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂)
    (hpc₁ : IsPCompIn 2 (Cz z) K₁) (hpc₂ : IsPCompIn 2 (Cz z) K₂) (hOK₁ : HatOK (Hat K₁))
    (hOK₂ : HatOK (Hat K₂)) {x y : G} (hx : x ∈ K₁) (hy : y ∈ K₂) (hu2 : (x * y) * (x * y) = 1)
    (hu1 : x * y ≠ 1) (huz : x * y ≠ z) (hxc : x ∈ cSec K₁) (hyc : y ∈ cSec K₂) : False := by
  have h1 := mem_sup_of_cSec_comp hM (Or.inl rfl) hpc₁ hOK₁ hx hxc
  have h2 := mem_sup_of_cSec_comp hM (Or.inr rfl) hpc₂ hOK₂ hy hyc
  have hu : x * y ∈ Oz z ⊔ zpowers z := (Oz z ⊔ zpowers z).mul_mem h1 h2
  have hzO : ∀ n ∈ Oz z, z * n = n * z := fun n hn =>
    (Subgroup.mem_centralizer_singleton_iff.1 (TwoThin.pPrimeCoreOf_le (Cz z) hn)).symm
  rcases eq_one_or_eq_of_mem_sup_zpowers hM.z_sq card_Oz_odd hzO hu hu2 with h | h
  · exact hu1 h
  · exact huz h

theorem orderOf_hat_four (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂)
    (hpc₁ : IsPCompIn 2 (Cz z) K₁) (hpc₂ : IsPCompIn 2 (Cz z) K₂) (hOK₁ : HatOK (Hat K₁))
    (hOK₂ : HatOK (Hat K₂)) {x y : G} (hx : x ∈ K₁) (hy : y ∈ K₂) (hu2 : (x * y) * (x * y) = 1)
    (hu1 : x * y ≠ 1) (huz : x * y ≠ z) :
    orderOf (hatMk K₁ ⟨x, hx⟩) = 4 ∧ orderOf (hatMk K₂ ⟨y, hy⟩) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcs₁ : K₂ ≤ cSec K₁ := hM.cs₁
  have hcs₂ : K₁ ≤ cSec K₂ := hM.cs₂
  have hN₁ : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set G) :=
    sup_le Subgroup.le_normalizer (fun a ha => (hcs₁ ha).1)
  have hN₂ : K₁ ⊔ K₂ ≤ normalizer (K₂ : Set G) :=
    sup_le (fun a ha => (hcs₂ ha).1) Subgroup.le_normalizer
  have hxy : x * y ∈ K₁ ⊔ K₂ := mul_mem (mem_sup_left hx) (mem_sup_right hy)
  have hΦ₁ : MulAut.conj (hatMk K₁ ⟨x, hx⟩ * hatMk K₁ ⟨x, hx⟩) = 1 := by
    have h1 := phi_mul_self K₁ (hN₁ hxy) hu2
    have e1 : phi K₁ (x * y) (hN₁ hxy) = MulAut.conj (hatMk K₁ ⟨x, hx⟩) := by
      have := phi_mul K₁ (le_normalizer hx) (hN₁ (mem_sup_right hy))
      rw [phi_of_mem K₁ hx, (phi_eq_one_iff K₁ (hN₁ (mem_sup_right hy))).2 (hcs₁ hy), mul_one]
        at this
      exact this
    rw [e1] at h1
    rw [map_mul]
    exact h1
  have hΦ₂ : MulAut.conj (hatMk K₂ ⟨y, hy⟩ * hatMk K₂ ⟨y, hy⟩) = 1 := by
    have h1 := phi_mul_self K₂ (hN₂ hxy) hu2
    have e1 : phi K₂ (x * y) (hN₂ hxy) = MulAut.conj (hatMk K₂ ⟨y, hy⟩) := by
      have := phi_mul K₂ (hN₂ (mem_sup_left hx)) (le_normalizer hy)
      rw [phi_of_mem K₂ hy, (phi_eq_one_iff K₂ (hN₂ (mem_sup_left hx))).2 (hcs₂ hx), one_mul]
        at this
      exact this
    rw [e1] at h1
    rw [map_mul]
    exact h1
  have hx4 := sq_eq_one_of_card_center hOK₁.sl2.2 _ (mem_center_of_conj_eq_one hΦ₁)
  have hy4 := sq_eq_one_of_card_center hOK₂.sl2.2 _ (mem_center_of_conj_eq_one hΦ₂)
  have hxne : ¬ hatMk K₁ ⟨x, hx⟩ * hatMk K₁ ⟨x, hx⟩ = 1 := by
    intro h
    have hxc : x ∈ cSec K₁ :=
      (mem_cSec_iff_hatMk_central hx).2 (hat_sq_eq_one_mem_center hOK₁ h)
    have huA : x * y ∈ cSec K₁ := mul_mem hxc (hcs₁ hy)
    have huB : x * y ∈ cSec K₂ := mem_cSec_other hpc₁ hpc₂ hcs₁ hcs₂ hOK₁ hOK₂ hx hy hu2 huA
    have hyc : y ∈ cSec K₂ := by
      have := mul_mem (inv_mem (hcs₂ hx)) huB
      simpa using this
    exact not_both_central hM hpc₁ hpc₂ hOK₁ hOK₂ hx hy hu2 hu1 huz hxc hyc
  have hyne : ¬ hatMk K₂ ⟨y, hy⟩ * hatMk K₂ ⟨y, hy⟩ = 1 := by
    intro h
    have hyc : y ∈ cSec K₂ :=
      (mem_cSec_iff_hatMk_central hy).2 (hat_sq_eq_one_mem_center hOK₂ h)
    have huA : x * y ∈ cSec K₂ := mul_mem (hcs₂ hx) hyc
    have hxyx : x * y * x⁻¹ ∈ K₂ := (Subgroup.mem_normalizer_iff.1 (hcs₂ hx).1 y).1 hy
    have hab : (x * y * x⁻¹) * x = x * y := by group
    have huB : (x * y * x⁻¹) * x ∈ cSec K₁ :=
      mem_cSec_other hpc₂ hpc₁ hcs₂ hcs₁ hOK₂ hOK₁ hxyx hx (by rw [hab]; exact hu2)
        (by rw [hab]; exact huA)
    rw [hab] at huB
    have hxc : x ∈ cSec K₁ := by
      have := mul_mem huB (inv_mem (hcs₁ hy))
      simpa using this
    exact not_both_central hM hpc₁ hpc₂ hOK₁ hOK₂ hx hy hu2 hu1 huz hxc hyc
  have hfour : ∀ {Q : Type} [Group Q] (a : Q), ¬ a * a = 1 → (a * a) * (a * a) = 1 → orderOf a = 4 := by
    intro Q _ a hne h4
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a) (by simpa [pow_two] using hne)
      (by
        have : a ^ 2 ^ (1 + 1) = (a * a) * (a * a) := by
          have e : (2 : ℕ) ^ (1 + 1) = 2 + 2 := by norm_num
          rw [e, pow_add, pow_two]
        rw [this]
        exact h4)
    simpa using h
  exact ⟨hfour _ hxne hx4, hfour _ hyne hy4⟩

end Basic

section Core

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem exists_conj_mod_core (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂) {x x' y y' : G}
    (hx : x ∈ K₁) (hx' : x' ∈ K₁) (hy : y ∈ K₂) (hy' : y' ∈ K₂)
    (hcx : IsConj (hatMk K₁ ⟨x, hx⟩) (hatMk K₁ ⟨x', hx'⟩))
    (hcy : IsConj (hatMk K₂ ⟨y, hy⟩) (hatMk K₂ ⟨y', hy'⟩)) :
    ∃ k ∈ K₁ ⊔ K₂, k * (x * y) * k⁻¹ * (x' * y')⁻¹ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := by
  classical
  have hKle₁ : K₁ ≤ K₁ ⊔ K₂ := le_sup_left
  have hKle₂ : K₂ ≤ K₁ ⊔ K₂ := le_sup_right
  let p : ↥(K₁ ⊔ K₂) →* Hat (K₁ ⊔ K₂) := hatMk (K₁ ⊔ K₂)
  have hcore : ∀ a : ↥(K₁ ⊔ K₂), p a = 1 ↔ (a : G) ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := fun a =>
    hatMk_eq_one_iff (K₁ ⊔ K₂) a
  let f₁ : ↥K₁ →* Hat (K₁ ⊔ K₂) := p.comp (Subgroup.inclusion hKle₁)
  let f₂ : ↥K₂ →* Hat (K₁ ⊔ K₂) := p.comp (Subgroup.inclusion hKle₂)
  have hker₁ : pPrimeCore 2 ↥K₁ ≤ f₁.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    show p (Subgroup.inclusion hKle₁ a) = 1
    rw [hcore]
    have h1 : (a : G) ∈ pPrimeCoreOf 2 K₁ := Subgroup.mem_map_of_mem K₁.subtype ha
    exact hM.O_le_OK (Or.inl rfl) h1
  have hker₂ : pPrimeCore 2 ↥K₂ ≤ f₂.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    show p (Subgroup.inclusion hKle₂ a) = 1
    rw [hcore]
    have h1 : (a : G) ∈ pPrimeCoreOf 2 K₂ := Subgroup.mem_map_of_mem K₂.subtype ha
    exact hM.O_le_OK (Or.inr rfl) h1
  let g₁ : Hat K₁ →* Hat (K₁ ⊔ K₂) := QuotientGroup.lift (pPrimeCore 2 ↥K₁) f₁ hker₁
  let g₂ : Hat K₂ →* Hat (K₁ ⊔ K₂) := QuotientGroup.lift (pPrimeCore 2 ↥K₂) f₂ hker₂
  have hg₁ : ∀ a : ↥K₁, g₁ (hatMk K₁ a) = p (Subgroup.inclusion hKle₁ a) := fun a => rfl
  have hg₂ : ∀ b : ↥K₂, g₂ (hatMk K₂ b) = p (Subgroup.inclusion hKle₂ b) := fun b => rfl
  have hcomm : ∀ (a : Hat K₁) (b : Hat K₂), Commute (g₁ a) (g₂ b) := by
    intro a b
    obtain ⟨a, rfl⟩ := hatMk_surjective K₁ a
    obtain ⟨b, rfl⟩ := hatMk_surjective K₂ b
    rw [hg₁, hg₂]
    have hc : ⁅(a : G), (b : G)⁆ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) :=
      hM.O_le_OK (Or.inl rfl) ((hM.cs₁ b.2).2.2 a a.2)
    have hAB : p ⁅Subgroup.inclusion hKle₁ a, Subgroup.inclusion hKle₂ b⁆ = 1 := by
      refine (hcore _).2 ?_
      have : (((⁅Subgroup.inclusion hKle₁ a, Subgroup.inclusion hKle₂ b⁆ : ↥(K₁ ⊔ K₂)) : G)) =
          ⁅(a : G), (b : G)⁆ := by
        simp [commutatorElement_def]
      rw [this]
      exact hc
    rw [map_commutatorElement] at hAB
    exact commutatorElement_eq_one_iff_commute.1 hAB
  let F : Hat K₁ × Hat K₂ →* Hat (K₁ ⊔ K₂) := MonoidHom.noncommCoprod g₁ g₂ hcomm
  have key : ∀ (a : ↥K₁) (b : ↥K₂) (hab : (a : G) * (b : G) ∈ K₁ ⊔ K₂),
      p ⟨(a : G) * (b : G), hab⟩ = F (hatMk K₁ a, hatMk K₂ b) := by
    intro a b hab
    show _ = g₁ (hatMk K₁ a) * g₂ (hatMk K₂ b)
    rw [hg₁, hg₂, ← map_mul]
    rfl
  obtain ⟨c₁, hc₁⟩ := isConj_iff.1 hcx
  obtain ⟨c₂, hc₂⟩ := isConj_iff.1 hcy
  obtain ⟨k₁, rfl⟩ := hatMk_surjective K₁ c₁
  obtain ⟨k₂, rfl⟩ := hatMk_surjective K₂ c₂
  have hkmem : (k₁ : G) * (k₂ : G) ∈ K₁ ⊔ K₂ := mul_mem (hKle₁ k₁.2) (hKle₂ k₂.2)
  refine ⟨(k₁ : G) * (k₂ : G), hkmem, ?_⟩
  have hxymem : x * y ∈ K₁ ⊔ K₂ := mul_mem (hKle₁ hx) (hKle₂ hy)
  have hxymem' : x' * y' ∈ K₁ ⊔ K₂ := mul_mem (hKle₁ hx') (hKle₂ hy')
  have hmem : (k₁ : G) * (k₂ : G) * (x * y) * ((k₁ : G) * (k₂ : G))⁻¹ * (x' * y')⁻¹ ∈ K₁ ⊔ K₂ :=
    mul_mem (mul_mem (mul_mem hkmem hxymem) (inv_mem hkmem)) (inv_mem hxymem')
  refine (hcore ⟨_, hmem⟩).1 ?_
  have e : (⟨(k₁ : G) * (k₂ : G) * (x * y) * ((k₁ : G) * (k₂ : G))⁻¹ * (x' * y')⁻¹, hmem⟩ :
      ↥(K₁ ⊔ K₂)) = ⟨(k₁ : G) * (k₂ : G), hkmem⟩ * ⟨x * y, hxymem⟩ * ⟨(k₁ : G) * (k₂ : G), hkmem⟩⁻¹ *
        ⟨x' * y', hxymem'⟩⁻¹ := rfl
  have hprod : F ((hatMk K₁ k₁, hatMk K₂ k₂) * (hatMk K₁ ⟨x, hx⟩, hatMk K₂ ⟨y, hy⟩) *
      (hatMk K₁ k₁, hatMk K₂ k₂)⁻¹) = F (hatMk K₁ ⟨x', hx'⟩, hatMk K₂ ⟨y', hy'⟩) := by
    congr 1
    exact Prod.ext (by simpa using hc₁) (by simpa using hc₂)
  rw [map_mul, map_mul, map_inv] at hprod
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, key k₁ k₂ hkmem, key ⟨x, hx⟩ ⟨y, hy⟩ hxymem,
    key ⟨x', hx'⟩ ⟨y', hy'⟩ hxymem', hprod]
  exact mul_inv_cancel _

end Core

section Main

theorem ivk_3_1a_lifted_of_II4 (h44 : II4_44) (hAut : II4_Aut) (hII : II4_4_4_center) :
    IVK_3_1a_lifted := by
  intro G _ _ z S K₁ K₂ hstd u v hu hv hu2 hv2 hu1 hv1 huz hvz
  classical
  have hM := m4_of_std hII hstd
  have hK₁m : K₁ ∈ ({K₁, K₂} : Set (Subgroup G)) := Set.mem_insert _ _
  have hK₂m : K₂ ∈ ({K₁, K₂} : Set (Subgroup G)) := Set.mem_insert_of_mem _ rfl
  have hpc₁ : IsPCompIn 2 (Cz z) K₁ := rigid_isPCompIn (std4_comp_rigid hstd hK₁m)
  have hpc₂ : IsPCompIn 2 (Cz z) K₂ := rigid_isPCompIn (std4_comp_rigid hstd hK₂m)
  have hOK₁ := std4_hatOK h44 hstd hK₁m
  have hOK₂ := std4_hatOK h44 hstd hK₂m
  obtain ⟨x, hx, y, hy, rfl⟩ := hM.mem_sup hu
  obtain ⟨x', hx', y', hy', rfl⟩ := hM.mem_sup hv
  obtain ⟨hx4, hy4⟩ := orderOf_hat_four hM hpc₁ hpc₂ hOK₁ hOK₂ hx hy hu2 hu1 huz
  obtain ⟨hx4', hy4'⟩ := orderOf_hat_four hM hpc₁ hpc₂ hOK₁ hOK₂ hx' hy' hv2 hv1 hvz
  have hcx := (hAut (Hat K₁) hOK₁.sl2).2.1 _ _ hx4 hx4'
  have hcy := (hAut (Hat K₂) hOK₂.sl2).2.1 _ _ hy4 hy4'
  obtain ⟨k, hk, hkO⟩ := exists_conj_mod_core hM hx hx' hy hy' hcx hcy
  have hu₁2 : (k * (x * y) * k⁻¹) * (k * (x * y) * k⁻¹) = 1 := by
    have : (k * (x * y) * k⁻¹) * (k * (x * y) * k⁻¹) = k * ((x * y) * (x * y)) * k⁻¹ := by group
    rw [this, hu2]
    group
  have hu₁1 : k * (x * y) * k⁻¹ ≠ 1 := by
    intro h
    apply hu1
    have : x * y = k⁻¹ * (k * (x * y) * k⁻¹) * k := by group
    rw [this, h]
    group
  obtain ⟨g, hg, hgv⟩ := exists_conj_of_mul_mem_odd (O := pPrimeCoreOf 2 (K₁ ⊔ K₂))
    (TwoThin.card_pPrimeCoreOf_odd (K₁ ⊔ K₂)) hu₁2 hv2 hu₁1 hv1
    (fun n hn => hM.coreK.normal (x' * y') hv n hn) hkO
  have hgK : g ∈ K₁ ⊔ K₂ :=
    (sup_le (TwoThin.pPrimeCoreOf_le (K₁ ⊔ K₂)) (zpowers_le.2 hv)) hg
  refine ⟨g * k, mul_mem hgK hk, ?_⟩
  calc g * k * (x * y) * (g * k)⁻¹ = g * (k * (x * y) * k⁻¹) * g⁻¹ := by group
    _ = x' * y' := hgv

end Main

end CFSG.GH74.GLS.IVK.Lifted
