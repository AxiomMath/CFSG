module

public import CFSG.Holt.H78.Sec4Toolkit
public import CFSG.Holt.H78.Conjugacy
public import CFSG.Holt.H78.DataSocle
public import CFSG.Holt.H78.Sec4SEAut

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open scoped Pointwise

namespace HoltData

section NRho

variable {K X : Type*} [Group K] [MulAction K X] (D : HoltData K X)

noncomputable def coordPoint (k : D.ι) (c : D.Ψc k) : X :=
  (D.exists_coord_apply_eq k c).choose

@[simp] theorem coord_coordPoint (k : D.ι) (c : D.Ψc k) : D.coord (D.coordPoint k c) k = c :=
  (D.exists_coord_apply_eq k c).choose_spec

noncomputable def nRhoFun (k : D.ι) (g : K) (c : D.Ψc k) : D.Ψc k :=
  D.coord (g • D.coordPoint k c) k

theorem nRhoFun_coord {k : D.ι} {g : K} (hg : g ∈ Subgroup.normalizer (D.L k : Set K))
    (ω : X) : D.nRhoFun k g (D.coord ω k) = D.coord (g • ω) k :=
  ((D.normalizer_L_preserves_fibres hg _ ω).1).mpr (D.coord_coordPoint k _)

noncomputable def nRho (k : D.ι) :
    Subgroup.normalizer (D.L k : Set K) →* Equiv.Perm (D.Ψc k) where
  toFun g :=
    { toFun := D.nRhoFun k g
      invFun := D.nRhoFun k g⁻¹
      left_inv := fun c => by
        rw [← D.coord_coordPoint k c, D.nRhoFun_coord g.2, D.nRhoFun_coord (inv_mem g.2),
          inv_smul_smul]
      right_inv := fun c => by
        rw [← D.coord_coordPoint k c, D.nRhoFun_coord (inv_mem g.2), D.nRhoFun_coord g.2,
          smul_inv_smul] }
  map_one' := Equiv.ext fun c => by
    change D.nRhoFun k 1 c = c
    rw [← D.coord_coordPoint k c, D.nRhoFun_coord (one_mem _), one_smul]
  map_mul' g h := Equiv.ext fun c => by
    change D.nRhoFun k (g * h) c = D.nRhoFun k g (D.nRhoFun k h c)
    rw [← D.coord_coordPoint k c, D.nRhoFun_coord (mul_mem g.2 h.2), D.nRhoFun_coord h.2,
      D.nRhoFun_coord g.2, mul_smul]

theorem nRho_coord {k : D.ι} (g : Subgroup.normalizer (D.L k : Set K)) (ω : X) :
    D.nRho k g (D.coord ω k) = D.coord ((g : K) • ω) k :=
  D.nRhoFun_coord g.2 ω

theorem nRho_eq_rho {k : D.ι} (g : Subgroup.normalizer (D.L k : Set K)) (h : jHull K X)
    (hgh : (g : K) = h) : D.nRho k g = D.ρ k h := by
  ext c
  rw [← D.coord_coordPoint k c, D.nRho_coord, ← D.coord_smul, hgh]

end NRho

section ExtRho

variable {K X : Type*} [Group K] [MulAction K X] (D : HoltData K X)

theorem mem_normalizer_L_of_unique {i₀ : D.ι} (hι : ∀ j, j = i₀) (g : K) :
    g ∈ Subgroup.normalizer (D.L i₀ : Set K) := by
  obtain ⟨σ, hσ⟩ := D.conj_L g
  have h := hσ i₀
  rw [hι (σ i₀)] at h
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [h]
    exact ⟨x, hx, rfl⟩
  · rw [h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    rw [mul_left_inj, mul_right_inj] at hyx'
    exact hyx' ▸ hy

noncomputable def extRho {i₀ : D.ι} (hι : ∀ j, j = i₀) : K →* Equiv.Perm (D.Ψc i₀) :=
  (D.nRho i₀).comp
    ((MonoidHom.id K).codRestrict _ fun g => D.mem_normalizer_L_of_unique hι g)

theorem extRho_coord {i₀ : D.ι} (hι : ∀ j, j = i₀) (g : K) (ω : X) :
    D.extRho hι g (D.coord ω i₀) = D.coord (g • ω) i₀ :=
  D.nRho_coord _ ω

theorem extRho_eq_rho {i₀ : D.ι} (hι : ∀ j, j = i₀) (h : jHull K X) :
    D.extRho hι h = D.ρ i₀ h :=
  D.nRho_eq_rho _ h rfl

theorem extRho_mem_normalizer {i₀ : D.ι} (hι : ∀ j, j = i₀) (g : K) :
    D.extRho hι g ∈ Subgroup.normalizer (D.M i₀ : Set (Equiv.Perm (D.Ψc i₀))) := by
  have key : ∀ g : K, ∀ m ∈ D.M i₀, D.extRho hι g * m * (D.extRho hι g)⁻¹ ∈ D.M i₀ := by
    intro g m hm
    obtain ⟨l, hl, rfl⟩ := D.mem_M.mp hm
    have hgl : g * (l : K) * g⁻¹ ∈ D.L i₀ :=
      (Subgroup.mem_normalizer_iff.mp (D.mem_normalizer_L_of_unique hι g) l).mp hl
    have hgl' : g * (l : K) * g⁻¹ ∈ jHull K X := D.L_le i₀ hgl
    refine D.mem_M.mpr ⟨⟨_, hgl'⟩, hgl, ?_⟩
    rw [← D.extRho_eq_rho hι, ← D.extRho_eq_rho hι]
    simp only [map_mul, map_inv]
  refine Subgroup.mem_normalizer_iff.mpr fun m => ⟨key g m, fun hm => ?_⟩
  have h2 := key g⁻¹ _ hm
  rwa [map_inv, inv_inv, show (D.extRho hι g)⁻¹ * (D.extRho hι g * m * (D.extRho hι g)⁻¹) *
    D.extRho hι g = m by group] at h2

end ExtRho

end HoltData

theorem IsTypeL.mem_fixSet {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {α : Ω} {v : G}
    (hv : IsTypeL G Ω α v) : α ∈ fixSet Ω (Subgroup.zpowers v) := by
  rw [fixSet_zpowers, mem_fixedBy]
  exact hv.smul_eq

theorem smul_mem_holtDelta_of_mem_inf {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]
    {α β : Ω} {g : G} (hg : g ∈ stabilizer G α ⊓ stabilizer G β) {δ : Ω}
    (hδ : δ ∈ holtDelta G Ω α β) : g • δ ∈ holtDelta G Ω α β := by
  have h := stabilizer_pair_le α β (stabilizer_inf_le_stabilizer_pair α β hg)
  rw [← mem_stabilizer_iff.mp h]
  exact Set.smul_mem_smul_set hδ

section Config

variable (G : Type) [Group G] (Ω : Type) [MulAction G Ω]

structure FinConfig (α β : Ω) (v : G) where
  isTypeL : IsTypeL G Ω α v
  Dv : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))
  pPrimeCore_eq_bot : CFSG.pPrimeCore 2 (typeLSection G Ω v) = ⊥
  isNaturalSE_Dv : ∀ k, IsNaturalSE (Dv.M k)
  i : Dv.ι
  mem_fixSet : β ∈ fixSet Ω (Subgroup.zpowers v)
  coord_ne : Dv.coord ⟨α, isTypeL.mem_fixSet⟩ i ≠ Dv.coord ⟨β, mem_fixSet⟩ i
  coord_eq : ∀ j, j ≠ i → Dv.coord ⟨α, isTypeL.mem_fixSet⟩ j = Dv.coord ⟨β, mem_fixSet⟩ j
  odd_twoPointKernel : Odd (Nat.card (twoPointKernel G Ω α β))
  D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)
  card_ι : Fintype.card D.ι = 1
  isNaturalSE_D : ∀ k, IsNaturalSE (D.M k)
  orbit_iff : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
    ∀ δ' : holtDelta G Ω α β,
      δ' ∈ orbit (jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β)) δ ↔
        (δ' : Ω) ∈ fixSet Ω (Subgroup.zpowers v)
  γ : holtDelta G Ω α β
  γ_mem : (γ : Ω) ∈ fixSet Ω (Subgroup.zpowers v)
  S : Subgroup G
  sylow : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (γ : Ω))
  v_mem : v ∈ S
  w : G
  w_mem : w ∈ longInvSwap G Ω α β
  w_fix : w • (γ : Ω) = γ
  w_comm : w ∈ Subgroup.centralizer (S : Set G)

end Config

namespace FinConfig

section Psi

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α β : Ω} {v : G}
  (C : FinConfig G Ω α β v)

include C in
theorem ne : α ≠ β := fun h =>
  C.coord_ne (congrArg (fun p => C.Dv.coord p C.i) (Subtype.ext h))

noncomputable def i₀ : C.D.ι := (Fintype.card_eq_one_iff.mp C.card_ι).choose

theorem eq_i₀ (j : C.D.ι) : j = C.i₀ := (Fintype.card_eq_one_iff.mp C.card_ι).choose_spec j

noncomputable abbrev Psi : Type := C.D.Ψc C.i₀

noncomputable abbrev N : Subgroup (Equiv.Perm C.Psi) := C.D.M C.i₀

theorem isNaturalSE_N : IsNaturalSE C.N := C.isNaturalSE_D C.i₀

noncomputable abbrev bγ : C.Psi := C.D.coord C.γ C.i₀

noncomputable abbrev Rhat : Subgroup (Equiv.Perm C.Psi) := seRadical C.N C.bγ

noncomputable abbrev Zhat : Subgroup (Equiv.Perm C.Psi) := rootCenter C.Rhat

@[expose] noncomputable def psi : stabilizer G ({α, β} : Set Ω) →* Equiv.Perm C.Psi :=
  (C.D.extRho C.eq_i₀).comp (twoPointHom G Ω α β).rangeRestrict

theorem psi_coord (g : stabilizer G ({α, β} : Set Ω)) (δ : holtDelta G Ω α β) :
    C.psi g (C.D.coord δ C.i₀) = C.D.coord (twoPointHom G Ω α β g δ) C.i₀ :=
  C.D.extRho_coord C.eq_i₀ _ δ

theorem psi_mem_normalizer (g : stabilizer G ({α, β} : Set Ω)) :
    C.psi g ∈ Subgroup.normalizer (C.N : Set (Equiv.Perm C.Psi)) :=
  C.D.extRho_mem_normalizer C.eq_i₀ _

theorem coord_i₀_eq_iff (δ δ' : holtDelta G Ω α β) :
    C.D.coord δ C.i₀ = C.D.coord δ' C.i₀ ↔
      δ' ∈ orbit (jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β)) δ := by
  rw [← C.D.coord_eq_iff]
  refine ⟨fun h => funext fun j => ?_, fun h => congrFun h C.i₀⟩
  rcases C.eq_i₀ j with rfl
  exact h

theorem coord_eq_bγ_iff (δ : holtDelta G Ω α β) :
    C.D.coord δ C.i₀ = C.bγ ↔ (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := by
  rw [eq_comm, C.coord_i₀_eq_iff]
  exact C.orbit_iff C.γ C.γ_mem δ

theorem psi_eq_one_iff (g : stabilizer G ({α, β} : Set Ω)) :
    C.psi g = 1 ↔ ∀ δ : holtDelta G Ω α β, twoPointHom G Ω α β g δ ∈
      orbit (jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β)) δ := by
  refine ⟨fun h δ => (C.coord_i₀_eq_iff _ _).mp ?_, fun h => Equiv.ext fun c => ?_⟩
  · rw [← C.psi_coord, h, Equiv.Perm.one_apply]
  · obtain ⟨δ, rfl⟩ := C.D.exists_coord_apply_eq C.i₀ c
    rw [C.psi_coord, Equiv.Perm.one_apply, eq_comm, C.coord_i₀_eq_iff]
    exact h δ

theorem psi_apply_bγ {g : stabilizer G ({α, β} : Set Ω)} (hg : (g : G) • (C.γ : Ω) = C.γ) :
    C.psi g C.bγ = C.bγ := by
  rw [C.psi_coord]
  exact congrArg (fun δ => C.D.coord δ C.i₀) (Subtype.ext hg)

noncomputable def psiPre (H : Subgroup (Equiv.Perm C.Psi)) : Subgroup G :=
  (H.comap C.psi).map (stabilizer G ({α, β} : Set Ω)).subtype

theorem mem_psiPre {H : Subgroup (Equiv.Perm C.Psi)} {g : G} :
    g ∈ C.psiPre H ↔ ∃ hg : g ∈ stabilizer G ({α, β} : Set Ω), C.psi ⟨g, hg⟩ ∈ H := by
  refine ⟨?_, fun ⟨hg, h⟩ => ⟨⟨g, hg⟩, h, rfl⟩⟩
  rintro ⟨g', hg', rfl⟩
  exact ⟨g'.2, hg'⟩

end Psi

section K

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem eq_one_of_pow_eq_one_of_odd {K : Subgroup G} (hK : Odd (Nat.card K)) {g : G}
    (hgK : g ∈ K) {k : ℕ} (hg : g ^ 2 ^ k = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hg
  have h2 : Odd (orderOf g) := hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hgK)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · rwa [pow_zero, orderOf_eq_one_iff] at hj
  · exact absurd (hj ▸ h2) (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩))

theorem eq_one_of_psi_eq_one (hS : Sec4Setting G Ω) {g : G} {k : ℕ} (hg2 : g ^ 2 ^ k = 1)
    (hg : g ∈ stabilizer G α ⊓ stabilizer G β)
    (hψ : C.psi ⟨g, stabilizer_inf_le_stabilizer_pair α β hg⟩ = 1)
    (hB : ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (Subgroup.zpowers v) → g • δ = δ) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set hgp := stabilizer_inf_le_stabilizer_pair α β hg
  have h3 : 3 ≤ Nat.card (holtDelta G Ω α β) := three_le_card_holtDelta_of_holtData hS.star C.D
  have hG' := hS.star_twoPoint C.ne h3
  set O := jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β)
  set ĝ : twoPointSection G Ω α β := twoPointElt hgp with hĝ
  have hĝ2 : ĝ ^ 2 ^ k = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hĝ, ← map_pow]
    exact (congrArg (twoPointHom G Ω α β) (Subtype.ext hg2 :
      (⟨g, hgp⟩ : stabilizer G ({α, β} : Set Ω)) ^ 2 ^ k = 1)).trans (map_one _))
  have hP : IsPGroup 2 (Subgroup.zpowers ĝ) := isPGroup_zpowers_of_pow_eq_one hĝ2
  have horb : ∀ δ : holtDelta G Ω α β, ĝ • δ ∈ orbit O δ := (C.psi_eq_one_iff _).mp hψ
  have hγF : C.γ ∈ fixSet (holtDelta G Ω α β) (Subgroup.zpowers ĝ) := by
    rw [fixSet_zpowers, mem_fixedBy]
    exact Subtype.ext (hB _ C.γ.2 C.γ_mem)
  have hfix : ∀ δ : holtDelta G Ω α β, ĝ • δ = δ := by
    intro δ
    have hstab : Subgroup.zpowers ĝ ≤ stabilizer (twoPointSection G Ω α β) (orbit O δ) := by
      rw [Subgroup.zpowers_le, mem_stabilizer_iff, smul_orbit_eq_orbit_smul, orbit_eq_iff]
      exact horb δ
    obtain ⟨ε, hεb, hεF⟩ := exists_mem_fixSet_of_le_stabilizer hP
      (odd_card_orbit_jOddCore δ) hstab
    have := hG'.isPretransitive_centralizer hP
    obtain ⟨c, hc⟩ := exists_smul_eq (Subgroup.centralizer
      ((Subgroup.zpowers ĝ : Subgroup (twoPointSection G Ω α β)) : Set (twoPointSection G Ω α β)))
      (⟨C.γ, hγF⟩ : fixSet (holtDelta G Ω α β) (Subgroup.zpowers ĝ)) ⟨ε, hεF⟩
    have hcγ : (c : twoPointSection G Ω α β) • C.γ = ε := congrArg Subtype.val hc
    have hδ : δ ∈ (c : twoPointSection G Ω α β) • orbit O C.γ := by
      rw [smul_orbit_eq_orbit_smul, hcγ, orbit_eq_iff.mpr hεb]
      exact mem_orbit_self δ
    obtain ⟨δ₀, hδ₀, rfl⟩ := hδ
    have hδ₀B : (δ₀ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := (C.orbit_iff C.γ C.γ_mem δ₀).mp hδ₀
    have hĝδ₀ : ĝ • δ₀ = δ₀ := Subtype.ext (hB _ δ₀.2 hδ₀B)
    have hcomm : (c : twoPointSection G Ω α β) * ĝ = ĝ * c :=
      (Subgroup.mem_centralizer_iff.mp c.2 ĝ (Subgroup.mem_zpowers ĝ)).symm
    rw [← mul_smul, ← hcomm, mul_smul, hĝδ₀]
  have hK : g ∈ twoPointKernel G Ω α β := by
    refine mem_twoPointKernel.mpr ⟨(Subgroup.mem_inf.mp hg).1, (Subgroup.mem_inf.mp hg).2,
      fun δ hδ => ?_⟩
    exact congrArg Subtype.val (hfix ⟨δ, hδ⟩)
  exact eq_one_of_pow_eq_one_of_odd C.odd_twoPointKernel hK hg2

end K

section Coord

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α β : Ω} {v : G}
  (C : FinConfig G Ω α β v)

abbrev a : fixSet Ω (Subgroup.zpowers v) := ⟨α, C.isTypeL.mem_fixSet⟩

abbrev b : fixSet Ω (Subgroup.zpowers v) := ⟨β, C.mem_fixSet⟩

include C in
theorem isPGroup_zpowers : IsPGroup 2 (Subgroup.zpowers v) :=
  isPGroup_zpowers_of_orderOf_eq_two C.isTypeL.orderOf_eq_two

include C in
theorem zpowers_le_stabilizer_inf :
    Subgroup.zpowers v ≤ stabilizer G α ⊓ stabilizer G β :=
  le_inf (mem_fixSet_iff_le_stabilizer.mp C.isTypeL.mem_fixSet)
    (mem_fixSet_iff_le_stabilizer.mp C.mem_fixSet)

variable [Finite G] [Fintype Ω]

omit [Finite G] in
include C in
theorem jOddCore_Dv_eq_bot :
    jOddCore (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) = ⊥ :=
  eq_bot_iff.mpr (C.pPrimeCore_eq_bot ▸ jOddCore_le_pPrimeCore)

omit [Finite G] in
theorem coord_Dv_injective : Function.Injective C.Dv.coord := fun ω ω' h => by
  have h' := (C.Dv.coord_eq_iff ω ω').mp h
  rw [orbit_jOddCore_eq_singleton C.jOddCore_Dv_eq_bot, Set.mem_singleton_iff] at h'
  exact h'.symm

variable [DecidableEq Ω] [FaithfulSMul G Ω]

theorem exists_longInvAt_Dv (hS : Sec4Setting G Ω) {δ : Ω} (hδΔ : δ ∈ holtDelta G Ω α β)
    (hδΦ : δ ∈ fixSet Ω (Subgroup.zpowers v)) :
    ∃ π : typeLSection G Ω v, π ∈ longInvAt (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))
      (⟨δ, hδΦ⟩ : fixSet Ω (Subgroup.zpowers v)) ∧ π • C.a = C.b := by
  obtain ⟨u, hu, huδ, huV⟩ := hS.exists_mem_longInvSwap_centralizer_of_mem_holtDelta C.ne hδΔ
    C.isPGroup_zpowers C.zpowers_le_stabilizer_inf (mem_fixSet_iff_le_stabilizer.mp hδΦ)
  refine ⟨centralizerImageElt huV, ⟨(hS.mem_longInv_centralizerImage_iff C.isPGroup_zpowers
    (three_le_card_fixSet_of_isTypeL hS.star C.isTypeL) _).mpr ⟨u, hu.1, huV, fun ω => rfl⟩,
    Subtype.ext huδ⟩, Subtype.ext hu.2⟩

theorem coord_of_mem_B (hS : Sec4Setting G Ω) {δ : Ω} (hδΔ : δ ∈ holtDelta G Ω α β)
    (hδΦ : δ ∈ fixSet Ω (Subgroup.zpowers v)) :
    (∀ k, k ≠ C.i → C.Dv.coord ⟨δ, hδΦ⟩ k = C.Dv.coord C.a k) ∧
      C.Dv.coord ⟨δ, hδΦ⟩ C.i ≠ C.Dv.coord C.a C.i ∧
        C.Dv.coord ⟨δ, hδΦ⟩ C.i ≠ C.Dv.coord C.b C.i := by
  obtain ⟨π, hπ, hπab⟩ := C.exists_longInvAt_Dv hS hδΔ hδΦ
  set πH : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    ⟨π, mem_jHull_of_mem_longInv hπ.1⟩
  have hρ := fun k => C.Dv.rho_mem_longInvAt hπ k
  have hab : ∀ k, C.Dv.ρ k πH (C.Dv.coord C.a k) = C.Dv.coord C.b k := fun k => by
    rw [← C.Dv.coord_smul, ← hπab]
  have hfix : ∀ k (c : C.Dv.Ψc k), C.Dv.ρ k πH c = c → c = C.Dv.coord ⟨δ, hδΦ⟩ k := by
    intro k c hc
    obtain ⟨c₀, -, huniq⟩ := (hρ k).1.2
    exact (huniq c hc).trans (huniq _ (hρ k).2).symm
  have hinv : ∀ k (c : C.Dv.Ψc k), C.Dv.ρ k πH (C.Dv.ρ k πH c) = c := fun k c => by
    rw [← Equiv.Perm.mul_apply, mul_self_eq_one_of_mem_longInv (hρ k).1, Equiv.Perm.one_apply]
  refine ⟨fun k hk => (hfix k _ ?_).symm, fun h => C.coord_ne ?_, fun h => C.coord_ne ?_⟩
  · rw [hab k, C.coord_eq k hk]
  · rw [← hab, ← h]
    exact ((hρ C.i).2).symm
  · have h1 : C.Dv.ρ C.i πH (C.Dv.coord C.b C.i) = C.Dv.coord C.b C.i := by
      rw [← h]
      exact (hρ C.i).2
    rw [← hinv C.i (C.Dv.coord C.a C.i), hab, h1]

end Coord

section OddCore

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_centralizer_of_mem_L {l : jHull (typeLSection G Ω v)
    (fixSet Ω (Subgroup.zpowers v))} (hl : ((l : typeLSection G Ω v)) ∈ C.Dv.L C.i)
    (hla : C.Dv.ρ C.i l (C.Dv.coord C.a C.i) = C.Dv.coord C.a C.i)
    (hlb : C.Dv.ρ C.i l (C.Dv.coord C.b C.i) = C.Dv.coord C.b C.i) :
    ∃ c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G),
      c ∈ stabilizer G α ⊓ stabilizer G β ∧
        ∀ ω : fixSet Ω (Subgroup.zpowers v), ∃ hω : c • (ω : Ω) ∈ fixSet Ω (Subgroup.zpowers v),
          C.Dv.coord ⟨c • (ω : Ω), hω⟩ = Function.update (C.Dv.coord ω) C.i
            (C.Dv.ρ C.i l (C.Dv.coord ω C.i)) := by
  obtain ⟨c, hc, hcl⟩ := mem_centralizerImage.mp ((l : typeLSection G Ω v)).2
  have hcoord : ∀ ω : fixSet Ω (Subgroup.zpowers v),
      C.Dv.coord ((l : typeLSection G Ω v) • ω) = Function.update (C.Dv.coord ω) C.i
        (C.Dv.ρ C.i l (C.Dv.coord ω C.i)) := fun ω => funext fun k => by
    rw [C.Dv.coord_smul]
    rcases eq_or_ne k C.i with rfl | hk
    · rw [Function.update_self]
    · rw [Function.update_of_ne hk, C.Dv.rho_eq_one_of_mem_L (Ne.symm hk) hl,
        Equiv.Perm.one_apply]
  have hfix : ∀ ω : fixSet Ω (Subgroup.zpowers v),
      C.Dv.ρ C.i l (C.Dv.coord ω C.i) = C.Dv.coord ω C.i → c • (ω : Ω) = ω := fun ω h => by
    rw [← hcl ω]
    refine congrArg Subtype.val (C.coord_Dv_injective ?_)
    change C.Dv.coord ((l : typeLSection G Ω v) • ω) = C.Dv.coord ω
    rw [hcoord, h, Function.update_eq_self]
  refine ⟨c, hc, Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr (hfix C.a hla),
    mem_stabilizer_iff.mpr (hfix C.b hlb)⟩, fun ω => ?_⟩
  have h := hcl ω
  refine ⟨h ▸ (((l : typeLSection G Ω v) : Equiv.Perm _) ω).2, ?_⟩
  rw [← hcoord ω]
  exact congrArg C.Dv.coord (Subtype.ext h.symm)

theorem exists_mem_B_ne_γ (hS : Sec4Setting G Ω) :
    ∃ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧ δ ≠ C.γ := by
  obtain ⟨π, hπ, hπab⟩ := C.exists_longInvAt_Dv hS C.γ.2 C.γ_mem
  set γ' : fixSet Ω (Subgroup.zpowers v) := ⟨C.γ, C.γ_mem⟩
  set πH : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    ⟨π, mem_jHull_of_mem_longInv hπ.1⟩
  have hM := C.isNaturalSE_Dv C.i
  obtain ⟨n, ii, e, hA⟩ := hM.exists_isBenderAction
  have hρM : C.Dv.ρ C.i πH ∈ C.Dv.M C.i := C.Dv.rho_mem_M_of_isNaturalSE hM πH
  have hρ := C.Dv.rho_mem_longInvAt hπ C.i
  have hγi : C.Dv.coord γ' C.i ∈ holtDelta (C.Dv.M C.i) (C.Dv.Ψc C.i)
      (C.Dv.coord C.a C.i) (C.Dv.coord C.b C.i) := by
    refine ⟨⟨_, hρM⟩, ⟨mem_longInv_subgroup_iff.mpr hρ.1, ?_⟩, hρ.2⟩
    change C.Dv.ρ C.i πH (C.Dv.coord C.a C.i) = C.Dv.coord C.b C.i
    rw [← C.Dv.coord_smul, ← hπab]
  have horb := hA.holtDelta_eq_orbit_of_mem C.coord_ne hγi
  have hcard := hA.ncard_holtDelta C.coord_ne
  obtain ⟨d, hd⟩ : ∃ d : ↥(stabilizer (C.Dv.M C.i) (C.Dv.coord C.a C.i) ⊓
      stabilizer (C.Dv.M C.i) (C.Dv.coord C.b C.i)), d • C.Dv.coord γ' C.i ≠ C.Dv.coord γ' C.i := by
    by_contra! h
    have hsub : holtDelta (C.Dv.M C.i) (C.Dv.Ψc C.i) (C.Dv.coord C.a C.i)
        (C.Dv.coord C.b C.i) ⊆ {C.Dv.coord γ' C.i} := by
      rw [horb]
      rintro x ⟨d, rfl⟩
      exact h d
    have h1 := (Set.ncard_le_ncard hsub (Set.finite_singleton _)).trans_eq (Set.ncard_singleton _)
    rw [hcard] at h1
    have := hA.four_le_q
    omega
  obtain ⟨l, hl, hld⟩ := C.Dv.mem_M.mp ((d : C.Dv.M C.i)).2
  have hda := (Subgroup.mem_inf.mp d.2).1
  have hdb := (Subgroup.mem_inf.mp d.2).2
  rw [mem_stabilizer_iff] at hda hdb
  obtain ⟨c, -, hcαβ, hcω⟩ := C.exists_centralizer_of_mem_L hl (by rw [hld]; exact hda)
    (by rw [hld]; exact hdb)
  obtain ⟨hcγ, hcγ'⟩ := hcω γ'
  refine ⟨⟨c • (C.γ : Ω), smul_mem_holtDelta_of_mem_inf hcαβ C.γ.2⟩, hcγ, fun h => hd ?_⟩
  have h2 := congrFun hcγ' C.i
  rw [Function.update_self] at h2
  have h0 : c • (C.γ : Ω) = C.γ := congrArg (fun x : holtDelta G Ω α β => (x : Ω)) h
  have h3 : (⟨c • (C.γ : Ω), hcγ⟩ : fixSet Ω (Subgroup.zpowers v)) = γ' := Subtype.ext h0
  rw [h3, hld] at h2
  exact h2.symm

include C in
theorem jOddCore_D_ne_bot (hS : Sec4Setting G Ω) :
    jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) ≠ ⊥ := by
  intro hO
  obtain ⟨δ, hδΦ, hδγ⟩ := C.exists_mem_B_ne_γ hS
  have h := (C.orbit_iff C.γ C.γ_mem δ).mpr hδΦ
  rw [orbit_jOddCore_eq_singleton hO, Set.mem_singleton_iff] at h
  exact hδγ h

end OddCore

section Parity

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem psi_eq_extRho {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) :
    C.psi ⟨g, hg⟩ = C.D.extRho C.eq_i₀ (twoPointElt hg) := rfl

omit [FaithfulSMul G Ω] in
theorem psi_eq_rho (hS : Sec4Setting G Ω) {g : G}
    (hg : g ∈ Subgroup.closure (longInvSwap G Ω α β)) :
    C.psi ⟨g, closure_longInvSwap_le_stabilizer_pair α β hg⟩ =
      C.D.ρ C.i₀ ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α β hg),
        twoPointElt_mem_jHull hS.star hg⟩ :=
  (C.psi_eq_extRho _).trans
    (C.D.extRho_eq_rho C.eq_i₀ ⟨_, twoPointElt_mem_jHull hS.star hg⟩)

omit [FaithfulSMul G Ω] in
theorem psi_mem_N (hS : Sec4Setting G Ω) {g : G}
    (hg : g ∈ Subgroup.closure (longInvSwap G Ω α β)) :
    C.psi ⟨g, closure_longInvSwap_le_stabilizer_pair α β hg⟩ ∈ C.N := by
  rw [C.psi_eq_rho hS hg]
  exact C.D.rho_mem_M_of_isNaturalSE C.isNaturalSE_N _

theorem t_not_mem_socPre (hS : Sec4Setting G Ω) : C.D.t ∉ C.D.socPre := fun ht =>
  C.jOddCore_D_ne_bot hS (C.D.t_mem_socPre_iff.mp ht).1

theorem index_socPre (hS : Sec4Setting G Ω) :
    (C.D.socPre.subgroupOf (jHull (twoPointSection G Ω α β) (holtDelta G Ω α β))).index = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp C.D.relIndex_socPre_jHull_dvd_two with h1 | h2
  · exact absurd (Subgroup.relIndex_eq_one.mp h1 (mem_jHull_of_mem_longInv C.D.t_mem))
      (C.t_not_mem_socPre hS)
  · exact h2

theorem mul_mem_socPre_iff (hS : Sec4Setting G Ω) {x y : twoPointSection G Ω α β}
    (hx : x ∈ jHull (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (hy : y ∈ jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)) :
    x * y ∈ C.D.socPre ↔ (x ∈ C.D.socPre ↔ y ∈ C.D.socPre) := by
  have h := Subgroup.mul_mem_iff_of_index_two (C.index_socPre hS) (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using h

theorem not_mem_socPre_of_mem_longInv (hS : Sec4Setting G Ω) {u : twoPointSection G Ω α β}
    (hu : u ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β)) : u ∉ C.D.socPre := by
  intro hus
  have h3 := three_le_card_holtDelta_of_holtData hS.star C.D
  obtain ⟨h, hh, rfl⟩ := exists_mem_jHull_conj_eq (hS.star_twoPoint C.ne h3)
    (hS.holtTheorem1Below_twoPoint h3) C.D.t_mem hu
  have h1 := C.D.conj_mem_socPre (inv_mem hh) hus
  rw [show h⁻¹ * (h * C.D.t * h⁻¹) * h⁻¹⁻¹ = C.D.t by group] at h1
  exact C.t_not_mem_socPre hS h1

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
include C in
theorem mul_smul_eq_iff {x y : G} (hx : x ∈ stabilizer G ({α, β} : Set Ω))
    (hy : y ∈ stabilizer G ({α, β} : Set Ω)) :
    (x * y) • α = α ↔ (x • α = α ↔ y • α = α) := by
  have hαβ := C.ne
  rcases smul_pair_of_mem_stabilizer_pair hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;>
    rcases smul_pair_of_mem_stabilizer_pair hy with ⟨hy1, -⟩ | ⟨hy1, -⟩ <;>
    rw [mul_smul, hy1]
  · simp [hx1]
  · simp [hx1, hx2, hαβ.symm]
  · simp [hx1, hαβ.symm]
  · simp [hx1, hx2]

theorem smul_eq_iff_mem_socPre (hS : Sec4Setting G Ω) {g : G}
    (hg : g ∈ Subgroup.closure (longInvSwap G Ω α β)) :
    g • α = α ↔ twoPointElt (closure_longInvSwap_le_stabilizer_pair α β hg) ∈ C.D.socPre := by
  have h3 := three_le_card_holtDelta_of_holtData hS.star C.D
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    have hxJ : twoPointElt (closure_longInvSwap_le_stabilizer_pair α β
        (Subgroup.subset_closure hx)) ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
      (hS.mem_longInv_twoPointSection_iff C.ne h3 _).mpr ⟨x, hx, fun δ => rfl⟩
    exact iff_of_false (fun h => C.ne (h.symm.trans hx.2)) (C.not_mem_socPre_of_mem_longInv hS hxJ)
  | one =>
    refine iff_of_true (one_smul G α) ?_
    rw [show twoPointElt (G := G) (α := α) (β := β) (closure_longInvSwap_le_stabilizer_pair α β
      (one_mem _)) = 1 from Subtype.ext (map_one (twoPointHom G Ω α β))]
    exact one_mem _
  | mul x y hx hy ihx ihy =>
    rw [show twoPointElt (closure_longInvSwap_le_stabilizer_pair α β (mul_mem hx hy)) =
      twoPointElt (closure_longInvSwap_le_stabilizer_pair α β hx) *
        twoPointElt (closure_longInvSwap_le_stabilizer_pair α β hy) from
      Subtype.ext (map_mul (twoPointHom G Ω α β) ⟨x, _⟩ ⟨y, _⟩),
      C.mul_mem_socPre_iff hS (twoPointElt_mem_jHull hS.star hx)
        (twoPointElt_mem_jHull hS.star hy)]
    exact (C.mul_smul_eq_iff (closure_longInvSwap_le_stabilizer_pair α β hx)
      (closure_longInvSwap_le_stabilizer_pair α β hy)).trans (iff_congr ihx ihy)
  | inv x hx ih =>
    rw [show twoPointElt (closure_longInvSwap_le_stabilizer_pair α β (inv_mem hx)) =
      (twoPointElt (closure_longInvSwap_le_stabilizer_pair α β hx))⁻¹ from
      Subtype.ext (map_inv (twoPointHom G Ω α β) ⟨x, _⟩), inv_mem_iff, inv_smul_eq_iff,
      eq_comm]
    exact ih

theorem eq_one_of_psi_eq_one' (hS : Sec4Setting G Ω) {g : G} {k : ℕ} (hg2 : g ^ 2 ^ k = 1)
    (hgJ : g ∈ Subgroup.closure (longInvSwap G Ω α β)) (hgα : g • α = α)
    (hψ : C.psi ⟨g, closure_longInvSwap_le_stabilizer_pair α β hgJ⟩ = 1) : g = 1 := by
  set hgp := closure_longInvSwap_le_stabilizer_pair α β hgJ
  have hĝH := twoPointElt_mem_jHull hS.star hgJ
  have hĝS := (C.smul_eq_iff_mem_socPre hS hgJ).mp hgα
  rw [C.psi_eq_rho hS hgJ] at hψ
  have hK : twoPointElt hgp ∈ jOrbitKernel (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    (C.D.mem_jOrbitKernel_iff_rho (h := ⟨_, hĝH⟩)).mpr fun j => by rw [C.eq_i₀ j]; exact hψ
  have hO : twoPointElt hgp ∈ jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) := by
    rw [← C.D.socPre_inf_jOrbitKernel]
    exact ⟨hĝS, hK⟩
  have hĝ2 : twoPointElt hgp ^ 2 ^ k = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, ← map_pow]
    exact (congrArg (twoPointHom G Ω α β) (Subtype.ext hg2 :
      (⟨g, hgp⟩ : stabilizer G ({α, β} : Set Ω)) ^ 2 ^ k = 1)).trans (map_one _))
  have hĝ1 := eq_one_of_pow_eq_one_of_odd odd_card_jOddCore hO hĝ2
  have hgβ : g • β = β := by
    rcases smul_pair_of_mem_stabilizer_pair hgp with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd (hgα.symm.trans h) C.ne
  refine eq_one_of_pow_eq_one_of_odd C.odd_twoPointKernel (mem_twoPointKernel.mpr
    ⟨hgα, hgβ, fun δ hδ => ?_⟩) hg2
  have h := congrArg (fun π : twoPointSection G Ω α β =>
    (((π : Equiv.Perm (holtDelta G Ω α β)) ⟨δ, hδ⟩ : holtDelta G Ω α β) : Ω)) hĝ1
  exact h

end Parity

end FinConfig

end CFSG.Holt.H78
