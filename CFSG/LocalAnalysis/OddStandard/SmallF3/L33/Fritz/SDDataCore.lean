module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDH8
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2ActModel
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSylow
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.OddStandard.SmallF3.L33.KD

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.HSFLit

structure SDConfig {X : Type} [Group X] (t : X) (L : Subgroup X) : Prop where
  orderOf_eq : orderOf t = 2
  le_centralizer : L ≤ centralizer ({t} : Set X)
  le_normalizer : centralizer ({t} : Set X) ≤ normalizer (L : Set X)
  pPrimeCore_eq_bot : pPrimeCore 2 ↥L = ⊥
  center_eq_bot : center ↥L = ⊥
  isCyclic : ∀ P : Sylow 2 ↥(centralizer (L : Set X)),
    IsCyclic (P : Subgroup ↥(centralizer (L : Set X)))

namespace SDConfig

variable {X : Type} [Group X] {t : X} {L : Subgroup X}

theorem not_mem (h : SDConfig t L) : t ∉ L := by
  intro htL
  have hc : (⟨t, htL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (h.le_centralizer g.2)
  rw [h.center_eq_bot, mem_bot] at hc
  have h1 : t = 1 := congrArg Subtype.val hc
  have h2 := h.orderOf_eq
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem mem_sylow (h : SDConfig t L) (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    t ∈ Config.sylowIn T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : centralizer ({t} : Set X) := ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ with ht'
  have hcen : ∀ c : centralizer ({t} : Set X), c * t' = t' * c := fun c =>
    Subtype.ext (mem_centralizer_singleton_iff.mp c.2)
  have hn : (zpowers t').Normal := by
    refine ⟨fun n hn c => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    rw [show c * t' ^ k * c⁻¹ = t' ^ k by rw [((Commute.zpow_right (hcen c) k)).eq]; group]
    exact zpow_mem (mem_zpowers t') k
  have hp : IsPGroup 2 (zpowers t') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht', Subgroup.orderOf_mk, h.orderOf_eq, pow_one])
  exact ⟨t', hp.le_sylow_of_normal T (mem_zpowers t'), rfl⟩

theorem commute_kernel (h : SDConfig t L) {l c : X} (hl : l ∈ L) (hc : c ∈ coreActionKernel L) :
    l * c = c * l := by
  have h1 := hc.2 l hl
  rw [h.pPrimeCore_eq_bot, Subgroup.map_bot, mem_bot] at h1
  calc l * c = c * (c⁻¹ * l * c) := by group
    _ = c * l := by
      congr 1
      have h2 : l⁻¹ * (c⁻¹ * l * c) = 1 := by rw [← h1]; group
      exact (inv_mul_eq_one.mp h2).symm

theorem inf_kernel (h : SDConfig t L) : L ⊓ coreActionKernel L = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgL, hgC⟩
  have hc : (⟨g, hgL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro j
    apply Subtype.ext
    exact h.commute_kernel j.2 hgC
  rw [h.center_eq_bot, mem_bot] at hc
  exact congrArg Subtype.val hc

theorem t_mem_kernel (h : SDConfig t L) : t ∈ coreActionKernel L := by
  refine ⟨h.le_normalizer (mem_centralizer_singleton_iff.mpr rfl), fun j hj => ?_⟩
  have hjt : j * t = t * j := mem_centralizer_singleton_iff.mp (h.le_centralizer hj)
  have h1 : j⁻¹ * t⁻¹ * j * t = 1 := by
    calc j⁻¹ * t⁻¹ * j * t = j⁻¹ * t⁻¹ * (j * t) := by group
      _ = j⁻¹ * t⁻¹ * (t * j) := by rw [hjt]
      _ = 1 := by group
  rw [h1]
  exact one_mem _

theorem isCyclic_inf_kernel (h : SDConfig t L) (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    IsCyclic (Config.sylowIn T ⊓ coreActionKernel L : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := (Config.sylowIn T ⊓ coreActionKernel L : Subgroup X) with hK
  have hKC : K ≤ centralizer (L : Set X) := fun g hg =>
    mem_centralizer_iff.mpr fun l hl => h.commute_kernel hl hg.2
  have hK2 : IsPGroup 2 (K.subgroupOf (centralizer (L : Set X))) :=
    ((Config.isPGroup_sylowIn T).to_inf_left).comap_of_injective _ (subtype_injective _)
  obtain ⟨P, hP⟩ := hK2.exists_le_sylow
  have hPc := h.isCyclic P
  have : IsCyclic (K.subgroupOf (centralizer (L : Set X))) := Subgroup.isCyclic_of_le hP
  exact (subgroupOfEquivOfLe hKC).isCyclic.mp this

theorem mem_inf_kernel (h : SDConfig t L) (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    t ∈ (Config.sylowIn T ⊓ coreActionKernel L : Subgroup X) :=
  ⟨h.mem_sylow T, h.t_mem_kernel⟩

theorem inf_kernel_inf_L (h : SDConfig t L) (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    (Config.sylowIn T ⊓ coreActionKernel L ⊓ L : Subgroup X) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨_, hgK⟩, hgL⟩
  rw [mem_bot]
  have := h.inf_kernel
  have hg : g ∈ L ⊓ coreActionKernel L := ⟨hgL, hgK⟩
  rw [this, mem_bot] at hg
  exact hg

end SDConfig

variable {X : Type} [Group X]

structure SDData (t : X) (L : Subgroup X) where
  config : SDConfig t L
  syl : Sylow 2 ↥(centralizer ({t} : Set X))
  ψ : ↥(Config.sylowIn syl) →* Perm (ZMod 8)
  ψ_eq_one_iff : ∀ g : ↥(Config.sylowIn syl), ψ g = 1 ↔ (g : X) ∈ coreActionKernel L
  ψ_mem_H8 : ∀ g : ↥(Config.sylowIn syl), ψ g ∈ H8
  ψ_mem_S16 : ∀ g : ↥(Config.sylowIn syl), (g : X) ∈ L → ψ g ∈ SD.S16
  exists_ψ_eq : ∀ σ ∈ SD.S16, ∃ g : ↥(Config.sylowIn syl), (g : X) ∈ L ∧ ψ g = σ

namespace SDData

variable {t : X} {L : Subgroup X} (A : SDData t L)

abbrev T : Subgroup X := Config.sylowIn A.syl

abbrev K : Subgroup X := A.T ⊓ coreActionKernel L

@[expose] def D : Subgroup X := L ⊓ (R8.comap A.ψ).map A.T.subtype

abbrev R : Subgroup X := A.T ⊓ A.D

theorem mem_D {g : X} (hg : g ∈ A.T) : g ∈ A.D ↔ g ∈ L ∧ A.ψ ⟨g, hg⟩ ∈ R8 := by
  constructor
  · rintro ⟨hL, ⟨g', hg', rfl⟩⟩
    exact ⟨hL, hg'⟩
  · rintro ⟨hL, h⟩
    exact ⟨hL, ⟨g, hg⟩, h, rfl⟩

theorem mem_R {g : X} : g ∈ A.R ↔ ∃ hg : g ∈ A.T, g ∈ L ∧ A.ψ ⟨g, hg⟩ ∈ R8 :=
  ⟨fun h => ⟨h.1, (A.mem_D h.1).mp h.2⟩, fun ⟨hg, h⟩ => ⟨hg, (A.mem_D hg).mpr h⟩⟩

theorem R_le_L : A.R ≤ L := fun _ h => h.2.1

include A in
theorem orderOf_t : orderOf t = 2 := A.config.orderOf_eq

theorem t_mem_T : t ∈ A.T := A.config.mem_sylow A.syl

theorem t_mem_K : t ∈ A.K := A.config.mem_inf_kernel A.syl

instance isCyclic_K : IsCyclic A.K := A.config.isCyclic_inf_kernel A.syl

theorem T_le_centralizer : A.T ≤ centralizer ({t} : Set X) := Config.sylowIn_le _

theorem isPGroup_T : IsPGroup 2 A.T := Config.isPGroup_sylowIn _

theorem commute_t {g : X} (hg : g ∈ A.T) : g * t = t * g :=
  mem_centralizer_singleton_iff.mp (A.T_le_centralizer hg)

theorem K_inf_L : A.K ⊓ L = ⊥ := A.config.inf_kernel_inf_L A.syl

theorem mem_K_iff {g : X} (hg : g ∈ A.T) : g ∈ A.K ↔ A.ψ ⟨g, hg⟩ = 1 := by
  rw [A.ψ_eq_one_iff]
  exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

theorem ψ_mem_R8' {g : X} (hg : g ∈ A.R) : A.ψ ⟨g, hg.1⟩ ∈ R8 := ((A.mem_R).mp hg).2.2

theorem eq_of_ψ_eq_of_mem_L [Finite X] {g₁ g₂ : X} (h₁ : g₁ ∈ A.T) (h₂ : g₂ ∈ A.T)
    (hL₁ : g₁ ∈ L) (hL₂ : g₂ ∈ L) (h : A.ψ ⟨g₁, h₁⟩ = A.ψ ⟨g₂, h₂⟩) : g₁ = g₂ := by
  have hm : g₁⁻¹ * g₂ ∈ A.T := mul_mem (inv_mem h₁) h₂
  have hK : g₁⁻¹ * g₂ ∈ A.K := by
    rw [A.mem_K_iff hm]
    have : (⟨g₁⁻¹ * g₂, hm⟩ : A.T) = (⟨g₁, h₁⟩ : A.T)⁻¹ * ⟨g₂, h₂⟩ := rfl
    rw [this, map_mul, map_inv, h, inv_mul_cancel]
  have : g₁⁻¹ * g₂ ∈ A.K ⊓ L := ⟨hK, L.mul_mem (L.inv_mem hL₁) hL₂⟩
  rw [A.K_inf_L, mem_bot, inv_mul_eq_one] at this
  exact this

theorem eq_of_ψ_eq [Finite X] {g₁ g₂ : X} (h₁ : g₁ ∈ A.R) (h₂ : g₂ ∈ A.R)
    (h : A.ψ ⟨g₁, h₁.1⟩ = A.ψ ⟨g₂, h₂.1⟩) : g₁ = g₂ :=
  A.eq_of_ψ_eq_of_mem_L h₁.1 h₂.1 h₁.2.1 h₂.2.1 h

theorem exists_mem_R_ψ_eq {σ : Perm (ZMod 8)} (hσ : σ ∈ R8) :
    ∃ r : X, ∃ hr : r ∈ A.R, A.ψ ⟨r, hr.1⟩ = σ := by
  obtain ⟨g, hgL, hgσ⟩ := A.exists_ψ_eq σ (SD.R8_le_S16 hσ)
  exact ⟨g, ⟨g.2, (A.mem_D g.2).mpr ⟨hgL, hgσ ▸ hσ⟩⟩, hgσ⟩

theorem card_R [Finite X] : Nat.card A.R = 8 := by
  have hbij : Function.Bijective
      (fun r : A.R => (⟨A.ψ ⟨r.1, r.2.1⟩, A.ψ_mem_R8' r.2⟩ : R8)) := by
    constructor
    · intro r s h
      exact Subtype.ext (A.eq_of_ψ_eq r.2 s.2 (congrArg Subtype.val h))
    · rintro ⟨σ, hσ⟩
      obtain ⟨r, hr, hrσ⟩ := A.exists_mem_R_ψ_eq hσ
      exact ⟨⟨r, hr⟩, Subtype.ext hrσ⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), L2Act.card_R8]

theorem card_T_eq : Nat.card A.T = Nat.card A.ψ.range * Nat.card A.K := by
  have hker : A.ψ.ker = A.K.subgroupOf A.T := by
    ext g
    rw [MonoidHom.mem_ker, A.ψ_eq_one_iff, mem_subgroupOf]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  rw [← Subgroup.card_mul_index A.ψ.ker, Subgroup.index_ker, hker,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : A.K ≤ A.T)).toEquiv, mul_comm]

theorem R8_le_range : R8 ≤ A.ψ.range := by
  intro σ hσ
  obtain ⟨g, -, hg⟩ := A.exists_ψ_eq σ (SD.R8_le_S16 hσ)
  exact ⟨g, hg⟩

theorem S16_le_range : SD.S16 ≤ A.ψ.range := by
  intro σ hσ
  obtain ⟨g, -, hg⟩ := A.exists_ψ_eq σ hσ
  exact ⟨g, hg⟩

theorem range_le_H8 : A.ψ.range ≤ H8 := by
  rintro _ ⟨g, rfl⟩
  exact A.ψ_mem_H8 g

variable [Finite X]

theorem eq_t_of_mem_K {k : X} (hk : k ∈ A.K) (hk2 : k ^ 2 = 1) (hk1 : k ≠ 1) : k = t := by
  classical
  have : Fintype A.K := Fintype.ofFinite _
  have ho : orderOf k = 2 := orderOf_eq_prime hk2 hk1
  have hk' : orderOf (⟨k, hk⟩ : A.K) = 2 := by rw [Subgroup.orderOf_mk, ho]
  have ht' : orderOf (⟨t, A.t_mem_K⟩ : A.K) = 2 := by rw [Subgroup.orderOf_mk, A.orderOf_t]
  have hd : 2 ∣ Fintype.card A.K := by
    rw [← hk', ← Nat.card_eq_fintype_card]
    exact orderOf_dvd_natCard _
  have h1 := IsCyclic.card_orderOf_eq_totient hd
  rw [Nat.totient_two] at h1
  have := Finset.card_le_one.mp h1.le ⟨k, hk⟩ (by simp [hk']) ⟨t, A.t_mem_K⟩ (by simp [ht'])
  exact congrArg Subtype.val this

end SDData

end CFSG.OddStandard.SmallF3.L33.KD
