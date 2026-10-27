module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43Fac
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12Cfg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Blueprint
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Aux

variable {T : Type} [Group T]

private def m12facSub (H N : Subgroup T) (hHN : H ≤ Subgroup.normalizer (N : Set T)) (X : Set T) :
    Subgroup T where
  carrier := {y | y ∈ H ∧ ∀ x ∈ X, x * y * x⁻¹ * y⁻¹ ∈ N}
  mul_mem' {a b} ha hb := by
    refine ⟨H.mul_mem ha.1 hb.1, fun x hx => ?_⟩
    have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact N.mul_mem (ha.2 x hx) ((Subgroup.mem_normalizer_iff.mp (hHN ha.1) _).mp (hb.2 x hx))
  one_mem' := ⟨H.one_mem, fun x _ => by simp⟩
  inv_mem' {a} ha := by
    refine ⟨H.inv_mem ha.1, fun x hx => ?_⟩
    have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem ha.1)) _).mp (N.inv_mem (ha.2 x hx))

private theorem mem_m12facSub {H N : Subgroup T} {hHN : H ≤ Subgroup.normalizer (N : Set T)}
    {X : Set T} {y : T} :
    y ∈ m12facSub H N hHN X ↔ y ∈ H ∧ ∀ x ∈ X, x * y * x⁻¹ * y⁻¹ ∈ N :=
  Iff.rfl

private theorem m12fac_hsN (K : Subgroup T) :
    sigmaGen K ≤ Subgroup.normalizer (oddCoreOf (sigmaGen K) : Set T) := fun _ hg =>
  mem_normalizer_iff_conjSub_eq.mpr
    (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer hg))

private theorem m12fac_le_firstFactor {K L : Subgroup T}
    (hL : L ∈ aStar (CoreAssembly.conjClass K) K) : L ≤ firstFactor K :=
  (le_omegaGen hL).trans le_sup_left

private theorem m12fac_conjSub_firstFactor_le {K X : Subgroup T} {m : T}
    (hA : ∀ L ∈ aStar (CoreAssembly.conjClass K) K, ∀ w ∈ L, m * w * m⁻¹ ∈ X)
    (hN : ∀ w ∈ oddCoreOf (sigmaGen K), m * w * m⁻¹ ∈ X) :
    conjSub m (firstFactor K) ≤ X := by
  have hle : firstFactor K ≤ X.comap (MulAut.conj m).toMonoidHom :=
    sup_le (iSup₂_le fun L hL w hw => hA L hL w hw) (fun w hw => hN w hw)
  intro y hy
  have h := hle (mem_conjSub_iff.mp hy)
  rw [Subgroup.mem_comap] at h
  have e : (MulAut.conj m).toMonoidHom (m⁻¹ * y * m) = y := by
    show m * (m⁻¹ * y * m) * m⁻¹ = y
    group
  rwa [e] at h

private theorem m12fac_mem_conjStab {Ω : Set (Subgroup T)} (hΩ : ConjInvariant Ω)
    {K L : Subgroup T} (hK : K ∈ Ω) (hL : L ∈ aStar Ω K) {g : T}
    (hgL : conjSub g L ∈ aStar Ω K) : g ∈ conjStab (aStar Ω K) := by
  have hKg : conjSub g K ∈ aStar Ω K := hgL.trans (aStar_conj hΩ (mem_aStar_symm hK hL).2 g)
  have hKg' : K ∈ aStar Ω (conjSub g K) := (mem_aStar_symm hK hKg).2
  rw [mem_conjStab_iff]
  intro M
  constructor
  · intro hM
    have h1 : conjSub g M ∈ aStar Ω (conjSub g K) := hKg'.trans hM
    have h2 := aStar_conj hΩ h1 g⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2
  · intro hM
    exact hKg.trans (aStar_conj hΩ hM g)

private theorem m12fac_sq_comm {K : Subgroup T} {z : T} (hu : IsUniqueInvolution K z) {g : T}
    {L : Subgroup T} (hg : conjSub g K = L) {a : T} (ha : a ∈ L) (ha4 : orderOf a = 4) :
    ∀ x ∈ L, a * a * x = x * (a * a) := by
  have hL : IsUniqueInvolution L (g * z * g⁻¹) := hg ▸ hu.conj g
  have h4 : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
  have haa : a * a = g * z * g⁻¹ := by
    rcases hL.unique (a * a) (L.mul_mem ha ha) (by rw [← pow_two a, ← pow_add]; exact h4) with h | h
    · exfalso
      have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [ha4] at h2
      norm_num at h2
    · exact h
  intro x hx
  have hx' : x * (g * z * g⁻¹) * x⁻¹ = g * z * g⁻¹ := hL.conj_eq (conjSub_eq_self_of_mem hx)
  rw [haa]
  calc g * z * g⁻¹ * x = x * (g * z * g⁻¹) * x⁻¹ * x := by rw [hx']
    _ = x * (g * z * g⁻¹) := by group

private theorem m12fac_conj_eq_inv {G : Type*} [Group G]
    (hnc : ∀ k d : G, orderOf k = 4 → orderOf d = 3 → k * d ≠ d * k) {d w : G}
    (hd : orderOf d = 3) (hw : orderOf w = 4) (hwd : w * d * w⁻¹ ∈ Subgroup.zpowers d) :
    w * d * w⁻¹ = d⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwd
  rw [← zpow_mod_orderOf, hd] at hk
  have hd3 : d ^ 3 = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
  have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk3 with h | h | h <;> rw [h] at hk
  · exfalso
    rw [zpow_zero] at hk
    have hd1 : d = 1 := by
      calc d = w⁻¹ * (w * d * w⁻¹) * w := by group
        _ = 1 := by rw [← hk]; group
    rw [hd1, orderOf_one] at hd
    norm_num at hd
  · exfalso
    rw [zpow_one] at hk
    refine hnc w d hw hd ?_
    calc w * d = (w * d * w⁻¹) * w := by group
      _ = d * w := by rw [← hk]
  · rw [← hk, zpow_two, eq_inv_iff_mul_eq_one, ← pow_three', hd3]

private theorem m12fac_eq_bot {G : Type*} [Group G]
    (hnc : ∀ k d : G, orderOf k = 4 → orderOf d = 3 → k * d ≠ d * k) {D : Subgroup G}
    (hD : Nat.card D ∣ 3) {α β : G} (hα : orderOf α = 4) (hβ : orderOf β = 4)
    (hαβ : orderOf (α * β) = 4) (hDα : ∀ d ∈ D, α * d * α⁻¹ ∈ D)
    (hDβ : ∀ d ∈ D, β * d * β⁻¹ ∈ D) : D = ⊥ := by
  rcases (Nat.dvd_prime Nat.prime_three).mp hD with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have : Finite D := Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := D)).mp (by
      intro hbot
      rw [hbot, Subgroup.card_bot] at h3
      omega)
    have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
    have hd3 : orderOf d = 3 := by
      have hdvd : orderOf d ∣ 3 := h3 ▸ Subgroup.orderOf_dvd_natCard D hdD
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hd1'
      · exact h
    have hDz : Subgroup.zpowers d = D :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdD)
        (by rw [Nat.card_zpowers, hd3, h3])
    have hαd : α * d * α⁻¹ = d⁻¹ :=
      m12fac_conj_eq_inv hnc hd3 hα (by rw [hDz]; exact hDα d hdD)
    have hβd : β * d * β⁻¹ = d⁻¹ :=
      m12fac_conj_eq_inv hnc hd3 hβ (by rw [hDz]; exact hDβ d hdD)
    apply hnc (α * β) d hαβ hd3
    calc α * β * d = α * (β * d * β⁻¹) * α⁻¹ * (α * β) := by group
      _ = (α * d * α⁻¹)⁻¹ * (α * β) := by rw [hβd]; group
      _ = d * (α * β) := by rw [hαd, inv_inv]

variable [Finite T]

private theorem m12fac_exists_four {K : Subgroup T} {z : T} (hd : FrameTightDatum K z) {g : T}
    {L : Subgroup T} (hg : conjSub g K = L) :
    ∃ a b : T, a ∈ L ∧ b ∈ L ∧ orderOf a = 4 ∧ orderOf b = 4 ∧ orderOf (a * b) = 4 := by
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup T))
    (bot_le : (⊥ : Subgroup T) ≤ K)
  obtain ⟨e⟩ := hd.quat R₀ hR₀
  have hmem : ∀ c : ↥R₀, g * (c : T) * g⁻¹ ∈ L := fun c => hg ▸ conj_mem_conjSub (hR₀.1 c.2)
  have hord : ∀ c : ↥R₀, orderOf (g * (c : T) * g⁻¹) = orderOf c := by
    intro c
    have e1 : g * (c : T) * g⁻¹ = MulAut.conj g (c : T) := by rw [MulAut.conj_apply]
    rw [e1, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
  refine ⟨g * (e.symm (QuaternionGroup.a 1) : T) * g⁻¹,
    g * (e.symm (QuaternionGroup.xa 0) : T) * g⁻¹, hmem _, hmem _, ?_, ?_, ?_⟩
  · rw [hord, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
  · rw [hord, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]
  · have e2 : g * (e.symm (QuaternionGroup.a 1) : T) * g⁻¹ *
        (g * (e.symm (QuaternionGroup.xa 0) : T) * g⁻¹) =
        g * ((e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) : ↥R₀) : T) * g⁻¹ := by
      rw [Subgroup.coe_mul]
      group
    rw [e2, hord, ← map_mul, MulEquiv.orderOf_eq, QuaternionGroup.a_mul_xa,
      QuaternionGroup.orderOf_xa]

end Aux

namespace FrameCfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {S : Subgroup T}

private theorem m12fac_comm_one (cfg : FrameCfg K z J zJ S)
    (hO : ∀ L ∈ aStar (CoreAssembly.conjClass K) K, oddCoreOf L ≤ oddCoreOf (sigmaGen K))
    {m : T} (hm : m ∈ sigmaNorm K) (hne : firstFactor K ≠ conjSub m (firstFactor K)) {x y : T}
    (hx : x ∈ firstFactor K) (hy : y ∈ conjSub m (firstFactor K)) :
    x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf (sigmaGen K) := by
  have hΩ := cfg.datum.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hHsN := m12fac_hsN K
  have hmN : conjSub m (oddCoreOf (sigmaGen K)) = oddCoreOf (sigmaGen K) :=
    Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer hm
  have hconjHs : conjSub m (firstFactor K) ≤ sigmaGen K := cfg.conjSub_firstFactor_le hm
  have step1 : ∀ L ∈ aStar (CoreAssembly.conjClass K) K, ∀ L₂ ∈ aStar (CoreAssembly.conjClass K) K,
      ∀ l ∈ L, ∀ l₂ ∈ conjSub m L₂, l * l₂ * l⁻¹ * l₂⁻¹ ∈ oddCoreOf (sigmaGen K) := by
    intro L hL L₂ hL₂ l hl l₂ hl₂
    have hL₂S : conjSub m L₂ ∈ sigmaOf K :=
      (mem_sigmaStarNorm_iff.mp (cfg.sigmaNorm_le_sigmaStarNorm hm) L₂).mp
        (aStar_subset_dstarComp_gen hΩ hKΩ hL₂).2
    have hL₂A : conjSub m L₂ ∉ aStar (CoreAssembly.conjClass K) K := fun h =>
      hne (mem_normalizer_iff_conjSub_eq.mp (mem_normalizer_firstFactor
        (m12fac_mem_conjStab hΩ.conjInvariant hKΩ hL₂ h) hm)).symm
    have h1 : l₂ * l * l₂⁻¹ * l⁻¹ ∈ oddCoreOf (sigmaGen K) := by
      have h0 := (cfg.commutator_le_of_not_mem_aStar hL₂S hL₂A hL
        (Subgroup.commutator_mem_commutator hl₂ hl)).2
      rw [commutatorElement_def] at h0
      exact sup_le (hO L hL) le_rfl h0
    have e : l * l₂ * l⁻¹ * l₂⁻¹ = (l₂ * l * l₂⁻¹ * l⁻¹)⁻¹ := by group
    rw [e]
    exact (oddCoreOf (sigmaGen K)).inv_mem h1
  have step2 : ∀ L ∈ aStar (CoreAssembly.conjClass K) K, ∀ l ∈ L,
      ∀ y ∈ conjSub m (firstFactor K), l * y * l⁻¹ * y⁻¹ ∈ oddCoreOf (sigmaGen K) := by
    intro L hL l hl
    have hlHs : l ∈ sigmaGen K := cfg.ht_le (m12fac_le_firstFactor hL hl)
    have hle : conjSub m (firstFactor K) ≤
        m12facSub (sigmaGen K) (oddCoreOf (sigmaGen K)) hHsN {l} := by
      refine m12fac_conjSub_firstFactor_le (fun L₂ hL₂ w hw => ?_) (fun w hw => ?_)
      · have hw' : m * w * m⁻¹ ∈ conjSub m L₂ := conj_mem_conjSub hw
        refine mem_m12facSub.mpr
          ⟨hconjHs (conjSub_mono (m12fac_le_firstFactor hL₂) hw'), ?_⟩
        intro v hv
        rw [Set.mem_singleton_iff.mp hv]
        exact step1 L hL L₂ hL₂ l hl _ hw'
      · have hw' : m * w * m⁻¹ ∈ oddCoreOf (sigmaGen K) := by
          rw [← hmN]
          exact conj_mem_conjSub hw
        refine mem_m12facSub.mpr ⟨oddCoreOf_le_self _ hw', ?_⟩
        intro v hv
        rw [Set.mem_singleton_iff.mp hv]
        exact (oddCoreOf (sigmaGen K)).mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hHsN hlHs) _).mp hw')
          ((oddCoreOf (sigmaGen K)).inv_mem hw')
    intro y hy
    exact (mem_m12facSub.mp (hle hy)).2 l rfl
  have hyHs : y ∈ sigmaGen K := hconjHs hy
  have hle2 : firstFactor K ≤ m12facSub (sigmaGen K) (oddCoreOf (sigmaGen K)) hHsN {y} := by
    refine sup_le (iSup₂_le fun L hL w hw => ?_) (fun w hw => ?_)
    · refine mem_m12facSub.mpr ⟨cfg.ht_le (m12fac_le_firstFactor hL hw), ?_⟩
      intro v hv
      rw [Set.mem_singleton_iff.mp hv]
      have e : y * w * y⁻¹ * w⁻¹ = (w * y * w⁻¹ * y⁻¹)⁻¹ := by group
      rw [e]
      exact (oddCoreOf (sigmaGen K)).inv_mem (step2 L hL w hw y hy)
    · refine mem_m12facSub.mpr ⟨oddCoreOf_le_self _ hw, ?_⟩
      intro v hv
      rw [Set.mem_singleton_iff.mp hv]
      exact (oddCoreOf (sigmaGen K)).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hHsN hyHs) _).mp hw) ((oddCoreOf (sigmaGen K)).inv_mem hw)
  have h := (mem_m12facSub.mp (hle2 hx)).2 y rfl
  have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact (oddCoreOf (sigmaGen K)).inv_mem h

theorem factor_comm_of (cfg : FrameCfg K z J zJ S)
    (hO : ∀ L ∈ aStar (CoreAssembly.conjClass K) K, oddCoreOf L ≤ oddCoreOf (sigmaGen K))
    {m₁ m₂ : T} (hm₁ : m₁ ∈ sigmaNorm K) (hm₂ : m₂ ∈ sigmaNorm K)
    (hne : conjSub m₁ (firstFactor K) ≠ conjSub m₂ (firstFactor K)) {x y : T}
    (hx : x ∈ conjSub m₁ (firstFactor K)) (hy : y ∈ conjSub m₂ (firstFactor K)) :
    x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf (sigmaGen K) := by
  have hm : m₁⁻¹ * m₂ ∈ sigmaNorm K := (sigmaNorm K).mul_mem ((sigmaNorm K).inv_mem hm₁) hm₂
  have hne' : firstFactor K ≠ conjSub (m₁⁻¹ * m₂) (firstFactor K) := by
    intro h
    apply hne
    calc conjSub m₁ (firstFactor K) = conjSub m₁ (conjSub (m₁⁻¹ * m₂) (firstFactor K)) := by
          rw [← h]
      _ = conjSub m₂ (firstFactor K) := by rw [← conjSub_mul, mul_inv_cancel_left]
  have hx' : m₁⁻¹ * x * m₁ ∈ firstFactor K := mem_conjSub_iff.mp hx
  have hy' : m₁⁻¹ * y * m₁ ∈ conjSub (m₁⁻¹ * m₂) (firstFactor K) := by
    rw [mem_conjSub_iff]
    have h := mem_conjSub_iff.mp hy
    rwa [show (m₁⁻¹ * m₂)⁻¹ * (m₁⁻¹ * y * m₁) * (m₁⁻¹ * m₂) = m₂⁻¹ * y * m₂ by group]
  have h := m12fac_comm_one cfg hO hm hne' hx' hy'
  have hN : conjSub m₁ (oddCoreOf (sigmaGen K)) = oddCoreOf (sigmaGen K) :=
    Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer hm₁
  rw [← hN, mem_conjSub_iff]
  rwa [show m₁⁻¹ * (x * y * x⁻¹ * y⁻¹) * m₁ = (m₁⁻¹ * x * m₁) * (m₁⁻¹ * y * m₁) *
    (m₁⁻¹ * x * m₁)⁻¹ * (m₁⁻¹ * y * m₁)⁻¹ by group]

theorem factor_inf_le_of (cfg : FrameCfg K z J zJ S)
    (hO : ∀ L ∈ aStar (CoreAssembly.conjClass K) K, oddCoreOf L ≤ oddCoreOf (sigmaGen K))
    (hZ : Subgroup.center (SecQuot (firstFactor K)) = ⊥) {m₁ m₂ : T} (hm₁ : m₁ ∈ sigmaNorm K)
    (hm₂ : m₂ ∈ sigmaNorm K) (hne : conjSub m₁ (firstFactor K) ≠ conjSub m₂ (firstFactor K)) :
    conjSub m₁ (firstFactor K) ⊓ conjSub m₂ (firstFactor K) ≤ oddCoreOf (sigmaGen K) := by
  rintro x ⟨hx₀, hx⟩
  have hxc : ∀ y ∈ conjSub m₁ (firstFactor K), y * x * y⁻¹ * x⁻¹ ∈ oddCoreOf (sigmaGen K) :=
    fun y hy => cfg.factor_comm_of hO hm₁ hm₂ hne hy hx
  have hm₀N : conjSub m₁ (oddCoreOf (sigmaGen K)) = oddCoreOf (sigmaGen K) :=
    Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer hm₁
  have hx' : m₁⁻¹ * x * m₁ ∈ firstFactor K := mem_conjSub_iff.mp hx₀
  have hcomm : ∀ w ∈ firstFactor K,
      w * (m₁⁻¹ * x * m₁) * w⁻¹ * (m₁⁻¹ * x * m₁)⁻¹ ∈ oddCoreOf (sigmaGen K) := by
    intro w hw
    have h1 := hxc (m₁ * w * m₁⁻¹) (conj_mem_conjSub hw)
    rw [← hm₀N, mem_conjSub_iff] at h1
    rwa [show m₁⁻¹ * (m₁ * w * m₁⁻¹ * x * (m₁ * w * m₁⁻¹)⁻¹ * x⁻¹) * m₁ =
      w * (m₁⁻¹ * x * m₁) * w⁻¹ * (m₁⁻¹ * x * m₁)⁻¹ by group] at h1
  have hOHt := cfg.oddCoreOf_firstFactor
  have hcentral : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))
      (⟨_, hx'⟩ : ↥(firstFactor K)) ∈ Subgroup.center (SecQuot (firstFactor K)) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(firstFactor K)) q
    have h1 : w * ⟨_, hx'⟩ * w⁻¹ * (⟨_, hx'⟩ : ↥(firstFactor K))⁻¹ ∈
        classicalInvolutionOddCore ↥(firstFactor K) := by
      have h2 := hcomm w w.2
      rw [← hOHt] at h2
      obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.mp h2
      have hu' : u = w * ⟨_, hx'⟩ * w⁻¹ * (⟨_, hx'⟩ : ↥(firstFactor K))⁻¹ := Subtype.ext huv
      rw [← hu']
      exact hu
    have h3 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))
        (w * ⟨_, hx'⟩ * w⁻¹ * (⟨_, hx'⟩ : ↥(firstFactor K))⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h3)
  rw [hZ, Subgroup.mem_bot] at hcentral
  have hx'O : m₁⁻¹ * x * m₁ ∈ oddCoreOf (sigmaGen K) := by
    rw [← hOHt]
    exact Subgroup.mem_map.mpr ⟨⟨_, hx'⟩, (QuotientGroup.eq_one_iff _).mp hcentral, rfl⟩
  rw [← hm₀N, mem_conjSub_iff]
  exact hx'O

theorem factor_eq_of_mem_of (cfg : FrameCfg K z J zJ S)
    (hO : ∀ L ∈ aStar (CoreAssembly.conjClass K) K, oddCoreOf L ≤ oddCoreOf (sigmaGen K))
    (hZ : Subgroup.center (SecQuot (firstFactor K)) = ⊥) {m₁ m₂ : T} (hm₁ : m₁ ∈ sigmaNorm K)
    (hm₂ : m₂ ∈ sigmaNorm K) {x : T} (hx₁ : x ∈ conjSub m₁ (firstFactor K))
    (hx₂ : x ∈ conjSub m₂ (firstFactor K)) (hxO : x ∉ oddCoreOf (sigmaGen K)) :
    conjSub m₁ (firstFactor K) = conjSub m₂ (firstFactor K) := by
  by_contra hne
  exact hxO (cfg.factor_inf_le_of hO hZ hm₁ hm₂ hne ⟨hx₁, hx₂⟩)

end FrameCfg

namespace M12Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H S : Subgroup T}

theorem oddCoreOf_le_of_mem_aStar
    (cfg : M12Cfg K z J zJ H S) {L : Subgroup T}
    (hL : L ∈ aStar (CoreAssembly.conjClass K) K) : oddCoreOf L ≤ oddCoreOf (sigmaGen K) := by
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hLHt : L ≤ firstFactor K := m12fac_le_firstFactor hL
  obtain ⟨g, hg⟩ := (mem_aStar_symm hKΩ hL).1
  have hg' : conjSub g K = L := hg
  obtain ⟨a, b, haL, hbL, ha4, hb4, hab4⟩ := m12fac_exists_four cfg.datum hg'
  have hzc : ∀ x ∈ L, a * a * x = x * (a * a) := m12fac_sq_comm cfg.datum.unique hg' haL ha4
  have hOHt : oddCoreOf L ≤ firstFactor K := (oddCoreOf_le_self L).trans hLHt
  have haHt : a ∈ firstFactor K := hLHt haL
  have hbHt : b ∈ firstFactor K := hLHt hbL
  have habHt : a * b ∈ firstFactor K := (firstFactor K).mul_mem haHt hbHt
  obtain ⟨e⟩ := cfg.equiv
  let ρ : ↥(firstFactor K) →* NativeSporadic.M12 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)))
  let ψ : ↥(oddCoreOf L) →* NativeSporadic.M12 := ρ.comp (Subgroup.inclusion hOHt)
  have hρ4 : ∀ (c : T) (hc : c ∈ firstFactor K), orderOf c = 4 → orderOf (ρ ⟨c, hc⟩) = 4 := by
    intro c hc hc4
    show orderOf (e ((⟨c, hc⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K))) = 4
    rw [MulEquiv.orderOf_eq]
    exact orderOf_mk_eq_four hc hc4
  have hα4 : orderOf (ρ ⟨a, haHt⟩) = 4 := hρ4 a haHt ha4
  have hβ4 : orderOf (ρ ⟨b, hbHt⟩) = 4 := hρ4 b hbHt hb4
  have hαβ4 : orderOf (ρ ⟨a, haHt⟩ * ρ ⟨b, hbHt⟩) = 4 := by
    rw [← map_mul]
    exact hρ4 (a * b) habHt hab4
  have hnorm : ∀ (c : T) (hc : c ∈ L), ∀ d ∈ ψ.range,
      ρ ⟨c, hLHt hc⟩ * d * (ρ ⟨c, hLHt hc⟩)⁻¹ ∈ ψ.range := by
    rintro c hc _ ⟨x, rfl⟩
    have hcx : c * (x : T) * c⁻¹ ∈ oddCoreOf L :=
      Asc77.mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hc) x.2
    refine ⟨⟨_, hcx⟩, ?_⟩
    have e1 : (Subgroup.inclusion hOHt ⟨_, hcx⟩ : ↥(firstFactor K)) =
        ⟨c, hLHt hc⟩ * Subgroup.inclusion hOHt x * (⟨c, hLHt hc⟩ : ↥(firstFactor K))⁻¹ :=
      Subtype.ext rfl
    show ρ (Subgroup.inclusion hOHt ⟨_, hcx⟩) = _
    rw [e1, map_mul, map_mul, map_inv]
    rfl
  have hcent : ψ.range ≤ Subgroup.centralizer ({ρ ⟨a, haHt⟩ * ρ ⟨a, haHt⟩} : Set _) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : Subgroup.inclusion hOHt x * (⟨a, haHt⟩ * ⟨a, haHt⟩) =
        (⟨a, haHt⟩ * ⟨a, haHt⟩ : ↥(firstFactor K)) * Subgroup.inclusion hOHt x :=
      Subtype.ext (hzc _ (oddCoreOf_le_self L x.2)).symm
    show ρ (Subgroup.inclusion hOHt x) * (ρ ⟨a, haHt⟩ * ρ ⟨a, haHt⟩) =
      ρ ⟨a, haHt⟩ * ρ ⟨a, haHt⟩ * ρ (Subgroup.inclusion hOHt x)
    rw [← map_mul, ← map_mul, ← map_mul, e1]
  have hodd : Odd (Nat.card ψ.range) :=
    (oddCoreOf_odd_natCard L).of_dvd_nat (Subgroup.card_range_dvd ψ)
  have h192 : Nat.card ψ.range ∣ 2 ^ 6 * 3 := by
    have h := Subgroup.card_dvd_of_le hcent
    rw [m12_card_centralizer_sq _ hα4] at h
    exact h
  have h3 : Nat.card ψ.range ∣ 3 :=
    ((Odd.coprime_two_right hodd).pow_right 6).dvd_of_dvd_mul_left h192
  have hbot : ψ.range = ⊥ :=
    m12fac_eq_bot (fun k d hk hd => m12_not_commute_four_three k d hk hd) h3 hα4 hβ4 hαβ4
      (hnorm a haL) (hnorm b hbL)
  intro x hx
  have h1 : ψ ⟨x, hx⟩ = 1 := by
    have h0 : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hbot] at h0
    exact (Subgroup.mem_bot).mp h0
  have h1' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))
      (Subgroup.inclusion hOHt ⟨x, hx⟩) = 1 := by
    apply e.injective
    rw [map_one]
    exact h1
  have h2 : Subgroup.inclusion hOHt ⟨x, hx⟩ ∈ classicalInvolutionOddCore ↥(firstFactor K) :=
    (QuotientGroup.eq_one_iff _).mp h1'
  rw [← cfg.toFrameCfg.oddCoreOf_firstFactor]
  exact Subgroup.mem_map.mpr ⟨_, h2, rfl⟩

theorem factor_comm
    (cfg : M12Cfg K z J zJ H S) {m₁ m₂ : T} (hm₁ : m₁ ∈ sigmaNorm K)
    (hm₂ : m₂ ∈ sigmaNorm K) (hne : conjSub m₁ (firstFactor K) ≠ conjSub m₂ (firstFactor K))
    {x y : T} (hx : x ∈ conjSub m₁ (firstFactor K)) (hy : y ∈ conjSub m₂ (firstFactor K)) :
    x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf (sigmaGen K) :=
  cfg.toFrameCfg.factor_comm_of (fun _ hL => cfg.oddCoreOf_le_of_mem_aStar hL) hm₁ hm₂ hne hx hy

theorem factor_eq_of_mem
    (cfg : M12Cfg K z J zJ H S) {m₁ m₂ : T} (hm₁ : m₁ ∈ sigmaNorm K) (hm₂ : m₂ ∈ sigmaNorm K) {x : T}
    (hx₁ : x ∈ conjSub m₁ (firstFactor K)) (hx₂ : x ∈ conjSub m₂ (firstFactor K))
    (hxO : x ∉ oddCoreOf (sigmaGen K)) :
    conjSub m₁ (firstFactor K) = conjSub m₂ (firstFactor K) :=
  cfg.toFrameCfg.factor_eq_of_mem_of (fun _ hL => cfg.oddCoreOf_le_of_mem_aStar hL)
    cfg.center_eq_bot hm₁ hm₂ hx₁ hx₂ hxO

end M12Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
