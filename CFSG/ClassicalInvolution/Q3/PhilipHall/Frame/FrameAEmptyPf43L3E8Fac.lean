module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43Fac
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8Cfg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8Shape3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Aux

variable {T : Type} [Group T]

private def l3facSub (H N : Subgroup T) (hHN : H ≤ Subgroup.normalizer (N : Set T)) (X : Set T) :
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

private theorem mem_l3facSub {H N : Subgroup T} {hHN : H ≤ Subgroup.normalizer (N : Set T)}
    {X : Set T} {y : T} :
    y ∈ l3facSub H N hHN X ↔ y ∈ H ∧ ∀ x ∈ X, x * y * x⁻¹ * y⁻¹ ∈ N :=
  Iff.rfl

private theorem l3fac_hsN (K : Subgroup T) :
    sigmaGen K ≤ Subgroup.normalizer (oddCoreOf (sigmaGen K) : Set T) := fun _ hg =>
  mem_normalizer_iff_conjSub_eq.mpr
    (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer hg))

private theorem l3fac_le_firstFactor {K L : Subgroup T}
    (hL : L ∈ aStar (CoreAssembly.conjClass K) K) : L ≤ firstFactor K :=
  (le_omegaGen hL).trans le_sup_left

private theorem l3fac_conjSub_firstFactor_le {K X : Subgroup T} {m : T}
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

private theorem l3fac_mem_conjStab {Ω : Set (Subgroup T)} (hΩ : ConjInvariant Ω) {K L : Subgroup T}
    (hK : K ∈ Ω) (hL : L ∈ aStar Ω K) {g : T} (hgL : conjSub g L ∈ aStar Ω K) :
    g ∈ conjStab (aStar Ω K) := by
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

variable [Finite T]

private theorem l3fac_mk_injective {Ht R : Subgroup T} (hRHt : R ≤ Ht) (hR : IsPGroup 2 R) :
    Function.Injective ((QuotientGroup.mk' (classicalInvolutionOddCore ↥Ht)).comp
      (Subgroup.inclusion hRHt)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨k, hk⟩ := hR a
  have h1 : Subgroup.inclusion hRHt a ∈ classicalInvolutionOddCore ↥Ht :=
    (QuotientGroup.eq_one_iff _).mp ha
  have hk' : (Subgroup.inclusion hRHt a) ^ 2 ^ k = 1 := by
    rw [← map_pow, hk, map_one]
  have hodd : Odd (orderOf (Subgroup.inclusion hRHt a)) :=
    (CFSG.ComponentClassification.OddCore.odd_card ↥Ht).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ h1)
  have h3 : Subgroup.inclusion hRHt a = 1 :=
    orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow hodd (orderOf_dvd_of_pow_eq_one hk'))
  exact (Subgroup.inclusion_injective hRHt) (by rw [h3, map_one])

end Aux

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem oddCoreOf_le_of_mem_aStar (cfg : L3E8Cfg K z J zJ H Q E S) {L : Subgroup T}
    (hL : L ∈ aStar (CoreAssembly.conjClass K) K) : oddCoreOf L ≤ oddCoreOf (sigmaGen K) := by
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hLHt : L ≤ firstFactor K := l3fac_le_firstFactor hL
  obtain ⟨g, hg⟩ := (mem_aStar_symm hKΩ hL).1
  have hg' : conjSub g K = L := hg
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup T))
    (bot_le : (⊥ : Subgroup T) ≤ K)
  obtain ⟨e⟩ := cfg.datum.quat R₀ hR₀
  have hRL : conjSub g R₀ ≤ L := hg' ▸ conjSub_mono hR₀.1
  have hR2 : IsPGroup 2 (conjSub g R₀) := isPGroup_conjSub g hR₀.2.1
  have hRHt : conjSub g R₀ ≤ firstFactor K := hRL.trans hLHt
  have hOHt : oddCoreOf L ≤ firstFactor K := (oddCoreOf_le_self L).trans hLHt
  let φ : ↥(conjSub g R₀) →* SecQuot (firstFactor K) :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))).comp
      (Subgroup.inclusion hRHt)
  let ψ : ↥(oddCoreOf L) →* SecQuot (firstFactor K) :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))).comp
      (Subgroup.inclusion hOHt)
  have hφ : Function.Injective φ := l3fac_mk_injective hRHt hR2
  have hP : Nonempty (↥φ.range ≃* QuaternionGroup 2) :=
    ⟨(MonoidHom.ofInjective hφ).symm.trans ((Subgroup.equivMapOfInjective R₀
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans e)⟩
  have hD : Odd (Nat.card ψ.range) :=
    (oddCoreOf_odd_natCard L).of_dvd_nat (Subgroup.card_range_dvd ψ)
  have hfwd : ∀ (a : ↥(conjSub g R₀)) (b : ↥(oddCoreOf L)), φ a * ψ b * (φ a)⁻¹ ∈ ψ.range := by
    intro a b
    have hab : (a : T) * b * (a : T)⁻¹ ∈ oddCoreOf L :=
      Asc77.mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (hRL a.2)) b.2
    refine ⟨⟨_, hab⟩, ?_⟩
    have e1 : (Subgroup.inclusion hOHt ⟨_, hab⟩ : ↥(firstFactor K)) =
        Subgroup.inclusion hRHt a * Subgroup.inclusion hOHt b * (Subgroup.inclusion hRHt a)⁻¹ :=
      Subtype.ext rfl
    show QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))
      (Subgroup.inclusion hOHt ⟨_, hab⟩) = _
    rw [e1, map_mul, map_mul, map_inv]
    rfl
  have hPD : φ.range ≤ Subgroup.normalizer (ψ.range : Set (SecQuot (firstFactor K))) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · rintro ⟨b, rfl⟩
      exact hfwd a b
    · rintro ⟨b, hb⟩
      have e2 : φ a⁻¹ * ψ b * (φ a⁻¹)⁻¹ = d := by
        rw [hb, map_inv, inv_inv]
        group
      rw [← e2]
      exact hfwd a⁻¹ b
  obtain ⟨F, hF⟩ := cfg.faithful
  have hbot : ψ.range = ⊥ := FaithfulL3E8.eq_bot_of_le_normalizer hF hP hD hPD
  intro x hx
  have h1 : ψ ⟨x, hx⟩ = 1 := by
    have h0 : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hbot] at h0
    exact (Subgroup.mem_bot).mp h0
  have h2 : Subgroup.inclusion hOHt ⟨x, hx⟩ ∈ classicalInvolutionOddCore ↥(firstFactor K) :=
    (QuotientGroup.eq_one_iff _).mp h1
  rw [← cfg.oddCoreOf_firstFactor]
  exact Subgroup.mem_map.mpr ⟨_, h2, rfl⟩

private theorem l3fac_comm_one (cfg : L3E8Cfg K z J zJ H Q E S) {m : T} (hm : m ∈ sigmaNorm K)
    (hne : firstFactor K ≠ conjSub m (firstFactor K)) {x y : T} (hx : x ∈ firstFactor K)
    (hy : y ∈ conjSub m (firstFactor K)) : x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf (sigmaGen K) := by
  have hΩ := cfg.datum.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hHsN := l3fac_hsN K
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
        (l3fac_mem_conjStab hΩ.conjInvariant hKΩ hL₂ h) hm)).symm
    have h1 : l₂ * l * l₂⁻¹ * l⁻¹ ∈ oddCoreOf (sigmaGen K) := by
      have h0 := (cfg.commutator_le_of_not_mem_aStar hL₂S hL₂A hL
        (Subgroup.commutator_mem_commutator hl₂ hl)).2
      rw [commutatorElement_def] at h0
      exact sup_le (cfg.oddCoreOf_le_of_mem_aStar hL) le_rfl h0
    have e : l * l₂ * l⁻¹ * l₂⁻¹ = (l₂ * l * l₂⁻¹ * l⁻¹)⁻¹ := by group
    rw [e]
    exact (oddCoreOf (sigmaGen K)).inv_mem h1
  have step2 : ∀ L ∈ aStar (CoreAssembly.conjClass K) K, ∀ l ∈ L,
      ∀ y ∈ conjSub m (firstFactor K), l * y * l⁻¹ * y⁻¹ ∈ oddCoreOf (sigmaGen K) := by
    intro L hL l hl
    have hlHs : l ∈ sigmaGen K := cfg.ht_le (l3fac_le_firstFactor hL hl)
    have hle : conjSub m (firstFactor K) ≤
        l3facSub (sigmaGen K) (oddCoreOf (sigmaGen K)) hHsN {l} := by
      refine l3fac_conjSub_firstFactor_le (fun L₂ hL₂ w hw => ?_) (fun w hw => ?_)
      · have hw' : m * w * m⁻¹ ∈ conjSub m L₂ := conj_mem_conjSub hw
        refine mem_l3facSub.mpr ⟨hconjHs (conjSub_mono (l3fac_le_firstFactor hL₂) hw'), ?_⟩
        intro v hv
        rw [Set.mem_singleton_iff.mp hv]
        exact step1 L hL L₂ hL₂ l hl _ hw'
      · have hw' : m * w * m⁻¹ ∈ oddCoreOf (sigmaGen K) := by
          rw [← hmN]
          exact conj_mem_conjSub hw
        refine mem_l3facSub.mpr ⟨oddCoreOf_le_self _ hw', ?_⟩
        intro v hv
        rw [Set.mem_singleton_iff.mp hv]
        exact (oddCoreOf (sigmaGen K)).mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hHsN hlHs) _).mp hw')
          ((oddCoreOf (sigmaGen K)).inv_mem hw')
    intro y hy
    exact (mem_l3facSub.mp (hle hy)).2 l rfl
  have hyHs : y ∈ sigmaGen K := hconjHs hy
  have hle2 : firstFactor K ≤ l3facSub (sigmaGen K) (oddCoreOf (sigmaGen K)) hHsN {y} := by
    refine sup_le (iSup₂_le fun L hL w hw => ?_) (fun w hw => ?_)
    · refine mem_l3facSub.mpr ⟨cfg.ht_le (l3fac_le_firstFactor hL hw), ?_⟩
      intro v hv
      rw [Set.mem_singleton_iff.mp hv]
      have e : y * w * y⁻¹ * w⁻¹ = (w * y * w⁻¹ * y⁻¹)⁻¹ := by group
      rw [e]
      exact (oddCoreOf (sigmaGen K)).inv_mem (step2 L hL w hw y hy)
    · refine mem_l3facSub.mpr ⟨oddCoreOf_le_self _ hw, ?_⟩
      intro v hv
      rw [Set.mem_singleton_iff.mp hv]
      exact (oddCoreOf (sigmaGen K)).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hHsN hyHs) _).mp hw) ((oddCoreOf (sigmaGen K)).inv_mem hw)
  have h := (mem_l3facSub.mp (hle2 hx)).2 y rfl
  have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact (oddCoreOf (sigmaGen K)).inv_mem h

theorem factor_comm (cfg : L3E8Cfg K z J zJ H Q E S) {m₁ m₂ : T} (hm₁ : m₁ ∈ sigmaNorm K)
    (hm₂ : m₂ ∈ sigmaNorm K) (hne : conjSub m₁ (firstFactor K) ≠ conjSub m₂ (firstFactor K))
    {x y : T} (hx : x ∈ conjSub m₁ (firstFactor K)) (hy : y ∈ conjSub m₂ (firstFactor K)) :
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
  have h := l3fac_comm_one cfg hm hne' hx' hy'
  have hN : conjSub m₁ (oddCoreOf (sigmaGen K)) = oddCoreOf (sigmaGen K) :=
    Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer hm₁
  rw [← hN, mem_conjSub_iff]
  rwa [show m₁⁻¹ * (x * y * x⁻¹ * y⁻¹) * m₁ = (m₁⁻¹ * x * m₁) * (m₁⁻¹ * y * m₁) *
    (m₁⁻¹ * x * m₁)⁻¹ * (m₁⁻¹ * y * m₁)⁻¹ by group]

theorem factor_indep (cfg : L3E8Cfg K z J zJ H Q E S) {ι : Type*} {m₀ : T} (m : ι → T)
    (hm₀ : m₀ ∈ sigmaNorm K) (hm : ∀ i, m i ∈ sigmaNorm K)
    (hne : ∀ i, conjSub (m i) (firstFactor K) ≠ conjSub m₀ (firstFactor K)) :
    conjSub m₀ (firstFactor K) ⊓ ⨆ i, conjSub (m i) (firstFactor K) ≤ oddCoreOf (sigmaGen K) := by
  have hHsN := l3fac_hsN K
  have hle : ⨆ i, conjSub (m i) (firstFactor K) ≤
      l3facSub (sigmaGen K) (oddCoreOf (sigmaGen K)) hHsN (conjSub m₀ (firstFactor K) : Set T) :=
    iSup_le fun i w hw => mem_l3facSub.mpr ⟨cfg.conjSub_firstFactor_le (hm i) hw,
      fun y hy => cfg.factor_comm hm₀ (hm i) (hne i).symm hy hw⟩
  rintro x ⟨hx₀, hx⟩
  have hxc := (mem_l3facSub.mp (hle hx)).2
  have hm₀N : conjSub m₀ (oddCoreOf (sigmaGen K)) = oddCoreOf (sigmaGen K) :=
    Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer hm₀
  have hx' : m₀⁻¹ * x * m₀ ∈ firstFactor K := mem_conjSub_iff.mp hx₀
  have hcomm : ∀ w ∈ firstFactor K,
      w * (m₀⁻¹ * x * m₀) * w⁻¹ * (m₀⁻¹ * x * m₀)⁻¹ ∈ oddCoreOf (sigmaGen K) := by
    intro w hw
    have h1 := hxc (m₀ * w * m₀⁻¹) (conj_mem_conjSub hw)
    rw [← hm₀N, mem_conjSub_iff] at h1
    rwa [show m₀⁻¹ * (m₀ * w * m₀⁻¹ * x * (m₀ * w * m₀⁻¹)⁻¹ * x⁻¹) * m₀ =
      w * (m₀⁻¹ * x * m₀) * w⁻¹ * (m₀⁻¹ * x * m₀)⁻¹ by group] at h1
  have hOHt := cfg.oddCoreOf_firstFactor
  obtain ⟨F, hF⟩ := cfg.faithful
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
  rw [FaithfulL3E8.center_eq_bot hF, Subgroup.mem_bot] at hcentral
  have hx'O : m₀⁻¹ * x * m₀ ∈ oddCoreOf (sigmaGen K) := by
    rw [← hOHt]
    exact Subgroup.mem_map.mpr ⟨⟨_, hx'⟩, (QuotientGroup.eq_one_iff _).mp hcentral, rfl⟩
  rw [← hm₀N, mem_conjSub_iff]
  exact hx'O

theorem factor_inf_le (cfg : L3E8Cfg K z J zJ H Q E S) {m₁ m₂ : T} (hm₁ : m₁ ∈ sigmaNorm K)
    (hm₂ : m₂ ∈ sigmaNorm K) (hne : conjSub m₁ (firstFactor K) ≠ conjSub m₂ (firstFactor K)) :
    conjSub m₁ (firstFactor K) ⊓ conjSub m₂ (firstFactor K) ≤ oddCoreOf (sigmaGen K) := by
  have h := cfg.factor_indep (ι := Unit) (fun _ => m₂) hm₁ (fun _ => hm₂) (fun _ => Ne.symm hne)
  rwa [iSup_const] at h

theorem factor_eq_of_mem (cfg : L3E8Cfg K z J zJ H Q E S) {m₁ m₂ : T} (hm₁ : m₁ ∈ sigmaNorm K)
    (hm₂ : m₂ ∈ sigmaNorm K) {x : T} (hx₁ : x ∈ conjSub m₁ (firstFactor K))
    (hx₂ : x ∈ conjSub m₂ (firstFactor K)) (hxO : x ∉ oddCoreOf (sigmaGen K)) :
    conjSub m₁ (firstFactor K) = conjSub m₂ (firstFactor K) := by
  by_contra hne
  exact hxO (cfg.factor_inf_le hm₁ hm₂ hne ⟨hx₁, hx₂⟩)

end L3E8Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
