module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.Assembly.Dichotomy
open scoped commutatorElement

@[expose] def fixedSubgroup {X : Type} [Group X] (σ : MulAut X) : Subgroup X :=
  MonoidHom.eqLocus (σ : X →* X) (MonoidHom.id X)

theorem mem_fixedSubgroup_iff {X : Type} [Group X] {σ : MulAut X} {x : X} :
    x ∈ fixedSubgroup σ ↔ σ x = x :=
  Iff.rfl

abbrev innSubgroup (X : Type) [Group X] : Subgroup (MulAut X) :=
  (MulAut.conj : X →* MulAut X).range

theorem mem_innSubgroup_iff {X : Type} [Group X] {α : MulAut X} :
    α ∈ innSubgroup X ↔ ∃ x : X, MulAut.conj x = α :=
  Iff.rfl

@[expose] def AutOddFree (X : Type) [Group X] : Prop :=
  ∀ 𝒳 : Subgroup (MulAut X), innSubgroup X ≤ 𝒳 → ∀ f : 𝒳, orderOf f = 2 →
    involutionOddCore f = ⊥

@[expose] def AutOddFreeInner (X : Type) [Group X] : Prop :=
  ∀ 𝒳 : Subgroup (MulAut X), innSubgroup X ≤ 𝒳 → ∀ f : 𝒳, (f : MulAut X) ∈ innSubgroup X →
    orderOf f = 2 → involutionOddCore f = ⊥

@[expose] def AutOddFreeInnerOn (X : Type) [Group X] (P : X → Prop) : Prop :=
  ∀ 𝒳 : Subgroup (MulAut X), innSubgroup X ≤ 𝒳 → ∀ f : 𝒳, ∀ s : X,
    MulAut.conj s = (f : MulAut X) → P s → orderOf f = 2 → involutionOddCore f = ⊥

theorem AutOddFreeInner.on {X : Type} [Group X] (h : AutOddFreeInner X) (P : X → Prop) :
    AutOddFreeInnerOn X P :=
  fun 𝒳 hinn f s hs _ hf => h 𝒳 hinn f ⟨s, hs⟩ hf

@[expose] def FixedOddFree (X : Type) [Group X] : Prop :=
  ∀ σ : MulAut X, σ * σ = 1 → oddCoreIn (fixedSubgroup σ) = ⊥

theorem AutOddFree.inner {X : Type} [Group X] (h : AutOddFree X) : AutOddFreeInner X :=
  fun 𝒳 hinn f _ hf => h 𝒳 hinn f hf

section OddInn

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_eq_bot_of_odd_mem {I : Subgroup G} (hI : ∀ g : G, Odd (orderOf g) → g ∈ I)
    (f : G) (h : oddCoreIn (Subgroup.centralizer ({f} : Set G) ⊓ I) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({f} : Set G)) = ⊥ := by
  set C := Subgroup.centralizer ({f} : Set G) with hC
  have hNI : oddCoreIn C ≤ C ⊓ I := fun n hn =>
    ⟨oddCoreIn_le C hn, hI n (Odd.of_dvd_nat (odd_card_oddCoreIn C)
      (Subgroup.orderOf_dvd_natCard _ hn))⟩
  have hle : oddCoreIn C ≤ oddCoreIn (C ⊓ I) :=
    le_oddCoreIn_of_normalizes hNI (inf_le_left.trans (normalizer_oddCoreIn C))
      (odd_card_oddCoreIn C)
  rw [h] at hle
  exact le_bot_iff.mp hle

theorem oddCoreIn_eq_bot_of_comm_mem {I : Subgroup G} [I.Normal] (f : G)
    (h1 : oddCoreIn (Subgroup.centralizer ({f} : Set G) ⊓ I) = ⊥)
    (h2 : ∀ g ∈ oddCoreIn (Subgroup.centralizer ({f} : Set G)),
      (∀ i ∈ Subgroup.centralizer ({f} : Set G) ⊓ I, g * i = i * g) → g ∈ I) :
    oddCoreIn (Subgroup.centralizer ({f} : Set G)) = ⊥ := by
  set C := Subgroup.centralizer ({f} : Set G) with hC
  set N := oddCoreIn C with hN
  have hNC : N ≤ C := oddCoreIn_le C
  have hM : N ⊓ (C ⊓ I) = ⊥ := by
    refine le_bot_iff.mp ?_
    have hnormS : ∀ y ∈ C ⊓ I, ∀ w, w ∈ N ⊓ (C ⊓ I) → y * w * y⁻¹ ∈ N ⊓ (C ⊓ I) := by
      intro y hy w hw
      exact ⟨conj_mem_oddCoreIn hy.1 hw.1,
        (C ⊓ I).mul_mem ((C ⊓ I).mul_mem hy hw.2) ((C ⊓ I).inv_mem hy)⟩
    have hle : N ⊓ (C ⊓ I) ≤ oddCoreIn (C ⊓ I) := by
      refine le_oddCoreIn_of_normalizes inf_le_right (fun y hy => ?_)
        ((odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨hnormS y hy w, fun h => ?_⟩
      have := hnormS y⁻¹ ((C ⊓ I).inv_mem hy) _ h
      simpa [mul_assoc] using this
    rwa [h1] at hle
  have hcomm : ∀ n ∈ N, ∀ i ∈ C ⊓ I, n * i = i * n := by
    intro n hn i hi
    have hc : ⁅n, i⁆ ∈ N ⊓ (C ⊓ I) := by
      refine ⟨?_, ?_, ?_⟩
      · have h3 : i * n⁻¹ * i⁻¹ ∈ N := conj_mem_oddCoreIn hi.1 (N.inv_mem hn)
        have : ⁅n, i⁆ = n * (i * n⁻¹ * i⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [this]
        exact N.mul_mem hn h3
      · have : ⁅n, i⁆ = n * i * n⁻¹ * i⁻¹ := commutatorElement_def n i
        rw [this]
        exact C.mul_mem (C.mul_mem (C.mul_mem (hNC hn) hi.1) (C.inv_mem (hNC hn))) (C.inv_mem hi.1)
      · have h4 : n * i * n⁻¹ ∈ I := Subgroup.Normal.conj_mem inferInstance i hi.2 n
        have : ⁅n, i⁆ = n * i * n⁻¹ * i⁻¹ := commutatorElement_def n i
        rw [this]
        exact I.mul_mem h4 (I.inv_mem hi.2)
    rw [hM, Subgroup.mem_bot] at hc
    exact commutatorElement_eq_one_iff_mul_comm.mp hc
  refine eq_bot_iff.mpr fun n hn => ?_
  have hnI := h2 n hn (hcomm n hn)
  have hn' : n ∈ N ⊓ (C ⊓ I) := ⟨hn, hNC hn, hnI⟩
  rwa [hM] at hn'

end OddInn


section Conj

variable {X : Type} [Group X]

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro x y hxy
  have h : ∀ g : X, x * y⁻¹ * g = g * (x * y⁻¹) := by
    intro g
    have h1 := congrArg (fun α : MulAut X => α (y⁻¹ * g * y)) hxy
    simp only [MulAut.conj_apply] at h1
    calc x * y⁻¹ * g = (x * (y⁻¹ * g * y) * x⁻¹) * x * y⁻¹ := by group
      _ = (y * (y⁻¹ * g * y) * y⁻¹) * x * y⁻¹ := by rw [h1]
      _ = g * (x * y⁻¹) := by group
  have hmem : x * y⁻¹ ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun g => (h g).symm
  rw [hZ, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

theorem mul_conj_mul_inv (σ : MulAut X) (x : X) :
    σ * MulAut.conj x * σ⁻¹ = MulAut.conj (σ x) := by
  ext y
  simp [MulAut.conj_apply]

theorem conj_comm_iff (hZ : Subgroup.center X = ⊥) {σ : MulAut X} (hσ : σ * σ = 1) (x : X) :
    MulAut.conj x * σ = σ * MulAut.conj x ↔ σ x = x := by
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have h1 := mul_conj_mul_inv σ x
  rw [hσinv] at h1
  constructor
  · intro hc
    have h2 : MulAut.conj (σ x) = MulAut.conj x := by
      rw [← h1]
      calc σ * MulAut.conj x * σ = (MulAut.conj x * σ) * σ := by rw [← hc]
        _ = MulAut.conj x := by rw [mul_assoc, hσ, mul_one]
    exact conj_injective_of_center_eq_bot hZ h2
  · intro hx
    rw [hx] at h1
    calc MulAut.conj x * σ = (σ * MulAut.conj x * σ) * σ := by rw [h1]
      _ = σ * MulAut.conj x := by rw [mul_assoc, mul_assoc, hσ, mul_one]

theorem mul_self_eq_one_of_orderOf_eq_two' {G : Type} [Group G] {f : G} (hf : orderOf f = 2) :
    f * f = 1 := by
  have := pow_orderOf_eq_one f
  rwa [hf, sq] at this

theorem fixedSubgroup_conj (s : X) : fixedSubgroup (MulAut.conj s) = Subgroup.centralizer {s} := by
  ext x
  rw [mem_fixedSubgroup_iff, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc x * s = (s * x * s⁻¹) * s := by rw [h]
      _ = s * x := by group
  · intro h
    calc s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [h]
      _ = x := by group

instance innSubgroup_normal : (innSubgroup X).Normal :=
  ⟨fun n hn g => by
    obtain ⟨x, rfl⟩ := hn
    exact ⟨g x, (mul_conj_mul_inv g x).symm⟩⟩

end Conj

section Fixed

variable {X : Type} [Group X]

noncomputable def fixedToInn (𝒳 : Subgroup (MulAut X)) (hinn : innSubgroup X ≤ 𝒳)
    (σ : MulAut X) : ↥(fixedSubgroup σ) →* ↥𝒳 :=
  ((MulAut.conj : X →* MulAut X).comp (fixedSubgroup σ).subtype).codRestrict 𝒳
    fun x => hinn ⟨x, rfl⟩

theorem fixedToInn_injective (hZ : Subgroup.center X = ⊥) (𝒳 : Subgroup (MulAut X))
    (hinn : innSubgroup X ≤ 𝒳) (σ : MulAut X) : Function.Injective (fixedToInn 𝒳 hinn σ) := by
  intro x y hxy
  have h1 : MulAut.conj (x : X) = MulAut.conj (y : X) := congrArg Subtype.val hxy
  exact Subtype.ext (conj_injective_of_center_eq_bot hZ h1)

theorem range_fixedToInn (hZ : Subgroup.center X = ⊥) (𝒳 : Subgroup (MulAut X))
    (hinn : innSubgroup X ≤ 𝒳) (f : 𝒳) (hf : f * f = 1) :
    (fixedToInn 𝒳 hinn (f : MulAut X)).range =
      Subgroup.centralizer ({f} : Set 𝒳) ⊓ (innSubgroup X).subgroupOf 𝒳 := by
  have hσσ : (f : MulAut X) * (f : MulAut X) = 1 := congrArg Subtype.val hf
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_),
      Subgroup.mem_subgroupOf.mpr ⟨x, rfl⟩⟩
    exact (conj_comm_iff hZ hσσ (x : X)).mpr x.2
  · rintro ⟨hg1, hg2⟩
    obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.mp hg2
    have hcomm := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg1)
    have hxf : (x : X) ∈ fixedSubgroup (f : MulAut X) := by
      rw [mem_fixedSubgroup_iff, ← conj_comm_iff hZ hσσ x, hx]
      exact hcomm
    exact ⟨⟨x, hxf⟩, Subtype.ext hx⟩

end Fixed

section AutFixed

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem oddCoreIn_centralizer_inner_eq_bot (hZ : Subgroup.center X = ⊥)
    (𝒳 : Subgroup (MulAut X)) (hinn : innSubgroup X ≤ 𝒳) (f : 𝒳) (hf2 : f * f = 1)
    (hfix : oddCoreIn (fixedSubgroup (f : MulAut X)) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({f} : Set 𝒳) ⊓ (innSubgroup X).subgroupOf 𝒳) = ⊥ := by
  rw [← range_fixedToInn hZ 𝒳 hinn f hf2]
  have h1 : componentClassificationOddCore ↥(fixedSubgroup (f : MulAut X)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hfix
  exact oddCoreIn_range_eq_bot_of_injective _ (fixedToInn_injective hZ 𝒳 hinn _) h1

theorem involutionOddCore_eq_bot_of_fixed (hZ : Subgroup.center X = ⊥)
    (hodd : ∀ α : MulAut X, Odd (orderOf α) → α ∈ innSubgroup X) (𝒳 : Subgroup (MulAut X))
    (hinn : innSubgroup X ≤ 𝒳) (f : 𝒳) (hf2 : f * f = 1)
    (hfix : oddCoreIn (fixedSubgroup (f : MulAut X)) = ⊥) : involutionOddCore f = ⊥ := by
  refine oddCoreIn_eq_bot_of_odd_mem (I := (innSubgroup X).subgroupOf 𝒳) ?_ f ?_
  · intro g hg
    exact Subgroup.mem_subgroupOf.mpr (hodd g (by rwa [Subgroup.orderOf_coe]))
  · exact oddCoreIn_centralizer_inner_eq_bot hZ 𝒳 hinn f hf2 hfix

theorem autOddFree_of_fixedOddFree (hZ : Subgroup.center X = ⊥)
    (hodd : ∀ α : MulAut X, Odd (orderOf α) → α ∈ innSubgroup X) (hF : FixedOddFree X) :
    AutOddFree X := by
  intro 𝒳 hinn f hf
  have hf2 := mul_self_eq_one_of_orderOf_eq_two' hf
  exact involutionOddCore_eq_bot_of_fixed hZ hodd 𝒳 hinn f hf2
    (hF (f : MulAut X) (congrArg Subtype.val hf2))

theorem autOddFreeInnerOn_of_centralizing_inner (P : X → Prop) (hZ : Subgroup.center X = ⊥)
    (hO : ∀ x : X, P x → orderOf x = 2 → involutionOddCore x = ⊥)
    (hodd : ∀ s : X, P s → orderOf s = 2 → ∀ α : MulAut X, Odd (orderOf α) →
      (∀ x ∈ Subgroup.centralizer ({s} : Set X), α x = x) → α ∈ innSubgroup X) :
    AutOddFreeInnerOn X P := by
  intro 𝒳 hinn f s hs hPs hf
  have hf2 := mul_self_eq_one_of_orderOf_eq_two' hf
  have hss : s * s = 1 := by
    apply conj_injective_of_center_eq_bot hZ
    rw [map_mul, hs, map_one]
    exact congrArg Subtype.val hf2
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [map_one] at hs
    have : orderOf f = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext hs.symm
    omega
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rwa [← sq] at hss) hs1
  have hfs : (f : MulAut X) = MulAut.conj s := hs.symm
  have hfix : oddCoreIn (fixedSubgroup (f : MulAut X)) = ⊥ := by
    rw [hfs, fixedSubgroup_conj]
    exact hO s hPs hs2
  refine oddCoreIn_eq_bot_of_comm_mem (I := (innSubgroup X).subgroupOf 𝒳) f
    (oddCoreIn_centralizer_inner_eq_bot hZ 𝒳 hinn f hf2 hfix) ?_
  intro g hg hcomm
  have hodd_g : Odd (orderOf (g : MulAut X)) := by
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat (odd_card_oddCoreIn (Subgroup.centralizer ({f} : Set 𝒳)))
      (Subgroup.orderOf_dvd_natCard _ hg)
  refine Subgroup.mem_subgroupOf.mpr (hodd s hPs hs2 (g : MulAut X) hodd_g ?_)
  intro x hx
  have hxf : x ∈ fixedSubgroup (f : MulAut X) := by
    rw [hfs, fixedSubgroup_conj]
    exact hx
  have hmem : fixedToInn 𝒳 hinn (f : MulAut X) ⟨x, hxf⟩ ∈
      Subgroup.centralizer ({f} : Set 𝒳) ⊓ (innSubgroup X).subgroupOf 𝒳 := by
    rw [← range_fixedToInn hZ 𝒳 hinn f hf2]
    exact ⟨⟨x, hxf⟩, rfl⟩
  have h1 := congrArg Subtype.val (hcomm _ hmem)
  have h2 : (g : MulAut X) * MulAut.conj x = MulAut.conj x * (g : MulAut X) := h1
  have h3 : MulAut.conj ((g : MulAut X) x) = MulAut.conj x := by
    rw [← mul_conj_mul_inv, h2]
    group
  exact conj_injective_of_center_eq_bot hZ h3

theorem autOddFreeInner_of_centralizing_inner (hZ : Subgroup.center X = ⊥)
    (hO : ∀ x : X, orderOf x = 2 → involutionOddCore x = ⊥)
    (hodd : ∀ s : X, orderOf s = 2 → ∀ α : MulAut X, Odd (orderOf α) →
      (∀ x ∈ Subgroup.centralizer ({s} : Set X), α x = x) → α ∈ innSubgroup X) :
    AutOddFreeInner X := by
  intro 𝒳 hinn f hfinn hf
  obtain ⟨s, hs⟩ := hfinn
  exact autOddFreeInnerOn_of_centralizing_inner (fun _ => True) hZ (fun x _ => hO x)
    (fun s _ => hodd s) 𝒳 hinn f s hs trivial hf

theorem autOddFreeInner_of_oddCoreFree (hZ : Subgroup.center X = ⊥)
    (hO : ∀ x : X, orderOf x = 2 → involutionOddCore x = ⊥)
    (hodd : ∀ α : MulAut X, Odd (orderOf α) → α ∈ innSubgroup X) : AutOddFreeInner X :=
  autOddFreeInner_of_centralizing_inner hZ hO fun _ _ α hα _ => hodd α hα

end AutFixed

section Transport

theorem AutOddFree.of_mulEquiv {X X' : Type} [Group X] [Finite X] [Group X'] [Finite X']
    (e : X ≃* X') (h : AutOddFree X) : AutOddFree X' := by
  intro 𝒳' hinn' f' hf'
  set φ : MulAut X ≃* MulAut X' := MulAut.congr e with hφ
  set 𝒳 : Subgroup (MulAut X) := 𝒳'.map φ.symm.toMonoidHom with h𝒳
  have hinn : innSubgroup X ≤ 𝒳 := by
    rintro _ ⟨x, rfl⟩
    refine ⟨φ (MulAut.conj x), hinn' ⟨e x, ?_⟩, by simp⟩
    ext y
    simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
  let ε : ↥𝒳' ≃* ↥𝒳 := φ.symm.subgroupMap 𝒳'
  have hf : orderOf (ε f') = 2 := by rw [MulEquiv.orderOf_eq]; exact hf'
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv ε f' (h 𝒳 hinn (ε f') hf)

variable (X : Type) [Group X]

@[expose] noncomputable def autToCentralQuotient : MulAut X →* MulAut (X ⧸ Subgroup.center X) where
  toFun α := QuotientGroup.congr _ _ α (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' α β := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

variable {X}

theorem autToCentralQuotient_mk (α : MulAut X) (x : X) :
    autToCentralQuotient X α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  rfl

theorem autToCentralQuotient_injective [Group.IsPerfect X] :
    Function.Injective (autToCentralQuotient X) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  have h : (α : X →* X) = MonoidHom.id X := by
    refine CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect
      (θ := QuotientGroup.mk' (Subgroup.center X))
      (fun y hy => (QuotientGroup.eq_one_iff y).mp hy) _ _ fun x => ?_
    have := DFunLike.congr_fun hα (QuotientGroup.mk x)
    rw [autToCentralQuotient_mk] at this
    exact this
  ext x
  exact DFunLike.congr_fun h x

theorem autOddFree_of_centralQuotient [Finite X] [Group.IsPerfect X]
    (h : AutOddFree (X ⧸ Subgroup.center X)) : AutOddFree X := by
  intro 𝒳 hinn f hf
  have hΦ := autToCentralQuotient_injective (X := X)
  set 𝒳' := 𝒳.map (autToCentralQuotient X) with h𝒳'
  have hinn' : innSubgroup (X ⧸ Subgroup.center X) ≤ 𝒳' := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨MulAut.conj x, hinn ⟨x, rfl⟩, ?_⟩
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  let ε : ↥𝒳 ≃* ↥𝒳' := 𝒳.equivMapOfInjective (autToCentralQuotient X) hΦ
  have hf' : orderOf (ε f) = 2 := by rw [MulEquiv.orderOf_eq]; exact hf
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv ε f (h 𝒳' hinn' (ε f) hf')

theorem autOddFreeInner_of_centralQuotient [Finite X] [Group.IsPerfect X]
    (h : AutOddFreeInner (X ⧸ Subgroup.center X)) : AutOddFreeInner X := by
  intro 𝒳 hinn f hfinn hf
  have hΦ := autToCentralQuotient_injective (X := X)
  set 𝒳' := 𝒳.map (autToCentralQuotient X) with h𝒳'
  have hinn' : innSubgroup (X ⧸ Subgroup.center X) ≤ 𝒳' := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨MulAut.conj x, hinn ⟨x, rfl⟩, ?_⟩
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  let ε : ↥𝒳 ≃* ↥𝒳' := 𝒳.equivMapOfInjective (autToCentralQuotient X) hΦ
  have hf' : orderOf (ε f) = 2 := by rw [MulEquiv.orderOf_eq]; exact hf
  have hεinn : ((ε f : ↥𝒳') : MulAut (X ⧸ Subgroup.center X)) ∈
      innSubgroup (X ⧸ Subgroup.center X) := by
    obtain ⟨x, hx⟩ := hfinn
    refine ⟨QuotientGroup.mk x, ?_⟩
    show MulAut.conj (QuotientGroup.mk x) = autToCentralQuotient X (f : MulAut X)
    rw [← hx]
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv ε f (h 𝒳' hinn' (ε f) hεinn hf')

end Transport

end CFSG.ClassicalInvolution.Q3.Q3NM
