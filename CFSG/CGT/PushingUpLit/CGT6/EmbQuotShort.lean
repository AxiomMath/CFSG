module

public import CFSG.CGT.PushingUpLit.CGT6.EmbConjMod

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit
open CFSG.Quasithin (commV)
open scoped commutatorElement

section Residual

theorem oResidualTwo_eq_top_of_surjective {L M : Type} [Group L] [Group M] (f : L →* M)
    (hf : Function.Surjective f) (h : oResidualTwo L = ⊤) : oResidualTwo M = ⊤ := by
  rw [oResidualTwo_eq_top_iff]
  intro N' hN' hpow
  have hN : (N'.comap f).Normal := hN'.comap f
  have htop : N'.comap f = ⊤ := by
    refine (oResidualTwo_eq_top_iff.mp h) _ hN fun g => ?_
    obtain ⟨k, hk⟩ := hpow (f g)
    exact ⟨k, by rw [Subgroup.mem_comap, map_pow]; exact hk⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := hf x
  have : y ∈ N'.comap f := by rw [htop]; trivial
  exact this

theorem eq_one_of_oResidualTwo_eq_top {K Q : Type} [Group K] [Group Q] (hK : oResidualTwo K = ⊤)
    (hQ : IsPGroup 2 Q) (f : K →* Q) (x : K) : f x = 1 := by
  have h := oResidualTwo_eq_top_iff.mp hK f.ker inferInstance fun g => by
    obtain ⟨k, hk⟩ := hQ (f g)
    exact ⟨k, by rw [MonoidHom.mem_ker, map_pow]; exact hk⟩
  rw [← MonoidHom.mem_ker, h]
  trivial

end Residual

section Prelim

variable {L L' : Type} [Group L] [Group L'] {Θ : L →* L'}

theorem TwoQuot.apply_mem_shortU (h : TwoQuot Θ) {u : L} (hu : u ∈ shortU L) :
    Θ u ∈ shortU L' := by
  rw [← h.map_shortU]
  exact Subgroup.mem_map_of_mem Θ hu

theorem TwoQuot.exists_mem_shortU (h : TwoQuot Θ) {y : L'} (hy : y ∈ shortU L') :
    ∃ u ∈ shortU L, Θ u = y := by
  rw [← h.map_shortU] at hy
  exact hy

@[expose] def TwoQuot.restrictU (h : TwoQuot Θ) : ↥(shortU L) →* ↥(shortU L') :=
  (Θ.comp (shortU L).subtype).codRestrict (shortU L') fun u => h.apply_mem_shortU u.2

theorem TwoQuot.coe_restrictU (h : TwoQuot Θ) (u : ↥(shortU L)) :
    ((h.restrictU u : ↥(shortU L')) : L') = Θ (u : L) := rfl

theorem TwoQuot.restrictU_surjective (h : TwoQuot Θ) : Function.Surjective h.restrictU := by
  intro y
  obtain ⟨u, hu, hΘ⟩ := h.exists_mem_shortU y.2
  exact ⟨⟨u, hu⟩, Subtype.ext hΘ⟩

theorem CentralTwoQuot.mem_center_of_map_mem_center (h : CentralTwoQuot Θ)
    (hres : oResidualTwo L = ⊤) {x : L} (hx : Θ x ∈ Subgroup.center L') :
    x ∈ Subgroup.center L := by
  have hc : ∀ l : L, x * l * x⁻¹ * l⁻¹ ∈ Θ.ker := fun l => by
    rw [MonoidHom.mem_ker]
    have := Subgroup.mem_center_iff.mp hx (Θ l)
    simp only [map_mul, map_inv]
    rw [← this]
    group
  let f : L →* ↥Θ.ker := MonoidHom.mk' (fun l => ⟨x * l * x⁻¹ * l⁻¹, hc l⟩) fun l l' => by
    apply Subtype.ext
    have hz := Subgroup.mem_center_iff.mp (h.central (hc l')) l
    show x * (l * l') * x⁻¹ * (l * l')⁻¹ = (x * l * x⁻¹ * l⁻¹) * (x * l' * x⁻¹ * l'⁻¹)
    calc x * (l * l') * x⁻¹ * (l * l')⁻¹
        = (x * l * x⁻¹ * l⁻¹) * (l * (x * l' * x⁻¹ * l'⁻¹)) * l⁻¹ := by group
      _ = (x * l * x⁻¹ * l⁻¹) * ((x * l' * x⁻¹ * l'⁻¹) * l) * l⁻¹ := by rw [hz]
      _ = (x * l * x⁻¹ * l⁻¹) * (x * l' * x⁻¹ * l'⁻¹) := by group
  refine Subgroup.mem_center_iff.mpr fun l => ?_
  have h1 := congrArg Subtype.val (eq_one_of_oResidualTwo_eq_top hres h.two f l)
  have h2 : x * l * x⁻¹ * l⁻¹ = 1 := h1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

theorem CentralTwoQuot.mem_shortC_iff (h : CentralTwoQuot Θ) (hres : oResidualTwo L = ⊤) {u : L}
    (hu : u ∈ shortU L) : u ∈ shortC L ↔ Θ u ∈ shortC L' := by
  have hΘu : Θ u ∈ shortU L' := h.apply_mem_shortU hu
  simp only [shortC, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, hc⟩
    refine ⟨hΘu, Subgroup.mem_center_iff.mpr fun l' => ?_⟩
    obtain ⟨l, rfl⟩ := h.surj l'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc l]
  · rintro ⟨-, hc⟩
    exact ⟨hu, h.mem_center_of_map_mem_center hres hc⟩

theorem CentralTwoQuot.restrictU_ker_le (h : CentralTwoQuot Θ) :
    h.restrictU.ker ≤ (shortC L).subgroupOf (shortU L) := by
  intro u hu
  rw [Subgroup.mem_subgroupOf]
  have hΘ : Θ (u : L) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
  exact ⟨u.2, h.central (MonoidHom.mem_ker.mpr hΘ)⟩

theorem CentralTwoQuot.exists_descend {M : Type*} [Group M] (h : CentralTwoQuot Θ)
    (hres : oResidualTwo L = ⊤) (ψ : ↥(shortU L) →* M)
    (hker : ψ.ker = (shortC L).subgroupOf (shortU L)) :
    ∃ ψ' : ↥(shortU L') →* M, (∀ u, ψ' (h.restrictU u) = ψ u) ∧
      ψ'.ker = (shortC L').subgroupOf (shortU L') := by
  have hle : h.restrictU.ker ≤ ψ.ker := hker ▸ h.restrictU_ker_le
  have hcomp : ∀ u, (h.restrictU.liftOfSurjective h.restrictU_surjective ⟨ψ, hle⟩)
      (h.restrictU u) = ψ u := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply h.restrictU _ _ ⟨ψ, hle⟩ u
  refine ⟨h.restrictU.liftOfSurjective h.restrictU_surjective ⟨ψ, hle⟩, hcomp, ?_⟩
  ext y
  obtain ⟨u, rfl⟩ := h.restrictU_surjective y
  rw [MonoidHom.mem_ker, hcomp, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf, h.mem_shortC_iff hres u.2]
  rfl

theorem CentralTwoQuot.exists_descend_module {A M : Type*} [Group A] [Group M]
    (h : CentralTwoQuot Θ) (hres : oResidualTwo L = ⊤) (φ : (L ⧸ pCore 2 L) ≃* A)
    (act : A → M → M) (ψ : ↥(shortU L) →* M) (hker : ψ.ker = (shortC L).subgroupOf (shortU L))
    (hact : ∀ (l u : L) (hu : u ∈ shortU L) (hu' : l * u * l⁻¹ ∈ shortU L),
      ψ ⟨l * u * l⁻¹, hu'⟩ = act (φ (l : L ⧸ pCore 2 L)) (ψ ⟨u, hu⟩)) :
    ∃ ψ' : ↥(shortU L') →* M, (∀ u, ψ' (h.restrictU u) = ψ u) ∧
      ψ'.ker = (shortC L').subgroupOf (shortU L') ∧
      ∀ (l u : L') (hu : u ∈ shortU L') (hu' : l * u * l⁻¹ ∈ shortU L'),
        ψ' ⟨l * u * l⁻¹, hu'⟩ =
          act ((h.toTwoQuot.quotPCore.symm.trans φ) (l : L' ⧸ pCore 2 L')) (ψ' ⟨u, hu⟩) := by
  obtain ⟨ψ', hcomp, hker'⟩ := h.exists_descend hres ψ hker
  refine ⟨ψ', hcomp, hker', fun l' u' hu hu' => ?_⟩
  obtain ⟨l, rfl⟩ := h.surj l'
  obtain ⟨u, hu₀, rfl⟩ := h.exists_mem_shortU hu
  have hu₁ : l * u * l⁻¹ ∈ shortU L := shortU_normal.conj_mem _ hu₀ l
  have e1 : h.restrictU ⟨l * u * l⁻¹, hu₁⟩ = ⟨Θ l * Θ u * (Θ l)⁻¹, hu'⟩ :=
    Subtype.ext (by rw [TwoQuot.coe_restrictU, map_mul, map_mul, map_inv])
  have e3 : h.toTwoQuot.quotPCore.symm ((Θ l : L') : L' ⧸ pCore 2 L') =
      (l : L ⧸ pCore 2 L) := by
    rw [← h.toTwoQuot.quotPCore_mk]
    exact MulEquiv.symm_apply_apply _ _
  calc ψ' ⟨Θ l * Θ u * (Θ l)⁻¹, hu'⟩ = ψ' (h.restrictU ⟨l * u * l⁻¹, hu₁⟩) := by rw [e1]
    _ = ψ ⟨l * u * l⁻¹, hu₁⟩ := hcomp _
    _ = act (φ (l : L ⧸ pCore 2 L)) (ψ ⟨u, hu₀⟩) := hact l u hu₀ hu₁
    _ = act (φ (l : L ⧸ pCore 2 L)) (ψ' ⟨Θ u, hu⟩) := congrArg _ (hcomp ⟨u, hu₀⟩).symm
    _ = _ := by simp only [MulEquiv.trans_apply, e3]

theorem CentralTwoQuot.module_of_quot {A M : Type*} [Group A] [Group M]
    (h : CentralTwoQuot Θ) (hres : oResidualTwo L = ⊤) (φ' : (L' ⧸ pCore 2 L') ≃* A)
    (act : A → M → M) (ψ' : ↥(shortU L') →* M)
    (hker : ψ'.ker = (shortC L').subgroupOf (shortU L'))
    (hact : ∀ (l u : L') (hu : u ∈ shortU L') (hu' : l * u * l⁻¹ ∈ shortU L'),
      ψ' ⟨l * u * l⁻¹, hu'⟩ = act (φ' (l : L' ⧸ pCore 2 L')) (ψ' ⟨u, hu⟩)) :
    (ψ'.comp h.restrictU).ker = (shortC L).subgroupOf (shortU L) ∧
      ∀ (l u : L) (hu : u ∈ shortU L) (hu' : l * u * l⁻¹ ∈ shortU L),
        (ψ'.comp h.restrictU) ⟨l * u * l⁻¹, hu'⟩ =
          act ((h.toTwoQuot.quotPCore.trans φ') (l : L ⧸ pCore 2 L))
            ((ψ'.comp h.restrictU) ⟨u, hu⟩) := by
  refine ⟨?_, fun l u hu hu' => ?_⟩
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (h.mem_shortC_iff hres u.2).symm
  · have hmem : Θ l * Θ u * (Θ l)⁻¹ ∈ shortU L' := by
      have := h.apply_mem_shortU hu'
      rwa [map_mul, map_mul, map_inv] at this
    have e1 : h.restrictU ⟨l * u * l⁻¹, hu'⟩ = ⟨Θ l * Θ u * (Θ l)⁻¹, hmem⟩ :=
      Subtype.ext (by rw [TwoQuot.coe_restrictU, map_mul, map_mul, map_inv])
    have e2 : h.restrictU ⟨u, hu⟩ = ⟨Θ u, h.apply_mem_shortU hu⟩ := rfl
    simp only [MonoidHom.comp_apply, e1, e2]
    exact hact (Θ l) (Θ u) (h.apply_mem_shortU hu) hmem

theorem CentralTwoQuot.altModuleWith_quot (h : CentralTwoQuot Θ) (hres : oResidualTwo L = ⊤)
    {n : ℕ} {φ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin (2 * n + 1))}
    (hn : IsNaturalAltModuleWith L n φ) :
    IsNaturalAltModuleWith L' n (h.toTwoQuot.quotPCore.symm.trans φ) := by
  obtain ⟨ψ, hsum, hsurj, hker, hact⟩ := hn
  obtain ⟨ψ', hcomp, hker', hact'⟩ := h.exists_descend_module hres φ
    (fun σ m => Multiplicative.ofAdd (permActionTwo (σ : Equiv.Perm (Fin (2 * n + 1)))
      (Multiplicative.toAdd m))) ψ hker hact
  refine ⟨ψ', fun y => ?_, fun v hv => ?_, hker', hact'⟩
  · obtain ⟨u, rfl⟩ := h.restrictU_surjective y
    rw [hcomp]
    exact hsum u
  · obtain ⟨u, hu⟩ := hsurj v hv
    exact ⟨h.restrictU u, by rw [hcomp]; exact hu⟩

theorem CentralTwoQuot.altModuleWith_of_quot (h : CentralTwoQuot Θ) (hres : oResidualTwo L = ⊤)
    {n : ℕ} {φ' : (L' ⧸ pCore 2 L') ≃* alternatingGroup (Fin (2 * n + 1))}
    (hn : IsNaturalAltModuleWith L' n φ') :
    IsNaturalAltModuleWith L n (h.toTwoQuot.quotPCore.trans φ') := by
  obtain ⟨ψ', hsum, hsurj, hker, hact⟩ := hn
  obtain ⟨hker', hact'⟩ := h.module_of_quot hres φ'
    (fun σ m => Multiplicative.ofAdd (permActionTwo (σ : Equiv.Perm (Fin (2 * n + 1)))
      (Multiplicative.toAdd m))) ψ' hker hact
  refine ⟨ψ'.comp h.restrictU, fun u => hsum _, fun v hv => ?_, hker', hact'⟩
  obtain ⟨y, hy⟩ := hsurj v hv
  obtain ⟨u, rfl⟩ := h.restrictU_surjective y
  exact ⟨u, hy⟩

theorem CentralTwoQuot.slModule_quot (h : CentralTwoQuot Θ) (hres : oResidualTwo L = ⊤) {n : ℕ}
    (hn : IsNaturalSLTwoModule L n) : IsNaturalSLTwoModule L' n := by
  obtain ⟨φ, ψ, hsurj, hker, hact⟩ := hn
  obtain ⟨ψ', hcomp, hker', hact'⟩ := h.exists_descend_module hres φ
    (fun g m => Multiplicative.ofAdd
      ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd m)))
    ψ hker hact
  refine ⟨h.toTwoQuot.quotPCore.symm.trans φ, ψ', fun v => ?_, hker', hact'⟩
  obtain ⟨u, hu⟩ := hsurj v
  exact ⟨h.restrictU u, by rw [hcomp]; exact hu⟩

theorem CentralTwoQuot.slModule_of_quot (h : CentralTwoQuot Θ) (hres : oResidualTwo L = ⊤) {n : ℕ}
    (hn : IsNaturalSLTwoModule L' n) : IsNaturalSLTwoModule L n := by
  obtain ⟨φ', ψ', hsurj, hker, hact⟩ := hn
  obtain ⟨hker', hact'⟩ := h.module_of_quot hres φ'
    (fun g m => Multiplicative.ofAdd
      ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd m)))
    ψ' hker hact
  refine ⟨h.toTwoQuot.quotPCore.trans φ', ψ'.comp h.restrictU, fun v => ?_, hker', hact'⟩
  obtain ⟨y, hy⟩ := hsurj v
  obtain ⟨u, rfl⟩ := h.restrictU_surjective y
  exact ⟨u, hy⟩

end Prelim

section Central

variable {L L' : Type} [Group L] [Group L'] [Finite L] [Finite L'] {Θ : L →* L'}

theorem CentralTwoQuot.isShortGroup_quot (h : CentralTwoQuot Θ) (hres : oResidualTwo L = ⊤)
    (hL : IsShortGroup L) : IsShortGroup L' := by
  have hUc : ∀ u ∈ shortU L, ∀ o ∈ pCore 2 L, u * o = o * u := fun u hu o ho =>
    ((shortU_le_center_iff.mp hL.U_le_center) u hu).2 o ho
  have hU' := h.shortU_comm_quot hUc
  refine ⟨?_, oResidualTwo_eq_top_of_surjective Θ h.surj hL.residual_eq, ?_, ?_, ?_, ?_⟩
  · exact (isCharacteristicP_iff_generalizedFitting_eq_pCore L' 2).mp
      (h.isCharacteristicP_quot
        ((isCharacteristicP_iff_generalizedFitting_eq_pCore L 2).mpr hL.fitting_eq))
  · rcases hL.quotient_type with hq | hp
    · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv h.toTwoQuot.quotPCore hq)
    · exact Or.inr (by rwa [← Nat.card_congr h.toTwoQuot.quotPCore.toEquiv])
  · rw [shortU_le_center_iff]
    exact fun u hu => ⟨shortU_le_pCore' L' hu, hU' u hu⟩
  · refine lt_of_le_of_ne shortC_le_shortU fun heq => ?_
    refine lt_irrefl _ (lt_of_lt_of_le hL.nonzero fun u hu => ?_)
    rw [h.mem_shortC_iff hres hu, heq]
    exact h.apply_mem_shortU hu
  · intro N' hN' hN'U hCN'
    have hNn : (N'.comap Θ ⊓ shortU L).Normal := by
      have := hN'.comap Θ
      infer_instance
    have hCN : shortC L ≤ N'.comap Θ ⊓ shortU L := fun c hc =>
      ⟨hCN' ((h.mem_shortC_iff hres (shortC_le_shortU hc)).mp hc), shortC_le_shortU hc⟩
    rcases hL.irreducible _ hNn inf_le_right hCN with h1 | h1
    · left
      refine le_antisymm (fun y hy => ?_) hCN'
      obtain ⟨u, hu, rfl⟩ := h.exists_mem_shortU (hN'U hy)
      have hmem : u ∈ N'.comap Θ ⊓ shortU L := ⟨hy, hu⟩
      rw [h1] at hmem
      exact (h.mem_shortC_iff hres hu).mp hmem
    · right
      refine le_antisymm hN'U fun y hy => ?_
      obtain ⟨u, hu, rfl⟩ := h.exists_mem_shortU hy
      have hmem : u ∈ N'.comap Θ ⊓ shortU L := by rw [h1]; exact hu
      exact hmem.1

theorem CentralTwoQuot.inClassX_quot (h : CentralTwoQuot Θ) (hres : oResidualTwo L = ⊤) :
    InClassX L → InClassX L' := by
  rintro ⟨hS, hnat⟩
  refine ⟨h.isShortGroup_quot hres hS, ?_⟩
  rcases hnat with ⟨n, hn, hnat⟩ | ⟨n, hn, hnat⟩
  · obtain ⟨φ, hφ⟩ := isNaturalAltModule_iff.mp hnat
    exact Or.inl ⟨n, hn, isNaturalAltModule_iff.mpr ⟨_, h.altModuleWith_quot hres hφ⟩⟩
  · exact Or.inr ⟨n, hn, h.slModule_quot hres hnat⟩

theorem CentralTwoQuot.isShortGroup_of_quot (h : CentralTwoQuot Θ) (hres : oResidualTwo L = ⊤)
    (hUc : ∀ u ∈ shortU L, ∀ o ∈ pCore 2 L, u * o = o * u) (h' : IsShortGroup L') :
    IsShortGroup L := by
  refine ⟨?_, hres, ?_, ?_, ?_, ?_⟩
  · exact (isCharacteristicP_iff_generalizedFitting_eq_pCore L 2).mp
      (h.isCharacteristicP_of
        ((isCharacteristicP_iff_generalizedFitting_eq_pCore L' 2).mpr h'.fitting_eq))
  · rcases h'.quotient_type with hq | hp
    · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv h.toTwoQuot.quotPCore.symm hq)
    · exact Or.inr (by rwa [← Nat.card_congr h.toTwoQuot.quotPCore.symm.toEquiv])
  · rw [shortU_le_center_iff]
    exact fun u hu => ⟨shortU_le_pCore' L hu, hUc u hu⟩
  · obtain ⟨y, hyU, hyC⟩ := IsConcreteLE.exists_of_lt h'.nonzero
    obtain ⟨u, hu, rfl⟩ := h.exists_mem_shortU hyU
    refine lt_of_le_of_ne shortC_le_shortU fun heq => hyC ?_
    have : u ∈ shortC L := heq ▸ hu
    exact (h.mem_shortC_iff hres hu).mp this
  · intro N hN hNU hCN
    have hN' : (N.map Θ).Normal := hN.map Θ h.surj
    have hN'U : N.map Θ ≤ shortU L' := h.map_shortU ▸ Subgroup.map_mono hNU
    have hC'N : shortC L' ≤ N.map Θ := by
      intro y hy
      obtain ⟨u, hu, rfl⟩ := h.exists_mem_shortU (shortC_le_shortU hy)
      exact ⟨u, hCN ((h.mem_shortC_iff hres hu).mpr hy), rfl⟩
    rcases h'.irreducible _ hN' hN'U hC'N with h1 | h1
    · left
      refine le_antisymm (fun n hn => ?_) hCN
      have : Θ n ∈ N.map Θ := Subgroup.mem_map_of_mem Θ hn
      rw [h1] at this
      exact (h.mem_shortC_iff hres (hNU hn)).mpr this
    · right
      refine le_antisymm hNU fun u hu => ?_
      have : Θ u ∈ N.map Θ := by rw [h1]; exact h.apply_mem_shortU hu
      obtain ⟨n, hn, hΘ⟩ := this
      have hk : n⁻¹ * u ∈ shortC L :=
        ⟨(shortU L).mul_mem ((shortU L).inv_mem (hNU hn)) hu,
          h.central (MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hΘ, inv_mul_cancel]))⟩
      simpa using N.mul_mem hn (hCN hk)

theorem CentralTwoQuot.inClassX_of_quot (h : CentralTwoQuot Θ) (hres : oResidualTwo L = ⊤)
    (hUc : ∀ u ∈ shortU L, ∀ o ∈ pCore 2 L, u * o = o * u) : InClassX L' → InClassX L := by
  rintro ⟨hS, hnat⟩
  refine ⟨h.isShortGroup_of_quot hres hUc hS, ?_⟩
  rcases hnat with ⟨n, hn, hnat⟩ | ⟨n, hn, hnat⟩
  · obtain ⟨φ, hφ⟩ := isNaturalAltModule_iff.mp hnat
    exact Or.inl ⟨n, hn, isNaturalAltModule_iff.mpr ⟨_, h.altModuleWith_of_quot hres hφ⟩⟩
  · exact Or.inr ⟨n, hn, h.slModule_of_quot hres hnat⟩

end Central

section Arrow

variable {Γ Γ' : Type} [Group Γ] [Group Γ']

theorem arrowNat_of_central' {Y X : Subgroup Γ} {Yb Xb : Subgroup Γ'} [Finite ↥X] [Finite ↥Xb]
    {ΘX : ↥X →* ↥Xb} {ΘY : ↥Y →* ↥Yb} (hX : CentralTwoQuot ΘX) (hres : oResidualTwo ↥X = ⊤)
    (hY : CentralTwoQuot ΘY) (hYX : Y ≤ X)
    (hcompat : ∀ y : ↥Y, ((ΘY y : ↥Yb) : Γ') = ((ΘX ⟨y, hYX y.2⟩ : ↥Xb) : Γ'))
    (hsU : (shortU ↥Y).map Y.subtype ≤ (shortU ↥X).map X.subtype) (heq : Yb = Xb → Y = X)
    (harr : ArrowNat Yb Xb) : ArrowNat Y X := by
  rcases harr with h1 | ⟨a, b, φ, F, ⟨ψ⟩, hnat, hF, -, -, himg⟩
  · exact Or.inl (heq h1)
  · right
    refine ⟨a, b, hX.toTwoQuot.quotPCore.trans φ, F, ⟨hY.quotPCore.trans ψ⟩,
      hX.altModuleWith_of_quot hres hnat, hF, hsU, hYX, ?_⟩
    rw [← himg]
    ext σ
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply]
    constructor
    · rintro ⟨q, ⟨y', hy', rfl⟩, rfl⟩
      refine ⟨_, ⟨ΘX y', ?_, rfl⟩, rfl⟩
      rw [← hcompat ⟨y', hy'⟩]
      exact (ΘY ⟨y', hy'⟩).2
    · rintro ⟨q, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨y, hy⟩ := hY.surj ⟨(z : Γ'), hz⟩
      refine ⟨_, ⟨⟨y.1, hYX y.2⟩, y.2, rfl⟩, ?_⟩
      have hz' : ΘX ⟨y.1, hYX y.2⟩ = z := by
        apply Subtype.ext
        rw [← hcompat y, hy]
      show φ (hX.toTwoQuot.quotPCore (((⟨y.1, hYX y.2⟩ : ↥X) : ↥X ⧸ pCore 2 ↥X))) =
        φ ((z : ↥Xb ⧸ pCore 2 ↥Xb))
      rw [← hz']
      rfl

end Arrow

section Yu

variable {V : Type} [CommGroup V]

theorem USelf_of_oResidualTwo [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {K : Subgroup (MulAut V)}
    (hK : oResidualTwo ↥K = ⊤) : USelf K := by
  intro N hN
  let N₀ : Subgroup ↥(commV K) := N.subgroupOf (commV K)
  have hgen : ∀ (g : ↥K) (v : V),
      (⟨(g : MulAut V) v * v⁻¹, commV_mem_of_apply K g v⟩ : ↥(commV K)) ∈ N₀ := by
    intro g v
    let f : ↥K →* ↥(commV K) ⧸ N₀ := MonoidHom.mk' (fun g =>
      QuotientGroup.mk ⟨(g : MulAut V) v * v⁻¹, commV_mem_of_apply K g v⟩) (fun g h => by
      let w : ↥(commV K) := ⟨(h : MulAut V) v * v⁻¹, commV_mem_of_apply K h v⟩
      let u₁ : ↥(commV K) := ⟨(g : MulAut V) (w : V) * (w : V)⁻¹,
        commV_mem_of_apply K g (w : V)⟩
      have hu₁ : u₁ ∈ N₀ := hN g g.2 w w.2
      have hprod : (⟨((g * h : ↥K) : MulAut V) v * v⁻¹, commV_mem_of_apply K (g * h) v⟩ :
          ↥(commV K)) = u₁ * w * ⟨(g : MulAut V) v * v⁻¹, commV_mem_of_apply K g v⟩ := by
        apply Subtype.ext
        show ((g * h : ↥K) : MulAut V) v * v⁻¹ = ((g : MulAut V) ((h : MulAut V) v * v⁻¹) *
          ((h : MulAut V) v * v⁻¹)⁻¹) * ((h : MulAut V) v * v⁻¹) * ((g : MulAut V) v * v⁻¹)
        rw [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
        group
      show QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
      rw [hprod, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff u₁).mpr hu₁, one_mul]
      exact mul_comm _ _)
    have hQ : IsPGroup 2 (↥(commV K) ⧸ N₀) := fun q => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨1, ?_⟩
      have ha : a ^ 2 = 1 := Subtype.ext (by simpa using hV (a : V))
      rw [pow_one, ← QuotientGroup.mk_pow, ha, QuotientGroup.mk_one]
    exact (QuotientGroup.eq_one_iff _).mp (eq_one_of_oResidualTwo_eq_top hK hQ f g)
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  exact hgen ⟨g, hg⟩ v

theorem oResidualTwo_yuHol_of_oResidualTwo [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {K : Subgroup (MulAut V)} (hK : oResidualTwo ↥K = ⊤) : oResidualTwo ↥(yuHol K) = ⊤ := by
  have h := oResidualTwo_yuHol_conjClosure (Y := K) (Xt := K)
    (SubTwo.noTwoQuotient_of_oResidualTwo hK) (USelf_of_oResidualTwo hV hK)
  rwa [show conjClosure K K = K from le_antisymm (conjClosure_le le_rfl) le_conjClosure] at h

theorem shortU_comm_pCore_yuHol_of_oTwoIn_eq_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {K : Subgroup (MulAut V)} (hK : oTwoIn K = ⊥) :
    ∀ u ∈ shortU ↥(yuHol K), ∀ o ∈ pCore 2 ↥(yuHol K), u * o = o * u := by
  have hp : pCore 2 ↥K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hK
  have hP : pCore 2 ↥(yuHol K) = (yuInc K).range := by
    rw [pCore_yuHol K hV, hp, MonoidHom.comap_bot, ker_yuProj]
  intro u hu o ho
  obtain ⟨a, ha⟩ : u ∈ (yuInc K).range := hP ▸ shortU_le_pCore' _ hu
  obtain ⟨b, hb⟩ : o ∈ (yuInc K).range := hP ▸ ho
  rw [← ha, ← hb]
  exact yuInc_comm K a b

end Yu

end CFSG.CGT.PushingUpLit.CGT6
