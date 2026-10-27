module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.Monster.B.TwoA.Base.ElemAut

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

variable {T : Type} [Group T]

@[expose] def BurgTorusFor (α : MulAut T) : Prop :=
  ∃ Q : Subgroup T, IsQuasisimple Q ∧ Q ≤ fixedSubgroup α ∧
    fixedSubgroup α ≤ normalizer (Q : Set T) ∧
  ∃ (u : T) (S : Subgroup T), orderOf u = 2 ∧ IsQuasisimple S ∧
    S ≤ centralizer ({u} : Set T) ∧ centralizer ({u} : Set T) ≤ normalizer (S : Set T) ∧
    (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧ Nonempty (S ≃* SL(2, GaloisField p n))) ∧
    (center S).map S.subtype = zpowers u ∧
    (∀ s, α s ∈ S ↔ s ∈ S) ∧ (∃ s ∈ S, α s ≠ s) ∧
    ∀ β : MulAut T, Odd (orderOf β) → α * β = β * α → (∀ x ∈ Q, β x = x) →
      (∀ s, β s ∈ S ↔ s ∈ S) ∧ ((∀ s ∈ S, β s = s) → β = 1)

theorem mul_conj_mul_inv (α : MulAut T) (x : T) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  ext y
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.apply_inv_self]

theorem conj_injective (hZ : center T = ⊥) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgZ : g ∈ center T := by
    rw [mem_center_iff]
    intro x
    have h := congrArg (fun φ : MulAut T => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * g = g * x * g⁻¹ * g := by rw [h]
      _ = g * x := by group
  rw [hZ, mem_bot] at hgZ
  exact hgZ

theorem mem_normalizer_map_conj {S : Subgroup T} {β : MulAut T} (hβ : ∀ s, β s ∈ S ↔ s ∈ S) :
    β ∈ normalizer ((S.map (MulAut.conj : T →* MulAut T) : Subgroup (MulAut T)) :
      Set (MulAut T)) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨β s, (hβ s).2 hs, (mul_conj_mul_inv β s).symm⟩
  · rintro ⟨s, hs, hs'⟩
    have hs'' : β (β⁻¹ s) ∈ S := by rw [MulAut.apply_inv_self]; exact hs
    refine ⟨β⁻¹ s, (hβ _).1 hs'', ?_⟩
    have e1 : h = β⁻¹ * MulAut.conj s * β := by
      change MulAut.conj s = β * h * β⁻¹ at hs'
      rw [hs']
      group
    have e2 := mul_conj_mul_inv β⁻¹ s
    rw [inv_inv] at e2
    rw [e1]
    exact e2.symm

theorem apply_eq_of_commute_conj (hZ : center T = ⊥) {β : MulAut T} {x : T}
    (h : β * MulAut.conj x = MulAut.conj x * β) : β x = x := by
  apply conj_injective hZ
  rw [← mul_conj_mul_inv, h, mul_inv_cancel_right]

theorem BurgTorusFor.congr {T' : Type} [Group T'] (e : T ≃* T') {α : MulAut T}
    (h : BurgTorusFor α) : BurgTorusFor (MulAut.congr e α) := by
  obtain ⟨Q, hQq, hQα, hQN, u, S, hu, hSq, hSu, hSN, ⟨p, n, hp, hp2, hn, ⟨eS⟩⟩, hZS, hαS,
    ⟨s₀, hs₀, hαs₀⟩, hβ⟩ := h
  have hα' : ∀ y, MulAut.congr e α y = e (α (e.symm y)) := fun _ => rfl
  have hmem : ∀ (A : Subgroup T) (y : T'), y ∈ A.map e.toMonoidHom ↔ e.symm y ∈ A := by
    intro A y
    rw [mem_map_equiv]
  have hfix : fixedSubgroup (MulAut.congr e α) = (fixedSubgroup α).map e.toMonoidHom := by
    ext y
    rw [hmem]
    change MulAut.congr e α y = y ↔ α (e.symm y) = e.symm y
    rw [hα']
    constructor
    · intro hy
      have := congrArg e.symm hy
      rwa [MulEquiv.symm_apply_apply] at this
    · intro hy
      rw [hy, MulEquiv.apply_symm_apply]
  have hcen : centralizer ({e u} : Set T') = (centralizer ({u} : Set T)).map e.toMonoidHom := by
    ext y
    rw [hmem, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have := congrArg e.symm hy
      rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
    · intro hy
      have := congrArg e hy
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  have hnorm : ∀ {A N : Subgroup T}, N ≤ normalizer (A : Set T) →
      N.map e.toMonoidHom ≤ normalizer ((A.map e.toMonoidHom : Subgroup T') : Set T') := by
    intro A N hN
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    change e.symm y ∈ A ↔ e.symm (e g * y * (e g)⁻¹) ∈ A
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact (mem_normalizer_iff.1 (hN hg)) _
  let eQ : Q ≃* Q.map e.toMonoidHom := Q.equivMapOfInjective e.toMonoidHom e.injective
  let eS' : S ≃* S.map e.toMonoidHom := S.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨Q.map e.toMonoidHom, LocalCores.isQuasisimple_of_mulEquiv eQ hQq, ?_, ?_, e u,
    S.map e.toMonoidHom, ?_, LocalCores.isQuasisimple_of_mulEquiv eS' hSq, ?_, ?_,
    ⟨p, n, hp, hp2, hn, ⟨eS'.symm.trans eS⟩⟩, ?_, ?_, ⟨e s₀, ⟨s₀, hs₀, rfl⟩, ?_⟩, ?_⟩
  · rw [hfix]
    exact map_mono hQα
  · rw [hfix]
    exact hnorm hQN
  · rw [MulEquiv.orderOf_eq]
    exact hu
  · rw [hcen]
    exact map_mono hSu
  · rw [hcen]
    exact hnorm hSN
  · have hcomp : (S.map e.toMonoidHom).subtype.comp (eS' : S →* S.map e.toMonoidHom) =
        e.toMonoidHom.comp S.subtype := by
      ext x
      rfl
    rw [← map_center_eq eS', map_map, hcomp, ← map_map, hZS, MonoidHom.map_zpowers]
    rfl
  · intro y
    rw [hmem, hmem, hα', MulEquiv.symm_apply_apply]
    exact hαS _
  · rw [hα', MulEquiv.symm_apply_apply]
    intro h
    exact hαs₀ (e.injective h)
  · intro β' hβ' hcomm hQfix
    set β := (MulAut.congr e).symm β' with hβdef
    have hβ'eq : β' = MulAut.congr e β := by rw [hβdef, MulEquiv.apply_symm_apply]
    have hβapp : ∀ x, β x = e.symm (β' (e x)) := fun _ => rfl
    have hodd : Odd (orderOf β) := by
      rw [hβdef, MulEquiv.orderOf_eq]
      exact hβ'
    have hcomm' : α * β = β * α := by
      apply (MulAut.congr e).injective
      rw [map_mul, map_mul, ← hβ'eq]
      exact hcomm
    have hQfix' : ∀ x ∈ Q, β x = x := by
      intro x hx
      rw [hβapp, hQfix (e x) ⟨x, hx, rfl⟩, MulEquiv.symm_apply_apply]
    obtain ⟨hβS, hβ1⟩ := hβ β hodd hcomm' hQfix'
    refine ⟨fun y => ?_, fun hSfix => ?_⟩
    · rw [hmem, hmem]
      have := hβS (e.symm y)
      rwa [hβapp, MulEquiv.apply_symm_apply] at this
    · have h1 : β = 1 := hβ1 fun x hx => by
        rw [hβapp, hSfix (e x) ⟨x, hx, rfl⟩, MulEquiv.symm_apply_apply]
      rw [hβ'eq, h1, map_one]

theorem BurgTorusFor.conj (ψ : MulAut T) {α : MulAut T} (h : BurgTorusFor α) :
    BurgTorusFor (ψ * α * ψ⁻¹) := by
  have e : MulAut.congr ψ α = ψ * α * ψ⁻¹ := by
    ext x
    rfl
  rw [← e]
  exact h.congr ψ

theorem normal_map_centralizer (hZ : center T = ⊥) {B : Subgroup (MulAut T)}
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (x : T) :
    ((centralizer ({x} : Set T)).map (MulAut.conj : T →* MulAut T) ≤
        B ⊓ centralizer ({MulAut.conj x} : Set (MulAut T))) ∧
      (((centralizer ({x} : Set T)).map (MulAut.conj : T →* MulAut T)).subgroupOf
        (B ⊓ centralizer ({MulAut.conj x} : Set (MulAut T)))).Normal := by
  have hle : (centralizer ({x} : Set T)).map (MulAut.conj : T →* MulAut T) ≤
      B ⊓ centralizer ({MulAut.conj x} : Set (MulAut T)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hB ⟨g, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      (mem_centralizer_singleton_iff.1 hg)]
  refine ⟨hle, (normal_subgroupOf_iff hle).2 ?_⟩
  rintro _ k ⟨g, hg, rfl⟩ hk
  have hk' : k ∈ centralizer ({MulAut.conj x} : Set (MulAut T)) := (Subgroup.mem_inf.1 hk).2
  refine ⟨k g, ?_, (mul_conj_mul_inv k g).symm⟩
  have hkx : k x = x := apply_eq_of_commute_conj hZ (mem_centralizer_singleton_iff.1 hk')
  have hg' : g ∈ centralizer ({x} : Set T) := hg
  show k g ∈ centralizer ({x} : Set T)
  rw [mem_centralizer_singleton_iff, ← hkx, ← map_mul, ← map_mul,
    (mem_centralizer_singleton_iff.1 hg')]

theorem normal_map_fixedSubgroup {B : Subgroup (MulAut T)}
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (α : MulAut T) :
    ((fixedSubgroup α).map (MulAut.conj : T →* MulAut T) ≤
        B ⊓ centralizer ({α} : Set (MulAut T))) ∧
      (((fixedSubgroup α).map (MulAut.conj : T →* MulAut T)).subgroupOf
        (B ⊓ centralizer ({α} : Set (MulAut T)))).Normal := by
  have hle : (fixedSubgroup α).map (MulAut.conj : T →* MulAut T) ≤
      B ⊓ centralizer ({α} : Set (MulAut T)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hB ⟨g, rfl⟩, ?_⟩
    have hg' : α g = g := hg
    rw [mem_centralizer_singleton_iff]
    have := mul_conj_mul_inv α g
    rw [hg'] at this
    calc MulAut.conj g * α = (α * MulAut.conj g * α⁻¹) * α := by rw [this]
      _ = α * MulAut.conj g := by group
  refine ⟨hle, (normal_subgroupOf_iff hle).2 ?_⟩
  rintro _ k ⟨g, hg, rfl⟩ hk
  refine ⟨k g, ?_, (mul_conj_mul_inv k g).symm⟩
  have hg' : α g = g := hg
  have hk' : k * α = α * k := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hk).2
  change α (k g) = k g
  rw [← MulAut.mul_apply, ← hk', MulAut.mul_apply, hg']

theorem isSubnormal_map_conj {A N : Subgroup T} (hAN : A ≤ N) (hNA : N ≤ normalizer (A : Set T))
    {H : Subgroup (MulAut T)} (hNH : N.map (MulAut.conj : T →* MulAut T) ≤ H)
    (hNn : ((N.map (MulAut.conj : T →* MulAut T)).subgroupOf H).Normal) :
    ((A.map (MulAut.conj : T →* MulAut T)).subgroupOf H).IsSubnormal := by
  have hle : A.map (MulAut.conj : T →* MulAut T) ≤ N.map (MulAut.conj : T →* MulAut T) :=
    map_mono hAN
  refine GroupTheory.isSubnormal_subgroupOf_trans hle hNH ?_ hNn.isSubnormal
  refine ((normal_subgroupOf_iff hle).2 ?_).isSubnormal
  rintro _ _ ⟨a, ha, rfl⟩ ⟨k, hk, rfl⟩
  exact ⟨k * a * k⁻¹, (mem_normalizer_iff.1 (hNA hk) a).1 ha, by
    rw [map_mul, map_mul, map_inv]⟩

theorem propAConclusionIn_of_burgTorusFor [Finite T] (hZ : center T = ⊥)
    {B : Subgroup (MulAut T)} (hB : (MulAut.conj : T →* MulAut T).range ≤ B)
    {α : MulAut T} (hα : orderOf α = 2) (h : BurgTorusFor α)
    {Y : Subgroup (MulAut T)} (hY : Y ≠ ⊥) (hYO : Y ≤ oddCoreIn B α) :
    PropAConclusionIn B α Y := by
  obtain ⟨Q, hQq, hQα, hQN, u, S, hu, hSq, hSu, hSN, ⟨p, n, hp, hp2, hn, ⟨eS⟩⟩, hZS, hαS,
    ⟨s₀, hs₀, hαs₀⟩, hβ⟩ := h
  set c : T →* MulAut T := MulAut.conj with hcdef
  have hci : Function.Injective c := conj_injective hZ
  let eQ : Q ≃* Q.map c := Q.equivMapOfInjective c hci
  let eS' : S ≃* S.map c := S.equivMapOfInjective c hci
  have hQq' : IsQuasisimple (Q.map c) := LocalCores.isQuasisimple_of_mulEquiv eQ hQq
  have hSq' : IsQuasisimple (S.map c) := LocalCores.isQuasisimple_of_mulEquiv eS' hSq
  have hQe : Even (Nat.card (Q.map c)) := even_card_of_isQuasisimple hQq'
  have hSe : Even (Nat.card (S.map c)) := even_card_of_isQuasisimple hSq'
  obtain ⟨hFH, hFn⟩ := normal_map_fixedSubgroup hB α
  have hQH : Q.map c ≤ B ⊓ centralizer ({α} : Set (MulAut T)) := (map_mono hQα).trans hFH
  have hQs : ((Q.map c).subgroupOf (B ⊓ centralizer ({α} : Set (MulAut T)))).IsSubnormal :=
    isSubnormal_map_conj hQα hQN hFH hFn
  obtain ⟨hCH, hCn⟩ := normal_map_centralizer hZ hB u
  have hSH : S.map c ≤ B ⊓ centralizer ({c u} : Set (MulAut T)) := (map_mono hSu).trans hCH
  have hSs : ((S.map c).subgroupOf (B ⊓ centralizer ({c u} : Set (MulAut T)))).IsSubnormal :=
    isSubnormal_map_conj hSu hSN hCH hCn
  have hSc : IsPComponent 2 ((S.map c).subgroupOf (B ⊓ centralizer ({c u} : Set (MulAut T)))) :=
    isPComponent_two_of_quasisimple hSH hSq' hSs hSe
  have hfixQ : ∀ β ∈ oddCoreIn B α, ∀ x ∈ Q, β x = x := by
    intro β hβO x hx
    exact apply_eq_of_commute_conj hZ
      (commute_of_mem_pPrimeCore hQH hQq' hQs hQe hβO ⟨x, hx, rfl⟩)
  refine propAConclusionIn_of_core hα hY hYO (hB ⟨u, rfl⟩)
    (by rw [orderOf_injective c hci u]; exact hu) (hSH.trans inf_le_left)
    (hSH.trans inf_le_right) hSc ⟨p, n, hp, hp2, hn, ⟨eS'.symm.trans eS⟩⟩ ?_
    (mem_normalizer_map_conj hαS) ⟨c s₀, ⟨s₀, hs₀, rfl⟩, ?_⟩ ?_ ?_
  · have hcomp : (S.map c).subtype.comp (eS' : S →* S.map c) = c.comp S.subtype := by
      ext x
      rfl
    rw [← map_center_eq eS', map_map, hcomp, ← map_map, hZS, MonoidHom.map_zpowers]
  · intro h
    apply hαs₀
    apply hci
    rw [← mul_conj_mul_inv, h, mul_inv_cancel_right]
  · intro β hβO
    have hcomm := commute_of_mem_oddCoreIn hβO
    exact mem_normalizer_map_conj (hβ β (odd_orderOf_of_mem_oddCoreIn hβO) hcomm.symm
      (hfixQ β hβO)).1
  · intro β hβO hSfix
    have hcomm := commute_of_mem_oddCoreIn hβO
    exact (hβ β (odd_orderOf_of_mem_oddCoreIn hβO) hcomm.symm (hfixQ β hβO)).2
      fun x hx => apply_eq_of_commute_conj hZ (hSfix _ ⟨x, hx, rfl⟩)

end CFSG.ComponentClassification.Burgoyne.E2
