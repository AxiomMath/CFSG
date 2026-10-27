module

public import CFSG.GH74.GLS.Stage2.Local.P34Sp4Cls
public import CFSG.GH74.GLS.Stage2.Local.P34Sp4OddN
public import CFSG.GH74.GLS.Stage2.Local.P34Bar

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatFactsSp4

@[expose] def OddAutFixTrivial : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
    ∀ β : MulAut (StatedProj (StatedSp 2 F)), Odd (orderOf β) → (∀ x ∈ E1 F, β x = x) →
      (∀ x ∈ E2 F, β x = x) → β = 1

theorem Sp4Setting.exists_model {X : Type} [Group X] [Finite X] {K : Subgroup X} {q : ℕ} {u : X}
    (hset : Sp4Setting K q u) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ 4 ≤ Nat.card F ∧
      ∃ ψ : ↥K ≃* StatedProj (StatedSp 2 F), ψ ⟨u, hset.mem⟩ = u1 F := by
  obtain ⟨F, iF, fF, hFq, ⟨e⟩⟩ := hset.psp4
  have hodd : Odd (Nat.card F) := hFq ▸ hset.odd
  have h4 : 4 ≤ Nat.card F := by
    have := hset.gt3
    omega
  obtain ⟨P', hP'le, hperf, hcard⟩ := hset.big
  have hP'K : P' ≤ K := hP'le.trans inf_le_left
  have hP'u : P' ≤ centralizer ({u} : Set X) := hP'le.trans inf_le_right
  let uK : ↥K := ⟨u, hset.mem⟩
  have huK : orderOf uK = 2 := by
    rw [← hset.inv]
    exact (Subgroup.orderOf_coe uK).symm
  have hPu : P'.subgroupOf K ≤ centralizer ({uK} : Set ↥K) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hpu : (p : X) * u = u * (p : X) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hP'u (Subgroup.mem_subgroupOf.1 hp))
    exact Subtype.ext hpu
  have hcardK : Nat.card F * (Nat.card F ^ 2 - 1) / 2 < Nat.card ↥(P'.subgroupOf K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'K).toEquiv, hFq]
    exact hcard
  obtain ⟨g, hg⟩ := exists_conj_u1_of_big hodd e huK hPu (perfect_subgroupOf hP'K hperf) hcardK
  refine ⟨F, iF, fF, hodd, h4, e.trans (MulAut.conj g⁻¹), ?_⟩
  change (MulAut.conj g⁻¹) (e uK) = u1 F
  rw [MulAut.conj_apply]
  simpa using hg

theorem sp4OddCore_of_aut (hM : OddAutFixTrivial) : Sp4OddCore := by
  intro X _ _ K q u hset
  classical
  have hKn : K.Normal := hset.normal
  obtain ⟨F, iF, fF, hodd, h4, ψ, hψ⟩ := hset.exists_model
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  set Y : Subgroup X := centralizer ({u} : Set X) with hYdef
  have hΘn : (pPrimeCore 2 ↥Y).Normal := pPrimeCore_normal
  set Θ' : Subgroup X := (pPrimeCore 2 ↥Y).map Y.subtype with hΘ'
  have hΘ'odd : ∀ k ∈ Θ', Odd (orderOf k) := by
    rintro _ ⟨t, ht, rfl⟩
    have := odd_orderOf_of_mem_pPrimeCore ht
    rwa [← Subgroup.orderOf_coe] at this
  have hΘ'Y : Θ' ≤ Y := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hΘ'conj : ∀ y ∈ Y, ∀ k ∈ Θ', y * k * y⁻¹ ∈ Θ' := by
    rintro y hy _ ⟨t, ht, rfl⟩
    exact ⟨⟨y, hy⟩ * t * ⟨y, hy⟩⁻¹, hΘn.conj_mem t ht ⟨y, hy⟩, by simp⟩
  have hψcent : ∀ k : ↥K, ψ k ∈ centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))) ↔
      (k : X) ∈ Y := by
    intro k
    rw [Subgroup.mem_centralizer_singleton_iff, hYdef, Subgroup.mem_centralizer_singleton_iff,
      ← hψ]
    constructor
    · intro h
      have h' : ψ (k * ⟨u, hset.mem⟩) = ψ (⟨u, hset.mem⟩ * k) := by
        rw [map_mul, map_mul]
        exact h
      exact congrArg Subtype.val (ψ.injective h')
    · intro h
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext h)
  set R : Subgroup (StatedProj (StatedSp 2 F)) := (Θ'.subgroupOf K).map ψ.toMonoidHom with hR
  have hRD : R ≤ centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))) := by
    rintro _ ⟨k, hk, rfl⟩
    exact (hψcent k).mpr (hΘ'Y (Subgroup.mem_subgroupOf.mp hk))
  have hnorm : ∀ d ∈ centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))), ∀ r ∈ R,
      d * r * d⁻¹ ∈ R := by
    intro d hd r hr
    obtain ⟨d₀, rfl⟩ := ψ.surjective d
    obtain ⟨k, hk, rfl⟩ := hr
    refine ⟨d₀ * k * d₀⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact hΘ'conj _ ((hψcent d₀).mp hd) _ (Subgroup.mem_subgroupOf.mp hk)
  have hodd' : ∀ r ∈ R, Odd (orderOf r) := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 := hΘ'odd _ (Subgroup.mem_subgroupOf.mp hk)
    rw [Subgroup.orderOf_coe] at h1
    change Odd (orderOf (ψ k))
    rwa [MulEquiv.orderOf_eq]
  have hRbot : R = ⊥ := oddNormal_u1_trivial hodd h4 hRD hnorm hodd'
  have hΘK : ∀ k : ↥K, (k : X) ∈ Θ' → k = 1 := by
    intro k hk
    have : ψ k ∈ R := ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    rw [hRbot, Subgroup.mem_bot] at this
    exact ψ.injective (this.trans (map_one ψ).symm)
  have hcomm : ∀ t ∈ pPrimeCore 2 ↥Y, ∀ d : ↥K, (d : X) ∈ Y →
      ((t : ↥Y) : X) * (d : X) = (d : X) * ((t : ↥Y) : X) := by
    intro t ht d hdY
    have htΘ' : ((t : ↥Y) : X) ∈ Θ' := ⟨t, ht, rfl⟩
    have hc1 : ((t : ↥Y) : X) * (d : X) * ((t : ↥Y) : X)⁻¹ * (d : X)⁻¹ ∈ K :=
      K.mul_mem (hKn.conj_mem (d : X) d.2 (t : X)) (K.inv_mem d.2)
    have hc2 : ((t : ↥Y) : X) * (d : X) * ((t : ↥Y) : X)⁻¹ * (d : X)⁻¹ ∈ Θ' := by
      have e : ((t : ↥Y) : X) * (d : X) * ((t : ↥Y) : X)⁻¹ * (d : X)⁻¹ =
          ((t : ↥Y) : X) * ((d : X) * ((t : ↥Y) : X)⁻¹ * (d : X)⁻¹) := by group
      rw [e]
      exact Θ'.mul_mem htΘ' (hΘ'conj _ hdY _ (Θ'.inv_mem htΘ'))
    have h1 := hΘK ⟨_, hc1⟩ hc2
    have h3 : ((t : ↥Y) : X) * (d : X) * ((t : ↥Y) : X)⁻¹ * (d : X)⁻¹ = 1 :=
      congrArg Subtype.val h1
    exact (commutatorElement_eq_one_iff_mul_comm).mp h3
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  set x : X := ((t : ↥Y) : X) with hx
  let β : MulAut (StatedProj (StatedSp 2 F)) :=
    MulAut.congr ψ (MulAut.conjNormal x : MulAut ↥K)
  have hβapp : ∀ p, β p = ψ (MulAut.conjNormal x (ψ.symm p)) := fun p => rfl
  have hfix : ∀ p ∈ centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))), β p = p := by
    intro p hp
    have hp' : ψ (ψ.symm p) ∈ centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))) := by
      rw [ψ.apply_symm_apply]
      exact hp
    have hd := hcomm t ht (ψ.symm p) ((hψcent _).mp hp')
    rw [hβapp]
    have : MulAut.conjNormal x (ψ.symm p) = ψ.symm p := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      rw [← hx] at hd
      calc x * (ψ.symm p : X) * x⁻¹ = (ψ.symm p : X) * x * x⁻¹ := by rw [hd]
        _ = (ψ.symm p : X) := by group
    rw [this, ψ.apply_symm_apply]
  have hodd'' : Odd (orderOf β) := by
    have h1 : Odd (orderOf x) := by
      have := odd_orderOf_of_mem_pPrimeCore ht
      rwa [← Subgroup.orderOf_coe] at this
    have h2' : orderOf (MulAut.conjNormal x : MulAut ↥K) ∣ orderOf x :=
      orderOf_map_dvd (MulAut.conjNormal : X →* MulAut ↥K) x
    have h3 : orderOf β = orderOf (MulAut.conjNormal x : MulAut ↥K) :=
      MulEquiv.orderOf_eq (MulAut.congr ψ) _
    rw [h3]
    exact Odd.of_dvd_nat h1 h2'
  have hβ1 : β = 1 := hM F hodd β hodd''
    (fun p hp => hfix p (((E1_le_X0 h2).trans X0_le_centralizer) hp))
    (fun p hp => hfix p (((E2_le_X0 h2).trans X0_le_centralizer) hp))
  have hc1 : MulAut.conjNormal x = (1 : MulAut ↥K) := by
    apply (MulAut.congr ψ).injective
    rw [map_one]
    exact hβ1
  have hxK : x ∈ K := by
    apply hset.cen
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : ↥K) : X)) hc1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc k * x = (x * k * x⁻¹) * x := by rw [this]
      _ = x * k := by group
  have hx1 : (⟨x, hxK⟩ : ↥K) = 1 := hΘK ⟨x, hxK⟩ ⟨t, ht, rfl⟩
  have hx1' : x = 1 := congrArg Subtype.val hx1
  exact Subtype.ext hx1'

end CFSG.GH74.GLS.Stage2.Local.P34
