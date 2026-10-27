module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P37Aut
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3Aux
public import CFSG.GH74.GLS.SP.Local.SPLCtW
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK

structure LiftData {X A : Type} [Group X] [Group A] (φ : X →* MulAut A) (T P : Subgroup X)
    (f z : X) : Prop where
  hT2 : IsPGroup 2 ↥T
  hPT : P ≤ T
  hPn : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P
  hPker : ∀ p ∈ P, φ p = 1 → p = 1
  hSyl : IsSylowOf 2 (P.map φ) (innAut A)
  hdih : ∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥P n
  hfT : f ∈ T
  hf2 : orderOf f = 2
  hfc : ∀ p ∈ P, f * p = p * f
  hfout : φ f ∉ innAut A
  hzP : z ∈ P
  hz2 : orderOf z = 2
  hzc : ∀ t ∈ T, t * z = z * t
  hzu : ∀ w ∈ P, (∀ p ∈ P, w * p = p * w) → w = 1 ∨ w = z

namespace LiftData

variable {X A : Type} [Group X] [Group A] {φ : X →* MulAut A}
  {T P : Subgroup X} {f z : X} (D : LiftData φ T P f z)

include D

theorem hff : f * f = 1 := by
  have := pow_orderOf_eq_one f
  rwa [D.hf2, sq] at this

theorem hzz : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [D.hz2, sq] at this

theorem hz1 : z ≠ 1 := fun h => by
  have := D.hz2
  rw [h, orderOf_one] at this
  omega

theorem isPGroup_map : IsPGroup 2 ↥(T.map φ) :=
  D.hT2.of_surjective (φ.subgroupMap T) (φ.subgroupMap_surjective T)

theorem ψ_injective : Function.Injective (φ.comp P.subtype) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  exact Subtype.ext (D.hPker a a.2 ha)

noncomputable def equivMap {H : Subgroup X} (hH : H ≤ P) : ↥H ≃* ↥(H.map φ) :=
  (Subgroup.subgroupOfEquivOfLe hH).symm.trans
    ((Subgroup.equivMapOfInjective (H.subgroupOf P) (φ.comp P.subtype) D.ψ_injective).trans
      (MulEquiv.subgroupCongr (by
        ext g
        simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
          Subgroup.subtype_apply]
        constructor
        · rintro ⟨⟨u, hu⟩, hu', rfl⟩
          exact ⟨u, hu', rfl⟩
        · rintro ⟨u, hu, rfl⟩
          exact ⟨⟨u, hH hu⟩, hu, rfl⟩)))

theorem card_map_of_le {H : Subgroup X} (hH : H ≤ P) : Nat.card ↥(H.map φ) = Nat.card ↥H :=
  (Nat.card_congr (D.equivMap hH).toEquiv).symm

theorem map_dihedralMax {P₀ : Subgroup X} (hP₀ : IsDihedralMaxIn P₀ P) :
    P₀.map φ ≤ P.map φ ∧ ((P₀.map φ).subgroupOf (P.map φ)).index = 2 ∧
      ∃ n : ℕ, IsDihedralTwoGroup ↥(P₀.map φ) n := by
  obtain ⟨hP₀P, hcard, hdihP₀⟩ := hP₀
  have hle : P₀.map φ ≤ P.map φ := Subgroup.map_mono hP₀P
  obtain ⟨n, hn3, hdn⟩ := D.hdih
  obtain ⟨k, hk, hk2, ⟨ρ⟩⟩ := hdn.2
  have hPcard : Nat.card ↥P = 2 ^ n := by
    rw [Nat.card_congr ρ.toEquiv, DihedralGroup.nat_card]
    exact hk.symm
  have hP₀card : Nat.card ↥P₀ = 2 ^ (n - 1) := by
    have : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  refine ⟨hle, ?_, ?_⟩
  · have h1 := Subgroup.relIndex_mul_card (H := P₀.map φ) (K := P.map φ)
    rw [inf_eq_left.2 hle, D.card_map_of_le hP₀P, D.card_map_of_le le_rfl, hcard] at h1
    have hpos : 0 < Nat.card ↥P₀ := by rw [hP₀card]; positivity
    have h2 : (P₀.map φ).relIndex (P.map φ) = 2 := by
      have : (P₀.map φ).relIndex (P.map φ) * Nat.card ↥P₀ = 2 * Nat.card ↥P₀ := h1
      exact Nat.eq_of_mul_eq_mul_right hpos this
    exact h2
  · refine ⟨n - 1, by omega, ?_⟩
    rw [← hP₀card]
    exact SP.Local.CtW.isDihedralOrder_of_mulEquiv (D.equivMap hP₀P) hdihP₀

section Fin

variable [Finite A]

theorem map_inf_inn : T.map φ ⊓ innAut A = P.map φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPB : P.map φ ≤ T.map φ ⊓ innAut A := le_inf (Subgroup.map_mono D.hPT) D.hSyl.le
  exact D.hSyl.eq_of_le hPB inf_le_right D.isPGroup_map.to_inf_left

end Fin

theorem hφz1 : φ z ≠ 1 := fun h => D.hz1 (D.hPker z D.hzP h)

theorem hφzz : φ z * φ z = 1 := by rw [← map_mul, D.hzz, map_one]

theorem hφz2 : orderOf (φ z) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact D.hφzz) D.hφz1

theorem hφf1 : φ f ≠ 1 := fun h => D.hfout (h ▸ (innAut A).one_mem)

theorem hφff : φ f * φ f = 1 := by rw [← map_mul, D.hff, map_one]

theorem hφf2 : orderOf (φ f) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact D.hφff) D.hφf1

theorem eq_of_map_eq {p q : X} (hp : p ∈ P) (hq : q ∈ P) (h : φ p = φ q) : p = q := by
  have h1 : p * q⁻¹ = 1 := D.hPker _ (P.mul_mem hp (P.inv_mem hq)) (by rw [map_mul, map_inv, h]; simp)
  exact mul_inv_eq_one.1 h1

section Fin2

variable [Finite A]

theorem apply_autLevelJ (hAJ : AutLevelJ A) {E : Subgroup X} (hET : E ≤ T)
    (hE : IsElementaryAbelian 2 ↥E) (hE8 : 8 ≤ Nat.card ↥(E.map φ)) :
    E.map φ ≤ P.map φ ⊔ zpowers (φ f) ∧
      ∀ P₀ : Subgroup (MulAut A), P₀ ≤ P.map φ → (P₀.subgroupOf (P.map φ)).index = 2 →
        (∃ n : ℕ, IsDihedralTwoGroup ↥P₀ n) →
        ∃ (R : Subgroup (MulAut A)) (σ₀ : MulAut A), IsCyclic ↥R ∧ σ₀ ∈ R ∧
          (φ f = σ₀ ∨ φ f = σ₀ * φ z) ∧
          (∀ τ ∈ T.map φ, τ ∈ normalizer (P₀ : Set (MulAut A)) ↔ τ * σ₀ = σ₀ * τ) ∧
          ∀ τ ∈ T.map φ, τ ∈ normalizer (P₀ : Set (MulAut A)) → ∃ q ∈ P.map φ, q⁻¹ * τ ∈ R := by
  have hBinn := D.map_inf_inn
  have hSylB : IsSylowOf 2 (T.map φ ⊓ innAut A) (innAut A) := by rw [hBinn]; exact D.hSyl
  have hÊ : IsElementaryAbelian 2 ↥(E.map φ) := by
    have := hE
    exact IsElementaryAbelian.map φ
  have hzB : φ z ∈ T.map φ ⊓ innAut A := by
    rw [hBinn]
    exact Subgroup.mem_map_of_mem φ D.hzP
  have hzc' : ∀ q ∈ T.map φ ⊓ innAut A, φ z * q = q * φ z := by
    intro q hq
    rw [hBinn] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [← map_mul, ← map_mul, ← D.hzc p (D.hPT hp)]
  have hzu' : ∀ w ∈ T.map φ ⊓ innAut A, (∀ q ∈ T.map φ ⊓ innAut A, w * q = q * w) →
      w = 1 ∨ w = φ z := by
    intro w hw hwc
    rw [hBinn] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    have hpc : ∀ p' ∈ P, p * p' = p' * p := by
      intro p' hp'
      have h1 := hwc (φ p') (by rw [hBinn]; exact Subgroup.mem_map_of_mem φ hp')
      have h2 : φ (p * p') = φ (p' * p) := by rw [map_mul, map_mul]; exact h1
      exact D.eq_of_map_eq (P.mul_mem hp hp') (P.mul_mem hp' hp) h2
    rcases D.hzu p hp hpc with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]
  have hσB : φ f ∈ T.map φ := Subgroup.mem_map_of_mem φ D.hfT
  have hσc : ∀ q ∈ T.map φ ⊓ innAut A, φ f * q = q * φ f := by
    intro q hq
    rw [hBinn] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [← map_mul, ← map_mul, D.hfc p hp]
  have key := hAJ (T.map φ) D.isPGroup_map hSylB (E.map φ) (Subgroup.map_mono hET) hÊ hE8 (φ z) hzB
    D.hφz2 hzc' hzu' (φ f) hσB D.hφf2 D.hfout hσc
  rw [hBinn] at key
  exact key

theorem J_le (hAJ : AutLevelJ A) {E : Subgroup X} (hET : E ≤ T) (hE : IsElementaryAbelian 2 ↥E)
    (hE8 : 8 ≤ Nat.card ↥(E.map φ)) : E ≤ (P ⊔ zpowers f) ⊔ (T ⊓ φ.ker) := by
  obtain ⟨hJ, -⟩ := D.apply_autLevelJ hAJ hET hE hE8
  rw [← MonoidHom.map_zpowers, ← Subgroup.map_sup] at hJ
  intro e he
  obtain ⟨u, hu, hue⟩ := hJ (Subgroup.mem_map_of_mem φ he)
  have huT : u ∈ T := sup_le D.hPT (zpowers_le.2 D.hfT) hu
  have hk : u⁻¹ * e ∈ T ⊓ φ.ker := ⟨T.mul_mem (T.inv_mem huT) (hET he),
    MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hue]; simp)⟩
  have : e = u * (u⁻¹ * e) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hk)

theorem normalizer_iff (hAJ : AutLevelJ A) {E₀ : Subgroup X} (hE₀T : E₀ ≤ T)
    (hE₀ : IsElementaryAbelian 2 ↥E₀) (hE₀8 : 8 ≤ Nat.card ↥(E₀.map φ))
    (hZ : ∀ k ∈ T ⊓ φ.ker, ∀ s ∈ T, k * s = s * k) {P₀ : Subgroup X}
    (hP₀ : IsDihedralMaxIn P₀ P) :
    ∀ t ∈ T, (∀ u ∈ P₀, t * u * t⁻¹ ∈ P₀) ↔ t * f = f * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut A) :=
    Finite.of_injective (fun σ : MulAut A => (σ : A → A)) (fun a b h => MulEquiv.ext (congrFun h))
  obtain ⟨-, hN⟩ := D.apply_autLevelJ hAJ hE₀T hE₀ hE₀8
  obtain ⟨hle, hidx, hdih⟩ := D.map_dihedralMax hP₀
  obtain ⟨R, σ₀, hRcyc, hσ₀R, hfσ, hnorm, hdec⟩ := hN (P₀.map φ) hle hidx hdih
  have hP₀P : P₀ ≤ P := hP₀.1
  have hzφ : ∀ g ∈ T, φ g * φ z = φ z * φ g := fun g hg => by
    rw [← map_mul, ← map_mul, D.hzc g hg]
  have hcommσ : ∀ g ∈ T, g * f = f * g → φ g * σ₀ = σ₀ * φ g := by
    intro g hg hc
    have h1 : φ g * φ f = φ f * φ g := by rw [← map_mul, ← map_mul, hc]
    rcases hfσ with h | h
    · rw [← h]
      exact h1
    · rw [h] at h1
      have h2 : φ g * σ₀ * φ z = σ₀ * φ g * φ z := by
        calc φ g * σ₀ * φ z = φ g * (σ₀ * φ z) := by group
          _ = σ₀ * φ z * φ g := h1
          _ = σ₀ * (φ z * φ g) := by group
          _ = σ₀ * (φ g * φ z) := by rw [hzφ g hg]
          _ = σ₀ * φ g * φ z := by group
      exact mul_right_cancel h2
  intro t ht
  constructor
  · intro hconj
    have hτn : φ t ∈ normalizer ((P₀.map φ : Subgroup (MulAut A)) : Set (MulAut A)) := by
      refine Thm1L3.mem_normalizer_of_conj_le fun w hw => ?_
      obtain ⟨u, hu, rfl⟩ := hw
      exact ⟨t * u * t⁻¹, hconj u hu, by rw [map_mul, map_mul, map_inv]⟩
    obtain ⟨q, hq, hqR⟩ := hdec (φ t) (Subgroup.mem_map_of_mem φ ht) hτn
    obtain ⟨p, hp, rfl⟩ := hq
    set s : X := p⁻¹ * t with hs
    have hsT : s ∈ T := T.mul_mem (T.inv_mem (D.hPT hp)) ht
    have hφs : φ s ∈ R := by
      rw [hs, map_mul, map_inv]
      exact hqR
    obtain ⟨f', hf'T, hf'P, hf'R, hf'f⟩ : ∃ f' : X, f' ∈ T ∧ (∀ p ∈ P, f' * p = p * f') ∧
        φ f' = σ₀ ∧ ∀ g ∈ T, g * f' = f' * g → g * f = f * g := by
      rcases hfσ with h | h
      · exact ⟨f, D.hfT, D.hfc, h, fun g _ hg => hg⟩
      · refine ⟨f * z, T.mul_mem D.hfT (D.hPT D.hzP), fun p hp => ?_, ?_, ?_⟩
        · have hzp : z * p = p * z := (D.hzc p (D.hPT hp)).symm
          calc f * z * p = f * (z * p) := by group
            _ = f * (p * z) := by rw [hzp]
            _ = f * p * z := by group
            _ = p * f * z := by rw [D.hfc p hp]
            _ = p * (f * z) := by group
        · rw [map_mul, h, mul_assoc, D.hφzz, mul_one]
        · intro g hg hgc
          have hgz : g * z = z * g := D.hzc g hg
          have h2 : g * f * z = f * g * z := by
            calc g * f * z = g * (f * z) := by group
              _ = f * z * g := hgc
              _ = f * (z * g) := by group
              _ = f * (g * z) := by rw [hgz]
              _ = f * g * z := by group
          exact mul_right_cancel h2
    let F : Subgroup X := T ⊓ R.comap φ
    have hsF : s ∈ F := ⟨hsT, hφs⟩
    have hf'F : f' ∈ F := ⟨hf'T, show φ f' ∈ R by rw [hf'R]; exact hσ₀R⟩
    have : IsCyclic ↥R := hRcyc
    let ψ' : ↥F →* ↥R := (φ.comp F.subtype).codRestrict R (fun a => a.2.2)
    have hker : ψ'.ker ≤ Subgroup.center ↥F := by
      intro a ha
      rw [Subgroup.mem_center_iff]
      intro g
      have ha1 : φ (a : X) = 1 := congrArg Subtype.val ha
      have haT : (a : X) ∈ T ⊓ φ.ker := ⟨a.2.1, ha1⟩
      exact Subtype.ext ((hZ _ haT _ g.2.1).symm)
    have hcomm := (ψ'.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm
      (⟨s, hsF⟩ : ↥F) ⟨f', hf'F⟩
    have hsf' : s * f' = f' * s := congrArg Subtype.val hcomm
    have htf' : t * f' = f' * t := by
      have ht' : t = p * s := by rw [hs]; group
      calc t * f' = p * (s * f') := by rw [ht']; group
        _ = p * (f' * s) := by rw [hsf']
        _ = (p * f') * s := by group
        _ = (f' * p) * s := by rw [(hf'P p hp).symm]
        _ = f' * (p * s) := by group
        _ = f' * t := by rw [← ht']
    exact hf'f t ht htf'
  · intro hc u hu
    have hτ := (hnorm (φ t) (Subgroup.mem_map_of_mem φ ht)).2 (hcommσ t ht hc)
    have hφu : φ u ∈ P₀.map φ := Subgroup.mem_map_of_mem φ hu
    have h1 := (Subgroup.mem_normalizer_iff.1 hτ (φ u)).1 hφu
    obtain ⟨u', hu', hu'e⟩ := h1
    have hconjP : t * u * t⁻¹ ∈ P := D.hPn t ht u (hP₀P hu)
    have : u' = t * u * t⁻¹ := D.eq_of_map_eq (hP₀P hu') hconjP (by rw [hu'e, map_mul, map_mul, map_inv])
    rw [← this]
    exact hu'

end Fin2

end LiftData

end CFSG.GH74.GLS.C3.Layer1.Thm1
