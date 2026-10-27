module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.WielandtProductBasic
public import CFSG.GroupTheory.AutomorphismAction.MapEqOfMapsTo

public section

namespace CFSG

open Subgroup

open scoped Pointwise

section

variable {X : Type*} [Group X]

theorem exists_eq_quotient_mk'_pow {Φ : MulAut X} {H : Subgroup (MulAut X)} [H.Normal]
    (hΦ : ∀ α : MulAut X, ∃ y : X, ∃ j : ℕ, α = MulAut.conj y * Φ ^ j)
    (hN : (MulAut.conj : X →* MulAut X).range ≤ H) (x : MulAut X ⧸ H) :
    ∃ j : ℕ, x = QuotientGroup.mk' H Φ ^ j := by
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective H x
  obtain ⟨y, j, rfl⟩ := hΦ α
  have hy : QuotientGroup.mk' H (MulAut.conj y) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hN ⟨y, rfl⟩
  exact ⟨j, by rw [map_mul, map_pow, hy, one_mul]⟩

theorem normal_range_conj_sup_zpowers_pow {Φ : MulAut X}
    (hΦ : ∀ α : MulAut X, ∃ y : X, ∃ j : ℕ, α = MulAut.conj y * Φ ^ j) (m : ℕ) :
    ((MulAut.conj : X →* MulAut X).range ⊔ zpowers (Φ ^ m)).Normal := by
  let N : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range
  have hconj (ψ : MulAut X) (x : X) : ψ * MulAut.conj x * ψ⁻¹ = MulAut.conj (ψ x) := by
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    rw [show ψ (ψ⁻¹ y) = y from MulEquiv.apply_symm_apply ψ y]
  have hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨x, hx⟩ := hn
    rw [← hx]
    exact ⟨g x, (hconj g x).symm⟩
  have hcomm : IsMulCommutative (MulAut X ⧸ N) := by
    refine IsMulCommutative.of_comm ?_
    intro a b
    obtain ⟨i, rfl⟩ := exists_eq_quotient_mk'_pow hΦ (H := N) le_rfl a
    obtain ⟨j, rfl⟩ := exists_eq_quotient_mk'_pow hΦ (H := N) le_rfl b
    rw [← pow_add, ← pow_add, add_comm]
  have hcommutator : _root_.commutator (MulAut X) ≤ N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp hcomm
  exact Subgroup.Normal.of_commutator_le (MulAut X) (hcommutator.trans le_sup_left)

theorem index_dvd_of_le_range_conj_sup_zpowers {Φ : MulAut X} {H : Subgroup (MulAut X)} {m : ℕ}
    (hΦ : ∀ α : MulAut X, ∃ y : X, ∃ j : ℕ, α = MulAut.conj y * Φ ^ j)
    (hN : (MulAut.conj : X →* MulAut X).range ≤ H) (hH : H.Normal) (hm : Φ ^ m ∈ H) :
    H.index ∣ m := by
  have hgen : ∀ x : MulAut X ⧸ H, ∃ j : ℕ, x = QuotientGroup.mk' H Φ ^ j :=
    exists_eq_quotient_mk'_pow hΦ hN
  have hqHm : QuotientGroup.mk' H Φ ^ m = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hm
  have htop : Subgroup.zpowers (QuotientGroup.mk' H Φ) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨j, rfl⟩ := hgen x
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, by simp⟩
  have hcard : Nat.card (MulAut X ⧸ H) = orderOf (QuotientGroup.mk' H Φ) := by
    rw [← Nat.card_zpowers (a := QuotientGroup.mk' H Φ), htop, Subgroup.card_top]
  rw [Subgroup.index_eq_card, hcard]
  exact orderOf_dvd_of_pow_eq_one hqHm

theorem map_toMonoidHom_le_normalizer_of_conj_mem {S₀ S : Subgroup X} {γ : MulAut X}
    (h : ∀ s ∈ S, MulAut.conj (γ s) ∈ S₀.map (MulAut.conj : X →* MulAut X)) :
    S.map γ.toMonoidHom ≤ Subgroup.normalizer S₀ := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh k hk
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hh
  obtain ⟨s₀, hs₀, hs₀eq⟩ := Subgroup.mem_map.mp (h s hs)
  simp only [MulEquiv.coe_toMonoidHom]
  rw [show γ s * k * (γ s)⁻¹ = MulAut.conj (γ s) k from (MulAut.conj_apply _ _).symm,
    show MulAut.conj (γ s) k = MulAut.conj s₀ k from by rw [hs₀eq], MulAut.conj_apply]
  exact S₀.mul_mem (S₀.mul_mem hs₀ hk) (S₀.inv_mem hs₀)

theorem index_range_conj_sup_zpowers_pow_dvd {Φ : MulAut X}
    (hΦ : ∀ α : MulAut X, ∃ y : X, ∃ j : ℕ, α = MulAut.conj y * Φ ^ j) (m : ℕ) :
    ((MulAut.conj : X →* MulAut X).range ⊔ zpowers (Φ ^ m)).index ∣ m := by
  have hH : ((MulAut.conj : X →* MulAut X).range ⊔ zpowers (Φ ^ m)).Normal :=
    normal_range_conj_sup_zpowers_pow hΦ m
  exact index_dvd_of_le_range_conj_sup_zpowers hΦ le_sup_left hH
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers (Φ ^ m)))

end

variable {X : Type*} [Group X] [Finite X] {r : ℕ} [Fact r.Prime]

theorem relIndex_map_conj_range_dvd (H : Subgroup X) :
    (H.map (MulAut.conj : X →* MulAut X)).relIndex (MulAut.conj : X →* MulAut X).range ∣
      H.index := by
  let f : X →* MulAut X := MulAut.conj
  have hle : H.map f ≤ f.range := Subgroup.map_le_range f H
  have h1 := Subgroup.relIndex_mul_index hle
  have h2 := Subgroup.index_map (f := f) (H := H)
  have hpos : 0 < f.range.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hrel : (H.map f).relIndex f.range = (H ⊔ f.ker).index := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, h2]
  rw [hrel]
  exact Subgroup.index_dvd_of_le le_sup_left

theorem zpowers_le_normalizer_map_conj_of_mapsTo {S : Subgroup X} {φ : MulAut X}
    (hφS : ∀ s ∈ S, φ s ∈ S) :
    zpowers φ ≤ Subgroup.normalizer (S.map (MulAut.conj : X →* MulAut X)) := by
  have hconj (ψ : MulAut X) (x : X) : ψ * MulAut.conj x * ψ⁻¹ = MulAut.conj (ψ x) := by
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    rw [show ψ (ψ⁻¹ y) = y from MulEquiv.apply_symm_apply ψ y]
  have hmap : S.map φ.toMonoidHom = S := GroupTheory.map_eq_of_mapsTo φ hφS
  have hcomp : ((MulAut.conj φ).toMonoidHom).comp (MulAut.conj : X →* MulAut X) =
      (MulAut.conj : X →* MulAut X).comp φ.toMonoidHom := by
    ext x y
    exact congrArg (fun e : MulAut X => e y) (hconj φ x)
  have hmem : φ ∈ Subgroup.normalizer (S.map (MulAut.conj : X →* MulAut X)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc (S.map (MulAut.conj : X →* MulAut X)).map (MulAut.conj φ).toMonoidHom
        = S.map (((MulAut.conj φ).toMonoidHom).comp
            (MulAut.conj : X →* MulAut X)) := by rw [Subgroup.map_map]
      _ = S.map ((MulAut.conj : X →* MulAut X).comp φ.toMonoidHom) := by rw [hcomp]
      _ = (S.map φ.toMonoidHom).map (MulAut.conj : X →* MulAut X) := by rw [Subgroup.map_map]
      _ = S.map (MulAut.conj : X →* MulAut X) := by rw [hmap]
  exact Subgroup.zpowers_le.mpr hmem

theorem inf_range_conj_le_map_conj {S₀ : Subgroup X} {P : Subgroup (MulAut X)}
    (hInn : S₀.map (MulAut.conj : X →* MulAut X) ≤ P)
    (hP : IsPGroup r P) (hS₀i : ¬ r ∣ S₀.index) :
    P ⊓ (MulAut.conj : X →* MulAut X).range ≤ S₀.map (MulAut.conj : X →* MulAut X) := by
  let N : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range
  let Inn : Subgroup (MulAut X) := S₀.map (MulAut.conj : X →* MulAut X)
  have hInnP : Inn ≤ P ⊓ N := le_inf hInn (Subgroup.map_le_range _ S₀)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hP.to_le inf_le_left)
  have hrelN : Inn.relIndex N ∣ S₀.index := relIndex_map_conj_range_dvd S₀
  have hrelD : Inn.relIndex (P ⊓ N) ∣ Inn.relIndex N :=
    ⟨(P ⊓ N).relIndex N,
      (Subgroup.relIndex_mul_relIndex Inn (P ⊓ N) N hInnP inf_le_right).symm⟩
  have hdvdI : Inn.relIndex (P ⊓ N) ∣ S₀.index := hrelD.trans hrelN
  have hdvdC : Inn.relIndex (P ⊓ N) ∣ Nat.card ↥(P ⊓ N) :=
    Subgroup.relIndex_dvd_card Inn (P ⊓ N)
  have hcop : Nat.Coprime (Nat.card ↥(P ⊓ N)) S₀.index := by
    rw [hn]
    exact ((Fact.out : r.Prime).coprime_iff_not_dvd.mpr hS₀i).pow_left n
  have hone : Inn.relIndex (P ⊓ N) = 1 := by
    have hgcd : Inn.relIndex (P ⊓ N) ∣ Nat.gcd (Nat.card ↥(P ⊓ N)) S₀.index :=
      Nat.dvd_gcd hdvdC hdvdI
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hgcd
    exact Nat.dvd_one.mp hgcd
  exact Subgroup.relIndex_eq_one.mp hone

theorem exists_eq_map_conj_mul_pow_of_mem {S₀ : Subgroup X} {φ : MulAut X}
    (hφS : ∀ s ∈ S₀, φ s ∈ S₀) {x : MulAut X}
    (hx : x ∈ S₀.map (MulAut.conj : X →* MulAut X) ⊔ zpowers φ) :
    ∃ s₀ ∈ S₀, ∃ j : ℕ, x = MulAut.conj s₀ * φ ^ j := by
  have hcoe : (↑(S₀.map (MulAut.conj : X →* MulAut X) ⊔ zpowers φ) :
      Set (MulAut X)) = (S₀.map (MulAut.conj : X →* MulAut X)) * zpowers φ :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (zpowers_le_normalizer_map_conj_of_mapsTo hφS)
  change x ∈ (↑(S₀.map (MulAut.conj : X →* MulAut X) ⊔ zpowers φ) :
    Set (MulAut X)) at hx
  rw [hcoe, Set.mem_mul] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff b φ).mp
    (mem_powers_iff_mem_zpowers.mpr hb)
  exact ⟨s₀, hs₀, j, by rw [← hab, ← hj]⟩

theorem isPGroup_map_conj_sup_zpowers {S₀ : Subgroup X} (hS₀ : IsPGroup r S₀) {φ : MulAut X}
    (hφ : ∃ k : ℕ, φ ^ (r ^ k) = 1) (hφS : ∀ s ∈ S₀, φ s ∈ S₀) :
    IsPGroup r ↥(S₀.map (MulAut.conj : X →* MulAut X) ⊔ zpowers φ) := by
  obtain ⟨k, hk⟩ := hφ
  exact IsPGroup.to_sup_of_normal_left' (hS₀.map _)
    (GroupTheory.WielandtProduct.isPGroup_zpowers_of_pow_eq_one hk)
    (zpowers_le_normalizer_map_conj_of_mapsTo hφS)

theorem not_dvd_index_map_conj_sup_zpowers {S₀ : Subgroup X} (hS₀ : IsPGroup r S₀)
    (hS₀i : ¬ r ∣ S₀.index) {φ : MulAut X} (hφ : ∃ k : ℕ, φ ^ (r ^ k) = 1)
    (hφS : ∀ s ∈ S₀, φ s ∈ S₀)
    (hφi : ¬ r ∣ ((MulAut.conj : X →* MulAut X).range ⊔ zpowers φ).index) :
    ¬ r ∣ (S₀.map (MulAut.conj : X →* MulAut X) ⊔ zpowers φ).index := by
  have _ := isPGroup_map_conj_sup_zpowers hS₀ hφ hφS
  let N : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range
  let P : Subgroup (MulAut X) := S₀.map (MulAut.conj : X →* MulAut X) ⊔ zpowers φ
  have hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨x, hx⟩ := hn
    rw [← hx]
    refine ⟨g x, ?_⟩
    ext y
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
    rw [show g (g⁻¹ y) = y from MulEquiv.apply_symm_apply g y]
  have hPQ : P ≤ N ⊔ zpowers φ := by
    refine sup_le ?_ le_sup_right
    exact (Subgroup.map_le_range (MulAut.conj : X →* MulAut X) S₀).trans le_sup_left
  have hmul : P.index = P.relIndex (N ⊔ zpowers φ) * (N ⊔ zpowers φ).index :=
    (Subgroup.relIndex_mul_index hPQ).symm
  have hQeq : N ⊔ zpowers φ = N ⊔ P := by
    dsimp [P]
    rw [← sup_assoc, sup_eq_left.mpr (Subgroup.map_le_range _ S₀)]
  have hrel : P.relIndex (N ⊔ zpowers φ) = P.relIndex N := by
    rw [hQeq]
    exact CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal N P
  have hle : P.relIndex N ∣ (S₀.map (MulAut.conj : X →* MulAut X)).relIndex N :=
    Subgroup.relIndex_dvd_of_le_left N (le_sup_left : S₀.map _ ≤ P)
  have hdvd : P.relIndex N ∣ S₀.index :=
    hle.trans (relIndex_map_conj_range_dvd S₀)
  have hnot : ¬ r ∣ P.relIndex N := fun h => hS₀i (h.trans hdvd)
  intro hdvdP
  rw [hmul, hrel] at hdvdP
  exact (Fact.out : r.Prime).dvd_mul.mp hdvdP |>.elim hnot hφi

theorem exists_conj_mem_map_conj_sup_zpowers {S₀ : Subgroup X} (hS₀ : IsPGroup r S₀)
    (hS₀i : ¬ r ∣ S₀.index) {φ : MulAut X} (hφ : ∃ k : ℕ, φ ^ (r ^ k) = 1)
    (hφS : ∀ s ∈ S₀, φ s ∈ S₀)
    (hφi : ¬ r ∣ ((MulAut.conj : X →* MulAut X).range ⊔ zpowers φ).index)
    {S : Subgroup X} (hS : IsPGroup r S)
    {Θ : Subgroup (MulAut X)} (hΘ : IsPGroup r Θ) (hΘS : ∀ α ∈ Θ, ∀ s ∈ S, α s ∈ S) :
    ∃ γ : MulAut X, ∀ ρ ∈ S.map (MulAut.conj : X →* MulAut X) ⊔ Θ,
      γ * ρ * γ⁻¹ ∈ S₀.map (MulAut.conj : X →* MulAut X) ⊔ zpowers φ := by
  classical
  let P : Subgroup (MulAut X) := S₀.map (MulAut.conj : X →* MulAut X) ⊔ zpowers φ
  have hconj (ψ : MulAut X) (x : X) : ψ * MulAut.conj x * ψ⁻¹ = MulAut.conj (ψ x) := by
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    rw [show ψ (ψ⁻¹ y) = y from MulEquiv.apply_symm_apply ψ y]
  have hP1 : IsPGroup r P := isPGroup_map_conj_sup_zpowers hS₀ hφ hφS
  have hP2 : ¬ r ∣ P.index := not_dvd_index_map_conj_sup_zpowers hS₀ hS₀i hφ hφS hφi
  let P' : Sylow r (MulAut X) := hP1.toSylow hP2
  have hP'coe : (P' : Subgroup (MulAut X)) = P := IsPGroup.toSylow_coe hP1 hP2
  have hR : IsPGroup r ↥(S.map (MulAut.conj : X →* MulAut X) ⊔ Θ) := by
    refine IsPGroup.to_sup_of_normal_left'
      (hS.map (MulAut.conj : X →* MulAut X)) hΘ ?_
    rw [Subgroup.le_normalizer_iff]
    intro α hα k hk
    obtain ⟨s, hs, hk⟩ := Subgroup.mem_map.mp hk
    rw [← hk, hconj α s]
    exact Subgroup.mem_map_of_mem _ (hΘS α hα s hs)
  obtain ⟨T, hRT⟩ := hR.exists_le_sylow
  obtain ⟨γ, hγT⟩ := MulAction.exists_smul_eq (MulAut X) T P'
  refine ⟨γ, ?_⟩
  intro ρ hρ
  have hρT : ρ ∈ (T : Subgroup (MulAut X)) := hRT hρ
  have hmem := Subgroup.smul_mem_pointwise_smul ρ (MulAut.conj γ) (T : Subgroup _) hρT
  have hcoe : (MulAut.conj γ) • (T : Subgroup (MulAut X)) = P := by
    rw [← Sylow.coe_subgroup_smul, hγT, hP'coe]
  rw [hcoe] at hmem
  simpa only [MulAut.smul_def, MulAut.conj_apply] using hmem

theorem exists_mulAut_map_eq_and_conj_mem {S₀ : Subgroup X} (hS₀ : IsPGroup r S₀)
    (hS₀i : ¬ r ∣ S₀.index) {φ : MulAut X} (hφ : ∃ k : ℕ, φ ^ (r ^ k) = 1)
    (hφS : ∀ s ∈ S₀, φ s ∈ S₀)
    (hφi : ¬ r ∣ ((MulAut.conj : X →* MulAut X).range ⊔ zpowers φ).index)
    {S : Subgroup X} (hS : IsPGroup r S) (hSi : ¬ r ∣ S.index)
    {Θ : Subgroup (MulAut X)} (hΘ : IsPGroup r Θ) (hΘS : ∀ α ∈ Θ, ∀ s ∈ S, α s ∈ S) :
    ∃ β : MulAut X, S.map β.toMonoidHom = S₀ ∧
      ∀ α ∈ Θ, ∃ s₀ ∈ S₀, ∃ j : ℕ, β * α * β⁻¹ = MulAut.conj s₀ * φ ^ j := by
  obtain ⟨γ, hγ⟩ :=
    exists_conj_mem_map_conj_sup_zpowers hS₀ hS₀i hφ hφS hφi hS hΘ hΘS
  let P : Subgroup (MulAut X) := S₀.map (MulAut.conj : X →* MulAut X) ⊔ zpowers φ
  have hP1 : IsPGroup r P := isPGroup_map_conj_sup_zpowers hS₀ hφ hφS
  have hγR : ∀ ρ ∈ S.map (MulAut.conj : X →* MulAut X) ⊔ Θ, γ * ρ * γ⁻¹ ∈ P := hγ
  have hD : P ⊓ (MulAut.conj : X →* MulAut X).range ≤
      S₀.map (MulAut.conj : X →* MulAut X) :=
    inf_range_conj_le_map_conj (P := P) le_sup_left hP1 hS₀i
  have hmemD : ∀ s ∈ S, MulAut.conj (γ s) ∈ P ⊓ (MulAut.conj : X →* MulAut X).range := by
    intro s hs
    have hρ : MulAut.conj s ∈ S.map (MulAut.conj : X →* MulAut X) ⊔ Θ :=
      Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hs)
    have hconj : γ * MulAut.conj s * γ⁻¹ = MulAut.conj (γ s) := by
      ext y
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
      rw [show γ (γ⁻¹ y) = y from MulEquiv.apply_symm_apply γ y]
    refine ⟨?_, ⟨γ s, rfl⟩⟩
    have := hγR (MulAut.conj s) hρ
    rwa [hconj] at this
  have hnorm : S.map γ.toMonoidHom ≤ Subgroup.normalizer S₀ :=
    map_toMonoidHom_le_normalizer_of_conj_mem fun s hs => hD (hmemD s hs)
  have hsup : S.map γ.toMonoidHom ⊔ S₀ = S₀ := by
    have hgroup : IsPGroup r ↥(S.map γ.toMonoidHom ⊔ S₀) :=
      IsPGroup.to_sup_of_normal_right' (hS.map _) hS₀ hnorm
    have hSylow : CFSG.ABGLocalTools.IsSylowOf r S₀ ⊤ :=
      CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, hS₀, by simpa using hS₀i⟩
    exact hSylow.eq_of_le le_sup_right le_top hgroup
  have hcardS : Nat.card S = Nat.card S₀ := by
    have h1 : Nat.card S = r ^ (Nat.card X).factorization r := by
      simpa using Sylow.card_eq_multiplicity (hS.toSylow hSi)
    have h2 : Nat.card S₀ = r ^ (Nat.card X).factorization r := by
      simpa using Sylow.card_eq_multiplicity (hS₀.toSylow hS₀i)
    rw [h1, h2]
  have hmapγ : S.map γ.toMonoidHom = S₀ := by
    refine Subgroup.eq_of_le_of_card_ge (K := S₀) ?_ ?_
    · rw [← hsup]
      exact le_sup_left
    rw [Subgroup.card_map_of_injective γ.injective, ← hcardS]
  refine ⟨γ, hmapγ, fun α hα => ?_⟩
  obtain ⟨s₀, hs₀, j, hβ⟩ := exists_eq_map_conj_mul_pow_of_mem hφS
    (hγR α (Subgroup.mem_sup_right hα))
  exact ⟨s₀, hs₀, j, hβ⟩

theorem apply_eq_self_of_pow_eq_one {S₀ : Subgroup X} (hS₀ : IsPGroup r S₀)
    (hS₀i : ¬ r ∣ S₀.index) (hS₀c : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a) {φ : MulAut X}
    (hφ : ∃ k : ℕ, φ ^ (r ^ k) = 1) (hφS : ∀ s ∈ S₀, φ s ∈ S₀)
    (hφi : ¬ r ∣ ((MulAut.conj : X →* MulAut X).range ⊔ zpowers φ).index) {m : ℕ}
    (hφm : ∀ s ∈ S₀, s ^ m = 1 → φ s = s) {S : Subgroup X} (hS : IsPGroup r S)
    (hSi : ¬ r ∣ S.index) {α : MulAut X} (hα : ∃ k : ℕ, α ^ (r ^ k) = 1)
    (hαS : ∀ s ∈ S, α s ∈ S) : ∀ s ∈ S, s ^ m = 1 → α s = s := by
  have hΘ : IsPGroup r ↥(zpowers α) := by
    obtain ⟨k, hk⟩ := hα
    exact GroupTheory.WielandtProduct.isPGroup_zpowers_of_pow_eq_one hk
  have hpow : ∀ j : ℕ, ∀ s ∈ S, (α ^ j) s ∈ S := by
    intro j
    induction j with
    | zero => intro s hs; simpa using hs
    | succ j ih =>
        intro s hs
        rw [pow_succ, MulAut.mul_apply]
        exact ih (α s) (hαS s hs)
  have hΘS : ∀ β ∈ zpowers α, ∀ s ∈ S, β s ∈ S := by
    intro β hβ s hs
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff β α).mp
      (mem_powers_iff_mem_zpowers.mpr hβ)
    exact hpow j s hs
  obtain ⟨β, hβS, hβconj⟩ :=
    exists_mulAut_map_eq_and_conj_mem hS₀ hS₀i hφ hφS hφi hS hSi hΘ hΘS
  intro s hs hsm
  have hβs_mem : β s ∈ S₀ := by
    rw [← hβS]
    exact Subgroup.mem_map_of_mem _ hs
  have hβs_pow : (β s) ^ m = 1 := by
    rw [← map_pow β s m, hsm, map_one]
  have hβs_fix : φ (β s) = β s := hφm (β s) hβs_mem hβs_pow
  obtain ⟨s₀, hs₀, j, hβexp⟩ := hβconj α (Subgroup.mem_zpowers α)
  have hφpow : ∀ j : ℕ, (φ ^ j) (β s) = β s := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [pow_succ, MulAut.mul_apply, hβs_fix, ih]
  have hfix : MulAut.conj s₀ (β s) = β s := by
    rw [MulAut.conj_apply, hS₀c s₀ hs₀ (β s) hβs_mem, mul_assoc, mul_inv_cancel, mul_one]
  have hβα : β (α s) = β s := by
    have h := congrArg (fun e : MulAut X => e (β s)) hβexp
    simpa [MulAut.mul_apply, hφpow j, hfix] using h
  exact β.injective hβα

theorem exists_orderOf_eq_forall_commute_forall_apply_eq {S₀ : Subgroup X} (hS₀ : IsPGroup r S₀)
    (hS₀i : ¬ r ∣ S₀.index) {φ : MulAut X}
    (hφ : ∃ k : ℕ, φ ^ (r ^ k) = 1) (hφS : ∀ s ∈ S₀, φ s ∈ S₀)
    (hφi : ¬ r ∣ ((MulAut.conj : X →* MulAut X).range ⊔ zpowers φ).index) {x₀ : X}
    (hx₀ : ∀ s ∈ S₀, x₀ * s = s * x₀) (hφx₀ : φ x₀ = x₀) {S : Subgroup X} (hS : IsPGroup r S)
    (hSi : ¬ r ∣ S.index) {Θ : Subgroup (MulAut X)} (hΘ : IsPGroup r Θ)
    (hΘS : ∀ α ∈ Θ, ∀ s ∈ S, α s ∈ S) :
    ∃ x : X, orderOf x = orderOf x₀ ∧ (∀ s ∈ S, x * s = s * x) ∧ ∀ α ∈ Θ, α x = x := by
  obtain ⟨β, hβS, hβconj⟩ :=
    exists_mulAut_map_eq_and_conj_mem hS₀ hS₀i hφ hφS hφi hS hSi hΘ hΘS
  have hβs_mem : ∀ s ∈ S, β s ∈ S₀ := by
    intro s hs
    rw [← hβS]
    exact Subgroup.mem_map_of_mem _ hs
  have hφpowx : ∀ j : ℕ, (φ ^ j) x₀ = x₀ := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [pow_succ, MulAut.mul_apply, hφx₀, ih]
  refine ⟨β.symm x₀, MulEquiv.orderOf_eq β.symm x₀, ?_, ?_⟩
  · intro s hs
    apply β.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hx₀ (β s) (hβs_mem s hs)
  · intro α hα
    obtain ⟨s₀, hs₀, j, hβexp⟩ := hβconj α hα
    apply β.injective
    have hR : (MulAut.conj s₀ * φ ^ j) x₀ = x₀ := by
      rw [MulAut.mul_apply, hφpowx j, MulAut.conj_apply, ← hx₀ s₀ hs₀, mul_assoc,
        mul_inv_cancel, mul_one]
    have h := congrArg (fun e : MulAut X => e x₀) hβexp
    rw [hR] at h
    simpa using h


end CFSG

end
