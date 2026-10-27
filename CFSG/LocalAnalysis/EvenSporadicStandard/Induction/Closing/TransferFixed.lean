module

public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.TransferFix

public section

namespace CFSG.EvenSporadicStandard.Induction.Closing

open Subgroup MulAction CFSG.RankThree.Transfer CFSG.EvenSporadicStandard.McLStd

variable {G : Type} [Group G] [Finite G] {t : G} {K : Subgroup G}

theorem prod_fixed_cosets_eq_one_of_mem {N : Subgroup G} [N.Normal] [IsSimpleGroup ↥N]
    (hnonab : ∃ a b : ↥N, a * b ≠ b * a) (htN : t ∈ N) (ht : t * t = 1) {A : Type*}
    [CommGroup A] (ψ : K →* A) [Fintype (G ⧸ K)] [DecidableEq (G ⧸ K)] :
    ∏ X : G ⧸ K, (if t • X = X then cosetValue ψ t X else 1) = 1 := by
  have h1 : ψ.transfer t = 1 := by
    have h0 : ψ.transfer.comp N.subtype = 1 := hom_eq_one_of_simple hnonab _
    have := DFunLike.congr_fun h0 ⟨t, htN⟩
    simpa using this
  have h2 : ψ.transfer t = ∏ X : G ⧸ K, (if t • X = X then cosetValue ψ t X else 1) := by
    refine transfer_eq_prod_fixed_of_orderOf_lt ψ t ?_
    intro h hlt
    have h2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ht)
    have h3 : orderOf (h : G) = 1 := by
      have := orderOf_pos (h : G)
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    have h4 : (h : G) = 1 := orderOf_eq_one_iff.1 h3
    have h5 : h = 1 := Subtype.ext h4
    rw [h5, map_one]
  rw [← h2]
  exact h1


theorem prod_fixedPoints_eq_one_of_mem {N : Subgroup G} [N.Normal] [IsSimpleGroup ↥N]
    (hnonab : ∃ a b : ↥N, a * b ≠ b * a) (htN : t ∈ N) (ht : t * t = 1) {P : Subgroup G}
    (hP : IsPGroup 2 P) (htP : t ∈ P) (hPt : ∀ p ∈ P, p * t = t * p) {A : Type*} [CommGroup A]
    [Finite A] (ψ : K →* A) [Fintype (fixedPoints P (G ⧸ K))] :
    ∏ X : fixedPoints P (G ⧸ K), cosetValue ψ t X = 1 := by
  classical
  have : Fintype (G ⧸ K) := Fintype.ofFinite _
  have : Fintype A := Fintype.ofFinite _
  have : DecidableEq (G ⧸ K) := Classical.decEq _
  have hF := prod_eq_prod_fixedPoints (P := P) (α := G ⧸ K) hP
    (fun X => if t • X = X then cosetValue ψ t X else 1) (fixedIf_smul ψ hPt) (by
      intro X
      split_ifs with hX
      · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective X
        have hx : x⁻¹ * t * x ∈ K := smul_coe_eq_iff.1 hX
        rw [cosetValue_coe ψ hx, ← map_mul]
        have : (⟨x⁻¹ * t * x, hx⟩ : K) * ⟨x⁻¹ * t * x, hx⟩ = 1 := by
          apply Subtype.ext
          show (x⁻¹ * t * x) * (x⁻¹ * t * x) = 1
          calc (x⁻¹ * t * x) * (x⁻¹ * t * x) = x⁻¹ * (t * t) * x := by group
            _ = 1 := by rw [ht]; group
        rw [this, map_one]
      · exact one_mul 1)
  rw [prod_fixed_cosets_eq_one_of_mem hnonab htN ht ψ] at hF
  have hfix : ∀ X : fixedPoints P (G ⧸ K), t • (X : G ⧸ K) = X := fun X => X.2 ⟨t, htP⟩
  calc ∏ X : fixedPoints P (G ⧸ K), cosetValue ψ t X
      = ∏ X : fixedPoints P (G ⧸ K),
          (if t • (X : G ⧸ K) = X then cosetValue ψ t X else 1) :=
        Finset.prod_congr rfl fun X _ => by simp [hfix X]
    _ = 1 := hF.symm

theorem exists_conj_ne_centralizing_of_mem {N : Subgroup G} [N.Normal] [IsSimpleGroup ↥N]
    (hnonab : ∃ a b : ↥N, a * b ≠ b * a) (htN : t ∈ N) (ht : t * t = 1) {P : Subgroup G}
    (hP : IsPGroup 2 P) (htP : t ∈ P) (hPt : ∀ p ∈ P, p * t = t * p) {A : Type*} [CommGroup A]
    [Finite A] (ψ : centralizer ({t} : Set G) →* A)
    (hψ : ψ ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ ≠ 1) :
    ∃ g : G, g * t * g⁻¹ ≠ t ∧ ∀ p ∈ P, p * (g * t * g⁻¹) = (g * t * g⁻¹) * p := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype (fixedPoints P (G ⧸ centralizer ({t} : Set G))) := Fintype.ofFinite _
  have h1 := prod_fixedPoints_eq_one_of_mem (K := centralizer ({t} : Set G)) hnonab htN ht hP htP
    hPt ψ
  have hmemM : ∀ p ∈ P, p ∈ centralizer ({t} : Set G) := fun p hp =>
    mem_centralizer_singleton_iff.2 (hPt p hp)
  have hone : ((1 : G) : G ⧸ centralizer ({t} : Set G)) ∈
      fixedPoints P (G ⧸ centralizer ({t} : Set G)) := by
    rw [coe_mem_fixedPoints_iff]
    intro p hp
    simpa using hmemM p hp
  have hall : ∀ X : fixedPoints P (G ⧸ centralizer ({t} : Set G)), X = ⟨_, hone⟩ := by
    rintro ⟨X, hX⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective X
    rw [coe_mem_fixedPoints_iff] at hX
    have hxt : x * t * x⁻¹ = t := by
      by_contra hne
      obtain ⟨p, hp, hpne⟩ := hcon x hne
      apply hpne
      have h := mem_centralizer_singleton_iff.1 (hX p hp)
      calc p * (x * t * x⁻¹) = x * ((x⁻¹ * p * x) * t) * x⁻¹ := by group
        _ = x * (t * (x⁻¹ * p * x)) * x⁻¹ := by rw [h]
        _ = (x * t * x⁻¹) * p := by group
    have hxM : x ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc x * t = (x * t * x⁻¹) * x := by group
        _ = t * x := by rw [hxt]
    apply Subtype.ext
    show (x : G ⧸ centralizer ({t} : Set G)) = ((1 : G) : G ⧸ centralizer ({t} : Set G))
    rw [QuotientGroup.eq]
    simpa using inv_mem hxM
  rw [Fintype.prod_eq_single (⟨_, hone⟩ : fixedPoints P (G ⧸ centralizer ({t} : Set G)))
    (fun X hX => absurd (hall X) hX)] at h1
  have ht1 : (1 : G)⁻¹ * t * 1 ∈ centralizer ({t} : Set G) := by simpa using hmemM t htP
  have h2 := cosetValue_coe ψ ht1
  apply hψ
  rw [← h1]
  show ψ ⟨t, _⟩ = cosetValue ψ t (((1 : G) : G ⧸ centralizer ({t} : Set G)))
  rw [h2]
  congr 1
  exact Subtype.ext (by simp)

end CFSG.EvenSporadicStandard.Induction.Closing
