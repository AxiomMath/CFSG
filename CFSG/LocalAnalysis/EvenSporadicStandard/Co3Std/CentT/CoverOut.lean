module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.CenterQuot

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup

theorem exists_normal_of_cover {X : Type} [Group X] [Finite X] (L : Subgroup X) [L.Normal]
    (hL : commutator ↥L = ⊤)
    (hQ : Nat.card (MulAut (↥L ⧸ center ↥L)) ∣ 6 * Nat.card (↥L ⧸ center ↥L))
    (hc : center (↥L ⧸ center ↥L) = ⊥) :
    ∃ N : Subgroup X, N.Normal ∧ N.index ∣ 6 ∧
      ∀ g : X, g ∈ N ↔ ∃ k ∈ L, ∀ l ∈ L, g * l * g⁻¹ = k * l * k⁻¹ := by
  haveI : Nonempty (↥L ⧸ center ↥L) := ⟨1⟩
  let Inn : Subgroup (MulAut (↥L ⧸ center ↥L)) :=
    (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)).range
  let ψ : X →* MulAut (↥L ⧸ center ↥L) :=
    { toFun := fun g => centerQuotAut (MulAut.conjNormal (H := L) g)
      map_one' := by simp [centerQuotAut_one]
      map_mul' := fun g h => by simp [centerQuotAut_mul] }
  have hψ : ∀ g, ψ g = centerQuotAut (MulAut.conjNormal (H := L) g) := fun _ => rfl
  have hInnNormal : Inn.Normal := by
    refine ⟨fun a ha b => ?_⟩
    rcases ha with ⟨q, rfl⟩
    refine ⟨b q, ?_⟩
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply]
  haveI : Inn.Normal := hInnNormal
  have hcardInn : Nat.card Inn = Nat.card (↥L ⧸ center ↥L) := by
    have hinj : Function.Injective
        (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hmem : x ∈ center (↥L ⧸ center ↥L) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have h := congrArg (fun e : MulAut (↥L ⧸ center ↥L) => e y) hx
        simp only [MulAut.conj_apply, MulAut.one_apply] at h
        have hxy : x * y = y * x := by
          calc x * y = x * y * x⁻¹ * x := by group
            _ = y * x := by rw [h]
        exact hxy.symm
      rw [hc] at hmem
      simpa using hmem
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hindexInn : Inn.index ∣ 6 := by
    have h := Subgroup.card_mul_index Inn
    rw [hcardInn] at h
    rw [← h, Nat.mul_comm 6] at hQ
    exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hQ
  let N : Subgroup X := Inn.comap ψ
  have hNindex : N.index ∣ 6 := by
    change (Inn.comap ψ).index ∣ 6
    rw [Subgroup.index_comap Inn ψ]
    exact (Subgroup.relIndex_dvd_index_of_normal Inn ψ.range).trans hindexInn
  refine ⟨N, hInnNormal.comap ψ, hNindex, ?_⟩
  intro g
  constructor
  · intro hg
    have hg' : ψ g ∈ Inn := hg
    rcases hg' with ⟨q, hq⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (s := center ↥L) q
    refine ⟨(k : X), k.2, ?_⟩
    intro l hl
    have hconj : MulAut.conjNormal (H := L) g = MulAut.conj k := by
      apply centerQuotAut_injective (K := ↥L) hL
      rw [centerQuotAut_conj]
      rw [hk, hq]
      exact (hψ g).symm
    have hval := congrArg (fun e : MulAut ↥L => ((e ⟨l, hl⟩ : ↥L) : X)) hconj
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using hval
  · rintro ⟨k, hk, hkl⟩
    refine ⟨((⟨k, hk⟩ : ↥L) : ↥L ⧸ center ↥L), ?_⟩
    have hconj : MulAut.conjNormal (H := L) g = MulAut.conj ⟨k, hk⟩ := by
      ext l
      simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using hkl l l.2
    calc MulAut.conj (((⟨k, hk⟩ : ↥L) : ↥L ⧸ center ↥L))
        = centerQuotAut (MulAut.conj (⟨k, hk⟩ : ↥L)) :=
          (centerQuotAut_conj (K := ↥L) (⟨k, hk⟩ : ↥L)).symm
      _ = centerQuotAut (MulAut.conjNormal (H := L) g) := by rw [← hconj]
      _ = ψ g := (hψ g).symm

theorem dvd_card_centralizer_quotient {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (center K)) (k : K)
    (h : p ∣ Nat.card (centralizer ({k} : Set K))) :
    p ∣ Nat.card (centralizer ({(k : K ⧸ center K)} : Set (K ⧸ center K))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype ↥(centralizer ({k} : Set K)) := Fintype.ofFinite _
  have hdvd : p ∣ Fintype.card ↥(centralizer ({k} : Set K)) := by
    simpa only [Nat.card_eq_fintype_card] using h
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card p hdvd
  have hcomm : (c : K) * k = k * (c : K) :=
    Subgroup.mem_centralizer_singleton_iff.mp c.2
  let cbar : K ⧸ center K := ((c : K) : K ⧸ center K)
  have hcbar_comm : cbar * (k : K ⧸ center K) = (k : K ⧸ center K) * cbar := by
    change ((c : K) : K ⧸ center K) * ((k : K) : K ⧸ center K) =
      ((k : K) : K ⧸ center K) * ((c : K) : K ⧸ center K)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]
  have hcK_pow : (c : K) ^ p = 1 := by
    have h' := pow_orderOf_eq_one (c : K)
    rwa [Subgroup.orderOf_coe c, hc] at h'
  have hcbar_pow : cbar ^ p = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (orderOf_map_dvd (QuotientGroup.mk' (center K)) (c : K)).trans
      (by rw [Subgroup.orderOf_coe c, hc])
  have hcbar_ne : cbar ≠ 1 := by
    intro h1
    have hmem : (c : K) ∈ center K := (QuotientGroup.eq_one_iff (c : K)).mp h1
    have hdvd : p ∣ Nat.card (center K) := by
      have h' := Subgroup.orderOf_dvd_natCard (center K) hmem
      rwa [Subgroup.orderOf_coe c, hc] at h'
    exact hZ hdvd
  have hcbar_order : orderOf cbar = p := orderOf_eq_prime hcbar_pow hcbar_ne
  have hcbar_mem : cbar ∈ centralizer ({(k : K ⧸ center K)} : Set (K ⧸ center K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcbar_comm
  have h' := Subgroup.orderOf_dvd_natCard
    (centralizer ({(k : K ⧸ center K)} : Set (K ⧸ center K))) hcbar_mem
  rwa [hcbar_order] at h'

end CFSG.EvenSporadicStandard.Co3Std.CentT
