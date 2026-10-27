module

public import CFSG.LieType.SeitzGeneration.HyperEx
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.LieType.SeitzGeneration CFSG.Open

section Hyper

variable {G : Type*} [Group G] {p : ℕ}

theorem mem_hyperClosure_of_dvd_card (hp : p.Prime) {E : Subgroup G} (hEcard : Nat.card E = p ^ 3)
    {k : G} (hk : p ^ 2 ∣ Nat.card ↥(E ⊓ Subgroup.centralizer {k})) :
    k ∈ hyperClosure p (⊤ : Subgroup G) E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero 3 hp.ne_zero)
  have : Finite ↥(E ⊓ Subgroup.centralizer {k}) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : E ⊓ Subgroup.centralizer {k} ≤ E))
      (Subgroup.inclusion_injective _)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hk
  let F : Subgroup G := K.map (E ⊓ Subgroup.centralizer {k}).subtype
  have hFD : F ≤ E ⊓ Subgroup.centralizer {k} := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hFcard : Nat.card F = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
  refine Subgroup.subset_closure ⟨Subgroup.mem_top k, F, hFD.trans inf_le_left, ?_, ?_⟩
  · have h := Subgroup.relIndex_mul_card (H := F) (K := E)
    rw [inf_eq_left.2 (hFD.trans inf_le_left), hFcard, hEcard] at h
    have h2 : F.relIndex E * p ^ 2 = p * p ^ 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) h2
  · intro f hf
    exact ((hFD hf).2 k rfl).symm

theorem sq_dvd_card_inf_centralizer (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E)
    [Finite E] {k e y : G} (heE : e ∈ E) (hyE : y ∈ E) (he1 : e ≠ 1) (hek : e * k = k * e)
    (hyk : y * k = k * y) (hy : y ∉ Subgroup.zpowers e) :
    p ^ 2 ∣ Nat.card ↥(E ⊓ Subgroup.centralizer {k}) := by
  have : Fact p.Prime := ⟨hp⟩
  set D : Subgroup G := E ⊓ Subgroup.centralizer {k} with hD
  have : Finite D :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : D ≤ E)) (Subgroup.inclusion_injective _)
  have hDp : IsPGroup p D := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 x x.2.1)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hDp
  have heD : e ∈ D := ⟨heE, fun m hm => by
    rw [Set.mem_singleton_iff.1 hm]; exact hek.symm⟩
  have hZD : Subgroup.zpowers e ≤ D := (Subgroup.zpowers_le).2 heD
  have hord : orderOf e = p := orderOf_eq_prime (hE.2 e heE) he1
  have hZcard : Nat.card (Subgroup.zpowers e) = p := by rw [Nat.card_zpowers, hord]
  have hdvd : p ∣ p ^ n := by
    rw [← hn, ← hZcard]
    exact Subgroup.card_dvd_of_le hZD
  have hn1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst this
    exact hp.one_lt.ne' (Nat.dvd_one.1 (by simpa using hdvd))
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n = 1 := by omega
    subst this
    have hyD : y ∈ D := ⟨hyE, fun m hm => by
      rw [Set.mem_singleton_iff.1 hm]; exact hyk.symm⟩
    have hZeq : Subgroup.zpowers e = D :=
      Subgroup.eq_of_le_of_card_ge hZD (by rw [hn, hZcard]; simp)
    exact hy (hZeq ▸ hyD)
  rw [hn]
  exact pow_dvd_pow p hn2

end Hyper

section Lift

theorem commute_of_commute_map {L C : Type*} [Group L] [Group C] {p : ℕ}
    (ρ : L →* C) (hkc : ∀ z ∈ ρ.ker, ∀ l : L, z * l = l * z)
    (hkp : Nat.Coprime (Nat.card ρ.ker) p) {x : L} (hx : x ^ p = 1) {l : L}
    (h : ρ x * ρ l = ρ l * ρ x) : x * l = l * x := by
  set c : L := l * x * l⁻¹ * x⁻¹ with hc
  have hcker : c ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, map_inv, h.symm]
    group
  have hcx : l * x * l⁻¹ = c * x := by rw [hc]; group
  have hcomm : Commute c x := hkc c hcker x
  have hpow : (l * x * l⁻¹) ^ p = 1 := by
    rw [conj_pow, hx]
    simp
  rw [hcx, hcomm.mul_pow, hx, mul_one] at hpow
  have hord : orderOf (⟨c, hcker⟩ : ρ.ker) ∣ Nat.card ρ.ker := orderOf_dvd_natCard _
  have hord' : orderOf (⟨c, hcker⟩ : ρ.ker) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext hpow
  have h1 : orderOf (⟨c, hcker⟩ : ρ.ker) = 1 :=
    Nat.eq_one_of_dvd_one (hkp ▸ Nat.dvd_gcd hord hord')
  have hc1 : c = 1 := by
    have := orderOf_eq_one_iff.1 h1
    exact congrArg Subtype.val this
  rw [hc1, one_mul] at hcx
  exact (mul_inv_eq_iff_eq_mul.1 hcx).symm

end Lift

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
