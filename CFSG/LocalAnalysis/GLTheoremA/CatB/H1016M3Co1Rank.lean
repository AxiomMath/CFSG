module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3Co1Rho
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Three

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.Co1Sylow

open CFSG.Open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open scoped Matrix

private theorem comm_of_card_dvd {G : Type*} [Group G] (h : Nat.card G ∣ 3 ^ 2) (x y : G) :
    x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h
  interval_cases k
  · haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.1 (by rw [hk', pow_zero])).1
    exact Subsingleton.elim _ _
  · haveI := isCyclic_of_prime_card (α := G) (p := 3) (by rw [hk', pow_one])
    exact (IsCyclic.isMulCommutative (α := G)).is_comm.comm x y
  · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq hk').is_comm.comm x y

section Card


private theorem card_range : Nat.card rho.range = 27 := by
  have hd := Subgroup.card_range_dvd rho
  rw [Co1T.card_Qg] at hd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  have hk3 : k ≤ 3 := by
    have h := card_rho_range_le
    rw [hk, show (27 : ℕ) = 3 ^ 3 by norm_num] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  have hk3' : 3 ≤ k := by
    by_contra hlt
    exact rho_range_noncomm (comm_of_card_dvd (by rw [hk]; exact Nat.pow_dvd_pow 3 (by omega)))
  obtain rfl : k = 3 := by omega
  rw [hk]
  norm_num

private theorem ker_rho : rho.ker = (ElemThree.E.subgroupOf GA).subgroupOf Co1T.Qg := by
  haveI : Finite ↥GA := Co1T.finite_GA
  symm
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => MonoidHom.mem_ker.2 (rho_eq_one
    (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hx)))) ?_
  have h := Subgroup.card_ker_mul_card_range rho
  rw [card_range, Co1T.card_Qg] at h
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe EG_le_Qg).toEquiv, card_EG]
  norm_num at h ⊢
  omega

private theorem mem_E_of_rho_eq_one {x : ↥Co1T.Qg} (hx : rho x = 1) :
    ((x : ↥GA) : GL24) ∈ ElemThree.E := by
  have h : x ∈ rho.ker := MonoidHom.mem_ker.2 hx
  rw [ker_rho] at h
  exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 h)

private theorem card_ker_le {F : Subgroup ↥GA} (hFQ : F ≤ Co1T.Qg)
    (hcomm : ∀ y ∈ F, ∀ z ∈ F, y * z = z * y) {y : F}
    (hy : rho (Subgroup.inclusion hFQ y) ≠ 1) :
    Nat.card (rho.comp (Subgroup.inclusion hFQ)).ker ≤ 27 := by
  have hE : ∀ z : ↥(rho.comp (Subgroup.inclusion hFQ)).ker,
      (((z : F) : ↥GA) : GL24) ∈ ElemThree.E := by
    intro z
    have h := mem_E_of_rho_eq_one (x := Subgroup.inclusion hFQ z)
      ((MonoidHom.comp_apply _ _ _).symm.trans (MonoidHom.mem_ker.1 z.2))
    rwa [Subgroup.coe_inclusion] at h
  have hc : ∀ z : ↥(rho.comp (Subgroup.inclusion hFQ)).ker,
      (((Subgroup.inclusion hFQ y : ↥Co1T.Qg) : ↥GA) : GL24) * (((z : F) : ↥GA) : GL24) =
        (((z : F) : ↥GA) : GL24) * (((Subgroup.inclusion hFQ y : ↥Co1T.Qg) : ↥GA) : GL24) := by
    intro z
    have h := congrArg Subtype.val (hcomm _ y.2 _ (z : F).2)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    rw [Subgroup.coe_inclusion]
    exact h
  refine le_trans (Nat.card_le_card_of_injective (fun z =>
    (⟨_, rho_mulVec_eExp (hE z) (hc z)⟩ : {b : Fin 6 → ZMod 3 //
      ((rho (Subgroup.inclusion hFQ y) : (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ) :
        Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ b = b})) ?_) (card_fix_rho_le hy)
  intro z z' h
  have h' := congrArg (fun b : {b : Fin 6 → ZMod 3 //
      ((rho (Subgroup.inclusion hFQ y) : (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ) :
        Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ b = b} => eProd b.1) h
  simp only [eProd_eExp] at h'
  exact Subtype.ext (Subtype.ext (Subtype.ext h'))

private theorem card_range_comp_le {F : Subgroup ↥GA} (hFQ : F ≤ Co1T.Qg)
    (hcomm : ∀ y ∈ F, ∀ z ∈ F, y * z = z * y) :
    Nat.card (rho.comp (Subgroup.inclusion hFQ)).range ≤ 9 := by
  haveI : Finite ↥rho.range := Nat.finite_of_card_ne_zero (by rw [card_range]; norm_num)
  have hle : (rho.comp (Subgroup.inclusion hFQ)).range ≤ rho.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  have hd : Nat.card (rho.comp (Subgroup.inclusion hFQ)).range ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← card_range]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  have hk2 : k ≠ 3 := by
    rintro rfl
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hk, card_range]; norm_num)
    refine rho_range_noncomm fun u v => ?_
    obtain ⟨y, hy⟩ : (u : (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ) ∈
        (rho.comp (Subgroup.inclusion hFQ)).range := by
      rw [heq]
      exact u.2
    obtain ⟨z, hz⟩ : (v : (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ) ∈
        (rho.comp (Subgroup.inclusion hFQ)).range := by
      rw [heq]
      exact v.2
    have hyz : y * z = z * y := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hcomm _ y.2 _ z.2)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hy, ← hz, ← map_mul, ← map_mul, hyz]
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 9 := by norm_num

theorem card_le_or_eq_of_le_Qg {F : Subgroup ↥GA} (hFQ : F ≤ Co1T.Qg)
    (hF : IsElemAbelian 3 F) : Nat.card F ≤ 3 ^ 5 ∨ F = ElemThree.E.subgroupOf GA := by
  haveI : Finite ↥GA := Co1T.finite_GA
  haveI := hF.1
  have hcomm : ∀ y ∈ F, ∀ z ∈ F, y * z = z * y := fun y hy z hz => setLike_mul_comm hy hz
  by_cases h1 : ∀ y : F, rho (Subgroup.inclusion hFQ y) = 1
  · have hFE : F ≤ ElemThree.E.subgroupOf GA := by
      intro y hy
      have h := mem_E_of_rho_eq_one (h1 ⟨y, hy⟩)
      rw [Subgroup.coe_inclusion] at h
      exact Subgroup.mem_subgroupOf.2 h
    have hd := Subgroup.card_dvd_of_le hFE
    rw [card_EG] at hd
    obtain ⟨k, hk6, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    rcases Nat.lt_or_ge k 6 with hk5 | hk6'
    · left
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · right
      exact Subgroup.eq_of_le_of_card_ge hFE (le_of_eq (by rw [card_EG, hk, show k = 6 by omega]))
  · obtain ⟨y, hy⟩ := not_forall.1 h1
    left
    rw [← Subgroup.card_ker_mul_card_range (rho.comp (Subgroup.inclusion hFQ))]
    calc _ ≤ 27 * 9 := Nat.mul_le_mul (card_ker_le hFQ hcomm hy) (card_range_comp_le hFQ hcomm)
      _ = 3 ^ 5 := by norm_num

end Card

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.Co1Sylow
