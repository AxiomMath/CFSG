module

public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
public import CFSG.GroupTheory.KleinFourAutomorphism

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open CFSG CFSG.OrderReductions.FrattiniAutomorphisms

theorem card_le_two_of_isPGroup_perm {X : Type} [Finite X] (hX : Nat.card X ≤ 3)
    (P : Subgroup (Equiv.Perm X)) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have hdvd : Nat.card P ∣ Nat.card (Equiv.Perm X) := Subgroup.card_subgroup_dvd_card P
  rw [Nat.card_perm] at hdvd
  have h6 : (Nat.card X).factorial ∣ 6 := by
    have := Nat.factorial_dvd_factorial hX
    simpa [Nat.factorial] using this
  have h2a : 2 ^ a ∣ 6 := ha ▸ hdvd.trans h6
  by_contra hlt
  push Not at hlt
  rw [ha] at hlt
  have ha2 : 2 ≤ a := by
    by_contra h
    push Not at h
    interval_cases a <;> simp at hlt
  have h4 : 4 ∣ 2 ^ a := by
    have : 2 ^ 2 ∣ 2 ^ a := pow_dvd_pow 2 ha2
    simpa using this
  have := h4.trans h2a
  omega

theorem index_le_two_of_frattini_quot_le_four {H : Type} [Group H] [Finite H] (T : Sylow 2 H)
    (Q : Subgroup H) (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q)
    (hQmax : ∀ N : Subgroup H, N.Normal → IsPGroup 2 N → N ≤ Q)
    (hC : Subgroup.centralizer (Q : Set H) ≤ Q) (hQT : Q ≤ (T : Subgroup H))
    (hV : Nat.card (↥Q ⧸ frattini ↥Q) ≤ 4) :
    (Q.subgroupOf (T : Subgroup H)).index ≤ 2 := by
  have := hQn
  let ρ : H →* MulAut (↥Q ⧸ frattini ↥Q) :=
    (quotientAutomorphism (frattini ↥Q)).comp MulAut.conjNormal
  let σ : H →* Equiv.Perm {v : ↥Q ⧸ frattini ↥Q // v ≠ 1} :=
    (nonidentityAutomorphismAction _).comp ρ
  have hker2 : IsPGroup 2 σ.ker := by
    rintro ⟨h, hh⟩
    have hρ : ρ h = 1 := by
      apply nonidentityAutomorphismAction_injective
      rw [map_one]
      exact MonoidHom.mem_ker.mp hh
    have hmem : (MulAut.conjNormal h : MulAut Q) ∈ (quotientAutomorphism (frattini ↥Q)).ker :=
      MonoidHom.mem_ker.mpr hρ
    obtain ⟨n, hn⟩ := frattini_automorphism_kernel_isPGroup 2 hQ2 ⟨MulAut.conjNormal h, hmem⟩
    have hn' : MulAut.conjNormal (h ^ 2 ^ n) = (1 : MulAut Q) := by
      rw [map_pow]
      exact congrArg Subtype.val hn
    have hcen : h ^ 2 ^ n ∈ Subgroup.centralizer (Q : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 := congrArg (fun f : MulAut Q => ((f ⟨q, hq⟩ : Q) : H)) hn'
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    obtain ⟨m, hm⟩ := hQ2 ⟨h ^ 2 ^ n, hC hcen⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    have hm' : (h ^ 2 ^ n) ^ 2 ^ m = 1 := congrArg Subtype.val hm
    rw [← pow_mul, ← pow_add] at hm'
    simpa using hm'
  have hKQ : σ.ker ≤ Q := hQmax σ.ker inferInstance hker2
  let φ : (T : Subgroup H) →* Equiv.Perm {v : ↥Q ⧸ frattini ↥Q // v ≠ 1} :=
    σ.comp (T : Subgroup H).subtype
  have hφ2 : IsPGroup 2 φ.range :=
    T.isPGroup'.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hXcard : Nat.card {v : ↥Q ⧸ frattini ↥Q // v ≠ 1} ≤ 3 := by
    classical
    let : Fintype (↥Q ⧸ frattini ↥Q) := Fintype.ofFinite _
    have h1 : Fintype.card {x : ↥Q ⧸ frattini ↥Q // x = 1} = 1 := by simp
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x : ↥Q ⧸ frattini ↥Q => x = 1),
      h1]
    rw [Nat.card_eq_fintype_card] at hV
    omega
  have hrange : Nat.card φ.range ≤ 2 := card_le_two_of_isPGroup_perm hXcard _ hφ2
  have hmul := Subgroup.relIndex_mul_relIndex σ.ker Q (T : Subgroup H) hKQ hQT
  have hker : σ.ker.relIndex (T : Subgroup H) = Nat.card φ.range := by
    rw [← Subgroup.index_ker]
    rfl
  have hdvd : Q.relIndex (T : Subgroup H) ∣ Nat.card φ.range := by
    rw [← hker]
    exact Dvd.intro_left _ hmul
  exact (Nat.le_of_dvd Nat.card_pos hdvd).trans hrange

end CFSG.GH74.Uniqueness.SU.K.R4
