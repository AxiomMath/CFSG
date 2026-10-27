module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

namespace S8

theorem exists_transvection {P : Type*} [Group P] [Finite P] {z u : P}
    (hzc : ∀ g : P, z * g = g * z) (hz1 : z ≠ 1) (hz2 : z * z = 1) (huz : u * u = z)
    (hcomm : ∀ g h : P, ⁅g, h⁆ = 1 ∨ ⁅g, h⁆ = z) :
    ∃ φ : P ≃* P, ∀ s, ¬ Commute s u → φ s = s * u := by
  classical
  have key : ∀ s : P, ¬ Commute s u → s * u = z * (u * s) := by
    intro s hs
    rcases hcomm s u with h | h
    · exact absurd ((commutatorElement_eq_one_iff_commute).1 h) hs
    · have h' : s * u * s⁻¹ * u⁻¹ = z := h
      calc s * u = (s * u * s⁻¹ * u⁻¹) * (u * s) := by group
        _ = z * (u * s) := by rw [h']
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have key' : ∀ t : P, ¬ Commute t u → u * t = z * (t * u) := by
    intro t ht
    have h := key t ht
    calc u * t = z⁻¹ * (z * (u * t)) := by group
      _ = z * (t * u) := by rw [← h, hzinv]
  let f : P → P := fun s => if Commute s u then s else s * u
  have hf : ∀ s t, f (s * t) = f s * f t := by
    intro s t
    by_cases hs : Commute s u <;> by_cases ht : Commute t u
    · have h : Commute (s * t) u := hs.mul_left ht
      simp only [f, if_pos hs, if_pos ht, if_pos h]
    · have hst : ¬ Commute (s * t) u := by
        intro h
        have h1 := key t ht
        have h2 : s * t * u = z * (u * (s * t)) := by
          calc s * t * u = s * (t * u) := by rw [mul_assoc]
            _ = s * (z * (u * t)) := by rw [h1]
            _ = z * (s * (u * t)) := by rw [← mul_assoc, ← hzc s, mul_assoc]
            _ = z * ((s * u) * t) := by rw [mul_assoc]
            _ = z * ((u * s) * t) := by rw [hs.eq]
            _ = z * (u * (s * t)) := by rw [mul_assoc]
        have h3 : s * t * u = u * (s * t) := h.eq
        rw [h3] at h2
        have : z = 1 := by
          have h4 : 1 * (u * (s * t)) = z * (u * (s * t)) := by rw [one_mul]; exact h2
          exact (mul_right_cancel h4).symm
        exact hz1 this
      simp only [f, if_pos hs, if_neg ht, if_neg hst, mul_assoc]
    · have hst : ¬ Commute (s * t) u := by
        intro h
        have h1 := key s hs
        have h2 : s * t * u = z * (u * (s * t)) := by
          calc s * t * u = s * (u * t) := by rw [mul_assoc, ht.eq]
            _ = (s * u) * t := by rw [mul_assoc]
            _ = (z * (u * s)) * t := by rw [h1]
            _ = z * (u * (s * t)) := by simp only [mul_assoc]
        have h3 : s * t * u = u * (s * t) := h.eq
        rw [h3] at h2
        have : z = 1 := by
          have h4 : 1 * (u * (s * t)) = z * (u * (s * t)) := by rw [one_mul]; exact h2
          exact (mul_right_cancel h4).symm
        exact hz1 this
      simp only [f, if_neg hs, if_pos ht, if_neg hst]
      calc s * t * u = s * (t * u) := by rw [mul_assoc]
        _ = s * (u * t) := by rw [ht.eq]
        _ = s * u * t := by rw [mul_assoc]
    · have hst : Commute (s * t) u := by
        have h1 := key s hs
        have h2 := key t ht
        show s * t * u = u * (s * t)
        calc s * t * u = s * (t * u) := by rw [mul_assoc]
          _ = s * (z * (u * t)) := by rw [h2]
          _ = z * (s * (u * t)) := by rw [← mul_assoc, ← hzc s, mul_assoc]
          _ = z * ((s * u) * t) := by rw [mul_assoc]
          _ = z * ((z * (u * s)) * t) := by rw [h1]
          _ = (z * z) * (u * (s * t)) := by simp only [mul_assoc]
          _ = u * (s * t) := by rw [hz2, one_mul]
      simp only [f, if_neg hs, if_neg ht, if_pos hst]
      have h1 : s * u * (t * u) = s * (u * t) * u := by simp only [mul_assoc]
      have h2 : s * (z * (t * u)) * u = z * (s * (t * (u * u))) := by
        calc s * (z * (t * u)) * u = (s * z) * (t * u) * u := by simp only [mul_assoc]
          _ = (z * s) * (t * u) * u := by rw [← hzc s]
          _ = z * (s * (t * (u * u))) := by simp only [mul_assoc]
      have h3 : z * (s * (t * (u * u))) = s * t := by
        rw [huz]
        calc z * (s * (t * z)) = z * (s * (z * t)) := by rw [hzc t]
          _ = z * ((s * z) * t) := by simp only [mul_assoc]
          _ = z * ((z * s) * t) := by rw [← hzc s]
          _ = (z * z) * (s * t) := by simp only [mul_assoc]
          _ = s * t := by rw [hz2, one_mul]
      rw [h1, key' t ht, h2, h3]
  let φ : P →* P := MonoidHom.mk' f hf
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    change f s = 1 at hs
    rw [Subgroup.mem_bot]
    by_cases hc : Commute s u
    · simpa only [f, if_pos hc] using hs
    · simp only [f, if_neg hc] at hs
      have h1 : s = u⁻¹ := eq_inv_of_mul_eq_one_left hs
      exact absurd (h1 ▸ (Commute.refl u).inv_left) hc
  refine ⟨MulEquiv.ofBijective φ (Finite.injective_iff_bijective.1 hinj), ?_⟩
  intro s hs
  show f s = s * u
  simp only [f, if_neg hs]

theorem extraspecial_char_abelian_cyclic {P : Type*} [Group P] [Finite P] (h2 : IsPGroup 2 P)
    (hcf : commutator P = frattini P) (hfz : frattini P = Subgroup.center P)
    (hcard : Nat.card (Subgroup.center P) = 2) (A : Subgroup P) [A.Characteristic]
    [IsMulCommutative A] : IsCyclic A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨zc, hzc1, hzcu⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center P)).1 hcard
  set z : P := (zc : P) with hz
  have hzcent : ∀ g, z * g = g * z := fun g => (Subgroup.mem_center_iff.1 zc.2 g).symm
  have hz1 : z ≠ 1 := fun h => hzc1 (Subtype.ext h)
  have hz2 : z * z = 1 := by
    have h := pow_card_eq_one' (G := Subgroup.center P) (x := zc)
    rw [hcard] at h
    have h' := congrArg Subtype.val h
    simpa [pow_two] using h'
  have hZmem : ∀ w ∈ Subgroup.center P, w = 1 ∨ w = z := by
    intro w hw
    by_cases h1 : (⟨w, hw⟩ : Subgroup.center P) = 1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (congrArg Subtype.val (hzcu _ h1))
  have hcomm : ∀ g h : P, ⁅g, h⁆ = 1 ∨ ⁅g, h⁆ = z := by
    intro g h
    have : ⁅g, h⁆ ∈ commutator P := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)
    rw [hcf, hfz] at this
    exact hZmem _ this
  have hnil : Group.IsNilpotent P := h2.isNilpotent
  have hsq : ∀ g : P, g * g ∈ Subgroup.center P := by
    intro g
    rw [← hfz]
    show g * g ∈ Order.radical (Subgroup P)
    rw [Order.radical, Subgroup.mem_iInf]
    intro M
    rw [Subgroup.mem_iInf]
    intro hM
    have hidx : M.index = 2 := (h2.isCoatom_iff_index_eq_prime).1 hM
    haveI : M.Normal := Subgroup.normal_of_index_eq_two hidx
    have := Subgroup.pow_index_mem M g
    rwa [hidx, pow_two] at this
  have hU : ∀ a ∈ A, ∀ u : P, u * u ≠ 1 → Commute a u := by
    intro a ha u hu
    by_contra hnc
    have huz : u * u = z := by
      rcases hZmem _ (hsq u) with h | h
      · exact absurd h hu
      · exact h
    obtain ⟨φ, hφ⟩ := exists_transvection hzcent hz1 hz2 huz hcomm
    have hφa : φ a = a * u := hφ a hnc
    have hfix := (inferInstance : A.Characteristic).fixed φ
    have hmem : φ a ∈ A := by
      have : a ∈ A.comap φ.toMonoidHom := by rw [hfix]; exact ha
      exact this
    rw [hφa] at hmem
    have hu' : u ∈ A := by
      have := A.mul_mem (A.inv_mem ha) hmem
      simpa using this
    exact hnc (by
      have := (IsMulCommutative.is_comm (M := A)).comm ⟨a, ha⟩ ⟨u, hu'⟩
      exact congrArg Subtype.val this)
  have hinv : ∀ a ∈ A, a * a = 1 → a ∈ Subgroup.center P := by
    intro a ha ha2
    by_contra hnz
    rw [Subgroup.mem_center_iff] at hnz
    push Not at hnz
    obtain ⟨s, hs⟩ := hnz
    have hsn : ¬ Commute a s := fun h => hs h.eq.symm
    have hss : s * s = 1 := by
      by_contra hne
      exact hsn (hU a ha s hne)
    have hsa : (s * a) * (s * a) = 1 := by
      by_contra hne
      have h1 := hU a ha (s * a) hne
      apply hsn
      have h2 : a * (s * a) = (s * a) * a := h1.eq
      have h3 : a * s * a = s * a * a := by simpa [mul_assoc] using h2
      exact mul_right_cancel h3
    apply hsn
    have h4 : s * a * s * a = 1 := by simpa [mul_assoc] using hsa
    have h5 : s * a = a * s := by
      calc s * a = s * a * (s * a) * (s * a)⁻¹ := by group
        _ = (s * a)⁻¹ := by rw [hsa, one_mul]
        _ = a⁻¹ * s⁻¹ := by rw [mul_inv_rev]
        _ = a * s := by
          rw [inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hss]
    exact h5.symm
  have hA2 : IsPGroup 2 A := h2.to_subgroup A
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  have hunique : ∀ l r : A, orderOf l = 2 → orderOf r = 2 → l = r := by
    have hz' : ∀ l : A, orderOf l = 2 → (l : P) = z := by
      intro l hl
      have hl2 : l ^ 2 = 1 := hl ▸ pow_orderOf_eq_one l
      have hl2' : (l : P) * l = 1 := by
        have := congrArg Subtype.val hl2
        simpa [pow_two] using this
      have hl1 : (l : P) ≠ 1 := by
        intro h
        have : l = 1 := Subtype.ext h
        rw [this, orderOf_one] at hl
        omega
      rcases hZmem _ (hinv l l.2 hl2') with h | h
      · exact absurd h hl1
      · exact h
    intro l r hl hr
    exact Subtype.ext ((hz' l hl).trans (hz' r hr).symm)
  letI : CommGroup A := { (inferInstance : Group A) with
    mul_comm := fun a b => (IsMulCommutative.is_comm (M := A)).comm a b }
  exact CFSG.TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
    k A hA2 hk hunique

theorem extraspec_symplectic {G : Type} [Group G] [Finite G] {S : Subgroup G} (hS : IsExtraSpec2 S) :
    GLASymplecticType S := by
  obtain ⟨h2, hcf, hfz, hcard⟩ := hS
  refine ⟨h2, ?_⟩
  intro A hAchar hAcomm
  haveI := hAchar
  haveI := hAcomm
  exact extraspecial_char_abelian_cyclic h2 hcf hfz hcard A

end S8

end CFSG.LocalAnalysis.GLTheoremA
