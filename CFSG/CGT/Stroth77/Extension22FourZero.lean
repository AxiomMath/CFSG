module

public import CFSG.CGT.Stroth77.Extension22FourAssembly
import all CFSG.CGT.Stroth77.Extension22FourAssembly
import all CFSG.CGT.Stroth77.Extension22FourBasis
import all CFSG.CGT.Stroth77.AmbientSplit
public import CFSG.CGT.Stroth77.Extension22FourBasis

public section

namespace CFSG.CGT.Stroth77

open scoped IsMulCommutative

section Helpers

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S}

theorem torus_t100_zero_add_self (z : Torus (Type100.k 0)) : z + z = 0 := by
  funext i
  fin_cases i
  · have hk : Type100.k 0 0 = 0 := k100_zero 0
    have h2 : (2 : ZMod (2 ^ Type100.k 0 0)) = 0 := by
      rw [hk]
      decide
    calc z 0 + z 0 = (2 : ZMod (2 ^ Type100.k 0 0)) * z 0 := by rw [two_mul]
      _ = 0 := by rw [h2, zero_mul]
  · have hk : Type100.k 0 1 = 1 := k100_one 0
    have h2 : (2 : ZMod (2 ^ Type100.k 0 1)) = 0 := by
      rw [hk]
      decide
    calc z 1 + z 1 = (2 : ZMod (2 ^ Type100.k 0 1)) * z 1 := by rw [two_mul]
      _ = 0 := by rw [h2, zero_mul]
  · have hk : Type100.k 0 2 = 1 := k100_two 0
    have h2 : (2 : ZMod (2 ^ Type100.k 0 2)) = 0 := by
      rw [hk]
      decide
    calc z 2 + z 2 = (2 : ZMod (2 ^ Type100.k 0 2)) * z 2 := by rw [two_mul]
      _ = 0 := by rw [h2, zero_mul]

theorem t100_zero_mul_self (D : StrothTypeData B (StrothTypeIndex.t100 0)) (x : B) :
    x * x = 1 := by
  apply D.ec_injective
  rw [D.ec_mul, D.ec_one]
  exact torus_t100_zero_add_self (D.ec x)

theorem sqSubgroup_eq_bot_of_m_zero (D : StrothTypeData B (StrothTypeIndex.t100 0)) :
    sqSubgroup D = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  rw [mem_sqSubgroup_iff_isSquare] at hx
  change ∃ b : B, (b : S) * (b : S) = (x : S) at hx
  obtain ⟨b, hb⟩ := hx
  apply Subtype.ext
  rw [← hb]
  simpa using congrArg (fun z : B => (z : S)) (t100_zero_mul_self D b)

theorem closure_c_e_f_of_m_zero
    (hcommC : IsMulCommutative C)
    (D : StrothTypeData B (StrothTypeIndex.t100 0))
    (hBC : B ≤ C) (hrel : Nat.card C = 4 * Nat.card B)
    {e f : C}
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) :
    Subgroup.closure ({⟨D.c, hBC D.c.2⟩, e, f} : Set C) = ⊤ := by
  classical
  haveI : IsMulCommutative C := hcommC
  let cC : C := ⟨D.c, hBC D.c.2⟩
  let aC : C := ⟨D.a, hBC D.a.2⟩
  let bC : C := ⟨D.b, hBC D.b.2⟩
  let K : Subgroup C := Subgroup.closure ({cC, e, f} : Set C)
  have hcK : cC ∈ K := Subgroup.subset_closure (by simp [K])
  have heK : e ∈ K := Subgroup.subset_closure (by simp [K])
  have hfK : f ∈ K := Subgroup.subset_closure (by simp [K])
  have haK : aC ∈ K := by
    have h : aC = e * e := he.symm
    rw [h]
    exact K.mul_mem heK heK
  have hbK : bC ∈ K := by
    have h : bC = f * f := hf.symm
    rw [h]
    exact K.mul_mem hfK hfK
  have hBgenB : Subgroup.closure ({(D.c : B), (D.a : B), (D.b : B)} : Set B) = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective B)
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    have himg : B.subtype '' ({(D.c : B), (D.a : B), (D.b : B)} : Set B) =
        ({(D.c : S), (D.a : S), (D.b : S)} : Set S) := by
      ext y
      simp
    rw [himg, D.closure_c_a_b]
  have hBgenC : B.subgroupOf C = Subgroup.closure ({cC, aC, bC} : Set C) := by
    calc B.subgroupOf C = (⊤ : Subgroup B).map (Subgroup.inclusion hBC) := by
          rw [Subgroup.map_top, Subgroup.inclusion_range]
      _ = (Subgroup.closure ({(D.c : B), (D.a : B), (D.b : B)} : Set B)).map
            (Subgroup.inclusion hBC) := by rw [hBgenB]
      _ = Subgroup.closure ((Subgroup.inclusion hBC) ''
            ({(D.c : B), (D.a : B), (D.b : B)} : Set B)) :=
          MonoidHom.map_closure (Subgroup.inclusion hBC) _
      _ = Subgroup.closure ({cC, aC, bC} : Set C) := by
          have hc_eq : (Subgroup.inclusion hBC D.c : C) = cC := Subtype.ext rfl
          have ha_eq : (Subgroup.inclusion hBC D.a : C) = aC := Subtype.ext rfl
          have hb_eq : (Subgroup.inclusion hBC D.b : C) = bC := Subtype.ext rfl
          congr 1
          ext y
          simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨b, hb, hby⟩
            rcases hb with rfl | rfl | rfl
            · exact Or.inl (hby.symm.trans hc_eq)
            · exact Or.inr (Or.inl (hby.symm.trans ha_eq))
            · exact Or.inr (Or.inr (hby.symm.trans hb_eq))
          · rintro (h | h | h)
            · exact ⟨D.c, Or.inl rfl, hc_eq.trans h.symm⟩
            · exact ⟨D.a, Or.inr (Or.inl rfl), ha_eq.trans h.symm⟩
            · exact ⟨D.b, Or.inr (Or.inr rfl), hb_eq.trans h.symm⟩
  have hB_le_K : B.subgroupOf C ≤ K := by
    rw [hBgenC]
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hcK
    · exact haK
    · exact hbK
  have hna : orderOf D.a = 2 := by
    rw [D.orderOf_a, n_t100]
    norm_num
  have hnb : orderOf D.b = 2 := by
    rw [D.orderOf_b, n_t100]
    norm_num
  have ha1 : D.a ≠ 1 := by
    intro h
    have : orderOf D.a = 1 := by rw [h, orderOf_one]
    rw [hna] at this
    norm_num at this
  have hb1 : D.b ≠ 1 := by
    intro h
    have : orderOf D.b = 1 := by rw [h, orderOf_one]
    rw [hnb] at this
    norm_num at this
  have hab : D.a ≠ D.b := by
    intro h
    have h' : (Torus.a : Torus (StrothTypeIndex.t100 0).k) = Torus.b := by
      have := congrArg (fun x : B => D.e (Additive.ofMul x)) h
      simpa [StrothTypeData.a, StrothTypeData.b] using this
    have hne : (Torus.a : Torus (StrothTypeIndex.t100 0).k) 1 ≠
        (Torus.b : Torus (StrothTypeIndex.t100 0).k) 1 := by
      simp [Torus.a, Torus.b, gen, Pi.single_apply]
      decide
    exact hne (congrFun h' 1)
  have hab_ne1 : D.a * D.b⁻¹ ≠ 1 := fun h => hab (mul_inv_eq_one.mp h)
  have he_notH : e ∉ B.subgroupOf C := by
    intro heH
    have heB : (e : S) ∈ B := Subgroup.mem_subgroupOf.mp heH
    let eB : B := ⟨(e : S), heB⟩
    have heB_sq : eB * eB = D.a := by
      apply Subtype.ext
      have h := congrArg (fun z : C => (z : S)) he
      simpa [eB, aC] using h
    have h1 : eB * eB = 1 := t100_zero_mul_self D eB
    rw [h1] at heB_sq
    exact ha1 heB_sq.symm
  have hf_notH : f ∉ B.subgroupOf C := by
    intro hfH
    have hfB : (f : S) ∈ B := Subgroup.mem_subgroupOf.mp hfH
    let fB : B := ⟨(f : S), hfB⟩
    have hfB_sq : fB * fB = D.b := by
      apply Subtype.ext
      have h := congrArg (fun z : C => (z : S)) hf
      simpa [fB, bC] using h
    have h1 : fB * fB = 1 := t100_zero_mul_self D fB
    rw [h1] at hfB_sq
    exact hb1 hfB_sq.symm
  have hef_notH : e * f⁻¹ ∉ B.subgroupOf C := by
    intro hefH
    have hefB : ((e * f⁻¹ : C) : S) ∈ B := Subgroup.mem_subgroupOf.mp hefH
    let y : B := ⟨((e * f⁻¹ : C) : S), hefB⟩
    have hy_sqC : (e * f⁻¹) * (e * f⁻¹) = aC * bC⁻¹ := by
      calc (e * f⁻¹) * (e * f⁻¹) = (e * e) * (f⁻¹ * f⁻¹) :=
            mul_mul_mul_comm _ _ _ _
        _ = (e * e) * (f * f)⁻¹ := by rw [← mul_inv_rev]
        _ = aC * bC⁻¹ := by rw [he, hf]
    have hy_sq : y * y = D.a * D.b⁻¹ := by
      apply Subtype.ext
      have h := congrArg (fun z : C => (z : S)) hy_sqC
      simpa [y, aC, bC] using h
    have h1 : y * y = 1 := t100_zero_mul_self D y
    rw [h1] at hy_sq
    exact hab_ne1 hy_sq.symm
  have hHindex : (B.subgroupOf C).index = 4 := index_four_of_relIndex hBC hrel
  have hrel_dvd : (B.subgroupOf C).relIndex K ∣ 4 := by
    have h := Subgroup.relIndex_mul_index hB_le_K
    rw [hHindex] at h
    exact ⟨K.index, h.symm⟩
  have hrel_ne1 : (B.subgroupOf C).relIndex K ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact he_notH (h1 heK)
  have hrel_ne2 : (B.subgroupOf C).relIndex K ≠ 2 := by
    intro h2
    have hH'index : ((B.subgroupOf C).subgroupOf K).index = 2 := by
      simpa [Subgroup.relIndex] using h2
    have heK' : (⟨e, heK⟩ : K) ∉ (B.subgroupOf C).subgroupOf K := by
      intro hmem
      exact he_notH (Subgroup.mem_subgroupOf.mp hmem)
    have hfK' : (⟨f⁻¹, K.inv_mem hfK⟩ : K) ∉ (B.subgroupOf C).subgroupOf K := by
      intro hmem
      exact hf_notH (inv_mem_iff.mp (Subgroup.mem_subgroupOf.mp hmem))
    have hprod : (⟨e, heK⟩ : K) * (⟨f⁻¹, K.inv_mem hfK⟩ : K) ∈
        (B.subgroupOf C).subgroupOf K :=
      (Subgroup.mul_mem_iff_of_index_two hH'index).mpr (by simp [heK', hfK'])
    have : e * f⁻¹ ∈ B.subgroupOf C := by
      simpa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using hprod
    exact hef_notH this
  have hrel4 : (B.subgroupOf C).relIndex K = 4 := by
    have hpos : 0 < (B.subgroupOf C).relIndex K :=
      Nat.pos_of_dvd_of_pos hrel_dvd (by norm_num)
    have hle : (B.subgroupOf C).relIndex K ≤ 4 := Nat.le_of_dvd (by norm_num) hrel_dvd
    interval_cases (B.subgroupOf C).relIndex K <;> simp_all
  have hKindex : K.index = 1 := by
    have h := Subgroup.relIndex_mul_index hB_le_K
    rw [hrel4, hHindex] at h
    omega
  exact Subgroup.index_eq_one.mp hKindex

end Helpers

end CFSG.CGT.Stroth77
