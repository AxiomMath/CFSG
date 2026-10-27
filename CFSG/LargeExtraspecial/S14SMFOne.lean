module

public import CFSG.LargeExtraspecial.S14SMEConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

namespace SMF

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem conj_z_not_mem_QG (S : Setting G) {k : G} (haQ : k * S.z * k⁻¹ ∉ S.QG) :
    k⁻¹ * S.z * k ∉ S.QG := by
  intro h
  have hne : (1 : G) * S.z * 1⁻¹ ≠ k * S.z * k⁻¹ := by
    intro h1
    apply haQ
    rw [← h1]
    simpa using S.z_mem_QG
  have h' := SME.mem_Qa_symm S (g := k) (k := 1) (by simpa using h) hne
  exact haQ (by simpa using h')

theorem mem_commutator_of_mem_Qa (S : Setting G) {k y : G} (hwM : k * S.z * k⁻¹ ∈ S.M)
    (hwQ : k * S.z * k⁻¹ ∉ S.QG) (hyQ : y ∈ S.QG) (hyw : k⁻¹ * y * k ∈ S.QG)
    (hno : ¬ ∃ r ∈ S.QG, r * (k * S.z * k⁻¹) * r⁻¹ = k * S.z * k⁻¹ * S.z) :
    ∃ r ∈ S.QG, k * S.z * k⁻¹ * r * (k * S.z * k⁻¹)⁻¹ * r⁻¹ = y ∨
      k * S.z * k⁻¹ * r * (k * S.z * k⁻¹)⁻¹ * r⁻¹ = y * S.z := by
  have hzw := conj_z_not_mem_QG S hwQ
  set w := k * S.z * k⁻¹ with hw
  have hw2 : w ^ 2 = 1 := by rw [hw, conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hfix : S.fixQt w = S.clSub (S.QG ⊓ centralizer ({w} : Set G)) := by
    by_contra h
    exact hno (S.lemma_3_2_1 hwM h)
  have key : y ∈ S.QG ⊓
      centralizer ((S.QG ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) := by
    refine ⟨hyQ, mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hsw : Commute s w := mem_centralizer_singleton_iff.mp hs.2
    have hsM : k⁻¹ * s * k ∈ S.M := (SME.mem_M_conj_iff S k s).mpr hsw
    rcases S.commutator_eq_one_or_z hs.1 hyQ with h | h
    · calc s * y = s * y * s⁻¹ * y⁻¹ * (y * s) := by group
        _ = y * s := by rw [h, one_mul]
    · exfalso
      apply hzw
      have e : k⁻¹ * S.z * k =
          (k⁻¹ * s * k) * (k⁻¹ * y * k) * (k⁻¹ * s * k)⁻¹ * (k⁻¹ * y * k)⁻¹ := by
        rw [← h]
        group
      rw [e]
      exact S.QG.mul_mem (S.conj_mem_QG hsM hyw) (S.QG.inv_mem hyw)
  have hyc : y ∈ (⁅zpowers w, S.QG⁆ : Subgroup G) := by
    rw [(S.commutator_eq_centralizer_centralizer hwM hwQ hw2 hfix).1]
    exact key
  rw [S.commutator_zpowers_eq_clPre hwM hwQ hw2] at hyc
  obtain ⟨r, hr, hrc⟩ := (S.mem_commQt_iff hwM).mp hyc.2
  refine ⟨r, hr, ?_⟩
  rcases (S.cl_eq_cl_iff (S.commutator_mem_QG hwM hr) hyQ).mp hrc with h | h
  · exact Or.inl h.symm
  · right
    rw [h, mul_assoc _ S.z S.z, S.z_mul_z, mul_one]

theorem commute_of_cl_eq_commutator (S : Setting G) {x c y : G} (hxM : x ∈ S.M)
    (hc : c ∈ S.QG) (hyQ : y ∈ S.QG) (hyy : y * y = 1)
    (hcl : S.cl y = S.cl (x * c * x⁻¹ * c⁻¹)) : c * y = y * c := by
  refine (S.polar_cl_eq_zero_iff hc hyQ).mp ?_
  have hw := CFSG.RankThree.OrthogonalInvolutions.wallForm_self (S.ρ_mem_O ⟨x, hxM⟩) (S.cl c)
  rw [CFSG.RankThree.OrthogonalInvolutions.wallForm_apply, ← S.cl_commutator hxM hc, ← hcl] at hw
  rw [hw]
  exact (S.q_cl_eq_zero_iff hyQ).mpr (by rw [sq, hyy])

theorem isConj_of_mem_J (S : Setting G) {g y : G} (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxQ : g * S.z * g⁻¹ ∉ S.QG) (hy1 : y ≠ 1)
    (hyJ : y ∈ (⁅zpowers (g * S.z * g⁻¹), S.QG⁆ : Subgroup G))
    (hyx : Commute (g * S.z * g⁻¹) y) (hyQx : y ∈ S.Qa g) :
    IsConj S.z y ∨ IsConj (g * S.z * g⁻¹ * S.z) y := by
  have hzT0 : g⁻¹ * S.z * g ∉ S.QG := conj_z_not_mem_QG S hxQ
  have hyQx' : g⁻¹ * y * g ∈ S.QG := (SME.mem_Qa_iff S g y).mp hyQx
  set T := S.conjBy g with hT
  set x := g * S.z * g⁻¹ with hx
  have hTz : T.z = x := rfl
  have hyT : y ∈ T.QG := hyQx
  have hxT : x ∈ T.QG := T.z_mem_QG
  have hzT : S.z ∉ T.QG := fun h => hzT0 ((SME.mem_Qa_iff S g S.z).mp h)
  have hx2 : x ^ 2 = 1 := by rw [hx, conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hxx : x * x = 1 := by rw [← sq, hx2]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hzx : x * S.z = S.z * x := S.z_comm hxM
  have hxy : x * y = y * x := hyx.eq
  have hzc : IsConj S.z x := isConj_iff.mpr ⟨g, rfl⟩
  rw [S.commutator_zpowers_eq_clPre hxM hxQ hx2] at hyJ
  obtain ⟨hyQ, hyc⟩ := hyJ
  have hyz : y ≠ S.z := fun h => hzT (h ▸ hyT)
  have hyxne : y ≠ x := fun h => hxQ (h ▸ hyQ)
  have hzy : y * S.z = S.z * y := S.z_comm_QG hyQ
  have hyy : y * y = 1 := by
    rw [← sq]
    rcases S.sq_eq_one_or_z hyQ with h1 | h1
    · exact h1
    · rcases T.sq_eq_one_or_z hyT with h2 | h2
      · exact h2
      · exfalso
        apply hxQ
        have e : S.z = x := h1.symm.trans h2
        rw [← e]
        exact S.z_mem_QG
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  obtain ⟨q, -, hq⟩ := SME.exists_conj_eq_mul_z S hyQ hy1 hyz
  have hyu : IsConj y (y * S.z) := isConj_iff.mpr ⟨q, hq⟩
  obtain ⟨c, hc, hcy⟩ := (S.mem_commQt_iff hxM).mp hyc
  rcases (S.cl_eq_cl_iff (S.commutator_mem_QG hxM hc) hyQ).mp hcy with hA | hB
  ·
    left
    have hcx : c * x * c⁻¹ = y * x := by
      calc c * x * c⁻¹ = c * x⁻¹ * c⁻¹ := by rw [hxi]
        _ = (x * x) * c * x⁻¹ * c⁻¹ := by rw [hxx, one_mul]
        _ = x * (x * c * x⁻¹ * c⁻¹) := by group
        _ = x * y := by rw [← hA]
        _ = y * x := hxy
    have h1 : IsConj S.z (y * x) := by
      rw [← hcx]
      exact hzc.trans (isConj_iff.mpr ⟨c, rfl⟩)
    have h2 : IsConj y (y * x) := SME.isConj_mul_of_mem_Qa S hyQx' hy1 hyxne
    exact h1.trans h2.symm
  ·
    have hB' : x * c * x⁻¹ * c⁻¹ = y * S.z := by
      rw [hB, mul_assoc _ S.z S.z, S.z_mul_z, mul_one]
    have hcy' : c * y = y * c := commute_of_cl_eq_commutator S hxM hc hyQ hyy (by
      rw [hB, S.cl_mul_z (S.commutator_mem_QG hxM hc)])
    have hcyc : c⁻¹ * y * c = y := by
      calc c⁻¹ * y * c = c⁻¹ * (y * c) := by group
        _ = c⁻¹ * (c * y) := by rw [hcy']
        _ = y := by group
    have hw : c * x * c⁻¹ = S.z * y * x := by
      calc c * x * c⁻¹ = (x * c * x⁻¹ * c⁻¹)⁻¹ * x := by group
        _ = (y * S.z)⁻¹ * x := by rw [hB']
        _ = S.z * y * x := by rw [mul_inv_rev, S.z_inv, hyi]
    have hwz : IsConj S.z (S.z * y * x) := by
      rw [← hw]
      exact hzc.trans (isConj_iff.mpr ⟨c, rfl⟩)
    have hwx : x * (S.z * y * x) = S.z * y * x * x := by
      calc x * (S.z * y * x) = (x * S.z) * y * x := by group
        _ = (S.z * x) * y * x := by rw [hzx]
        _ = S.z * (x * y) * x := by group
        _ = S.z * (y * x) * x := by rw [hxy]
        _ = S.z * y * x * x := by group
    have e1 : y * S.z = x * (S.z * y * x) := by
      rw [hwx, mul_assoc (S.z * y) x x, hxx, mul_one, hzy]
    have hwT : c * T.z * c⁻¹ ∈ T.M := by
      rw [mem_centralizer_singleton_iff, hTz, hw]
      exact hwx.symm
    have hwTQ : c * T.z * c⁻¹ ∉ T.QG := by
      intro h
      rw [hTz, hw] at h
      apply hzT
      have e : S.z = S.z * y * x * x⁻¹ * y⁻¹ := by group
      rw [e]
      exact T.QG.mul_mem (T.QG.mul_mem h (T.QG.inv_mem hxT)) (T.QG.inv_mem hyT)
    have hyw : c⁻¹ * y * c ∈ T.QG := by
      rw [hcyc]
      exact hyT
    by_cases hsub : ∃ r ∈ T.QG, r * (c * T.z * c⁻¹) * r⁻¹ = c * T.z * c⁻¹ * T.z
    ·
      left
      obtain ⟨r, hr, hrw⟩ := hsub
      rw [hTz, hw] at hrw
      have hrx : r * x = x * r := mem_centralizer_singleton_iff.mp (T.QG_le_M hr)
      have hu : r * (y * S.z) * r⁻¹ = S.z * y * x := by
        calc r * (y * S.z) * r⁻¹ = r * x * (S.z * y * x) * r⁻¹ := by rw [e1]; group
          _ = x * (r * (S.z * y * x) * r⁻¹) := by rw [hrx]; group
          _ = x * (S.z * y * x * x) := by rw [hrw]
          _ = x * (S.z * y * x) * x := by group
          _ = S.z * y * x * x * x := by rw [hwx]
          _ = S.z * y * x := by rw [mul_assoc (S.z * y * x) x x, hxx, mul_one]
      exact hwz.trans ((hyu.trans (isConj_iff.mpr ⟨r, hu⟩)).symm)
    ·
      obtain ⟨r, hr, hrd⟩ := mem_commutator_of_mem_Qa T hwT hwTQ hyT hyw hsub
      rw [hTz, hw] at hrd
      have hrx : r * x = x * r := mem_centralizer_singleton_iff.mp (T.QG_le_M hr)
      have hconj : ∀ d : G, S.z * y * x * r * (S.z * y * x)⁻¹ * r⁻¹ = d →
          r * (y * S.z) * r⁻¹ = x * d⁻¹ * (S.z * y * x) := by
        intro d hd
        calc r * (y * S.z) * r⁻¹ = r * x * (S.z * y * x) * r⁻¹ := by rw [e1]; group
          _ = x * (r * (S.z * y * x) * r⁻¹) := by rw [hrx]; group
          _ = x * ((S.z * y * x * r * (S.z * y * x)⁻¹ * r⁻¹)⁻¹ * (S.z * y * x)) := by
            group
          _ = x * d⁻¹ * (S.z * y * x) := by rw [hd]; group
      rcases hrd with hd | hd
      ·
        left
        have h := hconj y hd
        have hz' : x * y⁻¹ * (S.z * y * x) = S.z := by
          calc x * y⁻¹ * (S.z * y * x) = x * (y * S.z) * y * x := by rw [hyi]; group
            _ = x * (S.z * y) * y * x := by rw [hzy]
            _ = x * S.z * (y * y) * x := by group
            _ = x * S.z * x := by rw [hyy, mul_one]
            _ = S.z * x * x := by rw [hzx]
            _ = S.z := by rw [mul_assoc, hxx, mul_one]
        exact (hyu.trans (isConj_iff.mpr ⟨r, h.trans hz'⟩)).symm
      ·
        right
        have h := hconj (y * x) hd
        have hxz' : x * (y * x)⁻¹ * (S.z * y * x) = x * S.z := by
          calc x * (y * x)⁻¹ * (S.z * y * x) = x * (x⁻¹ * y⁻¹) * (S.z * y * x) := by
                rw [mul_inv_rev]
            _ = y⁻¹ * S.z * y * x := by group
            _ = y * S.z * y * x := by rw [hyi]
            _ = S.z * y * y * x := by rw [hzy]
            _ = S.z * x := by rw [mul_assoc S.z y y, hyy, mul_one]
            _ = x * S.z := hzx.symm
        exact (hyu.trans (isConj_iff.mpr ⟨r, h.trans hxz'⟩)).symm

end SMF

end CFSG.LargeExtraspecial.S14
