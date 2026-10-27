module

public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b6
public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b5

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace Tri

variable {K J M : Subgroup G} {t u : G}

theorem outer_of_not_adj (hQ : QuatAutFacts r) (h : Tri r Ω K J M t u) (hr : RigidEdge K J t u)
    {A B : Subgroup G} (hA : A ∈ Ω) (hB : B ∈ Ω) {a b : G} (ha : IsUniqueInvolution A a)
    (hb : IsUniqueInvolution B b) (hne : a ≠ b) (hab : a * b = b * a)
    (hnadj : B ∉ omegaNbr Ω A) :
    ∀ R : Subgroup G, IsSylow2In R A → b ∈ Subgroup.normalizer (R : Set G) → Outer R b := by
  intro R hR hbR
  have hbC : b ∈ B ⊓ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hb.mem, Subgroup.mem_centralizer_singleton_iff.mpr hab.symm⟩
  obtain ⟨V, hV, hbV⟩ := IsSylow2In.exists_ge (Asc77.T8.isPGroup_zpowers_of_sq hb.sq)
    (Subgroup.zpowers_le.mpr hbC)
  have hbV' : b ∈ V := hbV (Subgroup.mem_zpowers b)
  rcases pair_cases h.fam hQ.three_le hA hB ha hb hne hV hbV' with hadj | ⟨-, hout⟩ | hU
  · exact absurd hadj hnadj
  · exact hout R hR hbR
  · exact (no_type3 hQ h hr hA hB ha hb hne hV hbV' hU).elim

theorem no_type2_central (hQ : QuatAutFacts r) (h : Tri r Ω K J M t u) (hr : RigidEdge K J t u)
    {S : Sylow 2 G} {P T T' : Subgroup G} (hs : SylowTri Ω S K J M P T T' t u) {L : Subgroup G}
    (hL : L ∈ Ω) {y : G} (hy : IsUniqueInvolution L y) (hyS : y ∈ (S : Subgroup G))
    (hyt : y * t = t * y) (hyu : y * u = u * y) (hyE : y ∉ Subgroup.closure ({t, u} : Set G)) :
    False := by
  have hΩ := h.fam.hyp
  have htP : t ∈ P := T3.mem_of_isPGroup h.inv_K hs.syl_P.1 hs.syl_P.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h.mem hs.syl_P)
    omega)
  have huT : u ∈ T := T3.mem_of_isPGroup h.inv_J hs.syl_T.1 hs.syl_T.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hs.mem_J hs.syl_T)
    omega)
  have htS : t ∈ (S : Subgroup G) := hs.le_P htP
  have huS : u ∈ (S : Subgroup G) := hs.le_T huT
  have htuS : t * u ∈ (S : Subgroup G) := Subgroup.mul_mem _ htS huS
  have hcomm := h.comm_tu
  have hEle : Subgroup.closure ({t, u} : Set G) ≤ (S : Subgroup G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact htS
    · rw [Set.mem_singleton_iff.mp hx]; exact huS
  have hEy : Subgroup.closure ({t, u} : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact Subgroup.mem_centralizer_singleton_iff.mpr hyt.symm
    · rw [Set.mem_singleton_iff.mp hx]; exact Subgroup.mem_centralizer_singleton_iff.mpr hyu.symm
  obtain ⟨R, hR, hRinv⟩ := T3.exists_sylow_normalized
    (S.isPGroup'.to_le hEle) (hEy.trans (fun w hw => h.fam.tight L hL y hy hw))
  have hnorm : ∀ w ∈ Subgroup.closure ({t, u} : Set G),
      w ∈ Subgroup.normalizer (R : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRinv w hw)
  have htE : t ∈ Subgroup.closure ({t, u} : Set G) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set G) := Subgroup.subset_closure (by simp)
  have key : ∀ {B : Subgroup G} {b : G}, B ∈ Ω → IsUniqueInvolution B b →
      (B = K ∨ B = J ∨ B = M) → b ∈ Subgroup.closure ({t, u} : Set G) →
      b * t = t * b → b * u = u * b → y * b = b * y → Outer R b := by
    intro B b hB hb hBKJM hbE hbt hbu hyb
    refine outer_of_not_adj hQ h hr hL hB hy hb (fun e => hyE (e ▸ hbE)) hyb ?_ R hR (hnorm b hbE)
    intro hBL
    have hLB : L ∈ omegaNbr Ω B := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hL hB hBL
    refine hyE (h.mem_E_of_adj hBKJM hb hLB hy
      (X := (S : Subgroup G) ⊓ Subgroup.centralizer ({b} : Set G))
      (S.isPGroup'.to_le inf_le_left) inf_le_right
      (Subgroup.mem_inf.mpr ⟨htS, Subgroup.mem_centralizer_singleton_iff.mpr hbt.symm⟩)
      (Subgroup.mem_inf.mpr ⟨huS, Subgroup.mem_centralizer_singleton_iff.mpr hbu.symm⟩)
      (Subgroup.mem_inf.mpr ⟨hyS, Subgroup.mem_centralizer_singleton_iff.mpr hyb⟩))
  obtain ⟨e⟩ := h.fam.quat L hL R hR
  have ht2 : Outer R t := key h.mem h.inv_K (Or.inl rfl) htE rfl hcomm hyt
  have hu2 : Outer R u := key hs.mem_J h.inv_J (Or.inr (Or.inl rfl)) huE hcomm.symm rfl hyu
  have htu2 : Outer R (t * u) :=
    key hs.mem_M h.inv_M (Or.inr (Or.inr rfl))
      (Subgroup.mul_mem _ htE huE) (by rw [mul_assoc, ← hcomm]) (by rw [← mul_assoc, ← hcomm])
      (by rw [← mul_assoc, hyt, mul_assoc, hyu, ← mul_assoc])
  exact hQ.not_outer_triple e (hnorm t htE) (hnorm u huE) hcomm h.inv_K.sq h.inv_J.sq
    ⟨ht2, hu2, htu2⟩

theorem no_type2_swap (hQ : QuatAutFacts r) (h : Tri r Ω K J M t u) (hr : RigidEdge K J t u)
    {S : Sylow 2 G} {P T T' : Subgroup G} (hs : SylowTri Ω S K J M P T T' t u) {L : Subgroup G}
    (hL : L ∈ Ω) {y : G} (hy : IsUniqueInvolution L y) (hyS : y ∈ (S : Subgroup G))
    (hyt : y * t = t * y) (hyu : y * u * y⁻¹ = t * u)
    (hyE : y ∉ Subgroup.closure ({t, u} : Set G)) : False := by
  have hΩ := h.fam.hyp
  have htP : t ∈ P := T3.mem_of_isPGroup h.inv_K hs.syl_P.1 hs.syl_P.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h.mem hs.syl_P)
    omega)
  have huT : u ∈ T := T3.mem_of_isPGroup h.inv_J hs.syl_T.1 hs.syl_T.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hs.mem_J hs.syl_T)
    omega)
  have htS : t ∈ (S : Subgroup G) := hs.le_P htP
  have huS : u ∈ (S : Subgroup G) := hs.le_T huT
  have hnadj : K ∉ omegaNbr Ω L := fun hKL =>
    hyE (h.mem_E_of_adj (Or.inl rfl) h.inv_K
      (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hL h.mem hKL) hy
      (S.isPGroup'.to_le inf_le_left) inf_le_right
      (Subgroup.mem_inf.mpr ⟨htS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
      (Subgroup.mem_inf.mpr ⟨huS, Subgroup.mem_centralizer_singleton_iff.mpr h.comm_tu.symm⟩)
      (Subgroup.mem_inf.mpr ⟨hyS, Subgroup.mem_centralizer_singleton_iff.mpr hyt⟩))
  have hout := outer_of_not_adj hQ h hr hL h.mem hy h.inv_K
    (fun e => hyE (e ▸ Subgroup.subset_closure (by simp))) hyt hnadj
  obtain ⟨e⟩ := h.fam.quat J hs.mem_J T hs.syl_T
  haveI : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  obtain ⟨s, hsT, hso⟩ : ∃ s ∈ T, orderOf s = 4 :=
    ⟨_, (e.symm (QuaternionGroup.xa 0)).2, by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]⟩
  have hss : s * s = u := by
    have h4 : s * s * (s * s) = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hso, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two] at this
    have h1 : s * s ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one (x := s) (n := 2) (by rw [pow_two]; exact h1)
      rw [hso] at this
      norm_num at this
    exact (h.inv_J.unique (s * s) (hs.syl_T.1 (T.mul_mem hsT hsT)) h4).resolve_left h1
  have hyJ : conjSub y J = M :=
    h.fam.noTwins M hs.mem_M (conjSub y J) ⟨hΩ.conjInvariant y J hs.mem_J, t * u, h.inv_M,
      hyu ▸ h.inv_J.conj y⟩
  have hsyT' : y * s * y⁻¹ ∈ T' := by
    have h1 : y * s * y⁻¹ ∈ conjSub y J := conj_mem_conjSub (hs.syl_T.1 hsT)
    rw [hyJ] at h1
    rw [← hs.syl_T'.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left
      (le_inf hs.syl_T'.1 hs.le_T')]
    exact Subgroup.mem_inf.mpr ⟨h1, (S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem hyS (hs.le_T hsT)) ((S : Subgroup G).inv_mem hyS)⟩
  have hcs : s * (y * s * y⁻¹) = y * s * y⁻¹ * s := hs.comm_TT' s hsT _ hsyT'
  obtain ⟨d, hd⟩ : ∃ d : G, d = s * (y * s * y⁻¹) := ⟨_, rfl⟩
  have hdd : d * d = t := by
    have e1 : d * d = s * s * (y * (s * s) * y⁻¹) := by
      calc d * d = s * (y * s * y⁻¹ * s) * (y * s * y⁻¹) := by rw [hd]; group
        _ = s * (s * (y * s * y⁻¹)) * (y * s * y⁻¹) := by rw [← hcs]
        _ = s * s * (y * (s * s) * y⁻¹) := by group
    rw [e1, hss, hyu, ← mul_assoc, ← h.comm_tu, mul_assoc, h.inv_J.sq, mul_one]
  have hdy : d * y = y * d := by
    have e1 : y * d * y⁻¹ = d := by
      calc y * d * y⁻¹ = y * s * y⁻¹ * ((y * y) * s * (y * y)⁻¹) := by rw [hd]; group
        _ = y * s * y⁻¹ * s := by rw [hy.sq, one_mul, inv_one, mul_one]
        _ = d := by rw [hd, hcs]
    exact (mul_inv_eq_iff_eq_mul.mp e1).symm
  have hdS : d ∈ (S : Subgroup G) := hd ▸ (S : Subgroup G).mul_mem (hs.le_T hsT) (hs.le_T' hsyT')
  obtain ⟨R, hR, hRd⟩ := T3.exists_sylow_normalized
    (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hdS))
    ((Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hdy)).trans
      (h.fam.tight L hL y hy))
  have hdR : d ∈ Subgroup.normalizer (R : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (hRd d (Subgroup.mem_zpowers d))
  have htR : t ∈ Subgroup.normalizer (R : Set G) := hdd ▸ Subgroup.mul_mem _ hdR hdR
  obtain ⟨eR⟩ := h.fam.quat L hL R hR
  obtain ⟨w, hwR, hwd, hww⟩ := hQ.exists_fixed_of_sq eR hdR (by rw [hdd]; exact h.inv_K.sq)
  rw [hdd] at hwd
  exact hww (hout R hR htR w hwR hwd)

end Tri

end CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b
