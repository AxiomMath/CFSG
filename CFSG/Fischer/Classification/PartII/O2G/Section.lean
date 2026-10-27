module

public import CFSG.Fischer.Classification.PartII.O2G.Parity
public import CFSG.Fischer.Classification.PartII.O2G.Line

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

namespace O2G

variable {G : Type} [Group G] {D : Set G}

theorem conj_mem_insert_twinClass (hP : Pair G D) {y z x : G} (k : G)
    (hx : x ∈ insert y (twinClass (LocalClass D y) z)) :
    k * x * k⁻¹ ∈ insert (k * y * k⁻¹) (twinClass (LocalClass D (k * y * k⁻¹)) (k * z * k⁻¹)) := by
  rcases hx with rfl | hx
  · exact Or.inl rfl
  · exact Or.inr (LocalU.isTwin_conj hP k hx)

theorem even_ncard_insert_of_far (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d f y z c : G} (hd : d ∈ D)
    (hy : y ∈ twinClass (LocalClass D d) f) (hz : z ∈ twinClass (LocalClass D d) f) (hyz : y ≠ z)
    (hc : c ∈ D) (hcd : c * d ≠ d * c)
    (hcT : ∀ x ∈ twinClass (LocalClass D d) f, x * c ≠ c * x) :
    Even (insert d (twinClass (LocalClass D d) f)).ncard := by
  have := Pair.finite hP
  have hyD : y ∈ D := hy.2.1.1
  have hzD : z ∈ D := hz.2.1.1
  have hyzc : y * z = z * y := (isTwin_of_mem hy hz).2.2.1
  have hyc : c * y ≠ y * c := fun e => hcT y hy e.symm
  have hzc : c * z ≠ z * c := fun e => hcT z hz e.symm
  have hg : (y * z)⁻¹ = y * z := inv_eq_of_mul_eq_one_right (mul_mul_mul_self hP hyD hzD hyzc)
  obtain ⟨c', hc'⟩ : ∃ c', c' = y * z * c * (y * z) := ⟨_, rfl⟩
  have hc'D : c' ∈ D := by
    have h := Pair.conj_mem hP hc (y * z)
    rwa [hg, ← hc'] at h
  have hcc' : c * c' = c' * c := by
    rw [hc']
    exact (conj_mul_commute hP hyD hzD hc hyzc hyc hzc).symm
  have hcne : c ≠ c' := by
    rw [hc']
    exact (conj_mul_ne_self hP hyD hzD hc hyz hyzc hyc hzc).symm
  have hk : c * c' * (c * c') = 1 := mul_mul_mul_self hP hc hc'D hcc'
  have hkinv : (c * c')⁻¹ = c * c' := inv_eq_of_mul_eq_one_right hk
  have hstep : c' * y * c' = z * c * z := by
    rw [hc']
    exact conj_conj_eq hP hyD hzD hc hyzc fun e => hcT y hy e
  have hky : c * c' * y * (c * c')⁻¹ = z := by
    rw [hkinv]
    calc c * c' * y * (c * c') = c * c' * y * (c' * c) := by rw [hcc']
      _ = c * (c' * y * c') * c := by simp only [mul_assoc]
      _ = c * (c * z * c) * c := by rw [hstep, Pair.mul_mul_eq hP hzD hc (hcT z hz)]
      _ = z := Pair.mul_mul_mul_mul hP hc z
  have hkz : c * c' * z * (c * c')⁻¹ = y := by
    rw [← hky, hkinv, conj_conj_of_mul_self hk]
  have hΛy := insert_twinClass_eq hP hZ hS hd hy hz hyz
  have hΛz := insert_twinClass_eq hP hZ hS hd hz hy hyz.symm
  refine even_ncard_of_involution (Set.toFinite _) (fun x => c * c' * x * (c * c')⁻¹)
    (fun x hx => ?_) (fun x _ => ?_) (fun x hx => ?_)
  · rw [hΛy] at hx
    have h := conj_mem_insert_twinClass hP (c * c') hx
    rwa [hky, hkz, ← hΛz] at h
  · simp only [hkinv]
    exact conj_conj_of_mul_self hk x
  · show c * c' * x * (c * c')⁻¹ ≠ x
    by_cases hxy : x = y
    · rw [hxy, hky]
      exact hyz.symm
    by_cases hxz : x = z
    · rw [hxz, hkz]
      exact hyz
    have hxD : x ∈ D := by
      rcases hx with rfl | hx
      · exact hd
      · exact hx.2.1.1
    have hxc : x * c ≠ c * x := by
      rcases hx with rfl | hx
      · exact fun e => hcd e.symm
      · exact hcT x hx
    have hxyz : x * y = y * x ∧ x * z = z * x := by
      rcases hx with rfl | hx
      · exact ⟨hy.2.1.2.2.symm, hz.2.1.2.2.symm⟩
      · exact ⟨(isTwin_of_mem hx hy).2.2.1, (isTwin_of_mem hx hz).2.2.1⟩
    have hxg : x * (y * z) = y * z * x := by
      rw [← mul_assoc, hxyz.1, mul_assoc, hxyz.2, ← mul_assoc]
    have hgx : y * z * x * (y * z)⁻¹ = x := by
      rw [← hxg, mul_inv_cancel_right]
    have hxc' : x * c' ≠ c' * x := by
      intro e
      apply hxc
      refine (conj_commute_iff (y * z) x c).1 ?_
      rw [hgx, hg, ← hc']
      exact e
    rw [hkinv]
    exact conj_mul_ne_self hP hc hc'D hxD hcne hcc' hxc hxc'

theorem meetsTwins_muSet (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) (hna : NonabelianCommutator G) {d c : G} (hd : d ∈ D)
    (h2 : HasNormalPSubgroup 2 (LocalQuotient D d)) (hc : c ∈ D) (hcd : c * d ≠ d * c) :
    MeetsTwins (LocalClass D d) (muSet D d c) := by
  intro f hf
  by_contra hno
  simp only [not_exists, not_and] at hno
  have := Pair.finite hP
  obtain ⟨a, a', htw, hne⟩ := exists_isTwin_ne hP hZ hS hna hd h2
  have hev := even_ncard_twinClass hP hZ hS hd htw hne hf
  have hfT : f ∈ twinClass (LocalClass D d) f := self_mem_twinClass hf
  have hpos : 0 < (twinClass (LocalClass D d) f).ncard := (Set.ncard_pos).2 ⟨f, hfT⟩
  have hone : 1 < (twinClass (LocalClass D d) f).ncard := by
    obtain ⟨m, hm⟩ := hev
    omega
  obtain ⟨z, hz, hzf⟩ := Set.exists_ne_of_one_lt_ncard hone f
  have hcT : ∀ x ∈ twinClass (LocalClass D d) f, x * c ≠ c * x := by
    intro x hx hxc
    refine hno x ⟨hx.2.1, hx.2.1.1, ?_, hxc⟩ hx
    rintro rfl
    exact hcd hx.2.1.2.2
  have hevΛ := even_ncard_insert_of_far hP hZ hS hd hfT hz hzf.symm hc hcd hcT
  have hdT : d ∉ twinClass (LocalClass D d) f := fun h => h.2.1.2.1 rfl
  rw [Set.ncard_insert_of_notMem hdT] at hevΛ
  exact (Nat.even_add_one.1 hevΛ) hev

end O2G

open O2G

theorem o2_O1 {G : Type} [Group G] {D : Set G} (hH : Hyp G D) (hna : NonabelianCommutator G)
    {d : G} (hd : d ∈ D) (h2 : HasNormalPSubgroup 2 (LocalQuotient D d)) {c : G} (hc : c ∈ D)
    (hcd : c * d ≠ d * c) :
    TwinFree (LocalClass D d) (muSet D d c) ∧ MeetsTwins (LocalClass D d) (muSet D d c) :=
  ⟨twinFree_muSet hH.pair hH.center hH.simple hd hc hcd,
    meetsTwins_muSet hH.pair hH.center hH.simple hna hd h2 hc hcd⟩

theorem o2_O1_input : ∀ (G : Type) [Group G] (D : Set G), StatementBelow (Nat.card G) →
    Hyp G D → NonabelianCommutator G → ¬ IsSymplecticType D →
    ∀ d ∈ D, (LocalClass D d).Nonempty → HasNormalPSubgroup 2 (LocalQuotient D d) →
      ∀ c ∈ D, c * d ≠ d * c →
        LocalU.TwinFree (LocalClass D d) (muSet D d c) ∧
          LocalU.MeetsTwins (LocalClass D d) (muSet D d c) :=
  fun _ _ _ _ hH hna _ _ hd _ h2 _ hc hcd => o2_O1 hH hna hd h2 hc hcd

end CFSG.Fischer.Classification
