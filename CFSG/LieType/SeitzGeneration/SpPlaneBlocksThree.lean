module

public import CFSG.RankThree.PartOne.CTP.SeitzSpPlane
public import CFSG.LieType.SeitzGeneration.SpSubEmb
public import CFSG.LieType.SeitzGeneration.SpFourThree

public section

namespace CFSG.LieType.SeitzGeneration.SpPlaneThree

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K]

theorem nondegenerate_restrict_of_key {P : Submodule K (Fin r ⊕ Fin r → K)}
    (key : ∀ x ∈ P, (∀ y ∈ P, spForm r K x y = 0) → x = 0) :
    ((spForm r K).restrict P).Nondegenerate := by
  constructor
  · intro x hx
    exact Subtype.ext (key x x.2 fun y hy => hx ⟨y, hy⟩)
  · intro x hx
    refine Subtype.ext (key x x.2 fun y hy => ?_)
    have h : spForm r K y x = 0 := hx ⟨y, hy⟩
    rw [← spForm_isAlt.neg_eq y x, h, neg_zero]

theorem norm_eq_zero_of_no_fixed {U : Submodule K (Fin r ⊕ Fin r → K)} {g : StatedSp r K}
    (hg : g ^ 3 = 1) (hstab : ∀ v ∈ U, spEnd g v ∈ U)
    (hfix : ∀ v ∈ U, spEnd g v = v → v = 0) {u : Fin r ⊕ Fin r → K} (hu : u ∈ U) :
    u + spEnd g u + spEnd g (spEnd g u) = 0 :=
  hfix _ (U.add_mem (U.add_mem hu (hstab u hu)) (hstab _ (hstab u hu))) (spEnd_norm_fixed hg u)

theorem exists_spForm_ne_zero_of_no_fixed {U : Submodule K (Fin r ⊕ Fin r → K)}
    (hnd : ((spForm r K).restrict U).Nondegenerate) {g : StatedSp r K} (hg : g ^ 3 = 1)
    (hstab : ∀ v ∈ U, spEnd g v ∈ U) (hfix : ∀ v ∈ U, spEnd g v = v → v = 0)
    (hU : U ≠ ⊥) : ∃ u ∈ U, spForm r K u (spEnd g u) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have key : ∀ u ∈ U, ∀ w ∈ U, spForm r K u (spEnd g w) = - spForm r K w (spEnd g u) := by
    intro u hu w hw
    have h := hcon (u + w) (U.add_mem hu hw)
    simp only [map_add, LinearMap.add_apply] at h
    linear_combination h - hcon u hu - hcon w hw
  have h2 : ∀ u ∈ U, spEnd g (spEnd g u) = spEnd g u := by
    intro u hu
    have hmem : spEnd g (spEnd g u) - spEnd g u ∈ U :=
      U.sub_mem (hstab _ (hstab u hu)) (hstab u hu)
    have hz := hnd.1 ⟨_, hmem⟩ fun w => by
      change spForm r K (spEnd g (spEnd g u) - spEnd g u) w = 0
      have e1 : spForm r K (spEnd g (spEnd g u)) w = spForm r K u (spEnd g w) := by
        have := spEnd_isometry g (spEnd g (spEnd g u)) w
        rw [spEnd_cube_apply hg u] at this
        exact this.symm
      have e2 := spForm_isAlt.neg_eq (spEnd g u) w
      have k := key u hu w w.2
      rw [map_sub, LinearMap.sub_apply]
      linear_combination e1 + k + e2
    exact sub_eq_zero.mp (congrArg Subtype.val hz)
  apply hu₀0
  apply hfix u₀ hu₀
  have h3 : spEnd g (spEnd g (spEnd g u₀)) = spEnd g (spEnd g u₀) :=
    congrArg (spEnd g) (h2 u₀ hu₀)
  rw [spEnd_cube_apply hg u₀] at h3
  exact (h2 u₀ hu₀).symm.trans h3.symm

theorem span_pair_stable {g : StatedSp r K} {u : Fin r ⊕ Fin r → K}
    (hnorm : u + spEnd g u + spEnd g (spEnd g u) = 0) :
    ∀ v ∈ Submodule.span K {u, spEnd g u}, spEnd g v ∈ Submodule.span K {u, spEnd g u} := by
  intro v hv
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
  rw [map_add, map_smul, map_smul]
  have h : spEnd g (spEnd g u) = -u - spEnd g u := by linear_combination (norm := module) hnorm
  rw [h]
  exact Submodule.mem_span_pair.2 ⟨-b, a - b, by module⟩

theorem finrank_span_pair_of_spForm {u w : Fin r ⊕ Fin r → K} (h : spForm r K u w ≠ 0) :
    Module.finrank K (Submodule.span K {u, w}) = 2 := by
  rw [← range_pair_eq, finrank_span_eq_card (linearIndependent_pair_of_spForm h)]
  simp

theorem nondegenerate_span_pair {u w : Fin r ⊕ Fin r → K} (h : spForm r K u w ≠ 0) :
    ((spForm r K).restrict (Submodule.span K {u, w})).Nondegenerate := by
  refine nondegenerate_restrict_of_key fun x hx hxy => ?_
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
  have h1 := hxy u (Submodule.subset_span (Set.mem_insert _ _))
  have h2 := hxy w (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hc : spForm r K w u ≠ 0 := fun h0 => h (by rw [← spForm_isAlt.neg_eq w u, h0, neg_zero])
  have hb : b = 0 := by
    have : b * spForm r K w u = 0 := by simpa [spForm_isAlt u] using h1
    exact (mul_eq_zero.mp this).resolve_right hc
  have ha : a = 0 := by
    have : a * spForm r K u w = 0 := by simpa [spForm_isAlt w] using h2
    exact (mul_eq_zero.mp this).resolve_right h
  rw [ha, hb]
  simp

theorem mem_spStab_of_stable {W : Submodule K (Fin r ⊕ Fin r → K)} {g : StatedSp r K}
    (hg : g ^ 3 = 1) (h : ∀ v ∈ W, spEnd g v ∈ W) : g ∈ spStab W := by
  have hinv : g⁻¹ = g * g := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three, hg]
  intro u hu
  refine ⟨h u hu, ?_⟩
  rw [hinv, spEnd_comp_apply]
  exact h _ (h u hu)

theorem transCenter_of_four [Finite K] (h3 : (3 : K) ≠ 0) (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1)
    {E : Subgroup (StatedSp r K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9)
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hnd : ((spForm r K).restrict W).Nondegenerate)
    (hdim : Module.finrank K W = 4) (hstab : E ≤ spStab W)
    (hfaith : ∀ x ∈ E, (∀ v ∈ W, spEnd x v = v) → x = 1) {v : Fin r ⊕ Fin r → K} (hv : v ∈ W) :
    TransCenter (centralizerSpan E) v := by
  obtain ⟨m, e, heU, hm⟩ := SpSubEmb.exists hnd
  have hm2 : m = 2 := by omega
  subst hm2
  have hstab' : E ≤ spStab e.U := heU ▸ hstab
  set ψ : E →* StatedSp 2 K := e.res.comp (Subgroup.inclusion hstab') with hψ
  have hψa : ∀ a : E, ψ a = e.res ⟨a, hstab' a.2⟩ := fun a => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hψa, e.res_eq_one_iff] at hx
    exact Subtype.ext (hfaith x x.2 fun w hw => hx w (heU ▸ hw))
  have hrange : Nat.card ψ.range = 9 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hrangeComm : ∀ x ∈ ψ.range, ∀ y ∈ ψ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hcomm a a.2 b b.2))
  have hrangeExp : ∀ x ∈ ψ.range, x ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (hexp a a.2)
    rw [this, map_one]
  have hplane := closure_centralizers_spFour_three h3 hK hrangeComm hrangeExp hrange
  have hle : e.ext.range ≤ centralizerSpan E := by
    have key : e.ext.range =
        Subgroup.closure (e.ext '' {g | ∃ x ∈ ψ.range, x ≠ 1 ∧ g * x = x * g}) := by
      rw [MonoidHom.range_eq_map, ← hplane, MonoidHom.map_closure]
    rw [key, Subgroup.closure_le]
    rintro _ ⟨g, ⟨_, ⟨a, rfl⟩, hx1, hgx⟩, rfl⟩
    refine mem_centralizerSpan a.2 ?_ (e.commute_ext ⟨a, hstab' a.2⟩ hgx.symm).symm
    intro ha1
    apply hx1
    have : a = 1 := Subtype.ext ha1
    rw [this, map_one]
  intro t
  rw [← heU] at hv
  obtain ⟨x, hx⟩ : ∃ x, (e.φ x : Fin r ⊕ Fin r → K) = v := ⟨e.φ.symm ⟨v, hv⟩, by simp⟩
  rw [← hx, ← e.ext_spTransvection]
  exact hle ⟨_, rfl⟩

theorem exists_spPlaneDecomp_three [Finite K] (h3 : (3 : K) ≠ 0) {E : Subgroup (StatedSp r K)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) : SpPlaneDecomp 3 E := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨ℓ, hchar, n, hℓ, -⟩ := FiniteField.card' K
  have hpℓ : (3 : ℕ) ≠ ℓ := by
    rintro rfl
    exact h3 (by simpa using CharP.cast_eq_zero K 3)
  have hA : IsElementaryAbelian 3 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2
      ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, hexp⟩
  obtain ⟨h1, h2, h3', h4, h5, h6, h7⟩ := symplectic_plane_kernel_line_decomposition hℓ
    Nat.prime_three (by norm_num) hpℓ hA (by rw [hcard]; norm_num)
  exact ⟨h1, h2, h3', h4, h5, h6, h7⟩

theorem exists_ne_one_of_one_lt_card {G : Type*} [Group G] {M : Subgroup G}
    (h : 1 < Nat.card M) : ∃ t ∈ M, t ≠ 1 := by
  have : Finite M := Nat.finite_of_card_ne_zero (by omega)
  have hne : M ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot M).1 h
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  exact ⟨t, ht, fun h' => ht1 (Subtype.ext h')⟩

theorem spLineSpace_stable_of_comm {E : Subgroup (StatedSp r K)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {M : Subgroup ↥E} (y : ↥E)
    {s : Fin r ⊕ Fin r → K} (hs : s ∈ spLineSpace M) :
    spEnd (y : StatedSp r K) s ∈ spLineSpace M := by
  refine ⟨?_, ?_⟩
  · change spEnd (y : StatedSp r K) s ∈ CFSG.RankThree.Classical.fixSub (spRep E) M
    rw [CFSG.RankThree.Classical.mem_fixSub]
    intro d hd
    have h1 : spRep E d s = s := CFSG.RankThree.Classical.mem_fixSub.mp hs.1 d hd
    have h2 : spEnd (d : StatedSp r K) s = s := h1
    change spEnd (d : StatedSp r K) (spEnd (y : StatedSp r K) s) = spEnd (y : StatedSp r K) s
    rw [← Module.End.mul_apply, ← spEnd_mul, hcomm d d.2 y y.2, spEnd_mul, Module.End.mul_apply,
      h2]
  · rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hyu : spEnd (y : StatedSp r K) u = u :=
      CFSG.RankThree.Classical.mem_fixSub.mp hu y (Subgroup.mem_top y)
    have h3 := spRep_isometry E y u s
    change spForm r K (spEnd (y : StatedSp r K) u) (spEnd (y : StatedSp r K) s) = spForm r K u s
      at h3
    rw [hyu] at h3
    rw [h3]
    exact hs.2 u hu

theorem spEnd_eq_of_mem_spLineSpace {E : Subgroup (StatedSp r K)} {M : Subgroup ↥E} {d : ↥E}
    (hd : d ∈ M) {v : Fin r ⊕ Fin r → K} (hv : v ∈ spLineSpace M) :
    spEnd (d : StatedSp r K) v = v :=
  CFSG.RankThree.Classical.mem_fixSub.mp hv.1 d hd

end CFSG.LieType.SeitzGeneration.SpPlaneThree
