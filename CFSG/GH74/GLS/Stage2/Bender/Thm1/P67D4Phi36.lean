module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Phi36Plane
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Phi36Z0
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeX
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67InnerTools
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.RankThree.PartTwo.KFacts.AutKinds

public section

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.Chevalley

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem d4_false_of_phi36 {p f r : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrd : r ∣ (p ^ f) ^ 2 + p ^ f + 1 ∨ r ∣ (p ^ f) ^ 2 - p ^ f + 1)
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) r V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    (hinn : ∀ v ∈ V, v ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcen : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    mulAut_conj_injective_of_center_bot hcen
  obtain ⟨-, -, hVe, hVc, hZab, -, -, hZbot, hcomm⟩ := id h2
  have := hVe
  obtain ⟨E, hEe, hEc, hEV⟩ := exists_plane_of_inner hcen hVe hVc hinn
  have := hEe
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  obtain ⟨ε, d, hε, hd, hrd'⟩ : ∃ (ε : ℤ) (d : ℕ), (ε = 1 ∨ ε = -1) ∧
      (d : ℤ) = ((p ^ f : ℕ) : ℤ) ^ 2 + ε * (p ^ f : ℕ) + 1 ∧ r ∣ d := by
    rcases hrd with h | h
    · exact ⟨1, (p ^ f) ^ 2 + p ^ f + 1, Or.inl rfl, by push_cast; ring, h⟩
    · refine ⟨-1, (p ^ f) ^ 2 - p ^ f + 1, Or.inr rfl, ?_, h⟩
      have hle : p ^ f ≤ (p ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
      rw [Nat.cast_add, Nat.cast_sub hle]
      push_cast
      ring
  have hpd : (r : ℤ) ∣ ((p ^ f : ℕ) : ℤ) ^ 2 + ε * (p ^ f : ℕ) + 1 := by
    rw [← hd]
    exact_mod_cast hrd'
  have hr3 : 3 < r := by omega
  set Z₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Z.comap (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) with hZ₀
  have hZ₀mem : ∀ t, t ∈ Z₀ ↔ MulAut.conj t ∈ Z := fun t => Iff.rfl
  have hEv : ∀ e ∈ E, MulAut.conj e ∈ V := fun e he => by
    rw [← hEV]
    exact Subgroup.mem_map_of_mem _ he
  have hZc : ∀ t ∈ Z₀, ∀ e ∈ E, t * e = e * t := by
    intro t ht e he
    apply hinj
    rw [map_mul, map_mul]
    exact (hcomm _ (hEv e he) _ ((hZ₀mem t).1 ht)).symm
  have hZab₀ : ∀ a ∈ Z₀, ∀ b ∈ Z₀, a * b = b * a := by
    intro a ha b hb
    apply hinj
    rw [map_mul, map_mul]
    exact hZab _ ((hZ₀mem a).1 ha) _ ((hZ₀mem b).1 hb)
  have hnorm : ∀ x ∈ E, x ≠ 1 → ∀ s ∈ Subgroup.centralizer ({x} :
      Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      MulAut.conj s ∈ Subgroup.normalizer (Z : Set (MulAut (graphFixedRootGroup TwistTag.D4 K
        σ.toRingHom))) := by
    intro x hx hx1 s hs
    have hv1 : MulAut.conj x ≠ 1 := fun h => hx1 (hinj (by rw [h, map_one]))
    refine h3 _ (hEv x hx) hv1 s ?_
    rw [mem_fixSub, MulAut.conj_apply]
    have hxs : x * s = s * x := (Subgroup.mem_centralizer_singleton_iff.1 hs).symm
    calc x * s * x⁻¹ = s * x * x⁻¹ := by rw [hxs]
      _ = s := by group
  have hZn : ∀ x ∈ E, x ≠ 1 → ∀ s ∈ Subgroup.centralizer ({x} :
      Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), ∀ t ∈ Z₀, s * t * s⁻¹ ∈ Z₀ := by
    intro x hx hx1 s hs t ht
    have h := (Subgroup.mem_normalizer_iff.1 (hnorm x hx hx1 s hs) (MulAut.conj t)).1
      ((hZ₀mem t).1 ht)
    have e : (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (s * t * s⁻¹) =
        MulAut.conj s * MulAut.conj t * (MulAut.conj s)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hZ₀mem, e]
    exact h
  have hZ0 : ∀ t ∈ Z₀, t = 1 := d4_phi36_Z0_trivial hf K hK σ hσ hε hr hr3 hpd E hEe hEc Z₀ hZc
    hZab₀ hZn
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hZbot (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx))
  have hzout : z ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    rintro ⟨t, rfl⟩
    exact hz1 (by rw [hZ0 t hzZ, map_one])
  have hzE : ∀ e ∈ E, z e = e := by
    intro e he
    apply hinj
    rw [← mul_mulAutConj_mul_inv z e]
    have := hcomm _ (hEv e he) z hzZ
    rw [← this]
    group
  obtain ⟨x, hxE, hx1, hdata⟩ :=
    exists_singularData_of_plane hp hf K hK σ hσ hε hr hr3 hpd E hEe hEc
  have hzC : ∀ s ∈ Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      z s = s := by
    intro s hs
    have hmem : MulAut.conj s * z * (MulAut.conj s)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.1 (hnorm x hxE hx1 s hs) z).1 hzZ
    have hmem2 : MulAut.conj s * z * (MulAut.conj s)⁻¹ * z⁻¹ ∈ Z := Z.mul_mem hmem (Z.inv_mem hzZ)
    have e1 : MulAut.conj s * z * (MulAut.conj s)⁻¹ * z⁻¹ = MulAut.conj (s * (z s)⁻¹) := by
      have h := mul_mulAutConj_mul_inv z s
      calc MulAut.conj s * z * (MulAut.conj s)⁻¹ * z⁻¹ =
          MulAut.conj s * (z * (MulAut.conj s)⁻¹ * z⁻¹) := by group
        _ = MulAut.conj s * (z * MulAut.conj s * z⁻¹)⁻¹ := by group
        _ = MulAut.conj s * (MulAut.conj (z s))⁻¹ := by rw [h]
        _ = MulAut.conj (s * (z s)⁻¹) := by rw [map_mul, map_inv]
    rw [e1] at hmem2
    have h1 := hZ0 _ ((hZ₀mem _).2 hmem2)
    exact (mul_inv_eq_one.1 h1).symm
  have hzder : ∀ u ∈ ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)), Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom))⁆, z u = u := by
    intro u hu
    have hle : ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ ≤
        Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    exact hzC u (hle hu)
  obtain ⟨t3, ht3⟩ := pow_three_mem_range_of_fixes_singular hp hf K hK σ hσ hdata z hzder
  have ht3Z : t3 ∈ Z₀ := (hZ₀mem t3).2 (by rw [ht3]; exact Z.pow_mem hzZ 3)
  have hz3 : z ^ 3 = 1 := by rw [← ht3, hZ0 t3 ht3Z, map_one]
  exact phi36_false_of_outer_fixing_plane hf K hK σ hσ hε hr hr5 hpd E hEe hEc z hz3 hzout hzE

end CFSG.GH74.GLS.Stage2.Bender.Thm1
