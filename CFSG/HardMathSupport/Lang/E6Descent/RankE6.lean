module

public import CFSG.RankThree.PartOne.SLB4A.ClassExc
public import CFSG.Timmesfeld.Orders.ExceptionalTorus

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open TauCeti CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders

theorem exists_elemAbelian_of_hom {A G : Type*} [CommGroup A] [Group G] [Finite A]
    (Θ : A →* G) (T : Subgroup A) (hT : ∀ x ∈ T, x ^ 3 = 1) (k : ℕ)
    (hk : Nat.card Θ.ker ≤ k) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card T ≤ Nat.card E * k := by
  classical
  refine ⟨T.map Θ, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hT x hx, map_one]
  · let f : T →* G := Θ.comp T.subtype
    have hr : f.range = T.map Θ := by
      ext g
      simp [f, MonoidHom.mem_range, Subgroup.mem_map]
    have h1 : Nat.card T = Nat.card f.range * Nat.card f.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    have h2 : Nat.card f.ker ≤ Nat.card Θ.ker := by
      refine Nat.card_le_card_of_injective
        (fun x => (⟨(x.1 : A), by
          have := x.2
          rw [MonoidHom.mem_ker] at this ⊢
          simpa [f] using this⟩ : Θ.ker)) ?_
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val hxy
    rw [hr] at h1
    calc Nat.card T = Nat.card (T.map Θ) * Nat.card f.ker := h1
      _ ≤ Nat.card (T.map Θ) * k := Nat.mul_le_mul_left _ (h2.trans hk)

section Adjoint

variable {K : Type} [Field K] [Finite K]

theorem card_ker_zpowMatrix_cartan_E6_le :
    Nat.card (zpowMatrix (G := Kˣ) Tag.E6.cartan).ker ≤ 3 := by
  rw [card_ker_zpowMatrix_eq smithE6 smithE6P'_mul smithE6P_mul smithE6Q_mul,
    card_ker_zpowMatrix_diagonal]
  simp only [IsCyclic.card_powMonoidHom_ker, Nat.card_units]
  rw [show ∏ i : Fin Tag.E6.rank, (Nat.card K - 1).gcd (smithE6D i) =
      (Nat.card K - 1).gcd 3 by
    change ∏ i : Fin 6, (Nat.card K - 1).gcd (smithE6D i) = _
    simp [smithE6D, Fin.prod_univ_succ]]
  exact Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right _ _)

theorem exists_torsion_three_pi (h3 : 3 ∣ Nat.card K - 1) :
    ∃ T : Subgroup (Fin 6 → Kˣ), (∀ x ∈ T, x ^ 3 = 1) ∧ Nat.card T = 3 ^ 6 := by
  refine ⟨(zpowMatrix (G := Kˣ) (Matrix.diagonal fun _ : Fin 6 => ((3 : ℕ) : ℤ))).ker, ?_, ?_⟩
  · intro x hx
    funext j
    have h := congrFun ((MonoidHom.mem_ker).1 hx) j
    simp [zpowMatrix_apply, Matrix.diagonal_apply] at h
    simpa using h
  · rw [card_ker_zpowMatrix_diagonal (G := Kˣ) (fun _ : Fin 6 => 3)]
    simp only [IsCyclic.card_powMonoidHom_ker, Nat.card_units]
    rw [Nat.gcd_eq_right h3]
    simp

theorem exists_elemAbelian_243_adjointE6 (h3 : 3 ∣ Nat.card K - 1) :
    ∃ E : Subgroup (adjointGroup Tag.E6 K), IsElemAbelian 3 E ∧ 243 ≤ Nat.card E := by
  have hle : torusGroup Tag.E6 K ≤ adjointGroup Tag.E6 K :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨⟨i, t⟩, rfl⟩
      exact torusElt_mem_adjointGroup i t)
  let Θ : (Fin Tag.E6.rank → Kˣ) →* adjointGroup Tag.E6 K :=
    (Subgroup.inclusion hle).comp (torusCoordHom Tag.E6 K)
  have hker : Θ.ker = (zpowMatrix (G := Kˣ) Tag.E6.cartan).ker := by
    ext t
    simp only [MonoidHom.mem_ker, Θ, MonoidHom.comp_apply]
    rw [← torusCoordHom_eq_one_iff, ← Subgroup.inclusion_injective hle |>.eq_iff,
      map_one]
  obtain ⟨T, hT, hTc⟩ := exists_torsion_three_pi (K := K) h3
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_of_hom Θ T hT 3
    (hker ▸ card_ker_zpowMatrix_cartan_E6_le)
  refine ⟨E, hE, ?_⟩
  have h' : 3 ^ 6 ≤ Nat.card E * 3 := le_trans (le_of_eq hTc.symm) hcard
  omega

end Adjoint

theorem exists_elemAbelian_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (E : Subgroup H) (hE : IsElemAbelian 3 E) :
    ∃ E' : Subgroup G, IsElemAbelian 3 E' ∧ Nat.card E' = Nat.card E := by
  refine ⟨E.map e.symm.toMonoidHom, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  · exact Subgroup.card_map_of_injective e.symm.injective


theorem exists_elemAbelian_243_E6
    (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) (h3 : 3 ∣ q.card - 1) :
    ∃ E : Subgroup (CFSGIndex.lie ⟨.E6 q, hv⟩).Group, IsElemAbelian 3 E ∧ 243 ≤ Nat.card E := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.SLB4A.exists_equiv_adjointGroup
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6) q hv
  have h3K : 3 ∣ Nat.card K - 1 := hK ▸ h3
  obtain ⟨E, hE, hc⟩ := exists_elemAbelian_243_adjointE6 h3K
  obtain ⟨E', hE', hcard⟩ := exists_elemAbelian_of_mulEquiv e E hE
  exact ⟨E', hE', hcard ▸ hc⟩

theorem exists_elemAbelian_27_E6
    (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) (h3 : 3 ∣ q.card - 1) :
    ∃ E : Subgroup (CFSGIndex.lie ⟨.E6 q, hv⟩).Group, IsElemAbelian 3 E ∧ 27 ≤ Nat.card E := by
  obtain ⟨E, hE, hc⟩ := exists_elemAbelian_243_E6 q hv h3
  exact ⟨E, hE, by omega⟩

theorem three_pow_four_dvd_card_E6
    (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) (h3 : 3 ∣ q.card - 1) :
    3 ^ 4 ∣ Nat.card (CFSGIndex.lie ⟨.E6 q, hv⟩).Group := by
  obtain ⟨E, hE, hc⟩ := exists_elemAbelian_243_E6 q hv h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hp : IsPGroup 3 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 x.1 x.2⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hn5 : 5 ≤ n := by
    by_contra hlt
    have : n ≤ 4 := by omega
    have : 3 ^ n ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
    omega
  exact (Nat.pow_dvd_pow 3 (by omega : 4 ≤ n)).trans (hn ▸ Subgroup.card_subgroup_dvd_card E)

end CFSG.HardMathSupport.Lang.E6Descent
