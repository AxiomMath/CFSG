module

public import CFSG.LocalAnalysis.AGLEmbedding.CoverRankLift

public section

namespace CFSG.AGLEmbedding

open scoped commutatorElement

section General

variable {K X : Type} [Group K] [Group X]

theorem card_comap_of_ker_eq_center [Finite K] (π : K →* X) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (H : Subgroup X) :
    Nat.card (H.comap π) = Nat.card (Subgroup.center K) * Nat.card H := by
  have : Finite X := Finite.of_surjective π hπ
  have h1 := Subgroup.card_mul_index (H.comap π)
  rw [Subgroup.index_comap_of_surjective _ hπ] at h1
  have h2 := Subgroup.card_mul_index H
  have h3 : Nat.card K = Nat.card X * Nat.card (Subgroup.center K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, hker]
  have hi : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
  rw [h1, h3, ← h2]
  ring

theorem mem_normalizer_zpowers_of_conj_eq_pow [Finite X] {b h : X} {e : ℕ}
    (hh : h * b * h⁻¹ = b ^ e) : h ∈ Subgroup.normalizer (Subgroup.zpowers b : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (Subgroup.zpowers b).map (MulAut.conj h).toMonoidHom ≤ Subgroup.zpowers b := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    show MulAut.conj h b ∈ _
    rw [MulAut.conj_apply, hh]
    exact pow_mem (Subgroup.mem_zpowers b) e
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj h).injective).ge

theorem mul_card_le_card_of_lt_of_isPGroup [Finite K] {p : ℕ} (hp : p.Prime) {H L : Subgroup K}
    (hL : IsPGroup p L) (hHL : H < L) : p * Nat.card H ≤ Nat.card L := by
  have := Fact.mk hp
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHL.le
  obtain ⟨k, hk⟩ := hL.exists_card_eq
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hHL.ne (Subgroup.eq_of_le_of_card_ge hHL.le (by rw [hm, mul_one]))
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp (hk ▸ Dvd.intro_left _ hm.symm)
  have hj : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr fun h => hm1 (by rw [h, pow_zero])
  rw [hm, mul_comm]
  exact Nat.mul_le_mul_left _ ((pow_one p).symm.le.trans (Nat.pow_le_pow_right hp.pos hj))

theorem commute_of_map_mem_zpowers (π : K →* X) (hker : π.ker = Subgroup.center K) {w x y : K}
    (hy : π y ∈ Subgroup.zpowers (π w)) (hwx : Commute w x) : Commute y x := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h : ⁅y, x⁆ = ⁅w ^ m, x⁆ :=
    CoverCore.commutatorElement_eq_of_map_eq π hker (by rw [map_zpow, hm]) rfl
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hwx.zpow_left m).eq] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

theorem mul_comm_of_mem_comap_zpowers (π : K →* X) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (b : X) :
    ∀ x ∈ (Subgroup.zpowers b).comap π, ∀ y ∈ (Subgroup.zpowers b).comap π, x * y = y * x := by
  intro x hx y hy
  obtain ⟨w, rfl⟩ := hπ b
  exact commute_of_map_mem_zpowers π hker hx
    (commute_of_map_mem_zpowers π hker hy (Commute.refl w)).symm

end General

section Cover

variable {K X : Type} [Group K] [Group X] {p : ℕ} (D : ModuleSpec X p) (π : K →* X)

theorem ModuleSpec.mul_card_map_le_card_omegaOf [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (hZ1 : Subgroup.center K ≠ ⊥) (hZp : IsPGroup p (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K)) (hF : D.NoFun) {E : Subgroup K}
    (hEA : E ≤ D.span.comap π) (hZE : Subgroup.center K ≤ E)
    (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    p * Nat.card (E.map π) ≤ Nat.card (omegaOf E hE p) := by
  have := Fact.mk hp
  have hπZ : ∀ z ∈ Subgroup.center K, π z = 1 := fun z hz =>
    MonoidHom.mem_ker.mp (hker.symm ▸ hz)
  set A := omegaOf E hE p
  have hmap : A.map π = E.map π := by
    refine le_antisymm (Subgroup.map_mono omegaOf_le) ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hxz⟩ := D.exists_pow_eq_pow_of_noFun π hp hp2 hπ hker hZp hZc hF x (hEA hx)
    refine ⟨x * z⁻¹, ⟨mul_mem hx (hZE (inv_mem hz)), ?_⟩, ?_⟩
    · rw [(show Commute x z⁻¹ from Subgroup.mem_center_iff.mp (inv_mem hz) x).mul_pow, hxz,
        inv_pow, mul_inv_cancel]
    · rw [map_mul, hπZ _ (inv_mem hz), mul_one]
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Subgroup.center K, orderOf z₀ = p := by
    refine exists_prime_orderOf_dvd_card' p ?_
    rcases hZp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hZ1
    · exact h
  have hord : orderOf (z₀ : K) = p := (Subgroup.orderOf_coe z₀).trans hz₀
  have hz₀A : (z₀ : K) ∈ A := ⟨hZE z₀.2, hord ▸ pow_orderOf_eq_one _⟩
  have hkcard : p ≤ Nat.card (π.domRestrict A).ker := by
    have hmem : (⟨z₀, hz₀A⟩ : A) ∈ (π.domRestrict A).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply]
      exact hπZ _ z₀.2
    calc p = orderOf (⟨z₀, hz₀A⟩ : A) := by rw [Subgroup.orderOf_mk, hord]
      _ = Nat.card (Subgroup.zpowers (⟨z₀, hz₀A⟩ : A)) := (Nat.card_zpowers _).symm
      _ ≤ Nat.card (π.domRestrict A).ker :=
        Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hmem)
  have h1 := Subgroup.card_mul_index (π.domRestrict A).ker
  rw [Subgroup.index_ker, MonoidHom.domRestrict_range, hmap] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ hkcard

theorem ModuleSpec.card_le_mul_card_inf_centralizer [Finite K] (hp : p.Prime)
    (hker : π.ker = Subgroup.center K) (hZc : IsCyclic (Subgroup.center K)) {w : K}
    (hw : w ∈ D.span.comap π) :
    Nat.card (D.span.comap π) ≤
      p * Nat.card (D.span.comap π ⊓ Subgroup.centralizer ({w} : Set K) : Subgroup K) := by
  let ψ : D.span.comap π →* K :=
    { toFun := fun x => ⁅w, (x : K)⁆
      map_one' := by simp
      map_mul' := fun x y => by
        have hc := Subgroup.mem_center_iff.mp (D.commutator_mem_center π hker hw y.2) x
        simp only [Subgroup.coe_mul]
        rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc _ (x : K), hc, mul_assoc,
          mul_inv_cancel_right] }
  have hkerψ : ψ.ker =
      (D.span.comap π ⊓ Subgroup.centralizer ({w} : Set K)).subgroupOf (D.span.comap π) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    show ⁅w, (x : K)⁆ = 1 ↔ _
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h => ⟨x.2, h.symm⟩, fun h => h.2.symm⟩
  let W : Subgroup K := omegaOf (Subgroup.center K)
    (fun x hx y _ => (Subgroup.mem_center_iff.mp hx y).symm) p
  have hrange : ψ.range ≤ W := by
    rintro _ ⟨x, rfl⟩
    exact ⟨D.commutator_mem_center π hker hw x.2, D.commutator_pow_eq_one π hker hw x.2⟩
  have hW : Nat.card W ≤ p := by
    have := hZc
    have : IsCyclic W := Subgroup.isCyclic_of_le omegaOf_le
    refine Nat.le_of_dvd hp.pos ?_
    exact IsCyclic.exponent_eq_card (α := W) ▸
      Monoid.exponent_dvd_of_forall_pow_eq_one fun c => Subtype.ext c.2.2
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hkerψ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  rw [← h1, mul_comm p]
  exact Nat.mul_le_mul_left _ ((Subgroup.card_le_of_le hrange).trans hW)

theorem ModuleSpec.isPGroup_comap (hker : IsPGroup p π.ker) : IsPGroup p (D.span.comap π) := by
  refine IsPGroup.comap_of_ker_isPGroup (fun u => ⟨1, ?_⟩) π hker
  rw [pow_one]
  exact Subtype.ext (D.pow_eq_one_of_mem u.2)

theorem ModuleSpec.two_le_pRank_comap_zpowers [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (hZ1 : Subgroup.center K ≠ ⊥) (hZp : IsPGroup p (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K)) (hF : D.NoFun) {b : X} (hb : b ∈ D.span)
    (hb1 : b ≠ 1) : 2 ≤ Open.pRank p ((Subgroup.zpowers b).comap π) := by
  have := Fact.mk hp
  have hcomm := mul_comm_of_mem_comap_zpowers π hπ hker b
  refine le_pRank_of_pow_le_card (E := omegaOf _ hcomm p) hp omegaOf_le isElemAbelian_omegaOf ?_
  have h := D.mul_card_map_le_card_omegaOf π hp hp2 hπ hker hZ1 hZp hZc hF
    (Subgroup.comap_mono (Subgroup.zpowers_le.mpr hb)) (hker ▸ Subgroup.ker_le_comap π _) hcomm
  rwa [Subgroup.map_comap_eq_self_of_surjective hπ, Nat.card_zpowers,
    orderOf_eq_prime (D.pow_eq_one_of_mem hb) hb1, ← pow_two] at h

theorem ModuleSpec.exists_commute_not_mem_comap_zpowers [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (hZp : IsPGroup p (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (hn : 3 ≤ D.n ∨ (2 ≤ D.n ∧ D.NoAlt)) {b : X} (hb : b ∈ D.span) {w : K} (hw : π w = b) :
    ∃ x ∈ D.span.comap π, x ∉ (Subgroup.zpowers b).comap π ∧ Commute w x := by
  have := Fact.mk hp
  have hwA : w ∈ D.span.comap π := by rw [Subgroup.mem_comap, hw]; exact hb
  let C := D.span.comap π ⊓ Subgroup.centralizer ({w} : Set K)
  have hZ0 : 0 < Nat.card (Subgroup.center K) := Nat.card_pos
  have hQ : Nat.card ((Subgroup.zpowers b).comap π) ≤ Nat.card (Subgroup.center K) * p := by
    rw [card_comap_of_ker_eq_center π hπ hker, Nat.card_zpowers]
    exact Nat.mul_le_mul_left _ (Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one
      (D.pow_eq_one_of_mem hb)))
  have hÂ := D.card_comap π hp hπ hker
  have hC : Nat.card (Subgroup.center K) * p < Nat.card C := by
    rcases hn with hn | ⟨hn, hA⟩
    · have h1 := D.card_le_mul_card_inf_centralizer π hp hker hZc hwA
      rw [hÂ] at h1
      refine Nat.lt_of_mul_lt_mul_left (a := p) (lt_of_lt_of_le ?_ h1)
      calc p * (Nat.card (Subgroup.center K) * p)
          = Nat.card (Subgroup.center K) * p ^ 2 := by ring
        _ < Nat.card (Subgroup.center K) * p ^ D.n :=
          Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hp.one_lt (by omega)) hZ0
    · have hcomm := D.commute_of_noAlt π hp hp2 hπ hker hZp hZc hA
      have hCA : C = D.span.comap π :=
        inf_eq_left.mpr fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx w hwA)
      rw [hCA, hÂ]
      calc Nat.card (Subgroup.center K) * p = Nat.card (Subgroup.center K) * p ^ 1 := by ring
        _ < Nat.card (Subgroup.center K) * p ^ D.n :=
          Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hp.one_lt (by omega)) hZ0
  have hnot : ¬ C ≤ (Subgroup.zpowers b).comap π := fun h =>
    absurd ((Subgroup.card_le_of_le h).trans hQ) (not_le.mpr hC)
  obtain ⟨x, hxC, hxQ⟩ := Set.not_subset.mp hnot
  exact ⟨x, hxC.1, hxQ, (Subgroup.mem_centralizer_singleton_iff.mp hxC.2).symm⟩

theorem ModuleSpec.exists_commutative_overgroup [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (hZ1 : Subgroup.center K ≠ ⊥) (hZp : IsPGroup p (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K)) (hF : D.NoFun) (hn : 3 ≤ D.n ∨ (2 ≤ D.n ∧ D.NoAlt))
    {b : X} (hb : b ∈ D.span) (hb1 : b ≠ 1) :
    ∃ E : Subgroup K, (Subgroup.zpowers b).comap π ≤ E ∧ E ≤ D.span.comap π ∧
      IsMulCommutative E ∧ 3 ≤ Open.pRank p E := by
  have := Fact.mk hp
  set Q := (Subgroup.zpowers b).comap π
  obtain ⟨w, hw⟩ := hπ b
  obtain ⟨x, hxA, hxQ, hwx⟩ :=
    D.exists_commute_not_mem_comap_zpowers π hp hp2 hπ hker hZp hZc hn hb hw
  have hQA : Q ≤ D.span.comap π := Subgroup.comap_mono (Subgroup.zpowers_le.mpr hb)
  have hZQ : Subgroup.center K ≤ Q := hker ▸ Subgroup.ker_le_comap π _
  have hxy : ∀ y ∈ Q, Commute y x := fun y hy =>
    commute_of_map_mem_zpowers π hker (by rw [hw]; exact hy) hwx
  have hpair : (insert x (Q : Set K)).Pairwise Commute := by
    refine Set.pairwise_insert.mpr ⟨fun y hy z hz _ =>
      mul_comm_of_mem_comap_zpowers π hπ hker b y hy z hz,
      fun y hy _ => ⟨(hxy y hy).symm, hxy y hy⟩⟩
  set E := Subgroup.closure (insert x (Q : Set K))
  have hEc : IsMulCommutative E := Subgroup.isMulCommutative_closure hpair
  have hE : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val ((isMulCommutative_iff.mp hEc) ⟨u, hu⟩ ⟨v, hv⟩)
  have hQE : Q ≤ E := fun y hy => Subgroup.subset_closure (Set.mem_insert_of_mem x hy)
  have hxE : x ∈ E := Subgroup.subset_closure (Set.mem_insert x _)
  have hEA : E ≤ D.span.comap π := (Subgroup.closure_le _).mpr
    (Set.insert_subset hxA fun y hy => hQA hy)
  have hEp : IsPGroup p E := (D.isPGroup_comap π (hker ▸ hZp)).to_le hEA
  have hlt : p * Nat.card Q ≤ Nat.card E := mul_card_le_card_of_lt_of_isPGroup hp hEp
    (lt_of_le_of_ne hQE fun h => hxQ (show x ∈ Q by rw [h]; exact hxE))
  have hcardE : Nat.card E = Nat.card (Subgroup.center K) * Nat.card (E.map π) := by
    conv_lhs => rw [← Subgroup.comap_map_eq_self (hker ▸ hZQ.trans hQE : π.ker ≤ E)]
    exact card_comap_of_ker_eq_center π hπ hker _
  have hcardQ : Nat.card Q = Nat.card (Subgroup.center K) * p := by
    rw [card_comap_of_ker_eq_center π hπ hker, Nat.card_zpowers,
      orderOf_eq_prime (D.pow_eq_one_of_mem hb) hb1]
  have hmap : p ^ 2 ≤ Nat.card (E.map π) := by
    rw [hcardQ, hcardE] at hlt
    refine Nat.le_of_mul_le_mul_left (c := Nat.card (Subgroup.center K)) ?_ Nat.card_pos
    calc Nat.card (Subgroup.center K) * p ^ 2 = p * (Nat.card (Subgroup.center K) * p) := by ring
      _ ≤ _ := hlt
  refine ⟨E, hQE, hEA, hEc, le_pRank_of_pow_le_card (E := omegaOf E hE p) hp omegaOf_le
    isElemAbelian_omegaOf ?_⟩
  calc p ^ 3 = p * p ^ 2 := by ring
    _ ≤ p * Nat.card (E.map π) := Nat.mul_le_mul_left _ hmap
    _ ≤ _ := D.mul_card_map_le_card_omegaOf π hp hp2 hπ hker hZ1 hZp hZc hF hEA
        (hZQ.trans hQE) hE

end Cover

end CFSG.AGLEmbedding
