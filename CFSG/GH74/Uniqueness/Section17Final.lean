module

public import CFSG.GH74.Uniqueness.Section16Stmts
public import CFSG.GH74.Uniqueness.Section4Residual
public import CFSG.GH74.Uniqueness.Theorem1Final

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem oTwoIn_le (M : Subgroup X) : oTwoIn M ≤ M := Subgroup.map_subtype_le _

omit [Finite X] in
theorem oTwoIn_conj_mem (M : Subgroup X) {m : X} (hm : m ∈ M) {v : X} (hv : v ∈ oTwoIn M) :
    m * v * m⁻¹ ∈ oTwoIn M := by
  obtain ⟨v', hv', rfl⟩ := hv
  exact ⟨⟨m, hm⟩ * v' * ⟨m, hm⟩⁻¹,
    (pCore_normal (p := 2) (G := ↥M)).conj_mem v' hv' ⟨m, hm⟩, rfl⟩

omit [Finite X] in
theorem exists_mul_of_sup_eq {O D : Subgroup X} (hDn : ∀ d ∈ D, ∀ v ∈ O, d * v * d⁻¹ ∈ O)
    {m : X} (hm : m ∈ O ⊔ D) : ∃ v ∈ O, ∃ d ∈ D, m = v * d := by
  let S : Subgroup X :=
    { carrier := {m | ∃ v ∈ O, ∃ d ∈ D, m = v * d}
      mul_mem' := by
        rintro _ _ ⟨v, hv, d, hd, rfl⟩ ⟨v', hv', d', hd', rfl⟩
        refine ⟨v * (d * v' * d⁻¹), O.mul_mem hv (hDn d hd v' hv'), d * d', D.mul_mem hd hd', ?_⟩
        group
      one_mem' := ⟨1, O.one_mem, 1, D.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨v, hv, d, hd, rfl⟩
        refine ⟨d⁻¹ * v⁻¹ * d⁻¹⁻¹, ?_, d⁻¹, D.inv_mem hd, ?_⟩
        · exact hDn d⁻¹ (D.inv_mem hd) v⁻¹ (O.inv_mem hv)
        · group }
  have hle : O ⊔ D ≤ S := sup_le (fun v hv => ⟨v, hv, 1, D.one_mem, by simp⟩)
    (fun d hd => ⟨1, O.one_mem, d, hd, by simp⟩)
  exact hle hm

omit [Finite X] in
theorem exists_proj {O D : Subgroup X} (hDM : D ≤ M) (hOn : ∀ m ∈ M, ∀ v ∈ O, m * v * m⁻¹ ∈ O)
    (hsup : O ⊔ D = M) (hinf : O ⊓ D = ⊥) :
    ∃ π : ↥M →* ↥D, (∀ d : ↥D, π ⟨(d : X), hDM d.2⟩ = d) ∧
      ∀ m : ↥M, (m : X) * ((π m : ↥D) : X)⁻¹ ∈ O := by
  classical
  have hex : ∀ m : ↥M, ∃ d : ↥D, (m : X) * ((d : ↥D) : X)⁻¹ ∈ O := by
    intro m
    obtain ⟨v, hv, d, hd, hmd⟩ := exists_mul_of_sup_eq (O := O) (D := D)
      (fun d hd v hv => hOn d (hDM hd) v hv) (hsup ▸ m.2 : (m : X) ∈ O ⊔ D)
    refine ⟨⟨d, hd⟩, ?_⟩
    have : (m : X) * d⁻¹ = v := by rw [hmd]; group
    simpa [this] using hv
  have huniq : ∀ (m : ↥M) (d d' : ↥D), (m : X) * ((d : ↥D) : X)⁻¹ ∈ O →
      (m : X) * ((d' : ↥D) : X)⁻¹ ∈ O → d = d' := by
    intro m d d' h h'
    have h1 : ((d' : X) * (d : X)⁻¹) ∈ O := by
      have := O.mul_mem (O.inv_mem h') h
      have e : ((m : X) * (d' : X)⁻¹)⁻¹ * ((m : X) * (d : X)⁻¹) = (d' : X) * (d : X)⁻¹ := by group
      rwa [e] at this
    have h2 : ((d' : X) * (d : X)⁻¹) ∈ D := D.mul_mem d'.2 (D.inv_mem d.2)
    have h3 : ((d' : X) * (d : X)⁻¹) ∈ O ⊓ D := ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact Subtype.ext (mul_inv_eq_one.mp h3).symm
  let f : ↥M → ↥D := fun m => Classical.choose (hex m)
  have hf : ∀ m : ↥M, (m : X) * ((f m : ↥D) : X)⁻¹ ∈ O := fun m => Classical.choose_spec (hex m)
  refine ⟨
    { toFun := f
      map_one' := by
        refine huniq 1 _ 1 (hf 1) ?_
        simp
      map_mul' := by
        intro m m'
        refine huniq (m * m') _ _ (hf (m * m')) ?_
        have e : ((m * m' : ↥M) : X) * (((f m * f m' : ↥D) : ↥D) : X)⁻¹ =
            ((m : X) * ((m' : X) * ((f m' : ↥D) : X)⁻¹) * (m : X)⁻¹) *
              ((m : X) * ((f m : ↥D) : X)⁻¹) := by
          simp only [Subgroup.coe_mul, mul_inv_rev]
          group
        rw [e]
        exact O.mul_mem (hOn (m : X) m.2 _ (hf m')) (hf m) }, ?_, hf⟩
  intro d
  refine huniq _ _ d (hf _) ?_
  simp

omit [Finite X] in
theorem exists_odd_ne_one_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnc : ¬ ∀ a b : G, a * b = b * a) : ∃ x : G, Odd (orderOf x) ∧ x ≠ 1 := by
  by_contra hno
  push Not at hno
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 G := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card G = 2 ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := G)).ne' (fun {p} hp hpd => by
        have : Fact p.Prime := ⟨hp⟩
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpd
        by_contra hp2
        have hodd : Odd (orderOf x) := by
          rw [hx]; exact hp.odd_of_ne_two hp2
        have h1 : x = 1 := hno x hodd
        rw [h1, orderOf_one] at hx
        exact hp.one_lt.ne' hx.symm)⟩
    exact IsPGroup.of_card hk
  have : Group.IsNilpotent G := hp.isNilpotent
  have : Group.IsSolvable G := inferInstance
  exact hnc ((IsSimpleGroup.comm_iff_isSolvable (G := G)).mpr this)

theorem ZDSetup.false_of_oTwo_complement
    (S : ZDSetup X Z M) {D N : Subgroup X} {u : X}
    (hDM : D ≤ M) (hsup : oTwoIn M ⊔ D = M) (hinf : oTwoIn M ⊓ D = ⊥) (hND : N ≤ D)
    (hNn : (N.subgroupOf D).Normal) (hNodd : Odd (Nat.card N))
    (hk : ∃ k : ℕ, Nat.card D = Nat.card N * 2 ^ k) (huD : u ∈ D) (hu2 : orderOf u = 2) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπD, -⟩ := exists_proj (O := oTwoIn M) hDM
    (fun m hm v hv => oTwoIn_conj_mem M hm hv) hsup hinf
  obtain ⟨k, hk⟩ := hk
  have hQ : IsPGroup 2 (↥D ⧸ N.subgroupOf D) := by
    refine IsPGroup.of_card (n := k) ?_
    have h2 : Nat.card N = Nat.card (N.subgroupOf D) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hND).toEquiv.symm
    have h3 := Subgroup.card_mul_index (N.subgroupOf D)
    have hpos : 0 < Nat.card N := Nat.card_pos
    rw [← Subgroup.index_eq_card]
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc Nat.card N * (N.subgroupOf D).index
        = Nat.card (N.subgroupOf D) * (N.subgroupOf D).index := by rw [h2]
      _ = Nat.card ↥D := h3
      _ = Nat.card N * 2 ^ k := hk
  let φ : ↥M →* ↥D ⧸ N.subgroupOf D := (QuotientGroup.mk' (N.subgroupOf D)).comp π
  have huM : u ∈ M := hDM huD
  have huN : u ∉ N := CFSG.OddInversion.notMem_of_odd_card hNodd hu2
  have hu : u ∉ Subgroup.closure {y : X | y ∈ M ∧ Odd (orderOf y)} := by
    intro hmem
    have hle : Subgroup.closure {y : X | y ∈ M ∧ Odd (orderOf y)} ≤ φ.ker.map M.subtype := by
      rw [Subgroup.closure_le]
      rintro y ⟨hyM, hyodd⟩
      refine ⟨⟨y, hyM⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      by_contra hne
      have hd : 2 ∣ orderOf (φ ⟨y, hyM⟩) := hQ.dvd_orderOf hne
      have hd' : 2 ∣ orderOf y :=
        hd.trans ((orderOf_map_dvd φ ⟨y, hyM⟩).trans (by simp))
      exact (Nat.not_even_iff_odd.mpr hyodd) (even_iff_two_dvd.mpr hd')
    obtain ⟨m, hmker, hmu⟩ := hle hmem
    have hm : m = ⟨u, huM⟩ := Subtype.ext hmu
    rw [hm] at hmker
    have hmker' : (QuotientGroup.mk' (N.subgroupOf D)) (π ⟨u, huM⟩) = 1 := hmker
    rw [hπD ⟨u, huD⟩] at hmker'
    have h2 := (QuotientGroup.eq_one_iff (⟨u, huD⟩ : ↥D)).mp hmker'
    exact huN (Subgroup.mem_subgroupOf.mp h2)
  have hne := S.closure_odd_ne_top_of_not_mem huM hu
  have hsimp : IsSimpleGroup X := S.theorem1_unconditional.1
  have hN : (Subgroup.closure {y : X | Odd (orderOf y)}).Normal := closure_odd_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure {y : X | Odd (orderOf y)}) with hbot | htop
  · obtain ⟨t, ht, htM⟩ := S.exists_mem_not_mem
    obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
    have hnc : ¬ ∀ a b : X, a * b = b * a := by
      intro hall
      apply htM
      refine (S.prodDisc.2.2.1 z hz hzM t).mp ?_
      rw [hall t⁻¹ z, mul_assoc, inv_mul_cancel, mul_one]
      exact hzM
    obtain ⟨x, hxodd, hx1⟩ := exists_odd_ne_one_of_simple hnc
    have hxmem : x ∈ Subgroup.closure {y : X | Odd (orderOf y)} := Subgroup.subset_closure hxodd
    rw [hbot] at hxmem
    exact hx1 (Subgroup.mem_bot.mp hxmem)
  · exact hne htop

end CFSG.GH74.Uniqueness
