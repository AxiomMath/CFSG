module

public import CFSG.LieType.Chevalley.IntrinsicSimplePairs
public import CFSG.LieType.Chevalley.RankOneFaithful

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem map_eq_of_intertwine {S G : Type*} [Group S] [Group G] {f f' : S →* G}
    (hf' : Function.Injective f') {β : MulAut G} {γ : MulAut S}
    (h : ∀ s, f' (γ s) = β (f s)) {A : Subgroup S}
    (hA : (A.map f).map β.toMonoidHom = A.map f') : A.map γ.toMonoidHom = A := by
  apply Subgroup.map_injective hf'
  rw [Subgroup.map_map, ← hA, Subgroup.map_map]
  congr 1
  ext s
  exact h s

section SL2

variable {K : Type*} [Field K]

theorem map_sl2RootX_id {L : Type*} [Group L] (ρ : SL(2, K) →* L) :
    (sl2RootX (MonoidHom.id (SL(2, K)))).map ρ = sl2RootX ρ := by
  ext x
  simp only [Subgroup.mem_map, mem_sl2RootX, MonoidHom.id_apply]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, rfl⟩

theorem map_sl2RootY_id {L : Type*} [Group L] (ρ : SL(2, K) →* L) :
    (sl2RootY (MonoidHom.id (SL(2, K)))).map ρ = sl2RootY ρ := by
  ext x
  simp only [Subgroup.mem_map, mem_sl2RootY, MonoidHom.id_apply]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, rfl⟩

end SL2

variable {τ : Tag} {K : Type} [Field K]

theorem rankOneRep_injective
    (hK : ringChar K ≠ 2) (i : Fin τ.rank) :
    Function.Injective (rankOneRep τ K i) := fun _ _ hgh =>
  (odd_Chevalley_simple_root_SL2_faithful τ K hK i).1
    ((adjointGroup τ K).subtype.comp (rankOneRep τ K i))
    (fun c => congrArg Subtype.val (rankOneRep_upper i c))
    (fun c => congrArg Subtype.val (rankOneRep_lower i c)) (congrArg Subtype.val hgh)

theorem exists_params_of_map_simple
    [Finite K] (hK : ringChar K ≠ 2)
    {β : MulAut (adjointGroup τ K)} {i k : Fin τ.rank}
    (hX : (simplePosSubgroup τ K i).map β.toMonoidHom = simplePosSubgroup τ K k)
    (hY : (simpleNegSubgroup τ K i).map β.toMonoidHom = simpleNegSubgroup τ K k) :
    ∃ p : Kˣ × (K ≃+* K), (∀ c, β (adjX τ K i c) = adjX τ K k (p.1 * p.2 c)) ∧
      (∀ c, β (adjY τ K i c) = adjY τ K k (((p.1⁻¹ : Kˣ) : K) * p.2 c)) ∧
      ∀ t, β (adjD τ K i t) = adjD τ K k (Units.map p.2.toMonoidHom t) := by
  have hL : (rankOneSubgroup (τ := τ) (K := K) i).map β.toMonoidHom =
      rankOneSubgroup (τ := τ) (K := K) k := by
    rw [rankOneSubgroup, rankOneSubgroup, Subgroup.map_sup, hX, hY]
  have hbij : ∀ l : Fin τ.rank, Function.Bijective (rankOneRepL τ K l) := fun l =>
    ⟨fun _ _ hgh => rankOneRep_injective hK l (congrArg Subtype.val hgh),
      rankOneRepL_surjective l⟩
  let ei := MulEquiv.ofBijective (rankOneRepL τ K i) (hbij i)
  let ek := MulEquiv.ofBijective (rankOneRepL τ K k) (hbij k)
  let γ : MulAut (SL(2, K)) :=
    (ei.trans ((β.subgroupMap _).trans (MulEquiv.subgroupCongr hL))).trans ek.symm
  have hγ : ∀ g, rankOneRep τ K k (γ g) = β (rankOneRep τ K i g) := fun g => by
    have h := congrArg Subtype.val (ek.apply_symm_apply
      (((β.subgroupMap _).trans (MulEquiv.subgroupCongr hL)) (ei g)))
    exact h
  have hρ : Function.Surjective (MonoidHom.id (SL(2, K))) := Function.surjective_id
  have hγmem : γ ∈ pairAutSubgroup (sl2RootX (MonoidHom.id (SL(2, K))))
      (sl2RootY (MonoidHom.id (SL(2, K)))) := by
    refine ⟨map_eq_of_intertwine (rankOneRep_injective hK k) hγ ?_,
      map_eq_of_intertwine (rankOneRep_injective hK k) hγ ?_⟩
    · rw [map_sl2RootX_id, map_sl2RootX_id, sl2RootX_rankOneRep, sl2RootX_rankOneRep, hX]
    · rw [map_sl2RootY_id, map_sl2RootY_id, sl2RootY_rankOneRep, sl2RootY_rankOneRep, hY]
  obtain ⟨p, ⟨hx, hy, hd⟩, -⟩ := (central_SL2_root_pair_semilinear_parameters
    (MonoidHom.id (SL(2, K))) hρ fun g hg => ⟨1, one_pow 2, by
      rw [MonoidHom.id_apply] at hg
      rw [hg, Units.val_one, one_smul]
      rfl⟩).1 γ hγmem
  refine ⟨p, fun c => ?_, fun c => ?_, fun t => ?_⟩
  · have := hx c
    simp only [MonoidHom.id_apply] at this
    rw [← rankOneRep_upper, ← hγ, this, rankOneRep_upper]
  · have := hy c
    simp only [MonoidHom.id_apply] at this
    rw [← rankOneRep_lower, ← hγ, this, rankOneRep_lower]
  · have := hd t
    simp only [MonoidHom.id_apply] at this
    rw [← rankOneRep_diag, ← hγ, this, rankOneRep_diag]

theorem params_unique_of_map_simple
    {β : MulAut (adjointGroup τ K)} {i k : Fin τ.rank}
    {p q : Kˣ × (K ≃+* K)} (hp : ∀ c, β (adjX τ K i c) = adjX τ K k (p.1 * p.2 c))
    (hq : ∀ c, β (adjX τ K i c) = adjX τ K k (q.1 * q.2 c)) : p = q := by
  have e : ∀ c, (p.1 : K) * p.2 c = q.1 * q.2 c := fun c =>
    adjX_injective k ((hp c).symm.trans (hq c))
  have h1 : p.1 = q.1 := Units.ext (by simpa using e 1)
  have h2 : p.2 = q.2 := RingEquiv.ext fun c => by
    have := e c
    rw [h1] at this
    exact mul_left_cancel₀ q.1.ne_zero this
  exact Prod.ext h1 h2

theorem torus_compat_of_params
    {β : MulAut (adjointGroup τ K)} {π : Equiv.Perm (Fin τ.rank)}
    {i j : Fin τ.rank} {a : Kˣ} {σi σj : K ≃+* K}
    (hx : ∀ c, β (adjX τ K j c) = adjX τ K (π j) (a * σj c))
    (hd : ∀ t, β (adjD τ K i t) = adjD τ K (π i) (Units.map σi.toMonoidHom t)) (t : Kˣ) :
    Units.map σj.toMonoidHom (t ^ τ.cartan i j) =
      Units.map σi.toMonoidHom t ^ τ.cartan (π i) (π j) := by
  have hconj : ∀ (i j : Fin τ.rank) (t : Kˣ) (c : K),
      adjD τ K i t * adjX τ K j c * (adjD τ K i t)⁻¹ =
        adjX τ K j (((t ^ τ.cartan i j : Kˣ) : K) * c) := fun i j t c =>
    Subtype.ext (simple_torus_root_conjugation τ K i j t c).1
  have h1 := congrArg β (hconj i j t 1)
  rw [map_mul, map_mul, map_inv, hd, hx, hconj, hx] at h1
  have h2 := adjX_injective _ h1
  rw [map_one, mul_one, mul_one, mul_comm] at h2
  refine Units.ext ?_
  rw [Units.coe_map]
  exact (mul_left_cancel₀ a.ne_zero h2).symm

theorem modEq_two_of_neg_one_zpow_eq (hK : ringChar K ≠ 2) {m n : ℤ}
    (h : (-1 : Kˣ) ^ m = (-1 : Kˣ) ^ n) : m ≡ n [ZMOD 2] := by
  have hne : (-1 : Kˣ) ≠ 1 := fun h1 =>
    hK (neg_one_eq_one_iff.1 (by simpa using congrArg Units.val h1))
  rcases Int.even_or_odd m with hm | hm <;> rcases Int.even_or_odd n with hn | hn
  · exact (Int.even_iff.1 hm).trans (Int.even_iff.1 hn).symm
  · rw [hm.neg_one_zpow, hn.neg_one_zpow] at h
    exact absurd h.symm hne
  · rw [hm.neg_one_zpow, hn.neg_one_zpow] at h
    exact absurd h hne
  · exact (Int.odd_iff.1 hm).trans (Int.odd_iff.1 hn).symm

theorem perm_eq_one_of_cartanF4_parity (π : Equiv.Perm (Fin Tag.F4.rank))
    (h : ∀ i j, Tag.F4.cartan i j ≡ Tag.F4.cartan (π i) (π j) [ZMOD 2]) : π = 1 := by
  have hodd : ∀ i j, Tag.F4.cartan i j % 2 = Tag.F4.cartan (π i) (π j) % 2 := h
  have hpair : ∀ a b : Fin Tag.F4.rank, Tag.F4.cartan a b % 2 = 1 →
      Tag.F4.cartan b a % 2 = 0 → a = ⟨1, by decide⟩ ∧ b = ⟨2, by decide⟩ := by decide
  obtain ⟨h1, h2⟩ := hpair (π ⟨1, by decide⟩) (π ⟨2, by decide⟩)
    ((hodd _ _).symm.trans (by decide)) ((hodd _ _).symm.trans (by decide))
  have hrow : ∀ b : Fin Tag.F4.rank, Tag.F4.cartan ⟨1, by decide⟩ b % 2 = 1 →
      b = ⟨0, by decide⟩ ∨ b = ⟨2, by decide⟩ := by decide
  have h0 : π ⟨0, by decide⟩ = ⟨0, by decide⟩ := by
    have e := hodd ⟨1, by decide⟩ ⟨0, by decide⟩
    rw [h1] at e
    rcases hrow _ (e.symm.trans (by decide)) with h0 | h0
    · exact h0
    · exact absurd (π.injective (h0.trans h2.symm)) (by decide)
  have hlast : ∀ c : Fin Tag.F4.rank, c ≠ ⟨0, by decide⟩ → c ≠ ⟨1, by decide⟩ →
      c ≠ ⟨2, by decide⟩ → c = ⟨3, by decide⟩ := by decide
  have h3 : π ⟨3, by decide⟩ = ⟨3, by decide⟩ :=
    hlast _ (fun e => absurd (π.injective (e.trans h0.symm)) (by decide))
      (fun e => absurd (π.injective (e.trans h1.symm)) (by decide))
      (fun e => absurd (π.injective (e.trans h2.symm)) (by decide))
  refine Equiv.ext fun x => ?_
  have hx : ∀ x : Fin Tag.F4.rank, x = ⟨0, by decide⟩ ∨ x = ⟨1, by decide⟩ ∨
      x = ⟨2, by decide⟩ ∨ x = ⟨3, by decide⟩ := by decide
  rcases hx x with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem odd_root_pair_permutation_torus_compatibility
    (τ : Tag) (K : Type) [Field K] [Finite K]
    (hK : ringChar K ≠ 2) {β : MulAut (adjointGroup τ K)} (hβ : β ∈ unipotentPairAut τ K) :
    (∃! π : Equiv.Perm (Fin τ.rank), ∀ i,
      (simplePosSubgroup τ K i).map β.toMonoidHom = simplePosSubgroup τ K (π i) ∧
      (simpleNegSubgroup τ K i).map β.toMonoidHom = simpleNegSubgroup τ K (π i)) ∧
    ∀ π : Equiv.Perm (Fin τ.rank), (∀ i,
      (simplePosSubgroup τ K i).map β.toMonoidHom = simplePosSubgroup τ K (π i) ∧
      (simpleNegSubgroup τ K i).map β.toMonoidHom = simpleNegSubgroup τ K (π i)) →
    (∀ i, ∃! p : Kˣ × (K ≃+* K),
      (∀ c, β (adjX τ K i c) = adjX τ K (π i) (p.1 * p.2 c)) ∧
      (∀ c, β (adjY τ K i c) = adjY τ K (π i) (((p.1⁻¹ : Kˣ) : K) * p.2 c)) ∧
      ∀ t, β (adjD τ K i t) = adjD τ K (π i) (Units.map p.2.toMonoidHom t)) ∧
    (∀ (a : Fin τ.rank → Kˣ) (σ : Fin τ.rank → K ≃+* K),
      (∀ i, (∀ c, β (adjX τ K i c) = adjX τ K (π i) (a i * σ i c)) ∧
        (∀ c, β (adjY τ K i c) = adjY τ K (π i) ((((a i)⁻¹ : Kˣ) : K) * σ i c)) ∧
        ∀ t, β (adjD τ K i t) = adjD τ K (π i) (Units.map (σ i).toMonoidHom t)) →
      ∀ (i j : Fin τ.rank) (t : Kˣ), Units.map (σ j).toMonoidHom (t ^ τ.cartan i j) =
        Units.map (σ i).toMonoidHom t ^ τ.cartan (π i) (π j)) ∧
    (∀ i j, τ.cartan i j ≡ τ.cartan (π i) (π j) [ZMOD 2]) ∧
    (τ = .F4 → π = 1) ∧
    (τ = .G2 → ringChar K ≠ 3 → π = 1) := by
  refine ⟨exists_unique_perm_map_simple hβ, fun π hπ => ?_⟩
  have hex : ∀ i, ∃ p : Kˣ × (K ≃+* K),
      (∀ c, β (adjX τ K i c) = adjX τ K (π i) (p.1 * p.2 c)) ∧
      (∀ c, β (adjY τ K i c) = adjY τ K (π i) (((p.1⁻¹ : Kˣ) : K) * p.2 c)) ∧
      ∀ t, β (adjD τ K i t) = adjD τ K (π i) (Units.map p.2.toMonoidHom t) := fun i =>
    exists_params_of_map_simple hK (hπ i).1 (hπ i).2
  choose p hp using hex
  have hcompat : ∀ (a : Fin τ.rank → Kˣ) (σ : Fin τ.rank → K ≃+* K),
      (∀ i, (∀ c, β (adjX τ K i c) = adjX τ K (π i) (a i * σ i c)) ∧
        (∀ c, β (adjY τ K i c) = adjY τ K (π i) ((((a i)⁻¹ : Kˣ) : K) * σ i c)) ∧
        ∀ t, β (adjD τ K i t) = adjD τ K (π i) (Units.map (σ i).toMonoidHom t)) →
      ∀ (i j : Fin τ.rank) (t : Kˣ), Units.map (σ j).toMonoidHom (t ^ τ.cartan i j) =
        Units.map (σ i).toMonoidHom t ^ τ.cartan (π i) (π j) := fun a σ h i j t =>
    torus_compat_of_params (h j).1 (h i).2.2 t
  have hcompat' := hcompat (fun i => (p i).1) (fun i => (p i).2) hp
  have hparity : ∀ i j, τ.cartan i j ≡ τ.cartan (π i) (π j) [ZMOD 2] := fun i j => by
    have hm : ∀ σ : K ≃+* K, Units.map σ.toMonoidHom (-1) = -1 := fun σ => Units.ext (by
      rw [Units.coe_map, Units.val_neg, Units.val_one]
      change σ (-1) = -1
      rw [map_neg, map_one])
    have h := hcompat' i j (-1)
    rw [map_zpow, hm, hm] at h
    exact modEq_two_of_neg_one_zpow_eq hK h
  refine ⟨fun i => ⟨p i, hp i, fun q hq => params_unique_of_map_simple hq.1 (hp i).1⟩,
    hcompat, hparity, fun hτ => ?_, fun hτ h3 => ?_⟩
  · subst hτ
    exact perm_eq_one_of_cartanF4_parity π hparity
  · subst hτ
    have hx : ∀ x : Fin Tag.G2.rank, x = ⟨0, by decide⟩ ∨ x = ⟨1, by decide⟩ := by decide
    have h0 : π ⟨0, by decide⟩ = ⟨0, by decide⟩ := by
      rcases hx (π ⟨0, by decide⟩) with h0 | h0
      · exact h0
      · exfalso
        have h1 : π ⟨1, by decide⟩ = ⟨0, by decide⟩ := by
          rcases hx (π ⟨1, by decide⟩) with h1 | h1
          · exact h1
          · exact absurd (π.injective (h1.trans h0.symm)) (by decide)
        have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
        have h := hcompat' ⟨0, by decide⟩ ⟨1, by decide⟩ (Units.mk0 2 h2)
        rw [h0, h1] at h
        have hc01 : Tag.G2.cartan ⟨0, by decide⟩ ⟨1, by decide⟩ = -1 := by decide
        have hc10 : Tag.G2.cartan ⟨1, by decide⟩ ⟨0, by decide⟩ = -3 := by decide
        have h' := congrArg Units.val h
        simp only [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0,
          RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, MonoidHom.coe_ofClass,
          map_zpow₀, map_ofNat] at h'
        rw [hc01, hc10, zpow_neg, zpow_neg, zpow_one, inv_inj] at h'
        have h6 : (2 : K) * 3 = 0 := by
          norm_num at h'
          linear_combination -h'
        have e3 : (3 : K) = 0 := (mul_eq_zero.1 h6).resolve_left h2
        exact h3 (CharP.ringChar_of_prime_eq_zero Nat.prime_three (by exact_mod_cast e3))
    have h1 : π ⟨1, by decide⟩ = ⟨1, by decide⟩ := by
      rcases hx (π ⟨1, by decide⟩) with h1 | h1
      · exact absurd (π.injective (h1.trans h0.symm)) (by decide)
      · exact h1
    refine Equiv.ext fun x => ?_
    rcases hx x with rfl | rfl
    exacts [h0, h1]

end CFSG.LieType.Chevalley
