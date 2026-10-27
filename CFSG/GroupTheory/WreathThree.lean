module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.PGroup.OmegaComm
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.GroupTheory.WreathThree

open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def base (S : Subgroup G) (y : G) : Subgroup G :=
  S ⊔ S.map (MulAut.conj y).toMonoidHom ⊔ S.map (MulAut.conj (y ^ 2)).toMonoidHom

structure IsWreathThree (S : Subgroup G) (y : G) : Prop where
  isPGroup : IsPGroup 3 S
  isCyclic : IsCyclic S
  ne_bot : S ≠ ⊥
  comm : ∀ a ∈ base S y, ∀ b ∈ base S y, a * b = b * a
  card_base : Nat.card (base S y) = Nat.card S ^ 3
  pow_three_mem : y ^ 3 ∈ base S y

variable {S : Subgroup G} {y : G}

private abbrev conjS (S : Subgroup G) (y : G) : Subgroup G :=
  S.map (MulAut.conj y).toMonoidHom

private abbrev conjSq (S : Subgroup G) (y : G) : Subgroup G :=
  conjS S (y ^ 2)

private theorem le_base_left (S : Subgroup G) (y : G) : S ≤ base S y := by
  intro x hx
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)

private theorem conjS_le_base (S : Subgroup G) (y : G) : conjS S y ≤ base S y := by
  intro x hx
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hx)

private theorem conjSq_le_base (S : Subgroup G) (y : G) : conjSq S y ≤ base S y := by
  intro x hx
  exact Subgroup.mem_sup_right hx

private theorem map_conj_three_eq (h : IsWreathThree S y) :
    S.map (MulAut.conj (y ^ 3)).toMonoidHom = S := by
  have hfix : ∀ x ∈ S, MulAut.conj (y ^ 3) x = x := by
    intro x hx
    have hc := h.comm (y ^ 3) h.pow_three_mem x (le_base_left S y hx)
    simp only [MulAut.conj_apply]
    calc y ^ 3 * x * (y ^ 3)⁻¹ = x * y ^ 3 * (y ^ 3)⁻¹ := by rw [hc]
      _ = x := by group
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : (MulAut.conj (y ^ 3)) x ∈ S := by rw [hfix x hx]; exact hx
    simpa only [MulEquiv.coe_toMonoidHom] using hx'
  · intro x hx
    exact ⟨x, hx, by simpa only [MulEquiv.coe_toMonoidHom] using hfix x hx⟩

private theorem map_conjS_conj_eq (S : Subgroup G) (y : G) :
    (conjS S y).map (MulAut.conj y).toMonoidHom = conjSq S y := by
  rw [conjS, conjSq, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [show y * (y * x * y⁻¹) * y⁻¹ = y ^ 2 * x * (y ^ 2)⁻¹ by
    rw [pow_two]
    group]

private theorem map_conjSq_conj_eq (h : IsWreathThree S y) :
    (conjSq S y).map (MulAut.conj y).toMonoidHom = S := by
  have hcomp : (MulAut.conj y).toMonoidHom.comp (MulAut.conj (y ^ 2)).toMonoidHom =
      (MulAut.conj (y ^ 3)).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show y * (y ^ 2 * x * (y ^ 2)⁻¹) * y⁻¹ = y ^ 3 * x * (y ^ 3)⁻¹ by
      simp only [pow_succ, pow_two]
      group]
  rw [conjSq, conjS, Subgroup.map_map, hcomp, map_conj_three_eq h]

private theorem map_conj_base_eq (h : IsWreathThree S y) :
    (base S y).map (MulAut.conj y).toMonoidHom = base S y := by
  rw [base]
  change (S ⊔ conjS S y ⊔ conjSq S y).map (MulAut.conj y).toMonoidHom =
    S ⊔ conjS S y ⊔ conjSq S y
  rw [Subgroup.map_sup, Subgroup.map_sup]
  rw [show S.map (MulAut.conj y).toMonoidHom = conjS S y from rfl, map_conjS_conj_eq,
    map_conjSq_conj_eq h]
  ac_rfl

theorem mem_normalizer_base (h : IsWreathThree S y) :
    y ∈ Subgroup.normalizer (base S y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : MulAut.conj y x ∈ (base S y).map (MulAut.conj y).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rwa [map_conj_base_eq h] at hx'
  · intro hx
    have hx' : MulAut.conj y x ∈ (base S y).map (MulAut.conj y).toMonoidHom := by
      rwa [map_conj_base_eq h]
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hx'
    have hzx : z = x := (MulAut.conj y).injective hzy
    rwa [hzx] at hz

private theorem finite_of_isWreathThree (h : IsWreathThree S y) : Finite S := by
  obtain ⟨g, hg⟩ := h.isCyclic.exists_generator
  have hcard : Nat.card S = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  obtain ⟨k, hk⟩ := h.isPGroup g
  have hdvd : orderOf g ∣ 3 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  have hpos : 0 < Nat.card S := by
    rw [hcard]
    exact Nat.pos_of_dvd_of_pos hdvd (pow_pos (by norm_num : (0:ℕ) < 3) k)
  exact (Nat.card_ne_zero.mp hpos.ne').2

private theorem card_base_ne_zero (h : IsWreathThree S y) : Nat.card (base S y) ≠ 0 := by
  rw [h.card_base]
  haveI : Finite S := finite_of_isWreathThree h
  haveI : Nonempty S := ⟨1⟩
  exact pow_ne_zero 3 (Nat.card_pos (α := S)).ne'

private theorem finite_base (h : IsWreathThree S y) : Finite (base S y) :=
  (Nat.card_ne_zero.mp (card_base_ne_zero h)).2

private theorem isMulCommutative_base (h : IsWreathThree S y) :
    IsMulCommutative (base S y) :=
  IsMulCommutative.mk (Std.Commutative.mk fun a b =>
    Subtype.ext (h.comm (a : G) a.2 (b : G) b.2))

private noncomputable abbrev conjEquiv (S : Subgroup G) (g : G) : S ≃* conjS S g :=
  (MulEquiv.subgroupMap (MulAut.conj g) S : S ≃* conjS S g)

@[simp] private theorem conjEquiv_coe_apply (S : Subgroup G) (g : G) (x : S) :
    ((conjEquiv S g x : conjS S g) : G) = MulAut.conj g (x : G) := rfl

private noncomputable def coordF1 (h : IsWreathThree S y) : S →* base S y :=
  (Subgroup.subtype S).codRestrict (base S y) fun a => le_base_left S y a.2

private noncomputable def coordF2 (h : IsWreathThree S y) : S →* base S y :=
  (Subgroup.inclusion (conjS_le_base S y)).comp (conjEquiv S y).toMonoidHom

private noncomputable def coordF3 (h : IsWreathThree S y) : S →* base S y :=
  (Subgroup.inclusion (conjSq_le_base S y)).comp (conjEquiv S (y ^ 2)).toMonoidHom

private theorem coordF1_comm (h : IsWreathThree S y) (a b : S) :
    Commute (coordF1 h a) (coordF2 h b) :=
  Subtype.ext (h.comm (coordF1 h a) (coordF1 h a).2 (coordF2 h b) (coordF2 h b).2)

@[simp] private theorem coordF1_coe (h : IsWreathThree S y) (a : S) :
    ((coordF1 h a : base S y) : G) = (a : G) := rfl

@[simp] private theorem coordF2_coe (h : IsWreathThree S y) (b : S) :
    ((coordF2 h b : base S y) : G) = (conjEquiv S y b : G) := by
  dsimp [coordF2]
  rw [Subgroup.coe_inclusion, conjEquiv_coe_apply]
  rfl

@[simp] private theorem coordF3_coe (h : IsWreathThree S y) (c : S) :
    ((coordF3 h c : base S y) : G) = (conjEquiv S (y ^ 2) c : G) := by
  dsimp [coordF3]
  rw [Subgroup.coe_inclusion, conjEquiv_coe_apply]
  rfl

private noncomputable def coordHom (h : IsWreathThree S y) : (S × S) × S →* base S y :=
  let ψ : S × S →* base S y := MonoidHom.noncommCoprod (coordF1 h) (coordF2 h) (coordF1_comm h)
  MonoidHom.noncommCoprod ψ (coordF3 h) fun a b =>
    Subtype.ext (h.comm (ψ a) (ψ a).2 (coordF3 h b) (coordF3 h b).2)

private theorem coordHom_coe (h : IsWreathThree S y) (a b c : S) :
    ((coordHom h ((a, b), c) : base S y) : G) =
      (a : G) * (conjEquiv S y b : G) * (conjEquiv S (y ^ 2) c : G) := by
  change ((coordF1 h a : base S y) : G) * ((coordF2 h b : base S y) : G) *
      ((coordF3 h c : base S y) : G) = _
  rw [coordF1_coe, coordF2_coe, coordF3_coe]

private theorem conjS_le_normalizer (h : IsWreathThree S y) :
    conjS S y ≤ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb a ha
  have hc : b * a = a * b := h.comm b (conjS_le_base S y hb) a (le_base_left S y ha)
  rw [hc]
  simpa using ha

private theorem conjSq_le_normalizer_sup (h : IsWreathThree S y) :
    conjSq S y ≤ Subgroup.normalizer ((S ⊔ conjS S y : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro z hz x hx
  have hx' : x ∈ (S : Set G) * (conjS S y : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left S (conjS S y) (conjS_le_normalizer h)]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  have hza : z * a * z⁻¹ = a := by
    have hc := h.comm z (conjSq_le_base S y hz) a (le_base_left S y ha)
    rw [hc]
    simpa using ha
  have hzb : z * b * z⁻¹ = b := by
    have hc := h.comm z (conjSq_le_base S y hz) b (conjS_le_base S y hb)
    rw [hc]
    simpa using hb
  have hzab : z * (a * b) * z⁻¹ = a * b := by
    calc z * (a * b) * z⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) := by group
      _ = a * b := by rw [hza, hzb]
  rw [hzab]
  exact Subgroup.mul_mem_sup ha hb

private theorem coordHom_surjective (h : IsWreathThree S y) :
    Function.Surjective (coordHom h) := by
  intro x
  have hpair : (x : G) ∈ ((S ⊔ conjS S y : Subgroup G) : Set G) * (conjSq S y : Set G) := by
    have hset := Subgroup.coe_mul_of_right_le_normalizer_left (S ⊔ conjS S y) (conjSq S y)
      (conjSq_le_normalizer_sup h)
    rw [← hset]
    exact x.2
  obtain ⟨k, hk, c, hc, hkc⟩ := hpair
  have hk' : k ∈ (S : Set G) * (conjS S y : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left S (conjS S y) (conjS_le_normalizer h)]
    exact hk
  obtain ⟨a, ha, b, hb, hab⟩ := hk'
  obtain ⟨b', hb', hbval⟩ := Subgroup.mem_map.mp hb
  obtain ⟨c', hc', hcval⟩ := Subgroup.mem_map.mp hc
  refine ⟨((⟨a, ha⟩, ⟨b', hb'⟩), ⟨c', hc'⟩), ?_⟩
  ext
  rw [coordHom_coe]
  simp only [Subgroup.coe_inclusion, Subgroup.coe_subtype]
  rw [show (conjEquiv S y ⟨b', hb'⟩ : G) = b from hbval,
    show (conjEquiv S (y ^ 2) ⟨c', hc'⟩ : G) = c from hcval, ← hkc, ← hab]

private noncomputable def coordEquiv (h : IsWreathThree S y) : (S × S) × S ≃* base S y := by
  haveI : Finite S := finite_of_isWreathThree h
  haveI : Nonempty S := ⟨1⟩
  haveI : Finite (base S y) := finite_base h
  haveI : Fintype ((S × S) × S) := Fintype.ofFinite _
  haveI : Fintype (base S y) := Fintype.ofFinite _
  have hcard : Fintype.card ((S × S) × S) = Fintype.card (base S y) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_prod, Nat.card_prod,
      h.card_base]
    ring
  refine MulEquiv.ofBijective (coordHom h) ?_
  exact (Fintype.bijective_iff_surjective_and_card (coordHom h)).mpr
    ⟨coordHom_surjective h, hcard⟩

private theorem coordEquiv_coe (h : IsWreathThree S y) (a b c : S) :
    ((coordEquiv h ((a, b), c) : base S y) : G) =
      (a : G) * (conjEquiv S y b : G) * (conjEquiv S (y ^ 2) c : G) :=
  coordHom_coe h a b c

private def shiftAut (S : Subgroup G) : MulAut ((S × S) × S) where
  toFun x := ((x.2, x.1.1), x.1.2)
  invFun x := ((x.1.2, x.2), x.1.1)
  left_inv x := by rcases x with ⟨⟨a, b⟩, c⟩; rfl
  right_inv x := by rcases x with ⟨⟨a, b⟩, c⟩; rfl
  map_mul' x y := by rcases x with ⟨⟨a, b⟩, c⟩; rcases y with ⟨⟨a', b'⟩, c'⟩; rfl

private theorem shiftAut_apply (x : (S × S) × S) :
    shiftAut S x = ((x.2, x.1.1), x.1.2) := rfl

private theorem shiftAut_fixed_iff (x : (S × S) × S) :
    shiftAut S x = x ↔ ∃ t : S, x = ((t, t), t) := by
  rcases x with ⟨⟨a, b⟩, c⟩
  constructor
  · intro hx
    rw [shiftAut_apply] at hx
    simp only [Prod.mk.injEq] at hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    exact ⟨a, by rw [← h2, h1]⟩
  · rintro ⟨t, ht⟩
    rw [ht, shiftAut_apply]

private theorem conj_y_conj_y (x : G) :
    MulAut.conj y (MulAut.conj y x) = MulAut.conj (y ^ 2) x := by
  simp only [MulAut.conj_apply]
  rw [show y * (y * x * y⁻¹) * y⁻¹ = y ^ 2 * x * (y ^ 2)⁻¹ by
    rw [pow_two]
    group]

private theorem conj_y_conj_y_sq (h : IsWreathThree S y) {x : G} (hx : x ∈ base S y) :
    MulAut.conj y (MulAut.conj (y ^ 2) x) = x := by
  have hc := h.comm (y ^ 3) h.pow_three_mem x hx
  simp only [MulAut.conj_apply]
  calc y * (y ^ 2 * x * (y ^ 2)⁻¹) * y⁻¹ = y ^ 3 * x * (y ^ 3)⁻¹ := by
        simp only [pow_succ, pow_two]
        group
    _ = x := by rw [hc]; group

private theorem conj_y_sq_conj_y (h : IsWreathThree S y) {x : G} (hx : x ∈ base S y) :
    MulAut.conj (y ^ 2) (MulAut.conj y x) = x := by
  have hc := h.comm (y ^ 3) h.pow_three_mem x hx
  simp only [MulAut.conj_apply]
  calc y ^ 2 * (y * x * y⁻¹) * (y ^ 2)⁻¹ = y ^ 3 * x * (y ^ 3)⁻¹ := by
        simp only [pow_succ, pow_two]
        group
    _ = x := by rw [hc]; group

private theorem conj_y_coord (h : IsWreathThree S y) (x : (S × S) × S) :
    MulAut.conj y ((coordEquiv h x : base S y) : G) =
      ((coordEquiv h (shiftAut S x) : base S y) : G) := by
  rcases x with ⟨⟨a, b⟩, c⟩
  rw [coordEquiv_coe, coordEquiv_coe]
  simp only [shiftAut, MulAut.conj_apply]
  have h1 : y * (a : G) * y⁻¹ = (conjEquiv S y a : G) := rfl
  have h2 : y * (conjEquiv S y b : G) * y⁻¹ = (conjEquiv S (y ^ 2) b : G) := by
    rw [conjEquiv_coe_apply, conjEquiv_coe_apply]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc] using conj_y_conj_y (b : G)
  have h3 : y * (conjEquiv S (y ^ 2) c : G) * y⁻¹ = (c : G) := by
    have hc : (c : G) ∈ base S y := le_base_left S y c.2
    rw [conjEquiv_coe_apply]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc] using conj_y_conj_y_sq h hc
  have hcomm1 : Commute (conjEquiv S y a : G) (c : G) :=
    h.comm _ (conjS_le_base S y (conjEquiv S y a).2) _ (le_base_left S y c.2)
  have hcomm2 : Commute (conjEquiv S (y ^ 2) b : G) (c : G) :=
    h.comm _ (conjSq_le_base S y (conjEquiv S (y ^ 2) b).2) _ (le_base_left S y c.2)
  have hcomm3 : Commute ((conjEquiv S y a : G) * (conjEquiv S (y ^ 2) b : G)) (c : G) :=
    hcomm1.mul_left hcomm2
  calc y * ((a : G) * (conjEquiv S y b : G) * (conjEquiv S (y ^ 2) c : G)) * y⁻¹
      = (y * (a : G) * y⁻¹) * (y * (conjEquiv S y b : G) * y⁻¹) *
          (y * (conjEquiv S (y ^ 2) c : G) * y⁻¹) := by group
    _ = (conjEquiv S y a : G) * (conjEquiv S (y ^ 2) b : G) * (c : G) := by rw [h1, h2, h3]
    _ = (c : G) * (conjEquiv S y a : G) * (conjEquiv S (y ^ 2) b : G) := by
        rw [hcomm3.eq, mul_assoc]

private theorem mul_y_pow_three (h : IsWreathThree S y) {b : G} (hb : b ∈ base S y) :
    (b * y) ^ 3 = b * MulAut.conj y b * MulAut.conj (y ^ 2) b * y ^ 3 := by
  have hyb : y * b = MulAut.conj y b * y := by
    simp only [MulAut.conj_apply]
    group
  have hy2b : y ^ 2 * b = MulAut.conj (y ^ 2) b * y ^ 2 := by
    simp only [MulAut.conj_apply]
    group
  calc
    (b * y) ^ 3 = b * (y * b) * y * b * y := by
      rw [pow_succ, pow_two]
      group
    _ = b * (MulAut.conj y b * y) * y * b * y := by rw [hyb]
    _ = b * MulAut.conj y b * (y ^ 2 * b) * y := by
      simp only [pow_two]
      group
    _ = b * MulAut.conj y b * (MulAut.conj (y ^ 2) b * y ^ 2) * y := by rw [hy2b]
    _ = b * MulAut.conj y b * MulAut.conj (y ^ 2) b * y ^ 3 := by
      simp only [pow_succ, pow_two]
      group

private theorem y_mul_pow_three (h : IsWreathThree S y) {b : G} (hb : b ∈ base S y) :
    (y * b) ^ 3 = b * MulAut.conj y b * MulAut.conj (y ^ 2) b * y ^ 3 := by
  have hyb : y * b = MulAut.conj y b * y := by
    simp only [MulAut.conj_apply]
    group
  have hb' : MulAut.conj y b ∈ base S y :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_base h) b).mp hb
  have hcube := mul_y_pow_three h hb'
  rw [hyb, hcube]
  rw [conj_y_conj_y, conj_y_sq_conj_y h hb]
  have hb'' : MulAut.conj (y ^ 2) b ∈ base S y := by
    rw [← conj_y_conj_y]
    exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_base h) (MulAut.conj y b)).mp hb'
  have hcomm1 : Commute (MulAut.conj y b) b := h.comm _ hb' b hb
  have hcomm2 : Commute (MulAut.conj (y ^ 2) b) b := h.comm _ hb'' b hb
  have hcomm3 : Commute (MulAut.conj y b * MulAut.conj (y ^ 2) b) b :=
    hcomm1.mul_left hcomm2
  rw [show MulAut.conj y b * MulAut.conj (y ^ 2) b * b =
      b * MulAut.conj y b * MulAut.conj (y ^ 2) b by
    rw [hcomm3.eq, mul_assoc]]

private noncomputable def coordNorm (S : Subgroup G) (x : (S × S) × S) : (S × S) × S :=
  x * shiftAut S x * shiftAut S (shiftAut S x)

private theorem y_mul_pow_three_coord (h : IsWreathThree S y) [CommMonoid S]
    (x : (S × S) × S) :
    (y * ((coordEquiv h x : base S y) : G)) ^ 3 =
      ((coordEquiv h (coordNorm S x) : base S y) : G) * y ^ 3 := by
  have hb : ((coordEquiv h x : base S y) : G) ∈ base S y := (coordEquiv h x).2
  rw [y_mul_pow_three h hb]
  have h2 : MulAut.conj (y ^ 2) ((coordEquiv h x : base S y) : G) =
      ((coordEquiv h (shiftAut S (shiftAut S x)) : base S y) : G) := by
    rw [← conj_y_conj_y, conj_y_coord h x, conj_y_coord h (shiftAut S x)]
  rw [conj_y_coord h x, h2]
  have hmul : ((coordEquiv h (coordNorm S x) : base S y) : G) =
      ((coordEquiv h x : base S y) : G) *
      ((coordEquiv h (shiftAut S x) : base S y) : G) *
      ((coordEquiv h (shiftAut S (shiftAut S x)) : base S y) : G) := by
    rw [coordNorm, map_mul, map_mul]
    simp only [Subgroup.coe_mul]
  rw [hmul]

private theorem mul_y_pow_three_coord (h : IsWreathThree S y) [CommMonoid S]
    (x : (S × S) × S) :
    (((coordEquiv h x : base S y) : G) * y) ^ 3 =
      ((coordEquiv h (coordNorm S x) : base S y) : G) * y ^ 3 := by
  have hb : ((coordEquiv h x : base S y) : G) ∈ base S y := (coordEquiv h x).2
  rw [mul_y_pow_three h hb]
  have h2 : MulAut.conj (y ^ 2) ((coordEquiv h x : base S y) : G) =
      ((coordEquiv h (shiftAut S (shiftAut S x)) : base S y) : G) := by
    rw [← conj_y_conj_y, conj_y_coord h x, conj_y_coord h (shiftAut S x)]
  rw [conj_y_coord h x, h2]
  have hmul : ((coordEquiv h (coordNorm S x) : base S y) : G) =
      ((coordEquiv h x : base S y) : G) *
      ((coordEquiv h (shiftAut S x) : base S y) : G) *
      ((coordEquiv h (shiftAut S (shiftAut S x)) : base S y) : G) := by
    rw [coordNorm, map_mul, map_mul]
    simp only [Subgroup.coe_mul]
  rw [hmul]

theorem exists_mul_pow_three_eq_one (h : IsWreathThree S y) :
    ∃ s ∈ base S y, (y * s) ^ 3 = 1 := by
  haveI : Finite S := finite_of_isWreathThree h
  haveI : IsCyclic S := h.isCyclic
  letI : CommGroup S := IsCyclic.commGroup
  let e := coordEquiv h
  have hfix : MulAut.conj y (y ^ 3) = y ^ 3 := by
    simp only [MulAut.conj_apply]
    group
  let d : base S y := ⟨y ^ 3, h.pow_three_mem⟩
  have hd : ((d : base S y) : G) = y ^ 3 := rfl
  let x : (S × S) × S := e.symm d
  have hex : (e x : base S y) = d := MulEquiv.apply_symm_apply e d
  have hshift : shiftAut S x = x := by
    apply e.injective
    apply Subtype.ext
    rw [← conj_y_coord h x, hex, hd, hfix]
  obtain ⟨t, ht⟩ := (shiftAut_fixed_iff x).mp hshift
  have hy3 : y ^ 3 = ((e ((t, t), t) : base S y) : G) := by
    rw [← hd, ← hex, ← ht]
  refine ⟨(t⁻¹ : S), le_base_left S y (t⁻¹).2, ?_⟩
  let z : (S × S) × S := ((t⁻¹, 1), 1)
  have hz : ((e z : base S y) : G) = (t⁻¹ : G) := by
    rw [coordEquiv_coe]
    simp
  simp only [Subgroup.coe_inv]
  rw [← hz, y_mul_pow_three_coord h z]
  have hnorm : coordNorm S z = ((t⁻¹, t⁻¹), t⁻¹) := by
    rw [coordNorm]
    ext <;> simp [shiftAut_apply, z, mul_assoc]
  have hmul2 : ((e ((t⁻¹, t⁻¹), t⁻¹) : base S y) : G) * ((e ((t, t), t) : base S y) : G) =
      ((e (((t⁻¹, t⁻¹), t⁻¹) * ((t, t), t)) : base S y) : G) := by
    rw [map_mul]
    simp only [Subgroup.coe_mul]
  rw [hnorm, hy3, hmul2]
  have hone : ((t⁻¹, t⁻¹), t⁻¹) * ((t, t), t) = 1 := by
    ext <;> simp
  rw [hone, map_one]
  rfl

private theorem exists_mul_y_or_mul_y_sq (h : IsWreathThree S y) (hy : y ^ 3 = 1) {x : G}
    (hx : x ∈ base S y ⊔ Subgroup.zpowers y) (hxb : x ∉ base S y) :
    ∃ b ∈ base S y, x = b * y ∨ x = b * y ^ 2 := by
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (base S y : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_base h)
  have hx' : x ∈ (base S y : Set G) * (Subgroup.zpowers y : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (base S y) (Subgroup.zpowers y) hnorm]
    exact hx
  obtain ⟨b, hb, t, ht, hbt⟩ := hx'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht
  rw [← hk] at hbt
  have hk3 : y ^ k = y ^ (k % 3) := zpow_eq_zpow_emod k (by simpa using hy)
  rw [hk3] at hbt
  have hr0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hr3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0] at hbt
    simp at hbt
    exact absurd (hbt.symm ▸ hb) hxb
  · rw [h1] at hbt
    simp only [zpow_one] at hbt
    exact ⟨b, hb, Or.inl hbt.symm⟩
  · rw [h2] at hbt
    norm_num at hbt
    exact ⟨b, hb, Or.inr hbt.symm⟩

theorem not_mem_base (h : IsWreathThree S y) : y ∉ base S y := by
  intro hy
  haveI : Finite S := finite_of_isWreathThree h
  have hfix : ∀ x ∈ S, MulAut.conj y x = x := by
    intro x hx
    have hc := h.comm y hy x (le_base_left S y hx)
    simp only [MulAut.conj_apply]
    rw [hc]
    group
  have hS2 : conjS S y = S := by
    apply le_antisymm
    · rintro z hz
      obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hz
      have hfx : (MulEquiv.toMonoidHom (MulAut.conj y)) x = x := by
        simpa only [MulEquiv.coe_toMonoidHom] using hfix x hx
      rw [hfx] at hxval
      exact hxval ▸ hx
    · intro x hx
      exact ⟨x, hx, by
        simpa only [MulEquiv.coe_toMonoidHom] using hfix x hx⟩
  have hS3 : conjSq S y = S := by
    calc conjSq S y = (conjS S y).map (MulAut.conj y).toMonoidHom :=
          (map_conjS_conj_eq S y).symm
      _ = S.map (MulAut.conj y).toMonoidHom := by rw [hS2]
      _ = conjS S y := rfl
      _ = S := hS2
  have hbase : base S y = S := by
    rw [base]
    rw [show S.map (MulAut.conj y).toMonoidHom = S from hS2,
      show S.map (MulAut.conj (y ^ 2)).toMonoidHom = S from hS3]
    simp
  have hcard : Nat.card S ^ 3 = Nat.card S := by
    rw [← h.card_base, hbase]
  have h2 : 2 ≤ Nat.card S := by
    haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr h.ne_bot
    haveI : Fintype S := Fintype.ofFinite S
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hnpos : 0 < Nat.card S := by positivity
  have hsq : Nat.card S ^ 2 = 1 := by
    have h := hcard
    rw [show Nat.card S ^ 3 = Nat.card S ^ 2 * Nat.card S by ring] at h
    have h' : Nat.card S ^ 2 * Nat.card S = 1 * Nat.card S := by
      rw [one_mul]
      exact h
    exact Nat.mul_right_cancel hnpos h'
  nlinarith [hsq, h2]

theorem card_sup_zpowers [Finite G] (h : IsWreathThree S y) (hy : y ^ 3 = 1) :
    Nat.card (base S y ⊔ Subgroup.zpowers y : Subgroup G) = 3 * Nat.card (base S y) := by
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (base S y : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_base h)
  have hdisj : Disjoint (base S y) (Subgroup.zpowers y) := by
    rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_bot]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx.2
      have hk3 : y ^ k = y ^ (k % 3) := zpow_eq_zpow_emod k (by simpa using hy)
      have hr0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
      have hr3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
      have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · rw [h0] at hk3
        rw [hk3] at hk
        simpa using hk.symm
      · rw [h1] at hk3
        rw [hk3] at hk
        have hyB : y ∈ base S y := by
          have hyx : y = x := by simpa using hk
          exact hyx ▸ hx.1
        exact absurd hyB (not_mem_base h)
      · rw [h2] at hk3
        rw [hk3] at hk
        have hy2B : y ^ 2 ∈ base S y := by
          have hx2 : y ^ 2 = x := by simpa using hk
          exact hx2 ▸ hx.1
        have hsq : (y ^ 2) ^ 2 = y := by
          calc (y ^ 2) ^ 2 = y ^ (2 * 2) := by rw [pow_mul]
            _ = y ^ (3 + 1) := by norm_num
            _ = y ^ 3 * y ^ 1 := by rw [pow_add]
            _ = y := by rw [hy, one_mul, pow_one]
        have hyB : y ∈ base S y := by
          have h2B : (y ^ 2) ^ 2 ∈ base S y := (base S y).pow_mem hy2B 2
          rwa [hsq] at h2B
        exact absurd hyB (not_mem_base h)
    · exact bot_le
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (base S y) (Subgroup.zpowers y) hnorm hdisj
  rw [hcard]
  have hord : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply orderOf_eq_prime hy
    intro hy1
    exact not_mem_base h (hy1 ▸ (base S y).one_mem)
  rw [hord, Nat.mul_comm]

private def diagHom (S : Subgroup G) : S →* (S × S) × S where
  toFun a := ((a, a), a)
  map_one' := rfl
  map_mul' := by intro a b; rfl

private theorem diagHom_injective (S : Subgroup G) : Function.Injective (diagHom S) := by
  intro a b hab
  have h := congrArg (fun z : (S × S) × S => z.1.1) hab
  simpa [diagHom] using h

private noncomputable def diag (h : IsWreathThree S y) : S →* base S y :=
  (coordEquiv h).toMonoidHom.comp (diagHom S)

private theorem diag_injective (h : IsWreathThree S y) : Function.Injective (diag h) := by
  intro a b hab
  exact diagHom_injective S ((coordEquiv h).injective hab)

private theorem diag_eq_coord (h : IsWreathThree S y) (a : S) :
    (diag h a : base S y) = coordEquiv h ((a, a), a) := rfl

private theorem diag_range_eq (h : IsWreathThree S y) :
    (diag h).range.map (base S y).subtype =
      base S y ⊓ Subgroup.centralizer ({y} : Set G) := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hz
    obtain ⟨t, rfl⟩ := ha
    rw [← haz]
    constructor
    · exact (diag h t).2
    · change ((diag h t : base S y) : G) ∈ Subgroup.centralizer ({y} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfix : MulAut.conj y ((diag h t : base S y) : G) = ((diag h t : base S y) : G) := by
        rw [diag_eq_coord, conj_y_coord]
        congr 1
      have hzy : ((diag h t : base S y) : G) * y = y * ((diag h t : base S y) : G) := by
        simp only [MulAut.conj_apply] at hfix
        calc ((diag h t : base S y) : G) * y
            = (y * ((diag h t : base S y) : G) * y⁻¹) * y := by rw [hfix]
          _ = y * ((diag h t : base S y) : G) := by group
      exact hzy
  · rintro ⟨hzB, hzy⟩
    change z ∈ Subgroup.centralizer ({y} : Set G) at hzy
    rw [Subgroup.mem_centralizer_singleton_iff] at hzy
    have hfix : MulAut.conj y z = z := by
      simp only [MulAut.conj_apply]
      rw [← hzy]
      group
    let x : (S × S) × S := (coordEquiv h).symm ⟨z, hzB⟩
    have hx : (coordEquiv h x : base S y) = ⟨z, hzB⟩ := MulEquiv.apply_symm_apply _ _
    have hshift : shiftAut S x = x := by
      apply (coordEquiv h).injective
      apply Subtype.ext
      rw [← conj_y_coord h x, hx]
      exact hfix
    obtain ⟨t, ht⟩ := (shiftAut_fixed_iff x).mp hshift
    have hzdiag : (diag h t : base S y) = ⟨z, hzB⟩ := by
      rw [diag_eq_coord, ← hx, ht]
    have hmem : ((diag h t : base S y) : G) ∈
        Subgroup.map (base S y).subtype (diag h).range :=
      Subgroup.mem_map_of_mem (f := (base S y).subtype) (K := (diag h).range) ⟨t, rfl⟩
    rw [show ((diag h t : base S y) : G) = z from congrArg Subtype.val hzdiag] at hmem
    exact hmem

theorem exists_eq_mul_conj_mul_conj_sq_of_mem_inf_centralizer (h : IsWreathThree S y)
    (hy : y ^ 3 = 1) {x : G}
    (hx : x ∈ base S y ⊓ Subgroup.centralizer ({y} : Set G)) :
    ∃ a : S, x = (a : G) * MulAut.conj y (a : G) * MulAut.conj (y ^ 2) (a : G) := by
  have hx' : x ∈ (diag h).range.map (base S y).subtype := by
    rwa [diag_range_eq h]
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx'
  obtain ⟨t, ht⟩ := hz
  refine ⟨t, ?_⟩
  rw [← hzx, ← ht]
  change ((diag h t : base S y) : G) = _
  rw [diag_eq_coord, coordEquiv_coe]
  simp only [conjEquiv_coe_apply]

private theorem card_diag (h : IsWreathThree S y) :
    Nat.card ↥(base S y ⊓ Subgroup.centralizer ({y} : Set G)) = Nat.card S := by
  rw [← diag_range_eq h]
  rw [Subgroup.card_map_of_injective (base S y).subtype_injective]
  have h2 : Nat.card (diag h).range = Nat.card S :=
    (Nat.card_congr (Equiv.ofInjective (diag h) (diag_injective h))).symm
  exact h2

private theorem mem_centralizer_mul_y_iff (h : IsWreathThree S y) {b z : G}
    (hb : b ∈ base S y) (hz : z ∈ base S y) :
    z * (b * y) = (b * y) * z ↔ z * y = y * z := by
  constructor
  · intro hzy
    have h' : b * (z * y) = b * (y * z) := by
      calc b * (z * y) = (z * b) * y := by rw [h.comm z hz b hb]; group
        _ = z * (b * y) := by group
        _ = (b * y) * z := hzy
        _ = b * (y * z) := by group
    exact mul_left_cancel h'
  · intro hzy
    calc z * (b * y) = (z * b) * y := by group
      _ = (b * z) * y := by rw [h.comm z hz b hb]
      _ = b * (z * y) := by group
      _ = b * (y * z) := by rw [hzy]
      _ = (b * y) * z := by group

private theorem mem_centralizer_mul_y_sq_iff (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    {b z : G} (hb : b ∈ base S y) (hz : z ∈ base S y) :
    z * (b * y ^ 2) = (b * y ^ 2) * z ↔ z * y = y * z := by
  constructor
  · intro hzy
    have h' : b * (z * y ^ 2) = b * (y ^ 2 * z) := by
      calc b * (z * y ^ 2) = (z * b) * y ^ 2 := by rw [h.comm z hz b hb]; group
        _ = z * (b * y ^ 2) := by group
        _ = (b * y ^ 2) * z := hzy
        _ = b * (y ^ 2 * z) := by group
    have hzy2 : z * y ^ 2 = y ^ 2 * z := mul_left_cancel h'
    have h3 : y * (z * y ^ 2) * y = y * (y ^ 2 * z) * y := by rw [hzy2]
    have hleft : y * (z * y ^ 2) * y = y * z := by
      rw [show y * (z * y ^ 2) * y = y * z * y ^ 3 by
        simp only [pow_succ, pow_two]; group]
      rw [hy, mul_one]
    have hright : y * (y ^ 2 * z) * y = z * y := by
      rw [show y * (y ^ 2 * z) * y = y ^ 3 * z * y by
        simp only [pow_succ, pow_two]; group]
      rw [hy, one_mul]
    rw [hleft, hright] at h3
    exact h3.symm
  · intro hzy
    have hzy2 : z * y ^ 2 = y ^ 2 * z := by
      calc z * y ^ 2 = (z * y) * y := by rw [pow_two]; group
        _ = (y * z) * y := by rw [hzy]
        _ = y * (z * y) := by group
        _ = y * (y * z) := by rw [hzy]
        _ = y ^ 2 * z := by rw [pow_two]; group
    calc z * (b * y ^ 2) = (z * b) * y ^ 2 := by group
      _ = (b * z) * y ^ 2 := by rw [h.comm z hz b hb]
      _ = b * (z * y ^ 2) := by group
      _ = b * (y ^ 2 * z) := by rw [hzy2]
      _ = (b * y ^ 2) * z := by group

private theorem inf_centralizer_eq_diag (h : IsWreathThree S y) (hy : y ^ 3 = 1) {x : G}
    (hx : x ∈ base S y ⊔ Subgroup.zpowers y) (hxb : x ∉ base S y) :
    base S y ⊓ Subgroup.centralizer ({x} : Set G) =
      base S y ⊓ Subgroup.centralizer ({y} : Set G) := by
  obtain ⟨b, hb, hxy | hxy⟩ := exists_mul_y_or_mul_y_sq h hy hx hxb
  · rw [hxy]
    ext z
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hzB, hzx⟩
      exact ⟨hzB, (mem_centralizer_mul_y_iff h hb hzB).mp hzx⟩
    · rintro ⟨hzB, hzy⟩
      exact ⟨hzB, (mem_centralizer_mul_y_iff h hb hzB).mpr hzy⟩
  · rw [hxy]
    ext z
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hzB, hzx⟩
      exact ⟨hzB, (mem_centralizer_mul_y_sq_iff h hy hb hzB).mp hzx⟩
    · rintro ⟨hzB, hzy⟩
      exact ⟨hzB, (mem_centralizer_mul_y_sq_iff h hy hb hzB).mpr hzy⟩

theorem card_base_inf_centralizer [Finite G] (h : IsWreathThree S y) (hy : y ^ 3 = 1) {x : G}
    (hx : x ∈ base S y ⊔ Subgroup.zpowers y) (hxb : x ∉ base S y) :
    Nat.card ↥(base S y ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card S := by
  rw [inf_centralizer_eq_diag h hy hx hxb, card_diag h]

private theorem false_of_forall_conj_y_fix (h : IsWreathThree S y)
    (hfix : ∀ z ∈ base S y, MulAut.conj y z = z) : False := by
  haveI : Finite S := finite_of_isWreathThree h
  have hS2 : conjS S y = S := by
    apply le_antisymm
    · rintro z hz
      obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hz
      have hfa : (MulEquiv.toMonoidHom (MulAut.conj y)) a = a := by
        simpa only [MulEquiv.coe_toMonoidHom] using hfix a (le_base_left S y ha)
      rw [hfa] at haz
      exact haz ▸ ha
    · intro a ha
      exact ⟨a, ha, by
        simpa only [MulEquiv.coe_toMonoidHom] using hfix a (le_base_left S y ha)⟩
  have hS3 : conjSq S y = S := by
    calc conjSq S y = (conjS S y).map (MulAut.conj y).toMonoidHom :=
          (map_conjS_conj_eq S y).symm
      _ = S.map (MulAut.conj y).toMonoidHom := by rw [hS2]
      _ = conjS S y := rfl
      _ = S := hS2
  have hbase : base S y = S := by
    rw [base]
    rw [show S.map (MulAut.conj y).toMonoidHom = S from hS2,
      show S.map (MulAut.conj (y ^ 2)).toMonoidHom = S from hS3]
    simp
  have hcard : Nat.card S ^ 3 = Nat.card S := by
    rw [← h.card_base, hbase]
  have h2 : 2 ≤ Nat.card S := by
    haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr h.ne_bot
    haveI : Fintype S := Fintype.ofFinite S
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hnpos : 0 < Nat.card S := by positivity
  have hsq : Nat.card S ^ 2 = 1 := by
    have h := hcard
    rw [show Nat.card S ^ 3 = Nat.card S ^ 2 * Nat.card S by ring] at h
    have h' : Nat.card S ^ 2 * Nat.card S = 1 * Nat.card S := by
      rw [one_mul]
      exact h
    exact Nat.mul_right_cancel hnpos h'
  nlinarith [hsq, h2]

private theorem not_forall_conj_y_sq_fix (h : IsWreathThree S y) :
    ¬ ∀ z ∈ base S y, MulAut.conj (y ^ 2) z = z := by
  intro hfix2
  apply false_of_forall_conj_y_fix h
  intro z hz
  calc MulAut.conj y z = MulAut.conj y (MulAut.conj (y ^ 2) z) := by rw [hfix2 z hz]
    _ = z := conj_y_conj_y_sq h hz

theorem center_eq [Finite G] (h : IsWreathThree S y) (hy : y ^ 3 = 1) :
    (base S y ⊔ Subgroup.zpowers y) ⊓ Subgroup.centralizer
        ((base S y ⊔ Subgroup.zpowers y : Subgroup G) : Set G) =
      base S y ⊓ Subgroup.centralizer ({y} : Set G) := by
  apply le_antisymm
  · intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨hzP, hzC⟩ := hz
    rw [Subgroup.mem_inf]
    constructor
    · by_contra hzB
      obtain ⟨b, hb, hxy | hxy⟩ := exists_mul_y_or_mul_y_sq h hy hzP hzB
      · have hfix : ∀ w ∈ base S y, MulAut.conj y w = w := by
          intro w hw
          have hzw : MulAut.conj z w = w := by
            have hcw : w * z = z * w :=
              (Subgroup.mem_centralizer_iff.mp hzC) w (Subgroup.mem_sup_left hw)
            simp only [MulAut.conj_apply]
            rw [← hcw]
            group
          have hywB : MulAut.conj y w ∈ base S y :=
            (Subgroup.mem_normalizer_iff.mp (mem_normalizer_base h) w).mp hw
          have hbw : b * (MulAut.conj y w) * b⁻¹ = MulAut.conj y w := by
            have hc := h.comm b hb _ hywB
            rw [hc]
            group
          have hz_eq : MulAut.conj (b * y) w = MulAut.conj y w := by
            simp only [MulAut.conj_apply]
            rw [show b * y * w * (b * y)⁻¹ = b * (y * w * y⁻¹) * b⁻¹ by group]
            simpa only [MulAut.conj_apply] using hbw
          have hzw' : MulAut.conj (b * y) w = w := by
            rwa [hxy] at hzw
          rw [hz_eq] at hzw'
          exact hzw'
        exact false_of_forall_conj_y_fix h hfix
      · have hfix : ∀ w ∈ base S y, MulAut.conj (y ^ 2) w = w := by
          intro w hw
          have hzw : MulAut.conj z w = w := by
            have hcw : w * z = z * w :=
              (Subgroup.mem_centralizer_iff.mp hzC) w (Subgroup.mem_sup_left hw)
            simp only [MulAut.conj_apply]
            rw [← hcw]
            group
          have hywB : MulAut.conj (y ^ 2) w ∈ base S y := by
            rw [← conj_y_conj_y]
            exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_base h)
              (MulAut.conj y w)).mp
              ((Subgroup.mem_normalizer_iff.mp (mem_normalizer_base h) w).mp hw)
          have hbw : b * (MulAut.conj (y ^ 2) w) * b⁻¹ = MulAut.conj (y ^ 2) w := by
            have hc := h.comm b hb _ hywB
            rw [hc]
            group
          have hz_eq : MulAut.conj (b * y ^ 2) w = MulAut.conj (y ^ 2) w := by
            simp only [MulAut.conj_apply]
            rw [show b * y ^ 2 * w * (b * y ^ 2)⁻¹ =
              b * (y ^ 2 * w * (y ^ 2)⁻¹) * b⁻¹ by group]
            simpa only [MulAut.conj_apply] using hbw
          have hzw' : MulAut.conj (b * y ^ 2) w = w := by
            rwa [hxy] at hzw
          rw [hz_eq] at hzw'
          exact hzw'
        exact not_forall_conj_y_sq_fix h hfix
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hyP : y ∈ (base S y ⊔ Subgroup.zpowers y : Subgroup G) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      have hcy : y * z = z * y := (Subgroup.mem_centralizer_iff.mp hzC) y hyP
      exact hcy.symm
  · intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨hzB, hzy⟩ := hz
    change z ∈ Subgroup.centralizer ({y} : Set G) at hzy
    rw [Subgroup.mem_centralizer_singleton_iff] at hzy
    rw [Subgroup.mem_inf]
    constructor
    · exact Subgroup.mem_sup_left hzB
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hsub : (base S y ⊔ Subgroup.zpowers y : Subgroup G) ≤
          Subgroup.centralizer ({z} : Set G) := by
        apply sup_le
        · intro b hb
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact h.comm b hb z hzB
        · apply Subgroup.zpowers_le.mpr
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hzy.symm
      have hwC : w ∈ Subgroup.centralizer ({z} : Set G) := hsub hw
      have hcw : w * z = z * w := Subgroup.mem_centralizer_singleton_iff.mp hwC
      exact hcw

private theorem exists_conj_eq_of_mul_y (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    {b : G} (hb : b ∈ base S y) (hcube : (b * y) ^ 3 = 1) :
    ∃ c ∈ base S y, c * (b * y) * c⁻¹ = y ∨ c * (b * y) * c⁻¹ = y⁻¹ := by
  haveI : Finite S := finite_of_isWreathThree h
  haveI : IsCyclic S := h.isCyclic
  letI : CommGroup S := IsCyclic.commGroup
  let e := coordEquiv h
  let x0 : (S × S) × S := e.symm ⟨b, hb⟩
  have hx0 : ((e x0 : base S y) : G) = b := by simp [x0]
  have hcube' := mul_y_pow_three_coord h x0
  rw [hx0, hcube, hy, mul_one] at hcube'
  have hN : coordNorm S x0 = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_one]
    exact hcube'.symm
  rcases x0 with ⟨⟨u, v⟩, w⟩
  have huvw : u * v * w = 1 := by
    have h := congrArg (fun z : (S × S) × S => z.1.1) hN
    rw [coordNorm] at h
    simpa [shiftAut_apply, mul_assoc, mul_comm, mul_left_comm] using h
  have huvinv : u⁻¹ * v⁻¹ = w := by
    have huv : u * v = w⁻¹ := by
      calc u * v = (u * v * w) * w⁻¹ := by group
        _ = 1 * w⁻¹ := by rw [huvw]
        _ = w⁻¹ := by rw [one_mul]
    have h1 : u⁻¹ * v⁻¹ = (u * v)⁻¹ := by
      rw [mul_inv_rev, mul_comm]
    rw [h1, huv, inv_inv]
  let xc : (S × S) × S := ((1, v), u⁻¹)
  let c : base S y := e xc
  have hcoord : xc * (shiftAut S xc)⁻¹ = ((u, v), w) := by
    rw [show xc = ((1, v), u⁻¹) from rfl]
    ext <;> simp [shiftAut_apply, huvinv, mul_assoc, mul_comm, mul_left_comm]
  have hcalc : ((e (xc * (shiftAut S xc)⁻¹) : base S y) : G) =
      ((e xc : base S y) : G) * ((e (shiftAut S xc) : base S y) : G)⁻¹ := by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hconj : MulAut.conj y (c : G) = ((e (shiftAut S xc) : base S y) : G) :=
    conj_y_coord h xc
  have hc_eq : ((c : base S y) : G) * (MulAut.conj y (c : G))⁻¹ = b := by
    rw [hconj, ← hcalc, hcoord, hx0]
  have hcy : (c : G) * y * (c : G)⁻¹ = b * y := by
    calc (c : G) * y * (c : G)⁻¹
        = ((c : G) * (MulAut.conj y (c : G))⁻¹) * y := by
          simp only [MulAut.conj_apply]
          group
      _ = b * y := by rw [hc_eq]
  refine ⟨(c : base S y)⁻¹, (c⁻¹).2, Or.inl ?_⟩
  have h' := congrArg (fun z => (c : G)⁻¹ * z * c) hcy
  have hleft : (c : G)⁻¹ * ((c : G) * y * (c : G)⁻¹) * c = y := by group
  rw [hleft] at h'
  simpa only [Subgroup.coe_inv, inv_inv] using h'.symm

theorem exists_conj_eq_of_pow_three [Finite G] (h : IsWreathThree S y) (hy : y ^ 3 = 1) {x : G}
    (hx : x ∈ base S y ⊔ Subgroup.zpowers y) (hxb : x ∉ base S y) (hx3 : x ^ 3 = 1) :
    ∃ c ∈ base S y, c * x * c⁻¹ = y ∨ c * x * c⁻¹ = y⁻¹ := by
  obtain ⟨b, hb, hxy | hxy⟩ := exists_mul_y_or_mul_y_sq h hy hx hxb
  · obtain ⟨c, hc, hconj⟩ := exists_conj_eq_of_mul_y h hy hb (by rwa [hxy] at hx3)
    exact ⟨c, hc, by simpa [hxy] using hconj⟩
  · have hb' : MulAut.conj y b⁻¹ ∈ base S y :=
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_base h) b⁻¹).mp
        ((base S y).inv_mem hb)
    have hy2inv : (y ^ 2)⁻¹ = y := by
      have h2 : y ^ 2 = y⁻¹ := by
        calc y ^ 2 = y ^ 3 * y⁻¹ := by group
          _ = y⁻¹ := by rw [hy, one_mul]
      rw [h2, inv_inv]
    have hxinv : x⁻¹ = MulAut.conj y b⁻¹ * y := by
      rw [hxy, mul_inv_rev, hy2inv]
      simp only [MulAut.conj_apply]
      group
    have hxinv3 : (MulAut.conj y b⁻¹ * y) ^ 3 = 1 := by
      rw [← hxinv, show x⁻¹ ^ 3 = (x ^ 3)⁻¹ by group, hx3, inv_one]
    obtain ⟨c, hc, hconj⟩ := exists_conj_eq_of_mul_y h hy hb' hxinv3
    rw [← hxinv] at hconj
    refine ⟨c, hc, ?_⟩
    rcases hconj with hcy | hcy
    · right
      have h' := congrArg (fun z => z⁻¹) hcy
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using h'
    · left
      have h' := congrArg (fun z => z⁻¹) hcy
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using h'

private noncomputable def kerPowEquiv (h : IsWreathThree S y)
    (hcS : ∀ a b : S, a * b = b * a)
    (hcB : ∀ a b : base S y, a * b = b * a) :
    CFSG.omega₁ (base S y) (p := 3) ≃
      ((CFSG.omega₁ S (p := 3) × CFSG.omega₁ S (p := 3)) × CFSG.omega₁ S (p := 3)) where
  toFun x := by
    let z : (S × S) × S := (coordEquiv h).symm (x : base S y)
    have hx3 : ((x : base S y) : base S y) ^ 3 = 1 :=
      (CFSG.mem_omega₁_iff_of_comm (p := 3) hcB).mp x.2
    have hz : z ^ 3 = 1 := by
      apply (coordEquiv h).injective
      rw [map_pow, map_one, MulEquiv.apply_symm_apply]
      exact hx3
    refine ⟨(⟨z.1.1, ?_⟩, ⟨z.1.2, ?_⟩), ⟨z.2, ?_⟩⟩
    · apply (CFSG.mem_omega₁_iff_of_comm (p := 3) hcS).mpr
      have h := congrArg (fun t : (S × S) × S => t.1.1) hz
      simpa using h
    · apply (CFSG.mem_omega₁_iff_of_comm (p := 3) hcS).mpr
      have h := congrArg (fun t : (S × S) × S => t.1.2) hz
      simpa using h
    · apply (CFSG.mem_omega₁_iff_of_comm (p := 3) hcS).mpr
      have h := congrArg (fun t : (S × S) × S => t.2) hz
      simpa using h
  invFun z := by
    let w : (S × S) × S := ((z.1.1.1, z.1.2.1), z.2.1)
    have hw : w ^ 3 = 1 := by
      dsimp only [w]
      apply Prod.ext
      · apply Prod.ext
        · exact (CFSG.mem_omega₁_iff_of_comm (p := 3) hcS).mp z.1.1.2
        · exact (CFSG.mem_omega₁_iff_of_comm (p := 3) hcS).mp z.1.2.2
      · exact (CFSG.mem_omega₁_iff_of_comm (p := 3) hcS).mp z.2.2
    refine ⟨(coordEquiv h) w, ?_⟩
    apply (CFSG.mem_omega₁_iff_of_comm (p := 3) hcB).mpr
    rw [← map_pow, hw, map_one]
  left_inv x := by
    apply Subtype.ext
    simp [MulEquiv.apply_symm_apply]
  right_inv z := by
    ext <;> simp [MulEquiv.symm_apply_apply]

private theorem card_omega_base (h : IsWreathThree S y)
    (hcS : ∀ a b : S, a * b = b * a)
    (hcB : ∀ a b : base S y, a * b = b * a) :
    Nat.card ↥(CFSG.omega₁ (base S y) (p := 3)) = 27 := by
  haveI : Finite S := finite_of_isWreathThree h
  haveI : IsCyclic S := h.isCyclic
  rw [Nat.card_congr (kerPowEquiv h hcS hcB)]
  rw [Nat.card_prod, Nat.card_prod]
  have hK : Nat.card ↥(CFSG.omega₁ S (p := 3)) = 3 := by
    rw [CFSG.card_omega₁_of_isCyclic]
    have hdvd : 3 ∣ Nat.card S := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rcases h.isPGroup.card_eq_or_dvd with h1 | h3
      · exact absurd (Subgroup.card_eq_one.mp h1) h.ne_bot
      · exact h3
    exact Nat.gcd_eq_right hdvd
  rw [hK]

private theorem three_dvd_card_of_isWreathThree (h : IsWreathThree S y) :
    3 ∣ Nat.card S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h.isPGroup.card_eq_or_dvd with h1 | h3
  · exact absurd (Subgroup.card_eq_one.mp h1) h.ne_bot
  · exact h3

private theorem isCyclic_diag (h : IsWreathThree S y) :
    IsCyclic ↥(base S y ⊓ Subgroup.centralizer ({y} : Set G)) := by
  haveI : IsCyclic S := h.isCyclic
  let D : Subgroup G := base S y ⊓ Subgroup.centralizer ({y} : Set G)
  let f : S →* D :=
    ((base S y).subtype.comp (diag h)).codRestrict D (fun a => by
      change (diag h a : G) ∈ base S y ⊓ Subgroup.centralizer ({y} : Set G)
      rw [← diag_range_eq h]
      exact Subgroup.mem_map_of_mem (f := (base S y).subtype) (K := (diag h).range) ⟨a, rfl⟩)
  have hf : Function.Surjective f := by
    intro z
    have hz : (z : G) ∈ (diag h).range.map (base S y).subtype := by
      rw [diag_range_eq h]
      change (z : G) ∈ base S y ⊓ Subgroup.centralizer ({y} : Set G)
      exact z.2
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
    obtain ⟨a, rfl⟩ := hw
    exact ⟨a, Subtype.ext hwz⟩
  exact isCyclic_of_surjective f hf

private theorem sup_base_zpowers_y_le_sup_base_zpowers_x (h : IsWreathThree S y)
    (hy : y ^ 3 = 1) {x : G} (hxP : x ∈ base S y ⊔ Subgroup.zpowers y)
    (hxB : x ∉ base S y) :
    base S y ⊔ Subgroup.zpowers y ≤ base S y ⊔ Subgroup.zpowers x := by
  obtain ⟨b, hb, hxy | hxy⟩ := exists_mul_y_or_mul_y_sq h hy hxP hxB
  · have hy' : y ∈ base S y ⊔ Subgroup.zpowers x := by
      have hyx : y = b⁻¹ * x := by rw [hxy]; group
      have hm : b⁻¹ * x ∈ base S y ⊔ Subgroup.zpowers x :=
        Subgroup.mul_mem_sup ((base S y).inv_mem hb) (Subgroup.mem_zpowers x)
      have hgoal : (b⁻¹ * x ∈ base S y ⊔ Subgroup.zpowers x) ↔
          (y ∈ base S y ⊔ Subgroup.zpowers x) := by
        rw [← hyx]
      exact hgoal.mp hm
    exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hy')
  · have hy2' : y ^ 2 ∈ base S y ⊔ Subgroup.zpowers x := by
      have hy2x : y ^ 2 = b⁻¹ * x := by rw [hxy]; group
      have hm : b⁻¹ * x ∈ base S y ⊔ Subgroup.zpowers x :=
        Subgroup.mul_mem_sup ((base S y).inv_mem hb) (Subgroup.mem_zpowers x)
      have hgoal : (b⁻¹ * x ∈ base S y ⊔ Subgroup.zpowers x) ↔
          (y ^ 2 ∈ base S y ⊔ Subgroup.zpowers x) := by
        rw [← hy2x]
      exact hgoal.mp hm
    have hsq : (y ^ 2) ^ 2 = y := by
      calc (y ^ 2) ^ 2 = y ^ (2 * 2) := by rw [pow_mul]
        _ = y ^ (3 + 1) := by norm_num
        _ = y ^ 3 * y ^ 1 := by rw [pow_add]
        _ = y := by rw [hy, one_mul, pow_one]
    have hy' : y ∈ base S y ⊔ Subgroup.zpowers x := by
      have h2B : (y ^ 2) ^ 2 ∈ base S y ⊔ Subgroup.zpowers x :=
        (base S y ⊔ Subgroup.zpowers x).pow_mem hy2' 2
      have hgoal : ((y ^ 2) ^ 2 ∈ base S y ⊔ Subgroup.zpowers x) ↔
          (y ∈ base S y ⊔ Subgroup.zpowers x) := by
        rw [hsq]
      exact hgoal.mp h2B
    exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hy')

private theorem eq_inf_sup_of_le_sup (h : IsWreathThree S y) {x : G}
    (hxnorm : x ∈ Subgroup.normalizer (base S y : Set G)) {E : Subgroup G}
    (hE : E ≤ base S y ⊔ Subgroup.zpowers x) (hxE : x ∈ E) :
    E = (E ⊓ base S y) ⊔ Subgroup.zpowers x := by
  apply le_antisymm
  · intro e he
    have he' : e ∈ (base S y : Set G) * (Subgroup.zpowers x : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (base S y) (Subgroup.zpowers x)
        (Subgroup.zpowers_le.mpr hxnorm)]
      exact hE he
    obtain ⟨b, hb, t, ht, hbt⟩ := he'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht
    rw [← hk] at hbt
    have hxkE : x ^ k ∈ E :=
      Subgroup.zpowers_le.mpr hxE (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
    have hbE : b ∈ E := by
      have hb_eq : b = e * (x ^ k)⁻¹ := by rw [← hbt]; group
      rw [hb_eq]
      exact E.mul_mem he (E.inv_mem hxkE)
    have hbBE : b ∈ E ⊓ base S y := ⟨hbE, hb⟩
    rw [← hbt]
    exact Subgroup.mul_mem_sup hbBE (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hxE)

private theorem disjoint_base_zpowers_of_not_mem (h : IsWreathThree S y) {x : G}
    (hxB : x ∉ base S y) (hx3 : x ^ 3 = 1) :
    Disjoint (base S y) (Subgroup.zpowers x) := by
  rw [disjoint_iff]
  apply le_antisymm _ bot_le
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz.2
  have hk3 : x ^ k = x ^ (k % 3) := zpow_eq_zpow_emod k (by simpa using hx3)
  have hr0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hr3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0] at hk3
    rw [hk3] at hk
    simpa using hk.symm
  · rw [h1] at hk3
    rw [hk3] at hk
    have hx : x ∈ base S y := by
      have hx' : x = z := by simpa using hk
      exact hx' ▸ hz.1
    exact absurd hx hxB
  · rw [h2] at hk3
    rw [hk3] at hk
    have hx2 : x ^ 2 ∈ base S y := by
      have hx' : x ^ 2 = z := by simpa using hk
      exact hx' ▸ hz.1
    have hx : x ∈ base S y := by
      have hsq : (x ^ 2) ^ 2 = x := by
        calc (x ^ 2) ^ 2 = x ^ (2 * 2) := by rw [pow_mul]
          _ = x ^ (3 + 1) := by norm_num
          _ = x ^ 3 * x ^ 1 := by rw [pow_add]
          _ = x := by rw [hx3, one_mul, pow_one]
      rw [← hsq]
      exact (base S y).pow_mem hx2 2
    exact absurd hx hxB

theorem exists_unique_elemAbelian [Finite G] (h : IsWreathThree S y) (hy : y ^ 3 = 1) :
    ∃ A : Subgroup G, A ≤ base S y ∧ CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27 ∧
      (∀ x ∈ base S y, x ^ 3 = 1 → x ∈ A) ∧
      ∀ E : Subgroup G, E ≤ base S y ⊔ Subgroup.zpowers y → CFSG.Open.IsElemAbelian 3 E →
        Nat.card E = 27 → E = A := by
  haveI : Finite S := finite_of_isWreathThree h
  have hcS : ∀ a b : S, a * b = b * a := by
    haveI : IsCyclic S := h.isCyclic
    exact isMulCommutative_iff.mp (IsCyclic.isMulCommutative (α := S))
  have hcB : ∀ a b : base S y, a * b = b * a := fun a b =>
    Subtype.ext (h.comm (a : G) a.2 (b : G) b.2)
  let A : Subgroup G := (CFSG.omega₁ (base S y) (p := 3)).map (base S y).subtype
  have hA_le : A ≤ base S y := by
    intro z hz
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp hz
    exact w.2
  have hA_card : Nat.card A = 27 := by
    rw [show A = (CFSG.omega₁ (base S y) (p := 3)).map (base S y).subtype from rfl,
      Subgroup.card_map_of_injective (base S y).subtype_injective,
      card_omega_base h hcS hcB]
  have hA_elem : CFSG.Open.IsElemAbelian 3 A := by
    constructor
    · refine IsMulCommutative.mk (Std.Commutative.mk ?_)
      intro u v
      apply Subtype.ext
      exact h.comm u (hA_le u.2) v (hA_le v.2)
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      have hw' : (w : base S y) ^ 3 = 1 := (CFSG.mem_omega₁_iff_of_comm (p := 3) hcB).mp hw
      simpa [Subgroup.coe_pow] using congrArg (fun z : base S y => (z : G)) hw'
  have hA_univ : ∀ z ∈ base S y, z ^ 3 = 1 → z ∈ A := by
    intro z hz hz3
    have hz3B : (⟨z, hz⟩ : base S y) ^ 3 = 1 := by simpa using hz3
    have hz3' : (⟨z, hz⟩ : base S y) ∈ CFSG.omega₁ (base S y) (p := 3) :=
      (CFSG.mem_omega₁_iff_of_comm (p := 3) (y := (⟨z, hz⟩ : base S y)) hcB).mpr hz3B
    exact Subgroup.mem_map_of_mem _ hz3'
  refine ⟨A, hA_le, hA_elem, hA_card, hA_univ, ?_⟩
  intro E hE hEelem hEcard
  by_cases hEB : E ≤ base S y
  · have hEA : E ≤ A := fun z hz => hA_univ z (hEB hz) (hEelem.2 z hz)
    apply Subgroup.eq_of_le_of_card_ge hEA
    rw [hA_card, hEcard]
  · obtain ⟨x, hxE, hxB⟩ : ∃ x ∈ E, x ∉ base S y := by
      by_contra h
      apply hEB
      intro z hz
      by_contra hzB
      exact h ⟨z, hz, hzB⟩
    have hxP : x ∈ base S y ⊔ Subgroup.zpowers y := hE hxE
    have hx3 : x ^ 3 = 1 := hEelem.2 x hxE
    have hxnorm : x ∈ Subgroup.normalizer (base S y : Set G) := by
      have hPnorm : (base S y ⊔ Subgroup.zpowers y : Subgroup G) ≤
          Subgroup.normalizer (base S y : Set G) := by
        apply sup_le
        · exact (base S y).le_normalizer
        · exact Subgroup.zpowers_le.mpr (mem_normalizer_base h)
      exact hPnorm hxP
    have hEx : E ≤ base S y ⊔ Subgroup.zpowers x :=
      hE.trans (sup_base_zpowers_y_le_sup_base_zpowers_x h hy hxP hxB)
    have hEeq : E = (E ⊓ base S y) ⊔ Subgroup.zpowers x :=
      eq_inf_sup_of_le_sup h hxnorm hEx hxE
    have hdisj : Disjoint (E ⊓ base S y) (Subgroup.zpowers x) :=
      (disjoint_base_zpowers_of_not_mem h hxB hx3).mono inf_le_right le_rfl
    have hxEBnorm : Subgroup.zpowers x ≤ Subgroup.normalizer ((E ⊓ base S y) : Set G) := by
      change Subgroup.zpowers x ≤ Subgroup.normalizer (((E ⊓ base S y : Subgroup G) : Set G))
      rw [Subgroup.le_normalizer_iff]
      intro t ht b hb
      have hxb : x * b = b * x := CFSG.Open.IsElemAbelian.comm hEelem hxE hb.1
      have hxcen : x ∈ Subgroup.centralizer ({b} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hxb
      have htc : t ∈ Subgroup.centralizer ({b} : Set G) :=
        Subgroup.zpowers_le.mpr hxcen ht
      have htb : t * b = b * t := Subgroup.mem_centralizer_singleton_iff.mp htc
      have hfix : t * b * t⁻¹ = b := by rw [htb]; group
      rw [hfix]
      exact hb
    have hcardE : Nat.card E = Nat.card ↥(E ⊓ base S y) * 3 := by
      conv_lhs => rw [hEeq]
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (E ⊓ base S y) (Subgroup.zpowers x) hxEBnorm hdisj]
      congr 1
      rw [Nat.card_zpowers]
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hx3 (by intro h1; exact hxB (h1 ▸ (base S y).one_mem))
    have hDcomm : ∀ a b : ↥(base S y ⊓ Subgroup.centralizer ({y} : Set G)), a * b = b * a := by
      intro a b
      apply Subtype.ext
      exact h.comm (a : G) a.2.1 (b : G) b.2.1
    have hEB_le_D : E ⊓ base S y ≤ base S y ⊓ Subgroup.centralizer ({y} : Set G) := by
      intro z hz
      rw [Subgroup.mem_inf] at hz
      obtain ⟨hzE, hzB⟩ := hz
      have hzx : z * x = x * z := CFSG.Open.IsElemAbelian.comm hEelem hzE hxE
      have hzC : z ∈ Subgroup.centralizer ({x} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hzx
      rw [← inf_centralizer_eq_diag h hy hxP hxB]
      exact ⟨hzB, hzC⟩
    have hcardEB : Nat.card ↥(E ⊓ base S y) ≤ 3 := by
      let D : Subgroup G := base S y ⊓ Subgroup.centralizer ({y} : Set G)
      let f : ↥(E ⊓ base S y) → ↥(CFSG.omega₁ (↥D) (p := 3)) := fun z =>
        ⟨⟨z.1, hEB_le_D z.2⟩, (CFSG.mem_omega₁_iff_of_comm (p := 3) hDcomm).mpr (by
          apply Subtype.ext
          exact hEelem.2 z.1 z.2.1)⟩
      have hf : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun w => ((w : ↥(CFSG.omega₁ (↥D) (p := 3))) : G)) hab
      haveI : Finite ↥D := Subtype.finite
      haveI : IsCyclic ↥D := isCyclic_diag h
      have hDcard : Nat.card ↥(CFSG.omega₁ (↥D) (p := 3)) = 3 := by
        rw [CFSG.card_omega₁_of_isCyclic]
        show (Nat.card ↥(base S y ⊓ Subgroup.centralizer ({y} : Set G))).gcd 3 = 3
        rw [card_diag h]
        exact Nat.gcd_eq_right (three_dvd_card_of_isWreathThree h)
      have hle := Nat.card_le_card_of_injective f hf
      rw [hDcard] at hle
      exact hle
    have hE_le : Nat.card E ≤ 9 := by
      rw [hcardE]
      nlinarith [hcardEB]
    omega
