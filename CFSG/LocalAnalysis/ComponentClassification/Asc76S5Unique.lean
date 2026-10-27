module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Shapes

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

theorem eq_of_mulEquiv_of_inverts {G : Type} [Group G] [Finite G] {R C C' : Subgroup G}
    (hR : IsPGroup 2 R) (hCR : C ≤ R) (hCn : (C.subgroupOf R).Normal) (hC : IsMulCommutative C)
    (hinv : ∀ r ∈ R, r ∉ C → r ^ 2 ∈ C → ∀ x ∈ C, r * x * r⁻¹ = x⁻¹)
    (hE : ∀ E : Subgroup G, C ≤ E → E ≤ R → (∀ x ∈ E, x ^ 2 ∈ C) →
      (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ C) → C.relIndex E ≤ 2)
    (hsq : ∀ x ∈ C, x ^ 2 = 1 → ∃ y ∈ C, x = y ^ 2) (hcyc : ¬ IsCyclic C) (hC'R : C' ≤ R)
    (e : C' ≃* C) : C' = C := by
  by_contra hne
  have hRN : R ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCR).mp hCn
  have hC'2 : IsPGroup 2 C' := hR.to_le hC'R
  have hcomm : ∀ a ∈ C', ∀ b ∈ C', Commute a b := fun a ha b hb => by
    have h1 : e ⟨a, ha⟩ * e ⟨b, hb⟩ = e ⟨b, hb⟩ * e ⟨a, ha⟩ := hC.is_comm.comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)
  have hsq' : ∀ x ∈ C', x ^ 2 = 1 → ∃ y ∈ C', x = y ^ 2 := by
    intro x hx hx2
    have h1 : (e ⟨x, hx⟩ : G) ^ 2 = 1 := by
      have h2 : (⟨x, hx⟩ : C') ^ 2 = 1 := Subtype.ext (by simpa using hx2)
      rw [← Subgroup.coe_pow, ← map_pow, h2, map_one, Subgroup.coe_one]
    obtain ⟨y, hyC, hy⟩ := hsq _ (e ⟨x, hx⟩).2 h1
    refine ⟨(e.symm ⟨y, hyC⟩ : G), (e.symm ⟨y, hyC⟩).2, ?_⟩
    have h3 : e ⟨x, hx⟩ = e (e.symm ⟨y, hyC⟩ ^ 2) := by
      rw [map_pow, e.apply_symm_apply]
      exact Subtype.ext (by simpa using hy)
    have h4 := congrArg Subtype.val (e.injective h3)
    simpa using h4
  have hC'C : ¬ C' ≤ C := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (Nat.card_congr e.toEquiv).ge)
  obtain ⟨c, hcC', hcC, hc2⟩ :=
    AschbacherStrongEmbedding.Lemma34.exists_mem_sq_mem_of_not_le hC'2 hC'C
  have hinvc := hinv c (hC'R hcC') hcC (by rw [pow_two]; exact hc2)
  have hI2 : ∀ x ∈ C', x ∈ C → x ^ 2 = 1 := by
    intro x hxC' hxC
    have h1 := hinvc x hxC
    rw [(hcomm c hcC' x hxC').eq, mul_inv_cancel_right] at h1
    rw [pow_two]
    nth_rewrite 1 [h1]
    exact inv_mul_cancel x
  let Y : Subgroup G :=
    { carrier := {y | y ∈ C' ∧ y ^ 2 ∈ C}
      mul_mem' := fun {a b} ha hb => ⟨C'.mul_mem ha.1 hb.1, by
        rw [(hcomm a ha.1 b hb.1).mul_pow]
        exact C.mul_mem ha.2 hb.2⟩
      one_mem' := ⟨C'.one_mem, by rw [one_pow]; exact C.one_mem⟩
      inv_mem' := fun {a} ha => ⟨C'.inv_mem ha.1, by rw [inv_pow]; exact C.inv_mem ha.2⟩ }
  have hY : ∀ y, y ∈ Y ↔ y ∈ C' ∧ y ^ 2 ∈ C := fun y => Iff.rfl
  have hYC' : Y ≤ C' := fun y hy => ((hY y).mp hy).1
  have hYN : Y ≤ Subgroup.normalizer (C : Set G) := (hYC'.trans hC'R).trans hRN
  let φ : Y →* G :=
    { toFun := fun y => (y : G) ^ 2
      map_one' := by rw [Subgroup.coe_one, one_pow]
      map_mul' := fun a b => by
        rw [Subgroup.coe_mul]
        exact (hcomm a (hYC' a.2) b (hYC' b.2)).mul_pow 2 }
  have hφ : ∀ y : Y, φ y = (y : G) ^ 2 := fun y => rfl
  have hrange : φ.range = C ⊓ Y := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [hφ]
      exact ⟨((hY y).mp y.2).2, Y.pow_mem y.2 2⟩
    · rintro ⟨hxC, hxY⟩
      obtain ⟨y, hyC', rfl⟩ := hsq' x (hYC' hxY) (hI2 x (hYC' hxY) hxC)
      exact ⟨⟨y, (hY y).mpr ⟨hyC', hxC⟩⟩, rfl⟩
  have hcardY : Nat.card φ.ker * Nat.card (C ⊓ Y : Subgroup G) = Nat.card Y := by
    rw [← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hidx : C.relIndex Y ≤ 2 := by
    rw [← AschbacherTheorem3.relIndex_sup_of_le_normalizer hYN]
    refine hE (C ⊔ Y) le_sup_left (sup_le hCR (hYC'.trans hC'R)) ?_ ?_
    · intro x hx
      obtain ⟨a, ha, y, hy, rfl⟩ := NormalizedProduct.coordinates C Y hYN x hx
      have hyay : y * a * y⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hYN hy) a).mp ha
      rw [show (a * y) ^ 2 = a * (y * a * y⁻¹) * y ^ 2 by simp only [pow_two]; group]
      exact C.mul_mem (C.mul_mem ha hyay) ((hY y).mp hy).2
    · intro x hx x' hx'
      obtain ⟨a, ha, y, hy, rfl⟩ := NormalizedProduct.coordinates C Y hYN x hx
      obtain ⟨b, hb, z, hz, rfl⟩ := NormalizedProduct.coordinates C Y hYN x' hx'
      have hyz : y * z * y⁻¹ * z⁻¹ = 1 := by
        rw [(hcomm y (hYC' hy) z (hYC' hz)).eq]
        group
      have hyb : y * b * y⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hYN hy) b).mp hb
      have hza : z * a⁻¹ * z⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hYN hz) a⁻¹).mp (C.inv_mem ha)
      rw [show a * y * (b * z) * (a * y)⁻¹ * (b * z)⁻¹ =
          a * (y * b * y⁻¹) * (y * z * y⁻¹ * z⁻¹) * (z * a⁻¹ * z⁻¹) * b⁻¹ by group, hyz,
        mul_one]
      exact C.mul_mem (C.mul_mem (C.mul_mem ha hyb) hza) (C.inv_mem hb)
  have hker : Nat.card φ.ker ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card C Y
    have hpos : 0 < Nat.card (C ⊓ Y : Subgroup G) := Nat.card_pos
    have h2 : Nat.card φ.ker = C.relIndex Y :=
      Nat.eq_of_mul_eq_mul_right hpos (hcardY.trans h1.symm)
    omega
  have huniq : ∀ x y : C', orderOf x = 2 → orderOf y = 2 → x = y := by
    intro x y hx hy
    by_contra hxy
    have hx2 : (x : G) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
    have hy2 : (y : G) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
    have hx1 : (x : G) ≠ 1 := fun h => by
      rw [show x = 1 from Subtype.ext h, orderOf_one] at hx
      omega
    have hy1 : (y : G) ≠ 1 := fun h => by
      rw [show y = 1 from Subtype.ext h, orderOf_one] at hy
      omega
    have hxY : (x : G) ∈ Y := (hY _).mpr ⟨x.2, by rw [hx2]; exact C.one_mem⟩
    have hyY : (y : G) ∈ Y := (hY _).mpr ⟨y.2, by rw [hy2]; exact C.one_mem⟩
    have hxk : (⟨x, hxY⟩ : Y) ∈ φ.ker := by rw [MonoidHom.mem_ker, hφ]; exact hx2
    have hyk : (⟨y, hyY⟩ : Y) ∈ φ.ker := by rw [MonoidHom.mem_ker, hφ]; exact hy2
    have h3 : 2 < Nat.card φ.ker := by
      have := Fintype.ofFinite φ.ker
      rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
      refine ⟨1, ⟨⟨x, hxY⟩, hxk⟩, ⟨⟨y, hyY⟩, hyk⟩, fun h => hx1 ?_, fun h => hy1 ?_,
        fun h => hxy ?_⟩
      · exact (congrArg (fun w : φ.ker => ((w : Y) : G)) h).symm
      · exact (congrArg (fun w : φ.ker => ((w : Y) : G)) h).symm
      · exact Subtype.ext (congrArg (fun w : φ.ker => ((w : Y) : G)) h)
    omega
  have hC'c : IsMulCommutative (⊤ : Subgroup C') :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext ((hcomm _ (a : C').2 _ (b : C').2).eq))⟩⟩
  have hcyc' : IsCyclic (⊤ : Subgroup C') :=
    CFSG.BenderSuzuki.External.huppert_III_7_6b_isCyclic_of_isMulCommutative_unique_order_two
      hC'2 huniq ⊤ hC'c
  have hcycC' : IsCyclic C' :=
    isCyclic_of_surjective Subgroup.topEquiv.toMonoidHom Subgroup.topEquiv.surjective
  exact hcyc (isCyclic_of_surjective e.toMonoidHom e.surjective)

end CFSG.ComponentClassification.Asc76.Sec5
