module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClasses
public import CFSG.LieType.Multipliers.U62Bridge

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Sporadic.Schreier CFSG.Fischer

structure ToddParabolic (Q : Type) [Group Q] where
  A : Subgroup Q
  K : Subgroup Q
  S : Subgroup Q
  a₁ : Q
  a₂ : Q
  a₃ : Q
  card_Q : Nat.card Q = 9196830720
  card_A : Nat.card A = 2 ^ 9
  A_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  A_sq : ∀ x ∈ A, x ^ 2 = 1
  card_K : Nat.card K = 20160
  lieModel_K : CFSG.Blueprint.LieModel K .PSL 3 2 2
  K_le_normalizer : K ≤ Subgroup.normalizer (A : Set Q)
  A_inf_K : A ⊓ K = ⊥
  normalizer_A : Subgroup.normalizer (A : Set Q) = A ⊔ K
  centralizer_A : Subgroup.centralizer (A : Set Q) = A
  a_mem : a₁ ∈ A ∧ a₂ ∈ A ∧ a₃ ∈ A
  conj_into_A : ∀ t : Q, orderOf t = 2 → ∃ g : Q, g * t * g⁻¹ ∈ A
  classes : ∀ t : Q, orderOf t = 2 → IsConj t a₁ ∨ IsConj t a₂ ∨ IsConj t a₃
  not_isConj : ¬ IsConj a₁ a₂ ∧ ¬ IsConj a₁ a₃ ∧ ¬ IsConj a₂ a₃
  orbits : ∀ a ∈ A, a ≠ 1 → a ∈ conjClass K a₁ ∨ a ∈ conjClass K a₂ ∨ a ∈ conjClass K a₃
  orbit_card : (conjClass K a₁).ncard = 21 ∧ (conjClass K a₂).ncard = 210 ∧
    (conjClass K a₃).ncard = 280
  card_S : Nat.card S = 2 ^ 15
  A_le_S : A ≤ S
  center_S : ∀ x ∈ S, (∀ s ∈ S, x * s = s * x) ↔ x = 1 ∨ x = a₁
  abelian_S : ∀ X : Subgroup Q, X ≤ S → (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) →
    Nat.card X ≤ 2 ^ 9 ∧ (Nat.card X = 2 ^ 9 → X = A)
  sq_a₁ : ∃ u v : Q, orderOf u = 3 ∧ orderOf v = 3 ∧ u * a₁ = a₁ * u ∧ v * a₁ = a₁ * v ∧
    (u * v) ^ 2 = a₁
  sq_a₂ : ∃ y ∈ A ⊔ K, y ^ 2 = a₂
  not_sq_a₃ : ∀ g : Q, g ^ 2 ≠ a₃

namespace ToddParabolic

variable {Q : Type} [Group Q]

theorem finite (D : ToddParabolic Q) : Finite Q :=
  Nat.finite_of_card_ne_zero (by rw [D.card_Q]; norm_num)

theorem index_of_card (D : ToddParabolic Q) {S' : Subgroup Q} (h : Nat.card S' = 2 ^ 15) :
    S'.index = 280665 := by
  have := S'.card_mul_index
  rw [h, D.card_Q] at this
  omega

theorem exists_conj_le_S (D : ToddParabolic Q) {S' : Subgroup Q} (hS' : Nat.card S' = 2 ^ 15) :
    ∃ g : Q, ∀ x ∈ S', g * x * g⁻¹ ∈ D.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := D.finite
  have hP : IsPGroup 2 D.S := IsPGroup.of_card D.card_S
  have hP' : IsPGroup 2 S' := IsPGroup.of_card hS'
  have hi : ¬ 2 ∣ D.S.index := by rw [D.index_of_card D.card_S]; norm_num
  have hi' : ¬ 2 ∣ S'.index := by rw [D.index_of_card hS']; norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q (hP'.toSylow hi') (hP.toSylow hi)
  refine ⟨g, fun x hx => ?_⟩
  have h1 : g * x * g⁻¹ ∈ ((g • hP'.toSylow hi' : Sylow 2 Q) : Subgroup Q) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨x, (IsPGroup.mem_toSylow hP' hi').2 hx, rfl⟩
  rw [hg] at h1
  exact (IsPGroup.mem_toSylow hP hi).1 h1

theorem abelian_of_sylow (D : ToddParabolic Q) {S' : Subgroup Q} (hS' : Nat.card S' = 2 ^ 15)
    (hAS' : D.A ≤ S') {X : Subgroup Q} (hX : X ≤ S') (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    Nat.card X ≤ 2 ^ 9 ∧ (Nat.card X = 2 ^ 9 → X = D.A) := by
  obtain ⟨g, hg⟩ := D.exists_conj_le_S hS'
  have hψ : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hmap : ∀ Y : Subgroup Q, Y ≤ S' → (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) →
      Nat.card Y ≤ 2 ^ 9 ∧ (Nat.card Y = 2 ^ 9 → Y.map (MulAut.conj g).toMonoidHom = D.A) := by
    intro Y hY hYc
    have hle : Y.map (MulAut.conj g).toMonoidHom ≤ D.S := by
      rintro _ ⟨y, hy, rfl⟩
      exact hg y (hY hy)
    have hc : ∀ x ∈ Y.map (MulAut.conj g).toMonoidHom,
        ∀ y ∈ Y.map (MulAut.conj g).toMonoidHom, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hYc x hx y hy]
    have h := D.abelian_S _ hle hc
    rw [Subgroup.card_map_of_injective hψ] at h
    exact h
  obtain ⟨h1, h2⟩ := hmap X hX hcomm
  refine ⟨h1, fun h => Subgroup.map_injective hψ ?_⟩
  rw [h2 h, (hmap D.A hAS' D.A_comm).2 D.card_A]

end ToddParabolic

section Transport

variable
    {Q : Type} [Group Q] (e : Q ≃* T46)

noncomputable def embT46 :
    Q →* Equiv.Perm (Fin 693) := T46.subtype.comp e.toMonoidHom

theorem embT46_injective :
    Function.Injective (embT46 e) :=
  Subtype.val_injective.comp e.injective

theorem embT46_mem
    (q : Q) : embT46 e q ∈ T46 := (e q).2

theorem embT46_symm
    {x : Equiv.Perm (Fin 693)} (hx : x ∈ T46) :
    embT46 e (e.symm ⟨x, hx⟩) = x := by
  simp [embT46]

theorem exists_embT46
    {x : Equiv.Perm (Fin 693)} (hx : x ∈ T46) : ∃ q, embT46 e q = x :=
  ⟨_, embT46_symm e hx⟩

theorem map_comap_embT46
    {H : Subgroup (Equiv.Perm (Fin 693))} (hH : H ≤ T46) :
    (H.comap (embT46 e)).map (embT46 e) = H :=
  Subgroup.map_comap_eq_self fun _ hx => MonoidHom.mem_range.2 (exists_embT46 e (hH hx))

theorem card_comap_embT46
    {H : Subgroup (Equiv.Perm (Fin 693))} (hH : H ≤ T46) :
    Nat.card (H.comap (embT46 e)) = Nat.card H := by
  calc Nat.card (H.comap (embT46 e)) = Nat.card ((H.comap (embT46 e)).map (embT46 e)) :=
        (Subgroup.card_map_of_injective (embT46_injective e)).symm
    _ = Nat.card H := by rw [map_comap_embT46 e hH]

noncomputable def comapEquiv
    {H : Subgroup (Equiv.Perm (Fin 693))} (hH : H ≤ T46) :
    H.comap (embT46 e) ≃* H :=
  ((H.comap (embT46 e)).equivMapOfInjective (embT46 e) (embT46_injective e)).trans
    (MulEquiv.subgroupCongr (map_comap_embT46 e hH))

theorem embT46_eq_iff
    {q r : Q} : embT46 e q = embT46 e r ↔ q = r :=
  (embT46_injective e).eq_iff

theorem orderOf_embT46
    (q : Q) : orderOf (embT46 e q) = orderOf q :=
  orderOf_injective _ (embT46_injective e) q

theorem mem_sup_of_mem_uP
    {q : Q} (hq : embT46 e q ∈ uP) :
    q ∈ uA.comap (embT46 e) ⊔ uK.comap (embT46 e) := by
  rw [uP_eq] at hq
  have hq' : embT46 e q ∈
      ((uA ⊔ uK : Subgroup (Equiv.Perm (Fin 693))) : Set (Equiv.Perm (Fin 693))) := hq
  rw [Subgroup.coe_mul_of_right_le_normalizer_left uA uK uK_le_normalizer] at hq'
  obtain ⟨a, ha, k, hk, hak⟩ := Set.mem_mul.1 hq'
  obtain ⟨a', rfl⟩ := exists_embT46 e (uA_le_T46 ha)
  obtain ⟨k', rfl⟩ := exists_embT46 e (uK_le_T46 hk)
  have hq'' : q = a' * k' := (embT46_injective e) (by rw [map_mul, hak])
  rw [hq'']
  exact Subgroup.mul_mem_sup ha hk

theorem image_conjClass_embT46
    (a : Q) :
    embT46 e '' conjClass (uK.comap (embT46 e)) a = conjClass uK (embT46 e a) := by
  ext x
  constructor
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨embT46 e c, hc, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨k', rfl⟩ := exists_embT46 e (uK_le_T46 hk)
    exact ⟨k' * a * k'⁻¹, ⟨k', hk, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩

theorem mem_normalizer_comap
    {q : Q}
    (hq : q ∈ Subgroup.normalizer ((uA.comap (embT46 e) : Subgroup Q) : Set Q)) :
    embT46 e q ∈ Subgroup.normalizer (uA : Set (Equiv.Perm (Fin 693))) := by
  rw [Subgroup.mem_normalizer_iff] at hq ⊢
  intro h
  have hhT : h ∈ uA ∨ embT46 e q * h * (embT46 e q)⁻¹ ∈ uA → h ∈ T46 := by
    rintro (hh | hh)
    · exact uA_le_T46 hh
    · have h1 := uA_le_T46 hh
      have e1 : h = (embT46 e q)⁻¹ * (embT46 e q * h * (embT46 e q)⁻¹) * embT46 e q := by
        group
      rw [e1]
      exact T46.mul_mem (T46.mul_mem (T46.inv_mem (embT46_mem e q)) h1) (embT46_mem e q)
  constructor
  · intro hh
    obtain ⟨h', rfl⟩ := exists_embT46 e (hhT (Or.inl hh))
    have := (hq h').1 hh
    simpa [Subgroup.mem_comap, map_mul, map_inv] using this
  · intro hh
    obtain ⟨h', rfl⟩ := exists_embT46 e (hhT (Or.inr hh))
    refine (hq h').2 ?_
    simpa [Subgroup.mem_comap, map_mul, map_inv] using hh

theorem comap_uK_le_normalizer :
    uK.comap (embT46 e) ≤ Subgroup.normalizer ((uA.comap (embT46 e) : Subgroup Q) : Set Q) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have := Subgroup.mem_normalizer_iff.1 (uK_le_normalizer hq) (embT46 e h)
  simpa [Subgroup.mem_comap, map_mul, map_inv] using this

noncomputable def ToddParabolic.ofMulEquivT46 :
    ToddParabolic Q where
  A := uA.comap (embT46 e)
  K := uK.comap (embT46 e)
  S := uS.comap (embT46 e)
  a₁ := e.symm ⟨j1, uA_le_T46 j1_mem⟩
  a₂ := e.symm ⟨j2, uA_le_T46 j2_mem⟩
  a₃ := e.symm ⟨j3, uA_le_T46 j3_mem⟩
  card_Q := by rw [Nat.card_congr e.toEquiv, card_T46]
  card_A := (card_comap_embT46 e uA_le_T46).trans (card_uA.trans (by norm_num))
  A_comm x hx y hy := (embT46_injective e) (by rw [map_mul, map_mul]; exact uA_comm _ hx _ hy)
  A_sq x hx := (embT46_injective e) (by rw [map_pow, map_one]; exact uA_sq _ hx)
  card_K := by rw [card_comap_embT46 e uK_le_T46, card_uK]
  lieModel_K := lieModel_of_mulEquiv_S ((comapEquiv e uK_le_T46).trans uKEquivS)
  K_le_normalizer := comap_uK_le_normalizer e
  A_inf_K := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : embT46 e x ∈ uA ⊓ uK := ⟨hx.1, hx.2⟩
    rw [uA_inf_uK, Subgroup.mem_bot, ← map_one (embT46 e), embT46_eq_iff] at h1
    exact (Subgroup.mem_bot).2 h1
  normalizer_A := by
    refine le_antisymm (fun q hq => mem_sup_of_mem_uP e ?_)
      (sup_le Subgroup.le_normalizer (comap_uK_le_normalizer e))
    rw [← normalizer_uA]
    exact ⟨embT46_mem e q, mem_normalizer_comap e hq⟩
  centralizer_A := by
    refine le_antisymm (fun q hq => ?_) fun q hq => ?_
    · have hc : embT46 e q ∈ T46 ⊓ Subgroup.centralizer (uA : Set (Equiv.Perm (Fin 693))) := by
        refine ⟨embT46_mem e q, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
        obtain ⟨h', rfl⟩ := exists_embT46 e (uA_le_T46 hh)
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hq h' hh]
      rw [centralizer_uA] at hc
      exact hc
    · exact Subgroup.mem_centralizer_iff.2 fun h hh =>
        (embT46_injective e) (by rw [map_mul, map_mul]; exact uA_comm _ hh _ hq)
  a_mem := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Subgroup.mem_comap, embT46_symm]
    · exact j1_mem
    · exact j2_mem
    · exact j3_mem
  conj_into_A t ht := by
    obtain ⟨g, hg, hgA⟩ := conj_into_uA (embT46_mem e t) (by rw [orderOf_embT46]; exact ht)
    obtain ⟨g', rfl⟩ := exists_embT46 e hg
    exact ⟨g', by simpa [Subgroup.mem_comap, map_mul, map_inv] using hgA⟩
  classes t ht := by
    obtain ⟨g, hg, hgj⟩ := involution_classes (embT46_mem e t)
      (by rw [orderOf_embT46]; exact ht)
    obtain ⟨g', rfl⟩ := exists_embT46 e hg
    have key : ∀ (j : Equiv.Perm (Fin 693)) (hj : j ∈ T46),
        embT46 e g' * embT46 e t * (embT46 e g')⁻¹ = j → IsConj t (e.symm ⟨j, hj⟩) := by
      intro j hj h
      refine isConj_iff.2 ⟨g', (embT46_injective e) ?_⟩
      rw [map_mul, map_mul, map_inv, embT46_symm]
      exact h
    rcases hgj with h | h | h
    · exact Or.inl (key j1 _ h)
    · exact Or.inr (Or.inl (key j2 _ h))
    · exact Or.inr (Or.inr (key j3 _ h))
  not_isConj := by
    have hmap : ∀ {a b : Q}, IsConj a b → IsConj (embT46 e a) (embT46 e b) := by
      intro a b h
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      exact isConj_iff.2 ⟨embT46 e c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩
    obtain ⟨h12, h13, h23⟩ := not_isConj_j
    refine ⟨fun h => h12 ?_, fun h => h13 ?_, fun h => h23 ?_⟩ <;>
      simpa only [embT46_symm] using hmap h
  orbits a ha ha1 := by
    have ha1' : embT46 e a ≠ 1 := fun h => ha1 ((embT46_injective e) (by rw [h, map_one]))
    have hback : ∀ (j : Equiv.Perm (Fin 693)) (hj : j ∈ T46),
        embT46 e a ∈ conjClass uK j →
          a ∈ conjClass (uK.comap (embT46 e)) (e.symm ⟨j, hj⟩) := by
      intro j hj h
      rw [← embT46_symm e hj, ← image_conjClass_embT46] at h
      obtain ⟨x, hx, hxa⟩ := h
      rwa [← (embT46_injective e) hxa]
    rcases korbits.1 _ ha ha1' with h | h | h
    · exact Or.inl (hback j1 _ h)
    · exact Or.inr (Or.inl (hback j2 _ h))
    · exact Or.inr (Or.inr (hback j3 _ h))
  orbit_card := by
    have h : ∀ (j : Equiv.Perm (Fin 693)) (hj : j ∈ T46),
        (conjClass (uK.comap (embT46 e)) (e.symm ⟨j, hj⟩)).ncard = (conjClass uK j).ncard := by
      intro j hj
      rw [← Set.ncard_image_of_injective _ (embT46_injective e), image_conjClass_embT46,
        embT46_symm]
    obtain ⟨-, h1, h2, h3⟩ := korbits
    exact ⟨(h j1 _).trans h1, (h j2 _).trans h2, (h j3 _).trans h3⟩
  card_S := (card_comap_embT46 e uS_le_T46).trans (card_uS.trans (by norm_num))
  A_le_S := Subgroup.comap_mono uA_le_uS
  center_S x hx := by
    have h1 : (∀ s ∈ uS.comap (embT46 e), x * s = s * x) ↔
        ∀ s ∈ uS, embT46 e x * s = s * embT46 e x := by
      constructor
      · intro hc s hs
        obtain ⟨s', rfl⟩ := exists_embT46 e (uS_le_T46 hs)
        rw [← map_mul, ← map_mul, hc s' hs]
      · intro hc s hs
        exact (embT46_injective e) (by rw [map_mul, map_mul]; exact hc _ hs)
    have hj : embT46 e (e.symm ⟨j1, uA_le_T46 j1_mem⟩) = j1 := embT46_symm e _
    rw [h1, center_uS hx]
    constructor
    · rintro (h | h)
      · exact Or.inl ((embT46_injective e) (by rw [h, map_one]))
      · exact Or.inr ((embT46_injective e) (by rw [h, hj]))
    · rintro (rfl | rfl)
      · exact Or.inl (map_one _)
      · exact Or.inr hj
  abelian_S X hX hcomm := by
    have hXS : X.map (embT46 e) ≤ uS := Subgroup.map_le_iff_le_comap.2 hX
    have hcomm' : ∀ x ∈ X.map (embT46 e), ∀ y ∈ X.map (embT46 e), x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy]
    obtain ⟨h1, h2⟩ := abelian_le_uS hXS hcomm'
    rw [Subgroup.card_map_of_injective (embT46_injective e)] at h1 h2
    refine ⟨le_of_le_of_eq h1 (by norm_num), fun h => ?_⟩
    rw [← Subgroup.comap_map_eq_self_of_injective (embT46_injective e) X,
      h2 (h.trans (by norm_num))]
  sq_a₁ := by
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := square_facts
    refine ⟨e.symm ⟨o1, o1_mem⟩, e.symm ⟨o2, o2_mem⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← orderOf_embT46, embT46_symm]
      exact h1
    · rw [← orderOf_embT46, embT46_symm]
      exact h2
    · refine (embT46_injective e) ?_
      rw [map_mul, map_mul, embT46_symm, embT46_symm]
      exact h3
    · refine (embT46_injective e) ?_
      rw [map_mul, map_mul, embT46_symm, embT46_symm]
      exact h4
    · refine (embT46_injective e) ?_
      rw [map_pow, map_mul, embT46_symm, embT46_symm, embT46_symm]
      exact h5
  sq_a₂ := by
    refine ⟨e.symm ⟨y2, uP_le_T46 sq_j2.1⟩, mem_sup_of_mem_uP e ?_, ?_⟩
    · rw [embT46_symm]
      exact sq_j2.1
    · refine (embT46_injective e) ?_
      rw [map_pow, embT46_symm, embT46_symm]
      exact sq_j2.2
  not_sq_a₃ g hg := by
    refine not_sq_j3 (embT46 e g) (embT46_mem e g) ?_
    rw [← map_pow, hg, embT46_symm]

end Transport

theorem nonempty_toddParabolic
    {Q : Type} [Group Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSU 6 2 1) : Nonempty (ToddParabolic Q) := by
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U62.nonempty_mulEquiv_T46 hQ
  exact ⟨ToddParabolic.ofMulEquivT46 e⟩

end CFSG.EvenSmallLie.UnitarySix
