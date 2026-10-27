module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec5Types

public section

namespace CFSG.ComponentClassification.AS76b.Sec5

variable {V : Type} [AddCommGroup V] {X : Type} [Group X] [DistribMulAction X V]
  {A B : Subgroup X} {R U W : AddSubgroup V}

theorem exists_mem_ne_ne [Finite V] (H : AddSubgroup V) (hH : 2 < Nat.card H) (a b : V) :
    ∃ c ∈ H, c ≠ a ∧ c ≠ b := by
  by_contra hcon
  have hsub : (H : Set V) ⊆ {a, b} := by
    intro c hc
    by_contra hc'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc'
    exact hcon ⟨c, hc, hc'.1, hc'.2⟩
  have h1 := Set.ncard_le_ncard hsub
  have h2 := Set.ncard_insert_le a {b}
  rw [Set.ncard_singleton] at h2
  have h3 : (H : Set V).ncard = Nat.card H := (Nat.card_coe_set_eq _).symm
  omega

namespace Hyp51

variable (h : Hyp51 X A B R U W)
include h

theorem AB_comm {a b : X} (ha : a ∈ A) (hb : b ∈ B) (v : V) : (b * a) • v = (a * b) • v := by
  rw [h.AB_smul ha hb v, mul_smul, h.A_smul ha v, smul_add, smul_add,
    h.B_fix b hb _ (AddSubgroup.mem_sup_left (h.decomp.cR v).2),
    h.B_fix b hb _ (AddSubgroup.mem_sup_right (h.A_W a ha _ (h.decomp.cW v).2))]

theorem symm : Hyp51 X B A R W U where
  two := h.two
  decomp := ⟨by rw [sup_right_comm]; exact h.decomp.sup_eq,
    by rw [sup_comm]; exact h.decomp.inf_R, by rw [inf_comm]; exact h.decomp.inf_U⟩
  two_lt := h.two_lt
  card_eq := h.card_eq.symm
  A_fix := h.B_fix
  B_fix := h.A_fix
  A_W := h.B_U
  B_U := h.A_W
  A_trans := h.B_trans
  B_trans := h.A_trans
  A_free := h.B_free
  B_free := h.A_free
  normal := by
    intro n hn b hb a ha
    obtain ⟨a', ha', b', hb', hab⟩ := h.normal n hn a ha b hb
    refine ⟨b', hb', a', ha', fun v => ?_⟩
    rw [mul_smul, mul_smul, h.AB_comm ha hb, ← mul_smul, ← mul_smul, hab v,
      h.AB_comm ha' hb']
  one := fun T hT hTR => by
    obtain ⟨h1, h2⟩ := h.one T hT hTR
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2 | ⟨h2, h3⟩
    · exact Or.inr (Or.inl h2)
    · exact Or.inl h2
    · exact Or.inr (Or.inr ⟨h3, h2⟩)
  twoU := h.twoW
  twoW := h.twoU
  three := by
    obtain ⟨T, hT, h1, h2, h3⟩ := h.three
    exact ⟨T, hT, h1, h3, h2⟩

theorem R_ne_bot : R ≠ ⊥ := fun hR => by
  have := h.two_lt
  rw [hR, AddSubgroup.card_bot] at this
  omega

theorem U_ne_R : U ≠ R := fun hUR => h.R_ne_bot (by rw [← h.decomp.inf_RU, hUR, inf_idem])

theorem eq_R_or_U [Finite V] (hU : U ∈ members X R) {T : AddSubgroup V} (hT : T ∈ members X R)
    (hle : T ≤ R ⊔ U) : T = R ∨ T = U := by
  rcases h.twoU U hU le_sup_right with ⟨-, hRU⟩ | hUU
  · exact hRU T hT hle
  · rw [inf_idem] at hUU
    have := card_of_mem_members hU
    rw [hUU, AddSubgroup.card_bot] at this
    have := h.two_lt
    omega

theorem le_RU_or_W_le [Finite V] {Z : AddSubgroup V} (hZ : ∀ a ∈ A, ∀ z ∈ Z, a • z ∈ Z) :
    Z ≤ R ⊔ U ∨ W ≤ Z := by
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.1 hcon
  obtain ⟨z, hz, hzRU⟩ := IsConcreteLE.not_le_iff_exists.1 h1
  have hw₀ : (h.decomp.cW z : V) ≠ 0 := fun h0 =>
    hzRU ((h.decomp.cW_eq_zero_iff z).1 (Subtype.ext h0))
  have hz' : z = (h.decomp.cR z : V) + h.decomp.cU z + h.decomp.cW z :=
    (h.decomp.coord_sum z).symm
  have key : ∀ w' ∈ W, w' ≠ 0 → w' + h.decomp.cW z ∈ Z := by
    intro w' hw' hw'0
    obtain ⟨a, ha, haw⟩ := h.A_trans _ (h.decomp.cW z).2 w' hw' hw₀ hw'0
    have haz : a • z = (h.decomp.cR z : V) + h.decomp.cU z + w' := by rw [h.A_smul ha z, haw]
    have he : a • z + z = w' + h.decomp.cW z := by
      calc a • z + z = ((h.decomp.cR z : V) + h.decomp.cU z + w') +
            ((h.decomp.cR z : V) + h.decomp.cU z + h.decomp.cW z) := by rw [haz, ← hz']
        _ = ((h.decomp.cR z : V) + h.decomp.cU z + ((h.decomp.cR z : V) + h.decomp.cU z)) +
            (w' + h.decomp.cW z) := add_add_add_comm _ _ _ _
        _ = w' + h.decomp.cW z := by rw [h.two, zero_add]
    rw [← he]
    exact Z.add_mem (hZ a ha z hz) hz
  apply h2
  intro w hw
  by_cases hw0 : w = 0
  · rw [hw0]
    exact zero_mem Z
  obtain ⟨w₁, hw₁, hw₁0, hw₁w⟩ := exists_mem_ne_ne W h.two_lt_card_W 0 w
  have hw₂ : w + w₁ ≠ 0 := fun h0 => hw₁w (h.eq_of_add_eq_zero' h0).symm
  have e : w₁ + h.decomp.cW z + (w + w₁ + h.decomp.cW z) = w := by
    calc w₁ + h.decomp.cW z + (w + w₁ + h.decomp.cW z) =
          w + (w₁ + w₁) + ((h.decomp.cW z : V) + h.decomp.cW z) := by abel
      _ = w := by rw [h.two, h.two, add_zero, add_zero]
  rw [← e]
  exact Z.add_mem (key w₁ hw₁ hw₁0) (key _ (W.add_mem hw hw₁) hw₂)

theorem A_smul_mem_RW {a : X} (ha : a ∈ A) {v : V} (hv : v ∈ R ⊔ W) : a • v ∈ R ⊔ W := by
  have hU0 : h.decomp.cU v = 0 := (h.decomp.cU_eq_zero_iff v).2 hv
  rw [h.A_smul ha v, hU0, ZeroMemClass.coe_zero, add_zero]
  exact AddSubgroup.add_mem_sup (h.decomp.cR v).2 (h.A_W a ha _ (h.decomp.cW v).2)

variable [Finite V]

theorem img_U_of_img_R (hU : U ∈ members X R) (hW : W ∉ members X R) {n : X}
    (hn : img n R = R) : img n U = U := by
  have hinv : ∀ a ∈ A, ∀ z ∈ img n U, a • z ∈ img n U := by
    intro a ha z hz
    obtain ⟨u, hu, rfl⟩ := mem_img.1 hz
    obtain ⟨a', ha', b', hb', hab⟩ := h.normal n hn a ha 1 B.one_mem
    have he : a • n • u = n • ((n⁻¹ * (a * 1) * n) • u) := by
      rw [mul_one, mul_smul, mul_smul, smul_inv_smul]
    rw [he, hab u]
    apply smul_mem_img
    rw [mul_smul, h.A_fix a' ha' _ (AddSubgroup.mem_sup_right (h.B_U b' hb' u hu))]
    exact h.B_U b' hb' u hu
  rcases h.le_RU_or_W_le hinv with hle | hle
  · rcases h.eq_R_or_U hU (img_mem_members hU n) hle with hR | hU'
    · exact absurd (img_injective n (hR.trans hn.symm)) h.U_ne_R
    · exact hU'
  · have hcard : Nat.card (img n U) ≤ Nat.card W := by
      rw [card_img, h.card_eq]
    have hWmem : W ∈ members X R := by
      rw [AddSubgroup.eq_of_le_of_card_ge hle hcard]
      exact img_mem_members hU n
    exact absurd hWmem hW

theorem img_R_of_img_U (hU : U ∈ members X R) (hW : W ∉ members X R) {x : X}
    (hx : img x U = U) : img x R = R := by
  have : Finite (AddSubgroup V) := Finite.of_injective _ SetLike.coe_injective
  have hwd : ∀ y z : X, img y R = img z R → img y U = img z U := by
    intro y z hyz
    have h1 : img (z⁻¹ * y) R = R := by rw [img_mul, hyz, img_inv_img]
    have h2 := h.img_U_of_img_R hU hW h1
    rw [img_mul] at h2
    calc img y U = img z (img z⁻¹ (img y U)) := (img_img_inv z _).symm
      _ = img z U := by rw [h2]
  let π : members X R → members X R := fun T =>
    ⟨img (Classical.choose T.2) U, img_mem_members hU _⟩
  have hπ : ∀ (T : members X R) (y : X), img y R = T → (π T : AddSubgroup V) = img y U :=
    fun T y hy => hwd _ _ ((Classical.choose_spec T.2).trans hy.symm)
  have hsurj : Function.Surjective π := by
    rintro ⟨S, z, rfl⟩
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : X, img x₀ R = U := hU
    refine ⟨⟨img (z * x₀⁻¹) R, ⟨_, rfl⟩⟩, Subtype.ext ?_⟩
    rw [hπ _ (z * x₀⁻¹) rfl, img_mul, ← hx₀, img_inv_img]
  have hinj := Finite.injective_iff_surjective.2 hsurj
  have hxR : π ⟨img x R, ⟨x, rfl⟩⟩ = π ⟨R, self_mem_members⟩ := by
    apply Subtype.ext
    rw [hπ _ x rfl, hπ _ 1 (img_one R), hx, img_one]
  exact congrArg Subtype.val (hinj hxR)

theorem star (hU : U ∈ members X R) (hW : W ∉ members X R)
    (hT : ∃ T ∈ members X R, T ≠ R ∧ T ≤ R ⊔ W) : False := by
  obtain ⟨T, ⟨x, rfl⟩, hTR, hTle⟩ := hT
  have hTR' : img x R ⊓ R = ⊥ := (h.one _ ⟨x, rfl⟩ hTR).1
  have hTW : img x R ⊓ W = ⊥ := by
    rcases h.twoW _ ⟨x, rfl⟩ hTle with ⟨hTWeq, -⟩ | hTW
    · exact (hW (hTWeq ▸ ⟨x, rfl⟩)).elim
    · exact hTW
  have hBinv : ∀ b ∈ B, ∀ z ∈ img x U, b • z ∈ img x U := by
    intro b hb z hz
    have hbT : img b (img x R) = img x R :=
      img_eq_self_of_fix fun t ht => h.B_fix b hb t (hTle ht)
    have hn : img (x⁻¹ * b * x) R = R := by rw [img_mul, img_mul, hbT, img_inv_img]
    have h2 := h.img_U_of_img_R hU hW hn
    obtain ⟨u, hu, rfl⟩ := mem_img.1 hz
    have he : b • x • u = x • ((x⁻¹ * b * x) • u) := by
      rw [mul_smul, mul_smul, smul_inv_smul]
    rw [he]
    apply smul_mem_img
    rw [← h2]
    exact smul_mem_img hu
  have hxU : img x U ≤ R ⊔ W := by
    rcases h.symm.le_RU_or_W_le hBinv with hle | hle
    · exact hle
    · have hcard : Nat.card (img x U) ≤ Nat.card U := by rw [card_img]
      have hUx := AddSubgroup.eq_of_le_of_card_ge hle hcard
      exact absurd (h.img_R_of_img_U hU hW hUx.symm) hTR
  have hRUx : img x (R ⊔ U) = R ⊔ W := by
    refine AddSubgroup.eq_of_le_of_card_ge (by rw [img_sup]; exact sup_le hTle hxU) ?_
    rw [card_img, h.decomp.card_RU, h.decomp.card_RW, h.card_eq]
  have hmem : ∀ S ∈ members X R, S ≤ R ⊔ W → S = img x R ∨ S = img x U := by
    intro S hS hle
    have hle' : img x⁻¹ S ≤ R ⊔ U := by
      rw [← img_inv_img x (R ⊔ U), hRUx]
      exact img_le_img hle
    rcases h.eq_R_or_U hU (img_mem_members hS x⁻¹) hle' with h1 | h1
    · left
      rw [← h1, img_img_inv]
    · right
      rw [← h1, img_img_inv]
  obtain ⟨t, ht, ht0⟩ := (img x R).bot_or_exists_ne_zero.resolve_left fun hbot => by
    have := card_of_mem_members (⟨x, rfl⟩ : img x R ∈ members X R)
    rw [hbot, AddSubgroup.card_bot] at this
    have := h.two_lt
    omega
  have htU : h.decomp.cU t = 0 := (h.decomp.cU_eq_zero_iff t).2 (hTle ht)
  have htW : (h.decomp.cW t : V) ≠ 0 := fun h0 =>
    not_mem_of_inf_eq_bot hTR' ht ht0 ((h.decomp.mem_R_iff t).2 ⟨htU, Subtype.ext h0⟩)
  obtain ⟨w₁, hw₁, hw₁0, hw₁t⟩ := exists_mem_ne_ne W h.two_lt_card_W 0 (h.decomp.cW t)
  obtain ⟨a, ha, haw⟩ := h.A_trans _ (h.decomp.cW t).2 w₁ hw₁ htW hw₁0
  have haT : img a (img x R) ≠ img x R := by
    intro haT
    have hat : a • t ∈ img x R := by
      rw [← haT]
      exact smul_mem_img ht
    have ht' : (h.decomp.cR t : V) + h.decomp.cW t = t := by
      have := h.decomp.coord_sum t
      rwa [htU, ZeroMemClass.coe_zero, add_zero] at this
    have hat' : a • t = (h.decomp.cR t : V) + w₁ := by
      rw [h.A_smul ha t, haw, htU, ZeroMemClass.coe_zero, add_zero]
    have hsum : t + a • t = h.decomp.cW t + w₁ := by
      calc t + a • t = ((h.decomp.cR t : V) + h.decomp.cW t) + ((h.decomp.cR t : V) + w₁) := by
            rw [hat', ht']
        _ = ((h.decomp.cR t : V) + h.decomp.cR t) + ((h.decomp.cW t : V) + w₁) :=
            add_add_add_comm _ _ _ _
        _ = h.decomp.cW t + w₁ := by rw [h.two, zero_add]
    have hne : (h.decomp.cW t : V) + w₁ ≠ 0 := fun h0 => hw₁t (h.eq_of_add_eq_zero' h0).symm
    refine not_mem_of_inf_eq_bot hTW ((img x R).add_mem ht hat) (hsum ▸ hne) ?_
    rw [hsum]
    exact W.add_mem (h.decomp.cW t).2 hw₁
  have haTle : img a (img x R) ≤ R ⊔ W := fun s hs => by
    obtain ⟨s', hs', rfl⟩ := mem_img.1 hs
    exact h.A_smul_mem_RW ha (hTle hs')
  have haR : img a (img x R) ≠ R := by
    intro haR
    have hR : img a⁻¹ R = R := img_eq_self_of_fix fun r hr =>
      h.A_fix a⁻¹ (A.inv_mem ha) r (AddSubgroup.mem_sup_left hr)
    apply hTR
    rw [← img_inv_img a (img x R), haR, hR]
  rcases hmem R self_mem_members le_sup_left with h1 | h1
  · exact hTR h1.symm
  · rcases hmem _ (img_mem_members ⟨x, rfl⟩ a) haTle with h2 | h2
    · exact haT h2
    · exact haR (h2.trans h1.symm)

end Hyp51

end CFSG.ComponentClassification.AS76b.Sec5
