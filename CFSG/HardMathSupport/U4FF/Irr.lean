module

public import CFSG.HardMathSupport.U4FF.Outer
public import CFSG.HardMathSupport.U4FF.TwoRank
public import CFSG.HardMathSupport.U4FF.Dim
public import CFSG.HardMathSupport.U4FF.Split

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family

variable {S : Type} [CommGroup S] [Finite S] {n : ℕ} {L A : Subgroup (MulAut S)}

theorem sup_invariant {U V : Subgroup S} {f : MulAut S} (hU : ∀ u ∈ U, f u ∈ U ⊔ V)
    (hV : ∀ v ∈ V, f v ∈ U ⊔ V) : ∀ s ∈ U ⊔ V, f s ∈ U ⊔ V := by
  intro s hs
  obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.1 hs
  rw [map_mul]
  exact (U ⊔ V).mul_mem (hU u hu) (hV v hv)

theorem isIrrOn_of_offender (hS : ∀ s : S, s * s = 1) (hL : IsU4Group n L)
    (hA : IsElemAbelian2 A) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S)))
    (hirr : IsIrrOn (L ⊔ A)) (hoff : Nat.card S ≤ Nat.card A * Nat.card (fixV A)) :
    IsIrrOn L := by
  classical
  by_contra hne
  obtain ⟨S₁, hS₁, hS₁0, hS₁top⟩ : ∃ W : Subgroup S, (∀ l ∈ L, ∀ w ∈ W, l w ∈ W) ∧ W ≠ ⊥ ∧
      W ≠ ⊤ := by
    unfold IsIrrOn at hne
    push_neg at hne
    exact hne
  have hn := one_le_of_isU4Group hL
  have hsimple := isSimpleGroup_of_isU4Group hL
  let img : MulAut S → Subgroup S := fun a => S₁.map a.toMonoidHom
  have mem_img : ∀ a s, s ∈ img a ↔ ∃ w ∈ S₁, a w = s := fun a s => by
    simp [img, Subgroup.mem_map]
  have img_mul : ∀ a b, img (a * b) = (img b).map a.toMonoidHom := by
    intro a b
    ext s
    simp only [img, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨b w, ⟨w, hw, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
  have hLN : L ≤ Subgroup.normalizer (L : Set (MulAut S)) := Subgroup.le_normalizer
  have conj_mem : ∀ a ∈ Subgroup.normalizer (L : Set (MulAut S)), ∀ l ∈ L, a⁻¹ * l * a ∈ L := by
    intro a ha l hl
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) l).mp hl
    simpa using this
  have img_L : ∀ a ∈ Subgroup.normalizer (L : Set (MulAut S)), ∀ l ∈ L, ∀ s ∈ img a,
      l s ∈ img a := by
    intro a ha l hl s hs
    obtain ⟨w, hw, rfl⟩ := (mem_img a s).1 hs
    refine (mem_img a _).2 ⟨(a⁻¹ * l * a) w, hS₁ _ (conj_mem a ha l hl) w hw, ?_⟩
    simp [MulAut.mul_apply]
  have img_of_mem : ∀ l ∈ L, img l = S₁ := by
    intro l hl
    ext s
    rw [mem_img]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hS₁ l hl w hw
    · intro hs
      exact ⟨(l⁻¹) s, hS₁ _ (L.inv_mem hl) s hs, by simp [MulAut.mul_apply]⟩
  have img_one : img 1 = S₁ := img_of_mem 1 L.one_mem
  have hdecomp : ∀ x ∈ L ⊔ A, ∃ l ∈ L, ∃ a ∈ A, x = l * a :=
    fun x hx => exists_mul_of_mem_sup_of_normalizer hAN hx
  by_cases hAL : ∀ a ∈ A, a ∈ L
  ·
    have := hirr S₁ (fun x hx w hw => by
      obtain ⟨l, hl, a, ha, rfl⟩ := hdecomp x hx
      rw [MulAut.mul_apply]
      exact hS₁ l hl _ (hS₁ a (hAL a ha) w hw))
    rcases this with h | h
    · exact hS₁0 h
    · exact hS₁top h
  · push_neg at hAL
    obtain ⟨a₀, ha₀A, ha₀L⟩ := hAL
    have ha₀N : a₀ ∈ Subgroup.normalizer (L : Set (MulAut S)) := hAN ha₀A
    have hdich : ∀ a ∈ A, img a = S₁ ∨ img a = img a₀ := by
      intro a ha
      by_cases haL : a ∈ L
      · exact Or.inl (img_of_mem a haL)
      · right
        have hl : a₀⁻¹ * a ∈ L :=
          inv_mul_mem_of_not_mem hS hL hA hAN hirr ha₀A ha ha₀L haL
        have : a = a₀ * (a₀⁻¹ * a) := by group
        rw [this, img_mul, img_of_mem _ hl]
    have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA.1
    have hsup : S₁ ⊔ img a₀ = ⊤ := by
      have hLinv : ∀ l ∈ L, ∀ t ∈ S₁ ⊔ img a₀, l t ∈ S₁ ⊔ img a₀ := fun l hl =>
        sup_invariant (fun u hu => Subgroup.mem_sup_left (hS₁ l hl u hu))
          (fun v hv => Subgroup.mem_sup_right (img_L a₀ ha₀N l hl v hv))
      rcases hirr (S₁ ⊔ img a₀) (fun x hx t ht => by
        obtain ⟨l, hl, a, ha, rfl⟩ := hdecomp x hx
        rw [MulAut.mul_apply]
        refine hLinv l hl _ ?_
        refine sup_invariant (f := a) (fun u hu => ?_) (fun v hv => ?_) t ht
        · have : a u ∈ img a := (mem_img a _).2 ⟨u, hu, rfl⟩
          rcases hdich a ha with h | h
          · rw [h] at this; exact Subgroup.mem_sup_left this
          · rw [h] at this; exact Subgroup.mem_sup_right this
        · obtain ⟨w, hw, rfl⟩ := (mem_img a₀ v).1 hv
          have : (a * a₀) w ∈ img (a * a₀) := (mem_img _ _).2 ⟨w, hw, rfl⟩
          have e : a ((a₀ : MulAut S) w) = (a * a₀) w := by rw [MulAut.mul_apply]
          rw [e]
          rcases hdich (a * a₀) (A.mul_mem ha ha₀A) with h | h
          · rw [h] at this; exact Subgroup.mem_sup_left this
          · rw [h] at this; exact Subgroup.mem_sup_right this) with h | h
      · exfalso
        apply hS₁0
        rw [eq_bot_iff]
        calc S₁ ≤ S₁ ⊔ img a₀ := le_sup_left
          _ = ⊥ := h
      · exact h
    have hinf : S₁ ⊓ img a₀ = ⊥ := by
      have hallA : ∀ y ∈ S₁ ⊓ img a₀, ∀ b ∈ A, y ∈ img b := by
        intro y hy b hb
        rcases hdich b hb with h | h
        · rw [h]; exact hy.1
        · rw [h]; exact hy.2
      rcases hirr (S₁ ⊓ img a₀) (fun x hx y hy => by
        obtain ⟨l, hl, a, ha, rfl⟩ := hdecomp x hx
        rw [MulAut.mul_apply]
        have hay : a y ∈ S₁ ⊓ img a₀ := by
          have key : ∀ b ∈ A, a y ∈ img b := by
            intro b hb
            have hb' : a⁻¹ * b ∈ A := A.mul_mem (A.inv_mem ha) hb
            have h1 : y ∈ img (a⁻¹ * b) := hallA y hy _ hb'
            have h2 : a y ∈ (img (a⁻¹ * b)).map a.toMonoidHom :=
              Subgroup.mem_map_of_mem _ h1
            rw [← img_mul] at h2
            simpa using h2
          exact ⟨by simpa [img_one] using key 1 A.one_mem, key a₀ ha₀A⟩
        exact ⟨hS₁ l hl _ hay.1, img_L a₀ ha₀N l hl _ hay.2⟩) with h | h
      · exact h
      · exfalso
        exact hS₁top (eq_top_iff.2 (fun s _ => by
          have : s ∈ S₁ ⊓ img a₀ := by rw [h]; trivial
          exact this.1))
    have hnt : ∃ l ∈ L, ∃ s ∈ S₁, l s ≠ s := by
      by_contra hcon
      push_neg at hcon
      have hL1 : ∀ l ∈ L, l = 1 := by
        intro l hl
        refine MulEquiv.ext fun s => ?_
        have hs : s ∈ S₁ ⊔ img a₀ := by rw [hsup]; trivial
        obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.1 hs
        obtain ⟨w, hw, rfl⟩ := (mem_img a₀ v).1 hv
        rw [map_mul, hcon l hl u hu]
        have h1 : l (a₀ w) = a₀ (((a₀⁻¹ * l * a₀ : MulAut S)) w) := by
          simp [MulAut.mul_apply]
        rw [h1, hcon _ (conj_mem a₀ ha₀N l hl) w hw]
        rfl
      haveI := hsimple.toNontrivial
      obtain ⟨l, hl⟩ := exists_ne (1 : ↥L)
      exact hl (Subtype.ext (hL1 l l.2))
    have hS₁card : 2 ^ (4 * n + 1) ≤ Nat.card S₁ :=
      two_pow_le_card_of_nontrivial_action hS hL S₁ hS₁ hnt
    have hsplit := card_split a₀ S₁ hinf hsup
    have ha₀2 : a₀ * a₀ = 1 := by simpa [sq] using hA.2 a₀ ha₀A
    have hfix := card_fixV_le_of_split a₀ ha₀2 S₁ hinf hsup (A := A) (E := A ⊓ L) hAc ha₀A
      inf_le_left (fun b hb x hx => hS₁ b hb.2 x hx)
    set C : Subgroup S := S₁ ⊓ fixV (A ⊓ L) with hC
    have hC1 : Nat.card S₁ * Nat.card S₁ ≤ Nat.card A * Nat.card C := by
      calc Nat.card S₁ * Nat.card S₁ = Nat.card S := by rw [hsplit, sq]
        _ ≤ Nat.card A * Nat.card (fixV A) := hoff
        _ ≤ Nat.card A * Nat.card C := Nat.mul_le_mul_left _ hfix
    have hCle : Nat.card C ≤ Nat.card S₁ := by
      have : C.subgroupOf S₁ ≤ ⊤ := le_top
      calc Nat.card C = Nat.card (C.subgroupOf S₁) :=
            (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
        _ ≤ Nat.card S₁ := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hAE := card_le_two_mul_inf hS hL hA hAN hirr
    have hE4 : Nat.card ↥(A ⊓ L) ≤ (2 ^ n) ^ 4 := by
      refine card_le_q4_of_elemAbelian hL ⟨fun a ha b hb => hA.1 a ha.1 b hb.1,
        fun a ha => hA.2 a ha.1⟩ inf_le_right
    have hpow : (2 ^ n) ^ 4 = 2 ^ (4 * n) := by rw [← pow_mul]; ring_nf
    have hSpos : 0 < Nat.card S₁ := Nat.card_pos
    by_cases hE : A ⊓ L = ⊥
    ·
      have hE1 : Nat.card ↥(A ⊓ L) = 1 := by rw [hE]; simp
      have hA2 : Nat.card A ≤ 2 := by omega
      have : Nat.card S₁ ≤ 2 := by
        have h3 : Nat.card S₁ * Nat.card S₁ ≤ 2 * Nat.card S₁ :=
          hC1.trans (Nat.mul_le_mul hA2 hCle)
        exact Nat.le_of_mul_le_mul_right h3 hSpos
      have h4 : 2 ^ (4 * n + 1) ≥ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    ·
      obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE
      have hbE : (b : MulAut S) ∈ A ⊓ L := b.2
      have hbL : (b : MulAut S) ∈ L := hbE.2
      have hb1' : (b : MulAut S) ≠ 1 := fun h => hb1 (Subtype.ext h)
      have hnotfix : ∃ s ∈ S₁, (b : MulAut S) s ≠ s := by
        by_contra hcon
        push_neg at hcon
        apply hb1'
        have hinj := actOn_injective hL S₁ hS₁ hnt
        have : actOn S₁ hS₁ ⟨b, hbL⟩ = actOn S₁ hS₁ 1 := by
          refine MulEquiv.ext fun s => Subtype.ext ?_
          exact hcon s s.2
        have := hinj this
        exact congrArg Subtype.val this
      obtain ⟨s, hs, hbs⟩ := hnotfix
      have hsC : s ∉ C := fun hh => hbs (hh.2 b hbE)
      have hCne : C.subgroupOf S₁ ≠ ⊤ := by
        intro htop
        apply hsC
        have : (⟨s, hs⟩ : S₁) ∈ C.subgroupOf S₁ := by rw [htop]; trivial
        exact this
      have hidx : 2 ≤ (C.subgroupOf S₁).index := by
        have h1 : (C.subgroupOf S₁).index ≠ 1 := fun h => hCne (Subgroup.index_eq_one.1 h)
        have h0 : (C.subgroupOf S₁).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        omega
      have hCS : Nat.card C * 2 ≤ Nat.card S₁ := by
        have h1 := (C.subgroupOf S₁).card_mul_index
        have h2 : Nat.card C = Nat.card (C.subgroupOf S₁) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
        calc Nat.card C * 2 ≤ Nat.card C * (C.subgroupOf S₁).index := Nat.mul_le_mul_left _ hidx
          _ = Nat.card S₁ := by rw [h2]; exact h1
      have hA4 : Nat.card A ≤ 2 ^ (4 * n + 1) := by
        calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L) := hAE
          _ ≤ 2 * (2 ^ n) ^ 4 := Nat.mul_le_mul_left _ hE4
          _ = 2 ^ (4 * n + 1) := by rw [hpow, pow_succ]; ring
      have h5 : 2 * (Nat.card S₁ * Nat.card S₁) ≤ Nat.card A * Nat.card S₁ := by
        calc 2 * (Nat.card S₁ * Nat.card S₁) ≤ 2 * (Nat.card A * Nat.card C) :=
              Nat.mul_le_mul_left _ hC1
          _ = Nat.card A * (Nat.card C * 2) := by ring
          _ ≤ Nat.card A * Nat.card S₁ := Nat.mul_le_mul_left _ hCS
      have h6 : 2 * Nat.card S₁ ≤ Nat.card A := by
        have : (2 * Nat.card S₁) * Nat.card S₁ ≤ Nat.card A * Nat.card S₁ := by
          calc (2 * Nat.card S₁) * Nat.card S₁ = 2 * (Nat.card S₁ * Nat.card S₁) := by ring
            _ ≤ _ := h5
        exact Nat.le_of_mul_le_mul_right this hSpos
      have h7 : 2 * 2 ^ (4 * n + 1) ≤ 2 * Nat.card S₁ := Nat.mul_le_mul_left _ hS₁card
      have h8 : 2 * 2 ^ (4 * n + 1) ≤ 2 ^ (4 * n + 1) := by omega
      have h9 : 0 < 2 ^ (4 * n + 1) := by positivity
      omega

end CFSG.HardMathSupport.U4FF
