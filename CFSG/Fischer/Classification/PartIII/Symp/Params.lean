module

public import CFSG.Fischer.Classification.PartIII.Symp.Count
public import CFSG.Fischer.Uniq.Counting

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X : Type} [Group X] {E : Set X}

namespace LocalSymp

theorem even_ncard_of_involution {α : Type*} [Finite α] {S : Set α} (τ : α → α)
    (hS : ∀ x ∈ S, τ x ∈ S) (hτ : ∀ x ∈ S, τ (τ x) = x) (hfix : ∀ x ∈ S, τ x ≠ x) :
    Even S.ncard := by
  classical
  have := Fintype.ofFinite α
  let σ : Equiv.Perm S :=
    { toFun := fun x => ⟨τ x, hS x x.2⟩
      invFun := fun x => ⟨τ x, hS x x.2⟩
      left_inv := fun x => Subtype.ext (hτ x x.2)
      right_inv := fun x => Subtype.ext (hτ x x.2) }
  have h2 : σ ^ 2 = 1 := Equiv.ext fun x => Subtype.ext (hτ x x.2)
  have hsupp : σ.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true, ne_eq]
    exact fun h => hfix x x.2 (congrArg Subtype.val h)
  have := Equiv.Perm.two_dvd_card_support h2
  rw [hsupp, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at this
  exact even_iff_two_dvd.2 this

end LocalSymp

open LocalSymp

section Lift

variable (hP : Pair X E) (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup (commutator X))
  {d : X} (hd : d ∈ E)
include hP hZ hS hd

theorem Pair.ncard_val_image_preimage {T : Set (LocalQuotient E d)}
    (hT : T ⊆ LocalImages E d) :
    (Subtype.val '' (starImage E d ⁻¹' T)).ncard = T.ncard := by
  have := Pair.finite hP
  rw [Set.ncard_image_of_injective _ Subtype.val_injective,
    ← Set.ncard_image_of_injective _ (Pair.starImage_injective_of_simple hP hZ hS hd),
    Set.image_preimage_eq_of_subset (by rw [range_starImage]; exact hT)]

theorem Pair.ncard_muSet_inter_localClass (x y : LocalClass E d) :
    (muSet E x y ∩ LocalClass E d).ncard =
      (muSet (LocalImages E d) (starImage E d x) (starImage E d y)).ncard := by
  have hinj := Pair.starImage_injective_of_simple hP hZ hS hd
  rw [← Pair.ncard_val_image_preimage hP hZ hS hd (fun q hq => hq.1.1)]
  congr 1
  ext g
  constructor
  · rintro ⟨⟨⟨hgE, hgx, hgxc⟩, ⟨-, hgy, hgyc⟩⟩, hgd⟩
    refine ⟨⟨g, hgd⟩, ⟨⟨range_starImage (E := E) d ▸ ⟨_, rfl⟩, fun h => hgx ?_,
      (Pair.starImage_commute_iff hP ⟨g, hgd⟩ x).2 hgxc⟩, ⟨range_starImage (E := E) d ▸
      ⟨_, rfl⟩, fun h => hgy ?_, (Pair.starImage_commute_iff hP ⟨g, hgd⟩ y).2 hgyc⟩⟩, rfl⟩
    · exact congrArg Subtype.val (hinj h)
    · exact congrArg Subtype.val (hinj h)
  · rintro ⟨f, ⟨⟨-, hfx, hfxc⟩, ⟨-, hfy, hfyc⟩⟩, rfl⟩
    exact ⟨⟨⟨f.2.1, fun h => hfx (congrArg _ (Subtype.ext h)),
      (Pair.starImage_commute_iff hP f x).1 hfxc⟩, ⟨f.2.1, fun h => hfy (congrArg _
        (Subtype.ext h)), (Pair.starImage_commute_iff hP f y).1 hfyc⟩⟩, f.2⟩

theorem Pair.ncard_inter_localClass (f : LocalClass E d) :
    (LocalClass E d ∩ LocalClass E f).ncard =
      (LocalClass (LocalImages E d) (starImage E d f)).ncard := by
  have hinj := Pair.starImage_injective_of_simple hP hZ hS hd
  rw [← Pair.ncard_val_image_preimage hP hZ hS hd (fun q hq => hq.1)]
  congr 1
  ext g
  constructor
  · rintro ⟨hgd, hgE, hgf, hgfc⟩
    exact ⟨⟨g, hgd⟩, ⟨range_starImage (E := E) d ▸ ⟨_, rfl⟩,
      fun h => hgf (congrArg Subtype.val (hinj h)),
      (Pair.starImage_commute_iff hP ⟨g, hgd⟩ f).2 hgfc⟩, rfl⟩
  · rintro ⟨g, ⟨-, hgf, hgfc⟩, rfl⟩
    exact ⟨g.2, g.2.1, fun h => hgf (congrArg _ (Subtype.ext h)),
      (Pair.starImage_commute_iff hP g f).1 hgfc⟩

end Lift

section MuSet

theorem Pair.even_ncard_muSet_far (hP : Pair X E) {d c f : X} (hf : f ∈ muSet E d c) :
    Even (muSet E d c ∩ {g | g * f ≠ f * g}).ncard := by
  have := Pair.finite hP
  have hfE := hf.1.1
  refine even_ncard_of_involution (fun g => f * g * f) (fun g hg => ⟨Pair.mul_mul_mem_muSet hP hf
    hg.1, fun h => hg.2 ?_⟩) (fun g _ => Pair.mul_mul_mul_mul hP hfE g) fun g hg h =>
      hg.2 ((Pair.mul_mul_eq_self_iff hP hfE g).1 h).symm
  have h1 : f * g * f * f = f * g := by rw [mul_assoc (f * g), Pair.mul_self hP hfE, mul_one]
  have h2 : f * (f * g * f) = g * f := by simp only [← mul_assoc, Pair.mul_self hP hfE, one_mul]
  rw [h1, h2] at h
  exact h.symm

theorem Pair.ncard_muSet_eq_add (hP : Pair X E) {d c f : X} (hf : f ∈ muSet E d c) :
    (muSet E d c).ncard = 1 + (muSet E d c ∩ LocalClass E f).ncard +
      (muSet E d c ∩ {g | g * f ≠ f * g}).ncard := by
  have := Pair.finite hP
  have hM : muSet E d c = insert f ((muSet E d c ∩ LocalClass E f) ∪
      (muSet E d c ∩ {g | g * f ≠ f * g})) := by
    ext g
    constructor
    · intro hg
      by_cases hgf : g = f
      · exact Or.inl hgf
      · by_cases hc : g * f = f * g
        · exact Or.inr (Or.inl ⟨hg, hg.1.1, hgf, hc⟩)
        · exact Or.inr (Or.inr ⟨hg, hc⟩)
    · rintro (rfl | ⟨hg, -⟩ | ⟨hg, -⟩)
      · exact hf
      · exact hg
      · exact hg
  have hf' : f ∉ (muSet E d c ∩ LocalClass E f) ∪ (muSet E d c ∩ {g | g * f ≠ f * g}) := by
    rintro (⟨-, -, h, -⟩ | ⟨-, h⟩)
    · exact h rfl
    · exact h rfl
  have hdisj : Disjoint (muSet E d c ∩ LocalClass E f) (muSet E d c ∩ {g | g * f ≠ f * g}) :=
    Set.disjoint_left.2 fun g h1 h2 => h2.2 h1.2.2.2
  conv_lhs => rw [hM]
  rw [Set.ncard_insert_of_notMem hf', Set.ncard_union_eq hdisj]
  ring

theorem Pair.ncard_muSet_inter_localClass_eq (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {d c f : X} (hd : d ∈ E) (hc : c ∈ E)
    (hcd : c * d ≠ d * c) (hf : f ∈ muSet E d c) {μH : ℕ}
    (hμH : ∀ q ∈ LocalImages E d, ∀ r ∈ LocalImages E d, q * r ≠ r * q →
      (muSet (LocalImages E d) q r).ncard = μH) :
    (muSet E d c ∩ LocalClass E f).ncard = μH := by
  have := Pair.finite hP
  obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj hP hf.1.1 hd)
  have hd' : g * d * g⁻¹ ∈ LocalClass E d := by
    have := (Pair.conj_mem_localClass_iff hP g (e := f) (f := d)).2
      ⟨hd, hf.1.2.1.symm, hf.1.2.2.symm⟩
    rwa [hg] at this
  have hc' : g * c * g⁻¹ ∈ LocalClass E d := by
    have := (Pair.conj_mem_localClass_iff hP g (e := f) (f := c)).2
      ⟨hc, hf.2.2.1.symm, hf.2.2.2.symm⟩
    rwa [hg] at this
  have hdc : g * d * g⁻¹ * (g * c * g⁻¹) ≠ g * c * g⁻¹ * (g * d * g⁻¹) := by
    rw [Ne, conj_commute_iff]
    exact fun h => hcd h.symm
  have himg : (fun s => g * s * g⁻¹) '' (muSet E d c ∩ LocalClass E f) =
      muSet E (g * d * g⁻¹) (g * c * g⁻¹) ∩ LocalClass E d := by
    rw [Set.image_inter (conj_injective g), Pair.image_conj_muSet hP, Pair.image_conj_localClass hP,
      hg]
  rw [← Set.ncard_image_of_injective _ (conj_injective g), himg,
    Pair.ncard_muSet_inter_localClass hP hZ hS hd ⟨_, hd'⟩ ⟨_, hc'⟩]
  refine hμH _ (range_starImage (E := E) d ▸ ⟨_, rfl⟩) _ (range_starImage (E := E) d ▸ ⟨_, rfl⟩)
    fun h => hdc ((Pair.starImage_commute_iff hP ⟨_, hd'⟩ ⟨_, hc'⟩).1 h)

end MuSet

theorem Pair.params_basic (hH : Hyp X E) (hna : NonabelianCommutator X)
    (hnot : ¬ IsSymplecticType E) {d : X} (hd : d ∈ E)
    (hsymp : IsSymplecticType (LocalImages E d)) {lam : ℕ}
    (hlam : ∀ q ∈ LocalImages E d, (LocalClass (LocalImages E d) q).ncard = lam) :
    ∃ μ : ℕ, (∀ c ∈ E, c * d ≠ d * c → (muSet E d c).ncard = μ) ∧
      4 * μ ≤ (LocalImages E d).ncard ∧
      μ * {c | c ∈ E ∧ c * d ≠ d * c}.ncard =
        (LocalImages E d).ncard * ((LocalImages E d).ncard - 1 - lam) ∧
      E.ncard = 1 + (LocalImages E d).ncard + {c | c ∈ E ∧ c * d ≠ d * c}.ncard := by
  obtain ⟨hP, hZ, hS⟩ := hH
  have := Pair.finite hP
  obtain ⟨c₀, hc₀, hc₀d⟩ : ∃ c ∈ E, c * d ≠ d * c := by
    by_contra! h
    have hdZ : d ∈ Subgroup.center X := (Pair.mem_center_iff hP).2 h
    rw [hZ, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  set μ := (muSet E d c₀).ncard with hμdef
  have hμ : ∀ c ∈ E, c * d ≠ d * c → (muSet E d c).ncard = μ := by
    intro c hc hcd
    obtain ⟨g, hgd, hgc⟩ := Pair.exists_conj_pair_of_not_commute hP hZ hS hna hd hc hd hc₀
      (fun h => hcd h.symm) fun h => hc₀d h.symm
    calc (muSet E d c).ncard = ((fun s => g * s * g⁻¹) '' muSet E d c).ncard :=
          (Set.ncard_image_of_injective _ (conj_injective g)).symm
      _ = μ := by rw [Pair.image_conj_muSet hP, hgd, hgc]
  refine ⟨μ, hμ, ?_, ?_, ?_⟩
  ·
    obtain ⟨a, ha, b, hb, z, hz, hab, hzl⟩ : ∃ a ∈ E, ∃ b ∈ E, ∃ z ∈ E, a * b ≠ b * a ∧
        ¬ (z * a = a * z ∨ z * b = b * z ∨ z * (a * b * a) = a * b * a * z) := by
      by_contra! h
      exact hnot fun a ha b hb z hz hab => by
        by_contra h'
        exact h' (by simpa using h a ha b hb z hz hab)
    push Not at hzl
    obtain ⟨hza, hzb, hzl⟩ := hzl
    have hμa : ∀ q ∈ E, a * q ≠ q * a → (muSet E a q).ncard = μ := by
      intro q hq haq
      obtain ⟨g, hga, hgq⟩ := Pair.exists_conj_pair_of_not_commute hP hZ hS hna ha hq hd hc₀
        haq fun h => hc₀d h.symm
      rw [hμdef, ← hga, ← hgq, ← Pair.image_conj_muSet hP,
        Set.ncard_image_of_injective _ (conj_injective g)]
    have h4 := Pair.four_mul_ncard_muSet_le hP hd hsymp ha hb hz hab (fun h => hza h.symm)
      (fun h => hzb h.symm) hzl hμa
    rwa [Pair.ncard_localClass_eq hP ha hd, ← Pair.ncard_localImages hP hZ hS hd] at h4
  ·
    have hk : (LocalClass E d).ncard = (LocalImages E d).ncard :=
      (Pair.ncard_localImages hP hZ hS hd).symm
    have h := Pair.card_A hP hd (k := (LocalImages E d).ncard) (l := lam) (m := μ)
      (by rw [Nat.card_coe_set_eq, hk])
      (fun f hf => by rw [Nat.card_coe_set_eq, Pair.ncard_localClass_eq hP hf.1 hd, hk])
      (fun f hf => by
        rw [Nat.card_coe_set_eq, Pair.ncard_inter_localClass hP hZ hS hd ⟨f, hf⟩]
        exact hlam _ (range_starImage (E := E) d ▸ ⟨_, rfl⟩))
      (fun c hc hcd => by rw [Nat.card_coe_set_eq]; exact hμ c hc hcd)
    rw [Nat.card_coe_set_eq] at h
    rw [mul_comm]
    exact h
  · have h := Pair.card_eq_add hP hd
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      ← Pair.ncard_localImages hP hZ hS hd] at h
    exact h

theorem Pair.params_of_local (hH : Hyp X E) (hna : NonabelianCommutator X)
    (hnot : ¬ IsSymplecticType E) {d : X} (hd : d ∈ E)
    (hsymp : IsSymplecticType (LocalImages E d)) {lam μH : ℕ}
    (hlam : ∀ q ∈ LocalImages E d, (LocalClass (LocalImages E d) q).ncard = lam)
    (hμH : ∀ q ∈ LocalImages E d, ∀ r ∈ LocalImages E d, q * r ≠ r * q →
      (muSet (LocalImages E d) q r).ncard = μH) :
    ∃ μ δ : ℕ, Even δ ∧ μ = 1 + μH + δ ∧
      (∀ c ∈ E, c * d ≠ d * c → (muSet E d c).ncard = μ) ∧
      4 * μ ≤ (LocalImages E d).ncard ∧
      μ * {c | c ∈ E ∧ c * d ≠ d * c}.ncard =
        (LocalImages E d).ncard * ((LocalImages E d).ncard - 1 - lam) ∧
      E.ncard = 1 + (LocalImages E d).ncard + {c | c ∈ E ∧ c * d ≠ d * c}.ncard := by
  obtain ⟨μ, hμ, h4, hA, hE⟩ := Pair.params_basic hH hna hnot hd hsymp hlam
  obtain ⟨hP, hZ, hS⟩ := hH
  have hconn := Pair.connected_of_nonabelian hP hS hna
  obtain ⟨c₀, hc₀, hc₀d⟩ : ∃ c ∈ E, c * d ≠ d * c := by
    by_contra! h
    have hdZ : d ∈ Subgroup.center X := (Pair.mem_center_iff hP).2 h
    rw [hZ, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  obtain ⟨f, hf⟩ := Pair.muSet_nonempty hP hconn hd hc₀ hc₀d
  have hdec := Pair.ncard_muSet_eq_add hP hf
  rw [Pair.ncard_muSet_inter_localClass_eq hP hZ hS hd hc₀ hc₀d hf hμH, hμ c₀ hc₀ hc₀d] at hdec
  exact ⟨μ, _, Pair.even_ncard_muSet_far hP hf, hdec, hμ, h4, hA, hE⟩

end CFSG.Fischer.Classification
