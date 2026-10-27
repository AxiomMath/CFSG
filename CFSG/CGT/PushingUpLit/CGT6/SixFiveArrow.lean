module

public import CFSG.CGT.PushingUpLit.EightOneBlocksStruct
public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped Pointwise Nat

theorem mem_altStabilizer' {m : ℕ} {F : Finset (Fin m)} {σ : alternatingGroup (Fin m)} :
    σ ∈ altStabilizer m F ↔ ∀ i ∈ F, (σ : Equiv.Perm (Fin m)) i = i := by
  simp only [altStabilizer, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  rfl

theorem range_ofSubtype_compl {k : ℕ} (F : Finset (Fin k)) :
    (alternatingGroup.ofSubtype Fᶜ).range = altStabilizer k F := by
  ext σ
  rw [alternatingGroup.mem_range_ofSubtype_iff, mem_altStabilizer']
  constructor
  · intro h i hi
    by_contra hne
    have := h (Equiv.Perm.mem_support.mpr hne)
    simp [hi] at this
  · intro h x hx
    have hne := Equiv.Perm.mem_support.mp hx
    simp only [Finset.mem_compl]
    exact fun hxF => hne (h x hxF)

theorem altStab_map_of_range_eq {m k : ℕ} (hm : m = 5 ∨ 7 ≤ m) {F₂ : Finset (Fin k)}
    (hcard : F₂ᶜ.card = m) {θ : alternatingGroup (Fin m) →* alternatingGroup (Fin k)}
    (hθ : Function.Injective θ) (hrange : θ.range = altStabilizer k F₂) :
    ∃ τ : Fin m → Fin k, Function.Injective τ ∧ (∀ i, τ i ∉ F₂) ∧
      ∀ F₁ : Finset (Fin m),
        (altStabilizer m F₁).map θ = altStabilizer k (F₂ ∪ F₁.image τ) := by
  classical
  have hcard' : Fintype.card ↥(F₂ᶜ) = m := by rw [Fintype.card_coe]; exact hcard
  let e : Fin m ≃ ↥(F₂ᶜ) := (Fintype.equivFinOfCardEq hcard').symm
  let ε : alternatingGroup (Fin m) →* alternatingGroup (Fin k) :=
    (alternatingGroup.ofSubtype F₂ᶜ).comp e.altCongrHom.toMonoidHom
  have hε : Function.Injective ε :=
    alternatingGroup.ofSubtype_injective.comp e.altCongrHom.injective
  have hεrange : ε.range = altStabilizer k F₂ := by
    rw [← range_ofSubtype_compl F₂]
    ext x
    simp only [MonoidHom.mem_range, ε, MonoidHom.comp_apply]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := e.altCongrHom.surjective y
      exact ⟨z, rfl⟩
  let θe : alternatingGroup (Fin m) ≃* θ.range := MonoidHom.ofInjective hθ
  let εe : alternatingGroup (Fin m) ≃* ε.range := MonoidHom.ofInjective hε
  let c : θ.range ≃* ε.range := MulEquiv.subgroupCongr (hrange.trans hεrange.symm)
  let α : MulAut (alternatingGroup (Fin m)) := (θe.trans c).trans εe.symm
  have hα : ∀ g, ε (α g) = θ g := by
    intro g
    have h1 : εe (α g) = c (θe g) := by simp [α]
    exact congrArg Subtype.val h1
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation hm α
  have hkey : ∀ (g : alternatingGroup (Fin m)) (i : Fin m),
      ((θ g : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) ((e (σ i) : ↥(F₂ᶜ)) : Fin k) =
        ((e (σ ((g : Equiv.Perm (Fin m)) i)) : ↥(F₂ᶜ)) : Fin k) := by
    intro g i
    rw [← hα g]
    show (Equiv.Perm.ofSubtype
      (((e.altCongrHom (α g)) : alternatingGroup ↥(F₂ᶜ)) : Equiv.Perm ↥(F₂ᶜ)))
        ((e (σ i) : ↥(F₂ᶜ)) : Fin k) = _
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ (e (σ i)).2]
    simp [Equiv.altCongrHom_apply_coe, hσ]
  have hfix : ∀ (g : alternatingGroup (Fin m)), ∀ j ∈ F₂,
      ((θ g : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) j = j := by
    intro g j hj
    have : θ g ∈ altStabilizer k F₂ := by
      rw [← hrange]
      exact ⟨g, rfl⟩
    exact mem_altStabilizer'.mp this j hj
  have hinj : Function.Injective (fun i : Fin m => ((e (σ i) : ↥(F₂ᶜ)) : Fin k)) := by
    intro i j hij
    exact σ.injective (e.injective (Subtype.val_injective hij))
  refine ⟨fun i => ((e (σ i) : ↥(F₂ᶜ)) : Fin k), hinj, ?_, ?_⟩
  · intro i hi
    have := (e (σ i)).2
    simp only [Finset.mem_compl] at this
    exact this hi
  · intro F₁
    ext x
    simp only [Subgroup.mem_map, mem_altStabilizer']
    constructor
    · rintro ⟨g, hg, rfl⟩
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact hfix g j hj
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        rw [hkey]
        simp [hg i hi]
    · intro hx
      have hxF₂ : x ∈ θ.range := by
        rw [hrange, mem_altStabilizer']
        exact fun j hj => hx j (Finset.mem_union_left _ hj)
      obtain ⟨g, rfl⟩ := hxF₂
      refine ⟨g, ?_, rfl⟩
      intro i hi
      have h1 := hx _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi))
      rw [hkey] at h1
      exact hinj h1

theorem natCard_alt (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n ! / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp

theorem natCard_alt_small (n : ℕ) (hn : n < 2) : Nat.card (alternatingGroup (Fin n)) = 1 := by
  have : Subsingleton (Fin n) := by
    rcases Nat.lt_succ_iff.mp hn |>.eq_or_lt with rfl | h
    · infer_instance
    · have : n = 0 := by omega
      subst this
      infer_instance
  have : Subsingleton (alternatingGroup (Fin n)) := by
    constructor
    intro a b
    exact Subtype.ext (Subsingleton.elim _ _)
  exact Nat.card_unique

theorem alt_card_le {a b : ℕ} (ha : 5 ≤ a)
    (h : Nat.card (alternatingGroup (Fin a)) ≤ Nat.card (alternatingGroup (Fin b))) : a ≤ b := by
  by_contra hba'
  have hba : b < a := not_le.mp hba'
  rw [natCard_alt a (by omega)] at h
  by_cases hb : 2 ≤ b
  · rw [natCard_alt b hb] at h
    have h1 : b ! < a ! := (Nat.factorial_lt (by omega)).mpr hba
    have h2 : 2 ∣ a ! := Nat.dvd_factorial (by norm_num) (by omega)
    have h3 : 2 ∣ b ! := Nat.dvd_factorial (by norm_num) hb
    omega
  · rw [natCard_alt_small b (by omega)] at h
    have h5 : 120 ≤ a ! := by
      calc 120 = 5 ! := by decide
        _ ≤ a ! := Nat.factorial_le ha
    have h2 : 2 ∣ a ! := Nat.dvd_factorial (by norm_num) (by omega)
    omega

theorem alt_card_inj {a b : ℕ} (ha : 5 ≤ a)
    (h : Nat.card (alternatingGroup (Fin a)) = Nat.card (alternatingGroup (Fin b))) : a = b := by
  have h1 : a ≤ b := alt_card_le ha h.le
  exact le_antisymm h1 (alt_card_le (by omega) h.ge)

theorem five_le_of_isSimple {Q : Type} [Group Q] {m : ℕ} (iso : Q ≃* alternatingGroup (Fin m))
    (hs : IsSimpleGroup Q) (hnab : ∃ a b : Q, a * b ≠ b * a) : 5 ≤ m := by
  by_contra hm
  have hm' : m ≤ 4 := by omega
  have hsolv : Group.IsSolvable (alternatingGroup (Fin m)) :=
    alternatingGroup.isSolvable (by simpa using hm')
  have hQ : Group.IsSolvable Q :=
    Group.isSolvable_of_surjective (f := iso.symm.toMonoidHom) iso.symm.surjective
  obtain ⟨a, b, hab⟩ := hnab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := Q)).mpr hQ a b)

theorem deg_ne_six {Y : Type} [Group Y] [Finite Y] (hY : InClassX Y) {m : ℕ}
    (iso : (Y ⧸ pCore 2 Y) ≃* alternatingGroup (Fin m)) : m ≠ 6 := by
  rintro rfl
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [natCard_alt 6 (by norm_num)]
    decide
  have hQ : Nat.card (Y ⧸ pCore 2 Y) = 360 := by rw [Nat.card_congr iso.toEquiv, h360]
  rcases hY.2 with ⟨a, ha, iso', -⟩ | ⟨b, hb, iso', -⟩
  · have h1 : Nat.card (Y ⧸ pCore 2 Y) = Nat.card (alternatingGroup (Fin (2 * a + 1))) :=
      Nat.card_congr iso'.toEquiv
    rw [hQ, natCard_alt (2 * a + 1) (by omega)] at h1
    have h2 : 2 ∣ (2 * a + 1)! := Nat.dvd_factorial (by norm_num) (by omega)
    have h5 : (5 : ℕ)! = 120 := by norm_num [Nat.factorial]
    have h7 : (7 : ℕ)! = 5040 := by norm_num [Nat.factorial]
    rcases Nat.lt_or_ge (2 * a + 1) 6 with hlt | hge
    · have := Nat.factorial_le (show 2 * a + 1 ≤ 5 by omega)
      omega
    · have := Nat.factorial_le (show 7 ≤ 2 * a + 1 by omega)
      omega
  · have h1 : Nat.card (Y ⧸ pCore 2 Y) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 b)) :=
      Nat.card_congr iso'.toEquiv
    rw [hQ, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      GaloisField.card 2 b (by omega)] at h1
    by_cases hb4 : 4 ≤ b
    · have h16 : 16 ≤ 2 ^ b := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb4
      have h255 : 255 ≤ (2 ^ b) ^ 2 - 1 := by
        have : 256 ≤ (2 ^ b) ^ 2 := by nlinarith
        omega
      have : 16 * 255 ≤ 2 ^ b * ((2 ^ b) ^ 2 - 1) := Nat.mul_le_mul h16 h255
      omega
    · have hb3 : b ≤ 3 := by omega
      interval_cases b <;> norm_num at h1

theorem ker_comp_inclusion_le_pCore {G : Type} [Group G] [Finite G] {Y Z : Subgroup G}
    (hYZ : Y ≤ Z) {B : Type*} [Group B] (Φ : ↥Z →* B) (hΦ : Φ.ker ≤ pCore 2 ↥Z) :
    (Φ.comp (Subgroup.inclusion hYZ)).ker ≤ pCore 2 ↥Y := by
  have hn : ((pCore 2 ↥Z).comap (Subgroup.inclusion hYZ)).Normal :=
    (pCore_normal (p := 2)).comap _
  have hp : IsPGroup 2 ((pCore 2 ↥Z).comap (Subgroup.inclusion hYZ)) :=
    (pCore_isPGroup (p := 2)).comap_of_injective _ (Subgroup.inclusion_injective hYZ)
  have hle : (pCore 2 ↥Z).comap (Subgroup.inclusion hYZ) ≤ pCore 2 ↥Y := le_sSup ⟨hn, hp⟩
  intro y hy
  exact hle (hΦ hy)

theorem card_quot_pCore_le {A : Type} [Group A] [Finite A] {B : Type*} [Group B] (f : A →* B)
    (hf : Function.Surjective f) (hker : f.ker ≤ pCore 2 A) :
    Nat.card (A ⧸ pCore 2 A) ≤ Nat.card B := by
  have : Finite B := Finite.of_surjective f hf
  have h1 : (pCore 2 A).index ∣ f.ker.index := Subgroup.index_dvd_of_le hker
  have h2 : f.ker.index = Nat.card B := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf]
    exact Subgroup.card_top
  rw [h2] at h1
  exact Nat.le_of_dvd Nat.card_pos h1

theorem natCard_altStabilizer {m k : ℕ} {F : Finset (Fin k)} (h : Fᶜ.card = m) :
    Nat.card ↥(altStabilizer k F) = Nat.card ↥(alternatingGroup (Fin m)) := by
  classical
  have hcard' : Fintype.card ↥(Fᶜ) = m := by rw [Fintype.card_coe]; exact h
  let e : Fin m ≃ ↥(Fᶜ) := (Fintype.equivFinOfCardEq hcard').symm
  rw [← range_ofSubtype_compl F]
  have h1 : Nat.card ↥(alternatingGroup.ofSubtype Fᶜ).range = Nat.card ↥(alternatingGroup ↥(Fᶜ)) :=
    (Nat.card_congr (MonoidHom.ofInjective
      (alternatingGroup.ofSubtype_injective (s := Fᶜ))).toEquiv).symm
  rw [h1]
  exact (Nat.card_congr e.altCongrHom.toEquiv).symm

theorem arrow_trans_of_inClassX {G : Type} [Group G] [Finite G] {X Y Z : Subgroup G}
    (hX : InClassX ↥X) (hY : InClassX ↥Y) (h1 : Arrow X Y) (h2 : Arrow Y Z) : Arrow X Z := by
  classical
  by_cases hXY : X = Y
  · rw [hXY]
    exact h2
  by_cases hYZ : Y = Z
  · rw [← hYZ]
    exact h1
  have h1' := h1
  rcases h1 with h1 | ⟨n, m, ⟨ψX⟩, φY, F₁, hF₁, hU₁, hXY', himg₁⟩
  · exact absurd h1 hXY
  rcases h2 with h2 | ⟨m', k, ⟨ψY⟩, φZ, F₂, hF₂, hU₂, hYZ', himg₂⟩
  · exact absurd h2 hYZ
  obtain ⟨hsimple, hnab⟩ := arrow_top_simple hX hY hXY' hXY h1'
  have hm5 : 5 ≤ m := five_le_of_isSimple φY hsimple hnab
  have hm6 : m ≠ 6 := deg_ne_six hY φY
  have hm : m = 5 ∨ 7 ≤ m := by omega
  have hmm' : m = m' :=
    alt_card_inj hm5 ((Nat.card_congr φY.toEquiv).symm.trans (Nat.card_congr ψY.toEquiv))
  let ΦY : ↥Y →* alternatingGroup (Fin m) :=
    φY.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥Y))
  let ΦZ : ↥Z →* alternatingGroup (Fin k) :=
    φZ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥Z))
  have hΦY : Function.Surjective ΦY := φY.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerY : ΦY.ker = pCore 2 ↥Y := by
    ext y
    simp only [MonoidHom.mem_ker, ΦY, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      EmbeddingLike.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hkerZ : ΦZ.ker = pCore 2 ↥Z := by
    ext y
    simp only [MonoidHom.mem_ker, ΦZ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      EmbeddingLike.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let f : ↥Y →* alternatingGroup (Fin k) := ΦZ.comp (Subgroup.inclusion hYZ')
  have hkerf : f.ker ≤ pCore 2 ↥Y := ker_comp_inclusion_le_pCore hYZ' ΦZ hkerZ.le
  have himg₁' : (X.subgroupOf Y).map ΦY = altStabilizer m F₁ := by
    rw [← himg₁, Subgroup.map_map]
  have himg₂' : (Y.subgroupOf Z).map ΦZ = altStabilizer k F₂ := by
    rw [← himg₂, Subgroup.map_map]
  have hrangef : f.range = altStabilizer k F₂ := by
    rw [← himg₂', MonoidHom.range_comp, Subgroup.inclusion_range]
  have hmk : m ≤ k := by
    by_contra hk
    have hk' : k < m := not_le.mp hk
    have hF₂0 : F₂.card = 0 := by omega
    have hF₂e : F₂ = ∅ := Finset.card_eq_zero.mp hF₂0
    have htop : f.range = ⊤ := by
      rw [hrangef, hF₂e]
      ext σ
      simp [mem_altStabilizer']
    have hfs : Function.Surjective f := MonoidHom.range_eq_top.mp htop
    have h3 := card_quot_pCore_le f hfs hkerf
    rw [Nat.card_congr φY.toEquiv] at h3
    have h4 := alt_card_le hm5 h3
    omega
  have hnm : n ≤ m := by
    by_contra hn
    have hn' : m < n := not_le.mp hn
    have hF₁0 : F₁.card = 0 := by omega
    have hF₁e : F₁ = ∅ := Finset.card_eq_zero.mp hF₁0
    let g : ↥X →* alternatingGroup (Fin m) := ΦY.comp (Subgroup.inclusion hXY')
    have hrg : g.range = ⊤ := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range, himg₁', hF₁e]
      ext σ
      simp [mem_altStabilizer']
    have hgs : Function.Surjective g := MonoidHom.range_eq_top.mp hrg
    have hkerg : g.ker ≤ pCore 2 ↥X := ker_comp_inclusion_le_pCore hXY' ΦY hkerY.le
    have h3 := card_quot_pCore_le g hgs hkerg
    rw [Nat.card_congr ψX.toEquiv] at h3
    have h4 := alt_card_le (by omega : 5 ≤ n) h3
    omega
  have hcompl : F₂ᶜ.card = m := by
    rw [Finset.card_compl, Fintype.card_fin, hF₂]
    omega
  have hkerfeq : f.ker = pCore 2 ↥Y := by
    refine le_antisymm hkerf ?_
    have hidxf : f.ker.index = Nat.card ↥(altStabilizer k F₂) := by
      rw [Subgroup.index_ker, hrangef]
    have hidxY : (pCore 2 ↥Y).index = Nat.card ↥(alternatingGroup (Fin m)) := by
      rw [← hkerY, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hΦY]
      exact Subgroup.card_top
    have hidx : f.ker.index = (pCore 2 ↥Y).index := by
      rw [hidxf, hidxY, natCard_altStabilizer hcompl]
    have hc1 := Subgroup.index_mul_card (H := f.ker)
    have hc2 := Subgroup.index_mul_card (H := pCore 2 ↥Y)
    have hpos : 0 < (pCore 2 ↥Y).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hidx] at hc1
    have hcard : Nat.card ↥(pCore 2 ↥Y) ≤ Nat.card ↥f.ker :=
      (Nat.mul_left_cancel hpos (hc2.trans hc1.symm)).le
    exact fun x hx => by
      have := Subgroup.eq_of_le_of_card_ge hkerf hcard
      rw [this]
      exact hx
  have hker_le : ΦY.ker ≤ f.ker := by rw [hkerY, hkerfeq]
  let θ₀ : alternatingGroup (Fin m) →* alternatingGroup (Fin k) :=
    ΦY.liftOfSurjective hΦY ⟨f, hker_le⟩
  have hθ₀ : ∀ y, θ₀ (ΦY y) = f y := fun y =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨f, hker_le⟩ y
  have hθ₀inj : Function.Injective θ₀ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨y, rfl⟩ := hΦY a
    rw [hθ₀] at ha
    have hy : y ∈ f.ker := ha
    rw [hkerfeq, ← hkerY] at hy
    exact hy
  have hθ₀range : θ₀.range = altStabilizer k F₂ := by
    rw [← hrangef]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨y, rfl⟩ := hΦY a
      exact ⟨y, (hθ₀ y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨ΦY y, hθ₀ y⟩
  obtain ⟨τ, hτinj, hτF, hτ⟩ := altStab_map_of_range_eq hm hcompl hθ₀inj hθ₀range
  have hdisj : Disjoint F₂ (F₁.image τ) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx'
    exact hτF i hx
  refine Or.inr ⟨n, k, ⟨ψX⟩, φZ, F₂ ∪ F₁.image τ, ?_, hU₁.trans hU₂, hXY'.trans hYZ', ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hτinj, hF₂, hF₁]
    omega
  · have hXZ : (X.subgroupOf Y).map (Subgroup.inclusion hYZ') = X.subgroupOf Z := by
      ext z
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hz
        exact ⟨⟨z.1, hXY' hz⟩, hz, rfl⟩
    have hfθ : f = θ₀.comp ΦY := MonoidHom.ext fun y => (hθ₀ y).symm
    rw [Subgroup.map_map, ← hXZ, Subgroup.map_map]
    have : (ΦZ.comp (Subgroup.inclusion hYZ')) = f := rfl
    show (X.subgroupOf Y).map (ΦZ.comp (Subgroup.inclusion hYZ')) = _
    rw [this, hfθ, ← Subgroup.map_map, himg₁', hτ]

end CFSG.CGT.PushingUpLit.CGT6
