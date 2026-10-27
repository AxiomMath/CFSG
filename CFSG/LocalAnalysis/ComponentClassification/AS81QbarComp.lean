module

public import CFSG.LocalAnalysis.ComponentClassification.AS81QbarType
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.ComponentClassification.AS81.Qbar

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalCores CFSG.ABGLocalTools

variable {Y : Type} [Group Y]

@[expose] noncomputable def compPerm [Finite Y] (e : MulAut Y) : Equiv.Perm (ComponentIndex Y) where
  toFun K := ⟨K.1.map e.toMonoidHom, isComponent_map_mulEquiv e K.2⟩
  invFun K := ⟨K.1.map e.symm.toMonoidHom, isComponent_map_mulEquiv e.symm K.2⟩
  left_inv K := Subtype.ext (map_map_symm e K.1)
  right_inv K := Subtype.ext (by simpa only [MulEquiv.symm_symm] using map_map_symm e.symm K.1)

@[expose] noncomputable def compPermHom [Finite Y] : MulAut Y →* Equiv.Perm (ComponentIndex Y) where
  toFun := compPerm
  map_one' := Equiv.ext fun K => Subtype.ext (by
    ext x
    change x ∈ K.1.map (1 : MulAut Y).toMonoidHom ↔ x ∈ K.1
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩)
  map_mul' e f := Equiv.ext fun K => Subtype.ext (by
    change K.1.map (e * f).toMonoidHom = (K.1.map f.toMonoidHom).map e.toMonoidHom
    rw [Subgroup.map_map]
    rfl)

theorem compPermHom_apply [Finite Y] (e : MulAut Y) (K : ComponentIndex Y) :
    (compPermHom e K).1 = K.1.map e.toMonoidHom :=
  rfl

theorem apply_mem_of_compPerm [Finite Y] {e : MulAut Y} {K : ComponentIndex Y}
    (he : compPerm e K = K) {x : Y} (hx : x ∈ K.1) : e x ∈ K.1 := by
  have h1 : e x ∈ (compPerm e K).1 := ⟨x, hx, rfl⟩
  rwa [he] at h1

theorem mk_eq_of_sameOn {K : Subgroup Y} {t t' : K}
    (h : ∀ x ∈ K, (t : Y)⁻¹ * x * t = (t' : Y)⁻¹ * x * t') :
    (QuotientGroup.mk t : K ⧸ center K) = QuotientGroup.mk t' := by
  rw [QuotientGroup.eq, mem_center_iff]
  intro g
  apply Subtype.ext
  simp only [coe_mul, coe_inv]
  have h2 := h ((t : Y) * g * (t : Y)⁻¹) (K.mul_mem (K.mul_mem t.2 g.2) (K.inv_mem t.2))
  calc (g : Y) * ((t : Y)⁻¹ * t') =
      (t : Y)⁻¹ * t' * ((t' : Y)⁻¹ * ((t : Y) * g * (t : Y)⁻¹) * t') := by group
    _ = (t : Y)⁻¹ * t' * ((t : Y)⁻¹ * ((t : Y) * g * (t : Y)⁻¹) * t) := by rw [← h2]
    _ = (t : Y)⁻¹ * t' * g := by group

theorem sameOn_of_mk_eq {K : Subgroup Y} {t t' : K}
    (h : (QuotientGroup.mk t : K ⧸ center K) = QuotientGroup.mk t') :
    ∀ x ∈ K, (t : Y)⁻¹ * x * t = (t' : Y)⁻¹ * x * t' := by
  rw [QuotientGroup.eq, mem_center_iff] at h
  intro x hx
  have h1 := congrArg Subtype.val
    (h ⟨(t : Y)⁻¹ * x * t, K.mul_mem (K.mul_mem (K.inv_mem t.2) hx) t.2⟩)
  simp only [coe_mul, coe_inv] at h1
  calc (t : Y)⁻¹ * x * t =
      ((t : Y)⁻¹ * t')⁻¹ * (((t : Y)⁻¹ * t') * ((t : Y)⁻¹ * x * t)) := by group
    _ = ((t : Y)⁻¹ * t')⁻¹ * (((t : Y)⁻¹ * x * t) * ((t : Y)⁻¹ * t')) := by rw [h1]
    _ = (t' : Y)⁻¹ * x * t' := by group

theorem sameOn_apply {K : Subgroup Y} (e : MulAut Y) (heK' : ∀ x ∈ K, e⁻¹ x ∈ K) {a p : Y}
    (h : ∀ x ∈ K, a⁻¹ * x * a = p⁻¹ * x * p) :
    ∀ x ∈ K, (e a)⁻¹ * x * e a = (e p)⁻¹ * x * e p := by
  intro x hx
  have h1 := h (e⁻¹ x) (heK' x hx)
  have h2 := congrArg e h1
  simp only [map_mul, map_inv, MulAut.apply_inv_self] at h2
  exact h2

section Quot

variable {K : Subgroup Y}

@[expose] noncomputable def quotCenterAutHom : MulAut K →* MulAut (K ⧸ center K) where
  toFun α := QuotientGroup.congr (center K) (center K) α (map_center_eq α)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
    rfl
  map_mul' α β := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
    rfl

theorem quotCenterAutHom_mk (α : MulAut K) (x : K) :
    quotCenterAutHom α (QuotientGroup.mk x : K ⧸ center K) = QuotientGroup.mk (α x) :=
  rfl

end Quot

theorem isSylowOf_inf_component [Finite Y] (S : Sylow 2 Y) {K : Subgroup Y} (hK : IsComponent K) :
    IsSylowOf 2 ((S : Subgroup Y) ⊓ K) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowOf 2 (S : Subgroup Y) ⊤ :=
    isSylowOf_iff.mpr ⟨le_top, S.isPGroup', by rw [relIndex_top_right]; exact S.not_dvd_index⟩
  have : (layer Y).Characteristic := layer_characteristic
  have hn : (layer Y).Normal := inferInstance
  have h1 : IsSylowOf 2 ((S : Subgroup Y) ⊓ layer Y) (layer Y) :=
    hS.inf_of_le_normalizer le_top (normalizer_eq_top_iff.mpr hn).ge
  have h2 := h1.inf_of_le_normalizer (component_le_layer hK) (layer_le_normalizer hK)
  rwa [inf_assoc, inf_eq_right.mpr (component_le_layer hK)] at h2

theorem exists_derivedSeries_sameOn [Finite Y]
    (S : Sylow 2 Y) {A : Subgroup Y} {K : Subgroup Y} (hK : IsComponent K)
    (htype : goldschmidtSimpleType (K ⧸ center K)) (hind : InducesOmega1 A K S)
    {H : Type*} [Group H] (σ : H →* MulAut Y) (hσA : ∀ h, ∀ a ∈ A, σ h a ∈ A)
    (hσK : ∀ h, ∀ x ∈ K, σ h x ∈ K) :
    ∃ m : ℕ, ∀ h ∈ derivedSeries H m, ∀ a ∈ A, ∀ x ∈ K,
      (σ h a)⁻¹ * x * σ h a = a⁻¹ * x * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
  have hσK' : ∀ h, ∀ x ∈ K, (σ h)⁻¹ x ∈ K := fun h x hx => by
    rw [← map_inv]
    exact hσK h⁻¹ x hx
  obtain ⟨P, hP⟩ := isSylowOf_inf_component S hK
  set TL : Sylow 2 (K ⧸ center K) := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
    with hTL
  have hTLcoe : (TL : Subgroup (K ⧸ center K)) = (P : Subgroup K).map (QuotientGroup.mk' _) :=
    Sylow.coe_mapSurjective _ _
  have hmemP : ∀ t : K, (t : Y) ∈ (S : Subgroup Y) → t ∈ (P : Subgroup K) := by
    intro t ht
    have h1 : (t : Y) ∈ (P : Subgroup K).map K.subtype := by rw [hP]; exact ⟨ht, t.2⟩
    obtain ⟨t', ht', hte⟩ := h1
    rwa [Subtype.ext hte] at ht'
  have hgen : ∀ t : K, (t : Y) ∈ (S : Subgroup Y) →
      (t : Y) ^ 2 ∈ centralizer (K : Set Y) →
      (QuotientGroup.mk t : K ⧸ center K) ∈ Omega1 (TL : Subgroup (K ⧸ center K)) := by
    intro t ht ht2
    refine GoldType.mem_omega1 ?_ ?_
    · rw [hTLcoe]
      exact ⟨t, hmemP t ht, rfl⟩
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.mp ht2 g g.2)
  set ρL : H →* MulAut (K ⧸ center K) := quotCenterAutHom.comp (restrictAut σ K hσK) with hρL
  have hρL : ∀ h (x : K), ρL h (QuotientGroup.mk x) = QuotientGroup.mk ⟨σ h x, hσK h x x.2⟩ :=
    fun h x => rfl
  have hW : ∀ h, ∀ w ∈ Omega1 (TL : Subgroup (K ⧸ center K)),
      ρL h w ∈ Omega1 (TL : Subgroup (K ⧸ center K)) := by
    intro h w hw
    have hle : Omega1 (TL : Subgroup (K ⧸ center K)) ≤
        (Omega1 (TL : Subgroup (K ⧸ center K))).comap (ρL h).toMonoidHom := by
      refine (closure_le _).mpr fun u hu => ?_
      obtain ⟨huT, hu2⟩ := hu
      rw [hTLcoe] at huT
      obtain ⟨p, hp, rfl⟩ := huT
      have hpS : (p : Y) ∈ (S : Subgroup Y) := by
        have : (p : Y) ∈ (P : Subgroup K).map K.subtype := ⟨p, hp, rfl⟩
        rw [hP] at this
        exact this.1
      have hp2 : (p : Y) ^ 2 ∈ centralizer (K : Set Y) := by
        rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
          mem_center_iff] at hu2
        refine mem_centralizer_iff.mpr fun g hg => ?_
        have := congrArg Subtype.val (hu2 ⟨g, hg⟩)
        simpa using this
      obtain ⟨a, ha, hap⟩ := hind.2 p ⟨hpS, p.2⟩ hp2
      obtain ⟨t, ⟨htS, htK⟩, ht2, hat⟩ := hind.1 (σ h a) (hσA h a ha)
      have hσap := sameOn_apply (σ h) (hσK' h) hap
      have hsame : ∀ x ∈ K, (t : Y)⁻¹ * x * t = (σ h p)⁻¹ * x * σ h p := fun x hx =>
        (hat x hx).symm.trans (hσap x hx)
      have hmk := mk_eq_of_sameOn (t := ⟨t, htK⟩) (t' := ⟨σ h p, hσK h p p.2⟩) hsame
      rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
        hρL, ← hmk]
      exact hgen ⟨t, htK⟩ htS ht2
    exact hle hw
  obtain ⟨m, hm⟩ := exists_derivedSeries_fix htype TL ρL hW
  refine ⟨m, fun h hh a ha x hx => ?_⟩
  obtain ⟨t, ⟨htS, htK⟩, ht2, hat⟩ := hind.1 a ha
  have hfix := hm h hh _ (hgen ⟨t, htK⟩ htS ht2)
  rw [hρL] at hfix
  have hσt := sameOn_of_mk_eq hfix
  have hσa := sameOn_apply (σ h) (hσK' h) hat
  calc (σ h a)⁻¹ * x * σ h a = (σ h t)⁻¹ * x * σ h t := hσa x hx
    _ = (t : Y)⁻¹ * x * t := hσt x hx
    _ = a⁻¹ * x * a := (hat x hx).symm

section Count

variable [Finite Y]

theorem isMulCommutative_omega1
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L] (hL : goldschmidtSimpleType L)
    (T : Sylow 2 L) : IsMulCommutative (Omega1 (T : Subgroup L)) := by
  have hab : ∀ {U : Subgroup L}, (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) → IsMulCommutative U :=
    fun h => ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩
  have hBender : fusionIsBenderGroup L → IsMulCommutative (Omega1 (T : Subgroup L)) := by
    intro hX
    rw [GoldType.omega1_eq_sylowCenter_of_bender hX T]
    refine hab fun a ha b hb => ?_
    exact (mem_centralizer_iff.mp hb.2 a ha.1)
  rcases hL with ⟨f, hf, he⟩ | ⟨n, hn, he⟩ | ⟨f, hf, he⟩ | hrest
  · exact hBender (Or.inl ⟨f, by omega, he⟩)
  · exact hBender (Or.inr (Or.inr ⟨n, hn, he⟩))
  · exact hBender (Or.inr (Or.inl ⟨f, hf, he⟩))
  · obtain ⟨hTc, -, -, -⟩ := GoldType.elementary_of_clauses hrest T
    refine hab fun a ha b hb => ?_
    exact congrArg Subtype.val
      (hTc.is_comm.comm ⟨a, GoldType.omega1_le _ ha⟩ ⟨b, GoldType.omega1_le _ hb⟩)

omit [Finite Y] in
theorem sq_eq_one_of_mem_omega1 {L : Type*} [Group L] {T : Subgroup L}
    (hab : IsMulCommutative (Omega1 T)) {w : L} (hw : w ∈ Omega1 T) : w ^ 2 = 1 := by
  induction hw using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact one_pow 2
  | mul x y hx hy hx2 hy2 =>
    have hxy : x * y = y * x := congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [(Commute.mul_pow hxy 2), hx2, hy2, one_mul]
  | inv x hx hx2 => rw [inv_pow, hx2, inv_one]

omit [Finite Y] in
theorem le_normalizer_of_inducesOmega1 (S : Sylow 2 Y) {A K : Subgroup Y}
    (hind : InducesOmega1 A K S) : A ≤ normalizer (K : Set Y) := by
  have key : ∀ a ∈ A, ∀ x ∈ K, a⁻¹ * x * a ∈ K := by
    intro a ha x hx
    obtain ⟨t, ⟨-, htK⟩, -, hat⟩ := hind.1 a ha
    rw [hat x hx]
    exact K.mul_mem (K.mul_mem (K.inv_mem htK) hx) htK
  intro a ha
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := key a⁻¹ (A.inv_mem ha) x hx
    rwa [inv_inv] at this
  · intro hx
    have := key a ha _ hx
    rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at this

theorem four_le_card_range
    (S : Sylow 2 Y) {A K : Subgroup Y} (hK : IsComponent K)
    (htype : goldschmidtSimpleType (K ⧸ center K)) (hind : InducesOmega1 A K S) :
    4 ≤ Nat.card (conjAutOn K A (le_normalizer_of_inducesOmega1 S hind)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
  obtain ⟨P, hP⟩ := isSylowOf_inf_component S hK
  set TL : Sylow 2 (K ⧸ center K) := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
    with hTL
  have hTLcoe : (TL : Subgroup (K ⧸ center K)) = (P : Subgroup K).map (QuotientGroup.mk' _) :=
    Sylow.coe_mapSurjective _ _
  set W := Omega1 (TL : Subgroup (K ⧸ center K)) with hW
  have hWab : IsMulCommutative W := isMulCommutative_omega1 htype TL
  have hW4 : 4 ≤ Nat.card W := (N11b (K ⧸ center K) htype TL hWab).1
  have hlift : ∀ w : W, ∃ a : A, ∃ t : K, (QuotientGroup.mk t : K ⧸ center K) = w ∧
      ∀ x ∈ K, (a : Y)⁻¹ * x * a = (t : Y)⁻¹ * x * t := by
    intro w
    have hwT : (w : K ⧸ center K) ∈ (TL : Subgroup (K ⧸ center K)) := GoldType.omega1_le _ w.2
    rw [hTLcoe] at hwT
    obtain ⟨p, hp, hpw⟩ := hwT
    have hpS : (p : Y) ∈ (S : Subgroup Y) := by
      have : (p : Y) ∈ (P : Subgroup K).map K.subtype := ⟨p, hp, rfl⟩
      rw [hP] at this
      exact this.1
    have hw2 := sq_eq_one_of_mem_omega1 hWab w.2
    have hp2 : (p : Y) ^ 2 ∈ centralizer (K : Set Y) := by
      rw [← hpw, QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
        mem_center_iff] at hw2
      refine mem_centralizer_iff.mpr fun g hg => ?_
      have := congrArg Subtype.val (hw2 ⟨g, hg⟩)
      simpa using this
    obtain ⟨a, ha, hap⟩ := hind.2 p ⟨hpS, p.2⟩ hp2
    exact ⟨⟨a, ha⟩, p, hpw, hap⟩
  choose F t hFt hF using hlift
  set Φ := conjAutOn K A (le_normalizer_of_inducesOmega1 S hind) with hΦ
  let G : W → Φ.range := fun w => ⟨Φ (F w), ⟨F w, rfl⟩⟩
  have hG : Function.Injective G := by
    intro w w' hww'
    have h1 : Φ (F w) = Φ (F w') := congrArg Subtype.val hww'
    have h2 : ∀ x ∈ K, ((F w : A) : Y)⁻¹ * x * (F w : A) = ((F w' : A) : Y)⁻¹ * x * (F w' : A) := by
      intro x hx
      have h3 := congrArg (fun e : MulAut K => ((e⁻¹) ⟨x, hx⟩ : Y)) h1
      simp only [← map_inv] at h3
      rw [hΦ, conjAutOn_apply, conjAutOn_apply] at h3
      simpa only [InvMemClass.coe_inv, inv_inv] using h3
    have h4 : ∀ x ∈ K, (t w : Y)⁻¹ * x * t w = (t w' : Y)⁻¹ * x * t w' := fun x hx =>
      ((hF w x hx).symm.trans (h2 x hx)).trans (hF w' x hx)
    apply Subtype.ext
    rw [← hFt w, ← hFt w']
    exact mk_eq_of_sameOn h4
  exact hW4.trans (Nat.card_le_card_of_injective G hG)

omit [Finite Y] in
theorem conjAutOn_eq_of_sameOn {K A : Subgroup Y} (hA : A ≤ normalizer (K : Set Y)) {a b : A}
    (h : ∀ y ∈ K, (a : Y)⁻¹ * y * a = (b : Y)⁻¹ * y * b) :
    conjAutOn K A hA a = conjAutOn K A hA b := by
  have h1 : conjAutOn K A hA a⁻¹ = conjAutOn K A hA b⁻¹ := by
    refine MulEquiv.ext fun w => Subtype.ext ?_
    rw [conjAutOn_apply, conjAutOn_apply]
    simpa only [InvMemClass.coe_inv, inv_inv] using h w w.2
  rw [map_inv, map_inv] at h1
  exact inv_injective h1

theorem conjAutOn_eq_one_of_ne {A : Subgroup Y} {K L : ComponentIndex Y}
    (hA : A ≤ normalizer (L.1 : Set Y)) (hKL : K ≠ L) {x : A} (hx : (x : Y) ∈ K.1) :
    conjAutOn L.1 A hA x = 1 := by
  refine MulEquiv.ext fun w => Subtype.ext ?_
  rw [conjAutOn_apply, ((componentIndex_commute hKL) _ _ hx w.2).eq, mul_inv_cancel_right]
  rfl

theorem surjective_conjAutOn_pi {A : Subgroup Y}
    (hAN : ∀ K : ComponentIndex Y, A ≤ normalizer (K.1 : Set Y))
    (hcover : ∀ K : ComponentIndex Y, ∀ a ∈ A, ∃ x ∈ A ⊓ K.1, ∀ y ∈ K.1,
      a⁻¹ * y * a = x⁻¹ * y * x) :
    Function.Surjective (fun (a : A) (K : ComponentIndex Y) =>
      (⟨conjAutOn K.1 A (hAN K) a, a, rfl⟩ : (conjAutOn K.1 A (hAN K)).range)) := by
  intro φ
  have hpre : ∀ K : ComponentIndex Y, ∃ x : A, (x : Y) ∈ K.1 ∧
      conjAutOn K.1 A (hAN K) x = (φ K : MulAut K.1) := by
    intro K
    obtain ⟨a, ha⟩ := (φ K).2
    obtain ⟨x, ⟨hxA, hxK⟩, hx⟩ := hcover K a a.2
    refine ⟨⟨x, hxA⟩, hxK, ?_⟩
    rw [← ha]
    exact (conjAutOn_eq_of_sameOn (hAN K) hx).symm
  choose x hxK hx using hpre
  have key : ∀ s : Finset (ComponentIndex Y), ∃ a : A, ∀ K : ComponentIndex Y,
      conjAutOn K.1 A (hAN K) a = if K ∈ s then (φ K : MulAut K.1) else 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, fun K => by simp⟩
    | insert K₀ s hK₀ ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨a * x K₀, fun K => ?_⟩
      rw [map_mul, ha K]
      by_cases hK : K = K₀
      · subst hK
        simp [hK₀, hx]
      · rw [conjAutOn_eq_one_of_ne (hAN K) (Ne.symm hK) (hxK K₀), mul_one]
        simp only [Finset.mem_insert, hK, false_or]
  obtain ⟨a, ha⟩ := key Finset.univ
  exact ⟨a, funext fun K => Subtype.ext (by simpa using ha K)⟩

theorem four_pow_card_componentIndex_le
    (S : Sylow 2 Y) {A : Subgroup Y}
    (htype : ∀ K : ComponentIndex Y, goldschmidtSimpleType (K.1 ⧸ center K.1))
    (hind : ∀ K : ComponentIndex Y, InducesOmega1 A K.1 S)
    (hcover : ∀ K : ComponentIndex Y, ∀ a ∈ A, ∃ x ∈ A ⊓ K.1, ∀ y ∈ K.1,
      a⁻¹ * y * a = x⁻¹ * y * x) :
    4 ^ Nat.card (ComponentIndex Y) ≤ Nat.card A := by
  have hAN : ∀ K : ComponentIndex Y, A ≤ normalizer (K.1 : Set Y) := fun K =>
    le_normalizer_of_inducesOmega1 S (hind K)
  have h1 := Nat.card_le_card_of_surjective _ (surjective_conjAutOn_pi hAN hcover)
  rw [Nat.card_pi] at h1
  have h2 : 4 ^ Nat.card (ComponentIndex Y) ≤
      ∏ K : ComponentIndex Y, Nat.card (conjAutOn K.1 A (hAN K)).range := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact Finset.pow_card_le_prod _ _ _ fun K _ => four_le_card_range S K.2 (htype K) (hind K)
  exact h2.trans h1

theorem exists_mem_conj_ne
    (S : Sylow 2 Y) {A K : Subgroup Y} (hK : IsComponent K)
    (htype : goldschmidtSimpleType (K ⧸ center K)) (hind : InducesOmega1 A K S) :
    ∃ a ∈ A, ∃ y ∈ K, a⁻¹ * y * a ≠ y := by
  have h4 := four_le_card_range S hK htype hind
  set Φ := conjAutOn K A (le_normalizer_of_inducesOmega1 S hind) with hΦ
  have hne : Φ.range ≠ ⊥ := by
    intro h
    rw [h, card_bot] at h4
    omega
  obtain ⟨⟨c, a₀, rfl⟩, hc⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hc' : Φ a₀ ≠ 1 := fun h => hc (Subtype.ext h)
  obtain ⟨w, hw⟩ : ∃ w : K, Φ a₀ w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hc' (MulEquiv.ext hcon)
  refine ⟨(a₀ : Y)⁻¹, A.inv_mem a₀.2, w, w.2, fun h => hw (Subtype.ext ?_)⟩
  rw [hΦ, conjAutOn_apply]
  simpa only [inv_inv] using h

end Count

theorem exists_derivedSeries_sameOn_components [Finite Y]
    (S : Sylow 2 Y) {A : Subgroup Y}
    (htype : ∀ K : ComponentIndex Y, goldschmidtSimpleType (K.1 ⧸ center K.1))
    (hind : ∀ K : ComponentIndex Y, InducesOmega1 A K.1 S)
    (hcover : ∀ K : ComponentIndex Y, ∀ a ∈ A, ∃ x ∈ A ⊓ K.1, ∀ y ∈ K.1,
      a⁻¹ * y * a = x⁻¹ * y * x)
    (hcard : Nat.card A < 4 ^ 5) {H : Type*} [Group H] (σ : H →* MulAut Y)
    (hσA : ∀ h, ∀ a ∈ A, σ h a ∈ A) :
    ∃ m : ℕ, ∀ h ∈ derivedSeries H m, ∀ a ∈ A, ∀ K : ComponentIndex Y, ∀ x ∈ K.1,
      (σ h a)⁻¹ * x * σ h a = a⁻¹ * x * a := by
  have hc : Nat.card (ComponentIndex Y) ≤ 4 := by
    have h1 := four_pow_card_componentIndex_le S htype hind hcover
    by_contra hcon
    push Not at hcon
    have h2 : 4 ^ 5 ≤ 4 ^ Nat.card (ComponentIndex Y) := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  have : Group.IsSolvable (Equiv.Perm (ComponentIndex Y)) := Equiv.Perm.isSolvable hc
  obtain ⟨m₀, hm₀⟩ := Group.IsSolvable.solvable (G := Equiv.Perm (ComponentIndex Y))
  set π : H →* Equiv.Perm (ComponentIndex Y) := compPermHom.comp σ with hπ
  have h0 : derivedSeries H m₀ ≤ π.ker := by
    intro h hh
    have h1 := map_derivedSeries_le_derivedSeries π m₀ ⟨h, hh, rfl⟩
    rw [hm₀, mem_bot] at h1
    exact h1
  have hfix : ∀ h ∈ π.ker, ∀ K : ComponentIndex Y, ∀ x ∈ K.1, σ h x ∈ K.1 := by
    intro h hh K x hx
    rw [MonoidHom.mem_ker] at hh
    have hK : compPerm (σ h) K = K := congrArg (fun e : Equiv.Perm (ComponentIndex Y) => e K) hh
    exact apply_mem_of_compPerm hK hx
  have hK : ∀ K : ComponentIndex Y, ∃ m : ℕ, ∀ h ∈ derivedSeries π.ker m, ∀ a ∈ A, ∀ x ∈ K.1,
      (σ h a)⁻¹ * x * σ h a = a⁻¹ * x * a := fun K =>
    exists_derivedSeries_sameOn S K.2 (htype K) (hind K) (σ.comp π.ker.subtype)
      (fun h a ha => hσA h a ha) (fun h x hx => hfix h h.2 K x hx)
  choose mK hmK using hK
  refine ⟨m₀ + Finset.univ.sup mK, fun h hh a ha K x hx => ?_⟩
  obtain ⟨h', hh', rfl⟩ := derivedSeries_add_le h0 (Finset.univ.sup mK) hh
  have hle : derivedSeries π.ker (Finset.univ.sup mK) ≤ derivedSeries π.ker (mK K) :=
    derivedSeries_antitone π.ker (Finset.le_sup (f := mK) (Finset.mem_univ K))
  exact hmK K h' (hle hh') a ha x hx

end CFSG.ComponentClassification.AS81.Qbar
