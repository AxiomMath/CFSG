module

public import CFSG.CGT.PushingUpLit.BHS.FourFourG

public section

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
open scoped Matrix

section Basic

variable {V : Type} [CommGroup V]

@[expose] def cenSection (W Z : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | (∀ w : V, w ∈ W ↔ g w ∈ W) ∧ ∀ w ∈ W, g w * w⁻¹ ∈ Z}
  one_mem' := ⟨fun w => by simp, fun w _ => by simp⟩
  mul_mem' := by
    rintro g g' ⟨hg, hgZ⟩ ⟨hg', hg'Z⟩
    refine ⟨fun w => (hg' w).trans (hg (g' w)), fun w hw => ?_⟩
    have h1 : g' w ∈ W := (hg' w).1 hw
    have e : (g * g') w * w⁻¹ = (g (g' w) * (g' w)⁻¹) * (g' w * w⁻¹) := by
      rw [MulAut.mul_apply]
      group
    rw [e]
    exact Z.mul_mem (hgZ _ h1) (hg'Z w hw)
  inv_mem' := by
    rintro g ⟨hg, hgZ⟩
    have hmem : ∀ w : V, w ∈ W ↔ g⁻¹ w ∈ W := fun w => by
      have := hg (g⁻¹ w)
      rw [MulAut.apply_inv_self] at this
      exact this.symm
    refine ⟨hmem, fun w hw => ?_⟩
    have h1 : g (g⁻¹ w) * (g⁻¹ w)⁻¹ ∈ Z := hgZ _ ((hmem w).1 hw)
    rw [MulAut.apply_inv_self] at h1
    have h2 := Z.inv_mem h1
    rwa [mul_inv_rev, inv_inv] at h2

theorem exists_mulVec_eq_of_ne_zero {F : Type*} [Field F] {v w : Fin 2 → F} (hv : v ≠ 0)
    (hw : w ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = w := by
  obtain ⟨g₁, hg₁⟩ := CFSG.Timmesfeld.ARS.NaturalModule.exists_mulVec_eq hv
  obtain ⟨g₂, hg₂⟩ := CFSG.Timmesfeld.ARS.NaturalModule.exists_mulVec_eq hw
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [← hg₁, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
  exact hg₂

namespace IsSLNatSection

variable {L : Subgroup (MulAut V)} {W Z : Subgroup V} {n : ℕ}

theorem sup_eq_of_invariant (h : IsSLNatSection L W Z n) (_hn : 1 ≤ n) (hZW : Z ≤ W)
    {N : Subgroup V} (hNW : N ≤ W) (hinv : ∀ g ∈ L, ∀ u ∈ N, g u ∈ N) (hN : ¬ N ≤ Z) :
    N ⊔ Z = W := by
  obtain ⟨hLW, θ, β, -, hker, hact⟩ := h
  obtain ⟨u₀, hu₀N, hu₀Z⟩ := IsConcreteLE.not_le_iff_exists.1 hN
  have hp₀ : u₀ ∈ W := hNW hu₀N
  have hv₀ : Multiplicative.toAdd (β ⟨u₀, hp₀⟩) ≠ 0 := by
    intro h0
    apply hu₀Z
    have h1 : β ⟨u₀, hp₀⟩ = 1 := by simpa using congrArg Multiplicative.ofAdd h0
    have h2 : (⟨u₀, hp₀⟩ : ↥W) ∈ β.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hU : ∀ v : Fin 2 → GaloisField 2 n,
      ∃ p : ↥W, (p : V) ∈ N ∧ β p = Multiplicative.ofAdd v := by
    intro v
    by_cases hv : v = 0
    · refine ⟨1, N.one_mem, ?_⟩
      rw [map_one, hv]
      rfl
    · obtain ⟨g, hg⟩ := exists_mulVec_eq_of_ne_zero hv₀ hv
      have hxW : ((θ.symm g : ↥L) : MulAut V) u₀ ∈ W := hLW _ (θ.symm g).2 u₀ hp₀
      refine ⟨⟨((θ.symm g : ↥L) : MulAut V) u₀, hxW⟩, hinv _ (θ.symm g).2 u₀ hu₀N, ?_⟩
      exact (hact (θ.symm g) ⟨u₀, hp₀⟩ hxW).trans (by rw [MulEquiv.apply_symm_apply, hg])
  refine le_antisymm (sup_le hNW hZW) fun w hw => ?_
  obtain ⟨p, hpN, hpβ⟩ := hU (Multiplicative.toAdd (β ⟨w, hw⟩))
  rw [ofAdd_toAdd] at hpβ
  have hker' : p⁻¹ * ⟨w, hw⟩ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpβ, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hker'
  have hz : (p : V)⁻¹ * w ∈ Z := hker'
  have hw' : w = (p : V) * ((p : V)⁻¹ * w) := by group
  rw [hw']
  exact Subgroup.mul_mem_sup hpN hz

theorem mem_of_forall_fixed (h : IsSLNatSection L W Z n) (_hn : 1 ≤ n) {w : V} (hw : w ∈ W)
    (hfix : ∀ g ∈ L, g w * w⁻¹ ∈ Z) : w ∈ Z := by
  obtain ⟨hLW, θ, β, -, hker, hact⟩ := h
  have hfixv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ Multiplicative.toAdd (β ⟨w, hw⟩) =
        Multiplicative.toAdd (β ⟨w, hw⟩) := by
    intro g
    have hxw : ((θ.symm g : ↥L) : MulAut V) w ∈ W := hLW _ (θ.symm g).2 w hw
    have h2 : (⟨((θ.symm g : ↥L) : MulAut V) w, hxw⟩ : ↥W) * (⟨w, hw⟩ : ↥W)⁻¹ ∈ β.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hfix _ (θ.symm g).2
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one,
      hact (θ.symm g) ⟨w, hw⟩ hxw] at h2
    have h3 := congrArg Multiplicative.toAdd h2
    rwa [toAdd_ofAdd, MulEquiv.apply_symm_apply] at h3
  have h1 := (CFSG.Timmesfeld.ARS.NaturalModule.forall_upperElt_mulVec_eq_iff _).1
    fun t => hfixv _
  have h2 := (CFSG.Timmesfeld.ARS.NaturalModule.forall_lowerElt_mulVec_eq_iff _).1
    fun t => hfixv _
  have h0 : Multiplicative.toAdd (β ⟨w, hw⟩) = 0 := by
    ext i
    fin_cases i
    · exact h2
    · exact h1
  have h1' : β ⟨w, hw⟩ = 1 := by simpa using congrArg Multiplicative.ofAdd h0
  have h3 : (⟨w, hw⟩ : ↥W) ∈ β.ker := h1'
  rw [hker, Subgroup.mem_subgroupOf] at h3
  exact h3

theorem eq_one_of_trivial (h : IsSLNatSection L W Z n) (_hn : 1 ≤ n) {a : MulAut V} (ha : a ∈ L)
    (htriv : ∀ w ∈ W, a w * w⁻¹ ∈ Z) : a = 1 := by
  obtain ⟨hLW, θ, β, hsurj, hker, hact⟩ := h
  have hθ : (θ ⟨a, ha⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) = 1 := by
    apply CFSG.Timmesfeld.ARS.NaturalModule.eq_one_of_forall_mulVec_eq
    intro v
    obtain ⟨p, hp⟩ := hsurj (Multiplicative.ofAdd v)
    have hpa : a p ∈ W := hLW a ha p p.2
    have h2 : (⟨a p, hpa⟩ : ↥W) * p⁻¹ ∈ β.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact htriv p p.2
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, hact ⟨a, ha⟩ p hpa, hp] at h2
    have h3 := congrArg Multiplicative.toAdd h2
    simpa using h3
  have h4 : (⟨a, ha⟩ : ↥L) = 1 := θ.injective (hθ.trans (map_one θ).symm)
  exact congrArg Subtype.val h4

end IsSLNatSection

theorem pow_four_eq_one_of_series {g : MulAut V} {Z W : Subgroup V} (hV : ∀ v : V, v ^ 2 = 1)
    (hZ : ∀ z ∈ Z, g z = z) (hW : ∀ w ∈ W, g w * w⁻¹ ∈ Z) (hVW : ∀ v : V, g v * v⁻¹ ∈ W) :
    g ^ 4 = 1 := by
  have hgg : ∀ x : V, g (g x) = (g (g x * x⁻¹) * (g x * x⁻¹)⁻¹) * x := by
    intro x
    have h1 : g (g x) = g (g x * x⁻¹) * g x := by
      have := map_mul g (g x * x⁻¹) x
      rwa [inv_mul_cancel_right] at this
    have hd : (g x * x⁻¹)⁻¹ = g x * x⁻¹ := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_two]
      exact hV _
    rw [h1, hd, mul_assoc, inv_mul_cancel_right]
  obtain ⟨e, he⟩ : ∃ e : V → V, ∀ x, e x ∈ Z ∧ g (g x) = e x * x :=
    ⟨fun x => g (g x * x⁻¹) * (g x * x⁻¹)⁻¹, fun x => ⟨hW _ (hVW x), hgg x⟩⟩
  have h4 : ∀ v : V, g (g (g (g v))) = v := by
    intro v
    calc g (g (g (g v))) = g (g (e v * v)) := by rw [(he v).2]
      _ = g (g (e v)) * g (g v) := by rw [map_mul, map_mul]
      _ = e v * (e v * v) := by rw [hZ _ (he v).1, hZ _ (he v).1, (he v).2]
      _ = (e v * e v) * v := (mul_assoc _ _ _).symm
      _ = v := by rw [← pow_two, hV, one_mul]
  have h5 : g ^ 4 = g * g * g * g := by simp only [pow_succ, pow_zero, one_mul]
  rw [h5]
  ext v
  simp only [MulAut.mul_apply, MulAut.one_apply]
  exact h4 v

theorem isElemAbelian2_of_isQuadratic (hV : ∀ v : V, v ^ 2 = 1) {E : Subgroup (MulAut V)}
    (hE : IsQuadratic E) : IsElemAbelian2 E := by
  refine ⟨FourOneTools.comm_of_isQuadratic hE, fun a ha => ?_⟩
  ext v
  have hu : a v * v⁻¹ ∈ fixV E := hE (G6.mem_commV_of_mem ha v)
  have hau : a (a v * v⁻¹) = a v * v⁻¹ := hu a ha
  have h1 : a (a v) = (a v * v⁻¹) * (a v) := by
    have := map_mul a (a v * v⁻¹) v
    rw [hau, inv_mul_cancel_right] at this
    exact this
  rw [pow_two, MulAut.mul_apply, h1, MulAut.one_apply]
  calc (a v * v⁻¹) * a v = (a v * v⁻¹) * (a v * v⁻¹) * v := by group
    _ = v := by rw [← pow_two, hV, one_mul]

theorem comm_of_trivial_series {X : Subgroup V} {g g' : MulAut V} (hg : ∀ x ∈ X, g x = x)
    (hg' : ∀ x ∈ X, g' x = x) (hgv : ∀ v : V, g v * v⁻¹ ∈ X) (hgv' : ∀ v : V, g' v * v⁻¹ ∈ X) :
    g * g' = g' * g := by
  ext v
  have e1 : g (g' v) = g' v * v⁻¹ * g v := by
    have h1 := map_mul g (g' v * v⁻¹) v
    rw [hg _ (hgv' v), inv_mul_cancel_right] at h1
    exact h1
  have e2 : g' (g v) = g v * v⁻¹ * g' v := by
    have h1 := map_mul g' (g v * v⁻¹) v
    rw [hg' _ (hgv v), inv_mul_cancel_right] at h1
    exact h1
  rw [MulAut.mul_apply, MulAut.mul_apply, e1, e2]
  comm_group

@[expose] def trivOnSeries (P : Subgroup (MulAut V)) (X : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | g ∈ P ∧ g ^ 2 = 1 ∧ (∀ x ∈ X, g x = x) ∧ ∀ v : V, g v * v⁻¹ ∈ X}
  one_mem' := ⟨P.one_mem, one_pow 2, fun x _ => rfl, fun v => by simp⟩
  mul_mem' := by
    rintro g g' ⟨hgP, hg2, hgX, hgv⟩ ⟨hg'P, hg'2, hg'X, hg'v⟩
    refine ⟨P.mul_mem hgP hg'P, ?_, fun x hx => ?_, fun v => ?_⟩
    · have hc : Commute g g' := comm_of_trivial_series hgX hg'X hgv hg'v
      rw [hc.mul_pow, hg2, hg'2, one_mul]
    · rw [MulAut.mul_apply, hg'X x hx, hgX x hx]
    · have e : (g * g') v * v⁻¹ = (g (g' v) * (g' v)⁻¹) * (g' v * v⁻¹) := by
        rw [MulAut.mul_apply]
        group
      rw [e]
      exact X.mul_mem (hgv (g' v)) (hg'v v)
  inv_mem' := by
    rintro g ⟨hgP, hg2, hgX, hgv⟩
    refine ⟨P.inv_mem hgP, ?_, fun x hx => ?_, fun v => ?_⟩
    · rw [inv_pow, hg2, inv_one]
    · calc g⁻¹ x = g⁻¹ (g x) := by rw [hgX x hx]
        _ = x := MulAut.inv_apply_self _ _ _
    · have h1 := hgv (g⁻¹ v)
      rw [MulAut.apply_inv_self] at h1
      have h2 := X.inv_mem h1
      rwa [mul_inv_rev, inv_inv] at h2

theorem trivOnSeries_le (P : Subgroup (MulAut V)) (X : Subgroup V) : trivOnSeries P X ≤ P :=
  fun _ hg => hg.1

theorem isElemAbelian2_trivOnSeries (P : Subgroup (MulAut V)) (X : Subgroup V) :
    IsElemAbelian2 (trivOnSeries P X) :=
  ⟨fun _ hg _ hg' => comm_of_trivial_series hg.2.2.1 hg'.2.2.1 hg.2.2.2 hg'.2.2.2,
    fun _ hg => hg.2.1⟩

end Basic

section Sylow

variable {V : Type} [CommGroup V] [Finite V]

namespace IsSLNatSection

variable {L : Subgroup (MulAut V)} {n : ℕ}

theorem eq_one_of_conj_eq (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n)
    {A D₁ : Subgroup (MulAut V)} (hA : IsSylowOf 2 A L) (h₁ : IsSylowOf 2 D₁ L) (hne : D₁ ≠ A)
    {a : MulAut V} (ha : a ∈ A) (hconj : conjSub a D₁ = D₁) : a = 1 := by
  have hinv : conjSub a⁻¹ D₁ = D₁ := by
    calc conjSub a⁻¹ D₁ = conjSub a⁻¹ (conjSub a D₁) := by rw [hconj]
      _ = D₁ := FourTwoTools.conjSub_inv_conjSub a D₁
  have hN : Subgroup.zpowers a ≤ Subgroup.normalizer (D₁ : Set (MulAut V)) := by
    rw [Subgroup.zpowers_le]
    exact FourTwoTools.mem_normalizer_of_conjSub_le hconj.le hinv.le
  have hZ : IsPGroup 2 (Subgroup.zpowers a) := hA.2.1.to_le (Subgroup.zpowers_le.2 ha)
  have hR : IsPGroup 2 (Subgroup.zpowers a ⊔ D₁ : Subgroup (MulAut V)) :=
    hZ.to_sup_of_normal_right' h₁.2.1 hN
  have hRL : Subgroup.zpowers a ⊔ D₁ ≤ L := sup_le (Subgroup.zpowers_le.2 (hA.1 ha)) h₁.1
  have hle := Glauberman.le_of_isSylowOf_of_le h₁ hR le_sup_right hRL
  have haD : a ∈ D₁ := hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hbot := h.sylow_inf_eq_bot hn hA h₁ hne.symm
  exact Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_inf.2 ⟨ha, haD⟩)

theorem exists_conj_sylow_of_ne (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n)
    {A D₁ D₂ : Subgroup (MulAut V)} (hA : IsSylowOf 2 A L) (h₁ : IsSylowOf 2 D₁ L)
    (h₂ : IsSylowOf 2 D₂ L) (hne₁ : D₁ ≠ A) (hne₂ : D₂ ≠ A) :
    ∃ a ∈ A, D₂ = conjSub a D₁ := by
  let f : A → Subgroup (MulAut V) := fun a => conjSub (a : MulAut V) D₁
  have hf : Function.Injective f := by
    intro a a' haa'
    have h1 : conjSub ((a : MulAut V)⁻¹ * (a' : MulAut V)) D₁ = D₁ := by
      rw [conjSub_mul]
      have : conjSub (a' : MulAut V) D₁ = conjSub (a : MulAut V) D₁ := haa'.symm
      rw [this, FourTwoTools.conjSub_inv_conjSub]
    have h2 := h.eq_one_of_conj_eq hn hA h₁ hne₁ (A.mul_mem (A.inv_mem a.2) a'.2) h1
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  have hrange : Set.range f ⊆ {S | IsSylowOf 2 S L} \ {A} := by
    rintro _ ⟨a, rfl⟩
    refine ⟨?_, ?_⟩
    · have := isSylowOf_conjSub h₁ (a : MulAut V)
      rwa [conjSub_self_of_mem (hA.1 a.2)] at this
    · intro hEq
      apply hne₁
      have hEq' : conjSub (a : MulAut V) D₁ = A := Set.mem_singleton_iff.1 hEq
      have h3 : conjSub (a : MulAut V)⁻¹ (conjSub (a : MulAut V) D₁) =
          conjSub (a : MulAut V)⁻¹ A := by
        rw [hEq']
      rwa [FourTwoTools.conjSub_inv_conjSub, conjSub_self_of_mem (A.inv_mem a.2)] at h3
  have hcardS : ({S | IsSylowOf 2 S L} \ {A}).ncard = 2 ^ n := by
    rw [Set.ncard_sdiff_singleton_of_mem (show A ∈ {S | IsSylowOf 2 S L} from hA),
      h.ncard_sylows hn]
    rfl
  have hcardR : (Set.range f).ncard = 2 ^ n := by
    rw [Set.ncard_range_of_injective hf, h.sylow_card hn hA]
  have hreq : Set.range f = {S | IsSylowOf 2 S L} \ {A} :=
    Set.eq_of_subset_of_ncard_le hrange (by rw [hcardS, hcardR])
  have hD₂ : D₂ ∈ Set.range f := by
    rw [hreq]
    exact ⟨h₂, hne₂⟩
  obtain ⟨a, ha⟩ := hD₂
  exact ⟨a, a.2, ha.symm⟩

end IsSLNatSection

theorem Hyp43.conjSub_sup_eq {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    {T M : Subgroup (MulAut V)} (h : Hyp43 P D T M) {A B : Subgroup (MulAut V)} (hA : A ∈ D)
    (hB : B ∈ D) (hne : A ≠ B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {k : MulAut V}
    (hkP : k ∈ P) (hk : ∀ x ∈ fixV (A ⊔ B), k x ∈ fixV (A ⊔ B)) :
    conjSub k (A ⊔ B) = A ⊔ B := by
  have hAB2 : IsElemAbelian2 (A ⊔ B) :=
    isElemAbelian2_sup (h.elemAb A hA) (h.elemAb B hB) hcomm
  have hABP : A ⊔ B ≤ P := sup_le (h.le A hA) (h.le B hB)
  have hquad : IsQuadratic (A ⊔ B) := (four_six h.toHyp41 hA hB hne hcomm).2
  have hABY : A ⊔ B ≤ trivOnSeries P (fixV (A ⊔ B)) := fun a ha =>
    ⟨hABP ha, hAB2.2 a ha, fun x hx => hx a ha, fun v => hquad (G6.mem_commV_of_mem ha v)⟩
  have hfixY : fixV (trivOnSeries P (fixV (A ⊔ B))) = fixV (A ⊔ B) :=
    le_antisymm (fixV_anti hABY) fun x hx y hy => hy.2.2.1 x hx
  have hmax := h.max A hA (trivOnSeries P (fixV (A ⊔ B))) (isElemAbelian2_trivOnSeries _ _)
    (trivOnSeries_le _ _)
  have hcardV : Nat.card V = Nat.card A * Nat.card B * Nat.card (fixV (A ⊔ B)) :=
    h.card_prod A hA B hB hne.symm hcomm
  have hVA : Nat.card V = Nat.card A * Nat.card (fixV A) := h.card_eq A hA
  have hbot : A ⊓ B = ⊥ := (h.eq_or_inf_eq_bot hA hB).resolve_left hne
  have hcardS : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
    have := card_sup_mul_card_inf' (X := A) (Y := B) hcomm
    rwa [hbot, Subgroup.card_bot, mul_one] at this
  have hYle : Nat.card ↥(trivOnSeries P (fixV (A ⊔ B))) ≤ Nat.card ↥(A ⊔ B) := by
    rw [hfixY, ← hVA, hcardV] at hmax
    rw [hcardS]
    exact Nat.le_of_mul_le_mul_right hmax Nat.card_pos
  have hYeq : A ⊔ B = trivOnSeries P (fixV (A ⊔ B)) := Subgroup.eq_of_le_of_card_ge hABY hYle
  have hk' : ∀ x ∈ fixV (A ⊔ B), k⁻¹ x ∈ fixV (A ⊔ B) := by
    have hinj : Function.Injective
        (fun x : fixV (A ⊔ B) => (⟨k x, hk x x.2⟩ : fixV (A ⊔ B))) := fun x y hxy =>
      Subtype.ext (k.injective (congrArg Subtype.val hxy))
    have hsurj := Finite.injective_iff_surjective.1 hinj
    intro x hx
    obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
    have hyx : k (y : V) = x := congrArg Subtype.val hy
    rw [← hyx, MulAut.inv_apply_self]
    exact y.2
  have hle : conjSub k (A ⊔ B) ≤ trivOnSeries P (fixV (A ⊔ B)) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨haP, ha2, haX, hav⟩ := hABY ha
    refine ⟨P.mul_mem (P.mul_mem hkP haP) (P.inv_mem hkP), ?_, fun x hx => ?_, fun v => ?_⟩
    · show (k * a * k⁻¹) ^ 2 = 1
      rw [conj_pow, ha2, mul_one, mul_inv_cancel]
    · show k (a (k⁻¹ x)) = x
      rw [haX _ (hk' x hx), MulAut.apply_inv_self]
    · show k (a (k⁻¹ v)) * v⁻¹ ∈ fixV (A ⊔ B)
      have h1 := hk _ (hav (k⁻¹ v))
      rwa [map_mul, map_inv, MulAut.apply_inv_self] at h1
  exact Subgroup.eq_of_le_of_card_ge (hle.trans hYeq.ge) (by rw [card_conjSub])

end Sylow

end CFSG.CGT.PushingUpLit.BHS
