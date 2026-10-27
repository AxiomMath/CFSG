module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourTransv

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Module CFSG.RankThree.FFModules

structure Alt7Hyp (G : Type*) [Group G] : Prop where
  card_le : ∀ R : Subgroup G, (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) → (∀ a ∈ R, a ^ 2 = 1) →
    Nat.card R ≤ 4
  conj : ∀ a b : G, a ≠ 1 → a ^ 2 = 1 → b ≠ 1 → b ^ 2 = 1 → IsConj a b
  order5 : ∃ a b : G, a ≠ 1 ∧ a ^ 2 = 1 ∧ b ≠ 1 ∧ b ^ 2 = 1 ∧ orderOf (a * b) = 5
  card_inv : Nat.card {t : G // t ^ 2 = 1 ∧ t ≠ 1} = 105
  card_G : Nat.card G = 2520
  klein : ∀ R : Subgroup G, Nat.card R = 4 → (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) →
    (∀ a ∈ R, a ^ 2 = 1) → 72 ≤ Nat.card (Subgroup.normalizer (R : Set G)) →
    ∃ E : Subgroup G, E ≤ Subgroup.normalizer (R : Set G) ∧ Nat.card E = 9
  klein_unique : ∀ {D R R' : Subgroup G}, IsPGroup 2 D → R ≤ D → R' ≤ D → Nat.card R = 4 →
    Nat.card R' = 4 → (∀ a ∈ R, a ^ 2 = 1) → (∀ a ∈ R', a ^ 2 = 1) →
    72 ≤ Nat.card (Subgroup.normalizer (R : Set G)) →
    72 ≤ Nat.card (Subgroup.normalizer (R' : Set G)) → R = R'

variable {G : Type*} [Group G] [Finite G] {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]
  [Finite Q]

theorem natCard_submodule_zmod2 (p : Submodule (ZMod 2) Q) :
    Nat.card p = 2 ^ finrank (ZMod 2) p := by
  have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := p)
  rwa [Nat.card_zmod] at this

theorem natCard_space_four (hdim : finrank (ZMod 2) Q = 4) : Nat.card Q = 16 := by
  have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Q)
  rw [Nat.card_zmod, hdim] at this
  simpa using this

open MulAction in
theorem card_eq_orbit_mul {G : Type*} [Group G] [Finite G] (K : Subgroup G) (t : G) :
    Nat.card K = Set.ncard {x : G | ∃ k ∈ K, x = k * t * k⁻¹} *
      Nat.card ↥(K ⊓ Subgroup.centralizer {t}) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let _ : MulAction K G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp K.subtype)
  have hsmul : ∀ (k : K) (x : G), k • x = k * x * (k : G)⁻¹ := by
    intro k x
    show (ConjAct.toConjAct (k : G)) • x = _
    rw [ConjAct.smul_def]; simp
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group K t
  have hset : (MulAction.orbit K t : Set G) = {x : G | ∃ k ∈ K, x = k * t * k⁻¹} := by
    ext x
    simp only [MulAction.mem_orbit_iff, hsmul, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
  have horb : Nat.card (MulAction.orbit K t) = Set.ncard {x : G | ∃ k ∈ K, x = k * t * k⁻¹} := by
    rw [← hset]; exact Nat.card_coe_set_eq _
  have hst : Nat.card (MulAction.stabilizer K t) = Nat.card ↥(K ⊓ Subgroup.centralizer {t}) := by
    refine Nat.card_congr ⟨fun k => ⟨k.1.1, Subgroup.mem_inf.2 ⟨k.1.2, ?_⟩⟩,
      fun k => ⟨⟨k.1, (Subgroup.mem_inf.1 k.2).1⟩, ?_⟩, ?_, ?_⟩
    · have := k.2
      rw [MulAction.mem_stabilizer_iff, hsmul] at this
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      calc t * (k : G) = (k : G) * t * (k : G)⁻¹ * (k : G) := by rw [this]
        _ = (k : G) * t := by group
    · have := (Subgroup.mem_inf.1 k.2).2
      rw [Subgroup.mem_centralizer_iff] at this
      rw [MulAction.mem_stabilizer_iff, hsmul]
      have e := this t (Set.mem_singleton t)
      show (k.1 : G) * t * (k.1 : G)⁻¹ = t
      rw [← e]; group
    · intro k; rfl
    · intro k; rfl
  simp only [← Nat.card_eq_fintype_card] at h
  rw [← h, horb, hst]

section Local

variable (ρ : Representation (ZMod 2) G Q) (hρ : Function.Injective ρ)
  (hdim : finrank (ZMod 2) Q = 4) (H : Alt7Hyp G)

include hρ hdim H

theorem fix_le_ker {R : Subgroup G} {t : G} (ht : t ∈ R) :
    fixSub ρ R ≤ LinearMap.ker (nilMap ρ t) := fun v hv =>
  (mem_ker_nilMap ρ t v).2 (hv t ht)

theorem finrank_ker_le_two {t : G} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    finrank (ZMod 2) (LinearMap.ker (nilMap ρ t)) ≤ 2 := by
  have : Module.Finite (ZMod 2) Q := Module.Finite.of_finite
  have h1 := LinearMap.finrank_range_add_finrank_ker (nilMap ρ t)
  have h2 := two_le_finrank_range_nilMap ρ hρ H.conj H.order5 ht1 ht2
  omega

theorem finrank_fix_le_two {R : Subgroup G} {t : G} (htR : t ∈ R) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    finrank (ZMod 2) (fixSub ρ R) ≤ 2 :=
  (Submodule.finrank_mono (fix_le_ker ρ hρ hdim H htR)).trans
    (finrank_ker_le_two ρ hρ hdim H ht1 ht2)

theorem card_R_eq_four {R : Subgroup G} (hR1 : R ≠ ⊥) (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hR2 : ∀ a ∈ R, a ^ 2 = 1)
    (hoff : Nat.card Q ≤ Nat.card R * Nat.card (fixSub ρ R)) :
    Nat.card R = 4 ∧ Nat.card (fixSub ρ R) = 4 := by
  obtain ⟨⟨t, htR⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hR1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hfin := finrank_fix_le_two ρ hρ hdim H htR ht1' (hR2 t htR)
  have hcard : Nat.card (fixSub ρ R) ≤ 4 := by
    rw [natCard_submodule_zmod2]
    calc 2 ^ finrank (ZMod 2) (fixSub ρ R) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hfin
      _ = 4 := by norm_num
  have hR4 := H.card_le R hRab hR2
  rw [natCard_space_four hdim] at hoff
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hfpos : 0 < Nat.card (fixSub ρ R) := Nat.card_pos
  constructor <;> nlinarith

theorem fix_eq_ker {R : Subgroup G} (hR1 : R ≠ ⊥) (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hR2 : ∀ a ∈ R, a ^ 2 = 1) (hoff : Nat.card Q ≤ Nat.card R * Nat.card (fixSub ρ R))
    {t : G} (htR : t ∈ R) (ht1 : t ≠ 1) :
    fixSub ρ R = LinearMap.ker (nilMap ρ t) := by
  have hc := (card_R_eq_four ρ hρ hdim H hR1 hRab hR2 hoff).2
  have hfr : finrank (ZMod 2) (fixSub ρ R) = 2 := by
    rw [natCard_submodule_zmod2] at hc
    have : (2 : ℕ) ^ finrank (ZMod 2) (fixSub ρ R) = 2 ^ 2 := by rw [hc]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  refine Submodule.eq_of_le_of_finrank_le (fix_le_ker ρ hρ hdim H htR) ?_
  rw [hfr]
  exact finrank_ker_le_two ρ hρ hdim H ht1 (hR2 t htR)

theorem range_le_fix {R : Subgroup G} (hR1 : R ≠ ⊥) (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hR2 : ∀ a ∈ R, a ^ 2 = 1) (hoff : Nat.card Q ≤ Nat.card R * Nat.card (fixSub ρ R))
    {t : G} (htR : t ∈ R) : LinearMap.range (nilMap ρ t) ≤ fixSub ρ R := by
  by_cases ht1 : t = 1
  · subst ht1
    rintro _ ⟨v, rfl⟩
    simp [nilMap_apply]
  · rw [fix_eq_ker ρ hρ hdim H hR1 hRab hR2 hoff htR ht1]
    exact range_le_ker_nilMap ρ (hR2 t htR)

end Local

section FGroup

variable (ρ : Representation (ZMod 2) G Q) (ℓ : Submodule (ZMod 2) Q)

theorem rho_inv_apply_rho (g : G) (w : Q) : ρ g⁻¹ (ρ g w) = w := by
  rw [← Module.End.mul_apply, ← map_mul]; simp

theorem rho_apply_rho_inv (g : G) (w : Q) : ρ g (ρ g⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul]; simp

theorem fix_aux {g h : G} (hg1 : ∀ v ∈ ℓ, ρ g v = v) (hh2 : ∀ q, nilMap ρ h q ∈ ℓ) (q : Q) :
    ρ g (ρ h q) = (ρ h q - q) + ρ g q := by
  have hm := hg1 _ (hh2 q)
  simp only [nilMap_apply, map_sub] at hm
  rw [← hm]; abel

@[expose] def fixF : Subgroup G where
  carrier := {g | (∀ v ∈ ℓ, ρ g v = v) ∧ ∀ q, nilMap ρ g q ∈ ℓ}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun v hv => ?_, fun q => ?_⟩
    · rw [map_mul, Module.End.mul_apply, hh1 v hv, hg1 v hv]
    · have hm' := fix_aux ρ ℓ hg1 hh2 q
      have : nilMap ρ (g * h) q = nilMap ρ g q + nilMap ρ h q := by
        simp only [nilMap_apply, map_mul, Module.End.mul_apply]
        rw [hm']; abel
      rw [this]
      exact ℓ.add_mem (hg2 q) (hh2 q)
  one_mem' := ⟨fun v _ => by simp, fun q => by simp [nilMap_apply]⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun v hv => ?_, fun q => ?_⟩
    · calc ρ g⁻¹ v = ρ g⁻¹ (ρ g v) := by rw [hg1 v hv]
        _ = v := rho_inv_apply_rho ρ g v
    · have h1 := hg2 (ρ g⁻¹ q)
      rw [nilMap_apply, rho_apply_rho_inv] at h1
      have : nilMap ρ g⁻¹ q = -(q - ρ g⁻¹ q) := by
        rw [nilMap_apply]; abel
      rw [this]
      exact ℓ.neg_mem h1

theorem fixF_sq (hρ : Function.Injective ρ) {g : G} (hg : g ∈ fixF ρ ℓ) : g ^ 2 = 1 := by
  obtain ⟨hg1, hg2⟩ := hg
  apply hρ
  rw [map_one, pow_two, map_mul]
  ext q
  simp only [Module.End.mul_apply, Module.End.one_apply]
  have e := fix_aux ρ ℓ hg1 hg2 q
  calc ρ g (ρ g q) = (ρ g q - q) + ρ g q := e
    _ = (ρ g q + ρ g q) - q := by abel
    _ = -q := by rw [two_smul_zmod2, zero_sub]
    _ = q := neg_eq_self_zmod2 q

theorem fixF_comm (hρ : Function.Injective ρ) {g h : G} (hg : g ∈ fixF ρ ℓ) (hh : h ∈ fixF ρ ℓ) :
    g * h = h * g := by
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  apply hρ
  rw [map_mul, map_mul]
  ext q
  simp only [Module.End.mul_apply]
  rw [fix_aux ρ ℓ hg1 hh2 q, fix_aux ρ ℓ hh1 hg2 q]
  abel

end FGroup

section Local2

variable (ρ : Representation (ZMod 2) G Q) (hρ : Function.Injective ρ)
  (hdim : finrank (ZMod 2) Q = 4) (H : Alt7Hyp G) {R : Subgroup G} (hR1 : R ≠ ⊥)
  (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hR2 : ∀ a ∈ R, a ^ 2 = 1)
  (hoff : Nat.card Q ≤ Nat.card R * Nat.card (fixSub ρ R))

include hρ hdim H hR1 hRab hR2 hoff

theorem eq_fixF : R = fixF ρ (fixSub ρ R) := by
  have hle : R ≤ fixF ρ (fixSub ρ R) := fun r hr =>
    ⟨fun v hv => hv r hr, fun q => range_le_fix ρ hρ hdim H hR1 hRab hR2 hoff hr ⟨q, rfl⟩⟩
  have hc4 := (card_R_eq_four ρ hρ hdim H hR1 hRab hR2 hoff).1
  have hFle := H.card_le (fixF ρ (fixSub ρ R))
    (fun a ha b hb => fixF_comm ρ _ hρ ha hb) (fun a ha => fixF_sq ρ _ hρ ha)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc4]; exact hFle)

theorem conj_mem_of_stab {g : G} (hs : ∀ v, v ∈ fixSub ρ R ↔ ρ g v ∈ fixSub ρ R) {r : G}
    (hr : r ∈ R) : g * r * g⁻¹ ∈ R := by
  rw [eq_fixF ρ hρ hdim H hR1 hRab hR2 hoff]
  have hr' : r ∈ fixF ρ (fixSub ρ R) := by
    rw [← eq_fixF ρ hρ hdim H hR1 hRab hR2 hoff]; exact hr
  obtain ⟨hr1, hr2⟩ := hr'
  refine ⟨fun v hv => ?_, fun q => ?_⟩
  · have hw : ρ g⁻¹ v ∈ fixSub ρ R := by
      rw [hs, rho_apply_rho_inv]; exact hv
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hr1 _ hw,
      rho_apply_rho_inv]
  · have hw := hr2 (ρ g⁻¹ q)
    have : nilMap ρ (g * r * g⁻¹) q = ρ g (nilMap ρ r (ρ g⁻¹ q)) := by
      simp only [nilMap_apply, map_sub, map_mul, Module.End.mul_apply, rho_apply_rho_inv]
    rw [this, ← hs]
    exact hw

theorem mem_normalizer_iff_stab {g : G} :
    g ∈ Subgroup.normalizer (R : Set G) ↔ ∀ v, v ∈ fixSub ρ R ↔ ρ g v ∈ fixSub ρ R := by
  constructor
  · intro hg
    have key : ∀ g' ∈ Subgroup.normalizer (R : Set G), ∀ v ∈ fixSub ρ R,
        ρ g' v ∈ fixSub ρ R := by
      intro g' hg' v hv r hr
      have h1 : g'⁻¹ * r * g' ∈ R :=
        (Subgroup.mem_normalizer_iff.1 hg' (g'⁻¹ * r * g')).2 (by simpa [mul_assoc] using hr)
      have e : r * g' = g' * (g'⁻¹ * r * g') := by group
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hv _ h1]
    intro v
    refine ⟨key g hg v, fun hv => ?_⟩
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hv
    rwa [rho_inv_apply_rho] at this
  · intro hs
    have hs' : ∀ v, v ∈ fixSub ρ R ↔ ρ g⁻¹ v ∈ fixSub ρ R := by
      intro v
      rw [hs (ρ g⁻¹ v), rho_apply_rho_inv]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => conj_mem_of_stab ρ hρ hdim H hR1 hRab hR2 hoff hs hh, fun hh => ?_⟩
    have := conj_mem_of_stab ρ hρ hdim H hR1 hRab hR2 hoff hs' hh
    simpa [mul_assoc] using this

theorem centralizer_le_normalizer {t : G} (htR : t ∈ R) (ht1 : t ≠ 1) {c : G}
    (hc : c ∈ Subgroup.centralizer {t}) : c ∈ Subgroup.normalizer (R : Set G) := by
  rw [mem_normalizer_iff_stab ρ hρ hdim H hR1 hRab hR2 hoff]
  have hct : ∀ d : G, d ∈ Subgroup.centralizer {t} → ∀ v, v ∈ fixSub ρ R → ρ d v ∈ fixSub ρ R := by
    intro d hd v hv
    rw [fix_eq_ker ρ hρ hdim H hR1 hRab hR2 hoff htR ht1] at hv ⊢
    rw [mem_ker_nilMap] at hv ⊢
    have e := (Subgroup.mem_centralizer_iff.1 hd) t (Set.mem_singleton t)
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hv]
  intro v
  refine ⟨hct c hc v, fun hv => ?_⟩
  have := hct c⁻¹ (Subgroup.inv_mem _ hc) _ hv
  rwa [rho_inv_apply_rho] at this

theorem exists_normalizer_conj {t₀ t₁ : G} (h0R : t₀ ∈ R) (h01 : t₀ ≠ 1) (h1R : t₁ ∈ R)
    (h11 : t₁ ≠ 1) : ∃ n ∈ Subgroup.normalizer (R : Set G), t₁ = n * t₀ * n⁻¹ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (H.conj t₀ t₁ h01 (hR2 t₀ h0R) h11 (hR2 t₁ h1R))
  refine ⟨c, ?_, hc.symm⟩
  rw [mem_normalizer_iff_stab ρ hρ hdim H hR1 hRab hR2 hoff]
  have k0 := fix_eq_ker ρ hρ hdim H hR1 hRab hR2 hoff h0R h01
  have k1 := fix_eq_ker ρ hρ hdim H hR1 hRab hR2 hoff h1R h11
  have e1 : t₁ * c = c * t₀ := by rw [← hc]; group
  have e2 : t₀ = c⁻¹ * t₁ * c := by rw [← hc]; group
  intro v
  constructor
  · intro hv
    rw [k0, mem_ker_nilMap] at hv
    rw [k1, mem_ker_nilMap, ← Module.End.mul_apply, ← map_mul, e1, map_mul,
      Module.End.mul_apply, hv]
  · intro hv
    rw [k1, mem_ker_nilMap] at hv
    rw [k0, mem_ker_nilMap]
    calc ρ t₀ v = ρ c⁻¹ (ρ t₁ (ρ c v)) := by
          conv_lhs => rw [e2]
          simp [map_mul, Module.End.mul_apply]
      _ = v := by rw [hv, rho_inv_apply_rho]

theorem card_normalizer_eq : Nat.card (Subgroup.normalizer (R : Set G)) = 72 := by
  classical
  obtain ⟨⟨t, htR⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hR1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hC : Subgroup.centralizer {t} ≤ Subgroup.normalizer (R : Set G) := fun c hc =>
    centralizer_le_normalizer ρ hρ hdim H hR1 hRab hR2 hoff htR ht1' hc
  have hN := card_eq_orbit_mul (Subgroup.normalizer (R : Set G)) t
  have hG := card_eq_orbit_mul (⊤ : Subgroup G) t
  rw [inf_eq_right.2 hC] at hN
  rw [top_inf_eq, Subgroup.card_top] at hG
  have hSN : {x : G | ∃ k ∈ Subgroup.normalizer (R : Set G), x = k * t * k⁻¹} =
      {x : G | x ∈ R ∧ x ≠ 1} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 hk t).1 htR, fun h => ht1' ?_⟩
      have : k * t * k⁻¹ = 1 := h
      simpa using this
    · rintro ⟨hxR, hx1⟩
      obtain ⟨n, hn, hxn⟩ := exists_normalizer_conj ρ hρ hdim H hR1 hRab hR2 hoff htR ht1' hxR hx1
      exact ⟨n, hn, hxn⟩
  have hSG : {x : G | ∃ k ∈ (⊤ : Subgroup G), x = k * t * k⁻¹} = {x : G | x ^ 2 = 1 ∧ x ≠ 1} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, -, rfl⟩
      refine ⟨?_, fun h => ht1' ?_⟩
      · have := hR2 t htR
        calc (k * t * k⁻¹) ^ 2 = k * t ^ 2 * k⁻¹ := by rw [pow_two, pow_two]; group
          _ = 1 := by rw [this]; group
      · have : k * t * k⁻¹ = 1 := h
        simpa using this
    · rintro ⟨hx2, hx1⟩
      obtain ⟨c, hc⟩ := isConj_iff.1 (H.conj t x ht1' (hR2 t htR) hx1 hx2)
      exact ⟨c, Subgroup.mem_top c, hc.symm⟩
  rw [hSN] at hN
  rw [hSG] at hG
  have h3 : Set.ncard {x : G | x ∈ R ∧ x ≠ 1} = 3 := by
    have hR4 := (card_R_eq_four ρ hρ hdim H hR1 hRab hR2 hoff).1
    have : {x : G | x ∈ R ∧ x ≠ 1} = (R : Set G) \ {1} := by
      ext x; simp
    rw [this, Set.ncard_sdiff_singleton_of_mem (R.one_mem)]
    have : (R : Set G).ncard = Nat.card R := (Nat.card_coe_set_eq _).symm
    rw [this, hR4]
  have h105 : Set.ncard {x : G | x ^ 2 = 1 ∧ x ≠ 1} = 105 := by
    rw [← H.card_inv, ← Nat.card_coe_set_eq]
    rfl
  rw [h3] at hN
  rw [h105, H.card_G] at hG
  omega

theorem alt7_four_offender :
    Nat.card R = 4 ∧ Nat.card (fixSub ρ R) = 4 ∧
      (∀ g : G, g ∈ Subgroup.normalizer (R : Set G) ↔
        ∀ v, v ∈ fixSub ρ R ↔ ρ g v ∈ fixSub ρ R) ∧
      Nat.card (Subgroup.normalizer (R : Set G)) = 72 ∧
      ∃ E : Subgroup G, E ≤ Subgroup.normalizer (R : Set G) ∧ Nat.card E = 9 := by
  obtain ⟨h4, hl4⟩ := card_R_eq_four ρ hρ hdim H hR1 hRab hR2 hoff
  have h72 := card_normalizer_eq ρ hρ hdim H hR1 hRab hR2 hoff
  exact ⟨h4, hl4, fun g => mem_normalizer_iff_stab ρ hρ hdim H hR1 hRab hR2 hoff, h72,
    H.klein R h4 hRab hR2 h72.ge⟩

end Local2

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
