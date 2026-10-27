module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbStep56
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveConn

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

namespace IIbSyl

theorem vElt_ne : ∀ x r x' : ZMod 2 × ZMod 2, r ≠ 0 → vElt x r ≠ vElt x' 0 := by decide +kernel

theorem vElt_split : ∀ x r : ZMod 2 × ZMod 2, vElt x r = vElt x 0 * vElt 0 r := by decide +kernel

theorem card_eq : Nat.card IIbSyl = 2 ^ 7 := card_IIbSyl

theorem roots_twelve : ∀ e : IIbSyl, e * e = 1 →
    12 ≤ (Finset.univ.filter (fun y : IIbSyl => y * y = e)).card → ∃ x, e = vElt x 0 := by
  decide +kernel

theorem card_roots_c1 :
    (Finset.univ.filter (fun y : IIbSyl => y * c1 = c1 * y ∧ y * y = z0)).card = 12 := by
  decide +kernel

theorem c1_facts : c1 * z0 = z0 * c1 ∧ c1 * c1 = 1 ∧ c1 ≠ 1 ∧ c1 ≠ z0 ∧ z0 ≠ 1 ∧ z0 * z0 = 1 := by
  decide

theorem vElt_mul_c1 : ∀ x : ZMod 2 × ZMod 2, vElt x 0 * c1 = c1 ∨ vElt x 0 * c1 = z0 * c1 ∨
    vElt x 0 * c1 = c1 * vv ∨ vElt x 0 * c1 = z0 * (c1 * vv) := by decide +kernel

theorem ss_c1 : (ss * c1 * ss⁻¹ = c1 * vv ∨ ss * c1 * ss⁻¹ = z0 * (c1 * vv)) ∧
    ss * z0 * ss⁻¹ = z0 := by decide

theorem invol_cases : ∀ m : IIbSyl, m * m = 1 →
    (∃ x, m = vElt x 0) ∨ (∃ x r, r ≠ 0 ∧ m = vElt x r) ∨
    (∃ x r, vElt x r * m * (vElt x r)⁻¹ = c1) ∨
    (∃ x r, vElt x r * m * (vElt x r)⁻¹ = ss ∨ (t * vElt x r) * m * (t * vElt x r)⁻¹ = ss) ∨
    (∃ x r, (vElt x r)⁻¹ * t * vElt x r = m ∨ (ss * vElt x r)⁻¹ * t * (ss * vElt x r) = m) := by
  decide +kernel

theorem conj_ss : ∀ m : IIbSyl, m * m = 1 → m.right = 1 → (∀ x y, m ≠ vElt x y) →
    m * a * m⁻¹ * a⁻¹ ≠ z0 →
    ∃ x r, vElt x r * m * (vElt x r)⁻¹ = ss ∨ (t * vElt x r) * m * (t * vElt x r)⁻¹ = ss := by
  decide +kernel

theorem comm_c1_a : c1 * a * c1⁻¹ * a⁻¹ = z0 := by decide

theorem c1_mem_P : c1 ∈ P := ⟨⟨Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (1, 0)⟩, rfl⟩

theorem right_eq_one_of_mem_P {m : IIbSyl} (hm : m ∈ P) : m.right = 1 := by
  obtain ⟨p, rfl⟩ := hm
  rfl

theorem t_facts : t * t = 1 ∧ c1 * t ≠ t * c1 := by decide

theorem c1_class : ∀ x r : ZMod 2 × ZMod 2, ∃ x' : ZMod 2 × ZMod 2,
    (vElt x r)⁻¹ * c1 * vElt x r = c1 * vElt x' 0 := by decide +kernel

def uu : IIbSyl := ⟨⟨Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (1, 1)⟩, 1⟩

theorem ss_bad : uu * z0 = z0 * uu ∧ uu * ss = ss * uu ∧ uu * uu = vv ∧ vv ≠ 1 ∧ vv ≠ z0 ∧
    vv ≠ ss ∧ vv ≠ z0 * ss := by decide

theorem c1_conj : ∀ s : IIbSyl, ∃ x : ZMod 2 × ZMod 2, s * c1 * s⁻¹ = c1 * vElt x 0 := by
  decide +kernel


end IIbSyl

theorem card_filter_le_of_injOn {α β : Type*} [Fintype α] [Fintype β] (ψ : α → β)
    {p : α → Prop} {q : β → Prop} [DecidablePred p] [DecidablePred q]
    (h1 : ∀ a, p a → q (ψ a)) (h2 : ∀ a b, p a → p b → ψ a = ψ b → a = b) :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card := by
  refine Finset.card_le_card_of_injOn ψ (fun a ha => ?_) (fun a ha b hb hab => ?_)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and] at ha ⊢
    exact h1 a ha
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and] at ha hb
    exact h2 a b ha hb hab

theorem rightConjugate_ptOf {G : Type*} [Group G] (z u g : G) :
    rightConjugate (ptOf z u) g = ptOf (g⁻¹ * z * g) (g⁻¹ * u * g) := by
  change (zpowers z ⊔ zpowers u).map (MulAut.conj g⁻¹).toMonoidHom = _
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  simp [ptOf]

namespace IIbData

variable {G : Type} [Group G] [Finite G] {A R T V₀ P : Subgroup G} {g t z₀ a σ c₁ : G}

theorem S₁_le (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁) :
    P ⊔ zpowers t ≤ normalizer (V₀ : Set G) ⊓ centralizer ({z₀} : Set G) := by
  have hPC : P ≤ centralizer (V₀ : Set G) := fun p hp =>
    (mem_transvGroup.mp (hD.sylowP.le hp)).2.1
  refine sup_le (fun p hp => mem_inf.mpr ⟨centralizer_le_normalizer _ (hPC hp), ?_⟩)
    (zpowers_le.mpr (mem_inf.mpr ⟨hS.normalizer_le_normalizer_V₀ hD.outer.normV, ?_⟩))
  · rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (hPC hp) z₀ hD.outer.z_mem).symm
  · rw [mem_centralizer_singleton_iff]
    exact hD.outer.z_comm

theorem le_E₁_of_conj (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    {x : G} (hzW : z₀ ∈ rightConjugate V₀ x) (hWS : rightConjugate V₀ x ≤ P ⊔ zpowers t) :
    rightConjugate V₀ x ≤ V₀ ⊔ zpowers c₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hfinj, hfrange, -, -, hfV0, hfR, hft, hfz, -, -, hfc⟩ := hD.emb
  have hV₀T : V₀ ≤ R ⊔ T := hS.loc.inf_A ▸ inf_le_left
  have hsq : ∀ w ∈ R ⊔ T, w * w = 1 := fun w hw => by rw [← sq]; exact hS.loc.elem.2 w hw
  have hcomm : ∀ w ∈ R ⊔ T, ∀ w' ∈ R ⊔ T, w * w' = w' * w := fun w hw w' hw' =>
    congrArg Subtype.val (hS.loc.elem.1.is_comm.comm ⟨w, hw⟩ ⟨w', hw'⟩)
  have hW : ∀ y, y ∈ rightConjugate V₀ x ↔ x * y * x⁻¹ ∈ V₀ := fun y =>
    mem_rightConjugate_iff V₀ x y
  have hW2 : ∀ y ∈ rightConjugate V₀ x, y * y = 1 := by
    intro y hy
    have h1 := hsq _ (hV₀T ((hW y).mp hy))
    have e : x * y * x⁻¹ * (x * y * x⁻¹) = x * (y * y) * x⁻¹ := by group
    rw [e] at h1
    have := congrArg (fun w => x⁻¹ * w * x) h1
    simpa [mul_assoc] using this
  have hWc : ∀ y ∈ rightConjugate V₀ x, ∀ y' ∈ rightConjugate V₀ x, y * y' = y' * y := by
    intro y hy y' hy'
    have h1 := hcomm _ (hV₀T ((hW y).mp hy)) _ (hV₀T ((hW y').mp hy'))
    have e1 : x * y * x⁻¹ * (x * y' * x⁻¹) = x * (y * y') * x⁻¹ := by group
    have e2 : x * y' * x⁻¹ * (x * y * x⁻¹) = x * (y' * y) * x⁻¹ := by group
    rw [e1, e2] at h1
    have := congrArg (fun w => x⁻¹ * w * x) h1
    simpa [mul_assoc] using this
  obtain ⟨eA⟩ := hS.equiv
  obtain ⟨yA, -, -, -, hk3, -⟩ := exists_klein_three eA hS.loc.sylowV₀.le hS.card_V₀
  have hzV₀ : z₀ ∈ V₀ := hD.outer.z_mem
  have hz1 : z₀ ≠ 1 := hD.outer.z_ne
  have hconjW : ∀ y ∈ rightConjugate V₀ x, y ≠ 1 → IsConj z₀ y := by
    intro y hy hy1
    have hxy : x * y * x⁻¹ ≠ 1 := fun e => hy1 (by
      have := congrArg (fun w => x⁻¹ * w * x) e
      simpa [mul_assoc] using this)
    obtain ⟨k, hk⟩ := hk3 z₀ hzV₀ _ ((hW y).mp hy) hz1 hxy
    refine isConj_iff.mpr ⟨x⁻¹ * (yA ^ k)⁻¹, ?_⟩
    rw [show x⁻¹ * (yA ^ k)⁻¹ * z₀ * (x⁻¹ * (yA ^ k)⁻¹)⁻¹ =
      x⁻¹ * ((yA ^ k)⁻¹ * z₀ * yA ^ k) * x by group, hk]
    group
  obtain ⟨y, hyW, hy1, hyz⟩ : ∃ y ∈ rightConjugate V₀ x, y ≠ 1 ∧ y ≠ z₀ := by
    by_contra hno
    push Not at hno
    have hle : rightConjugate V₀ x ≤ zpowers z₀ := fun y hy => by
      by_cases h1 : y = 1
      · rw [h1]; exact one_mem _
      · rw [hno y hy h1]; exact mem_zpowers z₀
    have h1 := card_le_of_le hle
    rw [rightConjugate_card, hS.card_V₀, Nat.card_zpowers,
      orderOf_eq_prime (by rw [sq]; exact hsq _ (hV₀T hzV₀)) hz1] at h1
    omega
  have hzy : z₀ * y = y * z₀ := hWc _ hzW _ hyW
  have hz2 : z₀ * z₀ = 1 := hW2 _ hzW
  have hy2 : y * y = 1 := hW2 _ hyW
  have hyzp : y ∉ zpowers z₀ := fun h => by
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hz2 h with e | e
    · exact hy1 e
    · exact hyz e
  have hWeq : ∀ w ∈ rightConjugate V₀ x, w = 1 ∨ w = z₀ ∨ w = y ∨ w = z₀ * y := by
    have hle : ptOf z₀ y ≤ rightConjugate V₀ x :=
      sup_le (zpowers_le.mpr hzW) (zpowers_le.mpr hyW)
    have heq := eq_of_le_of_card_ge hle (by
      rw [rightConjugate_card, hS.card_V₀, card_ptOf hz2 hz1 hy2 hzy hyzp])
    intro w hw
    rw [← heq] at hw
    exact (mem_ptOf hz2 hy2 hzy).mp hw
  obtain ⟨y', rfl⟩ : y ∈ f.range := hfrange ▸ hWS hyW
  have hy'2 : y' * y' = 1 := hfinj (by rw [map_mul, map_one]; exact hy2)
  have hy'1 : y' ≠ 1 := fun e => hy1 (by rw [e, map_one])
  have hy'z : y' ≠ IIbSyl.z0 := fun e => hyz (by rw [e, hfz])
  have hfV : ∀ x' : ZMod 2 × ZMod 2, f (IIbSyl.vElt x' 0) ∈ V₀ := fun x' => by
    rw [← hfV0]
    exact mem_map_of_mem f ⟨Multiplicative.ofAdd x', rfl⟩
  have hfR' : ∀ r : ZMod 2 × ZMod 2, f (IIbSyl.vElt 0 r) ∈ R := fun r => by
    rw [← hfR]
    exact mem_map_of_mem f ⟨Multiplicative.ofAdd r, rfl⟩
  rcases IIbSyl.invol_cases y' hy'2 with ⟨x', hx'⟩ | ⟨x', r, hr, hx'⟩ | ⟨x', r, hxr⟩ |
    ⟨x', r, hxr⟩ | ⟨x', r, hxr⟩
  ·
    intro w hw
    rcases hWeq w hw with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact mem_sup_left hzV₀
    · exact mem_sup_left (hx' ▸ hfV x')
    · exact mem_sup_left (mul_mem hzV₀ (hx' ▸ hfV x'))
  ·
    exfalso
    have hyV : f y' ∈ R ⊔ T := by
      rw [hx', IIbSyl.vElt_split, map_mul]
      exact mul_mem (hV₀T (hfV x')) (mem_sup_left (hfR' r))
    have hyV₀ : f y' ∉ V₀ := by
      intro hm
      rw [← hfV0] at hm
      obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hm
      exact IIbSyl.vElt_ne x' r _ hr (hx' ▸ (hfinj hw).symm)
    exact hS.not_isConj_of_mem_V₀ hzV₀ hz1 hyV hyV₀ (hconjW _ hyW hy1)
  ·
    obtain ⟨x'', hx''⟩ := IIbSyl.c1_class x' r
    have hy'e : y' = IIbSyl.c1 * IIbSyl.vElt x'' 0 := by rw [← hx'', ← hxr]; group
    have hyE : f y' ∈ V₀ ⊔ zpowers c₁ := by
      rw [hy'e, map_mul, hfc]
      exact mul_mem (mem_sup_right (mem_zpowers c₁)) (mem_sup_left (hfV x''))
    intro w hw
    rcases hWeq w hw with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact mem_sup_left hzV₀
    · exact hyE
    · exact mul_mem (mem_sup_left hzV₀) hyE
  ·
    exfalso
    obtain ⟨hu0, hus, huu, hv1, hvz, hvs, hvzs⟩ := IIbSyl.ss_bad
    have key : ∀ k : IIbSyl, k * y' * k⁻¹ = IIbSyl.ss → False := by
      intro k hk
      have hkz : f k * z₀ * (f k)⁻¹ = z₀ := by
        have hk' : f k ∈ P ⊔ zpowers t := hfrange ▸ (⟨k, rfl⟩ : f k ∈ f.range)
        have := mem_centralizer_singleton_iff.mp (mem_inf.mp (hD.S₁_le hS hk')).2
        rw [this, mul_inv_cancel_right]
      have hW' : ∀ w, w ∈ rightConjugate V₀ (x * (f k)⁻¹) →
          w = 1 ∨ w = z₀ ∨ w = f IIbSyl.ss ∨ w = z₀ * f IIbSyl.ss := by
        intro w hw
        have hw' : (f k)⁻¹ * w * f k ∈ rightConjugate V₀ x := by
          rw [mem_rightConjugate_iff] at hw ⊢
          rw [show x * ((f k)⁻¹ * w * f k) * x⁻¹ = x * (f k)⁻¹ * w * (x * (f k)⁻¹)⁻¹ by group]
          exact hw
        have hwe : w = f k * ((f k)⁻¹ * w * f k) * (f k)⁻¹ := by group
        have hss : f k * f y' * (f k)⁻¹ = f IIbSyl.ss := by
          rw [← hk, map_mul, map_mul, map_inv]
        rcases hWeq _ hw' with h1 | h1 | h1 | h1 <;> rw [hwe, h1]
        · left; group
        · exact Or.inr (Or.inl hkz)
        · exact Or.inr (Or.inr (Or.inl hss))
        · right; right; right
          rw [show f k * (z₀ * f y') * (f k)⁻¹ = (f k * z₀ * (f k)⁻¹) * (f k * f y' * (f k)⁻¹) by
            group, hkz, hss]
      have huC : f IIbSyl.uu ∈ centralizer ((rightConjugate V₀ (x * (f k)⁻¹) : Subgroup G) :
          Set G) := by
        rw [mem_centralizer_iff]
        intro w hw
        have huz : f IIbSyl.uu * z₀ = z₀ * f IIbSyl.uu := by rw [← hfz, ← map_mul, hu0, map_mul]
        have hus' : f IIbSyl.uu * f IIbSyl.ss = f IIbSyl.ss * f IIbSyl.uu := by
          rw [← map_mul, hus, map_mul]
        rcases hW' w hw with rfl | rfl | rfl | rfl
        · simp
        · exact huz.symm
        · exact hus'.symm
        · rw [mul_assoc, ← hus', ← mul_assoc, ← huz, mul_assoc]
      have hpg : IsPGroup 2 (zpowers (f IIbSyl.uu)) := by
        have h1 : IsPGroup 2 (⊤ : Subgroup IIbSyl) :=
          IsPGroup.of_card (n := 7) (by rw [card_top, IIbSyl.card_eq])
        have h2 := h1.map f
        rw [← MonoidHom.range_eq_map] at h2
        exact h2.to_le (zpowers_le.mpr ⟨IIbSyl.uu, rfl⟩)
      have hsq := hD.good (x * (f k)⁻¹) (f IIbSyl.uu) huC hpg
      rw [← map_mul, huu] at hsq
      rcases hW' _ hsq with e | e | e | e
      · exact hv1 (hfinj (e.trans (map_one f).symm))
      · exact hvz (hfinj (e.trans hfz.symm))
      · exact hvs (hfinj e)
      · exact hvzs (hfinj (by rw [e, map_mul, hfz]))
    rcases hxr with hxr | hxr
    · exact key _ hxr
    · exact key _ hxr
  ·
    exfalso
    apply hD.not_conj
    have key : ∀ h : IIbSyl, h⁻¹ * IIbSyl.t * h = y' → IsConj t (f y') := fun h hh =>
      isConj_iff.mpr ⟨(f h)⁻¹, by rw [inv_inv, ← hh, map_mul, map_mul, map_inv, hft]⟩
    have h1 : IsConj t (f y') := by
      rcases hxr with hxr | hxr
      · exact key _ hxr
      · exact key _ hxr
    exact h1.trans (hconjW _ hyW hy1).symm



omit [Finite G] in
theorem z₀_mem_S₁ (hD : IIbData A R T V₀ P t z₀ a σ c₁) : z₀ ∈ P ⊔ zpowers t := by
  obtain ⟨f, -, hfrange, -, -, -, -, -, hfz, -, -, -⟩ := hD.emb
  rw [← hfrange, ← hfz]
  exact ⟨_, rfl⟩

omit [Finite G] in
theorem c₁_mem_S₁ (hD : IIbData A R T V₀ P t z₀ a σ c₁) : c₁ ∈ P ⊔ zpowers t := by
  obtain ⟨f, -, hfrange, -, -, -, -, -, -, -, -, hfc⟩ := hD.emb
  rw [← hfrange, ← hfc]
  exact ⟨_, rfl⟩

theorem conj_ptOf_of_isConj (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    (hc : IsConj z₀ c₁) : ∃ x : G, rightConjugate V₀ x = ptOf z₀ c₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  obtain ⟨f, hfinj, hfrange, -, -, hfV0, -, -, hfz, -, -, hfc⟩ := hD.emb
  obtain ⟨hcz, hc2, hc1, hcz', hz1, hz2⟩ := IIbSyl.c1_facts
  obtain ⟨S, hS₁⟩ := Asc76X.exists_sylow_eq_of_isSylowOf_top hD.sylow
  have hzS : ∀ y ∈ (S : Subgroup G), z₀ * y = y * z₀ := fun y hy => by
    have := (hD.S₁_le hS (hS₁ ▸ hy)).2
    exact (mem_centralizer_singleton_iff.mp this).symm
  obtain ⟨k, hk, hkS⟩ := exists_conj_sylow_of_isConj S hzS hc
  have hmem : ∀ m : IIbSyl, m * IIbSyl.c1 = IIbSyl.c1 * m → k⁻¹ * f m * k ∈ f.range := by
    intro m hm
    rw [hfrange, ← hS₁]
    refine hkS _ ⟨?_, ?_⟩
    · rw [hS₁, ← hfrange]
      exact ⟨m, rfl⟩
    · exact mem_centralizer_singleton_iff.mpr (by rw [← hfc, ← map_mul, ← map_mul, hm])
  let ψ : IIbSyl → IIbSyl := fun m =>
    if h : m * IIbSyl.c1 = IIbSyl.c1 * m then
      (MonoidHom.ofInjective hfinj).symm ⟨_, hmem m h⟩ else 1
  have hψ : ∀ m (h : m * IIbSyl.c1 = IIbSyl.c1 * m), f (ψ m) = k⁻¹ * f m * k := by
    intro m h
    simp only [ψ, h, ↓reduceDIte]
    have := (MonoidHom.ofInjective hfinj).apply_symm_apply ⟨_, hmem m h⟩
    exact congrArg Subtype.val this
  have hz2' : z₀ * z₀ = 1 := by rw [← hfz, ← map_mul, hz2, map_one]
  set e := ψ IIbSyl.z0 with he_def
  have he : f e = k⁻¹ * z₀ * k := by rw [he_def, hψ _ hcz.symm, hfz]
  have he2 : e * e = 1 := by
    apply hfinj
    rw [map_mul, he, map_one]
    calc k⁻¹ * z₀ * k * (k⁻¹ * z₀ * k) = k⁻¹ * (z₀ * z₀) * k := by group
      _ = 1 := by rw [hz2']; group
  have hcard : 12 ≤ (Finset.univ.filter (fun y : IIbSyl => y * y = e)).card := by
    rw [← IIbSyl.card_roots_c1]
    refine card_filter_le_of_injOn ψ (fun m hm => ?_) (fun m m' hm hm' hmm' => ?_)
    · apply hfinj
      rw [map_mul, hψ m hm.1, he, ← hfz, ← hm.2, map_mul]
      group
    · have h1 := congrArg f hmm'
      rw [hψ m hm.1, hψ m' hm'.1] at h1
      apply hfinj
      have h2 := congrArg (fun y => k * y * k⁻¹) h1
      simpa [mul_assoc] using h2
  obtain ⟨x, hx⟩ := IIbSyl.roots_twelve e he2 hcard
  have hzV : k⁻¹ * z₀ * k ∈ V₀ := by
    rw [← he, hx, ← hfV0]
    exact mem_map_of_mem f ⟨Multiplicative.ofAdd x, rfl⟩
  have hzV₀ : z₀ ∈ V₀ := hD.outer.z_mem
  refine ⟨k⁻¹, (eq_of_le_of_card_ge (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_))
    ?_).symm⟩
  · rw [mem_rightConjugate_iff, inv_inv]
    exact hzV
  · rw [mem_rightConjugate_iff, inv_inv, ← hk]
    simpa [mul_assoc] using hzV₀
  · have hz1' : z₀ ≠ 1 := fun h1 => hz1 (hfinj (by rw [hfz, h1, map_one]))
    have hc2' : c₁ * c₁ = 1 := by rw [← hfc, ← map_mul, hc2, map_one]
    have hcz'' : z₀ * c₁ = c₁ * z₀ := by rw [← hfz, ← hfc, ← map_mul, ← map_mul, hcz]
    have hcn : c₁ ∉ zpowers z₀ := fun hm => by
      rcases RankTwoAltFive.eq_one_or_eq_of_mem_zpowers_of_sq hz2' hm with h1 | h1
      · exact hc1 (hfinj (by rw [hfc, h1, map_one]))
      · exact hcz' (hfinj (by rw [hfc, hfz, h1]))
    rw [rightConjugate_card, hS.card_V₀]
    exact (card_ptOf hz2' hz1' hc2' hcz'' hcn).ge

theorem line_conj (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    (hA : ∃ x : G, rightConjugate V₀ x = ptOf z₀ c₁) {e : G} (he : e ∈ V₀ ⊔ zpowers c₁)
    (hez : e ∉ zpowers z₀) : ∃ y : G, rightConjugate V₀ y = ptOf z₀ e := by
  obtain ⟨f, hfinj, -, -, -, hfV0, -, -, hfz, -, -, hfc⟩ := hD.emb
  obtain ⟨x₀, hx₀⟩ := hA
  obtain ⟨hcz, hc2, -, -, hz1, hz2⟩ := IIbSyl.c1_facts
  have hV : ∀ x : ZMod 2 × ZMod 2, f (IIbSyl.vElt x 0) ∈ V₀ := fun x => by
    rw [← hfV0]
    exact mem_map_of_mem f ⟨Multiplicative.ofAdd x, rfl⟩
  have hz2' : z₀ * z₀ = 1 := by rw [← hfz, ← map_mul, hz2, map_one]
  have hz1' : z₀ ≠ 1 := fun h1 => hz1 (hfinj (by rw [hfz, h1, map_one]))
  have hc2' : c₁ * c₁ = 1 := by rw [← hfc, ← map_mul, hc2, map_one]
  have hcN : zpowers c₁ ≤ normalizer (V₀ : Set G) :=
    zpowers_le.mpr ((hD.S₁_le hS (hD.c₁_mem_S₁)).1)
  obtain ⟨v, hv, b, hb, rfl⟩ := AS76b.exists_mul_of_mem_sup_of_le_normalizer hcN he
  obtain ⟨w, rfl⟩ : ∃ x : ZMod 2 × ZMod 2, f (IIbSyl.vElt x 0) = v := by
    rw [← hfV0] at hv
    obtain ⟨_, ⟨w, rfl⟩, rfl⟩ := hv
    exact ⟨Multiplicative.toAdd w, rfl⟩
  have hptz : ∀ u : G, ptOf z₀ (z₀ * u) = ptOf z₀ u := fun u => by
    simpa using IIbM12.ptOf_zpow_mul (z := z₀) 1 u
  rcases eq_one_or_eq_of_mem_zpowers_of_sq hc2' hb with hb1 | hb1 <;> rw [hb1] at hez ⊢
  ·
    refine ⟨1, ?_⟩
    rw [mul_one] at hez ⊢
    rw [rightConjugate_one]
    have hzu : z₀ * f (IIbSyl.vElt w 0) = f (IIbSyl.vElt w 0) * z₀ :=
      hS.comm (hS.V₀_le hD.outer.z_mem) (hS.V₀_le (hV w))
    refine (eq_of_le_of_card_ge (sup_le (zpowers_le.mpr hD.outer.z_mem)
      (zpowers_le.mpr (hV w))) ?_).symm
    rw [hS.card_V₀]
    exact (card_ptOf hz2' hz1' (hS.mul_self (hS.V₀_le (hV w))) hzu hez).ge
  ·
    have hs := IIbSyl.ss_c1
    have hW₂ : rightConjugate (ptOf z₀ c₁) (f IIbSyl.ss)⁻¹ =
        ptOf z₀ (f (IIbSyl.c1 * IIbSyl.vv)) := by
      rw [rightConjugate_ptOf, inv_inv, ← hfz, ← hfc, ← map_inv, ← map_mul, ← map_mul,
        ← map_mul, ← map_mul, hs.2]
      rcases hs.1 with h1 | h1 <;> rw [h1]
      rw [map_mul, hfz, hptz]
    rcases IIbSyl.vElt_mul_c1 w with h1 | h1 | h1 | h1 <;>
      rw [← hfc, ← map_mul, h1]
    · exact ⟨x₀, by rw [hx₀, hfc]⟩
    · exact ⟨x₀, by rw [map_mul, hfz, hptz, hx₀, hfc]⟩
    · exact ⟨x₀ * (f IIbSyl.ss)⁻¹, by rw [← rightConjugate_mul, hx₀, hW₂]⟩
    · exact ⟨x₀ * (f IIbSyl.ss)⁻¹, by
        rw [map_mul, hfz, hptz, ← rightConjugate_mul, hx₀, hW₂]⟩

theorem E₁_closed (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    (hA : ∃ x : G, rightConjugate V₀ x = ptOf z₀ c₁) {e : G} (he : e ∈ V₀ ⊔ zpowers c₁)
    {h : G} (hh : h ∈ centralizer ({z₀} : Set G)) (hS₁ : h⁻¹ * e * h ∈ P ⊔ zpowers t) :
    h⁻¹ * e * h ∈ V₀ ⊔ zpowers c₁ := by
  have hhz : h⁻¹ * z₀ * h = z₀ := by
    rw [mem_centralizer_singleton_iff] at hh
    rw [mul_assoc, ← hh, inv_mul_cancel_left]
  by_cases hez : e ∈ zpowers z₀
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hez
    have hc : Commute h z₀ := mem_centralizer_singleton_iff.mp hh
    rw [show h⁻¹ * z₀ ^ k * h = z₀ ^ k by
      rw [mul_assoc, ← (hc.zpow_right k).eq, inv_mul_cancel_left]]
    exact mem_sup_left (zpow_mem hD.outer.z_mem k)
  obtain ⟨y, hy⟩ := line_conj hS hD hA he hez
  have hW : rightConjugate V₀ (y * h) = ptOf z₀ (h⁻¹ * e * h) := by
    rw [← rightConjugate_mul, hy, rightConjugate_ptOf, hhz]
  have hle := le_E₁_of_conj hS hD (x := y * h) (by rw [hW]; exact mem_sup_left (mem_zpowers z₀))
    (by rw [hW]; exact sup_le (zpowers_le.mpr hD.z₀_mem_S₁) (zpowers_le.mpr hS₁))
  rw [hW] at hle
  exact hle (mem_sup_right (mem_zpowers _))

theorem S₁_le_of_V₀ (hD : IIbData A R T V₀ P t z₀ a σ c₁) (hS : Setting310 A R g T V₀) :
    V₀ ≤ P ⊔ zpowers t := by
  have hVP : R ⊔ T ≤ P := hD.inf_P ▸ inf_le_left
  exact (hS.V₀_le.trans hVP).trans le_sup_left

theorem f_vElt_mem {f : IIbSyl →* G} (hS : Setting310 A R g T V₀) (hfV0 : IIbSyl.V0.map f = V₀)
    (hfR : IIbSyl.R.map f = R) (x y : ZMod 2 × ZMod 2) : f (IIbSyl.vElt x y) ∈ R ⊔ T := by
  rw [IIbSyl.vElt_split, map_mul]
  refine mul_mem (hS.V₀_le ?_) (mem_sup_left ?_)
  · rw [← hfV0]
    exact mem_map_of_mem f ⟨Multiplicative.ofAdd x, rfl⟩
  · rw [← hfR]
    exact mem_map_of_mem f ⟨Multiplicative.ofAdd y, rfl⟩

theorem conj_mem_E₁ (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    {s : G} (hs : s ∈ P ⊔ zpowers t) {e : G} (he : e ∈ V₀ ⊔ zpowers c₁) :
    s * e * s⁻¹ ∈ V₀ ⊔ zpowers c₁ := by
  obtain ⟨f, -, hfrange, -, -, hfV0, -, -, -, -, -, hfc⟩ := hD.emb
  have hsN := (mem_inf.mp (hD.S₁_le hS hs)).1
  have hle : (V₀ ⊔ zpowers c₁).map (MulAut.conj s).toMonoidHom ≤ V₀ ⊔ zpowers c₁ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le ?_ (zpowers_le.mpr ?_)
    · rintro _ ⟨v, hv, rfl⟩
      exact mem_sup_left ((mem_normalizer_iff.mp hsN v).mp hv)
    · obtain ⟨m, rfl⟩ : s ∈ f.range := hfrange ▸ hs
      obtain ⟨x, hx⟩ := IIbSyl.c1_conj m
      change f m * c₁ * (f m)⁻¹ ∈ V₀ ⊔ zpowers c₁
      rw [← hfc, ← map_inv, ← map_mul, ← map_mul, hx, map_mul, hfc]
      refine mul_mem (mem_sup_right (mem_zpowers c₁)) (mem_sup_left ?_)
      rw [← hfV0]
      exact mem_map_of_mem f ⟨Multiplicative.ofAdd x, rfl⟩
  exact hle ⟨e, he, rfl⟩

end IIbData

end CFSG.ComponentClassification.RankTwoAltFive
