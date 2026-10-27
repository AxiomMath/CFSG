module

public import CFSG.Fischer.Classification.Basic.Reduced
public import CFSG.Fischer.Uniq.Connected
public import CFSG.Fischer.Uniq.MuSets

public section

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace CFSG.Fischer.Classification

variable {X : Type} [Group X] {E : Set X}

theorem Pair.commute_of_normalizes (hP : Pair X E) {R : Set X} (hRE : R ⊆ E)
    (hii : ∀ r ∈ R, ∀ x ∈ R, r * x * r ∈ R) {a : X} (ha : a ∈ E) (haR : a ∉ R)
    (hn : ∀ x ∈ R, a * x * a ∈ R) {x : X} (hx : x ∈ R) : a * x = x * a := by
  by_contra hax
  apply haR
  have h1 : x * a * x ∈ R := by
    rw [← Pair.mul_mul_eq hP ha (hRE hx) hax]
    exact hn x hx
  have := hii x hx _ h1
  rwa [Pair.mul_mul_mul_mul hP (hRE hx)] at this

theorem Pair.conj_mul_mem (hP : Pair X E) {R : Set X} (hRE : R ⊆ E)
    (hi : ∀ g : X, (∃ x ∈ R, g * x * g⁻¹ ∈ R) → ∀ x ∈ R, g * x * g⁻¹ ∈ R)
    (hii : ∀ r ∈ R, ∀ x ∈ R, r * x * r ∈ R) {r s : X} (hr : r ∈ R) (hs : s ∈ R)
    (hrs : r * s = s * r) (h : X) {a : X} (ha : a ∈ R) :
    h⁻¹ * (r * s * (h * a * h⁻¹) * (r * s)⁻¹) * h ∈ R := by
  have hrE := hRE hr
  have hsE := hRE hs
  have hrsi : (r * s)⁻¹ = r * s := by
    rw [mul_inv_rev, Pair.inv_eq hP hrE, Pair.inv_eq hP hsE, hrs]
  have hrs2 : r * s * (r * s) = 1 := by
    have := inv_mul_cancel (r * s)
    rwa [hrsi] at this
  set a' := h * a * h⁻¹ with ha'
  have ha'E : a' ∈ E := Pair.conj_mem hP (hRE ha) h
  have hback : h⁻¹ * a' * h = a := by rw [ha']; group
  have hconj : ∀ g : X, ∀ x ∈ R, g * x * g⁻¹ = a' → ∀ y ∈ R, h⁻¹ * (g * y * g⁻¹) * h ∈ R := by
    intro g x hx hgx y hy
    have := hi (h⁻¹ * g) ⟨x, hx, by
      rw [show h⁻¹ * g * x * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * x * g⁻¹) * h by group, hgx, hback]
      exact ha⟩ y hy
    rwa [show h⁻¹ * g * y * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * y * g⁻¹) * h by group] at this
  by_cases hmeet : ∃ x ∈ R, h * x * h⁻¹ ∈ R
  ·
    have h1 : a' ∈ R := hi h hmeet a ha
    have h2 : r * s * a' * (r * s)⁻¹ ∈ R := by
      rw [hrsi, show r * s * a' * (r * s) = r * (s * a' * s) * r by
        nth_rw 2 [hrs]; simp only [mul_assoc]]
      exact hii r hr _ (hii s hs _ h1)
    have := hconj 1 a' h1 (by group) _ h2
    simpa using this
  · push Not at hmeet
    have ha'R : a' ∉ R := hmeet a ha
    by_cases har : a' * r = r * a'
    ·
      have hn : ∀ x ∈ R, a' * x * a' ∈ R := by
        have := hi a' ⟨r, hr, by
          rw [Pair.inv_eq hP ha'E, show a' * r * a' = r by
            rw [har, mul_assoc, Pair.mul_self hP ha'E, mul_one]]
          exact hr⟩
        intro x hx
        have h3 := this x hx
        rwa [Pair.inv_eq hP ha'E] at h3
      have has : a' * s = s * a' := Pair.commute_of_normalizes hP hRE hii ha'E ha'R hn hs
      have hfix : r * s * a' * (r * s)⁻¹ = a' := by
        rw [hrsi]
        calc r * s * a' * (r * s) = r * (s * a') * (r * s) := by simp only [mul_assoc]
          _ = r * (a' * s) * (r * s) := by rw [has]
          _ = (r * a') * s * (r * s) := by simp only [mul_assoc]
          _ = (a' * r) * s * (r * s) := by rw [har]
          _ = a' * (r * s * (r * s)) := by simp only [mul_assoc]
          _ = a' := by rw [hrs2, mul_one]
      rw [hfix, hback]
      exact ha
    · by_cases has : a' * s = s * a'
      ·
        have hn : ∀ x ∈ R, a' * x * a' ∈ R := by
          have := hi a' ⟨s, hs, by
            rw [Pair.inv_eq hP ha'E, show a' * s * a' = s by
              rw [has, mul_assoc, Pair.mul_self hP ha'E, mul_one]]
            exact hs⟩
          intro x hx
          have h3 := this x hx
          rwa [Pair.inv_eq hP ha'E] at h3
        exact absurd (Pair.commute_of_normalizes hP hRE hii ha'E ha'R hn hr) har
      ·
        have hra : r * a' ≠ a' * r := fun h' => har h'.symm
        have hsa : s * a' ≠ a' * s := fun h' => has h'.symm
        have hb1 : a' * r * a' = r * a' * r := Pair.mul_mul_eq hP ha'E hrE har
        have hb2 : a' * s * a' = s * a' * s := Pair.mul_mul_eq hP ha'E hsE has
        have huE : r * a' * r ∈ E := Pair.mul_mul_mem hP hrE ha'E
        have hur : r * a' * r * r * (r * a' * r)⁻¹ = a' := by
          rw [Pair.inv_eq hP huE]
          calc r * a' * r * r * (r * a' * r) = r * a' * (r * r) * (r * a' * r) := by
                simp only [mul_assoc]
            _ = r * (a' * r * a') * r := by
                rw [Pair.mul_self hP hrE, mul_one]; simp only [mul_assoc]
            _ = r * (r * a' * r) * r := by rw [hb1]
            _ = a' := Pair.mul_mul_mul_mul hP hrE a'
        have hus : r * a' * r * s * (r * a' * r)⁻¹ = r * s * a' * (r * s)⁻¹ := by
          rw [Pair.inv_eq hP huE, hrsi]
          calc r * a' * r * s * (r * a' * r) = r * a' * (r * s * r) * a' * r := by
                simp only [mul_assoc]
            _ = r * a' * s * a' * r := by
                rw [hrs, mul_assoc s r r, Pair.mul_self hP hrE, mul_one]
            _ = r * (a' * s * a') * r := by simp only [mul_assoc]
            _ = r * (s * a' * s) * r := by rw [hb2]
            _ = r * s * a' * (s * r) := by simp only [mul_assoc]
            _ = r * s * a' * (r * s) := by rw [hrs]
        rw [← hus]
        exact hconj _ r hr hur s hs

theorem Pair.eq_of_closed (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {R : Set X} (hRE : R ⊆ E)
    (hi : ∀ g : X, (∃ x ∈ R, g * x * g⁻¹ ∈ R) → ∀ x ∈ R, g * x * g⁻¹ ∈ R)
    (hii : ∀ r ∈ R, ∀ x ∈ R, r * x * r ∈ R)
    (hiii : ∃ r ∈ R, ∃ s ∈ R, r ≠ s ∧ r * s = s * r) : R = E := by
  obtain ⟨r, hr, s, hs, hne, hrs⟩ := hiii
  have hrE := hRE hr
  have hsE := hRE hs
  have hnorm : ∀ g : X, (∀ x ∈ R, g * x * g⁻¹ ∈ R) → (∀ x ∈ R, g⁻¹ * x * g ∈ R) →
      g ∈ Subgroup.normalizer R := by
    intro g h1 h2 x
    refine ⟨h1 x, fun hx => ?_⟩
    have := h2 _ hx
    simpa [mul_assoc] using this
  have hrsi : (r * s)⁻¹ = r * s := by
    rw [mul_inv_rev, Pair.inv_eq hP hrE, Pair.inv_eq hP hsE, hrs]
  have hcore : r * s ∈ (Subgroup.normalizer R).normalCore := by
    intro b
    have key : ∀ x ∈ R, b * (r * s) * b⁻¹ * x * (b * (r * s) * b⁻¹)⁻¹ ∈ R := by
      intro x hx
      have := Pair.conj_mul_mem hP hRE hi hii hr hs hrs b⁻¹ hx
      convert this using 1
      group
    have hinv : (b * (r * s) * b⁻¹)⁻¹ = b * (r * s) * b⁻¹ := by
      rw [show (b * (r * s) * b⁻¹)⁻¹ = b * (r * s)⁻¹ * b⁻¹ by group, hrsi]
    refine hnorm _ key fun x hx => ?_
    have h := key x hx
    rw [hinv] at h
    rwa [hinv]
  have hcore_ne : (Subgroup.normalizer R).normalCore ≠ ⊥ := by
    intro h
    have h1 := hcore
    rw [h, Subgroup.mem_bot] at h1
    apply hne
    rw [← Pair.inv_eq hP hrE]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  have : (Subgroup.normalizer R).normalCore.Normal := Subgroup.normalCore_normal _
  have hle : commutator X ≤ Subgroup.normalizer R :=
    (commutator_le_of_normal hZ hS hcore_ne).trans (Subgroup.normalCore_le _)
  have hrN : r ∈ Subgroup.normalizer R :=
    hnorm r (fun x hx => by rw [Pair.inv_eq hP hrE]; exact hii r hr x hx)
      (fun x hx => by rw [Pair.inv_eq hP hrE]; exact hii r hr x hx)
  have hEN : ∀ e ∈ E, e ∈ Subgroup.normalizer R := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := Pair.exists_mem_commutator_conj hP hrE he
    exact mul_mem (mul_mem (hle hk) hrN) (inv_mem (hle hk))
  have htop : Subgroup.normalizer R = ⊤ := by
    rw [eq_top_iff, ← Pair.closure_eq hP, Subgroup.closure_le]
    exact hEN
  refine Set.Subset.antisymm hRE fun e he => ?_
  obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hrE he)
  have hg : g ∈ Subgroup.normalizer R := htop ▸ Subgroup.mem_top g
  exact (hg r).1 hr

@[expose] def ncReach (E : Set X) (x : X) : X → X → Prop :=
  Relation.ReflTransGen fun a b => a ∈ LocalClass E x ∧ b ∈ LocalClass E x ∧ a * b ≠ b * a

theorem ncReach.mem {x w v : X} (h : ncReach E x w v) (hw : w ∈ LocalClass E x) :
    v ∈ LocalClass E x := by
  induction h with
  | refl => exact hw
  | tail _ hbc _ => exact hbc.2.1

theorem ncReach.symm {x w v : X} (h : ncReach E x w v) : ncReach E x v w := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, fun e => hbc.2.2 e.symm⟩ ih

theorem ncReach.trans {x u v w : X} (h₁ : ncReach E x u v) (h₂ : ncReach E x v w) :
    ncReach E x u w :=
  Relation.ReflTransGen.trans h₁ h₂

theorem ncReach.tail' {x u v w : X} (h : ncReach E x u v) (hv : v ∈ LocalClass E x)
    (hw : w ∈ LocalClass E x) (hvw : v * w ≠ w * v) : ncReach E x u w :=
  Relation.ReflTransGen.tail h ⟨hv, hw, hvw⟩

theorem Pair.ncReach_conj (hP : Pair X E) (g : X) {x a b : X} (h : ncReach E x a b) :
    ncReach E (g * x * g⁻¹) (g * a * g⁻¹) (g * b * g⁻¹) := by
  refine Relation.ReflTransGen.lift (fun y => g * y * g⁻¹) (fun u v huv => ?_) _ _ h
  refine ⟨(Pair.conj_mem_localClass_iff hP g).2 huv.1,
    (Pair.conj_mem_localClass_iff hP g).2 huv.2.1, ?_⟩
  rw [Ne, conj_commute_iff]
  exact huv.2.2

theorem Pair.exists_conj_of_ncReach (hP : Pair X E) {x a b : X} (h : ncReach E x a b) :
    ∃ k ∈ LocalGroup E x, k * a * k⁻¹ = b := by
  induction h with
  | refl => exact ⟨1, one_mem _, by group⟩
  | @tail b c _ hbc ih =>
    obtain ⟨k, hk, hkb⟩ := ih
    refine ⟨b * c * k, mul_mem (mul_mem (mem_localGroup hbc.1) (mem_localGroup hbc.2.1)) hk, ?_⟩
    rw [show b * c * k * a * (b * c * k)⁻¹ = b * c * (k * a * k⁻¹) * (b * c)⁻¹ by group, hkb]
    exact Pair.mul_conj_left_eq hP hbc.1.1 hbc.2.1.1 hbc.2.2

theorem Pair.ncReach_mul_mul (hP : Pair X E) {x w a f : X} (hw : w ∈ LocalClass E x)
    (ha : ncReach E x w a) (hf : f ∈ LocalClass E x) : ncReach E x w (f * a * f) := by
  have haD := ha.mem hw
  by_cases hfa : f * a = a * f
  · rw [hfa, mul_assoc, Pair.mul_self hP hf.1, mul_one]
    exact ha
  · have h1 : ncReach E x w f := ha.tail' haD hf fun e => hfa e.symm
    have hfaf : f * a * f ∈ LocalClass E x := by
      refine ⟨Pair.mul_mul_mem hP hf.1 haD.1, fun e => haD.2.1 ?_,
        (commute_mul_mul_of_commute hf.2.2.symm haD.2.2.symm).symm⟩
      rw [← Pair.mul_mul_mul_mul hP hf.1 a, e, hf.2.2, mul_assoc, Pair.mul_self hP hf.1,
        mul_one]
    exact h1.tail' hf hfaf fun e => Pair.mul_mul_not_commute_left hP hf.1 hfa e.symm

theorem ncReach_of_subset {d x w v : X} (h : ncReach E d w v)
    (hsub : ∀ u, ncReach E d w u → u ∈ LocalClass E x) : ncReach E x w v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hb hbc ih => exact ih.tail' (hsub b hb) (hsub c (hb.tail hbc)) hbc.2.2

theorem Pair.subset_of_meet (hP : Pair X E) {W K V L : Set X} (hWE : W ⊆ E)
    (hK : ∀ x, x ∈ K ↔ x ∈ E ∧ x ∉ W ∧ ∀ a ∈ W, x * a = a * x)
    (hL : ∀ x, x ∈ L ↔ x ∈ E ∧ x ∉ V ∧ ∀ a ∈ V, x * a = a * x)
    (hLc : ∀ x ∈ L, ∀ y ∈ E, x * y = y * x → y ∈ V ∨ y ∈ L)
    (hLn : ∀ x ∈ L, ∀ y ∈ E, x * y = y * x → ∀ a ∈ V, y * a * y ∈ V)
    (hWconn : ∀ a ∈ W, ∀ b ∈ W,
      Relation.ReflTransGen (fun u v => u ∈ W ∧ v ∈ W ∧ u * v ≠ v * u) a b)
    (hcard : V.ncard ≤ W.ncard) (hVfin : V.Finite)
    {y : X} (hyK : y ∈ K) (hyL : y ∈ L) (hKL : K ≠ L) : W ⊆ L := by
  have hWy : ∀ a ∈ W, y * a = a * y := ((hK y).1 hyK).2.2
  have hyE : y ∈ E := ((hK y).1 hyK).1
  have hWV : ∀ a ∈ W, ∀ v ∈ V, a * v * a ∈ V := fun a ha => hLn y hyL a (hWE ha) (hWy a ha)
  have hWL : ∀ a ∈ W, ∀ z ∈ L, a * z * a ∈ L := by
    intro a ha z hz
    have haE := hWE ha
    obtain ⟨hzE, hzV, hzc⟩ := (hL z).1 hz
    refine (hL _).2 ⟨Pair.mul_mul_mem hP haE hzE, fun h => hzV ?_, fun v hv => ?_⟩
    · have := hWV a ha _ h
      rwa [Pair.mul_mul_mul_mul hP haE] at this
    · have h1 := hzc _ (hWV a ha v hv)
      calc a * z * a * v = a * (z * (a * v * a)) * a := by
            simp only [mul_assoc, Pair.mul_self hP haE, mul_one]
        _ = a * (a * v * a * z) * a := by rw [h1]
        _ = v * (a * z * a) := by
            simp only [← mul_assoc, Pair.mul_self hP haE, one_mul]
  have hmeet : ∃ a ∈ W, a ∈ L := by
    by_contra! hno
    have hWV' : W ⊆ V := fun a ha =>
      (hLc y hyL a (hWE ha) (hWy a ha)).resolve_right (hno a ha)
    have hWeq : W = V := Set.eq_of_subset_of_ncard_le hWV' hcard hVfin
    apply hKL
    ext x
    rw [hK, hL, hWeq]
  obtain ⟨a₀, ha₀W, ha₀L⟩ := hmeet
  suffices h : ∀ b, Relation.ReflTransGen (fun u v => u ∈ W ∧ v ∈ W ∧ u * v ≠ v * u) a₀ b →
      b ∈ L from fun b hb => h b (hWconn a₀ ha₀W b hb)
  intro b hpath
  induction hpath with
  | refl => exact ha₀L
  | @tail u v _ huv ih =>
    have hvE := hWE huv.2.1
    have huE := hWE huv.1
    have h1 : v * u * v ∈ L := hWL v huv.2.1 u ih
    rw [Pair.mul_mul_eq hP hvE huE fun e => huv.2.2 e.symm] at h1
    have h2 := hWL u huv.1 _ h1
    rwa [Pair.mul_mul_mul_mul hP huE] at h2

theorem ncReach.reflTransGen_comp {d w₁ a b : X} (ha : ncReach E d w₁ a) (h : ncReach E d a b) :
    Relation.ReflTransGen (fun u v => u ∈ {v | ncReach E d w₁ v} ∧ v ∈ {v | ncReach E d w₁ v} ∧
      u * v ≠ v * u) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hb hbc ih =>
    have hb' : ncReach E d w₁ b := ha.trans hb
    exact ih.tail ⟨hb', hb'.tail hbc, hbc.2.2⟩

theorem Pair.ncReach_localClass (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {d f₀ g₀ : X} (hd : d ∈ E)
    (hf₀ : f₀ ∈ LocalClass E d) (hg₀ : g₀ ∈ LocalClass E d) : ncReach E d f₀ g₀ := by
  by_contra hfg
  have hfin := Pair.finite hP
  obtain ⟨w₁, hw₁, hmax⟩ := Set.exists_max_image (LocalClass E d)
    (fun w => {v | ncReach E d w v}.ncard) (Set.toFinite _) ⟨f₀, hf₀⟩
  set W : Set X := {v | ncReach E d w₁ v} with hW
  have hWD : W ⊆ LocalClass E d := fun v hv => ncReach.mem hv hw₁
  have hWE : W ⊆ E := fun v hv => (hWD hv).1
  have hw₁W : w₁ ∈ W := Relation.ReflTransGen.refl
  have hbound : ∀ x ∈ E, ∀ w ∈ LocalClass E x, {v | ncReach E x w v}.ncard ≤ W.ncard := by
    intro x hx w hw
    obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd hx)
    have hw' : g⁻¹ * w * g ∈ LocalClass E d :=
      (Pair.conj_mem_localClass_iff hP g).1 (by rwa [show g * (g⁻¹ * w * g) * g⁻¹ = w by group])
    have hsub : {v | ncReach E (g * d * g⁻¹) w v} ⊆
        (fun y => g * y * g⁻¹) '' {v | ncReach E d (g⁻¹ * w * g) v} := by
      intro v hv
      refine ⟨g⁻¹ * v * g, ?_, by group⟩
      have := Pair.ncReach_conj hP g⁻¹ hv
      rwa [show g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d by group, inv_inv] at this
    calc {v | ncReach E (g * d * g⁻¹) w v}.ncard
        ≤ ((fun y => g * y * g⁻¹) '' {v | ncReach E d (g⁻¹ * w * g) v}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ {v | ncReach E d (g⁻¹ * w * g) v}.ncard := Set.ncard_image_le (Set.toFinite _)
      _ ≤ W.ncard := hmax _ hw'
  have hWreach : ∀ a ∈ W, ∀ b ∈ W, ncReach E d a b := fun a ha b hb =>
    (ha : ncReach E d w₁ a).symm.trans hb
  have hWnorm : ∀ a ∈ W, ∀ b ∈ W, a * b * a ∈ W := fun a ha b hb =>
    Pair.ncReach_mul_mul hP hw₁ hb (hWD ha)
  have hout : ∀ f ∈ LocalClass E d, f ∉ W → ∀ a ∈ W, f * a = a * f := by
    intro f hf hfW a ha
    by_contra hfa
    exact hfW ((ha : ncReach E d w₁ a).tail' (hWD ha) hf fun e => hfa e.symm)
  have hsub : ∀ x ∈ E, x ∉ W → (∀ a ∈ W, x * a = a * x) → W ⊆ LocalClass E x :=
    fun x _ hxW hxc a ha => ⟨hWE ha, fun e => hxW (e ▸ ha), (hxc a ha).symm⟩
  have hWcomp : ∀ x ∈ E, x ∉ W → (∀ a ∈ W, x * a = a * x) →
      {v | ncReach E x w₁ v} = W := by
    intro x hx hxW hxc
    have h1 : W ⊆ {v | ncReach E x w₁ v} := fun v hv =>
      ncReach_of_subset hv fun u hu => hsub x hx hxW hxc hu
    exact (Set.eq_of_subset_of_ncard_le h1 (hbound x hx w₁ (hsub x hx hxW hxc hw₁W))
      (Set.toFinite _)).symm
  have hnormK : ∀ x ∈ E, x ∉ W → (∀ a ∈ W, x * a = a * x) → ∀ y ∈ E, x * y = y * x →
      ∀ a ∈ W, y * a * y ∈ W := by
    intro x hx hxW hxc y hy hxy a ha
    by_cases hyx : y = x
    · rw [hyx, hxc a ha, mul_assoc, Pair.mul_self hP hx, mul_one]
      exact ha
    · have hyD : y ∈ LocalClass E x := ⟨hy, hyx, hxy.symm⟩
      have hcomp := hWcomp x hx hxW hxc
      have ha' : ncReach E x w₁ a := by rw [← hcomp] at ha; exact ha
      have := Pair.ncReach_mul_mul hP (hsub x hx hxW hxc hw₁W) ha' hyD
      rw [← hcomp]
      exact this
  have hcomm_of_norm : ∀ x ∈ E, x ∉ W → (∀ a ∈ W, x * a * x ∈ W) → ∀ a ∈ W, x * a = a * x :=
    fun x hx hxW hn a ha => Pair.commute_of_normalizes hP hWE hWnorm hx hxW hn ha
  set K : Set X := {x | x ∈ E ∧ x ∉ W ∧ ∀ a ∈ W, x * a = a * x} with hKdef
  have hK : ∀ x, x ∈ K ↔ x ∈ E ∧ x ∉ W ∧ ∀ a ∈ W, x * a = a * x := fun x => Iff.rfl
  have hKc : ∀ x ∈ K, ∀ y ∈ E, x * y = y * x → y ∈ W ∨ y ∈ K := by
    intro x hx y hy hxy
    by_cases hyW : y ∈ W
    · exact Or.inl hyW
    · exact Or.inr ⟨hy, hyW, hcomm_of_norm y hy hyW (hnormK x hx.1 hx.2.1 hx.2.2 y hy hxy)⟩
  have hKn : ∀ x ∈ K, ∀ y ∈ E, x * y = y * x → ∀ a ∈ W, y * a * y ∈ W :=
    fun x hx => hnormK x hx.1 hx.2.1 hx.2.2
  have hdK : d ∈ K := ⟨hd, fun h => (hWD h).2.1 rfl, fun a ha => (hWD ha).2.2.symm⟩
  obtain ⟨f, hfD, hfW⟩ : ∃ f ∈ LocalClass E d, f ∉ W := by
    by_contra! hall
    exact hfg (hWreach f₀ (hall f₀ hf₀) g₀ (hall g₀ hg₀))
  have hfK : f ∈ K := ⟨hfD.1, hfW, hout f hfD hfW⟩
  have hKii : ∀ k ∈ K, ∀ x ∈ K, k * x * k ∈ K := by
    intro k hk x hx
    refine ⟨Pair.mul_mul_mem hP hk.1 hx.1, fun h => hx.2.1 ?_, fun a ha => ?_⟩
    · have hc := hk.2.2 _ h
      rw [← Pair.mul_mul_mul_mul hP hk.1 x, hc, mul_assoc, Pair.mul_self hP hk.1, mul_one]
      exact h
    · exact (commute_mul_mul_of_commute (hk.2.2 a ha).symm (hx.2.2 a ha).symm).symm
  have hKE : K ⊆ E := fun x hx => hx.1
  have hw₁K : w₁ ∉ K := fun h => h.2.1 hw₁W
  have hKi : ¬ ∀ g : X, (∃ x ∈ K, g * x * g⁻¹ ∈ K) → ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
    intro hi
    have := Pair.eq_of_closed hP hZ hS hKE hi hKii
      ⟨d, hdK, f, hfK, fun e => hfD.2.1 e.symm, hfD.2.2.symm⟩
    exact hw₁K (by rw [this]; exact hWE hw₁W)
  push Not at hKi
  obtain ⟨g, ⟨y₀, hy₀K, hgy₀⟩, x₁, hx₁K, hgx₁⟩ := hKi
  set L : Set X := {z | g⁻¹ * z * g ∈ K} with hLdef
  set V : Set X := {v | g⁻¹ * v * g ∈ W} with hVdef
  have hconjE : ∀ z, g⁻¹ * z * g ∈ E ↔ z ∈ E := fun z => by
    simpa using Pair.conj_mem_iff hP g⁻¹ (a := z)
  have hVimg : V = (fun y => g * y * g⁻¹) '' W := by
    ext v
    refine ⟨fun hv => ⟨g⁻¹ * v * g, hv, by group⟩, ?_⟩
    rintro ⟨a, ha, rfl⟩
    change g⁻¹ * (g * a * g⁻¹) * g ∈ W
    rwa [show g⁻¹ * (g * a * g⁻¹) * g = a by group]
  have hVE : V ⊆ E := fun v hv => (hconjE v).1 (hWE hv)
  have hcard : V.ncard = W.ncard := by
    rw [hVimg]
    exact Set.ncard_image_of_injective _ (conj_injective g)
  have hcomm_conj : ∀ z v : X, g⁻¹ * z * g * (g⁻¹ * v * g) = g⁻¹ * v * g * (g⁻¹ * z * g) ↔
      z * v = v * z := fun z v => by
    simpa using conj_commute_iff g⁻¹ z v
  have hL : ∀ z, z ∈ L ↔ z ∈ E ∧ z ∉ V ∧ ∀ v ∈ V, z * v = v * z := by
    intro z
    change g⁻¹ * z * g ∈ K ↔ _
    rw [hK, hconjE]
    refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h v hv => ?_, fun h a ha => ?_⟩
    · exact (hcomm_conj z v).1 (h _ hv)
    · have hv : g * a * g⁻¹ ∈ V := by
        change g⁻¹ * (g * a * g⁻¹) * g ∈ W
        rwa [show g⁻¹ * (g * a * g⁻¹) * g = a by group]
      have := (hcomm_conj z _).2 (h _ hv)
      rwa [show g⁻¹ * (g * a * g⁻¹) * g = a by group] at this
  have hLc : ∀ x ∈ L, ∀ y ∈ E, x * y = y * x → y ∈ V ∨ y ∈ L := fun x hx y hy hxy =>
    hKc _ hx _ ((hconjE y).2 hy) ((hcomm_conj x y).2 hxy)
  have hLn : ∀ x ∈ L, ∀ y ∈ E, x * y = y * x → ∀ v ∈ V, y * v * y ∈ V := by
    intro x hx y hy hxy v hv
    have := hKn _ hx _ ((hconjE y).2 hy) ((hcomm_conj x y).2 hxy) _ hv
    change g⁻¹ * (y * v * y) * g ∈ W
    rwa [show g⁻¹ * y * g * (g⁻¹ * v * g) * (g⁻¹ * y * g) = g⁻¹ * (y * v * y) * g by group]
      at this
  have hWconn : ∀ a ∈ W, ∀ b ∈ W,
      Relation.ReflTransGen (fun u v => u ∈ W ∧ v ∈ W ∧ u * v ≠ v * u) a b :=
    fun a ha b hb => ncReach.reflTransGen_comp ha (hWreach a ha b hb)
  have hVconn : ∀ a ∈ V, ∀ b ∈ V,
      Relation.ReflTransGen (fun u v => u ∈ V ∧ v ∈ V ∧ u * v ≠ v * u) a b := by
    intro a ha b hb
    have h := hWconn _ ha _ hb
    have h' : Relation.ReflTransGen (fun u v => u ∈ V ∧ v ∈ V ∧ u * v ≠ v * u)
        (g * (g⁻¹ * a * g) * g⁻¹) (g * (g⁻¹ * b * g) * g⁻¹) := by
      refine Relation.ReflTransGen.lift (fun y => g * y * g⁻¹) (fun u v huv => ⟨?_, ?_, ?_⟩) _ _ h
      · change g⁻¹ * (g * u * g⁻¹) * g ∈ W
        rw [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
        exact huv.1
      · change g⁻¹ * (g * v * g⁻¹) * g ∈ W
        rw [show g⁻¹ * (g * v * g⁻¹) * g = v by group]
        exact huv.2.1
      · rw [Ne, conj_commute_iff]
        exact huv.2.2
    rwa [show g * (g⁻¹ * a * g) * g⁻¹ = a by group, show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
      at h'
  have hyK : g * y₀ * g⁻¹ ∈ K := hgy₀
  have hyL : g * y₀ * g⁻¹ ∈ L := by
    change g⁻¹ * (g * y₀ * g⁻¹) * g ∈ K
    rwa [show g⁻¹ * (g * y₀ * g⁻¹) * g = y₀ by group]
  have hKL : K ≠ L := by
    intro h
    apply hgx₁
    have : g * x₁ * g⁻¹ ∈ L := by
      change g⁻¹ * (g * x₁ * g⁻¹) * g ∈ K
      rwa [show g⁻¹ * (g * x₁ * g⁻¹) * g = x₁ by group]
    rwa [← h] at this
  have hWL : W ⊆ L := Pair.subset_of_meet hP hWE hK hL hLc hLn hWconn hcard.le
    (Set.toFinite _) hyK hyL hKL
  have hVK : V ⊆ K := Pair.subset_of_meet hP hVE hL hK hKc hKn hVconn hcard.ge
    (Set.toFinite _) hyL hyK hKL.symm
  have hLWK : ∀ z ∈ L, z ∈ W ∨ z ∈ K := by
    intro z hz
    obtain ⟨hzE, -, hzc⟩ := (hL z).1 hz
    have hv : g * w₁ * g⁻¹ ∈ V := by
      change g⁻¹ * (g * w₁ * g⁻¹) * g ∈ W
      rwa [show g⁻¹ * (g * w₁ * g⁻¹) * g = w₁ by group]
    exact hKc _ (hVK hv) z hzE (hzc _ hv).symm
  have hR : ∀ s, s ∈ W ∨ s ∈ K → ∀ t ∈ E, s * t = t * s → t ∈ W ∨ t ∈ K := by
    rintro s (hs | hs) t ht hst
    · rcases hLc s (hWL hs) t ht hst with h | h
      · exact Or.inr (hVK h)
      · exact hLWK t h
    · exact hKc s hs t ht hst
  have hconn := Pair.connected_of_simple hP hS
    ⟨d, f, hd, hfD.1, fun e => hfD.2.1 e.symm, hfD.2.2.symm⟩
  have hall : ∀ e ∈ E, e ∈ W ∨ e ∈ K := by
    intro e he
    have := reachable_induction (G := commGraph E) (p := fun a : E => (a : X) ∈ W ∨ (a : X) ∈ K)
      (fun a b hab ha => hR a ha b b.2 hab.2) (hconn ⟨d, hd⟩ ⟨e, he⟩) (Or.inr hdK)
    exact this
  have hEN : ∀ e ∈ E, e ∈ Subgroup.normalizer W := by
    intro e he a
    have hn : ∀ b ∈ W, e * b * e ∈ W := by
      rcases hall e he with h | h
      · exact hWnorm e h
      · intro b hb
        rw [h.2.2 b hb, mul_assoc, Pair.mul_self hP he, mul_one]
        exact hb
    rw [Pair.inv_eq hP he]
    refine ⟨hn a, fun ha => ?_⟩
    have := hn _ ha
    rwa [Pair.mul_mul_mul_mul hP he] at this
  have htop : Subgroup.normalizer W = ⊤ := by
    rw [eq_top_iff, ← Pair.closure_eq hP, Subgroup.closure_le]
    exact hEN
  obtain ⟨k, hk⟩ := isConj_iff.1 (Pair.isConj hP (hWE hw₁W) hd)
  have hkN : k ∈ Subgroup.normalizer W := htop ▸ Subgroup.mem_top k
  have hdW : d ∈ W := by
    rw [← hk]
    exact (hkN w₁).1 hw₁W
  exact (hWD hdW).2.1 rfl

theorem Pair.exists_localGroup_conj (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {d f g : X} (hd : d ∈ E) (hf : f ∈ LocalClass E d)
    (hg : g ∈ LocalClass E d) : ∃ h ∈ LocalGroup E d, h * f * h⁻¹ = g :=
  Pair.exists_conj_of_ncReach hP (Pair.ncReach_localClass hP hZ hS hd hf hg)

@[expose] def farClass (E : Set X) (d : X) : Set X := {c | c ∈ E ∧ c * d ≠ d * c}

theorem mem_farClass {d c : X} : c ∈ farClass E d ↔ c ∈ E ∧ c * d ≠ d * c := Iff.rfl

@[expose] def cReach (E : Set X) (d : X) : X → X → Prop :=
  Relation.ReflTransGen fun a b => a ∈ farClass E d ∧ b ∈ farClass E d ∧ a * b = b * a

theorem cReach.mem {d a b : X} (h : cReach E d a b) (ha : a ∈ farClass E d) :
    b ∈ farClass E d := by
  induction h with
  | refl => exact ha
  | tail _ hbc _ => exact hbc.2.1

theorem cReach.symm {d a b : X} (h : cReach E d a b) : cReach E d b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih

theorem cReach.trans {d a b c : X} (h₁ : cReach E d a b) (h₂ : cReach E d b c) :
    cReach E d a c :=
  Relation.ReflTransGen.trans h₁ h₂

theorem cReach.step {d a b : X} (ha : a ∈ farClass E d) (hb : b ∈ farClass E d)
    (hab : a * b = b * a) : cReach E d a b :=
  Relation.ReflTransGen.single ⟨ha, hb, hab⟩

abbrev localGroupD (E : Set X) (d : X) : Subgroup X :=
  Subgroup.closure (insert d (LocalClass E d))

theorem commute_of_mem_localGroupD {d h : X} (hh : h ∈ localGroupD E d) : h * d = d * h := by
  have : localGroupD E d ≤ Subgroup.centralizer ({d} : Set X) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 hy.2.2
  exact Subgroup.mem_centralizer_singleton_iff.1 (this hh)

theorem Pair.conj_mem_farClass (hP : Pair X E) {d h c : X} (hh : h * d = d * h)
    (hc : c ∈ farClass E d) : h * c * h⁻¹ ∈ farClass E d := by
  refine ⟨Pair.conj_mem hP hc.1 h, fun e => hc.2 ?_⟩
  have hd : h * d * h⁻¹ = d := by rw [hh, mul_inv_cancel_right]
  rw [← hd, conj_commute_iff] at e
  exact e

theorem Pair.cReach_conj (hP : Pair X E) (g : X) {d a b : X} (h : cReach E d a b) :
    cReach E (g * d * g⁻¹) (g * a * g⁻¹) (g * b * g⁻¹) := by
  have hmem : ∀ c, c ∈ farClass E d → g * c * g⁻¹ ∈ farClass E (g * d * g⁻¹) := by
    intro c hc
    refine ⟨Pair.conj_mem hP hc.1 g, ?_⟩
    rw [Ne, conj_commute_iff]
    exact hc.2
  refine Relation.ReflTransGen.lift (fun y => g * y * g⁻¹) (fun u v huv => ?_) _ _ h
  exact ⟨hmem u huv.1, hmem v huv.2.1, (conj_commute_iff g u v).2 huv.2.2⟩

theorem Pair.exists_conj_of_commute_far (hP : Pair X E) {d a b : X} (hd : d ∈ E)
    (ha : a ∈ farClass E d) (hb : b ∈ farClass E d) (hab : a * b = b * a) :
    ∃ h ∈ localGroupD E d, h * a * h⁻¹ = b := by
  by_cases hne : a = b
  · exact ⟨1, one_mem _, by rw [hne]; group⟩
  have haE := ha.1
  have hbE := hb.1
  have hdbar : a * b * d * (a * b)⁻¹ ∈ LocalClass E d :=
    Pair.triality_adj hP haE hbE hd hab hne (fun e => ha.2 e.symm) fun e => hb.2 e.symm
  refine ⟨a * b * d * (a * b)⁻¹ * d, mul_mem (Subgroup.subset_closure (Or.inr hdbar))
    (Subgroup.subset_closure (Or.inl rfl)), ?_⟩
  have htt : a * b * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * a * (b * b) := by rw [← hab]; simp only [mul_assoc]
      _ = 1 := by rw [Pair.mul_self hP haE, Pair.mul_self hP hbE, one_mul]
  have hti : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right htt
  rw [hti] at hdbar ⊢
  have hdbE := hdbar.1
  have htb : a * b * b = a := by rw [mul_assoc, Pair.mul_self hP hbE, mul_one]
  have hbt : b * (a * b) = a := by rw [← mul_assoc, ← hab, htb]
  have htbt : a * b * b * (a * b) = b := by
    rw [htb, ← mul_assoc, Pair.mul_self hP haE, one_mul]
  have hbd : b * d * b = d * b * d := Pair.mul_mul_eq hP hbE hd fun e => hb.2 e
  have had : a * d * a = d * a * d := Pair.mul_mul_eq hP haE hd fun e => ha.2 e
  have key : a * b * d * (a * b) * b * (a * b * d * (a * b)) = d * a * d := by
    calc a * b * d * (a * b) * b * (a * b * d * (a * b))
        = a * b * d * (a * b * b * (a * b)) * d * (a * b) := by simp only [mul_assoc]
      _ = a * b * (d * b * d) * (a * b) := by rw [htbt]; simp only [mul_assoc]
      _ = a * b * b * d * (b * (a * b)) := by rw [← hbd]; simp only [mul_assoc]
      _ = d * a * d := by rw [htb, hbt, had]
  rw [mul_inv_rev, Pair.inv_eq hP hd, Pair.inv_eq hP hdbE]
  have h2 := Pair.mul_self hP hdbE
  calc a * b * d * (a * b) * d * a * (d * (a * b * d * (a * b)))
      = a * b * d * (a * b) * (d * a * d) * (a * b * d * (a * b)) := by simp only [mul_assoc]
    _ = a * b * d * (a * b) * (a * b * d * (a * b)) * b *
          (a * b * d * (a * b) * (a * b * d * (a * b))) := by rw [← key]; simp only [mul_assoc]
    _ = b := by rw [h2, one_mul, mul_one]

theorem Pair.ncard_localClass_eq (hP : Pair X E) {x y : X} (hx : x ∈ E) (hy : y ∈ E) :
    (LocalClass E x).ncard = (LocalClass E y).ncard := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hx hy)
  rw [← Pair.image_conj_localClass hP g x, Set.ncard_image_of_injective _ (conj_injective g)]

theorem not_forall_commute {G : Type} [Group G] (h : ∃ a b : commutator G, a * b ≠ b * a) :
    ¬ ∀ a b : commutator G, a * b = b * a := fun h' =>
  let ⟨a, b, hab⟩ := h
  hab (h' a b)

theorem Pair.eq_of_localClass_subset (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a) {x y : X}
    (hx : x ∈ E) (hy : y ∈ E) (h : LocalClass E x ⊆ LocalClass E y) : x = y := by
  have := Pair.finite hP
  exact Pair.eq_of_localClass_eq hP hZ hS (not_forall_commute hna) hx hy
    (Set.eq_of_subset_of_ncard_le h (Pair.ncard_localClass_eq hP hy hx).le (Set.toFinite _))

theorem Pair.cReach_mul_mul (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a) {d c : X}
    (hd : d ∈ E) (hc : c ∈ farClass E d) (hμ : (muSet E d c).Nonempty) :
    cReach E d c (d * c * d) := by
  have hcE := hc.1
  have hcd := hc.2
  obtain ⟨f, hfD, hfμ, s, hsμ, hfs⟩ : ∃ f ∈ LocalClass E d, f ∉ muSet E d c ∧
      ∃ s ∈ muSet E d c, f * s * f ∉ muSet E d c := by
    by_contra! hall
    have hnorm : ∀ f ∈ LocalClass E d, ∀ s ∈ muSet E d c, f * s * f ∈ muSet E d c := by
      intro f hf s hs
      by_cases hfμ : f ∈ muSet E d c
      · exact Pair.mul_mul_mem_muSet hP hfμ hs
      · exact hall f hf hfμ s hs
    have hle : LocalGroup E d ≤ Subgroup.normalizer (muSet E d c) := by
      rw [LocalGroup, Subgroup.closure_le]
      intro f hf t
      rw [Pair.inv_eq hP hf.1]
      refine ⟨hnorm f hf t, fun h => ?_⟩
      have := hnorm f hf _ h
      rwa [Pair.mul_mul_mul_mul hP hf.1] at this
    obtain ⟨s₀, hs₀⟩ := hμ
    have hsub : LocalClass E d ⊆ LocalClass E c := by
      intro f hf
      obtain ⟨k, hk, rfl⟩ := Pair.exists_localGroup_conj hP hZ hS hd hs₀.1 hf
      exact ((hle hk s₀).1 hs₀).2
    exact hcd (by rw [Pair.eq_of_localClass_subset hP hZ hS hna hd hcE hsub])
  have hfE := hfD.1
  have ha : d * c * f * c * d ∈ LocalClass E c := Pair.nu_mem_localClass hP hd hcE hcd hfD
  have had : d * c * f * c * d * d ≠ d * (d * c * f * c * d) :=
    Pair.nu_not_commute hP hd hcE hcd hfD hfμ
  have hgD : f * s * f ∈ LocalClass E d := by
    refine ⟨Pair.mul_mul_mem hP hfE hsμ.1.1, fun e => hsμ.1.2.1 ?_,
      (commute_mul_mul_of_commute hfD.2.2.symm hsμ.1.2.2.symm).symm⟩
    rw [← Pair.mul_mul_mul_mul hP hfE s, e, hfD.2.2, mul_assoc, Pair.mul_self hP hfE, mul_one]
  have hgμ : f * s * f ∈ muSet E d (d * c * f * c * d) := by
    rw [Pair.muSet_nu hP hd hcE hcd hfD hfμ]
    exact ⟨s, hsμ, rfl⟩
  have hc'E : d * c * d ∈ E := Pair.mul_mul_mem hP hd hcE
  have hc'd : d * c * d * d ≠ d * (d * c * d) :=
    Pair.mul_mul_not_commute_left hP hd fun e => hcd e.symm
  have hμeq := Pair.muSet_eq_muSet_mul_mul hP hd hcE hcd
  have hb : d * (d * c * d) * (f * s * f) * (d * c * d) * d ∈ LocalClass E (d * c * d) :=
    Pair.nu_mem_localClass hP hd hc'E hc'd hgD
  have hbd := Pair.nu_not_commute hP hd hc'E hc'd hgD (by rwa [← hμeq])
  have hbeq : d * (d * c * d) * (f * s * f) * (d * c * d) * d = c * (f * s * f) * c := by
    have hdg : d * (f * s * f) * d = f * s * f := by
      rw [← hgD.2.2, mul_assoc, Pair.mul_self hP hd, mul_one]
    calc d * (d * c * d) * (f * s * f) * (d * c * d) * d
        = d * d * c * (d * (f * s * f) * d) * c * (d * d) := by simp only [mul_assoc]
      _ = c * (f * s * f) * c := by rw [hdg, Pair.mul_self hP hd, one_mul, mul_one]
  rw [hbeq] at hb hbd
  have hab : d * c * f * c * d * (c * (f * s * f) * c) =
      c * (f * s * f) * c * (d * c * f * c * d) := by
    have h1 : d * c * f * c * d * c = c * (d * c * f * c * d) := ha.2.2
    have h2 : f * s * f * (d * c * f * c * d) = d * c * f * c * d * (f * s * f) := hgμ.2.2.2
    calc d * c * f * c * d * (c * (f * s * f) * c)
        = (d * c * f * c * d * c) * (f * s * f) * c := by simp only [mul_assoc]
      _ = c * ((d * c * f * c * d) * (f * s * f)) * c := by rw [h1]; simp only [mul_assoc]
      _ = c * ((f * s * f) * (d * c * f * c * d)) * c := by rw [← h2]
      _ = c * (f * s * f) * (d * c * f * c * d * c) := by simp only [mul_assoc]
      _ = c * (f * s * f) * c * (d * c * f * c * d) := by rw [h1]; simp only [mul_assoc]
  have hA : d * c * f * c * d ∈ farClass E d := ⟨ha.1, had⟩
  have hB : c * (f * s * f) * c ∈ farClass E d := ⟨hb.1, hbd⟩
  have hC : d * c * d ∈ farClass E d := ⟨hc'E, hc'd⟩
  exact ((cReach.step hc hA ha.2.2.symm).trans (cReach.step hA hB hab)).trans
    (cReach.step hB hC hb.2.2)

theorem Pair.cReach_conj_gen (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    (hconn : (commGraph E).Connected) {d s c : X} (hd : d ∈ E)
    (hs : s ∈ insert d (LocalClass E d)) (hc : c ∈ farClass E d) :
    cReach E d c (s * c * s⁻¹) := by
  have hμ : ∀ c ∈ farClass E d, (muSet E d c).Nonempty := fun c hc =>
    Pair.muSet_nonempty hP hconn hd hc.1 hc.2
  rcases hs with rfl | hf
  · rw [Pair.inv_eq hP hd]
    exact Pair.cReach_mul_mul hP hZ hS hna hd hc (hμ c hc)
  · have hfE := hf.1
    rw [Pair.inv_eq hP hfE]
    by_cases hcf : c * s = s * c
    · rw [← hcf, mul_assoc, Pair.mul_self hP hfE, mul_one]
      exact Relation.ReflTransGen.refl
    · have hy : d * s * c * (d * s)⁻¹ ∈ LocalClass E c :=
        Pair.triality_adj hP hd hfE hc.1 hf.2.2.symm (fun e => hf.2.1 e.symm) hc.2 hcf
      have hyA : d * s * c * (d * s)⁻¹ ∈ farClass E d :=
        Pair.conj_mem_farClass hP (by rw [mul_assoc, hf.2.2]) hc
      have hfcf : s * c * s ∈ farClass E d := by
        have := Pair.conj_mem_farClass hP hf.2.2 hc
        rwa [Pair.inv_eq hP hfE] at this
      have hyeq : d * (s * c * s) * d = d * s * c * (d * s)⁻¹ := by
        rw [mul_inv_rev, Pair.inv_eq hP hd, Pair.inv_eq hP hfE]
        simp only [mul_assoc]
      have h1 := Pair.cReach_mul_mul hP hZ hS hna hd hfcf (hμ _ hfcf)
      rw [hyeq] at h1
      exact (cReach.step hc hyA hy.2.2.symm).trans h1.symm

theorem Pair.cReach_conj_of_mem (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    (hconn : (commGraph E).Connected) {d h : X} (hd : d ∈ E) (hh : h ∈ localGroupD E d) :
    ∀ c ∈ farClass E d, cReach E d c (h * c * h⁻¹) := by
  induction hh using Subgroup.closure_induction with
  | mem s hs => exact fun c hc => Pair.cReach_conj_gen hP hZ hS hna hconn hd hs hc
  | one =>
    intro c _
    rw [one_mul, inv_one, mul_one]
    exact Relation.ReflTransGen.refl
  | mul x y hx hy ihx ihy =>
    intro c hc
    have hyc : y * c * y⁻¹ ∈ farClass E d :=
      Pair.conj_mem_farClass hP (commute_of_mem_localGroupD hy) hc
    have h2 := ihx _ hyc
    rw [show x * (y * c * y⁻¹) * x⁻¹ = x * y * c * (x * y)⁻¹ by group] at h2
    exact (ihy c hc).trans h2
  | inv x hx ihx =>
    intro c hc
    have hxc : x⁻¹ * c * x⁻¹⁻¹ ∈ farClass E d :=
      Pair.conj_mem_farClass hP (commute_of_mem_localGroupD (inv_mem hx)) hc
    have h2 := ihx _ hxc
    rw [show x * (x⁻¹ * c * x⁻¹⁻¹) * x⁻¹ = c by group] at h2
    exact h2.symm

theorem Pair.exists_conj_of_cReach (hP : Pair X E) {d a b : X} (hd : d ∈ E)
    (h : cReach E d a b) : ∃ k ∈ localGroupD E d, k * a * k⁻¹ = b := by
  induction h with
  | refl => exact ⟨1, one_mem _, by group⟩
  | @tail b c _ hbc ih =>
    obtain ⟨k, hk, rfl⟩ := ih
    obtain ⟨k', hk', hk'c⟩ := Pair.exists_conj_of_commute_far hP hd hbc.1 hbc.2.1 hbc.2.2
    exact ⟨k' * k, mul_mem hk' hk, by rw [← hk'c]; group⟩

theorem Pair.conj_mem_farClass_iff (hP : Pair X E) (g : X) {d c : X} :
    g * c * g⁻¹ ∈ farClass E (g * d * g⁻¹) ↔ c ∈ farClass E d := by
  simp only [mem_farClass, Pair.conj_mem_iff hP, Ne, conj_commute_iff]

theorem cReach_of_subset {d z w v : X} (h : cReach E d w v)
    (hsub : ∀ u, cReach E d w u → u ∈ farClass E z) : cReach E z w v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hb hbc ih =>
    exact ih.trans (cReach.step (hsub b hb) (hsub c (hb.tail hbc)) hbc.2.2)

theorem Pair.closure_insert_far_eq_top (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    (hconn : (commGraph E).Connected) {d z : X} (hd : d ∈ E) (hz : z ∈ farClass E d) :
    Subgroup.closure (insert z (insert d (LocalClass E d))) = ⊤ := by
  set U := Subgroup.closure (insert z (insert d (LocalClass E d))) with hU
  have hzU : z ∈ U := Subgroup.subset_closure (Or.inl rfl)
  have hdU : d ∈ U := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hLU : LocalGroup E d ≤ U :=
    Subgroup.closure_mono fun f hf => Or.inr (Or.inr hf)
  set P : Set X := {e | ∃ u ∈ U, u * d * u⁻¹ = e} with hPdef
  have hzP : z ∈ P :=
    ⟨d * z, mul_mem hdU hzU, Pair.mul_conj_left_eq hP hd hz.1 fun e => hz.2 e.symm⟩
  obtain ⟨f, hfD, hfz⟩ : ∃ f ∈ LocalClass E d, f * z ≠ z * f := by
    by_contra! hall
    have hsub : LocalClass E d ⊆ LocalClass E z := fun f hf =>
      ⟨hf.1, fun e => hz.2 (by rw [← e]; exact hf.2.2), hall f hf⟩
    exact hz.2 (by rw [Pair.eq_of_localClass_subset hP hZ hS hna hd hz.1 hsub])
  have hfP : f ∈ P := by
    obtain ⟨u, hu, hud⟩ := hzP
    refine ⟨z * f * u, mul_mem (mul_mem hzU (hLU (mem_localGroup hfD))) hu, ?_⟩
    rw [show z * f * u * d * (z * f * u)⁻¹ = z * f * (u * d * u⁻¹) * (z * f)⁻¹ by group, hud]
    exact Pair.mul_conj_left_eq hP hz.1 hfD.1 fun e => hfz e.symm
  have hDP : LocalClass E d ⊆ P := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := Pair.exists_localGroup_conj hP hZ hS hd hfD hg
    obtain ⟨u, hu, rfl⟩ := hfP
    exact ⟨k * u, mul_mem (hLU hk) hu, by group⟩
  have hPc : ∀ e ∈ P, ∀ e' ∈ E, e * e' = e' * e → e' ∈ P := by
    rintro e ⟨u, hu, rfl⟩ e' he' hc
    by_cases h : e' = u * d * u⁻¹
    · exact ⟨u, hu, h.symm⟩
    · have hmem : u⁻¹ * e' * u ∈ LocalClass E d := by
        rw [← Pair.conj_mem_localClass_iff hP u, show u * (u⁻¹ * e' * u) * u⁻¹ = e' by group]
        exact ⟨he', h, hc.symm⟩
      obtain ⟨v, hv, hvd⟩ := hDP hmem
      refine ⟨u * v, mul_mem hu hv, ?_⟩
      rw [show u * v * d * (u * v)⁻¹ = u * (v * d * v⁻¹) * u⁻¹ by group, hvd]
      group
  have hEP : ∀ e ∈ E, e ∈ P := fun e he =>
    reachable_induction (G := commGraph E) (p := fun a : E => (a : X) ∈ P)
      (fun a b hab ha => hPc a ha b b.2 hab.2) (hconn ⟨d, hd⟩ ⟨e, he⟩) ⟨1, one_mem _, by group⟩
  rw [eq_top_iff, ← Pair.closure_eq hP, Subgroup.closure_le]
  intro e he
  obtain ⟨u, hu, rfl⟩ := hEP e he
  exact mul_mem (mul_mem hu hdU) (inv_mem hu)

theorem Pair.connected_of_nonabelian (hP : Pair X E) (hS : IsSimpleGroup (commutator X))
    (hna : ∃ a b : commutator X, a * b ≠ b * a) : (commGraph E).Connected := by
  obtain ⟨a, ha, b, hb, hab, habc⟩ := Pair.exists_ne_commute hP hS (not_forall_commute hna)
  exact Pair.connected_of_simple hP hS ⟨a, b, ha, hb, hab, habc⟩

theorem Pair.exists_conj_far (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    {d x : X} (hd : d ∈ E) (hx : x ∈ E) (hxd : x * d ≠ d * x) :
    ∀ c ∈ E, c * d ≠ d * c →
      ∃ g ∈ Subgroup.closure (insert d (LocalClass E d)), g * x * g⁻¹ = c := by
  intro c hc hcd
  have hconn := Pair.connected_of_nonabelian hP hS hna
  suffices h : cReach E d x c from Pair.exists_conj_of_cReach hP hd h
  by_contra hxc
  have hfin := Pair.finite hP
  obtain ⟨y₁, hy₁, hmax⟩ := Set.exists_max_image (farClass E d)
    (fun y => {v | cReach E d y v}.ncard) (Set.toFinite _) ⟨x, hx, hxd⟩
  set A₁ : Set X := {v | cReach E d y₁ v} with hA₁def
  have hA₁ : A₁ ⊆ farClass E d := fun v hv => cReach.mem hv hy₁
  have hy₁A : y₁ ∈ A₁ := Relation.ReflTransGen.refl
  obtain ⟨z, hz, hzA⟩ : ∃ z ∈ farClass E d, z ∉ A₁ := by
    by_contra! hall
    exact hxc ((hall x ⟨hx, hxd⟩ : cReach E d y₁ x).symm.trans (hall c ⟨hc, hcd⟩))
  have hA₁z : A₁ ⊆ farClass E z := fun a ha =>
    ⟨(hA₁ ha).1, fun e => hzA ((ha : cReach E d y₁ a).trans (cReach.step (hA₁ ha) hz e))⟩
  have hbound : ∀ w ∈ farClass E z, {v | cReach E z w v}.ncard ≤ A₁.ncard := by
    intro w hw
    obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd hz.1)
    have hw' : g⁻¹ * w * g ∈ farClass E d := by
      rw [← Pair.conj_mem_farClass_iff hP g, show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
      exact hw
    have hsub : {v | cReach E (g * d * g⁻¹) w v} ⊆
        (fun y => g * y * g⁻¹) '' {v | cReach E d (g⁻¹ * w * g) v} := by
      intro v hv
      refine ⟨g⁻¹ * v * g, ?_, by group⟩
      have := Pair.cReach_conj hP g⁻¹ hv
      rwa [show g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d by group, inv_inv] at this
    calc {v | cReach E (g * d * g⁻¹) w v}.ncard
        ≤ ((fun y => g * y * g⁻¹) '' {v | cReach E d (g⁻¹ * w * g) v}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ {v | cReach E d (g⁻¹ * w * g) v}.ncard := Set.ncard_image_le (Set.toFinite _)
      _ ≤ A₁.ncard := hmax _ hw'
  have hcompz : {v | cReach E z y₁ v} = A₁ := by
    have h1 : A₁ ⊆ {v | cReach E z y₁ v} := fun v hv =>
      cReach_of_subset hv fun u hu => hA₁z hu
    exact (Set.eq_of_subset_of_ncard_le h1 (hbound y₁ (hA₁z hy₁A)) (Set.toFinite _)).symm
  have hinv : ∀ s ∈ insert z (insert d (LocalClass E d)), ∀ a ∈ A₁, s * a * s⁻¹ ∈ A₁ := by
    rintro s (rfl | hs) a ha
    · have h1 := Pair.cReach_conj_gen hP hZ hS hna hconn hz.1
        (Set.mem_insert s (LocalClass E s)) (hA₁z ha)
      rw [← hcompz] at ha ⊢
      exact ha.trans h1
    · exact (ha : cReach E d y₁ a).trans (Pair.cReach_conj_gen hP hZ hS hna hconn hd hs (hA₁ ha))
  have htop : Subgroup.normalizer A₁ = ⊤ := by
    rw [eq_top_iff, ← Pair.closure_insert_far_eq_top hP hZ hS hna hconn hd hz,
      Subgroup.closure_le]
    intro s hs a
    have hsE : s ∈ E := by
      rcases hs with rfl | rfl | hs
      · exact hz.1
      · exact hd
      · exact hs.1
    refine ⟨hinv s hs a, fun h => ?_⟩
    have := hinv s hs _ h
    rwa [Pair.inv_eq hP hsE, Pair.mul_mul_mul_mul hP hsE] at this
  obtain ⟨k, hk⟩ := isConj_iff.1 (Pair.isConj hP (hA₁ hy₁A).1 hd)
  have hkN : k ∈ Subgroup.normalizer A₁ := htop ▸ Subgroup.mem_top k
  have hdA : d ∈ A₁ := by
    rw [← hk]
    exact (hkN y₁).1 hy₁A
  exact (hA₁ hdA).2 rfl

theorem Pair.exists_conj_pair_of_commute (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {a b c e : X} (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E)
    (he : e ∈ E) (hab : a ≠ b) (habc : a * b = b * a) (hce : c ≠ e) (hcec : c * e = e * c) :
    ∃ g : X, g * a * g⁻¹ = c ∧ g * b * g⁻¹ = e := by
  obtain ⟨g₀, rfl⟩ := isConj_iff.1 (Pair.isConj hP ha hc)
  have hb' : g₀ * b * g₀⁻¹ ∈ LocalClass E (g₀ * a * g₀⁻¹) :=
    (Pair.conj_mem_localClass_iff hP g₀).2 ⟨hb, hab.symm, habc.symm⟩
  obtain ⟨h, hh, hhe⟩ := Pair.exists_localGroup_conj hP hZ hS hc hb' ⟨he, hce.symm, hcec.symm⟩
  have hcomm := commute_of_mem_localGroup (fun g hg => hg.2.2) hh
  refine ⟨h * g₀, ?_, by rw [← hhe]; group⟩
  rw [show h * g₀ * a * (h * g₀)⁻¹ = h * (g₀ * a * g₀⁻¹) * h⁻¹ by group, hcomm,
    mul_inv_cancel_right]

theorem Pair.exists_conj_pair_of_not_commute (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    {a b c e : X} (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E) (he : e ∈ E) (hab : a * b ≠ b * a)
    (hce : c * e ≠ e * c) : ∃ g : X, g * a * g⁻¹ = c ∧ g * b * g⁻¹ = e := by
  obtain ⟨g₀, rfl⟩ := isConj_iff.1 (Pair.isConj hP ha hc)
  have hb'c : g₀ * b * g₀⁻¹ * (g₀ * a * g₀⁻¹) ≠ g₀ * a * g₀⁻¹ * (g₀ * b * g₀⁻¹) := by
    rw [Ne, conj_commute_iff]
    exact fun h => hab h.symm
  obtain ⟨h, hh, hhe⟩ := Pair.exists_conj_far hP hZ hS hna hc (Pair.conj_mem hP hb g₀) hb'c e he
    fun h => hce h.symm
  have hcomm := commute_of_mem_localGroupD hh
  refine ⟨h * g₀, ?_, by rw [← hhe]; group⟩
  rw [show h * g₀ * a * (h * g₀)⁻¹ = h * (g₀ * a * g₀⁻¹) * h⁻¹ by group, hcomm,
    mul_inv_cancel_right]

theorem Pair.exists_centralizer_conj_localClass (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {d f g : X} (hd : d ∈ E) (hf : f ∈ LocalClass E d)
    (hg : g ∈ LocalClass E d) : ∃ h ∈ Subgroup.centralizer ({d} : Set X), h * f * h⁻¹ = g := by
  obtain ⟨h, hh, hhg⟩ := Pair.exists_localGroup_conj hP hZ hS hd hf hg
  exact ⟨h, Subgroup.mem_centralizer_singleton_iff.2
    (commute_of_mem_localGroup (fun g hg => hg.2.2) hh), hhg⟩

theorem Pair.exists_centralizer_conj_far (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    {d x c : X} (hd : d ∈ E) (hx : x ∈ E) (hxd : x * d ≠ d * x) (hc : c ∈ E)
    (hcd : c * d ≠ d * c) : ∃ h ∈ Subgroup.centralizer ({d} : Set X), h * x * h⁻¹ = c := by
  obtain ⟨h, hh, hhc⟩ := Pair.exists_conj_far hP hZ hS hna hd hx hxd c hc hcd
  exact ⟨h, Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem_localGroupD hh), hhc⟩

end CFSG.Fischer.Classification
