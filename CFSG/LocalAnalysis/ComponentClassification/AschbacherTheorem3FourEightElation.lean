module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightCoset

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers

variable {X : Type} [Group X] [Finite X]
variable {G T S Q H : Subgroup X} {g y : X}

namespace ElemCtx

theorem conj_eq_mul_comm (c : ElemCtx G T S Q H g y) {w : X} (hwS : w ∈ S) (hwG : w ∈ G)
    (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) {s : X}
    (hs : s ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G) :
    s⁻¹ * w * s = w * (s⁻¹ * (w⁻¹ * s * w)) := by
  have hc := comm_mem_Z_of_mem_G c.elem hwS hwG hwW hs.1 hs.2
  have hc2 : (s⁻¹ * (w⁻¹ * s * w))⁻¹ = s⁻¹ * (w⁻¹ * s * w) :=
    Elem47.inv_eq_of_sq (sq_Z c.elem hc)
  calc s⁻¹ * w * s = w * (s⁻¹ * (w⁻¹ * s * w))⁻¹ := by group
    _ = w * (s⁻¹ * (w⁻¹ * s * w)) := by rw [hc2]

theorem A_comm' (c : ElemCtx G T S Q H g y) :
    ∀ a ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X),
      ∀ b ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X), a * b = b * a :=
  fun _ ha _ hb => M_comm' c.elem ha.1.1 hb.1.1

theorem isSylowOf_normalizer (c : ElemCtx G T S Q H g y) {E : Subgroup X}
    (hE : S ⊓ G ≤ Subgroup.normalizer (E : Set X)) :
    IsSylowOf 2 (S ⊓ G) (G ⊓ Subgroup.normalizer (E : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact c.isSylowOf_P.of_le (le_inf inf_le_right hE) inf_le_left

theorem false_of_elation (c : ElemCtx G T S Q H g y) {w : X} (hwS : w ∈ S) (hwG : w ∈ G)
    (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hw2 : w ^ 2 = 1)
    (hwA : ∀ a ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X), a * w = w * a)
    (hq : 8 ≤ Nat.card T ∨ ∀ z ∈ (T ⊔ rightConjugate T g) ⊓ G, z * w = w * z) {y' : X}
    (hy : y' ∈ G)
    (hyE : y' ∈ Subgroup.normalizer
      (cosetSub ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) w hw2 hwA :
        Set X))
    (hyw : y'⁻¹ * w * y' ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) :
    False := by
  have e := c.elem
  set A := (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) with hAdef
  set E := cosetSub A w hw2 hwA with hEdef
  have hww : w * w = 1 := by rw [← pow_two, hw2]
  have hE := c.le_normalizer_cosetSub hwS hwG hwW hw2 hwA
  have hEab := cosetSub_comm hw2 hwA c.A_comm'
  have hS₀ := c.isSylowOf_normalizer hE
  have hS₀A : ∀ s ∈ S ⊓ G, ∀ a ∈ A, s * a = a * s := fun s hs a ha => (A_comm ha hs.1).symm
  have hcoset : ∀ x ∈ E, x ∉ A → w⁻¹ * x ∈ A := fun x hx hxA => hx.resolve_left hxA
  have hAE : A ≤ E := le_cosetSub hw2 hwA
  have hAy : rightConjugate A y' ≠ A := by
    intro heq
    have h1 : y'⁻¹ * w * y' ∈ rightConjugate A y' := by rw [heq]; exact hyw
    rw [mem_rightConjugate_iff] at h1
    have h2 : y' * (y'⁻¹ * w * y') * y'⁻¹ = w := by group
    rw [h2] at h1
    exact hwW (Subgroup.mem_sup_right h1.1.1)
  have hnot : ∀ s ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G,
      s⁻¹ * (w⁻¹ * s * w) ≠ 1 → s⁻¹ * (w⁻¹ * s * w) ∉ rightConjugate A y' := by
    intro s hs hc1 hcy
    rcases eq_of_elation inf_le_right hEab hAE hcoset hS₀ hS₀A ⟨hy, hyE⟩
        (c.comm_mem_A hwS hwG hwW hw2 hs) hcy ⟨e.A_le_S hs.1, hs.2⟩
        (c.conj_eq_mul_comm hwS hwG hwW hs) with h | h
    · exact hAy h
    · exact hc1 h
  obtain ⟨s₁, hs₁, s₂, hs₂, h1, h2, h12⟩ := c.exists_comm_ne hwS hwG hwW hw2 hq
  have hc₁ := c.comm_mem_A hwS hwG hwW hw2 hs₁
  have hc₂ := c.comm_mem_A hwS hwG hwW hw2 hs₂
  have hmul := comm_mul e hwS hwG hwW hs₁ hs₂
  have h12' : (s₁ * s₂)⁻¹ * (w⁻¹ * (s₁ * s₂) * w) ≠ 1 := by
    rw [hmul]
    intro h
    apply h12
    rw [eq_inv_of_mul_eq_one_left h, Elem47.inv_eq_of_sq (sq_Z e hc₂.1)]
  apply hnot _ (Subgroup.mul_mem _ hs₁ hs₂) h12'
  rw [hmul, mem_rightConjugate_iff]
  have hout : ∀ x ∈ A, x ∉ rightConjugate A y' → w⁻¹ * (y' * x * y'⁻¹) ∈ A := by
    intro x hx hxy
    have hxE : y' * x * y'⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hyE x).mp (hAE hx)
    refine hxE.resolve_left ?_
    intro h
    exact hxy ((mem_rightConjugate_iff _ _ _).mpr h)
  have ha₁ := hout _ hc₁ (hnot s₁ hs₁ h1)
  have ha₂ := hout _ hc₂ (hnot s₂ hs₂ h2)
  set a₁ := w⁻¹ * (y' * (s₁⁻¹ * (w⁻¹ * s₁ * w)) * y'⁻¹) with ha₁def
  set a₂ := w⁻¹ * (y' * (s₂⁻¹ * (w⁻¹ * s₂ * w)) * y'⁻¹) with ha₂def
  have hconj : y' * ((s₁⁻¹ * (w⁻¹ * s₁ * w)) * (s₂⁻¹ * (w⁻¹ * s₂ * w))) * y'⁻¹ =
      (w * a₁) * (w * a₂) := by
    rw [ha₁def, ha₂def]
    group
  rw [hconj]
  have h3 : w * a₁ * (w * a₂) = w * (a₁ * w) * a₂ := by group
  rw [h3, hwA a₁ ha₁]
  have h4 : w * (w * a₁) * a₂ = (w * w) * (a₁ * a₂) := by group
  rw [h4, hww, one_mul]
  exact A.mul_mem ha₁ ha₂

theorem eq_of_card_le_two {A : Subgroup X} (hA : Nat.card A ≤ 2) {a b : X} (ha : a ∈ A)
    (hb : b ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have h3 : ({1, a, b} : Finset X).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, a, b, Ne.symm ha1, Ne.symm hb1, hab, rfl⟩
  have hsub : (↑({1, a, b} : Finset X) : Set X) ⊆ A := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact A.one_mem
    · exact ha
    · exact hb
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, h3, ← Nat.card_coe_set_eq] at h1
  have h2 : Nat.card (A : Set X) = Nat.card A := rfl
  omega

theorem false_of_squares (c : ElemCtx G T S Q H g y) {w : X} (hwS : w ∈ S) (hwG : w ∈ G)
    (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hw2 : w ^ 2 = 1)
    (hwA : ∀ a ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X), a * w = w * a)
    (hT : Nat.card T = 4) {z₁ : X} (hz₁ : z₁ ∈ (T ⊔ rightConjugate T g) ⊓ G)
    (hz₁w : z₁ * w ≠ w * z₁)
    (hk : Nat.card ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) ≤
      2 * Nat.card ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) :
        Subgroup X))
    {y' : X} (hy : y' ∈ G)
    (hyE : y' ∈ Subgroup.normalizer
      (cosetSub ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) w hw2 hwA :
        Set X))
    (hyw : y'⁻¹ * w * y' ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  set A := (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) with hAdef
  set E := cosetSub A w hw2 hwA with hEdef
  set Z := (T ⊔ rightConjugate T g) ⊓ G with hZdef
  set R := (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G with hRdef
  have hww : w * w = 1 := by rw [← pow_two, hw2]
  have hZ4 : Nat.card Z = 4 := by rw [e.card_Z, hT]
  have hz₁A : z₁ ∉ A := fun h => hz₁w (A_comm h hwS)
  have hA2 : Nat.card A ≤ 2 := by
    have hAZ : A ≤ Z := inf_le_left
    have hlt : Nat.card A < 4 := by
      by_contra hge
      have heq : A = Z := Subgroup.eq_of_le_of_card_ge hAZ (by omega)
      exact hz₁A (heq ▸ hz₁)
    have hdvd := Subgroup.card_dvd_of_le hAZ
    rw [hZ4] at hdvd
    have h3 : Nat.card A ≠ 3 := by
      intro h; rw [h] at hdvd; norm_num at hdvd
    omega
  have huniq := fun {a b : X} (ha : a ∈ A) (hb : b ∈ A) => eq_of_card_le_two hA2 ha hb
  set e' := y'⁻¹ * w * y' with he'def
  have he'1 : e' ≠ 1 := by
    intro h
    have : w = 1 := by
      calc w = y' * e' * y'⁻¹ := by rw [he'def]; group
        _ = 1 := by rw [h]; group
    exact hwW (this ▸ Subgroup.one_mem _)
  set K := G ⊓ Subgroup.centralizer (E : Set X) with hKdef
  have hKle : K ≤ G ⊓ Subgroup.normalizer (E : Set X) :=
    inf_le_inf_left G (Subgroup.centralizer_le_normalizer _)
  have hKN : G ⊓ Subgroup.normalizer (E : Set X) ≤ Subgroup.normalizer (K : Set X) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx.1, normalizer_le_normalizer_centralizer E hx.2⟩
  have hE := c.le_normalizer_cosetSub hwS hwG hwW hw2 hwA
  have hS₀ := c.isSylowOf_normalizer hE
  have hD : IsSylowOf 2 ((S ⊓ G) ⊓ K) K := hS₀.inf_of_le_normalizer hKle hKN
  set D := (S ⊓ G) ⊓ K with hDdef
  have hy'K : y' ∈ Subgroup.normalizer (K : Set X) := hKN ⟨hy, hyE⟩
  have hD' : IsSylowOf 2 (rightConjugate D y') K := by
    apply isSylowOf_of_card
    · intro x hx
      rw [mem_rightConjugate_iff] at hx
      exact (Subgroup.mem_normalizer_iff.mp hy'K x).mpr (hD.le hx)
    · rw [rightConjugate_card, CFSG.ABGLocalTools.IsSylowOf.card_eq hD]
  obtain ⟨k, hk, hkey⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hD hD'
  set m := k⁻¹ * y'⁻¹ with hmdef
  have hmD : m ∈ Subgroup.normalizer (D : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    have h1 := hkey (y'⁻¹ * d * y')
    rw [mem_rightConjugate_iff] at h1
    have h2 : y' * (y'⁻¹ * d * y') * y'⁻¹ = d := by group
    have h3 : k⁻¹ * (y'⁻¹ * d * y') * k = m * d * m⁻¹ := by rw [hmdef]; group
    rw [h2, h3] at h1
    exact h1
  have he'A : e' ∈ A := hyw
  have hmw : m * w * m⁻¹ = e' := by
    have hke : e' * k = k * e' :=
      Subgroup.mem_centralizer_iff.mp hk.2 e' (le_cosetSub hw2 hwA he'A)
    calc m * w * m⁻¹ = k⁻¹ * e' * k := by rw [hmdef, he'def]; group
      _ = e' := by rw [mul_assoc, hke]; group
  have hcomm_of : ∀ d : X, d⁻¹ * (w⁻¹ * d * w) = 1 → d * w = w * d := by
    intro d h
    have h1 : w⁻¹ * d * w = d := by
      calc w⁻¹ * d * w = d * (d⁻¹ * (w⁻¹ * d * w)) := by group
        _ = d := by rw [h, mul_one]
    calc d * w = w * (w⁻¹ * d * w) := by group
      _ = w * d := by rw [h1]
  have hsqR : ∀ d ∈ R, d * w = w * d → d ^ 2 ∈ A := by
    intro d hd hdw
    obtain ⟨z, hz, hzeq⟩ := sq_mul_comm_eq e hwS hwG hwW hw2 hd
    have h1 : d⁻¹ * (w⁻¹ * d * w) = 1 := by
      rw [mul_assoc w⁻¹, hdw, inv_mul_cancel_left, inv_mul_cancel]
    rw [h1, mul_one] at hzeq
    rw [hzeq]
    have hcz := c.comm_mem_A hwS hwG hwW hw2 (⟨Subgroup.mem_sup_right hz.1, hz.2⟩ : z ∈ R)
    rw [Elem47.inv_eq_of_sq (sq_Z e hz)] at hcz
    exact hcz
  have hsqD : ∀ d ∈ D, d ^ 2 ∈ A := by
    intro d hd
    have hdw : d * w = w * d :=
      (Subgroup.mem_centralizer_iff.mp hd.2.2 w (mem_cosetSub_self hw2 hwA)).symm
    by_cases hdW : d ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)
    · exact hsqR d ⟨hdW, hd.1.2⟩ hdw
    · obtain ⟨x, hxdef⟩ : ∃ x, x = d * w⁻¹ := ⟨_, rfl⟩
      have hxR : x ∈ R := by
        rw [hxdef]
        exact ⟨mul_inv_mem_W e hwS hd.1.1 hwW hdW, G.mul_mem hd.1.2 (G.inv_mem hwG)⟩
      have hdx : d = x * w := by rw [hxdef]; group
      have hxw : x * w = w * x := by
        rw [hxdef]
        calc d * w⁻¹ * w = (d * w) * w⁻¹ := by group
          _ = (w * d) * w⁻¹ := by rw [hdw]
          _ = w * (d * w⁻¹) := by group
      have h2 : d ^ 2 = x ^ 2 := by
        rw [hdx]
        calc (x * w) ^ 2 = x * (w * x) * w := by rw [pow_two]; group
          _ = x * (x * w) * w := by rw [hxw]
          _ = x ^ 2 * (w * w) := by rw [pow_two]; group
          _ = x ^ 2 := by rw [hww, mul_one]
      rw [h2]
      exact hsqR x hxR hxw
  have hRZ : ∃ r₀ ∈ R, r₀ ∉ Z := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hle : R ≤ Z := fun r hr => h r hr
    have := Subgroup.card_le_of_le hle
    rw [card_R e, hZ4, hT] at this
    omega
  obtain ⟨r₀, hr₀, hr₀Z⟩ := hRZ
  obtain ⟨r, hrR, hrZ, hrw⟩ : ∃ r ∈ R, r ∉ Z ∧ r * w = w * r := by
    by_cases hc₀ : r₀⁻¹ * (w⁻¹ * r₀ * w) = 1
    · exact ⟨r₀, hr₀, hr₀Z, hcomm_of r₀ hc₀⟩
    · have hz₁R : z₁ ∈ R := ⟨Subgroup.mem_sup_right hz₁.1, hz₁.2⟩
      have hcz₁ : z₁⁻¹ * (w⁻¹ * z₁ * w) ≠ 1 := fun h => hz₁w (hcomm_of z₁ h)
      have hc₁A := c.comm_mem_A hwS hwG hwW hw2 hz₁R
      have heq := huniq (c.comm_mem_A hwS hwG hwW hw2 hr₀) hc₁A hc₀ hcz₁
      refine ⟨r₀ * z₁, Subgroup.mul_mem _ hr₀ hz₁R, ?_, ?_⟩
      · intro h
        exact hr₀Z (by simpa using Subgroup.mul_mem _ h (Subgroup.inv_mem _ hz₁))
      · apply hcomm_of
        rw [comm_mul e hwS hwG hwW hr₀ hz₁R, heq, ← pow_two, sq_Z e hc₁A.1]
  have hrS : r ∈ S := e.A_le_S hrR.1
  have hrC : r ∈ Subgroup.centralizer (E : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hx with hx | hx
    · exact A_comm hx hrS
    · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, x = w * a := ⟨w⁻¹ * x, hx, by group⟩
      calc w * a * r = w * (a * r) := by group
        _ = w * (r * a) := by rw [A_comm ha hrS]
        _ = (w * r) * a := by group
        _ = (r * w) * a := by rw [hrw]
        _ = r * (w * a) := by group
  have hrD : r ∈ D := ⟨⟨hrS, hrR.2⟩, hrR.2, hrC⟩
  have hr2 : r ^ 2 = e' :=
    huniq (hsqD r hrD) he'A (fun h => hrZ (mem_Z_of_sq e hrR.1 hrR.2 h)) he'1
  have hm'D : m⁻¹ * r * m ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmD) r).mp hrD
    simpa using this
  have hw : (m⁻¹ * r * m) ^ 2 = w := by
    have h1 : (m⁻¹ * r * m) ^ 2 = m⁻¹ * r ^ 2 * m := by rw [pow_two, pow_two]; group
    rw [h1, hr2, ← hmw]
    group
  have hwA' := hsqD _ hm'D
  rw [hw] at hwA'
  exact hwW (Subgroup.mem_sup_right hwA'.1.1)

theorem false_of_normalizer (c : ElemCtx G T S Q H g y) {w : X} (hwS : w ∈ S) (hwG : w ∈ G)
    (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hw2 : w ^ 2 = 1)
    (hwA : ∀ a ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X), a * w = w * a)
    (hk : Nat.card ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) ≤
      2 * Nat.card ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) :
        Subgroup X))
    {y' : X} (hy : y' ∈ G)
    (hyE : y' ∈ Subgroup.normalizer
      (cosetSub ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) w hw2 hwA :
        Set X))
    (hyw : y'⁻¹ * w * y' ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) :
    False := by
  by_cases hq : 8 ≤ Nat.card T ∨ ∀ z ∈ (T ⊔ rightConjugate T g) ⊓ G, z * w = w * z
  · exact c.false_of_elation hwS hwG hwW hw2 hwA hq hy hyE hyw
  · simp only [not_or, not_le, not_forall] at hq
    obtain ⟨h8, z₁, hz₁, hz₁w⟩ := hq
    have hT : Nat.card T = 4 := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp c.frame.isPGroup
      have h4 := c.elem.four_le_card
      rw [hn] at h4 h8 ⊢
      rcases Nat.lt_or_ge n 3 with h | h
      · interval_cases n <;> simp_all
      · have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
        omega
    exact c.false_of_squares hwS hwG hwW hw2 hwA hT hz₁ hz₁w hk hy hyE hyw

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
