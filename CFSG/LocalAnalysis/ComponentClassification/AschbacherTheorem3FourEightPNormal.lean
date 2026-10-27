module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightNormal

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers

variable {X : Type} [Group X] [Finite X]
variable {G T S Q H : Subgroup X} {g y : X}

omit [Finite X] in
@[expose] def commSub (G N : Subgroup X) (e : X) (hN : G ≤ Subgroup.normalizer (N : Set X)) :
    Subgroup X where
  carrier := {x | x ∈ G ∧ x⁻¹ * (e⁻¹ * x * e) ∈ N}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨G.mul_mem ha hb, ?_⟩
    have h1 : b⁻¹ * (a⁻¹ * (e⁻¹ * a * e)) * b ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp (hN (G.inv_mem hb)) _).mp ha'
      simpa using this
    have heq : (a * b)⁻¹ * (e⁻¹ * (a * b) * e) =
        (b⁻¹ * (a⁻¹ * (e⁻¹ * a * e)) * b) * (b⁻¹ * (e⁻¹ * b * e)) := by group
    rw [heq]
    exact N.mul_mem h1 hb'
  one_mem' := ⟨G.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨G.inv_mem ha, ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hN ha) _).mp (N.inv_mem ha')
    have heq : a⁻¹⁻¹ * (e⁻¹ * a⁻¹ * e) = a * (a⁻¹ * (e⁻¹ * a * e))⁻¹ * a⁻¹ := by group
    rw [heq]
    exact h1

omit [Finite X] in
theorem mem_commSub {G N : Subgroup X} {e : X} {hN : G ≤ Subgroup.normalizer (N : Set X)}
    {x : X} : x ∈ commSub G N e hN ↔ x ∈ G ∧ x⁻¹ * (e⁻¹ * x * e) ∈ N := Iff.rfl

namespace ElemCtx

theorem comm_mem_Z_of_mem_S (c : ElemCtx G T S Q H g y) {r s : X}
    (hr : r ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G) (hs : s ∈ S) :
    r⁻¹ * (s⁻¹ * r * s) ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  have e := c.elem
  set W := rightConjugate T y ⊔ (T ⊔ rightConjugate T g) with hWdef
  set Z := (T ⊔ rightConjugate T g) ⊓ G with hZdef
  by_cases hsW : s ∈ W
  · exact comm_mem_Z_of_mem_W e hr.1 hsW
  ·
    obtain ⟨t, ht, p, hp, rfl⟩ := c.frame.mem_sup_iff.mp (c.sylowFrame.sylow.le hs)
    have hpS : p ∈ S := by simpa using S.mul_mem (S.inv_mem (c.sylowFrame.le ht)) hs
    have htW : t ∈ W := Subgroup.mem_sup_right (Subgroup.mem_sup_left ht)
    have hpW : p ∉ W := fun h => hsW (W.mul_mem htW h)
    have h1 : r⁻¹ * (t⁻¹ * r * t) ∈ Z := comm_mem_Z_of_mem_W e hr.1 htW
    set z₁ := r⁻¹ * (t⁻¹ * r * t) with hz₁
    have h2 : (t⁻¹ * r * t)⁻¹ * (p⁻¹ * (t⁻¹ * r * t) * p) ∈ Z := by
      have hrt : t⁻¹ * r * t ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G := by
        refine ⟨?_, ?_⟩
        · exact W.mul_mem (W.mul_mem (W.inv_mem htW) hr.1) htW
        · have := (Subgroup.mem_normalizer_iff.mp
            (c.frame.le_normalizer (T.inv_mem ht)) r).mp hr.2
          simpa using this
      exact comm_mem_Z_of_mem_G e hpS hp hpW hrt.1 hrt.2
    have heq : r⁻¹ * ((t * p)⁻¹ * r * (t * p)) =
        z₁ * ((t⁻¹ * r * t)⁻¹ * (p⁻¹ * (t⁻¹ * r * t) * p)) := by
      rw [hz₁]; group
    rw [heq]
    exact Z.mul_mem h1 h2

theorem le_normalizer_conj_Z (c : ElemCtx G T S Q H g y) {x : X}
    (hx : x ∈ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X)) {p : X} (hp : p ∈ S ⊓ G) :
    p ∈ Subgroup.normalizer
      (rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) x : Set X) := by
  have e := c.elem
  rw [← rightConjugate_eq_self_iff, rightConjugate_mul]
  have hxp : x * p * x⁻¹ ∈ S ⊓ G := (Subgroup.mem_normalizer_iff.mp hx p).mp hp
  have h1 : x * p = (x * p * x⁻¹) * x := by group
  rw [h1, ← rightConjugate_mul, (rightConjugate_eq_self_iff _ _).mpr
    (S_le_normalizer_Z e hxp.1)]

theorem le_normalizer_Z_of_centralizes (c : ElemCtx G T S Q H g y)
    (hP : G ≤ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X)) {t₀ : X} (ht₀ : t₀ ∈ T)
    (ht₀1 : t₀ ≠ 1) (hcent : ∀ x ∈ G, x⁻¹ * (t₀⁻¹ * x * t₀) ∈ S ⊓ G) :
    G ≤ Subgroup.normalizer (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) := by
  have e := c.elem
  set W := rightConjugate T y ⊔ (T ⊔ rightConjugate T g) with hWdef
  set Z := (T ⊔ rightConjugate T g) ⊓ G with hZdef
  intro x hx
  rw [← rightConjugate_eq_self_iff]
  by_contra hne
  set Zx := rightConjugate Z x with hZx
  have hZP : Z ≤ S ⊓ G := le_inf (inf_le_left.trans e.M_le_S) inf_le_right
  have hZxP : Zx ≤ S ⊓ G := by
    intro z hz
    rw [hZx, mem_rightConjugate_iff] at hz
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hP hx)) _).mp (hZP hz)
    simpa [mul_assoc] using h1
  have hZx2 : ∀ z ∈ Zx, z ^ 2 = 1 := by
    intro z hz
    rw [hZx, mem_rightConjugate_iff] at hz
    have h1 := sq_Z e hz
    have h2 : z ^ 2 = x⁻¹ * (x * z * x⁻¹) ^ 2 * x := by rw [pow_two, pow_two]; group
    rw [h2, h1]; group
  have hnot : ¬ Zx ≤ W := by
    intro hle
    apply hne
    apply Subgroup.eq_of_le_of_card_ge _ (by rw [hZx, rightConjugate_card])
    intro z hz
    exact mem_Z_of_sq e (hle hz) (hZxP hz).2 (hZx2 z hz)
  obtain ⟨w, hwZx, hwW⟩ := Set.not_subset.mp hnot
  have ht₀N : t₀ ∈ Subgroup.normalizer (Zx : Set X) := by
    rw [← rightConjugate_eq_self_iff, hZx, rightConjugate_mul]
    have h1 : x * t₀ = t₀ * (x * (x⁻¹ * (t₀⁻¹ * x * t₀))) := by group
    have hZt : rightConjugate Z t₀ = Z := by
      rw [rightConjugate_eq_self_iff]
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
        (fun z hz => M_comm' e hz.1 (Subgroup.mem_sup_left ht₀)))
    rw [h1, ← rightConjugate_mul, hZt, ← rightConjugate_mul]
    exact (rightConjugate_eq_self_iff _ _).mpr (c.le_normalizer_conj_Z (hP hx) (hcent x hx))
  have hwP := hZxP hwZx
  have hc1 : w⁻¹ * (t₀⁻¹ * w * t₀) ∈ Zx := by
    refine Zx.mul_mem (Zx.inv_mem hwZx) ?_
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht₀N) w).mp hwZx
    simpa using this
  have hc2 := comm_mem_R e hwP.1 hwP.2 ht₀
  have hcZ := mem_Z_of_sq e hc2.1 hc2.2 (hZx2 _ hc1)
  exact ht₀1 (eq_one_of_comm_mem_Z e hwP.1 hwW ht₀ hcZ)

theorem S_le_normalizer_R (c : ElemCtx G T S Q H g y) :
    S ≤ Subgroup.normalizer
      (((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G : Subgroup X) : Set X) := by
  intro s hs
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨S_le_normalizer_W c.elem hs,
      (sup_le Subgroup.le_normalizer c.frame.le_normalizer) (c.sylowFrame.sylow.le hs)⟩

theorem le_normalizer_R_of_central (c : ElemCtx G T S Q H g y)
    (hP : G ≤ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X))
    (hZ : G ≤ Subgroup.centralizer (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X)) :
    G ≤ Subgroup.normalizer
      (((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  have h := c.sylowFrame
  set W := rightConjugate T y ⊔ (T ⊔ rightConjugate T g) with hWdef
  set Z := (T ⊔ rightConjugate T g) ⊓ G with hZdef
  set R := W ⊓ G with hRdef
  intro y' hy'
  rw [← rightConjugate_eq_self_iff]
  by_contra hne
  set Ry := rightConjugate R y' with hRy
  have hRP : R ≤ S ⊓ G := inf_le_inf_right G e.A_le_S
  have hRyP : Ry ≤ S ⊓ G := by
    intro x hx
    rw [hRy, mem_rightConjugate_iff] at hx
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hP hy')) _).mp (hRP hx)
    simpa [mul_assoc] using h1
  have hZR : Z ≤ R := inf_le_inf_right G le_sup_right
  have hzy : ∀ z ∈ Z, y' * z * y'⁻¹ = z := by
    intro z hz
    have := Subgroup.mem_centralizer_iff.mp (hZ hy') z hz
    calc y' * z * y'⁻¹ = z * y' * y'⁻¹ := by rw [this]
      _ = z := by group
  have hZRy : Z ≤ Ry := by
    intro z hz
    rw [hRy, mem_rightConjugate_iff, hzy z hz]
    exact hZR hz
  have hidx : R.relIndex Ry ≤ 2 := by
    have h1 := Subgroup.relIndex_le_of_le_right hRyP (Elem47.relIndex_ne_zero_of_finite R _)
    rwa [c.relIndex_R_P] at h1
  have hcard_inf : Nat.card T * Nat.card T ≤ 2 * Nat.card (R ⊓ Ry : Subgroup X) := by
    have h1 := Subgroup.relIndex_mul_card R Ry
    rw [hRy, rightConjugate_card, card_R e] at h1
    rw [← h1]
    exact Nat.mul_le_mul_right _ hidx
  obtain ⟨a, haR, haZ⟩ : ∃ a ∈ R ⊓ Ry, a ∉ Z := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have h1 := Subgroup.card_le_of_le (show R ⊓ Ry ≤ Z from fun a ha => hall a ha)
    rw [e.card_Z] at h1
    have h4 := e.four_le_card
    nlinarith
  obtain ⟨u, huP, huW⟩ := c.exists_not_mem_W
  obtain ⟨t, ht, z, hz, hut⟩ := exists_conj_eq_mul e huP.1 huP.2 huW haR.1
  have htW : t ∈ W := Subgroup.mem_sup_right (Subgroup.mem_sup_left ht)
  have hform : ∀ x ∈ S ⊓ G, x ∉ R → ∃ z' ∈ Z, t⁻¹ * x * t = x * (a * z') := by
    intro x hxP hxR
    have hxW : x ∉ W := fun h1 => hxR ⟨h1, hxP.2⟩
    have hb : u⁻¹ * x ∈ R := by
      have h3 := mul_inv_mem_W e (S.inv_mem hxP.1) (S.inv_mem huP.1)
        (fun h1 => hxW (by simpa using W.inv_mem h1))
        (fun h1 => huW (by simpa using W.inv_mem h1))
      refine ⟨by simpa using h3, G.mul_mem (G.inv_mem huP.2) hxP.2⟩
    set b := u⁻¹ * x with hbdef
    have hab : a⁻¹ * (b⁻¹ * a * b) ∈ Z := comm_mem_Z_of_mem_W e haR.1.1 hb.1
    have hbt : b⁻¹ * (t⁻¹ * b * t) ∈ Z := comm_mem_Z_of_mem_W e hb.1 htW
    have hzb : z * b = b * z := e.Z_comm hz hb.1
    refine ⟨(a⁻¹ * (b⁻¹ * a * b)) * z * (b⁻¹ * (t⁻¹ * b * t)),
      Z.mul_mem (Z.mul_mem hab hz) hbt, ?_⟩
    have hx : x = u * b := by rw [hbdef]; group
    calc t⁻¹ * x * t = (t⁻¹ * u * t) * (t⁻¹ * b * t) := by rw [hx]; group
      _ = u * a * z * (t⁻¹ * b * t) := by rw [hut]
      _ = u * a * (z * b) * (b⁻¹ * (t⁻¹ * b * t)) := by group
      _ = u * a * (b * z) * (b⁻¹ * (t⁻¹ * b * t)) := by rw [hzb]
      _ = x * (a * ((a⁻¹ * (b⁻¹ * a * b)) * z * (b⁻¹ * (t⁻¹ * b * t)))) := by rw [hx]; group
  have htN : t ∈ Subgroup.normalizer (Ry : Set X) := by
    have hmap : ∀ x ∈ Ry, t⁻¹ * x * t ∈ Ry := by
      intro x hx
      by_cases hxR : x ∈ R
      · have h1 : x⁻¹ * (t⁻¹ * x * t) ∈ Z := comm_mem_Z_of_mem_W e hxR.1 htW
        have h2 : t⁻¹ * x * t = x * (x⁻¹ * (t⁻¹ * x * t)) := by group
        rw [h2]
        exact Ry.mul_mem hx (hZRy h1)
      · obtain ⟨z', hz', heq⟩ := hform x (hRyP hx) hxR
        rw [heq]
        exact Ry.mul_mem hx (Ry.mul_mem haR.2 (hZRy hz'))
    rw [← rightConjugate_eq_self_iff]
    apply Subgroup.eq_of_le_of_card_ge _ (rightConjugate_card _ _).ge
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have := hmap _ hx
    simpa [mul_assoc] using this
  have hGTZ : G ⊔ T ≤ Subgroup.centralizer (Z : Set X) := by
    refine sup_le hZ ?_
    intro t' ht'
    rw [Subgroup.mem_centralizer_iff]
    intro z' hz'
    exact M_comm' e hz'.1 (Subgroup.mem_sup_left ht')
  set K := (G ⊔ T) ⊓ Subgroup.normalizer (Ry : Set X) with hK
  have hSy : IsSylowOf 2 (rightConjugate S y') (G ⊔ T) :=
    isSylowOf_rightConjugate h.sylow (Subgroup.mem_sup_left hy')
  have hSyK : IsSylowOf 2 (rightConjugate S y') K :=
    hSy.of_le (le_inf hSy.le (rightConjugate_le_normalizer c.S_le_normalizer_R y')) inf_le_left
  have htK : t ∈ K := ⟨Subgroup.mem_sup_right ht, htN⟩
  have hz2 : IsPGroup 2 (Subgroup.zpowers t) :=
    h.toFrame.isPGroup.to_le (Subgroup.zpowers_le.mpr ht)
  obtain ⟨k, hk, hkey⟩ := isSylowOf_exists_conj_mem hSyK (Subgroup.zpowers_le.mpr htK) hz2
  have hks := hkey t (Subgroup.mem_zpowers t)
  rw [mem_rightConjugate_iff] at hks
  have htriv : ∀ x ∈ Ry, x⁻¹ * (t⁻¹ * x * t) ∈ Z := by
    intro x hx
    have hx₁ : k⁻¹ * x * k ∈ Ry := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk.2) x).mp hx
      simpa using this
    rw [hRy, mem_rightConjugate_iff] at hx₁
    have h1 := c.comm_mem_Z_of_mem_S hx₁ hks
    set w₀ := (y' * (k⁻¹ * x * k) * y'⁻¹)⁻¹ * ((y' * (k⁻¹ * t * k) * y'⁻¹)⁻¹ *
      (y' * (k⁻¹ * x * k) * y'⁻¹) * (y' * (k⁻¹ * t * k) * y'⁻¹)) with hw₀
    have hw₀' : x⁻¹ * (t⁻¹ * x * t) = k * (y'⁻¹ * w₀ * y') * k⁻¹ := by
      rw [hw₀]; group
    have h2 : y'⁻¹ * w₀ * y' = w₀ := by
      have := hzy w₀ h1
      calc y'⁻¹ * w₀ * y' = y'⁻¹ * (y' * w₀ * y'⁻¹) * y' := by rw [this]
        _ = w₀ := by group
    have h3 : k * w₀ * k⁻¹ = w₀ := by
      have := Subgroup.mem_centralizer_iff.mp (hGTZ hk.1) w₀ h1
      calc k * w₀ * k⁻¹ = w₀ * k * k⁻¹ := by rw [this]
        _ = w₀ := by group
    rw [hw₀', h2, h3]
    exact h1
  have hnot : ¬ Ry ≤ R := fun hle => hne (Subgroup.eq_of_le_of_card_ge hle
    (by rw [hRy, rightConjugate_card]))
  obtain ⟨x, hxRy, hxR⟩ := Set.not_subset.mp hnot
  obtain ⟨z', hz', heq⟩ := hform x (hRyP hxRy) hxR
  have h1 := htriv x hxRy
  rw [heq] at h1
  have h2 : a * z' ∈ Z := by simpa using h1
  apply haZ
  have := Z.mul_mem h2 (Z.inv_mem hz')
  simpa using this

theorem mem_P_of_two_pow (c : ElemCtx G T S Q H g y)
    (hP : G ≤ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X)) {x : X} (hx : x ∈ G) {k : ℕ}
    (hk : x ^ (2 ^ k) = 1) : x ∈ S ⊓ G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hz : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := j)
    (by rw [Nat.card_zpowers, hj])
  obtain ⟨k', hk', hkey⟩ := isSylowOf_exists_conj_mem c.isSylowOf_P
    (Subgroup.zpowers_le.mpr hx) hz
  have h1 := hkey x (Subgroup.mem_zpowers x)
  have h2 := (Subgroup.mem_normalizer_iff.mp (hP hk') _).mp h1
  simpa [mul_assoc] using h2

theorem le_normalizer_commSub (c : ElemCtx G T S Q H g y)
    (hP : G ≤ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X)) {e : X} (he : e ∈ T) :
    T ≤ Subgroup.normalizer ((commSub G (S ⊓ G) e hP : Subgroup X) : Set X) := by
  have hTP : T ≤ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (c.sylowFrame.le ht), c.frame.le_normalizer ht⟩
  have key : ∀ t ∈ T, ∀ x ∈ commSub G (S ⊓ G) e hP, t * x * t⁻¹ ∈ commSub G (S ⊓ G) e hP := by
    intro t ht x hx
    rw [mem_commSub] at hx ⊢
    obtain ⟨hxG, hxP⟩ := hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp (c.frame.le_normalizer ht) x).mp hxG, ?_⟩
    have hte : t * e = e * t := M_comm' c.elem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_left he)
    have h1 := (Subgroup.mem_normalizer_iff.mp (hTP ht) _).mp hxP
    have heq : (t * x * t⁻¹)⁻¹ * (e⁻¹ * (t * x * t⁻¹) * e) =
        t * (x⁻¹ * (e⁻¹ * x * e)) * t⁻¹ := by
      have hte' : e⁻¹ * t = t * e⁻¹ := by
        calc e⁻¹ * t = e⁻¹ * (t * e) * e⁻¹ := by group
          _ = e⁻¹ * (e * t) * e⁻¹ := by rw [hte]
          _ = t * e⁻¹ := by group
      calc (t * x * t⁻¹)⁻¹ * (e⁻¹ * (t * x * t⁻¹) * e)
          = t * x⁻¹ * t⁻¹ * (e⁻¹ * t) * x * (t⁻¹ * e) := by group
        _ = t * x⁻¹ * t⁻¹ * (t * e⁻¹) * x * (e * t⁻¹) := by
            rw [hte']
            congr 1
            calc t⁻¹ * e = t⁻¹ * (e * t) * t⁻¹ := by group
              _ = t⁻¹ * (t * e) * t⁻¹ := by rw [hte]
              _ = e * t⁻¹ := by group
        _ = t * (x⁻¹ * (e⁻¹ * x * e)) * t⁻¹ := by group
    rw [heq]
    exact h1
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key t ht x
  · intro hx
    have := key t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this

theorem false_of_normal_P (c : ElemCtx G T S Q H g y)
    (hP : G ≤ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  have h := c.sylowFrame
  have hF := h.toFrame
  set W := rightConjugate T y ⊔ (T ⊔ rightConjugate T g) with hWdef
  set Z := (T ⊔ rightConjugate T g) ⊓ G with hZdef
  set R := W ⊓ G with hRdef
  set P := S ⊓ G with hPdef
  by_cases hT₀ : ∃ t₀ ∈ T, t₀ ≠ 1 ∧ ∀ x ∈ G, x⁻¹ * (t₀⁻¹ * x * t₀) ∈ P
  · obtain ⟨t₀, ht₀, ht₀1, hcent⟩ := hT₀
    have hZN := c.le_normalizer_Z_of_centralizes hP ht₀ ht₀1 hcent
    have hTZ : T ≤ Subgroup.centralizer (Z : Set X) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact M_comm' e hz.1 (Subgroup.mem_sup_left ht)
    have hZC := c.le_centralizer_of_normal (sup_le hZN
      (hTZ.trans (Subgroup.centralizer_le_normalizer _))) hTZ
    exact c.not_le_normalizer_R (c.le_normalizer_R_of_central hP hZC)
  simp only [not_exists, not_and, not_forall] at hT₀
  obtain ⟨E, hET, hE2, hEcard⟩ := exists_four_le c.pRank_lt
  set L := G ⊔ T with hL
  have hPL : P ≤ L := inf_le_right.trans le_sup_left
  have hLP : L ≤ Subgroup.normalizer (P : Set X) := by
    refine sup_le hP ?_
    intro t ht
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (h.le ht), hF.le_normalizer ht⟩
  set P' := P.subgroupOf L with hP'
  have hP'n : P'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPL).mpr hLP
  set π := QuotientGroup.mk' P' with hπ
  set G' := G.subgroupOf L with hG'
  set E' := E.subgroupOf L with hE'
  set Gb := G'.map π with hGb
  set Eb := E'.map π with hEb
  have hπP : ∀ x : L, π x = 1 ↔ (x : X) ∈ P := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hP', Subgroup.mem_subgroupOf]
  set N₀ := G ⊓ Subgroup.normalizer (R : Set X) with hN₀
  have hPN₀ : P ≤ N₀ := fun x hx => ⟨hx.2, c.S_le_normalizer_R hx.1⟩
  have hkey : Gb ≤ (N₀.subgroupOf L).map π := by
    have hEbcard : Nat.card Eb = 2 ^ 2 := by
      rw [hEb, card_map_eq_of_ker π (fun x hx h1 => ?_), hE']
      · rw [← hEcard]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hET.trans le_sup_right)).toEquiv
      · rw [hπP] at h1
        have hxT : (x : X) ∈ T ⊓ G := ⟨hET (Subgroup.mem_subgroupOf.mp hx), h1.2⟩
        rw [hF.inf_eq_bot, Subgroup.mem_bot] at hxT
        exact Subtype.ext hxT
    have hEb2 : ∀ eb : Eb, eb ^ 2 = 1 := by
      rintro ⟨_, ⟨x, hx, rfl⟩⟩
      apply Subtype.ext
      have h1 := hE2 ⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩
      have h2 : (x : X) ^ 2 = 1 := by simpa using congrArg Subtype.val h1
      have h3 : x ^ 2 = 1 := Subtype.ext (by simpa using h2)
      simp [← map_pow, h3]
    have hGbodd : ¬ 2 ∣ Nat.card Gb := by
      intro h2
      obtain ⟨⟨xb, hxb⟩, hxb2⟩ := exists_prime_orderOf_dvd_card' 2 h2
      obtain ⟨x, hx, rfl⟩ := hxb
      have hx2 : π (x ^ 2) = 1 := by
        rw [map_pow]
        have := pow_orderOf_eq_one (⟨π x, Subgroup.mem_map_of_mem π hx⟩ : Gb)
        rw [hxb2] at this
        exact congrArg Subtype.val this
      rw [hπP] at hx2
      obtain ⟨m, hm⟩ := h.sylow.isPGroup.to_inf_left ⟨_, hx2⟩
      have hxm : (x : X) ^ (2 ^ (m + 1)) = 1 := by
        have : ((x : X) ^ 2) ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
        rw [pow_succ', pow_mul]
        simpa using this
      have hxP := c.mem_P_of_two_pow hP (Subgroup.mem_subgroupOf.mp hx) hxm
      have hπx : π x = 1 := (hπP x).mpr hxP
      have : orderOf (⟨π x, Subgroup.mem_map_of_mem π hx⟩ : Gb) = 1 := by
        rw [orderOf_eq_one_iff]
        exact Subtype.ext hπx
      omega
    have hEbN : Eb ≤ Subgroup.normalizer (Gb : Set (L ⧸ P')) := by
      have hE'N : E' ≤ Subgroup.normalizer (G' : Set L) := by
        intro x hx
        rw [hG', ← Subgroup.subgroupOf_normalizer_eq (le_sup_left : G ≤ L)]
        exact hF.le_normalizer (hET (Subgroup.mem_subgroupOf.mp hx))
      exact (Subgroup.map_mono hE'N).trans (Subgroup.le_normalizer_map _)
    have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      2 Nat.prime_two Eb Gb hEb2 hEbcard hGbodd hEbN
    rw [hgen]
    refine iSup_le fun eb => iSup_le fun heb1 => ?_
    obtain ⟨_, ⟨e₀, he₀, rfl⟩⟩ := eb
    have he₀T : (e₀ : X) ∈ T := hET (Subgroup.mem_subgroupOf.mp he₀)
    have he₀1 : (e₀ : X) ≠ 1 := by
      intro h1
      apply heb1
      apply Subtype.ext
      simp [show e₀ = 1 from Subtype.ext h1]
    rintro _ ⟨⟨x, hx, rfl⟩, hxC⟩
    have hxG : (x : X) ∈ G := Subgroup.mem_subgroupOf.mp hx
    have hcomm : (x : X)⁻¹ * ((e₀ : X)⁻¹ * x * e₀) ∈ P := by
      have h1 : π (x⁻¹ * (e₀⁻¹ * x * e₀)) = 1 := by
        have hc : π x * π e₀ = π e₀ * π x := Subgroup.mem_centralizer_singleton_iff.mp hxC
        simp only [map_mul, map_inv]
        rw [mul_assoc (π e₀)⁻¹, hc]
        group
      have h2 := (hπP _).mp h1
      simpa using h2
    have hxC' : (x : X) ∈ commSub G P e₀ hP := ⟨hxG, hcomm⟩
    have hne : commSub G P e₀ hP ≠ G := by
      intro heq
      obtain ⟨x₁, hx₁G, hx₁⟩ := hT₀ e₀ he₀T he₀1
      have hx₁C : x₁ ∈ commSub G P e₀ hP := by rw [heq]; exact hx₁G
      exact hx₁ hx₁C.2
    have hPC : P ≤ commSub G P e₀ hP := by
      intro z hz
      refine ⟨hz.2, P.mul_mem (P.inv_mem hz) ?_⟩
      have hTP : (e₀ : X)⁻¹ ∈ Subgroup.normalizer (P : Set X) :=
        Subgroup.inv_mem _ (hLP (Subgroup.mem_sup_right he₀T))
      have := (Subgroup.mem_normalizer_iff.mp hTP z).mp hz
      simpa using this
    have hR := c.le_normalizer_R (show commSub G P e₀ hP ≤ G from fun z hz => hz.1) hne
      (c.le_normalizer_commSub hP he₀T) hPC (fun z hz => hP hz.1)
    exact ⟨x, ⟨hxG, hR hxC'⟩, rfl⟩
  apply c.not_le_normalizer_R
  intro x hx
  have hxb : π ⟨x, (le_sup_left : G ≤ L) hx⟩ ∈ Gb := Subgroup.mem_map_of_mem π hx
  obtain ⟨n, hn, hnx⟩ := hkey hxb
  have h1 : π (n⁻¹ * ⟨x, (le_sup_left : G ≤ L) hx⟩) = 1 := by
    rw [map_mul, map_inv, hnx, inv_mul_cancel]
  rw [hπP] at h1
  have h2 : (n : X)⁻¹ * x ∈ N₀ := hPN₀ (by simpa using h1)
  have h3 := N₀.mul_mem (Subgroup.mem_subgroupOf.mp hn) h2
  have h4 : (n : X) * ((n : X)⁻¹ * x) = x := by group
  rw [h4] at h3
  exact h3.2

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
