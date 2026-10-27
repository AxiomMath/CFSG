module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

open Subgroup
open CFSG.GH74.GLS.Stage2.Signalizer.L53 (IsChiefPair exists_chief_below)
open scoped commutatorElement

section Abelian

variable {H : Type*} [Group H]

theorem comm_mul_of_abelian {R : Subgroup H} (hRn : R.Normal)
    (hRR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) {a b : H} (ha : a ∈ R) (hb : b ∈ R) (g : H) :
    ⁅a * b, g⁆ = ⁅a, g⁆ * ⁅b, g⁆ := by
  have hx : g * a⁻¹ * g⁻¹ ∈ R := hRn.conj_mem _ (R.inv_mem ha) g
  have hy : g * b⁻¹ * g⁻¹ ∈ R := hRn.conj_mem _ (R.inv_mem hb) g
  have e1 : ⁅a * b, g⁆ = a * (b * ((g * b⁻¹ * g⁻¹) * (g * a⁻¹ * g⁻¹))) := by
    simp only [commutatorElement_def]; group
  have e2 : ⁅a, g⁆ * ⁅b, g⁆ = a * ((g * a⁻¹ * g⁻¹) * (b * (g * b⁻¹ * g⁻¹))) := by
    simp only [commutatorElement_def]; group
  rw [e1, e2]
  congr 1
  rw [hRR _ hx _ (R.mul_mem hb hy), ← mul_assoc, ← mul_assoc]

theorem iterComm_mul_of_abelian {R : Subgroup H} (hRn : R.Normal)
    (hRR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) {a b : H} (ha : a ∈ R) (hb : b ∈ R) (g : H)
    (k : ℕ) : iterComm (a * b) g k = iterComm a g k * iterComm b g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterComm_succ, iterComm_succ, iterComm_succ, ih]
    exact comm_mul_of_abelian hRn hRR (iterComm_mem hRn ha g k) (iterComm_mem hRn hb g k) g

theorem iterComm_inv_of_abelian {R : Subgroup H} (hRn : R.Normal)
    (hRR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) {a : H} (ha : a ∈ R) (g : H) (k : ℕ) :
    iterComm a⁻¹ g k = (iterComm a g k)⁻¹ := by
  have h := iterComm_mul_of_abelian hRn hRR ha (R.inv_mem ha) g k
  rw [mul_inv_cancel, iterComm_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

end Abelian

section Weight

variable {H : Type*} [Group H]

theorem pairing_identity {U W R : Subgroup H} (hUn : U.Normal) (hWn : W.Normal) (hRn : R.Normal)
    (hRU : ∀ r ∈ R, ∀ x ∈ U, r * x = x * r) (hRW : ∀ r ∈ R, ∀ x ∈ W, r * x = x * r)
    (hRR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ R)
    (g : H) {v w : H} (hv : v ∈ U) (hw : w ∈ W) :
    ⁅g * v * g⁻¹, ⁅w, g⁆⁆ = ⁅⁅v, w⁆, g⁆ * ⁅⁅v, g⁆, w⁆⁻¹ := by
  have cU : ∀ x ∈ U, ∀ r ∈ R, x * r * x⁻¹ = r := fun x hx r hr => by
    rw [← hRU r hr x hx]; group
  have cW : ∀ x ∈ W, ∀ r ∈ R, x * r * x⁻¹ = r := fun x hx r hr => by
    rw [← hRW r hr x hx]; group
  have hgv : g * v * g⁻¹ ∈ U := hUn.conj_mem v hv g
  have hgw : g * w * g⁻¹ ∈ W := hWn.conj_mem w hw g
  have hvg : ⁅v, g⁆ ∈ U := comm_mem_of_normal hUn hv g
  set w' := g * w * g⁻¹ with hw'
  have h1 : ⁅g * v * g⁻¹, ⁅w, g⁆⁆ = ⁅g * v * g⁻¹, w⁆ * ⁅g * v * g⁻¹, w'⁆⁻¹ := by
    have e : ⁅g * v * g⁻¹, ⁅w, g⁆⁆ = ⁅g * v * g⁻¹, w⁆ *
        (w * (w'⁻¹ * ⁅g * v * g⁻¹, w'⁆⁻¹ * w'⁻¹⁻¹) * w⁻¹) := by
      rw [hw']; simp only [commutatorElement_def]; group
    rw [e, cW w'⁻¹ (W.inv_mem hgw) _ (R.inv_mem (hUW _ hgv _ hgw)),
      cW w hw _ (R.inv_mem (hUW _ hgv _ hgw))]
  have h2 : ⁅g * v * g⁻¹, w'⁆ = g * ⁅v, w⁆ * g⁻¹ := by
    rw [hw']; simp only [commutatorElement_def]; group
  have h3 : ⁅g * v * g⁻¹, w⁆ = ⁅⁅v, g⁆, w⁆⁻¹ * ⁅v, w⁆ := by
    have e1 : g * v * g⁻¹ = ⁅v, g⁆⁻¹ * v := by simp only [commutatorElement_def]; group
    have e2 : ⁅⁅v, g⁆⁻¹ * v, w⁆ = (⁅v, g⁆⁻¹ * ⁅v, w⁆ * ⁅v, g⁆⁻¹⁻¹) * ⁅⁅v, g⁆⁻¹, w⁆ := by
      simp only [commutatorElement_def]; group
    have e3 : ⁅⁅v, g⁆⁻¹, w⁆ = ⁅v, g⁆⁻¹ * ⁅⁅v, g⁆, w⁆⁻¹ * ⁅v, g⁆⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e1, e2, e3, cU _ (U.inv_mem hvg) _ (hUW _ hv _ hw),
      cU _ (U.inv_mem hvg) _ (R.inv_mem (hUW _ hvg _ hw))]
    exact hRR _ (hUW _ hv _ hw) _ (R.inv_mem (hUW _ hvg _ hw))
  rw [h1, h2, h3]
  have hx : ⁅v, w⁆ ∈ R := hUW _ hv _ hw
  have hy : ⁅⁅v, g⁆, w⁆ ∈ R := hUW _ hvg _ hw
  have hgx : g * ⁅v, w⁆ * g⁻¹ ∈ R := hRn.conj_mem _ hx g
  have e4 : ⁅⁅v, w⁆, g⁆ = ⁅v, w⁆ * (g * ⁅v, w⁆ * g⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e4, mul_assoc (⁅⁅v, g⁆, w⁆⁻¹), hRR _ (R.inv_mem hy) _ (R.mul_mem hx (R.inv_mem hgx))]

theorem weight_lemma {U U₁ W R : Subgroup H} (hUn : U.Normal) (hWn : W.Normal) (hRn : R.Normal)
    (hRU : ∀ r ∈ R, ∀ x ∈ U, r * x = x * r) (hRW : ∀ r ∈ R, ∀ x ∈ W, r * x = x * r)
    (hRR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ R)
    (hU₁W : ∀ u ∈ U₁, ∀ w ∈ W, ⁅u, w⁆ = 1) (g : H) {i j : ℕ} (hij : 1 ≤ i + j)
    (hZ : ∀ r ∈ R, iterComm r g j = 1) (hQ : ∀ u ∈ U, iterComm u g i ∈ U₁) :
    ∀ u ∈ U, ∀ w ∈ W, ⁅u, iterComm w g (i + j - 1)⁆ = 1 := by
  have hZk : ∀ r ∈ R, ∀ k, j ≤ k → iterComm r g k = 1 := by
    intro r hr k hk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [iterComm_add, hZ r hr, iterComm_one]
  have key : ∀ m b k : ℕ, j + b ≤ k + m + 1 → ∀ v ∈ U, iterComm v g b ∈ U₁ → ∀ w ∈ W,
      iterComm ⁅g ^ m * v * (g ^ m)⁻¹, iterComm w g m⁆ g k = 1 := by
    intro m
    induction m with
    | zero =>
      intro b k hbk v hv hvb w hw
      simp only [pow_zero, one_mul, inv_one, mul_one, iterComm_zero]
      rcases b with _ | b
      · rw [hU₁W v hvb w hw, iterComm_one]
      · exact hZk _ (hUW v hv w hw) k (by omega)
    | succ m ih =>
      intro b k hbk v hv hvb w hw
      rcases b with _ | b
      ·
        have h0 : ⁅g ^ (m + 1) * v * (g ^ (m + 1))⁻¹, iterComm w g (m + 1)⁆ =
            g ^ (m + 1) * ⁅v, (g ^ (m + 1))⁻¹ * iterComm w g (m + 1) * g ^ (m + 1)⁆ *
              (g ^ (m + 1))⁻¹ := by
          simp only [commutatorElement_def]; group
        have hwW : (g ^ (m + 1))⁻¹ * iterComm w g (m + 1) * g ^ (m + 1) ∈ W := by
          have := hWn.conj_mem _ (iterComm_mem hWn hw g (m + 1)) (g ^ (m + 1))⁻¹
          simpa using this
        rw [h0, hU₁W v hvb _ hwW]
        simp [iterComm_one]
      ·
        set v' := g ^ m * v * (g ^ m)⁻¹ with hv'
        set w' := iterComm w g m with hw'
        have hv'U : v' ∈ U := hUn.conj_mem v hv _
        have hw'W : w' ∈ W := iterComm_mem hWn hw g m
        have e1 : g ^ (m + 1) * v * (g ^ (m + 1))⁻¹ = g * v' * g⁻¹ := by
          rw [hv', pow_succ']; group
        have e2 : iterComm w g (m + 1) = ⁅w', g⁆ := iterComm_succ w g m
        rw [e1, e2, pairing_identity hUn hWn hRn hRU hRW hRR hUW g hv'U hw'W]
        have hx : ⁅v', w'⁆ ∈ R := hUW _ hv'U _ hw'W
        have hvg : ⁅v', g⁆ ∈ U := comm_mem_of_normal hUn hv'U g
        have hy : ⁅⁅v', g⁆, w'⁆ ∈ R := hUW _ hvg _ hw'W
        rw [iterComm_mul_of_abelian hRn hRR (comm_mem_of_normal hRn hx g) (R.inv_mem hy),
          iterComm_inv_of_abelian hRn hRR hy, ← iterComm_succ']
        have hA : iterComm ⁅v', w'⁆ g (k + 1) = 1 := ih (b + 1) (k + 1) (by omega) v hv hvb w hw
        have hvgc : ⁅v', g⁆ = g ^ m * ⁅v, g⁆ * (g ^ m)⁻¹ := by
          rw [hv']
          have := conj_iterComm (g ^ m) v g 1
          simp only [iterComm_succ, iterComm_zero] at this
          rw [this]
          congr 1
          group
        have hB : iterComm ⁅⁅v', g⁆, w'⁆ g k = 1 := by
          rw [hvgc]
          refine ih b k (by omega) _ (comm_mem_of_normal hUn hv g) ?_ w hw
          rw [← iterComm_succ']
          exact hvb
        rw [hA, hB, inv_one, mul_one]
  intro u hu w hw
  set n := i + j - 1
  have hv : (g ^ n)⁻¹ * u * g ^ n ∈ U := by
    have := hUn.conj_mem u hu (g ^ n)⁻¹
    simpa using this
  have := key n i 0 (by omega) _ hv (hQ _ hv) w hw
  rw [iterComm_zero] at this
  have e : g ^ n * ((g ^ n)⁻¹ * u * g ^ n) * (g ^ n)⁻¹ = u := by group
  rwa [e] at this

end Weight

section Theorem3

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem chief_iterComm_le {P Q : Subgroup G} (hPn : P.Normal) (hPp : IsPGroup p P)
    (hQn : Q.Normal) (hQP : Q ≤ P) (hPQ : ⁅P, Q⁆ ≤ Q ⊓ centralizer (Q : Set G))
    (hCQ : P ⊓ centralizer (Q : Set G) ≤ Q) (g : G) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hypQ : ∀ X Y : Subgroup G, IsChiefPair X Y → X ≤ Q → ∀ x ∈ X, iterComm x g i ∈ Y)
    (hypZ : ∀ X Y : Subgroup G, IsChiefPair X Y → X ≤ Q ⊓ centralizer (Q : Set G) →
      ∀ x ∈ X, iterComm x g j ∈ Y) :
    ∀ X Y : Subgroup G, IsChiefPair X Y → X ≤ P → ∀ x ∈ X, iterComm x g (i + j - 1) ∈ Y := by
  have hPnil : Group.IsNilpotent P := hPp.isNilpotent
  suffices h : ∀ n : ℕ, ∀ X Y : Subgroup G, Nat.card X = n → IsChiefPair X Y → X ≤ P →
      ∀ x ∈ X, iterComm x g (i + j - 1) ∈ Y from fun X Y hc hXP => h _ X Y rfl hc hXP
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X Y hn hc hXP
  have hXn : X.Normal := hc.1
  have hYn : Y.Normal := hc.2.1
  by_cases hXQ : X ≤ Q
  · intro x hx
    exact iterComm_mem_of_le hYn (hypQ X Y hc hXQ x hx) (by omega)
  have hQX : ⁅Q, X⁆ ≠ ⊥ := by
    intro h
    apply hXQ
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact fun x hx => hCQ ⟨hXP hx, h hx⟩
  obtain ⟨U, hUmin⟩ := (Set.toFinite {U : Subgroup G | U.Normal ∧ U ≤ Q ∧ ⁅U, X⁆ ≠ ⊥}).exists_minimal
    ⟨Q, hQn, le_rfl, hQX⟩
  obtain ⟨hUn, hUQ, hUX⟩ := hUmin.prop
  have hU1 : U ≠ ⊥ := by
    rintro rfl
    exact hUX (Subgroup.commutator_bot_left X)
  obtain ⟨U₁, hcU⟩ := exists_chief_below hUn hU1
  have hU₁X : ⁅U₁, X⁆ = ⊥ := by
    by_contra hne
    have hU₁U : U₁ < U := hcU.2.2.1
    exact hU₁U.not_ge (hUmin.le_of_le ⟨hcU.2.1, hU₁U.le.trans hUQ, hne⟩ hU₁U.le)
  set R := ⁅U, X⁆ with hRdef
  have hRn : R.Normal := Subgroup.commutator_normal U X
  obtain ⟨R₁, hcR⟩ := exists_chief_below hRn hUX
  have hRZ : R ≤ Q ⊓ centralizer (Q : Set G) := by
    refine (Subgroup.commutator_mono hUQ hXP).trans ?_
    rw [Subgroup.commutator_comm]
    exact hPQ
  have hRP : R ≤ P := hRZ.trans (inf_le_left.trans hQP)
  have hR₁n : R₁.Normal := hcR.2.1
  have hRPc : ⁅R, P⁆ ≤ R₁ := comm_le_of_chief hPnil hPn hRP hcR
  let K : Subgroup G :=
    { carrier := {x | x ∈ X ∧ ∀ u ∈ U, ⁅u, x⁆ ∈ R₁}
      mul_mem' := by
        rintro a b ⟨haX, ha⟩ ⟨hbX, hb⟩
        refine ⟨X.mul_mem haX hbX, fun u hu => ?_⟩
        have e : ⁅u, a * b⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact R₁.mul_mem (ha u hu) (hR₁n.conj_mem _ (hb u hu) a)
      one_mem' := ⟨X.one_mem, fun u _ => by simp⟩
      inv_mem' := by
        rintro a ⟨haX, ha⟩
        refine ⟨X.inv_mem haX, fun u hu => ?_⟩
        have e : ⁅u, a⁻¹⁆ = a⁻¹ * ⁅u, a⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        have := hR₁n.conj_mem _ (R₁.inv_mem (ha u hu)) a⁻¹
        simpa using this }
  have hKX : K ≤ X := fun x hx => hx.1
  have hKn : K.Normal := by
    refine ⟨fun x hx c => ⟨hXn.conj_mem x hx.1 c, fun u hu => ?_⟩⟩
    have e : ⁅u, c * x * c⁻¹⁆ = c * ⁅c⁻¹ * u * c, x⁆ * c⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine hR₁n.conj_mem _ (hx.2 _ ?_) c
    have := hUn.conj_mem u hu c⁻¹
    simpa using this
  have hKlt : K < X := by
    refine lt_of_le_of_ne hKX fun hKeq => ?_
    have : R ≤ R₁ := by
      rw [hRdef, Subgroup.commutator_le]
      intro u hu x hx
      rw [← hKeq] at hx
      exact hx.2 u hu
    exact hcR.2.2.1.not_ge this
  by_cases hKY : K ≤ Y
  ·
    intro x hx
    refine hKY ⟨iterComm_mem hXn hx g _, fun u hu => ?_⟩
    let π := QuotientGroup.mk' R₁
    have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective R₁
    have hcomm : ∀ a b : G, ⁅a, b⁆ ∈ R₁ → π a * π b = π b * π a := by
      intro a b hab
      have : π ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hab
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hUn' : (U.map π).Normal := hUn.map _ hπsurj
    have hXn' : (X.map π).Normal := hXn.map _ hπsurj
    have hRn' : (R.map π).Normal := hRn.map _ hπsurj
    have hRU' : ∀ r ∈ R.map π, ∀ y ∈ U.map π, r * y = y * r := by
      rintro _ ⟨r, hr, rfl⟩ _ ⟨y, hy, rfl⟩
      exact hcomm r y (hRPc (Subgroup.commutator_mem_commutator hr (hUQ.trans hQP hy)))
    have hRW' : ∀ r ∈ R.map π, ∀ y ∈ X.map π, r * y = y * r := by
      rintro _ ⟨r, hr, rfl⟩ _ ⟨y, hy, rfl⟩
      exact hcomm r y (hRPc (Subgroup.commutator_mem_commutator hr (hXP hy)))
    have hRR' : ∀ a ∈ R.map π, ∀ b ∈ R.map π, a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact hcomm a b (hRPc (Subgroup.commutator_mem_commutator ha (hRP hb)))
    have hUW' : ∀ y ∈ U.map π, ∀ z ∈ X.map π, ⁅y, z⁆ ∈ R.map π := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      rw [← map_commutatorElement]
      exact ⟨_, Subgroup.commutator_mem_commutator hy hz, rfl⟩
    have hU₁W' : ∀ y ∈ U₁.map π, ∀ z ∈ X.map π, ⁅y, z⁆ = 1 := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      rw [← map_commutatorElement]
      have : ⁅y, z⁆ ∈ ⁅U₁, X⁆ := Subgroup.commutator_mem_commutator hy hz
      rw [hU₁X, Subgroup.mem_bot] at this
      rw [this, map_one]
    have hZ' : ∀ r ∈ R.map π, iterComm r (π g) j = 1 := by
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_iterComm]
      exact (QuotientGroup.eq_one_iff _).mpr (hypZ R R₁ hcR hRZ r hr)
    have hQ' : ∀ y ∈ U.map π, iterComm y (π g) i ∈ U₁.map π := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_iterComm]
      exact ⟨_, hypQ U U₁ hcU hUQ y hy, rfl⟩
    have hw := weight_lemma hUn' hXn' hRn' hRU' hRW' hRR' hUW' hU₁W' (π g) (by omega) hZ' hQ'
      (π u) ⟨u, hu, rfl⟩ (π x) ⟨x, hx, rfl⟩
    rw [← map_iterComm, ← map_commutatorElement] at hw
    exact (QuotientGroup.eq_one_iff _).mp hw
  ·
    have hKYX : K ⊔ Y = X := by
      rcases hc.2.2.2 (K ⊔ Y) inferInstance le_sup_right (sup_le hKX hc.2.2.1.le) with h | h
      · exact absurd (h ▸ le_sup_left : K ≤ Y) hKY
      · exact h
    have hcK : IsChiefPair K (K ⊓ Y) := by
      refine ⟨hKn, inferInstance, lt_of_le_of_ne inf_le_left fun h => hKY (h ▸ inf_le_right),
        fun Z hZn hKYZ hZK => ?_⟩
      rcases hc.2.2.2 (Z ⊔ Y) inferInstance le_sup_right
          (sup_le (hZK.trans hKX) hc.2.2.1.le) with h | h
      · left
        exact le_antisymm (le_inf hZK (h ▸ le_sup_left)) hKYZ
      · right
        refine le_antisymm hZK fun k hk => ?_
        have hkX : k ∈ Z ⊔ Y := h ▸ hKX hk
        rw [Subgroup.mem_sup_of_normal_right] at hkX
        obtain ⟨z, hz, y, hy, rfl⟩ := hkX
        have hyK : y ∈ K := by
          have : y = z⁻¹ * (z * y) := by group
          rw [this]
          exact K.mul_mem (K.inv_mem (hZK hz)) hk
        exact Z.mul_mem hz (hKYZ ⟨hyK, hy⟩)
    have hcard : Nat.card K < n := hn ▸ Subgroup.card_lt_of_lt hKlt
    have hK' := ih _ hcard K (K ⊓ Y) rfl hcK (hKX.trans hXP)
    intro x hx
    rw [← hKYX, Subgroup.mem_sup_of_normal_right] at hx
    obtain ⟨k, hk, y, hy, rfl⟩ := hx
    rw [iterComm_mul_mem_iff hYn k hy]
    exact (hK' k hk).2

end Theorem3

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

end
