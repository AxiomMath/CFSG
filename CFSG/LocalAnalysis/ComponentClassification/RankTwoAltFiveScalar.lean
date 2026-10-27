module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveTransv
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveInvol

public section

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

namespace CFSG.ComponentClassification.RankTwoAltFive

theorem perm5_centralizer_P0 : ∀ σ : Perm (Fin 5), σ * (k1 : Perm (Fin 5)) = k1 * σ →
    σ * (k2 : Perm (Fin 5)) = k2 * σ →
      σ = 1 ∨ σ = (k1 : Perm (Fin 5)) ∨ σ = (k2 : Perm (Fin 5)) ∨
        σ = ((k1 * k2 : A5) : Perm (Fin 5)) := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_pow_two_mem {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hRc : R ≤ centralizer (R : Set G)) {u : G} (huK : u ∈ K) (huN : u ∈ normalizer (R : Set G))
    (a : ℕ) (hu : u ^ 2 ^ a ∈ centralizer (R : Set G)) : u ∈ centralizer (R : Set G) := by
  induction a generalizing u with
  | zero => simpa using hu
  | succ a ih =>
    apply ih huK huN
    apply mem_centralizer_of_sq_mem hR hRc (pow_mem huK _) (pow_mem huN _)
    rw [← pow_add, ← two_mul, ← pow_succ']
    exact hu

theorem exists_odd_of_not_le {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hRc : R ≤ centralizer (R : Set G))
    (hK : ¬ K ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G)) :
    ∃ y ∈ K ⊓ normalizer (R : Set G), y ∉ centralizer (R : Set G) ∧ Odd (orderOf y) := by
  obtain ⟨y, hy, hyC⟩ := IsConcreteLE.not_le_iff_exists.mp hK
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨y ^ 2 ^ a, pow_mem hy _, fun h1 => hyC (mem_centralizer_of_pow_two_mem hR hRc
    (mem_inf.mp hy).1 (mem_inf.mp hy).2 a h1), ?_⟩
  rw [orderOf_pow' y (pow_ne_zero _ two_ne_zero), hab, Nat.gcd_mul_right_left,
    Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  exact hb

omit [Finite G] in
theorem pow_conj_ne {E : Subgroup G} {b : G} (hb3 : b ^ 3 = 1)
    (hbf : ∀ x ∈ E, x ≠ 1 → b⁻¹ * x * b ≠ x) {k : ℕ} (hk : k % 3 ≠ 0) {x : G} (hx : x ∈ E)
    (hx1 : x ≠ 1) : (b ^ k)⁻¹ * x * b ^ k ≠ x := by
  have hbk : b ^ k = b ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hb3, one_pow, one_mul]
  rw [hbk]
  have hk3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h1 | h1
  · rw [h1, pow_one]
    exact hbf x hx hx1
  · rw [h1]
    intro hfix
    apply hbf x hx hx1
    have h4 : b ^ 4 = b := by
      rw [show 4 = 3 + 1 by rfl, pow_succ, hb3, one_mul]
    calc b⁻¹ * x * b = (b ^ 4)⁻¹ * x * b ^ 4 := by rw [h4]
      _ = (b ^ 2)⁻¹ * ((b ^ 2)⁻¹ * x * b ^ 2) * b ^ 2 := by group
      _ = x := by rw [hfix, hfix]

omit [Finite G] in
theorem conj_mem_centralizer {V : Subgroup G} {n c : G} (hn : n ∈ normalizer (V : Set G))
    (hc : c ∈ centralizer (V : Set G)) : n * c * n⁻¹ ∈ centralizer (V : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro v hv
  have hu : n⁻¹ * v * n ∈ V := by simpa using (mem_normalizer_iff.mp (inv_mem hn) v).mp hv
  have h1 := hc _ hu
  calc v * (n * c * n⁻¹) = n * ((n⁻¹ * v * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * v * n)) * n⁻¹ := by rw [h1]
    _ = n * c * n⁻¹ * v := by group

theorem exists_mul_mem_normalizer {H P : Subgroup G} (hP : IsSylowOf 2 P H) {t : G}
    (ht : t ∈ normalizer (H : Set G)) : ∃ p ∈ H, p * t ∈ normalizer (P : Set G) := by
  have hP' := AschbacherTheorem3.isSylowOf_rightConjugate hP t⁻¹
  rw [(rightConjugate_eq_self_iff H t⁻¹).mpr (inv_mem ht)] at hP'
  obtain ⟨c, hc, hPc⟩ := Lemma22.exists_conj_eq_of_isSylowOf hP hP'
  refine ⟨c⁻¹, inv_mem hc, mem_normalizer_of_map_conj_eq ?_⟩
  have e1 : (MulAut.conj (c⁻¹ * t)).toMonoidHom =
      (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have e2 : P.map (MulAut.conj t).toMonoidHom = P.map (MulAut.conj c).toMonoidHom := by
    have h1 := hPc
    change P.map (MulAut.conj t⁻¹⁻¹).toMonoidHom = P.map (MulAut.conj c).toMonoidHom at h1
    rwa [inv_inv] at h1
  have e3 : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
    group
  rw [e1, ← Subgroup.map_map, e2, Subgroup.map_map, e3, Subgroup.map_id]

omit [Finite G] in
theorem card_sup_mul_card_inf_of_le {A N : Subgroup G} (hAN : A ≤ normalizer (N : Set G)) :
    Nat.card (A ⊔ N : Subgroup G) * Nat.card (A ⊓ N : Subgroup G) = Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

omit [Finite G] in
theorem comm_mul_mul {P V V₀ : Subgroup G} (hV₀V : V₀ ≤ V)
    (hV₀Z : ∀ w ∈ V₀, ∀ x ∈ P, x * w = w * x) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hVP : ∀ x ∈ P, ∀ v ∈ V, v⁻¹ * (x * v * x⁻¹) ∈ V₀) {x x' v v' : G} (hx : x ∈ P)
    (hx' : x' ∈ P) (hv : v ∈ V) (hv' : v' ∈ V) :
    ∃ w ∈ V₀, (x * v) * (x' * v') * (x * v)⁻¹ * (x' * v')⁻¹ = (x * x' * x⁻¹ * x'⁻¹) * w := by
  obtain ⟨d₁, hd₁⟩ : ∃ d₁, v⁻¹ * (x'⁻¹ * v * x'⁻¹⁻¹) = d₁ := ⟨_, rfl⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d₂, v'⁻¹ * (x * v' * x⁻¹) = d₂ := ⟨_, rfl⟩
  have hd₁V : d₁ ∈ V₀ := hd₁ ▸ hVP _ (inv_mem hx') v hv
  have hd₂V : d₂ ∈ V₀ := hd₂ ▸ hVP x hx v' hv'
  have e1 : v * x' = x' * (v * d₁) := by
    rw [← hd₁]; group
  have e2 : v' * x⁻¹ = x⁻¹ * (v' * d₂) := by
    rw [← hd₂]; group
  refine ⟨d₂ * d₁, mul_mem hd₂V hd₁V, ?_⟩
  have hd₁x : x⁻¹ * d₁ = d₁ * x⁻¹ := hV₀Z d₁ hd₁V _ (inv_mem hx)
  have hd₁x' : x'⁻¹ * d₁ = d₁ * x'⁻¹ := hV₀Z d₁ hd₁V _ (inv_mem hx')
  have hd₂x' : x'⁻¹ * d₂ = d₂ * x'⁻¹ := hV₀Z d₂ hd₂V _ (inv_mem hx')
  have hd₁v' : v'⁻¹ * d₁ = d₁ * v'⁻¹ := hVab _ (inv_mem hv') _ (hV₀V hd₁V)
  have hvv : v * d₁ * v' * v⁻¹ = v' * d₁ := by
    have h1 : d₁ * v' = v' * d₁ := hVab _ (hV₀V hd₁V) _ hv'
    have h2 : v * (v' * d₁) = v' * d₁ * v := hVab _ hv _ (mul_mem hv' (hV₀V hd₁V))
    calc v * d₁ * v' * v⁻¹ = v * (d₁ * v') * v⁻¹ := by group
      _ = v * (v' * d₁) * v⁻¹ := by rw [h1]
      _ = v' * d₁ * v * v⁻¹ := by rw [h2]
      _ = v' * d₁ := by group
  have hv'd : v' * d₂ * v'⁻¹ = d₂ := by
    have h1 : v' * d₂ = d₂ * v' := hVab _ hv' _ (hV₀V hd₂V)
    rw [h1]; group
  calc (x * v) * (x' * v') * (x * v)⁻¹ * (x' * v')⁻¹
      = x * (v * x') * v' * v⁻¹ * x⁻¹ * v'⁻¹ * x'⁻¹ := by group
    _ = x * x' * (v * d₁ * v' * v⁻¹) * x⁻¹ * v'⁻¹ * x'⁻¹ := by rw [e1]; group
    _ = x * x' * v' * (d₁ * x⁻¹) * v'⁻¹ * x'⁻¹ := by rw [hvv]; group
    _ = x * x' * v' * x⁻¹ * (d₁ * v'⁻¹) * x'⁻¹ := by rw [← hd₁x]; group
    _ = x * x' * v' * x⁻¹ * v'⁻¹ * (d₁ * x'⁻¹) := by rw [← hd₁v']; group
    _ = x * x' * (v' * x⁻¹) * v'⁻¹ * x'⁻¹ * d₁ := by rw [← hd₁x']; group
    _ = x * x' * x⁻¹ * (v' * d₂ * v'⁻¹) * x'⁻¹ * d₁ := by rw [e2]; group
    _ = x * x' * x⁻¹ * (d₂ * x'⁻¹) * d₁ := by rw [hv'd]; group
    _ = (x * x' * x⁻¹ * x'⁻¹) * (d₂ * d₁) := by rw [← hd₂x']; group

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

theorem centralizer_le_normalizer_A :
    centralizer ((R ⊔ T : Subgroup G) : Set G) ≤ normalizer (A : Set G) := by
  have hR2 : ∀ x ∈ R, x * x = 1 := fun x hx => h.mul_self (mem_sup_left hx)
  obtain ⟨r, hr, hr1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  intro x hx
  have h1 := centralizer_le_normalizer_conj h.hyp.standard 1
    (by rw [rightConjugate_one]; exact h.sylowR.le hr) hr1 (hR2 r hr)
    (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx r (mem_sup_left hr)).symm)
  rwa [rightConjugate_one] at h1

theorem centralizer_le_sup :
    centralizer ((R ⊔ T : Subgroup G) : Set G) ≤ V₀ ⊔ centralizer (A : Set G) := by
  obtain ⟨e⟩ := h.equiv
  have hV₀A : Nat.card (V₀.subgroupOf A) = 4 := by
    rw [← h.card_V₀]
    exact Nat.card_congr (subgroupOfEquivOfLe h.V₀_le_A).toEquiv
  obtain ⟨ψ, hψ⟩ := exists_equiv_map_P0 e hV₀A
  set e' : ↥A ≃* A5 := ψ.symm with he'
  have hψV : ∀ q ∈ P0, ((ψ q : ↥A) : G) ∈ V₀ := fun q hq => by
    have : ψ q ∈ V₀.subgroupOf A := hψ ▸ ⟨q, hq, rfl⟩
    exact mem_subgroupOf.mp this
  intro x hx
  have hxN := h.centralizer_le_normalizer_A hx
  set σ := autPerm e' ⟨x, hxN⟩ with hσ
  have hcomm : ∀ q ∈ P0, σ * ((q : A5) : Perm (Fin 5)) = (q : Perm (Fin 5)) * σ := by
    intro q hq
    have hqA : ((ψ q : ↥A) : G) ∈ A := (ψ q).2
    have h1 : autPerm e' ⟨((ψ q : ↥A) : G), le_normalizer hqA⟩ = ((q : A5) : Perm (Fin 5)) := by
      rw [autPerm_of_mem e' hqA]
      congr 2
      rw [he']
      exact ψ.symm_apply_apply q
    rw [← h1, hσ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp hx _ (h.V₀_le (hψV q hq))).symm
  have hk1 : k1 ∈ P0 := by rw [mem_P0]; decide
  have hk2 : k2 ∈ P0 := by rw [mem_P0]; decide
  have hk12 : k1 * k2 ∈ P0 := by rw [mem_P0]; decide
  obtain ⟨q, hq, hσq⟩ : ∃ q ∈ P0, σ = ((q : A5) : Perm (Fin 5)) := by
    rcases perm5_centralizer_P0 σ (hcomm k1 hk1) (hcomm k2 hk2) with h1 | h1 | h1 | h1
    · exact ⟨1, one_mem _, by rw [h1]; rfl⟩
    · exact ⟨k1, hk1, h1⟩
    · exact ⟨k2, hk2, h1⟩
    · exact ⟨k1 * k2, hk12, h1⟩
  set w₀ : G := ((ψ q : ↥A) : G) with hw₀
  have hw₀V : w₀ ∈ V₀ := hψV q hq
  have hw₀A : w₀ ∈ A := (ψ q).2
  have hσw : autPerm e' ⟨w₀, le_normalizer hw₀A⟩ = σ := by
    rw [autPerm_of_mem e' hw₀A, hσq]
    congr 2
    rw [he']
    exact ψ.symm_apply_apply q
  have hxw : x * w₀⁻¹ ∈ centralizer (A : Set G) := by
    have h1 : autPerm e' (⟨x, hxN⟩ * (⟨w₀, le_normalizer hw₀A⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, hσw, ← hσ, mul_inv_cancel]
    exact (autPerm_eq_one_iff e' _).mp h1
  have : x = (x * w₀⁻¹) * w₀ := by group
  rw [this, sup_comm]
  exact mul_mem (mem_sup_left hxw) (mem_sup_right hw₀V)

theorem eq_of_le_centralizer {X : Subgroup G} (hVX : R ⊔ T ≤ X)
    (hXC : X ≤ centralizer ((R ⊔ T : Subgroup G) : Set G)) (hX : IsPGroup 2 X) : X = R ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXK : X ⊓ centralizer (A : Set G) = R :=
    h.sylowR.eq_of_le (le_inf (le_sup_left.trans hVX) h.sylowR.le) inf_le_right
      (hX.to_le inf_le_left)
  have hKN : centralizer (A : Set G) ≤ normalizer (V₀ : Set G) :=
    (centralizer_le fun v hv => h.V₀_le_A hv).trans (centralizer_le_normalizer _)
  refine le_antisymm (fun x hx => ?_) hVX
  obtain ⟨w, hw, k, hk, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer hKN (h.centralizer_le_sup (hXC hx))
  have hkX : k ∈ X := by
    have := mul_mem (inv_mem (hVX (h.V₀_le hw))) hx
    simpa using this
  have hkR : k ∈ R := hXK ▸ mem_inf.mpr ⟨hkX, hk⟩
  exact mul_mem (h.V₀_le hw) (mem_sup_left hkR)

theorem factorization_card_centralizer :
    (Nat.card (centralizer ((R ⊔ T : Subgroup G) : Set G))).factorization 2 = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup 2 ↥(R ⊔ T) := IsPGroup.of_card (n := 4) (by rw [h.loc.card]; rfl)
  have hVC : R ⊔ T ≤ centralizer ((R ⊔ T : Subgroup G) : Set G) :=
    le_centralizer_self_of_isElemAbelian h.loc.elem
  obtain ⟨S, hS, hVS⟩ := exists_isSylowOf_le hVC hVp
  have hSV := h.eq_of_le_centralizer hVS hS.le hS.isPGroup
  have hc := hS.card_eq
  rw [hSV, h.loc.card, show (16 : ℕ) = 2 ^ 4 by rfl] at hc
  exact (Nat.pow_right_injective le_rfl hc).symm

theorem exists_sylow_transv : ∃ P : Subgroup G, IsSylowOf 2 P (transvGroup (R ⊔ T) V₀) ∧
    R ⊔ T ≤ P ∧ P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T ∧ Nat.card P = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup 2 ↥(R ⊔ T) := IsPGroup.of_card (n := 4) (by rw [h.loc.card]; rfl)
  have hVC : R ⊔ T ≤ centralizer ((R ⊔ T : Subgroup G) : Set G) :=
    le_centralizer_self_of_isElemAbelian h.loc.elem
  have hCP := h.centralizer_le_transvGroup
  obtain ⟨P, hP, hVP⟩ := exists_isSylowOf_le (hVC.trans hCP) hVp
  refine ⟨P, hP, hVP, ?_, ?_⟩
  · exact h.eq_of_le_centralizer (le_inf hVP hVC) inf_le_right (hP.isPGroup.to_le inf_le_left)
  · have h1 := Subgroup.relIndex_mul_card (centralizer ((R ⊔ T : Subgroup G) : Set G))
      (transvGroup (R ⊔ T) V₀)
    rw [h.relIndex_transv, inf_eq_left.mpr hCP] at h1
    have hC0 : Nat.card (centralizer ((R ⊔ T : Subgroup G) : Set G)) ≠ 0 := Nat.card_pos.ne'
    have hf : (Nat.card (transvGroup (R ⊔ T) V₀)).factorization 2 = 6 := by
      rw [← h1, Nat.factorization_mul (by norm_num) hC0, Finsupp.add_apply,
        h.factorization_card_centralizer, show (4 : ℕ) = 2 ^ 2 by rfl, Nat.factorization_pow,
        Finsupp.smul_apply, Nat.Prime.factorization Nat.prime_two, Finsupp.single_eq_same]
      rfl
    rw [hP.card_eq, hf]
    rfl

theorem conj_ne_of_not_mem {y : G} (hyK : y ∈ centralizer (A : Set G))
    (hyN : y ∈ normalizer (R : Set G)) (hyC : y ∉ centralizer (R : Set G)) {r : G} (hr : r ∈ R)
    (hr1 : r ≠ 1) : y * r * y⁻¹ ≠ r := by
  intro hfix
  have hR2 : ∀ x ∈ R, x * x = 1 := fun x hx => h.mul_self (mem_sup_left hx)
  have hRc : R ≤ centralizer (R : Set G) := le_centralizer_self_of_isElemAbelian h.elemR
  apply hyC
  refine mem_centralizer_of_sq_mem h.sylowR hRc hyK hyN ?_
  obtain ⟨s₀, hs₀, hs₀1, hs₀r⟩ := exists_ne_one_ne h.cardR hR2 hr
  have hyR : ∀ x ∈ R, y * x * y⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hyN x).mp hx
  have hys : y * s₀ * y⁻¹ = s₀ ∨ y * s₀ * y⁻¹ = r * s₀ := by
    have hne1 : y * s₀ * y⁻¹ ≠ 1 := fun h1 => hs₀1 (by
      calc s₀ = y⁻¹ * (y * s₀ * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; group)
    have hner : y * s₀ * y⁻¹ ≠ r := fun h1 => hs₀r (by
      have : y * s₀ * y⁻¹ = y * r * y⁻¹ := by rw [h1, hfix]
      exact mul_left_cancel (mul_right_cancel this))
    rcases mem_four h.cardR hR2 hr hs₀ hr1 hs₀1 hs₀r.symm (hyR s₀ hs₀) with h1 | h1 | h1 | h1
    · exact absurd h1 hne1
    · exact absurd h1 hner
    · exact Or.inl h1
    · exact Or.inr h1
  have hys2 : y * y * s₀ * (y * y)⁻¹ = s₀ := by
    rcases hys with h1 | h1
    · calc y * y * s₀ * (y * y)⁻¹ = y * (y * s₀ * y⁻¹) * y⁻¹ := by group
        _ = s₀ := by rw [h1, h1]
    · calc y * y * s₀ * (y * y)⁻¹ = y * (y * s₀ * y⁻¹) * y⁻¹ := by group
        _ = y * (r * s₀) * y⁻¹ := by rw [h1]
        _ = (y * r * y⁻¹) * (y * s₀ * y⁻¹) := by group
        _ = r * (r * s₀) := by rw [hfix, h1]
        _ = s₀ := by rw [← mul_assoc, hR2 r hr, one_mul]
  have hyr2 : y * y * r * (y * y)⁻¹ = r := by
    calc y * y * r * (y * y)⁻¹ = y * (y * r * y⁻¹) * y⁻¹ := by group
      _ = r := by rw [hfix, hfix]
  rw [mem_centralizer_iff]
  intro x hx
  have hfx : y * y * x * (y * y)⁻¹ = x := by
    rcases mem_four h.cardR hR2 hr hs₀ hr1 hs₀1 hs₀r.symm hx with rfl | rfl | rfl | rfl
    · group
    · exact hyr2
    · exact hys2
    · calc y * y * (r * s₀) * (y * y)⁻¹ =
          (y * y * r * (y * y)⁻¹) * (y * y * s₀ * (y * y)⁻¹) := by group
        _ = r * s₀ := by rw [hyr2, hys2]
  calc x * (y * y) = y * y * x * (y * y)⁻¹ * (y * y) := by rw [hfx]
    _ = y * y * x := by group

omit [Finite G] h in
theorem transvHom_conj {r₀ : G} (hr₀ : r₀ ∈ R) {b : G} (hbr : b * r₀ = r₀ * b)
    {n : G} (hn : n ∈ transvGroup (R ⊔ T) V₀) (hbn : b * n * b⁻¹ ∈ transvGroup (R ⊔ T) V₀) :
    ((transvHom (T := T) (V₀ := V₀) hr₀ ⟨b * n * b⁻¹, hbn⟩ : ↥V₀) : G) =
      b * ((transvHom (T := T) (V₀ := V₀) hr₀ ⟨n, hn⟩ : ↥V₀) : G) * b⁻¹ := by
  change r₀⁻¹ * (b * n * b⁻¹ * r₀ * (b * n * b⁻¹)⁻¹) = b * (r₀⁻¹ * (n * r₀ * n⁻¹)) * b⁻¹
  have h1 : b⁻¹ * r₀ * b = r₀ := by
    calc b⁻¹ * r₀ * b = b⁻¹ * (r₀ * b) := by group
      _ = b⁻¹ * (b * r₀) := by rw [hbr]
      _ = r₀ := by group
  calc r₀⁻¹ * (b * n * b⁻¹ * r₀ * (b * n * b⁻¹)⁻¹) =
      r₀⁻¹ * (b * n * (b⁻¹ * r₀ * b) * n⁻¹ * b⁻¹) := by group
    _ = b * (b⁻¹ * r₀⁻¹ * b) * n * r₀ * n⁻¹ * b⁻¹ := by rw [h1]; group
    _ = b * (r₀⁻¹ * (n * r₀ * n⁻¹)) * b⁻¹ := by
      have h2 : b⁻¹ * r₀⁻¹ * b = r₀⁻¹ := by
        rw [← inv_inj]
        simpa [mul_assoc] using h1
      rw [h2]
      group

theorem transvHom_eq_iff {r₀ : G} (hr₀ : r₀ ∈ R) (hr₀1 : r₀ ≠ 1)
    (n n' : ↥(transvGroup (R ⊔ T) V₀)) :
    transvHom (T := T) (V₀ := V₀) hr₀ n = transvHom (T := T) (V₀ := V₀) hr₀ n' ↔
      ((n⁻¹ * n' : ↥(transvGroup (R ⊔ T) V₀)) : G) ∈
        centralizer ((R ⊔ T : Subgroup G) : Set G) := by
  rw [← mem_subgroupOf, ← h.ker_transvHom hr₀ hr₀1, MonoidHom.mem_ker, map_mul, map_inv,
    inv_mul_eq_one]

theorem mem_normalizer_V {b : G} (hbR : b ∈ normalizer (R : Set G))
    (hbV₀ : b ∈ normalizer (V₀ : Set G)) : b ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := by
  rw [← h.sup_R_V₀]
  exact mem_normalizer_sup hbR hbV₀

theorem mem_centralizer_R_of_graph {u : G} (hu : u ∈ transvGroup (R ⊔ T) V₀)
    (huC : u ∉ centralizer ((R ⊔ T : Subgroup G) : Set G)) {y : G}
    (hyN : y ∈ normalizer (R : Set G)) (hyV₀ : y ∈ centralizer (V₀ : Set G))
    (hc : (y * u * y⁻¹)⁻¹ * u ∈ centralizer ((R ⊔ T : Subgroup G) : Set G)) :
    y ∈ centralizer (R : Set G) := by
  rw [mem_centralizer_iff]
  intro r hr
  set r' := y⁻¹ * r * y with hr'
  have hr'R : r' ∈ R := by
    have := (mem_normalizer_iff.mp (inv_mem hyN) r).mp hr
    simpa [hr'] using this
  have h1 : u * r * u⁻¹ = y * (u * r' * u⁻¹) * y⁻¹ := by
    obtain ⟨c, hcdef⟩ : ∃ c, (y * u * y⁻¹)⁻¹ * u = c := ⟨_, rfl⟩
    rw [hcdef] at hc
    have hu' : u = (y * u * y⁻¹) * c := by rw [← hcdef]; group
    have hcr : c * r * c⁻¹ = r := by
      rw [← mem_centralizer_iff.mp hc r (mem_sup_left hr)]
      group
    calc u * r * u⁻¹ = (y * u * y⁻¹) * (c * r * c⁻¹) * (y * u * y⁻¹)⁻¹ := by
          conv_lhs => rw [hu']
          group
      _ = (y * u * y⁻¹) * r * (y * u * y⁻¹)⁻¹ := by rw [hcr]
      _ = y * (u * r' * u⁻¹) * y⁻¹ := by rw [hr']; group
  set d := r'⁻¹ * (u * r' * u⁻¹) with hd
  have hdV₀ : d ∈ V₀ := hu.2.2 r' (mem_sup_left hr'R)
  have h2 : u * r' * u⁻¹ = r' * d := by rw [hd]; group
  have hyd : y * d * y⁻¹ = d := by rw [← mem_centralizer_iff.mp hyV₀ d hdV₀]; group
  have h3 : u * r * u⁻¹ = r * d := by
    rw [h1, h2]
    calc y * (r' * d) * y⁻¹ = (y * r' * y⁻¹) * (y * d * y⁻¹) := by group
      _ = r * d := by rw [hyd, hr']; group
  set t := r⁻¹ * r' with ht
  have htR : t ∈ R := mul_mem (inv_mem hr) hr'R
  have hfix : u * t * u⁻¹ = t := by
    calc u * t * u⁻¹ = (u * r * u⁻¹)⁻¹ * (u * r' * u⁻¹) := by rw [ht]; group
      _ = (r * d)⁻¹ * (r' * d) := by rw [h3, h2]
      _ = d⁻¹ * (r⁻¹ * r') * d := by group
      _ = t := by
        rw [← ht, mul_assoc, h.comm (mem_sup_left htR) (h.V₀_le hdV₀), ← mul_assoc,
          inv_mul_cancel, one_mul]
  have htV₀ := h.mem_V₀_of_fixed hu huC (mem_sup_left htR) hfix
  have ht1 : t ∈ R ⊓ V₀ := mem_inf.mpr ⟨htR, htV₀⟩
  rw [h.inf_R_V₀, mem_bot] at ht1
  have hrr : r' = r := by
    calc r' = r * t := by rw [ht]; group
      _ = r := by rw [ht1, mul_one]
  calc r * y = y * (y⁻¹ * r * y) := by group
    _ = y * r := by rw [← hr', hrr]

theorem conj_mem_of_fix {r₀ : G} (hr₀ : r₀ ∈ R) (hr₀1 : r₀ ≠ 1) {t : G}
    (htV : t ∈ normalizer ((R ⊔ T : Subgroup G) : Set G)) (htN₀ : t ∈ normalizer (V₀ : Set G))
    (htodd : Odd (orderOf t)) {u : G} (hu : u ∈ transvGroup (R ⊔ T) V₀)
    (huC : u ∉ centralizer ((R ⊔ T : Subgroup G) : Set G))
    (hfix : u⁻¹ * (t * u * t⁻¹) ∈ centralizer ((R ⊔ T : Subgroup G) : Set G)) :
    ∀ n ∈ transvGroup (R ⊔ T) V₀,
      n⁻¹ * (t * n * t⁻¹) ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
  set P₀ := transvGroup (R ⊔ T) V₀ with hP₀
  set C := centralizer ((R ⊔ T : Subgroup G) : Set G) with hC
  have hV₀2 : ∀ x ∈ V₀, x * x = 1 := fun x hx => h.mul_self (h.V₀_le hx)
  let κ : ↥P₀ →* ↥P₀ :=
    { toFun := fun n => ⟨t * n * t⁻¹, transvGroup_normal htV htN₀ n.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [coe_mul]; group) }
  set f := transvHom (T := T) (V₀ := V₀) hr₀ with hf
  have hfeq := h.transvHom_eq_iff hr₀ hr₀1
  have hf1 : ∀ n : ↥P₀, f n = 1 ↔ (n : G) ∈ C := fun n => by
    rw [← MonoidHom.mem_ker, h.ker_transvHom hr₀ hr₀1, mem_subgroupOf]
  have hκC : ∀ n : ↥P₀, ((κ n : ↥P₀) : G) ∈ C ↔ (n : G) ∈ C := fun n => by
    constructor
    · intro h1
      have := conj_mem_centralizer (inv_mem htV) h1
      simpa [κ, mul_assoc] using this
    · exact conj_mem_centralizer htV
  set ψ := f.comp κ with hψ
  have hψ1 : ∀ n : ↥P₀, ψ n = 1 ↔ f n = 1 := fun n => by
    rw [hf1, ← hκC]
    exact hf1 (κ n)
  have hψf : ∀ n n' : ↥P₀, f n = f n' → ψ n = ψ n' := fun n n' he => by
    have h1 : f (n⁻¹ * n') = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have h2 := (hψ1 _).mpr h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  suffices hsuff : ∀ n : ↥P₀, ψ n = f n by
    intro n hn
    have h1 := hsuff ⟨n, hn⟩
    have h2 := (hfeq ⟨n, hn⟩ ⟨t * n * t⁻¹, transvGroup_normal htV htN₀ hn⟩).mp h1.symm
    simpa using h2
  set u' : ↥P₀ := ⟨u, hu⟩ with hu'
  have hψu : ψ u' = f u' := by
    have h1 := (hfeq u' (κ u')).mpr (by simpa [κ, hu'] using hfix)
    exact h1.symm
  have hu1 : f u' ≠ 1 := fun he => huC ((hf1 u').mp he)
  intro n
  by_cases hn1 : f n = 1
  · rw [hn1, (hψ1 n).mpr hn1]
  by_cases hnu : f n = f u'
  · rw [hψf n u' hnu, hψu, hnu]
  have hψn1 : ψ n ≠ 1 := fun he => hn1 ((hψ1 n).mp he)
  have hψnu : ψ n ≠ f u' := fun he => hnu (by
    have h1 : ψ (n⁻¹ * u') = 1 := by rw [map_mul, map_inv, he, ← hψu, inv_mul_cancel]
    have h2 := (hψ1 _).mp h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2)
  have hw4 := mem_four h.card_V₀ hV₀2 (f u').2 (f n).2 (fun he => hu1 (Subtype.ext he))
    (fun he => hn1 (Subtype.ext he)) (fun he => hnu (Subtype.ext he).symm) (ψ n).2
  rcases hw4 with h1 | h1 | h1 | h1
  · exact absurd (Subtype.ext h1) hψn1
  · exact absurd (Subtype.ext h1) hψnu
  · exact Subtype.ext h1
  ·
    exfalso
    have hψn : ψ n = f u' * f n := Subtype.ext h1
    have hstep : ∀ x : ↥P₀, f x = f n → f (κ (κ x)) = f n := by
      intro x hx
      have h2 : ψ x = f u' * f n := by rw [hψf x n hx, hψn]
      have h3 : f (κ x) = f (u' * n) := by
        change ψ x = _
        rw [h2, map_mul]
      have h4 : ψ (κ x) = ψ (u' * n) := hψf _ _ h3
      change ψ (κ x) = _
      rw [h4, map_mul, hψu, hψn, ← mul_assoc]
      have h5 : f u' * f u' = 1 := Subtype.ext (hV₀2 _ (f u').2)
      rw [h5, one_mul]
    have hpow : ∀ j : ℕ, f (κ^[2 * j] n) = f n := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Function.iterate_succ_apply',
          Function.iterate_succ_apply']
        exact hstep _ ih
    obtain ⟨m, hm⟩ := htodd
    have hκt : ∀ (j : ℕ) (x : ↥P₀), ((κ^[j] x : ↥P₀) : G) = t ^ j * x * (t ^ j)⁻¹ := by
      intro j
      induction j with
      | zero => intro x; simp
      | succ j ih =>
        intro x
        rw [Function.iterate_succ_apply']
        change t * ((κ^[j] x : ↥P₀) : G) * t⁻¹ = _
        rw [ih, pow_succ']
        group
    have hκ1 : κ^[2 * (m + 1)] n = κ n := by
      apply Subtype.ext
      rw [hκt, show 2 * (m + 1) = orderOf t + 1 by omega, pow_succ', pow_orderOf_eq_one]
      change _ = t * n * t⁻¹
      group
    have h2 := hpow (m + 1)
    rw [hκ1] at h2
    change ψ n = f n at h2
    rw [hψn] at h2
    apply hu1
    calc f u' = f u' * f n * (f n)⁻¹ := by group
      _ = 1 := by rw [h2, mul_inv_cancel]

theorem exists_scalar
    (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G)) :
    ∃ t : G, t ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) ∧ t ∈ normalizer (V₀ : Set G) ∧
      (∀ w ∈ V₀, w ≠ 1 → t * w * t⁻¹ ≠ w) ∧
      (∀ v ∈ R ⊔ T, v ∉ V₀ → v⁻¹ * (t * v * t⁻¹) ∉ V₀) ∧
      ∀ n ∈ transvGroup (R ⊔ T) V₀,
        n⁻¹ * (t * n * t⁻¹) ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eA⟩ := h.equiv
  have hV₀2 : ∀ x ∈ V₀, x * x = 1 := fun x hx => h.mul_self (h.V₀_le hx)
  have hR2 : ∀ x ∈ R, x * x = 1 := fun x hx => h.mul_self (mem_sup_left hx)
  have hRc : R ≤ centralizer (R : Set G) := le_centralizer_self_of_isElemAbelian h.elemR
  obtain ⟨y, hy, hyC, hyodd⟩ := exists_odd_of_not_le h.sylowR hRc hIIa
  obtain ⟨hyK, hyN⟩ := mem_inf.mp hy
  have hyV₀ : y ∈ centralizer (V₀ : Set G) := centralizer_le (fun v hv => h.V₀_le_A hv) hyK
  have hyN₀ : y ∈ normalizer (V₀ : Set G) := centralizer_le_normalizer _ hyV₀
  have hyV := h.mem_normalizer_V hyN hyN₀
  obtain ⟨b₀, hb₀A, hb₀N, hb₀3, hb₀tr, -⟩ := exists_klein_three eA h.V₀_le_A h.card_V₀
  have hb₀R : b₀ ∈ centralizer (R : Set G) := le_centralizer_iff.mp h.sylowR.le hb₀A
  have hb₀V := h.mem_normalizer_V (centralizer_le_normalizer _ hb₀R) hb₀N
  have hb₀3' : b₀ ^ 3 = 1 := hb₀3 ▸ pow_orderOf_eq_one b₀
  have hb₀f : ∀ x ∈ V₀, x ≠ 1 → b₀⁻¹ * x * b₀ ≠ x := fun x hx hx1 =>
    conj_ne_of_trans h.card_V₀ hV₀2 hb₀tr hx hx1
  have hyb : b₀ * y = y * b₀ := mem_centralizer_iff.mp hyK b₀ hb₀A
  obtain ⟨u, hu, huC⟩ := h.exists_transv
  obtain ⟨r₀, hr₀, hr₀1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  set f := transvHom (T := T) (V₀ := V₀) hr₀ with hf
  have hfeq := h.transvHom_eq_iff hr₀ hr₀1
  have hu₁ : y * u * y⁻¹ ∈ transvGroup (R ⊔ T) V₀ := transvGroup_normal hyV hyN₀ hu
  have hfne : f ⟨y * u * y⁻¹, hu₁⟩ ≠ f ⟨u, hu⟩ := by
    intro he
    rw [hfeq] at he
    simp only [coe_mul, InvMemClass.coe_inv] at he
    exact hyC (h.mem_centralizer_R_of_graph hu huC hyN hyV₀ he)
  have hf1 : ∀ n : ↥(transvGroup (R ⊔ T) V₀), f n = 1 ↔
      (n : G) ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := fun n => by
    rw [← MonoidHom.mem_ker, h.ker_transvHom hr₀ hr₀1, mem_subgroupOf]
  have hu1 : f ⟨u, hu⟩ ≠ 1 := fun he => huC ((hf1 _).mp he)
  have hu₁1 : f ⟨y * u * y⁻¹, hu₁⟩ ≠ 1 := fun he => huC (by
    have h1 := conj_mem_centralizer (inv_mem hyV) ((hf1 _).mp he)
    simpa [mul_assoc] using h1)
  have hfu₁V : ((f ⟨y * u * y⁻¹, hu₁⟩ : ↥V₀) : G) ∈ V₀ := (f _).2
  have hfuV : ((f ⟨u, hu⟩ : ↥V₀) : G) ∈ V₀ := (f _).2
  obtain ⟨k, hk⟩ := hb₀tr _ hfu₁V _ hfuV (fun he => hu₁1 (Subtype.ext he))
    (fun he => hu1 (Subtype.ext he))
  have hk3 : k % 3 ≠ 0 := by
    intro hk0
    have hbk : b₀ ^ k = 1 := by
      rw [← Nat.div_add_mod k 3, hk0, add_zero, pow_mul, hb₀3', one_pow]
    rw [hbk, inv_one, one_mul, mul_one] at hk
    exact hfne (Subtype.ext hk)
  set t := (b₀ ^ k)⁻¹ * y with ht
  have hbkR : (b₀ ^ k)⁻¹ ∈ centralizer (R : Set G) := inv_mem (pow_mem hb₀R k)
  have hbkV : (b₀ ^ k)⁻¹ ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) :=
    inv_mem (pow_mem hb₀V k)
  have hbkN₀ : (b₀ ^ k)⁻¹ ∈ normalizer (V₀ : Set G) := inv_mem (pow_mem hb₀N k)
  have htV : t ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := mul_mem hbkV hyV
  have htN₀ : t ∈ normalizer (V₀ : Set G) := mul_mem hbkN₀ hyN₀
  have htw : ∀ w ∈ V₀, t * w * t⁻¹ = (b₀ ^ k)⁻¹ * w * b₀ ^ k := by
    intro w hw
    have h1 : y * w * y⁻¹ = w := by rw [← mem_centralizer_iff.mp hyV₀ w hw]; group
    calc t * w * t⁻¹ = (b₀ ^ k)⁻¹ * (y * w * y⁻¹) * b₀ ^ k := by rw [ht]; group
      _ = (b₀ ^ k)⁻¹ * w * b₀ ^ k := by rw [h1]
  refine ⟨t, htV, htN₀, fun w hw hw1 => ?_, fun v hv hv0 => ?_, fun n hn => ?_⟩
  · rw [htw w hw]
    exact pow_conj_ne hb₀3' hb₀f hk3 hw hw1
  ·
    obtain ⟨r, hr, w, hw, rfl⟩ := h.exists_mul hv
    have hr1 : r ≠ 1 := fun he => hv0 (by rw [he, one_mul]; exact hw)
    have hyr : y * r * y⁻¹ ∈ R := (mem_normalizer_iff.mp hyN r).mp hr
    have h1 : t * (r * w) * t⁻¹ = (y * r * y⁻¹) * ((b₀ ^ k)⁻¹ * w * b₀ ^ k) := by
      have h2 : (b₀ ^ k)⁻¹ * (y * r * y⁻¹) * b₀ ^ k = y * r * y⁻¹ := by
        rw [← mem_centralizer_iff.mp hbkR _ hyr]
        group
      calc t * (r * w) * t⁻¹ = ((b₀ ^ k)⁻¹ * (y * r * y⁻¹) * b₀ ^ k) *
            (t * w * t⁻¹) := by rw [ht]; group
        _ = (y * r * y⁻¹) * ((b₀ ^ k)⁻¹ * w * b₀ ^ k) := by rw [h2, htw w hw]
    rw [h1]
    intro hmem
    have hw' : (b₀ ^ k)⁻¹ * w * b₀ ^ k ∈ V₀ := by
      have := (mem_normalizer_iff.mp hbkN₀ w).mp hw
      simpa using this
    have h3 : r⁻¹ * (y * r * y⁻¹) ∈ V₀ := by
      have h4 : (r * w)⁻¹ * ((y * r * y⁻¹) * ((b₀ ^ k)⁻¹ * w * b₀ ^ k)) =
          w⁻¹ * (r⁻¹ * (y * r * y⁻¹)) * ((b₀ ^ k)⁻¹ * w * b₀ ^ k) := by group
      rw [h4] at hmem
      have h6 : r⁻¹ * (y * r * y⁻¹) =
          w * (w⁻¹ * (r⁻¹ * (y * r * y⁻¹)) * ((b₀ ^ k)⁻¹ * w * b₀ ^ k)) *
            ((b₀ ^ k)⁻¹ * w * b₀ ^ k)⁻¹ := by group
      rw [h6]
      exact mul_mem (mul_mem hw hmem) (inv_mem hw')
    have h5 : r⁻¹ * (y * r * y⁻¹) ∈ R ⊓ V₀ := mem_inf.mpr ⟨mul_mem (inv_mem hr) hyr, h3⟩
    rw [h.inf_R_V₀, mem_bot] at h5
    apply h.conj_ne_of_not_mem hyK hyN hyC hr hr1
    calc y * r * y⁻¹ = r * (r⁻¹ * (y * r * y⁻¹)) := by group
      _ = r := by rw [h5, mul_one]
  ·
    have htodd : Odd (orderOf t) := by
      have hcomm : Commute (b₀ ^ k)⁻¹ y := by
        have : Commute b₀ y := hyb
        exact (this.pow_left k).inv_left
      have hb : ((b₀ ^ k)⁻¹) ^ (3 * orderOf y) = 1 := by
        rw [inv_pow, ← pow_mul, show k * (3 * orderOf y) = 3 * (k * orderOf y) by ring, pow_mul,
          hb₀3', one_pow, inv_one]
      have hy3 : y ^ (3 * orderOf y) = 1 := by
        rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
      have h1 : t ^ (3 * orderOf y) = 1 := by rw [ht, hcomm.mul_pow, hb, hy3, one_mul]
      exact (Nat.odd_mul.mpr ⟨by decide, hyodd⟩).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
    have htu : t * u * t⁻¹ = (b₀ ^ k)⁻¹ * (y * u * y⁻¹) * ((b₀ ^ k)⁻¹)⁻¹ := by
      rw [ht]; group
    have htuP : (b₀ ^ k)⁻¹ * (y * u * y⁻¹) * ((b₀ ^ k)⁻¹)⁻¹ ∈ transvGroup (R ⊔ T) V₀ :=
      transvGroup_normal hbkV hbkN₀ hu₁
    have hbr : (b₀ ^ k)⁻¹ * r₀ = r₀ * (b₀ ^ k)⁻¹ := (mem_centralizer_iff.mp hbkR r₀ hr₀).symm
    have h1 := transvHom_conj hr₀ hbr hu₁ htuP
    have h1' : ((f ⟨_, htuP⟩ : ↥V₀) : G) = ((f ⟨u, hu⟩ : ↥V₀) : G) := by
      rw [hf, h1]
      simp only [inv_inv]
      exact hk
    have hfix : u⁻¹ * (t * u * t⁻¹) ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
      have h2 := (hfeq ⟨u, hu⟩ ⟨_, htuP⟩).mp (Subtype.ext h1'.symm)
      rw [htu]
      simpa using h2
    exact h.conj_mem_of_fix hr₀ hr₀1 htV htN₀ htodd hu huC hfix n hn

theorem le_normalizer_transvGroup :
    normalizer ((R ⊔ T : Subgroup G) : Set G) ≤
      normalizer ((transvGroup (R ⊔ T) V₀ : Subgroup G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => transvGroup_normal hn (h.normalizer_le_normalizer_V₀ hn) hx, fun hx => ?_⟩
  have := transvGroup_normal (inv_mem hn) (h.normalizer_le_normalizer_V₀ (inv_mem hn)) hx
  simpa [mul_assoc] using this

theorem exists_scalar_P
    (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
    {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
    (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T) :
    ∃ t : G, t ∈ normalizer (P : Set G) ∧ t ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) ∧
      t ∈ normalizer (V₀ : Set G) ∧ (∀ w ∈ V₀, w ≠ 1 → t * w * t⁻¹ ≠ w) ∧
      (∀ v ∈ R ⊔ T, v ∉ V₀ → v⁻¹ * (t * v * t⁻¹) ∉ V₀) ∧
      ∀ x ∈ P, x⁻¹ * (t * x * t⁻¹) ∈ R ⊔ T := by
  obtain ⟨t, htV, htN₀, htf, htq, htP₀⟩ := h.exists_scalar hIIa
  obtain ⟨p, hp, hpt⟩ := exists_mul_mem_normalizer hP (h.le_normalizer_transvGroup htV)
  obtain ⟨hpV, hpC, hpq⟩ := hp
  have hpw : ∀ w ∈ V₀, p * w * p⁻¹ = w := fun w hw => by
    rw [← mem_centralizer_iff.mp hpC w hw]; group
  refine ⟨p * t, hpt, mul_mem hpV htV, mul_mem (centralizer_le_normalizer _ hpC) htN₀,
    fun w hw hw1 => ?_, fun v hv hv0 => ?_, fun x hx => ?_⟩
  · have htw : t * w * t⁻¹ ∈ V₀ := (mem_normalizer_iff.mp htN₀ w).mp hw
    have h1 : p * t * w * (p * t)⁻¹ = t * w * t⁻¹ := by
      calc p * t * w * (p * t)⁻¹ = p * (t * w * t⁻¹) * p⁻¹ := by group
        _ = t * w * t⁻¹ := hpw _ htw
    rw [h1]
    exact htf w hw hw1
  · intro hmem
    have htv : t * v * t⁻¹ ∈ R ⊔ T := (mem_normalizer_iff.mp htV v).mp hv
    have h1 := hpq _ htv
    apply htq v hv hv0
    have h2 : v⁻¹ * (t * v * t⁻¹) =
        (v⁻¹ * (p * t * v * (p * t)⁻¹)) * ((t * v * t⁻¹)⁻¹ * (p * (t * v * t⁻¹) * p⁻¹))⁻¹ := by
      group
    rw [h2]
    exact mul_mem hmem (inv_mem h1)
  · have hxP₀ : x ∈ transvGroup (R ⊔ T) V₀ := hP.le hx
    have hc := htP₀ x hxP₀
    have hpinv : p⁻¹ ∈ transvGroup (R ⊔ T) V₀ := inv_mem ⟨hpV, hpC, hpq⟩
    have h1 : x⁻¹ * (p * t * x * (p * t)⁻¹) ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
      have h2 : x⁻¹ * (p * t * x * (p * t)⁻¹) =
          (x⁻¹ * p * x * p⁻¹) * (p * (x⁻¹ * (t * x * t⁻¹)) * p⁻¹) := by group
      rw [h2]
      refine mul_mem ?_ (conj_mem_centralizer hpV hc)
      have := h.commutator_mem_centralizer (inv_mem hxP₀) ⟨hpV, hpC, hpq⟩
      simpa [mul_assoc] using this
    have h3 : x⁻¹ * (p * t * x * (p * t)⁻¹) ∈ P :=
      mul_mem (inv_mem hx) ((mem_normalizer_iff.mp hpt x).mp hx)
    rw [← hPC]
    exact mem_inf.mpr ⟨h3, h1⟩

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
