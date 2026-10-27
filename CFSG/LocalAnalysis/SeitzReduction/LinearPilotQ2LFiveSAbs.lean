module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWOne
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G : Type*} [Group G]

section Helpers

theorem conj_conj_of_mul_self {t : G} (ht : t * t = 1) (a : G) :
    t * (t * a * t⁻¹) * t⁻¹ = a := by
  calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t * t)⁻¹ := by group
    _ = a := by rw [ht, inv_one, one_mul, mul_one]

theorem mem_normalizer_of_mul_self_of_conj_mem {H : Subgroup G} {g : G} (hg : g * g = 1)
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h1 := h _ hx
  rwa [conj_conj_of_mul_self hg x] at h1

variable [Finite G] in
theorem two_mul_card_le_of_lt {H H' : Subgroup G} (h : H < H') :
    2 * Nat.card H ≤ Nat.card H' := by
  have hdvd : Nat.card H ∣ Nat.card H' := Subgroup.card_dvd_of_le h.le
  have hlt : Nat.card H < Nat.card H' := Subgroup.card_lt_of_lt h
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra hk2
    interval_cases k <;> simp_all
  rw [hk, mul_comm]
  exact Nat.mul_le_mul_left _ hk2

end Helpers

section Comm

theorem card_le_card_inf_mul_of_tcomm_mem [Finite G] {W B : Subgroup G} {s : G}
    (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (hsW : s ∈ normalizer (W : Set G))
    (hB : ∀ w ∈ W, s * w * s⁻¹ * w⁻¹ ∈ B) :
    Nat.card W ≤ Nat.card (W ⊓ centralizer ({s} : Set G) : Subgroup G) *
      Nat.card (B ⊓ W : Subgroup G) := by
  have hAB : ∀ a ∈ W, s * a * s⁻¹ * a⁻¹ ∈ B ⊓ W := fun a ha =>
    Subgroup.mem_inf.2 ⟨hB a ha, tcomm_mem hsW ha⟩
  set φ := tcommHom (t := s) hWc hsW le_rfl hAB with hφ
  have hker : Nat.card φ.ker = Nat.card (W ⊓ centralizer ({s} : Set G) : Subgroup G) :=
    card_ker_tcommHom hWc hsW le_rfl hAB inf_le_left fun a _ =>
      ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨‹_›, h⟩⟩
  have hW' := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker] at hW'
  rw [hW', mul_comm]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_card_group φ.range)

theorem card_sup_mul_card_inf_of_le_normalizer_sOne {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set G)
  have hAN : A ≤ N := le_normalizer
  have : (A.subgroupOf N).Normal := normal_in_normalizer
  have h1 := relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N ⊔ A.subgroupOf N)
  have h2 := relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N)
  rw [relIndex_sup_right, inf_of_le_left (le_sup_right : A.subgroupOf N ≤ _)] at h1
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (subgroupOf_sup hAN hB).symm
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hc _ (sup_le hAN hB)] at h1
  rw [hinf, hc _ (inf_le_left.trans hAN), hc B hB] at h2
  rw [hc A hAN] at h1
  calc Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G)
      = ((A.subgroupOf N).relIndex (B.subgroupOf N) * Nat.card A) *
          Nat.card (A ⊓ B : Subgroup G) := by rw [h1]
    _ = Nat.card A * ((A.subgroupOf N).relIndex (B.subgroupOf N) *
          Nat.card (A ⊓ B : Subgroup G)) := by ring
    _ = Nat.card A * Nat.card B := by rw [h2]

end Comm

section Sylow

variable [Finite G]

theorem exists_isPGroup_lt_of_card_lt {p : ℕ} [Fact p.Prime] {R S P : Subgroup G}
    (hS : IsPGroup p S) (hSR : S ≤ R) (hP : IsPGroup p P) (hPR : P ≤ R)
    (hlt : Nat.card S < Nat.card P) : ∃ Q : Subgroup G, IsPGroup p Q ∧ S < Q ∧ Q ≤ R := by
  have hS' : IsPGroup p (S.subgroupOf R) := hS.of_equiv (subgroupOfEquivOfLe hSR).symm
  have hP' : IsPGroup p (P.subgroupOf R) := hP.of_equiv (subgroupOfEquivOfLe hPR).symm
  obtain ⟨Q₀, hQ₀⟩ := hS'.exists_le_sylow
  obtain ⟨Q₁, hQ₁⟩ := hP'.exists_le_sylow
  have hc : Nat.card (Q₀ : Subgroup R) = Nat.card (Q₁ : Subgroup R) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hPc : Nat.card P ≤ Nat.card (Q₁ : Subgroup R) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hPR).toEquiv]
    exact Subgroup.card_le_of_le hQ₁
  refine ⟨(Q₀ : Subgroup R).map R.subtype, Q₀.isPGroup'.map _, ?_, map_subtype_le _⟩
  have hle : S ≤ (Q₀ : Subgroup R).map R.subtype := fun x hx =>
    ⟨⟨x, hSR hx⟩, hQ₀ (mem_subgroupOf.2 hx), rfl⟩
  refine lt_of_le_of_ne hle fun heq => ?_
  have h1 : Nat.card ((Q₀ : Subgroup R).map R.subtype) = Nat.card (Q₀ : Subgroup R) :=
    Subgroup.card_map_of_injective R.subtype_injective
  rw [← heq] at h1
  omega

omit [Finite G] in
theorem mem_normalizer_of_mem_normalizer_subgroupOf_sOne {S Q : Subgroup G} (hSQ : S ≤ Q)
    {g : Q} (hg : g ∈ normalizer ((S.subgroupOf Q : Subgroup Q) : Set Q)) :
    (g : G) ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    have h := (hg ⟨x, hSQ hx⟩).1 (mem_subgroupOf.2 hx)
    exact mem_subgroupOf.1 h
  · intro hx
    have hxQ : x ∈ Q := by
      have h1 : (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * g ∈ Q :=
        Q.mul_mem (Q.mul_mem (Q.inv_mem g.2) (hSQ hx)) g.2
      rwa [show (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * g = x by group] at h1
    have h := (hg ⟨x, hxQ⟩).2 (mem_subgroupOf.2 hx)
    exact mem_subgroupOf.1 h

theorem false_of_isPGroup_lt {W V S Q R₀ : Subgroup G} {t : G}
    (hW : ∀ w ∈ W, w * w = 1) (hWV : Nat.card W = Nat.card V ^ 2) (ht : t * t = 1)
    (hWS : W ≤ S) (hSN : S ≤ normalizer (W : Set G)) (htS : t ∈ S)
    (htcomm : ∀ s ∈ S, t * s * t⁻¹ * s⁻¹ ∈ V)
    (hB : ∀ B : Subgroup G, B ≤ S → B ≤ centralizer (V : Set G) → (∀ b ∈ B, b * b = 1) →
      (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) → Nat.card B = Nat.card W → B = W)
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → S ≤ P → P ≤ normalizer (W : Set G) → P = S)
    (hQ : IsPGroup 2 Q) (hSQ : S < Q) (hR₀ : ∀ q ∈ Q, ∀ x ∈ R₀, q * x * q⁻¹ ∈ R₀)
    (htR₀ : t ∉ R₀)
    (hkey : ∀ s ∈ S, s ∉ R₀ → s * s = 1 →
      Nat.card (W ⊓ centralizer ({s} : Set G) : Subgroup G) ≤ Nat.card V) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
  have hnil : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : S.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply ne_of_lt hSQ
    refine le_antisymm hSQ.le fun x hx => ?_
    have h1 : (⟨x, hx⟩ : Q) ∈ S.subgroupOf Q := htop ▸ mem_top _
    exact mem_subgroupOf.1 h1
  obtain ⟨g₀, hg₀N, hg₀S⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  set g : G := (g₀ : G) with hg
  have hgQ : g ∈ Q := g₀.2
  have hgS : g ∉ S := fun h => hg₀S (mem_subgroupOf.2 h)
  have hgNS : g ∈ normalizer (S : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf_sOne hSQ.le hg₀N
  have hgconj : ∀ x ∈ S, g⁻¹ * x * g ∈ S := by
    intro x hx
    have h1 := (mem_normalizer_iff.1 hgNS (g⁻¹ * x * g)).2
    apply h1
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
  set t' : G := g * t * g⁻¹ with ht'
  have ht'S : t' ∈ S := (mem_normalizer_iff.1 hgNS t).1 htS
  have ht'R₀ : t' ∉ R₀ := by
    intro h
    have h1 := hR₀ g⁻¹ (Q.inv_mem hgQ) t' h
    rw [show g⁻¹ * t' * g⁻¹⁻¹ = t by rw [ht']; group] at h1
    exact htR₀ h1
  have ht'2 : t' * t' = 1 := by
    rw [ht', show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ht, mul_one,
      mul_inv_cancel]
  have hkey' := hkey t' ht'S ht'R₀ ht'2
  set B : Subgroup G := V.map (MulAut.conj g).toMonoidHom with hBdef
  have hBt : ∀ w ∈ W, t' * w * t'⁻¹ * w⁻¹ ∈ B := by
    intro w hw
    have h1 := htcomm _ (hgconj w (hWS hw))
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ht']
    group
  have hBc : Nat.card B = Nat.card V :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have h1 := card_le_card_inf_mul_of_tcomm_mem hWc (hSN ht'S) hBt
  have h2 : Nat.card V ≤ Nat.card (B ⊓ W : Subgroup G) := by
    have hVpos : 0 < Nat.card V := Nat.card_pos
    have h3 := h1.trans (Nat.mul_le_mul_right _ hkey')
    rw [hWV, sq] at h3
    exact Nat.le_of_mul_le_mul_left h3 hVpos
  have hBW : B ≤ W := by
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : B ⊓ W ≤ B) (by rw [hBc]; exact h2)
    rw [← heq]
    exact inf_le_right
  set B' : Subgroup G := W.map (MulAut.conj g⁻¹).toMonoidHom with hB'def
  have hB'S : B' ≤ S := by
    rintro _ ⟨w, hw, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hgconj w (hWS hw)
  have hB'V : B' ≤ centralizer (V : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_centralizer_iff]
    intro v hv
    have hvB : g * v * g⁻¹ ∈ W := hBW ⟨v, hv, rfl⟩
    have h3 := hWc _ hw _ hvB
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc v * (g⁻¹ * w * g) = g⁻¹ * ((g * v * g⁻¹) * w) * g := by group
      _ = g⁻¹ * (w * (g * v * g⁻¹)) * g := by rw [h3]
      _ = g⁻¹ * w * g * v := by group
  have hB'c : ∀ b ∈ B', ∀ b' ∈ B', b * b' = b' * b := by
    rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g⁻¹ * w * g⁻¹⁻¹ * (g⁻¹ * w' * g⁻¹⁻¹) = g⁻¹ * (w * w') * g := by group
      _ = g⁻¹ * (w' * w) * g := by rw [hWc w hw w' hw']
      _ = g⁻¹ * w' * g⁻¹⁻¹ * (g⁻¹ * w * g⁻¹⁻¹) := by group
  have hB'card : Nat.card B' = Nat.card W :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hB'2 : ∀ b ∈ B', b * b = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g⁻¹ * w * g⁻¹⁻¹ * (g⁻¹ * w * g⁻¹⁻¹) = g⁻¹ * (w * w) * g by group, hW w hw, mul_one,
      inv_mul_cancel]
  have hB'W := hB B' hB'S hB'V hB'2 hB'c hB'card
  have hgW : g ∈ normalizer (W : Set G) := by
    refine inv_mem_iff.1 (mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · have h3 : g⁻¹ * x * g ∈ B' := ⟨x, hx, by simp⟩
      rw [hB'W] at h3
      simpa using h3
    · have h3 : g⁻¹ * x * g⁻¹⁻¹ ∈ B' := by rw [hB'W]; exact hx
      obtain ⟨w, hw, hwx⟩ := h3
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hwx
      have : w = x := by
        have h4 := congrArg (fun y => g * y * g⁻¹) hwx
        rwa [show g * (g⁻¹ * w * g) * g⁻¹ = w by group,
          show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h4
      rw [← this]
      exact hw
  have hP := hmax (S ⊔ zpowers g) (hQ.to_le (sup_le hSQ.le ((zpowers_le).2 hgQ))) le_sup_left
    (sup_le hSN ((zpowers_le).2 hgW))
  exact hgS (hP ▸ mem_sup_right (mem_zpowers g))

end Sylow

section Normalized

variable [Finite G]

theorem exists_isPGroup_sup_normalizer {C T S' : Subgroup G} (hT : IsPGroup 2 T)
    (hTC : T ≤ normalizer (C : Set G)) (hS' : IsPGroup 2 S') (hS'C : S' ≤ C) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ C ⊔ T ∧
      Nat.card S' * Nat.card T ≤ Nat.card P * Nat.card (C ⊓ T : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : T →* MulAut C := C.normalizerMonoidHom.comp (Subgroup.inclusion hTC)
  let _ : MulDistribMulAction T C := MulDistribMulAction.compHom C φ
  let _ : MulAction T (Sylow 2 C) := Sylow.pointwiseMulAction
  have hcard : ¬ 2 ∣ Nat.card (Sylow 2 C) := by
    intro h
    have h1 := card_sylow_modEq_one 2 C
    have h2 : Nat.card (Sylow 2 C) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.ModEq, h2] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨Q₀, hQ₀⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 C) hcard
  set Q : Subgroup G := (Q₀ : Subgroup C).map C.subtype with hQ
  have hQC : Q ≤ C := map_subtype_le _
  have hQp : IsPGroup 2 Q := Q₀.isPGroup'.map _
  have hTQ : T ≤ normalizer (Q : Set G) := by
    rw [le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    have hfix : (⟨b, hb⟩ : T) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
    have hmem : (⟨b, hb⟩ : T) • y ∈ (Q₀ : Subgroup C) := by
      have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : T) (Q₀ : Subgroup C) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    refine ⟨_, hmem, ?_⟩
    change (((C.normalizerMonoidHom) (Subgroup.inclusion hTC ⟨b, hb⟩)) y : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hS'Q : Nat.card S' ≤ Nat.card Q := by
    have hS'' : IsPGroup 2 (S'.subgroupOf C) := hS'.of_equiv (subgroupOfEquivOfLe hS'C).symm
    obtain ⟨Q₁, hQ₁⟩ := hS''.exists_le_sylow
    have hc : Nat.card (Q₁ : Subgroup C) = Nat.card (Q₀ : Subgroup C) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    rw [← Nat.card_congr (subgroupOfEquivOfLe hS'C).toEquiv, hQ,
      Subgroup.card_map_of_injective C.subtype_injective, ← hc]
    exact Subgroup.card_le_of_le hQ₁
  refine ⟨Q ⊔ T, IsPGroup.to_sup_of_normal_left' hQp hT hTQ, sup_le (hQC.trans le_sup_left)
    le_sup_right, ?_⟩
  have h1 := card_sup_mul_card_inf_of_le_normalizer_sOne hTQ
  have h2 : Nat.card (Q ⊓ T : Subgroup G) ≤ Nat.card (C ⊓ T : Subgroup G) :=
    Subgroup.card_le_of_le (inf_le_inf_right T hQC)
  calc Nat.card S' * Nat.card T ≤ Nat.card Q * Nat.card T := Nat.mul_le_mul_right _ hS'Q
    _ = Nat.card (Q ⊔ T : Subgroup G) * Nat.card (Q ⊓ T : Subgroup G) := h1.symm
    _ ≤ Nat.card (Q ⊔ T : Subgroup G) * Nat.card (C ⊓ T : Subgroup G) :=
      Nat.mul_le_mul_left _ h2

end Normalized

section Key

variable [Finite G]

theorem card_inf_centralizer_mul_le_card_mul {W B : Subgroup G} {t h : G}
    (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1) (htW : t ∈ normalizer (W : Set G))
    (hhW : h ∈ normalizer (W : Set G)) (hh : h * h = 1)
    (hB : ∀ w ∈ W, h * w * h⁻¹ * w⁻¹ ∈ B) :
    Nat.card (W ⊓ centralizer ({h * t} : Set G) : Subgroup G) ≤
      Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) : Subgroup G) *
        Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) ⊓ B :
          Subgroup G) := by
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
  have hhi : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  have hconj : ∀ w, w ∈ centralizer ({h * t} : Set G) → t * w * t⁻¹ = h⁻¹ * w * h := by
    intro w hw
    rw [mem_centralizer_singleton_iff] at hw
    calc t * w * t⁻¹ = h⁻¹ * ((h * t) * w) * t⁻¹ := by group
      _ = h⁻¹ * (w * (h * t)) * t⁻¹ := by rw [hw]
      _ = h⁻¹ * w * h := by group
  have hAB : ∀ a ∈ W ⊓ centralizer ({h * t} : Set G), t * a * t⁻¹ * a⁻¹ ∈
      W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) ⊓ B := by
    intro a ha
    obtain ⟨haW, hat⟩ := Subgroup.mem_inf.1 ha
    have he : t * a * t⁻¹ * a⁻¹ = h * a * h⁻¹ * a⁻¹ := by
      rw [hconj a hat, hhi]
    have hxW : h * a * h⁻¹ * a⁻¹ ∈ W := tcomm_mem hhW haW
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨tcomm_mem htW haW,
      tcomm_mem_centralizer hW ht htW haW⟩, ?_⟩, he ▸ hB a haW⟩
    rw [he, mem_centralizer_singleton_iff]
    have hx2 : (h * a * h⁻¹ * a⁻¹)⁻¹ = h * a * h⁻¹ * a⁻¹ :=
      inv_eq_of_mul_eq_one_right (hW _ hxW)
    calc h * a * h⁻¹ * a⁻¹ * h = (h * a * h⁻¹ * a⁻¹)⁻¹ * h := by rw [hx2]
      _ = a * h * a⁻¹ := by group
      _ = a * h⁻¹ * a⁻¹ := by rw [hhi]
      _ = (h * h) * a * h⁻¹ * a⁻¹ := by rw [hh, one_mul]
      _ = h * (h * a * h⁻¹ * a⁻¹) := by group
  set φ := tcommHom hWc htW inf_le_left hAB with hφ
  have hCA : W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) ≤
      W ⊓ centralizer ({h * t} : Set G) := by
    intro a ha
    obtain ⟨ha1, hah⟩ := Subgroup.mem_inf.1 ha
    obtain ⟨haW, hat⟩ := Subgroup.mem_inf.1 ha1
    refine Subgroup.mem_inf.2 ⟨haW, ?_⟩
    rw [mem_centralizer_singleton_iff] at hat hah ⊢
    calc a * (h * t) = (a * h) * t := by group
      _ = (h * a) * t := by rw [hah]
      _ = h * (a * t) := by group
      _ = h * (t * a) := by rw [hat]
      _ = h * t * a := by group
  have hker : Nat.card φ.ker =
      Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) : Subgroup G) := by
    refine card_ker_tcommHom hWc htW inf_le_left hAB hCA fun a ha => ⟨fun h1 => h1.1.2, ?_⟩
    intro hat
    obtain ⟨haW, haht⟩ := Subgroup.mem_inf.1 ha
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨haW, hat⟩, ?_⟩
    rw [mem_centralizer_singleton_iff] at hat haht ⊢
    have h1 : a * h * t = h * a * t := by
      calc a * h * t = a * (h * t) := by group
        _ = h * t * a := haht
        _ = h * (t * a) := by group
        _ = h * (a * t) := by rw [hat]
        _ = h * a * t := by group
    exact mul_right_cancel h1
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker] at hcard
  rw [hcard, mul_comm]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_card_group φ.range)

theorem card_mul_card_le_sq_of_inv {W : Subgroup G} {x y : G} (hW : ∀ w ∈ W, w * w = 1)
    (hxW : x ∈ normalizer (W : Set G)) (hyW : y ∈ normalizer (W : Set G)) (hx : x * x = 1)
    (hy : y ^ 3 = 1) (hxy : x * y * x⁻¹ = y⁻¹)
    (hCy : W ⊓ centralizer ({y} : Set G) ≤ centralizer ({x} : Set G)) :
    Nat.card W * Nat.card (W ⊓ centralizer ({y} : Set G) : Subgroup G) ≤
      Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 := by
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
  have hyy : y * y = y⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hy, pow_three, mul_assoc]
  have hAB : ∀ a ∈ W, x * a * x⁻¹ * a⁻¹ ∈ W ⊓ centralizer ({x} : Set G) := fun a ha =>
    Subgroup.mem_inf.2 ⟨tcomm_mem hxW ha, tcomm_mem_centralizer hW hx hxW ha⟩
  set φ := tcommHom (t := x) hWc hxW le_rfl hAB with hφ
  have hker : Nat.card φ.ker = Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    card_ker_tcommHom hWc hxW le_rfl hAB inf_le_left fun a _ =>
      ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨‹_›, h⟩⟩
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker] at hcard
  set M : Subgroup G := φ.range.map (W ⊓ centralizer ({x} : Set G)).subtype with hM
  have hMc : Nat.card M = Nat.card φ.range :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hMC : M ≤ W ⊓ centralizer ({x} : Set G) := map_subtype_le _
  have hMy : M ⊓ (W ⊓ centralizer ({y} : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzM, hzWy⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨_, ⟨w, rfl⟩, rfl⟩ := hzM
    have hvy0 : x * (w : G) * x⁻¹ * (w : G)⁻¹ ∈ centralizer ({y} : Set G) :=
      (Subgroup.mem_inf.1 hzWy).2
    rw [Subgroup.mem_bot]
    change x * (w : G) * x⁻¹ * (w : G)⁻¹ = 1
    have hw := w.2
    set v : G := x * (w : G) * x⁻¹ * (w : G)⁻¹ with hv
    have hvW' : v ∈ W := tcomm_mem hxW hw
    have hvy := mem_centralizer_singleton_iff.1 hvy0
    have hyv : y * v * y⁻¹ = v := by rw [← hvy, mul_inv_cancel_right]
    have hyv' : y⁻¹ * v * y = v := by
      calc y⁻¹ * v * y = y⁻¹ * (v * y) := by group
        _ = y⁻¹ * (y * v) := by rw [hvy]
        _ = v := by group
    set a : G := y * (w : G) * y⁻¹ with ha
    set b : G := y⁻¹ * (w : G) * y with hb
    have haW : a ∈ W := (mem_normalizer_iff.1 hyW _).1 hw
    have hbW : b ∈ W := by
      have h1 := (mem_normalizer_iff.1 (inv_mem hyW) (w : G)).1 hw
      rwa [inv_inv] at h1
    set w' : G := (w : G) * a * b with hw'
    have hw'W : w' ∈ W := W.mul_mem (W.mul_mem hw haW) hbW
    have hw'y : w' ∈ centralizer ({y} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have e1 : y * a * y⁻¹ = b := by
        rw [ha, hb, show y * (y * (w : G) * y⁻¹) * y⁻¹ = (y * y) * w * (y * y)⁻¹ by group, hyy,
          inv_inv]
      have e2 : y * b * y⁻¹ = (w : G) := by rw [hb]; group
      have h1 : y * w' * y⁻¹ = a * b * w := by
        rw [hw', show y * ((w : G) * a * b) * y⁻¹ =
          (y * w * y⁻¹) * (y * a * y⁻¹) * (y * b * y⁻¹) by group, e1, e2]
      have h2 : a * b * (w : G) = w' := by
        rw [hw', hWc _ (W.mul_mem haW hbW) _ hw]
        group
      calc w' * y = (y * w' * y⁻¹)⁻¹⁻¹ * y := by rw [h1, h2, inv_inv]
        _ = y * w' := by group
    have hxw' : x * w' * x⁻¹ = w' := by
      have h1 := mem_centralizer_singleton_iff.1 (hCy (Subgroup.mem_inf.2 ⟨hw'W, hw'y⟩))
      rw [← h1, mul_inv_cancel_right]
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have hyx : x * y⁻¹ * x⁻¹ = y := by
      rw [show x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ by group, hxy, inv_inv]
    have hu : x * (w : G) * x⁻¹ = v * w := by rw [hv]; group
    have ea : x * a * x⁻¹ = y⁻¹ * (v * w) * y := by
      rw [ha, show x * (y * (w : G) * y⁻¹) * x⁻¹ =
        (x * y * x⁻¹) * (x * w * x⁻¹) * (x * y⁻¹ * x⁻¹) by group, hxy, hyx, hu]
    have eb : x * b * x⁻¹ = y * (v * w) * y⁻¹ := by
      rw [hb, show x * (y⁻¹ * (w : G) * y) * x⁻¹ =
        (x * y⁻¹ * x⁻¹) * (x * w * x⁻¹) * (x * y * x⁻¹) by group, hxy, hyx, hu]
    have ea' : y⁻¹ * (v * w) * y = v * b := by
      rw [hb, show y⁻¹ * (v * (w : G)) * y = (y⁻¹ * v * y) * (y⁻¹ * w * y) by group, hyv']
    have eb' : y * (v * w) * y⁻¹ = v * a := by
      rw [ha, show y * (v * (w : G)) * y⁻¹ = (y * v * y⁻¹) * (y * w * y⁻¹) by group, hyv]
    have hv2 : v * v = 1 := hW v hvW'
    have hcomp : x * w' * x⁻¹ = v * w' := by
      rw [hw', show x * ((w : G) * a * b) * x⁻¹ =
        (x * w * x⁻¹) * (x * a * x⁻¹) * (x * b * x⁻¹) by group, hu, ea, eb, ea', eb']
      have c1 : (w : G) * (v * b) = v * ((w : G) * b) := by
        rw [← mul_assoc, hWc _ hw _ hvW', mul_assoc]
      have c2 : b * (v * a) = v * (b * a) := by
        rw [← mul_assoc, hWc _ hbW _ hvW', mul_assoc]
      have c3 : b * a = a * b := hWc _ hbW _ haW
      calc v * (w : G) * (v * b) * (v * a) = v * ((w : G) * (v * b)) * (v * a) := by group
        _ = v * (v * ((w : G) * b)) * (v * a) := by rw [c1]
        _ = (v * v) * ((w : G) * (b * (v * a))) := by group
        _ = (v * v) * ((w : G) * (v * (b * a))) := by rw [c2]
        _ = (v * v) * ((w : G) * (v * (a * b))) := by rw [c3]
        _ = (v * v) * (((w : G) * v) * (a * b)) := by group
        _ = (v * v) * ((v * (w : G)) * (a * b)) := by rw [hWc _ hw _ hvW']
        _ = (v * v) * v * ((w : G) * a * b) := by group
        _ = v * ((w : G) * a * b) := by rw [hv2, one_mul]
    rw [hxw'] at hcomp
    have h3 : v * w' = 1 * w' := by rw [← hcomp, one_mul]
    exact mul_right_cancel h3
  have hcommM : W ⊓ centralizer ({y} : Set G) ≤ normalizer (M : Set G) := by
    rw [le_normalizer_iff]
    intro a ha m hm
    have h1 := hWc a (Subgroup.mem_inf.1 ha).1 m (Subgroup.mem_inf.1 (hMC hm)).1
    rw [h1, mul_inv_cancel_right]
    exact hm
  have h1 := card_sup_mul_card_inf_of_le_normalizer_sOne hcommM
  rw [hMy, Subgroup.card_bot, mul_one] at h1
  have h2 : Nat.card (M ⊔ (W ⊓ centralizer ({y} : Set G)) : Subgroup G) ≤
      Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le (sup_le hMC (le_inf inf_le_left hCy))
  rw [h1, hMc] at h2
  calc Nat.card W * Nat.card (W ⊓ centralizer ({y} : Set G) : Subgroup G)
      = Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) *
          (Nat.card φ.range * Nat.card (W ⊓ centralizer ({y} : Set G) : Subgroup G)) := by
        rw [hcard]; ring
    _ ≤ Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) *
          Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) := Nat.mul_le_mul_left _ h2
    _ = _ := (sq _).symm

end Key

end CFSG.SeitzReduction.LinearPilot
