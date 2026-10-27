module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Conj
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Choice

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

namespace Six

omit [Finite X] in
theorem mem_closure_pair_cases {a b w : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : b * a = a * b) (hw : w ∈ closure ({a, b} : Set X)) :
    w = 1 ∨ w = a ∨ w = b ∨ w = a * b := by
  have h1 : ∀ v, a * (a * v) = v := fun v => by rw [← mul_assoc, ha, one_mul]
  have h2 : ∀ v, b * (b * v) = v := fun v => by rw [← mul_assoc, hb, one_mul]
  have h3 : ∀ v, b * (a * v) = a * (b * v) := fun v => by rw [← mul_assoc, hab, mul_assoc]
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  induction hw using Subgroup.closure_induction with
  | mem v hv =>
    rcases hv with hv | hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr (Or.inl hv))
  | one => exact Or.inl rfl
  | mul u v _ _ hu hv =>
    rcases hu with hu | hu | hu | hu <;> rcases hv with hv | hv | hv | hv <;> rw [hu, hv] <;>
      simp only [mul_assoc, one_mul, mul_one, ha, hb, hab, h1, h3, true_or, or_true]
  | inv u _ hu =>
    rcases hu with hu | hu | hu | hu <;> rw [hu] <;>
      simp only [inv_one, ha', hb', mul_inv_rev, hab, true_or, or_true]

omit [Finite X] in
theorem mem_normalizer_conjugate_of {B : Subgroup X} {g y : X}
    (hg : y * g * y⁻¹ ∈ normalizer (B : Set X)) : g ∈ normalizer (conjugate B y : Set X) := by
  rw [mem_normalizer_iff]
  intro z
  rw [mem_conjugate_iff, mem_conjugate_iff,
    show y * (g * z * g⁻¹) * y⁻¹ = (y * g * y⁻¹) * (y * z * y⁻¹) * (y * g * y⁻¹)⁻¹ by group]
  exact mem_normalizer_iff.mp hg _

omit [Finite X] in
theorem mem_normalizer_inf {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff]
  intro z
  rw [mem_inf, mem_inf]
  exact and_congr (mem_normalizer_iff.mp hA z) (mem_normalizer_iff.mp hB z)

omit [Finite X] in
theorem centralizer_le_normalizer_of_normal {a : X} {J : Subgroup X}
    (hJa : J ≤ centralizer ({a} : Set X))
    (hJn : (J.subgroupOf (centralizer ({a} : Set X))).Normal) :
    centralizer ({a} : Set X) ≤ normalizer (J : Set X) := by
  have hn := (normal_subgroupOf_iff hJa).mp hJn
  intro g hg
  rw [mem_normalizer_iff]
  intro n
  refine ⟨fun hn' => hn n g hn' hg, fun hn' => ?_⟩
  have := hn _ g⁻¹ hn' (inv_mem hg)
  rwa [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at this

omit [Finite X] in
theorem conjugate_coreActionKernel {J : Subgroup X} {c : X} (hc : c ∈ normalizer (J : Set X)) :
    conjugate (coreActionKernel J) c = coreActionKernel J := by
  apply le_antisymm
  · rintro _ ⟨k, hk, rfl⟩
    have := conj_mem_coreActionKernel hc hk
    simpa [MulAut.conj_apply] using this
  · intro k hk
    rw [mem_conjugate_iff]
    have := conj_mem_coreActionKernel (inv_mem hc) hk
    rwa [inv_inv] at this

end Six

namespace Hyp52

variable {h : Hyp52 X}

theorem IsX0Min.commutator_mem_T {y : X} (hy : h.IsX0Min y) {s : X} (hs : s ∈ h.S) :
    ⁅y, s⁆ ∈ h.T := by
  obtain ⟨hyU, hyT, -⟩ := hy
  obtain ⟨hnot, hmin⟩ := h.x0Index_spec ⟨_, fun hle => hyT (hle hyU)⟩
  have hi0 : h.x0Index ≠ 0 := by
    intro h0
    apply hnot
    rw [h0, upperP, upperS_zero, bot_inf_eq]
    exact bot_le
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  rw [hj] at hyU
  apply hmin j (by omega)
  exact mem_inf.mpr ⟨(h.commutator_mem_upperS (mem_inf.mp hyU).1 hs).1,
    (h.commutator_mem_P (mem_inf.mp hyU).2 hs).1⟩

theorem IsX0Min.inv {y : X} (hy : h.IsX0Min y) : h.IsX0Min y⁻¹ := by
  refine ⟨inv_mem hy.1, fun h1 => hy.2.1 ?_, ?_⟩
  · simpa using inv_mem h1
  · rw [inv_pow]
    exact inv_mem hy.2.2

theorem IsX0Min.mem_normalizer_Q {y : X} (hy : h.IsX0Min y) : y ∈ normalizer (h.Q : Set X) := by
  have key : ∀ {z : X}, h.IsX0Min z → ∀ q ∈ h.Q, z * q * z⁻¹ ∈ h.Q := by
    intro z hz q hq
    have hc := hz.commutator_mem_T (mem_inf.mp hq).1
    have heq : z * q * z⁻¹ = ⁅z, q⁆ * q := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact mul_mem (mem_inf.mp hc).1 hq
  rw [mem_normalizer_iff]
  intro q
  refine ⟨key hy q, fun hq => ?_⟩
  have := key hy.inv _ hq
  rwa [show y⁻¹ * (y * q * y⁻¹) * y⁻¹⁻¹ = q by group] at this

theorem IsX0Min.Q_le_normalizer_B0 {y : X} (hy : h.IsX0Min y) :
    h.Q ≤ normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X) := by
  intro q hq
  refine Six.mem_normalizer_inf (mem_inf.mp hq).2 (Six.mem_normalizer_conjugate_of ?_)
  exact (mem_inf.mp ((mem_normalizer_iff.mp hy.mem_normalizer_Q q).mp hq)).2

theorem IsX0Min.mem_normalizer_B0 {y : X} (hy : h.IsX0Min y) :
    y ∈ normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X) := by
  have hy2 : y ^ 2 ∈ normalizer (h.B : Set X) := (mem_inf.mp (mem_inf.mp hy.2.2).1).2
  rw [mem_normalizer_iff]
  intro z
  rw [mem_inf, mem_inf, mem_conjugate_iff, mem_conjugate_iff,
    show y * (y * z * y⁻¹) * y⁻¹ = y ^ 2 * z * (y ^ 2)⁻¹ by rw [pow_two]; group]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (mem_normalizer_iff.mp hy2 z).mp h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_normalizer_iff.mp hy2 z).mpr h2, h1⟩

theorem IsX0Min.commutator_ne_bot {y : X} (hy : h.IsX0Min y) : ⁅h.B, zpowers y⁆ ≠ ⊥ := by
  intro hbot
  have hcomm : ∀ β ∈ h.B, β * y = y * β := by
    intro β hβ
    have h1 : ⁅β, y⁆ ∈ ⁅h.B, zpowers y⁆ := commutator_mem_commutator hβ (mem_zpowers y)
    rw [hbot, mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  apply hy.2.1
  have hyP : y ∈ h.P := (mem_inf.mp hy.1).2
  refine mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hyP).1, ?_⟩, hyP⟩
  rw [mem_normalizer_iff]
  intro β
  constructor
  · intro hβ
    rw [← hcomm β hβ, mul_inv_cancel_right]
    exact hβ
  · intro hβ
    have h1 := hcomm _ hβ
    have h2 : β = y⁻¹ * (y * β * y⁻¹) * y := by group
    rw [h2, mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hβ

end Hyp52

namespace Six

variable {h : Hyp52 X}

omit [Finite X] in
theorem card_subgroupOf_eq (A C : Subgroup X) : Nat.card (A.subgroupOf C) = Nat.card ↥(A ⊓ C) := by
  rw [← inf_subgroupOf_right]
  exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv

theorem sylow_centralizer_zpowers
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X))) :
    ∃ R : Sylow 2 ↥(centralizer (zpowers h.a : Set X)),
      (R : Subgroup _) = (h.S ⊓ centralizer (zpowers h.a : Set X)).subgroupOf
        (centralizer (zpowers h.a : Set X)) := by
  have heq : centralizer (zpowers h.a : Set X) = centralizer ({h.a} : Set X) :=
    centralizer_zpowers_eq h.a
  have hSC : h.S ≤ centralizer ({h.a} : Set X) := h.S_le.trans inf_le_left
  rw [heq, inf_eq_left.mpr hSC]
  exact hSa

theorem sylow_centralizer_closure_pair
    (hJn : (h.J.subgroupOf (centralizer ({h.a} : Set X))).Normal)
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    (hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a) {b : X} (hbP : b ∈ h.P)
    (hb1 : b ≠ 1) (hba : b ≠ h.a)
    (hidx : ((centralizer ({b} : Set X)).subgroupOf h.S).index = 2) :
    ∃ R : Sylow 2 ↥(centralizer (closure {h.a, b} : Set X)),
      (R : Subgroup _) = (h.S ⊓ centralizer (closure {h.a, b} : Set X)).subgroupOf
        (centralizer (closure {h.a, b} : Set X)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizer (closure {h.a, b} : Set X) with hY
  have hYmem : ∀ g, g ∈ Y ↔ h.a * g = g * h.a ∧ b * g = g * b := by
    intro g
    rw [hY, centralizer_closure, mem_centralizer_iff]
    constructor
    · intro hg
      exact ⟨hg _ (by simp), hg _ (by simp)⟩
    · rintro ⟨h1, h2⟩ w hw
      rcases hw with rfl | rfl
      · exact h1
      · exact h2
  have hSC : h.S ≤ centralizer ({h.a} : Set X) := h.S_le.trans inf_le_left
  have hbS : b ∈ h.S := (mem_inf.mp hbP).1
  have hS2 : IsPGroup 2 h.S := by
    obtain ⟨R, hR⟩ := h.S_sylow
    have h1 : IsPGroup 2 (h.S.subgroupOf (centralizer ({h.a} : Set X) ⊓
        normalizer (h.J : Set X))) := hR ▸ R.isPGroup'
    have h2 := h1.map (centralizer ({h.a} : Set X) ⊓ normalizer (h.J : Set X)).subtype
    rwa [map_subgroupOf_eq_of_le h.S_le] at h2
  set C₀ := h.S ⊓ Y with hC₀
  have hC₀b : C₀ = h.S ⊓ centralizer ({b} : Set X) := by
    ext g
    rw [mem_inf, mem_inf, hYmem, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hg, -, h2⟩
      exact ⟨hg, h2.symm⟩
    · rintro ⟨hg, h2⟩
      exact ⟨hg, (mem_centralizer_singleton_iff.mp (hSC hg)).symm, h2.symm⟩
  have hC₀Y : C₀ ≤ Y := inf_le_right
  have hC₀2 : IsPGroup 2 (C₀.subgroupOf Y) := (hS2.to_le inf_le_left).comap_subtype
  obtain ⟨R, hR⟩ := hC₀2.exists_le_sylow
  set R₀ := (R : Subgroup Y).map Y.subtype with hR₀
  have hR₀Y : R₀ ≤ Y := map_subtype_le _
  have hC₀R₀ : C₀ ≤ R₀ := by
    intro g hg
    exact ⟨⟨g, hC₀Y hg⟩, hR (mem_subgroupOf.mpr hg), rfl⟩
  have hR₀2 : IsPGroup 2 R₀ := R.isPGroup'.map _
  have hR₀a : R₀ ≤ centralizer ({h.a} : Set X) := by
    intro g hg
    exact mem_centralizer_singleton_iff.mpr ((hYmem g).mp (hR₀Y hg)).1.symm
  obtain ⟨d, hd, hdS⟩ := exists_conjugate_le_of_sylow hSa hR₀a hR₀2
  have hdJ : d ∈ normalizer (h.J : Set X) :=
    centralizer_le_normalizer_of_normal h.J_le hJn hd
  have hab : b * h.a = h.a * b := comm_a hC hbS
  have hbC₀ : b ∈ C₀ := mem_inf.mpr ⟨hbS, (hYmem b).mpr ⟨hab.symm, rfl⟩⟩
  have hbR₀ := hC₀R₀ hbC₀
  set b' := d⁻¹ * b * d with hb'
  have hb'S : b' ∈ h.S := hdS (by
    rw [mem_conjugate_iff, show d * (d⁻¹ * b * d) * d⁻¹ = b by group]
    exact hbR₀)
  have hb'C : b' ∈ coreActionKernel h.J := conj_mem_coreActionKernel hdJ (mem_inf.mp hbP).2
  have hR₀d : conjugate R₀ d ≤ h.S ⊓ centralizer ({b'} : Set X) := by
    intro g hg
    refine mem_inf.mpr ⟨hdS hg, ?_⟩
    rw [mem_conjugate_iff] at hg
    have h1 := ((hYmem _).mp (hR₀Y hg)).2
    rw [mem_centralizer_singleton_iff, hb']
    calc g * (d⁻¹ * b * d) = d⁻¹ * ((d * g * d⁻¹) * b) * d := by group
      _ = d⁻¹ * (b * (d * g * d⁻¹)) * d := by rw [← h1]
      _ = d⁻¹ * b * d * g := by group
  have hcard_le : Nat.card R₀ ≤ Nat.card C₀ := by
    by_contra hlt
    push Not at hlt
    have hS_card : Nat.card C₀ * 2 = Nat.card h.S := by
      have h1 := card_mul_index ((centralizer ({b} : Set X)).subgroupOf h.S)
      rw [hidx, card_subgroupOf_eq] at h1
      rw [hC₀b, inf_comm]
      exact h1
    have hc1 : Nat.card C₀ < Nat.card ↥(h.S ⊓ centralizer ({b'} : Set X)) := by
      calc Nat.card C₀ < Nat.card R₀ := hlt
        _ = Nat.card (conjugate R₀ d) := (GSLit.card_conjugate R₀ d).symm
        _ ≤ _ := card_le_of_le hR₀d
    have hdvd : Nat.card ↥(h.S ⊓ centralizer ({b'} : Set X)) ∣ Nat.card h.S :=
      card_dvd_of_le inf_le_left
    have heq : Nat.card ↥(h.S ⊓ centralizer ({b'} : Set X)) = Nat.card h.S := by
      obtain ⟨t, ht⟩ := hdvd
      have hpos : 0 < Nat.card ↥(h.S ⊓ centralizer ({b'} : Set X)) := Nat.card_pos
      rcases t with _ | _ | t
      · rw [mul_zero] at ht
        exact absurd ht Nat.card_pos.ne'
      · rw [ht]
        ring
      · exfalso
        rw [← hS_card] at ht
        nlinarith
    have hSle : h.S ≤ centralizer ({b'} : Set X) :=
      (eq_of_le_of_card_ge inf_le_left heq.ge ▸ inf_le_right :)
    have hb'Z : b' ∈ h.P ⊓ centralizer (h.S : Set X) := by
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨hb'S, hb'C⟩, mem_centralizer_iff.mpr fun s hs => ?_⟩
      exact mem_centralizer_singleton_iff.mp (hSle hs)
    rw [hC] at hb'Z
    rcases eq_one_or_eq_a hb'Z with h1 | h1
    · apply hb1
      calc b = d * (d⁻¹ * b * d) * d⁻¹ := by group
        _ = 1 := by rw [← hb', h1]; group
    · apply hba
      have hda : d * h.a = h.a * d := mem_centralizer_singleton_iff.mp hd
      calc b = d * (d⁻¹ * b * d) * d⁻¹ := by group
        _ = d * h.a * d⁻¹ := by rw [← hb', h1]
        _ = h.a := by rw [hda, mul_inv_cancel_right]
  have hR₀eq : R₀ = C₀ := (eq_of_le_of_card_ge hC₀R₀ hcard_le).symm
  refine ⟨R, ?_⟩
  rw [← hR₀eq, hR₀]
  exact (comap_map_eq_self_of_injective Y.subtype_injective _).symm

end Six

theorem prop62 [IsSimpleGroup X] (hS : SchreierFor Blueprint.Catalog)
    (hnonab : ∃ u v : X, u * v ≠ v * u) (hK : Assembly.KProper Blueprint.Catalog X)
    (h : Hyp52 X) (hmax : GSMaximalUnbalancingTriple h.a h.x h.J)
    (hiso : GSIsoAt h.a h.J)
    (hT : h.T = h.B ⊔ zpowers h.a) (hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a)
    (hJn : (h.J.subgroupOf (centralizer ({h.a} : Set X))).Normal)
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    (hBP : ¬ h.P ≤ normalizer (h.B : Set X)) {y : X} (hy : h.IsX0Min y) :
    ∃ h' : Hyp52 X, h'.a = h.a ∧ h'.J = h.J ∧ h'.B = h.B ∧ h'.K = h.K ∧
      (∃ c ∈ centralizer ({h.a} : Set X) ⊓ normalizer (h.J : Set X),
        h'.S = conjugate h.S c ∧ h'.x = c⁻¹ * h.x * c) ∧
      h'.Q = h.Q ∧ h'.Q ≤ normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X) ∧
      y ∈ normalizer (h'.Q : Set X) ∧ y ∈ h'.P ∧ y ∉ h'.T ∧ y ^ 2 ∈ h'.T ∧
      (h'.S ⊓ normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X) ≤
          normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X) ⊓
            centralizer ((zpowers h.a ⊔ ⁅h.B, zpowers y⁆ : Subgroup X) : Set X) ∧
        ∃ R : Sylow 2 ↥(normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X) ⊓
            centralizer ((zpowers h.a ⊔ ⁅h.B, zpowers y⁆ : Subgroup X) : Set X)),
          (R : Subgroup _) =
            (h'.S ⊓ normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X)).subgroupOf
              (normalizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X) ⊓
                centralizer ((zpowers h.a ⊔ ⁅h.B, zpowers y⁆ : Subgroup X) : Set X))) ∧
      h'.Lemma61Shape y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy61 := h.lemma61 hT hC hBP hy
  set B₀ := h.B ⊓ conjugate h.B y with hB₀
  set E := zpowers h.a ⊔ ⁅h.B, zpowers y⁆ with hE
  have haa := Six.a_mul_a_self h
  have ha' : h.a⁻¹ = h.a := inv_eq_of_mul_eq_one_right haa
  have haB := Six.a_not_mem_B hC
  have hP1 := Six.upperP_one_eq hC
  have hSC : h.S ≤ centralizer ({h.a} : Set X) := h.S_le.trans inf_le_left
  have hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X) :=
    Six.centralizer_le_normalizer_of_normal h.J_le hJn
  have hS2 : IsPGroup 2 h.S := by
    obtain ⟨R, hR⟩ := h.S_sylow
    have h1 : IsPGroup 2 (h.S.subgroupOf (centralizer ({h.a} : Set X) ⊓
        normalizer (h.J : Set X))) := hR ▸ R.isPGroup'
    have h2 := h1.map (centralizer ({h.a} : Set X) ⊓ normalizer (h.J : Set X)).subtype
    rwa [map_subgroupOf_eq_of_le h.S_le] at h2
  have hBS : h.B ≤ h.S := h.B_le.trans inf_le_left
  have hBC : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hyP : y ∈ h.P := (mem_inf.mp hy.1).2
  have hyS : y ∈ h.S := (mem_inf.mp hyP).1
  have hyN : y ∉ normalizer (h.B : Set X) := fun hyN =>
    hy.2.1 (mem_inf.mpr ⟨mem_inf.mpr ⟨hyS, hyN⟩, hyP⟩)
  have hQB0 := hy.Q_le_normalizer_B0
  have hyQ := hy.mem_normalizer_Q
  have hyB0 := hy.mem_normalizer_B0
  have hBQ : h.B ≤ h.Q := le_inf hBS le_normalizer
  have hS0 : h.S ⊓ normalizer (B₀ : Set X) ≤ h.S := inf_le_left
  have hQS0 : h.Q ≤ h.S ⊓ normalizer (B₀ : Set X) := le_inf inf_le_left hQB0
  have haE : h.a ∈ E := mem_sup_left (mem_zpowers _)
  have hcase : ⁅h.B, zpowers y⁆ = zpowers h.a ∨
      ∃ b : X, orderOf b = 2 ∧ h.x⁻¹ * b * h.x = h.a * b ∧ h.upperP 2 = closure {h.a, b} ∧
        b ∈ h.B ⊓ conjugate h.B y ∧ y * b = b * y ∧ ⁅h.B, zpowers y⁆ ≤ closure {h.a, b} ∧
        ((centralizer ({b} : Set X)).subgroupOf h.S).index = 2 ∧
        ¬ ⁅h.B, zpowers y⁆ ≤ zpowers h.a := by
    rcases hy61 with ⟨-, h1⟩ | ⟨-, b, hb2, hbx, hU2, hbB0, hyb, hcomm, hidx⟩
    · exact Or.inl h1
    · by_cases hle : ⁅h.B, zpowers y⁆ ≤ zpowers h.a
      · left
        refine le_antisymm hle (zpowers_le.mpr ?_)
        obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hy.commutator_ne_bot
        have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
        rcases Six.eq_one_or_eq_a (hle hw) with h1 | h1
        · exact absurd h1 hw1'
        · rwa [← h1]
      · exact Or.inr ⟨b, hb2, hbx, hU2, hbB0, hyb, hcomm, hidx, hle⟩
  have hbfacts : ∀ b : X, orderOf b = 2 → h.upperP 2 = closure {h.a, b} →
      b ∈ h.B ⊓ conjugate h.B y → ⁅h.B, zpowers y⁆ ≤ closure {h.a, b} →
      ¬ ⁅h.B, zpowers y⁆ ≤ zpowers h.a →
      b * b = 1 ∧ b * h.a = h.a * b ∧ b ≠ 1 ∧ b ≠ h.a ∧ b ∈ h.P ∧ E = closure {h.a, b} ∧
        ∀ s ∈ h.S, ⁅b, s⁆ = 1 ∨ ⁅b, s⁆ = h.a := by
    intro b hb2 hU2 hbB0 hcomm hle
    have hbB : b ∈ h.B := (mem_inf.mp hbB0).1
    have hbP : b ∈ h.P := h.B_le hbB
    have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
    have hab : b * h.a = h.a * b := Six.comm_a hC (hBS hbB)
    have hb1 : b ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hb2
      exact absurd hb2 (by norm_num)
    have hba : b ≠ h.a := fun h1 => haB (h1 ▸ hbB)
    have hbU : b ∈ h.upperP 2 := hU2 ▸ subset_closure (by simp)
    refine ⟨hbb, hab, hb1, hba, hbP, ?_, fun s hs => ?_⟩
    · apply le_antisymm
      · exact sup_le (zpowers_le.mpr (subset_closure (by simp))) hcomm
      · rw [closure_le]
        intro w hw
        rcases hw with rfl | rfl
        · exact haE
        · obtain ⟨v, hv, hva⟩ := Set.not_subset.mp hle
          rcases Six.mem_closure_pair_cases haa hbb hab (hcomm hv) with h1 | h1 | h1 | h1
          · exact absurd (h1 ▸ one_mem _) hva
          · exact absurd (h1 ▸ mem_zpowers _) hva
          · rw [← h1]
            exact mem_sup_right hv
          · have := mul_mem haE (mem_sup_right hv : v ∈ E)
            rwa [h1, ← mul_assoc, haa, one_mul] at this
    · refine Six.eq_one_or_eq_a ?_
      rw [← hP1]
      exact mem_inf.mpr ⟨(h.commutator_mem_upperS (mem_inf.mp hbU).1 hs).1,
        (h.commutator_mem_P hbP hs).1⟩
  have hkey : (h.S ⊓ normalizer (B₀ : Set X) ≤ centralizer (E : Set X)) ∧
      ∃ R : Sylow 2 ↥(centralizer (E : Set X)),
        (R : Subgroup _) =
          (h.S ⊓ centralizer (E : Set X)).subgroupOf (centralizer (E : Set X)) := by
    rcases hcase with h1 | ⟨b, hb2, hbx, hU2, hbB0, hyb, hcomm, hidx, hle⟩
    · have hEA : E = zpowers h.a := by rw [hE, h1, sup_idem]
      rw [hEA]
      refine ⟨fun s hs => ?_, Six.sylow_centralizer_zpowers hSa⟩
      rw [centralizer_zpowers_eq]
      exact hSC (mem_inf.mp hs).1
    · obtain ⟨hbb, hab, hb1, hba, hbP, hEB, hbs⟩ := hbfacts b hb2 hU2 hbB0 hcomm hle
      rw [hEB]
      refine ⟨fun s hs => ?_, Six.sylow_centralizer_closure_pair hJn hSa hC hbP hb1 hba hidx⟩
      obtain ⟨hsS, hsN⟩ := mem_inf.mp hs
      have hsb : b * s = s * b := by
        rcases hbs s hsS with h1 | h1
        · exact commutatorElement_eq_one_iff_mul_comm.mp h1
        · exfalso
          apply haB
          have h2 : s * b * s⁻¹ ∈ B₀ := (mem_normalizer_iff.mp hsN b).mp hbB0
          rw [commutatorElement_def] at h1
          have h3 : s * b * s⁻¹ = h.a * b := by
            calc s * b * s⁻¹ = (b * s * b⁻¹ * s⁻¹)⁻¹ * b := by group
              _ = h.a * b := by rw [h1, ha']
          rw [h3] at h2
          have := mul_mem (mem_inf.mp h2).1 (inv_mem (mem_inf.mp hbB0).1)
          rwa [mul_inv_cancel_right] at this
      rw [centralizer_closure, mem_centralizer_iff]
      intro w hw
      rcases hw with rfl | rfl
      · exact (mem_centralizer_singleton_iff.mp (hSC hsS)).symm
      · exact hsb
  obtain ⟨hS0E, hCSE⟩ := hkey
  set M := normalizer (B₀ : Set X) ⊓ centralizer (E : Set X) with hM
  have hS0M : h.S ⊓ normalizer (B₀ : Set X) ≤ M := le_inf inf_le_right hS0E
  have hS02 : IsPGroup 2 ((h.S ⊓ normalizer (B₀ : Set X)).subgroupOf M) :=
    (hS2.to_le inf_le_left).comap_subtype
  obtain ⟨RT, hRT⟩ := hS02.exists_le_sylow
  set T := (RT : Subgroup M).map M.subtype with hTdef
  have hTM : T ≤ M := map_subtype_le _
  have hS0T : h.S ⊓ normalizer (B₀ : Set X) ≤ T := fun z hz =>
    ⟨⟨z, hS0M hz⟩, hRT (mem_subgroupOf.mpr hz), rfl⟩
  have hT2 : IsPGroup 2 T := RT.isPGroup'.map _
  have hTE : T ≤ centralizer (E : Set X) := hTM.trans inf_le_right
  obtain ⟨g, hgE, hgT⟩ := exists_conjugate_le_of_sylow hCSE hTE hT2
  have hga : g ∈ centralizer ({h.a} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hgE h.a haE).symm
  have hca : g⁻¹ ∈ centralizer ({h.a} : Set X) := inv_mem hga
  have hgJ : g ∈ normalizer (h.J : Set X) := hCN hga
  have hcJ : g⁻¹ ∈ normalizer (h.J : Set X) := inv_mem hgJ
  set c := g⁻¹ with hc
  set S' := conjugate h.S c with hS'
  have hconjS' : conjugate S' g = h.S := by
    rw [hS', conjugate_conjugate, hc, inv_mul_cancel, conjugate_one]
  have hconjInf : ∀ A A' : Subgroup X, conjugate (A ⊓ A') g = conjugate A g ⊓ conjugate A' g :=
    fun A A' => Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective
  have hconjN : ∀ F : Subgroup X,
      conjugate (normalizer (F : Set X)) g = normalizer (conjugate F g : Set X) :=
    fun F => map_equiv_normalizer_eq F (MulAut.conj g⁻¹)
  have hconjC : conjugate (coreActionKernel h.J) g = coreActionKernel h.J :=
    Six.conjugate_coreActionKernel hgJ
  have hTS' : T ≤ S' := by
    intro t ht
    have h1 : g⁻¹ * t * g ∈ h.S := (mem_inf.mp (hgT (by
      rw [mem_conjugate_iff, show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
      exact ht))).1
    rw [hS', mem_conjugate_iff, hc, inv_inv]
    exact h1
  have hQT : h.Q ≤ T := hQS0.trans hS0T
  have hBT : h.B ≤ T := hBQ.trans hQT
  have hQS' : h.Q ≤ S' := hQT.trans hTS'
  have hyS0 : y ∈ h.S ⊓ normalizer (B₀ : Set X) := mem_inf.mpr ⟨hyS, hyB0⟩
  have hyS' : y ∈ S' := hTS' (hS0T hyS0)
  have hNQ : S' ⊓ normalizer (h.B : Set X) = h.Q := by
    have hcard : Nat.card ↥(S' ⊓ normalizer (h.B : Set X)) ≤ Nat.card h.Q := by
      by_contra hlt
      push Not at hlt
      set E' := conjugate h.B g with hE'
      have hE'S : E' ≤ h.S := (map_mono hBT).trans (hgT.trans inf_le_left)
      have hE'C : E' ≤ coreActionKernel h.J := by
        rw [← hconjC]
        exact map_mono hBC
      have hE'card : Nat.card E' = Nat.card h.B := GSLit.card_conjugate h.B g
      have hNE' : conjugate (S' ⊓ normalizer (h.B : Set X)) g =
          h.S ⊓ normalizer (E' : Set X) := by
        rw [hconjInf, hconjS', hconjN]
      have hlt' : Nat.card ↥(h.S ⊓ normalizer (h.B : Set X)) <
          Nat.card ↥(h.S ⊓ normalizer (E' : Set X)) := by
        rw [← hNE', GSLit.card_conjugate]
        exact hlt
      obtain ⟨L, hL⟩ := h.isoCorr_of_lt E' (le_inf hE'S hE'C) (Or.inr ⟨hE'card, hlt'⟩)
      have hL' := Six.isoCorrSub_conjugate hca hcJ hL
      rw [hE', conjugate_conjugate, mul_inv_cancel, conjugate_one] at hL'
      exact h.not_isoCorrSub_B _ hL'
    exact (eq_of_le_of_card_ge (le_inf hQS' inf_le_right) hcard).symm
  have hsyl' := Six.sylow_conjugate_of_mem h.S_le h.S_sylow (mem_inf.mpr ⟨hca, hcJ⟩)
  have hxx : h.x * h.x = 1 := by
    obtain ⟨-, hx, -⟩ := gsUnbalancingTriple_iff.mp hmax.1
    rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hmax' : GSMaximalUnbalancingTriple h.a (c⁻¹ * h.x * c) h.J :=
    ⟨gsUnbalancingTriple_conj hmax.1 hca hcJ, hmax.2⟩
  have hB2 : IsPGroup 2 h.B := hS2.to_le hBS
  have hBa : h.B ≤ centralizer ({h.a} : Set X) := hBS.trans hSC
  have hinfx : h.B ⊓ conjugate h.B (c⁻¹ * h.x * c) = ⊥ :=
    inf_conjugate_eq_bot hS hnonab hK hmax' hiso hB2 hBa hBC h.conjClosure_eq h.commutator_eq
  have hx'S : c⁻¹ * h.x * c ∈ S' := by
    rw [hS', mem_conjugate_iff, show c * (c⁻¹ * h.x * c) * c⁻¹ = h.x by group]
    exact h.x_mem
  have hx'sq : (c⁻¹ * h.x * c) ^ 2 = 1 := by
    rw [pow_two, show c⁻¹ * h.x * c * (c⁻¹ * h.x * c) = c⁻¹ * (h.x * h.x) * c by group, hxx]
    group
  have hcardQ : Nat.card ↥(S' ⊓ normalizer (h.B : Set X)) =
      Nat.card ↥(h.S ⊓ normalizer (h.B : Set X)) := by rw [hNQ]
  let h' : Hyp52 X :=
    { h with
      S := S'
      x := c⁻¹ * h.x * c
      S_le := hsyl'.1
      S_sylow := hsyl'.2
      B_le := le_inf (hBT.trans hTS') hBC
      isoCorr_of_lt := by
        intro F hF hFcard
        set F' := conjugate F g with hF'
        have hF'S : F' ≤ h.S ⊓ coreActionKernel h.J := by
          rw [← hconjS', ← hconjC, ← hconjInf]
          exact map_mono hF
        have hF'card : Nat.card F' = Nat.card F := GSLit.card_conjugate F g
        have hNF' : Nat.card ↥(h.S ⊓ normalizer (F' : Set X)) =
            Nat.card ↥(S' ⊓ normalizer (F : Set X)) := by
          rw [← GSLit.card_conjugate (S' ⊓ normalizer (F : Set X)) g, hconjInf, hconjS', hconjN]
        obtain ⟨L, hL⟩ := h.isoCorr_of_lt F' hF'S (by
          rw [hF'card, hNF', ← hcardQ]
          exact hFcard)
        refine ⟨conjugate L c, ?_⟩
        have := Six.isoCorrSub_conjugate hca hcJ hL
        rwa [hF', conjugate_conjugate, hc, mul_inv_cancel, conjugate_one] at this
      x_mem := hx'S
      inf_conjugate_x := hinfx
      x_sq_mem := by
        rw [hx'sq]
        exact one_mem _
      sylow_layer := by
        obtain ⟨R, hR1, hR2⟩ := h.sylow_layer
        exact ⟨R, hR1.trans (le_of_eq hNQ.symm), hR2⟩ }
  have hQ' : h'.Q = h.Q := hNQ
  refine ⟨h', rfl, rfl, rfl, rfl, ⟨c, mem_inf.mpr ⟨hca, hcJ⟩, rfl, rfl⟩, hQ', hQ' ▸ hQB0,
    hQ' ▸ hyQ, mem_inf.mpr ⟨hyS', (mem_inf.mp hyP).2⟩, ?_, ?_, ?_, ?_⟩
  · intro hyT'
    exact hyN (mem_inf.mp (mem_inf.mp hyT').1).2
  · have hy2N : y ^ 2 ∈ normalizer (h.B : Set X) := (mem_inf.mp (mem_inf.mp hy.2.2).1).2
    have hy2C : y ^ 2 ∈ coreActionKernel h.J := (mem_inf.mp (mem_inf.mp hy.2.2).2).2
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨pow_mem hyS' 2, hy2N⟩, mem_inf.mpr ⟨pow_mem hyS' 2, hy2C⟩⟩
  ·
    have hS'0E : S' ⊓ normalizer (B₀ : Set X) ≤ centralizer (E : Set X) := by
      intro s hs
      obtain ⟨hsS', hsN⟩ := mem_inf.mp hs
      have hsa : s ∈ centralizer ({h.a} : Set X) := (mem_inf.mp (hsyl'.1 hsS')).1
      rcases hcase with h1 | ⟨b, hb2, hbx, hU2, hbB0, hyb, hcomm, hidx, hle⟩
      · rw [hE, h1, sup_idem, centralizer_zpowers_eq]
        exact hsa
      · obtain ⟨hbb, hab, hb1, hba, hbP, hEB, hbs⟩ := hbfacts b hb2 hU2 hbB0 hcomm hle
        have hcb : c * b = b * c :=
          (mem_centralizer_iff.mp (inv_mem hgE) b (hEB ▸ subset_closure (by simp))).symm
        have hcaa : c * h.a = h.a * c := mem_centralizer_singleton_iff.mp hca
        rw [hS', mem_conjugate_iff] at hsS'
        have hbs' : ⁅b, s⁆ = 1 ∨ ⁅b, s⁆ = h.a := by
          have heq : ⁅b, s⁆ = c⁻¹ * ⁅b, c * s * c⁻¹⁆ * c := by
            rw [commutatorElement_def, commutatorElement_def]
            calc b * s * b⁻¹ * s⁻¹ = c⁻¹ * ((c * b * c⁻¹) * (c * s * c⁻¹) * (c * b * c⁻¹)⁻¹ *
                (c * s * c⁻¹)⁻¹) * c := by group
              _ = c⁻¹ * (b * (c * s * c⁻¹) * b⁻¹ * (c * s * c⁻¹)⁻¹) * c := by
                rw [hcb, mul_inv_cancel_right]
          rcases hbs _ hsS' with h1 | h1
          · left
            rw [heq, h1]
            group
          · right
            rw [heq, h1, mul_assoc, ← hcaa, ← mul_assoc, inv_mul_cancel, one_mul]
        have hsb : b * s = s * b := by
          rcases hbs' with h1 | h1
          · exact commutatorElement_eq_one_iff_mul_comm.mp h1
          · exfalso
            apply haB
            have h2 : s * b * s⁻¹ ∈ B₀ := (mem_normalizer_iff.mp hsN b).mp hbB0
            rw [commutatorElement_def] at h1
            have h3 : s * b * s⁻¹ = h.a * b := by
              calc s * b * s⁻¹ = (b * s * b⁻¹ * s⁻¹)⁻¹ * b := by group
                _ = h.a * b := by rw [h1, ha']
            rw [h3] at h2
            have := mul_mem (mem_inf.mp h2).1 (inv_mem (mem_inf.mp hbB0).1)
            rwa [mul_inv_cancel_right] at this
        rw [hEB, centralizer_closure, mem_centralizer_iff]
        intro w hw
        rcases hw with rfl | rfl
        · exact (mem_centralizer_singleton_iff.mp hsa).symm
        · exact hsb
    refine ⟨le_inf inf_le_right hS'0E, ?_⟩
    have hS'2 : IsPGroup 2 S' := hS2.map (MulAut.conj c⁻¹).toMonoidHom
    have hTeq : T = S' ⊓ normalizer (B₀ : Set X) := by
      have hle : T ≤ S' ⊓ normalizer (B₀ : Set X) := le_inf hTS' (hTM.trans inf_le_left)
      refine eq_of_le_of_card_ge hle ?_
      have hS'M : S' ⊓ normalizer (B₀ : Set X) ≤ M := le_inf inf_le_right hS'0E
      have h2 : IsPGroup 2 ((S' ⊓ normalizer (B₀ : Set X)).subgroupOf M) :=
        (hS'2.to_le inf_le_left).comap_subtype
      obtain ⟨R', hR'⟩ := h2.exists_le_sylow
      calc Nat.card ↥(S' ⊓ normalizer (B₀ : Set X))
          = Nat.card ((S' ⊓ normalizer (B₀ : Set X)).subgroupOf M) := by
            rw [Six.card_subgroupOf_eq, inf_eq_left.mpr hS'M]
        _ ≤ Nat.card R' := card_le_of_le hR'
        _ = Nat.card RT := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
        _ = Nat.card T := (card_map_of_injective M.subtype_injective).symm
    refine ⟨RT, ?_⟩
    rw [← hTeq, hTdef]
    exact (comap_map_eq_self_of_injective M.subtype_injective _).symm
  ·
    rcases hcase with h1 | ⟨b, hb2, hbx, hU2, hbB0, hyb, hcomm, hidx, hle⟩
    · exact Or.inl h1
    · right
      obtain ⟨hbb, hab, hb1, hba, hbP, hEB, hbs⟩ := hbfacts b hb2 hU2 hbB0 hcomm hle
      have hcb : c * b = b * c :=
        (mem_centralizer_iff.mp (inv_mem hgE) b (hEB ▸ subset_closure (by simp))).symm
      have hcaa : c * h.a = h.a * c := mem_centralizer_singleton_iff.mp hca
      refine ⟨b, hb2, ?_, ?_, hbB0, hyb, hcomm, ?_⟩
      · show (c⁻¹ * h.x * c)⁻¹ * b * (c⁻¹ * h.x * c) = h.a * b
        have hcab : c * (h.a * b) = h.a * b * c := by
          rw [← mul_assoc, hcaa, mul_assoc, hcb, ← mul_assoc]
        calc (c⁻¹ * h.x * c)⁻¹ * b * (c⁻¹ * h.x * c)
            = c⁻¹ * (h.x⁻¹ * (c * b * c⁻¹) * h.x) * c := by group
          _ = c⁻¹ * (h.x⁻¹ * b * h.x) * c := by rw [hcb, mul_inv_cancel_right]
          _ = c⁻¹ * (h.a * b) * c := by rw [hbx]
          _ = c⁻¹ * (c * (h.a * b)) := by rw [mul_assoc, hcab]
          _ = h.a * b := by group
      · have hcN : c ∈ normalizer ((closure {h.a, b} : Subgroup X) : Set X) := by
          refine centralizer_le_normalizer _ ?_
          rw [centralizer_closure, mem_centralizer_iff]
          intro w hw
          rcases hw with rfl | rfl
          · exact hcaa.symm
          · exact hcb.symm
        calc h'.upperP 2 = conjugate (h.upperS 2) c ⊓
              (conjugate h.S c ⊓ conjugate (coreActionKernel h.J) c) := by
              show (Subgroup.upperCentralSeries (conjugate h.S c) 2).map
                (conjugate h.S c).subtype ⊓ (conjugate h.S c ⊓ coreActionKernel h.J) = _
              rw [Six.map_upperCentralSeries_conjugate, Six.conjugate_coreActionKernel hcJ]
              rfl
          _ = conjugate (h.upperP 2) c := by
              have hci : ∀ A A' : Subgroup X,
                  conjugate (A ⊓ A') c = conjugate A c ⊓ conjugate A' c :=
                fun A A' => Subgroup.map_inf _ _ _ (MulAut.conj c⁻¹).injective
              show _ = conjugate (h.upperS 2 ⊓ (h.S ⊓ coreActionKernel h.J)) c
              rw [hci, hci]
          _ = conjugate (closure {h.a, b}) c := by rw [hU2]
          _ = closure {h.a, b} := conjugate_eq_of_mem_normalizer hcN
      · show ((centralizer ({b} : Set X)).subgroupOf (conjugate h.S c)).index = 2
        rw [Six.index_centralizer_conjugate h.S hcb]
        exact hidx

end CFSG.ComponentClassification.GSThmB
