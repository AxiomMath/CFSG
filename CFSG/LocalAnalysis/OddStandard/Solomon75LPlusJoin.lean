module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusFactors
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalProduct
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def NoNormal3 (N : Subgroup G) : Prop :=
  ∀ P : Subgroup G, P ≤ N → IsPGroup 3 P → N ≤ normalizer (P : Set G) → P = ⊥

theorem commutator_eq_bot_or_twoSet_le {F K : Subgroup G} (hF : QFacts F)
    (hFK : F ≤ normalizer (K : Set G))
    (hperm : ∀ k ∈ K, (∀ f ∈ F, k * f * k⁻¹ ∈ F) ∨
      (∀ f ∈ F, ∀ f' ∈ F, k * f * k⁻¹ * f' = f' * (k * f * k⁻¹))) :
    ⁅F, K⁆ = ⊥ ∨ twoSet F ⊆ K := by
  by_cases hD : ∀ d ∈ F ⊓ K, ∀ g ∈ F, g * d = d * g
  · left
    have hnorm : ∀ k ∈ K, ∀ f ∈ F, k * f * k⁻¹ ∈ F := by
      intro k hk
      rcases hperm k hk with h | h
      · exact h
      · exfalso
        obtain ⟨t, ht, h', hh, _, _, g, hg, hgne⟩ := hF.noncentral_two
        apply hgne
        have hu1 : t⁻¹ * (k * t * k⁻¹) ∈ K := by
          have h1 : t⁻¹ * k * t⁻¹⁻¹ ∈ K := (mem_normalizer_iff.mp (hFK (F.inv_mem ht)) k).mp hk
          have h2 : t⁻¹ * (k * t * k⁻¹) = (t⁻¹ * k * t⁻¹⁻¹) * k⁻¹ := by group
          rw [h2]
          exact K.mul_mem h1 (K.inv_mem hk)
        have hu2 : h'⁻¹ * (t⁻¹ * (k * t * k⁻¹)) * h'⁻¹⁻¹ ∈ K :=
          (mem_normalizer_iff.mp (hFK (F.inv_mem hh)) _).mp hu1
        have hcomm : h'⁻¹ * (k * t * k⁻¹) * h' = k * t * k⁻¹ := by
          have := h t ht h' hh
          calc h'⁻¹ * (k * t * k⁻¹) * h' = h'⁻¹ * ((k * t * k⁻¹) * h') := by rw [mul_assoc]
            _ = h'⁻¹ * (h' * (k * t * k⁻¹)) := by rw [this]
            _ = k * t * k⁻¹ := by group
        have hw : t⁻¹ * (h'⁻¹ * t * h') ∈ K := by
          have : t⁻¹ * (h'⁻¹ * t * h') =
              (t⁻¹ * (k * t * k⁻¹)) * (h'⁻¹ * (t⁻¹ * (k * t * k⁻¹)) * h'⁻¹⁻¹)⁻¹ := by
            have e : h'⁻¹ * (t⁻¹ * (k * t * k⁻¹)) * h'⁻¹⁻¹ =
                (h'⁻¹ * t⁻¹ * h') * (h'⁻¹ * (k * t * k⁻¹) * h') := by group
            rw [e, hcomm]
            group
          rw [this]
          exact K.mul_mem hu1 (K.inv_mem hu2)
        exact hD _ ⟨F.mul_mem (F.inv_mem ht) (F.mul_mem (F.mul_mem (F.inv_mem hh) ht) hh), hw⟩ g hg
    have hKF : K ≤ normalizer (F : Set G) := Subgroup.le_normalizer_iff.mpr hnorm
    have := commute_of_inf_central hF hFK hKF hD
    rw [commutator_eq_bot_iff_le_centralizer]
    intro f hf
    rw [mem_centralizer_iff]
    intro k hk
    exact this k hk f hf
  · right
    push Not at hD
    obtain ⟨d, hd, g, hg, hne⟩ := hD
    intro q hq
    obtain ⟨a, ha, b, hb, hqab⟩ := hF.normal_dich d hd.1 ⟨g, hg, hne⟩ q hq.1 hq.2
    rw [hqab]
    exact K.mul_mem (commutator_mem_of_normalizes (A := K) (B := F) hFK hd.2 ha)
      (commutator_mem_of_normalizes (A := K) (B := F) hFK hd.2 hb)


theorem map_conj_pow_three {x : G} (hx3 : x ^ 3 = 1) (A : Subgroup G) :
    ((A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom).map
      (MulAut.conj x).toMonoidHom = A := by
  simp only [Subgroup.map_map]
  have : (MulAut.conj x).toMonoidHom.comp ((MulAut.conj x).toMonoidHom.comp
      (MulAut.conj x).toMonoidHom) = MonoidHom.id G := by
    ext y
    have h3 : x * x * x = 1 := by rw [← pow_three']; exact hx3
    have e : x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * y * (x * x * x)⁻¹ := by group
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    rw [e, h3]
    group
  rw [this]
  exact Subgroup.map_id A

theorem pow_four_mul_inv_pow_three (u : G) : u ^ 4 * (u ^ 3)⁻¹ = u := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add]
  norm_num

theorem pow_three_aux {a b c : G} (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) : (a⁻¹ * b ^ 2 * c⁻¹) ^ 3 = 1 := by
  have h1 : Commute (a⁻¹ * b ^ 2) c⁻¹ := (hac.inv_inv).mul_left ((hbc.pow_left 2).inv_right)
  have h2 : Commute a⁻¹ (b ^ 2) := (hab.inv_left).pow_right 2
  rw [h1.mul_pow, h2.mul_pow, inv_pow, inv_pow, ha, ← pow_mul, mul_comm 2 3, pow_mul, hb, hc]
  simp


theorem conj_eq_of_cube {SH SK : Finset (Subgroup G)} (hQH : ∀ F ∈ SH, QFacts F) (hcH : PComm SH)
    (hQK : ∀ F ∈ SK, QFacts F) (hcK : PComm SK) {x : G} (hx : x ∈ SK.sup id) (hx3 : x ^ 3 = 1)
    (hHK : SH.sup id ≤ normalizer ((SK.sup id : Subgroup G) : Set G))
    (hperm : ∀ F ∈ SH, F.map (MulAut.conj x).toMonoidHom ∈ SH) {F : Subgroup G} (hF : F ∈ SH) :
    F.map (MulAut.conj x).toMonoidHom = F := by
  by_contra hne
  set c := (MulAut.conj x).toMonoidHom with hc
  have hinj : Function.Injective (Subgroup.map c) :=
    Subgroup.map_injective (MulAut.conj x).injective
  have hF' : F.map c ∈ SH := hperm F hF
  have hF'' : (F.map c).map c ∈ SH := hperm _ hF'
  have hne1 : F ≠ F.map c := fun h => hne h.symm
  have hne2 : F.map c ≠ (F.map c).map c := fun h => hne (hinj h).symm
  have hne3 : F ≠ (F.map c).map c := by
    intro h
    apply hne
    have := congrArg (Subgroup.map c) h
    rw [map_conj_pow_three hx3] at this
    exact this
  have hFF' : ⁅F, F.map c⁆ = ⊥ := hcH (Finset.mem_coe.mpr hF) (Finset.mem_coe.mpr hF') hne1
  have hFF'' : ⁅F, (F.map c).map c⁆ = ⊥ :=
    hcH (Finset.mem_coe.mpr hF) (Finset.mem_coe.mpr hF'') hne3
  have hF'F'' : ⁅F.map c, (F.map c).map c⁆ = ⊥ :=
    hcH (Finset.mem_coe.mpr hF') (Finset.mem_coe.mpr hF'') hne2
  obtain ⟨h, hhF, hh1, hh3⟩ := (hQH F hF).nontriv3
  set hb := x * h * x⁻¹ with hhb
  set hcc := x * hb * x⁻¹ with hhcc
  have hbF' : hb ∈ F.map c := Subgroup.mem_map.mpr ⟨h, hhF, rfl⟩
  have hccF'' : hcc ∈ (F.map c).map c := Subgroup.mem_map.mpr ⟨hb, hbF', rfl⟩
  have hab : Commute h hb := commute_of_commutator_eq_bot hFF' hhF hbF'
  have hac : Commute h hcc := commute_of_commutator_eq_bot hFF'' hhF hccF''
  have hbc : Commute hb hcc := commute_of_commutator_eq_bot hF'F'' hbF' hccF''
  have hb3 : hb ^ 3 = 1 := by
    rw [hhb, conj_pow, hh3]
    group
  have hcc3 : hcc ^ 3 = 1 := by
    rw [hhcc, conj_pow, hb3]
    group
  have hhK : ∀ y ∈ SK.sup id, h⁻¹ * y * h⁻¹⁻¹ ∈ SK.sup id := fun y hy =>
    (mem_normalizer_iff.mp (hHK ((SH.sup id).inv_mem (le_sup_of_mem hF hhF)))  y).mp hy
  have hc0 : h⁻¹ * hb ∈ SK.sup id := by
    have e : h⁻¹ * hb = (h⁻¹ * x * h⁻¹⁻¹) * x⁻¹ := by rw [hhb]; group
    rw [e]
    exact (SK.sup id).mul_mem (hhK x hx) ((SK.sup id).inv_mem hx)
  have hu4 := comm_two_of_commProd hQK hcK (h⁻¹ * hb) hc0 x hx
  have hu : ⁅h⁻¹ * hb, x⁆ = h⁻¹ * hb ^ 2 * hcc⁻¹ := by
    have e1 : hcc = x * hb * x⁻¹ := hhcc
    have e2 : hb = x * h * x⁻¹ := hhb
    have : ⁅h⁻¹ * hb, x⁆ = h⁻¹ * hb * (x * hb⁻¹ * x⁻¹) * (x * h * x⁻¹) := by
      rw [commutatorElement_def]; group
    rw [this, ← e2]
    have e3 : x * hb⁻¹ * x⁻¹ = hcc⁻¹ := by rw [e1]; group
    rw [e3]
    have hbi : hb * hcc⁻¹ = hcc⁻¹ * hb := (hbc.inv_right).eq
    calc h⁻¹ * hb * hcc⁻¹ * hb = h⁻¹ * (hb * (hcc⁻¹ * hb)) := by group
      _ = h⁻¹ * (hb * (hb * hcc⁻¹)) := by rw [hbi]
      _ = h⁻¹ * hb ^ 2 * hcc⁻¹ := by rw [pow_two]; group
  rw [hu] at hu4
  have hu3 := pow_three_aux hab hac hbc hh3 hb3 hcc3
  have hu1 : h⁻¹ * hb ^ 2 * hcc⁻¹ = 1 := by
    calc h⁻¹ * hb ^ 2 * hcc⁻¹ = (h⁻¹ * hb ^ 2 * hcc⁻¹) ^ 4 * ((h⁻¹ * hb ^ 2 * hcc⁻¹) ^ 3)⁻¹ :=
          (pow_four_mul_inv_pow_three _).symm
      _ = 1 := by rw [hu4, hu3]; simp
  have hhe : h = hb ^ 2 * hcc⁻¹ := by
    have := congrArg (fun y => h * y) hu1
    simp only [mul_one] at this
    calc h = h * (h⁻¹ * hb ^ 2 * hcc⁻¹) := by rw [hu1, mul_one]
      _ = hb ^ 2 * hcc⁻¹ := by group
  have hcen : ∀ g ∈ F, g * h = h * g := by
    intro g hg
    have e1 : Commute g hb := commute_of_commutator_eq_bot hFF' hg hbF'
    have e2 : Commute g hcc := commute_of_commutator_eq_bot hFF'' hg hccF''
    rw [hhe]
    exact ((e1.pow_right 2).mul_right e2.inv_right).eq
  have hsq := (hQH F hF).center_sq h hhF hcen
  apply hh1
  calc h = h * h * h := by rw [hsq, one_mul]
    _ = h ^ 3 := (pow_three' h).symm
    _ = 1 := hh3


theorem inner_of_commProd {S : Finset (Subgroup G)} (hQ : ∀ A ∈ S, QFacts A) (hc : PComm S) (x : G)
    (hx : ∀ A ∈ S, ∃ h ∈ A, h ^ 3 = 1 ∧ ∀ f ∈ A, x * f * x⁻¹ = h * f * h⁻¹) :
    ∃ h ∈ S.sup id, h ^ 3 = 1 ∧ ∀ f ∈ S.sup id, x * f * x⁻¹ = h * f * h⁻¹ := by
  refine commProd_induction
    (fun A => ∃ h ∈ A, h ^ 3 = 1 ∧ ∀ f ∈ A, x * f * x⁻¹ = h * f * h⁻¹)
    (fun N => ∃ h ∈ N, h ^ 3 = 1 ∧ ∀ f ∈ N, x * f * x⁻¹ = h * f * h⁻¹) ?_ ?_ S hQ hx hc
  · refine ⟨1, one_mem _, by simp, fun f hf => ?_⟩
    rw [Subgroup.mem_bot] at hf
    subst hf
    simp
  · rintro F N hF ⟨a, haF, ha3, hFa⟩ hFN ⟨b, hbN, hb3, hNa⟩
    refine ⟨a * b, mul_mem (mem_sup_left haF) (mem_sup_right hbN), ?_, ?_⟩
    · rw [(commute_of_commutator_eq_bot hFN haF hbN).mul_pow, ha3, hb3, one_mul]
    · intro f hf
      obtain ⟨f1, hf1, f2, hf2, rfl⟩ := (mem_sup_of_commutator_eq_bot hFN).mp hf
      have c1 : b * f1 = f1 * b := (commute_of_commutator_eq_bot hFN hf1 hbN).symm.eq
      have hbfN : b * f2 * b⁻¹ ∈ N := N.mul_mem (N.mul_mem hbN hf2) (N.inv_mem hbN)
      have c2 : a⁻¹ * (b * f2 * b⁻¹) = (b * f2 * b⁻¹) * a⁻¹ :=
        (commute_of_commutator_eq_bot hFN (F.inv_mem haF) hbfN).eq
      have key : (a * b) * (f1 * f2) * (a * b)⁻¹ = (a * f1 * a⁻¹) * (b * f2 * b⁻¹) := by
        calc (a * b) * (f1 * f2) * (a * b)⁻¹ = a * (b * f1) * f2 * b⁻¹ * a⁻¹ := by group
          _ = a * (f1 * b) * f2 * b⁻¹ * a⁻¹ := by rw [c1]
          _ = a * f1 * (b * f2 * b⁻¹) * a⁻¹ := by group
          _ = a * f1 * ((b * f2 * b⁻¹) * a⁻¹) := by rw [mul_assoc (a * f1)]
          _ = a * f1 * (a⁻¹ * (b * f2 * b⁻¹)) := by rw [c2]
          _ = (a * f1 * a⁻¹) * (b * f2 * b⁻¹) := by group
      rw [key, ← hFa f1 hf1, ← hNa f2 hf2]
      group


theorem commutator_mul_left (a b c : G) : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutator_mul_right (a b c : G) : ⁅a, b * c⁆ = ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem commutator_inv_left' (a c : G) : ⁅a⁻¹, c⁆ = a⁻¹ * ⁅a, c⁆⁻¹ * a := by
  simp only [commutatorElement_def]
  group

theorem commutator_mem_of_sup {H K : Subgroup G}
    (hKH : K ≤ normalizer (H : Set G)) (hKK : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ H) :
    ∀ g ∈ H ⊔ K, ∀ g' ∈ H ⊔ K, ⁅g, g'⁆ ∈ H := by
  have hN : H ⊔ K ≤ normalizer (H : Set G) := sup_le Subgroup.le_normalizer hKH
  let X : Subgroup G :=
    { carrier := {g | g ∈ H ⊔ K ∧ ∀ g' ∈ H ⊔ K, ⁅g, g'⁆ ∈ H}
      mul_mem' := by
        rintro a b ⟨ha, hax⟩ ⟨hb, hbx⟩
        refine ⟨(H ⊔ K).mul_mem ha hb, fun g' hg' => ?_⟩
        rw [commutator_mul_left]
        refine H.mul_mem ?_ (hax g' hg')
        have : a * ⁅b, g'⁆ * a⁻¹ ∈ H := (mem_normalizer_iff.mp (hN ha) _).mp (hbx g' hg')
        exact this
      one_mem' := ⟨(H ⊔ K).one_mem, fun g' _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, hax⟩
        refine ⟨(H ⊔ K).inv_mem ha, fun g' hg' => ?_⟩
        rw [commutator_inv_left']
        have h1 : ⁅a, g'⁆⁻¹ ∈ H := H.inv_mem (hax g' hg')
        have : a⁻¹ * ⁅a, g'⁆⁻¹ * a⁻¹⁻¹ ∈ H :=
          (mem_normalizer_iff.mp (hN ((H ⊔ K).inv_mem ha)) _).mp h1
        simpa using this }
  have hHX : H ≤ X := fun h hh =>
    ⟨mem_sup_left hh, fun g' hg' => commutator_mem_of_normalizes (A := H) (B := H ⊔ K) hN hh hg'⟩
  have hKX : K ≤ X := by
    intro k hk
    refine ⟨mem_sup_right hk, fun g' hg' => ?_⟩
    obtain ⟨h, hh, k', hk', rfl⟩ :=
      (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing H K hKH g').mp hg'
    rw [commutator_mul_right]
    have h1 : ⁅k, h⁆ ∈ H := by
      have : ⁅k, h⁆ = ⁅h, k⁆⁻¹ := (commutatorElement_inv h k).symm
      rw [this]
      exact H.inv_mem (commutator_mem_of_normalizes (A := H) (B := K) hKH hh hk)
    have h2 : h * ⁅k, k'⁆ * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh (hKK k hk k' hk')) (H.inv_mem hh)
    have : ⁅k, h⁆ * h * ⁅k, k'⁆ * h⁻¹ = ⁅k, h⁆ * (h * ⁅k, k'⁆ * h⁻¹) := by group
    rw [this]
    exact H.mul_mem h1 h2
  intro g hg g' hg'
  exact (sup_le hHX hKX hg).2 g' hg'


theorem commutator_pow_of_commute {d e : G} (h : Commute d ⁅d, e⁆) (n : ℕ) :
    ⁅d ^ n, e⁆ = ⁅d, e⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : d * ⁅d, e⁆ ^ n * d⁻¹ = ⁅d, e⁆ ^ n := by
      rw [(h.pow_right n).eq]
      group
    rw [pow_succ' d n, commutator_mul_left, ih, h1, pow_succ]

theorem eq_one_of_centralizes {SH : Finset (Subgroup G)} (hQH : ∀ F ∈ SH, QFacts F)
    (hcH : PComm SH) {K : Subgroup G}
    (hKH : K ≤ normalizer ((SH.sup id : Subgroup G) : Set G))
    (hKK : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ SH.sup id)
    (hN3 : NoNormal3 (SH.sup id ⊔ K)) {c : G} (hcN : c ∈ SH.sup id ⊔ K)
    (hcc : ∀ f ∈ SH.sup id, c * f = f * c) (hc3 : c ^ 3 = 1) : c = 1 := by
  set H := SH.sup id with hH
  have hNH : H ⊔ K ≤ normalizer (H : Set G) := sup_le Subgroup.le_normalizer hKH
  have hcomm := commutator_mem_of_sup hKH hKK
  have hsq := center_sq_of_commProd hQH hcH
  let T : Subgroup G :=
    { carrier := {d | d ∈ H ⊔ K ∧ (∀ f ∈ H, d * f = f * d) ∧ d ^ 3 = 1}
      mul_mem' := by
        rintro d e ⟨hd, hdc, hd3⟩ ⟨he, hec, he3⟩
        refine ⟨(H ⊔ K).mul_mem hd he, fun f hf => ?_, ?_⟩
        · rw [mul_assoc, hec f hf, ← mul_assoc, hdc f hf, mul_assoc]
        · have hz : ⁅d, e⁆ ∈ H := hcomm d hd e he
          have hzc : ∀ f ∈ H, f * ⁅d, e⁆ = ⁅d, e⁆ * f := by
            intro f hf
            have h1 := hdc f hf
            have h2 := hec f hf
            have h3 : f * d⁻¹ = d⁻¹ * f := by
              calc f * d⁻¹ = d⁻¹ * (d * f) * d⁻¹ := by group
                _ = d⁻¹ * (f * d) * d⁻¹ := by rw [h1]
                _ = d⁻¹ * f := by group
            have h4 : f * e⁻¹ = e⁻¹ * f := by
              calc f * e⁻¹ = e⁻¹ * (e * f) * e⁻¹ := by group
                _ = e⁻¹ * (f * e) * e⁻¹ := by rw [h2]
                _ = e⁻¹ * f := by group
            rw [commutatorElement_def]
            calc f * (d * e * d⁻¹ * e⁻¹) = (f * d) * e * d⁻¹ * e⁻¹ := by group
              _ = d * (f * e) * d⁻¹ * e⁻¹ := by rw [← h1]; group
              _ = d * e * (f * d⁻¹) * e⁻¹ := by rw [← h2]; group
              _ = d * e * d⁻¹ * (f * e⁻¹) := by rw [h3]; group
              _ = d * e * d⁻¹ * e⁻¹ * f := by rw [h4]; group
          have hz2 : ⁅d, e⁆ * ⁅d, e⁆ = 1 := hsq _ hz fun n hn => (hzc n hn)
          have hdz : Commute d ⁅d, e⁆ := hdc _ hz
          have hz3 : ⁅d, e⁆ ^ 3 = 1 := by
            rw [← commutator_pow_of_commute hdz 3, hd3]
            simp
          have hz1 : ⁅d, e⁆ = 1 := by
            calc ⁅d, e⁆ = ⁅d, e⁆ * ⁅d, e⁆ * ⁅d, e⁆ := by rw [hz2, one_mul]
              _ = ⁅d, e⁆ ^ 3 := (pow_three' _).symm
              _ = 1 := hz3
          have hde : Commute d e := commutatorElement_eq_one_iff_mul_comm.mp hz1
          rw [hde.mul_pow, hd3, he3, one_mul]
      one_mem' := ⟨(H ⊔ K).one_mem, fun f _ => by simp, by simp⟩
      inv_mem' := by
        rintro d ⟨hd, hdc, hd3⟩
        refine ⟨(H ⊔ K).inv_mem hd, fun f hf => ?_, by rw [inv_pow, hd3, inv_one]⟩
        calc d⁻¹ * f = d⁻¹ * (f * d) * d⁻¹ := by group
          _ = d⁻¹ * (d * f) * d⁻¹ := by rw [hdc f hf]
          _ = f * d⁻¹ := by group }
  have hTN : T ≤ H ⊔ K := fun d hd => hd.1
  have hTp : IsPGroup 3 T := fun d => ⟨1, Subtype.ext (by simpa using d.2.2.2)⟩
  have hnorm : H ⊔ K ≤ normalizer (T : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    have key : ∀ g ∈ H ⊔ K, ∀ d ∈ T, g * d * g⁻¹ ∈ T := by
      rintro g hg d ⟨hd, hdc, hd3⟩
      refine ⟨(H ⊔ K).mul_mem ((H ⊔ K).mul_mem hg hd) ((H ⊔ K).inv_mem hg), fun f hf => ?_, ?_⟩
      · have hf' : g⁻¹ * f * g⁻¹⁻¹ ∈ H := (mem_normalizer_iff.mp (hNH ((H ⊔ K).inv_mem hg)) f).mp hf
        have := hdc _ hf'
        calc g * d * g⁻¹ * f = g * (d * (g⁻¹ * f * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * f * g) * d) * g⁻¹ := by simpa using congrArg (fun y => g * y * g⁻¹) this
          _ = f * (g * d * g⁻¹) := by group
      · rw [conj_pow, hd3]
        group
    intro d
    constructor
    · intro hd
      exact key g hg d hd
    · intro hd
      have := key g⁻¹ ((H ⊔ K).inv_mem hg) _ hd
      simpa [mul_assoc] using this
  have hT1 : T = ⊥ := hN3 T hTN hTp hnorm
  have : c ∈ T := ⟨hcN, hcc, hc3⟩
  rw [hT1, Subgroup.mem_bot] at this
  exact this


@[expose] def JoinStmt (G : Type) [Group G] (Q : Type) [Group Q] (m : ℕ) : Prop :=
  ∀ (H K : Subgroup G) (SH SK : Finset (Subgroup G)), SH.card + SK.card = m →
    (∀ F ∈ SH, Nonempty (↥F ≃* Q)) → (∀ F ∈ SK, Nonempty (↥F ≃* Q)) → PComm SH → PComm SK →
    SH.sup id = H → SK.sup id = K → H ⊔ K ≤ normalizer (H : Set G) →
    H ⊔ K ≤ normalizer (K : Set G) → NoNormal3 (H ⊔ K) → IsCommProd Q (H ⊔ K)

variable [Finite G] {Q : Type} [Group Q]

theorem perm_hyp {SH : Finset (Subgroup G)} (hQ : GoodQ Q) (hS : ∀ F ∈ SH, Nonempty (↥F ≃* Q))
    (hc : PComm SH) {k : G} (hk : k ∈ normalizer ((SH.sup id : Subgroup G) : Set G))
    {F : Subgroup G} (hF : F ∈ SH) :
    (∀ f ∈ F, k * f * k⁻¹ ∈ F) ∨
      (∀ f ∈ F, ∀ f' ∈ F, k * f * k⁻¹ * f' = f' * (k * f * k⁻¹)) := by
  have hmem := map_mem_of_map_eq hQ hS hc (MulAut.conj k) (map_conj_eq_of_mem_normalizer hk) hF
  by_cases heq : F.map (MulAut.conj k).toMonoidHom = F
  · left
    intro f hf
    have : k * f * k⁻¹ ∈ F.map (MulAut.conj k).toMonoidHom := Subgroup.mem_map.mpr ⟨f, hf, rfl⟩
    rwa [heq] at this
  · right
    intro f hf f' hf'
    have hcomm : ⁅F.map (MulAut.conj k).toMonoidHom, F⁆ = ⊥ :=
      hc (Finset.mem_coe.mpr hmem) (Finset.mem_coe.mpr hF) heq
    have : k * f * k⁻¹ ∈ F.map (MulAut.conj k).toMonoidHom := Subgroup.mem_map.mpr ⟨f, hf, rfl⟩
    exact (commute_of_commutator_eq_bot hcomm this hf').eq


omit [Finite G] in
theorem joinStmt_caseA (hQ : GoodQ Q) {m : ℕ} (IH : ∀ m' < m, JoinStmt G Q m')
    {H K : Subgroup G} {SH SK : Finset (Subgroup G)} (hcard : SH.card + SK.card = m)
    (hSH : ∀ F ∈ SH, Nonempty (↥F ≃* Q)) (hSK : ∀ F ∈ SK, Nonempty (↥F ≃* Q))
    (hcH : PComm SH) (hcK : PComm SK) (hH : SH.sup id = H) (hK : SK.sup id = K)
    (hnH : H ⊔ K ≤ normalizer (H : Set G)) (hnK : H ⊔ K ≤ normalizer (K : Set G))
    (hN3 : NoNormal3 (H ⊔ K)) {F : Subgroup G} (hF : F ∈ SH) (hFK : ⁅F, K⁆ = ⊥) :
    IsCommProd Q (H ⊔ K) := by
  classical
  have hQH : ∀ A ∈ SH, QFacts A := fun A hA => hQ.qFacts (hSH A hA).some
  set H0 := (SH.erase F).sup id with hH0
  have hsplit : H = F ⊔ H0 := by
    rw [← hH]
    conv_lhs => rw [← Finset.insert_erase hF]
    rw [Finset.sup_insert]
    rfl
  have hFH0 : ⁅F, H0⁆ = ⊥ := commutator_sup_eq_bot fun A hA =>
    hcH (Finset.mem_coe.mpr hF) (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hA))
      (Finset.ne_of_mem_erase hA).symm
  have hH0H : H0 ≤ H := hsplit ▸ le_sup_right
  have hKN : K ≤ H ⊔ K := le_sup_right
  have hHN : H ≤ H ⊔ K := le_sup_left
  have hFcK : ∀ f ∈ F, ∀ k ∈ K, f * k = k * f := fun f hf k hk =>
    (commute_of_commutator_eq_bot hFK hf hk).eq
  have hFcH0 : ∀ f ∈ F, ∀ x ∈ H0, f * x = x * f := fun f hf x hx =>
    (commute_of_commutator_eq_bot hFH0 hf hx).eq
  have hKH0 : K ≤ normalizer (H0 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk
    have hkH : k ∈ normalizer (H : Set G) := hnH (hKN hk)
    have key : ∀ x ∈ H0, k * x * k⁻¹ ∈ H0 := by
      let Hk : Subgroup G := H0.comap (MulAut.conj k).toMonoidHom
      have : H0 ≤ Hk := by
        refine le_of_three_of_commProd (S := SH.erase F) (H := Hk)
          (fun A hA => hQH A (Finset.mem_of_mem_erase hA))
          (hcH.mono (Finset.erase_subset _ _)) ?_
        intro x hx hx3
        show k * x * k⁻¹ ∈ H0
        have hxH : x ∈ H := hH0H hx
        have hy : k * x * k⁻¹ ∈ H := (mem_normalizer_iff.mp hkH x).mp hxH
        have hy3 : (k * x * k⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
        have hyc : ∀ f ∈ F, f * (k * x * k⁻¹) = (k * x * k⁻¹) * f := by
          intro f hf
          calc f * (k * x * k⁻¹) = (f * k) * x * k⁻¹ := by group
            _ = k * (f * x) * k⁻¹ := by rw [hFcK f hf k hk]; group
            _ = k * (x * f) * k⁻¹ := by rw [hFcH0 f hf x hx]
            _ = k * x * (f * k⁻¹) := by group
            _ = k * x * k⁻¹ * f := by
              have : f * k⁻¹ = k⁻¹ * f := by
                calc f * k⁻¹ = k⁻¹ * (k * f) * k⁻¹ := by group
                  _ = k⁻¹ * (f * k) * k⁻¹ := by rw [← hFcK f hf k hk]
                  _ = k⁻¹ * f := by group
              rw [this]; group
        obtain ⟨f', hf', r', hr', hfr⟩ := (mem_sup_of_commutator_eq_bot hFH0).mp (hsplit ▸ hy)
        have hf'c : ∀ g ∈ F, g * f' = f' * g := by
          intro g hg
          have h1 := hyc g hg
          rw [← hfr] at h1
          have h2 : g * r' = r' * g := (commute_of_commutator_eq_bot hFH0 hg hr').eq
          have : g * f' * r' = f' * g * r' := by
            calc g * f' * r' = g * (f' * r') := by rw [mul_assoc]
              _ = f' * r' * g := h1
              _ = f' * (r' * g) := by rw [mul_assoc]
              _ = f' * (g * r') := by rw [h2]
              _ = f' * g * r' := by rw [mul_assoc]
          exact mul_right_cancel this
        have hsq := (hQH F hF).center_sq f' hf' hf'c
        have hcm : Commute f' r' := commute_of_commutator_eq_bot hFH0 hf' hr'
        have h3 : f' * r' ^ 3 = 1 := by
          have := hy3
          rw [← hfr, hcm.mul_pow] at this
          have hf3 : f' ^ 3 = f' := by
            calc f' ^ 3 = f' * f' * f' := pow_three' f'
              _ = f' := by rw [hsq, one_mul]
          rwa [hf3] at this
        have hfr' : f' ∈ H0 := by
          have : f' = (r' ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
          rw [this]
          exact H0.inv_mem (H0.pow_mem hr' 3)
        rw [← hfr]
        exact H0.mul_mem hfr' hr'
      exact fun x hx => this hx
    exact key
  have hnH0 : H0 ⊔ K ≤ normalizer (H0 : Set G) := sup_le Subgroup.le_normalizer hKH0
  have hnK0 : H0 ⊔ K ≤ normalizer (K : Set G) :=
    sup_le ((hH0H.trans hHN).trans hnK) Subgroup.le_normalizer
  have hFcN : ∀ f ∈ F, ∀ g ∈ H0 ⊔ K, f * g = g * f := by
    have hle : H0 ⊔ K ≤ centralizer (F : Set G) := by
      refine sup_le (fun x hx => ?_) (fun k hk => ?_)
      · rw [mem_centralizer_iff]
        intro f hf
        exact hFcH0 f hf x hx
      · rw [mem_centralizer_iff]
        intro f hf
        exact hFcK f hf k hk
    intro f hf g hg
    exact (mem_centralizer_iff.mp (hle hg)) f hf
  have hsplit2 : H ⊔ K = F ⊔ (H0 ⊔ K) := by rw [hsplit, sup_assoc]
  have hN30 : NoNormal3 (H0 ⊔ K) := by
    intro P hPle hPp hPn
    have hFP : F ≤ normalizer (P : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro f hf p hp
      have : f * p * f⁻¹ = p := by
        rw [hFcN f hf p (hPle hp)]
        group
      rw [this]
      exact hp
    have hNP : H ⊔ K ≤ normalizer (P : Set G) := by
      rw [hsplit2]
      exact sup_le hFP hPn
    exact hN3 P (hPle.trans (sup_le_sup_right hH0H K)) hPp hNP
  have hlt : (SH.erase F).card + SK.card < m := by
    have := Finset.card_erase_lt_of_mem hF
    omega
  obtain ⟨S', hS'Q, hS'c, hS'sup⟩ := IH _ hlt H0 K (SH.erase F) SK rfl
    (fun A hA => hSH A (Finset.mem_of_mem_erase hA)) hSK (hcH.mono (Finset.erase_subset _ _)) hcK
    rfl hK hnH0 hnK0 hN30
  refine ⟨insert F S', ?_, ?_, ?_⟩
  · intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact hSH A hF
    · exact hS'Q A hA
  · rw [Finset.coe_insert]
    refine Set.pairwise_insert.mpr ⟨hS'c, fun b hb _ => ?_⟩
    have hb' : b ≤ H0 ⊔ K := hS'sup ▸ le_sup_of_mem (Finset.mem_coe.mp hb)
    have hFb : ⁅F, b⁆ = ⊥ := by
      have : ⁅F, H0 ⊔ K⁆ = ⊥ := by
        rw [commutator_eq_bot_iff_le_centralizer]
        intro f hf
        rw [mem_centralizer_iff]
        intro g hg
        exact (hFcN f hf g hg).symm
      exact le_bot_iff.mp (this ▸ Subgroup.commutator_mono_right hb')
    exact ⟨hFb, by rw [Subgroup.commutator_comm]; exact hFb⟩
  · rw [Finset.sup_insert, hsplit2]
    show F ⊔ S'.sup id = F ⊔ (H0 ⊔ K)
    rw [hS'sup]


theorem joinStmt_caseB (hQ : GoodQ Q)
    {K : Subgroup G} {SH SK : Finset (Subgroup G)}
    (hSH : ∀ F ∈ SH, Nonempty (↥F ≃* Q)) (hSK : ∀ F ∈ SK, Nonempty (↥F ≃* Q))
    (hcH : PComm SH) (hcK : PComm SK) (hK : SK.sup id = K)
    (hnH : SH.sup id ⊔ K ≤ normalizer ((SH.sup id : Subgroup G) : Set G))
    (hnK : SH.sup id ⊔ K ≤ normalizer (K : Set G)) (hN3 : NoNormal3 (SH.sup id ⊔ K))
    (hB : ∀ F ∈ SH, ⁅F, K⁆ ≠ ⊥) (hB' : ∀ F ∈ SK, ⁅F, (SH.sup id : Subgroup G)⁆ ≠ ⊥) :
    IsCommProd Q (SH.sup id ⊔ K) := by
  have hQH : ∀ A ∈ SH, QFacts A := fun A hA => hQ.qFacts (hSH A hA).some
  have hQK : ∀ A ∈ SK, QFacts A := fun A hA => hQ.qFacts (hSK A hA).some
  have hHle : SH.sup id ≤ SH.sup id ⊔ K := le_sup_left
  have hKle : K ≤ SH.sup id ⊔ K := le_sup_right
  have hB1 : ∀ F ∈ SH, twoSet F ⊆ K := by
    intro F hF
    have hFN : F ≤ normalizer (K : Set G) := (le_sup_of_mem hF).trans (hHle.trans hnK)
    have hperm : ∀ k ∈ K, (∀ f ∈ F, k * f * k⁻¹ ∈ F) ∨
        (∀ f ∈ F, ∀ f' ∈ F, k * f * k⁻¹ * f' = f' * (k * f * k⁻¹)) := fun k hk =>
      perm_hyp hQ hSH hcH (hnH (hKle hk)) hF
    exact (commutator_eq_bot_or_twoSet_le (hQH F hF) hFN hperm).resolve_left (hB F hF)
  have hB2 : ∀ F ∈ SK, twoSet F ⊆ ((SH.sup id : Subgroup G) : Set G) := by
    intro F hF
    have hFN : F ≤ normalizer ((SH.sup id : Subgroup G) : Set G) :=
      ((hK ▸ le_sup_of_mem hF : F ≤ K).trans hKle).trans hnH
    have hperm : ∀ h ∈ SH.sup id, (∀ f ∈ F, h * f * h⁻¹ ∈ F) ∨
        (∀ f ∈ F, ∀ f' ∈ F, h * f * h⁻¹ * f' = f' * (h * f * h⁻¹)) := fun h hh =>
      perm_hyp hQ hSK hcK (by rw [hK]; exact hnK (hHle hh)) hF
    exact (commutator_eq_bot_or_twoSet_le (hQK F hF) hFN hperm).resolve_left (hB' F hF)
  have hKK : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ SH.sup id := by
    intro k hk k' hk'
    have h4 := comm_two_of_commProd hQK hcK k (hK ▸ hk) k' (hK ▸ hk')
    exact two_mem_of_commProd hQK hcK
      (fun A hA f hf hf4 => hB2 A hA ⟨hf, hf4⟩) _ (hK ▸ commutator_mem_self (hK ▸ hk) (hK ▸ hk')) h4
  have hKH : K ≤ normalizer ((SH.sup id : Subgroup G) : Set G) := hKle.trans hnH
  have hKleH : K ≤ SH.sup id := by
    rw [← hK]
    refine le_of_three_of_commProd hQK hcK ?_
    intro x hx hx3
    have hxK : x ∈ K := hK ▸ hx
    have hxN : x ∈ normalizer ((SH.sup id : Subgroup G) : Set G) := hnH (hKle hxK)
    have hperm : ∀ F ∈ SH, F.map (MulAut.conj x).toMonoidHom ∈ SH := fun F hF =>
      map_mem_of_map_eq hQ hSH hcH (MulAut.conj x) (map_conj_eq_of_mem_normalizer hxN) hF
    have hfix : ∀ F ∈ SH, F.map (MulAut.conj x).toMonoidHom = F := fun F hF =>
      conj_eq_of_cube hQH hcH hQK hcK hx hx3 (by rw [hK]; exact hHle.trans hnK) hperm hF
    have houter : ∀ F ∈ SH, ∃ h ∈ F, h ^ 3 = 1 ∧ ∀ f ∈ F, x * f * x⁻¹ = h * f * h⁻¹ :=
      fun F hF => (hQH F hF).outer3 x (mem_normalizer_of_map_conj_eq (hfix F hF)) hx3
    obtain ⟨h, hhH, hh3, hha⟩ := inner_of_commProd hQH hcH x houter
    have hcc : ∀ f ∈ SH.sup id, h⁻¹ * x * f = f * (h⁻¹ * x) := by
      intro f hf
      have := hha f hf
      calc h⁻¹ * x * f = h⁻¹ * (x * f * x⁻¹) * x := by group
        _ = h⁻¹ * (h * f * h⁻¹) * x := by rw [this]
        _ = f * (h⁻¹ * x) := by group
    have hcN : h⁻¹ * x ∈ SH.sup id ⊔ K :=
      (SH.sup id ⊔ K).mul_mem ((SH.sup id ⊔ K).inv_mem (hHle hhH)) (hKle hxK)
    have hc3 : (h⁻¹ * x) ^ 3 = 1 := by
      have hxc : x = h * (h⁻¹ * x) := by group
      have hcomm : Commute h (h⁻¹ * x) := (hcc h hhH).symm
      have := hcomm.mul_pow 3
      rw [← hxc, hx3, hh3, one_mul] at this
      exact this.symm
    have hc1 := eq_one_of_centralizes hQH hcH hKH hKK hN3 hcN hcc hc3
    have hxh : x = h := by
      have : h⁻¹ * x = 1 := hc1
      calc x = h * (h⁻¹ * x) := by group
        _ = h := by rw [this, mul_one]
    rw [hxh]
    exact hhH
  rw [sup_eq_left.mpr hKleH]
  exact ⟨SH, hSH, hcH, rfl⟩


theorem joinStmt (hQ : GoodQ Q) (m : ℕ) : JoinStmt G Q m := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro H K SH SK hcard hSH hSK hcH hcK hH hK hnH hnK hN3
    by_cases hA : ∃ F ∈ SH, ⁅F, K⁆ = ⊥
    · obtain ⟨F, hF, hFK⟩ := hA
      exact joinStmt_caseA hQ IH hcard hSH hSK hcH hcK hH hK hnH hnK hN3 hF hFK
    by_cases hA' : ∃ F ∈ SK, ⁅F, H⁆ = ⊥
    · obtain ⟨F, hF, hFH⟩ := hA'
      have := joinStmt_caseA hQ IH (H := K) (K := H) (SH := SK) (SK := SH) (by omega)
        hSK hSH hcK hcH hK hH (by rwa [sup_comm]) (by rwa [sup_comm]) (by rwa [sup_comm]) hF hFH
      rwa [sup_comm] at this
    push Not at hA hA'
    subst hH
    subst hK
    exact joinStmt_caseB hQ hSH hSK hcH hcK rfl hnH hnK hN3 hA hA'

theorem isCommProd_sup (hQ : GoodQ Q) {H K : Subgroup G} (hH : IsCommProd Q H)
    (hK : IsCommProd Q K) (hnH : H ⊔ K ≤ normalizer (H : Set G))
    (hnK : H ⊔ K ≤ normalizer (K : Set G)) (hN3 : NoNormal3 (H ⊔ K)) :
    IsCommProd Q (H ⊔ K) := by
  obtain ⟨SH, hSH, hcH, hSHsup⟩ := hH
  obtain ⟨SK, hSK, hcK, hSKsup⟩ := hK
  exact joinStmt hQ _ H K SH SK rfl hSH hSK hcH hcK hSHsup hSKsup hnH hnK hN3

end CFSG.OddStandard.Solomon75
