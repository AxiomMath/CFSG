module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapGamma
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapDS
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Suzuki

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Matrix

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace GapSuz

omit [Finite X] in
theorem mem_zpowers_of_sq {a x : X} (ha : a * a = 1) (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · left; rw [hm, zpow_mul, zpow_two, ha, one_zpow]
  · right; rw [hm, zpow_add, zpow_mul, zpow_two, ha, one_zpow, one_mul, zpow_one]

@[expose] noncomputable def K0 (F : S.Frame) : Subgroup X := zpowers F.kF ⊔ zpowers S.t

theorem mem_K0 {x : X} (hx : x ∈ K0 F) : x = 1 ∨ x = F.kF ∨ x = S.t ∨ x = S.t * F.kF := by
  have hk2 : F.kF * F.kF = 1 := by rw [← pow_two]; exact F.kF_sq
  have htk : S.t * F.kF * S.t⁻¹ = F.kF := by
    rw [show S.t * F.kF = F.kF * S.t from
      (commute_of_mem_B t_mem_B (kF_mem_B F)), mul_inv_cancel_right]
  have hn : ∀ h ∈ zpowers F.kF, S.t * h * S.t⁻¹ ∈ zpowers F.kF := fun h hh => by
    rcases GapSuz.mem_zpowers_of_sq hk2 hh with rfl | rfl
    · simp
    · rw [htk]; exact mem_zpowers _
  rcases mem_or_mem_of_mem_sup (by rw [t_mul_t]; exact one_mem _) hn hx with h | h
  · rcases GapSuz.mem_zpowers_of_sq hk2 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have ht' : S.t⁻¹ = S.t := by rw [inv_eq_iff_mul_eq_one, t_mul_t]
    rcases GapSuz.mem_zpowers_of_sq hk2 h with h | h
    · right; right; left
      rw [ht'] at h
      calc x = S.t * (S.t * x) := by rw [← mul_assoc, t_mul_t, one_mul]
        _ = S.t := by rw [h, mul_one]
    · right; right; right
      rw [ht'] at h
      calc x = S.t * (S.t * x) := by rw [← mul_assoc, t_mul_t, one_mul]
        _ = S.t * F.kF := by rw [h]

end GapSuz

namespace BData

variable (A : BData S F T₁)

@[expose] noncomputable def VV : Subgroup X where
  carrier := {g | ∃ v : Fin 3 → ZMod 4, v 2 = 0 ∧ A.Φ v = g}
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, by simp [hv, hw], A.Φ_add v w⟩
  one_mem' := ⟨0, rfl, A.Φ_zero⟩
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨-v, by simp [hv], A.Φ_neg v⟩

theorem Φ_mem_VV_iff (v : Fin 3 → ZMod 4) : A.Φ v ∈ A.VV ↔ v 2 = 0 := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    rw [← A.Φ_injective hwv, hw]
  · intro h; exact ⟨v, h, rfl⟩

theorem VV_le_AA : A.VV ≤ A.AA := by
  rintro _ ⟨v, -, rfl⟩; exact A.Φ_mem v

theorem kF_not_mem_VV : F.kF ∉ A.VV := by
  rw [← A.Φ_k, Φ_mem_VV_iff]; decide

theorem t_not_mem_AA : S.t ∉ A.AA := by
  intro ht
  have h1 := (A.t_conj_eq_iff ![1, 0, 0]).mp (by rw [A.AA_comm ht (A.Φ_mem _),
    mul_inv_cancel_right]) 0
  revert h1; decide

theorem t_conj_VV {h : X} (hh : h ∈ A.VV) : S.t * h * S.t⁻¹ ∈ A.VV := by
  obtain ⟨v, hv, rfl⟩ := hh
  rw [A.t_conj_Φ]; exact ⟨-v, by simp [hv], rfl⟩

theorem t_mem_normalizer_VV : S.t ∈ normalizer (A.VV : Set X) := by
  rw [mem_normalizer_iff]
  intro h
  refine ⟨A.t_conj_VV, fun hh => ?_⟩
  have := A.t_conj_VV hh
  rwa [show S.t * (S.t * h * S.t⁻¹) * S.t⁻¹ = h by
    rw [show S.t⁻¹ = S.t by rw [inv_eq_iff_mul_eq_one, t_mul_t]]
    rw [← mul_assoc, ← mul_assoc, t_mul_t, one_mul, mul_assoc, t_mul_t, mul_one]] at this

theorem K0_inf_VV {x : X} (hx : x ∈ GapSuz.K0 F) (hV : x ∈ A.VV) : x = 1 := by
  rcases GapSuz.mem_K0 hx with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd hV A.kF_not_mem_VV
  · exact absurd (A.VV_le_AA hV) A.t_not_mem_AA
  · exfalso
    apply A.t_not_mem_AA
    have hk : F.kF ∈ A.AA := A.Φ_k ▸ A.Φ_mem _
    have := mul_mem (A.VV_le_AA hV) (inv_mem hk)
    rwa [mul_inv_cancel_right] at this

namespace Syl

variable {A} (Y : A.Syl)

@[expose] noncomputable def R : Subgroup X := Y.Q ⊔ zpowers S.t

theorem Q_le_R : Y.Q ≤ Y.R := le_sup_left

theorem t_mem_R : S.t ∈ Y.R := mem_sup_right (mem_zpowers _)

theorem VV_le_R : A.VV ≤ Y.R := (A.VV_le_AA.trans Y.AA_le_Q).trans Y.Q_le_R

theorem R_le_P : Y.R ≤ Y.P := sup_le inf_le_left (zpowers_le.mpr Y.t_mem)

theorem isPGroup_R : IsPGroup 2 Y.R := Y.isPGroup.to_le Y.R_le_P

theorem VV_central {g : X} (hg : g ∈ Y.Q) {h : X} (hh : h ∈ A.VV) : g * h = h * g :=
  ((mem_centralizer_iff.mp (mem_inf.mp hg).2) h (A.VV_le_AA hh)).symm

theorem Q_le_centralizer_VV : Y.Q ≤ centralizer (A.VV : Set X) := fun _ hg =>
  mem_centralizer_iff.mpr fun _ hh => (Y.VV_central hg hh).symm

theorem R_le_normalizer_VV : Y.R ≤ normalizer (A.VV : Set X) :=
  sup_le (Y.Q_le_centralizer_VV.trans (centralizer_le_normalizer _))
    (zpowers_le.mpr A.t_mem_normalizer_VV)

instance VV_normal : (A.VV.subgroupOf Y.R).Normal :=
  (normal_subgroupOf_iff_le_normalizer Y.VV_le_R).mpr Y.R_le_normalizer_VV

abbrev RV : Type := Y.R ⧸ A.VV.subgroupOf Y.R

noncomputable def pi : Y.R →* Y.RV := QuotientGroup.mk' _

theorem pi_surjective : Function.Surjective Y.pi := QuotientGroup.mk'_surjective _

theorem pi_eq_one_iff (r : Y.R) : Y.pi r = 1 ↔ (r : X) ∈ A.VV := by
  rw [pi, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem pi_eq_iff (r s : Y.R) : Y.pi r = Y.pi s ↔ ((r : X))⁻¹ * s ∈ A.VV := by
  rw [pi, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
  simp

theorem isPGroup_RV : IsPGroup 2 Y.RV :=
  Y.isPGroup_R.of_surjective Y.pi Y.pi_surjective

theorem AA_le_R : A.AA ≤ Y.R := Y.AA_le_Q.trans Y.Q_le_R

@[expose] noncomputable def tR : Y.R := ⟨S.t, Y.t_mem_R⟩

@[expose] noncomputable def kR : Y.R := ⟨F.kF, Y.AA_le_R (A.Φ_k ▸ A.Φ_mem _)⟩

@[expose] noncomputable def cR : Y.R := ⟨A.Φ ![0, 0, 1], Y.AA_le_R (A.Φ_mem _)⟩

theorem K0_le_R : GapSuz.K0 F ≤ Y.R :=
  sup_le (zpowers_le.mpr Y.kR.2) (zpowers_le.mpr Y.t_mem_R)

@[expose] noncomputable def UU : Subgroup Y.RV := ((GapSuz.K0 F).subgroupOf Y.R).map Y.pi

theorem card_UU : Nat.card Y.UU = 4 := by
  have hinj : Function.Injective (Y.pi.comp ((GapSuz.K0 F).subgroupOf Y.R).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, pi_eq_one_iff] at hx
    have h1 := A.K0_inf_VV (x.2 : ((x : Y.R) : X) ∈ GapSuz.K0 F) hx
    rw [mem_bot]
    exact Subtype.ext (Subtype.ext h1)
  have hrange : (Y.pi.comp ((GapSuz.K0 F).subgroupOf Y.R).subtype).range = Y.UU := by
    rw [UU, MonoidHom.range_comp, range_subtype]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
    Nat.card_congr (subgroupOfEquivOfLe Y.K0_le_R).toEquiv]
  exact A.V₁.card_kt

theorem UU_sq {u : Y.RV} (hu : u ∈ Y.UU) : u ^ 2 = 1 := by
  obtain ⟨x, hx, rfl⟩ := hu
  rw [← map_pow]
  have hx' : ((x : Y.R) : X) ∈ GapSuz.K0 F := hx
  have hsq : ((x : Y.R) : X) ^ 2 = 1 := by
    rcases GapSuz.mem_K0 hx' with h | h | h | h <;> rw [h]
    · exact one_pow 2
    · exact F.kF_sq
    · exact S.t_sq
    · rw [(Commute.mul_pow (commute_of_mem_B t_mem_B (kF_mem_B F)) 2), S.t_sq, F.kF_sq,
        one_mul]
  have : x ^ 2 = 1 := Subtype.ext (by simpa using hsq)
  rw [this, map_one]

theorem exists_of_comm_t_mod (hnc : ¬ SubConj F.E₁ F.E₂) {q : X} (hq : q ∈ Y.Q)
    (hc : q * S.t * q⁻¹ * S.t⁻¹ ∈ A.VV) : ∃ w : Fin 3 → ZMod 4, 2 * w 2 = 0 ∧ A.Φ w = q := by
  obtain ⟨v, hv2, hv⟩ := hc
  have ht' : S.t⁻¹ = S.t := by rw [inv_eq_iff_mul_eq_one, t_mul_t]
  have hconj : q * S.t * q⁻¹ = S.t * A.Φ (-v) := by
    have h1 : q * S.t * q⁻¹ = A.Φ v * S.t := by rw [hv]; group
    rw [h1, ← A.t_conj_Φ, ht']
    rw [show S.t * (S.t * A.Φ v * S.t) = (S.t * S.t) * A.Φ v * S.t by group, t_mul_t, one_mul]
  obtain ⟨h0, h1⟩ := A.two_mul_of_conj_t hnc (mem_inf.mp hq).2 hconj
  have hev : ∀ i, 2 * (-v) i = 0 := by
    intro i; fin_cases i
    · exact h0
    · exact h1
    · simp [hv2]
  obtain ⟨w, rfl⟩ := A.mem_AA.mp
    (Y.mem_AA_of_Q_normalizes hq (A.mem_normalizer_E₁ (mem_inf.mp hq).2 hconj hev))
  refine ⟨w, ?_, rfl⟩
  have e1 : A.Φ w * S.t * (A.Φ w)⁻¹ * S.t⁻¹ = A.Φ (w + w) := by
    rw [A.Φ_add, ← A.Φ_neg, show A.Φ w * S.t * A.Φ (-w) * S.t⁻¹ =
      A.Φ w * (S.t * A.Φ (-w) * S.t⁻¹) by group, A.t_conj_Φ, neg_neg]
  have := congrFun (A.Φ_injective (hv.trans e1)) 2
  rw [hv2, Pi.add_apply, ← two_mul] at this
  exact this.symm

theorem UU_ne_top : Y.UU ≠ ⊤ := by
  intro htop
  have hc : Y.pi Y.cR ∈ Y.UU := htop ▸ mem_top _
  obtain ⟨x, hx, hxc⟩ := hc
  rw [pi_eq_iff] at hxc
  have hx' : ((x : Y.R) : X) ∈ GapSuz.K0 F := hx
  have hk : F.kF = A.Φ ![0, 0, 2] := A.Φ_k.symm
  rcases GapSuz.mem_K0 hx' with h | h | h | h <;> rw [h] at hxc
  · rw [inv_one, one_mul] at hxc
    have := (A.Φ_mem_VV_iff _).mp hxc
    revert this; decide
  · rw [hk, ← A.Φ_neg, show (Y.cR : X) = A.Φ ![0, 0, 1] from rfl, ← A.Φ_add,
      A.Φ_mem_VV_iff] at hxc
    revert hxc; decide
  · apply A.t_not_mem_AA
    have := mul_mem (A.Φ_mem ![0, 0, 1]) (inv_mem (A.VV_le_AA hxc))
    rwa [show A.Φ ![0, 0, 1] * (S.t⁻¹ * (Y.cR : X))⁻¹ = S.t by
      rw [show (Y.cR : X) = A.Φ ![0, 0, 1] from rfl]; group] at this
  · apply A.t_not_mem_AA
    have hkA : F.kF ∈ A.AA := hk ▸ A.Φ_mem _
    have := mul_mem (mul_mem (A.Φ_mem ![0, 0, 1]) (inv_mem (A.VV_le_AA hxc))) (inv_mem hkA)
    rwa [show A.Φ ![0, 0, 1] * ((S.t * F.kF)⁻¹ * (Y.cR : X))⁻¹ * F.kF⁻¹ = S.t by
      rw [show (Y.cR : X) = A.Φ ![0, 0, 1] from rfl]; group] at this

theorem centralizer_UU_le (hnc : ¬ SubConj F.E₁ F.E₂) :
    (⊤ : Subgroup Y.RV) ⊓ centralizer (Y.UU : Set Y.RV) ≤ Y.UU := by
  rintro g ⟨-, hg⟩
  have htU : Y.pi Y.tR ∈ Y.UU := ⟨Y.tR, (mem_sup_right (mem_zpowers _) : S.t ∈ GapSuz.K0 F),
    rfl⟩
  have hgt := mem_centralizer_iff.mp hg _ htU
  obtain ⟨r, rfl⟩ := Y.pi_surjective g
  have key : ∀ q : Y.R, (q : X) ∈ Y.Q → Y.pi q * Y.pi Y.tR = Y.pi Y.tR * Y.pi q →
      Y.pi q ∈ Y.UU := by
    intro q hq hqt
    have hc : (q : X) * S.t * (q : X)⁻¹ * S.t⁻¹ ∈ A.VV := by
      have h1 : Y.pi (q * Y.tR * q⁻¹ * Y.tR⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hqt]; group
      exact (Y.pi_eq_one_iff _).mp h1
    obtain ⟨w, hw2, hw⟩ := Y.exists_of_comm_t_mod hnc hq hc
    have hsplit : A.Φ w = A.Φ ![w 0, w 1, 0] * A.Φ ![0, 0, w 2] := by
      rw [← A.Φ_add]; congr 1; funext i; fin_cases i <;> simp
    have hk : A.Φ ![0, 0, w 2] = 1 ∨ A.Φ ![0, 0, w 2] = F.kF := by
      rcases (show ∀ x : ZMod 4, 2 * x = 0 → x = 0 ∨ x = 2 by decide) _ hw2 with h | h <;>
        rw [h]
      · left; rw [show (![0, 0, 0] : Fin 3 → ZMod 4) = 0 by decide, A.Φ_zero]
      · right; exact A.Φ_k
    have hmem : A.Φ ![0, 0, w 2] ∈ GapSuz.K0 F := by
      rcases hk with h | h <;> rw [h]
      · exact one_mem _
      · exact mem_sup_left (mem_zpowers _)
    refine ⟨⟨A.Φ ![0, 0, w 2], (Y.K0_le_R hmem)⟩, hmem, ?_⟩
    rw [pi_eq_iff]
    change (A.Φ ![0, 0, w 2])⁻¹ * (q : X) ∈ A.VV
    rw [← hw, hsplit, show (A.Φ ![0, 0, w 2])⁻¹ * (A.Φ ![w 0, w 1, 0] * A.Φ ![0, 0, w 2]) =
      A.Φ ![w 0, w 1, 0] by rw [A.Φ_comm]; group]
    exact (A.Φ_mem_VV_iff _).mpr rfl
  have hn : ∀ h ∈ Y.Q, S.t * h * S.t⁻¹ ∈ Y.Q := fun h hh =>
    (mem_normalizer_iff.mp Y.t_inv_mem_Q h).mp hh
  rcases mem_or_mem_of_mem_sup (by rw [t_mul_t]; exact one_mem _) hn r.2 with h | h
  · exact key r h hgt.symm
  · have hq : (((Y.tR⁻¹ * r : Y.R)) : X) ∈ Y.Q := h
    have hcomm : Y.pi (Y.tR⁻¹ * r) * Y.pi Y.tR = Y.pi Y.tR * Y.pi (Y.tR⁻¹ * r) := by
      rw [map_mul, map_inv]
      calc (Y.pi Y.tR)⁻¹ * Y.pi r * Y.pi Y.tR = (Y.pi Y.tR)⁻¹ * (Y.pi r * Y.pi Y.tR) := by
            group
        _ = (Y.pi Y.tR)⁻¹ * (Y.pi Y.tR * Y.pi r) := by rw [hgt]
        _ = Y.pi Y.tR * ((Y.pi Y.tR)⁻¹ * Y.pi r) := by group
    have := mul_mem htU (key _ hq hcomm)
    rwa [map_mul, map_inv, mul_inv_cancel_left] at this

@[expose] noncomputable def QV : Subgroup Y.RV := (Y.Q.subgroupOf Y.R).map Y.pi

theorem t_not_mem_Q : S.t ∉ Y.Q := fun h => by
  have h1 := (mem_inf.mp h).2
  have := mem_centralizer_iff.mp h1 _ (A.Φ_mem ![1, 0, 0])
  have h2 := (A.t_conj_eq_iff ![1, 0, 0]).mp (by rw [← this, mul_inv_cancel_right]) 0
  revert h2; decide

theorem index_Q : (Y.Q.subgroupOf Y.R).index = 2 := by
  rw [index_eq_two_iff]
  refine ⟨Y.tR, fun b => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf]
  have ht' : S.t⁻¹ = S.t := by rw [inv_eq_iff_mul_eq_one, t_mul_t]
  have hn : ∀ h ∈ Y.Q, S.t * h * S.t⁻¹ ∈ Y.Q := fun h hh =>
    (mem_normalizer_iff.mp Y.t_inv_mem_Q h).mp hh
  change Xor ((b : X) * S.t ∈ Y.Q) ((b : X) ∈ Y.Q)
  rcases mem_or_mem_of_mem_sup (by rw [t_mul_t]; exact one_mem _) hn b.2 with h | h
  · refine Or.inr ⟨h, fun h' => Y.t_not_mem_Q ?_⟩
    have := mul_mem (inv_mem h) h'
    rwa [inv_mul_cancel_left] at this
  · refine Or.inl ⟨?_, fun h' => Y.t_not_mem_Q ?_⟩
    · have := hn _ h
      rwa [ht', show S.t * (S.t * (b : X)) * S.t = (S.t * S.t) * (b : X) * S.t by group,
        t_mul_t, one_mul] at this
    · have := mul_mem h (inv_mem h')
      rwa [ht', mul_inv_cancel_right] at this

theorem index_QV : Y.QV.index = 2 := by
  have hker : Y.pi.ker ≤ Y.Q.subgroupOf Y.R := by
    intro x hx
    rw [MonoidHom.mem_ker, pi_eq_one_iff] at hx
    exact (A.VV_le_AA.trans Y.AA_le_Q) hx
  exact (Subgroup.index_map_eq _ Y.pi_surjective hker).trans Y.index_Q

theorem card_QV : 2 * Nat.card Y.QV = Nat.card Y.RV := by
  rw [← Y.QV.card_mul_index, Y.index_QV, mul_comm]

theorem mem_QV_of {q : Y.R} (hq : (q : X) ∈ Y.Q) : Y.pi q ∈ Y.QV := ⟨q, hq, rfl⟩

theorem comm_cR {x : Y.RV} (hx : x ∈ Y.QV) : x * Y.pi Y.cR = Y.pi Y.cR * x := by
  obtain ⟨q, hq, rfl⟩ := hx
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change (q : X) * A.Φ ![0, 0, 1] = A.Φ ![0, 0, 1] * (q : X)
  exact ((mem_centralizer_iff.mp (mem_inf.mp hq).2) _ (A.Φ_mem _)).symm

theorem orderOf_cR : orderOf (Y.pi Y.cR) = 4 := by
  have hk : Y.cR ^ 2 = Y.kR := Subtype.ext (by
    change A.Φ ![0, 0, 1] ^ 2 = F.kF
    rw [← A.Φ_nsmul, ← A.Φ_k]; congr 1; decide)
  have h4 : Y.pi Y.cR ^ 2 ^ 2 = 1 := by
    have : Y.cR ^ 2 ^ 2 = 1 := Subtype.ext (by
      change A.Φ ![0, 0, 1] ^ 2 ^ 2 = 1
      rw [← A.Φ_nsmul, ← A.Φ_zero]; congr 1; decide)
    rw [← map_pow, this, map_one]
  have h2 : ¬ Y.pi Y.cR ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, hk, pi_eq_one_iff]
    exact A.kF_not_mem_VV
  exact orderOf_eq_prime_pow h2 h4

theorem isCyclic_QV (hnc : ¬ SubConj F.E₁ F.E₂) : IsCyclic Y.QV := by
  have hT : IsPGroup 2 (⊤ : Subgroup Y.RV) := Y.isPGroup_RV.to_subgroup ⊤
  rcases QuasithinUnique.suzuki_selfCentralizing_four hT le_top Y.card_UU
    (fun u hu => Y.UU_sq hu) (Y.centralizer_UU_le hnc) Y.UU_ne_top with
    ⟨m, -, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · let e' : Y.RV ≃* DihedralGroup (2 ^ m) := Subgroup.topEquiv.symm.trans e
    have hc4 : orderOf (e' (Y.pi Y.cR)) = 4 := by rw [MulEquiv.orderOf_eq, Y.orderOf_cR]
    have hle : Y.QV.map e'.toMonoidHom ≤ zpowers (DihedralGroup.r (1 : ZMod (2 ^ m))) := by
      rintro _ ⟨x, hx, rfl⟩
      refine GapDS.dihedral_rot_le _ (GapDS.dihedral_rot_of_comm hc4 ?_)
      change e' x * e' (Y.pi Y.cR) = e' (Y.pi Y.cR) * e' x
      rw [← map_mul, ← map_mul, Y.comm_cR hx]
    have : IsCyclic (Y.QV.map e'.toMonoidHom) := Subgroup.isCyclic_of_le hle
    exact isCyclic_of_injective (Y.QV.equivMapOfInjective e'.toMonoidHom e'.injective).toMonoidHom
      (Y.QV.equivMapOfInjective e'.toMonoidHom e'.injective).injective
  · have : Finite (CFSG.Open.SemidihedralGroup m) :=
      CFSG.Semidihedral.presentation_finite m (by omega)
    let e' : Y.RV ≃* CFSG.Open.SemidihedralGroup m := Subgroup.topEquiv.symm.trans e
    have hc4 : orderOf (e' (Y.pi Y.cR)) = 4 := by rw [MulEquiv.orderOf_eq, Y.orderOf_cR]
    have hcard : Nat.card Y.RV = 2 ^ m := by
      rw [Nat.card_congr e'.toEquiv, CFSG.Semidihedral.card m (by omega)]
    have hQV8 : 4 < Nat.card Y.QV := by
      have h1 := Y.card_QV
      rw [hcard] at h1
      have h2 : 16 ≤ 2 ^ m := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    have hsub : Y.QV.map e'.toMonoidHom ≤
        centralizer ({e' (Y.pi Y.cR)} : Set (CFSG.Open.SemidihedralGroup m)) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_singleton_iff]
      change e' x * e' (Y.pi Y.cR) = e' (Y.pi Y.cR) * e' x
      rw [← map_mul, ← map_mul, Y.comm_cR hx]
    have hC : 4 < Nat.card (centralizer ({e' (Y.pi Y.cR)} :
        Set (CFSG.Open.SemidihedralGroup m))) := by
      calc 4 < Nat.card Y.QV := hQV8
        _ = Nat.card (Y.QV.map e'.toMonoidHom) :=
          Nat.card_congr (Y.QV.equivMapOfInjective e'.toMonoidHom e'.injective).toEquiv
        _ ≤ _ := Subgroup.card_le_of_le hsub
    have hle : Y.QV.map e'.toMonoidHom ≤ CFSG.Semidihedral.rotationSubgroup m :=
      fun x hx => GapDS.sd_rot_of_comm hm hc4 hC (hsub hx)
    have : IsCyclic (CFSG.Semidihedral.rotationSubgroup m) := by
      unfold CFSG.Semidihedral.rotationSubgroup; infer_instance
    have : IsCyclic (Y.QV.map e'.toMonoidHom) := Subgroup.isCyclic_of_le hle
    exact isCyclic_of_injective (Y.QV.equivMapOfInjective e'.toMonoidHom e'.injective).toMonoidHom
      (Y.QV.equivMapOfInjective e'.toMonoidHom e'.injective).injective

noncomputable def piQ : Y.Q →* Y.QV :=
  ((Y.pi.comp (Subgroup.inclusion Y.Q_le_R)).codRestrict Y.QV fun q => Y.mem_QV_of q.2)

theorem piQ_ker_le_center : Y.piQ.ker ≤ center Y.Q := by
  intro q hq
  rw [MonoidHom.mem_ker] at hq
  have hq' : Y.pi (Subgroup.inclusion Y.Q_le_R q) = 1 := congrArg Subtype.val hq
  rw [pi_eq_one_iff] at hq'
  rw [mem_center_iff]
  intro g
  exact Subtype.ext (Y.VV_central g.2 hq')

theorem Q_comm (hnc : ¬ SubConj F.E₁ F.E₂) {a b : X} (ha : a ∈ Y.Q) (hb : b ∈ Y.Q) :
    a * b = b * a := by
  have := Y.isCyclic_QV hnc
  have h := (Y.piQ.isMulCommutative_of_isCyclic_of_ker_le_center Y.piQ_ker_le_center).is_comm.comm
    ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val h

end Syl

end BData

end Sec8

end CFSG.ComponentClassification.HSFLit
