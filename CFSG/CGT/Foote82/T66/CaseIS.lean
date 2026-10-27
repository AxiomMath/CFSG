module

public import CFSG.CGT.Foote82.T66.CaseISq
import CFSG.GH74.Uniqueness.SU.SU10Fusion
import CFSG.CGT.Foote82.T66.OddTranspTools

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart

section Groups

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_max_normalized (K R : Subgroup Γ) (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set Γ)) :
    ∃ S : Subgroup Γ, S ≤ K ∧ IsPGroup 2 S ∧ R ⊓ K ≤ S ∧
      (∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S) ∧
      ∀ Q : Subgroup Γ, Q ≤ K → IsPGroup 2 Q → Nat.card Q ≤ Nat.card S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup Γ := R ⊔ K with hM
  have hRM : R ≤ M := le_sup_left
  have hKM : K ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (K : Set Γ) := sup_le hRK Subgroup.le_normalizer
  haveI hKn : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hMN
  have hR' : IsPGroup 2 (R.subgroupOf M) := hR.comap_subtype
  obtain ⟨P, hP⟩ := hR'.exists_le_sylow
  refine ⟨((P : Subgroup ↥M) ⊓ K.subgroupOf M).map M.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.1 hx
  · exact (P.isPGroup'.to_inf_left).map M.subtype
  · rintro x ⟨hxR, hxK⟩
    exact ⟨⟨x, hRM hxR⟩, ⟨hP (Subgroup.mem_subgroupOf.2 hxR), Subgroup.mem_subgroupOf.2 hxK⟩,
      rfl⟩
  · rintro r hr _ ⟨s, ⟨hsP, hsK⟩, rfl⟩
    have hrP : (⟨r, hRM hr⟩ : ↥M) ∈ (P : Subgroup ↥M) := hP (Subgroup.mem_subgroupOf.2 hr)
    refine ⟨⟨r, hRM hr⟩ * s * ⟨r, hRM hr⟩⁻¹, ⟨?_, ?_⟩, rfl⟩
    · exact P.mul_mem (P.mul_mem hrP hsP) (P.inv_mem hrP)
    · exact hKn.conj_mem s hsK _
  · intro Q hQK hQ
    have hQ' : IsPGroup 2 (Q.subgroupOf M) := hQ.comap_subtype
    obtain ⟨P₂, hP₂⟩ := hQ'.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥M P₂ P
    have hle : (Q.subgroupOf M).map (MulAut.conj g).toMonoidHom ≤
        (P : Subgroup ↥M) ⊓ K.subgroupOf M := by
      rintro _ ⟨q, hq, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hg, Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ (hP₂ hq)
      · exact hKn.conj_mem q (Subgroup.mem_subgroupOf.2 (hQK (Subgroup.mem_subgroupOf.1 hq))) g
    have h1 : Nat.card Q = Nat.card (Q.subgroupOf M) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hQK.trans hKM)).toEquiv).symm
    have h2 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h2
    rw [Subgroup.card_map_of_injective M.subtype_injective, h1]
    exact h2

theorem exists_conj_of_max {K S₁ S₂ : Subgroup Γ} (h₁K : S₁ ≤ K) (h₁ : IsPGroup 2 S₁)
    (h₁max : ∀ Q : Subgroup Γ, Q ≤ K → IsPGroup 2 Q → Nat.card Q ≤ Nat.card S₁)
    (h₂K : S₂ ≤ K) (h₂ : IsPGroup 2 S₂)
    (h₂max : ∀ Q : Subgroup Γ, Q ≤ K → IsPGroup 2 Q → Nat.card Q ≤ Nat.card S₂) :
    ∃ c ∈ K, ∀ x : Γ, x ∈ S₂ ↔ c⁻¹ * x * c ∈ S₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ S : Subgroup Γ, S ≤ K → IsPGroup 2 S →
      (∀ Q : Subgroup Γ, Q ≤ K → IsPGroup 2 Q → Nat.card Q ≤ Nat.card S) →
      ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K) = S.subgroupOf K := by
    intro S hSK hS hmax
    have hS' : IsPGroup 2 (S.subgroupOf K) := hS.comap_subtype
    obtain ⟨P, hP⟩ := hS'.exists_le_sylow
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
    have h1 := hmax ((P : Subgroup ↥K).map K.subtype) (Subgroup.map_subtype_le _)
      (P.isPGroup'.map _)
    rw [Subgroup.card_map_of_injective K.subtype_injective] at h1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv]
    exact h1
  obtain ⟨P₁, hP₁⟩ := key S₁ h₁K h₁ h₁max
  obtain ⟨P₂, hP₂⟩ := key S₂ h₂K h₂ h₂max
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥K P₁ P₂
  refine ⟨c, c.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxK : x ∈ K := h₂K hx
    have hmem : (⟨x, hxK⟩ : ↥K) ∈ (P₂ : Subgroup ↥K) := by
      rw [hP₂]; exact Subgroup.mem_subgroupOf.2 hx
    rw [← hc, Sylow.coe_subgroup_smul] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    rw [hP₁] at hy
    have hy' := Subgroup.mem_subgroupOf.1 hy
    have hyx' : c * y * c⁻¹ = ⟨x, hxK⟩ := hyx
    have e : ((y : ↥K) : Γ) = (c : Γ)⁻¹ * x * (c : Γ) := by
      have := congrArg Subtype.val hyx'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [← this]
      group
    rwa [e] at hy'
  · intro hx
    have hxK : c⁻¹ * x * c ∈ K := h₁K hx
    have hmem : (⟨c⁻¹ * x * c, hxK⟩ : ↥K) ∈ (P₁ : Subgroup ↥K) := by
      rw [hP₁]; exact Subgroup.mem_subgroupOf.2 hx
    have h2 : MulAut.conj c • (⟨c⁻¹ * x * c, hxK⟩ : ↥K) ∈
        ((c • P₁ : Sylow 2 ↥K) : Subgroup ↥K) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hmem
    rw [hc, hP₂] at h2
    have h3 := Subgroup.mem_subgroupOf.1 h2
    have e : (((MulAut.conj c • (⟨c⁻¹ * x * c, hxK⟩ : ↥K)) : ↥K) : Γ) = x := by
      show ((c : Γ) * ((c : Γ)⁻¹ * x * c) * (c : Γ)⁻¹) = x
      group
    rwa [e] at h3

end Groups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

theorem iota2_swap (a b : Fin (m + 6)) :
    iota2 (m + 6) (swap a b) =
      swap (shift2 (m + 6) a : Fin (m + 6 + 2)) (shift2 (m + 6) b) := by
  refine Equiv.Perm.ext fun x => ?_
  by_cases hx : x ≠ 0 ∧ x ≠ 1
  · obtain ⟨j, rfl⟩ : ∃ j, (shift2 (m + 6) j : Fin (m + 6 + 2)) = x :=
      ⟨(shift2 (m + 6)).symm ⟨x, hx⟩, by simp⟩
    rw [iota2_apply_shift]
    have hinj : Function.Injective (fun j : Fin (m + 6) => (shift2 (m + 6) j : Fin (m + 6 + 2))) :=
      fun a b hab => (shift2 (m + 6)).injective (Subtype.ext hab)
    exact (hinj.swap_apply a b j).symm
  · simp only [not_and_or, not_not] at hx
    rcases hx with rfl | rfl
    · rw [iota2_apply_zero, swap_apply_of_ne_of_ne (shift2 (m + 6) a).2.1.symm
        (shift2 (m + 6) b).2.1.symm]
    · rw [iota2_apply_one, swap_apply_of_ne_of_ne (shift2 (m + 6) a).2.2.symm
        (shift2 (m + 6) b).2.2.symm]

theorem shift2_zero : (shift2 (m + 6) 0 : Fin (m + 6 + 2)) = 2 := Fin.ext (by
  rw [shift2_val]; rfl)

theorem shift2_one : (shift2 (m + 6) 1 : Fin (m + 6 + 2)) = 3 := Fin.ext (by
  rw [shift2_val]; rfl)

theorem shift2_two : (shift2 (m + 6) 2 : Fin (m + 6 + 2)) = 4 := Fin.ext (by
  rw [shift2_val]; rfl)

theorem shift2_three : (shift2 (m + 6) 3 : Fin (m + 6 + 2)) = 5 := Fin.ext (by
  rw [shift2_val]; rfl)

theorem yy_eq_pe_iota2 : yy ψ = pe ψ (iota2 (m + 6) (swap 0 1)) := by
  rw [iota2_swap, shift2_zero, shift2_one]; rfl

theorem Hyp.yy_mem_N (h : Hyp G L z v H₁ m ψ) : yy ψ ∈ NN G L := by
  rw [yy_eq_pe_iota2]; exact h.pe_iota2_mem_N _

theorem Hyp.N_le_normalizer_K (h : Hyp G L z v H₁ m ψ) :
    NN G L ≤ Subgroup.normalizer ((KK G L : Subgroup (GLV V)) : Set (GLV V)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ x ∈ NN G L, ∀ k ∈ KK G L, x * k * x⁻¹ ∈ KK G L := by
    intro x hx k hk
    refine ⟨G.mul_mem (G.mul_mem hx.1 hk.1) (G.inv_mem hx.1), Subgroup.mem_centralizer_iff.2
      fun l hl => ?_⟩
    have hl' : x⁻¹ * l * x ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hx.2) l).1 hl
      rwa [inv_inv] at this
    have hc := Subgroup.mem_centralizer_iff.1 hk.2 _ hl'
    calc l * (x * k * x⁻¹) = x * ((x⁻¹ * l * x) * k) * x⁻¹ := by group
      _ = x * (k * (x⁻¹ * l * x)) * x⁻¹ := by rw [hc]
      _ = x * k * x⁻¹ * l := by group
  intro k
  constructor
  · exact key x hx k
  · intro hk
    have := key x⁻¹ ((NN G L).inv_mem hx) _ hk
    simpa [mul_assoc] using this

@[expose] noncomputable def tt (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))) : GLV V :=
  pe ψ (iota2 (m + 6) (swap 0 1 * swap 2 3))

theorem tt_eq : tt ψ = pe ψ (swap 2 3 * swap 4 5) := by
  rw [tt, map_mul, iota2_swap, iota2_swap, shift2_zero, shift2_one, shift2_two, shift2_three]

theorem ne01' : (0 : Fin (m + 6)) ≠ 1 := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 1 by decide)
theorem ne02' : (0 : Fin (m + 6)) ≠ 2 := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 2 by decide)
theorem ne03' : (0 : Fin (m + 6)) ≠ 3 := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 3 by decide)
theorem ne23' : (2 : Fin (m + 6)) ≠ 3 := Fin.ne_of_val_ne (show (2 : ℕ) ≠ 3 by decide)

theorem dt_mem_alt : swap (0 : Fin (m + 6)) 1 * swap 2 3 ∈ alternatingGroup (Fin (m + 6)) := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, sign_swap ne01', sign_swap ne23']; rfl

theorem tt_eq_jL : tt ψ = jL ψ ⟨_, dt_mem_alt (m := m)⟩ := rfl

theorem Hyp.tt_mem_L (h : Hyp G L z v H₁ m ψ) : tt ψ ∈ L := by
  rw [tt_eq_jL]; exact h.jL_mem _

theorem Hyp.tt_not_mem_K (h : Hyp G L z v H₁ m ψ) : tt ψ ∉ KK G L := by
  intro ht
  have hc : ∀ a ∈ alternatingGroup (Fin (m + 6)),
      (swap 0 1 * swap 2 3 : Perm (Fin (m + 6))) * a = a * (swap 0 1 * swap 2 3) := by
    intro a ha
    have h1 := Subgroup.mem_centralizer_iff.1 ht.2 _ (h.jL_mem ⟨a, ha⟩)
    rw [tt_eq_jL, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (jL_injective h1).symm
  have h1 := CaseIAut.eq_one_of_commute_alternatingGroup (by omega) hc
  have h2 := congrArg (fun σ : Perm (Fin (m + 6)) => σ 0) h1
  simp only [Perm.mul_apply, Perm.one_apply] at h2
  rw [swap_apply_of_ne_of_ne ne02' ne03', swap_apply_left] at h2
  exact ne01' h2.symm

structure SBad (G L : Subgroup (GLV V)) (z : GLV V) (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2)))
    (S : Subgroup (GLV V)) : Prop where
  le : S ≤ KK G L
  isP : IsPGroup 2 S
  z_mem : z ∈ S
  y_norm : ∀ s ∈ S, yy ψ * s * (yy ψ)⁻¹ ∈ S
  max : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ Nat.card S
  four : 4 ≤ Nat.card S

theorem Hyp.z_comm_yy (h : Hyp G L z v H₁ m ψ) : z * yy ψ = yy ψ * z := by
  rw [h.z_eq, yy, ← map_mul, ← map_mul]
  congr 1
  refine (Equiv.Perm.Disjoint.commute ?_).eq
  intro x
  by_cases h0 : x = 0
  · right; rw [h0]; exact swap_apply_of_ne_of_ne ne02 ne03
  by_cases h1 : x = 1
  · right; rw [h1]; exact swap_apply_of_ne_of_ne ne12 ne13
  · left; exact swap_apply_of_ne_of_ne h0 h1

theorem Hyp.yy_orderOf (h : Hyp G L z v H₁ m ψ) : orderOf (yy ψ) = 2 := by
  rw [h.yy_eq, show gg ψ * z * (gg ψ)⁻¹ = (MulAut.conj (gg ψ)).toMonoidHom z from rfl,
    orderOf_injective _ (MulAut.conj (gg ψ)).injective]
  exact h.std.orderOf_s

theorem Hyp.exists_sBad (h : Hyp G L z v H₁ m ψ)
    (hbig : ∃ Q : Subgroup (GLV V), Q ≤ KK G L ∧ IsPGroup 2 Q ∧ 2 < Nat.card Q) :
    ∃ S, SBad G L z ψ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup (GLV V) := Subgroup.zpowers z ⊔ Subgroup.zpowers (yy ψ) with hR
  have hR2 : IsPGroup 2 R := by
    refine IsPGroup.to_sup_of_normal_right'
      (isPGroup_zpowers_of_mul_self (mul_self_of_orderOf_two h.std.orderOf_s))
      (isPGroup_zpowers_of_mul_self (mul_self_of_orderOf_two h.yy_orderOf)) ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact ((Commute.zpow_left (show Commute (yy ψ) z from h.z_comm_yy.symm) k)).eq
  have hRN : R ≤ Subgroup.normalizer ((KK G L : Subgroup (GLV V)) : Set (GLV V)) :=
    sup_le (Subgroup.zpowers_le.2 (h.N_le_normalizer_K h.z_mem_N))
      (Subgroup.zpowers_le.2 (h.N_le_normalizer_K h.yy_mem_N))
  obtain ⟨S, hSK, hS2, hRS, hnorm, hmax⟩ := exists_max_normalized (KK G L) R hR2 hRN
  obtain ⟨Q, hQK, hQ2, hQ⟩ := hbig
  refine ⟨S, ⟨hSK, hS2, hRS ⟨Subgroup.mem_sup_left (Subgroup.mem_zpowers z), h.z_mem_K⟩,
    fun s hs => hnorm _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) s hs, hmax, ?_⟩⟩
  have h1 := hmax Q hQK hQ2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS2
  have h4 : 2 < 2 ^ k := hk ▸ (lt_of_lt_of_le hQ h1)
  have hk2 : 2 ≤ k := by
    by_contra hc
    push Not at hc
    interval_cases k <;> simp at h4
  rw [hk]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2

variable {S : Subgroup (GLV V)}

theorem SBad.uniq (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) {a : GLV V} (ha : a ∈ S)
    (ha2 : orderOf a = 2) : a = z :=
  CFSG.GH74.Uniqueness.SU.SU10.eq_of_orderOf_two_of_pRank_le_one hS.isP
    ((CFSG.SectionRank.pRank_mono Nat.one_lt_two hS.le).trans h.rank.le) ha hS.z_mem ha2
    h.std.orderOf_s

theorem SBad.comm_z (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) {s : GLV V} (hs : s ∈ S) :
    s * z = z * s := by
  have hmem : s * z * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs hS.z_mem) (S.inv_mem hs)
  have hord : orderOf (s * z * s⁻¹) = 2 := by
    rw [show s * z * s⁻¹ = (MulAut.conj s).toMonoidHom z from rfl,
      orderOf_injective _ (MulAut.conj s).injective]
    exact h.std.orderOf_s
  have := hS.uniq h hmem hord
  calc s * z = s * z * s⁻¹ * s := by group
    _ = z * s := by rw [this]

theorem Hyp.card_le_two_of_comm (h : Hyp G L z v H₁ m ψ) {Q : Subgroup (GLV V)}
    (hQK : Q ≤ KK G L) (hQ : IsPGroup 2 Q) (hQz : ∀ q ∈ Q, q * z = z * q)
    (hQy : ∀ q ∈ Q, q * yy ψ = yy ψ * q) : Nat.card Q ≤ 2 := by
  refine h.card_le_two_of_centralizer (fun q hq => ⟨(hQK hq).1, ?_⟩) (fun q hq => (hQK hq).2) hQ
  refine h.normalizer_U_le (hQK hq).1 fun w hw => ⟨?_, ?_⟩
  · have := mem_commSpace_conj (g := q) hw.1
    rwa [show q * z * q⁻¹ = z by rw [hQz q hq, mul_inv_cancel_right]] at this
  · have := mem_commSpace_conj (g := q) hw.2
    rwa [show q * yy ψ * q⁻¹ = yy ψ by rw [hQy q hq, mul_inv_cancel_right]] at this

theorem SBad.exists_not_comm (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) :
    ∃ r ∈ S, r * yy ψ ≠ yy ψ * r := by
  by_contra hc
  push Not at hc
  have := h.card_le_two_of_comm hS.le hS.isP (fun q hq => hS.comm_z h hq) hc
  have := hS.four
  omega

theorem SBad.exists_conj_mul (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) :
    ∃ d ∈ S, d⁻¹ * yy ψ * d = yy ψ * z := by
  refine exists_conj_eq_mul_of_unique_involution hS.isP hS.z_mem h.std.orderOf_s
    (fun x hx hx2 => hS.uniq h hx hx2) h.yy_orderOf ?_ (hS.exists_not_comm h)
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact hS.y_norm s
  · intro hs
    have := hS.y_norm _ hs
    have hyy : yy ψ * yy ψ = 1 := mul_self_of_orderOf_two h.yy_orderOf
    have e : yy ψ * (yy ψ * s * (yy ψ)⁻¹) * (yy ψ)⁻¹ = s := by
      have hinv : (yy ψ)⁻¹ = yy ψ := inv_eq_of_mul_eq_one_right hyy
      rw [hinv]
      calc yy ψ * (yy ψ * s * yy ψ) * yy ψ = (yy ψ * yy ψ) * s * (yy ψ * yy ψ) := by group
        _ = s := by rw [hyy]; group
    rwa [e] at this

theorem conj_dt :
    (swap 0 4 * swap 1 5 : Perm (Fin (m + 6 + 2))) * (swap 2 3 * swap 0 1) *
        (swap 0 4 * swap 1 5)⁻¹ = swap 2 3 * swap 4 5 := by
  have h04 : (0 : Fin (m + 6 + 2)) ≠ 4 := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 4 by decide)
  have h05 : (0 : Fin (m + 6 + 2)) ≠ 5 := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 5 by decide)
  have h14 : (1 : Fin (m + 6 + 2)) ≠ 4 := Fin.ne_of_val_ne (show (1 : ℕ) ≠ 4 by decide)
  have h15 : (1 : Fin (m + 6 + 2)) ≠ 5 := Fin.ne_of_val_ne (show (1 : ℕ) ≠ 5 by decide)
  have h24 : (2 : Fin (m + 6 + 2)) ≠ 4 := Fin.ne_of_val_ne (show (2 : ℕ) ≠ 4 by decide)
  have h25 : (2 : Fin (m + 6 + 2)) ≠ 5 := Fin.ne_of_val_ne (show (2 : ℕ) ≠ 5 by decide)
  have h34 : (3 : Fin (m + 6 + 2)) ≠ 4 := Fin.ne_of_val_ne (show (3 : ℕ) ≠ 4 by decide)
  have h35 : (3 : Fin (m + 6 + 2)) ≠ 5 := Fin.ne_of_val_ne (show (3 : ℕ) ≠ 5 by decide)
  set π : Perm (Fin (m + 6 + 2)) := swap 0 4 * swap 1 5 with hπ
  have e : π * (swap 2 3 * swap 0 1) * π⁻¹ = (π * swap 2 3 * π⁻¹) * (π * swap 0 1 * π⁻¹) := by
    group
  rw [e, ← swap_apply_apply, ← swap_apply_apply]
  have p0 : π 0 = 4 := by
    rw [hπ, Perm.mul_apply, swap_apply_of_ne_of_ne ne01 h05, swap_apply_left]
  have p1 : π 1 = 5 := by
    have h54 : (5 : Fin (m + 6 + 2)) ≠ 4 := Fin.ne_of_val_ne (show (5 : ℕ) ≠ 4 by decide)
    rw [hπ, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne h05.symm h54]
  have p2 : π 2 = 2 := by
    rw [hπ, Perm.mul_apply, swap_apply_of_ne_of_ne ne12.symm h25,
      swap_apply_of_ne_of_ne ne02.symm h24]
  have p3 : π 3 = 3 := by
    rw [hπ, Perm.mul_apply, swap_apply_of_ne_of_ne ne13.symm h35,
      swap_apply_of_ne_of_ne ne03.symm h34]
  rw [p0, p1, p2, p3]

theorem SBad.exists_hh (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) :
    ∃ hh ∈ G, hh * z * hh⁻¹ = tt ψ := by
  obtain ⟨d, hdS, hd⟩ := hS.exists_conj_mul h
  have hdG : d ∈ G := (hS.le hdS).1
  set π : Perm (Fin (m + 6 + 2)) := swap 0 4 * swap 1 5 with hπ
  refine ⟨pe ψ π * d⁻¹ * gg ψ, G.mul_mem (G.mul_mem (h.H₁_le_G (pe_mem π)) (G.inv_mem hdG))
    h.gg_mem_G, ?_⟩
  have e1 : pe ψ π * d⁻¹ * gg ψ * z * (pe ψ π * d⁻¹ * gg ψ)⁻¹ =
      pe ψ π * (d⁻¹ * (gg ψ * z * (gg ψ)⁻¹) * d) * (pe ψ π)⁻¹ := by group
  rw [e1, ← h.yy_eq, hd, tt_eq, yy, h.z_eq, ← map_mul, ← map_inv, ← map_mul, ← map_mul, hπ,
    conj_dt]

theorem Hyp.hh_not_mem_N (h : Hyp G L z v H₁ m ψ) {hh : GLV V} (hhG : hh ∈ G)
    (hht : hh * z * hh⁻¹ = tt ψ) : hh ∉ Subgroup.normalizer (L : Set (GLV V)) := by
  intro hN
  apply h.tt_not_mem_K
  rw [← hht]
  have := (Subgroup.mem_normalizer_iff.1 (h.N_le_normalizer_K ⟨hhG, hN⟩) z).1 h.z_mem_K
  exact this

theorem SBad.conj_mem_N (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) {hh : GLV V}
    (hhG : hh ∈ G) (hht : hh * z * hh⁻¹ = tt ψ) {s : GLV V} (hs : s ∈ S) :
    hh⁻¹ * s * hh ∈ NN G L := by
  have hsG : s ∈ G := (hS.le hs).1
  refine h.centralizer_z_le (G.mul_mem (G.mul_mem (G.inv_mem hhG) hsG) hhG) ?_
  have hst : s * tt ψ = tt ψ * s :=
    (Subgroup.mem_centralizer_iff.1 (hS.le hs).2 _ h.tt_mem_L).symm
  have hz : z = hh⁻¹ * tt ψ * hh := by rw [← hht]; group
  rw [hz]
  calc hh⁻¹ * s * hh * (hh⁻¹ * tt ψ * hh) = hh⁻¹ * (s * tt ψ) * hh := by group
    _ = hh⁻¹ * (tt ψ * s) * hh := by rw [hst]
    _ = hh⁻¹ * tt ψ * hh * (hh⁻¹ * s * hh) := by group

theorem SBad.eq_one_of_conj_mem_K (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) {hh : GLV V}
    (hhG : hh ∈ G) (hht : hh * z * hh⁻¹ = tt ψ) {s : GLV V} (hs : s ∈ S)
    (hsK : hh⁻¹ * s * hh ∈ KK G L) : s = 1 := by
  have hodd := h.std.tight hh hhG (h.hh_not_mem_N hhG hht)
  have hmem : s ∈ KK G L ⊓ (KK G L).map (MulAut.conj hh).toMonoidHom :=
    ⟨hS.le hs, ⟨_, hsK, by simp [mul_assoc]⟩⟩
  exact eq_one_of_isPGroup_of_odd hS.isP hodd hs hmem

end CaseIAux

end CFSG.CGT.Foote82
