module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L511A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L16aStmt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem csl_comm (h52a : Asc82Lemma52a) {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
    (c : Sec5RCtx G t L S z r B A) :
    ∀ a ∈ S ⊓ centralizer (L : Set G), ∀ b ∈ S ⊓ centralizer (L : Set G), a * b = b * a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer (L : Set G) with hH
  have hP : IsPGroup 2 ↥((S ⊓ H).subgroupOf H) :=
    (c.sylow.2.1.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  haveI := h52a G t L c.toSec5Setting Q
  intro a ha b hb
  have ha' : (⟨a, ha.2⟩ : H) ∈ (Q : Subgroup H) := hPQ (Subgroup.mem_subgroupOf.mpr ha)
  have hb' : (⟨b, hb.2⟩ : H) ∈ (Q : Subgroup H) := hPQ (Subgroup.mem_subgroupOf.mpr hb)
  have := (IsCyclic.commGroup (α := ↥(Q : Subgroup H))).mul_comm ⟨⟨a, ha.2⟩, ha'⟩ ⟨⟨b, hb.2⟩, hb'⟩
  exact congrArg (fun q : ↥(Q : Subgroup H) => ((q : H) : G)) this

theorem csl_sq_eq_t (h52a : Asc82Lemma52a) {t : G} {L S : Subgroup G} {z r : G}
    {B A : Subgroup G} (c : Sec5RCtx G t L S z r B A) {x : G}
    (hx : x ∈ S ⊓ centralizer (L : Set G)) (hx4 : x ^ 4 = 1) (hxt : x ∉ zpowers t) :
    x * x = t := by
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer c.toSec3Setting
  have hcyc := h52a G t L c.toSec5Setting
  have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (c.sylow.1 hx.1)
  have hxx_t : x * x * t = t * (x * x) := by
    calc x * x * t = x * (x * t) := by group
      _ = x * (t * x) := by rw [hxt']
      _ = (x * t) * x := by group
      _ = (t * x) * x := by rw [hxt']
      _ = t * (x * x) := by group
  have hxxC : x * x ∈ centralizer (L : Set G) := Subgroup.mul_mem _ hx.2 hx.2
  have hxx2 : x * x * (x * x) = 1 := by
    rw [← hx4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rcases sec4_eq_of_commute hcyc hxxC htC hxx2 c.involution hxx_t with h1 | h1
  · exfalso
    rcases sec4_eq_of_commute hcyc hx.2 htC h1 c.involution hxt' with h2 | h2
    · exact hxt (by rw [h2]; exact one_mem _)
    · exact hxt (by rw [h2]; exact mem_zpowers t)
  · exact h1

theorem csl_A_cases {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
    (c : Sec5RCtx G t L S z r B A) : ∀ a ∈ A, ∃ b ∈ B, a = b ∨ a = r * b := by
  intro a ha
  have hrN : zpowers r ≤ normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer (B : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (c.B_le hb).2
  rw [c.A_eq] at ha
  have ha' : a ∈ ((zpowers r : Set G) * (B : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (zpowers r) B hrN]
    exact ha
  obtain ⟨u, hu, b, hb, hab⟩ := ha'
  beta_reduce at hab
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hr2 : orderOf r = 2 := sec5b_orderOf_r c
  refine ⟨b, hb, ?_⟩
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    have hr1 : r ^ n = 1 := by
      rw [← zpow_mod_orderOf, hr2]
      simp [h0]
    rw [← hab, hr1, one_mul]
  · right
    have hr1 : r ^ n = r := by
      rw [← zpow_mod_orderOf, hr2]
      simp [h1]
    rw [← hab, hr1]

theorem asc82Lemma511CSL_of (h34a : Asc82Lemma34a) (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53) (tab : Asc82Tab5)
    (h58d : Asc82Lemma58d) (h510 : Asc82Lemma510) (hF0 : Asc82FactPockets6)
    (hE : Asc82FactQCentExp6) (hB : Asc82FactQBCent6) : Asc82Lemma511CSL := by
  intro G _ _ t L S z r B A c x hx
  by_cases hxt : x ∈ zpowers t
  · exact Or.inl hxt
  right
  have hx4 := csl_pow_four h34a h36 h37 h52a h52b h53 tab h58d h510 hF0 hE c x hx
  have hx2t := csl_sq_eq_t h52a c hx hx4 hxt
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer c.toSec3Setting
  have hcyc := h52a G t L c.toSec5Setting
  have hBA : B ≤ A := c.A_eq ▸ le_sup_right
  have hrA : r ∈ A := c.A_eq ▸ Subgroup.mem_sup_left (mem_zpowers r)
  have htA : t ∈ A := hBA c.B_split.1
  have hrS : r ∈ S := c.A_le hrA
  have hrt : r ∈ centralizer ({t} : Set G) := c.sylow.1 hrS
  have hrt' : r * t = t * r := Subgroup.mem_centralizer_singleton_iff.mp hrt
  have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (c.sylow.1 hx.1)
  have hrN : r ∈ normalizer (L : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 c.toSec3SettingLB r hrt)
  have hxB : ∀ b ∈ B, x * b = b * x := fun b hb =>
    (Subgroup.mem_centralizer_iff.mp hx.2 b (c.B_le hb).1).symm
  have hx' : r * x * r⁻¹ ∈ S ⊓ centralizer (L : Set G) := by
    refine ⟨S.mul_mem (S.mul_mem hrS hx.1) (S.inv_mem hrS), ?_⟩
    show r * x * r⁻¹ ∈ centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : r⁻¹ * l * r ∈ L := by
      refine (Subgroup.mem_normalizer_iff.mp hrN (r⁻¹ * l * r)).mpr ?_
      have : r * (r⁻¹ * l * r) * r⁻¹ = l := by group
      rw [this]
      exact hl
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hl'
    calc l * (r * x * r⁻¹) = r * ((r⁻¹ * l * r) * x) * r⁻¹ := by group
      _ = r * (x * (r⁻¹ * l * r)) * r⁻¹ := by rw [hc]
      _ = r * x * r⁻¹ * l := by group
  have hcomm : Commute (r * x * r⁻¹) x := csl_comm h52a c _ hx' _ hx
  have hdX : r * x * r⁻¹ * x⁻¹ ∈ S ⊓ centralizer (L : Set G) :=
    Subgroup.mul_mem _ hx' (Subgroup.inv_mem _ hx)
  have hdd : r * x * r⁻¹ * x⁻¹ * (r * x * r⁻¹ * x⁻¹) = 1 := by
    have hci : x⁻¹ * (r * x * r⁻¹) = (r * x * r⁻¹) * x⁻¹ := hcomm.inv_right.eq.symm
    calc r * x * r⁻¹ * x⁻¹ * (r * x * r⁻¹ * x⁻¹)
        = (r * x * r⁻¹) * (x⁻¹ * (r * x * r⁻¹)) * x⁻¹ := by group
      _ = (r * x * r⁻¹) * ((r * x * r⁻¹) * x⁻¹) * x⁻¹ := by rw [hci]
      _ = r * (x * x) * r⁻¹ * (x * x)⁻¹ := by group
      _ = 1 := by rw [hx2t, hrt', mul_inv_cancel_right, mul_inv_cancel]
  have hdt : r * x * r⁻¹ * x⁻¹ * t = t * (r * x * r⁻¹ * x⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (c.sylow.1 hdX.1)
  rcases sec4_eq_of_commute hcyc hdX.2 htC hdd c.involution hdt with h1 | h1
  · exfalso
    have hrx : r * x = x * r := by
      calc r * x = (r * x * r⁻¹ * x⁻¹) * (x * r) := by group
        _ = x * r := by rw [h1, one_mul]
    have hxA : x ∈ centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨b, hb, rfl | rfl⟩ := csl_A_cases c a ha
      · exact (hxB a hb).symm
      · calc r * b * x = r * (x * b) := by rw [mul_assoc, hxB b hb]
          _ = x * (r * b) := by rw [← mul_assoc, hrx, mul_assoc]
    exact hxt (csl_centralizer_A h34a h36 h37 h52a h52b h53 tab h58d h510 hF0 hE hB c x hx hxA)
  · have hrx : r * x * r⁻¹ = t * x := by
      calc r * x * r⁻¹ = (r * x * r⁻¹ * x⁻¹) * x := by group
        _ = t * x := by rw [h1]
    have hxr : x * r * x⁻¹ ∈ A := by
      have : x * r * x⁻¹ = t⁻¹ * r := by
        calc x * r * x⁻¹ = x * (r * x * r⁻¹)⁻¹ * r := by group
          _ = x * (t * x)⁻¹ * r := by rw [hrx]
          _ = t⁻¹ * r := by group
      rw [this]
      exact A.mul_mem (A.inv_mem htA) hrA
    have hxir : x⁻¹ * r * x⁻¹⁻¹ ∈ A := by
      have : x⁻¹ * r * x⁻¹⁻¹ = t * r := by
        calc x⁻¹ * r * x⁻¹⁻¹ = x⁻¹ * (r * x * r⁻¹) * r := by group
          _ = x⁻¹ * (t * x) * r := by rw [hrx]
          _ = x⁻¹ * (x * t) * r := by rw [hxt']
          _ = t * r := by group
      rw [this]
      exact A.mul_mem htA hrA
    have hconj : ∀ g : G, (∀ b ∈ B, g * b = b * g) → g * r * g⁻¹ ∈ A →
        ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
      intro g hgB hgr a ha
      have hle : zpowers r ⊔ B ≤ A.comap (MulAut.conj g).toMonoidHom := by
        refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_comap.mpr ?_)) fun b hb =>
          Subgroup.mem_comap.mpr ?_
        · simpa [MulAut.conj_apply] using hgr
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [hgB b hb, mul_inv_cancel_right]
          exact hBA hb
      rw [c.A_eq] at ha
      simpa [MulAut.conj_apply] using Subgroup.mem_comap.mp (hle ha)
    have hxiB : ∀ b ∈ B, x⁻¹ * b = b * x⁻¹ := fun b hb =>
      (Commute.inv_left (show Commute x b from hxB b hb)).eq
    have hcA : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ zpowers t := by
      intro a ha
      obtain ⟨b, hb, rfl | rfl⟩ := csl_A_cases c a ha
      · rw [← hxB a hb, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _
      · have : r * b * x * (r * b)⁻¹ * x⁻¹ = t := by
          calc r * b * x * (r * b)⁻¹ * x⁻¹ = r * (b * x * b⁻¹) * r⁻¹ * x⁻¹ := by group
            _ = r * x * r⁻¹ * x⁻¹ := by rw [← hxB b hb, mul_inv_cancel_right]
            _ = t := h1
        rw [this]
        exact mem_zpowers t
    refine ⟨?_, le_antisymm ?_ ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · exact hconj x hxB hxr a
      · intro ha
        have := hconj x⁻¹ hxiB hxir _ ha
        rwa [show x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a by group] at this
    · rw [Subgroup.commutator_le]
      intro a ha k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hcA a ha)
      have hax : a * x * a⁻¹ = t ^ j * x := by rw [hj]; group
      have hjx : Commute (t ^ j) x := Commute.zpow_left hxt'.symm j
      rw [commutatorElement_def, ← conj_zpow, hax, hjx.mul_zpow, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.zpow_mem _ (mem_zpowers t) j) n
    · rw [Subgroup.zpowers_le]
      have : ⁅r, x⁆ = t := by rw [commutatorElement_def]; exact h1
      rw [← this]
      exact Subgroup.commutator_mem_commutator hrA (mem_zpowers x)

end CFSG.OddStandard.SmallF3.Omega
