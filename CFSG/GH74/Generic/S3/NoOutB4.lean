module

public import CFSG.GH74.KGroups.LinEvenAut
public import CFSG.GH74.KGroups.BalanceLift

public section

namespace CFSG.GH74.Generic.S3

open CFSG Subgroup
open CFSG.GH74.KGroups.L3Eps (InvDataB4)
open CFSG.GH74.KGroups.Bal (commutator_induction commutator_self_of_quasisimple lift_fixed)
open CFSG.QuasithinUnique.Setup.X5 (normalizerAct normalizerAct_of_mem normalizerAct_apply_mk coe_conjOn
  mem_centralizer_of_normalizerAct_eq_one eq_one_of_involution_mem_odd)
open scoped commutatorElement

theorem normal_le_center_or_eq_top' {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) (N : Subgroup Q)
    [N.Normal] : N ≤ center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  set π := QuotientGroup.mk' (center Q) with hπ
  have hNn : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hNZ : ∀ q : Q, ∃ n ∈ N, n⁻¹ * q ∈ center Q := by
      intro q
      have : π q ∈ N.map π := h ▸ mem_top _
      obtain ⟨n, hn, hnq⟩ := this
      refine ⟨n, hn, ?_⟩
      rw [← QuotientGroup.ker_mk' (center Q), MonoidHom.mem_ker, map_mul, map_inv, ← hπ, hnq,
        inv_mul_cancel]
    have htop : (⊤ : Subgroup Q) = ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ := by
      rw [← _root_.commutator_def]
      exact (@Group.IsPerfect.commutator_eq_top Q _ hperf).symm
    rw [eq_top_iff, htop, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨n₁, hn₁, hz₁⟩ := hNZ x
    obtain ⟨n₂, hn₂, hz₂⟩ := hNZ y
    have hx : x = n₁ * (n₁⁻¹ * x) := by group
    have hy : y = n₂ * (n₂⁻¹ * y) := by group
    set z₁ := n₁⁻¹ * x
    set z₂ := n₂⁻¹ * y
    have c₁ := Subgroup.mem_center_iff.mp hz₁
    have c₂ := Subgroup.mem_center_iff.mp hz₂
    rw [hx, hy, commutatorElement_def]
    have e : n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by
      calc n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹
          = n₁ * (z₁ * (n₂ * z₂) * z₁⁻¹) * n₁⁻¹ * (n₂ * z₂)⁻¹ := by group
        _ = n₁ * (n₂ * z₂) * n₁⁻¹ * (n₂ * z₂)⁻¹ := by
            rw [← c₁ (n₂ * z₂), mul_assoc _ z₁, mul_inv_cancel, mul_one]
        _ = n₁ * n₂ * (z₂ * n₁⁻¹) * z₂⁻¹ * n₂⁻¹ := by group
        _ = n₁ * n₂ * (n₁⁻¹ * z₂) * z₂⁻¹ * n₂⁻¹ := by rw [← c₂ n₁⁻¹]
        _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)

section Main

variable {G : Type} [Group G]

theorem b4_inner {M : Subgroup G} [Group.IsPerfect M] {a : G} (haM : a ∈ M)
    (ha1 : (QuotientGroup.mk ⟨a, haM⟩ : ↥M ⧸ center ↥M) ≠ 1) (ha2 : a * a = 1)
    {q : ℕ} {S : Subgroup (↥M ⧸ center ↥M)} (hS : InvDataB4 q (↥M ⧸ center ↥M) (QuotientGroup.mk ⟨a, haM⟩) S)
    {z : G} (hzN : z ∈ normalizer (M : Set G)) (hz2 : z * z = 1) (hza : z * a = a * z)
    (R : Subgroup (↥M ⧸ center ↥M)) (hRodd : Odd (Nat.card R))
    (hRS : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R)
    (hfix : ∀ s ∈ S, normalizerAct M ⟨z, hzN⟩ s * s⁻¹ ∈ R) :
    ∃ m ∈ M, ∀ n ∈ M, z * n * z⁻¹ = m * n * m⁻¹ := by
  classical
  set t : ↥M ⧸ center ↥M := QuotientGroup.mk ⟨a, haM⟩ with ht
  set σ := normalizerAct M ⟨z, hzN⟩ with hσ
  have htt : t * t = 1 := by
    rw [ht, ← QuotientGroup.mk_mul, show (⟨a, haM⟩ * ⟨a, haM⟩ : ↥M) = 1 from Subtype.ext ha2]
    rfl
  have hσ2 : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have : (⟨z, hzN⟩ : normalizer (M : Set G)) * ⟨z, hzN⟩ = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hσt : σ t = t := by
    rw [hσ, ht, normalizerAct_apply_mk]
    congr 1
    apply Subtype.ext
    rw [coe_conjOn]
    show z * a * z⁻¹ = a
    calc z * a * z⁻¹ = (a * z) * z⁻¹ := by rw [hza]
      _ = a := by group
  have hσC : ∀ c ∈ Subgroup.centralizer ({t} : Set (↥M ⧸ center ↥M)),
      σ c ∈ Subgroup.centralizer ({t} : Set (↥M ⧸ center ↥M)) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    calc σ c * t = σ c * σ t := by rw [hσt]
      _ = σ (c * t) := (map_mul σ c t).symm
      _ = σ (t * c) := by rw [hc]
      _ = σ t * σ c := map_mul σ t c
      _ = t * σ c := by rw [hσt]
  have hσS : ∀ s ∈ S, σ s ∈ S := by
    intro s hs
    have hperf : ⁅S, S⁆ = S := commutator_self_of_quasisimple hS.quasisimple
    rw [← hperf] at hs
    refine commutator_induction (C := fun y => σ y ∈ S) hs ?_ ?_ ?_ ?_
    · intro a₁ ha₁ b₁ hb₁
      have : σ ⁅a₁, b₁⁆ = ⁅σ a₁, σ b₁⁆ := by
        simp only [commutatorElement_def, map_mul, map_inv]
      rw [this]
      exact hS.commutator_mem _ (hσC _ (hS.le_centralizer ha₁)) _ (hσC _ (hS.le_centralizer hb₁))
    · rw [map_one]
      exact one_mem S
    · intro y₁ y₂ h₁ h₂
      rw [map_mul]
      exact S.mul_mem h₁ h₂
    · intro y₁ h₁
      rw [map_inv]
      exact S.inv_mem h₁
  have hTbot : ∀ w ∈ S ⊓ R, w = 1 := by
    set T : Subgroup ↥S := (S ⊓ R).subgroupOf S with hT
    have hTn : T.Normal := ⟨fun n hn g => by
      rw [hT, Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨S.mul_mem (S.mul_mem g.2 hn.1) (S.inv_mem g.2), hRS g g.2 n hn.2⟩⟩
    rcases normal_le_center_or_eq_top' hS.quasisimple T with hle | htop
    · intro w hw
      have hwT : (⟨w, hw.1⟩ : ↥S) ∈ T := hw
      rcases hS.center ⟨w, hw.1⟩ (hle hwT) with h1 | h1
      · exact h1
      · have hwR : w ∈ R := hw.2
        have h1' : w = t := h1
        have : w * w = 1 := by rw [h1']; exact htt
        exact eq_one_of_involution_mem_odd (C := R) hRodd hwR this
    · exfalso
      have htR : t ∈ R := by
        have : (⟨t, hS.mem⟩ : ↥S) ∈ T := htop ▸ Subgroup.mem_top _
        exact this.2
      exact ha1 (eq_one_of_involution_mem_odd (C := R) hRodd htR htt)
  have hfixS : ∀ s ∈ S, σ s = s := by
    intro s hs
    have h1 : σ s * s⁻¹ ∈ S ⊓ R := ⟨S.mul_mem (hσS s hs) (S.inv_mem hs), hfix s hs⟩
    exact mul_inv_eq_one.1 (hTbot _ h1)
  rcases hS.aut_fixing σ hσ2 hfixS with h | h
  · have hc := mem_centralizer_of_normalizerAct_eq_one M (a := ⟨z, hzN⟩) h
    refine ⟨1, one_mem _, fun n hn => ?_⟩
    have := Subgroup.mem_centralizer_iff.1 hc n hn
    calc z * n * z⁻¹ = (n * z) * z⁻¹ := by rw [← this]
      _ = 1 * n * 1⁻¹ := by group
  · have h1 : normalizerAct M (⟨z, hzN⟩ * ⟨a, Subgroup.le_normalizer haM⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hσ, h, normalizerAct_of_mem M haM, mul_inv_cancel]
    have hc := mem_centralizer_of_normalizerAct_eq_one M h1
    refine ⟨a, haM, fun n hn => ?_⟩
    have hn' : a * n * a⁻¹ ∈ M := mul_mem (mul_mem haM hn) (inv_mem haM)
    have h2 := Subgroup.mem_centralizer_iff.1 hc _ hn'
    have h3 : (a * n * a⁻¹) * (z * a⁻¹) = (z * a⁻¹) * (a * n * a⁻¹) := by
      simpa using h2
    calc z * n * z⁻¹ = (z * a⁻¹) * (a * n * a⁻¹) * (z * a⁻¹)⁻¹ := by group
      _ = ((z * a⁻¹) * (a * n * a⁻¹)) * (z * a⁻¹)⁻¹ := rfl
      _ = ((a * n * a⁻¹) * (z * a⁻¹)) * (z * a⁻¹)⁻¹ := by rw [h3]
      _ = a * n * a⁻¹ := by group

end Main

end CFSG.GH74.Generic.S3
