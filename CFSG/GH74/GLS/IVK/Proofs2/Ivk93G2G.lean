module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cls
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93G2Lift
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93G2Swap
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93G2Sylow
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ModelLU
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ExcShape
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93OrdG2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint

@[expose] def Ivk93G2Res3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z Kind.g2 S →
    (∃ (r₁ : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), G2Shape z S r₁ 3 L₁ L₂) →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) = ⊥ →
      IsSimpleGroup ↥(generalizedFitting (HBar H)) →
      (∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) → PerfInJ H →
      HasTwoInvolutionClasses (HBar H) → FUS H

@[expose] def Psp4Swap : Prop :=
  ∀ {J : Type} [Group J] [Finite J] {q q₁ q₂ : ℕ}, Odd q → 5 ≤ q → IVK.IsPSp4 J q →
    ∀ {x : J} {L₁ L₂ : Subgroup J}, Ivk93Cfg2 x q₁ q₂ L₁ L₂ → ∀ (P : Sylow 2 J),
      x ∈ (P : Subgroup J) → (∀ s ∈ (P : Subgroup J), s * x = x * s) →
      ∃ s ∈ (P : Subgroup J), L₁.map (MulAut.conj s).toMonoidHom = L₂ ∧
        L₂.map (MulAut.conj s).toMonoidHom = L₁

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem sylow_le_of_card_le {X : Type} [Group X] [Finite X] (J : Subgroup X) (T : Sylow 2 X)
    (P : Sylow 2 ↥J) (hP : (P : Subgroup ↥J) = ((T : Subgroup X) ⊓ J).subgroupOf J)
    (hcard : Nat.card ↥(T : Subgroup X) ≤ Nat.card ↥(P : Subgroup ↥J)) : (T : Subgroup X) ≤ J := by
  have hPc : Nat.card ↥(P : Subgroup ↥J) = Nat.card ↥((T : Subgroup X) ⊓ J) := by
    rw [hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : (T : Subgroup X) ⊓ J ≤ J)).toEquiv
  have heq : (T : Subgroup X) ⊓ J = (T : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [← hPc]; exact hcard)
  rw [← heq]
  exact inf_le_right

theorem fus_of_J_one_class {H : Subgroup G} (T : Sylow 2 (HBar H))
    (hTJ : (T : Subgroup (HBar H)) ≤ generalizedFitting (HBar H))
    (hJone : ∀ a b : ↥(generalizedFitting (HBar H)), orderOf a = 2 → orderOf b = 2 → IsConj a b) :
    FUS H := by
  have : (generalizedFitting (HBar H)).Normal := LocalCores.generalized_fitting_characteristic.2
  have hodd := index_odd_of_sylow_le T hTJ
  intro u v hu hv _
  have hub : orderOf (QuotientGroup.mk u : HBar H) = 2 := orderOf_mk_eq_two H hu
  have hvb : orderOf (QuotientGroup.mk v : HBar H) = 2 := orderOf_mk_eq_two H hv
  have huJ := involution_mem_of_odd_index hodd hub
  have hvJ := involution_mem_of_odd_index hodd hvb
  exact MonoidHom.map_isConj (generalizedFitting (HBar H)).subtype
    (hJone ⟨_, huJ⟩ ⟨_, hvJ⟩ (by rw [← Subgroup.orderOf_coe]; exact hub)
      (by rw [← Subgroup.orderOf_coe]; exact hvb))

theorem ivk93_g2_of_swap (h93 : Ivk93Pair2)
    (hres : Ivk93G2Res3) (hswap : Psp4Swap) (hctx : Stage2Ctx G z Kind.g2 S) {H : Subgroup G}
    (hne : H ≠ ⊤) (hCH : Cen z ≤ H) (hV : pCore 2 (HBar H) = ⊥)
    (hs : IsSimpleGroup ↥(generalizedFitting (HBar H)))
    (hn : ∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) (hPerf : PerfInJ H)
    (h2 : HasTwoInvolutionClasses (HBar H)) : FUS H := by
  have hz2 := hctx.orderOf_z
  have hzmem : z ∈ H := hCH (mem_Cen_self z)
  obtain ⟨r₁, r₂, L₁, L₂, hshape⟩ : ∃ (r₁ r₂ : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
      G2Shape z S r₁ r₂ L₁ L₂ := by
    cases hctx.data with
    | g2 h => exact h.shape
  by_cases h3 : r₂ = 3
  · subst h3
    exact hres G z S hctx ⟨r₁, L₁, L₂, hshape⟩ H hne hCH hV hs hn hPerf h2
  have hodd₂ : Odd r₂ := hshape.2.1
  have hodd₁ : Odd r₁ := hshape.1
  have hr₂ : 3 < r₂ := by
    obtain ⟨F, _, _, hFq, -⟩ := exists_sl2_equiv_of_hasSL2Model hshape.2.2.2.2.2.1
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨m, hm⟩ := hodd₂
    omega
  have hr₁ : 3 < r₁ := hshape.2.2.1
  have hr₁5 : 5 ≤ r₁ := by
    obtain ⟨m, hm⟩ := hodd₁
    omega
  have hp2 := pair2_of_g2Shape hshape hr₂
  obtain ⟨hzJ, B₁, B₂, hB₁J, hB₂J, hB₁C, hB₂C, hm₁, hm₂, hcfg⟩ := exists_cfg2 hz2 hCH hPerf hp2
  have hcen := isCentralInvolution_zbar hctx hCH hzJ
  have hGH := ghList_J hctx hne hs hn
  have hconcl := h93 ↥(generalizedFitting (HBar H)) hs hGH _ hcen r₁ r₂ _ _ hcfg
  obtain ⟨T, hT⟩ := exists_sylow_barIn hctx hCH
  have hTcard : Nat.card ↥(T : Subgroup (HBar H)) =
      2 ^ ((r₁ * (r₁ ^ 2 - 1) * (r₂ * (r₂ ^ 2 - 1))).factorization 2) := by
    rw [hT, card_barIn_S hctx hCH]
    exact card_S_g2 hctx hshape
  have : (generalizedFitting (HBar H)).Normal := LocalCores.generalized_fitting_characteristic.2
  obtain ⟨P, hP⟩ := Glauberman.sylow_inf_normal T (N := generalizedFitting (HBar H))
  have hxP : (⟨mkH H ⟨z, hzmem⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) ∈
      (P : Subgroup ↥(generalizedFitting (HBar H))) := by
    rw [hP, Subgroup.mem_subgroupOf]
    exact ⟨by rw [hT]; exact zbar_mem_barIn hctx hCH, hzJ⟩
  have hxc : ∀ s ∈ (P : Subgroup ↥(generalizedFitting (HBar H))),
      s * (⟨mkH H ⟨z, hzmem⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) =
        ⟨mkH H ⟨z, hzmem⟩, hzJ⟩ * s := by
    intro s hs
    rw [hP, Subgroup.mem_subgroupOf] at hs
    exact Subtype.ext (zbar_comm_barIn hctx hCH (hT ▸ hs.1))
  have hx2 := hcen.1
  have hPcard : Nat.card ↥(P : Subgroup ↥(generalizedFitting (HBar H))) =
      Nat.card ↥((T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H)) := by
    rw [hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : (T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H) ≤
        generalizedFitting (HBar H))).toEquiv
  have hone : (∀ a b : ↥(generalizedFitting (HBar H)), orderOf a = 2 → orderOf b = 2 → IsConj a b) →
      Nat.card ↥(T : Subgroup (HBar H)) ≤ Nat.card ↥(P : Subgroup ↥(generalizedFitting (HBar H))) →
      FUS H := fun hJone hle =>
    fus_of_J_one_class T (sylow_le_of_card_le _ T P hP hle) hJone
  have hLU : ∀ {p f : ℕ}, p.Prime → p ≠ 2 → p ^ f = r₁ → r₂ = r₁ →
      ((p ^ f % 8 ≠ 1 ∧ LieModel ↥(generalizedFitting (HBar H)) .PSL 4 p f) ∨
        (p ^ f % 8 ≠ 7 ∧ LieModel ↥(generalizedFitting (HBar H)) .PSU 4 p f)) → False := by
    intro p f hp' hpp2 hpf heq hK
    have hshape' : G2Shape z S r₁ r₁ L₁ L₂ := heq ▸ hshape
    have hcardP := jm_card_lu hp' hpp2 (hpf ▸ hr₁5) hK P hxP hx2 hxc
    rw [hpf] at hcardP
    have hle : Nat.card ↥((T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H)) ≤
        Nat.card ↥(T : Subgroup (HBar H)) := Subgroup.card_le_of_le inf_le_left
    rw [← hPcard, hcardP, hT, card_barIn_S hctx hCH, card_S_g2_diag hctx hshape'] at hle
    have hpos : 0 < 2 ^ nuQ r₁ := pow_pos (by norm_num) _
    have := Nat.le_of_mul_le_mul_left hle hpos
    omega
  rcases hconcl with ⟨heq, hPsp | ⟨p, f, hp', hpp2, hf, hpf, h8, hm⟩ | ⟨p, f, hp', hpp2, hf, hpf, h8, hm⟩ |
      ⟨p, f, hp', hpp2, hf, hpf, hm⟩⟩ | ⟨p, f, hp', hpp2, hf, hm, hq⟩
  ·
    exfalso
    obtain ⟨s, hsP, hs12, hs21⟩ := hswap hodd₁ hr₁5 hPsp hcfg P hxP hxc
    have hsT : (s : HBar H) ∈ barIn H S := by
      have := hsP
      rw [hP, Subgroup.mem_subgroupOf] at this
      rw [← hT]
      exact this.1
    have h12 : B₁.map (MulAut.conj (s : HBar H)).toMonoidHom = B₂ :=
      map_conj_of_subgroupOf s.2 hB₁J hB₂J hs12
    have h21 : B₂.map (MulAut.conj (s : HBar H)).toMonoidHom = B₁ :=
      map_conj_of_subgroupOf s.2 hB₂J hB₁J hs21
    obtain ⟨t, htS, ht12, ht21⟩ := swap_to_bar hctx hCH hm₁ hm₂ hsT h12 h21
    obtain ⟨-, -, -, hprod, hsl₁, -, -, -, -, -, hPGL₁, -⟩ := hshape
    have hq := hp2.comp₁.1
    have hnt : Nontrivial ↥L₁ := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have hperf : Group.IsPerfect ↥L₁ := hq.1
    have hnab : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact Ivk93Exc.not_comm_of_perfect (A := L₁) (fun b hb b' hb' => hcon b hb b' hb')
    exact false_of_swap hprod.2.1 hnab hPGL₁ htS ht12 ht21
  ·
    exfalso
    exact hLU hp' hpp2 hpf heq.symm (Or.inl ⟨by rw [hpf]; exact h8, hm⟩)
  ·
    exfalso
    exact hLU hp' hpp2 hpf heq.symm (Or.inr ⟨by rw [hpf]; exact h8, hm⟩)
  ·
    refine hone (g2_one_class hp' hpp2 hm) (le_of_eq ?_)
    rw [hTcard, g2_sylow_card hp' hpp2 hm P hx2 hxc, hpf, ← heq]
  ·
    refine hone (d4_one_class hp' hpp2 hm) (le_of_eq ?_)
    rw [hTcard, d4_sylow_card hp' hpp2 hm P hx2 hxc]
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Nat.mul_comm (p ^ f * ((p ^ f) ^ 2 - 1))]

end Main

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
