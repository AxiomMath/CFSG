module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29B7Abs
public import CFSG.GH74.GLS.TwoThin.KGroupCore

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Sec29B7AbsD

open CFSG Subgroup CFSG.LocalCores CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS
  CFSG.GH74.GLS.TwoThin CFSG.GH74.Generic.BProg.B3.S3Sec29B7Aut
  CFSG.GH74.Generic.BProg.B3.S3Sec29B7Abs
open scoped commutatorElement

variable {H : Type} [Group H] {Iabs : Type} [Group Iabs]

theorem conjSub_conjSub (a b : H) (K : Subgroup H) :
    conjSub a (conjSub b K) = conjSub (a * b) K := by
  ext z
  rw [mem_conjSub', mem_conjSub', mem_conjSub']
  have : (a * b)⁻¹ * z * (a * b) = b⁻¹ * (a⁻¹ * z * a) * b := by group
  rw [this]

theorem comm_of_comm_swapDiag {x : H} {L : Subgroup H} (hAB : ⁅L, conjSub x⁻¹ L⁆ = ⊥) (a b : ↥L)
    (h : (a : H) * swapDiag hAB b = swapDiag hAB b * a) : (a : H) * b = b * a := by
  rw [swapDiag_apply] at h
  have hc : (a : H) * (x⁻¹ * b * x) = (x⁻¹ * b * x) * a :=
    commute_of_commutator_conj_eq_bot hAB a.2 (conj_mem_conjSub (t := x) b.2)
  have : ((a : H) * b) * (x⁻¹ * b * x) = (b * a) * (x⁻¹ * b * x) := by
    calc (a : H) * b * (x⁻¹ * b * x) = a * (b * (x⁻¹ * b * x)) := by group
      _ = (b * (x⁻¹ * b * x)) * a := h
      _ = b * ((x⁻¹ * b * x) * a) := by group
      _ = b * (a * (x⁻¹ * b * x)) := by rw [hc]
      _ = (b * a) * (x⁻¹ * b * x) := by group
  exact mul_right_cancel this

theorem conjSub_one (K : Subgroup H) : conjSub 1 K = K := by
  ext z
  rw [mem_conjSub']
  simp

theorem conj_conj_comm {d x : H} (h : d * x = x * d) (m : H) :
    d * (x * m * x⁻¹) * d⁻¹ = x * (d * m * d⁻¹) * x⁻¹ := by
  have e4 : x⁻¹ * d⁻¹ = d⁻¹ * x⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, h]
  calc d * (x * m * x⁻¹) * d⁻¹ = (d * x) * m * (x⁻¹ * d⁻¹) := by group
    _ = (x * d) * m * (d⁻¹ * x⁻¹) := by rw [h, e4]
    _ = x * (d * m * d⁻¹) * x⁻¹ := by group

theorem contra_diagonal [Finite H] {x : H} (hx2 : orderOf x = 2) {L M : Subgroup H}
    (hL : IsComponent L) (hMLL : M = L ∨ M = conjSub x⁻¹ L)
    (hAB : ⁅L, conjSub x⁻¹ L⁆ = ⊥)
    (ρ : Iabs →* H) (O : Subgroup Iabs) [O.Normal] (hker : ρ.ker ≤ O)
    (hQ : ¬ Group.IsSolvable (Iabs ⧸ O))
    (Ib : Subgroup H) (hρIb : ∀ i, ρ i ∈ Ib) (hIbρ : ∀ b ∈ Ib, ∃ i, ρ i = b)
    (hIs : Ib ≤ (swapDiag hAB).range)
    (hIsub : (Ib.subgroupOf (centralizer ({x} : Set H))).IsSubnormal)
    (D : Subgroup H) (hD4 : Nat.card D = 4) (hD2 : ∀ d ∈ D, d * d = 1) (hxD : x ∈ D)
    (hDI : ∀ d ∈ D, ∀ i, ∃ j, d * ρ i * d⁻¹ = ρ j)
    (hDO : ∀ d ∈ D, ∀ n ∈ O, ∃ n' ∈ O, d * ρ n * d⁻¹ = ρ n')
    (hcov : ∀ d ∈ D, ∀ i, ∃ i', d * ρ i' = ρ i' * d ∧ i⁻¹ * i' ∈ O)
    (hfaith : ∀ d ∈ D, (∀ m ∈ M, d * m = m * d) → d = 1) : False := by
  classical
  have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hx2
  have hDcomm : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d := by
    intro d hd e he
    have h1 : (d * e) * (d * e) = 1 := hD2 _ (mul_mem hd he)
    have hdi := inv_eq_of_mul_self (hD2 d hd)
    have hei := inv_eq_of_mul_self (hD2 e he)
    have h2 : d * e = (d * e)⁻¹ := (inv_eq_of_mul_self h1).symm
    rwa [mul_inv_rev, hdi, hei] at h2
  set Δ := (swapDiag hAB).range with hΔdef
  have hΔC : Δ ≤ centralizer ({x} : Set H) := by
    rintro _ ⟨l, rfl⟩
    exact swapDiag_mem_centralizer hAB hxinv l
  have hΔq : IsQuasisimple ↥Δ := by
    have hDa := isQuasisimple_range_swapDiag hAB (assembly_isQuasisimple_of_isComponent hL)
    exact CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mpr
      ⟨hDa.1, hDa.2⟩
  have hρΔ : ∀ i, ρ i ∈ Δ := fun i => hIs (hρIb i)
  obtain ⟨i₁, i₂, hne⟩ := exists_noncomm ρ O hker hQ
  have hIbΔ : Δ ≤ Ib := by
    have hsub : (Ib.subgroupOf Δ).IsSubnormal := isSubnormal_inf_subgroupOf hIsub hΔC
    rcases eq_top_or_le_center_of_subnormal hΔq hsub with htop | hcen
    · intro d hd
      have : (⟨d, hd⟩ : ↥Δ) ∈ Ib.subgroupOf Δ := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    · exfalso
      apply hne
      have h1 : (⟨ρ i₁, hρΔ i₁⟩ : ↥Δ) ∈ center ↥Δ := hcen (Subgroup.mem_subgroupOf.2 (hρIb i₁))
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 h1 ⟨ρ i₂, hρΔ i₂⟩)).symm
  have hΔIb : ∀ δ ∈ Δ, ∃ i, ρ i = δ := fun δ hδ => hIbρ δ (hIbΔ hδ)
  have hN₀c : ∀ n ∈ O, ∀ δ ∈ Δ, δ * ρ n = ρ n * δ := by
    let N₀ : Subgroup ↥Δ := (O.map ρ).subgroupOf Δ
    have hN₀n : N₀.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨o, ho, hon⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
      obtain ⟨i, hi⟩ := hΔIb g g.2
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2
        ⟨i * o * i⁻¹, Subgroup.Normal.conj_mem ‹O.Normal› o ho i, ?_⟩)
      show ρ (i * o * i⁻¹) = (g : H) * (n : H) * (g : H)⁻¹
      rw [map_mul, map_mul, map_inv, hi, hon]
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hΔq hN₀n with htop | hcen
    · exfalso
      apply hQ
      have hall : ∀ i : Iabs, i ∈ O := by
        intro i
        have h1 : (⟨ρ i, hρΔ i⟩ : ↥Δ) ∈ N₀ := by
          rw [htop]
          exact Subgroup.mem_top _
        obtain ⟨o, ho, hoi⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h1)
        have h2 : o⁻¹ * i ∈ ρ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv]
          change (ρ o)⁻¹ * ρ i = 1
          rw [hoi]
          group
        have := O.mul_mem ho (hker h2)
        simpa using this
      refine Group.isSolvable_of_comm (fun a b => ?_)
      obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective b
      rw [(QuotientGroup.eq_one_iff i).2 (hall i), (QuotientGroup.eq_one_iff j).2 (hall j)]
    · intro n hn δ hδ
      have h1 : (⟨ρ n, hρΔ n⟩ : ↥Δ) ∈ N₀ := Subgroup.mem_subgroupOf.2 ⟨n, hn, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 (hcen h1) ⟨δ, hδ⟩)
  have hDΔ : ∀ d ∈ D, ∀ δ ∈ Δ, d * δ * d⁻¹ ∈ Δ := by
    intro d hd δ hδ
    obtain ⟨i, rfl⟩ := hΔIb δ hδ
    obtain ⟨j, hj⟩ := hDI d hd i
    rw [hj]
    exact hρΔ j
  have hDL : ∀ d ∈ D, conjSub d L = L ∨ conjSub d L = conjSub x⁻¹ L := by
    intro d hd
    have hdinv : d⁻¹ = d := inv_eq_of_mul_self (hD2 d hd)
    have hN₂ : IsComponent (conjSub d L) := isComponent_conjSub hL d
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hLc : ⁅conjSub d L, L⁆ = ⊥ := (distinct_components_commute hN₂ hL).resolve_left h1
    have hL'c : ⁅conjSub d L, conjSub x⁻¹ L⁆ = ⊥ :=
      (distinct_components_commute hN₂ (isComponent_conjSub hL _)).resolve_left h2
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple hL.1
    apply hab
    apply Subtype.ext
    refine comm_of_comm_swapDiag hAB a b ?_
    set δ₁ := swapDiag hAB b with hδ₁
    have hδ₂Δ : d * δ₁ * d⁻¹ ∈ Δ := hDΔ d hd δ₁ ⟨b, rfl⟩
    obtain ⟨b', hb'⟩ := hδ₂Δ
    have ha₀ : d * (a : H) * d⁻¹ ∈ conjSub d L := by
      rw [mem_conjSub']
      have : d⁻¹ * (d * (a : H) * d⁻¹) * d = a := by group
      rw [this]
      exact a.2
    have hcomm : (d * (a : H) * d⁻¹) * (d * δ₁ * d⁻¹) = (d * δ₁ * d⁻¹) * (d * (a : H) * d⁻¹) := by
      rw [← hb', swapDiag_apply]
      have hc1 := Subgroup.commutator_mem_commutator ha₀ b'.2
      have hc2 := Subgroup.commutator_mem_commutator ha₀ (conj_mem_conjSub (t := x) b'.2)
      rw [hLc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc1
      rw [hL'c, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc2
      calc d * (a : H) * d⁻¹ * ((b' : H) * (x⁻¹ * b' * x))
          = (d * (a : H) * d⁻¹ * b') * (x⁻¹ * b' * x) := by group
        _ = (b' * (d * (a : H) * d⁻¹)) * (x⁻¹ * b' * x) := by rw [hc1]
        _ = b' * ((d * (a : H) * d⁻¹) * (x⁻¹ * b' * x)) := by group
        _ = b' * ((x⁻¹ * b' * x) * (d * (a : H) * d⁻¹)) := by rw [hc2]
        _ = ((b' : H) * (x⁻¹ * b' * x)) * (d * (a : H) * d⁻¹) := by group
    calc (a : H) * δ₁ = d⁻¹ * ((d * (a : H) * d⁻¹) * (d * δ₁ * d⁻¹)) * d := by group
      _ = d⁻¹ * ((d * δ₁ * d⁻¹) * (d * (a : H) * d⁻¹)) * d := by rw [hcomm]
      _ = δ₁ * a := by group
  obtain ⟨d, hdD, hd1, hdx, hdL⟩ : ∃ d ∈ D, d ≠ 1 ∧ d ≠ x ∧ conjSub d L = L := by
    obtain ⟨x', hx'D, y', hy'D, hx'1, hy'1, hx'y'⟩ :=
      CFSG.ComponentClassification.AutL2Facts.exists_two_ne_of_card_four D hD4
    obtain ⟨d₁, hd₁D, hd₁1, hd₁x⟩ : ∃ d₁ ∈ D, d₁ ≠ 1 ∧ d₁ ≠ x := by
      by_cases hxx : x' = x
      · exact ⟨y', hy'D, hy'1, fun h => hx'y' (hxx.trans h.symm)⟩
      · exact ⟨x', hx'D, hx'1, hxx⟩
    rcases hDL d₁ hd₁D with h | h
    · exact ⟨d₁, hd₁D, hd₁1, hd₁x, h⟩
    · refine ⟨x * d₁, mul_mem hxD hd₁D, ?_, ?_, ?_⟩
      · intro h
        apply hd₁x
        rw [eq_inv_of_mul_eq_one_right h, hxinv]
      · intro h
        exact hd₁1 (mul_eq_left.1 h)
      · rw [← conjSub_conjSub, h, conjSub_conjSub, mul_inv_cancel, conjSub_one]
  have hdd : d * d = 1 := hD2 d hdD
  have hdinv : d⁻¹ = d := inv_eq_of_mul_self hdd
  have hdx' : d * x = x * d := hDcomm d hdD x hxD
  have hdNΔ : d ∈ normalizer (Δ : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hDΔ d hdD z hz, fun hz => ?_⟩
    have := hDΔ d hdD _ hz
    rwa [show d * (d * z * d⁻¹) * d⁻¹ = z by
      calc d * (d * z * d⁻¹) * d⁻¹ = (d * d) * z * (d * d)⁻¹ := by group
        _ = z := by rw [hdd]; group] at this
  have hcent : ∀ δ ∈ Δ, ∃ n ∈ O, δ⁻¹ * (d * δ * d⁻¹) = ρ n := by
    intro δ hδ
    obtain ⟨i, rfl⟩ := hΔIb δ hδ
    obtain ⟨i', hi'c, hi'O⟩ := hcov d hdD i
    have hmem : i'⁻¹ * i ∈ O := by
      have := O.inv_mem hi'O
      rwa [mul_inv_rev, inv_inv] at this
    obtain ⟨o', ho', hoeq⟩ := hDO d hdD (i'⁻¹ * i) hmem
    refine ⟨i⁻¹ * i' * o', O.mul_mem hi'O ho', ?_⟩
    have e2 : d * ρ i' * d⁻¹ = ρ i' := by
      rw [hi'c]
      group
    have e1 : ρ i = ρ i' * ρ (i'⁻¹ * i) := by
      rw [← map_mul]
      congr 1
      group
    have h1 : d * ρ i * d⁻¹ = ρ i' * ρ o' := by
      rw [e1, ← hoeq]
      calc d * (ρ i' * ρ (i'⁻¹ * i)) * d⁻¹ = (d * ρ i' * d⁻¹) * (d * ρ (i'⁻¹ * i) * d⁻¹) := by
            group
        _ = ρ i' * (d * ρ (i'⁻¹ * i) * d⁻¹) := by rw [e2]
    rw [h1]
    simp only [map_mul, map_inv]
    group
  have hdΔ : ∀ δ ∈ Δ, d * δ * d⁻¹ = δ := by
    have hα : normalizerConjHom Δ ⟨d, hdNΔ⟩ = 1 := by
      have : Group.IsPerfect ↥Δ := hΔq.1
      refine CFSG.ComponentClassification.CentralCover.eq_one_of_forall_inv_mul_mem_center _
        (fun g => ?_)
      obtain ⟨n, hn, hneq⟩ := hcent g g.2
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      show (h : H) * ((g : H)⁻¹ * (d * g * d⁻¹)) = ((g : H)⁻¹ * (d * g * d⁻¹)) * h
      rw [hneq]
      exact hN₀c n hn h h.2
    intro δ hδ
    exact congrArg Subtype.val (DFunLike.congr_fun hα ⟨δ, hδ⟩)
  have hdNL : d ∈ normalizer (L : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 : z ∈ L ↔ z ∈ conjSub d L := by rw [hdL]
    rw [h1, mem_conjSub', hdinv]
  have hdL' : ∀ m ∈ L, d * m * d⁻¹ = m := by
    have hα : normalizerConjHom L ⟨d, hdNL⟩ = 1 := by
      have : Group.IsPerfect ↥L := hL.1.1
      refine CFSG.ComponentClassification.CentralCover.eq_one_of_forall_inv_mul_mem_center _
        (fun g => ?_)
      apply ker_swapDiag_le_center hAB
      rw [MonoidHom.mem_ker]
      have hsd : swapDiag hAB (normalizerConjHom L ⟨d, hdNL⟩ g) = swapDiag hAB g := by
        rw [swapDiag_apply, swapDiag_apply]
        have hcoe : ((normalizerConjHom L ⟨d, hdNL⟩ g : ↥L) : H) = d * g * d⁻¹ := rfl
        rw [hcoe]
        have hδ := hdΔ (swapDiag hAB g) ⟨g, rfl⟩
        rw [swapDiag_apply] at hδ
        rw [← hδ]
        have hcx : d * x⁻¹ = x⁻¹ * d := by
          rw [hxinv]
          exact hdx'
        have hc := conj_conj_comm hcx (g : H)
        rw [inv_inv] at hc
        calc d * (g : H) * d⁻¹ * (x⁻¹ * (d * (g : H) * d⁻¹) * x)
            = d * (g : H) * d⁻¹ * (d * (x⁻¹ * (g : H) * x) * d⁻¹) := by rw [← hc]
          _ = d * ((g : H) * (x⁻¹ * (g : H) * x)) * d⁻¹ := by group
      rw [map_mul, map_inv, hsd]
      group
    intro m hm
    exact congrArg Subtype.val (DFunLike.congr_fun hα ⟨m, hm⟩)
  have hdM : ∀ m ∈ M, d * m = m * d := by
    intro m hm
    rcases hMLL with rfl | rfl
    · have := hdL' m hm
      rwa [mul_inv_eq_iff_eq_mul] at this
    · have hm' : x * m * x⁻¹ ∈ L := by
        have := mem_conjSub'.1 hm
        rwa [inv_inv] at this
      have h1 := hdL' _ hm'
      rw [conj_conj_comm hdx' m] at h1
      have h3 : x * (d * m * d⁻¹) = x * m := mul_right_cancel h1
      have h2 : d * m * d⁻¹ = m := mul_left_cancel h3
      rwa [mul_inv_eq_iff_eq_mul] at h2
  exact hd1 (hfaith d hdD hdM)

theorem contra_main [Finite H] {x : H} (hx2 : orderOf x = 2) {L M : Subgroup H}
    (hL : IsComponent L) (hM : IsComponent M) {r : ℕ}
    (hr : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ r = p ^ f)
    (hMsl : HasSL2Model ↥M (fun q => q = r)) (hMLL : M = L ∨ M = conjSub x⁻¹ L)
    (ρ : Iabs →* H) (O : Subgroup Iabs) [O.Normal] (hker : ρ.ker ≤ O)
    (hQ : ¬ Group.IsSolvable (Iabs ⧸ O))
    (Ib : Subgroup H) (hρIb : ∀ i, ρ i ∈ Ib) (hIbρ : ∀ b ∈ Ib, ∃ i, ρ i = b)
    (hcases : (conjSub x⁻¹ L = L ∧ Ib ≤ L) ∨ (conjSub x⁻¹ L ≠ L ∧
      ∃ hAB : ⁅L, conjSub x⁻¹ L⁆ = ⊥, Ib ≤ (swapDiag hAB).range))
    (hIsub : (Ib.subgroupOf (centralizer ({x} : Set H))).IsSubnormal)
    (D : Subgroup H) (hD4 : Nat.card D = 4) (hD2 : ∀ d ∈ D, d * d = 1) (hxD : x ∈ D)
    (hDI : ∀ d ∈ D, ∀ i, ∃ j, d * ρ i * d⁻¹ = ρ j)
    (hDO : ∀ d ∈ D, ∀ n ∈ O, ∃ n' ∈ O, d * ρ n * d⁻¹ = ρ n')
    (hcov : ∀ d ∈ D, ∀ i, ∃ i', d * ρ i' = ρ i' * d ∧ i⁻¹ * i' ∈ O)
    (hfaith : ∀ d ∈ D, (∀ m ∈ M, d * m = m * d) → d = 1) : False := by
  rcases hcases with ⟨hLL, hIL⟩ | ⟨hLL, hAB, hIs⟩
  · have hML : M = L := by
      rcases hMLL with h | h
      · exact h
      · rw [h]
        exact hLL
    exact contra_vertical hM hr hMsl ρ O hker hQ (fun i => hML ▸ hIL (hρIb i)) D hD4 hD2 hDI hcov
      hfaith
  · exact contra_diagonal hx2 hL hMLL hAB ρ O hker hQ Ib hρIb hIbρ hIs hIsub D hD4 hD2 hxD hDI hDO
      hcov hfaith

end S3Sec29B7AbsD

end CFSG.GH74.Generic.BProg.B3
