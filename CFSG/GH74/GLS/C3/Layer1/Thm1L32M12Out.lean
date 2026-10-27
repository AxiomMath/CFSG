module

public import CFSG.GH74.KGroups.TwoM12Inner
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalOuter
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBActionKernel
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndSix

public section

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Sporadic.Schreier
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32.M12O

theorem exists_mul_of_mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
          _ = a₁ * (a₂ * b₁) * b₂ := by rw [← hAB a₂ ha₂ b₁ hb₁]
          _ = a₁ * a₂ * (b₁ * b₂) := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have := hAB a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := this.symm }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by group⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, by group⟩)
  exact hle hx

theorem eq_fixedD_of_perfect
    {R : Subgroup NativeSporadic.M12} (hRD : R ≤ fixedD) (hR : ⁅R, R⁆ = R) (hne : R ≠ ⊥) :
    R = fixedD := by
  let e : ↥fixedD ≃* ↥(alternatingGroup (Fin 5)) := fivePointEquiv
  let R₀ : Subgroup ↥fixedD := R.subgroupOf fixedD
  let ι : ↥fixedD →* Equiv.Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := fun a b hab => e.injective (Subtype.ext hab)
  have hR₀perf : ⁅R₀, R₀⁆ = R₀ := by
    apply Subgroup.map_injective fixedD.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hRD, hR]
  have hR₀ne : R₀ ≠ ⊥ := by
    intro h
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (⟨x, hRD hx⟩ : ↥fixedD) ∈ R.subgroupOf fixedD := hx
    rw [show R.subgroupOf fixedD = R₀ from rfl, h, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  let R₁ : Subgroup (Equiv.Perm (Fin 5)) := R₀.map ι
  have hR₁perf : Group.IsPerfect ↥R₁ :=
    Subgroup.isPerfect_iff.2 (by rw [← Subgroup.map_commutator, hR₀perf])
  have hR₁ne : R₁ ≠ ⊥ := by
    intro h
    apply hR₀ne
    exact (Subgroup.map_eq_bot_iff_of_injective R₀ hι).1 h
  have hA := CFSG.RankThree.PartTwo.Sec4.Census.perfect_perm_five hR₁perf hR₁ne
  have hcardA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
  have hcardD : Nat.card fixedD = 60 := by rw [Nat.card_congr e.toEquiv, hcardA]
  have h1 : Nat.card R₁ = Nat.card R₀ := Subgroup.card_map_of_injective hι
  have h2 : Nat.card R₀ = Nat.card R := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRD).toEquiv
  have h3 : Nat.card R₁ = 60 := by rw [hA, hcardA]
  exact Subgroup.eq_of_le_of_card_ge hRD (by omega)


theorem mul_conj_mul_inv' {G : Type*} [Group G] (φ : MulAut G) (k : G) :
    φ * MulAut.conj k * φ⁻¹ = MulAut.conj (φ k) := by
  ext a
  simp [MulAut.conj_apply]

theorem aut_commuting_with_outer
    {α γ : MulAut NativeSporadic.M12} {a : NativeSporadic.M12}
    (ha : α = MulAut.conj a * beta * (MulAut.conj a)⁻¹) (hγ : γ * α = α * γ) :
    ∃ m : NativeSporadic.M12, α m = m ∧ ∀ y, α y = y → γ y = m * y * m⁻¹ := by
  set c : MulAut NativeSporadic.M12 := MulAut.conj a with hc
  have hβ : beta = c⁻¹ * α * c := by rw [ha]; group
  obtain ⟨x, hx⟩ := exists_conj_or_conj_mul_beta (c⁻¹ * γ * c)
  have hcomm : (c⁻¹ * γ * c) * beta = beta * (c⁻¹ * γ * c) := by
    rw [hβ]
    calc c⁻¹ * γ * c * (c⁻¹ * α * c) = c⁻¹ * (γ * α) * c := by group
      _ = c⁻¹ * (α * γ) * c := by rw [hγ]
      _ = c⁻¹ * α * c * (c⁻¹ * γ * c) := by group
  have hγeq : γ = c * (c⁻¹ * γ * c) * c⁻¹ := by group
  have hbinv : beta⁻¹ = beta := inv_eq_of_mul_eq_one_right beta_mul_self
  rcases hx with hx | hx
  ·
    rw [hx] at hcomm
    have h1 : MulAut.conj (beta x) = MulAut.conj x := by
      rw [← mul_conj_mul_inv']
      calc beta * MulAut.conj x * beta⁻¹ = (MulAut.conj x * beta) * beta⁻¹ := by rw [hcomm]
        _ = MulAut.conj x := by group
    have hxβ : beta x = x := conj_injective h1
    refine ⟨a * x * a⁻¹, ?_, fun y _ => ?_⟩
    · rw [ha]
      exact conj_beta_apply_conj a x hxβ
    · rw [hγeq, hx]
      simp [hc, MulAut.conj_apply, mul_assoc]
  ·
    rw [hx] at hcomm
    have h1 : MulAut.conj (beta x) = MulAut.conj x := by
      rw [← mul_conj_mul_inv', hbinv]
      calc beta * MulAut.conj x * beta = beta * (MulAut.conj x * beta) := by group
        _ = (MulAut.conj x * beta) * beta := hcomm.symm
        _ = MulAut.conj x * (beta * beta) := by group
        _ = MulAut.conj x := by rw [beta_mul_self]; group
    have hxβ : beta x = x := conj_injective h1
    refine ⟨a * x * a⁻¹, ?_, fun y hy => ?_⟩
    · rw [ha]
      exact conj_beta_apply_conj a x hxβ
    · have hγm : γ = MulAut.conj (a * x * a⁻¹) * α := by
        rw [hγeq, hx, ha]
        simp only [map_mul, map_inv, hc]
        group
      rw [hγm, MulAut.mul_apply, hy, MulAut.conj_apply]

theorem decomp_fixSub
    (a m : NativeSporadic.M12) (hm : (MulAut.conj a * beta * (MulAut.conj a)⁻¹) m = m) :
    ∃ z' : NativeSporadic.M12, (∀ d ∈ fixedD.map (MulAut.conj a).toMonoidHom, z' * d = d * z') ∧
      ∃ d₁ ∈ fixedD.map (MulAut.conj a).toMonoidHom, m = z' * d₁ := by
  have hmem : m ∈ fixSub (MulAut.conj a * beta * (MulAut.conj a)⁻¹) := hm
  rw [fixSub_conj_beta] at hmem
  obtain ⟨x, hx, rfl⟩ := hmem
  obtain ⟨-, -, -, -, -, -, -, -, hsup, -, hzc, -, -, -, -⟩ :=
    ctss_m12_pinned_outer_fixed_product_and_five_point_map
  rw [← hsup] at hx
  have hAB : ∀ u ∈ Subgroup.zpowers elemZ, ∀ b ∈ fixedD, u * b = b * u := by
    intro u hu b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    exact ((Commute.zpow_left (show Commute elemZ b from hzc b hb) k)).eq
  obtain ⟨zz, hzz, d, hd, rfl⟩ := exists_mul_of_mem_sup_of_commute hAB hx
  refine ⟨MulAut.conj a zz, ?_, MulAut.conj a d, ⟨d, hd, rfl⟩, by simp [map_mul]⟩
  rintro _ ⟨d', hd', rfl⟩
  have := hAB zz hzz d' hd'
  show MulAut.conj a zz * MulAut.conj a d' = MulAut.conj a d' * MulAut.conj a zz
  rw [← map_mul, ← map_mul, this]


theorem core
    {H : Type} [Group H] {L : Subgroup H} [L.Normal]
    (hL : CFSG.GH74.E2.Shape2M12 ↥L) (s : H) (hs2 : s * s = 1)
    (hout : ¬ ∃ u ∈ L, ∀ l ∈ L, s * l * s⁻¹ = u * l * u⁻¹)
    (P : Subgroup H) (hPL : P ≤ L) (hP : ⁅P, P⁆ = P) (hP1 : P ≠ ⊥)
    (hPs : ∀ x ∈ P, s * x * s⁻¹ = x)
    (g : H) (hgs : g * s = s * g) (hgP : ∀ p ∈ P, g * p * g⁻¹ ∈ P) :
    ∃ d ∈ P, ∀ p ∈ P, g * p * g⁻¹ = d * p * d⁻¹ := by
  classical
  obtain ⟨t, π, hc⟩ := CFSG.GH74.KGroups.TwoM12.exists_isCover hL
  have hperfL : Group.IsPerfect ↥L := hL.1.1
  have hkerZ : π.ker = center ↥L := hc.ker_eq.trans hc.center_eq.symm
  let θ : H →* MulAut NativeSporadic.M12 := CentralCover.fullAction π hc.surjective hkerZ
  have hθapp : ∀ (h : H) (l : ↥L), θ h (π l) = π (MulAut.conjNormal h l) :=
    CentralCover.fullAction_apply π hc.surjective hkerZ
  set α : MulAut NativeSporadic.M12 := θ s with hαdef
  set γ : MulAut NativeSporadic.M12 := θ g with hγdef
  have hαα : α * α = 1 := by rw [hαdef, ← map_mul, hs2, map_one]
  have hγα : γ * α = α * γ := by rw [hαdef, hγdef, ← map_mul, ← map_mul, hgs]
  have hαout : α ∉ inner NativeSporadic.M12 := by
    rintro ⟨m, hm⟩
    obtain ⟨u, rfl⟩ := hc.surjective m
    apply hout
    refine ⟨(u : H), u.2, fun l hl => ?_⟩
    have hu : θ (u : H) = α := (CentralCover.fullAction_coe π hc.surjective hkerZ u).trans hm
    have h1 : θ ((u : H)⁻¹ * s) = 1 := by
      rw [map_mul, map_inv, hu]
      exact inv_mul_cancel α
    have hcent : (u : H)⁻¹ * s ∈ centralizer (L : Set H) :=
      (CentralCover.mem_ker_fullAction_iff π hc.surjective hkerZ ((u : H)⁻¹ * s)).1
        ((MonoidHom.mem_ker).2 h1)
    have h2 := mem_centralizer_iff.1 hcent l hl
    calc s * l * s⁻¹ = (u : H) * (((u : H)⁻¹ * s) * l) * s⁻¹ := by group
      _ = (u : H) * (l * ((u : H)⁻¹ * s)) * s⁻¹ := by rw [← h2]
      _ = (u : H) * l * (u : H)⁻¹ := by group
  have hα2 : orderOf α = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hαα) (fun h => hαout (h ▸ one_mem _))
  obtain ⟨a, ha⟩ := exists_conj_beta_of_outer hα2 hαout
  obtain ⟨m, hmα, hmγ⟩ := aut_commuting_with_outer ha hγα
  have hm' : (MulAut.conj a * beta * (MulAut.conj a)⁻¹) m = m := by rw [← ha]; exact hmα
  obtain ⟨z', hz'c, d₁, hd₁, hmeq⟩ := decomp_fixSub a m hm'
  let P' : Subgroup ↥L := P.subgroupOf L
  have hP'perf : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPL, hP]
  have hP'ne : P' ≠ ⊥ := by
    intro h
    apply hP1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (⟨x, hPL hx⟩ : ↥L) ∈ P.subgroupOf L := hx
    rw [show P.subgroupOf L = P' from rfl, h, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  let Q : Subgroup NativeSporadic.M12 := P'.map π
  have hQα : ∀ q ∈ Q, α q = q := by
    rintro _ ⟨l, hl, rfl⟩
    rw [hαdef, hθapp]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact hPs l hl
  have hQperf : ⁅Q, Q⁆ = Q := by rw [← Subgroup.map_commutator, hP'perf]
  have hQne : Q ≠ ⊥ := by
    intro hQ
    have hle : P' ≤ π.ker := (Subgroup.map_eq_bot_iff P').1 hQ
    rw [hc.ker_eq, ← hc.center_eq] at hle
    apply hP'ne
    rw [← hP'perf, eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 (hle hx) y).symm
  have hQfix : Q ≤ fixSub α := fun q hq => hQα q hq
  have hD'eq : ⁅fixSub α, fixSub α⁆ = fixedD.map (MulAut.conj a).toMonoidHom := by
    rw [ha]; exact commutator_fixSub_conj_beta a
  have hQD : Q ≤ fixedD.map (MulAut.conj a).toMonoidHom := by
    rw [← hD'eq]
    calc Q = ⁅Q, Q⁆ := hQperf.symm
      _ ≤ ⁅fixSub α, fixSub α⁆ := Subgroup.commutator_mono hQfix hQfix
  let R : Subgroup NativeSporadic.M12 := Q.map (MulAut.conj a⁻¹).toMonoidHom
  have hconj : ∀ y : NativeSporadic.M12, (MulAut.conj a⁻¹) (MulAut.conj a y) = y := by
    intro y
    simp only [MulAut.conj_apply]
    group
  have hconj' : ∀ y : NativeSporadic.M12, (MulAut.conj a) (MulAut.conj a⁻¹ y) = y := by
    intro y
    simp only [MulAut.conj_apply]
    group
  have hRD : R ≤ fixedD := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hQD hq
    show (MulAut.conj a⁻¹) (MulAut.conj a y) ∈ fixedD
    rw [hconj]
    exact hy
  have hRperf : ⁅R, R⁆ = R := by rw [← Subgroup.map_commutator, hQperf]
  have hRne : R ≠ ⊥ := fun h =>
    hQne ((Subgroup.map_eq_bot_iff_of_injective Q (MulAut.conj a⁻¹).injective).1 h)
  have hReq : R = fixedD := eq_fixedD_of_perfect hRD hRperf hRne
  have hd₁Q : d₁ ∈ Q := by
    obtain ⟨y, hy, rfl⟩ := hd₁
    have hyR : y ∈ R := hReq ▸ hy
    obtain ⟨q, hq, hqy⟩ := hyR
    have hqy' : (MulAut.conj a⁻¹) q = y := hqy
    show (MulAut.conj a) y ∈ Q
    rw [← hqy', hconj']
    exact hq
  obtain ⟨dl, hdl, hπd⟩ := hd₁Q
  set d : H := (dl : H) with hd
  have hdP : d ∈ P := hdl
  have hkey : ∀ l : ↥L, l ∈ P' → π (MulAut.conjNormal g l) = π (dl * l * dl⁻¹) := by
    intro l hl
    have hπl : π l ∈ Q := ⟨l, hl, rfl⟩
    rw [← hθapp g l]
    show γ (π l) = _
    rw [hmγ (π l) (hQα _ hπl), hmeq, map_mul, map_mul, map_inv, hπd]
    have hmem : d₁ * π l * d₁⁻¹ ∈ fixedD.map (MulAut.conj a).toMonoidHom :=
      mul_mem (mul_mem hd₁ (hQD hπl)) (inv_mem hd₁)
    have := hz'c _ hmem
    calc z' * d₁ * π l * (z' * d₁)⁻¹ = z' * (d₁ * π l * d₁⁻¹) * z'⁻¹ := by group
      _ = d₁ * π l * d₁⁻¹ := by rw [this]; group
  have hperfP : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hP
  let Θ : ↥P →* ↥P :=
    ((MulAut.conj (d⁻¹ * g)).toMonoidHom.comp P.subtype).codRestrict P (fun p => by
      have h1 : g * (p : H) * g⁻¹ ∈ P := hgP p p.2
      have h2 : (MulAut.conj (d⁻¹ * g)) (p : H) = d⁻¹ * (g * (p : H) * g⁻¹) * d := by
        simp [MulAut.conj_apply, mul_assoc]
      show (MulAut.conj (d⁻¹ * g)) (p : H) ∈ P
      rw [h2]
      exact mul_mem (mul_mem (inv_mem hdP) h1) hdP)
  have hΘapp : ∀ p : ↥P, ((Θ p : ↥P) : H) = d⁻¹ * (g * (p : H) * g⁻¹) * d := by
    intro p
    show (MulAut.conj (d⁻¹ * g)) (p : H) = _
    simp [MulAut.conj_apply, mul_assoc]
  have hcentral : ∀ p : ↥P, p⁻¹ * Θ p ∈ center ↥P := by
    intro p
    have hp : (p : H) ∈ L := hPL p.2
    let lp : ↥L := ⟨p, hp⟩
    have hlp : lp ∈ P' := p.2
    have hπ1 : π (lp⁻¹ * (dl⁻¹ * MulAut.conjNormal g lp * dl)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hkey lp hlp, map_mul, map_mul, map_inv, hπd]
      group
    have hker : lp⁻¹ * (dl⁻¹ * MulAut.conjNormal g lp * dl) ∈ π.ker := hπ1
    rw [hc.ker_eq, ← hc.center_eq] at hker
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    have hq : (q : H) ∈ L := hPL q.2
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hker ⟨q, hq⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hΘapp]
    simpa [hd, mul_assoc] using h2
  have hΘ : Θ = MonoidHom.id ↥P :=
    PerfectAutomorphisms.hom_eq_id_of_central_displacement Θ hcentral
  refine ⟨d, hdP, fun p hp => ?_⟩
  have h3 := congrArg (fun f : ↥P →* ↥P => ((f ⟨p, hp⟩ : ↥P) : H)) hΘ
  simp only [hΘapp, MonoidHom.id_apply] at h3
  calc g * p * g⁻¹ = d * (d⁻¹ * (g * p * g⁻¹) * d) * d⁻¹ := by group
    _ = d * p * d⁻¹ := by rw [h3]


theorem mem_normalizer_of_forall {Z : Type} [Group Z] [Finite Z] (L : Subgroup Z) (g : Z)
    (hg : ∀ l ∈ L, g * l * g⁻¹ ∈ L) : g ∈ normalizer (L : Set Z) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : L.map (MulAut.conj g).toMonoidHom ≤ L := by
    rintro _ ⟨l, hl, rfl⟩
    exact hg l hl
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

end CFSG.GH74.GLS.C3.Layer1.Thm1L32.M12O

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32

open CFSG.GH74.GLS.C3.Layer1.Thm1L32.M12O

theorem m12_outer_centralizer_inner
    {Z : Type} [Group Z] [Finite Z] (L : Subgroup Z)
    (hL : CFSG.GH74.E2.Shape2M12 ↥L) (s : Z) (hs2 : s * s = 1)
    (hsL : ∀ l ∈ L, s * l * s⁻¹ ∈ L)
    (hout : ¬ ∃ u ∈ L, ∀ l ∈ L, s * l * s⁻¹ = u * l * u⁻¹)
    (P : Subgroup Z) (hPL : P ≤ L) (hP : ⁅P, P⁆ = P) (hP1 : P ≠ ⊥)
    (hPs : ∀ x ∈ P, s * x * s⁻¹ = x)
    (g : Z) (hgs : g * s = s * g) (hgL : ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hgP : ∀ p ∈ P, g * p * g⁻¹ ∈ P) :
    ∃ d ∈ P, ∀ p ∈ P, g * p * g⁻¹ = d * p * d⁻¹ := by
  set N : Subgroup Z := normalizer (L : Set Z) with hN
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hsN : s ∈ N := mem_normalizer_of_forall L s hsL
  have hgN : g ∈ N := mem_normalizer_of_forall L g hgL
  let L' : Subgroup ↥N := L.subgroupOf N
  have hL'N : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2 le_rfl
  have hL' : CFSG.GH74.E2.Shape2M12 ↥L' :=
    CFSG.GH74.E2.Shape2M12.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLN).symm hL
  let s' : ↥N := ⟨s, hsN⟩
  let g' : ↥N := ⟨g, hgN⟩
  let P' : Subgroup ↥N := P.subgroupOf N
  have hP'L' : P' ≤ L' := Subgroup.subgroupOf_mono N hPL
  have hP'perf : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hPL.trans hLN), hP]
  have hP'ne : P' ≠ ⊥ := by
    intro h
    apply hP1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (⟨x, hLN (hPL hx)⟩ : ↥N) ∈ P.subgroupOf N := hx
    rw [show P.subgroupOf N = P' from rfl, h, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  have hout' : ¬ ∃ u ∈ L', ∀ l ∈ L', s' * l * s'⁻¹ = u * l * u⁻¹ := by
    rintro ⟨u, hu, hall⟩
    apply hout
    refine ⟨(u : Z), hu, fun l hl => ?_⟩
    have := congrArg Subtype.val (hall ⟨l, hLN hl⟩ hl)
    exact this
  obtain ⟨d', hd'P, hd'⟩ := core (L := L') hL' s' (Subtype.ext hs2) hout' P' hP'L' hP'perf hP'ne
    (fun x hx => Subtype.ext (hPs x hx)) g' (Subtype.ext hgs) (fun p hp => hgP p hp)
  refine ⟨(d' : Z), hd'P, fun p hp => ?_⟩
  have := congrArg Subtype.val (hd' ⟨p, hLN (hPL hp)⟩ hp)
  exact this

end CFSG.GH74.GLS.C3.Layer1.Thm1L32
