module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203KSide
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma14h
import CFSG.GH74.GLS.Stage2.Local.P27.QIdArith
import CFSG.GH74.GLS.IVK.Proofs2.Ivk714AltAut
import CFSG.GH74.GLS.Stage2.Local.P34S5Jbar
public import CFSG.Assembly.GL83LieDefs

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2 CFSG.GorensteinWalter
open CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L203


section AutL2

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem oddAut_eq_one_of_fixes_subfield
    (hF : L2Field F) (e : K ≃* L2 F) {q : ℕ} (hFq : Nat.card F = q ^ 2) (hq : Odd q) (hq3 : 3 ≤ q)
    {I : Subgroup K} (hI : IsL2 ↥I (fun r => r = q)) {α : MulAut K} (hα : Odd (orderOf α))
    (hfix : ∀ i ∈ I, α i = i) : α = 1 := by
  have hI' : IsL2 ↥I (fun q₀ => Odd q₀ ∧ 3 ≤ q₀) := by
    obtain ⟨F₀, i1, i2, hP, e₀⟩ := hI
    exact ⟨F₀, i1, i2, ⟨hP ▸ hq, hP ▸ hq3⟩, e₀⟩
  obtain ⟨⟨e', -, hle⟩, -⟩ := ivk_1_4h F hF K e I hI'
  have hcent : α ∈ Subgroup.centralizer
      ((I.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) : Set (MulAut K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨i, hi, rfl⟩
    ext k
    show (MulAut.conj i : MulAut K) (α k) = α ((MulAut.conj i : MulAut K) k)
    simp only [MulAut.conj_apply, map_mul, map_inv]
    have := hfix i hi
    rw [this]
  have hmem : α ∈ fieldAutSub e' := hle hcent
  obtain ⟨σ, hσ⟩ := hmem
  have hord : orderOf σ = orderOf α := by
    rw [← hσ]; exact (orderOf_injective (fieldAutHom e') (fieldAutHom_injective e') σ).symm
  by_contra hne
  have hσ1 : σ ≠ 1 := fun h => hne (by rw [← hσ, h, map_one])
  have hodd : Odd (orderOf σ) := hord ▸ hα
  have hr1 : orderOf σ ≠ 1 := fun h => hσ1 (orderOf_eq_one_iff.1 h)
  have hr3 : 3 ≤ orderOf σ := by
    obtain ⟨m, hm⟩ := hodd
    have : m ≠ 0 := fun h0 => hr1 (by omega)
    omega
  obtain ⟨⟨F₁, i1, i2, hq₁, ⟨ψ⟩⟩, -⟩ := (ivk_1_4a F hF K e' σ).2.1 hodd
  have hq₁' : Nat.card F₁ ^ orderOf σ = q ^ 2 := hq₁.trans hFq
  have hq₀odd : Odd (Nat.card F₁) := by
    have : Odd (Nat.card F₁ ^ orderOf σ) := hq₁' ▸ hq.pow
    exact (Nat.odd_pow_iff (by omega : orderOf σ ≠ 0)).mp this
  have hCL2 : IsL2 ↥(fixedSubgroup K (fieldAutHom e' σ)) (fun r => r = Nat.card F₁) :=
    ⟨F₁, i1, i2, rfl, ⟨ψ⟩⟩
  have hIle : I ≤ fixedSubgroup K (fieldAutHom e' σ) := by
    intro i hi
    show (fieldAutHom e' σ) i = i
    rw [hσ]; exact hfix i hi
  have hdvd : Nat.card ↥I ∣ Nat.card ↥(fixedSubgroup K (fieldAutHom e' σ)) := Subgroup.card_dvd_of_le hIle
  rw [Stage2.Local.P27.QId.card_isL2 hq hI, Stage2.Local.P27.QId.card_isL2 hq₀odd hCL2] at hdvd
  have hpos : 0 < Nat.card ↥(fixedSubgroup K (fieldAutHom e' σ)) := Nat.card_pos
  rw [Stage2.Local.P27.QId.card_isL2 hq₀odd hCL2] at hpos
  have hle2 := Nat.le_of_dvd hpos hdvd
  have hq₀3 : 3 ≤ Nat.card F₁ := by
    obtain ⟨m, hm⟩ := hq₀odd
    have : 2 ≤ Nat.card F₁ := Finite.one_lt_card
    omega
  have hqq : q ≤ Nat.card F₁ := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) < q * (q ^ 2 - 1) := by
      have hb : 1 ≤ Nat.card F₁ ^ 2 := Nat.one_le_pow _ _ (by omega)
      have ha : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [hb, ha]
      have hlt' : ((Nat.card F₁ : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast hlt
      have h3' : (3 : ℤ) ≤ (Nat.card F₁ : ℤ) := by exact_mod_cast hq₀3
      have hpos : (0 : ℤ) < (q : ℤ) ^ 2 + (q : ℤ) * (Nat.card F₁ : ℤ) + (Nat.card F₁ : ℤ) ^ 2 - 1 := by
        nlinarith
      nlinarith [mul_pos (sub_pos.2 hlt') hpos]
    have h2 : q * (q ^ 2 - 1) / 2 ≤ Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) / 2 := hle2
    have hev : 2 ∣ q * (q ^ 2 - 1) := by
      obtain ⟨m, hm⟩ := hq
      have : q ^ 2 - 1 = 4 * (m * (m + 1)) := by
        subst hm
        apply Nat.sub_eq_of_eq_add
        ring
      rw [this]
      exact ⟨q * (2 * (m * (m + 1))), by ring⟩
    omega
  have h3 : q ^ orderOf σ ≤ q ^ 2 := by
    calc q ^ orderOf σ ≤ Nat.card F₁ ^ orderOf σ := Nat.pow_le_pow_left hqq _
      _ = q ^ 2 := hq₁'
  have h4 : q ^ 3 ≤ q ^ orderOf σ := Nat.pow_le_pow_right (by omega) hr3
  have h5 : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

end AutL2


section AutA7

open Equiv Equiv.Perm

theorem not_dvd_card_centralizer (g : Perm (Fin 7)) (hg : Odd (orderOf g)) (hg1 : g ≠ 1) :
    ¬ 60 ∣ Nat.card (Subgroup.centralizer ({g} : Set (Perm (Fin 7)))) := by
  rw [Equiv.Perm.nat_card_centralizer g]
  have hmem : ∀ a ∈ g.cycleType, 3 ≤ a ∧ Odd a := by
    intro a ha
    have h2 := Equiv.Perm.two_le_of_mem_cycleType ha
    have hodd : Odd a := Odd.of_dvd_nat hg (Equiv.Perm.dvd_of_mem_cycleType ha)
    refine ⟨?_, hodd⟩
    obtain ⟨m, hm⟩ := hodd
    omega
  have hsum : g.cycleType.sum ≤ 7 := by simpa using Equiv.Perm.sum_cycleType_le g
  have hne : g.cycleType ≠ 0 := fun h => hg1 (Equiv.Perm.cycleType_eq_zero.1 h)
  have hcard : Multiset.card g.cycleType ≤ 2 := by
    have : Multiset.card g.cycleType • 3 ≤ g.cycleType.sum :=
      Multiset.card_nsmul_le_sum (fun a ha => (hmem a ha).1)
    simp only [smul_eq_mul] at this
    omega
  have hcard0 : 0 < Multiset.card g.cycleType := Multiset.card_pos.2 hne
  rcases (show Multiset.card g.cycleType = 1 ∨ Multiset.card g.cycleType = 2 by omega) with h1 | h2
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 h1
    have ha' := hmem a (by rw [ha]; simp)
    rw [ha] at hsum ⊢
    simp only [Multiset.sum_singleton] at hsum
    obtain ⟨hlo, hodd'⟩ := ha'
    obtain ⟨m, hm⟩ := hodd'
    have : a = 3 ∨ a = 5 ∨ a = 7 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  · obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 h2
    have ha' := hmem a (by rw [hab]; simp)
    have hb' := hmem b (by rw [hab]; simp)
    rw [hab] at hsum ⊢
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum
    obtain ⟨m, hm⟩ := ha'.2
    obtain ⟨n, hn⟩ := hb'.2
    have : a = 3 ∧ b = 3 := by omega
    obtain ⟨rfl, rfl⟩ := this
    decide

theorem oddAut_eq_one_of_fixes_A5 {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 7))
    {I : Subgroup K} (hI : IsL2 ↥I (fun r => r = 5)) {α : MulAut K} (hα : Odd (orderOf α))
    (hfix : ∀ i ∈ I, α i = i) : α = 1 := by
  have hn : 7 ≤ 7 := le_rfl
  set θ := CFSG.GH74.GLS.IVK.Proofs2.altAutEquiv hn e with hθ
  set g := θ α with hg
  have hgord : orderOf g = orderOf α := MulEquiv.orderOf_eq θ α
  by_contra hne
  have hg1 : g ≠ 1 := fun h => hne (θ.injective (by rw [← hg, h, map_one]))
  have hcomm : ∀ i ∈ I, g * CFSG.GH74.GLS.IVK.Proofs2.psiAlt e i =
      CFSG.GH74.GLS.IVK.Proofs2.psiAlt e i * g := by
    intro i hi
    have h1 := CFSG.GH74.GLS.IVK.Proofs2.altAutEquiv_spec hn e α i
    rw [hfix i hi] at h1
    rw [← hθ, ← hg] at h1
    calc g * CFSG.GH74.GLS.IVK.Proofs2.psiAlt e i
        = (g * CFSG.GH74.GLS.IVK.Proofs2.psiAlt e i * g⁻¹) * g := by group
      _ = CFSG.GH74.GLS.IVK.Proofs2.psiAlt e i * g := by rw [← h1]
  have hle : I.map (CFSG.GH74.GLS.IVK.Proofs2.psiAlt e) ≤
      Subgroup.centralizer ({g} : Set (Perm (Fin 7))) := by
    rintro _ ⟨i, hi, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcomm i hi
  have hcard : Nat.card ↥(I.map (CFSG.GH74.GLS.IVK.Proofs2.psiAlt e)) = 60 := by
    rw [Subgroup.card_map_of_injective (CFSG.GH74.GLS.IVK.Proofs2.psiAlt_injective e),
      Stage2.Local.P27.QId.card_isL2 (by decide : Odd 5) hI]
    norm_num
  have hdvd : 60 ∣ Nat.card (Subgroup.centralizer ({g} : Set (Perm (Fin 7)))) := by
    rw [← hcard]; exact Subgroup.card_dvd_of_le hle
  exact not_dvd_card_centralizer g (hgord ▸ hα) hg1 hdvd

end AutA7

section StepA

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem stepA {O K Q I : Subgroup X} [O.Normal] [K.Normal] (hIK : I ≤ K)
    (hIO : ∀ i ∈ I, i ∈ O → i = 1) (hIQ : ∀ i ∈ I, ∀ q ∈ Q, i * q = q * i)
    (hQodd : Odd (Nat.card Q))
    (hAut : ∀ (J : Subgroup ↥(K.map (QuotientGroup.mk' O))) (α : MulAut ↥(K.map (QuotientGroup.mk' O))),
      Nonempty (↥J ≃* ↥I) → Odd (orderOf α) → (∀ j ∈ J, α j = j) → α = 1) :
    Q ≤ (Subgroup.centralizer ((K.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) : Set (X ⧸ O))).comap
      (QuotientGroup.mk' O) := by
  set π : X →* X ⧸ O := QuotientGroup.mk' O with hπ
  set Kb : Subgroup (X ⧸ O) := K.map π with hKb
  have hKbn : Kb.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective O)
  have hIKb : I.map π ≤ Kb := Subgroup.map_mono hIK
  set J : Subgroup ↥Kb := (I.map π).subgroupOf Kb with hJ
  have hinj : Function.Injective (π.comp I.subtype) := by
    rw [injective_iff_map_eq_one]
    intro i hi
    have : (i : X) ∈ O := (QuotientGroup.eq_one_iff _).1 hi
    exact Subtype.ext (hIO i i.2 this)
  have hJI : Nonempty (↥J ≃* ↥I) := by
    let e1 : ↥J ≃* ↥(I.map π) := Subgroup.subgroupOfEquivOfLe hIKb
    let e2 : ↥I ≃* ↥(π.comp I.subtype).range := MonoidHom.ofInjective hinj
    let e3 : ↥(π.comp I.subtype).range ≃* ↥(I.map π) :=
      MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype])
    exact ⟨e1.trans (e3.symm.trans e2.symm)⟩
  intro q hq
  show π q ∈ Subgroup.centralizer (Kb : Set (X ⧸ O))
  let α : MulAut ↥Kb := MulAut.conjNormal (H := Kb) (π q)
  have hαord : Odd (orderOf α) := by
    have h1 : orderOf α ∣ orderOf (π q) := orderOf_map_dvd (MulAut.conjNormal (H := Kb)) (π q)
    have h2 : orderOf (π q) ∣ orderOf q := orderOf_map_dvd π q
    have h3 : orderOf q ∣ Nat.card ↥Q := by
      have := orderOf_dvd_natCard (⟨q, hq⟩ : ↥Q)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hQodd (h1.trans (h2.trans h3))
  have hfix : ∀ j ∈ J, α j = j := by
    intro j hj
    obtain ⟨i, hi, hij⟩ := Subgroup.mem_subgroupOf.1 hj
    apply Subtype.ext
    show π q * (j : X ⧸ O) * (π q)⁻¹ = (j : X ⧸ O)
    rw [← hij, ← map_mul, ← map_inv, ← map_mul]
    have := hIQ i hi q hq
    congr 1
    calc q * i * q⁻¹ = (i * q) * q⁻¹ := by rw [← this]
      _ = i := by group
  have h1 := hAut J α hJI hαord hfix
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hb' : (⟨b, hb⟩ : ↥Kb) = α ⟨b, hb⟩ := by rw [h1]; rfl
  have := congrArg Subtype.val hb'
  simp only [α, MulAut.conjNormal_apply] at this
  show b * π q = π q * b
  calc b * π q = (π q * b * (π q)⁻¹) * π q := by rw [← this]
    _ = π q * b := by group

end StepA

theorem not_quaternion_equiv_dihedral_four : ¬ Nonempty (QuaternionGroup 2 ≃* DihedralGroup 4) := by
  rintro ⟨e⟩
  have h1 : Fintype.card {x : QuaternionGroup 2 // x * x = 1 ∧ x ≠ 1} = 1 := by decide
  have h2 : Fintype.card {x : DihedralGroup 4 // x * x = 1 ∧ x ≠ 1} = 5 := by decide
  have hiff : ∀ x : QuaternionGroup 2, (x * x = 1 ∧ x ≠ 1) ↔ (e x * e x = 1 ∧ e x ≠ 1) := by
    intro x
    constructor
    · rintro ⟨h, hne⟩
      refine ⟨?_, fun h' => hne (e.injective (by rw [h', map_one]))⟩
      rw [← map_mul, h, map_one]
    · rintro ⟨h, hne⟩
      refine ⟨?_, fun h' => hne (by rw [h', map_one])⟩
      apply e.injective
      rw [map_mul, h, map_one]
  have : Fintype.card {x : QuaternionGroup 2 // x * x = 1 ∧ x ≠ 1} =
      Fintype.card {x : DihedralGroup 4 // x * x = 1 ∧ x ≠ 1} :=
    Fintype.card_congr (Equiv.subtypeEquiv e.toEquiv (fun x => hiff x))
  omega


theorem not_quaternion_of_hasDihedralSylowTwo {X : Type} [Group X] [Finite X]
    (h : HasDihedralSylowTwo X) (H : Subgroup X) : ¬ Nonempty (↥H ≃* QuaternionGroup 2) := by
  rintro ⟨f⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥H = 8 := by
    rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hp : IsPGroup 2 ↥H := by
    rw [IsPGroup.iff_card]
    exact ⟨3, by rw [hcard]; norm_num⟩
  obtain ⟨S, hHS⟩ := hp.exists_le_sylow
  obtain ⟨m, hm, ⟨e⟩⟩ := h S
  set H' : Subgroup ↥(S : Subgroup X) := H.subgroupOf (S : Subgroup X) with hH'
  set H'' : Subgroup (DihedralGroup (2 ^ m)) := H'.map (e.toMonoidHom) with hH''
  let g : ↥H'' ≃* ↥H :=
    (Subgroup.equivMapOfInjective H' e.toMonoidHom e.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hHS)
  rcases GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral hm H'' with hc | ⟨k, hk, ⟨d⟩⟩
  · have hcyc : IsCyclic (QuaternionGroup 2) := (g.trans f).isCyclic.1 hc
    have hcomm : IsMulCommutative (QuaternionGroup 2) := hcyc.isMulCommutative
    have : ∀ a b : QuaternionGroup 2, a * b = b * a := fun a b => hcomm.is_comm.comm a b
    exact absurd (this (QuaternionGroup.a 1) (QuaternionGroup.xa 0)) (by decide)
  · have hk2 : Nat.card (DihedralGroup (2 ^ k)) = 8 := by
      have := Nat.card_congr (d.symm.trans (g.trans f)).toEquiv
      rw [this, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [DihedralGroup.nat_card] at hk2
    have hk3 : 2 ^ k = 4 := by omega
    have hk4 : k = 2 := by
      have : (2 : ℕ) ^ k = 2 ^ 2 := by rw [hk3]; norm_num
      exact Nat.pow_right_injective (le_refl 2) this
    subst hk4
    exact not_quaternion_equiv_dihedral_four ⟨(d.symm.trans (g.trans f)).symm⟩


section Combine

variable {G : Type} [Group G]

theorem hAut_of_fullCL4 [Finite G] {t : G} {q : ℕ}
    (hq : Odd q) (hq5 : 5 ≤ q) (hc : CFSG.GH74.GLS.Stage2.Local.P27.FullCL4 t q)
    {I : Subgroup ↥(centralizer ({t} : Set G))} (hI : IsL2 ↥I (fun r => r = q)) :
    ∀ (J : Subgroup ↥((KX t).map (QuotientGroup.mk' (OX t))))
      (α : MulAut ↥((KX t).map (QuotientGroup.mk' (OX t)))),
      Nonempty (↥J ≃* ↥I) → Odd (orderOf α) → (∀ j ∈ J, α j = j) → α = 1 := by
  intro J α hJI hα hfix
  obtain ⟨e⟩ := KXb_equiv t
  have hJ : IsL2 ↥J (fun r => r = q) := by
    obtain ⟨F₀, i1, i2, hP, ⟨e₀⟩⟩ := hI
    obtain ⟨f⟩ := hJI
    exact ⟨F₀, i1, i2, hP, ⟨f.trans e₀⟩⟩
  rcases hc with ⟨F, i1, i2, hF, ⟨eL⟩⟩ | ⟨hq5', ⟨eA⟩⟩
  · have hF' : Nat.card F = q ^ 2 := hF
    have hFL : L2Field F := by
      refine ⟨?_, ?_⟩
      · rw [hF']; exact hq.pow
      · rw [hF']; nlinarith
    exact oddAut_eq_one_of_fixes_subfield hFL (e.trans eL) hF' hq (by omega) hJ hα hfix
  · subst hq5'
    exact oddAut_eq_one_of_fixes_A5 (e.trans eA) hJ hα hfix

theorem hasDihedralSylowTwo_KXb [Finite G] {t : G} {q : ℕ} (hq : Odd q)
    (hc : CFSG.GH74.GLS.Stage2.Local.P27.FullCL4 t q) :
    HasDihedralSylowTwo ↥((KX t).map (QuotientGroup.mk' (OX t))) := by
  obtain ⟨e⟩ := KXb_equiv t
  have hD : Stage2.Local.P34.DihJ (↥(Jx t) ⧸ pPrimeCore 2 ↥(Jx t)) := by
    rcases hc with ⟨F, i1, i2, hF, ⟨eL⟩⟩ | ⟨-, hA⟩
    · left
      refine ⟨F, i1, i2, ?_, ⟨eL⟩⟩
      rw [show Nat.card F = q ^ 2 from hF]; exact hq.pow
    · exact Or.inr hA
  have := hD.hasDihedralSylowTwo
  exact GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e this

theorem false_of_quaternion [Finite G] {t : G} {q : ℕ} (hq : Odd q)
    (hc : CFSG.GH74.GLS.Stage2.Local.P27.FullCL4 t q)
    {I H : Subgroup ↥(centralizer ({t} : Set G))} (hIK : I ≤ KX t)
    (hIO : ∀ i ∈ I, i ∈ OX t → i = 1) (hHI : H ≤ I)
    (hHq : Nonempty (↥H ≃* QuaternionGroup 2)) : False := by
  have := KX_normal t
  have : (OX t).Normal := inferInstance
  set π := QuotientGroup.mk' (OX t)
  have hinj : Function.Injective (π.comp H.subtype) := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have : (h : ↥(centralizer ({t} : Set G))) ∈ OX t := (QuotientGroup.eq_one_iff _).1 hh
    exact Subtype.ext (hIO h (hHI h.2) this)
  have hHK : H.map π ≤ (KX t).map π := Subgroup.map_mono (hHI.trans hIK)
  obtain ⟨f⟩ := hHq
  let e1 : ↥H ≃* ↥(π.comp H.subtype).range := MonoidHom.ofInjective hinj
  let e2 : ↥(π.comp H.subtype).range ≃* ↥(H.map π) :=
    MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype])
  let e3 : ↥((H.map π).subgroupOf ((KX t).map π)) ≃* ↥(H.map π) :=
    Subgroup.subgroupOfEquivOfLe hHK
  exact not_quaternion_of_hasDihedralSylowTwo (hasDihedralSylowTwo_KXb hq hc)
    ((H.map π).subgroupOf ((KX t).map π)) ⟨e3.trans (e2.symm.trans (e1.symm.trans f))⟩

theorem stepA_of_fullCL4 [Finite G] {t : G} {q : ℕ}
    (hq : Odd q) (hq5 : 5 ≤ q) (hc : CFSG.GH74.GLS.Stage2.Local.P27.FullCL4 t q)
    {Q I : Subgroup ↥(centralizer ({t} : Set G))} (hIK : I ≤ KX t)
    (hIO : ∀ i ∈ I, i ∈ OX t → i = 1) (hIQ : ∀ i ∈ I, ∀ q ∈ Q, i * q = q * i)
    (hQodd : Odd (Nat.card Q))
    (hI : IsL2 ↥I (fun r => r = q) ∨ ∃ H : Subgroup ↥(centralizer ({t} : Set G)), H ≤ I ∧
      Nonempty (↥H ≃* QuaternionGroup 2)) :
    Q ≤ Ctil t := by
  have := KX_normal t
  have : (OX t).Normal := inferInstance
  rcases hI with hI | ⟨H, hHI, hHq⟩
  · exact stepA hIK hIO hIQ hQodd (hAut_of_fullCL4 hq hq5 hc hI)
  · exact (false_of_quaternion hq hc hIK hIO hHI hHq).elim

end Combine

end CFSG.GH74.GLS.Stage2.Final.Thm6.L203
