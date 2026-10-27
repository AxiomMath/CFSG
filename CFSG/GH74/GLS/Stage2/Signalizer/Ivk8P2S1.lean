module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S1Rank
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der62
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Closed
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt17
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt18

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.GH74.Uniqueness.SU.SU1
open scoped commutatorElement

section Small

variable {G : Type} [Group G] [Finite G]

theorem Fm_commute_Em (H : Subgroup G) {a b : G} (ha : a ∈ Fm H) (hb : b ∈ Em H) :
    a * b = b * a := by
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have h1 : ⁅a', b'⁆ ∈ ⁅fittingSubgroup ↥H, layer ↥H⁆ := Subgroup.commutator_mem_commutator ha' hb'
  rw [CFSG.LocalCores.fitting_layer_commute, Subgroup.mem_bot] at h1
  have h2 : a' * b' = b' * a' := commutatorElement_eq_one_iff_mul_comm.1 h1
  exact congrArg Subtype.val h2

theorem Op2_commute_pPrimeCoreOf (M : Subgroup G) {a b : G} (ha : a ∈ Op 2 M)
    (hb : b ∈ pPrimeCoreOf 2 M) : a * b = b * a := by
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : Disjoint (pCore 2 ↥M) (pPrimeCore 2 ↥M) := by
    rw [Subgroup.disjoint_def]
    intro x hx1 hx2
    obtain ⟨i, hi⟩ := (pCore_isPGroup (p := 2) (G := ↥M)) ⟨x, hx1⟩
    have hi' : x ^ (2 ^ i) = 1 := congrArg Subtype.val hi
    have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥M))
    have hd : orderOf (⟨x, hx2⟩ : ↥(pPrimeCore 2 ↥M)) ∣ Nat.card ↥(pPrimeCore 2 ↥M) :=
      orderOf_dvd_natCard _
    have h1 : Odd (orderOf x) := by
      have := Odd.of_dvd_nat hodd hd
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf x ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one hi'
    have h3 : orderOf x = 1 := by
      rcases (Nat.dvd_prime_pow Nat.prime_two).1 h2 with ⟨j, -, hj⟩
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [hj, h0, pow_zero]
      · exfalso
        have : Even (orderOf x) := by
          rw [hj]
          exact (Nat.even_pow.2 ⟨even_two, hpos.ne'⟩)
        exact (Nat.not_even_iff_odd.2 h1) this
    exact orderOf_eq_one_iff.1 h3
  have h := Subgroup.commute_of_normal_of_disjoint (pCore 2 ↥M) (pPrimeCore 2 ↥M) pCore_normal
    pPrimeCore_normal hdisj a' b' ha' hb'
  exact congrArg Subtype.val h

theorem z_mem_Op2_Cen {z : G} (hz2 : orderOf z = 2) : z ∈ Op 2 (Cen z) := by
  have hW : IsPGroup 2 ↥(zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  have hle : zpowers z ≤ Op 2 (Cen z) :=
    CFSG.GH74.GLS.Stage2.Final.Thm6.L20.le_Op_of_normalized 2
      (Subgroup.zpowers_le.2 (mem_Cen_self z)) (fun b hb w hw => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        have hbz : Commute b z := Subgroup.mem_centralizer_singleton_iff.1 hb
        have : b * z ^ m * b⁻¹ = z ^ m := by
          rw [(hbz.zpow_right m).eq]
          group
        rw [this]
        exact Subgroup.zpow_mem_zpowers z m) hW
  exact hle (Subgroup.mem_zpowers z)

omit [Finite G] in
theorem conjugate_inv_conjugate (M : Subgroup G) (g : G) : conjugate (conjugate M g) g⁻¹ = M := by
  ext x
  rw [L193.mem_conjugate_iff', L193.mem_conjugate_iff']
  have e : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
  rw [e]

omit [Finite G] in
theorem conjugate_of_mem {M : Subgroup G} {g : G} (hg : g ∈ M) : conjugate M g = M := by
  ext x
  rw [L193.mem_conjugate_iff']
  constructor
  · intro hx
    have := M.mul_mem (M.mul_mem (M.inv_mem hg) hx) hg
    simpa [mul_assoc] using this
  · intro hx
    exact M.mul_mem (M.mul_mem hg hx) (M.inv_mem hg)

end Small

section Main

theorem prop18_13_of (h171 : Prop17_1) (h178 : Prop17_8) (h1812 : Prop18_12)
    (hB13 : Bender13) : Prop18_13 := by
  intro G _ _ z k S M p h U hUP hUn hUe hUc H hH hcase
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := h.odd
    omega
  obtain ⟨hMC, -⟩ := h171 G z k S M h.base.ctx h.base.fail
  have hMcoat : IsCoatom M := h.base.ctx.mem.1
  have hksimple : IsKProperSimple G := h.base.ctx.ctx.std.kps
  have hz2 : orderOf z = 2 := h.base.ctx.ctx.central.1
  have hzOp : z ∈ Op 2 M := hMC ▸ z_mem_Op2_Cen hz2
  have hzFs : z ∈ Fs M := h.base.ctx.z_mem_Fs
  have hFsM : ∀ q : ℕ, q.Prime → ∀ y ∈ Op p M, y ≠ 1 → y ^ p = 1 → ¬ IsPGroup q ↥(Fs M) := by
    intro q hq y hy hy1 hyp hFq
    have hy' : y ∈ Fs M := Fm_le_Fs M (Bender.Thm1.Op_le_Fm p hp M hy)
    obtain ⟨n, hn⟩ := hFq ⟨z, hzFs⟩
    obtain ⟨m, hm⟩ := hFq ⟨y, hy'⟩
    have hn' : z ^ (q ^ n) = 1 := congrArg Subtype.val hn
    have hm' : y ^ (q ^ m) = 1 := congrArg Subtype.val hm
    have h2 : 2 ∣ q ^ n := hz2 ▸ orderOf_dvd_of_pow_eq_one hn'
    have hq2 : q = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
    have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
    have h3 : p ∣ q ^ m := hyo ▸ orderOf_dvd_of_pow_eq_one hm'
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h3)
    exact h.odd (hpq.trans hq2)
  have key : ∀ V : Subgroup G, V ≤ Op p M → IsElementaryAbelian p ↥V → ¬ IsCyclic ↥V →
      (∀ v ∈ V, 3 ≤ CFSG.pRank p ↥(Op p M ⊓ centralizer ({v} : Set G))) → zpowers z ⊔ V ≤ H →
      (Fs H ≤ M ∧ z ∈ Op 2 H) ∨
        (p = 3 ∧ Nat.card ↥V = 9 ∧ Odd (Nat.card ↥(H ⊓ centralizer (Em H : Set G)))) :=
    fun V hVP hVe hVnc hVr hzV => by
      rcases h1812 G z k S M p h V hVP hVe hVnc (fun v hv _ => hVr v hv) H hH hzV with
        h1 | ⟨h1, h2, -, -, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2, h3⟩
  rcases hcase with ⟨X, hXF, hX1, ⟨r, hr, hXe⟩, hXH⟩ | ⟨g, hHg, V, hVQ, hVe, hVc, hzVH⟩
  ·
    obtain ⟨hzH, V, hVP, hVe, hV3, hVH⟩ := exists_V_a h hMC hUP hUn hUe hUc hXF hr hXe hXH
    have hVE := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p V).mp hVe
    have hp2 : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by norm_num)
    have hVnc := not_isCyclic_of_card hp hVe (hp2.trans hV3)
    rcases key V hVP hVe hVnc (rank_centralizer_of_elem hp hVP hVE hV3)
        (sup_le (Subgroup.zpowers_le.2 hzH) hVH) with ⟨hFs, hz2H⟩ | ⟨-, hV9, -⟩
    ·
      have hLHM : Links H M :=
        ⟨zpowers z, Subgroup.zpowers_le.2 (Bender.Thm1.Op_le_Fm 2 Nat.prime_two H hz2H),
          inf_le_left.trans hFs⟩
      have hLMH : Links M H :=
        ⟨X, hXF.trans (Fof_le_Fm hp M U), inf_le_right.trans hXH⟩
      rcases hB13 G hksimple M H hMcoat hH hLMH hLHM with hMH | ⟨q, hq, hqM, -⟩
      · exact hMH.symm
      · exfalso
        have hVne : V ≠ ⊥ := by
          intro hbot
          rw [hbot, Subgroup.card_bot] at hV3
          have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
          omega
        obtain ⟨⟨y, hyV⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hVne
        have hy1' : y ≠ 1 := fun h' => hy1 (Subtype.ext h')
        exact hFsM q hq y (hVP hyV) hy1' ((isElemAbelian_iff.1 hVE).2 y hyV) hqM
    · exfalso
      have : p ^ 3 ≤ 9 := hV9 ▸ hV3
      have h27 : 3 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
      omega
  ·
    have hVP : V ≤ Op p M := hVQ.trans inf_le_left
    have hVnc := not_isCyclic_of_card hp hVe hVc
    have hVr := exists_V_b h hUP hUn hUe hUc hVQ hVe
    rcases key V hVP hVe hVnc hVr hzVH with ⟨hFs, hz2H⟩ | ⟨-, -, hOdd⟩
    ·
      have hHM : conjugate H g⁻¹ = M := hHg ▸ conjugate_inv_conjugate M g
      have ht : g * z * g⁻¹ ∈ Op 2 M := by
        have h1 : g * z * g⁻¹ ∈ conjugate (Op 2 H) g⁻¹ := by
          rw [L193.mem_conjugate_iff']
          have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
          rw [e]
          exact hz2H
        have h2 := L193.op_conjugate_le 2 H g⁻¹ h1
        rwa [hHM] at h2
      have hcent : g * z * g⁻¹ ∈ centralizer (pPrimeCoreOf 2 M : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (Op2_commute_pPrimeCoreOf M ht hb).symm
      have hconj : IsConj z (g * z * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
      have htz := h178 G z k S M h.base _ hconj hcent
      have hgM : g ∈ M := by
        rw [hMC]
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have : g * z * g⁻¹ * g = z * g := by rw [htz]
        calc g * z = g * z * g⁻¹ * g := by group
          _ = z * g := this
      rw [hHg]
      exact conjugate_of_mem hgM
    ·
      exfalso
      have hz'H : g⁻¹ * z * g ∈ Op 2 H := by
        have h1 : g⁻¹ * z * g ∈ conjugate (Op 2 M) g := by
          rw [L193.mem_conjugate_iff']
          have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
          rw [e]
          exact hzOp
        have h2 := L193.op_conjugate_le 2 M g h1
        rwa [← hHg] at h2
      have hz'ord : orderOf (g⁻¹ * z * g) = 2 := by
        rw [← hz2]
        have : g⁻¹ * z * g = (MulAut.conj g⁻¹).toMonoidHom z := by
          simp
        rw [this]
        exact orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective z
      have hz'F : g⁻¹ * z * g ∈ H ⊓ centralizer (Em H : Set G) := by
        refine Subgroup.mem_inf.2 ⟨Bender.Thm1.Op_le 2 H hz'H, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (Fm_commute_Em H (Bender.Thm1.Op_le_Fm 2 Nat.prime_two H hz'H) hb).symm
      have hdvd := Subgroup.orderOf_dvd_natCard (H ⊓ centralizer (Em H : Set G)) hz'F
      rw [hz'ord] at hdvd
      exact (Nat.not_even_iff_odd.2 hOdd) (even_iff_two_dvd.2 hdvd)

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S1
