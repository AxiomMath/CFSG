module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QAsm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DegPerm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DegLift

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section DblRoot

variable {X : Type} [Group X] [Finite X] {n : ℕ} {A : Subgroup X}

omit [Finite X] in
theorem ahatZbar_mem_center (M : AhatModel X n A) {z : X} (hzA : z ∈ A)
    (hAz : A ≤ centralizer ({z} : Set X)) :
    M.e (QuotientGroup.mk (⟨z, hzA⟩ : ↥A)) ∈ center M.K := by
  rw [Subgroup.mem_center_iff]
  intro k
  obtain ⟨b, rfl⟩ := M.surj_mk k
  rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 2
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hAz b.2))

theorem ahatZbar_ne_one (M : AhatModel X n A) {z : X} (hzA : z ∈ A) (hz2 : orderOf z = 2) :
    M.e (QuotientGroup.mk (⟨z, hzA⟩ : ↥A)) ≠ 1 := by
  intro h1'
  have h2 : (QuotientGroup.mk (⟨z, hzA⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) = 1 :=
    M.e.injective (by rw [map_one]; exact h1')
  have h3 : z ∈ oddCoreOf A := mem_oddCoreOf_iff.2 ⟨hzA, (QuotientGroup.eq_one_iff _).1 h2⟩
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have h4 := eq_one_of_sq_eq_one_of_mem_odd (odd_card_oddCoreOf A) h3 hzz
  rw [h4, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem pow_odd_of_mul_self_eq_one {G : Type*} [Group G] {g : G} (hg : g * g = 1) {m : ℕ}
    (hm : Odd m) : g ^ m = g := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, hg, one_pow, one_mul]

theorem exists_dbl_root (M : AhatModel X n A) (hn : 8 ≤ n) {z s : X} (hzA : z ∈ A)
    (hz2 : orderOf z = 2) (hAz : A ≤ centralizer ({z} : Set X))
    (hsN : s ∈ normalizer (A : Set X)) (hs2 : s * s = 1) {k : ℕ} {hk : 2 * k ≤ n}
    (hσ : M.permX s = stdInv n k hk) {i l : Fin k} (hil : i ≠ l) :
    ∃ x ∈ A, s * x = x * s ∧ x * x = z ∧ M.permX x = dblPair n k hk i l := by
  have hind : M.C.Induces (M.autOf s hsN) (stdInv n k hk) := by
    have := M.induces_perm hn s hsN
    rwa [← M.permX_of_mem hsN, hσ] at this
  obtain ⟨xb, hxbfix, hxbρ⟩ := hind.exists_dblPair_mem_fixSub i l hil
  obtain ⟨x₀, hx₀A, hsx₀, hx₀e⟩ := M.exists_lift_cent hsN hs2 (AhatData.mem_fixSub.1 hxbfix)
  have hinj := (pairEmb n k hk).injective
  have hab : pairEmb n k hk (i, 0) ≠ pairEmb n k hk (i, 1) := fun e => by
    have := hinj e; simp at this
  have hac : pairEmb n k hk (i, 0) ≠ pairEmb n k hk (l, 0) := fun e => hil (by
    have := hinj e; simp_all)
  have had : pairEmb n k hk (i, 0) ≠ pairEmb n k hk (l, 1) := fun e => hil (by
    have := hinj e; simp_all)
  have hbc : pairEmb n k hk (i, 1) ≠ pairEmb n k hk (l, 0) := fun e => hil (by
    have := hinj e; simp_all)
  have hbd : pairEmb n k hk (i, 1) ≠ pairEmb n k hk (l, 1) := fun e => hil (by
    have := hinj e; simp_all)
  have hcd : pairEmb n k hk (l, 0) ≠ pairEmb n k hk (l, 1) := fun e => by
    have := hinj e; simp at this
  have hxb2 : xb * xb ≠ 1 := M.C.sq_dbl_ne_one hn hab hac had hbc hbd hcd hxbρ
  have hxbc : xb * xb ∈ center M.K := M.C.sq_mem_center (by
    rw [hxbρ]
    exact dbl_mul_self hab hac had hbc hbd hcd)
  have hsq : xb * xb = M.e (QuotientGroup.mk (⟨z, hzA⟩ : ↥A)) :=
    M.C.center_eq_of_ne_one hxbc (ahatZbar_mem_center M hzA hAz) hxb2 (ahatZbar_ne_one M hzA hz2)
  have hx₀2 : M.e (QuotientGroup.mk (⟨x₀ * x₀, mul_mem hx₀A hx₀A⟩ : ↥A)) =
      M.e (QuotientGroup.mk (⟨z, hzA⟩ : ↥A)) := by
    rw [← hsq, ← hx₀e, ← map_mul, ← QuotientGroup.mk_mul]
    rfl
  have hoz : z⁻¹ * (x₀ * x₀) ∈ oddCoreOf A := by
    rw [mem_oddCoreOf_iff]
    refine ⟨mul_mem (inv_mem hzA) (mul_mem hx₀A hx₀A), ?_⟩
    exact QuotientGroup.eq.1 (M.e.injective hx₀2).symm
  set o : X := z⁻¹ * (x₀ * x₀) with ho
  have hxo : x₀ * x₀ = z * o := by rw [ho]; group
  have hzo : z * o = o * z :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hAz (oddCoreOf_le A hoz))).symm
  have hoodd : Odd (orderOf o) := by
    have h1' : orderOf (⟨o, hoz⟩ : oddCoreOf A) ∣ Nat.card (oddCoreOf A) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1'
    exact Odd.of_dvd_nat (odd_card_oddCoreOf A) h1'
  have hz1 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  refine ⟨x₀ ^ orderOf o, pow_mem hx₀A _, ?_, ?_, ?_⟩
  · exact (Commute.pow_right (show Commute s x₀ from hsx₀) _).eq
  · have hzc : Commute z o := hzo
    calc x₀ ^ orderOf o * x₀ ^ orderOf o = (x₀ * x₀) ^ orderOf o :=
          ((Commute.refl x₀).mul_pow _).symm
      _ = (z * o) ^ orderOf o := by rw [hxo]
      _ = z ^ orderOf o * o ^ orderOf o := hzc.mul_pow _
      _ = z := by
          rw [pow_orderOf_eq_one, mul_one]
          exact pow_odd_of_mul_self_eq_one hz1 hoodd
  · have hxA : x₀ ^ orderOf o ∈ A := pow_mem hx₀A _
    rw [M.permX_of_mem_A hn hxA]
    have : M.e (QuotientGroup.mk (⟨x₀ ^ orderOf o, hxA⟩ : ↥A)) = xb ^ orderOf o := by
      rw [← hx₀e, ← map_pow, ← QuotientGroup.mk_pow]
      rfl
    rw [this, map_pow, hxbρ]
    exact pow_odd_of_mul_self_eq_one (dbl_mul_self hab hac had hbc hbd hcd) hoodd

end DblRoot

namespace PairCtx

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z s : X} {A A' : Subgroup X}
  {M : AhatModel X n A} {M' : AhatModel X n A'}

theorem false_of_ge_twelve (h : PairCtx X n z s A A' M M') (hn12 : 12 ≤ n) : False := by
  have hn : 8 ≤ n := h.hn
  have hsN : s ∈ normalizer (A : Set X) := h.hNz h.s_mem_C
  have hk6 := six_le_transCount h.sq_permX_s hn12 h.hfix h.hsgn
  have hk6' := six_le_transCount h.sq_permX_z hn12 h.hfix' h.hsgn'
  have hR : h.RCore := h.twoElts_of_ge_six hk6
  have hP : h.swap.RCore := h.swap.twoElts_of_ge_six hk6'
  obtain ⟨a, haA, u, huz, v, hvO, -, hsdec⟩ := h.exists_decomp hP
  have hsA : s ∈ A := by
    rw [hsdec]
    exact mul_mem (mul_mem haA ((Subgroup.zpowers_le.2 h.hzA) huz)) (oddCoreOf_le A hvO)
  obtain ⟨k, hkk⟩ := involution_support_even h.sq_permX_s
  have htr : transCount (M.permX s) = k := by
    unfold transCount
    rw [hkk]
    omega
  rw [htr] at hk6
  have hfs := fixCount_add_support (M.permX s)
  have hfs3 := h.hfix
  have hk4 : 4 ∣ k := by
    have hρ : M.C.ρ (M.e (QuotientGroup.mk (⟨s, hsA⟩ : ↥A))) = M.permX s :=
      (M.permX_of_mem_A hn hsA).symm
    have hss : M.e (QuotientGroup.mk (⟨s, hsA⟩ : ↥A)) *
        M.e (QuotientGroup.mk (⟨s, hsA⟩ : ↥A)) = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul]
      have : (⟨s, hsA⟩ : ↥A) * ⟨s, hsA⟩ = 1 := Subtype.ext h.sq_s
      rw [this]
      simp
    have := (M.C.sq_eq_one_iff_dvd hn (by rw [hρ]; exact h.sq_permX_s)).1 hss
    rw [hρ, hkk] at this
    omega
  obtain ⟨m, hm⟩ := hk4
  have hm2 : 2 ≤ m := by omega
  have hk2n : 2 * k ≤ n := by omega
  obtain ⟨ν, hν⟩ := exists_conj_stdInv (n := n) (k := k) (h := hk2n) h.sq_permX_s hkk
  let M₁ : AhatModel X n A := M.conjC ν
  have : Finite M₁.K := Finite.of_equiv _ M₁.e.toEquiv
  have hσ₁ : M₁.permX s = stdInv n k hk2n := by
    show (M.conjC ν).permX s = _
    rw [M.conjC_permX hn, hν]
  let i : Fin k := ⟨0, by omega⟩
  let l : Fin k := ⟨1, by omega⟩
  have hil : i ≠ l := fun e => by simpa [i, l] using congrArg Fin.val e
  obtain ⟨x, hxA, hsx, hxx, hxρ⟩ :=
    exists_dbl_root M₁ hn h.hzA h.hz h.hAz hsN h.sq_s hσ₁ hil
  have hxN : x ∈ normalizer (A : Set X) := Subgroup.le_normalizer hxA
  have hx4 : (x * x) * (x * x) = 1 := by rw [hxx]; exact h.sq_z
  let B : Subgroup X := A ⊓ centralizer ({s} : Set X) ⊓ centralizer ({x} : Set X)
  have hBA : B ≤ A := fun b hb => hb.1.1
  have hBs : ∀ b ∈ B, b * s = s * b := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.1 hb.1.2
  have hBx : ∀ b ∈ B, b * x = x * b := fun b hb => Subgroup.mem_centralizer_singleton_iff.1 hb.2
  have hBN : B ≤ normalizer (A : Set X) := hBA.trans Subgroup.le_normalizer
  have hBN' : B ≤ normalizer (A' : Set X) := fun b hb =>
    h.hNs (Subgroup.mem_centralizer_singleton_iff.2 (hBs b hb))
  have hxs' : x ∈ centralizer ({s} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 hsx.symm
  have hxN' : x ∈ normalizer (A' : Set X) := h.hNs hxs'
  have hzN' : z ∈ normalizer (A' : Set X) := h.hNs h.z_mem_C
  let ψ : ↥B →* Perm (Fin n) := (M₁.permHom hn).comp (Subgroup.inclusion hBN)
  let T : ↥B →* Perm (Fin n) := (M'.permHom hn).comp (Subgroup.inclusion hBN')
  have hψ : ∀ b : ↥B, ψ b = M₁.permX (b : X) := fun b => (M₁.permX_of_mem (hBN b.2)).symm
  have hT : ∀ b : ↥B, T b = M'.permX (b : X) := fun b => (M'.permX_of_mem (hBN' b.2)).symm
  have hTt : ∀ b : ↥B, T b * M'.permX z = M'.permX z * T b := fun b => by
    rw [hT, ← M'.permX_mul hn (hBN' b.2) hzN', ← M'.permX_mul hn hzN' (hBN' b.2)]
    congr 1
    exact (Subgroup.mem_centralizer_singleton_iff.1 (h.hAz (hBA b.2)))
  have hTσ : ∀ b : ↥B, T b * M'.permX x = M'.permX x * T b := fun b => by
    rw [hT, ← M'.permX_mul hn (hBN' b.2) hxN', ← M'.permX_mul hn hxN' (hBN' b.2)]
    congr 1
    exact hBx b b.2
  have hσσ : M'.permX x * M'.permX x = M'.permX z := by
    rw [← M'.permX_mul hn hxN' hxN', hxx]
  have hker : Group.IsSolvable T.ker := by
    have hRsolv : Group.IsSolvable ↥h.R := h.isSolvable_R hR
    have hle : T.ker.map B.subtype ≤ h.R := by
      rintro _ ⟨b, hb, rfl⟩
      have hb1 : M'.permX (b : X) = 1 := by
        rw [← hT]
        exact MonoidHom.mem_ker.1 hb
      exact h.mem_R_iff.2 ⟨h.hAz (hBA b.2),
        Subgroup.mem_centralizer_singleton_iff.2 (hBs b b.2),
        (M'.permX_eq_one_iff hn (hBN' b.2)).1 hb1⟩
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((Subgroup.inclusion hle).comp
        (Subgroup.equivMapOfInjective T.ker B.subtype B.subtype_injective).toMonoidHom))
      ((Subgroup.inclusion_injective hle).comp (MulEquiv.injective _))
  obtain ⟨k', htk'⟩ := involution_support_even h.sq_permX_z
  have hfs' := fixCount_add_support (M'.permX z)
  have hfs3' := h.hfix'
  have htr' : transCount (M'.permX z) = k' := by
    unfold transCount
    rw [htk']
    omega
  rw [htr'] at hk6'
  have hk'even : Even k' := even_of_involution_sign h.sq_permX_z htk' h.hsgn'
  obtain ⟨Ξ, _, _, Θ, hΞ, hΘ⟩ := exists_hom_solvable_ker h.sq_permX_z htk' (by omega)
    hk'even hσσ T hTt hTσ hker
  have hΞ' : Fintype.card Ξ = 2 * m := by omega
  have hQ : Q0 n k hk2n i l ≤ ψ.range := by
    rw [Q0_eq_closure, Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    have hxb : M₁.C.ρ (M₁.e (QuotientGroup.mk (⟨x, hxA⟩ : ↥A))) = dblPair n k hk2n i l := by
      rw [← M₁.permX_of_mem_A hn hxA, hxρ]
    have hind : M₁.C.Induces (M₁.autOf s hsN) (stdInv n k hk2n) := by
      have := M₁.induces_perm hn s hsN
      rwa [← M₁.permX_of_mem hsN, hσ₁] at this
    obtain ⟨y, hyfix, hyρ, hyc⟩ := hind.exists_odd_lift_comm hxb hc
    have hys : M₁.autOf s hsN y = y := AhatData.mem_fixSub.1 hyfix
    have hyx : M₁.autOf x hxN y = y := by
      have e : M₁.autOf x hxN = MulAut.conj (M₁.e (QuotientGroup.mk (⟨x, hxA⟩ : ↥A))) :=
        M₁.autOf_of_mem hxA
      rw [e, MulAut.conj_apply, ← hyc]
      group
    obtain ⟨b, hbA, hsb, hxb', hbe⟩ := M₁.exists_lift_cent₂ hsN hxN h.sq_s hx4 hsx hys hyx
    have hbB : b ∈ B := ⟨⟨hbA, Subgroup.mem_centralizer_singleton_iff.2 hsb.symm⟩,
      Subgroup.mem_centralizer_singleton_iff.2 hxb'.symm⟩
    refine ⟨⟨b, hbB⟩, ?_⟩
    rw [hψ, M₁.permX_of_mem_A hn hbA, hbe, hyρ]
  have hk7 : 7 ≤ k := by omega
  have : IsSimpleGroup ↥(Q0 n k hk2n i l) := Q0_isSimpleGroup (h := hk2n) hk7 hil
  have hcard := card_le_factorial_of_solvable_ker (Q0 n k hk2n i l)
    (Q0_not_isSolvable (h := hk2n) hk7 hil) ψ hQ Θ hΘ
  have hc2 := card_Q0 (h := hk2n) hk7 hil
  have hlt := two_mul_factorial_lt m hm2
  rw [hΞ'] at hcard
  have hk' : k - 2 = 4 * m - 2 := by omega
  rw [hk'] at hc2
  omega

end PairCtx

theorem lemma58 (hF : Solomon75Frac53) : Solomon75Lemma58 := by
  intro X _ _ n z Z S h h1 hZ
  by_contra hn
  obtain ⟨s, M, M', hctx⟩ := h.exists_pairCtx hF h1 hZ
  exact hctx.false_of_ge_twelve (by omega)

end CFSG.OddStandard.Solomon75
