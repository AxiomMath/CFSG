module

public import CFSG.GH74.Generic.BProg.B2.T4OutComm
public import CFSG.GH74.Generic.BProg.B2.PumpupTableExc
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Aut
import CFSG.GH74.Generic.S3.V1InnerLib
import CFSG.GH74.GLS.IVK.Proofs2.GHInvStar
public import CFSG.GH74.KGroups.L3EpsSylow
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.GH74.Generic.BProg.B2.T4

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def OutG2Comm : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H : Subgroup N), H.Normal →
    (∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) → PuG2 ↥H → commutator N ≤ H

namespace T4ElimOut

section G2


theorem commutator_inner_of_g2 {J : Type} [Group J] {f : ℕ} (hf : 1 ≤ f)
    (hL : LieModel J .G2 0 3 f) (α β : MulAut J) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : J →* MulAut J).range := by
  have hY' : ChevalleyExceptionalModel J .G2 3 f := by
    rcases hL with ⟨hc, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd hc (by decide)
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨ψ⟩⟩ := hY'
  have hcenter : Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 K)
      = ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let ψ' : J ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 K) :=
    ψ.trans ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot)
  obtain ⟨-, H', _, hcyc, Θ, hΘ⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.g2_aut_facts Nat.prime_three (by norm_num) hf K hKcard
  refine T4OutCore.commutator_inner_of_mulEquiv ψ' (fun a b => ?_) α β
  rw [← hΘ, MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  have hc : ∀ x y : H', x * y = y * x := fun x y => by
    have : IsMulCommutative H' := IsCyclic.isMulCommutative
    exact (IsMulCommutative.is_comm (M := H')).comm x y
  calc Θ a * Θ b * (Θ a)⁻¹ * (Θ b)⁻¹ = (Θ b * Θ a) * (Θ a)⁻¹ * (Θ b)⁻¹ := by rw [hc (Θ a) (Θ b)]
    _ = 1 := by group

end G2


section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K] [Finite K]

theorem linear_involution_inner_odd {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    {a : MulAut (projectiveSL n K)} (ha : a ∈ commutator (MulAut (projectiveSL n K)))
    (ha2 : a ^ 2 = 1) :
    a ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  have hD : a ∈ linearAutGroup n K := T4OutCore.mem_of_commutator_mem
    (fun α β => CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup
      hn α β) ha
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hD
  obtain ⟨-, hcard⟩ := CFSG.LocalAnalysis.ComponentInitial.OuterDerived.linear_diagonal_outer
    (K := K) (n := n) (by omega)
  set φ := (QuotientGroup.mk' (inner (projectiveSL n K))).comp (conjAut n K) with hφ
  have hmem : (QuotientGroup.mk a : MulAut (projectiveSL n K) ⧸ inner (projectiveSL n K)) ∈
      φ.range := ⟨A, by rw [hφ, MonoidHom.comp_apply, hA]; rfl⟩
  set x : ↥φ.range := ⟨_, hmem⟩ with hxdef
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    change (QuotientGroup.mk a : MulAut (projectiveSL n K) ⧸ inner (projectiveSL n K)) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, ha2, QuotientGroup.mk_one]
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h2 : orderOf x ∣ Nat.card ↥φ.range := orderOf_dvd_natCard x
  have h5 : orderOf x ∣ n := h2.trans (hcard.trans (Nat.gcd_dvd_left n _))
  have h3 : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd h1 h5
    have hc : Nat.gcd 2 n = 1 := (Nat.coprime_two_left.2 hodd)
    rwa [hc] at this
  have hx1 : x = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have h4 : (QuotientGroup.mk a : MulAut (projectiveSL n K) ⧸ inner (projectiveSL n K)) = 1 :=
    congrArg Subtype.val hx1
  exact (QuotientGroup.eq_one_iff (N := inner (projectiveSL n K)) a).mp h4

end Linear

theorem inner_of_involution_psl_odd {J : Type} [Group J] {n p f : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hL : LieModel J .PSL n p f) {a : MulAut J} (ha : a ∈ commutator (MulAut J))
    (ha2 : a ^ 2 = 1) : a ∈ (MulAut.conj : J →* MulAut J).range := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := T4OutCore.linear_model hL
  exact T4OutCore.inner_of_involution_of_mulEquiv e
    (fun b hb hb2 => linear_involution_inner_odd hn hodd hb hb2) ha ha2

section InvLite

open CFSG.GH74.KGroups.L3Eps
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped commutatorElement

structure InvLite (K : Type*) [Group K] (t : K) (S : Subgroup K) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥S
  le_centralizer : S ≤ Subgroup.centralizer ({t} : Set K)
  conj_mem : ∀ x ∈ Subgroup.centralizer ({t} : Set K), ∀ s ∈ S, x * s * x⁻¹ ∈ S
  commutator_mem : ∀ x ∈ Subgroup.centralizer ({t} : Set K),
    ∀ y ∈ Subgroup.centralizer ({t} : Set K), ⁅x, y⁆ ∈ S
  involution : ∀ s ∈ S, s * s = 1 → s = 1 ∨ s = t

theorem mem_map_symm {K X : Type*} [Group K] [Group X] (e : K ≃* X) (S : Subgroup X) (x : K) :
    x ∈ S.map (e.symm : X →* K) ↔ e x ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨e x, h, by simp⟩

theorem invLite_of_equiv {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {K : Type*} [Group K] (e : K ≃* projectiveSL 3 F) {t : K} (ht : e t = tInv) :
    InvLite K t (blockSub.map (e.symm : projectiveSL 3 F →* K)) := by
  have hF2 : ringChar F ≠ 2 := fun h => h2 (by
    have : CharP F 2 := h ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)
  have hcen : ∀ x : K, x ∈ Subgroup.centralizer ({t} : Set K) ↔
      e x ∈ Subgroup.centralizer ({tInv} : Set (projectiveSL 3 F)) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← ht,
      ← map_mul, ← map_mul]
    exact ⟨fun h => by rw [h], fun h => e.injective h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap e.symm blockSub)
      (isQuasisimple_blockSub h4)
  · intro s hs
    rw [mem_map_symm] at hs
    rw [hcen]
    exact blockSub_le_centralizer hs
  · intro x hx s hs
    rw [hcen] at hx
    rw [mem_map_symm] at hs ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_blockSub h2 hx hs
  · intro x hx y hy
    rw [hcen] at hx hy
    rw [mem_map_symm, map_commutatorElement]
    exact commutator_mem_blockSub h2 hx hy
  · intro s hs hs2
    rw [mem_map_symm] at hs
    have h1 : e s * e s = 1 := by rw [← map_mul, hs2, map_one]
    rcases blockSub_involution hF2 hs h1 with h | h
    · left
      exact e.injective (h.trans (map_one e).symm)
    · right
      exact e.injective (h.trans ht.symm)

theorem exists_invLite_lin {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    {K : Type} [Group K] [Finite K] (hX : StatedClassicalModel K .PSL 3 p f) :
    ∀ x : K, x * x = 1 → x ≠ 1 → ∃ S : Subgroup K, InvLite K x S := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd : Odd (Nat.card F) := by rw [hF]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.Generic.S3.two_ne_zero_of_odd_card hodd
  have h5' : 5 ≤ Nat.card F := by rw [hF]; exact h5
  intro x hx2 hx1
  have hex2 : e x * e x = 1 := by rw [← map_mul, hx2, map_one]
  have hex1 : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hg⟩ := CFSG.GH74.Generic.S3.singleInv_projectiveSL h2 (e x) tInv hex2 hex1
    tInv_mul_self (tInv_ne_one h2)
  let e' : K ≃* projectiveSL 3 F := e.trans (MulAut.conj g)
  have he' : e' x = tInv := by
    show MulAut.conj g (e x) = tInv
    rw [MulAut.conj_apply]
    exact hg
  exact ⟨_, invLite_of_equiv h2 (by omega) e' he'⟩

theorem false_of_invLite {N : Type} [Group N] [Finite N] {H L : Subgroup N} {t : N}
    (hLC : IsCompIn (H ⊓ Subgroup.centralizer ({t} : Set N)) L) (htH : t ∈ H)
    (h2 : PumpupTableTwoInv.HasTwoInvolutions L) {S : Subgroup ↥H}
    (hInv : InvLite ↥H (⟨t, htH⟩ : ↥H) S) : False := by
  have hB := PumpupTableL3.isCompIn_centralizer_subgroupOf htH hLC
  have hLS : L.subgroupOf H = S :=
    CFSG.GH74.GLS.IVK.GHInv.eq_of_isCompIn_of_normal_quasisimple hInv.quasisimple
      hInv.le_centralizer hInv.conj_mem hInv.commutator_mem hB
  have hLH : L ≤ H := hLC.1.trans inf_le_left
  obtain ⟨a, haL, b, hbL, ha2, hb2, ha1, hb1, hab⟩ := h2
  have hmem : ∀ c ∈ L, c * c = 1 → c ≠ 1 → c = t := by
    intro c hc hc2 hc1
    have hcS : (⟨c, hLH hc⟩ : ↥H) ∈ S := by
      rw [← hLS]
      exact hc
    rcases hInv.involution _ hcS (Subtype.ext hc2) with h | h
    · exact absurd (congrArg Subtype.val h) hc1
    · exact congrArg Subtype.val h
  exact hab ((hmem a haL ha2 ha1).trans (hmem b hbL hb2 hb1).symm)

end InvLite

section L3Shape


theorem false_of_inner_l3 {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N} {L : Subgroup N}
    (hs : ShapeInCent H t L) (htH : t ∈ H) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hH : LieModel ↥H .PSL 3 p f) : False := by
  have ht2 : t * t = 1 := by
    have := hs.inv
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq this)
  have ht1 : t ≠ 1 := fun h => by
    have := hs.inv
    rw [h, orderOf_one] at this
    omega
  have hst := PumpupTableBasic.stated_of_lieModel (Or.inl rfl) hH
  obtain ⟨S, hInv⟩ := exists_invLite_lin hp hp2 h5 hst (⟨t, htH⟩ : ↥H)
    (Subtype.ext ht2) (fun h => ht1 (congrArg Subtype.val h))
  exact false_of_invLite hs.comp htH (PumpupTableTwoInv.hasTwoInvolutions_of_shapeInCent hs) hInv

end L3Shape

end T4ElimOut

section G2Main


theorem outG2Comm_proved : OutG2Comm := by
  intro N _ _ H hHn hfaith hL t ht
  obtain ⟨f, hf, hm⟩ := hL
  have := hHn
  exact T4OutCore.mem_of_conjNormal_mem_inner hfaith
    (T4OutCore.mem_of_commutator_mem
      (fun α β => T4ElimOut.commutator_inner_of_g2 (by omega) hm α β)
      (T4OutComm.conjNormal_mem_commutator ht))

end G2Main

section G2Shape


theorem false_of_shape_puG2 (hO : OutG2Comm) {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (hL : PuG2 ↥H) (ht : t ∈ commutator N) : False := by
  have htH : t ∈ H := hO N H hs.normal hs.faithful hL ht
  obtain ⟨f, hf, hm⟩ := hL
  exact PumpupTableExc.pumpupIn_g2 3 f Nat.prime_three (by norm_num) (by omega) N H t L hs htH hm

end G2Shape

section L3Row


theorem false_of_shape_puL3sq {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (hL : PuL3sq ↥H) (ht : t ∈ commutator N) : False := by
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hL
  have hHn := hs.normal
  have ht2 : (MulAut.conjNormal t : MulAut ↥H) ^ 2 = 1 := by
    have h : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [hs.inv] at this
    rw [← map_pow, h, map_one]
  have hc := T4OutComm.conjNormal_mem_commutator (H := H) ht
  have htH : t ∈ H := T4OutCore.mem_of_conjNormal_mem_inner hs.faithful
    (T4ElimOut.inner_of_involution_psl_odd (by norm_num) ⟨1, rfl⟩ hm hc ht2)
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h5 : 5 ≤ p ^ (2 * f) := by
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right hp.pos (by omega)
  exact T4ElimOut.false_of_inner_l3 hs htH hp hp2 h5 hm

end L3Row

end CFSG.GH74.Generic.BProg.B2.T4
