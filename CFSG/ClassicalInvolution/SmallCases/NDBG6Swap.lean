module

public import CFSG.ClassicalInvolution.SmallCases.NDBG6Comp
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinSide
public import CFSG.ClassicalInvolution.Asc77.AscIHTwin
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RG2Pair
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.NDB.NDBG

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77.T3Typed
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

section Norm

variable {Ω : Set (Subgroup G)} {z : G}

theorem conj_range_eq (C : XCtx p f Ω z) {b : Fin C.D.card} (hG2 : C.D.tag b = .G2)
    (hother : ∀ i, i ≠ b → BSC.zbar z ∈ (C.psi i).range) (c : OddQuot z) :
    conjSub c (C.psi b).range = (C.psi b).range := by
  obtain ⟨hinj, hZ⟩ := injective_and_center_of_g2 C hG2
  obtain ⟨X, hXdef⟩ : ∃ X : Subgroup (OddQuot z), X = conjSub c (C.psi b).range := ⟨_, rfl⟩
  have hX : IsComponentOf X ⊤ := by
    rw [hXdef]
    exact (LocalComponents.equiv_iff (MulAut.conj c) _).mpr (C.isComponentOf_range b)
  rw [← hXdef]
  by_contra hne
  have hXi : ∀ i, X ≠ (C.psi i).range := by
    intro i hi
    by_cases hib : i = b
    · subst hib
      exact hne hi
    · have hz : BSC.zbar z ∈ X := hi ▸ hother i hib
      rw [hXdef, mem_conjSub_iff] at hz
      have e : c⁻¹ * BSC.zbar z * c = BSC.zbar z := by
        rw [mul_assoc, NDB.Cover.zbar_comm c, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e] at hz
      exact zbar_not_mem_range C hG2 hz
  have hcomm : ∀ i, (C.psi i).range ≤ Subgroup.centralizer (X : Set (OddQuot z)) := by
    intro i y hy
    have h := LocalComponents.commute_of_ne _ _ hX (C.isComponentOf_range i) (hXi i)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hm := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact hm
  have hJ := memberJoin_le_of_forall C hcomm
  have hXJ : X ≤ memberJoin (exactFamily Ω z) z := by
    intro x hx
    rw [hXdef, mem_conjSub_iff] at hx
    obtain ⟨k, hk⟩ := hx
    have h1 : c⁻¹ * x * c ∈ memberJoin (exactFamily Ω z) z := hk ▸ C.psi_mem_memberJoin b k
    have h2 := (memberJoin_normal_of_normalizes C.hs.normalizes).conj_mem _ h1 c
    simpa [mul_assoc] using h2
  obtain ⟨mb⟩ := BSC.exists_compMem C b
  obtain ⟨t, htdef⟩ : ∃ t : OddQuot z,
      t = oddQuotMk z ⟨mb.n, C.involution_mem_centralizer mb.hN mb.hn⟩ := ⟨_, rfl⟩
  have ht1 : t ≠ 1 := htdef ▸ (C.isUniqueInvolution_modOdd mb.hN mb.hn).ne_one
  have htR : t ∈ (C.psi b).range := by
    have h := oddQuotMk_mem_modOdd (C.involution_mem_exactCore mb.hN mb.hn)
      (C.involution_mem_centralizer mb.hN mb.hn)
    rw [mb.himg] at h
    rw [htdef]
    exact Subgroup.map_le_range _ _ h
  refine ht1 (eq_one_of_mem_range_of_comm hinj hZ htR fun s hs => ?_)
  have hcs : c * s * c⁻¹ ∈ X := by
    rw [hXdef, mem_conjSub_iff]
    simpa [mul_assoc] using hs
  have hct : c * t * c⁻¹ ∈ X := by
    rw [hXdef, mem_conjSub_iff]
    simpa [mul_assoc] using htR
  have h := Subgroup.mem_centralizer_iff.mp (hJ (hXJ hcs)) _ hct
  have h' : c * (t * s) * c⁻¹ = c * (s * t) * c⁻¹ := by
    calc c * (t * s) * c⁻¹ = (c * t * c⁻¹) * (c * s * c⁻¹) := by group
      _ = (c * s * c⁻¹) * (c * t * c⁻¹) := h
      _ = c * (s * t) * c⁻¹ := by group
  simpa using h'

end Norm

section Aut

theorem mem_centralizer_of_conj_eq {X : Type} [Group X] {h a : X} (e : h * a * h⁻¹ = a) :
    h ∈ Subgroup.centralizer ({a} : Set X) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc h * a = h * a * h⁻¹ * h := by group
    _ = a * h := by rw [e]

theorem exists_mulAut_of_conj_range {M X : Type} [Group M] [Group X] {ψ : M →* X}
    (hinj : Function.Injective ψ) {c : X} (hc : conjSub c ψ.range = ψ.range) :
    ∃ α : MulAut M, ∀ R : Subgroup M, (R.map α.toMonoidHom).map ψ = conjSub c (R.map ψ) := by
  have hmem : ∀ x ∈ ψ.range, c * x * c⁻¹ ∈ ψ.range := fun x hx => by
    rw [← hc]
    exact ⟨x, hx, rfl⟩
  have hmem' : ∀ x ∈ ψ.range, c⁻¹ * x * c ∈ ψ.range := fun x hx => by
    rw [← hc, mem_conjSub_iff] at hx
    exact hx
  let β : ψ.range ≃* ψ.range :=
    { toFun := fun x => ⟨c * x * c⁻¹, hmem x x.2⟩
      invFun := fun x => ⟨c⁻¹ * x * c, hmem' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  let ε : M ≃* ψ.range := MonoidHom.ofInjective hinj
  refine ⟨(ε.trans β).trans ε.symm, fun R => ?_⟩
  have key : ∀ k : M, ψ (((ε.trans β).trans ε.symm) k) = c * ψ k * c⁻¹ := fun k => by
    have h := congrArg Subtype.val (ε.apply_symm_apply (β (ε k)))
    rw [MonoidHom.ofInjective_apply] at h
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h]
    rfl
  rw [Subgroup.map_map]
  unfold conjSub
  rw [Subgroup.map_map]
  congr 1
  ext k
  exact key k

end Aut

section Swap

variable {K : Subgroup G} {z : G}

local notation "𝒞" => Generic.CoreAssembly.conjClass

theorem exists_swap_centralizing (C : XCtx p f (𝒞 K) z) {b e : Fin C.D.card}
    (hG2 : C.D.tag b = .G2) (hother : ∀ i, i ≠ b → BSC.zbar z ∈ (C.psi i).range)
    (mb : BSC.CompMem C b) {T : Subgroup G} (hTcl : IsClassicalMember p f T z)
    (hTmod : modOdd z T = (C.psi e).range) {x : G} (hxC : x ∈ Subgroup.centralizer ({z} : Set G))
    (hx : conjSub x C.K = T) :
    ∃ y : G, y ∈ Subgroup.centralizer ({z} : Set G) ∧ y * mb.n * y⁻¹ = mb.n ∧
      conjSub y C.K = T := by
  obtain ⟨hinj, -⟩ := injective_and_center_of_g2 C hG2
  have hnorm := conj_range_eq C hG2 hother
  obtain ⟨xb, hxb⟩ : ∃ xb : OddQuot z, xb = oddQuotMk z ⟨x, hxC⟩ := ⟨_, rfl⟩
  have hnC := C.involution_mem_centralizer mb.hN mb.hn
  obtain ⟨nb, hnbdef⟩ : ∃ nb : OddQuot z, nb = oddQuotMk z ⟨mb.n, hnC⟩ := ⟨_, rfl⟩
  have hn2 : mb.n * mb.n = 1 := mb.hn.isCentralInvolution.sq
  have hnb2 : nb * nb = 1 := by
    rw [hnbdef, ← map_mul]
    have e : (⟨mb.n, hnC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨mb.n, hnC⟩ = 1 :=
      Subtype.ext hn2
    rw [e, map_one]
  have hnb1 : nb ≠ 1 := by
    rw [hnbdef]
    exact (C.isUniqueInvolution_modOdd mb.hN mb.hn).ne_one
  have hnbR : nb ∈ (C.psi b).range := by
    rw [hnbdef]
    exact Subgroup.map_le_range _ _ (BSC.BSD.nb_mem mb)
  obtain ⟨k₀, hk₀⟩ := hnbR
  have huR : xb * nb * xb⁻¹ ∈ (C.psi b).range := by
    rw [← hnorm xb, mem_conjSub_iff]
    have e : xb⁻¹ * (xb * nb * xb⁻¹) * xb = nb := by group
    rw [e]
    exact ⟨k₀, hk₀⟩
  obtain ⟨kᵤ, hkᵤ⟩ := huR
  have hk₀2 : k₀ * k₀ = 1 := hinj (by rw [map_mul, hk₀, hnb2, map_one])
  have hk₀1 : k₀ ≠ 1 := fun h => hnb1 (by rw [← hk₀, h, map_one])
  have hkᵤ2 : kᵤ * kᵤ = 1 := hinj (by
    rw [map_mul, hkᵤ, map_one]
    calc xb * nb * xb⁻¹ * (xb * nb * xb⁻¹) = xb * (nb * nb) * xb⁻¹ := by group
      _ = 1 := by rw [hnb2]; group)
  have hkᵤ1 : kᵤ ≠ 1 := fun h => hnb1 (by
    have h1 : xb * nb * xb⁻¹ = 1 := by rw [← hkᵤ, h, map_one]
    calc nb = xb⁻¹ * (xb * nb * xb⁻¹) * xb := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨h, hh⟩ := g2_model_involutions_conj hG2 C.hp (C.D.admissible b) hkᵤ2 hk₀2 hkᵤ1 hk₀1
  obtain ⟨w, hwY, hw⟩ := C.exists_lift_psi b h
  have hwC : w ∈ Subgroup.centralizer ({z} : Set G) := exactLayer_le_centralizer _ z hwY
  have hnY : mb.n ∈ exactLayer (𝒞 K) z :=
    exactCore_le_exactLayer mb.hN (C.involution_mem_exactCore mb.hN mb.hn)
  have hxnY : x * mb.n * x⁻¹ ∈ exactLayer (𝒞 K) z := by
    rw [← conjSub_exactLayer C.hΩ.conjInvariant hxC, mem_conjSub_iff]
    have e : x⁻¹ * (x * mb.n * x⁻¹) * x = mb.n := by group
    rw [e]
    exact hnY
  have hn'Y : w * (x * mb.n * x⁻¹) * w⁻¹ ∈ exactLayer (𝒞 K) z :=
    mul_mem (mul_mem hwY hxnY) (inv_mem hwY)
  have hn'2 : w * (x * mb.n * x⁻¹) * w⁻¹ * (w * (x * mb.n * x⁻¹) * w⁻¹) = 1 := by
    calc w * (x * mb.n * x⁻¹) * w⁻¹ * (w * (x * mb.n * x⁻¹) * w⁻¹) =
        w * (x * (mb.n * mb.n) * x⁻¹) * w⁻¹ := by group
      _ = 1 := by rw [hn2]; group
  have himg : oddQuotMk z ⟨w * (x * mb.n * x⁻¹) * w⁻¹, exactLayer_le_centralizer _ z hn'Y⟩ =
      oddQuotMk z ⟨mb.n, exactLayer_le_centralizer _ z hnY⟩ := by
    have e : (⟨w * (x * mb.n * x⁻¹) * w⁻¹, exactLayer_le_centralizer _ z hn'Y⟩ :
        ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨w, hwC⟩ * (⟨x, hxC⟩ * ⟨mb.n, hnC⟩ * ⟨x, hxC⟩⁻¹) * ⟨w, hwC⟩⁻¹ := rfl
    rw [e]
    simp only [map_mul, map_inv]
    rw [← hxb, ← hnbdef, hw, ← hkᵤ, ← map_inv, ← map_mul, ← map_mul, hh, hk₀]
  obtain ⟨o, ho, hoe⟩ := C.exists_conj_of_oddQuotMk_eq hn'Y hnY hn'2 hn2 himg
  have hoY : o ∈ exactLayer (𝒞 K) z := oddCoreIn_le _ ho
  have hoC : o ∈ Subgroup.centralizer ({z} : Set G) := exactLayer_le_centralizer _ z hoY
  refine ⟨o⁻¹ * w * x, mul_mem (mul_mem (inv_mem hoC) hwC) hxC, ?_, ?_⟩
  · calc o⁻¹ * w * x * mb.n * (o⁻¹ * w * x)⁻¹ = o⁻¹ * (w * (x * mb.n * x⁻¹) * w⁻¹) * o := by
          group
      _ = mb.n := by rw [hoe]; group
  ·
    have hzT : ∀ c ∈ Subgroup.centralizer ({z} : Set G), modOdd z (conjSub c T) =
        modOdd z T → conjSub c T = T := by
      intro c hc hmod
      have hcl : IsClassicalMember p f (conjSub c T) z := by
        have h1 := hTcl.conj c
        rwa [conj_eq_of_mem_centralizer_singleton hc] at h1
      exact Cover.eq_of_modOdd_eq hcl hTcl hmod
    have hwT : conjSub w T = T := by
      refine hzT w hwC ?_
      rw [modOdd_conjSub_of_mem_centralizer hwC, hTmod]
      have hwJ : oddQuotMk z ⟨w, hwC⟩ ∈ memberJoin (exactFamily (𝒞 K) z) z := by
        rw [← range_layerToOddQuot_eq]
        exact ⟨⟨w, hwY⟩, rfl⟩
      have hle : conjSub (oddQuotMk z ⟨w, hwC⟩) (C.psi e).range ≤ (C.psi e).range := by
        intro u hu
        rw [mem_conjSub_iff] at hu
        have h1 := C.conj_psi_range e hwJ _ hu
        simpa [mul_assoc] using h1
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
    have hoT : conjSub o⁻¹ T = T := by
      refine hzT o⁻¹ (inv_mem hoC) ?_
      have ho1 : oddQuotMk z ⟨o⁻¹, inv_mem hoC⟩ = 1 :=
        oddQuotMk_eq_one_of_mem_oddCoreIn
          (inv_mem (Cover.oddCoreIn_exactLayer_le C.hΩ.conjInvariant z ho)) (inv_mem hoC)
      rw [modOdd_conjSub_of_mem_centralizer (inv_mem hoC), ho1, conjSub_one]
    rw [conjSub_mul, conjSub_mul, hx, hwT, hoT]

theorem false_of_g2_twin_of_ne_three (hp3 : p ≠ 3) (C : XCtx p f (𝒞 K) z)
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) {b : Fin C.D.card}
    (hG2 : C.D.tag b = .G2) (hcard : C.D.card = 3) : False := by
  have hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := fun h => by
    rw [hG2] at h
    exact absurd h.1 (by decide)
  obtain ⟨hinj, -⟩ := injective_and_center_of_g2 C hG2
  have hf : 0 < f := BSC.BSD.pos_exp_of_five_le C.hq
  have hA1 : ∀ i, i ≠ b → (C.D.tag i = .PSL ∧ C.D.rank i = 2) ∧
      ∀ m : BSC.CompMem C i, m.nbar = BSC.zbar z := fun i hi => BSC.nbar_eq_of_A1 C hno hb hi
  have hother : ∀ i, i ≠ b → BSC.zbar z ∈ (C.psi i).range := by
    intro i hi
    obtain ⟨m⟩ := BSC.exists_compMem C i
    rw [← (hA1 i hi).2 m]
    exact Subgroup.map_le_range _ _ m.nbar_mem
  have hnorm := conj_range_eq C hG2 hother
  obtain ⟨j₀, hj₀, hK₀⟩ := C.exists_A1_of_K
  have hj₀b : j₀ ≠ b := fun h => hb (h ▸ hj₀)
  obtain ⟨e, hej, heb⟩ := Fin.exists_ne_and_ne_of_two_lt j₀ b (by omega : 2 < C.D.card)
  obtain ⟨me⟩ := BSC.exists_compMem C e
  have hme := (hA1 e heb).2 me
  obtain ⟨hTcl, hTmod⟩ := BSC.classical_of_nbar_eq C (hA1 e heb).1 me hme
  have hTK : me.N ≠ C.K := BSC.twin_ne_K C hj₀ hK₀ hej (hA1 e heb).1 me hme
  obtain ⟨mb⟩ := BSC.exists_compMem C b
  obtain ⟨g, -, hgn⟩ := BSC.BSD.exists_conj_of_compMem C mb
  have hKmod : modOdd z C.K = (C.psi j₀).range := by rw [← C.exactCore_K]; exact hK₀
  obtain ⟨hLtq, hLcl, RL, hRL, hLimg, -⟩ := BSC.BSD.exists_fund_conj_twin hno hb mb hgn C.hK
    C.K_cl fun y hy => BSC.BSD.nb_comm_of_range hj₀b mb (hKmod ▸ hy)
  obtain ⟨hStq, hScl, RS, hRS, hSimg, -⟩ := BSC.BSD.exists_fund_conj_twin hno hb mb hgn me.hN.1
    hTcl fun y hy => BSC.BSD.nb_comm_of_range heb mb (hTmod ▸ hy)
  obtain ⟨x, hx, hxn⟩ := BSC.BSD.exists_conj_of_compMem C me
  have hxz : x * z * x⁻¹ = z := by
    rw [← hxn]
    exact (me.hn.eq_of_isCentralInvolution C.hp hf hTcl.isCentralInvolution).symm
  have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := mem_centralizer_of_conj_eq hxz
  obtain ⟨y', hy'C, hy'n, hy'K⟩ := exists_swap_centralizing C hG2 hother mb hTcl hTmod hxC hx
  obtain ⟨y, hydef⟩ : ∃ y : G, y = g⁻¹ * y' * g := ⟨_, rfl⟩
  have hyz : y * z * y⁻¹ = z := by
    have e : g * z * g⁻¹ = mb.n := hgn.symm
    calc y * z * y⁻¹ = g⁻¹ * (y' * (g * z * g⁻¹) * y'⁻¹) * g := by rw [hydef]; group
      _ = z := by rw [e, hy'n, ← e]; group
  have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := mem_centralizer_of_conj_eq hyz
  have hyLS : conjSub y (conjSub g⁻¹ C.K) = conjSub g⁻¹ me.N := by
    rw [← conjSub_mul, hydef, show g⁻¹ * y' * g * g⁻¹ = g⁻¹ * y' by group, conjSub_mul, hy'K]
  obtain ⟨yb, hyb⟩ : ∃ yb : OddQuot z, yb = oddQuotMk z ⟨y, hyC⟩ := ⟨_, rfl⟩
  have himgS : RS.map (C.psi b) = conjSub yb (RL.map (C.psi b)) := by
    rw [hyb, ← hSimg, ← hLimg, ← hyLS, ← modOdd_conjSub_of_mem_centralizer hyC]
    congr 1
    have h := exactCore_conjSub y z (conjSub g⁻¹ C.K)
    rwa [hyz] at h
  obtain ⟨α, hα⟩ := exists_mulAut_of_conj_range hinj (hnorm yb)
  have hαR : RL.map α.toMonoidHom = RS := by
    apply Subgroup.map_injective hinj
    rw [himgS, hα]
  obtain ⟨k', hk'⟩ := exists_conjSub_of_mulAut_tag C.hp hp3 hG2 (C.D.admissible b) α hRL
  have hUL := C.isUniqueInvolution_modOdd hLtq hLcl
  rw [hLimg] at hUL
  obtain ⟨cL, hcL, hUcL⟩ := isUniqueInvolution_of_map hinj hUL
  have hUS := C.isUniqueInvolution_modOdd hStq hScl
  rw [hSimg] at hUS
  obtain ⟨cS, hcS, hUcS⟩ := isUniqueInvolution_of_map hinj hUS
  have hcc : cS = cL := hinj (hcS.trans hcL.symm)
  rw [← hαR, hk', hcc] at hUcS
  have hRR := noTwinsFund_of_g2_tag C.hp hG2 (C.D.admissible b) RL hRL cL hUcL k' hUcS
  have hRSL : RS = RL := by rw [← hαR, hk', hRR]
  have hLS : conjSub g⁻¹ me.N = conjSub g⁻¹ C.K :=
    BSC.BSD.eq_of_fund_eq C.hz2 hStq hLtq hScl hLcl (by rw [hSimg, hLimg, hRSL])
  exact hTK (BSC.BSD.conjSub_inj g⁻¹ hLS)

end Swap

end CFSG.ClassicalInvolution.NDB.NDBG
