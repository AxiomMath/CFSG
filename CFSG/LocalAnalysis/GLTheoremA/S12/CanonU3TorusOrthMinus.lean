module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3OrthMinus
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3TorusOrthBlock
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3TorusCore
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.HardMathSupport.Lang.Triality.SylowInnerExt

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3.OrthMinus

open CFSG.Open Polynomial Module QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)

open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow

theorem not_isSolvable_and_of_projOrth {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hV : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) (hdim : Module.finrank K V = 8)
    {m n : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m) (hn : Odd n) (hn3 : 3 ≤ n) (hmn : m ∣ n)
    {x x₁ x₂ : ProjOrthDerived Q} (hx : orderOf x = 3) (h₁ : x₁ ^ 3 = 1) (h₂ : x₂ ^ 3 = 1)
    (hc₁ : Commute x x₁) (hc₂ : Commute x x₂) (hc₁₂ : Commute x₁ x₂)
    {J : Subgroup (ProjOrthDerived Q)}
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({x} : Set (ProjOrthDerived Q))))
    (hcard : Nat.card (↥J ⧸ Subgroup.center ↥J) = CFSG.Open.ordTwistedA 2 (2 ^ n))
    (hmoves : ∀ k : ℕ, ∃ j ∈ J, j * (x₂ * x₁ ^ k) ≠ (x₂ * x₁ ^ k) * j) :
    ¬ (IsSolvable ↥(J ⊓ Subgroup.centralizer ({x₁} : Set (ProjOrthDerived Q))) ∧
      IsSolvable ↥(J ⊓ Subgroup.centralizer ({x₂} : Set (ProjOrthDerived Q)))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := m)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hpℓ : 3 ≠ ringChar K := by rw [hring]; norm_num
  let ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  have hinj : Function.Injective ρ := injective_mk'_of_charTwo hQ hT
  have hsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  let ι : ↥(orthDerived Q) ≃* ProjOrthDerived Q := MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩
  let y : ↥(orthDerived Q) := ι.symm x
  let y₁ : ↥(orthDerived Q) := ι.symm x₁
  let y₂ : ↥(orthDerived Q) := ι.symm x₂
  have hρy : ρ y = x := MulEquiv.apply_symm_apply ι x
  have hρy₁ : ρ y₁ = x₁ := MulEquiv.apply_symm_apply ι x₁
  have hρy₂ : ρ y₂ = x₂ := MulEquiv.apply_symm_apply ι x₂
  have hy3 : y ^ 3 = 1 := by
    apply ι.injective
    rw [map_pow, map_one]
    change ρ y ^ 3 = 1
    rw [hρy, ← hx]
    exact pow_orderOf_eq_one x
  have hy1 : y ≠ 1 := by
    intro hy
    have hx1 : x = 1 := by rw [← hρy, hy, map_one]
    have h1' : orderOf x = 1 := orderOf_eq_one_iff.mpr hx1
    omega
  have hy₁3sub : y₁ ^ 3 = 1 := by
    apply ι.injective
    rw [map_pow, map_one]
    change ρ y₁ ^ 3 = 1
    rw [hρy₁, h₁]
  have hy₂3sub : y₂ ^ 3 = 1 := by
    apply ι.injective
    rw [map_pow, map_one]
    change ρ y₂ ^ 3 = 1
    rw [hρy₂, h₂]
  have hcy₁ : Commute y y₁ := by
    show y * y₁ = y₁ * y
    apply ι.injective
    rw [map_mul, map_mul]
    change ρ y * ρ y₁ = ρ y₁ * ρ y
    rw [hρy, hρy₁]
    exact hc₁.eq
  have hcy₂ : Commute y y₂ := by
    show y * y₂ = y₂ * y
    apply ι.injective
    rw [map_mul, map_mul]
    change ρ y * ρ y₂ = ρ y₂ * ρ y
    rw [hρy, hρy₂]
    exact hc₂.eq
  have hcy₁₂ : Commute y₁ y₂ := by
    show y₁ * y₂ = y₂ * y₁
    apply ι.injective
    rw [map_mul, map_mul]
    change ρ y₁ * ρ y₂ = ρ y₂ * ρ y₁
    rw [hρy₁, hρy₂]
    exact hc₁₂.eq
  have hyx : (QuotientGroup.mk y : ProjOrthDerived Q) = x := by
    have h : ρ y = x := hρy
    rwa [QuotientGroup.mk'_apply] at h
  have hJ' : CFSG.Open.IsComponentOf J
      (Subgroup.centralizer ({(QuotientGroup.mk y : ProjOrthDerived Q)} :
        Set (ProjOrthDerived Q))) := by
    rw [hyx]
    exact hJ
  obtain ⟨hnm, h, hh, hne1, hself, hdeg, hmult, hq, hJh⟩ :=
    exists_selfDual_block_of_component hQ hT hV hdim hK hm hn hn3 hmn hy3 hy1 hJ' hcard
  have hm2 : 2 ≤ m := by omega
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hy : OddOrderIsometry Q 3 (y : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_pow_eq_one Nat.prime_three hpℓ hQ y hy3
  have hy₁mem : (y₁ : V ≃ₗ[K] V) ∈ isometryCentralizer Q (y : V ≃ₗ[K] V) := by
    rw [mem_isometryCentralizer]
    refine ⟨fun v => (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup y₁.2)) v, fun v => ?_⟩
    have hcomm : (y₁ : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V) =
        (y : V ≃ₗ[K] V) * (y₁ : V ≃ₗ[K] V) := by
      simpa using congrArg Subtype.val hcy₁.symm.eq
    simpa only [LinearEquiv.mul_apply] using congrArg (fun e : V ≃ₗ[K] V => e v) hcomm
  have hy₂mem : (y₂ : V ≃ₗ[K] V) ∈ isometryCentralizer Q (y : V ≃ₗ[K] V) := by
    rw [mem_isometryCentralizer]
    refine ⟨fun v => (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup y₂.2)) v, fun v => ?_⟩
    have hcomm : (y₂ : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V) =
        (y : V ≃ₗ[K] V) * (y₂ : V ≃ₗ[K] V) := by
      simpa using congrArg Subtype.val hcy₂.symm.eq
    simpa only [LinearEquiv.mul_apply] using congrArg (fun e : V ≃ₗ[K] V => e v) hcomm
  have hy₁3 : (y₁ : V ≃ₗ[K] V) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hy₁3sub
  have hy₂3 : (y₂ : V ≃ₗ[K] V) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hy₂3sub
  have hcy₁₂' : Commute (y₁ : V ≃ₗ[K] V) (y₂ : V ≃ₗ[K] V) :=
    Commute.map hcy₁₂ (Subgroup.subtype (orthDerived Q))
  let F : Subgroup (V ≃ₗ[K] V) := specialBlock Q (y : V ≃ₗ[K] V) h
  have hSB : F ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  have hmovesBlock : ∀ k : ℕ, ∃ g ∈ F,
      g * ((y₂ : V ≃ₗ[K] V) * (y₁ : V ≃ₗ[K] V) ^ k) ≠
        ((y₂ : V ≃ₗ[K] V) * (y₁ : V ≃ₗ[K] V) ^ k) * g := by
    intro k
    obtain ⟨j, hj, hne⟩ := hmoves k
    rw [hJh] at hj
    obtain ⟨g, hg, hgj⟩ := hj
    refine ⟨(g : V ≃ₗ[K] V), Subgroup.mem_subgroupOf.mp hg, ?_⟩
    intro hcomm
    apply hne
    have hcomm' : Commute g (y₂ * y₁ ^ k) := by
      apply Subtype.ext
      simpa using hcomm
    have hxpow : (x₂ * x₁ ^ k : ProjOrthDerived Q) = ρ (y₂ * y₁ ^ k) := by
      rw [map_mul, map_pow, hρy₂, hρy₁]
    rw [← hgj, hxpow, ← map_mul, ← map_mul, hcomm'.eq]
  have hle₁ : F ⊓ Subgroup.centralizer ({(y₁ : V ≃ₗ[K] V)} :
      Set (V ≃ₗ[K] V)) ≤ orthDerived Q := inf_le_left.trans hSB
  have hle₂ : F ⊓ Subgroup.centralizer ({(y₂ : V ≃ₗ[K] V)} :
      Set (V ≃ₗ[K] V)) ≤ orthDerived Q := inf_le_left.trans hSB
  let φ₁ : ↥(F ⊓ Subgroup.centralizer ({(y₁ : V ≃ₗ[K] V)} :
      Set (V ≃ₗ[K] V))) →*
      ↥(J ⊓ Subgroup.centralizer ({x₁} : Set (ProjOrthDerived Q))) :=
    (ρ.comp (Subgroup.inclusion hle₁)).codRestrict _ (fun A => by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hJh]
        exact Subgroup.mem_map.mpr ⟨⟨(A : V ≃ₗ[K] V), hle₁ A.2⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp A.2).1, rfl⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm : Commute (A : V ≃ₗ[K] V) (y₁ : V ≃ₗ[K] V) :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp A.2).2
        have hcomm' : Commute (Subgroup.inclusion hle₁ A) y₁ := by
          apply Subtype.ext
          simpa using hcomm.eq
        have hmap := Commute.map hcomm' ρ
        rw [hρy₁] at hmap
        exact hmap.eq)
  let φ₂ : ↥(F ⊓ Subgroup.centralizer ({(y₂ : V ≃ₗ[K] V)} :
      Set (V ≃ₗ[K] V))) →*
      ↥(J ⊓ Subgroup.centralizer ({x₂} : Set (ProjOrthDerived Q))) :=
    (ρ.comp (Subgroup.inclusion hle₂)).codRestrict _ (fun A => by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hJh]
        exact Subgroup.mem_map.mpr ⟨⟨(A : V ≃ₗ[K] V), hle₂ A.2⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp A.2).1, rfl⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm : Commute (A : V ≃ₗ[K] V) (y₂ : V ≃ₗ[K] V) :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp A.2).2
        have hcomm' : Commute (Subgroup.inclusion hle₂ A) y₂ := by
          apply Subtype.ext
          simpa using hcomm.eq
        have hmap := Commute.map hcomm' ρ
        rw [hρy₂] at hmap
        exact hmap.eq)
  have hinjφ₁ : Function.Injective φ₁ := by
    intro A B hAB
    have h : ρ (Subgroup.inclusion hle₁ A) = ρ (Subgroup.inclusion hle₁ B) :=
      congrArg Subtype.val hAB
    have h' := hinj h
    exact Subtype.ext (by simpa using congrArg Subtype.val h')
  have hinjφ₂ : Function.Injective φ₂ := by
    intro A B hAB
    have h : ρ (Subgroup.inclusion hle₂ A) = ρ (Subgroup.inclusion hle₂ B) :=
      congrArg Subtype.val hAB
    have h' := hinj h
    exact Subtype.ext (by simpa using congrArg Subtype.val h')
  rintro ⟨hsolJ₁, hsolJ₂⟩
  have hsol₁ : IsSolvable ↥(F ⊓ Subgroup.centralizer ({(y₁ : V ≃ₗ[K] V)} :
      Set (V ≃ₗ[K] V))) := by
    exact @Group.isSolvable_of_isSolvable_injective _ _ _ _ φ₁ hinjφ₁ hsolJ₁
  have hsol₂ : IsSolvable ↥(F ⊓ Subgroup.centralizer ({(y₂ : V ≃ₗ[K] V)} :
      Set (V ≃ₗ[K] V))) := by
    exact @Group.isSolvable_of_isSolvable_injective _ _ _ _ φ₂ hinjφ₂ hsolJ₂
  exact not_isSolvable_and_of_specialBlock hK hm hm2 hy hh hne1 hself hmult hy₁mem hy₂mem
    hy₁3 hy₂3 hcy₁₂' hmovesBlock ⟨hsol₁, hsol₂⟩

end CFSG.LocalAnalysis.GLTheoremA.CanonU3.OrthMinus

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open
open CFSG.RankThree.Classical2 (ProjOrthDerived)

open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)


section Certs


theorem u3TorusCoreOn_orthMinus :
    U3TorusCoreOn fun lab => lab.tag = .twD ∧ lab.rank ≠ 2 ∧ lab.rank ≠ 3 := by
  intro S _ _ labL β β₁ β₂ n J hF hT
  obtain ⟨hD, hr2, hr3⟩ := hF
  obtain ⟨K, hKf, hKfin, b, c, e, hKcard, hodd, ⟨s, hs, hsord⟩, hQ, hTgen, hV, hdim, hcardJ⟩ :=
    U3CoreHyp.exists_orthMinus_model hT.core hD hr2 hr3
  let Q : QuadraticForm K (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus 4 K b c
  obtain ⟨_, _, _, _, _, _, _, ⟨_⟩, ⟨s₁, hs₁⟩⟩ :=
    innDiagKind_twD_data_orthMinus hT.core.center_eq_bot hD hr2 hr3 hT.innDiagKind₁
  obtain ⟨_, _, _, _, _, _, _, ⟨_⟩, ⟨s₂, hs₂⟩⟩ :=
    innDiagKind_twD_data_orthMinus hT.core.center_eq_bot hD hr2 hr3 hT.innDiagKind₂
  have hcen := hT.core.center_eq_bot
  have hs₁3 : s₁ ^ 3 = 1 := by
    apply CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot hcen
    rw [map_pow, hs₁, hT.pow_three₁, map_one]
  have hs₂3 : s₂ ^ 3 = 1 := by
    apply CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot hcen
    rw [map_pow, hs₂, hT.pow_three₂, map_one]
  have hcs₁ : Commute s s₁ := by
    apply CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot hcen
    rw [map_mul, map_mul, hs, hs₁]
    exact hT.commute₁.eq
  have hcs₂ : Commute s s₂ := by
    apply CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot hcen
    rw [map_mul, map_mul, hs, hs₂]
    exact hT.commute₂.eq
  have hcs₁₂ : Commute s₁ s₂ := by
    apply CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot hcen
    rw [map_mul, map_mul, hs₁, hs₂]
    exact hT.commute₁₂.eq
  have hfix : fixSubgroup β = Subgroup.centralizer ({s} : Set S) := by
    rw [← hs]
    exact CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj s
  have hfix₁ : fixSubgroup β₁ = Subgroup.centralizer ({s₁} : Set S) := by
    rw [← hs₁]
    exact CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj s₁
  have hfix₂ : fixSubgroup β₂ = Subgroup.centralizer ({s₂} : Set S) := by
    rw [← hs₂]
    exact CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj s₂
  have hmovesS : ∀ k : ℕ, ∃ j ∈ J, j * (s₂ * s₁ ^ k) ≠ (s₂ * s₁ ^ k) * j := by
    intro k
    obtain ⟨j, hj, hne⟩ := hT.moves₂ k
    refine ⟨j, hj, ?_⟩
    intro hcomm
    apply hne
    have hpow : β₂ * β₁ ^ k = MulAut.conj (s₂ * s₁ ^ k) := by
      rw [map_mul, map_pow, hs₂, hs₁]
    rw [hpow, MulAut.conj_apply, ← hcomm]
    group
  let x : ProjOrthDerived Q := e s
  let x₁ : ProjOrthDerived Q := e s₁
  let x₂ : ProjOrthDerived Q := e s₂
  let J' : Subgroup (ProjOrthDerived Q) := J.map (e : S →* ProjOrthDerived Q)
  have hx : orderOf x = 3 := by
    change orderOf (e s) = 3
    rw [MulEquiv.orderOf_eq, hsord]
  have hx₁ : x₁ ^ 3 = 1 := by
    change (e s₁) ^ 3 = 1
    rw [← map_pow, hs₁3, map_one]
  have hx₂ : x₂ ^ 3 = 1 := by
    change (e s₂) ^ 3 = 1
    rw [← map_pow, hs₂3, map_one]
  have hc₁ : Commute x x₁ := by
    change Commute (e s) (e s₁)
    exact Commute.map hcs₁ (e : S →* ProjOrthDerived Q)
  have hc₂ : Commute x x₂ := by
    change Commute (e s) (e s₂)
    exact Commute.map hcs₂ (e : S →* ProjOrthDerived Q)
  have hc₁₂ : Commute x₁ x₂ := by
    change Commute (e s₁) (e s₂)
    exact Commute.map hcs₁₂ (e : S →* ProjOrthDerived Q)
  have hJcomp : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({s} : Set S)) := by
    have h1 := hT.core.isComponentOf
    rwa [hfix] at h1
  have hJ' : CFSG.Open.IsComponentOf J'
      (Subgroup.centralizer ({x} : Set (ProjOrthDerived Q))) := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJcomp
    have h2 : (Subgroup.centralizer ({s} : Set S)).map (e : S →* ProjOrthDerived Q) =
        Subgroup.centralizer ({(e s)} : Set (ProjOrthDerived Q)) :=
      CFSG.Walter.map_centralizer_singleton_mulEquiv e s
    exact h2 ▸ h1
  let eJ : ↥J ≃* ↥J' :=
    Subgroup.equivMapOfInjective J (e : S →* ProjOrthDerived Q) e.injective
  have hquot : Nat.card (J' ⧸ Subgroup.center J') = Nat.card (J ⧸ Subgroup.center J) := by
    exact (Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J') eJ
      (Subgroup.map_center_eq eJ)).toEquiv).symm
  have hcard' : Nat.card (J' ⧸ Subgroup.center J') = ordTwistedA 2 (2 ^ n) := by
    rw [hquot, hcardJ]
  have hmoves' : ∀ k : ℕ, ∃ j ∈ J', j * (x₂ * x₁ ^ k) ≠ (x₂ * x₁ ^ k) * j := by
    intro k
    obtain ⟨j, hj, hne⟩ := hmovesS k
    refine ⟨e j, Subgroup.mem_map_of_mem (e : S →* ProjOrthDerived Q) hj, ?_⟩
    intro hcomm
    apply hne
    apply e.injective
    simpa only [map_mul, map_pow] using hcomm
  have hmap₁ : (J ⊓ Subgroup.centralizer ({s₁} : Set S)).map e.toMonoidHom =
      J' ⊓ Subgroup.centralizer ({x₁} : Set (ProjOrthDerived Q)) := by
    rw [Subgroup.map_inf J (Subgroup.centralizer ({s₁} : Set S)) e.toMonoidHom e.injective,
      CFSG.Walter.map_centralizer_singleton_mulEquiv]
    rfl
  have hmap₂ : (J ⊓ Subgroup.centralizer ({s₂} : Set S)).map e.toMonoidHom =
      J' ⊓ Subgroup.centralizer ({x₂} : Set (ProjOrthDerived Q)) := by
    rw [Subgroup.map_inf J (Subgroup.centralizer ({s₂} : Set S)) e.toMonoidHom e.injective,
      CFSG.Walter.map_centralizer_singleton_mulEquiv]
    rfl
  have hnot := CFSG.LocalAnalysis.GLTheoremA.CanonU3.OrthMinus.not_isSolvable_and_of_projOrth
    hQ hTgen hV hdim hKcard hodd hT.core.odd hT.core.three_le hT.core.dvd hx hx₁ hx₂
    hc₁ hc₂ hc₁₂ hJ' hcard' hmoves'
  rintro ⟨hsol₁, hsol₂⟩
  apply hnot
  constructor
  · rw [← hmap₁]
    have hsolS₁ : IsSolvable ↥(J ⊓ Subgroup.centralizer ({s₁} : Set S)) := by
      rw [← hfix₁]
      exact hsol₁
    let e₁ := Subgroup.equivMapOfInjective (J ⊓ Subgroup.centralizer ({s₁} : Set S))
      e.toMonoidHom e.injective
    exact @Group.isSolvable_of_isSolvable_injective _ _ _ _ e₁.symm.toMonoidHom
      e₁.symm.injective hsolS₁
  · rw [← hmap₂]
    have hsolS₂ : IsSolvable ↥(J ⊓ Subgroup.centralizer ({s₂} : Set S)) := by
      rw [← hfix₂]
      exact hsol₂
    let e₂ := Subgroup.equivMapOfInjective (J ⊓ Subgroup.centralizer ({s₂} : Set S))
      e.toMonoidHom e.injective
    exact @Group.isSolvable_of_isSolvable_injective _ _ _ _ e₂.symm.toMonoidHom
      e₂.symm.injective hsolS₂

end Certs

end CFSG.LocalAnalysis.GLTheoremA.CanonU3

end
