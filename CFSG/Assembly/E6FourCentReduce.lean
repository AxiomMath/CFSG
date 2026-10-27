module

public import CFSG.Assembly.E6FourCentConj
public import CFSG.Assembly.E6FourCentCentralizes
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
import CFSG.RankThree.PartOne.KE6.EqpTorsion
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import Certificates.Certificate10050
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate8117
import CFSG.RankThree.Classical2.TwistedE6Phi3Lines
import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
import CFSG.RankThree.PartOne.KE6.EqpArith
import CFSG.RankThree.PartOne.KE6.Phi3Arith
import CFSG.RankThree.PartOne.KE6.Phi3Lattice
import CFSG.RankThree.PartOne.KE6.Phi3Torus
import CFSG.RankThree.PartOne.KE6.Phi6Arith
import CFSG.RankThree.PartOne.KF4.KernelTools

public section

namespace CFSG.Assembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.StandardType Subgroup
open scoped Matrix


theorem e6FourCent_reduce {J : Type} [Group J] [Finite J] (hJ : E6FourMark J)
    (hZ : center J = ⊥) {A : Subgroup J} (hA : Nat.card A = 5 ^ 4) {s : J} (hsA : s ∈ A)
    (hs1 : s ≠ 1) {X : Subgroup J} (hX : IsComponentOf X (centralizer ({s} : Set J)))
    (hAX : A ≤ normalizer (X : Set J)) (hC : A ⊓ centralizer (X : Set J) = zpowers s) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup Tag.E6 L 5) (ζ : Lˣ)
      (v : Fin Tag.E6.rank → ZMod 5)
      (i : KernelComponent (rootCharHom (fun j => ζ ^ (v j).val))),
      S.D.q = 4 ∧ (∀ γ, IsRoot Tag.E6 γ → S.ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ) ∧
      (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      IsPrimitiveRoot (ζ : L) 5 ∧ E6FourIsSol v ∧ v ≠ 0 ∧
      rootDiagUnit Tag.E6 (fun j => ζ ^ (v j).val) ∈ S.D.torus ∧
      Nonempty (↥X ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom (fun j => ζ ^ (v j).val)) i)) ∧
      Nat.card {w : Fin Tag.E6.rank → ZMod 5 // E6FourIsSol w ∧
        ∀ γ ∈ rationalRoots S.ρ (rootCharHom (fun j => ζ ^ (v j).val)) i, e6Pair w γ = 0} ≤ 5 := by
  classical
  obtain ⟨L, hLf, hLac, S, ι, hq, hρ, hΦ, hinj, hrange, hAE⟩ := e6FourCent_conj hJ hZ hA
  letI : Field L := hLf
  letI : IsAlgClosed L := hLac
  have hE : Nat.card S.E = 5 ^ 4 := by
    rw [← hAE, Subgroup.card_map_of_injective hinj, hA]
  have h4L : (4 : L) = 0 := by
    simpa [hq] using S.hqpow.2
  obtain ⟨hp5L, ζ, hζu⟩ :=
    CFSG.RankThree.PartOne.KE6.eqp_prime_setup (L := L) (q := 4) h4L (p := 5)
      Nat.prime_five (by norm_num)
  have hζ : IsPrimitiveRoot (ζ : L) 5 := IsPrimitiveRoot.coe_units_iff.mpr hζu
  have hsE : ι s ∈ S.E := by
    rw [← hAE]
    exact Subgroup.mem_map_of_mem ι hsA
  have hxT : ι s ∈ S.D.torus := (S.E_le hsE).1
  have hx5 : (ι s) ^ 5 = 1 := S.E_exp (ι s) hsE
  obtain ⟨a, ha⟩ := e6Four_torus_mem S hxT
  have hTa : rootDiagUnit Tag.E6 a ∈ S.D.torus := by rw [← ha]; exact hxT
  have hrootpow : (rootDiagUnit Tag.E6 a) ^ 5 = rootDiagUnit Tag.E6 (a ^ 5) :=
    (map_pow (rootDiagUnitHom Tag.E6 L) a 5).symm
  have ha5 : a ^ 5 = 1 :=
    (rootDiagUnit_injective (τ := Tag.E6))
      (by rw [← hrootpow, ← ha, hx5, rootDiagUnit_one])
  have h5 : ∀ j, a j ^ 5 = 1 := fun j => by simpa using congrFun ha5 j
  obtain ⟨v, hvsol, hv⟩ := e6Four_torsion_sol S hq hρ ζ hζ hTa h5
  let a' : Fin Tag.E6.rank → Lˣ := fun j => ζ ^ (v j).val
  have ha' : rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a' :=
    congrArg (rootDiagUnit Tag.E6) (funext hv)
  have his : ι s = rootDiagUnit Tag.E6 a' := ha.trans ha'
  have hT' : rootDiagUnit Tag.E6 a' ∈ S.D.torus := by rw [← ha']; exact hTa
  have hv0 : v ≠ 0 := by
    intro hvz
    have ha1 : a = 1 := by
      funext j
      rw [hv j, hvz]
      simp
    exact hs1 (hinj (by rw [ha, ha1, rootDiagUnit_one, map_one]))
  let β : MulAut J := MulAut.conj s
  have hβ : ∀ c, ι (β c) = rootDiagUnit Tag.E6 a' * ι c * (rootDiagUnit Tag.E6 a')⁻¹ := by
    intro c
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, his]
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β =
      Subgroup.centralizer ({s} : Set J) := by
    ext x
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc x * s = (s * x * s⁻¹) * s := by rw [h]
        _ = s * x := by group
    · intro h; rw [← h]; group
  have hXopen : CFSG.Open.IsComponentOf X
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) := by
    rw [hfix]
    exact isComponentOf_iff_open.mp hX
  have hne : Tag.E6 ≠ Tag.G2 := by decide
  have hsmall : Tag.E6 = .G2 → 5 ≤ 5 ∨ 4 ≤ S.D.q := fun h => by cases h
  have hap : ∀ j, a' j ^ 5 = 1 := by
    intro j
    show (ζ ^ (v j).val) ^ 5 = 1
    rw [← pow_mul, mul_comm, pow_mul, hζu.pow_eq_one, one_pow]
  have his1 : ι s ≠ 1 := fun h => hs1 (hinj (by rw [h, map_one]))
  have h1' : rootDiagUnit Tag.E6 a' ≠ 1 := by rw [← his]; exact his1
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime
    S Nat.prime_five hp5L hsmall hT' hap h1'
  obtain ⟨i, _, hmap⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S Nat.prime_five
      ι hinj hrange β hβ hT' hap h1' hTame hXopen
  refine ⟨L, hLf, hLac, S, ζ, v, i, hq, hρ, hΦ, hζ, hvsol, hv0, hT', ?_, ?_⟩
  · exact ⟨(Subgroup.equivMapOfInjective X ι hinj).trans (MulEquiv.subgroupCongr hmap)⟩
  let T : Type := {w : Fin Tag.E6.rank → ZMod 5 // E6FourIsSol w ∧
    ∀ γ ∈ rationalRoots S.ρ (rootCharHom a') i, e6Pair w γ = 0}
  change Nat.card T ≤ 5
  let dw : T → ModGL Tag.E6 L := fun w => rootDiagUnit Tag.E6 (fun j => ζ ^ (w.1 j).val)
  have hdE : ∀ w : T, dw w ∈ S.E := fun w => e6FourCent_E_realize S hq hρ hE ζ hζ w.2.1
  have exists_y : ∀ w : T, ∃ y : J, y ∈ A ∧ ι y = dw w := fun w => by
    have h1 : dw w ∈ A.map ι := by rw [hAE]; exact hdE w
    exact (Subgroup.mem_map (f := ι)).1 h1
  let yw : T → J := fun w => Classical.choose (exists_y w)
  have hyw : ∀ w : T, yw w ∈ A ∧ ι (yw w) = dw w := fun w => Classical.choose_spec (exists_y w)
  have hcomm : ∀ (w : T) {u : J}, u ∈ X → yw w * u = u * yw w := by
    intro w u hu
    have hιu : ι u ∈ rationalComponent S.ρ S.Γ (rootCharHom a') i := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem ι hu
    have hb : ∀ γ ∈ rationalRoots S.ρ (rootCharHom a') i,
        rootChar (fun j => ζ ^ (w.1 j).val) γ = 1 := by
      intro γ hγ
      exact (e6Four_rootChar_eq_one_iff ζ hζ w.1 γ).2 (w.2.2 γ hγ)
    have hcw := e6Four_rootDiag_commute S i hb hιu
    have h1 : ι (yw w * u) = ι (u * yw w) := by
      rw [map_mul, map_mul, (hyw w).2]
      exact hcw.eq
    exact hinj h1
  have hyC : ∀ w : T, yw w ∈ Subgroup.centralizer (X : Set J) := fun w =>
    Subgroup.mem_centralizer_iff.2 fun u hu => (hcomm w hu).symm
  let f : T → ↥(zpowers s) := fun w =>
    ⟨yw w, by rw [← hC]; exact Subgroup.mem_inf.2 ⟨(hyw w).1, hyC w⟩⟩
  have hf_inj : Function.Injective f := by
    intro w w' hww'
    have hy : yw w = yw w' := congrArg Subtype.val hww'
    have hdw : dw w = dw w' := by rw [← (hyw w).2, ← (hyw w').2, hy]
    have hdw' : rootDiagUnit Tag.E6 (fun j => ζ ^ (w.1 j).val) =
        rootDiagUnit Tag.E6 (fun j => ζ ^ (w'.1 j).val) := hdw
    have hfun : (fun j => ζ ^ (w.1 j).val) = (fun j => ζ ^ (w'.1 j).val) :=
      (rootDiagUnit_injective (τ := Tag.E6)) hdw'
    refine Subtype.ext (funext fun j => ?_)
    exact ZMod.val_injective 5
      (IsPrimitiveRoot.pow_inj hζu (ZMod.val_lt (w.1 j)) (ZMod.val_lt (w'.1 j))
        (congrFun hfun j))
  have hs5 : s ^ 5 = 1 := hinj (by rw [map_pow, hx5, map_one])
  have hcard : Nat.card T ≤ Nat.card (zpowers s) := Nat.card_le_card_of_injective f hf_inj
  rw [Nat.card_zpowers] at hcard
  exact le_trans hcard (orderOf_le_of_pow_eq_one (by norm_num) hs5)

end CFSG.Assembly

end
