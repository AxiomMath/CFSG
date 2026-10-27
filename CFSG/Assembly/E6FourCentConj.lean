module

public import CFSG.Assembly.E6FourCentSetup
public import CFSG.Assembly.E6FourCentTorus
public import CFSG.Assembly.E6FourCentSols
public import CFSG.Assembly.E6FourNeighbourSylow
import CFSG.RankThree.PartOne.KE6.EqpTorsion
public import CFSG.Assembly.E6FourNeighbourCfg
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
open scoped Matrix Pointwise


private lemma map_conj_eq_self_of_mem {G : Type*} [Group G] {K : Subgroup G} {g : G}
    (hg : g ∈ K) : K.map (MulAut.conj g).toMonoidHom = K := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨h, hh, hx⟩ := hx
    rw [← hx]
    change (MulAut.conj g) h ∈ K
    rw [MulAut.conj_apply]
    exact K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg)
  · intro h hh
    rw [Subgroup.mem_map]
    refine ⟨MulAut.conj g⁻¹ h, ?_, ?_⟩
    · change (MulAut.conj g⁻¹) h ∈ K
      rw [MulAut.conj_apply]
      exact K.mul_mem (K.mul_mem (K.inv_mem hg) hh) (by simpa using hg)
    · change (MulAut.conj g) (MulAut.conj g⁻¹ h) = h
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group

private lemma sylow_conj_map {p : ℕ} {G : Type*} [Group G] {g : G} {P Q : Sylow p G}
    (h : g • P = Q) : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = (Q : Subgroup G) := by
  have hsub : (Q : Subgroup G) = MulAut.conj g • (P : Subgroup G) := by
    rw [← h]
    exact Sylow.coe_subgroup_smul
  rw [hsub]
  rfl

private lemma map_subgroupOf_conj {G : Type*} [Group G] {K : Subgroup G} (H : Subgroup G)
    (hH : H ≤ K) (g : ↥K) :
    ((H.subgroupOf K).map (MulAut.conj g).toMonoidHom).map K.subtype =
      H.map (MulAut.conj (g : G)).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, hyx⟩
    refine ⟨(z : G), hz, ?_⟩
    rw [← hyx, ← hzy]
    change (MulAut.conj (g : G)) (z : G) = ((MulAut.conj g) z : G)
    rw [MulAut.conj_apply, MulAut.conj_apply]
    rfl
  · rintro ⟨w, hw, hwx⟩
    refine ⟨⟨(MulAut.conj (g : G)) w, ?_⟩, ⟨⟨⟨w, hH hw⟩, ?_, ?_⟩, hwx⟩⟩
    · change (g : G) * w * (g : G)⁻¹ ∈ K
      rw [← MulAut.conj_apply]
      exact K.mul_mem (K.mul_mem g.2 (hH hw)) (K.inv_mem g.2)
    · exact hw
    · change (MulAut.conj g) ⟨w, hH hw⟩ = ⟨(MulAut.conj (g : G)) w, _⟩
      apply Subtype.ext
      rfl

private theorem exists_sol_of_mem {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E6 L 5) (hq : S.D.q = 4)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5) (x : S.E) :
    ∃ v : Fin Tag.E6.rank → ZMod 5, E6FourIsSol v ∧
      (x : ModGL Tag.E6 L) = rootDiagUnit Tag.E6 (fun j => ζ ^ (v j).val) := by
  obtain ⟨a, ha⟩ := e6Four_torus_mem S (S.E_le x.2).1
  have hx5 : (x : ModGL Tag.E6 L) ^ 5 = 1 := S.E_exp x x.2
  have ha5 : a ^ 5 = 1 := by
    apply rootDiagUnit_injective (τ := Tag.E6) (K := L)
    change (rootDiagUnitHom Tag.E6 L) (a ^ 5) = (rootDiagUnitHom Tag.E6 L) 1
    rw [map_pow (rootDiagUnitHom Tag.E6 L), map_one (rootDiagUnitHom Tag.E6 L)]
    change (rootDiagUnit Tag.E6 a) ^ 5 = 1
    rw [← ha]
    exact hx5
  have h5 : ∀ j, a j ^ 5 = 1 := by
    intro j
    have h := congrFun ha5 j
    simpa using h
  have hT : rootDiagUnit Tag.E6 a ∈ S.D.torus := by rw [← ha]; exact (S.E_le x.2).1
  obtain ⟨v, hv, hav⟩ := e6Four_torsion_sol S hq hρ ζ hζ hT h5
  refine ⟨v, hv, ?_⟩
  rw [ha]
  congr 1
  funext j
  exact hav j

private noncomputable def e6SolOf {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E6 L 5) (hq : S.D.q = 4)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5) (x : S.E) :
    {v : Fin Tag.E6.rank → ZMod 5 // E6FourIsSol v} :=
  ⟨(Classical.choose (exists_sol_of_mem S hq hρ ζ hζ x)),
   (Classical.choose_spec (exists_sol_of_mem S hq hρ ζ hζ x)).1⟩

private theorem e6SolOf_spec {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E6 L 5) (hq : S.D.q = 4)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5) (x : S.E) :
    (x : ModGL Tag.E6 L) =
      rootDiagUnit Tag.E6 (fun j => ζ ^ ((e6SolOf S hq hρ ζ hζ x).1 j).val) :=
  (Classical.choose_spec (exists_sol_of_mem S hq hρ ζ hζ x)).2

private theorem e6SolOf_injective {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E6 L 5) (hq : S.D.q = 4)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5) :
    Function.Injective (e6SolOf S hq hρ ζ hζ) := by
  intro x y hxy
  apply Subtype.ext
  rw [e6SolOf_spec S hq hρ ζ hζ x, e6SolOf_spec S hq hρ ζ hζ y, hxy]

private noncomputable def solFin (x : {v : Fin Tag.E6.rank → ZMod 5 // E6FourIsSol v}) :
    Fin 625 :=
  ⟨Classical.choose (exists_e6SolVec x.2), (Classical.choose_spec (exists_e6SolVec x.2)).1⟩

private theorem solFin_injective : Function.Injective solFin := by
  intro x y hxy
  apply Subtype.ext
  have hchoose : Classical.choose (exists_e6SolVec x.2) =
      Classical.choose (exists_e6SolVec y.2) := congrArg Fin.val hxy
  rw [← (Classical.choose_spec (exists_e6SolVec x.2)).2,
      ← (Classical.choose_spec (exists_e6SolVec y.2)).2, hchoose]

private theorem solFin_surjective : Function.Surjective solFin := by
  intro n
  refine ⟨⟨e6SolVec n.1, e6SolVec_isSol n.1⟩, ?_⟩
  apply Fin.ext
  show Classical.choose (exists_e6SolVec (e6SolVec_isSol n.1)) = n.1
  exact e6SolVec_injOn (Classical.choose_spec (exists_e6SolVec (e6SolVec_isSol n.1))).1 n.2
    (Classical.choose_spec (exists_e6SolVec (e6SolVec_isSol n.1))).2

private theorem natCard_sol :
    Nat.card {v : Fin Tag.E6.rank → ZMod 5 // E6FourIsSol v} = 5 ^ 4 := by
  have hbij : Function.Bijective solFin := ⟨solFin_injective, solFin_surjective⟩
  rw [Nat.card_eq_of_bijective solFin hbij]
  norm_num [Nat.card_eq_fintype_card]

private theorem e6Four_E_card_le {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E6 L 5) (hq : S.D.q = 4)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5) :
    Nat.card S.E ≤ 5 ^ 4 := by
  calc Nat.card S.E ≤ Nat.card {v : Fin Tag.E6.rank → ZMod 5 // E6FourIsSol v} :=
        Nat.card_le_card_of_injective _ (e6SolOf_injective S hq hρ ζ hζ)
    _ = 5 ^ 4 := natCard_sol

theorem e6FourCent_conj {J : Type} [Group J] [Finite J] (hJ : E6FourMark J)
    (hZ : center J = ⊥) {A : Subgroup J} (hA : Nat.card A = 5 ^ 4) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup Tag.E6 L 5)
      (ι : J →* ModGL Tag.E6 L),
      S.D.q = 4 ∧ (∀ γ, IsRoot Tag.E6 γ → S.ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ) ∧
      (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ A.map ι = S.E := by
  obtain ⟨L, iF, iC, S, ι, hq, hρ, hinj, hrange, ⟨S₀, hS₀torus⟩, hΦ⟩ := e6FourCent_setup hJ hZ
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI hmodel : Finite ↥S.D.model := S.finite
  haveI hΓfin : Finite ↥S.Γ := by
    have hle : S.Γ ≤ S.D.model := Subgroup.commutator_le_self S.D.model
    exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  haveI hEfin : Finite ↥S.E := by
    have hle : S.E ≤ S.D.model := fun x hx =>
      Subgroup.commutator_le_self S.D.model (S.E_le hx).2
    exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hA5 : IsPGroup 5 A := IsPGroup.of_card hA
  obtain ⟨P, hAP⟩ := IsPGroup.exists_le_sylow hA5
  have hPcard : Nat.card P = 5 ^ 4 := e6FourSylowFive_holds J hJ hZ P
  have hfacJ : (Nat.card J).factorization 5 = 4 := by
    have h := Sylow.card_eq_multiplicity P
    rw [hPcard] at h
    exact (Nat.pow_right_injective (by norm_num : 1 < 5) h).symm
  have hcardΓ : Nat.card ↥S.Γ = Nat.card J := by
    have h1 : Nat.card ↥ι.range = Nat.card J :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rwa [hrange] at h1
  have hS₀card : Nat.card S₀ = 5 ^ 4 := by
    have h := Sylow.card_eq_multiplicity S₀
    rw [hcardΓ, hfacJ] at h
    exact h
  let H : Subgroup (ModGL Tag.E6 L) := A.map ι
  have hHle : H ≤ S.Γ := by
    dsimp only [H]
    rw [← hrange]
    exact Subgroup.map_le_range ι A
  have hHcard : Nat.card H = 5 ^ 4 := by
    dsimp only [H]
    rw [Subgroup.card_map_of_injective (f := ι) (K := A) hinj, hA]
  have hHsubcard : Nat.card (H.subgroupOf S.Γ) = 5 ^ 4 := by
    rw [← Subgroup.card_subtype S.Γ (H.subgroupOf S.Γ), Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hHle, hHcard]
  obtain ⟨Q, hHQ⟩ := IsPGroup.exists_le_sylow (IsPGroup.of_card hHsubcard)
  have hQcard : Nat.card Q = 5 ^ 4 := by
    have h := Sylow.card_eq_multiplicity Q
    rw [hcardΓ, hfacJ] at h
    exact h
  have hHeqQ : H.subgroupOf S.Γ = Q :=
    Subgroup.eq_of_le_of_card_ge hHQ (by rw [hHsubcard, hQcard])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥S.Γ) Q S₀
  have hQmap : (Q : Subgroup ↥S.Γ).map (MulAut.conj g).toMonoidHom = (S₀ : Subgroup ↥S.Γ) :=
    sylow_conj_map hg
  have hHmap : (H.subgroupOf S.Γ).map (MulAut.conj g).toMonoidHom =
      (S₀ : Subgroup ↥S.Γ) := by
    rw [← hHeqQ] at hQmap
    exact hQmap
  have hTmapH : (S₀ : Subgroup ↥S.Γ).map S.Γ.subtype =
      H.map (MulAut.conj (g : ModGL Tag.E6 L)).toMonoidHom := by
    rw [← hHmap]
    exact map_subgroupOf_conj H hHle g
  have hS₀le : (S₀ : Subgroup ↥S.Γ).map S.Γ.subtype ≤ S.E := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyT : (y : ModGL Tag.E6 L) ∈ S.D.torus := hS₀torus hy
    have hy5 : (y : ModGL Tag.E6 L) ^ 5 = 1 := by
      have h625 : y ^ (5 ^ 4) = 1 := by
        have h : orderOf y ∣ Nat.card ↥(S₀ : Subgroup ↥S.Γ) :=
          Subgroup.orderOf_dvd_natCard (S₀ : Subgroup ↥S.Γ) hy
        rw [hS₀card] at h
        exact orderOf_dvd_iff_pow_eq_one.mp h
      have hmod625 : ((y : ModGL Tag.E6 L)) ^ (5 ^ 4) = 1 := by
        change (S.Γ.subtype y) ^ (5 ^ 4) = 1
        rw [← map_pow S.Γ.subtype y (5 ^ 4), h625, map_one]
      have hmod15 : ((y : ModGL Tag.E6 L)) ^ 15 = 1 := by
        obtain ⟨a, ha⟩ := e6Four_torus_mem S hyT
        have hTa : rootDiagUnit Tag.E6 a ∈ S.D.torus := by rw [← ha]; exact hyT
        have ha15 : a ^ 15 = 1 := by
          funext j
          simpa using e6Four_torus_exp S hq hρ hTa j
        calc ((y : ModGL Tag.E6 L)) ^ 15 = (rootDiagUnit Tag.E6 a) ^ 15 := by rw [ha]
          _ = rootDiagUnit Tag.E6 (a ^ 15) :=
              (map_pow (rootDiagUnitHom Tag.E6 L) a 15).symm
          _ = 1 := by rw [ha15, rootDiagUnit_one]
      have horder : orderOf ((y : ModGL Tag.E6 L)) ∣ 5 := by
        have h1 : orderOf ((y : ModGL Tag.E6 L)) ∣ 15 := orderOf_dvd_of_pow_eq_one hmod15
        have h2 : orderOf ((y : ModGL Tag.E6 L)) ∣ 5 ^ 4 := orderOf_dvd_of_pow_eq_one hmod625
        have h3 := Nat.dvd_gcd h1 h2
        rwa [show Nat.gcd 15 (5 ^ 4) = 5 by norm_num] at h3
      exact orderOf_dvd_iff_pow_eq_one.mp horder
    exact S.E_all (y : ModGL Tag.E6 L) ⟨hyT, y.2⟩ hy5
  have hcardT : Nat.card ((S₀ : Subgroup ↥S.Γ).map S.Γ.subtype) = 5 ^ 4 := by
    rw [Subgroup.card_subtype, hS₀card]
  have hcardSE : Nat.card S.E ≤ 5 ^ 4 := by
    have hq4 : ((4 : ℕ) : L) = 0 := by rw [← hq]; exact S.hqpow.2
    obtain ⟨-, ζ, hζ'⟩ := CFSG.RankThree.PartOne.KE6.eqp_prime_setup (q := 4) hq4
      Nat.prime_five (by norm_num)
    exact e6Four_E_card_le S hq hρ ζ (IsPrimitiveRoot.coe_units_iff.mpr hζ')
  have hTSE : (S₀ : Subgroup ↥S.Γ).map S.Γ.subtype = S.E :=
    Subgroup.eq_of_le_of_card_ge hS₀le (by rw [hcardT]; exact hcardSE)
  have hHSE : H.map (MulAut.conj (g : ModGL Tag.E6 L)).toMonoidHom = S.E := by
    rw [← hTmapH, hTSE]
  refine ⟨L, iF, iC, S, (MulAut.conj (g : ModGL Tag.E6 L)).toMonoidHom.comp ι,
    hq, hρ, hΦ, ?_, ?_, ?_⟩
  · exact (MulEquiv.injective (MulAut.conj (g : ModGL Tag.E6 L))).comp hinj
  · show ((MulAut.conj (g : ModGL Tag.E6 L)).toMonoidHom.comp ι).range = S.Γ
    rw [show ((MulAut.conj (g : ModGL Tag.E6 L)).toMonoidHom.comp ι).range =
        ι.range.map (MulAut.conj (g : ModGL Tag.E6 L)).toMonoidHom from
        (MonoidHom.map_range (MulAut.conj (g : ModGL Tag.E6 L)).toMonoidHom ι).symm]
    rw [hrange]
    exact map_conj_eq_self_of_mem g.2
  · show A.map ((MulAut.conj (g : ModGL Tag.E6 L)).toMonoidHom.comp ι) = S.E
    rw [← Subgroup.map_map (K := A) (f := ι)
      (g := (MulAut.conj (g : ModGL Tag.E6 L)).toMonoidHom)]
    change H.map (MulAut.conj (g : ModGL Tag.E6 L)).toMonoidHom = S.E
    exact hHSE

theorem e6FourCent_E_realize {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E6 L 5)
    (hq : S.D.q = 4)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    (hE : Nat.card S.E = 5 ^ 4) (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5)
    {w : Fin Tag.E6.rank → ZMod 5} (hw : E6FourIsSol w) :
    rootDiagUnit Tag.E6 (fun j => ζ ^ (w j).val) ∈ S.E := by
  have hle : Nat.card {v : Fin Tag.E6.rank → ZMod 5 // E6FourIsSol v} ≤ Nat.card S.E := by
    rw [natCard_sol, hE]
  have hbij := (e6SolOf_injective S hq hρ ζ hζ).bijective_of_nat_card_le hle
  obtain ⟨x, hx⟩ := hbij.2 ⟨w, hw⟩
  have hxspec := e6SolOf_spec S hq hρ ζ hζ x
  rw [hx] at hxspec
  rw [← hxspec]
  exact x.2

end CFSG.Assembly

end
