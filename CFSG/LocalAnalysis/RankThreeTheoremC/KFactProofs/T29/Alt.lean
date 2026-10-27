module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Step0
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294AltPerm
public import CFSG.Holt.H78.AltModelAut
public import CFSG.HardMathSupport.Curtis.Coordinator.PlaneBlock

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement
open CFSG.HardMathSupport.Curtis.Coordinator.Plane
  (conjL conjL_apply conjHom quotAut quotAut_mk quotAutHom)

section Alt

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem le_pCore_of_selfCentralizing {C : Type} [Group C] [Finite C]
    (hF : IsCyclic ↥(CFSG.pCore 3 C))
    (hself : centralizer ((CFSG.pCore 3 C : Subgroup C) : Set C) ≤ CFSG.pCore 3 C)
    {D : Subgroup C} (hD : IsPGroup 3 D) : D ≤ CFSG.pCore 3 C := by
  haveI : (CFSG.pCore 3 C).Normal := CFSG.pCore_normal
  have key : ∀ g : C, (MulAut.conjNormal : C →* MulAut ↥(CFSG.pCore 3 C)) g = 1 →
      g ∈ centralizer ((CFSG.pCore 3 C : Subgroup C) : Set C) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h2 := congrArg
      (fun φ : MulAut ↥(CFSG.pCore 3 C) => ((φ ⟨h, hh⟩ : ↥(CFSG.pCore 3 C)) : C)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    exact ((mul_inv_eq_iff_eq_mul).mp h2).symm
  have hcomm : ∀ c d : C, c * d * c⁻¹ * d⁻¹ ∈ CFSG.pCore 3 C := by
    intro c d
    let ψ : C →* (ZMod (Nat.card ↥(CFSG.pCore 3 C)))ˣ :=
      (IsCyclic.mulAutMulEquiv ↥(CFSG.pCore 3 C)).toMonoidHom.comp
        (MulAut.conjNormal : C →* MulAut ↥(CFSG.pCore 3 C))
    have hk : c * d * c⁻¹ * d⁻¹ ∈ ψ.ker :=
      Abelianization.commutator_subset_ker ψ
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top c) (Subgroup.mem_top d))
    have h3 : (IsCyclic.mulAutMulEquiv ↥(CFSG.pCore 3 C))
        ((MulAut.conjNormal : C →* MulAut ↥(CFSG.pCore 3 C)) (c * d * c⁻¹ * d⁻¹)) = 1 :=
      MonoidHom.mem_ker.mp hk
    have h1 : (MulAut.conjNormal : C →* MulAut ↥(CFSG.pCore 3 C)) (c * d * c⁻¹ * d⁻¹) = 1 :=
      (IsCyclic.mulAutMulEquiv ↥(CFSG.pCore 3 C)).map_eq_one_iff.mp h3
    exact hself (key _ h1)
  have hnorm : (D ⊔ CFSG.pCore 3 C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ D ⊔ CFSG.pCore 3 C :=
      (le_sup_right : CFSG.pCore 3 C ≤ D ⊔ CFSG.pCore 3 C) (hcomm g n)
    have h2 : g * n * g⁻¹ * n⁻¹ * n ∈ D ⊔ CFSG.pCore 3 C := mul_mem h1 hn
    rwa [inv_mul_cancel_right] at h2
  have hpg : IsPGroup 3 ↥(D ⊔ CFSG.pCore 3 C) :=
    IsPGroup.to_sup_of_normal_right hD (CFSG.pCore_isPGroup : IsPGroup 3 ↥(CFSG.pCore 3 C))
  have hle : D ⊔ CFSG.pCore 3 C ≤ CFSG.pCore 3 C :=
    le_sSup (show D ⊔ CFSG.pCore 3 C ∈ {K : Subgroup C | K.Normal ∧ IsPGroup 3 K} from
      ⟨hnorm, hpg⟩)
  exact le_trans (le_sup_left : D ≤ D ⊔ CFSG.pCore 3 C) hle

end Alt

section Alt

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem card_outer_alternating_dvd_four {n : ℕ} (hn : 5 ≤ n) :
    Nat.card (Outer (alternatingGroup (Fin n))) ∣ 4 := by
  by_cases h6 : n = 6
  · subst h6
    have hquot := (inner (alternatingGroup (Fin 6))).card_eq_card_quotient_mul_card_subgroup
    rw [CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_card] at hquot
    have hd := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.card_mulAut_alternating_six_dvd
    have hd' : Nat.card (MulAut (alternatingGroup (Fin 6)) ⧸ inner (alternatingGroup (Fin 6))) * 360
        ∣ 4 * 360 := by
      rw [← hquot]
      exact hd.trans (by norm_num)
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hd'
  · have h2 := CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_card_dvd_two_outside_six
      (n := n) (by omega)
    exact h2.trans (by norm_num)

theorem alt_three_aut_inner {n : ℕ} (hn : 5 ≤ n) (φ : MulAut (alternatingGroup (Fin n)))
    (hφ : φ ^ 3 = 1) : ∃ g : alternatingGroup (Fin n), φ = MulAut.conj g := by
  have hdvd := card_outer_alternating_dvd_four hn
  obtain ⟨q, hqdef⟩ : ∃ q : Outer (alternatingGroup (Fin n)),
      q = QuotientGroup.mk φ := ⟨_, rfl⟩
  have hq3 : q ^ 3 = 1 := by
    have h := map_pow (QuotientGroup.mk' (inner (alternatingGroup (Fin n)))) φ 3
    rw [hφ, map_one] at h
    rw [hqdef]
    exact h.symm
  have h1 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
  have h2 : orderOf q ∣ 4 := (orderOf_dvd_natCard q).trans hdvd
  have h3 : orderOf q = 1 := by
    have h4 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 3 4 = 1 by norm_num] at h4
    exact Nat.dvd_one.mp h4
  have hq1 : q = 1 := orderOf_eq_one_iff.mp h3
  rw [hqdef] at hq1
  have hmem : φ ∈ inner (alternatingGroup (Fin n)) :=
    (QuotientGroup.eq_one_iff (N := inner (alternatingGroup (Fin n))) φ).mp hq1
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, hg.symm⟩

end Alt

section Alt

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem conjNormal_injective_of_centralizer_eq_bot (M : Subgroup X) [M.Normal]
    (hC : centralizer (M : Set X) = ⊥) :
    Function.Injective (MulAut.conjNormal : X →* MulAut M) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgC : g ∈ centralizer (M : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := congrArg (fun a : MulAut M => ((a ⟨l, hl⟩ : M) : X)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rw [hC, Subgroup.mem_bot] at hgC
  exact hgC

theorem T29Setup.centralizer_eq_bot (h : T29Setup X L x) (hZ : center ↥L = ⊥) :
    centralizer (L : Set X) = ⊥ := by
  haveI hLn : L.Normal := h.normal
  by_contra hC1
  have hCn : (centralizer (L : Set X)).Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro l hl
    have hgl : g⁻¹ * l * g ∈ L := by
      have h1 := hLn.conj_mem l hl g⁻¹
      rwa [inv_inv] at h1
    have hcl : g⁻¹ * l * g * c = c * (g⁻¹ * l * g) := hc (g⁻¹ * l * g) hgl
    calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [hcl]
      _ = g * c * g⁻¹ * l := by group
  have hL1 : L ≠ ⊥ := by
    obtain ⟨-, -, -, hsimp⟩ := h.comp
    haveI : Nontrivial (↥L ⧸ center ↥L) := hsimp.toNontrivial
    haveI : Nontrivial ↥L :=
      Function.Surjective.nontrivial
        (QuotientGroup.mk_surjective : Function.Surjective (QuotientGroup.mk : ↥L → ↥L ⧸ center ↥L))
    exact (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance
  have hxpg : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.ord, pow_one])
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hxpg
  obtain ⟨z, hz⟩ := h.exists_omegaCentral (hP (Subgroup.mem_zpowers x))
  have hzC : z ∈ centralizer (L : Set X) :=
    IsOmegaCentral.mem_of_normal_of_core h.core hz hCn hC1
  have hzL : z ∈ L := IsOmegaCentral.mem_of_normal_of_core h.core hz hLn hL1
  have hcen : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hc := Subgroup.mem_centralizer_iff.mp hzC (g : X) g.2
    simpa using hc
  rw [hZ, Subgroup.mem_bot] at hcen
  have hz1 : z = 1 := by simpa using congrArg Subtype.val hcen
  have hord := hz.order
  rw [hz1, orderOf_one] at hord
  norm_num at hord

theorem T29Setup.pRank_top_le_alt (h : T29Setup X L x) (hZ : center ↥L = ⊥) {n : ℕ}
    (hn : 5 ≤ n) (e : (↥L ⧸ center ↥L) ≃* alternatingGroup (Fin n)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ n / 3 := by
  haveI hLn : L.Normal := h.normal
  have hC : centralizer (L : Set X) = ⊥ := T29Setup.centralizer_eq_bot h hZ
  have hinj : Function.Injective (MulAut.conjNormal : X →* MulAut L) :=
    conjNormal_injective_of_centralizer_eq_bot L hC
  obtain ⟨-, -, hcomm, -⟩ := h.comp
  haveI : Group.IsPerfect ↥L := ⟨hcomm⟩
  have h1 := CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num)
    (MulAut.conjNormal : X →* MulAut L) hinj
  have h2 := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_aut_le hn e Nat.prime_three
    (by norm_num)
  exact h1.trans h2

theorem T29Setup.false_of_alt_large (h : T29Setup X L x) (hZ : center ↥L = ⊥) {n : ℕ}
    (hn : 9 ≤ n) (e : (↥L ⧸ center ↥L) ≃* alternatingGroup (Fin n)) : False := by
  haveI hLn : L.Normal := h.normal
  have hC : centralizer (L : Set X) = ⊥ := T29Setup.centralizer_eq_bot h hZ
  have hinj : Function.Injective (MulAut.conjNormal : X →* MulAut L) :=
    conjNormal_injective_of_centralizer_eq_bot L hC
  obtain ⟨e', -⟩ : ∃ e' : ↥L ≃* alternatingGroup (Fin n), True :=
    ⟨(QuotientGroup.quotientBot (G := ↥L)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans e), trivial⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut (alternatingGroup (Fin n)),
      φ = MulAut.congr e' (MulAut.conjNormal (H := L) x) := ⟨_, rfl⟩
  have hx3 : x ^ 3 = 1 := by
    rw [← h.ord]
    exact pow_orderOf_eq_one x
  have hφ3 : φ ^ 3 = 1 := by
    rw [hφ, ← map_pow, ← map_pow, hx3, map_one, map_one]
  have h5 : 5 ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  have h6 : Fintype.card (Fin n) ≠ 6 := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨σ, hσ⟩ := CFSG.Holt.H78.exists_perm_conj_eq_of_mulAut_alternatingGroup h5 h6 φ
  have hφσ : φ = MulAut.conjNormal (H := alternatingGroup (Fin n)) σ := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [hσ a, MulAut.conjNormal_apply]
  have hσ3 : σ ^ 3 = 1 := by
    have hc : (MulAut.conjNormal (H := alternatingGroup (Fin n)) (σ ^ 3)) =
        MulAut.conjNormal (H := alternatingGroup (Fin n)) 1 := by
      rw [map_pow, map_one, ← hφσ, hφ3]
    exact CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega) hc
  haveI hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B, instB, F, hBcomm, hBpow, hBcard, hFinj, hFσ⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.exists_hom_elemAbelian_commute_of_pow_eq_one
      (p := 3) (by norm_num) n (Fin n) (Fintype.card_fin n) σ hσ3
  have hev : ∀ b : B, F b ∈ alternatingGroup (Fin n) := by
    intro b
    rw [Equiv.Perm.mem_alternatingGroup]
    have h3 : F b ^ 3 = 1 := by
      rw [← map_pow, hBpow b, map_one]
    have hs : Equiv.Perm.sign (F b) ^ 3 = 1 := by
      rw [← map_pow, h3, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (F b)) with h1 | h1
    · exact h1
    · rw [h1] at hs
      exact absurd hs (by decide)
  obtain ⟨F', hF'⟩ : ∃ F' : B →* alternatingGroup (Fin n),
      ∀ b, ((F' b : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = F b :=
    ⟨{ toFun := fun b => ⟨F b, hev b⟩
       map_one' := Subtype.ext (map_one F)
       map_mul' := fun a b => Subtype.ext (map_mul F a b) }, fun b => rfl⟩
  have hF'inj : Function.Injective F' := by
    intro a b hab
    apply hFinj
    exact (hF' a).symm.trans ((congrArg Subtype.val hab).trans (hF' b))
  obtain ⟨G', hG'⟩ : ∃ G' : B →* X, ∀ b, G' b = ((e'.symm (F' b) : ↥L) : X) :=
    ⟨L.subtype.comp (e'.symm.toMonoidHom.comp F'), fun b => rfl⟩
  have hG'inj : Function.Injective G' := by
    intro a b hab
    apply hF'inj
    apply e'.symm.injective
    apply Subtype.ext
    exact (hG' a).symm.trans (hab.trans (hG' b))
  have hG'range : G'.range ≤ centralizer ({x} : Set X) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy, hG' b]
    have hfixed : φ (F' b) = F' b := by
      apply Subtype.ext
      rw [hσ (F' b), hF' b]
      rw [← (hFσ b).eq, mul_inv_cancel_right]
    have hpt : φ (F' b) = e' ((MulAut.conjNormal (H := L) x) (e'.symm (F' b))) := by
      subst hφ
      rfl
    have hfix : (MulAut.conjNormal (H := L) x) (e'.symm (F' b)) = e'.symm (F' b) := by
      apply e'.injective
      rw [e'.apply_symm_apply, ← hpt, hfixed]
    have hxa : x * ((e'.symm (F' b) : ↥L) : X) * x⁻¹ = ((e'.symm (F' b) : ↥L) : X) :=
      congrArg (fun t : ↥L => (t : X)) hfix
    calc x * ((e'.symm (F' b) : ↥L) : X)
        = (x * ((e'.symm (F' b) : ↥L) : X) * x⁻¹) * x := by group
      _ = ((e'.symm (F' b) : ↥L) : X) * x := by rw [hxa]
  have hk := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num)
    hBcomm hBpow hBcard G' hG'inj hG'range
  rw [h.cent] at hk
  omega

theorem T29Setup.false_of_alt_center_bot (h : T29Setup X L x) (hZ : center ↥L = ⊥) {n : ℕ}
    (hn : 5 ≤ n) (e : (↥L ⧸ center ↥L) ≃* alternatingGroup (Fin n)) : False := by
  by_cases h9 : 9 ≤ n
  · exact T29Setup.false_of_alt_large h hZ h9 e
  · have h1 := T29Setup.pRank_top_le_alt h hZ hn e
    have h2 := h.rank
    omega

end Alt

section CoverHelpers

theorem commutator_mul_central {K : Type} [Group K] {za zb : K} (hza : za ∈ Subgroup.center K)
    (hzb : zb ∈ Subgroup.center K) (a b : K) :
    za * a * (zb * b) * (za * a)⁻¹ * (zb * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hconj : ∀ z ∈ Subgroup.center K, ∀ x : K, z * x * z⁻¹ = x := by
    intro z hz x
    rw [← Subgroup.mem_center_iff.mp hz x, mul_inv_cancel_right]
  calc za * a * (zb * b) * (za * a)⁻¹ * (zb * b)⁻¹
      = za * (a * (zb * b) * a⁻¹) * za⁻¹ * (b⁻¹ * zb⁻¹) := by group
    _ = (a * (zb * b) * a⁻¹) * (b⁻¹ * zb⁻¹) := by rw [hconj za hza]
    _ = a * (zb * (b * a⁻¹ * b⁻¹) * zb⁻¹) := by group
    _ = a * (b * a⁻¹ * b⁻¹) := by rw [hconj zb hzb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_one_of_trivial_mod_center {K : Type} [Group K] (hK : commutator K = ⊤) (α : K →* K)
    (hα : ∀ k : K, α k * k⁻¹ ∈ Subgroup.center K) : ∀ k : K, α k = k := by
  have hcomm : ∀ a b : K, α ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    obtain ⟨za, hza, hza_eq⟩ : ∃ z ∈ Subgroup.center K, α a = z * a :=
      ⟨α a * a⁻¹, hα a, (inv_mul_cancel_right _ _).symm⟩
    obtain ⟨zb, hzb, hzb_eq⟩ : ∃ z ∈ Subgroup.center K, α b = z * b :=
      ⟨α b * b⁻¹, hα b, (inv_mul_cancel_right _ _).symm⟩
    simp only [commutatorElement_def, map_mul, map_inv]
    rw [hza_eq, hzb_eq]
    exact commutator_mul_central hza hzb a b
  have hle : commutator K ≤ MonoidHom.eqLocus α (MonoidHom.id K) := by
    show ⁅(⊤ : Subgroup K), ⊤⁆ ≤ _
    rw [Subgroup.commutator_le]
    intro a _ b _
    show α ⁅a, b⁆ = ⁅a, b⁆
    exact hcomm a b
  rw [hK] at hle
  intro k
  exact hle (Subgroup.mem_top k)

theorem conj_alg_identity {X : Type} [Group X] (g Lz K T U : X) (hT : T = g * K * g⁻¹)
    (hU : U = T⁻¹ * (Lz * K * Lz⁻¹)) (hUL : Lz * U = U * Lz) (hUK : K * U = U * K) :
    Lz⁻¹ * g * K * (Lz⁻¹ * g)⁻¹ * K⁻¹ = U⁻¹ := by
  have hP : T = Lz * K * Lz⁻¹ * U⁻¹ := by
    rw [hU]
    group
  have hLU' : U⁻¹ * Lz = Lz * U⁻¹ := by
    have hc : Commute Lz U := hUL
    exact hc.inv_right.eq.symm
  have hLU : Lz⁻¹ * U⁻¹ * Lz = U⁻¹ := by
    rw [mul_assoc, hLU', ← mul_assoc, inv_mul_cancel, one_mul]
  have hKU : K * U⁻¹ = U⁻¹ * K := (show Commute K U from hUK).inv_right.eq
  calc Lz⁻¹ * g * K * (Lz⁻¹ * g)⁻¹ * K⁻¹
      = Lz⁻¹ * (g * K * g⁻¹) * Lz * K⁻¹ := by group
    _ = Lz⁻¹ * (Lz * K * Lz⁻¹ * U⁻¹) * Lz * K⁻¹ := by rw [← hT, hP]
    _ = K * (Lz⁻¹ * U⁻¹ * Lz) * K⁻¹ := by group
    _ = K * U⁻¹ * K⁻¹ := by rw [hLU]
    _ = U⁻¹ := by rw [hKU, mul_inv_cancel_right]

end CoverHelpers

section Alt

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem T29Setup.card_center_alt (h : T29Setup X L x) (hZ : center ↥L ≠ ⊥) {n : ℕ}
    (hn : 5 ≤ n) (e : (↥L ⧸ center ↥L) ≃* alternatingGroup (Fin n)) :
    Nat.card (center ↥L) = 3 ∧ (n = 6 ∨ n = 7) := by
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr h.comp.2.2.1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.center_isPGroup
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hZ
    exact Subgroup.card_eq_one.mp (by rw [hk, pow_zero])
  have hfac := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.center_facts hn e Nat.prime_three
    (by norm_num)
  have hdvd : 3 ∣ Nat.card (center ↥L) := by
    rw [hk]
    exact dvd_pow_self 3 hk0
  have h3 := hfac.2 hdvd
  refine ⟨?_, h3.2⟩
  have hf := hfac.1
  rw [hk, Nat.factorization_pow_self Nat.prime_three] at hf
  have hk1 : k = 1 := by omega
  rw [hk, hk1, pow_one]

theorem T29Setup.exists_mul_alt (h : T29Setup X L x) {n : ℕ} (hn : 5 ≤ n) (hn7 : n ≤ 7)
    (e : (↥L ⧸ center ↥L) ≃* alternatingGroup (Fin n)) {g : X} (hg : g ^ 3 = 1) :
    ∃ l ∈ L, ∃ c ∈ centralizer (L : Set X), g = l * c := by
  clear hn7
  haveI hLn : L.Normal := h.normal
  have hN : ∀ y : X, y ∈ Subgroup.normalizer (L : Set X) := by
    intro y
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact Subgroup.mem_top y
  obtain ⟨θ, hθdef⟩ : ∃ θ : MulAut ↥L, θ = conjL g (hN g) := ⟨_, rfl⟩
  have hT : ∀ k : ↥L, ((θ k : ↥L) : X) = g * (k : X) * g⁻¹ := by
    intro k
    rw [hθdef]
    rfl
  have hθ3 : θ ^ 3 = 1 := by
    have hg3 : (⟨g, hN g⟩ : ↥(Subgroup.normalizer (L : Set X))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hg)
    have h1 := map_pow (conjHom L) (⟨g, hN g⟩ : ↥(Subgroup.normalizer (L : Set X))) 3
    rw [hg3, map_one] at h1
    rw [hθdef]
    exact h1.symm
  have hq3 : quotAut θ ^ 3 = 1 := by
    have h1 := map_pow (quotAutHom L) θ 3
    rw [hθ3, map_one] at h1
    exact h1.symm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulAut (alternatingGroup (Fin n)),
      ψ = MulAut.congr e (quotAut θ) := ⟨_, rfl⟩
  have hψ3 : ψ ^ 3 = 1 := by
    have h1 := map_pow (MulAut.congr e) (quotAut θ) 3
    rw [hq3, map_one] at h1
    rw [hψ]
    exact h1.symm
  obtain ⟨a, ha⟩ := alt_three_aut_inner hn ψ hψ3
  have hψapp : ∀ l : ↥L, ψ (e (l : ↥L ⧸ center ↥L)) = e ((θ l : ↥L) : ↥L ⧸ center ↥L) := by
    intro l
    simp only [hψ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      quotAut_mk]
  obtain ⟨l₀, hl₀⟩ := QuotientGroup.mk_surjective (e.symm a)
  have hl₀a : e (l₀ : ↥L ⧸ center ↥L) = a := by
    rw [hl₀, MulEquiv.apply_symm_apply]
  have hkey : ∀ l : ↥L, (θ l)⁻¹ * (l₀ * l * l₀⁻¹) ∈ center ↥L := by
    intro l
    have h1 := hψapp l
    rw [ha, MulAut.conj_apply, ← hl₀a] at h1
    have h2 : ((θ l : ↥L) : ↥L ⧸ center ↥L) = ((l₀ * l * l₀⁻¹ : ↥L) : ↥L ⧸ center ↥L) := by
      apply e.injective
      rw [← h1]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
    exact QuotientGroup.eq.mp h2
  obtain ⟨c, hc_def⟩ : ∃ c : X, c = (l₀ : X)⁻¹ * g := ⟨_, rfl⟩
  obtain ⟨α, hα_def⟩ : ∃ α : MulAut ↥L, α = conjL c (hN c) := ⟨_, rfl⟩
  have hαapp : ∀ k : ↥L, ((α k : ↥L) : X) = c * (k : X) * c⁻¹ := by
    intro k
    rw [hα_def]
    rfl
  have hα : ∀ k : ↥L, α k * k⁻¹ ∈ center ↥L := by
    intro k
    have hu := hkey k
    have hU : (((θ k)⁻¹ * (l₀ * k * l₀⁻¹) : ↥L) : X)
        = ((θ k : ↥L) : X)⁻¹ * ((l₀ : X) * (k : X) * (l₀ : X)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hUL : (l₀ : X) * (((θ k)⁻¹ * (l₀ * k * l₀⁻¹) : ↥L) : X)
        = (((θ k)⁻¹ * (l₀ * k * l₀⁻¹) : ↥L) : X) * (l₀ : X) := by
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hu l₀)
      simpa only [Subgroup.coe_mul] using h1
    have hUK : (k : X) * (((θ k)⁻¹ * (l₀ * k * l₀⁻¹) : ↥L) : X)
        = (((θ k)⁻¹ * (l₀ * k * l₀⁻¹) : ↥L) : X) * (k : X) := by
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hu k)
      simpa only [Subgroup.coe_mul] using h1
    have hX := conj_alg_identity g (l₀ : X) (k : X) ((θ k : ↥L) : X)
      (((θ k)⁻¹ * (l₀ * k * l₀⁻¹) : ↥L) : X) (hT k) hU hUL hUK
    have heq : α k * k⁻¹ = ((θ k)⁻¹ * (l₀ * k * l₀⁻¹))⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hαapp, hc_def]
      exact hX
    rw [heq]
    exact inv_mem hu
  have hfix := eq_one_of_trivial_mod_center h.comp.2.2.1 α.toMonoidHom hα
  have hcent : c ∈ centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hX : c * m * c⁻¹ = m := by
      have h1 : ((α ⟨m, hm⟩ : ↥L) : X) = c * m * c⁻¹ := hαapp ⟨m, hm⟩
      have h2 : ((α ⟨m, hm⟩ : ↥L) : X) = m := congrArg Subtype.val (hfix ⟨m, hm⟩)
      exact h1.symm.trans h2
    calc m * c = (c * m * c⁻¹) * c := by rw [hX]
      _ = c * m := by group
  refine ⟨(l₀ : X), l₀.2, c, hcent, ?_⟩
  rw [hc_def]
  group

end Alt

section CentralizerOfL

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem centralizer_normal (hL : L.Normal) : (centralizer (L : Set X)).Normal :=
  inferInstance

theorem map_pPrimeCore_le {C : Subgroup X} [C.Normal] :
    (CFSG.pPrimeCore 3 ↥C).map C.subtype ≤
      CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := X) 3 := by
  haveI : (CFSG.pPrimeCore 3 ↥C).Characteristic :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_characteristic (G := ↥C) 3
  have hnorm : ((CFSG.pPrimeCore 3 ↥C).map C.subtype).Normal := inferInstance
  have hN : Nat.Coprime 3 (Nat.card ↥(CFSG.pPrimeCore 3 ↥C)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime (G := ↥C) 3
  have hcop : Nat.Coprime 3 (Nat.card ↥((CFSG.pPrimeCore 3 ↥C).map C.subtype)) :=
    Nat.Coprime.coprime_dvd_right ((CFSG.pPrimeCore 3 ↥C).card_map_dvd C.subtype) hN
  exact CFSG.RankThreeCoreUniqueness.Helpers.normal_coprime_le_primeComplementCore 3 _ hnorm hcop

theorem pPrimeCore_centralizer_eq_bot (h : T29Setup X L x) :
    CFSG.pPrimeCore 3 ↥(centralizer (L : Set X)) = ⊥ := by
  haveI hLn : L.Normal := h.normal
  haveI : (centralizer (L : Set X)).Normal := centralizer_normal hLn
  rw [eq_bot_iff]
  intro n hn
  have h1 : ((n : ↥(centralizer (L : Set X))) : X) ∈
      (CFSG.pPrimeCore 3 ↥(centralizer (L : Set X))).map (centralizer (L : Set X)).subtype :=
    Subgroup.mem_map_of_mem (centralizer (L : Set X)).subtype hn
  have h2 := map_pPrimeCore_le (C := centralizer (L : Set X)) h1
  rw [h.core, Subgroup.mem_bot] at h2
  rw [Subgroup.mem_bot]
  exact Subtype.ext h2

theorem layer_centralizer_eq_bot (h : T29Setup X L x) :
    CFSG.layer ↥(centralizer (L : Set X)) = ⊥ := by
  haveI hLn : L.Normal := h.normal
  haveI : (centralizer (L : Set X)).Normal := centralizer_normal hLn
  rw [CFSG.layer.eq_sSup]
  refine le_bot_iff.mp (sSup_le fun J hJ => ?_)
  exfalso
  have hJc : CFSG.Open.IsComponentOf J ⊤ := (CFSG.isComponent_iff_open J).mp hJ
  have hCtop : (⊤ : Subgroup ↥(centralizer (L : Set X))).map (centralizer (L : Set X)).subtype =
      centralizer (L : Set X) := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hy
      exact c.2
    · intro hy
      exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  have hCs : (centralizer (L : Set X)).IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
  have hsub : CFSG.Open.IsSubnormal (J.map (centralizer (L : Set X)).subtype) ⊤ := by
    have h1 := CFSG.Open.IsSubnormal.map (centralizer (L : Set X)).subtype hJc.2.1
    rw [hCtop] at h1
    exact CFSG.Open.IsSubnormal.trans h1 (CFSG.Open.IsSubnormal.of_mathlib hCs)
  have hq : CFSG.Open.IsQuasisimple ↥(J.map (centralizer (L : Set X)).subtype) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv
      (J.equivMapOfInjective (centralizer (L : Set X)).subtype
        (centralizer (L : Set X)).subtype_injective).symm
      hJc.2.2
  have hML : J.map (centralizer (L : Set X)).subtype = L :=
    h.uniq (J.map (centralizer (L : Set X)).subtype) ⟨le_top, hsub, hq⟩
  have hLC : L ≤ centralizer (L : Set X) := hML.symm.le.trans (Subgroup.map_subtype_le J)
  have hcen : ∀ z : ↥L, z ∈ Subgroup.center ↥L := by
    intro z
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (Subgroup.mem_centralizer_iff.mp (hLC z.2)) g g.2
  have hsimp : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := h.comp.2.2.2
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [(QuotientGroup.eq_one_iff a').mpr (hcen a'), (QuotientGroup.eq_one_iff b').mpr (hcen b')]

theorem T29Setup.map_pCore_centralizer_le (h : T29Setup X L x) :
    (CFSG.pCore 3 ↥(centralizer (L : Set X))).map (centralizer (L : Set X)).subtype ≤
      CFSG.pCore 3 X := by
  haveI hLn : L.Normal := h.normal
  haveI : (centralizer (L : Set X)).Normal := centralizer_normal hLn
  haveI : (CFSG.pCore 3 ↥(centralizer (L : Set X))).Characteristic :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCore_characteristic (G := ↥(centralizer (L : Set X))) 3
  have hnorm : ((CFSG.pCore 3 ↥(centralizer (L : Set X))).map
      (centralizer (L : Set X)).subtype).Normal := inferInstance
  have hp : IsPGroup 3 ↥((CFSG.pCore 3 ↥(centralizer (L : Set X))).map
      (centralizer (L : Set X)).subtype) :=
    IsPGroup.map (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup
      (G := ↥(centralizer (L : Set X))) 3) (centralizer (L : Set X)).subtype
  exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCore 3 _ hnorm hp

theorem T29Setup.centralizer_pCore_le (h : T29Setup X L x) :
    centralizer ((CFSG.pCore 3 ↥(centralizer (L : Set X)) : Subgroup ↥(centralizer (L : Set X))) :
      Set ↥(centralizer (L : Set X))) ≤ CFSG.pCore 3 ↥(centralizer (L : Set X)) := by
  haveI hLn : L.Normal := h.normal
  haveI : (centralizer (L : Set X)).Normal := centralizer_normal hLn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot
    ↥(centralizer (L : Set X)) 3 (pPrimeCore_centralizer_eq_bot h) (layer_centralizer_eq_bot h)

end CentralizerOfL

section Alt

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem T29Setup.le_pCore_of_centralizer (h : T29Setup X L x)
    (hO : IsCyclic ↥(CFSG.pCore 3 X)) {D : Subgroup X} (hD : IsPGroup 3 D)
    (hDC : D ≤ centralizer (L : Set X)) : D ≤ CFSG.pCore 3 X := by
  set C : Subgroup X := centralizer (L : Set X) with hC
  let D₀ : Subgroup ↥C := D.subgroupOf C
  have hD₀ : IsPGroup 3 ↥D₀ :=
    hD.of_injective (Subgroup.subgroupOfEquivOfLe hDC).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hDC).injective
  have hF : IsCyclic ↥(CFSG.pCore 3 ↥C) := by
    have h1 := h.map_pCore_centralizer_le
    haveI : IsCyclic ↥(CFSG.pCore 3 X) := hO
    haveI : IsCyclic ↥((CFSG.pCore 3 ↥C).map C.subtype) := isCyclic_of_le h1
    exact isCyclic_of_surjective ((CFSG.pCore 3 ↥C).equivMapOfInjective C.subtype
      C.subtype_injective).symm.toMonoidHom
      ((CFSG.pCore 3 ↥C).equivMapOfInjective C.subtype C.subtype_injective).symm.surjective
  have hle := le_pCore_of_selfCentralizing hF h.centralizer_pCore_le hD₀
  intro d hd
  have hd' : (⟨d, hDC hd⟩ : ↥C) ∈ D₀ := hd
  exact h.map_pCore_centralizer_le ⟨_, hle hd', rfl⟩

theorem T29Setup.false_of_alt_center_ne_bot (h : T29Setup X L x) (hN1 : NoncyclicCentreRank)
    (hA : AltTripleCoverAbelianBound) (hZ : center ↥L ≠ ⊥) {n : ℕ} (hn : 5 ≤ n)
    (e : (↥L ⧸ center ↥L) ≃* alternatingGroup (Fin n)) : False := by
  haveI hLn : L.Normal := h.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcard3, hn67⟩ := h.card_center_alt hZ hn e
  have hn7 : n ≤ 7 := by omega
  have hO : IsCyclic ↥(CFSG.pCore 3 X) := h.isCyclic_pCore hN1
  have hrank := h.pRank_top_eq
  obtain ⟨E, -, hEel, hE27⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  rw [hrank] at hE27
  have hE27' : Nat.card E = 27 := by rw [hE27]; norm_num
  set C : Subgroup X := centralizer (L : Set X) with hC
  have hLE : ∀ g ∈ E, ∃ l ∈ L, ∃ c ∈ C, g = l * c := fun g hg =>
    h.exists_mul_alt hn hn7 e (hEel.2 g hg)
  have hEp : IsPGroup 3 E := CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 3 E hEel
  have hEC : Nat.card (E ⊓ C : Subgroup X) ≤ 3 := by
    have hle : (E ⊓ C : Subgroup X) ≤ CFSG.pCore 3 X :=
      h.le_pCore_of_centralizer hO (hEp.to_le inf_le_left) inf_le_right
    haveI : IsCyclic ↥(CFSG.pCore 3 X) := hO
    haveI : IsCyclic ↥(E ⊓ C : Subgroup X) := isCyclic_of_le hle
    refine card_le_three_of_cyclic (W := ↥(E ⊓ C : Subgroup X)) ?_
    intro w
    have := hEel.2 (w : X) w.2.1
    exact Subtype.ext (by simpa using this)
  have hZ' : Nat.card (L ⊓ C : Subgroup X) = 3 := by
    have hEq : (L ⊓ C : Subgroup X) = (center ↥L).map L.subtype := by
      ext g
      constructor
      · rintro ⟨hgL, hgC⟩
        refine ⟨⟨g, hgL⟩, Subgroup.mem_center_iff.mpr fun l => ?_, rfl⟩
        have := Subgroup.mem_centralizer_iff.mp hgC l l.2
        exact Subtype.ext this
      · rintro ⟨c, hc, rfl⟩
        refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
        have := Subgroup.mem_center_iff.mp hc ⟨l, hl⟩
        exact congrArg Subtype.val this
    rw [hEq, Subgroup.card_map_of_injective L.subtype_injective]
    exact hcard3
  have hC3 : ∀ B : Subgroup X, B ≤ C → IsPGroup 3 B → ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    intro B hBC hB b hb b' hb'
    have hle : B ≤ CFSG.pCore 3 X := h.le_pCore_of_centralizer hO hB hBC
    haveI : IsCyclic ↥(CFSG.pCore 3 X) := hO
    have := (inferInstance : IsMulCommutative ↥(CFSG.pCore 3 X)).is_comm.comm
      (⟨b, hle hb⟩ : ↥(CFSG.pCore 3 X)) ⟨b', hle hb'⟩
    exact congrArg Subtype.val this
  obtain ⟨A, hAL, hA3, hAab, hA27⟩ := exists_abelian_of_elemAbelian_cover hLE hEC hE27' hEel hZ'
    hC3
  have hAp : IsPGroup 3 ↥(A.subgroupOf L) :=
    hA3.of_injective (Subgroup.subgroupOfEquivOfLe hAL).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAL).injective
  have hbound := hA ↥L h.comp.2.2 hcard3 ⟨n, hn, ⟨e⟩⟩ (A.subgroupOf L) hAp (by
    intro a ha b hb
    have := hAab a ha b hb
    exact Subtype.ext this)
  have hcardA : Nat.card ↥(A.subgroupOf L) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  omega

end Alt

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
