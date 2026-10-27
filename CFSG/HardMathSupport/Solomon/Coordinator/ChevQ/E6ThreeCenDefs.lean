module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoCalc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.CatLeafProof (weylWordElt)
open CFSG.StandardType.TableBExc.E6Three (mapsRootLines_rootDiagUnit)

set_option linter.unusedSectionVars false

theorem e6Cen_mul_conj_mul_inv {G : Type*} [Group G] (φ : MulAut G) (s : G) :
    φ * MulAut.conj s * φ⁻¹ = MulAut.conj (φ s) :=
  MulEquiv.ext fun g => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

section Concl

variable {K : Type} [Field K]

@[expose] def E6CenConcl (K : Type) [Field K] (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) :
    Prop :=
  ∃ s u : adjointGroup Tag.E6 K, MulAut.conj s ∈ E ∧ MulAut.conj u ∈ E ∧
    MulAut.conj u ∉ Subgroup.zpowers (MulAut.conj s) ∧
    Module.finrank K (LinearMap.ker
      (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 24 ∧
    ∀ k : ℕ, k < 3 → Module.finrank K (LinearMap.ker
      ((((s ^ k * u : adjointGroup Tag.E6 K) : ModGL .E6 K) :
        Module.End K (RootModule .E6 K)) - 1)) = 30

theorem e6Cen_finrank_apply {φ : MulAut (adjointGroup Tag.E6 K)} (hφ : φ ∈ e6Inndiag K)
    (s : adjointGroup Tag.E6 K) :
    Module.finrank K (LinearMap.ker
      ((((φ s : adjointGroup Tag.E6 K) : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) =
      Module.finrank K (LinearMap.ker
        (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) := by
  rw [← range_e6InndiagConj K] at hφ
  obtain ⟨x, rfl⟩ := hφ
  rw [e6InndiagConj_apply]
  exact finrank_ker_conj_sub_one _ _

theorem e6Cen_mem_map_congr {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (φ : MulAut (adjointGroup Tag.E6 K)) {ε : MulAut (adjointGroup Tag.E6 K)} :
    ε ∈ E.map (MulAut.congr φ).toMonoidHom ↔ φ⁻¹ * ε * φ ∈ E := by
  constructor
  · rintro ⟨ε', hε', rfl⟩
    rw [congr_toMonoidHom_apply, show φ⁻¹ * (φ * ε' * φ⁻¹) * φ = ε' by group]
    exact hε'
  · intro h
    exact ⟨_, h, by rw [congr_toMonoidHom_apply]; group⟩

theorem E6CenConcl.of_map {φ : MulAut (adjointGroup Tag.E6 K)} (hφ : φ ∈ e6Inndiag K)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (h : E6CenConcl K (E.map (MulAut.congr φ).toMonoidHom)) : E6CenConcl K E := by
  obtain ⟨s, u, hs, hu, hsu, h24, h30⟩ := h
  have hφi : φ⁻¹ ∈ e6Inndiag K := inv_mem hφ
  have hc : ∀ t : adjointGroup Tag.E6 K, MulAut.conj t ∈ E.map (MulAut.congr φ).toMonoidHom →
      MulAut.conj (φ⁻¹ t) ∈ E := fun t ht => by
    rw [← e6Cen_mul_conj_mul_inv, inv_inv]
    exact (e6Cen_mem_map_congr φ).1 ht
  refine ⟨φ⁻¹ s, φ⁻¹ u, hc s hs, hc u hu, fun h => hsu ?_, ?_, fun k hk => ?_⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have e := congrArg (fun ψ => φ * ψ * φ⁻¹) hk
    simp only [← map_zpow, e6Cen_mul_conj_mul_inv, MulAut.apply_inv_self] at e
    rw [← map_zpow]
    exact e
  · rw [e6Cen_finrank_apply hφi]
    exact h24
  · rw [← map_pow, ← map_mul, e6Cen_finrank_apply hφi]
    exact h30 k hk

theorem e6InnerAll24_of_map {φ : MulAut (adjointGroup Tag.E6 K)} (hφ : φ ∈ e6Inndiag K)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (h : E6InnerAll24 K (E.map (MulAut.congr φ).toMonoidHom)) : E6InnerAll24 K E := by
  intro s hs hs1
  have h1 : MulAut.conj (φ s) ∈ E.map (MulAut.congr φ).toMonoidHom := by
    rw [← e6Cen_mul_conj_mul_inv, ← congr_toMonoidHom_apply]
    exact Subgroup.mem_map_of_mem _ hs
  have h2 : φ s ≠ 1 := fun h' => hs1 (φ.injective (h'.trans (map_one φ).symm))
  rw [← e6Cen_finrank_apply hφ]
  exact h (φ s) h1 h2

variable [Finite K]

@[expose] def E6CenCube (K : Type) [Field K] [Finite K]
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) : Prop :=
  IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ E ≤ e6Inndiag K ∧
    ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) ∧ ¬ E6NormalizesR K E ∧
    ¬ E6InnerAll24 K E

theorem E6CenCube.map {φ : MulAut (adjointGroup Tag.E6 K)} (hφ : φ ∈ e6Inndiag K)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (h : E6CenCube K E) :
    E6CenCube K (E.map (MulAut.congr φ).toMonoidHom) := by
  obtain ⟨hE, hEc, hED, hEi, hER, hA⟩ := h
  obtain ⟨h1, h2, h3, h4, h5⟩ := e6Cube_map_congr hφ hE hEc hED hEi hER
  exact ⟨h1, h2, h3, h4, h5, fun h' => hA (e6InnerAll24_of_map hφ h')⟩

end Concl

section Mono

variable
  {K : Type} [Field K]

theorem e6Cen_four_le_card [Finite K] (hK : 3 ∣ Nat.card K - 1) : 4 ≤ Nat.card K := by
  have h2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial K)
    omega
  omega

theorem e6Cen_conj_mul_rootDiag (n : adjointGroup Tag.E6 K) (b : Fin Tag.E6.rank → Kˣ) :
    MulAut.conj n * rootDiagAutHom Tag.E6 K b =
      e6InndiagConj K ⟨(n : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 b,
        mul_mem (adjointGroup_le_e6InndiagGL K n.2) (rootDiagUnit_mem_e6InndiagGL b)⟩ := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [e6InndiagConj_apply]
  change (n : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 b * h * (rootDiagUnit Tag.E6 b)⁻¹) *
    (n : ModGL Tag.E6 K)⁻¹ = _
  group

theorem e6Cen_coe_eq_of_conj_eq [Finite K] (hK4 : 4 ≤ Nat.card K)
    {s n : adjointGroup Tag.E6 K} {b : Fin Tag.E6.rank → Kˣ}
    (h : MulAut.conj s = MulAut.conj n * rootDiagAutHom Tag.E6 K b) :
    (s : ModGL Tag.E6 K) = n * rootDiagUnit Tag.E6 b := by
  have hs : MulAut.conj s = e6InndiagConj K ⟨s, adjointGroup_le_e6InndiagGL K s.2⟩ :=
    MulEquiv.ext fun h => Subtype.ext (by rw [e6InndiagConj_apply]; rfl)
  rw [hs, e6Cen_conj_mul_rootDiag] at h
  exact congrArg Subtype.val (e6InndiagConj_injective K hK4 h)

theorem e6Cen_coe_eq_of_conj_eq_rootDiag [Finite K] (hK4 : 4 ≤ Nat.card K)
    {s : adjointGroup Tag.E6 K} {b : Fin Tag.E6.rank → Kˣ}
    (h : MulAut.conj s = rootDiagAutHom Tag.E6 K b) :
    (s : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 b := by
  have h' : MulAut.conj s = MulAut.conj 1 * rootDiagAutHom Tag.E6 K b := by
    rw [map_one, one_mul, h]
  rw [e6Cen_coe_eq_of_conj_eq hK4 h', OneMemClass.coe_one, one_mul]

theorem bmMono_one : BmMono (1 : MulAut (adjointGroup Tag.E6 K)) 1 :=
  ⟨1, 1, by rw [OneMemClass.coe_one]; exact one_mem _,
    by rw [OneMemClass.coe_one]; exact mapsRootLines_one, by rw [map_one, map_one, mul_one]⟩

theorem BmMono.inv {X : MulAut (adjointGroup Tag.E6 K)} {v : WeylGroup Tag.E6}
    (h : BmMono X v) : BmMono X⁻¹ v⁻¹ := by
  obtain ⟨n, b, hn, hnv, rfl⟩ := h
  have hn' : ((n⁻¹ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈ monomialSubgroup Tag.E6 K := by
    rw [InvMemClass.coe_inv]
    exact inv_mem hn
  have hv' : MapsRootLines ((n⁻¹ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) v⁻¹ := by
    rw [InvMemClass.coe_inv]
    exact hnv.inv
  refine ⟨n⁻¹, weylTuple v⁻¹⁻¹ b⁻¹, hn', hv', ?_⟩
  rw [mul_inv_rev, ← map_inv (rootDiagAutHom Tag.E6 K), ← map_inv MulAut.conj,
    bm_rootDiag_mul_conj hn' hv']

theorem BmMono.pow {X : MulAut (adjointGroup Tag.E6 K)} {v : WeylGroup Tag.E6}
    (h : BmMono X v) (k : ℕ) : BmMono (X ^ k) (v ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact bmMono_one
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem BmMono.conj_word {X : MulAut (adjointGroup Tag.E6 K)} {v : WeylGroup Tag.E6}
    (h : BmMono X v) (μ : List (Fin Tag.E6.rank)) :
    BmMono (MulAut.conj (weylWordElt .E6 K μ) * X * (MulAut.conj (weylWordElt .E6 K μ))⁻¹)
      ((coxeterSystem Tag.E6).wordProd μ * v * ((coxeterSystem Tag.E6).wordProd μ)⁻¹) :=
  ((bmMono_conj μ).mul h).mul (bmMono_conj_inv μ)

theorem BmMono.exists_eq_rootDiag {X : MulAut (adjointGroup Tag.E6 K)} (h : BmMono X 1) :
    ∃ b, X = rootDiagAutHom Tag.E6 K b := by
  have h' : BmMono X ((coxeterSystem Tag.E6).wordProd []) := by
    rwa [CoxeterSystem.wordProd_nil]
  obtain ⟨b, hb⟩ := h'.exists_eq_word
  refine ⟨b, ?_⟩
  rw [hb, show weylWordElt .E6 K [] = 1 from rfl, map_one, one_mul]

variable [Finite K]

theorem BmMono.unique (hK4 : 4 ≤ Nat.card K) {X : MulAut (adjointGroup Tag.E6 K)}
    {v v' : WeylGroup Tag.E6} (h : BmMono X v) (h' : BmMono X v') : v = v' := by
  obtain ⟨n, b, -, hnv, rfl⟩ := h
  obtain ⟨n', b', -, hnv', he⟩ := h'
  rw [e6Cen_conj_mul_rootDiag, e6Cen_conj_mul_rootDiag] at he
  have e : (n : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 b =
      (n' : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 b' :=
    congrArg Subtype.val (e6InndiagConj_injective K hK4 he)
  have m1 := hnv.mul (mapsRootLines_rootDiagUnit (τ := Tag.E6) (K := K) b)
  have m2 := hnv'.mul (mapsRootLines_rootDiagUnit (τ := Tag.E6) (K := K) b')
  rw [mul_one] at m1 m2
  rw [e] at m1
  exact m1.unique m2

@[expose] def e6CenImage (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) :
    Subgroup (WeylGroup Tag.E6) where
  carrier := {v | ∃ X ∈ E, BmMono X v}
  mul_mem' := by
    rintro _ _ ⟨X, hX, hXv⟩ ⟨Y, hY, hYu⟩
    exact ⟨X * Y, mul_mem hX hY, hXv.mul hYu⟩
  one_mem' := ⟨1, one_mem E, bmMono_one⟩
  inv_mem' := by
    rintro _ ⟨X, hX, hXv⟩
    exact ⟨X⁻¹, inv_mem hX, hXv.inv⟩

theorem mem_e6CenImage {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {v : WeylGroup Tag.E6} :
    v ∈ e6CenImage E ↔ ∃ X ∈ E, BmMono X v :=
  Iff.rfl

theorem e6CenImage_pow_three (hK4 : 4 ≤ Nat.card K)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    {v : WeylGroup Tag.E6} (hv : v ∈ e6CenImage E) : v ^ 3 = 1 := by
  obtain ⟨X, hX, hXv⟩ := hv
  have h := hXv.pow 3
  rw [hE.2 X hX] at h
  exact (BmMono.unique hK4 bmMono_one h).symm

theorem e6CenImage_mul_comm (hK4 : 4 ≤ Nat.card K)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    {v u : WeylGroup Tag.E6} (hv : v ∈ e6CenImage E) (hu : u ∈ e6CenImage E) :
    v * u = u * v := by
  obtain ⟨X, hX, hXv⟩ := hv
  obtain ⟨Y, hY, hYu⟩ := hu
  have hc : X * Y = Y * X := congrArg Subtype.val (hE.1.is_comm.comm (⟨X, hX⟩ : E) ⟨Y, hY⟩)
  have h1 := hXv.mul hYu
  rw [hc] at h1
  exact BmMono.unique hK4 h1 (hYu.mul hXv)

@[expose] def E6CenFrame (O : Subgroup (WeylGroup Tag.E6))
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) : Prop :=
  (∀ X ∈ E, ∃ v ∈ O, BmMono X v) ∧ ∀ v ∈ O, ∃ X ∈ E, BmMono X v

theorem e6CenFrame_image {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (h : ∀ X ∈ E, ∃ v, BmMono X v) : E6CenFrame (e6CenImage E) E :=
  ⟨fun X hX => by
    obtain ⟨v, hv⟩ := h X hX
    exact ⟨v, ⟨X, hX, hv⟩, hv⟩, fun _ hv => hv⟩

theorem e6CenImage_le (hK4 : 4 ≤ Nat.card K) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    {O : Subgroup (WeylGroup Tag.E6)} (h : ∀ X ∈ E, ∃ v ∈ O, BmMono X v) : e6CenImage E ≤ O := by
  rintro v ⟨X, hX, hXv⟩
  obtain ⟨v', hv', hXv'⟩ := h X hX
  rwa [BmMono.unique hK4 hXv hXv']

theorem E6CenFrame.map_word {O : Subgroup (WeylGroup Tag.E6)}
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (h : E6CenFrame O E)
    (μ : List (Fin Tag.E6.rank)) :
    E6CenFrame (O.map (MulAut.conj ((coxeterSystem Tag.E6).wordProd μ)).toMonoidHom)
      (E.map (MulAut.congr (MulAut.conj (weylWordElt .E6 K μ))).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨X, hX, rfl⟩
    obtain ⟨v, hv, hXv⟩ := h.1 X hX
    rw [congr_toMonoidHom_apply]
    exact ⟨_, ⟨v, hv, rfl⟩, hXv.conj_word μ⟩
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨X, hX, hXv⟩ := h.2 v hv
    refine ⟨_, ⟨X, hX, rfl⟩, ?_⟩
    rw [congr_toMonoidHom_apply]
    exact hXv.conj_word μ

theorem e6Cen_conj_word_mem_inndiag (μ : List (Fin Tag.E6.rank)) :
    MulAut.conj (weylWordElt .E6 K μ) ∈ e6Inndiag K :=
  innerAut_le_e6Inndiag K ⟨_, rfl⟩

end Mono

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
