module

public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross
public import CFSG.GroupTheory.ElementaryAbelianTransport
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.LieType.OutStructure

open Matrix TauCeti CFSG.Open CFSG.AGLEmbeddingD2

theorem not_isD2SeitzException_typeA {m : ℕ} (hm : 4 ≤ m) (q : PrimePower) (p : ℕ) :
    ¬ IsD2SeitzException p (LieTypeIndex.A m q) ∧
      ¬ IsD2SeitzException p (LieTypeIndex.twistedA m q) := by
  constructor <;>
  · rintro (⟨-, ⟨q', -, -, h⟩ | ⟨q', -, -, h⟩ | ⟨q', -, -, h⟩ | ⟨q', -, -, h | h⟩ | h⟩ | ⟨-, h | h⟩)
      <;> simp only [reduceCtorEq, LieTypeIndex.A.injEq, LieTypeIndex.twistedA.injEq] at h
      <;> omega

theorem exists_lieIndex_of_classical {S : Type} [Group S] {t : StatedLieTag} {N r f : ℕ}
    (hcl : StatedClassicalModel S t N r f) (ht : t = .PSL ∨ t = .PSU) (hN : 5 ≤ N) :
    ∃ d : ValidLieTypeIndex, d.1.characteristic = r ∧ (∀ p, ¬ IsD2SeitzException p d.1) ∧
      Nonempty (S ≃* (CFSGIndex.lie d).Group) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rcases ht with rfl | rfl
  · have h := hcl
    let q : PrimePower := ⟨r, f, h.1.1, by have hf := h.1.2.1; omega⟩
    have : Fact r.Prime := ⟨h.1.1⟩
    have hdup : ¬ (LieTypeIndex.A (m + 1 - 1) q).IsDuplicateRepresentative := by
      rw [LieTypeIndex.isDuplicateRepresentative_iff]
      omega
    have hv : (LieTypeIndex.A (m + 1 - 1) q).Valid :=
      CFSG.ClassicalModels.linearCatalog_index_valid (m + 1) r f h.1 hdup
    have hv' : (LieTypeIndex.A m q).Valid := by simpa using hv
    obtain ⟨K, hfield, hfinite, hKcard, ⟨e⟩⟩ := h.2
    let _ := hfield
    let _ := hfinite
    let eK := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K (m + 1) r f
      (by have hf := h.1.2.1; omega) hKcard
    let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv'
    refine ⟨⟨LieTypeIndex.A m q, hv'⟩, by simp [q], fun p =>
      (not_isD2SeitzException_typeA (by omega) q p).1, ⟨(e.trans eK).trans eC.symm⟩⟩
  · obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := hcl
    let _ := hfield
    let _ := hfinite
    have hp : r.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    have hv := CFSG.ClassicalModels.unitaryCatalog_index_valid (m + 1) r f hadm
    let _ : Fact r.Prime := ⟨hp⟩
    let q : PrimePower := ⟨r, f, hp, by omega⟩
    let L := GaloisField r (2 * f)
    let _ : Fintype K := Fintype.ofFinite K
    let _ : Fintype L := Fintype.ofFinite L
    have hcard : Fintype.card K = Fintype.card L := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
        GaloisField.card r (2 * f) (by omega), ← pow_mul, mul_comm]
    let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
    let e1 := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin (m + 1)) φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ (m + 1) (r ^ f))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
    have hv' : (LieTypeIndex.twistedA m q).Valid := by simpa using hv
    let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv'
    exact ⟨⟨_, hv'⟩, by simp [q], fun p => (not_isD2SeitzException_typeA (by omega) q p).2,
      ⟨(e.trans e1).trans eT.symm⟩⟩

theorem le_closure_fixed_of_seitz (hS : KFactSeitzRankTwo) {Y : Type} [Group Y] [Finite Y]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {C : Subgroup Y} {d : ValidLieTypeIndex}
    (hpd : p ≠ d.1.characteristic) (hexc : ¬ IsD2SeitzException p d.1)
    (φ : ↥C ≃* (CFSGIndex.lie d).Group) {E : Subgroup Y} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hEN : E ≤ Subgroup.normalizer (C : Set Y))
    (hfaith : ∀ x ∈ E, x ≠ 1 → ∃ c ∈ C, x * c ≠ c * x) :
    C ≤ Subgroup.closure {c | c ∈ C ∧ ∃ x ∈ E, x ≠ 1 ∧ x * c = c * x} := by
  classical
  let N : Subgroup Y := Subgroup.normalizer (C : Set Y)
  have hCN : C ≤ N := Subgroup.le_normalizer
  let C' : Subgroup N := C.subgroupOf N
  have : C'.Normal := Subgroup.normal_in_normalizer
  let Φ : ↥C' ≃* (CFSGIndex.lie d).Group := (Subgroup.subgroupOfEquivOfLe hCN).trans φ
  let ψ : N →* MulAut (CFSGIndex.lie d).Group :=
    (MulAut.congr Φ).toMonoidHom.comp (MulAut.conjNormal (H := C'))
  let E' : Subgroup N := E.subgroupOf N
  have hψ : ∀ (x : N) (c : C'), ψ x (Φ c) = Φ (MulAut.conjNormal (H := C') x c) := by
    intro x c
    simp [ψ, MulAut.congr_apply]
  have hinj : ∀ x ∈ E', ψ x = 1 → x = 1 := by
    intro x hx h1
    by_contra hne
    have hxY : (x : Y) ≠ 1 := fun h => hne (Subtype.ext h)
    obtain ⟨c, hc, hxc⟩ := hfaith x hx hxY
    apply hxc
    have h2 := congrArg (fun α : MulAut (CFSGIndex.lie d).Group => α (Φ ⟨⟨c, hCN hc⟩, hc⟩)) h1
    simp only [hψ, MulAut.one_apply] at h2
    have h3 := congrArg (fun z : ↥C' => ((z : N) : Y)) (Φ.injective h2)
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h3
    calc (x : Y) * c = (x : Y) * c * (x : Y)⁻¹ * x := by group
      _ = c * x := by rw [h3]
  have hψE : Set.InjOn ψ E' := by
    intro x hx y hy hxy
    have : x * y⁻¹ = 1 := hinj _ (E'.mul_mem hx (E'.inv_mem hy)) (by rw [map_mul, map_inv, hxy,
      mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  have hE''c : Nat.card (E'.map ψ) = p ^ 2 := by
    rw [← hE'c]
    exact Nat.card_congr (Equiv.ofBijective (fun x : E' => (⟨ψ x, x, x.2, rfl⟩ : E'.map ψ))
      ⟨fun a b hab => Subtype.ext (hψE a.2 b.2 (congrArg Subtype.val hab)), fun ⟨y, x, hx, hy⟩ =>
        ⟨⟨x, hx⟩, Subtype.ext hy⟩⟩).symm
  have hgen := hS d p hp hp2 hpd hexc (E'.map ψ)
    (CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hE N) ψ) hE''c
  intro c hc
  have hk : Φ ⟨⟨c, hCN hc⟩, hc⟩ ∈ Subgroup.closure
      {k : (CFSGIndex.lie d).Group | ∃ e ∈ E'.map ψ, e ≠ 1 ∧ e k = k} := by
    rw [hgen]
    exact Subgroup.mem_top _
  let θ : (CFSGIndex.lie d).Group →* Y :=
    N.subtype.comp (C'.subtype.comp Φ.symm.toMonoidHom)
  have hθ : θ (Φ ⟨⟨c, hCN hc⟩, hc⟩) = c := by simp [θ]
  have hmem := Subgroup.mem_map_of_mem θ hk
  rw [MonoidHom.map_closure, hθ] at hmem
  refine Subgroup.closure_mono ?_ hmem
  rintro _ ⟨k, ⟨_, ⟨x, hx, rfl⟩, hne, hfix⟩, rfl⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hne (map_one ψ)
  set c' : ↥C' := Φ.symm k with hc'
  have hk' : k = Φ c' := by simp [hc']
  rw [hk', hψ] at hfix
  have h3 := congrArg (fun z : ↥C' => ((z : N) : Y)) (Φ.injective hfix)
  simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h3
  refine ⟨?_, (x : Y), hx, fun h => hx1 (Subtype.ext h), ?_⟩
  · simp only [θ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    exact c'.2
  · simp only [θ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom]
    rw [← hc']
    calc (x : Y) * ((c' : N) : Y) = (x : Y) * ((c' : N) : Y) * (x : Y)⁻¹ * x := by group
      _ = ((c' : N) : Y) * x := by rw [h3]

end CFSG.LieType.OutStructure
