module

public import CFSG.Open.GlaubermanZJCharacteristicMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2
import CFSG.GroupTheory.Gorenstein.MaxCardThompson
import CFSG.GroupTheory.SylowNaturalCharacteristic
import CFSG.GroupTheory.PCore.Transport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
public import CFSG.Open.Catalog

public section

namespace CFSG
namespace Adapters

open scoped Pointwise commutatorElement

section Bridges

variable {G : Type*} [Group G]

theorem leanEval_pCore_eq (p : ℕ) (G : Type*) [Group G] :
    CFSG.Open.pCore p G = CFSG.pCore p G := CFSG.Open.pCore_eq_pCore p G

theorem leanEval_thompsonSubgroup_eq (S : Subgroup G) :
    CFSG.Open.thompsonSubgroup S = CFSG.thompsonSubgroup (G := G) S :=
  rfl

theorem mulAut_smul_eq_map (ψ : MulAut G) (H : Subgroup G) :
    ψ • H = H.map ψ.toMonoidHom := by
  ext x
  simp [Subgroup.pointwise_smul_def]

theorem map_conj_of_normal (H : Subgroup G) [hH : H.Normal] (g : G) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hH.conj_mem y hy g
  · intro hx
    refine ⟨g⁻¹ * x * g, by simpa using hH.conj_mem x hx g⁻¹, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem map_mem_thompsonAbelianSubgroups {H : Type*} [Group H] (e : G ≃* H)
    {P A : Subgroup G} (hA : A ∈ thompsonAbelianSubgroups (G := G) P) :
    A.map e.toMonoidHom ∈ thompsonAbelianSubgroups (G := H) (P.map e.toMonoidHom) := by
  obtain ⟨hAP, hAc, hAm⟩ := hA
  refine ⟨Subgroup.map_mono hAP, inferInstance, ?_⟩
  intro B hB hBc
  have hBP : B.map e.symm.toMonoidHom ≤ P := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hB hy
    simpa using hz
  calc
    Nat.card B = Nat.card (B.map e.symm.toMonoidHom) :=
      (Subgroup.card_map_of_injective (K := B) e.symm.injective).symm
    _ ≤ Nat.card A := hAm _ hBP inferInstance
    _ = Nat.card (A.map e.toMonoidHom) :=
      (Subgroup.card_map_of_injective (K := A) e.injective).symm

theorem map_symm_map {H : Type*} [Group H] (e : G ≃* H) (K : Subgroup G) :
    (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩

theorem thompsonSubgroup_map_mulEquiv {H : Type*} [Group H]
    (P : Subgroup G) (e : G ≃* H) :
    (thompsonSubgroup (G := G) P).map e.toMonoidHom =
      thompsonSubgroup (G := H) (P.map e.toMonoidHom) :=
  map_thompsonSubgroup_of_injective e.toMonoidHom P (e.injective.comp P.subtype_injective)

theorem thompsonCenter_map_mulEquiv {H : Type*} [Group H]
    (P : Subgroup G) (e : G ≃* H) :
    (thompsonCenter (G := G) P).map e.toMonoidHom =
      thompsonCenter (G := H) (P.map e.toMonoidHom) :=
  map_thompsonCenter_of_injective e.toMonoidHom P (e.injective.comp P.subtype_injective)

theorem thompsonCenter_characteristic_of_normal [Finite G] (p : ℕ) [Fact p.Prime]
    (S : Sylow p G) (hN : (thompsonCenter (G := G) (S : Subgroup G)).Normal) :
    (thompsonCenter (G := G) (S : Subgroup G)).Characteristic :=
  have := hN
  characteristic_of_normal_of_map_mulEquiv (fun P => thompsonCenter (G := G) P)
    (fun φ P => thompsonCenter_map_mulEquiv P φ) S

end Bridges

theorem glauberman_zj_characteristic
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hcharp : Subgroup.centralizer (CFSG.Open.pCore p G : Set G) ≤
      CFSG.Open.pCore p G)
    (S : Sylow p G)
    (hstable : ∀ (P : Subgroup G) [P.Normal], IsPGroup p P →
      CFSG.Open.StatedConjPStable p P) :
    ((Subgroup.center (CFSG.Open.thompsonSubgroup (S : Subgroup G))).map
        (CFSG.Open.thompsonSubgroup (S : Subgroup G)).subtype).Characteristic := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  rw [leanEval_thompsonSubgroup_eq, ← centerIn_eq_map_center]
  change (thompsonCenter (G := G) (S : Subgroup G)).Characteristic
  have hbot : pPrimeCore p G = ⊥ := by
    have hle : pPrimeCore p G ≤ pCore p G :=
      (pPrimeCore_le_centralizer_of_normal_pgroup (G := G) p (pCore p G)
        (pCore_isPGroup (G := G) (p := p))).trans hcharp
    obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (G := G) (p := p))
    have hcoprime : Nat.Coprime (Nat.card (pCore p G)) (Nat.card (pPrimeCore p G)) := by
      rw [hcard]
      exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
    have hinf : pCore p G ⊓ pPrimeCore p G = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hcoprime).eq_bot
    rwa [inf_eq_right.mpr hle] at hinf
  by_cases hOp : pCore p G = ⊥
  ·
    have hall : ∀ x : G, x = 1 := by
      intro x
      have hx : x ∈ Subgroup.centralizer (pCore p G : Set G) := by
        rw [hOp]
        exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
          simp [hh]
      simpa [hOp] using hcharp hx
    have hZ : thompsonCenter (G := G) (S : Subgroup G) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 fun x _ => hall x
    rw [hZ]
    infer_instance
  have hpodd : p ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  have hOp'p : Op_p'p p G = pCore p G := Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G) (p := p) hbot
  have hconstrained : PConstrainedGroup (G := G) p := by
    intro Q _ hQ
    rw [hOp'p, hbot, bot_sup_eq] at hQ
    rw [hOp'p, hQ]
    exact hcharp
  have hstable' : PStableGroup' (G := G) p := by
    intro Q A hQn hQp _ _ hcomm
    rw [hbot, bot_sup_eq] at hQn
    have := hQn
    have hst := hstable Q hQp
    have hNtop : Subgroup.normalizer (Q : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hQn
    dsimp only
    rw [Subgroup.map_le_iff_le_comap]
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    have hquad : ∀ u ∈ Q, (u⁻¹ * (a : G)⁻¹ * u * a)⁻¹ * (a : G)⁻¹ *
        (u⁻¹ * (a : G)⁻¹ * u * a) * a = 1 := by
      intro u hu
      have hmem : ⁅(⁅u⁻¹, (a : G)⁻¹⁆)⁻¹, (a : G)⁻¹⁆ ∈ ⁅⁅Q, A⁆, A⁆ :=
        Subgroup.commutator_mem_commutator
          (inv_mem (Subgroup.commutator_mem_commutator (inv_mem hu) (inv_mem ha)))
          (inv_mem ha)
      rw [hcomm, Subgroup.mem_bot] at hmem
      simpa only [commutatorElement_def, inv_inv] using hmem
    have hx := hst (a : G) hquad
    simp only [CFSG.Open.StatedConjActionPCore, Subgroup.mem_comap] at hx
    let N : Subgroup G := Subgroup.normalizer (Q : Set G)
    let C : Subgroup G := Subgroup.centralizer (Q : Set G)
    have hCN : C ≤ N := by
      simpa using (centralizer_le_normalizer (G := G) Q)
    have : (C.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (H := C) (K := N) hCN).2
        (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (X := G) Q)
    let g0 : G →* N := (MonoidHom.id G).codRestrict N (fun g => by
      show g ∈ Subgroup.normalizer (Q : Set G)
      rw [hNtop]
      exact Subgroup.mem_top g)
    have hker : C ≤ (C.subgroupOf N).comap g0 := by
      intro c hc
      simpa [Subgroup.mem_subgroupOf, g0] using hc
    let f : G ⧸ C →* N ⧸ C.subgroupOf N := QuotientGroup.map C (C.subgroupOf N) g0 hker
    have hg0 : Function.Surjective g0 := by
      intro n
      exact ⟨n, Subtype.ext rfl⟩
    have hf : Function.Surjective f :=
      QuotientGroup.map_surjective_of_surjective (N := C) (C.subgroupOf N) g0
        ((QuotientGroup.mk'_surjective _).comp hg0) hker
    have hmap : (pCore p (G ⧸ C)).map f ≤ pCore p (N ⧸ C.subgroupOf N) :=
      le_sSup ⟨Subgroup.Normal.map (H := pCore p (G ⧸ C))
          (pCore_normal (G := G ⧸ C) (p := p)) f hf,
        IsPGroup.map (p := p) (H := pCore p (G ⧸ C)) (pCore_isPGroup (G := G ⧸ C) (p := p)) f⟩
    exact hmap ⟨(a : G), hx, rfl⟩
  have hnormal := G_theorem_8_2_11 (G := G) (p := p) hpodd hOp hconstrained hstable' S
  rw [hbot, sup_bot_eq] at hnormal
  exact thompsonCenter_characteristic_of_normal p S hnormal

end Adapters
end CFSG
