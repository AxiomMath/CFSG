module

public import CFSG.RankThree.PartOne.KE8F.E8Frame
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveSylowWeyl

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace Four

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


section Frame

theorem exists_frame_canonical (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (L : Type) [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L ℓ] :
    ∃ F : E8P4Frame0 K L ℓ f, F.n = canonicalRep (coxeterSystem .E8) L vElt := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  set n : ModGL .E8 L := canonicalRep (coxeterSystem .E8) L vElt with hn
  have hnm : n ∈ monomialSubgroup .E8 L := canonicalRep_mem_monomialSubgroup L _
  have hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8P4WW :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_gen .E8 K hf L n hnC
  refine ⟨⟨n, hnm, hnW, g0, hg0C, hg0, fun P hP hPC hPF hPperf => ?_,
    e8P4_twistedTorus hnm hnW⟩, rfl⟩
  have := (finite_fixed_subgroup_rational_perfect (K := K) (L := L) 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr P hPC hPF).2.2 P le_rfl hPperf
  rwa [adjEmb_range]

end Frame

section Group

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] {ℓ f : ℕ} [Fact ℓ.Prime]
  [CharP L ℓ]

@[expose] def twistFixed (F : E8P4Frame0 K L ℓ f) : Subgroup (ModGL .E8 L) :=
  ((MulAut.conj F.n).toMonoidHom.comp
    (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))).eqLocus (MonoidHom.id _)

theorem mem_twistFixed {F : E8P4Frame0 K L ℓ f} {x : ModGL .E8 L} :
    x ∈ twistFixed F ↔
      F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * F.n⁻¹ = x :=
  Iff.rfl

structure IsLift (F : E8P4Frame0 K L ℓ f) (m : ModGL .E8 L) : Prop where
  mem : m ∈ monomialSubgroup .E8 L
  maps : MapsRootLines m cElt
  fix : m ∈ twistFixed F

@[expose] def sylowGrp (F : E8P4Frame0 K L ℓ f) (m : ModGL .E8 L) : Subgroup (ModGL .E8 L) :=
  twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ⊔ Subgroup.zpowers m

variable {F : E8P4Frame0 K L ℓ f} {m : ModGL .E8 L}

theorem sylowGrp_le_monomial (hm : IsLift F m) : sylowGrp F m ≤ monomialSubgroup .E8 L :=
  sup_le (fun x hx => torusGroup_le_monomialSubgroup (mem_twistedTorusOf.1 hx).1)
    (Subgroup.zpowers_le.2 hm.mem)

theorem sylowGrp_le_twistFixed (hm : IsLift F m) : sylowGrp F m ≤ twistFixed F :=
  sup_le (fun x hx => mem_twistFixed.2 (mem_twistedTorusOf.1 hx).2)
    (Subgroup.zpowers_le.2 hm.fix)

theorem sylowGrp_le_adjoint (hm : IsLift F m) : sylowGrp F m ≤ adjointGroup .E8 L :=
  (sylowGrp_le_monomial hm).trans monomialSubgroup_le_adjointGroup'

theorem twistedTorus_le_sylowGrp (F : E8P4Frame0 K L ℓ f) (m : ModGL .E8 L) :
    twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ≤ sylowGrp F m :=
  le_sup_left

theorem mem_sylowGrp_self (F : E8P4Frame0 K L ℓ f) (m : ModGL .E8 L) : m ∈ sylowGrp F m :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers m)

@[expose] def sylowRho (hm : IsLift F m) : sylowGrp F m →* WeylGroup .E8 :=
  (weylQuotientHom .E8 L).comp (Subgroup.inclusion (sylowGrp_le_monomial hm))

theorem sylowRho_apply (hm : IsLift F m) (x : sylowGrp F m) :
    sylowRho hm x = weylQuotientHom .E8 L ⟨x, sylowGrp_le_monomial hm x.2⟩ :=
  rfl

theorem sylowRho_eq_one_iff (hm : IsLift F m) (x : sylowGrp F m) :
    sylowRho hm x = 1 ↔
      (x : ModGL .E8 L) ∈
        twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  rw [sylowRho_apply, weylQuotientHom_eq_one_iff]
  exact ⟨fun h => mem_twistedTorusOf.2 ⟨h, mem_twistFixed.1 (sylowGrp_le_twistFixed hm x.2)⟩,
    fun h => (mem_twistedTorusOf.1 h).1⟩

theorem sylowRho_self (hm : IsLift F m) :
    sylowRho hm ⟨m, mem_sylowGrp_self F m⟩ = cElt :=
  weylQuotientHom_eq (g := ⟨m, hm.mem⟩) hm.maps

theorem sylowRho_mem_zpowers (hm : IsLift F m) (x : sylowGrp F m) :
    sylowRho hm x ∈ Subgroup.zpowers cElt := by
  set T0 := twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) with hT0
  have hT : T0.subgroupOf (sylowGrp F m) ≤ (Subgroup.zpowers cElt).comap (sylowRho hm) := by
    intro x hx
    rw [Subgroup.mem_comap, (sylowRho_eq_one_iff hm x).2 hx]
    exact one_mem _
  have hZ : (Subgroup.zpowers m).subgroupOf (sylowGrp F m) ≤
      (Subgroup.zpowers cElt).comap (sylowRho hm) := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hx' : x = (⟨m, mem_sylowGrp_self F m⟩ : sylowGrp F m) ^ k :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [Subgroup.mem_comap, hx', map_zpow, sylowRho_self hm]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hsup : T0.subgroupOf (sylowGrp F m) ⊔ (Subgroup.zpowers m).subgroupOf (sylowGrp F m) =
      ⊤ := by
    have h := Subgroup.subgroupOf_sup (A := T0) (A' := Subgroup.zpowers m)
      (B := sylowGrp F m) le_sup_left le_sup_right
    rw [← h]
    exact Subgroup.subgroupOf_self (sylowGrp F m)
  have hle := sup_le hT hZ
  rw [hsup] at hle
  exact hle (Subgroup.mem_top x)

theorem sylowRho_range (hm : IsLift F m) : (sylowRho hm).range = Subgroup.zpowers cElt := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact sylowRho_mem_zpowers hm x
  · rw [Subgroup.zpowers_le]
    exact ⟨_, sylowRho_self hm⟩

theorem card_sylowRho_range (hm : IsLift F m) : Nat.card (sylowRho hm).range = 5 := by
  rw [sylowRho_range hm]
  exact card_zpowers_cElt

theorem sylowRho_ker (hm : IsLift F m) :
    (sylowRho hm).ker =
      (twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))).subgroupOf
        (sylowGrp F m) := by
  ext x
  rw [MonoidHom.mem_ker, sylowRho_eq_one_iff hm]
  rfl

theorem card_sylowGrp (hm : IsLift F m) :
    Nat.card (sylowGrp F m) =
      5 * Nat.card
        (twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have h1 := Subgroup.card_mul_index (sylowRho hm).ker
  rw [Subgroup.index_ker, card_sylowRho_range hm, sylowRho_ker hm] at h1
  have h2 : Nat.card ((twistedTorusOf F.n
      (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))).subgroupOf (sylowGrp F m)) =
      Nat.card (twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (twistedTorus_le_sylowGrp F m)).toEquiv
  rw [h2] at h1
  omega

theorem card_twistedTorus [IsAlgClosure K L] (F : E8P4Frame0 K L ℓ f) (hK : Nat.card K = ℓ ^ f)
    (hf : 1 ≤ f) :
    Nat.card (twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) =
      (Nat.card K * Nat.card K + 1) ^ 4 := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hinj : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  rw [F.hT, Subgroup.card_map_of_injective hinj]
  exact card_T0 hFr hℓq

end Group

end Four

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
