module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.Open.LocalVocabulary

public noncomputable section

namespace CFSG.FullDefectCanonical

open scoped Classical Pointwise

universe u

variable {G : Type u} [Group G] {p : ℕ} [hp : Fact p.Prime]

@[expose] def sylowCenter (S : Sylow p G) : Subgroup G :=
  (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype

omit hp in
theorem sylowCenter_le_sylow (S : Sylow p G) : sylowCenter S ≤ (S : Subgroup G) :=
  Subgroup.map_subtype_le _

omit hp in
theorem sylowCenter_le_centralizer (S : Sylow p G) :
    sylowCenter S ≤ Subgroup.centralizer (S : Set G) := by
  rintro z ⟨a, ha, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha ⟨s, hs⟩)

omit hp in
theorem mem_sylowCenter_iff (S : Sylow p G) (g : G) :
    g ∈ sylowCenter S ↔ g ∈ (S : Subgroup G) ∧ g ∈ Subgroup.centralizer (S : Set G) := by
  constructor
  · intro hg
    exact ⟨sylowCenter_le_sylow S hg, sylowCenter_le_centralizer S hg⟩
  · rintro ⟨hgS, hgC⟩
    refine ⟨⟨g, hgS⟩, ?_, rfl⟩
    apply (Subgroup.mem_center_iff (G := (S : Subgroup G))).mpr
    intro s
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hgC s.val s.property

@[expose] def sylowCentralizerCenter (S : Sylow p G) :
    Sylow p (Subgroup.centralizer (S : Set G)) := by
  let C := Subgroup.centralizer (S : Set G)
  let Z := (sylowCenter S).subgroupOf C
  have hZp : IsPGroup p Z :=
    (S.isPGroup'.to_le (sylowCenter_le_sylow S)).comap_subtype
  refine { Z with isPGroup' := hZp, is_maximal' := ?_ }
  intro Q hQ hZQ
  let P := Q.map C.subtype
  have hPp : IsPGroup p P := hQ.map C.subtype
  have hPN : P ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.map_subtype_le Q).trans (Subgroup.centralizer_le_normalizer _)
  have hjoin := S.isPGroup'.to_sup_of_normal_left' hPp hPN
  have hPS : P ≤ (S : Subgroup G) := by
    have hmax := S.is_maximal' hjoin le_sup_left
    exact le_sup_right.trans_eq hmax
  apply le_antisymm _ hZQ
  intro q hq
  have hqP : (q : G) ∈ P := Subgroup.mem_map_of_mem C.subtype hq
  exact Subgroup.mem_subgroupOf.mpr ((mem_sylowCenter_iff S q).mpr ⟨hPS hqP, q.2⟩)

@[expose] def centralizerCore (S : Sylow p G) : Subgroup G :=
  (CFSG.pPrimeCore p (Subgroup.centralizer (S : Set G))).map
    (Subgroup.centralizer (S : Set G)).subtype

omit hp in
theorem centralizerCore_le_centralizer (S : Sylow p G) :
    centralizerCore S ≤ Subgroup.centralizer (S : Set G) :=
  Subgroup.map_subtype_le _

theorem le_normal_of_pGroup_quotient [Finite G] (W N : Subgroup G) [N.Normal]
    (hW : Nat.Coprime p (Nat.card W)) (hquot : IsPGroup p (G ⧸ N)) : W ≤ N := by
  let f := QuotientGroup.mk' N
  let A := W.map f
  have hA : Nat.Coprime p (Nat.card A) :=
    Nat.Coprime.coprime_dvd_right (W.card_map_dvd f) hW
  have hAp : IsPGroup p A := hquot.to_subgroup A
  have hAcard : Nat.card A = 1 := by
    rcases hAp.card_eq_or_dvd with hone | hdvd
    · exact hone
    · exact absurd hdvd ((Nat.Prime.coprime_iff_not_dvd hp.out).mp hA)
  have hAbot : A = ⊥ := (Subgroup.eq_bot_iff_card A).mpr hAcard
  intro w hw
  apply (QuotientGroup.eq_one_iff w).mp
  apply Subgroup.mem_bot.mp
  rw [← hAbot]
  exact Subgroup.mem_map_of_mem f hw

theorem eq_pPrimeCore_of_pGroup_quotient [Finite G] (N : Subgroup G) [N.Normal]
    (hN : Nat.Coprime p (Nat.card N)) (hquot : IsPGroup p (G ⧸ N)) :
    N = CFSG.pPrimeCore p G := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, hN⟩
  · exact le_normal_of_pGroup_quotient (CFSG.pPrimeCore p G) N
      (CFSG.pPrimeCore_coprime_card (p := p) (G := G)) hquot

theorem pPrimeCore_isComplement_of_central [Finite G] (P : Sylow p G)
    (hP : (P : Subgroup G) ≤ Subgroup.center G) :
    (CFSG.pPrimeCore p G).IsComplement' (P : Subgroup G) := by
  have hNC : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_center_iff.mp (hP hx) g).symm
  let N := (MonoidHom.transferSylow P hNC).ker
  have hcomp : N.IsComplement' (P : Subgroup G) :=
    MonoidHom.ker_transferSylow_isComplement' P hNC
  have hN : Nat.Coprime p (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).mpr (MonoidHom.not_dvd_card_ker_transferSylow P hNC)
  have hquot : IsPGroup p (G ⧸ N) :=
    P.isPGroup'.of_equiv hcomp.symm.QuotientMulEquiv.symm
  exact eq_pPrimeCore_of_pGroup_quotient N hN hquot ▸ hcomp

omit hp in
theorem sylowCentralizerCenter_le_center (S : Sylow p G) :
    ((sylowCentralizerCenter S : Subgroup (Subgroup.centralizer (S : Set G)))) ≤
      Subgroup.center (Subgroup.centralizer (S : Set G)) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hzS : (z : G) ∈ (S : Subgroup G) :=
    sylowCenter_le_sylow S (Subgroup.mem_subgroupOf.mp hz)
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp g.2 z hzS).symm

theorem core_isComplement [Finite G] (S : Sylow p G) :
    (CFSG.pPrimeCore p (Subgroup.centralizer (S : Set G))).IsComplement'
      ((sylowCentralizerCenter S : Subgroup (Subgroup.centralizer (S : Set G)))) :=
  pPrimeCore_isComplement_of_central (sylowCentralizerCenter S)
    (sylowCentralizerCenter_le_center S)

theorem coprime_card_centralizerCore [Finite G] (S : Sylow p G) :
    Nat.Coprime p (Nat.card (centralizerCore S)) := by
  rw [centralizerCore, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact CFSG.pPrimeCore_coprime_card (p := p) (G := Subgroup.centralizer (S : Set G))

theorem sylow_inf_centralizerCore [Finite G] (S : Sylow p G) :
    (S : Subgroup G) ⊓ centralizerCore S = ⊥ := by
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [Sylow.card_eq_multiplicity]
  exact Nat.Coprime.pow_left _ (coprime_card_centralizerCore S)

theorem mem_sup_centralizer_iff [Finite G] (S : Sylow p G) (g : G) :
    g ∈ (S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G) ↔
      ∃ v ∈ (S : Subgroup G), ∃ x ∈ centralizerCore S, g = v * x := by
  constructor
  · intro hg
    have hset := Subgroup.coe_mul_of_right_le_normalizer_left (S : Subgroup G)
      (Subgroup.centralizer (S : Set G)) (Subgroup.centralizer_le_normalizer _)
    have hg' : g ∈ ((S : Subgroup G) : Set G) * (Subgroup.centralizer (S : Set G) : Set G) := by
      rw [← hset]; exact hg
    obtain ⟨v, hv, c, hc, rfl⟩ := hg'
    obtain ⟨⟨x, a⟩, hxa⟩ := (core_isComplement S).existsUnique ⟨c, hc⟩ |>.exists
    have hcx : (c : G) = (x : G) * (a : G) := by
      have := congrArg Subtype.val hxa
      simpa using this.symm
    have haS : ((a : Subgroup.centralizer (S : Set G)) : G) ∈ (S : Subgroup G) :=
      sylowCenter_le_sylow S (Subgroup.mem_subgroupOf.mp a.2)
    have hxa' : ((x : Subgroup.centralizer (S : Set G)) : G) * a = a * x :=
      (Subgroup.mem_centralizer_iff.mp (x : Subgroup.centralizer (S : Set G)).2 a haS).symm
    refine ⟨v * a, S.mul_mem hv haS, x, ⟨x, x.2, rfl⟩, ?_⟩
    rw [hcx, hxa', mul_assoc]
  · rintro ⟨v, hv, x, hx, rfl⟩
    exact Subgroup.mul_mem_sup hv (centralizerCore_le_centralizer S hx)

@[expose] def productEquiv [Finite G] (S : Sylow p G) :
    ↥(S : Subgroup G) × ↥(centralizerCore S) ≃*
      ((S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G) : Subgroup G) := by
  let f : ↥(S : Subgroup G) × ↥(centralizerCore S) →*
      ((S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G) : Subgroup G) := {
    toFun x := ⟨(x.1 : G) * (x.2 : G),
      Subgroup.mul_mem_sup x.1.2 (centralizerCore_le_centralizer S x.2.2)⟩
    map_one' := by ext; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      have hc := Subgroup.mem_centralizer_iff.mp (centralizerCore_le_centralizer S x.2.2)
        (y.1 : G) y.1.2
      change ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
        ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
      calc
        _ = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by group
        _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by rw [hc]
        _ = _ := by group }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    change (x.1 : G) * x.2 = y.1 * y.2 at h
    have hmem : ((y.1 : G))⁻¹ * x.1 ∈ (S : Subgroup G) ⊓ centralizerCore S := by
      refine ⟨S.mul_mem (S.inv_mem y.1.2) x.1.2, ?_⟩
      have : ((y.1 : G))⁻¹ * x.1 = y.2 * (x.2 : G)⁻¹ := by
        calc ((y.1 : G))⁻¹ * x.1 = (y.1 : G)⁻¹ * (x.1 * x.2) * (x.2 : G)⁻¹ := by group
          _ = (y.1 : G)⁻¹ * (y.1 * y.2) * (x.2 : G)⁻¹ := by rw [h]
          _ = y.2 * (x.2 : G)⁻¹ := by group
      rw [this]
      exact (centralizerCore S).mul_mem y.2.2 ((centralizerCore S).inv_mem x.2.2)
    rw [sylow_inf_centralizerCore S, Subgroup.mem_bot] at hmem
    have h1 : (x.1 : G) = y.1 := by
      calc (x.1 : G) = y.1 * ((y.1 : G)⁻¹ * x.1) := by group
        _ = y.1 := by rw [hmem, mul_one]
    have h2 : (x.2 : G) = y.2 := by
      rw [h1] at h
      exact mul_left_cancel h
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · rintro ⟨g, hg⟩
    obtain ⟨v, hv, x, hx, rfl⟩ := (mem_sup_centralizer_iff S g).mp hg
    exact ⟨(⟨v, hv⟩, ⟨x, hx⟩), rfl⟩

@[simp] theorem productEquiv_apply [Finite G] (S : Sylow p G)
    (x : ↥(S : Subgroup G) × ↥(centralizerCore S)) :
    ((productEquiv S x : ((S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G) : Subgroup G)) :
      G) = (x.1 : G) * (x.2 : G) := rfl

end CFSG.FullDefectCanonical
