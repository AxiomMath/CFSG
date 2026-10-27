module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4FixedLine
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MinusStmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnH90
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnLift

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut

theorem d4MnFL_diagramMap_inv_rootVec_perm {L : Type} [Field L]
    {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : IsRoot TwistTag.D4.tag γ) :
    ((diagramMap TwistTag.D4 L)⁻¹ : ModGL TwistTag.D4.tag L).val
        (rootVec TwistTag.D4.tag L (permLattice TwistTag.D4.perm γ)) =
      rootVec TwistTag.D4.tag L γ := by
  rw [← diagramMap_rootVec TwistTag.D4 L γ hγ]
  have h2 : (((diagramMap TwistTag.D4 L)⁻¹ * diagramMap TwistTag.D4 L : ModGL TwistTag.D4.tag L) :
      Module.End L (RootModule TwistTag.D4.tag L)) (rootVec TwistTag.D4.tag L γ) =
      rootVec TwistTag.D4.tag L γ := by
    rw [inv_mul_cancel]
    rfl
  exact h2

section Torus

theorem d4MnFL_conj_Q_rootDiagUnit {L : Type} [Field L] {Q : ModGL TwistTag.D4.tag L}
    (hQ : Q = diagramMap TwistTag.D4 L ∨ Q = (diagramMap TwistTag.D4 L)⁻¹)
    {b : Fin TwistTag.D4.tag.rank → Lˣ} (hb : ∀ i, b (TwistTag.D4.perm i) = b i) :
    Q⁻¹ * rootDiagUnit TwistTag.D4.tag b * Q = rootDiagUnit TwistTag.D4.tag b := by
  rcases hQ with rfl | rfl
  · rw [d4Minus_h90_conj]
    exact congrArg _ (funext hb)
  · rw [inv_inv, mul_inv_eq_iff_eq_mul, diagramMap_mul_rootDiagUnit]
    refine congrArg (· * diagramMap TwistTag.D4 L) (congrArg _ (funext fun i => ?_))
    rw [← hb (TwistTag.D4.perm.symm i), Equiv.apply_symm_apply]

end Torus

section Weyl

theorem d4MnFL_mapsRootLines_conj_diagramMap {L : Type} [Field L] {g : ModGL TwistTag.D4.tag L}
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
    (hg : MapsRootLines g w) :
    MapsRootLines (diagramMap TwistTag.D4 L * g * (diagramMap TwistTag.D4 L)⁻¹) w := by
  intro α hα
  have hβ : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm.symm α) :=
    hα.permLattice (cartan_perm_symm TwistTag.D4.cartan_perm)
  obtain ⟨c, hc⟩ := hg _ hβ
  refine ⟨c, ?_⟩
  have h1 : ((diagramMap TwistTag.D4 L)⁻¹ : ModGL TwistTag.D4.tag L).val
      (rootVec TwistTag.D4.tag L α) =
      rootVec TwistTag.D4.tag L (permLattice TwistTag.D4.perm.symm α) := by
    have := d4MnFL_diagramMap_inv_rootVec_perm (L := L) hβ
    rwa [LieType.Chevalley.permLattice_permLattice_symm] at this
  have h2 : permLattice TwistTag.D4.perm (w • permLattice TwistTag.D4.perm.symm α) = w • α := by
    rw [← (mem_relWeylTwist_iff_smul TwistTag.D4).1 hw,
      LieType.Chevalley.permLattice_permLattice_symm]
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, h1, hc, map_smul,
    diagramMap_rootVec _ _ _ (IsRoot.smul hβ w), h2]

theorem d4MnFL_mapsRootLines_conj_diagramMap_inv {L : Type} [Field L]
    {g : ModGL TwistTag.D4.tag L} {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) (hg : MapsRootLines g w) :
    MapsRootLines ((diagramMap TwistTag.D4 L)⁻¹ * g * diagramMap TwistTag.D4 L) w := by
  intro α hα
  have hβ : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm α) :=
    hα.permLattice TwistTag.D4.cartan_perm
  obtain ⟨c, hc⟩ := hg _ hβ
  refine ⟨c, ?_⟩
  have h2 : w • permLattice TwistTag.D4.perm α = permLattice TwistTag.D4.perm (w • α) :=
    (mem_relWeylTwist_iff_smul TwistTag.D4).1 hw α
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    diagramMap_rootVec _ _ _ hα, hc, map_smul, h2,
    d4MnFL_diagramMap_inv_rootVec_perm (IsRoot.smul hα w)]

theorem d4MnFL_mapsRootLines_conj_Q {L : Type} [Field L] {Q g : ModGL TwistTag.D4.tag L}
    (hQ : Q = diagramMap TwistTag.D4 L ∨ Q = (diagramMap TwistTag.D4 L)⁻¹)
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
    (hg : MapsRootLines g w) : MapsRootLines (Q⁻¹ * g * Q) w := by
  rcases hQ with rfl | rfl
  · exact d4MnFL_mapsRootLines_conj_diagramMap_inv hw hg
  · rw [inv_inv]
    exact d4MnFL_mapsRootLines_conj_diagramMap hw hg

theorem d4MnFL_relWeylTwist_of_fixed {L : Type} [Field L] (Fr : L →+* L)
    {x k : ModGL TwistTag.D4.tag L} {w : WeylGroup TwistTag.D4.tag}
    (hk : k ∈ torusGroup TwistTag.D4.tag L)
    (hx : x = k * canonicalRep (coxeterSystem TwistTag.D4.tag) L w)
    (hxF : trialityOpposition L * twistHom TwistTag.D4 L Fr x * (trialityOpposition L)⁻¹ = x) :
    w ∈ relWeylTwist TwistTag.D4 := by
  have hFx : MapsRootLines (twistHom TwistTag.D4 L Fr x) (weylTwist TwistTag.D4 w) := by
    rw [hx, map_mul, twistHom_canonicalRep]
    exact mapsRootLines_mul_canonicalRep (twistHom_mem_torusGroup TwistTag.D4 L Fr hk) _
  have hzx := ((mapsRootLines_trialityOpposition (K := L)).mul hFx).mul
    (mapsRootLines_trialityOpposition (K := L)).inv
  rw [d4Minus_oppositionWeyl_comm, mul_inv_cancel_right, hxF] at hzx
  have hxw : MapsRootLines x w := hx ▸ mapsRootLines_mul_canonicalRep hk w
  exact (mem_relWeylTwist TwistTag.D4).2 (hzx.unique hxw)

theorem d4MnFL_weyl_cube {L : Type} [Field L] {Q x : ModGL TwistTag.D4.tag L}
    (hQ : Q = diagramMap TwistTag.D4 L ∨ Q = (diagramMap TwistTag.D4 L)⁻¹)
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4) (hx : MapsRootLines x w)
    (hcyc : x * (Q⁻¹ * x * Q) * (Q⁻¹ * (Q⁻¹ * x * Q) * Q) = 1) : w ^ 3 = 1 := by
  have h1 := d4MnFL_mapsRootLines_conj_Q hQ hw hx
  have h2 := d4MnFL_mapsRootLines_conj_Q hQ hw h1
  have h := (hx.mul h1).mul h2
  rw [hcyc] at h
  rw [pow_three']
  exact h.unique mapsRootLines_one

end Weyl

section Main

theorem d4MnFL_psi_fieldActor_conj {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {L : Type} [Field L] [Algebra K L] {g₀ : ModGL TwistTag.D4.tag L} (Fr : L →+* L)
    (hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L))
    (hP : diagramMap TwistTag.D4 L * g₀ = g₀ * diagramMap TwistTag.D4 L) {δ : K ≃+* K}
    (hδ : δ = σ ∨ δ = σ⁻¹) :
    ∃ Q : ModGL TwistTag.D4.tag L,
      (Q = diagramMap TwistTag.D4 L ∨ Q = (diagramMap TwistTag.D4 L)⁻¹) ∧
      ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        d4MinusPsi σ L g₀ (fieldActor (t := TwistTag.D4) σ δ y) =
          Q⁻¹ * d4MinusPsi σ L g₀ y * Q := by
  rcases hδ with rfl | rfl
  · exact ⟨diagramMap TwistTag.D4 L, Or.inl rfl, fun y => d4MinusPsi_fieldActor Fr hcomm hP y⟩
  · refine ⟨(diagramMap TwistTag.D4 L)⁻¹, Or.inr rfl, fun y => ?_⟩
    have h2 : fieldActor (t := TwistTag.D4) σ σ⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹ :=
      map_inv (fieldActorHom (t := TwistTag.D4) σ) σ
    have h := d4MinusPsi_fieldActor Fr hcomm hP ((fieldActor (t := TwistTag.D4) σ σ)⁻¹ y)
    rw [MulAut.apply_inv_self] at h
    rw [h2, inv_inv]
    calc d4MinusPsi σ L g₀ ((fieldActor (t := TwistTag.D4) σ σ)⁻¹ y)
        = diagramMap TwistTag.D4 L * ((diagramMap TwistTag.D4 L)⁻¹ *
            d4MinusPsi σ L g₀ ((fieldActor (t := TwistTag.D4) σ σ)⁻¹ y) *
            diagramMap TwistTag.D4 L) * (diagramMap TwistTag.D4 L)⁻¹ := by group
      _ = diagramMap TwistTag.D4 L * d4MinusPsi σ L g₀ y * (diagramMap TwistTag.D4 L)⁻¹ := by
          rw [← h]

theorem d4Minus_fixed_line {p f : ℕ} [Fact p.Prime] (hp : p.Prime) (_hp2 : p ≠ 2)
    (_hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p]
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀)
    (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K)
    (hv : d4MinusPsi σ L g₀ v ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L p f)))
    (hv1 : v ≠ 1) (hv3 : v ^ 3 = 1)
    (hnM : d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnT : d4MinusPsi σ L g₀ n ∉ torusGroup TwistTag.D4.tag L)
    (hδ : δ = σ ∨ δ = σ⁻¹)
    (he3 : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) ^ 3 = 1)
    (hfix : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) v = v) :
    ∃ A : Lˣ, A ^ 3 = 1 ∧ A ≠ 1 ∧
      d4MinusPsi σ L g₀ v = rootDiagUnit TwistTag.D4.tag ![A, A, 1, A] := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  obtain ⟨hg₀C, hg₀P, hg₀F⟩ := hg₀
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  set ψ := d4MinusPsi σ L g₀ with hψdef
  have hinj : Function.Injective ψ := d4MinusPsi_injective g₀
  have hrange := d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F
  rw [d4Q_twistedTorus Fr] at hv
  obtain ⟨b, hb, hbv⟩ := Subgroup.mem_map.1 hv
  have hψv : ψ v = rootDiagUnit TwistTag.D4.tag b := hbv.symm
  have hcube : ∀ i, b i ^ 3 = 1 := by
    intro i
    have h : ψ (v ^ 3) = 1 := by rw [hv3, map_one]
    rw [map_pow, hψv, rootDiagUnit_pow, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)] at h
    have := congrFun (rootDiagUnit_injective h) i
    simpa using this
  obtain ⟨hb1, hb3⟩ := d4Q_eq_of_pow_eq_one hFr (p := 3) (by omega) hb hcube
  have h10 : b (1 : Fin 4) = b (0 : Fin 4) := hb1
  have h30 : b (3 : Fin 4) = b (0 : Fin 4) := hb3
  have hbρ : ∀ i, b (TwistTag.D4.perm i) = b i := by
    intro i
    rcases fin_cases i with rfl | rfl | rfl | rfl
    · rw [perm_i0]
      exact hb1
    · rw [perm_i1]
      exact hb3.trans hb1.symm
    · rw [perm_i2]
    · rw [perm_i3]
      exact hb3.symm
  obtain ⟨Q, hQ, hΨ'⟩ := d4MnFL_psi_fieldActor_conj (g₀ := g₀) Fr hcomm hg₀P hδ
  have hΨ : ∀ y, ψ (fieldActor (t := TwistTag.D4) σ δ y) = Q⁻¹ * ψ y * Q := hΨ'
  have hΦv : fieldActor (t := TwistTag.D4) σ δ v = v := by
    apply hinj
    rw [hΨ, hψv, d4MnFL_conj_Q_rootDiagUnit hQ hbρ]
  have hnv : n * v * n⁻¹ = v := by
    rw [MulAut.mul_apply, hΦv, MulAut.conj_apply] at hfix
    exact hfix
  have hxv : ψ n * rootDiagUnit TwistTag.D4.tag b * (ψ n)⁻¹ = rootDiagUnit TwistTag.D4.tag b := by
    rw [← hψv, ← map_inv, ← map_mul, ← map_mul, hnv]
  obtain ⟨w, k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets hnM
  have hxF : trialityOpposition L * twistHom TwistTag.D4 L Fr (ψ n) *
      (trialityOpposition L)⁻¹ = ψ n := ((hrange (ψ n)).1 ⟨n, rfl⟩).2
  have hwrel : w ∈ relWeylTwist TwistTag.D4 := d4MnFL_relWeylTwist_of_fixed Fr hk hxk hxF
  have hxW : MapsRootLines (ψ n) w := hxk ▸ mapsRootLines_mul_canonicalRep hk w
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hnT
    rw [hxk, canonicalRep_one, mul_one]
    exact hk
  have hΦ3 : (fieldActor (t := TwistTag.D4) σ δ) ^ 3 = 1 := by
    have h := d4_fieldActor_pow_three K hK σ hσ
    rcases hδ with h' | h'
    · rw [h']
      exact h
    · have h2 : fieldActor (t := TwistTag.D4) σ σ⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹ :=
        map_inv (fieldActorHom (t := TwistTag.D4) σ) σ
      rw [h', h2, inv_pow, h, inv_one]
  have hN := normSeq_eq_one_of_pow_eq_one hZ hΦ3 he3
  rw [normSeq_three] at hN
  have hcyc : ψ n * (Q⁻¹ * ψ n * Q) * (Q⁻¹ * (Q⁻¹ * ψ n * Q) * Q) = 1 := by
    have h := congrArg ψ hN
    simpa only [map_mul, hΨ, map_one] using h
  have hw3 : w ^ 3 = 1 := d4MnFL_weyl_cube hQ hwrel hxW hcyc
  have hdbk : rootDiagUnit TwistTag.D4.tag b * k = k * rootDiagUnit TwistTag.D4.tag b :=
    rootDiagUnit_mul_comm_of_mem_torusGroup b hk
  have hconj : rootDiagUnit TwistTag.D4.tag b =
      canonicalRep (coxeterSystem TwistTag.D4.tag) L w * rootDiagUnit TwistTag.D4.tag b *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹ := by
    set nw := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hnw
    set db := rootDiagUnit TwistTag.D4.tag b with hdb
    rw [hxk] at hxv
    have h1 : k * (nw * db * nw⁻¹) * k⁻¹ = db := by
      calc k * (nw * db * nw⁻¹) * k⁻¹ = k * nw * db * (k * nw)⁻¹ := by group
        _ = db := hxv
    have h2 : nw * db * nw⁻¹ = k⁻¹ * db * k := by
      calc nw * db * nw⁻¹ = k⁻¹ * (k * (nw * db * nw⁻¹) * k⁻¹) * k := by group
        _ = k⁻¹ * db * k := by rw [h1]
    rw [h2, mul_assoc, hdbk, inv_mul_cancel_left]
  have hchar : ∀ u, rootChar b (w • u) = rootChar b u :=
    (rootDiagUnit_eq_conj_canonicalRep_iff b b w).1 hconj
  have hb2 : b (2 : Fin 4) = 1 := by
    have h0 := hchar (d4LatVec 1 0 0 0)
    rcases d4_order_three_smul_single_zero hwrel hw1 hw3 with hk | hk
    · rw [hk, rootChar_d4_apply, rootChar_d4_apply] at h0
      simp [d4LatVec] at h0
      exact h0
    · rw [hk, rootChar_d4_apply, rootChar_d4_apply] at h0
      simp [d4LatVec] at h0
      rw [h10, h30] at h0
      have h2 : (b (2 : Fin 4))⁻¹ = 1 := by
        calc (b (2 : Fin 4))⁻¹ = b (0 : Fin 4) * ((b (0 : Fin 4))⁻¹ * (b (2 : Fin 4))⁻¹ *
              (b (0 : Fin 4))⁻¹) * b (0 : Fin 4) := by group
          _ = b (0 : Fin 4) * b (0 : Fin 4) * b (0 : Fin 4) := by rw [h0]
          _ = b (0 : Fin 4) ^ 3 := (pow_three' _).symm
          _ = 1 := hcube _
      exact inv_eq_one.1 h2
  have hA1 : b (0 : Fin 4) ≠ 1 := by
    intro h0
    apply hv1
    apply hinj
    have h1 : b = 1 := by
      funext i
      fin_cases i
      · exact h0
      · exact h10.trans h0
      · exact hb2
      · exact h30.trans h0
    rw [hψv, h1, rootDiagUnit_one, map_one]
  refine ⟨b (0 : Fin 4), hcube _, hA1, ?_⟩
  rw [hψv]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact h10
  · exact hb2
  · exact h30

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
