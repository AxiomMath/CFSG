module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFixedLine
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnPerX
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ZRoot

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalInvolution.Balance

theorem d4_rootChar_longVec {L : Type} [Field L] {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (h2 : b (2 : Fin 4) = 1) (hs : b (0 : Fin 4) * b (1 : Fin 4) * b (3 : Fin 4) = 1)
    (v : Fin TwistTag.D4.tag.rank → ℤ)
    (h01 : v (0 : Fin 4) = v (1 : Fin 4)) (h13 : v (1 : Fin 4) = v (3 : Fin 4)) :
    rootChar b v = 1 := by
  rw [rootChar_d4_apply, h2, one_zpow, mul_one, h01, ← h13, ← mul_zpow, ← mul_zpow, hs, one_zpow]

theorem mem_d4LongA2_iff_hex (α : Fin d4.rank → ℤ) :
    α ∈ d4LongA2 ↔ ∃ j : Fin 6, α = d4Hex j := by
  rw [d4LongA2_mem_iff]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩, ⟨3, rfl⟩, ⟨5, rfl⟩, ⟨4, rfl⟩]
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

section Kernel


theorem d4_rho_fixed_iff_mem_longA2 {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) :
    rho α = α ↔ α ∈ d4LongA2 := by
  rw [mem_d4LongA2_iff_hex]
  obtain ⟨k, hk, rfl⟩ := (isRoot_d4_iff).1 hα
  clear hα
  revert k
  decide +kernel

theorem d4Minus_rootCharKernel {L : Type} [Field L] {A : Lˣ} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1)
    (α : Fin TwistTag.D4.tag.rank → ℤ) :
    α ∈ rootCharKernel (τ := TwistTag.D4.tag) ![A, A, 1, A] ↔ α ∈ d4LongA2 := by
  constructor
  · rintro ⟨hα, h1⟩
    by_contra hnot
    have hρ : rho α ≠ α := fun h => hnot ((d4_rho_fixed_iff_mem_longA2 hα).1 h)
    exact rootChar_z_ne_one A hA3 hA1 hα hρ h1
  · intro hα
    have hroot := d4LongA2_isRoot hα
    refine ⟨hroot, ?_⟩
    exact rootChar_z_fixed A hA3 hroot ((d4_rho_fixed_iff_mem_longA2 hroot).2 hα)

end Kernel

section Coord


theorem d4_rootChar_weyl_single {L : Type} [Field L] {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (h2 : a (2 : Fin 4) = 1) (hs : a (0 : Fin 4) * a (1 : Fin 4) * a (3 : Fin 4) = 1)
    {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) (hw3 : w ^ 3 = 1) (i : Fin TwistTag.D4.tag.rank) :
    rootChar a (w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) = a i := by
  obtain ⟨hx1, hx2⟩ := d4_weyl_order_three_mod_fixed w hw hw3 (Pi.single i 1)
  have hdec : w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      Pi.single i 1 + (w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) - Pi.single i 1) := by
    abel
  have h1 : rootChar a (w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) - Pi.single i 1) = 1 :=
    d4_rootChar_longVec h2 hs _ hx1 hx2
  rw [hdec, rootChar_add, h1, mul_one]
  simpa using rootChar_nsmul_single a i 1

theorem d4Minus_coord {p f : ℕ} [Fact p.Prime] (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p]
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀)
    (n c₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K)
    (hnM : d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hδ : δ = σ ∨ δ = σ⁻¹)
    (he3 : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) ^ 3 = 1)
    (a : Fin TwistTag.D4.tag.rank → Lˣ)
    (hψc : d4MinusPsi σ L g₀ c₀ = rootDiagUnit TwistTag.D4.tag a)
    (h2 : a (2 : Fin 4) = 1) (hs : a (0 : Fin 4) * a (1 : Fin 4) * a (3 : Fin 4) = 1)
    (hfix : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) c₀ = c₀) :
    ∃ B : Lˣ, B ^ 3 = 1 ∧ a = ![B, B, 1, B] := by
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
  have hrange := d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F
  obtain ⟨Q, hQ, hΨ'⟩ := d4MnFL_psi_fieldActor_conj (g₀ := g₀) Fr hcomm hg₀P hδ
  have hΨ : ∀ y, ψ (fieldActor (t := TwistTag.D4) σ δ y) = Q⁻¹ * ψ y * Q := hΨ'
  obtain ⟨w, k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets hnM
  have hxF : trialityOpposition L * twistHom TwistTag.D4 L Fr (ψ n) *
      (trialityOpposition L)⁻¹ = ψ n := ((hrange (ψ n)).1 ⟨n, rfl⟩).2
  have hwrel : w ∈ relWeylTwist TwistTag.D4 := d4MnFL_relWeylTwist_of_fixed Fr hk hxk hxF
  have hxW : MapsRootLines (ψ n) w := hxk ▸ mapsRootLines_mul_canonicalRep hk w
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
  obtain ⟨τ, hτ, hQd⟩ : ∃ τ : Equiv.Perm (Fin TwistTag.D4.tag.rank),
      (τ = TwistTag.D4.perm ∨ τ = TwistTag.D4.perm.symm) ∧
        Q⁻¹ * rootDiagUnit TwistTag.D4.tag a * Q =
          rootDiagUnit TwistTag.D4.tag (fun i => a (τ i)) := by
    rcases hQ with rfl | rfl
    · exact ⟨TwistTag.D4.perm, Or.inl rfl, d4Minus_h90_conj a⟩
    · refine ⟨TwistTag.D4.perm.symm, Or.inr rfl, ?_⟩
      rw [inv_inv, diagramMap_mul_rootDiagUnit, mul_inv_cancel_right]
  have hfixψ : ψ n * (Q⁻¹ * rootDiagUnit TwistTag.D4.tag a * Q) * (ψ n)⁻¹ =
      rootDiagUnit TwistTag.D4.tag a := by
    have h := congrArg ψ hfix
    rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hΨ, hψc] at h
    exact h
  rw [hQd, hxk] at hfixψ
  have hdk : rootDiagUnit TwistTag.D4.tag (fun i => a (τ i)) * k =
      k * rootDiagUnit TwistTag.D4.tag (fun i => a (τ i)) :=
    rootDiagUnit_mul_comm_of_mem_torusGroup _ hk
  have hconj : rootDiagUnit TwistTag.D4.tag a =
      canonicalRep (coxeterSystem TwistTag.D4.tag) L w *
        rootDiagUnit TwistTag.D4.tag (fun i => a (τ i)) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹ := by
    set nw := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hnw
    set db := rootDiagUnit TwistTag.D4.tag (fun i => a (τ i)) with hdb
    set da := rootDiagUnit TwistTag.D4.tag a with hda
    have h1 : k * (nw * db * nw⁻¹) * k⁻¹ = da := by
      calc k * (nw * db * nw⁻¹) * k⁻¹ = k * nw * db * (k * nw)⁻¹ := by group
        _ = da := hfixψ
    have h2 : nw * db * nw⁻¹ = k⁻¹ * da * k := by
      calc nw * db * nw⁻¹ = k⁻¹ * (k * (nw * db * nw⁻¹) * k⁻¹) * k := by group
        _ = k⁻¹ * da * k := by rw [h1]
    have hdak : da * k = k * da := rootDiagUnit_mul_comm_of_mem_torusGroup a hk
    rw [h2, mul_assoc, hdak, inv_mul_cancel_left]
  have hchar := (rootDiagUnit_eq_conj_canonicalRep_iff a (fun i => a (τ i)) w).1 hconj
  have hcoord : ∀ i : Fin TwistTag.D4.tag.rank, a (τ i) = a i := by
    intro i
    have h := hchar (Pi.single i 1)
    rw [d4_rootChar_weyl_single h2 hs hwrel hw3 i] at h
    have h' : rootChar (fun j => a (τ j)) (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) =
        a (τ i) := by
      simpa using rootChar_nsmul_single (fun j => a (τ j)) i 1
    rw [h'] at h
    exact h.symm
  have e0 : TwistTag.D4.perm (0 : Fin 4) = (1 : Fin 4) := perm_i0
  have e1 : TwistTag.D4.perm (1 : Fin 4) = (3 : Fin 4) := perm_i1
  have f0 : TwistTag.D4.perm.symm (0 : Fin 4) = (3 : Fin 4) :=
    (Equiv.symm_apply_eq _).2 perm_i3.symm
  have f1 : TwistTag.D4.perm.symm (1 : Fin 4) = (0 : Fin 4) :=
    (Equiv.symm_apply_eq _).2 perm_i0.symm
  have h10 : a (1 : Fin 4) = a (0 : Fin 4) ∧ a (3 : Fin 4) = a (0 : Fin 4) := by
    rcases hτ with rfl | rfl
    · have c0 := hcoord (0 : Fin 4)
      have c1 := hcoord (1 : Fin 4)
      rw [e0] at c0
      rw [e1] at c1
      exact ⟨c0, c1.trans c0⟩
    · have c0 := hcoord (0 : Fin 4)
      have c1 := hcoord (1 : Fin 4)
      rw [f0] at c0
      rw [f1] at c1
      exact ⟨c1.symm, c0⟩
  refine ⟨a (0 : Fin 4), ?_, ?_⟩
  · rw [h10.1, h10.2] at hs
    rw [pow_three']
    exact hs
  · funext i
    fin_cases i
    · rfl
    · exact h10.1
    · exact h2
    · exact h10.2


theorem d4Minus_coord_mem_zpowers {p f : ℕ} [Fact p.Prime] (hp : p.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p]
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀)
    (v n c₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K) {A : Lˣ}
    (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1)
    (hψv : d4MinusPsi σ L g₀ v = rootDiagUnit TwistTag.D4.tag ![A, A, 1, A])
    (hnM : d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hδ : δ = σ ∨ δ = σ⁻¹)
    (he3 : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) ^ 3 = 1)
    (a : Fin TwistTag.D4.tag.rank → Lˣ)
    (hψc : d4MinusPsi σ L g₀ c₀ = rootDiagUnit TwistTag.D4.tag a)
    (h2 : a (2 : Fin 4) = 1) (hs : a (0 : Fin 4) * a (1 : Fin 4) * a (3 : Fin 4) = 1)
    (hfix : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) c₀ = c₀) :
    c₀ ∈ Subgroup.zpowers v := by
  obtain ⟨B, hB3, hBa⟩ := d4Minus_coord hp hf K hK σ hσ L hg₀ n c₀ δ hnM hδ he3 a hψc h2 hs hfix
  have hprim : IsPrimitiveRoot ((A : Lˣ) : L) 3 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hA3 hA1))
  have hB' : ((B : Lˣ) : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hB3, Units.val_one]
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hB'
  have hBj : B = A ^ j := Units.ext (by rw [Units.val_pow_eq_pow_val, hj])
  refine Subgroup.mem_zpowers_iff.2 ⟨(j : ℤ), ?_⟩
  apply d4MinusPsi_injective g₀
  have hpow := rootDiagUnit_pow (τ := TwistTag.D4.tag) (![A, A, 1, A] : Fin 4 → Lˣ) j
  rw [zpow_natCast, map_pow, hψv, hpow, hψc, hBa, hBj]
  congr 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact one_pow j
  · rfl

end Coord

end CFSG.GH74.GLS.Stage2.Bender.Thm1
