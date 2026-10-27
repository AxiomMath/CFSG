module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactE9
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactU33
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33Elementary
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrSmall

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.QuasithinUnique

section AutOrder

open CFSG.AGLEmbedding.ParabAutIrr CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem card_mulAut_psu33 {Y : Type} [Group Y] [Finite Y]
    (h : CFSG.Open.StatedClassicalModel Y .PSU 3 3 1) (hcard : Nat.card Y = 6048)
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) :
    Nat.card (MulAut Y) = 12096 := by
  obtain ⟨K, _, hU3, hq, hn3, ⟨e⟩⟩ := exists_equiv_primeFormP_gen h
  obtain ⟨⟨eP⟩, -, -, hOutT, -⟩ := unitary_full_diagonal_outer_order hU3 hn3 hq
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) = 2 := by
    obtain ⟨⟨e', -⟩, -⟩ := (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism e)
    rw [Nat.card_congr e'.toEquiv, hOutT]
    norm_num
  rw [card_mulAut_eq_card_outer_mul hinj, hOut, hcard]

end AutOrder

section Helpers

theorem card_centralizer_congr {G H : Type*} [Group G] [Group H] (f : G ≃* H) (a : G) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) =
      Nat.card (Subgroup.centralizer ({f a} : Set H)) := by
  have hmap : (Subgroup.centralizer ({a} : Set G)).map f.toMonoidHom =
      Subgroup.centralizer ({f a} : Set H) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hx]
    · intro hy
      refine ⟨f.symm y, ?_, by simp⟩
      apply f.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
  rw [← hmap, Subgroup.card_map_of_injective f.injective]

theorem conj_map_apply {G : Type*} [Group G] (α : MulAut G) (m : G) :
    (MulAut.conj (α m) : MulAut G) = α * MulAut.conj m * α⁻¹ := by
  ext n
  simp [MulAut.conj_apply, mul_assoc]

theorem mem_centralizer_of_conjNormal_eq_one {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    (x : X) (h : (MulAut.conjNormal x : MulAut ↥N) = 1) :
    x ∈ Subgroup.centralizer (N : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have := congrArg (fun f : MulAut ↥N => (f ⟨n, hn⟩ : X)) h
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
  show n * x = x * n
  calc n * x = (x * n * x⁻¹) * x := by rw [this]
    _ = x * n := by group

end Helpers

section Main

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33

theorem nilp_cube_zero {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9)
    (ν : Matrix (Fin 3) (Fin 3) F) (h : (1 + ν) ^ 3 = 1) : ν ^ 3 = 0 := by
  haveI := charP_three hF
  have h3F : ((3 : ℕ) : F) = 0 := CharP.cast_eq_zero F 3
  have h3ν : (3 : ℕ) • ν = 0 := by rw [← Nat.cast_smul_eq_nsmul F, h3F, zero_smul]
  have h3ν2 : (3 : ℕ) • ν ^ 2 = 0 := by rw [← Nat.cast_smul_eq_nsmul F, h3F, zero_smul]
  have e : (1 + ν) ^ 3 = 1 + (3 : ℕ) • ν + (3 : ℕ) • ν ^ 2 + ν ^ 3 := by noncomm_ring
  rw [e, h3ν, h3ν2] at h
  simpa using h

theorem kFactE9U33 : KFactE9U33 := by
  intro X _ _ N Q _ hs hmod hQ hQ9 hQC htrans
  classical
  obtain ⟨F, hFfield, hF9, ⟨e⟩⟩ := exists_equiv_statedSU_of_model hmod
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF9]; norm_num)
  have hcardK : Nat.card ↥(SU F) = 6048 :=
    CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU hF9
  have hcardN : Nat.card ↥N = 6048 := by
    rw [Nat.card_congr e.toEquiv]; exact hcardK
  have hnc : ¬ IsMulCommutative ↥N := by
    intro hc
    haveI := hs
    letI : CommGroup ↥N := { (inferInstance : Group ↥N) with mul_comm := hc.is_comm.comm }
    have := IsSimpleGroup.prime_card (α := ↥N)
    rw [hcardN] at this
    exact absurd this (by norm_num)
  have hinj := conj_injective_of_simple hs hnc
  have hAut : Nat.card (MulAut ↥N) = 12096 := card_mulAut_psu33 hmod hcardN hinj
  set I : Subgroup (MulAut ↥N) := innSub ↥N with hI
  have hIcard : Nat.card I = 6048 := by
    rw [← hcardN]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hIidx : I.index = 2 := by
    have h := Subgroup.card_mul_index I
    rw [hIcard, hAut] at h
    omega
  set φ : X →* MulAut ↥N := MulAut.conjNormal with hφ
  have hφinj : ∀ x ∈ Q, ∀ y ∈ Q, φ x = φ y → x = y := by
    intro x hx y hy h
    have h1 : φ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have hc := mem_centralizer_of_conjNormal_eq_one N _ h1
    have : x⁻¹ * y ∈ Q ⊓ Subgroup.centralizer (N : Set X) := ⟨Q.mul_mem (Q.inv_mem hx) hy, hc⟩
    rw [hQC, Subgroup.mem_bot] at this
    exact inv_mul_eq_one.mp this
  have hinner : ∀ x ∈ Q, ∃ m : ↥N, (MulAut.conj m : MulAut ↥N) = φ x := by
    intro x hx
    have h3 : (φ x) ^ 3 = 1 := by rw [← map_pow, hQ.2 x hx, map_one]
    have h4 : φ x = ((φ x) ^ 2) ^ 2 := by
      calc φ x = φ x * (φ x) ^ 3 := by rw [h3, mul_one]
        _ = ((φ x) ^ 2) ^ 2 := by group
    have hmem : φ x ∈ I := by
      rw [h4]
      exact Subgroup.sq_mem_of_index_two hIidx _
    obtain ⟨m, hm⟩ := hmem
    exact ⟨m, hm⟩
  choose! nn hnn using hinner
  have hnn_mul : ∀ x ∈ Q, ∀ y ∈ Q, nn (x * y) = nn x * nn y := by
    intro x hx y hy
    apply hinj
    rw [map_mul, hnn x hx, hnn y hy, hnn (x * y) (Q.mul_mem hx hy), map_mul]
  let n' : ↥Q →* ↥N := MonoidHom.mk' (fun x => nn x) (fun x y => hnn_mul x x.2 y y.2)
  have hn'inj : Function.Injective n' := by
    intro x y h
    apply Subtype.ext
    apply hφinj x x.2 y y.2
    rw [← hnn x x.2, ← hnn y y.2]
    exact congrArg (fun m => (MulAut.conj m : MulAut ↥N)) h
  let ψ : ↥Q →* ↥(SU F) := e.toMonoidHom.comp n'
  have hψinj : Function.Injective ψ := e.injective.comp hn'inj
  set Qk : Subgroup ↥(SU F) := ψ.range with hQk
  have hQk9 : Nat.card Qk = 9 := by
    rw [← hQ9]
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hQk3 : ∀ z ∈ Qk, z ^ 3 = 1 := by
    rintro _ ⟨q, rfl⟩
    have h3 : q ^ 3 = 1 := Subtype.ext (by simpa using hQ.2 (q : X) q.2)
    rw [← map_pow, h3, map_one]
  have hQkc : ∀ z ∈ Qk, ∀ w ∈ Qk, z * w = w * z := by
    rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact hQ.1.is_comm.comm q q'
  obtain ⟨y₀, hy₀Q, hy₀reg⟩ := exists_regular_of_elemAbelian hF9 Qk hQk3 hQkc hQk9
  have hy₀3 : (mat (y₀ : GL (Fin 3) F) - 1) ^ 3 = 0 := by
    apply nilp_cube_zero hF9
    have h := hQk3 y₀ hy₀Q
    have : mat (((y₀ ^ 3 : ↥(SU F)) : GL (Fin 3) F)) = 1 := by rw [h]; rfl
    have h2 : mat (((y₀ ^ 3 : ↥(SU F)) : GL (Fin 3) F)) = (mat (y₀ : GL (Fin 3) F)) ^ 3 := rfl
    rw [add_sub_cancel, ← h2, this]
  have hy₀C := card_centralizer_regular_le hF9 y₀ hy₀3 hy₀reg
  have hC : ∀ z ∈ Qk, z ≠ 1 → Nat.card (Subgroup.centralizer ({z} : Set ↥(SU F))) ≤ 9 := by
    intro z hz hz1
    obtain ⟨q, rfl⟩ := hz
    obtain ⟨q₀, hq₀⟩ := hy₀Q
    have hq1 : (q : X) ≠ 1 := fun h => hz1 (by
      have : q = 1 := Subtype.ext h
      rw [this, map_one])
    have hq₀1 : (q₀ : X) ≠ 1 := by
      intro h
      have : q₀ = 1 := Subtype.ext h
      have hy1 : y₀ = 1 := by rw [← hq₀, this, map_one]
      apply hy₀reg
      rw [hy1]
      simp [mat]
    obtain ⟨g, -, hg⟩ := htrans (q : X) q.2 (q₀ : X) q₀.2 hq1 hq₀1
    have hαn : (φ g) (nn q) = nn q₀ := by
      apply hinj
      rw [conj_map_apply, hnn (q : X) q.2, hnn (q₀ : X) q₀.2, ← hg, map_mul, map_mul, map_inv]
    have c1 := card_centralizer_congr e (nn q)
    have c2 := card_centralizer_congr (φ g) (nn q)
    have c3 := card_centralizer_congr e (nn q₀)
    have hψq : ψ q = e (nn q) := rfl
    have hψq0 : ψ q₀ = e (nn q₀) := rfl
    rw [hψq, ← c1, c2, hαn, c3, ← hψq0, hq₀]
    exact hy₀C
  exact false_of_small_centralizers Qk hQk9 hQkc hQk3 hcardK hC

theorem kFactRankTwoE9 : KFactRankTwoE9 := kFactRankTwoE9_of_u33 kFactE9U33

end Main

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
