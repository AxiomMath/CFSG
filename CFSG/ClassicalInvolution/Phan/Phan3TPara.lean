module

public import CFSG.ClassicalInvolution.Phan.Phan3TBlocks
public import CFSG.ClassicalInvolution.Phan.Phan3GRec
public import CFSG.ClassicalInvolution.Phan.Parabolic

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.Monster.B.Geometry
  CFSG.Monster.B.Geometry.ChamberSystem CFSG.ClassicalInvolution.Phan.TitsChamber

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {Y : Type} [Group Y] {n : ℕ}

noncomputable def levi3Hom (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) {a : ℕ}
    (ha : a + 2 < n) (Θ : Su K p f 4 →* Y) : blockSup K p f n (typeInt n a (a + 3)) →* Y :=
  (Θ.comp (MonoidHom.ofInjective (blockEmb_injective (K := K) (p := p) (f := f)
    (by omega : a + 4 ≤ n + 1))).symm.toMonoidHom).comp
    (Subgroup.inclusion (blockSup_typeInt_three hK hq ha).le)

theorem levi3Hom_apply (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) {a : ℕ}
    (ha : a + 2 < n) (Θ : Su K p f 4 →* Y) (x : blockSup K p f n (typeInt n a (a + 3)))
    (A : Su K p f 4) (hx : (x : Su K p f (n + 1)) = blockEmb K p f (n + 1) 4 a (by omega) A) :
    levi3Hom hK hq ha Θ x = Θ A := by
  obtain ⟨x, hx'⟩ := x
  subst hx
  exact congrArg Θ (ofInjective_symm_apply_self (blockEmb_injective (K := K) (p := p) (f := f)
    (by omega : a + 4 ≤ n + 1)) A _)

theorem exists_isParabolicHom3 (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2)
    (F : PhanFamily K p f Y n) {a : ℕ} (ha : a + 2 < n) (Θ : Su K p f 4 →* Y)
    (hΘ : ∀ k : Fin 3, Θ.comp (blockEmb2 K p f 3 k) = F.ι ⟨a + k, by omega⟩) :
    ∃ φ : parabolic K p f n (typeInt n a (a + 3)) →* Y,
      F.IsParabolicHom (typeInt n a (a + 3)) φ := by
  have h4 : a + 4 ≤ n + 1 := by omega
  have hblk : ∀ (k : Fin 3) (A : Su K p f 2),
      blockEmb2 K p f n ⟨a + k, by omega⟩ A =
        blockEmb K p f (n + 1) 4 a h4 (blockEmb2 K p f 3 k A) := fun k A =>
    (DFunLike.congr_fun (blockEmb4_comp_blockEmb2 (K := K) (p := p) (f := f) h4 k) A).symm
  have hmem : ∀ j : Fin n, j ∈ typeInt n a (a + 3) → ∃ k : Fin 3, j = ⟨a + k, by omega⟩ := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := hj
    exact ⟨⟨j.val - a, by omega⟩, Fin.ext (by simp only; omega)⟩
  have hφN : F.IsBlockHom (typeInt n a (a + 3)) (levi3Hom hK hq ha Θ) := by
    intro j hj A
    obtain ⟨k, rfl⟩ := hmem j hj
    rw [levi3Hom_apply hK hq ha Θ _ (blockEmb2 K p f 3 k A) (hblk k A)]
    exact DFunLike.congr_fun (hΘ k) A
  have hagree : ∀ (g : Su K p f (n + 1)) (hN : g ∈ blockSup K p f n (typeInt n a (a + 3)))
      (hT : g ∈ torus (unitaryInvolution K p f) (n + 1)),
      levi3Hom hK hq ha Θ ⟨g, hN⟩ = F.torusHom ⟨g, hT⟩ := by
    intro g hN hT
    obtain ⟨A, rfl⟩ : g ∈ (blockEmb K p f (n + 1) 4 a h4).range :=
      (blockSup_typeInt_three hK hq ha) ▸ hN
    obtain ⟨u, v, w, huvw⟩ := exists_blockEmb4_diag ha hT
    have j0 : (⟨a, by omega⟩ : Fin n) ∈ typeInt n a (a + 3) := ⟨le_refl a, by simp only; omega⟩
    have j1 : (⟨a + 1, by omega⟩ : Fin n) ∈ typeInt n a (a + 3) :=
      ⟨by simp only; omega, by simp only; omega⟩
    have j2 : (⟨a + 2, ha⟩ : Fin n) ∈ typeInt n a (a + 3) :=
      ⟨by simp only; omega, by simp only; omega⟩
    have m0 := blockEmb2_mem_blockSup j0 (torusTwo (unitaryInvolution K p f) u)
    have m1 := blockEmb2_mem_blockSup j1 (torusTwo (unitaryInvolution K p f) v)
    have m2 := blockEmb2_mem_blockSup j2 (torusTwo (unitaryInvolution K p f) w)
    have t0 := blockEmb2_torusTwo_mem_torus (K := K) (p := p) (f := f) (n := n) ⟨a, by omega⟩ u
    have t1 := blockEmb2_torusTwo_mem_torus (K := K) (p := p) (f := f) (n := n)
      ⟨a + 1, by omega⟩ v
    have t2 := blockEmb2_torusTwo_mem_torus (K := K) (p := p) (f := f) (n := n) ⟨a + 2, ha⟩ w
    have e1 : (⟨blockEmb K p f (n + 1) 4 a h4 A, hN⟩ :
        blockSup K p f n (typeInt n a (a + 3))) =
        (⟨_, m0⟩ : blockSup K p f n (typeInt n a (a + 3))) *
          (⟨_, m1⟩ : blockSup K p f n (typeInt n a (a + 3))) *
          (⟨_, m2⟩ : blockSup K p f n (typeInt n a (a + 3))) :=
      Subtype.ext huvw
    have e2 : (⟨blockEmb K p f (n + 1) 4 a h4 A, hT⟩ :
        torus (unitaryInvolution K p f) (n + 1)) =
        (⟨_, t0⟩ : torus (unitaryInvolution K p f) (n + 1)) *
          (⟨_, t1⟩ : torus (unitaryInvolution K p f) (n + 1)) *
          (⟨_, t2⟩ : torus (unitaryInvolution K p f) (n + 1)) :=
      Subtype.ext huvw
    rw [e1, e2, map_mul, map_mul, map_mul, map_mul,
      F.torusHom_blockEmb2 ⟨a, by omega⟩ u t0, F.torusHom_blockEmb2 ⟨a + 1, by omega⟩ v t1,
      F.torusHom_blockEmb2 ⟨a + 2, ha⟩ w t2]
    rw [hφN _ j0 _, hφN _ j1 _, hφN _ j2 _]
  obtain ⟨φ, h1, h2⟩ := exists_hom_sup_of_normalizes'
    (torus_le_normalizer_blockSup hK (typeInt n a (a + 3))) (levi3Hom hK hq ha Θ) F.torusHom
    hagree (fun t x => F.conj_relation hK hφN t x)
  exact ⟨φ, fun t ht => h2 ⟨t, ht⟩, fun j hj A =>
    (h1 ⟨blockEmb2 K p f n j A, blockEmb2_mem_blockSup hj A⟩).trans (hφN j hj A)⟩

theorem isParabolicHom_restrict (F : PhanFamily K p f Y n) {J J' : Set (Fin n)}
    (hJJ' : J' ⊆ J) {φ : parabolic K p f n J →* Y} (hφ : F.IsParabolicHom J φ) :
    F.IsParabolicHom J' (φ.comp (Subgroup.inclusion (parabolic_mono hJJ'))) :=
  ⟨fun t ht => hφ.1 t ht, fun j hj A => hφ.2 j (hJJ' hj) A⟩

theorem isParabolicHom_compat (F : PhanFamily K p f Y n) {J J' : Set (Fin n)}
    (hJJ' : J' ⊆ J) {φ : parabolic K p f n J →* Y} (hφ : F.IsParabolicHom J φ)
    {φ' : parabolic K p f n J' →* Y} (hφ' : F.IsParabolicHom J' φ') (g : Su K p f (n + 1))
    (hgJ' : g ∈ parabolic K p f n J') (hgJ : g ∈ parabolic K p f n J) :
    φ' ⟨g, hgJ'⟩ = φ ⟨g, hgJ⟩ :=
  DFunLike.congr_fun (F.isParabolicHom_unique hφ' (isParabolicHom_restrict F hJJ' hφ))
    ⟨g, hgJ'⟩

theorem encard_typeInt_three_le_two {a : ℕ} (ha : ¬ a + 2 < n) :
    (typeInt n a (a + 3)).encard ≤ 2 := by
  have : typeInt n a (a + 3) = typeInt n a (a + 2) := by
    ext j
    simp only [mem_typeInt]
    have := j.isLt
    omega
  rw [this]
  exact encard_typeInt_le_two le_rfl

theorem phanUniversalAt3_of_blocks (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f = 3)
    (F : PhanFamily K p f Y n)
    (hΘ : ∀ (a : ℕ) (ha : a + 2 < n), ∃ Θ : Su K p f 4 →* Y,
      ∀ k : Fin 3, Θ.comp (blockEmb2 K p f 3 k) = F.ι ⟨a + k, by omega⟩) :
    ∃ ψ : Su K p f (n + 1) →* Y, (∀ i : Fin n, ψ.comp (blockEmb2 K p f n i) = F.ι i) ∧
      ∀ (i : Fin n) (h : (i : ℕ) + 1 < n), ψ.comp (blockEmb3 K p f n i h) = F.θ i := by
  have hq2 : p ^ f ≠ 2 := by omega
  have hσ := isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK
  have hcard : Nat.card K = 3 ^ 2 := by rw [hK, hq]
  have hS := frameSystem_simplyConnectedOn3_of_card hσ hcard n
  have hconn := frameSystem_connected (n := n) hσ hK (by omega : 3 ≤ p ^ f)
  have hex : ∀ J : Set (Fin n), J3 n J → ∃ φ : parabolic K p f n J →* Y, F.IsParabolicHom J φ := by
    intro J hJ
    rcases hJ with h2 | ⟨a, rfl⟩
    · exact F.exists_isParabolicHom hK h2
    · by_cases ha : a + 2 < n
      · obtain ⟨Θ, hΘ'⟩ := hΘ a ha
        exact exists_isParabolicHom3 hK hq2 F ha Θ hΘ'
      · exact F.exists_isParabolicHom hK (encard_typeInt_three_le_two ha)
  choose φ hφ using hex
  obtain ⟨ψ, hψ, -⟩ := tits_chamber_universal_completion_of_family
    (frameSystem (unitaryInvolution K p f) n) (J3 n) (Or.inl (by simp)) (fun i => Or.inl (by simp))
    hconn hS (G := Su K p f (n + 1))
    (fun g i x y h => frameSystem_adj_smul g h) (stdFrame (unitaryInvolution K p f) (n + 1))
    (fun c => exists_smul_stdFrame hσ c) (parabolic K p f n)
    (fun J _ g => mem_parabolic_iff hK J g) φ
    (fun J J' hJ hJ' hJJ' g hgJ' hgJ => isParabolicHom_compat F hJJ' (hφ J hJ) (hφ J' hJ') g hgJ'
      hgJ)
  refine ⟨ψ, F.comp_blockEmb_of_parabolicHom hK hq2 ψ fun J hJ g => ?_⟩
  rw [hψ J (Or.inl hJ) g]
  exact DFunLike.congr_fun (F.isParabolicHom_unique (hφ J (Or.inl hJ))
    (F.isParabolicHom_parabolicHom hK hJ)) g

end CFSG.ClassicalInvolution.Phan.Q3G
