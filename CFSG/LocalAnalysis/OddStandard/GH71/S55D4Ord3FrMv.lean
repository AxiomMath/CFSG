module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Fr

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.OddAut

theorem map_eq_of_map_le {G : Type*} [Group G] [Finite G] (E : Subgroup G) (φ : MulAut G)
    (h : E.map φ.toMonoidHom ≤ E) : E.map φ.toMonoidHom = E :=
  Subgroup.eq_of_le_of_card_ge h (by rw [Subgroup.card_map_of_injective φ.injective])

section Two

variable
  {K : Type} [Field K] (σ : K ≃+* K) {L : Type} [Field L] [Algebra K L]
  (g₀ : ModGL TwistTag.D4.tag L)

local notation "𝒞" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem d4Frame_comm {x y : 𝒞} (hx : d4MinusPsi σ L g₀ x ∈ torusGroup TwistTag.D4.tag L)
    (hy : d4MinusPsi σ L g₀ y ∈ torusGroup TwistTag.D4.tag L) : x * y = y * x := by
  apply d4MinusPsi_injective g₀
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  rw [map_mul, map_mul, hl]
  exact rootDiagUnit_mul_comm_of_mem_torusGroup l hy

@[expose] def d4FrTwo : Subgroup 𝒞 where
  carrier := {y | d4MinusPsi σ L g₀ y ∈ torusGroup TwistTag.D4.tag L ∧ y * y = 1}
  mul_mem' := by
    rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
    refine ⟨by rw [map_mul]; exact mul_mem hx hy, ?_⟩
    have hc := d4Frame_comm σ g₀ hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc]
      _ = 1 := by rw [← mul_assoc, hx2, one_mul, hy2]
  one_mem' := ⟨by rw [map_one]; exact one_mem _, mul_one 1⟩
  inv_mem' := by
    rintro x ⟨hx, hx2⟩
    refine ⟨by rw [map_inv]; exact inv_mem hx, ?_⟩
    rw [← mul_inv_rev, hx2, inv_one]

theorem isPGroup_d4FrTwo : IsPGroup 2 (d4FrTwo σ g₀) := fun x =>
  ⟨1, Subtype.ext (by rw [pow_one, sq]; exact x.2.2)⟩

theorem d4FrTwo_comm : ∀ x ∈ d4FrTwo σ g₀, ∀ y ∈ d4FrTwo σ g₀, x * y = y * x :=
  fun _ hx _ hy => d4Frame_comm σ g₀ hx.1 hy.1

end Two


section Moves

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {L : Type}
  [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p] {g₀ : ModGL TwistTag.D4.tag L}

local notation "𝒞" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem movesAbelianTwo_frame (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hg₀ : D4MinusFrame p f L g₀) (φ : MulAut 𝒞)
    (hφT : ∀ y, d4MinusPsi σ L g₀ y ∈ torusGroup TwistTag.D4.tag L →
      d4MinusPsi σ L g₀ (φ y) ∈ torusGroup TwistTag.D4.tag L)
    {w : WeylGroup TwistTag.D4.tag} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hφs : ∀ c : Fin TwistTag.D4.tag.rank → ℤ, (∀ j, c (TwistTag.D4.perm.symm j) = c j) →
      ∀ y : 𝒞, d4MinusPsi σ L g₀ y = rootDiagUnit TwistTag.D4.tag (d4Sign L c) →
        d4MinusPsi σ L g₀ (φ y) = rootDiagUnit TwistTag.D4.tag (weylTuple w (d4Sign L c))) :
    MovesAbelianTwo φ := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have h2 : (2 : L) ≠ 0 := by
    intro h0
    have h2p : p ∣ 2 := (CharP.cast_eq_zero_iff L p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2p)
  refine ⟨d4FrTwo σ g₀, isPGroup_d4FrTwo σ g₀, d4FrTwo_comm σ g₀, map_eq_of_map_le _ φ ?_, ?_⟩
  · rintro _ ⟨y, ⟨hy, hy2⟩, rfl⟩
    exact ⟨hφT y hy, by rw [MulEquiv.coe_toMonoidHom, ← map_mul, hy2, map_one]⟩
  · have hsign : ∀ c : Fin TwistTag.D4.tag.rank → ℤ, (∃ j, ∀ k,
        (TwistTag.D4.tag.cartan j k - c k) % 2 = 0) → (∀ i, c (TwistTag.D4.perm.symm i) = c i) →
        weylTuple w (d4Sign L c) ≠ d4Sign L c → ∃ x ∈ d4FrTwo σ g₀, φ x ≠ x := by
      intro c ⟨j, hj⟩ hρ hmove
      obtain ⟨y, hy⟩ := rootDiagUnit_d4Sign_mem_range σ hf hK hσ hg₀ c j hj hρ
      refine ⟨y, ⟨by rw [hy]; exact rootDiagUnit_mem_torusGroup _, d4MinusPsi_injective g₀ ?_⟩,
        fun h => hmove ?_⟩
      · rw [map_mul, hy, ← rootDiagUnit_mul, d4Sign_mul_self, rootDiagUnit_one, map_one]
      · have h' := congrArg (d4MinusPsi σ L g₀) h
        rw [hφs c hρ y hy, hy] at h'
        exact rootDiagUnit_injective h'
    rcases d4_weyl_moves_sign_all h2 hw3 hw1 with hA | hB
    · exact hsign d4ParA ⟨2, by decide⟩ (by decide) hA
    · exact hsign d4ParB ⟨0, by decide⟩ (by decide) hB

omit
  [Fact p.Prime] [Finite K] [IsAlgClosure K L] [CharP L p] in
theorem weyl_ne_one_of_not_mem_torus {x : ModGL TwistTag.D4.tag L}
    (hxM : x ∈ monomialSubgroup TwistTag.D4.tag L) (hxT : x ∉ torusGroup TwistTag.D4.tag L)
    {w : WeylGroup TwistTag.D4.tag} (hw : MapsRootLines x w) : w ≠ 1 :=
  fun h => hxT (mem_torusGroup_of_mapsRootLines_one hxM (h ▸ hw))

theorem d4_frame_movesAbelianTwo_inner (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hg₀ : D4MinusFrame p f L g₀) (n : 𝒞)
    (hnM : d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnT : d4MinusPsi σ L g₀ n ∉ torusGroup TwistTag.D4.tag L) (hn3 : n ^ 3 = 1) :
    MovesAbelianTwo (MulAut.conj n) := by
  obtain ⟨w, hw⟩ := exists_mapsRootLines_of_mem hnM
  have hw3 : w ^ 3 = 1 := by
    have h := d4Minus_mapsRootLines_pow hw 3
    rw [← map_pow, hn3, map_one] at h
    exact (mapsRootLines_one.unique h).symm
  refine movesAbelianTwo_frame σ hp2 hf hK hσ hg₀ (MulAut.conj n) (fun y hy => ?_) hw3
    (weyl_ne_one_of_not_mem_torus hnM hnT hw) (fun c _ y hy => ?_)
  · rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    exact monomial_conj_mem_torus_d4 hnM hy
  · rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hy]
    exact monomial_conj_rootDiagUnit hnM hw _

theorem d4_frame_movesAbelianTwo_outer (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hg₀ : D4MinusFrame p f L g₀) (n : 𝒞)
    (hnM : d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnT : d4MinusPsi σ L g₀ n ∉ torusGroup TwistTag.D4.tag L)
    (hN : normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1) :
    MovesAbelianTwo (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ c, iterateFrobenius L p f c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = (iterateFrobenius L p f).comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  have hψδ := d4MinusPsi_fieldActor (iterateFrobenius L p f) hcomm hg₀.2.1
  obtain ⟨w, hw⟩ := exists_mapsRootLines_of_mem hnM
  obtain ⟨hM1, hw1⟩ := diagramMap_conj_monomial_of_mem_range σ hf hK hσ hg₀ ⟨n, rfl⟩ hnM hw
  rw [← hψδ] at hM1 hw1
  obtain ⟨-, hw2⟩ := diagramMap_conj_monomial_of_mem_range σ hf hK hσ hg₀ ⟨_, rfl⟩ hM1 hw1
  rw [← hψδ] at hw2
  have hw3 : w ^ 3 = 1 := by
    have h := (hw.mul hw1).mul hw2
    have e : normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = n * fieldActor σ σ n *
        fieldActor σ σ (fieldActor σ σ n) := by
      simp only [normSeq, pow_two, MulAut.mul_apply, MulAut.one_apply, pow_zero, pow_one, one_mul]
    rw [← map_mul, ← map_mul, ← e, hN, map_one] at h
    rw [pow_three']
    exact (mapsRootLines_one.unique h).symm
  refine movesAbelianTwo_frame σ hp2 hf hK hσ hg₀ _ (fun y hy => ?_) hw3
    (weyl_ne_one_of_not_mem_torus hnM hnT hw) (fun c hρ y hy => ?_)
  · rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hψδ]
    refine monomial_conj_mem_torus_d4 hnM ?_
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
    rw [ha, d4Minus_h90_conj]
    exact rootDiagUnit_mem_torusGroup _
  · rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hψδ, hy,
      diagramMap_conj_d4Sign c hρ]
    exact monomial_conj_rootDiagUnit hnM hw _

end Moves

end CFSG.OddStandard.GH71.S55
