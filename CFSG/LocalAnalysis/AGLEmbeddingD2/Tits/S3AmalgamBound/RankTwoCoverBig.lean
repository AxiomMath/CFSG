module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerThompson
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

theorem not_isPSolvable_three_of_simple {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ¬ IsMulCommutative S) (h3 : 3 ∣ Nat.card S) :
    ¬ CFSG.HallHigman.IsPSolvable 3 S := fun hsolv =>
  false_of_isPSolvable_surj (N := S) (H := ⊤) hsolv (⊤ : Subgroup S).subtype
    (fun s => ⟨⟨s, trivial⟩, rfl⟩) hS hnc h3

theorem not_isPSolvable_three_sl2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) :
    ¬ CFSG.HallHigman.IsPSolvable 3 (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hS := sl2_isSimpleGroup (k := F) h4
  have hnc : ¬ IsMulCommutative (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro hc
    have := hc.is_comm.comm (sl2Upper (1 : F)) (sl2Lower (1 : F))
    have h2 : ((sl2Upper (1 : F) * sl2Lower (1 : F) : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 0 0 =
        ((sl2Lower (1 : F) * sl2Upper (1 : F) : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 0 0 := by rw [this]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
    simp [sl2Upper, sl2Lower, Matrix.mul_apply, Fin.sum_univ_two] at h2
  refine not_isPSolvable_three_of_simple hS hnc ?_
  obtain ⟨f, -, hf⟩ := exists_card_eq_two_pow F
  rw [card_sl2, hf]
  refine Dvd.dvd.mul_left ?_ _
  have : 3 ∣ 4 ^ f - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 f
  have e : (2 ^ f) ^ 2 = 4 ^ f := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e]; exact this

section Node

variable {K Y : Type} [Group K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem not_isPSolvable_map_rankOne_of_sl2Node (h : BorelQuotient D n H π M) {i : Fin D.rank}
    {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    (hnode : HasSL2Node D i F) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥((rankOne D.rootGroup i).map π) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hinj, hU, hL⟩ := hnode
  have hS := sl2_isSimpleGroup (k := F) h4
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hker : (π.comp φ).ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (π.comp φ).ker with hb | ht
    · exact hb
    · exfalso
      have hmem : sl2Upper (1 : F) ∈ (π.comp φ).ker := by rw [ht]; exact Subgroup.mem_top _
      have hx : π (φ (sl2Upper (1 : F))) = 1 := MonoidHom.mem_ker.1 hmem
      have hxk : φ (sl2Upper (1 : F)) ∈ π.ker := hx
      obtain ⟨k, hk⟩ := h.pGroup _ hα ⟨φ (sl2Upper (1 : F)), hU 1⟩
      have hk' : φ (sl2Upper (1 : F)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hM := h.ker_pow _ hxk
      have hcop : Nat.Coprime (2 ^ k) M := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 h.odd)
      have h1 : orderOf (φ (sl2Upper (1 : F))) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
          (orderOf_dvd_of_pow_eq_one hM)
      have h2 : φ (sl2Upper (1 : F)) = 1 := orderOf_eq_one_iff.1 h1
      have h3 : sl2Upper (1 : F) = 1 := hinj (by rw [h2, map_one])
      have h4' := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
        (A : Matrix (Fin 2) (Fin 2) F) 0 1) h3
      simp [sl2Upper] at h4'
  have hψ : Function.Injective (π.comp φ) := (MonoidHom.ker_eq_bot_iff _).1 hker
  have hle : φ.range ≤ rankOne D.rootGroup i := by
    rintro _ ⟨A, rfl⟩
    have hA := Sp.mem_closure_sl2 A
    have hcl : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
        (rankOne D.rootGroup i).comap φ := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact le_sup_left (a := D.rootGroup (Pi.single i 1)) (hU c)
      · exact le_sup_right (b := D.rootGroup (-Pi.single i 1)) (hL c)
    exact hcl hA
  intro hsolv
  have hV : (π.comp φ).range ≤ (rankOne D.rootGroup i).map π := by
    rintro _ ⟨A, rfl⟩
    exact ⟨φ A, hle ⟨A, rfl⟩, rfl⟩
  have h1 := OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hsolv hV
  have e := MonoidHom.ofInjective hψ
  exact not_isPSolvable_three_sl2 h4
    (OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv e.symm h1)

end Node

section Cover

variable {W : Type} [Group W] [Finite W] {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem exists_borelQuotient_conj {L S₀ : Subgroup W} (hS : IsSylowTwoOf S₀ L)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M) :
    ∃ π' : K →* ↥L ⧸ Subgroup.center ↥L, BorelQuotient D n H π' M ∧
      (S₀.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) =
        (posUnipotent D).map π' := by
  obtain ⟨T, hT⟩ := McLaughlin.Lie.exists_sylow_of_isSylowTwoOf hS
  have hsurj := QuotientGroup.mk'_surjective (Subgroup.center ↥L)
  obtain ⟨π', hπ', hker, hT'⟩ := h.exists_conj_eq (T.mapSurjective hsurj)
  refine ⟨π', ⟨h.ct, h.extras, h.pGroup, hπ', h.odd, h.torus_pow,
    fun z hz => h.ker_central z (hker ▸ hz), fun z hz => h.ker_pow z (hker ▸ hz)⟩, ?_⟩
  rw [← hT, ← hT', Sylow.coe_mapSurjective]

theorem isPSolvable_map_subgroupOf {A : Subgroup W} (L : Subgroup W)
    (hA : CFSG.HallHigman.IsPSolvable 3 ↥A) :
    CFSG.HallHigman.IsPSolvable 3
      ↥((A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : CFSG.HallHigman.IsPSolvable 3 ↥(A ⊓ L) :=
    OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hA inf_le_left
  have h2 : CFSG.HallHigman.IsPSolvable 3 ↥((A ⊓ L).subgroupOf L) :=
    OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).symm h1
  rw [← Subgroup.inf_subgroupOf_right] 
  exact OrdinaryProofs.PSolvableClosure.isPSolvable_map _ h2

theorem false_of_big_node {L S₀ A₁ A₂ : Subgroup W} (hS : IsSylowTwoOf S₀ L)
    (hcov : CoveredByTwo L S₀ A₁ A₂) (h1 : CFSG.HallHigman.IsPSolvable 3 ↥A₁)
    (h2 : CFSG.HallHigman.IsPSolvable 3 ↥A₂) {π : K →* ↥L ⧸ Subgroup.center ↥L}
    (h : BorelQuotient D n H π M) (i : Fin D.rank)
    (hbig : ∀ {π' : K →* ↥L ⧸ Subgroup.center ↥L}, BorelQuotient D n H π' M →
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥((rankOne D.rootGroup i).map π')) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π', hπ', hT⟩ := exists_borelQuotient_conj hS h
  rcases cover_of_borelQuotient hS hcov hπ' hT i with hc | hc
  · exact hbig hπ' (OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
      (isPSolvable_map_subgroupOf L h1) hc)
  · exact hbig hπ' (OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
      (isPSolvable_map_subgroupOf L h2) hc)

end Cover

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
