module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverMin
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8ParabolicBasic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Lift

theorem exists_pElement_lift {G Q : Type*} [Group G] [Group Q] [Finite G] (f : G →* Q) {p : ℕ}
    [hp : Fact p.Prime] {x : G} (hx : ∃ k : ℕ, orderOf (f x) = p ^ k) :
    ∃ e : ℕ, (∃ k : ℕ, orderOf (x ^ e) = p ^ k) ∧ f (x ^ e) = f x := by
  obtain ⟨k, hk⟩ := hx
  set o := orderOf x with ho
  have ho0 : o ≠ 0 := (orderOf_pos x).ne'
  set a := o.factorization p with ha
  set m := o / p ^ a with hm
  have hom : o = p ^ a * m := (Nat.mul_div_cancel' (Nat.ordProj_dvd o p)).symm
  have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp.out ho0
  obtain ⟨e, he1, he2⟩ := Nat.chineseRemainder (Nat.Coprime.pow_left k hcop) 1 0
  have hme : m ∣ e := (Nat.modEq_zero_iff_dvd).1 he2
  obtain ⟨e', he'⟩ := hme
  refine ⟨e, ?_, ?_⟩
  · have hpow : (x ^ e) ^ (p ^ a) = 1 := by
      rw [← pow_mul, he', show m * e' * p ^ a = o * e' by rw [hom]; ring, pow_mul, ho,
        pow_orderOf_eq_one, one_pow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hpow)
    exact ⟨j, hj⟩
  · have h1 := pow_mod_orderOf (f x) e
    have h2 := pow_mod_orderOf (f x) 1
    rw [hk] at h1 h2
    have h3 : e % p ^ k = 1 % p ^ k := he1
    rw [h3] at h1
    rw [map_pow, ← h1, h2, pow_one]

end Lift

section Transport

variable {G : Type*} [Group G]

theorem mem_normalizer_iff_map' {X₀ : Subgroup G} (K : Subgroup ↥X₀) (x : ↥X₀) :
    x ∈ Subgroup.normalizer (K : Set ↥X₀) ↔
      (x : G) ∈ Subgroup.normalizer ((K.map X₀.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨x * y' * x⁻¹, (hx y').mp hy', by simp⟩
    · rintro ⟨z, hz, hzy⟩
      have hzy' : (z : G) = (x : G) * y * (x : G)⁻¹ := hzy
      have hz' : (x⁻¹ * z * x : ↥X₀) ∈ K := by
        refine (hx (x⁻¹ * z * x)).mpr ?_
        have e1 : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
        rw [e1]
        exact hz
      refine ⟨x⁻¹ * z * x, hz', ?_⟩
      show (((x⁻¹ * z * x : ↥X₀)) : G) = y
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzy']
      group
  · intro hx y
    constructor
    · intro hy
      have h1 := (hx (y : G)).mp ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := h1
      have : z = x * y * x⁻¹ := Subtype.ext (by simpa using hzy)
      rwa [← this]
    · intro hy
      have h1 := (hx (y : G)).mpr (by
        refine ⟨x * y * x⁻¹, hy, ?_⟩
        simp)
      obtain ⟨z, hz, hzy⟩ := h1
      have : z = y := Subtype.ext hzy
      rwa [← this]

theorem map_normalizer_eq_inf' {X₀ : Subgroup G} (K : Subgroup ↥X₀) :
    (Subgroup.normalizer (K : Set ↥X₀)).map X₀.subtype =
      Subgroup.normalizer ((K.map X₀.subtype : Subgroup G) : Set G) ⊓ X₀ := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(mem_normalizer_iff_map' K x).mp hx, x.2⟩
  · rintro ⟨hz, hzX⟩
    exact ⟨⟨z, hzX⟩, (mem_normalizer_iff_map' K ⟨z, hzX⟩).mpr hz, rfl⟩

end Transport

section Main

variable {W : Type} [Group W] [Finite W] {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem cover_of_borelQuotient {L S₀ A₁ A₂ : Subgroup W} (hS : IsSylowTwoOf S₀ L)
    (hcov : CoveredByTwo L S₀ A₁ A₂) {π : K →* ↥L ⧸ Subgroup.center ↥L}
    (h : BorelQuotient D n H π M)
    (hT : (S₀.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) =
      (posUnipotent D).map π) (i : Fin D.rank) :
    (rankOne D.rootGroup i).map π ≤
        (A₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ∨
      (rankOne D.rootGroup i).map π ≤
        (A₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center ↥L with hZ
  set q : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hqdef
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Z
  have hqker : q.ker = Z := by rw [hqdef, QuotientGroup.ker_mk']
  obtain ⟨S, hSS⟩ := Lie.exists_sylow_of_isSylowTwoOf hS
  have hS₀L : S₀ ≤ L := hS.1
  set S₀' : Subgroup ↥L := S₀.subgroupOf L with hS₀'
  have hker_le_B : π.ker ≤ borel D H := fun z hz =>
    CFSG.ClassicalInvolution.WeakCT.normalizer_posUnipotent_le_borel h.ct h.extras
      (Subgroup.center_le_normalizer (posUnipotent D : Set K) (h.ker_central z hz))
  have hNY : Subgroup.normalizer (((S₀').map q : Subgroup _) : Set _) = (borel D H).map π := by
    rw [hqdef, hT]
    exact h.normalizer_map_posUnipotent
  have hBL : Subgroup.normalizer (S₀' : Set ↥L) = ((borel D H).map π).comap q := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_comap, ← hNY]
      exact Subgroup.le_normalizer_map q ⟨x, hx, rfl⟩
    · intro hx
      rw [Subgroup.mem_comap, ← hNY] at hx
      have h1 := normalizer_map_le S hq (by rw [hqker]) (by
        rw [hSS]
        exact hx)
      obtain ⟨x', hx', hxx'⟩ := h1
      have hz : x'⁻¹ * x ∈ Z := by
        rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel]
      have : x = x' * (x'⁻¹ * x) := by group
      rw [this]
      refine Subgroup.mul_mem _ (by rwa [hSS] at hx')
        (Subgroup.center_le_normalizer (S₀' : Set ↥L) hz)
  obtain ⟨P, hBP, hLP, hPne, hmin⟩ := exists_minOver_of_node h.ct h.extras i
  have hcomapP : (P.map π).comap π = P := by
    rw [Subgroup.comap_map_eq]
    exact sup_eq_left.2 ((hker_le_B).trans hBP)
  have hY1 : (borel D H).map π ≤ P.map π := Subgroup.map_mono hBP
  have hY2 : (borel D H).map π ≠ P.map π := by
    intro heq
    apply hPne
    have := congrArg (Subgroup.comap π) heq
    rw [hcomapP, Subgroup.comap_map_eq, sup_eq_left.2 hker_le_B] at this
    exact this.symm
  have hY3 : ∀ Q : Subgroup (↥L ⧸ Z), (borel D H).map π ≤ Q → Q ≤ P.map π →
      Q = (borel D H).map π ∨ Q = P.map π := by
    intro Q hBQ hQP
    have hBc : borel D H ≤ Q.comap π := fun b hb => hBQ ⟨b, hb, rfl⟩
    have hQc : Q.comap π ≤ P := by
      have := Subgroup.comap_mono (f := π) hQP
      rwa [hcomapP] at this
    have hQ := Subgroup.map_comap_eq_self_of_surjective h.surj Q
    rcases hmin _ hBc hQc with h1 | h1
    · left; rw [← hQ, h1]
    · right; rw [← hQ, h1]
  set PL : Subgroup ↥L := (P.map π).comap q with hPL
  set BL : Subgroup ↥L := ((borel D H).map π).comap q with hBLdef
  have hBW : L ⊓ Subgroup.normalizer (S₀ : Set W) = BL.map L.subtype := by
    rw [show BL = Subgroup.normalizer (S₀' : Set ↥L) from hBL.symm, map_normalizer_eq_inf', hS₀',
      Subgroup.map_subgroupOf_eq_of_le hS₀L, inf_comm]
  have hZBL : Z ≤ BL := by
    intro z hz
    rw [hBLdef, Subgroup.mem_comap]
    have : q z = 1 := by rw [← MonoidHom.mem_ker, hqker]; exact hz
    rw [this]
    exact one_mem _
  have hPmin : IsMinOverBorel L S₀ (PL.map L.subtype) := by
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [hBW]
      refine lt_of_le_of_ne (Subgroup.map_mono (Subgroup.comap_mono hY1)) fun heq => ?_
      have h1 : BL = PL := Subgroup.map_injective L.subtype_injective heq
      have h2 := congrArg (Subgroup.map q) h1
      rw [hBLdef, hPL, Subgroup.map_comap_eq_self_of_surjective hq,
        Subgroup.map_comap_eq_self_of_surjective hq] at h2
      exact hY2 h2
    · intro Q hQ1 hQ2
      rw [hBW] at hQ1 ⊢
      have hQL : Q ≤ L := hQ2.trans (Subgroup.map_subtype_le _)
      have hQe : (Q.subgroupOf L).map L.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQL
      have hB' : BL ≤ Q.subgroupOf L := by
        have h1 : BL.map L.subtype ≤ (Q.subgroupOf L).map L.subtype := by rw [hQe]; exact hQ1
        exact (Subgroup.map_le_map_iff_of_injective L.subtype_injective).1 h1
      have hP' : Q.subgroupOf L ≤ PL := by
        have h1 : (Q.subgroupOf L).map L.subtype ≤ PL.map L.subtype := by rw [hQe]; exact hQ2
        exact (Subgroup.map_le_map_iff_of_injective L.subtype_injective).1 h1
      have hlow : (borel D H).map π ≤ (Q.subgroupOf L).map q := by
        have := Subgroup.map_mono (f := q) hB'
        rwa [hBLdef, Subgroup.map_comap_eq_self_of_surjective hq] at this
      have hup : (Q.subgroupOf L).map q ≤ P.map π := by
        have := Subgroup.map_mono (f := q) hP'
        rwa [hPL, Subgroup.map_comap_eq_self_of_surjective hq] at this
      have hQ' : (Q.subgroupOf L).map q = ((Q.subgroupOf L).map q) := rfl
      have hcm : ((Q.subgroupOf L).map q).comap q = Q.subgroupOf L := by
        rw [Subgroup.comap_map_eq, hqker]
        exact sup_eq_left.2 (hZBL.trans hB')
      rcases hY3 _ hlow hup with h1 | h1
      · left
        rw [← hQe]
        congr 1
        rw [← hcm, h1]
      · right
        rw [← hQe]
        congr 1
        rw [← hcm, h1]
  have key : ∀ A : Subgroup W, pElementSubgroup 2 (PL.map L.subtype) ≤ A →
      (rankOne D.rootGroup i).map π ≤ (A.subgroupOf L).map q := by
    intro A hA
    have hroot : ∀ γ : Fin D.rank → ℤ, γ ∈ D.roots → D.rootGroup γ ≤ rankOne D.rootGroup i →
        (D.rootGroup γ).map π ≤ (A.subgroupOf L).map q := by
      rintro γ hγ hγL _ ⟨x, hx, rfl⟩
      have hxP : π x ∈ P.map π := ⟨x, hLP (hγL hx), rfl⟩
      obtain ⟨xt, hxt⟩ := hq (π x)
      have hxtP : xt ∈ PL := by
        rw [hPL, Subgroup.mem_comap, hxt]
        exact hxP
      have hx2 : ∃ k : ℕ, orderOf (q xt) = 2 ^ k := by
        obtain ⟨k, hk⟩ := h.pGroup γ hγ ⟨x, hx⟩
        have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have hd : orderOf (π x) ∣ 2 ^ k :=
          (orderOf_map_dvd π x).trans (orderOf_dvd_of_pow_eq_one hk')
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
        exact ⟨j, by rw [hxt]; exact hj⟩
      obtain ⟨e, ⟨k, hk⟩, hfe⟩ := exists_pElement_lift q (p := 2) hx2
      have hmemPL : xt ^ e ∈ PL := Subgroup.pow_mem _ hxtP e
      have hmemW : ((xt ^ e : ↥L) : W) ∈ PL.map L.subtype := ⟨_, hmemPL, rfl⟩
      have hord : orderOf ((xt ^ e : ↥L) : W) = 2 ^ k := by
        rw [Subgroup.orderOf_coe]; exact hk
      have hmemA : ((xt ^ e : ↥L) : W) ∈ A :=
        hA (Subgroup.subset_closure ⟨hmemW, k, hord⟩)
      refine ⟨xt ^ e, ?_, ?_⟩
      · exact hmemA
      · rw [hfe, hxt]
    show (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).map π ≤ _
    rw [Subgroup.map_sup]
    refine sup_le (hroot _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
      le_sup_left) (hroot _ ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)) le_sup_right)
  rcases hcov _ hPmin with h1 | h1
  · exact Or.inl (key A₁ h1)
  · exact Or.inr (key A₂ h1)

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
