module

public import CFSG.Goldschmidt.Steps.G3aFStar
public import CFSG.Goldschmidt.Steps.G37Transport

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open

section Chains

variable {M : Type*} [Group M]

theorem isSubnormal_trans' {X Y Z : Subgroup M} (h₁ : IsSubnormal X Y) (h₂ : IsSubnormal Y Z) :
    IsSubnormal X Z :=
  h₁.trans h₂

theorem isComponentOf_top_of_normal {L K : Subgroup M} (hK : K.Normal) (hL : IsComponentOf L K) :
    IsComponentOf L ⊤ :=
  ⟨le_top, isSubnormal_trans' hL.2.1 (IsSubnormal.step le_top inferInstance
    (IsSubnormal.refl ⊤)), hL.2.2⟩

theorem isComponentOf_map_mulEquiv {M' : Type*} [Group M'] (e : M ≃* M') {L K : Subgroup M}
    (hL : IsComponentOf L K) : IsComponentOf (L.map e.toMonoidHom) (K.map e.toMonoidHom) :=
  ⟨Subgroup.map_mono hL.1, CFSG.ComponentClassification.Components.chain_map _ hL.2.1,
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (L.equivMapOfInjective e.toMonoidHom e.injective).symm hL.2.2⟩

theorem map_conj_eq_of_normal {K : Subgroup M} (hK : K.Normal) (g : M) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hK.conj_mem y hy g
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have := hK.conj_mem x hx g⁻¹
      rwa [inv_inv] at this
    · simp [MulAut.conj_apply, mul_assoc]

theorem isComponentOf_conj {L K : Subgroup M} (hK : K.Normal) (hL : IsComponentOf L K) (g : M) :
    IsComponentOf (L.map (MulAut.conj g).toMonoidHom) K := by
  have h := isComponentOf_map_mulEquiv (MulAut.conj g) hL
  rwa [map_conj_eq_of_normal hK g] at h

theorem isSubnormal_of_isComponentOf {L : Subgroup M} (hL : IsComponentOf L ⊤) :
    L.IsSubnormal :=
  CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
    Subgroup.IsSubnormal.top

end Chains

section Top

variable {M : Type} [Group M] [Finite M]

theorem goldschmidtOddCore_eq_bot_of_isSubnormal (hO : goldschmidtOddCore M = ⊥)
    {S : Subgroup M} (hS : S.IsSubnormal) : goldschmidtOddCore S = ⊥ := by
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hS
  rw [← goldschmidtOddCore_eq_pPrimeCore M, hO, le_bot_iff] at h1
  rw [goldschmidtOddCore_eq_pPrimeCore]
  exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).mp h1

theorem oddCoreOf_eq_bot_of_isSubnormal (hO : goldschmidtOddCore M = ⊥) {S : Subgroup M}
    (hS : S.IsSubnormal) : oddCoreOf S = ⊥ := by
  rw [oddCoreOf, goldschmidtOddCore_eq_bot_of_isSubnormal hO hS, Subgroup.map_bot]

theorem goldschmidtOddCore_top_eq_bot (hO : goldschmidtOddCore M = ⊥) :
    goldschmidtOddCore (⊤ : Subgroup M) = ⊥ :=
  goldschmidtOddCore_eq_bot_of_isSubnormal hO Subgroup.IsSubnormal.top

@[expose] noncomputable def topQuot (hO : goldschmidtOddCore M = ⊥) :
    M ≃* (⊤ : Subgroup M) ⧸ goldschmidtOddCore (⊤ : Subgroup M) :=
  Subgroup.topEquiv.symm.trans (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (goldschmidtOddCore_top_eq_bot hO).symm))

theorem topQuot_apply (hO : goldschmidtOddCore M = ⊥) (x : M) :
    topQuot hO x = (QuotientGroup.mk (⟨x, trivial⟩ : (⊤ : Subgroup M)) :
      (⊤ : Subgroup M) ⧸ goldschmidtOddCore (⊤ : Subgroup M)) :=
  rfl

theorem barOf_top_eq_map (hO : goldschmidtOddCore M = ⊥) (B : Subgroup M) :
    barOf ⊤ B = B.map (topQuot hO).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x : M), hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, trivial⟩, hx, rfl⟩

theorem preOf_top_eq_comap (hO : goldschmidtOddCore M = ⊥)
    (L : Subgroup ((⊤ : Subgroup M) ⧸ goldschmidtOddCore (⊤ : Subgroup M))) :
    preOf ⊤ L = L.comap (topQuot hO).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, trivial⟩, hx, rfl⟩

theorem preOf_top_barOf (hO : goldschmidtOddCore M = ⊥) (B : Subgroup M) :
    preOf ⊤ (barOf ⊤ B) = B := by
  rw [preOf_top_eq_comap hO, barOf_top_eq_map hO]
  exact Subgroup.comap_map_eq_self_of_injective (topQuot hO).injective B

theorem preOf_top_centralizer_barOf (hO : goldschmidtOddCore M = ⊥) (B : Subgroup M) :
    preOf ⊤ (Subgroup.centralizer (barOf ⊤ B : Set _)) = Subgroup.centralizer (B : Set M) := by
  rw [preOf_top_eq_comap hO, barOf_top_eq_map hO]
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h b hb
    apply (topQuot hO).injective
    have := h _ ⟨b, hb, rfl⟩
    simpa using this
  · rintro h _ ⟨b, hb, rfl⟩
    have := congrArg (topQuot hO) (h b hb)
    simpa using this

end Top

section Closure

variable {M : Type*} [Group M]

theorem normalClosureIn_top_normal (A : Subgroup M) : (normalClosureIn ⊤ A).Normal := by
  have h1 : (Subgroup.normalClosure ((A.subgroupOf ⊤ : Subgroup (⊤ : Subgroup M)) :
      Set (⊤ : Subgroup M))).Normal := Subgroup.normalClosure_normal
  exact h1.map _ (fun x => ⟨⟨x, trivial⟩, rfl⟩)

theorem le_normalClosureIn_top (A : Subgroup M) : A ≤ normalClosureIn ⊤ A :=
  fun x hx => ⟨⟨x, trivial⟩, Subgroup.subset_normalClosure hx, rfl⟩

end Closure

section Components

variable {M : Type} [Group M] [Finite M]

structure CompFacts (A L : Subgroup M) : Prop where
  le : L ≤ normalClosureIn ⊤ A
  comp : IsComponentOf L ⊤
  sstar : IsSStarIn L (A ⊓ L)
  closure : normalClosureIn L (A ⊓ L) = L
  split : A = A ⊓ L ⊔ A ⊓ Subgroup.centralizer (L : Set M)
  types : IsGoldTypeI L ∨ IsGoldTypeII L
  noncentral : ∃ x ∈ A ⊓ L, ∃ y ∈ L, x * y ≠ y * x
  center : IsPGroup 2 (Subgroup.center L)

theorem isGoldType_of_sstar {L B : Subgroup M} (hO : goldschmidtOddCore M = ⊥)
    (hL : IsComponentOf L ⊤) (hS : IsSStarIn L B) (hcl : normalClosureIn L B = L) :
    IsGoldTypeI L ∨ IsGoldTypeII L := by
  obtain ⟨-, -, T, -, -, -, -, -, -, hK4⟩ := hS
  set K := normalClosureIn L B with hK
  have hKsn : K.IsSubnormal := by
    rw [hcl]
    exact isSubnormal_of_isComponentOf hL
  have hOK : goldschmidtOddCore K = ⊥ := goldschmidtOddCore_eq_bot_of_isSubnormal hO hKsn
  let eQ : K ⧸ goldschmidtOddCore K ≃* L :=
    ((QuotientGroup.quotientMulEquivOfEq hOK).trans QuotientGroup.quotientBot).trans
      (MulEquiv.subgroupCongr hcl)
  let e : (⊤ : Subgroup (K ⧸ goldschmidtOddCore K)) ≃* L := Subgroup.topEquiv.trans eQ
  have hc : IsComponentOf (⊤ : Subgroup (K ⧸ goldschmidtOddCore K)) ⊤ :=
    ⟨le_rfl, IsSubnormal.refl _,
      CFSG.ComponentClassification.Components.quasisimple_of_equiv e hL.2.2⟩
  rcases hK4 ⊤ hc with h | h
  · exact Or.inl (SStarTransport.isGoldTypeI_of_mulEquiv e h)
  · exact Or.inr (SStarTransport.isGoldTypeII_of_mulEquiv e h)

omit [Finite M] in
theorem exists_mul_ne_of_quasisimple {L : Subgroup M} (hL : CFSG.Open.IsQuasisimple L) :
    ∃ a b : L, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  have hZ : Subgroup.center L = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact hab y x
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2
  have hsub : Subsingleton (L ⧸ Subgroup.center L) := by
    rw [hZ]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton _ hsub

theorem compFacts
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A)
    {L : Subgroup M} (hL : IsComponentOf L (normalClosureIn ⊤ A)) : CompFacts A L := by
  have hLtop : IsComponentOf L ⊤ := isComponentOf_top_of_normal (normalClosureIn_top_normal A) hL
  have hc : IsComponentOf (barOf ⊤ L) (barOf ⊤ (normalClosureIn ⊤ A)) := by
    rw [barOf_top_eq_map hO, barOf_top_eq_map hO]
    exact isComponentOf_map_mulEquiv _ hL
  obtain ⟨h1, h2, h3⟩ := (G31 M ⊤ A hS).1 _ hc
  rw [preOf_top_barOf hO] at h1 h2 h3
  rw [preOf_top_centralizer_barOf hO] at h3
  have hLsn : L.IsSubnormal := isSubnormal_of_isComponentOf hLtop
  rw [oddCoreOf_eq_bot_of_isSubnormal hO hLsn, sup_bot_eq] at h2
  have hcl : normalClosureIn L (A ⊓ L) = L := h2.symm
  refine ⟨hL.1, hLtop, h1, hcl, h3, isGoldType_of_sstar hO hLtop h1 hcl, ?_,
    CFSG.isPGroup_of_nilpotent_normal (Subgroup.center L) inferInstance inferInstance
      (by
        rw [← goldschmidtOddCore_eq_pPrimeCore]
        exact goldschmidtOddCore_eq_bot_of_isSubnormal hO hLsn)⟩
  by_contra hcen
  push Not at hcen
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_quasisimple hL.2.2
  apply hab
  have h4 : ((A ⊓ L).subgroupOf L : Subgroup L) ≤ Subgroup.center L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcen x hx y y.2).symm
  have h5 : Subgroup.normalClosure (((A ⊓ L).subgroupOf L : Subgroup L) : Set L) ≤
      Subgroup.center L := Subgroup.normalClosure_le_normal h4
  have ha : (a : M) ∈ normalClosureIn L (A ⊓ L) := by rw [hcl]; exact a.2
  obtain ⟨a', ha', haa'⟩ := ha
  rw [show a' = a from Subtype.ext haa'] at ha'
  exact (Subgroup.mem_center_iff.mp (h5 ha') b).symm

end Components

section Gen

variable {M : Type} [Group M] [Finite M]

@[expose] noncomputable def phiTop (A : Subgroup M)
    (hOK : goldschmidtOddCore (normalClosureIn ⊤ A) = ⊥) :
    normalClosureIn ⊤ A ⧸ goldschmidtOddCore (normalClosureIn ⊤ A) →* M :=
  QuotientGroup.lift _ (normalClosureIn ⊤ A).subtype (by rw [hOK]; exact bot_le)

omit [Finite M] in
theorem phiTop_mk (A : Subgroup M) (hOK : goldschmidtOddCore (normalClosureIn ⊤ A) = ⊥)
    (k : normalClosureIn ⊤ A) : phiTop A hOK (QuotientGroup.mk k) = k := rfl

omit [Finite M] in
theorem phiTop_injective (A : Subgroup M) (hOK : goldschmidtOddCore (normalClosureIn ⊤ A) = ⊥) :
    Function.Injective (phiTop A hOK) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, phiTop_mk] at hx
  have hk : k = 1 := Subtype.ext hx
  rw [hk, QuotientGroup.mk_one]
  exact Subgroup.one_mem _

omit [Finite M] in
theorem phiTop_range (A : Subgroup M) (hOK : goldschmidtOddCore (normalClosureIn ⊤ A) = ⊥) :
    (phiTop A hOK).range = normalClosureIn ⊤ A := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    exact k.2
  · intro hx
    exact ⟨QuotientGroup.mk ⟨x, hx⟩, rfl⟩

theorem goldschmidtOddCore_normalClosureIn (hO : goldschmidtOddCore M = ⊥) (A : Subgroup M) :
    goldschmidtOddCore (normalClosureIn ⊤ A) = ⊥ :=
  goldschmidtOddCore_eq_bot_of_isSubnormal hO (normalClosureIn_top_normal A).isSubnormal

theorem exists_gen (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A) :
    ∃ Z₂ : Subgroup M, Z₂ ≤ A ∧
      (∀ z ∈ Z₂, ∀ k ∈ normalClosureIn ⊤ A, z * k = k * z) ∧
      ∀ X : Subgroup M, Z₂ ≤ X → (∀ L, IsComponentOf L (normalClosureIn ⊤ A) → L ≤ X) →
        normalClosureIn ⊤ A ≤ X := by
  obtain ⟨-, -, T, -, -, -, hK1, hK2, hK3, -⟩ := hS
  set K := normalClosureIn ⊤ A with hK
  have hOK : goldschmidtOddCore K = ⊥ := goldschmidtOddCore_normalClosureIn hO A
  set φ := phiTop A hOK with hφ
  refine ⟨(CFSG.Open.pCore 2 (K ⧸ goldschmidtOddCore K)).map φ, ?_, ?_, ?_⟩
  ·
    have h1 : CFSG.Open.pCore 2 (K ⧸ goldschmidtOddCore K) ≤ barOf K A := by
      rw [hK3]
      exact le_sup_left
    refine (Subgroup.map_mono h1).trans ?_
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ha
  ·
    rintro _ ⟨z, hz, rfl⟩ k hk
    have hzc := Subgroup.mem_center_iff.mp (hK2 hz) (QuotientGroup.mk ⟨k, hk⟩)
    have := congrArg φ hzc
    rw [map_mul, map_mul, hφ, phiTop_mk] at this
    exact this.symm
  · intro X hZX hLX
    have hle : (⊤ : Subgroup (K ⧸ goldschmidtOddCore K)) ≤ X.comap φ := by
      rw [← hK1]
      refine sup_le (Subgroup.map_le_iff_le_comap.mp hZX) (sSup_le fun L' hL' => ?_)
      have hc : IsComponentOf (L'.map φ) K := by
        refine ⟨?_, ?_, ?_⟩
        · rintro _ ⟨y, -, rfl⟩
          exact (phiTop_range A hOK).le ⟨y, rfl⟩
        · have := CFSG.ComponentClassification.Components.chain_map φ hL'.2.1
          rwa [← MonoidHom.range_eq_map, hφ, phiTop_range] at this
        · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
            (L'.equivMapOfInjective φ (phiTop_injective A hOK)).symm hL'.2.2
      exact Subgroup.map_le_iff_le_comap.mp (hLX _ hc)
    intro x hx
    obtain ⟨y, hy⟩ : x ∈ φ.range := by rw [hφ, phiTop_range]; exact hx
    rw [← hy]
    exact hle (Subgroup.mem_top y)

end Gen

end CFSG.Goldschmidt.G310
