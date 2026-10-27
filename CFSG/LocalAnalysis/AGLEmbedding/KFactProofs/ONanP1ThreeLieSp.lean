module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieWeakCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieDefs
public import CFSG.LieType.Steinberg.Classical.Symplectic.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenAbstract
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier

public section

namespace CFSG.AGLEmbedding.P1Lie

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem TauCeti.GLSymplecticFin

section Sp

variable {n : ℕ} {F : Type} [Field F]

@[expose] def toStdSpHom (n : ℕ) : (Fin n → ℤ) →+ (Fin n → ℤ) :=
  AddMonoidHom.mk' (toStd n) fun v w => by
    funext a
    simp only [toStd, Pi.add_apply]
    split_ifs <;> ring

theorem toStdSpHom_apply (v : Fin n → ℤ) : toStdSpHom n v = toStd n v := rfl

theorem stdVec_support (r : RootSubgroupIndex n) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : ¬ (stdVec r i ≠ 0 ∧ stdVec r j ≠ 0 ∧ stdVec r k ≠ 0) := by
  rintro ⟨h1, h2, h3⟩
  rcases r with a | a | ⟨a, b, hab⟩ | ⟨a, b, hab⟩ | ⟨a, b, hab⟩ <;>
    simp only [stdVec, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.single_apply,
      Fin.ext_iff, ne_eq] at h1 h2 h3 hij hik hjk <;>
    split_ifs at h1 h2 h3 <;> simp_all

theorem rootsC_support {ε : Fin n → ℤ} (hε : ε ∈ roots (isFiniteType_cartanC n) ∅) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (toStdSpHom n ε i ≠ 0 ∧ toStdSpHom n ε j ≠ 0 ∧ toStdSpHom n ε k ≠ 0) := by
  rw [roots_eq] at hε
  obtain ⟨r, hr⟩ := hε
  rw [toStdSpHom_apply, ← hr]
  exact stdVec_support r hij hik hjk

theorem rootsC_le_two {ε : Fin n → ℤ} (hε : ε ∈ roots (isFiniteType_cartanC n) ∅) (i : Fin n) :
    toStdSpHom n ε i ≤ 2 := by
  rw [roots_eq] at hε
  obtain ⟨r, hr⟩ := hε
  rw [toStdSpHom_apply, ← hr]
  rcases r with a | a | ⟨a, b, hab⟩ | ⟨a, b, hab⟩ | ⟨a, b, hab⟩ <;>
    simp only [stdVec, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.single_apply]
      <;> (try simp only [nsmul_eq_mul, Nat.cast_ofNat]) <;> split_ifs <;> omega

@[expose] def cSum (n a b : ℕ) : Fin n → ℤ := fun k =>
  if k.val < a then 0 else if k.val < b then 1 else if k.val + 1 < n then 2 else 1

@[expose] def cLong (n a : ℕ) : Fin n → ℤ := fun k =>
  if k.val < a then 0 else if k.val + 1 < n then 2 else 1

theorem toStd_cSum {a b : ℕ} (hab : a < b) (hb : b < n) :
    toStd n (cSum n a b) = Pi.single (⟨a, by omega⟩ : Fin n) 1 + Pi.single (⟨b, hb⟩ : Fin n) 1 := by
  funext x
  simp only [toStd, cSum, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem toStd_cLong {a : ℕ} (ha : a + 1 < n) :
    toStd n (cLong n a) = 2 • Pi.single (⟨a, by omega⟩ : Fin n) 1 := by
  funext x
  simp only [toStd, cLong, Pi.smul_apply, Pi.single_apply, Fin.ext_iff, nsmul_eq_mul,
    Nat.cast_ofNat]
  split_ifs <;> omega

theorem cSum_mem_roots {a b : ℕ} (hab : a < b) (hb : b < n) :
    cSum n a b ∈ roots (isFiniteType_cartanC n) ∅ := by
  rw [roots_eq]
  exact ⟨.positiveSum ⟨a, by omega⟩ ⟨b, hb⟩ hab, (toStd_cSum hab hb).symm⟩

theorem cLong_mem_roots {a : ℕ} (ha : a + 1 < n) :
    cLong n a ∈ roots (isFiniteType_cartanC n) ∅ := by
  rw [roots_eq]
  exact ⟨.positiveLong ⟨a, by omega⟩, (toStd_cLong ha).symm⟩

theorem two_le_ht_cSum {a b : ℕ} (hab : a < b) (hb : b < n) : 2 ≤ ht (cSum n a b) :=
  two_le_ht_of_two_pos (fun k => by simp only [cSum]; split_ifs <;> omega)
    (i := ⟨a, by omega⟩) (j := ⟨n - 1, by omega⟩) (by simp [Fin.ext_iff]; omega)
    (by simp [cSum, hab]) (by simp only [cSum]; split_ifs <;> omega)

theorem two_le_ht_cLong {a : ℕ} (ha : a + 1 < n) : 2 ≤ ht (cLong n a) :=
  two_le_ht_of_two_pos (fun k => by simp only [cLong]; split_ifs <;> omega)
    (i := ⟨a, by omega⟩) (j := ⟨n - 1, by omega⟩) (by simp [Fin.ext_iff]; omega)
    (by simp [cLong, ha]) (by simp only [cLong]; split_ifs <;> omega)

theorem toStdSpHom_cSum {a b : ℕ} (hab : a < b) (hb : b < n) (i : Fin n) :
    toStdSpHom n (cSum n a b) i = (if i.val = a then 1 else 0) + (if i.val = b then 1 else 0) := by
  rw [toStdSpHom_apply, toStd_cSum hab hb]
  simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]

theorem toStdSpHom_cLong {a : ℕ} (ha : a + 1 < n) (i : Fin n) :
    toStdSpHom n (cLong n a) i = if i.val = a then 2 else 0 := by
  rw [toStdSpHom_apply, toStd_cLong ha]
  simp only [Pi.smul_apply, Pi.single_apply, Fin.ext_iff, nsmul_eq_mul, Nat.cast_ofNat]
  split_ifs <;> simp

theorem cSum_ne_cLong (hn : 2 ≤ n) : cSum n 0 1 ≠ cLong n 0 := by
  intro h
  have h1 := congrArg (fun v => toStdSpHom n v ⟨0, by omega⟩) h
  simp only [toStdSpHom_cSum (by omega : 0 < 1) (by omega : 1 < n),
    toStdSpHom_cLong (by omega : 0 + 1 < n)] at h1
  simp at h1

theorem commRoots_cSum_cLong (hn : 2 ≤ n) :
    CommRoots (rootDatum n F) (cSum n 0 1) (cLong n 0) := by
  refine commRoots_of_bound (D := rootDatum n F) (toStdSpHom n) rfl (i := ⟨0, by omega⟩) (M := 2)
    (fun ε hε => rootsC_le_two hε _) (cSum_mem_roots (by omega) (by omega))
    (cLong_mem_roots (by omega)) ?_ ?_ ?_ ?_ ?_
  · exact cSum_ne_cLong hn
  · intro i
    change 0 ≤ toStdSpHom n (cSum n 0 1) i
    rw [toStdSpHom_cSum (by omega) (by omega)]
    split_ifs <;> omega
  · intro i
    change 0 ≤ toStdSpHom n (cLong n 0) i
    rw [toStdSpHom_cLong (by omega)]
    split_ifs <;> omega
  · refine ⟨⟨0, by omega⟩, ?_⟩
    change toStdSpHom n (cSum n 0 1) ⟨0, by omega⟩ ≠ 0
    rw [toStdSpHom_cSum (by omega) (by omega)]
    simp
  · intro a' b' ha' hb'
    change 2 < (a' : ℤ) * toStdSpHom n (cSum n 0 1) ⟨0, by omega⟩ +
        b' * toStdSpHom n (cLong n 0) ⟨0, by omega⟩
    rw [toStdSpHom_cSum (by omega) (by omega), toStdSpHom_cLong (by omega)]
    simp
    omega

theorem weakCore_sp {p f : ℕ} (hp : p.Prime) [CharP F p] [Finite F] (hF : Nat.card F = p ^ f)
    (hn : 3 ≤ n ∨ (n = 2 ∧ 2 ≤ f)) :
    GLBWeakCore p (posUnipotent (rootDatum n F)) = ⊤ := by
  have hX : ∀ γ ∈ (rootDatum n F).roots, IsPGroup p ((rootDatum n F).rootGroup γ) := fun γ hγ =>
    isPGroup_of_isParametrization Sp.isParametrization hγ
  rcases hn with hn | ⟨rfl, hf⟩
  · exact weakCore_posUnipotent_eq_top_of_image_triple (D := rootDatum n F) (isCTGroupDatum n F)
      (steinbergExtras n F) hp (by change 2 ≤ n; omega) hX rfl (toStdSpHom n)
      (fun ε hε i j k => rootsC_support hε) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (k := ⟨2, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]) (cSum_mem_roots (by omega) (by omega))
      (cSum_mem_roots (by omega) (by omega)) (cSum_mem_roots (by omega) (by omega))
      (toStd_cSum (by omega) (by omega)) (toStd_cSum (by omega) (by omega))
      (toStd_cSum (by omega) (by omega)) (two_le_ht_cSum (by omega) (by omega))
      (two_le_ht_cSum (by omega) (by omega)) (two_le_ht_cSum (by omega) (by omega))
  · refine weakCore_posUnipotent_eq_top_of_pair (isCTGroupDatum 2 F) (steinbergExtras 2 F) hp
      (by change 2 ≤ 2; omega) Sp.isParametrization hF hf (γ₁ := cSum 2 0 1) (γ₂ := cLong 2 0) ?_
      (cSum_ne_cLong le_rfl) (commRoots_cSum_cLong le_rfl)
    exact (Finset.forall_mem_insert _ _ _).2 ⟨posData_of_two_le_ht rfl
      (cSum_mem_roots (by omega) (by omega)) (two_le_ht_cSum (by omega) (by omega)),
      fun γ hγ => by
        rw [Finset.mem_singleton.1 hγ]
        exact posData_of_two_le_ht rfl (cLong_mem_roots (by omega)) (two_le_ht_cLong (by omega))⟩

open CFSG.AGLEmbedding.CharPGen in
theorem exists_pGroup_weakCore_sp {G : Type} [Group G] [Finite G] [Finite F] {p f : ℕ}
    [Fact p.Prime] [CharP F p] (hF : Nat.card F = p ^ f) (hn : 3 ≤ n ∨ (n = 2 ∧ 2 ≤ f))
    (e : G ≃* StatedProj (StatedSp n F)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBWeakCore p P = ⊤ := by
  have hn0 : 0 < n := by omega
  have hext := steinbergExtras n F
  have hX : ∀ γ ∈ (rootDatum n F).roots, IsPGroup p ((rootDatum n F).rootGroup γ) := fun γ hγ =>
    isPGroup_of_isParametrization Sp.isParametrization hγ
  have hU : IsPGroup p (posUnipotent (rootDatum n F)) := isPGroup_iSup_pos hext hX
  let π : StatedSp n F →* G := e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hinj : ∀ x ∈ posUnipotent (rootDatum n F), π x = 1 → x = 1 := by
    intro x hx hx1
    have hmk : (QuotientGroup.mk' _ x : StatedProj (StatedSp n F)) = 1 :=
      e.symm.injective (by rw [map_one]; exact hx1)
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    exact eq_one_of_mem_statedScalars_of_pow (Sum.inl ⟨0, hn0⟩)
      (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff x).1 hmk)) (congrArg Subtype.val hk)
  exact ⟨(posUnipotent (rootDatum n F)).map π, hU.map π,
    weakCore_map_eq_top Fact.out π hπ hinj (weakCore_sp Fact.out hF hn)⟩

theorem exists_pGroup_weakCore_of_model_psp {G : Type} [Group G] [Finite G] {n p f : ℕ}
    (h : StatedClassicalModel G .PSp n p f) (hn : 3 ≤ n ∨ (n = 2 ∧ 2 ≤ f)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBWeakCore p P = ⊤ := by
  obtain ⟨⟨hp, hf, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact exists_pGroup_weakCore_sp hcard hn e

end Sp

end CFSG.AGLEmbedding.P1Lie

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def IsWeakSpIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, 2 ≤ q.exponent ∧ d.1 = .B 2 q) ∨
    ∃ (r : ℕ) (q : TauCeti.PrimePower), 3 ≤ r ∧ d.1 = .C r q

theorem weakCharPGenAt_sp : WeakCharPGenAt IsWeakSpIndex := by
  intro K _ _ _ _ d hd ⟨e⟩ p hp hp2 hchar hrank T
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  rcases hd with ⟨q, hq, hd⟩ | ⟨r, q, hr, hd⟩
  · simp only at hd hchar
    subst hd
    have hpq : p = q.p := by simpa using hchar
    subst hpq
    obtain ⟨P, hP, hcore⟩ := P1Lie.exists_pGroup_weakCore_of_model_psp
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) (Or.inr ⟨rfl, hq⟩)
    exact P1Lie.weakCore_eq_top_of_pGroup hp hP hcore T
  · simp only at hd hchar
    subst hd
    have hpq : p = q.p := by simpa using hchar
    subst hpq
    obtain ⟨P, hP, hcore⟩ := P1Lie.exists_pGroup_weakCore_of_model_psp
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e) (Or.inl hr)
    exact P1Lie.weakCore_eq_top_of_pGroup hp hP hcore T

end CFSG.AGLEmbedding
