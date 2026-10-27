module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.ComponentClassification CFSG.RankThreeCoreUniqueness

variable {G : Type} [Group G]

private theorem map_conj_eq_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    X.map (MulAut.conj g).toMonoidHom = X := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
      simpa using this
    · simp [MulAut.conj_apply, mul_assoc]

private theorem mem_normalizer_of_map_conj_le {S : Subgroup G} {g : G}
    (h₁ : S.map (MulAut.conj g).toMonoidHom ≤ S)
    (h₂ : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ S) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h₁ (Subgroup.mem_map_of_mem _ hx)
  · intro hx
    have := h₂ (Subgroup.mem_map_of_mem _ hx)
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem oUpperTwo_le_self (X : Subgroup G) : AS76b.oUpperTwo X ≤ X :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

private theorem map_oUpperTwo_le {G' : Type*} [Group G'] (f : G →* G') (X : Subgroup G) :
    (AS76b.oUpperTwo X).map f ≤ AS76b.oUpperTwo (X.map f) := by
  unfold AS76b.oUpperTwo
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hx, hodd⟩, rfl⟩
  exact ⟨Subgroup.mem_map_of_mem f hx, hodd.of_dvd_nat (orderOf_map_dvd f x)⟩

private theorem map_oUpperTwo_of_injective {G' : Type*} [Group G'] {f : G →* G'}
    (hf : Function.Injective f) (X : Subgroup G) :
    (AS76b.oUpperTwo X).map f = AS76b.oUpperTwo (X.map f) := by
  refine le_antisymm (map_oUpperTwo_le f X) ?_
  unfold AS76b.oUpperTwo
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro y ⟨hy, hodd⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact ⟨x, ⟨hx, by rwa [← orderOf_injective f hf x]⟩, rfl⟩

theorem IsSymThreeOrSUThreeTwo.of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : IsSymThreeOrSUThreeTwo Q) : IsSymThreeOrSUThreeTwo Q' := by
  rcases h with ⟨f⟩ | ⟨K, hK, hKf, hcard, ⟨f⟩⟩
  · exact Or.inl ⟨e.symm.trans f.some⟩
  · exact Or.inr ⟨K, hK, hKf, hcard, ⟨e.symm.trans f⟩⟩

private theorem closure_two_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : Subgroup.closure {y : Q' | ∃ k : ℕ, y ^ (2 ^ k) = 1} = ⊤) :
    Subgroup.closure {x : Q | ∃ k : ℕ, x ^ (2 ^ k) = 1} = ⊤ := by
  have h1 : (Subgroup.closure {y : Q' | ∃ k : ℕ, y ^ (2 ^ k) = 1}).map e.symm.toMonoidHom =
      ⊤ := by
    rw [h, Subgroup.map_top, MonoidHom.range_eq_top]
    exact e.symm.surjective
  rw [MonoidHom.map_closure] at h1
  rw [eq_top_iff, ← h1]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨y, ⟨k, hk⟩, rfl⟩
  exact ⟨k, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hk, map_one]⟩

private theorem closure_two_perm :
    Subgroup.closure {x : Equiv.Perm (Fin 3) | ∃ k : ℕ, x ^ (2 ^ k) = 1} = ⊤ := by
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap]
  refine Subgroup.closure_mono ?_
  rintro σ ⟨a, b, -, rfl⟩
  exact ⟨1, by rw [pow_one, pow_two, Equiv.swap_mul_self]⟩

private theorem cube_perm :
    ∀ x ∈ AS76b.oUpperTwo (⊤ : Subgroup (Equiv.Perm (Fin 3))), x ^ 3 = 1 := by
  have hmul : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1 := by decide
  have hinv : ∀ a : Equiv.Perm (Fin 3), a ^ 3 = 1 → a⁻¹ ^ 3 = 1 := by decide
  have hodd : ∀ y : Equiv.Perm (Fin 3), Odd (orderOf y) → y ^ 3 = 1 := by
    intro y hy
    have h23 : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 ∨ σ ^ 2 = 1 := by decide
    rcases h23 y with h | h
    · exact h
    · have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one h
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
      · rw [orderOf_eq_one_iff.mp h1]
        simp
      · rw [h1] at hy
        exact absurd hy (by decide)
  let T : Subgroup (Equiv.Perm (Fin 3)) :=
    { carrier := {x | x ^ 3 = 1}
      mul_mem' := fun ha hb => hmul _ _ ha hb
      one_mem' := one_pow 3
      inv_mem' := fun ha => hinv _ ha }
  have hle : AS76b.oUpperTwo (⊤ : Subgroup (Equiv.Perm (Fin 3))) ≤ T :=
    (Subgroup.closure_le _).mpr fun y hy => hodd y hy.2
  exact fun x hx => hle hx

private theorem cube_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : ∀ x ∈ AS76b.oUpperTwo (⊤ : Subgroup Q'), x ^ 3 = 1) :
    ∀ x ∈ AS76b.oUpperTwo (⊤ : Subgroup Q), x ^ 3 = 1 := by
  intro x hx
  have h1 : e x ∈ AS76b.oUpperTwo (⊤ : Subgroup Q') := by
    have := map_oUpperTwo_le e.toMonoidHom (⊤ : Subgroup Q) (Subgroup.mem_map_of_mem _ hx)
    rwa [Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective] at this
  apply e.injective
  rw [map_pow, map_one]
  exact h _ h1

private theorem barM_self_eq_top (M : Subgroup G) : barM M M = ⊤ := by
  unfold barM
  rw [Subgroup.subgroupOf_self, Subgroup.map_top, QuotientGroup.range_mk']

private theorem isQuasisimple_of_isTwoPrimeComponent_self {M : Subgroup G}
    (h : IsTwoPrimeComponent M M) : Open.IsQuasisimple (↥M ⧸ CFSG.pCore 2 ↥M) := by
  have h1 := h.component.2.2
  rw [barM_self_eq_top] at h1
  exact Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm h1

private theorem isTwoPrimeComponent_self_of {M : Subgroup G} (hp : ⁅M, M⁆ = M)
    (hq : Open.IsQuasisimple (↥M ⧸ CFSG.pCore 2 ↥M)) : IsTwoPrimeComponent M M where
  le := le_rfl
  subnormal := .refl M
  perfect := hp
  component := by
    rw [barM_self_eq_top]
    exact ⟨le_rfl, .refl _, Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hq⟩

private theorem nonempty_quotEquiv_map_conj (g : G) (I : Subgroup G) :
    Nonempty ((↥I ⧸ CFSG.pCore 2 ↥I) ≃*
      (↥(I.map (MulAut.conj g).toMonoidHom) ⧸
        CFSG.pCore 2 ↥(I.map (MulAut.conj g).toMonoidHom))) :=
  ⟨QuotientGroup.congr _ _ ((MulAut.conj g).subgroupMap I) (CFSG.pCore_map_iso 2 _)⟩

private theorem pCoreOf_map_conj (p : ℕ) (Y : Subgroup G) (g : G) :
    pCoreOf p (Y.map (MulAut.conj g).toMonoidHom) =
      (pCoreOf p Y).map (MulAut.conj g).toMonoidHom :=
  LieType.BorelTits.pCoreOf_map_mulEquiv p (MulAut.conj g) Y

theorem IsCZeroMember.map_conj {X I : Subgroup G} (h : IsCZeroMember X I) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    IsCZeroMember X (I.map (MulAut.conj g).toMonoidHom) := by
  have hX : X.map (MulAut.conj g).toMonoidHom = X := map_conj_eq_of_mem_normalizer hg
  refine ⟨?_, ?_, ?_⟩
  · calc I.map (MulAut.conj g).toMonoidHom ≤ X.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono h.le
      _ = X := hX
  · have := h.subnormal.map (MulAut.conj g).toMonoidHom
    rwa [hX] at this
  · obtain ⟨ε⟩ := nonempty_quotEquiv_map_conj g I
    rcases h.shape with ha | ⟨hp, hq⟩
    · refine Or.inl (isTwoPrimeComponent_self_of ?_ ?_)
      · rw [← Subgroup.map_commutator, ha.perfect]
      · exact Open.IsQuasisimple.of_mulEquiv ε.symm
          (isQuasisimple_of_isTwoPrimeComponent_self ha)
    · refine Or.inr ⟨?_, IsSymThreeOrSUThreeTwo.of_mulEquiv ε hq⟩
      calc pCoreOf 2 (I.map (MulAut.conj g).toMonoidHom)
          = (pCoreOf 2 I).map (MulAut.conj g).toMonoidHom := pCoreOf_map_conj 2 I g
        _ = (pCoreOf 2 X).map (MulAut.conj g).toMonoidHom := by rw [hp]
        _ = pCoreOf 2 (X.map (MulAut.conj g).toMonoidHom) := (pCoreOf_map_conj 2 X g).symm
        _ = pCoreOf 2 X := by rw [hX]

private theorem map_conj_iSup_cZero_le {Y : Subgroup G} (F : Subgroup G → Subgroup G)
    (hF : ∀ (I : Subgroup G) (g : G),
      (F I).map (MulAut.conj g).toMonoidHom = F (I.map (MulAut.conj g).toMonoidHom))
    {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    (⨆ I ∈ cZero Y, F I).map (MulAut.conj g).toMonoidHom ≤ ⨆ I ∈ cZero Y, F I := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun I hI => ?_
  rw [← Subgroup.map_le_iff_le_comap, hF]
  exact le_iSup₂ (f := fun J (_ : J ∈ cZero Y) => F J) _ (IsCZeroMember.map_conj hI hg)

private theorem normalizer_le_normalizer_iSup_cZero {Y : Subgroup G}
    (F : Subgroup G → Subgroup G)
    (hF : ∀ (I : Subgroup G) (g : G),
      (F I).map (MulAut.conj g).toMonoidHom = F (I.map (MulAut.conj g).toMonoidHom)) :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer ((⨆ I ∈ cZero Y, F I : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_of_map_conj_le (map_conj_iSup_cZero_le F hF hg)
    (map_conj_iSup_cZero_le F hF (Subgroup.inv_mem _ hg))

theorem le_normalizer_jZero (H L : Subgroup G) :
    Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) ≤ Subgroup.normalizer (jZero H L : Set G) :=
  normalizer_le_normalizer_iSup_cZero (fun I => I) fun _ _ => rfl

theorem le_normalizer_jOne (H L : Subgroup G) :
    Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) ≤ Subgroup.normalizer (jOne H L : Set G) :=
  normalizer_le_normalizer_iSup_cZero AS76b.oUpperTwo fun I g =>
    map_oUpperTwo_of_injective (MulAut.conj g).injective I

theorem jOne_le_jZero (H L : Subgroup G) : jOne H L ≤ jZero H L :=
  iSup₂_mono fun _ _ => oUpperTwo_le_self _

theorem jZero_le (H L : Subgroup G) : jZero H L ≤ H ⊓ L :=
  iSup₂_le fun _ hI => hI.le

theorem IsCZeroMember.le_jZero {H L I : Subgroup G} (h : IsCZeroMember (H ⊓ L) I) :
    I ≤ jZero H L :=
  le_iSup₂ (f := fun J (_ : J ∈ cZero (H ⊓ L)) => J) I h

theorem IsCZeroMember.oUpperTwo_le_jOne {H L I : Subgroup G} (h : IsCZeroMember (H ⊓ L) I) :
    AS76b.oUpperTwo I ≤ jOne H L :=
  le_iSup₂ (f := fun J (_ : J ∈ cZero (H ⊓ L)) => AS76b.oUpperTwo J) I h

section SUThreeTwo

variable (hSU : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
  Subgroup.closure {x : ↥(StatedSU 3 2 K) | ∃ k : ℕ, x ^ (2 ^ k) = 1} = ⊤ ∧
    ∀ x ∈ AS76b.oUpperTwo (⊤ : Subgroup ↥(StatedSU 3 2 K)), x ^ 3 = 1)
include hSU

theorem IsSymThreeOrSUThreeTwo.closure_two {Q : Type} [Group Q] (h : IsSymThreeOrSUThreeTwo Q) :
    Subgroup.closure {x : Q | ∃ k : ℕ, x ^ (2 ^ k) = 1} = ⊤ := by
  rcases h with ⟨f⟩ | ⟨K, hK, hKf, hcard, ⟨f⟩⟩
  · exact closure_two_of_mulEquiv f.some closure_two_perm
  · exact closure_two_of_mulEquiv f (hSU K hcard).1

theorem IsSymThreeOrSUThreeTwo.cube {Q : Type} [Group Q] (h : IsSymThreeOrSUThreeTwo Q) :
    ∀ x ∈ AS76b.oUpperTwo (⊤ : Subgroup Q), x ^ 3 = 1 := by
  rcases h with ⟨f⟩ | ⟨K, hK, hKf, hcard, ⟨f⟩⟩
  · exact cube_of_mulEquiv f.some cube_perm
  · exact cube_of_mulEquiv f (hSU K hcard).2

theorem IsCZeroMember.cube_mem {I : Subgroup G}
    (hb : IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I)) :
    ∀ x ∈ AS76b.oUpperTwo I, x ^ 3 ∈ pCoreOf 2 I := by
  intro x hx
  have hI : AS76b.oUpperTwo I = (AS76b.oUpperTwo (⊤ : Subgroup ↥I)).map I.subtype := by
    rw [map_oUpperTwo_of_injective I.subtype_injective, Subgroup.map_top, Subgroup.range_subtype]
  rw [hI] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥I) y ∈
      AS76b.oUpperTwo (⊤ : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I)) := by
    have := map_oUpperTwo_le (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) (⊤ : Subgroup ↥I)
      (Subgroup.mem_map_of_mem _ hy)
    rwa [Subgroup.map_top, QuotientGroup.range_mk'] at this
  have h3 := IsSymThreeOrSUThreeTwo.cube hSU hb _ h1
  have h4 : y ^ 3 ∈ CFSG.pCore 2 ↥I := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using h3
  exact Subgroup.mem_map_of_mem I.subtype h4

end SUThreeTwo

end CFSG.AGLEmbedding
