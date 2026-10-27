module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSymSub
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSymCore
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreeBase
import CFSG.GroupTheory.ABGLocalTools.RelativeStability

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Prod

open CFSG.Open Subgroup

@[expose] def ProdFactor (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* Equiv.Perm (Fin 3)) ∨ (CFSG.pCore 2 G = ⊥ ∧ CFSG.pCore 3 G = ⊥)

theorem exists_conj_mul_order_three :
    ∀ x : Equiv.Perm (Fin 3), x ≠ 1 →
      ∃ g : Equiv.Perm (Fin 3), x * (g * x * g⁻¹) ≠ 1 ∧ (x * (g * x * g⁻¹)) ^ 3 = 1 := by
  decide +kernel

theorem perm3_invol_inv_of_order_three :
    ∀ x : Equiv.Perm (Fin 3), x ^ 2 = 1 → x ≠ 1 →
      ∀ b : Equiv.Perm (Fin 3), b ^ 3 = 1 → b ≠ 1 → x * b * x⁻¹ = b⁻¹ := by
  decide +kernel

theorem pCore_two_perm_three : CFSG.pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨g, hg1, hg3⟩ := exists_conj_mul_order_three x hx1
  have hn : (CFSG.pCore 2 (Equiv.Perm (Fin 3))).Normal := CFSG.pCore_normal
  have hy : x * (g * x * g⁻¹) ∈ CFSG.pCore 2 (Equiv.Perm (Fin 3)) :=
    mul_mem hx (hn.conj_mem x hx g)
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := Equiv.Perm (Fin 3)) ⟨_, hy⟩
  have hk' : (x * (g * x * g⁻¹)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact hg1 (Sym.eq_one_of_pow_two_pow_three ⟨k, hk'⟩ ⟨1, by simpa using hg3⟩)

theorem pCore_two_eq_bot_of_prodFactor {G : Type} [Group G] (h : ProdFactor G) :
    CFSG.pCore 2 G = ⊥ := by
  rcases h with ⟨⟨e⟩⟩ | ⟨h2, -⟩
  · exact SymThree.pCore_eq_bot_of_mulEquiv 2 e pCore_two_perm_three
  · exact h2

theorem isPGroup_two_zpowers {K : Type*} [Group K] {x : K} (hx : x ^ 2 = 1) :
    IsPGroup 2 (zpowers x) := by
  have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)

section Basic

variable {ι : Type} [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]

theorem evalMonoidHom_surjective (i : ι) : Function.Surjective (Pi.evalMonoidHom G i) :=
  fun b => ⟨Pi.mulSingle i b, Pi.mulSingle_eq_same i b⟩

theorem conj_mulSingle (s : ∀ i, G i) (i : ι) (β : G i) :
    s * Pi.mulSingle i β * s⁻¹ = Pi.mulSingle i (s i * β * (s i)⁻¹) := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [Pi.mulSingle_eq_of_ne hji]

theorem normal_map_mulSingle (i : ι) :
    ((⊤ : Subgroup (G i)).map (MonoidHom.mulSingle G i)).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨x, -, rfl⟩ g
  refine ⟨g i * x * (g i)⁻¹, trivial, ?_⟩
  simpa using (conj_mulSingle g i x).symm

theorem nonempty_mulEquiv_perm_of_mem_pCore_three (hG : ∀ i, ProdFactor (G i))
    {a : ∀ i, G i} (ha : a ∈ CFSG.pCore 3 (∀ i, G i)) {i : ι} (hai : a i ≠ 1) :
    Nonempty (G i ≃* Equiv.Perm (Fin 3)) := by
  rcases hG i with h | ⟨-, h3⟩
  · exact h
  · exfalso
    have hle := CFSG.ABGLocalTools.map_pCore_le_of_surjective (p := 3) (Pi.evalMonoidHom G i)
      (evalMonoidHom_surjective i)
    have hmem := hle (Subgroup.mem_map_of_mem (Pi.evalMonoidHom G i) ha)
    rw [h3, Subgroup.mem_bot] at hmem
    exact hai hmem

theorem coord_eq_one_of_pCore_two {X : Subgroup (∀ i, G i)} (hXs : IsSubnormal X ⊤)
    {a s : ∀ i, G i} (hXeq : X = closure {a, s}) (hsX : s ∈ X) (hs2 : s ^ 2 = 1) {i : ι}
    (hO2 : CFSG.pCore 2 (G i) = ⊥) (hai : a i = 1) : s i = 1 := by
  have hsub : (X.map (Pi.evalMonoidHom G i)).IsSubnormal :=
    (IsSubnormal.top_iff.1 hXs).map (evalMonoidHom_surjective i)
  have hsi2 : s i ^ 2 = 1 := by simpa using congrFun hs2 i
  have hle : X.map (Pi.evalMonoidHom G i) ≤ zpowers (s i) := by
    rw [hXeq, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with h | h
    · rw [h]
      show a i ∈ zpowers (s i)
      rw [hai]
      exact one_mem _
    · rw [h]
      exact mem_zpowers _
  have hp : IsPGroup 2 (X.map (Pi.evalMonoidHom G i)) :=
    (isPGroup_two_zpowers hsi2).to_le hle
  have h1 : X.map (Pi.evalMonoidHom G i) ≤ CFSG.pCore 2 (G i) :=
    Sym.le_pCore_of_subnormal 2 hsub hp
  rw [hO2] at h1
  exact Subgroup.mem_bot.1 (h1 (Subgroup.mem_map_of_mem (Pi.evalMonoidHom G i) hsX))

end Basic

section Product

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
  [∀ i, Finite (G i)]

theorem exists_mulSingle_eq_of_subnormal_symThree (hG : ∀ i, ProdFactor (G i))
    {X : Subgroup (∀ i, G i)} (hX : Sym.IsSymThree X) (hXs : IsSubnormal X ⊤) :
    ∃ i, Nonempty (G i ≃* Equiv.Perm (Fin 3)) ∧
      X = (⊤ : Subgroup (G i)).map (MonoidHom.mulSingle G i) := by
  classical
  obtain ⟨a, haX, ha1, ha3, hXa, ⟨s, hsX, hs2, hs1⟩, hord⟩ := Sym.symThree_data hX
  obtain ⟨hinv, hXeq⟩ := hXa s hsX hs2 hs1
  have haN : a ∈ CFSG.pCore 3 (∀ i, G i) := Sym.mem_pCore_three hX hXs haX ha3 ha1
  obtain ⟨i, hai⟩ : ∃ i, a i ≠ 1 := by
    by_contra h
    push Not at h
    exact ha1 (funext h)
  obtain ⟨e⟩ := nonempty_mulEquiv_perm_of_mem_pCore_three hG haN hai
  have ha3i : a i ^ 3 = 1 := by simpa using congrFun ha3 i
  have hs2i : s i ^ 2 = 1 := by simpa using congrFun hs2 i
  have hinvi : s i * a i * (s i)⁻¹ = (a i)⁻¹ := by simpa using congrFun hinv i
  have hs1i : s i ≠ 1 := by
    intro h
    rw [h, one_mul, inv_one, mul_one] at hinvi
    apply hai
    have h2 : a i ^ 2 = 1 := by
      calc a i ^ 2 = a i * a i := pow_two _
        _ = a i * (a i)⁻¹ := by rw [← hinvi]
        _ = 1 := mul_inv_cancel _
    calc a i = a i ^ 3 * (a i ^ 2)⁻¹ := by group
      _ = 1 := by rw [ha3i, h2]; group
  have hconj : ∀ β : G i, β ^ 3 = 1 → β ≠ 1 → s i * β * (s i)⁻¹ = β⁻¹ := by
    intro β hβ3 hβ1
    apply e.injective
    rw [map_mul, map_mul, map_inv, map_inv]
    refine perm3_invol_inv_of_order_three (e (s i)) ?_ ?_ (e β) ?_ ?_
    · rw [← map_pow, hs2i, map_one]
    · exact fun h => hs1i (e.injective (h.trans (map_one e).symm))
    · rw [← map_pow, hβ3, map_one]
    · exact fun h => hβ1 (e.injective (h.trans (map_one e).symm))
  have hpow : ∀ β : G i, β ^ 3 = 1 → (Pi.mulSingle i β : ∀ j, G j) ^ 3 = 1 := by
    intro β hβ3
    have h := (MonoidHom.mulSingle G i).map_pow β 3
    rw [hβ3, map_one] at h
    simpa using h.symm
  have hmemX : ∀ β : G i, β ^ 3 = 1 → β ≠ 1 → (Pi.mulSingle i β : ∀ j, G j) ∈ X := by
    intro β hβ3 hβ1
    refine Sym.mem_of_inv_involution hX hXs hsX hs2 hs1 (hpow β hβ3) ?_
    rw [conj_mulSingle, hconj β hβ3 hβ1]
    exact Pi.mulSingle_inv i β
  have hm1 : (Pi.mulSingle i (a i) : ∀ j, G j) ≠ 1 := by
    intro h
    apply hai
    simpa using congrFun h i
  have hma := hord _ (hmemX (a i) ha3i hai) (hpow (a i) ha3i) hm1
  have hak : ∀ k, k ≠ i → a k = 1 := by
    intro k hk
    rcases hma with h | h <;> simpa [Pi.mulSingle_eq_of_ne hk] using (congrFun h k).symm
  have hsk : ∀ k, k ≠ i → s k = 1 := fun k hk =>
    coord_eq_one_of_pCore_two hXs hXeq hsX hs2 (pCore_two_eq_bot_of_prodFactor (hG k))
      (hak k hk)
  refine ⟨i, ⟨e⟩, ?_⟩
  set A : Subgroup (∀ j, G j) := (⊤ : Subgroup (G i)).map (MonoidHom.mulSingle G i) with hA
  have hsupp : ∀ x : ∀ j, G j, (∀ k, k ≠ i → x k = 1) → x ∈ A := by
    intro x hx
    refine ⟨x i, trivial, ?_⟩
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hx j hji, Pi.mulSingle_eq_of_ne hji]
  have hle : X ≤ A := by
    rw [hXeq, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hsupp _ hak
    · exact hsupp _ hsk
  haveI : Finite X := Sym.finite_symThree hX
  have hinj : Function.Injective (MonoidHom.mulSingle G i) := Pi.mulSingle_injective i
  have hAcard : Nat.card A = 6 := by
    rw [hA, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      SymThree.card_eq_six_of_mulEquiv e]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hAcard, Sym.card_symThree hX])

end Product

theorem normal_of_subnormal_symThree_of_equiv {R : Type} [Group R] {ι : Type} [Fintype ι]
    [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (hG : ∀ i, ProdFactor (G i)) (e : R ≃* ∀ i, G i) {X : Subgroup R}
    (hX : Sym.IsSymThree X) (hXs : IsSubnormal X ⊤) : X.Normal := by
  have hXs' : IsSubnormal (X.map e.toMonoidHom) ⊤ :=
    IsSubnormal.top_iff.2 ((IsSubnormal.top_iff.1 hXs).map e.surjective)
  have hX' : Sym.IsSymThree (X.map e.toMonoidHom) := by
    obtain ⟨eX⟩ := hX
    exact ⟨(X.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eX⟩
  obtain ⟨i, -, hi⟩ := exists_mulSingle_eq_of_subnormal_symThree hG hX' hXs'
  have hn : (X.map e.toMonoidHom).Normal := hi ▸ normal_map_mulSingle i
  have h := hn.comap e.toMonoidHom
  rwa [Subgroup.comap_map_eq_self_of_injective e.injective] at h

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Prod
