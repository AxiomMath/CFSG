module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeG2
import CFSG.LocalAnalysis.AGLEmbeddingD2.AbelianSylowGL
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisEngine

public section

namespace CFSG.AGLEmbeddingD2.HeisG2

section CentralProduct

variable {G A B : Type*} [Group G] [Group A] [Group B]

theorem exists_isPGroup_map_eq_of_le_range {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (ψ : X →* G) {P : Subgroup G} (hP : P ≤ ψ.range) (hp : IsPGroup p P) :
    ∃ U : Subgroup X, IsPGroup p U ∧ U.map ψ = P := by
  have hU₁ : IsPGroup p (P.subgroupOf ψ.range) := hp.comap_subtype
  obtain ⟨U, -, hU, hUm⟩ := HeisEngine.exists_isPGroup_map_eq ψ.rangeRestrict_surjective hU₁
  refine ⟨U, hU, ?_⟩
  have e : U.map ψ = (U.map ψ.rangeRestrict).map ψ.range.subtype := by
    rw [Subgroup.map_map]
    rfl
  rw [e, hUm, Subgroup.map_subgroupOf_eq_of_le hP]

theorem isMulCommutative_of_isPGroup_of_commute [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
    (f : A →* G) (g : B →* G) (hfg : ∀ a b, Commute (f a) (g b))
    (hA : ∀ Q : Subgroup A, IsPGroup p Q → IsMulCommutative Q)
    (hB : ∀ Q : Subgroup B, IsPGroup p Q → IsMulCommutative Q) {P : Subgroup G}
    (hP : P ≤ f.range ⊔ g.range) (hp : IsPGroup p P) : IsMulCommutative P := by
  obtain ⟨U, hU, rfl⟩ := exists_isPGroup_map_eq_of_le_range (MonoidHom.noncommCoprod f g hfg)
    (by rwa [MonoidHom.noncommCoprod_range]) hp
  have h1 := hA _ (hU.map (MonoidHom.fst A B))
  have h2 := hB _ (hU.map (MonoidHom.snd A B))
  refine IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  have e1 := setLike_mul_comm (Subgroup.mem_map_of_mem (MonoidHom.fst A B) hx)
    (Subgroup.mem_map_of_mem (MonoidHom.fst A B) hy)
  have e2 := setLike_mul_comm (Subgroup.mem_map_of_mem (MonoidHom.snd A B) hx)
    (Subgroup.mem_map_of_mem (MonoidHom.snd A B) hy)
  simp only [MonoidHom.coe_fst, MonoidHom.coe_snd] at e1 e2
  rw [← map_mul, ← map_mul]
  congr 1
  exact Prod.ext e1 e2

end CentralProduct

section SL2

theorem isMulCommutative_of_isPGroup_five_sl2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hQ : IsPGroup 5 Q) :
    IsMulCommutative Q := by
  have := Fintype.ofFinite F
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  refine AbelianSylowGL.isMulCommutative_of_isPGroup_five_of_injective_GL_two_pow (f := f) hf
    ?_ Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective Q hQ
  have h : (f : ℕ) % 2 = 1 ∨ (f : ℕ) % 4 = 2 ∨ (f : ℕ) % 4 = 0 := by omega
  rcases h with h | h | h
  · exact Or.inl ⟨Nat.odd_iff.2 h, by norm_num⟩
  · exact Or.inr (Or.inl ⟨h, by norm_num⟩)
  · exact Or.inr (Or.inr ⟨Nat.dvd_of_mod_eq_zero h, by norm_num⟩)

end SL2

section Square

theorem exists_unit_sq_eq {K : Type} [Field K] [Finite K] [CharP K 2] (s : Kˣ) :
    ∃ u : Kˣ, u ^ 2 = s := by
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  obtain ⟨u, hu⟩ := (PerfectRing.bijective_frobenius (R := K) (p := 2)).2 (s : K)
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact s.ne_zero (by simpa using hu.symm)
  exact ⟨Units.mk0 u hu0, Units.ext (by simpa using hu)⟩

end Square

section Torus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

variable
  {τ : Tag} {F : RootOperatorFamily τ} {K : Type} [Field K]

theorem torusElement_inv (i : Fin τ.rank) (u : Kˣ) :
    (torusElement τ K i u)⁻¹ = torusElement τ K i u⁻¹ :=
  (map_inv (torusHom K i) u).symm

theorem commute_torusElement_mul_inv_xPar_single (k i : Fin τ.rank) {t u : Kˣ}
    (h : u ^ 2 = t ^ τ.cartan k i) (c : K) :
    Commute (torusElement τ K k t * (torusElement τ K i u)⁻¹) (xPar F (Pi.single i 1) c) := by
  have hs : ∀ l, ∑ j, τ.cartan l j * (simpleRoot τ i).1 j = τ.cartan l i := fun l => by
    simp [simpleRoot, Pi.single_apply]
  refine (mul_inv_eq_iff_eq_mul).1 ?_
  rw [xPar_simple, torusElement_inv]
  calc _ = torusElement τ K k t * (torusElement τ K i u⁻¹ * F.eltElement (simpleRoot τ i) c *
        (torusElement τ K i u⁻¹)⁻¹) * (torusElement τ K k t)⁻¹ := by group
    _ = F.eltElement (simpleRoot τ i) c := by
      rw [F.torusElement_mul_eltElement_mul_inv, hs, F.torusElement_mul_eltElement_mul_inv, hs]
      congr 1
      have e : (t ^ τ.cartan k i : Kˣ) * u⁻¹ ^ τ.cartan i i = 1 := by
        rw [Tag.cartan_self, ← h, zpow_ofNat, inv_pow, mul_inv_cancel]
      rw [← mul_assoc, ← Units.val_mul, e, Units.val_one, one_mul]

theorem commute_torusElement_mul_inv_xPar_neg_single (k i : Fin τ.rank) {t u : Kˣ}
    (h : u ^ 2 = t ^ τ.cartan k i) (c : K) :
    Commute (torusElement τ K k t * (torusElement τ K i u)⁻¹) (xPar F (-Pi.single i 1) c) := by
  have hs : ∀ l, ∑ j, τ.cartan l j * (-simpleRoot τ i).1 j = -τ.cartan l i := fun l => by
    simp [simpleRoot, Pi.single_apply]
  refine (mul_inv_eq_iff_eq_mul).1 ?_
  rw [xPar_neg_simple, torusElement_inv]
  calc _ = torusElement τ K k t * (torusElement τ K i u⁻¹ * F.eltElement (-simpleRoot τ i) c *
        (torusElement τ K i u⁻¹)⁻¹) * (torusElement τ K k t)⁻¹ := by group
    _ = F.eltElement (-simpleRoot τ i) c := by
      rw [F.torusElement_mul_eltElement_mul_inv, hs, F.torusElement_mul_eltElement_mul_inv, hs]
      congr 1
      have e : (t ^ (-τ.cartan k i) : Kˣ) * u⁻¹ ^ (-τ.cartan i i) = 1 := by
        rw [Tag.cartan_self, zpow_neg, ← h, zpow_neg, zpow_ofNat, inv_pow, inv_inv, inv_mul_cancel]
      rw [← mul_assoc, ← Units.val_mul, e, Units.val_one, one_mul]

theorem torusElement_mul_inv_mem_centralizer_rankOne (k i : Fin τ.rank) {t u : Kˣ}
    (h : u ^ 2 = t ^ τ.cartan k i) :
    torusElement τ K k t * (torusElement τ K i u)⁻¹ ∈
      Subgroup.centralizer (rankOne (rootGroup F K) i : Set (adjointGroup τ K)) := by
  set g := torusElement τ K k t * (torusElement τ K i u)⁻¹
  have hle : rankOne (rootGroup F K) i ≤ Subgroup.centralizer {g} := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_single τ i) x).1 hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (commute_torusElement_mul_inv_xPar_single k i h c).eq
    · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_neg_single τ i) x).1 hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (commute_torusElement_mul_inv_xPar_neg_single k i h c).eq
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) g rfl).symm

theorem iSup_torus_le_sup_centralizer_rankOne [Finite K] [CharP K 2] (i : Fin τ.rank) :
    (⨆ k, torus K k) ≤ ((⨆ k, torus K k) ⊓
      Subgroup.centralizer (rankOne (rootGroup F K) i : Set (adjointGroup τ K))) ⊔
        rankOne (rootGroup F K) i := by
  refine iSup_le fun k => ?_
  rintro _ ⟨t, rfl⟩
  obtain ⟨u, hu⟩ := exists_unit_sq_eq (t ^ τ.cartan k i)
  have e : (torusHom K k) t =
      (torusElement τ K k t * (torusElement τ K i u)⁻¹) * torusElement τ K i u :=
    (inv_mul_cancel_right _ _).symm
  rw [e]
  have hT : ∀ (j : Fin τ.rank) (v : Kˣ), torusElement τ K j v ∈ ⨆ k, torus K k := fun j v =>
    le_iSup (torus K) j ⟨v, rfl⟩
  refine Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨?_, ?_⟩) ?_
  · exact mul_mem (hT k t) (inv_mem (hT i u))
  · exact torusElement_mul_inv_mem_centralizer_rankOne k i hu
  · exact torus_le_rankOne (F := F) i ⟨u, rfl⟩

end Torus

section G2

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.SquareGeneric
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem isMulCommutative_of_isPGroup_five_le_torus_sup_rankOne_g2 (i : Fin (Tag.rank .G2))
    {Q : Subgroup ↥(adjointGroup .G2 K)}
    (hQ : Q ≤ (⨆ k, torus (τ := .G2) K k) ⊔ rankOne (g2Datum K).rootGroup i)
    (h5 : IsPGroup 5 Q) : IsMulCommutative Q := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨φ, hφ, hx, hy⟩ := g2_exists_sl2_hom (K := K) i
  have hrange : rankOne (g2Datum K).rootGroup i = φ.range :=
    rankOne_eq_range_of_sl2
      (adjDatum_isParametrization (F := rootOperatorFamily .G2) (K := K)
        (RootSystem.ofCartan (g2Datum K).isFiniteType (g2Datum K).divisible)
        (adjDatum_roots (rootOperatorFamily .G2) K))
      (fun c => (hx c).trans (xPar_simple i c).symm)
      (fun c => (hy c).trans (xPar_neg_simple i c).symm)
  have hT : IsMulCommutative ↥(⨆ k, torus (τ := .G2) K k) := by
    have h := isMulCommutative_torus (g2_steinbergExtras K)
    exact h
  set C : Subgroup ↥(adjointGroup .G2 K) := (⨆ k, torus (τ := .G2) K k) ⊓
    Subgroup.centralizer (rankOne (g2Datum K).rootGroup i : Set ↥(adjointGroup .G2 K))
  have hCc : IsMulCommutative ↥C := isMulCommutative_anti (inf_le_left : C ≤ _)
  have hle : Q ≤ C.subtype.range ⊔ φ.range := by
    rw [Subgroup.range_subtype, ← hrange]
    exact hQ.trans (sup_le (iSup_torus_le_sup_centralizer_rankOne (F := rootOperatorFamily .G2) i)
      le_sup_right)
  refine isMulCommutative_of_isPGroup_of_commute C.subtype φ (fun c a => ?_)
    (fun Q' _ => IsMulCommutative.of_setLike_mul_comm fun a _ b _ => hCc.is_comm.comm a b)
    (fun Q' hQ' => isMulCommutative_of_isPGroup_five_sl2 Q' hQ') hle h5
  have hmem : φ a ∈ rankOne (g2Datum K).rootGroup i := by
    rw [hrange]
    exact ⟨a, rfl⟩
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 c.2).2 (φ a) hmem).symm

theorem isMulCommutative_of_isPGroup_five_g2 {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* AdjointQuotient .G2 K) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) (hJ : J ≠ ⊤) (P : Subgroup Y)
    (hPJ : P ≤ J) (hP : IsPGroup 5 P) : IsMulCommutative P := by
  by_contra hPc
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hb := borelQuotient_g2 (K := K) e
  obtain ⟨π', hb', -, hBJ⟩ := BorelQuotient.exists_conj_parab hb T hNJ
  obtain ⟨Q, hQle, hQ, hQc⟩ := HeisEngine.exists_nonabelian_le_torus_sup_leviM hb' hBJ
    (by norm_num) hPJ hP hPc
  have hBJ' : (borel (g2Datum K) (torus (τ := .G2) K)).map π' ≤ J :=
    Subgroup.map_le_iff_le_comap.mpr hBJ
  obtain ⟨j, hj⟩ := LieOut.exists_node_not_mem_negIndices hb' hBJ' hJ
  have hsub : (negIndices (g2Datum K) (J.comap π')).Subsingleton := by
    intro x hx y hy
    have hxj : x.val ≠ j.val := fun h => hj (Fin.ext h ▸ hx)
    have hyj : y.val ≠ j.val := fun h => hj (Fin.ext h ▸ hy)
    have h1 : x.val < 2 := x.isLt
    have h2 : y.val < 2 := y.isLt
    have h3 : j.val < 2 := j.isLt
    exact Fin.ext (by omega)
  rcases hsub.eq_empty_or_singleton with hI | ⟨i, hI⟩
  · rw [hI, leviM_empty, sup_bot_eq] at hQle
    have := isMulCommutative_torus hb'.extras
    exact hQc (isMulCommutative_anti hQle)
  · rw [hI, leviM_singleton] at hQle
    exact hQc (isMulCommutative_of_isPGroup_five_le_torus_sup_rankOne_g2 i hQle hQ)

end G2

end CFSG.AGLEmbeddingD2.HeisG2
