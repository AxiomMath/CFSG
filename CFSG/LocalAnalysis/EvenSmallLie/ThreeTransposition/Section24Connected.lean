module

public import CFSG.LocalAnalysis.EvenSmallLie.ThreeTransposition.Section24

public section

namespace CFSG.EvenSmallLie.ThreeTransposition

open CFSG.Blueprint.Fischer CFSG.Fischer
open scoped Pointwise

variable {G : Type} [Group G]

section Sylow

theorem mem_smul_sylow_iff {p : ℕ} (T : Sylow p G) (g x : G) :
    x ∈ (g • T : Sylow p G) ↔ g⁻¹ * x * g ∈ T := by
  rw [← SetLike.mem_coe, Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem mul_eq_of_conj_eq {x f : G} (h : x * f * x⁻¹ = f) : x * f = f * x := by
  calc x * f = x * f * x⁻¹ * x := by group
    _ = f * x := by rw [h]

theorem mul_mul_self_of_commute {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : x * y = y * x) : x * y * (x * y) = 1 := by
  calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
    _ = x * (x * y) * y := by rw [← h]
    _ = 1 := by rw [← mul_assoc, hx, one_mul, hy]

theorem mul_self_of_mem_closure_of_pairwise {S : Set G} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hS2 : ∀ x ∈ S, x * x = 1) {x : G} (hx : x ∈ Subgroup.closure S) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS2 x hx
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    exact mul_mul_self_of_commute ihx ihy (commute_of_mem_closure_of_pairwise hS hx hy)
  | inv x _ ih => rw [← mul_inv_rev, ih, inv_one]

theorem isPGroup_closure_of_pairwise {S : Set G} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hS2 : ∀ x ∈ S, x * x = 1) : IsPGroup 2 (Subgroup.closure S) := by
  have key : ∀ x ∈ Subgroup.closure S, x * x = 1 := fun x hx =>
    mul_self_of_mem_closure_of_pairwise hS hS2 hx
  intro g
  refine ⟨1, ?_⟩
  ext
  simpa [pow_two] using key g g.2

theorem exists_sylow_of_pairwise {S : Set G} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hS2 : ∀ x ∈ S, x * x = 1) : ∃ T : Sylow 2 G, S ⊆ T := by
  obtain ⟨T, hT⟩ := (isPGroup_closure_of_pairwise hS hS2).exists_le_sylow
  exact ⟨T, fun x hx => hT (Subgroup.subset_closure hx)⟩

theorem smul_sylow_inter_eq_image {D : Set G} (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D)
    {p : ℕ} (T : Sylow p G) (g : G) :
    ((g • T : Sylow p G) : Set G) ∩ D = (fun x => g * x * g⁻¹) '' ((T : Set G) ∩ D) := by
  ext x
  constructor
  · rintro ⟨hxT, hxD⟩
    refine ⟨g⁻¹ * x * g, ⟨(mem_smul_sylow_iff T g x).1 hxT, ?_⟩, by group⟩
    simpa using hDinv g⁻¹ x hxD
  · rintro ⟨y, ⟨hyT, hyD⟩, rfl⟩
    exact ⟨(mem_smul_sylow_iff T g _).2 (by simpa [mul_assoc] using hyT), hDinv g y hyD⟩

theorem sylow_inter_eq_of_subset [Finite G] {D : Set G}
    (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) {T T' : Sylow 2 G}
    (h : (T : Set G) ∩ D ⊆ T') : (T' : Set G) ∩ D = (T : Set G) ∩ D := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G T T'
  have himage := smul_sylow_inter_eq_image hDinv T g
  have hcard : (((g • T : Sylow 2 G) : Set G) ∩ D).ncard = ((T : Set G) ∩ D).ncard := by
    rw [himage, Set.ncard_image_of_injective _ fun a b hab => by simpa using hab]
  exact Eq.symm (Set.eq_of_subset_of_ncard_le (fun x hx => ⟨h hx, hx.2⟩) hcard.le
    (Set.toFinite _))

theorem exists_mem_sylow_of_le [Finite G] {p : ℕ} [Fact p.Prime] {K P Q : Subgroup G}
    (hPK : P ≤ K) (hQK : Q ≤ K) (hP : IsPGroup p P) (hQ : IsPGroup p Q) :
    ∃ k ∈ K, ∃ T : Sylow p G, P ≤ T ∧ ∀ x ∈ Q, k * x * k⁻¹ ∈ T := by
  obtain ⟨S, hS⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨S₂, hS₂⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S₂ S
  obtain ⟨T, hT⟩ := (S.isPGroup'.map K.subtype).exists_le_sylow
  refine ⟨k, k.2, T, fun x hx => hT ⟨⟨x, hPK hx⟩, hS hx, rfl⟩, fun x hx => ?_⟩
  have h2 : k * ⟨x, hQK hx⟩ * k⁻¹ ∈ S := by
    rw [← hk, mem_smul_sylow_iff, show k⁻¹ * (k * ⟨x, hQK hx⟩ * k⁻¹) * k = ⟨x, hQK hx⟩ by group]
    exact hS₂ hx
  exact hT ⟨_, h2, rfl⟩

variable {D : Set G}

theorem exists_mem_normalizer_conj_eq [Finite G] (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D)
    (T : Sylow 2 G) (hcomm : ∀ a ∈ (T : Set G) ∩ D, ∀ b ∈ (T : Set G) ∩ D, a * b = b * a)
    {y : G} (hy : ∀ a ∈ (T : Set G) ∩ D, a * y = y * a) {e f g : G}
    (he : e ∈ (T : Set G) ∩ D) (hf : f ∈ (T : Set G) ∩ D) (hg : g * y = y * g)
    (hgef : g * e * g⁻¹ = f) :
    ∃ h ∈ Subgroup.normalizer ((T : Set G) ∩ D) ⊓ Subgroup.centralizer {y}, h * e * h⁻¹ = f := by
  let K := Subgroup.centralizer {y} ⊓ Subgroup.centralizer {f}
  let P := Subgroup.closure ((T : Set G) ∩ D)
  have hPK : P ≤ K := by
    rw [Subgroup.closure_le]
    intro x hx
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (hy x hx),
      Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx f hf)⟩
  have hQK : P.map (MulAut.conj g).toMonoidHom ≤ K := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro x hx
    have hgc : Commute g y := hg
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · exact ((hgc.mul_left (hy x hx : Commute x y)).mul_left hgc.inv_left :)
    · change g * x * g⁻¹ * f = f * (g * x * g⁻¹)
      rw [← hgef]
      exact (conj_commute_iff g x e).2 (hcomm x hx e he)
  have hP : IsPGroup 2 P := T.isPGroup'.to_le ((Subgroup.closure_le _).2 Set.inter_subset_left)
  obtain ⟨k, hkK, T', hPT', hQT'⟩ := exists_mem_sylow_of_le hPK hQK hP (hP.map _)
  have hT' : (T' : Set G) ∩ D = (T : Set G) ∩ D :=
    sylow_inter_eq_of_subset hDinv fun x hx => hPT' (Subgroup.subset_closure hx)
  refine ⟨k * g, ⟨Subgroup.mem_normalizer_fintype fun x hx => ?_,
    Subgroup.mul_mem _ hkK.1 (Subgroup.mem_centralizer_singleton_iff.2 hg)⟩, ?_⟩
  · have h1 : k * (g * x * g⁻¹) * k⁻¹ ∈ T' :=
      hQT' _ (Subgroup.mem_map_of_mem _ (Subgroup.subset_closure hx))
    rw [← hT']
    exact ⟨by simpa [mul_assoc] using h1, hDinv (k * g) x hx.2⟩
  · rw [show k * g * e * (k * g)⁻¹ = k * (g * e * g⁻¹) * k⁻¹ by group, hgef,
      Subgroup.mem_centralizer_singleton_iff.1 hkK.2, mul_inv_cancel_right]

end Sylow

section Components

@[expose] def compSet (D : Set G) (x : G) : Set G :=
  {y | ∃ (hx : x ∈ D) (hy : y ∈ D), (commGraph D).Reachable ⟨x, hx⟩ ⟨y, hy⟩}

variable {D : Set G}

theorem compSet_subset (x : G) : compSet D x ⊆ D := fun _ ⟨_, hy, _⟩ => hy

theorem mem_compSet_self {x : G} (hx : x ∈ D) : x ∈ compSet D x := ⟨hx, hx, .refl _⟩

theorem mem_compSet_of_commute {x y : G} (hx : x ∈ D) (hy : y ∈ D) (h : x * y = y * x) :
    y ∈ compSet D x :=
  ⟨hx, hy, commGraph_reachable_of_commute h⟩

theorem mem_compSet_comm {x y : G} (h : y ∈ compSet D x) : x ∈ compSet D y := by
  obtain ⟨hx, hy, hr⟩ := h
  exact ⟨hy, hx, hr.symm⟩

theorem compSet_eq {x y : G} (h : y ∈ compSet D x) : compSet D y = compSet D x := by
  obtain ⟨hx, hy, hr⟩ := h
  ext z
  constructor
  · rintro ⟨_, hz, hrz⟩
    exact ⟨hx, hz, hr.trans hrz⟩
  · rintro ⟨_, hz, hrz⟩
    exact ⟨hy, hz, hr.symm.trans hrz⟩

theorem image_supp_connectedComponentMk {x : G} (hx : x ∈ D) :
    Subtype.val '' ((commGraph D).connectedComponentMk ⟨x, hx⟩).supp = compSet D x := by
  ext y
  simp only [Set.mem_image, SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq]
  constructor
  · rintro ⟨⟨y, hy⟩, hr, rfl⟩
    exact ⟨hx, hy, hr.symm⟩
  · rintro ⟨_, hy, hr⟩
    exact ⟨⟨y, hy⟩, hr.symm, rfl⟩

theorem reachable_of_subset {E : Set G} (hED : E ⊆ D) {u v : E}
    (h : (commGraph E).Reachable u v) : (commGraph D).Reachable ⟨u, hED u.2⟩ ⟨v, hED v.2⟩ := by
  let f : commGraph E →g commGraph D :=
    { toFun := fun w => ⟨w, hED w.2⟩
      map_rel' := fun {a b} hab => by
        rw [commGraph_adj_iff] at hab ⊢
        exact hab }
  exact h.map f

theorem conj_mem_compSet (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (g : G) {x y : G}
    (h : y ∈ compSet D x) : g * y * g⁻¹ ∈ compSet D (g * x * g⁻¹) := by
  obtain ⟨hx, hy, hr⟩ := h
  let f : commGraph D →g commGraph D :=
    { toFun := fun v => ⟨g * v * g⁻¹, hDinv g v v.2⟩
      map_rel' := fun {u v} huv => by
        rw [commGraph_adj_iff] at huv ⊢
        exact ⟨fun e => huv.1 (by simpa using e), (conj_commute_iff g u v).2 huv.2⟩ }
  exact ⟨hDinv g x hx, hDinv g y hy, hr.map f⟩

theorem mem_normalizer_compSet_iff (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) {x : G}
    (hx : x ∈ D) (g : G) :
    g ∈ Subgroup.normalizer (compSet D x) ↔ g * x * g⁻¹ ∈ compSet D x := by
  rw [Subgroup.mem_set_normalizer_iff]
  refine ⟨fun h => (h x).1 (mem_compSet_self hx), fun hg n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · have h := conj_mem_compSet hDinv g hn
    rwa [compSet_eq hg] at h
  · have h1 := conj_mem_compSet hDinv g⁻¹ hn
    have h2 := conj_mem_compSet hDinv g⁻¹ hg
    rw [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at h1
    rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h2
    rwa [← compSet_eq h2] at h1

theorem exists_fixed_of_component
    (h3 : ∀ Δ : (commGraph D).ConnectedComponent,
      ∀ x ∈ Subgroup.normalizer (Subtype.val '' Δ.supp), orderOf x = 2 →
        ∃ f ∈ Subtype.val '' Δ.supp, x * f * x⁻¹ = f)
    {v : G} (hv : v ∈ D) {x : G} (hxN : x ∈ Subgroup.normalizer (compSet D v))
    (hx2 : orderOf x = 2) : ∃ f ∈ compSet D v, x * f * x⁻¹ = f := by
  have h := h3 ((commGraph D).connectedComponentMk ⟨v, hv⟩) x
  rw [image_supp_connectedComponentMk hv] at h
  exact h hxN hx2

end Components

section OneThree

variable {D : Set G}

theorem IsOddTranspositionSet.centralizer_le_normalizer
    (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hD2 : ∀ x ∈ D, orderOf x = 2)
    (hodd : IsOddTranspositionSet D) {d e : G} (hd : d ∈ D) (he : e ∈ LocalClass D d) :
    Subgroup.centralizer {e * d} ≤ Subgroup.normalizer (compSet D d) := by
  intro g hg
  rw [mem_normalizer_compSet_iff hDinv hd]
  have hgc : Commute g (e * d) := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hdc : Commute d (e * d) := Commute.mul_right (he.2.2.symm : Commute d e) (Commute.refl d)
  have hc : Commute (g * d * g⁻¹) (e * d) := (hgc.mul_left hdc).mul_left hgc.inv_left
  rw [he.2.2] at hc
  exact mem_compSet_of_commute hd (hDinv g d hd)
    (hodd.commute_of_commute_mul hD2 hd he (hDinv g d hd) hc).symm

theorem IsOddTranspositionSet.centralizer_le_normalizer_of_mem_sylow [Finite G]
    (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hD2 : ∀ x ∈ D, orderOf x = 2)
    (hodd : IsOddTranspositionSet D) (T : Sylow 2 G)
    (h2 : ∀ a ∈ (T : Set G) ∩ D, ∀ b ∈ (T : Set G) ∩ D, ∀ c ∈ (T : Set G) ∩ D,
      ¬ ∀ e ∈ (T : Set G) ∩ D, ∀ f ∈ (T : Set G) ∩ D,
        ∃ g ∈ Subgroup.normalizer ((T : Set G) ∩ D) ⊓ Subgroup.centralizer {a * b * c},
          g * e * g⁻¹ = f)
    {a b c : G} (ha : a ∈ (T : Set G) ∩ D) (hb : b ∈ (T : Set G) ∩ D)
    (hc : c ∈ (T : Set G) ∩ D) :
    Subgroup.centralizer {a * b * c} ≤ Subgroup.normalizer (compSet D a) := by
  have hΩ : ∀ u ∈ (T : Set G) ∩ D, ∀ v ∈ (T : Set G) ∩ D, u * v = v * u :=
    fun u hu v hv => hodd.commute_of_mem_pGroup hD2 T.isPGroup' hu.2 hu.1 hv.2 hv.1
  have hΩy : ∀ u ∈ (T : Set G) ∩ D, u * (a * b * c) = a * b * c * u := fun u hu =>
    Commute.mul_right (Commute.mul_right (hΩ u hu a ha : Commute u a) (hΩ u hu b hb))
      (hΩ u hu c hc)
  let E : Set G := D ∩ (Subgroup.centralizer {a * b * c} : Set G)
  have hED : E ⊆ D := Set.inter_subset_left
  have hmemE : ∀ u ∈ (T : Set G) ∩ D, u ∈ E := fun u hu =>
    ⟨hu.2, Subgroup.mem_centralizer_singleton_iff.2 (hΩy u hu)⟩
  have hnt : ¬ ∀ u ∈ E, ∀ v ∈ E, ∃ g ∈ Subgroup.closure E, g * u * g⁻¹ = v := by
    intro htr
    refine h2 a ha b hb c hc fun e he f hf => ?_
    obtain ⟨g, hg, hgef⟩ := htr e (hmemE e he) f (hmemE f hf)
    have hgy := ((Subgroup.closure_le _).2 Set.inter_subset_right :
      Subgroup.closure E ≤ Subgroup.centralizer {a * b * c}) hg
    exact exists_mem_normalizer_conj_eq hDinv T hΩ hΩy he hf
      (Subgroup.mem_centralizer_singleton_iff.1 hgy) hgef
  have hconn := (hodd.subset hED).connected_of_not_transitive (fun x hx => hD2 x hx.1) hnt
  intro g hg
  rw [mem_normalizer_compSet_iff hDinv ha.2]
  have hgc : Commute g (a * b * c) := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hgaE : g * a * g⁻¹ ∈ E := ⟨hDinv g a ha.2, Subgroup.mem_centralizer_singleton_iff.2
    (((hgc.mul_left (hΩy a ha : Commute a _)).mul_left hgc.inv_left :))⟩
  exact ⟨ha.2, hDinv g a ha.2,
    reachable_of_subset hED (hconn.preconnected ⟨a, hmemE a ha⟩ ⟨g * a * g⁻¹, hgaE⟩)⟩

theorem IsOddTranspositionSet.centralizer_le_normalizer_of_commute [Finite G]
    (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hD2 : ∀ x ∈ D, orderOf x = 2)
    (hodd : IsOddTranspositionSet D) (T : Sylow 2 G)
    (h2 : ∀ a ∈ (T : Set G) ∩ D, ∀ b ∈ (T : Set G) ∩ D, ∀ c ∈ (T : Set G) ∩ D,
      ¬ ∀ e ∈ (T : Set G) ∩ D, ∀ f ∈ (T : Set G) ∩ D,
        ∃ g ∈ Subgroup.normalizer ((T : Set G) ∩ D) ⊓ Subgroup.centralizer {a * b * c},
          g * e * g⁻¹ = f)
    {a b c : G} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) :
    Subgroup.centralizer {a * b * c} ≤ Subgroup.normalizer (compSet D a) := by
  have hS : ∀ x ∈ ({a, b, c} : Set G), ∀ y ∈ ({a, b, c} : Set G), x * y = y * x := by
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) <;> first | rfl | assumption | exact Eq.symm ‹_›
  have hS2 : ∀ x ∈ ({a, b, c} : Set G), x * x = 1 := by
    rintro x (rfl | rfl | rfl) <;> exact mul_self_of_orderOf (hD2 _ ‹_›)
  obtain ⟨T', hT'⟩ := exists_sylow_of_pairwise hS hS2
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G T T'
  have hmem : ∀ x ∈ D, x ∈ ({a, b, c} : Set G) → g⁻¹ * x * g ∈ (T : Set G) ∩ D := by
    intro x hx hxS
    refine ⟨(mem_smul_sylow_iff T g x).1 (hT' hxS), ?_⟩
    simpa using hDinv g⁻¹ x hx
  have hle := hodd.centralizer_le_normalizer_of_mem_sylow hDinv hD2 T h2
    (hmem a ha (by simp)) (hmem b hb (by simp)) (hmem c hc (by simp))
  intro x hx
  rw [mem_normalizer_compSet_iff hDinv ha]
  have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer
      {g⁻¹ * a * g * (g⁻¹ * b * g) * (g⁻¹ * c * g)} := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    rw [show g⁻¹ * a * g * (g⁻¹ * b * g) * (g⁻¹ * c * g) = g⁻¹ * (a * b * c) * g⁻¹⁻¹ by group,
      show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group]
    exact (conj_commute_iff g⁻¹ x (a * b * c)).2 hx
  have h := hle hx'
  rw [mem_normalizer_compSet_iff hDinv (hmem a ha (by simp)).2] at h
  have h' := conj_mem_compSet hDinv g h
  rwa [show g * (g⁻¹ * x * g * (g⁻¹ * a * g) * (g⁻¹ * x * g)⁻¹) * g⁻¹ = x * a * x⁻¹ by group,
    show g * (g⁻¹ * a * g) * g⁻¹ = a by group] at h'

theorem IsOddTranspositionSet.connected_of_sylow [Finite G]
    (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hD2 : ∀ x ∈ D, orderOf x = 2)
    (hodd : IsOddTranspositionSet D) (T : Sylow 2 G)
    (h1 : {x | x ∈ Subgroup.closure ((T : Set G) ∩ D) ∧ x ≠ 1} ≠ (T : Set G) ∩ D)
    (h2 : ∀ a ∈ (T : Set G) ∩ D, ∀ b ∈ (T : Set G) ∩ D, ∀ c ∈ (T : Set G) ∩ D,
      ¬ ∀ e ∈ (T : Set G) ∩ D, ∀ f ∈ (T : Set G) ∩ D,
        ∃ g ∈ Subgroup.normalizer ((T : Set G) ∩ D) ⊓ Subgroup.centralizer {a * b * c},
          g * e * g⁻¹ = f)
    (h3 : ∀ Δ : (commGraph D).ConnectedComponent,
      ∀ x ∈ Subgroup.normalizer (Subtype.val '' Δ.supp), orderOf x = 2 →
        ∃ f ∈ Subtype.val '' Δ.supp, x * f * x⁻¹ = f) :
    (commGraph D).Connected := by
  obtain ⟨d, hd, e, he, hxD, hx1⟩ : ∃ d ∈ (T : Set G) ∩ D, ∃ e ∈ (T : Set G) ∩ D,
      d * e ∉ D ∧ d * e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine h1 (Set.ext fun x => ⟨fun ⟨hxcl, hx1⟩ => ?_, fun hx =>
      ⟨Subgroup.subset_closure hx, ne_one_of_orderOf (hD2 x hx.2)⟩⟩)
    have key : ∀ y ∈ Subgroup.closure ((T : Set G) ∩ D), y ∈ (T : Set G) ∩ D ∨ y = 1 := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy => exact Or.inl hy
      | one => exact Or.inr rfl
      | mul y z _ _ ihy ihz =>
        rcases ihy with hy | rfl
        · rcases ihz with hz | rfl
          · by_cases hyz : y * z ∈ D
            · exact Or.inl ⟨mul_mem hy.1 hz.1, hyz⟩
            · exact Or.inr (hcon y hy z hz hyz)
          · simpa only [mul_one] using Or.inl hy
        · simpa only [one_mul] using ihz
      | inv y _ ihy =>
        rcases ihy with hy | rfl
        · exact Or.inl (by rwa [inv_of_orderOf (hD2 y hy.2)])
        · exact Or.inr inv_one
    exact (key x hxcl).resolve_right hx1
  have hd2 := mul_self_of_orderOf (hD2 d hd.2)
  have he2 := mul_self_of_orderOf (hD2 e he.2)
  have hde : d * e = e * d :=
    hodd.commute_of_mem_pGroup hD2 T.isPGroup' hd.2 hd.1 he.2 he.1
  have hed : e ≠ d := fun h => hx1 (by rw [h, hd2])
  have heloc : e ∈ LocalClass D d := ⟨he.2, hed, hde.symm⟩
  have hx2 : d * e * (d * e) = 1 := mul_mul_self_of_commute hd2 he2 hde
  have hxo : orderOf (d * e) = 2 := orderOf_mul_of_commute hd2 he2 hed.symm hde
  have hNd : ∀ u ∈ D, u ∈ Subgroup.normalizer (compSet D d) → u ∈ compSet D d := by
    intro u hu huN
    obtain ⟨f, hf, hfu⟩ := exists_fixed_of_component h3 hd.2 huN (hD2 u hu)
    rw [← compSet_eq hf]
    exact mem_compSet_of_commute (compSet_subset d hf) hu (mul_eq_of_conj_eq hfu).symm
  have hCx : Subgroup.centralizer {d * e} ≤ Subgroup.normalizer (compSet D d) := by
    have h := hodd.centralizer_le_normalizer hDinv hD2 hd.2 heloc
    rwa [← hde] at h
  suffices hall : ∀ a ∈ D, a ∈ compSet D d by
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ⟨⟨d, hd.2⟩⟩⟩
    obtain ⟨_, _, hu⟩ := hall u u.2
    obtain ⟨_, _, hv⟩ := hall v v.2
    exact hu.symm.trans hv
  intro a ha
  by_contra haΔ
  have ha2 := mul_self_of_orderOf (hD2 a ha)
  have hxa : ¬ Odd (orderOf (d * e * a)) := by
    intro hodd'
    obtain ⟨g, -, hg⟩ := Timmesfeld.exists_conj_of_odd_orderOf_mul hx2 ha2 hodd'
    refine hxD ?_
    have h := hDinv g⁻¹ a ha
    rwa [← hg, show g⁻¹ * (g * (d * e) * g⁻¹) * g⁻¹⁻¹ = d * e by group] at h
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.1 hxa
  have hk0 : 0 < k := by
    have := orderOf_pos (d * e * a)
    omega
  obtain ⟨hz1, -, hzx, hza⟩ := dihedral_center hx2 ha2 hk hk0
  have e1 : a * (d * e * a) ^ k = d * e * (d * e * a) ^ (k + 1) := by
    rw [pow_succ', ← mul_assoc, ← mul_assoc (d * e) (d * e) a, hx2, one_mul]
  have hconj := exists_conj_eq_mul_pow hx2 ha2 (k + 1)
  rw [← e1] at hconj
  generalize (d * e * a) ^ k = z at hz1 hzx hza hconj
  have hzz : a * z * a = z := by rw [hza, mul_assoc, ha2, mul_one]
  have hCz : Subgroup.centralizer {z} ≤ Subgroup.normalizer (compSet D a) := by
    rcases hconj with ⟨g, -, hg⟩ | ⟨g, -, hg⟩
    ·
      have hbD : g * d * g⁻¹ ∈ D := hDinv g d hd.2
      have hcD : g * e * g⁻¹ ∈ D := hDinv g e he.2
      have hbc : g * d * g⁻¹ * (g * e * g⁻¹) = a * z := by
        rw [← hg]
        group
      have hcb : g * e * g⁻¹ ∈ LocalClass D (g * d * g⁻¹) :=
        ⟨hcD, fun h => hed (conj_injective h), (conj_commute_iff g e d).2 hde.symm⟩
      have hbcb : g * d * g⁻¹ ∈ LocalClass D (g * e * g⁻¹) :=
        ⟨hbD, fun h => hed (conj_injective h).symm, (conj_commute_iff g d e).2 hde⟩
      have habc : a * (g * d * g⁻¹ * (g * e * g⁻¹)) = g * d * g⁻¹ * (g * e * g⁻¹) * a := by
        rw [hbc, ← mul_assoc, ha2, one_mul, hzz]
      have hab := hodd.commute_of_commute_mul hD2 hbD hcb ha habc
      have hac := hodd.commute_of_commute_mul hD2 hcD hbcb ha
        (by rw [hcb.2.2]; exact habc)
      have h := hodd.centralizer_le_normalizer_of_commute hDinv hD2 T h2 hbD hcD ha
        hcb.2.2.symm hab.symm hac.symm
      rwa [hbc, hzz, compSet_eq (mem_compSet_of_commute ha hbD hab)] at h
    ·
      have hazD : a * z ∈ D := hg ▸ hDinv g a ha
      have hazl : a * z ∈ LocalClass D a := by
        refine ⟨hazD, fun h => hz1 (mul_left_cancel (h.trans (mul_one a).symm)), ?_⟩
        rw [mul_assoc, ← hza, ← mul_assoc]
      have h := hodd.centralizer_le_normalizer hDinv hD2 ha hazl
      rwa [hzz] at h
  obtain ⟨f, hf, hfx⟩ := exists_fixed_of_component h3 ha
    (hCz (Subgroup.mem_centralizer_singleton_iff.2 hzx)) hxo
  have hfΔ : f ∈ compSet D d := hNd f (compSet_subset a hf)
    (hCx (Subgroup.mem_centralizer_singleton_iff.2 (mul_eq_of_conj_eq hfx).symm))
  exact haΔ (by rw [← compSet_eq hfΔ]; exact mem_compSet_comm hf)

end OneThree

end CFSG.EvenSmallLie.ThreeTransposition
