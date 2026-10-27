module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerTodd

public section

namespace CFSG.EvenSmallLie.UnitarySix.Fischer

open CFSG.Blueprint.Fischer CFSG.Fischer Subgroup CFSG.ComponentClassification.WittDesign
  CFSG.EvenSmallLie.ThreeTransposition
open CFSG.EvenSmallLie.UnitarySix.ToddOrbit (orb orb_subset conj_mem_orb_iff')

variable {G : Type} [Group G] [Finite G] {t : G} {L E : Subgroup G}
  {p : L →* Equiv.Perm (Fin 693)}

namespace FischerHyp

theorem exists_sylow
    (h : FischerHyp t L E p) :
    ∃ T : Sylow 2 G, E ≤ T ∧ (T : Subgroup G) ≤ normalizer (E : Set G) := by
  set N := normalizer (E : Set G)
  obtain ⟨P⟩ : Nonempty (Sylow 2 N) := inferInstance
  set Q := (P : Subgroup N).map N.subtype
  have hQcard : Nat.card Q = 2 ^ 17 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact h.card_sylowN P
  obtain ⟨T, hQT⟩ := (IsPGroup.of_card hQcard).exists_le_sylow
  have hQT' : Q = T := Subgroup.eq_of_le_of_card_ge hQT (by rw [h.card_sylow T, hQcard])
  refine ⟨T, ?_, hQT' ▸ Subgroup.map_subtype_le _⟩
  rw [← hQT']
  intro e he
  have : (E.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hEp : IsPGroup 2 (E.subgroupOf N) := IsPGroup.of_card (n := 10) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_normalizer).toEquiv]
    exact h.todd.card_E)
  exact ⟨⟨e, le_normalizer he⟩, hEp.le_sylow_of_normal P (mem_subgroupOf.2 he), rfl⟩

omit [Finite G] in
theorem orb_subset_tClass : orb E t ⊆ tClass t := by
  rintro _ ⟨n, -, rfl⟩
  exact isConj_iff.2 ⟨n⁻¹, by group⟩

omit [Finite G] in
theorem mem_orb_of_mem_E
    (h : FischerHyp t L E p) {d : G} (hdD : d ∈ tClass t) (hdE : d ∈ E) :
    d ∈ orb E t := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hdD
  obtain ⟨n, hn, hnt⟩ := h.todd.fusion c⁻¹ (by simpa only [inv_inv] using hdE)
  exact ⟨n, hn, by rw [← hnt, inv_inv]⟩

omit [Finite G] in
theorem mem_E_of_mem_localClass
    (h : FischerHyp t L E p) {d : G}
    (hd : d ∈ LocalClass (tClass t) t) (hdN : d ∈ normalizer (E : Set G)) : d ∈ E := by
  obtain ⟨m, hm⟩ := h.tv d (h.mem_L hd) hd.1 hd.2.1
  have hnorm : tvP m ∈ normalizer (uA : Set (Equiv.Perm (Fin 693))) := by
    rw [← hm]
    refine mem_normalizer_fintype fun a ha => ?_
    obtain ⟨y, hy⟩ := h.todd.surj a (uA_le_T46 ha)
    have hyE : (y : G) ∈ E := (h.todd.mem_E y).2 ⟨y.2, by rw [hy]; exact ha⟩
    have hc : d * y * d⁻¹ ∈ E := (mem_normalizer_iff.1 hdN y).1 hyE
    obtain ⟨hL, hpu⟩ := (h.todd.mem_E _).1 hc
    have e : (⟨d * y * d⁻¹, hL⟩ : L) = ⟨d, h.mem_L hd⟩ * y * ⟨d, h.mem_L hd⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hy] at hpu
    exact hpu
  exact (h.todd.mem_E d).2 ⟨h.mem_L hd, hm ▸ mem_uA_of_mem_normalizer hnorm⟩

omit [Finite G] in
theorem sylow_inter_eq
    (h : FischerHyp t L E p) {T : Sylow 2 G} (hET : E ≤ T)
    (hTN : (T : Subgroup G) ≤ normalizer (E : Set G)) :
    (T : Set G) ∩ tClass t = orb E t := by
  obtain ⟨f, hf⟩ := h.m22
  ext d
  refine ⟨fun ⟨hdT, hdD⟩ => ?_, fun hd => ⟨hET (h.orb_subset_E hd), orb_subset_tClass hd⟩⟩
  have hdN := hTN hdT
  by_cases hdE : d ∈ E
  · exact h.mem_orb_of_mem_E hdD hdE
  exfalso
  have hd2 : d * d = 1 := mul_self_of_mem_tClass h.orderOf_t hdD
  have hσ2 : labelPerm f ⟨d, hdN⟩ * labelPerm f ⟨d, hdN⟩ = 1 := by
    rw [← labelPerm_mul, show (⟨d, hdN⟩ * ⟨d, hdN⟩ : normalizer (E : Set G)) = 1 from
      Subtype.ext hd2, labelPerm_one]
  obtain ⟨i, hi⟩ := exists_fixed_of_mul_self (labelPerm_mem f hf _) hσ2
  have hde : d * (f.symm i : G) * d⁻¹ = f.symm i := by
    have := labelPerm_symm f ⟨d, hdN⟩ (f.symm i)
    rw [Equiv.apply_symm_apply, hi] at this
    exact this.symm
  obtain ⟨n, hn, hne⟩ := (f.symm i).2
  have hdc : d * (f.symm i : G) = f.symm i * d := by
    calc d * (f.symm i : G) = d * f.symm i * d⁻¹ * d := by group
      _ = f.symm i * d := by rw [hde]
  have hloc : n * d * n⁻¹ ∈ LocalClass (tClass t) t := by
    refine ⟨conj_mem_tClass n hdD, fun he => hdE ?_, ?_⟩
    · have : d = n⁻¹ * t * n := by rw [← he]; group
      rw [this, hne]
      exact h.orb_subset_E (f.symm i).2
    · have ht : t = n * f.symm i * n⁻¹ := by rw [← hne]; group
      rw [ht]
      calc n * d * n⁻¹ * (n * f.symm i * n⁻¹) = n * (d * f.symm i) * n⁻¹ := by group
        _ = n * (f.symm i * d) * n⁻¹ := by rw [hdc]
        _ = n * f.symm i * n⁻¹ * (n * d * n⁻¹) := by group
  have hEd := h.mem_E_of_mem_localClass hloc (mul_mem (mul_mem hn hdN) (inv_mem hn))
  apply hdE
  have := (mem_normalizer_iff.1 (inv_mem hn) _).1 hEd
  rwa [show n⁻¹ * (n * d * n⁻¹) * n⁻¹⁻¹ = d by group] at this


omit [Finite G] in
theorem orb_subset_compSet
    (h : FischerHyp t L E p) :
    orb E t ⊆ ThreeTransposition.compSet (tClass t) t :=
  fun s hs => mem_compSet_of_commute (self_mem_tClass t) (orb_subset_tClass hs)
    (h.E_comm t h.todd.t_mem_E s (h.orb_subset_E hs))

omit [Finite G] in
theorem normalizer_le_normalizer_compSet
    (h : FischerHyp t L E p) :
    normalizer (E : Set G) ≤ normalizer (ThreeTransposition.compSet (tClass t) t) := by
  intro y hy
  rw [mem_normalizer_compSet_iff (tClass_inv t) (self_mem_tClass t)]
  have ho : y * t * y⁻¹ ∈ orb E t := (conj_mem_orb_iff' hy).2 ToddOrbit.t_mem_orb
  exact h.orb_subset_compSet ho

end FischerHyp

theorem exists_conj_mem_of_le {Y : Subgroup G} (T : Sylow 2 G) (hTY : (T : Subgroup G) ≤ Y)
    {x : G} (hxY : x ∈ Y) (hx2 : x * x = 1) : ∃ y ∈ Y, y * x * y⁻¹ ∈ T := by
  obtain ⟨Q, hQ⟩ := exists_sylow_of_pairwise (G := Y) (S := {⟨x, hxY⟩})
    (by rintro _ rfl _ rfl; rfl) (by rintro _ rfl; exact Subtype.ext hx2)
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y Q (T.subtype hTY)
  have hmem : y * ⟨x, hxY⟩ * y⁻¹ ∈ ((T.subtype hTY : Sylow 2 Y) : Subgroup Y) := by
    rw [← hy]
    show y * ⟨x, hxY⟩ * y⁻¹ ∈ (y • Q : Sylow 2 Y)
    rw [mem_smul_sylow_iff, show y⁻¹ * (y * ⟨x, hxY⟩ * y⁻¹) * y = ⟨x, hxY⟩ by group]
    exact hQ rfl
  rw [Sylow.coe_subtype, mem_subgroupOf] at hmem
  exact ⟨y, y.2, hmem⟩

namespace FischerHyp

theorem fixed_of_component
    (h : FischerHyp t L E p) :
    ∀ Δ : (commGraph (tClass t)).ConnectedComponent,
      ∀ x ∈ normalizer (Subtype.val '' Δ.supp), orderOf x = 2 →
        ∃ f ∈ Subtype.val '' Δ.supp, x * f * x⁻¹ = f := by
  obtain ⟨T, -, hTN⟩ := h.exists_sylow
  obtain ⟨f, hf⟩ := h.m22
  have hDinv := tClass_inv t
  intro Δ
  induction Δ using SimpleGraph.ConnectedComponent.ind with
  | h v =>
  obtain ⟨v, hv⟩ := v
  intro x hx hx2
  rw [image_supp_connectedComponentMk hv] at hx ⊢
  obtain ⟨c, rfl⟩ := isConj_iff.1 hv
  have hx2' : x * x = 1 := ThreeTransposition.mul_self_of_orderOf hx2
  have hct : c⁻¹ * (c * t * c⁻¹) * c⁻¹⁻¹ = t := by group
  have hx' : c⁻¹ * x * c ∈ normalizer (ThreeTransposition.compSet (tClass t) t) := by
    rw [mem_normalizer_compSet_iff hDinv (self_mem_tClass t)]
    have h1 := (mem_normalizer_compSet_iff hDinv hv x).1 hx
    have h2 := conj_mem_compSet hDinv c⁻¹ h1
    rw [hct] at h2
    rwa [show c⁻¹ * (x * (c * t * c⁻¹) * x⁻¹) * c⁻¹⁻¹ = c⁻¹ * x * c * t * (c⁻¹ * x * c)⁻¹ by
      group] at h2
  have hx'2 : c⁻¹ * x * c * (c⁻¹ * x * c) = 1 := by
    rw [show c⁻¹ * x * c * (c⁻¹ * x * c) = c⁻¹ * (x * x) * c by group, hx2', mul_one,
      inv_mul_cancel]
  obtain ⟨y, hy, hyT⟩ := exists_conj_mem_of_le T
    (le_trans hTN h.normalizer_le_normalizer_compSet) hx' hx'2
  set x'' := y * (c⁻¹ * x * c) * y⁻¹ with hx''
  have hx''N := hTN hyT
  have hx''2 : x'' * x'' = 1 := by
    rw [hx'', show y * (c⁻¹ * x * c) * y⁻¹ * (y * (c⁻¹ * x * c) * y⁻¹) =
      y * (c⁻¹ * x * c * (c⁻¹ * x * c)) * y⁻¹ by group, hx'2, mul_one, mul_inv_cancel]
  have hσ2 : labelPerm f ⟨x'', hx''N⟩ * labelPerm f ⟨x'', hx''N⟩ = 1 := by
    rw [← labelPerm_mul, show (⟨x'', hx''N⟩ * ⟨x'', hx''N⟩ : normalizer (E : Set G)) = 1 from
      Subtype.ext hx''2, labelPerm_one]
  obtain ⟨i, hi⟩ := exists_fixed_of_mul_self (labelPerm_mem f hf _) hσ2
  have hfix : x'' * (f.symm i : G) * x''⁻¹ = f.symm i := by
    have := labelPerm_symm f ⟨x'', hx''N⟩ (f.symm i)
    rw [Equiv.apply_symm_apply, hi] at this
    exact this.symm
  have he : (f.symm i : G) ∈ ThreeTransposition.compSet (tClass t) t :=
    h.orb_subset_compSet (f.symm i).2
  have hy' : y⁻¹ ∈ normalizer (ThreeTransposition.compSet (tClass t) t) := inv_mem hy
  have he' : y⁻¹ * f.symm i * y⁻¹⁻¹ ∈ ThreeTransposition.compSet (tClass t) t :=
    (Subgroup.mem_set_normalizer_iff.1 hy' (f.symm i : G)).1 he
  refine ⟨c * (y⁻¹ * f.symm i * y⁻¹⁻¹) * c⁻¹, conj_mem_compSet hDinv c he', ?_⟩
  have hx'_eq : c⁻¹ * x * c = y⁻¹ * x'' * y := by rw [hx'']; group
  calc x * (c * (y⁻¹ * f.symm i * y⁻¹⁻¹) * c⁻¹) * x⁻¹ =
      c * y⁻¹ * ((y * (c⁻¹ * x * c) * y⁻¹) * f.symm i * (y * (c⁻¹ * x * c) * y⁻¹)⁻¹) * y *
        c⁻¹ := by group
    _ = c * (y⁻¹ * f.symm i * y⁻¹⁻¹) * c⁻¹ := by rw [← hx'', hfix]; group


@[reducible] def conjActOrb (K : Subgroup G) (hK : K ≤ normalizer (orb E t)) :
    MulAction K (orb E t) where
  smul k s := ⟨k * s * (k : G)⁻¹, (mem_set_normalizer_iff.1 (hK k.2) s).1 s.2⟩
  one_smul s := Subtype.ext (by
    show ((1 : K) : G) * (s : G) * ((1 : K) : G)⁻¹ = s
    simp)
  mul_smul k k' s := Subtype.ext (by
    show ((k * k' : K) : G) * (s : G) * ((k * k' : K) : G)⁻¹ =
      (k : G) * ((k' : G) * s * (k' : G)⁻¹) * (k : G)⁻¹
    simp only [Subgroup.coe_mul]
    group)

theorem mem_normalizer_E_of_orb
    (h : FischerHyp t L E p) {f : orb E t ≃ Fin 22}
    (hf : ∀ σ : Equiv.Perm (Fin 22), σ ∈ M22 ↔ ∃ n ∈ normalizer (E : Set G),
      ∀ s : orb E t, (f.symm (σ (f s)) : G) = n * s * n⁻¹)
    {g : G} (hg : g ∈ normalizer (orb E t)) : g ∈ normalizer (E : Set G) := by
  refine mem_normalizer_fintype fun e he => ?_
  rw [SetLike.mem_coe, ← h.closure_orb f hf] at he ⊢
  induction he using Subgroup.closure_induction with
  | mem x hx => exact subset_closure ((mem_set_normalizer_iff.1 hg x).1 hx)
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem not_transitive
    (h : FischerHyp t L E p) {f : orb E t ≃ Fin 22}
    (hf : ∀ σ : Equiv.Perm (Fin 22), σ ∈ M22 ↔ ∃ n ∈ normalizer (E : Set G),
      ∀ s : orb E t, (f.symm (σ (f s)) : G) = n * s * n⁻¹) :
    ∀ a ∈ orb E t, ∀ b ∈ orb E t, ∀ c ∈ orb E t, ¬ ∀ e ∈ orb E t, ∀ f' ∈ orb E t,
      ∃ g ∈ normalizer (orb E t) ⊓ centralizer {a * b * c}, g * e * g⁻¹ = f' := by
  intro a ha b hb c hc htr
  set K := normalizer (orb E t) ⊓ centralizer {a * b * c}
  let _ := conjActOrb K inf_le_left
  have hp11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have horbit : MulAction.orbit K (⟨t, ToddOrbit.t_mem_orb⟩ : orb E t) = Set.univ := by
    refine Set.eq_univ_of_forall fun s => ?_
    obtain ⟨g, hg, hgs⟩ := htr t ToddOrbit.t_mem_orb s s.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgs⟩
  have h22 : 22 ∣ Nat.card K := by
    have hi := MulAction.index_stabilizer K (⟨t, ToddOrbit.t_mem_orb⟩ : orb E t)
    rw [horbit, Set.ncard_univ, Nat.card_congr f, Nat.card_fin] at hi
    rw [← hi]
    exact Subgroup.index_dvd_card _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := K) 11 (dvd_trans (by norm_num) h22)
  have hgN := h.mem_normalizer_E_of_orb hf g.2.1
  have hy : a * b * c ∈ E :=
    mul_mem (mul_mem (h.orb_subset_E ha) (h.orb_subset_E hb)) (h.orb_subset_E hc)
  have hy1 := h.eq_one_of_orderOf_eleven f hf hgN (by rw [Subgroup.orderOf_coe]; exact hg) hy
    (mem_centralizer_singleton_iff.1 g.2.2)
  have hb2 : b * b = 1 := by rw [← sq]; exact h.todd.E_sq b (h.orb_subset_E hb)
  have hc2 : c * c = 1 := by rw [← sq]; exact h.todd.E_sq c (h.orb_subset_E hc)
  have hab : a * b = c := by
    calc a * b = a * b * c * c := by rw [mul_assoc (a * b), hc2, mul_one]
      _ = c := by rw [hy1, one_mul]
  by_cases hab' : a = b
  · rw [hab', hb2] at hab
    exact ToddOrbit.one_notMem_orb (ThreeTransposition.ne_one_of_orderOf h.orderOf_t)
      (hab ▸ hc)
  · exact h.mul_notMem_orb f hf ha hb hab' (hab ▸ hc)


theorem connected_of_hii
    (h : FischerHyp t L E p)
    (hii : ∀ b ∈ LocalClass (tClass t) t, ∀ a ∈ tClass t, a * t ≠ t * a →
      a ∈ LocalClass (tClass t) b → ∀ c ∈ LocalClass (tClass t) t,
        ∃ f ∈ LocalClass (tClass t) a ∩ LocalClass (tClass t) t, f * c = c * f) :
    (commGraph (tClass t)).Connected ∧ IsThreeTranspositionSet (tClass t) := by
  obtain ⟨T, hET, hTN⟩ := h.exists_sylow
  obtain ⟨f, hf⟩ := h.m22
  have hTD := h.sylow_inter_eq hET hTN
  have hcl := h.closure_orb f hf
  refine connected_isThreeTranspositionSet ⟨t, rfl⟩
    (fun x hx => orderOf_of_mem_tClass h.orderOf_t hx) (self_mem_tClass t) h.pair_localGroup hii T
    ?_ ?_ ?_ ?_ ?_ h.fixed_of_component
  · rw [hTD, hcl]
    exact fun x hx y hy => h.E_comm x hx y hy
  · rw [hTD]
    refine le_antisymm ((closure_le _).2 (h.orb_subset_closure_mul f hf)) ((closure_le _).2 ?_)
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (subset_closure ha) (subset_closure hb)
  · rw [hTD]
    exact h.pair_inj f hf
  · rw [hTD]
    obtain ⟨n, hn, hne⟩ := h.todd.move
    have hs : n⁻¹ * t * n ∈ orb E t := ⟨n, hn, rfl⟩
    have ht2 : t * t = 1 := ThreeTransposition.mul_self_of_orderOf h.orderOf_t
    intro heq
    have hx : t * (n⁻¹ * t * n) ∈ {x | x ∈ closure (orb E t) ∧ x ≠ 1} := by
      refine ⟨mul_mem (subset_closure ToddOrbit.t_mem_orb) (subset_closure hs), fun h1 => hne ?_⟩
      calc n⁻¹ * t * n = t * t * (n⁻¹ * t * n) := by rw [ht2, one_mul]
        _ = t := by rw [mul_assoc, h1, mul_one]
    rw [heq] at hx
    exact h.mul_notMem_orb f hf ToddOrbit.t_mem_orb hs (Ne.symm hne) hx
  · rw [hTD]
    exact h.not_transitive hf

end FischerHyp

end CFSG.EvenSmallLie.UnitarySix.Fischer
