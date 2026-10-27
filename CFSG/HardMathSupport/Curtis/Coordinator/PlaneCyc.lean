module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycBlockFacts
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPL
public import CFSG.HardMathSupport.Curtis.Coordinator.PlaneBlock
public import CFSG.HardMathSupport.Curtis.Coordinator.PlaneElem
public import CFSG.HardMathSupport.Curtis.Coordinator.PlaneTypes
import CFSG.HardMathSupport.Curtis.Coordinator.BlockGlue
import CFSG.HardMathSupport.Curtis.Coordinator.ToralThreeReduce
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchGlue

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.Plane

open CFSG.AGLEmbedding CFSG.Open CFSG.QuasithinUnique

theorem exists_mul_of_mem_sup_centralizer' {Y : Type} [Group Y] {L : Subgroup Y} {u : Y}
    (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)) :
    ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), u = l * c := by
  have hCN : L ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set Y) : Set Y) :=
    CFSG.AGLEmbedding.ToralCensus.le_normalizer_centralizer L
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCN] at hu
  obtain ⟨l, hl, c, hc, rfl⟩ := hu
  exact ⟨l, hl, c, hc, rfl⟩

theorem eq_one_of_central_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hperf : commutator X = ⊤) : ∀ z : X, (∀ w, w * z = z * w) → z = 1 := by
  intro z hz
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · have : z ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr hz
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  · exfalso
    have h1 : commutator X = ⊥ := (_root_.commutator_eq_bot_iff_center_eq_top X).mpr h
    rw [hperf] at h1
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    have ha : a = 1 := Subgroup.mem_bot.mp (h1 ▸ Subgroup.mem_top a)
    have hb : b = 1 := Subgroup.mem_bot.mp (h1 ▸ Subgroup.mem_top b)
    exact hab (ha.trans hb.symm)

theorem not_sq_dvd_of_prime {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hN : N = 1080 ∨ N = 2520) :
    ¬ p ^ 2 ∣ N := by
  intro h
  have hle : p ^ 2 ≤ N := Nat.le_of_dvd (by rcases hN with rfl | rfl <;> norm_num) h
  have hp50 : p ≤ 50 := by rcases hN with rfl | rfl <;> nlinarith
  rcases hN with rfl | rfl <;> interval_cases p <;>
    first | exact absurd hp (by decide) | exact absurd h (by decide)

section Block

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

omit [Finite G] in
theorem eq_one_of_mem_center_barM {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥(barM M L))) {ζ : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hζL : ζ ∈ barM M L)
    (hζC : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hζp : ζ ^ p = 1) : ζ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hzc : (⟨ζ, hζL⟩ : ↥(barM M L)) ∈ Subgroup.center ↥(barM M L) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_centralizer_iff.mp hζC g g.2)
  set z : ↥(Subgroup.center ↥(barM M L)) := ⟨⟨ζ, hζL⟩, hzc⟩ with hz
  have hzp : z ^ p = 1 := Subtype.ext (Subtype.ext (by simpa using hζp))
  have hz1 : z ≠ 1 := fun h => hne (congrArg (fun w : ↥(Subgroup.center ↥(barM M L)) =>
    ((w : ↥(barM M L)) : ↥M ⧸ CFSG.pCore 2 ↥M)) h)
  have : orderOf z = p := orderOf_eq_prime hzp hz1
  exact hZ (this ▸ orderOf_dvd_natCard z)

omit [Finite G] in
theorem eq_one_of_center_alt {m : ℕ} (hm : 4 ≤ m) (e : ↥(barM M L) ≃* alternatingGroup (Fin m))
    {ζ : ↥M ⧸ CFSG.pCore 2 ↥M} (hζL : ζ ∈ barM M L)
    (hζC : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : ζ = 1 := by
  have hc0 := alternatingGroup.center_eq_bot (α := Fin m) (by rw [Nat.card_fin]; exact hm)
  have hmem : e ⟨ζ, hζL⟩ ∈ Subgroup.center (alternatingGroup (Fin m)) := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (Subgroup.mem_centralizer_iff.mp hζC g' g'.2))
  rw [hc0, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hmem
  exact congrArg Subtype.val hmem

omit [Finite G] in
theorem eq_one_of_center_card_three {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3) {ζ : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hζL : ζ ∈ barM M L)
    (hζC : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hζp : ζ ^ p = 1) : ζ = 1 := by
  refine eq_one_of_mem_center_barM hp (fun h => ?_) hζL hζC hζp
  rw [hZ] at h
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  omega

@[expose] def ZetaOK (M S L : Subgroup G) (p : ℕ) : Prop :=
  ∀ ζ ∈ blockPL M S L, ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
    ζ ^ p = 1 → ζ = 1

omit [Finite G] in
theorem zetaOK_of_psi {X : Type*} [Group X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (e : ↥(blockPL M S L) ⧸ CFSG.pCore 2 ↥(blockPL M S L) ≃* X)
    (hX : ∀ z : X, (∀ w, w * z = z * w) → z ^ p = 1 → z = 1) : ZetaOK M S L p := by
  obtain ⟨ψ, hψ, hker⟩ := exists_psi e
  intro ζ hζJ hζC hζp
  have h := eq_one_of_central hp (by omega) ψ hψ hker hX ⟨ζ, hζJ⟩ (fun w => Subtype.ext ?_)
    (Subtype.ext (by simpa using hζp))
  · exact congrArg Subtype.val h
  · exact Subgroup.mem_centralizer_iff.mp hζC w (blockPL_le_barM w.2)

variable (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
  (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)

include hK hA hL hX hS in
theorem three_data (hTPL : CitedBlockTransvectionPL) (h3 : NineThreeThree M S L) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : PLGood (blockPL M S L) p ∧ ZetaOK M S L p := by
  have hp2 : p ≠ 2 := by omega
  rcases hTPL G M S L hK hA hL hX hS h3 with ⟨k, d, hk, ⟨q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · obtain ⟨hsimple, -⟩ := kFactSpTwoSimple_holds k d hk ⟨q, hq, hd⟩
    have hperf := kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds k d hk ⟨q, hq, hd⟩
    refine ⟨plGood_of_perfect hp hp2 e ⊤ (Subgroup.isPerfect_iff.mpr (by
      rw [← commutator_def]; exact hperf)) (fun _ _ => Subgroup.mem_top _),
      zetaOK_of_psi hp hp5 e ?_⟩
    have := hsimple
    exact fun z hz _ => eq_one_of_central_of_simple hperf z hz
  · exact ⟨plGood_perm hp hp5 e,
      zetaOK_of_psi hp hp5 e fun z hz hzp => perm_central_p hp hp5 z hz hzp⟩

omit [Finite G] in
theorem four_data (h4 : NineThreeFour M S L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PLGood (blockPL M S L) p ∧ ZetaOK M S L p := by
  obtain ⟨-, hZ3, ⟨e⟩, -⟩ := h4
  refine ⟨Or.inl fun h => ?_, fun ζ hζJ hζC hζp =>
    eq_one_of_center_card_three hp hp5 hZ3 (blockPL_le_barM hζJ) hζC hζp⟩
  have h1 : Nat.card (blockPL M S L) ∣ Nat.card (barM M L) :=
    Subgroup.card_dvd_of_le (blockPL_le_barM)
  have h2 : Nat.card ↥(barM M L) = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(barM M L)),
      Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hZ3]
    decide
  rw [h2] at h1
  exact not_sq_dvd_of_prime hp hp5 (Or.inl rfl) (h.trans h1)

omit [Finite G] in
theorem five_data (h5 : NineThreeFive M L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PLGood (blockPL M S L) p ∧ ZetaOK M S L p := by
  obtain ⟨-, ⟨e⟩, -⟩ := h5
  refine ⟨Or.inl fun h => ?_, fun ζ hζJ hζC hζp =>
    eq_one_of_center_alt (by norm_num) e (blockPL_le_barM hζJ) hζC⟩
  have h1 : Nat.card (blockPL M S L) ∣ Nat.card (barM M L) :=
    Subgroup.card_dvd_of_le (blockPL_le_barM)
  have h2 : Nat.card ↥(barM M L) = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  rw [h2] at h1
  exact not_sq_dvd_of_prime hp hp5 (Or.inr rfl) (h.trans h1)

theorem six_data (h6 : NineThreeSix M S L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PLGood (blockPL M S L) p ∧ ZetaOK M S L p := by
  obtain ⟨-, n, -, ⟨e⟩⟩ := h6
  exact ⟨plGood_perm hp hp5 e,
    zetaOK_of_psi hp hp5 e fun z hz hzp => perm_central_p hp hp5 z hz hzp⟩

include hL in
theorem seven_data (h7 : NineThreeSeven M S L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PLGood (blockPL M S L) p ∧ ZetaOK M S L p := by
  obtain ⟨-, n, ⟨e⟩, ⟨eP⟩⟩ := h7
  have := barM_isPerfect hL
  have := barM_nontrivial hL
  have h5 := five_le_of_isPerfect_mulEquiv_alternatingGroup e
  exact ⟨plGood_perm hp hp5 eP, fun ζ hζJ hζC _ =>
    eq_one_of_center_alt (by omega) e (blockPL_le_barM hζJ) hζC⟩

include hL in
theorem eight_data (h8 : NineThreeEight M S L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PLGood (blockPL M S L) p ∧ ZetaOK M S L p := by
  obtain ⟨-, N, r, ⟨m, hm⟩, hr, h0, h2, h4, ⟨e⟩, φ, -⟩ := h8
  have := barM_isPerfect hL
  have := barM_nontrivial hL
  have h5 := five_le_of_isPerfect_mulEquiv_alternatingGroup e
  exact ⟨plGood_perm_prod hp hp5 (by omega) φ, fun ζ hζJ hζC _ =>
    eq_one_of_center_alt (by omega) e (blockPL_le_barM hζJ) hζC⟩

end Block

section Main

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

omit [Finite G] in
theorem clauses_of_good {p : ℕ} (hp : p.Prime)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M S L → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup p Q → IsCyclic Q)
    (hgood : PLGood (blockPL M S L) p) (hzeta : ZetaOK M S L p) {u : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hu : u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hup : u ^ p = 1)
    (huC : u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hfix : ∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L) :
    (∀ ζ ∈ barM M L, ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      ζ ^ p = 1 → ζ = 1) ∧
    (u ∈ barM M L → ∀ v ∈ barM M L, v ^ p = 1 → v * u = u * v → v ∉ Subgroup.zpowers u →
      ∀ y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        (∃ k : ℕ, y ^ p ^ k = 1) → y * v * y⁻¹ = v → y * u * y⁻¹ ≠ u * v) := by
  obtain ⟨l₀, hl₀, c, hc, hu_eq⟩ := exists_mul_of_mem_sup_centralizer' hu
  refine ⟨fun ζ hζL hζC hζp => hzeta ζ (hfix ζ hζL ?_) hζC hζp, ?_⟩
  ·
    have h1 : ζ * c = c * ζ := Subgroup.mem_centralizer_iff.mp hc ζ hζL
    have h2 : l₀ * ζ = ζ * l₀ := Subgroup.mem_centralizer_iff.mp hζC l₀ hl₀
    rw [hu_eq]
    calc l₀ * c * ζ * (l₀ * c)⁻¹ = l₀ * (c * ζ) * c⁻¹ * l₀⁻¹ := by group
      _ = l₀ * (ζ * c) * c⁻¹ * l₀⁻¹ := by rw [h1]
      _ = l₀ * ζ * l₀⁻¹ := by group
      _ = ζ := by rw [h2]; group
  · intro huL v hvL hvp hvu hvnot y _ _ _ _
    exfalso
    have huJ : u ∈ blockPL M S L := hfix u huL (by rw [mul_inv_cancel_right])
    have hvJ : v ∈ blockPL M S L := hfix v hvL (by rw [← hvu, mul_inv_cancel_right])
    have hu1 : u ≠ 1 := fun h => huC (h ▸ Subgroup.one_mem _)
    obtain ⟨E, hEel, hEc, -, -, hEmin, -⟩ :=
      exists_elemAbelian_of_two hp (hvu.symm : Commute u v) hup hvp hu1 hvnot
    exact hgood.false_of_plane hp hcyc (hEmin _ huJ hvJ) hEel hEc

theorem clauses_two (hC : KFactFixCensusPrime) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h2 : NineThreeTwo M S L) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M S L → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup p Q → IsCyclic Q)
    {u : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hu : u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hup : u ^ p = 1)
    (huC : u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hV : ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
      V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      V ≤ Subgroup.normalizer (barM M (S ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ u ∈ V)
    (hfix : ∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L) :
    (∀ ζ ∈ barM M L, ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      ζ ^ p = 1 → ζ = 1) ∧
    (u ∈ barM M L → ∀ v ∈ barM M L, v ^ p = 1 → v * u = u * v → v ∉ Subgroup.zpowers u →
      ∀ y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        (∃ k : ℕ, y ^ p ^ k = 1) → y * v * y⁻¹ = v → y * u * y⁻¹ ≠ u * v) := by
  have hCP := compParab_of_nineThreeTwo hA hL hS h2
  obtain ⟨V, hVp, hVL, hVSL, huV⟩ := hV
  have hVO : V ≤ Subgroup.normalizer
      (pCoreOf 2 (blockPL M S L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [← h2.2.2]
    exact hVSL
  obtain ⟨hZ, hcase⟩ := hC _ (barM M L) (blockPL M S L) hCP p hp hp5 hcyc u hu hup huC
    ⟨V, hVp, hVL, hVO, huV⟩ hfix
  refine ⟨fun ζ hζL hζC hζp => eq_one_of_mem_center_barM hp hZ hζL hζC hζp, ?_⟩
  intro huL v hvL hvp hvu hvnot y hy hyp hyv hyuv
  exfalso
  have hu1 : u ≠ 1 := fun h => huC (h ▸ Subgroup.one_mem _)
  obtain ⟨E, hEel, hEc, huE, hvE, hEmin, hEmem⟩ :=
    exists_elemAbelian_of_two hp (hvu.symm : Commute u v) hup hvp hu1 hvnot
  have hEL : E ≤ barM M L := hEmin _ huL hvL
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; exact pow_ne_zero 2 hp.ne_zero)
  have hyE : y ∈ Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_of_conj huE hvE hEmem hyv hyuv
  rcases hcase with hcyc' | ⟨e, -, ⟨φ⟩⟩
  · have hEC : E ≤ barM M L ⊓ Subgroup.centralizer ({u} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      refine le_inf hEL fun x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.mp hk]
      have := hEel.1.is_comm.comm (⟨u, huE⟩ : ↥E) ⟨x, hx⟩
      exact congrArg Subtype.val this
    have : Fact p.Prime := ⟨hp⟩
    exact absurd (hcyc' E hEC (IsPGroup.of_card (n := 2) hEc))
      (ToralCensus.not_isCyclic_of_elemAbelian_pow hp (by norm_num) hEel hEc)
  · have hall := plane_core hp hp5 hZ φ hEL hEel hEc hy hyE hyp u huE
    have h1 : u * v = u := hyuv.symm.trans hall
    have h2' : v = 1 := by simpa using h1
    exact hvnot (h2' ▸ Subgroup.one_mem _)

end Main

theorem citedBlockToralCycAut_of_census (hC : KFactFixCensusPrime)
    (hTPL : CitedBlockTransvectionPL) : CitedBlockToralCycAut := by
  intro G _ _ M S L p hK hA hL h93 hX hS hp hp5 hcyc u hu hup huC hV hfix
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact (hX h1).elim
  · exact clauses_two hC hA hL hS h2 hp hp5 hcyc hu hup huC hV hfix
  · obtain ⟨hg, hz⟩ := three_data hK hA hL hX hS hTPL h3 hp hp5
    exact clauses_of_good hp hcyc hg hz hu hup huC hfix
  · obtain ⟨hg, hz⟩ := four_data h4 hp hp5
    exact clauses_of_good hp hcyc hg hz hu hup huC hfix
  · obtain ⟨hg, hz⟩ := five_data h5 hp hp5
    exact clauses_of_good hp hcyc hg hz hu hup huC hfix
  · obtain ⟨hg, hz⟩ := six_data h6 hp hp5
    exact clauses_of_good hp hcyc hg hz hu hup huC hfix
  · obtain ⟨hg, hz⟩ := seven_data hL h7 hp hp5
    exact clauses_of_good hp hcyc hg hz hu hup huC hfix
  · obtain ⟨hg, hz⟩ := eight_data hL h8 hp hp5
    exact clauses_of_good hp hcyc hg hz hu hup huC hfix

end CFSG.HardMathSupport.Curtis.Coordinator.Plane
