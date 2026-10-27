module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinAut

public section

namespace CFSG.QuasithinUnique.Out21

open CFSG.Open CFSG.GorensteinWalter
open scoped MatrixGroups

section Setup

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

omit [Field F] [Finite F] in
theorem hodd_of (hp7 : 7 ≤ p) (hF : Nat.card F = p) : IsOddPrimePower (Nat.card F) :=
  Unc25K1.isOddPrimePower_of_card_prime hp7 hF

omit [Field F] [Finite F] [Fact p.Prime] in
theorem three_lt (hp7 : 7 ≤ p) (hF : Nat.card F = p) : 3 < Nat.card F := by
  rw [hF]
  omega

theorem finite_pgl2 : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

@[expose] noncomputable def autPGL (hp7 : 7 ≤ p) (hF : Nat.card F = p) : PGL2 F →* MulAut (PSL2 F) :=
  pgl2InnerAutPSL2 F (hodd_of hp7 hF) (three_lt hp7 hF)

theorem autPGL_injective (hp7 : 7 ≤ p) (hF : Nat.card F = p) :
    Function.Injective (autPGL hp7 hF) :=
  pgl2InnerAutPSL2_injective F _ _

theorem autPGL_surjective (hp7 : 7 ≤ p) (hF : Nat.card F = p) :
    Function.Surjective (autPGL hp7 hF) := by
  intro α
  have hKpow : Nat.card F = p ^ 1 := by rw [hF, pow_one]
  obtain ⟨xx, hxx⟩ := pGammaL2ToMulAutPSL2_surjective F hKpow (hodd_of hp7 hF) (three_lt hp7 hF) α
  have h := congrArg (pGammaL2ToMulAutPSL2 F (hodd_of hp7 hF) (three_lt hp7 hF))
    (SemidirectProduct.inl_left_mul_inr_right xx)
  rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr, hxx] at h
  have hσ : xx.right = 1 :=
    (CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime F hF).elim _ _
  rw [hσ, map_one, mul_one] at h
  exact ⟨xx.left, h⟩

@[expose] noncomputable def autEquiv (hp7 : 7 ≤ p) (hF : Nat.card F = p) : PGL2 F ≃* MulAut (PSL2 F) :=
  MulEquiv.ofBijective (autPGL hp7 hF) ⟨autPGL_injective hp7 hF, autPGL_surjective hp7 hF⟩

theorem autEquiv_apply (hp7 : 7 ≤ p) (hF : Nat.card F = p) (g : PGL2 F) :
    autEquiv hp7 hF g = autPGL hp7 hF g := rfl

theorem card_aut (hp7 : 7 ≤ p) (hF : Nat.card F = p) :
    Nat.card (MulAut (PSL2 F)) = 2 * Nat.card (PSL2 F) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [← Nat.card_congr (autEquiv hp7 hF).toEquiv, pgl2_card_formula F,
    psl2_card_formula F (hodd_of hp7 hF), hF]
  obtain ⟨k, hk⟩ := hpodd
  have h1 : p ^ 2 - 1 = 2 * (2 * k ^ 2 + 2 * k) := by
    have : p ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by rw [hk]; ring
    omega
  have h2 : p * (p ^ 2 - 1) = 2 * (p * (2 * k ^ 2 + 2 * k)) := by rw [h1]; ring
  rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem exists_injective_dihedral (hp7 : 7 ≤ p) (hF : Nat.card F = p)
    (P : Subgroup (MulAut (PSL2 F))) (hP : IsPGroup 2 P) :
    ∃ (m : ℕ) (f : ↥P →* DihedralGroup (2 ^ m)), Function.Injective f := by
  have := finite_pgl2 (F := F)
  set e := autEquiv hp7 hF with he
  let ι : ↥P ≃* ↥(P.map e.symm.toMonoidHom) :=
    Subgroup.equivMapOfInjective P e.symm.toMonoidHom e.symm.injective
  have hP' : IsPGroup 2 ↥(P.map e.symm.toMonoidHom) := hP.of_equiv ι
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨m, -, ⟨eQ⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F (hodd_of hp7 hF) Q
  refine ⟨m, eQ.toMonoidHom.comp ((Subgroup.inclusion hQ).comp ι.toMonoidHom), ?_⟩
  intro a b hab
  have h1 := eQ.injective hab
  exact ι.injective (Subgroup.inclusion_injective hQ h1)

theorem mem_innerAut_iff (hp7 : 7 ≤ p) (hF : Nat.card F = p) (α : MulAut (PSL2 F)) :
    α ∈ innerAut (PSL2 F) ↔ (autEquiv hp7 hF).symm α ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    apply (autEquiv hp7 hF).injective
    rw [MulEquiv.apply_symm_apply, autEquiv_apply, autPGL]
    exact pgl2InnerAutPSL2_toPGL F _ _ y
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have : α = autEquiv hp7 hF (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := by
      rw [hy, MulEquiv.apply_symm_apply]
    rw [this, autEquiv_apply, autPGL, pgl2InnerAutPSL2_toPGL F _ _ y]

end Setup

section Outer

variable {Y : Type*} [Group Y]

@[expose] def HasTorus (J : Subgroup Y) (g : Y) : Prop :=
  ∃ (U : Subgroup Y) (w : Y), IsCyclic ↥U ∧ Nat.card ↥U % 4 = 2 ∧ 6 ≤ Nat.card ↥U ∧ g ∈ U ∧
    ¬ U ≤ J ∧ (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧
    Subgroup.centralizer ({g} : Set Y) = U ⊔ Subgroup.zpowers w

theorem HasTorus.map {J : Subgroup Y} {s : Y} (h : HasTorus J s) (φ : Y ≃* Y)
    (hJ : ∀ y, φ y ∈ J ↔ y ∈ J) : HasTorus J (φ s) := by
  obtain ⟨U, w, hcyc, h4, h6, hsU, hUJ, hw, hC⟩ := h
  refine ⟨U.map φ.toMonoidHom, φ w, ?_, ?_, ?_, ⟨s, hsU, rfl⟩, ?_, ?_, ?_⟩
  · exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective U φ.toMonoidHom φ.injective)).mp hcyc
  · rw [Subgroup.card_map_of_injective φ.injective]; exact h4
  · rw [Subgroup.card_map_of_injective φ.injective]; exact h6
  · intro hle
    apply hUJ
    intro x hx
    exact (hJ x).mp (hle ⟨x, hx, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    show φ w * φ y * (φ w)⁻¹ = (φ y)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, hw y hy]
    simp
  · have hcent : Subgroup.centralizer ({φ s} : Set Y) =
        (Subgroup.centralizer ({s} : Set Y)).map φ.toMonoidHom := by
      ext y
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map_equiv,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hy
        have := congrArg φ.symm hy
        simpa using this
      · intro hy
        have := congrArg φ hy
        simpa using this
    rw [hcent, hC, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl

theorem HasTorus.oddNormal {J : Subgroup Y} (hJ : J.index = 2) {s : Y} (hs2 : s * s = 1)
    (hs1 : s ≠ 1) (h : HasTorus J s) :
    s ∉ J ∧ ∃ N : Subgroup Y, N ≠ ⊥ ∧ Odd (Nat.card ↥N) ∧
      N ≤ J ⊓ Subgroup.centralizer ({s} : Set Y) ∧
      J ⊓ Subgroup.centralizer ({s} : Set Y) ≤ Subgroup.normalizer (N : Set Y) := by
  obtain ⟨U, w, hcyc, h4, h6, hsU, hUJ, hw, hC⟩ := h
  have hJn : J.Normal := Subgroup.normal_of_index_eq_two hJ
  set N : Subgroup Y := U ⊓ J with hN
  have hrel : J.relIndex U = 2 := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal J U
    rw [hJ] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (Subgroup.relIndex_eq_one.mp h1) hUJ
    · exact h1
  have hcardN : Nat.card ↥N * 2 = Nat.card ↥U := by
    have h1 := Subgroup.card_mul_index (N.subgroupOf U)
    have h2 : (N.subgroupOf U).index = 2 := by
      show N.relIndex U = 2
      rw [hN, Subgroup.inf_relIndex_left]
      exact hrel
    rw [h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ≤ U)).toEquiv] at h1
    exact h1
  have hNodd : Odd (Nat.card ↥N) := by
    rw [Nat.odd_iff]
    omega
  have hN3 : 3 ≤ Nat.card ↥N := by omega
  have hsJ : s ∉ J := by
    intro hsJ
    have hsN : s ∈ N := ⟨hsU, hsJ⟩
    have hord : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
    have := Subgroup.orderOf_dvd_natCard N hsN
    rw [hord] at this
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr this)
  have hwN : w ∈ Subgroup.normalizer (U : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hw x hx]
      exact U.inv_mem hx
    · intro hx
      have h1 := hw _ hx
      have h2 : w * x * w⁻¹ = x⁻¹ := by
        calc w * x * w⁻¹ = w⁻¹ * (w * (w * x * w⁻¹) * w⁻¹) * w := by group
          _ = w⁻¹ * (w * x⁻¹ * w⁻¹) * w := by rw [h1]; group
          _ = x⁻¹ := by group
      have h3 : x⁻¹ ∈ U := h2 ▸ hx
      simpa using U.inv_mem h3
  refine ⟨hsJ, N, ?_, hNodd, ?_, ?_⟩
  · intro hbot
    rw [hbot] at hN3
    simp at hN3
  · exact le_inf inf_le_right (inf_le_left.trans (hC ▸ le_sup_left))
  · intro x hx
    have hxU : x ∈ Subgroup.normalizer (U : Set Y) := by
      have hxc : x ∈ U ⊔ Subgroup.zpowers w := hC ▸ hx.2
      exact (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hwN) :
        U ⊔ Subgroup.zpowers w ≤ Subgroup.normalizer (U : Set Y)) hxc
    rw [Subgroup.mem_normalizer_iff] at hxU ⊢
    intro g
    refine (and_congr (hxU g) ?_)
    constructor
    · intro hg
      exact hJn.conj_mem g hg x
    · intro hg
      have := hJn.conj_mem _ hg x⁻¹
      simpa [mul_assoc] using this

end Outer

section Embed

theorem oddNormalFix_of_embed {X Y : Type*} [Group X] [Group Y] (ι : X →* Y)
    (hι : Function.Injective ι) (α : MulAut X) (g : Y) (hα : ∀ x, ι (α x) = g * ι x * g⁻¹)
    (N₀ : Subgroup Y) (hN0 : N₀ ≠ ⊥) (hNodd : Odd (Nat.card ↥N₀)) (hNJ : N₀ ≤ ι.range)
    (hNC : N₀ ≤ Subgroup.centralizer ({g} : Set Y))
    (hNnorm : Subgroup.centralizer ({g} : Set Y) ⊓ ι.range ≤ Subgroup.normalizer (N₀ : Set Y)) :
    OddNormalFix α := by
  refine ⟨N₀.comap ι, ?_, ?_, ?_, ?_⟩
  · intro hbot
    apply hN0
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := hNJ hy
    have hx : x ∈ N₀.comap ι := hy
    rw [hbot, Subgroup.mem_bot] at hx
    rw [hx, map_one]
    exact Subgroup.one_mem _
  · have hmap : (N₀.comap ι).map ι = N₀ := Subgroup.map_comap_eq_self hNJ
    rw [← hmap] at hNodd
    rwa [Subgroup.card_map_of_injective hι] at hNodd
  · intro x hx
    have hc : g * ι x = ι x * g :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hNC hx)).symm
    show α x = x
    apply hι
    rw [hα x]
    calc g * ι x * g⁻¹ = (ι x * g) * g⁻¹ := by rw [hc]
      _ = ι x := by group
  · intro x hx
    have hx' : α x = x := hx
    have hc : ι x ∈ Subgroup.centralizer ({g} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hα x
      rw [hx'] at this
      calc ι x * g = (g * ι x * g⁻¹) * g := by rw [← this]
        _ = g * ι x := by group
    have hn := Subgroup.mem_normalizer_iff.mp (hNnorm ⟨hc, x, rfl⟩)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_comap, map_mul, map_inv]
    exact hn (ι y)

end Embed

section OuterMain

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

theorem exists_torus_involution (hp7 : 7 ≤ p) (hF : Nat.card F = p) :
    ∃ s : PGL2 F, s ≠ 1 ∧ s * s = 1 ∧
      HasTorus (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range s := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hoddF : Odd (Nat.card F) := by rw [hF]; exact hpodd
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by
    have := Nat.odd_iff.mp hpodd
    omega
  rcases h4 with h4 | h4
  · obtain ⟨U, s, w, hcyc, hcard, hsU, hss, hs1, hwU, hw2, hwinv, hC, hcross⟩ :=
      pgl2_nonsplit_torus_centralizer_data F hoddF
    have hc4 : Nat.card ↥U % 4 = 2 := by rw [hcard, hF]; omega
    have hc6 : 6 ≤ Nat.card ↥U := by rw [hcard, hF]; omega
    exact ⟨s, hs1, hss, U, w, hcyc, hc4, hc6, hsU, hcross hoddF, hwinv, hC⟩
  · obtain ⟨U, s, w, hcyc, hcard, hsU, hss, hs1, hwU, hw2, hwinv, hC, hcross⟩ :=
      pgl2_split_torus_centralizer_data F hoddF
    have hc4 : Nat.card ↥U % 4 = 2 := by rw [hcard, hF]; omega
    have hc6 : 6 ≤ Nat.card ↥U := by rw [hcard, hF]; omega
    exact ⟨s, hs1, hss, U, w, hcyc, hc4, hc6, hsU, hcross hoddF, hwinv, hC⟩

theorem oddNormalFix_of_outer_involution (hp7 : 7 ≤ p) (hF : Nat.card F = p)
    {α : MulAut (PSL2 F)} (hα2 : α * α = 1) (hαi : α ∉ innerAut (PSL2 F)) : OddNormalFix α := by
  have := finite_pgl2 (F := F)
  set e := autEquiv hp7 hF with he
  set J : Subgroup (PGL2 F) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hJdef
  have hodd := hodd_of hp7 hF
  have hcard := three_lt hp7 hF
  have hJcomm : commutator (PGL2 F) = J :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three F hodd hcard
  have hJidx : J.index = 2 := pgl2_psl2Range_index_eq_two F hodd
  have hJn : J.Normal := Subgroup.normal_of_index_eq_two hJidx
  set g := e.symm α with hg
  have hg2 : g * g = 1 := by
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, hα2, map_one]
  have hgJ : g ∉ J := fun h => hαi ((mem_innerAut_iff hp7 hF α).mpr h)
  have hg1 : g ≠ 1 := fun h => hgJ (h ▸ J.one_mem)
  obtain ⟨s, hs1, hs2, hT⟩ := exists_torus_involution hp7 hF
  obtain ⟨hsJ, -⟩ := hT.oddNormal hJidx hs2 hs1
  have hconj : IsConj g s :=
    pgl2_outer_involutions_conjugate F hodd hcard ⟨hg1, by rw [pow_two]; exact hg2⟩
      ⟨hs1, by rw [pow_two]; exact hs2⟩ (by rw [hJcomm]; exact hgJ) (by rw [hJcomm]; exact hsJ)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  let φ : PGL2 F ≃* PGL2 F := MulAut.conj c⁻¹
  have hφs : φ s = g := by
    show c⁻¹ * s * c⁻¹⁻¹ = g
    rw [← hc]
    group
  have hJφ : ∀ y, φ y ∈ J ↔ y ∈ J := by
    intro y
    constructor
    · intro hy
      have := hJn.conj_mem _ hy c
      simpa [φ, MulAut.conj_apply, mul_assoc] using this
    · intro hy
      exact hJn.conj_mem y hy c⁻¹
  have hTg : HasTorus J g := hφs ▸ hT.map φ hJφ
  obtain ⟨-, N₀, hN01, hN0odd, hN0le, hN0norm⟩ := hTg.oddNormal hJidx hg2 hg1
  refine oddNormalFix_of_embed (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))
    (fun a b h => Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h) α g ?_ N₀ hN01 hN0odd
    (hN0le.trans inf_le_left) (hN0le.trans inf_le_right) ?_
  · intro x
    have hαg : α = autPGL hp7 hF g := by
      rw [← autEquiv_apply, hg, MulEquiv.apply_symm_apply]
    rw [hαg]
    exact toPGL_pgl2InnerAutPSL2_apply F hodd hcard g x
  · exact fun x hx => hN0norm ⟨hx.2, hx.1⟩

end OuterMain

end CFSG.QuasithinUnique.Out21
