module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightUPRigid
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightUKey

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary (SU rootHom coe_rootHom rootMatrix)
open CFSG.LieType.Universal.Symplectic.SpExtras (elt mat_elt E)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Diff

variable {N ε : ℕ} {K F : Type} [Field K] [Field F] [CharP K 2] {hε : ε ≤ 1} {σ : F ≃+* F}
  {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}

theorem coe_ctuEmbed_elt_difference {p p' : Fin N} (hpp : p ≠ p') (c : K) :
    (((ctuEmbed ε hε σ ι hι (elt (.difference p p' hpp) c) : SU σ (2 * N + ε)) :
      GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
        1 + single (ctuCoord N ε (Sum.inl (Sum.inl p))) (ctuCoord N ε (Sum.inl (Sum.inl p')))
          (ι c) - single (ctuCoord N ε (Sum.inl (Sum.inr p'))) (ctuCoord N ε (Sum.inl (Sum.inr p)))
            (ι c) := by
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  rw [ctuEmbed_apply_ctuCoord, mat_elt, Matrix.sub_apply, Matrix.add_apply, single_apply,
    single_apply, one_apply]
  simp only [(ctuCoord N ε).injective.eq_iff]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, map_apply, Matrix.add_apply, Matrix.smul_apply, one_apply]
    simp only [E, Matrix.sub_apply, single_apply, Sum.inl.injEq, smul_eq_mul]
    split_ifs <;> simp_all [sub_eq_add_neg]
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₂, one_apply]
    simp

theorem ctuEmbed_elt_difference_eq_rootHom (hσ : ∀ c, σ (σ c) = c) {p p' : Fin N}
    (hpp : p ≠ p') {i j : Fin (2 * N + ε)} (hi : ctuCoord N ε (Sum.inl (Sum.inl p)) = i)
    (hj : ctuCoord N ε (Sum.inl (Sum.inl p')) = j) (hij : i ≠ j) (hii : i ≠ Fin.rev i)
    (hjj : j ≠ Fin.rev j) (c : K) :
    ctuEmbed ε hε σ ι hι (elt (.difference p p' hpp) c) =
      rootHom σ hσ hij hii hjj (Multiplicative.ofAdd (ι c)) := by
  subst hi hj
  apply Subtype.ext
  apply Units.ext
  rw [coe_ctuEmbed_elt_difference, coe_rootHom, toAdd_ofAdd, rootMatrix, hι, ctuCoord_rev hε,
    ctuCoord_rev hε, ctuPar_inl, ctuPar_inl, par_inl, par_inl]

end Diff

section Conj

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c} {e : L ≃* StatedSp 4 K}

theorem NsUniParam.exists_barPow_of_conj_long_swap (hK : Nat.card K = 2)
    (hF : Nat.card F = (2 ^ 1) ^ 2) {k l : Fin 4} (hkl : k ≠ l)
    (P : NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k) {h : G}
    (hN : h ∈ normalizer (centralizerPerfectCore (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l)) :
      Set G))
    {S : Set (StatedSp 4 K)}
    (hSpos : ∀ p, p ∉ ({k, l} : Finset (Fin 4)) → ∀ c : K, elt (.positiveLong p) c ∈ S)
    (hSneg : ∀ p, p ∉ ({k, l} : Finset (Fin 4)) → ∀ c : K, elt (.negativeLong p) c ∈ S)
    (hSswap : ∀ p p', p ∉ ({k, l} : Finset (Fin 4)) → p' ∉ ({k, l} : Finset (Fin 4)) → p ≠ p' →
      permSp K (Equiv.swap p p') ∈ S)
    (hfix : ∀ y ∈ spBlock K ({k, l} : Finset (Fin 4))ᶜ, y ∈ S →
      h * ((e.symm y : L) : G) = ((e.symm y : L) : G) * h) :
    ∃ b : Bool, ∀ (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4))),
      h * P.Φ ⟨x, ctuBlock_pair_le_left _ k l hx⟩ * h⁻¹ =
        P.Φ ⟨barPow (unitaryInvolution_involutive hF) b x, ctuBlock_pair_le_left _ k l
          ((barPow_mem_ctuBlock_iff _ b _ x).2 hx)⟩ := by
  classical
  set σ := unitaryInvolution F 2 1 with hσdef
  set B := ctuBlock σ 0 ({k, l} : Finset (Fin 4)) with hB
  set φ : B →* G := P.Φ.comp (Subgroup.inclusion (ctuBlock_pair_le_left σ k l)) with hφ
  have hφapp : ∀ z : B, φ z = P.Φ ⟨z, ctuBlock_pair_le_left σ k l z.2⟩ := fun z => rfl
  have hφinj : Function.Injective φ := fun x y hxy => by
    have h' := P.injOn_ctuBlock hF (by norm_num) hkl (x := ⟨x, ctuBlock_pair_le_left σ k l x.2⟩)
      (y := ⟨y, ctuBlock_pair_le_left σ k l y.2⟩) (ctuBlock_pair_le_right σ k l x.2)
      (ctuBlock_pair_le_right σ k l y.2) hxy
    exact Subtype.ext (congrArg (fun w : ctuBlock σ 0 ({k} : Finset (Fin 4)) =>
      (w : SU σ (2 * 4 + 0))) h')
  have hover := P.overlap_eq hF hkl
  have hex : ∀ z : B, ∃ z' : B, h * φ z * h⁻¹ = φ z' := by
    intro z
    have hz : φ z ∈ centralizerPerfectCore (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l)) := by
      rw [← hover]
      exact ⟨⟨z, ctuBlock_pair_le_left σ k l z.2⟩, mem_subgroupOf.2 z.2, rfl⟩
    have hz' := (mem_normalizer_iff.1 hN (φ z)).1 hz
    rw [← hover] at hz'
    obtain ⟨w, hw, hw'⟩ := hz'
    exact ⟨⟨w, mem_subgroupOf.1 hw⟩, hw'.symm⟩
  choose f hf using hex
  have hfmul : ∀ z w : B, f (z * w) = f z * f w := fun z w => hφinj (by
    rw [← hf, map_mul, map_mul, ← hf, ← hf]
    group)
  have hfinj : Function.Injective f := fun z w hzw => hφinj (by
    have h1 := hf z
    have h2 := hf w
    rw [hzw, ← h2] at h1
    have h3 := congrArg (fun g => h⁻¹ * g * h) h1
    simpa [mul_assoc] using h3)
  have : Finite (GL (Fin (2 * 4 + 0)) F) :=
    Finite.of_injective (fun u : GL (Fin (2 * 4 + 0)) F =>
      (u : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F)) fun _ _ h => Units.ext h
  set α : MulAut B := MulEquiv.ofBijective (MonoidHom.mk' f hfmul)
    ⟨hfinj, Finite.surjective_of_injective hfinj⟩ with hα
  have hαapp : ∀ z : B, φ (α z) = h * φ z * h⁻¹ := fun z => (hf z).symm
  have hRc : 2 ≤ ({k, l} : Finset (Fin 4))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hkl]
  have hfixα : ∀ (y : StatedSp 4 K) (hy : y ∈ spBlock K ({k, l} : Finset (Fin 4))ᶜ), y ∈ S →
      α ⟨ctuEmbed 0 (Nat.zero_le 1) σ ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ =
        ⟨ctuEmbed 0 (Nat.zero_le 1) σ ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ := by
    intro y hy hyS
    apply hφinj
    have hyk : y ∈ spBlock K ({k} : Finset (Fin 4))ᶜ :=
      spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hy
    have hφy : φ ⟨ctuEmbed 0 (Nat.zero_le 1) σ ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ =
        ((e.symm y : L) : G) := P.N1 y hyk
    rw [hαapp, hφy, hfix y hy hyS, mul_inv_cancel_right]
  obtain ⟨ν, hν, b, hb⟩ := exists_ctuaTwist_of_mulAut_fix_long_swap (by rw [hK, pow_one]) hF
    le_rfl (Nat.zero_le 1) hι hRc hSpos hSneg hSswap α hfixα
  refine ⟨b, fun x hx => ?_⟩
  have h1 := hαapp ⟨x, hx⟩
  rw [hφapp, hφapp] at h1
  rw [← h1]
  congr 1
  apply Subtype.ext
  change ((α ⟨x, hx⟩ : B) : SU σ (2 * 4 + 0)) = _
  rw [hb, ctuaTwist_zero_eq_barPow]

end Conj

section Steps

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N ε : ℕ}
  {hε : ε ≤ 1} {F : Type} [Field F] {σ : F ≃+* F} {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}
  {e : L ≃* StatedSp N K}

omit [CharP K 2] in
theorem nsElt_mem_spBlock_singleton (k : Fin N) :
    nsElt (K := K) k ∈ spBlock K ({k} : Finset (Fin N)) := by
  rw [spBlock_singleton]
  exact nsTorusSp_le_longRootSp2 k (nsElt_mem_nsTorusSp k)

theorem NsUniParam.commute_symm_of_commute_ctuEmbed {k : Fin N}
    (P : NsUniParam ε hε σ ι hι e k) {d : SU σ (2 * N + ε)}
    (hd : d ∈ ctuBlock σ ε ({k} : Finset (Fin N))) {y : StatedSp N K}
    (hy : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ)
    (hdy : d * ctuEmbed ε hε σ ι hι y = ctuEmbed ε hε σ ι hι y * d) :
    P.Φ ⟨d, hd⟩ * ((e.symm y : L) : G) = ((e.symm y : L) : G) * P.Φ ⟨d, hd⟩ := by
  rw [← P.N1 y hy, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hdy

omit [CharP K 2] in
theorem mem_normalizer_of_commute_nsElt [Finite G] {k l : Fin N} {D : G}
    (hk : ((e.symm (nsElt k) : L) : G) * D = D * ((e.symm (nsElt k) : L) : G))
    (hl : ((e.symm (nsElt l) : L) : G) * D = D * ((e.symm (nsElt l) : L) : G)) :
    D ∈ normalizer (centralizerPerfectCore
      (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l)) : Set G) := by
  have hle : modelToG e (nsTorusSp K k ⊔ nsTorusSp K l) ≤ centralizer ({D} : Set G) := by
    rw [UnitaryPilot.modelToG_sup]
    refine sup_le ?_ ?_
    · rw [nsTorusSp, UnitaryPilot.modelToG_def, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
        zpowers_le, mem_centralizer_singleton_iff]
      exact hk
    · rw [nsTorusSp, UnitaryPilot.modelToG_def, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
        zpowers_le, mem_centralizer_singleton_iff]
      exact hl
  have hDc : D ∈ centralizer (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l) : Set G) := by
    rw [mem_centralizer_iff]
    intro z hz
    exact mem_centralizer_singleton_iff.1 (hle hz)
  exact F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
    (centralizer_le_normalizer _ hDc)

end Steps

section Key

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c} {e : L ≃* StatedSp 4 K}

omit [Finite G] [Finite K] in
theorem NsUniParam.false_of_conj_bar_of_pow_three (hF : Nat.card F = (2 ^ 1) ^ 2)
    {k l : Fin 4} (hkl : k ≠ l)
    (P : NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k) {D : G}
    (hD3 : D ^ 3 = 1)
    (hb : ∀ (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4))),
      D * P.Φ ⟨x, ctuBlock_pair_le_left _ k l hx⟩ * D⁻¹ =
        P.Φ ⟨barPow (unitaryInvolution_involutive hF) true x, ctuBlock_pair_le_left _ k l
          ((barPow_mem_ctuBlock_iff _ true _ x).2 hx)⟩)
    {g : SU (unitaryInvolution F 2 1) (2 * 4 + 0)}
    (hg : g ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4)))
    (hbar : barPow (unitaryInvolution_involutive hF) true g ≠ g) : False := by
  have hσ : ∀ c, unitaryInvolution F 2 1 (unitaryInvolution F 2 1 c) = c :=
    unitaryInvolution_involutive hF
  have hgb : barPow hσ true g ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4)) :=
    (barPow_mem_ctuBlock_iff hσ true _ g).2 hg
  have e1 := hb g hg
  have e2 : D * P.Φ ⟨barPow hσ true g, ctuBlock_pair_le_left _ k l hgb⟩ * D⁻¹ =
      P.Φ ⟨g, ctuBlock_pair_le_left _ k l hg⟩ := by
    rw [hb _ hgb]
    congr 2
    exact barPow_true_barPow_true hσ g
  obtain ⟨a, ha⟩ : ∃ a : G, a = P.Φ ⟨g, ctuBlock_pair_le_left _ k l hg⟩ := ⟨_, rfl⟩
  rw [← ha] at e1 e2
  have h3 : a = D * (D * a * D⁻¹) * D⁻¹ := by rw [e1, e2]
  have key : D * a * D⁻¹ = a := by
    calc D * a * D⁻¹ = D * (D * (D * a * D⁻¹) * D⁻¹) * D⁻¹ := by rw [← h3]
      _ = D ^ 3 * a * (D ^ 3)⁻¹ := by rw [pow_three]; group
      _ = a := by rw [hD3, one_mul, inv_one, mul_one]
  have h4 : P.Φ ⟨g, ctuBlock_pair_le_left _ k l hg⟩ =
      P.Φ ⟨barPow hσ true g, ctuBlock_pair_le_left _ k l hgb⟩ := by
    rw [← ha, ← e1, key]
  have h5 := P.injOn_ctuBlock hF (by norm_num) hkl (ctuBlock_pair_le_right _ k l hg)
    (ctuBlock_pair_le_right _ k l hgb) h4
  exact hbar (congrArg Subtype.val h5).symm

theorem commute_overlap_of_torus (hK : Nat.card K = 2) (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P : ∀ k : Fin 4, NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k)
    (hagree : NsUniParamAgree P) {k l p p' : Fin 4} (hkl : k ≠ l) (hpp : p ≠ p')
    (hcompl : ({k, l} : Finset (Fin 4))ᶜ = {p, p'})
    (hw : ∀ z ∈ centralizerPerfectCore (modelToG e (nsTorusSp K p ⊔ nsTorusSp K p')),
      ((e.symm (permSp K (Equiv.swap p p')) : L) : G) * z =
        z * ((e.symm (permSp K (Equiv.swap p p')) : L) : G))
    {d : SU (unitaryInvolution F 2 1) (2 * 4 + 0)}
    (hd : d ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({p, p'} : Finset (Fin 4))) (hd3 : d ^ 3 = 1)
    (hdk : d * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt k) =
      ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt k) * d)
    (hdl : d * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt l) =
      ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt l) * d)
    {g : SU (unitaryInvolution F 2 1) (2 * 4 + 0)}
    (hg : g ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4)))
    (hbar : barPow (unitaryInvolution_involutive hF) true g ≠ g)
    (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
    (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4))) :
    (P p).Φ ⟨d, ctuBlock_pair_le_left _ p p' hd⟩ * (P k).Φ ⟨x, ctuBlock_pair_le_left _ k l hx⟩ =
      (P k).Φ ⟨x, ctuBlock_pair_le_left _ k l hx⟩ *
        (P p).Φ ⟨d, ctuBlock_pair_le_left _ p p' hd⟩ := by
  have hdp := ctuBlock_pair_le_left _ p p' hd
  have hdp' := ctuBlock_pair_le_right _ p p' hd
  have hDD : (P p).Φ ⟨d, hdp⟩ = (P p').Φ ⟨d, hdp'⟩ := hagree p p' d hdp hdp'
  have hmem : ∀ q : Fin 4, q ∉ ({k, l} : Finset (Fin 4)) ↔ q = p ∨ q = p' := by
    intro q
    rw [← Finset.mem_compl, hcompl, Finset.mem_insert, Finset.mem_singleton]
  have hkp : k ∉ ({p} : Finset (Fin 4)) := fun h =>
    ((hmem p).2 (Or.inl rfl)) (by rw [← Finset.mem_singleton.1 h]; simp)
  have hlp : l ∉ ({p} : Finset (Fin 4)) := fun h =>
    ((hmem p).2 (Or.inl rfl)) (by rw [← Finset.mem_singleton.1 h]; simp)
  have hDN := mem_normalizer_of_commute_nsElt (e := e)
    ((P p).commute_symm_of_commute_ctuEmbed hdp (nsElt_mem_spBlock_compl_of_not_mem hkp) hdk).symm
    ((P p).commute_symm_of_commute_ctuEmbed hdp (nsElt_mem_spBlock_compl_of_not_mem hlp) hdl).symm
  have hfix : ∀ y ∈ spBlock K ({k, l} : Finset (Fin 4))ᶜ,
      y ∈ {y : StatedSp 4 K | y ∈ spBlock K ({p} : Finset (Fin 4)) ∨
        y ∈ spBlock K ({p'} : Finset (Fin 4)) ∨ y = permSp K (Equiv.swap p p')} →
      (P p).Φ ⟨d, hdp⟩ * ((e.symm y : L) : G) = ((e.symm y : L) : G) * (P p).Φ ⟨d, hdp⟩ := by
    intro y _ hyS
    rcases hyS with hy | hy | hy
    · rw [hDD]
      exact (P p').commute_symm_of_commute_ctuEmbed hdp'
        (spBlock_mono (by simpa using hpp.symm) hy)
        (commute_ctuBlock_ctuEmbed hd (spBlock_mono (by simp) hy))
    · exact (P p).commute_symm_of_commute_ctuEmbed hdp (spBlock_mono (by simpa using hpp) hy)
        (commute_ctuBlock_ctuEmbed hd (spBlock_mono (by simp) hy))
    · rw [hy]
      exact (hw _ ((P p).mem_overlap hF hpp hd)).symm
  obtain ⟨b, hb⟩ := (P k).exists_barPow_of_conj_long_swap hK hF hkl hDN
    (fun q hq c => by
      rcases (hmem q).1 hq with rfl | rfl
      · exact Or.inl (elt_positiveLong_mem_spBlock (Finset.mem_singleton_self _) c)
      · exact Or.inr (Or.inl (elt_positiveLong_mem_spBlock (Finset.mem_singleton_self _) c)))
    (fun q hq c => by
      rcases (hmem q).1 hq with rfl | rfl
      · exact Or.inl (elt_negativeLong_mem_spBlock (Finset.mem_singleton_self _) c)
      · exact Or.inr (Or.inl (elt_negativeLong_mem_spBlock (Finset.mem_singleton_self _) c)))
    (fun q q' hq hq' hqq => by
      rcases (hmem q).1 hq with h1 | h1 <;> rcases (hmem q').1 hq' with h2 | h2
      · exact absurd (h1.trans h2.symm) hqq
      · rw [h1, h2]
        exact Or.inr (Or.inr rfl)
      · rw [h1, h2, Equiv.swap_comm]
        exact Or.inr (Or.inr rfl)
      · exact absurd (h1.trans h2.symm) hqq) hfix
  cases b
  · exact mul_inv_eq_iff_eq_mul.1 (hb x hx)
  · exfalso
    have hD3 : (P p).Φ ⟨d, hdp⟩ ^ 3 = 1 := by
      have h1 : (⟨d, hdp⟩ : ctuBlock (unitaryInvolution F 2 1) 0 ({p} : Finset (Fin 4))) ^ 3 =
          1 := Subtype.ext (by rw [SubgroupClass.coe_pow, hd3, OneMemClass.coe_one])
      rw [← map_pow, h1, map_one]
    exact (P k).false_of_conj_bar_of_pow_three hF hkl hD3 hb hg hbar

end Key

end CFSG.SeitzReduction.SymplecticPilot
