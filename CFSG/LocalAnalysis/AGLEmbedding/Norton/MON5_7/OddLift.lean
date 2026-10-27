module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt

public section

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Open CFSG.RankThree.Classical2 CFSG.RankThree.CentralCover CFSG.AGLEmbedding

@[expose] def LiftableNormalizerGenP (p : ℕ) (L : Type*) [Group L] : Prop :=
  ∃ (E : Subgroup L) (S : Set (Subgroup L)), (∀ x ∈ E, x ^ p = 1) ∧ p ^ 3 ≤ Nat.card E ∧
    S.Nonempty ∧ (∀ F ∈ S, F ≤ E ∧ p ^ 2 ≤ Nat.card F) ∧ LiftsComm E ∧
    ⊤ ≤ ⨆ F ∈ S, Subgroup.normalizer (F : Set L)

theorem liftsComm_of_invertersP {L : Type*} [Group L] {ι : Type} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h w : ι → L) (hcomm : ∀ i j, Commute (h i) (h j))
    (hord : ∀ i, orderOf (h i) = p) (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) :
    IsElemAbelian p (Subgroup.closure (Set.range h)) ∧
      Nat.card (Subgroup.closure (Set.range h)) = p ^ Fintype.card ι ∧
      LiftsComm (Subgroup.closure (Set.range h)) := by
  have hid := inversion_basis_package (φ := MonoidHom.id L) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le) hp hp2 h w hcomm hord hinv hfix
  exact ⟨hid.1, hid.2.1, fun Y _ _ φ hφ hker =>
    (inversion_basis_package hφ hker hp hp2 h w hcomm hord hinv hfix).2.2⟩

theorem weakCore_top_of_coverP {K L : Type} [Group K] [Finite K] [Group L] (π : K →* L)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup L} {S : Set (Subgroup L)} (hE3 : ∀ x ∈ E, x ^ p = 1)
    (hE : p ^ 3 ≤ Nat.card E) (hSne : S.Nonempty) (hS : ∀ F ∈ S, F ≤ E ∧ p ^ 2 ≤ Nat.card F)
    (hcomm : ∀ x ∈ E.comap π, ∀ y ∈ E.comap π, x * y = y * x)
    (hgen : ⊤ ≤ ⨆ F ∈ S, Subgroup.normalizer (F : Set L)) {T : Subgroup K}
    (hT : E.comap π ≤ T) : GLBWeakCore p T = ⊤ := by
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨V, hVE, hVab, hVcard, -⟩ := exists_elemAbelian_le_centralizer (φ := π) hπ hker
    hp hp2 hE3 hcomm hE (u := 1) (by simp)
    (fun x _ => by rw [map_one]; exact Commute.one_left _)
  have hN : ∀ F ∈ S, Subgroup.normalizer ((F.comap π : Subgroup K) : Set K) ≤
      GLBWeakCore p T := by
    intro F hF
    have hFE : F.comap π ≤ E.comap π := Subgroup.comap_mono (hS F hF).1
    refine le_sSup ⟨F.comap π, hFE.trans hT, ?_, ?_, rfl⟩
    · obtain ⟨W, hW, hWab, hWcard, -⟩ := exists_elemAbelian_le_centralizer (φ := π) hπ hker
        hp hp2 (fun x hx => hE3 x ((hS F hF).1 hx))
        (fun x hx y hy => hcomm x (hFE hx) y (hFE hy)) (hS F hF).2 (u := 1) (by simp)
        (fun x _ => by rw [map_one]; exact Commute.one_left _)
      exact SectionRank.le_pRank hp1 hW hWab hWcard
    · refine SectionRank.le_pRank hp1 (E := V) ?_ hVab hVcard
      refine le_sup_of_le_right (le_inf (hVE.trans hT) ?_)
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact hcomm q (hFE hq) v (hVE hv)
  set M : Subgroup K := ⨆ F ∈ S, Subgroup.normalizer ((F.comap π : Subgroup K) : Set K) with hM
  have hMle : M ≤ GLBWeakCore p T := iSup₂_le fun F hF => hN F hF
  have himg : M.map π = ⊤ := by
    rw [eq_top_iff]
    refine hgen.trans (iSup₂_le fun F hF l hl => ?_)
    obtain ⟨x, rfl⟩ := hπ l
    refine Subgroup.mem_map.2 ⟨x, ?_, rfl⟩
    have hrange : F ≤ π.range := by
      rw [MonoidHom.range_eq_top.2 hπ]
      exact le_top
    have hx : x ∈ Subgroup.normalizer ((F.comap π : Subgroup K) : Set K) := by
      rw [← Subgroup.comap_normalizer_eq_of_le_range hrange]
      exact hl
    exact (le_iSup₂ (f := fun F (_ : F ∈ S) =>
      Subgroup.normalizer ((F.comap π : Subgroup K) : Set K)) F hF) hx
  obtain ⟨F₀, hF₀⟩ := hSne
  have hkerM : π.ker ≤ M := fun z hz =>
    (le_iSup₂ (f := fun F (_ : F ∈ S) => Subgroup.normalizer ((F.comap π : Subgroup K) : Set K))
      F₀ hF₀) (Subgroup.center_le_normalizer _ (hker hz))
  refine eq_top_iff.2 fun x _ => hMle ?_
  have hmem : π x ∈ M.map π := by
    rw [himg]
    exact Subgroup.mem_top _
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 hmem
  have hker' : m⁻¹ * x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
  have : x = m * (m⁻¹ * x) := by group
  rw [this]
  exact M.mul_mem hm (hkerM hker')

theorem weakCore_eq_top_of_normalizerGenP {K L : Type} [Group K] [Finite K] [Group L]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hL : LiftableNormalizerGenP p L)
    (e : K ⧸ Subgroup.center K ≃* L)
    (hZ : IsPGroup p (Subgroup.center K)) (T : Sylow p K) :
    GLBWeakCore p (T : Subgroup K) = ⊤ := by
  obtain ⟨E, S, hE3, hE, hSne, hS, hlift, hgen⟩ := hL
  set π : K →* L := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hπdef
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      ← map_one e, e.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE3 g g.2)⟩
  have hP : IsPGroup p (E.comap π) := hEp.comap_of_ker_isPGroup π (hker ▸ hZ)
  obtain ⟨T₀, hT₀⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T₀ T
  have hTmap : (T : Subgroup K) = (T₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  set π' : K →* L := π.comp (MulAut.conj g⁻¹).toMonoidHom with hπ'def
  have hπ' : Function.Surjective π' := hπ.comp (MulAut.conj g⁻¹).surjective
  have hπ'x : ∀ x, π' x = π (g⁻¹ * x * g) := fun x => by
    simp [hπ'def]
  have hker' : π'.ker ≤ Subgroup.center K := by
    intro x hx
    have h1 : g⁻¹ * x * g ∈ Subgroup.center K := by
      rw [← hker, MonoidHom.mem_ker, ← hπ'x]
      exact hx
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [← h2]
    exact (inferInstance : (Subgroup.center K).Normal).conj_mem _ h1 g
  refine weakCore_top_of_coverP π' hπ' hker' (Fact.out : p.Prime) hp2 hE3 hE hSne hS
    (hlift K π' hπ' hker') hgen ?_
  intro x hx
  have hx' : g⁻¹ * x * g ∈ E.comap π := by
    rw [Subgroup.mem_comap, ← hπ'x]
    exact hx
  rw [hTmap]
  exact ⟨g⁻¹ * x * g, hT₀ hx', by simp [mul_assoc]⟩

theorem coverWeakGen_of_liftableP {X : Type} [Group X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : LiftableNormalizerGenP p X) : CoverWeakGen X p := by
  intro K _ _ π hπ hker _ _ hZ _ T
  have e : K ⧸ Subgroup.center K ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  exact weakCore_eq_top_of_normalizerGenP hp2 h e hZ T

theorem coverWeakGen_of_liftableNormalizerGen {X : Type} [Group X] (h : LiftableNormalizerGen X) :
    @CoverWeakGen X _ 3 ⟨Nat.prime_three⟩ := by
  intro K _ _ π hπ hker _ _ hZ _ T
  have e : K ⧸ Subgroup.center K ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  exact weakCore_eq_top_of_normalizerGen h e hZ T

end CFSG.AGLEmbedding.Norton.MON5_7
