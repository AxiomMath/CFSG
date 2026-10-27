module

public import CFSG.HardMathSupport.Solomon.Coordinator.Defs
public import CFSG.HardMathSupport.Timmesfeld.Proving.ElemAbelianSubgroup
public import CFSG.Open.SignalizerFunctorTheoremMilestoneDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

@[expose] def SignalizerFunctorTheoremK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ k : ℕ, 1 ≤ k →
    ∀ A : Subgroup G, IsElemAbelian p A → p ^ (k + 2) ≤ Nat.card A →
    ∀ Θ : Subgroup G → Subgroup G,
      (∀ S ∈ signalizerFunctorEk p k A, Θ S ≤ Subgroup.centralizer (S : Set G)) →
      (∀ S ∈ signalizerFunctorEk p k A, Nat.Coprime p (Nat.card (Θ S))) →
      (∀ S ∈ signalizerFunctorEk p k A, A ≤ Subgroup.normalizer (Θ S : Set G)) →
      (∀ S ∈ signalizerFunctorEk p k A, ∀ S' ∈ signalizerFunctorEk p k A,
        Θ S ⊓ Subgroup.centralizer (S' : Set G) ≤ Θ S') →
      (∀ S ∈ signalizerFunctorEk p k A, CFSG.SectionRank.IsKGroupCat ↥(Θ S)) →
      let W : Subgroup G := ⨆ (S : Subgroup G) (_ : S ∈ signalizerFunctorEk p k A), Θ S
      (Nat.Coprime p (Nat.card W) ∧ A ≤ Subgroup.normalizer (W : Set G)) ∧
      (∀ S ∈ signalizerFunctorEk p k A, W ⊓ Subgroup.centralizer (S : Set G) = Θ S) ∧
      (∀ Y : Subgroup G, A ≤ Subgroup.normalizer (Y : Set G) →
        (∀ S ∈ signalizerFunctorEk p k A, Y ⊓ Subgroup.centralizer (S : Set G) ≤ Θ S) →
        Y ≤ W) ∧
      ((∀ S ∈ signalizerFunctorEk p k A, Group.IsSolvable (Θ S)) → Group.IsSolvable W)

variable {G : Type*} [Group G]

theorem glaDelta_le_glaPPrimeCoreOf {p : ℕ} {D : Subgroup G} {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    GLADelta p D ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G)) :=
  iInf_le_of_le d (iInf_le_of_le hd (iInf_le _ hd1))

theorem glaDelta_le_centralizer (p : ℕ) (D : Subgroup G) :
    GLADelta p D ≤ Subgroup.centralizer (D : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  by_cases hd1 : d = 1
  · rw [hd1, one_mul, mul_one]
  · have hxC : x ∈ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.map_subtype_le _ (glaDelta_le_glaPPrimeCoreOf hd hd1 hx)
    exact (Subgroup.mem_centralizer_singleton_iff.1 hxC).symm

theorem not_dvd_card_glaDelta [Finite G] {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hD : D ≠ ⊥) :
    ¬ p ∣ Nat.card (GLADelta p D) := by
  obtain ⟨⟨d, hd⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD
  have hd1' : d ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  intro h
  exact not_dvd_card_glaPPrimeCoreOf hp _
    (h.trans (Subgroup.card_dvd_of_le (glaDelta_le_glaPPrimeCoreOf hd hd1')))

theorem centralizer_le_normalizer_glaDelta (p : ℕ) (D : Subgroup G) :
    Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (GLADelta p D : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [GLADelta, Subgroup.mem_iInf]
  refine forall_congr' fun d => forall_congr' fun hd => forall_congr' fun _ => ?_
  have hgd : g ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hg) d hd).symm
  exact Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p _ hgd) x

theorem le_normalizer_glaDelta {p : ℕ} {A D : Subgroup G} (hA : IsElemAbelian p A) (hDA : D ≤ A) :
    A ≤ Subgroup.normalizer (GLADelta p D : Set G) := by
  refine le_trans ?_ (centralizer_le_normalizer_glaDelta p D)
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact elemAbelian_comm hA (hDA hd) ha

theorem glaDelta_inf_centralizer_le {p k : ℕ} {A D D' : Subgroup G} (hbal : IsBalancedWrt p k A)
    (hD : IsEkIn p k A D) (hD' : IsEkIn p k A D') :
    GLADelta p D ⊓ Subgroup.centralizer (D' : Set G) ≤ GLADelta p D' := by
  rintro y ⟨hyΔ, hyC⟩
  simp only [GLADelta, Subgroup.mem_iInf]
  intro x hx hx1
  have hyx : y ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hyC) x hx).symm
  exact hbal D hD x (hD'.1 hx) hx1 ⟨hyΔ, hyx⟩

theorem isEkIn_iff_mem_signalizerFunctorEk {p k : ℕ} {A D : Subgroup G}
    (hA : IsElemAbelian p A) : IsEkIn p k A D ↔ D ∈ signalizerFunctorEk p k A :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, isElemAbelian_mono hA h.1, h.2⟩⟩

theorem IsEkIn.ne_bot {p k : ℕ} {A D : Subgroup G} (hp : p.Prime) (hk : 1 ≤ k)
    (hD : IsEkIn p k A D) : D ≠ ⊥ := by
  intro h
  have h1 := hD.2.2
  rw [h, Subgroup.card_bot] at h1
  exact absurd h1.symm (Nat.ne_of_gt (Nat.one_lt_pow (by omega) hp.one_lt))

theorem le_iSup_inf_centralizer_isEkIn [Finite G] {p k n : ℕ} (hp : p.Prime) {E Y : Subgroup G}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ n) (hkn : k < n)
    (hEY : E ≤ Subgroup.normalizer (Y : Set G)) (hY : ¬ p ∣ Nat.card Y) :
    Y ≤ ⨆ (F : Subgroup G) (_ : IsEkIn p k E F), Y ⊓ Subgroup.centralizer (F : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  refine (le_iSup_inf_centralizer_hyperplane hE hEY hY).trans (iSup₂_le fun K hK => ?_)
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hKcard : Nat.card K = p ^ n' := card_eq_of_index_eq hp hK.1 hK.2 hcard
  obtain ⟨F, hFK, hFel, hFcard⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.exists_elemAbelian_subgroup_card_pow hp
      (isElemAbelian_mono hE hK.1) (by omega : k ≤ n') hKcard
  refine le_iSup_of_le F (le_iSup_of_le ⟨hFK.trans hK.1, hFel, hFcard⟩ ?_)
  exact inf_le_inf_left Y (Subgroup.centralizer_le hFK)

theorem thetaClosure_eq_iSup_signalizerFunctorEk {p k : ℕ} {A : Subgroup G}
    (hA : IsElemAbelian p A) :
    thetaClosure p k A = ⨆ (S : Subgroup G) (_ : S ∈ signalizerFunctorEk p k A), GLADelta p S :=
  iSup_congr fun _ => iSup_congr_Prop (isEkIn_iff_mem_signalizerFunctorEk hA) fun _ => rfl

theorem thetaClosure_complete (hSF : SignalizerFunctorTheoremK) {G : Type} [Group G] [Finite G]
    {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {A : Subgroup G} (hA : IsElemAbelian p A)
    (hrank : p ^ (k + 2) ≤ Nat.card A) (hbal : IsBalancedWrt p k A)
    (hK : ∀ D : Subgroup G, IsEkIn p k A D → CFSG.SectionRank.IsKGroupCat ↥(GLADelta p D)) :
    (Nat.Coprime p (Nat.card (thetaClosure p k A)) ∧
        A ≤ Subgroup.normalizer (thetaClosure p k A : Set G)) ∧
      ∀ D : Subgroup G, IsEkIn p k A D →
        thetaClosure p k A ⊓ Subgroup.centralizer (D : Set G) = GLADelta p D := by
  have hE : ∀ S ∈ signalizerFunctorEk p k A, IsEkIn p k A S := fun S hS =>
    (isEkIn_iff_mem_signalizerFunctorEk hA).2 hS
  obtain ⟨⟨hcop, hnorm⟩, hcent, -, -⟩ := hSF G p hp k hk A hA hrank (GLADelta p)
    (fun S _ => glaDelta_le_centralizer p S)
    (fun S hS => (Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_card_glaDelta hp ((hE S hS).ne_bot hp hk)))
    (fun S hS => le_normalizer_glaDelta hA (hS.1))
    (fun S hS S' hS' => glaDelta_inf_centralizer_le hbal (hE S hS) (hE S' hS'))
    (fun S hS => hK S (hE S hS))
  rw [thetaClosure_eq_iSup_signalizerFunctorEk hA]
  exact ⟨⟨hcop, hnorm⟩, fun D hD => hcent D ((isEkIn_iff_mem_signalizerFunctorEk hA).1 hD)⟩

theorem thetaClosure_eq_of_le [Finite G] {p k n : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {A E : Subgroup G}
    (hA : IsElemAbelian p A) (hbal : IsBalancedWrt p k A) (hEA : E ≤ A)
    (hEcard : Nat.card E = p ^ n) (hkn : k < n) :
    thetaClosure p k E = thetaClosure p k A := by
  have hEel : IsElemAbelian p E := isElemAbelian_mono hA hEA
  refine le_antisymm (iSup₂_le fun F hF => le_iSup₂_of_le F ⟨hF.1.trans hEA, hF.2⟩ le_rfl)
    (iSup₂_le fun D hD => ?_)
  have hgen := le_iSup_inf_centralizer_isEkIn (k := k) hp hEel hEcard hkn
    ((hEA.trans (le_normalizer_glaDelta hA hD.1))) (not_dvd_card_glaDelta hp (hD.ne_bot hp hk))
  refine hgen.trans (iSup₂_le fun F hF => ?_)
  exact (glaDelta_inf_centralizer_le hbal hD ⟨hF.1.trans hEA, hF.2⟩).trans
    (le_iSup₂_of_le F hF le_rfl)

theorem glaDelta_gLBConj (p : ℕ) (g : G) (D : Subgroup G) :
    GLADelta p (GLBConj g D) = GLBConj g (GLADelta p D) := by
  ext y
  rw [mem_gLBConj]
  simp only [GLADelta, Subgroup.mem_iInf]
  constructor
  · intro h d hd hd1
    have hd' : g⁻¹ * d * g ∈ GLBConj g D := by
      rw [mem_gLBConj]
      have e : g * (g⁻¹ * d * g) * g⁻¹ = d := by group
      rw [e]
      exact hd
    have hd1' : g⁻¹ * d * g ≠ 1 := by
      intro h1
      apply hd1
      calc d = g * (g⁻¹ * d * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hy := h _ hd' hd1'
    rw [centralizer_singleton_gLBConj, glaPPrimeCoreOf_gLBConj, mem_gLBConj] at hy
    exact hy
  · intro h d hd hd1
    rw [mem_gLBConj] at hd
    have hd1' : g * d * g⁻¹ ≠ 1 := by
      intro h1
      apply hd1
      calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have key := h _ hd hd1'
    rw [← mem_gLBConj, ← glaPPrimeCoreOf_gLBConj, ← centralizer_singleton_gLBConj] at key
    have e : g⁻¹ * (g * d * g⁻¹) * g = d := by group
    rw [e] at key
    exact key

theorem isEkIn_gLBConj_iff {p k : ℕ} (g : G) {E D : Subgroup G} :
    IsEkIn p k (GLBConj g E) (GLBConj g D) ↔ IsEkIn p k E D := by
  have hcard : Nat.card (GLBConj g D) = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hel : IsElemAbelian p (GLBConj g D) ↔ IsElemAbelian p D := by
    constructor
    · intro h
      have h' := CFSG.SectionRank.isElemAbelian_map h (MulAut.conj g).toMonoidHom
      rwa [GLBConj, Subgroup.map_map, show (MulAut.conj g).toMonoidHom.comp
        (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G by
          ext x
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            MonoidHom.id_apply]
          group, Subgroup.map_id] at h'
    · intro h
      exact CFSG.SectionRank.isElemAbelian_map h _
  refine ⟨fun h => ⟨?_, hel.1 h.2.1, hcard ▸ h.2.2⟩,
    fun h => ⟨gLBConj_mono g h.1, hel.2 h.2.1, hcard.symm ▸ h.2.2⟩⟩
  have := gLBConj_mono g⁻¹ h.1
  rwa [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at this

theorem thetaClosure_gLBConj (p k : ℕ) (g : G) (E : Subgroup G) :
    thetaClosure p k (GLBConj g E) = GLBConj g (thetaClosure p k E) := by
  apply le_antisymm
  · refine iSup₂_le fun F hF => ?_
    have hF' : IsEkIn p k E (GLBConj g⁻¹ F) := by
      rw [← isEkIn_gLBConj_iff g, gLBConj_gLBConj_inv]
      exact hF
    calc GLADelta p F = GLADelta p (GLBConj g (GLBConj g⁻¹ F)) := by rw [gLBConj_gLBConj_inv]
      _ = GLBConj g (GLADelta p (GLBConj g⁻¹ F)) := glaDelta_gLBConj p g _
      _ ≤ GLBConj g (thetaClosure p k E) := gLBConj_mono g (le_iSup₂_of_le _ hF' le_rfl)
  · refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun D hD => ?_)
    refine Subgroup.map_le_iff_le_comap.1 ?_
    change GLBConj g (GLADelta p D) ≤ _
    rw [← glaDelta_gLBConj]
    exact le_iSup₂_of_le (GLBConj g D) ((isEkIn_gLBConj_iff g).2 hD) le_rfl

theorem normalizer_le_normalizer_thetaClosure (p k : ℕ) (E : Subgroup G) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (thetaClosure p k E : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq] at hg ⊢
  rw [← thetaClosure_gLBConj, hg]

theorem glbCore_le_normalizer_thetaClosure [Finite G] {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    {A : Subgroup G} (hA : IsElemAbelian p A) (hbal : IsBalancedWrt p k A) :
    GLBCore p (k + 1) A ≤ Subgroup.normalizer (thetaClosure p k A : Set G) := by
  refine sSup_le ?_
  rintro N ⟨Q, hQA, hQrank, rfl⟩
  have hQel : IsElemAbelian p Q := isElemAbelian_mono hA hQA
  have : Fact p.Prime := ⟨hp⟩
  have hQp : IsPGroup p Q := fun x => ⟨1, Subtype.ext (by simpa using hQel.2 x x.2)⟩
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  obtain ⟨E, hEQ, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := p) hp.one_lt Q
  have hle : p ^ CFSG.Open.pRank p Q ≤ p ^ n := by
    rw [← hEcard, ← hn]
    exact Subgroup.card_le_of_le hEQ
  have hkn : k < n := by
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
    omega
  rw [← thetaClosure_eq_of_le hp hk hA hbal hQA hn hkn]
  exact normalizer_le_normalizer_thetaClosure p k Q

end CFSG.HardMathSupport.Solomon.Coordinator
