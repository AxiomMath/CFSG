module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteenNarrow
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Extra
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open

section Transport

variable {p : ℕ}

theorem narrowGamma_mono {K : Type*} [Group K] [Finite K] (hp : p.Prime) {T T' : Subgroup K}
    (h : T ≤ T') : narrowGamma p T ≤ narrowGamma p T' := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine sup_le (iSup₂_le fun A ⟨hAT, hA, hAc⟩ => normalizer_le_narrowGamma (hAT.trans h) hA hAc)
    (iSup₂_le fun x ⟨hxT, hxo, h2⟩ => ?_)
  obtain ⟨E, hET, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h2
  exact centralizer_le_narrowGamma (h hxT) hxo
    (CFSG.SectionRank.le_pRank hp.one_lt (hET.trans (inf_le_inf_right _ h)) hE hEc)

theorem narrowGamma_map_le {K L : Type*} [Group K] [Finite K] [Group L] [Finite L]
    (hp : p.Prime) (e : K ≃* L) (T : Subgroup K) :
    (narrowGamma p T).map e.toMonoidHom ≤ narrowGamma p (T.map e.toMonoidHom) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (iSup₂_le fun A ⟨hAT, hA, hAc⟩ => ?_) (iSup₂_le fun x ⟨hxT, hxo, h2⟩ => ?_)
  · rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_equiv_normalizer_eq]
    exact normalizer_le_narrowGamma (Subgroup.map_mono hAT) (isElemAbelian_map _ hA)
      (by rw [Subgroup.card_map_of_injective e.injective, hAc])
  · rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨E, hET, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h2
    have hcent : ∀ k : K, k ∈ Subgroup.centralizer ({x} : Set K) →
        e k ∈ Subgroup.centralizer ({e x} : Set L) := fun k hk => by
      rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
      rw [← map_mul, ← map_mul, hk]
    refine le_trans ?_ (centralizer_le_narrowGamma (x := e x) ⟨x, hxT, rfl⟩
      (by rw [MulEquiv.orderOf_eq, hxo]) ?_)
    · rintro _ ⟨k, hk, rfl⟩
      exact hcent k hk
    · refine CFSG.SectionRank.le_pRank hp.one_lt (E := E.map e.toMonoidHom) ?_
        (isElemAbelian_map _ hE) (by rw [Subgroup.card_map_of_injective e.injective, hEc])
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨⟨k, (hET hk).1, rfl⟩, hcent k (hET hk).2⟩

theorem narrowGamma_eq_top_of_mulEquiv {K L : Type*} [Group K] [Finite K] [Group L] [Finite L]
    (hp : p.Prime) (e : K ≃* L) {T : Subgroup K} (h : narrowGamma p T = ⊤) :
    narrowGamma p (T.map e.toMonoidHom) = ⊤ := by
  refine eq_top_iff.2 fun l _ => narrowGamma_map_le hp e T ?_
  rw [h]
  exact ⟨e.symm l, Subgroup.mem_top _, by simp⟩

theorem narrowGamma_eq_top_of_sylow {X K : Type} [Group X] [Finite X] [Group K] [Finite K]
    (hp : p.Prime) (e : X ≃* K) (Q : Sylow p X) (h : narrowGamma p (Q : Subgroup X) = ⊤)
    (T : Sylow p K) : narrowGamma p (T : Subgroup K) = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e.symm Q.isPGroup' Q.not_dvd_index T
  rw [hΦ]
  exact narrowGamma_eq_top_of_mulEquiv hp Φ h

theorem narrowGamma_eq_top_of_le_sylow {X K : Type} [Group X] [Finite X] [Group K] [Finite K]
    (hp : p.Prime) (e : X ≃* K) {Q : Subgroup X} (hQ : IsPGroup p Q)
    (h : narrowGamma p Q = ⊤) (T : Sylow p K) : narrowGamma p (T : Subgroup K) = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q₀, hQQ₀⟩ := hQ.exists_le_sylow
  refine narrowGamma_eq_top_of_sylow hp e Q₀ (eq_top_iff.2 ?_) T
  rw [← h]
  exact narrowGamma_mono hp hQQ₀

end Transport

theorem narrowGamma_eq_top_of_closure_centralizer {p : ℕ} {K : Type*} [Group K] [Finite K]
    (hp : p.Prime) {T A : Subgroup K} (hAT : A ≤ T) (hA : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2)
    (h : Subgroup.closure {k : K | ∃ a ∈ A, a ≠ 1 ∧ k * a = a * k} = ⊤) :
    narrowGamma p T = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [eq_top_iff, ← h, Subgroup.closure_le]
  rintro k ⟨a, haA, ha1, hak⟩
  refine centralizer_le_narrowGamma (hAT haA) (orderOf_eq_prime (hA.2 a haA) ha1) ?_
    (Subgroup.mem_centralizer_singleton_iff.2 hak)
  refine CFSG.SectionRank.le_pRank hp.one_lt (le_inf hAT fun b hb => ?_) hA hAc
  exact Subgroup.mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (hA.1.is_comm.comm ⟨b, hb⟩ ⟨a, haA⟩))

theorem mem_normalizer_of_forall_conj_mem {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    {g : X} (h : ∀ s ∈ E, g * s * g⁻¹ ∈ E) : g ∈ Subgroup.normalizer (E : Set X) := by
  have hmap : E.map (MulAut.conj g).toMonoidHom = E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact h s hs
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨h s, fun hs => ?_⟩
  rw [← hmap] at hs
  obtain ⟨t, ht, hts⟩ := hs
  have hts' : t = s := by
    simpa [MulAut.conj_apply] using hts
  rw [← hts']
  exact ht

theorem narrowGamma_eq_top_of_sevenModel {p : ℕ} {X : Type*} [Group X] [Finite X]
    [hp : Fact p.Prime] {Q : Subgroup X} {z : X} {gens : Set X}
    (D : CFSG.HardMathSupport.Dickson.I271.SevenModel X p Q z gens) {E : Subgroup X}
    (hEQ : E ≤ Q) (hE : IsElemAbelian p E) (hE2 : Nat.card E = p ^ 2) :
    narrowGamma p Q = ⊤ := by
  have hp' : p.Prime := hp.out
  rw [eq_top_iff, ← D.gens_top, Subgroup.closure_le]
  intro g hg
  rcases D.gens_good g hg with hgz | ⟨w, F, hwF, hwQ, hwz, hgw⟩ | ⟨E', hE'Q, hE', hE'2, hgE'⟩
  · exact centralizer_le_narrowGamma D.line.mem D.line.orderOf_w
      (CFSG.SectionRank.le_pRank hp'.one_lt (le_inf hEQ (hEQ.trans D.line.le_cent)) hE hE2) hgz
  · have hzw : Commute z w := (Subgroup.mem_centralizer_singleton_iff.1 (D.line.le_cent hwQ)).symm
    have hpl := CFSG.HardMathSupport.Dickson.I271.card_closure_pair_sq hzw D.line.pow_eq
      hwF.pow_eq D.line.ne_one hwz
    have hplE : IsElemAbelian p (Subgroup.closure ({z, w} : Set X)) :=
      IsElemAbelian.closure_of_commute
        (by rintro a (rfl | rfl) b (rfl | rfl); exacts [rfl, hzw, hzw.symm, rfl])
        (by rintro a (rfl | rfl); exacts [D.line.pow_eq, hwF.pow_eq])
    refine centralizer_le_narrowGamma hwQ hwF.orderOf_w ?_ hgw
    refine CFSG.SectionRank.le_pRank hp'.one_lt (le_inf ?_ ?_) hplE hpl
    · rw [Subgroup.closure_le]
      rintro a (rfl | rfl)
      exacts [D.line.mem, hwQ]
    · rw [Subgroup.closure_le]
      rintro a (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 hzw.eq
      · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  · exact normalizer_le_narrowGamma hE'Q hE' hE'2 (mem_normalizer_of_forall_conj_mem hgE')

theorem narrowGamma_eq_top_of_seitz (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) {p : ℕ}
    {d : TauCeti.ValidLieTypeIndex} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ≠ d.1.characteristic)
    (hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1) {K : Type} [Group K] [Finite K]
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hZ : Subgroup.center K = ⊥) {T A : Subgroup K}
    (hAT : A ≤ T) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) : narrowGamma p T = ⊤ := by
  set L := (TauCeti.CFSGIndex.lie d).Group
  haveI : Finite L := Finite.of_equiv K e.toEquiv
  set A' : Subgroup L := A.map e.toMonoidHom with hA'
  have hA'el : IsElemAbelian p A' := isElemAbelian_map _ hA
  have hA'c : Nat.card A' = p ^ 2 := by rw [hA', Subgroup.card_map_of_injective e.injective, hAc]
  have hZL : ∀ l : L, MulAut.conj l = 1 → l = 1 := by
    intro l hl
    have hc : e.symm l ∈ Subgroup.center K := Subgroup.mem_center_iff.2 fun k => by
      apply e.injective
      have := congrArg (fun σ : MulAut L => σ (e k)) hl
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      calc e k * l = l * e k * l⁻¹ * l := by rw [this]
        _ = l * e k := by group
    rw [hZ, Subgroup.mem_bot] at hc
    simpa using congrArg e hc
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    exact Subgroup.mem_bot.2 (hZL l (MonoidHom.mem_ker.1 hl))
  have hgen := hS d p hp hp2 hpd hexc (A'.map (MulAut.conj : L →* MulAut L))
    (isElemAbelian_map _ hA'el) (by rw [Subgroup.card_map_of_injective hinj, hA'c])
  have hK : Subgroup.closure {k : K | ∃ a ∈ A, a ≠ 1 ∧ k * a = a * k} = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : e k ∈ Subgroup.closure
        {l : L | ∃ σ ∈ A'.map (MulAut.conj : L →* MulAut L), σ ≠ 1 ∧ σ l = l} := by
      rw [hgen]
      exact Subgroup.mem_top _
    have hmap : (Subgroup.closure
        {l : L | ∃ σ ∈ A'.map (MulAut.conj : L →* MulAut L), σ ≠ 1 ∧ σ l = l}).map
          e.symm.toMonoidHom ≤ Subgroup.closure {k : K | ∃ a ∈ A, a ≠ 1 ∧ k * a = a * k} := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨l, ⟨σ, ⟨_, ⟨a, haA, rfl⟩, rfl⟩, hσ1, hσl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨a, haA, fun ha1 => hσ1 ?_, ?_⟩
      · rw [ha1]
        simp
      · apply e.injective
        simp only [MulAut.conj_apply, MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom] at hσl
        change e (e.symm l * a) = e (a * e.symm l)
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        change e a * l * (e a)⁻¹ = l at hσl
        calc l * e a = e a * l * (e a)⁻¹ * e a := by rw [hσl]
          _ = e a * l := by group
    exact hmap ⟨e k, hk, by simp⟩
  exact narrowGamma_eq_top_of_closure_centralizer hp hAT hA hAc hK

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
