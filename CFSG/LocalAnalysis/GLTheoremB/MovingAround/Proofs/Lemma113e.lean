module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

namespace Lemma113e

@[expose] def InputB_order3 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q),
    ∀ x ∈ Q, x ^ 3 = 1 → x ≠ 1 → x ∈ E ∨ ∃ q ∈ Q, x ∈ GLBConj q A

@[expose] def InputB_fusA : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q) (x : G),
    x⁻¹ * e * x ∈ A → ∃ n ∈ Subgroup.normalizer (A : Set G), n⁻¹ * e * n = x⁻¹ * e * x

@[expose] def InputB_core : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q),
    Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G)

section Helpers

variable {G : Type} [Group G] [Finite G]

private theorem mem_GLBConj_iff' {H : Subgroup G} {g x : G} :
    x ∈ GLBConj g H ↔ g * x * g⁻¹ ∈ H := by
  unfold GLBConj
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e1 : g * ((MulAut.conj g⁻¹).toMonoidHom y) * g⁻¹ = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [e1]
    exact hy
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

private theorem GLBConj_eq_self_of_mem_normalizer {H : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (H : Set G)) : GLBConj x H = H := by
  ext y
  rw [mem_GLBConj_iff']
  exact (Subgroup.mem_normalizer_iff.1 hx y).symm

private theorem centralizer_of_conj_eq {e x n : G} (h : n⁻¹ * e * n = x⁻¹ * e * x) :
    x * n⁻¹ ∈ Subgroup.centralizer ({e} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  have hex : e * x = x * (n⁻¹ * e * n) := by
    rw [h]
    group
  calc e * (x * n⁻¹) = (e * x) * n⁻¹ := by group
    _ = x * (n⁻¹ * e * n) * n⁻¹ := by rw [hex]
    _ = x * n⁻¹ * e := by group

private theorem isPGroup_of_isElemAbelian {p : ℕ} [Fact p.Prime] {F : Subgroup G}
    (hF : IsElemAbelian p F) : IsPGroup p F := by
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : (g : G) ^ p = 1 := hF.2 (g : G) g.2
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hg)
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 (orderOf_dvd_of_pow_eq_one hgp) with h1 | h1
  · exact ⟨0, by simp [h1]⟩
  · exact ⟨1, by simp [h1]⟩

private theorem card_eq_pow_pRank_of_isElemAbelian {p : ℕ} [Fact p.Prime] {F : Subgroup G}
    (hF : IsElemAbelian p F) : Nat.card F = p ^ CFSG.Open.pRank p F := by
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hF).exists_card_eq
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have h1 : n ≤ CFSG.Open.pRank p F := CFSG.SectionRank.le_pRank hp le_rfl hF hn
  have h2 : CFSG.Open.pRank p F ≤ n := by
    apply CFSG.SectionRank.pRank_le hp
    intro E' hE'F _
    rw [← hn]
    exact Subgroup.card_le_of_le hE'F
  rw [hn, le_antisymm h2 h1]

private theorem mem_centralizer_of_mem_centerOf {Q : Subgroup G} {z q : G} (hz : z ∈ centerOf Q)
    (hq : q ∈ Q) : z * q = q * z := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
  have h2 := Subgroup.mem_center_iff.1 hw ⟨q, hq⟩
  have h3 : q * (w : G) = (w : G) * q := congrArg Subtype.val h2
  exact h3.symm

private theorem exists_normalizer_of_conj_mem {e : G} {Q E' : Subgroup G}
    (hQS : IsSylowIn 3 (Subgroup.centralizer ({e} : Set G)) Q) (hE' : IsElemAbelian 3 E')
    (hWC : PieceB_WC E' Q) {x : G} (hx : x⁻¹ * e * x ∈ E') :
    ∃ n ∈ Subgroup.normalizer (E' : Set G), n⁻¹ * e * n = x⁻¹ * e * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSC : E'.map (MulAut.conj x).toMonoidHom ≤ Subgroup.centralizer ({e} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    have hcomm : (x⁻¹ * e * x) * s = s * (x⁻¹ * e * x) :=
      congrArg Subtype.val (hE'.1.is_comm.comm ⟨x⁻¹ * e * x, hx⟩ ⟨s, hs⟩)
    show e * (x * s * x⁻¹) = x * s * x⁻¹ * e
    calc e * (x * s * x⁻¹) = x * ((x⁻¹ * e * x) * s) * x⁻¹ := by group
      _ = x * (s * (x⁻¹ * e * x)) * x⁻¹ := by rw [hcomm]
      _ = x * s * x⁻¹ * e := by group
  have hSp : IsPGroup 3 ↥(E'.map (MulAut.conj x).toMonoidHom) :=
    (isPGroup_of_isElemAbelian hE').map _
  obtain ⟨c, hcC, hc⟩ := Lemma113b.exists_conj_mem_of_isSylowIn hQS hSC hSp
  have hec : e * c = c * e := Subgroup.mem_centralizer_iff.1 hcC e (Set.mem_singleton e)
  have hce : c⁻¹ * e * c = e := by
    calc c⁻¹ * e * c = c⁻¹ * (e * c) := by group
      _ = c⁻¹ * (c * e) := by rw [hec]
      _ = e := by group
  have hsub : GLBConj (c * x)⁻¹ E' ≤ Q := by
    intro y hy
    have hs : (c * x)⁻¹ * y * (c * x)⁻¹⁻¹ ∈ E' := mem_GLBConj_iff'.1 hy
    have hmem : x * ((c * x)⁻¹ * y * (c * x)⁻¹⁻¹) * x⁻¹ ∈ E'.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map.2 ⟨_, hs, rfl⟩
    have h1 := hc _ hmem
    have h2 : c * (x * ((c * x)⁻¹ * y * (c * x)⁻¹⁻¹) * x⁻¹) * c⁻¹ = y := by group
    rw [h2] at h1
    exact h1
  have hWCw := hWC (c * x)⁻¹ hsub
  have hn : c * x ∈ Subgroup.normalizer (E' : Set G) := by
    have h3 := inv_mem (mem_normalizer_of_GLBConj_eq hWCw)
    rw [inv_inv] at h3
    exact h3
  refine ⟨c * x, hn, ?_⟩
  calc (c * x)⁻¹ * e * (c * x) = x⁻¹ * (c⁻¹ * e * c) * x := by group
    _ = x⁻¹ * e * x := by rw [hce]

end Helpers

section Claims

variable {G : Type} [Group G] [Finite G]

theorem pieceB_WC_of {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q) : PieceB_WC E Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEsc : IsSCp 3 M E := h.pair.1.1.1.1
  have hEab : IsElemAbelian 3 E := hEsc.2.1
  have hEQ : E ≤ Q := le_trans le_sup_left h.hQ.2
  have hcardE : Nat.card E = 3 ^ 4 := by
    rw [card_eq_pow_pRank_of_isElemAbelian hEab, h.h4]
  have hJ : E = thompsonJ 3 Q := hA.2.2.2.2.2.1
  have hpQ : CFSG.Open.pRank 3 Q = 4 := by
    apply le_antisymm
    · obtain ⟨F, hFQ, hF, hFc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) Q
      have hIEk : IsEkIn 3 (CFSG.Open.pRank 3 Q) Q F := ⟨hFQ, hF, hFc⟩
      have hFt : F ≤ thompsonJ 3 Q := by
        unfold thompsonJ
        exact le_iSup₂ (f := fun (E' : Subgroup G) (_ : IsEkIn 3 (CFSG.Open.pRank 3 Q) Q E') => E') F hIEk
      rw [← hJ] at hFt
      have hle := Subgroup.card_le_of_le hFt
      rw [hFc, hcardE] at hle
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
    · exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hEQ hEab hcardE
  intro g hg
  have hgE : IsElemAbelian 3 (GLBConj g E) := isElemAbelian_GLBConj g hEab
  have hgcard : Nat.card (GLBConj g E) = 3 ^ 4 := by
    rw [← hcardE]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hIEk : IsEkIn 3 (CFSG.Open.pRank 3 Q) Q (GLBConj g E) := by
    rw [hpQ]
    exact ⟨hg, hgE, hgcard⟩
  have hle : GLBConj g E ≤ thompsonJ 3 Q := by
    unfold thompsonJ
    exact le_iSup₂ (f := fun (E' : Subgroup G) (_ : IsEkIn 3 (CFSG.Open.pRank 3 Q) Q E') => E') (GLBConj g E) hIEk
  rw [← hJ] at hle
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hgcard, hcardE]))

theorem pieceB_SylZ_of {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q) :
    PieceB_SylZ (E ⊓ A) Q := by
  have hle : omegaOne 3 (centerOf Q) ≤ centerOf Q := by
    unfold omegaOne
    exact (Subgroup.closure_le _).2 (fun x hx => (show x ∈ centerOf Q ∧ x ^ 3 = 1 from hx).1)
  have hQC : Q ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ centerOf Q := hle (show z ∈ omegaOne 3 (centerOf Q) by rw [hA.1]; exact hz)
    exact mem_centralizer_of_mem_centerOf hz' hq
  refine ⟨hQC, h.hQ.1.2.1, fun R' hR'C hR'p hQR' => ?_⟩
  have hR'Cg : R' ≤ Subgroup.centralizer ({e} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact Subgroup.mem_centralizer_iff.1 (hR'C hx) e h.he.1
  exact h.hQ.1.2.2 R' hR'Cg hR'p hQR'

theorem pieceB_fus_of (hIa : InputB_order3) (hIb : InputB_fusA) {m : ℕ} {B M E A : Subgroup G}
    {a e : G} {K Q : Subgroup G} (h : Cfg113 G m B M E A a e K Q)
    (hA : Claim113A (M := M) E A e K Q) : PieceB_fus E A e := by
  intro hNE hNA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEsc : IsSCp 3 M E := h.pair.1.1.1.1
  have hEab : IsElemAbelian 3 E := hEsc.2.1
  have heE : e ∈ E := (Subgroup.mem_inf.1 h.he.1).1
  have he1 : e ≠ 1 := h.he.2
  have hQC : Q ≤ Subgroup.centralizer ({e} : Set G) := h.hQ.1.1
  have hWC : PieceB_WC E Q := pieceB_WC_of h hA
  obtain ⟨g, hgQ, hgne⟩ := hA.2.2.2.2.2.2
  have hf_mem : g⁻¹ * e * g ∈ Q := by
    apply hgQ
    rw [mem_GLBConj_iff']
    rw [show g * (g⁻¹ * e * g) * g⁻¹ = e by group]
    exact Subgroup.mem_zpowers e
  have hf3 : (g⁻¹ * e * g) ^ 3 = 1 := by
    have h3 : e ^ 3 = 1 := hEab.2 e heE
    rw [pow_three] at h3 ⊢
    calc g⁻¹ * e * g * (g⁻¹ * e * g * (g⁻¹ * e * g)) = g⁻¹ * (e * (e * e)) * g := by group
      _ = 1 := by rw [h3]; group
  have hf1 : g⁻¹ * e * g ≠ 1 := by
    intro h1
    apply he1
    have h2 : e = g * (g⁻¹ * e * g) * g⁻¹ := by group
    rw [h2, h1]
    group
  rcases hIa h hA (g⁻¹ * e * g) hf_mem hf3 hf1 with hfE | ⟨q, hq, hfq⟩
  · obtain ⟨n, hn, hnf⟩ := exists_normalizer_of_conj_mem h.hQ.1 hEab hWC hfE
    have hnN : n ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := hNE hn
    have hc : g * n⁻¹ ∈ Subgroup.centralizer ({e} : Set G) := centralizer_of_conj_eq hnf
    have hgN : g ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
      have key := mul_mem (Lemma113b.centralizer_le_normalizer_zpowers' e hc) hnN
      rwa [show g * n⁻¹ * n = g by group] at key
    exact hgne (GLBConj_eq_self_of_mem_normalizer hgN)
  · rw [mem_GLBConj_iff'] at hfq
    have hx : (g * q⁻¹)⁻¹ * e * (g * q⁻¹) ∈ A := by
      rw [show (g * q⁻¹)⁻¹ * e * (g * q⁻¹) = q * (g⁻¹ * e * g) * q⁻¹ by group]
      exact hfq
    obtain ⟨n, hn, hnx⟩ := hIb h hA (g * q⁻¹) hx
    have hnN : n ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := hNA hn
    have hc : g * q⁻¹ * n⁻¹ ∈ Subgroup.centralizer ({e} : Set G) := centralizer_of_conj_eq hnx
    have hqN : q ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) :=
      Lemma113b.centralizer_le_normalizer_zpowers' e (hQC hq)
    have hgN : g ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
      have key := mul_mem (mul_mem (Lemma113b.centralizer_le_normalizer_zpowers' e hc) hnN) hqN
      rwa [show g * q⁻¹ * n⁻¹ * n * q = g by group] at key
    exact hgne (GLBConj_eq_self_of_mem_normalizer hgN)

theorem pieceB_core_of (hII : InputB_core) {m : ℕ} {B M E A : Subgroup G} {a e : G}
    {K Q : Subgroup G} (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q) :
    PieceB_core E A e := by
  intro hN0
  have hNA : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    hII h hA hN0
  have hQC : Q ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) := (pieceB_SylZ_of h hA).1
  have hAsc : IsSCp 3 M A := h.pair.1.2.1.1.1
  have hAab : IsElemAbelian 3 A := hAsc.2.1
  refine ⟨Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G), ?_, ?_, ?_⟩
  · intro n hn t ht
    rw [Subgroup.mem_centralizer_iff] at ht ⊢
    intro z hz
    have hz' : n * z * n⁻¹ ∈ E ⊓ A := (Subgroup.mem_normalizer_iff.1 (hNA hn) z).1 hz
    have hc : (n * z * n⁻¹) * t = t * (n * z * n⁻¹) := ht _ hz'
    calc z * (n⁻¹ * t * n) = n⁻¹ * ((n * z * n⁻¹) * t) * n := by group
      _ = n⁻¹ * (t * (n * z * n⁻¹)) * n := by rw [hc]
      _ = n⁻¹ * t * n * z := by group
  · intro t ht z hz
    exact (Subgroup.mem_centralizer_iff.1 ht z hz).symm
  · intro a' ha' hca
    have haQ : a' ∈ Q := (le_sup_right.trans h.hQ.2) ha'
    have hcen : a' ∈ centerOf Q := by
      unfold centerOf
      refine Subgroup.mem_map.2 ⟨⟨a', haQ⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro q
      apply Subtype.ext
      have hq : (q : G) * a' = a' * (q : G) := hca (q : G) (hQC q.2)
      exact hq
    have hm : a' ∈ omegaOne 3 (centerOf Q) := by
      unfold omegaOne
      exact Subgroup.subset_closure ⟨hcen, hAab.2 a' ha'⟩
    rw [hA.1] at hm
    exact hm

end Claims

theorem pieceB_claims_of_inputs (hIa : InputB_order3) (hIb : InputB_fusA) (hII : InputB_core) :
    Lemma113_ii_pieceB_Claims := by
  intro G _ _ m B M E A a e K Q h hA
  exact ⟨pieceB_WC_of h hA, pieceB_SylZ_of h hA, pieceB_fus_of hIa hIb h hA,
    pieceB_core_of hII h hA⟩

theorem pieceB_statement_of_inputs (hIa : InputB_order3) (hIb : InputB_fusA) (hII : InputB_core) :
    Lemma113_ii_pieceBStatement :=
  lemma113_ii_pieceB_of (pieceB_claims_of_inputs hIa hIb hII)

end Lemma113e

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
