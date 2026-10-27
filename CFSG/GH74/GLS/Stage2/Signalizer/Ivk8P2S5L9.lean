module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5XdJoin
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Cmm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4aStmt
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt18

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

section Nine

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElementaryAbelian_of_le {p : ℕ} {D E : Subgroup G} (hDE : D ≤ E)
    (hE : IsElementaryAbelian p ↥E) : IsElementaryAbelian p ↥D :=
  CFSG.IsElementaryAbelian.of_le hE hDE

theorem Fpi_le_XDR (hB12 : Bender12) (h184 : Lemma18_4ac) (h171 : Prop17_1) (h1123 : IG_11_23)
    {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
    {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t) (hF : S5Facts z M p E)
    {D : Subgroup G} (hDE : D ≤ E) (hDc : Nat.card ↥D = p ^ 2) {Y : Subgroup G}
    (hYn : ∀ v ∈ Vof M E, v ∈ normalizer (Y : Set G)) (hzY : z ∈ normalizer (Y : Set G))
    (hF1 : Fpi (piF' M) Y ⊓ M = ⊥) : Fpi (piF' M) Y ≤ XDR M D := by
  have hp : p.Prime := hctx.prime
  obtain ⟨hinv, hodd⟩ := inverts_F1 hF.hMz (mul_self_eq_one_of_orderOf hF.hz2) hzY hF1
  have hσ' : ∀ q ∈ piF' M, q.Prime := fun q hq => prime_of_mem_piF' hq
  refine (Fpi_le_iSup_Op hσ' Y).trans (iSup₂_le fun q hq => ?_)
  have hqp : q ≠ p := by
    intro h
    exact hq.2 (h ▸ hF.hppi.2)
  have hDn : D ≤ normalizer ((Op q Y : Subgroup G) : Set G) := by
    intro v hv
    have hvV : v ∈ Vof M E := hF.hEV (hDE hv)
    refine mem_normalizer_of_cj_eq ?_
    unfold cj
    rw [← Op_map q (MulAut.conj v)]
    have : Y.map (MulAut.conj v).toMonoidHom = Y := cj_eq_of_mem_normalizer (hYn v hvV)
    rw [this]
  have hcop : Nat.Coprime p (Nat.card ↥(Op q Y)) := by
    have : Fact q.Prime := ⟨hσ' q hq⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).1 (isPGroup_Op q (hσ' q hq) Y)
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp (hσ' q hq)).2 hqp.symm)
  have hgen := h1123 G p hp D (Op q Y) (isElementaryAbelian_of_le hDE hctx.E_elem) hDc hcop hDn
  refine hgen.trans (iSup₂_le fun v hv => ?_)
  rintro x ⟨hxQ, hxC⟩
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  · have hxF1 : x ∈ Fpi (piF' M) Y := Op_le_Fpi hq (hσ' q hq) Y hxQ
    have hxM : x ∉ M := fun hxM =>
      hx1 (Subgroup.mem_bot.1 (hF1 ▸ (⟨hxF1, hxM⟩ : x ∈ Fpi (piF' M) Y ⊓ M)))
    have hvD : v ∈ Dstar M D := ⟨hv.1, hv.2, fun hle => hxM (hle hxC)⟩
    have hc2 := comm2_le_XdR hB12 h184 h171 hctx (hDE hv.1) hv.2 hvD.2.2
    have hxX : x ∈ XdR M v := odd_inverted_mem_XdR hc2 hxC (hinv x hxF1) (hodd x hxF1)
    have hle : XdR M v ≤ XDR M D := le_iSup₂_of_le v hvD le_rfl
    exact hle hxX

theorem comp_le_XDR (hB12 : Bender12) (h183 : Lemma18_3a) (h184 : Lemma18_4ac)
    (h186 : Lemma18_6) (h171 : Prop17_1) {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
    {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t) (hF : S5Facts z M p E)
    {D : Subgroup G} (hDE : D ≤ E)
    (hDc : Nat.card ↥D = p ^ 2) {Y : Subgroup G}
    (hYn : ∀ v ∈ Vof M E, v ∈ normalizer (Y : Set G)) (hYM : ¬ Y ≤ M) (hYtop : Y ≠ ⊤)
    {J : Subgroup G} (hJ : IsCompIn Y J) : J ≤ XDR M D := by
  have hp : p.Prime := hctx.prime
  have h3 := h183 G z k S M p E t hctx Y hYn hYM hYtop J hJ
  have hJz : ⁅J, zpowers z⁆ = J := h3.2.1
  have hJZ : ⁅J, omega1Z p (Op p M)⁆ = J := h3.2.2
  have hZJ : omega1Z p (Op p M) ≤ normalizer (J : Set G) := by
    have := le_normalizer_commutator (H := omega1Z p (Op p M)) (K := J)
    rwa [Subgroup.commutator_comm, hJZ] at this
  have hJM : ¬ J ≤ M := by
    intro hJM
    apply ne_bot_of_isCompIn hJ
    rw [← hJz]
    exact commutator_zpowers_eq_bot_of_le (hF.hMz ▸ hJM)
  rcases (h184 G z k S M p E t hctx Y hYn hYM hYtop J hJ).2 with ⟨hEZ, hidx⟩ | ⟨hL34, -⟩
  · obtain ⟨d, hdD, hd1, hdC⟩ := exists_centralizing_of_relIndex hp hZJ
      (K := centralizer (J : Set G) ⊓ (Y ⊔ pPrimeCoreOf 2 (Vof M E) ⊔ zpowers z)) inf_le_left
      (hDE.trans hEZ) hDc hidx
    have hdC' : J ≤ centralizer ({d} : Set G) := fun j hj =>
      Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hdC) j hj)
    have hdD' : d ∈ Dstar M D := ⟨hdD, hd1, fun hle => hJM (hdC'.trans hle)⟩
    have hc2 := comm2_le_XdR hB12 h184 h171 hctx (hDE hdD) hd1 hdD'.2.2
    exact (le_XdR_of_comp hc2 hdC' hJz).trans (le_iSup₂_of_le d hdD' le_rfl)
  · exact absurd hL34 (h186 G z k S M p E t hctx Y hYn hYM hYtop J hJ)

theorem member_le_XDR (hB12 : Bender12) (h183 : Lemma18_3a) (h184 : Lemma18_4ac)
    (h185 : Lemma18_5R) (h186 : Lemma18_6) (h171 : Prop17_1) (h1123 : IG_11_23) {z : G}
    {k : Kind} {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G}
    (hctx : Ctx18 G z k S M p E t) (hF : S5Facts z M p E) {D : Subgroup G} (hDE : D ≤ E)
    (hDc : Nat.card ↥D = p ^ 2) {Y : Subgroup G} (hY : Y ∈ XfamR z M (Vof M E)) :
    Y ≤ XDR M D := by
  have hYM : ¬ Y ≤ M := not_le_of_mem_XfamR hF.hMz hY
  have h5 : Y = Em Y ⊔ Fpi (piF' M) Y := h185 G z k S M p E t hctx Y hY
  obtain ⟨-, hYtop, hYn, hYz, hF1, -⟩ := hY
  have hzY : z ∈ normalizer (Y : Set G) := z_mem_normalizer_of_comm hYz
  rw [h5]
  refine sup_le (Em_le_of_forall_comp fun J hJ => ?_)
    (Fpi_le_XDR hB12 h184 h171 h1123 hctx hF hDE hDc hYn hzY hF1)
  exact comp_le_XDR hB12 h183 h184 h186 h171 hctx hF hDE hDc hYn hYM hYtop hJ

end Nine

theorem lemma18_9R_of (hB12 : Bender12) (h183 : Lemma18_3a) (h184 : Lemma18_4ac)
    (h185 : Lemma18_5R) (h186 : Lemma18_6) (h171 : Prop17_1) (h1123 : IG_11_23)
    (hcl : Claim18Xd) (h188 : Lemma18_8R) : Lemma18_9R := by
  intro G _ _ z k S M p E t hctx D hDE hDc hD
  by_contra hDtop
  have hF := S5Facts.of_ctx h171 hctx
  have hW := XDR_mem_XfamR hB12 h183 h171 hcl hctx hDE hD hDtop
  exact h188 G z k S M p E t hctx
    ⟨XDR M D, hW, fun Y hY =>
      member_le_XDR hB12 h183 h184 h185 h186 h171 h1123 hctx hF hDE hDc hY⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
