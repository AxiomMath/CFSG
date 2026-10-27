module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5L9
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5L10
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5L11
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5L8

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section P181

variable {G : Type} [Group G] [Finite G]

theorem exists_E {p : ℕ} (hp : p.Prime) {P : Subgroup G} {t : G} (htP : t ∈ P)
    (hord : orderOf t = p) (hrank : 3 ≤ CFSG.pRank p ↥(P ⊓ centralizer ({t} : Set G))) :
    ∃ A : Subgroup G, A ≤ P ⊓ centralizer ({t} : Set G) ∧ CFSG.Open.IsElemAbelian p A ∧
      Nat.card ↥A = p ^ 3 ∧ zpowers t ⊔ A ≤ P ∧ IsElementaryAbelian p ↥(zpowers t ⊔ A) ∧
      3 ≤ CFSG.pRank p ↥(zpowers t ⊔ A) := by
  have h3 : 3 ≤ CFSG.Open.pRank p (P ⊓ centralizer ({t} : Set G)) := by
    rwa [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp] at hrank
  obtain ⟨A, hAle, hAel, hAcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp h3
  have hzt : CFSG.Open.IsElemAbelian p (zpowers t) :=
    CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers (by rw [← hord]; exact pow_orderOf_eq_one t)
  have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hbt : b * t = t * b := Subgroup.mem_centralizer_singleton_iff.1 (hAle hb).2
    exact ((Commute.zpow_left (show Commute t b from hbt.symm) n)).eq
  have hEel : CFSG.Open.IsElemAbelian p (zpowers t ⊔ A) :=
    CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup hzt hAel hcomm
  refine ⟨A, hAle, hAel, hAcard, sup_le (Subgroup.zpowers_le.2 htP) (hAle.trans inf_le_left),
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).2 hEel, ?_⟩
  have := CFSG.GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt
    (le_sup_right : A ≤ zpowers t ⊔ A) hAel hAcard
  rwa [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp]

theorem comp_comm_eq (h183 : Lemma18_3a) {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
    {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t) (hF : S5Facts z M p E)
    {X : Subgroup G} (hX : X ∈ XfamR z M (Vof M E)) {J : Subgroup G} (hJ : IsCompIn X J) :
    ⁅J, zpowers z⁆ = J ∧ ⁅J, omega1Z p (Op p M)⁆ = J :=
  (h183 G z k S M p E t hctx X hX.2.2.1 (not_le_of_mem_XfamR hF.hMz hX) hX.2.1 J hJ).2

theorem exists_D (h183 : Lemma18_3a) (h184 : Lemma18_4ac) (h186 : Lemma18_6) {z : G} {k : Kind}
    {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t)
    (hF : S5Facts z M p E) {X : Subgroup G} (hX : X ∈ XfamR z M (Vof M E)) {J : Subgroup G}
    (hJ : IsCompIn X J) {A : Subgroup G} (hAE : A ≤ E) (hAel : CFSG.Open.IsElemAbelian p A)
    (hAcard : Nat.card ↥A = p ^ 3) :
    ∃ D : Subgroup G, D ≤ A ∧ Nat.card ↥D = p ^ 2 ∧ D ≤ centralizer (J : Set G) := by
  have hp : p.Prime := hctx.prime
  have hXM := not_le_of_mem_XfamR hF.hMz hX
  have hZJ : omega1Z p (Op p M) ≤ normalizer (J : Set G) := by
    have := le_normalizer_commutator (H := omega1Z p (Op p M)) (K := J)
    rwa [Subgroup.commutator_comm, (comp_comm_eq h183 hctx hF hX hJ).2] at this
  rcases (h184 G z k S M p E t hctx X hX.2.2.1 hXM hX.2.1 J hJ).2 with ⟨hEZ, hidx⟩ | ⟨hL34, -⟩
  swap
  · exact absurd hL34 (h186 G z k S M p E t hctx X hX.2.2.1 hXM hX.2.1 J hJ)
  have hle := card_le_mul_card_inf hp hZJ
    (K := centralizer (J : Set G) ⊓ (X ⊔ pPrimeCoreOf 2 (Vof M E) ⊔ zpowers z)) inf_le_left
    (hAE.trans hEZ) hidx
  rw [hAcard] at hle
  have hF' : CFSG.Open.IsElemAbelian p (A ⊓ centralizer (J : Set G)) :=
    CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.mono inf_le_left hAel
  obtain ⟨j, hj⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card hp hF'
  have hj2 : 2 ≤ j := by
    rw [hj] at hle
    have h1 : p * p ^ 2 ≤ p * p ^ j := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ p * p ^ j := hle
    have h2 : p ^ 2 ≤ p ^ j := Nat.le_of_mul_le_mul_left h1 hp.pos
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h2
  obtain ⟨D, hDle, -, hDcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_subgroup_card hp hF' hj2 hj
  exact ⟨D, hDle.trans inf_le_left, hDcard, hDle.trans inf_le_right⟩

omit [Finite G] in
theorem Dstar_nonempty {z : G} {M J D : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hMz : M = centralizer {z}) (hJz : ⁅J, zpowers z⁆ = J) (hJ : J ≠ ⊥)
    (hDJ : D ≤ centralizer (J : Set G)) (hDc : Nat.card ↥D = p ^ 2) : (Dstar M D).Nonempty := by
  have hJM : ¬ J ≤ M := by
    intro h
    apply hJ
    rw [← hJz]
    exact commutator_zpowers_eq_bot_of_le (hMz ▸ h)
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDc
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  obtain ⟨d, hd⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD1
  have hd1 : (d : G) ≠ 1 := fun h => hd (Subtype.ext h)
  have hJd : J ≤ centralizer ({(d : G)} : Set G) := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hDJ d.2) j hj)
  exact ⟨d, d.2, hd1, fun hle => hJM (hJd.trans hle)⟩

end P181

theorem prop18_1_of (hB12 : Bender12) (h171 : Prop17_1) (h183 : Lemma18_3a)
    (h184 : Lemma18_4ac) (h185 : Lemma18_5R) (h186 : Lemma18_6) (h1123 : IG_11_23)
    (hcl : Claim18Xd) : Prop18_1 := by
  intro G _ _ z k S M hF17 p hp hp2 hrank t ht hord htrank
  by_contra hfail
  obtain ⟨A, hAle, hAel, hAcard, hEP, hEel, hErank⟩ := exists_E hp ht hord htrank
  have htE : t ∈ zpowers t ⊔ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hAE : A ≤ zpowers t ⊔ A := le_sup_right
  have hctx : Ctx18 G z k S M p (zpowers t ⊔ A) t :=
    ⟨hF17, hp, hp2, hrank, ht, hord, htrank, hfail, hEP, hEel, htE, hErank⟩
  have hF := S5Facts.of_ctx h171 hctx
  have h188 := lemma18_8R_of h171
  have h189 := lemma18_9R_of hB12 h183 h184 h185 h186 h171 h1123 hcl h188
  have h1810 := lemma18_10R_of hB12 h183 h184 h185 h171 hcl h189
  have h1811 := lemma18_11Q_of hB12 h171 h183 h184 h185 hcl
  obtain ⟨X₀, hX₀, hEm₀⟩ := h1810 G z k S M p (zpowers t ⊔ A) t hctx
  have hcomp₀ : ∃ J₀, IsCompIn X₀ J₀ := by
    by_contra hno
    push Not at hno
    exact hEm₀ (le_bot_iff.1 (Em_le_of_forall_comp fun J hJ => absurd hJ (hno J)))
  obtain ⟨J₀, hJ₀⟩ := hcomp₀
  obtain ⟨Jm, ⟨Xm, hXm, hJm⟩, hmaxJ⟩ := Set.exists_max_image
    {J : Subgroup G | ∃ X ∈ XfamR z M (Vof M (zpowers t ⊔ A)), IsCompIn X J} ordq
    (Set.toFinite _) ⟨J₀, X₀, hX₀, hJ₀⟩
  have hmax : ∀ X' ∈ XfamR z M (Vof M (zpowers t ⊔ A)), ∀ J' : Subgroup G, IsCompIn X' J' →
      ordq J' ≤ ordq Jm := fun X' hX' J' hJ' => hmaxJ J' ⟨X', hX', hJ'⟩
  by_cases hQex : ∃ X D : Subgroup G, QTriple z M (zpowers t ⊔ A) p (ordq Jm) X D
  · obtain ⟨X, D, hQ⟩ := hQex
    obtain ⟨hXmem, ⟨J₁, J₂, hJ₁, hJ₂, hJ12, hEmX, hm1, hm2⟩, hDE, hDc, hDEm⟩ := hQ
    have hDJ : D ≤ centralizer (J₁ : Set G) := fun v hv =>
      Subgroup.mem_centralizer_iff.2 fun x hx =>
        Subgroup.mem_centralizer_iff.1 (hDEm hv) x (le_Em_of_isCompIn hJ₁ hx)
    have hlt := h1811 G z k S M p (zpowers t ⊔ A) t hctx (ordq Jm) hmax X hXmem J₁ hJ₁ hm1 D hDE
      hDc hDJ (fun _ => ⟨hXmem, ⟨J₁, J₂, hJ₁, hJ₂, hJ12, hEmX, hm1, hm2⟩, hDE, hDc, hDEm⟩)
    have hDn := Dstar_nonempty hp hF.hMz (comp_comm_eq h183 hctx hF hXmem hJ₁).1
      (ne_bot_of_isCompIn hJ₁) hDJ hDc
    exact absurd (h189 G z k S M p (zpowers t ⊔ A) t hctx D hDE hDc hDn) hlt.ne
  · obtain ⟨D, hDA, hDc, hDJ⟩ := exists_D h183 h184 h186 hctx hF hXm hJm hAE hAel hAcard
    have hDE : D ≤ zpowers t ⊔ A := hDA.trans hAE
    have hlt := h1811 G z k S M p (zpowers t ⊔ A) t hctx (ordq Jm) hmax Xm hXm Jm hJm rfl D hDE
      hDc hDJ (fun h => absurd h hQex)
    have hDn := Dstar_nonempty hp hF.hMz (comp_comm_eq h183 hctx hF hXm hJm).1
      (ne_bot_of_isCompIn hJm) hDJ hDc
    exact absurd (h189 G z k S M p (zpowers t ⊔ A) t hctx D hDE hDc hDn) hlt.ne

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
