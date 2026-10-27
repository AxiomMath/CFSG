module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Cmm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Plane
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4aStmt
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

section Ten

variable {G : Type} [Group G] [Finite G]

theorem member_structure (h185 : Lemma18_5R) {z : G} {k : Kind}
    {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t)
    (hF : S5Facts z M p E) {X : Subgroup G} (hX : X ∈ XfamR z M (Vof M E)) (hEm : Em X = ⊥) :
    (∀ x ∈ X, z * x * z⁻¹ = x⁻¹) ∧ (∀ x ∈ X, Odd (orderOf x)) ∧
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) ∧ X ⊓ M = ⊥ ∧ ¬ p ∣ Nat.card ↥X := by
  have h5 : X = Em X ⊔ Fpi (piF' M) X := h185 G z k S M p E t hctx X hX
  rw [hEm, bot_sup_eq] at h5
  have hXF : X ≤ Fpi (piF' M) X := h5.le
  obtain ⟨-, -, -, hXz, hF1, -⟩ := hX
  have hzX := z_mem_normalizer_of_comm hXz
  obtain ⟨hinv, hodd⟩ := inverts_F1 hF.hMz (mul_self_eq_one_of_orderOf hF.hz2) hzX hF1
  refine ⟨fun x hx => hinv x (hXF hx), fun x hx => hodd x (hXF hx), ?_, ?_, ?_⟩
  · intro x hx y hy
    have h1 := hinv (x * y) (hXF (X.mul_mem hx hy))
    have h2 := hinv x (hXF hx)
    have h3 := hinv y (hXF hy)
    have e : z * (x * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹) := by group
    rw [e, h2, h3, mul_inv_rev] at h1
    have h4 := congrArg (fun w => w⁻¹) h1
    simp only [mul_inv_rev, inv_inv] at h4
    exact h4.symm
  · exact eq_bot_iff.2 ((inf_le_inf_right M hXF).trans hF1.le)
  · exact not_dvd_card_of_le_Fpi (fun q hq => prime_of_mem_piF' hq) hctx.prime
      (fun h => h.2 hF.hppi.2) X hXF

end Ten

theorem lemma18_10R_of (hB12 : Bender12) (h183 : Lemma18_3a) (h184 : Lemma18_4ac)
    (h185 : Lemma18_5R) (h171 : Prop17_1) (hcl : Claim18Xd) (h189 : Lemma18_9R) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (E : Subgroup G)
      (t : G), Ctx18 G z k S M p E t → ∃ X ∈ XfamR z M (Vof M E), Em X ≠ ⊥ := by
  intro G _ _ z k S M p E t hctx
  by_contra hno'
  have hno : ∀ X ∈ XfamR z M (Vof M E), Em X = ⊥ := by
    intro X hX
    by_contra h
    exact hno' ⟨X, hX, h⟩
  have hF := S5Facts.of_ctx h171 hctx
  have hp : p.Prime := hctx.prime
  have ht1 : t ≠ 1 := by
    intro h
    have := hctx.t_ord
    rw [h, orderOf_one] at this
    exact hp.one_lt.ne this
  have hX₀ := XdR_mem_XfamR hB12 h183 h171 hcl hctx hctx.t_E ht1 hctx.t_fail
  obtain ⟨hinv₀, hodd₀, -, hXM₀, hXp⟩ := member_structure h185 hctx hF hX₀ (hno _ hX₀)
  have h3 : 3 ≤ Open.pRank p E := by
    have := hctx.E_rank
    rwa [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp] at this
  obtain ⟨E₃, hE₃E, hE₃el, hE₃c⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp h3
  have hE₃e : IsElementaryAbelian p ↥E₃ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E₃).2 hE₃el
  have hE₃n : E₃ ≤ normalizer ((XdR M t : Subgroup G) : Set G) := fun v hv =>
    hX₀.2.2.1 v (hF.hEV (hE₃E hv))
  obtain ⟨D, hDE₃, hDc, x, hxX, hx1, hxD⟩ := exists_plane_fixing hp hE₃e hE₃c hE₃n hXp hX₀.1
  have hDE : D ≤ E := hDE₃.trans hE₃E
  have hxM : x ∉ M := fun hxM' =>
    hx1 (Subgroup.mem_bot.1 (hXM₀ ▸ (⟨hxX, hxM'⟩ : x ∈ XdR M t ⊓ M)))
  have hxC : ∀ d ∈ D, x ∈ centralizer ({d} : Set G) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hxD d hd).symm
  have hDstar : ∀ d ∈ D, d ≠ 1 → d ∈ Dstar M D := fun d hd hd1 =>
    ⟨hd, hd1, fun hle => hxM (hle (hxC d hd))⟩
  have hDne : (Dstar M D).Nonempty := by
    have hD1 : D ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hDc
      have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    obtain ⟨d, hd⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD1
    exact ⟨(d : G), hDstar d d.2 (fun h => hd (Subtype.ext h))⟩
  have hXD := h189 G z k S M p E t hctx D hDE hDc hDne
  have hle : XDR M D ≤ centralizer ({x} : Set G) := by
    refine iSup₂_le fun d hd => ?_
    have hXd := XdR_mem_XfamR hB12 h183 h171 hcl hctx (hDE hd.1) hd.2.1 hd.2.2
    obtain ⟨-, -, hab, -, -⟩ := member_structure h185 hctx hF hXd (hno _ hXd)
    have hxd : x ∈ XdR M d := odd_inverted_mem_XdR
      (comm2_le_XdR hB12 h184 h171 hctx (hDE hd.1) hd.2.1 hd.2.2) (hxC d hd.1)
      (hinv₀ x hxX) (hodd₀ x hxX)
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (hab y hy x hxd)
  rw [hXD] at hle
  exact centralizer_ne_top hF.hkps hx1 (top_le_iff.1 hle)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
