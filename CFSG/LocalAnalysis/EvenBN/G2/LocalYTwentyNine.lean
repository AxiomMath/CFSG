module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwentyEight

public section


namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Torus

variable {K : Type} [Field K]
  [Finite K]

theorem exists_centralizer_J₆_mul [CharP K 2] (d : G2Data L K) {M N : Subgroup G} (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set G)) (hJM : d.J₆ ≤ normalizer (M : Set G))
    (hJN : d.J₆ ≤ normalizer (N : Set G)) (hM : IsPGroup 2 M) {m : G} (hm : m ∈ M)
    (hfix : ∀ j ∈ d.J₆, m⁻¹ * (j * m * j⁻¹) ∈ N) :
    ∃ c ∈ M ⊓ centralizer (d.J₆ : Set G), ∃ n ∈ N, m = c * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent M := hM.isNilpotent
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hM
  refine Common.exists_mem_inf_centralizer_mul_of_coprime hNM hMN hJM hJN inferInstance ?_ hm
    hfix
  rw [hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2
    ((odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le (d.image_mono inf_le_left))))

end Torus

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem rootGroup_v_sup_yamadaU₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    d.rootGroup g2v ⊔ yamadaU₂ d t = yamadaE₂ d t ∧ d.rootGroup g2v ⊓ yamadaU₂ d t = ⊥ ∧
      d.rootGroup g2v ≤ normalizer (yamadaU₂ d t : Set G) := by
  obtain ⟨-, hYX, hYW, hXF, hWF, hFD, -, hDS, -⟩ := d.inclusions
  obtain ⟨-, -, hW, hF, -, -, hXW, -⟩ := d.yamada_defs
  have hAW : d.rootGroup g2v ≤ d.W := le_sup_left.trans hW.le
  have hAS : d.rootGroup g2v ≤ d.S := hAW.trans (hWF.trans (hFD.trans hDS))
  have hSU : d.S ≤ normalizer (yamadaU₂ d t : Set G) := fun s hs =>
    (h.le_normalizer_yamadaU₂ d hK hD).1 (Subgroup.mem_inf.2
      ⟨h.L_le_centralizer (d.image_le _ hs), Subgroup.le_normalizer hs⟩)
  have hAE : d.rootGroup g2v ≤ yamadaE₂ d t :=
    (hAW.trans hWF).trans (le_sup_left.trans le_sup_left)
  have hUE : yamadaU₂ d t ≤ yamadaE₂ d t := sup_le_sup_right (sup_le_sup_right hXF _) _
  have hXU : d.X ≤ yamadaU₂ d t := le_sup_left.trans le_sup_left
  have hFAU : d.F ≤ d.rootGroup g2v ⊔ yamadaU₂ d t := by
    rw [← hF, ← hW]
    exact sup_le (hXU.trans le_sup_right)
      (sup_le le_sup_left ((hYX.trans hXU).trans le_sup_right))
  have hAX : d.rootGroup g2v ⊓ d.X = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxA, hxX⟩ := Subgroup.mem_inf.1 hx
    rw [← Y_inf_rootGroup_v d]
    refine Subgroup.mem_inf.2 ⟨?_, hxA⟩
    rw [← hXW]
    exact Subgroup.mem_inf.2 ⟨hxX, hAW hxA⟩
  have hAU : d.rootGroup g2v ⊓ yamadaU₂ d t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxA, hxU⟩ := Subgroup.mem_inf.1 hx
    have hxL : x ∈ L := d.image_le _ hxA
    have hX₂L : yamadaX₂ d t ⊓ centralizer ({t} : Set G) ≤ L := by
      rw [h.yamadaX₂_inf_centralizer d hK hD]
      exact d.image_le _
    have hxX₂ :=
      h.mem_of_mem_sup_zpowers_of_le (h.t_mem_normalizer_yamadaX₂ d hK hD).1 hX₂L hxL hxU
    have hxX : x ∈ d.X := by
      rw [← h.yamadaX₂_inf_centralizer d hK hD]
      exact Subgroup.mem_inf.2 ⟨hxX₂, h.L_le_centralizer hxL⟩
    rw [← hAX]
    exact Subgroup.mem_inf.2 ⟨hxA, hxX⟩
  refine ⟨le_antisymm (sup_le hAE hUE) (sup_le (sup_le hFAU ?_) ?_), hAU, hAS.trans hSU⟩
  · exact (le_sup_right.trans le_sup_left).trans le_sup_right
  · exact (le_sup_right : zpowers t ≤ yamadaU₂ d t).trans le_sup_right

theorem J_le_normalizers_four (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    d.J ≤ normalizer (yamadaL₄ d t : Set G) ∧ d.J ≤ normalizer (yamadaC₄ d t : Set G) ∧
      d.J ≤ normalizer (yamadaE₄ d t : Set G) ∧ d.J ≤ normalizer (yamadaE₂ d t : Set G) ∧
      d.J ≤ normalizer (yamadaU₂ d t : Set G) := by
  obtain ⟨hJ₆J, -⟩ := h.J₆_facts d hK
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hJR₄ := h.J_le_normalizer_yamadaR₄ d hK hD
  have hJL₂ : d.J ≤ normalizer (yamadaL₂ d t : Set G) := fun j hj =>
    le_normalizer_yamadaL₂ d t ((h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK
      hD).2 (mem_sup_right (hJC hj)))
  have hJCs : d.J ≤ normalizer (yamadaCstar d t : Set G) := fun j hj =>
    LieType.BorelTits.le_normalizer_pCoreOf 2 _
      ((h.centralizer_inf_normalizer_S_le d hK hD).1 (hJC hj))
  have hL₄ : d.J ≤ normalizer (yamadaL₄ d t : Set G) := fun j hj =>
    mem_normalizer_sup (Common.mem_normalizer_inf (hJR₄ hj)
      (Subgroup.le_normalizer (mem_centralizer_iff.2 fun y hy => J_mul_comm d (hJ₆J hy) hj)))
      (hJL₂ hj)
  have hC₄ : d.J ≤ normalizer (yamadaC₄ d t : Set G) := fun j hj =>
    Common.mem_normalizer_inf (hJR₄ hj) (hJCs hj)
  exact ⟨hL₄, hC₄, fun j hj => Common.mem_normalizer_inf (hL₄ hj) (hC₄ hj),
    fun j hj => (h.centralizer_inf_normalizer_S_le_normalizers hW d hK hD).2.2.2 (hJC hj),
    fun j hj => (h.le_normalizer_yamadaU₂ d hK hD).1 (hJC hj)⟩

theorem yamadaE₄_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaE₂ d t ≤ yamadaE₄ d t ∧ yamadaE₄ d t ⊓ d.S = d.F ∧
      yamadaR₄ d t ≤ normalizer (yamadaE₂ d t : Set G) ∧
      yamadaR₄ d t ≤ normalizer (yamadaE₄ d t : Set G) ∧
      yamadaL₄ d t ⊓ yamadaC₂ d t ≤ yamadaE₂ d t ∧
      Nat.card (yamadaE₄ d t) = 2 * Nat.card K ^ 7 ∧ d.S ⊔ yamadaE₄ d t = yamadaR₄ d t := by
  obtain ⟨-, hR₂R₄, -, hR₄Cs, hC₂, hR₄c⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨hR₄C₂, hR₄eq, hC₄R₂, hR₄C₄, -⟩ := h.yamada_5_32_1_R₄ hW d hK hD
  obtain ⟨hR₄L₂, -, hL₄R₂, hR₄L₄, -⟩ := h.yamada_5_32_1_L₄ hW d hK hD
  obtain ⟨-, -, -, -, hL₄R₄, hL₄c⟩ := h.yamadaL₄_facts hW d hK hD
  obtain ⟨-, -, -, -, -, hFD, -, hDS, hMS, -⟩ := d.inclusions
  have hL₂C₂ := h.yamadaL₂_inf_yamadaC₂ d hK hD
  have hMC₂ := h.M_inf_yamadaC₂ d hK hD
  have hL₂L₄ : yamadaL₂ d t ≤ yamadaL₄ d t := le_sup_right
  have hC₂C₄ : yamadaC₂ d t ≤ yamadaC₄ d t := hC₄R₂.ge.trans inf_le_left
  have hE₂E₄ : yamadaE₂ d t ≤ yamadaE₄ d t :=
    le_inf ((hL₂C₂.ge.trans inf_le_left).trans hL₂L₄) ((hL₂C₂.ge.trans inf_le_right).trans hC₂C₄)
  have hR₄E₂ : yamadaR₄ d t ≤ normalizer (yamadaE₂ d t : Set G) := fun x hx => by
    rw [← hL₂C₂]
    exact Common.mem_normalizer_inf (hR₄L₂ hx) (hR₄C₂ hx)
  have hR₄E₄ : yamadaR₄ d t ≤ normalizer (yamadaE₄ d t : Set G) := fun x hx =>
    Common.mem_normalizer_inf (hR₄L₄ hx) (hR₄C₄ hx)
  have hML₂ : d.M ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d hK)
  have hL₄C₂ : yamadaL₄ d t ⊓ yamadaC₂ d t ≤ yamadaE₂ d t := fun x hx => by
    obtain ⟨hxL₄, hxC₂⟩ := Subgroup.mem_inf.1 hx
    rw [← hL₂C₂]
    refine Subgroup.mem_inf.2 ⟨?_, hxC₂⟩
    rw [← hL₄R₂]
    exact Subgroup.mem_inf.2 ⟨hxL₄, (hC₂.le.trans inf_le_right) hxC₂⟩
  have hE₄S : yamadaE₄ d t ⊓ d.S = d.F := by
    refine le_antisymm (fun x hx => ?_)
      (le_inf ((le_sup_left.trans le_sup_left).trans hE₂E₄) (hFD.trans hDS))
    obtain ⟨hxE, hxS⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxL₄, hxC₄⟩ := Subgroup.mem_inf.1 hxE
    have hxR₂ : x ∈ yamadaR₂ d t := (le_sup_right : d.S ≤ yamadaR₂ d t) hxS
    have hxL₂ : x ∈ yamadaL₂ d t := hL₄R₂.le (Subgroup.mem_inf.2 ⟨hxL₄, hxR₂⟩)
    have hxM : x ∈ d.M := (h.yamadaL₂_inf_S d hK).le (Subgroup.mem_inf.2 ⟨hxL₂, hxS⟩)
    have hxC₂ : x ∈ yamadaC₂ d t := hC₂.ge (Subgroup.mem_inf.2
      ⟨(Subgroup.mem_inf.1 hxC₄).2, hxR₂⟩)
    exact hMC₂.le (Subgroup.mem_inf.2 ⟨hxM, hxC₂⟩)
  have hq : 0 < Nat.card K := Nat.card_pos
  have hC₄c : Nat.card (yamadaC₄ d t) = 2 * Nat.card K ^ 8 := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaC₄ d t) (B := yamadaR₂ d t)
      (hR₂R₄.trans hR₄C₄)
    rw [← hR₄eq, hC₄R₂, hR₄c, (h.card_yamadaC₂_E₂_V₂ d hK hD).1, h.card_yamadaR₂ d hK] at h1
    refine Nat.eq_of_mul_eq_mul_right (show 0 < 2 * Nat.card K ^ 8 by positivity) ?_
    rw [← h1]
    ring
  have hlow : 2 * Nat.card K ^ 7 ≤ Nat.card (yamadaE₄ d t) := by
    have h1 : Nat.card (yamadaL₄ d t ⊔ yamadaC₄ d t : Subgroup G) * Nat.card (yamadaE₄ d t) =
        Nat.card (yamadaL₄ d t) * Nat.card (yamadaC₄ d t) :=
      Common.card_sup_mul_card_inf_eq ((inf_le_left : yamadaC₄ d t ≤ yamadaR₄ d t).trans hR₄L₄)
    have h2 : Nat.card (yamadaL₄ d t ⊔ yamadaC₄ d t : Subgroup G) ≤ 2 * Nat.card K ^ 9 := by
      rw [← hR₄c]
      exact Subgroup.card_le_of_le (sup_le hL₄R₄ inf_le_left)
    rw [hL₄c, hC₄c] at h1
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < 2 * Nat.card K ^ 9 by positivity)
    calc 2 * Nat.card K ^ 7 * (2 * Nat.card K ^ 9) =
          Nat.card (yamadaL₄ d t ⊔ yamadaC₄ d t : Subgroup G) * Nat.card (yamadaE₄ d t) := by
          rw [h1]
          ring
      _ ≤ 2 * Nat.card K ^ 9 * Nat.card (yamadaE₄ d t) := Nat.mul_le_mul_right _ h2
      _ = Nat.card (yamadaE₄ d t) * (2 * Nat.card K ^ 9) := by ring
  have hE₄R₄ : yamadaE₄ d t ≤ yamadaR₄ d t := inf_le_left.trans hL₄R₄
  have hSR₄ : d.S ≤ yamadaR₄ d t := (le_sup_right : d.S ≤ yamadaR₂ d t).trans hR₂R₄
  have h3 : Nat.card (yamadaE₄ d t ⊔ d.S : Subgroup G) * Nat.card K ^ 4 =
      Nat.card (yamadaE₄ d t) * Nat.card K ^ 6 := by
    have := Common.card_sup_mul_card_inf_eq (A := yamadaE₄ d t) (B := d.S) (hSR₄.trans hR₄E₄)
    rwa [hE₄S, d.cards.2.2.2.2.1, d.cards.2.2.2.2.2.2.2] at this
  have hle : yamadaE₄ d t ⊔ d.S ≤ yamadaR₄ d t := sup_le hE₄R₄ hSR₄
  have hcard : Nat.card (yamadaE₄ d t) = 2 * Nat.card K ^ 7 := by
    refine le_antisymm (Nat.le_of_mul_le_mul_right (c := Nat.card K ^ 6) ?_ (by positivity))
      hlow
    calc Nat.card (yamadaE₄ d t) * Nat.card K ^ 6 =
          Nat.card (yamadaE₄ d t ⊔ d.S : Subgroup G) * Nat.card K ^ 4 := h3.symm
      _ ≤ Nat.card (yamadaR₄ d t) * Nat.card K ^ 4 :=
          Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hle)
      _ = 2 * Nat.card K ^ 7 * Nat.card K ^ 6 := by rw [hR₄c]; ring
  refine ⟨hE₂E₄, hE₄S, hR₄E₂, hR₄E₄, hL₄C₂, hcard, ?_⟩
  rw [sup_comm]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h5 : Nat.card (yamadaE₄ d t ⊔ d.S : Subgroup G) * Nat.card K ^ 4 =
      Nat.card (yamadaR₄ d t) * Nat.card K ^ 4 := by
    rw [h3, hcard, hR₄c]
    ring
  exact (Nat.eq_of_mul_eq_mul_right (by positivity) h5).ge

theorem inv_mul_conj_mem_yamadaE₂_of_J₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {e j : G}
    (he : e ∈ yamadaE₄ d t) (hj : j ∈ d.J₆) : e⁻¹ * (j * e * j⁻¹) ∈ yamadaE₂ d t := by
  obtain ⟨hJ₆J, -⟩ := h.J₆_facts d hK
  obtain ⟨-, -, hJE₄, -⟩ := h.J_le_normalizers_four hW d hK hD
  obtain ⟨-, -, -, -, hL₄R₄, -⟩ := h.yamadaL₄_facts hW d hK hD
  obtain ⟨-, -, -, -, hC₂, -⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨-, -, -, -, hL₄C₂, -⟩ := h.yamadaE₄_facts hW d hK hD
  have heR₄ : e ∈ yamadaR₄ d t := hL₄R₄ (Subgroup.mem_inf.1 he).1
  have h1 := h.inv_mul_conj_mem_yamadaR₂_of_J₆ hW d hK hD heR₄ hj
  have h2 : e⁻¹ * (j * e * j⁻¹) ∈ yamadaE₄ d t :=
    mul_mem (inv_mem he) ((mem_normalizer_iff.1 (hJE₄ (hJ₆J hj)) _).1 he)
  exact hL₄C₂ (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 h2).1, hC₂.ge (Subgroup.mem_inf.2
    ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 h2).2).2, h1⟩)⟩)

theorem yamadaR₄_inf_centralizer_J₆_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₄ d t ⊓ centralizer (d.J₆ : Set G) ≤ yamadaE₄ d t := fun c hc => by
  obtain ⟨hcR, hcJ⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨hJ₆J, -, hC, -⟩ := h.J₆_facts d hK
  obtain ⟨-, -, hJE₄, -⟩ := h.J_le_normalizers_four hW d hK hD
  obtain ⟨-, hE₄S, -, hR₄E₄, -, -, hSE⟩ := h.yamadaE₄_facts hW d hK hD
  obtain ⟨-, hR₂R₄, -⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨-, -, -, hXF, -, hFD, -, hDS, -⟩ := d.inclusions
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hJF : d.J₆ ≤ normalizer (d.F : Set G) := fun j hj => by
    have : j ∈ L ⊓ normalizer (d.F : Set G) := by
      rw [d.yamada_3_13_1_G.2.1]
      exact mem_sup_left (hJ₆J hj)
    exact (Subgroup.mem_inf.1 this).2
  rw [← hSE] at hcR
  obtain ⟨s, hs, e, he, rfl⟩ := Common.exists_mul_of_le_normalizer'
    (((le_sup_right : d.S ≤ yamadaR₂ d t).trans hR₂R₄).trans hR₄E₄) _ hcR
  have hfix : ∀ j ∈ d.J₆, s⁻¹ * (j * s * j⁻¹) ∈ d.F := fun j hj => by
    have hjc : j * (s * e) = s * e * j := mem_centralizer_iff.1 hcJ j hj
    have hjS := (Subgroup.mem_inf.1 (hJC (hJ₆J hj))).2
    rw [← hE₄S]
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (inv_mem hs) ((mem_normalizer_iff.1 hjS _).1 hs)⟩
    rw [show s⁻¹ * (j * s * j⁻¹) = e * (j * e * j⁻¹)⁻¹ by
      calc s⁻¹ * (j * s * j⁻¹) = s⁻¹ * (j * (s * e) * j⁻¹) * (j * e * j⁻¹)⁻¹ := by group
        _ = e * (j * e * j⁻¹)⁻¹ := by rw [hjc]; group]
    exact mul_mem he (inv_mem ((mem_normalizer_iff.1 (hJE₄ (hJ₆J hj)) _).1 he))
  obtain ⟨c', hc', n, hn, rfl⟩ := exists_centralizer_J₆_mul d (hFD.trans hDS)
    d.S_le_normalizers.2.2.2.2.1 (fun j hj => (Subgroup.mem_inf.1 (hJC (hJ₆J hj))).2) hJF
    d.isSylowOf_S.isPGroup hs hfix
  have hc'F : c' ∈ d.F := by
    rw [hC] at hc'
    exact hXF ((le_sup_left.trans d.yamada_defs.2.1.le) hc')
  have hFE₄ : d.F ≤ yamadaE₄ d t := hE₄S.ge.trans inf_le_left
  exact mul_mem (mul_mem (hFE₄ hc'F) (hFE₄ hn)) he

theorem yamadaE₂_inf_centralizer_J₆_le (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaE₂ d t ⊓ centralizer (d.J₆ : Set G) ≤ yamadaU₂ d t := fun x hx => by
  obtain ⟨hxE, hxJ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hJ₆J, hJ₆c, -, hJA, -, hreg⟩ := h.J₆_facts d hK
  obtain ⟨hE, hAU, hAN⟩ := h.rootGroup_v_sup_yamadaU₂ d hK hD
  have hJU : d.J₆ ≤ normalizer (yamadaU₂ d t : Set G) := fun j hj =>
    (h.le_normalizer_yamadaU₂ d hK hD).1 (h.J_le_centralizer_inf_normalizer_S d (hJ₆J hj))
  rw [← hE] at hxE
  obtain ⟨a, ha, v, hv, rfl⟩ := Common.exists_mul_of_le_normalizer' hAN _ hxE
  by_cases ha1 : a = 1
  · rw [ha1, one_mul]
    exact hv
  exfalso
  have hall : ∀ j ∈ d.J₆, j = 1 := fun j hj => by
    refine hreg a ha ha1 j hj ?_
    have hjx : j * (a * v) = a * v * j := mem_centralizer_iff.1 hxJ j hj
    have hmem : a⁻¹ * (j * a * j⁻¹) ∈ d.rootGroup g2v ⊓ yamadaU₂ d t := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha) ((mem_normalizer_iff.1 (hJA hj) _).1 ha),
        ?_⟩
      rw [show a⁻¹ * (j * a * j⁻¹) = v * (j * v * j⁻¹)⁻¹ by
        calc a⁻¹ * (j * a * j⁻¹) = a⁻¹ * (j * (a * v) * j⁻¹) * (j * v * j⁻¹)⁻¹ := by group
          _ = v * (j * v * j⁻¹)⁻¹ := by rw [hjx]; group]
      exact mul_mem hv (inv_mem ((mem_normalizer_iff.1 (hJU hj) _).1 hv))
    rw [hAU, Subgroup.mem_bot] at hmem
    calc j * a = a * (a⁻¹ * (j * a * j⁻¹)) * j := by group
      _ = a * j := by rw [hmem, mul_one]
  have hbot : d.J₆ = ⊥ := eq_bot_iff.2 fun j hj => (Subgroup.mem_bot).2 (hall j hj)
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  rw [hbot, Subgroup.card_bot] at hJ₆c
  omega

theorem yamada_5_32_1_E₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaE₄ d t ≤ normalizer (yamadaU₂ d t : Set G) ∧
      yamadaE₄ d t = yamadaU₄ d t ⊔ yamadaE₂ d t ∧ yamadaU₄ d t ⊓ yamadaE₂ d t = yamadaU₂ d t ∧
      yamadaE₄ d t ≤ normalizer (yamadaU₄ d t : Set G) ∧
      yamadaE₄ d t ≤ normalizer (yamadaE₂ d t : Set G) ∧
      (∀ x ∈ yamadaE₄ d t, x * x ∈ yamadaU₂ d t) ∧
      (∀ x ∈ yamadaE₄ d t, ∀ y ∈ yamadaE₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaU₂ d t) ∧
      Nat.card (yamadaE₄ d t) = Nat.card K ^ 2 * Nat.card (yamadaU₂ d t) := by
  obtain ⟨hJ₆J, -, -, hJA, htrans, hreg⟩ := h.J₆_facts d hK
  obtain ⟨hR₄R, -, -, -, -, -⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨-, -, -, -, -, hsqR₄, -, -⟩ := h.yamada_5_32_1_R₄ hW d hK hD
  obtain ⟨hE₂E₄, -, hR₄E₂, -, hL₄C₂, hcard, -⟩ := h.yamadaE₄_facts hW d hK hD
  obtain ⟨-, -, -, -, hL₄R₄, -⟩ := h.yamadaL₄_facts hW d hK hD
  obtain ⟨-, -, hJE₄, hJE₂, hJU₂⟩ := h.J_le_normalizers_four hW d hK hD
  obtain ⟨hAE, hAU, hAN⟩ := h.rootGroup_v_sup_yamadaU₂ d hK hD
  have hR₄p : IsPGroup 2 (yamadaR₄ d t) := (h.isPGroup_yamadaRstar d).to_le hR₄R
  have hR₄U₂ : yamadaR₄ d t ≤ normalizer (yamadaU₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hJU : d.J₆ ≤ normalizer (yamadaU₂ d t : Set G) := fun j hj => hJU₂ (hJ₆J hj)
  have hU₂E₂ : yamadaU₂ d t ≤ yamadaE₂ d t := le_sup_right.trans hAE.le
  have hE₄R₄ : yamadaE₄ d t ≤ yamadaR₄ d t := inf_le_left.trans hL₄R₄
  have hE₄U₂ : yamadaE₄ d t ≤ normalizer (yamadaU₂ d t : Set G) := hE₄R₄.trans hR₄U₂
  have hE₂U₂ : yamadaE₂ d t ≤ normalizer (yamadaU₂ d t : Set G) := hE₂E₄.trans hE₄U₂
  have hCU₂ : yamadaR₄ d t ⊓ centralizer (d.J₆ : Set G) ≤ normalizer (yamadaU₂ d t : Set G) :=
    inf_le_left.trans hR₄U₂
  have hCJ := h.yamadaR₄_inf_centralizer_J₆_le hW d hK hD
  have hU₄E₄ : yamadaU₄ d t ≤ yamadaE₄ d t := sup_le hCJ (hU₂E₂.trans hE₂E₄)
  have hE₄eq : yamadaE₄ d t = yamadaU₄ d t ⊔ yamadaE₂ d t := by
    refine le_antisymm (fun e he => ?_) (sup_le hU₄E₄ hE₂E₄)
    obtain ⟨c, hc, n, hn, rfl⟩ := exists_centralizer_J₆_mul d hE₂E₄ (hE₄R₄.trans hR₄E₂)
      (fun j hj => hJE₄ (hJ₆J hj)) (fun j hj => hJE₂ (hJ₆J hj)) (hR₄p.to_le hE₄R₄) he
      (fun j hj => h.inv_mul_conj_mem_yamadaE₂_of_J₆ hW d hK hD he hj)
    exact mul_mem (mem_sup_left (mem_sup_left (Subgroup.mem_inf.2
      ⟨hE₄R₄ (Subgroup.mem_inf.1 hc).1, (Subgroup.mem_inf.1 hc).2⟩))) (mem_sup_right hn)
  have hU₄E₂ : yamadaU₄ d t ⊓ yamadaE₂ d t = yamadaU₂ d t := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hU₂E₂)
    obtain ⟨hxU, hxE⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨c, hc, v, hv, rfl⟩ := Common.exists_mul_of_le_normalizer' hCU₂ _ hxU
    have hcE : c ∈ yamadaE₂ d t := by
      have := mul_mem hxE (inv_mem (hU₂E₂ hv))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (h.yamadaE₂_inf_centralizer_J₆_le d hK hD
      (Subgroup.mem_inf.2 ⟨hcE, (Subgroup.mem_inf.1 hc).2⟩)) hv
  have hE9 : ∀ c ∈ yamadaR₄ d t ⊓ centralizer (d.J₆ : Set G), ∀ e ∈ yamadaE₂ d t,
      c * e * c⁻¹ * e⁻¹ ∈ yamadaU₂ d t := fun c hc => by
    obtain ⟨hcR, hcJ⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨m, hm⟩ := hR₄p ⟨c, hcR⟩
    have hcm : c ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    exact conj_mul_inv_mem_of_regular (le_sup_left.trans hAE.le)
      (fun e he => Common.exists_mul_of_le_normalizer' hAN e (hAE.ge he)) hE₂U₂ hAU hJA hJU
      (fun j hj k hk => J_mul_comm d (hJ₆J hj) (hJ₆J hk))
      ((odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le hJ₆J)) htrans hreg
      (hR₄E₂ hcR) (hR₄U₂ hcR) hcJ hcm
  have hE₂NU₄ : yamadaE₂ d t ≤ normalizer (yamadaU₄ d t : Set G) := fun e he =>
    mem_normalizer_of_conj_mem fun x hx => by
      obtain ⟨c, hc, v, hv, rfl⟩ := Common.exists_mul_of_le_normalizer' hCU₂ _ hx
      rw [show e * (c * v) * e⁻¹ = c * (c⁻¹ * e * c⁻¹⁻¹ * e⁻¹) * (e * v * e⁻¹) by group]
      exact mul_mem (mul_mem (mem_sup_left hc) (mem_sup_right (hE9 _ (inv_mem hc) e he)))
        (mem_sup_right ((mem_normalizer_iff.1 (hE₂U₂ he) _).1 hv))
  have hE₄NU₄ : yamadaE₄ d t ≤ normalizer (yamadaU₄ d t : Set G) :=
    hE₄eq.le.trans (sup_le Subgroup.le_normalizer hE₂NU₄)
  have hE₄NE₂ : yamadaE₄ d t ≤ normalizer (yamadaE₂ d t : Set G) := hE₄R₄.trans hR₄E₂
  have hsqC : ∀ c ∈ yamadaR₄ d t ⊓ centralizer (d.J₆ : Set G), c * c ∈ yamadaU₂ d t :=
    fun c hc => by
      have hcL₄ := (Subgroup.mem_inf.1 (hCJ hc)).1
      exact h.yamadaE₂_inf_centralizer_J₆_le d hK hD (Subgroup.mem_inf.2
        ⟨hL₄C₂ (Subgroup.mem_inf.2 ⟨mul_mem hcL₄ hcL₄, hsqR₄ c (Subgroup.mem_inf.1 hc).1⟩),
          mul_mem (Subgroup.mem_inf.1 hc).2 (Subgroup.mem_inf.1 hc).2⟩)
  obtain ⟨hsqU₄, -⟩ := mul_self_mem_of_sup (N := yamadaU₂ d t) hCU₂
    (sup_le hCU₂ Subgroup.le_normalizer) hsqC (fun b hb => mul_mem hb hb)
    (fun a ha b hb => mul_mem ((mem_normalizer_iff.1 (hCU₂ ha) _).1 hb) (inv_mem hb))
  have hAW : d.rootGroup g2v ≤ d.W := le_sup_left.trans d.yamada_defs.2.2.1.le
  obtain ⟨hsqE₂, -⟩ := mul_self_mem_of_sup (N := yamadaU₂ d t) hAN (hAE.le.trans hE₂U₂)
    (fun a ha => by rw [W_mul_self d (hAW ha)]; exact one_mem _) (fun b hb => mul_mem hb hb)
    (fun a ha b hb => mul_mem ((mem_normalizer_iff.1 (hAN ha) _).1 hb) (inv_mem hb))
  obtain ⟨hsq, hcomm⟩ := mul_self_mem_of_sup (A := yamadaU₄ d t) (B := yamadaE₂ d t)
    (N := yamadaU₂ d t) (hU₄E₄.trans hE₄NE₂) (hE₄eq.ge.trans hE₄U₂) hsqU₄
    (fun e he => hsqE₂ e (hAE.ge he)) (fun x hx e he => by
      rw [← hU₄E₂]
      refine Subgroup.mem_inf.2 ⟨?_, mul_mem ((mem_normalizer_iff.1
        ((hU₄E₄.trans hE₄NE₂) hx) _).1 he) (inv_mem he)⟩
      rw [show x * e * x⁻¹ * e⁻¹ = x * (e * x⁻¹ * e⁻¹) by group]
      exact mul_mem hx ((mem_normalizer_iff.1 (hE₂NU₄ he) _).1 (inv_mem hx)))
  refine ⟨hE₄U₂, hE₄eq, hU₄E₂, hE₄NU₄, hE₄NE₂, fun x hx => hsq x (hE₄eq.le hx),
    fun x hx y hy => hcomm x (hE₄eq.le hx) y (hE₄eq.le hy), ?_⟩
  obtain ⟨htX, htX'⟩ := h.t_mem_normalizer_yamadaX₂ d hK hD
  rw [hcard, show yamadaU₂ d t = yamadaX₂ d t ⊔ zpowers t from rfl, h.card_sup_zpowers htX htX',
    h.card_yamadaX₂ d hK hD]
  ring

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
