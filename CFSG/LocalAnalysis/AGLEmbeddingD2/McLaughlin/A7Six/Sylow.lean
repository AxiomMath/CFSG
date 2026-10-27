module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Offender
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open Equiv Equiv.Perm

variable {X : Type} [Group X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

namespace SixCtx

variable (c : SixCtx T L)

theorem img_mono {A B : Subgroup X} (hAB : A ≤ B) : c.img A ≤ c.img B := by
  rintro _ ⟨⟨a, ha'⟩, ha, rfl⟩
  exact ⟨⟨a, ha'⟩, hAB ha, rfl⟩

variable [Finite X]

theorem exists_swap_mem_img_T (hX : GNSetting X T) (hTL : T ≤ nL T L)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) : ∃ i j : Fin 7, i ≠ j ∧ swap i j ∈ c.img T := by
  by_contra hcon
  push Not at hcon
  have hAbot : ∀ A : Subgroup X, IsMaxElemAbelian T A → c.img A = ⊥ := by
    intro A hA
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    by_contra hσ1
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra h
      push Not at h
      exact hσ1 (Equiv.ext h)
    have h1 := c.swap_mem_theta hX hTL hA hσ hi
    exact hcon i (σ i) hi.symm (c.img_mono hA.1 h1)
  have hJc : ∀ j ∈ thompsonJ T, ∀ l ∈ L, QuotientGroup.mk' (gnC T) j * l *
      (QuotientGroup.mk' (gnC T) j)⁻¹ = l := by
    intro j hj
    have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
    set K : Subgroup X := (c.θ.ker).map (nL T L).subtype with hK
    have hJK : thompsonJ T ≤ K := by
      refine iSup₂_le fun A hA a ha => ?_
      have h1 : c.θ ⟨a, hTL (hA.1 ha)⟩ ∈ c.img A := ⟨⟨a, hTL (hA.1 ha)⟩, ha, rfl⟩
      rw [hAbot A hA, Subgroup.mem_bot] at h1
      exact ⟨⟨a, hTL (hA.1 ha)⟩, h1, rfl⟩
    obtain ⟨⟨g, hg⟩, hg1, hgj⟩ := hJK hj
    simp only [Subgroup.coe_subtype] at hgj
    subst hgj
    exact (c.hθ1 ⟨g, hg⟩).1 hg1
  have hbot : ⁅L, gnImg T (thompsonJ T)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    have := hJc j hj l hl
    calc QuotientGroup.mk' (gnC T) j * l =
        QuotientGroup.mk' (gnC T) j * l * (QuotientGroup.mk' (gnC T) j)⁻¹ *
          QuotientGroup.mk' (gnC T) j := by group
      _ = l * QuotientGroup.mk' (gnC T) j := by rw [this]
  rw [hJ] at hbot
  have h1 : Nat.card ↥L = 1 := by rw [hbot, Subgroup.card_bot]
  have h2 : Nat.card ↥L = 2520 := by
    rw [Nat.card_congr c.eL.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  omega

theorem eight_le_card_img_T_inf (hX : GNSetting X T) (hTL : T ≤ nL T L)
    (hL : IsComponentOf L ⊤) :
    8 ≤ Nat.card (c.img T ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) := by
  classical
  have hSyl := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
    hX.sylow hL.2.1
  have hcardL : Nat.card ↥L = 2520 := by
    rw [Nat.card_congr c.eL.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have h8 : 2 ^ 3 ∣ Nat.card (gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) := by
    have hmul := Subgroup.relIndex_mul_card (gnImg T T ⊓ L) L
    rw [inf_eq_left.mpr hSyl.1, hcardL] at hmul
    have hodd : ¬ 2 ∣ (gnImg T T ⊓ L).relIndex L := hSyl.2.2
    have hcop : Nat.Coprime (2 ^ 3) ((gnImg T T ⊓ L).relIndex L) :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    have h1 : 2 ^ 3 ∣ Nat.card (gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) *
        (gnImg T T ⊓ L).relIndex L := by
      rw [mul_comm, hmul]; norm_num
    exact hcop.dvd_of_dvd_mul_right h1
  have hmem : ∀ y : ↥(gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)),
      ((c.eL ⟨y, y.2.2⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈
        c.img T ⊓ alternatingGroup (Fin 7) := by
    rintro ⟨y, ⟨t, ht, rfl⟩, hy⟩
    refine ⟨⟨⟨t, hTL ht⟩, ht, ?_⟩, (c.eL ⟨_, hy⟩).2⟩
    exact c.hθL ⟨t, hTL ht⟩ ⟨_, hy⟩ rfl
  let f : ↥(gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) →
      ↥(c.img T ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) :=
    fun y => ⟨_, hmem y⟩
  have hf : Function.Injective f := by
    intro y y' h
    have h0 := congrArg Subtype.val h
    have h1 : c.eL ⟨y, y.2.2⟩ = c.eL ⟨y', y'.2.2⟩ := Subtype.ext h0
    have h2 := congrArg Subtype.val (c.eL.injective h1)
    exact Subtype.ext h2
  have hle := Nat.card_le_card_of_injective f hf
  exact (Nat.le_of_dvd Nat.card_pos h8).trans hle

theorem card_img_T (hX : GNSetting X T) (hTL : T ≤ nL T L) (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) : Nat.card (c.img T) = 16 := by
  classical
  set H := c.img T with hH
  have hp : IsPGroup 2 H := by
    have hT : IsPGroup 2 ↥(T.subgroupOf (nL T L)) :=
      IsPGroup.of_equiv hX.sylow.2.1 (Subgroup.subgroupOfEquivOfLe hTL).symm
    exact IsPGroup.map hT c.θ
  obtain ⟨i, j, hij, hsw⟩ := c.exists_swap_mem_img_T hX hTL hJ
  have hrel : (alternatingGroup (Fin 7)).relIndex H = 2 := by
    have hdvd : (alternatingGroup (Fin 7)).relIndex H ∣ 2 := by
      rw [← alternatingGroup.index_eq_two (α := Fin 7)]
      exact Subgroup.relIndex_dvd_index_of_normal (H := alternatingGroup (Fin 7)) (K := H)
    have hne1 : (alternatingGroup (Fin 7)).relIndex H ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro hle
      have := Equiv.Perm.mem_alternatingGroup.mp (hle hsw)
      rw [Equiv.Perm.sign_swap hij] at this
      exact absurd this (by decide)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hmul : (alternatingGroup (Fin 7)).relIndex H *
      Nat.card (alternatingGroup (Fin 7) ⊓ H : Subgroup (Perm (Fin 7))) = Nat.card H :=
    Subgroup.relIndex_mul_card (alternatingGroup (Fin 7)) H
  rw [hrel] at hmul
  have h8 := c.eight_le_card_img_T_inf hX hTL hL
  rw [← hH, inf_comm] at h8
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hdvd : Nat.card H ∣ 5040 := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [Nat.card_perm, Nat.card_fin] at this
  rw [hk] at hdvd hmul
  have hk4 : k ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 5 ∣ 5040 := (Nat.pow_dvd_pow 2 hlt).trans hdvd
    exact absurd this (by decide)
  have hk4' : 4 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hk, show k = 4 by omega]
  rfl

theorem map_conj_alternatingGroup (σ : Perm (Fin 7)) :
    (alternatingGroup (Fin 7)).map (MulAut.conj σ).toMonoidHom = alternatingGroup (Fin 7) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup] at hy ⊢
    simp [MulAut.conj_apply, hy]
  · intro hx
    refine ⟨σ⁻¹ * x * σ, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup] at hx ⊢
      simp [hx]
    · simp [MulAut.conj_apply]; group

end SixCtx

@[expose] def conjA7 (σ : Perm (Fin 7)) : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) :=
  ((MulAut.conj σ).subgroupMap (alternatingGroup (Fin 7))).trans
    (MulEquiv.subgroupCongr (SixCtx.map_conj_alternatingGroup σ))

theorem coe_conjA7 (σ : Perm (Fin 7)) (x : alternatingGroup (Fin 7)) :
    ((conjA7 σ x : alternatingGroup (Fin 7)) : Perm (Fin 7)) = σ * x * σ⁻¹ := rfl

namespace SixCtx

@[expose] noncomputable def conj (c : SixCtx T L) (σ : Perm (Fin 7)) : SixCtx T L where
  eL := c.eL.trans (conjA7 σ)
  θs := (MulAut.conj σ).toMonoidHom.comp c.θs
  hθs := by
    intro y l l' h
    simp only [MulEquiv.trans_apply, coe_conjA7, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [c.hθs y l l' h]
    group
  hθsL := by
    intro y l h
    simp only [MulEquiv.trans_apply, coe_conjA7, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [c.hθsL y l h]
  hθs1 := by
    intro y
    rw [← c.hθs1 y]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro h
      calc c.θs y = σ⁻¹ * (σ * c.θs y * σ⁻¹) * σ := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  φ := (AddMonoidHom.toMultiplicative (altAct σ)).comp c.φ
  hφ := by
    show Function.Bijective (⇑(AddMonoidHom.toMultiplicative (altAct σ)) ∘ ⇑c.φ)
    refine Function.Bijective.comp ⟨fun x y h => ?_, fun x => ?_⟩ c.hφ
    · change Multiplicative.ofAdd (altAct σ (Multiplicative.toAdd x)) =
        Multiplicative.ofAdd (altAct σ (Multiplicative.toAdd y)) at h
      have h1 := congrArg (fun z => altAct σ⁻¹ (Multiplicative.toAdd z)) h
      simp only [toAdd_ofAdd, altAct_inv_apply] at h1
      exact Multiplicative.toAdd.injective h1
    · refine ⟨Multiplicative.ofAdd (altAct σ⁻¹ (Multiplicative.toAdd x)), ?_⟩
      change Multiplicative.ofAdd (altAct σ (Multiplicative.toAdd
        (Multiplicative.ofAdd (altAct σ⁻¹ (Multiplicative.toAdd x))))) = x
      rw [toAdd_ofAdd, altAct_apply_inv, ofAdd_toAdd]
  hφe := by
    intro g u v h
    change altAct σ (Multiplicative.toAdd (c.φ v)) =
      altAct (σ * c.θs (πN T L g) * σ⁻¹) (altAct σ (Multiplicative.toAdd (c.φ u)))
    rw [c.hφe g u v h, altAct_mul, altAct_mul, altAct_inv_apply]

theorem conj_θ (c : SixCtx T L) (σ : Perm (Fin 7)) (g : ↥(nL T L)) :
    (c.conj σ).θ g = σ * c.θ g * σ⁻¹ := rfl

theorem img_conj (c : SixCtx T L) (σ : Perm (Fin 7)) (A : Subgroup X) :
    (c.conj σ).img A = (c.img A).map (MulAut.conj σ).toMonoidHom := by
  rw [SixCtx.img, SixCtx.img, Subgroup.map_map]
  rfl

theorem exists_conj_img_T [Finite X] (c : SixCtx T L) (hX : GNSetting X T) (hTL : T ≤ nL T L)
    (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    {D : Subgroup (Perm (Fin 7))} (hD : Nat.card D = 16) :
    ∃ σ : Perm (Fin 7), (c.conj σ).img T = D := by
  have h2 : (Nat.card (Perm (Fin 7))).factorization 2 = 4 := by
    rw [Nat.card_perm, Nat.card_fin, Nat.factorization_def _ Nat.prime_two]
    have : Nat.factorial 7 = 2 ^ 4 * 315 := by decide
    rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
    simp [padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 315 by decide)]
  have hP : Nat.card (c.img T) = 2 ^ (Nat.card (Perm (Fin 7))).factorization 2 := by
    rw [h2, c.card_img_T hX hTL hL hJ]; norm_num
  have hQ : Nat.card D = 2 ^ (Nat.card (Perm (Fin 7))).factorization 2 := by
    rw [h2, hD]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Perm (Fin 7))
    (Sylow.ofCard (c.img T) hP) (Sylow.ofCard D hQ)
  refine ⟨σ, ?_⟩
  have h3 := congrArg (fun P : Sylow 2 (Perm (Fin 7)) => (P : Subgroup (Perm (Fin 7)))) hσ
  simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at h3
  rw [img_conj, ← h3]
  rfl

end SixCtx

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
