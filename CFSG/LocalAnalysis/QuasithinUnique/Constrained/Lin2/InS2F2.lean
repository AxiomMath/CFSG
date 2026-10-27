module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2E1

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

structure S2Ok (T M H S L D : Subgroup G) (n : ℕ) (t : G) (M₀ : Subgroup G) (x : G) (q : ℕ)
    (W : Subgroup G) (D₁ D₂ : Subgroup G) : Prop where
  base : S2Base T M H S L D n t M₀ x q W
  hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n
  hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n
  hD : D = D₁ ⊔ D₂
  hC : baumD S L = ⊥
  hDx : conjR D x = D

theorem S2Base.exists_ok (B : S2Base T M H S L D n t M₀ x₀ q W) (h246 : Lemma246Double) :
    ∃ (y : G) (D₁ D₂ : Subgroup G), S2Ok T M H S L D n t M₀ y q W D₁ D₂ := by
  obtain ⟨y, D₁, D₂, By, hT₁, hT₂, hD, hDy⟩ := B.exists_good_normalizing h246
  exact ⟨y, D₁, D₂, ⟨By, hT₁, hT₂, hD, By.C_eq_bot hT₁ hT₂ hD hDy, hDy⟩⟩

namespace S2Ok

variable {D₁ D₂ : Subgroup G} (O : S2Ok T M H S L D n t M₀ x₀ q W D₁ D₂)
include O

theorem conjR_R₁ : conjR (thompsonJ S ⊓ L) x₀ = thompsonJ S ⊓ L :=
  O.base.conjR_R₁ O.hT₁ O.hT₂ O.hD O.hC O.hDx

theorem conjR_R₂ : conjR (thompsonJ S ⊓ conjR L t) x₀ = thompsonJ S ⊓ conjR L t :=
  O.base.conjR_R₂ O.hT₁ O.hT₂ O.hD O.hC O.hDx

theorem x_mem_S₁ : x₀ ∈ s2S₁ M₀ S L := O.base.x₀_mem_S₁ O.hT₁ O.hT₂ O.hD O.hC O.hDx

theorem conj_mem_R1_iff {s : G} (hs : s ∈ S) :
    x₀ * s * x₀⁻¹ ∈ AppE.R1 S L ↔ s ∈ AppE.R1 S L := by
  have hxS : x₀ * s * x₀⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 O.base.su.hxN s).1 hs
  constructor
  · intro h
    have h1 : x₀ * s * x₀⁻¹ ∈ s2S₁ M₀ S L := by
      rw [← O.base.S_inf_S₁] at h
      exact h.2
    have h2 : s ∈ s2S₁ M₀ S L := by
      have := (s2S₁ M₀ S L).mul_mem ((s2S₁ M₀ S L).mul_mem ((s2S₁ M₀ S L).inv_mem O.x_mem_S₁) h1)
        O.x_mem_S₁
      simpa [mul_assoc] using this
    rw [← O.base.S_inf_S₁]
    exact ⟨hs, h2⟩
  · intro h
    have h1 : s ∈ s2S₁ M₀ S L := O.base.R1_le_S₁ h
    have h2 : x₀ * s * x₀⁻¹ ∈ s2S₁ M₀ S L :=
      (s2S₁ M₀ S L).mul_mem ((s2S₁ M₀ S L).mul_mem O.x_mem_S₁ h1) ((s2S₁ M₀ S L).inv_mem O.x_mem_S₁)
    rw [← O.base.S_inf_S₁]
    exact ⟨hxS, h2⟩

theorem comm_x_t_mem_R1 : x₀ * t * x₀⁻¹ * t⁻¹ ∈ AppE.R1 S L := by
  have hB := O.base
  have ht : t ∈ S := hB.ht
  have htn : t ∉ AppE.R1 S L := fun h => hB.hne (AppE.mem_R1_iff.1 h).2
  have hxt : x₀ * t * x₀⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hB.su.hxN t).1 ht
  have hxtn : x₀ * t * x₀⁻¹ ∉ AppE.R1 S L := fun h => htn ((O.conj_mem_R1_iff ht).1 h)
  have := CFSG.QuasithinUnique.inv_mul_mem_of_relIndex_two hB.dbl.relIndex_R1 (S.inv_mem hxt)
    (fun h => hxtn (by simpa using (AppE.R1 S L).inv_mem h)) (S.inv_mem ht)
    (fun h => htn (by simpa using (AppE.R1 S L).inv_mem h))
  simpa using this

theorem conjR_conjR_x_t :
    conjR (conjR (blockU L) x₀) t = conjR (blockU (conjR L t)) x₀ := by
  rw [DoubleA3.blockU_conjR, conjR_conjR, conjR_conjR]
  have hc := O.comm_x_t_mem_R1
  have hcN : x₀ * t * x₀⁻¹ * t⁻¹ ∈ Subgroup.normalizer (blockU L : Set G) :=
    mem_normalizer_blockU_of (conjR_eq_self_iff.1 (AppE.mem_R1_iff.1 hc).2)
  have e : x₀ * t = (x₀ * t * x₀⁻¹ * t⁻¹) * (t * x₀) := by group
  rw [e, ← conjR_conjR, conjR_eq_of_mem_normalizer hcN]

theorem UT3_R₁ : UT3 (thompsonJ S ⊓ L) (blockU L) (conjR (blockU L) x₀) W q := by
  have hB := O.base
  have kf := hB.su.kf₁
  have rk := hB.su.loc.rk
  have hxN : x₀ ∈ Subgroup.normalizer (baum S : Set G) := hB.su.hxB
  have hR₁ := O.conjR_R₁
  have hZ : blockU L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := hB.blockZ_eq_bot O.hC
  have hUR₁ : blockU L ≤ thompsonJ S ⊓ L := le_inf hB.U₁_le_R (blockU_le L)
  have hU'R₁ : conjR (blockU L) x₀ ≤ thompsonJ S ⊓ L := (conjR_mono hUR₁ x₀).trans hR₁.le
  have hcard_U : Nat.card (blockU L) = q ^ 2 := by
    have h1 := hB.su.loc.hZ
    rw [hZ, Subgroup.relIndex_bot_left] at h1
    exact h1
  refine ⟨?_, ?_, ?_, kf.infU, ?_, ?_, hcard_U, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rintro r ⟨hrR, hrL⟩
      have hrB : r ∈ baum S := by rw [hB.baum_eq]; exact hrR
      rw [← kf.supQ] at hrB
      have hNQ : (baum S ⊓ Subgroup.centralizer (blockU L : Set G)) ≤
          Subgroup.normalizer ((conjSubgroup (blockU L) x₀ : Subgroup G) : Set G) :=
        inf_le_left.trans (rk.B_le_normU_conj hxN)
      obtain ⟨u', hu', q', hq', hr⟩ := (mem_sup_iff_of_le_normalizer hNQ).1 hrB
      have hu'L : u' ∈ L := (hU'R₁ hu').2
      have hq'L : q' ∈ L := by
        have : u'⁻¹ * r ∈ L := L.mul_mem (L.inv_mem hu'L) hrL
        rw [hr] at this
        simpa using this
      have hq'' : q' ∈ blockU L ⊔ ((baum S ⊓ Subgroup.centralizer (blockU L : Set G)) ⊓
          Subgroup.centralizer (L : Set G)) := kf.Q_eq ▸ hq'
      have hNE : ((baum S ⊓ Subgroup.centralizer (blockU L : Set G)) ⊓
          Subgroup.centralizer (L : Set G)) ≤ Subgroup.normalizer (blockU L : Set G) := by
        refine le_normalizer_of_commute fun a ha b hb => ?_
        exact Subgroup.mem_centralizer_iff.1 hb.2 a (blockU_le L ha)
      obtain ⟨u, hu, c, hc, hq⟩ := (mem_sup_iff_of_le_normalizer hNE).1 hq''
      have hcL : c ∈ L := by
        have : u⁻¹ * q' ∈ L := L.mul_mem (L.inv_mem (blockU_le L hu)) hq'L
        rw [hq] at this
        simpa using this
      have hcZ : c ∈ centerOf L := ⟨hcL, hc.2⟩
      rw [← blockZ_eq_centerOf hB.hL.2.1 hB.pCore_L, hB.blockZ_eq_bot O.hC] at hcZ
      have hc1 : c = 1 := Subgroup.mem_bot.1 hcZ
      rw [hr, hq, hc1, mul_one]
      exact (blockU L ⊔ conjR (blockU L) x₀).mul_mem (Subgroup.mem_sup_right hu')
        (Subgroup.mem_sup_left hu)
    · exact sup_le hUR₁ hU'R₁
  · intro a ha
    have := C1.blockU_sq hB.hL a ha
    rwa [pow_two] at this
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_conjR_iff'.1 ha
    have hbb : b * b = 1 := by
      have := C1.blockU_sq hB.hL b hb
      rwa [pow_two] at this
    calc x₀⁻¹ * b * x₀ * (x₀⁻¹ * b * x₀) = x₀⁻¹ * (b * b) * x₀ := by group
      _ = 1 := by rw [hbb]; group
  · intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ ⁅blockU L, conjSubgroup (blockU L) x₀⁆ :=
      Subgroup.commutator_mem_commutator ha hb
    rw [kf.commU] at h1
    simpa [commutatorElement_def] using h1
  · intro b hb hbW a ha hab
    have hbQ : b ∉ baum S ⊓ Subgroup.centralizer (blockU L : Set G) := fun hh =>
      hbW (kf.infQ ▸ ⟨hb, hh⟩)
    exact (rk.cent_y b (kf.Ux_le_B hb) hbQ a ha).mpr hab
  · exact (card_conjR _ _).trans hcard_U
  · have h1 := C5.card_eq_card_mul_relIndex rk.W_le_U
    rw [rk.idx_W, hcard_U] at h1
    have hq : 0 < q := lt_of_lt_of_le (by norm_num) hB.su.loc.q2
    have : q * Nat.card W = q * q := by rw [mul_comm, ← h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hq this
  · exact lt_of_lt_of_le (by norm_num) hB.su.loc.q2

theorem UT3_R₂ : UT3 (thompsonJ S ⊓ conjR L t) (blockU (conjR L t))
    (conjR (blockU (conjR L t)) x₀) (conjR W t) q := by
  have h := O.UT3_R₁.conj t
  have e1 : conjR (thompsonJ S ⊓ L) t = thompsonJ S ⊓ conjR L t := by
    rw [conjR_inf, thompsonJ_normalized (Subgroup.le_normalizer O.base.ht)]
  have e2 : conjR (blockU L) t = blockU (conjR L t) := (DoubleA3.blockU_conjR L t).symm
  rw [e1, O.conjR_conjR_x_t, e2] at h
  exact h

end S2Ok

end CFSG.QuasithinUnique.Lin2
