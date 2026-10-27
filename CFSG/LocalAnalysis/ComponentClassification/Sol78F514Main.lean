module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Y
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Fin
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Iso
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514L0
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514T3

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5 CFSG.GH74.GLS.Stage1.Thm6.Sec12b
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.Asc76
  CFSG.Open CFSG.ComponentClassification.RankTwoSporadic

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem conj_t_eq_of_mem_R {x : G} (hx : x ∈ centralizer ({z * t} : Set G))
    (hxR : x⁻¹ * t * x ∈ S ⊓ L) : x⁻¹ * t * x = t := by
  have hxd : x⁻¹ * (z * t) * x = z * t := by
    have h1 := mem_centralizer_singleton_iff.mp hx
    calc x⁻¹ * (z * t) * x = x⁻¹ * (x * (z * t)) := by rw [h1]; group
      _ = z * t := by group
  have hzx : x⁻¹ * z * x = z * t * (x⁻¹ * t * x) := by
    calc x⁻¹ * z * x = x⁻¹ * (z * t) * x * (x⁻¹ * t * x) := by
          rw [show x⁻¹ * (z * t) * x * (x⁻¹ * t * x) = x⁻¹ * z * (t * t) * x by group,
            H.mul_self_t, mul_one]
      _ = z * t * (x⁻¹ * t * x) := by rw [hxd]
  have hmem : x⁻¹ * z * x ∈ S ⊓ L ⊔ conjugate (S ⊓ L) s := by
    rw [hzx]
    exact mul_mem (mul_mem (mem_sup_right H.z_mem_Rs) (mem_sup_left H.sec5.tR)) (mem_sup_left hxR)
  rcases H.conj_z_eq_of_mem_sup hx hmem with h1 | h1
  · rw [hzx] at h1
    calc x⁻¹ * t * x = (z * t)⁻¹ * (z * t * (x⁻¹ * t * x)) := by group
      _ = t := by rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right H.mul_self_t,
            inv_eq_of_mul_eq_one_right H.mul_self_z, mul_assoc, H.mul_self_z, mul_one]
  · exfalso
    rw [hzx] at h1
    have h2 : x⁻¹ * t * x = z := by
      calc x⁻¹ * t * x = (z * t)⁻¹ * (z * t * (x⁻¹ * t * x)) := by group
        _ = z := by rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right H.mul_self_t,
              inv_eq_of_mul_eq_one_right H.mul_self_z, ← H.z_mul_t, mul_assoc, H.mul_self_t,
              mul_one]
    have h4 : z ∈ S ⊓ L ⊓ conjugate (S ⊓ L) s := mem_inf.mpr ⟨h2 ▸ hxR, H.z_mem_Rs⟩
    rw [H.R_inf_Rs, mem_bot] at h4
    exact H.z_ne_one h4

theorem conj_z_of_mem_T {x : G} (hxT : x ∈ T) : x⁻¹ * z * x = z ∨ x⁻¹ * z * x = t := by
  by_cases hxS : x ∈ S
  · left
    have h1 := H.sec5.zS x hxS
    calc x⁻¹ * z * x = x⁻¹ * (x * z) := by rw [mul_assoc, ← h1]
      _ = z := by group
  · right
    have hw := H.mul_s_mem_of_not_mem hxT hxS
    have h1 := H.sec5.zS _ hw
    calc x⁻¹ * z * x = s * ((x * s)⁻¹ * z * (x * s)) * s⁻¹ := by group
      _ = s * ((x * s)⁻¹ * ((x * s) * z)) * s⁻¹ := by rw [mul_assoc _ z, ← h1]
      _ = s * z * s⁻¹ := by group
      _ = t := H.conj_s_z

theorem centralizer_d_inf_t :
    centralizer ({z * t} : Set G) ⊓ centralizer ({t} : Set G) =
      centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) := by
  ext x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    calc x * z = x * (z * t) * t := by rw [mul_assoc x, mul_assoc z, H.mul_self_t, mul_one]
      _ = z * t * x * t := by rw [h1]
      _ = z * t * (t * x) := by rw [mul_assoc (z * t), h2]
      _ = z * x := by rw [mul_assoc z, ← mul_assoc t, H.mul_self_t, one_mul]
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc], h2⟩

theorem actG_mem_Lin_of_mem_R {r : G} (hr : r ∈ S ⊓ L) : actG L ε r ∈ Lin := by
  rw [actG_of_mem_self ε (mem_inf.mp hr).2]
  exact H.autData.inn_le ⟨_, rfl⟩

theorem actG_mul_not_mem {r f : G} (hr : r ∈ S ⊓ L) (hfS : f ∈ S) (hf : actG L ε f ∉ Lin) :
    actG L ε (r * f) ∉ Lin := by
  intro h1
  apply hf
  have hrN := H.sec5.S_le (mem_inf.mp hr).1
  have hfN := H.sec5.S_le hfS
  rw [actG_mul ε hrN hfN] at h1
  have h2 : actG L ε f = (actG L ε r)⁻¹ * (actG L ε r * actG L ε f) := by group
  rw [h2]
  exact mul_mem (inv_mem (H.actG_mem_Lin_of_mem_R hr)) h1

theorem false_of_pgl (h3 : Asc76Theorem3Large) {h : G} (hhC : h ∈ centralizer ({z * t} : Set G))
    (hhT : h⁻¹ * z * h ∈ T) (hhz : h⁻¹ * z * h ≠ z) (hht : h⁻¹ * z * h ≠ t) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hyS, -, -⟩ := H.pgl_of_conj hhC hhT hhz hht
  have hy2 := H.conj_z_mul_self h
  have hfix := H.fix_R_of_conj hhC hhT hhz hht
  have hfixs := H.fix_Rs_of_conj hhC hhT hhz hht
  obtain ⟨E, hES, hTE, hE2, hE8, htE, -⟩ := H.e8
  obtain ⟨f, hfS, hf2, hflin, hfR, hfRs⟩ :=
    H.exists_field_centralizing hyS hy2 hfix hfixs hES hTE hE2 htE hE8
  obtain ⟨b₀, hb₀R, hb₀2, hb₀1, hb₀t, hcls₀⟩ := H.exists_conj_refl_R hyS hy2 hfix
  obtain ⟨ρ, b, j, hD, -⟩ := H.exists_dihData_R
  set C := centralizer ({z * t} : Set G) with hC
  have hSC : S ≤ C := H.sec5.ST.trans H.T_le_centralizer_d
  have hRC : S ⊓ L ≤ C := inf_le_left.trans hSC
  have hdC : z * t ∈ C := mem_centralizer_singleton_iff.mpr rfl
  set t' : C := ⟨t, hSC H.sec5.tS⟩ with ht'
  set z' : C := ⟨z, hSC H.sec5.zS_mem⟩ with hz'
  set f' : C := ⟨f, hSC hfS⟩ with hf'
  set d' : C := ⟨z * t, hdC⟩ with hd'
  set h' : C := ⟨h, hhC⟩ with hh'
  set b₀' : C := ⟨b₀, hRC hb₀R⟩ with hb₀'
  set R' := (S ⊓ L).subgroupOf C with hR'
  have hmemR : ∀ x : C, x ∈ R' ↔ (x : G) ∈ S ⊓ L := fun x => mem_subgroupOf
  have ht2 : t' * t' = 1 := Subtype.ext H.mul_self_t
  have ht1 : t' ≠ 1 := fun e => H.t_ne_one (congrArg Subtype.val e)
  have htR : t' ∈ R' := H.sec5.tR
  have htc : ∀ r ∈ R', r * t' = t' * r := fun r hr =>
    Subtype.ext (H.sec5.tZ r (mem_inf.mp ((hmemR r).mp hr)).1)
  have hf2' : f' * f' = 1 := Subtype.ext hf2
  have hfc : ∀ r ∈ R', r * f' = f' * r := fun r hr => Subtype.ext (hfR r ((hmemR r).mp hr)).symm
  have hfR' : f' ∉ R' := fun hf => hflin (H.actG_mem_Lin_of_mem_R hf)
  have hsR : ∀ r ∈ R', r * r = 1 → r ≠ 1 → Group.IsSolvable ↥(centralizer ({r} : Set C)) := by
    intro r hr hr2 hr1
    apply isSolvable_centralizer_of_inf
    have hrR := (hmemR r).mp hr
    have hr2' : (r : G) * r = 1 := congrArg Subtype.val hr2
    have hr1' : (r : G) ≠ 1 := fun e => hr1 (Subtype.ext e)
    by_cases hrt : (r : G) = t
    · have h1 := H.isSolvable_CZ
      rw [← H.centralizer_d_inf_t] at h1
      rw [hrt]
      exact h1
    · exact H.isSolvable_CH (mem_inf.mp hrR).1 hr2' hr1' (fun r' hr' => H.commute_R_Rs hrR hr')
        (Or.inl ⟨hrR, hrt⟩)
  have hsF : ∀ r ∈ R', r * r = 1 → Group.IsSolvable ↥(centralizer ({r * f'} : Set C)) := by
    intro r hr hr2
    apply isSolvable_centralizer_of_inf
    have hrR := (hmemR r).mp hr
    have hr2' : (r : G) * r = 1 := congrArg Subtype.val hr2
    have hrf : (r : G) * f = f * r := (hfR r hrR).symm
    have hlin := H.actG_mul_not_mem hrR hfS hflin
    exact H.isSolvable_CH (mul_mem (mem_inf.mp hrR).1 hfS)
      (by
        calc (r : G) * f * (r * f) = r * (f * r) * f := by group
          _ = 1 := by rw [← hrf, ← mul_assoc, hr2', one_mul, hf2])
      (fun e => hlin (by rw [show (r : G) * f = 1 from e, actG_one]; exact one_mem _))
      (fun r' hr' => by
        calc (r : G) * f * r' = r * (f * r') := by group
          _ = r * (r' * f) := by rw [hfRs r' hr']
          _ = (r * r') * f := by group
          _ = (r' * r) * f := by rw [H.commute_R_Rs hrR hr']
          _ = r' * (r * f) := by group)
      (Or.inr hlin)
  have hcen : ∀ r ∈ R', (∀ s' ∈ R', r * s' = s' * r) → r * r = 1 → r ≠ 1 → r = t' := by
    intro r hr hrc _ hr1
    rcases H.sec5.center_R H.nonab ((hmemR r).mp hr)
        (fun r' hr' => congrArg Subtype.val (hrc ⟨r', hRC hr'⟩ hr')) with e | e
    · exact absurd (Subtype.ext e) hr1
    · exact Subtype.ext e
  have hgen : ∀ r ∈ R', ∃ c₁ ∈ R', ∃ c₂ ∈ R', c₁ * c₁ = 1 ∧ c₂ * c₂ = 1 ∧ r = c₁ * c₂ := by
    intro r hr
    obtain ⟨c₁, hc₁, c₂, hc₂, h1, h2, he⟩ := hD.prod_inv _ ((hmemR r).mp hr)
    exact ⟨⟨c₁, hRC hc₁⟩, hc₁, ⟨c₂, hRC hc₂⟩, hc₂, Subtype.ext h1, Subtype.ext h2, Subtype.ext he⟩
  have hb₀R' : b₀' ∈ R' := hb₀R
  have hb₀2' : b₀' * b₀' = 1 := Subtype.ext hb₀2
  have hb₀1' : b₀' ≠ 1 := fun e => hb₀1 (congrArg Subtype.val e)
  have hb₀t' : b₀' ≠ t' := fun e => hb₀t (congrArg Subtype.val e)
  obtain ⟨hWodd, -, -⟩ :=
    sigW_spec ht2 ht1 htR htc hf2' hfc hfR' hsR hsF hb₀R' hb₀2' hb₀1' hb₀t'
  have hRW : R' ≤ normalizer (sigW t' f' : Set C) :=
    le_normalizer_sigW ht2 ht1 htR htc hf2' hfc hfR' hsR hsF hgen
  have hNRW : normalizer (R' : Set C) ≤ normalizer (sigW t' f' : Set C) :=
    normalizer_le_normalizer_sigW ht2 ht1 htR htc hf2' hfc hfR' hsR hsF hcen hb₀R' hb₀2' hb₀1'
      hb₀t'
  have hθW : ∀ b' ∈ R', b' * b' = 1 → b' ≠ 1 → b' ≠ t' →
      oddCoreOfCentralizer b' ≤ sigW t' f' := fun b' hb'R hb'2 hb'1 hb't =>
    le_sup_right.trans (sigW_spec ht2 ht1 htR htc hf2' hfc hfR' hsR hsF hb'R hb'2 hb'1 hb't).2.1.ge
  have hθt : oddCoreOfCentralizer t' ≤ sigW t' f' := le_sup_right.trans le_sup_left
  set K := R' ⊔ sigW t' f' with hK
  have hR2 : IsPGroup 2 R' := H.sec5.R_sylow.isPGroup.of_equiv (subgroupOfEquivOfLe hRC).symm
  have hdisj : Disjoint (sigW t' f') R' := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    exact mem_bot.mpr (eq_one_of_mem_isPGroup_of_mem_odd hR2 hWodd (mem_inf.mp hx).2
      (mem_inf.mp hx).1)
  have hcardK : Nat.card K = Nat.card (sigW t' f') * Nat.card R' := by
    rw [hK, sup_comm]
    exact GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hRW hdisj
  have hRK : IsSylowOf 2 R' K := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_left, hR2, fun h2 => ?_⟩
    have h1 := Subgroup.relIndex_mul_card R' K
    rw [inf_eq_left.mpr (le_sup_left : R' ≤ K), hcardK] at h1
    have h3 : R'.relIndex K = Nat.card (sigW t' f') :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    rw [h3] at h2
    exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr h2)
  obtain ⟨NL, hNL, hNLodd, hNLn, hL₀⟩ := H.exists_normal_complement_L₀
  have hLC : L ⊓ centralizer ({t} : Set G) ≤ C := fun x hx => by
    have hxz := mem_centralizer_singleton_iff.mp (H.sec5.zL.2.1 (mem_inf.mp hx).1)
    have hxt := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
    exact mem_centralizer_singleton_iff.mpr (by
      rw [← mul_assoc, hxz, mul_assoc, hxt, ← mul_assoc])
  have hNLC : NL ≤ C := hNL.trans hLC
  have hCt : ∀ x : C, x ∈ centralizer ({t'} : Set C) →
      (x : G) ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) := by
    intro x hx
    have hxt : (x : G) * t = t * x := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)
    rw [← H.centralizer_d_inf_t]
    exact mem_inf.mpr ⟨x.2, mem_centralizer_singleton_iff.mpr hxt⟩
  have hRsyl' : IsSylowOf 2 R' ((L ⊓ centralizer ({t} : Set G)).subgroupOf C) :=
    (Asc76.Sec5.isSylowOf_subgroupOf_iff hRC hLC).mpr
      (H.sec5.R_sylow.of_le H.R_le_L₀ inf_le_left)
  have hL₀' : (L ⊓ centralizer ({t} : Set G)).subgroupOf C ≤ NL.subgroupOf C ⊔ R' := by
    rw [hR', ← Subgroup.subgroupOf_sup hNLC hRC]
    exact fun x hx => hL₀ hx
  have hN₀θ : NL.subgroupOf C ≤ oddCoreOfCentralizer t' := by
    refine le_oddCoreOfCentralizer_of_normal (fun x hx => ?_) (fun c hc n hn => ?_) ?_
    · exact mem_centralizer_singleton_iff.mpr (Subtype.ext
        (mem_centralizer_singleton_iff.mp (mem_inf.mp (hNL hx)).2))
    · exact hNLn _ (hCt c hc) _ hn
    · rw [Nat.card_congr (subgroupOfEquivOfLe hNLC).toEquiv]
      exact hNLodd
  have hCL : centralizer ({t'} : Set C) ≤
      normalizer (((L ⊓ centralizer ({t} : Set G)).subgroupOf C : Subgroup C) : Set C) := by
    intro x hx
    obtain ⟨hxz, hxt⟩ := mem_inf.mp (hCt x hx)
    have hxN := H.sec5.centralizer_le_normalizer hxz
    rw [Asc76.Sec5.mem_normalizer_subgroupOf_iff hLC, mem_normalizer_iff]
    intro y
    rw [mem_inf, mem_inf]
    exact and_congr (mem_normalizer_iff.mp hxN y) (mem_normalizer_iff.mp (le_normalizer hxt) y)
  have hCtK : centralizer ({t'} : Set C) ≤ normalizer (K : Set C) :=
    le_normalizer_sup_of_sylow hRsyl' hL₀' (hN₀θ.trans hθt) hCL hNRW
  have hCzK : ∀ x : C, x * z' = z' * x → x ∈ normalizer (K : Set C) := by
    intro x hx
    apply hCtK
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have h1 : (x : G) * z = z * x := congrArg Subtype.val hx
    have h2 : (x : G) * (z * t) = z * t * x := mem_centralizer_singleton_iff.mp x.2
    change (x : G) * t = t * x
    calc (x : G) * t = x * (z * (z * t)) := by rw [← mul_assoc z, H.mul_self_z, one_mul]
      _ = z * (x * (z * t)) := by rw [← mul_assoc, h1, mul_assoc]
      _ = z * (z * t * x) := by rw [h2]
      _ = t * x := by rw [← mul_assoc, ← mul_assoc, H.mul_self_z, one_mul]
  have hCbK : ∀ (b : G) (hbR : b ∈ S ⊓ L), b * b = 1 → b ≠ 1 → b ≠ t →
      centralizer ({(⟨b, hRC hbR⟩ : C)} : Set C) ≤ normalizer (K : Set C) := by
    intro b hbR hb2 hb1 hbt
    obtain ⟨g, hgC, hgz, hgS, P, hP, hcl⟩ := H.exists_conj_strongly_closed (mem_inf.mp hbR).1 hb2
      hb1 (fun r hr => H.commute_R_Rs hbR hr) (Or.inl ⟨hbR, hbt⟩)
    have hgz' : g * z = z * g := by
      calc g * z = g * (g⁻¹ * z * g) := by rw [hgz]
        _ = z * g := by group
    have hgN := H.sec5.centralizer_le_normalizer (mem_centralizer_singleton_iff.mpr hgz')
    have ha'R : g⁻¹ * b * g ∈ S ⊓ L :=
      mem_inf.mpr ⟨hgS, Foote5.conj_mem_of_mem_normalizer hgN (mem_inf.mp hbR).2⟩
    have ha'1 : g⁻¹ * b * g ≠ 1 := fun e => hb1 (by
      calc b = g * (g⁻¹ * b * g) * g⁻¹ := by group
        _ = 1 := by rw [e]; group)
    have hgt : g⁻¹ * t * g = t := by
      have h1 : g⁻¹ * (z * t) * g = z * t := by
        calc g⁻¹ * (z * t) * g = g⁻¹ * (g * (z * t)) := by
              rw [mem_centralizer_singleton_iff.mp hgC]; group
          _ = z * t := by group
      calc g⁻¹ * t * g = (g⁻¹ * z * g)⁻¹ * (g⁻¹ * (z * t) * g) := by group
        _ = t := by rw [hgz, h1, ← mul_assoc, inv_mul_cancel, one_mul]
    have ha't : g⁻¹ * b * g ≠ t := fun e => hbt (by
      calc b = g * (g⁻¹ * b * g) * g⁻¹ := by group
        _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [e, hgt]
        _ = t := by group)
    obtain ⟨N, hNX, hNn, hNodd, hcov⟩ := H.exists_odd_mul_centralizer ha'R ha'1 hP hcl
    set a'' : C := ⟨g⁻¹ * b * g, hRC ha'R⟩ with ha''
    have hNC : N ≤ C := hNX.trans inf_le_left
    have hN' : N.subgroupOf C ≤ oddCoreOfCentralizer a'' := by
      refine le_oddCoreOfCentralizer_of_normal (fun x hx => ?_) (fun c hc n hn => ?_) ?_
      · exact mem_centralizer_singleton_iff.mpr (Subtype.ext
          (mem_centralizer_singleton_iff.mp (mem_inf.mp (hNX hx)).2))
      · exact hNn _ (mem_inf.mpr ⟨c.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))⟩) _ hn
      · rw [Nat.card_congr (subgroupOfEquivOfLe hNC).toEquiv]
        exact hNodd
    have hθ := hθW a'' ha'R (Subtype.ext (by
      change g⁻¹ * b * g * (g⁻¹ * b * g) = 1
      rw [show g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g by group, hb2]; group))
      (fun e => ha'1 (congrArg Subtype.val e)) (fun e => ha't (congrArg Subtype.val e))
    have hCa : centralizer ({a''} : Set C) ≤ normalizer (K : Set C) := by
      intro x hx
      have hxX : (x : G) ∈ C ⊓ centralizer ({g⁻¹ * b * g} : Set G) :=
        mem_inf.mpr ⟨x.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))⟩
      obtain ⟨k, hkN, hkz⟩ := hcov x hxX
      set k' : C := ⟨k, hNC hkN⟩ with hk'
      have hk'K : k' ∈ normalizer (K : Set C) := le_normalizer (mem_sup_right (hθ (hN' hkN)))
      have hk'x : k'⁻¹ * x ∈ normalizer (K : Set C) := hCzK _ (Subtype.ext hkz)
      rw [show x = k' * (k'⁻¹ * x) by group]
      exact mul_mem hk'K hk'x
    set g' : C := ⟨g, hgC⟩ with hg'
    have hg'K : g' ∈ normalizer (K : Set C) := hCzK g' (Subtype.ext hgz')
    intro x hx
    have hxb : (x : G) * b = b * x := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)
    have h1 : g'⁻¹ * x * g' ∈ centralizer ({a''} : Set C) := by
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      change g⁻¹ * x * g * (g⁻¹ * b * g) = g⁻¹ * b * g * (g⁻¹ * x * g)
      calc g⁻¹ * x * g * (g⁻¹ * b * g) = g⁻¹ * (x * b) * g := by group
        _ = g⁻¹ * (b * x) * g := by rw [hxb]
        _ = g⁻¹ * b * g * (g⁻¹ * x * g) := by group
    rw [show x = g' * (g'⁻¹ * x * g') * g'⁻¹ by group]
    exact mul_mem (mul_mem hg'K (hCa h1)) (inv_mem hg'K)
  have hnc : ∀ g : C, g * t' * g⁻¹ ≠ b₀' := by
    intro g hg
    have h1 : (g : G) * t * (g : G)⁻¹ = b₀ := congrArg Subtype.val hg
    have h2 := H.conj_t_eq_of_mem_R (x := (g : G)⁻¹) (inv_mem g.2)
      (by rw [inv_inv, h1]; exact hb₀R)
    rw [inv_inv, h1] at h2
    exact hb₀t h2
  have hyK : (h'⁻¹ * z' * h' : C) ∈ normalizer (K : Set C) :=
    hCzK _ (Subtype.ext (H.sec5.zS _ hyS))
  have hcls : ∀ i ∈ R', i * i = 1 → i ≠ 1 →
      ∃ n ∈ normalizer (K : Set C), n * i * n⁻¹ = t' ∨ n * i * n⁻¹ = b₀' := by
    intro i hi hi2 hi1
    by_cases hit : i = t'
    · exact ⟨1, one_mem _, Or.inl (by rw [hit]; group)⟩
    · obtain ⟨g, hgR, hg⟩ := hcls₀ i ((hmemR i).mp hi) (congrArg Subtype.val hi2)
        (fun e => hi1 (Subtype.ext e)) (fun e => hit (Subtype.ext e))
      have hg'K : (⟨g, hRC hgR⟩ : C) ∈ normalizer (K : Set C) :=
        le_normalizer (mem_sup_left (show (⟨g, hRC hgR⟩ : C) ∈ R' from hgR))
      rcases hg with hg | hg
      · exact ⟨⟨g, hRC hgR⟩, hg'K, Or.inr (Subtype.ext hg)⟩
      · refine ⟨⟨g, hRC hgR⟩ * (h'⁻¹ * z' * h'), mul_mem hg'K hyK, Or.inr (Subtype.ext ?_)⟩
        have e1 : ((⟨g, hRC hgR⟩ * (h'⁻¹ * z' * h') * i *
            (⟨g, hRC hgR⟩ * (h'⁻¹ * z' * h'))⁻¹ : C) : G) =
            g * ((h⁻¹ * z * h) * (i : G) * (h⁻¹ * z * h)⁻¹) * g⁻¹ := by
          have e2 : ((h' : C) : G) = h := rfl
          have e3 : ((z' : C) : G) = z := rfl
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, e2, e3]
          group
        rw [e1, hg]
  have htight : ∀ x : C, Even (Nat.card (K ⊓ rightConjugate K x : Subgroup C)) →
      x ∈ normalizer (K : Set C) := fun x hx =>
    mem_normalizer_of_even hRK hcls hnc hCtK (hCbK b₀ hb₀R hb₀2 hb₀1 hb₀t) hx
  set O := standardComponentOddCore C with hO
  have hOodd : Odd (Nat.card O) := odd_card_standardComponentOddCore
  set π := QuotientGroup.mk' O with hπ
  have hKb := tightlyEmbedded_map_mk hOodd hRK (even_of_involution htR ht2 ht1) htight
  have hRKb := isSylowOf_map_mk hOodd hRK
  have hinj : Function.Injective (π.comp R'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    exact mem_bot.mpr (Subtype.ext (eq_one_of_mem_isPGroup_of_mem_odd hR2 hOodd x.2 hx))
  have eR : R' ≃* R'.map π := (MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype]))
  obtain ⟨m, hm1, ⟨eD⟩⟩ := H.sec5.exists_dihedral_R
  have hRd : AschbacherTheorem3.IsDihedralTwoGroup (R'.map π) :=
    ⟨m + 1, by omega, ⟨(eR.symm.trans (subgroupOfEquivOfLe hRC)).trans eD⟩⟩
  have hcardR : 4 < Nat.card (R'.map π) := by
    rw [← Nat.card_congr eR.toEquiv, Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv,
      card_eq_two_mul hD, hD.ord]
    have : 0 < 2 ^ j := by positivity
    omega
  have hWK : (sigW t' f').map π ≤ K.map π := map_mono le_sup_right
  have hKW : K.map π ≤ normalizer (((sigW t' f').map π : Subgroup (C ⧸ O)) : Set (C ⧸ O)) :=
    (map_mono (sup_le hRW le_normalizer)).trans (le_normalizer_map π)
  have hWodd' : Odd (Nat.card ((sigW t' f').map π)) :=
    Odd.of_dvd_nat hWodd (Subgroup.card_map_dvd (H := sigW t' f') π)
  have hKRW : K.map π ≤ R'.map π ⊔ (sigW t' f').map π := (Subgroup.map_sup _ _ _).le
  obtain ⟨ub, hubR, hubP, hub2⟩ := exists_mem_pCore h3 standardComponentOddCore_quotient_eq_bot
    hKb hRKb hRd hcardR hWK hKW hWodd' hKRW
  obtain ⟨u, huR, rfl⟩ := hubR
  have hT' : IsSylowOf 2 (T.subgroupOf C) ⊤ := by
    have h1 := (Asc76.Sec5.isSylowOf_subgroupOf_iff H.T_le_centralizer_d le_rfl).mpr
      H.isSylowOf_T_H
    rwa [subgroupOf_self] at h1
  refine false_of_mem_pCore (T := T.subgroupOf C) (R := R') (z := z') (d := d') (h := h') (u := u)
    (Subtype.ext H.d_mul_self) (fun x => Subtype.ext (mem_centralizer_singleton_iff.mp x.2))
    hT' (fun x hx => ?_) hR2 (fun hd => ?_) (fun r hr => ?_) (fun r hr hry => ?_) huR hubP
    (fun e => hub2 (by rw [← map_mul, e, map_one]))
  · rcases H.conj_z_of_mem_T (mem_subgroupOf.mp hx) with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · refine Or.inr (Subtype.ext ?_)
      change (x : G)⁻¹ * z * x = z * (z * t)
      rw [h1, ← mul_assoc, H.mul_self_z, one_mul]
  · have h1 : z * t ∈ S ⊓ L := hd
    have h2 : z ∈ S ⊓ L := by
      have h3 := mul_mem h1 H.sec5.tR
      rwa [mul_assoc, H.mul_self_t, mul_one] at h3
    have h4 : z ∈ S ⊓ L ⊓ conjugate (S ⊓ L) s := mem_inf.mpr ⟨h2, H.z_mem_Rs⟩
    rw [H.R_inf_Rs, mem_bot] at h4
    exact H.z_ne_one h4
  · exact H.sec5.conj_mem_R hyS ((hmemR r).mp hr)
  · rcases hfix r ((hmemR r).mp hr) (congrArg Subtype.val hry) with e | e
    · exact Subtype.ext (by change (r : G) * r = 1; rw [e, one_mul])
    · exact Subtype.ext (by change (r : G) * r = 1; rw [e, H.mul_self_t])

theorem isSolvable_centralizer (h3 : Asc76Theorem3Large) :
    Group.IsSolvable ↥(centralizer ({z * t} : Set G)) := by
  have hSC : S ≤ centralizer ({z * t} : Set G) := H.sec5.ST.trans H.T_le_centralizer_d
  refine isSolvable_of_isolated_pair H.mul_self_z H.mul_self_t H.z_ne_one H.t_ne_one
    H.isSolvable_CZ le_rfl (hSC H.sec5.zS_mem) (hSC H.sec5.tS) H.isSylowOf_T_H
    fun x hx hxT => ?_
  by_contra hne
  push Not at hne
  exact H.false_of_pgl h3 hx hxT hne.1 hne.2

theorem isSolvable_centralizer_of_mem (h3 : Asc76Theorem3Large) {d : G}
    (hd : d ∈ S ⊓ L ⊔ conjugate (S ⊓ L) s) (hd2 : d * d = 1) (hdR : d ∉ S ⊓ L)
    (hdRs : d ∉ conjugate (S ⊓ L) s) : Group.IsSolvable ↥(centralizer ({d} : Set G)) := by
  obtain ⟨a, ha, b, hb, rfl, ha2, hb2⟩ := H.exists_mul_of_mem_sup hd hd2
  have ha1 : a ≠ 1 := fun e => hdRs (by rw [e, one_mul]; exact hb)
  have hb1 : b ≠ 1 := fun e => hdR (by rw [e, mul_one]; exact ha)
  obtain ⟨g, hg⟩ := H.exists_conj_diag ha hb (orderOf_eq_prime (by rw [sq]; exact ha2) ha1)
    (orderOf_eq_prime (by rw [sq]; exact hb2) hb1)
  have hconj : conjugate (centralizer ({a * b} : Set G)) g = centralizer ({z * t} : Set G) := by
    ext x
    rw [mem_conjugate_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← hg]
    constructor
    · intro h1
      calc x * (g⁻¹ * (a * b) * g) = g⁻¹ * ((g * x * g⁻¹) * (a * b)) * g := by group
        _ = g⁻¹ * ((a * b) * (g * x * g⁻¹)) * g := by rw [h1]
        _ = g⁻¹ * (a * b) * g * x := by group
    · intro h1
      calc g * x * g⁻¹ * (a * b) = g * (x * (g⁻¹ * (a * b) * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * (a * b) * g) * x) * g⁻¹ := by rw [h1]
        _ = a * b * (g * x * g⁻¹) := by group
  obtain ⟨e⟩ := nonempty_conjugate_equiv (centralizer ({a * b} : Set G)) g
  rw [hconj] at e
  have := H.isSolvable_centralizer h3
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

end Hyp

end CFSG.ComponentClassification.Sol78.F514
