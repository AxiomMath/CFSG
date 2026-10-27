module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push28Elem
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push28Compl

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G]

structure Push28Out (L T U₁ : Subgroup G) (q : ℕ) (y d : G) : Prop where
  A_le : gmsA L T ≤ U₁
  card : Nat.card U₁ = q ^ 2
  le_normalizer : T ≤ normalizer (U₁ : Set G)
  inf_eq_bot : (T ⊓ centralizer (L : Set G)) ⊓ U₁ = ⊥
  centralizer_eq : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 →
    U₁ ⊓ centralizer ({t} : Set G) = gmsA L T
  comm_mem : ∀ t ∈ T ⊓ centralizer (L : Set G), ∀ u ∈ U₁, t * u * t⁻¹ * u⁻¹ ∈ gmsA L T
  sq_mem : ∀ u ∈ U₁, u * u ∈ gmsA L T
  sylow : IsSylowOf 2 (U₁ ⊔ T) (normalizer (gmsV L T : Set G))
  mem_normalizer : d ∈ normalizer (U₁ : Set G)
  odd : Odd (orderOf d)
  conj_T₀ : ∀ t ∈ T ⊓ centralizer (L : Set G), d * t * d⁻¹ = t
  conj_A : ∀ a ∈ gmsA L T, d * a * d⁻¹ = y * a * y⁻¹
  pow_conj : ∀ u ∈ U₁, d ^ (q - 1) * u * (d ^ (q - 1))⁻¹ = u

variable [Finite G] {L T R : Subgroup G} {f : ℕ}

namespace Push28Torus

variable {y d : G}

theorem exists_push28Out
    (hd : Push28Torus L T R y d) (hR : Sec3.IsR L T R) (hy : Sec3.IsTorus L T y)
    (h313 : Lemma313 L T (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (htr : ∀ Q ∈ gmsDelta L T, ∃ u ∈ gmsTrans L T,
      rightConjugate (T ⊓ centralizer (L : Set G)) u⁻¹ = Q)
    (hsq : ∀ x ∈ R, x * x ∈ gmsA L T) :
    ∃ U₁ : Subgroup G, U₁ ≤ R ∧ Push28Out L T U₁ (2 ^ f) y d := by
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀
  obtain ⟨hVc, hVel, -, -, -⟩ := hX.vFacts h hF
  obtain ⟨hA₁c, hA₁sq, -⟩ := hX.sylow h
  have hVR := hR.gmsV_le_of_psl2 h hf e
  have hRA : ∀ r ∈ R, ∀ a ∈ gmsA L T, r * a = a * r := fun r hr a ha =>
    Sec3.commute_of_mem_gmsTrans (hR.le_gmsTrans hr) ha
  have hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ gmsA L T := fun x hx y hy =>
    commutator_mem_of_sq_mem' hRA hsq hx hy
  have hdA : d ∈ normalizer (gmsA L T : Set G) := h313.normalizer_le hd.mem_normalizer_V
  have hD : ComplData R (gmsA L T) (gmsV L T) d :=
    { A_le := le_sup_left
      Z_le := hVR
      normal := fun p hp a ha => by rw [hRA p hp a ha, mul_inv_cancel_right]; exact ha
      comm := hcomm
      sq := hsq
      normP := hd.mem_normalizer
      normA := hdA
      odd := hd.odd
      fix := fun x hx => hd.fix_iff hR hy h313 h hF hf e hX hx }
  obtain ⟨U₁, hAU, hUR, hUV, hfac, hUd, hmax⟩ := exists_compl hD
  have hUn : ∀ r ∈ R, ∀ u ∈ U₁, r * u * r⁻¹ ∈ U₁ := by
    intro r hr u hu
    have h1 := hcomm _ (inv_mem (hUR hu)) _ hr
    have e1 : r * u * r⁻¹ = u * (u⁻¹ * r * u⁻¹⁻¹ * r⁻¹) := by group
    rw [e1]
    exact mul_mem hu (hAU h1)
  have hdpow : ∀ (k : ℕ), ∀ u ∈ U₁, d ^ k * u * (d ^ k)⁻¹ ∈ U₁ := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      have e1 : d ^ (k + 1) * u * (d ^ (k + 1))⁻¹ = d * (d ^ k * u * (d ^ k)⁻¹) * d⁻¹ := by group
      rw [e1]
      exact hUd _ (ih u hu)
  have hRsup : gmsV L T ⊔ U₁ = R := by
    refine le_antisymm (sup_le hVR hUR) fun x hx => ?_
    obtain ⟨u, hu, z, hz, rfl⟩ := hfac x hx
    have := mul_mem (mem_sup_right hu : u ∈ gmsV L T ⊔ U₁) (mem_sup_left hz)
    exact this
  have hcard : Nat.card U₁ = (2 ^ f) ^ 2 := by
    have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer
      (A := gmsV L T) (B := U₁) (hUR.trans hR.le_normalizer_gmsV)
    rw [hRsup, inf_comm, hUV, hR.card_eq_of_psl2 h313 h hF hf e hX htr, hA₁c] at h1
    have hpos : 0 < Nat.card (gmsV L T) := Nat.card_pos
    have h2 : Nat.card (gmsV L T) * Nat.card U₁ = Nat.card (gmsV L T) * (2 ^ f) ^ 2 := by
      rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hinf : T₀ ⊓ U₁ = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨htT, htU⟩ := mem_inf.mp ht
    have htA : t ∈ gmsA L T := by
      rw [← hUV]
      exact mem_inf.mpr ⟨htU, mem_sup_right htT⟩
    have := mem_inf.mpr ⟨htT, htA⟩
    rwa [h313.inf_gmsA_eq_bot Sec3.mem_delta_T₀] at this
  have hC : ∀ t ∈ T₀, t ≠ 1 → U₁ ⊓ centralizer ({t} : Set G) = gmsA L T := by
    intro t ht ht1
    have htt : t * t = 1 := by rw [← sq]; exact hVel.2 t (mem_sup_right ht)
    refine le_antisymm (fun u hu => ?_) (le_inf hAU fun a ha => ?_)
    · obtain ⟨huU, huC⟩ := mem_inf.mp hu
      have huM : u ∈ normalizer (L : Set G) :=
        h.centralizer_le_normalizer_of_mem (mem_inf.mp ht).2 ht1 htt huC
      have huV : u ∈ normalizer (gmsV L T : Set G) := hR.le_normalizer_gmsV (hUR huU)
      have huN : u ∈ normalizer (T₀ : Set G) := by
        rw [hT₀, ← Sec3.gmsV_inf_centralizer_eq h hX]
        exact mem_normalizer_inf huV (h.normalizer_le_normalizer_centralizer huM)
      have huV' : u ∈ gmsV L T := by
        rw [← hR.inf_normalizer_eq_of_psl2 h313 h hF hf e hX]
        exact mem_inf.mpr ⟨hUR huU, huN⟩
      rw [← hUV]
      exact mem_inf.mpr ⟨huU, huV'⟩
    · exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (mem_inf.mp ht).2 a (mem_inf.mp (mem_inf.mp ha).1).2)
  have hTU : ∀ w ∈ T, ∀ u ∈ U₁, w * u * w⁻¹ ∈ U₁ := by
    intro w hw
    have hwA := h.le_normalizer_gmsA hw
    have hwV := h.le_normalizer_gmsV hw
    have hwR := hR.le_normalizer hw
    obtain ⟨m, v, hv, hvR⟩ := hd.exists_conj_eq_of_mem_T hR hy h313 h hF hf e hX hw
    set U' := rightConjugate U₁ w⁻¹ with hU'
    have hmemU' : ∀ x, x ∈ U' ↔ w⁻¹ * x * w ∈ U₁ := fun x => by
      rw [hU', mem_rightConjugate_iff, inv_inv]
    have hAU' : gmsA L T ≤ U' := fun a ha => (hmemU' a).mpr (hAU (by
      simpa using (mem_normalizer_iff.mp (inv_mem hwA) a).mp ha))
    have hU'R : U' ≤ R := fun x hx => by
      have h1 := (mem_normalizer_iff.mp hwR _).mp (hUR ((hmemU' x).mp hx))
      simpa [mul_assoc] using h1
    have hU'V : U' ⊓ gmsV L T = gmsA L T := by
      refine le_antisymm (fun x hx => ?_) (le_inf hAU' le_sup_left)
      obtain ⟨hxU, hxV⟩ := mem_inf.mp hx
      have h1 : w⁻¹ * x * w ∈ gmsA L T := by
        rw [← hUV]
        refine mem_inf.mpr ⟨(hmemU' x).mp hxU, ?_⟩
        simpa using (mem_normalizer_iff.mp (inv_mem hwV) x).mp hxV
      have h2 := (mem_normalizer_iff.mp hwA _).mp h1
      simpa [mul_assoc] using h2
    have hU'd : ∀ x ∈ U', d * x * d⁻¹ ∈ U' := by
      intro x hx
      rw [hmemU'] at hx ⊢
      have e1 : w⁻¹ * (d * x * d⁻¹) * w =
          (w⁻¹ * d * w) * (w⁻¹ * x * w) * (w⁻¹ * d * w)⁻¹ := by group
      rw [e1, hvR _ (hUR hx)]
      exact hUn v (hVR hv) _ (hdpow m _ hx)
    have hle := hmax U' hAU' hU'R hU'V hU'd
    intro u hu
    apply hle
    rw [hmemU']
    simpa [mul_assoc] using hu
  have hTN : T ≤ normalizer (U₁ : Set G) := fun w hw =>
    mem_normalizer_of_conj_mem_of_finite' (hTU w hw)
  have hsup : U₁ ⊔ T = R ⊔ T := by
    refine le_antisymm (sup_le_sup_right hUR T) (sup_le (fun x hx => ?_) le_sup_right)
    obtain ⟨u, hu, z, hz, rfl⟩ := hfac x hx
    have hVT : gmsV L T ≤ T := sup_le (inf_le_left.trans inf_le_left) inf_le_left
    have hzT : z ∈ T := hVT hz
    exact mul_mem (mem_sup_left hu) (mem_sup_right hzT)
  have hq1 : ∀ a ∈ gmsA L T, d ^ (2 ^ f - 1) * a * (d ^ (2 ^ f - 1))⁻¹ = a := by
    intro a ha
    rw [hd.pow_conj_eq hy _ a (mem_sup_left ha)]
    have h1 : hy.aut ^ (2 ^ f - 1) = 1 := by rw [← hy.orderOf_aut hX h]; exact pow_orderOf_eq_one _
    exact (hy.aut_pow_eq_one_iff _).mp h1 a ha
  have key : ∀ t ∈ T₀, t ≠ 1 → ∀ g : G, Odd (orderOf g) → g * t = t * g →
      (∀ a ∈ gmsA L T, g * a * g⁻¹ = a) → (∀ u ∈ U₁, g * u * g⁻¹ ∈ U₁) →
      ∀ u ∈ U₁, g * u * g⁻¹ = u := by
    intro t ht ht1 g hgo hgt hgA hgU u hu
    have hcu : u * t * u⁻¹ * t⁻¹ ∈ gmsA L T :=
      Sec3.conj_mul_inv_mem (hR.le_gmsTrans (hUR hu)) (mem_sup_right ht)
    have hgt' : g * t * g⁻¹ = t := by rw [hgt, mul_inv_cancel_right]
    have h1 : g * (u * t * u⁻¹ * t⁻¹) * g⁻¹ = u * t * u⁻¹ * t⁻¹ := hgA _ hcu
    have h2 : g * (u * t * u⁻¹ * t⁻¹) * g⁻¹ =
        (g * u * g⁻¹) * t * (g * u * g⁻¹)⁻¹ * t⁻¹ := by
      calc g * (u * t * u⁻¹ * t⁻¹) * g⁻¹ =
          (g * u * g⁻¹) * (g * t * g⁻¹) * (g * u * g⁻¹)⁻¹ * (g * t * g⁻¹)⁻¹ := by group
        _ = (g * u * g⁻¹) * t * (g * u * g⁻¹)⁻¹ * t⁻¹ := by rw [hgt']
    rw [h2] at h1
    have h3 : (g * u * g⁻¹) * t * (g * u * g⁻¹)⁻¹ = u * t * u⁻¹ := mul_right_cancel h1
    set a := u⁻¹ * (g * u * g⁻¹) with ha
    have e1 : g * u * g⁻¹ = u * a := by rw [ha]; group
    rw [e1] at h3
    have h4 : a * t * a⁻¹ = t := by
      calc a * t * a⁻¹ = u⁻¹ * (u * a * t * (u * a)⁻¹) * u := by group
        _ = u⁻¹ * (u * t * u⁻¹) * u := by rw [h3]
        _ = t := by group
    have hat : a * t = t * a := by
      calc a * t = a * t * a⁻¹ * a := by group
        _ = t * a := by rw [h4]
    have haA : a ∈ gmsA L T := by
      rw [← hC t ht ht1]
      exact mem_inf.mpr ⟨mul_mem (inv_mem hu) (hgU u hu), mem_centralizer_singleton_iff.mpr hat⟩
    have hga : g * a = a * g := by
      have := hgA a haA
      calc g * a = g * a * g⁻¹ * g := by group
        _ = a * g := by rw [this]
    have haa : a * a = 1 := by rw [← sq]; exact hA₁sq a haA
    exact conj_eq_of_odd_of_eq_mul hgo hga haa (by rw [ha]; group)
  have hpow : ∀ u ∈ U₁, d ^ (2 ^ f - 1) * u * (d ^ (2 ^ f - 1))⁻¹ = u := by
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.T₀_ne_bot
    have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
    have hdt : Commute d t := by
      have := hd.conj_T₀ hy ht
      show d * t = t * d
      calc d * t = d * t * d⁻¹ * d := by group
        _ = t * d := by rw [this]
    exact key t ht ht1' _ (hd.odd.of_dvd_nat (orderOf_pow_dvd _)) (hdt.pow_left _).eq hq1
      (hdpow _)
  refine ⟨U₁, hUR, ?_⟩
  exact
    { A_le := hAU
      card := hcard
      le_normalizer := hTN
      inf_eq_bot := hinf
      centralizer_eq := hC
      comm_mem := fun t ht u hu => by
        have := inv_mem (Sec3.conj_mul_inv_mem (hR.le_gmsTrans (hUR hu)) (mem_sup_right ht))
        have e1 : (u * t * u⁻¹ * t⁻¹)⁻¹ = t * u * t⁻¹ * u⁻¹ := by group
        rwa [e1] at this
      sq_mem := fun u hu => hsq u (hUR hu)
      sylow := hsup ▸ hR.isSylowOf_sup_of_psl2 h hX htr
      mem_normalizer := mem_normalizer_of_conj_mem_of_finite' hUd
      odd := hd.odd
      conj_T₀ := fun t ht => hd.conj_T₀ hy ht
      conj_A := fun a ha => hd.conj_eq a (mem_sup_left ha)
      pow_conj := hpow }

end Push28Torus

end CFSG.ComponentClassification.GMS78
