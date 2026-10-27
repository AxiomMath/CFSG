module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51C
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51B

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)} (hD : Foote5AutData 𝕊 Lin)
  (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {x : G} (hx : x ∈ normalizer (S : Set G))
  (hxQ : x ∉ normalizer (Q : Set G)) (hodd : Odd (orderOf x)) (hxt : x * t * x⁻¹ = t)
include h ε hD hna hx hxQ hodd hxt

theorem Q_inf_commutator_eq_bot : Q ⊓ ⁅S, S⁆ = ⊥ := by
  by_contra hne
  have hN : S ≤ normalizer ((Q ⊓ ⁅S, S⁆ : Subgroup G) : Set G) :=
    le_normalizer_of_conj_mem fun s hs y hy => mem_inf.mpr ⟨h.conj_mem_Q hs (mem_inf.mp hy).1,
      conj_mem_commutator_of_mem_normalizer (le_normalizer hs) (mem_inf.mp hy).2⟩
  obtain ⟨u, huN, hu2, huS⟩ :=
    exists_involution_center h.isPGroup_S (inf_le_left.trans h.QS) hN hne
  have hu1 : u ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hu2
    omega
  have huQ := (mem_inf.mp huN).1
  have hstep : ∀ v : G, v ∈ ⁅S, S⁆ → (∀ s ∈ S, s * v = v * s) →
      x⁻¹ * v * x ∈ ⁅S, S⁆ ∧ ∀ s ∈ S, s * (x⁻¹ * v * x) = x⁻¹ * v * x * s := by
    intro v hv hvZ
    refine ⟨?_, fun s hs => ?_⟩
    · have h1 := conj_mem_commutator_of_mem_normalizer (inv_mem hx) hv
      rwa [inv_inv] at h1
    · have h1 := hvZ _ ((mem_normalizer_iff.mp hx s).mp hs)
      calc s * (x⁻¹ * v * x) = x⁻¹ * ((x * s * x⁻¹) * v) * x := by group
        _ = x⁻¹ * (v * (x * s * x⁻¹)) * x := by rw [h1]
        _ = x⁻¹ * v * x * s := by group
  have hxt' : x⁻¹ * t * x = t := by
    calc x⁻¹ * t * x = x⁻¹ * (x * t * x⁻¹) * x := by rw [hxt]
      _ = t := by group
  have hQQx := h.inf_conjugate_eq_bot hx hxQ
  have hQQx2 := h.inf_conjugate_eq_bot (pow_mem hx 2) (sq_not_mem_normalizer hxQ hodd)
  obtain ⟨hv1C, hv1Z⟩ := hstep u (mem_inf.mp huN).2 huS
  obtain ⟨q₁, hq₁, hv1 | hv1⟩ := h.exists_eq_of_mem_commutator_center ε hD hna hv1C hv1Z
  · have h1 : x⁻¹ * u * x ∈ Q ⊓ conjugate Q x := by
      refine mem_inf.mpr ⟨by rw [hv1]; exact hq₁, mem_conjugate_iff.mpr ?_⟩
      rw [show x * (x⁻¹ * u * x) * x⁻¹ = u by group]
      exact huQ
    rw [hQQx, mem_bot] at h1
    apply hu1
    calc u = x * (x⁻¹ * u * x) * x⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · obtain ⟨hv2C, hv2Z⟩ := hstep _ hv1C hv1Z
    obtain ⟨q₂, hq₂, hv2 | hv2⟩ := h.exists_eq_of_mem_commutator_center ε hD hna hv2C hv2Z
    · have h1 : x⁻¹ * (x⁻¹ * u * x) * x ∈ Q ⊓ conjugate Q (x ^ 2) := by
        refine mem_inf.mpr ⟨by rw [hv2]; exact hq₂, mem_conjugate_iff.mpr ?_⟩
        rw [show x ^ 2 * (x⁻¹ * (x⁻¹ * u * x) * x) * (x ^ 2)⁻¹ = u by group]
        exact huQ
      rw [hQQx2, mem_bot] at h1
      apply hu1
      calc u = x ^ 2 * (x⁻¹ * (x⁻¹ * u * x) * x) * (x ^ 2)⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · have h3 : x⁻¹ * (x⁻¹ * u * x) * x = x⁻¹ * q₁ * x * t := by
        rw [hv1, show x⁻¹ * (q₁ * t) * x = x⁻¹ * q₁ * x * (x⁻¹ * t * x) by group, hxt']
      have h2 : x⁻¹ * q₁ * x = q₂ := by
        rw [h3] at hv2
        exact mul_right_cancel hv2
      have h4 : x⁻¹ * q₁ * x ∈ Q ⊓ conjugate Q x :=
        mem_inf.mpr ⟨by rw [h2]; exact hq₂, conj_mem_conjugate hq₁ x⟩
      rw [hQQx, mem_bot] at h4
      have hq₁1 : q₁ = 1 := by
        calc q₁ = x * (x⁻¹ * q₁ * x) * x⁻¹ := by group
          _ = 1 := by rw [h4]; group
      rw [hq₁1, one_mul] at hv1
      have hut : u = t := by
        calc u = x * (x⁻¹ * u * x) * x⁻¹ := by group
          _ = t := by rw [hv1, hxt]
      have h5 : t ∈ Q ⊓ L := mem_inf.mpr ⟨hut ▸ huQ, h.tL⟩
      rw [h.Q_inf_L, mem_bot] at h5
      exact h.t_ne_one h5

theorem Q_le_center {q s : G} (hq : q ∈ Q) (hs : s ∈ S) : s * q = q * s := by
  have hc : s * q * s⁻¹ * q⁻¹ ∈ Q ⊓ ⁅S, S⁆ := by
    refine mem_inf.mpr ⟨mul_mem (h.conj_mem_Q hs hq) (inv_mem hq), ?_⟩
    rw [← commutatorElement_def]
    exact commutator_mem_commutator hs (h.QS hq)
  rw [h.Q_inf_commutator_eq_bot ε hD hna hx hxQ hodd hxt, mem_bot] at hc
  calc s * q = s * q * s⁻¹ * q⁻¹ * (q * s) := by group
    _ = q * s := by rw [hc, one_mul]

theorem conjugate_Q_le_center {y s : G} (hy : y ∈ conjugate Q x) (hs : s ∈ S) :
    s * y = y * s := by
  have h1 := h.Q_le_center ε hD hna hx hxQ hodd hxt (mem_conjugate_iff.mp hy)
    ((mem_normalizer_iff.mp hx s).mp hs)
  calc s * y = x⁻¹ * ((x * s * x⁻¹) * (x * y * x⁻¹)) * x := by group
    _ = x⁻¹ * ((x * y * x⁻¹) * (x * s * x⁻¹)) * x := by rw [h1]
    _ = y * s := by group

theorem fix_actImage_conjugate_Q :
    ∀ α ∈ actImage L ε (conjugate Q x), ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), α ρ = ρ := by
  intro α hα ρ hρ
  obtain ⟨p, hp, rfl⟩ := (mem_actImage ε ((h.conjugate_Q_le hx).trans h.S_le)).mp hα
  exact (h.actG_fix_iff ε (h.conjugate_Q_le hx hp)).mpr (fun r hr =>
    (h.conjugate_Q_le_center ε hD hna hx hxQ hodd hxt hp (mem_inf.mp hr).1).symm) ρ hρ

theorem actG_sq_conjugate_Q {p : G} (hp : p ∈ conjugate Q x) :
    actG L ε p * actG L ε p = 1 :=
  (hD.centralizer_sylow (h.Rbar ε) _
    (isPGroup_actImage ε (h.isPGroup_S.to_le (h.conjugate_Q_le hx)))
    (h.fix_actImage_conjugate_Q ε hD hna hx hxQ hodd hxt)).1 _
    (actG_mem_actImage ε ((h.conjugate_Q_le hx).trans h.S_le) hp)

theorem card_Q_eq_four :
    Nat.card Q = 4 ∧ Nat.card (actImage L ε (conjugate Q x)) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPS : conjugate Q x ≤ S := h.conjugate_Q_le hx
  have hPC : conjugate Q x ⊓ coreActionKernel L = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyQ : y ∈ Q := by
      rw [← h.inf_coreActionKernel]
      exact mem_inf.mpr ⟨hPS (mem_inf.mp hy).1, (mem_inf.mp hy).2⟩
    have h1 : y ∈ Q ⊓ conjugate Q x := mem_inf.mpr ⟨hyQ, (mem_inf.mp hy).1⟩
    rwa [h.inf_conjugate_eq_bot hx hxQ] at h1
  have hcard := card_eq_card_inf_mul_card_actImage ε (hPS.trans h.S_le)
  rw [hPC, card_bot, one_mul, card_conjugate_eq_card] at hcard
  have h4 := (hD.centralizer_sylow (h.Rbar ε) _ (isPGroup_actImage ε (h.isPGroup_S.to_le hPS))
    (h.fix_actImage_conjugate_Q ε hD hna hx hxQ hodd hxt)).2
  have hrQ : CFSG.Open.pRank 2 Q = 2 := by
    have h1 := h.pRank_Q
    rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h1
  obtain ⟨E, hEQ, -, hEcard⟩ := SectionRank.exists_pRank one_lt_two Q
  rw [hrQ] at hEcard
  have hQ4 : 4 ≤ Nat.card Q := by
    have h1 := card_le_of_le hEQ
    rw [hEcard] at h1
    simpa using h1
  omega

theorem exists_not_mem_lin : ∃ q' ∈ conjugate Q x, actG L ε q' ∉ Lin := by
  classical
  by_contra hall
  have hall' : ∀ q' ∈ conjugate Q x, actG L ε q' ∈ Lin := fun q' hq' => by
    by_contra h1
    exact hall ⟨q', hq', h1⟩
  have hPN : conjugate Q x ≤ normalizer (L : Set G) := (h.conjugate_Q_le hx).trans h.S_le
  have hnaR : ∃ a ∈ (h.Rbar ε : Subgroup 𝕊), ∃ b ∈ (h.Rbar ε : Subgroup 𝕊), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    exact ⟨_, h.psi_mem_Rbar ε ha, _, h.psi_mem_Rbar ε hb,
      fun h1 => hab ((h.psi_comm_iff ε ha hb).mp h1)⟩
  have hsub : ∀ α ∈ actImage L ε (conjugate Q x),
      α ∈ ({1, actG L ε t} : Finset (MulAut 𝕊)) := by
    intro α hα
    obtain ⟨p, hp, rfl⟩ := (mem_actImage ε hPN).mp hα
    obtain ⟨c, hcR, hcZ, hc⟩ := hD.centralizer_sylow_lin (h.Rbar ε) hnaR _ (hall' p hp)
      ⟨1, by rw [pow_one, pow_two]; exact h.actG_sq_conjugate_Q ε hD hna hx hxQ hodd hxt hp⟩
      (h.fix_actImage_conjugate_Q ε hD hna hx hxQ hodd hxt _ hα)
    obtain ⟨r, hr, rfl⟩ := (h.mem_Rbar_iff ε).mp hcR
    have hrZ : ∀ r' ∈ S ⊓ L, (r : G) * r' = r' * r := fun r' hr' =>
      (h.psi_comm_iff ε hr hr').mp (hcZ _ (h.psi_mem_Rbar ε hr'))
    rcases h.center_R hna hr hrZ with h1 | h1
    · have hr1 : r = 1 := Subtype.ext h1
      rw [hc, hr1, map_one, map_one]
      exact Finset.mem_insert_self _ _
    · have hrt : r = ⟨t, h.tL⟩ := Subtype.ext h1
      rw [hc, hrt, ← actG_of_mem_self ε h.tL]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hle := SmallLocal.card_le_of_forall_mem_finset _ hsub
  have h2 : ({1, actG L ε t} : Finset (MulAut 𝕊)).card ≤ 2 := Finset.card_le_two
  have h4 := (h.card_Q_eq_four ε hD hna hx hxQ hodd hxt).2
  omega

theorem mem_innAut_of_mem_lin {s : G} (hs : s ∈ S) (hlin : actG L ε s ∈ Lin)
    (hsq : actG L ε s * actG L ε s = 1) : actG L ε s ∈ innAut5 𝕊 := by
  by_contra hinn
  obtain ⟨q', hq', hq'lin⟩ := h.exists_not_mem_lin ε hD hna hx hxQ hodd hxt
  have hq'S := h.conjugate_Q_le hx hq'
  have hcomm : actG L ε s * actG L ε q' = actG L ε q' * actG L ε s := by
    rw [← actG_mul ε (h.S_le hs) (h.S_le hq'S), ← actG_mul ε (h.S_le hq'S) (h.S_le hs),
      h.conjugate_Q_le_center ε hD hna hx hxQ hodd hxt hq' hs]
  exact hD.not_commute _ _ hlin hinn hsq hq'lin
    (h.actG_sq_conjugate_Q ε hD hna hx hxQ hodd hxt hq') hcomm

end Sec5

end CFSG.ComponentClassification.Foote5
