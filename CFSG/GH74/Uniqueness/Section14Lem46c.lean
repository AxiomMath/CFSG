module

public import CFSG.GH74.Uniqueness.Section14Lem46

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] {Z : Set X} {M : Subgroup X} {t : X} {n r : ℕ}
  {L K J Mo P U T S2 : Subgroup X}

namespace Sec146

variable (F : Facts14 Z M t n r L K J Mo P U T S2)
include F

theorem quot_center [Finite X] (hsq : ∀ x ∈ S2, x * x ∈ T) :
    ∀ s ∈ S2, ∀ w ∈ Mo ⊔ U, s * w * s⁻¹ * w⁻¹ ∈ Mo := by
  intro s hs w hw
  by_cases hsT : s ∈ T
  · have : s * w = w * s := (MoU_central F w hw s hsT).symm
    rw [this, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  set c := s * w * s⁻¹ * w⁻¹ with hcdef
  have hsN := S2_le_NT F hs
  have hc : c ∈ Mo ⊔ U := mul_mem (NT_norm_MoU F hsN w hw) (inv_mem hw)
  have hss : s * s ∈ T := hsq s hs
  have hssw : (s * s) * w = w * (s * s) := (MoU_central F w hw _ hss).symm
  have h1 : s * c * s⁻¹ = c⁻¹ := by
    have e1 : (s * s) * w * (s * s)⁻¹ = w := by rw [hssw, mul_inv_cancel_right]
    calc s * c * s⁻¹ = (s * s) * w * (s * s)⁻¹ * (s * w⁻¹ * s⁻¹) := by rw [hcdef]; group
      _ = w * (s * w⁻¹ * s⁻¹) := by rw [e1]
      _ = c⁻¹ := by rw [hcdef]; group
  have h2 : c⁻¹ = c := inv_eq_of_mul_eq_one_right (MoU_sq F c hc)
  have hsc : s * c = c * s := by
    calc s * c = s * c * s⁻¹ * s := by group
      _ = c * s := by rw [h1, h2]
  exact cent_out F hs hsT hc hsc

theorem trans_u [Finite X] (hcard : Nat.card S2 = 2 ^ n * Nat.card T)
    (hqc : ∀ s ∈ S2, ∀ w ∈ Mo ⊔ U, s * w * s⁻¹ * w⁻¹ ∈ Mo) :
    ∀ u ∈ U, u ≠ 1 → ∀ m ∈ Mo, ∃ s ∈ S2, s * u * s⁻¹ = m * u := by
  intro u₁ hu₁ hu₁1 m hm
  set N₁ := stabCoset Mo u₁
  set θ₁ := stabCosetHom Mo (Mo_comm F) u₁ with hθ₁
  have hS2N₁ : S2 ≤ N₁ := fun s hs => ⟨S2_le_C0 F hs, hqc s hs u₁ (mem_sup_right hu₁)⟩
  have hTN₁ : T ≤ N₁ := F.T_le_S2.trans hS2N₁
  set S2' := S2.subgroupOf N₁ with hS2'
  have h1 := card_eq_card_inf_ker_mul θ₁ S2'
  have hker : θ₁.ker ⊓ S2' = T.subgroupOf N₁ := by
    ext g
    rw [mem_inf, MonoidHom.mem_ker, hθ₁, stabCosetHom_eq_one_iff, hS2', mem_subgroupOf,
      mem_subgroupOf, ← cent_S2_u F hu₁ hu₁1, mem_inf, mem_centralizer_singleton_iff]
  have hcS2' : Nat.card S2' = Nat.card S2 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS2N₁).toEquiv
  have hcT' : Nat.card (T.subgroupOf N₁) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN₁).toEquiv
  rw [hker, hcS2', hcT', hcard] at h1
  have h2 : Nat.card ↥(S2'.map θ₁) = 2 ^ n := by
    have hT0 : 0 < Nat.card T := Nat.card_pos
    have : Nat.card T * Nat.card ↥(S2'.map θ₁) = Nat.card T * 2 ^ n := by
      rw [← h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hT0 this
  have h3 : S2'.map θ₁ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [h2, F.card_Mo]
  have hmem : (⟨m, hm⟩ : ↥Mo) ∈ S2'.map θ₁ := h3 ▸ mem_top _
  obtain ⟨g, hg, hgm⟩ := hmem
  refine ⟨g, mem_subgroupOf.mp hg, ?_⟩
  have h4 := congrArg Subtype.val hgm
  rw [hθ₁, stabCosetHom_apply] at h4
  calc (g : X) * u₁ * (g : X)⁻¹ = (g : X) * u₁ * (g : X)⁻¹ * u₁⁻¹ * u₁ := by group
    _ = m * u₁ := by rw [h4]

theorem normal [Finite X] (hqc : ∀ s ∈ S2, ∀ w ∈ Mo ⊔ U, s * w * s⁻¹ * w⁻¹ ∈ Mo) :
    normalizer (T : Set X) ≤ normalizer (S2 : Set X) := by
  set Stab' : Subgroup X := ⨅ (w : ↥(Mo ⊔ U)), stabCoset Mo (w : X) with hStab'
  set Stab := normalizer (T : Set X) ⊓ Stab' with hStab
  have mem_Stab : ∀ h : X, h ∈ Stab ↔ h ∈ normalizer (T : Set X) ∧
      h ∈ centralizer (Mo : Set X) ∧ ∀ w ∈ Mo ⊔ U, h * w * h⁻¹ * w⁻¹ ∈ Mo := by
    intro h
    rw [hStab, mem_inf, hStab', mem_iInf]
    constructor
    · rintro ⟨hN, hW⟩
      exact ⟨hN, (hW ⟨1, one_mem _⟩).1, fun w hw => (hW ⟨w, hw⟩).2⟩
    · rintro ⟨hN, hC, hW⟩
      exact ⟨hN, fun w => ⟨hC, hW w w.2⟩⟩
  have hS2Stab : S2 ≤ Stab := fun s hs =>
    (mem_Stab s).mpr ⟨S2_le_NT F hs, S2_le_C0 F hs, hqc s hs⟩
  have hStab2 : IsPGroup 2 Stab := by
    intro h
    obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (h : X)).ne'
    refine ⟨a, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    set h' := (h : X) ^ 2 ^ a with hh'
    have hh'S : h' ∈ Stab := pow_mem h.2 _
    have hord : orderOf h' = m := by
      rw [hh', orderOf_pow_of_dvd (by positivity) (by rw [hom]; exact dvd_mul_right _ _), hom,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hodd : Odd (orderOf h') := hord ▸ hm
    obtain ⟨-, hC, hW⟩ := (mem_Stab h').mp hh'S
    have hcomm : ∀ w ∈ Mo ⊔ U, h' * w = w * h' := by
      intro w hw
      apply commute_of_odd_of_commutator_mem hodd
      · exact ((mem_centralizer_iff.mp hC) _ (hW w hw)).symm
      · exact F.Mo_sq _ (hW w hw)
    have hT := cent_MoU_le F hcomm
    have hzodd : Odd (Nat.card (zpowers h')) := by rw [Nat.card_zpowers]; exact hodd
    exact Bender.eq_one_of_isPGroup_two_of_odd F.T_sylow.isPGroup hzodd hT (mem_zpowers h')
  have hStabeq : Stab = S2 := (F.S2_sylow.eq_of_le hS2Stab inf_le_left hStab2)
  have key : ∀ g ∈ normalizer (T : Set X), ∀ s ∈ S2, g * s * g⁻¹ ∈ S2 := by
    intro g hg s hs
    rw [← hStabeq, mem_Stab]
    obtain ⟨hsN, hsC, hsW⟩ := (mem_Stab s).mp (hS2Stab hs)
    refine ⟨mul_mem (mul_mem hg hsN) (inv_mem hg), ?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro m hm
      have hm' : g⁻¹ * m * g ∈ Mo := by
        have := (mem_normalizer_iff.mp (NT_norm_Mo F (inv_mem hg)) m).mp hm
        simpa using this
      have h1 := (mem_centralizer_iff.mp hsC) _ hm'
      calc m * (g * s * g⁻¹) = g * ((g⁻¹ * m * g) * s) * g⁻¹ := by group
        _ = g * (s * (g⁻¹ * m * g)) * g⁻¹ := by rw [h1]
        _ = g * s * g⁻¹ * m := by group
    · intro w hw
      have hw' : g⁻¹ * w * g ∈ Mo ⊔ U := by
        have := NT_norm_MoU F (inv_mem hg) w hw
        simpa using this
      have h1 := hsW _ hw'
      have e : g * s * g⁻¹ * w * (g * s * g⁻¹)⁻¹ * w⁻¹ =
          g * (s * (g⁻¹ * w * g) * s⁻¹ * (g⁻¹ * w * g)⁻¹) * g⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.mp (NT_norm_Mo F hg) _).mp h1
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem D_norm_J {d : X} (hd : d ∈ dGrp M t) : ∀ j ∈ J, d * j * d⁻¹ ∈ J := by
  intro j hj
  have hdN := F.D_norm_L hd
  rw [F.J_eq] at hj ⊢
  rw [mem_centralizer_iff] at hj ⊢
  intro l hl
  have hl' : d⁻¹ * l * d ∈ L := by
    have := (mem_normalizer_iff.mp (inv_mem hdN) l).mp hl
    simpa using this
  have h1 := hj _ hl'
  calc l * (d * j * d⁻¹) = d * ((d⁻¹ * l * d) * j) * d⁻¹ := by group
    _ = d * (j * (d⁻¹ * l * d)) * d⁻¹ := by rw [h1]
    _ = d * j * d⁻¹ * l := by group

theorem normalizer_T [Finite X] (hcard : Nat.card S2 = 2 ^ n * Nat.card T)
    (hqc : ∀ s ∈ S2, ∀ w ∈ Mo ⊔ U, s * w * s⁻¹ * w⁻¹ ∈ Mo) :
    ∀ g ∈ normalizer (T : Set X), ∃ s ∈ S2, ∃ d ∈ dGrp M t,
      d ∈ normalizer (U : Set X) ∧ g = s * d := by
  intro g hg
  obtain ⟨u, hu, hu1, -⟩ := exists_u F
  have hguMoU : g * u * g⁻¹ ∈ Mo ⊔ U := NT_norm_MoU F hg u (mem_sup_right hu)
  obtain ⟨m, hm, u₁, hu₁, hmu⟩ := (mem_MoU_iff F).mp hguMoU
  have hu₁1 : u₁ ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hmu
    have huMo : u ∈ Mo := by
      have := (mem_normalizer_iff.mp (NT_norm_Mo F hg) u).mpr (hmu ▸ hm)
      exact this
    have : u ∈ Mo ⊓ U := mem_inf.mpr ⟨huMo, hu⟩
    rw [Mo_inf_U F, mem_bot] at this
    exact hu1 this
  obtain ⟨s, hs, hsu⟩ := trans_u F hcard hqc u₁ hu₁ hu₁1 m⁻¹ (inv_mem hm)
  have hsm : s * m = m * s := ((mem_centralizer_iff.mp (S2_le_C0 F hs)) m hm).symm
  have hyu : (s * g) * u * (s * g)⁻¹ = u₁ := by
    calc (s * g) * u * (s * g)⁻¹ = s * (g * u * g⁻¹) * s⁻¹ := by group
      _ = s * m * u₁ * s⁻¹ := by rw [hmu]; group
      _ = m * (s * u₁ * s⁻¹) := by rw [hsm]; group
      _ = u₁ := by rw [hsu]; group
  have hyN : s * g ∈ normalizer (T : Set X) := mul_mem (S2_le_NT F hs) hg
  have hyL : s * g ∈ normalizer (L : Set X) :=
    F.conj_J_NL u (F.U_le_J hu) hu1 u₁ (F.U_le_J hu₁) hu₁1 (s * g) hyu
  obtain ⟨l, hl, d, hd, hld⟩ := F.NL_eq (s * g) hyL
  have hyP : ∀ y ∈ normalizer (T : Set X), y ∈ normalizer (L : Set X) →
      ∀ x ∈ P, y * x * y⁻¹ ∈ P := by
    intro y hyT hyL' x hx
    exact T_inf_L F _ ((mem_normalizer_iff.mp hyT x).mp (P_le_T F hx))
      ((mem_normalizer_iff.mp hyL' x).mp (F.P_le_L hx))
  have hyPN : s * g ∈ normalizer (P : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hyP _ hyN hyL x, fun hx => ?_⟩
    have := hyP _ (inv_mem hyN) (inv_mem hyL) _ hx
    simpa [mul_assoc] using this
  have hlP : l ∈ normalizer (P : Set X) := by
    have : l = (s * g) * d⁻¹ := by rw [hld]; group
    rw [this]
    exact mul_mem hyPN (inv_mem (F.D_norm_P hd))
  obtain ⟨p, hp, k, hk, hpk⟩ := F.NL_P l hl hlP
  have hd'D : k * d ∈ dGrp M t := mul_mem (K_le_D F hk) hd
  have hyd' : s * g = p * (k * d) := by rw [hld, hpk]; group
  have hd'N : k * d ∈ normalizer (T : Set X) := by
    have : k * d = p⁻¹ * (s * g) := by rw [hyd']; group
    rw [this]
    exact mul_mem (inv_mem (le_normalizer (P_le_T F hp))) hyN
  have hd'U : k * d ∈ normalizer (U : Set X) := by
    have key : ∀ y ∈ normalizer (T : Set X), y ∈ dGrp M t → ∀ x ∈ U, y * x * y⁻¹ ∈ U := by
      intro y hyT hyD x hx
      exact T_inf_J F _ ((mem_normalizer_iff.mp hyT x).mp (U_le_T F hx))
        (D_norm_J F hyD x (F.U_le_J hx))
    rw [mem_normalizer_iff]
    intro x
    refine ⟨key _ hd'N hd'D x, fun hx => ?_⟩
    have := key _ (inv_mem hd'N) (inv_mem hd'D) _ hx
    simpa [mul_assoc] using this
  refine ⟨s⁻¹ * p, mul_mem (inv_mem hs) (F.T_le_S2 (P_le_T F hp)), k * d, hd'D, hd'U, ?_⟩
  calc g = s⁻¹ * (s * g) := by group
    _ = s⁻¹ * (p * (k * d)) := by rw [hyd']
    _ = s⁻¹ * p * (k * d) := by group

theorem lemma146 [Finite X] : Concl146 M t n K Mo U T S2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu, hu1, huS⟩ := exists_u F
  obtain ⟨hKN, hcard, hsq, hKtr⟩ := main_u F hu hu1 huS
  have hqc := quot_center F hsq
  obtain ⟨y, hyS, hyT⟩ := exists_S2_not_T F
  exact
    { sylow2 := by
        intro W hW
        obtain ⟨k, hk⟩ := hW.exists_card_eq
        have h1 : 2 ^ k ∣ Nat.card X := hk ▸ Subgroup.card_subgroup_dvd_card W
        have h2 : k ≤ (Nat.card X).factorization 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h1
        rw [hk, hcard, ← F.two_part]
        exact Nat.pow_le_pow_right (by norm_num) h2
      card_S2 := hcard
      S2_le_M := S2_le_M F
      S2_le_C0 := S2_le_C0 F
      normal := normal F hqc
      center := by
        intro x hx hc
        have hxT : x ∈ T := cent_MoU_le F fun w hw => hc w (F.T_le_S2 (MoU_le_T F hw))
        have hxZ : x ∈ Mo ⊔ U := center_T F x hxT fun z hz => hc z (F.T_le_S2 hz)
        exact cent_out F hyS hyT hxZ (hc y hyS).symm
      quot_center := hqc
      cent_S2_u := fun _ hu hu1 => cent_S2_u F hu hu1
      trans_u := trans_u F hcard hqc
      cent_out := fun _ hx hxT _ hw hxw => cent_out F hx hxT hw hxw
      normalizer_T := normalizer_T F hcard hqc
      K_trans_S2 := hKtr
      K_norm_S2 := hKN
      sq_mem_T := hsq
      T_lt_S2 := lt_of_le_of_ne F.T_le_S2 fun h => hyT (h ▸ hyS) }

end Sec146

theorem lemma146 {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {t : X} {n r : ℕ}
    {L K J Mo P U T S2 : Subgroup X} (F : Facts14 Z M t n r L K J Mo P U T S2) :
    Concl146 M t n K Mo U T S2 :=
  Sec146.lemma146 F

end CFSG.GH74.Uniqueness
