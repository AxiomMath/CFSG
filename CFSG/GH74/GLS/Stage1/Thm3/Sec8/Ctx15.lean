module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx14
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx6

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem S1_normal (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {t s : G} (ht : t ∈ S) (hs1 : s ∈ S1 S K₁) :
    t * s * t⁻¹ ∈ S1 S K₁ := by
  have hle : (S1 S K₁).relIndex S ≤ 2 := hs.fused.p66.2.1.1
  have hpos : (S1 S K₁).relIndex S ≠ 0 := Basic.relIndex_ne_zero' _ _
  rcases (show (S1 S K₁).relIndex S = 1 ∨ (S1 S K₁).relIndex S = 2 by omega) with h1 | h1
  · have hSS : S ≤ S1 S K₁ := Subgroup.relIndex_eq_one.1 h1
    exact mul_mem (mul_mem (hSS ht) hs1) (inv_mem (hSS ht))
  · have hN : ((S1 S K₁).subgroupOf S).Normal := Subgroup.normal_of_index_eq_two h1
    exact hN.conj_mem ⟨s, S1_le_S hs1⟩ hs1 ⟨t, ht⟩

theorem conj_V₁_eq_V₂ (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 2)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ 2) {t : G} (ht : t ∈ S) (hn : t ∉ S1 S K₁) :
    conjugate (Vof S K₁ W₂) t⁻¹ = Vof S K₂ W₁ := by
  by_contra hne
  obtain ⟨e, he', hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have he1 : e = 1 := by omega
  subst he1
  have hQ₂ : Pof S K₁ = Qof S K₂ := hs.Q₂_eq_P₁_of_e_one hII hq2
  have hV := hs.card_V₁ hII hq
  have hP₁ : Nat.card ↥(Pof S K₁) = 8 := by omega
  have hP₂ : Nat.card ↥(Pof S K₂) = 8 := by omega
  have hV₂card := hs.V₂_card_eq hII hq hrec hk
  have hV₂card' : Nat.card ↥(Vof S K₂ W₁) = 4 := by rw [hV₂card]; norm_num
  have htinv : t⁻¹ ∈ S := inv_mem ht
  have hC'P : conjugate (Vof S K₁ W₂) t⁻¹ ≤ Pof S K₂ := by
    intro x hx
    have hx' : t⁻¹ * x * t ∈ Vof S K₁ W₂ := by
      have := mem_conjugate_iff.1 hx
      rwa [inv_inv] at this
    have h1 := hs.swap_P₁ hII ht hn hx'.2
    have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rwa [e] at h1
  have hC'c : IsCyclic ↥(conjugate (Vof S K₁ W₂) t⁻¹) := by
    rw [conjugate_eq_comap]; exact Basic.cyclic_comap_conj _ hs.V₁_cyclic t⁻¹
  have hC'card : Nat.card ↥(conjugate (Vof S K₁ W₂) t⁻¹) = 4 := by
    rw [conjugate_card, hk]; norm_num
  have hC'S : ∀ s ∈ S1 S K₁, ∀ x ∈ conjugate (Vof S K₁ W₂) t⁻¹,
      s * x * s⁻¹ ∈ conjugate (Vof S K₁ W₂) t⁻¹ := by
    intro s hs1 x hx
    have hx' : t⁻¹ * x * t ∈ Vof S K₁ W₂ := by
      have := mem_conjugate_iff.1 hx
      rwa [inv_inv] at this
    have hs' : t⁻¹ * s * t ∈ S1 S K₁ := by
      have := hs.S1_normal htinv hs1
      rwa [inv_inv] at this
    have h1 := hs.V₁_normal hII _ hs' _ hx'
    rw [mem_conjugate_iff, inv_inv]
    have e : t⁻¹ * (s * x * s⁻¹) * t = (t⁻¹ * s * t) * (t⁻¹ * x * t) * (t⁻¹ * s * t)⁻¹ := by group
    rw [e]; exact h1
  have hall : ∀ s ∈ S1 S K₁, ∀ p ∈ Pof S K₂, s * p * s⁻¹ * p⁻¹ ∈ zpowers z := fun s hs1 =>
    (hs.gq_P hII hq (Or.inr rfl)).Q8_comm_mod_z hP₂ (inf_le_right : Vof S K₂ W₁ ≤ Pof S K₂)
      hs.V₂_cyclic hV₂card' hC'P hC'c hC'card (fun h' => hne h'.symm)
      (fun c hc => hs.V₂_normal hII s hs1 c hc) (hC'S s hs1)
  have h8 : 8 * Nat.card ↥(Qof S K₂) ≤ Nat.card ↥(S1 S K₁) := by
    have hcard := hs.card_S1_eq hII hq hrec
    have h1 := hs.V₁h_card hII hq
    rw [hcard, h1, hP₁]
  obtain ⟨hN, a, b, hab⟩ := hs.nab_quot (K := K₂) (Or.inr rfl) (hs.Q₂_le_S1 hII) h8
  let π : ↥(S1 S K₁) →* (↥(S1 S K₁) ⧸ (Qof S K₂).subgroupOf (S1 S K₁)) := QuotientGroup.mk' _
  let R : Subgroup (↥(S1 S K₁) ⧸ (Qof S K₂).subgroupOf (S1 S K₁)) :=
    ((Pz S z).subgroupOf (S1 S K₁)).map π
  have hP₁Pz : Pof S K₁ ≤ Pz S z := by rw [hs.Pz_eq_sup hII]; exact le_sup_left
  have hker : π.ker ≤ (Pz S z).subgroupOf (S1 S K₁) := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    have hx' : (x : G) ∈ Qof S K₂ := hx
    rw [← hQ₂] at hx'
    exact hP₁Pz hx'
  have hR : R.index = 2 := by
    have := Subgroup.index_map_eq ((Pz S z).subgroupOf (S1 S K₁)) (QuotientGroup.mk'_surjective _) hker
    rw [this]; exact he
  have hz_cen : ∀ p ∈ S, ∀ c ∈ zpowers z, p⁻¹ * c * p = c := by
    intro p hp c hc
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    have hcomm : Commute p z := (hs.z_comm hII hp).symm
    calc p⁻¹ * z ^ m * p = p⁻¹ * (z ^ m * p) := by group
      _ = p⁻¹ * (p * z ^ m) := by rw [← (Commute.zpow_right hcomm m).eq]
      _ = z ^ m := by group
  have hcen : ∀ (s p : ↥(S1 S K₁)), (p : G) ∈ Pof S K₂ → π s * π p = π p * π s := by
    intro s p hp
    rw [← map_mul, ← map_mul]
    show (QuotientGroup.mk (s * p) : _) = QuotientGroup.mk (p * s)
    apply QuotientGroup.eq.2
    show (((s : G) * p)⁻¹ * (p * s) : G) ∈ Qof S K₂
    have h1 := hall (s : G)⁻¹ (inv_mem s.2) p hp
    rw [inv_inv] at h1
    have hpS : (p : G) ∈ S := hp.1
    have e : ((s : G) * p)⁻¹ * (p * s) = (p : G)⁻¹ * ((s : G)⁻¹ * p * s * (p : G)⁻¹) * p := by group
    rw [e, hz_cen p hpS _ h1]
    exact (zpowers_le.2 (hs.z_mem_Q hII (Or.inr rfl))) h1
  have hRcen : ∀ r ∈ R, ∀ d : ↥(S1 S K₁) ⧸ (Qof S K₂).subgroupOf (S1 S K₁), r * d = d * r := by
    intro r hr d
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 hr
    have ha₀' : (a₀ : G) ∈ Pz S z := ha₀
    rw [hs.Pz_eq_sup hII] at ha₀'
    obtain ⟨p₁, hp₁, p₂, hp₂, hdec⟩ := Basic.mem_sup_of_commute' (hs.P_comm hII) ha₀'
    have hp₂S1 : p₂ ∈ S1 S K₁ := hs.P_le_S1 hII (Or.inr rfl) hp₂
    have hpi : π a₀ = π ⟨p₂, hp₂S1⟩ := by
      show (QuotientGroup.mk a₀ : _) = QuotientGroup.mk ⟨p₂, hp₂S1⟩
      apply QuotientGroup.eq.2
      show ((a₀ : G))⁻¹ * p₂ ∈ Qof S K₂
      have hc : Commute p₂ p₁⁻¹ := (show Commute p₁ p₂ from hs.P_comm hII p₁ hp₁ p₂ hp₂).symm.inv_right
      have e : ((a₀ : G))⁻¹ * p₂ = p₁⁻¹ := by
        rw [hdec]
        calc (p₁ * p₂)⁻¹ * p₂ = p₂⁻¹ * (p₁⁻¹ * p₂) := by group
          _ = p₂⁻¹ * (p₂ * p₁⁻¹) := by rw [hc.eq]
          _ = p₁⁻¹ := by group
      rw [e, ← hQ₂]
      exact inv_mem hp₁
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ d
    rw [hpi]
    exact (hcen s ⟨p₂, hp₂S1⟩ hp₂).symm
  obtain ⟨w, hwS1, hwP⟩ : ∃ w ∈ S1 S K₁, w ∉ Pz S z := by
    by_contra hcon
    push Not at hcon
    exact hs.S1_ne_Pz hII hq hrec (le_antisymm (fun x hx => hcon x hx) (hs.Pz_le_S1 hII))
  have hy : π ⟨w, hwS1⟩ ∉ R := by
    intro hy
    obtain ⟨a₀, ha₀, hπ⟩ := Subgroup.mem_map.1 hy
    have h1 : (a₀)⁻¹ * ⟨w, hwS1⟩ ∈ (Qof S K₂).subgroupOf (S1 S K₁) := QuotientGroup.eq.1 hπ
    have h2 : ((a₀ : G))⁻¹ * w ∈ Qof S K₂ := h1
    rw [← hQ₂] at h2
    apply hwP
    have e : w = (a₀ : G) * (((a₀ : G))⁻¹ * w) := by group
    rw [e]
    exact mul_mem ha₀ (hP₁Pz h2)
  exact hab (Basic.comm_of_index_two R hR (fun a ha b _ => hRcen a ha b) hy
    (fun r hr => (hRcen r hr _).symm) a b)

theorem swap_V_small (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 2)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ 2) {t : G} (ht : t ∈ S) (hn : t ∉ S1 S K₁) :
    (∀ x ∈ Vof S K₁ W₂, t * x * t⁻¹ ∈ Vof S K₂ W₁) ∧
      (∀ x ∈ Vof S K₂ W₁, t * x * t⁻¹ ∈ Vof S K₁ W₂) := by
  have h1 := hs.conj_V₁_eq_V₂ hII hq hrec he hk ht hn
  have htinv : t⁻¹ ∈ S := inv_mem ht
  have htn' : t⁻¹ ∉ S1 S K₁ := fun h' => hn (by have := inv_mem h'; rwa [inv_inv] at this)
  have h2 := hs.conj_V₁_eq_V₂ hII hq hrec he hk htinv htn'
  rw [inv_inv] at h2
  constructor
  · intro x hx
    have hxc : t * x * t⁻¹ ∈ conjugate (Vof S K₁ W₂) t⁻¹ := by
      rw [mem_conjugate_iff]
      have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rw [e]; exact hx
    rwa [h1] at hxc
  · intro x hx
    rw [← h2] at hx
    exact mem_conjugate_iff.1 hx

theorem A_normedBy_S_e1_small (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 2)
    (hk2 : 2 ≤ 2) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ 2) : NormedBy (Aof S K₁ W₂ h) S :=
  hs.A_normedBy_S_of hII hq hrec hk2 hk (fun t ht hn => hs.swap_V_small hII hq hrec he hk ht hn)
    (fun x hxS hx1 hx2 _ => hs.KL_e1 hII hq hrec hk2 hk he hxS hx1 hx2)

theorem lemma82d (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    NormedBy (Aof S K₁ W₂ h) (S ⊔ zpowers h) ∧
      (∀ a ∈ Aof S K₁ W₂ h, ∀ b ∈ Aof S K₁ W₂ h, a * b = b * a) ∧ Aof S K₁ W₂ h ≤ S1 S K₁ ∧
      S ⊓ centralizer (Aof S K₁ W₂ h : Set G) = Aof S K₁ W₂ h := by
  obtain ⟨k, hk2, hk⟩ := hs.exists_k hII hq
  obtain ⟨e, he, hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have hS : NormedBy (Aof S K₁ W₂ h) S := by
    rcases he with rfl | rfl
    · have he1 : (Pz S z).relIndex (S1 S K₁) = 2 := by omega
      by_cases hSS : S = S1 S K₁
      · intro t ht a ha
        exact hs.A_normedBy_S1 hII hq hrec hk2 hk t (by rw [← hSS]; exact ht) a ha
      · by_cases hk3 : k = 2
        · subst hk3
          exact hs.A_normedBy_S_e1_small hII hq hrec he1 hk2 hk
        · have hV := hs.card_V₁ hII hq
          have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h16 : 16 ≤ Nat.card ↥(Qof S K₁) := by omega
          exact hs.A_normedBy_S_of hII hq hrec hk2 hk
            (fun t ht hn => hs.swap_V hII hq hrec h16 ht hn)
            (fun x hxS hx1 hx2 _ => hs.KL_e1 hII hq hrec hk2 hk he1 hxS hx1 hx2)
    · have he2 : (Pz S z).relIndex (S1 S K₁) = 4 := by omega
      exact hs.A_normedBy_S_e2 hII hq hrec he2 hk2 hk
  exact ⟨hs.A_normedBy_Sh hII hq hrec hk hS, hs.A_comm hII hq hrec, hs.A_le_S1 hII hq hrec,
    hs.cent_eq hII hq hrec⟩

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
