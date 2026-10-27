module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrImg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocC

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma map_subtype_top_eq {Γ : Type} [Group Γ] (K : Subgroup Γ) :
    (⊤ : Subgroup ↥K).map K.subtype = K := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

private lemma mem_sup_of_commute' {Γ : Type} [Group Γ] {A B : Subgroup Γ}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : Γ} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  have key : ∀ a ∈ A, ∀ h ∈ B, a * h * a⁻¹ ∈ B := by
    intro a ha h hh
    rw [hAB a ha h hh, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have hle : A ≤ normalizer (B : Set Γ) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key a ha h hh, fun hh => ?_⟩
    have h2 := key a⁻¹ (A.inv_mem ha) _ hh
    have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rwa [e] at h2
  have := Subgroup.coe_mul_of_left_le_normalizer_right A B hle
  have hg' : g ∈ ((A ⊔ B : Subgroup Γ) : Set Γ) := hg
  rw [this] at hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := hg'
  exact ⟨a, ha, b, hb, rfl⟩

private lemma card_sup_le_of_commute' {Γ : Type} [Group Γ] [Finite Γ] {A B : Subgroup Γ}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  have hsurj : Function.Surjective (fun x : ↥A × ↥B =>
      (⟨(x.1 : Γ) * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(A ⊔ B))) := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute' hAB hg
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod] at this

private lemma F_le_S (s : Setting3 G L) : s.fr'.F ≤ s.fr'.S := by
  rw [SFrame.F, SFrame.S, Subgroup.closure_le]
  rintro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · rw [SFrame.z]
    exact pow_mem (Subgroup.subset_closure (by simp)) 2

theorem s3_isE3_F (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (s : Setting3 G L) : IsE 3 ↥s.fr.F := by
  have h11 : (s.fr').Fact11 (innerAut (L ⧸ center L)) := s.facts.1
  have h14 : (s.fr').Fact14 := s.facts.2.2.2.1
  have h15 : (s.fr').Fact15 := s.facts.2.2.2.2.1
  have hE4 : IsE 4 ↥(s.fr'.F ⊔ closure {s.fr'.σ}) := h15.2.2.2.1.2.1
  have hσ'notS : s.fr'.σ ∉ s.fr'.S := by
    intro hσS
    have hSσ_eq : s.fr'.Sσ = s.fr'.S := by
      apply le_antisymm
      · rw [Frame.Sσ, Subgroup.closure_le]
        rintro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact hσS
      · rw [SFrame.S, Frame.Sσ, Subgroup.closure_le]
        rintro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
    have hSylowTop : IsSylowIn 2 ⊤ s.fr'.S := hSσ_eq ▸ h11.2.2
    have hrel := Subgroup.relIndex_mul_relIndex (H := s.fr'.S)
      (K := innerAut (L ⧸ center L)) (L := ⊤) h11.2.1.1 le_top
    rw [Subgroup.relIndex_top_right, hOut] at hrel
    have hdvd : 2 ∣ s.fr'.S.relIndex (innerAut (L ⧸ center L)) * 2 := dvd_mul_left 2 _
    rw [hrel] at hdvd
    exact hSylowTop.2.2 hdvd
  have hσ'notF : s.fr'.σ ∉ s.fr'.F := fun h => hσ'notS (F_le_S s h)
  let H : Subgroup (MulAut (L ⧸ center L)) := s.fr'.F ⊔ closure {s.fr'.σ}
  have hE4H : IsE 4 ↥H := hE4
  have hH_el : IsElemAbelian 2 H := by
    have h := (isElemAbelian_map (Subgroup.subtype_injective H) 2 (⊤ : Subgroup ↥H)).mpr hE4H.1
    rwa [map_subtype_top_eq H] at h
  have hHcard : Nat.card ↥H = 16 := by
    rw [hE4H.2]; norm_num
  have hσ'H : s.fr'.σ ∈ H := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hσ'2 : s.fr'.σ ^ 2 = 1 := hH_el.2 s.fr'.σ hσ'H
  have hσ'ne1 : s.fr'.σ ≠ 1 := fun h => hσ'notF (h ▸ one_mem _)
  have horderσ : orderOf s.fr'.σ = 2 := orderOf_eq_prime hσ'2 hσ'ne1
  have hcardZp : Nat.card ↥(zpowers s.fr'.σ) = 2 := by rw [Nat.card_zpowers, horderσ]
  have hH_eq : H = s.fr'.F ⊔ zpowers s.fr'.σ := by rw [Subgroup.zpowers_eq_closure]
  have hcomm : ∀ a ∈ s.fr'.F, ∀ b ∈ zpowers s.fr'.σ, a * b = b * a := by
    intro a ha b hb
    haveI : IsMulCommutative ↥H := hH_el.1
    have hb' : b ∈ closure {s.fr'.σ} := by rwa [Subgroup.zpowers_eq_closure] at hb
    have hHa : a ∈ H := Subgroup.mem_sup_left ha
    have hHb : b ∈ H := Subgroup.mem_sup_right hb'
    exact congrArg Subtype.val (mul_comm' (⟨a, hHa⟩ : ↥H) ⟨b, hHb⟩)
  have hF_max : s.fr'.F ∈ maxElemAbelian (s.fr'.A ⊓ s.fr'.B) := by
    rw [h14.2.2.2.1.2.2.1]
    simp
  have hF'_el : IsElemAbelian 2 s.fr'.F := hF_max.2.1
  have hF'_le_H : s.fr'.F ≤ H := le_sup_left
  have hF'_dvd : Nat.card ↥s.fr'.F ∣ 16 := by
    have := Subgroup.card_dvd_of_le hF'_le_H
    rwa [hHcard] at this
  have hF'_ne_H : s.fr'.F ≠ H := fun h => hσ'notF (h ▸ hσ'H)
  have hF'_card_ne : Nat.card ↥s.fr'.F ≠ 16 := by
    intro hc
    exact hF'_ne_H (Subgroup.eq_of_le_of_card_ge hF'_le_H (by rw [hc, hHcard]))
  have hF'_ge : 8 ≤ Nat.card ↥s.fr'.F := by
    have hle := card_sup_le_of_commute' (A := s.fr'.F) (B := zpowers s.fr'.σ) hcomm
    rw [← hH_eq, hHcard, hcardZp] at hle
    omega
  have hF'_card : Nat.card ↥s.fr'.F = 8 := by
    obtain ⟨d, hd⟩ := hF'_dvd
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd
    have hd1 : d ≠ 1 := by
      rintro rfl
      exact hF'_card_ne (by simpa using hd.symm)
    have hd2 : 2 ≤ d := by
      have : 0 < d := Nat.pos_of_ne_zero hd0
      omega
    have h8 : Nat.card ↥s.fr'.F * 2 ≤ 16 := by
      calc Nat.card ↥s.fr'.F * 2 ≤ Nat.card ↥s.fr'.F * d := Nat.mul_le_mul_left _ hd2
        _ = 16 := hd.symm
    omega
  have hF'_el_top : IsElemAbelian 2 (⊤ : Subgroup ↥s.fr'.F) := by
    refine (isElemAbelian_map (Subgroup.subtype_injective s.fr'.F) 2
      (⊤ : Subgroup ↥s.fr'.F)).mp ?_
    rwa [map_subtype_top_eq s.fr'.F]
  have hF'_isE : IsE 3 ↥s.fr'.F := by
    refine ⟨hF'_el_top, ?_⟩
    rw [hF'_card]; norm_num
  have hF_le_S : s.fr.F ≤ s.fr.S := (s3_F_le_A s).trans (s3_A_le_S s)
  have hF_le_N : s.fr.F ≤ normalizer (L : Set G) := hF_le_S.trans (s3_S_le_N s)
  have hcomp : jOn L hF_le_N =
      (jOn L (s3_S_le_N s)).comp (Subgroup.inclusion hF_le_S) :=
    MonoidHom.ext fun x => congrArg (jHom L) (Subtype.ext rfl)
  have hfinj : Function.Injective (jOn L hF_le_N) := by
    rw [hcomp]
    exact (s3_jOn_S_injective s hS hZ).comp (Subgroup.inclusion_injective hF_le_S)
  have hrange : (jOn L hF_le_N).range = s.fr'.F := by
    rw [range_jOn, s3_jSub_F hS hZ s]
  have hmap : IsE 3 ↥((⊤ : Subgroup ↥s.fr.F).map (jOn L hF_le_N)) := by
    rw [← MonoidHom.range_eq_map (jOn L hF_le_N), hrange]
    exact hF'_isE
  have htop : IsE 3 ↥(⊤ : Subgroup ↥s.fr.F) := (isE_map hfinj 3 ⊤).mp hmap
  exact (isE_equiv (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥s.fr.F) ≃* ↥s.fr.F) 3).mp htop

end CFSG.OddStandard.HigherRank.YamadaG23
