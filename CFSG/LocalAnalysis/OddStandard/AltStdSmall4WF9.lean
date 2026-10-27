module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4CentCard
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4WF9Wreath
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTransfer

public section

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup

namespace WF9

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

theorem card_le_of_isPGroup (c : Config G L Q n θ z) (hin : IsASmall L n z) {W : Subgroup G}
    (hW : IsPGroup 2 W) (hWC : W ≤ centralizer ({z} : Set G)) : Nat.card W ≤ 128 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW' : IsPGroup 2 (W.subgroupOf (centralizer ({z} : Set G))) :=
    hW.of_equiv (subgroupOfEquivOfLe hWC).symm
  obtain ⟨P, hP⟩ := hW'.exists_le_sylow
  have h1 := (sec4CentSylowCard_holds G L Q n θ z c P).1 hin
  calc Nat.card W = Nat.card (W.subgroupOf (centralizer ({z} : Set G))) :=
        Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv.symm
    _ ≤ Nat.card P := card_le_of_le hP
    _ = 128 := by rw [h1]; norm_num

theorem not_conj_mem (c : Config G L Q n θ z) (hin : IsASmall L n z) (hzz : z * z = 1)
    {B : Subgroup G} (hBp : IsPGroup 2 B)
    (hB : ∀ x ∈ B, x * x = 1 → 256 ≤ Nat.card (B ⊓ centralizer ({x} : Set G) : Subgroup G))
    (g : G) : g⁻¹ * z * g ∉ B := by
  intro hg
  have hx2 : g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hzz]; group
  have h256 := hB _ hg hx2
  have hWC : (B ⊓ centralizer ({g⁻¹ * z * g} : Set G)).map (MulAut.conj g).toMonoidHom ≤
      centralizer ({z} : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    have hwx := mem_centralizer_singleton_iff.1 (mem_inf.1 hw).2
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * w * g⁻¹ * z = g * (w * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * w) * g⁻¹ := by rw [hwx]
      _ = z * (g * w * g⁻¹) := by group
  have h128 := card_le_of_isPGroup c hin
    ((hBp.to_le inf_le_left).map (MulAut.conj g).toMonoidHom) hWC
  rw [card_map_of_injective (MulAut.conj g).injective] at h128
  omega

end WF9

open WF9 in
theorem sec4WreathFalseSmall_holds :
    ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
      (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
        IsASmall L n z → HData θ c.hn8 z T → WreathStruct z T → False := by
  intro G _ _ L Q n θ z c T hin hH hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := c.ot.std.simple
  obtain ⟨K₁, F₁, hK₁N, hcomm, hinter, hE8, -, hF₁K, hF₁T, -, hF168, hcent, -, -⟩ :=
    hW.exists_factor
  have hzz : z * z = 1 := by rw [← pow_two, ← c.ot.cyc.order, pow_orderOf_eq_one]
  obtain ⟨D₁, hD₁8, -, hD₁F⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two (n := 3)
    (H := ⊥) (L := F₁) (by rw [card_bot]; exact one_dvd _) (by rw [hF168]; norm_num) bot_le
  have hD₁K : D₁ ≤ K₁ := hD₁F.trans hF₁K
  have hA : AffData (K₁ ⊓ T) D₁ :=
    { sq := fun e he => by rw [← pow_two]; exact hH.elem e (mem_inf.1 he).2
      cardE := hE8
      cardD := by rw [hD₁8]; norm_num
      norm := fun d hd => by
        have hdK := hD₁K hd
        rw [mem_normalizer_iff]
        intro x
        rw [mem_inf, mem_inf, ← mem_normalizer_iff.1 (hK₁N hdK) x]
        constructor
        · rintro ⟨hxK, hxT⟩
          exact ⟨mul_mem (mul_mem hdK hxK) (inv_mem hdK), hxT⟩
        · rintro ⟨hxK, hxT⟩
          refine ⟨?_, hxT⟩
          have h : x = d⁻¹ * (d * x * d⁻¹) * d := by group
          rw [h]
          exact mul_mem (mul_mem (inv_mem hdK) hxK) hdK
      inf := eq_bot_iff.2 fun x hx => by
        have h : x ∈ F₁ ⊓ T :=
          mem_inf.2 ⟨hD₁F (mem_inf.1 hx).2, (mem_inf.1 (mem_inf.1 hx).1).2⟩
        rwa [hF₁T] at h
      faith := fun d hd hde => by
        have h1 : d ∈ centralizer ((K₁ ⊓ T : Subgroup G) : Set G) ⊓ K₁ :=
          mem_inf.2 ⟨mem_centralizer_iff.2 fun e he => (hde e he).symm, hD₁K hd⟩
        rw [hcent] at h1
        have h2 : d ∈ F₁ ⊓ T := mem_inf.2 ⟨hD₁F hd, (mem_inf.1 h1).2⟩
        rwa [hF₁T, mem_bot] at h2 }
  have hE2 : IsPGroup 2 (K₁ ⊓ T : Subgroup G) := IsPGroup.of_card (n := 3) (by rw [hE8]; norm_num)
  have hR2 : IsPGroup 2 (K₁ ⊓ T ⊔ D₁ : Subgroup G) :=
    hE2.to_sup_of_normal_left' (IsPGroup.of_card hD₁8) hA.norm
  have hRK : (K₁ ⊓ T ⊔ D₁ : Subgroup G) ≤ K₁ := sup_le inf_le_left hD₁K
  have hRzK : conjSub z (K₁ ⊓ T ⊔ D₁) ≤ conjSub z K₁ := map_mono hRK
  have hWr : WrData (K₁ ⊓ T ⊔ D₁) z :=
    { sq := hzz
      comm := fun a ha b hb => hcomm a (hRK ha) b (hRzK hb)
      inf := eq_bot_iff.2 fun x hx => by
        have h : x ∈ K₁ ⊓ conjSub z K₁ :=
          mem_inf.2 ⟨hRK (mem_inf.1 hx).1, hRzK (mem_inf.1 hx).2⟩
        rwa [hinter] at h
      not_mem := fun hz => by
        have hzK : z ∈ K₁ ⊔ conjSub z K₁ := sup_le_sup hRK hRzK hz
        have hle : K₁ ⊔ conjSub z K₁ ≤ normalizer (K₁ : Set G) :=
          sup_le le_normalizer fun b hb =>
            centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha => hcomm a ha b hb)
        have hzN := hle hzK
        have hKK : K₁ ≤ conjSub z K₁ := fun k hk => by
          have h1 : z⁻¹ * k * z ∈ K₁ := (mem_normalizer_iff''.1 hzN k).1 hk
          have h2 := conj_mem_conjSub (z := z) h1
          rwa [show z * (z⁻¹ * k * z) * z⁻¹ = k by group] at h2
        have hbot : K₁ = ⊥ := by
          rw [eq_bot_iff, ← hinter]
          exact le_inf le_rfl hKK
        have h := hE8
        rw [hbot, bot_inf_eq, card_bot] at h
        omega }
  have hTHp := hWr.isPGroup_top hR2
  have hnc := not_conj_mem c hin hzz (hTHp.to_le le_sup_left) fun x hx hx2 =>
    hWr.card_cent_ge (fun a ha ha2 => hA.card_centralizer_ge ha ha2) hx hx2
  by_cases hidx : 2 ∣ (K₁ ⊓ T ⊔ D₁ ⊔ conjSub z (K₁ ⊓ T ⊔ D₁) ⊔ zpowers z : Subgroup G).index
  ·
    obtain ⟨P, hTHP⟩ := hTHp.exists_le_sylow
    have hne : (K₁ ⊓ T ⊔ D₁ ⊔ conjSub z (K₁ ⊓ T ⊔ D₁) ⊔ zpowers z : Subgroup G).subgroupOf
        (P : Subgroup G) ≠ ⊤ := by
      intro htop
      have hPTH : (P : Subgroup G) ≤
          K₁ ⊓ T ⊔ D₁ ⊔ conjSub z (K₁ ⊓ T ⊔ D₁) ⊔ zpowers z := fun x hx => by
        have h : (⟨x, hx⟩ : P) ∈ (K₁ ⊓ T ⊔ D₁ ⊔ conjSub z (K₁ ⊓ T ⊔ D₁) ⊔ zpowers z :
            Subgroup G).subgroupOf (P : Subgroup G) := by
          rw [htop]
          trivial
        exact mem_subgroupOf.1 h
      have h := le_antisymm hTHP hPTH
      exact P.not_dvd_index (h ▸ hidx)
    have hnil : Group.IsNilpotent P := P.isPGroup'.isNilpotent
    have hlt := Group.normalizerCondition_of_isNilpotent (G := P) _ (lt_of_le_of_ne le_top hne)
    obtain ⟨⟨y, hyP⟩, hyN, hyTH⟩ := SetLike.exists_of_lt hlt
    have hyN' : y ∈ normalizer ((K₁ ⊓ T ⊔ D₁ ⊔ conjSub z (K₁ ⊓ T ⊔ D₁) ⊔ zpowers z :
        Subgroup G) : Set G) := by
      have h : (⟨y, hyP⟩ : P) ∈ (normalizer ((K₁ ⊓ T ⊔ D₁ ⊔ conjSub z (K₁ ⊓ T ⊔ D₁) ⊔
          zpowers z : Subgroup G) : Set G)).subgroupOf (P : Subgroup G) := by
        rw [subgroupOf_normalizer_eq hTHP]
        exact hyN
      exact mem_subgroupOf.1 h
    have hyTH' : y ∉ K₁ ⊓ T ⊔ D₁ ⊔ conjSub z (K₁ ⊓ T ⊔ D₁) ⊔ zpowers z := fun h =>
      hyTH (mem_subgroupOf.2 h)
    have hxTH : y⁻¹ * z * y ∈ K₁ ⊓ T ⊔ D₁ ⊔ conjSub z (K₁ ⊓ T ⊔ D₁) ⊔ zpowers z :=
      (mem_normalizer_iff''.1 hyN' z).1 (mem_sup_right (mem_zpowers z))
    have hx2 : y⁻¹ * z * y * (y⁻¹ * z * y) = 1 := by
      calc y⁻¹ * z * y * (y⁻¹ * z * y) = y⁻¹ * (z * z) * y := by group
        _ = 1 := by rw [hzz]; group
    obtain ⟨b, hbR, hbx⟩ := hWr.exists_conj_of_not_mem hxTH (hnc y) hx2
    have hbTH : b ∈ K₁ ⊓ T ⊔ D₁ ⊔ conjSub z (K₁ ⊓ T ⊔ D₁) ⊔ zpowers z :=
      mem_sup_left (mem_sup_left hbR)
    have hybC : y * b ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc y * b * z = y * (b * z * b⁻¹) * b := by group
        _ = y * (y⁻¹ * z * y) * b := by rw [hbx]
        _ = z * (y * b) := by group
    have hybP : y * b ∈ (P : Subgroup G) := mul_mem hyP (hTHP hbTH)
    have hcardP := card_le_of_isPGroup c hin (P.isPGroup'.to_le inf_le_left)
      (inf_le_right : (P : Subgroup G) ⊓ centralizer ({z} : Set G) ≤ centralizer ({z} : Set G))
    have hcardTH := hWr.card_cent_z
    have hR64 := hA.card_sup_ge
    have heq : (K₁ ⊓ T ⊔ D₁ ⊔ conjSub z (K₁ ⊓ T ⊔ D₁) ⊔ zpowers z) ⊓
        centralizer ({z} : Set G) = (P : Subgroup G) ⊓ centralizer ({z} : Set G) :=
      eq_of_le_of_card_ge (inf_le_inf_right _ hTHP) (by omega)
    have hyb : y * b ∈ (K₁ ⊓ T ⊔ D₁ ⊔ conjSub z (K₁ ⊓ T ⊔ D₁) ⊔ zpowers z) ⊓
        centralizer ({z} : Set G) := by
      rw [heq]
      exact mem_inf.2 ⟨hybP, hybC⟩
    apply hyTH'
    have h : y = y * b * b⁻¹ := by group
    rw [h]
    exact mul_mem (mem_inf.1 hyb).1 (inv_mem hbTH)
  ·
    obtain ⟨g, hg, -, -⟩ :=
      CFSG.ComponentClassification.HarrisLit.HarrisEnd.exists_extremal_conj_of_relIndex_two
        c.ot.std.nonab hTHp hidx le_sup_left hWr.relIndex_base (mem_sup_right (mem_zpowers z))
        hWr.not_mem (by rw [pow_two]; exact hzz)
    exact hnc g hg

end CFSG.OddStandard.AltStdSmall4
