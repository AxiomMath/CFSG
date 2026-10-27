module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.CentralWeak

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

namespace Setup

variable (S : Setup L z t F L1 N)

include S

theorem not_isConj_z_mul (hFix : FixFour L F) {d l : G} (hd : d ∈ normalizer (F : Set G) ⊓ L)
    (hdF : d ∉ F) (hl : l ∈ L1) (h2 : d * l * (d * l) = 1) : ¬ IsConj z (d * l) := by
  have hdX : d ∈ normalizer (L1 : Set G) := S.D_le_X hd
  have hdz : d * z = z * d := (S.one.z_comm d (mem_inf.1 hd).2).symm
  have hdL : d * d ∈ L := L.mul_mem (mem_inf.1 hd).2 (mem_inf.1 hd).2
  have hd2 : d * d ∈ F := S.sq_mem_F_of_involution hdX hdL hl h2
  have hdN : ∀ x, x ∈ F ↔ d * x * d⁻¹ ∈ F := Subgroup.mem_normalizer_iff.1 (mem_inf.1 hd).1
  have hg2F : ∀ x ∈ F, d * d * x = x * (d * d) := fun x hx =>
    S.nd.F_comm _ hd2 x hx
  have hF4 : Nat.card F = Nat.card ↥(F ⊓ centralizer ({d} : Set G)) ^ 2 := by
    have hup := hFix d hd hdF hd2
    have hlow := card_le_sq_card_centralizer S.nd.F_comm S.nd.F_sq hdN hg2F
    rw [S.nd.F_card] at hlow ⊢
    nlinarith
  have hL16 := S.card_centralizer_L1_eq hdX hdz hd2 (hFix d hd hdF hd2)
  have hL1c : Nat.card L1 = Nat.card ↥(L1 ⊓ centralizer ({d} : Set G)) ^ 2 := by
    rw [S.L1_card, hL16]
    norm_num
  have hg2L : ∀ x ∈ L1, d * d * x = x * (d * d) := fun x hx =>
    S.L1_comm _ (S.F_le hd2) x hx
  have hdL1 : ∀ x, x ∈ L1 ↔ d * x * d⁻¹ ∈ L1 := Subgroup.mem_normalizer_iff.1 hdX
  have hli : l * l = 1 := S.L1_sq l hl
  have hdl : d * l * d = l := by
    have h1 : d * l * d * l = 1 := by
      calc d * l * d * l = d * l * (d * l) := by group
        _ = 1 := h2
    calc d * l * d = (d * l * d * l) * l⁻¹ := by group
      _ = l := by rw [h1, one_mul, inv_eq_of_mul_eq_one_right hli]
  have hinv : (d * d)⁻¹ ∈ F := Subgroup.inv_mem _ hd2
  obtain ⟨f₀, hf₀, hθ⟩ := exists_eq_mul_conj_of_card_eq S.nd.F_comm S.nd.F_sq hdN hg2F hF4 hinv
    (by group)
  have hf₀L1 : f₀ ∈ L1 := S.F_le hf₀
  have hf₀2 : f₀ * f₀ = 1 := S.nd.F_sq f₀ hf₀
  have hu2 : d * f₀ * (d * f₀) = 1 := by
    calc d * f₀ * (d * f₀) = d * (f₀ * (d * f₀ * d⁻¹)) * d := by group
      _ = d * (d * d)⁻¹ * d := by rw [hθ]
      _ = 1 := by group
  have hfd : d * f₀ * d = f₀ := by
    calc d * f₀ * d = (d * f₀ * d * f₀) * f₀⁻¹ := by group
      _ = f₀ := by
        rw [show d * f₀ * d * f₀ = 1 from by
          calc d * f₀ * d * f₀ = d * f₀ * (d * f₀) := by group
            _ = 1 := hu2, one_mul, inv_eq_of_mul_eq_one_right hf₀2]
  have hdl' : d⁻¹ * l = l * d := by
    calc d⁻¹ * l = d⁻¹ * (d * l * d) := by rw [hdl]
      _ = l * d := by group
  have hcomm : f₀ * l * d = d * (f₀ * l) := by
    calc f₀ * l * d = f₀ * (l * d) := by group
      _ = (d * f₀ * d) * (d⁻¹ * l) := by rw [hfd, hdl']
      _ = d * (f₀ * l) := by group
  obtain ⟨m, hm, hmθ⟩ := exists_eq_mul_conj_of_card_eq S.L1_comm S.L1_sq hdL1 hg2L hL1c
    (L1.mul_mem hf₀L1 hl) hcomm
  have hn : d * m * d⁻¹ ∈ L1 := (hdL1 m).1 hm
  have hmi : m⁻¹ = m := inv_eq_of_mul_eq_one_right (S.L1_sq m hm)
  have hn' : d⁻¹ * m * d = d * m * d⁻¹ := by
    have h1 := hg2L _ hn
    calc d⁻¹ * m * d = (d * d)⁻¹ * (d * m * d⁻¹) * (d * d) := by group
      _ = (d * m * d⁻¹) := by
        rw [show (d * d)⁻¹ * (d * m * d⁻¹) * (d * d) = (d * d)⁻¹ * ((d * d) * (d * m * d⁻¹)) from by
          rw [h1]; group]
        group
  have key : m * (d * f₀) * m⁻¹ = d * l := by
    calc m * (d * f₀) * m⁻¹ = d * (d⁻¹ * m * d) * f₀ * m⁻¹ := by group
      _ = d * (d * m * d⁻¹) * f₀ * m := by rw [hn', hmi]
      _ = d * (f₀ * ((d * m * d⁻¹) * m)) := by
        rw [show d * (d * m * d⁻¹) * f₀ * m = d * ((d * m * d⁻¹) * f₀ * m) from by group,
          S.L1_comm _ hn f₀ hf₀L1]
        group
      _ = d * (f₀ * (m * (d * m * d⁻¹))) := by rw [S.L1_comm _ hn m hm]
      _ = d * (f₀ * (f₀ * l)) := by rw [hmθ]
      _ = d * ((f₀ * f₀) * l) := by group
      _ = d * l := by rw [hf₀2, one_mul]
  have hu : d * f₀ ∈ L := L.mul_mem (mem_inf.1 hd).2 (S.nd.F_le hf₀)
  have hu1 : d * f₀ ≠ 1 := by
    intro h
    apply hdF
    have : d = f₀⁻¹ := by
      calc d = (d * f₀) * f₀⁻¹ := by group
        _ = f₀⁻¹ := by rw [h, one_mul]
    rw [this]
    exact Subgroup.inv_mem _ hf₀
  intro hcz
  exact S.one.not_isConj_z_of_mem hu hu2 hu1 (hcz.trans (isConj_iff.2 ⟨m, key⟩).symm)

omit [Finite G] in
theorem relIndex_inf_preimageY {M : Subgroup (Ybar L1)} (hM : M.index = 2)
    (hz0 : piY L1 S.zX ∉ M) {P : Subgroup G} (hPX : P ≤ normalizer (L1 : Set G)) (hzP : z ∈ P) :
    (P ⊓ preimageY L1 M).relIndex P = 2 := by
  refine Subgroup.index_eq_two_iff.2 ⟨⟨z, hzP⟩, fun b => ?_⟩
  have hbX : (b : G) ∈ normalizer (L1 : Set G) := hPX b.2
  have hbzX : (b : G) * z ∈ normalizer (L1 : Set G) :=
    (normalizer (L1 : Set G)).mul_mem hbX S.zX.2
  have key : ((b : G) * z ∈ preimageY L1 M) ↔ ¬ ((b : G) ∈ preimageY L1 M) := by
    rw [mem_preimageY_iff hbzX, mem_preimageY_iff hbX]
    have : piY L1 ⟨(b : G) * z, hbzX⟩ = piY L1 ⟨(b : G), hbX⟩ * piY L1 S.zX := rfl
    rw [this, Subgroup.mul_mem_iff_of_index_two hM]
    exact ⟨fun h h' => hz0 (h.1 h'), fun h => ⟨fun h' => absurd h' h, fun h' => absurd h' hz0⟩⟩
  show Xor (b * ⟨z, hzP⟩ ∈ (P ⊓ preimageY L1 M).subgroupOf P)
    (b ∈ (P ⊓ preimageY L1 M).subgroupOf P)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, mem_inf]
  by_cases hB : (b : G) ∈ preimageY L1 M
  · exact Or.inr ⟨⟨b.2, hB⟩, fun h => key.1 h.2 hB⟩
  · exact Or.inl ⟨⟨P.mul_mem b.2 hzP, key.2 hB⟩, fun h => hB h.2⟩

theorem false_of_central [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hFix : FixFour L F) (hA7 : NormQuotA7 (normalizer (F : Set G) ⊓ L) F)
    (hL2 : ¬ 256 ∣ Nat.card L) (hnc : ∀ x ∈ L1, ¬ IsConj z x)
    (hcen : ∀ y : Ybar L1, y * piY L1 S.zX = piY L1 S.zX * y) : False := by
  have hz2 : z * z = 1 := S.one.z_mul_self
  have hz1 : z ≠ 1 := S.one.z_ne_one
  have hz2' : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  obtain ⟨P, hP, hzP, hT⟩ := S.exists_sylow_X hL2
  have hPX : P ≤ normalizer (L1 : Set G) := hP.le
  have hL1P : L1 ≤ P := S.L1_le_of_isSylowOf hP
  have hwc := S.weakly_closed hFix hA7 hL2 hcen hP hT
  have hSyl : ¬ 2 ∣ P.index := not_dvd_index_of_weakly_closed hP.isPGroup hL1P hwc hPX hP
  have hnot := S.zbar_not_mem_Nbar hA7
  have hidx := S.relIndex_inf_preimageY (S.Nbar_index_eq_two hA7 hcen) hnot hPX hzP
  have hz0 : z ∉ P ⊓ preimageY L1 (Nbar L F L1) := fun h =>
    hnot ((mem_preimageY_iff S.zX.2).1 (mem_inf.1 h).2)
  obtain ⟨g, hg⟩ := exists_conj_mem_complement hnonab hP.isPGroup hSyl inf_le_left hidx hzP hz0
    hz2'
  obtain ⟨hyP, hyM⟩ := mem_inf.1 hg
  obtain ⟨hyX, hyN⟩ := mem_preimageY.1 hyM
  have hconj : IsConj z (g⁻¹ * z * g) := isConj_iff.2 ⟨g⁻¹, by group⟩
  have hy2 : g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  obtain ⟨d, hd, l, hl, hyd⟩ := S.exists_eq_mul_of_mem_sylowX hcen hP hT hyP
  have hdX : d ∈ normalizer (L1 : Set G) := S.D_le_X hd
  rcases hyd with hyd | hyd
  · by_cases hdF : d ∈ F
    · exact hnc _ (hyd ▸ L1.mul_mem (S.F_le hdF) hl) hconj
    · exact S.not_isConj_z_mul hFix hd hdF hl (hyd ▸ hy2) (hyd ▸ hconj)
  · have hlX : l ∈ normalizer (L1 : Set G) := Subgroup.le_normalizer hl
    have hπ : piY L1 ⟨g⁻¹ * z * g, hyX⟩ = piY L1 S.zX * piY L1 ⟨d, hdX⟩ := by
      have : (⟨g⁻¹ * z * g, hyX⟩ : ↥(normalizer (L1 : Set G))) =
          S.zX * ⟨d, hdX⟩ * ⟨l, hlX⟩ := Subtype.ext hyd
      rw [this, map_mul, map_mul, S.piY_eq_one_of_mem_L1 hl hlX, mul_one]
    have hπd : piY L1 ⟨d, hdX⟩ ∈ Nbar L F L1 := mem_Nbar_iff.2 ⟨⟨d, hdX⟩, hd, rfl⟩
    apply hnot
    have := Subgroup.mul_mem _ hyN (Subgroup.inv_mem _ hπd)
    rw [hπ] at this
    simpa using this

end Setup

end CFSG.EvenSporadicStandard.M23Std
