module

public import CFSG.GH74.GLS.C3.Layer1.Th2P85AltSE

public section

namespace CFSG.GH74.GLS.Th2.P85.Sp

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.Th2.P85.Alt CFSG.GH74.GLS.TwoThin

section Cent

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_centralizer_conj (x g : G) :
    Nat.card ↥(centralizer ({g⁻¹ * x * g} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) := by
  have h := Stage1.Thm2.Recip.map_centralizer_singleton_conj x g⁻¹
  rw [inv_inv] at h
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

theorem two_adic_dom {M : Subgroup G} {x w : G} (hxM : x ∈ M) (hwM : w ∈ M)
    (hx2 : orderOf x = 2) (hw2 : orderOf w = 2) (hCx : centralizer ({x} : Set G) ≤ M)
    (hcard : Nat.card ↥(centralizer ({w} : Set G)) = Nat.card ↥(centralizer ({x} : Set G))) :
    ∀ k : ℕ, 2 ^ k ∣ Nat.card ↥(centralizer ({barMk ↥M ⟨w, hwM⟩} : Set (Mb M)) ⊓ ⊤) →
      2 ^ k ∣ Nat.card ↥(centralizer ({barMk ↥M ⟨x, hxM⟩} : Set (Mb M)) ⊓ ⊤) := by
  intro k hk
  rw [inf_top_eq] at hk ⊢
  obtain ⟨rw, hrw, hw⟩ := card_centralizer_barMk (M := M)
    (show orderOf (⟨w, hwM⟩ : ↥M) = 2 from (Subgroup.orderOf_mk w hwM).trans hw2)
  obtain ⟨rx, hrx, hx⟩ := card_centralizer_barMk (M := M)
    (show orderOf (⟨x, hxM⟩ : ↥M) = 2 from (Subgroup.orderOf_mk x hxM).trans hx2)
  have h1 : 2 ^ k ∣ Nat.card ↥(centralizer ({(⟨w, hwM⟩ : ↥M)} : Set ↥M)) := by
    rw [hw]
    exact hk.mul_left rw
  have h2 : Nat.card ↥(centralizer ({(⟨w, hwM⟩ : ↥M)} : Set ↥M)) ∣
      Nat.card ↥(centralizer ({w} : Set G)) := by
    have hsub : centralizer ({(⟨w, hwM⟩ : ↥M)} : Set ↥M) =
        (centralizer ({w} : Set G)).subgroupOf M := by
      ext c
      rw [mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    have h4 : Nat.card ↥((centralizer ({w} : Set G)).subgroupOf M) =
        Nat.card ↥(centralizer ({w} : Set G) ⊓ M) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective M.subtype_injective]
    rw [hsub, h4]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h3 : 2 ^ k ∣ Nat.card ↥(centralizer ({x} : Set G)) := hcard ▸ h1.trans h2
  rw [card_centralizer_of_le hxM hCx, hx] at h3
  have hcop : Nat.Coprime (2 ^ k) rx := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hrx)
  exact hcop.dvd_of_dvd_mul_left h3

theorem exists_odd_normal_seven {M : Subgroup G} {x w g : G} (hxM : x ∈ M) (hwM : w ∈ M)
    (hw2 : orderOf w = 2) (hCx : centralizer ({x} : Set G) ≤ M) (hg : g * w * g⁻¹ = x)
    (hY : Nat.card ↥(centralizer ({barMk ↥M ⟨x, hxM⟩} : Set (Mb M))) = 480)
    (hZ7 : 7 ∣ Nat.card ↥(centralizer ({barMk ↥M ⟨w, hwM⟩} : Set (Mb M)))) :
    ∃ R : Subgroup (Mb M), R ≤ centralizer ({barMk ↥M ⟨w, hwM⟩} : Set (Mb M)) ∧
      (∀ z ∈ centralizer ({barMk ↥M ⟨w, hwM⟩} : Set (Mb M)), ∀ r ∈ R, z * r * z⁻¹ ∈ R) ∧
      Odd (Nat.card ↥R) ∧ 7 ∣ Nat.card ↥R := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set w' : ↥M := ⟨w, hwM⟩ with hw'
  set x' : ↥M := ⟨x, hxM⟩ with hx'
  have hw'2 : orderOf w' = 2 := (Subgroup.orderOf_mk w hwM).trans hw2
  have hconj : ∀ a : G, a * w = w * a → g * a * g⁻¹ ∈ centralizer ({x} : Set G) := by
    intro a ha
    rw [mem_centralizer_singleton_iff, ← hg]
    calc g * a * g⁻¹ * (g * w * g⁻¹) = g * (a * w) * g⁻¹ := by group
      _ = g * (w * a) * g⁻¹ := by rw [ha]
      _ = g * w * g⁻¹ * (g * a * g⁻¹) := by group
  set N₁ : Subgroup G := centralizer ({w} : Set G) ⊓ M ⊓
    (pPrimeCoreOf 2 M).comap (MulAut.conj g).toMonoidHom with hN₁
  have hmemN₁ : ∀ b : G, b ∈ N₁ ↔ b ∈ centralizer ({w} : Set G) ∧ b ∈ M ∧
      g * b * g⁻¹ ∈ pPrimeCoreOf 2 M := fun b => by
    simp only [hN₁, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    tauto
  have hN₁M : N₁ ≤ M := fun b hb => ((hmemN₁ b).1 hb).2.1
  have hN₁norm : ∀ c : G, c ∈ M → c * w = w * c → ∀ b ∈ N₁, c * b * c⁻¹ ∈ N₁ := by
    intro c hcM hcw b hb
    obtain ⟨hbw, hbM, hbO⟩ := (hmemN₁ b).1 hb
    refine (hmemN₁ _).2 ⟨?_, M.mul_mem (M.mul_mem hcM hbM) (M.inv_mem hcM), ?_⟩
    · rw [mem_centralizer_singleton_iff] at hbw ⊢
      have hcw' : c⁻¹ * w = w * c⁻¹ := by
        calc c⁻¹ * w = c⁻¹ * (w * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * w) * c⁻¹ := by rw [hcw]
          _ = w * c⁻¹ := by group
      calc c * b * c⁻¹ * w = c * b * (c⁻¹ * w) := by group
        _ = c * b * (w * c⁻¹) := by rw [hcw']
        _ = c * (b * w) * c⁻¹ := by group
        _ = c * (w * b) * c⁻¹ := by rw [hbw]
        _ = w * (c * b * c⁻¹) := by
          calc c * (w * b) * c⁻¹ = (c * w) * b * c⁻¹ := by group
            _ = (w * c) * b * c⁻¹ := by rw [hcw]
            _ = w * (c * b * c⁻¹) := by group
    · have hgcM : g * c * g⁻¹ ∈ M := hCx (hconj c hcw)
      have h1 : g * (c * b * c⁻¹) * g⁻¹ =
          (g * c * g⁻¹) * (g * b * g⁻¹) * (g * c * g⁻¹)⁻¹ := by group
      rw [h1]
      have hcn : g * c * g⁻¹ ∈ normalizer (pPrimeCoreOf 2 M : Set G) :=
        TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hgcM)
      exact (Subgroup.mem_normalizer_iff.1 hcn _).1 hbO
  obtain ⟨ζ, hζ⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(centralizer ({barMk ↥M w'} : Set (Mb M)))) 7 hZ7
  obtain ⟨a, ha⟩ := barMkCentralizer_surjective hw'2 ζ
  have hbarA : barMk ↥M (a : ↥M) = (ζ : Mb M) := by
    have h := barMkCentralizer_apply hw'2 a
    rw [ha] at h
    exact h.symm
  have hawG : ((a : ↥M) : G) * w = w * ((a : ↥M) : G) :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.1 a.2)
  set b₀ : ↥M := (a : ↥M) ^ 480 with hb₀
  have hb₀coe : (b₀ : G) = ((a : ↥M) : G) ^ 480 := by rw [hb₀]; rfl
  have hb₀w : (b₀ : G) * w = w * (b₀ : G) := by
    rw [hb₀coe]
    exact ((Commute.pow_left (show Commute ((a : ↥M) : G) w from hawG) 480)).eq
  have hgaM : g * ((a : ↥M) : G) * g⁻¹ ∈ M := hCx (hconj _ hawG)
  set ga : ↥M := ⟨g * ((a : ↥M) : G) * g⁻¹, hgaM⟩ with hga
  have hgax : ga * x' = x' * ga := Subtype.ext (mem_centralizer_singleton_iff.1 (hconj _ hawG))
  have hy0mem : barMk ↥M ga ∈ centralizer ({barMk ↥M x'} : Set (Mb M)) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hgax]
  have hy0pow : (barMk ↥M ga) ^ 480 = 1 := by
    have h1 := pow_card_eq_one'
      (x := (⟨barMk ↥M ga, hy0mem⟩ : ↥(centralizer ({barMk ↥M x'} : Set (Mb M)))))
    rw [hY] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  have hb₀gM : g * (b₀ : G) * g⁻¹ ∈ M := by
    have : g * (b₀ : G) * g⁻¹ = ((ga : ↥M) : G) ^ 480 := by
      rw [hb₀coe, hga]
      exact (conj_pow).symm
    rw [this]
    exact M.pow_mem ga.2 480
  have hb₀O : g * (b₀ : G) * g⁻¹ ∈ pPrimeCoreOf 2 M := by
    have heq : (⟨g * (b₀ : G) * g⁻¹, hb₀gM⟩ : ↥M) = ga ^ 480 := by
      apply Subtype.ext
      show g * (b₀ : G) * g⁻¹ = ((ga ^ 480 : ↥M) : G)
      rw [hb₀coe, Subgroup.coe_pow]
      exact (conj_pow).symm
    refine (barMk_eq_one_iff_mem_pPrimeCoreOf ⟨_, hb₀gM⟩).1 ?_
    rw [heq, map_pow, hy0pow]
  have hb₀N : (b₀ : G) ∈ N₁ :=
    (hmemN₁ _).2 ⟨mem_centralizer_singleton_iff.2 hb₀w, b₀.2, hb₀O⟩
  have hRle : imgM M N₁ ≤ centralizer ({barMk ↥M w'} : Set (Mb M)) := by
    intro r hr
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hr
    have hmw := mem_centralizer_singleton_iff.1 ((hmemN₁ _).1 hm).1
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hmw
  have hRnorm : ∀ z ∈ centralizer ({barMk ↥M w'} : Set (Mb M)), ∀ r ∈ imgM M N₁,
      z * r * z⁻¹ ∈ imgM M N₁ := by
    intro z hz r hr
    obtain ⟨⟨c, hcC⟩, hcz⟩ := barMkCentralizer_surjective hw'2 ⟨z, hz⟩
    have hcz' : barMk ↥M c = z := by
      have h := barMkCentralizer_apply hw'2 ⟨c, hcC⟩
      rw [hcz] at h
      exact h.symm
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hr
    have hcw : (c : G) * w = w * (c : G) :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 hcC)
    refine mem_imgM_iff.2 ⟨c * m * c⁻¹, ?_, ?_⟩
    · have := hN₁norm (c : G) c.2 hcw (m : G) hm
      simpa using this
    · rw [← hcz', map_mul, map_mul, map_inv]
  refine ⟨imgM M N₁, hRle, hRnorm, ?_, ?_⟩
  · have hodd1 : Odd (Nat.card ↥N₁) := by
      let φ : ↥N₁ →* ↥(pPrimeCoreOf 2 M) :=
        ((MulAut.conj g).toMonoidHom.comp N₁.subtype).codRestrict (pPrimeCoreOf 2 M)
          (fun b => ((hmemN₁ b).1 b.2).2.2)
      have hφ : Function.Injective φ := fun b c h =>
        Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))
      exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd M) (Subgroup.card_dvd_of_injective φ hφ)
    have hmap : Nat.card ↥(imgM M N₁) ∣ Nat.card ↥(N₁.subgroupOf M) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥(N₁.subgroupOf M) = Nat.card ↥N₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₁M).toEquiv
    exact Odd.of_dvd_nat hodd1 (h2 ▸ hmap)
  · have hmem : barMk ↥M b₀ ∈ imgM M N₁ := mem_imgM_iff.2 ⟨b₀, hb₀N, rfl⟩
    have hζo : orderOf (ζ : Mb M) = 7 := (Subgroup.orderOf_coe ζ).trans hζ
    have hpow := orderOf_pow' (x := (ζ : Mb M)) (n := 480) (by norm_num)
    rw [hζo] at hpow
    have hr7 : orderOf (barMk ↥M b₀) = 7 := by
      rw [hb₀, map_pow, hbarA, hpow]
      norm_num
    have := Subgroup.orderOf_dvd_natCard (imgM M N₁) hmem
    rwa [hr7] at this

end Cent

end CFSG.GH74.GLS.Th2.P85.Sp
