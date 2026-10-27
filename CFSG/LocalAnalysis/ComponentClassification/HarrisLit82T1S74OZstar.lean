module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74GZstar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74OSetup

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

namespace SetupOdd

variable {G : Type} [Group G] [Finite G] (S : SetupOdd G)

abbrev Y : Subgroup G := centralizer ({S.q₃} : Set G)

theorem odd_relIndex_L_inf {A : Subgroup G} (hAH : A ≤ S.H) : Odd ((S.L ⊓ A).relIndex A) := by
  let L' := S.L.subgroupOf S.H
  let A' := A.subgroupOf S.H
  have hL' : L'.Normal := ⟨fun n hn h => by
    rw [mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact S.hLn h h.2 n hn⟩
  have h1 : L'.relIndex (L' ⊔ A') = L'.relIndex A' := relIndex_sup_left A' L'
  have h2 : L'.relIndex (L' ⊔ A') ∣ L'.index := relIndex_dvd_index_of_le le_sup_left
  have h3 : L'.relIndex A' = S.L.relIndex A := relIndex_subgroupOf hAH
  have h4 : (S.L ⊓ A).relIndex A = S.L.relIndex A := inf_relIndex_right S.L A
  rw [h4, ← h3, ← h1]
  exact Odd.of_dvd_nat S.hodd h2

variable {iX : S.X} {S₀ B : Subgroup S.X}

abbrev iG (iX : S.X) : G := S.φ iX

theorem iG_facts (hI : IBarFacts S.K S.p iX) :
    S.iG iX * S.iG iX = 1 ∧ S.iG iX ∈ S.Y ∧ S.iG iX * S.t * (S.iG iX)⁻¹ = S.z * S.t ∧
      S.iG iX * S.z = S.z * S.iG iX ∧ S.iG iX ∈ S.L := by
  refine ⟨by rw [← map_mul, hI.mul_self, map_one], ?_, ?_, S.commute_z (S.mem_L iX), S.mem_L iX⟩
  · rw [mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, hI.commute_J₁ (qThree S.K) ⟨_, rfl⟩]
  · rw [← map_inv, ← map_mul, ← map_mul, hI.conj_t, map_mul, S.hφz]

theorem iG_ne_z (hI : IBarFacts S.K S.p iX) : S.iG iX ≠ S.z := by
  intro h
  have hX : iX = spinZ S.K := S.hφ (h.trans S.hφz.symm)
  have hct := hI.conj_t
  rw [hX] at hct
  obtain ⟨-, hz1, hzc, -⟩ := spinZ_facts S.hp S.hp2 S.hK
  have h1 : spinZ S.K * tSeven S.K * (spinZ S.K)⁻¹ = tSeven S.K := by
    rw [(mem_center_iff.mp hzc (tSeven S.K)).symm]
    group
  rw [h1] at hct
  apply hz1
  calc spinZ S.K = spinZ S.K * tSeven S.K * (tSeven S.K)⁻¹ := by group
    _ = tSeven S.K * (tSeven S.K)⁻¹ := by rw [← hct]
    _ = 1 := by group

abbrev S₀G (S₀ : Subgroup S.X) : Subgroup G := S₀.map S.φ

theorem S₀G_le (hSy : SylowFacts S.K iX S₀ B) : S.S₀G S₀ ≤ S.Y ⊓ S.H := by
  rintro _ ⟨x, hx, rfl⟩
  have h := (S.map_centralizer (qThree S.K)).le ⟨x, hSy.le_centralizer hx, rfl⟩
  exact ⟨(mem_inf.mp h).2, S.hLH (mem_inf.mp h).1⟩

theorem not_dvd_YH (hSy : SylowFacts S.K iX S₀ B) :
    ¬ 2 ∣ (S.S₀G S₀).relIndex (S.Y ⊓ S.H) := by
  have hLY : S.L ⊓ (S.Y ⊓ S.H) = (centralizer ({qThree S.K} : Set S.X)).map S.φ := by
    rw [S.map_centralizer]
    ext x
    simp only [mem_inf]
    constructor
    · rintro ⟨hL, hY, -⟩
      exact ⟨hL, hY⟩
    · rintro ⟨hL, hY⟩
      exact ⟨hL, hY, S.hLH hL⟩
  have h1 : (S.S₀G S₀).relIndex (S.L ⊓ (S.Y ⊓ S.H)) =
      S₀.relIndex (centralizer ({qThree S.K} : Set S.X)) := by
    rw [hLY]
    exact relIndex_map_map_of_injective _ _ S.hφ
  have hS₀L : S.S₀G S₀ ≤ S.L ⊓ (S.Y ⊓ S.H) := le_inf (S.map_le_L _) (S.S₀G_le hSy)
  have h2 := Subgroup.relIndex_mul_relIndex _ _ _ hS₀L
    (inf_le_right : S.L ⊓ (S.Y ⊓ S.H) ≤ S.Y ⊓ S.H)
  have h3 := S.odd_relIndex_L_inf (A := S.Y ⊓ S.H) inf_le_right
  rw [← h2, h1]
  intro hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h | h
  · exact hSy.not_dvd h
  · exact (Nat.not_even_iff_odd.mpr h3) (even_iff_two_dvd.mpr h)

theorem not_dvd_Y (hSy : SylowFacts S.K iX S₀ B) : ¬ 2 ∣ (S.S₀G S₀).relIndex S.Y := by
  refine not_dvd_relIndex_of_center (z := S.z) (S.S₀G_le hSy) (hSy.isPGroup.map S.φ)
    (S.not_dvd_YH hSy) ?_ S.facts.2.1 ?_
  · exact ⟨spinZ S.K, hSy.B_le hSy.z_mem, S.hφz⟩
  · rintro _ ⟨x, hx, rfl⟩ hc
    have hc' : ∀ y ∈ S₀, x * y = y * x := fun y hy =>
      S.hφ (by rw [map_mul, map_mul]; exact hc _ ⟨y, hy, rfl⟩)
    rcases hSy.center x hx hc' with rfl | rfl
    · exact Or.inl (map_one S.φ)
    · exact Or.inr S.hφz

theorem commute_z_S₀G {x : G} (hx : x ∈ S.S₀G S₀) : x * S.z = S.z * x :=
  S.commute_z (S.map_le_L S₀ hx)

theorem involutions_BG (hSy : SylowFacts S.K iX S₀ B) {x : G} (hx : x ∈ B.map S.φ)
    (hxx : x * x = 1) : x = 1 ∨ x = S.z ∨ x = S.t ∨ x = S.z * S.t := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hyy : y * y = 1 := S.hφ (by rw [map_mul, hxx, map_one])
  rcases hSy.involutions_B y hy hyy with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (Or.inl S.hφz)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (by rw [map_mul, S.hφz])))

theorem card_S₀ (hSy : SylowFacts S.K iX S₀ B) : Nat.card S₀ = 2 * Nat.card B := by
  have h := Subgroup.relIndex_mul_card B S₀
  rw [hSy.relIndex_B, inf_of_le_left hSy.B_le] at h
  exact h.symm

theorem ncard_sqrt (a : S.X) :
    ({x | x ∈ B.map S.φ ∧ x * x = S.φ a} : Set G).ncard =
      ({x | x ∈ B ∧ x * x = a} : Set S.X).ncard := by
  have himg : S.φ '' {x | x ∈ B ∧ x * x = a} = {x | x ∈ B.map S.φ ∧ x * x = S.φ a} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxx⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by rw [← map_mul, hxx]⟩
    · rintro ⟨⟨x, hx, rfl⟩, hxx⟩
      exact ⟨x, ⟨hx, S.hφ (by rw [map_mul, hxx])⟩, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ S.hφ]

theorem not_conj_t (hSy : SylowFacts S.K iX S₀ B) {g : G} (hg : g ∈ S.Y)
    (hgz : g * S.z * g⁻¹ = S.t) : False := by
  obtain ⟨hzz, hz1, htt, ht1, hzt, hzt', -, -, -⟩ := S.facts
  have hSYH := S.S₀G_le hSy
  have hS₀2 : IsPGroup 2 (S.S₀G S₀) := hSy.isPGroup.map S.φ
  have hSi := S.not_dvd_YH hSy
  obtain ⟨hRle, hR2, hRi⟩ := sylow_map_conj hg hSYH hS₀2 hSi
  rw [hgz] at hRle hRi
  set BG := B.map S.φ with hBG
  have hBle : BG ≤ S.Y ⊓ centralizer ({S.t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(hSYH ⟨x, hSy.B_le hx, rfl⟩).1, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, hSy.commute_t x hx]
  have hB2 : IsPGroup 2 BG := (hSy.isPGroup.to_le hSy.B_le).map S.φ
  obtain ⟨c, hc, hcB⟩ := exists_conj_le_of_sylow hRle hR2 hRi hBle hB2
  have hct : c * S.t = S.t * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
  set k := c⁻¹ * g with hk
  set R := (S.S₀G S₀).map (MulAut.conj k).toMonoidHom with hR
  have hBR : BG ≤ R := by
    intro b hb
    obtain ⟨s, hs, hsb⟩ := hcB ⟨b, hb, rfl⟩
    refine ⟨s, hs, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hsb ⊢
    calc k * s * k⁻¹ = c⁻¹ * (g * s * g⁻¹) * c := by rw [hk]; group
      _ = c⁻¹ * (c * b * c⁻¹) * c := by rw [hsb]
      _ = b := by group
  have hkz : k * S.z * k⁻¹ = S.t := by
    calc k * S.z * k⁻¹ = c⁻¹ * (g * S.z * g⁻¹) * c := by rw [hk]; group
      _ = c⁻¹ * S.t * c := by rw [hgz]
      _ = S.t := by rw [mul_assoc, ← hct]; group
  have hRcen : ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) → x = 1 ∨ x = S.t := by
    rintro _ ⟨s, hs, rfl⟩ hc'
    have hs' : ∀ y ∈ S.S₀G S₀, s * y = y * s := by
      intro y hy
      have := hc' _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      have h2 := congrArg (fun w => k⁻¹ * w * k) this
      simpa [mul_assoc] using h2
    obtain ⟨s', hs'm, rfl⟩ := hs
    have hs'c : ∀ y ∈ S₀, s' * y = y * s' := fun y hy =>
      S.hφ (by rw [map_mul, map_mul]; exact hs' _ ⟨y, hy, rfl⟩)
    rcases hSy.center s' hs'm hs'c with rfl | rfl
    · left
      simp
    · right
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, S.hφz]
      exact hkz
  have htR : ∀ y ∈ R, S.t * y = y * S.t := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hkz]
    calc k * S.z * k⁻¹ * (k * s * k⁻¹) = k * (S.z * s) * k⁻¹ := by group
      _ = k * (s * S.z) * k⁻¹ := by rw [S.commute_z_S₀G hs]
      _ = k * s * k⁻¹ * (k * S.z * k⁻¹) := by group
  have hcardR : Nat.card R = 2 * Nat.card BG := by
    rw [hR, card_map_of_injective (MulAut.conj k).injective, S.card_map, hBG, S.card_map,
      S.card_S₀ hSy]
  have hidx : (BG.subgroupOf R).index = 2 := by
    have h := Subgroup.relIndex_mul_card BG R
    rw [inf_of_le_left hBR, hcardR] at h
    have hpos : 0 < Nat.card BG := Nat.card_pos
    change BG.relIndex R = 2
    nlinarith [h]
  have hBn : (BG.subgroupOf R).Normal := normal_of_index_eq_two hidx
  have hnorm : ∀ r ∈ R, ∀ b ∈ BG, r * b * r⁻¹ ∈ BG := by
    intro r hr b hb
    have := hBn.conj_mem ⟨b, hBR hb⟩ (mem_subgroupOf.mpr hb) ⟨r, hr⟩
    exact mem_subgroupOf.mp this
  have hzB : S.z ∈ BG := ⟨spinZ S.K, hSy.z_mem, S.hφz⟩
  obtain ⟨r, hr, hrz⟩ : ∃ r ∈ R, r * S.z ≠ S.z * r := by
    by_contra hcon
    push Not at hcon
    rcases hRcen S.z (hBR hzB) (fun y hy => (hcon y hy).symm) with h | h
    · exact hz1 h
    · exact hzt' h
  have hrzB : r * S.z * r⁻¹ ∈ BG := hnorm r hr _ hzB
  have hrzz : r * S.z * r⁻¹ * (r * S.z * r⁻¹) = 1 := by
    calc r * S.z * r⁻¹ * (r * S.z * r⁻¹) = r * (S.z * S.z) * r⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hrt : r * S.t * r⁻¹ = S.t := by
    rw [← htR r hr]
    group
  have hrzt : r * S.z * r⁻¹ = S.z * S.t := by
    rcases S.involutions_BG hSy hrzB hrzz with h | h | h | h
    · exfalso
      apply hz1
      calc S.z = r⁻¹ * (r * S.z * r⁻¹) * r := by group
        _ = 1 := by rw [h]; group
    · exfalso
      apply hrz
      calc r * S.z = (r * S.z * r⁻¹) * r := by group
        _ = S.z * r := by rw [h]
    · exfalso
      apply hzt'
      calc S.z = r⁻¹ * (r * S.z * r⁻¹) * r := by group
        _ = r⁻¹ * (r * S.t * r⁻¹) * r := by rw [h, hrt]
        _ = S.t := by group
    · exact h
  have hrinv : r⁻¹ ∈ R := inv_mem hr
  have himg : (fun x => r * x * r⁻¹) '' {x | x ∈ BG ∧ x * x = S.z} =
      {x | x ∈ BG ∧ x * x = S.z * S.t} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxx⟩, rfl⟩
      refine ⟨hnorm r hr x hx, ?_⟩
      calc r * x * r⁻¹ * (r * x * r⁻¹) = r * (x * x) * r⁻¹ := by group
        _ = S.z * S.t := by rw [hxx, hrzt]
    · rintro ⟨hy, hyy⟩
      refine ⟨r⁻¹ * y * r⁻¹⁻¹, ⟨hnorm r⁻¹ hrinv y hy, ?_⟩, by group⟩
      calc r⁻¹ * y * r⁻¹⁻¹ * (r⁻¹ * y * r⁻¹⁻¹) = r⁻¹ * (y * y) * r := by group
        _ = r⁻¹ * (r * S.z * r⁻¹) * r := by rw [hyy, hrzt]
        _ = S.z := by group
  have hinj : Function.Injective (fun x : G => r * x * r⁻¹) := fun a b h => by
    simpa using h
  have hcount := Set.ncard_image_of_injective {x | x ∈ BG ∧ x * x = S.z} hinj
  rw [himg] at hcount
  have e1 := S.ncard_sqrt (B := B) (spinZ S.K)
  have e2 := S.ncard_sqrt (B := B) (spinZ S.K * tSeven S.K)
  rw [S.hφz] at e1
  rw [map_mul, S.hφz] at e2
  exact hSy.sqrt (by rw [← e1, ← e2, hcount])

theorem not_conj_zt (hI : IBarFacts S.K S.p iX) (hSy : SylowFacts S.K iX S₀ B) {g : G}
    (hg : g ∈ S.Y) (hgz : g * S.z * g⁻¹ = S.z * S.t) : False := by
  obtain ⟨hii, hiY, hit, hiz, -⟩ := S.iG_facts hI
  refine S.not_conj_t hSy (g := S.iG iX * g) (mul_mem hiY hg) ?_
  have hinv : (S.iG iX)⁻¹ = S.iG iX := inv_eq_of_mul_eq_one_right hii
  calc S.iG iX * g * S.z * (S.iG iX * g)⁻¹ = S.iG iX * (g * S.z * g⁻¹) * (S.iG iX)⁻¹ := by
        group
    _ = S.iG iX * S.z * (S.iG iX)⁻¹ * (S.iG iX * S.t * (S.iG iX)⁻¹) := by rw [hgz]; group
    _ = S.z * (S.z * S.t) := by rw [hit, hiz]; group
    _ = S.t := by rw [← mul_assoc, S.facts.1, one_mul]

theorem not_conj_i (hI : IBarFacts S.K S.p iX) (hSy : SylowFacts S.K iX S₀ B) {g : G}
    (hg : g ∈ S.Y) (hgz : g * S.z * g⁻¹ = S.iG iX) : False := by
  obtain ⟨hzz, hz1, -, -, -, -, -, -, -⟩ := S.facts
  have hSYH := S.S₀G_le hSy
  have hS₀2 : IsPGroup 2 (S.S₀G S₀) := hSy.isPGroup.map S.φ
  obtain ⟨hRle, hR2, hRi⟩ := sylow_map_conj hg hSYH hS₀2 (S.not_dvd_YH hSy)
  rw [hgz] at hRle hRi
  obtain ⟨D, hD, hzD⟩ := hSy.derived_i
  set DG := D.map S.φ with hDG
  have hDle : DG ≤ S.Y ⊓ centralizer ({S.iG iX} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(hSYH ⟨x, (hD hx).1, rfl⟩).1, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hD hx).2]
  have hD2 : IsPGroup 2 DG := (hSy.isPGroup.to_le (hD.trans inf_le_left)).map S.φ
  obtain ⟨c, hc, hcD⟩ := exists_conj_le_of_sylow hRle hR2 hRi hDle hD2
  have hci : c * S.iG iX = S.iG iX * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
  set k := g⁻¹ * c with hk
  have hkY : k ∈ S.Y := mul_mem (inv_mem hg) (mem_inf.mp hc).1
  have hkD : DG.map (MulAut.conj k).toMonoidHom ≤ S.S₀G S₀ := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨s, hs, hsd⟩ := hcD ⟨d, hd, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hsd ⊢
    have : k * d * k⁻¹ = s := by
      calc k * d * k⁻¹ = g⁻¹ * (c * d * c⁻¹) * g := by rw [hk]; group
        _ = g⁻¹ * (g * s * g⁻¹) * g := by rw [← hsd]
        _ = s := by group
    rw [this]
    exact hs
  have hki : k * S.iG iX * k⁻¹ = S.z := by
    calc k * S.iG iX * k⁻¹ = g⁻¹ * (c * S.iG iX * c⁻¹) * g := by rw [hk]; group
      _ = g⁻¹ * S.iG iX * g := by rw [hci]; group
      _ = g⁻¹ * (g * S.z * g⁻¹) * g := by rw [hgz]
      _ = S.z := by group
  have hkzB : k * S.z * k⁻¹ ∈ B.map S.φ := by
    have h1 : S.z ∈ ⁅DG, DG⁆ := by
      rw [hDG, ← map_commutator]
      exact ⟨spinZ S.K, hzD, S.hφz⟩
    have h2 : k * S.z * k⁻¹ ∈
        ⁅DG.map (MulAut.conj k).toMonoidHom, DG.map (MulAut.conj k).toMonoidHom⁆ := by
      rw [← map_commutator]
      exact ⟨S.z, h1, rfl⟩
    have h3 := commutator_mono hkD hkD h2
    have h4 : ⁅S.S₀G S₀, S.S₀G S₀⁆ ≤ B.map S.φ := by
      rw [← map_commutator]
      exact map_mono hSy.commutator_le
    exact h4 h3
  have hkzz : k * S.z * k⁻¹ * (k * S.z * k⁻¹) = 1 := by
    calc k * S.z * k⁻¹ * (k * S.z * k⁻¹) = k * (S.z * S.z) * k⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  rcases S.involutions_BG hSy hkzB hkzz with h | h | h | h
  · apply hz1
    calc S.z = k⁻¹ * (k * S.z * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  · apply S.iG_ne_z hI
    calc S.iG iX = k⁻¹ * (k * S.iG iX * k⁻¹) * k := by group
      _ = k⁻¹ * S.z * k := by rw [hki]
      _ = k⁻¹ * (k * S.z * k⁻¹) * k := by rw [h]
      _ = S.z := by group
  · exact S.not_conj_t hSy hkY h
  · exact S.not_conj_zt hI hSy hkY h

theorem weaklyClosed (hI : IBarFacts S.K S.p iX) (hSy : SylowFacts S.K iX S₀ B) {g : G}
    (hg : g ∈ S.Y) (hgS : g⁻¹ * S.z * g ∈ S.S₀G S₀) : g⁻¹ * S.z * g = S.z := by
  obtain ⟨hzz, hz1, -, -, -, -, -, -, -⟩ := S.facts
  have hginv : g⁻¹ * S.z * g⁻¹⁻¹ = g⁻¹ * S.z * g := by rw [inv_inv]
  obtain ⟨u, hu, hug⟩ := hgS
  have huu : u * u = 1 := S.hφ (by
    rw [map_mul, hug, map_one]
    calc g⁻¹ * S.z * g * (g⁻¹ * S.z * g) = g⁻¹ * (S.z * S.z) * g := by group
      _ = 1 := by rw [hzz]; group)
  by_cases huB : u ∈ B
  · rcases hSy.involutions_B u huB huu with rfl | rfl | rfl | rfl
    · exfalso
      apply hz1
      rw [map_one] at hug
      calc S.z = g * (g⁻¹ * S.z * g) * g⁻¹ := by group
        _ = 1 := by rw [← hug]; group
    · rw [← hug, S.hφz]
    · exfalso
      exact S.not_conj_t hSy (inv_mem hg) (hginv.trans hug.symm)
    · exfalso
      refine S.not_conj_zt hI hSy (inv_mem hg) (hginv.trans ?_)
      rw [← hug, map_mul, S.hφz]
  · obtain ⟨s, hs, hsi⟩ := hSy.conj_i u hu huB huu
    exfalso
    have hsY : S.φ s ∈ S.Y := (S.S₀G_le hSy ⟨s, hs, rfl⟩).1
    refine S.not_conj_i hI hSy (g := (S.φ s)⁻¹ * g⁻¹) (mul_mem (inv_mem hsY) (inv_mem hg)) ?_
    have h1 : S.φ s * S.iG iX * (S.φ s)⁻¹ = g⁻¹ * S.z * g := by
      rw [← hug, ← hsi]
      simp only [map_mul, map_inv]
    calc (S.φ s)⁻¹ * g⁻¹ * S.z * ((S.φ s)⁻¹ * g⁻¹)⁻¹ =
        (S.φ s)⁻¹ * (g⁻¹ * S.z * g) * S.φ s := by group
      _ = (S.φ s)⁻¹ * (S.φ s * S.iG iX * (S.φ s)⁻¹) * S.φ s := by rw [h1]
      _ = S.iG iX := by group

theorem le_sup_oddCore (hI : IBarFacts S.K S.p iX) (hSy : SylowFacts S.K iX S₀ B) :
    S.Y ≤ (pPrimeCore 2 ↥S.Y).map S.Y.subtype ⊔ (S.Y ⊓ S.H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hzz, hz1, -, -, -, -, -, -, -⟩ := S.facts
  have hS₀Y : S.S₀G S₀ ≤ S.Y := fun x hx => (S.S₀G_le hSy hx).1
  let P : Sylow 2 ↥S.Y := toSylowIn hS₀Y (hSy.isPGroup.map S.φ) (S.not_dvd_Y hSy)
  have hzS₀ : S.z ∈ S.S₀G S₀ := ⟨spinZ S.K, hSy.B_le hSy.z_mem, S.hφz⟩
  let zY : ↥S.Y := ⟨S.z, hS₀Y hzS₀⟩
  have hzP : zY ∈ (P : Subgroup ↥S.Y) := (mem_toSylowIn hS₀Y _ _ zY).mpr hzS₀
  let zP : ↥(P : Subgroup ↥S.Y) := ⟨zY, hzP⟩
  have hzZ : zP ∈ center ↥(P : Subgroup ↥S.Y) := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hx : ((x : ↥S.Y) : G) ∈ S.S₀G S₀ := (mem_toSylowIn hS₀Y _ _ x).mp x.2
    exact S.commute_z_S₀G hx
  have hzord : orderOf zP = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have hwc : ∀ g : ↥S.Y, g⁻¹ * (zP : ↥S.Y) * g ∈ (P : Subgroup ↥S.Y) →
      g⁻¹ * (zP : ↥S.Y) * g = zP := by
    intro g hg
    rw [mem_toSylowIn] at hg
    apply Subtype.ext
    exact S.weaklyClosed hI hSy g.2 hg
  obtain ⟨h1, -⟩ := CFSG.Milestones.glauberman_zStar_central_sylow_involution P zP hzZ hzord hwc
  intro y hy
  obtain ⟨c, hc, k, hk, hck⟩ := h1 ⟨y, hy⟩
  have hy' : y = (c : G) * (k : G) := congrArg Subtype.val hck
  have hcH : (c : G) ∈ S.Y ⊓ S.H := by
    refine mem_inf.mpr ⟨c.2, mem_centralizer_singleton_iff.mpr ?_⟩
    have := mem_centralizer_singleton_iff.mp hc
    exact congrArg Subtype.val this
  have hkO : (k : G) ∈ (pPrimeCore 2 ↥S.Y).map S.Y.subtype := by
    rw [oddCore_eq_pPrimeCore'] at hk
    exact ⟨k, hk, rfl⟩
  rw [hy', sup_comm]
  exact mul_mem_sup hcH hkO

end SetupOdd

end CFSG.ComponentClassification.HarrisLit.T1.S74
