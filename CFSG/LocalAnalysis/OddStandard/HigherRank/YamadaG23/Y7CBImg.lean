module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBDef

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private theorem y7c_mem_conjSub {Γ : Type} [Group Γ] (c : Γ) (Y : Subgroup Γ) (x : Γ) :
    x ∈ conjSub c Y ↔ c⁻¹ * x * c ∈ Y := by
  rw [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h : c⁻¹ * (MulAut.conj c).toMonoidHom y * c = y := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [h]
    exact hy
  · intro h
    refine ⟨c⁻¹ * x * c, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem y7cPre_le_X (Y : Subgroup (y7cGam s)) : y7cPre s Y ≤ y7cX s := by
  intro x hx
  exact ((mem_y7cPre s).mp hx).1

theorem y7c_M3_le_pre (Y : Subgroup (y7cGam s)) : M3 s ≤ y7cPre s Y := by
  intro x hx
  refine (mem_y7cPre s).mpr ⟨y7c_M3_le_X s hx, ?_⟩
  rw [(y7cPi_eq_one_iff s ⟨x, y7c_M3_le_X s hx⟩).mpr hx]
  exact Y.one_mem

theorem y7cImg_mono {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) : y7cImg s H₁ ≤ y7cImg s H₂ := by
  intro γ hγ
  obtain ⟨x, hx, rfl⟩ := (mem_y7cImg s).mp hγ
  exact (mem_y7cImg s).mpr ⟨x, h hx, rfl⟩

theorem y7cPre_img {H : Subgroup G} (hX : H ≤ y7cX s) (hM : M3 s ≤ H) :
    y7cPre s (y7cImg s H) = H := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxX, hπ⟩ := (mem_y7cPre s).mp hx
    obtain ⟨y, hyH, hyπ⟩ := (mem_y7cImg s).mp hπ
    have h1 : (y : G)⁻¹ * x ∈ M3 s := (y7cPi_eq_iff s y ⟨x, hxX⟩).mp hyπ
    have h2 : (y : G) * ((y : G)⁻¹ * x) ∈ H := H.mul_mem hyH (hM h1)
    simpa using h2
  · intro hx
    exact (mem_y7cPre s).mpr ⟨hX hx, (mem_y7cImg s).mpr ⟨⟨x, hX hx⟩, hx, rfl⟩⟩

theorem y7cImg_pre (Y : Subgroup (y7cGam s)) : y7cImg s (y7cPre s Y) = Y := by
  ext γ
  constructor
  · intro hγ
    obtain ⟨x, hx, rfl⟩ := (mem_y7cImg s).mp hγ
    exact ((mem_y7cPre s).mp hx).2
  · intro hγ
    obtain ⟨x, rfl⟩ := y7cPi_surjective s γ
    exact (mem_y7cImg s).mpr ⟨x, (mem_y7cPre s).mpr ⟨x.2, hγ⟩, rfl⟩

theorem y7cPre_mono {Y₁ Y₂ : Subgroup (y7cGam s)} : y7cPre s Y₁ ≤ y7cPre s Y₂ ↔ Y₁ ≤ Y₂ := by
  constructor
  · intro h
    calc Y₁ = y7cImg s (y7cPre s Y₁) := (y7cImg_pre s Y₁).symm
      _ ≤ y7cImg s (y7cPre s Y₂) := y7cImg_mono s h
      _ = Y₂ := y7cImg_pre s Y₂
  · intro h x hx
    obtain ⟨hxX, hπ⟩ := (mem_y7cPre s).mp hx
    exact (mem_y7cPre s).mpr ⟨hxX, h hπ⟩

theorem y7cPre_sup (Y₁ Y₂ : Subgroup (y7cGam s)) :
    y7cPre s (Y₁ ⊔ Y₂) = y7cPre s Y₁ ⊔ y7cPre s Y₂ := by
  have hX : y7cPre s Y₁ ⊔ y7cPre s Y₂ ≤ y7cX s :=
    sup_le (y7cPre_le_X s Y₁) (y7cPre_le_X s Y₂)
  have hM : M3 s ≤ y7cPre s Y₁ ⊔ y7cPre s Y₂ := (y7c_M3_le_pre s Y₁).trans le_sup_left
  have h := y7cPre_img s hX hM
  have hs : y7cImg s (y7cPre s Y₁ ⊔ y7cPre s Y₂) =
      y7cImg s (y7cPre s Y₁) ⊔ y7cImg s (y7cPre s Y₂) := by
    unfold y7cImg
    rw [Subgroup.subgroupOf_sup (y7cPre_le_X s Y₁) (y7cPre_le_X s Y₂), Subgroup.map_sup]
  rw [hs, y7cImg_pre, y7cImg_pre] at h
  exact h

theorem y7cPre_inf (Y₁ Y₂ : Subgroup (y7cGam s)) :
    y7cPre s (Y₁ ⊓ Y₂) = y7cPre s Y₁ ⊓ y7cPre s Y₂ := by
  ext x
  simp only [Subgroup.mem_inf, mem_y7cPre]
  constructor
  · rintro ⟨h, h1, h2⟩
    exact ⟨⟨h, h1⟩, ⟨h, h2⟩⟩
  · rintro ⟨⟨h, h1⟩, ⟨_, h2⟩⟩
    exact ⟨h, h1, h2⟩

theorem y7cPre_bot : y7cPre s ⊥ = M3 s := by
  ext x
  rw [mem_y7cPre]
  constructor
  · rintro ⟨h, hπ⟩
    exact (y7cPi_eq_one_iff s ⟨x, h⟩).mp (Subgroup.mem_bot.mp hπ)
  · intro hx
    exact ⟨y7c_M3_le_X s hx,
      Subgroup.mem_bot.mpr ((y7cPi_eq_one_iff s ⟨x, y7c_M3_le_X s hx⟩).mpr hx)⟩

theorem y7cImg_sup {H₁ H₂ : Subgroup G} (h₁ : H₁ ≤ y7cX s) (h₂ : H₂ ≤ y7cX s) :
    y7cImg s (H₁ ⊔ H₂) = y7cImg s H₁ ⊔ y7cImg s H₂ := by
  unfold y7cImg
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem y7c_card_img {H : Subgroup G} (hX : H ≤ y7cX s) (hM : M3 s ≤ H) :
    Nat.card (y7cImg s H) * Nat.card (M3 s) = Nat.card H := by
  let φ : ↥H →* y7cGam s := (y7cPi s).comp (Subgroup.inclusion hX)
  have hker : φ.ker = (M3 s).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact y7cPi_eq_one_iff s ⟨x, hX x.2⟩
  have hrange : φ.range = y7cImg s H := by
    ext γ
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_y7cImg s).mpr ⟨⟨x, hX x.2⟩, x.2, rfl⟩
    · intro hγ
      obtain ⟨x, hxH, rfl⟩ := (mem_y7cImg s).mp hγ
      exact ⟨⟨x, hxH⟩, rfl⟩
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange] at h
  have hc : Nat.card ((M3 s).subgroupOf H) = Nat.card (M3 s) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv
  rw [hc] at h
  rw [mul_comm]
  exact h

theorem y7c_card_pre (Y : Subgroup (y7cGam s)) :
    Nat.card (y7cPre s Y) = Nat.card Y * Nat.card (M3 s) := by
  have h := y7c_card_img s (y7cPre_le_X s Y) (y7c_M3_le_pre s Y)
  rw [y7cImg_pre] at h
  exact h.symm

theorem y7cPre_conj (x : ↥(y7cX s)) (Y : Subgroup (y7cGam s)) :
    y7cPre s (conjSub (y7cPi s x) Y) = conjSub (x : G) (y7cPre s Y) := by
  have key : ∀ z : ↥(y7cX s),
      y7cPi s (x⁻¹ * z * x) = (y7cPi s x)⁻¹ * y7cPi s z * y7cPi s x := by
    intro z
    simp only [map_mul, map_inv]
  ext z
  rw [y7c_mem_conjSub, mem_y7cPre]
  constructor
  · rintro ⟨hzX, hπ⟩
    rw [y7c_mem_conjSub] at hπ
    have h : (x : G)⁻¹ * z * x ∈ y7cX s :=
      (y7cX s).mul_mem ((y7cX s).mul_mem ((y7cX s).inv_mem x.2) hzX) x.2
    have h2 : y7cPi s (x⁻¹ * ⟨z, hzX⟩ * x) ∈ Y := by
      rw [key]
      exact hπ
    exact (mem_y7cPre s).mpr ⟨h, h2⟩
  · intro hz
    obtain ⟨h, hπ⟩ := (mem_y7cPre s).mp hz
    have hzX : z ∈ y7cX s := by
      have h3 := (y7cX s).mul_mem ((y7cX s).mul_mem x.2 h) ((y7cX s).inv_mem x.2)
      simpa [mul_assoc] using h3
    refine ⟨hzX, ?_⟩
    rw [y7c_mem_conjSub]
    have h2 : y7cPi s (x⁻¹ * ⟨z, hzX⟩ * x) ∈ Y := hπ
    rw [key] at h2
    exact h2

theorem y7cImg_conj (x : ↥(y7cX s)) (H : Subgroup G) :
    y7cImg s (conjSub (x : G) H) = conjSub (y7cPi s x) (y7cImg s H) := by
  have key : ∀ z : ↥(y7cX s),
      y7cPi s (x⁻¹ * z * x) = (y7cPi s x)⁻¹ * y7cPi s z * y7cPi s x := by
    intro z
    simp only [map_mul, map_inv]
  have key' : ∀ z : ↥(y7cX s),
      y7cPi s (x * z * x⁻¹) = y7cPi s x * y7cPi s z * (y7cPi s x)⁻¹ := by
    intro z
    simp only [map_mul, map_inv]
  ext γ
  rw [y7c_mem_conjSub]
  constructor
  · intro hγ
    obtain ⟨w, hw, rfl⟩ := (mem_y7cImg s).mp hγ
    rw [y7c_mem_conjSub] at hw
    refine (mem_y7cImg s).mpr ⟨x⁻¹ * w * x, hw, ?_⟩
    exact key w
  · intro hγ
    obtain ⟨v, hv, hvπ⟩ := (mem_y7cImg s).mp hγ
    refine (mem_y7cImg s).mpr ⟨x * v * x⁻¹, ?_, ?_⟩
    · rw [y7c_mem_conjSub]
      have h : (x : G)⁻¹ * ((x * v * x⁻¹ : ↥(y7cX s)) : G) * x = v := by
        simp [mul_assoc]
      rw [h]
      exact hv
    · rw [key', hvπ]
      group

end CFSG.OddStandard.HigherRank.YamadaG23
