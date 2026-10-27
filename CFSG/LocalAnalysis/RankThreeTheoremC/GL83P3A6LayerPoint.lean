module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerFrame
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43A6Point
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6SylowProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Struct
import CFSG.RankThree.PartTwo.Sec11.Wreath

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer

open CFSG.Open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux

section Transport

variable {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]

theorem map_Qf (f : X →* Y) (a b c : X) : (Qf a b c).map f = Qf (f a) (f b) (f c) := by
  simp only [Qf, Subgroup.map_sup, MonoidHom.map_zpowers]

theorem vitriple_comap (f : X →* Y) (hf : Function.Injective f) {a b c : X}
    (h : VITriple (f a) (f b) (f c)) : VITriple a b c := by
  have hpow : ∀ z : X, f z ^ 3 = 1 → z ^ 3 = 1 := fun z hz => hf (by rw [map_pow, hz, map_one])
  have hne : ∀ z : X, f z ≠ 1 → z ≠ 1 := fun z hz h1 => hz (by rw [h1, map_one])
  have hcomm : ∀ z w : X, f z * f w = f w * f z → z * w = w * z :=
    fun z w hzw => hf (by rw [map_mul, map_mul, hzw])
  have hmem : ∀ (z : X) (A : Subgroup X), z ∈ A → f z ∈ A.map f := fun z A hz => ⟨z, hz, rfl⟩
  refine ⟨hpow a h.x_pow, hpow b h.e₂_pow, hpow c h.e₃_pow, hne a h.x_ne, hne b h.e₂_ne,
    hne c h.e₃_ne, hcomm a b h.comm_x₂, hcomm a c h.comm_x₃, hcomm b c h.comm_23, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    have h1 : f z ∈ zpowers (f b) ⊓ zpowers (f c) := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [← MonoidHom.map_zpowers]; exact hmem z _ (mem_inf.mp hz).1
      · rw [← MonoidHom.map_zpowers]; exact hmem z _ (mem_inf.mp hz).2
    rw [h.ind_23, mem_bot] at h1
    exact mem_bot.mpr (hf (h1.trans (map_one f).symm))
  · rw [eq_bot_iff]
    intro z hz
    have h1 : f z ∈ (zpowers (f b) ⊔ zpowers (f c)) ⊓ zpowers (f a) := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, ← Subgroup.map_sup]
        exact hmem z _ (mem_inf.mp hz).1
      · rw [← MonoidHom.map_zpowers]; exact hmem z _ (mem_inf.mp hz).2
    rw [h.ind_x, mem_bot] at h1
    exact mem_bot.mpr (hf (h1.trans (map_one f).symm))

theorem vitriple_map (f : X →* Y) {a b c : X} (h : VITriple a b c)
    (hinj : ∀ w ∈ Qf a b c, f w = 1 → w = 1) : VITriple (f a) (f b) (f c) := by
  have hpow : ∀ z : X, z ^ 3 = 1 → f z ^ 3 = 1 := fun z hz => by rw [← map_pow, hz, map_one]
  have hne : ∀ z ∈ Qf a b c, z ≠ 1 → f z ≠ 1 := fun z hz h1 hf1 => h1 (hinj z hz hf1)
  have hcomm : ∀ z w : X, z * w = w * z → f z * f w = f w * f z :=
    fun z w hzw => by rw [← map_mul, ← map_mul, hzw]
  have haQ : a ∈ Qf a b c := Tri.x_mem h
  have hbQ : b ∈ Qf a b c := Tri.e₂_mem h
  have hcQ : c ∈ Qf a b c := Tri.e₃_mem h
  refine ⟨hpow a h.x_pow, hpow b h.e₂_pow, hpow c h.e₃_pow, hne a haQ h.x_ne,
    hne b hbQ h.e₂_ne, hne c hcQ h.e₃_ne, hcomm a b h.comm_x₂, hcomm a c h.comm_x₃,
    hcomm b c h.comm_23, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (mem_inf.mp hz).1
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (mem_inf.mp hz).2
    have hw : b ^ i * (c ^ j)⁻¹ ∈ Qf a b c :=
      mul_mem (zpow_mem hbQ i) (inv_mem (zpow_mem hcQ j))
    have hfw : f (b ^ i * (c ^ j)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, map_zpow, hi, hj, mul_inv_cancel]
    have h1 := hinj _ hw hfw
    have hbc : b ^ i = c ^ j := mul_inv_eq_one.mp h1
    have h2 : b ^ i ∈ zpowers b ⊓ zpowers c :=
      mem_inf.mpr ⟨zpow_mem_zpowers b i, hbc ▸ zpow_mem_zpowers c j⟩
    rw [h.ind_23, mem_bot] at h2
    rw [mem_bot, ← hi, ← map_zpow, h2, map_one]
  · rw [eq_bot_iff]
    intro z hz
    have hz1 : z ∈ (zpowers b ⊔ zpowers c).map f := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      exact (mem_inf.mp hz).1
    obtain ⟨w, hw, rfl⟩ := hz1
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (mem_inf.mp hz).2
    have hwQ : w * (a ^ k)⁻¹ ∈ Qf a b c :=
      mul_mem (mem_sup_right hw) (inv_mem (zpow_mem haQ k))
    have hfw : f (w * (a ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
    have hwa : w = a ^ k := mul_inv_eq_one.mp (hinj _ hwQ hfw)
    have h2 : w ∈ (zpowers b ⊔ zpowers c) ⊓ zpowers a :=
      mem_inf.mpr ⟨hw, hwa ▸ zpow_mem_zpowers a k⟩
    rw [h.ind_x, mem_bot] at h2
    rw [mem_bot, h2, map_one]

end Transport

structure PointData {G : Type} [Group G] [Finite G] (P : Sylow 3 G) (M J : Subgroup G)
    (x e₂ e₃ t ρ : G) (s : ℤ) : Prop where
  tri : VITriple x e₂ e₃
  x_mem : x ∈ (P : Subgroup G)
  x_memM : x ∈ M
  t_mem : t ∈ (P : Subgroup G)
  t_x : t * x * t⁻¹ = e₂
  t_e₂ : t * e₂ * t⁻¹ = e₃
  t_e₃ : t * e₃ * t⁻¹ = x
  ρ_mem : ρ ∈ M
  ρ_x : ρ * x * ρ⁻¹ = x
  ρ_e₂ : ρ * e₂ * ρ⁻¹ = e₃ ^ s
  ρ_e₃ : ρ * e₃ * ρ⁻¹ = e₂ ^ (-s)
  s_cases : s = 1 ∨ s = -1
  Q_eq : Qf x e₂ e₃ = (P : Subgroup G) ⊓ centralizer ({x} : Set G)
  e₂_mem : e₂ ∈ (P : Subgroup G) ⊓ J
  e₃_mem : e₃ ∈ (P : Subgroup G) ⊓ J
  lines : ∀ g : G, g * x * g⁻¹ ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) →
    g * x * g⁻¹ ∈ zpowers x ∨ g * x * g⁻¹ ∈ zpowers e₂ ∨ g * x * g⁻¹ ∈ zpowers e₃
  wreath : Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)))
  P_le : (P : Subgroup G) ≤ M

section Point

variable {G : Type} [Group G] [Finite G]

theorem exists_pointData (hS : Setting G) (hU0 : FullCoreLocal G)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J)
    (h34S : A6Prop34S 3 P J x)
    (hnwc : ¬ LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G))) :
    ∃ (e₂ e₃ t ρ : G) (s : ℤ), PointData P M J x e₂ e₃ t ρ s := by
  classical
  have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA1 : A6SylowData := a6SylowData_proved
  obtain ⟨⟨hQab, -, hfus⟩, -, hShapeVI⟩ := h34S
  obtain ⟨hWr, -, hQc⟩ := hShapeVI hnwc
  obtain ⟨φ⟩ := hWr
  have hP81 : Nat.card (P : Subgroup G) = 81 := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.RankThree.PartTwo.Sec11.card_wreath
  have hQc27 : Nat.card ((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) = 27 := by
    rw [hQc]; norm_num
  obtain ⟨hxP, hxLO, -, -⟩ := id hgen
  obtain ⟨hxM, hx1, hx3, -, -⟩ := id hxLO
  have hxJ : x ∉ J := a6_x_not_mem_J hS hU0 hp hM hgen hJ
  have hDcard : Nat.card ((P : Subgroup G) ⊓ J : Subgroup G) = 9 := by
    have := (a6_T_data hS hU0 hA1 hp hM hgen hJ).2.2
    rw [this]; norm_num
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  obtain ⟨t, e₂, e₃, htP, he₂, he₃, ht3x, he₂D, he₃D, he₂3, he₃3, he₂1, he₃1, hc2x, hc3x, hc23,
    hind23, hindx, hlines⟩ := vi_lines P.isPGroup' hP81 hxP hx1 hx3 hxJ hQab hQc27 hDcard hfus
  have hxJ' : ∀ b : ℤ, x ^ b ∈ J → x ^ b = 1 := by
    intro b hb
    by_contra hb1
    apply hxJ
    have h1 := zpowers_eq_of_mem hx3 hx1 (zpow_mem_zpowers x b) hb1
    have hx' : x ∈ zpowers (x ^ b) := h1.symm ▸ mem_zpowers x
    exact (zpowers_le.mpr hb) hx'
  have hT : VITriple x e₂ e₃ :=
    { x_pow := hx3, e₂_pow := he₂3, e₃_pow := he₃3, x_ne := hx1, e₂_ne := he₂1, e₃_ne := he₃1
      comm_x₂ := hc2x.symm, comm_x₃ := hc3x.symm, comm_23 := hc23, ind_23 := hind23,
      ind_x := hindx }
  have hDQ : (P : Subgroup G) ⊓ J ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    le_inf inf_le_left (inf_le_right.trans hJ.le_centralizer)
  have hQfQ : Qf x e₂ e₃ ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
    refine sup_le (zpowers_le.mpr ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩)
      (sup_le (zpowers_le.mpr (hDQ he₂D)) (zpowers_le.mpr (hDQ he₃D)))
  obtain ⟨ρ, hρC, hρN, hρrot⟩ := a6_exists_rotation hgen hJ
  have hρM : ρ ∈ M := (a6l43_point_facts hS hU0 hA1 hp hM hgen hJ).1 hρN
  have hρx : ρ * x * ρ⁻¹ = x := by
    rw [mem_centralizer_singleton_iff.mp hρC]; group
  obtain ⟨s, hs, hρ₂, hρ₃⟩ := vi_rotation (D := (P : Subgroup G) ⊓ J) (J := J) he₂D he₃D
    inf_le_right hxJ' (fun g hg => hlines g (hDQ hg)) he₂ he₃ he₂3 he₃3 he₂1 he₃1 hind23 hρN
    hρrot
  have hQeq : Qf x e₂ e₃ = (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hQfQ (by rw [hT.Q_card, hQc27])
  exact ⟨e₂, e₃, t, ρ, s,
    { tri := hT, x_mem := hxP, x_memM := hxM, t_mem := htP, t_x := he₂.symm, t_e₂ := he₃.symm,
      t_e₃ := ht3x, ρ_mem := hρM, ρ_x := hρx, ρ_e₂ := hρ₂, ρ_e₃ := hρ₃, s_cases := hs,
      Q_eq := hQeq, e₂_mem := he₂D, e₃_mem := he₃D, lines := hlines, wreath := ⟨φ⟩,
      P_le := hPM }⟩

end Point

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer
