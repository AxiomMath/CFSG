module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Phi

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal
open scoped Pointwise

variable {G : Type} [Group G]

theorem fz59crit_cent_conj [Finite G] {t x : G}
    (hcent : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P ≤ 2 ^ 7)
    (hxt : IsConj t x) :
    ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({x} : Set G) → Nat.card P ≤ 2 ^ 7 := by
  intro P hP hPx
  obtain ⟨c, hc⟩ := isConj_iff.mp hxt
  let ψ : G →* G := (MulAut.conj c⁻¹).toMonoidHom
  have hψ : Function.Injective ψ := (MulAut.conj c⁻¹).injective
  rw [← Subgroup.card_map_of_injective hψ]
  refine hcent (P.map ψ) (hP.map ψ) ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp (hPx hy)
  have hxc : x = c * t * c⁻¹ := hc.symm
  simp only [ψ, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
  rw [hxc] at hyx
  calc c⁻¹ * y * c⁻¹⁻¹ * t = c⁻¹ * (y * (c * t * c⁻¹)) * c := by group
    _ = c⁻¹ * ((c * t * c⁻¹) * y) * c := by rw [hyx]
    _ = t * (c⁻¹ * y * c⁻¹⁻¹) := by group

theorem fz59_crit_core [Finite G] {Z H : Subgroup G} {t x : G} (hZ : Nat.card Z = 4)
    (hcent : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P ≤ 2 ^ 7)
    (hxt : IsConj t x) (hH : ∀ n ∈ H, ∃ z ∈ Z, n * x * n⁻¹ = x * z) :
    ¬ 2 ^ 10 ∣ Nat.card H := by
  classical
  letI : MulAction H G := MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp H.subtype)
  have hsmul : ∀ (n : H) (g : G), n • g = (n : G) * g * (n : G)⁻¹ := fun n g => rfl
  set S := MulAction.stabilizer H x
  have horb : (MulAction.orbit H x).ncard ≤ 4 := by
    have hsub : MulAction.orbit H x ⊆ (fun z => x * z) '' (Z : Set G) := by
      rintro _ ⟨n, rfl⟩
      obtain ⟨z, hz, h⟩ := hH n n.2
      exact ⟨z, hz, by show x * z = n • x; rw [hsmul, h]⟩
    calc (MulAction.orbit H x).ncard ≤ ((fun z => x * z) '' (Z : Set G)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (Z : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 4 := by rw [← Nat.card_coe_set_eq]; exact hZ
  have hidx : S.index = (MulAction.orbit H x).ncard := MulAction.index_stabilizer H x
  have hcard : Nat.card S * S.index = Nat.card H := Subgroup.card_mul_index S
  have hS8 : ¬ 2 ^ 8 ∣ Nat.card S := by
    intro hdvd
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := S) 2 hdvd
    let φ : S →* G := H.subtype.comp S.subtype
    have hφ : Function.Injective φ := H.subtype_injective.comp S.subtype_injective
    have hP : Nat.card (K.map φ) = 2 ^ 8 := by rw [Subgroup.card_map_of_injective hφ, hK]
    have hPp : IsPGroup 2 (K.map φ) := IsPGroup.of_card hP
    have hle : K.map φ ≤ centralizer ({x} : Set G) := by
      rintro _ ⟨k, -, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (k : H) • x = x := MulAction.mem_stabilizer_iff.mp k.2
      rw [hsmul] at h1
      show ((k : H) : G) * x = x * ((k : H) : G)
      calc ((k : H) : G) * x = ((k : H) : G) * x * ((k : H) : G)⁻¹ * ((k : H) : G) := by group
        _ = x * ((k : H) : G) := by rw [h1]
    have := fz59crit_cent_conj hcent hxt (K.map φ) hPp hle
    rw [hP] at this
    omega
  intro h10
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle4 : S.index ≤ 4 := hidx ▸ horb
  have h12 : S.index ∣ 12 := by
    interval_cases (S.index) <;> decide
  rw [← hcard] at h10
  have h1 : 2 ^ 10 ∣ Nat.card S * 12 := h10.trans (Nat.mul_dvd_mul_left _ h12)
  have h2 : 2 ^ 8 * 4 ∣ (Nat.card S * 3) * 4 := by
    have : Nat.card S * 12 = (Nat.card S * 3) * 4 := by ring
    rw [this] at h1
    simpa using h1
  have h3 : 2 ^ 8 ∣ Nat.card S * 3 := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h2
  exact hS8 ((Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h3))

theorem fz59crit_cell_mem_R (b : Fin 3 → Fin 2 → G) (c : Fz59Cell) :
    fz59CellElt b c ∈ fz59R b := by
  obtain ⟨i, k⟩ := c
  have h0 : b i 0 ∈ fz59R b := Subgroup.subset_closure ⟨(i, 0), rfl⟩
  have h1 : b i 1 ∈ fz59R b := Subgroup.subset_closure ⟨(i, 1), rfl⟩
  fin_cases k
  · exact h0
  · exact h1
  · exact (fz59R b).mul_mem h0 h1

theorem fz59crit_cell_sq {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (c : Fz59Cell) :
    fz59CellElt b c ^ 2 = b c.1 0 ^ 2 := by
  obtain ⟨i, k⟩ := c
  fin_cases k
  · rfl
  · exact (hb.quat i).2.1
  · exact ((hb.quat i).mul_left.2.1).symm

theorem fz59crit_sq_mem_Z {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (i : Fin 3) :
    b i 0 ^ 2 ∈ fz59Z b := by
  rw [fz59_mem_Z hb]
  fin_cases i <;> simp

theorem fz59crit_Z_sq {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {w : G} (hw : w ∈ fz59Z b) :
    w ^ 2 = 1 := by
  rw [fz59_mem_Z hb] at hw
  have h4 : ∀ i, (b i 0 ^ 2) ^ 2 = 1 := fun i => by rw [← pow_mul]; exact (hb.quat i).1
  rcases hw with rfl | rfl | rfl | rfl
  · simp
  · exact h4 0
  · exact h4 1
  · exact h4 2

theorem fz59_conj_mem_Z {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (n : normalizer ((fz59R b : Subgroup G) : Set G))
    {z : G} (hz : z ∈ fz59Z b) : (n : G) * z * (n : G)⁻¹ ∈ fz59Z b := by
  have hcomm := fz59_Z_central hb
  have key : ∀ i, (n : G) * b i 0 ^ 2 * (n : G)⁻¹ ∈ fz59Z b := by
    intro i
    obtain ⟨w, hw, hn⟩ := hΦ.1 n (i, 0)
    have hn' : (n : G) * b i 0 * (n : G)⁻¹ = fz59CellElt b (Φ n (i, 0)) * w := hn
    have e1 : (n : G) * b i 0 ^ 2 * (n : G)⁻¹ = ((n : G) * b i 0 * (n : G)⁻¹) ^ 2 := by
      rw [conj_pow]
    rw [e1, hn']
    have hxw : Commute (fz59CellElt b (Φ n (i, 0))) w :=
      (hcomm w hw _ (fz59crit_cell_mem_R b _)).symm
    rw [hxw.mul_pow, fz59crit_cell_sq hb, fz59crit_Z_sq hb hw, mul_one]
    exact fz59crit_sq_mem_Z hb _
  rw [fz59_mem_Z hb] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · simpa using (fz59Z b).one_mem
  · exact key 0
  · exact key 1
  · exact key 2

theorem fz59crit_tr_inj {ω ω' : Fin 3 → Fin 3} (h : fz59Tr ω = fz59Tr ω') : ω = ω' := by
  funext i
  have h1 : (i, ω i) ∈ fz59Tr ω := by simp [fz59Tr]
  rw [h] at h1
  simp [fz59Tr] at h1
  exact h1.symm

theorem fz59_card_ker {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (hker : ∀ n, Φ n = 1 → (n : G) ∈ fz59R b) :
    Nat.card Φ.ker = 2 ^ 8 := by
  have hmap : Φ.ker.map (normalizer ((fz59R b : Subgroup G) : Set G)).subtype = fz59R b := by
    ext g
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hker n hn
    · intro hg
      exact ⟨⟨g, Subgroup.le_normalizer hg⟩, fz59_phi_one_of_mem hb hΦ _ hg, rfl⟩
  calc Nat.card Φ.ker
      = Nat.card (Φ.ker.map (normalizer ((fz59R b : Subgroup G) : Set G)).subtype) :=
        (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
    _ = Nat.card (fz59R b) := by rw [hmap]
    _ = 2 ^ 8 := fz59_card_R hb

theorem fz59_crit [Finite G] {t : G} {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (hker : ∀ n, Φ n = 1 → (n : G) ∈ fz59R b)
    (hcent : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P ≤ 2 ^ 7)
    (ω : Fin 3 → Fin 3) {z : G} (hz : z ∈ fz59Z b) (hconj : IsConj t (fz59Prod b ω * z)) :
    ¬ 4 ∣ Nat.card (MulAction.stabilizer Φ.range (fz59Tr ω)) := by
  classical
  intro h4
  set S := MulAction.stabilizer Φ.range (fz59Tr ω)
  set Hs : Subgroup (normalizer ((fz59R b : Subgroup G) : Set G)) := S.comap Φ.rangeRestrict
  have hker_card : Nat.card Φ.ker = 2 ^ 8 := fz59_card_ker hb hΦ hker
  have hidx : Hs.index = S.index := Subgroup.index_comap_of_surjective S Φ.rangeRestrict_surjective
  have h1 : Nat.card Hs * Hs.index = Nat.card (normalizer ((fz59R b : Subgroup G) : Set G)) :=
    Subgroup.card_mul_index Hs
  have h2 : Nat.card S * S.index = Nat.card Φ.range := Subgroup.card_mul_index S
  have h3 : Nat.card Φ.ker * Nat.card Φ.range =
      Nat.card (normalizer ((fz59R b : Subgroup G) : Set G)) := Subgroup.card_ker_mul_card_range Φ
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hHs_card : Nat.card Hs = 2 ^ 8 * Nat.card S := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card Hs * S.index = Nat.card Hs * Hs.index := by rw [hidx]
      _ = Nat.card Φ.ker * Nat.card Φ.range := by rw [h1, h3]
      _ = 2 ^ 8 * (Nat.card S * S.index) := by rw [hker_card, h2]
      _ = 2 ^ 8 * Nat.card S * S.index := by ring
  set H : Subgroup G := Hs.map (normalizer ((fz59R b : Subgroup G) : Set G)).subtype with hH
  have hH_card : Nat.card H = 2 ^ 8 * Nat.card S := by
    rw [hH, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hHs_card]
  refine fz59_crit_core (Z := fz59Z b) (H := H) (fz59_card_Z hb) hcent hconj ?_ ?_
  · rintro _ ⟨n, hn, rfl⟩
    have hstab : (fz59Tr ω).image (Φ n) = fz59Tr ω := MulAction.mem_stabilizer_iff.mp hn
    obtain ⟨ω', z', hz', hconj', himg⟩ := fz59_phi_prod hb hΦ n ω
    have hω' : ω' = ω := fz59crit_tr_inj (by rw [← himg, hstab])
    rw [hω'] at hconj'
    refine ⟨z⁻¹ * (z' * ((n : G) * z * (n : G)⁻¹)),
      (fz59Z b).mul_mem ((fz59Z b).inv_mem hz)
        ((fz59Z b).mul_mem hz' (fz59_conj_mem_Z hb hΦ n hz)), ?_⟩
    calc (n : G) * (fz59Prod b ω * z) * (n : G)⁻¹
        = ((n : G) * fz59Prod b ω * (n : G)⁻¹) * ((n : G) * z * (n : G)⁻¹) := by group
      _ = (fz59Prod b ω * z') * ((n : G) * z * (n : G)⁻¹) := by rw [hconj']
      _ = fz59Prod b ω * z * (z⁻¹ * (z' * ((n : G) * z * (n : G)⁻¹))) := by group
  · have h10 : (2 : ℕ) ^ 10 = 2 ^ 8 * 4 := by norm_num
    rw [hH_card, h10]
    exact Nat.mul_dvd_mul_left _ h4

end CFSG.OddStandard.SmallF3.FritzII
