module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsBasic
public import CFSG.LieType.SteinbergBRSuzukiNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelInterface

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.LieType.Ree

variable {G : Type*} [Group G] {a : ℕ} {K : Type} [Field K]

@[expose] noncomputable def szModelU (L : Subgroup G)
    (e : L ≃* suzukiGroup a K) : Subgroup G :=
  ((suzukiU a K).comap e.toMonoidHom).map L.subtype

theorem mem_szModelU {L : Subgroup G} {e : L ≃* suzukiGroup a K}
    {x : G} : x ∈ szModelU L e ↔ ∃ hx : x ∈ L, e ⟨x, hx⟩ ∈ suzukiU a K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem szModelU_le (L : Subgroup G) (e : L ≃* suzukiGroup a K) :
    szModelU L e ≤ L := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem exists_szRootCoords [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {L : Subgroup G} (e : L ≃* suzukiGroup a K) (u₀ v₀ : K)
    (l : Kˣ) :
    ∃ u v : G → K, SzRootCoords (szModelU L e) a
      ((e.symm (suzukiSElt a K u₀ v₀ * suzukiDElt a K l) : L) : G) u v (l : K) := by
  obtain ⟨h2, hadd, -⟩ := suzuki_frob_data a hK
  set θ := 2 ^ (a + 1) with hθ
  have hex : ∀ x : G, ∃ p : K × K, ∀ hx : x ∈ L, e ⟨x, hx⟩ ∈ suzukiU a K →
      e ⟨x, hx⟩ = suzukiSElt a K p.1 p.2 := by
    intro x
    by_cases hx : x ∈ L
    · by_cases hU : e ⟨x, hx⟩ ∈ suzukiU a K
      · obtain ⟨α, β, h⟩ := (mem_suzukiU_iff hK).mp hU
        exact ⟨(α, β), fun _ _ => h.symm⟩
      · exact ⟨(0, 0), fun _ h => absurd h hU⟩
    · exact ⟨(0, 0), fun h => absurd h hx⟩
  choose f hf using hex
  have hfx : ∀ x (hx : x ∈ szModelU L e), e ⟨x, szModelU_le L e hx⟩ =
      suzukiSElt a K (f x).1 (f x).2 := by
    intro x hx
    obtain ⟨hxL, hU⟩ := mem_szModelU.mp hx
    exact hf x hxL hU
  have hθ1 : ∀ z : K, z ^ (θ + 1) = z ^ θ * z := fun z => pow_succ z θ
  refine ⟨fun x => (f x).1, fun x => (f x).2 + (f x).1 ^ (θ + 1), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro x hx x' hx'
    have h := hfx (x * x') (mul_mem hx hx')
    rw [show (⟨x * x', szModelU_le L e (mul_mem hx hx')⟩ : L) =
      ⟨x, szModelU_le L e hx⟩ * ⟨x', szModelU_le L e hx'⟩ from rfl, map_mul, hfx x hx,
      hfx x' hx', suzukiSElt_mul hK, suzukiSElt_inj] at h
    obtain ⟨e1, e2⟩ := h
    refine ⟨e1.symm, ?_⟩
    rw [← e1, ← e2, hθ1, hθ1, hθ1, hadd]
    linear_combination ((f x).1 ^ θ * (f x').1) * h2
  ·
    intro x hx x' hx' hu hv
    rw [hu] at hv
    have hv' : (f x).2 = (f x').2 := add_right_cancel hv
    have h := (hfx x hx).trans ((congrArg₂ (suzukiSElt a K) hu hv').trans (hfx x' hx').symm)
    exact congrArg Subtype.val (e.injective h)
  ·
    intro α β
    set g := e.symm (suzukiSElt a K α (β + α ^ (θ + 1))) with hg
    have hgU : e g ∈ suzukiU a K := by
      rw [hg, MulEquiv.apply_symm_apply]
      exact (mem_suzukiU_iff hK).mpr ⟨_, _, rfl⟩
    have hgx : (g : G) ∈ szModelU L e := mem_szModelU.mpr ⟨g.2, hgU⟩
    have h := hfx g hgx
    rw [show (⟨(g : G), szModelU_le L e hgx⟩ : L) = g from rfl, hg, MulEquiv.apply_symm_apply,
      suzukiSElt_inj] at h
    obtain ⟨e1, e2⟩ := h
    refine ⟨g, hgx, e1.symm, ?_⟩
    rw [← e1, ← e2]
    linear_combination (α ^ (θ + 1)) * h2
  all_goals
    have hconjS : ∀ α β : K, (suzukiSElt a K u₀ v₀)⁻¹ * suzukiSElt a K α β * suzukiSElt a K u₀ v₀ =
        suzukiSElt a K α (β + u₀ ^ θ * α + α ^ θ * u₀) := by
      intro α β
      rw [suzukiSElt_inv hK, suzukiSElt_mul hK, suzukiSElt_mul hK, suzukiSElt_inj]
      constructor
      · linear_combination u₀ * h2
      · rw [hadd, hθ1]
        linear_combination (v₀ + u₀ ^ θ * u₀) * h2
    set dL : L := e.symm (suzukiSElt a K u₀ v₀ * suzukiDElt a K l) with hdL
    have hkey : ∀ x (hx : x ∈ szModelU L e),
        ∃ h : (dL : G)⁻¹ * x * dL ∈ L, e ⟨(dL : G)⁻¹ * x * dL, h⟩ =
          suzukiSElt a K ((l : K) * (f x).1)
            ((l : K) ^ (θ + 1) * ((f x).2 + u₀ ^ θ * (f x).1 + (f x).1 ^ θ * u₀)) := by
      intro x hx
      have hxL := szModelU_le L e hx
      refine ⟨mul_mem (mul_mem (inv_mem dL.2) hxL) dL.2, ?_⟩
      rw [show (⟨(dL : G)⁻¹ * x * dL, mul_mem (mul_mem (inv_mem dL.2) hxL) dL.2⟩ : L) =
        dL⁻¹ * ⟨x, hxL⟩ * dL from rfl, map_mul, map_mul, map_inv, hdL, MulEquiv.apply_symm_apply,
        hfx x hx]
      rw [show (suzukiSElt a K u₀ v₀ * suzukiDElt a K l)⁻¹ * suzukiSElt a K (f x).1 (f x).2 *
          (suzukiSElt a K u₀ v₀ * suzukiDElt a K l) = (suzukiDElt a K l)⁻¹ *
          ((suzukiSElt a K u₀ v₀)⁻¹ * suzukiSElt a K (f x).1 (f x).2 * suzukiSElt a K u₀ v₀) *
          suzukiDElt a K l by group, hconjS, suzukiDElt_conj hK]
    have hmem : ∀ x (hx : x ∈ szModelU L e), (dL : G)⁻¹ * x * dL ∈ szModelU L e := by
      intro x hx
      obtain ⟨h, he⟩ := hkey x hx
      exact mem_szModelU.mpr ⟨h, by rw [he]; exact suzukiSElt_mem_suzukiU a K _ _⟩
    have hcoord : ∀ x (hx : x ∈ szModelU L e), (f ((dL : G)⁻¹ * x * dL)).1 = (l : K) * (f x).1 ∧
        (f ((dL : G)⁻¹ * x * dL)).2 =
          (l : K) ^ (θ + 1) * ((f x).2 + u₀ ^ θ * (f x).1 + (f x).1 ^ θ * u₀) := by
      intro x hx
      obtain ⟨h, he⟩ := hkey x hx
      exact suzukiSElt_inj.mp ((hfx _ (hmem x hx)).symm.trans he)
  · exact hmem
  · intro x hx
    exact (hcoord x hx).1
  · intro x hx hu
    obtain ⟨h1, h3⟩ := hcoord x hx
    rw [h1, h3, hu]
    simp only [hθ, mul_zero, zero_mul, add_zero,
      zero_pow (pow_ne_zero (a + 1) (two_ne_zero : (2 : ℕ) ≠ 0)),
      zero_pow (Nat.succ_ne_zero (2 ^ (a + 1)))]

theorem exists_mulEquiv_szModelU_eq [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {L : Subgroup G} (e : L ≃* suzukiGroup a K)
    {T₁ : Subgroup G} (hT₁L : T₁ ≤ L)
    (hT₁ : ∃ P : Sylow 2 L, (P : Subgroup L) = T₁.subgroupOf L) :
    ∃ e' : L ≃* suzukiGroup a K, szModelU L e' = T₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hT₁
  have hPp : IsPGroup 2 ((P : Subgroup L).map e.toMonoidHom) := P.isPGroup'.map _
  obtain ⟨g, hg⟩ := CFSG.LieType.SteinbergBR.exists_le_conj_suzukiU hK hPp
  let e' : L ≃* suzukiGroup a K := e.trans (MulAut.conj g⁻¹)
  have he' : ∀ y, e' y = g⁻¹ * e y * g := fun y => by simp [e']
  refine ⟨e', ?_⟩
  have hle : (P : Subgroup L) ≤ (suzukiU a K).comap e'.toMonoidHom := by
    intro y hy
    rw [mem_comap, MulEquiv.coe_toMonoidHom, he']
    exact hg _ (mem_map_of_mem _ hy)
  have hpg : IsPGroup 2 ((suzukiU a K).comap e'.toMonoidHom) :=
    (CFSG.LieType.SteinbergBR.isPGroup_suzukiU hK).comap_of_injective _ e'.injective
  have heq := P.is_maximal' hpg hle
  show ((suzukiU a K).comap e'.toMonoidHom).map L.subtype = T₁
  rw [heq, hP, subgroupOf_map_subtype, inf_of_le_left hT₁L]

theorem coprime_theta_succ (a : ℕ) : Nat.Coprime (2 ^ (a + 1) + 1) (2 ^ (2 * a + 1) - 1) := by
  have hX : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
  have hY : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have key : (2 ^ (a + 1) + 1) * (2 ^ (a + 1) - 1) = 2 * (2 ^ (2 * a + 1) - 1) + 1 := by
    have h3 : (2 : ℤ) ^ (a + 1) * 2 ^ (a + 1) = 2 * 2 ^ (2 * a + 1) := by
      rw [← pow_add, ← pow_succ']
      congr 1
      ring
    zify [hX, hY]
    linear_combination h3
  show Nat.gcd _ _ = 1
  have hg1 := Nat.gcd_dvd_left (2 ^ (a + 1) + 1) (2 ^ (2 * a + 1) - 1)
  have hg2 := Nat.gcd_dvd_right (2 ^ (a + 1) + 1) (2 ^ (2 * a + 1) - 1)
  have h4 : Nat.gcd (2 ^ (a + 1) + 1) (2 ^ (2 * a + 1) - 1) ∣ 2 * (2 ^ (2 * a + 1) - 1) + 1 :=
    key ▸ dvd_mul_of_dvd_left hg1 _
  exact Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_of_dvd_right hg2 2)).mp h4)

theorem exists_eq_suzukiSElt_mul_suzukiDElt [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {L : Subgroup G} (e : L ≃* suzukiGroup a K)
    {d : G} (hdL : d ∈ L) (hdN : d ∈ normalizer (szModelU L e : Set G)) :
    ∃ (u₀ v₀ : K) (l : Kˣ), e ⟨d, hdL⟩ = suzukiSElt a K u₀ v₀ * suzukiDElt a K l := by
  obtain ⟨-, -, hNB, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.Suzuki_model_opposite_root_interface ha hK
  have hconj : ∀ g : L, e g ∈ suzukiU a K ↔ e (⟨d, hdL⟩ * g * ⟨d, hdL⟩⁻¹) ∈ suzukiU a K := by
    intro g
    have h1 : (g : G) ∈ szModelU L e ↔ e g ∈ suzukiU a K :=
      ⟨fun h => by obtain ⟨_, h'⟩ := mem_szModelU.mp h; exact h', fun h => mem_szModelU.mpr ⟨g.2, h⟩⟩
    have h2 : ((⟨d, hdL⟩ * g * ⟨d, hdL⟩⁻¹ : L) : G) ∈ szModelU L e ↔
        e (⟨d, hdL⟩ * g * ⟨d, hdL⟩⁻¹) ∈ suzukiU a K :=
      ⟨fun h => by obtain ⟨_, h'⟩ := mem_szModelU.mp h; exact h', fun h => mem_szModelU.mpr ⟨_, h⟩⟩
    rw [← h1, ← h2]
    exact mem_normalizer_iff.mp hdN g
  have hN : e ⟨d, hdL⟩ ∈ normalizer (suzukiU a K : Set (suzukiGroup a K)) := by
    refine mem_normalizer_iff.mpr fun x => ?_
    obtain ⟨g, rfl⟩ := e.surjective x
    rw [hconj g, map_mul, map_mul, map_inv]
  rw [hNB] at hN
  obtain ⟨⟨⟨u₀, v₀⟩, l⟩, hp, -⟩ := (suzuki_borel_structure hK).2.2.2.2.2.2.1 _ hN
  exact ⟨u₀, v₀, l, hp⟩

theorem pow_theta_succ_generator_of_generator [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {l : K} (hl : ∀ w : K, w ≠ 0 → ∃ m : ℕ, l ^ m = w) :
    ∀ w : K, w ≠ 0 → ∃ m : ℕ, (l ^ (2 ^ (a + 1) + 1)) ^ m = w := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  have h1N : 1 < 2 ^ (2 * a + 1) - 1 := by
    have : 2 ^ 2 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hl0 : l ≠ 0 := by
    rintro rfl
    have hall : ∀ w : K, w = 0 ∨ w = 1 := by
      intro w
      by_cases hw : w = 0
      · exact Or.inl hw
      · obtain ⟨m, hm⟩ := hl w hw
        rcases m with _ | m
        · exact Or.inr (by rw [← hm, pow_zero])
        · exact (hw (by rw [← hm, zero_pow (Nat.succ_ne_zero _)])).elim
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun w _ => by
      rcases hall w with hw | hw <;> simp [hw]
    have h4 := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ, hcardK] at h4
    have h5 : 2 ^ 2 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (h5.trans h4) (by norm_num)
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime (coprime_theta_succ a) h1N
  have hq : l ^ (2 ^ (2 * a + 1) - 1) = 1 := by
    rw [← hcardK]
    exact FiniteField.pow_card_sub_one_eq_one l hl0
  intro w hw
  obtain ⟨m, rfl⟩ := hl w hw
  refine ⟨s * m, ?_⟩
  rw [← pow_mul, ← mul_assoc, pow_mul,
    ← Nat.mod_add_div ((2 ^ (a + 1) + 1) * s) (2 ^ (2 * a + 1) - 1), hs, pow_add, pow_mul, hq,
    one_pow, mul_one, pow_one]

end CFSG.SeitzReduction.RankOne
