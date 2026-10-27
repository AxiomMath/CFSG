module

public import CFSG.GH74.Uniqueness.SU.KI1r4QAbs
public import CFSG.GH74.Uniqueness.SU.SU5L34
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.Q64

open Subgroup CFSG CFSG.OrderReductions.FrattiniAutomorphisms CFSG.GH74.Uniqueness.SU.SU5

variable {H : Type} [Group H]

@[expose] def actV (R : Subgroup H) :
    ↥(normalizer (R : Set H)) →* MulAut (↥R ⧸ frattini ↥R) :=
  (quotientAutomorphism (frattini ↥R)).comp R.normalizerMonoidHom

theorem actV_apply (R : Subgroup H) (g : ↥(normalizer (R : Set H))) (r : ↥R) :
    actV R g (r : ↥R ⧸ frattini ↥R) = ((R.normalizerMonoidHom g r : ↥R) : ↥R ⧸ frattini ↥R) :=
  quotientAutomorphism_apply (frattini ↥R) _ r

theorem exists_pow_eq_one_of_actV_eq_one [Finite H] (R : Subgroup H) (hR2 : IsPGroup 2 R)
    (hC : centralizer (R : Set H) ≤ R) (g : ↥(normalizer (R : Set H))) (hg : actV R g = 1) :
    ∃ n : ℕ, (g : H) ^ 2 ^ n = 1 := by
  have hmem : (R.normalizerMonoidHom g : MulAut ↥R) ∈ (quotientAutomorphism (frattini ↥R)).ker :=
    MonoidHom.mem_ker.mpr hg
  obtain ⟨n, hn⟩ := frattini_automorphism_kernel_isPGroup 2 hR2
    ⟨R.normalizerMonoidHom g, hmem⟩
  have hn' : R.normalizerMonoidHom (g ^ 2 ^ n) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hn
  have hcen : (g : H) ^ 2 ^ n ∈ centralizer (R : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 := congrArg (fun f : MulAut ↥R => ((f ⟨q, hq⟩ : ↥R) : H)) hn'
    have h2 : (((g ^ 2 ^ n : ↥(normalizer (R : Set H))) : H)) * q *
        (((g ^ 2 ^ n : ↥(normalizer (R : Set H))) : H))⁻¹ = q := h1
    rw [Subgroup.coe_pow] at h2
    calc q * (g : H) ^ 2 ^ n = ((g : H) ^ 2 ^ n * q * ((g : H) ^ 2 ^ n)⁻¹) * (g : H) ^ 2 ^ n := by
          rw [h2]
      _ = (g : H) ^ 2 ^ n * q := by group
  obtain ⟨m, hm⟩ := hR2 ⟨(g : H) ^ 2 ^ n, hC hcen⟩
  refine ⟨n + m, ?_⟩
  have hm' : ((g : H) ^ 2 ^ n) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  rwa [← pow_mul, ← pow_add] at hm'

theorem mem_of_actV_eq_one [Finite H] (R : Subgroup H) (hR2 : IsPGroup 2 R)
    (hC : centralizer (R : Set H) ≤ R)
    (hO2 : ∀ W : Subgroup H, W ≤ normalizer (R : Set H) → IsPGroup 2 W →
      (∀ n ∈ normalizer (R : Set H), ∀ w ∈ W, n * w * n⁻¹ ∈ W) → W ≤ R)
    (g : ↥(normalizer (R : Set H))) (hg : actV R g = 1) : (g : H) ∈ R := by
  have hK2 : IsPGroup 2 (actV R).ker := by
    rintro ⟨k, hk⟩
    obtain ⟨n, hn⟩ := exists_pow_eq_one_of_actV_eq_one R hR2 hC k (MonoidHom.mem_ker.mp hk)
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hn
  have hK'2 : IsPGroup 2 ((actV R).ker.map (normalizer (R : Set H)).subtype) := hK2.map _
  have hK'N : (actV R).ker.map (normalizer (R : Set H)).subtype ≤ normalizer (R : Set H) := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hK'norm : ∀ n ∈ normalizer (R : Set H), ∀ w ∈ (actV R).ker.map (normalizer (R : Set H)).subtype,
      n * w * n⁻¹ ∈ (actV R).ker.map (normalizer (R : Set H)).subtype := by
    intro n hn w hw
    obtain ⟨k, hk, rfl⟩ := hw
    refine ⟨⟨n, hn⟩ * k * ⟨n, hn⟩⁻¹, ?_, rfl⟩
    exact (MonoidHom.normal_ker (actV R)).conj_mem k hk ⟨n, hn⟩
  have hle := hO2 _ hK'N hK'2 hK'norm
  exact hle ⟨g, MonoidHom.mem_ker.mpr hg, rfl⟩

@[expose] def imV (R U : Subgroup H) : Subgroup (↥R ⧸ frattini ↥R) :=
  (U.subgroupOf R).map (QuotientGroup.mk' (frattini ↥R))

theorem mem_imV_iff (R U : Subgroup H) (hΦU : ∀ z ∈ frattini ↥R, (z : H) ∈ U) (r : ↥R) :
    (r : ↥R ⧸ frattini ↥R) ∈ imV R U ↔ (r : H) ∈ U := by
  constructor
  · rintro ⟨u, hu, hur⟩
    have h1 : u⁻¹ * r ∈ frattini ↥R := QuotientGroup.eq.mp hur
    have h2 : (r : H) = (u : H) * (((u⁻¹ * r : ↥R)) : H) := by
      simp
    rw [h2]
    exact U.mul_mem (Subgroup.mem_subgroupOf.mp hu) (hΦU _ h1)
  · intro h
    exact ⟨r, Subgroup.mem_subgroupOf.mpr h, rfl⟩

theorem actV_mem_iff (R U U' : Subgroup H) (hΦU : ∀ z ∈ frattini ↥R, (z : H) ∈ U)
    (hΦU' : ∀ z ∈ frattini ↥R, (z : H) ∈ U')
    (g : ↥(normalizer (R : Set H))) (hg : ∀ u : H, u ∈ U ↔ (g : H) * u * (g : H)⁻¹ ∈ U')
    (v : ↥R ⧸ frattini ↥R) : v ∈ imV R U ↔ actV R g v ∈ imV R U' := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective v
  rw [actV_apply, mem_imV_iff R U hΦU, mem_imV_iff R U' hΦU']
  exact hg r

theorem conj_map_eq_or {R U₁ U₂ : Subgroup H} (hF : L34Facts R U₁ U₂) (g : H)
    (hgN : g ∈ normalizer (R : Set H)) (U : Subgroup H) (hUR : U ≤ R) (hUE : IsE 4 U) :
    U.map (MulAut.conj g).toMonoidHom = U₁ ∨ U.map (MulAut.conj g).toMonoidHom = U₂ := by
  refine hF.unique _ ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgN u).mp (hUR hu)
  · exact (isE_map (MulAut.conj g).injective).mpr hUE

theorem mem_iff_conj_of_map_eq {U U' : Subgroup H} {g : H}
    (h : U.map (MulAut.conj g).toMonoidHom = U') (u : H) : u ∈ U ↔ g * u * g⁻¹ ∈ U' := by
  constructor
  · intro hu
    rw [← h]
    exact ⟨u, hu, by simp [MulAut.conj_apply]⟩
  · intro hu
    rw [← h] at hu
    obtain ⟨w, hw, hwu⟩ := hu
    have : w = u := by
      have h3 : g * w * g⁻¹ = g * u * g⁻¹ := by simpa [MulAut.conj_apply] using hwu
      simpa using h3
    rw [← this]
    exact hw

theorem normalizes_of_odd {R U₁ U₂ : Subgroup H} (hF : L34Facts R U₁ U₂)
    (g : H) (hgN : g ∈ normalizer (R : Set H)) (m : ℕ) (hm : Odd m) (hgm : g ^ m = 1) :
    (∀ u : H, u ∈ U₁ ↔ g * u * g⁻¹ ∈ U₁) ∧ (∀ u : H, u ∈ U₂ ↔ g * u * g⁻¹ ∈ U₂) := by
  obtain ⟨h1, h2⟩ := map_conj_eq_of_odd U₁ U₂ hF.A_ne_B g m hm hgm
    (conj_map_eq_or hF g hgN U₁ hF.A_le hF.A_E) (conj_map_eq_or hF g hgN U₂ hF.B_le hF.B_E)
  exact ⟨mem_iff_conj_of_map_eq h1, mem_iff_conj_of_map_eq h2⟩

theorem card_imV_eq_four {R U : Subgroup H} (hUR : U ≤ R) (hU16 : Nat.card U = 16)
    (hΦ4 : Nat.card (frattini ↥R) = 4) (hΦU : ∀ z ∈ frattini ↥R, (z : H) ∈ U) :
    Nat.card (imV R U) = 4 := by
  set U' : Subgroup ↥R := U.subgroupOf R with hU'
  have hle : frattini ↥R ≤ U' := fun z hz => Subgroup.mem_subgroupOf.mpr (hΦU z hz)
  set f : ↥U' →* ↥R ⧸ frattini ↥R := (QuotientGroup.mk' (frattini ↥R)).comp U'.subtype with hf
  have hrange : f.range = imV R U := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : f.ker = (frattini ↥R).subgroupOf U' := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (u : ↥R)
  have hkerc : Nat.card f.ker = 4 := by
    rw [hker, ← hΦ4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hU'c : Nat.card U' = 16 := by
    rw [hU', ← hU16]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUR).toEquiv
  have h := Subgroup.card_ker_mul_card_range f
  rw [hkerc, hU'c, hrange] at h
  omega

theorem imV_sup {R U₁ U₂ : Subgroup H} (hU₁ : U₁ ≤ R) (hU₂ : U₂ ≤ R) (hsup : U₁ ⊔ U₂ = R) :
    imV R U₁ ⊔ imV R U₂ = ⊤ := by
  have h1 : U₁.subgroupOf R ⊔ U₂.subgroupOf R = ⊤ := by
    apply Subgroup.map_injective R.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hU₁, inf_of_le_left hU₂, hsup, Subgroup.map_top, Subgroup.range_subtype]
  unfold imV
  rw [← Subgroup.map_sup, h1]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem frattini_mem {R U₁ U₂ : Subgroup H} (hF : L34Facts R U₁ U₂)
    (hfr : frattini ↥R = center ↥R) (z : ↥R) (hz : z ∈ frattini ↥R) :
    (z : H) ∈ U₁ ∧ (z : H) ∈ U₂ := by
  rw [hfr] at hz
  have hZ : (z : H) ∈ Zc R := by
    rw [mem_Zc]
    refine ⟨z.2, fun h hh => ?_⟩
    have := Subgroup.mem_center_iff.mp hz ⟨h, hh⟩
    exact (congrArg Subtype.val this).symm
  rw [← hF.inf_eq] at hZ
  exact ⟨hZ.1, hZ.2⟩

theorem injective_actV_restrict [Finite H] {R : Subgroup H} (hR2 : IsPGroup 2 R)
    (hC : centralizer (R : Set H) ≤ R)
    (hO2 : ∀ W : Subgroup H, W ≤ normalizer (R : Set H) → IsPGroup 2 W →
      (∀ n ∈ normalizer (R : Set H), ∀ w ∈ W, n * w * n⁻¹ ∈ W) → W ≤ R)
    (P : Subgroup H) (hodd : ¬ 2 ∣ Nat.card P) :
    Function.Injective ((actV R).comp (P.subgroupOf (normalizer (R : Set H))).subtype) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg1 : actV R (g : ↥(normalizer (R : Set H))) = 1 := hg
  have hgR : ((g : ↥(normalizer (R : Set H))) : H) ∈ R := mem_of_actV_eq_one R hR2 hC hO2 _ hg1
  have hgP : ((g : ↥(normalizer (R : Set H))) : H) ∈ P := g.2
  obtain ⟨n, hn⟩ := hR2 ⟨_, hgR⟩
  have hn' : ((g : ↥(normalizer (R : Set H))) : H) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hcard : ((g : ↥(normalizer (R : Set H))) : H) ^ Nat.card P = 1 := by
    have := pow_card_eq_one' (G := ↥P) (x := ⟨_, hgP⟩)
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (2 ^ n) (Nat.card P) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h1 : ((g : ↥(normalizer (R : Set H))) : H) ^ Nat.gcd (2 ^ n) (Nat.card P) = 1 :=
    pow_gcd_eq_one.mpr ⟨hn', hcard⟩
  rw [hcop, pow_one] at h1
  exact Subtype.ext (Subtype.ext h1)

theorem card_map_actV [Finite H] {R : Subgroup H} (hR2 : IsPGroup 2 R)
    (hC : centralizer (R : Set H) ≤ R)
    (hO2 : ∀ W : Subgroup H, W ≤ normalizer (R : Set H) → IsPGroup 2 W →
      (∀ n ∈ normalizer (R : Set H), ∀ w ∈ W, n * w * n⁻¹ ∈ W) → W ≤ R)
    (P : Subgroup H) (hPN : P ≤ normalizer (R : Set H)) (hodd : ¬ 2 ∣ Nat.card P) :
    Nat.card ((P.subgroupOf (normalizer (R : Set H))).map (actV R)) = Nat.card P := by
  have hinj := injective_actV_restrict hR2 hC hO2 P hodd
  have hrange : ((actV R).comp (P.subgroupOf (normalizer (R : Set H))).subtype).range =
      (P.subgroupOf (normalizer (R : Set H))).map (actV R) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, card_range_of_injective hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv

theorem actV_preserves_of_odd {R U₁ U₂ : Subgroup H} (hF : L34Facts R U₁ U₂)
    (hU₁ : ∀ z ∈ frattini ↥R, (z : H) ∈ U₁) (hU₂ : ∀ z ∈ frattini ↥R, (z : H) ∈ U₂)
    (P : Subgroup H) (hodd : ¬ 2 ∣ Nat.card P) :
    ∀ φ ∈ (P.subgroupOf (normalizer (R : Set H))).map (actV R), ∀ v,
      (v ∈ imV R U₁ ↔ φ v ∈ imV R U₁) ∧ (v ∈ imV R U₂ ↔ φ v ∈ imV R U₂) := by
  intro φ hφ v
  obtain ⟨g, hg, rfl⟩ := hφ
  have hgP : (g : H) ∈ P := hg
  have hmodd : Odd (Nat.card P) := Nat.odd_iff.mpr (by omega)
  have hgm : (g : H) ^ Nat.card P = 1 := by
    have := pow_card_eq_one' (G := ↥P) (x := ⟨_, hgP⟩)
    exact congrArg Subtype.val this
  obtain ⟨hn1, hn2⟩ := normalizes_of_odd hF (g : H) g.2 (Nat.card P) hmodd hgm
  exact ⟨actV_mem_iff R U₁ U₁ hU₁ hU₁ g hn1 v, actV_mem_iff R U₂ U₂ hU₂ hU₂ g hn2 v⟩

theorem card_odd_dvd_nine [Finite H] {R U₁ U₂ : Subgroup H} (hF : L34Facts R U₁ U₂)
    (hR2 : IsPGroup 2 R)
    (hC : centralizer (R : Set H) ≤ R)
    (hO2 : ∀ W : Subgroup H, W ≤ normalizer (R : Set H) → IsPGroup 2 W →
      (∀ n ∈ normalizer (R : Set H), ∀ w ∈ W, n * w * n⁻¹ ∈ W) → W ≤ R)
    (hfr : frattini ↥R = center ↥R) (hΦ4 : Nat.card (frattini ↥R) = 4)
    (P : Subgroup H) (hPN : P ≤ normalizer (R : Set H)) (hodd : ¬ 2 ∣ Nat.card P) :
    Nat.card P ∣ 9 := by
  classical
  have hU₁ : ∀ z ∈ frattini ↥R, (z : H) ∈ U₁ := fun z hz => (frattini_mem hF hfr z hz).1
  have hU₂ : ∀ z ∈ frattini ↥R, (z : H) ∈ U₂ := fun z hz => (frattini_mem hF hfr z hz).2
  have hE₁ : Nat.card U₁ = 16 := by have := hF.A_E.2; norm_num at this; exact this
  have hE₂ : Nat.card U₂ = 16 := by have := hF.B_E.2; norm_num at this; exact this
  have hV₁ : Nat.card (imV R U₁) = 4 := card_imV_eq_four hF.A_le hE₁ hΦ4 hU₁
  have hV₂ : Nat.card (imV R U₂) = 4 := card_imV_eq_four hF.B_le hE₂ hΦ4 hU₂
  have hsup := imV_sup hF.A_le hF.B_le hF.sup_eq
  have hQcard := card_map_actV hR2 hC hO2 P hPN hodd
  have hQodd : ¬ 2 ∣ Nat.card ((P.subgroupOf (normalizer (R : Set H))).map (actV R)) := by
    rw [hQcard]; exact hodd
  have h9 := odd_card_dvd_nine (imV R U₁) (imV R U₂) hV₁ hV₂ hsup _ hQodd
    (actV_preserves_of_odd hF hU₁ hU₂ P hodd)
  rwa [hQcard] at h9

end CFSG.GH74.Uniqueness.SU.K.R4.Q64
