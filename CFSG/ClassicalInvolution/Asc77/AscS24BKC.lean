module

public import CFSG.ClassicalInvolution.Asc77.AscS24BIV
public import CFSG.ClassicalInvolution.Asc77.AscS24BSwap

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] [Fact p.Prime] in
theorem exists_conj_of_mul_odd {a c : G} (ha : a * a = 1) (hac : a * c * (a * c) = 1)
    {O : Subgroup G} (hO : Odd (Nat.card ↥O)) (hc : c ∈ O) : ∃ o ∈ O, o * a * o⁻¹ = a * c := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hinv : a * c * a⁻¹ = c⁻¹ := by
    rw [hainv]
    have h1 : a * c * a * c = 1 := by rw [← hac]; group
    calc a * c * a = a * c * a * c * c⁻¹ := by group
      _ = c⁻¹ := by rw [h1, one_mul]
  have hodd : Odd (orderOf c) := Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O hc)
  obtain ⟨m, hm⟩ := hodd
  have hpow : c ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one c
  have h2m : c ^ (2 * m) = c⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact hpow
  have key : a * (c ^ m)⁻¹ * a⁻¹ = c ^ m := by
    rw [← inv_pow, ← conj_pow]
    congr 1
    rw [show a * c⁻¹ * a⁻¹ = (a * c * a⁻¹)⁻¹ by group, hinv, inv_inv]
  refine ⟨c ^ m, Subgroup.pow_mem _ hc m, ?_⟩
  calc c ^ m * a * (c ^ m)⁻¹ = c ^ m * (a * (c ^ m)⁻¹ * a⁻¹) * a := by group
    _ = c ^ (2 * m) * a := by rw [key, two_mul, pow_add]
    _ = a * c * a⁻¹ * a := by rw [h2m, hinv]
    _ = a * c := by group

omit [Fact p.Prime] in
theorem exists_conj_of_mem_coset {W : Subgroup G} (hW2 : IsPGroup 2 W) {a t₁ : G}
    (ha : a ∈ Subgroup.normalizer (W : Set G)) (ha2 : a * a ∈ W) (ht : a⁻¹ * t₁ ∈ W ⊔ OCW W)
    (ht2 : t₁ * t₁ = 1) :
    ∃ w ∈ W, a * w * (a * w) = 1 ∧ ∃ o ∈ OCW W, o * (a * w) * o⁻¹ = t₁ := by
  obtain ⟨w, hw, c, hc, hwc⟩ := Thompson.mem_sup_OCW_iff.mp ht
  have ht₁ : t₁ = a * w * c := by
    calc t₁ = a * (a⁻¹ * t₁) := by group
      _ = a * w * c := by rw [← hwc]; group
  set b := a * w with hb
  have hbN : b ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ ha (Subgroup.le_normalizer hw)
  have hbW : b * b ∈ W := by
    have h1 : a * w * a⁻¹ ∈ W := (Thompson.mem_normalizer_iff_of_mem ha w).mpr hw
    have e : b * b = (a * w * a⁻¹) * (a * a) * w := by rw [hb]; group
    rw [e]
    exact W.mul_mem (W.mul_mem h1 ha2) hw
  have hbc : b * c * (b * c) = 1 := by rw [← ht₁]; exact ht2
  have hbO : b * b ∈ OCW W := by
    have hbON : b ∈ Subgroup.normalizer (OCW W : Set G) :=
      Thompson.normalizer_le_normalizer_OCW W hbN
    have h1 : b * c⁻¹ * b⁻¹ ∈ OCW W :=
      (Subgroup.mem_normalizer_iff.mp hbON _).mp (Subgroup.inv_mem _ hc)
    have e : b * b = b * c⁻¹ * b⁻¹ * c⁻¹ := by
      have h2 : b * c * b = c⁻¹ := by
        calc b * c * b = b * c * (b * c) * c⁻¹ := by group
          _ = c⁻¹ := by rw [hbc, one_mul]
      calc b * b = b * (b * c * b) * b⁻¹ * c⁻¹ := by group
        _ = b * c⁻¹ * b⁻¹ * c⁻¹ := by rw [h2]
    rw [e]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hc)
  have hbb : b * b = 1 := by
    refine Asc77.eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hbO ?_
    exact hW2.to_le (Subgroup.zpowers_le.mpr hbW)
  obtain ⟨o, ho, hoc⟩ := exists_conj_of_mul_odd hbb hbc (oddCoreOf_odd_natCard _) hc
  exact ⟨w, hw, hbb, o, ho, by rw [hoc, ← ht₁]⟩

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

include C in
theorem conj_z_of_coset [IsSimpleGroup G] {a t₁ : G} (ha : a ∈ Subgroup.normalizer (W : Set G))
    (ha2 : a * a ∈ W) (hmem : ∀ w ∈ W, a * w * (a * w) = 1 → a * w ∈ K ⊔ K')
    (ht : a⁻¹ * t₁ ∈ W ⊔ OCW W) (ht2 : t₁ * t₁ = 1) (ht1 : t₁ ≠ 1) :
    ∃ g : G, g * z * g⁻¹ = t₁ := by
  obtain ⟨w, hw, hw2, o, -, ho⟩ :=
    exists_conj_of_mem_coset (Thompson.isPGroup_of_mem_WSet C.hd.hW) ha ha2 ht ht2
  have hne : a * w ≠ 1 := by
    intro h; apply ht1; rw [← ho, h]; group
  obtain ⟨g, hg⟩ := C.conj_z_of_mem_sup (hmem w hw hw2) hw2 hne
  exact ⟨o * g, by rw [← ho, ← hg]; group⟩

include C in
theorem kc_aux [IsSimpleGroup G] {t : G} (htM : t ∈ MGrp Ω W) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    {a : G} (haM : a ∈ MGrp Ω W) (ha2 : a * a ∈ W)
    (hmem : ∀ w ∈ W, a * w * (a * w) = 1 → a * w ∈ K ⊔ K') {m : ↥(MGrp Ω W)}
    (e : piM Ω W m * piM Ω W ⟨a, haM⟩ * (piM Ω W m)⁻¹ = piM Ω W ⟨t, htM⟩) :
    ∃ g : G, g * z * g⁻¹ = t := by
  have hmN : (m : G) ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W m.2
  have haN : a ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W haM
  have htN : t ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W htM
  have ht₁N : (m : G)⁻¹ * t * m ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hmN) htN) hmN
  have e' : Thompson.piG W (m : G) * Thompson.piG W a * (Thompson.piG W (m : G))⁻¹ =
      Thompson.piG W t := congrArg Subtype.val e
  have hpi : Thompson.piG W a = Thompson.piG W ((m : G)⁻¹ * t * m) := by
    rw [Thompson.piG_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ hmN) htN) hmN,
      Thompson.piG_mul (Subgroup.inv_mem _ hmN) htN, Thompson.piG_inv hmN, ← e']
    group
  have hmem' := (Thompson.piG_eq_iff haN ht₁N).mp hpi
  have ht₁2 : (m : G)⁻¹ * t * m * ((m : G)⁻¹ * t * m) = 1 := by
    calc (m : G)⁻¹ * t * m * ((m : G)⁻¹ * t * m) = (m : G)⁻¹ * (t * t) * m := by group
      _ = 1 := by rw [ht2]; group
  have ht₁1 : (m : G)⁻¹ * t * m ≠ 1 := by
    intro h; apply ht1
    calc t = (m : G) * ((m : G)⁻¹ * t * m) * (m : G)⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨g, hg⟩ := C.conj_z_of_coset haN ha2 hmem hmem' ht₁2 ht₁1
  refine ⟨(m : G) * g, ?_⟩
  calc (m : G) * g * z * ((m : G) * g)⁻¹ = (m : G) * (g * z * g⁻¹) * (m : G)⁻¹ := by group
    _ = t := by rw [hg]; group

include C in
theorem kc [IsSimpleGroup G] {t : G} (htS : t ∈ (S : Subgroup G)) (htM : t ∈ MGrp Ω W)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : ∃ g : G, g * z * g⁻¹ = t := by
  by_cases htW : t ∈ W
  · exact C.conj_z_of_mem_sup (C.mem_sup_of_mul_self htW ht2) ht2 ht1
  have hW2 := Thompson.isPGroup_of_mem_WSet C.hd.hW
  have htN : t ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W htM
  set τ := piM Ω W ⟨t, htM⟩ with hτ
  have hτ2 : τ * τ = 1 := by
    rw [hτ, ← map_mul]
    have : (⟨t, htM⟩ : ↥(MGrp Ω W)) * ⟨t, htM⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    have h1 : Thompson.piG W t = 1 := congrArg Subtype.val h
    have h2 : t ∈ W ⊔ OCW W := (Thompson.piG_eq_one_iff htN).mp h1
    have ht2' : IsPGroup 2 (Subgroup.zpowers t) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr htS)
    exact htW (Thompson.mem_of_isPGroup_of_mem_sup_OCW hW2 ht2' h2)
  have hφ2 : C.D.φ τ * C.D.φ τ = 1 := by rw [← map_mul, hτ2, map_one]
  have hφ1 : C.D.φ τ ≠ 1 := fun h => hτ1 (C.D.φ.injective (h.trans (map_one _).symm))
  have hinv := T7C2.mem_invs4 _ hφ2 hφ1
  have hab : C.D.φ (T7D.imgQ C.D.F.ρ) ≠ C.D.φ (T7D.imgQ C.D.F.ρ') :=
    fun h => C.D.hab (C.D.φ.injective h)
  have hcomm : C.D.φ (T7D.imgQ C.D.F.ρ) * C.D.φ (T7D.imgQ C.D.F.ρ') =
      C.D.φ (T7D.imgQ C.D.F.ρ') * C.D.φ (T7D.imgQ C.D.F.ρ) := by
    rw [← map_mul, ← map_mul, C.D.hcomm]
  have hrM : C.D.F.ρ.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR C.D.F.ρ.hr
  have htM' : C.D.F.ρ'.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ'.hR C.D.F.ρ'.hr
  have hra : T7D.imgQ C.D.F.ρ = piM Ω W ⟨_, hrM⟩ := Subtype.ext rfl
  have hta : T7D.imgQ C.D.F.ρ' = piM Ω W ⟨_, htM'⟩ := Subtype.ext rfl
  have hrr : C.D.F.ρ.r * C.D.F.ρ.r ∈ W := by rw [C.r_mul_self]; exact C.hd.hzW
  have hrt : C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r) ∈ W := by
    have e : C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r) =
        C.D.F.ρ.r * C.D.F.ρ.r * (C.D.F.ρ'.r * C.D.F.ρ'.r) := by
      calc C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r)
          = C.D.F.ρ.r * (C.D.F.ρ'.r * C.D.F.ρ.r) * C.D.F.ρ'.r := by group
        _ = C.D.F.ρ.r * (C.D.F.ρ.r * C.D.F.ρ'.r) * C.D.F.ρ'.r := by rw [C.commute_r_t.eq]
        _ = C.D.F.ρ.r * C.D.F.ρ.r * (C.D.F.ρ'.r * C.D.F.ρ'.r) := by group
    rw [e, C.r_mul_self, C.t_mul_self]
    exact W.mul_mem C.hd.hzW C.hd.hzW
  rcases perm4_inv_conj _ hinv _ (C.φ_imgQ_mem _) _ (C.φ_imgQ_mem _) hab hcomm with
    ⟨σ, -, hσ⟩ | ⟨σ, -, hσ⟩
  · obtain ⟨m, hm⟩ := piM_surjective W (C.D.φ.symm σ)
    refine C.kc_aux htM ht2 ht1 hrM hrr (fun w hw h => C.r_mul_mem_sup hw h) (m := m) ?_
    apply C.D.φ.injective
    rw [map_mul, map_mul, map_inv, hm, MulEquiv.apply_symm_apply, ← hra]
    exact hσ
  · obtain ⟨m, hm⟩ := piM_surjective W (C.D.φ.symm σ)
    have hrtM : C.D.F.ρ.r * C.D.F.ρ'.r ∈ MGrp Ω W := Subgroup.mul_mem _ hrM htM'
    refine C.kc_aux htM ht2 ht1 hrtM hrt (fun w hw h => C.rt_mul_mem_sup hw h) (m := m) ?_
    apply C.D.φ.injective
    have hprod : piM Ω W ⟨_, hrtM⟩ = T7D.imgQ C.D.F.ρ * T7D.imgQ C.D.F.ρ' := by
      rw [hra, hta, ← map_mul]; rfl
    rw [map_mul, map_mul, map_inv, hm, MulEquiv.apply_symm_apply, hprod, map_mul]
    exact hσ

end Ctx8

end S24B

end CFSG.ClassicalInvolution.Asc77
