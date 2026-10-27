module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S9d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S9c

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven

theorem Nine81.eq_three_of_pow {p f : ℕ} (hp : p.Prime) (hq : p ^ f = 3) : p = 3 ∧ f = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    norm_num at hq
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hq ▸ dvd_pow_self p hf)
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num) (hq.trans (pow_one 3).symm)⟩

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

theorem lieModel_J_of_q3 (H₁ : h.L81Hyp) (hSp : CF81Sp4Three) {p f : ℕ} (hp : p.Prime)
    (hK : Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 p f) (hq : p ^ f = 3) :
    Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2 := by
  obtain ⟨rfl, rfl⟩ := Nine81.eq_three_of_pow hp hq
  obtain ⟨-, p₀, f₀, hp₀, -, hf₀, hK₀, hJ₀⟩ := Hyp52.Sec8Case.exists_params h.toHyp52 H₁.case8
  have h0 : p₀ = 3 ∧ f₀ = 1 := by
    rcases hK₀ with hK₀ | ⟨h1, h2, -⟩
    · exact Nine81.eq_three_of_pow hp₀ (hSp _ p₀ f₀ hp₀ hf₀ hK hK₀)
    · exact ⟨h1, h2⟩
  obtain ⟨rfl, rfl⟩ := h0
  rcases hJ₀ with hL | ⟨-, -, hA⟩
  · exact hL
  · exact Or.inl ⟨by decide,
      CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six _
        hA⟩

namespace Data

variable {H₁ : h.L81Hyp} (d : Data H₁)

theorem centralizer_eq_of_q3 (hNine : CF81L2NineCent) (hSp : CF81Sp4Three) {v : H}
    (hst : d.Stage7 v) {p f : ℕ} (hp : p.Prime)
    (hK : Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 p f) (hq : p ^ f = 3) :
    centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H) =
      (oddCoreIn (centralizer ({h.a} : Set H)) ⊓ centralizer ({h.a * d.z} : Set H)) ⊔ h.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H) with hW
  have hΓ := hNine _ (H₁.lieModel_J_of_q3 hSp hp hK hq) _ d.orderOf_zbar
  obtain ⟨N, hNO, hNN, hNodd⟩ := d.exists_oddCore_Y9 hst
  have hWN : W ≤ normalizer (h.J : Set H) := inf_le_left.trans H₁.centralizer_le_normalizer_J
  have hzN : d.z ∈ normalizer (h.J : Set H) := le_normalizer d.z_mem_J
  have hpow : ∀ x ∈ W, ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
    intro x hx
    obtain ⟨k, o, ho, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hyo : orderOf (x ^ 2 ^ k) ∣ o :=
      orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, ← hord, pow_orderOf_eq_one])
    have hyW : x ^ 2 ^ k ∈ W := pow_mem hx _
    have hyN := hWN hyW
    refine ⟨k, hNodd _ ?_ (Odd.of_dvd_nat ho hyo)⟩
    refine mem_inf.mpr ⟨(mem_inf.mp hyW).1, (rhoE_eq_one_iff hyN).mp ?_⟩
    have hρΓ : rhoE h.J (x ^ 2 ^ k) ∈ centralizer ({rhoE h.J d.z} : Set (MulAut _)) := by
      rw [mem_centralizer_singleton_iff, ← rhoE_mul hyN hzN, ← rhoE_mul hzN hyN,
        d.comm_z_of_mem_W hyW]
    rw [rhoE_of_mem_J d.z_mem_J] at hρΓ
    obtain ⟨n, hn⟩ := hΓ ⟨_, hρΓ⟩
    have h1 : orderOf (rhoE h.J (x ^ 2 ^ k)) ∣ 2 ^ n :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
    have h2 : orderOf (rhoE h.J (x ^ 2 ^ k)) ∣ orderOf (x ^ 2 ^ k) := by
      rw [rhoE_of_mem hyN, ← Subgroup.orderOf_mk _ hyN]
      exact orderOf_map_dvd _ _
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr ho)) h1 (h2.trans hyo))
  have hNC : W ≤ centralizer ({h.a} : Set H) := inf_le_left
  have hNW : (N.subgroupOf W).Normal := ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    simpa using (mem_normalizer_iff.mp (hNN (hNC g.2)) x).mp hx⟩
  have hQ2 : IsPGroup 2 (↥W ⧸ N.subgroupOf W) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hpow x x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
      simpa using hk
  have hS2W : IsPGroup 2 (h.S.subgroupOf W) := h.isPGroup_S.comap_subtype
  obtain ⟨T, hT⟩ := hS2W.exists_le_sylow
  have hTS : (T : Subgroup ↥W).map W.subtype ≤ h.S := by
    obtain ⟨R, hR⟩ := H₁.S_sylow_C
    have hT2 : IsPGroup 2 (((T : Subgroup ↥W).map W.subtype).subgroupOf
        (centralizer ({h.a} : Set H))) := (T.isPGroup'.map _).comap_subtype
    have hle : (R : Subgroup ↥(centralizer ({h.a} : Set H))) ≤
        ((T : Subgroup ↥W).map W.subtype).subgroupOf (centralizer ({h.a} : Set H)) := by
      rw [hR]
      intro x hx
      have hxW : (x : H) ∈ W := d.S_le_W (mem_subgroupOf.mp hx)
      exact mem_subgroupOf.mpr ⟨⟨x, hxW⟩, hT (mem_subgroupOf.mpr (mem_subgroupOf.mp hx)), rfl⟩
    have heq := R.is_maximal' hT2 hle
    intro y hy
    have hyC : y ∈ centralizer ({h.a} : Set H) := hNC (map_subtype_le _ hy)
    have h1 : (⟨y, hyC⟩ : ↥(centralizer ({h.a} : Set H))) ∈
        ((T : Subgroup ↥W).map W.subtype).subgroupOf (centralizer ({h.a} : Set H)) :=
      mem_subgroupOf.mpr hy
    rw [heq, hR] at h1
    exact mem_subgroupOf.mp h1
  have hsurj := QuotientGroup.mk'_surjective (N.subgroupOf W)
  have htop : (T.mapSurjective hsurj : Subgroup (↥W ⧸ N.subgroupOf W)) = ⊤ :=
    ((T.mapSurjective hsurj).is_maximal' (hQ2.to_subgroup ⊤) le_top).symm
  apply le_antisymm
  · intro x hx
    have h1 : QuotientGroup.mk' (N.subgroupOf W) ⟨x, hx⟩ ∈
        (T.mapSurjective hsurj : Subgroup (↥W ⧸ N.subgroupOf W)) := by
      rw [htop]
      exact mem_top _
    rw [Sylow.coe_mapSurjective] at h1
    obtain ⟨t, ht, hte⟩ := mem_map.mp h1
    have h2 : t⁻¹ * ⟨x, hx⟩ ∈ N.subgroupOf W := by
      rw [← QuotientGroup.eq]
      exact hte
    have htS : (t : H) ∈ h.S := hTS (mem_map.mpr ⟨t, ht, rfl⟩)
    have hy : (t : H)⁻¹ * x ∈ N := by simpa using mem_subgroupOf.mp h2
    have hyW : (t : H)⁻¹ * x ∈ W := mul_mem (inv_mem t.2) hx
    rw [show x = t * ((t : H)⁻¹ * x) by group]
    exact mul_mem (mem_sup_right htS) (mem_sup_left (mem_inf.mpr ⟨hNO hy, (mem_inf.mp hyW).2⟩))
  · refine sup_le ?_ d.S_le_W
    exact inf_le_inf_right _ (map_subtype_le _ : oddCoreIn (centralizer ({h.a} : Set H)) ≤ _)

end Data

end L81Hyp

end Hyp59

theorem gs81Step9Input (hCP : CF81L2CentPerfect) (hNine : CF81L2NineCent)
    (hSp : CF81Sp4Three) : GS81Step9Input := by
  intro H _ _ h H₁ d v hst p f hp _ _ hK
  exact ⟨d.layerIn_eq_bot hCP hst, fun hq => d.centralizer_eq_of_q3 hNine hSp hst hp hK hq⟩

end CFSG.ComponentClassification.GSThmB
