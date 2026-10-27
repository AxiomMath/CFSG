module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs


public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

theorem lift62x_inf_ker_eq_bot {Y Z : Type} [Group Y] [Group Z] [Finite Y] (φ : Y →* Z)
    {f : ℕ} {P : Subgroup Y} (hP : IsPGroup f P) (hker : Nat.Coprime f (Nat.card φ.ker)) :
    P ⊓ φ.ker = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgP, hgK⟩
  obtain ⟨k, hk⟩ := hP ⟨g, hgP⟩
  have hpow : g ^ f ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have h1 : orderOf g ∣ f ^ k := orderOf_dvd_of_pow_eq_one hpow
  have h2 : orderOf g ∣ Nat.card φ.ker := φ.ker.orderOf_dvd_natCard hgK
  exact Subgroup.mem_bot.mpr
    (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hker.pow_left k) h1 h2))

theorem lift62x_sylow_map {Y Z : Type} [Group Y] [Group Z] [Finite Y] (φ : Y →* Z)
    (hφ : Function.Surjective φ) {f : ℕ} {P : Subgroup Y} (hP : IsPGroup f P)
    (hPi : ¬ f ∣ P.index) : IsPGroup f (P.map φ) ∧ ¬ f ∣ (P.map φ).index :=
  ⟨hP.map φ, fun h => hPi (h.trans (P.index_map_dvd hφ))⟩

theorem lift62x_exists_mem_normalizer {Y Z : Type} [Group Y] [Group Z] [Finite Y] (φ : Y →* Z)
    (hφ : Function.Surjective φ) {f : ℕ} (hf : f.Prime) {P : Subgroup Y} (hP : IsPGroup f P)
    (hPi : ¬ f ∣ P.index) {z : Z} (hz : z ∈ normalizer ((P.map φ : Subgroup Z) : Set Z)) :
    ∃ y ∈ normalizer (P : Set Y), φ y = z := by
  have : Fact f.Prime := ⟨hf⟩
  obtain ⟨S, rfl⟩ : ∃ S : Sylow f Y, (S : Subgroup Y) = P := ⟨hP.toSylow hPi, rfl⟩
  obtain ⟨j, rfl⟩ := hφ z
  obtain ⟨R, hR⟩ : ∃ R : Subgroup Y, ∀ x, x ∈ R ↔ φ x ∈ (S : Subgroup Y).map φ :=
    ⟨((S : Subgroup Y).map φ).comap φ, fun x => Iff.rfl⟩
  have hSR : (S : Subgroup Y) ≤ R := fun x hx => (hR x).2 (Subgroup.mem_map_of_mem φ hx)
  have hjR : ((j • S : Sylow f Y) : Subgroup Y) ≤ R := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    rw [hR]
    have h1 := (Subgroup.mem_normalizer_iff.mp hz (φ s)).mp (Subgroup.mem_map_of_mem φ hs)
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R (S.subtype hSR) ((j • S).subtype hjR)
  rw [Sylow.smul_subtype] at hr
  have h1 : (r : Y) • S = j • S := Sylow.subtype_injective hr
  have hn : (r : Y)⁻¹ * j ∈ normalizer ((S : Subgroup Y) : Set Y) := by
    have h2 : ((r : Y)⁻¹ * j) • S = S := by rw [mul_smul, ← h1, inv_smul_smul]
    exact Sylow.smul_eq_iff_mem_normalizer.mp h2
  obtain ⟨p, hp, hpr⟩ := Subgroup.mem_map.mp ((hR r).mp r.2)
  refine ⟨p * ((r : Y)⁻¹ * j), Subgroup.mul_mem _ (Subgroup.le_normalizer hp) hn, ?_⟩
  rw [map_mul, map_mul, map_inv, hpr, mul_inv_cancel_left]

theorem lift62x_core (hK : KFactAbelianSylowRankThree) {Y Z : Type} [Group Y] [Finite Y]
    [Group Z] [Finite Z] (hZ : CFSG.IsKGroup Z) (hq : CFSG.Open.IsQuasisimple Z) (φ : Y →* Z)
    (hφ : Function.Surjective φ) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2)
    (hker : Nat.Coprime f (Nat.card φ.ker)) {P A : Subgroup Y} (hP : IsPGroup f P)
    (hPi : ¬ f ∣ P.index) (hPc : IsMulCommutative P) (hAP : A ≤ P) (hA3 : Nat.card A = f ^ 3)
    (hA1 : ∀ y ∈ A, y ^ f = 1) (hA2 : ∀ y ∈ P, y ^ f = 1 → y ∈ A) :
    ∃ y ∈ normalizer (P : Set Y), ∀ n : ℕ, ∃ a ∈ A, y ^ (2 ^ n) * a ≠ a * y ^ (2 ^ n) := by
  have hinf : P ⊓ φ.ker = ⊥ := lift62x_inf_ker_eq_bot φ hP hker
  obtain ⟨hPmap, hPmapi⟩ := lift62x_sylow_map φ hφ hP hPi
  have hinj : ∀ x ∈ P, ∀ y ∈ P, φ x = φ y → x = y := by
    intro x hx y hy hxy
    have h : x⁻¹ * y ∈ P ⊓ φ.ker :=
      Subgroup.mem_inf.mpr ⟨P.mul_mem (P.inv_mem hx) hy,
        MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy, inv_mul_cancel])⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h
    exact h
  have hcard : Nat.card (A.map φ) = f ^ 3 := by
    rw [← hA3]
    exact Nat.card_image_of_injOn (fun x hx y hy hxy => hinj x (hAP hx) y (hAP hy) hxy)
  have hA1' : ∀ y ∈ A.map φ, y ^ f = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA1 a ha, map_one]
  have hA2' : ∀ y ∈ P.map φ, y ^ f = 1 → y ∈ A.map φ := by
    rintro _ ⟨u, hu, rfl⟩ hyf
    have huf : u ^ f ∈ P ⊓ φ.ker :=
      Subgroup.mem_inf.mpr ⟨P.pow_mem hu f, MonoidHom.mem_ker.mpr (by rw [map_pow]; exact hyf)⟩
    rw [hinf, Subgroup.mem_bot] at huf
    exact Subgroup.mem_map_of_mem φ (hA2 u hu huf)
  obtain ⟨g, hg, hgn⟩ := hK Z hZ hq f hf hf2 (P.map φ) (A.map φ) hPmap hPmapi inferInstance
    (Subgroup.map_mono hAP) hcard hA1' hA2'
  obtain ⟨y, hy, rfl⟩ := lift62x_exists_mem_normalizer φ hφ hf hP hPi hg
  refine ⟨y, hy, fun n => ?_⟩
  obtain ⟨b, hb, hbne⟩ := hgn n
  obtain ⟨a, ha, rfl⟩ := hb
  refine ⟨a, ha, fun h => hbne ?_⟩
  simpa [map_mul, map_pow] using congrArg φ h

open scoped IsMulCommutative in
private theorem lift62x_pow_index_eq_one {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤)
    {Q : Subgroup K} (hQc : IsMulCommutative Q) {z : K} (hz : z ∈ center K) :
    z ^ Q.index = 1 := by
  have key : ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * z ^ k * g₀ ∈ Q → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have h : g₀ * z ^ k = z ^ k * g₀ :=
      (Subgroup.mem_center_iff.mp ((center K).pow_mem hz k) g₀)
    rw [mul_assoc, ← h, inv_mul_cancel_left]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id Q) z key
  have h2 : MonoidHom.transfer (MonoidHom.id Q) z = 1 := by
    have hker := Abelianization.commutator_subset_ker (MonoidHom.transfer (MonoidHom.id Q))
    rw [hK] at hker
    exact MonoidHom.mem_ker.mp (hker (Subgroup.mem_top z))
  rw [h2] at h1
  exact congrArg Subtype.val h1.symm

theorem lift62x_center_eq_one {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤) {f : ℕ}
    (hf : f.Prime) {Q : Subgroup K} (hQ : IsPGroup f Q) (hQi : ¬ f ∣ Q.index)
    (hQc : IsMulCommutative Q) {z : K} (hz : z ∈ center K) (hzf : z ^ f = 1) : z = 1 := by
  have _ := hQ
  have h1 := lift62x_pow_index_eq_one hK hQc hz
  have h2 : orderOf z ∣ f := orderOf_dvd_of_pow_eq_one hzf
  have h3 : orderOf z ∣ Q.index := orderOf_dvd_of_pow_eq_one h1
  have h4 : Nat.Coprime f Q.index := (Nat.Prime.coprime_iff_not_dvd hf).2 hQi
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h4 h2 h3)

end CFSG.LocalAnalysis.RankThreeTheoremC
