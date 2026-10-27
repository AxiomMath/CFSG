module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiPartitionBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis SzPartition

variable {G : Type*} [Group G]

open Classical in
@[expose] noncomputable def szUT {K : Type*} (T₁ : Subgroup G) (t : G) (u : G → K) (w : G) : K :=
  if w ∈ T₁ then u w else u (w * t)

section SzUT

variable {K : Type*} {T₁ : Subgroup G} {t : G} {u : G → K}

theorem szUT_of_mem {y : G} (hy : y ∈ T₁) : szUT T₁ t u y = u y := by
  rw [szUT, ite_eq_left hy]

theorem szUT_mul_t (ht2 : t ^ 2 = 1) (htT : t ∉ T₁) {y : G} (hy : y ∈ T₁) :
    szUT T₁ t u (y * t) = u y := by
  have hyt : y * t ∉ T₁ := fun h => htT (by
    have := mul_mem (inv_mem hy) h
    rwa [inv_mul_cancel_left] at this)
  rw [szUT, ite_eq_right hyt, mul_assoc, ← sq, ht2, mul_one]

theorem szUT_eq (ht2 : t ^ 2 = 1) (htT : t ∉ T₁) {y z : G} (hy : y ∈ T₁) (hz : z ∈ zpowers t) :
    szUT T₁ t u (y * z) = u y := by
  rcases mem_zpowers_involution_eq_one_or_eq ht2 hz with rfl | rfl
  · rw [mul_one, szUT_of_mem hy]
  · exact szUT_mul_t ht2 htT hy

theorem mem_szA₁_of_mem_sup_zpowers (ht : t ∈ centralizer (T₁ : Set G)) (ht2 : t ^ 2 = 1)
    (htT : t ∉ T₁) {x : G} (hx : x ∈ T₁) (hxA : x ∈ szA₁ T₁ ⊔ zpowers t) : x ∈ szA₁ T₁ := by
  have htA : t ∈ centralizer (szA₁ T₁ : Set G) := centralizer_le (szA₁_le T₁) ht
  obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers htA hxA
  rcases mem_zpowers_involution_eq_one_or_eq ht2 hz with rfl | rfl
  · rwa [mul_one]
  · exfalso
    apply htT
    have := mul_mem (inv_mem (szA₁_le T₁ hb)) hx
    rwa [inv_mul_cancel_left] at this

variable [Field K] {a : ℕ} {d : G} {v : G → K} {κ : K}

theorem SzRootCoords.szUT_mul (hc : SzRootCoords T₁ a d u v κ) (ht : t ∈ centralizer (T₁ : Set G))
    (ht2 : t ^ 2 = 1) (htT : t ∉ T₁) {w w' : G} (hw : w ∈ T₁ ⊔ zpowers t)
    (hw' : w' ∈ T₁ ⊔ zpowers t) :
    szUT T₁ t u (w * w') = szUT T₁ t u w + szUT T₁ t u w' := by
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers ht hw
  obtain ⟨y', hy', z', hz', rfl⟩ := exists_mul_eq_of_mem_sup_zpowers ht hw'
  have hzy : y' * z = z * y' := commute_of_mem_zpowers hz (mem_centralizer_iff.mp ht y' hy')
  have e : y * z * (y' * z') = y * y' * (z * z') := by
    calc y * z * (y' * z') = y * (z * y') * z' := by group
      _ = y * (y' * z) * z' := by rw [hzy]
      _ = y * y' * (z * z') := by group
  rw [e, szUT_eq ht2 htT (mul_mem hy hy') (mul_mem hz hz'), szUT_eq ht2 htT hy hz,
    szUT_eq ht2 htT hy' hz', (hc.mul y hy y' hy').1]

variable [Fintype K]

theorem SzRootCoords.szUT_eq_zero_of_mem (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (ht : t ∈ centralizer (T₁ : Set G)) (ht2 : t ^ 2 = 1)
    (htT : t ∉ T₁) {w : G} (hw : w ∈ szA₁ T₁ ⊔ zpowers t) : szUT T₁ t u w = 0 := by
  have htA : t ∈ centralizer (szA₁ T₁ : Set G) := centralizer_le (szA₁_le T₁) ht
  obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers htA hw
  rw [szUT_eq ht2 htT (szA₁_le T₁ hb) hz, hc.u_eq_zero_of_mem_szA₁ ha hK hb]

theorem SzRootCoords.mem_of_szUT_eq_zero (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (ht : t ∈ centralizer (T₁ : Set G)) (ht2 : t ^ 2 = 1)
    (htT : t ∉ T₁) {w : G} (hw : w ∈ T₁ ⊔ zpowers t) (h0 : szUT T₁ t u w = 0) :
    w ∈ szA₁ T₁ ⊔ zpowers t := by
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers ht hw
  rw [szUT_eq ht2 htT hy hz] at h0
  exact mul_mem_sup ((hc.mem_szA₁_iff ha hK hy).mpr h0) hz

theorem SzRootCoords.sq_mem_and_v_sq [CharP K 2] (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (ht : t ∈ centralizer (T₁ : Set G)) (ht2 : t ^ 2 = 1)
    (htT : t ∉ T₁) {w : G} (hw : w ∈ T₁ ⊔ zpowers t) :
    w ^ 2 ∈ szA₁ T₁ ∧ v (w ^ 2) = szUT T₁ t u w ^ (2 ^ (a + 1) + 1) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers ht hw
  have hyz : Commute y z := commute_of_mem_zpowers hz (mem_centralizer_iff.mp ht y hy)
  have hz2 : z ^ 2 = 1 := by
    rcases mem_zpowers_involution_eq_one_or_eq ht2 hz with rfl | rfl
    · exact one_pow 2
    · exact ht2
  rw [hyz.mul_pow, hz2, mul_one, szUT_eq ht2 htT hy hz]
  exact ⟨hc.sq_mem_szA₁ ha hK hy, (hc.sq hy).2⟩

theorem SzRootCoords.exists_addAut_conj [CharP K 2] (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) (ht : t ∈ centralizer (T₁ : Set G))
    (ht2 : t ^ 2 = 1) (htT : t ∉ T₁) {n : G}
    (hnT : n ∈ normalizer ((T₁ ⊔ zpowers t : Subgroup G) : Set G))
    (hnA : n ∈ normalizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ φ : AddAut K, ∀ x ∈ T₁, szUT T₁ t u (n * x * n⁻¹) = φ (u x) := by
  choose x hx using fun α : K => hc.surj α 0
  have hTA : szA₁ T₁ ⊔ zpowers t ≤ T₁ ⊔ zpowers t := sup_le_sup_right (szA₁_le T₁) _
  have hconjT : ∀ y ∈ T₁ ⊔ zpowers t, n * y * n⁻¹ ∈ T₁ ⊔ zpowers t := fun y hy =>
    (mem_normalizer_iff.mp hnT y).mp hy
  set F : K → K := fun α => szUT T₁ t u (n * x α * n⁻¹)
  have hFu : ∀ y ∈ T₁, szUT T₁ t u (n * y * n⁻¹) = F (u y) := by
    intro y hy
    obtain ⟨hxT, hxu, -⟩ := hx (u y)
    have hb : (x (u y))⁻¹ * y ∈ szA₁ T₁ := hc.inv_mul_mem_szA₁_of_u_eq ha hK hxT hy hxu
    have e : n * y * n⁻¹ = (n * x (u y) * n⁻¹) * (n * ((x (u y))⁻¹ * y) * n⁻¹) := by group
    have hbA : n * ((x (u y))⁻¹ * y) * n⁻¹ ∈ szA₁ T₁ ⊔ zpowers t :=
      (mem_normalizer_iff.mp hnA _).mp (mem_sup_left hb)
    rw [e, hc.szUT_mul ht ht2 htT (hconjT _ (mem_sup_left hxT)) (hTA hbA),
      hc.szUT_eq_zero_of_mem ha hK ht ht2 htT hbA, add_zero]
  have hadd : ∀ α β : K, F (α + β) = F α + F β := by
    intro α β
    obtain ⟨hαT, hαu, -⟩ := hx α
    obtain ⟨hβT, hβu, -⟩ := hx β
    have h1 := hFu _ (mul_mem hαT hβT)
    rw [(hc.mul _ hαT _ hβT).1, hαu, hβu] at h1
    rw [← h1, show n * (x α * x β) * n⁻¹ = (n * x α * n⁻¹) * (n * x β * n⁻¹) by group,
      hc.szUT_mul ht ht2 htT (hconjT _ (mem_sup_left hαT)) (hconjT _ (mem_sup_left hβT))]
  let F' : K →+ K := AddMonoidHom.mk' F hadd
  have hinj : Function.Injective F' := by
    refine (injective_iff_map_eq_zero F').mpr fun α hα => ?_
    obtain ⟨hαT, hαu, -⟩ := hx α
    have h1 : n * x α * n⁻¹ ∈ szA₁ T₁ ⊔ zpowers t :=
      hc.mem_of_szUT_eq_zero ha hK ht ht2 htT (hconjT _ (mem_sup_left hαT)) hα
    have h2 : x α ∈ szA₁ T₁ ⊔ zpowers t := by
      have h3 := (mem_normalizer_iff''.mp hnA _).mp h1
      rwa [show n⁻¹ * (n * x α * n⁻¹) * n = x α by group] at h3
    rw [← hαu]
    exact hc.u_eq_zero_of_mem_szA₁ ha hK (mem_szA₁_of_mem_sup_zpowers ht ht2 htT hαT h2)
  refine ⟨AddEquiv.ofBijective F' (Finite.injective_iff_bijective.mp hinj), fun y hy => ?_⟩
  rw [hFu y hy]
  rfl

end SzUT

namespace SzPartitionData

variable {A₁ : Subgroup G} {t : G}

theorem exists_equiv (hD : SzPartitionData A₁ t) {K : Type*} {v : G → K}
    (hv_inj : ∀ b ∈ A₁, ∀ b' ∈ A₁, v b = v b' → b = b') (hv_surj : ∀ β : K, ∃ b ∈ A₁, v b = β) :
    ∃ e : gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t) ≃ K,
      ∀ b (hb : b ∈ A₁), e ⟨zpowers (b * t), hD.mem_iff.mpr ⟨b, hb, rfl⟩⟩ = v b := by
  let ι : A₁ → gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t) := fun b =>
    ⟨zpowers (b * t), hD.mem_iff.mpr ⟨b, b.2, rfl⟩⟩
  have hι : Function.Bijective ι := by
    refine ⟨fun b b' hbb => Subtype.ext
      (hD.eq_of_zpowers_eq b.2 b'.2 (congrArg Subtype.val hbb)), fun Q => ?_⟩
    obtain ⟨b, hb, hQ⟩ := hD.mem_iff.mp Q.2
    exact ⟨⟨b, hb⟩, Subtype.ext hQ.symm⟩
  let w : A₁ → K := fun b => v b
  have hw : Function.Bijective w := by
    refine ⟨fun b b' hbb => Subtype.ext (hv_inj b b.2 b' b'.2 hbb), fun β => ?_⟩
    obtain ⟨b, hb, rfl⟩ := hv_surj β
    exact ⟨⟨b, hb⟩, rfl⟩
  refine ⟨(Equiv.ofBijective ι hι).symm.trans (Equiv.ofBijective w hw), fun b hb => ?_⟩
  have e : (⟨zpowers (b * t), hD.mem_iff.mpr ⟨b, hb, rfl⟩⟩ :
      gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t)) = ι ⟨b, hb⟩ := rfl
  rw [Equiv.trans_apply, e, Equiv.ofBijective_symm_apply_apply]
  rfl

theorem permCongr_action_apply (hD : SzPartitionData A₁ t) {K : Type*} {v : G → K}
    {e : gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t) ≃ K}
    (he : ∀ b (hb : b ∈ A₁), e ⟨zpowers (b * t), hD.mem_iff.mpr ⟨b, hb, rfl⟩⟩ = v b)
    (n : normalizer ((A₁ ⊔ zpowers t : Subgroup G) : Set G)) {c : G} (hc : c ∈ A₁)
    (hnc : (n : G) * t * (n : G)⁻¹ = c * t) {b : G} (hb : b ∈ A₁) :
    e.permCongr (gmsRootConjugateAction (A₁ ⊔ zpowers t) (zpowers t) n) (v b) =
      v ((n : G) * b * (n : G)⁻¹ * c) := by
  have hb' : (n : G) * b * (n : G)⁻¹ * c ∈ A₁ :=
    mul_mem ((mem_normalizer_iff.mp (hD.normalizer_le n.2) b).mp hb) hc
  rw [Equiv.permCongr_apply, ← he b hb, Equiv.symm_apply_apply, ← he _ hb']
  congr 1
  apply Subtype.ext
  change (zpowers (b * t)).map (MulAut.conj (n : G)).toMonoidHom = _
  exact SzPartitionData.map_conj_zpowers_mul hnc b

end SzPartitionData

end CFSG.SeitzReduction.RankOne
