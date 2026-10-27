module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeUnique

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

namespace D1MSideAt

theorem mem_barM_of_fusion {M S R : Subgroup G} (h : D1MSideAt M S) (hp : p.Prime)
    (hp2 : p ≠ 2) {z : G} (hzR : z ∈ R) (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z))
    (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (S : Set G))
    (hNR : Subgroup.normalizer (R : Set G) ≤ M) {L : Subgroup G}
    (hL : IsWeakSBlock M S L)
    (hzL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ barM M L) {T : Subgroup G}
    (hRz : ∀ r ∈ R, z * r = r * z) (hexp : ∀ r ∈ R, r ^ 3 = 1)
    (hfus : ∀ r ∈ R, r ∉ T → r ∈ fusionSet R z) {w : G} (hwR : w ∈ R) (hwT : w ∉ T)
    (hwM : w ∈ M) : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hwM⟩ ∈ barM M L := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set zb := mk ⟨z, hzM⟩ with hzb
  have hzC := h.not_mem_centralizer_block hp hp2 hzM hz hCz hL
  obtain ⟨-, m, hmN, hwm⟩ := hfus w hwR hwT
  have hmM : m ∈ M := hNR hmN
  set w₁ := m * z * m⁻¹ with hw₁
  have hw₁R : w₁ ∈ R := (Subgroup.mem_normalizer_iff.mp hmN z).mp hzR
  have hw₁M : w₁ ∈ M := M.mul_mem (M.mul_mem hmM hzM) (M.inv_mem hmM)
  have hw₁T : w₁ ∉ T := fun h1 => hwT ((Subgroup.zpowers_le.mpr h1) hwm)
  set mb := mk ⟨m, hmM⟩ with hmb
  have hw₁b : mk ⟨w₁, hw₁M⟩ = mb * zb * mb⁻¹ := by
    rw [hmb, hzb, ← map_inv, ← map_mul, ← map_mul]; rfl
  set B := barM M (L.map (MulAut.conj m).toMonoidHom) with hB
  have hBeq : B = (barM M L).map (MulAut.conj mb).toMonoidHom := barM_map_conj hmM L
  have hBc : IsComponentOf B ⊤ := (hL.toIsTwoPrimeComponent.map_conj hmM).component
  have hw₁B : mk ⟨w₁, hw₁M⟩ ∈ B := by rw [hBeq, hw₁b]; exact ⟨zb, hzL, rfl⟩
  have hw₁C : mk ⟨w₁, hw₁M⟩ ∉ Subgroup.centralizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro hc
    apply hzC
    rw [hBeq, hw₁b] at hc
    exact mem_centralizer_of_conj_mem_map hc
  have hBL : B = barM M L := by
    by_contra hne
    have hw₁L : mk ⟨w₁, hw₁M⟩ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      le_centralizer_of_component_ne hBc hL.component hne hw₁B
    obtain ⟨j, hj, huT⟩ : ∃ j : ℕ, (j = 1 ∨ j = 2) ∧ z * w₁ ^ j ∉ T := by
      by_cases h1 : z * w₁ ^ 1 ∈ T
      · refine ⟨2, Or.inr rfl, fun h2 => hw₁T ?_⟩
        have := T.mul_mem h2 (T.inv_mem h1)
        have e : z * w₁ ^ 2 * (z * w₁ ^ 1)⁻¹ = w₁ := by
          have hc : z * w₁ = w₁ * z := hRz w₁ hw₁R
          calc z * w₁ ^ 2 * (z * w₁ ^ 1)⁻¹ = z * w₁ * w₁ * w₁⁻¹ * z⁻¹ := by group
            _ = w₁ * z * z⁻¹ := by rw [hc]; group
            _ = w₁ := by group
        rwa [e] at this
      · exact ⟨1, Or.inl rfl, h1⟩
    have huR : z * w₁ ^ j ∈ R := R.mul_mem hzR (R.pow_mem hw₁R j)
    have huM : z * w₁ ^ j ∈ M := M.mul_mem hzM (M.pow_mem hw₁M j)
    obtain ⟨-, m', hm'N, hum'⟩ := hfus _ huR huT
    have hm'M : m' ∈ M := hNR hm'N
    set A := barM M (L.map (MulAut.conj m').toMonoidHom) with hA
    have hAc : IsComponentOf A ⊤ := (hL.toIsTwoPrimeComponent.map_conj hm'M).component
    have hz'A : mk ⟨m' * z * m'⁻¹, M.mul_mem (M.mul_mem hm'M hzM) (M.inv_mem hm'M)⟩ ∈ A := by
      rw [hA, barM_map_conj hm'M L]
      refine ⟨zb, hzL, ?_⟩
      rw [hzb, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have huA : mk ⟨z * w₁ ^ j, huM⟩ ∈ A := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hum'
      have : (⟨z * w₁ ^ j, huM⟩ : M) =
          (⟨m' * z * m'⁻¹, M.mul_mem (M.mul_mem hm'M hzM) (M.inv_mem hm'M)⟩ : M) ^ k :=
        Subtype.ext (by simpa using hk.symm)
      rw [this, map_zpow]
      exact Subgroup.zpow_mem _ hz'A k
    have hub : mk ⟨z * w₁ ^ j, huM⟩ = zb * (mk ⟨w₁, hw₁M⟩) ^ j := by
      rw [hzb, ← map_pow, ← map_mul]; rfl
    by_cases hAL : A = barM M L
    ·
      rw [hAL] at huA
      have hwjL : (mk ⟨w₁, hw₁M⟩) ^ j ∈ barM M L := by
        have := (barM M L).mul_mem ((barM M L).inv_mem hzL) huA
        rwa [hub, inv_mul_cancel_left] at this
      have hwjC : (mk ⟨w₁, hw₁M⟩) ^ j ∈
          Subgroup.centralizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        le_centralizer_of_component_ne hL.component hBc (Ne.symm hne) hwjL
      apply hw₁C
      have hw3 : (mk ⟨w₁, hw₁M⟩) ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨w₁, hw₁M⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hexp w₁ hw₁R)
        rw [this, map_one]
      rcases hj with rfl | rfl
      · simpa using hwjC
      · have e : mk ⟨w₁, hw₁M⟩ = ((mk ⟨w₁, hw₁M⟩) ^ 2) ^ 2 := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hw3, one_mul, pow_one]
        rw [e]
        exact Subgroup.pow_mem _ hwjC 2
    ·
      have huC : mk ⟨z * w₁ ^ j, huM⟩ ∈
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        le_centralizer_of_component_ne hAc hL.component hAL huA
      apply hzC
      have := Subgroup.mul_mem _ huC (Subgroup.inv_mem _ (Subgroup.pow_mem _ hw₁L j))
      rwa [hub, mul_inv_cancel_right] at this
  rw [hBL] at hw₁B
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwm
  have : (⟨w, hwM⟩ : M) = (⟨w₁, hw₁M⟩ : M) ^ k := Subtype.ext (by simpa using hk.symm)
  rw [this, map_zpow]
  exact Subgroup.zpow_mem _ hw₁B k

theorem barM_le_of_fusion {M S R : Subgroup G} (h : D1MSideAt M S) (hp : p.Prime)
    (hp2 : p ≠ 2) {z : G} (hzR : z ∈ R) (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z))
    (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (S : Set G))
    (hNR : Subgroup.normalizer (R : Set G) ≤ M) {L : Subgroup G}
    (hL : IsWeakSBlock M S L)
    (hzL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ barM M L) {T : Subgroup G}
    (hzT : z ∉ T) (hRz : ∀ r ∈ R, z * r = r * z) (hexp : ∀ r ∈ R, r ^ 3 = 1)
    (hfus : ∀ r ∈ R, r ∉ T → r ∈ fusionSet R z) : barM M R ≤ barM M L := by
  rintro _ ⟨⟨r, hrM⟩, hr, rfl⟩
  have hrR : r ∈ R := Subgroup.mem_subgroupOf.mp hr
  by_cases hrT : r ∈ T
  · have hzrT : z * r ∉ T := fun h1 => hzT (by simpa using T.mul_mem h1 (T.inv_mem hrT))
    have h1 := h.mem_barM_of_fusion hp hp2 hzR hzM hz hCz hNR hL hzL hRz hexp hfus
      (R.mul_mem hzR hrR) hzrT (M.mul_mem hzM hrM)
    have h2 := (barM M L).mul_mem ((barM M L).inv_mem hzL) h1
    have e : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z * r, M.mul_mem hzM hrM⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hrM⟩ := by
      rw [← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext (by simp)
    rwa [e] at h2
  · exact h.mem_barM_of_fusion hp hp2 hzR hzM hz hCz hNR hL hzL hRz hexp hfus hrR hrT hrM

end D1MSideAt

end CFSG.AGLEmbedding
