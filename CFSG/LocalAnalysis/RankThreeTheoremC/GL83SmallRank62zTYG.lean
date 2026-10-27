module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

theorem k631_quat_involution {k : ℕ} [NeZero k] (x : QuaternionGroup k) (hx : x ^ 2 = 1)
    (hx1 : x ≠ 1) : x = QuaternionGroup.a (k : ZMod (2 * k)) := by
  cases x with
  | a i =>
    have h2 : i + i = 0 := by
      have := hx
      rw [pow_two, QuaternionGroup.a_mul_a, ← QuaternionGroup.a_zero] at this
      exact QuaternionGroup.a.inj this
    have hm : (2 * k) ∣ (i.val + i.val) := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact h2
    have hlt : i.val < 2 * k := ZMod.val_lt i
    have hk : k ∣ i.val := by
      have : 2 * k ∣ 2 * i.val := by rwa [two_mul i.val]
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp this
    obtain ⟨c, hc⟩ := hk
    have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    have hc2 : c < 2 := by
      by_contra hcon
      push Not at hcon
      have : 2 * k ≤ k * c := by nlinarith
      omega
    interval_cases c
    · exfalso
      apply hx1
      have : i = 0 := by
        rw [← ZMod.natCast_zmod_val i, hc]
        simp
      rw [this]
      rfl
    · have : i = (k : ZMod (2 * k)) := by
        rw [← ZMod.natCast_zmod_val i, hc]
        simp
      rw [this]
  | xa i =>
    exfalso
    have h1 : QuaternionGroup.a (k : ZMod (2 * k)) = 1 := by
      rw [← QuaternionGroup.xa_sq i]; exact hx
    rw [← QuaternionGroup.a_zero] at h1
    have h2 : (k : ZMod (2 * k)) = 0 := QuaternionGroup.a.inj h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    have := Nat.le_of_dvd hkpos h2
    omega

variable {G : Type} [Group G]

theorem k631_mem_center_sup {S A B : Subgroup G} (hS : A ⊔ B = S) {y : G} (hyA : y ∈ A)
    (hyB : y ∈ B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : y ∈ smallRankCenter S := by
  have hyS : y ∈ S := hS ▸ Subgroup.mem_sup_left hyA
  have hle : A ⊔ B ≤ centralizer ({y} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hAB a ha y hyB
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact (hAB y hyA b hb).symm
  have hc : y ∈ centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have := hle (hS ▸ hs)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  exact ⟨hyS, hc⟩

theorem k631_mem_center_sup3 {S A B C : Subgroup G} (hS : A ⊔ B ⊔ C = S) {y : G} (hyA : y ∈ A)
    (hyB : y ∈ B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) : y ∈ smallRankCenter S := by
  have hyS : y ∈ S := hS ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_left hyA)
  have hle : A ⊔ B ⊔ C ≤ centralizer ({y} : Set G) := by
    refine sup_le (sup_le (fun a ha => ?_) (fun b hb => ?_)) (fun c hc => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hAB a ha y hyB
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact (hAB y hyA b hb).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact (hAC y hyA c hc).symm
  have hc : y ∈ centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have := hle (hS ▸ hs)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  exact ⟨hyS, hc⟩

theorem k631_exists_involution {A B : Subgroup G} [Finite G]
    (hcard : Nat.card (A ⊓ B : Subgroup G) = 2) :
    ∃ y ∈ A ⊓ B, y ≠ 1 ∧ y ^ 2 = 1 := by
  have hnt : Nontrivial ↥(A ⊓ B) := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.one_lt_iff_ne_zero_and_ne_one]
    omega
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥(A ⊓ B))
  refine ⟨x, x.2, fun h => hx1 (Subtype.ext h), ?_⟩
  have := pow_card_eq_one' (G := ↥(A ⊓ B)) (x := x)
  rw [hcard] at this
  exact congrArg Subtype.val this

theorem k631_tyg_quaternion [Finite G] {S : Subgroup G} {n : ℕ}
    (h : smallRankIsQ8Quaternion S n) :
    ∃ t y g : G, t ∈ S ∧ g ∈ S ∧ y ∈ smallRankCenter S ∧ t ^ 2 = 1 ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧
      t * y = y * t ∧ g * t * g⁻¹ = t * y := by
  obtain ⟨A, B, ⟨φ⟩, hn, ⟨ψ⟩, hAB, hS, hcard⟩ := h
  have hk : NeZero (2 ^ (n - 2)) := inferInstance
  obtain ⟨y, hyAB, hy1, hy2⟩ := k631_exists_involution hcard
  have hyA : y ∈ A := hyAB.1
  have hyB : y ∈ B := hyAB.2
  have hφy : φ ⟨y, hyA⟩ = QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) := by
    apply k631_quat_involution
    · rw [← map_pow]
      have : (⟨y, hyA⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hy2)
      rw [this, map_one]
    · intro h1
      apply hy1
      have := φ.injective (h1.trans (map_one φ).symm)
      exact congrArg Subtype.val this
  have hψy : ψ ⟨y, hyB⟩ = QuaternionGroup.a ((2 ^ (n - 2) : ℕ) : ZMod (2 * 2 ^ (n - 2))) := by
    apply k631_quat_involution
    · rw [← map_pow]
      have : (⟨y, hyB⟩ : ↥B) ^ 2 = 1 := Subtype.ext (by simpa using hy2)
      rw [this, map_one]
    · intro h1
      apply hy1
      have := ψ.injective (h1.trans (map_one ψ).symm)
      exact congrArg Subtype.val this
  set a₀ : ↥A := φ.symm (QuaternionGroup.xa 0) with ha₀
  set b₀ : ↥B := ψ.symm (QuaternionGroup.xa 0) with hb₀
  set g₀ : ↥A := φ.symm (QuaternionGroup.xa 1) with hg₀
  have ha2 : a₀ ^ 2 = ⟨y, hyA⟩ := by
    apply φ.injective
    rw [map_pow, ha₀, MulEquiv.apply_symm_apply, QuaternionGroup.xa_sq, hφy]
  have hb2 : b₀ ^ 2 = ⟨y, hyB⟩ := by
    apply ψ.injective
    rw [map_pow, hb₀, MulEquiv.apply_symm_apply, QuaternionGroup.xa_sq, hψy]
  have hq8 : (QuaternionGroup.xa 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 *
      (QuaternionGroup.xa 1)⁻¹ = (QuaternionGroup.xa 0)⁻¹ := by decide
  have hga : g₀ * a₀ * g₀⁻¹ = a₀⁻¹ := by
    apply φ.injective
    simp only [map_mul, map_inv, ha₀, hg₀, MulEquiv.apply_symm_apply]
    exact hq8
  have haG : (a₀ : G) ^ 2 = y := by
    have := congrArg Subtype.val ha2
    simpa using this
  have hbG : (b₀ : G) ^ 2 = y := by
    have := congrArg Subtype.val hb2
    simpa using this
  have hgaG : (g₀ : G) * (a₀ : G) * (g₀ : G)⁻¹ = (a₀ : G)⁻¹ := by
    have := congrArg Subtype.val hga
    simpa using this
  have hab : (a₀ : G) * (b₀ : G) = (b₀ : G) * (a₀ : G) := hAB _ a₀.2 _ b₀.2
  have hgb : (g₀ : G) * (b₀ : G) = (b₀ : G) * (g₀ : G) := hAB _ g₀.2 _ b₀.2
  have hya : (a₀ : G) * y = y * (a₀ : G) := hAB _ a₀.2 _ hyB
  have hyb : y * (b₀ : G) = (b₀ : G) * y := hAB _ hyA _ b₀.2
  have hinv : (a₀ : G)⁻¹ = (a₀ : G) * y := by
    have h4 : (a₀ : G) ^ 4 = 1 := by
      have : (a₀ : G) ^ 4 = ((a₀ : G) ^ 2) ^ 2 := by rw [← pow_mul]
      rw [this, haG, hy2]
    have : (a₀ : G) * y = (a₀ : G) ^ 3 := by rw [← haG]; group
    rw [this]
    have : (a₀ : G) ^ 3 * (a₀ : G) = 1 := by rw [← h4]; group
    exact (eq_inv_of_mul_eq_one_left this).symm
  refine ⟨(a₀ : G) * (b₀ : G), y, (g₀ : G), mul_mem (hS ▸ Subgroup.mem_sup_left a₀.2)
    (hS ▸ Subgroup.mem_sup_right b₀.2), hS ▸ Subgroup.mem_sup_left g₀.2,
    k631_mem_center_sup hS hyA hyB hAB, ?_, hy2, hy1, ?_, ?_⟩
  · calc ((a₀ : G) * (b₀ : G)) ^ 2 = (a₀ : G) ^ 2 * (b₀ : G) ^ 2 := by
          rw [pow_two, pow_two, pow_two]
          calc (a₀ : G) * (b₀ : G) * ((a₀ : G) * (b₀ : G))
              = (a₀ : G) * ((b₀ : G) * (a₀ : G)) * (b₀ : G) := by group
            _ = (a₀ : G) * ((a₀ : G) * (b₀ : G)) * (b₀ : G) := by rw [hab]
            _ = (a₀ : G) * (a₀ : G) * ((b₀ : G) * (b₀ : G)) := by group
      _ = 1 := by rw [haG, hbG, ← pow_two, hy2]
  · calc (a₀ : G) * (b₀ : G) * y = (a₀ : G) * ((b₀ : G) * y) := by group
      _ = (a₀ : G) * (y * (b₀ : G)) := by rw [hyb]
      _ = ((a₀ : G) * y) * (b₀ : G) := by group
      _ = (y * (a₀ : G)) * (b₀ : G) := by rw [hya]
      _ = y * ((a₀ : G) * (b₀ : G)) := by group
  · calc (g₀ : G) * ((a₀ : G) * (b₀ : G)) * (g₀ : G)⁻¹
        = ((g₀ : G) * (a₀ : G) * (g₀ : G)⁻¹) * ((g₀ : G) * (b₀ : G) * (g₀ : G)⁻¹) := by group
      _ = (a₀ : G)⁻¹ * (b₀ : G) := by
          rw [hgaG, hgb]; group
      _ = (a₀ : G) * y * (b₀ : G) := by rw [hinv]
      _ = (a₀ : G) * (y * (b₀ : G)) := by group
      _ = (a₀ : G) * ((b₀ : G) * y) := by rw [hyb]
      _ = (a₀ : G) * (b₀ : G) * y := by group

theorem k631_tyg_dihedral [Finite G] {S : Subgroup G} {n : ℕ}
    (h : smallRankIsQ8D8CentralCyclic S n) :
    ∃ t y g : G, t ∈ S ∧ g ∈ S ∧ y ∈ smallRankCenter S ∧ t ^ 2 = 1 ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧
      t * y = y * t ∧ g * t * g⁻¹ = t * y := by
  obtain ⟨A, B, C, ⟨φ⟩, ⟨ψ⟩, hC, hCcard, hAB, hAC, hBC, hAB2, hABC2, hS⟩ := h
  obtain ⟨y, hyAB, hy1, hy2⟩ := k631_exists_involution hAB2
  have hyA : y ∈ A := hyAB.1
  have hyB : y ∈ B := hyAB.2
  have hcenter : ∀ x : DihedralGroup 4, (∀ z, x * z = z * x) → x = 1 ∨ x = DihedralGroup.r 2 := by
    decide
  have hψy : ψ ⟨y, hyB⟩ = DihedralGroup.r 2 := by
    rcases hcenter (ψ ⟨y, hyB⟩) (fun z => by
      obtain ⟨b, rfl⟩ := ψ.surjective z
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAB y hyA b.1 b.2)) with h1 | h1
    · exfalso
      apply hy1
      have := ψ.injective (h1.trans (map_one ψ).symm)
      exact congrArg Subtype.val this
    · exact h1
  set t₀ : ↥B := ψ.symm (DihedralGroup.sr 0) with ht₀
  set g₀ : ↥B := ψ.symm (DihedralGroup.r 1) with hg₀
  have hd : (DihedralGroup.r 1 : DihedralGroup 4) * DihedralGroup.sr 0 * (DihedralGroup.r 1)⁻¹ =
      DihedralGroup.sr 0 * DihedralGroup.r 2 := by decide
  have ht2 : (DihedralGroup.sr 0 : DihedralGroup 4) ^ 2 = 1 := by decide
  have hyd : (⟨y, hyB⟩ : ↥B) = ψ.symm (DihedralGroup.r 2) := by
    rw [← hψy, MulEquiv.symm_apply_apply]
  have hgt : g₀ * t₀ * g₀⁻¹ = t₀ * ⟨y, hyB⟩ := by
    apply ψ.injective
    simp only [map_mul, map_inv, ht₀, hg₀, hyd, MulEquiv.apply_symm_apply]
    exact hd
  have ht0sq : t₀ ^ 2 = 1 := by
    apply ψ.injective
    rw [map_pow, ht₀, MulEquiv.apply_symm_apply, ht2, map_one]
  have hty : t₀ * ⟨y, hyB⟩ = ⟨y, hyB⟩ * t₀ := by
    apply Subtype.ext
    exact (hAB y hyA t₀.1 t₀.2).symm
  have hBS : B ≤ S := hS ▸ le_trans le_sup_right le_sup_left
  refine ⟨(t₀ : G), y, (g₀ : G), hBS t₀.2, hBS g₀.2, k631_mem_center_sup3 hS hyA hyB hAB hAC,
    ?_, hy2, hy1, ?_, ?_⟩
  · have := congrArg Subtype.val ht0sq
    simpa using this
  · have := congrArg Subtype.val hty
    simpa using this
  · have := congrArg Subtype.val hgt
    simpa using this

end CFSG.LocalAnalysis.RankThreeTheoremC
