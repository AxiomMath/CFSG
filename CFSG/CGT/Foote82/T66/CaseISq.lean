module

public import CFSG.CGT.Foote82.T66.CaseITheta
public import CFSG.CGT.Foote82.T66.CaseISyl

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

theorem Hyp.z_mem_G (h : Hyp G L z v H₁ m ψ) : z ∈ G :=
  h.setup6.S_le (Subgroup.mem_zpowers z)

theorem Hyp.z_comm_L (h : Hyp G L z v H₁ m ψ) {l : GLV V} (hl : l ∈ L) : l * z = z * l :=
  (Subgroup.mem_centralizer_iff.1 (h.setup6.component.1 hl).2 z (Subgroup.mem_zpowers z)).symm

theorem Hyp.z_mem_K (h : Hyp G L z v H₁ m ψ) : z ∈ KK G L :=
  ⟨h.z_mem_G, Subgroup.mem_centralizer_iff.2 fun l hl => h.z_comm_L hl⟩

theorem Hyp.K_le_N (h : Hyp G L z v H₁ m ψ) : KK G L ≤ NN G L := fun x hx =>
  ⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩

theorem Hyp.z_mem_N (h : Hyp G L z v H₁ m ψ) : z ∈ NN G L := h.K_le_N h.z_mem_K

theorem Hyp.centralizer_z_le (h : Hyp G L z v H₁ m ψ) {x : GLV V} (hxG : x ∈ G)
    (hxz : x * z = z * x) : x ∈ NN G L := by
  by_contra hx
  have hxN : x ∉ Subgroup.normalizer (L : Set (GLV V)) := fun h' => hx ⟨hxG, h'⟩
  have hodd := h.std.tight x hxG hxN
  have hzmem : z ∈ KK G L ⊓ (KK G L).map (MulAut.conj x).toMonoidHom :=
    ⟨h.z_mem_K, ⟨z, h.z_mem_K, by
      show x * z * x⁻¹ = z
      rw [hxz, mul_inv_cancel_right]⟩⟩
  have hord : orderOf (⟨z, hzmem⟩ : ↥(KK G L ⊓ (KK G L).map (MulAut.conj x).toMonoidHom)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact h.std.orderOf_s
  have h2 := orderOf_dvd_natCard (⟨z, hzmem⟩ : ↥(KK G L ⊓ (KK G L).map (MulAut.conj x).toMonoidHom))
  rw [hord] at h2
  exact (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hodd)) h2

theorem Hyp.pe_iota2_mem_N (h : Hyp G L z v H₁ m ψ) (σ : Perm (Fin (m + 6))) :
    pe ψ (iota2 (m + 6) σ) ∈ NN G L := by
  refine ⟨h.H₁_le_G (pe_mem _), Subgroup.mem_normalizer_iff.2 fun l => ?_⟩
  have hconj : ∀ (τ : Perm (Fin (m + 6))) (a : alternatingGroup (Fin (m + 6))),
      pe ψ (iota2 (m + 6) τ) * jL ψ a * (pe ψ (iota2 (m + 6) τ))⁻¹ =
        jL ψ (CaseIAut.conjA τ a) := by
    intro τ a
    rw [jL_apply, jL_apply, CaseIAut.coe_conjA, ← map_inv, ← map_mul, ← map_mul, ← map_inv,
      ← map_mul, ← map_mul]
  rw [← h.range_jL]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, (hconj σ a).symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨CaseIAut.conjA σ⁻¹ b, ?_⟩
    have := hconj σ⁻¹ b
    rw [hb, map_inv, map_inv, inv_inv] at this
    rw [← this]
    group

theorem eq_sq_of_mem_zpowers {Γ : Type*} [Group Γ] {w x : Γ} (hw : orderOf w = 4)
    (hx : x ∈ Subgroup.zpowers w) (hx2 : orderOf x = 2) : x = w * w := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h4 : (orderOf w : ℤ) = 4 := by rw [hw]; rfl
  have hred : w ^ i = w ^ (i % 4) := by rw [← h4, zpow_mod_orderOf]
  have hlt : 0 ≤ i % 4 ∧ i % 4 < 4 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  rw [hred] at hx2 ⊢
  have hcases : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases hcases with h0 | h0 | h0 | h0 <;> rw [h0] at hx2 ⊢
  · simp at hx2
  · rw [zpow_one] at hx2; rw [hw] at hx2; exact absurd hx2 (by norm_num)
  · rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, sq]
  · have : orderOf (w ^ (3 : ℤ)) = 4 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, orderOf_pow' w (by norm_num), hw]
      rfl
    rw [this] at hx2; exact absurd hx2 (by norm_num)

theorem Hyp.not_sq (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    {w : GLV V} (hwG : w ∈ G) (hw : w * w = z) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := h.std.orderOf_s
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have hwz : w * z = z * w := by rw [← hw]; group
  have hwN : w ∈ NN G L := h.centralizer_z_le hwG hwz
  have hw4 : orderOf w = 4 := by
    have h1 : w ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq w, hw, sq, h.zz]
    have h2 : w ^ 2 ≠ 1 := by rw [sq, hw]; exact hz1
    have hdvd : orderOf w ∣ 4 := orderOf_dvd_of_pow_eq_one h1
    have hnd : ¬ orderOf w ∣ 2 := fun hd => h2 (orderOf_dvd_iff_pow_eq_one.1 hd)
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf w ∣ 2 ^ 2 from hdvd)
    interval_cases j
    · exact absurd (by rw [hj']; norm_num) hnd
    · exact absurd (by rw [hj']; norm_num) hnd
    · simpa using hj'
  obtain ⟨θ, hθ, hθ1, hθ3⟩ := h.exists_thetaL
  set τ := θ ⟨w, hwN⟩ with hτ
  have hθz : θ ⟨z, h.z_mem_N⟩ = 1 :=
    (hθ1 _).2 fun a => (h.z_comm_L (h.jL_mem a)).symm
  have hττ : τ * τ = 1 := by
    rw [hτ, ← map_mul]
    have : (⟨w, hwN⟩ : ↥(NN G L)) * ⟨w, hwN⟩ = ⟨z, h.z_mem_N⟩ := Subtype.ext hw
    rw [this, hθz]
  set ℓ := pe ψ (iota2 (m + 6) τ) with hℓ
  have hℓN : ℓ ∈ NN G L := h.pe_iota2_mem_N τ
  have hθℓ : θ ⟨ℓ, hℓN⟩ = τ := hθ3 _ τ rfl
  have hcentral : ∀ x : ↥(NN G L), θ x = 1 → (x : GLV V) ∈ KK G L := by
    intro x hx
    refine ⟨x.2.1, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    rw [← h.range_jL] at hl
    obtain ⟨a, rfl⟩ := hl
    exact ((hθ1 x).1 hx a).symm
  have hk : ℓ⁻¹ * w ∈ KK G L := by
    have := hcentral (⟨ℓ, hℓN⟩⁻¹ * ⟨w, hwN⟩) (by rw [map_mul, map_inv, hθℓ, inv_mul_cancel])
    exact this
  have hτ1 : τ ≠ 1 := by
    intro h1
    have hℓ1 : ℓ = 1 := by rw [hℓ, h1, map_one, map_one]
    rw [hℓ1, inv_one, one_mul] at hk
    have hle : Subgroup.zpowers w ≤ KK G L := Subgroup.zpowers_le.2 hk
    have hp : IsPGroup 2 (Subgroup.zpowers w) := by
      rw [IsPGroup.iff_card, Nat.card_zpowers, hw4]
      exact ⟨2, rfl⟩
    have := hK2 _ hle hp
    rw [Nat.card_zpowers, hw4] at this
    omega
  have hℓz : ℓ ≠ z := by
    intro he
    rw [h.z_eq, hℓ] at he
    have := pe_injective he
    have h0 := congrArg (fun f : Perm (Fin (m + 6 + 2)) => f 0) this
    simp only [iota2_apply_zero, swap_apply_left] at h0
    exact ne01 h0
  have hℓ2 : orderOf ℓ = 2 := by
    have hℓℓ : ℓ * ℓ = 1 := by rw [hℓ, ← map_mul, ← map_mul, hττ, map_one, map_one]
    have hℓ1 : ℓ ≠ 1 := by
      intro he
      rw [hℓ] at he
      have h1 : iota2 (m + 6) τ = 1 := pe_injective (he.trans (map_one _).symm)
      exact hτ1 (iota2_injective _ (h1.trans (map_one _).symm))
    exact orderOf_eq_prime (by rw [sq]; exact hℓℓ) hℓ1
  have hℓzc : ℓ * z = z * ℓ := by
    rw [hℓ, h.z_eq, ← map_mul, ← map_mul]
    congr 1
    refine Equiv.Perm.ext fun x => ?_
    simp only [Perm.mul_apply]
    by_cases hx0 : x = 0
    · rw [hx0, swap_apply_left, iota2_apply_one, iota2_apply_zero, swap_apply_left]
    by_cases hx1 : x = 1
    · rw [hx1, swap_apply_right, iota2_apply_zero, iota2_apply_one, swap_apply_right]
    · have h1 : iota2 (m + 6) τ x ≠ 0 := fun he =>
        hx0 ((iota2 (m + 6) τ).injective (he.trans (iota2_apply_zero τ).symm))
      have h2 : iota2 (m + 6) τ x ≠ 1 := fun he =>
        hx1 ((iota2 (m + 6) τ).injective (he.trans (iota2_apply_one τ).symm))
      rw [swap_apply_of_ne_of_ne hx0 hx1, swap_apply_of_ne_of_ne h1 h2]
  let M : Subgroup (GLV V) := KK G L ⊔ Subgroup.zpowers ℓ
  have hMN : M ≤ NN G L := sup_le h.K_le_N (Subgroup.zpowers_le.2 hℓN)
  have hθM : ∀ x : ↥(NN G L), (x : GLV V) ∈ M → θ x ∈ Subgroup.zpowers τ := by
    intro x hx
    let P : Subgroup (GLV V) :=
      ((Subgroup.zpowers τ).comap θ).map (NN G L).subtype
    have hMP : M ≤ P := by
      refine sup_le (fun k hk => ⟨⟨k, h.K_le_N hk⟩, ?_, rfl⟩) (Subgroup.zpowers_le.2
        ⟨⟨ℓ, hℓN⟩, by
          show θ ⟨ℓ, hℓN⟩ ∈ Subgroup.zpowers τ
          rw [hθℓ]; exact Subgroup.mem_zpowers τ, rfl⟩)
      show θ ⟨k, h.K_le_N hk⟩ ∈ Subgroup.zpowers τ
      rw [(hθ1 _).2 fun a => (Subgroup.mem_centralizer_iff.1 hk.2 _ (h.jL_mem a)).symm]
      exact Subgroup.one_mem _
    obtain ⟨y, hy, hyx⟩ := hMP hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hbound : ∀ Q : Subgroup (GLV V), Q ≤ M → IsPGroup 2 Q → Nat.card Q ≤ 4 := by
    intro Q hQM hQ
    let f : ↥Q →* Perm (Fin (m + 6)) := θ.comp (Subgroup.inclusion (hQM.trans hMN))
    have hker : Nat.card f.ker ≤ 2 := by
      let Qk : Subgroup (GLV V) := f.ker.map Q.subtype
      have hQk : Qk ≤ KK G L := by
        rintro _ ⟨q, hq, rfl⟩
        exact hcentral _ hq
      have hQk2 : IsPGroup 2 Qk := (hQ.to_subgroup f.ker).map Q.subtype
      have := hK2 Qk hQk hQk2
      rwa [Subgroup.card_map_of_injective Q.subtype_injective] at this
    have hrange : Nat.card f.range ≤ 2 := by
      have hle : f.range ≤ Subgroup.zpowers τ := by
        rintro _ ⟨q, rfl⟩
        exact hθM _ (hQM q.2)
      have := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hττ) hτ1] at this
      exact this
    have := Subgroup.card_ker_mul_card_range f
    rw [← this]
    nlinarith
  have hwM : w ∈ M := by
    have : w = ℓ * (ℓ⁻¹ * w) := by group
    rw [this]
    exact M.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers ℓ)) (Subgroup.mem_sup_left hk)
  let E : Subgroup (GLV V) := Subgroup.zpowers z ⊔ Subgroup.zpowers ℓ
  have hEM : E ≤ M := sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_sup_left h.z_mem_K))
    (Subgroup.zpowers_le.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers ℓ)))
  have hE2 : IsPGroup 2 E := by
    refine IsPGroup.to_sup_of_normal_right'
      (isPGroup_zpowers_of_mul_self (mul_self_of_orderOf_two hz2))
      (isPGroup_zpowers_of_mul_self (mul_self_of_orderOf_two hℓ2)) ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact ((Commute.zpow_left (show Commute ℓ z from hℓzc) k)).eq
  let E' : Subgroup ↥M := E.subgroupOf M
  have hE'2 : IsPGroup 2 E' := hE2.comap_subtype
  obtain ⟨P₃, hP₃⟩ := hE'2.exists_le_sylow
  let W' : Subgroup ↥M := Subgroup.zpowers ⟨w, hwM⟩
  have hW'2 : IsPGroup 2 W' := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, Subgroup.orderOf_mk, hw4]
    exact ⟨2, rfl⟩
  obtain ⟨P₄, hP₄⟩ := hW'2.exists_le_sylow
  have hcardP : ∀ P : Sylow 2 ↥M, Nat.card P ≤ 4 := by
    intro P
    have := hbound ((P : Subgroup ↥M).map M.subtype) (Subgroup.map_subtype_le _)
      (P.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective M.subtype_injective] at this
  have hW'card : Nat.card W' = 4 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hw4]
  have hP₄eq : (P₄ : Subgroup ↥M) = W' :=
    (Subgroup.eq_of_le_of_card_ge hP₄ (by rw [hW'card]; exact hcardP P₄)).symm
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥M P₄ P₃
  have hmem : ∀ x : ↥M, x ∈ (P₃ : Subgroup ↥M) → x ∈ Subgroup.zpowers (c * ⟨w, hwM⟩ * c⁻¹) := by
    intro x hx
    rw [← hc, Sylow.coe_subgroup_smul, hP₄eq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    show MulAut.conj c (⟨w, hwM⟩ ^ k) ∈ _
    rw [map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  have hcw4 : orderOf (c * ⟨w, hwM⟩ * c⁻¹) = 4 := by
    rw [show c * ⟨w, hwM⟩ * c⁻¹ = (MulAut.conj c).toMonoidHom ⟨w, hwM⟩ from rfl,
      orderOf_injective _ (MulAut.conj c).injective, Subgroup.orderOf_mk, hw4]
  have hzP : (⟨z, hEM (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))⟩ : ↥M) ∈
      (P₃ : Subgroup ↥M) := hP₃ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left
        (Subgroup.mem_zpowers z)))
  have hℓP : (⟨ℓ, hEM (Subgroup.mem_sup_right (Subgroup.mem_zpowers ℓ))⟩ : ↥M) ∈
      (P₃ : Subgroup ↥M) := hP₃ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers ℓ)))
  have e1 := eq_sq_of_mem_zpowers hcw4 (hmem _ hzP) (by rw [Subgroup.orderOf_mk]; exact hz2)
  have e2 := eq_sq_of_mem_zpowers hcw4 (hmem _ hℓP) (by rw [Subgroup.orderOf_mk]; exact hℓ2)
  exact hℓz (congrArg Subtype.val (e2.trans e1.symm))

end CaseIAux

end CFSG.CGT.Foote82
