module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31iSylow
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31iQuat
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31iCoreC
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31iU

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2.Lemma31iRels

namespace Lemma31i

open scoped Pointwise

theorem card_sup_zpowers_le {H : Type} [Group H] [Finite H] (P : Subgroup H) {t : H}
    (htt : t * t = 1) (hP : ∀ x ∈ P, t * x * t⁻¹ ∈ P) :
    Nat.card ↥(P ⊔ zpowers t) ≤ 2 * Nat.card ↥P := by
  have hnorm : zpowers t ≤ normalizer (P : Set H) := by
    rw [zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hP x hx, fun hx => ?_⟩
    have h1 := hP _ hx
    have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
      calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
        _ = x := by rw [htt]; group
    rwa [e] at h1
  have hcoe : ((P ⊔ zpowers t : Subgroup H) : Set H) = (P : Set H) * (zpowers t : Set H) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P (zpowers t) hnorm
  have hsub : ((P ⊔ zpowers t : Subgroup H) : Set H) ⊆
      (P : Set H) ∪ (fun x => x * t) '' (P : Set H) := by
    intro x hx
    rw [hcoe] at hx
    obtain ⟨p, hp, w, hw, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (show w ∈ zpowers t from hw)
    show p * t ^ k ∈ (P : Set H) ∪ (fun x => x * t) '' (P : Set H)
    rcases Lemma31iU.zpow_sq_cases htt k with hk | hk
    · left
      rw [hk, mul_one]
      exact hp
    · right
      exact ⟨p, hp, by rw [hk]⟩
  calc Nat.card ↥(P ⊔ zpowers t) = ((P ⊔ zpowers t : Subgroup H) : Set H).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ((P : Set H) ∪ (fun x => x * t) '' (P : Set H)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (P : Set H).ncard + ((fun x => x * t) '' (P : Set H)).ncard := Set.ncard_union_le _ _
    _ = (P : Set H).ncard + (P : Set H).ncard := by
        rw [Set.ncard_image_of_injective _ (mul_left_injective t)]
    _ = 2 * Nat.card ↥P := by
        rw [← Nat.card_coe_set_eq]
        change Nat.card ↥P + Nat.card ↥P = 2 * Nat.card ↥P
        ring

theorem card_le_half {H : Type} [Group H] [Finite H] {C G₀ : Subgroup H} (hCG : C ≤ G₀) {j : H}
    (hj : j ∈ G₀) (hjC : j ∉ C) {N : ℕ} (hN : Nat.card ↥G₀ ≤ 2 * N) : Nat.card ↥C ≤ N := by
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hCG
  have hc2 : 2 ≤ c := by
    by_contra hcon
    push Not at hcon
    interval_cases c
    · rw [mul_zero] at hc
      have := Nat.card_pos (α := ↥G₀)
      omega
    · rw [mul_one] at hc
      have h1 := Subgroup.eq_of_le_of_card_ge hCG (le_of_eq hc)
      exact hjC (by rw [h1]; exact hj)
  have : Nat.card ↥C * 2 ≤ Nat.card ↥C * c := Nat.mul_le_mul_left _ hc2
  omega

section Rels

variable {H : Type} [Group H] {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem rels_of (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) {t : H}
    (htt : t * t = 1) (hK : K₁.map (MulAut.conj t).toMonoidHom = K₂) {n : ℕ} (hn : 3 ≤ n)
    {d j d' j' : H} (hd : d ∈ K₁) (hj : j ∈ K₁) (hdo : orderOf d = 2 ^ (n - 1))
    (hdz : d ^ 2 ^ (n - 2) = z) (hjj : j * j = z) (hjd : j * d * j⁻¹ = d⁻¹)
    (hd' : d' = t * d * t⁻¹) (hj' : j' = t * j * t⁻¹) : Rels n z t d j d' j' := by
  have htz : t * z * t⁻¹ = z := h.t_comm_z hz hz1 htt hK
  have hdK : t * d * t⁻¹ ∈ K₂ := ProdSL2.swap_mem₁ hK hd
  have hjK : t * j * t⁻¹ ∈ K₂ := ProdSL2.swap_mem₁ hK hj
  subst hd' hj'
  refine
    { three_le := hn
      d_ord := hdo
      d'_ord := ?_
      z_eq := hdz.symm
      z_eq' := ?_
      jj := hjj
      jj' := ?_
      jdj := hjd
      jdj' := ?_
      dd' := h.comm d hd _ hdK
      dj' := h.comm d hd _ hjK
      jd' := h.comm j hj _ hdK
      jj'c := h.comm j hj _ hjK
      tt := htt
      td := rfl
      tj := rfl
      indep := ?_ }
  · have := MulEquiv.orderOf_eq (MulAut.conj t) d
    rw [MulAut.conj_apply] at this
    exact this.trans hdo
  · rw [conj_pow, hdz, htz]
  · calc (t * j * t⁻¹) * (t * j * t⁻¹) = t * (j * j) * t⁻¹ := by group
      _ = t * z * t⁻¹ := by rw [hjj]
      _ = z := htz
  · calc (t * j * t⁻¹) * (t * d * t⁻¹) * (t * j * t⁻¹)⁻¹ = t * (j * d * j⁻¹) * t⁻¹ := by group
      _ = t * d⁻¹ * t⁻¹ := by rw [hjd]
      _ = (t * d * t⁻¹)⁻¹ := by group
  · intro k l hkl
    have h1 : d ^ k ∈ K₁ := K₁.pow_mem hd k
    have h2 : (t * d * t⁻¹) ^ l ∈ K₂ := K₂.pow_mem hdK l
    exact h.inter_cases hz hz1 _ ⟨h1, hkl ▸ h2⟩

end Rels

end Lemma31i

open Lemma31i in
theorem ivk_3_1i_fixed :
    ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H),
      ProdSL2 H K₁ K₂ F₁ F₂ → ∀ z ∈ K₁ ⊓ K₂, z ≠ 1 → ∀ T : Sylow 2 H,
        ∀ u ∈ (T : Subgroup H) ⊓ (K₁ ⊔ K₂), orderOf u = 2 → u ≠ z →
          (∀ x ∈ (T : Subgroup H) ⊓ (K₁ ⊔ K₂), ∀ v ∈ zpowers u ⊔ zpowers z,
            x * v * x⁻¹ ∈ zpowers u ⊔ zpowers z) →
          ∀ t ∈ (T : Subgroup H), orderOf t = 2 → K₁.map (MulAut.conj t).toMonoidHom = K₂ →
          (∀ v ∈ zpowers u ⊔ zpowers z, t * v * t⁻¹ ∈ zpowers u ⊔ zpowers z) →
          ∀ n : ℕ, Nat.card ↥((T : Subgroup H) ⊓ K₁) * 2 = 2 ^ (n + 1) →
            ∃ B₁ B₂ : Subgroup H, ∃ y : H, orderOf y = 2 ∧
              centralizer ({u} : Set H) ⊓ (((T : Subgroup H) ⊓ (K₁ ⊔ K₂)) ⊔ zpowers t) =
                (B₁ ⊔ B₂) ⊔ zpowers y ∧
              (∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) ∧ B₁ ⊓ B₂ = ⊥ ∧
              IsDihedralOrder ↥B₁ (2 ^ (n - 1)) ∧ IsDihedralOrder ↥B₂ (2 ^ (n - 1)) ∧
              IsDihedralOrder ↥(B₁ ⊔ zpowers y) (2 ^ n) ∧ IsDihedralOrder ↥(B₂ ⊔ zpowers y) (2 ^ n) := by
  intro F₁ F₂ _ _ H _ _ K₁ K₂ h z hz hz1 T u hu hu2 huz hP t ht ht2 hK htn n hn
  have htt : t * t = 1 := Lemma31iU.mul_self_of_orderOf ht2
  have huu : u * u = 1 := Lemma31iU.mul_self_of_orderOf hu2
  have hu1 : u ≠ 1 := Lemma31iU.ne_one_of_orderOf hu2
  obtain ⟨hn3, hzT, ⟨φ⟩, hPcard, hdec⟩ := Lemma31iSylow.sylow_side h hz hz1 T ht htt hK hn
  have hzz := Lemma31iU.z_sq h hz hz1
  have hKz : ∀ x ∈ K₁ ⊔ K₂, z * x = x * z := fun x hx => h.z_comm hz hx
  have htz : t * z * t⁻¹ = z := h.t_comm_z hz hz1 htt hK
  have htzc : t * z = z * t := by
    have := htz
    rwa [mul_inv_eq_iff_eq_mul] at this
  have huK : u ∈ K₁ ⊔ K₂ := hu.2
  have huzc : u * z = z * u := (hKz u huK).symm
  obtain ⟨a, ha, b, hb, hab⟩ := hdec u hu
  obtain ⟨haa, hbb⟩ := Lemma31iU.sq_of_decomp h hz hz1 ha.2 hb.2 (by rw [← hab]; exact huu)
    (by rw [← hab]; exact hu1) (by rw [← hab]; exact huz)
  have hdich : ∀ x ∈ (T : Subgroup H) ⊓ K₁, x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a * z := by
    intro x hx
    have hxP : x ∈ (T : Subgroup H) ⊓ (K₁ ⊔ K₂) := ⟨hx.1, Subgroup.mem_sup_left hx.2⟩
    have hxz : x * z = z * x := (hKz x (Subgroup.mem_sup_left hx.2)).symm
    have hmem := hP x hxP u (Subgroup.mem_sup_left (mem_zpowers u))
    have hdi := Lemma31iU.conj_dichotomy huu hzz huzc hu1 huz hxz hmem
    rw [hab] at hdi
    exact Lemma31iU.conj_a h hz hb.2 hx.2 hdi
  have hzP₁ : z ∈ (T : Subgroup H) ⊓ K₁ := ⟨hzT, hz.1⟩
  obtain ⟨d, hdP, j, hjP, hdo, hdz, hjj, hjd, i, hai⟩ :=
    Lemma31iQuat.exists_dj hn3 φ hzP₁ hz1 hzz ha hdich
  obtain ⟨d', hd'⟩ : ∃ d' : H, d' = t * d * t⁻¹ := ⟨_, rfl⟩
  obtain ⟨j', hj'⟩ : ∃ j' : H, j' = t * j * t⁻¹ := ⟨_, rfl⟩
  have hR : Rels n z t d j d' j' :=
    rels_of h hz hz1 htt hK hn3 hdP.2 hjP.2 hdo hdz hjj hjd hd' hj'
  have haform := Lemma31iU.a_form hn3 hdo hdz hzz haa hai
  have htu : t * (a * b) * t⁻¹ = a * b ∨ t * (a * b) * t⁻¹ = (a * b) * z := by
    have hmem := htn u (Subgroup.mem_sup_left (mem_zpowers u))
    have hdi := Lemma31iU.conj_dichotomy huu hzz huzc hu1 huz htzc hmem
    rw [hab] at hdi
    exact hdi
  have hbform := Lemma31iU.swap_b h hz hz1 htt hK ha.2 hb.2 htu
  have hD : d ^ 2 ^ (n - 3) ∈ K₁ := K₁.pow_mem hdP.2 _
  have huform := Lemma31iU.u_form h hz hz1 htt hK hD haform hbform
  have hDt : t * d ^ 2 ^ (n - 3) * t⁻¹ = d' ^ 2 ^ (n - 3) := by
    rw [hd', conj_pow]
  rw [hDt] at huform
  have huform' : a * b = uvec n d d' ∨ a * b = uvec n d d' * z := huform
  have hja : j * a * j⁻¹ = a * z := by
    calc j * a * j⁻¹ = j * d ^ i * j⁻¹ := by rw [hai]
      _ = (j * d * j⁻¹) ^ i := conj_pow.symm
      _ = (d⁻¹) ^ i := by rw [hjd]
      _ = (d ^ i)⁻¹ := inv_pow d i
      _ = a⁻¹ := by rw [hai]
      _ = a * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, haa, hzz])
  have hjb : j * b * j⁻¹ = b := by
    rw [mul_inv_eq_iff_eq_mul]
    exact h.comm j hjP.2 b hb.2
  have hzb : z * b = b * z := hKz b (Subgroup.mem_sup_right hb.2)
  have hjc : j * (a * b) * j⁻¹ = a * b * z := by
    calc j * (a * b) * j⁻¹ = (j * a * j⁻¹) * (j * b * j⁻¹) := by group
      _ = (a * z) * b := by rw [hja, hjb]
      _ = a * (z * b) := by group
      _ = a * (b * z) := by rw [hzb]
      _ = a * b * z := by group
  set P : Subgroup H := (T : Subgroup H) ⊓ (K₁ ⊔ K₂) with hPdef
  have hPt : ∀ x ∈ P, t * x * t⁻¹ ∈ P := fun x hx =>
    ⟨(T : Subgroup H).mul_mem ((T : Subgroup H).mul_mem ht hx.1) ((T : Subgroup H).inv_mem ht),
      h.fstar_normal.conj_mem x hx.2 t⟩
  have hdG : d ∈ P := ⟨hdP.1, Subgroup.mem_sup_left hdP.2⟩
  have hjG : j ∈ P := ⟨hjP.1, Subgroup.mem_sup_left hjP.2⟩
  have hd'G : d' ∈ P := by rw [hd']; exact hPt d hdG
  have hj'G : j' ∈ P := by rw [hj']; exact hPt j hjG
  have hG₀ : Nat.card ↥(P ⊔ zpowers t) ≤ 2 * 2 ^ (2 * n - 1) := by
    have := card_sup_zpowers_le P htt hPt
    rwa [hPcard] at this
  have hBle : B₁ d d' j j' t ⊔ B₂ d d' t ⊔ zpowers (j * d' * j') ≤ P ⊔ zpowers t :=
    Lemma31iCoreC.B_le_of_mem (Subgroup.mem_sup_left hdG) (Subgroup.mem_sup_left hd'G)
      (Subgroup.mem_sup_left hjG) (Subgroup.mem_sup_left hj'G) (Subgroup.mem_sup_right (mem_zpowers t))
  have hBcent : B₁ d d' j j' t ⊔ B₂ d d' t ⊔ zpowers (j * d' * j') ≤
      centralizer ({a * b} : Set H) := by
    intro g hg
    rw [mem_centralizer_singleton_iff]
    have hg1 := Lemma31iCoreB.comm_u hR g hg
    have hg2 := Lemma31iCoreC.B_comm_z hR g hg
    rcases huform' with hu' | hu'
    · rw [hu']
      exact hg1
    · rw [hu']
      calc g * (uvec n d d' * z) = (g * uvec n d d') * z := by group
        _ = (uvec n d d' * g) * z := by rw [hg1]
        _ = uvec n d d' * (g * z) := by group
        _ = uvec n d d' * (z * g) := by rw [hg2]
        _ = uvec n d d' * z * g := by group
  have hjP' : j ∈ P ⊔ zpowers t := Subgroup.mem_sup_left hjG
  have hjC : j ∉ centralizer ({a * b} : Set H) ⊓ (P ⊔ zpowers t) := by
    intro hj
    have := mem_centralizer_singleton_iff.mp hj.1
    have e : j * (a * b) * j⁻¹ = a * b := by
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    rw [hjc] at e
    exact hz1 (mul_eq_left.mp e)
  have hCle : Nat.card ↥(centralizer ({a * b} : Set H) ⊓ (P ⊔ zpowers t)) ≤ 2 ^ (2 * n - 1) :=
    card_le_half inf_le_right hjP' hjC hG₀
  have hbig := Lemma31iCoreC.card_big hR
  refine ⟨B₁ d d' j j' t, B₂ d d' t, j * d' * j', Lemma31iCoreB.orderOf_y hR, ?_,
    Lemma31iCoreA.B_comm hR, Lemma31iCoreA.B_inf hR, Lemma31iCoreA.B₁_dihedral hR,
    Lemma31iCoreA.B₂_dihedral hR, Lemma31iCoreB.y_dihedral₁ hR, Lemma31iCoreB.y_dihedral₂ hR⟩
  rw [hab]
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hBcent hBle) (hCle.trans hbig)).symm

end CFSG.GH74.GLS.IVK.Proofs2
