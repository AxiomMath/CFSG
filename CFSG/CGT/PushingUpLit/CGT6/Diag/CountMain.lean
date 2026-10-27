module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.CountIndec
public import CFSG.CGT.PushingUpLit.CGT6.Diag.CountLower
public import CFSG.CGT.PushingUpLit.CGT6.Diag.Sel

public section

namespace CFSG.CGT.PushingUpLit.CGT6

namespace Diag.Count

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6

section Lower

variable {V : Type} [CommGroup V] [Finite V] {K K' Y : Subgroup (MulAut V)} {t : MulAut V}

omit [Finite V] in
theorem sup_commV_eq_top (h : DiagPre K K' Y t) {W : Subgroup V} (hW : GInv K W) {k₀ : MulAut V}
    (hk₀ : k₀ ∈ K') (hsup : W ⊔ diagImg k₀ W = ⊤) : W ⊔ commV Y = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v ∈ W ⊔ diagImg k₀ W := hsup ▸ Subgroup.mem_top v
  obtain ⟨w₁, hw₁, x, hx, rfl⟩ := Subgroup.mem_sup.mp hv
  obtain ⟨w₂, hw₂, rfl⟩ := hx
  obtain ⟨k, hk, hkk⟩ := (Diag.Sel.mem_K'_iff h).mp hk₀
  have hy : k * k₀ ∈ Y := (h.Y_mem _).mpr ⟨k, hk, by rw [hkk]⟩
  have hw' : k⁻¹ w₂ ∈ W := hW k⁻¹ (K.inv_mem hk) w₂ hw₂
  have hcomm : k * k₀ = k₀ * k := h.comm k hk k₀ hk₀
  have h1 : k₀.toMonoidHom w₂ = (k * k₀) (k⁻¹ w₂) := by
    rw [hcomm]
    simp [MulAut.mul_apply]
  have h2 : (k * k₀) (k⁻¹ w₂) * (k⁻¹ w₂)⁻¹ ∈ commV Y :=
    Subgroup.subset_closure ⟨k * k₀, hy, k⁻¹ w₂, rfl⟩
  have h3 : w₁ * k₀.toMonoidHom w₂ =
      (w₁ * k⁻¹ w₂) * ((k * k₀) (k⁻¹ w₂) * (k⁻¹ w₂)⁻¹) := by
    rw [h1, mul_assoc, mul_comm ((k * k₀) (k⁻¹ w₂)) (k⁻¹ w₂)⁻¹, mul_inv_cancel_left]
  rw [h3]
  exact Subgroup.mul_mem_sup (W.mul_mem hw₁ hw') h2

theorem lower_bound (hV : ∀ v : V, v ^ 2 = 1) (h : DiagPair K K' Y t) {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y))
    (hcore : DiagCoreOut K K' n) : 2 ^ (3 * n) ≤ Nat.card ↥(commV Y) := by
  have hUcard := card_commV (by omega) hnat
  have hU1 : 1 < Nat.card ↥(commV Y) := by
    rw [hUcard]
    have h1 : 0 < Nat.card ↥(commV Y ⊓ fixV Y) := Nat.card_pos
    have h2 : 1 < 2 ^ (2 * n) := Nat.one_lt_two_pow (by omega)
    nlinarith
  have hVnt : Nontrivial V := by
    have : Nontrivial ↥(commV Y) := Finite.one_lt_card_iff_nontrivial.mp hU1
    exact (commV Y).subtype_injective.nontrivial
  obtain ⟨θ₁⟩ := hcore.iso
  have hKcard : Nat.card ↥K = 2 ^ n * (2 ^ (2 * n) - 1) := by
    rw [Nat.card_congr θ₁.toEquiv, card_sl2_fq (by omega)]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K) 2 (n := n)
    (hKcard ▸ dvd_mul_right _ _)
  let S' : Subgroup (MulAut V) := (S.map K.subtype).map (MulAut.conj t).toMonoidHom
  have hS'card : Nat.card ↥S' = 2 ^ n := by
    simp only [S']
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective,
      Subgroup.card_map_of_injective K.subtype_injective, hS]
  have hS'K' : S' ≤ K' := by
    rw [h.Kconj]
    exact Subgroup.map_mono (by rintro _ ⟨u, -, rfl⟩; exact u.2)
  obtain ⟨w₀, hw₀1, hw₀⟩ := exists_fixed_of_hom hV (IsPGroup.of_card hS'card) S'.subtype
  have hfix : fixV S' ≠ ⊥ := by
    intro hbot
    have hmem : w₀ ∈ fixV S' := fun x hx => hw₀ ⟨x, hx⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hw₀1 hmem
  have hinv : GInv K (fixV S') := by
    intro k hk a ha s hs
    have h1 : k * s = s * k := h.comm k hk s (hS'K' hs)
    calc s (k a) = (s * k) a := rfl
      _ = (k * s) a := by rw [← h1]
      _ = k (s a) := rfl
      _ = k a := by rw [ha s hs]
  obtain ⟨W, hWfix, hWmin⟩ := Diag.Irr.exists_minimal_inv K hinv hfix
  obtain ⟨θ, ⟨hKW, β, hβs, hβk, hβe⟩, k₀, hk₀, hinf, hsup⟩ := hcore.split W hWmin
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hWcard : Nat.card ↥W = 2 ^ (2 * n) := by
    rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩), card_sl_model (by omega)]
  have hVcard : Nat.card V = 2 ^ (4 * n) := by
    have h1 := card_sup_mul_card_inf W (diagImg k₀ W)
    rw [hinf, hsup, Subgroup.card_bot, Subgroup.card_top, mul_one] at h1
    have h2 : Nat.card ↥(diagImg k₀ W) = Nat.card ↥W := by
      rw [diagImg, Subgroup.card_map_of_injective (f := k₀.toMonoidHom) k₀.injective]
    rw [h1, h2, hWcard, ← pow_add]
    ring_nf
  have hsupU : W ⊔ commV Y = ⊤ := sup_commV_eq_top h.toDiagPre hKW hk₀ hsup
  have hcomm : ∀ u ∈ S, ∀ w ∈ W, (u : MulAut V) w * w⁻¹ ∈ commV Y := by
    intro u hu w hw
    have hs : t * (u : MulAut V) * t⁻¹ ∈ S' :=
      ⟨(u : MulAut V), ⟨u, hu, rfl⟩, by simp [MulAut.conj_apply]⟩
    have hsw : (t * (u : MulAut V) * t⁻¹) w = w := (mem_fixV.mp (hWfix hw)) _ hs
    have hy : (u : MulAut V) * (t * (u : MulAut V) * t⁻¹) ∈ Y := (h.Y_mem _).mpr ⟨u, u.2, rfl⟩
    have h1 : ((u : MulAut V) * (t * (u : MulAut V) * t⁻¹)) w = (u : MulAut V) w := by
      rw [MulAut.mul_apply, hsw]
    rw [← h1]
    exact Subgroup.subset_closure ⟨_, hy, w, rfl⟩
  have hge := card_inf_ge (by omega) θ hKW β hβs hβe S hS hcomm
  have hprod := card_sup_mul_card_inf W (commV Y)
  rw [hsupU, Subgroup.card_top, hVcard, hWcard] at hprod
  have h1 : 2 ^ (2 * n) * 2 ^ (3 * n) ≤ 2 ^ (2 * n) * Nat.card ↥(commV Y) := by
    rw [← hprod]
    calc 2 ^ (2 * n) * 2 ^ (3 * n) = 2 ^ (4 * n) * 2 ^ n := by
          rw [← pow_add, ← pow_add]
          ring_nf
      _ ≤ 2 ^ (4 * n) * Nat.card ↥(W ⊓ commV Y) := Nat.mul_le_mul_left _ hge
  exact Nat.le_of_mul_le_mul_left h1 (by positivity)

end Lower

end Diag.Count

theorem diagModCount_holds : DiagMod_count := by
  intro V _ _ hV K K' Y t h n hn hnat hcore
  exact le_antisymm (Diag.Count.card_commV_le hn hV h.perfY hnat)
    (Diag.Count.lower_bound hV h hn hnat hcore)

end CFSG.CGT.PushingUpLit.CGT6
