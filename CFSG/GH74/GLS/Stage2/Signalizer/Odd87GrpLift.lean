module

public import Mathlib.GroupTheory.Sylow
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup

section Surjection

theorem inf_eq_bot_of_isPGroup_of_ne {H : Type*} [Group H] [Finite H] {p q : ℕ} [hp : Fact p.Prime]
    [hq : Fact q.Prime] (hpq : p ≠ q) (A B : Subgroup H) (hA : IsPGroup p ↥A)
    (hB : IsPGroup q ↥B) : A ⊓ B = ⊥ := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := p)).mp hA
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := q)).mp hB
  have : Nat.Coprime (Nat.card A) (Nat.card B) := by
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes hp.out hq.out).mpr hpq)
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard this)

theorem isPGroup_two_inf_eq_bot_of_odd {M : Type*} [Group M] [Finite M] (P K : Subgroup M)
    (hP : IsPGroup 2 ↥P) (hK : Odd (Nat.card K)) : P ⊓ K = ⊥ := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have : Nat.Coprime (Nat.card P) (Nat.card K) := by
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hK)
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard this)

theorem map_sylow_comap_eq {G H : Type*} [Group G] [Finite G] [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) {p : ℕ} [Fact p.Prime] (W : Subgroup H) (hW : IsPGroup p ↥W)
    (P : Sylow p ↥(W.comap φ)) : (P.map (W.comap φ).subtype).map φ = W := by
  let f : ↥(W.comap φ) →* ↥W := (φ.comp (W.comap φ).subtype).codRestrict W fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨g, rfl⟩ := hφ w
    exact ⟨⟨g, hw⟩, rfl⟩
  have hTop : IsPGroup p ↥(⊤ : Subgroup ↥W) := hW.of_equiv Subgroup.topEquiv.symm
  have hmax := (P.mapSurjective hf).3 hTop le_top
  rw [Sylow.coe_mapSurjective] at hmax
  ext x
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    exact k.2
  · intro hx
    have : (⟨x, hx⟩ : ↥W) ∈ P.map f := by rw [← hmax]; trivial
    obtain ⟨a, ha, hax⟩ := this
    exact ⟨a.1, ⟨a, ha, rfl⟩, congrArg Subtype.val hax⟩

theorem exists_pGroup_map_sup_eq_top {G H : Type*} [Group G] [Finite G] [Group H] (φ : G →* H)
    {p : ℕ} [Fact p.Prime] (W X : Subgroup H) [W.Normal] (hX : IsPGroup p ↥X)
    (hXW : X ⊔ W = ⊤) (B : Subgroup G) (hB : B.map φ ⊔ W = ⊤) :
    ∃ P : Subgroup G, P ≤ B ∧ IsPGroup p ↥P ∧ P.map φ ⊔ W = ⊤ := by
  obtain ⟨P₁⟩ : Nonempty (Sylow p ↥B) := inferInstance
  let f : ↥B →* H ⧸ W := ((QuotientGroup.mk' W).comp φ).comp B.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have hh : h ∈ B.map φ ⊔ W := by rw [hB]; trivial
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hh
    obtain ⟨a, ha, w, hw, rfl⟩ := hh
    obtain ⟨b, hb, rfl⟩ := ha
    refine ⟨⟨b, hb⟩, ?_⟩
    have hw1 : QuotientGroup.mk' W w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
    show QuotientGroup.mk' W (φ b) = QuotientGroup.mk' W (φ b * w)
    rw [map_mul, hw1, mul_one]
  have hQuot : IsPGroup p (H ⧸ W) := by
    refine hX.of_surjective ((QuotientGroup.mk' W).comp X.subtype) ?_
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have hh : h ∈ X ⊔ W := by rw [hXW]; trivial
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hh
    obtain ⟨x, hx, w, hw, rfl⟩ := hh
    refine ⟨⟨x, hx⟩, ?_⟩
    have hw1 : QuotientGroup.mk' W w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
    show QuotientGroup.mk' W x = QuotientGroup.mk' W (x * w)
    rw [map_mul, hw1, mul_one]
  have hTop : IsPGroup p ↥(⊤ : Subgroup (H ⧸ W)) := hQuot.of_equiv Subgroup.topEquiv.symm
  have hmax := (P₁.mapSurjective hf).3 hTop le_top
  rw [Sylow.coe_mapSurjective] at hmax
  refine ⟨P₁.map B.subtype, Subgroup.map_subtype_le _, P₁.isPGroup'.map _, ?_⟩
  rw [eq_top_iff]
  intro h _
  have : (QuotientGroup.mk h : H ⧸ W) ∈ P₁.map f := by rw [← hmax]; trivial
  obtain ⟨a, ha, hax⟩ := this
  have hq : φ a.1 ∈ (P₁.map B.subtype).map φ := ⟨a.1, ⟨a, ha, rfl⟩, rfl⟩
  have hw : (φ a.1)⁻¹ * h ∈ W := QuotientGroup.eq.mp hax
  have : h = φ a.1 * ((φ a.1)⁻¹ * h) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hq hw

theorem exists_conj_map_eq_of_sup_eq_top {H : Type*} [Group H] [Finite H] {p : ℕ}
    [hp' : Fact p.Prime] (hp : p ≠ 2) (W X Q : Subgroup H) [W.Normal] (hW : IsPGroup 2 ↥W)
    (hX : IsPGroup p ↥X) (hQ : IsPGroup p ↥Q) (hXW : X ⊔ W = ⊤) (hQW : Q ⊔ W = ⊤) :
    ∃ h : H, Q.map (MulAut.conj h).toMonoidHom = X := by
  have hcard : ∀ S : Subgroup H, IsPGroup p ↥S → S ⊔ W = ⊤ → Nat.card S = W.index := by
    intro S hS hSW
    have hSW' : S ⊓ W = ⊥ := inf_eq_bot_of_isPGroup_of_ne hp S W hS hW
    have h1 : W.relIndex (S ⊔ W) = W.relIndex S := Subgroup.relIndex_sup_right S W
    rw [hSW, Subgroup.relIndex_top_right] at h1
    have h2 : W.relIndex S * Nat.card ↥(W ⊓ S) = Nat.card S := Subgroup.relIndex_mul_card W S
    rw [inf_comm, hSW', Subgroup.card_bot, mul_one] at h2
    exact h2.symm.trans h1.symm
  have hindex : ∀ S : Subgroup H, Nat.card S = W.index → S.index = Nat.card W := by
    intro S hS
    have h1 := Subgroup.card_mul_index S
    have h2 := Subgroup.card_mul_index W
    have hpos : 0 < Nat.card S := Nat.card_pos
    rw [hS] at h1 hpos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, ← h2, mul_comm])
  have hnd : ¬ p ∣ Nat.card W := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hW
    rw [hn]
    intro hd
    exact hp ((Nat.prime_dvd_prime_iff_eq hp'.out Nat.prime_two).mp (hp'.out.dvd_of_dvd_pow hd))
  let SQ : Sylow p H := hQ.toSylow (by rw [hindex Q (hcard Q hQ hQW)]; exact hnd)
  let SX : Sylow p H := hX.toSylow (by rw [hindex X (hcard X hX hXW)]; exact hnd)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H SQ SX
  refine ⟨h, ?_⟩
  have h1 : (SQ : Subgroup H).map (MulAut.conj h).toMonoidHom = SX := by
    rw [← hh]
    rfl
  exact h1

theorem exists_two_p_lift_of_sup_eq_top {G H : Type*} [Group G] [Finite G] [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (W X : Subgroup H)
    [W.Normal] (hW : IsPGroup 2 ↥W) (hX : IsPGroup p ↥X) (hWX : W ⊔ X = ⊤) :
    ∃ W' X' : Subgroup G, IsPGroup 2 ↥W' ∧ IsPGroup p ↥X' ∧ W'.map φ = W ∧ X'.map φ = X ∧
      X' ≤ normalizer (W' : Set G) := by
  have : Finite H := Finite.of_surjective φ hφ
  have hXW : X ⊔ W = ⊤ := by rw [sup_comm]; exact hWX
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥(W.comap φ)) := inferInstance
  have hP₀ := map_sylow_comap_eq φ hφ W hW P₀
  set W₀ : Subgroup G := P₀.map (W.comap φ).subtype with hW₀
  have hW₀2 : IsPGroup 2 ↥W₀ := P₀.isPGroup'.map _
  have hF : normalizer (W₀ : Set G) ⊔ W.comap φ = ⊤ := Sylow.normalizer_sup_eq_top P₀
  have hBW : (normalizer (W₀ : Set G)).map φ ⊔ W = ⊤ := by
    have h1 : (normalizer (W₀ : Set G) ⊔ W.comap φ).map φ = ⊤ := by
      rw [hF, Subgroup.map_top, MonoidHom.range_eq_top.mpr hφ]
    rwa [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective hφ] at h1
  obtain ⟨P, hPB, hPp, hPW⟩ := exists_pGroup_map_sup_eq_top φ W X hX hXW _ hBW
  obtain ⟨h, hh⟩ := exists_conj_map_eq_of_sup_eq_top hp W X (P.map φ) hW hX (hPp.map φ) hXW hPW
  obtain ⟨ĥ, hĥ⟩ := hφ h
  have hcφ : φ.comp (MulAut.conj ĥ).toMonoidHom = ((MulAut.conj h).toMonoidHom).comp φ := by
    ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, hĥ]
  refine ⟨W₀.map (MulAut.conj ĥ).toMonoidHom, P.map (MulAut.conj ĥ).toMonoidHom,
    hW₀2.map _, hPp.map _, ?_, ?_, ?_⟩
  · rw [Subgroup.map_map, hcφ, ← Subgroup.map_map, hP₀]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (by rw [Subgroup.normalizer_eq_top (H := W)]; trivial)
  · rw [Subgroup.map_map, hcφ, ← Subgroup.map_map]
    exact hh
  · exact (Subgroup.map_mono hPB).trans (Subgroup.le_normalizer_map _)

end Surjection

section Quotient

variable {M : Type} [Group M] [Finite M] (N : Subgroup M) [N.Normal]

theorem exists_two_lift (hN : Odd (Nat.card N)) (W : Subgroup (M ⧸ N)) (hW : IsPGroup 2 ↥W) :
    ∃ W' : Subgroup M, IsPGroup 2 ↥W' ∧ W'.map (QuotientGroup.mk' N) = W ∧ W' ⊓ N = ⊥ := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(W.comap (QuotientGroup.mk' N))) := inferInstance
  have hP := map_sylow_comap_eq (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) W hW P
  exact ⟨P.map _, P.isPGroup'.map _, hP, isPGroup_two_inf_eq_bot_of_odd _ N (P.isPGroup'.map _) hN⟩

theorem exists_involution_lift_quot (hN : Odd (Nat.card N)) (s : M ⧸ N) (hs : s * s = 1) :
    ∃ s' : M, s' * s' = 1 ∧ QuotientGroup.mk' N s' = s := by
  have h2 : s ^ 2 = 1 := by rw [pow_two]; exact hs
  have hW : IsPGroup 2 ↥(Subgroup.zpowers s) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  obtain ⟨W', -, hmap, hbot⟩ := exists_two_lift N hN _ hW
  have hs' : s ∈ W'.map (QuotientGroup.mk' N) := by
    rw [hmap]; exact Subgroup.mem_zpowers s
  obtain ⟨x, hx, rfl⟩ := hs'
  refine ⟨x, ?_, rfl⟩
  have hxx : x * x ∈ W' ⊓ N := by
    have h1 : QuotientGroup.mk' N (x * x) = 1 := by rw [map_mul]; exact hs
    exact ⟨W'.mul_mem hx hx, (QuotientGroup.eq_one_iff (x * x)).mp h1⟩
  rw [hbot] at hxx
  exact Subgroup.mem_bot.mp hxx

theorem exists_two_p_lift (hN : Odd (Nat.card N)) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (W X : Subgroup (M ⧸ N)) (hW : IsPGroup 2 ↥W) (hX : IsPGroup p ↥X)
    (hXW : X ≤ normalizer (W : Set (M ⧸ N))) :
    ∃ W' X' : Subgroup M, IsPGroup 2 ↥W' ∧ IsPGroup p ↥X' ∧
      W'.map (QuotientGroup.mk' N) = W ∧ X'.map (QuotientGroup.mk' N) = X ∧
      X' ≤ normalizer (W' : Set M) ∧ W' ⊓ N = ⊥ := by
  set π : M →* M ⧸ N := QuotientGroup.mk' N with hπ
  set Y : Subgroup (M ⧸ N) := W ⊔ X with hY
  have hWY : W ≤ Y := le_sup_left
  have hXY : X ≤ Y := le_sup_right
  have hYN : Y ≤ normalizer (W : Set (M ⧸ N)) := sup_le Subgroup.le_normalizer hXW
  set Yh : Subgroup M := Y.comap π with hYh
  let φ : ↥Yh →* ↥Y := (π.comp Yh.subtype).codRestrict Y fun g => g.2
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨m, hy⟩, rfl⟩
  have hWn : (W.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWY).mpr hYN
  have hW' : IsPGroup 2 ↥(W.subgroupOf Y) := hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWY).symm
  have hX' : IsPGroup p ↥(X.subgroupOf Y) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXY).symm
  have hsup : W.subgroupOf Y ⊔ X.subgroupOf Y = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hWY hXY]
    exact Subgroup.subgroupOf_self Y
  obtain ⟨W₂, X₂, hW₂, hX₂, hW₂φ, hX₂φ, hnorm⟩ :=
    exists_two_p_lift_of_sup_eq_top φ hφ hp (W.subgroupOf Y) (X.subgroupOf Y) hW' hX' hsup
  have hcomp : π.comp Yh.subtype = Y.subtype.comp φ := rfl
  refine ⟨W₂.map Yh.subtype, X₂.map Yh.subtype, hW₂.map _, hX₂.map _, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hW₂φ, Subgroup.subgroupOf_map_subtype]
    exact inf_of_le_left hWY
  · rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hX₂φ, Subgroup.subgroupOf_map_subtype]
    exact inf_of_le_left hXY
  · exact (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map _)
  · exact isPGroup_two_inf_eq_bot_of_odd _ N (hW₂.map _) hN

end Quotient

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
