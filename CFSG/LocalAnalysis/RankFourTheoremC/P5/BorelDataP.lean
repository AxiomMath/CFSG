module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.BorelData
public import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

structure BorelDataP (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M : Subgroup G) (x : G) {n : ℕ}
    (f : GaloisField p n → G) (W : Subgroup G) : Prop where
  five_le : 5 ≤ p
  three_le : 3 ≤ n
  f_add : ∀ s t, f (s + t) = f s * f t
  f_inj : Function.Injective f
  f_comm : ∀ t, f t * x = x * f t
  f_ne : ∀ t, f t ≠ x
  le : W ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G)
  mem_iff : ∀ g, g ∈ W ↔ ∃ (t : GaloisField p n) (i : ℕ), i < p ∧ g = f t * x ^ i
  of_pow_p : ∀ y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), y ^ p = 1 → y ∈ W
  torus : ∀ a : (GaloisField p n)ˣ, ∃ g : G, g * x * g⁻¹ = x ∧
    ∀ t, g * f t * g⁻¹ = f ((a : GaloisField p n) ^ 2 * t)
  x_pow : x ^ p = 1
  x_ne_one : x ≠ 1
  x_mem : x ∈ (P : Subgroup G)
  reduced : ∃ (R : Sylow p (RedCent p x)) (K : Subgroup (RedCent p x))
      (d : TauCeti.ValidLieTypeIndex),
    PPointFacts p M x R K (.lie d) ∧ IsLinTwoIndex p n d ∧ Nonempty (K ≃* PSL2GF p n) ∧
    (∀ t, ∃ hc : f t ∈ centralizer ({x} : Set G),
      QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
        ⟨f t, hc⟩ ∈ (R : Subgroup (RedCent p x)) ⊓ K ∧
      (t ≠ 0 → QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
        ⟨f t, hc⟩ ≠ 1)) ∧
    (∀ k ∈ (R : Subgroup (RedCent p x)) ⊓ K, ∃ (t : GaloisField p n)
      (hc : f t ∈ centralizer ({x} : Set G)),
      QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
        ⟨f t, hc⟩ = k) ∧
    (∀ σ ∈ K, σ ∈ normalizer (((R : Subgroup (RedCent p x)) ⊓ K : Subgroup (RedCent p x)) :
        Set (RedCent p x)) → ∃ b : (GaloisField p n)ˣ, ∀ (t : GaloisField p n)
      (hc : f t ∈ centralizer ({x} : Set G))
      (hc' : f ((b : GaloisField p n) ^ 2 * t) ∈ centralizer ({x} : Set G)),
      σ * QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
        ⟨f t, hc⟩ * σ⁻¹ = QuotientGroup.mk'
          (primeComplementCore (G := centralizer ({x} : Set G)) p)
          ⟨f ((b : GaloisField p n) ^ 2 * t), hc'⟩) ∧
    (∀ a : (GaloisField p n)ˣ, ∃ τ ∈ K, τ ∈ normalizer (((R : Subgroup (RedCent p x)) ⊓ K :
        Subgroup (RedCent p x)) : Set (RedCent p x)) ∧ ∀ (t : GaloisField p n)
      (hc : f t ∈ centralizer ({x} : Set G))
      (hc' : f ((a : GaloisField p n) ^ 2 * t) ∈ centralizer ({x} : Set G)),
      τ * QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
        ⟨f t, hc⟩ * τ⁻¹ = QuotientGroup.mk'
          (primeComplementCore (G := centralizer ({x} : Set G)) p)
          ⟨f ((a : GaloisField p n) ^ 2 * t), hc'⟩) ∧
        (R : Subgroup (RedCent p x)) =
          (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
            (centralizer ({x} : Set G))).map
            (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))

section Repack

variable {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {x : G}

theorem exists_borelDataP_of_linTwo (hp5 : 5 ≤ p) (hloc : D1Local p P M)
    (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x)
    {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)} {d : TauCeti.ValidLieTypeIndex}
    {n : ℕ} (hn : 3 ≤ n) (hf : PPointFacts p M x R K (.lie d)) (hd : IsLinTwoIndex p n d)
    (hReq : (R : Subgroup (RedCent p x)) =
      (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
        (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))) :
    ∃ (f : GaloisField p n → G) (W : Subgroup G), BorelDataP p P M x f W := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨f, W, hfadd, hfinj, hfx, hxf, hWQ, hW, hW3, htor, hK, h1, h2, h3, h4, h5⟩ :=
    PPointP.IsPPoint.exists_borelData_p hp2 hloc h (by omega) hp5 hf hd hReq
  have hxp : x ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.elem.2.1] at this
  have hx1 : x ≠ 1 := by
    intro h1'
    have := h.elem.2.1
    rw [h1', orderOf_one] at this
    exact hp.out.ne_one this.symm
  exact ⟨f, W, ⟨hp5, hn, hfadd, hfinj, hfx, hxf, hWQ, hW, hW3, htor, hxp, hx1, h.mem,
    ⟨R, K, d, hf, hd, hK, h1, h2, h3, h4, h5⟩⟩⟩

end Repack

namespace BorelDataP

variable {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {x : G} {n : ℕ}
  {f : GaloisField p n → G} {W : Subgroup G}

theorem f_zero (hB : BorelDataP p P M x f W) : f 0 = 1 := by
  have h1 := hB.f_add 0 0
  rw [add_zero] at h1
  exact mul_left_cancel (h1.symm.trans (mul_one (f 0)).symm)

theorem f_nat_mul (hB : BorelDataP p P M x f W) (t : GaloisField p n) (k : ℕ) :
    f ((k : GaloisField p n) * t) = f t ^ k := by
  induction k with
  | zero => simp [hB.f_zero]
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, hB.f_add, ih, pow_succ]

theorem f_pow_p (hB : BorelDataP p P M x f W) (t : GaloisField p n) : f t ^ p = 1 := by
  have hpF : ((p : ℕ) : GaloisField p n) = 0 := CharP.cast_eq_zero (GaloisField p n) p
  rw [← hB.f_nat_mul t p, hpF, zero_mul, hB.f_zero]

theorem f_neg (hB : BorelDataP p P M x f W) (t : GaloisField p n) : f (-t) = (f t)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hB.f_add, neg_add_cancel, hB.f_zero]

theorem f_mem (hB : BorelDataP p P M x f W) (t : GaloisField p n) : f t ∈ (P : Subgroup G) :=
  (hB.le ((hB.mem_iff _).mpr ⟨t, 0, hp.out.pos, by simp⟩)).1

theorem f_mem_W (hB : BorelDataP p P M x f W) (t : GaloisField p n) : f t ∈ W :=
  (hB.mem_iff _).mpr ⟨t, 0, hp.out.pos, by simp⟩

theorem f_not_mem_zpowers (hB : BorelDataP p P M x f W) {t : GaloisField p n} (ht : t ≠ 0) :
    f t ∉ zpowers x := by
  intro hmem
  have hf1 : f t ≠ 1 := fun h1 => ht (hB.f_inj (h1.trans hB.f_zero.symm))
  have hfo : orderOf (f t) = p := orderOf_eq_prime (hB.f_pow_p t) hf1
  have hxo : orderOf x = p := orderOf_eq_prime hB.x_pow hB.x_ne_one
  have heq : zpowers (f t) = zpowers x := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hmem) (by
    rw [Nat.card_zpowers, Nat.card_zpowers, hfo, hxo])
  have hxmem : x ∈ zpowers (f t) := heq ▸ mem_zpowers x
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hxmem)
  exact hB.f_ne ((m : GaloisField p n) * t) ((hB.f_nat_mul t m).trans hm)

@[expose] def plane (x : G) (f : GaloisField p n → G) (t₀ : GaloisField p n) : Subgroup G :=
  zpowers x ⊔ zpowers (f t₀)

theorem plane_card (hB : BorelDataP p P M x f W) {t₀ : GaloisField p n} (ht₀ : t₀ ≠ 0) :
    Nat.card (plane x f t₀) = p ^ 2 := by
  have hxo : orderOf x = p := orderOf_eq_prime hB.x_pow hB.x_ne_one
  have hcomm : ∀ e ∈ zpowers x, e * f t₀ = f t₀ * e := fun e he => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left (show Commute x (f t₀) from (hB.f_comm t₀).symm) k).eq
  rw [plane, CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp.out (zpowers x)
    (hB.f_pow_p t₀) (hB.f_not_mem_zpowers ht₀) hcomm, Nat.card_zpowers, hxo]
  ring

theorem exists_plane_eq (hB : BorelDataP p P M x f W) {U : Subgroup G} (hUP : U ≤ (P : Subgroup G))
    (hUe : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2) (hxU : x ∈ U)
    (hPab : IsMulCommutative (P : Subgroup G)) :
    ∃ t₀ : GaloisField p n, t₀ ≠ 0 ∧ U = plane x f t₀ := by
  have hxo : orderOf x = p := orderOf_eq_prime hB.x_pow hB.x_ne_one
  obtain ⟨y, hyU, hyx⟩ : ∃ y ∈ U, y ∉ zpowers x := by
    by_contra hall
    push_neg at hall
    have h1 : Nat.card U ≤ Nat.card (zpowers x) := Subgroup.card_le_of_le (fun y hy => hall y hy)
    rw [Nat.card_zpowers, hxo, hUc] at h1
    nlinarith [hB.five_le]
  have hyp : y ^ p = 1 := hUe.2 y hyU
  have hcomm : x * y = y * x := congrArg Subtype.val (hUe.1.is_comm.comm ⟨x, hxU⟩ ⟨y, hyU⟩)
  have hyC : y ∈ centralizer ({x} : Set G) :=
    mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]; exact hcomm
  have hyW : y ∈ W := hB.of_pow_p y (Subgroup.mem_inf.mpr ⟨hUP hyU, hyC⟩) hyp
  obtain ⟨t, i, _, hyeq⟩ := (hB.mem_iff y).mp hyW
  have hft : f t = y * (x ^ i)⁻¹ := by rw [hyeq, mul_inv_cancel_right]
  have hfU : f t ∈ U := by
    rw [hft]
    exact U.mul_mem hyU (U.inv_mem (U.pow_mem hxU i))
  have ht : t ≠ 0 := by
    rintro rfl
    apply hyx
    rw [hyeq, hB.f_zero, one_mul]
    exact (zpowers x).pow_mem (mem_zpowers x) i
  have hle : plane x f t ≤ U := sup_le (zpowers_le.mpr hxU) (zpowers_le.mpr hfU)
  have hcard : Nat.card (plane x f t) = p ^ 2 := hB.plane_card ht
  exact ⟨t, ht, (Subgroup.eq_of_le_of_card_ge hle (hUc.le.trans hcard.ge)).symm⟩

@[expose] noncomputable def fHom (hB : BorelDataP p P M x f W) :
    Multiplicative (GaloisField p n) →* G where
  toFun t := f t.toAdd
  map_one' := by simpa using hB.f_zero
  map_mul' s t := hB.f_add _ _

@[expose] noncomputable def QK (hB : BorelDataP p P M x f W) : Subgroup G := hB.fHom.range

theorem mem_QK (hB : BorelDataP p P M x f W) {g : G} : g ∈ hB.QK ↔ ∃ t, f t = g := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.toAdd, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t, rfl⟩

theorem f_mem_QK (hB : BorelDataP p P M x f W) (t : GaloisField p n) : f t ∈ hB.QK :=
  hB.mem_QK.mpr ⟨t, rfl⟩

theorem QK_le_W (hB : BorelDataP p P M x f W) : hB.QK ≤ W := by
  intro g hg
  obtain ⟨t, rfl⟩ := hB.mem_QK.mp hg
  exact hB.f_mem_W t

theorem QK_le_P (hB : BorelDataP p P M x f W) : hB.QK ≤ (P : Subgroup G) :=
  fun _ hg => (hB.le (hB.QK_le_W hg)).1

theorem QK_comm (hB : BorelDataP p P M x f W) {a b : G} (ha : a ∈ hB.QK) (hb : b ∈ hB.QK) :
    a * b = b * a := by
  obtain ⟨s, rfl⟩ := hB.mem_QK.mp ha
  obtain ⟨t, rfl⟩ := hB.mem_QK.mp hb
  rw [← hB.f_add, ← hB.f_add, add_comm]

theorem QK_pow_p (hB : BorelDataP p P M x f W) {a : G} (ha : a ∈ hB.QK) : a ^ p = 1 := by
  obtain ⟨t, rfl⟩ := hB.mem_QK.mp ha
  exact hB.f_pow_p t

theorem QK_isElemAbelian (hB : BorelDataP p P M x f W) : IsElemAbelian p hB.QK :=
  ⟨⟨⟨fun a b => Subtype.ext (hB.QK_comm a.2 b.2)⟩⟩, fun _ ha => hB.QK_pow_p ha⟩

theorem QK_comm_x (hB : BorelDataP p P M x f W) {a : G} (ha : a ∈ hB.QK) : x * a = a * x := by
  obtain ⟨t, rfl⟩ := hB.mem_QK.mp ha
  exact (hB.f_comm t).symm

end BorelDataP

end CFSG.LocalAnalysis.RankFourTheoremC.P5
