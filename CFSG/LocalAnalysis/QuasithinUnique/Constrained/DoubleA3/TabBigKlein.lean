module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Block
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

@[expose] def KleinSC (H : Type*) [Group H] : Prop :=
  ∀ V : Subgroup H, Nat.card ↥V = 4 → (∀ v ∈ V, v * v = 1) →
    ∀ g : H, (∀ v ∈ V, g * v = v * g) → g ∈ V

theorem KleinSC.of_mulEquiv {K H : Type*} [Group K] [Group H] (e : K ≃* H) (h : KleinSC H) :
    KleinSC K := by
  intro V hV4 hV2 g hg
  have hcard : Nat.card ↥(V.map e.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hV4
  have hsq : ∀ w ∈ V.map e.toMonoidHom, w * w = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    show e v * e v = 1
    rw [← map_mul, hV2 v hv, map_one]
  have hc : ∀ w ∈ V.map e.toMonoidHom, e g * w = w * e g := by
    rintro _ ⟨v, hv, rfl⟩
    show e g * e v = e v * e g
    rw [← map_mul, ← map_mul, hg v hv]
  obtain ⟨v, hv, hve⟩ := h _ hcard hsq (e g) hc
  have hvg : v = g := e.injective hve
  rw [← hvg]
  exact hv

section Elements

variable {H : Type*} [Group H]

theorem exists_two_ne_one_of_card_four {V : Subgroup H} (hV2 : ∀ v ∈ V, v * v = 1)
    (hV4 : Nat.card ↥V = 4) : ∃ t ∈ V, t ≠ 1 ∧ ∃ b ∈ V, b ≠ 1 ∧ b ≠ t := by
  have hfin : Finite ↥V := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨t, htV, ht1⟩ : ∃ t ∈ V, t ≠ 1 := by
    by_contra hcon
    have hle : V ≤ ⊥ := fun u hu => by
      rw [Subgroup.mem_bot]
      by_contra h'
      exact hcon ⟨u, hu, h'⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hV4, Subgroup.card_bot] at h1
    omega
  refine ⟨t, htV, ht1, ?_⟩
  by_contra hcon
  have ht2 : t ^ 2 = 1 := by rw [sq]; exact hV2 t htV
  have hle : V ≤ zpowers t := fun u hu => by
    rw [mem_zpowers_iff_of_sq_eq_one ht2]
    by_contra h'
    push Not at h'
    exact hcon ⟨u, hu, h'.1, h'.2⟩
  have hfz : Finite ↥(zpowers t) :=
    Finite.of_injective (Subgroup.inclusion ((zpowers_le).mpr htV))
      (Subgroup.inclusion_injective _)
  have h1 := Subgroup.card_le_of_le hle
  have h2 : Nat.card ↥(zpowers t) = 2 := by rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1]
  rw [hV4, h2] at h1
  omega

theorem comm_of_sq_eq_one {V : Subgroup H} (hV2 : ∀ v ∈ V, v * v = 1) {a b : H} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hV2 a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hV2 b hb)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hV2 (a * b) (V.mul_mem ha hb))
  rw [mul_inv_rev, ha', hb'] at hab
  exact hab.symm

end Elements

section A4

variable {G : Type} [Group G] [Finite G]

theorem IsA4Block.eq_of_card_four {L U W : Subgroup G} (h : IsA4Block L U) (hWL : W ≤ L)
    (hW4 : Nat.card ↥W = 4) : W = U := by
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  have hLN : L ≤ normalizer (U : Set G) := by
    rw [hLc]
    exact sup_le Subgroup.le_normalizer ((zpowers_le).mpr hcN)
  have hWN : W ≤ normalizer (U : Set G) := hWL.trans hLN
  have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hWN
  have hU4 := h.card_U
  rw [hW4, hU4] at hmul
  have hdvd12 : Nat.card ↥(W ⊔ U) ∣ 12 := by
    have := Subgroup.card_dvd_of_le (sup_le hWL h.le : W ⊔ U ≤ L)
    rwa [h.card_L] at this
  have hdvd16 : Nat.card ↥(W ⊔ U) ∣ 16 := Dvd.intro _ hmul
  have hdvd4 : Nat.card ↥(W ⊔ U) ∣ 4 := by
    have := Nat.dvd_gcd hdvd16 hdvd12
    norm_num at this
    exact this
  have hge : 4 ≤ Nat.card ↥(W ⊔ U) := by
    rw [← hU4]
    exact Subgroup.card_le_of_le le_sup_right
  have hs : Nat.card ↥(W ⊔ U) = 4 := le_antisymm (Nat.le_of_dvd (by norm_num) hdvd4) hge
  rw [hs] at hmul
  have hinf : Nat.card ↥(W ⊓ U) = 4 := by omega
  have hWU : W ⊓ U = W :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hinf, hW4])
  have hWleU : W ≤ U := hWU ▸ inf_le_right
  exact Subgroup.eq_of_le_of_card_ge hWleU (by rw [hW4, hU4])

theorem IsA4Block.mem_normalizer_U {L U : Subgroup G} (h : IsA4Block L U) {p : G}
    (hp : p ∈ normalizer (L : Set G)) : p ∈ normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  let W : Subgroup G := U.map (MulAut.conj p).toMonoidHom
  have hWL : W ≤ L := by
    rintro _ ⟨u, hu, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hp u).mp (h.le hu)
  have hW4 : Nat.card ↥W = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj p).injective]
    exact h.card_U
  have hWU : W = U := h.eq_of_card_four hWL hW4
  intro x
  constructor
  · intro hx
    have : p * x * p⁻¹ ∈ W := ⟨x, hx, rfl⟩
    rwa [hWU] at this
  · intro hx
    rw [← hWU] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : p * y * p⁻¹ = p * x * p⁻¹ := hyx
    have : y = x := by simpa using hyx'
    rwa [← this]

theorem tabBigA4_of_kleinSC {K L U P : Subgroup G} (hK : KleinSC ↥K) (hLK : L ≤ K)
    (hA4 : IsA4Block L U) (hPK : P ≤ K) (hP2 : IsPGroup 2 ↥P)
    (hPL : P ≤ normalizer (L : Set G)) : Nat.card ↥P ≤ 8 := by
  classical
  have hUK : U ≤ K := hA4.le.trans hLK
  have hC : ∀ g ∈ K, (∀ u ∈ U, g * u = u * g) → g ∈ U := by
    intro g hg hgu
    have hV : Nat.card ↥(U.subgroupOf K) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv]
      exact hA4.card_U
    have hV2 : ∀ v ∈ U.subgroupOf K, v * v = 1 := fun v hv =>
      Subtype.ext (by simpa [sq] using hA4.sq_U (v : G) hv)
    exact hK (U.subgroupOf K) hV hV2 ⟨g, hg⟩ (fun v hv => Subtype.ext (hgu (v : G) hv))
  have hPU : P ≤ normalizer (U : Set G) := fun p hp => hA4.mem_normalizer_U (hPL hp)
  have hB2 : IsPGroup 2 ↥(P ⊔ U) := by
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hPU
    have hdvd : Nat.card ↥(P ⊔ U) ∣ 2 ^ (n + 2) := by
      have h1 : Nat.card ↥(P ⊔ U) ∣ Nat.card ↥P * Nat.card ↥U := Dvd.intro _ hmul
      have h2 : Nat.card ↥P * Nat.card ↥U = 2 ^ (n + 2) := by rw [hn, hA4.card_U]; ring
      rwa [h2] at h1
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card hm
  have hBN : P ⊔ U ≤ normalizer (U : Set G) := sup_le hPU Subgroup.le_normalizer
  have hBK : P ⊔ U ≤ K := sup_le hPK hUK
  have hPB : Nat.card ↥P ≤ Nat.card ↥(P ⊔ U) := Subgroup.card_le_of_le le_sup_left
  by_cases hcent : P ⊔ U ≤ centralizer (U : Set G)
  · have hBU : P ⊔ U ≤ U := fun g hg =>
      hC g (hBK hg) (fun u hu => (Subgroup.mem_centralizer_iff.mp (hcent hg) u hu).symm)
    have := Subgroup.card_le_of_le hBU
    rw [hA4.card_U] at this
    omega
  · obtain ⟨z, hzU, hz1, hrel, -⟩ := klein_structure hA4.card_U hA4.sq_U
      (le_sup_right : U ≤ P ⊔ U) hBN hB2 hcent
    have hle : (P ⊔ U) ⊓ centralizer (U : Set G) ≤ U := fun g hg =>
      hC g (hBK hg.1) (fun u hu => (Subgroup.mem_centralizer_iff.mp hg.2 u hu).symm)
    have h1 := Subgroup.card_le_of_le hle
    rw [hA4.card_U] at h1
    have hcardB := card_eq_card_mul_relIndex_of_le
      (inf_le_left : (P ⊔ U) ⊓ centralizer (U : Set G) ≤ P ⊔ U)
    rw [hrel] at hcardB
    omega

end A4

end CFSG.QuasithinUnique.DoubleA3
