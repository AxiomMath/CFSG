module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneNine

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L128P

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem thirteen_one_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V n V₁ V₂) {g : G} (hg : g ∈ p128 T L V) :
    V ≤ w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g := by
  obtain ⟨-, -, hab⟩ := hs.hyp.card_sq
  obtain ⟨-, hTV⟩ := hs.hyp.hyp.le_and_normalizes_F4 h1222
  have hgN : g ∈ Subgroup.normalizer (V : Set G) :=
    ((inf_le_left : p128 T L V ≤ L ⊔ T).trans (sup_le hs.hyp.hyp.irrPlus.2.2.1 hTV)) hg
  have hVW : V ≤ w128 V V₁ V₂ := fun v hv => ⟨le_conjClosure V _ hv,
    Subgroup.mem_centralizer_iff.mpr fun w hw => hab w (hs.v2.1 hw) v hv⟩
  refine fun v hv => ⟨hVW hv, ?_⟩
  show v ∈ rconj (w128 V V₁ V₂) g
  rw [mem_rconj]
  exact hVW ((Subgroup.mem_normalizer_iff.mp hgN v).mp hv)

theorem thirteen_two_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V n V₁ V₂) {g : G} (hg : g ∈ p128 T L V) :
    CFSG.conjugate (zU128 V V₁) g ≤ Subgroup.centralizer (V : Set G) := by
  intro z hz
  have hz' : g * z * g⁻¹ ∈ zU128 V V₁ := mem_rconj.mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvE := thirteen_one_F4 h1222 hs hg hv
  have hv' : g * v * g⁻¹ ∈ u128 V V₁ := (mem_rconj.mp hvE.2).1
  have h1 := Subgroup.mem_centralizer_iff.mp hz'.2 _ hv'
  calc v * z = g⁻¹ * ((g * v * g⁻¹) * (g * z * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * z * g⁻¹) * (g * v * g⁻¹)) * g := by rw [h1]
    _ = z * v := by group

theorem thirteen_eight_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    CFSG.Open.pRank 3 (centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂) ≤ 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂ with hCdef
  set G₂ := Subgroup.normalizer (V₂ : Set G) with hG₂
  set N := i128 T L V V₁ ⊓ Subgroup.centralizer (V₂ : Set G) with hNdef
  obtain ⟨E, hEC, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) C
  have hCG₂ : C ≤ G₂ := fun x hx => mem_normalizer_of_conj_mem_of_finite fun v hv => by
    have h1 := hx.2.2 v hv
    have e : x * v * x⁻¹ = (x * v * x⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact V₂.mul_mem (hs.le h1) hv
  have hEG₂ : E ≤ G₂ := hEC.trans hCG₂
  have hEcV : ∀ e ∈ E, e ∈ Subgroup.centralizer (V₂ : Set G) := fun e he =>
    mem_centralizer_of_pow_three hs (hEC he) (hE.2 e he)

  have hIP := i128_le_p128_F4 h1222 h12213 hs
  have hIG₂ : i128 T L V V₁ ≤ G₂ := hIP.trans (p128_le_normalizer le_rfl hs.v2)
  have hG₂I := normalizer_le_normalizer_i128_F4 h1222 hs
  have hNorm : G₂ ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hG₂I hx, normalizer_le_normalizer_centralizer'' _ hx⟩
  have hN2G : IsPGroup 2 ↥N := by
    rw [hNdef, i128_inf_centralizer_F4 h1222 h12213 hs]
    exact pCoreOf_isPGroup 2 _
  have hNG₂ : N ≤ G₂ := inf_le_left.trans hIG₂
  have hNnormal : (N.subgroupOf G₂).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNorm
  have hN2 : IsPGroup 2 ↥(N.subgroupOf G₂) :=
    hN2G.of_equiv (Subgroup.subgroupOfEquivOfLe hNG₂).symm

  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨-, hsq, -⟩ := hs.hyp.card_sq
  obtain ⟨a, ha, ha1, b, hb, hbV₁⟩ := exists_gens hV₁2 hV₂4
  obtain ⟨k, hk, hka, hkb, -⟩ := exists_rotation_mem_F4 h1222 hs.hyp hs.v1 hs.v2 hs.le ha ha1 hb hbV₁
  have hb2 : b * b = 1 := by rw [← pow_two]; exact hsq b (hs.v2.1 hb)
  have hkI : k ∈ i128 T L V V₁ := by
    rw [i128_eq_sup_F4 h1222 h12213 hs]
    exact Subgroup.mem_sup_left hk
  have hkG₂ : k ∈ G₂ := hIG₂ hkI
  have hkab : k * (a * b) * k⁻¹ = a := by
    calc k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
      _ = b * (a * b) := by rw [hka, hkb]
      _ = a := by
        rw [← mul_assoc, ← hs.hyp.card_sq.2.2 a (hs.v1.1 ha) b (hs.v2.1 hb), mul_assoc, hb2,
          mul_one]
  have hk3C : k ^ 3 ∈ Subgroup.centralizer (V₂ : Set G) := by
    have h3a : k ^ 3 * a * (k ^ 3)⁻¹ = a := by
      calc k ^ 3 * a * (k ^ 3)⁻¹ = k * (k * (k * a * k⁻¹) * k⁻¹) * k⁻¹ := by
            rw [pow_three]; group
        _ = a := by rw [hka, hkb, hkab]
    have h3b : k ^ 3 * b * (k ^ 3)⁻¹ = b := by
      calc k ^ 3 * b * (k ^ 3)⁻¹ = k * (k * (k * b * k⁻¹) * k⁻¹) * k⁻¹ := by
            rw [pow_three]; group
        _ = b := by rw [hkb, hkab, hka]
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rcases eq_of_mem_four hs.le hV₁2 hV₂4 ha ha1 hbV₁ hb hv with e | e | e | e <;> rw [e]
    · group
    · calc a * k ^ 3 = (k ^ 3 * a * (k ^ 3)⁻¹) * k ^ 3 := by rw [h3a]
        _ = k ^ 3 * a := by group
    · calc b * k ^ 3 = (k ^ 3 * b * (k ^ 3)⁻¹) * k ^ 3 := by rw [h3b]
        _ = k ^ 3 * b := by group
    · calc a * b * k ^ 3 =
          (k ^ 3 * a * (k ^ 3)⁻¹) * (k ^ 3 * b * (k ^ 3)⁻¹) * k ^ 3 := by
            rw [h3a, h3b]
        _ = k ^ 3 * (a * b) := by group
  have hkC : k ∉ Subgroup.centralizer (V₂ : Set G) := fun hc => hbV₁ (by
    have h1 := Subgroup.mem_centralizer_iff.mp hc a (hs.le ha)
    have h2 : k * a * k⁻¹ = a := by rw [← h1]; group
    rw [← hka, h2]
    exact ha)
  have hk3 : k ^ 3 ∈ N := ⟨(i128 T L V V₁).pow_mem hkI 3, hk3C⟩

  have hAc : ∀ x y : ↥E, x * y = y * x := fun x y => hE.1.is_comm.comm x y
  have hAp : ∀ x : ↥E, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hk3' : (⟨k, hkG₂⟩ : ↥G₂) ^ 3 ∈ N.subgroupOf G₂ := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hk3
  have hcomm' : ∀ x : ↥E, Subgroup.inclusion hEG₂ x * (⟨k, hkG₂⟩ : ↥G₂) *
      (Subgroup.inclusion hEG₂ x)⁻¹ * (⟨k, hkG₂⟩ : ↥G₂)⁻¹ ∈ N.subgroupOf G₂ := by
    intro x
    rw [Subgroup.mem_subgroupOf]
    show (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ N
    have hxG₂ : (x : G) ∈ G₂ := hEG₂ x.2
    have hxC : (x : G) ∈ Subgroup.centralizer (V₂ : Set G) := hEcV x x.2
    constructor
    · have h1 : (x : G) * k * (x : G)⁻¹ ∈ i128 T L V V₁ :=
        (Subgroup.mem_normalizer_iff.mp (hG₂I hxG₂) k).mp hkI
      exact (i128 T L V V₁).mul_mem h1 ((i128 T L V V₁).inv_mem hkI)
    · have h1 : k * (x : G)⁻¹ * k⁻¹ ∈ Subgroup.centralizer (V₂ : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer'' _ hkG₂) _).mp
          ((Subgroup.centralizer (V₂ : Set G)).inv_mem hxC)
      have e : (x : G) * k * (x : G)⁻¹ * k⁻¹ = (x : G) * (k * (x : G)⁻¹ * k⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hxC h1
  have hind' : ∀ (x : ↥E) (m : ↥G₂), m ∈ N.subgroupOf G₂ → ∀ j : ℤ,
      (⟨k, hkG₂⟩ : ↥G₂) ^ j = Subgroup.inclusion hEG₂ x * m → (3 : ℤ) ∣ j := by
    intro x m hm j hj
    by_contra h3
    have hmC : (m : G) ∈ Subgroup.centralizer (V₂ : Set G) := (Subgroup.mem_subgroupOf.mp hm).2
    have hkj : k ^ j = (x : G) * (m : G) := by
      have := congrArg (fun y : ↥G₂ => (y : G)) hj
      simpa using this
    have hkjC : k ^ j ∈ Subgroup.centralizer (V₂ : Set G) := by
      rw [hkj]
      exact Subgroup.mul_mem _ (hEcV x x.2) hmC
    exact hkC (mem_of_zpow_mem_of_pow_three_mem _ hk3C hkjC h3)
  have key := succ_le_pRank_quotient (N.subgroupOf G₂) hN2 hAc hAp hEcard
    (Subgroup.inclusion hEG₂) (Subgroup.inclusion_injective hEG₂) ⟨k, hkG₂⟩ hk3' hcomm' hind'

  have hN3 : ¬ 3 ∣ Nat.card ↥(N.subgroupOf G₂) := by
    obtain ⟨j, hj⟩ := hN2.exists_card_eq
    rw [hj]
    intro hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  have hq := CFSG.SectionRank.pRank_quotient_eq (p := 3) (N.subgroupOf G₂) hN3
  have hsub : CFSG.Open.pRank 3 (⊤ : Subgroup ↥G₂) = CFSG.Open.pRank 3 G₂ :=
    pRank_top_subtype (p := 3) G₂
  have hG₂core : pCoreOf 2 G₂ ≠ ⊥ := by
    have hV₂p : IsPGroup 2 V₂ := IsPGroup.of_card hs.v2.2.1
    have hV₂le : V₂ ≤ pCoreOf 2 G₂ :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hV₂p
    intro hbot
    rw [hbot, le_bot_iff] at hV₂le
    rw [hV₂le, Subgroup.card_bot] at hV₂4
    omega
  have h2 : CFSG.Open.pRank 3 G₂ ≤ 2 :=
    pRank_le_two_of_pCoreOf_ne_bot hs.hyp.hyp.qtke hG₂core Nat.prime_three (by norm_num)
  omega

end L128P

end CFSG.Quasithin.H13
