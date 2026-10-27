module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1Setup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Quasithin CFSG.ProperTwoGeneratedCore.Assembly

section Burnside

variable {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

theorem exists_mem_normalizer_conj_eq_of_mem_centralizer (P : Sylow p K) {a b g : K}
    (ha : a ∈ Subgroup.centralizer (P : Set K)) (hb : b ∈ Subgroup.centralizer (P : Set K))
    (hg : g⁻¹ * a * g = b) : ∃ n ∈ Subgroup.normalizer (P : Set K), n⁻¹ * a * n = b :=
  burnside_fusion_lemma_centralizer P le_rfl (fun c hc => Subgroup.eq_of_le_of_card_ge hc (by
    rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective])) ha hb hg

theorem exists_mem_normalizer_conj_eq_of_le (P : Sylow p K) {H : Subgroup K}
    (hPH : (P : Subgroup K) ≤ H) {a b g : K} (ha : a ∈ Subgroup.centralizer (P : Set K))
    (hb : b ∈ Subgroup.centralizer (P : Set K)) (hgH : g ∈ H) (hg : g⁻¹ * a * g = b) :
    ∃ n ∈ H, n ∈ Subgroup.normalizer (P : Set K) ∧ n⁻¹ * a * n = b := by
  let C := H ⊓ Subgroup.centralizer ({b} : Set K)
  have hPC : (P : Subgroup K) ≤ C := fun x hx =>
    ⟨hPH hx, Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hb x hx)⟩
  have hP'C : ((g⁻¹ • P : Sylow p K) : Subgroup K) ≤ C := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      ← map_inv, inv_inv, MulAut.conj_apply] at hx
    refine ⟨?_, ?_⟩
    · have h := H.mul_mem (H.mul_mem (H.inv_mem hgH) (hPH hx)) hgH
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h
    · change x ∈ Subgroup.centralizer ({b} : Set K)
      rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
      have h := Subgroup.mem_centralizer_iff.mp ha _ hx
      calc x * (g⁻¹ * a * g) = g⁻¹ * (g * x * g⁻¹ * a) * g := by group
        _ = g⁻¹ * (a * (g * x * g⁻¹)) * g := by rw [h]
        _ = g⁻¹ * a * g * x := by group
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C ((g⁻¹ • P).subtype hP'C) (P.subtype hPC)
  have hcP : ((c : K) * g⁻¹) • P = P := by
    rw [mul_smul]
    exact Sylow.subtype_injective ((Sylow.smul_subtype hP'C c).symm.trans hc)
  have hn := Sylow.smul_eq_iff_mem_normalizer.mp hcP
  refine ⟨((c : K) * g⁻¹)⁻¹, H.inv_mem (H.mul_mem c.2.1 (H.inv_mem hgH)),
    (Subgroup.normalizer _).inv_mem hn, ?_⟩
  have hcb : (c : K) * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
  calc ((c : K) * g⁻¹)⁻¹⁻¹ * a * ((c : K) * g⁻¹)⁻¹ = c * (g⁻¹ * a * g) * (c : K)⁻¹ := by group
    _ = b := by rw [hg, hcb, mul_inv_cancel_right]

theorem exists_pow_mem_of_mem_normalizer (P : Sylow p K) {n : K}
    (hn : n ∈ Subgroup.normalizer (P : Set K)) :
    ∃ m : ℕ, ¬ p ∣ m ∧ n ^ m ∈ (P : Subgroup K) := by
  refine ⟨(P : Subgroup K).relIndex (Subgroup.normalizer (P : Set K)), fun hdvd => ?_, ?_⟩
  · refine P.not_dvd_index ?_
    rw [← Subgroup.relIndex_mul_index Subgroup.le_normalizer]
    exact dvd_mul_of_dvd_left hdvd _
  · have : ((P : Subgroup K).subgroupOf (Subgroup.normalizer (P : Set K))).Normal :=
      Subgroup.normal_in_normalizer
    have h := Subgroup.pow_index_mem
      ((P : Subgroup K).subgroupOf (Subgroup.normalizer (P : Set K))) ⟨n, hn⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h
    exact h

end Burnside

theorem dihedralGroup_two_eq_or_eq_mul : ∀ a b c : DihedralGroup 2, a ≠ 1 → b ≠ 1 → b ≠ a →
    c ≠ 1 → c ≠ a → c = b ∨ c = a * b := by
  decide

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

namespace CaseB1

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {M : ℕ}

theorem mem_centralizer_of_mem_X (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) : x ∈ Subgroup.centralizer (b1S T : Set (J ⧸ Subgroup.center J)) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hs => (hb.commute_of_mem_X_of_mem_S hx hs).eq.symm

theorem mk_mem_centralizer (hb : CaseB1 Q B T L M) :
    (u : J ⧸ Subgroup.center J) ∈ Subgroup.centralizer (b1S T : Set (J ⧸ Subgroup.center J)) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hs => (hb.commute_mk_of_mem_S hs).eq

theorem S_le_centralizer (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) : b1S T ≤ Subgroup.centralizer {x} := fun _ hs =>
  Subgroup.mem_centralizer_singleton_iff.mpr (hb.commute_of_mem_X_of_mem_S hx hs).eq.symm

theorem inv_mul_mul_mem_X (hb : CaseB1 Q B T L M) {x g : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hg : g⁻¹ * x * g ∈ b1S T) : g⁻¹ * x * g ∈ b1X T L := by
  by_cases hx1 : x = 1
  · rw [hx1, mul_one, inv_mul_cancel]
    exact one_mem _
  have hy2 : orderOf (g⁻¹ * x * g) = 2 :=
    (orderOf_inv_mul_mul g x).trans (hb.orderOf_of_mem_X hx hx1)
  have hym : ¬ IsMixedInv (g⁻¹ * x * g) := by
    rw [isMixedInv_inv_mul_mul_iff]
    exact hb.not_isMixedInv_of_mem_X hx
  refine (hb.mem_X_or_mem_D_of_not_isMixedInv hg hy2 hym).resolve_right fun hyD => ?_
  have hyu := (hb.commute_mk_of_mem_S hg).eq
  have hw : g * (u : J ⧸ Subgroup.center J) * g⁻¹ ∈ Subgroup.centralizer {x} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * (u : J ⧸ Subgroup.center J) * g⁻¹ * x
        = g * ((u : J ⧸ Subgroup.center J) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * x * g * (u : J ⧸ Subgroup.center J)) * g⁻¹ := by rw [← hyu]
      _ = x * (g * (u : J ⧸ Subgroup.center J) * g⁻¹) := by group
  have hw2 : orderOf (g * (u : J ⧸ Subgroup.center J) * g⁻¹) = 2 := by
    have h := orderOf_inv_mul_mul g⁻¹ (u : J ⧸ Subgroup.center J)
    rw [inv_inv] at h
    rw [h]
    exact hb.orderOf_mk
  obtain ⟨c, hc, hcS⟩ :=
    involution_conjugate_into_sylow hb.sylow _ (hb.S_le_centralizer hx) _ hw hw2
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hkx : (g⁻¹ * c)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * c) = x := by
    calc (g⁻¹ * c)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * c) = c⁻¹ * (c * x) := by rw [hcx]; group
      _ = x := inv_mul_cancel_left c x
  have hkv : c⁻¹ * (g * (u : J ⧸ Subgroup.center J) * g⁻¹) * c =
      (g⁻¹ * c)⁻¹ * (u : J ⧸ Subgroup.center J) * (g⁻¹ * c) := by
    group
  rw [hkv] at hcS
  have hv2 := (orderOf_inv_mul_mul (g⁻¹ * c) (u : J ⧸ Subgroup.center J)).trans hb.orderOf_mk
  have hvm : ¬ IsMixedInv ((g⁻¹ * c)⁻¹ * (u : J ⧸ Subgroup.center J) * (g⁻¹ * c)) := by
    rw [isMixedInv_inv_mul_mul_iff]
    exact hb.not_isMixedInv_of_mem_D hb.mk_mem_D
  rcases hb.mem_X_or_mem_D_of_not_isMixedInv hcS hv2 hvm with hvX | hvD
  ·
    obtain ⟨n, hn, hnv⟩ := exists_mem_normalizer_conj_eq_of_mem_centralizer hb.sylow
      hb.mk_mem_centralizer (hb.mem_centralizer_of_mem_X hvX) rfl
    have hnu := Subgroup.mem_centralizer_singleton_iff.mp (hb.normalizer_le_centralizer hn)
    rw [← hnv, mul_assoc, ← hnu, inv_mul_cancel_left] at hvX
    exact hb.mk_not_mem_X hvX
  ·
    have hmix := hb.isMixedInv_mul hx hvD hx1 hv2
    have hxv : x * ((g⁻¹ * c)⁻¹ * (u : J ⧸ Subgroup.center J) * (g⁻¹ * c)) =
        (g⁻¹ * c)⁻¹ * (g⁻¹ * x * g * (u : J ⧸ Subgroup.center J)) * (g⁻¹ * c) := by
      calc x * ((g⁻¹ * c)⁻¹ * (u : J ⧸ Subgroup.center J) * (g⁻¹ * c))
          = (g⁻¹ * c)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * c) *
              ((g⁻¹ * c)⁻¹ * (u : J ⧸ Subgroup.center J) * (g⁻¹ * c)) := by rw [hkx]
        _ = (g⁻¹ * c)⁻¹ * (g⁻¹ * x * g * (u : J ⧸ Subgroup.center J)) * (g⁻¹ * c) := by group
    rw [hxv, isMixedInv_inv_mul_mul_iff] at hmix
    exact hb.not_isMixedInv_of_mem_D ((b1D T L).mul_mem hyD hb.mk_mem_D) hmix

theorem mul_mul_inv_mem_X (hb : CaseB1 Q B T L M) {x g : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hg : g * x * g⁻¹ ∈ b1S T) : g * x * g⁻¹ ∈ b1X T L := by
  have h := hb.inv_mul_mul_mem_X hx (g := g⁻¹) (by rwa [inv_inv])
  rwa [inv_inv] at h

theorem eq_one_of_inv_mul_mul_mem_D (hb : CaseB1 Q B T L M) {x g : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hg : g⁻¹ * x * g ∈ b1D T L) : x = 1 := by
  have h := hb.eq_one_of_mem_X_of_mem_D (hb.inv_mul_mul_mem_X hx (hb.D_le_S hg)) hg
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem inv_mul_mk_mul_mem_D (hb : CaseB1 Q B T L M) {g : J ⧸ Subgroup.center J}
    (hg : g⁻¹ * (u : J ⧸ Subgroup.center J) * g ∈ b1S T) :
    g⁻¹ * (u : J ⧸ Subgroup.center J) * g ∈ b1D T L := by
  have hm : ¬ IsMixedInv (g⁻¹ * (u : J ⧸ Subgroup.center J) * g) := by
    rw [isMixedInv_inv_mul_mul_iff]
    exact hb.not_isMixedInv_of_mem_D hb.mk_mem_D
  refine (hb.mem_X_or_mem_D_of_not_isMixedInv hg
    ((orderOf_inv_mul_mul _ _).trans hb.orderOf_mk) hm).resolve_left fun hX => ?_
  have h := hb.mul_mul_inv_mem_X hX (g := g)
    (by rw [show g * (g⁻¹ * (u : J ⧸ Subgroup.center J) * g) * g⁻¹ = u by group]; exact hb.mk_mem_S)
  rw [show g * (g⁻¹ * (u : J ⧸ Subgroup.center J) * g) * g⁻¹ = u by group] at h
  exact hb.mk_not_mem_X h

theorem normalizer_le_normalizer_X (hb : CaseB1 Q B T L M) :
    Subgroup.normalizer (b1S T : Set (J ⧸ Subgroup.center J)) ≤
      Subgroup.normalizer (b1X T L : Set (J ⧸ Subgroup.center J)) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  refine fun x => ⟨fun hx => hb.mul_mul_inv_mem_X hx ((hn x).mp (hb.X_le_S hx)), fun hx => ?_⟩
  have h := hb.inv_mul_mul_mem_X hx (g := n) (by
    rw [show n⁻¹ * (n * x * n⁻¹) * n = x by group]
    exact (hn x).mpr (hb.X_le_S hx))
  rwa [show n⁻¹ * (n * x * n⁻¹) * n = x by group] at h

theorem eq_or_eq_mul_of_mem_X (hb : CaseB1 Q B T L M) {x y z : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hy : y ∈ b1X T L) (hz : z ∈ b1X T L) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hyx : y ≠ x) (hz1 : z ≠ 1) (hzx : z ≠ x) : z = y ∨ z = x * y := by
  have hne : ∀ {s t : b1X T L}, (s : J ⧸ Subgroup.center J) ≠ t → hb.psiX s ≠ hb.psiX t :=
    fun h h' => h (congrArg Subtype.val (hb.psiX.injective h'))
  have h1 : ∀ {s : b1X T L}, (s : J ⧸ Subgroup.center J) ≠ 1 → hb.psiX s ≠ 1 := fun h h' =>
    h (by rw [(MulEquiv.map_eq_one_iff _).mp h', OneMemClass.coe_one])
  rcases dihedralGroup_two_eq_or_eq_mul (hb.psiX ⟨x, hx⟩) (hb.psiX ⟨y, hy⟩) (hb.psiX ⟨z, hz⟩)
    (h1 hx1) (h1 hy1) (hne hyx) (h1 hz1) (hne hzx) with h | h
  · exact Or.inl (congrArg Subtype.val (hb.psiX.injective h))
  · rw [← map_mul] at h
    exact Or.inr (congrArg Subtype.val (hb.psiX.injective h))

theorem commute_sq_of_mem_normalizer (hb : CaseB1 Q B T L M) {x n y : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hx1 : x ≠ 1)
    (hn : n ∈ Subgroup.normalizer (b1S T : Set (J ⧸ Subgroup.center J))) (hnx : Commute n x)
    (hy : y ∈ b1X T L) : Commute (n ^ 2) y := by
  by_cases hy1 : y = 1
  · rw [hy1]
    exact Commute.one_right _
  by_cases hyx : y = x
  · rw [hyx]
    exact hnx.pow_left 2
  have hz : n * y * n⁻¹ ∈ b1X T L :=
    (Subgroup.mem_normalizer_iff.mp (hb.normalizer_le_normalizer_X hn) y).mp hy
  have hz1 : n * y * n⁻¹ ≠ 1 := fun h => hy1 (by
    rw [show y = n⁻¹ * (n * y * n⁻¹) * n by group, h, mul_one, inv_mul_cancel])
  have hzx : n * y * n⁻¹ ≠ x := fun h => hyx (by
    rw [show y = n⁻¹ * (n * y * n⁻¹) * n by group, h, mul_assoc, ← hnx.eq, inv_mul_cancel_left])
  rcases hb.eq_or_eq_mul_of_mem_X hx hy hz hx1 hy1 hyx hz1 hzx with h | h
  · refine Commute.pow_left ?_ 2
    calc n * y = n * y * n⁻¹ * n := by group
      _ = y * n := by rw [h]
  · rw [commute_iff_eq, pow_two]
    calc n * n * y = n * (n * y * n⁻¹) * n⁻¹ * (n * n) := by group
      _ = n * (x * y) * n⁻¹ * (n * n) := by rw [h]
      _ = n * x * n⁻¹ * (n * y * n⁻¹) * (n * n) := by group
      _ = x * (x * y) * (n * n) := by rw [h, hnx.eq, mul_inv_cancel_right]
      _ = y * (n * n) := by rw [← mul_assoc x x y, hb.mul_self_of_mem_X hx, one_mul]

theorem commute_of_mem_normalizer (hb : CaseB1 Q B T L M) {x n y : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hx1 : x ≠ 1)
    (hn : n ∈ Subgroup.normalizer (b1S T : Set (J ⧸ Subgroup.center J))) (hnx : Commute n x)
    (hy : y ∈ b1X T L) : Commute n y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hnm⟩ := exists_pow_mem_of_mem_normalizer hb.sylow hn
  obtain ⟨j, rfl⟩ : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm)
  have h2 := (hb.commute_sq_of_mem_normalizer hx hx1 hn hnx hy).pow_left j
  have hm' : Commute (n ^ (2 * j + 1)) y := (hb.commute_of_mem_X_of_mem_S hy hnm).symm
  have hn' : n = ((n ^ 2) ^ j)⁻¹ * n ^ (2 * j + 1) := by
    rw [← pow_mul, pow_succ, inv_mul_cancel_left]
  rw [hn']
  exact h2.inv_left.mul_left hm'

theorem inv_mul_mul_eq_of_mem_centralizer (hb : CaseB1 Q B T L M)
    {x y c : J ⧸ Subgroup.center J} (hx : x ∈ b1X T L) (hx1 : x ≠ 1) (hy : y ∈ b1X T L)
    (hc : c ∈ Subgroup.centralizer {x}) (hcy : c⁻¹ * y * c ∈ b1S T) : c⁻¹ * y * c = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hnC, hnN, hny⟩ := exists_mem_normalizer_conj_eq_of_le hb.sylow
    (hb.S_le_centralizer hx) (hb.mem_centralizer_of_mem_X hy)
    (hb.mem_centralizer_of_mem_X (hb.inv_mul_mul_mem_X hy hcy)) hc rfl
  rw [← hny, mul_assoc, ← (hb.commute_of_mem_normalizer hx hx1 hnN
    (Subgroup.mem_centralizer_singleton_iff.mp hnC) hy).eq, inv_mul_cancel_left]

end CaseB1

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
